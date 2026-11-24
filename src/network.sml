structure network :> network =
struct

open HolKernel aiLib kernel sexp exec prog

type 'a net = 'a vector vector
type iv = int -> int
type ex = iv * int
type cache = int ref net
type pfn = (prog ref * exec ref * int list ref * int list ref) net
type node = int * int
type negpos = int * int
  
(* --------------------------------------------------------------------------
   Debugging
   -------------------------------------------------------------------------- *)
 
fun npts (n,p) = (its n ^ " " ^ its p)
fun nts (n,p) = (its n ^ "-" ^ its p)
fun debugf f = if !debug_flag then pe (f ()) else ()

(* --------------------------------------------------------------------------
   Net primitives
   -------------------------------------------------------------------------- *)

fun width_of_net net = Vector.length (Vector.sub (net,0))
fun depth_of_net net = Vector.length net
fun dim_of_net pn = (depth_of_net pn, width_of_net pn)

fun net_app f net = 
  let fun g (di,line) = Vector.appi (fn (wi,x) => f (x,di,wi)) line in
    Vector.appi g net
  end

fun net_sub net (i,j) = Vector.sub (Vector.sub (net,i),j);

fun net_tabulate (d,w) f = 
  Vector.tabulate (d,fn i => Vector.tabulate (w,fn j => f (i,j)))

(* --------------------------------------------------------------------------
   Program networks
   -------------------------------------------------------------------------- *)

fun flatten_pfn pfn = 
  map (! o #1) (List.concat (map vector_to_list (vector_to_list pfn)))

fun pfn_compare (pfn1,pfn2) = 
  list_compare prog_compare (flatten_pfn pfn1, flatten_pfn pfn2) 

fun descendant_aux (d,w) pfn (di,wil) = 
  if di = d-1 then [] else
  let 
    val pv = Vector.sub (pfn,di)
    fun add_dep (wi,dict) = eaddl (! (#4 (Vector.sub (pv,wi)))) dict
    val r =  (di+1, elist (foldl add_dep (eempty Int.compare) wil))
  in
    r :: descendant_aux (d,w) pfn r
  end
  
fun descendant pfn (di,wil) = 
  (di,wil) :: descendant_aux (dim_of_net pfn) pfn (di,wil) 
  
fun ancestor_aux (pfn:pfn) (di,wil) = 
  if di <= 0 then [] else
  let 
    val pv = Vector.sub (pfn,di)
    fun add_dep (wi,dict) = eaddl (! (#3 (Vector.sub (pv,wi)))) dict
    val r =  (di-1, elist (foldl add_dep (eempty Int.compare) wil))
  in
    r :: ancestor_aux pfn r
  end  
  
fun ancestor pfn (di,wil) = (di,wil) :: ancestor_aux pfn (di,wil)

fun write_node (p,_,incoming,outgoing) = 
  infts (zip_prog (!p)) ^ "|" ^ 
  lts (map its (!incoming)) ^ "|" ^ 
  lts (map its (!outgoing))

fun write_pv pv = String.concatWith " " (map write_node (vector_to_list pv))

fun write_pfn file pn = writel file (map write_pv (vector_to_list pn))

fun read_node s = 
  let 
    val (s1,s2,s3) = split_triple #"|" s
    val p = unzip_prog (stinf s1)
    val incoming = map string_to_int (stl s2)
    val outgoing = map string_to_int (stl s3)
  in
    (ref p, ref (mk_exec p), ref incoming, ref outgoing)
  end
    
fun read_pv s = Vector.fromList (map read_node (String.tokens Char.isSpace s))
  
fun read_pfn file = Vector.fromList (map read_pv (readl file))

(* --------------------------------------------------------------------------
   Initialize examples
   -------------------------------------------------------------------------- *)

val starttoken = [0,0,0,0]

fun ex_of_sentence sentence = 
  let 
    val sentencev = Vector.fromList (starttoken @ sentence)
    fun f i = if i < 4 then NONE else
      SOME (fn x => Vector.sub (sentencev, x mod i), Vector.sub (sentencev, i))
  in
    List.mapPartial I (List.tabulate (Vector.length sentencev,f))
  end

fun ex_of_sentencel sentencel = 
  List.concat (map ex_of_sentence sentencel)

(* --------------------------------------------------------------------------
   Computing a node and its dependencies
   -------------------------------------------------------------------------- *)

val reset_flag = ref false
val resetl_glob = ref []
val cache_empty = valOf Int.maxInt

fun compute_node_once inputf cache pfn (di,wi) =
  let
    val _ = inputf_glob := inputf    
    val _ = layerf_glob := 
      (if di = 0 then inputf else    
       (layerv_glob := Vector.sub(cache,di-1); access_layer))
    val _ = self_glob := wi
    val (d,w) = dim_of_net cache
    val i1 = (!layerf_glob) (wi - 1)
    val i2 = (!layerf_glob) (wi + 1)
    val _ = z_glob := (!layerf_glob) wi
    val fref = #2 (net_sub pfn (di,wi))
    val onew = (!fref) (i1,i2)
    val oref = net_sub cache (di,wi)
    val _ = if not (!reset_flag) then () else 
      resetl_glob := (fn () => oref := cache_empty) :: !resetl_glob 
  in
    oref := onew
  end

fun compute_node inputf cache pfn di wi =
  if ! (net_sub cache (di,wi)) <> cache_empty then () else
  let 
    val incoming = #3 (net_sub pfn (di,wi))
    val _ = app (compute_node inputf cache pfn (di-1)) (!incoming) 
  in
    compute_node_once inputf cache pfn (di,wi)
  end

fun recompute_node_unit inputf cache pfn (di,wi) =
  let val x = net_sub cache (di,wi) in 
    x := cache_empty; 
    compute_node inputf cache pfn di wi
  end
  
fun recompute_node inputf cache pfn (di,wi) =
  let val x = net_sub cache (di,wi) in 
    x := cache_empty; 
    compute_node inputf cache pfn di wi;
    !x
  end
  
(* --------------------------------------------------------------------------
   Dependency graph
   -------------------------------------------------------------------------- *)

(* todo: could replace with a set for better performance for large 
number of connections *)
fun dep_of_prog pfn (di,wi) p = 
  if di <= 0 then [] else
  let val w = width_of_net pfn in
    mk_fast_set Int.compare 
     (map (fn x => (x + wi) mod w) (collect_readargl p))
  end
  
fun rm_sedge pfn (d',w) wi =
  let val outgoing = #4 (net_sub pfn (d',wi)) in
    outgoing := filter (fn x => x <> w) (!outgoing)
  end

fun add_sedge pfn (d',w) wi = 
  let val outgoing = #4 (net_sub pfn (d',wi)) in
    if mem w (!outgoing) then () else outgoing := w :: !outgoing
  end

fun update_sdep pfn (di,wi) =
  let 
    val w = width_of_net pfn
    val (pref,_,incoming,_) = net_sub pfn (di,wi) 
    val newincoming = dep_of_prog pfn (di,wi) (!pref)
    val oldincoming = !incoming  
  in  
    incoming := newincoming;
    app (rm_sedge pfn (di-1,wi)) oldincoming;
    app (add_sedge pfn (di-1,wi)) newincoming
  end

fun recompute_alldep pfn = 
  let fun f (_,di,wi) = update_sdep pfn (di,wi) in net_app f pfn end

(* --------------------------------------------------------------------------
   Initialization
   -------------------------------------------------------------------------- *)

fun init_pfn (d,w) = 
  let
    fun f (di,wi) = 
      let val p = (!random_prog_glob) di in 
        (ref p, ref (mk_exec p), ref [], ref []) 
      end
    val pfn = net_tabulate (d,w) f
    val _ = recompute_alldep pfn
  in
    pfn
  end

fun init_cache pfn = net_tabulate (dim_of_net pfn) (fn _ => ref cache_empty)

(* --------------------------------------------------------------------------
   Negpos and score
   -------------------------------------------------------------------------- *)

fun negpos_vl l =
  let
    fun f (neg,pos) ((di,wi),out) =
      if out <= 0 then () else 
      if wi mod 2 = 0 then incr neg else incr pos
    val (neg,pos) = (ref 0, ref 0)
    val _ = app (f (neg,pos)) l
  in
    (!neg,!pos)
  end

val scaling = 1000000000
val scalingr = Real.fromInt scaling

fun score_negpos (obj,(neg,pos)) =
  let
    val total = neg + pos
    val correct = if obj > 0 then pos else neg   
    val freq = if total = 0 then 0.5 else int_div correct total
    val logr = if freq < epsilon then 21.0 else ~ (Math.ln freq)
  in
    Real.round (logr * scalingr)
  end

(* --------------------------------------------------------------------------
   Compute what would be the score if the output of a program was 0 or 1
   -------------------------------------------------------------------------- *)

fun negpos_inputf cache pfn tnodel inputf = 
  negpos_vl (map_assoc (recompute_node inputf cache pfn) tnodel)
  
fun negpos_01 cache pfn (di,wi) inputf (nodel,tnodel) npd =
  let
    val x = net_sub cache (hd nodel)
    val xold = !x    
    fun f a = 
      let 
        val _ = x := a
        val _ = app (recompute_node_unit inputf cache pfn) (tl nodel)
        val vl = map_assoc (! o net_sub cache) tnodel
      in
        negpos_vl vl
      end
    val r = if xold = 0 then (npd, f 1) else (f 0, npd)
    val _ = x := cache_empty
  in
    r
  end

fun score_01 cache pfn (nb,pb) (di,wi) (inputf,obj) = 
  let 
    val (depth,width) = dim_of_net pfn
    val descl = descendant pfn (di,[wi])
    val nodel = distrib descl
    val tnodeline = last descl
    val tnodel = map (fn x => (fst tnodeline, x)) (snd tnodeline)
    val (nd,pd) = negpos_inputf cache pfn tnodel inputf
    val (nh,ph) = (nb - nd, pb - pd)
    val ((n0,p0),(n1,p1)) = 
      negpos_01 cache pfn (di,wi) inputf (nodel,tnodel) (nd,pd)
    val np0 = (nh + n0, ph + p0) 
    val np1 = (nh + n1, ph + p1)
  in
    (np0,np1)
  end

(* --------------------------------------------------------------------------
   Execute program and associate its score
   -------------------------------------------------------------------------- *)

fun update_prog_partial pfn (di,wi) (p,dep,exec) = 
  let val (pref,fref,incoming,_) = net_sub pfn (di,wi) in
    pref := p; fref := exec; incoming := dep
  end

val prog_skip = ref 0

fun accuracy (obj,(neg,pos)) =
  if obj <= 0 
  then (if neg > pos then 1 else 0)
  else (if pos > neg then 1 else 0)    
       
fun score_prog cache pfn (di,wi) (inputf,obj) (np0,np1) (p,dep,exec) =
  let 
    val (np,t) = if np0 = np1 then (np0,0) else
      let
        val _ = update_prog_partial pfn (di,wi) (p,dep,exec) 
        val told = !run_time
        val x = recompute_node inputf cache pfn (di,wi)
        val tdiff = !run_time - told
      in
        (if x = 0 then np0 else np1, tdiff)
      end
    val sc = score_negpos (obj,np)
    val acc = accuracy (obj,np)
    val conf = fst np + snd np
  in
    (sc, t, acc, conf)
  end

(* --------------------------------------------------------------------------
   Reference implementation with no optimizations
   -------------------------------------------------------------------------- *)

fun score_nodep pfn (inputf,obj) =
  let 
    val (depth,width) = dim_of_net pfn
    val nodel = cartesian_product 
      (List.tabulate (depth,I)) (List.tabulate (width,I))
    val cache = init_cache pfn
    val tnodel = List.tabulate (width, fn wi => (depth - 1, wi))
    val _ = app (compute_node_once inputf cache pfn) nodel
    fun f node = ! (net_sub cache node) 
    val vl = map_assoc f tnodel
    val negpos = negpos_vl vl
    val sc = score_negpos (obj, negpos)
  in
    (negpos,sc)
  end

fun proba_negpos (neg,pos) =
  let val total = neg + pos in
    if total = 0 then 0.5 else int_div pos total
  end

(* --------------------------------------------------------------------------
   Inference
   -------------------------------------------------------------------------- *)

fun infer pfn inputf =
  let 
    val (depth,width) = dim_of_net pfn
    val nodel = cartesian_product 
      (List.tabulate (depth,I)) (List.tabulate (width,I))
    val cache = init_cache pfn
    val tnodel = List.tabulate (width, fn wi => (depth - 1, wi))
    val _ = app (compute_node_once inputf cache pfn) nodel
    fun f node = ! (net_sub cache node) 
    val vl = map_assoc f tnodel
    val negpos = negpos_vl vl
  in
    proba_negpos negpos
  end


end (* struct *)

(*
load "network"; open aiLib kernel exec prog network;
val pfn = init_pfn (4,1000);

val starttoken = [0,0,0,0];

fun sample_bit proba = if random_real () < proba then 1 else 0;

fun decode_aux pfn l n = if n <= 0 then l else
  let
    val v = Vector.fromList l
    val i = Vector.length v
    fun inputf x = Vector.sub (v, x mod i)
    val proba = infer pfn inputf
    val bit = sample_bit proba
  in
    decode_aux pfn (l @ [bit]) (n-1)
  end;
  
fun decode pfn n = 
  let val l = decode_aux pfn starttoken n in
    snd (part_n (length starttoken) l) 
  end;

val (l,t) = add_time (decode pfn) 1000;





*)
