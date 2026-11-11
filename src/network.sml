structure network :> network =
struct

open HolKernel aiLib kernel sexp exec prog

type 'a net = 'a vector vector
type iv = int ref vector
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
 
fun all_suffixes objl = case objl of 
    [] => [] 
  | a :: m => objl :: all_suffixes m 

fun all_rev_prefixes objl = rev (all_suffixes (rev objl));
 
fun exl_of_sentence w sentence = 
  let 
    val obj = hd sentence
    val objm = tl sentence
    val pobjv = Vector.fromList (0 :: 0 :: 0 :: 0 :: objm)
  in
    (pobjv, obj)
  end  

fun ex_of_sentencel w l = 
  let fun f ex = map (exl_of_sentence w) (all_rev_prefixes ex) in  
    List.concat (map f l)
  end

(* --------------------------------------------------------------------------
   Computing a node and its dependencies
   -------------------------------------------------------------------------- *)

val reset_flag = ref false
val resetl_glob = ref []
val cache_empty = valOf Int.maxInt

fun compute_node_once inputv cache pfn (di,wi) =
  let
    val _ = inputv_glob := inputv
    val _ = layerv_glob := (if di = 0 then inputv else Vector.sub(cache,di-1))
    val _ = self_glob := wi
    val (d,w) = dim_of_net cache
    val i1 = ! (Vector.sub (!layerv_glob, (wi - 1) mod w))
    val i2 = ! (Vector.sub (!layerv_glob, (wi + 1) mod w))
    val _ = z_glob := ! (Vector.sub (!layerv_glob, wi))
    val fref = #2 (net_sub pfn (di,wi))
    val onew = (!fref) (i1,i2)
    val oref = net_sub cache (di,wi)
    val _ = if not (!reset_flag) then () else 
      resetl_glob := (fn () => oref := cache_empty) :: !resetl_glob 
  in
    oref := onew
  end

fun compute_node inputv cache pfn di wi =
  if ! (net_sub cache (di,wi)) <> cache_empty then () else
  let 
    val incoming = #3 (net_sub pfn (di,wi))
    val _ = app (compute_node inputv cache pfn (di-1)) (!incoming) 
  in
    compute_node_once inputv cache pfn (di,wi)
  end

fun recompute_node_unit inputv cache pfn (di,wi) =
  let val x = net_sub cache (di,wi) in 
    x := cache_empty; 
    compute_node inputv cache pfn di wi
  end
  
fun recompute_node inputv cache pfn (di,wi) =
  let val x = net_sub cache (di,wi) in 
    x := cache_empty; 
    compute_node inputv cache pfn di wi;
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

(* score out of 1 million *)
val scaling = 1000000000

fun score_negpos (obj,(neg,pos)) =
  let
    val total = neg + pos
    val correct = if obj > 0 then pos else neg   
  in
    if total = 0 then scaling div 2 else (correct * scaling) div total
  end

fun score_negpos2 (obj,(neg,pos)) =
  if obj > 0 then pos - 10 * neg else neg - 10 * pos
  
(* --------------------------------------------------------------------------
   Compute what would be the score if the output of a program was 0 or 1
   -------------------------------------------------------------------------- *)

fun negpos_inputv cache pfn tnodel inputv = 
  negpos_vl (map_assoc (recompute_node inputv cache pfn) tnodel)
  
fun negpos_01 cache pfn (di,wi) inputv (nodel,tnodel) npd =
  let
    val x = net_sub cache (hd nodel)
    val xold = !x    
    fun f a = 
      let 
        val _ = x := a
        val _ = app (recompute_node_unit inputv cache pfn) (tl nodel)
        val vl = map_assoc (! o net_sub cache) tnodel
      in
        negpos_vl vl
      end
    val r = if xold = 0 then (npd, f 1) else (f 0, npd)
    val _ = x := cache_empty
  in
    r
  end

fun score_01 cache pfn (nb,pb) (di,wi) (inputv,obj) = 
  let 
    val (depth,width) = dim_of_net pfn
    val descl = descendant pfn (di,[wi])
    val nodel = distrib descl
    val tnodeline = last descl
    val tnodel = map (fn x => (fst tnodeline, x)) (snd tnodeline)
    val (nd,pd) = negpos_inputv cache pfn tnodel inputv
    val (nh,ph) = (nb - nd, pb - pd)
    val ((n0,p0),(n1,p1)) = 
      negpos_01 cache pfn (di,wi) inputv (nodel,tnodel) (nd,pd)
    val np0 = (nh + n0, ph + p0) 
    val np1 = (nh + n1, ph + p1) 
    val sc0 = score_negpos (obj,np0)
    val sc1 = score_negpos (obj,np1)
  in
    ((np0,np1),(sc0,sc1))
  end

(* --------------------------------------------------------------------------
   Execute program and associate its score
   -------------------------------------------------------------------------- *)

fun update_prog_partial pfn (di,wi) (p,dep,exec) = 
  let val (pref,fref,incoming,_) = net_sub pfn (di,wi) in
    pref := p; fref := exec; incoming := dep
  end

val prog_skip = ref 0

fun score_prog cache pfn (di,wi) (inputv,obj) 
  ((np0,np1),(sc0,sc1)) (p,dep,exec) =
  if sc0 = sc1 then (incr prog_skip; (sc0, 0)) else
  let
    val _ = update_prog_partial pfn (di,wi) (p,dep,exec) 
    val told = !run_time
    val x = recompute_node inputv cache pfn (di,wi)
    val tdiff = !run_time - told
    val sc = if x = 0 then sc0 else sc1
  in
    (sc,tdiff)
  end

(* --------------------------------------------------------------------------
   Reference implementation with no optimizations
   -------------------------------------------------------------------------- *)

fun score_nodep pfn (inputv,obj) =
  let 
    val (depth,width) = dim_of_net pfn
    val nodel = cartesian_product 
      (List.tabulate (depth,I)) (List.tabulate (width,I))
    val cache = init_cache pfn
    val tnodel = List.tabulate (width, fn wi => (depth - 1, wi))
    val _ = app (compute_node_once inputv cache pfn) nodel
    fun f node = ! (net_sub cache node) 
    val vl = map_assoc f tnodel
    val negpos = negpos_vl vl
    val sc = score_negpos (obj, negpos)
  in
    (negpos,sc)
  end



end (* struct *)

(*
load "network"; open aiLib kernel exec prog network;
val pfn = init_pfn (4,1000);
write_pfn "aaa_test" pfn;
val newpfn = read_pfn "aaa_test";
pfn_compare (pfn,newpfn);
*)
