structure network :> network =
struct

open HolKernel aiLib kernel sexp exec prog

type 'a net = 'a vector vector
type iv = int ref vector
type ex = iv * int
type cache = int ref net
type pfn = (prog ref * exec ref * int ref * int list ref * int list ref) net
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
    fun add_dep (wi,dict) = eaddl (! (#5 (Vector.sub (pv,wi)))) dict
    val r =  (di+1, elist (foldl add_dep (eempty Int.compare) wil))
  in
    r :: descendant_aux (d,w) pfn r
  end
  
fun descendant pfn (di,wil) = 
  (di,wil) :: descendant_aux (dim_of_net pfn) pfn (di,wil) 
  
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
    val pobjv = Vector.fromList (0 :: 1 :: 1 :: 1 :: objm)
    val m = Vector.length pobjv
    fun f i = ref (Vector.sub (pobjv, i mod m))
  in
    (Vector.tabulate (w,f), obj)
  end  

fun ex_of_sentencel w l = 
  let fun f ex = map (exl_of_sentence w) (all_rev_prefixes ex) in  
    List.concat (map f l)
  end

(* --------------------------------------------------------------------------
   Computing a node and its dependencies
   -------------------------------------------------------------------------- *)

fun compute_node_once inputv cache pfn (di,wi) =
  let 
    val (pref,fref,_,_,_) = net_sub pfn (di,wi) 
    val (d,w) = dim_of_net cache
    val ov = Vector.sub(cache,di)
    val _ = inputv_glob := inputv
    val _ = layerv_glob := (if di = 0 then inputv else Vector.sub(cache,di-1))
    val _ = self_glob := wi
    val index1 = (wi - 1) mod w
    val i1 = ! (Vector.sub (!layerv_glob, index1))
    val index2 = (wi + 1) mod w
    val i2 = ! (Vector.sub (!layerv_glob, index2))
    val _ = z_glob := ! (Vector.sub (!layerv_glob, wi))
    val onew = (!fref) (i1,i2)
    val oref = Vector.sub (ov,wi)
  in
    oref := onew
  end

val cache_empty = valOf Int.maxInt

fun compute_node inputv cache pfn di wi =
  if ! (net_sub cache (di,wi)) <> cache_empty then () else
  let 
    val (_,_,_,incoming,_) = net_sub pfn (di,wi)
    val _ = app (compute_node inputv cache pfn (di-1)) (!incoming) 
  in
    compute_node_once inputv cache pfn (di,wi)
  end

fun recompute_node inputv cache pfn (di,wi) =
  let val x = net_sub cache (di,wi) in 
    x := cache_empty; compute_node inputv cache pfn di wi
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
  let val (_,_,_,_,outgoing) = net_sub pfn (d',wi) in
    outgoing := filter (fn x => x <> w) (!outgoing)
  end

fun add_sedge pfn (d',w) wi = 
  let val (_,_,_,_,outgoing) = net_sub pfn (d',wi) in
    if mem w (!outgoing) then () else outgoing := w :: !outgoing
  end

fun update_sdep pfn (di,wi) =
  let 
    val w = width_of_net pfn
    val (pref,_,_,incoming,_) = net_sub pfn (di,wi) 
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
        (ref p, ref (mk_exec p), ref (valOf Int.maxInt), ref [], ref []) 
      end
    val pfn = net_tabulate (d,w) f
    val _ = recompute_alldep pfn
  in
    pfn
  end

fun init_cache (d,w) = net_tabulate (d,w) (fn _ => ref cache_empty)

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

val conf_penalty = ref 0.00001

fun score_negpos (obj,(negtop,postop)) =
  let 
    val (neg,pos) = (Real.fromInt negtop, Real.fromInt postop)
    val total = neg + pos + 2.0 * !conf_penalty 
    val r = if obj > 0 then pos else neg   
  in
    if total < epsilon then 0.5 else (r + !conf_penalty) / total
  end

fun update_prog_partial pfn (di,wi) (p,dep) = 
  let 
    val (pref,fref,_,incoming,_) = net_sub pfn (di,wi) 
    val pold = !pref
    val fold = !fref
    val incomingold = !incoming
    fun undo () = (pref := pold; fref := fold; incoming := incomingold)
  in
    pref := p; fref := mk_exec p; incoming := dep; undo
  end
  
(* these could probably work on a shared cache *)
fun negpos_inputv pfn terminall inputv = 
  let 
    val (depth,width) = dim_of_net pfn
    val cache = init_cache (depth,width);
    val _ = app (recompute_node inputv cache pfn) terminall
    val vl = map_assoc (! o net_sub cache) terminall
  in
    negpos_vl vl
  end;

fun negpos_01 pfn (di,wi) inputv =
  let 
    val (depth,width) = dim_of_net pfn
    val cache = init_cache (depth,width);
    val r = descendant pfn (di,[wi])
    val r' = last r
    val terminall = map (fn x => (fst r', x)) (snd r');
    val nodel = distrib r
    val x = net_sub cache (hd nodel);
    fun f a = 
      let 
        val _ = x := a
        val _ = app (recompute_node inputv cache pfn) (tl nodel)
        val vl = map_assoc (! o net_sub cache) terminall
      in
        negpos_vl vl
      end
  in
    (f 0, f 1)
  end; 

fun score_01_aux (((negh,posh),obj),((neg0,pos0),(neg1,pos1))) = 
  (score_negpos (obj,(negh + neg0, posh + pos0)),
   score_negpos (obj,(negh + neg1, posh + pos1)));


fun score_01 pfn (di,wi) (inputv,obj) = 
  let 
    val (depth,width) = dim_of_net pfn
    val allterminall = List.tabulate (width, fn i => (depth - 1,i));
    val base = negpos_inputv pfn allterminall inputv
    val r = last (descendant pfn (di,[wi]))
    val terminall = map (fn x => (fst r, x)) (snd r)
    val diff = negpos_inputv pfn terminall inputv
    val hole = (fst base - fst diff, snd base - snd diff)
    val (negpos0,negpos1) = negpos_01 pfn (di,wi) inputv
  in
    (negpos0 = negpos1, score_01_aux ((hole,obj),(negpos0,negpos1)))
  end

fun score_prog cache pfn (di,wi) (inputv,obj) (b,(sc0,sc1)) (p,dep) =
  if b then sc0 else
  let
    val undo = update_prog_partial pfn (di,wi) (p,dep) 
    val _ = recompute_node inputv cache pfn (di,wi)
            handle Subscript => raise Msg "recompute_node"
    val sc = (if ! (net_sub cache (di,wi)) = 0 then sc0 else sc1)
             handle Subscript => raise Msg "sc" 
    val _ = undo ()
  in
    sc 
  end

fun score_nodep pfn (inputv,obj) =
  let 
    val (depth,width) = dim_of_net pfn
    val nodel = cartesian_product 
      (List.tabulate (depth,I)) (List.tabulate (width,I))
    val cache = init_cache (depth,width)
    val terminall = List.tabulate (width, fn wi => (depth - 1, wi))
    val _ = app (compute_node_once inputv cache pfn) nodel
    fun f node = ! (net_sub cache node) 
    val vl = map_assoc f terminall
    val negpos = negpos_vl vl
    val sc = score_negpos (obj, negpos)
  in
    (sc,negpos)
  end



end (* struct *)

(*
load "network"; open aiLib kernel exec prog network;

val sentencel = [[1,0,1,1,0,0,1,0,1,1,1,1,1,0,0,0,0,1]];
val (depth,width) = (4,100);
val (pfn,exl) = init_hill (depth,width) sentencel;
val nprog = 1000;
time (loop_hill exl pfn) nprog;

todo:  
3) choose the program with the best score 
   (maybe later early give up for programs that will never catch up 
    or a competition style tournament)
4) use integer scores to be able to compare identical scores instead of relying
on epsilon.
*)
