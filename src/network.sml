structure network :> network =
struct

open HolKernel aiLib kernel sexp exec prog

type 'a net = 'a vector vector
type cache = (int ref * int list ref * int list ref) net * (int * int)) list
type pfn = (prog ref * exec ref) net
type pn = cache * pfn
type pnx = pn * real * int
type ex = (int ref vector * (int * int)) list

fun width_of_net net = Vector.length (Vector.sub (net,0))
fun depth_of_net net = Vector.length net

fun flatten_pn (_,pn) = 
  map (! o fst) (List.concat (map vector_to_list (vector_to_list pn)))

fun pn_compare (pn1,pn2) = 
  list_compare prog_compare (flatten_pn pn1, flatten_pn pn2) 

(* --------------------------------------------------------------------------
   Dependency graph
   -------------------------------------------------------------------------- *)

fun add_edge cache (d,w) wi = 
  let val (_,_,outgoing) = Vector.sub (Vector.sub (cache, d - 1),wi) in
    if mem w outgoing then () else outgoing := w :: outgoing
  end

fun rm_edge cache (d,w) wi =
  let val (_,_,outgoing) = Vector.sub (Vector.sub (cache,d - 1),wi) in
    outgoing := filter (fn x => x <> w) outgoing
  end

fun update_depl cache (d,w) depl =
  let 
    val (_,incoming,_) = Vector.sub (Vector.sub (cache,d),w) 
    val olddepl = !incoming  
  in
    incoming := depl;
    app (rm_edge cache (d,w)) olddepl;
    app (add_edge cache (d,w)) depl
  end

(* --------------------------------------------------------------------------
   I/O for program networks
   -------------------------------------------------------------------------- *)

(*
fun write_pn file pn = 
  let 
    val width = width_of_net pn
    val depth = depth_of_net pn
    val pl = flatten_pn pn
    val pil = map zip_prog pl
    val s = cws [its width, its depth] ^ " " ^ cws (map infts pil)
  in
    writel file [s]
  end
  
fun read_pnx file = 
   case tws (hd (readl file)) of
     ws :: ds :: psl => 
     let 
       val (sc,t) = (streal scs, stint ts)
       val (width,depth) = (stint ws, stint ds) 
       fun f p = (ref p, ref (mk_exec_safe p))
       val pl = map (f o unzip_prog o stinf) psl  
       val pll = mk_batch_full width pl
     in
       (Vector.fromList (map Vector.fromList pll), sc, t)
     end
   | _ => raise Msg "read_pn"
*)

(* --------------------------------------------------------------------------
   Run program networks
   -------------------------------------------------------------------------- *)

fun run_node width fv iv i =
  let
    val (_,fref) = Vector.sub (fv, i)
    val i1 = Vector.sub (iv, (i - 1) mod width)       
    val i2 = Vector.sub (iv, (i + 1) mod width)
    val _ = z_glob := Vector.sub  (iv, i)
  in
    (!fref) (i1,i2)
  end

fun run_layer fv iv = 
  let
    val width = Vector.length fv 
    val _ = iv_glob := Vector.map ref iv
    val r = Vector.tabulate (width, run_node width fv iv)
  in
    r
  end

fun runl_aux pn di dmax iv = 
  if di >= dmax then iv else
  runl_aux pn (di + 1) dmax (run_layer (Vector.sub (pn,di)) iv)

fun runl pn iv = runl_aux pn 0 (depth_of_net pn) iv

(* --------------------------------------------------------------------------
   Evaluate program networks
   -------------------------------------------------------------------------- *)

fun count iv = 
  let 
    val (neg,pos) = (ref 0,ref 0)
    fun f (i,x) = if x > 0 then incr pos else incr neg      
    val _ = Vector.appi f iv
  in
    (!neg,!pos)
  end

fun score_obj pn (iv,obj) = 
  let 
    val newiv = runl pn iv
    val (neg,pos) = count newiv
    val sc = if obj > 0 then pos else neg 
  in
    sc
  end

fun iv_of_objl n objl = 
  let 
    val pobjv = Vector.fromList (1 :: 1 :: 1 :: 1 :: rev objl)
    val m = Vector.length pobjv
    fun f i = Vector.sub (pobjv, i mod m)
  in
    Vector.tabulate (n,f)
  end

fun logit n x = if x <= 0 then 100000000.0 else 0.0 - Math.ln (int_div x n)

fun score_exone pfn (iv,(obj,_)) = score_obj pfn (Vector.map ! iv, obj)
  
fun infer_test pfn ex = 
  if null ex then raise Msg "infer_test: empty" else 
  let 
    val w = width_of_net pfn
    val scl = map (score_exone pfn) ex
    val sclpos = filter (fn x => x > w div 2) scl
    val acc = int_div (length sclpos) (length scl)
    val loss = sum_real (map (logit w) scl)
  in
    pe ("test loss " ^ rts_round 3 loss ^ 
        ", test accuracy " ^ rts_round 3 acc);
    (loss, acc)
  end


(* --------------------------------------------------------------------------
   Initialize cache from examples
   -------------------------------------------------------------------------- *)
 
fun all_suffixes objl = case objl of 
    [] => [] 
  | a :: m => objl :: all_suffixes m 

fun all_rev_prefixes objl = rev (all_suffixes (rev objl));
 
fun iv_of_objl_ref w tokenpos objl = 
  let 
    val obj = hd objl
    val objm = tl objl
    val pobjv = Vector.fromList (1 :: 1 :: 1 :: 1 :: objm)
    val m = Vector.length pobjv
    fun f i = ref (Vector.sub (pobjv, i mod m))
  in
    (Vector.tabulate (w,f), (obj,tokenpos))
  end  

fun vol_of_sentencel w l = 
  let 
    fun f ex = mapi (iv_of_objl_ref w) (all_rev_prefixes ex)
    val r = List.concat (map f l)
  in  
    r
  end

fun vol_of_exol exol = 
  let fun f (inputl,output) = 
    (Vector.fromList (map ref inputl), (output,0)) 
  in
    map f exol
  end
 

fun cache_of_vol (d,w) vol =
  let
    val _ = pe (its (length vol) ^ " examples")
    fun g v = Vector.tabulate (d+1, 
      fn i => if i = 0 then v else Vector.tabulate (w, fn _ => ref 0))
  in
    map_fst g vol
  end 

(* --------------------------------------------------------------------------
   Running the network
   -------------------------------------------------------------------------- *)

val undol_glob = ref []  

val x_id = get_id "x"
val y_id = get_id "y"
val z_id = get_id "z"

fun runc_node pv (iv,ov) w wi =
  let
    val (pref,fref) = Vector.sub (pv, wi)
    val (p,f) = (!pref,!fref)
    val _ = if !dep_flag then access_glob := [] else ()
    val i1 = !
      (
      if !dep_flag 
      then access (contain_id_fo x_id p) iv ((wi - 1) mod w) 
      else Vector.sub (iv, (wi - 1) mod w)
      )   
    val i2 = !
      (
      if !dep_flag 
      then access (contain_id_fo y_id p) iv ((wi + 1) mod w) 
      else Vector.sub (iv, (wi + 1) mod w)
      ) 
    val _ = z_glob := ! 
      (
      if !dep_flag 
      then access (contain_id z_id p) iv wi 
      else Vector.sub (iv,wi)     
      )
    val r = f (i1,i2)
    val oref = Vector.sub (ov, wi)
    val oold = !oref
    fun g () = oref := oold
    val _ = undol_glob := g :: !undol_glob
  in
    oref := r
  end

fun runc_layer cache pn (d,w) di wil =
  let
    val pv = Vector.sub (pn,di)
    val iv = Vector.sub (cache,di)
    val ov = Vector.sub (cache,di+1)
    val _ = iv_glob := iv
  in
    app (runc_node pv (iv,ov) w) wil
  end

fun runcl_aux cache pn (d,w) di wil = 
  if di >= d then () else
  let 
    val () = runc_layer cache pn (d,w) di wil 
    val newwil = List.tabulate (w,I)  
  in
    runcl_aux cache pn (d,w) (di+1) newwil
  end

fun dim_of_net pn = (depth_of_net pn, width_of_net pn)

fun runcl cache pn di wil = runcl_aux cache pn (dim_of_net pn) di wil

fun update_cache_full (cachel,pfn) = 
  let val wil = List.tabulate (width_of_net pfn, I) in
    app (fn x => runcl (fst x) pfn 0 wil) cachel
  end
  
(* --------------------------------------------------------------------------
   Initialization and updates
   -------------------------------------------------------------------------- *)
  
fun init_cache vol pfn =
  let
    val cache = cache_of_vol (dim_of_net pfn) vol  
    val wil = List.tabulate (width_of_net pfn, I) 
    val _ = update_cache_full (cache,pfn)
  in
    cache
  end

fun update_cache (cache,pn) (di,wi) = 
  app (fn x => runcl (fst x) pn di [wi]) cache

fun update_pn pfn (p,di,wi) = 
  let 
    val (pref,fref) = Vector.sub (Vector.sub (snd pfn,di), wi) 
    val (pold,fold) = (!pref,!fref)
    fun f () = (pref := pold; fref := fold)
    val _ = undol_glob := f :: !undol_glob
    val _ = (pref := p; fref := mk_exec_safe p)
  in
    update_cache_full pfn
  end

(* --------------------------------------------------------------------------
   Scoring
   -------------------------------------------------------------------------- *)

fun output_layer cache = Vector.sub (cache, Vector.length cache - 1)

fun count_ref tokenpos ov = 
  let 
    val (neg,pos) = (ref 0,ref 0)
    fun f (i,x) = if !x > 0 then incr pos else incr neg
    val _ = Vector.appi f ov
  in
    (!neg,!pos)
  end

fun score_cache_one (cache,(obj,tokenpos)) =
  let 
    val ov = output_layer cache 
    val (neg,pos) = count_ref tokenpos ov
  in
    if obj > 0 then pos else neg
  end 
    
fun score_pn (cache,_) = 
  let
    val width = width_of_net (fst (hd cache))
    val scl = map score_cache_one cache
    val sc = sum_real (map (logit width) scl)
  in
    (sc,scl)
  end

fun random_pnx (d,w) vol =
  let 
    fun f i = Vector.tabulate (w, fn _ => 
      let val p = random_prog () in (ref p, ref (mk_exec_safe p)) end 
      )
    val pfn = Vector.tabulate (d, f)
    val cache = init_cache vol pfn
    val pn = (cache,pfn)
    val loss1 = fst (score_pn pn)
    val (loss2,acc2) = infer_test pfn vol
  in 
    pe ("cached: " ^ rts_pad 2 loss1 ^ ", " ^  "plain: " ^ rts_pad 2 loss2);
    (pn, loss1, valOf (Int.maxInt))
  end

end (* struct *)


(* 
load "network"; open aiLib kernel exec prog network;
val targetl1 = [0,1,1,0,0];
val targetl2 = [1,1,0];
val width = 100;
val vol = vol_of_sentencel width [targetl1, targetl2];

PolyML.print_depth 10;
val (pn,_,_) = random_pnx (8,width) vol;


val (sc,scl) = score_cache cache;


val access_line = ref []
val access_network = ref []
val obj_network = ref []


(*
val _ = self_glob := i
  val _ = access_glob := []
access_line := !access_glob :: !access_line; 
  val _ = access_line := []
 val _ = obj_network := r :: !obj_network
 val _ = access_network := rev (!access_line) :: !access_network
  *)
  
 (* let 
    val _ = access_network := []
    val _ = obj_network := [iv]
    val r =
    val _ = access_network := rev (!access_network)
    val _ = obj_network := rev (!obj_network)
  in
    r
  end
 *)  
    
(* todo: improve the dependencies tracking *)


val width = 40;
val iv = iv_of_objl width targetl2;
val (pnet,_,_) = random_pnx (width,4);

val fnet = mk_fnet pvl;
val r = runl fnet iv;



fun mk_depv width accessl = 
  let
    val depv = Vector.tabulate (width, fn _ => ref ([]: int list))
    fun update_dep (j,i)  = 
      let val l = Vector.sub (depv,i) in l := j :: !l end;
    val pairl = distrib ((number_fst 0) accessl)
  in
    app update_dep pairl;
    depv
  end;

val depnetwork = map (mk_depv width) (!access_network);

fun dep_of_aux depnetwork acc depl = case depnetwork of 
    [] => rev acc 
  | v :: m =>
  let 
    fun f x = ! (Vector.sub (v, x))
    val newdepl = mk_fast_set Int.compare (List.concat (map f depl))
  in
    dep_of_aux m (newdepl :: acc) newdepl
  end;
  
fun dep_of depnetwork x = dep_of_aux depnetwork [[x]] [x];

val r = dep_of depnetwork 6;


fun compute_fast p (wi,di) net = 
  let
    val node = Vector.sub (Vector.sub (net,di),wi) 
    val f = mk_exec_safe p
    val i1 = access b1 (iv, (i - 1) mod width)       
    val i2 = access b2 (iv, (i + 1) mod width)
    val _ = z_glob := access b3 (iv, i)
    val output = #output node
    val org = !output
    fun restore () = output := org
    
  in
    (restorel := restore :: restorel; output := f (#input node))
  end

depv;
todo: modify a single node and only update the affected part of the network.
!obj_network;

0) update the program at position i
1) look up the previous input and recompute the output for position i
2) look up the dependencies on the second layer  
3) recompute the dependencies on the second layer
4) see if it would affect any relevant output (hard to say because they might need the results for later), maybe the last layer could be like that as it is not used but this is complicating things.








pe (String.concatWith "\n" 
  (map string_of_prog (first_n 10 (flatten_pvl pvl))));

*)

