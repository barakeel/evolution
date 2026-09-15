structure network :> network =
struct

open HolKernel aiLib kernel sexp exec prog

type 'a net = 'a vector vector
type cache = ((int ref * int list ref * int list ref) net * (int * int)) list
type pfn = (prog ref * exec ref) net
type pn = cache * pfn
type pnx = pn * real * int
type ex = (int vector * (int * int)) list

fun debugf f = if !debug_flag then pe (f ()) else ()

val cache_glob = ref ([]:cache)
val exi_glob = ref 0
val node_counter = ref 0

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
  let val (_,_,outgoing) = Vector.sub (Vector.sub (cache,d),wi) in
    if mem w (!outgoing) then () else outgoing := w :: (!outgoing)
  end

fun rm_edge cache (d,w) wi =
  let val (_,_,outgoing) = Vector.sub (Vector.sub (cache,d),wi) in
    outgoing := filter (fn x => x <> w) (!outgoing)
  end

fun update_depl cache (d,w) depl =
  let 
    val (_,incoming,_) = Vector.sub (Vector.sub (cache,d+1),w) 
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
   Run program networks: programs have same depth index as their input.
   -------------------------------------------------------------------------- *)

fun s13 (a,b,c) = a
fun s33 (a,b,c) = c
fun get_ref iv i = s13 (Vector.sub (iv, i))
fun get_value iv i = ! (get_ref iv i)

fun print_cache_one (di,iv) =   
  pe ("layer " ^ its di ^ ": " ^ ilts (map (! o s13) (vector_to_list iv)))
      
fun print_cache cache = Vector.appi print_cache_one cache

fun run_node di width fv iv i =
  let
    val (pref,fref) = Vector.sub (fv, i)
    val i1 = get_value iv ((i - 1) mod width)       
    val i2 = get_value iv ((i + 1) mod width)
    val _ = z_glob := get_value iv i
    val r = (!fref) (i1,i2)
    val cache = fst (List.nth (!cache_glob, !exi_glob))
    val (r',_,_) = Vector.sub (Vector.sub (cache,di+1),i)
  in
    if !r' = r then r else
    (
    pe ( 
       "node " ^ its di ^ " " ^ its i ^ "\n" ^
       "program: " ^ string_of_prog (!pref) ^ "\n" ^
       "input: x " ^ its i1 ^ " y "  ^ its i2 ^ " z " ^ its (!z_glob) ^ "\n" ^
       "output: " ^ its r ^ " does not match cache " ^ its (!r'))
    ;
    print_endline "cache";
    print_cache cache;
    raise Msg "mismatch"
    )   
  end

fun run_layer di fv iv = 
  let
    val width = Vector.length fv 
    val _ = iv_glob := Vector.map (fn x => (ref x, ref [], ref [])) iv
    val _ = debug ("layer " ^ its di ^ ": " ^ ilts (vector_to_list iv))
    val r = Vector.tabulate (width, run_node di width fv (!iv_glob))
  in
    r
  end

fun runl_aux pn di dmax iv = 
  if di >= dmax then iv else
  runl_aux pn (di + 1) dmax (run_layer di (Vector.sub (pn,di)) iv)

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

fun score_obj pn exi (iv,obj) = 
  let 
    val _ = exi_glob := exi
    val newiv = runl pn iv
    val _ = debugf (fn () => "output: " ^ ilts (vector_to_list newiv))
    val (neg,pos) = count newiv
    val sc = if obj > 0 then pos else neg 
  in
    sc
  end

fun logit n x = if x <= 0 then 100000000.0 else 0.0 - Math.ln (int_div x n)

fun score_exone pfn exi (iv,(obj,_)) = score_obj pfn exi (iv, obj)
  
fun infer_test pfn ex = 
  if null ex then raise Msg "infer_test: empty" else 
  let 
    val w = width_of_net pfn
    val scl = mapi (score_exone pfn) ex
    val sclpos = filter (fn x => x > w div 2) scl
    val acc = int_div (length sclpos) (length scl)
    val loss = sum_real (map (logit w) scl)
  in
    pe ("test loss " ^ rts_pad 3 loss ^ ", test acc " ^ rts_pad 3 acc);
    (loss, acc)
  end


(* --------------------------------------------------------------------------
   Initialize cache from examples
   -------------------------------------------------------------------------- *)
 
fun all_suffixes objl = case objl of 
    [] => [] 
  | a :: m => objl :: all_suffixes m 

fun all_rev_prefixes objl = rev (all_suffixes (rev objl));
 
fun iv_of_objl w tokenpos objl = 
  let 
    val obj = hd objl
    val objm = tl objl
    val pobjv = Vector.fromList (0 :: 1 :: 1 :: 1 :: objm)
    val m = Vector.length pobjv
    fun f i = Vector.sub (pobjv, i mod m)
  in
    (Vector.tabulate (w,f), (obj,tokenpos))
  end  

fun vol_of_sentencel w l = 
  let 
    fun f ex = mapi (iv_of_objl w) (all_rev_prefixes ex)
    val r = List.concat (map f l)
  in  
    r
  end

fun vol_of_exol exol = 
  let fun f (inputl,output) = (Vector.fromList inputl, (output,0)) in
    map f exol
  end
 

fun cache_of_vol (d,w) vol =
  let
    val _ = pe (its (length vol) ^ " examples")
    fun g v = Vector.tabulate (d+1, fn i => 
     Vector.tabulate (w, fn j => 
      (ref (if i = 0 then Vector.sub (v,j) else 0) ,ref [],ref [])))
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


fun runc_node cache (d,w) pv (iv,ov) di wi =
  let
    val _ = node_counter := !node_counter + 1
    val (pref,fref) = Vector.sub (pv, wi)
    val (p,f) = (!pref,!fref)
    val _ = if !dep_flag then access_glob := [] else ()
    val index1 = (wi - 1) mod w
    val i1 = if !dep_flag then access (contain_id_fo x_id p) iv index1 else
      get_value iv index1
    val index2 = (wi + 1) mod w
    val i2 = if !dep_flag then access (contain_id_fo y_id p) iv index2 else
      get_value iv index2
    val _ = z_glob := (if !dep_flag then access (contain_id z_id p) iv wi else     
      get_value iv wi)
    val r = f (i1,i2)
    val oref = get_ref ov wi
    val oold = !oref
    fun g () = oref := oold
    val _ = undol_glob := g :: !undol_glob
    val _ = if !dep_flag then update_depl cache (di,wi) (!access_glob) else ()
  in
    oref := r
  end

fun runc_layer cache pn (d,w) di wil =
  let
    val pv = Vector.sub (pn,di)
    val iv = Vector.sub (cache,di)
    val ov = Vector.sub (cache,di+1)
    val _ = debugf (fn () => 
      "layer " ^ its di ^ ": " ^ ilts (map (! o s13) (vector_to_list iv)))
    val _ = iv_glob := iv
    val _ = app (runc_node cache (d,w) pv (iv,ov) di) wil
    val _ = debugf (fn () => 
      "edges " ^ its di ^ "-" ^ its (di+1) ^ ": " ^ 
      String.concatWith "," (map (ilts o ! o s33) (vector_to_list iv)))
  in
    ()
  end
 
val nodep_flag = ref false 
 
fun runcl_aux b cache pn (d,w) di wil = 
  if di >= d then () else
  let
    val newwil = if b then List.tabulate (w,I) else 
      let 
        val ov = Vector.sub (cache,di+1)
        fun dep_of wi = ! (s33 (Vector.sub (ov,wi)))
      in
        mk_fast_set Int.compare (List.concat (map dep_of wil))
      end
    val () = runc_layer cache pn (d,w) di wil
  in
    runcl_aux b cache pn (d,w) (di+1) newwil
  end

fun dim_of_net pn = (depth_of_net pn, width_of_net pn)

fun output_layer cache = Vector.sub (cache, Vector.length cache - 1)

fun runcl b cache pn di wil = 
   let 
     val _ = runcl_aux b cache pn (dim_of_net pn) di wil
     val _ = debugf (fn () => 
       "output: "  ^ ilts (map (! o s13) (vector_to_list (output_layer cache))))
   in
     ()
   end

fun update_cache_full (cachel,pfn) = 
  let val wil = List.tabulate (width_of_net pfn, I) in
    app (fn x => runcl true (fst x) pfn 0 wil) cachel
  end
  
fun update_cache (cachel,pfn) (di,wil) = 
  app (fn x => runcl false (fst x) pfn di wil) cachel  
  
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

fun update_pn pn (p,di,wi) = 
  let 
    val (pref,fref) = Vector.sub (Vector.sub (snd pn,di), wi) 
    val (pold,fold) = (!pref,!fref)
    fun f () = (pref := pold; fref := fold)
    val _ = undol_glob := f :: !undol_glob
    val _ = (pref := p; fref := mk_exec_safe p)
    val _ = if !nodep_flag 
            then update_cache_full pn 
            else update_cache pn (di,[wi])
    (*
    val nc = !node_counter 
    val nc' = !node_counter - nc
    val (depth,width) = dim_of_net (snd pn)
    val nex = length (fst pn)
    *)
  in
    (* pe ("nodes: " ^ its nc' ^ "/" ^ its (depth * width * nex)); *)
    ()
  end

(* --------------------------------------------------------------------------
   Scoring
   -------------------------------------------------------------------------- *)


fun input_layer cache = Vector.sub (cache, 0)

fun count_ref ov = 
  let 
    val (neg,pos) = (ref 0,ref 0)
    fun f (i,x) = if ! (s13 x) > 0 then incr pos else incr neg
    val _ = Vector.appi f ov
  in
    (!neg,!pos)
  end

fun score_cache_one (cache,(obj,tokenpos)) =
  let
    val iv = input_layer cache
    val ov = output_layer cache 
    val (neg,pos) = count_ref ov
  in
    if obj > 0 then pos else neg
  end 
    
(* todo: only recompute the score partially *)
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
    val _ = dep_flag := true
    val _ = pe "init programs"
    fun f i = Vector.tabulate (w, fn _ => 
      let val p = random_prog () in (ref p, ref (mk_exec_safe p)) end 
      )
    val pfn = Vector.tabulate (d, f)
    val _ = pe "init cache"
    val cache = init_cache vol pfn
    val pn = (cache,pfn)
    val loss1 = fst (score_pn pn)
    val _ = undol_glob := []
    val _ = pe ("loss cache: " ^ rts_pad 4 loss1)
    val _ = pe "init infer"
    val _ = cache_glob := cache
    val (loss2,acc2) = infer_test pfn vol
    val _ = pe ("loss infer: " ^ rts_pad 4 loss2)
    val _ = dep_flag := false
  in 
    (pn, loss1, valOf (Int.maxInt))
  end

end (* struct *)

(*
todo:  print cache with structre
load "network"; open aiLib kernel exec prog network;
val targetl1 = [0,1,1,0,0,1];
val width = 10;
val vol = vol_of_sentencel width [targetl1];
debug_flag := true;
val (_,_,_) = random_pnx (4,width) vol;

*)
