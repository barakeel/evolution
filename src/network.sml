structure network :> network =
struct

open HolKernel aiLib kernel sexp exec prog

type 'a net = 'a vector vector
type cache = ((int ref * int list ref * int list ref) net * 
  (int * int * int ref)) list
type pfn = 
  (prog ref * exec ref * (bool * bool * bool) option ref * int ref) net
type pn = cache * pfn
type pnx = pn * real * int
type ex = (int vector * (int * int * int ref)) list

fun debugf f = if !debug_flag then pe (f ()) else ()

val cache_glob = ref ([]:cache)
val exi_glob = ref 0
val node_counter = ref 0
val node_dep_counter = ref 0

val mod_glob = ref 1

fun width_of_net net = Vector.length (Vector.sub (net,0))
fun depth_of_net net = Vector.length net
fun dim_of_net pn = (depth_of_net pn, width_of_net pn)

fun flatten_pn (_,pn) = 
  map (! o #1) (List.concat (map vector_to_list (vector_to_list pn)))

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
   Run program networks: programs have same depth index as their input.
   -------------------------------------------------------------------------- *)

fun s13 (a,b,c) = a
fun s33 (a,b,c) = c
fun get_ref iv i = s13 (Vector.sub (iv, i))
fun get_value iv i = ! (get_ref iv i)

fun print_cache_one (di,iv) =   
  pe ("layer " ^ its di ^ ": " ^ ilts (map (! o s13) (vector_to_list iv)))
      
fun print_cache cache = Vector.appi print_cache_one cache

fun run_node di width pfv iv i =
  let
    val _ = self_glob := i
    val (pref,fref,_,_) = Vector.sub (pfv, i)
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

fun run_layer di pfv iv = 
  let
    val width = Vector.length pfv 
    val _ = iv_glob := Vector.map (fn x => (ref x, ref [], ref [])) iv
    val _ = 
      debugf (fn () => ("layer " ^ its di ^ ": " ^ ilts (vector_to_list iv)))
    val r = Vector.tabulate (width, run_node di width pfv (!iv_glob))
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

fun count tokenpos iv = 
  let 
    val (neg,pos) = (ref 0,ref 0)
    fun f (i,x) = 
      (* if (i - tokenpos) mod (!mod_glob) = 0 
         then if x > 0 then incr pos else incr neg
         else ()  *)
      if i mod 2 = 0 andalso x > 0 then incr pos
      else if i mod 2 = 1 andalso x > 0 then incr neg
      else ()
   
    val _ = Vector.appi f iv
  in
    (!neg,!pos)
  end

fun score_obj pn exi (iv,obj,tokenpos) = 
  let 
    val _ = exi_glob := exi
    val newiv = runl pn iv
    val _ = debugf (fn () => "output: " ^ ilts (vector_to_list newiv))
    val (neg,pos) = count tokenpos newiv
    val sc = if neg + pos = 0 then 0.5 else 
      int_div (if obj > 0 then pos else neg) (neg + pos)  
  in
    sc
  end

fun logit n x = if x > n then raise Msg ("logit: " ^ its x) else
                if x <= 0 then 100000000.0 else 0.0 - Math.ln (int_div x n)

fun score_exone pfn exi (iv,(obj,tokenpos,_)) = 
  score_obj pfn exi (iv,obj,tokenpos)
  
fun infer_test pfn ex = 
  if null ex then raise Msg "infer_test: empty" else 
  let 
    val w = width_of_net pfn
    val w' = w div (!mod_glob)
    val scl = mapi (score_exone pfn) ex
    val sclpos = filter (fn x => x > 0.5) scl
    val acc = int_div (length sclpos) (length scl)
    val loss = sum_real (map (logit w') scl)
  in
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
    (Vector.tabulate (w,f), (obj,tokenpos,ref 0))
  end  

fun vol_of_sentencel w l = 
  let 
    fun f ex = mapi (iv_of_objl w) (all_rev_prefixes ex)
    val r = List.concat (map f l)
  in  
    r
  end

fun vol_of_exol exol = 
  let fun f (inputl,output) = (Vector.fromList inputl, (output,0,ref 0)) in
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
val tokenpos_glob = ref 0

val x_id = get_id "x"
val y_id = get_id "y"
val z_id = get_id "z"


(* test *)
fun runc_node scref cache (d,w) pv (iv,ov) di wi =
  let
    val _ = self_glob := wi
    val _ = incr node_counter
    val (pref,fref,_,_) = Vector.sub (pv, wi)
    val index1 = (wi - 1) mod w
    val i1 = get_value iv index1
    val index2 = (wi + 1) mod w
    val i2 = get_value iv index2
    val _ = z_glob := get_value iv wi
    val r = (!fref) (i1,i2)
    val oref = get_ref ov wi
    val oold = !oref
    fun g () = oref := oold
    val _ = undol_glob := g :: !undol_glob
    val _ = 
      if di = d - 1 andalso (wi - !tokenpos_glob) mod (!mod_glob) = 0 then
        if r > 0 andalso oold <= 0 
          then (incr scref; 
                undol_glob := (fn () => decr scref) :: !undol_glob)
        else if r <= 0 andalso oold > 0 
          then (decr scref; 
                undol_glob := (fn () => incr scref) :: !undol_glob)
        else ()
      else ()
  in
    oref := r
  end

(* final pass *)
fun runc_node_dep scref cache (d,w) pv (iv,ov) di wi =
  let
    val _ = self_glob := wi
    val _ = incr node_dep_counter
    val (pref,fref,blref,_) = Vector.sub (pv, wi)
    val (p,f) = (!pref,!fref)
    val (b1,b2,b3) = case !blref of SOME x => x | NONE => 
      let val r = 
        (contain_id_fo x_id p, contain_id_fo y_id p, contain_id z_id p)
      in
        blref := SOME r; r
      end
    val _ = access_glob := []
    val index1 = (wi - 1) mod w
    val i1 = access b1 iv index1
    val index2 = (wi + 1) mod w
    val i2 = access b2 iv index2
    val _ = z_glob := access b3 iv wi
    val r = f (i1,i2)
    val oref = get_ref ov wi
    val oold = !oref
    val _ = update_depl cache (di,wi) (!access_glob)
    val _ = 
      if di = d - 1 andalso (wi - !tokenpos_glob) mod (!mod_glob) = 0 then
        if r > 0 andalso oold <= 0 then incr scref
        else if r <= 0 andalso oold > 0 then decr scref
        else ()
      else ()
  in
    oref := r
  end

fun runc_layer scref cache pn (d,w) di wil =
  let
    val pv = Vector.sub (pn,di)
    val iv = Vector.sub (cache,di)
    val ov = Vector.sub (cache,di+1)
    val _ = iv_glob := iv
    val _ = if !dep_flag 
            then app (runc_node_dep scref cache (d,w) pv (iv,ov) di) wil
            else app (runc_node scref cache (d,w) pv (iv,ov) di) wil
  in
    ()
  end
 
val fullupdate_flag = ref false 
 
fun runcl_aux scref b cache pn (d,w) di wil = 
  if di >= d then () else
  let
    val newwil = if b then List.tabulate (w,I) else 
      let 
        val ov = Vector.sub (cache,di+1)
        fun add_dep (wi,d) = eaddl (! (s33 (Vector.sub (ov,wi)))) d
      in
        elist (foldl add_dep (eempty Int.compare) wil)
      end
    val () = runc_layer scref cache pn (d,w) di wil
  in
    runcl_aux scref b cache pn (d,w) (di+1) newwil
  end



fun output_layer cache = Vector.sub (cache, Vector.length cache - 1)

fun count_pos v = 
  let 
    val pos = ref 0
    fun f (i,x) = if !(s13 x) > 0 then incr pos else ()
  in
    Vector.appi f v; !pos
  end

fun runcl b (cache,(_,tokenpos,scref)) pn di wil = 
   let 
     val _ = tokenpos_glob := tokenpos
     val _ = runcl_aux scref b cache pn (dim_of_net pn) di wil
   in
     ()
   end

fun update_cache_full (cachel,pfn) = 
  let val wil = List.tabulate (width_of_net pfn, I) in
    app (fn x => runcl true x pfn 0 wil) cachel
  end
  
val full_flag = ref false  
  
fun update_cache (cachel,pfn) (di,wil) = 
  if !full_flag 
  then update_cache_full (cachel,pfn)
  else app (fn x => runcl false x pfn di wil) cachel  
  
(* --------------------------------------------------------------------------
   Initialization and updates
   -------------------------------------------------------------------------- *)
  
fun init_cache vol pfn =
  let
    val cache = cache_of_vol (dim_of_net pfn) vol  
    val wil = List.tabulate (width_of_net pfn, I) 
    val _ = dep_flag := true
    val _ = update_cache_full (cache,pfn)
    val _ = dep_flag := false
  in
    cache
  end

fun update_pn pn (p,di,wi) = 
  let
    val (pref,fref,blref,tref) = Vector.sub (Vector.sub (snd pn,di), wi) 
    val (pold,fold,blold,told) = (!pref,!fref,!blref,!tref)
    fun f () = (pref := pold; fref := fold; blref := blold; tref := told)
    val _ = undol_glob := f :: !undol_glob
    val _ = (pref := p; fref := mk_exec_safe p; blref := NONE)
    val r = !run_time
    val _ = update_cache pn (di,[wi])
    val _ = tref := !run_time - r
  in
    ()
  end

(* --------------------------------------------------------------------------
   Scoring
   -------------------------------------------------------------------------- *)


fun input_layer cache = Vector.sub (cache, 0)

(*
fun count_ref ov = 
  let 
    val (neg,pos) = (ref 0,ref 0)
    fun f (i,x) = if ! (s13 x) > 0 then incr pos else incr neg
    val _ = Vector.appi f ov
  in
    (!neg,!pos)
  end
*)

(*
fun score_cache_one (cache,(obj,tokenpos,scref)) =
  let
    val ov = output_layer cache 
    val (neg,pos) = count_ref ov
  in
    if obj > 0 then pos else neg
  end 
*)

fun score_cache w' (cache,(obj,tokenpos,scref)) =
  if obj > 0 then !scref else w' - !scref

(*
  let 
    val r0 = 
    (* val r1 = score_cache_one (cache,(obj,tokenpos,scref)) *)
  in
    (* if r1 <> r0 then raise Msg "score: mismatch" else *) r0
  end
*)   

fun score_pn (cachel,_) = 
  let
    val w = width_of_net (fst (hd cachel))
    val w' = w div (!mod_glob)
    val scl = map (score_cache w') cachel
    val sc = sum_real (map (logit w') scl)
  in
    (sc,scl)
  end

fun random_pnx (d,w) vol =
  let 
    val _ = pe "init programs"
    val maxint = valOf Int.maxInt
    fun f i = Vector.tabulate (w, fn _ => 
      let val p = random_prog () in (ref p, ref (mk_exec_safe p), ref NONE
      , ref maxint) 
      end 
      )
    val pfn = Vector.tabulate (d, f)
    val _ = pe "init cache"
    val cache = init_cache vol pfn
    val pn = (cache,pfn)
    val loss1 = fst (score_pn pn)
    val _ = undol_glob := []
    val _ = pe ("loss cache: " ^ rts_pad 4 loss1)
    val _ = pe "init test"
    val _ = cache_glob := cache
    val (loss2,_) = infer_test pfn vol
    val _ = pe ("loss test: " ^ rts_pad 4 loss2)
    val _ = if Real.abs (loss2 - loss1) > 0.1 
            then raise Msg "mismatch: loss" else ()
  in 
    (pn, loss1, valOf (Int.maxInt))
  end

end (* struct *)

(*
load "network"; open aiLib kernel exec prog network;
val targetl1 = [0,1,1,0,0,1];
val width = 10;
val vol = vol_of_sentencel width [targetl1];
debug_flag := true;
val (_,_,_) = random_pnx (4,width) vol;

*)
