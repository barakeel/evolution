structure network :> network =
struct

open HolKernel aiLib kernel sexp exec prog

type 'a net = 'a vector vector
type cache = (int ref net * (int * int * int ref * int ref)) list
type pfn = (prog ref * exec ref * int ref * int list ref * int list ref) net
type pn = cache * pfn
type pnx = pn * real
type ex = (int vector * (int * int * int ref * int ref)) list

fun debugf f = if !debug_flag then pe (f ()) else ()

val cache_glob = ref ([]:cache)
val exi_glob = ref 0
val node_counter = ref 0
val node_dep_counter = ref 0

fun width_of_net net = Vector.length (Vector.sub (net,0))
fun depth_of_net net = Vector.length net
fun dim_of_net pn = (depth_of_net pn, width_of_net pn)

fun net_app f net = 
  let fun g (di,line) = Vector.appi (fn (wi,x) => f (x,di,wi)) line in
    Vector.appi g net
  end

fun flatten_pn (_,pn) = 
  map (! o #1) (List.concat (map vector_to_list (vector_to_list pn)))

fun pn_compare (pn1,pn2) = 
  list_compare prog_compare (flatten_pn pn1, flatten_pn pn2) 

(* --------------------------------------------------------------------------
   Run program networks: programs have same depth index as their input.
   -------------------------------------------------------------------------- *)

fun get_ref iv i = Vector.sub (iv, i)
fun get_value iv i = ! (get_ref iv i)

fun print_cache_one (di,iv) =   
  pe ("layer " ^ its di ^ ": " ^ ilts (map ! (vector_to_list iv)))
      
fun print_cache cache = Vector.appi print_cache_one cache


fun negpos_update2 wi (negref,posref) r =
  if r > 0 then (if wi mod 2 = 0 then incr negref else incr posref) else ()

fun run_node negpos dmax di width pfv iv wi =
  let
    val _ = self_glob := wi
    val (pref,fref,_,_,_) = Vector.sub (pfv, wi)
    val i1 = get_value iv ((wi - 1) mod width)       
    val i2 = get_value iv ((wi + 1) mod width)
    val _ = z_glob := get_value iv wi
    val r = (!fref) (i1,i2)
    val _ = if di = dmax - 1 then negpos_update2 wi negpos r else ()
    val cache = fst (List.nth (!cache_glob, !exi_glob))
    val r' = Vector.sub (Vector.sub (cache,di+1),wi)
  in
    if !r' = r then r else
    (
    pe ( 
       "node " ^ its di ^ " " ^ its wi ^ "\n" ^
       "program: " ^ string_of_prog (!pref) ^ "\n" ^
       "input: x " ^ its i1 ^ " y "  ^ its i2 ^ " z " ^ its (!z_glob) ^ "\n" ^
       "output: " ^ its r ^ " does not match cache " ^ its (!r'))
    ;
    print_endline "cache";
    print_cache cache;
    raise Msg "mismatch"
    )   
  end

fun run_layer negpos dmax di pfv iv = 
  let
    val width = Vector.length pfv 
    val _ = iv_glob := Vector.map (fn x => ref x) iv
    val r = 
      Vector.tabulate (width, run_node negpos dmax di width pfv (!iv_glob))
  in
    r
  end

fun runl_aux negpos pn di dmax iv = 
  if di >= dmax then iv else
  runl_aux negpos pn (di + 1) dmax 
    (run_layer negpos dmax di (Vector.sub (pn,di)) iv)

fun runl negpos pn iv = runl_aux negpos pn 0 (depth_of_net pn) iv

(* --------------------------------------------------------------------------
   Evaluate program networks
   -------------------------------------------------------------------------- *)

val conf_penalty = ref 0.00001

fun score_negpos obj (negtop,postop) =
  let 
    val (neg,pos) = (Real.fromInt negtop, Real.fromInt postop)
    val total = neg + pos + 2.0 * !conf_penalty 
    val r = if obj > 0 then pos else neg   
  in
    if total <= epsilon then 0.5 else (r + !conf_penalty) / total
  end
  
fun score_obj pn exi (iv,obj,tokenpos) = 
  let 
    val _ = exi_glob := exi
    val (neg,pos) = (ref 0,ref 0)
    val newiv = runl (neg,pos) pn iv
  in
    score_negpos obj (!neg,!pos)
  end

fun logit x = (*~ (Math.ln x)*) x
fun loss_scl scl = 1.0 - average_real (map logit scl)

fun score_exone pfn exi (iv,(obj,tokenpos,_,_)) = 
  score_obj pfn exi (iv,obj,tokenpos)
  
fun infer_test pfn ex = 
  if null ex then raise Msg "infer_test: empty" else 
  let
    val scl = mapi (score_exone pfn) ex
    val sclpos = filter (fn x => x > 0.5) scl
    val acc = int_div (length sclpos) (length scl)
    val loss = loss_scl scl
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
    (Vector.tabulate (w,f), (obj,tokenpos,ref 0,ref 0))
  end  

fun vol_of_sentencel w l = 
  let 
    fun f ex = mapi (iv_of_objl w) (all_rev_prefixes ex)
    val r = List.concat (map f l)
  in  
    r
  end

fun cache_of_vol (d,w) vol =
  let
    val _ = pe (its (length vol) ^ " examples")
    fun g v = 
     Vector.tabulate (d+1, fn i => 
     Vector.tabulate (w, fn j => 
       ref (if i = 0 then Vector.sub (v,j) else 0)
     ))
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
fun negpos_update wi (negref,posref) oold onew =
  if onew > 0 andalso oold <= 0 then 
    let val f = 
      if wi mod 2 = 0 
      then (fn () => decr negref) 
      else (fn () => decr posref)
    in
      if wi mod 2 = 0 then incr negref else incr posref; 
      undol_glob := f :: !undol_glob
    end
  else if onew <= 0 andalso oold > 0 then 
    let val f = 
      if wi mod 2 = 0 
      then (fn () => incr negref) 
      else (fn () => incr posref)
    in
      if wi mod 2 = 0 then decr negref else decr posref; 
      undol_glob := f :: !undol_glob
    end
  else ()

fun runc_node negpos cache (d,w) pv (iv,ov) di wi =
  let
    val _ = self_glob := wi
    val _ = incr node_counter
    val (pref,fref,_,_,_) = Vector.sub (pv, wi)
    val index1 = (wi - 1) mod w
    val i1 = get_value iv index1
    val index2 = (wi + 1) mod w
    val i2 = get_value iv index2
    val _ = z_glob := get_value iv wi
    val onew = (!fref) (i1,i2)
    val oref = get_ref ov wi
    val oold = !oref
    fun g () = oref := oold
    val _ = undol_glob := g :: !undol_glob
    val _ = if di = d - 1 then negpos_update wi negpos oold onew else ()
  in
    oref := onew
  end

fun runc_layer negpos cache pn (d,w) di wil =
  let
    val pv = Vector.sub (pn,di)
    val iv = Vector.sub (cache,di)
    val ov = Vector.sub (cache,di+1)
    val _ = iv_glob := iv
    val _ = app (runc_node negpos cache (d,w) pv (iv,ov) di) wil
  in
    ()
  end

fun s55 (_,_,_,_,outgoing) = outgoing
 
fun runcl_aux negpos b cache pfn (d,w) di wil = 
  if di >= d then () else
  let
    val newwil = if b then List.tabulate (w,I) else 
      let 
        val pv = Vector.sub (pfn,di)
        fun add_dep (wi,dict) = eaddl (! (s55 (Vector.sub (pv,wi)))) dict
      in
        elist (foldl add_dep (eempty Int.compare) wil)
      end
    val () = runc_layer negpos cache pfn (d,w) di wil
  in
    runcl_aux negpos b cache pfn (d,w) (di+1) newwil
  end

fun output_layer cache = Vector.sub (cache, Vector.length cache - 1)

fun runcl b (cache,(_,tokenpos,negref,posref)) pfn di wil = 
   let 
     val _ = tokenpos_glob := tokenpos
     val _ = runcl_aux (negref,posref) b cache pfn (dim_of_net pfn) di wil
   in
     ()
   end

fun update_cache_full (cachel,pfn) = 
  let val wil = List.tabulate (width_of_net pfn, I) in
    app (fn x => runcl true x pfn 0 wil) cachel
  end

fun update_cache (cachel,pfn) (di,wil) = 
  app (fn x => runcl false x pfn di wil) cachel  
  
(* --------------------------------------------------------------------------
   Initialization and updates
   -------------------------------------------------------------------------- *)

(* could replace with a set for better performance for large 
number of connections *)

fun rm_sedge pfn (d',w) wi =
  let val (_,_,_,_,outgoing) = Vector.sub (Vector.sub (pfn,d'),wi) in
    outgoing := filter (fn x => x <> w) (!outgoing)
  end

fun add_sedge pfn (d',w) wi = 
  let val (_,_,_,_,outgoing) = Vector.sub (Vector.sub (pfn,d'),wi) in
    if mem w (!outgoing) then () else outgoing := w :: !outgoing
  end

fun update_sdep pfn (p,di,wi) =
  if di <= 0 then () else
  let 
    val w = width_of_net pfn
    val newincoming = mk_fast_set Int.compare 
      (map (fn x => (x + wi) mod w) (collect_readargl p))
    val (_,_,_,incoming,_) = Vector.sub (Vector.sub (pfn,di),wi) 
    val oldincoming = !incoming  
  in  
    incoming := newincoming;
    app (rm_sedge pfn (di-1,wi)) oldincoming;
    app (add_sedge pfn (di-1,wi)) newincoming
  end

fun recompute_alldep pfn = 
  let fun f (x,di,wi) = 
    if di <= 0 then () else update_sdep pfn (! (#1 x),di,wi) 
  in
    net_app f pfn
  end
  
fun init_cache vol pfn =
  let
    val cache = cache_of_vol (dim_of_net pfn) vol  
    val wil = List.tabulate (width_of_net pfn, I)
    val _ = update_cache_full (cache,pfn)
    val _ = recompute_alldep pfn
  in
    cache
  end

fun update_pn pn (p,di,wi) = 
  let
    val (pref,fref,tref,_,_) = 
      Vector.sub (Vector.sub (snd pn,di), wi) 
    val (pold,fold,told) = (!pref,!fref,!tref)
    fun f () = 
     (pref := pold; fref := fold; tref := told)
    val _ = undol_glob := f :: !undol_glob
    val _ = (pref := p; fref := mk_exec p)
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

fun score_cache (cache,(obj,tokenpos,negref,posref)) =
  score_negpos obj (!negref,!posref)

fun score_pn (cachel,_) = 
  let val scl = map score_cache cachel in (loss_scl scl ,scl) end

fun random_pnx (d,w) vol =
  let 
    val _ = pe "init programs"
    val maxint = valOf Int.maxInt
    fun f di = Vector.tabulate (w, fn wi => 
      let val p = (!random_prog_glob) di in 
        (ref p, ref (mk_exec p), ref maxint, ref [], ref []) 
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
    (pn, loss1)
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
