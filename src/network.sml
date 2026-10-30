structure network :> network =
struct

open HolKernel aiLib kernel sexp exec prog

type 'a net = 'a vector vector
type ex = (int vector * (int * int ref * int ref)) list
type cache = (int ref net * (int * int ref * int ref)) list
type pfn = (prog ref * exec ref * int ref * int list ref * int list ref) net
type pn = cache * pfn
type pnx = pn * real

val cache_glob = ref ([]:cache)
val exi_glob = ref 0
val node_counter = ref 0
val node_dep_counter = ref 0
val maxint = valOf Int.maxInt

fun npts (n,p) = (its n ^ " " ^ its p)


(* --------------------------------------------------------------------------
   Debugging
   -------------------------------------------------------------------------- *)
   
fun debugf f = if !debug_flag then pe (f ()) else ()
fun print_cache_one (di,iv) =   
  pe ("layer " ^ its di ^ ": " ^ ilts (map ! (vector_to_list iv)))
      
fun print_cache cache = Vector.appi print_cache_one cache

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

fun net_sub v2 (i,j) = Vector.sub (Vector.sub (v2,i),j);

fun net_tab (d,w) f = 
  Vector.tabulate (d,fn i => Vector.tabulate (w,fn j => f (i,j)))


fun flatten_pn (_,pn) = 
  map (! o #1) (List.concat (map vector_to_list (vector_to_list pn)))

fun pn_compare (pn1,pn2) = 
  list_compare prog_compare (flatten_pn pn1, flatten_pn pn2) 

(* --------------------------------------------------------------------------
   Run program networks: programs have same depth index as their input.
   -------------------------------------------------------------------------- *)

fun get_ref iv i = Vector.sub (iv, i)
fun get_value iv i = ! (get_ref iv i)

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
    val _ = layerv_glob := Vector.map (fn x => ref x) iv
    val r = 
      Vector.tabulate (width, run_node negpos dmax di width pfv (!layerv_glob))
  in
    r
  end

fun runl_aux negpos pn di dmax iv = 
  if di >= dmax then iv else
  runl_aux negpos pn (di + 1) dmax 
    (run_layer negpos dmax di (Vector.sub (pn,di)) iv)

fun runl negpos pn iv = 
  let val _ = inputv_glob := Vector.map (fn x => ref x) iv in
    runl_aux negpos pn 0 (depth_of_net pn) iv
  end
  
(* --------------------------------------------------------------------------
   Evaluate program networks
   -------------------------------------------------------------------------- *)

val conf_penalty = ref 0.00001

fun score_negpos (obj,(negtop,postop)) =
  let 
    val (neg,pos) = (Real.fromInt negtop, Real.fromInt postop)
    val total = neg + pos + 2.0 * !conf_penalty 
    val r = if obj > 0 then pos else neg   
  in
    if total < epsilon then 0.5 else (r + !conf_penalty) / total
  end
  
fun score_obj pfn exi (iv,(obj,_,_)) = 
  let 
    val _ = exi_glob := exi
    val (neg,pos) = (ref 0,ref 0)
    val newiv = runl (neg,pos) pfn iv
  in
    score_negpos (obj,(!neg,!pos))
  end

fun logit x = (*~ (Math.ln x)*) x
fun loss_scl scl = 1.0 - average_real (map logit scl)
  
fun infer_test pfn ex = 
  if null ex then raise Msg "infer_test: empty" else 
  let
    val scl = mapi (score_obj pfn) ex
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
 
fun iv_of_objl w objl = 
  let 
    val obj = hd objl
    val objm = tl objl
    val pobjv = Vector.fromList (0 :: 1 :: 1 :: 1 :: objm)
    val m = Vector.length pobjv
    fun f i = Vector.sub (pobjv, i mod m)
  in
    (Vector.tabulate (w,f), (obj,ref 0,ref 0))
  end  

fun ex_of_sentencel w l = 
  let 
    fun f ex = map (iv_of_objl w) (all_rev_prefixes ex)
    val r = List.concat (map f l)
  in  
    r
  end

fun inputvl_of_ex ex = 
  let
    fun g (v,(obj,_,_)) = 
      (Vector.tabulate (Vector.length v, fn i => ref (Vector.sub (v,i))),
       obj)
  in
    map g ex
  end 

fun objl_of_ex ex = let fun g (_,(obj,_,_)) = obj in map g ex end 

fun cache_of_ex (d,w) ex =
  let
    val _ = pe (its (length ex) ^ " examples")
    fun f v (i,j) = ref (if i = 0 then Vector.sub (v,j) else 0)
    fun g v = net_tab (d+1,w) (f v)
  in
    map_fst g ex
  end 

(* ==========================================================================
   Running the network
   ========================================================================== *)

val undol_glob = ref []

fun init_vcache (d,w) = 
  let
    val maxint = valOf (Int.maxInt)
    fun f di = Vector.tabulate (w, fn wi => ref maxint)
    val pfn = Vector.tabulate (d, f) 
  in
    pfn
  end;

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

(* --------------------------------------------------------------------------
   Computing a node
   -------------------------------------------------------------------------- *)

fun compute_node_once inputv cache pfn (di,wi) =
  let 
    val (pref,fref,_,_,_) = net_sub pfn (di,wi) 
    val (d,w) = dim_of_net cache
    val ov = Vector.sub(cache,di)
    val _ = inputv_glob := inputv
    val _ = layerv_glob := (if di = 0 then inputv else Vector.sub(cache,di-1))
    val _ = self_glob := wi
    val _ = incr node_counter
    val index1 = (wi - 1) mod w
    val i1 = get_value (!layerv_glob) index1
    val index2 = (wi + 1) mod w
    val i2 = get_value (!layerv_glob) index2
    val _ = z_glob := get_value (!layerv_glob) wi
    val onew = (!fref) (i1,i2)
    val oref = get_ref ov wi
    val oold = !oref
    (*
    fun g () = oref := oold
    val _ = undol_glob := g :: !undol_glob
    *)
  in
    oref := onew
  end

fun score_nodep pfn (inputv,obj) =
  let 
    val (depth,width) = dim_of_net pfn
    val nodel = cartesian_product 
      (List.tabulate (depth,I)) (List.tabulate (width,I))
    val cache = init_vcache (depth,width)
    val terminall = List.tabulate (width, fn wi => (depth - 1, wi))
    val _ = app (compute_node_once inputv cache pfn) nodel
    fun f node = ! (net_sub cache node) 
    val vl = map_assoc f terminall
    val negpos = negpos_vl vl
    (* val _ = pe ("nodep: " ^ npts negpos) *)
  in
    score_negpos (obj, negpos)
  end

(* recursively compute nodes and their dependencies *)
fun compute_node inputv cache pfn di wi =
  if ! (net_sub cache (di,wi)) <> maxint then () else
  let 
    val (_,_,_,incoming,_) = Vector.sub(Vector.sub(pfn,di),wi)
    val _ = app (compute_node inputv cache pfn (di-1)) (!incoming) 
  in
    compute_node_once inputv cache pfn (di,wi)
  end

(* recompute the node and dependencies if they have not been computed yet *)
fun recompute_node inputv cache pfn (di,wi) =
  let val x = net_sub cache (di,wi) in 
    x := maxint; compute_node inputv cache pfn di wi
  end

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

(* --------------------------------------------------------------------------
   Computing a layer
   -------------------------------------------------------------------------- *)

fun runc_layer negpos cache pn (d,w) di wil =
  let
    val pv = Vector.sub (pn,di)
    val iv = Vector.sub (cache,di)
    val ov = Vector.sub (cache,di+1)
    val _ = layerv_glob := iv
    val _ = app (runc_node negpos cache (d,w) pv (iv,ov) di) wil
  in
    ()
  end

(* --------------------------------------------------------------------------
   Computing full update
   -------------------------------------------------------------------------- *)

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

fun runcl b (cache,(_,negref,posref)) pfn di wil = 
  let val _ = inputv_glob := Vector.sub (cache,0) in
    runcl_aux (negref,posref) b cache pfn (dim_of_net pfn) di wil
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
  let val (_,_,_,_,outgoing) = net_sub pfn (d',wi) in
    outgoing := filter (fn x => x <> w) (!outgoing)
  end

fun add_sedge pfn (d',w) wi = 
  let val (_,_,_,_,outgoing) = net_sub pfn (d',wi) in
    if mem w (!outgoing) then () else outgoing := w :: !outgoing
  end

fun update_sdep pfn (di,wi) =
  if di <= 0 then () else
  let 
    val w = width_of_net pfn
    val (pref,_,_,incoming,_) = net_sub pfn (di,wi) 
    val newincoming = mk_fast_set Int.compare 
      (map (fn x => (x + wi) mod w) (collect_readargl (!pref)))
    (* val _ = pe (ilts newincoming) *)
    val oldincoming = !incoming  
  in  
    incoming := newincoming;
    app (rm_sedge pfn (di-1,wi)) oldincoming;
    app (add_sedge pfn (di-1,wi)) newincoming
  end

fun recompute_alldep pfn = 
  let fun f (_,di,wi) = update_sdep pfn (di,wi) in
    net_app f pfn
  end
  
fun init_cache ex pfn =
  let
    val cache = cache_of_ex (dim_of_net pfn) ex  
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
   Dependencies
   -------------------------------------------------------------------------- *)
   
fun descendant_aux (d,w) pfn (di,wil) = 
  if di = d-1 then [] else
  let 
    val pv = Vector.sub (pfn,di)
    fun add_dep (wi,dict) = eaddl (! (s55 (Vector.sub (pv,wi)))) dict
    val r =  (di+1, elist (foldl add_dep (eempty Int.compare) wil))
  in
    r :: descendant_aux (d,w) pfn r
  end
  
fun descendant pfn (di,wil) = 
  (di,wil) :: descendant_aux (dim_of_net pfn) pfn (di,wil)

(* --------------------------------------------------------------------------
   Scoring
   -------------------------------------------------------------------------- *)

fun score_cache (cache,(obj,negref,posref)) =
  score_negpos (obj,(!negref,!posref))

fun score_pn (cachel,_) = 
  let val scl = map score_cache cachel in (loss_scl scl ,scl) end


(* --------------------------------------------------------------------------
   Random network used for initialization
   -------------------------------------------------------------------------- *)

fun random_pfn (d,w) = 
  let
    fun f (di,wi) = 
      let val p = (!random_prog_glob) di in 
        (ref p, ref (mk_exec p), ref maxint, ref [], ref []) 
      end
  in
    net_tab (d,w) f
  end



fun random_pnx (d,w) ex =
  let 
    val _ = pe ("init programs: " ^ its d ^ " " ^ its w)
    val pfn = random_pfn (d,w)
    val _ = pe "init cache"
    val cache = init_cache ex pfn
    val pn = (cache,pfn)
    val loss1 = fst (score_pn pn)
    val _ = undol_glob := []
    val _ = pe ("loss cache: " ^ rts_pad 4 loss1)
    val _ = pe "init test"
    val _ = cache_glob := cache
    val (loss2,_) = infer_test pfn ex
    val _ = pe ("loss test: " ^ rts_pad 4 loss2)
    val _ = if Real.abs (loss2 - loss1) > 0.1 
            then raise Msg "mismatch: loss" else ()
  in 
    (pn, loss1)
  end

(* --------------------------------------------------------------------------
   Compute negpos score for a list of terminal nodes and an input example
   -------------------------------------------------------------------------- *)

fun update_prog pfn p (di,wi) = 
  let 
    val (pref,fref,tref,incoming,outgoing) = net_sub pfn (di,wi) 
    val pold = !pref
    val fold = !fref
    val told = !tref
    val incomingold = !incoming
    val outgoingold = !outgoing
    fun undo () = 
      (pref := pold; fref := fold; tref := told; 
       incoming := incomingold;
       outgoing := outgoingold)
  in
    pref := p; fref := mk_exec p; 
    update_sdep pfn (di,wi);
    undo
  end



fun negpos_inputv pfn terminall inputv = 
  let 
    val (depth,width) = dim_of_net pfn
    val cache = init_vcache (depth,width);
    val _ = app (recompute_node inputv cache pfn) terminall
    val vl = map_assoc (! o net_sub cache) terminall
  in
    negpos_vl vl
  end;

fun negpos_01 pfn (di,wi) inputv =
  let 
    val (depth,width) = dim_of_net pfn
    val cache = init_vcache (depth,width);
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
    (* val _ = pe ("base: " ^ npts base) *)
    val r = last (descendant pfn (di,[wi]))
    val terminall = map (fn x => (fst r, x)) (snd r)
    val diff = negpos_inputv pfn terminall inputv
    (* val _ = pe ("diff: " ^ npts base) *)
    val hole = (fst base - fst diff, snd base - snd diff)
    val (negpos0,negpos1) = negpos_01 pfn (di,wi) inputv
    (*
    val _ = pe ("np0: " ^ npts negpos0)
    val _ = pe ("np1: " ^ npts negpos1)
    *)
  in
    score_01_aux ((hole,obj),(negpos0,negpos1))
  end
  
fun score_prog_full pfn (di,wi) (inputv,obj) p =   
  let
    val (depth,width) = dim_of_net pfn
    val cache = init_vcache (depth,width)
    val undo = update_prog pfn p (di,wi)
    val terminall = List.tabulate (width, fn i => (depth - 1,i));
    val negpos = negpos_inputv pfn terminall inputv
    val _ = undo ()
  in
    score_negpos (obj,negpos)
  end
  
fun sameish r1 r2 = Real.abs (r1 - r2) < epsilon  
  
  
  
fun score_prog pfn (di,wi) (inputv,obj) (sc0,sc1) p =
  if sameish sc0 sc1 then sc0 else
  let 
    val (depth,width) = dim_of_net pfn
    val cache = init_vcache (depth,width)
    val undo = update_prog pfn p (di,wi)
    val _ = recompute_node inputv cache pfn (di,wi)
    val sc = if ! (net_sub cache (di,wi)) = 0 then sc0 else sc1
    (* val scfull  = score_prog_full pfn (di,wi) (inputv,obj) p *)
    val _ = undo ()
    (* val undo = update_prog pfn p (di,wi)
       val scfull  = score_nodep pfn (inputv,obj)
       val _ = undo () *)
  in
    sc 
    (* 
    if sameish sc scfull 
    then sc 
    else raise Msg ("score_prog: " ^ rts_pad 4 sc ^ " " ^ rts_pad 4 scfull)
    *)
  end
  

(* --------------------------------------------------------------------------
   Hill climbing loop
   -------------------------------------------------------------------------- *)

fun init_hill (depth,width) sentencel =
  let 
    val pfn = random_pfn (depth,width);
    val _ = recompute_alldep pfn;
    val ex = ex_of_sentencel width sentencel;
    val inputvl = inputvl_of_ex ex
  in
    (pfn,inputvl)
  end

fun random_node (depth,width) = 
  (random_int (0,depth-1), random_int (0,width -1))
  
fun list_radd (x:real list) (y:real list) = 
  map (fn (x,y) => x + y) (combine (x,y));   

fun loop_hill_aux rt inputvl pfn scold nprog n =
  let 
    val (depth,width) = dim_of_net pfn
    val (di,wi) = random_node (depth,width)
    val p = ! (#1 (net_sub pfn (di,wi)))
    val progl = mk_fast_set prog_compare_size (* [p] *)
      (p :: (List.tabulate (nprog, !random_prog_glob)))
    val scorel_glob = ref (List.tabulate (length progl, fn _ => 0.0))
    fun f inputvo = 
      let 
        val (sc0,sc1) = score_01 pfn (di,wi) inputvo
        val r = map (score_prog pfn (di,wi) inputvo (sc0,sc1)) progl
      in
        scorel_glob := list_radd r (!scorel_glob)
      end
    val _ = app f inputvl
    val r = combine (progl,!scorel_glob)
    val scnew = dfind p (dnew prog_compare r) 
    val _ = 
      if scold <= 0.0 then ()
      else if sameish scold scnew then () 
      else raise Msg ("loop_hill: " ^ rts_pad 4 scold ^ " " ^ rts_pad 4 scnew)
    val (prog,sc) = hd (dict_sort compare_rmax r)
    val _ = if sc < scold - epsilon 
            then raise Msg "loop_hill"
            else ()
    val _ = pe (its n ^ ": " ^ 
      rts_pad 4 (sc / Real.fromInt (length inputvl)) (* to optimize ? *)
      ^ " " ^ its di ^ "-" ^ its wi)
    val _ = update_prog pfn prog (di,wi)
    val t = Time.toReal (Timer.checkRealTimer rt) / Real.fromInt n
    val _ =  if n mod 100 <> 0 then () else
      pe (its n ^ " : average time " ^ rts_pad 2 (t * 1000.0) ^ " ms")
  in
    loop_hill_aux rt inputvl pfn sc nprog (n + 1)
  end

fun loop_hill inputvl pfn nprog =
  loop_hill_aux (Timer.startRealTimer ()) inputvl pfn 0.0 nprog 1;

end (* struct *)

(*
load "network"; open aiLib kernel exec prog network;

val sentencel = [[1,0,1,1,0,1]];
val (depth,width) = (4,10);
val (pfn,inputvl) = init_hill (depth,width) sentencel;
val nprog = 1000;
time (loop_hill inputvl pfn) nprog;




  


then print the loss/accuracy/confidence and repeat.


todo: 
1) unify the cache 
2) keep a running score for each program that is the sum of all the previous
   scores (maybe average them in the end for nice human look)
3) choose the program with the best score 
   (maybe later early give up for programs that will never catch up 
    or a competition style tournament)
4) use integer scores to be able to compare identical scores instead of relying
on epsilon.
5) 


*)
