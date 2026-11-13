structure hill :> hill =
struct

open HolKernel aiLib kernel exec prog network

(* --------------------------------------------------------------------------
   Profiling
   -------------------------------------------------------------------------- *)
    
val dep_timer = ref 0.0
val score01_timer = ref 0.0
val scoreprog_timer = ref 0.0
val stats_timer = ref 0.0
val minor_timer = ref 0.0
val init_timer = ref 0.0
val gen_timer = ref 0.0
val npl_timer = ref 0.0
val stats_freq = ref 1000


val timerl = [
  ("sc01", score01_timer),
  ("dep", dep_timer),
  ("scp", scoreprog_timer),
  ("init", init_timer),
  ("gen", gen_timer),
  ("stats", stats_timer),
  ("minor", minor_timer),
  ("npl", npl_timer)
  ]  
  
(* --------------------------------------------------------------------------
   Helpers
   -------------------------------------------------------------------------- *)

fun sameish r1 r2 = Real.abs (r1 - r2) < epsilon  
fun nts (n,p) = (its n ^ "-" ^ its p)
fun npts (n,p) = (its n ^ "_" ^ its p)

fun random_node (depth,width) = 
  (random_int (0,depth-1), random_int (0,width -1))
  
fun list_add x y = map (fn (x,y) => x + y) (combine (x,y));   
fun list_add2 x y = map (fn ((x1,x2),(y1,y2)) => 
  (x1+y1,x2+y2)) (combine (x,y)); 

fun save_node pfn (di,wi) = 
  let 
    val (p,f,incoming,_) = net_sub pfn (di,wi) 
    val (pold,fold,incomingold) = (!p,!f,!incoming)
    fun restore () = (p := pold; f := fold; incoming := incomingold)
  in
    restore
  end

fun update_prog pfn p (di,wi) = 
  let val (pref,fref,_,_) = net_sub pfn (di,wi) in
    pref := p; fref := mk_exec p; update_sdep pfn (di,wi)
  end

fun inv_cmp cmp (a,b) = cmp (b,a)

(* --------------------------------------------------------------------------
   Statistics
   -------------------------------------------------------------------------- *)

val r2 = rts_pad 2
val r4 = rts_pad 4

val prog_glob = ref (Ins (0,[]))

fun accuracy npscl nex = 
  int_div (length (filter (fn x => snd x > scaling div 2) npscl)) nex
fun confidence npscl nex = 
  int_div (sum_int (map (fn ((a,b),_) => a + b) npscl)) nex  
fun hscore sc nex = (int_div sc scaling) / (Real.fromInt nex)

fun stats_hill nprog rt (exl,nex) pfn n sc =
  if n mod !stats_freq <> 0 then () else
  let
    val npscl = map (score_nodep pfn) exl
    val sctrue = sum_int (map snd npscl)
    val hsc = hscore sctrue nex
    val acc = accuracy npscl nex
    val conf = confidence npscl nex
    val _  = 
      if sc = sctrue then () else 
      raise Msg ("mismatch: optimized" ^ its sc ^ ", basic " ^ its sctrue)
    val ku = Real.round (int_div (!run_time) (n * 1000))
    val t = Time.toReal (Timer.checkRealTimer rt)
    val ti = (t - !stats_timer) / Real.fromInt n
    fun f (x,t) = if !t < epsilon then NONE else 
                  SOME (x ^ " " ^ r2 (!t), !t) 
    val timers = String.concatWith "s, " 
      (map fst (dict_sort compare_rmax (List.mapPartial f timerl)))
  in
    pe (
      its n ^ ": statistics" ^ "\n  " ^ 
      "iter: " ^ r2 (ti * 1000.0) ^ "ms/i, " ^ its ku ^ "ku/i" ^ "\n  " ^
      "total " ^ r2 t ^ "s: " ^ timers ^ "\n  " ^
      "sc " ^ r4 hsc ^ ", acc " ^ r4 acc ^ ", conf " ^ r4 conf ^ "\n  " ^
      "last change: " ^ string_of_prog (!prog_glob) ^ "\n  " ^
      "prog skip: " ^ r4 (int_div (!prog_skip) (nprog * n * nex))
       )
   end

fun report n sc scold nex npscl (di,wi) = 
  if sc = scold then () else 
  let 
    val hsc = hscore sc nex
    val acc = accuracy npscl nex
    val conf = confidence npscl nex
  in 
    pe (its n ^ ": " ^ 
    "sc " ^ r4 hsc ^ ", acc " ^ r4 acc ^ ", conf " ^ r4 conf ^ 
    ", node " ^ nts (di,wi))
  end

(* --------------------------------------------------------------------------
   Hill climbing initialization
   -------------------------------------------------------------------------- *)

fun init_hill (depth,width) sentencel =
  let 
    val _ = (run_time := 0; app (fn (_,r) => r := 0.0) timerl)
    val pfn = init_pfn (depth,width)
    val exl = ex_of_sentencel sentencel
    val npl = map (fst o score_nodep pfn) exl
  in
    (pfn,exl,npl)
  end

fun apply_undo () = (app (fn f => f ()) (!resetl_glob); resetl_glob := [])
fun net_all f net = Vector.all (fn v => Vector.all f v) net
fun is_clean cache = net_all (fn x => !x = cache_empty) cache

(* --------------------------------------------------------------------------
   Main computation
   -------------------------------------------------------------------------- *)
 
fun compute_scorel cache pfn (di,wi) pdel candl =
  let 
    fun f () = ref (List.tabulate (length pdel, fn _ => (0,0)))
    val scorel = total_time minor_timer f ()
    fun f (np,ex) = 
      let
        val np = total_time score01_timer 
          (score_01 cache pfn np (di,wi)) ex
        val restore = save_node pfn (di,wi)
        val r = total_time scoreprog_timer 
          (map (score_prog cache pfn (di,wi) ex np)) pdel
        val _ = (apply_undo (); restore ())
      in
        scorel := list_add2 (map (fn (x,y,z,w) => (x,y)) r) (!scorel); np
      end
    val _ = reset_flag := true
    val npl01 = map f candl
    val _ = reset_flag := false
  in
    (npl01, !scorel)
  end

(* --------------------------------------------------------------------------
   Winner re-computation
   -------------------------------------------------------------------------- *)

fun npscl_of_winner cache pfn (di,wi) exl npscl01 winner =  
  let
    val restore = save_node pfn (di,wi)
    val _ = update_prog_partial pfn (di,wi) 
      (winner, dep_of_prog pfn (di,wi) winner, mk_exec winner)
    fun f (inputv,obj) =
      let val x = recompute_node inputv cache pfn (di,wi) in
        apply_undo (); x
      end
    val _ = reset_flag := true
    val nodeol = map f exl
    val _ = reset_flag := false
    val _ = restore ()
    fun f (((np0,np1),(sc0,sc1)),nodeo) = 
      if nodeo = 0 then (np0,sc0) else (np1,sc1)
  in
    map f (combine (npscl01, nodeol))
  end

(* --------------------------------------------------------------------------
   Hill climbing loop
   --------------------------------------------------------------------------*) 

fun loop_hill_aux nprog cache rt (exl,nex) pfn nplold scold n =   
  let
    val (depth,width) = dim_of_net pfn
    val (di,wi) = total_time minor_timer random_node (depth,width)
    val p = ! (#1 (net_sub pfn (di,wi)))
    fun f () = mk_fast_set prog_compare_size
      (p :: (List.tabulate (nprog, !random_prog_glob)))
    val progl = total_time gen_timer f ()
    val npexl = combine (nplold,exl)
    fun f p = (p, dep_of_prog pfn (di,wi) p, mk_exec p)
    val pdel = total_time gen_timer (map f) progl
    val (npl01,scorel) = compute_scorel cache pfn (di,wi) pdel npexl
    fun f () =
      let val cmp = 
        snd_compare (cpl_compare (inv_cmp Int.compare) Int.compare) 
      in
        hd (dict_sort cmp (combine (progl,scorel))) 
      end
    val (winner,(sc,_)) = total_time minor_timer f ()
    val npscl = total_time npl_timer 
      (npscl_of_winner cache pfn (di,wi) exl npl01) winner
    val _ = total_time minor_timer 
      (report n sc scold nex npscl) (di,wi)
    val _ = update_prog pfn winner (di,wi)
    val _ = prog_glob := winner
    val _ = total_time stats_timer (stats_hill nprog rt (exl,nex) pfn n) sc
    val nplnew = map fst npscl
  in 
    loop_hill_aux nprog cache rt (exl,nex) pfn nplnew sc (n + 1)
  end

fun loop_hill nprog (pfn,exl,npl) =
  let 
    val nex = length exl
    val cache = init_cache pfn
    val rt = Timer.startRealTimer ()
    val _ = prog_skip := 0
    val _ = pe ("training on " ^ its nex ^ " examples")
  in
    loop_hill_aux nprog cache rt (exl,nex) pfn npl (~1) 1
  end



end (* struct *)

(*
load "hill";

PolyML.print_depth 0; 
open kernel aiLib prog exec network hill;
val sentencel = map stil (readl "aaa_test100");
val (depth,width) = (4,1024);
val nprog = 100;
val init = init_hill (depth,width) (first_n 10 sentencel);
PolyML.print_depth 40;

stats_freq := 1000;
time (loop_hill nprog) init;
(* warning: cannot restart without init_hill first *)

todo:
  and test the best of the other ones (this could be also done without 
  parallelization)
- idea: only recompute time for winners
- early give up for programs that will never catch up 
  or a competition style tournament
- could do a batch for all the nodes (so that no repetition occurs)

*)




