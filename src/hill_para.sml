structure hill_para :> hill_para =
struct

open HolKernel aiLib kernel exec prog network

val expdir = "/dev/shm/thibault"

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
val stats_freq = ref 100

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
  
fun combine_err (l1,l2) = combine (l1,l2) handle HOL_ERR _ =>
  raise Msg ("combine: " ^ its (length l1) ^ " <> " ^ its (length l2))
  
(* --------------------------------------------------------------------------
   Helpers
   -------------------------------------------------------------------------- *)

fun rmDir_err dir =
  if exists_file dir then OS.FileSys.rmDir dir else ()

val sti = string_to_int 
fun nts (n,p) = (its n ^ "-" ^ its p)
fun stn s = let val (a,b) = split_pair #"-" s in (sti a, sti b) end 

fun its4 (n1,n2,n3,n4) = its n1 ^ "-" ^ its n2 ^ "-" ^ its n3 ^ "-" ^ its n4
fun sti4 s = 
  let val (a,b,c,d) = split_quadruple #"-" s in 
    (sti a, sti b, sti c, sti d) 
  end 

fun random_node (depth,width) = 
  (random_int (0,depth-1), random_int (0,width -1))
  
fun list_add x y = map (fn (x,y) => x + y) (combine_err (x,y));   
fun list_add2 x y = map (fn ((x1,x2),(y1,y2)) => 
  (x1+y1,x2+y2)) (combine_err (x,y)); 
fun list_add3 x y = map (fn ((x1,x2,x3),(y1,y2,y3)) => 
  (x1+y1,x2+y2,x3+y3)) (combine_err (x,y)); 
fun list_add4 x y = map (fn ((x1,x2,x3,x4),(y1,y2,y3,y4)) => 
  (x1+y1,x2+y2,x3+y3,x4+y4)) (combine_err (x,y)); 

fun save_node pfn (di,wi) = 
  let 
    val (p,f,incoming,_) = net_sub pfn (di,wi) 
    val (pold,fold,incomingold) = (!p,!f,!incoming)
    fun restore () = (p := pold; f := fold; incoming := incomingold)
  in
    restore
  end

fun update_prog pfn p node = 
  let val (pref,fref,_,_) = net_sub pfn node in
    pref := p; fref := mk_exec p; update_sdep pfn node
  end
  
fun inv_cmp cmp (a,b) = cmp (b,a)

fun sum_int2 l = case l of [] => (0,0) | (a,b) :: m => 
  let val (c,d) = sum_int2 m in (a + c, b + d) end

fun sum_int4 l = case l of [] => (0,0,0,0) | (a1,b1,c1,d1) :: m => 
  let val (a2,b2,c2,d2) = sum_int4 m in (a1 + a2, b1 + b2, c1 + c2, d1 + d2) end

val szip_prog = infts o zip_prog
val sunzip_prog = unzip_prog o stinf

fun apply_undo () = (app (fn f => f ()) (!resetl_glob); resetl_glob := [])
fun net_all f net = Vector.all (fn v => Vector.all f v) net
fun is_clean cache = net_all (fn x => !x = cache_empty) cache

(* --------------------------------------------------------------------------
   Statistics
   -------------------------------------------------------------------------- *)

val r2 = rts_pad 2
val r4 = rts_pad 4

fun stats rt iter =
  if iter = 0 orelse iter mod !stats_freq <> 0 then () else
  let
    val ku = Real.round (int_div (!run_time) (iter * 1000))
    val t = Time.toReal (Timer.checkRealTimer rt)
    val ti = (t - !stats_timer) / Real.fromInt iter
    fun f (x,t) = if !t < epsilon then NONE else 
                  SOME (x ^ " " ^ r2 (!t), !t) 
    val timers = String.concatWith "s, " 
      (map fst (dict_sort compare_rmax (List.mapPartial f timerl)))
  in
    pe (
       its iter ^ ": statistics" ^
       "\n  iter: " ^ r2 (ti * 1000.0) ^ "ms/i, " ^ its ku ^ "ku/i" ^
       "\n  total " ^ r2 t ^ "s: " ^ timers
       )
   end

(* --------------------------------------------------------------------------
   Communication files
   -------------------------------------------------------------------------- *)

val pl_file = expdir ^ "/pl"
val node_file = expdir ^ "/node"

fun write_pl pl = writel pl_file (map szip_prog pl)
fun read_pl () = map sunzip_prog (readl pl_file)
fun write_node node = writel node_file [nts node]
fun read_node () = stn (hd (readl node_file))

val winner_file = expdir ^ "/winner"
fun write_winner p = writel winner_file [szip_prog p]
fun read_winner () = sunzip_prog (hd (readl winner_file))


fun worker_file wid = expdir ^ "/worker" ^ its wid
fun write_worker wid scorel = 
  writel_atomic (worker_file wid) (map its4 scorel)
fun read_worker wid = map sti4 (readl (worker_file wid))

fun barrier_dir iter = expdir ^ "/iter" ^ its iter

(* --------------------------------------------------------------------------
   Worker
   -------------------------------------------------------------------------- *)

fun barrier file =
  let fun busy () = if exists_file file then () else 
    (OS.Process.sleep (Time.fromReal 0.0001); busy ()) in
    busy ()
  end

fun read_exl (ncore,wid) = 
  let 
    val sentencel = map stil (readl (selfdir ^ "/aaa_test100")) 
    val exltot = ex_of_sentencel sentencel
  in
    List.nth (cut_n ncore exltot, wid)
  end

(* read candidates *)
fun read_pdel pfn =   
  let
    val (node,pl) = (read_node (), read_pl ())
    fun f p = (p, dep_of_prog pfn node p, mk_exec p)
  in
    (node, map f pl)
  end

(* computes previous npl for each example *)
fun npexl_of pfn exl npl01 node =  
  let
    val cache = init_cache pfn
    fun f ((np0,np1),(inputv,obj)) =
      let val x = recompute_node inputv cache pfn node in
        apply_undo (); 
        (if x = 0 then np0 else np1, (inputv,obj))
      end
    val _ = reset_flag := true
    val npexl = map f (combine_err (npl01,exl))
    val _ = reset_flag := false
  in
    npexl
  end

fun update_npexl pfn exl npl01o = case npl01o of 
    SOME (npl01,node) => npexl_of pfn exl npl01 node
  | NONE => map (fn x => (fst (score_nodep pfn x), x)) exl

(* computes scores and memorizes npl01 for next round *)
fun score_npex scorel cache pfn (node,pdel) (np,ex) = 
  let
    val np01 = total_time score01_timer (score_01 cache pfn np node) ex
    val restore = save_node pfn node
    val scl = total_time scoreprog_timer 
      (map (score_prog cache pfn node ex np01)) pdel
    val _ = (apply_undo (); restore ())
  in
    scorel := list_add4 scl (!scorel); np01
  end

fun score_npexl pfn (node,pdel) npexl =
  let
    val _ = reset_flag := true
    val cache = init_cache pfn
    val scorel = ref (List.tabulate (length pdel, fn _ => (0,0,0,0)))
    val npl01 = map (score_npex scorel cache pfn (node,pdel)) npexl
    val _ = reset_flag := false 
  in
    (!scorel,npl01)
  end

fun update_prog_wrapper npl01o pfn =
  let val file = expdir ^ "/winner" in
    if not (exists_file file) then () else
    let val p = read_winner () in update_prog pfn p (snd (valOf npl01o)) end
  end

fun worker s =
  let 
    val _ = (run_time := 0; app (fn (_,r) => r := 0.0) timerl)
    val (ncore,wid) = stn s
    val exl = read_exl (ncore,wid)
    val pfn = read_pfn (expdir ^ "/pfn_init")
    val itertot = sti (hd (readl (expdir ^ "/itertot")))
    val rt = Timer.startRealTimer ()
    fun loop npl01o iter =
      if iter >= itertot then "done" else
      let
        val _ = barrier (barrier_dir iter)
        val _ = total_time gen_timer (update_prog_wrapper npl01o) pfn
        val npexl = total_time npl_timer (update_npexl pfn exl) npl01o
        val (node,pdel) = read_pdel pfn
        val (scorel,npl01) = score_npexl pfn (node,pdel) npexl
        val _ = write_worker wid scorel
        val _ = total_time stats_timer (stats rt) iter
      in
        loop (SOME (npl01,node)) (iter + 1)
      end
  in
    loop NONE 0 
  end

(* --------------------------------------------------------------------------
   Dispatcher
   -------------------------------------------------------------------------- *)

fun random_pl winnerl nprog = mk_fast_set prog_compare_size
  (winnerl @ (List.tabulate (nprog, !random_prog_glob)))

fun dispatcher_send iter winnerl nprog pfn = 
  let 
    val node = random_node (dim_of_net pfn) 
    val pl = random_pl winnerl nprog
  in
    write_node node; write_pl pl; mkDir_err (barrier_dir iter);
    (node,pl)
  end

fun dispatcher_wait_one v wid =
  let 
    val _ = OS.Process.sleep (Time.fromReal 0.0001)
    val r = Vector.sub (v,wid) 
    val file = worker_file wid
  in
    if isSome (!r) orelse not (exists_file file) then () else
    let val x = read_worker wid in remove_file file; r := SOME x end
  end

fun dispatcher_wait_aux v ncore wid =
  if Vector.all (isSome o !) v then () else 
  (
  dispatcher_wait_one v wid;
  dispatcher_wait_aux v ncore ((wid + 1) mod ncore) 
  )

fun dispatcher_wait ncore = 
  let
    val v = Vector.tabulate (ncore, fn _ => ref NONE)
    val _ = dispatcher_wait_aux v ncore 0
    val scll = map (valOf o !) (vector_to_list v)
    val scl = map sum_int4 (list_combine scll)
  in
    scl
  end
  
fun cpl_compare24 cmp1 cmp2 ((a1,b1,c1,d1),(a2,b2,c2,d2)) =
  cpl_compare cmp1 cmp2 ((a1,b1),(a2,b2))
  
val cmp_score = snd_compare (cpl_compare24 Int.compare Int.compare)

fun dispatcher s = 
  let 
    val (s1,s2,s3) = split_triple #" " s
    val ncore = sti s2
    val nprog = sti s3
    val pfn = read_pfn (expdir ^ "/pfn_init")
    val itertot = sti (hd (readl (expdir ^ "/itertot")))
    val sentencel = map stil (readl (selfdir ^ "/aaa_test100")) 
    val exltot = ex_of_sentencel sentencel
    val exln = length exltot
    fun loop oldsc iter winnerl =
      if iter >= itertot then 
        (write_pfn (expdir ^ "/pfn_final") pfn; "done") 
      else 
      let
        val (node,pl) = dispatcher_send iter winnerl nprog pfn
        val scl = dispatcher_wait ncore
        val _ = rmDir_err (barrier_dir iter)
        val (winner,(sc,speed,acc,conf)) = 
          hd (dict_sort cmp_score (combine_err (pl,scl)))
        val _ = update_prog pfn winner node
        val _ = if sc = oldsc then () else
           pe (its iter ^ ": " ^
                    "sc " ^ r4 (int_div sc (exln * scaling)) ^ 
                    ", acc " ^ r4 (int_div acc exln) ^
                    ", conf " ^ r4 (int_div conf exln) ^ 
                    ", speed " ^ r4 (int_div speed exln))
        val _ = write_winner winner
      in
        loop sc (iter + 1) [winner]
      end
  in
    loop 0 0 []
  end

(* --------------------------------------------------------------------------
   Main
   -------------------------------------------------------------------------- *)

fun job s = 
  if String.isPrefix "dispatcher" s then dispatcher s else worker s

fun hill_para ncore nprog (depth,width) itertot =
  let
    val _ = clean_dir expdir
    val _ = write_pfn (expdir ^ "/pfn_init") (init_pfn (depth,width))
    val _ = writel (expdir ^ "/itertot") [its itertot]
    val sl = map nts (List.tabulate (ncore, fn i => (ncore,i)))
    val s = "dispatcher" ^ " " ^ its ncore ^ " " ^ its nprog      
    val _ = parmap_sl (ncore + 1) "hill_para.job" (s :: sl)
  in
    read_pfn (expdir ^ "/pfn_final")
  end 

end (* struct *)

(*
load "hill_para";

PolyML.print_depth 0; 
open kernel aiLib prog exec network hill_para;
PolyML.print_depth 40;

val (depth,width) = (4,10000);
val nprog = 100;
val ncore = 50;
val niter = 1000000;

val pfn = hill_para ncore nprog (depth,width) niter;


*)




