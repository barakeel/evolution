structure hill_para :> hill_para =
struct

open HolKernel aiLib kernel exec prog network

(* --------------------------------------------------------------------------
   Helpers
   -------------------------------------------------------------------------- *)

fun combine_err (l1,l2) = combine (l1,l2) handle HOL_ERR _ =>
  raise Msg ("combine: " ^ its (length l1) ^ " <> " ^ its (length l2))

fun rmDir_err dir =
  if exists_file dir then OS.FileSys.rmDir dir else ()

fun create_fifo path =
  Posix.FileSys.mkfifo (path, 
    Posix.FileSys.S.flags [Posix.FileSys.S.irusr, Posix.FileSys.S.iwusr])

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
   Communication files
   -------------------------------------------------------------------------- *)

val shmdir = "/dev/shm/thibault"
val expname_glob = ref "default" 
fun expdir () = selfdir ^ "/exp/" ^ !expname_glob
fun read_exl trainfile  = 
  let 
    val l1 = map stil (readl trainfile)
    val l2 = ex_of_sentencel l1
  in
    pe (its (length l2) ^ " examples from " ^ its (length l1) ^ " sentences");
    l2
  end

(* dispatcher files *)
fun dispatcher_fifo wid = shmdir ^ "/dispatcher" ^ its wid ^ "fifo"
fun send_dispatcher_fifo wid =
  let val out = TextIO.openOut (dispatcher_fifo wid) in
    TextIO.output (out, "go\n"); TextIO.closeOut out
  end
fun receive_dispatcher_fifo wid = 
  let 
    val stream = TextIO.openIn (dispatcher_fifo wid)
    val line = TextIO.inputLine stream
    val _ = TextIO.closeIn stream
  in
    case line of
      NONE => raise Msg ("receive_dispatcher_fifo: " ^ its wid)
    | SOME _ => ()
  end

val pl_file = shmdir ^ "/pl"
val node_file = shmdir ^ "/node"
fun write_pl pl = writel pl_file (map szip_prog pl)
fun read_pl () = map sunzip_prog (readl pl_file)
fun write_node node = writel node_file [nts node]
fun read_node () = stn (hd (readl node_file))
val winner_file = shmdir ^ "/winner"
fun write_winner po = case po of 
     NONE => writel winner_file ["nowinner"] 
   | SOME p => writel winner_file [szip_prog p]
fun read_winnero () = 
  let val s = hd (readl winner_file) in
    if s = "nowinner" then NONE else SOME (sunzip_prog s)
  end

(* worker files *)
fun worker_fifo wid = shmdir ^ "/worker" ^ its wid ^ "fifo"
fun send_worker_fifo wid =
  let val out = TextIO.openOut (worker_fifo wid) in
    TextIO.output (out, "done\n"); TextIO.closeOut out
  end
fun receive_worker_fifo wid = 
  let 
    val stream = TextIO.openIn (worker_fifo wid)
    val line = TextIO.inputLine stream
    val _ = TextIO.closeIn stream
  in
    case line of 
      NONE => raise Msg ("receive_worker_fifo: " ^ its wid)
    | SOME _ => ()
  end
  
fun worker_file wid = shmdir ^ "/worker" ^ its wid
fun write_worker wid scorel = writel (worker_file wid) (map its4 scorel)
fun read_worker wid = 
  let 
    val file = worker_file wid
    val r = map sti4 (readl file) 
  in
    remove_file file; r
  end  

(* --------------------------------------------------------------------------
   Profiling
   -------------------------------------------------------------------------- *)
   
val dep_timer = ref 0.0
val score01_timer = ref 0.0
val scoreprog_timer = ref 0.0
val stats_timer = ref 0.0
val minor_timer = ref 0.0
val gen_timer = ref 0.0
val npl_timer = ref 0.0
val send_timer = ref 0.0
val wait_timer = ref 0.0
val sort_timer = ref 0.0
val barrier_timer = ref 0.0
val read_pdel_timer = ref 0.0
val write_worker_timer = ref 0.0
val score_total_timer = ref 0.0
val dispatch_timer = ref 0.0

val stats_freq = ref 100

val timerl_worker = [
  ("sc01", score01_timer),
  ("dep", dep_timer),
  ("scp", scoreprog_timer),
  ("gen", gen_timer),
  ("stats", stats_timer),
  ("minor", minor_timer),
  ("npl", npl_timer),
  ("barrier", barrier_timer),
  ("read_pdel", read_pdel_timer),
  ("write_worker", write_worker_timer),
  ("score_total", score_total_timer)
  ]
  
val timerl_dispatcher = [
  ("send", send_timer),
  ("wait", wait_timer),
  ("sort", sort_timer),
  ("latency",dispatch_timer)
  ]  
  


(* --------------------------------------------------------------------------
   Statistics
   -------------------------------------------------------------------------- *)

val r2 = rts_pad 2
val r4 = rts_pad 4

fun stats_worker rt iter =
  if iter = 0 orelse iter mod !stats_freq <> 0 then () else
  let
    val ku = Real.round (int_div (!run_time) (iter * 1000))
    val t = Time.toReal (Timer.checkRealTimer rt)
    val ti = (t - !stats_timer) / Real.fromInt iter
    fun f (x,t) = if !t < epsilon then NONE else 
                    SOME (x ^ " " ^ r2 (!t), !t) 
    val timers = String.concatWith "s, " 
      (map fst (dict_sort compare_rmax (List.mapPartial f timerl_worker))) 
      ^ "s"
  in
    pe (
        its iter ^ ": statistics" ^
        "\n  iter: " ^ r2 (ti * 1000.0) ^ "ms/i, " ^ its ku ^ "ku/i" ^
        "\n  total " ^ r2 t ^ "s: " ^ timers
       )
   end

fun stats_dispatcher iter =
  if iter = 0 orelse iter mod !stats_freq <> 0 then () else
  let
    fun f (x,t) = if !t < epsilon then NONE else 
                    SOME (x ^ " " ^ r2 (!t), !t) 
    val timers = String.concatWith "s, " 
      (map fst (dict_sort compare_rmax (List.mapPartial f timerl_dispatcher))) 
      ^ "s"
  in
    pe (its iter ^ " statistics: " ^ timers)
  end

(* --------------------------------------------------------------------------
   Worker
   -------------------------------------------------------------------------- *)

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

fun update_npexl pfn exl npl01o po = case npl01o of 
    SOME (npl01,npexl,node) => 
      (
      case po of 
        NONE => npexl 
      | SOME _ => npexl_of pfn exl npl01 node
      )
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

fun read_winner_wrapper () =
  let val file = shmdir ^ "/winner" in
    if not (exists_file file) then NONE else read_winnero ()
  end

fun update_prog_wrapper pfn npl01o po = case po of 
   NONE => () 
 | SOME p => update_prog pfn p (#3 (valOf npl01o))



fun write_worker_wrap wid scorel =
  (write_worker wid scorel; send_worker_fifo wid)

fun worker s =
  let
    val wid = sti s
    val _ = (run_time := 0; app (fn (_,r) => r := 0.0) timerl_worker)
    val (expname,trainfile,s3,s4,s5) = 
      quintuple_of_list (readl (shmdir ^ "/param"))
    val _ = expname_glob := expname
    val (ncore,nprog,itertot) = (sti s3, sti s4, sti s5)
    val pfn = read_pfn (shmdir ^ "/pfn_init")
    val exl = List.nth (cut_n ncore (read_exl trainfile), wid)
    val rt = Timer.startRealTimer ()
    fun loop npl01o iter =
      if iter >= itertot then "done" else        
      let
        val _ = total_time barrier_timer receive_dispatcher_fifo wid
        val po = read_winner_wrapper ()
        val (node,pdel) = total_time read_pdel_timer read_pdel pfn
        val _ = update_prog_wrapper pfn npl01o po
        val npexl = total_time npl_timer (update_npexl pfn exl npl01o) po
        val (scorel,npl01) = score_npexl pfn (node,pdel) npexl
        val _ = total_time write_worker_timer (write_worker_wrap wid) scorel
        val _ = total_time stats_timer (stats_worker rt) iter
      in
        loop (SOME (npl01,npexl,node)) (iter + 1)
      end
  in
    loop NONE 0 
  end

(* --------------------------------------------------------------------------
   Dispatcher
   -------------------------------------------------------------------------- *)

fun random_pl p nprog = 
  mk_fast_set prog_compare_size 
    (p :: (List.tabulate (nprog, !random_prog_glob)))

fun dispatcher_send iter nprog pfn ncore =  
  let 
    val node = random_node (dim_of_net pfn) 
    val p = ! (#1 (net_sub pfn node))
    val pl = random_pl p nprog
  in
    write_node node; write_pl pl;
    ignore (List.tabulate (ncore, send_dispatcher_fifo));
    (node, pl)
  end

val rt_dispatch = Timer.startRealTimer ()
val rt_dispatch_mem = ref 0.0

fun start_rt_dispatch () = 
  rt_dispatch_mem := Time.toReal (Timer.checkRealTimer rt_dispatch)
    
fun end_rt_dispatch () = 
  dispatch_timer := !dispatch_timer + 
    (Time.toReal (Timer.checkRealTimer rt_dispatch) - !rt_dispatch_mem)

fun dispatcher_wait_all v ncore =
  let
    val bstart = ref false
    fun f (wid,r) = if isSome (!r) then () else
      (
      let
        val _ = receive_worker_fifo wid
        val _ = if !bstart then () else (start_rt_dispatch (); bstart := true)
        val x = read_worker wid
      in 
        r := SOME x 
      end 
      handle Interrupt => raise Interrupt | _ => ()
      ) 
    fun loop () = if Vector.all (isSome o !) v then () else 
      (
      Vector.appi f v;
      OS.Process.sleep (Time.fromReal 0.0001); 
      loop ()
      )
  in
    loop ();
    end_rt_dispatch ()
  end  
  

fun dispatcher_receive ncore =  
  let
    val v = Vector.tabulate (ncore, fn _ => ref NONE)
    val _ = dispatcher_wait_all v ncore
    val scll = map (valOf o !) (vector_to_list v)
    val scl = map sum_int4 (list_combine scll)
  in
    scl
  end
  
fun cpl_compare12 cmp1 cmp2 ((a1,b1,c1,d1),(a2,b2,c2,d2)) =
  cpl_compare cmp1 cmp2 ((a1,b1),(a2,b2))
  
val cmp_score = snd_compare (cpl_compare12 Int.compare Int.compare)

fun report exln iter oldsc (sc,speed,acc,conf) =
  if sc >= oldsc then () else
  let 
    val scs = r4 (1.0 - Math.exp (~ (int_div sc (exln * scaling))))
    val accs = r4 (int_div acc exln)
    val confs = r4 (int_div conf exln)
    val speeds = r4 (int_div speed exln)
    val s = its iter ^ ": " ^ "sc " ^ scs ^ " "  ^ its sc ^ ", acc " ^ 
     accs ^ ", conf " ^ confs ^ ", speed " ^ speeds
  in
    pe s; append_endline (expdir () ^ "/stats") s
  end

(* maybe do some test at the moment of export *)
fun export_network pfn iter itertot = 
  if iter = itertot orelse iter mod 10000 = 0
  then write_pfn (expdir () ^ "/pfn" ^ its iter) pfn
  else ()

fun dispatcher () =  
  let 
    val _ = (run_time := 0; app (fn (_,r) => r := 0.0) timerl_dispatcher)
    val (expname,trainfile,s3,s4,s5) = 
      quintuple_of_list (readl (shmdir ^ "/param"))
    val _ = expname_glob := expname
    val (ncore,nprog,itertot) = (sti s3, sti s4, sti s5)
    val pfn = read_pfn (shmdir ^ "/pfn_init")
    val exln = length (read_exl trainfile)
    fun loop oldsc iter =
      if iter >= itertot then (export_network pfn iter itertot; "done") else  
      let
        val _ = export_network pfn iter itertot
        val (node,pl) = total_time send_timer
          (dispatcher_send iter nprog pfn) ncore
        val scl = total_time wait_timer dispatcher_receive ncore
        fun f () = hd (dict_sort cmp_score (combine_err (pl,scl)))
        val (winner,(sc,speed,acc,conf)) = total_time sort_timer f ()
        val _ = report exln iter oldsc (sc,speed,acc,conf)
        val winnero = 
          if winner = ! (#1 (net_sub pfn node)) then NONE else 
          (update_prog pfn winner node; SOME winner)
        val _ = pe (if isSome winnero then "winner" else "loser")
        val _ = write_winner winnero
        val _ = stats_dispatcher iter        
      in
        loop sc (iter + 1)
      end
  in
    loop (valOf Int.maxInt) 0
  end

(* --------------------------------------------------------------------------
   Main
   -------------------------------------------------------------------------- *)

fun job s = 
  if String.isPrefix "dispatcher" s then dispatcher () else worker s

fun hill_para expname trainfile ncore nprog itertot (depth,width) =
  let
    val _ = expname_glob := expname
    val _ = app mkDir_err [selfdir ^ "/exp",expdir ()]
    val _ = clean_dir shmdir
    val _ = writel (shmdir ^ "/param") 
      [expname, trainfile, its ncore, its nprog, its itertot]
    val _ = write_pfn (shmdir ^ "/pfn_init") (init_pfn (depth,width))
    val _ = List.tabulate (ncore, fn i => create_fifo (dispatcher_fifo i)) 
    val _ = List.tabulate (ncore, fn i => create_fifo (worker_fifo i))
    val sl = "dispatcher" :: List.tabulate (ncore, its)
    val _ = parmap_sl (ncore + 1) "hill_para.job" sl
  in
    ()
  end 

end (* struct *)

(*
load "hill_para";

PolyML.print_depth 0; 
open kernel aiLib prog exec network hill_para;
PolyML.print_depth 40;

val (depth,width) = (4,2000);
val nprog = 2000;
val ncore = 50;
val niter = 100000;
val expname = "net" ^ "-" ^ its depth ^ "-" ^ its width ^ "-" ^ its nprog
val trainfile = selfdir ^ "/aaa_test1000"; (* 30,000 bits *)

val _ = hill_para expname trainfile ncore nprog niter (depth,width);


17500 statistics: wait 5239.88s, send 570.00s, sort 9.99s
17502: sc 0.4686, acc 0.8056, conf 78.7434, speed 29.7380
300 ms per iter and latency over 50 percent.

70800 statistics: wait 89613.54s, latency 24159.12s, send 2391.73s, sort 41.86s
70803: sc 0.2438, acc 0.8663, conf 28.6556, speed 0.8366
70804: sc 0.2438, acc 0.8663, conf 28.6565, speed 1.4130
12000ms per iter
(todo start with a network instead of depth,width)
*)

