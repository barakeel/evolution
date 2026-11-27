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

val str = valOf o Real.fromString
val sti = string_to_int 
fun nts (n,p) = (its n ^ "-" ^ its p)
fun stn s = let val (a,b) = split_pair #"-" s in (sti a, sti b) end 

fun its4 (n1,n2,n3,n4) = its n1 ^ "-" ^ its n2 ^ "-" ^ its n3 ^ "-" ^ its n4
fun sti4 iter s = 
  let val (a,b,c,d,e) = split_quintuple #"-" s in 
    if sti e <> iter then raise Msg ("sti4: " ^ its iter ^ " " ^ e) else
    (sti a, sti b, sti c, sti d) 
  end 

fun random_node (depth,width) = 
  (random_int_seed (0,depth-1), random_int_seed (0,width -1))
  
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
fun open_dispatcher_outs ncore =
  Vector.tabulate (ncore, fn wid => TextIO.openOut (dispatcher_fifo wid))
fun send_dispatcher_fifos outs =
  Vector.app (fn out => (TextIO.output (out, "go\n"); TextIO.flushOut out)) outs
fun receive_dispatcher_fifo ins wid =
  case TextIO.inputLine ins of
    NONE => raise Msg ("receive_dispatcher_fifo: " ^ its wid)
  | SOME _ => ()

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
fun open_worker_ins ncore =
  Vector.tabulate (ncore, fn wid => TextIO.openIn (worker_fifo wid))

fun send_worker_scores iter out scorel =
  (app (fn x => TextIO.output (out, its4 x ^ "-" ^ its iter ^ "\n")) scorel;
   TextIO.output (out, "END\n");
   TextIO.flushOut out)

fun receive_worker_scores iter ins wid =
  let
    fun loop acc =
      case TextIO.inputLine ins of
        NONE => raise Msg ("receive_worker_scores: " ^ its wid)
      | SOME "END\n" => rev acc
      | SOME line =>
          let val s = String.substring (line, 0, String.size line - 1) in
            loop (sti4 iter s :: acc)
          end
  in
    loop []
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
  
val rt_dispatch = Timer.startRealTimer ()
val rt_dispatch_mem = ref 0.0
fun start_rt_dispatch () = 
  rt_dispatch_mem := Time.toReal (Timer.checkRealTimer rt_dispatch)
fun end_rt_dispatch () = 
  dispatch_timer := !dispatch_timer + 
    (Time.toReal (Timer.checkRealTimer rt_dispatch) - !rt_dispatch_mem)
    
(* --------------------------------------------------------------------------
   Statistics
   -------------------------------------------------------------------------- *)

val r2 = rts_pad 2
val r4 = rts_pad 4

fun stats_worker wid rt iter =
  if iter = 0 orelse iter mod !stats_freq <> 0 then () else
  let
    val ku = Real.round (int_div (!run_time) (iter * 1000))
    val total = Time.toReal (Timer.checkRealTimer rt)
    val ti = total / Real.fromInt iter
    fun f (x,t) = if !t < epsilon then NONE else 
                    SOME (x ^ " " ^ r2 (!t), !t) 
    val timers = String.concatWith "s, " 
      (map fst (dict_sort compare_rmax (List.mapPartial f timerl_worker))) 
      ^ "s"
    val s =  
      its iter ^ ": " ^ r2 (ti * 1000.0) ^ "ms/i, " ^ its ku ^ "ku/i, " ^
       "total " ^ r2 total ^ "s: " ^ timers
  in
    pe s; 
    if wid = 0 
    then append_endline (expdir () ^ "/timer") ("worker0 " ^ s) else ()  
  end

fun stats_dispatcher rt iter =
  if iter = 0 orelse iter mod !stats_freq <> 0 then () else
  let
    val total = Time.toReal (Timer.checkRealTimer rt)
    fun f (x,t) = if !t < epsilon then NONE else 
                    SOME (x ^ " " ^ r2 (!t), !t) 
    val timers = String.concatWith "s, " 
      (map fst (dict_sort compare_rmax (List.mapPartial f timerl_dispatcher))) 
      ^ "s"
    val s = "dispatcher " ^ its iter ^ ": total " ^ r2 total ^ "s, " ^ timers
  in
    pe s; append_endline (expdir () ^ "/timer") s
  end

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
    val np01 = total_time score01_timer 
      (score_01 cache pfn np node) ex
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

fun sextuple_of_list l = case l of 
    [a,b,c,d,e,f] => (a,b,c,d,e,f)
  | _ => raise Msg "sextuple_of_list"

fun worker s =
  let
    val wid = sti s
    val _ = (run_time := 0; app (fn (_,r) => r := 0.0) timerl_worker)
    val (expname,trainfile,s3,s4,s5,s6) = 
      sextuple_of_list (readl (shmdir ^ "/param"))
    val _ = expname_glob := expname
    val _ = init_seed (str s6)
    val (ncore,nprog,itertot) = (sti s3, sti s4, sti s5)
    val pfn = read_pfn (shmdir ^ "/pfn_init")
    val exl = List.nth (cut_n ncore (read_exl trainfile), wid)
    val disp_in = TextIO.openIn (dispatcher_fifo wid)
    val work_out = TextIO.openOut (worker_fifo wid)
    val rt = Timer.startRealTimer ()
    fun loop npl01o iter =
      if iter >= itertot then
        (TextIO.closeIn disp_in; TextIO.closeOut work_out; "done")
      else        
      let
        val _ = total_time barrier_timer (receive_dispatcher_fifo disp_in) wid
        val po = read_winner_wrapper ()
        val (node,pdel) = total_time read_pdel_timer read_pdel pfn
        val _ = update_prog_wrapper pfn npl01o po
        val npexl = total_time npl_timer (update_npexl pfn exl npl01o) po
        val (scorel,npl01) = score_npexl pfn (node,pdel) npexl
        val _ = total_time write_worker_timer 
           (send_worker_scores iter work_out) scorel
        val _ = total_time stats_timer (stats_worker wid rt) iter
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
  let 
    val d = ref (enew prog_compare [p]) 
    fun loop () = if elength (!d) >= nprog then () else 
      d := eadd ((!random_prog_glob) 0) (!d)
  in
    loop (); elist (!d)
  end

fun dispatcher_send iter nprog pfn disp_outs =  
  let 
    val node = random_node (dim_of_net pfn) 
    val p = ! (#1 (net_sub pfn node))
    val pl = random_pl p nprog
  in
    write_node node; write_pl pl;
    send_dispatcher_fifos disp_outs;
    (node, pl)
  end

fun dispatcher_receive iter work_insl =  
  let
    val bstart = ref false
    fun f (wid, ins) =
      let
        val x = receive_worker_scores iter ins wid
        val _ = if !bstart then () else (start_rt_dispatch (); bstart := true)
      in
        x
      end
    val scll = map f work_insl
    val scl = map sum_int4 (list_combine scll)
  in
    end_rt_dispatch (); scl
  end

fun find_winner pl scl = 
  let
    fun cpl_compare12 cmp1 cmp2 ((a1,b1,c1,d1),(a2,b2,c2,d2)) =
          cpl_compare cmp1 cmp2 ((a1,b1),(a2,b2))
    val cmp_score = snd_compare (cpl_compare12 Int.compare Int.compare)
  in
    hd (dict_sort cmp_score (combine_err (pl,scl)))
  end
  
fun export_network pfn iter itertot = 
  if iter = itertot orelse iter mod 10000 = 0
  then write_pfn (expdir () ^ "/pfn" ^ its iter) pfn
  else ()  
  
fun dispatcher () =  
  let 
    val _ = (run_time := 0; app (fn (_,r) => r := 0.0) timerl_dispatcher)
    val (expname,trainfile,s3,s4,s5,s6) = 
      sextuple_of_list (readl (shmdir ^ "/param"))
    val _ = expname_glob := expname
    val _ = init_seed (str s6)
    val (ncore,nprog,itertot) = (sti s3, sti s4, sti s5)
    val pfn = read_pfn (shmdir ^ "/pfn_init")
    val exln = length (read_exl trainfile)
    val disp_outs = open_dispatcher_outs ncore
    val work_ins = open_worker_ins ncore
    val work_insl = number_fst 0 (vector_to_list work_ins)
    fun close_all () = (Vector.app TextIO.closeOut disp_outs;
                        Vector.app TextIO.closeIn work_ins)
    val rt = Timer.startRealTimer ()
    fun loop oldsc iter =
      if iter >= itertot then
        (export_network pfn iter itertot; close_all (); "done")
      else  
      let
        val _ = export_network pfn iter itertot
        val (node,pl) = total_time send_timer
          (dispatcher_send iter nprog pfn) disp_outs
        val scl = total_time wait_timer 
          (dispatcher_receive iter) work_insl
        val (winner,(sc,speed,acc,conf)) = total_time sort_timer 
          find_winner pl scl
        val _ = report exln iter oldsc (sc,speed,acc,conf)
        val winnero = 
          if winner = ! (#1 (net_sub pfn node)) then NONE else 
          (update_prog pfn winner node; SOME winner)
        val _ = write_winner winnero
        val _ = stats_dispatcher rt iter        
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

fun hill_para expname seed trainfile ncore nprog itertot (depth,width) =
  let
    val _ = expname_glob := expname
    val _ = init_seed seed
    val _ = app mkDir_err [selfdir ^ "/exp",expdir ()]
    val _ = writel (expdir () ^ "/param") 
      ["expname: " ^ expname, 
       "trainfile: " ^ trainfile, 
       "ncore: " ^ its ncore, 
       "nprog: " ^ its nprog, 
       "itertot: " ^ its itertot,
       "depth-width: " ^ its depth ^ "-" ^ its width,
       "seed: " ^ rts seed
       ]
    val _ = clean_dir shmdir
    val _ = writel (shmdir ^ "/param") 
      [expname, trainfile, its ncore, its nprog, its itertot, rts seed]
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

val (depth,width) = (8,1000);
val nprog = 2000;
val ncore = 50;
val niter = 100000;
val expname = "exp6"
val seed = random_seed ();
val trainfile = selfdir ^ "/aaa_test1000"; (* 30444 bits *)

val _ = hill_para expname seed trainfile ncore nprog niter (depth,width);


17500 statistics: wait 5239.88s, send 570.00s, sort 9.99s
17502: sc 0.4686, acc 0.8056, conf 78.7434, speed 29.7380
300 ms per iter and latency over 50 percent.

70800 statistics: wait 89613.54s, latency 24159.12s, send 2391.73s, sort 41.86s
70803: sc 0.2438, acc 0.8663, conf 28.6556, speed 0.8366
70804: sc 0.2438, acc 0.8663, conf 28.6565, speed 1.4130

43990: sc 0.2177 7474806685860, acc 0.8703, conf 20.1336, speed 0.1060

*)

(* local machine test

load "hill_para";

PolyML.print_depth 0; 
open kernel aiLib prog exec network hill_para;
PolyML.print_depth 40;

val (depth,width) = (4,1000);
val nprog = 100;
val ncore = 2;
val niter = 100000;
val expname = "exp9"
val seed = 118276875.0 (* random_seed (); *)
val trainfile = selfdir ^ "/aaa_test100"; (* 5324 bits *)

val _ = hill_para expname seed trainfile ncore nprog niter (depth,width);

*)


