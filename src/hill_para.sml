structure hill_para :> hill_para =
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
    val ti = t / Real.fromInt n
    fun f (x,t) = (x ^ " " ^ r2 (!t), !t) 
    val timers = String.concatWith "s, " 
      (map fst (dict_sort compare_rmax (map f timerl)))
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
    val pfn = total_time init_timer init_pfn (depth,width);
    val exl = total_time init_timer (ex_of_sentencel width) sentencel
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
        val npsc = total_time score01_timer 
          (score_01 cache pfn np (di,wi)) ex
        val restore = save_node pfn (di,wi)
        val r = total_time scoreprog_timer 
          (map (score_prog cache pfn (di,wi) ex npsc)) pdel
        val _ = (apply_undo (); restore ())
      in
        scorel := list_add2 r (!scorel); npsc
      end
    val _ = reset_flag := true
    val npscl01 = map f candl
    val _ = reset_flag := false
  in
    (npscl01, !scorel)
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
   Main computation in parallel (should be its own file)
   -------------------------------------------------------------------------- *)
 
val sti = string_to_int 
fun stnp s = let val (n,p) = split_pair #"_" s in (sti n, sti p) end 

(* in *) 
fun write_pl file pl = writel file (map (infts o zip_prog) pl)
fun read_pl file = map (unzip_prog o stinf) (readl file) 
 
fun write_npl file npl = writel file (map npts npl)

fun writes_ex (iv,obj) = lts (its obj :: map (its o !) (vector_to_list iv))
fun writes_npex (np,ex) = npts np ^ "|" ^ writes_ex ex
fun writes_npexl npexl = if null npexl then "@" else 
  String.concatWith ";" (map writes_npex npexl)

fun reads_ex s =
  let 
    val sl = stl s 
    val obj = sti (hd sl)
    val iv = Vector.fromList (map (ref o sti) (tl sl))
  in
    (iv,obj)
  end
fun reads_npex s = 
  let val (s1,s2) = split_pair #"|" s in (stnp s1, reads_ex s2) end
fun reads_npexl s = if s = "@" then []  else map reads_npex 
  (String.tokens (fn x => x = #";") s)

fun read_node file = 
  let val (s1,s2) = split_pair #"-" (hd (readl file)) in 
    (sti s1, sti s2) 
  end
fun write_node file n = writel file [nts n]

(* out *)
fun writes_npsc01 ((np0,np1),(sc0,sc1)) = 
  npts np0 ^ "-" ^ npts np1 ^ "-" ^ its sc0 ^ "-" ^ its sc1
fun writes_npscl01 npscl01 = lts (map writes_npsc01 npscl01)
fun read_npsc01 s = 
  let val (s1,s2,s3,s4) = 
    quadruple_of_list (String.tokens (fn x => x = #"-") s)
  in
    ((stnp s1, stnp s2), (sti s3, sti s4))
  end
fun read_npscl01 s = map read_npsc01 (stl s)  
  
fun writes_score (sc,t) = its sc ^ "-" ^ its t
fun writes_scorel scorel = lts (map writes_score scorel) 
fun read_score s = 
  let val (s1,s2) = split_pair #"-" s in (sti s1, sti s2) end
fun read_scorel s = map read_score (stl s)

fun end_para s =
  let val (s1,s2) = split_pair #"|" s in (read_npscl01 s1, read_scorel s2) end

(* function *)
fun init_para (pfn,pl,node) =
  (
  mkDir_err (selfdir ^ "/para");
  write_pfn (selfdir ^ "/para/pfn") pfn;
  write_pl (selfdir ^ "/para/pl") pl;
  write_node (selfdir ^ "/para/node") node
  )
  
fun compute_scorel_para s =
  let
    val paradir = selfdir ^ "/para"
    val pfn = read_pfn (paradir ^ "/pfn")
    val pl = read_pl (paradir ^ "/pl")
    val node = read_node (paradir ^ "/node")
    val npexl = reads_npexl s
    val _ = pe ("completed read: " ^ (its (length npexl)) ^ " examples")
    fun f p = (p, dep_of_prog pfn node p, mk_exec p)
    val pdel = total_time gen_timer (map f) pl
    val scorel = ref (List.tabulate (length pdel, fn _ => (0,0)))
    val cache = init_cache pfn    
    fun f (np,ex) = 
      let
        val npsc = total_time score01_timer (score_01 cache pfn np node) ex
        val restore = save_node pfn node
        val r = total_time scoreprog_timer 
          (map (score_prog cache pfn node ex npsc)) pdel
        val _ = (apply_undo (); restore ())
      in
        scorel := list_add2 r (!scorel); npsc
      end
    val _ = reset_flag := true
    val npscl01 = map f npexl
    val _ = reset_flag := false
  in
    writes_npscl01 npscl01 ^ "|" ^ writes_scorel (!scorel)
  end 

(* --------------------------------------------------------------------------
   Hill climbing loop
   --------------------------------------------------------------------------*) 

fun sum_int2 l = case l of [] => (0,0) | (a,b) :: m => 
  let val (c,d) = sum_int2 m in (a + c, b + d) end

fun worker s = if s = "0" then dispatcher s else worker s

val iter_glob = ref 0

fun init_hill (depth,width) sentencel =
  let 
    val _ = (run_time := 0; app (fn (_,r) => r := 0.0) timerl)
    val pfn = total_time init_timer init_pfn (depth,width);
    
    val npl = map (fst o score_nodep pfn) exl
    val expdir = selfdir ^ "/para"
    val _ = clean_dir expdir
  in
    write_pfn (expdir ^ "/pfn") pfn;
    write_npl (expdir ^ "/npl") npl
  end




fun dispatcher s = 
  let 
    
  
  val (depth,width) = dim_of_net pfn
  val (di,wi) = total_time minor_timer random_node (depth,width)
  val p = ! (#1 (net_sub pfn (di,wi)))
  fun f () = mk_fast_set prog_compare_size
    (p :: (List.tabulate (nprog, !random_prog_glob)))
  val progl = total_time gen_timer f ()
  val npexl = combine (nplold,exl)
  
  fun f () =
    let val cmp = 
      snd_compare (cpl_compare (inv_cmp Int.compare) Int.compare) 
    in
      hd (dict_sort cmp (combine (progl,scorel))) 
    end
  val (winner,(sc,_)) = total_time minor_timer f ()
  val npscl = total_time npl_timer 
    (npscl_of_winner cache pfn (di,wi) exl npscl01) winner
  val _ = total_time minor_timer 
    (report n sc scold nex npscl) (di,wi)
  val _ = update_prog pfn winner (di,wi)
  val _ = prog_glob := winner
  val _ = total_time stats_timer (stats_hill nprog rt (exl,nex) pfn n) sc
  val nplnew = map fst npscl
 

fun wait_update iter


fun init_worker i = 
  let 
    val ncore = read from i
    val sentencel = map stil (readl "aaa_test100");
    val sentencel2 = List.nth (cut_n ncore sentencel, i)
    val exl = total_time init_timer (ex_of_sentencel width) sentencel2
    val pfn = read_pfn "bla"
  in
    
  end

fun computer s =
  let 
    
    val pfn = wait_update (!iter_glob)
    val _ = 

fun loop_hill_aux ncore nprog cache rt (exl,nex) pfn nplold scold n =   
  let

    val (npscl01,scorel) = 
      let 
        val _ = total_time init_timer init_para (pfn,progl,(di,wi)) 
        val sl = map writes_npexl (cut_n ncore npexl)
        fun f () = smlRedirect.hide_in_file (selfdir ^ "/aaa_redirect")
          (parmap_sl ncore "hill.compute_scorel_para") sl
        val rl = total_time scoreprog_timer f ()
        fun f () = split (map end_para rl)
        val (a,b) = total_time score01_timer f ()
      in
        (List.concat a, map sum_int2 (list_combine b))
      end

  in 
    loop_hill_aux ncore nprog cache rt (exl,nex) pfn nplnew sc (n + 1)
  end

fun loop_hill ncore nprog (pfn,exl,npl) =
  let 
    val nex = length exl
    val cache = init_cache pfn
    val rt = Timer.startRealTimer ()
    val _ = prog_skip := 0
    val _ = pe ("training on " ^ its nex ^ " examples")
  in
    loop_hill_aux ncore nprog cache rt (exl,nex) pfn npl (~1) 1
  end



end (* struct *)

(*
load "hill";

PolyML.print_depth 0; 
open kernel aiLib prog exec network hill_para;
val sentencel = map stil (readl "aaa_test100");
val (depth,width) = (4,1024);
val nprog = 100;
val ncore = 1;
val init = init_hill (depth,width) sentencel;
PolyML.print_depth 40;

time (loop_hill ncore nprog) init;

(* error when restarting without reinitializing because mismatch 
   between pfn and npl *)

todo:
  and test the best of the other ones (this could be also done without 
  parallelization)
- idea: only recompute time for winners
- early give up for programs that will never catch up 
  or a competition style tournament
- could do a batch for all the nodes (so that no repetition occurs)

*)




