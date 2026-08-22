structure hill :> hill =
struct

open HolKernel aiLib kernel exec prog network

(* --------------------------------------------------------------------------
   Profiling
   -------------------------------------------------------------------------- *)

val io_time = ref 0.0
val log_time = ref 0.0 

fun log_aux (i, (pvl,sc,t), scll) =
  let 
    val sizel = map prog_size (flatten_pvl pvl)
    val size = sum_int sizel
  in  
    pe (its i ^ ": " ^ pretty_real sc ^ " " ^ its t ^ " " ^ its size);
    app (pe o cws o (map its)) scll
  end

fun log x = total_time log_time log_aux x

(* --------------------------------------------------------------------------
   Mutation
   -------------------------------------------------------------------------- *)

fun mutate_pv_once (width,depth) pv =
  let 
    val i' = random_int (0, width -1)
    fun f i = if i = i' then random_prog () else Vector.sub (pv,i)
  in
    Vector.tabulate (width, f)
  end

fun mutate_pvl_once wd pvl = 
  let 
    val i' = random_int (0, length pvl - 1)
    fun f i pv = if i' = i then mutate_pv_once wd pv else pv
    val pvl' = mapi f pvl
  in
    pvl'
  end

fun mutate_score param pvl =
  let
    val wd = (#width param, #depth param)
    val pvl' = mutate_pvl_once wd pvl
    val (scll,sc',t') = score_exl wd pvl' (#exl param)
  in
    ((pvl',sc',t'), scll)
  end  

(* --------------------------------------------------------------------------
   Parallelized hill climbing
   -------------------------------------------------------------------------- *)

val expname = ref "test"
fun exp_dir () = selfdir ^ "/exp/" ^ !expname
fun best_file () = selfdir ^ "/exp/" ^ !expname ^ "/best"  
fun ex_file () = selfdir ^ "/exp/" ^ !expname ^ "/ex" 
fun log_file () =  selfdir ^ "/exp/" ^ !expname ^ "/log" 

(* examples *)
fun read_exl () = 
  (pe ("reading examples from " ^ ex_file ());
   map (map stint o tws) (readl (ex_file ())))

fun write_exl exl = 
  (pe ("writing examples to " ^ ex_file ());
   writel (ex_file ()) (map (cws o (map its)) exl))  

(* --------------------------------------------------------------------------
   Shared updates between workers
   -------------------------------------------------------------------------- *)

fun read_word file =
  let
    val ins = TextIO.openIn file
    fun loop acc = case TextIO.input1 ins of
        NONE => implode (rev acc)
      | SOME c => if Char.isSpace c then implode (rev acc) else loop (c :: acc)
    val r = loop []
  in
    TextIO.closeIn ins; r
  end
 
fun check_bestsc_aux () = streal (read_word (best_file ()))
fun check_bestsc () = total_time io_time check_bestsc_aux ()

fun write_bestpvlx_aux wid pvl =
  let 
    val filenew = best_file ()
    val fileold = filenew ^ its wid
  in
    write_pvlx fileold pvl;
    OS.FileSys.rename {old = fileold, new = filenew}
  end

fun write_bestpvlx wid pvl = total_time io_time (write_bestpvlx_aux wid) pvl
 
fun read_bestpvlx () = total_time io_time read_pvlx (best_file ())

(* --------------------------------------------------------------------------
   Worker start and end
   -------------------------------------------------------------------------- *)
 
type param =
  {wid: int, width: int, depth: int,
   exl: int list list,
   rt: Timer.real_timer, rtmax: Time.time,
   share : bool} 
   
fun sextuple_of_list l = case l of 
    [a,b,c,d,e,f] => (a,b,c,d,e,f)
  | _ => raise Msg "sextuple_of_list"   

fun init_worker s = 
  let
    val (ws,ds,ts,wids,es,shares) = sextuple_of_list (tws s)
    val share = shares = "true"
    val _ = expname := es
    val exl = read_exl ()
    val (width,depth,rtmax,wid) = (stint ws, stint ds, streal ts, stint wids)
    val pvlx = random_pvlx (width,depth)
    val _ = if share then write_bestpvlx wid pvlx else ()
  in
    (
    {wid = stint wids, width = stint ws, depth = stint ds,
     exl = exl,
     rt = Timer.startRealTimer (), rtmax = Time.fromReal (streal ts), 
     share = share}
    ,
    pvlx
    )
  end

fun end_workers n = 
  let 
    fun fi i = selfdir ^ "/exp/reserved_stringspec/buildheap_script" ^ its i
    fun fo i = selfdir ^ "/exp/" ^ !expname ^ "/log" ^ its i
    fun g i = OS.FileSys.rename {old = fi i, new = fo i}
  in
    ignore (List.tabulate (n, g))
  end

(* --------------------------------------------------------------------------
   Hill climbing loop
   -------------------------------------------------------------------------- *)

fun check_rt param i =
  i mod 100 = 0 andalso Timer.checkRealTimer (#rt param) > #rtmax param

fun hill_aux param i (pvlx as (pvl,sc,t)) =
  if check_rt param i then pvlx else
  if #share param andalso i mod 10 = 0 andalso check_bestsc () < sc - epsilon 
    then hill_aux param (i+1) (read_bestpvlx ()) else
  let
    val (pvlx' as (pvl',sc',t'),scll) = mutate_score param pvl
    val newpvlx = 
      if sc' < sc - epsilon then
        if #share param then
          let val bestsc = check_bestsc () in
            if sc' < bestsc - epsilon
            then (log (i, pvlx', scll); write_bestpvlx (#wid param) pvlx'; pvlx')
            else read_bestpvlx ()
          end 
        else (log (i, pvlx', scll); pvlx')  
      else if sc' < sc + epsilon andalso t' < t then pvlx' else pvlx
  in
    hill_aux param (i+1) newpvlx 
  end

fun hill param pvlx = hill_aux param 0 pvlx

fun hill_para s =
  let 
    val (param,pvlx) = init_worker s
    val (_,sce,_) = hill param pvlx
  in
    if #share param then pe ("io time: " ^ rts_round 2 (!io_time)) else ();
    pe ("log time: " ^ rts_round 2 (!log_time));
    rts sce 
  end

(* --------------------------------------------------------------------------
   Hill climbing wrappers
   -------------------------------------------------------------------------- *)

fun run_single (width,depth,rtmax) exl =
  let 
    val param = 
      {wid = 0, width = width, depth = depth,
       exl = exl,
       rt = Timer.startRealTimer (), rtmax = Time.fromReal rtmax, 
       share = false} 
    val pvlx = random_pvlx (width,depth)
  in
    hill param pvlx
  end
  
fun init_exp exps exl =
  (
  expname := exps;
  app mkDir_err [selfdir ^ "/exp", selfdir ^ "/exp/" ^ !expname];
  write_exl exl
  )

fun run_para ncore exps exl (width,depth,rtmax) = 
  let
    val _ = init_exp exps exl
    fun f i = cws [its width, its depth, rts rtmax, its i, !expname, "true"];
    val sl = List.tabulate (ncore, f);
    val slout =  parmap_sl ncore "hill.hill_para" sl
  in 
    writel (log_file ()) ["loss: " ^ hd slout];
    end_workers ncore;
    streal (hd slout)
  end;

fun run_test ncore exps exl wdtl = 
  let 
    val _ = init_exp exps exl
    fun f i (width,depth,rtmax) = 
      cws [its width, its depth, rts rtmax, its i, exps, "false"];
    val sli = mapi f wdtl;
    val slo =  parmap_sl ncore "hill.hill_para" sli
  in
    writel (log_file ()) ["loss: " ^ cws slo];
    end_workers ncore;
    map streal slo
  end;
  
end (* struct *)

(*

load "hill"; open kernel aiLib prog hill;

val bll10 =
   [[1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0,
     0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1,
     0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1,
     0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0,
     0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0,
     1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1],
    [1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1,
     1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0,
     1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0,
     1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0,
     1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1,
     0, 0, 1, 1],
    [0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0,
     0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0,
     1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0,
     1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0,
     0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1],
    [1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0,
     1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 1,
     0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    [0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 0,
     0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0,
     1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0,
     0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0,
     0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1,
     0, 1, 0, 1, 1, 1, 0, 0],
    [0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0,
     0, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0,
     1, 1, 0, 0, 1, 0, 0, 1],
    [0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1,
     1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1,
     0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1],
    [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0,
     0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0,
     0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0,
     1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0,
     1, 1, 0, 0],
    [1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1,
     1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0,
     0, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1],
    [1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1,
     1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1,
     1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0,
     0, 0, 0, 0, 1, 0, 0, 1]];


val (width,depth,rtmax) = (200,8,10.0);
val ncore = 2;
val exps = "bll10";
val r = run_para ncore exps bll10 (width,depth,rtmax);



val targetl1 =
   [0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0,
    0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0,
    0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1];

val targetl2 = [0,1,1,0,0,1,1,0,1,0,1,0,1,1,1,1];

val (width,depth,rtmax) = (200,8,100.0);
val r = run_single (width,depth,rtmax) [targetl1,targetl2];

val wdtl = List.tabulate (ncore, fn i => (100, 3+i, 100.0));  
val r = run_test ncore exps targetl wdtl;

*)


(*

load "hill"; open kernel aiLib prog hill;

val ill = read_oeis ();
val ill10 = random_subset 10 ill;

val bll10 = map binl_of_idl ill10; map length bll10;
PolyML.print_depth 200;
bll10;
*)
