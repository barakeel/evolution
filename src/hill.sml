structure hill :> hill =
struct

open HolKernel aiLib kernel exec prog network

type param =
  {wid: int, width: int, depth: int,
   exl: ex, exlt: ex,
   rt: Timer.real_timer, rtmax: Time.time,
   share : bool} 

(* --------------------------------------------------------------------------
   Profiling
   -------------------------------------------------------------------------- *)

val io_time = ref 0.0
val log_time = ref 0.0 

fun log_aux (i, (pn,sc,t), scl) =
  let 
    val w2 = width_of_net (snd pn) div 2
    val sizel = map prog_size (flatten_pn pn)
    val size = sum_int sizel
    val sclpos = filter (fn x => x > w2) scl
    val accuracy = int_div (length sclpos) (length scl)
  in  
    pe ("iteration " ^ its i ^ ", " ^ 
        "loss " ^ rts_pad 4 sc ^ ", " ^
        "accurracy " ^ rts_pad 4 accuracy ^ ", " ^ 
        "size " ^ its size)    
    ; pe (cws (map its scl))
  end

fun log x = total_time log_time log_aux x

(* --------------------------------------------------------------------------
   Parallelized hill climbing
   -------------------------------------------------------------------------- *)
val expname = ref "test"

(*

fun exp_dir () = selfdir ^ "/exp/" ^ !expname
fun best_file () = "/dev/shm/thibault/best"  
fun ex_file () = selfdir ^ "/exp/" ^ !expname ^ "/ex" 
fun log_file () =  selfdir ^ "/exp/" ^ !expname ^ "/log" 

(* examples *)
fun read_exl () = 
  (pe ("reading examples from " ^ ex_file ());
   map (map stint o tws) (readl (ex_file ())))

fun write_exl exl = 
  (pe ("writing examples to " ^ ex_file ());
   writel (ex_file ()) (map (cws o (map its)) exl))  
*)

(* --------------------------------------------------------------------------
   Shared updates between workers
   -------------------------------------------------------------------------- *)

(*
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

fun write_bestpnx_aux wid pn =
  let 
    val filenew = best_file ()
    val fileold = filenew ^ its wid
  in
    write_pnx fileold pn;
    OS.FileSys.rename {old = fileold, new = filenew}
  end

fun write_bestpnx wid pn = total_time io_time (write_bestpnx_aux wid) pn
 
fun read_bestpnx () = total_time io_time read_pnx (best_file ())
*)


(* --------------------------------------------------------------------------
   Worker start and end
   -------------------------------------------------------------------------- *)
 

   
 (*
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
    val pnx = random_pnx (depth,width) exl
    val _ = (* if share then write_bestpnx wid pnx else *) ()
  in
    (
    {wid = stint wids, width = stint ws, depth = stint ds,
     exl = exl,
     rt = Timer.startRealTimer (), rtmax = Time.fromReal (streal ts), 
     share = share}
    ,
    pnx
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
*)

(* --------------------------------------------------------------------------
   Mutation
   -------------------------------------------------------------------------- *)

fun mutate_pn_once param pn = 
  let 
    val (d,w) = (#depth param, #width param)
    val (di,wi) = (random_int (0, d - 1), random_int (0, w - 1))
  in
    update_pn pn (random_prog (), di, wi)  
  end

(*
fun check_others param (i,scl) (sc',pnx') = 
  let val bestsc = check_bestsc () in
    if sc' < bestsc - epsilon
    then (log (i, pnx', scl); write_bestpnx (#wid param) pnx'; pnx')
    else read_bestpnx ()
  end
*)

fun mutate_pn param i (pnx as (pn,sc,t)) =
  let
    val _ = mutate_pn_once param pn
    val (sc',scl) = score_pn pn
    val t' = valOf Int.maxInt
    val pnx' = (pn,sc',t')
    val newpnx = 
      if sc' < sc + epsilon 
      then (if sc' < sc - epsilon then log (i, pnx', scl) else (); pnx')
      else (pn,sc,t')
  in
    (* if #share param then check_others param (i,scl) (sc',pnx')
        else *) 
     (* else if sc' < sc + epsilon andalso t' < t 
        then pnx' *)
        
    undol_glob := []; 
    newpnx  
  end    

(* --------------------------------------------------------------------------
   Hill climbing loop
   -------------------------------------------------------------------------- *)

fun check_rt param i =
  i mod 100 = 0 andalso Timer.checkRealTimer (#rt param) > #rtmax param

fun stats_aux param pfn i = 
  if not (i mod 1000 = 0 andalso i <> 0) then () else
  let 
    val t1 = Time.toReal (Timer.checkRealTimer (#rt param))
    val epoch = Real.fromInt (i div 1000)
    val t2 = t1 / epoch
    val t3 = int_div (!run_time) i
  in
    pe (its i ^ "(time) : total " ^ 
        rts_pad 2 t1 ^ "s " ^ its (!run_time) ^ "au, average " ^ 
        rts_round 3 t2 ^ "ms " ^ rts_round 2 t3 ^ "au");
    ignore (infer_test pfn (#exlt param))
  end
  
fun stats param i = total_time log_time (stats_aux param) i  

fun hill_aux param i (pnx as (pn,sc,t)) =
  (
  stats param (snd pn) i;
  if check_rt param i then pnx else
  (* if #share param andalso i mod 10 = 0 andalso check_bestsc () < sc - epsilon 
    then hill_aux param (i+1) (read_bestpnx ()) else *)
  let val pnx' = mutate_pn param i pnx in
    hill_aux param (i+1) pnx'
  end
  )
  
fun hill param pnx = hill_aux param 0 pnx

(*
fun hill_para s =
  let 
    val (param,pnx) = init_worker s
    val (_,sce,_) = hill param pnx
  in
    pe ("io time: " ^ rts_round 2 (!io_time));
    pe ("log time: " ^ rts_round 2 (!log_time));
    rts sce 
  end
*)

(* --------------------------------------------------------------------------
   Hill climbing wrappers
   -------------------------------------------------------------------------- *)

fun run_single (width,depth,rtmax) (exl,exlt) =
  let 
    val _ = run_time := 0
    val param = 
      {wid = 0, width = width, depth = depth,
       exl = exl, exlt = exlt,
       rt = Timer.startRealTimer (), rtmax = Time.fromReal rtmax, 
       share = false} 
    val pnx = random_pnx (depth,width) exl
  in
    hill param pnx
  end

(*
fun init_exp exps exl =
  (
  expname := exps;
  app mkDir_err ["/dev/shm/thibault",
                 selfdir ^ "/exp", selfdir ^ "/exp/" ^ !expname];
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
  end
*)
  

end (* struct *)



(*

load "hill"; open kernel aiLib prog network hill;


fun concatn n x = if n <= 1 then x else x @ concatn (n-1) x;

val (width,depth,rtmax) = (8,1,100.0);


fun mk_parity_pb width =  
  let
    fun product_int l = case l of [] => 1 | a :: m => a * product_int m;
    val exol0 = cartesian_productl (List.tabulate (width,fn _ => [~1,1]))
    val exol1 = map (fn x => (x, product_int x)) exol0
    val exl = vol_of_exol exol1
  in
    exl
  end;

val exl1 = mk_parity_pb width;
val exl2 = exl1;

val r = run_single (width,depth,rtmax) (exl1,exl2);


val pl = flatten_pn (#1 r);
app (pe o string_of_prog) pl;


*)


(*

load "hill"; open kernel aiLib prog network hill;


fun concatn n x = if n <= 1 then x else x @ concatn (n-1) x;

val (width,depth,rtmax) = (8,1,100.0);


fun mk_parity_pb width =  
  let
    fun product_int l = case l of [] => 1 | a :: m => a * product_int m;
    val exol0 = cartesian_productl (List.tabulate (width,fn _ => [~1,1]))
    val exol1 = map (fn x => (x, product_int x)) exol0
    val exl = vol_of_exol exol1
  in
    exl
  end;

val exl1 = mk_parity_pb width;
val exl2 = exl1;

val r = run_single (width,depth,rtmax) (exl1,exl2);


val pl = flatten_pn (#1 r);
app (pe o string_of_prog) pl;


*)


