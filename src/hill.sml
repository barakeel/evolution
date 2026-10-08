structure hill :> hill =
struct

open HolKernel aiLib kernel exec prog network

val expname = ref "test"

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
val init_time = ref 0.0
val score_time = ref 0.0
val update1_time = ref 0.0
val update2_time = ref 0.0
val iter_dep_counter = ref 0

fun log_aux (i, di,wi, (pn,sc,t), scl) =
  let
    val _ = cache_glob := fst pn
    val w = width_of_net (snd pn)
    val w' = w div (!mod_glob) 
    val sizel = map prog_size (flatten_pn pn)
    val size = sum_int sizel
    val sclpos = filter (fn x => x > w' div 2) scl
    val acc = int_div (length sclpos) (length scl)
  in  
    pe (its i ^ ": " ^ "loss " ^ rts_pad 4 sc ^ ", " ^ "acc " ^ 
        rts_pad 4 acc ^ " at " ^ its di ^ "-" ^ its wi)
    (* ; pe (cws (map its scl)) *)
  end

fun log x = total_time log_time log_aux x

fun stats_aux param loss (cachel,pfn) i = 
  if i mod 1000 = 0 andalso i <> 0 then
  let 
    val _ = cache_glob := cachel
    val nex = length cachel
    val t1 = Time.toReal (Timer.checkRealTimer (#rt param))
    val t2 = (t1 / Real.fromInt i) * 1000.0
    val t3 = (int_div (!run_time) (i + !iter_dep_counter)) / 1000.0
    val t3' = int_div (!run_time) (!node_counter + !node_dep_counter)
    val (d,w) = dim_of_net pfn
    val size = d * w * nex
    val t4 = int_div (!node_counter * 100) (size * i)
    val t5 = int_div (!node_dep_counter * 100) (size * !iter_dep_counter)
    val (losst,acct) = infer_test pfn (#exl param)
    
  in
    pe ("\n" ^ "iter " ^ its i ^ " " ^ its (!iter_dep_counter) ^ ", " ^ 
        rts_round 3 t2 ^ " ms/i, " ^ 
        rts_round 0 t3 ^ " ku/i, " ^
        rts_round 2 t3' ^ " u/n, " ^
        "node " ^ rts_round 2 t4 ^ "% " ^ rts_round 2 t5 ^ "% " ^
        "\n  total time " ^ rts_pad 2 t1 ^ ", " ^
        "score " ^ rts_pad 2 (!score_time) ^ ", " ^
        "update " ^ rts_pad 2 (!update1_time) ^ 
        " " ^ rts_pad 2 (!update2_time) ^ ", " ^
        "infer " ^ rts_pad 2 (!log_time) ^ ", " ^
        "init " ^ rts_pad 2 (!init_time) ^ 
        "\n" ^ "loss " ^ rts_pad 4 losst ^ ", " ^ 
               "acc " ^ rts_pad 4 acct
        );
    
    if Real.abs (loss - losst) > 0.1 then raise Msg "mismatch: loss" else ()
  end
  else ()

fun stats param loss i = total_time log_time (stats_aux param loss) i  


(* --------------------------------------------------------------------------
   Mutate a single node
   -------------------------------------------------------------------------- *)

fun mutation param pn = 
  let 
    val (d,w) = (#depth param, #width param)
    val (di,wi) = (random_int (0, d - 1), random_int (0, w - 1))
  in
    (random_prog (), di, wi)  
  end

fun mutate_pn param i (pnx as (pn,sc,t)) =
  let
    val (p,di,wi) = mutation param pn 
    val oldpt = (! o #4) (Vector.sub (Vector.sub (snd pn, di), wi))
    val _ = total_time update1_time (update_pn pn) (p,di,wi)
    val pt = (! o #4) (Vector.sub (Vector.sub (snd pn, di), wi))
    fun undo () = (app (fn f => f ()) (!undol_glob); undol_glob := [])
    val (sc',scl) = total_time score_time score_pn pn
    val t' = valOf Int.maxInt
    val pnx' = (pn,sc',t')
    val newpnx = 
      if sc' < sc - epsilon orelse (sc' < sc + epsilon andalso pt < oldpt) 
      then (
           if sc' < sc - epsilon then log (i,di,wi,pnx',scl) else ();
           undo ();
           incr iter_dep_counter;
           dep_flag := true; 
           total_time update2_time (update_pn pn) (p,di,wi); 
           dep_flag := false;
           undol_glob := [];
           pnx'
           )
      else (undo (); (pn,sc,t'))
  in
    newpnx  
  end    

(* --------------------------------------------------------------------------
   Hill climbing loop
   -------------------------------------------------------------------------- *)

fun check_rt param i =
  i mod 1000 = 0 andalso Timer.checkRealTimer (#rt param) > #rtmax param

fun hill_aux param i (pnx as (pn,sc,t)) =
  (
  stats param sc pn i;
  if check_rt param i then (pe ""; pnx) else
  let val pnx' = mutate_pn param i pnx in
    hill_aux param (i+1) pnx'
  end
  )
  
fun hill param pnx = hill_aux param 0 pnx

(* --------------------------------------------------------------------------
   Hill climbing wrappers
   -------------------------------------------------------------------------- *)

fun run_single (width,depth,rtmax) (exl,exlt) =
  let 
    val _ = (run_time := 0; node_counter := 0; node_dep_counter := 0;
             iter_dep_counter := 0)
    val _ = (score_time := 0.0; update1_time := 0.0; update2_time := 0.0;
      log_time := 0.0; init_time := 0.0)
    val param = 
      {wid = 0, width = width, depth = depth,
       exl = exl, exlt = exlt,
       rt = Timer.startRealTimer (), rtmax = Time.fromReal rtmax, 
       share = false} 
    val _ = undol_glob := []
    val pnx = total_time init_time (random_pnx (depth,width)) exl
  in
    hill param pnx
  end


end (* struct *)


(*

load "hill"; open kernel aiLib prog exec network hill;
val l2 = map stil (readl "aaa_test");
val (width,depth,rtmax) = (64,4,1000.0);
mod_glob := 8;
full_flag := false;
PolyML.print_depth 2;
val exl1 = vol_of_sentencel width (first_n 10 l2); 
(* initializes some ref *)
val r = time (run_single (width,depth,rtmax)) (exl1,[]);
PolyML.print_depth 40;

val pl = flatten_pn (#1 r);
app (pe o string_of_prog) pl;




early stoppage
1000 * 1000 * 10 = 10 millions

(* generates a small data set *)
val l = read_oeis ();
val l1 = filter (fn x => length x <= 16) l;

val l1' = random_subset 10 l1;
val l2 = map binl_of_idl l1'; map length l2;
writel "aaa_test" (map ilts l2);
(* *)

(* todo before running run_single: resets the score *)
val exl1 = vol_of_sentencel width [[1,0,1,0,1,1,0,0,0,1,0,1,0,1,1,1,1,0],[1,0,1,1,0,0,0,1,0,1,0,1,1,1,0]];
todo: compute the average 
      number of instructions per node (suspect it's less than 10 but could be close to 100 if some loops)

fix a bug: that happens rarely loss mismatch

plan: 
1) do mod
2) train on 10 examples
3) do parallelization
4) 

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


