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

fun log_aux (i, di,wi, (pn,sc,t), scl) =
  let
    val _ = cache_glob := fst pn
    val w2 = width_of_net (snd pn) div 2
    val sizel = map prog_size (flatten_pn pn)
    val size = sum_int sizel
    val sclpos = filter (fn x => x > w2) scl
    val acc = int_div (length sclpos) (length scl)
  in  
    pe (its i ^ ": " ^ "loss " ^ rts_pad 4 sc ^ ", " ^ "acc " ^ rts_pad 4 acc);
    pe (cws (map its scl))
  end

fun log x = total_time log_time log_aux x

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
    val _ = update_pn pn (p,di,wi)
    fun undo () = (app (fn f => f ()) (!undol_glob); undol_glob := [])
    val (sc',scl) = score_pn pn
    val t' = valOf Int.maxInt
    val pnx' = (pn,sc',t')
    val newpnx = 
      if sc' < sc + epsilon 
      then (
           if sc' < sc - epsilon 
           then log (i, di,wi, pnx', scl) 
           else ()
           ;
           undo ();
           dep_flag := true; update_pn pn (p,di,wi); dep_flag := false;
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

fun stats_aux param (cachel,pfn) i = 
  if i mod 1000 = 0 andalso i <> 0 then
  let 
    val nex = length cachel
    val t1 = Time.toReal (Timer.checkRealTimer (#rt param))
    val t2 = (t1 / Real.fromInt i) * 1000.0
    val t3 = (int_div (!run_time) i) / 1000.0
    val (d,w) = dim_of_net pfn
    val t4 = int_div (!node_counter * 100) (d * w * nex * i)
  in
    pe ("\n" ^ its i ^ ": speed " ^ 
        rts_round 3 t2 ^ " ms/i " ^ 
        rts_round 0 t3 ^ " ku/i " ^
        "nodes " ^ its (!node_counter) ^ "/" ^ its (d * w * nex * i) ^ " " ^
        rts_round 2 t4 ^ "%"
        );
    ignore (infer_test pfn (#exlt param))
  end
  else ()
  
fun stats param i = total_time log_time (stats_aux param) i  

fun hill_aux param i (pnx as (pn,sc,t)) =
  (
  stats param pn i;
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
    val _ = run_time := 0
    val _ = node_counter := 0
    val param = 
      {wid = 0, width = width, depth = depth,
       exl = exl, exlt = exlt,
       rt = Timer.startRealTimer (), rtmax = Time.fromReal rtmax, 
       share = false} 
    val pnx = random_pnx (depth,width) exl
  in
    hill param pnx
  end


end (* struct *)


(*
load "hill"; open kernel aiLib prog exec network hill;

val (width,depth,rtmax) = (256,4,60.0);
debug_flag := false;
nodep_flag := false;
val exl1 = vol_of_sentencel width [[1,0,1,0,1,1,0,0,0,1,0,1,0,1,1,1,1,0,1,0,1,1,0,0,0,1,0,1,0,1,1,1]];
val _ = run_single (width,depth,rtmax) (exl1,exl1);

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


