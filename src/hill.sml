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
    val sizel = map prog_size (flatten_pn pn)
    val size = sum_int sizel
    val sclpos = filter (fn x => x > 0.5) scl
    val nex = length scl
    val acc = int_div (length sclpos) nex
    val confl = map (fn (_,(_,_,x,y)) => !x + !y) (!cache_glob)
    val conf = int_div (sum_int confl) nex
  in  
    pe (its i ^ ": " ^ "loss " ^ rts_pad 4 sc ^ 
        ", acc " ^ rts_pad 4 acc ^ 
        ", conf " ^ rts_pad 4 conf ^
        ", pos " ^ its di ^ "-" ^ its wi
        
        )
    (* ; pe (cws (map its scl)) *)
  end

fun log x = total_time log_time log_aux x

fun stats_aux param loss (cachel,pfn) i = 
  if i mod 10000 = 0 andalso i <> 0 then
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
    val confl = map (fn (_,(_,_,x,y)) => !x + !y) (!cache_glob)
    val conf = int_div (sum_int confl) nex 
    val p = (! o #1) 
      (Vector.sub (Vector.sub (pfn, random_int (0,d-1)), random_int (0,w-1))) 
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
               "acc " ^ rts_pad 4 acct ^ ", " ^
               "conf " ^ rts_pad 4 conf ^
        "\n" ^ "example program: " ^ string_of_prog p
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
    ((!random_prog_glob) di, di, wi)  
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
  i mod 10000 = 0 andalso Timer.checkRealTimer (#rt param) > #rtmax param

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
todo: remove the cache put the computation graph on the network side
disallow dynamic connections.

idea only record posneg for each example and recompute the difference everytime

look at which nodes requires modifications, do not attempt to modify a node
that is "perfect".
*)

(*

load "hill";
PolyML.print_depth 0;
open kernel aiLib prog exec network hill;
PolyML.print_depth 40;
val l2 = map stil (readl "aaa_test");
val (width,depth,rtmax) = (512,4,3600.0);
conf_penalty := 0.0001;
PolyML.print_depth 2;
val exl1 = vol_of_sentencel width (first_n 10 l2); (* ! *)
val r = time (run_single (width,depth,rtmax)) (exl1,[]);
PolyML.print_depth 40;

(*
val pl = map (unzip_prog o stinf) (readl "aaa_prog");
val pll = mk_batch 512 pl;
val pvv = Vector.fromList (map Vector.fromList pll);
fun f (di:int) = Vector.sub (Vector.sub (pvv,di), random_int (0, 511));
random_prog_glob := f;
*)

iter 10000 3077, 20.426 ms/i, 285.0 ku/i, 56.72 u/n, node 0.47% 0.39% 
  total time 204.26, score 0.96, update 134.84 47.81, infer 5.82, init 6.93
loss 282.7277, acc 0.7702, conf 27.0864
example program: (cond 10 1 (mult (- (+ (+ (+ (readi 225319066190) 1) 1) (- 10))) (cond (- (- (mult (- (- 2)) (readi 35564989799)))) (loop (+ (readi 424887978670) (readi 571821572060)) (- (- 2)) (cond (loop (readi 886548213143) 1 1) 10 10)) (+ 1 (mult 10 2)))))

iter 10000 1868, 31.055 ms/i, 786.0 ku/i, 61.84 u/n, node 1.2% 0.81% 
  total time 310.55, score 0.71, update 234.37 54.08, infer 6.23, init 3.70
loss 267.5497, acc 0.8438, conf 35.4210
example program: (loop (- (cond (readi 323445732390) (readi 794923221132) (readi 824941873935))) (- 1) (mult 10 2))





let val pl = random_subset 20 (flatten_pn (#1 r)) in
  app (pe o string_of_prog) pl
end;

val pl = flatten_pn (#1 r);
val il = map zip_prog pl;

writel "aaa_prog" (map infts il);




(* generates a small data set *)
val l = read_oeis ();
val l1 = filter (fn x => length x <= 16) l;

val l1' = random_subset 10 l1;
val l2 = map binl_of_idl l1'; map length l2;
writel "aaa_test" (map ilts l2);

*)




