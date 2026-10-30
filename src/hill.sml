structure hill :> hill =
struct

open HolKernel aiLib kernel exec prog network

type 'a net = 'a vector vector
type iv = int ref vector
type ex = iv * int
type pfn = (prog ref * exec ref * int ref * int list ref * int list ref) net
type cache = int ref net
type node = int * int
type negpos = int * int
  
(* --------------------------------------------------------------------------
   Helper functions
   -------------------------------------------------------------------------- *)

fun sameish r1 r2 = Real.abs (r1 - r2) < epsilon  
fun nts (n,p) = (its n ^ "-" ^ its p)

fun random_node (depth,width) = 
  (random_int (0,depth-1), random_int (0,width -1))
  
fun list_radd (x:real list) (y:real list) = 
  map (fn (x,y) => x + y) (combine (x,y));   

fun update_prog pfn p (di,wi) = 
  let val (pref,fref,_,_,_) = net_sub pfn (di,wi) in
    pref := p; fref := mk_exec p; update_sdep pfn (di,wi)
  end

(* --------------------------------------------------------------------------
   Hill climbing loop
   -------------------------------------------------------------------------- *)

val prog_glob = ref (Ins (0,[]))

fun init_hill (depth,width) sentencel =
  let 
    val pfn = init_pfn (depth,width);
    val ex = ex_of_sentencel width sentencel
    val _ = run_time := 0
  in
    (pfn,ex)
  end

fun loop_hill_aux rt (exl,nex) pfn scold nprog n =
  let 
    val (depth,width) = dim_of_net pfn
    val (di,wi) = random_node (depth,width)
    val p = ! (#1 (net_sub pfn (di,wi)))
    val progl = mk_fast_set prog_compare_size
      (p :: (List.tabulate (nprog, !random_prog_glob)))
    val progdepl = map_assoc (dep_of_prog pfn (di,wi)) progl 
    val scorel = ref (List.tabulate (length progl, fn _ => 0.0))
    fun f inputvo = 
      let 
        val x = score_01 pfn (di,wi) inputvo
        val (depth,width) = dim_of_net pfn
        val cache = init_cache (depth,width)
        val r = map (score_prog cache pfn (di,wi) inputvo x) progdepl
      in
        scorel := list_radd r (!scorel)
      end
    val _ = app f exl
    val pscl = combine (progl,!scorel)
    val (prog,sc) = hd (dict_sort compare_rmax pscl)
    val _ = pe (its n ^ ": " ^ 
                rts_pad 4 (sc / Real.fromInt nex) ^ " " ^ 
                nts (di,wi))
    val _ = update_prog pfn prog (di,wi)
    val _ = prog_glob := prog
    val t = Time.toReal (Timer.checkRealTimer rt) / Real.fromInt n
    val _ =  if n mod 100 <> 0 then () else
      let 
        val scl = map (score_nodep pfn) exl 
        val confl = map (fn (_,(a,b)) => a + b) scl
        val scsum = sum_real (map fst scl)
        val acc = int_div (length (filter (fn x => fst x > 0.5) scl)) nex
        val _  = if sameish scsum sc then () else raise Msg "mismatch"
        val ku = Real.round (int_div (!run_time) (n * 1000))
      in
        pe (
          its n ^ ": " ^ 
          rts_pad 2 (t * 1000.0) ^ " ms/i " ^ 
          its ku ^ " ku/i\n  " ^ 
          "score " ^ rts_pad 4 (scsum / Real.fromInt nex) ^ ", " ^
          "accuracy " ^ rts_pad 4 acc ^ ", " ^
          "conf " ^ rts_pad 4 (average_int confl) ^ "\n  " ^
          "last change: " ^ string_of_prog (!prog_glob)
           )
      end
  in
    loop_hill_aux rt (exl,nex) pfn sc nprog (n + 1)
  end

fun loop_hill exl pfn nprog =
  loop_hill_aux (Timer.startRealTimer ()) (exl,length exl) pfn 0.0 nprog 1;




end (* struct *)

(*
load "hill";
PolyML.print_depth 0; open kernel aiLib prog exec network hill;
PolyML.print_depth 40;
val sentencel1 = map stil (readl "aaa_test100");
val sentencel2 = [[1,0,1,1,0,0,1,0,1,1,1,1,1,0,0,0,0,1]];
val (depth,width) = (4,100);
val (pfn,exl) = init_hill (depth,width) sentencel2;
val nprog = 1000;
time (loop_hill exl pfn) nprog;

*)




