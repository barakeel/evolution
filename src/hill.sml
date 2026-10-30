structure hill :> hill =
struct

open HolKernel aiLib kernel exec prog network


(* --------------------------------------------------------------------------
   Helper functions
   -------------------------------------------------------------------------- *)

fun init_hill (depth,width) sentencel =
  let 
    val pfn = init_pfn (depth,width);
    val ex = ex_of_sentencel width sentencel
  in
    (pfn,ex)
  end

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

fun loop_hill_aux rt exl pfn scold nprog n =
  let 
    val (depth,width) = dim_of_net pfn
    val (di,wi) = random_node (depth,width)
    val p = ! (#1 (net_sub pfn (di,wi)))
    val progl = mk_fast_set prog_compare_size (* [p] *)
      (p :: (List.tabulate (nprog, !random_prog_glob)))
    val scorel_glob = ref (List.tabulate (length progl, fn _ => 0.0))
    fun f inputvo = 
      let 
        val (sc0,sc1) = score_01 pfn (di,wi) inputvo
        val r = map (score_prog pfn (di,wi) inputvo (sc0,sc1)) progl
      in
        scorel_glob := list_radd r (!scorel_glob)
      end
    val _ = app f exl
    val r = combine (progl,!scorel_glob)
    val scnew = dfind p (dnew prog_compare r) 
    val _ = 
      if scold <= 0.0 then ()
      else if sameish scold scnew then () 
      else raise Msg ("loop_hill: " ^ rts_pad 4 scold ^ " " ^ rts_pad 4 scnew)
    val (prog,sc) = hd (dict_sort compare_rmax r)
    val _ = if sc < scold - epsilon 
            then raise Msg "loop_hill"
            else ()
    val scaver = sc / Real.fromInt (length exl) (* to optimize ? *)
    val _ = pe (its n ^ ": " ^ rts_pad 4 scaver ^ " " ^ nts (di,wi))
    val _ = update_prog pfn prog (di,wi)
    val t = Time.toReal (Timer.checkRealTimer rt) / Real.fromInt n
    val _ =  if n mod 100 <> 0 then () else
      let 
        val sctest = sum_real (map (score_nodep pfn) exl) 
        val _  = if sameish sctest sc then () else raise Msg "mismatch"
      in
        pe (its n ^ " : average time " ^ rts_pad 2 (t * 1000.0) ^ " ms")        
      end
  in
    loop_hill_aux rt exl pfn sc nprog (n + 1)
  end

fun loop_hill exl pfn nprog =
  loop_hill_aux (Timer.startRealTimer ()) exl pfn 0.0 nprog 1;




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




