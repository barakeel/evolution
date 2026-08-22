structure network :> network =
struct

open HolKernel aiLib kernel sexp exec prog

type progn = prog vector list
type prognx = prog vector list * real * int
type ex = int list

fun flatten_pvl pvl = List.concat (map vector_to_list pvl)

fun pvl_compare (pvl1,pvl2) = 
  list_compare prog_compare (flatten_pvl pvl1, flatten_pvl pvl2) 

fun random_pvlx (width,depth) =
  let 
    fun f i = Vector.tabulate (width, fn _ => random_prog ())
    val pvl = List.tabulate (depth, f)
  in 
    (pvl, Real.maxFinite , valOf (Int.maxInt))
  end

(* --------------------------------------------------------------------------
   I/O for program networks
   -------------------------------------------------------------------------- *)

fun write_pvlx file (pvl,sc,t) = 
  let 
    val width = Vector.length (hd pvl)
    val depth = length pvl
    val pl = List.concat (map vector_to_list pvl)
    val pil = map zip_prog pl
    val s = cws [rts sc, its t, its width, its depth] ^ " " ^ 
            cws (map infts pil)
  in
    writel file [s]
  end
  
fun read_pvlx file = 
   case tws (hd (readl file)) of
     scs :: ts :: ws :: ds :: psl => 
     let 
       val (sc,t) = (streal scs, stint ts)
       val (width,depth) = (stint ws, stint ds) 
       val pl = map (unzip_prog o stinf) psl  
       val pll = mk_batch_full width pl
     in
       (map Vector.fromList pll, sc, t)
     end
   | _ => raise Msg "read_pvl"

(* --------------------------------------------------------------------------
   Run program networks
   -------------------------------------------------------------------------- *)

(* fun pow2 x = if x <= 0 then 1 else 2 * pow2 (x - 1) *)

fun run_elem (width,depth) fv ivi iv i = 
  let 
    val f = Vector.sub (fv, i)
    val i1 = Vector.sub (iv, i)
    val i2 = Vector.sub (iv, (i + 1) mod width)
    val _ = xres_glob := Vector.sub (iv, (i + 2) mod width)
  in
    f (i1,i2)
  end

fun run_once fv depth ivi iv = 
  let
    val width = Vector.length fv 
    val _ = iv_glob := iv
  in
    Vector.tabulate (width, run_elem (width,depth) fv ivi iv)
  end

fun runl_aux depth ivi fvl iv = case fvl of 
    [] => iv 
  | fv :: m => runl_aux (depth + 1) ivi m (run_once fv depth ivi iv)

fun runl fvl iv = runl_aux 0 iv fvl iv

(* --------------------------------------------------------------------------
   Evaluate program networks
   -------------------------------------------------------------------------- *)

fun count b iv = 
  let 
    val counter = ref 0
    fun f x = case fst x of [] => () | a :: m => 
      if a > 0 then incr counter else ()
    val _ = Vector.app f iv
  in
    if b then !counter else Vector.length iv - !counter
  end

fun score_obj obj fvl iv = 
  let 
    val newiv = runl fvl iv
    val sc = count (obj > 0) newiv
  in
    (newiv,sc)
  end

fun iv_of_pobjl oiv n pobjl = 
  let 
    val pobjv = Vector.fromList pobjl
    val m = Vector.length pobjv
  in
    Vector.tabulate (n, fn i => 
      if i mod (m+1) = m then empty else 
      let val (l,n) = Vector.sub (oiv,i) in
        (Vector.sub (pobjv, i mod (m+1)) :: l, n + 1)
      end
      )
  end

fun score_objl_aux scl fvl iv pobjl objl = case objl of 
    [] => rev scl
  | obj :: newobjl =>
    let
      val newpobjl = pobjl @ [obj]
      val (oiv,sc: int) = score_obj obj fvl iv 
      val newiv = iv_of_pobjl oiv (Vector.length iv) newpobjl
      val newscl = sc :: scl
    in
      score_objl_aux newscl fvl newiv newpobjl newobjl
    end

fun score_ex fvl ex = 
  let 
    val width = Vector.length (hd fvl)
    val iv = Vector.tabulate (width, fn _ => empty)
    val scl = score_objl_aux [] fvl iv [] ex
  in
    scl
  end

fun logit n x = if x <= 0 then 100000000.0 else 0.0 - Math.ln (int_div x n)

fun score_exl (width,depth) pvl exl = 
  let
    val _ = run_time := 0
    val fvl = map (Vector.map mk_exec_safe) pvl
    val scll = map (score_ex fvl) exl
    val sc = sum_real (map (logit width) (List.concat scll))
  in
    (scll,sc,!run_time)
  end
  
end (* struct *)
