structure circle :> circle =
struct

open HolKernel aiLib kernel sexp
val ERR = mk_HOL_ERR "selfedit2"

exception Msg of string;
type obj = int list * int
type exec = obj * obj -> obj

(* --------------------------------------------------------------------------
   Timer
   -------------------------------------------------------------------------- *)

exception Check;
val timer = ref 0;
val timelimit = ref 10000;
fun ct n = 
  (timer := !timer + n; if !timer > !timelimit then raise Check else ())

(* --------------------------------------------------------------------------
   Primitives
   -------------------------------------------------------------------------- *)

(* helper *)
fun sing r = ([r], 1)  
val empty : obj = ([], 0)

(* task *)
val task_glob = ref empty
fun taskf fl (x,y) = (ct 1; !task_glob)

(* self *)
val self_glob = ref empty
fun selff fl (x,y) = (ct 1; !self_glob)

(* real *)
fun binf tim oper fl = case fl of
   [f1,f2] => (fn (x,y) => 
    let 
      val _ = ct tim
      val ((l1,n1),(l2,n2)) = (f1 (x,y),f2 (x,y)) 
    in 
      case (l1,l2) of 
        ([],_) => (l1,n1) 
      | (_,[]) => (l1,n1) 
      | (a1 :: b1, a2 :: b2) => (oper a1 a2 :: b1, n1)
    end)
  | _ => raise Msg "binf"


val one = ([1], 1)
fun onef fl (x,y) = (ct 1; one)
val two = ([2], 1)
fun twof fl (x,y) = (ct 1; two)
val ten = ([10], 1)
fun tenf fl (x,y) = (ct 1; ten)

fun add x1 x2 = x1 + x2
fun addf fl = binf 1 add fl
fun diff x1 x2  = x1 - x2
fun difff fl = binf 1 diff fl
fun mult x1 x2  = x1 * x2
fun multf fl = binf 1 mult fl

(* list *)
fun nullf fl (x,y) = (ct 1; empty)

fun lpop (l,n) = case l of [] => empty | a :: m => (m,n-1)

fun pop fl = case fl of 
    [f] => (fn (x,y) => (ct 1; lpop (f (x,y))))
  | _ => raise Msg "pop"

fun lpush a (m,n) = if n+1 > !timelimit then raise Check else (a :: m,n+1)
fun push fl = case fl of
   [f1,f2] => (fn (x,y) => 
    (
    ct 1; 
    let val ((l1,n1),(l2,n2)) = (f1 (x,y),f2 (x,y)) in 
      case l1 of a :: _ => lpush a (l2,n2) | _ => (l2,n2)
    end
    ))
  | _ => raise Msg "push"

fun interleave_aux1 l1 l2 = case (l1,l2) of
    ([],_) => l2
  | (_,[]) => l1
  | (a1 :: m1, a2 :: m2) => a1 :: a2 :: interleave_aux1 m1 m2

fun interleave_aux2 (l1,n1) (l2,n2) = 
  if n1 + n2 > !timelimit then raise Check else (interleave_aux1 l1 l2, n1+n2)
  
fun interleave fl = case fl of
   [f1,f2] => (fn xy => 
     let val ((l1,n1),(l2,n2)) = (f1 xy, f2 xy) in 
       (ct (n1+n2+1); interleave_aux2 (l1,n1) (l2,n2))
     end)
  | _ => raise Msg "push"

(* control flow *)
fun xvar fl (x,y) = (ct 1; x)
fun yvar fl (x,y) = (ct 1; y)

fun loop_aux f x xmax y =
  (
  ct 1; 
  if x >= xmax then y else loop_aux f (x+1) xmax (f (([x],1),y))
  )

fun loop_aux2 f x y = 
  (
  ct 1;
  case fst x of [] => y | xmax :: _ => loop_aux f 0 xmax y
  )

fun loop fl = case fl of
    [f1,f2,f3] => (fn xy => (ct 1; loop_aux2 f1 (f2 xy) (f3 xy)))
  | _ => raise Msg "loop"

fun loopl_aux f x y = 
   (
   ct 1;
   case x of ([],_) => y | (a :: m,n) => loopl_aux f (m,n-1) (f (x,y))
   )

fun loopl fl = case fl of
    [f1,f2,f3] => (fn xy => (ct 1; loopl_aux f1 (f2 xy) (f3 xy)))
  | _ => raise Msg "loopl"

fun cond fl = case fl of
    [f1,f2,f3] => (fn xy => 
    (
    ct 1; 
    case f1 xy of ([],_) => f3 xy | (x :: m,_) => 
      if x > 0 then f2 xy else f3 xy
    )
    )
  | _ => raise Msg "cond"

(* --------------------------------------------------------------------------
   Primitives
   -------------------------------------------------------------------------- *)

exception Open;

val execl =
  [
  (onef, "1", 0),
  (twof, "2", 0),
  (tenf, "10", 0),
  (addf, "+", 2),
  (difff, "-", 2), 
  (multf, "mult", 2),
  (pop, "pop", 1), 
  (push, "push", 2), 
  (interleave, "inter", 2),
  (xvar, "x", 0),
  (yvar, "y", 0),
  (loop, "loop", 3),
  (loopl, "loopl", 3),
  (cond, "cond", 3)
  ]

val execv = Vector.fromList execl
val execd = dnew String.compare (number_snd 0 (map #2 execl))

val _ = if Vector.length execv > 16
        then raise Msg "execv is too big" else ()

fun get_fun n = #1 (Vector.sub (execv,n))
fun get_name n = #2 (Vector.sub (execv,n))
fun get_arity n = #3 (Vector.sub (execv,n))

fun get_id s = dfind s execd handle NotFound => raise Msg ("get_id: " ^  s)

fun mk_exec (Ins (id,pl)) = (get_fun id) (map mk_exec pl)

fun mk_exec_safe p = 
  let val f = mk_exec p in 
    fn x => (timer := 0; f x handle Overflow => empty | Check => empty)
  end

(* --------------------------------------------------------------------------
   Converting between syntax tree and token list
   -------------------------------------------------------------------------- *)

fun flatten_prog ptop =
  let 
    val r = ref [] 
    fun loop (Ins (id,pl)) = (r := id :: !r; app loop pl)
  in 
    loop ptop; rev (!r)
  end

fun unflatten_progl_aux acc n l =
   (
   if n <= 0 then (rev acc, l) else
   (
   case l of 
     id :: m => 
     if id >= Vector.length execv then unflatten_progl_aux acc n m else
     let 
       val arity = get_arity id
       val (argl,cont) =  unflatten_progl_aux [] arity m
     in
       unflatten_progl_aux (Ins (id,argl) :: acc) (n-1) cont
     end
   | _ => raise Open
   )
   );
  
fun unflatten_prog l = 
  case (fst (unflatten_progl_aux [] 1 l) handle Open => []) of
    [p] => p
  | _ => raise Msg "unflatten_prog";
 

fun zip_il base l =
  let 
    open IntInf
    val basei = fromInt base
    val r = ref 1 
    fun f a = r := !r * basei + fromInt a
  in 
    app f l; !r
  end;
  
fun unzip_il base itop =
  let 
    open IntInf
    val basei = fromInt base
    val r = ref [] 
    fun loop i = if i < basei then () else
      (r := toInt (i mod basei) :: !r; loop (i div basei))
  in 
    loop itop; !r
  end; 
  
fun zip_prog p = zip_il (Vector.length execv) (flatten_prog p);
fun unzip_prog i = unflatten_prog (unzip_il (Vector.length execv) i);
 
 
fun bin_of_int n i = if n <= 0 then [] else
  Real.fromInt (i mod 2) :: bin_of_int (n-1) (i div 2)  
fun bin_of_prog p = List.concat (map (bin_of_int 4) (flatten_prog p)); 
 
(* --------------------------------------------------------------------------
   Random program
   -------------------------------------------------------------------------- *)
   
val arityl = List.tabulate (Vector.length execv, fn i => (i, get_arity i))
val arityl0 = map fst (filter (fn x => snd x = 0) arityl)
val aritylpos = filter (fn x => snd x > 0) arityl

fun random_prog n = 
  if n <= 1 then Ins (random_elem arityl0, []) else
  let
    val candl = filter (fn x => snd x <= n - 1) aritylpos 
    val (opern,arity) = random_elem candl
    val l = random_elem (number_partition arity (n - 1))
  in
    Ins (opern, map random_prog l)
  end   
 
fun randprog () = random_prog (random_int (5,20)); 
fun randpmem () = (randprog (),empty)

(* --------------------------------------------------------------------------
   Writing/reading program
   -------------------------------------------------------------------------- *)

fun sexp_of_prog (Ins (n,pl)) = case pl of 
    [] => Atom (get_name n)
  | _ => Sexp (Atom (get_name n) :: map sexp_of_prog pl) 

val string_of_sexp = sexp_to_string
val string_of_prog = string_of_sexp o sexp_of_prog;

val pp = pe o string_of_prog;

fun prog_of_sexp sexp = case sexp of
    Atom s => Ins (get_id s,[])
  | Sexp (Atom s :: m) => Ins (get_id s, map prog_of_sexp m)  
  | _ => raise Msg "prog_of_sexp" 

val sexp_of_string = string_to_sexp
val prog_of_string = prog_of_sexp o sexp_of_string

(* --------------------------------------------------------------------------
   Running an array of programs n times
   -------------------------------------------------------------------------- *)

fun run_elem n fv iv i = 
  let 
    val f = Vector.sub (fv, i)
    val i1 = Vector.sub (iv, i)
    val i2 = Vector.sub (iv, (i + 1) mod n)
  in
    f (i1,i2)
  end

fun run_once fv iv = 
  let val n = Vector.length fv in
    Vector.tabulate (n, run_elem n fv iv)
  end

fun run n fv iv = if n <= 0 then iv else run (n-1) fv (run_once fv iv);

fun runl fvl iv = case fvl of [] => iv | fv :: m => runl m (run_once fv iv)

(* --------------------------------------------------------------------------
   Evaluate the program on a task
   -------------------------------------------------------------------------- *)

fun count_neg iv = 
  let 
    val counter = ref 0
    fun f x = case fst x of [] => () | a :: m => 
      if a < 0 then incr counter else ()
    val _ = Vector.app f iv
  in
    !counter
  end

fun count_pos iv = 
  let 
    val counter = ref 0
    fun f x = case fst x of [] => () | a :: m => 
      if a > 0 then incr counter else ()
    val _ = Vector.app f iv
  in
    !counter
  end

fun score_obj obj fv iv = 
  let 
    val newiv = run 2 fv iv
    val sc = if obj > 0 then count_pos newiv else count_neg newiv
  in
    (newiv,sc)
  end

fun iv_of_pobjl n pobjl = 
  let 
    val pobjv = Vector.fromList pobjl 
    val m = Vector.length pobjv
  in
    Vector.tabulate (n, fn i => ([Vector.sub (pobjv, i mod m)],1))
  end

fun score_objl scl fv iv pobjl objl = case objl of 
    [] => scl
  | obj :: newobjl =>
    let
      val newpobjl = pobjl @ [obj]
      val (_,sc: int) = score_obj obj fv iv 
      val newiv = iv_of_pobjl (Vector.length iv) newpobjl
      val newscl = sc :: scl
    in
      score_objl newscl fv newiv newpobjl newobjl
    end

(* --------------------------------------------------------------------------
   Hill climbing
   -------------------------------------------------------------------------- *)

fun loss n x = if x <= 0 then 10000000.0 else 0.0 - Math.ln (int_div x n)

fun hill_aux i imax (pv,sc) objl =
  if i >= imax then pv else
  let 
    val n = Vector.length pv
    val pv' = Vector.update (pv, random_int (0,n-1), randprog ());
    val fv' = Vector.map mk_exec_safe pv';
    val iv = Vector.tabulate (n, fn _ => empty)
    val scl = score_objl [] fv' iv [] objl
    val sc' = sum_real (map (loss n) scl)
  in
    if sc' < sc 
    then (pe (its i ^ ": " ^ pretty_real sc' ^ " " ^ 
          String.concatWith " " (map its scl)); 
          hill_aux (i+1) imax (pv',sc') objl)
    else hill_aux (i+1) imax (pv,sc) objl
  end

fun hill n imax objl = 
  let 
    val pv = Vector.tabulate (n, fn _ => randprog ())
    val sc = 10000000.0
  in
    hill_aux 0 imax (pv,sc) objl
  end
  
end (* struct *)

(*

load "circle"; open kernel aiLib circle;

val (r,t) = add_time (hill 100) 1000000;




*)

