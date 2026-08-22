structure exec :> exec =
struct

open HolKernel aiLib kernel sexp

type obj = int list * int
type exec = obj * obj -> obj

(* --------------------------------------------------------------------------
   Default object
   -------------------------------------------------------------------------- *)

val empty : obj = ([], 0)

(* --------------------------------------------------------------------------
   Timer
   -------------------------------------------------------------------------- *)

exception Check;
val timer = ref 0;
val timelimit = ref 10000;
fun ct n = 
  (timer := !timer + n; if !timer > !timelimit then raise Check else ())

(* --------------------------------------------------------------------------
   Implementation of primitives
   -------------------------------------------------------------------------- *)

(* read from current layer *)
val iv_glob = ref (Vector.fromList [empty])
val xres_glob = ref empty
fun xresf fl = fn xy => (ct 1; !xres_glob)

fun inputf fl = case fl of
    [f] => (fn xy => 
    let 
      val _ = ct 10
      val (l1,n1) = f xy 
    in
      case l1 of [] => empty | a :: m =>
        Vector.sub (!iv_glob, a mod (Vector.length (!iv_glob)))
    end
    )
  | _ => raise Msg "inputf"

(* arithmetical operations *)
fun constf c fl = (fn xy => (ct 1; ([c],1)))

fun unf tim oper fl = case fl of
   [f] => (fn xy => 
    let 
      val _ = ct tim
      val (l,n)= f xy
    in 
      case l of [] => (l,n) | a :: m => (oper a :: m, n)
    end)
  | _ => raise Msg "unf"

fun binf tim oper fl = case fl of
   [f1,f2] => (fn xy => 
    let 
      val _ = ct tim
      val ((l1,n1),(l2,n2)) = (f1 xy, f2 xy) 
    in 
      case (l1,l2) of 
        ([],_) => (l1,n1) 
      | (_,[]) => (l1,n1) 
      | (a1 :: b1, a2 :: b2) => (oper a1 a2 :: b1, n1)
    end)
  | _ => raise Msg "binf"

val onef = constf 1
val twof = constf 2
val tenf = constf 10
fun add x1 x2 = x1 + x2
fun addf fl = binf 1 add fl
fun diff x1 x2  = x1 - x2
fun difff fl = unf 1 (op ~) fl
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
   Creating executable from program
   -------------------------------------------------------------------------- *)

val execl = 
  [
  (onef, "1", 0),(twof, "2", 0),(tenf, "10", 0),
  (addf, "+", 2),(difff, "-", 1), (multf, "mult", 2),
  (pop, "pop", 1),(push, "push", 2), (interleave, "inter", 2),
  (xvar, "x", 0),(yvar, "y", 0),
  (loop, "loop", 3),(loopl, "loopl", 3),(cond, "cond", 3),
  (inputf, "read", 1),(xresf, "xres", 1)
  ]

val execv = Vector.fromList execl
val execd = dnew String.compare (number_snd 0 (map #2 execl))

val _ = if Vector.length execv > 16 then raise Msg "execv" else ()

fun get_fun n = #1 (Vector.sub (execv,n))
fun get_name n = #2 (Vector.sub (execv,n))
fun get_arity n = #3 (Vector.sub (execv,n))

fun get_id s = dfind s execd handle NotFound => raise Msg ("get_id: " ^  s)

fun mk_exec (Ins (id,pl)) = (get_fun id) (map mk_exec pl)

val run_time = ref 0

fun mk_exec_safe p = 
  let val f = mk_exec p in 
    fn x => 
      let val r = (timer := 0; f x handle Overflow => empty | Check => empty) in
        run_time := !timer + !run_time; r
      end
  end

end (* struct *)


