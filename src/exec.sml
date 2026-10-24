structure exec :> exec =
struct

open HolKernel aiLib kernel sexp

type obj = int
type exec = obj * obj -> obj

(* --------------------------------------------------------------------------
   Default object
   -------------------------------------------------------------------------- *)

val default = 0

(* --------------------------------------------------------------------------
   Timer
   -------------------------------------------------------------------------- *)

exception Check;
val timer = ref 0;
val timelimit = ref 100;
fun ct n = 
  (timer := !timer + n; if !timer > !timelimit then raise Check else ())

(* --------------------------------------------------------------------------
   Implementation of primitives
   -------------------------------------------------------------------------- *)

val z_glob = ref default
fun zf fl = fn xy => (ct 1; !z_glob)

val xprev_glob = ref default
fun xprevf fl = fn xy => (ct 1; !xprev_glob)

(* read from previous layer *)
val iv_glob = ref (Vector.fromList [ref 0])
fun access x = ! (Vector.sub (!iv_glob, x mod (Vector.length (!iv_glob))))

fun readf fl = case fl of
    [f] => (fn xy => (ct 5; access (f xy)))
  | _ => raise Msg "readf"

val self_glob = ref 0

fun readif fl = case fl of
    [f] => (fn xy => (ct 5; access (!self_glob + f xy)))
  | _ => raise Msg "readif"

(* arithmetical operations *)
fun constf c fl = (fn xy => (ct 1; c))

fun unf tim oper fl = case fl of
    [f] => (fn xy => (ct tim; oper (f xy)))
  | _ => raise Msg "unf"

fun binf tim oper fl = case fl of
    [f1,f2] => (fn xy => (ct tim; oper (f1 xy) (f2 xy))) 
  | _ => raise Msg "binf"

val zerof = constf 0
val onef = constf 1
val twof = constf 2
val tenf = constf 10
fun add x1 x2 = x1 + x2
fun addf fl = binf 1 add fl
fun diff x1 x2  = x1 - x2
fun difff fl = unf 1 (op ~) fl
fun mult x1 x2  = x1 * x2
fun multf fl = binf 1 mult fl
fun modu x1 x2 = x1 mod x2
fun modf fl = binf 5 modu fl
fun divi x1 x2 = x1 div x2
fun divf fl = binf 5 divi fl

(* control flow *)
fun xvar fl (x,y) = (ct 1; x)
fun yvar fl (x,y) = (ct 1; y)

fun loop_aux f x xmax y =
  (ct 1; if x >= xmax then y else loop_aux f (x+1) xmax (f (x,y)))

fun loop fl = case fl of
    [f1,f2,f3] => (fn xy => (ct 1; loop_aux f1 0 (f2 xy) (f3 xy)))
  | _ => raise Msg "loop"

fun cond fl = case fl of
    [f1,f2,f3] => (fn xy => (ct 1; if f1 xy > 0 then f2 xy else f3 xy))
  | _ => raise Msg "cond"

(* --------------------------------------------------------------------------
   Creating executable from program
   -------------------------------------------------------------------------- *)

val execl = 
  [
  (onef, "1", 0),(twof, "2", 0),(tenf, "10", 0),
  (addf, "+", 2),(difff, "-", 1), (multf, "mult", 2),
  (xvar, "x", 0),(yvar, "y", 0),
  (loop, "loop", 3),(cond, "cond", 3),
  (zf, "z", 0) , (readif, "readi", 1)
  ]

val execv = Vector.fromList execl
val execd = dnew String.compare (number_snd 0 (map #2 execl))

val _ = if Vector.length execv >= 16 then raise Msg "execv" else ()

fun get_fun n = #1 (Vector.sub (execv,n))
fun get_name n = #2 (Vector.sub (execv,n))
fun get_arity n = #3 (Vector.sub (execv,n))

fun get_id s = dfind s execd handle NotFound => raise Msg ("get_id: " ^  s)

fun mk_exec_unsafe (Ins (id,pl)) = (get_fun id) (map mk_exec_unsafe pl)
  
val run_time = ref 0

fun mk_exec p = 
  let val f = mk_exec_unsafe p in 
    fn x => 
      let val r = (timer := 0; f x mod 2
   handle Div => default | Overflow => default | Check => default) 
      in
        run_time := !timer + !run_time; r
      end
  end

(* for computing constants *)
fun mk_exec_err p = 
  let val f = mk_exec_unsafe p in 
    fn x => 
      let val r = (timer := 0; f x
   handle Div => raise Msg "div" | Overflow => raise Msg "overflow" 
        | Check => raise Msg "check") 
      in
        r
      end
  end


end (* struct *)


