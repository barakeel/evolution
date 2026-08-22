structure kernel :> kernel =
struct

open HolKernel Abbrev boolLib aiLib dir

exception Msg of string;       

val selfdir = dir.selfdir 

(* -------------------------------------------------------------------------
   Reading flags from config file
   ------------------------------------------------------------------------- *)

val configd = 
  let 
    val sl = readl (selfdir ^ "/config")
    fun f s = SOME (pair_of_list (String.tokens Char.isSpace s)) 
      handle HOL_ERR _ => NONE
  in
    dnew String.compare (List.mapPartial f sl)
  end

fun bflag s = ref (string_to_bool (dfind s configd) handle NotFound => false)
fun bflag_true s = 
  ref (string_to_bool (dfind s configd) handle NotFound => true)
fun iflag s i = ref (string_to_int (dfind s configd) handle NotFound => i) 
fun iflagnoref s i = string_to_int (dfind s configd) handle NotFound => i
fun rflagnoref s i = valOf (Real.fromString (dfind s configd)) 
                     handle NotFound => i

(* -------------------------------------------------------------------------
   Dictionaries shortcuts
   ------------------------------------------------------------------------- *)

type ('a,'b) dict = ('a, 'b) Redblackmap.dict
fun eaddi x d = d := eadd x (!d)
fun ememi x d = emem x (!d)
fun daddi k v d = d := dadd k v (!d) 
fun dmemi x d = dmem x (!d)
fun dfindo k d = Redblackmap.peek (d,k)
fun ereml kl d = foldl (uncurry erem) d kl;
fun dreml kl d = foldl (uncurry drem) d kl;

(* -------------------------------------------------------------------------
   String tools
   ------------------------------------------------------------------------- *)

val infts = IntInf.toString
val stinf = valOf o IntInf.fromString
val streal = valOf o Real.fromString 
val stint = string_to_int
fun ilts il = String.concatWith " " (map its il)
fun stil s = map string_to_int (String.tokens Char.isSpace s)

val pe = print_endline
val cws = String.concatWith " "
val tws = String.tokens Char.isSpace

fun split_pair c s = pair_of_list (String.tokens (fn x => x = c) s)
  handle HOL_ERR _ => raise Msg ("split_pair: " ^ Char.toString c ^ " " ^ s)

(* -------------------------------------------------------------------------
   Other tools
   ------------------------------------------------------------------------- *)

fun range (a,b,f) = List.tabulate (b-a+1,fn i => f (i+a));

(* -------------------------------------------------------------------------
   Program
   ------------------------------------------------------------------------- *)

datatype prog = Ins of (int * prog list);

fun prog_compare (Ins(s1,pl1),Ins(s2,pl2)) =
  cpl_compare Int.compare (list_compare prog_compare) ((s1,pl1),(s2,pl2))

fun raw_prog (Ins (id,pl)) =
  if null pl then its id else
  "(" ^ String.concatWith " " (its id :: map raw_prog pl) ^ ")"

fun equal_prog (a,b) = (prog_compare (a,b) = EQUAL)

fun prog_size (Ins(id,pl)) = 1 + sum_int (map prog_size pl)

fun prog_compare_size (p1,p2) =
  cpl_compare Int.compare prog_compare ((prog_size p1,p1),(prog_size p2,p2))

fun all_subprog (p as Ins (_,pl)) = p :: List.concat (map all_subprog pl)

(* -------------------------------------------------------------------------
   Parallelizer for functions of the type : unit -> string -> string
   as long as the function is named in a signature ".sig".
   ------------------------------------------------------------------------- *)

fun write_string file s = writel file [s]
fun read_string file = singleton_of_list (readl file)
fun write_unit file () = ()
fun read_unit file = ()

fun stringspec_fun_default (s:string) = "default"
val stringspec_fun_glob = ref stringspec_fun_default
val stringspec_funname_glob = ref "kernel.stringspec_fun_default"

val stringspec : (unit, string, string) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "kernel.stringspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    [
    "smlExecScripts.buildheap_dir := " ^ 
       mlquote (!smlExecScripts.buildheap_dir),
    "kernel.stringspec_fun_glob := " ^ (!stringspec_funname_glob)
    ]
    ^ ")"),
  function = let fun f () s = (!stringspec_fun_glob) s in f end,
  write_param = write_unit,
  read_param = read_unit,
  write_arg = write_string,
  read_arg = read_string,
  write_result = write_string,
  read_result = read_string
  }

fun parmap_sl ncore funname sl =
  let  
    val dir = selfdir ^ "/exp/reserved_stringspec"
    val _ = app mkDir_err [(selfdir ^ "/exp"), dir]
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its 
      (string_to_int (dfind "search_memory" configd) handle NotFound => 5000) 
    val _ = stringspec_funname_glob := funname
    val _ = smlExecScripts.buildheap_dir := dir
    val slo = smlParallel.parmap_queue_extern ncore stringspec () sl
  in
    slo
  end

fun test_fun s = (implode o rev o explode) s

(*
load "kernel"; open aiLib kernel;
val sl = List.tabulate (1000, its);
parmap_sl 2 "kernel.test_fun" sl; 
*)

end (* struct *)
