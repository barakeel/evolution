signature circle =
sig

  val string_of_prog : kernel.prog -> string
  val prog_of_string : string -> kernel.prog
  val random_prog : int -> kernel.prog
  val randprog : unit -> kernel.prog
  
  type obj = int list * int
  type exec = obj * obj -> obj

  val timelimit : int ref
  val empty : obj
  val mk_exec : kernel.prog -> exec
  val mk_exec_safe : kernel.prog -> exec
  
  (* objectives *)
  val hill : real -> int -> int -> int -> int list ->  kernel.prog vector list
  val read_oeis : unit -> int list list
  val bitl_of_tokenl : int list -> int list
  
end
