signature exec =
sig

  type prog = kernel.prog
  type obj = int list * int
  type exec = obj * obj -> obj
  
  (* default object *)
  val empty : obj
  
  (* memory access *)
  val iv_glob : obj vector ref
  val xres_glob : obj ref
  
  (* global runtime *)
  val run_time : int ref
  
  (* lookup execv *)
  val get_name : int -> string
  val get_arity : int -> int 
  val get_id : string -> int
  
  (* executable *)
  val execv : ((exec list -> exec) * string * int) vector 
  val timelimit : int ref
  val mk_exec : prog -> exec
  val mk_exec_safe : prog -> exec
   
end
