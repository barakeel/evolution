signature exec =
sig

  type prog = kernel.prog
  type obj = int
  type exec = obj * obj -> obj
  
  (* default object *)
  val default : obj
  
  (* memory access *)
  val iv_glob: (obj ref * int list ref * int list ref) vector ref
  val z_glob : obj ref
  val xprev_glob : obj ref
  val self_glob : int ref
  
  (* dependency tracking *)
  val dep_flag : bool ref
  val access_glob : int list ref
  val access : bool -> (obj ref * int list ref * int list ref) vector -> int -> obj
  
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
