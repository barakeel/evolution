signature exec =
sig

  type prog = kernel.prog
  type obj = int
  type exec = obj * obj -> obj
  
  (* default object *)
  val default : obj
  
  (* memory access *)
  val inputv_glob: (obj ref) vector ref
  val layerv_glob: (obj ref) vector ref
  val access_layer : int -> obj
  val z_glob : obj ref
  val xprev_glob : obj ref
  val self_glob : int ref
  
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
  val mk_exec_err : prog -> exec
   
end
