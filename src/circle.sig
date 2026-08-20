signature circle =
sig

  type prog = kernel.prog
  type obj = int list * int
  type exec = obj * obj -> obj
  
  (* logging *)
  val log_time : real ref
  val write_time : real ref
  val expname : string ref 
  
  (* primitives *)
  val execv : ((exec list -> exec) * string * int) vector 
  val get_name : int -> string
  
  (* input/output *)
  val prog_of_string : string -> kernel.prog
  val string_of_prog : kernel.prog -> string
  val zip_prog : prog -> IntInf.int
  val unzip_prog : IntInf.int -> prog
  val write_pvl : string -> prog vector list * real * int -> unit
  val read_pvl : string -> prog vector list * real * int
  val pvl_compare : prog vector list * prog vector list -> order
  
  (* random program *)
  val random_prog : int -> kernel.prog
  val randprog : unit -> kernel.prog
  
  (* program execution *)
  val timelimit : int ref
  val empty : obj
  val mk_exec : kernel.prog -> exec
  val mk_exec_safe : kernel.prog -> exec
   
  (* objectives *)
  val hill : (int * int) -> int list -> int -> prog vector list * real * int
  val read_oeis : unit -> int list list
  val bitl_of_tokenl : int list -> int list
  
  (* parallelization *)
  val ex_file : unit -> string
  val hill_para : string -> string
  
end
