signature network =
sig

  type obj = exec.obj
  type exec = exec.exec
  type prog = kernel.prog
  type progn = prog vector list
  type prognx = prog vector list * real * int
  type ex = int list
  
  val flatten_pvl : progn -> prog list
  val pvl_compare : progn * progn -> order
  val random_pvlx : int * int -> prognx
  
  (* input/output: includes loss and total time *)
  val write_pvlx : string -> prognx -> unit
  val read_pvlx : string -> prognx
  
  (* running a program network: todo package it *) 
  val runl : exec vector list -> obj vector -> obj vector
  val score_ex : exec vector list -> ex -> int list
  val score_exl : int * int -> progn -> ex list -> int list list * real * int
  
   
end
