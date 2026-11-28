signature hill =
sig

  type obj = exec.obj
  type exec = exec.exec
  type prog = kernel.prog
  type ex = network.ex
  type pfn = network.pfn
  type negpos = network.negpos

  val random_pl : prog -> int -> prog list
  val job : string -> string
  val hill : string -> real -> 
    string -> int -> int -> int -> (int * int) -> unit

end
