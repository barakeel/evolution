signature hill_para =
sig

  type obj = exec.obj
  type exec = exec.exec
  type prog = kernel.prog
  type ex = network.ex
  type pfn = network.pfn
  type negpos = network.negpos

  val job : string -> string
  val hill_para : string -> string -> int -> int -> int -> (int * int) -> unit

end
