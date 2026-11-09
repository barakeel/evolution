signature hill =
sig

  type obj = exec.obj
  type exec = exec.exec
  type prog = kernel.prog
  type ex = network.ex
  type pfn = network.pfn
  type negpos = network.negpos

  (* hill *)
  val init_hill : int * int -> int list list -> pfn * ex list * negpos list
  val loop_hill : int -> pfn * ex list * negpos list -> unit

  (* parallelization *)
  val compute_scorel_para : string -> string

end
