signature hill =
sig

  type obj = exec.obj
  type exec = exec.exec
  type prog = kernel.prog

  type 'a net = 'a vector vector
  type iv = int ref vector
  type ex = iv * int
  type pfn = (prog ref * exec ref * int ref * int list ref * int list ref) net
  type cache = int ref net
  type node = int * int
  type negpos = int * int

  (* hill *)
  val init_hill : int * int -> int list list -> pfn * ex list
  val loop_hill : ex list -> pfn -> int -> unit

end
