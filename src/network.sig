signature network =
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
  
  val conf_penalty : real ref
  
  (* net primitives *)
  val width_of_net : 'a net -> int
  val depth_of_net : 'a net -> int
  val dim_of_net : 'a net -> int * int 
  val net_app : ('a * int * int -> unit) -> 'a net -> unit
  val net_sub : 'a net -> int * int -> 'a
  val net_tabulate : int * int -> (int * int -> 'a) -> 'a net
  val flatten_pfn : pfn -> prog list
  val pfn_compare : pfn * pfn -> order
  
  (* initialization *)
  val ex_of_sentencel : int -> int list list -> ex list
  val init_pfn : int * int -> pfn
  val init_cache : int * int -> cache
  
  (* dependency graph *)
  val descendant : pfn -> (int * int list) -> (int * int list) list  
  val update_sdep : pfn -> node -> unit
  val recompute_alldep : pfn -> unit
  
  (* computing a single node *)
  val recompute_node : iv -> cache -> pfn -> node -> unit
  
  (* negpos *)
  val negpos_inputv : pfn -> node list -> iv -> negpos
  val negpos_01 : pfn -> node -> iv -> negpos * negpos
 
  (* score *)
  val score_negpos : int * (int * int) -> real
  val score_01 : pfn -> node -> ex -> real * real
  val score_prog : pfn -> node -> ex -> real * real -> prog -> real
  
  (* hill *)
  val init_hill : int * int -> int list list -> pfn * ex list
  val loop_hill : ex list -> pfn -> int -> unit

  
  
end
