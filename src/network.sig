signature network =
sig

  type obj = exec.obj
  type exec = exec.exec
  type prog = kernel.prog
  
  type 'a net = 'a vector vector
  type iv = int -> int
  type ex = iv * int
  type pfn = (prog ref * exec ref * int list ref * int list ref) net
  type cache = int ref net
  type node = int * int
  type negpos = int * int

  (* stats *)
  val prog_skip : int ref
  val scaling : int
  
  (* net primitives *)
  val width_of_net : 'a net -> int
  val depth_of_net : 'a net -> int
  val dim_of_net : 'a net -> int * int 
  val net_app : ('a * int * int -> unit) -> 'a net -> unit
  val net_sub : 'a net -> int * int -> 'a
  val net_tabulate : int * int -> (int * int -> 'a) -> 'a net
  val flatten_pfn : pfn -> prog list
  val pfn_compare : pfn * pfn -> order
  val read_pfn : string -> pfn
  val write_pfn : string -> pfn -> unit
  
  (* initialization *)
  val ex_of_sentencel : int list list -> ex list
  val init_pfn : int * int -> pfn
  val cache_empty : int
  val init_cache : pfn -> cache
  
  (* dependency graph *)
  val dep_of_prog : pfn -> node -> prog -> int list
  val descendant : pfn -> (int * int list) -> (int * int list) list  
  val update_sdep : pfn -> node -> unit
  val recompute_alldep : pfn -> unit
  val update_prog_partial : pfn -> node -> (prog * int list * exec) -> unit
  
  (* computing a single node *)
  val recompute_node_unit : iv -> cache -> pfn -> node -> unit
  val recompute_node : iv -> cache -> pfn -> node -> int
  val reset_flag : bool ref
  val resetl_glob : (unit -> unit) list ref
  
  (* score *)
  val score_negpos : int * (int * int) -> int
  val score_01 : cache -> pfn -> negpos -> node -> ex -> 
    (negpos * negpos) * (int * int)
  val score_prog : cache -> pfn -> node -> ex -> 
    (negpos * negpos) * (int * int) -> (prog * int list * exec) -> (int * int)
  val score_nodep : pfn -> ex -> (negpos * int)
  
end
