signature network =
sig

  type obj = exec.obj
  type exec = exec.exec
  type prog = kernel.prog
  
  type 'a net = 'a vector vector
  type ex = (int vector * (int * int ref * int ref)) list
  type cache = (int ref net * (int * int ref * int ref)) list
  type pfn = (prog ref * exec ref * int ref * int list ref * int list ref) net
  type pn = cache * pfn
  type pnx = pn * real
  
  val run_time : int ref
  val node_counter : int ref 
  val node_dep_counter : int ref
  val conf_penalty : real ref
  
  val flatten_pn : pn -> prog list
  val pn_compare : pn * pn -> order
  
  (* net primitives *)
  val width_of_net : 'a net -> int
  val depth_of_net : 'a net -> int
  val dim_of_net : 'a net -> int * int 
  val net_app : ('a * int * int -> unit) -> 'a net -> unit
  val net_sub : 'a net -> int * int -> 'a
  val net_tab : int * int -> (int * int -> 'a) -> 'a net
  
  val score_negpos : int * (int * int) -> real
  
  (* running a program network without cache *) 
  val infer_test : pfn -> ex -> (real * real)
  
  (* example init *)
  val ex_of_sentencel : int -> int list list -> ex
  val inputvl_of_ex : ex -> (int ref vector * int) list
  val objl_of_ex : ex -> int list
  val init_cache : ex -> pfn -> cache
  val init_vcache : int * int -> int ref net
  
  (* program init *)
  val random_pfn : int * int -> pfn
 
  (* dependency graph *)
  val recompute_alldep : pfn -> unit
  val descendant : pfn -> (int * int list) -> (int * int list) list  
    
  (* computing a single node *)
  val recompute_node : 
    int ref vector -> int ref vector vector -> pfn -> (int * int) -> unit
  val negpos_inputv :
    pfn -> (int * int) list -> int ref vector -> int * int
  val negpos_01 :  
    pfn -> int * int -> int ref vector -> (int * int) * (int * int)
  val score_01 : 
    pfn -> int * int -> int ref vector * int -> real * real
  val score_prog : 
    pfn -> int * int -> int ref vector * int -> real * real -> prog -> real
  val init_hill : int * int -> int list list -> pfn * (int ref vector * int) list
  val loop_hill :  (int ref vector * int) list -> pfn -> int -> unit


    
  (* updating the network *)
  val undol_glob : (unit -> unit) list ref
  val cache_glob : cache ref
  
  val score_pn : pn -> (real * real list)
  val random_pnx : int * int -> ex -> pnx
  val update_pn : pn -> (prog * int * int) -> unit
  val update_sdep : pfn -> (int * int) -> unit
  
end
