signature network =
sig

  type obj = exec.obj
  type exec = exec.exec
  type prog = kernel.prog
  
  type 'a net = 'a vector vector
  type cache = (int ref net * (int * int * int ref * int ref)) list
  type pfn = (prog ref * exec ref * int ref * int list ref * int list ref) net
  type pn = cache * pfn
  type pnx = pn * real
  type ex = (int vector * (int * int * int ref * int ref)) list
  
  val run_time : int ref
  val node_counter : int ref 
  val node_dep_counter : int ref
  val conf_penalty : real ref
  
  val flatten_pn : pn -> prog list
  val pn_compare : pn * pn -> order
  val width_of_net : 'a net -> int
  val depth_of_net : 'a net -> int
  val dim_of_net : 'a net -> int * int 
  
  (* input/output: includes loss and total time *)
  (*
  val write_pnx : string -> pnx -> unit
  val read_pnx : string -> pnx
  *)

  (* running a program network without cache *) 
  val infer_test : pfn -> ex -> (real * real)
  
  (* data collection *)
  (*
  val obj_network : int vector list ref
  val access_network : int list list list ref
  *)
  (* example initialization *)
  val vol_of_sentencel : int -> int list list -> ex
    
  (* updating the network *)
  val undol_glob : (unit -> unit) list ref
  val cache_glob : cache ref
  val init_cache : ex -> pfn -> cache
  val score_pn : pn -> (real * real list)
  val random_pnx : int * int -> ex -> pnx
  val update_pn : pn -> (prog * int * int) -> unit
  val update_sdep : pfn -> (prog * int * int) -> unit
  
end
