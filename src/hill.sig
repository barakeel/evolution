signature hill =
sig

  type pnx = network.pnx
  type ex = network.ex
  type param =
    {wid: int, exl: ex, exlt: ex,
     rt: Timer.real_timer, rtmax: Time.time, share : bool} 
  
  (* logging *)
  val log_time : real ref
  val io_time : real ref
  val expname : string ref 
   
  (* hill climbing *)
  val hill : param -> pnx -> pnx
  val run_single : (int * int * real) -> ex * ex -> pnx
  (* val hill_para : string -> string *)
  
  (* wrappers *)
  
  
  (* 
  val run_para : int -> string -> ex -> (int * int * real)  -> real
  val run_test : int -> string -> ex -> (int * int * real) list -> real list
  *)
  
end
