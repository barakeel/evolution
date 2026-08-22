signature hill =
sig

  type prognx = network.prognx
  type ex = network.ex
  type param =
    {wid: int, width: int, depth: int,
     exl: int list list,
     rt: Timer.real_timer, rtmax: Time.time,
     share : bool} 
   
  (* logging *)
  val log_time : real ref
  val io_time : real ref
  val expname : string ref 
  
  (* hill climbing *)
  val hill : param -> prognx -> prognx
  
  (* wrappers *)
  val run_single : (int * int * real) -> ex list -> prognx
  val run_para : int -> string -> ex list -> (int * int * real)  -> real
  val run_test : int -> string -> ex list -> (int * int * real) list -> real list
   
end
