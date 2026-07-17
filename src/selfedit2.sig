signature selfedit2 =
sig

  val ptime : int
  val timelimit : int ref
  val read_oeis : unit -> real list list
  val randprog : unit -> kernel.prog
  val zip_prog : kernel.prog -> IntInf.int
  val unzip_prog : IntInf.int -> kernel.prog
  val string_of_prog : kernel.prog -> string
  val prog_of_string : string -> kernel.prog
  val score2f : string -> string
  val stats : string list -> real
  val half_loop : int -> int -> real -> real list -> 
    IntInf.int list -> IntInf.int list * real list
  
end
