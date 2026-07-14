signature selfedit2 =
sig

  val timelimit : int ref
  val read_oeis : unit -> real list list
  val randprog : unit -> kernel.prog
  val zip_prog : kernel.prog -> IntInf.int
  val unzip_prog : IntInf.int -> kernel.prog
  val string_of_prog : kernel.prog -> string
  val prog_of_string : string -> kernel.prog
  val score2f : string -> string
  
end
