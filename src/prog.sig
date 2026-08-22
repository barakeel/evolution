signature prog =
sig

  type prog = kernel.prog

  (* id list representation *)
  val flatten_prog : prog -> int list
  val unflatten_prog : int list -> prog
  
  (* sexp/string representation *)
  val prog_of_string : string -> prog
  val string_of_prog : prog -> string
  
  (* intinf representation *)
  val zip_prog : prog -> IntInf.int
  val unzip_prog : IntInf.int -> prog
  
  (* binary representation *)
  val binl_of_int : int -> int -> int list
  val binl_of_idl : int list -> int list
  val binl_of_prog : prog -> int list
   
  (* random *)
  val random_prog_size : int -> prog
  val random_prog : unit -> prog

  (* oeis *)
  val read_oeis : unit -> int list list
     
end
