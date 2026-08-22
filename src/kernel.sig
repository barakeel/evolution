signature kernel =
sig

  include Abbrev
  type ('a,'b) dict = ('a, 'b) Redblackmap.dict
  
  exception Msg of string;
  
  (* directory *)
  val selfdir : string 
  
  (* config *) 
  val configd : (string,string) dict
   
  (* dictionaries shortcut*)
  val dfindo : 'a -> ('a, 'b) dict -> 'b option
  val eaddi : 'a -> 'a Redblackset.set ref -> unit
  val ememi : 'a -> 'a Redblackset.set ref -> bool
  val daddi : 'a -> 'b -> ('a, 'b) dict ref -> unit
  val dmemi : 'a -> ('a, 'b) dict ref -> bool
  val ereml : 'a list -> 'a Redblackset.set -> 'a Redblackset.set
  val dreml : 'a list -> ('a,'b) dict -> ('a,'b) dict
  
  (* string tools *)
  val cws : string list -> string 
  val tws : string -> string list
  val pe : string -> unit
  val infts : IntInf.int -> string
  val stinf : string -> IntInf.int
  val streal : string -> real
  val stint : string -> int
  val stil : string -> int list
  val ilts : int list -> string
  val split_pair : char -> string -> string * string
  
  (* list tools *)
  val range : int * int * (int -> 'a) -> 'a list

  (* general program primitives *)
  datatype prog = Ins of (int * prog list)
  val raw_prog : prog -> string
  val prog_compare : prog * prog -> order
  val equal_prog : prog * prog -> bool
  val prog_size : prog -> int
  val prog_compare_size : prog * prog -> order
  
  (* parallelization of function of the type string to string *)
  val stringspec_fun_default : string -> string
  val stringspec_fun_glob : (string -> string) ref
  val stringspec_funname_glob : string ref
  val stringspec : (unit, string, string) smlParallel.extspec
  val parmap_sl : int -> string -> string list -> string list
  val test_fun : string -> string

end
