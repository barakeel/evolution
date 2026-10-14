structure prog :> prog =
struct

open HolKernel aiLib kernel sexp exec

fun contain_id id (Ins(x,pl)) = id = x orelse exists (contain_id id) pl

val loopid = get_id "loop" 

fun contain_id_fo id (Ins(x,pl)) = 
  if id = x then true else 
  let val pl' = if x = loopid then tl pl else pl in
    exists (contain_id_fo id) pl'
  end

(* --------------------------------------------------------------------------
   Program representations from ast: int list, bool list, intinf, sexp
   -------------------------------------------------------------------------- *)

(* int list *)
exception Open

fun flatten_prog ptop =
  let 
    val r = ref [] 
    fun loop (Ins (id,pl)) = (r := id :: !r; app loop pl)
  in 
    loop ptop; rev (!r)
  end

fun unflatten_progl_aux acc n l =
   (
   if n <= 0 then (rev acc, l) else
   (
   case l of 
     id :: m => 
     if id >= Vector.length execv then unflatten_progl_aux acc n m else
     let 
       val arity = get_arity id
       val (argl,cont) =  unflatten_progl_aux [] arity m
     in
       unflatten_progl_aux (Ins (id,argl) :: acc) (n-1) cont
     end
   | _ => raise Open
   )
   );
  
fun unflatten_prog l = 
  case (fst (unflatten_progl_aux [] 1 l) handle Open => []) of
    [p] => p
  | _ => raise Msg "unflatten_prog: arity"
 
(* intinf *)
fun zip_il base l =
  let 
    open IntInf
    val basei = fromInt base
    val r = ref 1 
    fun f a = r := !r * basei + fromInt a
  in 
    app f l; !r
  end;
  
fun unzip_il base itop =
  let 
    open IntInf
    val basei = fromInt base
    val r = ref [] 
    fun loop i = if i < basei then () else
      (r := toInt (i mod basei) :: !r; loop (i div basei))
  in 
    loop itop; !r
  end; 
  
fun zip_prog p = zip_il (Vector.length execv) (flatten_prog p);
fun unzip_prog i = unflatten_prog (unzip_il (Vector.length execv) i);

(* sexp *)
fun sexp_of_prog p = case p of 
    Ins (~1,[Ins(i,[])]) => Atom (its (i - Vector.length execv))
  | Ins (n,[]) => Atom (get_name n)
  | Ins (n,pl) => Sexp (Atom (get_name n) :: map sexp_of_prog pl) 

val string_of_sexp = sexp_to_string
val string_of_prog = string_of_sexp o sexp_of_prog;

fun prog_of_sexp sexp = case sexp of
    Atom s => Ins (get_id s,[])
  | Sexp (Atom s :: m) => Ins (get_id s, map prog_of_sexp m)  
  | _ => raise Msg "prog_of_sexp" 

val sexp_of_string = string_to_sexp
val prog_of_string = prog_of_sexp o sexp_of_string

(* bool list *)
fun binl_of_int n i = if n <= 0 then [] else
  i mod 2 :: binl_of_int (n-1) (i div 2)  
fun binl_of_prog p = List.concat (map (binl_of_int 4) (flatten_prog p));  
 
(* --------------------------------------------------------------------------
   Random program
   -------------------------------------------------------------------------- *)
 
(* val readid = get_id "read"  *)
val readiid = get_id "readi"
val loopid = get_id "loop"  
val xid = get_id "x"
val yid = get_id "y"
val zid = get_id "z"

val arityl = (* filter (fn x => not (mem (fst x) [zid])) *)
  (List.tabulate (Vector.length execv, fn i => (i, get_arity i)))
  
val arityl0 = map fst (filter (fn x => snd x = 0) arityl)
val arityl0x = filter (fn x => not (mem x [xid,yid])) arityl0
val aritylpos = filter (fn x => snd x > 0) arityl

(* under read *)
val constl = first_n 6 arityl
val constl0 = map fst (filter (fn x => snd x = 0) constl)
val constlpos = filter (fn x => snd x > 0) constl

(* read random *)
(* val random_read () = Ins (readiid, *) 

fun random_prog_size readb n = 
  let val l0 = if readb then constl0 else arityl0 in
  if n <= 1 then Ins (random_elem l0,[]) else
  let
    val candl = filter (fn x => snd x <= n - 1) 
      (if readb then constlpos else aritylpos) 
    val (id,arity) = 
      if null candl 
      then raise Msg "needs at least one arity 1 operator" 
      else random_elem candl
    val l = random_elem (number_partition arity (n - 1))
  in
    if id = readiid 
      then Ins (id, map (random_prog_size true) l)
    else if id = loopid 
      then 
      let val (a,b,c) = triple_of_list l in
        Ins(id, [random_prog_size readb a, 
                 random_prog_size readb b,
                 random_prog_size readb c])
      end
    else Ins (id, map (random_prog_size readb) l)
  end   
  end
  
fun count_readiid (Ins(i,pl)) = 
  if i = readiid then 1 else sum_int (map count_readiid pl)
  
fun random_prog () = 
  let val p = random_prog_size false (random_int (5,20)) in 
    if count_readiid p <= 1
    then random_prog ()
    else p
  end
  
(* --------------------------------------------------------------------------
   Compute static dependencies in a program
   -------------------------------------------------------------------------- *)

fun eval_const p = (mk_exec p) (0,0)

fun collect_readargl_aux loopb r (Ins(i,pl)) =
  if i = xid andalso not loopb then r := ~1 :: !r else
  if i = yid andalso not loopb then r := 1 :: !r else
  if i = zid then r := 0 :: !r else
  if i = readiid then r := eval_const (hd pl) :: !r else
  if i = loopid then 
    let val (a,b,c) = triple_of_list pl in
      collect_readargl_aux true r a;
      collect_readargl_aux loopb r b;
      collect_readargl_aux loopb r c
    end
  else app (collect_readargl_aux loopb r) pl
  
fun collect_readargl p =
  let val r = ref [] in 
    collect_readargl_aux false r p; 
    mk_fast_set Int.compare (!r) 
  end

(* --------------------------------------------------------------------------
   Reading OEIS programs
   -------------------------------------------------------------------------- *)
  
fun id_of_char s = 
  let val n = Char.ord (valOf (Char.fromString s)) in n - 65 end

fun idl_of_string s = 
  let val sl = tws s in map id_of_char sl end

fun read_line_aux acc il = case il of 
    [] => List.concat (rev acc) 
  | i :: m => read_line_aux (binl_of_int 4 i :: acc) m

fun binl_of_idl il = read_line_aux [] il

fun read_oeis () = 
  let
    val (sl0,t) = 
      add_time readl (selfdir ^ "/../../oeis-synthesis/src/data/oeis_smallprog")
    val _ = pe ("reading time: " ^ rts_round 2 t)
    val (sl1,t) = add_time (map (snd o (split_pair #":"))) sl0
    val _ = pe ("splitting time: " ^ rts_round 2 t)
    val (sl2,t) = add_time (map idl_of_string) sl1
    val _ = pe ("token time: " ^ rts_round 2 t)
  in
    sl2
  end
  
end (* struct *)

(*
load "prog"; open prog;
val p = random_prog ();
string_of_prog p;
collect_readargl p;
*)



