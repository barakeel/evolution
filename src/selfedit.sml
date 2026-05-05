load "aiLib"; open aiLib kernel sexp mlMatrix;

exception Msg of string;
type obj = mat list * int
type exec = obj * obj -> obj
val pe = print_endline;

(* --------------------------------------------------------------------------
   Timer
   -------------------------------------------------------------------------- *)

exception Check;
val timer = ref 0;
val timelimit = ref 10000;
fun ct n = 
  (timer := !timer + n; if !timer > !timelimit then raise Check else ())

(* --------------------------------------------------------------------------
   Primitives
   -------------------------------------------------------------------------- *)

val dim = 16

(* nullary *)
val mat0 = let fun f i j = 0.0 in mat_tabulate f (dim,dim) end

fun mati_aux itop = 
  let fun f i j =  if i = itop then 1.0 else 0.0 in 
    mat_tabulate f (dim,dim)
  end
  
fun matrand () = 
  let 
    val coeff = (int_div 1 dim)
    fun f i j =  coeff * random_real () - 0.5 * coeff 
  in 
    mat_tabulate f (dim,dim) 
  end
  
fun xvar fl (x,y) = (ct 1; x)
fun yvar fl (x,y) = (ct 1; y)
val empty = ([] : mat list ,0)
fun nullf fl (x,y) = (ct 1; empty)
fun randf fl (x,y) = (ct 40; ([matrand ()],1))

(* matrix *)
fun unf oper fl = case fl of 
  [f] => (fn (x,y) => 
          let 
            val _ = ct 1
            val (l,n) = f (x,y) 
          in 
            case l of [] => empty | za :: zm => (oper za :: zm, n)
          end
         )
  | _ => raise Msg "incrf"

fun relu m = let fun f x = if x > 0.0 then x else 0.0 in mat_map f m end
fun reluf fl = unf relu fl 

fun norm m = let fun f x = if x > 10.0 then 10.0 else 
   if x < ~10.0 then ~10.0 else x in mat_map f m end
fun normf fl = unf norm fl

fun flip m = let fun f x = ~x in mat_map f m end
fun flipf fl = unf flip fl

fun transposef fl = unf mat_transpose fl

fun binf tim oper fl = case fl of
   [f1,f2] => (fn (x,y) => 
    let 
      val _ = ct tim
      val ((l1,n1),(l2,n2)) = (f1 (x,y),f2 (x,y)) 
    in 
      case (l1,l2) of 
        ([],_) => (l1,n1) 
      | (_,[]) => (l1,n1) 
      | (a1 :: b1, a2 :: b2) => (oper a1 a2 :: b1, n1)
    end)
  | _ => raise Msg "binf"

fun addf fl = binf 1 mat_add fl

fun mat_prod m1 m2 = 
  let 
    val m2t = mat_transpose m2
    fun f i j = scalar_product (Vector.sub (m1,i)) (Vector.sub(m2t,j))
  in
    mat_tabulate f (dim,dim)
  end

fun multf fl = binf dim mat_prod fl

(* list *)
fun lpop (l,n) = case l of [] => empty | a :: m => (m,n-1)

fun pop fl = case fl of 
    [f] => (fn (x,y) => (ct 1; lpop (f (x,y))))
  | _ => raise Msg "pop"

fun lpush a (m,n) = if n+1 > !timelimit then raise Check else (a :: m,n+1)
fun push fl = case fl of
   [f1,f2] => (fn (x,y) => 
    (
    ct 1; 
    let val ((l1,n1),(l2,n2)) = (f1 (x,y),f2 (x,y)) in 
      case l1 of a :: _ => lpush a (l2,n2) | _ => (l2,n2)
    end
    ))
  | _ => raise Msg "push"

(* control flow *)
fun while3_aux f x y = 
   (
   ct 1;
   case x of ([],_) => y | (a :: m,n) => while3_aux f (m,n-1) (f (x,y))
   )

fun while3 fl = case fl of
    [f1,f2,f3] => (fn xy => (ct 1; while3_aux f1 (f2 xy) (f3 xy)))
  | _ => raise Msg "while3"

fun condnull fl = case fl of
    [f1,f2,f3] => (fn xy => 
    (ct 1; case f1 xy of ([],_) => f2 xy | _ => f3 xy))
  | _ => raise Msg "condnull"


(* --------------------------------------------------------------------------
   Primitives
   -------------------------------------------------------------------------- *)

exception Open;

val execv = Vector.fromList 
  [
  (xvar,"x",0), (yvar, "y", 0), 
  (xvar,"x",0), (yvar, "y", 0), 
  (nullf, "null",0), (randf, "rand", 0),
  (reluf, "relu", 1), (normf, "norm",1), (flipf, "flip", 1), 
  (transposef, "transpose", 1),
  (addf, "add", 2), (multf, "mult", 2),
  (pop, "pop", 1), (push, "push", 2), (while3, "while", 3),
  (xvar, "quote", 1)]

val _ = if Vector.length execv > dim
        then raise Msg "execv is too big" else ()

fun get_fun n = #1 (Vector.sub (execv,n))
fun get_name n = #2 (Vector.sub (execv,n))
fun get_arity n = #3 (Vector.sub (execv,n))

fun flatten_prog ptop =
  let 
    val r = ref [] 
    fun loop (Ins (id,pl)) = (r := id :: !r; app loop pl)
  in 
    loop ptop; rev (!r)
  end;


fun mk_exec (Ins (id,pl)) = 
  if id = Vector.length execv - 1 (* quote *) then 
    let 
      val idl = flatten_prog (hd pl) 
      val r = (map mati_aux idl, length idl)
    in 
      (fn (x,y) => (ct 1; r))
    end
  else (get_fun id) (map mk_exec pl)

(* --------------------------------------------------------------------------
   Converting between syntax tree and token list and arbitrary integer 
   for program representation
   -------------------------------------------------------------------------- *)


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
  | _ => raise Msg "unflatten_prog";
 

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
 
(* --------------------------------------------------------------------------
   Random program
   -------------------------------------------------------------------------- *)
   
val arityl = List.tabulate (Vector.length execv, fn i => (i, get_arity i))
val arityl0 = map fst (filter (fn x => snd x = 0) arityl)
val aritylpos = filter (fn x => snd x > 0) arityl

fun random_prog n = 
  if n <= 1 then Ins (random_elem arityl0, []) else
  let
    val candl = filter (fn x => snd x <= n - 1) aritylpos 
    val (opern,arity) = random_elem candl
    val l = random_elem (number_partition arity (n - 1))
  in
    Ins (opern, map random_prog l)
  end   
 
fun randprog () = random_prog (random_int (5,20)); 

(* --------------------------------------------------------------------------
   Printing program
   -------------------------------------------------------------------------- *)

fun sexp_of_prog (Ins (n,pl)) = case pl of 
    [] => Atom (get_name n)
  | _ => Sexp (Atom (get_name n) :: map sexp_of_prog pl) 

val string_of_sexp = sexp_to_string
val string_of_prog = string_of_sexp o sexp_of_prog;

val pp = pe o string_of_prog;

(* --------------------------------------------------------------------------
   Generating a new program from an existing one
   -------------------------------------------------------------------------- *)

fun token_of_mem (l,_) = case l of 
    [] => random_int (0, Vector.length execv - 1)
  | m :: _ => 
    let 
      fun collect acc i =
        if i >= Vector.length execv then rev acc else 
        collect ((i,Vector.sub (Vector.sub (m,i),0)) :: acc) (i+1)
      val disl1 = collect [] 0
      fun f x = if Real.isFinite x then Math.tanh x else 0.0
      val disl2 = normalize_distrib (map_snd f disl1)
    in
      select_in_distrib disl2
    end
    
fun timedf f x = (timer := 0; (f x handle Check => empty));
fun next_mem mem hist (p,f) = timedf f (mem,hist)
fun next_token mem hist pf =
  let val newmem = next_mem mem hist pf in
    (token_of_mem newmem, newmem) 
  end
  
fun next_prog_aux nmax npar acc mem hist pf = 
  if npar <= 0 then 
    (if null acc then NONE else SOME (unflatten_prog (rev acc)))
  else if nmax <= 0 then NONE else
  let
    val (id,newmem) = next_token mem hist pf
    val newhist = (mati_aux id :: fst hist, snd hist + 1)
    val arity = if id >= Vector.length execv then 1 else get_arity id
    val newnpar = npar + arity - 1
    val newacc = if id >= Vector.length execv then acc else id :: acc
  in
    next_prog_aux (nmax-1) newnpar newacc newmem newhist pf
  end
  
fun next_prog nmax mem pf = next_prog_aux nmax 1 [] mem pf 
  
fun loop_prog n p = 
  if n <= 0 then SOME p else
  case next_prog 40 empty empty (p,mk_exec p) of
      NONE => NONE
    | SOME newp => loop_prog (n-1) newp

(*
load "selfedit";

timelimit := 10000;  

let val p = randprog () in  pp p; pp (valOf newpo);

fun compete (ncur,ntot) sum (bestp,bestsc) (ntry,depth) =
  if ncur >= ntot then ((bestp,bestsc), int_div sum ntot) else 
  let
    fun score d n p = 
      if n <= 0 then length (elist d) else
      let val newd =
        case loop_prog depth p of NONE => d | SOME c => eadd c d
      in
        score newd (n-1) p
      end
    val newp = randprog ()
    val newsc = score (eempty prog_compare) ntry newp
    val newsum = sum + newsc
    val (newbestp,newbestsc) = 
      if newsc > bestsc then (newp,newsc) else (bestp,bestsc)
  in
    compete (ncur+1,ntot) newsum (newbestp,newbestsc) (ntry,depth)
  end;

fun f i =   
  let 
    val (((p,bestsc),aversc),t) = 
      add_time (compete (0,1000) 0 (Ins (0,[]),~1)) (100,i);
  in
    pe (its i ^ ": " ^ rts_round 2 aversc ^ " " ^ its bestsc)
  end;
  
app f (List.tabulate (10,fn i => i+1));  
  
*)

