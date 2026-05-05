load "aiLib"; open aiLib kernel sexp mlMatrix;

exception Msg of string;
exception Check;
exception Unexpected;

type obj = int list * int
type exec = obj * obj -> obj
type ind = prog * exec * obj;

(* --------------------------------------------------------------------------
   Timer
   -------------------------------------------------------------------------- *)

val timer = ref 0;
val timelimit = ref 1000;
val empty = ([] : mat list ,0)

fun ct n = 
  (timer := !timer + n; if !timer > !timelimit then raise Check else ())

(* --------------------------------------------------------------------------
   Primitives
   -------------------------------------------------------------------------- *)

val dim = 16

(* nullary operations *)
val mat1 = let fun f i j = if i = j then ~1.0 else 0.0 in 
  mat_tabulate f (dim,dim) end
fun matrand () = 
  let 
    val coeff = (int_div 1 dim)
    fun f i j =  coeff * random_real () - 0.5 * coeff 
  in 
    mat_tabulate f (dim,dim) 
  end
fun xvar fl (x,y) = (ct 1; x)
fun yvar fl (x,y) = (ct 1; y)
fun nullf fl (x,y) = (ct 1; empty)
fun onef fl (x,y) = (ct 1; ([mat1],1))
fun randf fl (x,y) = (ct 40; ([matrand ()],1))

(* matrix operations *)
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

fun matrelu m = let fun f x = if x > 0.0 then x else 0.0 in mat_map f m end
fun matreluf fl = unf matrelu fl 

fun matnorm m = let fun f x = if x > 10.0 then 10.0 else 
   if x < ~10.0 then ~10.0 else x in mat_map f m end
fun matnormf fl = unf matnorm fl

fun binf oper fl = case fl of
   [f1,f2] => (fn (x,y) => 
    (
    ct 1; 
    let val ((l1,n1),(l2,n2)) = (f1 (x,y),f2 (x,y)) in 
      case (l1,l2) of ([],_) => l1 | (_,[]) => l1 | (a1 :: b1, a2 :: b2) =>
      oper a1 a2 :: b1
    end
    ))
  | _ => raise Msg "binf"

fun addf fl = binf mat_add fl
fun multf fl = binf mat_mult fl

(* list operations *)
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

fun reverse_aux acc l = 
  (ct 1;
   case l of [] => acc | a :: m => reverse_aux (a :: acc) m)

fun reverse fl = case fl of 
    [f] => (fn xy => let val (l,n) = f xy in (reverse_aux [] l,n) end)
  | _ => raise Msg "reverse"

fun concatrev l1 l2 = 
  (
  ct 1;
  case l1 of [] => l2 | a :: m => concatrev m (a :: l2)
  )
  
fun concat fl = case fl of
    [f1,f2] => (fn xy => 
    let val ((l1,n1),(l2,n2)) = (f1 xy, f2 xy) in
      if n1 + n2 > !timelimit then raise Check else
      (concatrev (reverse_aux [] l1) l2, n1 + n2)
    end
    )
  | _ => raise Msg "concat"

fun interleave_aux a b = 
  (
  ct 1;
  case (a,b) of
    (_,[]) => a
  | ([],_) => b
  | (ae :: am, be :: bm) => ae :: be :: interleave_aux am bm
  )
  
fun interleave fl = case fl of
    [f1,f2] => (fn xy => 
    let val ((l1,n1),(l2,n2)) = (f1 xy, f2 xy) in
      if n1 + n2 > !timelimit then raise Check else
      (interleave_aux l1 l2, n1 + n2)
    end
    )
  | _ => raise Msg "interleave"

(* control flow operations *)
fun while3_aux f x y = 
   (
   ct 1;
   case x of ([],_) => y | (a :: m,n) => while3_aux f (m,n-1) (f (x,y))
   )

fun while3 fl = case fl of
    [f1,f2,f3] => (fn xy => (ct 1; while3_aux f1 (f2 xy) (f3 xy)))
  | _ => raise Msg "while3"

fun whilen_aux f x y = 
   (
   ct 1;
   case x of ([],_) => y | (a :: m,n) => 
     if a <= 0 then y else whilen_aux f (a-1 :: m, n) (f (x,y))
   )

fun whilen fl = case fl of
    [f1,f2,f3] => (fn xy => (ct 1; whilen_aux f1 (f2 xy) (f3 xy)))
  | _ => raise Msg "whilen"

fun condnull fl = case fl of
    [f1,f2,f3] => (fn xy => 
    (ct 1; case f1 xy of ([],_) => f2 xy | _ => f3 xy))
  | _ => raise Msg "condnull"

fun condpos fl = case fl of
    [f1,f2,f3] => (fn xy => 
    (ct 1; case f1 xy of ([],_) => f3 xy 
      | (a :: _, _) => if a > 0 then f2 xy else f3 xy))
  | _ => raise Msg "condpos"

(* --------------------------------------------------------------------------
   Creating executables
   -------------------------------------------------------------------------- *)

fun int_of_bin_notimer l = case l of 
    [] => 0
  | a :: m => (if a > 0 then 1 else 0) + 2 * int_of_bin_notimer m

fun int_of_bin l = case l of 
    [] => (ct 1; 0)
  | a :: m => (ct 1; (if a > 0 then 1 else 0) + 2 * int_of_bin m)

fun bin_of_int n i = if n <= 0 then [] else
  i mod 2 :: bin_of_int (n-1) (i div 2) 

exception Open;

fun s13 (a,b,c) = a
fun s33 (a,b,c) = c 

fun progl_of_bin ev acc n l =
   (
   ct 1;
   if n <= 0 then (rev acc, l) else
   (
   case l of 
     a :: b :: c :: d :: m => 
   let val id = int_of_bin [a,b,c,d] in 
     if id >= Array.length ev then progl_of_bin ev acc n m else
     let 
       val arity = s33 (Array.sub (ev, id))
       val (argl,cont) = progl_of_bin ev [] arity m
     in
       progl_of_bin ev (Ins (id, argl) :: acc) (n-1) cont
     end
   end
   | _ => raise Open
   )
   )
   
fun flatten_prog ptop =
  let 
    val r = ref [] 
    fun loop (Ins (id,pl)) = (r := id :: !r; app loop pl)
  in 
    loop ptop; rev (!r)
  end;
   
fun bin_of_prog p = List.concat (map (bin_of_int 4) (flatten_prog p));

fun mk_exec ev (Ins (id,pl)) =
  (
  ct 1;
  let val ef = s13 (Array.sub (ev, id)) in 
    ef (map (mk_exec ev) pl) 
  end
  )
  
val execa = Array.fromList [
  (* (xvar,"fake_exec",3), *) 
  (xvar,"x",0), (yvar, "y", 0),
  (zerof, "0", 0), (onef, "1", 0), (* (randf, "randf", 0), *)
  (negf, "not", 1), (incrf, "incr",1), (decrf, "decr", 1), 
  (* (reverse, "rev", 1), *) (pop, "pop", 1),  (push, "push", 2), 
  (* (concat, "concat", 2), (interleave, "interleave", 2), *)
  (whilen, "whilen", 3), (while3, "while", 3)
  (* (condpos, "condpos", 3), (condnull, "condnull", 3) *)
  ]
  
val _ = if Array.length execa > 16 then raise Msg "execa is too big" else ()

fun exec fl = case fl of
    [f1,f2,f3] => (fn (x,y) => 
    (
    ct 1; 
    let 
      val (z1,z2,z3) = (f1 (x,y), f2 (x,y), f3 (x,y)) 
      val po = case (SOME (progl_of_bin execa [] 1 (fst z1)) 
        handle Open => NONE) of 
          SOME ([ploc],_) => SOME ploc 
        | _ => NONE
      val f = case po of NONE => fst | SOME p => mk_exec execa p
    in 
      f (z2,z3) 
    end
    ))
  | _ => raise Msg "exec"
  
(* val _ = Array.update (execa, 0, (exec, "exec", 3)); *)

fun get_arity n = #3 (Array.sub (execa,n))
fun get_name n = #2 (Array.sub (execa,n))

fun mk_exec_err p = (timer := 0; mk_exec execa p handle Check => fst)

val arityl = List.tabulate (Array.length execa, fn i => (i, get_arity i))
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

fun sexp_of_prog (Ins (n,pl)) = case pl of 
    [] => Atom (get_name n)
  | _ => Sexp (Atom (get_name n) :: map sexp_of_prog pl) 

val string_of_sexp = sexp_to_string
val string_of_prog = string_of_sexp o sexp_of_prog;

val pe = print_endline;

fun proglo_of_bin l = 
  let val r = progl_of_bin execa [] 1 l in
    case r of ([p],cont) => SOME (p,cont) | _ => NONE 
  end
  handle Open => NONE;

fun proglo_of_bin_err l = (timer := 0; proglo_of_bin l handle Check => NONE)

(* --------------------------------------------------------------------------
   Compressing programs
   -------------------------------------------------------------------------- *)

fun unflatten_progl_aux acc n l =
   (
   if n <= 0 then (rev acc, l) else
   (
   case l of 
     id :: m => 
     if id >= Array.length execa then unflatten_progl_aux acc n m else
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
  
fun zip_prog p = zip_il (Array.length execa) (flatten_prog p);
fun unzip_prog i = unflatten_prog (unzip_il (Array.length execa) i);

(* --------------------------------------------------------------------------
   Population of programs
   -------------------------------------------------------------------------- *)

fun randpair popa =
  let
    val ai = random_int (0, Array.length popa - 1)
    fun loop () = 
      let val b = random_int (0, Array.length popa - 1) in
        if b <> ai then b else loop ()
      end
    val bi = loop ()
  in
    (ai,bi)
  end;

fun randprog () = random_prog (random_int (1,40));
fun randmem k = 
  let val n = random_int (1,k) in 
    (List.tabulate (n, fn _ => random_int (0,1)), n)
  end;
  
fun randind () = 
  let val p = randprog () in ((p, mk_exec_err p, randmem 40) : ind) end;

fun boil l = case l of [] => 0 | a :: m => if a > 0 then 1 else 0;

fun timedf f x = (timer := 0; (f x handle Check => empty));
 
fun next_mem mem (p,f) = timedf f (mem,mem)

fun next_token mem pf =
  let
    val mem1 = next_mem mem pf
    val mem2 = next_mem mem1 pf
    val mem3 = next_mem mem2 pf
    val mem4 = next_mem mem3 pf
  in
    (int_of_bin_notimer (map (boil o fst) [mem1,mem2,mem3,mem4]), mem4) 
  end
  
fun next_prog_aux nmax npar acc mem pf = 
  if npar <= 0 then 
    (
    if null acc then (NONE,mem) else (SOME (unflatten_prog (rev acc)), mem)
    )
  else if nmax <= 0 then (NONE,mem) else
  let
    val (id,newmem) = next_token mem pf
    val arity = if id >= Array.length execa then 1 else get_arity id
    val newnpar = npar + arity - 1
    val newacc = if id >= Array.length execa then acc else id :: acc
  in
    next_prog_aux (nmax-1) newnpar newacc newmem pf
  end
  
fun next_prog nmax mem pf = next_prog_aux nmax 1 [] mem pf 
  
val pp = pe o string_of_prog;

fun loop_prog nprog acc mem pf =  
  if nprog <= 0 then rev acc else
  case next_prog 20 mem pf of
    (NONE,newmem) => loop_prog (nprog-1) acc newmem pf
  | (SOME p, newmem) => loop_prog (nprog-1) (p :: acc) newmem pf
;

fun random_genp () = SOME ()

fun score p = 
  let
    val f = mk_exec_err p
    val pl = loop_prog 100 [] empty (p,f)
  in
    length (mk_fast_set prog_compare pl)
  end;
  
fun search_random_aux i (p,sc) = 
  if i <= 0 then (p,sc) else
  (
  let 
    val newp = random_prog (random_int (5,20))
    val newsc = score newp 
  in
    if newsc > sc then 
      (
      pe ("  " ^ its i ^ ": " ^ its newsc ^ " " ^ string_of_prog newp);
      search_random_aux (i-1) (newp,newsc)
      )
    else search_random_aux (i-1) (p,sc)
  end
  );

fun search_random n = search_random_aux n (Ins(0,[]),~1)

fun search_aux i (pf,mem) (p,sc) = 
  if i <= 0 then (p,sc) else
  (
  case next_prog 20 mem pf of
    (NONE, newmem) => search_aux (i-1) (pf,newmem) (p,sc)
  | (SOME newp, newmem) => 
    let val newsc = score newp in
      if newsc > sc then 
        (
        pe ("  " ^ its i ^ ": " ^ its newsc ^ " " ^ string_of_prog newp);
        search_aux (i-1) (pf,newmem) (newp,newsc)
        )
      else search_aux (i-1) (pf,newmem) (p,sc)
    end
  );

fun search n (pf,mem) = search_aux n (pf,mem) (Ins(0,[]),~1)


fun gen_seq nmax acc mem pf = 
  if nmax <= 0 then rev acc else
  let val newmem = next_mem mem pf in
    gen_seq (nmax-1) (boil (fst newmem) :: acc) newmem pf
  end

fun random_bits () = 
  let
    val p = random_prog (random_int (5,20))
    val f = mk_exec_err p
  in
    gen_seq 1000 [] empty (p,f)
  end



(* create the function for estimating how good there are at producing random sequences *)

(* the dynamics at play: 
escapers are trying to create a function with an unpredictable behavior (this does not mean they are interesting) see noisy tv problem but not too unpredictable as distinguish between good and bad predictors. The best is that it can be  predicted somewhat correctly by a few programs with a smooth learning curve. Take the best programs and see how well they perform on those (if they are the same programs) 
programs behaving the same way could be penalized.

road blocks.
*)

(* take a program and see if it generates good program, just give up if it's not on par. *)

(*
load "selfedit";

timelimit := 10000;  

val l = random_bits ();

fun find_nseq n d =
  (
  if elength d >= 1000 then elist d else
  let val l = random_bits () in
     if n mod 1000 = 0 then print "." else ();
     if not (emem l d) then print "x" else ();
    find_nseq (n+1) (eadd l d)
  end
  );

val d = eempty (list_compare Int.compare);
val ll = find_nseq 0 d;
writel "data" (map ilts ll);
  
(* todo: generate 1000 sequences of 100 bits with small programs *)

fun loop i p =
  if i <= 0 then p else
  let val (newp,newsc) = search 10000 ((p,mk_exec_err p),empty) in
    pe (its i ^ ": " ^ its newsc ^ " " ^ string_of_prog newp);
    loop (i-1) newp
  end;
    
val (p0,sc0) = search_random 10000;
val p100 = loop 100 p0;
  
  
*)

