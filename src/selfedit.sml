load "aiLib"; open aiLib kernel sexp;

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
val empty = ([] : int list ,0)

fun checktimer n = 
  (
  timer := !timer + n;
  if !timer > !timelimit then raise Check else ()
  )

(* --------------------------------------------------------------------------
   Annotated list
   -------------------------------------------------------------------------- *)

fun lpop (l,n) = case l of [] => empty | a :: m => (m,n-1)
fun lpush a (m,n) = if n+1 > !timelimit then raise Check else (a :: m,n+1)

(* --------------------------------------------------------------------------
   Primitives
   -------------------------------------------------------------------------- *)

fun xvar fl (x,y) = (checktimer 1; x)
fun yvar fl (x,y) = (checktimer 1; y)
fun nullf fl (x,y) = (checktimer 1; empty)
fun zerof fl (x,y) = (checktimer 1; ([0],1))
fun onef fl (x,y) = (checktimer 1; ([1],1))

val self_glob = ref empty
fun selff fl (x,y) = (checktimer 1; !self_glob)
val selfm_glob = ref empty
fun selfmf fl (x,y) = (checktimer 1; !selfm_glob)

val opp_glob = ref empty
fun oppf fl (x,y) = (checktimer 1; !opp_glob)
val oppm_glob = ref empty
fun oppmf fl (x,y) = (checktimer 1; !oppm_glob)


fun negf fl = case fl of 
  [f] => (fn (x,y) => 
          let 
            val _ = checktimer 1
            val (l,n) = f (x,y) 
          in 
            case l of [] => empty | za :: zm => (1 - za :: zm,n)
          end
         )
  | _ => raise Msg "incrf"

fun incrf fl = case fl of 
  [f] => (fn (x,y) => 
          let 
            val _ = checktimer 1
            val (l,n) = f (x,y) 
          in 
            case l of [] => empty | za :: zm => (za + 1 :: zm,n)
          end
         )
  | _ => raise Msg "incrf"
  
fun decrf fl = case fl of 
  [f] => (fn (x,y) => 
          let 
            val _ = checktimer 1
            val (l,n) = f (x,y) 
          in 
            case l of [] => empty | za :: zm => (za - 1 :: zm,n)
          end
         )
  | _ => raise Msg "decrf"

fun pop fl = case fl of 
    [f] => (fn (x,y) => (checktimer 1; lpop (f (x,y))))
  | _ => raise Msg "pop"

fun push fl = case fl of
   [f1,f2] => (fn (x,y) => 
    (
    checktimer 1; 
    let val ((l1,n1),(l2,n2)) = (f1 (x,y),f2 (x,y)) in 
      case l1 of a :: _ => lpush a (l2,n2) | _ => (l2,n2)
    end
    ))
  | _ => raise Msg "push"

fun reverse_aux acc l = 
  (checktimer 1;
   case l of [] => acc | a :: m => reverse_aux (a :: acc) m)

fun reverse fl = case fl of 
    [f] => (fn xy => let val (l,n) = f xy in (reverse_aux [] l,n) end)
  | _ => raise Msg "reverse"

fun concatrev l1 l2 = 
  (
  checktimer 1;
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
  checktimer 1;
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

fun while3_aux f x y = 
   (
   checktimer 1;
   case x of ([],_) => y | (a :: m,n) => while3_aux f (m,n-1) (f (x,y))
   )

fun while3 fl = case fl of
    [f1,f2,f3] => (fn xy => (checktimer 1; while3_aux f1 (f2 xy) (f3 xy)))
  | _ => raise Msg "while3"

fun condnull fl = case fl of
    [f1,f2,f3] => (fn xy => 
    (checktimer 1; case f1 xy of ([],_) => f2 xy | _ => f3 xy))
  | _ => raise Msg "condnull"

fun condpos fl = case fl of
    [f1,f2,f3] => (fn xy => 
    (checktimer 1; case f1 xy of ([],_) => f3 xy 
      | (a :: _, _) => if a > 0 then f2 xy else f3 xy))
  | _ => raise Msg "condpos"

(* --------------------------------------------------------------------------
   Creating executables
   -------------------------------------------------------------------------- *)

fun int_of_bin l = case l of 
    [] => (checktimer 1; 0)
  | a :: m => (checktimer 1; (if a > 0 then 1 else 0) + 2 * int_of_bin m)

fun bin_of_int n i = if n <= 0 then [] else
  i mod 2 :: bin_of_int (n-1) (i div 2) 

exception Open;

fun s13 (a,b,c) = a
fun s33 (a,b,c) = c 

fun progl_of_bin ev acc n l =
   (
   checktimer 1;
   if n <= 0 then (rev acc, l) else
   (
   case l of 
     a :: b :: c :: d :: m => 
   let val id = int_of_bin [a,b,c,d] in 
     if id >= Array.length ev then progl_of_bin ev acc n m else
     let 
       val arity = s33 (Array.sub (ev, id))
       val (argl,cont) = progl_of_bin ev [] arity m
       (* val _ = if length argl <> arity 
         then raise Msg ("progl_of_bin: " ^ its id ^ "," ^ its arity ^ "," ^ 
         its (length argl)) else () *)
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
  checktimer 1;
  let val ef = s13 (Array.sub (ev, id)) in 
    ef (map (mk_exec ev) pl) 
  end
  )
  
val execa = Array.fromList [
  (xvar,"fake_exec",3), (xvar,"x",0), (yvar, "y", 0),
  (zerof, "0", 0), (onef, "1", 0),
  (selff, "self", 0), (* (selfmf, "selfm",0), *) 
  (oppf, "opp", 0), (* (oppmf, "oppm", 0), *)
  (pop, "pop", 1), (negf, "not", 1), (* (decrf, "decr", 1), *) 
  (reverse, "rev", 1), (push, "push", 2), 
  (* (concat, "concat", 2), *) (interleave, "interleave", 2),
  (while3, "while", 3), (condpos, "condpos", 3)
  ]
  
val _ = if Array.length execa > 16 then raise Msg "execa is too big" else ()

fun exec fl = case fl of
    [f1,f2,f3] => (fn (x,y) => 
    (
    checktimer 1; 
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
  
val _ = Array.update (execa, 0, (exec, "exec", 3)); 

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

fun unflatten_prog_aux ev acc n l =
   (
   if n <= 0 then (rev acc, l) else
   (
   case l of 
     id :: m => 
     if id >= Array.length ev then unflatten_prog_aux ev acc n m else
     let 
       val arity = s33 (Array.sub (ev,id))
       val (argl,cont) =  unflatten_prog_aux ev [] arity m
     in
       unflatten_prog_aux ev (Ins (id,argl) :: acc) (n-1) cont
     end
   | _ => raise Open
   )
   );
  
fun unflatten_prog l = 
  case (fst (unflatten_prog_aux execa [] 1 l) handle Open => []) of
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
    (List.tabulate (n, fn _ => random_int (~10,10)), n)
  end;
  
fun randind () = 
  let val p = randprog () in ((p, mk_exec_err p, randmem 40) : ind) end;

fun boil l = case l of [] => 0 | a :: m => if a > 0 then 1 else 0;

fun timedf f x = (timer := 0; f x handle Check => empty);

fun reproduce (p1,f1,mem1) (p2,f2,mem2) = 
  let 
    val self = bin_of_prog p1
    val _ = self_glob := (self,length self) 
    val _ =  selfm_glob := mem1
    val opp = bin_of_prog p2
    val _ = opp_glob := (opp,length opp)
    val _ = oppm_glob := mem2
  in
    case proglo_of_bin_err (fst (timedf f1 (empty,empty))) of
      SOME (p,_) => (p, mk_exec_err p, empty)
    | NONE => randind ()
  end;
  
val pp = pe o string_of_prog;

(*
val _ = (pe (its ai); pp (#1 a); print_endline (ilts (fst (#3 a))))
val _ = (pe (its bi); pp (#1 b); print_endline (ilts (fst (#3 b))))
*)

(* --------------------------------------------------------------------------
   Statistics
   -------------------------------------------------------------------------- *)


val local_tot = ref 0
val local_pos = ref 0
val global_tot = ref 0
val global_pos = ref 0

fun init_tracker () = 
  (local_tot := 0; local_pos := 0; global_tot := 0; global_pos := 0)

fun result_tracker r = 
  (
  incr local_tot; incr global_tot;
  if r > 0 then (incr local_pos; incr global_pos) else ()
  )

val popa_counter = ref 0

fun popa_tracker popa = 
  (
  incr popa_counter;
  if !popa_counter mod 10000 <> 0 then () else 
  let 
    val l0 = array_to_list popa;
    val l1 = map snd l0
    val s1 = "loc " ^ pretty_real (int_div (!local_pos) (!local_tot))
    val s2 = "glob " ^ pretty_real (int_div (!global_pos) (!global_tot))
    val s3 = "age " ^ pretty_real (average_int (map fst l1))
    val s4 = "anc " ^ pretty_real (average_int (map snd l1))
    val _ = (local_tot := 0; local_pos := 0)
  in
    pe (its (!popa_counter div 10000) ^ ": " ^ 
        String.concatWith ", " [s1,s2,s3,s4])
  end
  )
    
(* --------------------------------------------------------------------------
   Parity game
   -------------------------------------------------------------------------- *)

fun boi i = if i > 0 then 1 else 0

fun parity_genf () = let val (game,n) = randmem 10 in
   ((game,n), length (filter (fn x => x > 0) game) mod 2)
  end 

fun greater_genf () = let val (game,n) = randmem 10 in
   ((game,n), if length (filter (fn x => x > 0) game) > 5 then 1 else 0)
  end

fun game genf n nmax ((p1,f1,mem1): ind) ((p2,f2,mem2): ind) r1 r2 = 
  if n >= nmax then ((p1,f1,mem1),(p2,f2,mem2), sum_int r1, sum_int r2) else
  let
    val (input,output) = genf ()
    val newmem1 = timedf f1 (input,(r1,n))
    val newmem2 = timedf f2 (input,(r2,n))
    val r1e = if boil (fst newmem1) = output then 1 else 0
    val r2e = if boil (fst newmem2) = output then 1 else 0
    val _ = result_tracker r1e
    val _ = result_tracker r2e
  in
    game genf (n+1) nmax (p1,f1,newmem1) (p2,f2,newmem2) (r1e :: r1) (r2e :: r2)
  end

fun update_pop popa =
  let 
    val _ = popa_tracker popa
    val (ai,bi) = randpair popa
    val ((a : ind),(aage,aanc)) = Array.sub (popa,ai)
    val ((b : ind),(bage,banc)) = Array.sub (popa,bi)
    val _ = opp_glob := empty
    val _ = oppm_glob := empty
    val _ = self_glob := empty
    val _ = selfm_glob := empty
    val genf = if random_real () < 0.5 then parity_genf else greater_genf 
    val (newa,newb,r1,r2) = game genf 0 30 a b [] []
    val ((winner,winneri),(loser,loseri)) = 
      if r1 >= r2 then ((newa,ai),(newb,bi)) else ((newb,bi),(newa,ai))
    val child = 
      if random_real () < 0.5 
      then (randind (), (0,0)) 
      else (reproduce winner loser, (0, Int.max (aanc,banc) + 1))
  in
    Array.update (popa, winneri, (winner, (aage + 1, aanc)));
    Array.update (popa, loseri, child)
  end;

(*
load "selfedit";

(* need some possibility to learn as individual and across generations *)

init_tracker ();
val popa = Array.tabulate (100, fn _ => (randind (),(0,0)));
fun f () = update_pop popa;
val (_,t) = add_time (funpow 10000000 f) ();


 val l0 = array_to_list popa;
    val l1 = map fst l0;
app (pp o #1) l1;
pp (#1 (Array.sub (initpopa,n)));
  
*)

