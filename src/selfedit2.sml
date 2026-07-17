structure selfedit2 :> selfedit2 =
struct

open HolKernel aiLib kernel sexp
val ERR = mk_HOL_ERR "selfedit2"

exception Msg of string;
type obj = real list * int
type exec = obj * obj -> obj

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

(* helper *)
fun sing r = ([r], 1)  
val empty : obj = ([], 0)

(* task *)
val task_glob = ref empty
fun taskf fl (x,y) = (ct 1; !task_glob)

(* self *)
val self_glob = ref empty
fun selff fl (x,y) = (ct 1; !self_glob)

(* real *)
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

val zero = ([0.0], 1)
val one = ([1.0], 1)
val half = ([0.5], 1)
fun zerof fl (x,y) = (ct 1; zero)
fun onef fl (x,y) = (ct 1; one)
fun halff fl (x,y) = (ct 1; half)
fun randf fl (x,y) = (ct 40; sing (random_real ()))
fun add x1 x2 = x1 + (x2 : real)
fun addf fl = binf 1 add fl
fun diff x1 x2  = x1 - (x2 : real)
fun difff fl = binf 1 diff fl
fun mult x1 x2  = x1 * (x2 : real)
fun multf fl = binf 1 mult fl

(* list *)
fun nullf fl (x,y) = (ct 1; empty)

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

fun interleave_aux1 l1 l2 = case (l1,l2) of
    ([],_) => l2
  | (_,[]) => l1
  | (a1 :: m1, a2 :: m2) => a1 :: a2 :: interleave_aux1 m1 m2

fun interleave_aux2 (l1,n1) (l2,n2) = 
  if n1 + n2 > !timelimit then raise Check else (interleave_aux1 l1 l2, n1+n2)
  
fun interleave fl = case fl of
   [f1,f2] => (fn xy => 
     let val ((l1,n1),(l2,n2)) = (f1 xy, f2 xy) in 
       (ct (n1+n2+1); interleave_aux2 (l1,n1) (l2,n2))
     end)
  | _ => raise Msg "push"

(* control flow *)
fun xvar fl (x,y) = (ct 1; x)
fun yvar fl (x,y) = (ct 1; y)

fun while3_aux f x y = 
   (
   ct 1;
   case x of ([],_) => y | (a :: m,n) => while3_aux f (m,n-1) (f (x,y))
   )

fun while3 fl = case fl of
    [f1,f2,f3] => (fn xy => (ct 1; while3_aux f1 (f2 xy) (f3 xy)))
  | _ => raise Msg "while3"

fun cond fl = case fl of
    [f1,f2,f3] => (fn xy => 
    (
    ct 1; 
    case f1 xy of ([],_) => f2 xy | (x :: m,_) => 
      if x <= 0.0 then f3 xy else f2 xy
    )
    )
  | _ => raise Msg "cond"

(* --------------------------------------------------------------------------
   Primitives
   -------------------------------------------------------------------------- *)

exception Open;

val execl =
  [
  (* (taskf, "task", 0),
    (selff, "self", 0), *)
  (zerof,"zero",0), 
  (onef, "one", 0),
  (halff, "half",0), 
  (* (randf, "rand", 0),*)
  (addf, "add", 2),
  (difff, "diff", 2), 
  (multf, "mult", 2),
  (pop, "pop", 1), 
  (push, "push", 2), 
  (interleave, "inter", 2),
  (xvar, "x", 0),
  (yvar, "y", 0),
  (while3, "fold", 3),
  (cond, "cond", 3)
  ]

val execv = Vector.fromList execl
val execd = dnew String.compare (number_snd 0 (map #2 execl))

val _ = if Vector.length execv > 16
        then raise Msg "execv is too big" else ()

fun get_fun n = #1 (Vector.sub (execv,n))
fun get_name n = #2 (Vector.sub (execv,n))
fun get_arity n = #3 (Vector.sub (execv,n))

fun get_id s = dfind s execd handle NotFound => raise Msg ("get_id: " ^  s)


fun mk_exec (Ins (id,pl)) = (get_fun id) (map mk_exec pl)

(* --------------------------------------------------------------------------
   Converting between syntax tree and token list
   -------------------------------------------------------------------------- *)

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
 
 
fun bin_of_int n i = if n <= 0 then [] else
  Real.fromInt (i mod 2) :: bin_of_int (n-1) (i div 2)  
fun bin_of_prog p = List.concat (map (bin_of_int 4) (flatten_prog p)); 
 
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
fun randpmem () = (randprog (),empty)

(* --------------------------------------------------------------------------
   Writing/reading program
   -------------------------------------------------------------------------- *)

fun sexp_of_prog (Ins (n,pl)) = case pl of 
    [] => Atom (get_name n)
  | _ => Sexp (Atom (get_name n) :: map sexp_of_prog pl) 

val string_of_sexp = sexp_to_string
val string_of_prog = string_of_sexp o sexp_of_prog;

val pp = pe o string_of_prog;

fun prog_of_sexp sexp = case sexp of
    Atom s => Ins (get_id s,[])
  | Sexp (Atom s :: m) => Ins (get_id s, map prog_of_sexp m)  
  | _ => raise Msg "prog_of_sexp" 

val sexp_of_string = string_to_sexp
val prog_of_string = prog_of_sexp o sexp_of_string
  
(* --------------------------------------------------------------------------
   Generating a new program from an existing one
   -------------------------------------------------------------------------- *)

fun timedf f x = (timer := 0; (f x handle Check => empty));

fun next_mem mem hist (p,f) = timedf f (mem,hist)

fun rbit_of_mem (l,_) = 
  case l of [] => 0.5 | x :: _ => 
  if x > 1.0 then 1.0 else 
    if x < 0.0 then 0.0 else if Real.isFinite x then x else 0.5

fun next_rbit hist (pf,mem) =
  let 
    val newmem = next_mem mem hist pf 
    val rbit = rbit_of_mem newmem
  in
    (rbit, newmem)
  end
  handle Unordered => raise Msg "next_rbit"

(* --------------------------------------------------------------------------
   Scores
   -------------------------------------------------------------------------- *)

fun bit_of_mem (l,_) = case l of 
    [] => if random_real () > 0.5 then 1 else 0
  | x :: _ =>  if x > random_real () then 1 else 0


fun next_bit mem hist pf =
  let 
    val newmem = next_mem mem hist pf 
    val bit = bit_of_mem newmem
    val newhist = (Real.fromInt bit :: fst hist , snd hist + 1)  
  in
    ((bit, newmem),hist)
  end
  
fun next_token mem hist pf =
  let 
    val ((bit1,mem1),hist1) = next_bit mem hist pf 
    val ((bit2,mem2),hist2) = next_bit mem1 hist1 pf
    val ((bit3,mem3),hist3) = next_bit mem2 hist2 pf
    val ((bit4,mem4),hist4) = next_bit mem3 hist3 pf
    val id = bit1 * 8  + bit2 * 4 + bit3 * 2 + bit4
    val id' = if id < Vector.length execv then id else
              random_int (0, Vector.length execv -1)
  in
    ((id', mem4), hist4)
  end
  
fun next_prog_aux nmax npar acc mem hist pf = 
  if npar <= 0 then 
    if null acc then NONE else SOME (unflatten_prog (rev acc), empty)
  else if nmax <= 0 then NONE else
  let
    val ((id,newmem),newhist) = next_token mem hist pf
    val arity = get_arity id
    val newnpar = npar + arity - 1
    val newacc = id :: acc
  in
    next_prog_aux (nmax-1) newnpar newacc newmem newhist pf
  end
  
fun next_prog nmax mem pf = next_prog_aux nmax 1 [] mem pf 

(* --------------------------------------------------------------------------
   Scores
   -------------------------------------------------------------------------- *)

fun bti b = if b then 1 else 0

fun sample p = next_prog 40 empty empty (p,mk_exec p)

fun sample_pmem (p,mem) = 
  let val l =  bin_of_prog p in
    task_glob := zero;
    self_glob := (l, length l);
    (
    case next_prog 40 mem empty (p,mk_exec p) of 
        SOME x => x 
      | NONE => randpmem ()
    )
  end

fun sample_token (pf,mem) = 
  (
  task_glob := one; 
  self_glob := empty;
  fst (fst (next_token mem empty pf))
  )

(* --------------------------------------------------------------------------
   Reading some token prediction data
   most significant bits first in quartet.
   -------------------------------------------------------------------------- *)
  
fun split_pair c s = pair_of_list (String.tokens (fn x => x = c) s)
  handle HOL_ERR _ => raise Msg (Char.toString c ^ ": " ^ s)  
  
fun id_of_gpt s = 
  let val n = Char.ord (valOf (Char.fromString s)) in n - 65 end

fun tokenl_of_gpt s = 
  let val sl = String.tokens Char.isSpace s in map id_of_gpt sl end

fun read_line acc il = case il of [] => rev acc | i :: m => 
  read_line (bin_of_int 4 i @ acc) m

fun read_oeis () = 
  let
    val sl0 = readl (selfdir ^ "/../../oeis-synthesis/src/data/oeis_smallprog")
    val sl1 = map (snd o (split_pair #":")) sl0
    val sl2 = map tokenl_of_gpt sl1
  in
    map (read_line []) sl2
  end

(* --------------------------------------------------------------------------
   Scores
   -------------------------------------------------------------------------- *)
  

fun score_rbit (hist,obj) (pf,mem) = 
  let val (rbit: real,newmem) = next_rbit hist (pf,mem) in
    ((rbit - obj) * (rbit - obj), newmem)
  end
  
fun score_ex_aux scl hist ex (pf,mem) = case ex of 
    [] => average_real scl
  | obj :: newex => 
    let val (sc,newmem) = score_rbit (hist,obj) (pf,mem) in
      score_ex_aux (sc :: scl) (obj :: fst hist, snd hist + 1) newex (pf,newmem)
    end

fun score_ex ex pfm = score_ex_aux [] empty ex pfm

fun score_exl exl p = 
  let 
    val pfm = ((p, mk_exec p),empty) 
    val sc = average_real (map (fn x => score_ex x pfm) exl)
  in
    sc  
  end

(* --------------------------------------------------------------------------
   Randomly generating programs
   -------------------------------------------------------------------------- *)

fun randmem () = let val n = random_int (1,14) in
    (List.tabulate (n, fn _ => random_real ()), n)
  end;


fun randpfmem () = 
  let 
    val p = randprog ()
    val mem = randmem () 
    val f = mk_exec p
  in
    ((p,f),[])
  end;

fun loop (n,ntot,rt,to) acc genf scoref = 
  if (n >= ntot andalso not (isSome to)) orelse
     (n mod 100 = 0 andalso isSome to 
      andalso Time.toReal (Timer.checkRealTimer rt) > valOf to)
  then (n, first_n 1000 (dict_sort compare_rmin (fst (!acc))))
  else
  let
    val p = genf ()
    val sc = scoref p
    val _ = acc := ((p,sc) :: fst (!acc), snd (!acc) + 1)
    val _ = if snd (!acc) <= 10000 then () else
      let  
        val l = dict_sort compare_rmin (fst (!acc))
        val newacc = (first_n 1000 l, 1000)
        val (bp,bsc) = hd (fst newacc)
      in   
        (* pe (its n ^ " " ^ rts_round 4 bsc ^ " " ^ string_of_prog bp); *)
        acc := newacc
      end
  in
    loop (n+1,ntot,rt,to) acc genf scoref
  end;

fun loop2 (n,ntot,rt,to) genf scoref = loop (n,ntot,rt,to) (ref ([],0)) genf scoref ;


fun samplep pf = case next_prog 40 empty empty pf of NONE => randprog () 
                | SOME (p,mem) => p;

fun mk_gen p = 
  let val f = mk_exec p in
    (fn () => samplep (p,f))
  end

val exl =
   [[1.0, 0.0, 1.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0,
     1.0, 0.0, 0.0, 0.0, 1.0, 0.0, 1.0, 0.0, 0.0, 1.0, 1.0, 0.0, 1.0, 1.0,
     0.0, 1.0, 0.0, 1.0, 1.0, 0.0, 1.0, 0.0, 0.0, 0.0, 1.0, 1.0, 1.0, 0.0,
     1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 1.0, 0.0, 0.0, 1.0]]: real list list


val ptime = (stint (dfind "ptime" configd) handle NotFound => 10000)

fun score2f s = 
  let 
    val (s1,s2) = pair_of_list (String.tokens Char.isSpace s)
    val _ = timelimit := ptime
    val p = unzip_prog (stinf s1)
    val genf = mk_gen p
    val scoref = score_exl exl
    val rt = Timer.startRealTimer ()
    val ((n,r),t) = add_time (loop2 (0,0,rt,SOME (streal s2)) genf) scoref
    val sc = snd (hd r)
  in
    pe ("score: " ^ rts_round 4 sc ^ ", time: " ^ rts_round 2 t ^ 
        ", iterations: " ^ its n ^ ", prog: " ^ string_of_prog p);
    rts sc ^ " " ^ its n ^ " " ^ (infts o zip_prog) p
  end

fun stats sl2 = 
  let 
    fun f x = 
      let val (a,b,c) = triple_of_list (String.tokens Char.isSpace x) in
        (stinf c, streal a)
      end
    val rl = map f sl2;
    val (i,sc) = hd (dict_sort compare_rmin rl);
  in
    pe ("best score: " ^ rts_round 4 sc ^ 
        ", best prog: " ^ string_of_prog (unzip_prog i));
    sc
  end;

fun half_progl sl2 = 
  let 
    fun f x = 
      let val (a,b,c) = triple_of_list (String.tokens Char.isSpace x) in
        (stinf c, streal a)
      end
    val rl = map f sl2
  in
    map fst (first_n (length sl2 div 2) (dict_sort compare_rmin rl))
  end;

fun half_loop ncore n gtime scl pl = 
  if n <= 0 then (pl,rev scl) else
  let 
    val _ = pe (its (length pl) ^ " programs for " ^ 
                rts gtime ^ " seconds each")
    val inputl = map (fn x => infts x ^ " " ^ rts gtime) pl
    val (outputl,t) = add_time (parmap_sl ncore "selfedit2.score2f") inputl;
    val _ = pe ("time: " ^ rts_round 2 t)
    val sc = stats outputl
    val newpl = half_progl outputl
  in
    half_loop ncore (n-1) (gtime * 2.0) (sc :: scl) newpl
  end;

end (* struct *)

(*

load "selfedit2"; open kernel aiLib selfedit2;


val ncore = 10;
val ntarget = 100;
val gtime = 0.5;
val niter = 4;

val pl = List.tabulate (ntarget, fn _ => zip_prog (randprog ()));

val ((rl,scl),t1) = add_time (half_loop ncore 4 gtime []) pl; length rl;
val (i1,sc1) = hd (dict_sort compare_rmin (number_fst 1 scl));
val inputl = map (fn x => infts x ^ " " ^ rts (gtime * Real.fromInt niter)) pl;
val (outputl,t2) = add_time (parmap_sl ncore "selfedit2.score2f") inputl;
val sc2 = stats outputl;

val expname = "hello1"
val expdir = selfdir ^ "/exp/" ^ expname
val _ = mkDir_err expdir;

writel (expdir ^ "/result") 
["para:" ^ 
   " iter " ^ its niter ^ 
   ", time " ^ rts gtime ^ 
   ", targets " ^ its ntarget, 
 "",
 "comp:" ^ 
   " score " ^ rts_round 4 sc1 ^ 
   " at iteration " ^ its i1  ^ 
   " in " ^ rts_round 2 t1 ^ " seconds",
 "rand:" ^ 
   " score " ^ rts_round 4 sc2 ^ 
   " in " ^ rts_round 2 t2 ^ " seconds"];

*)

