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
val timelimit = ref 40000;
fun ct n = 
  (timer := !timer + n; if !timer > !timelimit then raise Check else ())

(* --------------------------------------------------------------------------
   Primitives
   -------------------------------------------------------------------------- *)

val dim = 16

(* nullary *)
val mat0 = let fun f i j = 0.0 in mat_tabulate f (dim,dim) end
val mat1 = let fun f i j = 1.0 in mat_tabulate f (dim,dim) end

fun mati_aux itop = 
  let fun f i j =  if i = itop andalso j = 0 then 1.0 else 0.0 in 
    mat_tabulate f (dim,dim)
  end

val mativ = Vector.tabulate (dim, fn i => mati_aux i)
fun sing m = ([m],1)
  
fun matrand () = 
  let 
    val coeff = (int_div 1 dim)
    fun f i j =  coeff * random_real () - 0.5 * coeff 
  in 
    mat_tabulate f (dim,dim) 
  end

fun xvar fl (x,y) = (ct 1; x)
fun tokf n fl (x,y) = (ct 1; sing (Vector.sub (mativ, n)))

fun yvar fl (x,y) = (ct 1; y)
val empty = ([] : mat list ,0)
fun nullf fl (x,y) = (ct 1; empty)
fun randf fl (x,y) = (ct 40; sing (matrand ()))

val task_glob = ref empty
fun taskf fl (x,y) = (ct 1; !task_glob)


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

fun up m = let fun f x = x * 2.0 in mat_map f m end
fun down m = let fun f x = x * 0.1 in mat_map f m end

fun upf fl = unf up fl
fun downf fl = unf down fl

fun flip m = let fun f x = ~x in mat_map f m end
fun flipf fl = unf flip fl

fun transposef fl = unf mat_transpose fl

fun mat_permute m = 
  let 
    val (dim1,dim2) = mat_dim m 
    fun f i j = mat_sub m ((i-1) mod dim1) j
  in
    mat_tabulate f (dim1,dim2)
  end

fun permutef fl = unf mat_permute fl

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


fun mat_add m1 m2 =
  let fun f i j = mat_sub m1 i j + (mat_sub m2 i j: real) in
    mat_tabulate f (mat_dim m1)
  end
  
fun addf fl = binf 1 mat_add fl

fun mat_hadam m1 m2 =
  let fun f i j = mat_sub m1 i j * (mat_sub m2 i j: real) in
    mat_tabulate f (mat_dim m1)
  end
  
fun hadamf fl = binf 1 mat_hadam fl

fun mat_mult m1 m2 = 
  let 
    val m2t = mat_transpose m2
    fun f i j = scalar_product (Vector.sub (m1,i)) (Vector.sub(m2t,j))
  in
    mat_tabulate f (dim,dim)
  end

fun multf fl = binf dim mat_mult fl

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

val execl1 =
  [
  (xvar,"x",0), 
  (yvar, "y", 0),
  (nullf, "null",0), 
  (randf, "rand", 0),
  (taskf, "task", 0),
  (reluf, "relu", 1), 
  (* (upf, "up",1), *)
  (downf, "down", 1),
  (* (flipf, "flip", 1), *)
  (transposef, "transpose", 1),
  (permutef, "permute", 1),
  (addf, "add", 2), 
  (multf, "mult", 2),
  (hadamf, "hadam", 2), 
  (pop, "pop", 1), 
  (push, "push", 2), 
  (interleave, "inter", 2),
  (while3, "fold", 3)
  ]
  
val execl2 = 
  let fun f i (a,b,c) = [(a,b,c), (tokf (2 * i), "#" ^ b, 0)] in
    List.concat (mapi f execl1)
  end
 
val execv = Vector.fromList execl1

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


fun mk_exec (Ins (id,pl)) = (get_fun id) (map mk_exec pl)


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
fun randpmem () = (randprog (),empty)

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
      fun f x = if not (Real.isFinite x) then x else 
                if x > 1.0 then 1.0 else 
                if x < 0.0 then 0.0 else x
                
                (* Math.exp x   else 0.0 *)
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
    if null acc then NONE else SOME (unflatten_prog (rev acc), mem)
  else if nmax <= 0 then NONE else
  let
    val (id,newmem) = next_token mem hist pf
    val newhist = (mati_aux id :: fst hist, snd hist + 1)
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
  (
  task_glob := ([mat0],1);
  next_prog 40 mem empty (p,mk_exec p)
  )

fun sample_token pf = 
  (
  task_glob := ([mat1],1); 
  fst (next_token empty empty pf)
  )

fun score_aux nremain ncorrect pf = 
  if nremain <= 0 then ncorrect else 
  score_aux (nremain - 1) (ncorrect + bti (sample_token pf = 0)) pf

fun score (p,mem) = Real.fromInt (score_aux 100 0 (p,mk_exec p))

(* --------------------------------------------------------------------------
   MCTS (rewarding parent programs for their children)
   -------------------------------------------------------------------------- *)


type node =
{
  state    : prog * obj,
  parent   : int option,
  children : int list ref,
  visits   : real ref,
  sum      : real ref
}

val fake_prog = Ins (~1,[])

val fake_node = 
  {
  state = (fake_prog, empty), 
  parent = NONE, 
  children = ref [], 
  visits = ref 1.0, 
  sum = ref 0.0
  }
  
val myarr = Array.array (20000,fake_node)
val indexl = List.tabulate (Array.length myarr, I)
fun init_myarr () = app (fn i => Array.update (myarr,i,fake_node)) indexl


(* selection *)
val sqrt2 = Math.sqrt 2.0

fun uct pvis id =
   let val {visits,sum,...} = Array.sub (myarr,id) in
     (!sum) / (!visits) + sqrt2 * Math.sqrt (Math.ln pvis / (!visits))
   end

fun best_child pvis idl =
  let val l = map_assoc (uct pvis) idl in
    fst (hd (dict_sort compare_rmax l))
  end

fun select id = 
  let
    (* val _ = pe ("select " ^ its id) *)
    val {children,visits,...} = Array.sub (myarr,id)
    val cl = !children
  in 
    if null cl orelse Real.fromInt (length cl) < 2.0 * (Math.pow (!visits,0.5)) 
    then id
    else select (best_child (!visits) cl)
  end

(* expansion *)
val idl_glob = ref [] 
fun init_idl () = idl_glob := tl indexl
fun free_id () = 
   if null (!idl_glob) then raise Msg "no more free id" else
   let val id = hd (!idl_glob) in idl_glob := tl (!idl_glob); id end
    
fun expand id = 
  let  
    val {state,children,...} = Array.sub (myarr,id)
    val ind = case sample_pmem state of SOME x => x | NONE => randpmem ()
    val cid = free_id ()
    (* val _ = pe ("expand " ^ its cid) *)
    val cnode = 
      {
      state = ind,
      parent = SOME id,
      children = ref [],
      visits = ref 0.0,
      sum = ref 0.0
      }
  in
    children := cid :: !children;
    Array.update (myarr, cid, cnode);
    cid
  end

(* backup *)
fun backup sc id =
  let 
    (* val _ = pe ("backup " ^ its self) *)
    val {parent,visits,sum,...} = Array.sub (myarr,id)
    val _ = visits := (!visits) + 1.0
    val _ = sum := (!sum) + sc
  in
    case parent of 
      NONE => () 
    | SOME pid => backup sc pid
  end

fun backup_score id = backup (score (#state (Array.sub (myarr,id)))) id

(* --------------------------------------------------------------------------
   Population evolution with MCTS local search
   -------------------------------------------------------------------------- *)

fun pstats id = 
  let val {visits,sum,state,...} : node = Array.sub (myarr,id) in
    pe (
    its id ^ ": " ^ 
    its (Real.round (!visits)) ^ " " ^ pretty_real (!sum / !visits) ^
    " " ^ string_of_prog (fst state)
    )
  end;

fun get_visits id = ! (#visits (Array.sub (myarr,id)))
fun get_mean id = 
  let val {visits,sum,...} : node = Array.sub (myarr,id) in
    !sum / !visits
  end;

fun children_stats () = 
  let 
    val {visits,children,...} : node = Array.sub (myarr,0)
     val vis = Real.round (!visits)
  in 
    if vis mod 1000 <> 0 orelse null (!children) then () else
    let
      val id1 = (fst o hd) 
        (dict_sort compare_rmax (map_assoc get_visits (!children))) 
      val id2 = (fst o hd) 
        (dict_sort compare_rmax (map_assoc get_mean (!children))) 
    in
      (
      pe ("visits " ^ its vis ^ ", children " ^ its (length (!children)));
      pstats id1; pstats id2
      )
    end
  end;

fun loop () = 
  if null (!idl_glob) then () else 
  let 
    val _ = children_stats ()
    val sid = select 0 
    val cid = expand sid
    val _ = backup_score cid 
  in
    loop ()
  end;

fun init_root state =
  let val root = 
    {state = state, parent = NONE, children = ref [], 
     visits = ref 1.0, sum = ref 0.0} 
  in
    init_idl (); init_myarr (); Array.update (myarr, 0, root)
  end;
  

 
fun best_state () = 
  let 
    val {children,...} : node = Array.sub (myarr,0)
    val id = (fst o hd) 
        (dict_sort compare_rmax (map_assoc get_visits (!children)))
    val state = #state (Array.sub (myarr,id))
    val d = ref (eempty prog_compare)
    fun f (x : node) = d := eadd (fst (#state x)) (!d);
    val _ = Array.app f myarr;
    val n = elength (!d);
    in
      pe ("#### Selected " ^ its id ^ " ####");
      pe (its n ^ " different programs");
      pstats id; 
      state
  end;

fun looptop state = (init_root state; loop (); looptop (best_state ()));


(*
load "selfedit";
timelimit := 10000; 

val init_state = (Ins (3,[]), empty);
looptop init_state;

init_root init_state; loop ();




*)

