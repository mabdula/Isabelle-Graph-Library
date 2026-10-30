structure Machine : sig
  val sub_nat : int * int -> int
  val div_nat : int * int -> int
  val mod_nat : int * int -> int
  val upd : int * 'a * 'a array -> 'a array
end = struct
  fun sub_nat (m, n) = if m < n then 0 else m - n
  fun div_nat (m, n) = if n = 0 then 0 else Int.quot (m, n)
  fun mod_nat (m, n) = if n = 0 then m else Int.rem (m, n)
  fun upd (i, x, a) = (Array.update (a, i, x); a)
end


structure DFS_Lists : sig
  type ('a, 'b, 'c) dFS_state_ext
  val dfs_input_arrays_run :
    Int.int array ->
      Int.int array ->
        Int.int ->
          Int.int -> (unit -> (Int.int, (bool array), unit) dFS_state_ext)
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = (fn a => fn b => ((a : Int.int) = b))} : Int.int equal;

datatype typerepa = Typerep of string * typerepa list;

datatype 'a itself = Type;

fun typerep_nata t = Typerep ("Nat.nat", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_nat = {} : Int.int countable;

val typerep_nat = {typerep = typerep_nata} : Int.int typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  Int.int heap;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_nat =
  {less_eq = (fn a => fn b => Int.<= (a, b)),
    less = (fn a => fn b => Int.< (a, b))}
  : Int.int ord;

fun typerep_boola t = Typerep ("HOL.bool", []);

val countable_bool = {} : bool countable;

val typerep_bool = {typerep = typerep_boola} : bool typerep;

val heap_bool = {countable_heap = countable_bool, typerep_heap = typerep_bool} :
  bool heap;

fun typerep_lista A_ t = Typerep ("List.list", [typerep A_ Type]);

fun countable_list A_ = {} : ('a list) countable;

fun typerep_list A_ = {typerep = typerep_lista A_} : ('a list) typerep;

fun heap_list A_ =
  {countable_heap = countable_list (countable_heap A_),
    typerep_heap = typerep_list (typerep_heap A_)}
  : ('a list) heap;

fun typerep_optiona A_ t = Typerep ("Option.option", [typerep A_ Type]);

fun countable_option A_ = {} : ('a option) countable;

fun typerep_option A_ = {typerep = typerep_optiona A_} : ('a option) typerep;

fun heap_option A_ =
  {countable_heap = countable_option (countable_heap A_),
    typerep_heap = typerep_option (typerep_heap A_)}
  : ('a option) heap;

datatype num = One | Bit0 of num | Bit1 of num;

datatype return = Reachable | NotReachable;

datatype ('a, 'b, 'c) dFS_state_ext =
  DFS_state_ext of 'a list * 'b * return * 'c;

fun eq A_ a b = equal A_ a b;

fun null [] = true
  | null (x :: xs) = false;

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun hd (x21 :: x22) = x21;

fun blit A_ uu uv uw ux l =
  (if ((l : Int.int) = (0 : Int.int)) then (fn () => ())
    else (fn () =>
           let
             val x = (fn () => Array.sub (uu, uv)) ();
             val _ = (fn () => Machine.upd (ux, x, uw)) ();
           in
             blit A_ uu (Int.+ (uv, (1 : Int.int))) uw
               (Int.+ (ux, (1 : Int.int))) (Machine.sub_nat (l, (1 : Int.int)))
               ()
           end));

fun the_default uu (SOME x) = x
  | the_default x NONE = x;

fun nth_oo A_ v a i =
  (fn () =>
    let
      val l = (fn () => Array.length a) ();
    in
      (if Int.< (i, l) then (fn () => Array.sub (a, i)) else (fn () => v)) ()
    end);

fun upd_oo A_ f i x a =
  (fn () =>
    let
      val l = (fn () => Array.length a) ();
    in
      (if Int.< (i, l) then (fn () => Machine.upd (i, x, a)) else f) ()
    end);

fun seen (DFS_state_ext (stack, seen, return, more)) = seen;

fun stack (DFS_state_ext (stack, seen, return, more)) = stack;

fun array_grow A_ a s x =
  (fn () =>
    let
      val l = (fn () => Array.length a) ();
    in
      (if ((l : Int.int) = s) then (fn () => a)
        else (fn f_ => fn () => f_ (((fn () => Array.array (s, x))) ()) ())
               (fn aa =>
                 (fn f_ => fn () => f_
                   ((blit A_ a (0 : Int.int) aa (0 : Int.int) l) ()) ())
                   (fn _ => (fn () => aa))))
        ()
    end);

val iam_initial_size : Int.int = (8 : Int.int);

fun iam_new_sz A_ sz = (fn () => Array.array (sz, NONE));

fun iam_new A_ = iam_new_sz A_ iam_initial_size;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun ias_ins k a =
  upd_oo heap_bool
    (fn () =>
      let
        val l = (fn () => Array.length a) ();
      in
        let
          val newsz =
            max ord_nat (Int.+ (k, (1 : Int.int)))
              (Int.+ (Int.* ((2 : Int.int), l), (3 : Int.int)));
        in
          (fn f_ => fn () => f_ ((array_grow heap_bool a newsz false) ()) ())
            (fn aa => (fn () => Machine.upd (k, true, aa)))
        end
          ()
      end)
    k true a;

val ias_initial_size : Int.int = (8 : Int.int);

fun ias_new_sz sz = (fn () => Array.array (sz, false));

val ias_new : (unit -> (bool array)) = ias_new_sz ias_initial_size;

fun ias_memb k a = nth_oo heap_bool false a k;

fun dls_insert A_ x xs = (if member A_ xs x then xs else x :: xs);

fun iam_lookup A_ k a = nth_oo (heap_option A_) NONE a k;

fun iam_update A_ k v a =
  upd_oo (heap_option A_)
    (fn () =>
      let
        val l = (fn () => Array.length a) ();
      in
        let
          val newsz =
            max ord_nat (Int.+ (k, (1 : Int.int)))
              (Int.+ (Int.* ((2 : Int.int), l), (3 : Int.int)));
        in
          (fn f_ => fn () => f_ ((array_grow (heap_option A_) a newsz NONE) ())
            ())
            (fn aa => (fn () => Machine.upd (k, SOME v, aa)))
        end
          ()
      end)
    k (SOME v) a;

fun seen_update seena (DFS_state_ext (stack, seen, return, more)) =
  DFS_state_ext (stack, seena seen, return, more);

fun stack_update stacka (DFS_state_ext (stack, seen, return, more)) =
  DFS_state_ext (stacka stack, seen, return, more);

fun return_update returna (DFS_state_ext (stack, seen, return, more)) =
  DFS_state_ext (stack, seen, returna return, more);

fun neighbourhood_impl_iam_lookup g v =
  (fn () => let
              val l = iam_lookup (heap_list heap_nat) v g ();
            in
              the_default [] l
            end);

fun dls_diff_imp_ias_memb (x :: xs) ias =
  (fn () => let
              val b = ias_memb x ias ();
              val xsa = dls_diff_imp_ias_memb xs ias ();
            in
              (if b then (fn () => xsa) else (fn () => (x :: xsa))) ()
            end)
  | dls_diff_imp_ias_memb [] ias = (fn () => []);

fun dFS_imperative_iam_lookup_ias_memb_ias_ins g t dfs_state =
  (case stack dfs_state
    of [] => (fn () => (return_update (fn _ => NotReachable) dfs_state))
    | v :: stack_tl =>
      (if ((v : Int.int) = t)
        then (fn () => (return_update (fn _ => Reachable) dfs_state))
        else (fn () =>
               let
                 val ns = neighbourhood_impl_iam_lookup g v ();
                 val nsa = dls_diff_imp_ias_memb ns (seen dfs_state) ();
               in
                 (if not (null nsa)
                   then let
                          val u = hd nsa;
                          val stacka = u :: stack dfs_state;
                        in
                          (fn f_ => fn () => f_ ((ias_ins u (seen dfs_state))
                            ()) ())
                            (fn seena =>
                              dFS_imperative_iam_lookup_ias_memb_ias_ins g t
                                (seen_update (fn _ => seena)
                                  (stack_update (fn _ => stacka) dfs_state)))
                        end
                   else dFS_imperative_iam_lookup_ias_memb_ias_ins g t
                          (stack_update (fn _ => stack_tl) dfs_state))
                   ()
               end)));

fun dFS_initial_state_impl_ias_new_ias_ins s =
  (fn () => let
              val seen = ias_new ();
              val seena = ias_ins s seen ();
            in
              DFS_state_ext ([s], seena, NotReachable, ())
            end);

fun dFS_imperative_iam_lookup_ias_new_ias_memb_ias_ins g s t =
  (fn () => let
              val x = dFS_initial_state_impl_ias_new_ias_ins s ();
            in
              dFS_imperative_iam_lookup_ias_memb_ias_ins g t x ()
            end);

fun add_edge_impl_iam_lookup_iam_update g u v =
  (fn () =>
    let
      val l = iam_lookup (heap_list heap_nat) u g ();
    in
      let
        val la = the_default [] l;
        val lb = dls_insert equal_nat v la;
      in
        (fn f_ => fn () => f_ ((iam_update (heap_list heap_nat) u lb g) ()) ())
          (fn a => (fn () => a))
      end
        ()
    end);

fun iterate_range_infoed A_ B_ arr info_arr start enda fi acc =
  (if Int.<= (start, enda)
    then (fn () =>
           let
             val current = (fn () => Array.sub (arr, start)) ();
             val current_info = (fn () => Array.sub (info_arr, start)) ();
             val x = fi current current_info acc ();
           in
             iterate_range_infoed A_ B_ arr info_arr
               (Int.+ (start, (1 : Int.int))) enda fi x ()
           end)
    else (fn () => acc));

val empty_graph_impl_iam_new : (unit -> (((Int.int list) option) array)) =
  iam_new (heap_list heap_nat);

fun from_arrays_impl_iam_new_iam_lookup_iam_update fa ta =
  (fn () =>
    let
      val l = (fn () => Array.length fa) ();
      val g = empty_graph_impl_iam_new ();
    in
      (if ((l : Int.int) = (0 : Int.int)) then (fn () => g)
        else iterate_range_infoed heap_nat heap_nat fa ta (0 : Int.int)
               (Machine.sub_nat (l, (1 : Int.int)))
               (fn u => fn v => fn ga =>
                 add_edge_impl_iam_lookup_iam_update ga u v)
               g)
        ()
    end);

fun dfs_input_arrays_run fa ta s t =
  (fn () => let
              val g = from_arrays_impl_iam_new_iam_lookup_iam_update fa ta ();
            in
              dFS_imperative_iam_lookup_ias_new_ias_memb_ias_ins g s t ()
            end);

end; (*struct DFS_Lists*)
