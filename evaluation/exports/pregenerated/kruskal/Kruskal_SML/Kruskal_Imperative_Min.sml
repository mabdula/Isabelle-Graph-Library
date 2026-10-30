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


structure Kruskal_Imp_Min : sig
  type rat
  val rat_of_int : Int.int -> rat
  val kruskal_imp_min :
    rat array ->
      (Int.int * Int.int) array ->
        Int.int array -> Int.int -> (unit -> (Int.int list))
end = struct

datatype typerepa = Typerep of string * typerepa list;

datatype 'a itself = Type;

fun typerep_inta t = Typerep ("Int.int", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_int = {} : Int.int countable;

val typerep_int = {typerep = typerep_inta} : Int.int typerep;

val heap_int = {countable_heap = countable_int, typerep_heap = typerep_int} :
  Int.int heap;

fun typerep_nata t = Typerep ("Nat.nat", []);

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

datatype rat = Frct of (Int.int * Int.int);

fun typerep_rata t = Typerep ("Rat.rat", []);

val countable_rat = {} : rat countable;

val typerep_rat = {typerep = typerep_rata} : rat typerep;

val heap_rat = {countable_heap = countable_rat, typerep_heap = typerep_rat} :
  rat heap;

fun quotient_of (Frct x) = x;

fun less_eq_rat p q = let
                        val (a, c) = quotient_of p;
                        val (b, d) = quotient_of q;
                      in
                        Int.<= (Int.* (a, d), Int.* (c, b))
                      end;

fun less_rat p q = let
                     val (a, c) = quotient_of p;
                     val (b, d) = quotient_of q;
                   in
                     Int.< (Int.* (a, d), Int.* (c, b))
                   end;

val ord_rat = {less_eq = less_eq_rat, less = less_rat} : rat ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_rat = {ord_preorder = ord_rat} : rat preorder;

val order_rat = {preorder_order = preorder_rat} : rat order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_rat = {order_linorder = order_rat} : rat linorder;

fun typerep_proda A_ B_ t =
  Typerep ("Product_Type.prod", [typerep A_ Type, typerep B_ Type]);

fun countable_prod A_ B_ = {} : ('a * 'b) countable;

fun typerep_prod A_ B_ = {typerep = typerep_proda A_ B_} : ('a * 'b) typerep;

fun heap_prod A_ B_ =
  {countable_heap = countable_prod (countable_heap A_) (countable_heap B_),
    typerep_heap = typerep_prod (typerep_heap A_) (typerep_heap B_)}
  : ('a * 'b) heap;

datatype ('a, 'b, 'c) kruskal_state_imp_ext =
  Kruskal_state_imp_ext of 'a array * Int.int * 'a list * 'b * 'c;

fun upt i j =
  (if Int.< (i, j) then i :: upt (Int.+ (i, (1 : Int.int))) j else []);

fun of_int a = Frct (a, (1 : Int.int));

fun fold_map f [] = (fn () => [])
  | fold_map f (x :: xs) = (fn () => let
                                       val y = f x ();
                                       val ys = fold_map f xs ();
                                     in
                                       y :: ys
                                     end);

fun freeze A_ a =
  (fn () =>
    let
      val n = (fn () => Array.length a) ();
    in
      fold_map (fn b => (fn () => Array.sub (a, b))) (upt (0 : Int.int) n) ()
    end);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

fun uminus_rat p = Frct let
                          val (a, b) = quotient_of p;
                        in
                          (Int.~ a, b)
                        end;

fun swap_i A_ a i j = (fn () => let
                                  val x = (fn () => Array.sub (a, i)) ();
                                  val y = (fn () => Array.sub (a, j)) ();
                                  val _ = (fn () => Machine.upd (i, y, a)) ();
                                  val _ = (fn () => Machine.upd (j, x, a)) ();
                                in
                                  ()
                                end);

fun less_eq_prod A_ B_ (x1, y1) (x2, y2) =
  less A_ x1 x2 orelse less_eq A_ x1 x2 andalso less_eq B_ y1 y2;

fun part1_i (A1_, A2_) k a l r p =
  (if Int.<= (r, l) then (fn () => r)
    else (fn () =>
           let
             val v = (fn () => Array.sub (a, l)) ();
             val kv = (fn () => Array.sub (k, v)) ();
           in
             (if less_eq_prod
                   ((ord_preorder o preorder_order o order_linorder) A2_)
                   ord_nat p (kv, v)
               then part1_i (A1_, A2_) k a (Int.+ (l, (1 : Int.int))) r p
               else (fn f_ => fn () => f_ ((swap_i heap_nat a l r) ()) ())
                      (fn _ =>
                        part1_i (A1_, A2_) k a l
                          (Machine.sub_nat (r, (1 : Int.int))) p))
               ()
           end));

fun rat_of_int k = of_int k;

fun result_list
  (Kruskal_state_imp_ext (edge_array, edge_ptr, result_list, uf_impl, more)) =
  result_list;

fun result_list_update result_lista
  (Kruskal_state_imp_ext (edge_array, edge_ptr, result_list, uf_impl, more)) =
  Kruskal_state_imp_ext
    (edge_array, edge_ptr, result_lista result_list, uf_impl, more);

fun ufsi_imp_parent_of ufsi_imp i =
  (fn () =>
    let
      val n = (fn () => Array.sub (ufsi_imp, i)) ();
    in
      (if Int.< (n, (0 : Int.int)) then i else Int.max ((0 : Int.int), n))
    end);

fun ufsi_imp_compress ufsi_imp i rep_i =
  (if ((rep_i : Int.int) = i) then (fn () => ufsi_imp)
    else (fn () => Machine.upd (i, rep_i, ufsi_imp)));

fun ufsi_imp_rep_of_c ufsi_imp i =
  (fn () =>
    let
      val pi = ufsi_imp_parent_of ufsi_imp i ();
    in
      (if ((pi : Int.int) = i) then (fn () => i)
        else (fn f_ => fn () => f_ ((ufsi_imp_rep_of_c ufsi_imp pi) ()) ())
               (fn rep_i =>
                 (fn f_ => fn () => f_ ((ufsi_imp_compress ufsi_imp i rep_i) ())
                   ())
                   (fn _ => (fn () => rep_i))))
        ()
    end);

fun ufsi_imp_size ufsi_imp x =
  (fn () =>
    let
      val sz = (fn () => Array.sub (ufsi_imp, x)) ();
    in
      (if Int.< (sz, (0 : Int.int))
        then (fn () => (Int.max ((0 : Int.int), Int.~ sz)))
        else (fn () => (0 : Int.int)))
        ()
    end);

fun ufsi_imp_link ufsi_imp rep_x rep_y sz =
  (fn () => let
              val _ = (fn () => Machine.upd (rep_x, rep_y, ufsi_imp)) ();
            in
              (fn () => Machine.upd (rep_y, Int.~ sz, ufsi_imp)) ()
            end);

fun ufsi_imp_union_size_c ufsi_imp x y =
  (fn () =>
    let
      val rep_x = ufsi_imp_rep_of_c ufsi_imp x ();
      val rep_y = ufsi_imp_rep_of_c ufsi_imp y ();
    in
      (if ((rep_x : Int.int) = rep_y) then (fn () => ufsi_imp)
        else (fn f_ => fn () => f_ ((ufsi_imp_size ufsi_imp rep_x) ()) ())
               (fn sz_rep_x =>
                 (fn f_ => fn () => f_ ((ufsi_imp_size ufsi_imp rep_y) ()) ())
                   (fn sz_rep_y =>
                     (if Int.< (sz_rep_x, sz_rep_y)
                       then ufsi_imp_link ufsi_imp rep_x rep_y
                              (Int.+ (sz_rep_x, sz_rep_y))
                       else ufsi_imp_link ufsi_imp rep_y rep_x
                              (Int.+ (sz_rep_y, sz_rep_x))))))
        ()
    end);

fun edge_ptr_update edge_ptra
  (Kruskal_state_imp_ext (edge_array, edge_ptr, result_list, uf_impl, more)) =
  Kruskal_state_imp_ext
    (edge_array, edge_ptra edge_ptr, result_list, uf_impl, more);

fun uf_impl_update uf_impla
  (Kruskal_state_imp_ext (edge_array, edge_ptr, result_list, uf_impl, more)) =
  Kruskal_state_imp_ext
    (edge_array, edge_ptr, result_list, uf_impla uf_impl, more);

fun edge_array
  (Kruskal_state_imp_ext (edge_array, edge_ptr, result_list, uf_impl, more)) =
  edge_array;

fun edge_ptr
  (Kruskal_state_imp_ext (edge_array, edge_ptr, result_list, uf_impl, more)) =
  edge_ptr;

fun uf_impl
  (Kruskal_state_imp_ext (edge_array, edge_ptr, result_list, uf_impl, more)) =
  uf_impl;

fun ufsi_imp_same_set ufsi_imp x y =
  (fn () => let
              val rep_x = ufsi_imp_rep_of_c ufsi_imp x ();
              val rep_y = ufsi_imp_rep_of_c ufsi_imp y ();
            in
              ((rep_x : Int.int) = rep_y)
            end);

fun kruskal_imp_loop eps state =
  (fn () =>
    let
      val len = (fn () => Array.length (edge_array state)) ();
    in
      (if Int.< (edge_ptr state, len)
        then (fn f_ => fn () => f_
               (((fn () => Array.sub (edge_array state, edge_ptr state))) ())
               ())
               (fn e =>
                 (fn f_ => fn () => f_ (((fn () => Array.sub (eps, e))) ()) ())
                   (fn uv =>
                     (fn f_ => fn () => f_
                       ((ufsi_imp_same_set (uf_impl state) (fst uv) (snd uv))
                       ()) ())
                       (fn b =>
                         (if not b
                           then (fn f_ => fn () => f_
                                  ((ufsi_imp_union_size_c (uf_impl state)
                                     (fst uv) (snd uv))
                                  ()) ())
                                  (fn uf =>
                                    kruskal_imp_loop eps
                                      (uf_impl_update (fn _ => uf)
(result_list_update (fn _ => e :: result_list state)
  (edge_ptr_update (fn _ => Int.+ (edge_ptr state, (1 : Int.int))) state))))
                           else kruskal_imp_loop eps
                                  (edge_ptr_update
                                    (fn _ =>
                                      Int.+ (edge_ptr state, (1 : Int.int)))
                                    state)))))
        else (fn () => state))
        ()
    end);

fun ufsi_imp_init n = (fn () => Array.array (n, Int.~ (1 : Int.int)));

fun partition_i (A1_, A2_) k a l r =
  (fn () =>
    let
      val pv = (fn () => Array.sub (a, r)) ();
      val kp = (fn () => Array.sub (k, pv)) ();
      val m =
        part1_i (A1_, A2_) k a l (Machine.sub_nat (r, (1 : Int.int))) (kp, pv)
          ();
      val v = (fn () => Array.sub (a, m)) ();
      val kv = (fn () => Array.sub (k, v)) ();
    in
      let
        val ma =
          (if less_eq_prod
                ((ord_preorder o preorder_order o order_linorder) A2_) ord_nat
                (kp, pv) (kv, v)
            then Int.+ (m, (1 : Int.int)) else m);
      in
        (fn f_ => fn () => f_ ((swap_i heap_nat a ma r) ()) ())
          (fn _ => (fn () => ma))
      end
        ()
    end);

fun quicksort_i (A1_, A2_) k a l r =
  (if Int.< (l, r)
    then (fn () =>
           let
             val m = partition_i (A1_, A2_) k a l r ();
             val _ =
               quicksort_i (A1_, A2_) k a l (Machine.sub_nat (m, (1 : Int.int)))
                 ();
           in
             quicksort_i (A1_, A2_) k a (Int.+ (m, (1 : Int.int))) r ()
           end)
    else (fn () => ()));

fun qsort_desc (A1_, A2_) k a =
  (fn () =>
    let
      val n = (fn () => Array.length a) ();
      val _ =
        quicksort_i (A1_, A2_) k a (0 : Int.int)
          (Machine.sub_nat (n, (1 : Int.int))) ();
    in
      a
    end);

fun kruskal_imp_init costs edges n =
  (fn () =>
    let
      val edge_array = qsort_desc (heap_rat, linorder_rat) costs edges ();
      val uf = ufsi_imp_init n ();
    in
      Kruskal_state_imp_ext (edge_array, (0 : Int.int), [], uf, ())
    end);

fun kruskal_imp costs eps edges n =
  (fn () => let
              val state = kruskal_imp_init costs edges n ();
              val statea = kruskal_imp_loop eps state ();
            in
              result_list statea
            end);

fun kruskal_imp_min costs eps edges n =
  (fn () =>
    let
      val cs = freeze heap_rat costs ();
      val neg_costs = (fn () => Array.fromList (map uminus_rat cs)) ();
    in
      kruskal_imp neg_costs eps edges n ()
    end);

end; (*struct Kruskal_Imp_Min*)
