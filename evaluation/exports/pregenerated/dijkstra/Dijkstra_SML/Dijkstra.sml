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


structure Dijkstra : sig
  type ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k) dij_impl_state_ext
  val dijkstra_sp_query_int :
    ((Int.int array), (bool array), ((Int.int option) array),
      (Int.int array * (Int.int array * (Int.int array * Int.int ref))),
      (Int.int array * (Int.int array * Int.int array)),
      (Int.int array * Int.int ref), (Int.int array),
      (Int.int array * Int.int array), (bool array),
      (Int.int -> Int.int -> Int.int -> Int.int -> (unit -> bool)), unit)
      dij_impl_state_ext *
      Int.int array ->
      Int.int -> (unit -> ((Int.int array) option))
  val dijkstra_sp_compute_int :
    Int.int ->
      Int.int array ->
        Int.int array ->
          Int.int array ->
            Int.int array ->
              (unit ->
                (((Int.int array), (bool array), ((Int.int option) array),
                   (Int.int array *
                     (Int.int array * (Int.int array * Int.int ref))),
                   (Int.int array * (Int.int array * Int.int array)),
                   (Int.int array * Int.int ref), (Int.int array),
                   (Int.int array * Int.int array), (bool array),
                   (Int.int -> Int.int -> Int.int -> Int.int -> (unit -> bool)),
                   unit)
                   dij_impl_state_ext *
                  Int.int array))
  val dijkstra_shortest_path_int :
    Int.int ->
      Int.int array ->
        Int.int array ->
          Int.int array ->
            Int.int array -> Int.int array -> (unit -> ((Int.int array) option))
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_int = {equal = (fn a => fn b => ((a : Int.int) = b))} : Int.int equal;

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

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_int = {plus = (fn a => fn b => Int.+ (a, b))} : Int.int plus;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_int = {zero = (0 : Int.int)} : Int.int zero;

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

val minus_int = {minus = (fn a => fn b => Int.- (a, b))} : Int.int minus;

type 'a uminus = {uminus : 'a -> 'a};
val uminus = #uminus : 'a uminus -> 'a -> 'a;

val uminus_int = {uminus = Int.~} : Int.int uminus;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

val ord_int =
  {less_eq = (fn a => fn b => Int.<= (a, b)),
    less = (fn a => fn b => Int.< (a, b))}
  : Int.int ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_int = {ord_preorder = ord_int} : Int.int preorder;

val order_int = {preorder_order = preorder_int} : Int.int order;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add :
  'a cancel_semigroup_add -> 'a semigroup_add;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a group_add =
  {cancel_semigroup_add_group_add : 'a cancel_semigroup_add,
    minus_group_add : 'a minus, monoid_add_group_add : 'a monoid_add,
    uminus_group_add : 'a uminus};
val cancel_semigroup_add_group_add = #cancel_semigroup_add_group_add :
  'a group_add -> 'a cancel_semigroup_add;
val minus_group_add = #minus_group_add : 'a group_add -> 'a minus;
val monoid_add_group_add = #monoid_add_group_add :
  'a group_add -> 'a monoid_add;
val uminus_group_add = #uminus_group_add : 'a group_add -> 'a uminus;

val semigroup_add_int = {plus_semigroup_add = plus_int} : Int.int semigroup_add;

val cancel_semigroup_add_int =
  {semigroup_add_cancel_semigroup_add = semigroup_add_int} :
  Int.int cancel_semigroup_add;

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} :
  Int.int monoid_add;

val group_add_int =
  {cancel_semigroup_add_group_add = cancel_semigroup_add_int,
    minus_group_add = minus_int, monoid_add_group_add = monoid_add_int,
    uminus_group_add = uminus_int}
  : Int.int group_add;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_int = {order_linorder = order_int} : Int.int linorder;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a cancel_ab_semigroup_add =
  {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add,
    cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add,
    minus_cancel_ab_semigroup_add : 'a minus};
val ab_semigroup_add_cancel_ab_semigroup_add =
  #ab_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a ab_semigroup_add;
val cancel_semigroup_add_cancel_ab_semigroup_add =
  #cancel_semigroup_add_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a cancel_semigroup_add;
val minus_cancel_ab_semigroup_add = #minus_cancel_ab_semigroup_add :
  'a cancel_ab_semigroup_add -> 'a minus;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a cancel_comm_monoid_add =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add,
    comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};
val cancel_ab_semigroup_add_cancel_comm_monoid_add =
  #cancel_ab_semigroup_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a cancel_ab_semigroup_add;
val comm_monoid_add_cancel_comm_monoid_add =
  #comm_monoid_add_cancel_comm_monoid_add :
  'a cancel_comm_monoid_add -> 'a comm_monoid_add;

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add,
    group_add_ab_group_add : 'a group_add};
val cancel_comm_monoid_add_ab_group_add = #cancel_comm_monoid_add_ab_group_add :
  'a ab_group_add -> 'a cancel_comm_monoid_add;
val group_add_ab_group_add = #group_add_ab_group_add :
  'a ab_group_add -> 'a group_add;

val ab_semigroup_add_int = {semigroup_add_ab_semigroup_add = semigroup_add_int}
  : Int.int ab_semigroup_add;

val cancel_ab_semigroup_add_int =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int,
    minus_cancel_ab_semigroup_add = minus_int}
  : Int.int cancel_ab_semigroup_add;

val comm_monoid_add_int =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int,
    monoid_add_comm_monoid_add = monoid_add_int}
  : Int.int comm_monoid_add;

val cancel_comm_monoid_add_int =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_int,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
  : Int.int cancel_comm_monoid_add;

val ab_group_add_int =
  {cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int,
    group_add_ab_group_add = group_add_int}
  : Int.int ab_group_add;

type 'a ordered_ab_semigroup_add =
  {ab_semigroup_add_ordered_ab_semigroup_add : 'a ab_semigroup_add,
    order_ordered_ab_semigroup_add : 'a order};
val ab_semigroup_add_ordered_ab_semigroup_add =
  #ab_semigroup_add_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a ab_semigroup_add;
val order_ordered_ab_semigroup_add = #order_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a order;

type 'a strict_ordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add};
val ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add =
  #ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add :
  'a strict_ordered_ab_semigroup_add -> 'a ordered_ab_semigroup_add;

type 'a ordered_cancel_ab_semigroup_add =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
     'a cancel_ab_semigroup_add,
    strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
      'a strict_ordered_ab_semigroup_add};
val cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
  #cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
  'a ordered_cancel_ab_semigroup_add -> 'a cancel_ab_semigroup_add;
val strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
  #strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add :
  'a ordered_cancel_ab_semigroup_add -> 'a strict_ordered_ab_semigroup_add;

type 'a ordered_ab_semigroup_add_imp_le =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le :
     'a ordered_cancel_ab_semigroup_add};
val ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
  #ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le :
  'a ordered_ab_semigroup_add_imp_le -> 'a ordered_cancel_ab_semigroup_add;

type 'a strict_ordered_comm_monoid_add =
  {comm_monoid_add_strict_ordered_comm_monoid_add : 'a comm_monoid_add,
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add :
      'a strict_ordered_ab_semigroup_add};
val comm_monoid_add_strict_ordered_comm_monoid_add =
  #comm_monoid_add_strict_ordered_comm_monoid_add :
  'a strict_ordered_comm_monoid_add -> 'a comm_monoid_add;
val strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
  #strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add :
  'a strict_ordered_comm_monoid_add -> 'a strict_ordered_ab_semigroup_add;

type 'a ordered_comm_monoid_add =
  {comm_monoid_add_ordered_comm_monoid_add : 'a comm_monoid_add,
    ordered_ab_semigroup_add_ordered_comm_monoid_add :
      'a ordered_ab_semigroup_add};
val comm_monoid_add_ordered_comm_monoid_add =
  #comm_monoid_add_ordered_comm_monoid_add :
  'a ordered_comm_monoid_add -> 'a comm_monoid_add;
val ordered_ab_semigroup_add_ordered_comm_monoid_add =
  #ordered_ab_semigroup_add_ordered_comm_monoid_add :
  'a ordered_comm_monoid_add -> 'a ordered_ab_semigroup_add;

type 'a ordered_cancel_comm_monoid_add =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add :
     'a ordered_cancel_ab_semigroup_add,
    ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
      'a ordered_comm_monoid_add,
    strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
      'a strict_ordered_comm_monoid_add};
val ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add =
  #ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a ordered_cancel_ab_semigroup_add;
val ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
  #ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a ordered_comm_monoid_add;
val strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
  #strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add :
  'a ordered_cancel_comm_monoid_add -> 'a strict_ordered_comm_monoid_add;

type 'a ordered_ab_semigroup_monoid_add_imp_le =
  {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
     'a cancel_comm_monoid_add,
    ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le :
      'a ordered_ab_semigroup_add_imp_le,
    ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
      'a ordered_cancel_comm_monoid_add};
val cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
  #cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le -> 'a cancel_comm_monoid_add;
val ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le =
  #ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le ->
    'a ordered_ab_semigroup_add_imp_le;
val ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
  #ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le :
  'a ordered_ab_semigroup_monoid_add_imp_le ->
    'a ordered_cancel_comm_monoid_add;

type 'a ordered_ab_group_add =
  {ab_group_add_ordered_ab_group_add : 'a ab_group_add,
    ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add :
      'a ordered_ab_semigroup_monoid_add_imp_le};
val ab_group_add_ordered_ab_group_add = #ab_group_add_ordered_ab_group_add :
  'a ordered_ab_group_add -> 'a ab_group_add;
val ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add =
  #ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add :
  'a ordered_ab_group_add -> 'a ordered_ab_semigroup_monoid_add_imp_le;

val ordered_ab_semigroup_add_int =
  {ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_int,
    order_ordered_ab_semigroup_add = order_int}
  : Int.int ordered_ab_semigroup_add;

val strict_ordered_ab_semigroup_add_int =
  {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add =
     ordered_ab_semigroup_add_int}
  : Int.int strict_ordered_ab_semigroup_add;

val ordered_cancel_ab_semigroup_add_int =
  {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
     cancel_ab_semigroup_add_int,
    strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add =
      strict_ordered_ab_semigroup_add_int}
  : Int.int ordered_cancel_ab_semigroup_add;

val ordered_ab_semigroup_add_imp_le_int =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
     ordered_cancel_ab_semigroup_add_int}
  : Int.int ordered_ab_semigroup_add_imp_le;

val strict_ordered_comm_monoid_add_int =
  {comm_monoid_add_strict_ordered_comm_monoid_add = comm_monoid_add_int,
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
      strict_ordered_ab_semigroup_add_int}
  : Int.int strict_ordered_comm_monoid_add;

val ordered_comm_monoid_add_int =
  {comm_monoid_add_ordered_comm_monoid_add = comm_monoid_add_int,
    ordered_ab_semigroup_add_ordered_comm_monoid_add =
      ordered_ab_semigroup_add_int}
  : Int.int ordered_comm_monoid_add;

val ordered_cancel_comm_monoid_add_int =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add =
     ordered_cancel_ab_semigroup_add_int,
    ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
      ordered_comm_monoid_add_int,
    strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add =
      strict_ordered_comm_monoid_add_int}
  : Int.int ordered_cancel_comm_monoid_add;

val ordered_ab_semigroup_monoid_add_imp_le_int =
  {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
     cancel_comm_monoid_add_int,
    ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le =
      ordered_ab_semigroup_add_imp_le_int,
    ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le =
      ordered_cancel_comm_monoid_add_int}
  : Int.int ordered_ab_semigroup_monoid_add_imp_le;

val ordered_ab_group_add_int =
  {ab_group_add_ordered_ab_group_add = ab_group_add_int,
    ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add =
      ordered_ab_semigroup_monoid_add_imp_le_int}
  : Int.int ordered_ab_group_add;

type 'a linordered_ab_semigroup_add =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add :
     'a ordered_ab_semigroup_add,
    linorder_linordered_ab_semigroup_add : 'a linorder};
val ordered_ab_semigroup_add_linordered_ab_semigroup_add =
  #ordered_ab_semigroup_add_linordered_ab_semigroup_add :
  'a linordered_ab_semigroup_add -> 'a ordered_ab_semigroup_add;
val linorder_linordered_ab_semigroup_add = #linorder_linordered_ab_semigroup_add
  : 'a linordered_ab_semigroup_add -> 'a linorder;

type 'a linordered_cancel_ab_semigroup_add =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add :
     'a linordered_ab_semigroup_add,
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add :
      'a ordered_ab_semigroup_add_imp_le};
val linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
  #linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add :
  'a linordered_cancel_ab_semigroup_add -> 'a linordered_ab_semigroup_add;
val ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
  #ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add :
  'a linordered_cancel_ab_semigroup_add -> 'a ordered_ab_semigroup_add_imp_le;

type 'a linordered_ab_group_add =
  {linordered_cancel_ab_semigroup_add_linordered_ab_group_add :
     'a linordered_cancel_ab_semigroup_add,
    ordered_ab_group_add_linordered_ab_group_add : 'a ordered_ab_group_add};
val linordered_cancel_ab_semigroup_add_linordered_ab_group_add =
  #linordered_cancel_ab_semigroup_add_linordered_ab_group_add :
  'a linordered_ab_group_add -> 'a linordered_cancel_ab_semigroup_add;
val ordered_ab_group_add_linordered_ab_group_add =
  #ordered_ab_group_add_linordered_ab_group_add :
  'a linordered_ab_group_add -> 'a ordered_ab_group_add;

val linordered_ab_semigroup_add_int =
  {ordered_ab_semigroup_add_linordered_ab_semigroup_add =
     ordered_ab_semigroup_add_int,
    linorder_linordered_ab_semigroup_add = linorder_int}
  : Int.int linordered_ab_semigroup_add;

val linordered_cancel_ab_semigroup_add_int =
  {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add =
     linordered_ab_semigroup_add_int,
    ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add =
      ordered_ab_semigroup_add_imp_le_int}
  : Int.int linordered_cancel_ab_semigroup_add;

val linordered_ab_group_add_int =
  {linordered_cancel_ab_semigroup_add_linordered_ab_group_add =
     linordered_cancel_ab_semigroup_add_int,
    ordered_ab_group_add_linordered_ab_group_add = ordered_ab_group_add_int}
  : Int.int linordered_ab_group_add;

fun typerep_nata t = Typerep ("Nat.nat", []);

val countable_nat = {} : Int.int countable;

val typerep_nat = {typerep = typerep_nata} : Int.int typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  Int.int heap;

val zero_nat = {zero = (0 : Int.int)} : Int.int zero;

fun typerep_boola t = Typerep ("HOL.bool", []);

val countable_bool = {} : bool countable;

val typerep_bool = {typerep = typerep_boola} : bool typerep;

val heap_bool = {countable_heap = countable_bool, typerep_heap = typerep_bool} :
  bool heap;

fun typerep_optiona A_ t = Typerep ("Option.option", [typerep A_ Type]);

fun countable_option A_ = {} : ('a option) countable;

fun typerep_option A_ = {typerep = typerep_optiona A_} : ('a option) typerep;

fun heap_option A_ =
  {countable_heap = countable_option (countable_heap A_),
    typerep_heap = typerep_option (typerep_heap A_)}
  : ('a option) heap;

datatype num = One | Bit0 of num | Bit1 of num;

datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k) dij_impl_state_ext =
  Dij_impl_state_ext of 'a * 'b * 'c * 'd * 'e * 'f * 'g * 'h * 'i * 'j * 'k;

fun id x = (fn xa => xa) x;

fun eq A_ a b = equal A_ a b;

fun refa A_ x = (fn () => ref x);

fun src_imp x = (fn (fa, _) => (fn a => (fn () => Array.sub (fa, a)))) x;

fun tgt_imp x = (fn (_, a) => (fn b => (fn () => Array.sub (a, b)))) x;

fun edge_adv x = (fn _ => fn i => (fn () => (Int.+ (i, (1 : Int.int))))) x;

fun edge_cur x = (fn _ => (fn a => (fn () => a))) x;

fun parent i =
  Machine.div_nat (Machine.sub_nat (i, (1 : Int.int)), (2 : Int.int));

fun csr_has_imp A_ =
  (fn (ba, (_, ca)) => fn v => fn () =>
    let
      val i = (fn () => Array.sub (ca, v)) ();
      val e = (fn () => Array.sub (ba, Int.+ (v, (1 : Int.int)))) ();
    in
      Int.< (i, e)
    end);

fun csr_move_imp A_ =
  (fn (_, (_, ca)) => fn v => fn () =>
    let
      val i = (fn () => Array.sub (ca, v)) ();
      val _ = (fn () => Machine.upd (v, Int.+ (i, (1 : Int.int)), ca)) ();
    in
      ()
    end);

fun csr_reset_imp A_ =
  (fn (ba, (_, ca)) => fn v => fn () =>
    let
      val s = (fn () => Array.sub (ba, v)) ();
      val _ = (fn () => Machine.upd (v, s, ca)) ();
    in
      ()
    end);

fun edge_has_next x =
  (fn (fa, _) => fn i => fn () => let
                                    val l = (fn () => Array.length fa) ();
                                  in
                                    Int.< (i, l)
                                  end)
    x;

fun csr_fill_edges c b e si =
  (fn () =>
    let
      val ba = edge_has_next c si ();
    in
      (if ba
        then (fn f_ => fn () => f_ ((edge_cur c si) ()) ())
               (fn ea =>
                 (fn f_ => fn () => f_ ((src_imp c ea) ()) ())
                   (fn k =>
                     (fn f_ => fn () => f_ ((edge_cur c ea) ()) ())
                       (fn x =>
                         (fn f_ => fn () => f_
                           (((fn () => Array.sub (b, Int.+ (k, (1 : Int.int)))))
                           ()) ())
                           (fn p =>
                             (fn f_ => fn () => f_
                               (((fn () => Machine.upd
                                  (Int.+ (k, (1 : Int.int)),
                                  Int.+ (p, (1 : Int.int)), b)))
                               ()) ())
                               (fn _ =>
                                 (fn f_ => fn () => f_
                                   (((fn () => Machine.upd (p, x, e))) ()) ())
                                   (fn _ =>
                                     (fn f_ => fn () => f_ ((edge_adv c si) ())
                                       ())
                                       (csr_fill_edges c b e)))))))
        else (fn () => ()))
        ()
    end);

fun csr_init_edges c si m =
  (fn () =>
    let
      val b = edge_has_next c si ();
    in
      (if b then (fn f_ => fn () => f_ ((edge_cur c si) ()) ())
                   (fn e =>
                     (fn f_ => fn () => f_ ((edge_cur c e) ()) ())
                       (fn a => (fn () => Array.array (m, a))))
        else (fn () => Array.fromList []))
        ()
    end);

fun map_option f NONE = NONE
  | map_option f (SOME x2) = SOME (f x2);

fun csr_prefix_sums n b j acc =
  (if Int.<= (j, n)
    then (fn () =>
           let
             val c = (fn () => Array.sub (b, j)) ();
           in
             let
               val acca = Int.+ (c, acc);
             in
               (fn f_ => fn () => f_ (((fn () => Machine.upd (j, acca, b))) ())
                 ())
                 (fn _ => csr_prefix_sums n b (Int.+ (j, (1 : Int.int))) acca)
             end
               ()
           end)
    else (fn () => ()));

fun csr_count_edges n c b m si =
  (fn () =>
    let
      val ba = edge_has_next c si ();
    in
      (if ba
        then (fn f_ => fn () => f_ ((edge_cur c si) ()) ())
               (fn e =>
                 (fn f_ => fn () => f_ ((src_imp c e) ()) ())
                   (fn k =>
                     (fn f_ => fn () => f_
                       ((if Int.<= (Int.+ (k, (2 : Int.int)), n)
                          then (fn f_ => fn () => f_
                                 (((fn () => Array.sub (b,
                                    Int.+ (k, (2 : Int.int)))))
                                 ()) ())
                                 (fn d =>
                                   (fn f_ => fn () => f_
                                     (((fn () => Machine.upd
(Int.+ (k, (2 : Int.int)), Int.+ (d, (1 : Int.int)), b)))
                                     ()) ())
                                     (fn _ => (fn () => ())))
                          else (fn () => ()))
                       ()) ())
                       (fn _ =>
                         (fn f_ => fn () => f_ ((edge_adv c si) ()) ())
                           (csr_count_edges n c b (Int.+ (m, (1 : Int.int)))))))
        else (fn () => m))
        ()
    end);

fun csr_build_edges n c si =
  (fn () =>
    let
      val b =
        (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
      val m = csr_count_edges n c b (0 : Int.int) si ();
      val _ = csr_prefix_sums n b (1 : Int.int) (0 : Int.int) ();
      val e = csr_init_edges c si m ();
      val _ = csr_fill_edges c b e si ();
    in
      (b, e)
    end);

fun csr_current_imp A_ =
  (fn (_, (ea, ca)) => fn v => fn () =>
    let
      val x = (fn () => Array.sub (ca, v)) ();
    in
      (fn () => Array.sub (ea, x)) ()
    end);

fun copy_prefix_imp A_ k sa da i =
  (if Int.< (i, k)
    then (fn () => let
                     val x = (fn () => Array.sub (sa, i)) ();
                     val _ = (fn () => Machine.upd (i, x, da)) ();
                   in
                     copy_prefix_imp A_ k sa da (Int.+ (i, (1 : Int.int))) ()
                   end)
    else (fn () => ()));

fun csr_cursor_init n ba =
  (fn () => let
              val ca = (fn () => Array.array (n, (0 : Int.int))) ();
              val _ = copy_prefix_imp heap_nat n ba ca (0 : Int.int) ();
            in
              ca
            end);

fun arr_upd_imp B_ ix a k x =
  (fn () => let
              val _ = (fn () => Machine.upd (ix k, x, a)) ();
            in
              ()
            end);

fun arr_lookup_imp B_ ix a k = (fn () => Array.sub (a, ix k));

fun lc_has_imp A_ =
  (fn (sa, r) => fn () => let
                            val j = (fn () => ! r) ();
                            val l = (fn () => Array.length sa) ();
                          in
                            Int.< (j, l)
                          end);

fun lc_move_imp A_ =
  (fn (_, r) => fn () => let
                           val j = (fn () => ! r) ();
                         in
                           (fn () => r := (Int.+ (j, (1 : Int.int)))) ()
                         end);

fun sift_up_imp (A1_, A2_) ha pa ka x kx i =
  (if ((i : Int.int) = (0 : Int.int))
    then (fn () => let
                     val _ = (fn () => Machine.upd ((0 : Int.int), x, ha)) ();
                     val _ = (fn () => Machine.upd (x, (0 : Int.int), pa)) ();
                   in
                     ()
                   end)
    else let
           val p = parent i;
         in
           (fn () =>
             let
               val y = (fn () => Array.sub (ha, p)) ();
               val ky = (fn () => Array.sub (ka, y)) ();
             in
               (if less ((ord_preorder o preorder_order o order_linorder) A2_)
                     kx ky
                 then (fn f_ => fn () => f_ (((fn () => Machine.upd (i, y, ha)))
                        ()) ())
                        (fn _ =>
                          (fn f_ => fn () => f_
                            (((fn () => Machine.upd (y, i, pa))) ()) ())
                            (fn _ => sift_up_imp (A1_, A2_) ha pa ka x kx p))
                 else (fn f_ => fn () => f_ (((fn () => Machine.upd (i, x, ha)))
                        ()) ())
                        (fn _ =>
                          (fn f_ => fn () => f_
                            (((fn () => Machine.upd (x, i, pa))) ()) ())
                            (fn _ => (fn () => ()))))
                 ()
             end)
         end);

fun all_edges_imp u v e we = (fn () => true);

fun bool_array_set_isin_imp A_ xi x = (fn () => Array.sub (xi, x));

fun min_child_imp (A1_, A2_) ha ka sz l =
  (fn () =>
    let
      val a = (fn () => Array.sub (ha, l)) ();
      val kaa = (fn () => Array.sub (ka, a)) ();
    in
      (if Int.< (Int.+ (l, (1 : Int.int)), sz)
        then (fn f_ => fn () => f_
               (((fn () => Array.sub (ha, Int.+ (l, (1 : Int.int))))) ()) ())
               (fn b =>
                 (fn f_ => fn () => f_ (((fn () => Array.sub (ka, b))) ()) ())
                   (fn kb =>
                     (fn () =>
                       (if less ((ord_preorder o preorder_order o
                                   order_linorder)
                                  A2_)
                             kb kaa
                         then (Int.+ (l, (1 : Int.int)), (b, kb))
                         else (l, (a, kaa))))))
        else (fn () => (l, (a, kaa))))
        ()
    end);

fun sift_down_imp (A1_, A2_) ha pa ka sz x kx i =
  (if Int.< (Int.+ (Int.* ((2 : Int.int), i), (1 : Int.int)), sz)
    then (fn () =>
           let
             val a =
               min_child_imp (A1_, A2_) ha ka sz
                 (Int.+ (Int.* ((2 : Int.int), i), (1 : Int.int))) ();
           in
             let
               val (c, (z, kz)) = a;
             in
               (if less ((ord_preorder o preorder_order o order_linorder) A2_)
                     kz kx
                 then (fn f_ => fn () => f_ (((fn () => Machine.upd (i, z, ha)))
                        ()) ())
                        (fn _ =>
                          (fn f_ => fn () => f_
                            (((fn () => Machine.upd (z, i, pa))) ()) ())
                            (fn _ =>
                              sift_down_imp (A1_, A2_) ha pa ka sz x kx c))
                 else (fn f_ => fn () => f_ (((fn () => Machine.upd (i, x, ha)))
                        ()) ())
                        (fn _ =>
                          (fn f_ => fn () => f_
                            (((fn () => Machine.upd (x, i, pa))) ()) ())
                            (fn _ => (fn () => ()))))
             end
               ()
           end)
    else (fn () => let
                     val _ = (fn () => Machine.upd (i, x, ha)) ();
                     val _ = (fn () => Machine.upd (x, i, pa)) ();
                   in
                     ()
                   end));

fun lc_current_imp A_ =
  (fn (sa, r) => fn () => let
                            val x = (fn () => ! r) ();
                          in
                            (fn () => Array.sub (sa, x)) ()
                          end);

fun bool_array_set_insert_imp x xi =
  (fn () => let
              val _ = (fn () => Machine.upd (x, true, xi)) ();
            in
              ()
            end);

fun heap_empty_imp A_ n k0 =
  (fn () => let
              val ha = (fn () => Array.array (n, (0 : Int.int))) ();
              val pa = (fn () => Array.array (n, (0 : Int.int))) ();
              val ka = (fn () => Array.array (n, k0)) ();
              val sr = refa heap_nat (0 : Int.int) ();
            in
              (ha, (pa, (ka, sr)))
            end);

fun heap_insert_imp (A1_, A2_) hi x k =
  let
    val (ha, (pa, (ka, sr))) = hi;
  in
    (fn () => let
                val sz = (fn () => ! sr) ();
                val _ = (fn () => Machine.upd (x, k, ka)) ();
                val _ = (fn () => sr := (Int.+ (sz, (1 : Int.int)))) ();
              in
                sift_up_imp (A1_, A2_) ha pa ka x k sz ()
              end)
  end;

fun dijkstra_edge_ids ra pa k i =
  (if Int.< (i, k)
    then (fn () =>
           let
             val e =
               (fn () => Array.sub (ra,
                 Machine.sub_nat (k, Int.+ (i, (1 : Int.int)))))
                 ();
             val _ = (fn () => Machine.upd (i, e, pa)) ();
           in
             dijkstra_edge_ids ra pa k (Int.+ (i, (1 : Int.int))) ()
           end)
    else (fn () => ()));

fun heap_extract_min_imp (A1_, A2_) hi =
  let
    val (ha, (pa, (ka, sr))) = hi;
  in
    (fn () =>
      let
        val sz = (fn () => ! sr) ();
      in
        (if ((sz : Int.int) = (0 : Int.int)) then (fn () => NONE)
          else (fn f_ => fn () => f_ (((fn () => Array.sub (ha, (0 : Int.int))))
                 ()) ())
                 (fn x =>
                   (fn f_ => fn () => f_
                     (((fn () => sr := (Machine.sub_nat (sz, (1 : Int.int)))))
                     ()) ())
                     (fn _ =>
                       (if (((Machine.sub_nat (sz,
                               (1 : Int.int))) : Int.int) = (0 : Int.int))
                         then (fn () => (SOME x))
                         else (fn f_ => fn () => f_
                                (((fn () => Array.sub (ha,
                                   Machine.sub_nat (sz, (1 : Int.int)))))
                                ()) ())
                                (fn y =>
                                  (fn f_ => fn () => f_
                                    (((fn () => Array.sub (ka, y))) ()) ())
                                    (fn ky =>
                                      (fn f_ => fn () => f_
((sift_down_imp (A1_, A2_) ha pa ka (Machine.sub_nat (sz, (1 : Int.int))) y ky
   (0 : Int.int))
()) ())
(fn _ => (fn () => (SOME x)))))))))
          ()
      end)
  end;

fun heap_extract_min_key_imp (A1_, A2_) hi =
  let
    val (ha, (_, (ka, sr))) = hi;
  in
    (fn () =>
      let
        val sz = (fn () => ! sr) ();
      in
        (if ((sz : Int.int) = (0 : Int.int)) then (fn () => NONE)
          else (fn f_ => fn () => f_ (((fn () => Array.sub (ha, (0 : Int.int))))
                 ()) ())
                 (fn x =>
                   (fn f_ => fn () => f_ (((fn () => Array.sub (ka, x))) ()) ())
                     (fn k =>
                       (fn f_ => fn () => f_
                         ((heap_extract_min_imp (A1_, A2_) hi) ()) ())
                         (fn r => (fn () => (map_option (fn y => (y, k)) r))))))
          ()
      end)
  end;

fun dimp_target
  (Dij_impl_state_ext
    (dimp_dist, dimp_seen, dimp_parent, dimp_heap, dimp_graph, dimp_srcs,
      dimp_weight, dimp_ends, dimp_target, dimp_allowed, more))
  = dimp_target;

fun dijkstra_target_test_code (A1_, A2_) early_stop s u =
  (if early_stop then bool_array_set_isin_imp heap_bool (dimp_target s) u
    else (fn () => false));

fun dimp_graph
  (Dij_impl_state_ext
    (dimp_dist, dimp_seen, dimp_parent, dimp_heap, dimp_graph, dimp_srcs,
      dimp_weight, dimp_ends, dimp_target, dimp_allowed, more))
  = dimp_graph;

fun dimp_srcs
  (Dij_impl_state_ext
    (dimp_dist, dimp_seen, dimp_parent, dimp_heap, dimp_graph, dimp_srcs,
      dimp_weight, dimp_ends, dimp_target, dimp_allowed, more))
  = dimp_srcs;

fun dimp_seen
  (Dij_impl_state_ext
    (dimp_dist, dimp_seen, dimp_parent, dimp_heap, dimp_graph, dimp_srcs,
      dimp_weight, dimp_ends, dimp_target, dimp_allowed, more))
  = dimp_seen;

fun dimp_heap
  (Dij_impl_state_ext
    (dimp_dist, dimp_seen, dimp_parent, dimp_heap, dimp_graph, dimp_srcs,
      dimp_weight, dimp_ends, dimp_target, dimp_allowed, more))
  = dimp_heap;

fun dimp_dist
  (Dij_impl_state_ext
    (dimp_dist, dimp_seen, dimp_parent, dimp_heap, dimp_graph, dimp_srcs,
      dimp_weight, dimp_ends, dimp_target, dimp_allowed, more))
  = dimp_dist;

fun dijkstra_source_code (A1_, A2_) s v =
  (fn () =>
    let
      val _ =
        arr_upd_imp A2_ id (dimp_dist s) v
          (zero ((zero_monoid_add o monoid_add_group_add o
                   group_add_ab_group_add o ab_group_add_ordered_ab_group_add o
                   ordered_ab_group_add_linordered_ab_group_add)
                  A1_))
          ();
    in
      heap_insert_imp
        (A2_, (linorder_linordered_ab_semigroup_add o
                linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add o
                linordered_cancel_ab_semigroup_add_linordered_ab_group_add)
                A1_)
        (dimp_heap s) v
        (zero ((zero_monoid_add o monoid_add_group_add o
                 group_add_ab_group_add o ab_group_add_ordered_ab_group_add o
                 ordered_ab_group_add_linordered_ab_group_add)
                A1_))
        ()
    end);

fun dimp_weight
  (Dij_impl_state_ext
    (dimp_dist, dimp_seen, dimp_parent, dimp_heap, dimp_graph, dimp_srcs,
      dimp_weight, dimp_ends, dimp_target, dimp_allowed, more))
  = dimp_weight;

fun dimp_parent
  (Dij_impl_state_ext
    (dimp_dist, dimp_seen, dimp_parent, dimp_heap, dimp_graph, dimp_srcs,
      dimp_weight, dimp_ends, dimp_target, dimp_allowed, more))
  = dimp_parent;

fun heap_decrease_key_imp (A1_, A2_) hi x k =
  let
    val (ha, (pa, (ka, _))) = hi;
  in
    (fn () => let
                val i = (fn () => Array.sub (pa, x)) ();
                val _ = (fn () => Machine.upd (x, k, ka)) ();
              in
                sift_up_imp (A1_, A2_) ha pa ka x k i ()
              end)
  end;

fun dimp_ends
  (Dij_impl_state_ext
    (dimp_dist, dimp_seen, dimp_parent, dimp_heap, dimp_graph, dimp_srcs,
      dimp_weight, dimp_ends, dimp_target, dimp_allowed, more))
  = dimp_ends;

fun dijkstra_relax_all (A1_, A2_, A3_) unreached s u du e =
  (fn () =>
    let
      val v = tgt_imp (dimp_ends s) e ();
      val sn = bool_array_set_isin_imp heap_bool (dimp_seen s) v ();
    in
      (if sn then (fn () => ())
        else (fn f_ => fn () => f_ ((arr_lookup_imp A3_ id (dimp_weight s) e)
               ()) ())
               (fn we =>
                 (fn f_ => fn () => f_ ((arr_lookup_imp A3_ id (dimp_dist s) v)
                   ()) ())
                   (fn dv =>
                     let
                       val nv =
                         plus ((plus_semigroup_add o semigroup_add_monoid_add o
                                 monoid_add_group_add o group_add_ab_group_add o
                                 ab_group_add_ordered_ab_group_add o
                                 ordered_ab_group_add_linordered_ab_group_add)
                                A1_)
                           du we;
                     in
                       (if eq A2_ dv unreached
                         then (fn f_ => fn () => f_
                                ((arr_upd_imp A3_ id (dimp_dist s) v nv) ()) ())
                                (fn _ =>
                                  (fn f_ => fn () => f_
                                    ((arr_upd_imp (heap_option heap_nat) id
                                       (dimp_parent s) v (SOME e))
                                    ()) ())
                                    (fn _ =>
                                      heap_insert_imp
(A3_, (linorder_linordered_ab_semigroup_add o
        linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add o
        linordered_cancel_ab_semigroup_add_linordered_ab_group_add)
        A1_)
(dimp_heap s) v nv))
                         else (if less ((ord_preorder o preorder_order o
  order_linorder o linorder_linordered_ab_semigroup_add o
  linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add o
  linordered_cancel_ab_semigroup_add_linordered_ab_group_add)
 A1_)
                                    nv dv
                                then (fn f_ => fn () => f_
                                       ((arr_upd_imp A3_ id (dimp_dist s) v nv)
                                       ()) ())
                                       (fn _ =>
 (fn f_ => fn () => f_
   ((arr_upd_imp (heap_option heap_nat) id (dimp_parent s) v (SOME e)) ()) ())
   (fn _ =>
     heap_decrease_key_imp
       (A3_, (linorder_linordered_ab_semigroup_add o
               linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add o
               linordered_cancel_ab_semigroup_add_linordered_ab_group_add)
               A1_)
       (dimp_heap s) v nv))
                                else (fn () => ())))
                     end)))
        ()
    end);

fun dijkstra_loop_all (A1_, A2_, A3_) unreached early_stop s cur =
  (case cur
    of NONE =>
      (fn () =>
        let
          val b = lc_has_imp heap_nat (dimp_srcs s) ();
        in
          (if b then (fn f_ => fn () => f_
                       ((lc_current_imp heap_nat (dimp_srcs s)) ()) ())
                       (fn v =>
                         (fn f_ => fn () => f_
                           ((lc_move_imp heap_nat (dimp_srcs s)) ()) ())
                           (fn _ =>
                             (fn f_ => fn () => f_
                               ((dijkstra_source_code (A1_, A3_) s v) ()) ())
                               (fn _ =>
                                 dijkstra_loop_all (A1_, A2_, A3_) unreached
                                   early_stop s NONE)))
            else (fn f_ => fn () => f_
                   ((heap_extract_min_key_imp
                      (A3_, (linorder_linordered_ab_semigroup_add o
                              linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add o
                              linordered_cancel_ab_semigroup_add_linordered_ab_group_add)
                              A1_)
                      (dimp_heap s))
                   ()) ())
                   (fn a =>
                     (case a of NONE => (fn () => NONE)
                       | SOME (u, _) =>
                         (fn f_ => fn () => f_
                           ((bool_array_set_isin_imp heap_bool (dimp_seen s) u)
                           ()) ())
                           (fn sn =>
                             (if sn
                               then dijkstra_loop_all (A1_, A2_, A3_) unreached
                                      early_stop s NONE
                               else (fn f_ => fn () => f_
                                      ((bool_array_set_insert_imp u
 (dimp_seen s))
                                      ()) ())
                                      (fn _ =>
(fn f_ => fn () => f_ ((dijkstra_target_test_code (A1_, A3_) early_stop s u) ())
  ())
  (fn t =>
    (if t then (fn () => (SOME u))
      else (fn f_ => fn () => f_ ((csr_reset_imp heap_nat (dimp_graph s) u) ())
             ())
             (fn _ =>
               dijkstra_loop_all (A1_, A2_, A3_) unreached early_stop s
                 (SOME u))))))))))
            ()
        end)
    | SOME u =>
      (fn () =>
        let
          val b = csr_has_imp heap_nat (dimp_graph s) u ();
        in
          (if b then (fn f_ => fn () => f_
                       ((arr_lookup_imp A3_ id (dimp_dist s) u) ()) ())
                       (fn du =>
                         (fn f_ => fn () => f_
                           ((csr_current_imp heap_nat (dimp_graph s) u) ()) ())
                           (fn e =>
                             (fn f_ => fn () => f_
                               ((csr_move_imp heap_nat (dimp_graph s) u) ()) ())
                               (fn _ =>
                                 (fn f_ => fn () => f_
                                   ((dijkstra_relax_all (A1_, A2_, A3_)
                                      unreached s u du e)
                                   ()) ())
                                   (fn _ =>
                                     dijkstra_loop_all (A1_, A2_, A3_) unreached
                                       early_stop s (SOME u)))))
            else dijkstra_loop_all (A1_, A2_, A3_) unreached early_stop s NONE)
            ()
        end));

fun dijkstra_path_rev_code ei pa ra v k =
  (fn () =>
    let
      val a = arr_lookup_imp (heap_option heap_nat) id pa v ();
    in
      (case a of NONE => (fn () => k)
        | SOME e =>
          (fn f_ => fn () => f_ (((fn () => Machine.upd (k, e, ra))) ()) ())
            (fn _ =>
              (fn f_ => fn () => f_ ((src_imp ei e) ()) ())
                (fn u =>
                  dijkstra_path_rev_code ei pa ra u
                    (Int.+ (k, (1 : Int.int))))))
        ()
    end);

fun dijkstra_path_code (A1_, A2_) s ra v =
  dijkstra_path_rev_code (dimp_ends s) (dimp_parent s) ra v (0 : Int.int);

fun dijkstra_path_ids (A1_, A2_) si ra v =
  (fn () => let
              val k = dijkstra_path_code (A1_, A2_) si ra v ();
              val pa = (fn () => Array.array (k, (0 : Int.int))) ();
              val _ = dijkstra_edge_ids ra pa k (0 : Int.int) ();
            in
              pa
            end);

fun dijkstra_sp_query (A1_, A2_, A3_) unreached th v =
  let
    val (si, ra) = th;
  in
    (fn () =>
      let
        val d = (fn () => Array.sub (dimp_dist si, v)) ();
      in
        (if eq A2_ d unreached then (fn () => NONE)
          else (fn f_ => fn () => f_ ((dijkstra_path_ids (A1_, A3_) si ra v) ())
                 ())
                 (fn pa => (fn () => (SOME pa))))
          ()
      end)
  end;

fun dijkstra_csr_run_all (A1_, A2_, A3_) n unreached early_stop fa ta wa sa tg =
  (fn () =>
    let
      val a = csr_build_edges n (fa, ta) (0 : Int.int) ();
    in
      let
        val (ba, ea) = a;
      in
        (fn f_ => fn () => f_ ((csr_cursor_init n ba) ()) ())
          (fn ca =>
            (fn f_ => fn () => f_ (((fn () => Array.array (n, unreached))) ())
              ())
              (fn da =>
                (fn f_ => fn () => f_ (((fn () => Array.array (n, NONE))) ())
                  ())
                  (fn pa =>
                    (fn f_ => fn () => f_ (((fn () => Array.array (n, false)))
                      ()) ())
                      (fn se =>
                        (fn f_ => fn () => f_
                          ((heap_empty_imp A3_ n
                             (zero ((zero_monoid_add o monoid_add_group_add o
                                      group_add_ab_group_add o
                                      ab_group_add_ordered_ab_group_add o
                                      ordered_ab_group_add_linordered_ab_group_add)
                                     A1_)))
                          ()) ())
                          (fn hq =>
                            (fn f_ => fn () => f_ ((refa heap_nat (0 : Int.int))
                              ()) ())
                              (fn r =>
                                let
                                  val si =
                                    Dij_impl_state_ext
                                      (da, se, pa, hq, (ba, (ea, ca)), (sa, r),
wa, (fa, ta), tg, all_edges_imp, ());
                                in
                                  (fn f_ => fn () => f_
                                    ((dijkstra_loop_all (A1_, A2_, A3_)
                                       unreached early_stop si NONE)
                                    ()) ())
                                    (fn t => (fn () => (si, t)))
                                end))))))
      end
        ()
    end);

fun dijkstra_sp_compute (A1_, A2_, A3_) (B1_, B2_) n unreached fa ta wa sa =
  (fn () =>
    let
      val tg = (fn () => Array.array (n, false)) ();
      val ra = (fn () => Array.array (n, zero B1_)) ();
      val a =
        dijkstra_csr_run_all (A1_, A2_, A3_) n unreached false fa ta wa sa tg
          ();
    in
      let
        val (si, _) = a;
      in
        (fn () => (si, ra))
      end
        ()
    end);

fun dijkstra_mark_targets tv tg i =
  (fn () =>
    let
      val l = (fn () => Array.length tv) ();
    in
      (if Int.< (i, l)
        then (fn f_ => fn () => f_ (((fn () => Array.sub (tv, i))) ()) ())
               (fn v =>
                 (fn f_ => fn () => f_ (((fn () => Machine.upd (v, true, tg)))
                   ()) ())
                   (fn _ =>
                     dijkstra_mark_targets tv tg (Int.+ (i, (1 : Int.int)))))
        else (fn () => ()))
        ()
    end);

fun dijkstra_sp_query_int x =
  dijkstra_sp_query (linordered_ab_group_add_int, equal_int, heap_int)
    (Int.~ (1 : Int.int)) x;

fun dijkstra_shortest_path (A1_, A2_, A3_) n unreached fa ta wa sa tv =
  (fn () =>
    let
      val tg = (fn () => Array.array (n, false)) ();
      val ra = (fn () => Array.array (n, (0 : Int.int))) ();
      val _ = dijkstra_mark_targets tv tg (0 : Int.int) ();
      val a =
        dijkstra_csr_run_all (A1_, A2_, A3_) n unreached true fa ta wa sa tg ();
    in
      (case a of (_, NONE) => (fn () => NONE)
        | (si, SOME u) =>
          (fn f_ => fn () => f_ ((dijkstra_path_ids (A1_, A3_) si ra u) ()) ())
            (fn pa => (fn () => (SOME pa))))
        ()
    end);

fun dijkstra_sp_compute_int n =
  dijkstra_sp_compute (linordered_ab_group_add_int, equal_int, heap_int)
    (zero_nat, heap_nat) n (Int.~ (1 : Int.int));

fun dijkstra_shortest_path_int n =
  dijkstra_shortest_path (linordered_ab_group_add_int, equal_int, heap_int) n
    (Int.~ (1 : Int.int));

end; (*struct Dijkstra*)
