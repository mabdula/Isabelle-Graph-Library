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


structure Bipartite_Matching : sig
  val matching_imp : Int.int -> Int.int array -> Int.int array -> (unit -> (bool array))
  val b_matching_imp : Int.int array -> Int.int array -> Int.int array -> (unit -> (bool array))
  val weighted_matching_int_imp : Int.int -> Int.int array -> Int.int array -> Int.int array -> (unit -> (bool array))
  val weighted_b_matching_int_imp : Int.int array -> Int.int array -> Int.int array -> Int.int array -> (unit -> (bool array))
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

val heap_int = {countable_heap = countable_int, typerep_heap = typerep_int} : Int.int heap;

type 'a times = {times : 'a -> 'a -> 'a};
val times = #times : 'a times -> 'a -> 'a -> 'a;

type 'a dvd = {times_dvd : 'a times};
val times_dvd = #times_dvd : 'a dvd -> 'a times;

val times_int = {times = (fn a => fn b => Int.* (a, b))} : Int.int times;

val dvd_int = {times_dvd = times_int} : Int.int dvd;

fun abs_inta i = (if Int.< (i, (0 : Int.int)) then Int.~ i else i);

type 'a abs = {abs : 'a -> 'a};
val abs = #abs : 'a abs -> 'a -> 'a;

val abs_int = {abs = abs_inta} : Int.int abs;

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_int = {one = (1 : Int.int)} : Int.int one;

fun sgn_inta i = (if ((i : Int.int) = (0 : Int.int)) then (0 : Int.int) else (if Int.< ((0 : Int.int), i) then (1 : Int.int) else Int.~ (1 : Int.int)));

type 'a sgn = {sgn : 'a -> 'a};
val sgn = #sgn : 'a sgn -> 'a -> 'a;

val sgn_int = {sgn = sgn_inta} : Int.int sgn;

type 'a uminus = {uminus : 'a -> 'a};
val uminus = #uminus : 'a uminus -> 'a -> 'a;

type 'a minus = {minus : 'a -> 'a -> 'a};
val minus = #minus : 'a minus -> 'a -> 'a -> 'a;

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a cancel_semigroup_add = {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add : 'a cancel_semigroup_add -> 'a semigroup_add;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add : 'a ab_semigroup_add -> 'a semigroup_add;

type 'a cancel_ab_semigroup_add = {ab_semigroup_add_cancel_ab_semigroup_add : 'a ab_semigroup_add, cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_semigroup_add, minus_cancel_ab_semigroup_add : 'a minus};
val ab_semigroup_add_cancel_ab_semigroup_add = #ab_semigroup_add_cancel_ab_semigroup_add : 'a cancel_ab_semigroup_add -> 'a ab_semigroup_add;
val cancel_semigroup_add_cancel_ab_semigroup_add = #cancel_semigroup_add_cancel_ab_semigroup_add : 'a cancel_ab_semigroup_add -> 'a cancel_semigroup_add;
val minus_cancel_ab_semigroup_add = #minus_cancel_ab_semigroup_add : 'a cancel_ab_semigroup_add -> 'a minus;

type 'a monoid_add = {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add : 'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add = {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add, monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add : 'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add : 'a comm_monoid_add -> 'a monoid_add;

type 'a cancel_comm_monoid_add = {cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_ab_semigroup_add, comm_monoid_add_cancel_comm_monoid_add : 'a comm_monoid_add};
val cancel_ab_semigroup_add_cancel_comm_monoid_add = #cancel_ab_semigroup_add_cancel_comm_monoid_add : 'a cancel_comm_monoid_add -> 'a cancel_ab_semigroup_add;
val comm_monoid_add_cancel_comm_monoid_add = #comm_monoid_add_cancel_comm_monoid_add : 'a cancel_comm_monoid_add -> 'a comm_monoid_add;

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult : 'a semigroup_mult -> 'a times;

type 'a semiring = {ab_semigroup_add_semiring : 'a ab_semigroup_add, semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring : 'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring : 'a semiring -> 'a semigroup_mult;

type 'a semiring_0 = {comm_monoid_add_semiring_0 : 'a comm_monoid_add, mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 : 'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 : 'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

type 'a semiring_0_cancel = {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add, semiring_0_semiring_0_cancel : 'a semiring_0};
val cancel_comm_monoid_add_semiring_0_cancel = #cancel_comm_monoid_add_semiring_0_cancel : 'a semiring_0_cancel -> 'a cancel_comm_monoid_add;
val semiring_0_semiring_0_cancel = #semiring_0_semiring_0_cancel : 'a semiring_0_cancel -> 'a semiring_0;

type 'a ab_semigroup_mult = {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};
val semigroup_mult_ab_semigroup_mult = #semigroup_mult_ab_semigroup_mult : 'a ab_semigroup_mult -> 'a semigroup_mult;

type 'a comm_semiring = {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult, semiring_comm_semiring : 'a semiring};
val ab_semigroup_mult_comm_semiring = #ab_semigroup_mult_comm_semiring : 'a comm_semiring -> 'a ab_semigroup_mult;
val semiring_comm_semiring = #semiring_comm_semiring : 'a comm_semiring -> 'a semiring;

type 'a comm_semiring_0 = {comm_semiring_comm_semiring_0 : 'a comm_semiring, semiring_0_comm_semiring_0 : 'a semiring_0};
val comm_semiring_comm_semiring_0 = #comm_semiring_comm_semiring_0 : 'a comm_semiring_0 -> 'a comm_semiring;
val semiring_0_comm_semiring_0 = #semiring_0_comm_semiring_0 : 'a comm_semiring_0 -> 'a semiring_0;

type 'a comm_semiring_0_cancel = {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0, semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};
val comm_semiring_0_comm_semiring_0_cancel = #comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0_cancel -> 'a comm_semiring_0;
val semiring_0_cancel_comm_semiring_0_cancel = #semiring_0_cancel_comm_semiring_0_cancel : 'a comm_semiring_0_cancel -> 'a semiring_0_cancel;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

type 'a monoid_mult = {semigroup_mult_monoid_mult : 'a semigroup_mult, power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult : 'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a numeral = {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral : 'a numeral -> 'a semigroup_add;

type 'a semiring_numeral = {monoid_mult_semiring_numeral : 'a monoid_mult, numeral_semiring_numeral : 'a numeral, semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral : 'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral : 'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral : 'a semiring_numeral -> 'a semiring;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

type 'a semiring_1 = {semiring_numeral_semiring_1 : 'a semiring_numeral, semiring_0_semiring_1 : 'a semiring_0, zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 : 'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 : 'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 : 'a semiring_1 -> 'a zero_neq_one;

type 'a semiring_1_cancel = {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel, semiring_1_semiring_1_cancel : 'a semiring_1};
val semiring_0_cancel_semiring_1_cancel = #semiring_0_cancel_semiring_1_cancel : 'a semiring_1_cancel -> 'a semiring_0_cancel;
val semiring_1_semiring_1_cancel = #semiring_1_semiring_1_cancel : 'a semiring_1_cancel -> 'a semiring_1;

type 'a comm_monoid_mult = {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult, monoid_mult_comm_monoid_mult : 'a monoid_mult, dvd_comm_monoid_mult : 'a dvd};
val ab_semigroup_mult_comm_monoid_mult = #ab_semigroup_mult_comm_monoid_mult : 'a comm_monoid_mult -> 'a ab_semigroup_mult;
val monoid_mult_comm_monoid_mult = #monoid_mult_comm_monoid_mult : 'a comm_monoid_mult -> 'a monoid_mult;
val dvd_comm_monoid_mult = #dvd_comm_monoid_mult : 'a comm_monoid_mult -> 'a dvd;

type 'a comm_semiring_1 = {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult, comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0, semiring_1_comm_semiring_1 : 'a semiring_1};
val comm_monoid_mult_comm_semiring_1 = #comm_monoid_mult_comm_semiring_1 : 'a comm_semiring_1 -> 'a comm_monoid_mult;
val comm_semiring_0_comm_semiring_1 = #comm_semiring_0_comm_semiring_1 : 'a comm_semiring_1 -> 'a comm_semiring_0;
val semiring_1_comm_semiring_1 = #semiring_1_comm_semiring_1 : 'a comm_semiring_1 -> 'a semiring_1;

type 'a comm_semiring_1_cancel = {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel, comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1, semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};
val comm_semiring_0_cancel_comm_semiring_1_cancel = #comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_1_cancel -> 'a comm_semiring_0_cancel;
val comm_semiring_1_comm_semiring_1_cancel = #comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1_cancel -> 'a comm_semiring_1;
val semiring_1_cancel_comm_semiring_1_cancel = #semiring_1_cancel_comm_semiring_1_cancel : 'a comm_semiring_1_cancel -> 'a semiring_1_cancel;

type 'a comm_semiring_1_cancel_crossproduct = {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct : 'a comm_semiring_1_cancel};
val comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct = #comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct : 'a comm_semiring_1_cancel_crossproduct -> 'a comm_semiring_1_cancel;

type 'a semiring_no_zero_divisors = {semiring_0_semiring_no_zero_divisors : 'a semiring_0};
val semiring_0_semiring_no_zero_divisors = #semiring_0_semiring_no_zero_divisors : 'a semiring_no_zero_divisors -> 'a semiring_0;

type 'a semiring_1_no_zero_divisors = {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1, semiring_no_zero_divisors_semiring_1_no_zero_divisors : 'a semiring_no_zero_divisors};
val semiring_1_semiring_1_no_zero_divisors = #semiring_1_semiring_1_no_zero_divisors : 'a semiring_1_no_zero_divisors -> 'a semiring_1;
val semiring_no_zero_divisors_semiring_1_no_zero_divisors = #semiring_no_zero_divisors_semiring_1_no_zero_divisors : 'a semiring_1_no_zero_divisors -> 'a semiring_no_zero_divisors;

type 'a semiring_no_zero_divisors_cancel = {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel : 'a semiring_no_zero_divisors};
val semiring_no_zero_divisors_semiring_no_zero_divisors_cancel = #semiring_no_zero_divisors_semiring_no_zero_divisors_cancel : 'a semiring_no_zero_divisors_cancel -> 'a semiring_no_zero_divisors;

type 'a group_add = {cancel_semigroup_add_group_add : 'a cancel_semigroup_add, minus_group_add : 'a minus, monoid_add_group_add : 'a monoid_add, uminus_group_add : 'a uminus};
val cancel_semigroup_add_group_add = #cancel_semigroup_add_group_add : 'a group_add -> 'a cancel_semigroup_add;
val minus_group_add = #minus_group_add : 'a group_add -> 'a minus;
val monoid_add_group_add = #monoid_add_group_add : 'a group_add -> 'a monoid_add;
val uminus_group_add = #uminus_group_add : 'a group_add -> 'a uminus;

type 'a ab_group_add = {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add, group_add_ab_group_add : 'a group_add};
val cancel_comm_monoid_add_ab_group_add = #cancel_comm_monoid_add_ab_group_add : 'a ab_group_add -> 'a cancel_comm_monoid_add;
val group_add_ab_group_add = #group_add_ab_group_add : 'a ab_group_add -> 'a group_add;

type 'a ring = {ab_group_add_ring : 'a ab_group_add, semiring_0_cancel_ring : 'a semiring_0_cancel};
val ab_group_add_ring = #ab_group_add_ring : 'a ring -> 'a ab_group_add;
val semiring_0_cancel_ring = #semiring_0_cancel_ring : 'a ring -> 'a semiring_0_cancel;

type 'a ring_no_zero_divisors = {ring_ring_no_zero_divisors : 'a ring, semiring_no_zero_divisors_cancel_ring_no_zero_divisors : 'a semiring_no_zero_divisors_cancel};
val ring_ring_no_zero_divisors = #ring_ring_no_zero_divisors : 'a ring_no_zero_divisors -> 'a ring;
val semiring_no_zero_divisors_cancel_ring_no_zero_divisors = #semiring_no_zero_divisors_cancel_ring_no_zero_divisors : 'a ring_no_zero_divisors -> 'a semiring_no_zero_divisors_cancel;

type 'a neg_numeral = {group_add_neg_numeral : 'a group_add, numeral_neg_numeral : 'a numeral};
val group_add_neg_numeral = #group_add_neg_numeral : 'a neg_numeral -> 'a group_add;
val numeral_neg_numeral = #numeral_neg_numeral : 'a neg_numeral -> 'a numeral;

type 'a ring_1 = {neg_numeral_ring_1 : 'a neg_numeral, ring_ring_1 : 'a ring, semiring_1_cancel_ring_1 : 'a semiring_1_cancel};
val neg_numeral_ring_1 = #neg_numeral_ring_1 : 'a ring_1 -> 'a neg_numeral;
val ring_ring_1 = #ring_ring_1 : 'a ring_1 -> 'a ring;
val semiring_1_cancel_ring_1 = #semiring_1_cancel_ring_1 : 'a ring_1 -> 'a semiring_1_cancel;

type 'a ring_1_no_zero_divisors = {ring_1_ring_1_no_zero_divisors : 'a ring_1, ring_no_zero_divisors_ring_1_no_zero_divisors : 'a ring_no_zero_divisors, semiring_1_no_zero_divisors_ring_1_no_zero_divisors : 'a semiring_1_no_zero_divisors};
val ring_1_ring_1_no_zero_divisors = #ring_1_ring_1_no_zero_divisors : 'a ring_1_no_zero_divisors -> 'a ring_1;
val ring_no_zero_divisors_ring_1_no_zero_divisors = #ring_no_zero_divisors_ring_1_no_zero_divisors : 'a ring_1_no_zero_divisors -> 'a ring_no_zero_divisors;
val semiring_1_no_zero_divisors_ring_1_no_zero_divisors = #semiring_1_no_zero_divisors_ring_1_no_zero_divisors : 'a ring_1_no_zero_divisors -> 'a semiring_1_no_zero_divisors;

type 'a comm_ring = {comm_semiring_0_cancel_comm_ring : 'a comm_semiring_0_cancel, ring_comm_ring : 'a ring};
val comm_semiring_0_cancel_comm_ring = #comm_semiring_0_cancel_comm_ring : 'a comm_ring -> 'a comm_semiring_0_cancel;
val ring_comm_ring = #ring_comm_ring : 'a comm_ring -> 'a ring;

type 'a comm_ring_1 = {comm_ring_comm_ring_1 : 'a comm_ring, comm_semiring_1_cancel_comm_ring_1 : 'a comm_semiring_1_cancel, ring_1_comm_ring_1 : 'a ring_1};
val comm_ring_comm_ring_1 = #comm_ring_comm_ring_1 : 'a comm_ring_1 -> 'a comm_ring;
val comm_semiring_1_cancel_comm_ring_1 = #comm_semiring_1_cancel_comm_ring_1 : 'a comm_ring_1 -> 'a comm_semiring_1_cancel;
val ring_1_comm_ring_1 = #ring_1_comm_ring_1 : 'a comm_ring_1 -> 'a ring_1;

type 'a semidom = {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel, semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};
val comm_semiring_1_cancel_semidom = #comm_semiring_1_cancel_semidom : 'a semidom -> 'a comm_semiring_1_cancel;
val semiring_1_no_zero_divisors_semidom = #semiring_1_no_zero_divisors_semidom : 'a semidom -> 'a semiring_1_no_zero_divisors;

type 'a idom = {comm_ring_1_idom : 'a comm_ring_1, ring_1_no_zero_divisors_idom : 'a ring_1_no_zero_divisors, semidom_idom : 'a semidom, comm_semiring_1_cancel_crossproduct_idom : 'a comm_semiring_1_cancel_crossproduct};
val comm_ring_1_idom = #comm_ring_1_idom : 'a idom -> 'a comm_ring_1;
val ring_1_no_zero_divisors_idom = #ring_1_no_zero_divisors_idom : 'a idom -> 'a ring_1_no_zero_divisors;
val semidom_idom = #semidom_idom : 'a idom -> 'a semidom;
val comm_semiring_1_cancel_crossproduct_idom = #comm_semiring_1_cancel_crossproduct_idom : 'a idom -> 'a comm_semiring_1_cancel_crossproduct;

val plus_int = {plus = (fn a => fn b => Int.+ (a, b))} : Int.int plus;

val semigroup_add_int = {plus_semigroup_add = plus_int} : Int.int semigroup_add;

val cancel_semigroup_add_int = {semigroup_add_cancel_semigroup_add = semigroup_add_int} : Int.int cancel_semigroup_add;

val ab_semigroup_add_int = {semigroup_add_ab_semigroup_add = semigroup_add_int} : Int.int ab_semigroup_add;

val minus_int = {minus = (fn a => fn b => Int.- (a, b))} : Int.int minus;

val cancel_ab_semigroup_add_int = {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int, cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int, minus_cancel_ab_semigroup_add = minus_int} : Int.int cancel_ab_semigroup_add;

val zero_int = {zero = (0 : Int.int)} : Int.int zero;

val monoid_add_int = {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} : Int.int monoid_add;

val comm_monoid_add_int = {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int, monoid_add_comm_monoid_add = monoid_add_int} : Int.int comm_monoid_add;

val cancel_comm_monoid_add_int = {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_int, comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int} : Int.int cancel_comm_monoid_add;

val mult_zero_int = {times_mult_zero = times_int, zero_mult_zero = zero_int} : Int.int mult_zero;

val semigroup_mult_int = {times_semigroup_mult = times_int} : Int.int semigroup_mult;

val semiring_int = {ab_semigroup_add_semiring = ab_semigroup_add_int, semigroup_mult_semiring = semigroup_mult_int} : Int.int semiring;

val semiring_0_int = {comm_monoid_add_semiring_0 = comm_monoid_add_int, mult_zero_semiring_0 = mult_zero_int, semiring_semiring_0 = semiring_int} : Int.int semiring_0;

val semiring_0_cancel_int = {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_int, semiring_0_semiring_0_cancel = semiring_0_int} : Int.int semiring_0_cancel;

val ab_semigroup_mult_int = {semigroup_mult_ab_semigroup_mult = semigroup_mult_int} : Int.int ab_semigroup_mult;

val comm_semiring_int = {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_int, semiring_comm_semiring = semiring_int} : Int.int comm_semiring;

val comm_semiring_0_int = {comm_semiring_comm_semiring_0 = comm_semiring_int, semiring_0_comm_semiring_0 = semiring_0_int} : Int.int comm_semiring_0;

val comm_semiring_0_cancel_int = {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_int, semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_int} : Int.int comm_semiring_0_cancel;

val power_int = {one_power = one_int, times_power = times_int} : Int.int power;

val monoid_mult_int = {semigroup_mult_monoid_mult = semigroup_mult_int, power_monoid_mult = power_int} : Int.int monoid_mult;

val numeral_int = {one_numeral = one_int, semigroup_add_numeral = semigroup_add_int} : Int.int numeral;

val semiring_numeral_int = {monoid_mult_semiring_numeral = monoid_mult_int, numeral_semiring_numeral = numeral_int, semiring_semiring_numeral = semiring_int} : Int.int semiring_numeral;

val zero_neq_one_int = {one_zero_neq_one = one_int, zero_zero_neq_one = zero_int} : Int.int zero_neq_one;

val semiring_1_int = {semiring_numeral_semiring_1 = semiring_numeral_int, semiring_0_semiring_1 = semiring_0_int, zero_neq_one_semiring_1 = zero_neq_one_int} : Int.int semiring_1;

val semiring_1_cancel_int = {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_int, semiring_1_semiring_1_cancel = semiring_1_int} : Int.int semiring_1_cancel;

val comm_monoid_mult_int = {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_int, monoid_mult_comm_monoid_mult = monoid_mult_int, dvd_comm_monoid_mult = dvd_int} : Int.int comm_monoid_mult;

val comm_semiring_1_int = {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_int, comm_semiring_0_comm_semiring_1 = comm_semiring_0_int, semiring_1_comm_semiring_1 = semiring_1_int} : Int.int comm_semiring_1;

val comm_semiring_1_cancel_int = {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_int, comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_int, semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_int} : Int.int comm_semiring_1_cancel;

val comm_semiring_1_cancel_crossproduct_int = {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct = comm_semiring_1_cancel_int} : Int.int comm_semiring_1_cancel_crossproduct;

val semiring_no_zero_divisors_int = {semiring_0_semiring_no_zero_divisors = semiring_0_int} : Int.int semiring_no_zero_divisors;

val semiring_1_no_zero_divisors_int = {semiring_1_semiring_1_no_zero_divisors = semiring_1_int, semiring_no_zero_divisors_semiring_1_no_zero_divisors = semiring_no_zero_divisors_int} : Int.int semiring_1_no_zero_divisors;

val semiring_no_zero_divisors_cancel_int = {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel = semiring_no_zero_divisors_int} : Int.int semiring_no_zero_divisors_cancel;

val uminus_int = {uminus = Int.~} : Int.int uminus;

val group_add_int = {cancel_semigroup_add_group_add = cancel_semigroup_add_int, minus_group_add = minus_int, monoid_add_group_add = monoid_add_int, uminus_group_add = uminus_int} : Int.int group_add;

val ab_group_add_int = {cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int, group_add_ab_group_add = group_add_int} : Int.int ab_group_add;

val ring_int = {ab_group_add_ring = ab_group_add_int, semiring_0_cancel_ring = semiring_0_cancel_int} : Int.int ring;

val ring_no_zero_divisors_int = {ring_ring_no_zero_divisors = ring_int, semiring_no_zero_divisors_cancel_ring_no_zero_divisors = semiring_no_zero_divisors_cancel_int} : Int.int ring_no_zero_divisors;

val neg_numeral_int = {group_add_neg_numeral = group_add_int, numeral_neg_numeral = numeral_int} : Int.int neg_numeral;

val ring_1_int = {neg_numeral_ring_1 = neg_numeral_int, ring_ring_1 = ring_int, semiring_1_cancel_ring_1 = semiring_1_cancel_int} : Int.int ring_1;

val ring_1_no_zero_divisors_int = {ring_1_ring_1_no_zero_divisors = ring_1_int, ring_no_zero_divisors_ring_1_no_zero_divisors = ring_no_zero_divisors_int, semiring_1_no_zero_divisors_ring_1_no_zero_divisors = semiring_1_no_zero_divisors_int} : Int.int ring_1_no_zero_divisors;

val comm_ring_int = {comm_semiring_0_cancel_comm_ring = comm_semiring_0_cancel_int, ring_comm_ring = ring_int} : Int.int comm_ring;

val comm_ring_1_int = {comm_ring_comm_ring_1 = comm_ring_int, comm_semiring_1_cancel_comm_ring_1 = comm_semiring_1_cancel_int, ring_1_comm_ring_1 = ring_1_int} : Int.int comm_ring_1;

val semidom_int = {comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_int, semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_int} : Int.int semidom;

val idom_int = {comm_ring_1_idom = comm_ring_1_int, ring_1_no_zero_divisors_idom = ring_1_no_zero_divisors_int, semidom_idom = semidom_int, comm_semiring_1_cancel_crossproduct_idom = comm_semiring_1_cancel_crossproduct_int} : Int.int idom;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

type 'a abs_if = {abs_abs_if : 'a abs, minus_abs_if : 'a minus, uminus_abs_if : 'a uminus, zero_abs_if : 'a zero, ord_abs_if : 'a ord};
val abs_abs_if = #abs_abs_if : 'a abs_if -> 'a abs;
val minus_abs_if = #minus_abs_if : 'a abs_if -> 'a minus;
val uminus_abs_if = #uminus_abs_if : 'a abs_if -> 'a uminus;
val zero_abs_if = #zero_abs_if : 'a abs_if -> 'a zero;
val ord_abs_if = #ord_abs_if : 'a abs_if -> 'a ord;

val ord_int = {less_eq = (fn a => fn b => Int.<= (a, b)), less = (fn a => fn b => Int.< (a, b))} : Int.int ord;

val abs_if_int = {abs_abs_if = abs_int, minus_abs_if = minus_int, uminus_abs_if = uminus_int, zero_abs_if = zero_int, ord_abs_if = ord_int} : Int.int abs_if;

type 'a semiring_char_0 = {semiring_1_semiring_char_0 : 'a semiring_1};
val semiring_1_semiring_char_0 = #semiring_1_semiring_char_0 : 'a semiring_char_0 -> 'a semiring_1;

type 'a ring_char_0 = {semiring_char_0_ring_char_0 : 'a semiring_char_0, ring_1_ring_char_0 : 'a ring_1};
val semiring_char_0_ring_char_0 = #semiring_char_0_ring_char_0 : 'a ring_char_0 -> 'a semiring_char_0;
val ring_1_ring_char_0 = #ring_1_ring_char_0 : 'a ring_char_0 -> 'a ring_1;

val semiring_char_0_int = {semiring_1_semiring_char_0 = semiring_1_int} : Int.int semiring_char_0;

val ring_char_0_int = {semiring_char_0_ring_char_0 = semiring_char_0_int, ring_1_ring_char_0 = ring_1_int} : Int.int ring_char_0;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_int = {ord_preorder = ord_int} : Int.int preorder;

val order_int = {preorder_order = preorder_int} : Int.int order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_int = {order_linorder = order_int} : Int.int linorder;

type 'a idom_abs_sgn = {abs_idom_abs_sgn : 'a abs, sgn_idom_abs_sgn : 'a sgn, idom_idom_abs_sgn : 'a idom};
val abs_idom_abs_sgn = #abs_idom_abs_sgn : 'a idom_abs_sgn -> 'a abs;
val sgn_idom_abs_sgn = #sgn_idom_abs_sgn : 'a idom_abs_sgn -> 'a sgn;
val idom_idom_abs_sgn = #idom_idom_abs_sgn : 'a idom_abs_sgn -> 'a idom;

val idom_abs_sgn_int = {abs_idom_abs_sgn = abs_int, sgn_idom_abs_sgn = sgn_int, idom_idom_abs_sgn = idom_int} : Int.int idom_abs_sgn;

type 'a ordered_ab_semigroup_add = {ab_semigroup_add_ordered_ab_semigroup_add : 'a ab_semigroup_add, order_ordered_ab_semigroup_add : 'a order};
val ab_semigroup_add_ordered_ab_semigroup_add = #ab_semigroup_add_ordered_ab_semigroup_add : 'a ordered_ab_semigroup_add -> 'a ab_semigroup_add;
val order_ordered_ab_semigroup_add = #order_ordered_ab_semigroup_add : 'a ordered_ab_semigroup_add -> 'a order;

type 'a strict_ordered_ab_semigroup_add = {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add : 'a ordered_ab_semigroup_add};
val ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add = #ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add : 'a strict_ordered_ab_semigroup_add -> 'a ordered_ab_semigroup_add;

type 'a ordered_cancel_ab_semigroup_add = {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add : 'a cancel_ab_semigroup_add, strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add : 'a strict_ordered_ab_semigroup_add};
val cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add = #cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add : 'a ordered_cancel_ab_semigroup_add -> 'a cancel_ab_semigroup_add;
val strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add = #strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add : 'a ordered_cancel_ab_semigroup_add -> 'a strict_ordered_ab_semigroup_add;

type 'a ordered_comm_monoid_add = {comm_monoid_add_ordered_comm_monoid_add : 'a comm_monoid_add, ordered_ab_semigroup_add_ordered_comm_monoid_add : 'a ordered_ab_semigroup_add};
val comm_monoid_add_ordered_comm_monoid_add = #comm_monoid_add_ordered_comm_monoid_add : 'a ordered_comm_monoid_add -> 'a comm_monoid_add;
val ordered_ab_semigroup_add_ordered_comm_monoid_add = #ordered_ab_semigroup_add_ordered_comm_monoid_add : 'a ordered_comm_monoid_add -> 'a ordered_ab_semigroup_add;

type 'a ordered_semiring = {ordered_comm_monoid_add_ordered_semiring : 'a ordered_comm_monoid_add, semiring_ordered_semiring : 'a semiring};
val ordered_comm_monoid_add_ordered_semiring = #ordered_comm_monoid_add_ordered_semiring : 'a ordered_semiring -> 'a ordered_comm_monoid_add;
val semiring_ordered_semiring = #semiring_ordered_semiring : 'a ordered_semiring -> 'a semiring;

type 'a ordered_semiring_0 = {ordered_semiring_ordered_semiring_0 : 'a ordered_semiring, semiring_0_ordered_semiring_0 : 'a semiring_0};
val ordered_semiring_ordered_semiring_0 = #ordered_semiring_ordered_semiring_0 : 'a ordered_semiring_0 -> 'a ordered_semiring;
val semiring_0_ordered_semiring_0 = #semiring_0_ordered_semiring_0 : 'a ordered_semiring_0 -> 'a semiring_0;

type 'a ordered_cancel_semiring = {ordered_cancel_ab_semigroup_add_ordered_cancel_semiring : 'a ordered_cancel_ab_semigroup_add, ordered_semiring_0_ordered_cancel_semiring : 'a ordered_semiring_0, semiring_0_cancel_ordered_cancel_semiring : 'a semiring_0_cancel};
val ordered_cancel_ab_semigroup_add_ordered_cancel_semiring = #ordered_cancel_ab_semigroup_add_ordered_cancel_semiring : 'a ordered_cancel_semiring -> 'a ordered_cancel_ab_semigroup_add;
val ordered_semiring_0_ordered_cancel_semiring = #ordered_semiring_0_ordered_cancel_semiring : 'a ordered_cancel_semiring -> 'a ordered_semiring_0;
val semiring_0_cancel_ordered_cancel_semiring = #semiring_0_cancel_ordered_cancel_semiring : 'a ordered_cancel_semiring -> 'a semiring_0_cancel;

type 'a ordered_ab_semigroup_add_imp_le = {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le : 'a ordered_cancel_ab_semigroup_add};
val ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le = #ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le : 'a ordered_ab_semigroup_add_imp_le -> 'a ordered_cancel_ab_semigroup_add;

type 'a strict_ordered_comm_monoid_add = {comm_monoid_add_strict_ordered_comm_monoid_add : 'a comm_monoid_add, strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add : 'a strict_ordered_ab_semigroup_add};
val comm_monoid_add_strict_ordered_comm_monoid_add = #comm_monoid_add_strict_ordered_comm_monoid_add : 'a strict_ordered_comm_monoid_add -> 'a comm_monoid_add;
val strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add = #strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add : 'a strict_ordered_comm_monoid_add -> 'a strict_ordered_ab_semigroup_add;

type 'a ordered_cancel_comm_monoid_add = {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add : 'a ordered_cancel_ab_semigroup_add, ordered_comm_monoid_add_ordered_cancel_comm_monoid_add : 'a ordered_comm_monoid_add, strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add : 'a strict_ordered_comm_monoid_add};
val ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add = #ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add : 'a ordered_cancel_comm_monoid_add -> 'a ordered_cancel_ab_semigroup_add;
val ordered_comm_monoid_add_ordered_cancel_comm_monoid_add = #ordered_comm_monoid_add_ordered_cancel_comm_monoid_add : 'a ordered_cancel_comm_monoid_add -> 'a ordered_comm_monoid_add;
val strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add = #strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add : 'a ordered_cancel_comm_monoid_add -> 'a strict_ordered_comm_monoid_add;

type 'a ordered_ab_semigroup_monoid_add_imp_le = {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le : 'a cancel_comm_monoid_add, ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le : 'a ordered_ab_semigroup_add_imp_le, ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le : 'a ordered_cancel_comm_monoid_add};
val cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le = #cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le : 'a ordered_ab_semigroup_monoid_add_imp_le -> 'a cancel_comm_monoid_add;
val ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le = #ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le : 'a ordered_ab_semigroup_monoid_add_imp_le -> 'a ordered_ab_semigroup_add_imp_le;
val ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le = #ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le : 'a ordered_ab_semigroup_monoid_add_imp_le -> 'a ordered_cancel_comm_monoid_add;

type 'a ordered_ab_group_add = {ab_group_add_ordered_ab_group_add : 'a ab_group_add, ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add : 'a ordered_ab_semigroup_monoid_add_imp_le};
val ab_group_add_ordered_ab_group_add = #ab_group_add_ordered_ab_group_add : 'a ordered_ab_group_add -> 'a ab_group_add;
val ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add = #ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add : 'a ordered_ab_group_add -> 'a ordered_ab_semigroup_monoid_add_imp_le;

type 'a ordered_ring = {ordered_ab_group_add_ordered_ring : 'a ordered_ab_group_add, ordered_cancel_semiring_ordered_ring : 'a ordered_cancel_semiring, ring_ordered_ring : 'a ring};
val ordered_ab_group_add_ordered_ring = #ordered_ab_group_add_ordered_ring : 'a ordered_ring -> 'a ordered_ab_group_add;
val ordered_cancel_semiring_ordered_ring = #ordered_cancel_semiring_ordered_ring : 'a ordered_ring -> 'a ordered_cancel_semiring;
val ring_ordered_ring = #ring_ordered_ring : 'a ordered_ring -> 'a ring;

val ordered_ab_semigroup_add_int = {ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_int, order_ordered_ab_semigroup_add = order_int} : Int.int ordered_ab_semigroup_add;

val strict_ordered_ab_semigroup_add_int = {ordered_ab_semigroup_add_strict_ordered_ab_semigroup_add = ordered_ab_semigroup_add_int} : Int.int strict_ordered_ab_semigroup_add;

val ordered_cancel_ab_semigroup_add_int = {cancel_ab_semigroup_add_ordered_cancel_ab_semigroup_add = cancel_ab_semigroup_add_int, strict_ordered_ab_semigroup_add_ordered_cancel_ab_semigroup_add = strict_ordered_ab_semigroup_add_int} : Int.int ordered_cancel_ab_semigroup_add;

val ordered_comm_monoid_add_int = {comm_monoid_add_ordered_comm_monoid_add = comm_monoid_add_int, ordered_ab_semigroup_add_ordered_comm_monoid_add = ordered_ab_semigroup_add_int} : Int.int ordered_comm_monoid_add;

val ordered_semiring_int = {ordered_comm_monoid_add_ordered_semiring = ordered_comm_monoid_add_int, semiring_ordered_semiring = semiring_int} : Int.int ordered_semiring;

val ordered_semiring_0_int = {ordered_semiring_ordered_semiring_0 = ordered_semiring_int, semiring_0_ordered_semiring_0 = semiring_0_int} : Int.int ordered_semiring_0;

val ordered_cancel_semiring_int = {ordered_cancel_ab_semigroup_add_ordered_cancel_semiring = ordered_cancel_ab_semigroup_add_int, ordered_semiring_0_ordered_cancel_semiring = ordered_semiring_0_int, semiring_0_cancel_ordered_cancel_semiring = semiring_0_cancel_int} : Int.int ordered_cancel_semiring;

val ordered_ab_semigroup_add_imp_le_int = {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le = ordered_cancel_ab_semigroup_add_int} : Int.int ordered_ab_semigroup_add_imp_le;

val strict_ordered_comm_monoid_add_int = {comm_monoid_add_strict_ordered_comm_monoid_add = comm_monoid_add_int, strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add = strict_ordered_ab_semigroup_add_int} : Int.int strict_ordered_comm_monoid_add;

val ordered_cancel_comm_monoid_add_int = {ordered_cancel_ab_semigroup_add_ordered_cancel_comm_monoid_add = ordered_cancel_ab_semigroup_add_int, ordered_comm_monoid_add_ordered_cancel_comm_monoid_add = ordered_comm_monoid_add_int, strict_ordered_comm_monoid_add_ordered_cancel_comm_monoid_add = strict_ordered_comm_monoid_add_int} : Int.int ordered_cancel_comm_monoid_add;

val ordered_ab_semigroup_monoid_add_imp_le_int = {cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le = cancel_comm_monoid_add_int, ordered_ab_semigroup_add_imp_le_ordered_ab_semigroup_monoid_add_imp_le = ordered_ab_semigroup_add_imp_le_int, ordered_cancel_comm_monoid_add_ordered_ab_semigroup_monoid_add_imp_le = ordered_cancel_comm_monoid_add_int} : Int.int ordered_ab_semigroup_monoid_add_imp_le;

val ordered_ab_group_add_int = {ab_group_add_ordered_ab_group_add = ab_group_add_int, ordered_ab_semigroup_monoid_add_imp_le_ordered_ab_group_add = ordered_ab_semigroup_monoid_add_imp_le_int} : Int.int ordered_ab_group_add;

val ordered_ring_int = {ordered_ab_group_add_ordered_ring = ordered_ab_group_add_int, ordered_cancel_semiring_ordered_ring = ordered_cancel_semiring_int, ring_ordered_ring = ring_int} : Int.int ordered_ring;

type 'a zero_less_one = {order_zero_less_one : 'a order, zero_neq_one_zero_less_one : 'a zero_neq_one};
val order_zero_less_one = #order_zero_less_one : 'a zero_less_one -> 'a order;
val zero_neq_one_zero_less_one = #zero_neq_one_zero_less_one : 'a zero_less_one -> 'a zero_neq_one;

val zero_less_one_int = {order_zero_less_one = order_int, zero_neq_one_zero_less_one = zero_neq_one_int} : Int.int zero_less_one;

type 'a ordered_semiring_strict = {ordered_cancel_ab_semigroup_add_ordered_semiring_strict : 'a ordered_cancel_ab_semigroup_add, ordered_semiring_ordered_semiring_strict : 'a ordered_semiring, semiring_0_cancel_ordered_semiring_strict : 'a semiring_0_cancel};
val ordered_cancel_ab_semigroup_add_ordered_semiring_strict = #ordered_cancel_ab_semigroup_add_ordered_semiring_strict : 'a ordered_semiring_strict -> 'a ordered_cancel_ab_semigroup_add;
val ordered_semiring_ordered_semiring_strict = #ordered_semiring_ordered_semiring_strict : 'a ordered_semiring_strict -> 'a ordered_semiring;
val semiring_0_cancel_ordered_semiring_strict = #semiring_0_cancel_ordered_semiring_strict : 'a ordered_semiring_strict -> 'a semiring_0_cancel;

type 'a linordered_ab_semigroup_add = {ordered_ab_semigroup_add_linordered_ab_semigroup_add : 'a ordered_ab_semigroup_add, linorder_linordered_ab_semigroup_add : 'a linorder};
val ordered_ab_semigroup_add_linordered_ab_semigroup_add = #ordered_ab_semigroup_add_linordered_ab_semigroup_add : 'a linordered_ab_semigroup_add -> 'a ordered_ab_semigroup_add;
val linorder_linordered_ab_semigroup_add = #linorder_linordered_ab_semigroup_add : 'a linordered_ab_semigroup_add -> 'a linorder;

type 'a linordered_cancel_ab_semigroup_add = {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add : 'a linordered_ab_semigroup_add, ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add : 'a ordered_ab_semigroup_add_imp_le};
val linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add = #linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add : 'a linordered_cancel_ab_semigroup_add -> 'a linordered_ab_semigroup_add;
val ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add = #ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add : 'a linordered_cancel_ab_semigroup_add -> 'a ordered_ab_semigroup_add_imp_le;

type 'a linordered_semiring = {linordered_cancel_ab_semigroup_add_linordered_semiring : 'a linordered_cancel_ab_semigroup_add, ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring : 'a ordered_ab_semigroup_monoid_add_imp_le, ordered_cancel_semiring_linordered_semiring : 'a ordered_cancel_semiring};
val linordered_cancel_ab_semigroup_add_linordered_semiring = #linordered_cancel_ab_semigroup_add_linordered_semiring : 'a linordered_semiring -> 'a linordered_cancel_ab_semigroup_add;
val ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring = #ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring : 'a linordered_semiring -> 'a ordered_ab_semigroup_monoid_add_imp_le;
val ordered_cancel_semiring_linordered_semiring = #ordered_cancel_semiring_linordered_semiring : 'a linordered_semiring -> 'a ordered_cancel_semiring;

type 'a linordered_semiring_strict = {linordered_semiring_linordered_semiring_strict : 'a linordered_semiring, ordered_semiring_strict_linordered_semiring_strict : 'a ordered_semiring_strict};
val linordered_semiring_linordered_semiring_strict = #linordered_semiring_linordered_semiring_strict : 'a linordered_semiring_strict -> 'a linordered_semiring;
val ordered_semiring_strict_linordered_semiring_strict = #ordered_semiring_strict_linordered_semiring_strict : 'a linordered_semiring_strict -> 'a ordered_semiring_strict;

type 'a ordered_semiring_1 = {ordered_semiring_0_ordered_semiring_1 : 'a ordered_semiring_0, semiring_1_ordered_semiring_1 : 'a semiring_1, zero_less_one_ordered_semiring_1 : 'a zero_less_one};
val ordered_semiring_0_ordered_semiring_1 = #ordered_semiring_0_ordered_semiring_1 : 'a ordered_semiring_1 -> 'a ordered_semiring_0;
val semiring_1_ordered_semiring_1 = #semiring_1_ordered_semiring_1 : 'a ordered_semiring_1 -> 'a semiring_1;
val zero_less_one_ordered_semiring_1 = #zero_less_one_ordered_semiring_1 : 'a ordered_semiring_1 -> 'a zero_less_one;

type 'a ordered_semiring_1_strict = {ordered_semiring_1_ordered_semiring_1_strict : 'a ordered_semiring_1, ordered_semiring_strict_ordered_semiring_1_strict : 'a ordered_semiring_strict};
val ordered_semiring_1_ordered_semiring_1_strict = #ordered_semiring_1_ordered_semiring_1_strict : 'a ordered_semiring_1_strict -> 'a ordered_semiring_1;
val ordered_semiring_strict_ordered_semiring_1_strict = #ordered_semiring_strict_ordered_semiring_1_strict : 'a ordered_semiring_1_strict -> 'a ordered_semiring_strict;

type 'a linordered_semiring_1 = {linordered_semiring_linordered_semiring_1 : 'a linordered_semiring, ordered_semiring_1_linordered_semiring_1 : 'a ordered_semiring_1};
val linordered_semiring_linordered_semiring_1 = #linordered_semiring_linordered_semiring_1 : 'a linordered_semiring_1 -> 'a linordered_semiring;
val ordered_semiring_1_linordered_semiring_1 = #ordered_semiring_1_linordered_semiring_1 : 'a linordered_semiring_1 -> 'a ordered_semiring_1;

type 'a linordered_semiring_1_strict = {linordered_semiring_1_linordered_semiring_1_strict : 'a linordered_semiring_1, linordered_semiring_strict_linordered_semiring_1_strict : 'a linordered_semiring_strict, ordered_semiring_1_strict_linordered_semiring_1_strict : 'a ordered_semiring_1_strict};
val linordered_semiring_1_linordered_semiring_1_strict = #linordered_semiring_1_linordered_semiring_1_strict : 'a linordered_semiring_1_strict -> 'a linordered_semiring_1;
val linordered_semiring_strict_linordered_semiring_1_strict = #linordered_semiring_strict_linordered_semiring_1_strict : 'a linordered_semiring_1_strict -> 'a linordered_semiring_strict;
val ordered_semiring_1_strict_linordered_semiring_1_strict = #ordered_semiring_1_strict_linordered_semiring_1_strict : 'a linordered_semiring_1_strict -> 'a ordered_semiring_1_strict;

type 'a ordered_ab_group_add_abs = {abs_ordered_ab_group_add_abs : 'a abs, ordered_ab_group_add_ordered_ab_group_add_abs : 'a ordered_ab_group_add};
val abs_ordered_ab_group_add_abs = #abs_ordered_ab_group_add_abs : 'a ordered_ab_group_add_abs -> 'a abs;
val ordered_ab_group_add_ordered_ab_group_add_abs = #ordered_ab_group_add_ordered_ab_group_add_abs : 'a ordered_ab_group_add_abs -> 'a ordered_ab_group_add;

type 'a linordered_ab_group_add = {linordered_cancel_ab_semigroup_add_linordered_ab_group_add : 'a linordered_cancel_ab_semigroup_add, ordered_ab_group_add_linordered_ab_group_add : 'a ordered_ab_group_add};
val linordered_cancel_ab_semigroup_add_linordered_ab_group_add = #linordered_cancel_ab_semigroup_add_linordered_ab_group_add : 'a linordered_ab_group_add -> 'a linordered_cancel_ab_semigroup_add;
val ordered_ab_group_add_linordered_ab_group_add = #ordered_ab_group_add_linordered_ab_group_add : 'a linordered_ab_group_add -> 'a ordered_ab_group_add;

type 'a linordered_ring = {linordered_ab_group_add_linordered_ring : 'a linordered_ab_group_add, ordered_ab_group_add_abs_linordered_ring : 'a ordered_ab_group_add_abs, abs_if_linordered_ring : 'a abs_if, linordered_semiring_linordered_ring : 'a linordered_semiring, ordered_ring_linordered_ring : 'a ordered_ring};
val linordered_ab_group_add_linordered_ring = #linordered_ab_group_add_linordered_ring : 'a linordered_ring -> 'a linordered_ab_group_add;
val ordered_ab_group_add_abs_linordered_ring = #ordered_ab_group_add_abs_linordered_ring : 'a linordered_ring -> 'a ordered_ab_group_add_abs;
val abs_if_linordered_ring = #abs_if_linordered_ring : 'a linordered_ring -> 'a abs_if;
val linordered_semiring_linordered_ring = #linordered_semiring_linordered_ring : 'a linordered_ring -> 'a linordered_semiring;
val ordered_ring_linordered_ring = #ordered_ring_linordered_ring : 'a linordered_ring -> 'a ordered_ring;

type 'a linordered_ring_strict = {linordered_ring_linordered_ring_strict : 'a linordered_ring, linordered_semiring_strict_linordered_ring_strict : 'a linordered_semiring_strict, ring_no_zero_divisors_linordered_ring_strict : 'a ring_no_zero_divisors};
val linordered_ring_linordered_ring_strict = #linordered_ring_linordered_ring_strict : 'a linordered_ring_strict -> 'a linordered_ring;
val linordered_semiring_strict_linordered_ring_strict = #linordered_semiring_strict_linordered_ring_strict : 'a linordered_ring_strict -> 'a linordered_semiring_strict;
val ring_no_zero_divisors_linordered_ring_strict = #ring_no_zero_divisors_linordered_ring_strict : 'a linordered_ring_strict -> 'a ring_no_zero_divisors;

type 'a ordered_comm_semiring = {comm_semiring_0_ordered_comm_semiring : 'a comm_semiring_0, ordered_semiring_ordered_comm_semiring : 'a ordered_semiring};
val comm_semiring_0_ordered_comm_semiring = #comm_semiring_0_ordered_comm_semiring : 'a ordered_comm_semiring -> 'a comm_semiring_0;
val ordered_semiring_ordered_comm_semiring = #ordered_semiring_ordered_comm_semiring : 'a ordered_comm_semiring -> 'a ordered_semiring;

type 'a ordered_cancel_comm_semiring = {comm_semiring_0_cancel_ordered_cancel_comm_semiring : 'a comm_semiring_0_cancel, ordered_cancel_semiring_ordered_cancel_comm_semiring : 'a ordered_cancel_semiring, ordered_comm_semiring_ordered_cancel_comm_semiring : 'a ordered_comm_semiring};
val comm_semiring_0_cancel_ordered_cancel_comm_semiring = #comm_semiring_0_cancel_ordered_cancel_comm_semiring : 'a ordered_cancel_comm_semiring -> 'a comm_semiring_0_cancel;
val ordered_cancel_semiring_ordered_cancel_comm_semiring = #ordered_cancel_semiring_ordered_cancel_comm_semiring : 'a ordered_cancel_comm_semiring -> 'a ordered_cancel_semiring;
val ordered_comm_semiring_ordered_cancel_comm_semiring = #ordered_comm_semiring_ordered_cancel_comm_semiring : 'a ordered_cancel_comm_semiring -> 'a ordered_comm_semiring;

type 'a ordered_comm_semiring_strict = {ordered_cancel_comm_semiring_ordered_comm_semiring_strict : 'a ordered_cancel_comm_semiring, ordered_semiring_strict_ordered_comm_semiring_strict : 'a ordered_semiring_strict};
val ordered_cancel_comm_semiring_ordered_comm_semiring_strict = #ordered_cancel_comm_semiring_ordered_comm_semiring_strict : 'a ordered_comm_semiring_strict -> 'a ordered_cancel_comm_semiring;
val ordered_semiring_strict_ordered_comm_semiring_strict = #ordered_semiring_strict_ordered_comm_semiring_strict : 'a ordered_comm_semiring_strict -> 'a ordered_semiring_strict;

type 'a linordered_comm_semiring_strict = {linordered_semiring_strict_linordered_comm_semiring_strict : 'a linordered_semiring_strict, ordered_comm_semiring_strict_linordered_comm_semiring_strict : 'a ordered_comm_semiring_strict};
val linordered_semiring_strict_linordered_comm_semiring_strict = #linordered_semiring_strict_linordered_comm_semiring_strict : 'a linordered_comm_semiring_strict -> 'a linordered_semiring_strict;
val ordered_comm_semiring_strict_linordered_comm_semiring_strict = #ordered_comm_semiring_strict_linordered_comm_semiring_strict : 'a linordered_comm_semiring_strict -> 'a ordered_comm_semiring_strict;

type 'a linordered_nonzero_semiring = {semiring_char_0_linordered_nonzero_semiring : 'a semiring_char_0, linorder_linordered_nonzero_semiring : 'a linorder, comm_semiring_1_linordered_nonzero_semiring : 'a comm_semiring_1, ordered_comm_semiring_linordered_nonzero_semiring : 'a ordered_comm_semiring, ordered_semiring_1_linordered_nonzero_semiring : 'a ordered_semiring_1};
val semiring_char_0_linordered_nonzero_semiring = #semiring_char_0_linordered_nonzero_semiring : 'a linordered_nonzero_semiring -> 'a semiring_char_0;
val linorder_linordered_nonzero_semiring = #linorder_linordered_nonzero_semiring : 'a linordered_nonzero_semiring -> 'a linorder;
val comm_semiring_1_linordered_nonzero_semiring = #comm_semiring_1_linordered_nonzero_semiring : 'a linordered_nonzero_semiring -> 'a comm_semiring_1;
val ordered_comm_semiring_linordered_nonzero_semiring = #ordered_comm_semiring_linordered_nonzero_semiring : 'a linordered_nonzero_semiring -> 'a ordered_comm_semiring;
val ordered_semiring_1_linordered_nonzero_semiring = #ordered_semiring_1_linordered_nonzero_semiring : 'a linordered_nonzero_semiring -> 'a ordered_semiring_1;

type 'a linordered_semidom = {linordered_comm_semiring_strict_linordered_semidom : 'a linordered_comm_semiring_strict, linordered_nonzero_semiring_linordered_semidom : 'a linordered_nonzero_semiring, semidom_linordered_semidom : 'a semidom};
val linordered_comm_semiring_strict_linordered_semidom = #linordered_comm_semiring_strict_linordered_semidom : 'a linordered_semidom -> 'a linordered_comm_semiring_strict;
val linordered_nonzero_semiring_linordered_semidom = #linordered_nonzero_semiring_linordered_semidom : 'a linordered_semidom -> 'a linordered_nonzero_semiring;
val semidom_linordered_semidom = #semidom_linordered_semidom : 'a linordered_semidom -> 'a semidom;

type 'a ordered_comm_ring = {comm_ring_ordered_comm_ring : 'a comm_ring, ordered_cancel_comm_semiring_ordered_comm_ring : 'a ordered_cancel_comm_semiring, ordered_ring_ordered_comm_ring : 'a ordered_ring};
val comm_ring_ordered_comm_ring = #comm_ring_ordered_comm_ring : 'a ordered_comm_ring -> 'a comm_ring;
val ordered_cancel_comm_semiring_ordered_comm_ring = #ordered_cancel_comm_semiring_ordered_comm_ring : 'a ordered_comm_ring -> 'a ordered_cancel_comm_semiring;
val ordered_ring_ordered_comm_ring = #ordered_ring_ordered_comm_ring : 'a ordered_comm_ring -> 'a ordered_ring;

type 'a ordered_ring_abs = {ordered_ab_group_add_abs_ordered_ring_abs : 'a ordered_ab_group_add_abs, ordered_ring_ordered_ring_abs : 'a ordered_ring};
val ordered_ab_group_add_abs_ordered_ring_abs = #ordered_ab_group_add_abs_ordered_ring_abs : 'a ordered_ring_abs -> 'a ordered_ab_group_add_abs;
val ordered_ring_ordered_ring_abs = #ordered_ring_ordered_ring_abs : 'a ordered_ring_abs -> 'a ordered_ring;

type 'a linordered_idom = {ring_char_0_linordered_idom : 'a ring_char_0, idom_abs_sgn_linordered_idom : 'a idom_abs_sgn, linordered_ring_strict_linordered_idom : 'a linordered_ring_strict, linordered_semidom_linordered_idom : 'a linordered_semidom, linordered_semiring_1_strict_linordered_idom : 'a linordered_semiring_1_strict, ordered_comm_ring_linordered_idom : 'a ordered_comm_ring, ordered_ring_abs_linordered_idom : 'a ordered_ring_abs};
val ring_char_0_linordered_idom = #ring_char_0_linordered_idom : 'a linordered_idom -> 'a ring_char_0;
val idom_abs_sgn_linordered_idom = #idom_abs_sgn_linordered_idom : 'a linordered_idom -> 'a idom_abs_sgn;
val linordered_ring_strict_linordered_idom = #linordered_ring_strict_linordered_idom : 'a linordered_idom -> 'a linordered_ring_strict;
val linordered_semidom_linordered_idom = #linordered_semidom_linordered_idom : 'a linordered_idom -> 'a linordered_semidom;
val linordered_semiring_1_strict_linordered_idom = #linordered_semiring_1_strict_linordered_idom : 'a linordered_idom -> 'a linordered_semiring_1_strict;
val ordered_comm_ring_linordered_idom = #ordered_comm_ring_linordered_idom : 'a linordered_idom -> 'a ordered_comm_ring;
val ordered_ring_abs_linordered_idom = #ordered_ring_abs_linordered_idom : 'a linordered_idom -> 'a ordered_ring_abs;

val ordered_semiring_strict_int = {ordered_cancel_ab_semigroup_add_ordered_semiring_strict = ordered_cancel_ab_semigroup_add_int, ordered_semiring_ordered_semiring_strict = ordered_semiring_int, semiring_0_cancel_ordered_semiring_strict = semiring_0_cancel_int} : Int.int ordered_semiring_strict;

val linordered_ab_semigroup_add_int = {ordered_ab_semigroup_add_linordered_ab_semigroup_add = ordered_ab_semigroup_add_int, linorder_linordered_ab_semigroup_add = linorder_int} : Int.int linordered_ab_semigroup_add;

val linordered_cancel_ab_semigroup_add_int = {linordered_ab_semigroup_add_linordered_cancel_ab_semigroup_add = linordered_ab_semigroup_add_int, ordered_ab_semigroup_add_imp_le_linordered_cancel_ab_semigroup_add = ordered_ab_semigroup_add_imp_le_int} : Int.int linordered_cancel_ab_semigroup_add;

val linordered_semiring_int = {linordered_cancel_ab_semigroup_add_linordered_semiring = linordered_cancel_ab_semigroup_add_int, ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring = ordered_ab_semigroup_monoid_add_imp_le_int, ordered_cancel_semiring_linordered_semiring = ordered_cancel_semiring_int} : Int.int linordered_semiring;

val linordered_semiring_strict_int = {linordered_semiring_linordered_semiring_strict = linordered_semiring_int, ordered_semiring_strict_linordered_semiring_strict = ordered_semiring_strict_int} : Int.int linordered_semiring_strict;

val ordered_semiring_1_int = {ordered_semiring_0_ordered_semiring_1 = ordered_semiring_0_int, semiring_1_ordered_semiring_1 = semiring_1_int, zero_less_one_ordered_semiring_1 = zero_less_one_int} : Int.int ordered_semiring_1;

val ordered_semiring_1_strict_int = {ordered_semiring_1_ordered_semiring_1_strict = ordered_semiring_1_int, ordered_semiring_strict_ordered_semiring_1_strict = ordered_semiring_strict_int} : Int.int ordered_semiring_1_strict;

val linordered_semiring_1_int = {linordered_semiring_linordered_semiring_1 = linordered_semiring_int, ordered_semiring_1_linordered_semiring_1 = ordered_semiring_1_int} : Int.int linordered_semiring_1;

val linordered_semiring_1_strict_int = {linordered_semiring_1_linordered_semiring_1_strict = linordered_semiring_1_int, linordered_semiring_strict_linordered_semiring_1_strict = linordered_semiring_strict_int, ordered_semiring_1_strict_linordered_semiring_1_strict = ordered_semiring_1_strict_int} : Int.int linordered_semiring_1_strict;

val ordered_ab_group_add_abs_int = {abs_ordered_ab_group_add_abs = abs_int, ordered_ab_group_add_ordered_ab_group_add_abs = ordered_ab_group_add_int} : Int.int ordered_ab_group_add_abs;

val linordered_ab_group_add_int = {linordered_cancel_ab_semigroup_add_linordered_ab_group_add = linordered_cancel_ab_semigroup_add_int, ordered_ab_group_add_linordered_ab_group_add = ordered_ab_group_add_int} : Int.int linordered_ab_group_add;

val linordered_ring_int = {linordered_ab_group_add_linordered_ring = linordered_ab_group_add_int, ordered_ab_group_add_abs_linordered_ring = ordered_ab_group_add_abs_int, abs_if_linordered_ring = abs_if_int, linordered_semiring_linordered_ring = linordered_semiring_int, ordered_ring_linordered_ring = ordered_ring_int} : Int.int linordered_ring;

val linordered_ring_strict_int = {linordered_ring_linordered_ring_strict = linordered_ring_int, linordered_semiring_strict_linordered_ring_strict = linordered_semiring_strict_int, ring_no_zero_divisors_linordered_ring_strict = ring_no_zero_divisors_int} : Int.int linordered_ring_strict;

val ordered_comm_semiring_int = {comm_semiring_0_ordered_comm_semiring = comm_semiring_0_int, ordered_semiring_ordered_comm_semiring = ordered_semiring_int} : Int.int ordered_comm_semiring;

val ordered_cancel_comm_semiring_int = {comm_semiring_0_cancel_ordered_cancel_comm_semiring = comm_semiring_0_cancel_int, ordered_cancel_semiring_ordered_cancel_comm_semiring = ordered_cancel_semiring_int, ordered_comm_semiring_ordered_cancel_comm_semiring = ordered_comm_semiring_int} : Int.int ordered_cancel_comm_semiring;

val ordered_comm_semiring_strict_int = {ordered_cancel_comm_semiring_ordered_comm_semiring_strict = ordered_cancel_comm_semiring_int, ordered_semiring_strict_ordered_comm_semiring_strict = ordered_semiring_strict_int} : Int.int ordered_comm_semiring_strict;

val linordered_comm_semiring_strict_int = {linordered_semiring_strict_linordered_comm_semiring_strict = linordered_semiring_strict_int, ordered_comm_semiring_strict_linordered_comm_semiring_strict = ordered_comm_semiring_strict_int} : Int.int linordered_comm_semiring_strict;

val linordered_nonzero_semiring_int = {semiring_char_0_linordered_nonzero_semiring = semiring_char_0_int, linorder_linordered_nonzero_semiring = linorder_int, comm_semiring_1_linordered_nonzero_semiring = comm_semiring_1_int, ordered_comm_semiring_linordered_nonzero_semiring = ordered_comm_semiring_int, ordered_semiring_1_linordered_nonzero_semiring = ordered_semiring_1_int} : Int.int linordered_nonzero_semiring;

val linordered_semidom_int = {linordered_comm_semiring_strict_linordered_semidom = linordered_comm_semiring_strict_int, linordered_nonzero_semiring_linordered_semidom = linordered_nonzero_semiring_int, semidom_linordered_semidom = semidom_int} : Int.int linordered_semidom;

val ordered_comm_ring_int = {comm_ring_ordered_comm_ring = comm_ring_int, ordered_cancel_comm_semiring_ordered_comm_ring = ordered_cancel_comm_semiring_int, ordered_ring_ordered_comm_ring = ordered_ring_int} : Int.int ordered_comm_ring;

val ordered_ring_abs_int = {ordered_ab_group_add_abs_ordered_ring_abs = ordered_ab_group_add_abs_int, ordered_ring_ordered_ring_abs = ordered_ring_int} : Int.int ordered_ring_abs;

val linordered_idom_int = {ring_char_0_linordered_idom = ring_char_0_int, idom_abs_sgn_linordered_idom = idom_abs_sgn_int, linordered_ring_strict_linordered_idom = linordered_ring_strict_int, linordered_semidom_linordered_idom = linordered_semidom_int, linordered_semiring_1_strict_linordered_idom = linordered_semiring_1_strict_int, ordered_comm_ring_linordered_idom = ordered_comm_ring_int, ordered_ring_abs_linordered_idom = ordered_ring_abs_int} : Int.int linordered_idom;

val equal_nat = {equal = (fn a => fn b => ((a : Int.int) = b))} : Int.int equal;

fun typerep_nata t = Typerep ("Nat.nat", []);

val countable_nat = {} : Int.int countable;

val typerep_nat = {typerep = typerep_nata} : Int.int typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} : Int.int heap;

val one_nat = {one = (1 : Int.int)} : Int.int one;

val plus_nat = {plus = (fn a => fn b => Int.+ (a, b))} : Int.int plus;

val zero_nat = {zero = (0 : Int.int)} : Int.int zero;

fun typerep_boola t = Typerep ("HOL.bool", []);

val countable_bool = {} : bool countable;

val typerep_bool = {typerep = typerep_boola} : bool typerep;

val heap_bool = {countable_heap = countable_bool, typerep_heap = typerep_bool} : bool heap;

datatype num = One | Bit0 of num | Bit1 of num;

datatype ('a, 'b, 'c, 'd, 'e) bFS_state_imp_ext = BFS_state_imp_ext of 'a * 'c * 'b * Int.int * 'd * 'e;

fun id x = (fn xa => xa) x;

fun eq A_ a b = equal A_ a b;

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

fun max A_ a b = (if less_eq A_ a b then b else a);

fun min A_ a b = (if less_eq A_ a b then a else b);

fun iterate_range A_ arr start enda fi acc = (if Int.<= (start, enda) then (fn () => let
                                                                                       val current = (fn () => Array.sub (arr, start)) ();
                                                                                       val x = fi current acc ();
                                                                                     in
                                                                                       iterate_range A_ arr (Int.+ (start, (1 : Int.int))) enda fi x ()
                                                                                     end)
                                               else (fn () => acc));

fun iterate_neighbourhood A_ gi sindicesi eindicesi v fi acci = (fn () => let
                                                                            val n = (fn () => Array.length sindicesi) ();
                                                                          in
                                                                            (if Int.<= (n, v) then (fn () => acci) else (fn f_ => fn () => f_ (((fn () => Array.sub (sindicesi, v))) ()) ()) (fn vstart => (fn f_ => fn () => f_ (((fn () => Array.sub (eindicesi, v))) ()) ()) (fn vend => iterate_range A_ gi vstart vend (fi v) acci))) ()
                                                                          end);

fun bfs_nbs A_ (ga, (si, ei)) = iterate_neighbourhood A_ ga si ei;

fun bfs_path_rev di pari ra v k = (fn () => let
                                              val _ = (fn () => Machine.upd (k, v, ra)) ();
                                              val dv = (fn () => Array.sub (di, v)) ();
                                            in
                                              (if ((dv : Int.int) = (0 : Int.int)) then (fn () => (Int.+ (k, (1 : Int.int)))) else (fn f_ => fn () => f_ (((fn () => Array.sub (pari, v))) ()) ()) (fn u => bfs_path_rev di pari ra u (Int.+ (k, (1 : Int.int))))) ()
                                            end);

fun bfs_path di pari ra v = bfs_path_rev di pari ra v (0 : Int.int);

fun bset_ins v a = (fn () => Machine.upd (v, true, a));

fun bset_memb v a = (fn () => Array.sub (a, v));

fun part_ins_imp bl c y = (fn () => let
                                      val b = (fn () => Array.sub (bl, y)) ();
                                      val ca = (fn () => Array.sub (c, b)) ();
                                    in
                                      ((ca : Int.int) = (0 : Int.int))
                                    end);

fun bm_ins1 si y = let
                     val (_, (c1, (_, (bl, _)))) = si;
                   in
                     part_ins_imp bl c1 y
                   end;

fun bm_memb x si = let
                     val (xi, (_, (_, (_, _)))) = si;
                   in
                     (fn () => Array.sub (xi, x))
                   end;

fun mx_s si y = (fn () => let
                            val b = bm_memb (id y) si ();
                          in
                            (if b then (fn () => false) else bm_ins1 si (id y)) ()
                          end);

fun bm_ins2 si y = let
                     val (_, (_, (c2, (_, br)))) = si;
                   in
                     part_ins_imp br c2 y
                   end;

fun mx_t si y = (fn () => let
                            val b = bm_memb (id y) si ();
                          in
                            (if b then (fn () => false) else bm_ins2 si (id y)) ()
                          end);

fun foldl_range_imp f i n a = (if Int.< (i, n) then (fn () => let
                                                                val x = f i a ();
                                                              in
                                                                foldl_range_imp f (Int.+ (i, (1 : Int.int))) n x ()
                                                              end)
                                else (fn () => a));

fun fill_range_imp A_ f n a = foldl_range_imp (fn i => (fn aa => (fn () => Machine.upd (i, f i, aa)))) (0 : Int.int) n a;

fun xset_clear_imp n xi = fill_range_imp heap_bool (fn _ => false) n xi;

fun part_cnt_del bl c i = (fn () => let
                                      val b = (fn () => Array.sub (bl, i)) ();
                                      val ca = (fn () => Array.sub (c, b)) ();
                                      val _ = (fn () => Machine.upd (b, Machine.sub_nat (ca, (1 : Int.int)), c)) ();
                                    in
                                      ()
                                    end);

fun bm_del x si = let
                    val (xi, (c1, (c2, (bl, br)))) = si;
                  in
                    (fn () => let
                                val b = (fn () => Array.sub (xi, x)) ();
                              in
                                (if b then (fn f_ => fn () => f_ (((fn () => Machine.upd (x, false, xi))) ()) ()) (fn _ => (fn f_ => fn () => f_ ((part_cnt_del bl c1 x) ()) ()) (fn _ => part_cnt_del br c2 x)) else (fn () => ())) ()
                              end)
                  end;

fun part_cnt_ins bl c i = (fn () => let
                                      val b = (fn () => Array.sub (bl, i)) ();
                                      val ca = (fn () => Array.sub (c, b)) ();
                                      val _ = (fn () => Machine.upd (b, Int.+ (ca, (1 : Int.int)), c)) ();
                                    in
                                      ()
                                    end);

fun bm_ins x si = let
                    val (xi, (c1, (c2, (bl, br)))) = si;
                  in
                    (fn () => let
                                val b = (fn () => Array.sub (xi, x)) ();
                              in
                                (if b then (fn () => ()) else (fn f_ => fn () => f_ (((fn () => Machine.upd (x, true, xi))) ()) ()) (fn _ => (fn f_ => fn () => f_ ((part_cnt_ins bl c1 x) ()) ()) (fn _ => part_cnt_ins br c2 x))) ()
                              end)
                  end;

fun aug_imp sins_imp sdel_imp si ra k = (if ((k : Int.int) = (0 : Int.int)) then (fn () => ()) else (if ((k : Int.int) = (1 : Int.int)) then (fn () => let
                                                                                                                                                         val x = (fn () => Array.sub (ra, (0 : Int.int))) ();
                                                                                                                                                       in
                                                                                                                                                         sins_imp x si ()
                                                                                                                                                       end)
                                                                                                      else (fn () => let
                                                                                                                       val x = (fn () => Array.sub (ra, Machine.sub_nat (k, (1 : Int.int)))) ();
                                                                                                                       val y = (fn () => Array.sub (ra, Machine.sub_nat (k, (2 : Int.int)))) ();
                                                                                                                       val _ = sdel_imp y si ();
                                                                                                                       val _ = sins_imp x si ();
                                                                                                                     in
                                                                                                                       aug_imp sins_imp sdel_imp si ra (Machine.sub_nat (k, (2 : Int.int))) ()
                                                                                                                     end)));

fun mi_loop_imp sins_imp sdel_imp aug_path_imp si ra = (fn () => let
                                                                   val a = aug_path_imp si ra ();
                                                                 in
                                                                   (case a of NONE => (fn () => ()) | SOME k => (fn f_ => fn () => f_ ((aug_imp sins_imp sdel_imp si ra k) ()) ()) (fn _ => mi_loop_imp sins_imp sdel_imp aug_path_imp si ra)) ()
                                                                 end);

fun merge_cnt q1 q2 a b i j c = (if Int.< (i, a) then (if Int.< (j, b) then (fn () => let
                                                                                        val x = q1 i ();
                                                                                        val y = q2 j ();
                                                                                      in
                                                                                        (if Int.< (x, y) then merge_cnt q1 q2 a b (Int.+ (i, (1 : Int.int))) j (Int.+ (c, (1 : Int.int))) else (if Int.< (y, x) then merge_cnt q1 q2 a b i (Int.+ (j, (1 : Int.int))) (Int.+ (c, (1 : Int.int))) else merge_cnt q1 q2 a b (Int.+ (i, (1 : Int.int))) (Int.+ (j, (1 : Int.int))) (Int.+ (c, (1 : Int.int))))) ()
                                                                                      end)
                                                        else (fn () => (Int.+ (c, Machine.sub_nat (a, i)))))
                                  else (fn () => (Int.+ (c, Machine.sub_nat (b, j)))));

fun cand_bounds_imp nq1 q1 nq2 q2 h1 h2 sa ea n = foldl_range_imp (fn u => fn c => fn () => let
                                                                                              val a = nq1 h1 u ();
                                                                                              val b = nq2 h2 u ();
                                                                                              val ca = merge_cnt (q1 h1 u) (q2 h2 u) a b (0 : Int.int) (0 : Int.int) c ();
                                                                                              val _ = (if ((ca : Int.int) = c) then (fn f_ => fn () => f_ (((fn () => Machine.upd (u, (1 : Int.int), sa))) ()) ()) (fn _ => (fn f_ => fn () => f_ (((fn () => Machine.upd (u, (0 : Int.int), ea))) ()) ()) (fn _ => (fn () => ()))) else (fn f_ => fn () => f_ (((fn () => Machine.upd (u, c, sa))) ()) ()) (fn _ => (fn f_ => fn () => f_ (((fn () => Machine.upd (u, Machine.sub_nat (ca, (1 : Int.int)), ea))) ()) ()) (fn _ => (fn () => ())))) ();
                                                                                            in
                                                                                              ca
                                                                                            end)
                                                    (0 : Int.int) n (0 : Int.int);

fun merge_wr q1 q2 a b g i j p = (if Int.< (i, a) then (fn () => let
                                                                   val x = q1 i ();
                                                                 in
                                                                   (if Int.< (j, b) then (fn f_ => fn () => f_ ((q2 j) ()) ()) (fn y => (if Int.< (x, y) then (fn f_ => fn () => f_ (((fn () => Machine.upd (p, x, g))) ()) ()) (fn _ => merge_wr q1 q2 a b g (Int.+ (i, (1 : Int.int))) j (Int.+ (p, (1 : Int.int)))) else (if Int.< (y, x) then (fn f_ => fn () => f_ (((fn () => Machine.upd (p, y, g))) ()) ()) (fn _ => merge_wr q1 q2 a b g i (Int.+ (j, (1 : Int.int))) (Int.+ (p, (1 : Int.int)))) else (fn f_ => fn () => f_ (((fn () => Machine.upd (p, x, g))) ()) ()) (fn _ => merge_wr q1 q2 a b g (Int.+ (i, (1 : Int.int))) (Int.+ (j, (1 : Int.int))) (Int.+ (p, (1 : Int.int))))))) else (fn f_ => fn () => f_ (((fn () => Machine.upd (p, x, g))) ()) ()) (fn _ => merge_wr q1 q2 a b g (Int.+ (i, (1 : Int.int))) j (Int.+ (p, (1 : Int.int))))) ()
                                                                 end)
                                   else (if Int.< (j, b) then (fn () => let
                                                                          val y = q2 j ();
                                                                          val _ = (fn () => Machine.upd (p, y, g)) ();
                                                                        in
                                                                          merge_wr q1 q2 a b g i (Int.+ (j, (1 : Int.int))) (Int.+ (p, (1 : Int.int))) ()
                                                                        end)
                                          else (fn () => p)));

fun cand_fill_imp nq1 q1 nq2 q2 h1 h2 ga n = foldl_range_imp (fn u => fn p => fn () => let
                                                                                         val a = nq1 h1 u ();
                                                                                         val b = nq2 h2 u ();
                                                                                       in
                                                                                         merge_wr (q1 h1 u) (q2 h2 u) a b ga (0 : Int.int) (0 : Int.int) p ()
                                                                                       end)
                                               (0 : Int.int) n (0 : Int.int);

fun cand_csr_imp nq1 q1 nq2 q2 h1 h2 n = (fn () => let
                                                     val sa = (fn () => Array.array (n, (0 : Int.int))) ();
                                                     val ea = (fn () => Array.array (n, (0 : Int.int))) ();
                                                     val m = cand_bounds_imp nq1 q1 nq2 q2 h1 h2 sa ea n ();
                                                     val ga = (fn () => Array.array (m, (0 : Int.int))) ();
                                                     val _ = cand_fill_imp nq1 q1 nq2 q2 h1 h2 ga n ();
                                                   in
                                                     (ga, (sa, ea))
                                                   end);

fun pt_ids_imp idx elt pt_imp h i k = (fn () => let
                                                  val y = pt_imp h (elt i) k ();
                                                in
                                                  idx y
                                                end);

fun part_npts_imp h x = let
                          val (_, (sa, ea)) = h;
                        in
                          (fn () => let
                                      val s = (fn () => Array.sub (sa, x)) ();
                                      val e = (fn () => Array.sub (ea, x)) ();
                                    in
                                      Machine.sub_nat (e, s)
                                    end)
                        end;

fun collect_range_imp p n fa = foldl_range_imp (fn y => fn k => fn () => let
                                                                           val b = p y ();
                                                                         in
                                                                           (if b then (fn f_ => fn () => f_ (((fn () => Machine.upd (k, y, fa))) ()) ()) (fn _ => (fn () => (Int.+ (k, (1 : Int.int))))) else (fn () => k)) ()
                                                                         end)
                                 (0 : Int.int) n (0 : Int.int);

fun find_range_imp p i n = (if Int.< (i, n) then (fn () => let
                                                             val b = p i ();
                                                           in
                                                             (if b then (fn () => (SOME i)) else find_range_imp p (Int.+ (i, (1 : Int.int))) n) ()
                                                           end)
                             else (fn () => NONE));

fun visited (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) = visited;

fun parent (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) = parent;

fun dists (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) = dists;

fun current_dist_update current_dista (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) = BFS_state_imp_ext (dists, current, visited, current_dista current_dist, parent, more);

fun visited_update visiteda (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) = BFS_state_imp_ext (dists, current, visiteda visited, current_dist, parent, more);

fun current_update currenta (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) = BFS_state_imp_ext (dists, currenta current, visited, current_dist, parent, more);

fun parent_update parenta (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) = BFS_state_imp_ext (dists, current, visited, current_dist, parenta parent, more);

fun dists_update distsa (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) = BFS_state_imp_ext (distsa dists, current, visited, current_dist, parent, more);

fun current_dist (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) = current_dist;

fun current (BFS_state_imp_ext (dists, current, visited, current_dist, parent, more)) = current;

fun bfs_cf_is_empty (B1_, B2_) (fronti, (frontp, buffer_fronti)) = (fn () => (eq B2_ frontp (zero B1_)));

fun iterate_range_strict A_ arr start enda fi acc = (if Int.< (start, enda) then (fn () => let
                                                                                             val current = (fn () => Array.sub (arr, start)) ();
                                                                                             val x = fi current acc ();
                                                                                           in
                                                                                             iterate_range_strict A_ arr (Int.+ (start, (1 : Int.int))) enda fi x ()
                                                                                           end)
                                                      else (fn () => acc));

fun mx_filt p si fi = (fn u => fn v => fn a => fn () => let
                                                          val ok = p si u v ();
                                                        in
                                                          (if ok then fi u v a else (fn () => a)) ()
                                                        end);

fun part_exch_imp bl x y = (fn () => let
                                       val a = (fn () => Array.sub (bl, x)) ();
                                       val b = (fn () => Array.sub (bl, y)) ();
                                     in
                                       ((a : Int.int) = b)
                                     end);

fun bm_exch2 si x y = let
                        val (_, (_, (_, (_, br)))) = si;
                      in
                        part_exch_imp br x y
                      end;

fun mx_nb2 si u v = (fn () => let
                                val b = bm_memb (id v) si ();
                              in
                                (if b then bm_exch2 si (id v) (id u) else (fn () => false)) ()
                              end);

fun bm_exch1 si x y = let
                        val (_, (_, (_, (bl, _)))) = si;
                      in
                        part_exch_imp bl x y
                      end;

fun mx_nb1 si u v = (fn () => let
                                val b = bm_memb (id v) si ();
                              in
                                (if b then (fn () => false) else (fn f_ => fn () => f_ ((bm_ins1 si (id v)) ()) ()) (fn s => (if s then (fn () => false) else bm_exch1 si (id u) (id v)))) ()
                              end);

fun mx_xnbs n gh u fi acc = let
                              val (si, gc) = gh;
                            in
                              (if Int.< (u, n) then (fn () => let
                                                                val b = bm_memb (id u) si ();
                                                              in
                                                                (if b then bfs_nbs heap_nat gc u (mx_filt mx_nb1 si fi) acc else (fn f_ => fn () => f_ ((bm_ins2 si (id u)) ()) ()) (fn t => (if t then (fn () => acc) else bfs_nbs heap_nat gc u (mx_filt mx_nb2 si fi) acc))) ()
                                                              end)
                                else (fn () => acc))
                            end;

fun xb_inner n gi pari u (front, (frontpt, vis)) = mx_xnbs n gi u (fn ua => fn v => fn (fronta, (frontpta, visa)) => fn () => let
                                                                                                                                val b = bset_memb v visa ();
                                                                                                                              in
                                                                                                                                (if not b then (fn f_ => fn () => f_ (((fn () => Machine.upd (frontpta, v, fronta))) ()) ()) (fn frontb => (fn f_ => fn () => f_ ((bset_ins v visa) ()) ()) (fn visb => (fn f_ => fn () => f_ (((fn () => Machine.upd (v, ua, pari))) ()) ()) (fn _ => (fn () => (frontb, (Int.+ (frontpta, (1 : Int.int)), visb)))))) else (fn () => (fronta, (frontpta, visa)))) ()
                                                                                                                              end)
                                                     (front, (frontpt, vis));

fun xb_outer n gi pari (old_front, old_frontp) (front, (frontpt, vis)) = iterate_range_strict heap_nat old_front (0 : Int.int) old_frontp (xb_inner n gi pari) (front, (frontpt, vis));

fun xb_round n gi (fronti, (frontp, buffer_fronti)) imp_vis pari = (fn () => let
                                                                               val a = xb_outer n gi pari (fronti, frontp) (buffer_fronti, ((0 : Int.int), imp_vis)) ();
                                                                             in
                                                                               let
                                                                                 val (front, (frontpt, vis)) = a;
                                                                               in
                                                                                 (fn () => ((front, (frontpt, fronti)), (vis, pari)))
                                                                               end
                                                                                 ()
                                                                             end);

fun bfs_set_dists A_ di (fronti, (frontp, buffer_fronti)) n = iterate_range_strict heap_nat fronti (0 : Int.int) frontp (fn v => (fn a => (fn () => Machine.upd (v, n, a)))) di;

fun xb_loop n gh state = (fn () => let
                                     val b = bfs_cf_is_empty (zero_nat, equal_nat) (current state) ();
                                   in
                                     (if b then (fn () => state) else (fn f_ => fn () => f_ ((xb_round n gh (current state) (visited state) (parent state)) ()) ()) (fn (currenta, (visiteda, parenta)) => let
                                                                                                                                                                                                             val d = current_dist state;
                                                                                                                                                                                                           in
                                                                                                                                                                                                             (fn f_ => fn () => f_ ((bfs_set_dists heap_nat (dists state) currenta (Int.+ (d, (1 : Int.int)))) ()) ()) (fn dist => xb_loop n gh (parent_update (fn _ => parenta) (current_dist_update (fn _ => Int.+ (d, (1 : Int.int))) (current_update (fn _ => currenta) (visited_update (fn _ => visiteda) (dists_update (fn _ => dist) state))))))
                                                                                                                                                                                                           end))
                                       ()
                                   end);

fun bfs_set_srcs_visited imp_vis (fronti, (frontp, buffer_fronti)) = iterate_range_strict heap_nat fronti (0 : Int.int) frontp (fn v => fn vis => fn () => let
                                                                                                                                                             val b = bset_memb v vis ();
                                                                                                                                                           in
                                                                                                                                                             (if not b then bset_ins v vis else (fn () => vis)) ()
                                                                                                                                                           end)
                                                                       imp_vis;

fun bfs_src_to_cf x = (fn () => x);

fun xb_init empty_vis src_imp imp_some_dist imp_some_par = (fn () => let
                                                                       val v = bfs_set_srcs_visited empty_vis src_imp ();
                                                                       val cf = bfs_src_to_cf src_imp ();
                                                                       val dists = bfs_set_dists heap_nat imp_some_dist cf (0 : Int.int) ();
                                                                     in
                                                                       BFS_state_imp_ext (dists, cf, v, (0 : Int.int), imp_some_par, ())
                                                                     end);

fun xb_run n gh empty_vis src_imp imp_some_dist imp_some_par = (fn () => let
                                                                           val init = xb_init empty_vis src_imp imp_some_dist imp_some_par ();
                                                                           val final = xb_loop n gh init ();
                                                                         in
                                                                           (visited final, (dists final, parent final))
                                                                         end);

fun mx_bfs_run n gh = xb_run n gh;

fun mx_tgt si vi y = (fn () => let
                                 val v = (fn () => Array.sub (vi, y)) ();
                               in
                                 (if v then mx_t si y else (fn () => false)) ()
                               end);

fun mx_tail n si ra r = let
                          val (vi, (da, pa)) = r;
                        in
                          (fn () => let
                                      val a = find_range_imp (mx_tgt si vi) (0 : Int.int) n ();
                                    in
                                      (case a of NONE => (fn () => NONE) | SOME t => (fn f_ => fn () => f_ ((bfs_path da pa ra t) ()) ()) (fn l => (fn () => (SOME l)))) ()
                                    end)
                        end;

fun mx_round n gc vi fr bf da pa si ra k = (fn () => let
                                                       val _ = xset_clear_imp n vi ();
                                                       val _ = fill_range_imp heap_nat id n da ();
                                                       val _ = fill_range_imp heap_nat id n pa ();
                                                       val _ = mx_bfs_run n (si, gc) vi (fr, (k, bf)) da pa ();
                                                     in
                                                       mx_tail n si ra (vi, (da, pa)) ()
                                                     end);

fun mx_has_nb n gc si y = mx_xnbs n (si, gc) y (fn _ => fn _ => fn _ => (fn () => true)) false;

fun mx_src n gc si y = (fn () => let
                                   val s = mx_s si y ();
                                 in
                                   (if s then mx_has_nb n gc si y else (fn () => false)) ()
                                 end);

fun mx_st si y = (fn () => let
                             val s = mx_s si y ();
                           in
                             (if s then bm_ins2 si (id y) else (fn () => false)) ()
                           end);

fun mx_aug_path n gc vi fr bf da pa si ra = (fn () => let
                                                        val a = find_range_imp (mx_st si) (0 : Int.int) n ();
                                                      in
                                                        (case a of NONE => (fn f_ => fn () => f_ ((collect_range_imp (mx_src n gc si) n fr) ()) ()) (fn k => (if ((k : Int.int) = (0 : Int.int)) then (fn () => NONE) else mx_round n gc vi fr bf da pa si ra k)) | SOME s => (fn f_ => fn () => f_ (((fn () => Machine.upd ((0 : Int.int), s, ra))) ()) ()) (fn _ => (fn () => (SOME (1 : Int.int))))) ()
                                                      end);

fun part_pt_imp h x k = let
                          val (oa, (sa, _)) = h;
                        in
                          (fn () => let
                                      val s = (fn () => Array.sub (sa, x)) ();
                                    in
                                      (fn () => Array.sub (oa, Int.+ (s, k))) ()
                                    end)
                        end;

fun mx_mi_ids n h1 h2 si = (fn () => let
                                       val gc = cand_csr_imp (fn h => fn i => part_npts_imp h (id i)) (pt_ids_imp id id part_pt_imp) (fn h => fn i => part_npts_imp h (id i)) (pt_ids_imp id id part_pt_imp) h1 h2 n ();
                                       val vi = (fn () => Array.array (n, false)) ();
                                       val fr = (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
                                       val bf = (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
                                       val da = (fn () => Array.array (n, (0 : Int.int))) ();
                                       val pa = (fn () => Array.array (n, (0 : Int.int))) ();
                                       val x = (fn () => Array.array (n, (0 : Int.int))) ();
                                     in
                                       mi_loop_imp (fn i => bm_ins (id i)) (fn i => bm_del (id i)) (mx_aug_path n gc vi fr bf da pa) si x ()
                                     end);

fun mx_mi n h1 h2 si = mx_mi_ids n h1 h2 si;

fun part_prefix_imp (A1_, A2_) nb b = foldl_range_imp (fn j => fn _ => fn () => let
                                                                                  val c = (fn () => Array.sub (b, j)) ();
                                                                                  val d = (fn () => Array.sub (b, Machine.sub_nat (j, (1 : Int.int)))) ();
                                                                                  val _ = (fn () => Machine.upd (j, plus A1_ c d, b)) ();
                                                                                in
                                                                                  ()
                                                                                end)
                                        (1 : Int.int) (Int.+ (nb, (1 : Int.int))) ();

fun part_count_imp (A1_, A2_, A3_) n nb bl b = foldl_range_imp (fn i => fn _ => fn () => let
                                                                                           val k = (fn () => Array.sub (bl, i)) ();
                                                                                         in
                                                                                           (if Int.<= (Int.+ (k, (2 : Int.int)), nb) then (fn f_ => fn () => f_ (((fn () => Array.sub (b, Int.+ (k, (2 : Int.int))))) ()) ()) (fn c => (fn f_ => fn () => f_ (((fn () => Machine.upd (Int.+ (k, (2 : Int.int)), plus A2_ c (one A1_), b))) ()) ()) (fn _ => (fn () => ()))) else (fn () => ())) ()
                                                                                         end)
                                                 (0 : Int.int) n ();

fun part_fill_imp n bl b oa = foldl_range_imp (fn i => fn _ => fn () => let
                                                                          val k = (fn () => Array.sub (bl, i)) ();
                                                                          val p = (fn () => Array.sub (b, Int.+ (k, (1 : Int.int)))) ();
                                                                          val _ = (fn () => Machine.upd (Int.+ (k, (1 : Int.int)), Int.+ (p, (1 : Int.int)), b)) ();
                                                                          val _ = (fn () => Machine.upd (p, i, oa)) ();
                                                                        in
                                                                          ()
                                                                        end)
                                (0 : Int.int) n ();

fun foldr_range_imp f i a = (if ((i : Int.int) = (0 : Int.int)) then (fn () => a) else (fn () => let
                                                                                                   val x = f (Machine.sub_nat (i, (1 : Int.int))) a ();
                                                                                                 in
                                                                                                   foldr_range_imp f (Machine.sub_nat (i, (1 : Int.int))) x ()
                                                                                                 end));

fun copy_range_imp A_ p n a = foldr_range_imp (fn i => fn _ => fn () => let
                                                                          val x = p i ();
                                                                          val _ = (fn () => Machine.upd (i, x, a)) ();
                                                                        in
                                                                          ()
                                                                        end)
                                n ();

fun part_handle_imp n nb bl = (fn () => let
                                          val b = (fn () => Array.array (Int.+ (nb, (1 : Int.int)), (0 : Int.int))) ();
                                          val _ = part_count_imp (one_nat, plus_nat, heap_nat) n nb bl b ();
                                          val _ = part_prefix_imp (plus_nat, heap_nat) nb b ();
                                          val oa = (fn () => Array.array (n, (0 : Int.int))) ();
                                          val _ = part_fill_imp n bl b oa ();
                                          val sa = (fn () => Array.array (n, (0 : Int.int))) ();
                                          val _ = copy_range_imp heap_nat (fn i => (fn f_ => fn () => f_ (((fn () => Array.sub (bl, i))) ()) ()) (fn a => (fn () => Array.sub (b, a)))) n sa ();
                                          val ea = (fn () => Array.array (n, (0 : Int.int))) ();
                                          val _ = copy_range_imp heap_nat (fn i => (fn f_ => fn () => f_ (((fn () => Array.sub (bl, i))) ()) ()) (fn k => (fn () => Array.sub (b, Int.+ (k, (1 : Int.int)))))) n ea ();
                                        in
                                          (oa, (sa, ea))
                                        end);

fun bm_setup_imp (A1_, A2_) (B1_, B2_) nv fa ta k = (fn () => let
                                                                val m = (fn () => Array.length fa) ();
                                                                val h1 = part_handle_imp m nv fa ();
                                                                val h2 = part_handle_imp m nv ta ();
                                                                val xi = (fn () => Array.array (m, false)) ();
                                                                val c1 = (fn () => Array.array (nv, zero A1_)) ();
                                                                val x = (fn () => Array.array (nv, zero B1_)) ();
                                                              in
                                                                k m h1 h2 xi c1 x ()
                                                              end);

fun bb_memb x si = let
                     val (xi, (c1, (c2, (bl, (br, _))))) = si;
                   in
                     bm_memb x (xi, (c1, (c2, (bl, br))))
                   end;

fun part_cap_ins_imp bl ka c y = (fn () => let
                                             val b = (fn () => Array.sub (bl, y)) ();
                                             val ca = (fn () => Array.sub (c, b)) ();
                                             val k = (fn () => Array.sub (ka, b)) ();
                                           in
                                             Int.< (ca, k)
                                           end);

fun bb_ins1 si y = let
                     val (_, (c1, (_, (bl, (_, k))))) = si;
                   in
                     part_cap_ins_imp bl k c1 y
                   end;

fun bx_s si y = (fn () => let
                            val b = bb_memb (id y) si ();
                          in
                            (if b then (fn () => false) else bb_ins1 si (id y)) ()
                          end);

fun bb_ins2 si y = let
                     val (_, (_, (c2, (_, (br, k))))) = si;
                   in
                     part_cap_ins_imp br k c2 y
                   end;

fun bx_t si y = (fn () => let
                            val b = bb_memb (id y) si ();
                          in
                            (if b then (fn () => false) else bb_ins2 si (id y)) ()
                          end);

fun bx_filt p si fi = (fn u => fn v => fn a => fn () => let
                                                          val ok = p si u v ();
                                                        in
                                                          (if ok then fi u v a else (fn () => a)) ()
                                                        end);

fun bb_exch2 si x y = let
                        val (_, (_, (_, (_, (br, _))))) = si;
                      in
                        part_exch_imp br x y
                      end;

fun bx_nb2 si u v = (fn () => let
                                val b = bb_memb (id v) si ();
                              in
                                (if b then bb_exch2 si (id v) (id u) else (fn () => false)) ()
                              end);

fun bb_exch1 si x y = let
                        val (_, (_, (_, (bl, (_, _))))) = si;
                      in
                        part_exch_imp bl x y
                      end;

fun bx_nb1 si u v = (fn () => let
                                val b = bb_memb (id v) si ();
                              in
                                (if b then (fn () => false) else (fn f_ => fn () => f_ ((bb_ins1 si (id v)) ()) ()) (fn s => (if s then (fn () => false) else bb_exch1 si (id u) (id v)))) ()
                              end);

fun bx_xnbs n gh u fi acc = let
                              val (si, gc) = gh;
                            in
                              (if Int.< (u, n) then (fn () => let
                                                                val b = bb_memb (id u) si ();
                                                              in
                                                                (if b then bfs_nbs heap_nat gc u (bx_filt bx_nb1 si fi) acc else (fn f_ => fn () => f_ ((bb_ins2 si (id u)) ()) ()) (fn t => (if t then (fn () => acc) else bfs_nbs heap_nat gc u (bx_filt bx_nb2 si fi) acc))) ()
                                                              end)
                                else (fn () => acc))
                            end;

fun xbb_inner n gi pari u (front, (frontpt, vis)) = bx_xnbs n gi u (fn ua => fn v => fn (fronta, (frontpta, visa)) => fn () => let
                                                                                                                                 val b = bset_memb v visa ();
                                                                                                                               in
                                                                                                                                 (if not b then (fn f_ => fn () => f_ (((fn () => Machine.upd (frontpta, v, fronta))) ()) ()) (fn frontb => (fn f_ => fn () => f_ ((bset_ins v visa) ()) ()) (fn visb => (fn f_ => fn () => f_ (((fn () => Machine.upd (v, ua, pari))) ()) ()) (fn _ => (fn () => (frontb, (Int.+ (frontpta, (1 : Int.int)), visb)))))) else (fn () => (fronta, (frontpta, visa)))) ()
                                                                                                                               end)
                                                      (front, (frontpt, vis));

fun xbb_outer n gi pari (old_front, old_frontp) (front, (frontpt, vis)) = iterate_range_strict heap_nat old_front (0 : Int.int) old_frontp (xbb_inner n gi pari) (front, (frontpt, vis));

fun xbb_round n gi (fronti, (frontp, buffer_fronti)) imp_vis pari = (fn () => let
                                                                                val a = xbb_outer n gi pari (fronti, frontp) (buffer_fronti, ((0 : Int.int), imp_vis)) ();
                                                                              in
                                                                                let
                                                                                  val (front, (frontpt, vis)) = a;
                                                                                in
                                                                                  (fn () => ((front, (frontpt, fronti)), (vis, pari)))
                                                                                end
                                                                                  ()
                                                                              end);

fun xbb_loop n gh state = (fn () => let
                                      val b = bfs_cf_is_empty (zero_nat, equal_nat) (current state) ();
                                    in
                                      (if b then (fn () => state) else (fn f_ => fn () => f_ ((xbb_round n gh (current state) (visited state) (parent state)) ()) ()) (fn (currenta, (visiteda, parenta)) => let
                                                                                                                                                                                                               val d = current_dist state;
                                                                                                                                                                                                             in
                                                                                                                                                                                                               (fn f_ => fn () => f_ ((bfs_set_dists heap_nat (dists state) currenta (Int.+ (d, (1 : Int.int)))) ()) ()) (fn dist => xbb_loop n gh (parent_update (fn _ => parenta) (current_dist_update (fn _ => Int.+ (d, (1 : Int.int))) (current_update (fn _ => currenta) (visited_update (fn _ => visiteda) (dists_update (fn _ => dist) state))))))
                                                                                                                                                                                                             end))
                                        ()
                                    end);

fun xbb_init empty_vis src_imp imp_some_dist imp_some_par = (fn () => let
                                                                        val v = bfs_set_srcs_visited empty_vis src_imp ();
                                                                        val cf = bfs_src_to_cf src_imp ();
                                                                        val dists = bfs_set_dists heap_nat imp_some_dist cf (0 : Int.int) ();
                                                                      in
                                                                        BFS_state_imp_ext (dists, cf, v, (0 : Int.int), imp_some_par, ())
                                                                      end);

fun xbb_run n gh empty_vis src_imp imp_some_dist imp_some_par = (fn () => let
                                                                            val init = xbb_init empty_vis src_imp imp_some_dist imp_some_par ();
                                                                            val final = xbb_loop n gh init ();
                                                                          in
                                                                            (visited final, (dists final, parent final))
                                                                          end);

fun bx_bfs_run n gh = xbb_run n gh;

fun bx_tgt si vi y = (fn () => let
                                 val v = (fn () => Array.sub (vi, y)) ();
                               in
                                 (if v then bx_t si y else (fn () => false)) ()
                               end);

fun bx_tail n si ra r = let
                          val (vi, (da, pa)) = r;
                        in
                          (fn () => let
                                      val a = find_range_imp (bx_tgt si vi) (0 : Int.int) n ();
                                    in
                                      (case a of NONE => (fn () => NONE) | SOME t => (fn f_ => fn () => f_ ((bfs_path da pa ra t) ()) ()) (fn l => (fn () => (SOME l)))) ()
                                    end)
                        end;

fun bx_round n gc vi fr bf da pa si ra k = (fn () => let
                                                       val _ = xset_clear_imp n vi ();
                                                       val _ = fill_range_imp heap_nat id n da ();
                                                       val _ = fill_range_imp heap_nat id n pa ();
                                                       val _ = bx_bfs_run n (si, gc) vi (fr, (k, bf)) da pa ();
                                                     in
                                                       bx_tail n si ra (vi, (da, pa)) ()
                                                     end);

fun bx_has_nb n gc si y = bx_xnbs n (si, gc) y (fn _ => fn _ => fn _ => (fn () => true)) false;

fun bx_src n gc si y = (fn () => let
                                   val s = bx_s si y ();
                                 in
                                   (if s then bx_has_nb n gc si y else (fn () => false)) ()
                                 end);

fun bx_st si y = (fn () => let
                             val s = bx_s si y ();
                           in
                             (if s then bb_ins2 si (id y) else (fn () => false)) ()
                           end);

fun bx_aug_path n gc vi fr bf da pa si ra = (fn () => let
                                                        val a = find_range_imp (bx_st si) (0 : Int.int) n ();
                                                      in
                                                        (case a of NONE => (fn f_ => fn () => f_ ((collect_range_imp (bx_src n gc si) n fr) ()) ()) (fn k => (if ((k : Int.int) = (0 : Int.int)) then (fn () => NONE) else bx_round n gc vi fr bf da pa si ra k)) | SOME s => (fn f_ => fn () => f_ (((fn () => Machine.upd ((0 : Int.int), s, ra))) ()) ()) (fn _ => (fn () => (SOME (1 : Int.int))))) ()
                                                      end);

fun bb_ins x si = let
                    val (xi, (c1, (c2, (bl, (br, _))))) = si;
                  in
                    bm_ins x (xi, (c1, (c2, (bl, br))))
                  end;

fun bb_del x si = let
                    val (xi, (c1, (c2, (bl, (br, _))))) = si;
                  in
                    bm_del x (xi, (c1, (c2, (bl, br))))
                  end;

fun bx_mi_ids n h1 h2 si = (fn () => let
                                       val gc = cand_csr_imp (fn h => fn i => part_npts_imp h (id i)) (pt_ids_imp id id part_pt_imp) (fn h => fn i => part_npts_imp h (id i)) (pt_ids_imp id id part_pt_imp) h1 h2 n ();
                                       val vi = (fn () => Array.array (n, false)) ();
                                       val fr = (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
                                       val bf = (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
                                       val da = (fn () => Array.array (n, (0 : Int.int))) ();
                                       val pa = (fn () => Array.array (n, (0 : Int.int))) ();
                                       val x = (fn () => Array.array (n, (0 : Int.int))) ();
                                     in
                                       mi_loop_imp (fn i => bb_ins (id i)) (fn i => bb_del (id i)) (bx_aug_path n gc vi fr bf da pa) si x ()
                                     end);

fun bx_mi n h1 h2 si = bx_mi_ids n h1 h2 si;

fun matching_imp nv fa ta = bm_setup_imp (zero_nat, heap_nat) (zero_nat, heap_nat) nv fa ta (fn m => fn h1 => fn h2 => fn xi => fn c1 => fn c2 => fn () => let
                                                                                                                                                             val _ = mx_mi m h1 h2 (xi, (c1, (c2, (fa, ta)))) ();
                                                                                                                                                           in
                                                                                                                                                             xi
                                                                                                                                                           end);

fun bb_setup_imp A_ (B1_, B2_) (C1_, C2_) fa ta ka k = (fn () => let
                                                                   val nv = (fn () => Array.length ka) ();
                                                                 in
                                                                   bm_setup_imp (B1_, B2_) (C1_, C2_) nv fa ta k ()
                                                                 end);

fun b_matching_imp fa ta ka = bb_setup_imp heap_nat (zero_nat, heap_nat) (zero_nat, heap_nat) fa ta ka (fn m => fn h1 => fn h2 => fn xi => fn c1 => fn c2 => fn () => let
                                                                                                                                                                        val _ = bx_mi m h1 h2 (xi, (c1, (c2, (fa, (ta, ka))))) ();
                                                                                                                                                                      in
                                                                                                                                                                        xi
                                                                                                                                                                      end);

fun eps_min A_ a v = (case a of NONE => SOME v | SOME w => SOME (min A_ w v));

fun wmx_gap (A1_, A2_, A3_) c1 c2 b vi = (fn u => fn v => fn a => fn () => let
                                                                             val r = (fn () => Array.sub (vi, v)) ();
                                                                           in
                                                                             (if r then (fn () => a) else (fn f_ => fn () => f_ ((if b then (fn f_ => fn () => f_ (((fn () => Array.sub (c1, u))) ()) ()) (fn x => (fn f_ => fn () => f_ (((fn () => Array.sub (c1, v))) ()) ()) (fn y => (fn () => (minus A1_ x y)))) else (fn f_ => fn () => f_ (((fn () => Array.sub (c2, v))) ()) ()) (fn x => (fn f_ => fn () => f_ (((fn () => Array.sub (c2, u))) ()) ()) (fn y => (fn () => (minus A1_ x y))))) ()) ()) (fn g => (fn () => (eps_min A3_ a g)))) ()
                                                                           end);

fun wmx_max (A1_, A2_) n p c = foldr_range_imp (fn y => fn a => fn () => let
                                                                           val pa = p y ();
                                                                         in
                                                                           (if pa then (fn f_ => fn () => f_ (((fn () => Array.sub (c, y))) ()) ()) (fn x => (fn () => (SOME (case a of NONE => x | SOME w => max A2_ w x)))) else (fn () => a)) ()
                                                                         end)
                                 n NONE;

fun wmx_teq (A1_, A2_) c cu = (fn _ => fn _ => fn v => fn () => let
                                                                  val cv = (fn () => Array.sub (c, v)) ();
                                                                in
                                                                  eq A1_ cu cv
                                                                end);

fun reweight_imp (A1_, A2_) shift_imp e c1 c2 = (fn () => let
                                                            val _ = shift_imp (uminus ((uminus_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A2_) e) c1 ();
                                                          in
                                                            shift_imp e c2 ()
                                                          end);

fun gain_imp (B1_, B2_) cval_imp c1 c2 ra k = (fn () => let
                                                          val u = (fn () => Array.sub (ra, Machine.sub_nat (k, (1 : Int.int)))) ();
                                                          val v = (fn () => Array.sub (ra, (0 : Int.int))) ();
                                                          val a = cval_imp c1 u ();
                                                          val b = cval_imp c2 v ();
                                                        in
                                                          less ((ord_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) B2_) (zero ((zero_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) B2_)) (plus ((plus_semigroup_add o semigroup_add_numeral o numeral_neg_numeral o neg_numeral_ring_1 o ring_1_ring_char_0 o ring_char_0_linordered_idom) B2_) a b)
                                                        end);

fun wmi_loop_imp (C1_, C2_) sins_imp sdel_imp cval_imp tight_ctx_imp tight_path_imp eps_imp shift_imp si c1 c2 ra = (fn () => let
                                                                                                                                val _ = tight_ctx_imp si c1 c2 ();
                                                                                                                                val a = tight_path_imp ra ();
                                                                                                                              in
                                                                                                                                (case a of NONE => (fn f_ => fn () => f_ ((eps_imp si c1 c2) ()) ()) (fn aa => (case aa of NONE => (fn () => ()) | SOME e => (fn f_ => fn () => f_ ((reweight_imp (C1_, C2_) shift_imp e c1 c2) ()) ()) (fn _ => wmi_loop_imp (C1_, C2_) sins_imp sdel_imp cval_imp tight_ctx_imp tight_path_imp eps_imp shift_imp si c1 c2 ra))) | SOME k => (fn f_ => fn () => f_ ((gain_imp (C1_, C2_) cval_imp c1 c2 ra k) ()) ()) (fn g => (if g then (fn f_ => fn () => f_ ((aug_imp sins_imp sdel_imp si ra k) ()) ()) (fn _ => wmi_loop_imp (C1_, C2_) sins_imp sdel_imp cval_imp tight_ctx_imp tight_path_imp eps_imp shift_imp si c1 c2 ra) else (fn () => ())))) ()
                                                                                                                              end);

fun winit_imp ccopy_imp czero_imp co c1 c2 = (fn () => let
                                                         val _ = ccopy_imp co c1 ();
                                                       in
                                                         czero_imp c2 ()
                                                       end);

fun wmi_run_imp (C1_, C2_) sins_imp sdel_imp cval_imp ccopy_imp czero_imp tight_ctx_imp tight_path_imp eps_imp shift_imp si co c1 c2 ra = (fn () => let
                                                                                                                                                      val _ = winit_imp ccopy_imp czero_imp co c1 c2 ();
                                                                                                                                                    in
                                                                                                                                                      wmi_loop_imp (C1_, C2_) sins_imp sdel_imp cval_imp tight_ctx_imp tight_path_imp eps_imp shift_imp si c1 c2 ra ()
                                                                                                                                                    end);

fun t_imp smemb_imp ins2_imp si y = (fn () => let
                                                val b = smemb_imp y si ();
                                              in
                                                (if b then (fn () => false) else ins2_imp si y) ()
                                              end);

fun s_imp smemb_imp ins1_imp si y = (fn () => let
                                                val b = smemb_imp y si ();
                                              in
                                                (if b then (fn () => false) else ins1_imp si y) ()
                                              end);

fun filt_imp p si fi = (fn u => fn v => fn a => fn () => let
                                                           val ok = p si u v ();
                                                         in
                                                           (if ok then fi u v a else (fn () => a)) ()
                                                         end);

fun nb2_imp smemb_imp exch2_imp si u v = (fn () => let
                                                     val b = smemb_imp v si ();
                                                   in
                                                     (if b then exch2_imp si v u else (fn () => false)) ()
                                                   end);

fun nb1_imp smemb_imp ins1_imp exch1_imp si u v = (fn () => let
                                                              val b = smemb_imp v si ();
                                                            in
                                                              (if b then (fn () => false) else (fn f_ => fn () => f_ ((ins1_imp si v) ()) ()) (fn s => (if s then (fn () => false) else exch1_imp si u v))) ()
                                                            end);

fun xnbs n smemb_imp ins1_imp exch1_imp ins2_imp exch2_imp gh u fi acc = let
                                                                           val (si, gc) = gh;
                                                                         in
                                                                           (if Int.< (u, n) then (fn () => let
                                                                                                             val b = smemb_imp u si ();
                                                                                                           in
                                                                                                             (if b then bfs_nbs heap_nat gc u (filt_imp (nb1_imp smemb_imp ins1_imp exch1_imp) si fi) acc else (fn f_ => fn () => f_ ((ins2_imp si u) ()) ()) (fn t => (if t then (fn () => acc) else bfs_nbs heap_nat gc u (filt_imp (nb2_imp smemb_imp exch2_imp) si fi) acc))) ()
                                                                                                           end)
                                                                             else (fn () => acc))
                                                                         end;

fun wmx_tnbs (A1_, A2_) n gh u fi acc = let
                                          val (si, (gc, (c1, c2))) = gh;
                                        in
                                          (if Int.< (u, n) then (fn () => let
                                                                            val b = bm_memb (id u) si ();
                                                                            val cu = (fn () => Array.sub ((if b then c1 else c2), u)) ();
                                                                          in
                                                                            xnbs n (fn i => bm_memb (id i)) (fn sia => fn i => bm_ins1 sia (id i)) (fn sia => fn i => fn j => bm_exch1 sia (id i) (id j)) (fn sia => fn i => bm_ins2 sia (id i)) (fn sia => fn i => fn j => bm_exch2 sia (id i) (id j)) (si, gc) u (filt_imp (wmx_teq (A1_, A2_) (if b then c1 else c2) cu) si fi) acc ()
                                                                          end)
                                            else (fn () => acc))
                                        end;

fun wxb_inner (A1_, A2_) n gi pari u (front, (frontpt, vis)) = wmx_tnbs (A1_, A2_) n gi u (fn ua => fn v => fn (fronta, (frontpta, visa)) => fn () => let
                                                                                                                                                        val b = bset_memb v visa ();
                                                                                                                                                      in
                                                                                                                                                        (if not b then (fn f_ => fn () => f_ (((fn () => Machine.upd (frontpta, v, fronta))) ()) ()) (fn frontb => (fn f_ => fn () => f_ ((bset_ins v visa) ()) ()) (fn visb => (fn f_ => fn () => f_ (((fn () => Machine.upd (v, ua, pari))) ()) ()) (fn _ => (fn () => (frontb, (Int.+ (frontpta, (1 : Int.int)), visb)))))) else (fn () => (fronta, (frontpta, visa)))) ()
                                                                                                                                                      end)
                                                                 (front, (frontpt, vis));

fun wxb_outer (A1_, A2_) n gi pari (old_front, old_frontp) (front, (frontpt, vis)) = iterate_range_strict heap_nat old_front (0 : Int.int) old_frontp (wxb_inner (A1_, A2_) n gi pari) (front, (frontpt, vis));

fun wxb_round (A1_, A2_) n gi (fronti, (frontp, buffer_fronti)) imp_vis pari = (fn () => let
                                                                                           val a = wxb_outer (A1_, A2_) n gi pari (fronti, frontp) (buffer_fronti, ((0 : Int.int), imp_vis)) ();
                                                                                         in
                                                                                           let
                                                                                             val (front, (frontpt, vis)) = a;
                                                                                           in
                                                                                             (fn () => ((front, (frontpt, fronti)), (vis, pari)))
                                                                                           end
                                                                                             ()
                                                                                         end);

fun wxb_loop (A1_, A2_) n gh state = (fn () => let
                                                 val b = bfs_cf_is_empty (zero_nat, equal_nat) (current state) ();
                                               in
                                                 (if b then (fn () => state) else (fn f_ => fn () => f_ ((wxb_round (A1_, A2_) n gh (current state) (visited state) (parent state)) ()) ()) (fn (currenta, (visiteda, parenta)) => let
                                                                                                                                                                                                                                     val d = current_dist state;
                                                                                                                                                                                                                                   in
                                                                                                                                                                                                                                     (fn f_ => fn () => f_ ((bfs_set_dists heap_nat (dists state) currenta (Int.+ (d, (1 : Int.int)))) ()) ()) (fn dist => wxb_loop (A1_, A2_) n gh (parent_update (fn _ => parenta) (current_dist_update (fn _ => Int.+ (d, (1 : Int.int))) (current_update (fn _ => currenta) (visited_update (fn _ => visiteda) (dists_update (fn _ => dist) state))))))
                                                                                                                                                                                                                                   end))
                                                   ()
                                               end);

fun wxb_init empty_vis src_imp imp_some_dist imp_some_par = (fn () => let
                                                                        val v = bfs_set_srcs_visited empty_vis src_imp ();
                                                                        val cf = bfs_src_to_cf src_imp ();
                                                                        val dists = bfs_set_dists heap_nat imp_some_dist cf (0 : Int.int) ();
                                                                      in
                                                                        BFS_state_imp_ext (dists, cf, v, (0 : Int.int), imp_some_par, ())
                                                                      end);

fun wxb_run (A1_, A2_) n gh empty_vis src_imp imp_some_dist imp_some_par = (fn () => let
                                                                                       val init = wxb_init empty_vis src_imp imp_some_dist imp_some_par ();
                                                                                       val final = wxb_loop (A1_, A2_) n gh init ();
                                                                                     in
                                                                                       (visited final, (dists final, parent final))
                                                                                     end);

fun wmx_tbfs_run (A1_, A2_) n gh = wxb_run (A1_, A2_) n gh;

fun tgt_imp smemb_imp ins2_imp si vi y = (fn () => let
                                                     val v = (fn () => Array.sub (vi, y)) ();
                                                   in
                                                     (if v then t_imp smemb_imp ins2_imp si y else (fn () => false)) ()
                                                   end);

fun wmx_wtgt (A1_, A2_) si vi c2 mT y = (fn () => let
                                                    val t = tgt_imp (fn i => bm_memb (id i)) (fn sia => fn i => bm_ins2 sia (id i)) si vi y ();
                                                  in
                                                    (if t then (fn f_ => fn () => f_ (((fn () => Array.sub (c2, y))) ()) ()) (fn z => (fn () => (eq A1_ z mT))) else (fn () => false)) ()
                                                  end);

fun wmx_thas_nb (A1_, A2_) n gh y = wmx_tnbs (A1_, A2_) n gh y (fn _ => fn _ => fn _ => (fn () => true)) false;

fun wmx_wsrc (A1_, A2_) n gh mS y = let
                                      val (si, (_, (c1, _))) = gh;
                                    in
                                      (fn () => let
                                                  val s = s_imp (fn i => bm_memb (id i)) (fn sia => fn i => bm_ins1 sia (id i)) si y ();
                                                in
                                                  (if s then (fn f_ => fn () => f_ (((fn () => Array.sub (c1, y))) ()) ()) (fn x => (if eq A1_ x mS then wmx_thas_nb (A1_, A2_) n gh y else (fn () => false))) else (fn () => false)) ()
                                                end)
                                    end;

fun wmx_drop (A1_, A2_) n gh mS vi = let
                                       val (si, (_, (c1, _))) = gh;
                                     in
                                       foldr_range_imp (fn y => fn _ => fn () => let
                                                                                   val s = s_imp (fn i => bm_memb (id i)) (fn sia => fn i => bm_ins1 sia (id i)) si y ();
                                                                                 in
                                                                                   (if s then (fn f_ => fn () => f_ (((fn () => Array.sub (c1, y))) ()) ()) (fn x => (if eq A1_ x mS then (fn f_ => fn () => f_ ((wmx_thas_nb (A1_, A2_) n gh y) ()) ()) (fn e => (if e then (fn () => ()) else (fn f_ => fn () => f_ (((fn () => Machine.upd (y, true, vi))) ()) ()) (fn _ => (fn () => ())))) else (fn () => ()))) else (fn () => ())) ()
                                                                                 end)
                                         n ()
                                     end;

fun st_imp smemb_imp ins1_imp ins2_imp si y = (fn () => let
                                                          val s = s_imp smemb_imp ins1_imp si y ();
                                                        in
                                                          (if s then ins2_imp si y else (fn () => false)) ()
                                                        end);

fun wmx_wst (A1_, A2_) (B1_, B2_) si c1 c2 mS mT y = (fn () => let
                                                                 val s = st_imp (fn i => bm_memb (id i)) (fn sia => fn i => bm_ins1 sia (id i)) (fn sia => fn i => bm_ins2 sia (id i)) si y ();
                                                               in
                                                                 (if s then (fn f_ => fn () => f_ (((fn () => Array.sub (c1, y))) ()) ()) (fn x => (if eq A1_ x mS then (fn f_ => fn () => f_ (((fn () => Array.sub (c2, y))) ()) ()) (fn z => (fn () => (eq B1_ z mT))) else (fn () => false))) else (fn () => false)) ()
                                                               end);

fun wmx_wsearch (A1_, A2_) n gc vi fr bf da pa si c1 c2 mS mT = (fn () => let
                                                                            val a = find_range_imp (wmx_wst (A1_, A2_) (A1_, A2_) si c1 c2 mS mT) (0 : Int.int) n ();
                                                                          in
                                                                            (case a of NONE => (fn f_ => fn () => f_ ((collect_range_imp (wmx_wsrc (A1_, A2_) n (si, (gc, (c1, c2))) mS) n fr) ()) ()) (fn k => (fn f_ => fn () => f_ ((xset_clear_imp n vi) ()) ()) (fn _ => (fn f_ => fn () => f_ ((if ((k : Int.int) = (0 : Int.int)) then (fn () => NONE) else (fn f_ => fn () => f_ ((fill_range_imp heap_nat id n da) ()) ()) (fn _ => (fn f_ => fn () => f_ ((fill_range_imp heap_nat id n pa) ()) ()) (fn _ => (fn f_ => fn () => f_ ((wmx_tbfs_run (A1_, A2_) n (si, (gc, (c1, c2))) vi (fr, (k, bf)) da pa) ()) ()) (fn _ => find_range_imp (wmx_wtgt (A1_, A2_) si vi c2 mT) (0 : Int.int) n)))) ()) ()) (fn aa => (case aa of NONE => (fn f_ => fn () => f_ ((wmx_drop (A1_, A2_) n (si, (gc, (c1, c2))) mS vi) ()) ()) (fn _ => (fn () => ((0 : Int.int), (0 : Int.int)))) | SOME t => (fn () => ((2 : Int.int), t)))))) | SOME s => (fn () => ((1 : Int.int), s))) ()
                                                                          end);

fun wmx_wtight_ctx (A1_, A2_, A3_, A4_) n gc vi fr bf da pa mi ti si c1 c2 = (fn () => let
                                                                                         val m1 = wmx_max (A3_, A4_) n (s_imp (fn i => bm_memb (id i)) (fn sia => fn i => bm_ins1 sia (id i)) si) c1 ();
                                                                                         val m2 = wmx_max (A3_, A4_) n (t_imp (fn i => bm_memb (id i)) (fn sia => fn i => bm_ins2 sia (id i)) si) c2 ();
                                                                                       in
                                                                                         let
                                                                                           val mS = (case m1 of NONE => zero A1_ | SOME x => x);
                                                                                           val mT = (case m2 of NONE => zero A1_ | SOME x => x);
                                                                                         in
                                                                                           (fn f_ => fn () => f_ (((fn () => Machine.upd ((0 : Int.int), mS, mi))) ()) ()) (fn _ => (fn f_ => fn () => f_ (((fn () => Machine.upd ((1 : Int.int), mT, mi))) ()) ()) (fn _ => (fn f_ => fn () => f_ ((wmx_wsearch (A2_, A3_) n gc vi fr bf da pa si c1 c2 mS mT) ()) ()) (fn t => (fn f_ => fn () => f_ (((fn () => Machine.upd ((0 : Int.int), fst t, ti))) ()) ()) (fn _ => (fn f_ => fn () => f_ (((fn () => Machine.upd ((1 : Int.int), snd t, ti))) ()) ()) (fn _ => (fn () => ()))))))
                                                                                         end
                                                                                           ()
                                                                                       end);

fun wmx_wctx_path da pa ti ra = (fn () => let
                                            val k = (fn () => Array.sub (ti, (0 : Int.int))) ();
                                            val v = (fn () => Array.sub (ti, (1 : Int.int))) ();
                                          in
                                            (if ((k : Int.int) = (1 : Int.int)) then (fn f_ => fn () => f_ (((fn () => Machine.upd ((0 : Int.int), v, ra))) ()) ()) (fn _ => (fn () => (SOME (1 : Int.int)))) else (if ((k : Int.int) = (2 : Int.int)) then (fn f_ => fn () => f_ ((bfs_path da pa ra v) ()) ()) (fn l => (fn () => (SOME l))) else (fn () => NONE))) ()
                                          end);

fun wmx_wshift (A1_, A2_) n vi e c = foldr_range_imp (fn i => fn _ => fn () => let
                                                                                 val r = (fn () => Array.sub (vi, i)) ();
                                                                               in
                                                                                 (if r then (fn f_ => fn () => f_ (((fn () => Array.sub (c, i))) ()) ()) (fn x => (fn f_ => fn () => f_ (((fn () => Machine.upd (i, plus A1_ x e, c))) ()) ()) (fn _ => (fn () => ()))) else (fn () => ())) ()
                                                                               end)
                                       n ();

fun wmx_czero (A1_, A2_) n c = (fn () => let
                                           val _ = fill_range_imp A2_ (fn _ => zero A1_) n c ();
                                         in
                                           ()
                                         end);

fun wmx_ccopy A_ n ca c = copy_range_imp A_ (fn a => (fn () => Array.sub (ca, a))) n c;

fun wmx_weps_step (A1_, A2_, A3_) n gc vi si c1 c2 mS mT u a = (fn () => let
                                                                           val r = (fn () => Array.sub (vi, u)) ();
                                                                           val b = bm_memb (id u) si ();
                                                                           val a1 = (if r then xnbs n (fn i => bm_memb (id i)) (fn sia => fn i => bm_ins1 sia (id i)) (fn sia => fn i => fn j => bm_exch1 sia (id i) (id j)) (fn sia => fn i => bm_ins2 sia (id i)) (fn sia => fn i => fn j => bm_exch2 sia (id i) (id j)) (si, gc) u (wmx_gap (A1_, A2_, A3_) c1 c2 b vi) a else (fn () => a)) ();
                                                                           val s = s_imp (fn i => bm_memb (id i)) (fn sia => fn i => bm_ins1 sia (id i)) si u ();
                                                                           val a2 = (if s andalso not r then (fn f_ => fn () => f_ (((fn () => Array.sub (c1, u))) ()) ()) (fn x => (fn () => (eps_min A3_ a1 (minus A1_ mS x)))) else (fn () => a1)) ();
                                                                           val t = t_imp (fn i => bm_memb (id i)) (fn sia => fn i => bm_ins2 sia (id i)) si u ();
                                                                         in
                                                                           (if t andalso r then (fn f_ => fn () => f_ (((fn () => Array.sub (c2, u))) ()) ()) (fn x => (fn () => (eps_min A3_ a2 (minus A1_ mT x)))) else (fn () => a2)) ()
                                                                         end);

fun wmx_weps (A1_, A2_, A3_) n gc vi mi si c1 c2 = (fn () => let
                                                               val mS = (fn () => Array.sub (mi, (0 : Int.int))) ();
                                                               val mT = (fn () => Array.sub (mi, (1 : Int.int))) ();
                                                             in
                                                               foldr_range_imp (wmx_weps_step (A1_, A2_, A3_) n gc vi si c1 c2 mS mT) n NONE ()
                                                             end);

fun wmx_wmi_ids (A1_, A2_, A3_) n h1 h2 si co c1 c2 =
  (fn () => let
              val gc = cand_csr_imp (fn h => fn i => part_npts_imp h (id i)) (pt_ids_imp id id part_pt_imp) (fn h => fn i => part_npts_imp h (id i)) (pt_ids_imp id id part_pt_imp) h1 h2 n ();
              val vi = (fn () => Array.array (n, false)) ();
              val fr = (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
              val bf = (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
              val da = (fn () => Array.array (n, (0 : Int.int))) ();
              val pa = (fn () => Array.array (n, (0 : Int.int))) ();
              val ra = (fn () => Array.array (n, (0 : Int.int))) ();
              val mi = (fn () => Array.array ((2 : Int.int), zero ((zero_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_))) ();
              val ti = (fn () => Array.array ((2 : Int.int), (0 : Int.int))) ();
            in
              wmi_run_imp (A2_, A3_) (fn i => bm_ins (id i)) (fn i => bm_del (id i)) (fn a => fn b => (fn () => Array.sub (a, b))) (wmx_ccopy A2_ n) (wmx_czero ((zero_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_, A2_) n) (wmx_wtight_ctx ((zero_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_, A1_, A2_, (ord_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_) n gc vi fr bf da pa mi ti) (wmx_wctx_path da pa ti) (wmx_weps ((minus_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_, A2_, (ord_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_) n gc vi mi)
                (wmx_wshift ((plus_semigroup_add o semigroup_add_numeral o numeral_neg_numeral o neg_numeral_ring_1 o ring_1_ring_char_0 o ring_char_0_linordered_idom) A3_, A2_) n vi) si co c1 c2 ra ()
            end);

fun wmx_wmi (A1_, A2_, A3_) n h1 h2 si co c1 c2 = wmx_wmi_ids (A1_, A2_, A3_) n h1 h2 si co c1 c2;

fun wbx_gap (A1_, A2_, A3_) c1 c2 b vi = (fn u => fn v => fn a => fn () => let
                                                                             val r = (fn () => Array.sub (vi, v)) ();
                                                                           in
                                                                             (if r then (fn () => a) else (fn f_ => fn () => f_ ((if b then (fn f_ => fn () => f_ (((fn () => Array.sub (c1, u))) ()) ()) (fn x => (fn f_ => fn () => f_ (((fn () => Array.sub (c1, v))) ()) ()) (fn y => (fn () => (minus A1_ x y)))) else (fn f_ => fn () => f_ (((fn () => Array.sub (c2, v))) ()) ()) (fn x => (fn f_ => fn () => f_ (((fn () => Array.sub (c2, u))) ()) ()) (fn y => (fn () => (minus A1_ x y))))) ()) ()) (fn g => (fn () => (eps_min A3_ a g)))) ()
                                                                           end);

fun wbx_max (A1_, A2_) n p c = foldr_range_imp (fn y => fn a => fn () => let
                                                                           val pa = p y ();
                                                                         in
                                                                           (if pa then (fn f_ => fn () => f_ (((fn () => Array.sub (c, y))) ()) ()) (fn x => (fn () => (SOME (case a of NONE => x | SOME w => max A2_ w x)))) else (fn () => a)) ()
                                                                         end)
                                 n NONE;

fun wbx_teq (A1_, A2_) c cu = (fn _ => fn _ => fn v => fn () => let
                                                                  val cv = (fn () => Array.sub (c, v)) ();
                                                                in
                                                                  eq A1_ cu cv
                                                                end);

fun wbx_tnbs (A1_, A2_) n gh u fi acc = let
                                          val (si, (gc, (c1, c2))) = gh;
                                        in
                                          (if Int.< (u, n) then (fn () => let
                                                                            val b = bb_memb (id u) si ();
                                                                            val cu = (fn () => Array.sub ((if b then c1 else c2), u)) ();
                                                                          in
                                                                            xnbs n (fn i => bb_memb (id i)) (fn sia => fn i => bb_ins1 sia (id i)) (fn sia => fn i => fn j => bb_exch1 sia (id i) (id j)) (fn sia => fn i => bb_ins2 sia (id i)) (fn sia => fn i => fn j => bb_exch2 sia (id i) (id j)) (si, gc) u (filt_imp (wbx_teq (A1_, A2_) (if b then c1 else c2) cu) si fi) acc ()
                                                                          end)
                                            else (fn () => acc))
                                        end;

fun wxbb_inner (A1_, A2_) n gi pari u (front, (frontpt, vis)) = wbx_tnbs (A1_, A2_) n gi u (fn ua => fn v => fn (fronta, (frontpta, visa)) => fn () => let
                                                                                                                                                         val b = bset_memb v visa ();
                                                                                                                                                       in
                                                                                                                                                         (if not b then (fn f_ => fn () => f_ (((fn () => Machine.upd (frontpta, v, fronta))) ()) ()) (fn frontb => (fn f_ => fn () => f_ ((bset_ins v visa) ()) ()) (fn visb => (fn f_ => fn () => f_ (((fn () => Machine.upd (v, ua, pari))) ()) ()) (fn _ => (fn () => (frontb, (Int.+ (frontpta, (1 : Int.int)), visb)))))) else (fn () => (fronta, (frontpta, visa)))) ()
                                                                                                                                                       end)
                                                                  (front, (frontpt, vis));

fun wxbb_outer (A1_, A2_) n gi pari (old_front, old_frontp) (front, (frontpt, vis)) = iterate_range_strict heap_nat old_front (0 : Int.int) old_frontp (wxbb_inner (A1_, A2_) n gi pari) (front, (frontpt, vis));

fun wxbb_round (A1_, A2_) n gi (fronti, (frontp, buffer_fronti)) imp_vis pari = (fn () => let
                                                                                            val a = wxbb_outer (A1_, A2_) n gi pari (fronti, frontp) (buffer_fronti, ((0 : Int.int), imp_vis)) ();
                                                                                          in
                                                                                            let
                                                                                              val (front, (frontpt, vis)) = a;
                                                                                            in
                                                                                              (fn () => ((front, (frontpt, fronti)), (vis, pari)))
                                                                                            end
                                                                                              ()
                                                                                          end);

fun wxbb_loop (A1_, A2_) n gh state = (fn () => let
                                                  val b = bfs_cf_is_empty (zero_nat, equal_nat) (current state) ();
                                                in
                                                  (if b then (fn () => state) else (fn f_ => fn () => f_ ((wxbb_round (A1_, A2_) n gh (current state) (visited state) (parent state)) ()) ()) (fn (currenta, (visiteda, parenta)) => let
                                                                                                                                                                                                                                       val d = current_dist state;
                                                                                                                                                                                                                                     in
                                                                                                                                                                                                                                       (fn f_ => fn () => f_ ((bfs_set_dists heap_nat (dists state) currenta (Int.+ (d, (1 : Int.int)))) ()) ()) (fn dist => wxbb_loop (A1_, A2_) n gh (parent_update (fn _ => parenta) (current_dist_update (fn _ => Int.+ (d, (1 : Int.int))) (current_update (fn _ => currenta) (visited_update (fn _ => visiteda) (dists_update (fn _ => dist) state))))))
                                                                                                                                                                                                                                     end))
                                                    ()
                                                end);

fun wxbb_init empty_vis src_imp imp_some_dist imp_some_par = (fn () => let
                                                                         val v = bfs_set_srcs_visited empty_vis src_imp ();
                                                                         val cf = bfs_src_to_cf src_imp ();
                                                                         val dists = bfs_set_dists heap_nat imp_some_dist cf (0 : Int.int) ();
                                                                       in
                                                                         BFS_state_imp_ext (dists, cf, v, (0 : Int.int), imp_some_par, ())
                                                                       end);

fun wxbb_run (A1_, A2_) n gh empty_vis src_imp imp_some_dist imp_some_par = (fn () => let
                                                                                        val init = wxbb_init empty_vis src_imp imp_some_dist imp_some_par ();
                                                                                        val final = wxbb_loop (A1_, A2_) n gh init ();
                                                                                      in
                                                                                        (visited final, (dists final, parent final))
                                                                                      end);

fun wbx_tbfs_run (A1_, A2_) n gh = wxbb_run (A1_, A2_) n gh;

fun wbx_wtgt (A1_, A2_) si vi c2 mT y = (fn () => let
                                                    val t = tgt_imp (fn i => bb_memb (id i)) (fn sia => fn i => bb_ins2 sia (id i)) si vi y ();
                                                  in
                                                    (if t then (fn f_ => fn () => f_ (((fn () => Array.sub (c2, y))) ()) ()) (fn z => (fn () => (eq A1_ z mT))) else (fn () => false)) ()
                                                  end);

fun wbx_thas_nb (A1_, A2_) n gh y = wbx_tnbs (A1_, A2_) n gh y (fn _ => fn _ => fn _ => (fn () => true)) false;

fun wbx_wsrc (A1_, A2_) n gh mS y = let
                                      val (si, (_, (c1, _))) = gh;
                                    in
                                      (fn () => let
                                                  val s = s_imp (fn i => bb_memb (id i)) (fn sia => fn i => bb_ins1 sia (id i)) si y ();
                                                in
                                                  (if s then (fn f_ => fn () => f_ (((fn () => Array.sub (c1, y))) ()) ()) (fn x => (if eq A1_ x mS then wbx_thas_nb (A1_, A2_) n gh y else (fn () => false))) else (fn () => false)) ()
                                                end)
                                    end;

fun wbx_drop (A1_, A2_) n gh mS vi = let
                                       val (si, (_, (c1, _))) = gh;
                                     in
                                       foldr_range_imp (fn y => fn _ => fn () => let
                                                                                   val s = s_imp (fn i => bb_memb (id i)) (fn sia => fn i => bb_ins1 sia (id i)) si y ();
                                                                                 in
                                                                                   (if s then (fn f_ => fn () => f_ (((fn () => Array.sub (c1, y))) ()) ()) (fn x => (if eq A1_ x mS then (fn f_ => fn () => f_ ((wbx_thas_nb (A1_, A2_) n gh y) ()) ()) (fn e => (if e then (fn () => ()) else (fn f_ => fn () => f_ (((fn () => Machine.upd (y, true, vi))) ()) ()) (fn _ => (fn () => ())))) else (fn () => ()))) else (fn () => ())) ()
                                                                                 end)
                                         n ()
                                     end;

fun wbx_wst (A1_, A2_) (B1_, B2_) si c1 c2 mS mT y = (fn () => let
                                                                 val s = st_imp (fn i => bb_memb (id i)) (fn sia => fn i => bb_ins1 sia (id i)) (fn sia => fn i => bb_ins2 sia (id i)) si y ();
                                                               in
                                                                 (if s then (fn f_ => fn () => f_ (((fn () => Array.sub (c1, y))) ()) ()) (fn x => (if eq A1_ x mS then (fn f_ => fn () => f_ (((fn () => Array.sub (c2, y))) ()) ()) (fn z => (fn () => (eq B1_ z mT))) else (fn () => false))) else (fn () => false)) ()
                                                               end);

fun wbx_wsearch (A1_, A2_) n gc vi fr bf da pa si c1 c2 mS mT = (fn () => let
                                                                            val a = find_range_imp (wbx_wst (A1_, A2_) (A1_, A2_) si c1 c2 mS mT) (0 : Int.int) n ();
                                                                          in
                                                                            (case a of NONE => (fn f_ => fn () => f_ ((collect_range_imp (wbx_wsrc (A1_, A2_) n (si, (gc, (c1, c2))) mS) n fr) ()) ()) (fn k => (fn f_ => fn () => f_ ((xset_clear_imp n vi) ()) ()) (fn _ => (fn f_ => fn () => f_ ((if ((k : Int.int) = (0 : Int.int)) then (fn () => NONE) else (fn f_ => fn () => f_ ((fill_range_imp heap_nat id n da) ()) ()) (fn _ => (fn f_ => fn () => f_ ((fill_range_imp heap_nat id n pa) ()) ()) (fn _ => (fn f_ => fn () => f_ ((wbx_tbfs_run (A1_, A2_) n (si, (gc, (c1, c2))) vi (fr, (k, bf)) da pa) ()) ()) (fn _ => find_range_imp (wbx_wtgt (A1_, A2_) si vi c2 mT) (0 : Int.int) n)))) ()) ()) (fn aa => (case aa of NONE => (fn f_ => fn () => f_ ((wbx_drop (A1_, A2_) n (si, (gc, (c1, c2))) mS vi) ()) ()) (fn _ => (fn () => ((0 : Int.int), (0 : Int.int)))) | SOME t => (fn () => ((2 : Int.int), t)))))) | SOME s => (fn () => ((1 : Int.int), s))) ()
                                                                          end);

fun wbx_wtight_ctx (A1_, A2_, A3_, A4_) n gc vi fr bf da pa mi ti si c1 c2 = (fn () => let
                                                                                         val m1 = wbx_max (A3_, A4_) n (s_imp (fn i => bb_memb (id i)) (fn sia => fn i => bb_ins1 sia (id i)) si) c1 ();
                                                                                         val m2 = wbx_max (A3_, A4_) n (t_imp (fn i => bb_memb (id i)) (fn sia => fn i => bb_ins2 sia (id i)) si) c2 ();
                                                                                       in
                                                                                         let
                                                                                           val mS = (case m1 of NONE => zero A1_ | SOME x => x);
                                                                                           val mT = (case m2 of NONE => zero A1_ | SOME x => x);
                                                                                         in
                                                                                           (fn f_ => fn () => f_ (((fn () => Machine.upd ((0 : Int.int), mS, mi))) ()) ()) (fn _ => (fn f_ => fn () => f_ (((fn () => Machine.upd ((1 : Int.int), mT, mi))) ()) ()) (fn _ => (fn f_ => fn () => f_ ((wbx_wsearch (A2_, A3_) n gc vi fr bf da pa si c1 c2 mS mT) ()) ()) (fn t => (fn f_ => fn () => f_ (((fn () => Machine.upd ((0 : Int.int), fst t, ti))) ()) ()) (fn _ => (fn f_ => fn () => f_ (((fn () => Machine.upd ((1 : Int.int), snd t, ti))) ()) ()) (fn _ => (fn () => ()))))))
                                                                                         end
                                                                                           ()
                                                                                       end);

fun wbx_wctx_path da pa ti ra = (fn () => let
                                            val k = (fn () => Array.sub (ti, (0 : Int.int))) ();
                                            val v = (fn () => Array.sub (ti, (1 : Int.int))) ();
                                          in
                                            (if ((k : Int.int) = (1 : Int.int)) then (fn f_ => fn () => f_ (((fn () => Machine.upd ((0 : Int.int), v, ra))) ()) ()) (fn _ => (fn () => (SOME (1 : Int.int)))) else (if ((k : Int.int) = (2 : Int.int)) then (fn f_ => fn () => f_ ((bfs_path da pa ra v) ()) ()) (fn l => (fn () => (SOME l))) else (fn () => NONE))) ()
                                          end);

fun wbx_wshift (A1_, A2_) n vi e c = foldr_range_imp (fn i => fn _ => fn () => let
                                                                                 val r = (fn () => Array.sub (vi, i)) ();
                                                                               in
                                                                                 (if r then (fn f_ => fn () => f_ (((fn () => Array.sub (c, i))) ()) ()) (fn x => (fn f_ => fn () => f_ (((fn () => Machine.upd (i, plus A1_ x e, c))) ()) ()) (fn _ => (fn () => ()))) else (fn () => ())) ()
                                                                               end)
                                       n ();

fun wbx_czero (A1_, A2_) n c = (fn () => let
                                           val _ = fill_range_imp A2_ (fn _ => zero A1_) n c ();
                                         in
                                           ()
                                         end);

fun wbx_ccopy A_ n ca c = copy_range_imp A_ (fn a => (fn () => Array.sub (ca, a))) n c;

fun wbx_weps_step (A1_, A2_, A3_) n gc vi si c1 c2 mS mT u a = (fn () => let
                                                                           val r = (fn () => Array.sub (vi, u)) ();
                                                                           val b = bb_memb (id u) si ();
                                                                           val a1 = (if r then xnbs n (fn i => bb_memb (id i)) (fn sia => fn i => bb_ins1 sia (id i)) (fn sia => fn i => fn j => bb_exch1 sia (id i) (id j)) (fn sia => fn i => bb_ins2 sia (id i)) (fn sia => fn i => fn j => bb_exch2 sia (id i) (id j)) (si, gc) u (wbx_gap (A1_, A2_, A3_) c1 c2 b vi) a else (fn () => a)) ();
                                                                           val s = s_imp (fn i => bb_memb (id i)) (fn sia => fn i => bb_ins1 sia (id i)) si u ();
                                                                           val a2 = (if s andalso not r then (fn f_ => fn () => f_ (((fn () => Array.sub (c1, u))) ()) ()) (fn x => (fn () => (eps_min A3_ a1 (minus A1_ mS x)))) else (fn () => a1)) ();
                                                                           val t = t_imp (fn i => bb_memb (id i)) (fn sia => fn i => bb_ins2 sia (id i)) si u ();
                                                                         in
                                                                           (if t andalso r then (fn f_ => fn () => f_ (((fn () => Array.sub (c2, u))) ()) ()) (fn x => (fn () => (eps_min A3_ a2 (minus A1_ mT x)))) else (fn () => a2)) ()
                                                                         end);

fun wbx_weps (A1_, A2_, A3_) n gc vi mi si c1 c2 = (fn () => let
                                                               val mS = (fn () => Array.sub (mi, (0 : Int.int))) ();
                                                               val mT = (fn () => Array.sub (mi, (1 : Int.int))) ();
                                                             in
                                                               foldr_range_imp (wbx_weps_step (A1_, A2_, A3_) n gc vi si c1 c2 mS mT) n NONE ()
                                                             end);

fun wbx_wmi_ids (A1_, A2_, A3_) n h1 h2 si co c1 c2 =
  (fn () => let
              val gc = cand_csr_imp (fn h => fn i => part_npts_imp h (id i)) (pt_ids_imp id id part_pt_imp) (fn h => fn i => part_npts_imp h (id i)) (pt_ids_imp id id part_pt_imp) h1 h2 n ();
              val vi = (fn () => Array.array (n, false)) ();
              val fr = (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
              val bf = (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
              val da = (fn () => Array.array (n, (0 : Int.int))) ();
              val pa = (fn () => Array.array (n, (0 : Int.int))) ();
              val ra = (fn () => Array.array (n, (0 : Int.int))) ();
              val mi = (fn () => Array.array ((2 : Int.int), zero ((zero_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_))) ();
              val ti = (fn () => Array.array ((2 : Int.int), (0 : Int.int))) ();
            in
              wmi_run_imp (A2_, A3_) (fn i => bb_ins (id i)) (fn i => bb_del (id i)) (fn a => fn b => (fn () => Array.sub (a, b))) (wbx_ccopy A2_ n) (wbx_czero ((zero_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_, A2_) n) (wbx_wtight_ctx ((zero_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_, A1_, A2_, (ord_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_) n gc vi fr bf da pa mi ti) (wbx_wctx_path da pa ti) (wbx_weps ((minus_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_, A2_, (ord_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_) n gc vi mi)
                (wbx_wshift ((plus_semigroup_add o semigroup_add_numeral o numeral_neg_numeral o neg_numeral_ring_1 o ring_1_ring_char_0 o ring_char_0_linordered_idom) A3_, A2_) n vi) si co c1 c2 ra ()
            end);

fun wbx_wmi (A1_, A2_, A3_) n h1 h2 si co c1 c2 = wbx_wmi_ids (A1_, A2_, A3_) n h1 h2 si co c1 c2;

fun weighted_matching_imp (A1_, A2_, A3_) nv fa ta wa = bm_setup_imp (zero_nat, heap_nat) (zero_nat, heap_nat) nv fa ta (fn m => fn h1 => fn h2 => fn xi => fn c1 => fn c2 => fn () => let
                                                                                                                                                                                         val w1 = (fn () => Array.array (m, zero ((zero_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_))) ();
                                                                                                                                                                                         val w2 = (fn () => Array.array (m, zero ((zero_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_))) ();
                                                                                                                                                                                         val _ = wmx_wmi (A1_, A2_, A3_) m h1 h2 (xi, (c1, (c2, (fa, ta)))) wa w1 w2 ();
                                                                                                                                                                                       in
                                                                                                                                                                                         xi
                                                                                                                                                                                       end);

fun weighted_b_matching_imp (A1_, A2_, A3_) fa ta ka wa = bb_setup_imp heap_nat (zero_nat, heap_nat) (zero_nat, heap_nat) fa ta ka (fn m => fn h1 => fn h2 => fn xi => fn c1 => fn c2 => fn () => let
                                                                                                                                                                                                    val w1 = (fn () => Array.array (m, zero ((zero_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_))) ();
                                                                                                                                                                                                    val w2 = (fn () => Array.array (m, zero ((zero_abs_if o abs_if_linordered_ring o linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom) A3_))) ();
                                                                                                                                                                                                    val _ = wbx_wmi (A1_, A2_, A3_) m h1 h2 (xi, (c1, (c2, (fa, (ta, ka))))) wa w1 w2 ();
                                                                                                                                                                                                  in
                                                                                                                                                                                                    xi
                                                                                                                                                                                                  end);

fun weighted_matching_int_imp nv fa ta wa = weighted_matching_imp (equal_int, heap_int, linordered_idom_int) nv fa ta wa;

fun weighted_b_matching_int_imp fa ta ka wa = weighted_b_matching_imp (equal_int, heap_int, linordered_idom_int) fa ta ka wa;

end; (*struct Bipartite_Matching*)
