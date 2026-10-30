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


structure Push_Relabel : sig
  val push_relabel_hl_run_int :
    Int.int ->
      Int.int ->
        Int.int ->
          Int.int array ->
            Int.int array -> Int.int array -> (unit -> (Int.int array))
  val push_relabel_rtf_run_int :
    Int.int ->
      Int.int ->
        Int.int ->
          Int.int array ->
            Int.int array -> Int.int array -> (unit -> (Int.int array))
  val push_relabel_fifo_run_int :
    Int.int ->
      Int.int ->
        Int.int ->
          Int.int array ->
            Int.int array -> Int.int array -> (unit -> (Int.int array))
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

fun sgn_inta i =
  (if ((i : Int.int) = (0 : Int.int)) then (0 : Int.int)
    else (if Int.< ((0 : Int.int), i) then (1 : Int.int)
           else Int.~ (1 : Int.int)));

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

type 'a cancel_semigroup_add =
  {semigroup_add_cancel_semigroup_add : 'a semigroup_add};
val semigroup_add_cancel_semigroup_add = #semigroup_add_cancel_semigroup_add :
  'a cancel_semigroup_add -> 'a semigroup_add;

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

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

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

type 'a mult_zero = {times_mult_zero : 'a times, zero_mult_zero : 'a zero};
val times_mult_zero = #times_mult_zero : 'a mult_zero -> 'a times;
val zero_mult_zero = #zero_mult_zero : 'a mult_zero -> 'a zero;

type 'a semigroup_mult = {times_semigroup_mult : 'a times};
val times_semigroup_mult = #times_semigroup_mult :
  'a semigroup_mult -> 'a times;

type 'a semiring =
  {ab_semigroup_add_semiring : 'a ab_semigroup_add,
    semigroup_mult_semiring : 'a semigroup_mult};
val ab_semigroup_add_semiring = #ab_semigroup_add_semiring :
  'a semiring -> 'a ab_semigroup_add;
val semigroup_mult_semiring = #semigroup_mult_semiring :
  'a semiring -> 'a semigroup_mult;

type 'a semiring_0 =
  {comm_monoid_add_semiring_0 : 'a comm_monoid_add,
    mult_zero_semiring_0 : 'a mult_zero, semiring_semiring_0 : 'a semiring};
val comm_monoid_add_semiring_0 = #comm_monoid_add_semiring_0 :
  'a semiring_0 -> 'a comm_monoid_add;
val mult_zero_semiring_0 = #mult_zero_semiring_0 :
  'a semiring_0 -> 'a mult_zero;
val semiring_semiring_0 = #semiring_semiring_0 : 'a semiring_0 -> 'a semiring;

type 'a semiring_0_cancel =
  {cancel_comm_monoid_add_semiring_0_cancel : 'a cancel_comm_monoid_add,
    semiring_0_semiring_0_cancel : 'a semiring_0};
val cancel_comm_monoid_add_semiring_0_cancel =
  #cancel_comm_monoid_add_semiring_0_cancel :
  'a semiring_0_cancel -> 'a cancel_comm_monoid_add;
val semiring_0_semiring_0_cancel = #semiring_0_semiring_0_cancel :
  'a semiring_0_cancel -> 'a semiring_0;

type 'a ab_semigroup_mult =
  {semigroup_mult_ab_semigroup_mult : 'a semigroup_mult};
val semigroup_mult_ab_semigroup_mult = #semigroup_mult_ab_semigroup_mult :
  'a ab_semigroup_mult -> 'a semigroup_mult;

type 'a comm_semiring =
  {ab_semigroup_mult_comm_semiring : 'a ab_semigroup_mult,
    semiring_comm_semiring : 'a semiring};
val ab_semigroup_mult_comm_semiring = #ab_semigroup_mult_comm_semiring :
  'a comm_semiring -> 'a ab_semigroup_mult;
val semiring_comm_semiring = #semiring_comm_semiring :
  'a comm_semiring -> 'a semiring;

type 'a comm_semiring_0 =
  {comm_semiring_comm_semiring_0 : 'a comm_semiring,
    semiring_0_comm_semiring_0 : 'a semiring_0};
val comm_semiring_comm_semiring_0 = #comm_semiring_comm_semiring_0 :
  'a comm_semiring_0 -> 'a comm_semiring;
val semiring_0_comm_semiring_0 = #semiring_0_comm_semiring_0 :
  'a comm_semiring_0 -> 'a semiring_0;

type 'a comm_semiring_0_cancel =
  {comm_semiring_0_comm_semiring_0_cancel : 'a comm_semiring_0,
    semiring_0_cancel_comm_semiring_0_cancel : 'a semiring_0_cancel};
val comm_semiring_0_comm_semiring_0_cancel =
  #comm_semiring_0_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a comm_semiring_0;
val semiring_0_cancel_comm_semiring_0_cancel =
  #semiring_0_cancel_comm_semiring_0_cancel :
  'a comm_semiring_0_cancel -> 'a semiring_0_cancel;

type 'a power = {one_power : 'a one, times_power : 'a times};
val one_power = #one_power : 'a power -> 'a one;
val times_power = #times_power : 'a power -> 'a times;

type 'a monoid_mult =
  {semigroup_mult_monoid_mult : 'a semigroup_mult,
    power_monoid_mult : 'a power};
val semigroup_mult_monoid_mult = #semigroup_mult_monoid_mult :
  'a monoid_mult -> 'a semigroup_mult;
val power_monoid_mult = #power_monoid_mult : 'a monoid_mult -> 'a power;

type 'a numeral =
  {one_numeral : 'a one, semigroup_add_numeral : 'a semigroup_add};
val one_numeral = #one_numeral : 'a numeral -> 'a one;
val semigroup_add_numeral = #semigroup_add_numeral :
  'a numeral -> 'a semigroup_add;

type 'a semiring_numeral =
  {monoid_mult_semiring_numeral : 'a monoid_mult,
    numeral_semiring_numeral : 'a numeral,
    semiring_semiring_numeral : 'a semiring};
val monoid_mult_semiring_numeral = #monoid_mult_semiring_numeral :
  'a semiring_numeral -> 'a monoid_mult;
val numeral_semiring_numeral = #numeral_semiring_numeral :
  'a semiring_numeral -> 'a numeral;
val semiring_semiring_numeral = #semiring_semiring_numeral :
  'a semiring_numeral -> 'a semiring;

type 'a zero_neq_one = {one_zero_neq_one : 'a one, zero_zero_neq_one : 'a zero};
val one_zero_neq_one = #one_zero_neq_one : 'a zero_neq_one -> 'a one;
val zero_zero_neq_one = #zero_zero_neq_one : 'a zero_neq_one -> 'a zero;

type 'a semiring_1 =
  {semiring_numeral_semiring_1 : 'a semiring_numeral,
    semiring_0_semiring_1 : 'a semiring_0,
    zero_neq_one_semiring_1 : 'a zero_neq_one};
val semiring_numeral_semiring_1 = #semiring_numeral_semiring_1 :
  'a semiring_1 -> 'a semiring_numeral;
val semiring_0_semiring_1 = #semiring_0_semiring_1 :
  'a semiring_1 -> 'a semiring_0;
val zero_neq_one_semiring_1 = #zero_neq_one_semiring_1 :
  'a semiring_1 -> 'a zero_neq_one;

type 'a semiring_1_cancel =
  {semiring_0_cancel_semiring_1_cancel : 'a semiring_0_cancel,
    semiring_1_semiring_1_cancel : 'a semiring_1};
val semiring_0_cancel_semiring_1_cancel = #semiring_0_cancel_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_0_cancel;
val semiring_1_semiring_1_cancel = #semiring_1_semiring_1_cancel :
  'a semiring_1_cancel -> 'a semiring_1;

type 'a comm_monoid_mult =
  {ab_semigroup_mult_comm_monoid_mult : 'a ab_semigroup_mult,
    monoid_mult_comm_monoid_mult : 'a monoid_mult,
    dvd_comm_monoid_mult : 'a dvd};
val ab_semigroup_mult_comm_monoid_mult = #ab_semigroup_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a ab_semigroup_mult;
val monoid_mult_comm_monoid_mult = #monoid_mult_comm_monoid_mult :
  'a comm_monoid_mult -> 'a monoid_mult;
val dvd_comm_monoid_mult = #dvd_comm_monoid_mult :
  'a comm_monoid_mult -> 'a dvd;

type 'a comm_semiring_1 =
  {comm_monoid_mult_comm_semiring_1 : 'a comm_monoid_mult,
    comm_semiring_0_comm_semiring_1 : 'a comm_semiring_0,
    semiring_1_comm_semiring_1 : 'a semiring_1};
val comm_monoid_mult_comm_semiring_1 = #comm_monoid_mult_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_monoid_mult;
val comm_semiring_0_comm_semiring_1 = #comm_semiring_0_comm_semiring_1 :
  'a comm_semiring_1 -> 'a comm_semiring_0;
val semiring_1_comm_semiring_1 = #semiring_1_comm_semiring_1 :
  'a comm_semiring_1 -> 'a semiring_1;

type 'a comm_semiring_1_cancel =
  {comm_semiring_0_cancel_comm_semiring_1_cancel : 'a comm_semiring_0_cancel,
    comm_semiring_1_comm_semiring_1_cancel : 'a comm_semiring_1,
    semiring_1_cancel_comm_semiring_1_cancel : 'a semiring_1_cancel};
val comm_semiring_0_cancel_comm_semiring_1_cancel =
  #comm_semiring_0_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_0_cancel;
val comm_semiring_1_comm_semiring_1_cancel =
  #comm_semiring_1_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a comm_semiring_1;
val semiring_1_cancel_comm_semiring_1_cancel =
  #semiring_1_cancel_comm_semiring_1_cancel :
  'a comm_semiring_1_cancel -> 'a semiring_1_cancel;

type 'a comm_semiring_1_cancel_crossproduct =
  {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct :
     'a comm_semiring_1_cancel};
val comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct =
  #comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct :
  'a comm_semiring_1_cancel_crossproduct -> 'a comm_semiring_1_cancel;

type 'a semiring_no_zero_divisors =
  {semiring_0_semiring_no_zero_divisors : 'a semiring_0};
val semiring_0_semiring_no_zero_divisors = #semiring_0_semiring_no_zero_divisors
  : 'a semiring_no_zero_divisors -> 'a semiring_0;

type 'a semiring_1_no_zero_divisors =
  {semiring_1_semiring_1_no_zero_divisors : 'a semiring_1,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors :
      'a semiring_no_zero_divisors};
val semiring_1_semiring_1_no_zero_divisors =
  #semiring_1_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_1;
val semiring_no_zero_divisors_semiring_1_no_zero_divisors =
  #semiring_no_zero_divisors_semiring_1_no_zero_divisors :
  'a semiring_1_no_zero_divisors -> 'a semiring_no_zero_divisors;

type 'a semiring_no_zero_divisors_cancel =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
     'a semiring_no_zero_divisors};
val semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
  #semiring_no_zero_divisors_semiring_no_zero_divisors_cancel :
  'a semiring_no_zero_divisors_cancel -> 'a semiring_no_zero_divisors;

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

type 'a ab_group_add =
  {cancel_comm_monoid_add_ab_group_add : 'a cancel_comm_monoid_add,
    group_add_ab_group_add : 'a group_add};
val cancel_comm_monoid_add_ab_group_add = #cancel_comm_monoid_add_ab_group_add :
  'a ab_group_add -> 'a cancel_comm_monoid_add;
val group_add_ab_group_add = #group_add_ab_group_add :
  'a ab_group_add -> 'a group_add;

type 'a ring =
  {ab_group_add_ring : 'a ab_group_add,
    semiring_0_cancel_ring : 'a semiring_0_cancel};
val ab_group_add_ring = #ab_group_add_ring : 'a ring -> 'a ab_group_add;
val semiring_0_cancel_ring = #semiring_0_cancel_ring :
  'a ring -> 'a semiring_0_cancel;

type 'a ring_no_zero_divisors =
  {ring_ring_no_zero_divisors : 'a ring,
    semiring_no_zero_divisors_cancel_ring_no_zero_divisors :
      'a semiring_no_zero_divisors_cancel};
val ring_ring_no_zero_divisors = #ring_ring_no_zero_divisors :
  'a ring_no_zero_divisors -> 'a ring;
val semiring_no_zero_divisors_cancel_ring_no_zero_divisors =
  #semiring_no_zero_divisors_cancel_ring_no_zero_divisors :
  'a ring_no_zero_divisors -> 'a semiring_no_zero_divisors_cancel;

type 'a neg_numeral =
  {group_add_neg_numeral : 'a group_add, numeral_neg_numeral : 'a numeral};
val group_add_neg_numeral = #group_add_neg_numeral :
  'a neg_numeral -> 'a group_add;
val numeral_neg_numeral = #numeral_neg_numeral : 'a neg_numeral -> 'a numeral;

type 'a ring_1 =
  {neg_numeral_ring_1 : 'a neg_numeral, ring_ring_1 : 'a ring,
    semiring_1_cancel_ring_1 : 'a semiring_1_cancel};
val neg_numeral_ring_1 = #neg_numeral_ring_1 : 'a ring_1 -> 'a neg_numeral;
val ring_ring_1 = #ring_ring_1 : 'a ring_1 -> 'a ring;
val semiring_1_cancel_ring_1 = #semiring_1_cancel_ring_1 :
  'a ring_1 -> 'a semiring_1_cancel;

type 'a ring_1_no_zero_divisors =
  {ring_1_ring_1_no_zero_divisors : 'a ring_1,
    ring_no_zero_divisors_ring_1_no_zero_divisors : 'a ring_no_zero_divisors,
    semiring_1_no_zero_divisors_ring_1_no_zero_divisors :
      'a semiring_1_no_zero_divisors};
val ring_1_ring_1_no_zero_divisors = #ring_1_ring_1_no_zero_divisors :
  'a ring_1_no_zero_divisors -> 'a ring_1;
val ring_no_zero_divisors_ring_1_no_zero_divisors =
  #ring_no_zero_divisors_ring_1_no_zero_divisors :
  'a ring_1_no_zero_divisors -> 'a ring_no_zero_divisors;
val semiring_1_no_zero_divisors_ring_1_no_zero_divisors =
  #semiring_1_no_zero_divisors_ring_1_no_zero_divisors :
  'a ring_1_no_zero_divisors -> 'a semiring_1_no_zero_divisors;

type 'a comm_ring =
  {comm_semiring_0_cancel_comm_ring : 'a comm_semiring_0_cancel,
    ring_comm_ring : 'a ring};
val comm_semiring_0_cancel_comm_ring = #comm_semiring_0_cancel_comm_ring :
  'a comm_ring -> 'a comm_semiring_0_cancel;
val ring_comm_ring = #ring_comm_ring : 'a comm_ring -> 'a ring;

type 'a comm_ring_1 =
  {comm_ring_comm_ring_1 : 'a comm_ring,
    comm_semiring_1_cancel_comm_ring_1 : 'a comm_semiring_1_cancel,
    ring_1_comm_ring_1 : 'a ring_1};
val comm_ring_comm_ring_1 = #comm_ring_comm_ring_1 :
  'a comm_ring_1 -> 'a comm_ring;
val comm_semiring_1_cancel_comm_ring_1 = #comm_semiring_1_cancel_comm_ring_1 :
  'a comm_ring_1 -> 'a comm_semiring_1_cancel;
val ring_1_comm_ring_1 = #ring_1_comm_ring_1 : 'a comm_ring_1 -> 'a ring_1;

type 'a semidom =
  {comm_semiring_1_cancel_semidom : 'a comm_semiring_1_cancel,
    semiring_1_no_zero_divisors_semidom : 'a semiring_1_no_zero_divisors};
val comm_semiring_1_cancel_semidom = #comm_semiring_1_cancel_semidom :
  'a semidom -> 'a comm_semiring_1_cancel;
val semiring_1_no_zero_divisors_semidom = #semiring_1_no_zero_divisors_semidom :
  'a semidom -> 'a semiring_1_no_zero_divisors;

type 'a idom =
  {comm_ring_1_idom : 'a comm_ring_1,
    ring_1_no_zero_divisors_idom : 'a ring_1_no_zero_divisors,
    semidom_idom : 'a semidom,
    comm_semiring_1_cancel_crossproduct_idom :
      'a comm_semiring_1_cancel_crossproduct};
val comm_ring_1_idom = #comm_ring_1_idom : 'a idom -> 'a comm_ring_1;
val ring_1_no_zero_divisors_idom = #ring_1_no_zero_divisors_idom :
  'a idom -> 'a ring_1_no_zero_divisors;
val semidom_idom = #semidom_idom : 'a idom -> 'a semidom;
val comm_semiring_1_cancel_crossproduct_idom =
  #comm_semiring_1_cancel_crossproduct_idom :
  'a idom -> 'a comm_semiring_1_cancel_crossproduct;

val plus_int = {plus = (fn a => fn b => Int.+ (a, b))} : Int.int plus;

val semigroup_add_int = {plus_semigroup_add = plus_int} : Int.int semigroup_add;

val cancel_semigroup_add_int =
  {semigroup_add_cancel_semigroup_add = semigroup_add_int} :
  Int.int cancel_semigroup_add;

val ab_semigroup_add_int = {semigroup_add_ab_semigroup_add = semigroup_add_int}
  : Int.int ab_semigroup_add;

val minus_int = {minus = (fn a => fn b => Int.- (a, b))} : Int.int minus;

val cancel_ab_semigroup_add_int =
  {ab_semigroup_add_cancel_ab_semigroup_add = ab_semigroup_add_int,
    cancel_semigroup_add_cancel_ab_semigroup_add = cancel_semigroup_add_int,
    minus_cancel_ab_semigroup_add = minus_int}
  : Int.int cancel_ab_semigroup_add;

val zero_int = {zero = (0 : Int.int)} : Int.int zero;

val monoid_add_int =
  {semigroup_add_monoid_add = semigroup_add_int, zero_monoid_add = zero_int} :
  Int.int monoid_add;

val comm_monoid_add_int =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_int,
    monoid_add_comm_monoid_add = monoid_add_int}
  : Int.int comm_monoid_add;

val cancel_comm_monoid_add_int =
  {cancel_ab_semigroup_add_cancel_comm_monoid_add = cancel_ab_semigroup_add_int,
    comm_monoid_add_cancel_comm_monoid_add = comm_monoid_add_int}
  : Int.int cancel_comm_monoid_add;

val mult_zero_int = {times_mult_zero = times_int, zero_mult_zero = zero_int} :
  Int.int mult_zero;

val semigroup_mult_int = {times_semigroup_mult = times_int} :
  Int.int semigroup_mult;

val semiring_int =
  {ab_semigroup_add_semiring = ab_semigroup_add_int,
    semigroup_mult_semiring = semigroup_mult_int}
  : Int.int semiring;

val semiring_0_int =
  {comm_monoid_add_semiring_0 = comm_monoid_add_int,
    mult_zero_semiring_0 = mult_zero_int, semiring_semiring_0 = semiring_int}
  : Int.int semiring_0;

val semiring_0_cancel_int =
  {cancel_comm_monoid_add_semiring_0_cancel = cancel_comm_monoid_add_int,
    semiring_0_semiring_0_cancel = semiring_0_int}
  : Int.int semiring_0_cancel;

val ab_semigroup_mult_int =
  {semigroup_mult_ab_semigroup_mult = semigroup_mult_int} :
  Int.int ab_semigroup_mult;

val comm_semiring_int =
  {ab_semigroup_mult_comm_semiring = ab_semigroup_mult_int,
    semiring_comm_semiring = semiring_int}
  : Int.int comm_semiring;

val comm_semiring_0_int =
  {comm_semiring_comm_semiring_0 = comm_semiring_int,
    semiring_0_comm_semiring_0 = semiring_0_int}
  : Int.int comm_semiring_0;

val comm_semiring_0_cancel_int =
  {comm_semiring_0_comm_semiring_0_cancel = comm_semiring_0_int,
    semiring_0_cancel_comm_semiring_0_cancel = semiring_0_cancel_int}
  : Int.int comm_semiring_0_cancel;

val power_int = {one_power = one_int, times_power = times_int} : Int.int power;

val monoid_mult_int =
  {semigroup_mult_monoid_mult = semigroup_mult_int,
    power_monoid_mult = power_int}
  : Int.int monoid_mult;

val numeral_int =
  {one_numeral = one_int, semigroup_add_numeral = semigroup_add_int} :
  Int.int numeral;

val semiring_numeral_int =
  {monoid_mult_semiring_numeral = monoid_mult_int,
    numeral_semiring_numeral = numeral_int,
    semiring_semiring_numeral = semiring_int}
  : Int.int semiring_numeral;

val zero_neq_one_int =
  {one_zero_neq_one = one_int, zero_zero_neq_one = zero_int} :
  Int.int zero_neq_one;

val semiring_1_int =
  {semiring_numeral_semiring_1 = semiring_numeral_int,
    semiring_0_semiring_1 = semiring_0_int,
    zero_neq_one_semiring_1 = zero_neq_one_int}
  : Int.int semiring_1;

val semiring_1_cancel_int =
  {semiring_0_cancel_semiring_1_cancel = semiring_0_cancel_int,
    semiring_1_semiring_1_cancel = semiring_1_int}
  : Int.int semiring_1_cancel;

val comm_monoid_mult_int =
  {ab_semigroup_mult_comm_monoid_mult = ab_semigroup_mult_int,
    monoid_mult_comm_monoid_mult = monoid_mult_int,
    dvd_comm_monoid_mult = dvd_int}
  : Int.int comm_monoid_mult;

val comm_semiring_1_int =
  {comm_monoid_mult_comm_semiring_1 = comm_monoid_mult_int,
    comm_semiring_0_comm_semiring_1 = comm_semiring_0_int,
    semiring_1_comm_semiring_1 = semiring_1_int}
  : Int.int comm_semiring_1;

val comm_semiring_1_cancel_int =
  {comm_semiring_0_cancel_comm_semiring_1_cancel = comm_semiring_0_cancel_int,
    comm_semiring_1_comm_semiring_1_cancel = comm_semiring_1_int,
    semiring_1_cancel_comm_semiring_1_cancel = semiring_1_cancel_int}
  : Int.int comm_semiring_1_cancel;

val comm_semiring_1_cancel_crossproduct_int =
  {comm_semiring_1_cancel_comm_semiring_1_cancel_crossproduct =
     comm_semiring_1_cancel_int}
  : Int.int comm_semiring_1_cancel_crossproduct;

val semiring_no_zero_divisors_int =
  {semiring_0_semiring_no_zero_divisors = semiring_0_int} :
  Int.int semiring_no_zero_divisors;

val semiring_1_no_zero_divisors_int =
  {semiring_1_semiring_1_no_zero_divisors = semiring_1_int,
    semiring_no_zero_divisors_semiring_1_no_zero_divisors =
      semiring_no_zero_divisors_int}
  : Int.int semiring_1_no_zero_divisors;

val semiring_no_zero_divisors_cancel_int =
  {semiring_no_zero_divisors_semiring_no_zero_divisors_cancel =
     semiring_no_zero_divisors_int}
  : Int.int semiring_no_zero_divisors_cancel;

val uminus_int = {uminus = Int.~} : Int.int uminus;

val group_add_int =
  {cancel_semigroup_add_group_add = cancel_semigroup_add_int,
    minus_group_add = minus_int, monoid_add_group_add = monoid_add_int,
    uminus_group_add = uminus_int}
  : Int.int group_add;

val ab_group_add_int =
  {cancel_comm_monoid_add_ab_group_add = cancel_comm_monoid_add_int,
    group_add_ab_group_add = group_add_int}
  : Int.int ab_group_add;

val ring_int =
  {ab_group_add_ring = ab_group_add_int,
    semiring_0_cancel_ring = semiring_0_cancel_int}
  : Int.int ring;

val ring_no_zero_divisors_int =
  {ring_ring_no_zero_divisors = ring_int,
    semiring_no_zero_divisors_cancel_ring_no_zero_divisors =
      semiring_no_zero_divisors_cancel_int}
  : Int.int ring_no_zero_divisors;

val neg_numeral_int =
  {group_add_neg_numeral = group_add_int, numeral_neg_numeral = numeral_int} :
  Int.int neg_numeral;

val ring_1_int =
  {neg_numeral_ring_1 = neg_numeral_int, ring_ring_1 = ring_int,
    semiring_1_cancel_ring_1 = semiring_1_cancel_int}
  : Int.int ring_1;

val ring_1_no_zero_divisors_int =
  {ring_1_ring_1_no_zero_divisors = ring_1_int,
    ring_no_zero_divisors_ring_1_no_zero_divisors = ring_no_zero_divisors_int,
    semiring_1_no_zero_divisors_ring_1_no_zero_divisors =
      semiring_1_no_zero_divisors_int}
  : Int.int ring_1_no_zero_divisors;

val comm_ring_int =
  {comm_semiring_0_cancel_comm_ring = comm_semiring_0_cancel_int,
    ring_comm_ring = ring_int}
  : Int.int comm_ring;

val comm_ring_1_int =
  {comm_ring_comm_ring_1 = comm_ring_int,
    comm_semiring_1_cancel_comm_ring_1 = comm_semiring_1_cancel_int,
    ring_1_comm_ring_1 = ring_1_int}
  : Int.int comm_ring_1;

val semidom_int =
  {comm_semiring_1_cancel_semidom = comm_semiring_1_cancel_int,
    semiring_1_no_zero_divisors_semidom = semiring_1_no_zero_divisors_int}
  : Int.int semidom;

val idom_int =
  {comm_ring_1_idom = comm_ring_1_int,
    ring_1_no_zero_divisors_idom = ring_1_no_zero_divisors_int,
    semidom_idom = semidom_int,
    comm_semiring_1_cancel_crossproduct_idom =
      comm_semiring_1_cancel_crossproduct_int}
  : Int.int idom;

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

type 'a abs_if =
  {abs_abs_if : 'a abs, minus_abs_if : 'a minus, uminus_abs_if : 'a uminus,
    zero_abs_if : 'a zero, ord_abs_if : 'a ord};
val abs_abs_if = #abs_abs_if : 'a abs_if -> 'a abs;
val minus_abs_if = #minus_abs_if : 'a abs_if -> 'a minus;
val uminus_abs_if = #uminus_abs_if : 'a abs_if -> 'a uminus;
val zero_abs_if = #zero_abs_if : 'a abs_if -> 'a zero;
val ord_abs_if = #ord_abs_if : 'a abs_if -> 'a ord;

val ord_int =
  {less_eq = (fn a => fn b => Int.<= (a, b)),
    less = (fn a => fn b => Int.< (a, b))}
  : Int.int ord;

val abs_if_int =
  {abs_abs_if = abs_int, minus_abs_if = minus_int, uminus_abs_if = uminus_int,
    zero_abs_if = zero_int, ord_abs_if = ord_int}
  : Int.int abs_if;

type 'a semiring_char_0 = {semiring_1_semiring_char_0 : 'a semiring_1};
val semiring_1_semiring_char_0 = #semiring_1_semiring_char_0 :
  'a semiring_char_0 -> 'a semiring_1;

type 'a ring_char_0 =
  {semiring_char_0_ring_char_0 : 'a semiring_char_0,
    ring_1_ring_char_0 : 'a ring_1};
val semiring_char_0_ring_char_0 = #semiring_char_0_ring_char_0 :
  'a ring_char_0 -> 'a semiring_char_0;
val ring_1_ring_char_0 = #ring_1_ring_char_0 : 'a ring_char_0 -> 'a ring_1;

val semiring_char_0_int = {semiring_1_semiring_char_0 = semiring_1_int} :
  Int.int semiring_char_0;

val ring_char_0_int =
  {semiring_char_0_ring_char_0 = semiring_char_0_int,
    ring_1_ring_char_0 = ring_1_int}
  : Int.int ring_char_0;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_int = {ord_preorder = ord_int} : Int.int preorder;

val order_int = {preorder_order = preorder_int} : Int.int order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_int = {order_linorder = order_int} : Int.int linorder;

type 'a idom_abs_sgn =
  {abs_idom_abs_sgn : 'a abs, sgn_idom_abs_sgn : 'a sgn,
    idom_idom_abs_sgn : 'a idom};
val abs_idom_abs_sgn = #abs_idom_abs_sgn : 'a idom_abs_sgn -> 'a abs;
val sgn_idom_abs_sgn = #sgn_idom_abs_sgn : 'a idom_abs_sgn -> 'a sgn;
val idom_idom_abs_sgn = #idom_idom_abs_sgn : 'a idom_abs_sgn -> 'a idom;

val idom_abs_sgn_int =
  {abs_idom_abs_sgn = abs_int, sgn_idom_abs_sgn = sgn_int,
    idom_idom_abs_sgn = idom_int}
  : Int.int idom_abs_sgn;

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

type 'a ordered_semiring =
  {ordered_comm_monoid_add_ordered_semiring : 'a ordered_comm_monoid_add,
    semiring_ordered_semiring : 'a semiring};
val ordered_comm_monoid_add_ordered_semiring =
  #ordered_comm_monoid_add_ordered_semiring :
  'a ordered_semiring -> 'a ordered_comm_monoid_add;
val semiring_ordered_semiring = #semiring_ordered_semiring :
  'a ordered_semiring -> 'a semiring;

type 'a ordered_semiring_0 =
  {ordered_semiring_ordered_semiring_0 : 'a ordered_semiring,
    semiring_0_ordered_semiring_0 : 'a semiring_0};
val ordered_semiring_ordered_semiring_0 = #ordered_semiring_ordered_semiring_0 :
  'a ordered_semiring_0 -> 'a ordered_semiring;
val semiring_0_ordered_semiring_0 = #semiring_0_ordered_semiring_0 :
  'a ordered_semiring_0 -> 'a semiring_0;

type 'a ordered_cancel_semiring =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_semiring :
     'a ordered_cancel_ab_semigroup_add,
    ordered_semiring_0_ordered_cancel_semiring : 'a ordered_semiring_0,
    semiring_0_cancel_ordered_cancel_semiring : 'a semiring_0_cancel};
val ordered_cancel_ab_semigroup_add_ordered_cancel_semiring =
  #ordered_cancel_ab_semigroup_add_ordered_cancel_semiring :
  'a ordered_cancel_semiring -> 'a ordered_cancel_ab_semigroup_add;
val ordered_semiring_0_ordered_cancel_semiring =
  #ordered_semiring_0_ordered_cancel_semiring :
  'a ordered_cancel_semiring -> 'a ordered_semiring_0;
val semiring_0_cancel_ordered_cancel_semiring =
  #semiring_0_cancel_ordered_cancel_semiring :
  'a ordered_cancel_semiring -> 'a semiring_0_cancel;

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

type 'a ordered_ring =
  {ordered_ab_group_add_ordered_ring : 'a ordered_ab_group_add,
    ordered_cancel_semiring_ordered_ring : 'a ordered_cancel_semiring,
    ring_ordered_ring : 'a ring};
val ordered_ab_group_add_ordered_ring = #ordered_ab_group_add_ordered_ring :
  'a ordered_ring -> 'a ordered_ab_group_add;
val ordered_cancel_semiring_ordered_ring = #ordered_cancel_semiring_ordered_ring
  : 'a ordered_ring -> 'a ordered_cancel_semiring;
val ring_ordered_ring = #ring_ordered_ring : 'a ordered_ring -> 'a ring;

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

val ordered_comm_monoid_add_int =
  {comm_monoid_add_ordered_comm_monoid_add = comm_monoid_add_int,
    ordered_ab_semigroup_add_ordered_comm_monoid_add =
      ordered_ab_semigroup_add_int}
  : Int.int ordered_comm_monoid_add;

val ordered_semiring_int =
  {ordered_comm_monoid_add_ordered_semiring = ordered_comm_monoid_add_int,
    semiring_ordered_semiring = semiring_int}
  : Int.int ordered_semiring;

val ordered_semiring_0_int =
  {ordered_semiring_ordered_semiring_0 = ordered_semiring_int,
    semiring_0_ordered_semiring_0 = semiring_0_int}
  : Int.int ordered_semiring_0;

val ordered_cancel_semiring_int =
  {ordered_cancel_ab_semigroup_add_ordered_cancel_semiring =
     ordered_cancel_ab_semigroup_add_int,
    ordered_semiring_0_ordered_cancel_semiring = ordered_semiring_0_int,
    semiring_0_cancel_ordered_cancel_semiring = semiring_0_cancel_int}
  : Int.int ordered_cancel_semiring;

val ordered_ab_semigroup_add_imp_le_int =
  {ordered_cancel_ab_semigroup_add_ordered_ab_semigroup_add_imp_le =
     ordered_cancel_ab_semigroup_add_int}
  : Int.int ordered_ab_semigroup_add_imp_le;

val strict_ordered_comm_monoid_add_int =
  {comm_monoid_add_strict_ordered_comm_monoid_add = comm_monoid_add_int,
    strict_ordered_ab_semigroup_add_strict_ordered_comm_monoid_add =
      strict_ordered_ab_semigroup_add_int}
  : Int.int strict_ordered_comm_monoid_add;

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

val ordered_ring_int =
  {ordered_ab_group_add_ordered_ring = ordered_ab_group_add_int,
    ordered_cancel_semiring_ordered_ring = ordered_cancel_semiring_int,
    ring_ordered_ring = ring_int}
  : Int.int ordered_ring;

type 'a zero_less_one =
  {order_zero_less_one : 'a order,
    zero_neq_one_zero_less_one : 'a zero_neq_one};
val order_zero_less_one = #order_zero_less_one : 'a zero_less_one -> 'a order;
val zero_neq_one_zero_less_one = #zero_neq_one_zero_less_one :
  'a zero_less_one -> 'a zero_neq_one;

val zero_less_one_int =
  {order_zero_less_one = order_int,
    zero_neq_one_zero_less_one = zero_neq_one_int}
  : Int.int zero_less_one;

type 'a ordered_semiring_strict =
  {ordered_cancel_ab_semigroup_add_ordered_semiring_strict :
     'a ordered_cancel_ab_semigroup_add,
    ordered_semiring_ordered_semiring_strict : 'a ordered_semiring,
    semiring_0_cancel_ordered_semiring_strict : 'a semiring_0_cancel};
val ordered_cancel_ab_semigroup_add_ordered_semiring_strict =
  #ordered_cancel_ab_semigroup_add_ordered_semiring_strict :
  'a ordered_semiring_strict -> 'a ordered_cancel_ab_semigroup_add;
val ordered_semiring_ordered_semiring_strict =
  #ordered_semiring_ordered_semiring_strict :
  'a ordered_semiring_strict -> 'a ordered_semiring;
val semiring_0_cancel_ordered_semiring_strict =
  #semiring_0_cancel_ordered_semiring_strict :
  'a ordered_semiring_strict -> 'a semiring_0_cancel;

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

type 'a linordered_semiring =
  {linordered_cancel_ab_semigroup_add_linordered_semiring :
     'a linordered_cancel_ab_semigroup_add,
    ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring :
      'a ordered_ab_semigroup_monoid_add_imp_le,
    ordered_cancel_semiring_linordered_semiring : 'a ordered_cancel_semiring};
val linordered_cancel_ab_semigroup_add_linordered_semiring =
  #linordered_cancel_ab_semigroup_add_linordered_semiring :
  'a linordered_semiring -> 'a linordered_cancel_ab_semigroup_add;
val ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring =
  #ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring :
  'a linordered_semiring -> 'a ordered_ab_semigroup_monoid_add_imp_le;
val ordered_cancel_semiring_linordered_semiring =
  #ordered_cancel_semiring_linordered_semiring :
  'a linordered_semiring -> 'a ordered_cancel_semiring;

type 'a linordered_semiring_strict =
  {linordered_semiring_linordered_semiring_strict : 'a linordered_semiring,
    ordered_semiring_strict_linordered_semiring_strict :
      'a ordered_semiring_strict};
val linordered_semiring_linordered_semiring_strict =
  #linordered_semiring_linordered_semiring_strict :
  'a linordered_semiring_strict -> 'a linordered_semiring;
val ordered_semiring_strict_linordered_semiring_strict =
  #ordered_semiring_strict_linordered_semiring_strict :
  'a linordered_semiring_strict -> 'a ordered_semiring_strict;

type 'a ordered_semiring_1 =
  {ordered_semiring_0_ordered_semiring_1 : 'a ordered_semiring_0,
    semiring_1_ordered_semiring_1 : 'a semiring_1,
    zero_less_one_ordered_semiring_1 : 'a zero_less_one};
val ordered_semiring_0_ordered_semiring_1 =
  #ordered_semiring_0_ordered_semiring_1 :
  'a ordered_semiring_1 -> 'a ordered_semiring_0;
val semiring_1_ordered_semiring_1 = #semiring_1_ordered_semiring_1 :
  'a ordered_semiring_1 -> 'a semiring_1;
val zero_less_one_ordered_semiring_1 = #zero_less_one_ordered_semiring_1 :
  'a ordered_semiring_1 -> 'a zero_less_one;

type 'a ordered_semiring_1_strict =
  {ordered_semiring_1_ordered_semiring_1_strict : 'a ordered_semiring_1,
    ordered_semiring_strict_ordered_semiring_1_strict :
      'a ordered_semiring_strict};
val ordered_semiring_1_ordered_semiring_1_strict =
  #ordered_semiring_1_ordered_semiring_1_strict :
  'a ordered_semiring_1_strict -> 'a ordered_semiring_1;
val ordered_semiring_strict_ordered_semiring_1_strict =
  #ordered_semiring_strict_ordered_semiring_1_strict :
  'a ordered_semiring_1_strict -> 'a ordered_semiring_strict;

type 'a linordered_semiring_1 =
  {linordered_semiring_linordered_semiring_1 : 'a linordered_semiring,
    ordered_semiring_1_linordered_semiring_1 : 'a ordered_semiring_1};
val linordered_semiring_linordered_semiring_1 =
  #linordered_semiring_linordered_semiring_1 :
  'a linordered_semiring_1 -> 'a linordered_semiring;
val ordered_semiring_1_linordered_semiring_1 =
  #ordered_semiring_1_linordered_semiring_1 :
  'a linordered_semiring_1 -> 'a ordered_semiring_1;

type 'a linordered_semiring_1_strict =
  {linordered_semiring_1_linordered_semiring_1_strict :
     'a linordered_semiring_1,
    linordered_semiring_strict_linordered_semiring_1_strict :
      'a linordered_semiring_strict,
    ordered_semiring_1_strict_linordered_semiring_1_strict :
      'a ordered_semiring_1_strict};
val linordered_semiring_1_linordered_semiring_1_strict =
  #linordered_semiring_1_linordered_semiring_1_strict :
  'a linordered_semiring_1_strict -> 'a linordered_semiring_1;
val linordered_semiring_strict_linordered_semiring_1_strict =
  #linordered_semiring_strict_linordered_semiring_1_strict :
  'a linordered_semiring_1_strict -> 'a linordered_semiring_strict;
val ordered_semiring_1_strict_linordered_semiring_1_strict =
  #ordered_semiring_1_strict_linordered_semiring_1_strict :
  'a linordered_semiring_1_strict -> 'a ordered_semiring_1_strict;

type 'a ordered_ab_group_add_abs =
  {abs_ordered_ab_group_add_abs : 'a abs,
    ordered_ab_group_add_ordered_ab_group_add_abs : 'a ordered_ab_group_add};
val abs_ordered_ab_group_add_abs = #abs_ordered_ab_group_add_abs :
  'a ordered_ab_group_add_abs -> 'a abs;
val ordered_ab_group_add_ordered_ab_group_add_abs =
  #ordered_ab_group_add_ordered_ab_group_add_abs :
  'a ordered_ab_group_add_abs -> 'a ordered_ab_group_add;

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

type 'a linordered_ring =
  {linordered_ab_group_add_linordered_ring : 'a linordered_ab_group_add,
    ordered_ab_group_add_abs_linordered_ring : 'a ordered_ab_group_add_abs,
    abs_if_linordered_ring : 'a abs_if,
    linordered_semiring_linordered_ring : 'a linordered_semiring,
    ordered_ring_linordered_ring : 'a ordered_ring};
val linordered_ab_group_add_linordered_ring =
  #linordered_ab_group_add_linordered_ring :
  'a linordered_ring -> 'a linordered_ab_group_add;
val ordered_ab_group_add_abs_linordered_ring =
  #ordered_ab_group_add_abs_linordered_ring :
  'a linordered_ring -> 'a ordered_ab_group_add_abs;
val abs_if_linordered_ring = #abs_if_linordered_ring :
  'a linordered_ring -> 'a abs_if;
val linordered_semiring_linordered_ring = #linordered_semiring_linordered_ring :
  'a linordered_ring -> 'a linordered_semiring;
val ordered_ring_linordered_ring = #ordered_ring_linordered_ring :
  'a linordered_ring -> 'a ordered_ring;

type 'a linordered_ring_strict =
  {linordered_ring_linordered_ring_strict : 'a linordered_ring,
    linordered_semiring_strict_linordered_ring_strict :
      'a linordered_semiring_strict,
    ring_no_zero_divisors_linordered_ring_strict : 'a ring_no_zero_divisors};
val linordered_ring_linordered_ring_strict =
  #linordered_ring_linordered_ring_strict :
  'a linordered_ring_strict -> 'a linordered_ring;
val linordered_semiring_strict_linordered_ring_strict =
  #linordered_semiring_strict_linordered_ring_strict :
  'a linordered_ring_strict -> 'a linordered_semiring_strict;
val ring_no_zero_divisors_linordered_ring_strict =
  #ring_no_zero_divisors_linordered_ring_strict :
  'a linordered_ring_strict -> 'a ring_no_zero_divisors;

type 'a ordered_comm_semiring =
  {comm_semiring_0_ordered_comm_semiring : 'a comm_semiring_0,
    ordered_semiring_ordered_comm_semiring : 'a ordered_semiring};
val comm_semiring_0_ordered_comm_semiring =
  #comm_semiring_0_ordered_comm_semiring :
  'a ordered_comm_semiring -> 'a comm_semiring_0;
val ordered_semiring_ordered_comm_semiring =
  #ordered_semiring_ordered_comm_semiring :
  'a ordered_comm_semiring -> 'a ordered_semiring;

type 'a ordered_cancel_comm_semiring =
  {comm_semiring_0_cancel_ordered_cancel_comm_semiring :
     'a comm_semiring_0_cancel,
    ordered_cancel_semiring_ordered_cancel_comm_semiring :
      'a ordered_cancel_semiring,
    ordered_comm_semiring_ordered_cancel_comm_semiring :
      'a ordered_comm_semiring};
val comm_semiring_0_cancel_ordered_cancel_comm_semiring =
  #comm_semiring_0_cancel_ordered_cancel_comm_semiring :
  'a ordered_cancel_comm_semiring -> 'a comm_semiring_0_cancel;
val ordered_cancel_semiring_ordered_cancel_comm_semiring =
  #ordered_cancel_semiring_ordered_cancel_comm_semiring :
  'a ordered_cancel_comm_semiring -> 'a ordered_cancel_semiring;
val ordered_comm_semiring_ordered_cancel_comm_semiring =
  #ordered_comm_semiring_ordered_cancel_comm_semiring :
  'a ordered_cancel_comm_semiring -> 'a ordered_comm_semiring;

type 'a ordered_comm_semiring_strict =
  {ordered_cancel_comm_semiring_ordered_comm_semiring_strict :
     'a ordered_cancel_comm_semiring,
    ordered_semiring_strict_ordered_comm_semiring_strict :
      'a ordered_semiring_strict};
val ordered_cancel_comm_semiring_ordered_comm_semiring_strict =
  #ordered_cancel_comm_semiring_ordered_comm_semiring_strict :
  'a ordered_comm_semiring_strict -> 'a ordered_cancel_comm_semiring;
val ordered_semiring_strict_ordered_comm_semiring_strict =
  #ordered_semiring_strict_ordered_comm_semiring_strict :
  'a ordered_comm_semiring_strict -> 'a ordered_semiring_strict;

type 'a linordered_comm_semiring_strict =
  {linordered_semiring_strict_linordered_comm_semiring_strict :
     'a linordered_semiring_strict,
    ordered_comm_semiring_strict_linordered_comm_semiring_strict :
      'a ordered_comm_semiring_strict};
val linordered_semiring_strict_linordered_comm_semiring_strict =
  #linordered_semiring_strict_linordered_comm_semiring_strict :
  'a linordered_comm_semiring_strict -> 'a linordered_semiring_strict;
val ordered_comm_semiring_strict_linordered_comm_semiring_strict =
  #ordered_comm_semiring_strict_linordered_comm_semiring_strict :
  'a linordered_comm_semiring_strict -> 'a ordered_comm_semiring_strict;

type 'a linordered_nonzero_semiring =
  {semiring_char_0_linordered_nonzero_semiring : 'a semiring_char_0,
    linorder_linordered_nonzero_semiring : 'a linorder,
    comm_semiring_1_linordered_nonzero_semiring : 'a comm_semiring_1,
    ordered_comm_semiring_linordered_nonzero_semiring :
      'a ordered_comm_semiring,
    ordered_semiring_1_linordered_nonzero_semiring : 'a ordered_semiring_1};
val semiring_char_0_linordered_nonzero_semiring =
  #semiring_char_0_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a semiring_char_0;
val linorder_linordered_nonzero_semiring = #linorder_linordered_nonzero_semiring
  : 'a linordered_nonzero_semiring -> 'a linorder;
val comm_semiring_1_linordered_nonzero_semiring =
  #comm_semiring_1_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a comm_semiring_1;
val ordered_comm_semiring_linordered_nonzero_semiring =
  #ordered_comm_semiring_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a ordered_comm_semiring;
val ordered_semiring_1_linordered_nonzero_semiring =
  #ordered_semiring_1_linordered_nonzero_semiring :
  'a linordered_nonzero_semiring -> 'a ordered_semiring_1;

type 'a linordered_semidom =
  {linordered_comm_semiring_strict_linordered_semidom :
     'a linordered_comm_semiring_strict,
    linordered_nonzero_semiring_linordered_semidom :
      'a linordered_nonzero_semiring,
    semidom_linordered_semidom : 'a semidom};
val linordered_comm_semiring_strict_linordered_semidom =
  #linordered_comm_semiring_strict_linordered_semidom :
  'a linordered_semidom -> 'a linordered_comm_semiring_strict;
val linordered_nonzero_semiring_linordered_semidom =
  #linordered_nonzero_semiring_linordered_semidom :
  'a linordered_semidom -> 'a linordered_nonzero_semiring;
val semidom_linordered_semidom = #semidom_linordered_semidom :
  'a linordered_semidom -> 'a semidom;

type 'a ordered_comm_ring =
  {comm_ring_ordered_comm_ring : 'a comm_ring,
    ordered_cancel_comm_semiring_ordered_comm_ring :
      'a ordered_cancel_comm_semiring,
    ordered_ring_ordered_comm_ring : 'a ordered_ring};
val comm_ring_ordered_comm_ring = #comm_ring_ordered_comm_ring :
  'a ordered_comm_ring -> 'a comm_ring;
val ordered_cancel_comm_semiring_ordered_comm_ring =
  #ordered_cancel_comm_semiring_ordered_comm_ring :
  'a ordered_comm_ring -> 'a ordered_cancel_comm_semiring;
val ordered_ring_ordered_comm_ring = #ordered_ring_ordered_comm_ring :
  'a ordered_comm_ring -> 'a ordered_ring;

type 'a ordered_ring_abs =
  {ordered_ab_group_add_abs_ordered_ring_abs : 'a ordered_ab_group_add_abs,
    ordered_ring_ordered_ring_abs : 'a ordered_ring};
val ordered_ab_group_add_abs_ordered_ring_abs =
  #ordered_ab_group_add_abs_ordered_ring_abs :
  'a ordered_ring_abs -> 'a ordered_ab_group_add_abs;
val ordered_ring_ordered_ring_abs = #ordered_ring_ordered_ring_abs :
  'a ordered_ring_abs -> 'a ordered_ring;

type 'a linordered_idom =
  {ring_char_0_linordered_idom : 'a ring_char_0,
    idom_abs_sgn_linordered_idom : 'a idom_abs_sgn,
    linordered_ring_strict_linordered_idom : 'a linordered_ring_strict,
    linordered_semidom_linordered_idom : 'a linordered_semidom,
    linordered_semiring_1_strict_linordered_idom :
      'a linordered_semiring_1_strict,
    ordered_comm_ring_linordered_idom : 'a ordered_comm_ring,
    ordered_ring_abs_linordered_idom : 'a ordered_ring_abs};
val ring_char_0_linordered_idom = #ring_char_0_linordered_idom :
  'a linordered_idom -> 'a ring_char_0;
val idom_abs_sgn_linordered_idom = #idom_abs_sgn_linordered_idom :
  'a linordered_idom -> 'a idom_abs_sgn;
val linordered_ring_strict_linordered_idom =
  #linordered_ring_strict_linordered_idom :
  'a linordered_idom -> 'a linordered_ring_strict;
val linordered_semidom_linordered_idom = #linordered_semidom_linordered_idom :
  'a linordered_idom -> 'a linordered_semidom;
val linordered_semiring_1_strict_linordered_idom =
  #linordered_semiring_1_strict_linordered_idom :
  'a linordered_idom -> 'a linordered_semiring_1_strict;
val ordered_comm_ring_linordered_idom = #ordered_comm_ring_linordered_idom :
  'a linordered_idom -> 'a ordered_comm_ring;
val ordered_ring_abs_linordered_idom = #ordered_ring_abs_linordered_idom :
  'a linordered_idom -> 'a ordered_ring_abs;

val ordered_semiring_strict_int =
  {ordered_cancel_ab_semigroup_add_ordered_semiring_strict =
     ordered_cancel_ab_semigroup_add_int,
    ordered_semiring_ordered_semiring_strict = ordered_semiring_int,
    semiring_0_cancel_ordered_semiring_strict = semiring_0_cancel_int}
  : Int.int ordered_semiring_strict;

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

val linordered_semiring_int =
  {linordered_cancel_ab_semigroup_add_linordered_semiring =
     linordered_cancel_ab_semigroup_add_int,
    ordered_ab_semigroup_monoid_add_imp_le_linordered_semiring =
      ordered_ab_semigroup_monoid_add_imp_le_int,
    ordered_cancel_semiring_linordered_semiring = ordered_cancel_semiring_int}
  : Int.int linordered_semiring;

val linordered_semiring_strict_int =
  {linordered_semiring_linordered_semiring_strict = linordered_semiring_int,
    ordered_semiring_strict_linordered_semiring_strict =
      ordered_semiring_strict_int}
  : Int.int linordered_semiring_strict;

val ordered_semiring_1_int =
  {ordered_semiring_0_ordered_semiring_1 = ordered_semiring_0_int,
    semiring_1_ordered_semiring_1 = semiring_1_int,
    zero_less_one_ordered_semiring_1 = zero_less_one_int}
  : Int.int ordered_semiring_1;

val ordered_semiring_1_strict_int =
  {ordered_semiring_1_ordered_semiring_1_strict = ordered_semiring_1_int,
    ordered_semiring_strict_ordered_semiring_1_strict =
      ordered_semiring_strict_int}
  : Int.int ordered_semiring_1_strict;

val linordered_semiring_1_int =
  {linordered_semiring_linordered_semiring_1 = linordered_semiring_int,
    ordered_semiring_1_linordered_semiring_1 = ordered_semiring_1_int}
  : Int.int linordered_semiring_1;

val linordered_semiring_1_strict_int =
  {linordered_semiring_1_linordered_semiring_1_strict =
     linordered_semiring_1_int,
    linordered_semiring_strict_linordered_semiring_1_strict =
      linordered_semiring_strict_int,
    ordered_semiring_1_strict_linordered_semiring_1_strict =
      ordered_semiring_1_strict_int}
  : Int.int linordered_semiring_1_strict;

val ordered_ab_group_add_abs_int =
  {abs_ordered_ab_group_add_abs = abs_int,
    ordered_ab_group_add_ordered_ab_group_add_abs = ordered_ab_group_add_int}
  : Int.int ordered_ab_group_add_abs;

val linordered_ab_group_add_int =
  {linordered_cancel_ab_semigroup_add_linordered_ab_group_add =
     linordered_cancel_ab_semigroup_add_int,
    ordered_ab_group_add_linordered_ab_group_add = ordered_ab_group_add_int}
  : Int.int linordered_ab_group_add;

val linordered_ring_int =
  {linordered_ab_group_add_linordered_ring = linordered_ab_group_add_int,
    ordered_ab_group_add_abs_linordered_ring = ordered_ab_group_add_abs_int,
    abs_if_linordered_ring = abs_if_int,
    linordered_semiring_linordered_ring = linordered_semiring_int,
    ordered_ring_linordered_ring = ordered_ring_int}
  : Int.int linordered_ring;

val linordered_ring_strict_int =
  {linordered_ring_linordered_ring_strict = linordered_ring_int,
    linordered_semiring_strict_linordered_ring_strict =
      linordered_semiring_strict_int,
    ring_no_zero_divisors_linordered_ring_strict = ring_no_zero_divisors_int}
  : Int.int linordered_ring_strict;

val ordered_comm_semiring_int =
  {comm_semiring_0_ordered_comm_semiring = comm_semiring_0_int,
    ordered_semiring_ordered_comm_semiring = ordered_semiring_int}
  : Int.int ordered_comm_semiring;

val ordered_cancel_comm_semiring_int =
  {comm_semiring_0_cancel_ordered_cancel_comm_semiring =
     comm_semiring_0_cancel_int,
    ordered_cancel_semiring_ordered_cancel_comm_semiring =
      ordered_cancel_semiring_int,
    ordered_comm_semiring_ordered_cancel_comm_semiring =
      ordered_comm_semiring_int}
  : Int.int ordered_cancel_comm_semiring;

val ordered_comm_semiring_strict_int =
  {ordered_cancel_comm_semiring_ordered_comm_semiring_strict =
     ordered_cancel_comm_semiring_int,
    ordered_semiring_strict_ordered_comm_semiring_strict =
      ordered_semiring_strict_int}
  : Int.int ordered_comm_semiring_strict;

val linordered_comm_semiring_strict_int =
  {linordered_semiring_strict_linordered_comm_semiring_strict =
     linordered_semiring_strict_int,
    ordered_comm_semiring_strict_linordered_comm_semiring_strict =
      ordered_comm_semiring_strict_int}
  : Int.int linordered_comm_semiring_strict;

val linordered_nonzero_semiring_int =
  {semiring_char_0_linordered_nonzero_semiring = semiring_char_0_int,
    linorder_linordered_nonzero_semiring = linorder_int,
    comm_semiring_1_linordered_nonzero_semiring = comm_semiring_1_int,
    ordered_comm_semiring_linordered_nonzero_semiring =
      ordered_comm_semiring_int,
    ordered_semiring_1_linordered_nonzero_semiring = ordered_semiring_1_int}
  : Int.int linordered_nonzero_semiring;

val linordered_semidom_int =
  {linordered_comm_semiring_strict_linordered_semidom =
     linordered_comm_semiring_strict_int,
    linordered_nonzero_semiring_linordered_semidom =
      linordered_nonzero_semiring_int,
    semidom_linordered_semidom = semidom_int}
  : Int.int linordered_semidom;

val ordered_comm_ring_int =
  {comm_ring_ordered_comm_ring = comm_ring_int,
    ordered_cancel_comm_semiring_ordered_comm_ring =
      ordered_cancel_comm_semiring_int,
    ordered_ring_ordered_comm_ring = ordered_ring_int}
  : Int.int ordered_comm_ring;

val ordered_ring_abs_int =
  {ordered_ab_group_add_abs_ordered_ring_abs = ordered_ab_group_add_abs_int,
    ordered_ring_ordered_ring_abs = ordered_ring_int}
  : Int.int ordered_ring_abs;

val linordered_idom_int =
  {ring_char_0_linordered_idom = ring_char_0_int,
    idom_abs_sgn_linordered_idom = idom_abs_sgn_int,
    linordered_ring_strict_linordered_idom = linordered_ring_strict_int,
    linordered_semidom_linordered_idom = linordered_semidom_int,
    linordered_semiring_1_strict_linordered_idom =
      linordered_semiring_1_strict_int,
    ordered_comm_ring_linordered_idom = ordered_comm_ring_int,
    ordered_ring_abs_linordered_idom = ordered_ring_abs_int}
  : Int.int linordered_idom;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = (fn a => fn b => ((a : Int.int) = b))} : Int.int equal;

fun typerep_nata t = Typerep ("Nat.nat", []);

val countable_nat = {} : Int.int countable;

val typerep_nat = {typerep = typerep_nata} : Int.int typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  Int.int heap;

val zero_nat = {zero = (0 : Int.int)} : Int.int zero;

val ord_nat =
  {less_eq = (fn a => fn b => Int.<= (a, b)),
    less = (fn a => fn b => Int.< (a, b))}
  : Int.int ord;

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

datatype ('a, 'b) pr_op = Push_Fwd of 'a | Push_Bwd of 'a | Advance of 'b |
  Relabel of 'b | Relabel_Gap of 'b | Done;

datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h) pr_imp_ext =
  Pr_imp_ext of
    'a * 'a * 'a * 'b * 'c * 'd * 'e * 'e * 'f * bool ref * Int.int ref *
      'g ref * 'h;

fun id x = (fn xa => xa) x;

fun eq A_ a b = equal A_ a b;

fun refa A_ x = (fn () => ref x);

fun src_imp x = (fn (fa, _) => (fn a => (fn () => Array.sub (fa, a)))) x;

fun tgt_imp x = (fn (_, a) => (fn b => (fn () => Array.sub (a, b)))) x;

fun the (SOME x2) = x2;

fun edge_adv x = (fn _ => fn i => (fn () => (Int.+ (i, (1 : Int.int))))) x;

fun edge_cur x = (fn _ => (fn a => (fn () => a))) x;

fun csr_has_imp A_ =
  (fn (ba, (_, ca)) => fn v => fn () =>
    let
      val i = (fn () => Array.sub (ca, v)) ();
      val e = (fn () => Array.sub (ba, Int.+ (v, (1 : Int.int)))) ();
    in
      Int.< (i, e)
    end);

fun csr_copy_imp n ba ca i =
  (if Int.< (i, n)
    then (fn () => let
                     val s = (fn () => Array.sub (ba, i)) ();
                     val _ = (fn () => Machine.upd (i, s, ca)) ();
                   in
                     csr_copy_imp n ba ca (Int.+ (i, (1 : Int.int))) ()
                   end)
    else (fn () => ()));

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

fun max A_ a b = (if less_eq A_ a b then b else a);

fun min A_ a b = (if less_eq A_ a b then a else b);

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

fun csr_cursor_init n ba =
  (fn () => let
              val ca = (fn () => Array.array (n, (0 : Int.int))) ();
              val _ = csr_copy_imp n ba ca (0 : Int.int) ();
            in
              ca
            end);

fun wrap cap i = (if Int.< (i, cap) then i else Machine.sub_nat (i, cap));

fun arr_upd_imp B_ ix a k x =
  (fn () => let
              val _ = (fn () => Machine.upd (ix k, x, a)) ();
            in
              ()
            end);

fun xset_insert_imp x xi =
  (fn () => let
              val _ = (fn () => Machine.upd (x, true, xi)) ();
            in
              ()
            end);

fun arr_lookup_imp B_ ix a k = (fn () => Array.sub (a, ix k));

fun abk_move_imp x =
  (fn (ha, (ta, (nXa, pVa))) => fn j => fn ja => fn () =>
    let
      val a = (fn () => Array.sub (ha, j)) ();
    in
      (case a of NONE => (fn () => ())
        | SOME aa =>
          (fn f_ => fn () => f_ (((fn () => Array.sub (ta, j))) ()) ())
            (fn z =>
              (fn f_ => fn () => f_ (((fn () => Array.sub (ha, ja))) ()) ())
                (fn f =>
                  (fn f_ => fn () => f_ (((fn () => Machine.upd (j, NONE, ha)))
                    ()) ())
                    (fn _ =>
                      (fn f_ => fn () => f_
                        (((fn () => Machine.upd (ja, SOME aa, ha))) ()) ())
                        (fn _ =>
                          (fn f_ => fn () => f_
                            (((fn () => Machine.upd (j, NONE, ta))) ()) ())
                            (fn _ =>
                              (fn f_ => fn () => f_
                                ((case f
                                   of NONE => (fn () => Machine.upd (ja, z, ta))
                                   | SOME _ => (fn () => ta))
                                ()) ())
                                (fn _ =>
                                  (fn f_ => fn () => f_
                                    (((fn () => Machine.upd (the z, f, nXa)))
                                    ()) ())
                                    (fn _ =>
                                      (fn f_ => fn () => f_
((case f of NONE => (fn () => pVa)
   | SOME y => (fn () => Machine.upd (y, z, pVa)))
()) ())
(fn _ => (fn () => ()))))))))))
        ()
    end)
    x;

fun abk_pick_imp x =
  (fn (ha, (_, (_, _))) => (fn a => (fn () => Array.sub (ha, a)))) x;

fun xset_scan a l i =
  (if Int.< (i, l)
    then (fn () =>
           let
             val b = (fn () => Array.sub (a, i)) ();
           in
             (if b then (fn () => i)
               else xset_scan a l (Int.+ (i, (1 : Int.int))))
               ()
           end)
    else (fn () => i));

fun abk_empty_imp n nb =
  (fn () => let
              val ha = (fn () => Array.array (nb, NONE)) ();
              val ta = (fn () => Array.array (nb, NONE)) ();
              val nXa = (fn () => Array.array (n, NONE)) ();
              val pVa = (fn () => Array.array (n, NONE)) ();
            in
              (ha, (ta, (nXa, pVa)))
            end);

fun abk_insert_imp x =
  (fn (ha, (ta, (nXa, pVa))) => fn xa => fn k => fn () =>
    let
      val f = (fn () => Array.sub (ha, k)) ();
      val _ = (fn () => Machine.upd (k, SOME xa, ha)) ();
      val _ =
        (case f of NONE => (fn () => Machine.upd (k, SOME xa, ta))
          | SOME _ => (fn () => ta))
          ();
      val _ = (fn () => Machine.upd (xa, f, nXa)) ();
      val _ = (fn () => Machine.upd (xa, NONE, pVa)) ();
      val _ =
        (case f of NONE => (fn () => pVa)
          | SOME y => (fn () => Machine.upd (y, SOME xa, pVa)))
          ();
    in
      ()
    end)
    x;

fun abk_remove_imp x =
  (fn (ha, (ta, (nXa, pVa))) => fn xa => fn k => fn () =>
    let
      val p = (fn () => Array.sub (pVa, xa)) ();
      val q = (fn () => Array.sub (nXa, xa)) ();
      val _ =
        (case p of NONE => (fn () => Machine.upd (k, q, ha))
          | SOME _ => (fn () => ha))
          ();
      val _ =
        (case q of NONE => (fn () => Machine.upd (k, p, ta))
          | SOME _ => (fn () => ta))
          ();
      val _ =
        (case p of NONE => (fn () => nXa)
          | SOME a => (fn () => Machine.upd (a, q, nXa)))
          ();
      val _ =
        (case q of NONE => (fn () => pVa)
          | SOME b => (fn () => Machine.upd (b, p, pVa)))
          ();
    in
      ()
    end)
    x;

fun arq_pop_imp A_ cap =
  (fn (aa, (hr, sr)) => fn () =>
    let
      val h = (fn () => ! hr) ();
      val s = (fn () => ! sr) ();
      val x = (fn () => Array.sub (aa, h)) ();
      val _ = (fn () => hr := (wrap cap (Int.+ (h, (1 : Int.int))))) ();
      val _ = (fn () => sr := (Machine.sub_nat (s, (1 : Int.int)))) ();
    in
      x
    end);

fun csr_fill_edges_tgt c b e si =
  (fn () =>
    let
      val ba = edge_has_next c si ();
    in
      (if ba
        then (fn f_ => fn () => f_ ((edge_cur c si) ()) ())
               (fn ea =>
                 (fn f_ => fn () => f_ ((tgt_imp c ea) ()) ())
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
                                       (csr_fill_edges_tgt c b e)))))))
        else (fn () => ()))
        ()
    end);

fun csr_init_edges_tgt c si m =
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

fun csr_rt_has_imp A_ =
  (fn (ba, (ea, (ca, _))) => csr_has_imp A_ (ba, (ea, ca)));

fun arq_push_imp A_ cap =
  (fn (aa, (hr, sr)) => fn x => fn () =>
    let
      val h = (fn () => ! hr) ();
      val s = (fn () => ! sr) ();
      val _ = (fn () => Machine.upd (wrap cap (Int.+ (h, s)), x, aa)) ();
    in
      (fn () => sr := (Int.+ (s, (1 : Int.int)))) ()
    end);

fun xset_it_init a = (fn () => let
                                 val l = (fn () => Array.length a) ();
                                 val i = xset_scan a l (0 : Int.int) ();
                               in
                                 (a, (l, i))
                               end);

fun xset_it_next it =
  let
    val (a, (l, i)) = it;
  in
    (fn () => let
                val j = xset_scan a l (Int.+ (i, (1 : Int.int))) ();
              in
                (i, (a, (l, j)))
              end)
  end;

fun pi_lab
  (Pr_imp_ext
    (pi_fwd, pi_bwd, pi_caps, pi_ex, pi_lab, pi_cnt, pi_out, pi_in, pi_ends,
      pi_mf, pi_mk, pi_md, more))
  = pi_lab;

fun pr_drain bi j g_imp =
  (fn () =>
    let
      val a = abk_pick_imp bi j ();
    in
      (case a of NONE => (fn () => ())
        | SOME v =>
          (fn f_ => fn () => f_ ((g_imp v) ()) ())
            (fn _ => pr_drain bi j g_imp))
        ()
    end);

fun pr_gap_walk bi j m g_imp =
  (if ((m : Int.int) = (0 : Int.int)) then (fn () => ())
    else (fn () =>
           let
             val _ = pr_drain bi j g_imp ();
           in
             pr_gap_walk bi (Int.+ (j, (1 : Int.int)))
               (Machine.sub_nat (m, (1 : Int.int))) g_imp ()
           end));

fun pr_lb_gap_fold x =
  (fn (_, (bi, dr)) => fn k => fn g_imp => fn () =>
    let
      val d = (fn () => ! dr) ();
    in
      pr_gap_walk bi (Int.+ (k, (1 : Int.int))) (Machine.sub_nat (d, k)) g_imp
        ()
    end)
    x;

fun pi_out
  (Pr_imp_ext
    (pi_fwd, pi_bwd, pi_caps, pi_ex, pi_lab, pi_cnt, pi_out, pi_in, pi_ends,
      pi_mf, pi_mk, pi_md, more))
  = pi_out;

fun pi_in
  (Pr_imp_ext
    (pi_fwd, pi_bwd, pi_caps, pi_ex, pi_lab, pi_cnt, pi_out, pi_in, pi_ends,
      pi_mf, pi_mk, pi_md, more))
  = pi_in;

fun pi_cnt
  (Pr_imp_ext
    (pi_fwd, pi_bwd, pi_caps, pi_ex, pi_lab, pi_cnt, pi_out, pi_in, pi_ends,
      pi_mf, pi_mk, pi_md, more))
  = pi_cnt;

fun pr_lower bi d =
  (if ((d : Int.int) = (0 : Int.int)) then (fn () => (0 : Int.int))
    else (fn () =>
           let
             val a = abk_pick_imp bi d ();
           in
             (case a of NONE => pr_lower bi (Machine.sub_nat (d, (1 : Int.int)))
               | SOME _ => (fn () => d))
               ()
           end));

fun pr_lb_upd n =
  (fn (lai, (bi, dr)) => fn v => fn k => fn () =>
    let
      val ka = arr_lookup_imp heap_nat id lai v ();
      val _ =
        (if Int.< (ka, n) then abk_remove_imp bi v ka else (fn () => ())) ();
      val _ =
        (if Int.< (k, n) then abk_insert_imp bi v k else (fn () => ())) ();
      val d = (fn () => ! dr) ();
      val da = pr_lower bi (if Int.< (k, n) then max ord_nat d k else d) ();
      val _ = (fn () => dr := da) ();
    in
      arr_upd_imp heap_nat id lai v k ()
    end);

fun pr_lb_get x = (fn (lai, (_, _)) => arr_lookup_imp heap_nat id lai) x;

fun pr_change_label nv v k si =
  (fn () =>
    let
      val ka = pr_lb_get (pi_lab si) v ();
      val c = arr_lookup_imp heap_nat id (pi_cnt si) ka ();
      val _ =
        arr_upd_imp heap_nat id (pi_cnt si) ka
          (Machine.sub_nat (c, (1 : Int.int))) ();
      val _ = pr_lb_upd nv (pi_lab si) v k ();
      val ca = arr_lookup_imp heap_nat id (pi_cnt si) k ();
    in
      arr_upd_imp heap_nat id (pi_cnt si) k (Int.+ (ca, (1 : Int.int))) ()
    end);

fun csr_rt_reset_imp A_ =
  (fn (ba, (ea, (ca, _))) => csr_reset_imp A_ (ba, (ea, ca)));

fun pr_gap_step nv k si v =
  (fn () =>
    let
      val lv = pr_lb_get (pi_lab si) v ();
    in
      (if Int.< (k, lv) andalso Int.< (lv, nv)
        then (fn f_ => fn () => f_
               ((pr_change_label nv v (Int.+ (nv, (1 : Int.int))) si) ()) ())
               (fn _ =>
                 (fn f_ => fn () => f_
                   ((csr_rt_reset_imp heap_nat (pi_out si) v) ()) ())
                   (fn _ => csr_rt_reset_imp heap_nat (pi_in si) v))
        else (fn () => ()))
        ()
    end);

fun pr_gap nv k si = pr_lb_gap_fold (pi_lab si) k (pr_gap_step nv k si);

fun csr_prefix_sums_tgt n b j acc =
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
                 (fn _ =>
                   csr_prefix_sums_tgt n b (Int.+ (j, (1 : Int.int))) acca)
             end
               ()
           end)
    else (fn () => ()));

fun csr_count_edges_tgt n c b m si =
  (fn () =>
    let
      val ba = edge_has_next c si ();
    in
      (if ba
        then (fn f_ => fn () => f_ ((edge_cur c si) ()) ())
               (fn e =>
                 (fn f_ => fn () => f_ ((tgt_imp c e) ()) ())
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
                           (csr_count_edges_tgt n c b
                             (Int.+ (m, (1 : Int.int)))))))
        else (fn () => m))
        ()
    end);

fun csr_build_edges_tgt n c si =
  (fn () =>
    let
      val b =
        (fn () => Array.array (Int.+ (n, (1 : Int.int)), (0 : Int.int))) ();
      val m = csr_count_edges_tgt n c b (0 : Int.int) si ();
      val _ = csr_prefix_sums_tgt n b (1 : Int.int) (0 : Int.int) ();
      val e = csr_init_edges_tgt c si m ();
      val _ = csr_fill_edges_tgt c b e si ();
    in
      (b, e)
    end);

fun csr_rt_move_imp A_ =
  (fn (ba, (ea, (ca, _))) => csr_move_imp A_ (ba, (ea, ca)));

fun arq_empty_imp A_ cap d =
  (fn () => let
              val aa = (fn () => Array.array (cap, d)) ();
              val hr = refa heap_nat (0 : Int.int) ();
              val sr = refa heap_nat (0 : Int.int) ();
            in
              (aa, (hr, sr))
            end);

fun foldl_range_imp f i n a =
  (if Int.< (i, n)
    then (fn () => let
                     val x = f i a ();
                   in
                     foldl_range_imp f (Int.+ (i, (1 : Int.int))) n x ()
                   end)
    else (fn () => a));

fun csr_edge_fold_imp x =
  (fn (_, (ea, (_, _))) => fn g => fn () =>
    let
      val m = (fn () => Array.length ea) ();
    in
      foldl_range_imp
        (fn i => fn _ =>
          (fn f_ => fn () => f_ (((fn () => Array.sub (ea, i))) ()) ()) g)
        (0 : Int.int) m () ()
    end)
    x;

fun pi_ends
  (Pr_imp_ext
    (pi_fwd, pi_bwd, pi_caps, pi_ex, pi_lab, pi_cnt, pi_out, pi_in, pi_ends,
      pi_mf, pi_mk, pi_md, more))
  = pi_ends;

fun pi_caps
  (Pr_imp_ext
    (pi_fwd, pi_bwd, pi_caps, pi_ex, pi_lab, pi_cnt, pi_out, pi_in, pi_ends,
      pi_mf, pi_mk, pi_md, more))
  = pi_caps;

fun pi_fwd
  (Pr_imp_ext
    (pi_fwd, pi_bwd, pi_caps, pi_ex, pi_lab, pi_cnt, pi_out, pi_in, pi_ends,
      pi_mf, pi_mk, pi_md, more))
  = pi_fwd;

fun pi_bwd
  (Pr_imp_ext
    (pi_fwd, pi_bwd, pi_caps, pi_ex, pi_lab, pi_cnt, pi_out, pi_in, pi_ends,
      pi_mf, pi_mk, pi_md, more))
  = pi_bwd;

fun pi_ex
  (Pr_imp_ext
    (pi_fwd, pi_bwd, pi_caps, pi_ex, pi_lab, pi_cnt, pi_out, pi_in, pi_ends,
      pi_mf, pi_mk, pi_md, more))
  = pi_ex;

fun pr_init_step (A1_, A2_) s si d =
  (fn () =>
    let
      val c = arr_lookup_imp A1_ id (pi_caps si) d ();
      val u = src_imp (pi_ends si) d ();
      val v = tgt_imp (pi_ends si) d ();
    in
      (if ((u : Int.int) = s) andalso not ((v : Int.int) = s)
        then (fn f_ => fn () => f_ ((arr_lookup_imp A1_ id (pi_ex si) s) ()) ())
               (fn x =>
                 (fn f_ => fn () => f_
                   ((arr_upd_imp A1_ id (pi_ex si) s
                      (minus
                        ((minus_abs_if o abs_if_linordered_ring o
                           linordered_ring_linordered_ring_strict o
                           linordered_ring_strict_linordered_idom)
                          A2_)
                        x c))
                   ()) ())
                   (fn _ =>
                     (fn f_ => fn () => f_
                       ((arr_upd_imp A1_ id (pi_fwd si) d
                          (zero ((zero_abs_if o abs_if_linordered_ring o
                                   linordered_ring_linordered_ring_strict o
                                   linordered_ring_strict_linordered_idom)
                                  A2_)))
                       ()) ())
                       (fn _ =>
                         (fn f_ => fn () => f_
                           ((arr_upd_imp A1_ id (pi_bwd si) d c) ()) ())
                           (fn _ =>
                             (fn f_ => fn () => f_
                               ((arr_lookup_imp A1_ id (pi_ex si) v) ()) ())
                               (fn y =>
                                 arr_upd_imp A1_ id (pi_ex si) v
                                   (plus ((plus_semigroup_add o
    semigroup_add_numeral o numeral_neg_numeral o neg_numeral_ring_1 o
    ring_1_ring_char_0 o ring_char_0_linordered_idom)
   A2_)
                                     y c))))))
        else (fn f_ => fn () => f_ ((arr_upd_imp A1_ id (pi_fwd si) d c) ()) ())
               (fn _ =>
                 arr_upd_imp A1_ id (pi_bwd si) d
                   (zero ((zero_abs_if o abs_if_linordered_ring o
                            linordered_ring_linordered_ring_strict o
                            linordered_ring_strict_linordered_idom)
                           A2_))))
        ()
    end);

fun pr_init (A1_, A2_) s nv si =
  (fn () =>
    let
      val _ = csr_edge_fold_imp (pi_out si) (pr_init_step (A1_, A2_) s si) ();
      val _ = pr_lb_upd nv (pi_lab si) s nv ();
      val _ =
        arr_upd_imp heap_nat id (pi_cnt si) (0 : Int.int)
          (Machine.sub_nat (nv, (1 : Int.int))) ();
    in
      arr_upd_imp heap_nat id (pi_cnt si) nv (1 : Int.int) ()
    end);

fun pr_move u si =
  (fn () =>
    let
      val b = csr_rt_has_imp heap_nat (pi_out si) u ();
    in
      (if b then csr_rt_move_imp heap_nat (pi_out si) u
        else csr_rt_move_imp heap_nat (pi_in si) u)
        ()
    end);

fun pr_admissible_fwd (A1_, A2_) ei fi li d =
  (fn () =>
    let
      val c = arr_lookup_imp A1_ id fi d ();
    in
      (if less ((ord_abs_if o abs_if_linordered_ring o
                  linordered_ring_linordered_ring_strict o
                  linordered_ring_strict_linordered_idom)
                 A2_)
            (zero ((zero_abs_if o abs_if_linordered_ring o
                     linordered_ring_linordered_ring_strict o
                     linordered_ring_strict_linordered_idom)
                    A2_))
            c
        then (fn f_ => fn () => f_ ((src_imp ei d) ()) ())
               (fn u =>
                 (fn f_ => fn () => f_ ((tgt_imp ei d) ()) ())
                   (fn v =>
                     (fn f_ => fn () => f_ ((pr_lb_get li u) ()) ())
                       (fn a =>
                         (fn f_ => fn () => f_ ((pr_lb_get li v) ()) ())
                           (fn b =>
                             (fn () =>
                               ((a : Int.int) = (Int.+ (b, (1 : Int.int)))))))))
        else (fn () => false))
        ()
    end);

fun pr_admissible_bwd (A1_, A2_) ei bi li d =
  (fn () =>
    let
      val c = arr_lookup_imp A1_ id bi d ();
    in
      (if less ((ord_abs_if o abs_if_linordered_ring o
                  linordered_ring_linordered_ring_strict o
                  linordered_ring_strict_linordered_idom)
                 A2_)
            (zero ((zero_abs_if o abs_if_linordered_ring o
                     linordered_ring_linordered_ring_strict o
                     linordered_ring_strict_linordered_idom)
                    A2_))
            c
        then (fn f_ => fn () => f_ ((src_imp ei d) ()) ())
               (fn u =>
                 (fn f_ => fn () => f_ ((tgt_imp ei d) ()) ())
                   (fn v =>
                     (fn f_ => fn () => f_ ((pr_lb_get li v) ()) ())
                       (fn a =>
                         (fn f_ => fn () => f_ ((pr_lb_get li u) ()) ())
                           (fn b =>
                             (fn () =>
                               ((a : Int.int) = (Int.+ (b, (1 : Int.int)))))))))
        else (fn () => false))
        ()
    end);

fun pr_skip_scan has cur move adm u ci =
  (fn () =>
    let
      val b = has ci u ();
    in
      (if b then (fn f_ => fn () => f_ ((cur ci u) ()) ())
                   (fn e =>
                     (fn f_ => fn () => f_ ((adm e) ()) ())
                       (fn a =>
                         (if a then (fn () => ())
                           else (fn f_ => fn () => f_ ((move ci u) ()) ())
                                  (fn _ =>
                                    pr_skip_scan has cur move adm u ci))))
        else (fn () => ()))
        ()
    end);

fun csr_rt_current_imp A_ =
  (fn (ba, (ea, (ca, _))) => csr_current_imp A_ (ba, (ea, ca)));

fun pr_skip (A1_, A2_) u si =
  (fn () =>
    let
      val _ =
        pr_skip_scan (csr_rt_has_imp heap_nat) (csr_rt_current_imp heap_nat)
          (csr_rt_move_imp heap_nat)
          (pr_admissible_fwd (A1_, A2_) (pi_ends si) (pi_fwd si) (pi_lab si)) u
          (pi_out si) ();
      val b = csr_rt_has_imp heap_nat (pi_out si) u ();
    in
      (if b then (fn () => ())
        else pr_skip_scan (csr_rt_has_imp heap_nat)
               (csr_rt_current_imp heap_nat) (csr_rt_move_imp heap_nat)
               (pr_admissible_bwd (A1_, A2_) (pi_ends si) (pi_bwd si)
                 (pi_lab si))
               u (pi_in si))
        ()
    end);

fun csr_reset_to_imp A_ key =
  (fn (_, (_, (ca, pa))) => fn v => fn e => fn () =>
    let
      val p = (fn () => Array.sub (pa, key e)) ();
      val _ = (fn () => Machine.upd (v, p, ca)) ();
    in
      ()
    end);

fun csr_pos_build_imp A_ key ea pa m =
  foldl_range_imp
    (fn i => fn _ => fn () =>
      let
        val e = (fn () => Array.sub (ea, i)) ();
        val _ = (fn () => Machine.upd (key e, i, pa)) ();
      in
        ()
      end)
    (0 : Int.int) m ();

fun iter_fold has_next next f it c =
  (fn () =>
    let
      val b = has_next it ();
    in
      (if b then (fn f_ => fn () => f_ ((next it) ()) ())
                   (fn (x, ita) =>
                     (fn f_ => fn () => f_ ((f x c) ()) ())
                       (iter_fold has_next next f ita))
        else (fn () => c))
        ()
    end);

fun arq_is_empty_imp A_ =
  (fn (_, (_, sr)) => fn () => let
                                 val s = (fn () => ! sr) ();
                               in
                                 ((s : Int.int) = (0 : Int.int))
                               end);

fun xset_it_has_next B_ it = let
                               val (_, (l, i)) = it;
                             in
                               (fn () => (less B_ i l))
                             end;

fun pr_advance (A1_, A2_) u si = (fn () => let
     val _ = pr_move u si ();
   in
     pr_skip (A1_, A2_) u si ()
   end);

fun pr_augment (A1_, A2_) d u v delta si =
  (fn () =>
    let
      val a = arr_lookup_imp A1_ id (pi_fwd si) d ();
      val _ =
        arr_upd_imp A1_ id (pi_fwd si) d
          (minus
            ((minus_abs_if o abs_if_linordered_ring o
               linordered_ring_linordered_ring_strict o
               linordered_ring_strict_linordered_idom)
              A2_)
            a delta)
          ();
      val b = arr_lookup_imp A1_ id (pi_bwd si) d ();
      val _ =
        arr_upd_imp A1_ id (pi_bwd si) d
          (plus ((plus_semigroup_add o semigroup_add_numeral o
                   numeral_neg_numeral o neg_numeral_ring_1 o
                   ring_1_ring_char_0 o ring_char_0_linordered_idom)
                  A2_)
            b delta)
          ();
      val x = arr_lookup_imp A1_ id (pi_ex si) u ();
      val _ =
        arr_upd_imp A1_ id (pi_ex si) u
          (minus
            ((minus_abs_if o abs_if_linordered_ring o
               linordered_ring_linordered_ring_strict o
               linordered_ring_strict_linordered_idom)
              A2_)
            x delta)
          ();
      val y = arr_lookup_imp A1_ id (pi_ex si) v ();
    in
      arr_upd_imp A1_ id (pi_ex si) v
        (plus ((plus_semigroup_add o semigroup_add_numeral o
                 numeral_neg_numeral o neg_numeral_ring_1 o ring_1_ring_char_0 o
                 ring_char_0_linordered_idom)
                A2_)
          y delta)
        ()
    end);

fun pr_hl_find bi br k =
  (fn () =>
    let
      val a = abk_pick_imp bi k ();
    in
      (case a
        of NONE =>
          (if ((k : Int.int) = (0 : Int.int)) then (fn () => NONE)
            else pr_hl_find bi br (Machine.sub_nat (k, (1 : Int.int))))
        | SOME u =>
          (fn f_ => fn () => f_ (((fn () => br := k)) ()) ())
            (fn _ => (fn () => (SOME u))))
        ()
    end);

fun pr_hl_lift nv bi br k j =
  (if ((j : Int.int) = (0 : Int.int)) orelse Int.<= (j, k) then (fn () => ())
    else (fn () =>
           let
             val a = abk_pick_imp bi j ();
           in
             (case a
               of NONE =>
                 pr_hl_lift nv bi br k (Machine.sub_nat (j, (1 : Int.int)))
               | SOME _ =>
                 (fn f_ => fn () => f_
                   ((abk_move_imp bi j (Int.+ (nv, (1 : Int.int)))) ()) ())
                   (fn _ =>
                     (fn f_ => fn () => f_ (((fn () => ! br)) ()) ())
                       (fn b =>
                         (fn f_ => fn () => f_
                           (((fn () => br :=
                              (max ord_nat b (Int.+ (nv, (1 : Int.int))))))
                           ()) ())
                           (fn _ =>
                             pr_hl_lift nv bi br k
                               (Machine.sub_nat (j, (1 : Int.int)))))))
               ()
           end));

fun equal_pr_op A_ B_ (Relabel_Gap x5) Done = false
  | equal_pr_op A_ B_ Done (Relabel_Gap x5) = false
  | equal_pr_op A_ B_ (Relabel x4) Done = false
  | equal_pr_op A_ B_ Done (Relabel x4) = false
  | equal_pr_op A_ B_ (Relabel x4) (Relabel_Gap x5) = false
  | equal_pr_op A_ B_ (Relabel_Gap x5) (Relabel x4) = false
  | equal_pr_op A_ B_ (Advance x3) Done = false
  | equal_pr_op A_ B_ Done (Advance x3) = false
  | equal_pr_op A_ B_ (Advance x3) (Relabel_Gap x5) = false
  | equal_pr_op A_ B_ (Relabel_Gap x5) (Advance x3) = false
  | equal_pr_op A_ B_ (Advance x3) (Relabel x4) = false
  | equal_pr_op A_ B_ (Relabel x4) (Advance x3) = false
  | equal_pr_op A_ B_ (Push_Bwd x2) Done = false
  | equal_pr_op A_ B_ Done (Push_Bwd x2) = false
  | equal_pr_op A_ B_ (Push_Bwd x2) (Relabel_Gap x5) = false
  | equal_pr_op A_ B_ (Relabel_Gap x5) (Push_Bwd x2) = false
  | equal_pr_op A_ B_ (Push_Bwd x2) (Relabel x4) = false
  | equal_pr_op A_ B_ (Relabel x4) (Push_Bwd x2) = false
  | equal_pr_op A_ B_ (Push_Bwd x2) (Advance x3) = false
  | equal_pr_op A_ B_ (Advance x3) (Push_Bwd x2) = false
  | equal_pr_op A_ B_ (Push_Fwd x1) Done = false
  | equal_pr_op A_ B_ Done (Push_Fwd x1) = false
  | equal_pr_op A_ B_ (Push_Fwd x1) (Relabel_Gap x5) = false
  | equal_pr_op A_ B_ (Relabel_Gap x5) (Push_Fwd x1) = false
  | equal_pr_op A_ B_ (Push_Fwd x1) (Relabel x4) = false
  | equal_pr_op A_ B_ (Relabel x4) (Push_Fwd x1) = false
  | equal_pr_op A_ B_ (Push_Fwd x1) (Advance x3) = false
  | equal_pr_op A_ B_ (Advance x3) (Push_Fwd x1) = false
  | equal_pr_op A_ B_ (Push_Fwd x1) (Push_Bwd x2) = false
  | equal_pr_op A_ B_ (Push_Bwd x2) (Push_Fwd x1) = false
  | equal_pr_op A_ B_ (Relabel_Gap x5) (Relabel_Gap y5) = eq B_ x5 y5
  | equal_pr_op A_ B_ (Relabel x4) (Relabel y4) = eq B_ x4 y4
  | equal_pr_op A_ B_ (Advance x3) (Advance y3) = eq B_ x3 y3
  | equal_pr_op A_ B_ (Push_Bwd x2) (Push_Bwd y2) = eq A_ x2 y2
  | equal_pr_op A_ B_ (Push_Fwd x1) (Push_Fwd y1) = eq A_ x1 y1
  | equal_pr_op A_ B_ Done Done = true;

fun cur_flag_imp A_ cf = (fn () => ! cf);

fun cur_get_imp A_ cu = (fn () => ! cu);

fun pr_discharge_op (A1_, A2_) gap si u =
  (fn () =>
    let
      val b = csr_rt_has_imp heap_nat (pi_out si) u ();
    in
      (if b then (fn f_ => fn () => f_
                   ((csr_rt_current_imp heap_nat (pi_out si) u) ()) ())
                   (fn d =>
                     (fn f_ => fn () => f_
                       ((pr_admissible_fwd (A1_, A2_) (pi_ends si) (pi_fwd si)
                          (pi_lab si) d)
                       ()) ())
                       (fn a =>
                         (fn () => (if a then Push_Fwd d else Advance u))))
        else (fn f_ => fn () => f_ ((csr_rt_has_imp heap_nat (pi_in si) u) ())
               ())
               (fn c =>
                 (if c then (fn f_ => fn () => f_
                              ((csr_rt_current_imp heap_nat (pi_in si) u) ())
                              ())
                              (fn d =>
                                (fn f_ => fn () => f_
                                  ((pr_admissible_bwd (A1_, A2_) (pi_ends si)
                                     (pi_bwd si) (pi_lab si) d)
                                  ()) ())
                                  (fn a =>
                                    (fn () =>
                                      (if a then Push_Bwd d else Advance u))))
                   else (fn () => (if gap then Relabel_Gap u else Relabel u)))))
        ()
    end);

fun cur_set_imp A_ cf cu u = (fn () => let
 val _ = (fn () => cf := true) ();
                                       in
 (fn () => cu := u) ()
                                       end);

fun pr_hl_after_relabel nv bi br cf cu si u =
  (fn () =>
    let
      val k = pr_lb_get (pi_lab si) u ();
      val _ =
        (if Int.< (k, nv)
          then (fn f_ => fn () => f_ ((arr_lookup_imp heap_nat id (pi_cnt si) k)
                 ()) ())
                 (fn c =>
                   (if ((c : Int.int) = (1 : Int.int))
                     then (fn f_ => fn () => f_ (((fn () => ! br)) ()) ())
                            (fn b =>
                              pr_hl_lift nv bi br k
                                (min ord_nat b
                                  (Machine.sub_nat (nv, (1 : Int.int)))))
                     else (fn () => ())))
          else (fn () => ()))
          ();
    in
      cur_set_imp heap_nat cf cu u ()
    end);

fun cur_clear_imp cf = (fn () => cf := false);

fun pr_hl_insert bi br si v =
  (fn () => let
              val lv = pr_lb_get (pi_lab si) v ();
              val _ = abk_insert_imp bi v lv ();
              val b = (fn () => ! br) ();
            in
              (fn () => br := (max ord_nat b lv)) ()
            end);

fun pr_hl_after_push A_ (C1_, C2_) s t bi br cf cu si u v keep =
  (fn () =>
    let
      val _ =
        (if not ((v : Int.int) = s) andalso not ((v : Int.int) = t)
          then (fn f_ => fn () => f_ ((arr_lookup_imp C1_ id (pi_ex si) v) ())
                 ())
                 (fn x =>
                   (if less_eq
                         ((ord_abs_if o abs_if_linordered_ring o
                            linordered_ring_linordered_ring_strict o
                            linordered_ring_strict_linordered_idom)
                           C2_)
                         x (zero ((zero_abs_if o abs_if_linordered_ring o
                                    linordered_ring_linordered_ring_strict o
                                    linordered_ring_strict_linordered_idom)
                                   C2_))
                     then pr_hl_insert bi br si v else (fn () => ())))
          else (fn () => ()))
          ();
    in
      (if keep then cur_set_imp A_ cf cu u else cur_clear_imp cf) ()
    end);

fun pr_hl_ctx_upd (B1_, B2_) s t nv opa bi br cf cu si u =
  (case opa
    of Push_Fwd d =>
      (fn () =>
        let
          val c = arr_lookup_imp B1_ id (pi_fwd si) d ();
          val x = arr_lookup_imp B1_ id (pi_ex si) u ();
          val v = tgt_imp (pi_ends si) d ();
        in
          pr_hl_after_push heap_nat (B1_, B2_) s t bi br cf cu si u v
            (less ((ord_abs_if o abs_if_linordered_ring o
                     linordered_ring_linordered_ring_strict o
                     linordered_ring_strict_linordered_idom)
                    B2_)
              c x)
            ()
        end)
    | Push_Bwd d =>
      (fn () =>
        let
          val c = arr_lookup_imp B1_ id (pi_bwd si) d ();
          val x = arr_lookup_imp B1_ id (pi_ex si) u ();
          val v = src_imp (pi_ends si) d ();
        in
          pr_hl_after_push heap_nat (B1_, B2_) s t bi br cf cu si u v
            (less ((ord_abs_if o abs_if_linordered_ring o
                     linordered_ring_linordered_ring_strict o
                     linordered_ring_strict_linordered_idom)
                    B2_)
              c x)
            ()
        end)
    | Advance _ => cur_set_imp heap_nat cf cu u
    | Relabel _ => cur_set_imp heap_nat cf cu u
    | Relabel_Gap _ => pr_hl_after_relabel nv bi br cf cu si u
    | Done => cur_set_imp heap_nat cf cu u);

fun pr_hl_discharge (A1_, A2_) s t nv bi br cf cu si u =
  (fn () => let
              val opa = pr_discharge_op (A1_, A2_) true si u ();
              val _ = pr_hl_ctx_upd (A1_, A2_) s t nv opa bi br cf cu si u ();
            in
              opa
            end);

fun pr_hl_select (B1_, B2_) s t nv =
  (fn (bi, (br, (cf, (cu, _)))) => fn si => fn () =>
    let
      val f = cur_flag_imp heap_bool cf ();
    in
      (if f then (fn f_ => fn () => f_ ((cur_get_imp heap_nat cu) ()) ())
                   (pr_hl_discharge (B1_, B2_) s t nv bi br cf cu si)
        else (fn f_ => fn () => f_ (((fn () => ! br)) ()) ())
               (fn b =>
                 (fn f_ => fn () => f_ ((pr_hl_find bi br b) ()) ())
                   (fn a =>
                     (case a of NONE => (fn () => Done)
                       | SOME u =>
                         (fn f_ => fn () => f_ (((fn () => ! br)) ()) ())
                           (fn k =>
                             (fn f_ => fn () => f_ ((abk_remove_imp bi u k) ())
                               ())
                               (fn _ =>
                                 pr_hl_discharge (B1_, B2_) s t nv bi br cf cu
                                   si u))))))
        ()
    end);

fun pi_mk
  (Pr_imp_ext
    (pi_fwd, pi_bwd, pi_caps, pi_ex, pi_lab, pi_cnt, pi_out, pi_in, pi_ends,
      pi_mf, pi_mk, pi_md, more))
  = pi_mk;

fun pi_mf
  (Pr_imp_ext
    (pi_fwd, pi_bwd, pi_caps, pi_ex, pi_lab, pi_cnt, pi_out, pi_in, pi_ends,
      pi_mf, pi_mk, pi_md, more))
  = pi_mf;

fun pi_md
  (Pr_imp_ext
    (pi_fwd, pi_bwd, pi_caps, pi_ex, pi_lab, pi_cnt, pi_out, pi_in, pi_ends,
      pi_mf, pi_mk, pi_md, more))
  = pi_md;

fun pr_min_set G_ si k d =
  (fn () => let
              val _ = (fn () => (pi_mf si) := true) ();
              val _ = (fn () => (pi_mk si) := k) ();
            in
              (fn () => (pi_md si) := d) ()
            end);

fun pr_min_scan (A1_, A2_) has cur move ri endp u ci si =
  (fn () =>
    let
      val b = has ci u ();
    in
      (if b then (fn f_ => fn () => f_ ((cur ci u) ()) ())
                   (fn d =>
                     (fn f_ => fn () => f_ ((arr_lookup_imp A1_ id ri d) ()) ())
                       (fn r =>
                         (if less ((ord_abs_if o abs_if_linordered_ring o
                                     linordered_ring_linordered_ring_strict o
                                     linordered_ring_strict_linordered_idom)
                                    A2_)
                               (zero ((zero_abs_if o abs_if_linordered_ring o
linordered_ring_linordered_ring_strict o linordered_ring_strict_linordered_idom)
                                       A2_))
                               r
                           then (fn f_ => fn () => f_ ((endp d) ()) ())
                                  (fn w =>
                                    (fn f_ => fn () => f_
                                      ((pr_lb_get (pi_lab si) w) ()) ())
                                      (fn k =>
(fn f_ => fn () => f_ ((move ci u) ()) ())
  (fn _ =>
    (fn f_ => fn () => f_ (((fn () => ! (pi_mf si))) ()) ())
      (fn f =>
        (fn f_ => fn () => f_ (((fn () => ! (pi_mk si))) ()) ())
          (fn ka =>
            (if not f orelse Int.< (k, ka)
              then (fn f_ => fn () => f_ ((pr_min_set heap_nat si k d) ()) ())
                     (fn _ =>
                       pr_min_scan (A1_, A2_) has cur move ri endp u ci si)
              else pr_min_scan (A1_, A2_) has cur move ri endp u ci si))))))
                           else (fn f_ => fn () => f_ ((move ci u) ()) ())
                                  (fn _ =>
                                    pr_min_scan (A1_, A2_) has cur move ri endp
                                      u ci si))))
        else (fn () => ()))
        ()
    end);

fun pr_new_label (A1_, A2_) u si =
  (fn () =>
    let
      val _ = csr_rt_reset_imp heap_nat (pi_out si) u ();
      val _ = (fn () => (pi_mf si) := false) ();
      val _ =
        pr_min_scan (A1_, A2_) (csr_rt_has_imp heap_nat)
          (csr_rt_current_imp heap_nat) (csr_rt_move_imp heap_nat) (pi_fwd si)
          (tgt_imp (pi_ends si)) u (pi_out si) si ();
      val f1 = (fn () => ! (pi_mf si)) ();
      val m1 = (fn () => ! (pi_mk si)) ();
      val _ = csr_rt_reset_imp heap_nat (pi_in si) u ();
      val _ =
        pr_min_scan (A1_, A2_) (csr_rt_has_imp heap_nat)
          (csr_rt_current_imp heap_nat) (csr_rt_move_imp heap_nat) (pi_bwd si)
          (src_imp (pi_ends si)) u (pi_in si) si ();
      val m = (fn () => ! (pi_mk si)) ();
      val d = (fn () => ! (pi_md si)) ();
    in
      (if not f1 orelse Int.< (m, m1)
        then (fn f_ => fn () => f_
               ((csr_reset_to_imp heap_nat id (pi_in si) u d) ()) ())
               (fn _ => (fn () => (Int.+ (m, (1 : Int.int)))))
        else (fn f_ => fn () => f_
               ((csr_reset_to_imp heap_nat id (pi_out si) u d) ()) ())
               (fn _ =>
                 (fn f_ => fn () => f_ ((csr_rt_reset_imp heap_nat (pi_in si) u)
                   ()) ())
                   (fn _ => (fn () => (Int.+ (m, (1 : Int.int)))))))
        ()
    end);

fun pr_relabel (A1_, A2_) nv u si =
  (fn () => let
              val k = pr_new_label (A1_, A2_) u si ();
            in
              pr_change_label nv u k si ()
            end);

fun pr_relabel_gap (A1_, A2_) nv u si =
  (fn () =>
    let
      val k = pr_lb_get (pi_lab si) u ();
      val _ = pr_relabel (A1_, A2_) nv u si ();
    in
      (if Int.< (k, nv)
        then (fn f_ => fn () => f_ ((arr_lookup_imp heap_nat id (pi_cnt si) k)
               ()) ())
               (fn c =>
                 (if ((c : Int.int) = (0 : Int.int)) then pr_gap nv k si
                   else (fn () => ())))
        else (fn () => ()))
        ()
    end);

fun pr_push_fwd (A1_, A2_) d si =
  (fn () =>
    let
      val u = src_imp (pi_ends si) d ();
      val v = tgt_imp (pi_ends si) d ();
      val x = arr_lookup_imp A1_ id (pi_ex si) u ();
      val c = arr_lookup_imp A1_ id (pi_fwd si) d ();
    in
      pr_augment (A1_, A2_) d u v
        (min ((ord_abs_if o abs_if_linordered_ring o
                linordered_ring_linordered_ring_strict o
                linordered_ring_strict_linordered_idom)
               A2_)
          x c)
        si ()
    end);

fun pr_push_bwd (A1_, A2_) d si =
  (fn () =>
    let
      val u = src_imp (pi_ends si) d ();
      val v = tgt_imp (pi_ends si) d ();
      val x = arr_lookup_imp A1_ id (pi_ex si) v ();
      val c = arr_lookup_imp A1_ id (pi_bwd si) d ();
    in
      pr_augment (A1_, A2_) d u v
        (uminus
          ((uminus_abs_if o abs_if_linordered_ring o
             linordered_ring_linordered_ring_strict o
             linordered_ring_strict_linordered_idom)
            A2_)
          (min ((ord_abs_if o abs_if_linordered_ring o
                  linordered_ring_linordered_ring_strict o
                  linordered_ring_strict_linordered_idom)
                 A2_)
            x c))
        si ()
    end);

fun pr_apply_op (A1_, A2_) nv (Push_Fwd d) si = pr_push_fwd (A1_, A2_) d si
  | pr_apply_op (A1_, A2_) nv (Push_Bwd d) si = pr_push_bwd (A1_, A2_) d si
  | pr_apply_op (A1_, A2_) nv (Advance u) si = pr_advance (A1_, A2_) u si
  | pr_apply_op (A1_, A2_) nv (Relabel u) si = pr_relabel (A1_, A2_) nv u si
  | pr_apply_op (A1_, A2_) nv (Relabel_Gap u) si =
    pr_relabel_gap (A1_, A2_) nv u si
  | pr_apply_op (A1_, A2_) nv Done si = (fn () => ());

fun pr_hl_main_loop (A1_, A2_) s t nv ci si =
  (fn () =>
    let
      val opa = pr_hl_select (A1_, A2_) s t nv ci si ();
    in
      (if equal_pr_op equal_nat equal_nat opa Done then (fn () => ())
        else (fn f_ => fn () => f_ ((pr_apply_op (A1_, A2_) nv opa si) ()) ())
               (fn _ => pr_hl_main_loop (A1_, A2_) s t nv ci si))
        ()
    end);

fun iter_set_fold_imp it_init has_next next si g_imp =
  (fn () => let
              val it = it_init si ();
            in
              iter_fold has_next next (fn x => fn _ => g_imp x) it () ()
            end);

fun pr_hl_init_step (B1_, B2_) s t bi br si v =
  (if not ((v : Int.int) = s) andalso not ((v : Int.int) = t)
    then (fn () =>
           let
             val x = arr_lookup_imp B1_ id (pi_ex si) v ();
           in
             (if less ((ord_abs_if o abs_if_linordered_ring o
                         linordered_ring_linordered_ring_strict o
                         linordered_ring_strict_linordered_idom)
                        B2_)
                   (zero ((zero_abs_if o abs_if_linordered_ring o
                            linordered_ring_linordered_ring_strict o
                            linordered_ring_strict_linordered_idom)
                           B2_))
                   x
               then pr_hl_insert bi br si v else (fn () => ()))
               ()
           end)
    else (fn () => ()));

fun pr_hl_init_ctx (C1_, C2_) s t =
  (fn (bi, (br, (cf, (_, vi)))) => fn si => fn () =>
    let
      val _ = (fn () => br := (0 : Int.int)) ();
      val _ =
        iter_set_fold_imp xset_it_init (xset_it_has_next ord_nat) xset_it_next
          vi (pr_hl_init_step (C1_, C2_) s t bi br si) ();
    in
      cur_clear_imp cf ()
    end);

fun pr_hl_main (A1_, A2_) s t nv ci si =
  (fn () => let
              val _ = pr_init (A1_, A2_) s nv si ();
              val _ = pr_hl_init_ctx (A1_, A2_) s t ci si ();
            in
              pr_hl_main_loop (A1_, A2_) s t nv ci si ()
            end);

fun pr_lb_init (C1_, C2_) vfold_imp =
  (fn (_, (bi, dr)) => fn () =>
    let
      val _ = vfold_imp (fn v => abk_insert_imp bi v (0 : Int.int)) ();
    in
      (fn () => dr := (zero C1_)) ()
    end);

fun amtf_push_front_imp x =
  (fn (fr, (nXa, pVa)) => fn xa => fn () =>
    let
      val f = (fn () => ! fr) ();
      val _ = (fn () => Machine.upd (xa, f, nXa)) ();
      val _ = (fn () => Machine.upd (xa, NONE, pVa)) ();
      val _ =
        (case f of NONE => (fn () => pVa)
          | SOME y => (fn () => Machine.upd (y, SOME xa, pVa)))
          ();
    in
      (fn () => fr := (SOME xa)) ()
    end)
    x;

fun amtf_remove_imp x =
  (fn (fr, (nXa, pVa)) => fn xa => fn () =>
    let
      val p = (fn () => Array.sub (pVa, xa)) ();
      val q = (fn () => Array.sub (nXa, xa)) ();
      val _ =
        (case p of NONE => (fn () => fr := q)
          | SOME a =>
            (fn f_ => fn () => f_ (((fn () => Machine.upd (a, q, nXa))) ()) ())
              (fn _ => (fn () => ())))
          ();
      val _ =
        (case q of NONE => (fn () => pVa)
          | SOME b => (fn () => Machine.upd (b, p, pVa)))
          ();
    in
      ()
    end)
    x;

fun amtf_move_to_front_imp li x = (fn () => let
      val _ = amtf_remove_imp li x ();
    in
      amtf_push_front_imp li x ()
    end);

fun pr_rtf_discharge (A1_, A2_) rr si u =
  (fn () =>
    let
      val opa = pr_discharge_op (A1_, A2_) false si u ();
      val _ =
        (case opa of Push_Fwd _ => (fn () => ()) | Push_Bwd _ => (fn () => ())
          | Advance _ => (fn () => ()) | Relabel _ => (fn () => rr := true)
          | Relabel_Gap _ => (fn () => ()) | Done => (fn () => ()))
          ();
    in
      opa
    end);

fun amtf_next_imp x =
  (fn (_, (nXa, _)) => (fn a => (fn () => Array.sub (nXa, a)))) x;

fun pr_rtf_stop cf rr = (fn () => let
                                    val _ = cur_clear_imp cf ();
                                    val _ = (fn () => rr := false) ();
                                  in
                                    Done
                                  end);

fun pr_rtf_scan (A1_, A2_) ls si n u =
  (if ((n : Int.int) = (0 : Int.int)) then (fn () => NONE)
    else (fn () =>
           let
             val x = arr_lookup_imp A1_ id (pi_ex si) u ();
           in
             (if less ((ord_abs_if o abs_if_linordered_ring o
                         linordered_ring_linordered_ring_strict o
                         linordered_ring_strict_linordered_idom)
                        A2_)
                   (zero ((zero_abs_if o abs_if_linordered_ring o
                            linordered_ring_linordered_ring_strict o
                            linordered_ring_strict_linordered_idom)
                           A2_))
                   x
               then (fn () => (SOME u))
               else (fn f_ => fn () => f_ ((amtf_next_imp ls u) ()) ())
                      (fn a =>
                        (case a of NONE => (fn () => NONE)
                          | SOME aa =>
                            pr_rtf_scan (A1_, A2_) ls si
                              (Machine.sub_nat (n, (1 : Int.int))) aa)))
               ()
           end));

fun pr_rtf_next (A1_, A2_) nv ls cf cu rr si u =
  (fn () =>
    let
      val a = amtf_next_imp ls u ();
    in
      (case a of NONE => pr_rtf_stop cf rr
        | SOME w0 =>
          (fn f_ => fn () => f_ ((pr_rtf_scan (A1_, A2_) ls si nv w0) ()) ())
            (fn aa =>
              (case aa of NONE => pr_rtf_stop cf rr
                | SOME w =>
                  (fn f_ => fn () => f_ ((cur_set_imp heap_nat cf cu w) ()) ())
                    (fn _ =>
                      (fn f_ => fn () => f_ (((fn () => rr := false)) ()) ())
                        (fn _ => pr_rtf_discharge (A1_, A2_) rr si w)))))
        ()
    end);

fun pr_rtf_select (B1_, B2_) nv =
  (fn (ls, (cf, (cu, (rr, _)))) => fn si => fn () =>
    let
      val f = cur_flag_imp heap_bool cf ();
    in
      (if not f then (fn () => Done)
        else (fn f_ => fn () => f_ ((cur_get_imp heap_nat cu) ()) ())
               (fn u =>
                 (fn f_ => fn () => f_ ((arr_lookup_imp B1_ id (pi_ex si) u) ())
                   ())
                   (fn x =>
                     (if less ((ord_abs_if o abs_if_linordered_ring o
                                 linordered_ring_linordered_ring_strict o
                                 linordered_ring_strict_linordered_idom)
                                B2_)
                           (zero ((zero_abs_if o abs_if_linordered_ring o
                                    linordered_ring_linordered_ring_strict o
                                    linordered_ring_strict_linordered_idom)
                                   B2_))
                           x
                       then pr_rtf_discharge (B1_, B2_) rr si u
                       else (fn f_ => fn () => f_ (((fn () => ! rr)) ()) ())
                              (fn rel =>
                                (fn f_ => fn () => f_
                                  ((if rel then amtf_move_to_front_imp ls u
                                     else (fn () => ()))
                                  ()) ())
                                  (fn _ =>
                                    pr_rtf_next (B1_, B2_) nv ls cf cu rr si
                                      u))))))
        ()
    end);

fun pr_rtf_main_loop (A1_, A2_) nv ci si =
  (fn () =>
    let
      val opa = pr_rtf_select (A1_, A2_) nv ci si ();
    in
      (if equal_pr_op equal_nat equal_nat opa Done then (fn () => ())
        else (fn f_ => fn () => f_ ((pr_apply_op (A1_, A2_) nv opa si) ()) ())
               (fn _ => pr_rtf_main_loop (A1_, A2_) nv ci si))
        ()
    end);

fun pr_rtf_init_step s t ls v =
  (if not ((v : Int.int) = s) andalso not ((v : Int.int) = t)
    then amtf_push_front_imp ls v else (fn () => ()));

fun amtf_first_imp x = (fn (fr, (_, _)) => (fn () => ! fr)) x;

fun pr_rtf_init_ctx s t =
  (fn (ls, (cf, (cu, (rr, vi)))) => fn _ => fn () =>
    let
      val _ =
        iter_set_fold_imp xset_it_init (xset_it_has_next ord_nat) xset_it_next
          vi (pr_rtf_init_step s t ls) ();
      val f = amtf_first_imp ls ();
      val _ =
        (case f of NONE => cur_clear_imp cf
          | SOME a => cur_set_imp heap_nat cf cu a)
          ();
    in
      (fn () => rr := false) ()
    end);

fun pr_rtf_main (A1_, A2_) s t nv ci si =
  (fn () => let
              val _ = pr_init (A1_, A2_) s nv si ();
              val _ = pr_rtf_init_ctx s t ci si ();
            in
              pr_rtf_main_loop (A1_, A2_) nv ci si ()
            end);

fun pr_csr_setup build n fa ta m =
  (fn () =>
    let
      val a = build n (fa, ta) (0 : Int.int) ();
    in
      let
        val (ba, ea) = a;
      in
        (fn f_ => fn () => f_ (((fn () => Array.array (m, (0 : Int.int)))) ())
          ())
          (fn pa =>
            (fn f_ => fn () => f_ ((csr_pos_build_imp heap_nat id ea pa m) ())
              ())
              (fn _ =>
                (fn f_ => fn () => f_ ((csr_cursor_init n ba) ()) ())
                  (fn oa => (fn () => (ba, (ea, (oa, pa)))))))
      end
        ()
    end);

fun pr_fifo_after_push A_ (C1_, C2_) s t nv qi cf cu si u v keep =
  (fn () =>
    let
      val _ =
        (if not ((v : Int.int) = s) andalso not ((v : Int.int) = t)
          then (fn f_ => fn () => f_ ((arr_lookup_imp C1_ id (pi_ex si) v) ())
                 ())
                 (fn x =>
                   (if less_eq
                         ((ord_abs_if o abs_if_linordered_ring o
                            linordered_ring_linordered_ring_strict o
                            linordered_ring_strict_linordered_idom)
                           C2_)
                         x (zero ((zero_abs_if o abs_if_linordered_ring o
                                    linordered_ring_linordered_ring_strict o
                                    linordered_ring_strict_linordered_idom)
                                   C2_))
                     then arq_push_imp heap_nat nv qi v else (fn () => ())))
          else (fn () => ()))
          ();
    in
      (if keep then cur_set_imp A_ cf cu u else cur_clear_imp cf) ()
    end);

fun pr_fifo_ctx_upd (B1_, B2_) s t nv opa qi cf cu si u =
  (case opa
    of Push_Fwd d =>
      (fn () =>
        let
          val c = arr_lookup_imp B1_ id (pi_fwd si) d ();
          val x = arr_lookup_imp B1_ id (pi_ex si) u ();
          val v = tgt_imp (pi_ends si) d ();
        in
          pr_fifo_after_push heap_nat (B1_, B2_) s t nv qi cf cu si u v
            (less ((ord_abs_if o abs_if_linordered_ring o
                     linordered_ring_linordered_ring_strict o
                     linordered_ring_strict_linordered_idom)
                    B2_)
              c x)
            ()
        end)
    | Push_Bwd d =>
      (fn () =>
        let
          val c = arr_lookup_imp B1_ id (pi_bwd si) d ();
          val x = arr_lookup_imp B1_ id (pi_ex si) u ();
          val v = src_imp (pi_ends si) d ();
        in
          pr_fifo_after_push heap_nat (B1_, B2_) s t nv qi cf cu si u v
            (less ((ord_abs_if o abs_if_linordered_ring o
                     linordered_ring_linordered_ring_strict o
                     linordered_ring_strict_linordered_idom)
                    B2_)
              c x)
            ()
        end)
    | Advance _ => cur_set_imp heap_nat cf cu u
    | Relabel _ => (fn () => let
                               val _ = arq_push_imp heap_nat nv qi u ();
                             in
                               cur_clear_imp cf ()
                             end)
    | Relabel_Gap _ => (fn () => let
                                   val _ = arq_push_imp heap_nat nv qi u ();
                                 in
                                   cur_clear_imp cf ()
                                 end)
    | Done => (fn () => let
                          val _ = arq_push_imp heap_nat nv qi u ();
                        in
                          cur_clear_imp cf ()
                        end));

fun pr_fifo_discharge (A1_, A2_) s t nv qi cf cu si u =
  (fn () => let
              val opa = pr_discharge_op (A1_, A2_) true si u ();
              val _ = pr_fifo_ctx_upd (A1_, A2_) s t nv opa qi cf cu si u ();
            in
              opa
            end);

fun pr_fifo_select (B1_, B2_) s t nv =
  (fn (qi, (cf, (cu, _))) => fn si => fn () =>
    let
      val f = cur_flag_imp heap_bool cf ();
    in
      (if f then (fn f_ => fn () => f_ ((cur_get_imp heap_nat cu) ()) ())
                   (pr_fifo_discharge (B1_, B2_) s t nv qi cf cu si)
        else (fn f_ => fn () => f_ ((arq_is_empty_imp heap_nat qi) ()) ())
               (fn e =>
                 (if e then (fn () => Done)
                   else (fn f_ => fn () => f_ ((arq_pop_imp heap_nat nv qi) ())
                          ())
                          (pr_fifo_discharge (B1_, B2_) s t nv qi cf cu si))))
        ()
    end);

fun pr_fifo_main_loop (A1_, A2_) s t nv ci si =
  (fn () =>
    let
      val opa = pr_fifo_select (A1_, A2_) s t nv ci si ();
    in
      (if equal_pr_op equal_nat equal_nat opa Done then (fn () => ())
        else (fn f_ => fn () => f_ ((pr_apply_op (A1_, A2_) nv opa si) ()) ())
               (fn _ => pr_fifo_main_loop (A1_, A2_) s t nv ci si))
        ()
    end);

fun pr_fifo_init_step (B1_, B2_) s t nv qi si v =
  (if not ((v : Int.int) = s) andalso not ((v : Int.int) = t)
    then (fn () =>
           let
             val x = arr_lookup_imp B1_ id (pi_ex si) v ();
           in
             (if less ((ord_abs_if o abs_if_linordered_ring o
                         linordered_ring_linordered_ring_strict o
                         linordered_ring_strict_linordered_idom)
                        B2_)
                   (zero ((zero_abs_if o abs_if_linordered_ring o
                            linordered_ring_linordered_ring_strict o
                            linordered_ring_strict_linordered_idom)
                           B2_))
                   x
               then arq_push_imp heap_nat nv qi v else (fn () => ()))
               ()
           end)
    else (fn () => ()));

fun pr_fifo_init_ctx (C1_, C2_) s t nv =
  (fn (qi, (cf, (_, vi))) => fn si => fn () =>
    let
      val _ =
        iter_set_fold_imp xset_it_init (xset_it_has_next ord_nat) xset_it_next
          vi (pr_fifo_init_step (C1_, C2_) s t nv qi si) ();
    in
      cur_clear_imp cf ()
    end);

fun pr_fifo_main (A1_, A2_) s t nv ci si =
  (fn () => let
              val _ = pr_init (A1_, A2_) s nv si ();
              val _ = pr_fifo_init_ctx (A1_, A2_) s t nv ci si ();
            in
              pr_fifo_main_loop (A1_, A2_) s t nv ci si ()
            end);

fun amtf_empty_imp n =
  (fn () => let
              val fr = refa (heap_option heap_nat) NONE ();
              val nXa = (fn () => Array.array (n, NONE)) ();
              val pVa = (fn () => Array.array (n, NONE)) ();
            in
              (fr, (nXa, pVa))
            end);

fun pr_vertex_count_step vi u c =
  (fn () =>
    let
      val b = (fn () => Array.sub (vi, u)) ();
    in
      (if b then (fn () => c)
        else (fn f_ => fn () => f_ ((xset_insert_imp u vi) ()) ())
               (fn _ => (fn () => (Int.+ (c, (1 : Int.int))))))
        ()
    end);

fun pr_vertex_set_imp fa ta vi m =
  foldl_range_imp
    (fn i => fn c => fn () => let
                                val u = (fn () => Array.sub (fa, i)) ();
                                val v = (fn () => Array.sub (ta, i)) ();
                                val x = pr_vertex_count_step vi u c ();
                              in
                                pr_vertex_count_step vi v x ()
                              end)
    (0 : Int.int) m (0 : Int.int);

fun push_relabel_setup (A1_, A2_) n fa ta ca =
  (fn () =>
    let
      val m = (fn () => Array.length fa) ();
      val oi = pr_csr_setup csr_build_edges n fa ta m ();
      val ii = pr_csr_setup csr_build_edges_tgt n fa ta m ();
      val vi = (fn () => Array.array (n, false)) ();
      val nv = pr_vertex_set_imp fa ta vi m ();
      val fw =
        (fn () => Array.array (m,
          zero ((zero_abs_if o abs_if_linordered_ring o
                  linordered_ring_linordered_ring_strict o
                  linordered_ring_strict_linordered_idom)
                 A2_)))
          ();
      val bw =
        (fn () => Array.array (m,
          zero ((zero_abs_if o abs_if_linordered_ring o
                  linordered_ring_linordered_ring_strict o
                  linordered_ring_strict_linordered_idom)
                 A2_)))
          ();
      val xa =
        (fn () => Array.array (n,
          zero ((zero_abs_if o abs_if_linordered_ring o
                  linordered_ring_linordered_ring_strict o
                  linordered_ring_strict_linordered_idom)
                 A2_)))
          ();
      val la = (fn () => Array.array (n, (0 : Int.int))) ();
      val lb = abk_empty_imp n nv ();
      val dr = refa heap_nat (0 : Int.int) ();
      val _ =
        pr_lb_init (zero_nat, heap_nat)
          (iter_set_fold_imp xset_it_init (xset_it_has_next ord_nat)
            xset_it_next vi)
          (la, (lb, dr)) ();
      val cn =
        (fn () => Array.array (Int.* ((2 : Int.int), nv), (0 : Int.int))) ();
      val mf = refa heap_bool false ();
      val mk = refa heap_nat (0 : Int.int) ();
      val md = refa heap_nat (0 : Int.int) ();
    in
      (Pr_imp_ext
         (fw, bw, ca, xa, (la, (lb, dr)), cn, oi, ii, (fa, ta), mf, mk, md, ()),
        (vi, nv))
    end);

fun push_relabel_hl_run (A1_, A2_) n s t fa ta ca =
  (fn () =>
    let
      val a = push_relabel_setup (A1_, A2_) n fa ta ca ();
    in
      let
        val (si, (vi, nv)) = a;
      in
        (fn f_ => fn () => f_ ((abk_empty_imp n (Int.* ((2 : Int.int), nv))) ())
          ())
          (fn bi =>
            (fn f_ => fn () => f_ ((refa heap_nat (0 : Int.int)) ()) ())
              (fn br =>
                (fn f_ => fn () => f_ ((refa heap_bool false) ()) ())
                  (fn cf =>
                    (fn f_ => fn () => f_ ((refa heap_nat (0 : Int.int)) ()) ())
                      (fn cu =>
                        (fn f_ => fn () => f_
                          ((pr_hl_main (A1_, A2_) s t nv
                             (bi, (br, (cf, (cu, vi)))) si)
                          ()) ())
                          (fn _ => (fn () => (pi_bwd si)))))))
      end
        ()
    end);

fun push_relabel_rtf_run (A1_, A2_) n s t fa ta ca =
  (fn () =>
    let
      val a = push_relabel_setup (A1_, A2_) n fa ta ca ();
    in
      let
        val (si, (vi, nv)) = a;
      in
        (fn f_ => fn () => f_ ((amtf_empty_imp n) ()) ())
          (fn ls =>
            (fn f_ => fn () => f_ ((refa heap_bool false) ()) ())
              (fn cf =>
                (fn f_ => fn () => f_ ((refa heap_nat (0 : Int.int)) ()) ())
                  (fn cu =>
                    (fn f_ => fn () => f_ ((refa heap_bool false) ()) ())
                      (fn rr =>
                        (fn f_ => fn () => f_
                          ((pr_rtf_main (A1_, A2_) s t nv
                             (ls, (cf, (cu, (rr, vi)))) si)
                          ()) ())
                          (fn _ => (fn () => (pi_bwd si)))))))
      end
        ()
    end);

fun push_relabel_fifo_run (A1_, A2_) n s t fa ta ca =
  (fn () =>
    let
      val a = push_relabel_setup (A1_, A2_) n fa ta ca ();
    in
      let
        val (si, (vi, nv)) = a;
      in
        (fn f_ => fn () => f_ ((arq_empty_imp heap_nat nv (0 : Int.int)) ()) ())
          (fn qi =>
            (fn f_ => fn () => f_ ((refa heap_bool false) ()) ())
              (fn cf =>
                (fn f_ => fn () => f_ ((refa heap_nat (0 : Int.int)) ()) ())
                  (fn cu =>
                    (fn f_ => fn () => f_
                      ((pr_fifo_main (A1_, A2_) s t nv (qi, (cf, (cu, vi))) si)
                      ()) ())
                      (fn _ => (fn () => (pi_bwd si))))))
      end
        ()
    end);

fun push_relabel_hl_run_int x =
  push_relabel_hl_run (heap_int, linordered_idom_int) x;

fun push_relabel_rtf_run_int x =
  push_relabel_rtf_run (heap_int, linordered_idom_int) x;

fun push_relabel_fifo_run_int x =
  push_relabel_fifo_run (heap_int, linordered_idom_int) x;

end; (*struct Push_Relabel*)
