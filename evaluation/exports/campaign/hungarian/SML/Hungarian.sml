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


structure Hungarian : sig
  type result
  val hungarian_csr_mw_run_int :
    bool ->
      Int.int ->
        Int.int ->
          Int.int ->
            Int.int array ->
              Int.int array ->
                Int.int array ->
                  Int.int array -> Int.int array -> (unit -> (Int.int array))
  val hungarian_csr_mwmc_run_int :
    bool ->
      Int.int ->
        Int.int ->
          Int.int ->
            Int.int array ->
              Int.int array ->
                Int.int array ->
                  Int.int array -> Int.int array -> (unit -> (Int.int array))
  val hungarian_csr_max_perfect_run_int :
    Int.int ->
      Int.int ->
        Int.int ->
          Int.int array ->
            Int.int array ->
              Int.int array ->
                Int.int array ->
                  Int.int array ->
                    (unit -> (result * (Int.int array * Int.int array)))
  val hungarian_csr_run_int :
    Int.int ->
      Int.int ->
        Int.int ->
          Int.int array ->
            Int.int array ->
              Int.int array ->
                Int.int array ->
                  Int.int array ->
                    (unit -> (result * (Int.int array * Int.int array)))
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

val equal_nat = {equal = (fn a => fn b => ((a : Int.int) = b))} : Int.int equal;

fun typerep_nata t = Typerep ("Nat.nat", []);

val countable_nat = {} : Int.int countable;

val typerep_nat = {typerep = typerep_nata} : Int.int typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  Int.int heap;

val ord_nat =
  {less_eq = (fn a => fn b => Int.<= (a, b)),
    less = (fn a => fn b => Int.< (a, b))}
  : Int.int ord;

fun typerep_boola t = Typerep ("HOL.bool", []);

val countable_bool = {} : bool countable;

val typerep_bool = {typerep = typerep_boola} : bool typerep;

val heap_bool = {countable_heap = countable_bool, typerep_heap = typerep_bool} :
  bool heap;

fun typerep_proda A_ B_ t =
  Typerep ("Product_Type.prod", [typerep A_ Type, typerep B_ Type]);

fun countable_prod A_ B_ = {} : ('a * 'b) countable;

fun typerep_prod A_ B_ = {typerep = typerep_proda A_ B_} : ('a * 'b) typerep;

fun heap_prod A_ B_ =
  {countable_heap = countable_prod (countable_heap A_) (countable_heap B_),
    typerep_heap = typerep_prod (typerep_heap A_) (typerep_heap B_)}
  : ('a * 'b) heap;

datatype num = One | Bit0 of num | Bit1 of num;

datatype result = Success | Failure | Notyetterm;

datatype imp_search_result = Imp_Unbounded | Imp_Matched | Imp_Path of Int.int;

datatype forest_part = Evens | Odds;

fun eq A_ a b = equal A_ a b;

fun refa A_ x = (fn () => ref x);

fun snd (x1, x2) = x2;

fun e_id e = snd (snd e);

fun fst (x1, x2) = x1;

fun e_src e = fst e;

fun e_tgt e = fst (snd e);

fun edge_adv x = (fn _ => fn i => (fn () => (Int.+ (i, (1 : Int.int))))) x;

fun edge_cur x =
  (fn (fa, ta) => fn i => fn () => let
                                     val u = (fn () => Array.sub (fa, i)) ();
                                     val v = (fn () => Array.sub (ta, i)) ();
                                   in
                                     (u, (v, i))
                                   end)
    x;

fun edge_key e = (fn () => (e_src e));

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

fun wnb_has_imp A_ B_ = (fn (ci, _) => csr_has_imp A_ ci);

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

fun wnb_move_imp A_ B_ = (fn (ci, _) => csr_move_imp A_ ci);

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

fun wnb_reset_imp A_ B_ = (fn (ci, _) => csr_reset_imp A_ ci);

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
                 (fn f_ => fn () => f_ ((edge_key ea) ()) ())
                   (fn k =>
                     (fn f_ => fn () => f_
                       (((fn () => Array.sub (b, Int.+ (k, (1 : Int.int))))) ())
                       ())
                       (fn p =>
                         (fn f_ => fn () => f_
                           (((fn () => Machine.upd (Int.+ (k, (1 : Int.int)),
                              Int.+ (p, (1 : Int.int)), b)))
                           ()) ())
                           (fn _ =>
                             (fn f_ => fn () => f_
                               (((fn () => Machine.upd (p, ea, e))) ()) ())
                               (fn _ =>
                                 (fn f_ => fn () => f_ ((edge_adv c si) ()) ())
                                   (csr_fill_edges c b e))))))
        else (fn () => ()))
        ()
    end);

fun csr_init_edges c si m =
  (fn () =>
    let
      val b = edge_has_next c si ();
    in
      (if b then (fn f_ => fn () => f_ ((edge_cur c si) ()) ())
                   (fn a => (fn () => Array.array (m, a)))
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
                 (fn f_ => fn () => f_ ((edge_key e) ()) ())
                   (fn k =>
                     (fn f_ => fn () => f_
                       ((if Int.<= (Int.+ (k, (2 : Int.int)), n)
                          then (fn f_ => fn () => f_
                                 (((fn () => Array.sub (b,
                                    Int.+ (k, (2 : Int.int)))))
                                 ()) ())
                                 (fn ca =>
                                   (fn f_ => fn () => f_
                                     (((fn () => Machine.upd
(Int.+ (k, (2 : Int.int)), Int.+ (ca, (1 : Int.int)), b)))
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

fun wnb_current_imp A_ C_ tgt =
  (fn (ci, _) => fn v => fn () => let
                                    val e = csr_current_imp A_ ci v ();
                                  in
                                    tgt e
                                  end);

fun numeral A_ One = one (one_numeral A_)
  | numeral A_ (Bit0 n) =
    let
      val m = numeral A_ n;
    in
      plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m
    end
  | numeral A_ (Bit1 n) =
    let
      val m = numeral A_ n;
    in
      plus ((plus_semigroup_add o semigroup_add_numeral) A_)
        (plus ((plus_semigroup_add o semigroup_add_numeral) A_) m m)
        (one (one_numeral A_))
    end;

fun divmod_nat m n = (Machine.div_nat (m, n), Machine.mod_nat (m, n));

fun xmap_upd_imp A_ xi k x =
  (fn () => let
              val _ = (fn () => Machine.upd (k, x, xi)) ();
            in
              ()
            end);

fun wnb_reset_all_imp A_ B_ n =
  (fn (a, b) => let
                  val (ba, (_, ca)) = a;
                in
                  (fn _ => csr_copy_imp n ba ca (0 : Int.int))
                end
                  b);

fun foldl_range_imp f i n a =
  (if Int.< (i, n)
    then (fn () => let
                     val x = f i a ();
                   in
                     foldl_range_imp f (Int.+ (i, (1 : Int.int))) n x ()
                   end)
    else (fn () => a));

fun fill_range_imp A_ f n a =
  foldl_range_imp (fn i => (fn aa => (fn () => Machine.upd (i, f i, aa))))
    (0 : Int.int) n a;

fun xset_clear_imp n xi = fill_range_imp heap_bool (fn _ => false) n xi;

fun of_nat A_ n =
  (if ((n : Int.int) = (0 : Int.int))
    then zero ((zero_mult_zero o mult_zero_semiring_0 o semiring_0_semiring_1)
                A_)
    else let
           val (m, q) = divmod_nat n (2 : Int.int);
           val ma =
             times ((times_power o power_monoid_mult o
                      monoid_mult_semiring_numeral o
                      semiring_numeral_semiring_1)
                     A_)
               (numeral
                 ((numeral_semiring_numeral o semiring_numeral_semiring_1) A_)
                 (Bit0 One))
               (of_nat A_ m);
         in
           (if ((q : Int.int) = (0 : Int.int)) then ma
             else plus ((plus_semigroup_add o semigroup_add_numeral o
                          numeral_semiring_numeral o
                          semiring_numeral_semiring_1)
                         A_)
                    ma (one ((one_numeral o numeral_semiring_numeral o
                               semiring_numeral_semiring_1)
                              A_)))
         end);

fun sgn_w A_ b w = (if b then uminus A_ w else w);

fun xmap_clear_imp A_ x n xi = fill_range_imp A_ (fn _ => x) n xi;

fun xset_insert_imp x xi =
  (fn () => let
              val _ = (fn () => Machine.upd (x, true, xi)) ();
            in
              ()
            end);

fun xmap_lookup_imp A_ xi k = (fn () => Array.sub (xi, k));

fun wnb_current_cost_imp A_ B_ =
  (fn (a, b) =>
    let
      val (_, (_, ca)) = a;
    in
      (fn wa => fn v => fn () => let
                                   val x = (fn () => Array.sub (ca, v)) ();
                                 in
                                   (fn () => Array.sub (wa, x)) ()
                                 end)
    end
      b);

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

fun fold_imp i m f s =
  (if Int.< (i, m)
    then (fn () => let
                     val x = f i s ();
                   in
                     fold_imp (Int.+ (i, (1 : Int.int))) m f x ()
                   end)
    else (fn () => s));

fun neg_step (A1_, A2_) wa wn i u =
  (fn () => let
              val w = (fn () => Array.sub (wa, i)) ();
              val _ = (fn () => Machine.upd (i, uminus A1_ w, wn)) ();
            in
              ()
            end);

fun pad_step s l nv aa a u =
  (fn () =>
    let
      val x =
        (if Int.< (a, l) then (fn () => Array.sub (s, a))
          else (fn () => (Int.+ (nv, Machine.sub_nat (a, l)))))
          ();
      val _ = (fn () => Machine.upd (a, x, aa)) ();
    in
      ()
    end);

fun pos_step s p a u =
  (fn () => let
              val x = (fn () => Array.sub (s, a)) ();
              val _ = (fn () => Machine.upd (x, a, p)) ();
            in
              ()
            end);

fun wgt_step A_ cf k fa ta wa pa wc i u =
  (fn () =>
    let
      val x = (fn () => Array.sub (fa, i)) ();
      val y = (fn () => Array.sub (ta, i)) ();
      val px = (fn () => Array.sub (pa, x)) ();
      val py = (fn () => Array.sub (pa, y)) ();
      val w = (fn () => Array.sub (wa, i)) ();
      val _ = (fn () => Machine.upd (Int.+ (Int.* (px, k), py), cf w, wc)) ();
    in
      ()
    end);

fun grid_step k asa bs fa ta j u =
  (fn () => let
              val x = (fn () => Array.sub (asa, Machine.div_nat (j, k))) ();
              val y = (fn () => Array.sub (bs, Machine.mod_nat (j, k))) ();
              val _ = (fn () => Machine.upd (j, x, fa)) ();
              val _ = (fn () => Machine.upd (j, y, ta)) ();
            in
              ()
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

fun extract_imp_step A_ kp n k la pa wc mi mo a s =
  (fn () =>
    let
      val u = (fn () => Array.sub (la, a)) ();
      val v = xmap_lookup_imp heap_nat mi u ();
    in
      (if ((v : Int.int) = n) then (fn () => ())
        else (fn f_ => fn () => f_ (((fn () => Array.sub (pa, v))) ()) ())
               (fn pv =>
                 (fn f_ => fn () => f_
                   (((fn () => Array.sub (wc, Int.+ (Int.* (a, k), pv)))) ())
                   ())
                   (fn w =>
                     (if kp w
                       then (fn f_ => fn () => f_
                              ((xmap_upd_imp heap_nat mo u v) ()) ())
                              (fn _ => xmap_upd_imp heap_nat mo v u)
                       else (fn () => ())))))
        ()
    end);

fun extract_imp A_ kp n k la pa wc mi mo =
  (fn () =>
    let
      val l = (fn () => Array.length la) ();
    in
      fold_imp (0 : Int.int) l (extract_imp_step A_ kp n k la pa wc mi mo) () ()
    end);

fun max_abs_step (A1_, A2_) wa i s =
  (fn () =>
    let
      val w = (fn () => Array.sub (wa, i)) ();
    in
      max ((ord_abs_if o abs_if_linordered_ring o
             linordered_ring_linordered_ring_strict o
             linordered_ring_strict_linordered_idom)
            A2_)
        (abs ((abs_abs_if o abs_if_linordered_ring o
                linordered_ring_linordered_ring_strict o
                linordered_ring_strict_linordered_idom)
               A2_)
          w)
        s
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

fun xset_it_has_next B_ it = let
                               val (_, (l, i)) = it;
                             in
                               (fn () => (less B_ i l))
                             end;

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

fun heap_clear_imp hi = let
                          val (_, (_, (_, sr))) = hi;
                        in
                          (fn () => sr := (0 : Int.int))
                        end;

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

fun heap_key_of_imp (A1_, A2_) hi x =
  let
    val (ha, (pa, (ka, sr))) = hi;
  in
    (fn () =>
      let
        val sz = (fn () => ! sr) ();
        val i = (fn () => Array.sub (pa, x)) ();
      in
        (if Int.< (i, sz)
          then (fn f_ => fn () => f_ (((fn () => Array.sub (ha, i))) ()) ())
                 (fn y =>
                   (if ((y : Int.int) = x)
                     then (fn f_ => fn () => f_ (((fn () => Array.sub (ka, x)))
                            ()) ())
                            (fn k => (fn () => (SOME k)))
                     else (fn () => NONE)))
          else (fn () => NONE))
          ()
      end)
  end;

fun perm_weights_imp A_ ea wa wc i m =
  (if Int.< (i, m)
    then (fn () =>
           let
             val e = (fn () => Array.sub (ea, i)) ();
             val w = (fn () => Array.sub (wa, e_id e)) ();
             val _ = (fn () => Machine.upd (i, w, wc)) ();
           in
             perm_weights_imp A_ ea wa wc (Int.+ (i, (1 : Int.int))) m ()
           end)
    else (fn () => ()));

fun forest_csr_empty n =
  (fn () => let
              val ei = (fn () => Array.array (n, false)) ();
              val oi = (fn () => Array.array (n, false)) ();
              val pai = (fn () => Array.array (n, n)) ();
            in
              (ei, (oi, pai))
            end);

fun xset_insert_all la i m s =
  (if Int.< (i, m)
    then (fn () => let
                     val v = (fn () => Array.sub (la, i)) ();
                     val _ = xset_insert_imp v s ();
                   in
                     xset_insert_all la (Int.+ (i, (1 : Int.int))) m s ()
                   end)
    else (fn () => ()));

fun augment_csr_loop bi ra i k =
  (if Int.< (Int.+ (i, (1 : Int.int)), k)
    then (fn () =>
           let
             val u = (fn () => Array.sub (ra, i)) ();
             val v = (fn () => Array.sub (ra, Int.+ (i, (1 : Int.int)))) ();
             val _ = xmap_upd_imp heap_nat bi u v ();
             val _ = xmap_upd_imp heap_nat bi v u ();
           in
             augment_csr_loop bi ra (Int.+ (i, (2 : Int.int))) k ()
           end)
    else (fn () => ()));

fun augment_csr bi ra k = augment_csr_loop bi ra (0 : Int.int) k;

fun augment_counted_csr x =
  (fn (bi, ki) => fn ra => fn k => fn () =>
    let
      val _ = augment_csr bi ra k ();
      val c = (fn () => ! ki) ();
      val _ = (fn () => ki := (Int.+ (c, (1 : Int.int)))) ();
    in
      (bi, ki)
    end)
    x;

fun matching_card_csr B_ = (fn (_, a) => (fn () => ! a));

fun rematch_csr n bi l r =
  (fn () => let
              val lq = xmap_lookup_imp heap_nat bi r ();
              val _ = xmap_upd_imp heap_nat bi lq n ();
              val _ = xmap_upd_imp heap_nat bi r l ();
            in
              xmap_upd_imp heap_nat bi l r ()
            end);

fun rematch_counted_csr n = (fn (bi, _) => rematch_csr n bi);

fun sc_csr_pot_shift (A1_, A2_) pti l v r1 d =
  (fn () =>
    let
      val p1 = xmap_lookup_imp A1_ pti r1 ();
      val _ = xmap_upd_imp A1_ pti l v ();
    in
      xmap_upd_imp A1_ pti r1
        (minus
          ((minus_abs_if o abs_if_linordered_ring o
             linordered_ring_linordered_ring_strict o
             linordered_ring_strict_linordered_idom)
            A2_)
          p1 d)
        ()
    end);

fun better_imp (A1_, A2_) p q =
  less ((ord_preorder o preorder_order o order_linorder) A2_) (fst p)
    (fst q) orelse
    eq A1_ (fst p) (fst q) andalso (snd (snd p) andalso not (snd (snd q)));

fun best_upd_imp (A1_, A2_) b c =
  (case b of NONE => SOME c
    | SOME p => (if better_imp (A1_, A2_) c p then SOME c else b));

fun best2_upd_imp (A1_, A2_) bs c =
  let
    val (b, s) = bs;
  in
    (case b of NONE => (SOME c, b)
      | SOME p =>
        (if better_imp (A1_, A2_) c p then (SOME c, b)
          else (b, best_upd_imp (A1_, A2_) s c)))
  end;

fun sc_csr_scan_best (A1_, A2_) (B1_, B2_) cur ci u bs =
  (fn () =>
    let
      val t =
        wnb_has_imp (heap_prod heap_nat (heap_prod heap_nat heap_nat)) A1_ ci u
          ();
    in
      (if t then (fn f_ => fn () => f_ ((cur ci u) ()) ())
                   (fn c =>
                     (fn f_ => fn () => f_
                       ((wnb_move_imp
                          (heap_prod heap_nat (heap_prod heap_nat heap_nat)) A1_
                          ci u)
                       ()) ())
                       (fn _ =>
                         sc_csr_scan_best (A1_, A2_) (B1_, B2_) cur ci u
                           (best2_upd_imp (B1_, B2_) bs c)))
        else (fn () => bs))
        ()
    end);

fun sc_csr_best_two (A1_, A2_) (B1_, B2_) cur ci u =
  (fn () =>
    let
      val _ =
        wnb_reset_imp (heap_prod heap_nat (heap_prod heap_nat heap_nat)) A1_ ci
          u ();
    in
      sc_csr_scan_best (A1_, A2_) (B1_, B2_) cur ci u (NONE, NONE) ()
    end);

fun sc_csr_cur_red (A1_, A2_) n pti bdi ci l =
  (fn () =>
    let
      val r =
        wnb_current_imp (heap_prod heap_nat (heap_prod heap_nat heap_nat)) A1_
          e_tgt ci l ();
      val c =
        wnb_current_cost_imp (heap_prod heap_nat (heap_prod heap_nat heap_nat))
          A1_ ci l ();
      val p = xmap_lookup_imp A1_ pti r ();
      val b = xmap_lookup_imp heap_nat (fst bdi) r ();
    in
      (minus ((minus_abs_if o abs_if_linordered_ring o
                linordered_ring_linordered_ring_strict o
                linordered_ring_strict_linordered_idom)
               A2_)
         c p,
        (r, ((b : Int.int) = n)))
    end);

fun sc_csr_chain (A1_, A2_, A3_) n k ci pti bdi l =
  (fn () =>
    let
      val a =
        sc_csr_best_two (A2_, A3_)
          (A1_, (linorder_linordered_nonzero_semiring o
                  linordered_nonzero_semiring_linordered_semidom o
                  linordered_semidom_linordered_idom)
                  A3_)
          (sc_csr_cur_red (A2_, A3_) n pti bdi) ci l ();
    in
      (case a of (NONE, _) => (fn () => NONE)
        | (SOME (u1, (r1, true)), NONE) =>
          (fn f_ => fn () => f_ ((xmap_upd_imp A2_ pti l u1) ()) ())
            (fn _ => (fn () => (SOME (l, r1))))
        | (SOME (u1, (r1, true)), SOME (u2, _)) =>
          (fn f_ => fn () => f_
            ((sc_csr_pot_shift (A2_, A3_) pti l u2 r1
               (minus
                 ((minus_abs_if o abs_if_linordered_ring o
                    linordered_ring_linordered_ring_strict o
                    linordered_ring_strict_linordered_idom)
                   A3_)
                 u2 u1))
            ()) ())
            (fn _ => (fn () => (SOME (l, r1))))
        | (SOME (_, (_, false)), NONE) => (fn () => NONE)
        | (SOME (u1, (r1, false)), SOME (u2, _)) =>
          (if ((k : Int.int) = (0 : Int.int)) then (fn () => NONE)
            else (fn f_ => fn () => f_ ((xmap_lookup_imp heap_nat (fst bdi) r1)
                   ()) ())
                   (fn lq =>
                     (fn f_ => fn () => f_
                       ((sc_csr_pot_shift (A2_, A3_) pti l u2 r1
                          (minus
                            ((minus_abs_if o abs_if_linordered_ring o
                               linordered_ring_linordered_ring_strict o
                               linordered_ring_strict_linordered_idom)
                              A3_)
                            u2 u1))
                       ()) ())
                       (fn _ =>
                         (fn f_ => fn () => f_ ((rematch_counted_csr n bdi l r1)
                           ()) ())
                           (fn _ =>
                             sc_csr_chain (A1_, A2_, A3_) n
                               (Machine.sub_nat (k, (1 : Int.int))) ci pti bdi
                               lq)))))
        ()
    end);

fun sc_csr_row (A1_, A2_, A3_) n cap ci pti bdi l =
  (fn () =>
    let
      val bl = xmap_lookup_imp heap_nat (fst bdi) l ();
    in
      (if ((bl : Int.int) = n)
        then sc_csr_chain (A1_, A2_, A3_) n cap ci pti bdi l
        else (fn () => NONE))
        ()
    end);

fun sc_csr_loop (A1_, A2_, A3_) n cap ci pti bdi it =
  (fn () =>
    let
      val b = xset_it_has_next ord_nat it ();
    in
      (if b then (fn f_ => fn () => f_ ((xset_it_next it) ()) ())
                   (fn (l, ita) =>
                     (fn f_ => fn () => f_
                       ((sc_csr_row (A1_, A2_, A3_) n cap ci pti bdi l) ()) ())
                       (fn a =>
                         (case a
                           of NONE =>
                             sc_csr_loop (A1_, A2_, A3_) n cap ci pti bdi ita
                           | SOME (aa, ba) =>
                             (fn () => (SOME (l, (aa, ba)), ita)))))
        else (fn () => (NONE, it)))
        ()
    end);

fun sc_csr_shortcut (A1_, A2_, A3_) n cap ci pti bdi ra it =
  (fn () =>
    let
      val a = sc_csr_loop (A1_, A2_, A3_) n cap ci pti bdi it ();
    in
      (case a of (NONE, ita) => (fn () => (false, ita))
        | (SOME (_, (aa, b)), ita) =>
          (fn f_ => fn () => f_
            (((fn () => Machine.upd ((0 : Int.int), aa, ra))) ()) ())
            (fn _ =>
              (fn f_ => fn () => f_
                (((fn () => Machine.upd ((1 : Int.int), b, ra))) ()) ())
                (fn _ => (fn () => (true, ita)))))
        ()
    end);

fun pds_csr_pot_step_even (A1_, A2_) pti mi av v u =
  (fn () =>
    let
      val pv = xmap_lookup_imp A1_ pti v ();
      val mv = xmap_lookup_imp A1_ mi v ();
    in
      xmap_upd_imp A1_ pti v
        (minus
          ((minus_abs_if o abs_if_linordered_ring o
             linordered_ring_linordered_ring_strict o
             linordered_ring_strict_linordered_idom)
            A2_)
          (plus ((plus_semigroup_add o semigroup_add_numeral o
                   numeral_neg_numeral o neg_numeral_ring_1 o
                   ring_1_ring_char_0 o ring_char_0_linordered_idom)
                  A2_)
            pv av)
          mv)
        ()
    end);

fun pds_csr_pot_step_odd (A1_, A2_) pti mi av v u =
  (fn () =>
    let
      val pv = xmap_lookup_imp A1_ pti v ();
      val mv = xmap_lookup_imp A1_ mi v ();
    in
      xmap_upd_imp A1_ pti v
        (plus ((plus_semigroup_add o semigroup_add_numeral o
                 numeral_neg_numeral o neg_numeral_ring_1 o ring_1_ring_char_0 o
                 ring_char_0_linordered_idom)
                A2_)
          (minus
            ((minus_abs_if o abs_if_linordered_ring o
               linordered_ring_linordered_ring_strict o
               linordered_ring_strict_linordered_idom)
              A2_)
            pv av)
          mv)
        ()
    end);

fun forest_csr_it_init p fi =
  let
    val (ei, (oi, _)) = fi;
  in
    (case p of Evens => xset_it_init ei | Odds => xset_it_init oi)
  end;

fun pds_csr_new_pot (A1_, A2_) fi mi av pti =
  (fn () =>
    let
      val it = forest_csr_it_init Evens fi ();
      val _ =
        iter_fold (xset_it_has_next ord_nat) xset_it_next
          (pds_csr_pot_step_even (A1_, A2_) pti mi av) it () ();
      val ita = forest_csr_it_init Odds fi ();
    in
      iter_fold (xset_it_has_next ord_nat) xset_it_next
        (pds_csr_pot_step_odd (A1_, A2_) pti mi av) ita () ()
    end);

fun xset_clear_unit n xi = (fn () => let
                                       val _ = xset_clear_imp n xi ();
                                     in
                                       ()
                                     end);

fun xmap_clear_unit A_ x n xi =
  (fn () => let
              val _ = xmap_clear_imp A_ x n xi ();
            in
              ()
            end);

fun forest_csr_clear n fi =
  let
    val (ei, (oi, pai)) = fi;
  in
    (fn () => let
                val _ = xset_clear_unit n ei ();
                val _ = xset_clear_unit n oi ();
                val _ = xmap_clear_unit heap_nat n n pai ();
              in
                fi
              end)
  end;

fun pds_csr_clear (A1_, A2_) n ci qi fi bi mi =
  (fn () =>
    let
      val _ = xmap_clear_unit heap_nat n n bi ();
      val _ =
        xmap_clear_unit A1_
          (zero ((zero_abs_if o abs_if_linordered_ring o
                   linordered_ring_linordered_ring_strict o
                   linordered_ring_strict_linordered_idom)
                  A2_))
          n mi ();
      val fia = forest_csr_clear n fi ();
      val _ = heap_clear_imp qi ();
      val _ =
        wnb_reset_all_imp (heap_prod heap_nat (heap_prod heap_nat heap_nat)) A1_
          n ci ();
    in
      fia
    end);

fun forest_csr_get_path_loop n pai ra k v =
  (fn () =>
    let
      val _ = (fn () => Machine.upd (k, v, ra)) ();
      val u = xmap_lookup_imp heap_nat pai v ();
    in
      (if ((u : Int.int) = n) then (fn () => (Int.+ (k, (1 : Int.int))))
        else forest_csr_get_path_loop n pai ra (Int.+ (k, (1 : Int.int))) u)
        ()
    end);

fun forest_csr_get_path n fi ra k v = let
val (_, (_, pai)) = fi;
                                      in
forest_csr_get_path_loop n pai ra k v
                                      end;

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

fun pds_csr_relax_old (A1_, A2_) qi bi l r key =
  (fn () =>
    let
      val a =
        heap_key_of_imp
          (A1_, (linorder_linordered_nonzero_semiring o
                  linordered_nonzero_semiring_linordered_semidom o
                  linordered_semidom_linordered_idom)
                  A2_)
          qi r ();
    in
      (case a of NONE => (fn () => ())
        | SOME k =>
          (if less ((ord_abs_if o abs_if_linordered_ring o
                      linordered_ring_linordered_ring_strict o
                      linordered_ring_strict_linordered_idom)
                     A2_)
                key k
            then (fn f_ => fn () => f_ ((xmap_upd_imp heap_nat bi r l) ()) ())
                   (fn _ =>
                     heap_decrease_key_imp
                       (A1_, (linorder_linordered_nonzero_semiring o
                               linordered_nonzero_semiring_linordered_semidom o
                               linordered_semidom_linordered_idom)
                               A2_)
                       qi r key)
            else (fn () => ())))
        ()
    end);

fun pds_csr_relax_new (A1_, A2_) qi bi l r key =
  (fn () =>
    let
      val _ = xmap_upd_imp heap_nat bi r l ();
    in
      heap_insert_imp
        (A1_, (linorder_linordered_nonzero_semiring o
                linordered_nonzero_semiring_linordered_semidom o
                linordered_semidom_linordered_idom)
                A2_)
        qi r key ()
    end);

fun pds_csr_relax (A1_, A2_) n pti qi bi l pl ml r c =
  (fn () =>
    let
      val pr = xmap_lookup_imp A1_ pti r ();
      val b = xmap_lookup_imp heap_nat bi r ();
    in
      (if ((b : Int.int) = n)
        then pds_csr_relax_new (A1_, A2_) qi bi l r
               (plus ((plus_semigroup_add o semigroup_add_numeral o
                        numeral_neg_numeral o neg_numeral_ring_1 o
                        ring_1_ring_char_0 o ring_char_0_linordered_idom)
                       A2_)
                 (minus
                   ((minus_abs_if o abs_if_linordered_ring o
                      linordered_ring_linordered_ring_strict o
                      linordered_ring_strict_linordered_idom)
                     A2_)
                   (minus
                     ((minus_abs_if o abs_if_linordered_ring o
                        linordered_ring_linordered_ring_strict o
                        linordered_ring_strict_linordered_idom)
                       A2_)
                     c pl)
                   pr)
                 ml)
        else pds_csr_relax_old (A1_, A2_) qi bi l r
               (plus ((plus_semigroup_add o semigroup_add_numeral o
                        numeral_neg_numeral o neg_numeral_ring_1 o
                        ring_1_ring_char_0 o ring_char_0_linordered_idom)
                       A2_)
                 (minus
                   ((minus_abs_if o abs_if_linordered_ring o
                      linordered_ring_linordered_ring_strict o
                      linordered_ring_strict_linordered_idom)
                     A2_)
                   (minus
                     ((minus_abs_if o abs_if_linordered_ring o
                        linordered_ring_linordered_ring_strict o
                        linordered_ring_strict_linordered_idom)
                       A2_)
                     c pl)
                   pr)
                 ml))
        ()
    end);

fun pds_csr_scan (A1_, A2_) n ci pti qi bi l pl ml =
  (fn () =>
    let
      val b =
        wnb_has_imp (heap_prod heap_nat (heap_prod heap_nat heap_nat)) A1_ ci l
          ();
    in
      (if b then (fn f_ => fn () => f_
                   ((wnb_current_imp
                      (heap_prod heap_nat (heap_prod heap_nat heap_nat)) A1_
                      e_tgt ci l)
                   ()) ())
                   (fn r =>
                     (fn f_ => fn () => f_
                       ((wnb_current_cost_imp
                          (heap_prod heap_nat (heap_prod heap_nat heap_nat)) A1_
                          ci l)
                       ()) ())
                       (fn c =>
                         (fn f_ => fn () => f_
                           ((wnb_move_imp
                              (heap_prod heap_nat (heap_prod heap_nat heap_nat))
                              A1_ ci l)
                           ()) ())
                           (fn _ =>
                             (fn f_ => fn () => f_
                               ((pds_csr_relax (A1_, A2_) n pti qi bi l pl ml r
                                  c)
                               ()) ())
                               (fn _ =>
                                 pds_csr_scan (A1_, A2_) n ci pti qi bi l pl
                                   ml))))
        else (fn () => ()))
        ()
    end);

fun pds_csr_update_ben (A1_, A2_) n ci pti mi qi bi l =
  (fn () =>
    let
      val _ =
        wnb_reset_imp (heap_prod heap_nat (heap_prod heap_nat heap_nat)) A1_ ci
          l ();
      val pl = xmap_lookup_imp A1_ pti l ();
      val x = xmap_lookup_imp A1_ mi l ();
    in
      pds_csr_scan (A1_, A2_) n ci pti qi bi l pl x ()
    end);

fun forest_csr_extend x y z fi =
  let
    val (ei, (oi, pai)) = fi;
  in
    (fn () => let
                val _ = xset_insert_imp y oi ();
                val _ = xset_insert_imp z ei ();
                val _ = xmap_upd_imp heap_nat pai y x ();
                val _ = xmap_upd_imp heap_nat pai z y ();
              in
                fi
              end)
  end;

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

fun pds_csr_loop (A1_, A2_) n ci qi pti bdi ra bi mi fi =
  (fn () =>
    let
      val a =
        heap_extract_min_key_imp
          (A1_, (linorder_linordered_nonzero_semiring o
                  linordered_nonzero_semiring_linordered_semidom o
                  linordered_semidom_linordered_idom)
                  A2_)
          qi ();
    in
      (case a
        of NONE =>
          (fn () =>
            (Imp_Unbounded,
              (zero ((zero_abs_if o abs_if_linordered_ring o
                       linordered_ring_linordered_ring_strict o
                       linordered_ring_strict_linordered_idom)
                      A2_),
                fi)))
        | SOME rk =>
          (fn f_ => fn () => f_ ((xmap_lookup_imp heap_nat bi (fst rk)) ()) ())
            (fn l =>
              (fn f_ => fn () => f_ ((xmap_lookup_imp heap_nat bdi (fst rk)) ())
                ())
                (fn la =>
                  (if ((la : Int.int) = n)
                    then (fn f_ => fn () => f_
                           (((fn () => Machine.upd ((0 : Int.int), fst rk, ra)))
                           ()) ())
                           (fn _ =>
                             (fn f_ => fn () => f_
                               ((forest_csr_get_path n fi ra (1 : Int.int) l)
                               ()) ())
                               (fn k => (fn () => (Imp_Path k, (snd rk, fi)))))
                    else (fn f_ => fn () => f_
                           ((xmap_upd_imp A1_ mi (fst rk) (snd rk)) ()) ())
                           (fn _ =>
                             (fn f_ => fn () => f_
                               ((xmap_upd_imp A1_ mi la (snd rk)) ()) ())
                               (fn _ =>
                                 (fn f_ => fn () => f_
                                   ((forest_csr_extend l (fst rk) la fi) ()) ())
                                   (fn fia =>
                                     (fn f_ => fn () => f_
                                       ((pds_csr_update_ben (A1_, A2_) n ci pti
  mi qi bi la)
                                       ()) ())
                                       (fn _ =>
 pds_csr_loop (A1_, A2_) n ci qi pti bdi ra bi mi fia))))))))
        ()
    end);

fun forest_csr_add_root v fi = let
                                 val (ei, (_, _)) = fi;
                               in
                                 (fn () => let
     val _ = xset_insert_imp v ei ();
   in
     fi
   end)
                               end;

fun pds_csr_init_step (A1_, A2_) n ci pti mi qi bi bdi l st =
  let
    val (fi, found) = st;
  in
    (fn () =>
      let
        val b = xmap_lookup_imp heap_nat bdi l ();
      in
        (if ((b : Int.int) = n)
          then (fn f_ => fn () => f_ ((forest_csr_add_root l fi) ()) ())
                 (fn fia =>
                   (fn f_ => fn () => f_
                     ((pds_csr_update_ben (A1_, A2_) n ci pti mi qi bi l) ())
                     ())
                     (fn _ => (fn () => (fia, true))))
          else (fn () => (fi, found)))
          ()
      end)
  end;

fun pds_csr_init (A1_, A2_) n ci pti mi qi bi bdi li fi =
  (fn () =>
    let
      val it = xset_it_init li ();
    in
      iter_fold (xset_it_has_next ord_nat) xset_it_next
        (pds_csr_init_step (A1_, A2_) n ci pti mi qi bi bdi) it (fi, false) ()
    end);

fun pds_csr_search (A1_, A2_) n ci qi pti bdi li ra fi bi mi =
  (fn () =>
    let
      val fi1 = pds_csr_clear (A1_, A2_) n ci qi fi bi mi ();
      val a = pds_csr_init (A1_, A2_) n ci pti mi qi bi bdi li fi1 ();
    in
      let
        val (fi2, found) = a;
      in
        (if not found then (fn () => (Imp_Matched, fi2))
          else (fn f_ => fn () => f_
                 ((pds_csr_loop (A1_, A2_) n ci qi pti bdi ra bi mi fi2) ()) ())
                 (fn (res, (av, fi3)) =>
                   (case res of Imp_Unbounded => (fn () => (res, fi3))
                     | Imp_Matched => (fn () => (res, fi3))
                     | Imp_Path _ =>
                       (fn f_ => fn () => f_
                         ((pds_csr_new_pot (A1_, A2_) fi3 mi av pti) ()) ())
                         (fn _ => (fn () => (res, fi3))))))
      end
        ()
    end);

fun path_search_csr (A1_, A2_) n =
  (fn (ci, (qi, (li, (fi, (bi, mi))))) => fn bdi => fn pti => fn ra => fn () =>
    let
      val a = pds_csr_search (A1_, A2_) n ci qi pti bdi li ra fi bi mi ();
    in
      let
        val (res, fia) = a;
      in
        (fn () => (res, (pti, (ci, (qi, (li, (fia, (bi, mi))))))))
      end
        ()
    end);

fun fallback_csr (A1_, A2_) n di mt pti ra =
  (fn () =>
    let
      val a = path_search_csr (A1_, A2_) n di (fst mt) pti ra ();
    in
      let
        val (res, (ptia, dia)) = a;
        val (ci, (_, (li, (_, (_, _))))) = dia;
      in
        (fn f_ => fn () => f_
          ((wnb_reset_all_imp (heap_prod heap_nat (heap_prod heap_nat heap_nat))
             A1_ n ci)
          ()) ())
          (fn _ =>
            (fn f_ => fn () => f_ ((xset_it_init li) ()) ())
              (fn it => (fn () => (res, (mt, (ptia, (dia, it)))))))
      end
        ()
    end);

fun path_search_sc_csr (A1_, A2_) (B1_, B2_, B3_) n theta cap =
  (fn si => fn mt => fn pti => fn ra =>
    let
      val (di, it) = si;
    in
      (fn () =>
        let
          val k = matching_card_csr A1_ mt ();
        in
          (if less A2_ k theta
            then (fn f_ => fn () => f_
                   ((sc_csr_shortcut (B1_, B2_, B3_) n cap (fst di) pti mt ra
                      it)
                   ()) ())
                   (fn a =>
                     (case a
                       of (true, ita) =>
                         (fn () =>
                           (Imp_Path (2 : Int.int), (mt, (pti, (di, ita)))))
                       | (false, _) => fallback_csr (B2_, B3_) n di mt pti ra))
            else fallback_csr (B2_, B3_) n di mt pti ra)
            ()
        end)
    end);

fun hungarian_csr_main_loop (A1_, A2_, A3_) n theta cap si mi pti ra =
  (fn () =>
    let
      val a =
        path_search_sc_csr (heap_nat, ord_nat) (A1_, A2_, A3_) n theta cap si mi
          pti ra ();
    in
      (case a
        of (Imp_Unbounded, (mia, (ptia, sia))) =>
          (fn () => (Failure, (mia, (ptia, sia))))
        | (Imp_Matched, (mia, (ptia, sia))) =>
          (fn () => (Success, (mia, (ptia, sia))))
        | (Imp_Path k, (mia, (ptia, sia))) =>
          (fn f_ => fn () => f_ ((augment_counted_csr mia ra k) ()) ())
            (fn mib =>
              hungarian_csr_main_loop (A1_, A2_, A3_) n theta cap sia mib ptia
                ra))
        ()
    end);

fun hungarian_csr A_ (B1_, B2_, B3_) n theta cap cL cR si mi pti ra =
  (if not (eq A_ cL cR) then (fn () => (Failure, (mi, (pti, si))))
    else hungarian_csr_main_loop (B1_, B2_, B3_) n theta cap si mi pti ra);

fun init_pot_csr_upd_min (A1_, A2_) pti u c =
  (fn () =>
    let
      val r = xmap_lookup_imp A1_ pti u ();
    in
      (if less_eq
            ((ord_abs_if o abs_if_linordered_ring o
               linordered_ring_linordered_ring_strict o
               linordered_ring_strict_linordered_idom)
              A2_)
            r c
        then (fn () => ()) else xmap_upd_imp A1_ pti u c)
        ()
    end);

fun init_pot_csr_scan A_ (B1_, B2_) ci pti u =
  (fn () =>
    let
      val b = wnb_has_imp A_ B1_ ci u ();
    in
      (if b then (fn f_ => fn () => f_ ((wnb_current_cost_imp A_ B1_ ci u) ())
                   ())
                   (fn c =>
                     (fn f_ => fn () => f_ ((wnb_move_imp A_ B1_ ci u) ()) ())
                       (fn _ =>
                         (fn f_ => fn () => f_
                           ((init_pot_csr_upd_min (B1_, B2_) pti u c) ()) ())
                           (fn _ => init_pot_csr_scan A_ (B1_, B2_) ci pti u)))
        else (fn () => ()))
        ()
    end);

fun init_pot_csr_step A_ (B1_, B2_) ci pti u x =
  (fn () =>
    let
      val _ = wnb_reset_imp A_ B1_ ci u ();
      val b = wnb_has_imp A_ B1_ ci u ();
    in
      (if b then (fn f_ => fn () => f_ ((wnb_current_cost_imp A_ B1_ ci u) ())
                   ())
                   (fn c =>
                     (fn f_ => fn () => f_ ((wnb_move_imp A_ B1_ ci u) ()) ())
                       (fn _ =>
                         (fn f_ => fn () => f_ ((xmap_upd_imp B1_ pti u c) ())
                           ())
                           (fn _ => init_pot_csr_scan A_ (B1_, B2_) ci pti u)))
        else (fn () => ()))
        ()
    end);

fun init_pot_csr A_ (B1_, B2_) ci li pti =
  (fn () =>
    let
      val it = xset_it_init li ();
    in
      iter_fold (xset_it_has_next ord_nat) xset_it_next
        (init_pot_csr_step A_ (B1_, B2_) ci pti) it () ()
    end);

fun hungarian_csr_run (A1_, A2_, A3_) n theta cap fa ta wa la rv =
  (fn () =>
    let
      val a = csr_build_edges n (fa, ta) (0 : Int.int) ();
    in
      let
        val (ba, ea) = a;
      in
        (fn f_ => fn () => f_ (((fn () => Array.length ea)) ()) ())
          (fn m =>
            (fn f_ => fn () => f_
              (((fn () => Array.array (m,
                 zero ((zero_abs_if o abs_if_linordered_ring o
                         linordered_ring_linordered_ring_strict o
                         linordered_ring_strict_linordered_idom)
                        A3_))))
              ()) ())
              (fn wc =>
                (fn f_ => fn () => f_
                  ((perm_weights_imp A2_ ea wa wc (0 : Int.int) m) ()) ())
                  (fn _ =>
                    (fn f_ => fn () => f_ ((csr_cursor_init n ba) ()) ())
                      (fn ca =>
                        (fn f_ => fn () => f_ (((fn () => Array.length la)) ())
                          ())
                          (fn cL =>
                            (fn f_ => fn () => f_ (((fn () => Array.length rv))
                              ()) ())
                              (fn cR =>
                                (fn f_ => fn () => f_
                                  (((fn () => Array.array (n, false))) ()) ())
                                  (fn li =>
                                    (fn f_ => fn () => f_
                                      ((xset_insert_all la (0 : Int.int) cL li)
                                      ()) ())
                                      (fn _ =>
(fn f_ => fn () => f_
  (((fn () => Array.array (n,
     zero ((zero_abs_if o abs_if_linordered_ring o
             linordered_ring_linordered_ring_strict o
             linordered_ring_strict_linordered_idom)
            A3_))))
  ()) ())
  (fn pti =>
    (fn f_ => fn () => f_
      ((init_pot_csr (heap_prod heap_nat (heap_prod heap_nat heap_nat))
         (A2_, A3_) ((ba, (ea, ca)), wc) li pti)
      ()) ())
      (fn _ =>
        (fn f_ => fn () => f_
          ((wnb_reset_all_imp (heap_prod heap_nat (heap_prod heap_nat heap_nat))
             A2_ n ((ba, (ea, ca)), wc))
          ()) ())
          (fn _ =>
            (fn f_ => fn () => f_ ((xset_it_init li) ()) ())
              (fn it =>
                (fn f_ => fn () => f_
                  ((heap_empty_imp A2_ n
                     (zero ((zero_abs_if o abs_if_linordered_ring o
                              linordered_ring_linordered_ring_strict o
                              linordered_ring_strict_linordered_idom)
                             A3_)))
                  ()) ())
                  (fn qi =>
                    (fn f_ => fn () => f_ ((forest_csr_empty n) ()) ())
                      (fn fi =>
                        (fn f_ => fn () => f_ (((fn () => Array.array (n, n)))
                          ()) ())
                          (fn bi =>
                            (fn f_ => fn () => f_
                              (((fn () => Array.array (n,
                                 zero ((zero_abs_if o abs_if_linordered_ring o
 linordered_ring_linordered_ring_strict o
 linordered_ring_strict_linordered_idom)
A3_))))
                              ()) ())
                              (fn mi =>
                                (fn f_ => fn () => f_
                                  (((fn () => Array.array (n, n))) ()) ())
                                  (fn mm =>
                                    (fn f_ => fn () => f_
                                      ((refa heap_nat (0 : Int.int)) ()) ())
                                      (fn ki =>
(fn f_ => fn () => f_ (((fn () => Array.array (n, (0 : Int.int)))) ()) ())
  (fn ra =>
    (fn f_ => fn () => f_
      ((hungarian_csr equal_nat (A1_, A2_, A3_) n theta cap cL cR
         ((((ba, (ea, ca)), wc), (qi, (li, (fi, (bi, mi))))), it) (mm, ki) pti
         ra)
      ()) ())
      (fn (r, (aa, b)) =>
        let
          val (mma, _) = aa;
        in
          (fn (ptia, _) => (fn () => (r, (mma, ptia))))
        end
          b))))))))))))))))))))
      end
        ()
    end);

fun hungarian_csr_complete A_ dflt cf n fa ta wa la rv =
  (fn () =>
    let
      val l = (fn () => Array.length la) ();
      val r = (fn () => Array.length rv) ();
      val m = (fn () => Array.length fa) ();
    in
      let
        val k = max ord_nat l r;
        val na =
          Int.+ (Int.+ (n, Machine.sub_nat (k, l)), Machine.sub_nat (k, r));
      in
        (fn f_ => fn () => f_ (((fn () => Array.array (k, (0 : Int.int)))) ())
          ())
          (fn laa =>
            (fn f_ => fn () => f_
              ((fold_imp (0 : Int.int) k (pad_step la l n laa) ()) ()) ())
              (fn _ =>
                (fn f_ => fn () => f_
                  (((fn () => Array.array (k, (0 : Int.int)))) ()) ())
                  (fn rva =>
                    (fn f_ => fn () => f_
                      ((fold_imp (0 : Int.int) k (pad_step rv r n rva) ()) ())
                      ())
                      (fn _ =>
                        (fn f_ => fn () => f_
                          (((fn () => Array.array (na, (0 : Int.int)))) ()) ())
                          (fn pa =>
                            (fn f_ => fn () => f_
                              ((fold_imp (0 : Int.int) k (pos_step laa pa) ())
                              ()) ())
                              (fn _ =>
                                (fn f_ => fn () => f_
                                  ((fold_imp (0 : Int.int) k (pos_step rva pa)
                                     ())
                                  ()) ())
                                  (fn _ =>
                                    (fn f_ => fn () => f_
                                      (((fn () => Array.array (Int.* (k, k),
 (0 : Int.int))))
                                      ()) ())
                                      (fn faa =>
(fn f_ => fn () => f_ (((fn () => Array.array (Int.* (k, k), (0 : Int.int))))
  ()) ())
  (fn taa =>
    (fn f_ => fn () => f_
      ((fold_imp (0 : Int.int) (Int.* (k, k)) (grid_step k laa rva faa taa) ())
      ()) ())
      (fn _ =>
        (fn f_ => fn () => f_ (((fn () => Array.array (Int.* (k, k), dflt))) ())
          ())
          (fn waa =>
            (fn f_ => fn () => f_
              ((fold_imp (0 : Int.int) m (wgt_step A_ cf k fa ta wa pa waa) ())
              ()) ())
              (fn _ =>
                (fn () =>
                  (faa, (taa, (waa, (laa, (rva, (pa, (na, k))))))))))))))))))))
      end
        ()
    end);

fun hungarian_csr_reduced_run (A1_, A2_, A3_) dflt cf kp n theta cap fa ta wa la
  rv =
  (fn () =>
    let
      val mo = (fn () => Array.array (n, n)) ();
      val a = hungarian_csr_complete A2_ dflt cf n fa ta wa la rv ();
    in
      let
        val (faa, (taa, (waa, (laa, (rva, (pa, (na, k))))))) = a;
      in
        (fn f_ => fn () => f_
          ((hungarian_csr_run (A1_, A2_, A3_) na theta cap faa taa waa laa rva)
          ()) ())
          (fn (_, (mi, _)) =>
            (fn f_ => fn () => f_ ((extract_imp A2_ kp na k la pa waa mi mo) ())
              ())
              (fn _ => (fn () => mo)))
      end
        ()
    end);

fun hungarian_csr_mw_run (A1_, A2_, A3_) neg =
  hungarian_csr_reduced_run (A1_, A2_, A3_)
    (zero ((zero_abs_if o abs_if_linordered_ring o
             linordered_ring_linordered_ring_strict o
             linordered_ring_strict_linordered_idom)
            A3_))
    (fn w =>
      min ((ord_abs_if o abs_if_linordered_ring o
             linordered_ring_linordered_ring_strict o
             linordered_ring_strict_linordered_idom)
            A3_)
        (zero ((zero_abs_if o abs_if_linordered_ring o
                 linordered_ring_linordered_ring_strict o
                 linordered_ring_strict_linordered_idom)
                A3_))
        (sgn_w
          ((uminus_abs_if o abs_if_linordered_ring o
             linordered_ring_linordered_ring_strict o
             linordered_ring_strict_linordered_idom)
            A3_)
          neg w))
    (fn w =>
      less ((ord_abs_if o abs_if_linordered_ring o
              linordered_ring_linordered_ring_strict o
              linordered_ring_strict_linordered_idom)
             A3_)
        w (zero ((zero_abs_if o abs_if_linordered_ring o
                   linordered_ring_linordered_ring_strict o
                   linordered_ring_strict_linordered_idom)
                  A3_)));

fun hungarian_csr_mwmc_run (A1_, A2_, A3_) neg n theta cap fa ta wa la rv =
  (fn () =>
    let
      val m = (fn () => Array.length wa) ();
      val l = (fn () => Array.length la) ();
      val r = (fn () => Array.length rv) ();
      val mx =
        fold_imp (0 : Int.int) m (max_abs_step (A2_, A3_) wa)
          (zero ((zero_abs_if o abs_if_linordered_ring o
                   linordered_ring_linordered_ring_strict o
                   linordered_ring_strict_linordered_idom)
                  A3_))
          ();
    in
      hungarian_csr_reduced_run (A1_, A2_, A3_)
        (plus ((plus_semigroup_add o semigroup_add_numeral o
                 numeral_neg_numeral o neg_numeral_ring_1 o ring_1_ring_char_0 o
                 ring_char_0_linordered_idom)
                A3_)
          (numeral
            ((numeral_neg_numeral o neg_numeral_ring_1 o ring_1_ring_char_0 o
               ring_char_0_linordered_idom)
              A3_)
            (Bit0 One))
          (times
            ((times_dvd o dvd_comm_monoid_mult o
               comm_monoid_mult_comm_semiring_1 o
               comm_semiring_1_comm_semiring_1_cancel o
               comm_semiring_1_cancel_semidom o semidom_idom o
               idom_idom_abs_sgn o idom_abs_sgn_linordered_idom)
              A3_)
            (of_nat
              ((semiring_1_semiring_char_0 o semiring_char_0_ring_char_0 o
                 ring_char_0_linordered_idom)
                A3_)
              (Int.+ (l, r)))
            mx))
        (sgn_w
          ((uminus_abs_if o abs_if_linordered_ring o
             linordered_ring_linordered_ring_strict o
             linordered_ring_strict_linordered_idom)
            A3_)
          neg)
        (fn w =>
          less ((ord_abs_if o abs_if_linordered_ring o
                  linordered_ring_linordered_ring_strict o
                  linordered_ring_strict_linordered_idom)
                 A3_)
            w (plus ((plus_semigroup_add o semigroup_add_numeral o
                       numeral_neg_numeral o neg_numeral_ring_1 o
                       ring_1_ring_char_0 o ring_char_0_linordered_idom)
                      A3_)
                (numeral
                  ((numeral_neg_numeral o neg_numeral_ring_1 o
                     ring_1_ring_char_0 o ring_char_0_linordered_idom)
                    A3_)
                  (Bit0 One))
                (times
                  ((times_dvd o dvd_comm_monoid_mult o
                     comm_monoid_mult_comm_semiring_1 o
                     comm_semiring_1_comm_semiring_1_cancel o
                     comm_semiring_1_cancel_semidom o semidom_idom o
                     idom_idom_abs_sgn o idom_abs_sgn_linordered_idom)
                    A3_)
                  (of_nat
                    ((semiring_1_semiring_char_0 o semiring_char_0_ring_char_0 o
                       ring_char_0_linordered_idom)
                      A3_)
                    (Int.+ (l, r)))
                  mx)))
        n theta cap fa ta wa la rv ()
    end);

fun hungarian_csr_mw_run_int x =
  hungarian_csr_mw_run (equal_int, heap_int, linordered_idom_int) x;

fun hungarian_csr_mwmc_run_int x =
  hungarian_csr_mwmc_run (equal_int, heap_int, linordered_idom_int) x;

fun hungarian_csr_max_perfect_run (A1_, A2_, A3_) n theta cap fa ta wa la rv =
  (fn () =>
    let
      val m = (fn () => Array.length wa) ();
      val wn =
        (fn () => Array.array (m,
          zero ((zero_abs_if o abs_if_linordered_ring o
                  linordered_ring_linordered_ring_strict o
                  linordered_ring_strict_linordered_idom)
                 A3_)))
          ();
      val _ =
        fold_imp (0 : Int.int) m
          (neg_step
            ((uminus_abs_if o abs_if_linordered_ring o
               linordered_ring_linordered_ring_strict o
               linordered_ring_strict_linordered_idom)
               A3_,
              A2_)
            wa wn)
          () ();
    in
      hungarian_csr_run (A1_, A2_, A3_) n theta cap fa ta wn la rv ()
    end);

fun hungarian_csr_max_perfect_run_int x =
  hungarian_csr_max_perfect_run (equal_int, heap_int, linordered_idom_int) x;

fun hungarian_csr_run_int x =
  hungarian_csr_run (equal_int, heap_int, linordered_idom_int) x;

end; (*struct Hungarian*)
