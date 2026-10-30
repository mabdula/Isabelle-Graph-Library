section \<open>Serialising \<open>nat\<close> to a 64-bit machine integer\<close>

theory Code_Target_Nat_Machine
  imports "HOL-Library.Code_Target_Nat" "HOL-Imperative_HOL.Array" AI_Provenance.Provenance
begin

provenance ai


text \<open>
  By default \<open>nat\<close> becomes SML's \<open>IntInf.int\<close>, so every array index is
  unbounded: each access converts and each loop step allocates a box. This theory
  serialises \<open>nat\<close> to MLton's \<open>Int.int\<close> instead, which is 64 bits under
  \<open>-default-type int64\<close>. \<open>int\<close>, and with it every flow, cost, capacity,
  balance and potential, stays on \<open>IntInf.int\<close>.

  \<open>Int.int\<close> rather than \<open>Word64.word\<close>: it is the index type of
  \<^verbatim>\<open>Array.sub\<close>, \<^verbatim>\<open>Array.update\<close> and
  \<^verbatim>\<open>Array.array\<close>, so an access needs no conversion, and its arithmetic
  raises \<open>Overflow\<close> instead of wrapping silently.

  The type must be printed as the qualified \<open>Int.int\<close>. HOL's \<open>int\<close> becomes a
  local \<^verbatim>\<open>datatype int\<close> in the generated module, which shadows the bare name
  \<open>int\<close> for everything printed after it. The modules \<open>Nat_Machine\<close> and
  \<open>Array_Machine\<close> are emitted before that declaration, so their signatures may say
  \<open>int\<close>.

  This is a trusted serialisation, not a theorem: it is correct only while no computed
  \<open>nat\<close> exceeds \<open>2^63 - 1\<close>. The argument:
    \<^item> \<open>nat\<close> occurs only as array indices, the sizes \<open>m\<close> and \<open>n\<close>,
      and counts derived from them; all quantities live in the locale's ring type
      \<open>'n\<close>, with no coercion to \<open>nat\<close>;
    \<^item> nats are never multiplied, so they stay in \<open>O(m + n)\<close>;
    \<^item> DIMACS bounds \<open>n, m \<le> 2^31 - 1\<close>, and the largest count computed is
      \<open>ns_arcs = red_m + n \<le> m + 2n + 1 \<le> 3 * (2^31 - 1) + 1\<close>.

  The first two are properties of the generated code. The driver's build re-checks them on
  the printed SML (\<open>check_index_discipline.py\<close>); if that check fails, this theory
  must go.
\<close>

subsection \<open>Helper operations\<close>

text \<open>HOL's \<open>div\<close> and \<open>mod\<close> are total, SML's raise at a zero divisor, hence a module.
      Subtraction is unguarded \<open>Int.-\<close>: no generated call subtracts a larger from a smaller nat.\<close>

code_printing code_module Nat_Machine \<rightharpoonup> (SML)
\<open>structure Nat_Machine : sig
  val divide : int * int -> int
  val modulo : int * int -> int
end = struct
  (* HOL makes division by zero total, with m div 0 = 0 and m mod 0 = m *)
  fun divide (m, n) = if n = 0 then 0 else Int.div (m, n)
  fun modulo (m, n) = if n = 0 then m else Int.mod (m, n)
end
\<close>

text \<open>\<^const>\<open>Array.upd\<close> returns the array and takes its arguments in another order than
      \<^verbatim>\<open>Array.update\<close>; a serialisation cannot reorder placeholders, so a module
      adjusts it.\<close>

code_printing code_module Array_Machine \<rightharpoonup> (SML)
\<open>structure Array_Machine : sig
  val upd : 'a array * int * 'a -> 'a array
end = struct
  fun upd (a, i, x) = (Array.update (a, i, x); a)
end
\<close>

subsection \<open>The serialisation\<close>

text \<open>\<open>Int.fromLarge\<close> and \<open>Int.toLarge\<close> convert from and to
      \<open>IntInf\<close> (MLton's \<open>LargeInt\<close>); \<open>fromLarge\<close> raises
      \<open>Overflow\<close> on a value beyond 64 bits.\<close>

code_printing
  type_constructor nat \<rightharpoonup> (SML) "Int.int"
| constant "0 :: nat" \<rightharpoonup> (SML) "(0 : Int.int)"
| constant "1 :: nat" \<rightharpoonup> (SML) "(1 : Int.int)"
| constant Suc \<rightharpoonup> (SML) "Int.+/ ((_),/ (1 : Int.int))"
| constant "(+) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Int.+/ ((_),/ (_))"
| constant "(-) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Int.-/ ((_),/ (_))"
| constant "(*) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Int.*/ ((_),/ (_))"
| constant "(div) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Nat'_Machine.divide/ ((_),/ (_))"
| constant "(mod) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Nat'_Machine.modulo/ ((_),/ (_))"
| constant "HOL.equal :: nat \<Rightarrow> nat \<Rightarrow> bool" \<rightharpoonup> (SML) "!((_ : Int.int) = _)"
| constant "(\<le>) :: nat \<Rightarrow> nat \<Rightarrow> bool" \<rightharpoonup> (SML) "Int.<=/ ((_),/ (_))"
| constant "(<) :: nat \<Rightarrow> nat \<Rightarrow> bool" \<rightharpoonup> (SML) "Int.</ ((_),/ (_))"
| constant nat_of_integer \<rightharpoonup> (SML) "Int.fromLarge"
| constant integer_of_nat \<rightharpoonup> (SML) "Int.toLarge"

code_reserved (SML) Nat_Machine Array_Machine

subsection \<open>Array access without a conversion\<close>

text \<open>\<^const>\<open>Array.nth\<close> and its siblings are generated through
      \<^const>\<open>Array.nth'\<close> and the like, which take an \<open>integer\<close> and would
      round-trip every index through \<open>IntInf\<close>. These wrappers take the \<open>nat\<close>, now
      the SML array index type, and are definitionally the original operations.\<close>

definition nth_machine :: "'a::heap array \<Rightarrow> nat \<Rightarrow> 'a Heap" where
  [simp]: "nth_machine = Array.nth"

definition upd_machine :: "'a::heap array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array Heap" where
  [simp]: "upd_machine a i x = Array.upd i x a"

definition new_machine :: "nat \<Rightarrow> 'a::heap \<Rightarrow> 'a array Heap" where
  [simp]: "new_machine = Array.new"

definition len_machine :: "'a::heap array \<Rightarrow> nat Heap" where
  [simp]: "len_machine = Array.len"

definition make_machine :: "nat \<Rightarrow> (nat \<Rightarrow> 'a::heap) \<Rightarrow> 'a array Heap" where
  [simp]: "make_machine = Array.make"

lemma machine_code [code]:
  "Array.nth a i = nth_machine a i"
  "Array.upd i x a = upd_machine a i x"
  "Array.new n x = new_machine n x"
  "Array.len a = len_machine a"
  "Array.make n f = make_machine n f"
  by simp_all

code_printing
  constant nth_machine \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ (_)))"
| constant upd_machine \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array'_Machine.upd/ ((_),/ (_),/ (_)))"
| constant new_machine \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.array/ ((_),/ (_)))"
| constant len_machine \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.length/ _)"
| constant make_machine \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.tabulate/ ((_),/ (_)))"

end
