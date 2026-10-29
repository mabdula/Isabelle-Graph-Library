theory Code_Target_Machine_Int
  imports
    "HOL-Library.Code_Target_Nat"
    "HOL-Library.Code_Target_Int"
    "Imperative_HOL_Go"
begin

section \<open>Serialising @{typ nat} and @{typ int} to Machine Integers\<close>

text \<open>Both @{typ nat} and @{typ int} become signed 64-bit integers of the target language:
  \<open>Int.int\<close> in SML (64 bits when compiled by MLton with \<open>-default-type int64\<close>; under Poly/ML,
  which only type checks the code here, \<open>Int.int\<close> is unbounded), \<open>Long\<close> in Scala and \<open>int64\<close>
  in Go. In Scala, @{typ int} is the opaque type \<open>Machine.Int64\<close>, a \<open>Long\<close> at run time: if both
  types were \<open>Long\<close>, the class instances for @{typ nat} and @{typ int} would be ambiguous
  implicits. Array indices and sizes are machine integers as well, so the array operations are
  printed directly instead of through @{typ integer}.

  The generated code contains no arbitrary precision arithmetic. In particular, the conversions
  from and to @{typ integer} are not printed, so a program that needs them does not compile.

  This is a trusted serialisation, not a theorem: it is faithful as long as no number the
  program computes leaves the 64-bit range. Natural number subtraction truncates at \<open>0\<close> and
  division and modulus by \<open>0\<close> behave as in HOL. Division and modulus on @{typ int} are not
  printed, since the rounding of the targets differs from HOL's.\<close>

subsection \<open>Helper Modules\<close>

code_printing code_module Machine \<rightharpoonup> (SML)
\<open>structure Machine : sig
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
\<close>
| code_module Machine \<rightharpoonup> (Scala)
\<open>object Machine {
  opaque type Int64 = Long
  def int(x: Long): Int64 = x
  def plusInt(a: Int64, b: Int64): Int64 = a + b
  def minusInt(a: Int64, b: Int64): Int64 = a - b
  def timesInt(a: Int64, b: Int64): Int64 = a * b
  def uminusInt(a: Int64): Int64 = - a
  def eqInt(a: Int64, b: Int64): Boolean = a == b
  def leInt(a: Int64, b: Int64): Boolean = a <= b
  def ltInt(a: Int64, b: Int64): Boolean = a < b
  def subNat(m: Long, n: Long): Long = if (m < n) 0L else m - n
  def divNat(m: Long, n: Long): Long = if (n == 0L) 0L else m / n
  def modNat(m: Long, n: Long): Long = if (n == 0L) m else m % n
  def alloc[A](n: Long)(x: A): Array.T[A] = Array.alloc(n.toInt)(x)
  def make[A](n: Long)(f: Long => A): Array.T[A] = Array.init(n.toInt)((i: Int) => f(i.toLong))
  def len[A](a: Array.T[A]): Long = a.length.toLong
  def nth[A](a: Array.T[A], i: Long): A = a(i.toInt)
  def upd[A](i: Long, x: A, a: Array.T[A]): Array.T[A] = { a.update(i.toInt, x); a }
}
\<close>
| code_module Machine \<rightharpoonup> (Go)
\<open>package Machine

func SubNat(m, n int64) int64 {
  if m < n { return 0 }
  return m - n
}

func DivNat(m, n int64) int64 {
  if n == 0 { return 0 }
  return m / n
}

func ModNat(m, n int64) int64 {
  if n == 0 { return m }
  return m % n
}

func New[A any](n int64, x A) func() []A {
  return func() []A {
    a := make([]A, n)
    for i := range a { a[i] = x }
    return a
  }
}

func Make[A any](n int64, f func(int64) A) func() []A {
  return func() []A {
    a := make([]A, n)
    for i := range a { a[i] = f(int64(i)) }
    return a
  }
}

func Len[A any](a []A) func() int64 {
  return func() int64 { return int64(len(a)) }
}

func Nth[A any](a []A, i int64) func() A {
  return func() A { return a[i] }
}

func Upd[A any](i int64, x A, a []A) func() []A {
  return func() []A { a[i] = x; return a }
}
\<close>

code_reserved (SML) Machine
code_reserved (Scala) Machine
code_reserved (Go) Machine

text \<open>The Go setup of the AFP adds its \<open>big.Int\<close> module, for @{typ integer}, to programs that do
  not compute on @{typ integer}, and Go rejects the then unused import. The module is removed.\<close>

code_printing code_module Bigint \<rightharpoonup> (Go)

text \<open>The Scala module of Imperative HOL also offers the array operations on @{typ integer}
  indices, as \<open>BigInt\<close>. Here it is replaced by the part that the operations above need.

  Arrays of machine integers and of booleans store their elements unboxed. Generic Scala code
  cannot allocate a \<open>scala.Array[Long]\<close> without a \<open>ClassTag\<close>, which the generated code does not
  pass around, so the representation is chosen at allocation, from the run time class of the
  initial value: a \<open>java.lang.Long\<close> (also the representation of \<open>Machine.Int64\<close>) gives a
  \<open>scala.Array[Long]\<close>, a \<open>java.lang.Boolean\<close> a \<open>scala.Array[Boolean]\<close>, and everything else a
  \<open>scala.Array[AnyRef]\<close>. In generic code, the element is boxed again when it is read.

  The array type is covariant: Scala infers the type of an array allocated with an initial value
  from that value alone, e.g. \<open>Nil.type\<close> for the empty list. Since the generated code is type
  correct in HOL, this does not let a wrong value into an array, nor a value of the wrong class
  into an unboxed array.\<close>

code_printing code_module "Heap" \<rightharpoonup> (Scala)
\<open>object Heap {
  def bind[A, B](f: Unit => A, g: A => Unit => B): Unit => B = (_: Unit) => g(f(()))(())
}

class Ref[A](x: A) {
  var value = x
}

object Ref {
  def apply[A](x: A): Ref[A] =
    new Ref[A](x)
  def lookup[A](r: Ref[A]): A =
    r.value
  def update[A](r: Ref[A], x: A): Unit =
    { r.value = x }
}

object Array {
  import scala.annotation.unchecked.uncheckedVariance

  abstract class T[+A] {
    def apply(i: Int): A
    def update(i: Int, x: A @uncheckedVariance): Unit
    def length: Int
    def toList: List[A] = List.tabulate(length)(apply)
    override def toString: String = toList.mkString("Array.T(", ",", ")")
  }

  final class LongT[+A](val array: scala.Array[Long]) extends T[A] {
    def apply(i: Int): A = array(i).asInstanceOf[A]
    def update(i: Int, x: A @uncheckedVariance): Unit = array(i) = x.asInstanceOf[Long]
    def length: Int = array.length
  }

  final class BooleanT[+A](val array: scala.Array[Boolean]) extends T[A] {
    def apply(i: Int): A = array(i).asInstanceOf[A]
    def update(i: Int, x: A @uncheckedVariance): Unit = array(i) = x.asInstanceOf[Boolean]
    def length: Int = array.length
  }

  final class RefT[+A](val array: scala.Array[AnyRef]) extends T[A] {
    def apply(i: Int): A = array(i).asInstanceOf[A]
    def update(i: Int, x: A @uncheckedVariance): Unit = array(i) = x.asInstanceOf[AnyRef]
    def length: Int = array.length
  }

  def alloc[A](n: Int)(x: A): T[A] = x match {
    case l: java.lang.Long =>
      val a = new scala.Array[Long](n); java.util.Arrays.fill(a, l.longValue); new LongT[A](a)
    case b: java.lang.Boolean =>
      val a = new scala.Array[Boolean](n); java.util.Arrays.fill(a, b.booleanValue); new BooleanT[A](a)
    case _ =>
      val a = new scala.Array[AnyRef](n); java.util.Arrays.fill(a, x.asInstanceOf[AnyRef]); new RefT[A](a)
  }

  def init[A](n: Int)(f: Int => A): T[A] =
    if (n == 0) new RefT[A](new scala.Array[AnyRef](0))
    else {
      val a = alloc(n)(f(0))
      for (i <- 1 until n) a(i) = f(i)
      a
    }

  def freeze[A](a: T[A]): List[A] = a.toList
}
\<close>

subsection \<open>Natural Numbers\<close>

code_printing
  type_constructor nat \<rightharpoonup> (SML) "Int.int" and (Scala) "Long" and (Go) "int64"
| constant "0 :: nat" \<rightharpoonup> (SML) "(0 : Int.int)" and (Scala) "0L" and (Go) "int64(0)"
| constant "1 :: nat" \<rightharpoonup> (SML) "(1 : Int.int)" and (Scala) "1L" and (Go) "int64(1)"
| constant Suc \<rightharpoonup> (SML) "Int.+/ ((_),/ (1 : Int.int))" and (Scala) "!(_ +/ 1L)"
    and (Go) "!((_) + 1)"
| constant "(+) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Int.+/ ((_),/ (_))" and (Scala) infixl 7 "+"
    and (Go) "!((_) + (_))"
| constant "(-) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Machine.sub'_nat/ ((_),/ (_))"
    and (Scala) "Machine.subNat((_), (_))" and (Go) "Machine.SubNat( _, _ )"
| constant "(*) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Int.*/ ((_),/ (_))" and (Scala) infixl 8 "*"
    and (Go) "!((_) * (_))"
| constant "(div) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Machine.div'_nat/ ((_),/ (_))"
    and (Scala) "Machine.divNat((_), (_))" and (Go) "Machine.DivNat( _, _ )"
| constant "(mod) :: nat \<Rightarrow> nat \<Rightarrow> nat" \<rightharpoonup> (SML) "Machine.mod'_nat/ ((_),/ (_))"
    and (Scala) "Machine.modNat((_), (_))" and (Go) "Machine.ModNat( _, _ )"
| constant "HOL.equal :: nat \<Rightarrow> nat \<Rightarrow> bool" \<rightharpoonup> (SML) "!((_ : Int.int) = _)"
    and (Scala) infixl 5 "==" and (Go) "!((_) == (_))"
| constant "(\<le>) :: nat \<Rightarrow> nat \<Rightarrow> bool" \<rightharpoonup> (SML) "Int.<=/ ((_),/ (_))" and (Scala) infixl 4 "<="
    and (Go) "!((_) <= (_))"
| constant "(<) :: nat \<Rightarrow> nat \<Rightarrow> bool" \<rightharpoonup> (SML) "Int.</ ((_),/ (_))" and (Scala) infixl 4 "<"
    and (Go) "!((_) < (_))"

text \<open>Generic code, e.g. @{const of_nat} into a ring that is only fixed by a class instance,
  divides natural numbers through @{const Euclidean_Rings.divmod_nat}, which
  @{theory "HOL-Library.Code_Target_Nat"} implements on @{typ integer}. Here it is implemented
  by the machine operations above.\<close>

lemma divmod_nat_machine [code]: "Euclidean_Rings.divmod_nat m n = (m div n, m mod n)"
  by (simp add: Euclidean_Rings.divmod_nat_def)

subsection \<open>Integers\<close>

code_printing
  type_constructor int \<rightharpoonup> (SML) "Int.int" and (Scala) "Machine.Int64" and (Go) "int64"
| constant "0 :: int" \<rightharpoonup> (SML) "(0 : Int.int)" and (Scala) "Machine.int(0L)" and (Go) "int64(0)"
| constant "1 :: int" \<rightharpoonup> (SML) "(1 : Int.int)" and (Scala) "Machine.int(1L)" and (Go) "int64(1)"
| constant "(+) :: int \<Rightarrow> int \<Rightarrow> int" \<rightharpoonup> (SML) "Int.+/ ((_),/ (_))"
    and (Scala) "Machine.plusInt((_), (_))" and (Go) "!((_) + (_))"
| constant "(-) :: int \<Rightarrow> int \<Rightarrow> int" \<rightharpoonup> (SML) "Int.-/ ((_),/ (_))"
    and (Scala) "Machine.minusInt((_), (_))" and (Go) "!((_) - (_))"
| constant "uminus :: int \<Rightarrow> int" \<rightharpoonup> (SML) "Int.~" and (Scala) "Machine.uminusInt((_))"
    and (Go) "!(- (_))"
| constant "(*) :: int \<Rightarrow> int \<Rightarrow> int" \<rightharpoonup> (SML) "Int.*/ ((_),/ (_))"
    and (Scala) "Machine.timesInt((_), (_))" and (Go) "!((_) * (_))"
| constant "HOL.equal :: int \<Rightarrow> int \<Rightarrow> bool" \<rightharpoonup> (SML) "!((_ : Int.int) = _)"
    and (Scala) "Machine.eqInt((_), (_))" and (Go) "!((_) == (_))"
| constant "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool" \<rightharpoonup> (SML) "Int.<=/ ((_),/ (_))"
    and (Scala) "Machine.leInt((_), (_))" and (Go) "!((_) <= (_))"
| constant "(<) :: int \<Rightarrow> int \<Rightarrow> bool" \<rightharpoonup> (SML) "Int.</ ((_),/ (_))"
    and (Scala) "Machine.ltInt((_), (_))" and (Go) "!((_) < (_))"

subsection \<open>Literals\<close>

text \<open>Numerals of both types are printed as literals. Without the two constants below, a numeral
  would be generated as the conversion of an @{typ integer} literal. Literals of type
  @{typ integer} are folded into @{const Code_Numeral.Pos} and @{const Code_Numeral.Neg} during
  preprocessing, hence the second form of the rules.\<close>

definition nat_lit :: "num \<Rightarrow> nat" where "nat_lit = numeral"

definition int_lit :: "num \<Rightarrow> int" where "int_lit = numeral"

lemma nat_lit_code_unfold [code_unfold]:
  "nat_of_integer (numeral k) = nat_lit k"
  "nat_of_integer (Code_Numeral.Pos k) = nat_lit k"
  by (simp_all add: nat_lit_def)

lemma int_lit_code_unfold [code_unfold]:
  "int_of_integer (numeral k) = int_lit k"
  "int_of_integer (- numeral k) = - int_lit k"
  "int_of_integer (Code_Numeral.Pos k) = int_lit k"
  "int_of_integer (Code_Numeral.Neg k) = - int_lit k"
  by (simp_all add: int_lit_def)

setup \<open>
  let
    fun add c printers = fold (fn (target, print) => Numeral.add_code c I (K print) target) printers
    fun sml k = "(" ^ string_of_int k ^ " : Int.int)"
    fun go k = "int64(" ^ string_of_int k ^ ")"
  in
    add \<^const_name>\<open>nat_lit\<close>
      [("SML", sml), ("Scala", fn k => "(" ^ string_of_int k ^ "L)"), ("Go", go)]
    #> add \<^const_name>\<open>int_lit\<close>
      [("SML", sml), ("Scala", fn k => "Machine.int(" ^ string_of_int k ^ "L)"), ("Go", go)]
  end
\<close>

subsection \<open>Arrays\<close>

code_printing
  constant Array.new \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.array/ ((_),/ (_)))"
    and (Scala) "('_: Unit)/ =>/ Machine.alloc((_))((_))" and (Go) "Machine.New( _, _ )"
| constant Array.make \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.tabulate/ ((_),/ (_)))"
    and (Scala) "('_: Unit)/ =>/ Machine.make((_))((_))" and (Go) "Machine.Make( _, _ )"
| constant Array.len \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.length/ _)"
    and (Scala) "('_: Unit)/ =>/ Machine.len((_))" and (Go) "Machine.Len( _ )"
| constant Array.nth \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ (_)))"
    and (Scala) "('_: Unit)/ =>/ Machine.nth((_), (_))" and (Go) "Machine.Nth( _, _ )"
| constant Array.upd \<rightharpoonup> (SML) "(fn/ ()/ =>/ Machine.upd/ ((_),/ (_),/ (_)))"
    and (Scala) "('_: Unit)/ =>/ Machine.upd((_), (_), (_))" and (Go) "Machine.Upd( _, _, _ )"

subsection \<open>Writing the Code to Files\<close>

text \<open>The code of the given constants for one target, written to \<open><name>_code_exports/<dir_name>\<close> next to
  the theory of the given context. A target that produces a single file (SML, Scala) writes it
  under the given file name, a target that produces several files (Go) under their own names.\<close>

ML \<open>
  fun write_machine_code ctxt consts module_name target dir_name file_name =
    let
      val (files, _) = Code_Target.produce_code ctxt false consts target module_name NONE [];
      val thy = Proof_Context.theory_of ctxt;
      val export_name = unsuffix "_Code_Export" (Context.theory_base_name thy);
      val dir = Path.append (Resources.master_directory thy)
        (Path.make [export_name ^ "_code_exports", dir_name]);
      fun write (names, code) =
        let
          val path = Path.append dir (Path.make (if null names then [file_name] else names));
          val _ = Isabelle_System.make_directory (Path.dir path);
        in File.write path (Bytes.content code); writeln ("wrote " ^ Path.implode path) end;
    in List.app write files end
\<close>

end
