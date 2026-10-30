(* The certifying DIMACS assignment solver.

     asn_solver [--no-oracle] <instance.asn> <solution>

   Parsing and printing are C (asn_io.c), the oracle is CSA with the
   certificate generators (oracle/), everything in between is the
   verified program Assignment_Solver.asn_solve_int exported from
   Hungarian_Method/Refinements/Assignment_Solver.thy: it checks that
   every node is on an arc, asks the oracle, checks the oracle's
   certificate and, if that fails, runs the verified Hungarian method.

   Compiled with -default-type int64, so Int.int is Int64.int: the
   machine integers of the exported code. MLton's Int64 arithmetic is
   overflow-checked, so an overflow aborts instead of giving a wrong
   answer. *)

structure Main =
struct

structure A = Assignment_Solver

val c_parse = _import "asn_parse" public : string -> Int64.int;
val c_sizes = _import "asn_sizes" public : Int64.int array -> unit;
val c_fill = _import "asn_fill" public :
  Int64.int array * Int64.int array * Int64.int array * Int64.int array * Int64.int array -> unit;
val c_oracle = _import "asn_oracle" public :
  Int64.int * Int64.int * Int64.int array * Int64.int array * Int64.int array *
  Int64.int * Int64.int array * Int64.int * Int64.int array *
  Int64.int array * Int64.int array * Int64.int array * Int64.int array -> Int64.int;
val c_print = _import "asn_print" public :
  string * string * Int64.int * string * Int64.int *
  Int64.int array * Int64.int array * Int64.int array -> Int64.int;

val c_stamp = _import "asn_stamp" public : Int64.int -> unit;
val c_report = _import "asn_report" public : unit -> unit;

(* The phase clock (asn_clock.c). Asn_Bench.enabled is a constant, so in
   the shipped build MLton removes the calls. *)
fun stamp k = if Asn_Bench.enabled then c_stamp k else ()

fun cstr s = s ^ "\000"

fun die msg = (TextIO.output (TextIO.stdErr, "asn: " ^ msg ^ "\n"); OS.Process.exit OS.Process.failure)

(* What the oracle answered; only for the comment line of the solution. *)
val oracle_said = ref "not asked"

(* The oracle in the shape the verified program expects: a heap action
   that leaves the input arrays alone and returns fresh arrays. *)
fun oracle n fa ta wa la rv () =
  let
    val () = stamp 1
    val m = Array.length fa
    val nl = Array.length la
    val nr = Array.length rv
    val ms = Array.array (nl, 0)
    val ys = Array.array (n, 0)
    val s = Array.array (nl, 0)
    val len = Array.array (1, 0)
    val st = c_oracle (n, m, fa, ta, wa, nl, la, nr, rv, ms, ys, s, len)
    val a =
      case st of
        1 => (oracle_said := "optimal"; A.Asn_opt (ms, ys))
      | 2 => (oracle_said := "infeasible";
              A.Asn_infeas (Array.tabulate (Array.sub (len, 0), fn i => Array.sub (s, i))))
      | _ => (oracle_said := "unknown"; A.Asn_unknown)
    val () = stamp 5
  in
    a
  end

fun no_oracle _ _ _ _ _ _ () = A.Asn_unknown

fun run use_oracle input output =
  let
    val () = if c_parse (cstr input) = 0 then () else die "malformed input"
    val sz = Array.array (4, 0)
    val () = c_sizes sz
    val n = Array.sub (sz, 0)
    val m = Array.sub (sz, 1)
    val fa = Array.array (m, 0)
    val ta = Array.array (m, 0)
    val wa = Array.array (m, 0)
    val la = Array.array (Array.sub (sz, 2), 0)
    val rv = Array.array (Array.sub (sz, 3), 0)
    val () = c_fill (fa, ta, wa, la, rv)
    val () = stamp 0
    val (feasible, sel) =
      A.asn_solve_int (if use_oracle then oracle else no_oracle) n fa ta wa la rv ()
    val () = stamp 6
    val selw = Array.tabulate (m, fn e => if Array.sub (sel, e) then 1 else 0)
    val cost = Array.foldli (fn (e, s, c) => if s then c + Array.sub (wa, e) else c) 0 sel
    val note = "oracle: " ^ !oracle_said
  in
    if c_print (cstr output, cstr note, if feasible then 1 else 0, cstr (String.map (fn #"~" => #"-" | c => c) (Int.toString cost)),
                m, fa, ta, selw) = 0
    then (if Asn_Bench.enabled then c_report () else ())
    else die ("cannot write " ^ output)
  end

fun main () =
  case CommandLine.arguments () of
    ["--no-oracle", inp, out] => run false inp out
  | [inp, out] => run true inp out
  | _ => die "usage: asn_solver [--no-oracle] <instance.asn> <solution>"

end

val () = Main.main ()
