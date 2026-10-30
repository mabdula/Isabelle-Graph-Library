(* The SML driver: one of the four problems, on one instance, timed.
 *
 *   solve_sml PROBLEM INSTANCE
 *   PROBLEM = matching | b_matching | weighted_matching | weighted_b_matching
 *
 * It prints one line, the shape every solver in the study answers in:
 *
 *   cpu_ms=<int> user_ms=<int> sys_ms=<int> card=<int> weight=<int>
 *
 * What is measured is the CPU time of the call into the generated code and
 * nothing else. Reading the instance, building the arrays, computing the
 * objective and checking the answer all happen outside the two clock readings.
 *
 * The entry point returns a thunk and the work happens when the thunk is
 * forced, not when the entry point is called, so the clock has to bracket both
 * -- matching_imp nv fa ta and the () that follows it. The case below
 * therefore only builds a function; the call itself happens between the
 * readings.
 *
 * Built with -default-type int64, so Int.int is 64-bit and the arrays handed
 * to the generated code hold the same integers Go's int64 and Scala's Long do.
 *)
structure Main =
struct

fun die msg =
  (TextIO.output (TextIO.stdErr, "error: " ^ msg ^ "\n");
   OS.Process.exit OS.Process.failure)

(* Whether each problem is weighted and whether it is capacitated -- the same
 * two flags the Sage baselines take. *)
fun flags "matching"            = SOME (false, false)
  | flags "b_matching"          = SOME (false, true)
  | flags "weighted_matching"   = SOME (true,  false)
  | flags "weighted_b_matching" = SOME (true,  true)
  | flags _                     = NONE

fun ms us = (us + 500) div 1000

fun main () =
  case CommandLine.arguments () of
      [problem, path] =>
        (case flags problem of
             NONE => die ("unknown problem " ^ problem)
           | SOME (_, capacities) =>
             let
               val inst = Instance.read (path, capacities)
                          handle Instance.Bad m => die m
                               | IO.Io {name, ...} => die ("cannot read " ^ name)
               val {fa, ta, wa, ka, ...} = inst
               val nv = Instance.nv inst
               val run =
                 case problem of
                     "matching"            => (fn () => Bipartite_Matching.matching_imp nv fa ta ())
                   | "b_matching"          => (fn () => Bipartite_Matching.b_matching_imp fa ta ka ())
                   | "weighted_matching"   => (fn () => Bipartite_Matching.weighted_matching_int_imp nv fa ta wa ())
                   | _                     => (fn () => Bipartite_Matching.weighted_b_matching_int_imp fa ta ka wa ())

               val timer = Timer.startCPUTimer ()
               val sol = run ()
               val {usr, sys} = Timer.checkCPUTimer timer

               val () = Instance.checkIndependent (inst, sol)
                        handle Instance.Bad m =>
                               die ("the answer is not a common independent set: " ^ m)
               val (card, weight) = Instance.objective (inst, sol)
               val u = Time.toMicroseconds usr
               val s = Time.toMicroseconds sys
             in
               print ("cpu_ms=" ^ LargeInt.toString (ms (u + s))
                      ^ " user_ms=" ^ LargeInt.toString (ms u)
                      ^ " sys_ms=" ^ LargeInt.toString (ms s)
                      ^ " card=" ^ Int.toString card
                      ^ " weight=" ^ Int.toString weight ^ "\n")
             end)
    | _ => die ("usage: " ^ CommandLine.name () ^ " PROBLEM INSTANCE")

end

val () = Main.main ()
