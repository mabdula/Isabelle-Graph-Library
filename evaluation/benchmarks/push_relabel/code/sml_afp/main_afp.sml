(* Benchmark driver for the AFP FIFO push-relabel export on DIMACS
 * maximum-flow instances, Standard ML.
 *
 * This is the older verified baseline, from the Archive of Formal Proofs.  It
 * is the same algorithm family as the newer export's FIFO variant and a very
 * different program.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .max file into arc arrays                 (clocked, reported)
 *   2. build the adjacency map and the capacity lookup     (clocked, reported)
 *   3. read the clock
 *   4. call fifo_push_relabel_impl
 *   5. read the clock again
 *   6. check the flow and add up its value                 (after the clock)
 *
 * Only step 4 sits between the two clock reads, and it is the WHOLE verified
 * program: fifo_push_relabel_impl tabulates the export's own n-by-n residual
 * capacity matrix from the capacity function, saturates the source arcs,
 * initialises the labels, the counters and the FIFO queue, and only then
 * starts discharging.  The matrix build is the export's setup and this study
 * measures verified exports whole, so it is inside.
 *
 * Step 2 is outside, and that favours this column.  The export takes an
 * adjacency map and a capacity function rather than an arc list, so something
 * has to turn the file's arcs into them; the newer export offers an entry
 * point that takes the arc arrays and builds its own structures inside the
 * clock, and this one does not.  The cost is reported in build_ms rather than
 * folded away, so the size of the discount is visible.
 *
 * THE MATRIX IS THE CEILING.  cf_init_impl is mtx_tabulate n n, a dense
 * array of n*n machine integers, filled entry by entry.  At eight bytes an
 * entry that is 800 MB at n = 10,000 and 80 GB at n = 100,000, and the fill
 * alone is n*n calls of the capacity function before any flow moves.  So this
 * column stops far below the sizes the other twelve reach, and it stops for a
 * reason that is a property of the verified program rather than of the
 * machine.  Where it cannot start, the row says OOM and the ladder stops.
 *
 * THE VALUE IS ADDED UP AFTER THE CLOCK, as a cross-reference against the
 * other twelve solvers and nothing more.  What comes back is the final
 * residual matrix, so the flow on an arc is its capacity less the residual,
 * and the value is the net out of the source.
 *
 * ONE PROBLEM PER PROCESS, as everywhere in this study.
 *)

structure A = AFP_FIFO_Push_Relabel

structure Driver =
struct

  fun err s = (TextIO.output (TextIO.stdErr, s ^ "\n");
               OS.Process.exit OS.Process.failure)

  val header =
"instance,nodes,arcs,variant,source,target,repeat,status," ^
    "flow_value,cpu_ms,cpu_usr_ms,cpu_sys_ms,thread_ms,wall_ms," ^
    "parse_ms,dedup_ms,build_ms,tag"

  fun usage () =
    err (String.concatWith "\n"
      ["usage: solve_sml_afp [options] <instance.max>",
       "",
       "  --source <v>       the source, a DIMACS node id (1-based).",
       "                     Defaults to the file's own `n <id> s' line.",
       "  --target <v>       the sink, likewise, from `n <id> t'",
       "  --repeats <k>      solve the SAME problem k times (default 1)",
       "  --header           print the CSV header line and exit",
       "  --csv              print one CSV row per repeat (default)",
       "  --human            print a human-readable block instead",
       "  --tag <s>          free-form label copied into the `tag' column",
       ""])

  fun msOf t = Time.toReal t * 1000.0
  fun fmt3 r = Real.fmt (StringCvt.FIX (SOME 3)) r

  type opts = { path : string option, source : int option, target : int option,
                repeats : int, csv : bool, tag : string }

  fun parseArgs args =
    let
      fun int v = case Int.fromString v of
                    SOME k => k | NONE => err ("not an integer: " ^ v)
      fun go (a, acc : opts) =
        case a of
          [] => acc
        | "--header" :: _ => (print (header ^ "\n");
                              OS.Process.exit OS.Process.success)
        | "--source" :: v :: r =>
            go (r, { path = #path acc, source = SOME (int v),
                     target = #target acc, repeats = #repeats acc,
                     csv = #csv acc, tag = #tag acc })
        | "--target" :: v :: r =>
            go (r, { path = #path acc, source = #source acc,
                     target = SOME (int v), repeats = #repeats acc,
                     csv = #csv acc, tag = #tag acc })
        | "--repeats" :: v :: r =>
            go (r, { path = #path acc, source = #source acc,
                     target = #target acc, repeats = int v,
                     csv = #csv acc, tag = #tag acc })
        | "--tag" :: v :: r =>
            go (r, { path = #path acc, source = #source acc,
                     target = #target acc, repeats = #repeats acc,
                     csv = #csv acc, tag = v })
        | "--csv" :: r =>
            go (r, { path = #path acc, source = #source acc,
                     target = #target acc, repeats = #repeats acc,
                     csv = true, tag = #tag acc })
        | "--human" :: r =>
            go (r, { path = #path acc, source = #source acc,
                     target = #target acc, repeats = #repeats acc,
                     csv = false, tag = #tag acc })
        | x :: r =>
            if String.isPrefix "--" x then err ("unknown option: " ^ x)
            else go (r, { path = SOME x, source = #source acc,
                          target = #target acc, repeats = #repeats acc,
                          csv = #csv acc, tag = #tag acc })
    in
      go (args, { path = NONE, source = NONE, target = NONE,
                  repeats = 1, csv = true, tag = "" } : opts)
    end

  (* The flow on the ordered pair (u, v) is what the capacity lost: the arc
   * started at c(u,v) and ended at cf(u,v).  Checking conservation here is
   * what tells a maximum flow apart from a maximum preflow. *)
  fun checkFlow (n, fwd, cf, s, t) =
    let
      val net = Array.array (n, 0)
      val rs = #rowStart fwd and col = #col fwd and cap = #cap fwd
      fun row (u, i, hi, ok) =
        if i >= hi then ok
        else
          let
            val v = Array.sub (col, i)
            val f = Array.sub (cap, i) - Array.sub (cf, u * n + v)
          in
            if f < 0 orelse f > Array.sub (cap, i) then false
            else (Array.update (net, u, Array.sub (net, u) - f);
                  Array.update (net, v, Array.sub (net, v) + f);
                  row (u, i + 1, hi, ok))
          end
      fun scan (u, ok) =
        if u >= n orelse not ok then ok
        else scan (u + 1, row (u, Array.sub (rs, u), Array.sub (rs, u + 1), ok))
      val withinCaps = scan (0, true)
      fun balanced v =
        if v >= n then true
        else if v = s orelse v = t then balanced (v + 1)
        else if Array.sub (net, v) <> 0 then false
        else balanced (v + 1)
      val value = ~(Array.sub (net, s))
      val status =
        if not withinCaps then "OVER_CAPACITY"
        else if not (balanced 0) then "NOT_A_FLOW"
        else if value <> Array.sub (net, t) then "UNBALANCED_ENDS"
        else "OK"
    in
      (value, status)
    end

  fun main () =
    let
      val opts = parseArgs (CommandLine.arguments ())
      val path = case #path opts of SOME p => p | NONE => usage ()
      val base = List.last (String.tokens (fn c => c = #"/") path)

      val setupCpu = Timer.startCPUTimer ()
      val { n = nNodes, m = nArcs, s = fileS, t = fileT, fa, ta, ca } =
            MaxParser.parseFile path
      val { usr = pUsr, sys = pSys } = Timer.checkCPUTimer setupCpu
      val parseMs = msOf pUsr + msOf pSys

      val s = case #source opts of SOME v => v | NONE => fileS
      val t = case #target opts of SOME v => v | NONE => fileT
      val _ = if s < 1 orelse s > nNodes orelse t < 1 orelse t > nNodes then
                err ("source or sink outside [1, " ^ Int.toString nNodes ^ "]")
              else ()
      val _ = if s = t then err "source and sink are the same vertex" else ()
      val n = nNodes + 1

      (* ---- 2. the shapes this export's entry point wants ---- *)
      val buildCpu = Timer.startCPUTimer ()
      val fwd = Csr.build (n, nArcs, fa, ta, ca)
      val bwd = Csr.build (n, nArcs, ta, fa, ca)
      val am = Csr.adjacency (fwd, bwd)
      val cfun = Csr.lookup fwd
      val { usr = bUsr, sys = bSys } = Timer.checkCPUTimer buildCpu
      val buildMs = msOf bUsr + msOf bSys

      fun one rep =
        let
          (* ---- 3. clock ---- *)
          val cpu = Timer.startCPUTimer ()
          val t0 = Time.now ()

          (* ---- 4. the verified program, whole: matrix and all ---- *)
          val cf = A.fifo_push_relabel_impl cfun s t n am ()

          (* ---- 5. clock ---- *)
          val t1 = Time.now ()
          val { usr, sys } = Timer.checkCPUTimer cpu

          val usrMs = msOf usr
          val sysMs = msOf sys
          val cpuMs = usrMs + sysMs
          val wallMs = msOf (Time.- (t1, t0))

          (* ---- 6. the answer, after the clock ---- *)
          val (value, status) = checkFlow (n, fwd, cf, s, t)
        in
          if #csv opts then
            print (String.concatWith ","
              [base, Int.toString nNodes, Int.toString nArcs,
               "afp_fifo", Int.toString s, Int.toString t,
               Int.toString rep, status, Int.toString value,
               fmt3 cpuMs, fmt3 usrMs, fmt3 sysMs, fmt3 cpuMs, fmt3 wallMs,
               fmt3 parseMs, "0.000", fmt3 buildMs,
               #tag opts] ^ "\n")
          else
            print (String.concat
              ["instance ", base, "  ", Int.toString nNodes, " nodes, ",
               Int.toString nArcs, " arcs\n",
               "variant  afp_fifo   ", Int.toString s, " -> ",
               Int.toString t, "   rep ", Int.toString rep, "\n",
               "flow     ", Int.toString value, "  (", status, ")\n",
               "cpu      ", fmt3 cpuMs, " ms   wall ", fmt3 wallMs,
               " ms   parse ", fmt3 parseMs, " ms   build ", fmt3 buildMs,
               " ms\n"])
        end

      fun loop k = if k > #repeats opts then () else (one k; loop (k + 1))
    in
      loop 1
    end

end

val () = Driver.main ()
