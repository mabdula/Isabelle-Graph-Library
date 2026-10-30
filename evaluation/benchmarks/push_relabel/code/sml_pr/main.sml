(* Benchmark driver for the verified push-relabel export on DIMACS
 * maximum-flow instances, Standard ML.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .max file into arc arrays                 (clocked, reported)
 *   2. read the clock
 *   3. call push_relabel_hl_run_int or push_relabel_fifo_run_int
 *   4. read the clock again
 *   5. add up the flow value, as a check                   (after the clock)
 *   6. report the difference, plus the value for cross-referencing
 *
 * Only step 3 sits between the two clock reads.  Building the two CSR
 * directions is inside it, because the export does that itself and this study
 * measures the whole verified program, setup included: the entry point is
 * handed three flat arrays and from them builds the forward CSR, the backward
 * CSR, the vertex set, the residual arrays, the excess and label arrays, the
 * label buckets and the counters before a single unit of flow moves.  Reading
 * the file is outside it, and so is reading the answer off afterwards.
 *
 * The entry point is
 *
 *     push_relabel_{hl,fifo}_run_int
 *       : int -> int -> int -> int array -> int array -> int array
 *       -> (unit -> int array)
 *
 * taking the vertex count, the source, the sink, the arc tails, the arc heads
 * and the arc capacities, and returning the flow on each arc.  parse_ms is
 * reported separately; dedup_ms and build_ms are 0.000 and that is not
 * padding, since this export takes parallel arcs as they come and is handed
 * the parser's own arrays with no structure built on its behalf.
 *
 * A MAXIMUM FLOW, NOT A MAXIMUM PREFLOW.  Both variants run until no vertex
 * other than the source and the sink carries any excess: the bucket array
 * spans labels up to 2n and pr_hl_find scans every label down to zero, and
 * the FIFO queue admits any vertex with excess whatever its label.  There is
 * no second phase because a run to exhaustion needs none -- what it ends with
 * is a flow already.  So no column of this study stops at a preflow, and the
 * value below is a maximum flow value.
 *
 * RELABEL-TO-FRONT IS NOT BENCHMARKED.  The export also offers
 * push_relabel_rtf_run_int.  It is not wired to anything here.
 *
 * THE VALUE IS ADDED UP AFTER THE CLOCK.  It is a cross-reference between the
 * thirteen solvers and nothing more; the measurement is the flow computation
 * alone, with no summing up inside it.  The sum is the net flow out of the
 * source -- out-arcs less in-arcs -- rather than merely the out-arcs, because
 * the source may have arcs coming back into it and a bare sum would then
 * overcount.
 *
 * ONE PROBLEM PER PROCESS.  The source and the sink are the file's own `n'
 * designator lines unless given on the command line, and there is deliberately
 * no way to hand this driver a second pair: a flow problem is a graph AND a
 * pair, so two pairs are two problems and must not share a solver call, a
 * solver object, or a process.
 *
 * The vertex count handed to the export is `nodes + 2', not `nodes'.  The CSR
 * counting pass buckets an arc under index tail+2 of an (n+1)-long array,
 * guarded by tail+2 <= n, so with ids running up to `nodes' the out-arcs of
 * the two highest ids would be dropped silently.  Widening n only makes the
 * export's own arrays longer; it changes nothing else.
 *)

structure P = Push_Relabel

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
      ["usage: solve_sml_pr [options] <instance.max>",
       "",
       "  --variant <v>      hl (highest label) or fifo.  Required.",
       "  --source <v>       the source, a DIMACS node id (1-based).",
       "                     Defaults to the file's own `n <id> s' line.",
       "  --target <v>       the sink, likewise, from `n <id> t'",
       "  --repeats <k>      solve the SAME problem k times and print a row",
       "                     for each (default 1).  The campaign uses one",
       "                     process per repeat instead.",
       "  --header           print the CSV header line and exit",
       "  --csv              print one CSV row per repeat (default)",
       "  --human            print a human-readable block instead",
       "  --tag <s>          free-form label copied into the `tag' column",
       ""])

  (* ---------- timing ---------- *)

  fun msOf t = Time.toReal t * 1000.0
  fun fmt3 r = Real.fmt (StringCvt.FIX (SOME 3)) r

  (* ---------- argument handling ---------- *)

  type opts = { path : string option, variant : string option,
                source : int option, target : int option,
                repeats : int, csv : bool, tag : string }

  fun parseArgs args =
    let
      fun int v = case Int.fromString v of
                    SOME k => k
                  | NONE => err ("not an integer: " ^ v)
      fun go (a, acc : opts) =
        case a of
          [] => acc
        | "--header" :: _ => (print (header ^ "\n");
                              OS.Process.exit OS.Process.success)
        | "--variant" :: v :: r =>
            go (r, { path = #path acc, variant = SOME v, source = #source acc,
                     target = #target acc, repeats = #repeats acc,
                     csv = #csv acc, tag = #tag acc })
        | "--source" :: v :: r =>
            go (r, { path = #path acc, variant = #variant acc,
                     source = SOME (int v), target = #target acc,
                     repeats = #repeats acc, csv = #csv acc, tag = #tag acc })
        | "--target" :: v :: r =>
            go (r, { path = #path acc, variant = #variant acc,
                     source = #source acc, target = SOME (int v),
                     repeats = #repeats acc, csv = #csv acc, tag = #tag acc })
        | "--repeats" :: v :: r =>
            go (r, { path = #path acc, variant = #variant acc,
                     source = #source acc, target = #target acc,
                     repeats = int v, csv = #csv acc, tag = #tag acc })
        | "--tag" :: v :: r =>
            go (r, { path = #path acc, variant = #variant acc,
                     source = #source acc, target = #target acc,
                     repeats = #repeats acc, csv = #csv acc, tag = v })
        | "--csv" :: r =>
            go (r, { path = #path acc, variant = #variant acc,
                     source = #source acc, target = #target acc,
                     repeats = #repeats acc, csv = true, tag = #tag acc })
        | "--human" :: r =>
            go (r, { path = #path acc, variant = #variant acc,
                     source = #source acc, target = #target acc,
                     repeats = #repeats acc, csv = false, tag = #tag acc })
        | x :: r =>
            if String.isPrefix "--" x then err ("unknown option: " ^ x)
            else go (r, { path = SOME x, variant = #variant acc,
                          source = #source acc, target = #target acc,
                          repeats = #repeats acc, csv = #csv acc,
                          tag = #tag acc })
    in
      go (args, { path = NONE, variant = NONE, source = NONE, target = NONE,
                  repeats = 1, csv = true, tag = "" } : opts)
    end

  (* ---------- the answer, read off after the clock ----------
   *
   * Two things are checked, and both are checks rather than part of the
   * measurement.  First that what came back is a FLOW: every arc within its
   * capacity, and every vertex but the source and the sink balanced.  A
   * maximum preflow would pass the capacity test and fail the balance test,
   * which is exactly the confusion this study has to be able to rule out.
   * Second the value, as the net flow out of the source -- out-arcs less
   * in-arcs, since the source may have arcs coming back into it and a bare
   * sum of out-arcs would then overcount.
   *)

  fun checkFlow (n, m, fa, ta, ca, bw, s, t) =
    let
      val net = Array.array (n, 0)
      fun scan i =
        if i >= m then true
        else
          let
            val f = Array.sub (bw, i)
          in
            if f < 0 orelse f > Array.sub (ca, i) then false
            else
              let
                val u = Array.sub (fa, i)
                val v = Array.sub (ta, i)
              in
                Array.update (net, u, Array.sub (net, u) - f);
                Array.update (net, v, Array.sub (net, v) + f);
                scan (i + 1)
              end
          end
      val withinCaps = scan 0
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
      val variant = case #variant opts of
                      SOME v => v
                    | NONE => err "a --variant is required: hl or fifo"
      val entry =
        case variant of
          "hl"   => P.push_relabel_hl_run_int
        | "fifo" => P.push_relabel_fifo_run_int
        | v      => err ("unknown variant: " ^ v ^ " (hl or fifo)")
      val base = List.last (String.tokens (fn c => c = #"/") path)

      (* Parsing is clocked and reported too, so that what sits OUTSIDE the
       * measurement is visible rather than merely asserted. *)
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
      val n = nNodes + 2

      fun one rep =
        let
          (* ---- 2. clock ----
           * CPU time is the measurement.  Wall time is read as well and kept
           * in the raw data, but no comparison is drawn from it: the campaign
           * runs several solvers at once, so wall time carries whatever the
           * others were doing and CPU time does not. *)
          val cpu = Timer.startCPUTimer ()
          val t0 = Time.now ()

          (* ---- 3. the verified program, whole ---- *)
          val bw = entry n s t fa ta ca ()

          (* ---- 4. clock ---- *)
          val t1 = Time.now ()
          val { usr, sys } = Timer.checkCPUTimer cpu

          val usrMs = msOf usr
          val sysMs = msOf sys
          val cpuMs = usrMs + sysMs
          val wallMs = msOf (Time.- (t1, t0))

          (* ---- 5. the answer, after the clock ---- *)
          val (value, status) = checkFlow (n, nArcs, fa, ta, ca, bw, s, t)
        in
          if #csv opts then
            print (String.concatWith ","
              [base, Int.toString nNodes, Int.toString nArcs,
               variant, Int.toString s, Int.toString t,
               Int.toString rep, status, Int.toString value,
               fmt3 cpuMs, fmt3 usrMs, fmt3 sysMs, fmt3 cpuMs, fmt3 wallMs,
               fmt3 parseMs, "0.000", "0.000",
               #tag opts] ^ "\n")
          else
            print (String.concat
              ["instance ", base, "  ", Int.toString nNodes, " nodes, ",
               Int.toString nArcs, " arcs\n",
               "variant  ", variant, "   ", Int.toString s, " -> ",
               Int.toString t, "   rep ", Int.toString rep, "\n",
               "flow     ", Int.toString value, "  (", status, ")\n",
               "cpu      ", fmt3 cpuMs, " ms   wall ", fmt3 wallMs,
               " ms   parse ", fmt3 parseMs, " ms\n"])
        end

      fun loop k = if k > #repeats opts then () else (one k; loop (k + 1))
    in
      loop 1
    end

end

val () = Driver.main ()
