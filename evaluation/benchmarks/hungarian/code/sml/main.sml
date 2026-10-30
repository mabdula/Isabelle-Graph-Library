(* Benchmark driver for the verified Hungarian method on DIMACS .asn instances.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .asn file and build the solver's arrays   (not measured)
 *   2. read the clock
 *   3. call the extracted SML solver
 *   4. read the clock again
 *   5. report the difference, plus the objective for checking
 *
 * Only step 3 sits between the two clock reads.  Building the CSR is inside
 * it, because the solver does that itself; reading the file and computing the
 * objective are outside it.
 *
 * The entry point used is `hungarian_csr_run_int', which is the MINIMUM WEIGHT
 * PERFECT MATCHING variant: it takes the bipartite graph as given (no padding
 * to a complete graph) and reports failure unless every vertex is matched.
 * The sibling entry points in the same structure solve other problems --
 * mw = minimum weight (not necessarily perfect), mwmc = minimum weight among
 * maximum cardinality, max_perfect = maximum weight perfect.
 *
 * Note the challenge's own objective is MAXIMUM weight (see the format
 * document); costs are read exactly as they appear in the file and minimised,
 * so a max-weight run means negating costs beforehand, not a different driver.
 *
 * This export's arrays are plain Int.int arrays and a mate is a vertex id with
 * `n' standing for "no mate", so the parser's arrays are handed over as they
 * are -- there is no nat/int wrapping to do and nothing is copied.  The export
 * never writes to fa, ta, wa, la or rv.
 *)

structure H = Hungarian

structure Driver =
struct

  fun err s = (TextIO.output (TextIO.stdErr, s ^ "\n"); OS.Process.exit OS.Process.failure)

  (* ---------- the settled solver arguments ----------
   * theta and cap stopped being knobs once the sweeps settled them: the theta
   * sweep settled theta at |X| (theta_frac 1.0), the cap sweep settled cap at
   * 2.  They are written here as literals rather than carried from the
   * command line to the solver call, so that MLton sees constants at the only
   * call site and can specialise the solver for them -- in particular the
   * chain loop, whose bound is then 2 rather than a value read from a record.
   *
   * The flags are still accepted so the campaign scripts need no change, but
   * they will only take the compiled-in value.  Asking for a different one is
   * an error rather than a request that is quietly ignored: a binary that
   * accepted `--cap 8' and then ran cap 2 would put a false number in the cap
   * column of every row it wrote. *)
  val CAP : int = 2
  val THETA_FRAC : real = 1.0

  val header =
    "instance,nodes,arcs,left,right,theta,theta_frac,cap,status," ^
    "matched,cost,cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms,tag"

  fun usage () =
    err (String.concatWith "\n"
      ["usage: solve_sml [options] <instance.asn>",
       "",
       "  --theta-frac 1.0   shortcut threshold as a fraction of |X|.  This",
       "                     binary is compiled for 1.0; no other value runs.",
       "  --cap 2            longest chain of displacements the shortcut may",
       "                     make before giving up and calling a Dijkstra.",
       "                     This binary is compiled for 2; no other value",
       "                     runs.  Rebuild to measure a different cap.",
       "  --header           print the CSV header line and exit",
       "  --csv              print one CSV row (default)",
       "  --human            print a human-readable block instead of CSV",
       "  --sol              also write the DIMACS solution (s/f lines) to stdout",
       "  --tag <s>          free-form label copied into the `tag' column",
       ""])

  (* ---------- timing ---------- *)

  fun msOf t = Time.toReal t * 1000.0
  fun fmt3 r = Real.fmt (StringCvt.FIX (SOME 3)) r

  (* ---------- argument handling ---------- *)

  type opts = { path : string option, thetaFrac : real, thetaAbs : int option,
                cap : int, csv : bool, sol : bool, tag : string }

  fun parseArgs args =
    let
      fun set (acc : opts, f) = f acc
      fun go (a, acc : opts) =
        case a of
          [] => acc
        | "--header" :: _ => (print (header ^ "\n"); OS.Process.exit OS.Process.success)
        | "--csv" :: r =>
            go (r, { path = #path acc, thetaFrac = #thetaFrac acc,
                     thetaAbs = #thetaAbs acc, cap = #cap acc, csv = true,
                     sol = #sol acc, tag = #tag acc })
        | "--human" :: r =>
            go (r, { path = #path acc, thetaFrac = #thetaFrac acc,
                     thetaAbs = #thetaAbs acc, cap = #cap acc, csv = false,
                     sol = #sol acc, tag = #tag acc })
        | "--sol" :: r =>
            go (r, { path = #path acc, thetaFrac = #thetaFrac acc,
                     thetaAbs = #thetaAbs acc, cap = #cap acc, csv = #csv acc,
                     sol = true, tag = #tag acc })
        | "--theta-frac" :: v :: r =>
            (case Real.fromString v of
               SOME p =>
                 if Real.!= (p, THETA_FRAC) then
                   err ("this binary is compiled for --theta-frac "
                        ^ fmt3 THETA_FRAC ^ "; rebuild to run another")
                 else go (r, { path = #path acc, thetaFrac = p,
                               thetaAbs = #thetaAbs acc, cap = #cap acc,
                               csv = #csv acc, sol = #sol acc, tag = #tag acc })
             | NONE => err ("not a number: " ^ v))
        | "--theta" :: _ =>
            err "this binary is compiled for theta = |X|; rebuild to run another"
        | "--cap" :: v :: r =>
            (case Int.fromString v of
               SOME k =>
                 if k <> CAP then
                   err ("this binary is compiled for --cap " ^ Int.toString CAP
                        ^ "; rebuild to run another")
                 else go (r, { path = #path acc, thetaFrac = #thetaFrac acc,
                               thetaAbs = #thetaAbs acc, cap = k,
                               csv = #csv acc, sol = #sol acc, tag = #tag acc })
             | NONE => err ("not an integer: " ^ v))
        | "--tag" :: v :: r =>
            go (r, { path = #path acc, thetaFrac = #thetaFrac acc,
                     thetaAbs = #thetaAbs acc, cap = #cap acc, csv = #csv acc,
                     sol = #sol acc, tag = v })
        | x :: r =>
            if String.isPrefix "--" x then usage ()
            else go (r, { path = SOME x, thetaFrac = #thetaFrac acc,
                          thetaAbs = #thetaAbs acc, cap = #cap acc,
                          csv = #csv acc, sol = #sol acc, tag = #tag acc })
    in
      go (args, { path = NONE, thetaFrac = 1.0, thetaAbs = NONE, cap = 2,
                  csv = true, sol = false, tag = "" })
    end

  (* ---------- main ---------- *)

  fun run () =
    let
      val opts = parseArgs (CommandLine.arguments ())
      val path = case #path opts of SOME p => p | NONE => usage ()

      val inst = AsnParser.parseFile path
      val { nNodes, nArcs, src, dst, cost, left, right } = inst
      val nLeft = Array.length left
      val nRight = Array.length right

      (* The CSR builder buckets an arc under index src+2 of an (n+1)-long
       * array, guarded by src+2 <= n, so a left vertex with a near-maximal id
       * would be dropped silently.  Widening n only makes the solver's arrays
       * longer, so take the safe bound. *)
      val maxLeft = Array.foldl Int.max ~1 left
      val n = Int.max (nNodes, maxLeft + 2)

      (* theta_frac 1.0 means theta = |X|, written out so that no real
       * arithmetic stands between the constant and the solver call. *)
      val theta = nLeft
      val thetaFracEff = if nLeft = 0 then 0.0 else THETA_FRAC
      val cap = CAP

      (* ---- 2. clock ----
       * CPU time is the measurement.  Wall time is read as well and kept in
       * the raw data, but it is not what any comparison is drawn from: the
       * campaign runs seven solvers at once, so wall time carries whatever the
       * other six were doing, while CPU time does not. *)
      val cpu = Timer.startCPUTimer ()
      val t0 = Time.now ()

      (* ---- 3. solve ---- *)
      val (_, (mi, _)) = H.hungarian_csr_run_int n nLeft CAP src dst cost left right ()

      (* ---- 4. clock ---- *)
      val t1 = Time.now ()
      val { usr, sys } = Timer.checkCPUTimer cpu

      (* ---- 5. report ---- *)
      val wallMs = msOf (Time.- (t1, t0))
      val usrMs = msOf usr
      val sysMs = msOf sys
      val cpuMs = usrMs + sysMs

      (* A mate of `n' means unmatched: the export allocates the mate array as
       * Array.array (n, n) and a real mate is a vertex id, which is < n. *)
      fun mateOf u =
        if u < Array.length mi
        then let val v = Array.sub (mi, u) in if v = n then NONE else SOME v end
        else NONE

      val matched =
        Array.foldl (fn (u, k) => case mateOf u of SOME _ => k + 1 | NONE => k) 0 left

      (* Sum the cost of the matched arcs.  Done after the clock, and guarded
       * against parallel arcs so a repeated pair is counted once. *)
      val counted = Array.array (n, false)
      val total = ref (0 : IntInf.int)
      val () =
        Array.appi
          (fn (i, u) =>
             if Array.sub (counted, u) then ()
             else case mateOf u of
                    SOME v =>
                      if v = Array.sub (dst, i)
                      then (Array.update (counted, u, true);
                            total := !total + IntInf.fromInt (Array.sub (cost, i)))
                      else ()
                  | NONE => ())
          src

      val perfect = (nLeft = nRight) andalso (matched = nLeft)
      val status = if perfect then "OPTIMAL" else "NO_PERFECT_MATCHING"
      val costStr = if perfect then IntInf.toString (!total) else "NA"

      val base = OS.Path.file path

      val () =
        if #csv opts then
          print (String.concatWith ","
            [base, Int.toString nNodes, Int.toString nArcs,
             Int.toString nLeft, Int.toString nRight,
             Int.toString theta, fmt3 thetaFracEff, Int.toString cap,
             status, Int.toString matched, costStr,
             fmt3 cpuMs, fmt3 usrMs, fmt3 sysMs, fmt3 cpuMs, fmt3 wallMs,
             #tag opts] ^ "\n")
        else
          print (String.concat
            ["instance   ", base, "\n",
             "nodes      ", Int.toString nNodes,
             " (|X| = ", Int.toString nLeft,
             ", |Y| = ", Int.toString nRight, ")\n",
             "arcs       ", Int.toString nArcs, "\n",
             "theta      ", Int.toString theta,
             "  (", fmt3 thetaFracEff, " of |X|)\n",
             "cap        ", Int.toString cap, "\n",
             "status     ", status, "\n",
             "matched    ", Int.toString matched, "\n",
             "cost       ", costStr, "\n",
             "cpu        ", fmt3 cpuMs, " ms   (the measurement)\n",
             "cpu user   ", fmt3 usrMs, " ms\n",
             "cpu sys    ", fmt3 sysMs, " ms\n",
             "wall       ", fmt3 wallMs, " ms\n"])

      val () =
        if #sol opts andalso perfect then
          (print ("s " ^ IntInf.toString (!total) ^ "\n");
           Array.app
             (fn u => case mateOf u of
                        SOME v => print ("f " ^ Int.toString (u + 1) ^ " " ^
                                         Int.toString (v + 1) ^ " 1\n")
                      | NONE => ())
             left)
        else if #sol opts then print "c no perfect matching exists\n"
        else ()
    in
      OS.Process.exit (if perfect then OS.Process.success else OS.Process.failure)
    end

end

val () = Driver.run ()
