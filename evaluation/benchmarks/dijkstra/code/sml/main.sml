(* Benchmark driver for the verified Dijkstra export on DIMACS .gr instances.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .gr file into three arc arrays            (not measured)
 *   2. read the clock
 *   3. call the extracted SML solver
 *   4. read the clock again
 *   5. report the difference, plus the answer for checking
 *
 * Only step 3 sits between the two clock reads.  Building the CSR is inside
 * it, because the solver does that itself and this study measures the whole
 * verified program, setup included.  Reading the file and adding up the cost
 * of the returned path are outside it.
 *
 * The entry point used is `dijkstra_shortest_path_int', the point-to-point
 * variant: it takes a set of sources and a set of targets, stops as soon as a
 * target is settled, and returns the path as a list of arc indices into the
 * arrays it was given, or NONE if no target is reachable.  The sibling entry
 * points `dijkstra_sp_compute_int' and `dijkstra_sp_query_int' split the same
 * work into a full run and a separate path extraction.
 *
 * ONE PROBLEM PER PROCESS.  The source and the target are given on the command
 * line and exactly one of them is accepted: a shortest-path problem is a graph
 * AND a pair, so two pairs are two problems and must not share a solver call,
 * a solver object, or a process.  There is deliberately no way to hand this
 * driver a list of pairs.  The pair is copied into the output row next to the
 * time it produced, so the campaign's queries.csv can be checked against the
 * results rather than trusted.
 *
 * The vertex count handed to the solver is `nodes + 2', not `nodes'.  The
 * export's CSR counting pass buckets an arc under index src+2 of an
 * (n+1)-long array, guarded by src+2 <= n, so with ids running up to `nodes'
 * the out-arcs of the two highest ids would be dropped silently.  Widening n
 * only makes the solver's own arrays longer; it changes nothing else.
 *)

structure D = Dijkstra

structure Driver =
struct

  fun err s = (TextIO.output (TextIO.stdErr, s ^ "\n");
               OS.Process.exit OS.Process.failure)

  val header =
    "instance,nodes,arcs,query,source,target,repeat,status," ^
    "reached,hops,dist,cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms," ^
    "parse_ms,dedup_ms,build_ms,tag"

  fun usage () =
    err (String.concatWith "\n"
      ["usage: solve_sml [options] <instance.gr>",
       "",
       "  --source <v>       the source, a DIMACS node id (1-based)",
       "  --target <v>       the target, a DIMACS node id (1-based)",
       "  --query <id>       the id this pair carries in queries.csv,",
       "                     copied into the `query' column (default 0)",
       "  --repeats <k>      solve the SAME problem k times and print a row",
       "                     for each (default 1).  The campaign uses one",
       "                     process per repeat instead.",
       "  --header           print the CSV header line and exit",
       "  --csv              print one CSV row per query and repeat (default)",
       "  --human            print a human-readable block instead",
       "  --tag <s>          free-form label copied into the `tag' column",
       ""])

  (* ---------- timing ---------- *)

  fun msOf t = Time.toReal t * 1000.0
  fun fmt3 r = Real.fmt (StringCvt.FIX (SOME 3)) r

  (* ---------- argument handling ---------- *)

  type opts = { path : string option, source : int option, target : int option,
                query : int, repeats : int, csv : bool, tag : string }

  fun parseArgs args =
    let
      fun set (acc : opts, path, source, target, query, repeats, csv, tag) =
        { path = path, source = source, target = target, query = query,
          repeats = repeats, csv = csv, tag = tag } : opts
      fun int v = case Int.fromString v of
                    SOME k => k
                  | NONE => err ("not an integer: " ^ v)
      fun go (a, acc : opts) =
        case a of
          [] => acc
        | "--header" :: _ => (print (header ^ "\n");
                              OS.Process.exit OS.Process.success)
        | "--csv" :: r =>
            go (r, set (acc, #path acc, #source acc, #target acc, #query acc,
                        #repeats acc, true, #tag acc))
        | "--human" :: r =>
            go (r, set (acc, #path acc, #source acc, #target acc, #query acc,
                        #repeats acc, false, #tag acc))
        | "--source" :: v :: r =>
            go (r, set (acc, #path acc, SOME (int v), #target acc, #query acc,
                        #repeats acc, #csv acc, #tag acc))
        | "--target" :: v :: r =>
            go (r, set (acc, #path acc, #source acc, SOME (int v), #query acc,
                        #repeats acc, #csv acc, #tag acc))
        | "--query" :: v :: r =>
            go (r, set (acc, #path acc, #source acc, #target acc, int v,
                        #repeats acc, #csv acc, #tag acc))
        | "--repeats" :: v :: r =>
            let val k = int v in
              if k < 1 then err "--repeats must be at least 1"
              else go (r, set (acc, #path acc, #source acc, #target acc,
                               #query acc, k, #csv acc, #tag acc))
            end
        | "--tag" :: v :: r =>
            go (r, set (acc, #path acc, #source acc, #target acc, #query acc,
                        #repeats acc, #csv acc, v))
        | x :: r =>
            if String.isPrefix "--" x then usage ()
            else go (r, set (acc, SOME x, #source acc, #target acc, #query acc,
                             #repeats acc, #csv acc, #tag acc))
    in
      go (args, { path = NONE, source = NONE, target = NONE, query = 0,
                  repeats = 1, csv = true, tag = "" })
    end

  (* ---------- main ---------- *)

  fun run () =
    let
      val opts = parseArgs (CommandLine.arguments ())
      val path = case #path opts of SOME p => p | NONE => usage ()
      val s = case #source opts of SOME v => v
                                 | NONE => err "a --source is required"
      val t = case #target opts of SOME v => v
                                 | NONE => err "a --target is required"
      val qid = #query opts
      val base = List.last (String.tokens (fn c => c = #"/") path)

      (* Parsing is clocked and reported too, so that what sits OUTSIDE the
       * measurement is visible rather than merely asserted.  dedup_ms and
       * build_ms are 0.000 here and that is not padding: this solver takes
       * parallel arcs as they come, and builds its CSR inside the entry
       * point, where it is measured.  The two Python baselines cannot do
       * either and their columns say so. *)
      val setupCpu = Timer.startCPUTimer ()
      val { n = nNodes, m = nArcs, fa, ta, wa } = GrParser.parseFile path
      val { usr = pUsr, sys = pSys } = Timer.checkCPUTimer setupCpu
      val parseMs = msOf pUsr + msOf pSys
      val n = nNodes + 2

      fun one rep =
        let
          val sa = Array.fromList [s]
          val tv = Array.fromList [t]

          (* ---- 2. clock ----
           * CPU time is the measurement.  Wall time is read as well and kept
           * in the raw data, but no comparison is drawn from it: the campaign
           * runs several solvers at once, so wall time carries whatever the
           * others were doing and CPU time does not.
           *
           * `proc_ms' is the whole process rather than the one thread.  Here
           * the two are the same number, because MLton reads getrusage on a
           * process that is doing nothing else; the column exists so that the
           * Scala driver, where they differ by the cost of the JIT, can be
           * read against these without a second shape of row. *)
          val cpu = Timer.startCPUTimer ()
          val t0 = Time.now ()

          (* ---- 3. solve ---- *)
          val res = D.dijkstra_shortest_path_int n fa ta wa sa tv ()

          (* ---- 4. clock ---- *)
          val t1 = Time.now ()
          val { usr, sys } = Timer.checkCPUTimer cpu

          val usrMs = msOf usr
          val sysMs = msOf sys
          val cpuMs = usrMs + sysMs
          val wallMs = msOf (Time.- (t1, t0))

          (* ---- 5. the answer, after the clock ---- *)
          val (status, reached, hops, dist) =
            case res of
              NONE => ("UNREACHABLE", 0, 0, ~1)
            | SOME ids =>
                let
                  val k = Array.length ids
                  val d = Array.foldl (fn (i, acc) => acc + Array.sub (wa, i)) 0 ids
                  (* the path runs from the source to the target; check the
                   * endpoints rather than trusting the length alone *)
                  val okEnds =
                    k = 0 orelse
                    (Array.sub (fa, Array.sub (ids, 0)) = s
                     andalso Array.sub (ta, Array.sub (ids, k - 1)) = t)
                in
                  (if okEnds then "OPTIMAL" else "BAD_PATH", 1, k, d)
                end
        in
          if #csv opts then
            print (String.concatWith ","
              [base, Int.toString nNodes, Int.toString nArcs,
               Int.toString qid, Int.toString s, Int.toString t,
               Int.toString rep, status,
               Int.toString reached, Int.toString hops, Int.toString dist,
               fmt3 cpuMs, fmt3 usrMs, fmt3 sysMs, fmt3 cpuMs, fmt3 wallMs,
               fmt3 parseMs, "0.000", "0.000",
               #tag opts] ^ "\n")
          else
            print (String.concat
              ["query ", Int.toString qid, "  ", Int.toString s, " -> ",
               Int.toString t, "  rep ", Int.toString rep, "\n",
               "  status   ", status, "\n",
               "  hops     ", Int.toString hops, "\n",
               "  dist     ", Int.toString dist, "\n",
               "  cpu      ", fmt3 cpuMs, " ms   (the measurement)\n",
               "  wall     ", fmt3 wallMs, " ms\n"])
        end

      fun go r = if r > #repeats opts then () else (one r; go (r + 1))
    in
      if s < 1 orelse s > nNodes orelse t < 1 orelse t > nNodes then
        err ("query " ^ Int.toString qid ^ ": (" ^ Int.toString s ^ ", " ^
             Int.toString t ^ ") outside [1, " ^ Int.toString nNodes ^ "]")
      else ();
      go 1
    end

end

val () = Driver.run ()
