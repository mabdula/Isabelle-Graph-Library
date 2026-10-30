(* Benchmark driver for the FUNCTIONAL verified BFS export (red-black trees)
 * on DIMACS .gr instances.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .gr file into arc arrays                  (clocked, reported)
 *   2. turn those arrays into the (tail, head) LIST the
 *      export's entry points take                          (clocked, reported)
 *   3. read the clock
 *   4. call graph_rbt, build_rbt_sources and
 *      bFS_check_reachable_rbt
 *   5. read the clock again
 *   6. report the difference, plus the answer for checking
 *
 * WHAT IS INSIDE THE CLOCK.  Steps 3 to 5, which is everything the verified
 * code does -- and that deliberately includes `graph_rbt', the build of the
 * adjacency map.  The export is handed a list of arcs and constructs its own
 * red-black tree of red-black trees from it; that construction is part of the
 * verified program and this study measures verified programs whole.  Leaving
 * it out would hide the dominant cost rather than report it: a_graph calls
 * `remdups' over the arc list and then scans the whole list once per vertex,
 * so the build is quadratic in the input where the search that follows is
 * not.  That is a property of the extracted code and it belongs in the
 * number.
 *
 * WHAT IS OUTSIDE IT.  Reading the file, and consing the arc list.  The list
 * is the export's INPUT -- the counterpart of the three plain arrays the
 * Dijkstra export took, which the parser also filled outside the clock -- so
 * it is marshalling rather than solving.  It is clocked on its own and
 * reported in build_ms, so the choice is visible rather than asserted, and a
 * reader who disagrees can add the two columns together and get the other
 * reading from the same raw rows.
 *
 * WHAT THIS EXPORT CAN ANSWER.  Reachability, and nothing more.  The
 * structure exposes `bFS_check_reachable_rbt', which runs the search and asks
 * whether the target is in the visited set.  It also exposes `bFS_dag_rbt',
 * which returns the search's parent structure -- but the tree type is
 * ABSTRACT in the exported signature and the one accessor that is exported,
 * `parent_rbt', takes a different tree type than bFS_dag_rbt returns.  So no
 * hop count can be read out of this export from outside it, and the `hops'
 * and `dist' columns are ~1 on every row rather than a number this driver
 * made up.  Cross-checking against the other solvers is on `reached'.
 *
 * NO TARGET IN THE SEARCH ITSELF.  bFS_check_reachable_rbt runs rounds until
 * the frontier is empty and only then looks the target up, so the whole
 * reachable region is settled.  Every solver in this study does the same; no
 * reference solver was given an early exit this export does not have.
 *
 * ONE PROBLEM PER PROCESS.  The source and the target are given on the command
 * line and exactly one of them is accepted: a search problem is a graph AND a
 * pair, so two pairs are two problems and must not share a solver call, a
 * solver object, or a process.  There is deliberately no way to hand this
 * driver a list of pairs.
 *
 * Node ids are handed to the export exactly as the file writes them, 1..n.
 * This export indexes nothing by id -- it keeps them in ordered trees -- so
 * there is no array to widen and no renumbering to do.
 *)

structure B = BFS_RBT

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
      ["usage: solve_sml_rbt [options] <instance.gr>",
       "",
       "  --source <v>       the source, a DIMACS node id (1-based)",
       "  --target <v>       the target, a DIMACS node id (1-based)",
       "  --query <id>       the id this pair carries in queries.csv,",
       "                     copied into the `query' column (default 0)",
       "  --repeats <k>      search the SAME problem k times and print a row",
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

      (* ---- 1. parse ---- *)
      val setupCpu = Timer.startCPUTimer ()
      val { n = nNodes, m = nArcs, fa, ta, wa = _ } = GrParser.parseFile path
      val { usr = pUsr, sys = pSys } = Timer.checkCPUTimer setupCpu
      val parseMs = msOf pUsr + msOf pSys

      (* ---- 2. the arc list ----
       * Built back-to-front with a plain accumulator so that it is one pass
       * and no reversal: the order of the arcs is not part of the problem,
       * and an export that sorts them into trees could not see the
       * difference if it were. *)
      val buildCpu = Timer.startCPUTimer ()
      val es =
        let
          fun go (i, acc) =
            if i < 0 then acc
            else go (i - 1, (Array.sub (fa, i), Array.sub (ta, i)) :: acc)
        in
          go (nArcs - 1, [])
        end
      val { usr = bUsr, sys = bSys } = Timer.checkCPUTimer buildCpu
      val buildMs = msOf bUsr + msOf bSys

      fun one rep =
        let
          (* ---- 3. clock ----
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

          (* ---- 4. the verified program, whole ---- *)
          val g = B.graph_rbt es
          val srcs = B.build_rbt_sources [s]
          val reachable = B.bFS_check_reachable_rbt g srcs t

          (* ---- 5. clock ---- *)
          val t1 = Time.now ()
          val { usr, sys } = Timer.checkCPUTimer cpu

          val usrMs = msOf usr
          val sysMs = msOf sys
          val cpuMs = usrMs + sysMs
          val wallMs = msOf (Time.- (t1, t0))

          (* ---- 6. the answer, after the clock ----
           * No hop count: see the note at the top of this file. *)
          val (status, reached) =
            if reachable then ("REACHED", 1) else ("UNREACHABLE", 0)
        in
          if #csv opts then
            print (String.concatWith ","
              [base, Int.toString nNodes, Int.toString nArcs,
               Int.toString qid, Int.toString s, Int.toString t,
               Int.toString rep, status,
               Int.toString reached, "-1", "-1",
               fmt3 cpuMs, fmt3 usrMs, fmt3 sysMs, fmt3 cpuMs, fmt3 wallMs,
               fmt3 parseMs, "0.000", fmt3 buildMs,
               #tag opts] ^ "\n")
          else
            print (String.concat
              ["query ", Int.toString qid, "  ", Int.toString s, " -> ",
               Int.toString t, "  rep ", Int.toString rep, "\n",
               "  status   ", status, "\n",
               "  hops     (not available from this export)\n",
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
