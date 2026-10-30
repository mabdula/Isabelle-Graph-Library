(* Benchmark driver for the IMPERATIVE verified BFS export (CSR arrays)
 * on DIMACS .gr instances.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .gr file into arc arrays                  (not measured)
 *   2. read the clock
 *   3. call bfs_csr_run
 *   4. read the clock again
 *   5. report the difference, plus the answer for checking
 *
 * Only step 3 sits between the two clock reads.  Building the CSR is inside
 * it, because the export does that itself and this study measures the whole
 * verified program, setup included: bfs_csr_run calls bfs_csr_build, which
 * counts the out-degrees, prefix-sums them, and fills the adjacency array,
 * and then allocates the frontier, the visited set, the distance array and
 * the parent array before a single vertex is settled.  Reading the file is
 * outside it, and so is reading the answer off afterwards.
 *
 * The entry point is
 *
 *     bfs_csr_run : int -> int array -> int array -> int array
 *                 -> (unit -> bool array * (int array * int array))
 *
 * taking the vertex count, the arc tails, the arc heads and an array of
 * sources, and returning the visited set, the distances and the parents.
 * dedup_ms and build_ms are 0.000 and that is not padding: this export takes
 * parallel arcs as they come, and it is handed the parser's own arrays with
 * no structure built on its behalf.
 *
 * NO TARGET.  bfs_csr_run settles everything reachable from the sources;
 * there is no early exit to ask for.  Every solver in this study does the
 * same, the four reference solvers included, so none of them is given a
 * shortcut this export does not have.
 *
 * WEIGHTS ARE PARSED AND THEN IGNORED.  The instances are the shortest-path
 * challenge's own, so that a BFS result and a Dijkstra result can be read
 * side by side on the same graph, but this is breadth-first search and the
 * export takes no weight array at all.
 *
 * ONE PROBLEM PER PROCESS.  The source and the target are given on the command
 * line and exactly one of them is accepted: a search problem is a graph AND a
 * pair, so two pairs are two problems and must not share a solver call, a
 * solver object, or a process.  There is deliberately no way to hand this
 * driver a list of pairs.
 *
 * THE ANSWER IS CHECKED THROUGH THE EXPORT'S OWN PATH WALKER.  Reachability
 * is read off the visited set and the hop count off the distance array, and
 * then `bfs_path' -- also part of the export -- walks the parent chain back
 * from the target and reports its length.  The two must agree and the walk
 * must end at the source, or the row says BAD_PATH.  bfs_path is called
 * AFTER the clock; it is a check, not part of the measurement.
 *
 * The vertex count handed to the export is `nodes + 2', not `nodes'.  The
 * CSR counting pass buckets an arc under index tail+2 of an (n+1)-long array,
 * guarded by tail+2 <= n, so with ids running up to `nodes' the out-arcs of
 * the two highest ids would be dropped silently.  Widening n only makes the
 * export's own arrays longer; it changes nothing else.
 *)

structure B = BFS_CSR

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
      ["usage: solve_sml_csr [options] <instance.gr>",
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

      (* Parsing is clocked and reported too, so that what sits OUTSIDE the
       * measurement is visible rather than merely asserted. *)
      val setupCpu = Timer.startCPUTimer ()
      val { n = nNodes, m = nArcs, fa, ta, wa = _ } = GrParser.parseFile path
      val { usr = pUsr, sys = pSys } = Timer.checkCPUTimer setupCpu
      val parseMs = msOf pUsr + msOf pSys
      val n = nNodes + 2

      fun one rep =
        let
          val sa = Array.fromList [s]

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

          (* ---- 3. the verified program, whole ---- *)
          val (visited, (dists, parents)) = B.bfs_csr_run n fa ta sa ()

          (* ---- 4. clock ---- *)
          val t1 = Time.now ()
          val { usr, sys } = Timer.checkCPUTimer cpu

          val usrMs = msOf usr
          val sysMs = msOf sys
          val cpuMs = usrMs + sysMs
          val wallMs = msOf (Time.- (t1, t0))

          (* ---- 5. the answer, after the clock ----
           * The distance array is initialised to the identity, not to an
           * infinity, so an unvisited vertex carries its own id there and the
           * visited set is the only sound test for reachability.  bfs_path
           * must not be called on an unvisited target: its parent is itself,
           * and the walk would not terminate. *)
          val reached = Array.sub (visited, t)
          val (status, hops) =
            if not reached then ("UNREACHABLE", 0)
            else
              let
                val d = Array.sub (dists, t)
                (* The export's own path walker, as a check on the export's
                 * own distance.  It writes the path into `ra' from the target
                 * backwards and returns how many vertices it wrote, so the
                 * hop count is one less and the last entry is the source. *)
                val ra = Array.array (n, 0)
                val k = BFS_API.path dists parents ra t ()
                val endsAtSource = k > 0 andalso Array.sub (ra, k - 1) = s
                val startsAtTarget = k > 0 andalso Array.sub (ra, 0) = t
              in
                if endsAtSource andalso startsAtTarget andalso k - 1 = d
                then ("REACHED", d)
                else ("BAD_PATH", 0)
              end
        in
          if #csv opts then
            print (String.concatWith ","
              [base, Int.toString nNodes, Int.toString nArcs,
               Int.toString qid, Int.toString s, Int.toString t,
               Int.toString rep, status,
               Int.toString (if reached then 1 else 0), Int.toString hops,
               (* in an unweighted graph the distance IS the hop count; both
                * columns are kept so a BFS row and a Dijkstra row share one
                * table shape *)
               (if reached then Int.toString hops else "-1"),
               fmt3 cpuMs, fmt3 usrMs, fmt3 sysMs, fmt3 cpuMs, fmt3 wallMs,
               fmt3 parseMs, "0.000", "0.000",
               #tag opts] ^ "\n")
          else
            print (String.concat
              ["query ", Int.toString qid, "  ", Int.toString s, " -> ",
               Int.toString t, "  rep ", Int.toString rep, "\n",
               "  status   ", status, "\n",
               "  hops     ", Int.toString hops, "\n",
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
