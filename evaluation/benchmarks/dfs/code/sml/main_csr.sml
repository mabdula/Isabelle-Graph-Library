(* Benchmark driver for the CSR verified DFS export on DIMACS .gr instances.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .gr file into arc arrays                  (clocked, reported)
 *   2. read the clock
 *   3. call dfs_edges_run
 *   4. read the clock again
 *   5. report the difference, plus what can be read of the answer
 *
 * Only step 3 sits between the two clock reads.  Building the CSR is inside
 * it, because the export does that itself and this study measures the whole
 * verified program, setup included: dfs_edges_run calls csr_build_heads,
 * which counts the out-degrees, prefix-sums them and fills the adjacency
 * array, and then allocates the cursor array, the stack and the seen array
 * before a single vertex is visited.  Reading the file is outside it.
 *
 * The entry point is
 *
 *     dfs_edges_run : int -> int array -> int array -> int -> int
 *                   -> (unit -> return * (int array * int ref))
 *
 * taking the vertex count, the arc tails, the arc heads, the source and the
 * target, and returning its verdict and its stack.
 *
 * THE TARGET IS NOT IN THE GRAPH, AND THAT IS THE POINT.  This export is a
 * reachability search: it stops the moment the top of its stack equals the
 * target.  This study measures a FULL graph search, so every run is given
 * target 0, which no DIMACS file ever names -- ids run 1..n -- and the search
 * therefore runs until its stack is empty, visiting everything reachable from
 * the source.  The driver REFUSES a target inside [1, n], so a real target
 * cannot be passed by accident.  Every reference solver in this study sweeps
 * the whole reachable region too; see drivers/cpp/solve_lemon_dfs.cc.
 *
 * WHAT CAN BE READ OFF AFTERWARDS.  The exported signature makes `return'
 * abstract and exports no accessor for it, so the verdict itself cannot be
 * inspected from outside the structure.  What it does hand back is the
 * export's own stack, and that settles the same question: a search that ran
 * to exhaustion leaves the stack empty, and one that stopped early leaves the
 * target on top.  So `reached' is read off the stack's size -- 0 entries
 * means the sweep completed -- and the row says BAD_TARGET if a stack comes
 * back non-empty, which would mean the export had found a vertex the file
 * does not contain.  `visited' is -1: the seen array stays inside the state
 * record and no accessor for it is exported.
 *
 * WEIGHTS ARE PARSED AND THEN IGNORED.  The instances are the shortest-path
 * challenge's own, so that a DFS row, a BFS row and a Dijkstra row can be
 * read side by side on the same graph, but this export takes no weight array.
 *
 * ONE PROBLEM PER PROCESS.  The source is given on the command line and
 * exactly one is accepted: a search problem is a graph AND a source, so two
 * sources are two problems and must not share a solver call or a process.
 * There is deliberately no way to hand this driver a list of sources.
 *
 * The vertex count handed to the export is `nodes + 2', not `nodes'.  The
 * CSR counting pass buckets an arc under index tail+2 of an (n+1)-long array,
 * guarded by tail+2 <= n, so with ids running up to `nodes' the out-arcs of
 * the two highest ids would be dropped silently.  Widening n only makes the
 * export's own arrays longer; it changes nothing else.
 *)

structure D = DFS_CSR

structure Driver =
struct

  fun err s = (TextIO.output (TextIO.stdErr, s ^ "\n");
               OS.Process.exit OS.Process.failure)

  val header =
    "instance,nodes,arcs,query,source,target,repeat,status," ^
    "reached,visited,cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms," ^
    "parse_ms,dedup_ms,build_ms,tag"

  fun usage () =
    err (String.concatWith "\n"
      ["usage: solve_sml_csr [options] <instance.gr>",
       "",
       "  --source <v>       the source, a DIMACS node id (1-based)",
       "  --target <v>       the target.  It must NOT be a node of the graph;",
       "                     the campaign passes 0.  See the note at the head",
       "                     of this file.",
       "  --query <id>       the id this source carries in queries.csv,",
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
          val (_, (_, depth)) = D.dfs_edges_run n fa ta s t ()

          (* ---- 4. clock ---- *)
          val t1 = Time.now ()
          val { usr, sys } = Timer.checkCPUTimer cpu

          val usrMs = msOf usr
          val sysMs = msOf sys
          val cpuMs = usrMs + sysMs
          val wallMs = msOf (Time.- (t1, t0))

          (* ---- 5. the answer, after the clock ----
           * An empty stack is a sweep that ran to exhaustion.  A non-empty
           * one would mean the export stopped on a vertex equal to a target
           * the graph does not contain, which cannot happen and would be a
           * fault worth seeing rather than averaging. *)
          val left = !depth
          val status = if left = 0 then "OK" else "BAD_TARGET"
        in
          if #csv opts then
            print (String.concatWith ","
              [base, Int.toString nNodes, Int.toString nArcs,
               Int.toString qid, Int.toString s, Int.toString t,
               Int.toString rep, status,
               (if left = 0 then "0" else "1"), "-1",
               fmt3 cpuMs, fmt3 usrMs, fmt3 sysMs, fmt3 cpuMs, fmt3 wallMs,
               fmt3 parseMs, "0.000", "0.000",
               #tag opts] ^ "\n")
          else
            print (String.concat
              ["query ", Int.toString qid, "  source ", Int.toString s,
               "  rep ", Int.toString rep, "\n",
               "  status   ", status, "\n",
               "  visited  (not available from this export)\n",
               "  cpu      ", fmt3 cpuMs, " ms   (the measurement)\n",
               "  wall     ", fmt3 wallMs, " ms\n"])
        end

      fun go r = if r > #repeats opts then () else (one r; go (r + 1))
    in
      if s < 1 orelse s > nNodes then
        err ("query " ^ Int.toString qid ^ ": source " ^ Int.toString s ^
             " outside [1, " ^ Int.toString nNodes ^ "]")
      else ();
      if t >= 1 andalso t <= nNodes then
        err ("query " ^ Int.toString qid ^ ": target " ^ Int.toString t ^
             " IS a node of this graph; this study searches the whole graph " ^
             "and needs a target outside [1, " ^ Int.toString nNodes ^ "]")
      else ();
      go 1
    end

end

val () = Driver.run ()
