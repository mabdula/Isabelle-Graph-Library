(* Benchmark driver for the ADJACENCY-LIST verified DFS export on DIMACS .gr
 * instances.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .gr file into arc arrays                  (clocked, reported)
 *   2. read the clock
 *   3. call dfs_input_arrays_run
 *   4. read the clock again
 *   5. report the difference
 *
 * Only step 3 sits between the two clock reads.  Building the adjacency
 * structure is inside it, because the export does that itself and this study
 * measures the whole verified program, setup included: dfs_input_arrays_run
 * calls from_arrays_impl, which walks the arc arrays and inserts each arc into
 * a growable array of lists, and that is the dominant cost on everything but
 * the sparsest instances -- add_edge scans the tail's whole list to keep it
 * duplicate-free, so the build is quadratic in the out-degree where the
 * search that follows is not.  That is a property of the extracted code and
 * it belongs in the number.  Reading the file is outside it.
 *
 * The entry point is
 *
 *     dfs_input_arrays_run : int array -> int array -> int -> int
 *                          -> (unit -> (int, bool array, unit) dFS_state_ext)
 *
 * taking the arc tails, the arc heads, the source and the target.  It takes
 * no vertex count: the array of lists grows as ids arrive.
 *
 * THE TARGET IS NOT IN THE GRAPH, AND THAT IS THE POINT.  This export is a
 * reachability search: it stops the moment the top of its stack equals the
 * target.  This study measures a FULL graph search, so every run is given
 * target 0, which no DIMACS file ever names -- ids run 1..n -- and the search
 * therefore runs until its stack is empty, visiting everything reachable from
 * the source.  The driver REFUSES a target inside [1, n], so a real target
 * cannot be passed by accident.
 *
 * NOTHING CAN BE READ OFF AFTERWARDS.  The exported signature makes
 * `dFS_state_ext' abstract and exports no accessor for any of its fields, so
 * neither the verdict nor the seen set can be inspected from outside the
 * structure.  Both answer columns are therefore -1 rather than a number this
 * driver made up, and `status' says RAN: the run completed.  The CSR export
 * next door hands back its stack and so can say more; this one hands back
 * only the opaque record.  What a finished run proves is the time it took.
 *
 * The returned state is stored in a ref that is read after the clock, so that
 * the whole-program optimiser cannot decide the call's result is unused and
 * delete the search.
 *
 * WEIGHTS ARE PARSED AND THEN IGNORED.  The instances are the shortest-path
 * challenge's own, so that a DFS row, a BFS row and a Dijkstra row can be
 * read side by side on the same graph, but this export takes no weight array.
 *
 * ONE PROBLEM PER PROCESS.  The source is given on the command line and
 * exactly one is accepted: a search problem is a graph AND a source, so two
 * sources are two problems and must not share a solver call or a process.
 *
 * Node ids are handed to the export exactly as the file writes them, 1..n.
 *)

structure D = DFS_Lists

structure Driver =
struct

  fun err s = (TextIO.output (TextIO.stdErr, s ^ "\n");
               OS.Process.exit OS.Process.failure)

  val header =
    "instance,nodes,arcs,query,source,target,repeat,status," ^
    "reached,visited,cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms," ^
    "parse_ms,dedup_ms,build_ms,tag"

  (* The search's result, kept alive past the clock.  See the note above. *)
  val sink : (int, (bool array), unit) D.dFS_state_ext option ref = ref NONE

  fun usage () =
    err (String.concatWith "\n"
      ["usage: solve_sml_lists [options] <instance.gr>",
       "",
       "  --source <v>       the source, a DIMACS node id (1-based)",
       "  --target <v>       the target.  It must NOT be a node of the graph;",
       "                     the campaign passes 0.",
       "  --query <id>       the id this source carries in queries.csv",
       "  --repeats <k>      search the SAME problem k times, one row each",
       "  --header           print the CSV header line and exit",
       "  --csv              print one CSV row per query and repeat (default)",
       "  --human            print a human-readable block instead",
       "  --tag <s>          free-form label copied into the `tag' column",
       ""])

  fun msOf t = Time.toReal t * 1000.0
  fun fmt3 r = Real.fmt (StringCvt.FIX (SOME 3)) r

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

      val setupCpu = Timer.startCPUTimer ()
      val { n = nNodes, m = nArcs, fa, ta, wa = _ } = GrParser.parseFile path
      val { usr = pUsr, sys = pSys } = Timer.checkCPUTimer setupCpu
      val parseMs = msOf pUsr + msOf pSys

      fun one rep =
        let
          (* ---- 2. clock ---- *)
          val cpu = Timer.startCPUTimer ()
          val t0 = Time.now ()

          (* ---- 3. the verified program, whole ---- *)
          val st = D.dfs_input_arrays_run fa ta s t ()

          (* ---- 4. clock ---- *)
          val t1 = Time.now ()
          val { usr, sys } = Timer.checkCPUTimer cpu

          val () = sink := SOME st
          val usrMs = msOf usr
          val sysMs = msOf sys
          val cpuMs = usrMs + sysMs
          val wallMs = msOf (Time.- (t1, t0))

          (* ---- 5. after the clock ----
           * Reading the ref keeps the search from being optimised away; the
           * state itself is abstract and says nothing. *)
          val status = case !sink of NONE => "NO_RESULT" | SOME _ => "RAN"
        in
          if #csv opts then
            print (String.concatWith ","
              [base, Int.toString nNodes, Int.toString nArcs,
               Int.toString qid, Int.toString s, Int.toString t,
               Int.toString rep, status, "-1", "-1",
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
