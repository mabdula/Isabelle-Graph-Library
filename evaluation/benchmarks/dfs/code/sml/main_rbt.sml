(* Benchmark driver for the RED-BLACK-TREE verified DFS export on DIMACS .gr
 * instances.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .gr file into arc arrays                  (clocked, reported)
 *   2. turn those arrays into the (tail, head) LIST the
 *      export's entry point takes                          (clocked, reported)
 *   3. read the clock
 *   4. call rbt_from_list, rbt_dfs_initial_state and rbt_dfs_impl
 *   5. read the clock again
 *   6. report the difference
 *
 * WHAT IS INSIDE THE CLOCK.  Steps 3 to 5, which is everything the verified
 * code does -- and that deliberately includes `rbt_from_list', the build of
 * the adjacency map.  The export is handed a list of arcs and constructs its
 * own red-black tree of red-black trees from it; that construction is part of
 * the verified program and this study measures verified programs whole.
 * Leaving it out would hide the dominant cost rather than report it.
 *
 * WHAT IS OUTSIDE IT.  Reading the file, and consing the arc list.  The list
 * is the export's INPUT -- the counterpart of the plain arrays the other two
 * exports take, which the parser also fills outside the clock -- so it is
 * marshalling rather than solving.  It is clocked on its own and reported in
 * build_ms, so the choice is visible rather than asserted, and a reader who
 * disagrees can add the two columns together and get the other reading from
 * the same raw rows.
 *
 * The entry points are
 *
 *     rbt_from_list          : (int * int) list -> graph
 *     rbt_dfs_initial_state  : int -> state
 *     rbt_dfs_impl           : graph -> int -> state -> state
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
 * neither the verdict nor the seen tree can be inspected from outside the
 * structure.  Both answer columns are therefore -1 rather than a number this
 * driver made up, and `status' says RAN: the run completed.
 *
 * The returned state is stored in a ref that is read after the clock, so that
 * the whole-program optimiser cannot decide the call's result is unused and
 * delete the search.  That matters more here than for the other two exports:
 * this one is purely functional and allocates rather than mutating, so there
 * is no side effect to keep it alive by itself.
 *
 * Node ids are handed to the export exactly as the file writes them, 1..n.
 * This export indexes nothing by id -- it keeps them in ordered trees -- so
 * there is no array to widen and no renumbering to do.
 *)

structure D = DFS_RBT

structure Driver =
struct

  fun err s = (TextIO.output (TextIO.stdErr, s ^ "\n");
               OS.Process.exit OS.Process.failure)

  val header =
    "instance,nodes,arcs,query,source,target,repeat,status," ^
    "reached,visited,cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms," ^
    "parse_ms,dedup_ms,build_ms,tag"

  (* The search's result, kept alive past the clock.  See the note above. *)
  val sink : (int, ((int * D.color) D.tree), unit) D.dFS_state_ext option ref =
    ref NONE

  fun usage () =
    err (String.concatWith "\n"
      ["usage: solve_sml_rbt [options] <instance.gr>",
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

      (* ---- 1. parse ---- *)
      val setupCpu = Timer.startCPUTimer ()
      val { n = nNodes, m = nArcs, fa, ta, wa = _ } = GrParser.parseFile path
      val { usr = pUsr, sys = pSys } = Timer.checkCPUTimer setupCpu
      val parseMs = msOf pUsr + msOf pSys

      (* ---- 2. the arc list ----
       * Built back-to-front with a plain accumulator so that it is one pass
       * and no reversal: the order of the arcs is not part of the problem. *)
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
          (* ---- 3. clock ---- *)
          val cpu = Timer.startCPUTimer ()
          val t0 = Time.now ()

          (* ---- 4. the verified program, whole ---- *)
          val g = D.rbt_from_list es
          val st0 = D.rbt_dfs_initial_state s
          val st = D.rbt_dfs_impl g t st0

          (* ---- 5. clock ---- *)
          val t1 = Time.now ()
          val { usr, sys } = Timer.checkCPUTimer cpu

          val () = sink := SOME st
          val usrMs = msOf usr
          val sysMs = msOf sys
          val cpuMs = usrMs + sysMs
          val wallMs = msOf (Time.- (t1, t0))

          (* ---- 6. after the clock ---- *)
          val status = case !sink of NONE => "NO_RESULT" | SOME _ => "RAN"
        in
          if #csv opts then
            print (String.concatWith ","
              [base, Int.toString nNodes, Int.toString nArcs,
               Int.toString qid, Int.toString s, Int.toString t,
               Int.toString rep, status, "-1", "-1",
               fmt3 cpuMs, fmt3 usrMs, fmt3 sysMs, fmt3 cpuMs, fmt3 wallMs,
               fmt3 parseMs, "0.000", fmt3 buildMs,
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
