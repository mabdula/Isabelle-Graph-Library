(* Benchmark driver for the verified Kruskal export (imperative, minimum
 * spanning tree) on DIMACS .gr instances.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .gr file into arc arrays                  (clocked, reported)
 *   2. collapse parallel edges to the cheapest             (clocked, reported)
 *   3. turn them into the export's three input arrays      (clocked, reported)
 *   4. read the clock
 *   5. call kruskal_imp_min
 *   6. read the clock again
 *   7. report the difference, plus the tree for checking
 *
 * Only step 5 sits between the two clock reads, and the whole verified
 * program is inside it: kruskal_imp_min copies the cost array into a negated
 * one, sorts the edge index array by cost (its own quicksort), initialises
 * its union-find array over the vertices and runs the Kruskal loop.  There
 * is no adjacency structure in Kruskal's algorithm and the export builds
 * none; what it builds inside the call is the sorted edge order and the
 * union-find forest, and both are measured.
 *
 * The entry point is
 *
 *     kruskal_imp_min : rat array -> (int * int) array -> int array -> int
 *                     -> (unit -> int list)
 *
 * taking the cost of every edge, the two endpoints of every edge, the array
 * of edge indices it will sort, and the vertex count; it returns the indices
 * of the edges of a minimum spanning forest.  Costs are the export's own
 * rational type, made with its rat_of_int.
 *
 * THE INPUT ARRAYS ARE BUILT OUTSIDE THE CLOCK, in build_ms.  They are the
 * parser's arrays repacked into the shape the signature asks for -- a pair
 * array instead of two arrays, rationals instead of integers, and the
 * identity index array -- and nothing more; every one of them could have
 * been filled while the file was read.  This is the same treatment the
 * functional exports' cons lists had in the BFS and DFS studies.  The edge
 * index array is sorted IN PLACE by the export, so a fresh one is built for
 * every repeat; reusing it would hand the quicksort an already sorted
 * array, which is its worst case.
 *
 * EVERY ARC IS AN UNDIRECTED EDGE, AND PARALLEL EDGES ARE COLLAPSED.  The
 * instances are the shortest-path challenge's directed files; a minimum
 * spanning tree is a problem on an undirected graph, so each arc line
 * (u, v, w) is one edge {u, v} of weight w.  The grid files carry both
 * directions of every pair with different weights and the dense files carry
 * some arcs twice; on Thomas Ammer's instruction of 2026-10-15 the parser
 * keeps the cheapest edge of every unordered pair (GrParser.collapse), so
 * the solver is handed a simple graph.  That is parsing work, outside the
 * clock, reported in dedup_ms; the `edges' column is the count after it,
 * `arcs' the file's.  Every driver in the study does the same, so all seven
 * solvers get the same edge list in the same order.
 *
 * THE ANSWER IS CHECKED AFTER THE CLOCK.  A union-find pass over the returned
 * edges confirms that no returned edge closes a cycle, and the count is
 * compared with n minus the number of connected components of the whole
 * graph, found by a second union-find pass over every arc.  Both passes are
 * the driver's, after the clock.  The tree's weight is reported so that the
 * seven solvers can be checked against each other: the weight of a minimum
 * spanning forest is a property of the graph alone.  A row whose returned
 * edges fail the check says BAD_TREE.
 *
 * The vertex count handed to the export is `nodes + 1', so that the DIMACS
 * ids 1..n index its union-find array directly; index 0 is an unused
 * singleton.  Nothing is renumbered.
 *)

structure K = Kruskal_Imp_Min

structure Driver =
struct

  fun err s = (TextIO.output (TextIO.stdErr, s ^ "\n");
               OS.Process.exit OS.Process.failure)

  val header =
    "instance,nodes,arcs,edges,repeat,status,tree_edges,tree_weight," ^
    "cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms," ^
    "parse_ms,dedup_ms,build_ms,tag"

  fun usage () =
    err (String.concatWith "\n"
      ["usage: solve_sml [options] <instance.gr>",
       "",
       "  --repeats <k>      solve the SAME instance k times and print a row",
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

  type opts = { path : string option, repeats : int, csv : bool, tag : string }

  fun parseArgs args =
    let
      fun set (path, repeats, csv, tag) =
        { path = path, repeats = repeats, csv = csv, tag = tag } : opts
      fun int v = case Int.fromString v of
                    SOME k => k
                  | NONE => err ("not an integer: " ^ v)
      fun go (a, acc : opts) =
        case a of
          [] => acc
        | "--header" :: _ => (print (header ^ "\n");
                              OS.Process.exit OS.Process.success)
        | "--csv" :: r => go (r, set (#path acc, #repeats acc, true, #tag acc))
        | "--human" :: r => go (r, set (#path acc, #repeats acc, false, #tag acc))
        | "--repeats" :: v :: r =>
            let val k = int v in
              if k < 1 then err "--repeats must be at least 1"
              else go (r, set (#path acc, k, #csv acc, #tag acc))
            end
        | "--tag" :: v :: r => go (r, set (#path acc, #repeats acc, #csv acc, v))
        | x :: r =>
            if String.isPrefix "--" x then usage ()
            else go (r, set (SOME x, #repeats acc, #csv acc, #tag acc))
    in
      go (args, { path = NONE, repeats = 1, csv = true, tag = "" })
    end

  (* ---------- the check, after the clock ----------
   * A plain union-find with path compression; the driver's own, not the
   * export's. *)

  fun find (p : int array) i =
    let val pi = Array.sub (p, i)
    in if pi = i then i
       else let val r = find p pi in Array.update (p, i, r); r end
    end

  (* the number of connected components of the whole graph *)
  fun components n fa ta =
    let
      val p = Array.tabulate (n + 1, fn i => i)
      val c = ref n
      val m = Array.length fa
      fun go i =
        if i >= m then ()
        else
          let val ru = find p (Array.sub (fa, i))
              val rv = find p (Array.sub (ta, i))
          in
            if ru <> rv then (Array.update (p, ru, rv); c := !c - 1) else ();
            go (i + 1)
          end
    in
      go 0; !c
    end

  (* ---------- main ---------- *)

  fun run () =
    let
      val opts = parseArgs (CommandLine.arguments ())
      val path = case #path opts of SOME p => p | NONE => usage ()
      val base = List.last (String.tokens (fn c => c = #"/") path)

      (* ---- 1. parse ----
       * Clocked and reported, so that what sits OUTSIDE the measurement is
       * visible rather than merely asserted. *)
      val setupCpu = Timer.startCPUTimer ()
      val parsed = GrParser.parseFile path
      val { usr = pUsr, sys = pSys } = Timer.checkCPUTimer setupCpu
      val parseMs = msOf pUsr + msOf pSys
      val nArcsFile = #m parsed
      (* ---- 2. collapse parallel edges: parsing work, outside, reported ---- *)
      val dCpu = Timer.startCPUTimer ()
      val { n = nNodes, m = nArcs, fa, ta, wa } = GrParser.collapse parsed
      val { usr = dUsr, sys = dSys } = Timer.checkCPUTimer dCpu
      val dedupMs = msOf dUsr + msOf dSys
      val n = nNodes + 1

      val comps = components nNodes fa ta

      fun one rep =
        let
          (* ---- 3. the export's input arrays, fresh for every repeat ---- *)
          val bCpu = Timer.startCPUTimer ()
          val costs = Array.tabulate (nArcs, fn i => K.rat_of_int (Array.sub (wa, i)))
          val eps = Array.tabulate (nArcs, fn i => (Array.sub (fa, i), Array.sub (ta, i)))
          val edges = Array.tabulate (nArcs, fn i => i)
          val { usr = bUsr, sys = bSys } = Timer.checkCPUTimer bCpu
          val buildMs = msOf bUsr + msOf bSys

          (* The closure is built before the first clock reading; the call
           * itself happens between the readings. *)
          val go = K.kruskal_imp_min costs eps edges n

          (* ---- 4. clock ----
           * CPU time is the measurement.  Wall time is read as well and kept
           * in the raw data, but no comparison is drawn from it: the campaign
           * runs several solvers at once, so wall time carries whatever the
           * others were doing and CPU time does not.
           *
           * `proc_ms' is the whole process rather than the one thread.  Here
           * the two are the same number, because MLton reads getrusage on a
           * process that is doing nothing else; the column exists so that the
           * JVM drivers, where they differ by the cost of the JIT, can be
           * read against these without a second shape of row. *)
          val cpu = Timer.startCPUTimer ()
          val t0 = Time.now ()

          (* ---- 5. the verified program, whole ---- *)
          val tree = go ()

          (* ---- 6. clock ---- *)
          val t1 = Time.now ()
          val { usr, sys } = Timer.checkCPUTimer cpu

          val usrMs = msOf usr
          val sysMs = msOf sys
          val cpuMs = usrMs + sysMs
          val wallMs = msOf (Time.- (t1, t0))

          (* ---- 7. the answer, after the clock ---- *)
          val p = Array.tabulate (n, fn i => i)
          fun walk ([], cnt, w, ok) = (cnt, w, ok)
            | walk (e :: es, cnt, w, ok) =
                if e < 0 orelse e >= nArcs then walk (es, cnt + 1, w, false)
                else
                  let
                    val ru = find p (Array.sub (fa, e))
                    val rv = find p (Array.sub (ta, e))
                  in
                    if ru = rv then walk (es, cnt + 1, w, false)
                    else (Array.update (p, ru, rv);
                          walk (es, cnt + 1,
                                Int64.+ (w, Int64.fromInt (Array.sub (wa, e))), ok))
                  end
          val (cnt, weight, acyclic) = walk (tree, 0, Int64.fromInt 0, true)
          val status = if acyclic andalso cnt = nNodes - comps then "SOLVED"
                       else "BAD_TREE"
        in
          if #csv opts then
            print (String.concatWith ","
              [base, Int.toString nNodes, Int.toString nArcsFile, Int.toString nArcs,
               Int.toString rep, status,
               Int.toString cnt, Int64.toString weight,
               fmt3 cpuMs, fmt3 usrMs, fmt3 sysMs, fmt3 cpuMs, fmt3 wallMs,
               fmt3 parseMs, fmt3 dedupMs, fmt3 buildMs,
               #tag opts] ^ "\n")
          else
            print (String.concat
              [base, "  rep ", Int.toString rep, "\n",
               "  status      ", status, "\n",
               "  tree edges  ", Int.toString cnt, "  (n - components = ",
               Int.toString (nNodes - comps), ")\n",
               "  tree weight ", Int64.toString weight, "\n",
               "  edges       ", Int.toString nArcs, "  (", Int.toString nArcsFile, " arcs in the file)\n",
               "  cpu         ", fmt3 cpuMs, " ms   (the measurement)\n",
               "  wall        ", fmt3 wallMs, " ms\n",
               "  build       ", fmt3 buildMs, " ms   (input arrays, outside)\n"])
        end

      fun loop r = if r > #repeats opts then () else (one r; loop (r + 1))
    in
      loop 1
    end

end

val () = Driver.run ()
