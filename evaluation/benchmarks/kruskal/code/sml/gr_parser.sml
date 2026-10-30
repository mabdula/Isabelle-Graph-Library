(* Reader for DIMACS shortest-path .gr files.
 *
 *   c <comment>
 *   p sp <nodes> <arcs>
 *   a <from> <to> <weight>
 *
 * Node ids are 1..nodes and are handed to the solver exactly as they appear:
 * renumbering them to 0-based would be setup work done outside the clock on
 * the solver's behalf, which is precisely what this study does not do.
 *
 * The arcs are returned as three parallel arrays in file order.  This study
 * is Kruskal's minimum spanning tree, so the weight array is read: every arc
 * line is one undirected edge of that weight.  PARALLEL EDGES ARE THEN
 * COLLAPSED by `collapse' below, on Thomas Ammer's instruction of 2026-10-15:
 * every unordered pair {u, v} keeps its cheapest arc, so the solver is handed
 * a simple graph.  The grid files carry both directions of every pair, the
 * dense files repeat some arcs; after the collapse each pair is one edge.
 * The collapse is part of parsing, outside the clock, and the driver reports
 * its time in dedup_ms.  The driver then turns the arrays into the export's
 * input arrays; that step is reported in build_ms.
 *)
structure GrParser =
struct

  type graph = { n : int, m : int,
                 fa : int array, ta : int array, wa : int array }

  exception GrError of string

  val BUFSZ = 4 * 1024 * 1024

  fun parseFile path =
    let
      val strm = BinIO.openIn path
      val buf = ref (Word8Vector.fromList [])
      val pos = ref 0
      val len = ref 0

      fun refill () =
        let
          val v = BinIO.inputN (strm, BUFSZ)
        in
          buf := v; pos := 0; len := Word8Vector.length v; !len > 0
        end

      (* ~1 at end of file *)
      fun get () =
        if !pos < !len then
          let val c = Word8.toInt (Word8Vector.sub (!buf, !pos))
          in pos := !pos + 1; c end
        else if refill () then
          (pos := 1; Word8.toInt (Word8Vector.sub (!buf, 0)))
        else ~1

      fun unget () = pos := !pos - 1

      fun isDigit c = c >= 48 andalso c <= 57
      fun isSpace c = c = 32 orelse c = 9 orelse c = 13 orelse c = 10

      fun skipSpace () =
        let val c = get ()
        in if c >= 0 andalso isSpace c then skipSpace () else c end

      (* a non-negative integer; raises at end of file *)
      fun readInt () =
        let
          val c0 = skipSpace ()
          val _ = if isDigit c0 then () else raise GrError ("expected a number in " ^ path)
          fun go acc =
            let val c = get ()
            in if isDigit c then go (acc * 10 + (c - 48))
               else (if c >= 0 then unget () else (); acc)
            end
        in
          go (c0 - 48)
        end

      fun skipLine () =
        let val c = get ()
        in if c < 0 orelse c = 10 then () else skipLine () end

      (* the header: skip comments, then 'p sp n m' *)
      fun header () =
        let val c = skipSpace ()
        in
          if c < 0 then raise GrError ("no problem line in " ^ path)
          else if c = 99 (* c *) then (skipLine (); header ())
          else if c = 112 (* p *) then
            let
              val _ = skipSpace ()        (* 's' of "sp" *)
              val _ = get ()              (* 'p' of "sp" *)
              val n = readInt ()
              val m = readInt ()
            in (n, m) end
          else raise GrError ("unexpected line in " ^ path)
        end

      val (n, m) = header ()
      val fa = Array.array (m, 0)
      val ta = Array.array (m, 0)
      val wa = Array.array (m, 0)

      fun arcs i =
        if i >= m then i
        else
          let val c = skipSpace ()
          in
            if c < 0 then i
            else if c = 97 (* a *) then
              let
                val u = readInt ()
                val v = readInt ()
                val w = readInt ()
              in
                Array.update (fa, i, u);
                Array.update (ta, i, v);
                Array.update (wa, i, w);
                arcs (i + 1)
              end
            else (skipLine (); arcs i)
          end

      val got = arcs 0
      val _ = BinIO.closeIn strm
      val _ = if got <> m then
                raise GrError (path ^ ": header says " ^ Int.toString m
                               ^ " arcs, found " ^ Int.toString got)
              else ()
    in
      { n = n, m = m, fa = fa, ta = ta, wa = wa }
    end


  (* Collapse parallel edges: every unordered pair {u, v} keeps its cheapest
   * arc.  Two stable counting sorts of the edge indices, by the larger
   * endpoint and then by the smaller, put equal pairs side by side in
   * (lo, hi) order; one scan keeps the minimum weight of each run.  Linear
   * in n + m.  The result lists each edge once as (lo, hi, w), sorted by
   * (lo, hi); self-loops, if any, are kept as they are. *)
  fun collapse { n, m, fa, ta, wa } =
    let
      val lo = Array.tabulate (m, fn i => Int.min (Array.sub (fa, i), Array.sub (ta, i)))
      val hi = Array.tabulate (m, fn i => Int.max (Array.sub (fa, i), Array.sub (ta, i)))
      (* stable counting sort of the index array `src' by `key' (0 .. n) *)
      fun csort (key, src) =
        let
          val cnt = Array.array (n + 2, 0)
          val _ = Array.app (fn i => let val k = Array.sub (key, i) + 1
                                     in Array.update (cnt, k, Array.sub (cnt, k) + 1) end) src
          fun prefix k = if k > n + 1 then ()
                         else (Array.update (cnt, k, Array.sub (cnt, k) + Array.sub (cnt, k - 1));
                               prefix (k + 1))
          val _ = prefix 1
          val out = Array.array (m, 0)
          val _ = Array.app (fn i => let val k = Array.sub (key, i)
                                         val p = Array.sub (cnt, k)
                                     in Array.update (out, p, i); Array.update (cnt, k, p + 1) end) src
        in out end
      val order = csort (lo, csort (hi, Array.tabulate (m, fn i => i)))
      val fa' = Array.array (m, 0)
      val ta' = Array.array (m, 0)
      val wa' = Array.array (m, 0)
      fun scan (k, d) =
        if k >= m then d
        else
          let
            val i = Array.sub (order, k)
            val (l, h, w) = (Array.sub (lo, i), Array.sub (hi, i), Array.sub (wa, i))
          in
            if d > 0 andalso Array.sub (fa', d - 1) = l andalso Array.sub (ta', d - 1) = h
            then (if w < Array.sub (wa', d - 1) then Array.update (wa', d - 1, w) else ();
                  scan (k + 1, d))
            else (Array.update (fa', d, l); Array.update (ta', d, h); Array.update (wa', d, w);
                  scan (k + 1, d + 1))
          end
      val d = scan (0, 0)
    in
      { n = n, m = d,
        fa = Array.tabulate (d, fn i => Array.sub (fa', i)),
        ta = Array.tabulate (d, fn i => Array.sub (ta', i)),
        wa = Array.tabulate (d, fn i => Array.sub (wa', i)) }
    end

end
