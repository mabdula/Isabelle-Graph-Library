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
 * The arcs are returned as three parallel arrays in file order.  The weight
 * array is filled and then never read: this study is breadth-first search and
 * ignores every weight.  The instances are the shortest-path challenge's own,
 * so that a BFS result and a Dijkstra result can be read side by side on the
 * same graph, and parsing the third field costs nothing to keep.
 *
 * Neither BFS entry point takes arrays, though.  Both want the arcs as a LIST
 * of (tail, head) pairs, so a driver turns these arrays into one; that step is
 * clocked on its own and reported in build_ms, exactly as the reference
 * solvers' structure builds are.
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

end
