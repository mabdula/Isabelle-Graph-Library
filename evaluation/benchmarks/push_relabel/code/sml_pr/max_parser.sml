(* Reader for DIMACS maximum-flow instances.
 *
 *   c <comment>
 *   p max <nodes> <arcs>
 *   n <id> s
 *   n <id> t
 *   a <from> <to> <capacity>
 *
 * Node ids are 1..nodes and are handed to the solver exactly as they appear.
 * Renumbering them to 0-based would be setup work done outside the clock on
 * the solver's behalf, which is precisely what this study does not do; the
 * driver pays for it instead by handing the export a vertex count one larger
 * than the file's, so that index `nodes' is in range and index 0 goes unused.
 * The export marks the vertices that actually occur in the arc list, so an
 * unused index 0 costs an array slot and nothing else.
 *
 * The arcs come back as three parallel arrays in file order, which is the
 * shape the export's entry point wants: it builds both CSR directions from
 * them itself, inside the measured call.
 *
 * Parallel arcs are kept.  A max-flow instance with two arcs between the same
 * pair is not the same problem as one arc of their combined capacity -- not
 * for the answer, which is the same, but for the work, and the work is what
 * is being measured.  genrmf emits both directions between neighbours in a
 * frame, so this is not hypothetical.
 *)
structure MaxParser =
struct

  type graph = { n : int, m : int, s : int, t : int,
                 fa : int array, ta : int array, ca : int array }

  exception MaxError of string

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
          val _ = if isDigit c0 then ()
                  else raise MaxError ("expected a number in " ^ path)
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

      (* the header: skip comments, then `p max n m'.  The problem word is
       * skipped a character at a time rather than matched, exactly as the
       * shortest-path reader skips "sp". *)
      fun header () =
        let val c = skipSpace ()
        in
          if c < 0 then raise MaxError ("no problem line in " ^ path)
          else if c = 99 (* c *) then (skipLine (); header ())
          else if c = 112 (* p *) then
            let
              fun word () =
                let val c = get ()
                in if c >= 0 andalso not (isSpace c) then word () else () end
              val _ = skipSpace ()        (* first character of "max" *)
              val _ = word ()             (* the rest of it *)
              val n = readInt ()
              val m = readInt ()
            in (n, m) end
          else raise MaxError ("unexpected line in " ^ path)
        end

      val (n, m) = header ()
      val fa = Array.array (m, 0)
      val ta = Array.array (m, 0)
      val ca = Array.array (m, 0)
      val src = ref ~1
      val snk = ref ~1

      (* `n <id> s' and `n <id> t' may appear anywhere, so the designator
       * lines are read in the same pass as the arcs rather than assumed to
       * come first. *)
      fun designator () =
        let
          val v = readInt ()
          val c = skipSpace ()
        in
          if c = 115 (* s *) then src := v
          else if c = 116 (* t *) then snk := v
          else raise MaxError (path ^ ": node line is neither s nor t");
          skipLine ()
        end

      fun body i =
        let val c = skipSpace ()
        in
          if c < 0 then i
          else if c = 97 (* a *) then
            if i >= m then
              raise MaxError (path ^ ": more arcs than the header promises")
            else
              let
                val u = readInt ()
                val v = readInt ()
                val w = readInt ()
              in
                Array.update (fa, i, u);
                Array.update (ta, i, v);
                Array.update (ca, i, w);
                body (i + 1)
              end
          else if c = 110 (* n *) then (designator (); body i)
          else (skipLine (); body i)
        end

      val got = body 0
      val _ = BinIO.closeIn strm
      val _ = if got <> m then
                raise MaxError (path ^ ": header says " ^ Int.toString m
                                ^ " arcs, found " ^ Int.toString got)
              else ()
      val _ = if !src < 1 orelse !snk < 1 then
                raise MaxError (path ^ ": no source or no sink line")
              else ()
    in
      { n = n, m = m, s = !src, t = !snk, fa = fa, ta = ta, ca = ca }
    end

end
