(* DIMACS assignment-problem (.asn) reader.
 *
 * Format (Network Flows 2.0, "Assignment Problem Definition and Format",
 * identical to the First DIMACS Challenge):
 *
 *   c <anything>            comment, may appear anywhere
 *   p asn <n> <m>           n nodes, m arcs; appears before any n/a line
 *   n <v>                   v is a vertex of X (the left side)
 *   a <v> <w> <c>           arc between v and w with cost c
 *
 * Node ids run 1..n.  Ids that appear in no `n' line belong to Y.
 * Costs fit in [-2^31, 2^31-1].
 *
 * Everything in here runs OUTSIDE the measured region: the clock is started
 * only once the arrays below have been handed to the solver.
 *)

structure AsnParser :
sig
  type instance = {
    nNodes : int,          (* n from the problem line *)
    nArcs  : int,          (* number of arcs actually read *)
    src    : int array,    (* 0-based left endpoint of arc i  *)
    dst    : int array,    (* 0-based right endpoint of arc i *)
    cost   : int array,
    left   : int array,    (* 0-based ids of X, ascending *)
    right  : int array     (* 0-based ids of Y, ascending *)
  }
  val parseFile : string -> instance
end =
struct

  type instance = {
    nNodes : int, nArcs : int,
    src : int array, dst : int array, cost : int array,
    left : int array, right : int array
  }

  fun die msg = raise Fail ("asn: " ^ msg)

  fun slurp path =
    let val f = TextIO.openIn path
    in  (TextIO.inputAll f before TextIO.closeIn f)
        handle e => (TextIO.closeIn f; raise e)
    end

  fun isSpace c = c = #" " orelse c = #"\t" orelse c = #"\r" orelse c = #"\n"

  fun parseFile path =
    let
      val s = slurp path
      val len = String.size s
      val pos = ref 0

      fun peek () = if !pos < len then SOME (String.sub (s, !pos)) else NONE

      fun skipSpace () =
        while !pos < len andalso isSpace (String.sub (s, !pos)) do pos := !pos + 1

      fun skipLine () =
        (while !pos < len andalso String.sub (s, !pos) <> #"\n" do pos := !pos + 1;
         if !pos < len then pos := !pos + 1 else ())

      (* a maximal run of non-space characters *)
      fun token () =
        (skipSpace ();
         if !pos >= len then NONE
         else
           let
             val start = !pos
           in
             while !pos < len andalso not (isSpace (String.sub (s, !pos))) do
               pos := !pos + 1;
             SOME (String.substring (s, start, !pos - start))
           end)

      fun int what =
        (skipSpace ();
         if !pos >= len then die ("unexpected end of file, wanted " ^ what)
         else
           let
             val neg = (String.sub (s, !pos) = #"-")
             val _ = if neg orelse String.sub (s, !pos) = #"+"
                     then pos := !pos + 1 else ()
             val start = !pos
             val acc = ref 0
           in
             while !pos < len
                   andalso Char.isDigit (String.sub (s, !pos)) do
               (acc := !acc * 10 + (Char.ord (String.sub (s, !pos)) - 48);
                pos := !pos + 1);
             if !pos = start then die ("expected an integer for " ^ what)
             else if neg then ~(!acc) else !acc
           end)

      (* --- pass: the problem line has to be found before sizing anything --- *)
      val nNodes = ref ~1
      val nArcsDecl = ref ~1

      val isLeft = ref (Array.fromList [] : bool array)
      val src = ref (Array.fromList [] : int array)
      val dst = ref (Array.fromList [] : int array)
      val cost = ref (Array.fromList [] : int array)
      val nArcs = ref 0

      fun ensureSized () =
        if !nNodes < 0 then die "node or arc line before the `p asn' line" else ()

      fun node () =
        let val v = int "node id"
        in
          ensureSized ();
          if v < 1 orelse v > !nNodes
          then die ("node id " ^ Int.toString v ^ " outside [1, " ^
                    Int.toString (!nNodes) ^ "]")
          else Array.update (!isLeft, v - 1, true)
        end

      (* arc arrays are grown geometrically: the count on the p line is a
       * declaration, not a guarantee, and some generators overshoot it. *)
      fun push (u, v, c) =
        let
          val cap = Array.length (!src)
          val i = !nArcs
        in
          if i >= cap
          then
            let
              val cap' = if cap = 0 then 1024 else cap * 2
              fun grow a = Array.tabulate (cap', fn j =>
                             if j < cap then Array.sub (a, j) else 0)
            in
              src := grow (!src); dst := grow (!dst); cost := grow (!cost)
            end
          else ();
          Array.update (!src, i, u);
          Array.update (!dst, i, v);
          Array.update (!cost, i, c);
          nArcs := i + 1
        end

      fun arc () =
        let
          val v = int "arc tail"
          val w = int "arc head"
          val c = int "arc cost"
        in
          ensureSized ();
          if v < 1 orelse v > !nNodes orelse w < 1 orelse w > !nNodes
          then die ("arc (" ^ Int.toString v ^ ", " ^ Int.toString w ^
                    ") outside [1, " ^ Int.toString (!nNodes) ^ "]")
          else push (v - 1, w - 1, c)
        end

      fun problem () =
        let
          val kind = case token () of
                       SOME t => t
                     | NONE => die "truncated problem line"
          val n = int "node count"
          val m = int "arc count"
        in
          if kind <> "asn"
          then die ("problem type `" ^ kind ^ "', expected `asn'")
          else if !nNodes >= 0 then die "more than one problem line"
          else
            (nNodes := n;
             nArcsDecl := m;
             isLeft := Array.array (n, false);
             src := Array.array (Int.max (m, 1), 0);
             dst := Array.array (Int.max (m, 1), 0);
             cost := Array.array (Int.max (m, 1), 0))
        end

      fun loop () =
        case token () of
          NONE => ()
        | SOME t =>
            (case t of
               "c" => (skipLine (); loop ())
             | "p" => (problem (); loop ())
             | "n" => (node (); loop ())
             | "a" => (arc (); loop ())
             | _ => die ("unknown line designator `" ^ t ^ "'"))

      val () = loop ()
      val () = if !nNodes < 0 then die "no problem line" else ()

      val n = !nNodes
      val nLeft = Array.foldl (fn (b, k) => if b then k + 1 else k) 0 (!isLeft)
      val nRight = n - nLeft

      val left = Array.array (Int.max (nLeft, 1), 0)
      val right = Array.array (Int.max (nRight, 1), 0)
      val li = ref 0
      val ri = ref 0
      val () =
        Array.appi
          (fn (v, b) =>
             if b then (Array.update (left, !li, v); li := !li + 1)
             else (Array.update (right, !ri, v); ri := !ri + 1))
          (!isLeft)

      (* trim the arc arrays to the number actually read *)
      val m = !nArcs
      fun trim a = Array.tabulate (m, fn i => Array.sub (a, i))

      (* The solver's CSR is keyed on the first endpoint and holds each arc in
       * one direction only, so src must be the X-side vertex.  Generators emit
       * arcs that way, but the format does not require the `n' lines to come
       * first, so orient here rather than trust the file. *)
      val () =
        let
          val lo = !isLeft
        in
          Array.appi
            (fn (i, u) =>
               let val v = Array.sub (!dst, i) in
                 if Array.sub (lo, u) andalso not (Array.sub (lo, v)) then ()
                 else if Array.sub (lo, v) andalso not (Array.sub (lo, u))
                 then (Array.update (!src, i, v); Array.update (!dst, i, u))
                 else die ("arc (" ^ Int.toString (u + 1) ^ ", " ^
                           Int.toString (v + 1) ^ ") is not between X and Y")
               end)
            (Array.tabulate (m, fn i => Array.sub (!src, i)))
        end
    in
      { nNodes = n, nArcs = m,
        src = trim (!src), dst = trim (!dst), cost = trim (!cost),
        left = Array.tabulate (nLeft, fn i => Array.sub (left, i)),
        right = Array.tabulate (nRight, fn i => Array.sub (right, i)) }
    end

end
