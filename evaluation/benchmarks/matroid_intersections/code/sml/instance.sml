(* The instance reader, shared by the four problems.
 *
 * It reads the format of asn_reader.py (competitors/*/code/) and applies the same
 * checks, so that every solver in the study rejects the same files and builds
 * the same arrays from the ones it accepts. Nothing here is on the clock: the
 * clock covers the call into the generated code alone.
 *
 *   c <comment>
 *   p asn <nodes> <arcs>        ("p bmatch ..." is accepted as well)
 *   n <id> [<cap>]              capacity of vertex <id>, default 1
 *   a <u> <v> [<w>]             edge {u, v}, u on the left, v on the right
 *
 * Vertex ids run 1..<nodes>. The sides come from the arcs: tails are left,
 * heads are right. A vertex on both sides is an error, and so is a repeated
 * edge -- the verified code requires simple graphs.
 *
 * The file is scanned twice: once to count the arcs and once to fill the
 * arrays. The problem line states the arc count, but it is not trusted for
 * anything but a sanity check, and counting is cheaper than growing arrays.
 *)
structure Instance :
sig
  exception Bad of string

  (* fa, ta and wa are indexed by edge; ka by vertex.
   *
   * ka has length nodes+1, not nodes. Vertex ids are 1-based and the generated
   * code indexes its per-vertex arrays by the id directly, so slot 0 exists
   * and is never used. Its length is also what the b-matching entry points
   * take as the vertex count -- they have no nv argument. The Sage baselines
   * build the same nb = nodes + 1. *)
  type t = { nodes : int, fa : int array, ta : int array,
             wa : int array, ka : int array }

  (* read path capacities: without capacities every capacity must be 1,
   * exactly as the Sage baselines insist, because a capacitated file is not a
   * matching instance. *)
  val read : string * bool -> t
  val nv : t -> int
  val objective : t * bool array -> int * int
  val checkIndependent : t * bool array -> unit
end =
struct

exception Bad of string

type t = { nodes : int, fa : int array, ta : int array,
           wa : int array, ka : int array }

fun nv ({ka, ...} : t) = Array.length ka

fun isSpace c = c = #" " orelse c = #"\t" orelse c = #"\r"

(* The first non-space index at or after p, bounded by e. *)
fun skipSpace (s, p, e) =
  if p < e andalso isSpace (String.sub (s, p)) then skipSpace (s, p + 1, e) else p

(* Past the token starting at p. *)
fun skipTok (s, p, e) =
  let val i = skipSpace (s, p, e)
      fun go j = if j < e andalso not (isSpace (String.sub (s, j))) then go (j + 1) else j
  in go i end

(* The integer at or after p: SOME (value, next index), or NONE at end of line. *)
fun scanInt (s, p, e) =
  let
    val i = skipSpace (s, p, e)
  in
    if i >= e then NONE
    else
      let
        val (neg, j) =
          case String.sub (s, i) of
              #"-" => (true, i + 1)
            | #"+" => (false, i + 1)
            | _    => (false, i)
        fun go (k, acc, any) =
          if k < e then
            let val c = String.sub (s, k) in
              if c >= #"0" andalso c <= #"9"
              then go (k + 1, acc * 10 + (Char.ord c - 48), true)
              else (k, acc, any)
            end
          else (k, acc, any)
        val (k, v, any) = go (j, 0, false)
      in
        if any then SOME (if neg then ~v else v, k) else NONE
      end
  end

(* One pass over the file. onNodes fires on the problem line, onCap on each n
 * line, onArc on each arc line; everything else is a comment or an error. *)
fun scan (s, onNodes, onCap, onArc) =
  let
    val n = String.size s
    fun need (what, lineno, x) =
      case x of SOME v => v
              | NONE => raise Bad ("line " ^ Int.toString lineno ^ ": malformed " ^ what ^ " line")
    fun lineEnd i = if i < n andalso String.sub (s, i) <> #"\n" then lineEnd (i + 1) else i
    fun loop (i, lineno) =
      if i >= n then ()
      else
        let
          val e = lineEnd i
          val k = skipSpace (s, i, e)
        in
          if k >= e then ()
          else
            case String.sub (s, k) of
                #"c" => ()
              | #"p" =>
                  let val p = skipTok (s, k, e)                  (* the kind word *)
                      val p = skipTok (s, p, e)                  (* "asn" or "bmatch" *)
                      val (nodes, p) = need ("problem", lineno, scanInt (s, p, e))
                      val arcs = case scanInt (s, p, e) of SOME (a, _) => a | NONE => 0
                  in onNodes (nodes, arcs, lineno) end
              | #"n" =>
                  let val p = skipTok (s, k, e)
                      val (id, p) = need ("n", lineno, scanInt (s, p, e))
                      val cap = case scanInt (s, p, e) of SOME (c, _) => c | NONE => 1
                  in onCap (id, cap, lineno) end
              | #"a" =>
                  let val p = skipTok (s, k, e)
                      val (u, p) = need ("arc", lineno, scanInt (s, p, e))
                      val (v, p) = need ("arc", lineno, scanInt (s, p, e))
                      val w = case scanInt (s, p, e) of SOME (x, _) => x | NONE => 1
                  in onArc (u, v, w, lineno) end
              | c => raise Bad ("line " ^ Int.toString lineno
                                ^ ": unknown line type " ^ Char.toString c);
          loop (e + 1, lineno + 1)
        end
  in loop (0, 1) end

fun slurp path =
  let val f = TextIO.openIn path
  in (TextIO.inputAll f before TextIO.closeIn f)
     handle e => (TextIO.closeIn f; raise e)
  end

(* No edge twice, in one pass over a neighbour list rather than by sorting or
 * hashing: bucket the edges by left endpoint, then walk each left vertex
 * stamping the right endpoints it has already been seen with. The dense
 * instances have millions of edges and this is off the clock, but it is not
 * off the memory budget. *)
fun checkSimple (nodes, fa, ta) =
  let
    val m = Array.length fa
    val start = Array.array (nodes + 2, 0)
    fun count e = if e >= m then () else
                    (Array.update (start, Array.sub (fa, e) + 1,
                                   Array.sub (start, Array.sub (fa, e) + 1) + 1);
                     count (e + 1))
    val () = count 0
    fun prefix x = if x > nodes + 1 then () else
                     (Array.update (start, x, Array.sub (start, x) + Array.sub (start, x - 1));
                      prefix (x + 1))
    val () = prefix 1
    val fill = Array.tabulate (nodes + 2, fn x => Array.sub (start, x))
    val nbr = Array.array (if m = 0 then 1 else m, 0)
    fun place e = if e >= m then () else
                    let val u = Array.sub (fa, e) in
                      Array.update (nbr, Array.sub (fill, u), Array.sub (ta, e));
                      Array.update (fill, u, Array.sub (fill, u) + 1);
                      place (e + 1)
                    end
    val () = place 0
    (* 0 is not a vertex id, so it means "unseen". *)
    val stamp = Array.array (nodes + 1, 0)
    fun walk u =
      if u > nodes then ()
      else
        let fun go k =
              if k >= Array.sub (start, u + 1) then ()
              else
                let val v = Array.sub (nbr, k) in
                  if Array.sub (stamp, v) = u
                  then raise Bad ("duplicate edge " ^ Int.toString u ^ " " ^ Int.toString v)
                  else (Array.update (stamp, v, u); go (k + 1))
                end
        in go (Array.sub (start, u)); walk (u + 1) end
  in walk 1 end

fun read (path, capacities) =
  let
    val s = slurp path

    (* Pass one: the problem line and the arc count. *)
    val nodes = ref ~1
    val count = ref 0
    val stated = ref 0
    fun setNodes (v, arcs, lineno) =
      if !nodes >= 0 then raise Bad ("line " ^ Int.toString lineno ^ ": second problem line")
      else (nodes := v; stated := arcs)
    val () = scan (s, setNodes, fn _ => (), fn _ => count := !count + 1)
    val nodes = !nodes
    val () = if nodes < 0 then raise Bad "missing problem line" else ()
    val m = !count

    (* Pass two: fill. *)
    val fa = Array.array (if m = 0 then 1 else m, 0)
    val ta = Array.array (if m = 0 then 1 else m, 0)
    val wa = Array.array (if m = 0 then 1 else m, 0)
    val ka = Array.array (nodes + 1, 1)
    val capOf = Array.array (nodes + 1, false)
    val at = ref 0
    fun inRange (x, lineno) =
      if x < 1 orelse x > nodes
      then raise Bad ("vertex " ^ Int.toString x ^ " outside 1.." ^ Int.toString nodes)
      else x
    fun putCap (id, c, lineno) =
      let val id = inRange (id, lineno) in
        if c < 0 then raise Bad ("negative capacity at vertex " ^ Int.toString id)
        else (Array.update (ka, id, c); Array.update (capOf, id, true))
      end
    fun putArc (u, v, w, lineno) =
      let val u = inRange (u, lineno)
          val v = inRange (v, lineno)
          val e = !at
      in Array.update (fa, e, u); Array.update (ta, e, v); Array.update (wa, e, w);
         at := e + 1
      end
    val () = scan (s, fn _ => (), putCap, putArc)

    (* The two sides disjoint. *)
    val left = Array.array (nodes + 1, false)
    val right = Array.array (nodes + 1, false)
    fun sides e = if e >= m then () else
                    (Array.update (left, Array.sub (fa, e), true);
                     Array.update (right, Array.sub (ta, e), true);
                     sides (e + 1))
    val () = sides 0
    fun bothSides x =
      if x > nodes then ()
      else if Array.sub (left, x) andalso Array.sub (right, x)
      then raise Bad ("vertex " ^ Int.toString x ^ " is on both sides")
      else bothSides (x + 1)
    val () = bothSides 1

    val () = checkSimple (nodes, fa, ta)

    val () =
      if capacities then ()
      else
        let fun go x = if x > nodes then ()
                       else if Array.sub (capOf, x) andalso Array.sub (ka, x) <> 1
                       then raise Bad "capacities other than 1 in a matching instance"
                       else go (x + 1)
        in go 1 end
  in
    { nodes = nodes, fa = fa, ta = ta, wa = wa, ka = ka }
  end

(* The answer read off the returned Boolean array: how many edges it holds and
 * what they weigh. Off the clock for every solver. *)
fun objective ({wa, ...} : t, sol) =
  let
    val m = Array.length sol
    fun go (e, card, weight) =
      if e >= m then (card, weight)
      else if Array.sub (sol, e)
      then go (e + 1, card + 1, weight + Array.sub (wa, e))
      else go (e + 1, card, weight)
  in go (0, 0, 0) end

(* The answer must be a common independent set of the two partition matroids:
 * no vertex, on either side, carries more edges than its capacity. The Sage
 * baselines make the same check on their own answers. It is cheap, off the
 * clock, and it catches a wrong answer at the run that produced it rather than
 * at the comparison months later. *)
fun checkIndependent ({nodes, fa, ta, ka, ...} : t, sol) =
  let
    val m = Array.length sol
    val cnt = Array.array (nodes + 1, 0)
    fun tally (side, e) =
      if e >= m then ()
      else (if Array.sub (sol, e)
            then let val x = Array.sub (side, e)
                 in Array.update (cnt, x, Array.sub (cnt, x) + 1) end
            else ();
            tally (side, e + 1))
    fun verify (what, x) =
      if x > nodes then ()
      else if Array.sub (cnt, x) > Array.sub (ka, x)
      then raise Bad (what ^ " vertex " ^ Int.toString x ^ " holds "
                      ^ Int.toString (Array.sub (cnt, x)) ^ " edges, capacity "
                      ^ Int.toString (Array.sub (ka, x)))
      else (Array.update (cnt, x, 0); verify (what, x + 1))
  in
    tally (fa, 0); verify ("left", 1);
    tally (ta, 0); verify ("right", 1)
  end

end
