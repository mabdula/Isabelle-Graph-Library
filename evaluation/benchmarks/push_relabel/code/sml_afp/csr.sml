(* Turning a DIMACS arc list into the shapes the AFP export's entry point
 * wants: an adjacency map and a capacity function.
 *
 * The AFP export does not take an arc list.  It takes
 *
 *   - `am', an (int list) array giving, for each vertex, its neighbours in
 *     the RESIDUAL graph -- every w with an arc v->w or an arc w->v, since
 *     both carry residual capacity once flow moves; and
 *   - `c', a function from a vertex pair to a capacity, which the export then
 *     tabulates into a dense n-by-n matrix of its own.
 *
 * Neither can be read straight off the file, so this module builds them and
 * the campaign reports the cost as build_ms, outside the measured call.  That
 * is an asymmetry in the AFP column's favour and it is recorded rather than
 * hidden: the newer export is handed the parser's three arrays untouched and
 * builds its own structures inside the clock, because it offers an entry
 * point that can be.  This one does not.
 *
 * PARALLEL ARCS ARE SUMMED HERE, not dropped.  A capacity matrix has one cell
 * per ordered pair, so two arcs u->v cannot both survive as themselves; their
 * capacities add, which leaves the maximum flow value unchanged.  The merge is
 * a counting sort by tail followed by an insertion sort within each row and a
 * linear pass over it -- the rows in these families hold a handful of entries
 * each, so this is linear in the arc count in practice and never quadratic.
 *)
structure Csr =
struct

  (* rowStart : n+1,  col : m,  cap : m -- rows sorted by target, no repeats *)
  type csr = { n : int, nnz : int, rowStart : int array,
               col : int array, cap : int array }

  fun build (n, m, fa, ta, ca) : csr =
    let
      val rowStart = Array.array (n + 1, 0)
      fun count i =
        if i >= m then ()
        else
          let val u = Array.sub (fa, i)
          in Array.update (rowStart, u + 1, Array.sub (rowStart, u + 1) + 1);
             count (i + 1)
          end
      val () = count 0
      fun prefix v =
        if v > n then ()
        else (Array.update (rowStart, v, Array.sub (rowStart, v)
                                         + Array.sub (rowStart, v - 1));
              prefix (v + 1))
      val () = prefix 1
      val cursor = Array.tabulate (n, fn v => Array.sub (rowStart, v))
      val col = Array.array (m, 0)
      val cap = Array.array (m, 0)
      fun scatter i =
        if i >= m then ()
        else
          let
            val u = Array.sub (fa, i)
            val k = Array.sub (cursor, u)
          in
            Array.update (col, k, Array.sub (ta, i));
            Array.update (cap, k, Array.sub (ca, i));
            Array.update (cursor, u, k + 1);
            scatter (i + 1)
          end
      val () = scatter 0

      (* insertion sort of one row by target; rows are short *)
      fun sortRow (lo, hi) =
        let
          fun ins j =
            if j >= hi then ()
            else
              let
                val cj = Array.sub (col, j)
                val wj = Array.sub (cap, j)
                fun shift k =
                  if k >= lo andalso Array.sub (col, k) > cj
                  then (Array.update (col, k + 1, Array.sub (col, k));
                        Array.update (cap, k + 1, Array.sub (cap, k));
                        shift (k - 1))
                  else k
                val k = shift (j - 1)
              in
                Array.update (col, k + 1, cj);
                Array.update (cap, k + 1, wj);
                ins (j + 1)
              end
        in
          ins (lo + 1)
        end

      (* merge equal targets by adding their capacities, compacting in place *)
      val newStart = Array.array (n + 1, 0)
      fun compact (v, out) =
        if v >= n then out
        else
          let
            val lo = Array.sub (rowStart, v)
            val hi = Array.sub (rowStart, v + 1)
            val () = Array.update (newStart, v, out)
            val () = sortRow (lo, hi)
            fun go (i, out) =
              if i >= hi then out
              else
                let
                  val c = Array.sub (col, i)
                  fun run (j, acc) =
                    if j < hi andalso Array.sub (col, j) = c
                    then run (j + 1, acc + Array.sub (cap, j))
                    else (j, acc)
                  val (j, acc) = run (i + 1, Array.sub (cap, i))
                in
                  Array.update (col, out, c);
                  Array.update (cap, out, acc);
                  go (j, out + 1)
                end
            val out = go (lo, out)
          in
            compact (v + 1, out)
          end
      val nnz = compact (0, 0)
      val () = Array.update (newStart, n, nnz)
    in
      { n = n, nnz = nnz, rowStart = newStart, col = col, cap = cap }
    end

  (* capacity of the ordered pair (u, v); 0 when there is no arc.  Binary
   * search rather than a cursor: the export tabulates its matrix in row-major
   * order today, but nothing in the entry point's type says so, and a lookup
   * that does not depend on the call order cannot be wrong about it. *)
  fun lookup ({ rowStart, col, cap, ... } : csr) (u, v) =
    let
      fun bs (lo, hi) =
        if lo >= hi then 0
        else
          let
            val mid = lo + (hi - lo) div 2
            val c = Array.sub (col, mid)
          in
            if c = v then Array.sub (cap, mid)
            else if c < v then bs (mid + 1, hi)
            else bs (lo, mid)
          end
    in
      bs (Array.sub (rowStart, u), Array.sub (rowStart, u + 1))
    end

  (* v's neighbours in the residual graph: out-targets and in-sources merged.
   * Both rows are already sorted, so this is one linear merge per vertex. *)
  fun adjacency (fwd : csr, bwd : csr) =
    let
      val n = #n fwd
      val fs = #rowStart fwd and fc = #col fwd
      val bs = #rowStart bwd and bc = #col bwd
    in
      Array.tabulate (n, fn v =>
        let
          val fhi = Array.sub (fs, v + 1)
          val bhi = Array.sub (bs, v + 1)
          fun go (i, j, acc) =
            if i >= fhi andalso j >= bhi then List.rev acc
            else if j >= bhi then go (i + 1, j, Array.sub (fc, i) :: acc)
            else if i >= fhi then go (i, j + 1, Array.sub (bc, j) :: acc)
            else
              let val a = Array.sub (fc, i) and b = Array.sub (bc, j)
              in
                if a = b then go (i + 1, j + 1, a :: acc)
                else if a < b then go (i + 1, j, a :: acc)
                else go (i, j + 1, b :: acc)
              end
        in
          go (Array.sub (fs, v), Array.sub (bs, v), [])
        end)
    end

end
