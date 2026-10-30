// Benchmark driver for JGraphT's Kruskal on DIMACS .gr instances.
//
//   run.sh [options] <instance.gr>
//
// Shape of a run, in this order:
//
//   1. parse the .gr file                                  (clocked, reported)
//   2. collapse parallel edges to the cheapest             (clocked, reported)
//   3. fill a DefaultUndirectedWeightedGraph from the edges (clocked, reported)
//   4. warm up: run Kruskal on THE INSTANCE ITSELF until compiled (not measured)
//   5. read the clock
//   6. new KruskalMinimumSpanningTree<>(g).getSpanningTree()
//   7. read the clock again
//   8. report the difference, plus the tree for checking
//
// THE GRAPH IS BUILT OUTSIDE THE CLOCK, and that is the rule of these studies
// applied: a structure that can be filled while the file is read may be built
// outside the clock; one that needs the complete arc list first is built after
// parsing and that build opens the clock.  Kruskal's algorithm needs no
// adjacency structure -- JGraphT's reads edgeSet(), sorts it by weight and
// joins endpoints in a UnionFind over vertexSet() -- so the most suitable
// JGraphT graph for it is the one that is filled one addEdge at a time and
// hands Kruskal its edges, their endpoints and their weights: a
// DefaultUndirectedWeightedGraph<Integer, DefaultWeightedEdge>, JGraphT's
// plain undirected weighted graph (an object per edge, hash maps around it;
// the parser has already collapsed parallel edges, so the multigraph class is
// not needed).  (jgrapht-opt's SparseIntUndirectedWeightedGraph
// is a CSR that needs the complete edge list up front and builds an incidence
// index Kruskal never reads; it would have to be built inside the clock, and
// the clock would then be charging Kruskal for a structure it does not use.)
// Here the graph is filled from the parsed arrays rather than from the file
// directly -- the same work in the same place -- and that time is build_ms.
//
// What IS inside the clock is everything KruskalMinimumSpanningTree does:
// copy edgeSet() into an ArrayList, sort it by weight, build a UnionFind over
// the vertices and run the loop, collecting the tree edges into a set.
//
// THE CLOCK is the solver thread's CPU time PLUS the collector's time, read
// from the JVM's own counters before and after the call and the differences
// added.  Under the serial collector a collection happens only because the
// measured thread allocated and only while that thread waits, so the sum is
// that thread's work plus the collecting done for it, and nothing else.  The
// whole-process clock also counts the JIT compiler threads and is kept as
// proc_ms, a diagnostic.
//
// THE WARM-UP runs the measured call on the measured graph before the clock
// opens, round after round until the compiler has been quiet for two rounds
// and at least two seconds of rounds have gone by, as the JGraphT drivers of
// the BFS, DFS and Dijkstra studies do.  Kruskal does not change the graph,
// so the rounds run on the graph itself; an instance over WARM_ARCS arcs is
// warmed on a separate pseudograph of its own induced subgraph on the first
// n' vertices, n' the largest power of two for which that subgraph fits.
// The rounds spin rather than sleep while the compiler settles, because an
// idle core on this box is clocked down.
//
// EVERY ARC IS AN UNDIRECTED EDGE, AND PARALLEL EDGES ARE COLLAPSED: on
// Thomas Ammer's instruction of 2026-10-15 the parser keeps the cheapest
// edge of every unordered pair (collapse() below), so the solver is handed a
// simple graph.  Parsing work, outside the clock, reported in dedup_ms; the
// `edges' column is the count after it, `arcs' the file's.  Every driver in
// the study does the same.  THE ANSWER IS CHECKED
// AFTER THE CLOCK with the driver's own union-find on the tree's edges, and
// the count is compared with n minus the number of connected components of
// the whole graph.  The tree weight is reported for the cross-check between
// solvers.

import java.io.File;
import java.io.IOException;
import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;

import org.jgrapht.alg.interfaces.SpanningTreeAlgorithm.SpanningTree;
import org.jgrapht.alg.spanning.KruskalMinimumSpanningTree;
import org.jgrapht.graph.DefaultWeightedEdge;
import org.jgrapht.graph.DefaultUndirectedWeightedGraph;

public final class JGraphTKruskal {

    static final String HEADER =
        "instance,nodes,arcs,edges,repeat,status,tree_edges,tree_weight," +
        "cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms," +
        "parse_ms,dedup_ms,build_ms,tag";

    static final ThreadMXBean THREADS = ManagementFactory.getThreadMXBean();
    static final List<GarbageCollectorMXBean> GCS =
        ManagementFactory.getGarbageCollectorMXBeans();
    static com.sun.management.OperatingSystemMXBean OS =
        ManagementFactory.getPlatformMXBean(com.sun.management.OperatingSystemMXBean.class);

    static long threadCpuNanos() { return THREADS.getCurrentThreadCpuTime(); }
    static long threadUserNanos() { return THREADS.getCurrentThreadUserTime(); }

    /** Time spent in garbage collection so far, in nanoseconds: the JVM's own
     *  counter, kept in whole milliseconds, scaled so it can be added to the
     *  thread clock.  THE OTHER HALF OF THE MEASUREMENT. */
    static long gcNanos() {
        long t = 0;
        for (GarbageCollectorMXBean g : GCS) {
            long v = g.getCollectionTime();
            if (v > 0) t += v;
        }
        return t * 1_000_000L;
    }

    static long procNanos() { return OS.getProcessCpuTime(); }

    static long jitMs() {
        java.lang.management.CompilationMXBean c =
            ManagementFactory.getCompilationMXBean();
        return (c == null || !c.isCompilationTimeMonitoringSupported())
               ? -1 : c.getTotalCompilationTime();
    }

    static void die(String msg) {
        System.err.println("error: " + msg);
        System.exit(1);
    }

    static String ms(long nanos) { return String.format("%.3f", nanos / 1e6); }

    // ---------- the instance ----------

    static final class Instance {
        int nNodes;
        int nArcs;
        int[] from;     // 0-based
        int[] to;       // 0-based
        long[] weight;
    }

    /** DIMACS .gr reader.  A transcription of the SML reader in
     *  drivers/sml/gr_parser.sml, so the drivers see the same arcs. */
    static Instance parseGr(String path) throws IOException {
        byte[] s = Files.readAllBytes(Paths.get(path));
        Instance in = new Instance();
        in.nNodes = -1;
        int[] from = new int[16];
        int[] to = new int[16];
        long[] w = new long[16];
        int m = 0;
        int p = 0;
        while (p < s.length) {
            while (p < s.length && (s[p] == ' ' || s[p] == '\t'
                                    || s[p] == '\n' || s[p] == '\r')) p++;
            if (p >= s.length) break;
            byte kind = s[p++];
            if (kind == 'c') {
                while (p < s.length && s[p] != '\n') p++;
                continue;
            }
            long[] f = new long[3];
            int nf = 0;
            boolean wantTag = (kind == 'p');
            while (p < s.length && s[p] != '\n' && nf < 3) {
                while (p < s.length && (s[p] == ' ' || s[p] == '\t')) p++;
                if (p >= s.length || s[p] == '\n' || s[p] == '\r') break;
                if (wantTag && !(s[p] >= '0' && s[p] <= '9') && s[p] != '-') {
                    while (p < s.length && s[p] != ' ' && s[p] != '\t'
                           && s[p] != '\n') p++;
                    wantTag = false;
                    continue;
                }
                boolean neg = false;
                if (s[p] == '-') { neg = true; p++; }
                if (!(p < s.length && s[p] >= '0' && s[p] <= '9')) break;
                long v = 0;
                while (p < s.length && s[p] >= '0' && s[p] <= '9') {
                    v = v * 10 + (s[p] - '0'); p++;
                }
                f[nf++] = neg ? -v : v;
            }
            while (p < s.length && s[p] != '\n') p++;
            if (p < s.length) p++;

            if (kind == 'p') {
                if (nf < 2) die(path + ": bad `p' line");
                in.nNodes = (int) f[0];
                int cap = Math.max((int) Math.min(f[1], Integer.MAX_VALUE - 8), 16);
                from = new int[cap]; to = new int[cap]; w = new long[cap];
            } else if (kind == 'a') {
                if (nf < 3) die(path + ": bad `a' line");
                if (in.nNodes < 0) die(path + ": arc line before the `p sp' line");
                if (m == from.length) {
                    int cap = from.length + (from.length >> 1) + 16;
                    from = java.util.Arrays.copyOf(from, cap);
                    to = java.util.Arrays.copyOf(to, cap);
                    w = java.util.Arrays.copyOf(w, cap);
                }
                from[m] = (int) f[0] - 1;
                to[m] = (int) f[1] - 1;
                w[m] = f[2];
                m++;
            }
        }
        if (in.nNodes < 0) die(path + ": no `p sp' line");
        in.nArcs = m;
        in.from = java.util.Arrays.copyOf(from, m);
        in.to = java.util.Arrays.copyOf(to, m);
        in.weight = java.util.Arrays.copyOf(w, m);
        return in;
    }

    /** Keep the cheapest arc of every unordered pair {u, v}.  Two stable
     *  counting sorts of the edge indices, by the larger endpoint and then by
     *  the smaller, put equal pairs side by side in (lo, hi) order; one scan
     *  keeps the minimum weight of each run.  Linear in n + m.  The result
     *  lists each edge once as (lo, hi, w), sorted by (lo, hi). */
    static Instance collapse(Instance in) {
        int n = in.nNodes, m = in.nArcs;
        int[] lo = new int[m], hi = new int[m];
        for (int i = 0; i < m; i++) {
            int u = in.from[i], v = in.to[i];
            if (u <= v) { lo[i] = u; hi[i] = v; } else { lo[i] = v; hi[i] = u; }
        }
        int[] src = new int[m], dst = new int[m], cnt = new int[n + 2];
        for (int i = 0; i < m; i++) src[i] = i;
        int[][] keys = { hi, lo };
        for (int pass = 0; pass < 2; pass++) {
            int[] key = keys[pass];
            java.util.Arrays.fill(cnt, 0);
            for (int i = 0; i < m; i++) cnt[key[src[i]] + 1]++;
            for (int k = 1; k <= n + 1; k++) cnt[k] += cnt[k - 1];
            for (int i = 0; i < m; i++) { int id = src[i]; dst[cnt[key[id]]++] = id; }
            int[] t = src; src = dst; dst = t;
        }
        Instance r = new Instance();
        r.nNodes = n;
        int[] f = new int[m], t = new int[m];
        long[] w = new long[m];
        int d = 0;
        for (int k = 0; k < m; k++) {
            int i = src[k];
            if (d > 0 && f[d - 1] == lo[i] && t[d - 1] == hi[i]) {
                if (in.weight[i] < w[d - 1]) w[d - 1] = in.weight[i];
            } else { f[d] = lo[i]; t[d] = hi[i]; w[d] = in.weight[i]; d++; }
        }
        r.nArcs = d;
        r.from = java.util.Arrays.copyOf(f, d);
        r.to = java.util.Arrays.copyOf(t, d);
        r.weight = java.util.Arrays.copyOf(w, d);
        return r;
    }

    /** The library's graph, filled edge by edge: OUTSIDE the clock, see the
     *  note at the top.  Vertices are the Integers 0..n-1. */
    static DefaultUndirectedWeightedGraph<Integer, DefaultWeightedEdge> build(
            int n, int[] from, int[] to, long[] w) {
        DefaultUndirectedWeightedGraph<Integer, DefaultWeightedEdge> g =
            new DefaultUndirectedWeightedGraph<>(DefaultWeightedEdge.class);
        for (int v = 0; v < n; v++) g.addVertex(Integer.valueOf(v));
        for (int i = 0; i < from.length; i++) {
            DefaultWeightedEdge e = g.addEdge(Integer.valueOf(from[i]), Integer.valueOf(to[i]));
            g.setEdgeWeight(e, (double) w[i]);
        }
        return g;
    }

    /** THE MEASURED CALL.  The warm-up goes through this same line. */
    static SpanningTree<DefaultWeightedEdge> solve(
            DefaultUndirectedWeightedGraph<Integer, DefaultWeightedEdge> g) {
        return new KruskalMinimumSpanningTree<>(g).getSpanningTree();
    }

    // ---------- the warm-up ----------

    static final int WARM_ARCS = 1 << 18;
    static final int WARM_MIN_REPS = 12;
    static final int WARM_MAX_REPS = 200;
    static final int WARM_QUIET = 2;
    static final int WARM_CAP_S = 60;
    static final int WARM_SLACK_MS = 4;
    static final int WARM_FLOOR_S = 2;

    static void warmUp(Instance in, DefaultUndirectedWeightedGraph<Integer, DefaultWeightedEdge> g) {
        DefaultUndirectedWeightedGraph<Integer, DefaultWeightedEdge> wg = g;
        if (in.nArcs > WARM_ARCS) {
            // one pass: how many arcs have both ends below each power of two
            int[] hist = new int[33];
            for (int i = 0; i < in.nArcs; i++) {
                int hi = Math.max(in.from[i], in.to[i]);
                hist[32 - Integer.numberOfLeadingZeros(hi)]++;   // floor(log2)+1
            }
            long cum = 0; int k = 0;
            for (int j = 0; j < 33; j++) {
                if (cum + hist[j] > WARM_ARCS) break;
                cum += hist[j]; k = j;
            }
            int wn = Math.max(1, 1 << k);                 // vertices 0 .. wn-1
            int[] f = new int[(int) cum], t = new int[(int) cum];
            long[] w = new long[(int) cum];
            int c = 0;
            for (int i = 0; i < in.nArcs; i++)
                if (in.from[i] < wn && in.to[i] < wn) { f[c] = in.from[i]; t[c] = in.to[i]; w[c] = in.weight[i]; c++; }
            wg = build(wn, f, t, w);
        }
        java.lang.management.CompilationMXBean cmp =
            ManagementFactory.getCompilationMXBean();
        boolean canWatch = cmp != null && cmp.isCompilationTimeMonitoringSupported();
        int quiet = 0;
        long deadline = System.nanoTime() + WARM_CAP_S * 1_000_000_000L;
        long work = 0;
        double sink = 0;
        for (int i = 0; i < WARM_MAX_REPS
                 && !(quiet >= WARM_QUIET && work >= WARM_FLOOR_S * 1_000_000_000L);
             i++) {
            long before = canWatch ? cmp.getTotalCompilationTime() : 0;
            long r0 = System.nanoTime();
            sink += solve(wg).getWeight();
            work += System.nanoTime() - r0;
            settleJit(cmp, canWatch);
            long after = canWatch ? cmp.getTotalCompilationTime() : 0;
            quiet = (canWatch && after - before <= WARM_SLACK_MS) ? quiet + 1 : 0;
            if (System.nanoTime() > deadline) break;
            if (!canWatch && i >= WARM_MIN_REPS) break;
        }
        if (sink < 0) System.err.println("unreachable");
    }

    /** Wait for the compiler's queue to drain, with a yielding spin. */
    static void settleJit(java.lang.management.CompilationMXBean c, boolean can) {
        if (!can) return;
        long last = -1;
        int quiet = 0;
        for (int i = 0; i < 1500 && quiet < 5; i++) {
            long t = c.getTotalCompilationTime();
            quiet = (t == last) ? quiet + 1 : 0;
            last = t;
            long until = System.nanoTime() + 2_000_000L;
            while (System.nanoTime() < until) Thread.yield();
        }
    }

    // ---------- the check, after the clock ----------

    static int find(int[] p, int i) {
        while (p[i] != i) { p[i] = p[p[i]]; i = p[i]; }
        return i;
    }

    static int components(Instance in) {
        int[] p = new int[in.nNodes];
        for (int i = 0; i < p.length; i++) p[i] = i;
        int c = in.nNodes;
        for (int i = 0; i < in.nArcs; i++) {
            int ru = find(p, in.from[i]), rv = find(p, in.to[i]);
            if (ru != rv) { p[ru] = rv; c--; }
        }
        return c;
    }

    // ---------- main ----------

    public static void main(String[] args) throws Exception {
        String path = null, tag = "";
        int repeats = 1;
        boolean csv = true;

        for (int i = 0; i < args.length; i++) {
            String a = args[i];
            if (a.equals("--header")) { System.out.println(HEADER); return; }
            else if (a.equals("--csv")) csv = true;
            else if (a.equals("--human")) csv = false;
            else if (a.equals("--tag") && i + 1 < args.length) tag = args[++i];
            else if (a.equals("--repeats") && i + 1 < args.length)
                repeats = Integer.parseInt(args[++i]);
            else if (a.startsWith("--")) die("unknown option " + a);
            else path = a;
        }
        if (path == null) die("an instance is required");
        if (repeats < 1) die("--repeats must be at least 1");

        // ---- 1. parse ----
        long t0 = threadCpuNanos();
        Instance raw = parseGr(path);
        long t1 = threadCpuNanos();
        // ---- 2. collapse parallel edges: parsing work, outside, reported ----
        Instance in = collapse(raw);
        int rawArcs = raw.nArcs;
        raw = null;
        long td = threadCpuNanos();
        // ---- 3. the library's graph, filled edge by edge (outside) ----
        DefaultUndirectedWeightedGraph<Integer, DefaultWeightedEdge> g =
            build(in.nNodes, in.from, in.to, in.weight);
        long t2 = threadCpuNanos();

        int comps = components(in);
        String base = new File(path).getName();
        StringBuilder out = new StringBuilder();

        // ---- 4. warm up, on this very graph ----
        warmUp(in, g);
        for (int rep = 1; rep <= repeats; rep++) {
            // Whatever the warm-up and the previous repeat left behind is
            // reclaimed HERE, outside the clock.
            System.gc();

            // ---- 5. clock ----
            long p0 = procNanos();
            long j0 = jitMs();
            long g0 = gcNanos();
            long u0 = threadUserNanos();
            long c0 = threadCpuNanos();
            long w0 = System.nanoTime();

            // ---- 6. Kruskal ----
            SpanningTree<DefaultWeightedEdge> tree = solve(g);

            // ---- 7. clock ----
            long w1 = System.nanoTime();
            long c1 = threadCpuNanos();
            long u1 = threadUserNanos();
            long g1 = gcNanos();
            long j1 = jitMs();
            long p1 = procNanos();

            // ---- 8. the answer, after the clock ----
            int[] p = new int[in.nNodes];
            for (int i = 0; i < p.length; i++) p[i] = i;
            long cnt = 0, weight = 0;
            boolean ok = true;
            for (DefaultWeightedEdge e : tree.getEdges()) {
                cnt++;
                int a = g.getEdgeSource(e).intValue(), b = g.getEdgeTarget(e).intValue();
                int ra = find(p, a), rb = find(p, b);
                if (ra == rb) ok = false;
                else { p[ra] = rb; weight += (long) g.getEdgeWeight(e); }
            }
            if (Math.round(tree.getWeight()) != weight) ok = false;
            String status = (ok && cnt == in.nNodes - comps) ? "SOLVED" : "BAD_TREE";

            long thrNs = c1 - c0, gcNs = g1 - g0;
            long cpuNs = thrNs + gcNs;                 // THE MEASUREMENT
            long usrNs = (u1 - u0) + gcNs, sysNs = thrNs - (u1 - u0);
            if (csv)
                out.append(String.join(",",
                    base, Integer.toString(in.nNodes), Integer.toString(rawArcs),
                    Integer.toString(in.nArcs),
                    Integer.toString(rep), status, Long.toString(cnt), Long.toString(weight),
                    ms(cpuNs), ms(usrNs), ms(sysNs), ms(p1 - p0), ms(w1 - w0),
                    ms(t1 - t0), ms(td - t1), ms(t2 - td), tag)).append('\n');
            else
                out.append(String.format(
                    "%s  rep %d%n  status      %s%n  tree edges  %d  (n - components = %d)%n"
                    + "  tree weight %d%n  edges       %d  (%d arcs in the file)%n"
                    + "  cpu         %s ms   (the measurement: thread + collector)%n"
                    + "  of which    %s ms was garbage collection%n"
                    + "  wall        %s ms%n"
                    + "  proc        %s ms   (whole process: + the JIT, which compiled for %d ms)%n"
                    + "  build       %s ms   (graph, outside)%n",
                    base, rep, status, cnt, in.nNodes - comps, weight, in.nArcs, rawArcs,
                    ms(cpuNs), ms(gcNs), ms(w1 - w0), ms(p1 - p0), j1 - j0, ms(t2 - td)));
            System.out.print(out);
            out.setLength(0);
            System.out.flush();
        }
    }
}
