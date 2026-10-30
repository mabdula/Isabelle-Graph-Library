/*
 * Solve a DIMACS .asn instance with JGraphT, timing only the solver call.
 *
 * Prints one CSV row in exactly the column order the SML driver writes, so
 * every solver in this study lands in the same table.
 *
 * Two JGraphT entry points are offered.  They are not variants of one thing:
 * they are different algorithms with different input requirements.
 *
 *   --solver kuhnmunkres
 *       org.jgrapht.alg.matching.KuhnMunkresMinimalWeightBipartitePerfectMatching
 *       The Hungarian method itself, O(V^3), which is the same algorithm the
 *       SML solver under test implements.  It REFUSES anything that is not a
 *       complete bipartite graph with equally sized sides -- it checks
 *       edges == |X|*|Y| and throws otherwise -- so on the two sparse families
 *       the absent arcs must be supplied at a cost no cheapest perfect
 *       matching would ever pick, exactly as the dense SciPy run `lsa' is fed.
 *       On the geometric family the graph is already complete, so this solver
 *       receives the instance untouched.
 *
 *   --solver mwbm
 *       org.jgrapht.alg.matching.MaximumWeightBipartiteMatching
 *       The LEDA-book shortest-augmenting-path method with vertex potentials,
 *       O(n(m + n log n)), working on the sparse arc list as it is on disk.
 *       It MAXIMISES weight, so arcs enter at (offset - cost).  The offset is
 *       the large one, |X|*cmax + 1, which makes every matching of k arcs beat
 *       every matching of k-1 arcs and so forces a maximum-cardinality answer:
 *       a perfect matching whenever one exists, and the cheapest such.  That
 *       choice is sound here, and was not sound for igraph, because this
 *       implementation carries its sums in BigDecimal exact arithmetic rather
 *       than in doubles.  The weights themselves still arrive as doubles, so
 *       the driver refuses any instance where the offset would leave the exact
 *       integer range of a double.
 *
 * JGraphT's other weighted matcher, KolmogorovWeightedPerfectMatching (blossom
 * V), is deliberately not benchmarked.
 *
 * Timing.  The clock is CPU time, user + system, of the thread that runs the
 * solver, taken from ThreadMXBean, which on Linux is clock_gettime on
 * CLOCK_THREAD_CPUTIME_ID and so has nanosecond resolution.  The whole-process
 * figure that would be the exact counterpart of getrusage, getProcessCpuTime,
 * is NOT used: HotSpot reads it out of /proc/self/stat, so it arrives in 10 ms
 * clock ticks, which is coarser than many of the runs being measured.  The
 * process figure is recorded alongside anyway, so the gap between the two --
 * the JIT compiler and the collector, which are native threads and so are
 * counted in one and not the other -- stays visible instead of being assumed
 * away.  The JVM is given one processor and the serial collector, so there are
 * no parallel GC threads to lose, and the solver is run once on a small
 * instance before the clock so the JIT has already compiled it.
 *
 * Reading the file and building the graph sit OUTSIDE the clock, as in every
 * other driver here.  What is inside the clock is the library's own entry
 * point, getMatching(), and for Kuhn-Munkres that call does its own O(V^2)
 * cost matrix build from hash lookups before any matching starts.  That is the
 * library's cost, so it is timed; it is attributed separately afterwards.
 *
 * Before the clock the solver is run once on a small instance to let the JIT
 * compile it, the same reason the Python drivers make a warm-up call.
 */

import org.jgrapht.Graph;
import org.jgrapht.alg.interfaces.MatchingAlgorithm;
import org.jgrapht.alg.matching.KuhnMunkresMinimalWeightBipartitePerfectMatching;
import org.jgrapht.alg.matching.MaximumWeightBipartiteMatching;
import org.jgrapht.graph.DefaultWeightedEdge;
import org.jgrapht.graph.SimpleWeightedGraph;

import java.io.BufferedInputStream;
import java.io.FileInputStream;
import java.io.InputStream;
import java.lang.management.ManagementFactory;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class JGraphTSolve {

    /* ---------------- DIMACS .asn reader (outside the clock) ------------- */

    static int nNodes, nArcs;
    static int[] src, dst;
    static long[] cost;
    static boolean[] leftFlag;

    static void parse(String path) throws Exception {
        byte[] b = Files.readAllBytes(Paths.get(path));
        int n = b.length, i = 0, na = 0;
        // first pass is unnecessary: the p line gives the arc count
        List<int[]> pend = null;
        int ai = 0;
        while (i < n) {
            int ls = i;
            while (i < n && b[i] != '\n') i++;
            int le = i;
            i++;
            if (ls >= le) continue;
            byte k = b[ls];
            if (k == 'a') {
                int p = ls + 1;
                long[] v = new long[3];
                for (int f = 0; f < 3; f++) {
                    while (p < le && (b[p] == ' ' || b[p] == '\t')) p++;
                    boolean neg = false;
                    if (p < le && (b[p] == '-' || b[p] == '+')) { neg = b[p] == '-'; p++; }
                    long x = 0;
                    while (p < le && b[p] >= '0' && b[p] <= '9') { x = x * 10 + (b[p] - '0'); p++; }
                    v[f] = neg ? -x : x;
                }
                src[ai] = (int) v[0];
                dst[ai] = (int) v[1];
                cost[ai] = v[2];
                ai++;
            } else if (k == 'p') {
                int p = ls + 1;
                long[] v = new long[3];
                int f = 0;
                while (p < le && f < 3) {
                    while (p < le && (b[p] == ' ' || b[p] == '\t')) p++;
                    if (p < le && ((b[p] >= '0' && b[p] <= '9'))) {
                        long x = 0;
                        while (p < le && b[p] >= '0' && b[p] <= '9') { x = x * 10 + (b[p] - '0'); p++; }
                        v[f++] = x;
                    } else {
                        while (p < le && b[p] != ' ' && b[p] != '\t') p++;
                    }
                }
                nNodes = (int) v[0];
                nArcs = (int) v[1];
                src = new int[nArcs];
                dst = new int[nArcs];
                cost = new long[nArcs];
                leftFlag = new boolean[nNodes + 2];
            } else if (k == 'n') {
                int p = ls + 1;
                while (p < le && (b[p] == ' ' || b[p] == '\t')) p++;
                int x = 0;
                while (p < le && b[p] >= '0' && b[p] <= '9') { x = x * 10 + (b[p] - '0'); p++; }
                if (x < leftFlag.length) leftFlag[x] = true;
            }
        }
        nArcs = ai;
    }

    /* ---------------------------- CPU clock ------------------------------ */

    static com.sun.management.OperatingSystemMXBean OS =
        (com.sun.management.OperatingSystemMXBean) ManagementFactory.getOperatingSystemMXBean();

    static long procCpuNs() { return OS.getProcessCpuTime(); }

    static java.lang.management.ThreadMXBean TH = ManagementFactory.getThreadMXBean();

    static long threadCpuNs() { return TH.getCurrentThreadCpuTime(); }

    static long threadUsrNs() { return TH.getCurrentThreadUserTime(); }

    /** utime and stime of this process in clock ticks, from /proc/self/stat. */
    static long[] procTicks() {
        try {
            String s = new String(Files.readAllBytes(Paths.get("/proc/self/stat")));
            int close = s.lastIndexOf(')');
            String[] f = s.substring(close + 2).trim().split("\\s+");
            // after comm and state, field 0 here is ppid; utime is stat field 14
            return new long[] { Long.parseLong(f[11]), Long.parseLong(f[12]) };
        } catch (Exception e) {
            return new long[] { 0, 0 };
        }
    }

    /* ------------------------------ main --------------------------------- */

    public static void main(String[] args) throws Exception {
        String path = null, solver = "kuhnmunkres", tag = "";
        boolean csv = false;
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "--solver": solver = args[++i]; break;
                case "--tag":    tag = args[++i];    break;
                case "--csv":    csv = true;         break;
                default:         path = args[i];
            }
        }
        if (path == null) { System.err.println("usage: JGraphTSolve [--solver kuhnmunkres|mwbm] [--tag t] [--csv] file.asn"); System.exit(2); }

        parse(path);

        /* left side = arc tails, as in the SciPy driver */
        int maxId = 0;
        for (int i = 0; i < nArcs; i++) { if (src[i] > maxId) maxId = src[i]; if (dst[i] > maxId) maxId = dst[i]; }
        boolean anyFlag = false;
        if (leftFlag != null) for (boolean f : leftFlag) if (f) { anyFlag = true; break; }

        int[] rowOf = new int[maxId + 2];
        int[] colOf = new int[maxId + 2];
        java.util.Arrays.fill(rowOf, -1);
        java.util.Arrays.fill(colOf, -1);
        int nLeft = 0, nRight = 0;
        if (anyFlag) {
            for (int v = 0; v < leftFlag.length && v <= maxId + 1; v++) if (leftFlag[v]) rowOf[v] = nLeft++;
        } else {
            boolean[] isSrc = new boolean[maxId + 2];
            for (int i = 0; i < nArcs; i++) isSrc[src[i]] = true;
            for (int v = 0; v < isSrc.length; v++) if (isSrc[v]) rowOf[v] = nLeft++;
        }
        boolean[] isDst = new boolean[maxId + 2];
        for (int i = 0; i < nArcs; i++) isDst[dst[i]] = true;
        for (int v = 0; v < isDst.length; v++) if (isDst[v] && rowOf[v] < 0) colOf[v] = nRight++;

        int[] rows = new int[nArcs], cols = new int[nArcs];
        long cmax = 0;
        for (int i = 0; i < nArcs; i++) {
            rows[i] = rowOf[src[i]];
            cols[i] = colOf[dst[i]];
            if (cost[i] > cmax) cmax = cost[i];
        }

        /* ---- input marshalling: before the clock ---- */
        Graph<Integer, DefaultWeightedEdge> g =
            new SimpleWeightedGraph<>(DefaultWeightedEdge.class);
        Set<Integer> part1 = new LinkedHashSet<>();
        Set<Integer> part2 = new LinkedHashSet<>();
        for (int i = 0; i < nLeft; i++)  { g.addVertex(i);          part1.add(i); }
        for (int j = 0; j < nRight; j++) { g.addVertex(nLeft + j);  part2.add(nLeft + j); }

        String status = "OPTIMAL";
        long bigPad = 0;
        long[][] denseCost = null;
        Map<Long, Long> realCost = null;

        if (solver.equals("kuhnmunkres")) {
            if (nLeft != nRight) {
                System.err.println("refusing to run: Kuhn-Munkres needs equally sized sides");
                System.exit(3);
            }
            /* One arc dearer than any whole perfect matching of real arcs, so a
             * cheapest assignment takes a fake arc only if no perfect matching
             * of real arcs exists at all. */
            bigPad = (long) nLeft * cmax + 1;
            if ((double) nLeft * (double) bigPad >= 9007199254740992.0) {
                System.err.println("refusing to run: padded weights would leave the exact integer range of a double");
                System.exit(3);
            }
            denseCost = new long[nLeft][nRight];
            for (long[] r : denseCost) java.util.Arrays.fill(r, bigPad);
            for (int i = 0; i < nArcs; i++) denseCost[rows[i]][cols[i]] = cost[i];
            for (int i = 0; i < nLeft; i++) {
                for (int j = 0; j < nRight; j++) {
                    DefaultWeightedEdge e = g.addEdge(i, nLeft + j);
                    g.setEdgeWeight(e, (double) denseCost[i][j]);
                }
            }
        } else if (solver.equals("mwbm")) {
            /* Maximiser: enter arcs at (offset - cost) with the large offset,
             * which forces a maximum-cardinality answer.  Safe because the
             * algorithm's own arithmetic is BigDecimal, exact at any size; the
             * only limit is that each weight be an exact integer double. */
            long offset = (long) nLeft * cmax + 1;
            if ((double) offset >= 9007199254740992.0) {
                System.err.println("refusing to run: weights would leave the exact integer range of a double");
                System.exit(3);
            }
            realCost = new HashMap<>(nArcs * 2);
            for (int i = 0; i < nArcs; i++) {
                DefaultWeightedEdge e = g.addEdge(rows[i], nLeft + cols[i]);
                if (e == null) continue;           /* parallel arc: already there */
                g.setEdgeWeight(e, (double) (offset - cost[i]));
                realCost.put((long) rows[i] * nRight + cols[i], cost[i]);
            }
            if (g.edgeSet().size() != nArcs) {
                System.err.println("refusing to run: graph holds " + g.edgeSet().size()
                                   + " edges for " + nArcs + " arcs");
                System.exit(3);
            }
        } else {
            System.err.println("unknown solver: " + solver);
            System.exit(2);
        }

        /* ---- warm the JIT on a small instance of the same solver ---- */
        warmUp(solver);

        MatchingAlgorithm<Integer, DefaultWeightedEdge> alg =
            solver.equals("kuhnmunkres")
                ? new KuhnMunkresMinimalWeightBipartitePerfectMatching<>(g, part1, part2)
                : new MaximumWeightBipartiteMatching<>(g, part1, part2);

        /* ---- clock ---- */
        long p0 = procCpuNs();
        long u0 = threadUsrNs();
        long c0 = threadCpuNs();
        long w0 = System.nanoTime();

        MatchingAlgorithm.Matching<Integer, DefaultWeightedEdge> m = null;
        try {
            m = alg.getMatching();
        } catch (IllegalArgumentException ex) {
            status = "REFUSED";
        }

        long w1 = System.nanoTime();
        long c1 = threadCpuNs();
        long u1 = threadUsrNs();
        long p1 = procCpuNs();
        /* ---- clock ---- */

        double wallMs = (w1 - w0) / 1e6;
        double cpuMs = (c1 - c0) / 1e6;
        double usrMs = (u1 - u0) / 1e6;
        double sysMs = cpuMs - usrMs;
        double procMs = (p1 - p0) / 1e6;

        int matched = 0;
        String costStr = "NA";
        if (m != null) {
            Set<DefaultWeightedEdge> es = m.getEdges();
            matched = es.size();
            long total = 0;
            boolean usedFake = false;
            for (DefaultWeightedEdge e : es) {
                int u = g.getEdgeSource(e), v = g.getEdgeTarget(e);
                int i = Math.min(u, v), j = Math.max(u, v) - nLeft;
                long c;
                if (denseCost != null) {
                    c = denseCost[i][j];
                    if (c >= bigPad) usedFake = true;
                } else {
                    Long rc = realCost.get((long) i * nRight + j);
                    if (rc == null) { usedFake = true; c = 0; } else c = rc;
                }
                total += c;
            }
            if (matched != nLeft || nLeft != nRight || usedFake) {
                status = "NO_PERFECT_MATCHING";
            } else {
                costStr = Long.toString(total);
            }
        }

        String base = Paths.get(path).getFileName().toString();
        if (csv) {
            System.out.printf("%s,%d,%d,%d,%d,0,0.000,%s,%d,%s,%.3f,%.3f,%.3f,%.3f,%s%n",
                base, nNodes, nArcs, nLeft, nRight, status, matched, costStr,
                cpuMs, usrMs, sysMs, wallMs, tag);
        } else {
            System.out.printf("instance   %s%n", base);
            System.out.printf("solver     jgrapht 1.5.3 / %s%n", solver);
            System.out.printf("nodes      %d (|X| = %d, |Y| = %d)%n", nNodes, nLeft, nRight);
            System.out.printf("arcs       %d%n", nArcs);
            System.out.printf("status     %s%n", status);
            System.out.printf("matched    %d%n", matched);
            System.out.printf("cost       %s%n", costStr);
            System.out.printf("cpu        %.3f ms   (the measurement: solver thread, user + system)%n", cpuMs);
            System.out.printf("cpu user   %.3f ms%n", usrMs);
            System.out.printf("cpu sys    %.3f ms%n", sysMs);
            System.out.printf("proc cpu   %.3f ms   (whole process, 10 ms ticks: JIT and GC included)%n", procMs);
            System.out.printf("wall       %.3f ms%n", wallMs);
        }
    }

    /** Run the chosen solver on a small instance so the JIT compiles it. */
    static void warmUp(String solver) {
        int n = 48;
        java.util.Random rnd = new java.util.Random(12345);
        for (int rep = 0; rep < 3; rep++) {
            Graph<Integer, DefaultWeightedEdge> g =
                new SimpleWeightedGraph<>(DefaultWeightedEdge.class);
            Set<Integer> a = new LinkedHashSet<>(), b = new LinkedHashSet<>();
            for (int i = 0; i < n; i++) { g.addVertex(i); a.add(i); }
            for (int j = 0; j < n; j++) { g.addVertex(n + j); b.add(n + j); }
            for (int i = 0; i < n; i++)
                for (int j = 0; j < n; j++) {
                    DefaultWeightedEdge e = g.addEdge(i, n + j);
                    g.setEdgeWeight(e, 1 + rnd.nextInt(1000));
                }
            if (solver.equals("kuhnmunkres")) {
                new KuhnMunkresMinimalWeightBipartitePerfectMatching<>(g, a, b).getMatching();
            } else {
                new MaximumWeightBipartiteMatching<>(g, a, b).getMatching();
            }
        }
    }
}
