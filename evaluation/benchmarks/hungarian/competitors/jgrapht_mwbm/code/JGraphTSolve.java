/*
 * Solve a DIMACS .asn instance with JGraphT.  One row per run.  What is
 * clocked is the library's structure build, where that structure needs the
 * complete arc list before it can be built, and then the solver call; nothing
 * else.
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
 * THE STRUCTURES.  The rule of this study: a solver gets its faster structure;
 * a structure that can be filled arc by arc while the file is read may be
 * built outside the clock; one that needs the complete arc list first is
 * built after parsing, and that build is the first part of the clocked
 * period, as it is for our exported code, which builds its CSR inside.
 *
 *   mwbm now runs on SparseIntUndirectedWeightedGraph from jgrapht-opt, a CSR
 *   graph, and that graph is BUILT INSIDE THE CLOCK: it is immutable and takes
 *   the complete edge list at construction, so it cannot consume arcs as the
 *   lines come off the file.  The jgrapht_mwbm_hashgraph column gives it a
 *   SimpleWeightedGraph -- an object per edge, a hash map from vertex to its
 *   edge set -- built before the clock, against an export that builds its CSR
 *   inside; that compares two layouts, not two implementations of the algorithm.  Repacking the parsed
 *   arrays into the List<Triple<Integer,Integer,Double>> the constructor
 *   demands is marshalling into the library's input format and stays outside.
 *   The matcher's own entry checks (requireUndirected, isSimple, which on a
 *   CSR graph is a scan rather than a flag, isBipartitePartition) are inside,
 *   as the library's own cost.
 *
 *   kuhnmunkres KEEPS its SimpleWeightedGraph, built before the clock.  Its
 *   first step inside getMatching() is |X|*|Y| calls of getEdge(x, y) to fill
 *   its cost matrix, and the hash-backed graph is the faster structure for
 *   that -- a CSR graph answers getEdge by scanning a row.  That graph fills
 *   arc by arc as the file is read, so its build may precede the clock; the
 *   dense padding of the sparse families is the arc list it is filled from.
 *   The constructor, getMatching(), and the O(V^2) matrix build inside it are
 *   the measurement.
 *
 * THE CLOCK IS THE THREAD CPU CLOCK PLUS THE COLLECTOR'S TIME.  cpu_ms is the
 * solver thread's CPU time (ThreadMXBean, CLOCK_THREAD_CPUTIME_ID, nanosecond
 * resolution) plus the time the JVM's own counter says the collector spent
 * (GarbageCollectorMXBean.getCollectionTime, in whole milliseconds), both
 * read immediately before and after the call.  The JVM runs with the serial
 * collector on one processor, so a collection is the VM thread working while
 * the measured thread stands still; a thread clock alone drops that work, and
 * these matchers allocate heavily (BigDecimal everywhere, |X|^2 edge objects
 * for kuhnmunkres).  The process clock is not the measurement: it counts the
 * JIT compiler threads, which keep compiling inside the window after any
 * warm-up this study can afford, and it arrives in 10 ms ticks.  It is still
 * printed in --human mode as a diagnostic, with the compiler's own counter.
 *
 * THE WARM-UP.  Before the clock the chosen solver is run on a seeded random
 * instance, through the same measured function, until two whole solves add
 * nothing to the compiler's total (60 s cap).  A fixed small number of runs
 * was not enough: HotSpot compiles in the background and the measured call
 * itself brings methods over the threshold.
 */

import org.jgrapht.Graph;
import org.jgrapht.alg.interfaces.MatchingAlgorithm;
import org.jgrapht.alg.matching.KuhnMunkresMinimalWeightBipartitePerfectMatching;
import org.jgrapht.alg.matching.MaximumWeightBipartiteMatching;
import org.jgrapht.alg.util.Triple;
import org.jgrapht.graph.DefaultWeightedEdge;
import org.jgrapht.graph.SimpleWeightedGraph;
import org.jgrapht.opt.graph.sparse.SparseIntUndirectedWeightedGraph;

import java.lang.management.CompilationMXBean;
import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
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
        int n = b.length, i = 0;
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

    /* ---------------------------- the clock ------------------------------ */

    static final ThreadMXBean THREADS = ManagementFactory.getThreadMXBean();
    static final List<GarbageCollectorMXBean> GCS =
        ManagementFactory.getGarbageCollectorMXBeans();
    static com.sun.management.OperatingSystemMXBean OS =
        ManagementFactory.getPlatformMXBean(com.sun.management.OperatingSystemMXBean.class);

    /** The calling thread alone, in nanoseconds. */
    static long threadCpuNs() { return THREADS.getCurrentThreadCpuTime(); }
    static long threadUsrNs() { return THREADS.getCurrentThreadUserTime(); }

    /** Time spent in garbage collection so far, in nanoseconds.  The JVM's
     *  own counter, kept in whole milliseconds; under the serial collector it
     *  is the time the measured thread stood still while the VM thread
     *  collected.  THE OTHER HALF OF THE MEASUREMENT. */
    static long gcNs() {
        long t = 0;
        for (GarbageCollectorMXBean g : GCS) {
            long v = g.getCollectionTime();
            if (v > 0) t += v;
        }
        return t * 1_000_000L;
    }

    /** The whole process, 10 ms ticks.  A diagnostic, not the measurement:
     *  it includes the JIT compiler. */
    static long procCpuNs() { return OS.getProcessCpuTime(); }

    /** Milliseconds the JIT compiler has spent, cumulative.  A diagnostic. */
    static long jitMs() {
        CompilationMXBean c = ManagementFactory.getCompilationMXBean();
        return (c == null || !c.isCompilationTimeMonitoringSupported())
               ? -1 : c.getTotalCompilationTime();
    }

    /* ----------------------- the measured functions ---------------------- */

    /** mwbm: build the CSR graph from the triple list, then match.  Both
     *  inside the clock. */
    static final class MwbmResult {
        Graph<Integer, Integer> g;
        MatchingAlgorithm.Matching<Integer, Integer> m;
    }

    static MwbmResult solveMwbm(int nVertices, List<Triple<Integer, Integer, Double>> es,
                                Set<Integer> part1, Set<Integer> part2) {
        MwbmResult r = new MwbmResult();
        r.g = new SparseIntUndirectedWeightedGraph(nVertices, es);
        r.m = new MaximumWeightBipartiteMatching<>(r.g, part1, part2).getMatching();
        return r;
    }

    /** kuhnmunkres: the constructor and getMatching() on the complete
     *  hash-backed graph that was filled before the clock. */
    static MatchingAlgorithm.Matching<Integer, DefaultWeightedEdge> solveKm(
            Graph<Integer, DefaultWeightedEdge> g, Set<Integer> part1, Set<Integer> part2) {
        return new KuhnMunkresMinimalWeightBipartitePerfectMatching<>(g, part1, part2).getMatching();
    }

    /* ------------------------------ warm-up ------------------------------ */

    static final int WARM_MIN_REPS = 12;    // if the compiler cannot be watched
    static final int WARM_MAX_REPS = 60;    // the cap on going round again
    static final int WARM_QUIET = 2;        // clean solves needed to stop
    static final int WARM_CAP_S = 60;       // and a cap in seconds
    static long sink = 0;                   // keeps the warm-up results alive

    static void warmUp(String solver) {
        // A seeded random instance, the same for every run of every file.
        // kuhnmunkres: complete, 256 a side (65536 edge objects; its solve is
        // cubic so this is a few tens of milliseconds a round).  mwbm: 2048 a
        // side at eleven arcs per left vertex, the shape of the sparse
        // families, with the weights entered as (offset - cost) exactly as a
        // real instance's are.
        java.util.Random rnd = new java.util.Random(20261014L);
        Runnable one;
        if (solver.equals("kuhnmunkres")) {
            int n = 256;
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
            one = () -> { sink += solveKm(g, a, b).getEdges().size(); };
        } else {
            int n = 2048, deg = 11;
            long offset = (long) n * 1000 + 1;
            Set<Long> seen = new HashSet<>();
            List<Triple<Integer, Integer, Double>> es = new ArrayList<>(n * deg);
            for (int i = 0; i < n; i++)
                for (int k = 0; k < deg; k++) {
                    int j = rnd.nextInt(n);
                    if (!seen.add((long) i * n + j)) continue;   // keep it simple
                    es.add(Triple.of(i, n + j, (double) (offset - (1 + rnd.nextInt(1000)))));
                }
            Set<Integer> a = new LinkedHashSet<>(), b = new LinkedHashSet<>();
            for (int i = 0; i < n; i++) a.add(i);
            for (int j = 0; j < n; j++) b.add(n + j);
            one = () -> { sink += solveMwbm(2 * n, es, a, b).m.getEdges().size(); };
        }

        // Go round until a WHOLE solve adds nothing to the compiler's total,
        // twice running; HotSpot compiles in the background and the measured
        // call itself brings methods over the threshold, so a fixed count is
        // not enough.  The caps keep a JVM that never settles from hanging
        // the run.
        CompilationMXBean cmp = ManagementFactory.getCompilationMXBean();
        boolean canWatch = cmp != null && cmp.isCompilationTimeMonitoringSupported();
        int quiet = 0;
        long deadline = System.nanoTime() + WARM_CAP_S * 1_000_000_000L;
        for (int i = 0; i < WARM_MAX_REPS && quiet < WARM_QUIET; i++) {
            long before = canWatch ? cmp.getTotalCompilationTime() : 0;
            one.run();
            settleJit(cmp, canWatch);
            long after = canWatch ? cmp.getTotalCompilationTime() : 0;
            quiet = (canWatch && after == before) ? quiet + 1 : 0;
            if (System.nanoTime() > deadline) break;
            if (!canWatch && i >= WARM_MIN_REPS) break;
        }
        if (sink < 0) System.err.println("unreachable");
    }

    /** Wait for the compiler's queue to drain: return once its total time has
     *  not moved for five polls in a row.  A sleep, so the compiler threads
     *  get the core. */
    static void settleJit(CompilationMXBean c, boolean can) {
        if (!can) return;
        long last = -1;
        int quiet = 0;
        for (int i = 0; i < 300 && quiet < 5; i++) {       // at most ~3 s
            long t = c.getTotalCompilationTime();
            quiet = (t == last) ? quiet + 1 : 0;
            last = t;
            try { Thread.sleep(10); } catch (InterruptedException e) { return; }
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
                case "--human":  csv = false;        break;
                default:         path = args[i];
            }
        }
        if (path == null) { System.err.println("usage: JGraphTSolve [--solver kuhnmunkres|mwbm] [--tag t] [--csv] file.asn"); System.exit(2); }
        if (!solver.equals("kuhnmunkres") && !solver.equals("mwbm")) {
            System.err.println("unknown solver: " + solver);
            System.exit(2);
        }

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
        Set<Integer> part1 = new LinkedHashSet<>();
        Set<Integer> part2 = new LinkedHashSet<>();
        for (int i = 0; i < nLeft; i++)  part1.add(i);
        for (int j = 0; j < nRight; j++) part2.add(nLeft + j);

        String status = "OPTIMAL";
        long bigPad = 0;
        long[][] denseCost = null;
        Map<Long, Long> realCost = null;
        Graph<Integer, DefaultWeightedEdge> kmGraph = null;           // kuhnmunkres
        List<Triple<Integer, Integer, Double>> es = null;              // mwbm

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
            /* The hash-backed graph, filled arc by arc: the faster structure
             * for this algorithm's getEdge(x, y) lookups, and one that could
             * be filled while the file is read, so it is built here, outside
             * the clock.  See the header. */
            kmGraph = new SimpleWeightedGraph<>(DefaultWeightedEdge.class);
            for (int i = 0; i < nLeft; i++)  kmGraph.addVertex(i);
            for (int j = 0; j < nRight; j++) kmGraph.addVertex(nLeft + j);
            for (int i = 0; i < nLeft; i++) {
                for (int j = 0; j < nRight; j++) {
                    DefaultWeightedEdge e = kmGraph.addEdge(i, nLeft + j);
                    kmGraph.setEdgeWeight(e, (double) denseCost[i][j]);
                }
            }
        } else {
            /* Maximiser: enter arcs at (offset - cost) with the large offset,
             * which forces a maximum-cardinality answer.  Safe because the
             * algorithm's own arithmetic is BigDecimal, exact at any size; the
             * only limit is that each weight be an exact integer double. */
            long offset = (long) nLeft * cmax + 1;
            if ((double) offset >= 9007199254740992.0) {
                System.err.println("refusing to run: weights would leave the exact integer range of a double");
                System.exit(3);
            }
            /* The constructor's input list -- marshalling, outside the clock.
             * The CSR graph itself is built from it inside.  A parallel arc
             * would make the graph non-simple and the matcher would refuse it;
             * the first sweep refused such an instance too, so refuse here,
             * before anything is measured. */
            realCost = new HashMap<>(nArcs * 2);
            es = new ArrayList<>(nArcs);
            for (int i = 0; i < nArcs; i++) {
                if (realCost.put((long) rows[i] * nRight + cols[i], cost[i]) != null) {
                    System.err.println("refusing to run: parallel arc " + src[i] + " -> " + dst[i]);
                    System.exit(3);
                }
                es.add(Triple.of(rows[i], nLeft + cols[i], (double) (offset - cost[i])));
            }
        }

        /* ---- warm the JIT through the measured function ---- */
        warmUp(solver);
        // The warm-up's garbage is unreachable now.  Ask for it to be
        // reclaimed HERE, outside the clock, so that its collection is not
        // charged to the measurement.
        System.gc();

        /* ---- clock ---- */
        long p0 = procCpuNs();
        long j0 = jitMs();
        long g0 = gcNs();
        long u0 = threadUsrNs();
        long c0 = threadCpuNs();
        long w0 = System.nanoTime();

        MatchingAlgorithm.Matching<Integer, DefaultWeightedEdge> mKm = null;
        MwbmResult mw = null;
        try {
            if (solver.equals("kuhnmunkres")) mKm = solveKm(kmGraph, part1, part2);
            else                              mw = solveMwbm(nLeft + nRight, es, part1, part2);
        } catch (IllegalArgumentException ex) {
            status = "REFUSED";
        }

        long w1 = System.nanoTime();
        long c1 = threadCpuNs();
        long u1 = threadUsrNs();
        long g1 = gcNs();
        long j1 = jitMs();
        long p1 = procCpuNs();
        /* ---- clock ---- */

        long thrNs = c1 - c0, gcNsD = g1 - g0;
        long cpuNsD = thrNs + gcNsD;                        // THE MEASUREMENT
        long usrNsD = (u1 - u0) + gcNsD, sysNsD = thrNs - (u1 - u0);
        double wallMs = (w1 - w0) / 1e6;
        double cpuMs = cpuNsD / 1e6;
        double usrMs = usrNsD / 1e6;
        double sysMs = sysNsD / 1e6;
        double procMs = (p1 - p0) / 1e6;

        /* ---- the answer, after the clock ---- */
        int matched = 0;
        String costStr = "NA";
        if (mKm != null || mw != null) {
            long total = 0;
            boolean usedFake = false;
            if (mKm != null) {
                Set<DefaultWeightedEdge> edges = mKm.getEdges();
                matched = edges.size();
                for (DefaultWeightedEdge e : edges) {
                    int u = kmGraph.getEdgeSource(e), v = kmGraph.getEdgeTarget(e);
                    int i = Math.min(u, v), j = Math.max(u, v) - nLeft;
                    long c = denseCost[i][j];
                    if (c >= bigPad) usedFake = true;
                    total += c;
                }
            } else {
                Set<Integer> edges = mw.m.getEdges();
                matched = edges.size();
                for (Integer e : edges) {
                    int u = mw.g.getEdgeSource(e), v = mw.g.getEdgeTarget(e);
                    int i = Math.min(u, v), j = Math.max(u, v) - nLeft;
                    Long rc = realCost.get((long) i * nRight + j);
                    if (rc == null) { usedFake = true; } else total += rc;
                }
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
            System.out.printf("cpu        %.3f ms   (the measurement: solver thread + collector)%n", cpuMs);
            System.out.printf("  thread   %.3f ms%n", thrNs / 1e6);
            System.out.printf("  gc       %.3f ms%n", gcNsD / 1e6);
            System.out.printf("cpu user   %.3f ms   (thread user + collector)%n", usrMs);
            System.out.printf("cpu sys    %.3f ms%n", sysMs);
            System.out.printf("proc cpu   %.3f ms   (whole process, 10 ms ticks: JIT included; a diagnostic)%n", procMs);
            System.out.printf("jit        %d ms   (compiled inside the window; a diagnostic)%n", j1 - j0);
            System.out.printf("wall       %.3f ms%n", wallMs);
        }
    }
}
