// Benchmark driver for JGraphT's Dijkstra on DIMACS .gr instances.
//
//   run.sh [options] <instance.gr>
//
// Shape of a run, in this order:
//
//   1. parse the .gr file                                  (clocked, reported)
//   2. repack the arcs into JGraphT's input list           (clocked, reported)
//   3. warm up: build and solve THE INSTANCE ITSELF (or a bounded subgraph
//      of it) until the JIT is quiet, spinning between rounds   (not measured)
//   4. read the clock
//   5. BUILD THE CSR GRAPH, then call IntVertexDijkstraShortestPath.getPath(s, t)
//   6. read the clock again
//   7. report the difference, plus the answer for checking
//
// THE GRAPH BUILD IS INSIDE THE CLOCK, AND THAT IS A DELIBERATE CHANGE.  The
// earlier campaign left it outside, on the grounds that an unverified library
// reads a file straight into its own graph and so its build fuses with
// parsing.  That reasoning does not hold for a CSR graph: SparseIntDirectedGraph
// is immutable and is handed a COMPLETE list of arcs at construction, so it
// cannot consume arcs as the lines come off the file.  The build is a separate
// pass over the whole arc list, exactly as it is for our exported code, and it
// is therefore measured exactly as our exported code's is.  LEMON's
// StaticDigraph is treated the same way in this study for the same reason.
//
// What is left outside the clock is the file read (parse_ms) and repacking the
// parsed int arrays into the List<Pair<Integer,Integer>> that the constructor
// demands (build_ms).  That repacking is marshalling into the library's input
// format, not the building of its structure, and it is the counterpart of the
// std::vector<std::pair<int,int>> the LEMON driver fills before its own clock
// opens.  Both figures are reported so that what sits outside the measurement
// is visible rather than merely asserted.  dedup_ms is 0.000: a sparse graph
// takes parallel arcs as they come, where SciPy and NetworkX cannot.
//
// THE GRAPH TYPE.  SparseIntDirectedWeightedGraph, from jgrapht-opt, whose backing is
// a CSR boolean matrix -- the same layout our export builds, and the reason
// this driver was rewritten.  The earlier campaign used DirectedWeightedPseudograph,
// which is the most permissive member of jgrapht-core's one and only graph
// family: an object per arc, a hash map from vertex to its edge set and another
// from edge to its endpoints.  Comparing that against a CSR export measured the
// difference between two layouts, not between two implementations of Dijkstra.
//
// Parallel arcs survive.  The road networks have them -- USA-road-t.NY alone
// has 3724 node pairs carrying two or three arcs, with different travel times
// -- and a sparse graph holds each one, as the pseudograph did; SciPy and
// NetworkX cannot, and are handed the cheapest of each bundle instead.
//
// NO_INCOMING_EDGES.  The constructor is given this third argument so that only
// the forward CSR is built.  Dijkstra walks outgoing arcs and never
// asks for an incoming one; the plain two-argument constructor would pass
// FULL_INCOMING_EDGES and build a reverse index this study never reads, which
// would be work charged to the library for nothing.  Vertex ids are 0..n-1
// already, so no renumbering is needed.
//
// ONE PROBLEM PER PROCESS.  The source and the target are given on the command
// line and exactly one of them is accepted: a shortest-path problem is a graph
// AND a pair, so two pairs are two problems and must not share a solver call,
// a solver object, or a process.  There is deliberately no way to hand this
// driver a list of pairs.
//
// The algorithm's OWN setup is inside the clock here, as it is for ours and
// for LEMON.  getPath constructs JGraphT's private Algorithm object, which
// allocates the distance, predecessor and heap-handle arrays and fills the
// distances with infinity over every vertex; that happens on the call, not on
// the IntVertexDijkstraShortestPath object built outside.
//
// EVERY REPEAT REBUILDS THE GRAPH.  It has to: the build is now part of what is
// being measured, so a repeat that reused the graph would be timing something
// else.  The previous repeat's graph is dropped and a collection is asked for
// BEFORE the clock opens, so that the cost of reclaiming it falls outside the
// next measurement rather than inside it.
//
// THE CLOCK IS THE THREAD CPU CLOCK PLUS THE COLLECTOR'S TIME.  The thread
// clock alone -- what the earlier campaign read -- leaves out the garbage
// collector, which under the serial collector runs on the VM thread while the
// measured thread stands still, and with the graph build now inside the
// window the run allocates enough for that to matter: it was found to
// understate by as much as 2.4x on the largest instances.  So the collector's
// own accumulated pause time, read from the JVM's GarbageCollectorMXBeans
// before and after the call, is added to the thread's time.  Under the serial
// collector a collection happens only because the measured thread allocated
// and only while it waits, so the sum is exactly that thread's work plus the
// collecting done on its behalf, and nothing else.
//
// The process clock was tried instead and rejected, with measurements.  It
// counts every thread, and the JIT compiler threads go on compiling well into
// the measured window even after a warm-up that has run to silence: on a
// 65536-node graph a 184 ms search read 320 ms on the process clock, 142 ms
// of it the compiler.  That is the JVM compiling, not the library working,
// and no warm-up this study could afford removed it.  Collection in those same
// windows was 0 ms -- the heap is 45 GB and one build-and-search never fills
// it at the small sizes -- so the process clock added what it should not and
// what it should have added was not there.  The collector's time becomes real
// on the road networks, and that is where it is counted.
//
// The collector's counter is in whole milliseconds; the thread clock is in
// nanoseconds.  cpu_ms is their sum and is the measurement.  cpu_usr_ms is
// the thread's user time plus the collector's time, cpu_sys_ms the thread's
// system time, so the two still add up to cpu_ms.  proc_ms is the whole
// process from /proc/self/stat in 10 ms ticks, as in every earlier campaign:
// a diagnostic that shows the JIT's share, not a measurement.
//
// THE WARM-UP.  Before the first measured call the same entry point is run on
// the instance itself -- the measured graph from the measured source, or, over
// WARM_ARCS arcs, the induced subgraph on its first n' nodes that fits the
// budget -- round after round, the answers thrown away, until the compiler has
// been quiet for WARM_QUIET rounds and at least WARM_FLOOR_S seconds of rounds
// have run (caps: WARM_MAX_REPS rounds, WARM_CAP_S seconds).  Without it the
// first measurement is an interpreter measurement: HotSpot starts in the
// interpreter and only compiles a method once it has been entered enough
// times.  MLton, Go and g++ are compiled ahead of time and have no such phase,
// so timing a cold JVM would not be comparing the same thing.  It goes through
// solve(), the very same line of code the measurement does, so the CSR
// CONSTRUCTOR is compiled too and not merely the search.  An earlier version
// warmed on a synthetic graph; warmUp() below says why that was replaced on
// 2026-10-14.  Between rounds the driver spins, yielding, rather than sleeps:
// see settleJit().
//
// THE HEAP.  IntVertexDijkstraShortestPath uses a 4-ARY addressable array heap
// by default, not a binary one.  That is JGraphT's own default and it is left
// alone: this driver measures the library as a user of the library gets it.
// Our export and LEMON both use binary heaps.  The difference is recorded
// here rather than tuned away.
//
// Vertices are the integers 0 .. n-1, which is the range
// IntVertexDijkstraShortestPath is specialised for: outside it the class falls
// back to an open-addressing hash map on every vertex touch.

import java.io.IOException;
import java.io.File;
import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.jgrapht.GraphPath;
import org.jgrapht.alg.shortestpath.IntVertexDijkstraShortestPath;
import org.jgrapht.alg.util.Triple;
import org.jgrapht.opt.graph.sparse.IncomingEdgesSupport;
import org.jgrapht.opt.graph.sparse.SparseIntDirectedWeightedGraph;

public final class JGraphTSolve {

    static final String HEADER =
        "instance,nodes,arcs,query,source,target,repeat,status," +
        "reached,hops,dist,cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms," +
        "parse_ms,dedup_ms,build_ms,clock_build_ms,clock_solve_ms,tag";

    static final ThreadMXBean THREADS = ManagementFactory.getThreadMXBean();
    static final List<GarbageCollectorMXBean> GCS =
        ManagementFactory.getGarbageCollectorMXBeans();
    static com.sun.management.OperatingSystemMXBean OS =
        ManagementFactory.getPlatformMXBean(com.sun.management.OperatingSystemMXBean.class);

    /** The calling thread alone, in nanoseconds. */
    static long threadCpuNanos() { return THREADS.getCurrentThreadCpuTime(); }
    static long threadUserNanos() { return THREADS.getCurrentThreadUserTime(); }

    /** Time spent in garbage collection so far, in nanoseconds.
     *
     *  The JVM's own counter, which under the serial collector is the time the
     *  measured thread stood still while the VM thread collected what it had
     *  allocated.  It is kept in whole milliseconds by the JVM; the figure is
     *  scaled so it can be added to the thread clock.  THE OTHER HALF OF THE
     *  MEASUREMENT. */
    static long gcNanos() {
        long t = 0;
        for (GarbageCollectorMXBean g : GCS) {
            long v = g.getCollectionTime();
            if (v > 0) t += v;
        }
        return t * 1_000_000L;
    }

    /** The whole process, in 10 ms ticks out of /proc/self/stat.  A
     *  diagnostic -- it includes the JIT compiler -- not the measurement. */
    static long procNanos() { return OS.getProcessCpuTime(); }

    /** Milliseconds the JIT compiler has spent, cumulative.  A diagnostic,
     *  not part of the measurement: it says how much of a measured window was
     *  the JVM still compiling rather than the library working.  Printed in
     *  --human mode only. */
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

    /** The intermediate reading of the clocked period: thread clock and
     *  collector time the moment the structure is built, before the
     *  solve.  Written by solve(), read after the clock closes. */
    static long midCpuNs, midGcNs;

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
            if (kind == 'c') {                       // a comment: drop the line
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
            // anything else (`t', stray tags) is ignored
        }
        if (in.nNodes < 0) die(path + ": no `p sp' line");
        in.nArcs = m;
        in.from = java.util.Arrays.copyOf(from, m);
        in.to = java.util.Arrays.copyOf(to, m);
        in.weight = java.util.Arrays.copyOf(w, m);
        return in;
    }

    /** Repack the parsed arcs into the list the CSR constructor demands.
     *
     *  OUTSIDE THE CLOCK.  This is marshalling into the library's input
     *  format -- the counterpart of the std::vector<std::pair<int,int>> the
     *  LEMON driver fills -- and not the building of the library's structure.
     *  It is clocked separately and reported in build_ms. */
    static List<Triple<Integer, Integer, Double>> edgeList(Instance in) {
        List<Triple<Integer, Integer, Double>> es = new ArrayList<>(in.nArcs);
        for (int i = 0; i < in.nArcs; i++)
            es.add(Triple.of(Integer.valueOf(in.from[i]), Integer.valueOf(in.to[i]),
                             Double.valueOf((double) in.weight[i])));
        return es;
    }

    /** THE MEASURED CALL: build the CSR graph, then solve on it.
     *
     *  Build and solve sit in one function, and the warm-up goes through this
     *  very same function, so a warm-up can never drift away from the thing it
     *  is warming and the constructor is compiled before the clock opens.
     *
     *  getPath constructs JGraphT's private Algorithm object, which allocates
     *  the distance, predecessor and heap-handle arrays and fills the
     *  distances with infinity over every vertex; that is the algorithm's own
     *  setup and it happens on the call, inside the clock, as it does for ours
     *  and for LEMON.  Returns the path, or null, and the graph it was found
     *  on, so the answer can be checked AFTER the clock. */
    static final class Answer {
        SparseIntDirectedWeightedGraph g;
        GraphPath<Integer, Integer> path;
    }

    static Answer solve(int n, List<Triple<Integer, Integer, Double>> edges,
                        int si, int ti) {
        Answer a = new Answer();
        a.g = new SparseIntDirectedWeightedGraph(n, edges,
                        IncomingEdgesSupport.NO_INCOMING_EDGES);
        // ---- the intermediate reading: the structure is built ----
        midCpuNs = threadCpuNanos();
        midGcNs = gcNanos();
        a.path = new IntVertexDijkstraShortestPath<Integer>(a.g).getPath(si, ti);
        return a;
    }

    // ---------- the warm-up ----------

    //: The warm-up budget and how long to keep going round.  The warm-up is
    //: wall time spent inside the per-run cap without being measured, so it
    //: has to be worth its cost; the caps below bound it.
    static final int WARM_ARCS = 1 << 18;    // the warm-up graph's size cap
    static final int WARM_MIN_REPS = 12;    // if the compiler cannot be watched
    static final int WARM_MAX_REPS = 200;   // the cap on going round again
    static final int WARM_QUIET = 2;        // clean solves needed to stop
    static final int WARM_CAP_S = 60;       // and a cap in seconds

    /** Warm up ON THE INSTANCE ITSELF, from the measured source.
     *
     *  A synthetic warm-up graph (a random digraph at m = 4n, 65536 nodes)
     *  was used before this and did not warm the right thing: HotSpot
     *  compiles against branch and type profiles, the profile of a different
     *  graph is a different profile, and the measured call still provoked
     *  fresh compilation after the warm-up, inflating the smallest cells.
     *  (In the dfs study the same warm-up also failed to settle within its
     *  cap, because that library's depth-first iterator is quadratic on a
     *  deep random graph; here the old warm-up took some eight seconds,
     *  most of it waiting for a compiler counter that creeps by a
     *  millisecond a round.)
     *
     *  So the warm-up runs the measured call on the measured input.  The code
     *  the clock then sees is compiled against exactly the profile it runs
     *  with, which is the steady state a JIT benchmark is meant to report.
     *  HotSpot specialises on frequencies, not on values; nothing of the
     *  answer survives a round.
     *
     *  Bounded, so that the warm-up can never take longer than it did before:
     *  an instance over WARM_ARCS arcs is warmed on its own induced subgraph
     *  on the first n' nodes, n' the largest power of two for which that
     *  subgraph fits the budget, searched from node 0.  Beyond the budget the
     *  measured solve is seconds to minutes, next to which a shape mismatch
     *  costs nothing visible. */
    static void warmUp(int n, List<Triple<Integer, Integer, Double>> edges, int si, int ti) {
        List<Triple<Integer, Integer, Double>> es = edges;
        int wn = n, ws = si, wt = ti;
        if (edges.size() > WARM_ARCS) {
            // one pass: how many arcs have both ends below each power of two
            int[] hist = new int[33];
            for (Triple<Integer, Integer, Double> p : edges) {
                int hi = Math.max(p.getFirst(), p.getSecond());
                hist[32 - Integer.numberOfLeadingZeros(hi)]++;   // floor(log2)+1
            }
            long cum = 0; int k = 0;
            for (int j = 0; j < 33; j++) {
                if (cum + hist[j] > WARM_ARCS) break;
                cum += hist[j]; k = j;
            }
            wn = Math.max(1, 1 << k);                 // nodes 0 .. wn-1
            es = new ArrayList<>((int) cum);
            for (Triple<Integer, Integer, Double> p : edges)
                if (p.getFirst() < wn && p.getSecond() < wn) es.add(p);
            ws = 0; wt = wn - 1;
        }
        long sink = 0;

        // Run the entry point until running it no longer provokes the
        // compiler, then once more to be sure.
        //
        // WHY THE CONDITION IS THIS ONE.  A fixed number of repetitions is not
        // enough.  HotSpot compiles in the BACKGROUND: a warm-up loop only
        // puts methods on the compiler's queue, and the queue goes on draining
        // afterwards, on other threads.  The thread clock does not count the
        // compiler, but the measured thread has to RUN compiled code, and a
        // method the compiler has not finished with yet runs in the
        // interpreter or at a lower tier.  So the test is the one that
        // matters: go round again until a WHOLE solve() adds no more than
        // WARM_SLACK_MS to the compiler's total, twice running.  (Strict
        // equality was tried: the counter creeps by a millisecond or two a
        // round for a long time, and a run spent thirty rounds waiting for
        // two consecutive zeros.)
        //
        // The caps are there so that a JVM which never settles starts the run
        // anyway rather than hanging it.
        java.lang.management.CompilationMXBean cmp =
            ManagementFactory.getCompilationMXBean();
        boolean canWatch = cmp != null && cmp.isCompilationTimeMonitoringSupported();
        int quiet = 0;
        long deadline = System.nanoTime() + WARM_CAP_S * 1_000_000_000L;
        long work = 0;                                    // ns spent in rounds
        // A quiet compiler is necessary but not sufficient.  HotSpot's top
        // tier is reached by COUNTING invocations and back edges, and a small
        // instance gives few per round: measured on a 1024-node instance, the
        // counter went quiet after four rounds with the hot code still in the
        // profiled tier, reading 70 ms, and reached its 34 ms steady state
        // only after some twenty rounds, about a second of work.  So the
        // rounds also have to add up to WARM_FLOOR_S of solving before quiet
        // is believed.  A round that is long is its own floor.
        for (int i = 0; i < WARM_MAX_REPS
                 && !(quiet >= WARM_QUIET && work >= WARM_FLOOR_S * 1_000_000_000L);
             i++) {
            long before = canWatch ? cmp.getTotalCompilationTime() : 0;
            long r0 = System.nanoTime();
            GraphPath<Integer, Integer> p = solve(wn, es, ws, wt).path;
            if (p != null) sink += p.getEdgeList().size();
            work += System.nanoTime() - r0;
            settleJit(cmp, canWatch);
            long after = canWatch ? cmp.getTotalCompilationTime() : 0;
            quiet = (canWatch && after - before <= WARM_SLACK_MS) ? quiet + 1 : 0;
            if (System.nanoTime() > deadline) break;
            if (!canWatch && i >= WARM_MIN_REPS) break;
        }
        if (sink < 0) System.err.println("unreachable");   // keep it alive
    }
    static final int WARM_SLACK_MS = 4;     // compiler creep that counts as quiet
    static final int WARM_FLOOR_S = 2;      // least solving before quiet counts

    /** Wait for the compiler's queue to drain: return once its total time has
     *  not moved for five polls in a row, ten milliseconds of silence.  (The
     *  dfs driver polls every 10 ms; here it is every 2 ms, because a
     *  1024-node Dijkstra round is a millisecond and two hundred rounds of
     *  waiting fifty milliseconds each cost twelve seconds a process.)
     *
     *  A YIELDING SPIN, NOT A SLEEP.  The box runs schedutil on acpi-cpufreq
     *  and a core that sleeps is clocked down within milliseconds (1.8 GHz
     *  idle against 3.9 GHz under load).  A warm-up that slept between rounds
     *  handed the measured call a cold core: the same instance read 75 ms
     *  after a sleeping warm-up and 34 ms after a spinning one.  Yielding
     *  still gives the compiler thread the core whenever it is runnable. */
    static void settleJit(java.lang.management.CompilationMXBean c, boolean can) {
        if (!can) return;
        long last = -1;
        int quiet = 0;
        for (int i = 0; i < 1500 && quiet < 5; i++) {      // at most ~3 s
            long t = c.getTotalCompilationTime();
            quiet = (t == last) ? quiet + 1 : 0;
            last = t;
            long until = System.nanoTime() + 2_000_000L;
            while (System.nanoTime() < until) Thread.yield();
        }
    }

    // ---------- main ----------

    public static void main(String[] args) throws Exception {
        String path = null, tag = "";
        int src = -1, dst = -1, qid = 0;
        int repeats = 1;
        boolean csv = true;

        for (int i = 0; i < args.length; i++) {
            String a = args[i];
            if (a.equals("--header")) { System.out.println(HEADER); return; }
            else if (a.equals("--csv")) csv = true;
            else if (a.equals("--human")) csv = false;
            else if (a.equals("--source") && i + 1 < args.length) src = Integer.parseInt(args[++i]);
            else if (a.equals("--target") && i + 1 < args.length) dst = Integer.parseInt(args[++i]);
            else if (a.equals("--query") && i + 1 < args.length) qid = Integer.parseInt(args[++i]);
            else if (a.equals("--tag") && i + 1 < args.length) tag = args[++i];
            else if (a.equals("--repeats") && i + 1 < args.length)
                repeats = Integer.parseInt(args[++i]);
            else if (a.startsWith("--")) die("unknown option " + a);
            else path = a;
        }
        if (path == null) die("an instance is required");
        if (src < 0) die("a --source is required");
        if (dst < 0) die("a --target is required");
        if (repeats < 1) die("--repeats must be at least 1");

        // ---- 1. parse ----
        long t0 = threadCpuNanos();
        Instance in = parseGr(path);
        long t1 = threadCpuNanos();
        // ---- 2. repack into the library's input format (NOT its structure) ----
        List<Triple<Integer, Integer, Double>> edges = edgeList(in);
        long t2 = threadCpuNanos();

        String base = new File(path).getName();
        StringBuilder out = new StringBuilder();

        {
            if (src < 1 || src > in.nNodes || dst < 1 || dst > in.nNodes)
                die("query " + qid + ": (" + src + ", " + dst + ") outside [1, "
                    + in.nNodes + "]");
            int si = src - 1, ti = dst - 1;
            // ---- 3. warm up, on this very input ----
            warmUp(in.nNodes, edges, si, ti);
            for (int rep = 1; rep <= repeats; rep++) {
                // The previous repeat's graph is unreachable by now.  Ask for
                // it to be reclaimed HERE, outside the clock, so that the cost
                // of reclaiming it is not charged to the next measurement.
                System.gc();

                // ---- 4. clock ----
                long p0 = procNanos();
                long j0 = jitMs();
                long g0 = gcNanos();
                long u0 = threadUserNanos();
                long c0 = threadCpuNanos();
                long w0 = System.nanoTime();

                // ---- 5. build the CSR graph, then solve ----
                // Both are inside the clock on purpose.  The graph is built
                // here because a CSR graph cannot be built while the file is
                // being read, so its build is a separate pass exactly as our
                // export's is; and the Algorithm object with its arrays is
                // constructed by getPath, which is this algorithm's own
                // setup, which our export cannot put outside either.
                Answer ans = solve(in.nNodes, edges, si, ti);

                // ---- 6. clock ----
                long w1 = System.nanoTime();
                long c1 = threadCpuNanos();
                long u1 = threadUserNanos();
                long g1 = gcNanos();
                long j1 = jitMs();
                long p1 = procNanos();

                // ---- 7. the answer, after the clock ----
                GraphPath<Integer, Integer> path2 = ans.path;
                String status = "UNREACHABLE";
                int reached = 0, hops = 0;
                long dist = -1;
                if (path2 != null) {
                    hops = path2.getEdgeList().size();
                    long d = 0;
                    for (Integer e : path2.getEdgeList())
                        d += Math.round(ans.g.getEdgeWeight(e));
                    boolean okEnds = hops == 0
                        || (path2.getStartVertex() == si && path2.getEndVertex() == ti);
                    status = okEnds ? "OPTIMAL" : "BAD_PATH";
                    reached = 1;
                    dist = d;
                }

                long thrNs = c1 - c0, gcNs = g1 - g0;
                long cpuNs = thrNs + gcNs;                 // THE MEASUREMENT
                // the two parts of the clocked period; they add up to cpuNs
                long buildNs = (midCpuNs - c0) + (midGcNs - g0);
                long solveNs = (c1 - midCpuNs) + (g1 - midGcNs);
                long usrNs = (u1 - u0) + gcNs, sysNs = thrNs - (u1 - u0);
                if (csv)
                    out.append(String.join(",",
                        base, Integer.toString(in.nNodes), Integer.toString(in.nArcs),
                        Integer.toString(qid), Integer.toString(src),
                        Integer.toString(dst), Integer.toString(rep),
                        status, Integer.toString(reached), Integer.toString(hops),
                        Long.toString(dist),
                        ms(cpuNs), ms(usrNs), ms(sysNs), ms(p1 - p0),
                        ms(w1 - w0),
                        ms(t1 - t0), "0.000", ms(t2 - t1),
                        ms(buildNs), ms(solveNs), tag)).append('\n');
                else
                    out.append(String.format(
                        "query %d  %d -> %d  rep %d%n  status   %s%n  hops     %d%n"
                        + "  dist     %d%n"
                        + "  cpu      %s ms   (the measurement: thread + collector,%n"
                        + "                     build and solve together)%n"
                        + "  of which %s ms was garbage collection%n"
                        + "  wall     %s ms%n"
                        + "  proc     %s ms   (whole process, 10 ms ticks: + the JIT,%n"
                        + "                     which compiled for %d ms)%n",
                        qid, src, dst, rep, status, hops, dist,
                        ms(cpuNs), ms(gcNs), ms(w1 - w0), ms(p1 - p0), j1 - j0));
                System.out.print(out);
                out.setLength(0);
                System.out.flush();
            }
        }
    }
}
