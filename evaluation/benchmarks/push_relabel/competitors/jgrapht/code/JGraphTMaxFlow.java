/* Reference solver for the push-relabel study: JGraphT's PushRelabelMFImpl.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .max file                                 (clocked, reported)
 *   2. build the JGraphT graph                             (clocked, reported)
 *   3. warm up: solve a small network several times        (not measured)
 *   4. read the clock
 *   5. construct PushRelabelMFImpl and call getMaximumFlow
 *   6. read the clock again
 *   7. check the flow and read its value                   (after the clock)
 *
 * Only step 5 sits between the two clock reads.  Steps 1 and 2 are outside it
 * because for an unverified library the structure build fuses with parsing --
 * a solver like this one would normally read the file straight into its own
 * graph.  That is not possible for verified exported code, which is handed
 * plain arrays and builds its own structures inside the entry point, so for
 * our export the build is inside the clock.  The asymmetry is inherent and it
 * favours this library, which needs it: building the graph is by far the
 * slowest thing this driver does.  Both are clocked and reported anyway, in
 * parse_ms and build_ms, so what sits outside the measurement is visible
 * rather than merely asserted.  dedup_ms is 0.000: a weighted pseudograph
 * takes parallel arcs as they come, exactly as our export and LEMON do.
 *
 * A MAXIMUM FLOW, NOT A MAXIMUM PREFLOW.  getMaximumFlow returns the flow on
 * every arc, and the implementation runs to exhaustion to produce it: its
 * enqueue has no height cut-off, so any vertex carrying excess is queued
 * whatever its label, and the loop ends only when none is left.  That is the
 * one-phase algorithm, and what it ends with is a flow.  Our export does the
 * same.  The flow is checked below rather than taken on trust.
 *
 * THE WARM-UP.  Before the measured call the same entry point is run on a
 * small network, several times, and the answers thrown away.  Without it the
 * first measurement is an interpreter measurement: HotSpot starts in the
 * interpreter and only compiles a method once it has been entered enough
 * times.  MLton, Go and g++ are compiled ahead of time and have no such
 * phase, so timing a cold JVM would not be comparing the same thing.  The
 * warm-up network is a small capacitated layered graph from a fixed seed, not
 * a plain traversal, so that the push, the relabel, the gap heuristic and the
 * global relabelling all get compiled; and it is the same work on every run of
 * every instance, so it cannot vary one measurement against another.  It is
 * deliberately small: warm-up is wall time spent inside the per-run cap
 * without being measured, so it has to be worth its cost.
 *
 * THE HEURISTIC FLAGS ARE LEFT ALONE.  PushRelabelMFImpl exposes
 * USE_GLOBAL_RELABELING_HEURISTIC and USE_GAP_RELABELING_HEURISTIC as static
 * switches.  Both keep their shipped defaults: this is the library as a user
 * of the library gets it, not a hand-tuned version of it.
 *
 * THE VALUE IS READ AFTER THE CLOCK, as a cross-reference between the thirteen
 * solvers and nothing more; the measurement is the flow computation alone,
 * with no summing up inside it.
 *
 * ONE PROBLEM PER PROCESS.  The source and the sink come from the file's own
 * `n' designator lines unless given on the command line, and there is
 * deliberately no way to hand this driver a second pair.
 */

import java.io.IOException;
import java.io.File;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Map;

import org.jgrapht.alg.flow.PushRelabelMFImpl;
import org.jgrapht.alg.interfaces.MaximumFlowAlgorithm;
import org.jgrapht.graph.DefaultWeightedEdge;
import org.jgrapht.graph.DirectedWeightedPseudograph;

public final class JGraphTMaxFlow {

    static final String HEADER =
        "instance,nodes,arcs,variant,source,target,repeat,status," +
        "flow_value,cpu_ms,cpu_usr_ms,cpu_sys_ms,thread_ms,wall_ms," +
        "parse_ms,dedup_ms,build_ms,tag";

    static final ThreadMXBean THREADS = ManagementFactory.getThreadMXBean();
    static com.sun.management.OperatingSystemMXBean OS =
        ManagementFactory.getPlatformMXBean(com.sun.management.OperatingSystemMXBean.class);

    static long threadCpuNanos() { return THREADS.getCurrentThreadCpuTime(); }

    /* WHOLE-PROCESS CPU, user and system, in nanoseconds.
     *
     * This is the measurement, and it is the same quantity getrusage(RUSAGE_SELF)
     * gives the SML, C++, Go and Python drivers.  It is NOT read from
     * ThreadMXBean, and the difference is not a detail: HotSpot's serial
     * collector runs on the VM thread rather than on the thread that allocated,
     * so a per-thread clock drops every collection on the floor.  On one Scala
     * run of ak-4102 the solver thread showed 7.2 seconds while the process had
     * burned 21.6, the missing 14.3 being garbage collection the generated code
     * had caused.  The JIT compiler threads are outside the thread clock for the
     * same reason.  thread_ms keeps the per-thread figure alongside, so the gap
     * stays visible rather than being assumed away.
     *
     * /proc/self/stat fields 14 and 15, in clock ticks of 10 ms.  Coarse, but
     * the runs that matter here are seconds to minutes long, and it is the only
     * way to get the user/system split of the whole process from a JVM. */
    static long[] procUserSysNanos() {
        try {
            String s = new String(Files.readAllBytes(Paths.get("/proc/self/stat")),
                                  java.nio.charset.StandardCharsets.US_ASCII);
            int rp = s.lastIndexOf(')');        /* comm itself may hold parens */
            String[] f = s.substring(rp + 2).trim().split("\\s+");
            long tick = 10_000_000L;            /* 100 Hz, checked with getconf */
            return new long[] { Long.parseLong(f[11]) * tick,
                                Long.parseLong(f[12]) * tick };
        } catch (IOException e) {
            long c = OS.getProcessCpuTime();
            return new long[] { c, 0L };
        }
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
        int source = -1;        // 0-based
        int sink = -1;          // 0-based
        int[] from;             // 0-based
        int[] to;               // 0-based
        long[] cap;
    }

    /** DIMACS .max reader.  A transcription of the SML reader in
     *  drivers/sml/max_parser.sml, so the drivers see the same arcs. */
    static Instance parseMax(String path) throws IOException {
        byte[] s = Files.readAllBytes(Paths.get(path));
        Instance in = new Instance();
        in.nNodes = -1;
        int[] from = new int[16];
        int[] to = new int[16];
        long[] cp = new long[16];
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
            if (kind == 'n') {                       // `n <id> s' or `n <id> t'
                while (p < s.length && (s[p] == ' ' || s[p] == '\t')) p++;
                long v = 0;
                while (p < s.length && s[p] >= '0' && s[p] <= '9') {
                    v = v * 10 + (s[p] - '0'); p++;
                }
                while (p < s.length && (s[p] == ' ' || s[p] == '\t')) p++;
                if (p < s.length && s[p] == 's') in.source = (int) v - 1;
                else if (p < s.length && s[p] == 't') in.sink = (int) v - 1;
                else die(path + ": node line is neither s nor t");
                while (p < s.length && s[p] != '\n') p++;
                if (p < s.length) p++;
                continue;
            }
            long[] f = new long[3];
            int nf = 0;
            boolean wantTag = (kind == 'p');
            while (p < s.length && s[p] != '\n' && nf < 3) {
                while (p < s.length && (s[p] == ' ' || s[p] == '\t')) p++;
                if (p >= s.length || s[p] == '\n' || s[p] == '\r') break;
                if (wantTag && !(s[p] >= '0' && s[p] <= '9')) {
                    while (p < s.length && s[p] != ' ' && s[p] != '\t'
                           && s[p] != '\n') p++;
                    wantTag = false;
                    continue;
                }
                if (!(s[p] >= '0' && s[p] <= '9')) break;
                long v = 0;
                while (p < s.length && s[p] >= '0' && s[p] <= '9') {
                    v = v * 10 + (s[p] - '0'); p++;
                }
                f[nf++] = v;
            }
            while (p < s.length && s[p] != '\n') p++;
            if (p < s.length) p++;

            if (kind == 'p') {
                if (nf < 2) die(path + ": bad `p' line");
                in.nNodes = (int) f[0];
                int cap = Math.max((int) Math.min(f[1], Integer.MAX_VALUE - 8), 16);
                from = new int[cap]; to = new int[cap]; cp = new long[cap];
            } else if (kind == 'a') {
                if (nf < 3) die(path + ": bad `a' line");
                if (in.nNodes < 0) die(path + ": arc line before the `p max' line");
                if (m == from.length) {
                    int cap = from.length + (from.length >> 1) + 16;
                    from = java.util.Arrays.copyOf(from, cap);
                    to = java.util.Arrays.copyOf(to, cap);
                    cp = java.util.Arrays.copyOf(cp, cap);
                }
                from[m] = (int) f[0] - 1;
                to[m] = (int) f[1] - 1;
                cp[m] = f[2];
                m++;
            }
        }
        if (in.nNodes < 0) die(path + ": no `p max' line");
        if (in.source < 0 || in.sink < 0) die(path + ": no source or no sink line");
        in.nArcs = m;
        in.from = java.util.Arrays.copyOf(from, m);
        in.to = java.util.Arrays.copyOf(to, m);
        in.cap = java.util.Arrays.copyOf(cp, m);
        return in;
    }

    static DirectedWeightedPseudograph<Integer, DefaultWeightedEdge> build(Instance in) {
        DirectedWeightedPseudograph<Integer, DefaultWeightedEdge> g =
            new DirectedWeightedPseudograph<>(DefaultWeightedEdge.class);
        for (int v = 0; v < in.nNodes; v++) g.addVertex(v);
        for (int i = 0; i < in.nArcs; i++) {
            DefaultWeightedEdge e = g.addEdge(in.from[i], in.to[i]);
            if (e != null) g.setEdgeWeight(e, (double) in.cap[i]);
        }
        return g;
    }

    /** The call that will be measured.  Written here rather than inline so
     *  that the warm-up below goes through the very same line of code, and a
     *  warm-up can never drift away from the thing it is warming. */
    static MaximumFlowAlgorithm.MaximumFlow<DefaultWeightedEdge> solve(
            DirectedWeightedPseudograph<Integer, DefaultWeightedEdge> g,
            int s, int t) {
        PushRelabelMFImpl<Integer, DefaultWeightedEdge> alg =
            new PushRelabelMFImpl<>(g);
        return alg.getMaximumFlow(Integer.valueOf(s), Integer.valueOf(t));
    }

    // ---------- the warm-up ----------

    //: Shape of the warm-up network and how many times it is solved.  Both are
    //: deliberately small: the warm-up is wall time spent inside the per-run
    //: cap without being measured, so it has to be worth its cost.  Ten solves
    //: of a 24-level, 16-wide capacitated network drives the push, the
    //: relabel, the gap heuristic and the global relabelling well past
    //: HotSpot's compilation threshold.
    static final int WARM_WIDTH = 16;
    static final int WARM_LEVELS = 24;
    static final int WARM_REPS = 10;

    static void warmUp() {
        int w = WARM_WIDTH, L = WARM_LEVELS;
        int n = w * L + 2;
        int source = 0, sink = n - 1;
        DirectedWeightedPseudograph<Integer, DefaultWeightedEdge> g =
            new DirectedWeightedPseudograph<>(DefaultWeightedEdge.class);
        for (int v = 0; v < n; v++) g.addVertex(v);
        long seed = 12345L;
        // a fixed-seed generator, so the warm-up is the same work every time
        java.util.function.LongSupplier next = new java.util.function.LongSupplier() {
            long s = 12345L;
            public long getAsLong() {
                s = s * 6364136223846793005L + 1442695040888963407L;
                return ((s >>> 33) % 1000L) + 1L;
            }
        };
        for (int j = 1; j <= w; j++) {
            DefaultWeightedEdge e = g.addEdge(source, j);
            if (e != null) g.setEdgeWeight(e, 3000.0);
            DefaultWeightedEdge f = g.addEdge((L - 1) * w + j, sink);
            if (f != null) g.setEdgeWeight(f, 3000.0);
        }
        for (int i = 0; i < L - 1; i++) {
            for (int j = 1; j <= w; j++) {
                int u = i * w + j;
                for (int k = 0; k < 3; k++) {
                    int v = (i + 1) * w + 1 + (int) ((u * 7L + k * 13L) % w);
                    DefaultWeightedEdge e = g.addEdge(u, v);
                    if (e != null) g.setEdgeWeight(e, (double) next.getAsLong());
                }
            }
        }
        double sink2 = 0;
        for (int i = 0; i < WARM_REPS; i++) sink2 += solve(g, source, sink).getValue();
        if (sink2 < 0) System.err.println("impossible");   // keep it alive
    }

    // ---------- main ----------

    public static void main(String[] args) throws Exception {
        String path = null, tag = "";
        int src = -1, dst = -1;
        int repeats = 1;
        boolean csv = true;

        for (int i = 0; i < args.length; i++) {
            String a = args[i];
            if (a.equals("--header")) { System.out.println(HEADER); return; }
            else if (a.equals("--csv")) csv = true;
            else if (a.equals("--human")) csv = false;
            else if (a.equals("--source") && i + 1 < args.length) src = Integer.parseInt(args[++i]);
            else if (a.equals("--target") && i + 1 < args.length) dst = Integer.parseInt(args[++i]);
            else if (a.equals("--tag") && i + 1 < args.length) tag = args[++i];
            else if (a.equals("--repeats") && i + 1 < args.length) {
                repeats = Integer.parseInt(args[++i]);
                if (repeats < 1) die("--repeats must be at least 1");
            } else if (a.startsWith("--")) {
                System.err.println(
                    "usage: JGraphTMaxFlow [options] <instance.max>\n" +
                    "  --source <v>       the source, a DIMACS node id (1-based).\n" +
                    "                     Defaults to the file's own `n <id> s' line.\n" +
                    "  --target <v>       the sink, likewise, from `n <id> t'\n" +
                    "  --repeats <k>      solve the SAME problem k times (default 1)\n" +
                    "  --header           print the CSV header line and exit\n" +
                    "  --csv              print one CSV row per repeat (default)\n" +
                    "  --human            print a human-readable block instead\n" +
                    "  --tag <s>          free-form label copied into the `tag' column");
                System.exit(1);
            } else path = a;
        }
        if (path == null) die("an instance is required");

        // ---- 1. parse ----
        long t0 = threadCpuNanos();
        Instance in = parseMax(path);
        long t1 = threadCpuNanos();
        // ---- 2. build ----
        DirectedWeightedPseudograph<Integer, DefaultWeightedEdge> g = build(in);
        long t2 = threadCpuNanos();
        // ---- 3. warm up ----
        warmUp();

        int si = (src < 0) ? in.source : src - 1;
        int ti = (dst < 0) ? in.sink : dst - 1;
        if (si < 0 || si >= in.nNodes || ti < 0 || ti >= in.nNodes)
            die("source or sink outside [1, " + in.nNodes + "]");
        if (si == ti) die("source and sink are the same vertex");

        String base = new File(path).getName();

        for (int rep = 1; rep <= repeats; rep++) {
            // ---- 4. clock ----
            long[] q0 = procUserSysNanos();
            long c0 = threadCpuNanos();
            long w0 = System.nanoTime();

            // ---- 5. the library ----
            MaximumFlowAlgorithm.MaximumFlow<DefaultWeightedEdge> res =
                solve(g, si, ti);

            // ---- 6. clock ----
            long w1 = System.nanoTime();
            long c1 = threadCpuNanos();
            long[] q1 = procUserSysNanos();
            long usr = q1[0] - q0[0], sysd = q1[1] - q0[1];
            long cpu = usr + sysd;

            // ---- 7. the answer, after the clock ----
            long value = Math.round(res.getValue());
            Map<DefaultWeightedEdge, Double> fm = res.getFlowMap();
            long[] net = new long[in.nNodes];
            String status = "OK";
            for (Map.Entry<DefaultWeightedEdge, Double> en : fm.entrySet()) {
                DefaultWeightedEdge e = en.getKey();
                long f = Math.round(en.getValue());
                if (f < 0 || f > Math.round(g.getEdgeWeight(e))) {
                    status = "OVER_CAPACITY";
                    break;
                }
                net[g.getEdgeSource(e)] -= f;
                net[g.getEdgeTarget(e)] += f;
            }
            if (status.equals("OK")) {
                for (int v = 0; v < in.nNodes; v++)
                    if (v != si && v != ti && net[v] != 0) { status = "NOT_A_FLOW"; break; }
            }
            if (status.equals("OK") && -net[si] != value) status = "VALUE_MISMATCH";

            if (csv) {
                System.out.println(String.join(",",
                    base, Integer.toString(in.nNodes), Integer.toString(in.nArcs),
                    "jgrapht_push_relabel", Integer.toString(si + 1),
                    Integer.toString(ti + 1), Integer.toString(rep), status,
                    Long.toString(value),
                    ms(cpu), ms(usr), ms(sysd), ms(c1 - c0), ms(w1 - w0),
                    ms(t1 - t0), "0.000", ms(t2 - t1), tag));
            } else {
                System.out.printf(
                    "instance %s  %d nodes, %d arcs%n" +
                    "variant  jgrapht_push_relabel   %d -> %d   rep %d%n" +
                    "flow     %d  (%s)%n" +
                    "cpu      %s ms   wall %s ms   parse %s ms   build %s ms%n",
                    base, in.nNodes, in.nArcs, si + 1, ti + 1, rep,
                    value, status, ms(cpu), ms(w1 - w0),
                    ms(t1 - t0), ms(t2 - t1));
            }
            System.out.flush();
        }
    }
}
