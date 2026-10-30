// Benchmark driver for JGraphT's depth-first search on DIMACS .gr instances.
//
//   run.sh [options] <instance.gr>
//
// Shape of a run, in this order:
//
//   1. parse the .gr file                                  (clocked, reported)
//   2. build the JGraphT graph                             (clocked, reported)
//   3. warm up: search a small grid several times          (not measured)
//   4. read the clock
//   5. drain a DepthFirstIterator from the source
//   6. read the clock again
//   7. report the difference, plus the answer for checking
//
// Only step 5 sits between the two clock reads.  Steps 1 and 2 are outside it
// because for an unverified library the structure build fuses with parsing --
// a solver like this one would normally read the file straight into its own
// graph.  That is not possible for verified exported code, which is handed
// plain arrays and builds its own structures inside the entry point, so for
// our exports the build is inside the clock.  The asymmetry is inherent and it
// favours this library, which needs it: building the graph is by far the
// slowest thing this driver does.  Both are clocked and reported anyway, in
// parse_ms and build_ms, so what sits outside the measurement is visible
// rather than merely asserted.  dedup_ms is 0.000: a pseudograph takes
// parallel arcs as they come.
//
// IT SWEEPS EVERYTHING REACHABLE FROM THE SOURCE, AND NOTHING ELSE.  The
// iterator is drained to exhaustion, so there is no early exit -- our exports
// are given a target the graph does not contain and never stop early either.
// But JGraphT's iterators traverse ACROSS components by default: when the
// start component runs dry they pick an unvisited vertex anywhere in the
// graph and carry on, which would make this solver do strictly more work than
// everyone else.  setCrossComponentTraversal(false) stops that, so what is
// measured is one depth-first search from s over exactly the region reachable
// from s.
//
// THE CROSS-CHECK IS THE NUMBER OF VERTICES VISITED.  The order the vertices
// come out in is a property of the implementation -- JGraphT's depth-first
// order is not our export's -- but HOW MANY come out is a property of the
// graph and the source alone.  So `visited' is the column the solvers are
// checked against each other on, and here it is simply how many vertices the
// drained iterator produced.
//
// WEIGHTS ARE PARSED AND THEN IGNORED.  The instances are the shortest-path
// challenge's own, so that a DFS row, a BFS row and a Dijkstra row can be read
// side by side on the same graph, but depth-first search has no use for the
// third field of an arc line and the graph carries no weights.
//
// ONE PROBLEM PER PROCESS.  The source is given on the command line and
// exactly one is accepted: a search problem is a graph AND a source, so two
// sources are two problems and must not share a solver call, a solver object,
// or a process.  There is deliberately no way to hand this driver a list of
// sources.
//
// THE TARGET MUST NOT BE A VERTEX.  It is carried on the command line only so
// that every driver in the study takes the same arguments, and this one
// refuses anything inside [1, n], exactly as the exports' drivers do.
//
// The algorithm's OWN setup is inside the clock here, as it is for ours and
// for LEMON: the DepthFirstIterator is CONSTRUCTED inside the clock, so the
// map of per-vertex search data it fills as it goes is allocated inside the
// measurement, not before it.
//
// THE WARM-UP.  Before the first measured call the same entry point is run on
// a small grid, several times, and the answers thrown away.  Without it the
// first measurement is an interpreter measurement: HotSpot starts in the
// interpreter and only compiles a method once it has been entered enough
// times.  MLton, Go and g++ are compiled ahead of time and have no such phase,
// so timing a cold JVM would not be comparing the same thing.  The grid is
// four-connected, so the warm-up is the same work on every run of every
// instance and cannot vary one measurement against another.
//
// THE GRAPH TYPE.  DirectedPseudograph, because the road networks have
// parallel arcs -- USA-road-t.NY alone has 3724 node pairs carrying two or
// three arcs.  A DefaultDirectedGraph would silently refuse the second arc of
// each pair.  For depth-first search that would change no reachable set, but
// it would change how much work the solver does, and the other solvers are
// not given that discount.  Unweighted: DefaultEdge, no edge weights at all.
//
// THE COST THIS LIBRARY CARRIES.  DepthFirstIterator is generic over the
// vertex type, so the search data lives in a HashMap keyed by boxed Integers
// rather than in an array indexed by vertex id.  That is the library as a user
// of the library gets it, and it is left alone rather than hand-tuned.

import java.io.IOException;
import java.io.File;
import java.lang.management.ManagementFactory;
import java.lang.management.ThreadMXBean;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;

import org.jgrapht.graph.DefaultEdge;
import org.jgrapht.graph.DirectedPseudograph;
import org.jgrapht.traverse.DepthFirstIterator;

public final class JGraphTDfs {

    static final String HEADER =
        "instance,nodes,arcs,query,source,target,repeat,status," +
        "reached,visited,cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms," +
        "parse_ms,dedup_ms,build_ms,tag";

    static final ThreadMXBean THREADS = ManagementFactory.getThreadMXBean();
    static com.sun.management.OperatingSystemMXBean OS =
        ManagementFactory.getPlatformMXBean(com.sun.management.OperatingSystemMXBean.class);

    // The whole process, in 10 ms ticks out of /proc/self/stat.
    static long procNanos() { return OS.getProcessCpuTime(); }
    // The calling thread alone, in nanoseconds.
    static long threadCpuNanos() { return THREADS.getCurrentThreadCpuTime(); }
    static long threadUserNanos() { return THREADS.getCurrentThreadUserTime(); }

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

    static DirectedPseudograph<Integer, DefaultEdge> build(Instance in) {
        DirectedPseudograph<Integer, DefaultEdge> g =
            new DirectedPseudograph<>(DefaultEdge.class);
        for (int v = 0; v < in.nNodes; v++) g.addVertex(v);
        for (int i = 0; i < in.nArcs; i++) g.addEdge(in.from[i], in.to[i]);
        return g;
    }

    /** One depth-first search from `si', to exhaustion, cross-component
     *  traversal off.  Returns how many vertices it settled. */
    static int dfs(DirectedPseudograph<Integer, DefaultEdge> g, int si) {
        DepthFirstIterator<Integer, DefaultEdge> it =
            new DepthFirstIterator<>(g, Integer.valueOf(si));
        it.setCrossComponentTraversal(false);
        int seen = 0;
        while (it.hasNext()) { it.next(); seen++; }
        return seen;
    }

    // ---------- the warm-up ----------

    //: Side of the warm-up grid and how many times it is searched.  Both are
    //: deliberately small: the warm-up is wall time spent inside the per-run
    //: cap without being measured, so it has to be worth its cost.  Twenty
    //: searches of a 32x32 grid drives the iterator and its hash map well
    //: past HotSpot's compilation threshold.
    static final int WARM_SIDE = 32;
    static final int WARM_REPS = 20;

    static void warmUp() {
        int k = WARM_SIDE;
        int n = k * k;
        DirectedPseudograph<Integer, DefaultEdge> g =
            new DirectedPseudograph<>(DefaultEdge.class);
        for (int v = 0; v < n; v++) g.addVertex(v);
        for (int r = 0; r < k; r++) {
            for (int c = 0; c < k; c++) {
                int id = r * k + c;
                if (c + 1 < k) { g.addEdge(id, id + 1); g.addEdge(id + 1, id); }
                if (r + 1 < k) { g.addEdge(id, id + k); g.addEdge(id + k, id); }
            }
        }
        long sink = 0;
        for (int i = 0; i < WARM_REPS; i++)
            sink += dfs(g, 0);
        if (sink < 0) System.err.println("unreachable");   // keep it alive
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
        // ---- 2. build ----
        DirectedPseudograph<Integer, DefaultEdge> g = build(in);
        long t2 = threadCpuNanos();
        // ---- 3. warm up ----
        warmUp();

        String base = new File(path).getName();
        StringBuilder out = new StringBuilder();

        {
            if (src < 1 || src > in.nNodes)
                die("query " + qid + ": source " + src + " outside [1, "
                    + in.nNodes + "]");
            if (dst >= 1 && dst <= in.nNodes)
                die("query " + qid + ": target " + dst + " IS a node of this "
                    + "graph; this study searches the whole graph and needs a "
                    + "target outside [1, " + in.nNodes + "]");
            int si = src - 1;
            for (int rep = 1; rep <= repeats; rep++) {
                // ---- 4. clock ----
                long p0 = procNanos();
                long u0 = threadUserNanos();
                long c0 = threadCpuNanos();
                long w0 = System.nanoTime();

                // ---- 5. search ----
                // The iterator is built inside the clock on purpose: the map
                // of per-vertex search data it fills is this algorithm's own
                // setup, and our exports cannot put theirs outside either.
                int visited = dfs(g, si);

                // ---- 6. clock ----
                long w1 = System.nanoTime();
                long c1 = threadCpuNanos();
                long u1 = threadUserNanos();
                long p1 = procNanos();

                // ---- 7. the answer, after the clock ----
                // The target is not a vertex of the graph, so `reached' is 0
                // and the sweep is known to have run to exhaustion.
                long cpuNs = c1 - c0, usrNs = u1 - u0;
                if (csv)
                    out.append(String.join(",",
                        base, Integer.toString(in.nNodes), Integer.toString(in.nArcs),
                        Integer.toString(qid), Integer.toString(src),
                        Integer.toString(dst), Integer.toString(rep),
                        "OK", "0", Integer.toString(visited),
                        ms(cpuNs), ms(usrNs), ms(cpuNs - usrNs), ms(p1 - p0),
                        ms(w1 - w0),
                        ms(t1 - t0), "0.000", ms(t2 - t1), tag)).append('\n');
                else
                    out.append(String.format(
                        "query %d  source %d  rep %d%n  status   OK%n"
                        + "  visited  %d%n  cpu      %s ms   (the measurement)%n"
                        + "  proc     %s ms   (whole process: + the JIT)%n"
                        + "  wall     %s ms%n",
                        qid, src, rep, visited,
                        ms(cpuNs), ms(p1 - p0), ms(w1 - w0)));
                System.out.print(out);
                out.setLength(0);
                System.out.flush();
            }
        }
    }
}
