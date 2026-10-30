/* Reference solver for the push-relabel study: Goldberg's hi_pr, version 3.5.
 *
 * WHY THIS SOLVER IS HERE.  Neither of the other two push-relabel codes in
 * this study does periodic global relabelling.  Our export has the highest
 * label rule and the gap heuristic and nothing else; LEMON has the same two
 * (it calls the gap heuristic "bound decrease") plus exact starting labels
 * from one reverse breadth-first sweep in init(), and no periodic update and
 * no setting to ask for one.  hi_pr has all three, and the periodic update is
 * the one that matters most on hard instances.  It is also the code the
 * DIMACS max-flow literature measures against, so it is the right strong
 * opponent rather than a second middling one.
 *
 * GOLDBERG'S SOURCE IS NOT EDITED.  hipr-3.5/ is the 3.5 distribution exactly
 * as it was unpacked; hipr-3.5.tar beside it is the archive, kept so the two
 * can be diffed.  This file includes hi_pr.c with `main' renamed by the
 * preprocessor, so the algorithm -- globalUpdate, gap, relabel, discharge,
 * stageOne, stageTwo, every constant, ALPHA, BETA and GLOB_UPDT_FREQ -- is
 * compiled from his bytes.  What is replaced is the shell around it: his main
 * reads stdin, prints a few `c' lines and times with a float second counter
 * of two decimals, which is too coarse for the small rungs and counts user
 * time only.  Ours takes a file, splits user and system time, and prints the
 * study's CSV row.  Nothing between the clock reads is ours.
 *
 * Shape of a run, in this order:
 *
 *   1. parse the .max file, which also builds his arc arrays  (clocked, shown)
 *   2. read the clock
 *   3. allocDS(), init(), stageOne(), stageTwo()
 *   4. read the clock again
 *   5. check the flow and read its value                      (after the clock)
 *
 * Step 1 is outside the measurement for the same reason it is for LEMON: for
 * an unverified library the structure build fuses with parsing, and here it
 * literally is the same pass -- his parser writes the final node and arc
 * arrays as it reads.  So build_ms is 0.000 and parse_ms carries both; nothing
 * is hidden, it is just not separable.  dedup_ms is 0.000 as well: hi_pr takes
 * parallel arcs as they come, exactly as our export and LEMON do.
 *
 * allocDS() IS INSIDE THE CLOCK, which is stricter than hi_pr's own timing,
 * where it sits outside.  It allocates the bucket array -- the level
 * structure, the algorithm's own working set, not the graph.  LEMON's
 * equivalent allocation happens inside Preflow::init() and is inside the
 * clock there, and our export's is inside its entry point and cannot be
 * lifted out at all.  Treating the three the same way is worth more than
 * reproducing each one's house style.
 *
 * BOTH STAGES.  stageOne() ends with a maximum PREFLOW; stageTwo() turns it
 * into a maximum FLOW.  hi_pr compiled with -DCUT_ONLY skips the second and
 * is much faster, and that is not what the other columns compute, so this
 * driver always runs both and is never built with CUT_ONLY.
 *
 * THE VALUE IS READ AFTER THE CLOCK, as everywhere else: his `flow' global is
 * the sink's excess at the end of stage one, and the arc flows are checked
 * after the clock for capacity and for conservation at every vertex but the
 * two ends, which is what tells a maximum flow from a maximum preflow.
 *
 * ONE PROBLEM PER PROCESS.  The source and the sink come from the file's own
 * `n' designator lines unless given on the command line, and there is no way
 * to hand this driver a second pair.  --repeats is not offered: hi_pr's state
 * is global and consumed by a run, so a second solve in the same process
 * would need the residual capacities restored, which is work this driver
 * would be doing inside nobody's clock.  The campaign gives every repeat its
 * own process in any case.
 *
 * Licence: hi_pr is Copyright (C) 1995-2004 IG Systems, Inc.  Free to use as
 * it stands; commercial use requires a licence.  See hipr-3.5/COPYRIGHT.
 */

#include <sys/resource.h>
#include <time.h>

/* Goldberg's program, his main renamed away.  Everything below the include is
 * ours; everything inside it is his. */
#define main hipr_main_unused
#include "hipr-3.5/hi_pr.c"
#undef main

static const char *HEADER =
  "instance,nodes,arcs,variant,source,target,repeat,status,"
  "flow_value,cpu_ms,cpu_usr_ms,cpu_sys_ms,thread_ms,wall_ms,"
  "parse_ms,dedup_ms,build_ms,tag";

static void die(const char *msg) {
  fprintf(stderr, "%s\n", msg);
  exit(1);
}

/* ---------- clock ----------
 * CPU time (user + system) is the measurement, as everywhere else in this
 * study.  Wall time is recorded as well but nothing is derived from it: the
 * campaign runs several solvers at once, so wall time carries whatever the
 * other runs were doing and CPU time does not. */

static void cpu_now(double *usr_ms, double *sys_ms) {
  struct rusage ru;
  getrusage(RUSAGE_SELF, &ru);
  *usr_ms = ru.ru_utime.tv_sec * 1000.0 + ru.ru_utime.tv_usec / 1000.0;
  *sys_ms = ru.ru_stime.tv_sec * 1000.0 + ru.ru_stime.tv_usec / 1000.0;
}

static double wall_now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec * 1000.0 + ts.tv_nsec / 1000000.0;
}

int main(int argc, char **argv) {
  const char *path = NULL, *tag = "";
  long long src = -1, dst = -1;
  int csv = 1, i;
  double u0, s0, u1, s1;

  globUpdtFreq = GLOB_UPDT_FREQ;      /* hi_pr's own default, 0.5 */

  for (i = 1; i < argc; i++) {
    const char *a = argv[i];
    if (!strcmp(a, "--header")) { printf("%s\n", HEADER); return 0; }
    else if (!strcmp(a, "--csv")) csv = 1;
    else if (!strcmp(a, "--human")) csv = 0;
    else if (!strcmp(a, "--source") && i + 1 < argc) src = atoll(argv[++i]);
    else if (!strcmp(a, "--target") && i + 1 < argc) dst = atoll(argv[++i]);
    else if (!strcmp(a, "--tag") && i + 1 < argc) tag = argv[++i];
    else if (!strcmp(a, "--update-freq") && i + 1 < argc)
      globUpdtFreq = (float) atof(argv[++i]);
    else if (a[0] == '-' && a[1] == '-') {
      fprintf(stderr,
        "usage: solve_hipr [options] <instance.max>\n"
        "  --source <v>       the source, a DIMACS node id (1-based).\n"
        "                     Defaults to the file's own `n <id> s' line.\n"
        "  --target <v>       the sink, likewise, from `n <id> t'\n"
        "  --update-freq <f>  hi_pr's global relabelling frequency\n"
        "                     (default 0.5, his own; larger means more often)\n"
        "  --header           print the CSV header line and exit\n"
        "  --csv              print one CSV row (default)\n"
        "  --human            print a human-readable block instead\n"
        "  --tag <s>          free-form label copied into the `tag' column\n");
      return 1;
    } else path = a;
  }
  if (!path) die("an instance is required");

  {
  const char *base = strrchr(path, '/');
  base = base ? base + 1 : path;

  /* ---- 1. parse, which is also the structure build ---- */
  cpu_now(&u0, &s0);
  if (!freopen(path, "r", stdin)) { perror(path); return 1; }
  if (parse(&n, &m, &nodes, &arcs, &cap, &source, &sink, &nMin) != 0)
    die("hi_pr's parser rejected the instance");
  cpu_now(&u1, &s1);
  {
  double parse_ms = (u1 - u0) + (s1 - s0);

  /* The parser took the source and the sink from the file.  A pair given on
   * the command line overrides it; node v lives at nodes + (v - nMin). */
  if (src < 0) src = (long long)(source - nodes) + nMin;
  if (dst < 0) dst = (long long)(sink   - nodes) + nMin;
  if (src < nMin || src >= nMin + n || dst < nMin || dst >= nMin + n)
    die("source or sink out of range");
  if (src == dst) die("source and sink are the same vertex");
  source = nodes + (src - nMin);
  sink   = nodes + (dst - nMin);

  {
  /* ---- 2. clock ---- */
  double w0 = wall_now_ms();
  cpu_now(&u0, &s0);

  /* ---- 3. hi_pr, whole: its own setup, then both stages ---- */
  if (allocDS()) { fprintf(stderr, "Out of memory\n"); return 1; }
  init();
  stageOne();
  stageTwo();

  /* ---- 4. clock ---- */
  cpu_now(&u1, &s1);
  {
  double w1 = wall_now_ms();
  double usr_ms = u1 - u0, sys_ms = s1 - s0;
  double cpu_ms = usr_ms + sys_ms, wall_ms = w1 - w0;

  /* ---- 5. the answer, after the clock ---- */
  long long value = (long long) flow;
  const char *status = "OK";
  long long *net = (long long *) calloc((size_t) n + 2, sizeof(long long));
  node *v;
  arc *a;
  if (!net) { fprintf(stderr, "Out of memory\n"); return 1; }

  forAllNodes(v) {
    forAllArcs(v, a) {
      if (cap[a - arcs] > 0) {               /* an arc of the input */
        long long c = (long long) cap[a - arcs];
        long long f = c - (long long) a->resCap;
        if (f < 0 || f > c ||
            (long long) a->resCap + (long long) a->rev->resCap != c) {
          status = "OVER_CAPACITY";
          goto checked;
        }
        net[nNode(v) - nMin]       -= f;
        net[nNode(a->head) - nMin] += f;
      }
    }
  }
  {
  long long w;
  for (w = 0; w < n; w++)
    if (w + nMin != src && w + nMin != dst && net[w] != 0)
      { status = "NOT_A_FLOW"; break; }
  if (!strcmp(status, "OK") && -net[src - nMin] != value)
    status = "VALUE_MISMATCH";
  }
checked:

  if (csv)
    printf("%s,%ld,%ld,hi_pr,%lld,%lld,%d,%s,%lld,"
           "%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%.3f,%s\n",
           base, n, m, src, dst, 1, status, value,
           cpu_ms, usr_ms, sys_ms, cpu_ms, wall_ms,
           parse_ms, 0.0, 0.0, tag);
  else
    printf("instance %s  %ld nodes, %ld arcs\n"
           "variant  hi_pr   %lld -> %lld   rep 1\n"
           "flow     %lld  (%s)\n"
           "cpu      %.3f ms   wall %.3f ms   parse %.3f ms\n"
           "work     %ld pushes, %ld relabels, %ld global updates, "
           "%ld gaps, %ld nodes relabelled by gap\n",
           base, n, m, src, dst, value, status,
           cpu_ms, wall_ms, parse_ms,
           pushCnt, relabelCnt, updateCnt, gapCnt, gNodeCnt);

  /* His operation counts cost nothing to report and say why a row is fast or
   * slow -- in particular how often the global update fired.  They go to
   * stderr so the CSV column set stays the one every other driver prints. */
  fprintf(stderr,
          "c hi_pr work: pushes=%ld relabels=%ld updates=%ld gaps=%ld "
          "gapnodes=%ld updfreq=%.3f\n",
          pushCnt, relabelCnt, updateCnt, gapCnt, gNodeCnt, globUpdtFreq);

  free(net);
  return 0;
  }}}}
}
