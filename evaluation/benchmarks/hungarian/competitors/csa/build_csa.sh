#!/bin/bash
# Build the DIMACS reference solver CSA (Goldberg & Kennedy, cost-scaling
# push-relabel assignment) as the campaign ran it: variant csa_q, from the
# precise-costs sources of the challenge's own tarball csa-flows20.tar.gz
# (md5 e07d8ad4b68bba1096f39eba7cfd7dda,
# https://coral.ise.lehigh.edu//wp-content/uploads/flows20/csa-flows20.tar.gz;
# fetched to this directory by ../../setup_libraries.sh),
# with the three changes below applied here, on a copy, and recorded in
# build/PATCHES.txt.  Only the measured variant is built.
#
#   1. -DMIN_COST.  The shipped Makefile does not define it, and parse.c negates
#      every arc cost when it is undefined, so stock CSA solves the MAXIMUM-cost
#      assignment.  The study minimises throughout.
#   2. A nanosecond CPU clock (measure.c; two added lines in main.c stop it
#      immediately after the scaling loop and print it).  CSA's own myclock()
#      reads times()->tms_utime: 10 ms ticks, user time only, divided by a
#      hardcoded 60 Hz.
#   3. WHERE THE CLOCK OPENS.  parse() reads the arc lines into a temporary
#      list and then packs that list into CSA's per-node arc arrays -- a
#      counting sort over the COMPLETE list.  That pack is a structure built
#      after parsing, and the rule of the study is that such a build is the
#      first part of the clocked period.  One added line in parse.c starts the
#      clock immediately before the pack, and the per-node degree counts are
#      zeroed and recounted after it, so the whole counting sort is inside.
#      Everything in main() before the scaling loop is CSA's own setup and is
#      inside too.  No solver line is touched.
#
# usage: build_csa.sh      (run by the Makefile; needs cc, python3, tar)
set -uo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$here"
[[ -d csa-flows20 ]] || tar xzf csa-flows20.tar.gz
src="$here/csa-flows20/csa"
build="$here/build"
[[ -d "$src" ]] || { echo "missing pristine source: $src"; exit 1; }

rm -rf "$build"
mkdir -p "$build"
cp "$src"/*.c "$src"/*.h "$build"/ 2>/dev/null
cp "$src"/prec_costs/*.c "$src"/prec_costs/*.h "$build"/   # these override

# ---- change 2: the clock ----
cat > "$build/measure.c" <<'CEOF'
/* Added for the Hungarian study.  Not part of the DIMACS distribution.
   A nanosecond CPU clock.  Started in parse.c immediately before the arc list
   is packed into CSA's per-node arc arrays (the structure build, which needs
   the complete list and so comes after parsing), stopped in main.c immediately
   after the scaling loop.  Reading the file is outside; the objective is
   computed afterwards, outside too. */
#include <stdio.h>
#include <time.h>
#include <sys/time.h>
#include <sys/resource.h>

static struct timespec cpu0, cpu1;
static struct rusage   ru0,  ru1;

void csa_measure_start(void)
{
  getrusage(RUSAGE_SELF, &ru0);
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &cpu0);
}

void csa_measure_stop(void)
{
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &cpu1);
  getrusage(RUSAGE_SELF, &ru1);
}

static double ms_ts(struct timespec a, struct timespec b)
{ return (b.tv_sec - a.tv_sec) * 1000.0 + (b.tv_nsec - a.tv_nsec) / 1e6; }

static double ms_tv(struct timeval a, struct timeval b)
{ return (b.tv_sec - a.tv_sec) * 1000.0 + (b.tv_usec - a.tv_usec) / 1e3; }

void csa_measure_report(void)
{
  printf("MEASURE cpu_ms=%.6f usr_ms=%.6f sys_ms=%.6f\n",
         ms_ts(cpu0, cpu1),
         ms_tv(ru0.ru_utime, ru1.ru_utime),
         ms_tv(ru0.ru_stime, ru1.ru_stime));
  (void) fflush(stdout);
}
CEOF

# ---- the two-line main.c patch: stop the clock, print it ----
python3 - "$build/main.c" <<'PYEOF'
import sys
p = sys.argv[1]
s = open(p, newline="").read()          # keep the file's own line endings
NL = "\r\n" if "\r\n" in s else "\n"
subs = [("time = myclock() - time;", "csa_measure_stop();" + NL + "time = myclock() - time;"),
        ("display_results(time);",   "display_results(time);" + NL + "csa_measure_report();")]
for old, new in subs:
    old = NL + old + NL; new = NL + new + NL
    if s.count(old) != 1:
        sys.exit("main.c patch: expected exactly one %r, found %d" % (old, s.count(old)))
    s = s.replace(old, new)
open(p, "w", newline="").write(s)
PYEOF
[[ $? -eq 0 ]] || { echo "main.c patch failed"; exit 1; }

# ---- change 3: the parse.c patch: start the clock before the pack ----
python3 - "$build/parse.c" <<'PYEOF'
import sys
p = sys.argv[1]
s = open(p, newline="").read()          # keep the file's own line endings
NL = "\r\n" if "\r\n" in s else "\n"
anchor = "if (arc_count != m)" + NL + "  parse_error(BADCOUNT);" + NL
if s.count(anchor) != 1:
    sys.exit("parse.c patch: expected exactly one %r, found %d" % (anchor, s.count(anchor)))
block = anchor + """
/* Hungarian study: THE CLOCK OPENS HERE.  Everything
   from this line to the end of parse() packs the arc list into CSA's own
   per-node arc arrays -- a counting sort over the complete list, which needs
   every arc read before it can place the first one, and so is a structure
   built after parsing.  The per-node degree counts were accumulated by the
   read loop above; they are zeroed and recounted here so that the whole sort,
   counting pass included, is inside the clock.  No solver line is touched.
   See build_csa.sh and PATCHES.txt. */
csa_measure_start();
for (tail = 0; tail < lhs_n; tail++)
  lhs_degree[tail] = 0;
#ifdef	STORE_REV_ARCS
for (tail = 0; tail < n - lhs_n; tail++)
  rhs_degree[tail] = 0;
#endif
for (temp_a = temp_arcs; temp_a != temp_arcs + arc_count; temp_a++)
  {
  lhs_degree[temp_a->tail - head_lhs_node]++;
#ifdef	STORE_REV_ARCS
  rhs_degree[temp_a->head - head_rhs_node]++;
#endif
  }
"""
block = block.replace("\n", NL)
s = s.replace(anchor, block)
s = "extern void csa_measure_start(void);   /* Hungarian study; see PATCHES.txt */" + NL + s
open(p, "w", newline="").write(s)
PYEOF
[[ $? -eq 0 ]] || { echo "parse.c patch failed"; exit 1; }

# -O4 is what the shipped Makefile asks for; gcc treats it as -O3.
CC="${CC:-cc}"
CFLAGS="-O4 -w"
BASE="main.c refine.c update_epsilon.c parse.c stack.c timer.c debug.c measure.c"

( cd "$here" && diff -u csa-flows20/csa/main.c build/main.c > build/main.c.patch )
( cd "$here" && diff -u csa-flows20/csa/parse.c build/parse.c > build/parse.c.patch )
{
  echo "Changes applied to the pristine DIMACS CSA sources, and nothing else:"
  echo
  echo "1. -DMIN_COST on every compile (see build_csa.sh for why)."
  echo "2. measure.c added, and two lines added to main.c (main.c.patch) that"
  echo "   stop the clock immediately after the scaling loop and print it."
  echo "3. parse.c (parse.c.patch): the clock is STARTED immediately before the"
  echo "   arc list is packed into CSA's per-node arc arrays, and the per-node"
  echo "   degree counts are redone after that line, so that the whole counting"
  echo "   sort is inside the clock."
  echo
  echo "Variant built: csa_q = -DQUEUE_ORDER with queue.c (the campaign's variant,"
  echo "chosen by the study's probe over the authors' 'interesting' list)."
  echo "Compiler: $($CC --version | head -1)"
  echo "CFLAGS:   $CFLAGS -DMIN_COST -DQUEUE_ORDER"
} > "$build/PATCHES.txt"

( cd "$build" && $CC $CFLAGS -DMIN_COST -DQUEUE_ORDER -o csa_q $BASE queue.c -lm 2>csa_q.log ) \
  && echo "built $build/csa_q" || { echo "FAILED csa_q (see $build/csa_q.log)"; exit 1; }
