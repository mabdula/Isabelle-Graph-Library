/*
  The phase clock of the timing build (make bench). CPU time of this
  process (CLOCK_PROCESS_CPUTIME_ID), never wall time, in milliseconds
  since the process started.

  The seven stamps, in order:
    0  parsed: the input is in the SML arrays, before the verified program
    1  oracle entered (SML side)
    2  CSA starts
    3  CSA done: the certificate generators start
    4  leaving C
    5  oracle done: its answer is in SML form
    6  verified program done

  Compiled in by the macro ASN_TIMING (make bench). Without it, both
  functions are empty; the shipped build never calls them anyway, since
  its SML side selects asn_bench_off.sml (MLton has no preprocessor, so
  the Makefile picks the file) and MLton folds the calls away. A stamp
  not reached (the oracle not asked, or answering before CSA starts) is
  printed as -1.
*/

#include <stdint.h>
#include <stdio.h>
#include <time.h>

#define ASN_STAMPS 7

#ifdef ASN_TIMING
static double stamps[ASN_STAMPS] = { -1, -1, -1, -1, -1, -1, -1 };

void asn_stamp(int64_t k) {
  struct timespec ts;
  if (k < 0 || k >= ASN_STAMPS) return;
  if (clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts) == 0)
    stamps[k] = (double)ts.tv_sec * 1e3 + (double)ts.tv_nsec / 1e6;
}

/* One CSV line on stderr, the seven stamps, no header. */
void asn_report(void) {
  for (int k = 0; k < ASN_STAMPS; k++)
    fprintf(stderr, k + 1 < ASN_STAMPS ? "%.3f," : "%.3f\n", stamps[k]);
}
#else
void asn_stamp(int64_t k) { (void)k; }
void asn_report(void) {}
#endif
