"""DIMACS shortest-path (.gr) reader and the shared pieces of the Python drivers.

    c <anything>            comment, may appear anywhere
    p sp <nodes> <arcs>     appears before any arc line
    a <from> <to> <weight>  a directed arc

Node ids are kept exactly as the file writes them, 1..n.  The arrays returned
are 0-based (id - 1) because both Python libraries index from zero; that
renumbering is parsing work and sits outside the clock, as all of this file
does.

Reading is done with numpy over the whole byte buffer rather than line by
line: the road networks run to 58 million arcs and a Python loop over them
would take longer than every solver in the study put together.
"""

import csv
import os
import resource
import sys

import numpy as np


def parse_gr(path):
    """-> (n_nodes, n_arcs, frm, to, weight), all 0-based int64 arrays."""
    with open(path, "rb") as fh:
        raw = fh.read()

    n_nodes = None
    # The problem line is short and near the front; find it without touching
    # the rest of the buffer.
    pos = 0
    while True:
        end = raw.find(b"\n", pos)
        if end < 0:
            end = len(raw)
        line = raw[pos:end]
        if line[:1] == b"p":
            f = line.split()
            if len(f) < 4 or f[1] != b"sp":
                raise ValueError("%s: bad problem line: %r" % (path, line))
            n_nodes = int(f[2])
            body = end + 1
            break
        if end >= len(raw):
            raise ValueError("%s: no `p sp' line" % path)
        pos = end + 1

    # After the problem line come a few more comments and then nothing but
    # `a' lines.  Skip past the comments, then check that the rest really is
    # uniform; if it is -- and in every instance this study uses it is -- the
    # whole block is four repeating tokens and splits in one pass.
    while body < len(raw) and raw[body:body + 1] in (b"c", b"\n", b"\r"):
        nl = raw.find(b"\n", body)
        body = len(raw) if nl < 0 else nl + 1
    tail = raw[body:]
    if b"\nc" in tail:
        # Comments mixed in among the arcs: drop them line by line first.
        tail = b"\n".join(ln for ln in tail.split(b"\n") if ln[:1] == b"a")
    toks = tail.split()
    if len(toks) % 4:
        raise ValueError("%s: arc block is not `a <u> <v> <w>' throughout" % path)
    # a <from> <to> <weight>, repeating
    frm = np.array(toks[1::4], dtype=np.int64)
    to = np.array(toks[2::4], dtype=np.int64)
    w = np.array(toks[3::4], dtype=np.int64)

    return n_nodes, int(frm.size), frm - 1, to - 1, w


# There is deliberately NO helper here for reading a list of source-target
# pairs into a driver.  A shortest-path problem is a graph AND a pair, so each
# pair is its own problem and gets its own process; the campaign runner reads
# instances/queries.csv and launches one run per row.


HEADER = ("instance,nodes,arcs,query,source,target,repeat,status,"
          "reached,hops,dist,cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms,"
          "parse_ms,dedup_ms,build_ms,tag")

# The last three columns are the work done OUTSIDE the clock, so that what is
# outside it is visible rather than merely asserted:
#
#   parse_ms   reading the .gr file into arc arrays
#   dedup_ms   collapsing parallel arcs to their cheapest member
#   build_ms   turning those arrays into the library's own structure
#
# They are properties of the run, not of the query, so the same three figures
# repeat on every row a run prints.  CPU time, like every other time column.
#
# For our three exports every one of them except parse_ms is 0.000, and that
# is not padding: the export is handed plain arrays, takes parallel arcs as
# they come, and builds its CSR inside the entry point, where it is measured.
# For SciPy and NetworkX dedup_ms is real work this driver does on the
# library's behalf, because neither data structure can hold two arcs between
# the same pair.


def cpu_ms():
    """Process CPU time so far, user and system, in milliseconds.

    getrusage over the whole process, the same quantity the SML, Go and LEMON
    drivers read, so the figures sit in one column without conversion."""
    ru = resource.getrusage(resource.RUSAGE_SELF)
    return (ru.ru_utime * 1000.0, ru.ru_stime * 1000.0)


def emit(row, human=False):
    if human:
        sys.stdout.write(
            "query %d  %d -> %d  rep %d\n"
            "  status   %s\n  hops     %s\n  dist     %s\n"
            "  cpu      %s ms   (the measurement)\n  wall     %s ms\n"
            % (row[3], row[4], row[5], row[6], row[7], row[9], row[10],
               row[11], row[15]))
    else:
        w = csv.writer(sys.stdout, lineterminator="\n")
        w.writerow(row)
    try:
        sys.stdout.flush()
    except BrokenPipeError:        # the reader went away: not our problem
        os._exit(0)


def limit_memory(gb):
    """Cap the address space of this run.

    The campaign puts seven runs on the machine at once, and the Python
    libraries build dense structures over graphs with tens of millions of
    nodes.  A run that asks for more than its share must die alone, as a
    recorded MEMORY row, rather than take the machine's other six runs with
    it.  The cap is recorded in the conditions file, not hidden here."""
    if gb and gb > 0:
        soft = int(gb * (1 << 30))
        resource.setrlimit(resource.RLIMIT_AS, (soft, soft))


def dedupe_min(n, frm, to, w):
    """Keep one arc per (tail, head), the cheapest.  -> (frm, to, w).

    Neither of the Python libraries can hold parallel arcs.  SciPy's CSR
    build ADDS the weights of arcs that share a pair, and NetworkX's add_edge
    OVERWRITES, keeping whichever it saw last; both are wrong answers, not
    slow ones.  The road networks have them (USA-road-t.NY alone has 3724
    pairs carrying two or three arcs).

    For a shortest-path problem a bundle of parallel arcs is exactly its
    cheapest member, so collapsing them changes no answer.  It is input
    marshalling, like the renumbering above, and sits outside the clock:
    these libraries would read a file straight into a structure that cannot
    represent the duplicate in the first place.  Our export, LEMON and
    JGraphT take the arcs as they come and need none of this.  It is clocked
    and reported in dedup_ms either way, so the cost this study incurs on
    their behalf is on the record rather than hidden.

    HOW IT IS DONE.  One pass, no Python loop, no hash table:

      * pack each arc into a single integer, tail * n + head, which is exact
        because both ids are below n and n^2 is far inside int64 even for the
        24-million-node USA network;
      * ONE stable argsort of those integers.  numpy's stable sort on an
        integer array is a radix sort, so this is linear in the arc count
        rather than m log m, and it is the only sort here -- an earlier
        version used lexsort on (weight, key), which is two sorts and two
        gathers over every array;
      * np.minimum.reduceat over the run boundaries picks the cheapest weight
        of each bundle in one sweep;
      * the surviving tails and heads are recovered from the packed key by
        divmod, so the big frm and to arrays are never gathered at all.

    AND THE COMMON CASE COSTS ALMOST NOTHING.  Both synthetic families have
    no parallel arcs whatever, so when the run count equals the arc count the
    originals are handed straight back, unsorted and uncopied.
    """
    m = frm.size
    if m == 0:
        return frm, to, w
    key = frm.astype(np.int64, copy=False) * np.int64(n) + to
    order = np.argsort(key, kind="stable")      # radix sort on int64
    key = key[order]
    dup = key[1:] == key[:-1]
    if not dup.any():
        # no two arcs share a pair: nothing to collapse, and the caller gets
        # the arrays it already had.  Asking `any' first keeps this case from
        # ever materialising the run-boundary index, which on the USA network
        # would be another 460 MB.
        return frm, to, w
    starts = np.flatnonzero(np.concatenate(([True], ~dup)))
    wmin = np.minimum.reduceat(w[order], starts)
    ukey = key[starts]
    return (ukey // np.int64(n)).astype(frm.dtype), \
           (ukey % np.int64(n)).astype(to.dtype), wmin
