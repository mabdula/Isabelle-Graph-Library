"""DIMACS (.gr) reader and the shared pieces of the Python drivers.

    c <anything>            comment, may appear anywhere
    p sp <nodes> <arcs>     appears before any arc line
    a <from> <to> <weight>  a directed arc

THIS STUDY IS KRUSKAL'S MINIMUM SPANNING TREE, and every arc line is one
undirected edge of the given weight.  The files are the shortest-path
challenge's directed ones, and PARALLEL EDGES ARE COLLAPSED on the way in:
every unordered pair {u, v}
keeps its cheapest arc (collapse_min), so every solver is handed the same
simple graph.  Parsing work, outside the clock, reported in dedup_ms.

Node ids are kept exactly as the file writes them, 1..n.  The arrays returned
are 0-based (id - 1) because both Python libraries index from zero; that
renumbering is parsing work and sits outside the clock, as all of this file
does.

Reading is done with numpy over the whole byte buffer rather than line by
line: the dense family runs to 67 million arcs and a Python loop over them
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


HEADER = ("instance,nodes,arcs,edges,repeat,status,tree_edges,tree_weight,"
          "cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms,"
          "parse_ms,dedup_ms,build_ms,clock_build_ms,clock_solve_ms,tag")

# clock_build_ms and clock_solve_ms are the two parts of the CLOCKED period,
# for a driver whose structure is built inside the clock (SciPy's CSR
# matrix): one intermediate clock reading is taken after the build and
# before the solve.  cpu_ms stays the difference between the first and the
# last reading, the canonical time; the two parts add up to it.  Empty for a
# driver whose structure is filled while the file is parsed (NetworkX).

# parse_ms, dedup_ms and build_ms are the work done OUTSIDE the clock, so
# that what is outside it is visible rather than merely asserted:
#
#   parse_ms   reading the .gr file into arc arrays
#   dedup_ms   collapsing parallel edges: every unordered pair {u, v} keeps
#              its cheapest arc (collapse_min), in every driver of the
#              study.  The grids carry both directions of every pair, the
#              dense files repeat a few per cent of their arcs.
#   build_ms   turning those arrays into the library's input arrays or, for
#              NetworkX, its graph


def cpu_ms():
    """Process CPU time so far, user and system, in milliseconds.

    getrusage over the whole process, the same quantity the SML, Go and LEMON
    drivers read, so the figures sit in one column without conversion."""
    ru = resource.getrusage(resource.RUSAGE_SELF)
    return (ru.ru_utime * 1000.0, ru.ru_stime * 1000.0)


def emit(row, human=False):
    if human:
        sys.stdout.write(
            "%s  rep %s\n  status      %s\n  tree edges  %s\n  tree weight %s\n"
            "  edges       %s  (%s arcs in the file)\n"
            "  cpu         %s ms   (the measurement)\n  wall        %s ms\n"
            % (row[0], row[4], row[5], row[6], row[7], row[3], row[2], row[8], row[12]))
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
    libraries build large structures over graphs with tens of millions of
    arcs.  A run that asks for more than its share must die alone, as a
    recorded MEMORY row, rather than take the machine's other six runs with
    it.  The cap is recorded in the conditions file, not hidden here."""
    if gb and gb > 0:
        soft = int(gb * (1 << 30))
        resource.setrlimit(resource.RLIMIT_AS, (soft, soft))


def collapse_min(n, frm, to, w):
    """Keep the cheapest arc of every unordered pair {u, v}.  -> (frm, to, w),
    each edge once as (lo, hi, w), sorted by (lo, hi).

    One pass, no Python loop: pack each pair into lo * n + hi (exact: both
    ids are below n and n^2 is far inside int64), ONE stable argsort of
    those integers (a radix sort on int64), np.minimum.reduceat over the run
    boundaries for the cheapest weight of each pair, and the endpoints back
    out of the packed key by divmod.  The same (lo, hi) order the native
    drivers' counting sorts produce.  Self-loops, if any, stay."""
    m = frm.size
    if m == 0:
        return frm, to, w
    lo = np.minimum(frm, to).astype(np.int64, copy=False)
    hi = np.maximum(frm, to).astype(np.int64, copy=False)
    key = lo * np.int64(n) + hi
    order = np.argsort(key, kind="stable")      # radix sort on int64
    key = key[order]
    starts = np.flatnonzero(np.concatenate(([True], key[1:] != key[:-1])))
    wmin = np.minimum.reduceat(w[order], starts)
    ukey = key[starts]
    return (ukey // np.int64(n)).astype(frm.dtype), \
           (ukey % np.int64(n)).astype(to.dtype), wmin
