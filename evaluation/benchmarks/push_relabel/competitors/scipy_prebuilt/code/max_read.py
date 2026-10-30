"""DIMACS (.max) reader and the shared pieces of the Python drivers.

    c <anything>            comment, may appear anywhere
    p max <nodes> <arcs>    appears before any arc line
    n <id> s                the source
    n <id> t                the sink
    a <from> <to> <cap>     a directed arc with a capacity

Node ids are kept exactly as the file writes them, 1..n.  The arrays returned
are 0-based (id - 1) because both Python libraries index from zero; that
renumbering is parsing work and sits outside the clock, as all of this file
does.

Reading is done with numpy over the whole byte buffer rather than line by
line: the biggest instances in this study run to hundreds of millions of arcs
and a Python loop over them would take longer than every solver put together.
"""

import csv
import os
import resource
import sys

import numpy as np


def parse_max(path):
    """-> (n_nodes, n_arcs, source, sink, frm, to, cap).

    frm and to are 0-based int64 arrays; source and sink are 0-based ints."""
    with open(path, "rb") as fh:
        raw = fh.read()

    n_nodes = None
    source = sink = None

    # The problem line and the two node designator lines are short and near
    # the front.  Walk the head of the file line by line until both ends are
    # known, then hand the rest to numpy in one piece.
    pos = 0
    body = None
    while True:
        end = raw.find(b"\n", pos)
        if end < 0:
            end = len(raw)
        line = raw[pos:end]
        kind = line[:1]
        if kind == b"p":
            f = line.split()
            if len(f) < 4 or f[1] != b"max":
                raise ValueError("%s: bad problem line: %r" % (path, line))
            n_nodes = int(f[2])
        elif kind == b"n":
            f = line.split()
            if len(f) < 3:
                raise ValueError("%s: bad node line: %r" % (path, line))
            if f[2] == b"s":
                source = int(f[1])
            elif f[2] == b"t":
                sink = int(f[1])
            else:
                raise ValueError("%s: node line is neither s nor t" % path)
        elif kind == b"a":
            body = pos
            break
        if end >= len(raw):
            break
        pos = end + 1

    if n_nodes is None:
        raise ValueError("%s: no `p max' line" % path)
    if source is None or sink is None:
        raise ValueError("%s: no source or no sink line" % path)
    if body is None:
        raise ValueError("%s: no arc lines" % path)

    tail = raw[body:]
    if b"\nc" in tail or b"\nn" in tail:
        # designators or comments mixed in among the arcs: drop them first
        tail = b"\n".join(ln for ln in tail.split(b"\n") if ln[:1] == b"a")
    toks = tail.split()
    if len(toks) % 4:
        raise ValueError("%s: arc block is not `a <u> <v> <c>' throughout" % path)
    frm = np.array(toks[1::4], dtype=np.int64)
    to = np.array(toks[2::4], dtype=np.int64)
    cap = np.array(toks[3::4], dtype=np.int64)

    return (n_nodes, int(frm.size), source - 1, sink - 1,
            frm - 1, to - 1, cap)


# There is deliberately NO helper here for reading a list of source-sink pairs
# into a driver.  A flow problem is a graph AND a pair, so each pair is its own
# problem and gets its own process; the campaign runner launches one run per
# instance.


HEADER = ("instance,nodes,arcs,variant,source,target,repeat,status,"
          "flow_value,cpu_ms,cpu_usr_ms,cpu_sys_ms,proc_ms,wall_ms,"
          "parse_ms,dedup_ms,build_ms,tag")

# The last three columns are the work done OUTSIDE the clock, so that what is
# outside it is visible rather than merely asserted:
#
#   parse_ms   reading the .max file into arc arrays
#   dedup_ms   collapsing parallel arcs by adding their capacities
#   build_ms   turning those arrays into the library's own structure
#
# They are properties of the run, not of the query, so the same three figures
# repeat on every row a run prints.  CPU time, like every other time column.


def cpu_ms():
    """Process CPU time so far, user and system, in milliseconds.

    getrusage over the whole process, the same quantity the SML, Go and LEMON
    drivers read, so the figures sit in one column without conversion."""
    ru = resource.getrusage(resource.RUSAGE_SELF)
    return (ru.ru_utime * 1000.0, ru.ru_stime * 1000.0)


def emit(row, human=False):
    if human:
        sys.stdout.write(
            "instance %s  %s nodes, %s arcs\n"
            "variant  %s   %s -> %s   rep %s\n"
            "flow     %s  (%s)\n"
            "cpu      %s ms   wall %s ms   parse %s ms   build %s ms\n"
            % (row[0], row[1], row[2], row[3], row[4], row[5], row[6],
               row[8], row[7], row[9], row[13], row[14], row[16]))
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


def dedupe_sum(n, frm, to, cap):
    """Keep one arc per (tail, head), with the capacities ADDED.  -> arrays.

    NetworkX cannot hold parallel arcs: add_edge OVERWRITES, keeping whichever
    capacity it saw last, which is a wrong answer rather than a slow one.  For
    a flow problem a bundle of parallel arcs is exactly one arc of their
    combined capacity, so adding them changes no maximum flow value.

    SciPy needs none of this and does not call it: building a CSR matrix from
    coordinates ADDS duplicate entries, which is the right thing here, and the
    summing happens inside its own build.  LEMON, JGraphT and all six verified
    columns take parallel arcs as they come.

    It is input marshalling and sits outside the clock, clocked and reported in
    dedup_ms so the cost this study incurs on NetworkX's behalf is on the
    record rather than hidden.

    HOW IT IS DONE.  One stable argsort of the packed key tail * n + head --
    numpy's stable sort on an integer array is a radix sort, so this is linear
    in the arc count -- then np.add.reduceat over the run boundaries.  AND THE
    COMMON CASE COSTS ALMOST NOTHING: none of the three families in this study
    emits parallel arcs, so the run count equals the arc count and the
    originals are handed straight back, unsorted and uncopied.
    """
    m = frm.size
    if m == 0:
        return frm, to, cap
    key = frm.astype(np.int64, copy=False) * np.int64(n) + to
    order = np.argsort(key, kind="stable")      # radix sort on int64
    key = key[order]
    dup = key[1:] == key[:-1]
    if not dup.any():
        # no two arcs share a pair: nothing to collapse, and the caller gets
        # the arrays it already had.  Asking `any' first keeps this case from
        # ever materialising the run-boundary index.
        return frm, to, cap
    starts = np.flatnonzero(np.concatenate(([True], ~dup)))
    csum = np.add.reduceat(cap[order], starts)
    ukey = key[starts]
    return (ukey // np.int64(n)).astype(frm.dtype), \
           (ukey % np.int64(n)).astype(to.dtype), csum
