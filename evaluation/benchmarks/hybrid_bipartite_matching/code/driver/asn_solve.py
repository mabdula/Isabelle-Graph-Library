#!/usr/bin/env python3
"""One run of the certifying hybrid solver (asn_solver.zip), one CSV row.

    bench/asn_solve.py [--binary PATH] [--no-oracle] [--csv] [--tag T] instance.asn

The solver is the bench build (`make bench`), which carries the phase clock
compiled in and prints seven CPU-time stamps on stderr.  All seven are kept
in the row; nothing is reduced to a ratio here.

The clock
---------
The seven stamps are CPU time of the process (CLOCK_PROCESS_CPUTIME_ID),
in milliseconds since the process started:

    0 parsed        the instance is in the SML arrays, before the verified
                    program starts
    1 oracle entered (SML side)
    2 CSA starts
    3 CSA done, the certificate generators start
    4 leaving C
    5 oracle done, its answer in SML form
    6 verified program done

so the headline number, directly comparable with every other solver in this
study, is

    cpu_ms = stamp6 - stamp0

the verified program and nothing else: reading the .asn file is before
stamp 0 and writing the solution is after stamp 6.  A stamp that was not
reached is -1 and the phase that needs it is left blank.

The cost and the matching size are read back out of the solution file
afterwards, outside the clock.
"""

import argparse
import csv
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import time

HEADER = ("instance,nodes,arcs,left,right,status,matched,cost,oracle,"
          "cpu_ms,t_parsed,t_oracle_in,t_csa_start,t_csa_done,t_leave_c,"
          "t_oracle_done,t_done,screen_ms,glue_in_ms,csa_ms,cert_ms,"
          "glue_out_ms,check_cleanup_ms,wall_ms,tag").split(",")


def read_instance_head(path):
    """nodes, arcs, left-node count -- from the file, not from the solver."""
    nodes = arcs = None
    left = 0
    with open(path) as f:
        for line in f:
            c = line[:1]
            if c == "p":
                _, _, a, b = line.split()
                nodes, arcs = int(a), int(b)
            elif c == "n":
                left += 1
            elif c == "a":
                break
    return nodes, arcs, left


def read_solution(path):
    """cost, matched -- read after the clock has stopped."""
    cost = None
    matched = 0
    oracle = ""
    with open(path) as f:
        for line in f:
            if line.startswith("s "):
                v = line[2:].strip()
                cost = None if v == "infeasible" else int(v)
            elif line.startswith("f "):
                matched += 1
            elif line.startswith("c oracle:"):
                oracle = line.split(":", 1)[1].strip()
    return cost, matched, oracle


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("instance")
    ap.add_argument("--binary", required=True)
    ap.add_argument("--no-oracle", action="store_true")
    ap.add_argument("--timeout", type=float, default=None)
    ap.add_argument("--csv", action="store_true")
    ap.add_argument("--tag", default="")
    a = ap.parse_args()

    inst = pathlib.Path(a.instance)
    nodes, arcs, left = read_instance_head(inst)
    right = (nodes - left) if nodes is not None else ""

    out = tempfile.NamedTemporaryFile(suffix=".sol", delete=False)
    out.close()
    cmd = [a.binary] + (["--no-oracle"] if a.no_oracle else []) + [str(inst), out.name]

    status = "OPTIMAL"
    stamps = [-1.0] * 7
    cost = matched = oracle = ""
    t0 = time.time()
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True,
                              timeout=a.timeout)
    except subprocess.TimeoutExpired:
        status = "TIMEOUT"
        proc = None
    wall_ms = (time.time() - t0) * 1e3

    if proc is not None:
        if proc.returncode != 0:
            status = "ERROR"
        else:
            line = next((l for l in reversed(proc.stderr.strip().splitlines())
                         if re.fullmatch(r"\s*-?[\d.]+(,-?[\d.]+){6}\s*", l)), None)
            if line is None:
                status = "ERROR"
            else:
                stamps = [float(x) for x in line.strip().split(",")]
                cost, matched, oracle = read_solution(out.name)
                if cost is None:
                    status = "INFEASIBLE"
    os.unlink(out.name)

    def span(i, j):
        return "" if stamps[i] < 0 or stamps[j] < 0 else f"{stamps[j] - stamps[i]:.3f}"

    if status in ("TIMEOUT", "ERROR"):
        row = [inst.name] + [""] * (len(HEADER) - 2) + [a.tag]
        row[1], row[2], row[3], row[4] = nodes, arcs, left, right
        row[5] = status
        row[23] = f"{wall_ms:.3f}"
    else:
        row = [inst.name, nodes, arcs, left, right, status, matched,
               "" if cost is None else cost, oracle,
               span(0, 6)] + [f"{s:.3f}" for s in stamps] + [
               span(0, 1), span(1, 2), span(2, 3), span(3, 4), span(4, 5),
               span(5, 6), f"{wall_ms:.3f}", a.tag]

    w = csv.writer(sys.stdout)
    if not a.csv:
        w.writerow(HEADER)
    w.writerow(row)
    return 0


if __name__ == "__main__":
    sys.exit(main())
