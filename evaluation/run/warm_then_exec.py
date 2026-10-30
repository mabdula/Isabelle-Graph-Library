#!/usr/bin/env python3
"""Spin on one core for a few seconds, then exec the solver on that core.

    warm_then_exec.py SECONDS -- command args...

WHY.  The box runs schedutil on acpi-cpufreq and parks an idle core at
1.49 GHz.  A solver that starts on an idle core and finishes within about
1.5 s runs at that frequency throughout: LEMON on ak-131078 read 1600 ms
from an idle core and 735 ms right after a 5 s busy spin on the same core.
Runs of several seconds ramp the core themselves and are not affected.

HOW.  This process inherits the island affinity the runner set with
taskset.  It narrows that to the single core it is on, spins for SECONDS
(a busy loop, never a sleep), and execs the command.  The exec keeps the
core and its affinity, so the solver parses and solves on a core that has
been busy without a gap.  The spin is outside the solver's process and so
outside every clock it reads; the solver's own measurement is unchanged.
"""
import os
import sys
import time


def main():
    argv = sys.argv[1:]
    if len(argv) < 3 or argv[1] != "--":
        sys.exit(__doc__)
    seconds = float(argv[0])
    cmd = argv[2:]
    # One core, the one we are on; the solver is single-threaded.
    cores = sorted(os.sched_getaffinity(0))
    core = os.sched_getcpu() if hasattr(os, "sched_getcpu") else cores[0]
    if core not in cores:
        core = cores[0]
    os.sched_setaffinity(0, {core})
    end = time.monotonic() + seconds
    x = 1.0
    while time.monotonic() < end:
        for _ in range(100000):
            x = x * 1.0000001 + 1e-9
    os.execvp(cmd[0], cmd)


if __name__ == "__main__":
    main()
