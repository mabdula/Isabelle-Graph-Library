# Experimental evaluation of IsaGraphLib

This directory reproduces the running-time comparison of the paper's body (Fig. 2 and 3; the tables behind
them are Tables 5, 7 to 9, 11 to 24 and 26 to 28 of the appendix): the verified code exports of the library,
in Standard ML, against the libraries they were compared with.  It is meant to be run on a fresh Ubuntu VM
(x86_64, with `build-essential`, `curl`, `patch`, `perl` and `python3`), without root,
with network access during the setup.  Everything it needs is downloaded by the setup and kept under
`evaluation/work/`; nothing is installed outside the repository.

## The three experiments

Each script first runs the setup for its experiment (`setup/setup.sh <mode>`) and then the measurements
(`run/run.sh <mode>`); the two can also be run one after the other by hand.  Both take the one option
`--old-generated-code` (below).

| script | what it does | time |
|---|---|---|
| `experiments_smoke.sh` | our SML exports once on the smallest instance of every family of the body's figures, with the code exports shipped in `exports/pregenerated/`; also the hybrid solver for the assignment problem (Tables 35 to 37) | about 20 minutes: downloads and builds about 15 minutes, measurements a few minutes |
| `experiments_8h.sh` | downloads Isabelle2025-2 and the AFP entries the library needs, builds the export sessions and generates the code exports anew, then measures imperative SML and the main competitor (LEMON CSR; Sage with our oracle for matroid intersection) on the first family column of every row of Fig. 2 and 3 (Tables 5, 9, 13, 16, 19, 22 and 26), size by size across the seven benchmarks, one instance and one run per size, until 8 hours since the start are used up | 8 hours |
| `experiments_full.sh` | the Isabelle build as above, then every family, size and instance of the body and every library column | about 18 days of measurements after the setup (below) |

With `--old-generated-code` the measured code exports are those of the paper's campaign (`exports/campaign/`),
and Isabelle is neither downloaded nor built.  Without it, the smoke test measures the pregenerated exports
and the other two the exports the Isabelle build writes.  The AFP push-relabel export is supplied pregenerated
only.

The 8-hour experiment transfers its clock from the setup to the measurements by itself: the setup records its
start in `work/started_8h`, and the measurement script starts no run after 8 hours from then.

## Browsing the library in Isabelle/jEdit

`browse_library_jedit.sh [THEORY ...]` opens an index theory of the paper (`../Paper_Index`, one theory per section;
default `Index_00_Introduction_Main_Theorems`, or several, or `all`) in Isabelle/jEdit: every listing of the paper is an
entry there that links to its theorem, definition or locale in the library.  The script downloads Isabelle2025-2 and the
AFP entries the library needs into `work/` and builds HOL-Library, the session the index theories start from, and nothing
more; Isabelle/jEdit checks the opened theory and the library theories it imports while they are shown, which takes
longer the more of the library the theory refers to.  It needs a display.

## Estimates

The measurement times are twice the wall time the campaign spent on the same runs (sequential; the campaign
ran up to seven runs in parallel on 32 cores), plus two hours for the setup and the Isabelle build.  On the
paper's machine, the runs of the full experiment took about 217 hours in total, so the estimate is about 435
hours (18 days) plus the setup; the 8-hour experiment's runs took about 3 hours, so with the setup it fills its
8 hours; the smoke test's runs take a few minutes.  The largest instances need up to about 48 GB of RAM (`PROTOCOL.txt`
of each benchmark); the generated instances are deleted as soon as no run needs them, so at most about 10 GB
of them (the largest rmf-long instance) are on disk at a time.  A VM with 2 processors, 8 GB of RAM and 25 GB of free
disk has enough disk for every experiment, and enough RAM for the smoke test and the 8-hour
experiment (whose runs stop at the sizes that no longer fit, marked `OOM`); for the full experiment give it the RAM above.

## Results

Every run writes `results/<date>_<mode>/`, with one directory per benchmark and family:

| file | content |
|---|---|
| `<benchmark>/<family>/table.csv` | the paper's table projected to the columns measured: one row per size, one cell per solver, `seconds (ratio to the SML column)` |
| `<benchmark>/<family>/table_paper.csv` | the same table as in the paper appendix, for comparison |
| `<benchmark>/<family>/raw.csv` | one row per run: status, `cpu_ms`, the row the program printed |
| `SUMMARY.txt`, `conditions.txt`, `run.log` | per table the deviation from the cells of the paper appendix; the conditions of the run; the log |

Cells: a number is seconds (the hybrid tables: milliseconds), the mean over the problems of a size of the
per-problem median of the repeats; `TO` timeout; `OOM` out of memory; `ERR` the program stopped with an error;
`n/a` not applicable; `NOT_RUN` not started, the time budget was used up; `k/m` beside a number: k of m
problems finished; `not available` the program could not be built or the instance not fetched.  On another
machine the absolute times differ from the paper by a constant factor; the ratios between the columns are what
to compare, and runs of a few milliseconds are noisy.

The smoke test works when every `status` in every `raw.csv` reads `OK` and no table cell reads `not available`,
apart from cells that depend on a file listed in `NOT_AVAILABLE.txt`.  Its tables hold our SML columns only;
the other columns are measured by the other two experiments.

## What the setup downloads

`modes.conf` says what each mode runs; the setup fetches only what that needs, checks every file against the
md5 of the file the numbers of the paper appendix were made with, and tries every file's sources in order
(`toolchains_dist/MANIFEST.txt`, `third_party/SOURCES.txt`, `setup/afp_entries.txt`).  A download that fails
does not stop the setup: the file, its sources, md5 and the path to put it at are printed and recorded in
`NOT_AVAILABLE.txt`, and the columns or rows that depend on it are left out and marked in the tables.  Put the
file there and run the setup again.

| component | version |
|---|---|
| MLton, with GMP 6.3.0 from the Ubuntu libgmp-dev package | 20241230 |
| gcc and g++, the compilers of the paper's campaign, from the Ubuntu 22.04 packages (with their isl, mpc and mpfr); they compile everything, MLton's C code included | 11.4.0 |
| CMake (for LEMON) | 3.22.1 |
| Eclipse Temurin JDK (for the JGraphT columns) | 21.0.12.1+1 |
| CPython, with numpy 2.2.6, scipy 1.15.3, networkx 3.4.2, ortools 9.15.6755, passagemath 10.6.48 (pinned in each `requirements.txt`) | 3.10.12 |
| Isabelle, and the AFP entries the export sessions need, from the AFP's Isabelle2025-2 release branch at one pinned state | 2025-2 |
| LEMON | 1.3.1 |
| JGraphT with jheaps 0.14, apfloat 1.14.0, fastutil 8.5.18 | 1.5.3 |
| DIMACS generators ch9-1.1, assign.c, dcube.c, twocost.a, geomasn.a, genrmfDimacs, washington.c | as distributed |
| Andrew Goldberg's hi_pr 3.5, PRF 1.8 (the AK generator) and CSA (not redistributed, fetched at setup) | as distributed |
| the USA-road-t road networks of the 9th DIMACS Challenge (NY in the smoke test, all twelve in the full experiment) | as distributed |

## Layout

| entry | content |
|---|---|
| `experiments_smoke.sh`, `experiments_8h.sh`, `experiments_full.sh` | the three experiments |
| `browse_library_jedit.sh` | the library in Isabelle/jEdit, from the paper's index theories |
| `modes.conf` | what each experiment runs: benchmarks, columns, families, sizes, repeats, order, code exports |
| `setup/` | the setup: `setup.sh` runs `toolchains.sh`, `isabelle.sh` (which runs `afp.sh`), `exports.sh`, `thirdparty.sh`, `programs.sh`; `afp_entries.txt`, `export_files.txt` |
| `run/` | the measurements: `run.sh` runs `run_experiments.py` (plans the runs, generates and deletes the instances, starts one single-run program per run) and `make_tables.py`; both need only the VM's `python3` |
| `benchmarks/<name>/` | one directory per problem: the single-run programs (`code/`, `competitors/`), `columns.txt`, `instances/`, the results of the paper appendix, `README.txt`, `PROTOCOL.txt`, `ENVIRONMENT.txt` |
| `exports/` | the code exports: `campaign/` (the paper's) and `pregenerated/` (from the current library) |
| `toolchains_dist/`, `third_party/` | the download lists with sources and md5s |
| `work/`, `results/` | written by the setup and the runs (not tracked) |

The measurements have three layers: `run/run_experiments.py` picks the next instance and solver and starts
the single-run program as a user would from the command line; the single-run program (`bench_*`, built by the
benchmark's Makefile) parses the instance, times the solver and prints one CSV row; the solver is the code
export or the library.  `benchmarks/<name>/README.txt` says how to run any program by hand.

## Licence

The authors' code is under the licence of the repository (`../LICENSE`); the downloaded components keep their
own licences (`THIRD_PARTY_LICENSES.txt`).
