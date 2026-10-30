# The certifying DIMACS assignment solver

A solver for the DIMACS assignment problem (minimum-cost perfect matching in a
bipartite graph) in the pattern of the network simplex solver in
`Mincost_Flow_Algorithms/Use_Network_Simplex`:

```
parse (C)  ->  verified program  ->  print (C)
                 |  every node on an arc?   (no: infeasible, oracle not asked)
                 |  oracle (CSA + certificate generators, untrusted)
                 |  verified checker of the certificate
                 |  rejected: verified Hungarian method, from scratch
```

The Hungarian method has **no warm start**: when the checker rejects, it
solves the instance from scratch and ignores the oracle's answer.

## Layout

```
oracle/csa/              CSA (Goldberg and Kennedy), precise costs, built as a library
oracle/asn_certificates.c   the oracle entry and the certificate generators
driver/asn_main.sml      the MLton main: FFI glue around the verified program
driver/asn_io.c          the .asn parser and the solution printer
driver/Makefile
verified/Assignment_Solver.sml   the verified program, in the zip only
testing/                 tiny behaviour tests (no benchmarks)
```

The verified program is compiled from
`../Refinements/generated/Assignment_SML/Assignment_Solver.sml`, which
`Refinements/Assignment_Solver_Export.thy` writes. Inside the repository the
build reads it there, so it cannot use a stale copy. The zip ships a copy in
`verified/`, which the build uses when the repository path does not exist.

## Build and run

```
cd driver
make                      # asn_solver
./asn_solver instance.asn solution
./asn_solver --no-oracle instance.asn solution     # verified Hungarian method only
make fault                # asn_solver_fault, see Testing
make bench                # asn_solver_bench, see Timing
```

Needs MLton (found on `PATH` or in Isabelle's `contrib`) and a C compiler.
MLton's runtime needs GMP headers and libraries. The Makefile looks in the
system location first, then under `GMP_DIR`, like the network simplex build.

## Input and output

```
p asn <nodes> <arcs>
n <id>              one line per left node
a <l> <r> <cost>    an arc from a left node to a right node
```

Every node not declared by an `n` line is a right node. The parser rejects as
malformed:

* ids out of range;
* a left node declared twice;
* an arc that is not from a left node to a right node;
* a wrong arc count;
* two arcs between the same pair of nodes.

The output:

* `c oracle: <optimal|infeasible|unknown|not asked>`: what the oracle
  answered, for information only;
* then either `s <cost>` and one `f <l> <r> 1` line per assigned pair, or
  `s infeasible`.

## What is proved

`Refinements/Assignment_Solver.thy`, theorem `asn_solve_int_correct`:

* **Premises on the input.** The parser establishes them:
  * the lengths match;
  * the left and the right nodes are distinct and disjoint, and below the
    vertex bound;
  * every arc runs from a left node to a right node;
  * there are no parallel arcs.
* **Premise on the oracle.** It leaves the input arrays unchanged and returns
  fresh arrays. Nothing is assumed about what it computes.
* **Result.** The flag is `True` exactly when every node is on an arc and the
  graph has a perfect matching. If it is `True`, the selected arcs are a
  minimum-weight perfect matching.

The statement uses only the library notions `perfect_matching` and
`min_weight_perfect_matching`. The certificates, the checker and the Hungarian
method are the method, not part of the claim.

## What is trusted

* **The parser and the printer**, `driver/asn_io.c`.
* **The FFI glue**, `driver/asn_main.sml`. It wraps the oracle so that it
  returns fresh arrays, which is the oracle premise above.
* **MLton and machine integers.** The exported code uses machine integers
  only. MLton's `Int64` arithmetic is overflow-checked, so an overflow aborts
  instead of giving a wrong answer.

The oracle is not trusted: whatever it returns is checked.

## The oracle

`oracle/csa` is CSA with these changes, all marked `CSA_LIBRARY`:

* **`parse_arrays`.** It builds CSA's data structures from arrays instead of
  stdin.
* **`csa_solve_arrays`.** It runs the scaling loop without printing. An
  instance with all costs zero starts at epsilon 1 instead of 0.
* **A termination guard.** CSA does not terminate on instances without a
  perfect matching (its README says so), because the prices then fall without
  bound within one refine. A price below the per-refine floor in `main.c`
  stops CSA. On a feasible instance a wrong firing would only cost time.

The variant is `csa_q`: queue ordering of the active nodes, precise costs,
no quick minima, `MIN_COST`, compiled with `-O3`. It is the fastest variant on
the instances this solver is meant for. `csa_release` also frees the queue.

`oracle/asn_certificates.c` turns CSA's result into a certificate:

* **Optimality.** CSA's prices are only epsilon-optimal doubles. Starting from
  the rounded prices, a label-correcting shortest-path pass over the right
  nodes repairs them into exact integer duals that are feasible and tight on
  the matching. A negative cycle means the matching is not optimal; the answer
  is then unknown.
* **Infeasibility.** The generator starts from CSA's partial matching and
  augments along alternating paths. When a search from a free left node finds
  no augmenting path, the left nodes it reached are a Hall violator. If the
  sides differ in size, the violator is empty.

If a generator fails, the answer is unknown and the Hungarian method decides.
If costs are too large for CSA's doubles to stay exact, the oracle answers
unknown.

## Timing

`make bench` builds `asn_solver_bench`, with the measurements compiled in. On
the C side they are compiled in by the macro `ASN_TIMING`. MLton has no
preprocessor, so on the SML side the Makefile selects `asn_bench_on.sml`
instead of `asn_bench_off.sml`. The shipped `asn_solver` contains no clock
calls.

After writing the solution, the bench build prints one CSV line on stderr. It
holds seven stamps of the process's CPU time (`CLOCK_PROCESS_CPUTIME_ID`,
never wall time), in milliseconds since the process started:

1. parsed, before the verified program starts;
2. the oracle is entered (SML);
3. CSA starts;
4. CSA is done and the certificate generators start;
5. control leaves C;
6. the oracle is done, its answer in SML form;
7. the verified program is done.

A stamp that is not reached prints as `-1`, for example when the oracle is
not asked.

## Testing

Behaviour tests on tiny instances only. Benchmarks belong on a different
machine.

* `testing/instances/*.asn`: hand-made cases, one per answer type.
* `testing/oracle_check.c`: runs the oracle alone and checks its certificate
  the way the verified checker does:

  ```
  cc -O2 -o oracle_check oracle_check.c ../oracle/asn_certificates.c ../driver/asn_io.c ../driver/obj/csa_*.o -lm
  python3 random_check.py 2000 1 ./oracle_check
  ```

* `testing/random_check.py --solver N SEED <solver...>`: random instances with
  up to 6 + 6 nodes, compared with a brute-force optimum. Run it on
  `asn_solver`, `asn_solver --no-oracle` and `asn_solver_fault`.
* **`asn_solver_fault`** corrupts one matching edge and one dual value in every
  optimality certificate. A correct answer from it shows that the checker
  rejected the certificate and the verified cleanup solved the instance.
