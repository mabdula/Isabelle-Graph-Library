# IsaGraphLib artefact: Formally Verified Efficient Graph Algorithms in Isabelle/HOL

This artefact is the Isabelle/HOL formal development accompanying the paper. It contains the full library of verified graph algorithms, the code exported from it, and a machine-checked index that links every listing in the paper to its formal counterpart.

For the contents of the library, the publications it builds on, and how to install Isabelle and the Archive of Formal Proofs and register this development as a component, see `README.md`. For the index, see `Paper_Index/README.md`.

## Badges

We apply for the Available, Functional, and Reusable badges. The artefact is archived at [DOI to be added].

## Running the artefact

Run each of the following commands from this directory. Each build command checks every proof in the sessions it selects, and it succeeds if Isabelle reports every session as finished and returns exit code 0. We measured the times below with the default settings of Isabelle, with which it builds one session at a time using 8 threads, on a machine with two AMD EPYC 7343 processors, which have 16 cores each and run at up to 3.9 GHz, 378 GiB of memory, and Ubuntu 22.04 on x86_64. Since a build uses at most 8 threads, the times depend more on the speed of a core than on the number of cores beyond 8.

### Smoke test

The smoke test builds no session. The theories are checked interactively in Isabelle/jEdit. [To be added: the command that opens them in Isabelle/jEdit, and the time that processing them takes.]

The script `evaluation/experiments_smoke.sh` compiles the generated SML code of the algorithms with the Poly/ML compiler that ships with Isabelle, and runs each algorithm on a small example. [Stub, to be filled in.]

### Experiments within 8 hours

```
isabelle build -D . -X paper_index
```

This builds every session of the library, leaving out the index. On that machine, starting from an installation in which only the sessions that come with Isabelle had been built, it took 2 hours and 13 minutes, that is 11 hours and 44 minutes of CPU time; this includes the sessions of Isabelle and of the Archive of Formal Proofs on which the library depends.

The experimental evaluation for this run is `evaluation/experiments_8h.sh`. [Stub, to be filled in.]

### Full run

```
isabelle build -D .
```

This builds every session listed in `ROOTS`, which comprises the whole library and every section of the index. Each section of the index checks again the theories of the library that it imports, so this run takes longer than the previous one. On the same machine it took 3 hours and 5 minutes, that is 16 hours and 48 minutes of CPU time, of which the index took 52 minutes, that is 5 hours and 4 minutes of CPU time. After the run within 8 hours, the sessions of the library are not built again, and this run only adds the time of the index.

The experimental evaluation for this run is `evaluation/experiments_full.sh`. [Stub, to be filled in.]
