# AI provenance: instructions for LLMs

Every part of an Isabelle theory carries a provenance label: `human`, `ai_human`, or `ai`.
Humans assign `human` and `ai_human`. You make no judgement between the labels:

- Everything you write from scratch is `ai`: definitions, statements, proofs, and proof steps.
- Lines that you edit keep their label.
- `ai` and `ai_human` mean that an LLM made a semantic contribution: a new definition, statement,
  proof, or proof step. Mechanical work is not an AI contribution, even when you write the new
  lines yourself. Text that you copy and paste, adapt to renamed or changed constants, restructure
  without changing the steps of a proof (e.g. a block `{ fix x assume A have B }` turned into
  `have B if A for x`), or only lay out differently keeps the label of the text it comes from.

## Syntax

- `provenance ai` labels all following commands, until the next `provenance` command or the end of the theory. It cannot be used inside proofs.
- The marker `\<^marker>\<open>provenance ai\<close>`, written directly after a command keyword, overrides the current label:
  - on a goal or block (`lemma`, `have`, `show`, `obtain`, `proof`, `{`), it labels everything up to the point where that goal or block is closed;
  - on `apply`, it labels the rest of the apply script, including `done`;
  - on any other command, e.g. `by`, it labels that command only.
- Examples: `lemma \<^marker>\<open>provenance ai\<close> foo: ...` labels a lemma and its proof; `by \<^marker>\<open>provenance ai\<close> auto` labels only the proof; `have \<^marker>\<open>provenance ai\<close> ...` labels one step of an Isar proof and its sub-proof.
- The keyword is only available in theories that import `AI_Provenance.Provenance`, directly or through other imports. If a theory you create does not reach it, add it as the last of the imports, and add `AI_Provenance` to the `sessions` of the ROOT file. If it is the first import, the theory gets the simplifier set-up of Pure instead of that of HOL, and simple proofs and definitions fail.

## Rules

1. Put `provenance ai` directly after `begin` of every theory you create.
2. When you add material to a part with another label, label it `ai` with a marker, or put `provenance ai` before it and restore the previous label after it.
3. When you prove a statement that you did not write, the statement keeps its label and the proof gets an `ai` marker, on its `proof`, `apply`, or `by`.
4. Never change the label of an existing line, whether or not you edit it. Write `human` or `ai_human` only to restore the label of the existing lines that follow material you inserted (rule 2).
5. Check your labels with `isabelle ai_provenance -s SESSION`, which fails if a command other than the theory header is unmarked.
