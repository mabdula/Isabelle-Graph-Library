theory Provenance
  imports Pure
  keywords "provenance" :: thy_decl
begin

section \<open>Provenance of theory content\<close>

text \<open>
  Parts of a theory are labelled by how they were developed:

  \<^descr> \<open>human\<close>: developed by humans;
  \<^descr> \<open>ai_human\<close>: developed collaboratively by humans and an LLM, e.g.\ a human
    prompted the LLM in detail on how to formalise a concept, revised its output, or
    formalised parts of it manually;
  \<^descr> \<open>ai\<close>: written from scratch by an LLM, e.g.\ auxiliary lemmas and definitions.

  Parts without a label are \<open>unmarked\<close>.

  An LLM makes no judgement between \<open>ai\<close> and \<open>ai_human\<close>: it labels everything it
  writes from scratch \<open>ai\<close>, and lines that it edits keep their label. The labels
  \<open>human\<close> and \<open>ai_human\<close> are assigned by humans.

  This theory only defines the syntax of the labels: Isabelle checks that every label is one
  of the three above, and reports it as markup. The labels have no other effect on the
  theory. They are counted from the theory sources by the separate tool
  \<^verbatim>\<open>isabelle ai_provenance\<close>.
\<close>

ML \<open>
structure Provenance =
struct

val kinds = ["human", "ai_human", "ai"];

val parse_kind =
  Parse.group (fn () => "provenance kind " ^ commas_quote kinds)
    (Parse.position (Scan.first (map Parse.reserved kinds)));

fun report ctxt (kind, pos) =
  Context_Position.report ctxt pos ("provenance", [("kind", kind)]);

end;
\<close>


section \<open>Switch\<close>

text \<open>
  \<^theory_text>\<open>provenance kind\<close> sets the label of all subsequent commands,
  until the next @{command provenance} or the end of the theory. Every theory starts
  unmarked.
\<close>

ML \<open>
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>provenance\<close>
    "set the label (human, ai_human, or ai) of subsequent commands"
    (Provenance.parse_kind >> (fn kind => fn lthy => (Provenance.report lthy kind; lthy)));
\<close>


section \<open>Exceptions\<close>

text \<open>
  The document marker \<open>\<^marker>\<open>provenance kind\<close>\<close> overrides the label of the
  command it is attached to, and of the commands that belong to it:

  \<^item> on a goal statement or a block, e.g.\ \<^theory_text>\<open>lemma\<close>, \<^theory_text>\<open>have\<close>,
    \<^theory_text>\<open>show\<close>, \<^theory_text>\<open>proof\<close>, or \<^theory_text>\<open>{\<close>, it labels everything up to the point where
    that goal or block is closed;
  \<^item> on \<^theory_text>\<open>apply\<close>, it labels the rest of the apply script, including the
    closing \<^theory_text>\<open>done\<close>;
  \<^item> on any other command, e.g.\ \<^theory_text>\<open>by\<close>, it labels that command only.

  For instance, the statement of a lemma written by a human and its proof found by an LLM
  are labelled by \<^theory_text>\<open>by \<^marker>\<open>provenance ai\<close> auto\<close> in a part labelled
  \<open>human\<close>. Markers can be nested; once a goal or block is closed, the enclosing label
  applies again.
\<close>

ML \<open>
val _ =
  Theory.setup
    (Document_Marker.setup0 \<^binding>\<open>provenance\<close> Provenance.parse_kind
      (fn kind => fn ctxt => (Provenance.report ctxt kind; ctxt)));
\<close>

end
