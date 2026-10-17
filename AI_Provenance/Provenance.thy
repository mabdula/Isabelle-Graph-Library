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
  \<^descr> \<open>ai\<close>: developed by an LLM alone.

  Parts without a label are \<open>unmarked\<close>.
\<close>

ML \<open>
structure Provenance =
struct

val kinds = ["human", "ai", "ai_human"];

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
  until the next @{command provenance} or the end of the theory. Importing
  theories start unmarked.
\<close>

ML \<open>
structure Provenance_Switch =
struct

structure Data = Theory_Data
(
  type T = string option;
  val empty = NONE;
  fun merge _ = NONE;
);

val get = Data.get;

val _ =
  Theory.setup (Theory.at_begin (fn thy =>
    if is_some (Data.get thy) then SOME (Data.put NONE thy) else NONE));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>provenance\<close>
    "set the label (human, ai_human, or ai) of subsequent commands"
    (Provenance.parse_kind >> (fn (kind, pos) => fn lthy =>
      (Provenance.report lthy (kind, pos);
       Local_Theory.background_theory (Data.put (SOME kind)) lthy)));

end;
\<close>


section \<open>Exceptions\<close>

text \<open>
  The document marker \<open>\<^marker>\<open>provenance kind\<close>\<close> overrides the label for a single
  command, including the proof of a goal statement.
\<close>

ML \<open>
structure Provenance_Marker =
struct

structure Data = Proof_Data
(
  type T = string option;
  fun init _ = NONE;
);

val get = Data.get;

val _ =
  Theory.setup
    (Document_Marker.setup0 \<^binding>\<open>provenance\<close> Provenance.parse_kind
      (fn (kind, pos) => fn ctxt =>
        (Provenance.report ctxt (kind, pos); Data.put (SOME kind) ctxt)));

end;
\<close>


section \<open>Report\<close>

text \<open>
  Batch builds export a tab-separated table \<^verbatim>\<open>provenance\<close> for each theory,
  with one row per command:

  \<^descr> \<open>line\<close>: source line of the command;
  \<^descr> \<open>command\<close>: command name;
  \<^descr> \<open>kind\<close>: label, where proof commands inherit it from their goal statement;
  \<^descr> \<open>facts\<close>: names of facts introduced by the command.

  The table is retrieved via \<^verbatim>\<open>isabelle export -x "*:provenance" SESSION\<close>.
\<close>

ML \<open>
structure Provenance_Report =
struct

fun facts_of state =
  if Toplevel.is_toplevel state then NONE
  else SOME (Global_Theory.facts_of (Toplevel.theory_of state));

fun new_facts prev state =
  (case (facts_of prev, facts_of state) of
    (SOME facts0, SOME facts) => map #1 (Facts.dest_static true [facts0] facts)
  | _ => []);

fun export ({segments, adjust_pos, ...}: Thy_Info.presentation_context) thy =
  let
    fun row ({span, command, state, ...}: Document_Output.segment) (prev, goal_kind) =
      let
        val in_proof = Toplevel.is_proof prev;
        val ctxt = Toplevel.presentation_context state;
        val kind =
          (case Provenance_Marker.get ctxt of
            SOME kind => SOME kind
          | NONE =>
              if in_proof then goal_kind
              else Provenance_Switch.get (Proof_Context.theory_of ctxt));
        val line = Position.line_of (adjust_pos (#1 (Command_Span.range span)));
        val fields =
          [the_default "" (Option.map string_of_int line), Toplevel.name_of command,
            the_default "unmarked" kind, implode_space (new_facts prev state)];
      in (fields, (state, if in_proof then goal_kind else kind)) end;

    val (rows, _) =
      fold_map row (filter_out (Command_Span.is_ignored o #span) segments)
        (Toplevel.make_state NONE, NONE);
    val table = ["line", "command", "kind", "facts"] :: rows;
  in
    Export.export thy \<^path_binding>\<open>provenance\<close>
      [XML.Text (cat_lines (map (space_implode "\t") table) ^ "\n")]
  end;

val _ = Theory.setup (Thy_Info.add_presentation export);

end;
\<close>

end
