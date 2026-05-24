theory More_Eisbach
imports General_ML_Tools "HOL-Eisbach.Eisbach_Tools"
begin

print_claset
  
find_theorems "(\<And>x. ?P x \<Longrightarrow> ?Q x) \<Longrightarrow> ?P \<le> ?Q"

(* Test lemma to verify we have not messed up simplifier by wrong import order of Eisbach *)
lemma "i<length a \<Longrightarrow> (a@b)!i = a!i"
  by (simp add: nth_append)


method_setup then_else = \<open>let
in
  Method.text_closure -- Method.text_closure -- Method.text_closure >>
    (fn ((textb, textt), texte) => fn ctxt => fn using => fn st =>
      let
        val bmethod = Method.evaluate_runtime textb ctxt using;
        val tmethod = Method.evaluate_runtime textt ctxt using;
        val emethod = Method.evaluate_runtime texte ctxt using;
      in
        (case try (fn st => bmethod st |> Seq.pull) st of
          SOME (SOME (Seq.Result st,_)) => tmethod st
        | _ => emethod st)
      end)
end     
\<close>

method_setup solved_then_else = \<open>let
in
  Method.text_closure -- Method.text_closure -- Method.text_closure >>
    (fn ((textb, textt), texte) => fn ctxt => fn using =>
      let
        val bmethod = method_evaluate textb ctxt [];
        val tmethod = method_evaluate textt ctxt [];
        val emethod = method_evaluate texte ctxt [];
      in
        SIMPLE_METHOD (bmethod SOLVED_THEN_ELSE (tmethod, emethod)) using
      end)
end     
\<close>



method_setup then_all_new_fwd =
 \<open>Method.text_closure -- Method.text_closure >> (fn (m1,m2) => fn ctxt => fn facts =>
   let
    val tac1 = method_evaluate m1 ctxt [] |> SELECT_GOAL 
    val tac2 = method_evaluate m2 ctxt [] |> SELECT_GOAL
   
   in SIMPLE_METHOD' (tac1 THEN_ALL_NEW_FWD tac2) facts end)
\<close>

method repeat_all_new_fwd methods m = (then_all_new_fwd \<open>m\<close> \<open>(repeat_all_new_fwd \<open>m\<close>)?\<close>)


method_setup focus_params_fixed =
 \<open>Method.text_closure >> (fn m1src => fn ctxt => fn facts =>
   let
      val m1 = Method.evaluate_runtime m1src ctxt []
      fun tac1 ctxt = NO_CONTEXT_TACTIC ctxt m1 
   
   in SIMPLE_METHOD' (Subgoal.FOCUS_PARAMS_FIXED (fn {context, ...} => tac1 context) ctxt) facts end)
\<close>

method_setup on_subgoal =
 \<open>Scan.lift Parse.nat -- Method.text_closure >> (fn (i,m) => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (SELECT_GOAL tac i) facts end)
\<close> \<open>Execute method on specified subgoal\<close>


method_setup repeat =
 \<open>Scan.lift Parse.nat -- Method.text_closure >> (fn (n,m) => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (REPEAT_DETERM_N n tac) facts end)
\<close>

method_setup repeat1 =
 \<open>Scan.lift Parse.nat -- Method.text_closure >> (fn (n,m) => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (tac THEN REPEAT_DETERM_N (n-1) tac) facts end)
\<close>

method_setup parallel_all =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (PARALLEL_GOALS tac) facts end)
\<close>

method_setup can =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac st' = method_evaluate m ctxt facts st'

   in SIMPLE_METHOD (CAN tac) facts end)
\<close>



method_setup seqs = \<open>
  let
    fun SEQS abort_tac [] = all_tac
      | SEQS abort_tac (m::ms) = m THEN_ELSE (SEQS abort_tac ms, abort_tac)
  in
    Method.text_closure --| Scan.lift @{keyword \<open>:\<close>} -- Scan.repeat1 Method.text_closure >> (fn (abm,ms) => fn ctxt => fn facts => let
      val abort_tac = method_evaluate abm ctxt facts
      val tacs = map (fn m => method_evaluate m ctxt facts) ms
    in
      SIMPLE_METHOD (SEQS abort_tac tacs) facts
    end)
  end
\<close> \<open>\<open>seqs abort m\<^sub>1 ... m\<^sub>n\<close>: Execute as many of the given methods. If one fails, execute abort\<close>


ML \<open>
  structure More_Eisbach_Basic = struct
    fun apply_method_noargs name ctxt =
      NO_CONTEXT_TACTIC ctxt (Method_Closure.apply_method ctxt name [] [] [] ctxt [])
      |> SELECT_GOAL;
  end
  
  open More_Eisbach_Basic
\<close>



end
