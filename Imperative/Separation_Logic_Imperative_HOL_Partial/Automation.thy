section \<open>Automation\<close>
theory Automation
imports Hoare_Triple "Tools/Basic_Tools" (*"../Lib/Refine_Util"*)
begin

text \<open>
  In this theory, we provide a set of tactics and a simplifier setup for easy
  reasoning with our separation logic.
\<close>




subsection \<open>Normalization of Assertions\<close>
text \<open>
  In this section, we provide a set of lemmas and a simplifier
  setup to bring assertions to a normal form. We provide a simproc that
  detects pure parts of assertions and duplicate pointers. Moreover,
  we provide ac-rules for assertions. See Section~\ref{sec:auto:overview}
  for a short overview of the available proof methods.
\<close>

thm mult_ac[no_vars]

lemma mult_left_ac: 
  "a * (b * c) = a * b * c"
  "a * b = b * a"
  "a * c * b = a * b * c"
  for a b c :: "'a::ab_semigroup_mult"
  by (simp_all add: ac_simps)

lemma mult_left_assoc: 
  "a * (b * c) = a * b * c"
  for a b c :: "'a::ab_semigroup_mult"
  by (simp_all add: ac_simps)
  
lemmas assn_aci =   
  inf_aci[where 'a=assn] 
  sup_aci[where 'a=assn] 
  mult_left_ac[where 'a=assn] 

lemmas star_assoc = mult.assoc[where 'a=assn] 
lemmas assn_assoc = 
  mult_left_assoc inf_assoc[where 'a=assn] sup_assoc[where 'a=assn] 

lemma merge_true_star_ctx: "true * (true * P) = true * P"
  by (simp add: ac_simps)
  
lemmas star_aci = 
  mult.assoc[where 'a=assn] mult.commute[where 'a=assn] mult.left_commute[where 'a=assn]
  assn_one_left mult_1_right[where 'a=assn]
  merge_true_star merge_true_star_ctx

text \<open>Move existential quantifiers to the front of assertions\<close>
lemma ex_assn_move_out[simp]:
  "\<And>Q R. (\<exists>\<^sub>Ax. Q x) * R = (\<exists>\<^sub>Ax. (Q x * R))"
  "\<And>Q R. R * (\<exists>\<^sub>Ax. Q x) = (\<exists>\<^sub>Ax. (R * Q x))"

  "\<And>P Q. (\<exists>\<^sub>Ax. Q x) \<and>\<^sub>A P = (\<exists>\<^sub>Ax. (Q x \<and>\<^sub>A P)) "
  "\<And>P Q. Q \<and>\<^sub>A (\<exists>\<^sub>Ax. P x) = (\<exists>\<^sub>Ax. (Q \<and>\<^sub>A P x))"

  "\<And>P Q. (\<exists>\<^sub>Ax. Q x) \<or>\<^sub>A P = (\<exists>\<^sub>Ax. (Q x \<or>\<^sub>A P))"
  "\<And>P Q. Q \<or>\<^sub>A (\<exists>\<^sub>Ax. P x) = (\<exists>\<^sub>Ax. (Q \<or>\<^sub>A P x))"
  apply -
  apply (simp add: ex_distrib_star)
  apply (subst mult.commute)
  apply (subst (2) mult.commute)
  apply (simp add: ex_distrib_star)

  apply (simp add: ex_distrib_and)
  apply (subst inf_commute)
  apply (subst (2) inf_commute)
  apply (simp add: ex_distrib_and)

  apply (simp add: ex_distrib_or)
  apply (subst sup_commute)
  apply (subst (2) sup_commute)
  apply (simp add: ex_distrib_or)
  done

text \<open>Extract pure assertions from and-clauses\<close>
lemma and_extract_pure_left_iff[simp]: "\<up>b \<and>\<^sub>A Q = (emp\<and>\<^sub>AQ)*\<up>b"
  by (cases b) auto

lemma and_extract_pure_left_ctx_iff[simp]: "P*\<up>b \<and>\<^sub>A Q = (P\<and>\<^sub>AQ)*\<up>b"
  by (cases b) auto

lemma and_extract_pure_right_iff[simp]: "P \<and>\<^sub>A \<up>b = (emp\<and>\<^sub>AP)*\<up>b"
  by (cases b) (auto simp: assn_aci)

lemma and_extract_pure_right_ctx_iff[simp]: "P \<and>\<^sub>A Q*\<up>b = (P\<and>\<^sub>AQ)*\<up>b"
  by (cases b) auto

lemmas and_extract_pure_iff = 
  and_extract_pure_left_iff and_extract_pure_left_ctx_iff
  and_extract_pure_right_iff and_extract_pure_right_ctx_iff

lemma merge_move_true_right: 
  "true*true = true"
  "P*true*true = P*true"
  "NO_MATCH true P \<Longrightarrow> true*P = P*true"
  "NO_MATCH true P \<Longrightarrow> P*true*Q = P*Q*true"
  by (simp_all add: algebra_simps)
  

lemma move_pure_right:
  "NO_MATCH (\<up>XX) A \<Longrightarrow> \<up>P * A = A * \<up>P"  
  "NO_MATCH (\<up>XX) B \<Longrightarrow> A*\<up>P*B = A*B*\<up>P"
  by (auto simp: ac_simps)
  
    
lemmas norm_assertion_simps =
  (* Neutral elements *)
  mult_1[where 'a=assn] mult_1_right[where 'a=assn]
  inf_top_left[where 'a=assn] inf_top_right[where 'a=assn]
  sup_bot_left[where 'a=assn] sup_bot_right[where 'a=assn]

  (* Zero elements *)
  star_false_left star_false_right
  inf_bot_left[where 'a=assn] inf_bot_right[where 'a=assn]
  sup_top_left[where 'a=assn] sup_top_right[where 'a=assn]

  (* Associativity *)
  mult_left_assoc[where 'a=assn]
  inf_assoc[where 'a=assn]
  sup_assoc[where 'a=assn]

  (* Existential Quantifiers *)
  ex_assn_move_out ex_assn_const

  (* Extract pure assertions from conjunctions *)
  and_extract_pure_iff

  (* Merging *)
  (*merge_pure_star*) merge_pure_and merge_pure_or
  merge_move_true_right (* Merge and move true to the right *) 
  inf_idem[where 'a=assn] sup_idem[where 'a=assn]

  (* Duplicated References *)
  sngr_same_false snga_same_false


subsubsection \<open>Simplifier Setup Fine-Tuning\<close>
text \<open>Imperative HOL likes to simplify pointer inequations to this strange
  operator. We do some additional simplifier setup here\<close>
lemma not_same_noteqr[simp]: "\<not> a=!=a"
  by (metis Ref.unequal)
declare Ref.noteq_irrefl[dest!]

lemma not_same_noteqa[simp]: "\<not> a=!!=a"
  by (metis Array.unequal)
declare Array.noteq_irrefl[dest!]

text \<open>However, it is safest to disable this rewriting, as there is
  a working standard simplifier setup for \<open>(\<noteq>)\<close>
\<close>
declare Ref.unequal[simp del]
declare Array.unequal[simp del]


subsection \<open>Normalization of Entailments\<close>

text \<open>Used by existential quantifier extraction tactic\<close>
lemma enorm_exI': (* Incomplete, as chosen x may depend on heap! *)
  "(\<And>x. Z x \<longrightarrow> (P \<Longrightarrow>\<^sub>A Q x)) \<Longrightarrow> (\<exists>x. Z x) \<longrightarrow> (P \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. Q x))"
  by (metis ent_ex_postI)
  
text \<open>Example of how to build an extraction lemma.\<close>
thm enorm_exI'[OF enorm_exI'[OF imp_refl]]

lemmas ent_triv = ent_true ent_false

text \<open>Dummy rule to detect Hoare triple goal\<close>
lemma is_hoare_triple: "<P> c <Q> \<Longrightarrow> <P> c <Q>" .
text \<open>Dummy rule to detect entailment goal\<close>
lemma is_entails: "P\<Longrightarrow>\<^sub>AQ \<Longrightarrow> P \<Longrightarrow>\<^sub>AQ" .




subsection \<open>Precondition tag\<close>

definition "sep_PRE P \<equiv> \<exists>h. h\<Turnstile>P"  
  
lemma sep_PRE_starE[elim!]:
  assumes "sep_PRE (A*B)" obtains "sep_PRE A" "sep_PRE B"
  using assms unfolding sep_PRE_def
  using mod_starD by blast

lemma sep_PRE_emp[simp]: "sep_PRE emp" unfolding sep_PRE_def
  using mod_emp_simp by blast
lemma sep_PRE_true[simp]: "sep_PRE true" unfolding sep_PRE_def
  using mod_true by blast
  
lemma sep_PRE_false[simp]: "sep_PRE false \<longleftrightarrow> False" unfolding sep_PRE_def by auto
  
lemma sep_PRE_pure[simp]: "sep_PRE (\<up>C) \<longleftrightarrow> C" by (cases C) auto

lemma ent_sep_PRE_I: "\<lbrakk>sep_PRE P \<Longrightarrow> P\<Longrightarrow>\<^sub>AQ\<rbrakk> \<Longrightarrow> P\<Longrightarrow>\<^sub>AQ"
  unfolding sep_PRE_def
  using entails_def by blast


subsection \<open>Frame Matcher\<close>



(* Trying new frame matcher *)

text \<open>This frame matcher works on frames and entailsments from left to right, 
  including pure assertions. This ensures a smooth and predictable handling of 
  schematic variables.

  Thus, we normalize separation conjunctions to be associated to the right. 
\<close>

(*definition [simp]: "FI_QUERY P Q F \<equiv> P \<Longrightarrow>\<^sub>A Q*F"*)
definition [simp]: "FI_COMP P\<^sub>1 P\<^sub>2 Q F \<equiv> P\<^sub>1*P\<^sub>2 \<Longrightarrow>\<^sub>A Q*F"

(*lemma FI_init: "FI_COMP P emp Q F \<Longrightarrow> FI_QUERY P Q F" by simp*)

(* Rotate a frame, bringing the next precondition atom to the front *)
lemma FI_rotate: 
  "FI_COMP PP (DD*P) Q F \<Longrightarrow> FI_COMP (P*PP) DD Q F"
  by (simp add: algebra_simps)

(* Match step for frame *)  

lemma FI_match_pure:
  assumes "C"
  shows "FI_COMP PP emp CC F \<Longrightarrow> FI_COMP PP emp (\<up>C * CC) F"
    and "FI_COMP PP emp emp F \<Longrightarrow> FI_COMP PP emp (\<up>C) F"
  using assms
  by (fastforce simp add: entails_def)+
  

lemma FI_match:  
  assumes "P \<Longrightarrow>\<^sub>A Q"
  shows
  "FI_COMP PP DD QQ F \<Longrightarrow> FI_COMP (P*PP) DD (Q*QQ) F" (* Regular match *)
  "FI_COMP emp DD QQ F \<Longrightarrow> FI_COMP P DD (Q*QQ) F" (* Last atom in premise *)
  "FI_COMP PP DD emp F \<Longrightarrow> FI_COMP (P*PP) DD Q F" (* Last atom in conclusion *)
  "FI_COMP emp DD emp F \<Longrightarrow> FI_COMP P DD Q F" (* Last atoms in prems and conclusion *)
  using assms
  by (simp_all add: ent_star_mono star_assoc)
  
  
(* Rotate back, e.g., after match was found. There are a few special cases, when the last
  atom was matched. The rules must be tried in order, without backtracking. *)
lemma FI_rotate_back:  
  "FI_COMP P D Q F \<Longrightarrow> FI_COMP emp (D*P) Q F"
  "FI_COMP (P*PP) D Q F \<Longrightarrow> FI_COMP PP (D*P) Q F"
  by (simp_all add: algebra_simps)
  
  
lemma FI_finalize: "FI_COMP P emp emp P" by simp

lemma ENT_finalize: 
  "FI_COMP emp emp emp emp" 
  "FI_COMP P emp emp true" 
  by simp_all

method sep_simp_assn = (simp named_ss HOL_basic_ss_nomatch: norm_assertion_simps)
  
method sep_assoc_right = (simp only: star_assoc)  




subsubsection \<open>Frame Inference\<close>
lemma frame_inference_init:
  assumes "FI_COMP P emp Q F"
  shows "P \<Longrightarrow>\<^sub>A Q * F"
  using assms unfolding FI_COMP_def by simp

lemma FI_COMP_pre_cong: "P=P' \<Longrightarrow> FI_COMP P PP Q F = FI_COMP P' PP Q F" by simp  

lemma FI_pre_init:
  "\<And>P. \<lbrakk>\<And>x. FI_COMP (P x) PP Q F \<rbrakk> \<Longrightarrow> FI_COMP (\<exists>\<^sub>Ax. P x) PP Q F"
  "\<And>P. \<lbrakk> C \<Longrightarrow> FI_COMP P PP Q F \<rbrakk> \<Longrightarrow> FI_COMP (P * \<up>C) PP Q F"
  "\<lbrakk> C \<Longrightarrow> FI_COMP emp PP Q F \<rbrakk> \<Longrightarrow> FI_COMP (\<up>C) PP Q F"
  apply (simp_all add: ac_simps ent_ex_preI)
  by (cases C; simp)
  
lemma FI_ex_postI: "FI_COMP P PP (Q x) F \<Longrightarrow> FI_COMP P PP (\<exists>\<^sub>Ax. Q x) F"  
  by (simp add: ent_ex_postI)

lemma FI_comp_sep_PREI: "\<lbrakk> sep_PRE P \<Longrightarrow> FI_COMP P emp Q F \<rbrakk> \<Longrightarrow> FI_COMP P emp Q F"
  using ent_sep_PRE_I by fastforce
    

method sep_fri_extract_pre = changed \<open>
  (simp named_ss HOL_ss_nomatch: move_pure_right cong: FI_COMP_pre_cong)?,
  (intro FI_pre_init)?
  \<close>
  
method sep_fri_init = changed \<open>
  sep_simp_assn?,
  sep_fri_extract_pre?,
  (rule FI_comp_sep_PREI),
  (intro FI_ex_postI)?,
  sep_assoc_right?
\<close>
    
  
method sep_fri_rotate_back = ((determ \<open>mrule FI_rotate_back\<close>)+)?

method sep_fri_match_pure methods solver = rule FI_match_pure, (solver;fail), sep_fri_rotate_back

method sep_fri_match_assn = rule FI_match[OF ent_refl], sep_fri_rotate_back

method sep_fri_not_finished = fails \<open>rule asm_rl[of "FI_COMP _ _ emp _"]\<close>

method sep_fri_match methods solver = (sep_fri_match_pure solver | sep_fri_match_assn)


method sep_fri_dbg_pure methods solver = 
  rule FI_match_pure, 
  solved_then_else \<open>solver;succeed\<close> sep_fri_rotate_back succeed

method sep_fri_rotate = determ \<open>mrule FI_rotate\<close>

method fails methods m = then_else \<open>can m\<close> fail succeed

method sep_fri_infer methods solver = (sep_fri_not_finished, (sep_fri_match solver | sep_fri_rotate))+

method sep_fri_finalize = (rule FI_finalize)

method sep_fri methods solver = 
  (mrule frame_inference_init),
  sep_fri_init?,
  (sep_fri_infer solver)?,
  sep_fri_finalize

method sep_fri_dbg_keep methods solver = 
  (mrule frame_inference_init),
  sep_fri_init?,
  (sep_fri_infer solver)?
  

(*
  Algorithm for frame inference:

  init:
    assn_norm_simps, assoc-star-right
  
  match:
    match_pure, solve-goal (auto), rotate_back
    
  infer:
    (match|rotate)+

  finalize: assoc-star-left    
    
*)
  
  
subsubsection \<open>Entailment Solver\<close>

lemma FI_norm_ent_true:
  "FI_COMP P PP emp true \<Longrightarrow> FI_COMP P PP (true) emp"
  "FI_COMP P PP emp true \<Longrightarrow> FI_COMP P PP (true) true"
  "FI_COMP P PP Q true \<Longrightarrow> FI_COMP P PP (Q*true) emp"
  "FI_COMP P PP Q true \<Longrightarrow> FI_COMP P PP (Q*true) true"
  by simp_all

lemma entails_solve_init:
  "FI_COMP P emp Q emp \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q"
  by (simp_all add: assn_aci)

method sep_ent_finalize = (rule ENT_finalize)

method sep_ent_init =
  (determ \<open>mrule entails_solve_init\<close>),
  sep_simp_assn?,
  sep_fri_extract_pre?,
  (rule FI_comp_sep_PREI),
  (intro FI_ex_postI FI_norm_ent_true)?,
  sep_assoc_right?

method sep_ent methods solver = 
  sep_ent_init,
  (sep_fri_infer solver)?,
  sep_ent_finalize

method sep_ent_dbg_keep methods solver = 
  sep_ent_init,
  (sep_fri_infer solver)?
  
  
lemma norm_pre_congs:  
  assumes "P=P'"  
  shows 
    "<P>c<QQ> = <P'>c<QQ>"
    "(P\<Longrightarrow>\<^sub>AQ) = (P'\<Longrightarrow>\<^sub>AQ)"
  using assms by auto
      
lemma ent_pure_preI:
  "\<lbrakk> C \<Longrightarrow> P\<Longrightarrow>\<^sub>AQ \<rbrakk> \<Longrightarrow> P*\<up>C \<Longrightarrow>\<^sub>A Q"  
  "\<lbrakk> C \<Longrightarrow> emp\<Longrightarrow>\<^sub>AQ \<rbrakk> \<Longrightarrow> \<up>C \<Longrightarrow>\<^sub>A Q"  
  by simp_all
  
lemmas norm_preI = ent_ex_preI ent_pure_preI
  
lemma ht_exEI: "\<lbrakk> \<And>x. <P x>c<Q> \<rbrakk>\<Longrightarrow> <\<exists>\<^sub>Ax. P x>c<Q>"
  by (meson hoare_triple_wlp mod_exE)

find_theorems "<_*\<up>_>_<_>"  
  
lemma ht_extract_pre_pure:    
  "\<lbrakk> C \<Longrightarrow> <P>c<Q> \<rbrakk> \<Longrightarrow> <P*\<up>C>c<Q>"
  "\<lbrakk> C \<Longrightarrow> <emp>c<Q> \<rbrakk> \<Longrightarrow> <\<up>C>c<Q>"
  subgoal using ht_frame_drop by fastforce
  subgoal by (metis (full_types) ht_false pure_false pure_true)
  done
  
lemmas norm_pre_extractI = ent_ex_preI ht_exEI ent_pure_preI ht_extract_pre_pure


(* Normalize preconditions and extract pure of entailments and Hoare triples *)
method sep_norm_pre = changed \<open>
  sep_simp_assn?,
  (simp named_ss HOL_ss_nomatch: move_pure_right cong: norm_pre_congs)?,
  (intro norm_pre_extractI)?\<close>
  
    
  
subsection \<open>Verification Condition Generator\<close>

named_theorems sep_heap_rules "Seplogic: VCG heap rules"
named_theorems sep_decon_rules "Seplogic: VCG deconstruct rules"

lemmas basic_deconstruct_rules[sep_decon_rules] = 
  decon_raise decon_bind decon_if decon_return decon_let 
  decon_case_prod decon_case_list decon_case_option decon_case_sum

lemmas basic_heap_rules[sep_heap_rules] = 
  ref_rule
  lookup_rule
  update_rule
  new_rule
  make_rule
  of_list_rule
  length_rule
  nth_rule
  upd_rule
  freeze_rule



text \<open>
  The vcg works on goals of the form
  
  \<open> \<lbrakk> \<dots>; h\<Turnstile>P \<rbrakk> \<Longrightarrow> wlp c ?Q h \<close>
  \<open> \<lbrakk> \<dots>; h\<Turnstile>P \<rbrakk> \<Longrightarrow> h\<Turnstile>Q \<close>
  
  For initialization, it converts a hoare-triple goal to a wlp-goal, and applies a consequence rule to
  achieve a schematic postcondition.
  
  Before each step, a goal is normalized by eliminating existential quantifiers in the precondition, 
  and extracting pure assertions.
\<close>

thm hoare_triple_wlpI wlp_cons

method sep_vcg_init = rule hoare_triple_wlpI

thm mod_exE

lemma mod_pureE1:
  assumes "h \<Turnstile> (P * \<up>C)"
  obtains "C" "h \<Turnstile> P"
  using assms by (cases C) auto

lemma mod_pureE2:  
  assumes "h \<Turnstile> \<up>C"
  obtains "C" "h \<Turnstile> emp"
  using assms by (cases C) auto
  
lemmas mod_pureE = mod_pureE1 mod_pureE2
    
  
method sep_vcg_step_init = changed \<open>
  sep_simp_assn?, 
  (simp named_ss HOL_basic_ss_nomatch: move_pure_right case_prod_app)?,
  (elim mod_exE mod_pureE)?
  \<close>

method sep_vcg_step_decon_aux = (rule sep_decon_rules)  

method sep_vcg_step_heap_aux methods solver uses heap =
  erule wlp_apply_ht,
  on_subgoal 2 \<open>rprems | assumption | rule heap sep_heap_rules\<close>,
  sep_fri solver

method sep_vcg_dbg_step_heap_aux_keep methods solver uses heap =
  erule wlp_apply_ht,
  on_subgoal 2 \<open>rprems | assumption | rule heap sep_heap_rules\<close>,
  sep_fri_dbg_keep solver
  
  
method sep_vcg_step_ent methods solver = (erule ent_fwd, sep_ent solver)

method sep_vcg_dbg_step_ent_keep methods solver 
  = (erule ent_fwd, sep_ent_dbg_keep solver)
  
    
method sep_vcg_step methods solver uses heap =
  (sep_vcg_init)
| sep_vcg_step_init?,(sep_vcg_step_decon_aux | sep_vcg_step_heap_aux solver heap: heap)
| sep_vcg_step_ent solver
| (solver;fail)
  
method sep_vcg_dbg_step methods solver uses heap =
  (sep_vcg_init)
| sep_vcg_step_init?,(sep_vcg_step_decon_aux | sep_vcg_dbg_step_heap_aux_keep solver heap:heap)
| sep_vcg_dbg_step_ent_keep solver
| (solver;fail)
  


method sep_vcg methods solver uses heap = (sep_vcg_step solver heap:heap | sep_ent solver)+

method sep_auto' methods solver uses heap = 
  (sep_vcg solver heap: heap | sep_ent solver | sep_vcg_step_init | ((solver) []))+

  
method_setup ins_facts =
 \<open>Method.text_closure >> (fn m => fn ctxt => SIMPLE_METHOD (method_evaluate m ctxt []))
\<close>
  
  
method sep_auto uses simp split heap intro intro' dest dest' elim elim'
 = ins_facts \<open>sep_auto' \<open>
    auto simp: simp split: split
        intro: intro intro!: "intro'" 
        dest: dest dest!: "dest'" 
        elim: elim elim!: "elim'"
  \<close> heap: heap \<close>
  
  
subsection \<open>Semi-Automatic Reasoning\<close>
text \<open>In this section, we provide some lemmas for semi-automatic reasoning\<close>

text \<open>Forward reasoning with frame. Use \<open>frame_inference\<close>-method 
  to discharge frame assumption.\<close>
lemma ent_frame_fwdI:
  assumes F: "Ps \<Longrightarrow>\<^sub>A P*F"
  assumes R: "P \<Longrightarrow>\<^sub>A R"
  assumes I: "R*F \<Longrightarrow>\<^sub>A Q"
  shows "Ps \<Longrightarrow>\<^sub>A Q"
  using assms
  by (metis ent_refl ent_star_mono ent_trans)

lemma mod_frame_fwdD:
  assumes M: "h\<Turnstile>Ps"
  assumes F: "Ps \<Longrightarrow>\<^sub>A P*F"
  assumes R: "P\<Longrightarrow>\<^sub>AR"
  shows "h\<Turnstile>R*F"
  using assms
  by (meson ent_star_mono entails_def)

lemma ht_frame_fwdI:
  assumes F: "Ps \<Longrightarrow>\<^sub>A P*F"
  assumes "P \<Longrightarrow>\<^sub>A R"
  assumes "<R*F> c <Q>"
  shows "<Ps> c <Q>"
  by (meson F assms(2,3) ent_refl ent_star_mono ht_cons_pre)

method sep_frame_fwd_gen methods solver uses rule =
  sep_norm_pre?,
  (rule ent_frame_fwdI[OF _ rule] ht_frame_fwdI[OF _ rule]  | drule mod_frame_fwdD[OF _ _ rule]),
  sep_fri solver

method sep_frame_fwd uses rule = sep_frame_fwd_gen \<open>auto\<close> rule: rule
  
  
text \<open>Apply precision rule with frame inference.\<close>
lemma prec_frame:
  assumes PREC: "precise P"
  assumes M1: "h\<Turnstile>(R1 \<and>\<^sub>A R2)"
  assumes F1: "R1 \<Longrightarrow>\<^sub>A P x p * F1"
  assumes F2: "R2 \<Longrightarrow>\<^sub>A P y p * F2"
  shows "x=y"
  using preciseD[OF PREC] M1 F1 F2
  by (metis entailsD mod_and_dist)

lemma prec_frame_expl:
  assumes PREC: "\<forall>x y. (h\<Turnstile>(P x * F1) \<and>\<^sub>A (P y * F2)) \<longrightarrow> x=y"
  assumes M1: "h\<Turnstile>(R1 \<and>\<^sub>A R2)"
  assumes F1: "R1 \<Longrightarrow>\<^sub>A P x * F1"
  assumes F2: "R2 \<Longrightarrow>\<^sub>A P y * F2"
  shows "x=y"
  using assms
  by (metis entailsD mod_and_dist)


text \<open>Variant that is useful within induction proofs, where induction
  goes over \<open>x\<close> or \<open>y\<close>\<close>
lemma prec_frame':
  assumes PREC: "(h\<Turnstile>(P x * F1) \<and>\<^sub>A (P y * F2)) \<longrightarrow> x=y"
  assumes M1: "h\<Turnstile>(R1 \<and>\<^sub>A R2)"
  assumes F1: "R1 \<Longrightarrow>\<^sub>A P x * F1"
  assumes F2: "R2 \<Longrightarrow>\<^sub>A P y * F2"
  shows "x=y"
  using assms
  by (metis entailsD mod_and_dist)


lemma ent_wand_frameI:
  assumes "(Q -* R) * F \<Longrightarrow>\<^sub>A S"
  assumes "P \<Longrightarrow>\<^sub>A F * X"
  assumes "Q*X \<Longrightarrow>\<^sub>A R"
  shows "P \<Longrightarrow>\<^sub>A S"
  using assms
  by (metis ent_frame_fwdI ent_wandI mult.commute)

subsubsection \<open>Manual Frame Inference\<close>

lemma ent_true_drop: 
  "P\<Longrightarrow>\<^sub>AQ*true \<Longrightarrow> P*R\<Longrightarrow>\<^sub>AQ*true"
  "P\<Longrightarrow>\<^sub>AQ \<Longrightarrow> P\<Longrightarrow>\<^sub>AQ*true"
  apply (metis assn_times_comm ent_star_mono ent_true merge_true_star_ctx)
  apply (metis assn_one_left ent_star_mono ent_true star_aci(2))
  done

lemma fr_refl: "A\<Longrightarrow>\<^sub>AB \<Longrightarrow> A*C \<Longrightarrow>\<^sub>AB*C"
  by (blast intro: ent_star_mono ent_refl)

lemma fr_rot: "(A*B \<Longrightarrow>\<^sub>A C) \<Longrightarrow> (B*A \<Longrightarrow>\<^sub>A C)" 
  by (simp add: assn_aci)

lemma fr_rot_rhs: "(A \<Longrightarrow>\<^sub>A B*C) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A C*B)" 
  by (simp add: assn_aci)

lemma ent_refl_true: "A \<Longrightarrow>\<^sub>A A * true"
  by (simp add: ent_true_drop(2)) 
    
lemma entt_fr_refl: "F\<Longrightarrow>\<^sub>tF' \<Longrightarrow> F*A \<Longrightarrow>\<^sub>t F'*A" by (rule entt_star_mono) auto
lemma entt_fr_drop: "F\<Longrightarrow>\<^sub>tF' \<Longrightarrow> F*A \<Longrightarrow>\<^sub>t F'"
  using ent_true_drop(1) enttD enttI by blast 
    
    
method_setup fr_rot = \<open>
  let
    fun rot_tac ctxt = 
      resolve_tac ctxt @{thms fr_rot} THEN'
      simp_tac (put_simpset HOL_basic_ss ctxt 
        addsimps @{thms star_assoc[symmetric]})

  in
    Scan.lift Parse.nat >> 
      (fn n => fn ctxt => SIMPLE_METHOD' (
        fn i => REPEAT_DETERM_N n (rot_tac ctxt i)))

  end
\<close>

method_setup fr_rot_rhs = \<open>
  let
    fun rot_tac ctxt = 
      resolve_tac ctxt @{thms fr_rot_rhs} THEN'
      simp_tac (put_simpset HOL_basic_ss ctxt 
        addsimps @{thms star_assoc[symmetric]})

  in
    Scan.lift Parse.nat >> 
      (fn n => fn ctxt => SIMPLE_METHOD' (
        fn i => REPEAT_DETERM_N n (rot_tac ctxt i)))

  end
\<close>


subsubsection \<open>Backward reasoning in entailment\<close>

lemma ent_post_left_guard:"(A \<Longrightarrow>\<^sub>A emp * P) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A P)" by simp

lemma ent_post_right_guard:"(A \<Longrightarrow>\<^sub>A P * emp) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A P)" by simp

lemma post_star_assoc_right:"(A \<Longrightarrow>\<^sub>A P * (Q * R)) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A (P * Q) * R)"
  by (simp add: assn_aci(9))

lemma ent_cons_post_rule:"(Q1 \<Longrightarrow>\<^sub>A Q2) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A (P * Q1) * R) \<Longrightarrow> (A \<Longrightarrow>\<^sub>A (P * Q2) * R)"
    by (meson ent_refl ent_star_mono ent_trans)

method ent_backward_prepare = 
  rule ent_post_left_guard, rule ent_post_right_guard, (simp only: flip:star_assoc)?

method ent_backward_process uses r = 
  repeat_all_new \<open>(rule ent_cons_post_rule[OF r] | rule post_star_assoc_right)\<close>

method ent_backward_finish = simp only:assn_one_left mult_1_right[where 'a=assn] flip:star_assoc

method ent_backward_all uses r = (ent_backward_prepare, ent_backward_process r:r); ent_backward_finish?





(*<*)
subsection \<open>Test Cases\<close>

lemma "\<And>x. A x * true * Q x \<Longrightarrow>\<^sub>A true * A x * Q x"
  apply (simp add: algebra_simps)
  done

lemma "A * (true * B) \<Longrightarrow>\<^sub>A true * A * B"
  apply (simp add: algebra_simps)
  done
  
lemma "h\<Turnstile>true*P*true \<longleftrightarrow> h\<Turnstile>P*true"
  by (simp add: algebra_simps)

lemma "A * true * \<up>(b \<and> c) * true * B \<Longrightarrow>\<^sub>A \<up>b * \<up>c * true *A * B"
  by (simp add: algebra_simps)

lemma "\<exists>y c. \<exists>\<^sub>Ax. P x * (R x * Q y) * \<up> (b \<and> c) \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. \<up>b * (P x * (R x * Q y) * \<up>c))"
  apply (intro exI)
  by sep_auto

lemma "A * B * (\<up>c * B * C * D * \<up>a * true * \<up>d) * (\<exists>\<^sub>Ax. E x * F * \<up>b) * true \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. \<up> (c \<and> a \<and> d \<and> b) *
          true * A * B * (true * B * C * D) * (E x * F))"
  by sep_auto

lemma "<P> c <\<lambda>r. Q r * true * \<up>(b r) * true * \<up>a> 
  \<longleftrightarrow> <P> c <\<lambda>r. Q r * true * \<up>(b r \<and> a)>"
  by sep_auto

  (*
lemma "(h\<Turnstile>((A*B*\<up>b*true*\<up>c*true) \<and>\<^sub>A (\<up>(p=q)*P*Q)))
  \<longleftrightarrow> h \<Turnstile> A * B * true \<and>\<^sub>A P * Q \<and> b \<and> c \<and> p = q"
  apply (auto)
  done
  *)



schematic_goal 
  "P1 * P2 * P3 * P4 \<Longrightarrow>\<^sub>A P3 * ?R1"
  "P1 * (P2 * (P3 * P4)) \<Longrightarrow>\<^sub>A P1 * ?R2"
  "P4 * (P2 * (P1 * P3)) \<Longrightarrow>\<^sub>A P1 * ?R2'"
  "P1 * P2 * P3 * P4 \<Longrightarrow>\<^sub>A P4 * ?R3"
  "P1 * P2 \<Longrightarrow>\<^sub>A P1 * ?R4"
  "P1 * P2 \<Longrightarrow>\<^sub>A P2 * ?R5"
  "P1 \<Longrightarrow>\<^sub>A P1 * ?R6"
  "P1 * P2 \<Longrightarrow>\<^sub>A emp * ?R7"
  by (sep_fri auto)+
  

lemma "\<lbrakk>A; B; C; b 17\<rbrakk> \<Longrightarrow> 
  Q 1 5 3 \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax y z. \<exists>\<^sub>Aa. Q x y z * \<up>(b a) * \<up>(y=5))"
  by sep_auto

thm nth_rule
lemma "<P * x\<mapsto>\<^sub>a[1,2,3]> 
  do { v\<leftarrow>Array.nth x 1; return v } 
  <\<lambda>r. P * x\<mapsto>\<^sub>a[1,2,3] * \<up>(r=2)>"
  by sep_auto


notepad begin
  fix A B D D1 D2 D3 P
  assume 1:"A \<Longrightarrow>\<^sub>A B" 
  have "D * A \<Longrightarrow>\<^sub>A D * B"
    apply(ent_backward_all r:1) 
    apply(rule ent_refl)
    done

  have "A \<Longrightarrow>\<^sub>A B" 
    apply(ent_backward_all r:1)
    apply(rule ent_refl)
    done

  have "A * D1 * D2 * D3 \<Longrightarrow>\<^sub>A B * D1 * D2 * D3"
    apply(ent_backward_all r:1)
    apply(rule ent_refl) 
    done

  have "D1 * D2 * D3 * A \<Longrightarrow>\<^sub>A D1 * D2 * D3 * B"
    apply(ent_backward_all r:1)
    apply(rule ent_refl) 
    done

  have "D1 * A * D2 * D3 \<Longrightarrow>\<^sub>A D1 * B * D2 * D3"
    apply(ent_backward_all r:1)
    apply(rule ent_refl) 
    done

  have "A * A \<Longrightarrow>\<^sub>A B * B" 
    apply(ent_backward_all r:1)
    apply(rule ent_refl) 
    done

  have "D1 * A * D2 * A * D3 \<Longrightarrow>\<^sub>A D1 * B * D2 * B * D3"
    apply(ent_backward_all r:1)
    apply(rule ent_refl) 
    done


  assume 2:"P \<Longrightarrow> A \<Longrightarrow>\<^sub>A B" 
  assume "P"
  have "D * A \<Longrightarrow>\<^sub>A D * B"
    apply(ent_backward_all r:2) 
    apply(rule \<open>P\<close> ent_refl)+
    done

  have "A \<Longrightarrow>\<^sub>A B" 
    apply(ent_backward_all r:2) 
    apply(rule \<open>P\<close> ent_refl)+
    done

  have "A * D1 * D2 * D3 \<Longrightarrow>\<^sub>A B * D1 * D2 * D3"
    apply(ent_backward_all r:2) 
    apply(rule \<open>P\<close> ent_refl)+
    done

  have "D1 * D2 * D3 * A \<Longrightarrow>\<^sub>A D1 * D2 * D3 * B"
    apply(ent_backward_all r:2) 
    apply(rule \<open>P\<close> ent_refl)+
    done

  have "D1 * A * D2 * D3 \<Longrightarrow>\<^sub>A D1 * B * D2 * D3"
    apply(ent_backward_all r:2) 
    apply(rule \<open>P\<close> ent_refl)+
    done

  have "A * A \<Longrightarrow>\<^sub>A B * B" 
    apply(ent_backward_all r:2) 
    apply(rule \<open>P\<close> ent_refl)+
    done

  have "D1 * A * D2 * A * D3 \<Longrightarrow>\<^sub>A D1 * B * D2 * B * D3"
    apply(ent_backward_all r:2) 
    apply(rule \<open>P\<close> ent_refl)+
    done
end


(*>*)

subsection \<open>Quick Overview of Proof Methods\<close> 
  text_raw \<open>\label{sec:auto:overview}\<close>
text \<open>
  In this section, we give a quick overview of the available proof methods 
  and options. The most versatile proof method that we provide is
  \<open>sep_auto\<close>. It tries to solve the first subgoal, invoking appropriate
  proof methods as required. If it cannot solve the subgoal completely, it
  stops at the intermediate state that it could not handle any more. 

  \<open>sep_auto\<close> can be configured by 
  section-arguments for the simplifier, the classical reasoner, and all
  section-arguments for the verification condition generator and 
  entailment solver. Moreover, it takes an optional mode argument (mode), where
  valid modes are:
  \begin{description}
    \item[(nopre)] No preprocessing of goal. The preprocessor tries to clarify
      and simplify the goal before the main method is invoked.
    \item[(nopost)] No postprocessing of goal. The postprocessor tries to 
      solve or simplify goals left over by verification condition generation or
      entailment solving.
    \item[(plain)] Neither pre- nor postprocessing. Just applies vcg and 
      entailment solver.  
  \end{description}

  \paragraph{Entailment Solver.} The entailment solver processes goals of the
  form \<open>P \<Longrightarrow>\<^sub>A Q\<close>. It is invoked by the method \<open>solve_entails\<close>.
  It first tries to pull out pure parts of
  \<open>P\<close> and \<open>Q\<close>. This may introduce quantifiers, conjunction,
  and implication into the goal, that are eliminated by resolving with rules
  declared as \<open>sep_eintros\<close> (method argument: eintros[add/del]:).
  Moreover, it simplifies with rules declared as \<open>sep_dflt_simps\<close> 
  (section argument: \<open>dflt_simps[add/del]:\<close>).

  Now, \<open>P\<close> and \<open>Q\<close> should have the form \<open>X\<^sub>1*\<dots>*X\<^sub>n\<close>.
  Then, the frame-matcher is used to match all items of \<open>P\<close> with items
  of \<open>Q\<close>, and thus solve the implication. Matching is currently done 
  syntactically, but can instantiate schematic variables.

  Note that, by default, existential introduction is declared as 
  \<open>sep_eintros\<close>-rule. This introduces schematic variables, that can
  later be matched against. However, in some cases, the matching may instantiate
  the schematic variables in an undesired way. In this case, the argument 
  \<open>eintros del: exI\<close> should be passed to the entailment solver, and
  the existential quantifier should be instantiated manually.

  \paragraph{Frame Inference}
  The method \<open>frame_inference\<close> tries to solve a goal of the 
  form \<open>P\<Longrightarrow>Q*?F\<close>, by matching \<open>Q\<close> against the parts of 
  \<open>P\<close>, and instantiating \<open>?F\<close> accordingly. 
  Matching is done syntactically, possibly 
  instantiating schematic variables. \<open>P\<close> and \<open>Q\<close> should be 
  assertions separated by \<open>*\<close>. Note that frame inference does no 
  simplification or other kinds of normalization.

  The method \<open>heap_rule\<close> applies the specified heap rules, using
  frame inference if necessary. If no rules are specified, the default 
  heap rules are used.

  \paragraph{Verification Condition Generator}
  The verification condition generator processes goals of the form 
  \<open><P>c<Q>\<close>. It is invoked by the method \<open>vcg\<close>.
  First, it tries to pull out pure parts and simplifies with
  the default simplification rules. Then, it tries to resolve the goal with
  deconstruct rules (attribute: \<open>sep_decon_rules\<close>, 
  section argument: \<open>decon[add/del]:\<close>), and if this does not succeed, 
  it tries
  to resolve the goal with heap rules (attribute: \<open>sep_heap_rules\<close>, 
  section argument: \<open>heap[add/del]:\<close>), using the frame rule and 
  frame inference.
  If resolving is not possible, it also tries to apply the consequence rule to
  make the postcondition a schematic variable.
\<close>


(*<*)
subsection \<open>Hiding of internal stuff\<close>
hide_const (open) FI_COMP
(*>*)

end
