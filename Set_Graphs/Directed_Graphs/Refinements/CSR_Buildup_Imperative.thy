theory CSR_Buildup_Imperative
  imports Directed_Set_Graphs.CSR_Buildup Separation_Logic_Imperative_HOL_Partial.Sep_Main
begin

provenance ai


section \<open>Imperative CSR Buildup\<close>

text \<open>
  The functional counting sort of @{locale csr_buildup} is refined to Imperative HOL,
  following the imperative DFS: one locale combines the functional locale with the imperative
  operations and their Hoare triples, the loops are heap @{command partial_function}s,
  and each loop is shown to compute the functional loop by fixpoint induction.

  For efficiency,
  \<^item> the boundaries \<open>B\<close> and edges \<open>E\<close> are arrays updated in place, and
    no memory beyond them is allocated (in particular, no cursor array),
  \<^item> the prefix sums carry the running sum in a register, so each entry of \<open>B\<close> is read once,
  \<^item> the iterator is split into \<open>has_next\<close>, \<open>cur\<close> and \<open>adv\<close>,
    so no option or pair is built per edge. The iterator state is a plain value
    (e.g.\ a counter), so restarting the iterator for the second pass is free.
    The iterator operations additionally take the handle \<open>c\<close> of the input container (e.g.\ the
    input arrays). No imperative value is fixed by a locale: the container is an argument of the
    programs, and the refinement assertion @{term input_assn} relates it to the input in the
    Hoare triples, which the operations preserve.
  \<^item> \<open>E\<close> does not store the elements themselves but their values under a function \<open>val\<close>, so an
    element can be a position in the input, from which the key and the stored value are read.
    The key and the value operations therefore also take the input container.
\<close>

text \<open>The code locale fixes only the size and the imperative iterator, key and value operations;
      it has no assumptions, so that the programs can be globally interpreted and exported.\<close>

locale imp_csr_buildup_code =
  fixes n :: nat
    and it_has_next_impl :: "'ci \<Rightarrow> 'si \<Rightarrow> bool Heap"
    and it_cur_impl :: "'ci \<Rightarrow> 'si \<Rightarrow> 'e Heap"
    and it_adv_impl :: "'ci \<Rightarrow> 'si \<Rightarrow> 'si Heap"
    and key_impl :: "'ci \<Rightarrow> 'e \<Rightarrow> nat Heap"
    and val_impl :: "'ci \<Rightarrow> 'e \<Rightarrow> 'x::heap Heap"
begin

subsection \<open>Programs\<close>

text \<open>Count pass, refining @{term "it_fold count_step"}.\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) count_imp ::
  "'ci \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> 'si \<Rightarrow> nat Heap" where
  "count_imp c B m si = do {
     b \<leftarrow> it_has_next_impl c si;
     if b then do {
       e \<leftarrow> it_cur_impl c si;
       k \<leftarrow> key_impl c e;
       (if k + 2 \<le> n then do {
          d \<leftarrow> Array.nth B (k + 2);
          Array.upd (k + 2) (Suc d) B;
          return () }
        else return ());
       si' \<leftarrow> it_adv_impl c si;
       count_imp c B (Suc m) si' }
     else return m }"

text \<open>Prefix sums, refining @{term "fold prefix_step [j..<Suc n]"}; \<open>acc\<close> holds
      \<open>B!(j-1)\<close>.\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) prefix_imp :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "prefix_imp B j acc =
     (if j \<le> n then do {
        c \<leftarrow> Array.nth B j;
        let acc' = c + acc;
        Array.upd j acc' B;
        prefix_imp B (Suc j) acc' }
      else return ())"

text \<open>Fill pass, refining @{term "it_fold fill_step"}; the value of the element is stored.\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) fill_imp ::
  "'ci \<Rightarrow> nat array \<Rightarrow> 'x array \<Rightarrow> 'si \<Rightarrow> unit Heap" where
  "fill_imp c B E si = do {
     b \<leftarrow> it_has_next_impl c si;
     if b then do {
       e \<leftarrow> it_cur_impl c si;
       k \<leftarrow> key_impl c e;
       x \<leftarrow> val_impl c e;
       p \<leftarrow> Array.nth B (k + 1);
       Array.upd (k + 1) (Suc p) B;
       Array.upd p x E;
       si' \<leftarrow> it_adv_impl c si;
       fill_imp c B E si' }
     else return () }"

text \<open>Allocation of the edge array, refining @{const csr_buildup.init_E}.\<close>

definition \<^marker>\<open>provenance ai_human\<close> init_E_imp :: "'ci \<Rightarrow> 'si \<Rightarrow> nat \<Rightarrow> 'x array Heap" where
  "init_E_imp c si m = do {
     b \<leftarrow> it_has_next_impl c si;
     if b then do { e \<leftarrow> it_cur_impl c si; x \<leftarrow> val_impl c e; Array.new m x }
     else Array.of_list [] }"

definition \<^marker>\<open>provenance ai_human\<close> csr_build_imp :: "'ci \<Rightarrow> 'si \<Rightarrow> (nat array \<times> 'x array) Heap" where
  "csr_build_imp c si = do {
     B \<leftarrow> Array.new (Suc n) 0;
     m \<leftarrow> count_imp c B 0 si;
     prefix_imp B 1 0;
     E \<leftarrow> init_E_imp c si m;
     fill_imp c B E si;
     return (B, E) }"

text \<open>The build into arrays allocated by the caller: \<open>B\<close> is zero, \<open>E\<close> has one cell
      per element. This lets an algorithm allocate all its arrays once at the start.\<close>

definition \<^marker>\<open>provenance ai_human\<close> csr_build_into ::
  "'ci \<Rightarrow> 'si \<Rightarrow> nat array \<Rightarrow> 'x array \<Rightarrow> unit Heap" where
  "csr_build_into c si B E = do {
     count_imp c B 0 si;
     prefix_imp B 1 0;
     fill_imp c B E si }"

end

text \<open>The proof locale: the functional counting sort, the value function, the iterator relation
      and the context assertion, with one Hoare triple per imperative operation.\<close>

locale imp_csr_buildup = csr_buildup it_next it_seq it_invar key n s0 +
  imp_csr_buildup_code n it_has_next_impl it_cur_impl it_adv_impl key_impl val_impl
  for it_next :: "'s \<Rightarrow> ('e \<times> 's) option"
    and it_seq :: "'s \<Rightarrow> 'e list"
    and it_invar :: "'s \<Rightarrow> bool"
    and key :: "'e \<Rightarrow> nat"
    and n :: nat
    and s0 :: 's
    and it_has_next_impl :: "'ci \<Rightarrow> 'si \<Rightarrow> bool Heap"
    and it_cur_impl :: "'ci \<Rightarrow> 'si \<Rightarrow> 'e Heap"
    and it_adv_impl :: "'ci \<Rightarrow> 'si \<Rightarrow> 'si Heap"
    and key_impl :: "'ci \<Rightarrow> 'e \<Rightarrow> nat Heap"
    and val_impl :: "'ci \<Rightarrow> 'e \<Rightarrow> 'x::heap Heap" +
  fixes val :: "'e \<Rightarrow> 'x"
    and it_rel :: "'s \<Rightarrow> 'si \<Rightarrow> bool"
    and input_assn :: "'ci \<Rightarrow> assn"
  assumes has_next_rule:
    "\<lbrakk>it_invar s; it_rel s si\<rbrakk> \<Longrightarrow>
       <input_assn c> it_has_next_impl c si <\<lambda>b. input_assn c * \<up>(b \<longleftrightarrow> it_next s \<noteq> None)>"
    and cur_rule:
    "\<lbrakk>it_invar s; it_rel s si; it_next s = Some (e, s')\<rbrakk> \<Longrightarrow>
       <input_assn c> it_cur_impl c si <\<lambda>r. input_assn c * \<up>(r = e)>"
    and adv_rule:
    "\<lbrakk>it_invar s; it_rel s si; it_next s = Some (e, s')\<rbrakk> \<Longrightarrow>
       <input_assn c> it_adv_impl c si <\<lambda>si'. input_assn c * \<up>(it_rel s' si')>"
    and key_rule:
    "e \<in> set (it_seq s0) \<Longrightarrow> <input_assn c> key_impl c e <\<lambda>k. input_assn c * \<up>(k = key e)>"
    and val_rule:
    "e \<in> set (it_seq s0) \<Longrightarrow> <input_assn c> val_impl c e <\<lambda>x. input_assn c * \<up>(x = val e)>"
begin

subsection \<open>Correctness\<close>

lemma \<^marker>\<open>provenance ai_human\<close> count_imp_rule:
  "<input_assn c * B \<mapsto>\<^sub>a Bs * \<up>(it_invar s \<and> it_rel s si \<and> set (it_seq s) \<subseteq> set es \<and> length Bs = Suc n)>
     count_imp c B m si
   <\<lambda>r. input_assn c * B \<mapsto>\<^sub>a fst (it_fold count_step s (Bs, m))
         * \<up>(r = snd (it_fold count_step s (Bs, m)))>"
proof(induction arbitrary: s si Bs m rule: count_imp.fixp_induct)
  case (3 f)
  show ?case
  proof(cases "it_invar s \<and> it_rel s si \<and> set (it_seq s) \<subseteq> set es \<and> length Bs = Suc n")
    case True
    show ?thesis
    proof(cases "it_next s")
      case (Some a)
      then obtain e s' where "it_next s = Some (e, s')" "e \<in> set (it_seq s0)"
        "it_invar s'" "set (it_seq s') \<subseteq> set es"
        using True it_next_Some[of s]
        by (cases a) (auto simp: es_def)
      thus ?thesis
        using True
        by (sep_auto heap: has_next_rule[of s si] cur_rule[of s si e s'] adv_rule[of s si e s'] key_rule[of e]
            3[where s1=s'] simp: it_fold_Some count_step_def Let_def)
    qed (use True in \<open>sep_auto heap: has_next_rule[of s si] simp: it_fold_None\<close>)
  qed (intro ht_extract_pre_pure(1), simp)
qed simp_all

lemma \<^marker>\<open>provenance ai_human\<close> prefix_imp_rule:
  "<B \<mapsto>\<^sub>a Bs * \<up>(length Bs = Suc n \<and> 0 < j \<and> acc = Bs ! (j - 1))>
     prefix_imp B j acc
   <\<lambda>_. B \<mapsto>\<^sub>a fold prefix_step [j..<Suc n] Bs>"
proof(induction arbitrary: Bs j acc rule: prefix_imp.fixp_induct)
  case (3 f)
  show ?case
  proof(cases "length Bs = Suc n \<and> 0 < j \<and> acc = Bs ! (j - 1)")
    case True
    have "j \<le> n \<Longrightarrow> fold prefix_step [j..<Suc n] Bs
        = fold prefix_step [Suc j..<Suc n] (list_update Bs j (Bs ! j + acc))"
      using True
      by (subst upt_conv_Cons[of j "Suc n"]) (simp_all add: prefix_step_def del: upt_Suc)
    thus ?thesis
      using True
      by (sep_auto heap: 3[where j1="Suc j"])
  qed (intro ht_extract_pre_pure(1), simp)
qed simp_all

lemma \<^marker>\<open>provenance ai_human\<close> prefix_sums_imp_rule:
  "<B \<mapsto>\<^sub>a Bs * \<up>(length Bs = Suc n \<and> Bs ! 0 = 0)> prefix_imp B 1 0 <\<lambda>_. B \<mapsto>\<^sub>a prefix_sums Bs>"
  using prefix_imp_rule[where j=1 and acc=0]
  by (simp add: prefix_sums_def)

lemma \<^marker>\<open>provenance ai_human\<close> fill_imp_rule:
  "<input_assn c * B \<mapsto>\<^sub>a Bs * E \<mapsto>\<^sub>a map val Es
      * \<up>(it_invar s \<and> it_rel s si \<and> xs @ it_seq s = es \<and> fill_invar xs (Bs, Es))>
     fill_imp c B E si
   <\<lambda>_. input_assn c * B \<mapsto>\<^sub>a fst (it_fold fill_step s (Bs, Es))
         * E \<mapsto>\<^sub>a map val (snd (it_fold fill_step s (Bs, Es)))>"
proof(induction arbitrary: s si xs Bs Es rule: fill_imp.fixp_induct)
  case (3 f)
  show ?case
  proof(cases "it_invar s \<and> it_rel s si \<and> xs @ it_seq s = es \<and> fill_invar xs (Bs, Es)")
    case True
    show ?thesis
    proof(cases "it_next s")
      case (Some a)
      then obtain e s' where "it_next s = Some (e, s')" "xs @ e # it_seq s' = es" "it_invar s'"
        using True it_next_Some[of s]
        by (cases a) auto
      moreover have "e \<in> set (it_seq s0)"
        unfolding es_def[symmetric] calculation(2)[symmetric]
        by simp
      ultimately show ?thesis
        using True fill_step_bounds[of xs e "it_seq s'" Bs Es] fill_step_invar[of xs e "it_seq s'" Bs Es]
        by (sep_auto heap: has_next_rule[of s si] cur_rule[of s si e s'] adv_rule[of s si e s'] key_rule[of e]
            val_rule[of e] 3[where s1=s' and xs1="xs @ [e]" and Bs1="fst (fill_step e (Bs, Es))"
              and Es1="snd (fill_step e (Bs, Es))",
              unfolded fill_step_def Let_def case_prod_conv fst_conv snd_conv map_update]
            simp: it_fold_Some fill_step_def Let_def)
    qed (use True in \<open>sep_auto heap: has_next_rule[of s si] simp: it_fold_None\<close>)
  qed (intro ht_extract_pre_pure(1), simp)
qed simp_all

lemma \<^marker>\<open>provenance ai_human\<close> init_E_imp_rule:
  "<input_assn c * \<up>(it_rel s0 si)> init_E_imp c si m <\<lambda>E. input_assn c * E \<mapsto>\<^sub>a map val (init_E m)>"
proof(cases "it_next s0")
  case (Some a)
  then obtain e s' where "it_next s0 = Some (e, s')"
    by (cases a) auto
  thus ?thesis
    using s0_invar it_next_Some[of s0 e s']
    unfolding init_E_imp_def init_E_def
    by (sep_auto heap: has_next_rule[of s0] cur_rule[of s0 _ e s'] val_rule)
qed (sep_auto simp: init_E_imp_def init_E_def s0_invar heap: has_next_rule[of s0])

lemma \<^marker>\<open>provenance ai_human\<close> csr_build_imp_rule:
  "<input_assn c * \<up>(it_rel s0 si)> csr_build_imp c si
   <\<lambda>(B, E). input_assn c * B \<mapsto>\<^sub>a B_spec * E \<mapsto>\<^sub>a map val E_spec>"
  unfolding csr_build_imp_def
  using count_edges csr_build_correct
  by (sep_auto heap: count_imp_rule[where s=s0] prefix_sums_imp_rule init_E_imp_rule
      fill_imp_rule[where s=s0 and xs="[]"]
      simp: count_edges_def csr_build_def count_B_nth s0_invar es_def[symmetric] fill_invar_init)

lemma \<^marker>\<open>provenance ai_human\<close> csr_build_into_rule:
  "<input_assn c * B \<mapsto>\<^sub>a replicate (Suc n) 0 * E \<mapsto>\<^sub>a map val Es
      * \<up>(it_rel s0 si \<and> length Es = length es)>
     csr_build_into c si B E
   <\<lambda>_. input_assn c * B \<mapsto>\<^sub>a B_spec * E \<mapsto>\<^sub>a map val E_spec>"
proof-
  have "fill_invar [] (prefix_sums (count_B es), Es)" if "length Es = length es"
    using that
    by (simp add: fill_invar_def prefix_sums_count_B del: upt_Suc)
  thus ?thesis
    unfolding csr_build_into_def
    using count_edges fill_correct[of Es]
    by (sep_auto heap: count_imp_rule[where s=s0] prefix_sums_imp_rule
        fill_imp_rule[where s=s0 and xs="[]"]
        simp: count_edges_def count_B_nth s0_invar es_def[symmetric] it_fold_s0)
qed

end

end


