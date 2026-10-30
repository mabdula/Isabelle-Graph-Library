theory CSR_Graph_Reset_To
  imports
    CSR_Graph
    Data_Structures.Imp_Range_Iteration
begin

provenance ai


section \<open>CSR Iterators with Jumping to an Element\<close>

text \<open>The CSR collection of @{locale csr_graph} extended by a position array \<open>P\<close>, built once:
      for every entry \<open>E ! i\<close> of the element array, \<open>P\<close> holds \<open>i\<close> at the key
      of that entry, e.g. at the identifier of an edge. Setting the iterator of \<open>v\<close> to an
      element \<open>e\<close> of its block then sets the cursor of \<open>v\<close> to the position of
      \<open>e\<close>: one array read and one array write.\<close>

locale csr_graph_reset_to = csr_graph_imp n K B E
  for n K B and E :: "'e::heap list" +
  fixes key :: "'e \<Rightarrow> nat"
    and P :: "nat list"
  assumes P_pos: "\<And> i. i < length E \<Longrightarrow> key (E ! i) < length P \<and> P ! key (E ! i) = i"
begin

definition "csr_reset_to c v e = fun_upd c v (P ! key e)"

lemma seg_pos:
  assumes "v \<in> K" "e \<in> csr_abstract c v"
  shows "B ! v \<le> P ! key e \<and> P ! key e < B ! Suc v \<and> E ! (P ! key e) = e \<and> key e < length P"
  using assms P_pos B_bound[OF K_less[OF assms(1)]]
  by (auto simp: csr_abstract_def seg_def)

sublocale csr_rt: indexed_iterable_set_reset_to csr_invar csr_abstract csr_current csr_has
    csr_iterated csr_remaining csr_move csr_reset K csr_reset_to
proof(unfold_locales, goal_cases)
  case (1 C i x)
  thus ?case
    by (auto dest: seg_pos simp: csr_invar_def csr_reset_to_def)
next
  case (3 C C' i x)
  thus ?case
    using P_pos[of "C' i"] B_bound[of i] K_less[of i]
    by (auto simp: csr_reset_to_def csr_iterated_def csr_remaining_def csr_has_def csr_current_def)
qed (simp_all add: csr_abstract_def csr_reset_to_def csr_iterated_def csr_remaining_def)

end

text \<open>The imperative collection: the CSR arrays together with the position array. The programs
      are global.\<close>

type_synonym 'e csr_rt_imp = "nat array \<times> 'e array \<times> nat array \<times> nat array"

definition csr_rt_has_imp :: "'e::heap csr_rt_imp \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "csr_rt_has_imp = (\<lambda> (Ba, Ea, Ca, Pa) v. csr_has_imp (Ba, Ea, Ca) v)"

definition csr_rt_current_imp :: "'e::heap csr_rt_imp \<Rightarrow> nat \<Rightarrow> 'e Heap" where
  "csr_rt_current_imp = (\<lambda> (Ba, Ea, Ca, Pa) v. csr_current_imp (Ba, Ea, Ca) v)"

definition csr_rt_move_imp :: "'e::heap csr_rt_imp \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "csr_rt_move_imp = (\<lambda> (Ba, Ea, Ca, Pa) v. csr_move_imp (Ba, Ea, Ca) v)"

definition csr_rt_reset_imp :: "'e::heap csr_rt_imp \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "csr_rt_reset_imp = (\<lambda> (Ba, Ea, Ca, Pa) v. csr_reset_imp (Ba, Ea, Ca) v)"

definition csr_reset_to_imp ::
  "('e \<Rightarrow> nat) \<Rightarrow> 'e::heap csr_rt_imp \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> unit Heap" where
  "csr_reset_to_imp key = (\<lambda> (Ba, Ea, Ca, Pa) v e. do {
     p \<leftarrow> Array.nth Pa (key e);
     _ \<leftarrow> Array.upd v p Ca;
     return () })"

context csr_graph_reset_to
begin

definition csr_rt_assn :: "(nat \<Rightarrow> nat) \<Rightarrow> 'e csr_rt_imp \<Rightarrow> assn" where
  "csr_rt_assn c = (\<lambda> (Ba, Ea, Ca, Pa). csr_assn c (Ba, Ea, Ca) * Pa \<mapsto>\<^sub>a P)"

lemma csr_reset_to_imp_rule:
  assumes "csr_invar c" "v \<in> K" "e \<in> csr_abstract c v"
  shows "<csr_rt_assn c Ci> csr_reset_to_imp key Ci v e <\<lambda>_. csr_rt_assn (csr_reset_to c v e) Ci>"
  using assms(2,3) seg_pos[of v e c] K_less[of v]
  by (cases Ci rule: prod_cases4)
    (sep_auto simp: csr_rt_assn_def csr_assn_def csr_reset_to_imp_def csr_reset_to_def nth_list_update)

sublocale csr_rt_imp: indexed_iterable_set_reset_to_imp csr_invar csr_abstract csr_current csr_has
    csr_iterated csr_remaining csr_move csr_reset K csr_rt_assn csr_rt_current_imp csr_rt_has_imp
    csr_rt_move_imp csr_rt_reset_imp csr_reset_to "csr_reset_to_imp key"
proof(unfold_locales, goal_cases)
  case (1 C i Ci)
  show ?case
    by (cases Ci rule: prod_cases4)
      (sep_auto heap: csr_current_imp_rule[OF 1(2,1,3)] simp: csr_rt_assn_def csr_rt_current_imp_def)
next
  case (2 C i Ci)
  thus ?case
    by (cases Ci rule: prod_cases4) (sep_auto heap: csr_has_imp_rule simp: csr_rt_assn_def csr_rt_has_imp_def)
next
  case (3 C i Ci)
  show ?case
    by (cases Ci rule: prod_cases4)
      (sep_auto heap: csr_move_imp_rule[OF 3(2,3)] simp: csr_rt_assn_def csr_rt_move_imp_def)
next
  case (4 C i Ci)
  thus ?case
    by (cases Ci rule: prod_cases4) (sep_auto heap: csr_reset_imp_rule simp: csr_rt_assn_def csr_rt_reset_imp_def)
qed (rule csr_reset_to_imp_rule)

end

section \<open>Folding over All Elements\<close>

text \<open>A fold over the whole element array, independent of the cursors.\<close>

definition csr_rt_edges_fold_imp ::
  "'e::heap csr_rt_imp \<Rightarrow> ('e \<Rightarrow> unit Heap) \<Rightarrow> unit Heap" where
  "csr_rt_edges_fold_imp = (\<lambda> (Ba, Ea, Ca, Pa) g. do {
     m \<leftarrow> Array.len Ea;
     foldl_range_imp (\<lambda> i _. do { e \<leftarrow> Array.nth Ea i; g e }) 0 m () })"

context csr_graph_reset_to
begin

lemma csr_rt_edges_fold_imp_rule:
  assumes "I acc"
      and g: "\<And> acc e. \<lbrakk>I acc; e \<in> set E\<rbrakk> \<Longrightarrow>
                I (g acc e) \<and> <R acc> g_imp e <\<lambda>_. R (g acc e)>"
  shows "<csr_rt_assn c Ci * R acc> csr_rt_edges_fold_imp Ci g_imp
         <\<lambda>_. csr_rt_assn c Ci * R (foldl g acc E)>"
proof(cases Ci rule: prod_cases4)
  case (fields Ba Ea Ca Pa)
  define F where
    "F = Ba \<mapsto>\<^sub>a B * Pa \<mapsto>\<^sub>a P * (\<exists>\<^sub>A l. Ca \<mapsto>\<^sub>a l * \<up>(length l = n \<and> (\<forall> v \<in> K. l ! v = c v)))"
  let ?A = "\<lambda> a (_::unit). R a * \<up>(I a)"
  have "<?A a u * (Ea \<mapsto>\<^sub>a E * F)> do { e \<leftarrow> Array.nth Ea j; g_imp e }
        <\<lambda> r. ?A (g a (E ! j)) r * (Ea \<mapsto>\<^sub>a E * F)>"
    if "0 \<le> j" "j < length E" for j a and u :: unit
    using that(2)
    by (sep_auto heap: g[of a "E ! j", THEN conjunct2] simp: g[of a "E ! j", THEN conjunct1])
  hence run: "<?A acc () * (Ea \<mapsto>\<^sub>a E * F)>
                foldl_range_imp (\<lambda> i _. do { e \<leftarrow> Array.nth Ea i; g_imp e }) 0 (length E) ()
              <\<lambda> r. ?A (foldl (\<lambda> a j. g a (E ! j)) acc [0..<length E]) r *
                    (Ea \<mapsto>\<^sub>a E * F)>"
    by (intro foldl_range_imp_rule) simp_all
  show ?thesis
    using assms(1)
    unfolding fields csr_rt_edges_fold_imp_def prod.case csr_rt_assn_def csr_assn_def F_def
    by (sep_auto heap: run[unfolded F_def] simp: foldl_upt_nth)
qed

end

section \<open>Building the Position Array\<close>

text \<open>One pass over the element array writes the position of every element at its key into a
      preallocated array.\<close>

definition "csr_pos_list key E P0 = foldl (\<lambda> P i. list_update P (key (E ! i)) i) P0 [0..<length E]"

lemma csr_pos_list_props:
  assumes "distinct (map key E)" "\<forall> e \<in> set E. key e < length P0"
  shows "length (csr_pos_list key E P0) = length P0"
        "\<And> i. i < length E \<Longrightarrow> key (E ! i) < length (csr_pos_list key E P0) \<and>
                               csr_pos_list key E P0 ! key (E ! i) = i"
  using foldl_upd_nth_hit[where g = "\<lambda> i. key (E ! i)" and f = "\<lambda> i. i", of "[0..<length E]" _ P0]
    nth_eq_iff_index_eq[OF assms(1)] assms(2)
  by (simp_all add: csr_pos_list_def inj_on_def)

lemma csr_graph_reset_to_pos_list:
  assumes "csr_graph n K B E" "distinct (map key E)" "\<forall> e \<in> set E. key e < length P0"
  shows "csr_graph_reset_to n K B E key (csr_pos_list key E P0)"
  by (intro csr_graph_reset_to.intro csr_graph_reset_to_axioms.intro csr_graph_imp.intro)
    (simp_all add: assms csr_pos_list_props)

definition csr_pos_build_imp ::
  "('e \<Rightarrow> nat) \<Rightarrow> 'e::heap array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "csr_pos_build_imp key Ea Pa m =
     foldl_range_imp (\<lambda> i _. do { e \<leftarrow> Array.nth Ea i; Array.upd (key e) i Pa; return () }) 0 m ()"

lemma csr_pos_build_imp_rule:
  assumes "\<forall> e \<in> set E. key e < length P0"
  shows "<Ea \<mapsto>\<^sub>a E * Pa \<mapsto>\<^sub>a P0> csr_pos_build_imp key Ea Pa (length E)
         <\<lambda>_. Ea \<mapsto>\<^sub>a E * Pa \<mapsto>\<^sub>a csr_pos_list key E P0>"
proof-
  let ?A = "\<lambda> P (_::unit). Pa \<mapsto>\<^sub>a P * \<up>(length P = length P0)"
  have "<?A P0 () * Ea \<mapsto>\<^sub>a E> csr_pos_build_imp key Ea Pa (length E)
        <\<lambda> r. ?A (foldl (\<lambda> P j. list_update P (key (E ! j)) j) P0 [0..<length E]) r * Ea \<mapsto>\<^sub>a E>"
    unfolding csr_pos_build_imp_def
    using assms
    by (intro foldl_range_imp_rule) sep_auto
  thus ?thesis
    by (rule ht_cons_prec[rotated 2]) (sep_auto simp: csr_pos_list_def)+
qed

end
