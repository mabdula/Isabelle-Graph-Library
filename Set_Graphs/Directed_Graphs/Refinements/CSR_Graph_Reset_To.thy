theory CSR_Graph_Reset_To
  imports
    CSR_Graph
    Data_Structures.Iterable_Set_Reset_To_Specs_Imp
    Data_Structures.Imp_Range_Iteration
begin

section \<open>CSR Iterators with Jumping to an Element\<close>

text \<open>The CSR collection of @{locale csr_graph} extended by a position array \<open>P\<close>, built once:
      for every entry \<open>E ! i\<close> of the element array, \<open>P\<close> holds \<open>i\<close> at the key of that entry, e.g.
      at the identifier of an edge. Setting the iterator of \<open>v\<close> to an element \<open>e\<close> of its block
      then sets the cursor of \<open>v\<close> to the position of \<open>e\<close>: one array read and one array write.\<close>

locale csr_graph_reset_to = csr_graph_imp n K B E
  for n K B and E :: "'e::heap list" +
  fixes key :: "'e \<Rightarrow> nat"
    and P :: "nat list"
  assumes P_pos: "\<And> i. i < length E \<Longrightarrow> key (E ! i) < length P \<and> P ! key (E ! i) = i"
begin

definition "csr_reset_to c v e = fun_upd c v (P ! key e)"

lemma seg_pos:
  assumes "e \<in> seg a b" "b \<le> length E"
  shows "a \<le> P ! key e" "P ! key e < b" "E ! (P ! key e) = e"
proof-
  obtain j where j: "a \<le> j" "j < b" "e = E ! j"
    using assms(1) by (auto simp add: seg_def)
  have "P ! key e = j"
    using P_pos[of j] j assms(2) by simp
  thus "a \<le> P ! key e" "P ! key e < b" "E ! (P ! key e) = e"
    using j by simp_all
qed

sublocale csr_rt: indexed_iterable_set_reset_to csr_invar csr_abstract csr_current csr_has
    csr_iterated csr_remaining csr_move csr_reset K csr_reset_to
proof(intro indexed_iterable_set_reset_to.intro[OF csr.indexed_iterable_set_axioms]
        indexed_iterable_set_reset_to_axioms.intro, goal_cases)
  case (1 C i x)
  have "B ! i \<le> P ! key x" "P ! key x < B ! Suc i"
    using seg_pos(1,2)[OF 1(3)[unfolded csr_abstract_def] B_bound[OF K_less[OF 1(2)]]] by simp_all
  thus ?case
    using 1(1) by (auto simp add: csr_invar_def csr_reset_to_def)
next
  case (2 C i x j)
  show ?case
    by (simp add: csr_abstract_def)
next
  case (3 C C' i x)
  have b: "B ! Suc i \<le> length E"
    using B_bound[OF K_less[OF 3(2)]] .
  have "C' i < length E" "E ! C' i = x"
    using 3(5,6) b by (simp_all add: csr_has_def csr_current_def)
  hence "P ! key x = C' i"
    using P_pos[of "C' i"] by simp
  thus ?case
    using 3(5) by (simp add: csr_reset_to_def csr_iterated_def csr_remaining_def csr_has_def
                             csr_current_def \<open>E ! C' i = x\<close>)
next
  case (4 C i x j)
  thus ?case
    by (simp add: csr_reset_to_def csr_iterated_def)
next
  case (5 C i x j)
  thus ?case
    by (simp add: csr_reset_to_def csr_remaining_def)
qed

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

definition csr_reset_to_imp :: "('e \<Rightarrow> nat) \<Rightarrow> 'e::heap csr_rt_imp \<Rightarrow> nat \<Rightarrow> 'e \<Rightarrow> unit Heap" where
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
proof-
  obtain Ba Ea Ca Pa where Ci: "Ci = (Ba, Ea, Ca, Pa)"
    by (cases Ci) auto
  have "key e < length P"
  proof-
    obtain j where j: "B ! v \<le> j" "j < B ! Suc v" "e = E ! j"
      using assms(3) by (auto simp add: csr_abstract_def seg_def)
    have "j < length E"
      using j(2) B_bound[OF K_less[OF assms(2)]] by simp
    thus ?thesis
      using P_pos[of j] j(3) by simp
  qed
  thus ?thesis
    unfolding Ci csr_rt_assn_def csr_assn_def csr_reset_to_imp_def csr_reset_to_def
    using K_less[OF assms(2)] assms(2)
    by (sep_auto simp: nth_list_update)
qed

sublocale csr_rt_imp: indexed_iterable_set_reset_to_imp csr_invar csr_abstract csr_current csr_has
    csr_iterated csr_remaining csr_move csr_reset K csr_rt_assn csr_rt_current_imp csr_rt_has_imp
    csr_rt_move_imp csr_rt_reset_imp csr_reset_to "csr_reset_to_imp key"
proof(intro indexed_iterable_set_reset_to_imp.intro indexed_iterable_set_reset_to_imp_axioms.intro
        indexed_iterable_set_imp.intro indexed_iterable_set_imp_axioms.intro
        csr.indexed_iterable_set_axioms csr_rt.indexed_iterable_set_reset_to_axioms, goal_cases)
  case (1 C i Ci)
  obtain Ba Ea Ca Pa where Ci: "Ci = (Ba, Ea, Ca, Pa)"
    by (cases Ci) auto
  show ?case
    unfolding Ci csr_rt_assn_def csr_rt_current_imp_def prod.case
    by (rule ht_cons_post[OF ht_frame[OF csr_current_imp_rule[OF 1(2,1,3)]]]) sep_auto
next
  case (2 C i Ci)
  obtain Ba Ea Ca Pa where Ci: "Ci = (Ba, Ea, Ca, Pa)"
    by (cases Ci) auto
  show ?case
    unfolding Ci csr_rt_assn_def csr_rt_has_imp_def prod.case
    by (rule ht_cons_post[OF ht_frame[OF csr_has_imp_rule[OF 2(2)]]]) sep_auto
next
  case (3 C i Ci)
  obtain Ba Ea Ca Pa where Ci: "Ci = (Ba, Ea, Ca, Pa)"
    by (cases Ci) auto
  show ?case
    unfolding Ci csr_rt_assn_def csr_rt_move_imp_def prod.case
    by (rule ht_cons_post[OF ht_frame[OF csr_move_imp_rule[OF 3(2,3)]]]) sep_auto
next
  case (4 C i Ci)
  obtain Ba Ea Ca Pa where Ci: "Ci = (Ba, Ea, Ca, Pa)"
    by (cases Ci) auto
  show ?case
    unfolding Ci csr_rt_assn_def csr_rt_reset_imp_def prod.case
    by (rule ht_cons_post[OF ht_frame[OF csr_reset_imp_rule[OF 4(2)]]]) sep_auto
next
  case (5 C i x Ci)
  thus ?case
    by (rule csr_reset_to_imp_rule)
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
proof-
  have inj: "inj_on (\<lambda> i. key (E ! i)) (set [0..<length E])"
    unfolding inj_on_def using nth_eq_iff_index_eq[OF assms(1)] by simp
  show "length (csr_pos_list key E P0) = length P0"
    by (simp add: csr_pos_list_def)
  show "key (E ! i) < length (csr_pos_list key E P0) \<and> csr_pos_list key E P0 ! key (E ! i) = i"
    if "i < length E" for i
    using foldl_upd_nth_hit[where g = "\<lambda> i. key (E ! i)" and f = "\<lambda> i. i", OF inj, of i P0]
          that assms(2)
    by (simp add: csr_pos_list_def)
qed

lemma csr_graph_reset_to_pos_list:
  assumes "csr_graph n K B E" "distinct (map key E)" "\<forall> e \<in> set E. key e < length P0"
  shows "csr_graph_reset_to n K B E key (csr_pos_list key E P0)"
  using csr_graph_imp.intro[OF assms(1)] csr_pos_list_props(2)[OF assms(2,3)]
  by (intro csr_graph_reset_to.intro csr_graph_reset_to_axioms.intro) simp_all

definition csr_pos_build_imp :: "('e \<Rightarrow> nat) \<Rightarrow> 'e::heap array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "csr_pos_build_imp key Ea Pa m =
     foldl_range_imp (\<lambda> i _. do { e \<leftarrow> Array.nth Ea i; Array.upd (key e) i Pa; return () }) 0 m ()"

lemma csr_pos_build_imp_rule:
  assumes "\<forall> e \<in> set E. key e < length P0"
  shows "<Ea \<mapsto>\<^sub>a E * Pa \<mapsto>\<^sub>a P0> csr_pos_build_imp key Ea Pa (length E)
         <\<lambda>_. Ea \<mapsto>\<^sub>a E * Pa \<mapsto>\<^sub>a csr_pos_list key E P0>"
proof-
  let ?A = "\<lambda> P (_::unit). Pa \<mapsto>\<^sub>a P * \<up>(length P = length P0)"
  have step: "<?A P u * Ea \<mapsto>\<^sub>a E>
                do { e \<leftarrow> Array.nth Ea j; Array.upd (key e) j Pa; return () }
              <\<lambda> r. ?A (list_update P (key (E ! j)) j) r * Ea \<mapsto>\<^sub>a E>"
    if "0 \<le> j" "j < length E" for j P and u :: unit
    using that assms by sep_auto
  have run: "<?A P0 () * Ea \<mapsto>\<^sub>a E> csr_pos_build_imp key Ea Pa (length E)
             <\<lambda> r. ?A (foldl (\<lambda> P j. list_update P (key (E ! j)) j) P0 [0..<length E]) r * Ea \<mapsto>\<^sub>a E>"
    unfolding csr_pos_build_imp_def by (rule foldl_range_imp_rule) (rule step)
  show ?thesis
    by (rule ht_cons_post[OF ht_cons_pre[OF _ run]]) (sep_auto simp: csr_pos_list_def)+
qed

end
