theory Matroid_Intersection_Path_Loop
  imports Matroid_Intersection
begin

section \<open>Matroid Intersection as a Loop over an Abstract Path Search\<close>

text \<open>The augmentation loop of unweighted matroid intersection. 
  It is parametrised by a function \<open>augmenting_path\<close> that returns a shortest
  augmenting path in the exchange graph of the current solution, or nothing.
  How this path is found (explicit graph, implicit graph, oracles, BFS) is
  invisible here.\<close>

record 'sol intersection_state = solution::'sol

lemma solution_remove: "solution (state \<lparr> solution:= new_sol \<rparr>) = new_sol"
  by auto

subsection \<open>Augmentation\<close>

text \<open>Augmenting a solution along a path, shared by every loop that augments along
  exchange-graph paths (unweighted and weighted).\<close>

locale intersection_augment_spec =
fixes set_insert::"'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
  and set_delete::"'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
  and to_set::"'mset \<Rightarrow> 'a set"
  and set_invar::"'mset \<Rightarrow> bool"
  and set_empty::"'mset"
begin

fun augment where
  "augment X Nil = X"|
  "augment X [x] = set_insert x X"|
  "augment X (x#y#xs) = augment (set_insert x (set_delete y X)) xs"

lemmas [code] = augment.simps

end

locale intersection_augment =
  intersection_augment_spec +
  fixes carrier::"'a set"
  assumes set_insert: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar (set_insert x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_insert x S) = Set.insert x (to_set S)"
  assumes set_delete: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar (set_delete x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_delete x S) = (to_set S) - {x}"
  assumes set_empty: "set_invar set_empty" "to_set set_empty = {}"
begin

lemma effect_of_augmentation:
  assumes "set_invar X" "to_set X \<subseteq> carrier" "set p \<subseteq> carrier" "distinct p"
    "X' = ((to_set X \<union> {p ! i | i. i < length p \<and> even i}) -  {p ! i | i. i < length p \<and> odd i})"
  shows "set_invar (augment X p)" "to_set (augment X p) = X'"
proof-
  show "set_invar (augment X p)"
    using assms(1-3)
    by (induction X p rule: augment.induct) (auto simp: set_insert set_delete)
  show "to_set (augment X p) = X'"
    using assms
  proof(induction X p arbitrary: X' rule: augment.induct)
    case (3 X x y zs)
    hence "to_set (augment (set_insert x (set_delete y X)) zs)
             = insert x (to_set X - {y}) \<union> {zs ! i | i. i < length zs \<and> even i}
               - {zs ! i | i. i < length zs \<and> odd i}"
      by (intro 3(1)) (auto simp: set_insert set_delete)
    thus ?case
      using 3(2-) nth_set_subset[of zs even] nth_set_subset[of zs odd]
      by (simp only: evens_odds_Cons2) (simp, blast)
  qed (auto simp: set_insert less_Suc_eq_0_disj)
qed

end

subsection \<open>The Loop\<close>

locale unweighted_intersection_path_loop_spec =
  intersection_augment_spec set_insert set_delete to_set set_invar set_empty
  for set_insert::"'a \<Rightarrow> 'mset \<Rightarrow> 'mset" and set_delete to_set set_invar set_empty +
  fixes augmenting_path::"'mset \<Rightarrow> 'a list option"
begin

function (domintros) matroid_intersection::"'mset intersection_state\<Rightarrow> 'mset intersection_state"  where
  "matroid_intersection state =
 (let X = solution state in
     (case augmenting_path X of 
          None \<Rightarrow> state |
          Some p \<Rightarrow> matroid_intersection (state \<lparr> solution := augment X p\<rparr>) ))"
  by pat_completeness auto

definition "matroid_intersection_recurse_cond state =
(let X = solution state in
     (case augmenting_path X of 
          None \<Rightarrow> False |
          Some p \<Rightarrow> True))"

lemma matroid_intersection_recurse_condE:
  "\<lbrakk>matroid_intersection_recurse_cond state;
    \<And> p X. \<lbrakk>X = solution state; augmenting_path X = Some p\<rbrakk> \<Longrightarrow> P\<rbrakk>
     \<Longrightarrow> P"
  by (force simp: matroid_intersection_recurse_cond_def Let_def)

definition "matroid_intersection_recurse_upd state =
(let X = solution state in
     state \<lparr> solution := augment X (the (augmenting_path X)) \<rparr>)"

lemma P_of_matroid_intersection_recurseI:
  "\<lbrakk>matroid_intersection_recurse_cond state;
    \<And> p X. \<lbrakk>X = solution state; augmenting_path X = Some p\<rbrakk>
      \<Longrightarrow> P (state \<lparr> solution := augment X p\<rparr>)\<rbrakk>
     \<Longrightarrow> P (matroid_intersection_recurse_upd state)"
  by (cases "augmenting_path (solution state)")
     (auto simp: matroid_intersection_recurse_cond_def matroid_intersection_recurse_upd_def Let_def)

definition "matroid_intersection_terminates_cond state =
(let X = solution state in
     (case augmenting_path X of 
          None \<Rightarrow> True |
          Some p \<Rightarrow> False))"

lemma matroid_intersection_terminates_condE:
  "\<lbrakk>matroid_intersection_terminates_cond state;
    \<And> X. \<lbrakk>X = solution state; augmenting_path X = None\<rbrakk> \<Longrightarrow> P\<rbrakk>
     \<Longrightarrow> P"
  by (force simp: matroid_intersection_terminates_cond_def Let_def)

lemma matroid_intersection_cases:
  "\<lbrakk>matroid_intersection_terminates_cond state \<Longrightarrow> P;
    matroid_intersection_recurse_cond state \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (cases "augmenting_path (solution state)")
     (auto simp: matroid_intersection_terminates_cond_def matroid_intersection_recurse_cond_def Let_def)

lemma matroid_intersection_simps:
  assumes "matroid_intersection_dom state"
  shows "matroid_intersection_terminates_cond state \<Longrightarrow> matroid_intersection state = state"
    "matroid_intersection_recurse_cond state \<Longrightarrow>
       matroid_intersection state = matroid_intersection (matroid_intersection_recurse_upd state)"
  by (auto intro: P_of_matroid_intersection_recurseI matroid_intersection_terminates_condE
      simp: matroid_intersection.psimps[OF assms] split: option.split)

lemma matroid_intersection_induct:
  assumes "matroid_intersection_dom state"
    "\<And> state. \<lbrakk>matroid_intersection_dom state;
       matroid_intersection_recurse_cond state \<Longrightarrow> P (matroid_intersection_recurse_upd state)\<rbrakk>
         \<Longrightarrow> P state"
  shows "P state"
  by (rule matroid_intersection.pinduct[OF assms(1)],
      rule assms(2)[simplified matroid_intersection_recurse_cond_def matroid_intersection_recurse_upd_def])
     (auto simp: Let_def split: option.splits)

partial_function (tailrec) matroid_intersection_impl::
  "'mset intersection_state \<Rightarrow> 'mset intersection_state" where
  "matroid_intersection_impl state =
 (let X = solution state in
     (case augmenting_path X of 
          None \<Rightarrow> state |
          Some p \<Rightarrow> matroid_intersection_impl (state \<lparr> solution := augment X p \<rparr>)))"

lemma implementation_is_same:
  "matroid_intersection_dom state \<Longrightarrow> matroid_intersection_impl state = matroid_intersection state"
  by (induction state rule: matroid_intersection.pinduct)
     (subst matroid_intersection_impl.simps, subst matroid_intersection.psimps, simp,
      auto simp: Let_def split: option.split)

definition "initial_state = \<lparr> solution = set_empty \<rparr>"

lemmas [code] = matroid_intersection_impl.simps initial_state_def

end

text \<open>Specification of the path search: \<open>None\<close> iff there is no walk from \<open>S\<close> to \<open>T\<close>
  in the exchange graph, and a returned path is such a walk which is shortest 
  between its endpoints.\<close>

locale unweighted_intersection_path_loop =
  unweighted_intersection_path_loop_spec
  where set_insert = "set_insert::'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    + intersection_augment where set_insert = set_insert and carrier = carrier
    + double_matroid 
  where carrier = "carrier::'a set"
  for set_insert carrier +
  assumes augmenting_path:
    "\<And> X. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; indep1 (to_set X); indep2 (to_set X)\<rbrakk>
      \<Longrightarrow> augmenting_path X = None \<longleftrightarrow> 
           (\<nexists> p u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)) \<and>
                       u \<in> S (to_set X) \<and> v \<in> T (to_set X))"
    "\<And> X p. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; indep1 (to_set X); indep2 (to_set X);
             augmenting_path X = Some p\<rbrakk>
      \<Longrightarrow> \<exists> u v. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v))
                  \<and> u \<in> S (to_set X) \<and> v \<in> T (to_set X) \<and>
             (\<nexists> p'. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p' v \<or> (p' = [u] \<and> u = v))
                         \<and> length p' < length p)"
begin

definition "indep_invar state = 
   (indep1 (to_set (solution state)) \<and> (indep2 (to_set (solution state))))"

text \<open>Augmenting along a shortest walk from \<open>S\<close> to \<open>T\<close>, or at a single vertex in
both \<open>S\<close> and \<open>T\<close>, keeps the solution a common independent set and raises its cardinality
by one.\<close>

lemma augment_walk_props:
  assumes "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
    "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v" "u \<in> S (to_set X)" "v \<in> T (to_set X)"
    "\<nexists>q. vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u q v \<and> length q < length p"
  shows "set_invar (augment X p) \<and> indep1 (to_set (augment X p)) \<and> indep2 (to_set (augment X p)) \<and>
    card (to_set (augment X p)) = card (to_set X) + 1"
proof-
  have "set p \<subseteq> carrier" "distinct p"
    using assms(3-5,8) dVs_A1A2_carrier[of "to_set X"]
      vwalk_bet_in_vertices[of "A1 (to_set X) \<union> A2 (to_set X)" u p v]
      shortest_vwalk_bet_distinct[of "A1 (to_set X) \<union> A2 (to_set X)" u p v]
    by blast+
  thus ?thesis
    using assms effect_of_augmentation[OF assms(1,2)]
      augment_in_both_matroids[of "to_set X" u p v "to_set (augment X p)"]
    by simp
qed

lemma augment_single_props:
  "\<lbrakk>set_invar X; to_set X \<subseteq> carrier; indep1 (to_set X); indep2 (to_set X); u \<in> S (to_set X);
    u \<in> T (to_set X)\<rbrakk> \<Longrightarrow>
     set_invar (augment X [u]) \<and> indep1 (to_set (augment X [u])) \<and> indep2 (to_set (augment X [u])) \<and>
     card (to_set (augment X [u])) = card (to_set X) + 1"
  using S_in_carrier[of "to_set X"] augment_in_both_matroids_single[of "to_set X" u]
  by (auto simp: set_insert)

text \<open>Hence one augmentation along the path returned by the path search does so.\<close>

lemma augmenting_path_Some_props:
  assumes "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
    "augmenting_path X = Some p"
  shows "set_invar (augment X p)" "indep1 (to_set (augment X p))" "indep2 (to_set (augment X p))"
    "card (to_set (augment X p)) = card (to_set X) + 1"
    "\<exists>u v p. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)) \<and>
       u \<in> S (to_set X) \<and> v \<in> T (to_set X)"
proof-
  obtain u v where "vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)"
    "u \<in> S (to_set X)" "v \<in> T (to_set X)"
    "\<nexists> p'. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p' v \<or> (p' = [u] \<and> u = v))
       \<and> length p' < length p"
    using augmenting_path(2)[OF assms]
    by blast
  thus "set_invar (augment X p)" "indep1 (to_set (augment X p))" "indep2 (to_set (augment X p))"
    "card (to_set (augment X p)) = card (to_set X) + 1"
    "\<exists>u v p. (vwalk_bet (A1 (to_set X) \<union> A2 (to_set X)) u p v \<or> (p = [u] \<and> u = v)) \<and>
       u \<in> S (to_set X) \<and> v \<in> T (to_set X)"
    using assms augment_walk_props[of X u p v] augment_single_props[of X u]
    by blast+
qed

lemma indep_invar_recurse_improvement:
  assumes "matroid_intersection_recurse_cond state" "indep_invar state"
    "set_invar (solution state)" "to_set (solution state) \<subseteq> carrier"
  shows   "indep_invar (matroid_intersection_recurse_upd state)"
    "set_invar (solution (matroid_intersection_recurse_upd state))" 
    "to_set (solution (matroid_intersection_recurse_upd state)) \<subseteq> carrier"
    "card (to_set (solution (matroid_intersection_recurse_upd state))) = 
          card (to_set (solution state)) + 1"
    "S (to_set (solution state)) \<noteq> {}"
    "T (to_set (solution state)) \<noteq> {}"
    and   "\<exists>u v p. (vwalk_bet (A1 (to_set (solution state)) \<union> A2 (to_set (solution state))) u p v
                     \<or> (p = [u] \<and> u = v)) \<and>
           u \<in> S (to_set (solution state)) \<and>
           v \<in> T (to_set (solution state))"
  using assms augmenting_path_Some_props[of "solution state"] matroid1.indep_subset_carrier
  by (auto simp: indep_invar_def matroid_intersection_recurse_cond_def
        matroid_intersection_recurse_upd_def Let_def split: option.splits)

lemma indep_invar_max_found:
  assumes "matroid_intersection_terminates_cond state" "indep_invar state"
    "set_invar (solution state)" "to_set (solution state) \<subseteq> carrier"
  shows "is_max (to_set (solution state))"
proof-
  have "\<nexists>p x y. x \<in> S (to_set (solution state)) \<and> y \<in> T (to_set (solution state)) \<and>
          (vwalk_bet (A1 (to_set (solution state)) \<union> A2 (to_set (solution state))) x p y \<or> x = y)"
    using assms augmenting_path(1)[of "solution state"]
    by (simp add: indep_invar_def matroid_intersection_terminates_cond_def split: option.splits)
       blast
  thus ?thesis
    using assms(2) if_no_augpath_then_maximum(1)[OF _ _ _ refl]
    by (auto simp: indep_invar_def is_max_def)
qed

lemma matroid_intersection_domI:
  "(matroid_intersection_recurse_cond state \<Longrightarrow>
      matroid_intersection_dom (matroid_intersection_recurse_upd state)) \<Longrightarrow>
     matroid_intersection_dom state"
  by (rule matroid_intersection.domintros)
     (auto simp: matroid_intersection_recurse_cond_def matroid_intersection_recurse_upd_def)

lemma matroid_intersection_terminates_general:
  assumes "indep_invar state" "set_invar (solution state)" "to_set (solution state) \<subseteq> carrier"
    "m = card carrier - card (to_set (solution state))"
  shows "matroid_intersection_dom state"
  using assms
proof(induction m arbitrary: state)
  case 0
  hence "to_set (solution state) = carrier"
    by (simp add: card_seteq matroid2.carrier_finite)
  hence "S (to_set (solution state)) = {}"
    by (simp add: S_def)
  thus ?case
    using 0 indep_invar_recurse_improvement(5)[of state]
    by (blast intro: matroid_intersection_domI)
next
  case (Suc m)
  show ?case
  proof(rule matroid_intersection_domI)
    assume "matroid_intersection_recurse_cond state"
    thus "matroid_intersection_dom (matroid_intersection_recurse_upd state)"
      using Suc.prems indep_invar_recurse_improvement(1-4)[of state]
      by (auto intro: Suc.IH)
  qed
qed

lemma matroid_intersection_correctness_general:
  assumes "indep_invar state" "set_invar (solution state)" "to_set (solution state) \<subseteq> carrier"
  shows "is_max (to_set (solution (matroid_intersection state)))"
  using assms
proof(induction state rule: matroid_intersection_induct)
  case (2 state)
  thus ?case
    by (cases state rule: matroid_intersection_cases)
       (auto simp: indep_invar_max_found matroid_intersection_simps indep_invar_recurse_improvement)
qed (use matroid_intersection_terminates_general[OF assms refl] in simp)

lemma matroid_intersection_correctness:
  "indep_invar (matroid_intersection initial_state)"
  "is_max (to_set (solution (matroid_intersection initial_state)))"
  using matroid_intersection_correctness_general
  by (simp add: indep_invar_def initial_state_def is_max_def set_empty)+

lemma matroid_intersection_terminates: "matroid_intersection_dom initial_state"
  by (rule matroid_intersection_terminates_general) (auto simp: indep_invar_def set_empty initial_state_def)

lemma matroid_intersection_total_correctness:
  "is_max (to_set (solution (matroid_intersection initial_state)))"
  "matroid_intersection_dom initial_state"
  using matroid_intersection_correctness matroid_intersection_terminates
  by auto

lemma same_result: "matroid_intersection_impl initial_state = matroid_intersection initial_state"
  by (simp add: implementation_is_same matroid_intersection_terminates)

lemma impl_total_correctness:
  "is_max (to_set (solution (matroid_intersection_impl initial_state)))"
  using matroid_intersection_total_correctness(1) same_result
  by simp

end

end