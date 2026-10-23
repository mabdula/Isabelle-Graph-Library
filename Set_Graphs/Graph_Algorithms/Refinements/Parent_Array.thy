theory Parent_Array
  imports Parent_Map_Spec_Imp Imperative.Array_Range_Iteration
begin

section \<open>Parent Maps as Arrays\<close>

text \<open>A parent map over the vertices \<open>{..<n}\<close> is a single array of length \<open>n\<close>. A root is its own
      parent. Entries of vertices that are neither in the tree nor roots are arbitrary, so the
      array need not be cleared before it is initialised with new roots.

      The functional model is a partial map: @{term "\<pi> v = Some u"} means that \<open>u\<close> is the parent
      of \<open>v\<close>, or \<open>v\<close> is a root if \<open>u = v\<close>.\<close>

subsection \<open>The Imperative Operations\<close>

partial_function (heap) parent_array_get_path_imp :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
  where
  "parent_array_get_path_imp Pa Ra k s =
     do { Array.upd k s Ra;
          u \<leftarrow> Array.nth Pa s;
          if u = s then return (Suc k)
          else parent_array_get_path_imp Pa Ra (Suc k) u }"

fun parent_array_init_imp :: "nat array \<times> nat \<Rightarrow> nat array \<Rightarrow> unit Heap" where
  "parent_array_init_imp (Ra, k) Pa = iterate_range_strict Ra 0 k (\<lambda> v _. do { Array.upd v v Pa; return () }) ()"

definition parent_array_extend_imp :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "parent_array_extend_imp Pa u v = do { Array.upd v u Pa; return () }"

subsection \<open>The Functional Model\<close>

locale parent_array =
  fixes n :: nat
begin

definition "pa_graph (\<pi>::nat \<Rightarrow> nat option) = {(v, u). \<pi> v = Some u \<and> u \<noteq> v}"

definition "pa_roots (\<pi>::nat \<Rightarrow> nat option) = {v. \<pi> v = Some v}"

text \<open>The parents are in the map, and a rank decreases along the edges, so that following the
      parents ends in a root.\<close>

definition "pa_invar \<pi> \<longleftrightarrow> dom \<pi> \<subseteq> {..<n} \<and> (\<forall> v u. \<pi> v = Some u \<longrightarrow> u \<in> dom \<pi>) \<and>
     (\<exists> r::nat \<Rightarrow> nat. \<forall> v u. (v, u) \<in> pa_graph \<pi> \<longrightarrow> r u < r v)"

text \<open>Following the parents for at most \<open>f\<close> steps. Since a path has at most \<open>n\<close> vertices, \<open>n\<close>
      steps suffice.\<close>

fun pa_path_fuel :: "nat \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> nat list" where
  "pa_path_fuel 0 \<pi> s = [s]"
| "pa_path_fuel (Suc f) \<pi> s =
     (case \<pi> s of Some u \<Rightarrow> if u = s then [s] else s # pa_path_fuel f \<pi> u | None \<Rightarrow> [s])"

definition "pa_get_path \<pi> s = pa_path_fuel n \<pi> s"

definition "pa_init (R::nat list) = (\<lambda> v. if v \<in> set R then Some v else None)"

definition "pa_extend \<pi> (u::nat) v = \<pi>(v \<mapsto> u)"

definition "pa_parent_assn \<pi> Pa =
   (\<exists>\<^sub>A xs. Pa \<mapsto>\<^sub>a xs * \<up>(length xs = n \<and> (\<forall> v u. \<pi> v = Some u \<longrightarrow> xs ! v = u)))"

text \<open>The roots are given by a prefix of an array.\<close>

definition "pa_roots_assn (R::nat list) Ri =
   (\<exists>\<^sub>A xs. fst Ri \<mapsto>\<^sub>a xs * \<up>(snd Ri < length xs \<and> set (take (snd Ri) xs) = set R))"

lemma pa_graph_dVs_dom: "pa_invar \<pi> \<Longrightarrow> dVs (pa_graph \<pi>) \<union> pa_roots \<pi> = dom \<pi>"
  unfolding pa_invar_def pa_graph_def pa_roots_def dVs_eq by force

lemma pa_path_fuel_props:
  fixes r :: "nat \<Rightarrow> nat"
  assumes "pa_invar \<pi>" "\<forall> v u. (v, u) \<in> pa_graph \<pi> \<longrightarrow> r u < r v" "s \<in> dom \<pi>"
  shows "pa_path_fuel f \<pi> s \<noteq> [] \<and> hd (pa_path_fuel f \<pi> s) = s \<and> set (pa_path_fuel f \<pi> s) \<subseteq> dom \<pi> \<and>
         (\<forall> y \<in> set (pa_path_fuel f \<pi> s). r y \<le> r s) \<and>
         sorted_wrt (\<lambda> a b. r b < r a) (pa_path_fuel f \<pi> s) \<and>
         (tl (pa_path_fuel f \<pi> s) = [] \<or> Vwalk.vwalk (pa_graph \<pi>) (pa_path_fuel f \<pi> s)) \<and>
         (\<pi> (last (pa_path_fuel f \<pi> s)) = Some (last (pa_path_fuel f \<pi> s)) \<or>
          length (pa_path_fuel f \<pi> s) = Suc f)"
  using assms(3)
proof(induction f arbitrary: s)
  case 0
  then show ?case
    by simp
next
  case (Suc f)
  obtain u where u: "\<pi> s = Some u"
    using Suc.prems by blast
  show ?case
  proof(cases "u = s")
    case True
    then show ?thesis
      using u Suc.prems by simp
  next
    case False
    have e: "(s, u) \<in> pa_graph \<pi>"
      using u False by (simp add: pa_graph_def)
    have ud: "u \<in> dom \<pi>"
      using assms(1) u by (auto simp: pa_invar_def)
    have ru: "r u < r s"
      using assms(2) e by blast
    note IH = Suc.IH[OF ud]
    obtain p' where p': "pa_path_fuel f \<pi> u = u # p'"
      using IH by (cases "pa_path_fuel f \<pi> u") auto
    have eq: "pa_path_fuel (Suc f) \<pi> s = s # u # p'"
      using u False p' by simp
    have vw: "Vwalk.vwalk (pa_graph \<pi>) (u # p')"
      using IH e unfolding p' by (cases p') (auto simp: dVsI)
    show ?thesis
      unfolding eq using IH ru e vw Suc.prems unfolding p' by fastforce
  qed
qed

lemma sorted_wrt_rank_distinct: "sorted_wrt (\<lambda> a b. (r::nat \<Rightarrow> nat) b < r a) p \<Longrightarrow> distinct p"
  by (induction p) auto

lemma pa_get_path_root:
  assumes "pa_invar \<pi>" "s \<in> dom \<pi>"
  shows "\<pi> (last (pa_get_path \<pi> s)) = Some (last (pa_get_path \<pi> s))"
proof-
  obtain r :: "nat \<Rightarrow> nat" where r: "\<forall> v u. (v, u) \<in> pa_graph \<pi> \<longrightarrow> r u < r v"
    using assms(1) unfolding pa_invar_def by blast
  have props: "sorted_wrt (\<lambda> a b. r b < r a) (pa_get_path \<pi> s)" "set (pa_get_path \<pi> s) \<subseteq> dom \<pi>"
    "\<pi> (last (pa_get_path \<pi> s)) = Some (last (pa_get_path \<pi> s)) \<or> length (pa_get_path \<pi> s) = Suc n"
    using pa_path_fuel_props[OF assms(1) r assms(2), of n] by (simp_all add: pa_get_path_def)
  have "length (pa_get_path \<pi> s) \<noteq> Suc n"
  proof
    assume len: "length (pa_get_path \<pi> s) = Suc n"
    have "distinct (pa_get_path \<pi> s)"
      by (rule sorted_wrt_rank_distinct[OF props(1)])
    then have "card (set (pa_get_path \<pi> s)) = Suc n"
      using len by (simp add: distinct_card)
    moreover have "set (pa_get_path \<pi> s) \<subseteq> {..<n}"
      using props(2) assms(1) unfolding pa_invar_def by (blast intro: order.trans)
    ultimately show False
      using card_mono[OF finite_lessThan[of n], of "set (pa_get_path \<pi> s)"] by simp
  qed
  then show ?thesis
    using props(3) by simp
qed

lemma pa_get_path_props:
  assumes "pa_invar \<pi>" "s \<in> dom \<pi>"
  shows "pa_get_path \<pi> s \<noteq> []" "hd (pa_get_path \<pi> s) = s" "distinct (pa_get_path \<pi> s)"
        "tl (pa_get_path \<pi> s) = [] \<or> Vwalk.vwalk (pa_graph \<pi>) (pa_get_path \<pi> s)"
proof-
  obtain r :: "nat \<Rightarrow> nat" where r: "\<forall> v u. (v, u) \<in> pa_graph \<pi> \<longrightarrow> r u < r v"
    using assms(1) unfolding pa_invar_def by blast
  note props = pa_path_fuel_props[OF assms(1) r assms(2), of n]
  show "pa_get_path \<pi> s \<noteq> []" "hd (pa_get_path \<pi> s) = s"
       "tl (pa_get_path \<pi> s) = [] \<or> Vwalk.vwalk (pa_graph \<pi>) (pa_get_path \<pi> s)"
    using props unfolding pa_get_path_def by blast+
  show "distinct (pa_get_path \<pi> s)"
    using props sorted_wrt_rank_distinct unfolding pa_get_path_def by blast
qed

sublocale Parent_Map_Spec_static "{..<n}" pa_graph pa_get_path pa_invar pa_roots
proof(unfold_locales, goal_cases)
  case (1 \<pi>)
  then show ?case
    using pa_graph_dVs_dom[OF 1] unfolding pa_invar_def by blast
next
  case (2 \<pi> s)
  have s: "s \<in> dom \<pi>"
    using 2 pa_graph_dVs_dom[OF 2(1)] by blast
  note p = pa_get_path_props[OF 2(1) s]
  have t: "last (pa_get_path \<pi> s) \<in> pa_roots \<pi>"
    using pa_get_path_root[OF 2(1) s] by (simp add: pa_roots_def)
  show ?case
  proof(cases "tl (pa_get_path \<pi> s) = []")
    case True
    then have "pa_get_path \<pi> s = [s]"
      using p(1,2) by (cases "pa_get_path \<pi> s") auto
    then show ?thesis
      using t by auto
  next
    case False
    then have "distinct_vwalk_bet (pa_graph \<pi>) s (pa_get_path \<pi> s) (last (pa_get_path \<pi> s))"
      using p by (simp add: distinct_vwalk_bet_def vwalk_bet_def)
    then show ?thesis
      using t by blast
  qed
qed

sublocale Parent_Map_Spec_init "{..<n}" pa_graph pa_invar pa_roots set pa_init "\<lambda> _. True"
proof(unfold_locales, goal_cases)
  case (1 R)
  then show ?case
    by (auto simp: pa_roots_def pa_init_def)
next
  case (2 R)
  then show ?case
    by (auto simp: pa_graph_def pa_init_def split: if_splits)
next
  case (3 R)
  have "pa_graph (pa_init R) = {}"
    by (auto simp: pa_graph_def pa_init_def split: if_splits)
  then show ?case
    using 3 by (auto simp: pa_invar_def pa_init_def split: if_splits)
qed

sublocale Parent_Map_Spec_extend "{..<n}" pa_graph pa_extend pa_invar pa_roots
proof(unfold_locales, goal_cases)
  case (1 \<pi> u v)
  have v: "v \<notin> dom \<pi>" "v < n"
    using 1 pa_graph_dVs_dom[OF 1(1)] by auto
  have u: "u \<in> dom \<pi>"
    using 1 pa_graph_dVs_dom[OF 1(1)] by auto
  obtain r :: "nat \<Rightarrow> nat" where r: "\<forall> x y. (x, y) \<in> pa_graph \<pi> \<longrightarrow> r y < r x"
    using 1(1) unfolding pa_invar_def by blast
  have "u \<noteq> v"
    using u v by blast
  have "\<forall> x y. (x, y) \<in> pa_graph (pa_extend \<pi> u v) \<longrightarrow> fun_upd r v (Suc (r u)) y < fun_upd r v (Suc (r u)) x"
  proof(intro allI impI)
    fix x y
    assume xy: "(x, y) \<in> pa_graph (pa_extend \<pi> u v)"
    show "fun_upd r v (Suc (r u)) y < fun_upd r v (Suc (r u)) x"
    proof(cases "x = v")
      case True
      then show ?thesis
        using xy \<open>u \<noteq> v\<close> by (simp add: pa_graph_def pa_extend_def)
    next
      case False
      then have "(x, y) \<in> pa_graph \<pi>"
        using xy by (simp add: pa_graph_def pa_extend_def)
      moreover have "y \<noteq> v"
        using calculation v(1) 1(1) by (auto simp: pa_graph_def pa_invar_def)
      ultimately show ?thesis
        using r False by simp
    qed
  qed
  moreover have "dom (pa_extend \<pi> u v) \<subseteq> {..<n}"
    using 1(1) v by (auto simp: pa_invar_def pa_extend_def)
  moreover have "\<forall> x y. pa_extend \<pi> u v x = Some y \<longrightarrow> y \<in> dom (pa_extend \<pi> u v)"
    using 1(1) u by (auto simp: pa_invar_def pa_extend_def)
  ultimately show ?case
    unfolding pa_invar_def by blast
next
  case (2 \<pi> u v)
  have "v \<notin> dom \<pi>" "u \<in> dom \<pi>"
    using 2 pa_graph_dVs_dom[OF 2(1)] by auto
  then show ?case
    by (auto simp: pa_graph_def pa_extend_def split: if_splits)
next
  case (3 \<pi> u v)
  have "v \<notin> dom \<pi>" "u \<in> dom \<pi>"
    using 3 pa_graph_dVs_dom[OF 3(1)] by auto
  then show ?case
    by (auto simp: pa_roots_def pa_extend_def split: if_splits)
qed

subsection \<open>Correctness of the Imperative Operations\<close>

lemma pa_nth_rule:
  "\<lbrakk>\<pi> s = Some u; s < n\<rbrakk> \<Longrightarrow>
   <pa_parent_assn \<pi> Pa> Array.nth Pa s <\<lambda>r. pa_parent_assn \<pi> Pa * \<up>(r = u)>"
  unfolding pa_parent_assn_def by sep_auto
lemma pa_get_path_imp_fuel:
  assumes "pa_invar \<pi>"
  shows "\<lbrakk>s \<in> dom \<pi>; \<pi> (last (pa_path_fuel f \<pi> s)) = Some (last (pa_path_fuel f \<pi> s));
          k + length (pa_path_fuel f \<pi> s) \<le> length r\<rbrakk> \<Longrightarrow>
         <pa_parent_assn \<pi> Pa * Ra \<mapsto>\<^sub>a r> parent_array_get_path_imp Pa Ra k s
         <\<lambda>k'. pa_parent_assn \<pi> Pa *
               Ra \<mapsto>\<^sub>a (take k r @ pa_path_fuel f \<pi> s @ drop (k + length (pa_path_fuel f \<pi> s)) r) *
               \<up>(k' = k + length (pa_path_fuel f \<pi> s))>"
proof(induction f arbitrary: s k r)
  case 0
  have s: "s < n" and k: "k < length r" and root: "\<pi> s = Some s"
    using 0 assms by (auto simp: pa_invar_def)
  then show ?case
    by (subst parent_array_get_path_imp.simps)
       (sep_auto heap: pa_nth_rule[of \<pi> s s, OF root s] simp: upd_conv_take_nth_drop)
next
  case (Suc f)
  obtain u where u: "\<pi> s = Some u"
    using Suc.prems(1) by blast
  have s: "s < n"
    using Suc.prems(1) assms by (auto simp: pa_invar_def)
  have "pa_path_fuel (Suc f) \<pi> s \<noteq> []"
    by (simp split: option.split)
  then have k: "k < length r"
    using Suc.prems(3) by (cases "pa_path_fuel (Suc f) \<pi> s") auto
  show ?case
  proof(cases "u = s")
    case True
    then show ?thesis
      using u s k
      by (subst parent_array_get_path_imp.simps)
         (sep_auto heap: pa_nth_rule[of \<pi> s u, OF u s] simp: upd_conv_take_nth_drop)
  next
    case False
    have eq: "pa_path_fuel (Suc f) \<pi> s = s # pa_path_fuel f \<pi> u"
      using u False by simp
    have ud: "u \<in> dom \<pi>"
      using assms u by (auto simp: pa_invar_def)
    have ne: "pa_path_fuel f \<pi> u \<noteq> []"
      by (cases f) (auto split: option.split)
    have last: "\<pi> (last (pa_path_fuel f \<pi> u)) = Some (last (pa_path_fuel f \<pi> u))"
      using Suc.prems(2) ne unfolding eq by simp
    have len: "Suc k + length (pa_path_fuel f \<pi> u) \<le> length (list_update r k s)"
      using Suc.prems(3) unfolding eq by simp
    note IH = Suc.IH[OF ud last len]
    have tu: "list_update (take (Suc k) r) k s = take k r @ [s]"
      using k by (simp add: take_Suc_conv_app_nth list_update_append)
    have dv: "drop (Suc (k + length (pa_path_fuel f \<pi> u))) (list_update r k s) =
              drop (Suc (k + length (pa_path_fuel f \<pi> u))) r"
      by (rule drop_update_cancel) simp
    show ?thesis
      unfolding eq
      using u s k False
      by (subst parent_array_get_path_imp.simps)
         (sep_auto heap: pa_nth_rule[of \<pi> s u, OF u s] IH simp: tu dv)
  qed
qed
lemma pa_get_path_rule:
  "\<lbrakk>pa_invar \<pi>; s \<in> dVs (pa_graph \<pi>) \<union> pa_roots \<pi>; k + length (pa_get_path \<pi> s) \<le> length r\<rbrakk> \<Longrightarrow>
   <pa_parent_assn \<pi> Pa * Ra \<mapsto>\<^sub>a r> parent_array_get_path_imp Pa Ra k s
   <\<lambda>k'. pa_parent_assn \<pi> Pa *
         Ra \<mapsto>\<^sub>a (take k r @ pa_get_path \<pi> s @ drop (k + length (pa_get_path \<pi> s)) r) *
         \<up>(k' = k + length (pa_get_path \<pi> s))>"
  using pa_get_path_imp_fuel[of \<pi> s n k r Pa Ra] pa_get_path_root[of \<pi> s] pa_graph_dVs_dom[of \<pi>]
  unfolding pa_get_path_def by blast

lemma foldl_insert_set: "foldl (\<lambda> A x. Set.insert x A) B ys = set ys \<union> B"
  by (induction ys arbitrary: B) auto

text \<open>Initialisation from a prefix of length @{term k} of the array @{term Ra}.\<close>

lemma pa_init_array_rule:
  assumes "set R \<subseteq> {..<n}" "k < length xs" "set (take k xs) = set R"
  shows "<Ra \<mapsto>\<^sub>a xs * pa_parent_assn \<pi> Pa> parent_array_init_imp (Ra, k) Pa
         <\<lambda>_. Ra \<mapsto>\<^sub>a xs * pa_parent_assn (pa_init R) Pa>"
proof-
  define acc_assn where
    "acc_assn = (\<lambda> (A::nat set) (_::unit).
       \<exists>\<^sub>A xs. Pa \<mapsto>\<^sub>a xs * \<up>(length xs = n \<and> (\<forall> v \<in> A. xs ! v = v)))"
  have nths: "nths xs {0..<k} = take k xs"
    by (simp add: atLeast0LessThan)
  have step: "<acc_assn A acci * emp> do { Array.upd x x Pa; return () }
              <\<lambda>r. acc_assn (Set.insert x A) r * emp>"
    if x: "x \<in> set (nths xs {0..<k})" for A acci x
  proof-
    have "x < n"
      using x assms(1,3) unfolding nths by auto
    then show ?thesis
      unfolding acc_assn_def by (sep_auto simp: nth_list_update)
  qed
  have fold: "foldl (\<lambda> A x. Set.insert x A) {} (nths xs {0..<k}) = set R"
    unfolding nths foldl_insert_set assms(3) by simp
  have main: "<Ra \<mapsto>\<^sub>a xs * acc_assn {} ()>
     iterate_range_strict Ra 0 k (\<lambda> v _. do { Array.upd v v Pa; return () }) ()
     <\<lambda>_. Ra \<mapsto>\<^sub>a xs * acc_assn (set R) ()>"
    using iterate_range_strict_rule[of xs 0 k acc_assn emp
            "\<lambda> v _. do { Array.upd v v Pa; return () }" "\<lambda> A x. Set.insert x A" Ra "{}" "()",
            OF step] assms(2)
    unfolding fold by (sep_auto simp: mod_pure_star_dist)
  have pre: "pa_parent_assn \<pi> Pa \<Longrightarrow>\<^sub>A acc_assn {} ()"
    unfolding pa_parent_assn_def acc_assn_def by sep_auto
  have post: "acc_assn (set R) () \<Longrightarrow>\<^sub>A pa_parent_assn (pa_init R) Pa"
    unfolding pa_parent_assn_def acc_assn_def pa_init_def by (sep_auto split: if_splits)
  show ?thesis
    unfolding parent_array_init_imp.simps
    by (rule ht_cons_prec[OF ent_star_mono[OF ent_refl pre] ent_star_mono[OF ent_refl post] main])
qed

lemma pa_init_rule:
  assumes "set R \<subseteq> {..<n}"
  shows "<pa_parent_assn \<pi> Pa * pa_roots_assn R Ri> parent_array_init_imp Ri Pa
         <\<lambda>_. pa_parent_assn (pa_init R) Pa * pa_roots_assn R Ri>"
proof(cases Ri)
  case (Pair Ra k)
  show ?thesis
    unfolding Pair pa_roots_assn_def fst_conv snd_conv
    by (sep_auto heap: pa_init_array_rule[OF assms])
qed

lemma pa_extend_rule:
  "\<lbrakk>pa_invar \<pi>; v \<in> {..<n} - dVs (pa_graph \<pi>) - pa_roots \<pi>; u \<in> dVs (pa_graph \<pi>) \<union> pa_roots \<pi>\<rbrakk> \<Longrightarrow>
   <pa_parent_assn \<pi> Pa> parent_array_extend_imp Pa u v <\<lambda>_. pa_parent_assn (pa_extend \<pi> u v) Pa>"
  unfolding pa_parent_assn_def parent_array_extend_imp_def pa_extend_def
  by (sep_auto simp: nth_list_update)

text \<open>Any array of length \<open>n\<close> refines the empty parent map, e.g. a freshly allocated one.\<close>

lemma pa_parent_assn_intro: "length xs = n \<Longrightarrow> Pa \<mapsto>\<^sub>a xs \<Longrightarrow>\<^sub>A pa_parent_assn Map.empty Pa"
  unfolding pa_parent_assn_def by sep_auto

sublocale static_imp: Parent_Map_Spec_static_imp "{..<n}" pa_graph pa_get_path pa_invar pa_roots
  pa_parent_assn parent_array_get_path_imp
  by unfold_locales (rule pa_get_path_rule)

sublocale init_imp: Parent_Map_Spec_init_imp "{..<n}" pa_graph pa_invar pa_roots set pa_init "\<lambda> _. True"
  pa_parent_assn pa_roots_assn parent_array_init_imp
  by unfold_locales (rule pa_init_rule, simp)

sublocale extend_imp: Parent_Map_Spec_extend_imp "{..<n}" pa_graph pa_extend pa_invar pa_roots
  pa_parent_assn parent_array_extend_imp
  by unfold_locales (rule pa_extend_rule)

end

end
