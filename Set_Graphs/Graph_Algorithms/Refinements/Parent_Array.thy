theory Parent_Array
  imports Parent_Map_Spec_Imp Imperative.Array_Range_Iteration
begin

provenance ai


section \<open>Parent Maps as Arrays\<close>

text \<open>A parent map over the vertices \<open>{..<n}\<close> is a single array of length \<open>n\<close>. A root is its own
      parent. Entries of vertices that are neither in the tree nor roots are arbitrary, so the
      array need not be cleared before it is initialised with new roots.

      The functional model is a partial map: @{term "\<pi> v = Some u"} means that \<open>u\<close> is the parent
      of \<open>v\<close>, or \<open>v\<close> is a root if \<open>u = v\<close>.\<close>

subsection \<open>The Imperative Operations\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) parent_array_get_path_imp :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
  where
  "parent_array_get_path_imp Pa Ra k s =
     do { Array.upd k s Ra;
          u \<leftarrow> Array.nth Pa s;
          if u = s then return (Suc k)
          else parent_array_get_path_imp Pa Ra (Suc k) u }"

fun parent_array_init_imp :: "nat array \<times> nat \<Rightarrow> nat array \<Rightarrow> unit Heap" where
  "parent_array_init_imp (Ra, k) Pa = iterate_range_strict Ra 0 k (\<lambda> v _. do { Array.upd v v Pa; return () }) ()"

definition \<^marker>\<open>provenance ai_human\<close> parent_array_extend_imp :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
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
  unfolding pa_invar_def pa_graph_def pa_roots_def dVs_eq
  by force

lemma pa_path_fuel_nonempty: "pa_path_fuel f \<pi> s \<noteq> []"
  by (cases f) (auto split: option.split)

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
  case (Suc f)
  then obtain u where u: "\<pi> s = Some u"
    by blast
  show ?case
  proof(cases "u = s")
    case False
    hence "(s, u) \<in> pa_graph \<pi>" "u \<in> dom \<pi>"
      using assms(1) u
      by (auto simp: pa_graph_def pa_invar_def)
    moreover obtain p' where p': "pa_path_fuel f \<pi> u = u # p'"
      using Suc.IH[OF calculation(2)]
      by (cases "pa_path_fuel f \<pi> u") auto
    moreover have "Vwalk.vwalk (pa_graph \<pi>) (u # p')"
      using Suc.IH[OF calculation(2)] calculation(1)
      unfolding p'
      by (cases p') (auto simp: dVsI)
    ultimately show ?thesis
      using Suc.IH[OF \<open>u \<in> dom \<pi>\<close>] assms(2) Suc.prems u False
      unfolding p'
      by (fastforce simp: p')
  qed (use u Suc.prems in simp)
qed simp

lemma pa_get_path_props:
  assumes "pa_invar \<pi>" "s \<in> dom \<pi>"
  shows "pa_get_path \<pi> s \<noteq> []" "hd (pa_get_path \<pi> s) = s" "distinct (pa_get_path \<pi> s)"
        "tl (pa_get_path \<pi> s) = [] \<or> Vwalk.vwalk (pa_graph \<pi>) (pa_get_path \<pi> s)"
        "\<pi> (last (pa_get_path \<pi> s)) = Some (last (pa_get_path \<pi> s))"
proof-
  obtain r :: "nat \<Rightarrow> nat" where "\<forall> v u. (v, u) \<in> pa_graph \<pi> \<longrightarrow> r u < r v"
    using assms(1)
    unfolding pa_invar_def
    by blast
  note props = pa_path_fuel_props[OF assms(1) this assms(2), of n]
  thus "pa_get_path \<pi> s \<noteq> []" "hd (pa_get_path \<pi> s) = s" "distinct (pa_get_path \<pi> s)"
       "tl (pa_get_path \<pi> s) = [] \<or> Vwalk.vwalk (pa_graph \<pi>) (pa_get_path \<pi> s)"
    using sorted_wrt_rank_distinct
    unfolding pa_get_path_def
    by blast+
  moreover have "card (set (pa_get_path \<pi> s)) \<le> n"
    using props assms(1)
    unfolding pa_invar_def pa_get_path_def
    by (intro card_mono[OF finite_lessThan[of n], simplified]) blast
  ultimately show "\<pi> (last (pa_get_path \<pi> s)) = Some (last (pa_get_path \<pi> s))"
    using props
    by (auto simp: pa_get_path_def distinct_card)
qed

sublocale Parent_Map_Spec_static "{..<n}" pa_graph pa_get_path pa_invar pa_roots
proof(unfold_locales, goal_cases)
  case (1 \<pi>)
  thus ?case
    using pa_graph_dVs_dom[OF 1]
    unfolding pa_invar_def
    by blast
next
  case (2 \<pi> s)
  hence "s \<in> dom \<pi>"
    using pa_graph_dVs_dom
    by blast
  note p = pa_get_path_props[OF 2(1) this]
  show ?case
  proof(cases "tl (pa_get_path \<pi> s) = []")
    case True
    hence "pa_get_path \<pi> s = [s]"
      using p(1,2)
      by (cases "pa_get_path \<pi> s") auto
    thus ?thesis
      using p(5)
      by (auto simp: pa_roots_def)
  qed (use p in \<open>auto simp: pa_roots_def distinct_vwalk_bet_def vwalk_bet_def\<close>)
qed

sublocale Parent_Map_Spec_init "{..<n}" pa_graph pa_invar pa_roots set pa_init "\<lambda> _. True"
  by unfold_locales (auto simp: pa_roots_def pa_init_def pa_graph_def pa_invar_def split: if_splits)

lemma pa_extend_dom:
  "\<lbrakk>pa_invar \<pi>; v \<in> {..<n} - dVs (pa_graph \<pi>) - pa_roots \<pi>; u \<in> dVs (pa_graph \<pi>) \<union> pa_roots \<pi>\<rbrakk>
   \<Longrightarrow> v \<notin> dom \<pi> \<and> v < n \<and> u \<in> dom \<pi>"
  using pa_graph_dVs_dom
  by blast

sublocale Parent_Map_Spec_extend "{..<n}" pa_graph pa_extend pa_invar pa_roots
proof(unfold_locales, goal_cases)
  case (1 \<pi> u v)
  obtain r :: "nat \<Rightarrow> nat" where "\<forall> x y. (x, y) \<in> pa_graph \<pi> \<longrightarrow> r y < r x"
    using 1(1)
    unfolding pa_invar_def
    by blast
  hence "\<forall> x y. (x, y) \<in> pa_graph (pa_extend \<pi> u v) \<longrightarrow>
           fun_upd r v (Suc (r u)) y < fun_upd r v (Suc (r u)) x"
    using 1(1) pa_extend_dom[OF 1]
    by (auto simp: pa_graph_def pa_extend_def pa_invar_def)
  thus ?case
    using 1(1) pa_extend_dom[OF 1]
    unfolding pa_invar_def
    by (intro conjI exI[of _ "fun_upd r v (Suc (r u))"]) (auto simp: pa_extend_def)
qed (auto dest!: pa_extend_dom simp: pa_graph_def pa_roots_def pa_extend_def split: if_splits)

subsection \<open>Correctness of the Imperative Operations\<close>

lemma \<^marker>\<open>provenance ai_human\<close> pa_nth_rule:
  "\<lbrakk>\<pi> s = Some u; s < n\<rbrakk> \<Longrightarrow>
   <pa_parent_assn \<pi> Pa> Array.nth Pa s <\<lambda>r. pa_parent_assn \<pi> Pa * \<up>(r = u)>"
  unfolding pa_parent_assn_def
  by sep_auto

lemma \<^marker>\<open>provenance ai_human\<close> pa_get_path_imp_fuel:
  "\<lbrakk>pa_invar \<pi>; s \<in> dom \<pi>; \<pi> (last (pa_path_fuel f \<pi> s)) = Some (last (pa_path_fuel f \<pi> s));
    k + length (pa_path_fuel f \<pi> s) \<le> length r\<rbrakk> \<Longrightarrow>
   <pa_parent_assn \<pi> Pa * Ra \<mapsto>\<^sub>a r> parent_array_get_path_imp Pa Ra k s
   <\<lambda>k'. pa_parent_assn \<pi> Pa *
         Ra \<mapsto>\<^sub>a (take k r @ pa_path_fuel f \<pi> s @ drop (k + length (pa_path_fuel f \<pi> s)) r) *
         \<up>(k' = k + length (pa_path_fuel f \<pi> s))>"
proof(induction f arbitrary: s k r)
  case 0
  hence "s < n" "k < length r" "\<pi> s = Some s"
    by (auto simp: pa_invar_def)
  thus ?case
    by (subst parent_array_get_path_imp.simps) (sep_auto heap: pa_nth_rule simp: upd_conv_take_nth_drop)
next
  case (Suc f)
  then obtain u where u: "\<pi> s = Some u"
    by blast
  have "s < n" "k < length r"
    using Suc.prems pa_path_fuel_nonempty[of "Suc f" \<pi> s]
    by (auto simp: pa_invar_def neq_Nil_conv simp del: pa_path_fuel.simps)
  show ?case
  proof(cases "u = s")
    case True
    thus ?thesis
      using u \<open>s < n\<close> \<open>k < length r\<close>
      by (subst parent_array_get_path_imp.simps) (sep_auto heap: pa_nth_rule simp: upd_conv_take_nth_drop)
  next
    case False
    hence "pa_path_fuel (Suc f) \<pi> s = s # pa_path_fuel f \<pi> u" "u \<in> dom \<pi>"
      using Suc.prems(1) u
      by (auto simp: pa_invar_def)
    moreover note IH = Suc.IH[OF Suc.prems(1) this(2)]
    moreover have "list_update (take (Suc k) r) k s = take k r @ [s]"
      using \<open>k < length r\<close>
      by (simp add: take_Suc_conv_app_nth list_update_append)
    ultimately show ?thesis
      using Suc.prems(3,4) u \<open>s < n\<close> \<open>k < length r\<close> False pa_path_fuel_nonempty[of f \<pi> u]
      by (subst parent_array_get_path_imp.simps)
        (sep_auto heap: pa_nth_rule IH simp: take_update_swap)
  qed
qed

lemma \<^marker>\<open>provenance ai_human\<close> pa_get_path_rule:
  "\<lbrakk>pa_invar \<pi>; s \<in> dVs (pa_graph \<pi>) \<union> pa_roots \<pi>;
    k + length (pa_get_path \<pi> s) \<le> length r\<rbrakk> \<Longrightarrow>
   <pa_parent_assn \<pi> Pa * Ra \<mapsto>\<^sub>a r> parent_array_get_path_imp Pa Ra k s
   <\<lambda>k'. pa_parent_assn \<pi> Pa *
         Ra \<mapsto>\<^sub>a (take k r @ pa_get_path \<pi> s @ drop (k + length (pa_get_path \<pi> s)) r) *
         \<up>(k' = k + length (pa_get_path \<pi> s))>"
  using pa_get_path_imp_fuel[of \<pi> s n k r Pa Ra] pa_get_path_props(5)[of \<pi> s] pa_graph_dVs_dom[of \<pi>]
  unfolding pa_get_path_def
  by blast

text \<open>Initialisation from a prefix of length @{term k} of the array @{term Ra}.\<close>

lemma \<^marker>\<open>provenance ai_human\<close> pa_init_array_rule:
  assumes "set R \<subseteq> {..<n}" "k < length xs" "set (take k xs) = set R"
  shows "<Ra \<mapsto>\<^sub>a xs * pa_parent_assn \<pi> Pa> parent_array_init_imp (Ra, k) Pa
         <\<lambda>_. Ra \<mapsto>\<^sub>a xs * pa_parent_assn (pa_init R) Pa>"
proof-
  define acc_assn where
    "acc_assn = (\<lambda> (A::nat set) (_::unit).
       \<exists>\<^sub>A xs. Pa \<mapsto>\<^sub>a xs * \<up>(length xs = n \<and> (\<forall> v \<in> A. xs ! v = v)))"
  have "<acc_assn A acci * emp> do { Array.upd x x Pa; return () }
        <\<lambda>r. acc_assn (Set.insert x A) r * emp>"
    if "x \<in> set (nths xs {0..<k})" for A acci x
    using that assms(1,3)
    unfolding acc_assn_def
    by (sep_auto simp: nth_list_update atLeast0LessThan)
  hence "<Ra \<mapsto>\<^sub>a xs * acc_assn {} ()>
           iterate_range_strict Ra 0 k (\<lambda> v _. do { Array.upd v v Pa; return () }) ()
         <\<lambda>_. Ra \<mapsto>\<^sub>a xs * acc_assn (set R) ()>"
    using iterate_range_strict_rule[of xs 0 k acc_assn emp
            "\<lambda> v _. do { Array.upd v v Pa; return () }" "\<lambda> A x. Set.insert x A" Ra "{}" "()"] assms(2,3)
    by (sep_auto simp: mod_pure_star_dist atLeast0LessThan foldl_insert_set)
  thus ?thesis
    unfolding parent_array_init_imp.simps
    by (rule ht_cons_prec[rotated 2])
      (sep_auto simp: pa_parent_assn_def acc_assn_def pa_init_def split: if_splits)+
qed

lemma \<^marker>\<open>provenance ai_human\<close> pa_init_rule:
  assumes "set R \<subseteq> {..<n}"
  shows "<pa_parent_assn \<pi> Pa * pa_roots_assn R Ri> parent_array_init_imp Ri Pa
         <\<lambda>_. pa_parent_assn (pa_init R) Pa * pa_roots_assn R Ri>"
  by (induction Ri) (unfold pa_roots_assn_def fst_conv snd_conv, sep_auto heap: pa_init_array_rule[OF assms])

lemma \<^marker>\<open>provenance ai_human\<close> pa_extend_rule:
  "\<lbrakk>pa_invar \<pi>; v \<in> {..<n} - dVs (pa_graph \<pi>) - pa_roots \<pi>;
    u \<in> dVs (pa_graph \<pi>) \<union> pa_roots \<pi>\<rbrakk> \<Longrightarrow>
   <pa_parent_assn \<pi> Pa> parent_array_extend_imp Pa u v <\<lambda>_. pa_parent_assn (pa_extend \<pi> u v) Pa>"
  unfolding pa_parent_assn_def parent_array_extend_imp_def pa_extend_def
  by (sep_auto simp: nth_list_update)

text \<open>Any array of length \<open>n\<close> refines the empty parent map, e.g. a freshly allocated one.\<close>

lemma pa_parent_assn_intro: "length xs = n \<Longrightarrow> Pa \<mapsto>\<^sub>a xs \<Longrightarrow>\<^sub>A pa_parent_assn Map.empty Pa"
  unfolding pa_parent_assn_def
  by sep_auto

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

text \<open>The parent array at the fixed handle \<open>Pa\<close>: the operations of the parent array are
      correct for it.\<close>

lemma parent_array_at:
  "Parent_Map_Spec_extend_imp {..<n} parent_array.pa_graph parent_array.pa_extend
     (parent_array.pa_invar n) parent_array.pa_roots
     (\<lambda>p pi. parent_array.pa_parent_assn n p pi * \<up>(pi = Pa)) parent_array_extend_imp"
  "Parent_Map_Spec_static_imp {..<n} parent_array.pa_graph (parent_array.pa_get_path n)
     (parent_array.pa_invar n) parent_array.pa_roots
     (\<lambda>p pi. parent_array.pa_parent_assn n p pi * \<up>(pi = Pa)) parent_array_get_path_imp"
  "\<lbrakk>set R \<subseteq> {..<n}; k < length xs; set (take k xs) = set R\<rbrakk> \<Longrightarrow>
   <Ra \<mapsto>\<^sub>a xs * (parent_array.pa_parent_assn n \<pi> \<pi>i * \<up>(\<pi>i = Pa))> parent_array_init_imp (Ra, k) \<pi>i
   <\<lambda>_. Ra \<mapsto>\<^sub>a xs * (parent_array.pa_parent_assn n (parent_array.pa_init R) \<pi>i * \<up>(\<pi>i = Pa))>"
proof-
  interpret pa: parent_array n .
  show "Parent_Map_Spec_extend_imp {..<n} parent_array.pa_graph parent_array.pa_extend
     (parent_array.pa_invar n) parent_array.pa_roots
     (\<lambda>p pi. parent_array.pa_parent_assn n p pi * \<up>(pi = Pa)) parent_array_extend_imp"
    by (intro Parent_Map_Spec_extend_imp.intro Parent_Map_Spec_extend_imp_axioms.intro
              Parent_Map_Spec_extend_imp.axioms(1)[OF pa.extend_imp.Parent_Map_Spec_extend_imp_axioms])
       (sep_auto heap: pa.pa_extend_rule)
  show "Parent_Map_Spec_static_imp {..<n} parent_array.pa_graph (parent_array.pa_get_path n)
     (parent_array.pa_invar n) parent_array.pa_roots
     (\<lambda>p pi. parent_array.pa_parent_assn n p pi * \<up>(pi = Pa)) parent_array_get_path_imp"
    by (intro Parent_Map_Spec_static_imp.intro Parent_Map_Spec_static_imp_axioms.intro
              Parent_Map_Spec_static_imp.axioms(1)[OF pa.static_imp.Parent_Map_Spec_static_imp_axioms])
       (sep_auto heap: pa.pa_get_path_rule)
  show "\<lbrakk>set R \<subseteq> {..<n}; k < length xs; set (take k xs) = set R\<rbrakk> \<Longrightarrow>
   <Ra \<mapsto>\<^sub>a xs * (parent_array.pa_parent_assn n \<pi> \<pi>i * \<up>(\<pi>i = Pa))> parent_array_init_imp (Ra, k) \<pi>i
   <\<lambda>_. Ra \<mapsto>\<^sub>a xs * (parent_array.pa_parent_assn n (parent_array.pa_init R) \<pi>i * \<up>(\<pi>i = Pa))>"
    by (sep_auto heap: pa.pa_init_array_rule)
qed

end
