theory Push_Relabel_Label_Buckets_Imperative
  imports
    Push_Relabel_Label_Buckets
    Data_Structures.Fixed_Univ_Map_Specs_Imp
    Data_Structures.Fixed_Univ_Buckets_Specs_Imp
    Data_Structures.Fixed_Univ_Set_Iterate_Imp
begin

section \<open>Imperative Label Maps with Buckets\<close>

text \<open>The label map with buckets of theory \<open>Push_Relabel_Label_Buckets\<close>, now on an imperative
      label array, imperative buckets and a reference holding the bound on the bucket numbers in
      use. All operations work in place. The gap enumeration walks the buckets \<open>k + 1, ..., d\<close>
      for the bound \<open>d\<close> read before the walk and takes the elements of each bucket one by one;
      it removes nothing itself, since the step applied to an element lifts its label to at least
      the number of vertices, which removes it from its bucket.\<close>

locale label_buckets_imp_code =
  fixes N :: nat
    and lm_get_imp :: "'lmi \<Rightarrow> 'v \<Rightarrow> nat Heap"
    and lm_upd_imp :: "'lmi \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> unit Heap"
    and buckets_insert_imp :: "'bi \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> unit Heap"
    and buckets_remove_imp :: "'bi \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> unit Heap"
    and buckets_pick_imp :: "'bi \<Rightarrow> nat \<Rightarrow> 'v option Heap"
begin

partial_function (heap) lower_imp :: "'bi \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "lower_imp Bi d =
     (if d = 0 then return 0
      else do {
        p \<leftarrow> buckets_pick_imp Bi d;
        case p of None \<Rightarrow> lower_imp Bi (d - 1) | Some _ \<Rightarrow> return d })"

definition "lb_get_imp = (\<lambda> (Lai, Bi, Dr) v. lm_get_imp Lai v)"

definition "lb_upd_imp = (\<lambda> (Lai, Bi, Dr) v k'. do {
   k \<leftarrow> lm_get_imp Lai v;
   (if k < N then buckets_remove_imp Bi v k else return ());
   (if k' < N then buckets_insert_imp Bi v k' else return ());
   d \<leftarrow> !Dr;
   d' \<leftarrow> lower_imp Bi (if k' < N then max d k' else d);
   Dr := d';
   lm_upd_imp Lai v k' })"

partial_function (heap) drain_imp :: "'bi \<Rightarrow> nat \<Rightarrow> ('v \<Rightarrow> unit Heap) \<Rightarrow> unit Heap" where
  "drain_imp Bi j g_imp = do {
     p \<leftarrow> buckets_pick_imp Bi j;
     case p of None \<Rightarrow> return () | Some v \<Rightarrow> do { g_imp v; drain_imp Bi j g_imp } }"

partial_function (heap) gap_walk_imp :: "'bi \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('v \<Rightarrow> unit Heap) \<Rightarrow> unit Heap" where
  "gap_walk_imp Bi j m g_imp =
     (if m = 0 then return ()
      else do { drain_imp Bi j g_imp; gap_walk_imp Bi (Suc j) (m - 1) g_imp })"

definition "lb_gap_fold_imp = (\<lambda> (Lai, Bi, Dr) k g_imp. do {
   d \<leftarrow> !Dr;
   gap_walk_imp Bi (Suc k) (d - k) g_imp })"

text \<open>Initialisation, on a label array holding the initial labels and empty buckets, by a given
      imperative vertex fold.\<close>

definition "lb_init_imp vfold_imp = (\<lambda> (Lai, Bi, Dr). do {
   vfold_imp (\<lambda> v. buckets_insert_imp Bi v 0);
   Dr := 0 })"

end

locale label_buckets_imp =
  label_buckets_correct V N lm_invar lm_upd lm_get buckets_invar buckets_abstract buckets_empty
    buckets_insert buckets_remove buckets_pick buckets_move lm_init bucket_vertex_fold +
  label_buckets_imp_code N lm_get_imp lm_upd_imp buckets_insert_imp buckets_remove_imp
    buckets_pick_imp +
  label_array_imp: fixed_univ_map_imp V lm_invar lm_upd lm_get "id :: nat \<Rightarrow> nat" lm_assn
    lm_upd_imp lm_get_imp +
  bucket_imp: fixed_univ_buckets_imp V "{..<N}" buckets_invar buckets_abstract buckets_empty
    buckets_insert buckets_remove buckets_pick buckets_move buckets_assn buckets_empty_imp
    buckets_insert_imp buckets_remove_imp buckets_pick_imp buckets_move_imp
  for V :: "'v::heap set" and N lm_invar lm_upd lm_get buckets_invar buckets_abstract buckets_empty
    buckets_insert buckets_remove buckets_pick buckets_move lm_init bucket_vertex_fold
    and lm_get_imp :: "'lmi \<Rightarrow> 'v \<Rightarrow> nat Heap" and lm_upd_imp
    and buckets_insert_imp :: "'bi \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> unit Heap" and buckets_remove_imp
    buckets_pick_imp lm_assn buckets_assn buckets_empty_imp buckets_move_imp
begin

definition "lb_assn = (\<lambda> (L, B, d) (Lai, Bi, Dr). lm_assn L Lai * buckets_assn B Bi * Dr \<mapsto>\<^sub>r d)"

lemma lb_assn_tuple: "lb_assn (L, B, d) (Lai, Bi, Dr) = lm_assn L Lai * buckets_assn B Bi * Dr \<mapsto>\<^sub>r d"
  by (simp add: lb_assn_def)

lemma lower_imp_rule:
  assumes "buckets_invar B" "d < N"
  shows "<buckets_assn B Bi> lower_imp Bi d <\<lambda>r. buckets_assn B Bi * \<up>(r = lower B d)>"
  using assms(2)
proof(induction d)
  case 0
  show ?case
    by (subst lower_imp.simps) sep_auto
next
  case (Suc d)
  thus ?case
    using assms(1)
    by (subst lower_imp.simps) (sep_auto heap: Suc.IH[OF Suc_lessD[OF Suc.prems]] split: option.splits)
qed

lemma lb_get_imp_rule:
  assumes "lb_invar A" "v \<in> V"
  shows "<lb_assn A Ai> lb_get_imp Ai v <\<lambda>x. lb_assn A Ai * \<up>(id x = lb_get A v)>"
  using assms
  unfolding lb_get_imp_def lb_get_def
  by (cases A rule: prod_cases3, cases Ai rule: prod_cases3) (sep_auto simp: lb_assn_tuple lb_invar_def)

lemma lb_upd_imp_rule:
  assumes "lb_invar A" "v \<in> V"
  shows "<lb_assn A Ai> lb_upd_imp Ai v k' <\<lambda>_. lb_assn (lb_upd A v (id k')) Ai>"
proof-
  obtain L B d Lai Bi Dr where A: "A = (L, B, d)" and Ai: "Ai = (Lai, Bi, Dr)"
    by (cases A rule: prod_cases3, cases Ai rule: prod_cases3) auto
  note st = lb_upd_steps[OF assms(1)[unfolded A] assms(2)]
  define k where "k = lm_get L v"
  define B1 where "B1 = (if k < N then buckets_remove B v k else B)"
  define B2 where "B2 = (if k' < N then buckets_insert B1 v k' else B1)"
  have b: "buckets_invar B1" "buckets_abstract B1 v = None"
          "k < N \<Longrightarrow> buckets_remove B v k = B1" "\<not> k < N \<Longrightarrow> B = B1"
          "k' < N \<Longrightarrow> buckets_insert B1 v k' = B2" "\<not> k' < N \<Longrightarrow> B1 = B2"
    using st(6,7)[folded k_def, folded B1_def]
    by (simp_all add: B1_def B2_def)
  note r3 = lower_imp_rule[OF st(8,10)[of k', folded k_def, folded B1_def, folded B2_def]]
  note lk = label_array_imp.fixed_univ_map_lookup_rule[OF st(2) assms(2), of Lai, unfolded id_apply, folded k_def]
   and lu = label_array_imp.fixed_univ_map_upd_rule[OF st(2) assms(2), of Lai k', unfolded id_apply]
  show ?thesis
  proof(cases "k' < N")
    case True
    note r = r3[unfolded if_P[OF True]]
    show ?thesis
      using st(3) st(5)[folded k_def] b(1,2) assms(2) True
      unfolding A Ai lb_assn_tuple lb_upd_imp_def prod.case
                st(1)[of k', folded k_def, folded B1_def, folded B2_def] id_def
      by (sep_auto heap: lk r lu simp: b(3-6))
  next
    case False
    note r = r3[unfolded if_not_P[OF False]]
    show ?thesis
      using st(3) st(5)[folded k_def] b(1,2) assms(2) False
      unfolding A Ai lb_assn_tuple lb_upd_imp_def prod.case
                st(1)[of k', folded k_def, folded B1_def, folded B2_def] id_def
      by (sep_auto heap: lk r lu simp: b(3-6))

  qed
qed

lemma lb_fixed_univ_map_imp:
  "fixed_univ_map_imp V lb_invar lb_upd lb_get (id :: nat \<Rightarrow> nat) lb_assn lb_upd_imp lb_get_imp"
  by (intro fixed_univ_map_imp.intro lb_fixed_univ_map fixed_univ_map_basic_imp.intro
            fixed_univ_map_imp_axioms.intro lb_get_imp_rule lb_upd_imp_rule)

subsection \<open>The Gap Enumeration\<close>

lemma pick_lb_rule:
  assumes "Li = (Lai, Bi, Dr)" "buckets_invar B" "j < N"
  shows "<lb_assn (L, B, d) Li> buckets_pick_imp Bi j
         <\<lambda>p. lb_assn (L, B, d) Li * \<up>(p = buckets_pick B j)>"
  using assms(2,3) unfolding assms(1) lb_assn_tuple
  by sep_auto

lemma bound_lb_rule:
  assumes "Li = (Lai, Bi, Dr)"
  shows "<lb_assn (L, B, d) Li> !Dr <\<lambda>x. lb_assn (L, B, d) Li * \<up>(x = d)>"
  unfolding assms(1) lb_assn_tuple
  by sep_auto

text \<open>A visited vertex \<open>v\<close> lies in bucket \<open>j\<close>; the step lifts its label to at least the
      number of vertices, which takes it out of its bucket and leaves the other buckets unchanged.\<close>

lemma lb_upd_lift:
  assumes "lb_invar (L, B, d)" "v \<in> V" "lm_get L v < N" "N \<le> k'"
  shows "lb_upd (L, B, d) v k' =
         (lm_upd L v k', buckets_remove B v (lm_get L v), lower (buckets_remove B v (lm_get L v)) d)"
  using assms lb_upd_steps(1)[where k' = k']
  by simp

lemma lb_invar_buckets: "lb_invar (L, B, d) \<Longrightarrow> buckets_invar B"
  by (simp add: lb_invar_def)

lemma lb_pick_props:
  assumes "lb_invar (L, B, d)" "j < N" "buckets_pick B j = Some v"
  shows "buckets_abstract B v = Some j" "v \<in> V" "lm_get L v = j"
proof-
  note bi = lb_invar_buckets[OF assms(1)]
  show "buckets_abstract B v = Some j"
    using bi assms(2,3) bucket.buckets_pick(2)[of B j v]
    by simp
  thus "v \<in> V" "lm_get L v = j"
    using bi assms(1) bucket.buckets_universe[of B v j]
    by (auto simp: lb_invar_def split: if_splits)
qed

lemma drain_imp_rule:
  assumes g: "\<And> acc v. \<lbrakk>lb_invar (fst acc); v \<in> V; k < lb_get (fst acc) v;
                         lb_get (fst acc) v < card V\<rbrakk> \<Longrightarrow>
          (\<exists> k'. card V \<le> k' \<and> fst (g acc v) = lb_upd (fst acc) v k') \<and>
          <lb_assn (fst acc) Li * R (snd acc)> g_imp v
          <\<lambda>_. lb_assn (fst (g acc v)) Li * R (snd (g acc v))>"
      and Li: "Li = (Lai, Bi, Dr)"
      and "lb_invar (L, B, d)" "k < j" "j < N" "card {x. buckets_abstract B x = Some j} \<le> n"
  shows "(\<exists> L' d'. fst (snd (drain B j n g ((L, B, d), r))) =
                    (L', fst (drain B j n g ((L, B, d), r)), d') \<and>
                  lb_invar (L', fst (drain B j n g ((L, B, d), r)), d')) \<and>
         <lb_assn (L, B, d) Li * R r> drain_imp Bi j g_imp
         <\<lambda>_. lb_assn (fst (snd (drain B j n g ((L, B, d), r)))) Li *
              R (snd (snd (drain B j n g ((L, B, d), r))))>"
  using assms(3-6)
proof(induction n arbitrary: L B d r)
  case 0
  note bi = lb_invar_buckets[OF 0(1)]
  have "buckets_pick B j = None"
    using 0(3,4) bi bucket.buckets_pick(1)[of B j] bucket_finite[of B j]
    by auto
  thus ?case
    using 0(1)
    by (intro conjI, simp, subst drain_imp.simps) (sep_auto heap: pick_lb_rule[OF Li bi 0(3)])
next
  case (Suc n)
  note bi = lb_invar_buckets[OF Suc.prems(1)]
  show ?case
  proof(cases "buckets_pick B j")
    case None
    show ?thesis
      using Suc.prems(1)
      by (intro conjI, simp add: None, subst drain_imp.simps)
         (sep_auto heap: pick_lb_rule[OF Li bi Suc.prems(3)] simp: None)
  next
    case (Some v)
    note vj = lb_pick_props[OF Suc.prems(1,3) Some]
    note gv = g[of "((L, B, d), r)" v, unfolded fst_conv snd_conv lb_get_def prod.case vj(3),
                OF Suc.prems(1) vj(2) Suc.prems(2) Suc.prems(3)[unfolded N]]
    obtain k' where k': "card V \<le> k'" "fst (g ((L, B, d), r) v) = lb_upd (L, B, d) v k'"
      using gv
      by (elim conjE exE) (simp add: that)
    define B1 where "B1 = buckets_remove B v j"
    obtain r' where g1: "g ((L, B, d), r) v = ((lm_upd L v k', B1, lower B1 d), r')"
      using k' Suc.prems(1,3) vj(2,3) lb_upd_lift[of L B d v k']
      by (cases "g ((L, B, d), r) v") (auto simp add: N B1_def)
    have "lb_invar (lm_upd L v k', B1, lower B1 d)" "card {x. buckets_abstract B1 x = Some j} \<le> n"
      using Suc.prems(1,4) vj(1,2) k'(2) g1 bi lb_upd_props(1)[of "(L, B, d)" v k'] bucket_finite[of B j]
      by (simp_all add: B1_def bucket_level_remove card_Diff_singleton)
    note IH = Suc.IH[OF this(1) Suc.prems(2,3) this(2), of r']
    show ?thesis
      using conjunct2[OF gv] IH
      unfolding drain.simps(2) Some option.case B1_def[symmetric] g1
      by (intro conjI, simp, subst drain_imp.simps)
         (sep_auto heap: pick_lb_rule[OF Li bi Suc.prems(3)] simp: Some)
  qed
qed

lemma gap_walk_imp_rule:
  assumes g: "\<And> acc v. \<lbrakk>lb_invar (fst acc); v \<in> V; k < lb_get (fst acc) v;
                         lb_get (fst acc) v < card V\<rbrakk> \<Longrightarrow>
          (\<exists> k'. card V \<le> k' \<and> fst (g acc v) = lb_upd (fst acc) v k') \<and>
          <lb_assn (fst acc) Li * R (snd acc)> g_imp v
          <\<lambda>_. lb_assn (fst (g acc v)) Li * R (snd (g acc v))>"
      and Li: "Li = (Lai, Bi, Dr)"
      and "lb_invar (L, B, d)" "k < j" "0 < m \<Longrightarrow> j + m \<le> N"
  shows "<lb_assn (L, B, d) Li * R r> gap_walk_imp Bi j m g_imp
         <\<lambda>_. lb_assn (fst (gap_walk B j m g ((L, B, d), r))) Li *
              R (snd (gap_walk B j m g ((L, B, d), r)))>"
  using assms(3-5)
proof(induction m arbitrary: j L B d r)
  case 0
  show ?case
    by (subst gap_walk_imp.simps) sep_auto
next
  case (Suc m)
  have "j < N"
    using Suc.prems(3)
    by simp
  note dr = drain_imp_rule[OF g Li Suc.prems(1,2) this bucket_card_le[OF lb_invar_buckets[OF Suc.prems(1)]], of r]
  obtain L' d' where e:
    "fst (snd (drain B j N g ((L, B, d), r))) = (L', fst (drain B j N g ((L, B, d), r)), d')"
    "lb_invar (L', fst (drain B j N g ((L, B, d), r)), d')"
    using dr
    by blast
  define B' where "B' = fst (drain B j N g ((L, B, d), r))"
  define r' where "r' = snd (snd (drain B j N g ((L, B, d), r)))"
  have "snd (drain B j N g ((L, B, d), r)) = ((L', B', d'), r')"
    using e(1)
    by (simp add: prod_eq_iff B'_def r'_def)
  hence gw: "gap_walk B j (Suc m) g ((L, B, d), r) = gap_walk B' (Suc j) m g ((L', B', d'), r')"
    by (simp add: case_prod_beta B'_def)
  have "0 < m \<Longrightarrow> Suc j + m \<le> N"
    using Suc.prems(3)
    by simp
  note IH = Suc.IH[OF e(2)[folded B'_def] less_SucI[OF Suc.prems(2)] this, of r']
  have t: "<lb_assn (L, B, d) Li * R r> drain_imp Bi j g_imp <\<lambda>_. lb_assn (L', B', d') Li * R r'>"
    using conjunct2[OF dr] unfolding e(1)[folded B'_def] r'_def[symmetric] .
  show ?case
    unfolding gw
    by (subst gap_walk_imp.simps) (sep_auto heap: t IH)
qed


text \<open>The rule required from the gap enumeration of the label map by the generic algorithm.\<close>

lemma lb_gap_fold_imp_rule:
  assumes "lb_invar l"
      and g: "\<And> acc v. \<lbrakk>lb_invar (fst acc); v \<in> V; k < lb_get (fst acc) v;
                         lb_get (fst acc) v < card V\<rbrakk> \<Longrightarrow>
          (\<exists> k'. card V \<le> k' \<and> fst (g acc v) = lb_upd (fst acc) v k') \<and>
          <lb_assn (fst acc) Li * R (snd acc)> g_imp v
          <\<lambda>_. lb_assn (fst (g acc v)) Li * R (snd (g acc v))>"
  shows "<lb_assn l Li * R r> lb_gap_fold_imp Li k g_imp
         <\<lambda>_. lb_assn (fst (lb_gap_fold l k g (l, r))) Li * R (snd (lb_gap_fold l k g (l, r)))>"
proof-
  obtain L B d Lai Bi Dr where l: "l = (L, B, d)" and Li: "Li = (Lai, Bi, Dr)"
    by (cases l rule: prod_cases3, cases Li rule: prod_cases3) auto
  have m: "0 < d - k \<Longrightarrow> Suc k + (d - k) \<le> N"
    using assms(1)
    by (simp add: lb_invar_def l)
  note gw = gap_walk_imp_rule[OF g Li assms(1)[unfolded l] lessI m, of r]
  have c: "lb_gap_fold_imp Li k g_imp = do { x \<leftarrow> !Dr; gap_walk_imp Bi (Suc k) (x - k) g_imp }"
    by (simp add: Li lb_gap_fold_imp_def)
  show ?thesis
    unfolding c l lb_gap_fold_def prod.case
    by (sep_auto heap: bound_lb_rule[OF Li] gw)
qed

subsection \<open>Initialisation\<close>

text \<open>The initialisation is given an imperative vertex fold implementing
      @{term bucket_vertex_fold}, whose own data are described by @{term M}.\<close>

lemma lb_init_imp_rule:
  assumes "set_fold_imp_rule V M bucket_vertex_fold vfold_imp"
  shows "<M * (lm_assn lm_init Lai * buckets_assn buckets_empty Bi * Dr \<mapsto>\<^sub>r d0)>
           lb_init_imp vfold_imp (Lai, Bi, Dr)
         <\<lambda>_. M * lb_assn lb_init (Lai, Bi, Dr)>"
proof-
  define P where
    "P = (\<lambda> W B. buckets_invar B \<and>
                  buckets_abstract B = (\<lambda> x. if x \<in> W then Some (0::nat) else None))"
  have step: "P (insert v W) (buckets_insert a v 0) \<and>
              <buckets_assn a Bi> buckets_insert_imp Bi v 0 <\<lambda>_. buckets_assn (buckets_insert a v 0) Bi>"
    if a: "P W a" "W \<subseteq> V" "v \<in> V" "v \<notin> W" for W a v
  proof-
    note n = N_pos[folded lessThan_iff]
    have an: "buckets_invar a" "buckets_abstract a v = None"
      using a(1,4)
      by (simp_all add: P_def)
    show ?thesis
      using an a(1,3) n bucket.buckets_insert[of a v 0] bucket_imp.buckets_insert_rule[of a v 0]
      by (auto simp add: P_def fun_eq_iff)
  qed
  have "P {} buckets_empty"
    using bucket.buckets_empty
    by (simp add: P_def)
  note f = set_fold_imp_ruleD[OF assms, where g = "\<lambda> B v. buckets_insert B v 0"
             and g_imp = "\<lambda> v. buckets_insert_imp Bi v 0" and P = P and R = "\<lambda> B. buckets_assn B Bi",
             OF this step]
  show ?thesis
    unfolding lb_init_imp_def lb_init_def prod.case lb_assn_tuple
    by (sep_auto heap: f)
qed
end

end
