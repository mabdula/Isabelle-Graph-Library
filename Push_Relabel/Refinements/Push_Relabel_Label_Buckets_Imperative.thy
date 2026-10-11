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
  have IH: "<buckets_assn B Bi> lower_imp Bi d <\<lambda>r. buckets_assn B Bi * \<up>(r = lower B d)>"
    using Suc by simp
  show ?case
    using Suc.prems assms(1)
    by (subst lower_imp.simps) (sep_auto heap: IH split: option.splits)
qed

lemma lb_get_imp_rule:
  assumes "lb_invar A" "v \<in> V"
  shows "<lb_assn A Ai> lb_get_imp Ai v <\<lambda>x. lb_assn A Ai * \<up>(id x = lb_get A v)>"
proof-
  obtain L B d where A: "A = (L, B, d)"
    by (cases A) auto
  obtain Lai Bi Dr where Ai: "Ai = (Lai, Bi, Dr)"
    by (cases Ai) auto
  have "lm_invar L"
    using assms(1) by (simp add: lb_invar_def A)
  thus ?thesis
    using assms(2) unfolding A Ai lb_assn_tuple lb_get_imp_def lb_get_def
    by sep_auto
qed

lemma lb_upd_imp_rule:
  assumes "lb_invar A" "v \<in> V"
  shows "<lb_assn A Ai> lb_upd_imp Ai v k' <\<lambda>_. lb_assn (lb_upd A v (id k')) Ai>"
proof-
  obtain L B d where A: "A = (L, B, d)"
    by (cases A) auto
  obtain Lai Bi Dr where Ai: "Ai = (Lai, Bi, Dr)"
    by (cases Ai) auto
  note st = lb_upd_steps[OF assms(1)[unfolded A] assms(2)]
  define k where "k = lm_get L v"
  define B1 where "B1 = (if k < N then buckets_remove B v k else B)"
  define B2 where "B2 = (if k' < N then buckets_insert B1 v k' else B1)"
  have b1: "buckets_invar B1" "buckets_abstract B1 v = None"
    using st(6,7)[folded k_def, folded B1_def] by simp_all
  have e1: "k < N \<Longrightarrow> buckets_remove B v k = B1" "\<not> k < N \<Longrightarrow> B = B1"
    by (simp_all add: B1_def)
  have e2: "k' < N \<Longrightarrow> buckets_insert B1 v k' = B2" "\<not> k' < N \<Longrightarrow> B1 = B2"
    by (simp_all add: B2_def)
  note r3 = lower_imp_rule[OF st(8,10)[of k', folded k_def, folded B1_def, folded B2_def]]
  have lk: "<lm_assn L Lai> lm_get_imp Lai v <\<lambda>x. lm_assn L Lai * \<up>(x = k)>"
    using label_array_imp.fixed_univ_map_lookup_rule[OF st(2) assms(2), of Lai] by (simp add: k_def)
  have lu: "<lm_assn L Lai> lm_upd_imp Lai v k' <\<lambda>_. lm_assn (lm_upd L v k') Lai>"
    using label_array_imp.fixed_univ_map_upd_rule[OF st(2) assms(2), of Lai k'] by simp
  show ?thesis
  proof(cases "k' < N")
    case True
    have r: "<buckets_assn B2 Bi> lower_imp Bi (max d k')
             <\<lambda>r. buckets_assn B2 Bi * \<up>(r = lower B2 (max d k'))>"
      using r3 True by simp
    show ?thesis
      using st(3) st(5)[folded k_def] b1 assms(2) True
      unfolding A Ai lb_assn_tuple lb_upd_imp_def prod.case
                st(1)[of k', folded k_def, folded B1_def, folded B2_def] id_def
      by (sep_auto heap: lk r lu simp: e1 e2)
  next
    case False
    have r: "<buckets_assn B2 Bi> lower_imp Bi d <\<lambda>r. buckets_assn B2 Bi * \<up>(r = lower B2 d)>"
      using r3 False by simp
    show ?thesis
      using st(3) st(5)[folded k_def] b1 assms(2) False
      unfolding A Ai lb_assn_tuple lb_upd_imp_def prod.case
                st(1)[of k', folded k_def, folded B1_def, folded B2_def] id_def
      by (sep_auto heap: lk r lu simp: e1 e2)
  qed
qed

lemma lb_fixed_univ_map_imp:
  "fixed_univ_map_imp V lb_invar lb_upd lb_get (id :: nat \<Rightarrow> nat) lb_assn lb_upd_imp lb_get_imp"
  by (intro fixed_univ_map_imp.intro lb_fixed_univ_map fixed_univ_map_imp_axioms.intro
            lb_get_imp_rule lb_upd_imp_rule)

subsection \<open>The Gap Enumeration\<close>

lemma pick_lb_rule:
  assumes "Li = (Lai, Bi, Dr)" "buckets_invar B" "j < N"
  shows "<lb_assn (L, B, d) Li> buckets_pick_imp Bi j
         <\<lambda>p. lb_assn (L, B, d) Li * \<up>(p = buckets_pick B j)>"
  using assms(2,3) unfolding assms(1) lb_assn_tuple by sep_auto

lemma bound_lb_rule:
  assumes "Li = (Lai, Bi, Dr)"
  shows "<lb_assn (L, B, d) Li> !Dr <\<lambda>x. lb_assn (L, B, d) Li * \<up>(x = d)>"
  unfolding assms(1) lb_assn_tuple by sep_auto

text \<open>A visited vertex \<open>v\<close> lies in bucket \<open>j\<close>; the step lifts its label to at least the number
      of vertices, which takes it out of its bucket and leaves the other buckets unchanged.\<close>

lemma lb_upd_lift:
  assumes "lb_invar (L, B, d)" "v \<in> V" "lm_get L v < N" "N \<le> k'"
  shows "lb_upd (L, B, d) v k' =
         (lm_upd L v k', buckets_remove B v (lm_get L v), lower (buckets_remove B v (lm_get L v)) d)"
  using lb_upd_steps(1)[OF assms(1,2), of k'] assms(3,4) by simp

lemma drain_imp_rule:
  assumes g: "\<And> acc v. \<lbrakk>lb_invar (fst acc); v \<in> V; k < lb_get (fst acc) v;
                         lb_get (fst acc) v < card V\<rbrakk> \<Longrightarrow>
          (\<exists> k'. card V \<le> k' \<and> fst (g acc v) = lb_upd (fst acc) v k') \<and>
          <lb_assn (fst acc) Li * R (snd acc)> g_imp v
          <\<lambda>_. lb_assn (fst (g acc v)) Li * R (snd (g acc v))>"
      and Li: "Li = (Lai, Bi, Dr)"
      and "lb_invar (L, B, d)" "k < j" "j < N" "card {x. buckets_abstract B x = Some j} \<le> n"
  shows "(\<exists> L' d'. fst (snd (drain B j n g ((L, B, d), r))) = (L', fst (drain B j n g ((L, B, d), r)), d') \<and>
                  lb_invar (L', fst (drain B j n g ((L, B, d), r)), d')) \<and>
         <lb_assn (L, B, d) Li * R r> drain_imp Bi j g_imp
         <\<lambda>_. lb_assn (fst (snd (drain B j n g ((L, B, d), r)))) Li *
              R (snd (snd (drain B j n g ((L, B, d), r))))>"
  using assms(3-6)
proof(induction n arbitrary: L B d r)
  case 0
  have bi: "buckets_invar B"
    using 0(1) by (simp add: lb_invar_def)
  have fin: "finite {x. buckets_abstract B x = Some j}"
    using bucket.buckets_universe[OF bi] V_finite by (auto intro: finite_subset)
  have "\<forall> x. buckets_abstract B x \<noteq> Some j"
    using 0(4) card_0_eq[OF fin] by auto
  hence pk: "buckets_pick B j = None"
    using bucket.buckets_pick(1)[OF bi] 0(3) by simp
  show ?case
    using 0(1)
    by (intro conjI, simp, subst drain_imp.simps)
       (sep_auto heap: pick_lb_rule[OF Li bi 0(3)] simp: pk)
next
  case (Suc n)
  have bi: "buckets_invar B"
    using Suc.prems(1) by (simp add: lb_invar_def)
  show ?case
  proof(cases "buckets_pick B j")
    case None
    show ?thesis
      using Suc.prems(1)
      by (intro conjI, simp add: None, subst drain_imp.simps)
         (sep_auto heap: pick_lb_rule[OF Li bi Suc.prems(3)] simp: None)
  next
    case (Some v)
    have vj: "buckets_abstract B v = Some j"
      using bucket.buckets_pick(2)[OF bi _ Some] Suc.prems(3) by simp
    have v: "v \<in> V"
      using bucket.buckets_universe[OF bi vj] by simp
    have lv: "lm_get L v = j"
      using Suc.prems(1) v vj by (auto simp add: lb_invar_def split: if_splits)
    define acc where "acc = ((L, B, d), r)"
    have lg: "lb_get (fst acc) v = j"
      using lv by (simp add: acc_def lb_get_def)
    have pre: "lb_invar (fst acc)" "k < lb_get (fst acc) v" "lb_get (fst acc) v < card V"
      using Suc.prems(1,2,3) lg by (simp_all add: acc_def N)
    obtain k' where k': "card V \<le> k'" "fst (g acc v) = lb_upd (fst acc) v k'"
      using conjunct1[OF g[OF pre(1) v pre(2,3)]] by blast
    note gt = conjunct2[OF g[OF pre(1) v pre(2,3)]]
    define L1 where "L1 = lm_upd L v k'"
    define B1 where "B1 = buckets_remove B v j"
    define d1 where "d1 = lower B1 d"
    have g1: "fst (g acc v) = (L1, B1, d1)"
      using k' lb_upd_lift[OF Suc.prems(1) v, of k'] lv Suc.prems(3)
      by (simp add: acc_def N L1_def B1_def d1_def)
    have inv1: "lb_invar (L1, B1, d1)"
      using lb_upd_props(1)[OF pre(1) v, of k'] k'(2) g1 by simp
    have ab1: "buckets_abstract B1 = fun_upd (buckets_abstract B) v None"
      using bucket.buckets_remove(2)[OF bi vj] by (simp add: B1_def)
    have "{x. buckets_abstract B1 x = Some j} = {x. buckets_abstract B x = Some j} - {v}"
      using ab1 by auto
    moreover have "finite {x. buckets_abstract B x = Some j}"
      using bucket.buckets_universe[OF bi] V_finite by (auto intro: finite_subset)
    ultimately have c1: "card {x. buckets_abstract B1 x = Some j} \<le> n"
      using Suc.prems(4) vj by (simp add: card_Diff_singleton)
    note IH = Suc.IH[OF inv1 Suc.prems(2,3) c1, of "snd (g acc v)"]
    have gv: "g acc v = ((L1, B1, d1), snd (g acc v))"
      using g1 by (metis prod.collapse)
    have dr: "drain B j (Suc n) g ((L, B, d), r) = drain B1 j n g ((L1, B1, d1), snd (g acc v))"
      using Some gv by (simp add: acc_def B1_def)
    show ?thesis
      unfolding dr
    proof(intro conjI)
      show "\<exists> L' d'. fst (snd (drain B1 j n g ((L1, B1, d1), snd (g acc v)))) =
                     (L', fst (drain B1 j n g ((L1, B1, d1), snd (g acc v))), d') \<and>
                     lb_invar (L', fst (drain B1 j n g ((L1, B1, d1), snd (g acc v))), d')"
        using conjunct1[OF IH] .
      show "<lb_assn (L, B, d) Li * R r> drain_imp Bi j g_imp
            <\<lambda>_. lb_assn (fst (snd (drain B1 j n g ((L1, B1, d1), snd (g acc v))))) Li *
                 R (snd (snd (drain B1 j n g ((L1, B1, d1), snd (g acc v)))))>"
        using gt conjunct2[OF IH] unfolding acc_def g1
        by (subst drain_imp.simps)
           (sep_auto heap: pick_lb_rule[OF Li bi Suc.prems(3)] simp: Some g1[unfolded acc_def])
    qed
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
  have j: "j < N"
    using Suc.prems(3) by simp
  have bi: "buckets_invar B"
    using Suc.prems(1) by (simp add: lb_invar_def)
  have cj: "card {x. buckets_abstract B x = Some j} \<le> N"
    using bucket.buckets_universe[OF bi] V_finite by (auto intro!: card_mono simp add: N)
  note dr = drain_imp_rule[OF g Li Suc.prems(1,2) j cj, of r]
  obtain L' d' where e:
    "fst (snd (drain B j N g ((L, B, d), r))) = (L', fst (drain B j N g ((L, B, d), r)), d')"
    "lb_invar (L', fst (drain B j N g ((L, B, d), r)), d')"
    using conjunct1[OF dr] by blast
  define B' where "B' = fst (drain B j N g ((L, B, d), r))"
  define r' where "r' = snd (snd (drain B j N g ((L, B, d), r)))"
  have sd: "snd (drain B j N g ((L, B, d), r)) = ((L', B', d'), r')"
    using e(1) by (metis B'_def r'_def prod.collapse)
  have m: "0 < m \<Longrightarrow> Suc j + m \<le> N"
    using Suc.prems(3) by simp
  note IH = Suc.IH[OF e(2)[folded B'_def] less_SucI[OF Suc.prems(2)] m, of r']
  have gw: "gap_walk B j (Suc m) g ((L, B, d), r) = gap_walk B' (Suc j) m g ((L', B', d'), r')"
    using sd by (simp add: case_prod_beta B'_def)
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
  obtain L B d where l: "l = (L, B, d)"
    by (cases l) auto
  obtain Lai Bi Dr where Li: "Li = (Lai, Bi, Dr)"
    by (cases Li) auto
  have "d < N"
    using assms(1) by (simp add: lb_invar_def l)
  hence m: "0 < d - k \<Longrightarrow> Suc k + (d - k) \<le> N"
    by simp
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
    "P = (\<lambda> W B. buckets_invar B \<and> buckets_abstract B = (\<lambda> x. if x \<in> W then Some (0::nat) else None))"
  have step: "P (insert v W) (buckets_insert a v 0) \<and>
              <buckets_assn a Bi> buckets_insert_imp Bi v 0 <\<lambda>_. buckets_assn (buckets_insert a v 0) Bi>"
    if a: "P W a" "W \<subseteq> V" "v \<in> V" "v \<notin> W" for W a v
  proof-
    have n: "(0::nat) \<in> {..<N}"
      using N_pos by simp
    have an: "buckets_invar a" "buckets_abstract a v = None"
      using a(1,4) by (simp_all add: P_def)
    show ?thesis
      using bucket.buckets_insert[OF an(1) a(3) n an(2)]
            bucket_imp.buckets_insert_rule[OF an(1) a(3) n an(2)] a(1)
      by (auto simp add: P_def fun_eq_iff)
  qed
  have p0: "P {} buckets_empty"
    using bucket.buckets_empty by (simp add: P_def)
  note f = set_fold_imp_ruleD[OF assms, where g = "\<lambda> B v. buckets_insert B v 0"
             and g_imp = "\<lambda> v. buckets_insert_imp Bi v 0" and P = P and R = "\<lambda> B. buckets_assn B Bi",
             OF p0 step]
  show ?thesis
    unfolding lb_init_imp_def lb_init_def prod.case lb_assn_tuple
    by (sep_auto heap: f)
qed
end

end
