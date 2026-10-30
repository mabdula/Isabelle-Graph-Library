theory Push_Relabel_Label_Buckets
  imports
    Data_Structures.Fixed_Univ_Map_Specs
    Data_Structures.Fixed_Univ_Buckets_Specs
    AI_Provenance.Provenance
begin

provenance ai


section \<open>Label Maps with Buckets for the Gap Heuristic\<close>

text \<open>A label map over the vertices @{term V} that also keeps every vertex with a label below
      @{term N} (the number of vertices) in the bucket of its label, together with an upper bound
      \<open>d\<close> on the bucket numbers in use. Updating a label moves the vertex between buckets, raises
      the bound if necessary and lowers it while its bucket is empty. The vertices with labels
      strictly between \<open>k\<close> and @{term N} can thus be enumerated by walking the buckets
      \<open>k + 1, ..., d\<close>, which is the gap enumeration of the generic push-relabel algorithm.
      Everything is generic in the underlying label array and buckets.\<close>

locale \<^marker>\<open>provenance ai_human\<close> label_buckets =
  label_array: fixed_univ_map V lm_invar lm_upd lm_get +
  bucket: fixed_univ_buckets V "{..<N}" buckets_invar buckets_abstract buckets_empty
      buckets_insert buckets_remove buckets_pick buckets_move
  for V :: "'v set"
  and N :: nat
  and lm_invar :: "'lm \<Rightarrow> bool"
  and lm_upd :: "'lm \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> 'lm"
  and lm_get :: "'lm \<Rightarrow> 'v \<Rightarrow> nat"
  and buckets_invar :: "'b \<Rightarrow> bool"
  and buckets_abstract :: "'b \<Rightarrow> 'v \<Rightarrow> nat option"
  and buckets_empty buckets_insert buckets_remove buckets_pick buckets_move +
  fixes lm_init :: 'lm
  and bucket_vertex_fold :: "('b \<Rightarrow> 'v \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b"
begin

text \<open>Lowering the bound while its bucket is empty.\<close>

fun \<^marker>\<open>provenance ai_human\<close> lower where
  "lower B 0 = 0"
| "lower B (Suc d) = (case buckets_pick B (Suc d) of None \<Rightarrow> lower B d | Some _ \<Rightarrow> Suc d)"

definition "lb_get = (\<lambda> (L, B, d) v. lm_get L v)"

definition "lb_upd = (\<lambda> (L, B, d) v k'.
  (let k = lm_get L v;
       B1 = (if k < N then buckets_remove B v k else B);
       B2 = (if k' < N then buckets_insert B1 v k' else B1);
       d1 = (if k' < N then max d k' else d)
   in (lm_upd L v k', B2, lower B2 d1)))"

definition "lb_init = (lm_init, bucket_vertex_fold (\<lambda> B v. buckets_insert B v 0) buckets_empty, 0)"

text \<open>Taking the elements of bucket \<open>j\<close> one by one; the fuel is the number of vertices. The
      buckets without the drained ones are returned as well: the walk continues on them, as the
      walk in place does.\<close>

fun \<^marker>\<open>provenance ai_human\<close> drain where
  "drain B j 0 g acc = (B, acc)"
| "drain B j (Suc n) g acc =
     (case buckets_pick B j of None \<Rightarrow> (B, acc)
      | Some v \<Rightarrow> drain (buckets_remove B v j) j n g (g acc v))"

text \<open>Draining the buckets \<open>j, ..., j + m - 1\<close>.\<close>

fun \<^marker>\<open>provenance ai_human\<close> gap_walk where
  "gap_walk B j 0 g acc = acc"
| "gap_walk B j (Suc m) g acc = (case drain B j N g acc of (B', acc') \<Rightarrow> gap_walk B' (Suc j) m g acc')"

definition "lb_gap_fold = (\<lambda> (L, B, d) k g acc. gap_walk B (Suc k) (d - k) g acc)"

definition "lb_invar = (\<lambda> (L, B, d).
  lm_invar L \<and> buckets_invar B \<and> d < N \<and>
  (\<forall> v \<in> V. buckets_abstract B v = (if lm_get L v < N then Some (lm_get L v) else None)) \<and>
  (\<forall> v j. buckets_abstract B v = Some j \<longrightarrow> j \<le> d))"

end

locale \<^marker>\<open>provenance ai_human\<close> label_buckets_correct =
  label_buckets +
  assumes V_finite: "finite V"
  and N: "N = card V"
  and V_nonempty: "V \<noteq> {}"
  and lm_init: "lm_invar lm_init" "lm_get lm_init = (\<lambda> v. 0)"
  and bucket_vertex_fold:
        "\<And> g acc. \<exists> vs. distinct vs \<and> set vs = V \<and> bucket_vertex_fold g acc = foldl g acc vs"
begin

lemma N_pos: "0 < N"
  using V_finite V_nonempty
  by (simp add: N card_gt_0_iff)

lemma bucket_finite: "buckets_invar B \<Longrightarrow> finite {x. buckets_abstract B x = Some j}"
  using V_finite
  by (rule finite_subset[rotated]) (auto dest: bucket.buckets_universe)

lemma bucket_card_le: "buckets_invar B \<Longrightarrow> card {x. buckets_abstract B x = Some j} \<le> N"
  by (auto simp add: N intro!: card_mono V_finite dest: bucket.buckets_universe)

lemma lower_le: "lower B d \<le> d"
  by (induction d) (auto split: option.splits)

lemma lower_less: "d < N \<Longrightarrow> lower B d < N"
  using lower_le[of B d]
  by simp

lemma lower_bound:
  "\<lbrakk>buckets_invar B; d < N; buckets_abstract B v = Some j; j \<le> d\<rbrakk>
     \<Longrightarrow> j \<le> lower B d"
  by (induction d) (auto simp add: le_Suc_eq bucket.buckets_pick(1) split: option.splits)

text \<open>The intermediate buckets and bounds of an update, as computed by @{term lb_upd}.\<close>

lemma lb_upd_steps:
  fixes k' :: nat
  assumes "lb_invar (L, B, d)" "v \<in> V"
  defines "k \<equiv> lm_get L v"
  defines "B1 \<equiv> (if k < N then buckets_remove B v k else B)"
  defines "B2 \<equiv> (if k' < N then buckets_insert B1 v k' else B1)"
  defines "d1 \<equiv> (if k' < N then max d k' else d)"
  shows "lb_upd (L, B, d) v k' = (lm_upd L v k', B2, lower B2 d1)"
        "lm_invar L" "buckets_invar B" "d < N" "k < N \<Longrightarrow> buckets_abstract B v = Some k"
        "buckets_invar B1" "buckets_abstract B1 = (buckets_abstract B)(v := None)"
        "buckets_invar B2"
        "buckets_abstract B2 = (buckets_abstract B)(v := (if k' < N then Some k' else None))"
        "d1 < N" "\<forall> w j. buckets_abstract B2 w = Some j \<longrightarrow> j \<le> d1"
  using assms(1,2)
  by (auto simp add: lb_invar_def lb_upd_def Let_def k_def B1_def B2_def d1_def fun_upd_idem_iff le_max_iff_disj
                     bucket.buckets_remove bucket.buckets_insert)

lemma lb_upd_props:
  assumes "lb_invar A" "v \<in> V"
  shows "lb_invar (lb_upd A v k')" "lb_get (lb_upd A v k') = (lb_get A)(v := k')"
proof-
  obtain L B d where A: "A = (L, B, d)"
    by (cases A)
  note st = lb_upd_steps[OF assms(1)[unfolded A] assms(2)]
  have "lm_invar (lm_upd L v k')" "lm_get (lm_upd L v k') = (lm_get L)(v := k')"
    using st(2) assms(2)
    by (simp_all add: label_array.fixed_univ_map_upd_invar label_array.fixed_univ_map_upd)
  thus "lb_invar (lb_upd A v k')" "lb_get (lb_upd A v k') = (lb_get A)(v := k')"
    using assms(1) st(8-11)[where k'=k'] lower_bound[OF st(8,10)[where k'=k']]
    by (auto simp add: A st(1) lb_invar_def lb_get_def lower_less)
qed

lemma lb_fixed_univ_map: "fixed_univ_map V lb_invar lb_upd lb_get"
  by unfold_locales (simp_all add: lb_upd_props)

lemma init_fold:
  "\<lbrakk>distinct vs; buckets_invar B; set vs \<subseteq> V;
    \<forall> v \<in> set vs. buckets_abstract B v = None\<rbrakk> \<Longrightarrow>
     buckets_invar (foldl (\<lambda> B v. buckets_insert B v 0) B vs) \<and>
     buckets_abstract (foldl (\<lambda> B v. buckets_insert B v 0) B vs) =
       (\<lambda> x. if x \<in> set vs then Some 0 else buckets_abstract B x)"
proof(induction vs arbitrary: B)
  case (Cons v vs)
  hence "buckets_invar (buckets_insert B v 0)"
    "\<forall> w \<in> set vs. buckets_abstract (buckets_insert B v 0) w = None"
    using N_pos
    by (auto simp add: bucket.buckets_insert)
  from Cons.IH[OF _ this(1) _ this(2)] show ?case
    using Cons.prems N_pos
    by (auto simp add: bucket.buckets_insert fun_eq_iff)
qed simp

lemma lb_init_props: "lb_invar lb_init" "lb_get lb_init = (\<lambda> v. 0)"
  using bucket_vertex_fold[of "\<lambda> B v. buckets_insert B v 0" buckets_empty] lm_init N_pos
  by (auto simp add: lb_invar_def lb_init_def lb_get_def bucket.buckets_empty split: if_splits
           dest!: init_fold[OF _ bucket.buckets_empty(1), unfolded bucket.buckets_empty(2)])

lemma drain_props:
  assumes "buckets_invar B" "j < N" "card {x. buckets_abstract B x = Some j} \<le> n"
  shows "\<exists> ws. distinct ws \<and> set ws = {x. buckets_abstract B x = Some j} \<and>
               snd (drain B j n g acc) = foldl g acc ws \<and> buckets_invar (fst (drain B j n g acc)) \<and>
               buckets_abstract (fst (drain B j n g acc)) =
                 (\<lambda> x. if buckets_abstract B x = Some j then None else buckets_abstract B x)"
  using assms
proof(induction n arbitrary: acc B)
  case 0
  thus ?case
    using bucket_finite[of B j]
    by (auto simp add: fun_eq_iff)
next
  case (Suc n)
  show ?case
  proof(cases "buckets_pick B j")
    case None
    thus ?thesis
      using Suc.prems(1,2) bucket.buckets_pick(1)[of B j]
      by (auto simp add: fun_eq_iff)
  next
    case (Some v)
    hence "buckets_abstract B v = Some j"
      using Suc.prems(1,2)
      by (simp add: bucket.buckets_pick(2))
    moreover hence "card {x. buckets_abstract (buckets_remove B v j) x = Some j} \<le> n"
      using Suc.prems bucket_finite[of B j]
      by (simp add: bucket.bucket_level_remove)
    ultimately obtain ws where "distinct ws" "set ws = {x. buckets_abstract B x = Some j} - {v}"
      "snd (drain (buckets_remove B v j) j n g (g acc v)) = foldl g (g acc v) ws"
      "buckets_invar (fst (drain (buckets_remove B v j) j n g (g acc v)))"
      "buckets_abstract (fst (drain (buckets_remove B v j) j n g (g acc v))) =
         (\<lambda> x. if buckets_abstract (buckets_remove B v j) x = Some j then None
               else buckets_abstract (buckets_remove B v j) x)"
      using Suc.prems(1,2) bucket.buckets_remove(1)[of B v j] Suc.IH[of "buckets_remove B v j" "g acc v"]
      by (auto simp add: bucket.bucket_level_remove)
    thus ?thesis
      using Some Suc.prems(1) \<open>buckets_abstract B v = Some j\<close>
      by (intro exI[of _ "v # ws"]) (auto simp add: fun_eq_iff bucket.buckets_remove)
  qed
qed

lemma gap_walk_props:
  assumes "buckets_invar B" "0 < m \<Longrightarrow> j + m \<le> N"
  shows "\<exists> ws. distinct ws \<and>
               set ws = {x. \<exists> i. j \<le> i \<and> i < j + m \<and> buckets_abstract B x = Some i} \<and>
               gap_walk B j m g acc = foldl g acc ws"
  using assms
proof(induction m arbitrary: j acc B)
  case (Suc m)
  then obtain ws1 where ws1: "distinct ws1" "set ws1 = {x. buckets_abstract B x = Some j}"
    "snd (drain B j N g acc) = foldl g acc ws1" "buckets_invar (fst (drain B j N g acc))"
    "buckets_abstract (fst (drain B j N g acc)) =
       (\<lambda> x. if buckets_abstract B x = Some j then None else buckets_abstract B x)"
    using bucket_card_le[of B j] drain_props[of B j N g acc]
    by auto
  obtain ws2 where ws2: "distinct ws2"
    "set ws2 =
       {x. \<exists> i. Suc j \<le> i \<and> i < Suc j + m \<and>
                buckets_abstract (fst (drain B j N g acc)) x = Some i}"
    "gap_walk (fst (drain B j N g acc)) (Suc j) m g (snd (drain B j N g acc))
     = foldl g (snd (drain B j N g acc)) ws2"
    using Suc.IH[OF ws1(4), of "Suc j" "snd (drain B j N g acc)"] Suc.prems(2)
    by auto
  hence "set ws1 \<inter> set ws2 = {}"
        "set ws1 \<union> set ws2 =
           {x. \<exists> i. j \<le> i \<and> i < j + Suc m \<and> buckets_abstract B x = Some i}"
    using ws1(2,5)
    by (auto simp: le_eq_less_or_eq Suc_le_eq)
  thus ?case
    using ws1(1,3) ws2(1,3)
    by (intro exI[of _ "ws1 @ ws2"]) (simp add: case_prod_beta)
qed (rule exI[of _ "[]"]; simp)

lemma lb_gap_fold:
  assumes "lb_invar l"
  shows "\<exists> vs. distinct vs \<and>
               set vs = {v. v \<in> V \<and> k < lb_get l v \<and> lb_get l v < card V} \<and>
               lb_gap_fold l k g acc = foldl g acc vs"
proof-
  obtain L B d where l: "l = (L, B, d)"
    by (cases l)
  moreover hence I: "buckets_invar B" "d < N"
    "\<forall> w \<in> V. buckets_abstract B w = (if lm_get L w < N then Some (lm_get L w) else None)"
    "\<forall> w j. buckets_abstract B w = Some j \<longrightarrow> j \<le> d"
    using assms
    by (simp_all add: lb_invar_def)
  ultimately have "{x. \<exists> i. Suc k \<le> i \<and> i < Suc k + (d - k) \<and> buckets_abstract B x = Some i} =
                   {v. v \<in> V \<and> k < lb_get l v \<and> lb_get l v < card V}"
    by (fastforce simp: lb_get_def N split: if_splits dest: bucket.buckets_universe)
  thus ?thesis
    using I(1,2) gap_walk_props[of B "d - k" "Suc k" g acc]
    by (simp add: lb_gap_fold_def l)
qed

end

end
