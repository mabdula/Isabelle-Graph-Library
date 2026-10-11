theory Push_Relabel_Label_Buckets
  imports
    Data_Structures.Fixed_Univ_Map_Specs
    Data_Structures.Fixed_Univ_Buckets_Specs
begin

section \<open>Label Maps with Buckets for the Gap Heuristic\<close>

text \<open>A label map over the vertices @{term V} that also keeps every vertex with a label below
      @{term N} (the number of vertices) in the bucket of its label, together with an upper bound
      \<open>d\<close> on the bucket numbers in use. Updating a label moves the vertex between buckets, raises
      the bound if necessary and lowers it while its bucket is empty. The vertices with labels
      strictly between \<open>k\<close> and @{term N} can thus be enumerated by walking the buckets
      \<open>k + 1, ..., d\<close>, which is the gap enumeration of the generic push-relabel algorithm.
      Everything is generic in the underlying label array and buckets.\<close>

locale label_buckets =
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

fun lower where
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

fun drain where
  "drain B j 0 g acc = (B, acc)"
| "drain B j (Suc n) g acc =
     (case buckets_pick B j of None \<Rightarrow> (B, acc)
      | Some v \<Rightarrow> drain (buckets_remove B v j) j n g (g acc v))"

text \<open>Draining the buckets \<open>j, ..., j + m - 1\<close>.\<close>

fun gap_walk where
  "gap_walk B j 0 g acc = acc"
| "gap_walk B j (Suc m) g acc = (case drain B j N g acc of (B', acc') \<Rightarrow> gap_walk B' (Suc j) m g acc')"

definition "lb_gap_fold = (\<lambda> (L, B, d) k g acc. gap_walk B (Suc k) (d - k) g acc)"

definition "lb_invar = (\<lambda> (L, B, d).
  lm_invar L \<and> buckets_invar B \<and> d < N \<and>
  (\<forall> v \<in> V. buckets_abstract B v = (if lm_get L v < N then Some (lm_get L v) else None)) \<and>
  (\<forall> v j. buckets_abstract B v = Some j \<longrightarrow> j \<le> d))"

end

locale label_buckets_correct =
  label_buckets +
  assumes V_finite: "finite V"
  and N: "N = card V"
  and V_nonempty: "V \<noteq> {}"
  and lm_init: "lm_invar lm_init" "lm_get lm_init = (\<lambda> v. 0)"
  and bucket_vertex_fold:
        "\<And> g acc. \<exists> vs. distinct vs \<and> set vs = V \<and> bucket_vertex_fold g acc = foldl g acc vs"
begin

lemma N_pos: "0 < N"
  using V_finite V_nonempty by (simp add: N card_gt_0_iff)

lemma lower_props:
  assumes "buckets_invar B" "d < N" "\<forall> v j. buckets_abstract B v = Some j \<longrightarrow> j \<le> d"
  shows "lower B d \<le> d \<and> (\<forall> v j. buckets_abstract B v = Some j \<longrightarrow> j \<le> lower B d)"
  using assms(2,3)
proof(induction d)
  case (Suc d)
  show ?case
  proof(cases "buckets_pick B (Suc d)")
    case None
    have "\<forall> v. buckets_abstract B v \<noteq> Some (Suc d)"
      using bucket.buckets_pick(1)[OF assms(1)] Suc.prems(1) None by simp
    hence "\<forall> v j. buckets_abstract B v = Some j \<longrightarrow> j \<le> d"
      using Suc.prems(2) by (auto simp add: le_Suc_eq)
    hence "lower B d \<le> d \<and> (\<forall> v j. buckets_abstract B v = Some j \<longrightarrow> j \<le> lower B d)"
      using Suc.IH Suc.prems(1) by simp
    thus ?thesis
      using None by simp
  qed (use Suc.prems in simp)
qed simp

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
proof-
  have I: "lm_invar L" "buckets_invar B" "d < N"
          "\<forall> w \<in> V. buckets_abstract B w = (if lm_get L w < N then Some (lm_get L w) else None)"
          "\<forall> w j. buckets_abstract B w = Some j \<longrightarrow> j \<le> d"
    using assms(1) by (simp_all add: lb_invar_def)
  show "lb_upd (L, B, d) v k' = (lm_upd L v k', B2, lower B2 d1)"
    by (simp add: lb_upd_def Let_def k_def B1_def B2_def d1_def)
  show "lm_invar L" "buckets_invar B" "d < N"
    using I(1-3) .
  have Bv: "buckets_abstract B v = (if k < N then Some k else None)"
    using I(4) assms(2) by (simp add: k_def)
  thus "k < N \<Longrightarrow> buckets_abstract B v = Some k"
    by simp
  have B1: "buckets_invar B1 \<and> buckets_abstract B1 = (buckets_abstract B)(v := None)"
  proof(cases "k < N")
    case True
    thus ?thesis
      using bucket.buckets_remove[OF I(2)] Bv by (simp add: B1_def)
  next
    case False
    have "(buckets_abstract B)(v := None) = buckets_abstract B"
      using Bv False by auto
    thus ?thesis
      using I(2) False by (simp add: B1_def)
  qed
  thus "buckets_invar B1" "buckets_abstract B1 = (buckets_abstract B)(v := None)"
    by simp_all
  have B2: "buckets_invar B2 \<and>
            buckets_abstract B2 = (buckets_abstract B)(v := (if k' < N then Some k' else None))"
  proof(cases "k' < N")
    case True
    thus ?thesis
      using bucket.buckets_insert[OF conjunct1[OF B1] assms(2)] conjunct2[OF B1] by (simp add: B2_def)
  qed (use B1 in \<open>simp add: B2_def\<close>)
  thus "buckets_invar B2"
       "buckets_abstract B2 = (buckets_abstract B)(v := (if k' < N then Some k' else None))"
    by simp_all
  show "d1 < N" "\<forall> w j. buckets_abstract B2 w = Some j \<longrightarrow> j \<le> d1"
    using I(3,5) B2 by (auto simp add: d1_def le_max_iff_disj)
qed

lemma lb_upd_props:
  assumes "lb_invar A" "v \<in> V"
  shows "lb_invar (lb_upd A v k')" "lb_get (lb_upd A v k') = (lb_get A)(v := k')"
proof-
  obtain L B d where A: "A = (L, B, d)"
    by (cases A) auto
  note st = lb_upd_steps[OF assms(1)[unfolded A] assms(2)]
  have I: "\<forall> w \<in> V. buckets_abstract B w = (if lm_get L w < N then Some (lm_get L w) else None)"
    using assms(1) by (simp add: lb_invar_def A)
  note lw = lower_props[OF st(8,10,11)[of k']]
  have L': "lm_invar (lm_upd L v k')" "lm_get (lm_upd L v k') = (lm_get L)(v := k')"
    using label_array.fixed_univ_map_upd_invar[OF st(2) assms(2)]
          label_array.fixed_univ_map_upd[OF st(2) assms(2)] by simp_all
  show "lb_invar (lb_upd A v k')"
    unfolding A st(1)[of k'] lb_invar_def
    using L' st(8,9,10)[of k'] lw I by auto
  show "lb_get (lb_upd A v k') = (lb_get A)(v := k')"
    unfolding A st(1)[of k'] using L'(2) by (simp add: lb_get_def)
qed

lemma lb_fixed_univ_map: "fixed_univ_map V lb_invar lb_upd lb_get"
  using lb_upd_props by unfold_locales simp_all

lemma init_fold:
  assumes "buckets_invar B" "distinct vs" "set vs \<subseteq> V" "\<forall> v \<in> set vs. buckets_abstract B v = None"
  shows "buckets_invar (foldl (\<lambda> B v. buckets_insert B v 0) B vs) \<and>
         buckets_abstract (foldl (\<lambda> B v. buckets_insert B v 0) B vs) =
         (\<lambda> x. if x \<in> set vs then Some 0 else buckets_abstract B x)"
  using assms
proof(induction vs arbitrary: B)
  case (Cons v vs)
  have v: "v \<in> V" "buckets_abstract B v = None"
    using Cons.prems(3,4) by simp_all
  note ins = bucket.buckets_insert[OF Cons.prems(1) v(1) _ v(2), of 0, simplified N_pos lessThan_iff]
  have "buckets_invar (buckets_insert B v 0)" "distinct vs" "set vs \<subseteq> V"
       "\<forall> w \<in> set vs. buckets_abstract (buckets_insert B v 0) w = None"
    using ins Cons.prems by auto
  from Cons.IH[OF this] show ?case
    using ins(2) by auto
qed simp

lemma lb_init_props: "lb_invar lb_init" "lb_get lb_init = (\<lambda> v. 0)"
proof-
  obtain vs where vs: "distinct vs" "set vs = V"
    "bucket_vertex_fold (\<lambda> B v. buckets_insert B v 0) buckets_empty =
     foldl (\<lambda> B v. buckets_insert B v 0) buckets_empty vs"
    using bucket_vertex_fold by blast
  note f = init_fold[OF bucket.buckets_empty(1) vs(1)] vs(2) bucket.buckets_empty(2)
  show "lb_invar lb_init"
    using f lm_init N_pos by (simp add: lb_invar_def lb_init_def vs(3))
  show "lb_get lb_init = (\<lambda> v. 0)"
    using lm_init by (simp add: lb_get_def lb_init_def)
qed

lemma drain_props:
  assumes "buckets_invar B" "j < N" "card {x. buckets_abstract B x = Some j} \<le> n"
  shows "\<exists> ws. distinct ws \<and> set ws = {x. buckets_abstract B x = Some j} \<and>
               snd (drain B j n g acc) = foldl g acc ws \<and> buckets_invar (fst (drain B j n g acc)) \<and>
               buckets_abstract (fst (drain B j n g acc)) =
                 (\<lambda> x. if buckets_abstract B x = Some j then None else buckets_abstract B x)"
  using assms
proof(induction n arbitrary: B acc)
  case 0
  have fin: "finite {x. buckets_abstract B x = Some j}"
    using bucket.buckets_universe[OF 0(1)] V_finite by (auto intro: finite_subset)
  have e: "{x. buckets_abstract B x = Some j} = {}"
    using 0(3) card_0_eq[OF fin] by simp
  hence "(\<lambda> x. if buckets_abstract B x = Some j then None else buckets_abstract B x) =
         buckets_abstract B"
    by (auto simp add: fun_eq_iff)
  thus ?case
    using e 0(1) by simp
next
  case (Suc n)
  show ?case
  proof(cases "buckets_pick B j")
    case None
    have e: "{x. buckets_abstract B x = Some j} = {}"
      using bucket.buckets_pick(1)[OF Suc.prems(1)] Suc.prems(2) None by simp
    hence "(\<lambda> x. if buckets_abstract B x = Some j then None else buckets_abstract B x) =
           buckets_abstract B"
      by (auto simp add: fun_eq_iff)
    thus ?thesis
      using None e Suc.prems(1) by simp
  next
    case (Some v)
    have vj: "buckets_abstract B v = Some j"
      using bucket.buckets_pick(2)[OF Suc.prems(1) _ Some] Suc.prems(2) by simp
    define B1 where "B1 = buckets_remove B v j"
    note rm = bucket.buckets_remove[OF Suc.prems(1) vj, folded B1_def]
    have fin: "finite {x. buckets_abstract B x = Some j}"
      using bucket.buckets_universe[OF Suc.prems(1)] V_finite by (auto intro: finite_subset)
    have S1: "{x. buckets_abstract B1 x = Some j} = {x. buckets_abstract B x = Some j} - {v}"
      using rm(2) by auto
    hence "card {x. buckets_abstract B1 x = Some j} \<le> n"
      using Suc.prems(3) vj fin by simp
    then obtain ws where ws: "distinct ws" "set ws = {x. buckets_abstract B1 x = Some j}"
      "snd (drain B1 j n g (g acc v)) = foldl g (g acc v) ws"
      "buckets_invar (fst (drain B1 j n g (g acc v)))"
      "buckets_abstract (fst (drain B1 j n g (g acc v))) =
         (\<lambda> x. if buckets_abstract B1 x = Some j then None else buckets_abstract B1 x)"
      using Suc.IH[OF rm(1) Suc.prems(2)] by blast
    have dr: "drain B j (Suc n) g acc = drain B1 j n g (g acc v)"
      using Some by (simp add: B1_def)
    have ab: "(\<lambda> x. if buckets_abstract B1 x = Some j then None else buckets_abstract B1 x) =
              (\<lambda> x. if buckets_abstract B x = Some j then None else buckets_abstract B x)"
      using rm(2) vj by (auto simp add: fun_eq_iff)
    have vws: "distinct (v # ws)" "set (v # ws) = {x. buckets_abstract B x = Some j}"
      using ws(1,2) S1 vj by auto
    show ?thesis
      unfolding dr using vws ws(3-5) ab by (intro exI[of _ "v # ws"]) simp
  qed
qed

lemma gap_walk_props:
  assumes "buckets_invar B" "0 < m \<Longrightarrow> j + m \<le> N"
  shows "\<exists> ws. distinct ws \<and> set ws = {x. \<exists> i. j \<le> i \<and> i < j + m \<and> buckets_abstract B x = Some i} \<and>
               gap_walk B j m g acc = foldl g acc ws"
  using assms
proof(induction m arbitrary: j acc B)
  case (Suc m)
  have j: "j < N"
    using Suc.prems by simp
  have cj: "card {x. buckets_abstract B x = Some j} \<le> N"
    using bucket.buckets_universe[OF Suc.prems(1)] V_finite
    by (auto intro!: card_mono simp add: N)
  define B' where "B' = fst (drain B j N g acc)"
  define acc' where "acc' = snd (drain B j N g acc)"
  obtain ws1 where ws1: "distinct ws1" "set ws1 = {x. buckets_abstract B x = Some j}"
    "acc' = foldl g acc ws1" "buckets_invar B'"
    "buckets_abstract B' = (\<lambda> x. if buckets_abstract B x = Some j then None else buckets_abstract B x)"
    using drain_props[OF Suc.prems(1) j cj, of g acc] by (auto simp add: B'_def acc'_def)
  have m: "0 < m \<Longrightarrow> Suc j + m \<le> N"
    using Suc.prems by simp
  obtain ws2 where ws2: "distinct ws2"
    "set ws2 = {x. \<exists> i. Suc j \<le> i \<and> i < Suc j + m \<and> buckets_abstract B' x = Some i}"
    "gap_walk B' (Suc j) m g acc' = foldl g acc' ws2"
    using Suc.IH[OF ws1(4) m, of acc'] by auto
  have S2: "{x. \<exists> i. Suc j \<le> i \<and> i < Suc j + m \<and> buckets_abstract B' x = Some i} =
            {x. \<exists> i. Suc j \<le> i \<and> i < Suc j + m \<and> buckets_abstract B x = Some i}"
    using ws1(5) by auto
  have "set ws1 \<inter> set ws2 = {}"
    using ws1(2) ws2(2) S2 by auto
  hence dis: "distinct (ws1 @ ws2)"
    using ws1(1) ws2(1) by simp
  have eq: "{x. \<exists> i. j \<le> i \<and> i < j + Suc m \<and> buckets_abstract B x = Some i} =
                 {x. buckets_abstract B x = Some j} \<union>
                 {x. \<exists> i. Suc j \<le> i \<and> i < Suc j + m \<and> buckets_abstract B x = Some i}"
  proof(rule set_eqI, rule iffI)
    fix x
    assume "x \<in> {x. \<exists> i. j \<le> i \<and> i < j + Suc m \<and> buckets_abstract B x = Some i}"
    then obtain i where i: "j \<le> i" "i < j + Suc m" "buckets_abstract B x = Some i"
      by blast
    show "x \<in> {x. buckets_abstract B x = Some j} \<union>
              {x. \<exists> i. Suc j \<le> i \<and> i < Suc j + m \<and> buckets_abstract B x = Some i}"
    proof(cases "i = j")
      case False
      hence "Suc j \<le> i" "i < Suc j + m"
        using i(1,2) by simp_all
      thus ?thesis
        using i(3) by blast
    qed (use i in simp)
  next
    fix x
    assume "x \<in> {x. buckets_abstract B x = Some j} \<union>
                {x. \<exists> i. Suc j \<le> i \<and> i < Suc j + m \<and> buckets_abstract B x = Some i}"
    thus "x \<in> {x. \<exists> i. j \<le> i \<and> i < j + Suc m \<and> buckets_abstract B x = Some i}"
    proof
      assume "x \<in> {x. buckets_abstract B x = Some j}"
      thus ?thesis
        by (intro CollectI exI[of _ j]) simp
    next
      assume "x \<in> {x. \<exists> i. Suc j \<le> i \<and> i < Suc j + m \<and> buckets_abstract B x = Some i}"
      then obtain i where "Suc j \<le> i" "i < Suc j + m" "buckets_abstract B x = Some i"
        by blast
      thus ?thesis
        by (intro CollectI exI[of _ i]) simp
    qed
  qed
  have sw: "set (ws1 @ ws2) = {x. \<exists> i. j \<le> i \<and> i < j + Suc m \<and> buckets_abstract B x = Some i}"
    by (simp only: set_append ws1(2) ws2(2) S2 eq)
  have gw: "gap_walk B j (Suc m) g acc = foldl g acc (ws1 @ ws2)"
    using ws1(3) ws2(3) by (simp add: case_prod_beta B'_def acc'_def)
  show ?case
    by (rule exI[of _ "ws1 @ ws2"]) (simp only: dis sw gw simp_thms)
qed (rule exI[of _ "[]"]; simp)

lemma lb_gap_fold:
  assumes "lb_invar l"
  shows "\<exists> vs. distinct vs \<and> set vs = {v. v \<in> V \<and> k < lb_get l v \<and> lb_get l v < card V} \<and>
               lb_gap_fold l k g acc = foldl g acc vs"
proof-
  obtain L B d where l: "l = (L, B, d)"
    by (cases l) auto
  have I: "buckets_invar B" "d < N"
          "\<forall> w \<in> V. buckets_abstract B w = (if lm_get L w < N then Some (lm_get L w) else None)"
          "\<forall> w j. buckets_abstract B w = Some j \<longrightarrow> j \<le> d"
    using assms by (simp_all add: lb_invar_def l)
  have m: "0 < d - k \<Longrightarrow> Suc k + (d - k) \<le> N"
    using I(2) by simp
  have "{x. \<exists> i. Suc k \<le> i \<and> i < Suc k + (d - k) \<and> buckets_abstract B x = Some i} =
        {v. v \<in> V \<and> k < lb_get l v \<and> lb_get l v < card V}"
  proof(rule set_eqI, rule iffI)
    fix x
    assume "x \<in> {x. \<exists> i. Suc k \<le> i \<and> i < Suc k + (d - k) \<and> buckets_abstract B x = Some i}"
    then obtain i where i: "Suc k \<le> i" "buckets_abstract B x = Some i"
      by blast
    have x: "x \<in> V"
      using bucket.buckets_universe[OF I(1) i(2)] by simp
    thus "x \<in> {v. v \<in> V \<and> k < lb_get l v \<and> lb_get l v < card V}"
      using I(3) i by (auto simp add: lb_get_def l N split: if_splits)
  next
    fix x
    assume "x \<in> {v. v \<in> V \<and> k < lb_get l v \<and> lb_get l v < card V}"
    hence x: "x \<in> V" "k < lm_get L x" "lm_get L x < N"
      by (simp_all add: lb_get_def l N)
    hence "buckets_abstract B x = Some (lm_get L x)"
      using I(3) by simp
    moreover have "lm_get L x \<le> d"
      using I(4) calculation by blast
    ultimately show "x \<in> {x. \<exists> i. Suc k \<le> i \<and> i < Suc k + (d - k) \<and> buckets_abstract B x = Some i}"
      using x(2) by auto
  qed
  thus ?thesis
    using gap_walk_props[OF I(1) m, of g acc] by (simp add: lb_gap_fold_def l)
qed

end

end
