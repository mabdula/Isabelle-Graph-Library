theory Neighbourhood_Best_Scan
  imports
    Data_Structures.Iterable_Set_Specs
    Complex_Main
begin

section \<open>The Best Two Neighbours in a Collection of Neighbourhoods\<close>

text \<open>A cursor scan over the neighbourhood of a vertex @{term u} that keeps a neighbour of minimum
      key and a runner-up, i.e. a neighbour of minimum key among the others. Among neighbours of
      equal key, a neighbour satisfying @{term pref} wins. The key and the preference are
      arguments, so that the scan can be used with keys that change between calls.\<close>

locale nb_best_scan_spec =
  fixes rnb_current :: "'g \<Rightarrow> 'v \<Rightarrow> 'v"
    and rnb_has :: "'g \<Rightarrow> 'v \<Rightarrow> bool"
    and rnb_move :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
    and rnb_reset :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
begin

definition better :: "('v \<Rightarrow> bool) \<Rightarrow> real \<times> 'v \<Rightarrow> real \<times> 'v \<Rightarrow> bool" where
  "better pref p q = (fst p < fst q \<or> (fst p = fst q \<and> pref (snd p) \<and> \<not> pref (snd q)))"

definition "best_upd key pref u b r =
  (case b of None \<Rightarrow> Some (key u r, r)
   | Some p \<Rightarrow> if better pref (key u r, r) p then Some (key u r, r) else b)"

text \<open>A new best neighbour demotes the old one to the runner-up. Otherwise the new neighbour
      competes for the runner-up.\<close>

definition "best2_upd key pref u bs r =
  (case bs of (b, s) \<Rightarrow>
     (case b of None \<Rightarrow> (Some (key u r, r), b)
      | Some p \<Rightarrow> if better pref (key u r, r) p then (Some (key u r, r), b)
                  else (b, best_upd key pref u s r)))"

partial_function (tailrec) scan_best ::
  "('v \<Rightarrow> 'v \<Rightarrow> real) \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v \<Rightarrow> 'g \<Rightarrow>
   (real \<times> 'v) option \<times> (real \<times> 'v) option \<Rightarrow>
   'g \<times> (real \<times> 'v) option \<times> (real \<times> 'v) option" where
  "scan_best key pref u C bs =
     (if rnb_has C u then scan_best key pref u (rnb_move C u) (best2_upd key pref u bs (rnb_current C u))
      else (C, bs))"

definition "best_two key pref u C = scan_best key pref u (rnb_reset C u) (None, None)"

lemmas [code] = better_def best_upd_def best2_upd_def scan_best.simps best_two_def

text \<open>@{term b} is a best neighbour among @{term S}.\<close>

definition "best_inv key pref u S b =
  (case b of None \<Rightarrow> S = {}
   | Some (x, j) \<Rightarrow> j \<in> S \<and> x = key u j \<and> (\<forall>r\<in>S. x \<le> key u r) \<and>
                    (\<forall>r\<in>S. key u r = x \<and> pref r \<longrightarrow> pref j))"

text \<open>@{term b} is a best neighbour among @{term S}, and @{term s} is a best one among the others.\<close>

definition "best2_inv key pref u S bs =
  (case bs of (b, s) \<Rightarrow> best_inv key pref u S b \<and>
     (case b of None \<Rightarrow> s = None | Some (x, j) \<Rightarrow> best_inv key pref u (S - {j}) s))"

lemma best_upd_inv:
  "best_inv key pref u S b \<Longrightarrow> best_inv key pref u (insert r S) (best_upd key pref u b r)"
proof(cases b)
  case (Some p)
  moreover obtain y s where "p = (y, s)" by (cases p) auto
  ultimately show "best_inv key pref u S b \<Longrightarrow> ?thesis"
    by (cases "better pref (key u r, r) (y, s)")
       (auto simp: best_inv_def best_upd_def better_def)
qed (simp add: best_inv_def best_upd_def)

lemma best2_upd_fst: "fst (best2_upd key pref u bs r) = best_upd key pref u (fst bs) r"
  by (cases bs) (simp add: best2_upd_def best_upd_def split: option.splits)

lemma best2_upd_inv:
  assumes "best2_inv key pref u S bs" "r \<notin> S"
  shows "best2_inv key pref u (insert r S) (best2_upd key pref u bs r)"
proof-
  obtain b s where bs: "bs = (b, s)" by (cases bs) auto
  have B: "best_inv key pref u S b" using assms(1) by (simp add: best2_inv_def bs)
  have F: "best_inv key pref u (insert r S) (fst (best2_upd key pref u bs r))"
    using best_upd_inv[OF B] by (simp add: best2_upd_fst bs)
  show ?thesis
  proof(cases b)
    case None
    have "S = {}" using B by (simp add: best_inv_def None)
    thus ?thesis using F by (simp add: best2_inv_def best2_upd_def bs None best_inv_def)
  next
    case (Some p)
    obtain y j where p: "p = (y, j)" by (cases p) auto
    have j: "j \<in> S" using B by (simp add: best_inv_def Some p)
    have S2: "best_inv key pref u (S - {j}) s" using assms(1) by (simp add: best2_inv_def bs Some p)
    show ?thesis
    proof(cases "better pref (key u r, r) (y, j)")
      case True
      have eq: "best2_upd key pref u bs r = (Some (key u r, r), b)"
        by (simp add: best2_upd_def bs Some p True)
      have "insert r S - {r} = S" using assms(2) by blast
      thus ?thesis using F B by (simp add: eq best2_inv_def)
    next
      case False
      have eq: "best2_upd key pref u bs r = (b, best_upd key pref u s r)"
        by (simp add: best2_upd_def bs Some p False)
      have "insert r S - {j} = insert r (S - {j})" using assms(2) j by blast
      thus ?thesis using F best_upd_inv[OF S2, of r] by (simp add: eq best2_inv_def Some p)
    qed
  qed
qed

end

locale nb_best_scan = nb_best_scan_spec +
  rnb: indexed_iterable_set rnb_invar rnb_abstract rnb_current rnb_has rnb_iterated
      rnb_remaining rnb_move rnb_reset K
  for rnb_invar rnb_abstract rnb_iterated rnb_remaining K
begin

lemma scan_best_props:
  assumes "rnb_invar C" "u \<in> K" "finite (rnb_remaining C u)" "best2_inv key pref u S bs"
          "S \<inter> rnb_remaining C u = {}"
  shows "rnb_invar (fst (scan_best key pref u C bs)) \<and>
         rnb_abstract (fst (scan_best key pref u C bs)) = rnb_abstract C \<and>
         best2_inv key pref u (S \<union> rnb_remaining C u) (snd (scan_best key pref u C bs))"
  using assms
proof(induction "card (rnb_remaining C u)" arbitrary: C S bs)
  case 0
  hence empty: "rnb_remaining C u = {}" by simp
  hence not_has: "\<not> rnb_has C u" using rnb.idx_has[OF 0(2,3)] by simp
  show ?case
    using 0(2,5) by (simp add: scan_best.simps[of key pref u C bs] not_has empty)
next
  case (Suc n)
  hence ne: "rnb_remaining C u \<noteq> {}" by auto
  hence has: "rnb_has C u" using rnb.idx_has[OF Suc(3,4)] by simp
  define x where "x = rnb_current C u"
  define C' where "C' = rnb_move C u"
  have x_in: "x \<in> rnb_remaining C u" using rnb.idx_current[OF Suc(3,4) ne] by (simp add: x_def)
  have xS: "x \<notin> S" using disjoint_iff[THEN iffD1, OF Suc(7), rule_format, of x] x_in by auto
  have C': "rnb_invar C'" "rnb_remaining C' u = rnb_remaining C u - {x}"
           "rnb_abstract C' = rnb_abstract C"
    using rnb.idx_move_invar[OF Suc(3,4)] rnb.idx_move_remaining[OF Suc(3,4) ne]
          rnb.idx_move_abstract[OF Suc(3,4) ne]
    by (auto simp: C'_def x_def fun_eq_iff)
  have card: "n = card (rnb_remaining C' u)" using Suc(2,5) x_in by (simp add: C'(2))
  have disj: "insert x S \<inter> rnb_remaining C' u = {}" using Suc(7) by (auto simp: C'(2))
  define bs' where "bs' = best2_upd key pref u bs x"
  have IH: "rnb_invar (fst (scan_best key pref u C' bs')) \<and>
            rnb_abstract (fst (scan_best key pref u C' bs')) = rnb_abstract C' \<and>
            best2_inv key pref u (insert x S \<union> rnb_remaining C' u) (snd (scan_best key pref u C' bs'))"
    using Suc(1)[OF card C'(1) Suc(4) _ best2_upd_inv[OF Suc(6) xS] disj] Suc(5)
    by (simp add: C'(2) bs'_def)
  have eq: "scan_best key pref u C bs = scan_best key pref u C' bs'"
    by (simp add: scan_best.simps[of key pref u C bs] has C'_def x_def bs'_def)
  have "insert x S \<union> rnb_remaining C' u = S \<union> rnb_remaining C u" using x_in by (auto simp: C'(2))
  thus ?case using IH by (simp add: eq C'(3))
qed

lemma best_two_props:
  assumes "rnb_invar C" "u \<in> K" "finite (rnb_abstract C u)" "best_two key pref u C = (C', b, s)"
  shows "rnb_invar C'" "rnb_abstract C' = rnb_abstract C"
        "b = None \<longleftrightarrow> rnb_abstract C u = {}"
        "b = Some (x, j) \<Longrightarrow>
           j \<in> rnb_abstract C u \<and> x = key u j \<and> (\<forall>r\<in>rnb_abstract C u. x \<le> key u r) \<and>
           (\<forall>r\<in>rnb_abstract C u. key u r = x \<and> pref r \<longrightarrow> pref j)"
        "b = Some (x, j) \<Longrightarrow> s = None \<longleftrightarrow> rnb_abstract C u - {j} = {}"
        "\<lbrakk>b = Some (x, j); s = Some (y, i)\<rbrakk> \<Longrightarrow>
           i \<in> rnb_abstract C u - {j} \<and> y = key u i \<and> (\<forall>r\<in>rnb_abstract C u - {j}. y \<le> key u r)"
proof-
  have R: "rnb_invar (rnb_reset C u)" "rnb_remaining (rnb_reset C u) u = rnb_abstract C u"
          "rnb_abstract (rnb_reset C u) = rnb_abstract C"
    using rnb.idx_reset_invar[OF assms(1,2)] rnb.idx_reset_remaining[OF assms(1,2)]
          rnb.idx_reset_abstract[OF assms(1,2)] by (auto simp: fun_eq_iff)
  have P: "rnb_invar C' \<and> rnb_abstract C' = rnb_abstract C \<and>
           best2_inv key pref u (rnb_abstract C u) (b, s)"
    using scan_best_props[OF R(1) assms(2), of key pref "{}" "(None, None)"] assms(3,4)
    by (simp add: R(2,3) best_two_def best2_inv_def best_inv_def)
  hence B: "best_inv key pref u (rnb_abstract C u) b"
       and S: "case b of None \<Rightarrow> s = None
               | Some (x, j) \<Rightarrow> best_inv key pref u (rnb_abstract C u - {j}) s"
    by (simp_all add: best2_inv_def)
  show "rnb_invar C'" "rnb_abstract C' = rnb_abstract C" using P by simp+
  show "b = None \<longleftrightarrow> rnb_abstract C u = {}"
    using B by (auto simp: best_inv_def split: option.splits)
  show "b = Some (x, j) \<Longrightarrow>
           j \<in> rnb_abstract C u \<and> x = key u j \<and> (\<forall>r\<in>rnb_abstract C u. x \<le> key u r) \<and>
           (\<forall>r\<in>rnb_abstract C u. key u r = x \<and> pref r \<longrightarrow> pref j)"
    using B by (auto simp: best_inv_def)
  show "b = Some (x, j) \<Longrightarrow> s = None \<longleftrightarrow> rnb_abstract C u - {j} = {}"
    using S by (auto simp: best_inv_def split: option.splits)
  show "\<lbrakk>b = Some (x, j); s = Some (y, i)\<rbrakk> \<Longrightarrow>
           i \<in> rnb_abstract C u - {j} \<and> y = key u i \<and> (\<forall>r\<in>rnb_abstract C u - {j}. y \<le> key u r)"
    using S by (auto simp: best_inv_def)
qed

end

end
