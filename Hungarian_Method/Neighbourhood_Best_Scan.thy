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
  by (auto simp: best_inv_def best_upd_def better_def split: option.splits if_splits)

lemma best2_upd_fst: "fst (best2_upd key pref u bs r) = best_upd key pref u (fst bs) r"
  by (cases bs) (simp add: best2_upd_def best_upd_def split: option.splits)

lemma best_inv_Some_in:
  "best_inv key pref u S (Some (y, j)) \<Longrightarrow> j \<in> S"
  by (simp add: best_inv_def)

lemma best2_upd_inv:
  "\<lbrakk>best2_inv key pref u S bs; r \<notin> S\<rbrakk>
     \<Longrightarrow> best2_inv key pref u (insert r S) (best2_upd key pref u bs r)"
  using best_upd_inv[of key pref u S "fst bs" r]
        best_upd_inv[of key pref u "S - {snd (the (fst bs))}" "snd bs" r]
  by (cases bs; cases "fst bs")
     (auto simp: best2_inv_def best2_upd_def best_upd_def insert_Diff_if Diff_insert_absorb
           dest: best_inv_Some_in split: if_splits option.splits)

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
  thus ?case
    by (simp add: scan_best.simps[of key pref u C bs] rnb.idx_has)
next
  case (Suc n)
  hence "rnb_remaining C u \<noteq> {}"
    by auto
  with Suc have "rnb_has C u" "rnb_abstract (rnb_move C u) = rnb_abstract C"
      "n = card (rnb_remaining (rnb_move C u) u)" "finite (rnb_remaining (rnb_move C u) u)"
      "rnb_current C u \<notin> S"
      "insert (rnb_current C u) S \<inter> rnb_remaining (rnb_move C u) u = {}"
      "insert (rnb_current C u) S \<union> rnb_remaining (rnb_move C u) u = S \<union> rnb_remaining C u"
    using rnb.idx_current[of C u]
    by (auto simp: rnb.idx_has rnb.idx_move_abstract rnb.idx_move_remaining fun_eq_iff)
  thus ?case
    using Suc(1)[of "rnb_move C u" "insert (rnb_current C u) S"
                    "best2_upd key pref u bs (rnb_current C u)"] Suc(2-)
          best2_upd_inv[of key pref u S bs "rnb_current C u"]
    by (simp add: scan_best.simps[of key pref u C bs] rnb.idx_move_invar)
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
  using scan_best_props[of "rnb_reset C u" u key pref "{}" "(None, None)"] assms
  by (auto simp: rnb.idx_reset_invar rnb.idx_reset_remaining rnb.idx_reset_abstract fun_eq_iff
                 best_two_def best2_inv_def best_inv_def split: option.splits)

end

end
