theory Matroid_Intersection_Imp
  imports Matroid_Intersection_Exchange_Graph_Imp Exchange_Candidates_Imp
begin

section \<open>Unweighted Matroid Intersection in Imperative HOL\<close>

text \<open>The complete imperative algorithm for two matroids on the nats below \<open>n\<close>, given by
  oracles. The caller provides the handle of the empty solution and the static handles of the
  partner queries. The program builds the CSR of the candidate graph from the partner lists,
  allocates the work arrays of the path search, and runs the augmentation loop on them; this is
  the only place where arrays are allocated. The result is a maximum common independent set,
  in the solution handle.\<close>

subsection \<open>Code\<close>

declare intersection_augment_imp_spec.aug_imp.simps[code]
  unweighted_intersection_imp_loop_spec.mi_loop_imp.simps[code]

locale matroid_intersection_imp_ids_spec =
  unweighted_intersection_exchange_imp_spec n smemb_imp ins1_imp exch1_imp ins2_imp exch2_imp
  for n and smemb_imp :: "nat \<Rightarrow> 'si \<Rightarrow> bool Heap" and ins1_imp exch1_imp ins2_imp exch2_imp +
  fixes sins_imp :: "nat \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and sdel_imp :: "nat \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and npts1_imp :: "'h1 \<Rightarrow> nat \<Rightarrow> nat Heap"
    and pt1_imp :: "'h1 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
    and npts2_imp :: "'h2 \<Rightarrow> nat \<Rightarrow> nat Heap"
    and pt2_imp :: "'h2 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
begin

definition "mi_imp H1 H2 Si = do {
   Gc \<leftarrow> cand_csr_imp npts1_imp pt1_imp npts2_imp pt2_imp H1 H2 n;
   Vi \<leftarrow> Array.new n False;
   Fr \<leftarrow> Array.new (Suc n) 0;
   Bf \<leftarrow> Array.new (Suc n) 0;
   Da \<leftarrow> Array.new n 0;
   Pa \<leftarrow> Array.new n 0;
   Ra \<leftarrow> Array.new n 0;
   unweighted_intersection_imp_loop_spec.mi_loop_imp sins_imp sdel_imp 
     (aug_path_imp Gc Vi Fr Bf Da Pa) Si Ra }"

end

subsection \<open>Correctness\<close>

text \<open>First for matroids on the ids below \<open>n\<close> themselves.\<close>

locale matroid_intersection_imp_ids =
  matroid_intersection_imp_ids_spec n smemb_imp ins1_imp exch1_imp ins2_imp exch2_imp sins_imp sdel_imp
    npts1_imp pt1_imp npts2_imp pt2_imp +
  imp_nat_set n sol_assn smemb_imp sins_imp sdel_imp +
  unweighted_intersection_exchange_csr where set_insert = "Set.insert :: nat \<Rightarrow> nat set \<Rightarrow> nat set"
    and set_delete = "\<lambda> x X. X - {x}" and to_set = "\<lambda> X. X" and set_invar = finite
    and set_empty = "{}" and set_memb = "\<lambda> x X. x \<in> X" and carrier_list = "[0..<n]"
    and carrier = "{0..<n}" +
  o1: exchange_oracle_imp n orcl_prep1 ins_orcl1 exch_orcl1 sol_assn ins1_imp exch1_imp ost1 +
  o2: exchange_oracle_imp n orcl_prep2 ins_orcl2 exch_orcl2 sol_assn ins2_imp exch2_imp ost2 +
  c: exchange_candidates_imp n indep1 orcl_prep1 ins_orcl1 exch_orcl1 pts1 pst1 npts1_imp pt1_imp
    indep2 orcl_prep2 ins_orcl2 exch_orcl2 pts2 pst2 npts2_imp pt2_imp
  for n smemb_imp ins1_imp exch1_imp ins2_imp exch2_imp sins_imp sdel_imp 
    npts1_imp pt1_imp npts2_imp pt2_imp 
    sol_assn ost1 ost2 pts1 pst1 pts2 pst2
begin

sublocale m: unweighted_intersection_exchange_imp where n = n and smemb_imp = smemb_imp
  and ins1_imp = ins1_imp and exch1_imp = exch1_imp and ins2_imp = ins2_imp 
  and exch2_imp = exch2_imp and sol_assn = sol_assn and sins_imp = sins_imp 
  and sdel_imp = sdel_imp and ost1 = ost1 and ost2 = ost2 and orcl_prep1 = orcl_prep1 
  and ins_orcl1 = ins_orcl1 and exch_orcl1 = exch_orcl1 and orcl_prep2 = orcl_prep2 
  and ins_orcl2 = ins_orcl2 and exch_orcl2 = exch_orcl2 and indep1 = indep1 and indep2 = indep2 
  and es0 = "cand_list pts1 pts2 n"
  by (rule unweighted_intersection_exchange_imp.intro[OF imp_nat_set_axioms 
        unweighted_intersection_exchange_csr_axioms o1.exchange_oracle_imp_axioms
        o2.exchange_oracle_imp_axioms unweighted_intersection_exchange_imp_axioms.intro[OF 
        c.cand_bound c.cand_sorted c.cand_cover1 c.cand_cover2]])

text \<open>The whole program.\<close>

theorem mi_imp_correct:
  "<(sol_assn {} Si) * ost1 * ost2 * pst1 H1 * pst2 H2> mi_imp H1 H2 Si 
   <\<lambda> _. \<exists>\<^sub>A X. sol_assn X Si * ost1 * ost2 * pst1 H1 * pst2 H2 * true * \<up>(is_max X)>"
proof-
  let ?F = "sol_assn {} Si * ost1 * ost2"
  have cand: "<(sol_assn {} Si) * ost1 * ost2 * pst1 H1 * pst2 H2> cand_csr_imp npts1_imp pt1_imp npts2_imp pt2_imp H1 H2 n
              <\<lambda> Gc. ?F * pst1 H1 * pst2 H2 * bcsr_assn (build_nhlists (cand_list pts1 pts2 n)) Gc>"
    by (rule ht_frame_ac[OF c.cand_csr_rule, where R = ?F]) (simp only: star_aci, rule ent_refl)+
  show ?thesis
    unfolding mi_imp_def
    by (rule ht_bind[OF cand], (rule alloc_bind[OF len_assn_new])+,
        rule ht_frame_ac[OF m.loop_correct, where R = "pst1 H1 * pst2 H2"]) 
       ((simp only: m.mst_def work_assn_def parr_len star_aci, rule ent_refl),
        sep_auto simp: m.mst_def)
qed

end

subsection \<open>Matroids on Any Type\<close>

text \<open>The matroids live on any type \<open>'a\<close>. Only the CSR of the candidate graph and its search
  need nats: a bijection \<open>idx\<close> from the carrier onto the ids below \<open>n\<close>, with inverse \<open>elt\<close>,
  names the elements. Solution set, oracles and partner queries work on elements; the
  algorithm of the previous subsection runs on the ids, with every operation composed with
  \<open>elt\<close> and the partners mapped by \<open>idx\<close>. For the proof, the matroids are pulled back to the
  ids and a maximum common independent set on the ids is mapped back by \<open>elt\<close>.\<close>

definition "pt_ids_imp idx elt pt_imp H i k = do { y \<leftarrow> pt_imp H (elt i) k; return (idx y) }"

locale matroid_intersection_imp_spec =
  fixes n :: nat
    and idx :: "'a \<Rightarrow> nat"
    and elt :: "nat \<Rightarrow> 'a"
    and smemb_imp :: "'a \<Rightarrow> 'si \<Rightarrow> bool Heap"
    and ins1_imp :: "'si \<Rightarrow> 'a \<Rightarrow> bool Heap"
    and exch1_imp :: "'si \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool Heap"
    and ins2_imp :: "'si \<Rightarrow> 'a \<Rightarrow> bool Heap"
    and exch2_imp :: "'si \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool Heap"
    and sins_imp :: "'a \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and sdel_imp :: "'a \<Rightarrow> 'si \<Rightarrow> unit Heap"
    and npts1_imp :: "'h1 \<Rightarrow> 'a \<Rightarrow> nat Heap"
    and pt1_imp :: "'h1 \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a Heap"
    and npts2_imp :: "'h2 \<Rightarrow> 'a \<Rightarrow> nat Heap"
    and pt2_imp :: "'h2 \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a Heap"
begin

sublocale ids: matroid_intersection_imp_ids_spec n "\<lambda> i. smemb_imp (elt i)" 
  "\<lambda> Si i. ins1_imp Si (elt i)" "\<lambda> Si i j. exch1_imp Si (elt i) (elt j)"
  "\<lambda> Si i. ins2_imp Si (elt i)" "\<lambda> Si i j. exch2_imp Si (elt i) (elt j)"
  "\<lambda> i. sins_imp (elt i)" "\<lambda> i. sdel_imp (elt i)" 
  "\<lambda> H i. npts1_imp H (elt i)" "pt_ids_imp idx elt pt1_imp" 
  "\<lambda> H i. npts2_imp H (elt i)" "pt_ids_imp idx elt pt2_imp" .

definition "mi_imp H1 H2 Si = ids.mi_imp H1 H2 Si"

end

locale matroid_ids =
  fixes carrier :: "'a set" and idx :: "'a \<Rightarrow> nat" and elt :: "nat \<Rightarrow> 'a" and n :: nat
  assumes idx_bij: "bij_betw idx carrier {0..<n}"
    and elt_idx: "x \<in> carrier \<Longrightarrow> elt (idx x) = x"
begin

lemma idx_in: "x \<in> carrier \<Longrightarrow> idx x < n"
  using bij_betw_apply[OF idx_bij] by simp

lemma elt_in_idx: "i < n \<Longrightarrow> elt i \<in> carrier \<and> idx (elt i) = i"
proof-
  assume "i < n"
  then have "i \<in> idx ` carrier"
    using bij_betw_imp_surj_on[OF idx_bij] by simp
  then obtain x where "i = idx x" "x \<in> carrier"
    by (rule imageE)
  then show ?thesis 
    using elt_idx by simp
qed

lemma elt_in: "i < n \<Longrightarrow> elt i \<in> carrier"
  by (rule conjunct1[OF elt_in_idx])

lemma idx_elt: "i < n \<Longrightarrow> idx (elt i) = i"
  by (rule conjunct2[OF elt_in_idx])

lemma elt_inj: "inj_on elt {0..<n}"
proof(rule inj_onI)
  fix i j
  assume a: "i \<in> {0..<n}" "j \<in> {0..<n}" "elt i = elt j"
  then have "idx (elt i) = idx (elt j)"
    by simp
  then show "i = j"
    using a(1,2) idx_elt by simp
qed

lemma elt_card: "I \<subseteq> {0..<n} \<Longrightarrow> card (elt ` I) = card I"
  by (rule card_image[OF inj_on_subset[OF elt_inj]])

lemma elt_mem: "\<lbrakk>I \<subseteq> {0..<n}; i < n\<rbrakk> \<Longrightarrow> elt i \<in> elt ` I \<longleftrightarrow> i \<in> I"
  using inj_on_image_mem_iff[OF elt_inj] by simp

lemma elt_diff: 
  assumes "I \<subseteq> {0..<n}" "i < n" 
  shows "elt ` (I - {i}) = elt ` I - {elt i}"
proof-
  have "elt ` (I - {i}) = elt ` I - elt ` {i}"
    by (rule inj_on_image_set_diff[OF elt_inj]) (use assms in auto)
  then show ?thesis 
    by simp
qed

lemma elt_sub: "I \<subseteq> {0..<n} \<Longrightarrow> elt ` I \<subseteq> carrier"
  using elt_in by auto

lemma elt_surj: "X \<subseteq> carrier \<Longrightarrow> idx ` X \<subseteq> {0..<n} \<and> elt ` idx ` X = X"
proof-
  assume a: "X \<subseteq> carrier"
  have "elt ` idx ` X = (\<lambda> x. x) ` X"
    unfolding image_image by (rule image_cong[OF refl]) (use a elt_idx in blast)
  then show ?thesis
    using a idx_in by auto
qed

definition "pull indep I = (I \<subseteq> {0..<n} \<and> indep (elt ` I))"

definition "sol_ids sol_assn I Si = sol_assn (elt ` I) Si * \<up>(I \<subseteq> {0..<n})"

lemma pull_matroid:
  assumes "matroid carrier indep"
  shows "matroid {0..<n} (pull indep)"
proof-
  interpret matroid carrier indep 
    by (rule assms)
  show ?thesis
  proof(unfold_locales, goal_cases)
    case 1
    then show ?case by simp
  next
    case (2 X)
    then show ?case by (simp add: pull_def)
  next
    case 3
    have "indep {}"
      using indep_ex indep_subset empty_subsetI by metis
    then have "pull indep {}"
      by (simp add: pull_def)
    then show ?case by (rule exI)
  next
    case (4 X Y)
    have sub: "X \<subseteq> {0..<n}" and i: "indep (elt ` X)"
      using 4(1) by (simp_all add: pull_def)
    have "indep (elt ` Y)" 
      by (rule indep_subset[OF i image_mono[OF 4(2)]])
    moreover have "Y \<subseteq> {0..<n}"
      using 4(2) sub by (rule subset_trans)
    ultimately show ?case
      by (simp add: pull_def)
  next
    case (5 X Y)
    have sub: "X \<subseteq> {0..<n}" "Y \<subseteq> {0..<n}"
      using 5(1,2) by (simp_all add: pull_def)
    have ind: "indep (elt ` X)" "indep (elt ` Y)"
      using 5(1,2) by (simp_all add: pull_def)
    have "card (elt ` Y) < card (elt ` X)"
      using 5(3) elt_card[OF sub(1)] elt_card[OF sub(2)] by simp
    then have "\<exists> x \<in> elt ` X - elt ` Y. indep (Set.insert x (elt ` Y))"
      by (rule augment[OF ind])
    then obtain x' where x': "x' \<in> elt ` X - elt ` Y" "indep (Set.insert x' (elt ` Y))"
      by (elim bexE)
    then obtain x where x: "x \<in> X" "x' = elt x"
      by (elim DiffE imageE) 
    have "x \<notin> Y"
      using x x'(1) by (auto simp: image_iff)
    moreover have "x < n"
      using x(1) sub(1) by auto
    moreover have "pull indep (Set.insert x Y)"
      unfolding pull_def using calculation(2) x x'(2) sub by simp
    ultimately show ?case
      using x(1) by (intro bexI[of _ x]) simp_all
  qed
qed

lemma pull_max:
  assumes "\<And> X. indep1 X \<Longrightarrow> X \<subseteq> carrier" "I \<subseteq> {0..<n}"
    "\<nexists> J. pull indep1 J \<and> pull indep2 J \<and> card J > card I"
  shows "\<nexists> Y. indep1 Y \<and> indep2 Y \<and> card Y > card (elt ` I)"
proof
  assume "\<exists> Y. indep1 Y \<and> indep2 Y \<and> card Y > card (elt ` I)"
  then obtain Y where Y: "indep1 Y" "indep2 Y" "card Y > card (elt ` I)"
    by (elim exE conjE)
  have J: "idx ` Y \<subseteq> {0..<n}" "elt ` idx ` Y = Y"
    using elt_surj[OF assms(1)[OF Y(1)]] by simp_all
  have "pull indep1 (idx ` Y) \<and> pull indep2 (idx ` Y) \<and> card (idx ` Y) > card I"
    using J Y elt_card[OF J(1)] elt_card[OF assms(2)] unfolding pull_def by simp
  then have "\<exists> J. pull indep1 J \<and> pull indep2 J \<and> card J > card I"
    by (rule exI)
  with assms(3) show False
    by (rule notE)
qed

end

text \<open>An oracle on the elements with its partner query.\<close>

locale indexed_oracle_imp =
  matroid_ids carrier idx elt n +
  indep_oracle orcl_prep ins_orcl exch_orcl carrier indep "\<lambda> X. X" finite
  for carrier :: "'a set" and idx elt n and orcl_prep :: "'a set \<Rightarrow> 'o" 
    and ins_orcl exch_orcl indep +
  fixes sol_assn :: "'a set \<Rightarrow> 'si \<Rightarrow> assn"
    and ins_imp :: "'si \<Rightarrow> 'a \<Rightarrow> bool Heap"
    and exch_imp :: "'si \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool Heap"
    and ost :: assn
    and pts :: "'a \<Rightarrow> 'a list"
    and pst :: "'h \<Rightarrow> assn"
    and npts_imp :: "'h \<Rightarrow> 'a \<Rightarrow> nat Heap"
    and pt_imp :: "'h \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a Heap"
  assumes ins_imp:
    "<(sol_assn X Si) * ost * \<up>(y \<in> carrier)> ins_imp Si y
     <\<lambda> r. sol_assn X Si * ost * \<up>(r = ins_orcl (orcl_prep X) y)>"
    and exch_imp:
    "<(sol_assn X Si) * ost * \<up>(x \<in> carrier \<and> y \<in> carrier)> exch_imp Si x y
     <\<lambda> r. sol_assn X Si * ost * \<up>(r = exch_orcl (orcl_prep X) x y)>"
    and pts_sorted: "x \<in> carrier \<Longrightarrow> sorted_wrt (<) (map idx (pts x))"
    and pts_bound: "\<lbrakk>x \<in> carrier; y \<in> set (pts x)\<rbrakk> \<Longrightarrow> y \<in> carrier"
    and pts_cover: 
    "\<lbrakk>finite X; X \<subseteq> carrier; indep X; x \<in> X; y \<in> carrier - X;
      \<not> ins_orcl (orcl_prep X) y; exch_orcl (orcl_prep X) x y\<rbrakk> 
     \<Longrightarrow> y \<in> set (pts x) \<and> x \<in> set (pts y)"
    and npts_imp: "<pst H * \<up>(x \<in> carrier)> npts_imp H x <\<lambda> r. pst H * \<up>(r = length (pts x))>"
    and pt_imp: 
    "<pst H * \<up>(x \<in> carrier \<and> k < length (pts x))> pt_imp H x k <\<lambda> r. pst H * \<up>(r = pts x ! k)>"
begin

text \<open>The oracle and the partners on the ids.\<close>

definition "prep_ids I = orcl_prep (elt ` I)"

definition "ins_ids ox i = ins_orcl ox (elt i)"

definition "exch_ids ox i j = exch_orcl ox (elt i) (elt j)"

definition "pts_ids i = (if i < n then map idx (pts (elt i)) else [])"

lemma ids_matroid: "matroid {0..<n} (pull indep)"
  by (rule pull_matroid[OF matroid_axioms])

lemma ids_indep_oracle: "indep_oracle prep_ids ins_ids exch_ids {0..<n} (pull indep) (\<lambda> X. X) finite"
proof(intro indep_oracle.intro indep_oracle_axioms.intro ids_matroid, goal_cases)
  case (1 I y)
  have y: "y < n" "y \<notin> I"
    using 1(4) by simp_all
  have yc: "elt y \<in> carrier - elt ` I"
    using elt_in[OF y(1)] elt_mem[OF 1(2) y(1)] y(2) by simp
  have i: "finite (elt ` I)" "elt ` I \<subseteq> carrier" "indep (elt ` I)"
    using 1(1) elt_sub[OF 1(2)] 1(3) by (simp_all add: pull_def)
  have "Set.insert y I \<subseteq> {0..<n}"
    using 1(2) y(1) by simp
  then show ?case
    using ins_orcl[OF i yc] by (simp add: ins_ids_def prep_ids_def pull_def)
next
  case (2 I x y)
  have y: "y < n" "y \<notin> I"
    using 2(4) by simp_all
  have xn: "x < n"
    using 2(2,5) by auto
  have yc: "elt y \<in> carrier - elt ` I"
    using elt_in[OF y(1)] elt_mem[OF 2(2) y(1)] y(2) by simp
  have i: "finite (elt ` I)" "elt ` I \<subseteq> carrier" "indep (elt ` I)"
    using 2(1) elt_sub[OF 2(2)] 2(3) by (simp_all add: pull_def)
  have x: "elt x \<in> elt ` I"
    using 2(5) by simp
  have nd: "\<not> indep (Set.insert (elt y) (elt ` I))"
    using 2(6) 2(2) y(1) by (simp add: pull_def)
  have "Set.insert y (I - {x}) \<subseteq> {0..<n}"
    using 2(2) y(1) by auto
  then show ?case
    using exch_orcl[OF i yc x nd] elt_diff[OF 2(2) xn] 
    by (simp add: exch_ids_def prep_ids_def pull_def)
qed

lemma ids_oracle_imp: 
  "exchange_oracle_imp n prep_ids ins_ids exch_ids (sol_ids sol_assn) 
     (\<lambda> Si i. ins_imp Si (elt i)) (\<lambda> Si i j. exch_imp Si (elt i) (elt j)) ost"
proof(intro exchange_oracle_imp.intro, goal_cases)
  case (1 X Si y)
  have r: "y < n \<Longrightarrow> <(sol_assn Y Si) * ost> ins_imp Si (elt y) 
           <\<lambda> r. sol_assn Y Si * ost * \<up>(r = ins_orcl (orcl_prep Y) (elt y))>" for Y
    using ins_imp[of Y Si "elt y"] by (simp add: elt_in)
  show ?case 
    unfolding sol_ids_def prep_ids_def ins_ids_def by (sep_auto heap: r)
next
  case (2 X Si x y)
  have r: "\<lbrakk>x < n; y < n\<rbrakk> \<Longrightarrow> <(sol_assn Y Si) * ost> exch_imp Si (elt x) (elt y) 
           <\<lambda> r. sol_assn Y Si * ost * \<up>(r = exch_orcl (orcl_prep Y) (elt x) (elt y))>" for Y
    using exch_imp[of Y Si "elt x" "elt y"] by (simp add: elt_in)
  show ?case 
    unfolding sol_ids_def prep_ids_def exch_ids_def by (sep_auto heap: r)
qed

lemma ids_partners: 
  "exchange_partners_imp n (pull indep) prep_ids ins_ids exch_ids pts_ids pst 
     (\<lambda> H i. npts_imp H (elt i)) (pt_ids_imp idx elt pt_imp)"
proof(intro exchange_partners_imp.intro, goal_cases)
  case (1 x)
  then show ?case 
    unfolding pts_ids_def using pts_sorted[OF elt_in] by simp
next
  case (2 y x)
  then show ?case 
    unfolding pts_ids_def using pts_bound[OF elt_in] idx_in by (auto split: if_splits)
next
  case (3 X x y)
  have y: "elt y \<in> carrier - elt ` X"
    using elt_in[OF 3(5)] elt_mem[OF 3(2) 3(5)] 3(7) by simp
  have x: "elt x \<in> elt ` X"
    using 3(6) by simp
  have i: "finite (elt ` X)" "elt ` X \<subseteq> carrier" "indep (elt ` X)" 
    using 3(1) elt_sub[OF 3(2)] 3(3) by (simp_all add: pull_def)
  have c: "elt y \<in> set (pts (elt x)) \<and> elt x \<in> set (pts (elt y))"
    using 3(8,9) unfolding ins_ids_def exch_ids_def prep_ids_def by (rule pts_cover[OF i x y])
  have "idx (elt y) \<in> set (pts_ids x) \<and> idx (elt x) \<in> set (pts_ids y)"
    unfolding pts_ids_def set_map using 3(4,5) by (intro conjI) (simp_all add: c)
  then show ?case
    using idx_elt[OF 3(4)] idx_elt[OF 3(5)] by simp
next
  case (4 H x)
  have r: "x < n \<Longrightarrow> <pst H> npts_imp H (elt x) <\<lambda> r. pst H * \<up>(r = length (pts (elt x)))>"
    using npts_imp[of H "elt x"] by (simp add: elt_in)
  show ?case 
    unfolding pts_ids_def by (sep_auto heap: r)
next
  case (5 H x k)
  have r: "\<lbrakk>x < n; k < length (pts (elt x))\<rbrakk> \<Longrightarrow> 
           <pst H> pt_imp H (elt x) k <\<lambda> r. pst H * \<up>(r = pts (elt x) ! k)>"
    using pt_imp[of H "elt x" k] by (simp add: elt_in)
  show ?case 
    unfolding pt_ids_imp_def pts_ids_def by (sep_auto heap: r)
qed

end

text \<open>The algorithm for two matroids on \<open>'a\<close>. The solution set is an assertion on sets of
  elements, with membership test, insertion and deletion of elements.\<close>

locale matroid_intersection_imp =
  matroid_intersection_imp_spec n idx elt smemb_imp ins1_imp exch1_imp ins2_imp exch2_imp 
    sins_imp sdel_imp npts1_imp pt1_imp npts2_imp pt2_imp +
  o1: indexed_oracle_imp carrier idx elt n orcl_prep1 ins_orcl1 exch_orcl1 indep1 sol_assn 
    ins1_imp exch1_imp ost1 pts1 pst1 npts1_imp pt1_imp +
  o2: indexed_oracle_imp carrier idx elt n orcl_prep2 ins_orcl2 exch_orcl2 indep2 sol_assn 
    ins2_imp exch2_imp ost2 pts2 pst2 npts2_imp pt2_imp
  for n idx elt smemb_imp ins1_imp exch1_imp ins2_imp exch2_imp sins_imp sdel_imp 
    npts1_imp pt1_imp npts2_imp pt2_imp carrier orcl_prep1 ins_orcl1 exch_orcl1 indep1 sol_assn ost1 pts1 pst1
    orcl_prep2 ins_orcl2 exch_orcl2 indep2 ost2 pts2 pst2 +
  assumes smemb_rule: 
    "<(sol_assn X Si) * \<up>(x \<in> carrier)> smemb_imp x Si <\<lambda> r. sol_assn X Si * \<up>(r = (x \<in> X))>"
    and sins_rule: 
    "<(sol_assn X Si) * \<up>(x \<in> carrier)> sins_imp x Si <\<lambda> _. sol_assn (Set.insert x X) Si>"
    and sdel_rule: 
    "<(sol_assn X Si) * \<up>(x \<in> carrier)> sdel_imp x Si <\<lambda> _. sol_assn (X - {x}) Si>"
begin

sublocale double_matroid carrier indep1 indep2
  by (rule double_matroid.intro) (rule o1.matroid_axioms o2.matroid_axioms)+

lemma ids_set: 
  "imp_nat_set n (o1.sol_ids sol_assn) (\<lambda> i. smemb_imp (elt i)) (\<lambda> i. sins_imp (elt i)) 
     (\<lambda> i. sdel_imp (elt i))"
proof(intro imp_nat_set.intro, goal_cases)
  case (1 X Si)
  then show ?case 
    unfolding o1.sol_ids_def by sep_auto
next
  case (2 X Si x)
  have r: "x < n \<Longrightarrow> <(sol_assn Y Si)> smemb_imp (elt x) Si <\<lambda> r. sol_assn Y Si * \<up>(r = (elt x \<in> Y))>" 
    for Y
    using smemb_rule[of Y Si "elt x"] by (simp add: o1.elt_in)
  show ?case 
    unfolding o1.sol_ids_def by (sep_auto simp: o1.elt_mem heap: r)
next
  case (3 X Si x)
  have r: "x < n \<Longrightarrow> <(sol_assn Y Si)> sins_imp (elt x) Si <\<lambda> _. sol_assn (Set.insert (elt x) Y) Si>" 
    for Y
    using sins_rule[of Y Si "elt x"] by (simp add: o1.elt_in)
  show ?case 
    unfolding o1.sol_ids_def by (sep_auto heap: r)
next
  case (4 X Si x)
  have r: "x < n \<Longrightarrow> <(sol_assn Y Si)> sdel_imp (elt x) Si <\<lambda> _. sol_assn (Y - {elt x}) Si>" 
    for Y
    using sdel_rule[of Y Si "elt x"] by (simp add: o1.elt_in)
  show ?case 
    unfolding o1.sol_ids_def by (sep_auto simp: o1.elt_diff heap: r)
qed

text \<open>The instance on the ids.\<close>

lemma ids_imp:
  "matroid_intersection_imp_ids o1.prep_ids o1.ins_ids o1.exch_ids o2.prep_ids o2.ins_ids o2.exch_ids
     (o1.pull indep1) (o1.pull indep2) n (\<lambda> i. smemb_imp (elt i)) (\<lambda> Si i. ins1_imp Si (elt i))
     (\<lambda> Si i j. exch1_imp Si (elt i) (elt j)) (\<lambda> Si i. ins2_imp Si (elt i))
     (\<lambda> Si i j. exch2_imp Si (elt i) (elt j)) (\<lambda> i. sins_imp (elt i)) (\<lambda> i. sdel_imp (elt i))
     (\<lambda> H i. npts1_imp H (elt i)) (pt_ids_imp idx elt pt1_imp) 
     (\<lambda> H i. npts2_imp H (elt i)) (pt_ids_imp idx elt pt2_imp) (o1.sol_ids sol_assn)
     ost1 ost2 o1.pts_ids pst1 o2.pts_ids pst2"
  apply (intro matroid_intersection_imp_ids.intro unweighted_intersection_exchange_csr.intro
      unweighted_intersection_exchange_matroids.intro double_matroid.intro
      unweighted_intersection_exchange_matroids_axioms.intro exchange_candidates_imp.intro)
  apply (rule ids_set o1.ids_matroid o2.ids_matroid o1.ids_indep_oracle o2.ids_indep_oracle)+
  apply (simp_all only: finite_insert finite_Diff finite.emptyI set_upt distinct_upt refl simp_thms)
  apply (rule o1.ids_oracle_imp o2.ids_oracle_imp o1.ids_partners o2.ids_partners)+
  done

theorem mi_imp_correct:
  "<(sol_assn {} Si) * ost1 * ost2 * pst1 H1 * pst2 H2> mi_imp H1 H2 Si 
   <\<lambda> _. \<exists>\<^sub>A X. sol_assn X Si * ost1 * ost2 * pst1 H1 * pst2 H2 * true * \<up>(is_max X)>"
proof-
  interpret m: matroid_intersection_imp_ids where n = n 
    and smemb_imp = "\<lambda> i. smemb_imp (elt i)" and ins1_imp = "\<lambda> Si i. ins1_imp Si (elt i)" 
    and exch1_imp = "\<lambda> Si i j. exch1_imp Si (elt i) (elt j)" 
    and ins2_imp = "\<lambda> Si i. ins2_imp Si (elt i)" 
    and exch2_imp = "\<lambda> Si i j. exch2_imp Si (elt i) (elt j)" 
    and sins_imp = "\<lambda> i. sins_imp (elt i)" and sdel_imp = "\<lambda> i. sdel_imp (elt i)" 
    and npts1_imp = "\<lambda> H i. npts1_imp H (elt i)" and pt1_imp = "pt_ids_imp idx elt pt1_imp" 
    and npts2_imp = "\<lambda> H i. npts2_imp H (elt i)" and pt2_imp = "pt_ids_imp idx elt pt2_imp" 
    and sol_assn = "o1.sol_ids sol_assn" and ost1 = ost1 and ost2 = ost2 
    and orcl_prep1 = o1.prep_ids and ins_orcl1 = o1.ins_ids and exch_orcl1 = o1.exch_ids 
    and orcl_prep2 = o2.prep_ids and ins_orcl2 = o2.ins_ids and exch_orcl2 = o2.exch_ids 
    and indep1 = "o1.pull indep1" and indep2 = "o1.pull indep2" 
    and pts1 = o1.pts_ids and pst1 = pst1 and pts2 = o2.pts_ids and pst2 = pst2
    by (rule ids_imp)
  have mx: "is_max (elt ` I)" if a: "m.is_max I" for I
  proof-
    have I: "I \<subseteq> {0..<n}" "indep1 (elt ` I)" "indep2 (elt ` I)" 
      using a by (simp_all add: m.is_max_def o1.pull_def)
    have "\<nexists> J. o1.pull indep1 J \<and> o1.pull indep2 J \<and> card J > card I" 
      using a by (simp add: m.is_max_def)
    then have "\<nexists> Y. indep1 Y \<and> indep2 Y \<and> card Y > card (elt ` I)"
      using o1.pull_max[of indep1 I indep2, OF o1.indep_subset_carrier I(1)] by simp
    then show ?thesis
      using I(2,3) by (simp add: is_max_def)
  qed
  show ?thesis
    unfolding mi_imp_def
  proof(rule ht_cons[OF _ _ m.mi_imp_correct], goal_cases)
    case 1
    then show ?case
      unfolding o1.sol_ids_def by sep_auto
  next
    case (2 r)
    then show ?case
      unfolding o1.sol_ids_def by (sep_auto intro: mx)
  qed
qed

end

end
