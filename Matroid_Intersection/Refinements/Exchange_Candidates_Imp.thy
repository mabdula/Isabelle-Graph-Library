theory Exchange_Candidates_Imp
  imports Exchange_Oracles_Imp Directed_Set_Graphs.CSR_Neighbour_Lists Data_Structures.More_Lists
begin

section \<open>The Candidate Graph from Exchange Partners\<close>

text \<open>The constant candidate graph of the exchange graph search, built once from the partner
  lists of the two oracles: the neighbours of an element are the union of its partners in both
  matroids, in ascending order. It contains every exchange edge of every solution. It is a CSR
  (@{locale csr_concat}): the array of the block ends and the array of the
  neighbours. Both are filled in two passes over the elements, each merging the two partner
  lists of an element through the partner queries: the first pass counts the neighbours and
  writes the block ends, the second writes the neighbours into the array allocated in between.
  The time is linear in the size of the partner lists.\<close>

subsection \<open>Code\<close>

fun merge_uniq :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "merge_uniq [] ys = ys"
| "merge_uniq xs [] = xs"
| "merge_uniq (x # xs) (y # ys) =
     (if x < y then x # merge_uniq xs (y # ys)
      else if y < x then y # merge_uniq (x # xs) ys
      else x # merge_uniq xs ys)"

definition cand_list :: "(nat \<Rightarrow> nat list) \<Rightarrow> (nat \<Rightarrow> nat list) \<Rightarrow> nat
    \<Rightarrow> (nat \<times> nat) list" where
  "cand_list p1 p2 n = concat (map (\<lambda> u. map (Pair u) (merge_uniq (p1 u) (p2 u))) [0..<n])"

text \<open>The merge of the entries \<open>i..<a\<close> and \<open>j..<b\<close> of two partner lists, read through
    the
  queries \<open>q1\<close> and \<open>q2\<close>: counting the merged entries, starting from \<open>c\<close>, and
    writing them
  into an array from position \<open>p\<close> on, returning the position after them.\<close>

partial_function (heap) merge_cnt ::
  "(nat \<Rightarrow> nat Heap) \<Rightarrow> (nat \<Rightarrow> nat Heap) \<Rightarrow> nat \<Rightarrow> nat
    \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "merge_cnt q1 q2 a b i j c =
     (if i < a then
        if j < b then do {
          x \<leftarrow> q1 i;
          y \<leftarrow> q2 j;
          if x < y then merge_cnt q1 q2 a b (Suc i) j (Suc c)
          else if y < x then merge_cnt q1 q2 a b i (Suc j) (Suc c)
          else merge_cnt q1 q2 a b (Suc i) (Suc j) (Suc c) }
        else return (c + (a - i))
      else return (c + (b - j)))"

partial_function (heap) merge_wr ::
  "(nat \<Rightarrow> nat Heap) \<Rightarrow> (nat \<Rightarrow> nat Heap) \<Rightarrow> nat \<Rightarrow> nat
    \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
   nat Heap" where
  "merge_wr q1 q2 a b G i j p =
     (if i < a then do {
        x \<leftarrow> q1 i;
        if j < b then do {
          y \<leftarrow> q2 j;
          if x < y then do { Array.upd p x G; merge_wr q1 q2 a b G (Suc i) j (Suc p) }
          else if y < x then do { Array.upd p y G; merge_wr q1 q2 a b G i (Suc j) (Suc p) }
          else do { Array.upd p x G; merge_wr q1 q2 a b G (Suc i) (Suc j) (Suc p) } }
        else do { Array.upd p x G; merge_wr q1 q2 a b G (Suc i) j (Suc p) } }
      else if j < b then do { y \<leftarrow> q2 j; Array.upd p y G; merge_wr q1 q2 a b G i (Suc j) (Suc p) }
      else return p)"

declare merge_cnt.simps[code] merge_wr.simps[code]

text \<open>The CSR is built vertex by vertex (@{const csr_concat_build_imp}): the steps of the two passes
  merge the two partner lists of an element.\<close>

definition "cand_csr_imp nq1 q1 nq2 q2 H1 H2 n = csr_concat_build_imp 0
   (\<lambda> u c. do {
      a \<leftarrow> nq1 H1 u;
      b \<leftarrow> nq2 H2 u;
      merge_cnt (q1 H1 u) (q2 H2 u) a b 0 0 c })
   (\<lambda> u Ga p. do {
      a \<leftarrow> nq1 H1 u;
      b \<leftarrow> nq2 H2 u;
      merge_wr (q1 H1 u) (q2 H2 u) a b Ga 0 0 p })
   n"

subsection \<open>Correctness\<close>

lemma set_merge_uniq: "set (merge_uniq xs ys) = set xs \<union> set ys"
  by (induction xs ys rule: merge_uniq.induct) auto

lemma merge_uniq_Nil2: "merge_uniq xs [] = xs"
  by (cases xs) simp_all

lemma sorted_merge_uniq:
  "\<lbrakk>sorted_wrt (<) xs; sorted_wrt (<) ys\<rbrakk> \<Longrightarrow> sorted_wrt (<) (merge_uniq xs ys)"
proof(induction xs ys rule: merge_uniq.induct)
  case (3 x xs y ys)
  have "\<forall> z \<in> set ys. y < z" "\<forall> z \<in> set xs. x < z"
    using 3(4,5)
    by simp_all
  then show ?case
    using 3
    by (auto simp: set_merge_uniq)
qed simp_all

lemma nbrs_concat_Pair:
  "nbrs (concat (map (\<lambda> x. map (Pair x) (L x)) xs)) u = concat (map (\<lambda> x. if x = u then L x else [])
    xs)"
  by (induction xs) (simp_all add: nbrs_def filter_map comp_def)

lemma nbrs_cand_list: "nbrs (cand_list p1 p2 n) u = (if u < n then merge_uniq (p1 u) (p2 u) else [])"
  by (simp add: cand_list_def nbrs_concat_Pair concat_if_dist)

lemma mem_cand_list:
  "(u, v) \<in> set (cand_list p1 p2 n) \<longleftrightarrow> u < n \<and> (v \<in> set (p1 u) \<or> v \<in> set (p2
    u))"
  by (auto simp: cand_list_def set_merge_uniq)

text \<open>The merging loops, for any two lists read through two queries.\<close>

lemma merge_cnt_rule:
  assumes "\<And> k. k < length xs \<Longrightarrow> <F> q1 k <\<lambda> r. F * \<up>(r = xs ! k)>"
    and "\<And> k. k < length ys \<Longrightarrow> <F> q2 k <\<lambda> r. F * \<up>(r = ys ! k)>"
  shows "\<lbrakk>i \<le> length xs; j \<le> length ys\<rbrakk> \<Longrightarrow>
         <F> merge_cnt q1 q2 (length xs) (length ys) i j c
         <\<lambda> r. F * \<up>(r = c + length (merge_uniq (drop i xs) (drop j ys)))>"
proof(induction "length xs - i + (length ys - j)" arbitrary: i j c rule: less_induct)
  case less
  show ?case
  proof(cases "i < length xs")
    case i: True
    note dx = Cons_nth_drop_Suc[symmetric, OF i]
    show ?thesis
    proof(cases "j < length ys")
      case j: True
      note dy = Cons_nth_drop_Suc[symmetric, OF j]
      note r1 = less.hyps[of "Suc i" j "Suc c", simplified, simplified i j less.prems]
      note r2 = less.hyps[of i "Suc j" "Suc c", simplified, simplified i j less.prems]
      note r3 = less.hyps[of "Suc i" "Suc j" "Suc c", simplified, simplified i j less.prems]
      show ?thesis
        using i j
        by (subst merge_cnt.simps)
           (sep_auto heap: assms(1)[OF i] assms(2)[OF j] r1[unfolded dy] r2[unfolded dx] r3 simp: dx dy)
    next
      case False
      then show ?thesis
        using i
        by (subst merge_cnt.simps) (sep_auto simp: merge_uniq_Nil2)
    qed
  next
    case False
    then show ?thesis
      using less.prems
      by (subst merge_cnt.simps) sep_auto
  qed
qed

lemma merge_wr_rule:
  assumes "\<And> k. k < length xs \<Longrightarrow> <F> q1 k <\<lambda> r. F * \<up>(r = xs ! k)>"
    and "\<And> k. k < length ys \<Longrightarrow> <F> q2 k <\<lambda> r. F * \<up>(r = ys ! k)>"
  shows "\<lbrakk>i \<le> length xs; j \<le> length ys;
          p + length (merge_uniq (drop i xs) (drop j ys)) \<le> length g\<rbrakk> \<Longrightarrow>
         <G \<mapsto>\<^sub>a g * F> merge_wr q1 q2 (length xs) (length ys) G i j p
         <\<lambda> r. G \<mapsto>\<^sub>a (take p g @ merge_uniq (drop i xs) (drop j ys) @
                      drop (p + length (merge_uniq (drop i xs) (drop j ys))) g) * F *
               \<up>(r = p + length (merge_uniq (drop i xs) (drop j ys)))>"
proof(induction "length xs - i + (length ys - j)" arbitrary: i j p g rule: less_induct)
  case less
  show ?case
  proof(cases "i < length xs")
    case i: True
    note dx = Cons_nth_drop_Suc[symmetric, OF i]
    show ?thesis
    proof(cases "j < length ys")
      case j: True
      note dy = Cons_nth_drop_Suc[symmetric, OF j]
      show ?thesis
      proof(cases "xs ! i < ys ! j")
        case lt: True
        let ?M = "merge_uniq (drop (Suc i) xs) (drop j ys)"
        have M: "merge_uniq (drop i xs) (drop j ys) = xs ! i # ?M" "p < length g"
          using lt less.prems(3)
          by (auto simp: dx dy)
        note r = less.hyps[of "Suc i" j "Suc p" "g[p := xs ! i]", simplified, simplified i j less.prems(1,2)
          less.prems(3)[unfolded M(1), simplified]]
        show ?thesis
          unfolding M(1) take_drop_upd_insert[OF M(2), symmetric]
          using i j lt M(2)
          by (subst merge_wr.simps) (sep_auto heap: assms(1)[OF i] assms(2)[OF j] r)
      next
        case nlt: False
        show ?thesis
        proof(cases "ys ! j < xs ! i")
          case gt: True
          let ?M = "merge_uniq (drop i xs) (drop (Suc j) ys)"
          have M: "merge_uniq (drop i xs) (drop j ys) = ys ! j # ?M" "p < length g"
            using nlt gt less.prems(3)
            by (auto simp: dx dy)
          note r = less.hyps[of i "Suc j" "Suc p" "g[p := ys ! j]", simplified, simplified i j less.prems(1,2)
            less.prems(3)[unfolded M(1), simplified]]
          show ?thesis
            unfolding M(1) take_drop_upd_insert[OF M(2), symmetric]
            using i j nlt gt M(2)
            by (subst merge_wr.simps) (sep_auto heap: assms(1)[OF i] assms(2)[OF j] r)
        next
          case ngt: False
          let ?M = "merge_uniq (drop (Suc i) xs) (drop (Suc j) ys)"
          have M: "merge_uniq (drop i xs) (drop j ys) = xs ! i # ?M" "p < length g"
            using nlt ngt less.prems(3)
            by (auto simp: dx dy)
          note r = less.hyps[of "Suc i" "Suc j" "Suc p" "g[p := xs ! i]", simplified, simplified i j less.prems(1,2)
            less.prems(3)[unfolded M(1), simplified]]
          show ?thesis
            unfolding M(1) take_drop_upd_insert[OF M(2), symmetric]
            using i j nlt ngt M(2)
            by (subst merge_wr.simps) (sep_auto heap: assms(1)[OF i] assms(2)[OF j] r)
        qed
      qed
    next
      case nj: False
      let ?M = "merge_uniq (drop (Suc i) xs) (drop j ys)"
      have M: "merge_uniq (drop i xs) (drop j ys) = xs ! i # ?M" "p < length g"
        using nj less.prems(3)
        by (auto simp: dx merge_uniq_Nil2)
      note r = less.hyps[of "Suc i" j "Suc p" "g[p := xs ! i]", simplified, simplified i less.prems(1,2)
        less.prems(3)[unfolded M(1), simplified]]
      show ?thesis
        unfolding M(1) take_drop_upd_insert[OF M(2), symmetric]
        using i nj M(2) less.prems(1,2)
        by (subst merge_wr.simps) (sep_auto heap: assms(1)[OF i] r)
    qed
  next
    case ni: False
    show ?thesis
    proof(cases "j < length ys")
      case j: True
      let ?M = "merge_uniq (drop i xs) (drop (Suc j) ys)"
      note dy = Cons_nth_drop_Suc[symmetric, OF j]
      have M: "merge_uniq (drop i xs) (drop j ys) = ys ! j # ?M" "p < length g"
        using ni less.prems(3)
        by (auto simp: dy)
      note r = less.hyps[of i "Suc j" "Suc p" "g[p := ys ! j]", simplified, simplified j less.prems(1,2)
        less.prems(3)[unfolded M(1), simplified]]
      show ?thesis
        unfolding M(1) take_drop_upd_insert[OF M(2), symmetric]
        using ni j M(2) less.prems(1,2)
        by (subst merge_wr.simps) (sep_auto heap: assms(2)[OF j] r)
    next
      case nj: False
      then show ?thesis
        using ni
        by (subst merge_wr.simps) sep_auto
    qed
  qed
qed


locale exchange_candidates_imp =
  p1: exchange_partners_imp n indep1 orcl_prep1 ins_orcl1 exch_orcl1 pts1 pst1 npts1_imp pt1_imp +
  p2: exchange_partners_imp n indep2 orcl_prep2 ins_orcl2 exch_orcl2 pts2 pst2 npts2_imp pt2_imp
  for n indep1 orcl_prep1 ins_orcl1 exch_orcl1 pts1 pst1 npts1_imp pt1_imp
    indep2 orcl_prep2 ins_orcl2 exch_orcl2 pts2 pst2 npts2_imp pt2_imp
begin

abbreviation "es0 \<equiv> cand_list pts1 pts2 n"

lemma nbrs_es0: "u < n \<Longrightarrow> nbrs es0 u = merge_uniq (pts1 u) (pts2 u)"
  by (simp add: nbrs_cand_list)

lemma pt1_rule:
  "\<lbrakk>k < length (pts1 u); u < n\<rbrakk> \<Longrightarrow>
   <pst1 H1 * pst2 H2> pt1_imp H1 u k <\<lambda> r. pst1 H1 * pst2 H2 * \<up>(r = pts1 u ! k)>"
  by (sep_auto heap: p1.pt_imp)

lemma pt2_rule:
  "\<lbrakk>k < length (pts2 u); u < n\<rbrakk> \<Longrightarrow>
   <pst1 H1 * pst2 H2> pt2_imp H2 u k <\<lambda> r. pst1 H1 * pst2 H2 * \<up>(r = pts2 u ! k)>"
  by (sep_auto heap: p2.pt_imp)

lemma cnt_rule:
  assumes "u < n"
  shows "<pst1 H1 * pst2 H2>
           merge_cnt (pt1_imp H1 u) (pt2_imp H2 u) (length (pts1 u)) (length (pts2 u)) 0 0 c
         <\<lambda> r. pst1 H1 * pst2 H2 * \<up>(r = c + length (nbrs es0 u))>"
  using merge_cnt_rule[where F = "pst1 H1 * pst2 H2" and xs = "pts1 u" and ys = "pts2 u"
      and ?q1.0 = "pt1_imp H1 u" and ?q2.0 = "pt2_imp H2 u" and i = 0 and j = 0 and c = c,
      OF pt1_rule[OF _ assms] pt2_rule[OF _ assms]]
  by (simp add: nbrs_es0 assms)

lemma wr_rule:
  assumes "u < n" and "p + length (nbrs es0 u) \<le> length g"
  shows "<G \<mapsto>\<^sub>a g * (pst1 H1 * pst2 H2)>
           merge_wr (pt1_imp H1 u) (pt2_imp H2 u) (length (pts1 u)) (length (pts2 u)) G 0 0 p
         <\<lambda> r. G \<mapsto>\<^sub>a (take p g @ nbrs es0 u @ drop (p + length (nbrs es0 u)) g) *
               (pst1 H1 * pst2 H2) * \<up>(r = p + length (nbrs es0 u))>"
  using merge_wr_rule[where F = "pst1 H1 * pst2 H2" and xs = "pts1 u" and ys = "pts2 u"
      and ?q1.0 = "pt1_imp H1 u" and ?q2.0 = "pt2_imp H2 u" and i = 0 and j = 0 and p = p and g = g
      and G = G, OF pt1_rule[OF _ assms(1)] pt2_rule[OF _ assms(1)]] assms(2)
  by (simp add: nbrs_es0 assms(1))

lemma cand_csr_rule:
  "<pst1 H1 * pst2 H2> cand_csr_imp npts1_imp pt1_imp npts2_imp pt2_imp H1 H2 n
   <\<lambda> (Ba, Ga). pst1 H1 * pst2 H2 * Ba \<mapsto>\<^sub>a map (csr_start (nbrs es0)) [0..<Suc n] *
                Ga \<mapsto>\<^sub>a csr_entries (nbrs es0) n>"
  unfolding cand_csr_imp_def
proof(rule csr_concat_build.csr_concat_build_rule, unfold_locales, goal_cases)
  case (1 u c)
  then show ?case
    by (sep_auto heap: p1.npts_imp p2.npts_imp cnt_rule)
next
  case (2 u p g G)
  then show ?case
    by (sep_auto heap: p1.npts_imp p2.npts_imp wr_rule)
qed

text \<open>The properties the exchange graph search requires of its candidate graph.\<close>

lemma cand_bound: "(u, v) \<in> set es0 \<Longrightarrow> u < n \<and> v < n"
  using p1.pts_bound p2.pts_bound
  by (auto simp: mem_cand_list)

lemma cand_sorted: "sorted_wrt (<) (nbrs es0 u)"
  by (simp add: nbrs_cand_list sorted_merge_uniq p1.pts_sorted p2.pts_sorted)

lemma cand_cover1:
  "\<lbrakk>finite X; X \<subseteq> {0..<n}; indep1 X; indep2 X; u < n; v < n; u \<in> X; v \<notin> X;
    \<not> ins_orcl1 (orcl_prep1 X) v; exch_orcl1 (orcl_prep1 X) u v\<rbrakk> \<Longrightarrow> (u, v) \<in> set es0"
  using p1.pts_cover[of X u v]
  by (auto simp: mem_cand_list)

lemma cand_cover2:
  "\<lbrakk>finite X; X \<subseteq> {0..<n}; indep1 X; indep2 X; u < n; v < n; u \<notin> X; v \<in> X;
    \<not> ins_orcl2 (orcl_prep2 X) u; exch_orcl2 (orcl_prep2 X) v u\<rbrakk> \<Longrightarrow> (u, v) \<in> set es0"
  using p2.pts_cover[of X v u]
  by (auto simp: mem_cand_list)

end

end
