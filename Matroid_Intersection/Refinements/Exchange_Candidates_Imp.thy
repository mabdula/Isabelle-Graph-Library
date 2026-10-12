theory Exchange_Candidates_Imp
  imports Exchange_Oracles_Imp "Graph_Algorithms_Dev.BFS_Instantiation"
begin

section \<open>The Candidate Graph from Exchange Partners\<close>

text \<open>The constant candidate graph of the exchange graph search, built once from the partner
  lists of the two oracles: the neighbours of an element are the union of its partners in both
  matroids, in ascending order. It contains every exchange edge of every solution. It is a CSR
  as used by the BFS (@{const bcsr_assn}): the array of the block ends and the array of the
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

definition cand_list :: "(nat \<Rightarrow> nat list) \<Rightarrow> (nat \<Rightarrow> nat list) \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "cand_list p1 p2 n = concat (map (\<lambda> u. map (Pair u) (merge_uniq (p1 u) (p2 u))) [0..<n])"

text \<open>The merge of the entries \<open>i..<a\<close> and \<open>j..<b\<close> of two partner lists, read through the
  queries \<open>q1\<close> and \<open>q2\<close>: counting the merged entries, starting from \<open>c\<close>, and writing them
  into an array from position \<open>p\<close> on, returning the position after them.\<close>

partial_function (heap) merge_cnt :: 
  "(nat \<Rightarrow> nat Heap) \<Rightarrow> (nat \<Rightarrow> nat Heap) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
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
  "(nat \<Rightarrow> nat Heap) \<Rightarrow> (nat \<Rightarrow> nat Heap) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
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

text \<open>The first pass writes the end position of the neighbours of every element \<open>u\<close> into
  entry \<open>u + 1\<close> of the block array, whose entry \<open>0\<close> is \<open>0\<close>, and returns their total number;
  the second pass writes the neighbours.\<close>

definition "cand_bounds_imp nq1 q1 nq2 q2 H1 H2 Ba n = foldl_range_imp (\<lambda> u c. do {
     a \<leftarrow> nq1 H1 u;
     b \<leftarrow> nq2 H2 u;
     c' \<leftarrow> merge_cnt (q1 H1 u) (q2 H2 u) a b 0 0 c;
     Array.upd (Suc u) c' Ba;
     return c' }) 0 n 0"

definition "cand_fill_imp nq1 q1 nq2 q2 H1 H2 Ga n = foldl_range_imp (\<lambda> u p. do {
     a \<leftarrow> nq1 H1 u;
     b \<leftarrow> nq2 H2 u;
     merge_wr (q1 H1 u) (q2 H2 u) a b Ga 0 0 p }) 0 n 0"

definition "cand_csr_imp nq1 q1 nq2 q2 H1 H2 n = do {
   Ba \<leftarrow> Array.new (Suc n) 0;
   m \<leftarrow> cand_bounds_imp nq1 q1 nq2 q2 H1 H2 Ba n;
   Ga \<leftarrow> Array.new m 0;
   cand_fill_imp nq1 q1 nq2 q2 H1 H2 Ga n;
   return (Ba, Ga) }"

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
    using 3(4,5) by simp_all
  then show ?case
    using 3 by (auto simp: set_merge_uniq)
qed simp_all

lemma nbrs_concat_Pair:
  "nbrs (concat (map (\<lambda> x. map (Pair x) (L x)) xs)) u = concat (map (\<lambda> x. if x = u then L x else []) xs)"
  by (induction xs) (simp_all add: nbrs_def filter_map comp_def)

lemma concat_if_dist:
  "distinct xs \<Longrightarrow> concat (map (\<lambda> x. if x = u then L x else []) xs) = (if u \<in> set xs then L u else [])"
  by (induction xs) auto

lemma nbrs_cand_list: "nbrs (cand_list p1 p2 n) u = (if u < n then merge_uniq (p1 u) (p2 u) else [])"
  unfolding cand_list_def nbrs_concat_Pair by (simp add: concat_if_dist)

lemma mem_cand_list: 
  "(u, v) \<in> set (cand_list p1 p2 n) \<longleftrightarrow> u < n \<and> (v \<in> set (p1 u) \<or> v \<in> set (p2 u))"
  unfolding cand_list_def by (auto simp: set_merge_uniq)

text \<open>The merging loops, for any two lists read through two queries.\<close>

lemma merge_cnt_rule:
  assumes q1: "\<And> k. k < length xs \<Longrightarrow> <F> q1 k <\<lambda> r. F * \<up>(r = xs ! k)>"
    and q2: "\<And> k. k < length ys \<Longrightarrow> <F> q2 k <\<lambda> r. F * \<up>(r = ys ! k)>"
  shows "\<lbrakk>i \<le> length xs; j \<le> length ys\<rbrakk> \<Longrightarrow> 
         <F> merge_cnt q1 q2 (length xs) (length ys) i j c 
         <\<lambda> r. F * \<up>(r = c + length (merge_uniq (drop i xs) (drop j ys)))>"
proof(induction "length xs - i + (length ys - j)" arbitrary: i j c rule: less_induct)
  case less
  show ?case
  proof(cases "i < length xs")
    case i: True
    have dx: "drop i xs = xs ! i # drop (Suc i) xs"
      using i by (rule Cons_nth_drop_Suc[symmetric])
    show ?thesis
    proof(cases "j < length ys")
      case j: True
      have dy: "drop j ys = ys ! j # drop (Suc j) ys"
        using j by (rule Cons_nth_drop_Suc[symmetric])
      have r1: "<F> merge_cnt q1 q2 (length xs) (length ys) (Suc i) j (Suc c) 
                <\<lambda> r. F * \<up>(r = Suc c + length (merge_uniq (drop (Suc i) xs) (drop j ys)))>"
        by (rule less) (use i j less.prems in simp_all)
      have r2: "<F> merge_cnt q1 q2 (length xs) (length ys) i (Suc j) (Suc c) 
                <\<lambda> r. F * \<up>(r = Suc c + length (merge_uniq (drop i xs) (drop (Suc j) ys)))>"
        by (rule less) (use i j less.prems in simp_all)
      have r3: "<F> merge_cnt q1 q2 (length xs) (length ys) (Suc i) (Suc j) (Suc c) 
                <\<lambda> r. F * \<up>(r = Suc c + length (merge_uniq (drop (Suc i) xs) (drop (Suc j) ys)))>"
        by (rule less) (use i j less.prems in simp_all)
      show ?thesis
        using i j
        by (subst merge_cnt.simps) 
           (sep_auto heap: q1[OF i] q2[OF j] r1[unfolded dy] r2[unfolded dx] r3 simp: dx dy)
    next
      case False
      then show ?thesis
        using i by (subst merge_cnt.simps) (sep_auto simp: merge_uniq_Nil2)
    qed
  next
    case False
    then show ?thesis
      using less.prems by (subst merge_cnt.simps) sep_auto
  qed
qed

lemma take_drop_upd:
  assumes "p < length g"
  shows "take (Suc p) (g[p := x]) @ M @ drop (Suc p + length M) (g[p := x]) = 
         take p g @ (x # M) @ drop (p + length (x # M)) g"
proof-
  have "take (Suc p) (g[p := x]) = take p g @ [x]"
    by (rule take_upd_Suc[OF assms])
  moreover have "drop (Suc p + length M) (g[p := x]) = drop (Suc p + length M) g"
    by simp
  ultimately show ?thesis
    by simp
qed

lemma merge_wr_rule:
  assumes q1: "\<And> k. k < length xs \<Longrightarrow> <F> q1 k <\<lambda> r. F * \<up>(r = xs ! k)>"
    and q2: "\<And> k. k < length ys \<Longrightarrow> <F> q2 k <\<lambda> r. F * \<up>(r = ys ! k)>"
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
    have dx: "drop i xs = xs ! i # drop (Suc i) xs"
      using i by (rule Cons_nth_drop_Suc[symmetric])
    show ?thesis
    proof(cases "j < length ys")
      case j: True
      have dy: "drop j ys = ys ! j # drop (Suc j) ys"
        using j by (rule Cons_nth_drop_Suc[symmetric])
      show ?thesis
      proof(cases "xs ! i < ys ! j")
        case lt: True
        let ?M = "merge_uniq (drop (Suc i) xs) (drop j ys)"
        have M: "merge_uniq (drop i xs) (drop j ys) = xs ! i # ?M"
          using lt by (simp add: dx dy)
        have p: "p < length g"
          using less.prems(3) unfolding M by simp
        have r: "<G \<mapsto>\<^sub>a g[p := xs ! i] * F> 
                   merge_wr q1 q2 (length xs) (length ys) G (Suc i) j (Suc p) 
                 <\<lambda> r. G \<mapsto>\<^sub>a (take (Suc p) (g[p := xs ! i]) @ ?M @ 
                              drop (Suc p + length ?M) (g[p := xs ! i])) * F * 
                       \<up>(r = Suc p + length ?M)>"
          by (rule less) (use i j less.prems(3) in \<open>simp_all add: M\<close>)
        show ?thesis
          unfolding M take_drop_upd[OF p, symmetric]
          using i j lt p by (subst merge_wr.simps) (sep_auto heap: q1[OF i] q2[OF j] r)
      next
        case nlt: False
        show ?thesis
        proof(cases "ys ! j < xs ! i")
          case gt: True
          let ?M = "merge_uniq (drop i xs) (drop (Suc j) ys)"
          have M: "merge_uniq (drop i xs) (drop j ys) = ys ! j # ?M"
            using nlt gt by (simp add: dx dy)
          have p: "p < length g"
            using less.prems(3) unfolding M by simp
          have r: "<G \<mapsto>\<^sub>a g[p := ys ! j] * F> 
                     merge_wr q1 q2 (length xs) (length ys) G i (Suc j) (Suc p) 
                   <\<lambda> r. G \<mapsto>\<^sub>a (take (Suc p) (g[p := ys ! j]) @ ?M @ 
                                drop (Suc p + length ?M) (g[p := ys ! j])) * F * 
                         \<up>(r = Suc p + length ?M)>"
            by (rule less) (use i j less.prems(3) in \<open>simp_all add: M\<close>)
          show ?thesis
            unfolding M take_drop_upd[OF p, symmetric]
            using i j nlt gt p by (subst merge_wr.simps) (sep_auto heap: q1[OF i] q2[OF j] r)
        next
          case ngt: False
          let ?M = "merge_uniq (drop (Suc i) xs) (drop (Suc j) ys)"
          have eq: "xs ! i = ys ! j"
            using nlt ngt by simp
          have M: "merge_uniq (drop i xs) (drop j ys) = xs ! i # ?M"
            by (simp add: dx dy eq)
          have p: "p < length g"
            using less.prems(3) unfolding M by simp
          have r: "<G \<mapsto>\<^sub>a g[p := xs ! i] * F> 
                     merge_wr q1 q2 (length xs) (length ys) G (Suc i) (Suc j) (Suc p) 
                   <\<lambda> r. G \<mapsto>\<^sub>a (take (Suc p) (g[p := xs ! i]) @ ?M @ 
                                drop (Suc p + length ?M) (g[p := xs ! i])) * F * 
                         \<up>(r = Suc p + length ?M)>"
            by (rule less) (use i j less.prems(3) in \<open>simp_all add: M\<close>)
          show ?thesis
            unfolding M take_drop_upd[OF p, symmetric]
            using i j nlt ngt p by (subst merge_wr.simps) (sep_auto heap: q1[OF i] q2[OF j] r)
        qed
      qed
    next
      case nj: False
      let ?M = "merge_uniq (drop (Suc i) xs) (drop j ys)"
      have dy: "drop j ys = []"
        using nj by simp
      have M: "merge_uniq (drop i xs) (drop j ys) = xs ! i # ?M"
        by (simp add: dx dy merge_uniq_Nil2)
      have p: "p < length g"
        using less.prems(3) unfolding M by simp
      have r: "<G \<mapsto>\<^sub>a g[p := xs ! i] * F> 
                 merge_wr q1 q2 (length xs) (length ys) G (Suc i) j (Suc p) 
               <\<lambda> r. G \<mapsto>\<^sub>a (take (Suc p) (g[p := xs ! i]) @ ?M @ 
                            drop (Suc p + length ?M) (g[p := xs ! i])) * F * 
                     \<up>(r = Suc p + length ?M)>"
        by (rule less) (use i less.prems in \<open>simp_all add: M\<close>)
      show ?thesis
        unfolding M take_drop_upd[OF p, symmetric]
        using i nj p by (subst merge_wr.simps) (sep_auto heap: q1[OF i] r)
    qed
  next
    case ni: False
    have dx: "drop i xs = []"
      using ni by simp
    show ?thesis
    proof(cases "j < length ys")
      case j: True
      let ?M = "merge_uniq (drop i xs) (drop (Suc j) ys)"
      have dy: "drop j ys = ys ! j # drop (Suc j) ys"
        using j by (rule Cons_nth_drop_Suc[symmetric])
      have M: "merge_uniq (drop i xs) (drop j ys) = ys ! j # ?M"
        by (simp add: dx dy)
      have p: "p < length g"
        using less.prems(3) unfolding M by simp
      have r: "<G \<mapsto>\<^sub>a g[p := ys ! j] * F> 
                 merge_wr q1 q2 (length xs) (length ys) G i (Suc j) (Suc p) 
               <\<lambda> r. G \<mapsto>\<^sub>a (take (Suc p) (g[p := ys ! j]) @ ?M @ 
                            drop (Suc p + length ?M) (g[p := ys ! j])) * F * 
                     \<up>(r = Suc p + length ?M)>"
        by (rule less) (use j less.prems in \<open>simp_all add: M\<close>)
      show ?thesis
        unfolding M take_drop_upd[OF p, symmetric]
        using ni j p by (subst merge_wr.simps) (sep_auto heap: q2[OF j] r)
    next
      case nj: False
      then show ?thesis
        using ni by (subst merge_wr.simps) sep_auto
    qed
  qed
qed

text \<open>The CSR of the flat neighbour array of an edge list whose sources are below \<open>n\<close>: the
  block array holds the start offsets of the vertices up to \<open>n\<close>.\<close>

lemma bcsr_rel_build_nha:
  assumes out: "\<And> v. n \<le> v \<Longrightarrow> nbrs es v = []"
  shows "bcsr_rel (build_nhlists es) (map (start_off es) [0..<Suc n]) (build_nha es n)"
proof-
  let ?B = "map (start_off es) [0..<Suc n]"
  have mono: "?B ! v \<le> ?B ! Suc v \<and> ?B ! Suc v \<le> length (build_nha es n)"
    if "Suc v < length ?B" for v
  proof-
    have v: "v < n"
      using that by simp
    have "start_off es (Suc v) \<le> start_off es n"
      using v by (intro start_off_mono) simp
    then show ?thesis
      using v by (simp add: start_off_Suc length_build_nha del: upt_Suc)
  qed
  have blk: "(case build_nhlists es v of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) =
             (if Suc v < length ?B then nths (build_nha es n) {?B ! v..<?B ! Suc v} else [])" for v
  proof (cases "v < n")
    case True
    then show ?thesis
      using build_nha_nths_vertex[OF True, of es]
      by (simp add: build_nhlists_def start_off_Suc del: upt_Suc)
  next
    case False
    then show ?thesis
      using out[of v] by (simp add: build_nhlists_def del: upt_Suc)
  qed
  show ?thesis
    unfolding bcsr_rel_def using mono blk by blast
qed

text \<open>Arrays whose entries below \<open>u\<close> are written.\<close>

definition "prefix_map f u n = map (\<lambda> v. if v < u then f v else (0 :: nat)) [0..<n]"

lemma length_prefix_map [simp]: "length (prefix_map f u n) = n"
  unfolding prefix_map_def by simp

lemma prefix_map_upd: 
  "\<lbrakk>u < n; x = f u\<rbrakk> \<Longrightarrow> (prefix_map f u n)[u := x] = prefix_map f (Suc u) n"
  unfolding prefix_map_def by (rule nth_equalityI) (auto simp: nth_list_update)

lemma prefix_map_n: "prefix_map f n n = map f [0..<n]"
  unfolding prefix_map_def by simp

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
  "k < length (pts1 u) \<Longrightarrow> u < n \<Longrightarrow> 
   <pst1 H1 * pst2 H2> pt1_imp H1 u k <\<lambda> r. pst1 H1 * pst2 H2 * \<up>(r = pts1 u ! k)>"
  by (sep_auto heap: p1.pt_imp)

lemma pt2_rule: 
  "k < length (pts2 u) \<Longrightarrow> u < n \<Longrightarrow> 
   <pst1 H1 * pst2 H2> pt2_imp H2 u k <\<lambda> r. pst1 H1 * pst2 H2 * \<up>(r = pts2 u ! k)>"
  by (sep_auto heap: p2.pt_imp)

lemma cnt_rule:
  assumes u: "u < n"
  shows "<pst1 H1 * pst2 H2> 
           merge_cnt (pt1_imp H1 u) (pt2_imp H2 u) (length (pts1 u)) (length (pts2 u)) 0 0 c
         <\<lambda> r. pst1 H1 * pst2 H2 * \<up>(r = c + length (nbrs es0 u))>"
  using merge_cnt_rule[where F = "pst1 H1 * pst2 H2" and xs = "pts1 u" and ys = "pts2 u" 
      and ?q1.0 = "pt1_imp H1 u" and ?q2.0 = "pt2_imp H2 u" and i = 0 and j = 0 and c = c, 
      OF pt1_rule[OF _ u] pt2_rule[OF _ u]] 
  by (simp add: nbrs_es0 u)

lemma wr_rule:
  assumes u: "u < n" and le: "p + length (nbrs es0 u) \<le> length g"
  shows "<G \<mapsto>\<^sub>a g * (pst1 H1 * pst2 H2)> 
           merge_wr (pt1_imp H1 u) (pt2_imp H2 u) (length (pts1 u)) (length (pts2 u)) G 0 0 p
         <\<lambda> r. G \<mapsto>\<^sub>a (take p g @ nbrs es0 u @ drop (p + length (nbrs es0 u)) g) * 
               (pst1 H1 * pst2 H2) * \<up>(r = p + length (nbrs es0 u))>"
  using merge_wr_rule[where F = "pst1 H1 * pst2 H2" and xs = "pts1 u" and ys = "pts2 u" 
      and ?q1.0 = "pt1_imp H1 u" and ?q2.0 = "pt2_imp H2 u" and i = 0 and j = 0 and p = p and g = g 
      and G = G, OF pt1_rule[OF _ u] pt2_rule[OF _ u]] le
  by (simp add: nbrs_es0 u)

lemma bounds_rule:
  "<pst1 H1 * pst2 H2 * Ba \<mapsto>\<^sub>a replicate (Suc n) 0> 
     cand_bounds_imp npts1_imp pt1_imp npts2_imp pt2_imp H1 H2 Ba n
   <\<lambda> m. pst1 H1 * pst2 H2 * Ba \<mapsto>\<^sub>a map (start_off es0) [0..<Suc n] * \<up>(m = start_off es0 n)>"
proof-
  define A where "A = (\<lambda> u (_ :: unit) c. 
     Ba \<mapsto>\<^sub>a prefix_map (start_off es0) (Suc u) (Suc n) * \<up>(c = start_off es0 u))"
  have step: "<A u st c * (pst1 H1 * pst2 H2)> 
     do { a \<leftarrow> npts1_imp H1 u; b \<leftarrow> npts2_imp H2 u;
          c' \<leftarrow> merge_cnt (pt1_imp H1 u) (pt2_imp H2 u) a b 0 0 c;
          Array.upd (Suc u) c' Ba;
          return c' }
     <\<lambda> r. A (Suc u) () r * (pst1 H1 * pst2 H2)>" if u: "u < n" for u st c
    unfolding A_def
    using u by (sep_auto heap: p1.npts_imp p2.npts_imp cnt_rule simp: prefix_map_upd start_off_Suc)
  have run: "<A 0 () 0 * (pst1 H1 * pst2 H2)> 
               cand_bounds_imp npts1_imp pt1_imp npts2_imp pt2_imp H1 H2 Ba n
             <\<lambda> r. A n (foldl (\<lambda> a j. ()) () [0..<n]) r * (pst1 H1 * pst2 H2)>"
    unfolding cand_bounds_imp_def
    by (rule foldl_range_imp_idx_rule[where A = A and F = "pst1 H1 * pst2 H2" and g = "\<lambda> _ _. ()"]) 
       (rule step, simp_all)
  have init: "prefix_map (start_off es0) (Suc 0) (Suc n) = replicate (Suc n) 0"
    unfolding prefix_map_def by (rule nth_equalityI) (simp_all del: upt_Suc)
  show ?thesis
    by (rule ht_cons_post[OF ht_cons_pre[OF _ run]]) (sep_auto simp: A_def init prefix_map_n)+
qed

lemma fill_rule:
  "<pst1 H1 * pst2 H2 * Ga \<mapsto>\<^sub>a replicate (start_off es0 n) 0> 
     cand_fill_imp npts1_imp pt1_imp npts2_imp pt2_imp H1 H2 Ga n
   <\<lambda> _. pst1 H1 * pst2 H2 * Ga \<mapsto>\<^sub>a build_nha es0 n>"
proof-
  define A where "A = (\<lambda> u (gl :: nat list) p. 
     Ga \<mapsto>\<^sub>a gl * \<up>(p = start_off es0 u \<and> length gl = start_off es0 n \<and> 
                     take p gl = build_nha es0 u))"
  define g where "g = (\<lambda> u (gl :: nat list). 
     take (start_off es0 u) gl @ nbrs es0 u @ drop (start_off es0 (Suc u)) gl)"
  have step: "<A u gl p * (pst1 H1 * pst2 H2)> 
     do { a \<leftarrow> npts1_imp H1 u; b \<leftarrow> npts2_imp H2 u; 
          merge_wr (pt1_imp H1 u) (pt2_imp H2 u) a b Ga 0 0 p }
     <\<lambda> r. A (Suc u) (g u gl) r * (pst1 H1 * pst2 H2)>" if u: "u < n" for u gl p
  proof(cases "p = start_off es0 u \<and> length gl = start_off es0 n")
    case True
    have le: "p + length (nbrs es0 u) \<le> length gl"
      using True start_off_mono[of "Suc u" n es0] u by (simp add: start_off_Suc)
    have g: "g u gl = take p gl @ nbrs es0 u @ drop (p + length (nbrs es0 u)) gl"
      using True by (simp add: g_def start_off_Suc)
    have nha: "build_nha es0 (Suc u) = build_nha es0 u @ nbrs es0 u"
      by (simp add: build_nha_def)
    show ?thesis
      unfolding A_def g
      using u le True 
      by (sep_auto heap: p1.npts_imp p2.npts_imp wr_rule simp: start_off_Suc nha length_build_nha)
  next
    case False
    then show ?thesis
      unfolding A_def by sep_auto
  qed
  have run: "<A 0 (replicate (start_off es0 n) 0) 0 * (pst1 H1 * pst2 H2)> 
               cand_fill_imp npts1_imp pt1_imp npts2_imp pt2_imp H1 H2 Ga n
             <\<lambda> r. A n (foldl (\<lambda> a j. g j a) (replicate (start_off es0 n) 0) [0..<n]) r * 
                   (pst1 H1 * pst2 H2)>"
    unfolding cand_fill_imp_def
    by (rule foldl_range_imp_idx_rule[where A = A and F = "pst1 H1 * pst2 H2" and g = g]) 
       (rule step, simp_all)
  have fin: "\<lbrakk>length gl = start_off es0 n; take (start_off es0 n) gl = build_nha es0 n\<rbrakk> \<Longrightarrow> 
             gl = build_nha es0 n" for gl
    by simp
  show ?thesis
    by (rule ht_cons_post[OF ht_cons_pre[OF _ run]]) 
       (sep_auto simp: A_def build_nha_def dest: fin)+
qed

lemma cand_csr_rule:
  "<pst1 H1 * pst2 H2> cand_csr_imp npts1_imp pt1_imp npts2_imp pt2_imp H1 H2 n 
   <\<lambda> G. pst1 H1 * pst2 H2 * bcsr_assn (build_nhlists es0) G>"
proof-
  let ?B = "map (start_off es0) [0..<n] @ [start_off es0 n]"
  have rel: "bcsr_rel (build_nhlists es0) ?B (build_nha es0 n)"
    using bcsr_rel_build_nha[of n es0] by (simp add: nbrs_cand_list)
  have fin: "Ga \<mapsto>\<^sub>a build_nha es0 n * Ba \<mapsto>\<^sub>a ?B
             \<Longrightarrow>\<^sub>A bcsr_assn (build_nhlists es0) (Ba, Ga)" for Ba Ga
    unfolding bcsr_assn_def using rel by sep_auto
  have fin': "pst1 H1 * pst2 H2 * Ga \<mapsto>\<^sub>a build_nha es0 n * Ba \<mapsto>\<^sub>a ?B * true
              \<Longrightarrow>\<^sub>A pst1 H1 * pst2 H2 * bcsr_assn (build_nhlists es0) (Ba, Ga) * true" for Ba Ga
  proof-
    have "pst1 H1 * pst2 H2 * Ga \<mapsto>\<^sub>a build_nha es0 n * Ba \<mapsto>\<^sub>a ?B * true = 
          pst1 H1 * pst2 H2 * (Ga \<mapsto>\<^sub>a build_nha es0 n * Ba \<mapsto>\<^sub>a ?B) * true"
      by (simp only: mult.assoc)
    then show ?thesis
      by (simp only:) (intro ent_star_mono ent_refl fin)
  qed
  show ?thesis
    unfolding cand_csr_imp_def
    apply (sep_auto heap: bounds_rule fill_rule)
    apply (erule entailsD[OF fin'])
    done
qed

text \<open>The properties the exchange graph search requires of its candidate graph.\<close>

lemma cand_bound: "(u, v) \<in> set es0 \<Longrightarrow> u < n \<and> v < n"
  unfolding mem_cand_list using p1.pts_bound p2.pts_bound by blast

lemma cand_sorted: "sorted_wrt (<) (nbrs es0 u)"
  unfolding nbrs_cand_list by (simp add: sorted_merge_uniq p1.pts_sorted p2.pts_sorted)

lemma cand_cover1:
  "\<lbrakk>finite X; X \<subseteq> {0..<n}; indep1 X; indep2 X; u < n; v < n; u \<in> X; v \<notin> X;
    \<not> ins_orcl1 (orcl_prep1 X) v; exch_orcl1 (orcl_prep1 X) u v\<rbrakk> \<Longrightarrow> (u, v) \<in> set es0"
  unfolding mem_cand_list using p1.pts_cover[of X u v] by blast

lemma cand_cover2:
  "\<lbrakk>finite X; X \<subseteq> {0..<n}; indep1 X; indep2 X; u < n; v < n; u \<notin> X; v \<in> X;
    \<not> ins_orcl2 (orcl_prep2 X) u; exch_orcl2 (orcl_prep2 X) v u\<rbrakk> \<Longrightarrow> (u, v) \<in> set es0"
  unfolding mem_cand_list using p2.pts_cover[of X v u] by blast

end

end
