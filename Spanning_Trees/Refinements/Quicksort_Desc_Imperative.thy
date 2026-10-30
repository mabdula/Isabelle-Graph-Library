theory Quicksort_Desc_Imperative
  imports Separation_Logic_Imperative_HOL_Partial.Sep_Main
          "HOL-Library.Multiset" "HOL-Library.Product_Lexorder"
begin

provenance ai_human

no_notation Ref.update (\<open>_ := _\<close> 62)

section \<open>Imperative In-Place Quicksort by Keys (Descending)\<close>

text \<open>We adapt the imperative quicksort from \<open>HOL-Imperative_HOL.Imperative_Quicksort\<close> to sort
  an array of natural numbers (e.g. edges) in descending order of their keys, where the keys
  are stored in a second array on the heap (e.g. the costs of the edges). Ties are broken by the
  elements themselves, i.e. element \<open>x\<close> is compared via \<open>(ks ! x, x)\<close>, where \<open>ks\<close> is the content
  of the key array. Since this order is strict on different elements, the sorted result is
  unique.

  The algorithm is the same as the one in \<open>Imperative_Quicksort\<close> (with the last element of a
  range as pivot), except for the comparisons. The proofs are done in two steps: we first define
  a functional model of the algorithm on lists and prove it correct (following the proofs in
  \<open>Imperative_Quicksort\<close>), and then show that the imperative algorithm refines it.\<close>

subsection \<open>Functional Model\<close>

text \<open>The key function \<open>f\<close> is arbitrary in the functional model. Elements with a larger key are
  put first.\<close>

definition swap_l :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "swap_l xs i j = xs[i := xs ! j, j := xs ! i]"

function part1_f :: "('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> 'a list \<times> nat" where
  "part1_f f xs l r p =
    (if r \<le> l then (xs, r)
     else if p \<le> f (xs ! l) then part1_f f xs (l + 1) r p
     else part1_f f (swap_l xs l r) l (r - 1) p)"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(_, _, l, r, _). r - l)") auto

declare part1_f.simps[simp del]

definition partition_f :: "('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<times> nat" where
  "partition_f f xs l r = (
    let p = f (xs ! r);
        (ys, m) = part1_f f xs l (r - 1) p;
        m' = (if p \<le> f (ys ! m) then m + 1 else m)
    in (swap_l ys m' r, m'))"

text \<open>The test \<open>l \<le> m \<and> m \<le> r\<close> is always true (see below); it is only needed for termination.\<close>

function quicksort_f :: "('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "quicksort_f f xs l r =
    (if l < r then
      (let (ys, m) = partition_f f xs l r in
        if l \<le> m \<and> m \<le> r then quicksort_f f (quicksort_f f ys l (m - 1)) (m + 1) r else ys)
     else xs)"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>(_, _, l, r). r - l)") auto

declare quicksort_f.simps[simp del]

subsubsection \<open>Swapping\<close>

lemma swap_l_length[simp]: "length (swap_l xs i j) = length xs"
  by (simp add: swap_l_def)

lemma swap_l_mset[simp]: "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> mset (swap_l xs i j) = mset xs"
  by (simp add: swap_l_def mset_swap)

lemma swap_l_nth:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> k < length xs \<Longrightarrow>
    swap_l xs i j ! k = (if k = j then xs ! i else if k = i then xs ! j else xs ! k)"
  by (simp add: swap_l_def nth_list_update)

subsubsection \<open>Partitioning\<close>

lemma part1_f_props_conj:
  "r < length xs \<Longrightarrow> part1_f f xs l r p = (ys, m) \<Longrightarrow>
    length ys = length xs \<and> mset ys = mset xs \<and>
    (\<forall>i < length xs. i < l \<or> r < i \<longrightarrow> ys ! i = xs ! i) \<and>
    (l \<le> r \<longrightarrow> l \<le> m \<and> m \<le> r) \<and>
    (\<forall>i. l \<le> i \<and> i < m \<longrightarrow> p \<le> f (ys ! i)) \<and>
    (\<forall>i. m < i \<and> i \<le> r \<longrightarrow> f (ys ! i) < p)"
proof (induction f xs l r p arbitrary: ys m rule: part1_f.induct)
  case (1 f xs l r p)
  show ?case
  proof (cases "r \<le> l")
    case True
    hence "ys = xs" "m = r"
      using "1.prems"(2) by (simp_all add: part1_f.simps[of f xs l r p])
    thus ?thesis
      using True by auto
  next
    case lr: False
    show ?thesis
    proof (cases "p \<le> f (xs ! l)")
      case le: True
      have rec: "part1_f f xs (l + 1) r p = (ys, m)"
        using "1.prems"(2) lr le by (simp add: part1_f.simps[of f xs l r p])
      note IH = "1.IH"(1)[OF lr le "1.prems"(1) rec]
      have ys_l: "ys ! l = xs ! l"
        using IH "1.prems"(1) lr by auto
      show ?thesis
      proof (intro conjI allI impI)
        show "length ys = length xs" "mset ys = mset xs"
          using IH by auto
      next
        fix i
        assume "i < length xs" "i < l \<or> r < i"
        thus "ys ! i = xs ! i"
          using IH by auto
      next
        show "l \<le> m" "m \<le> r"
          using IH lr by auto
      next
        fix i
        assume i: "l \<le> i \<and> i < m"
        show "p \<le> f (ys ! i)"
        proof (cases "i = l")
          case True
          thus ?thesis using ys_l le by simp
        next
          case False
          thus ?thesis using IH i by auto
        qed
      next
        fix i
        assume "m < i \<and> i \<le> r"
        thus "f (ys ! i) < p"
          using IH by auto
      qed
    next
      case le: False
      let ?zs = "swap_l xs l r"
      have rec: "part1_f f ?zs l (r - 1) p = (ys, m)"
        using "1.prems"(2) lr le by (simp add: part1_f.simps[of f xs l r p])
      have len: "r - 1 < length ?zs"
        using "1.prems"(1) by simp
      note IH = "1.IH"(2)[OF lr le len rec]
      have zs: "\<And>i. i < length xs \<Longrightarrow> i \<noteq> l \<Longrightarrow> i \<noteq> r \<Longrightarrow> ?zs ! i = xs ! i"
        "?zs ! r = xs ! l"
        using "1.prems"(1) lr by (auto simp: swap_l_nth)
      have ys_r: "ys ! r = xs ! l"
        using IH zs(2) "1.prems"(1) lr by auto
      show ?thesis
      proof (intro conjI allI impI)
        show "length ys = length xs" "mset ys = mset xs"
          using IH "1.prems"(1) lr by auto
      next
        fix i
        assume "i < length xs" "i < l \<or> r < i"
        thus "ys ! i = xs ! i"
          using IH zs(1) lr by auto
      next
        show "l \<le> m" "m \<le> r"
          using IH lr by auto
      next
        fix i
        assume "l \<le> i \<and> i < m"
        thus "p \<le> f (ys ! i)"
          using IH by auto
      next
        fix i
        assume i: "m < i \<and> i \<le> r"
        show "f (ys ! i) < p"
        proof (cases "i = r")
          case True
          thus ?thesis using ys_r le by simp
        next
          case False
          thus ?thesis using IH i by auto
        qed
      qed
    qed
  qed
qed

lemma part1_f_props:
  assumes "part1_f f xs l r p = (ys, m)" "r < length xs"
  shows "length ys = length xs" "mset ys = mset xs"
    "\<And>i. i < length xs \<Longrightarrow> i < l \<or> r < i \<Longrightarrow> ys ! i = xs ! i"
    "l \<le> r \<Longrightarrow> l \<le> m \<and> m \<le> r"
    "\<And>i. l \<le> i \<Longrightarrow> i < m \<Longrightarrow> p \<le> f (ys ! i)"
    "\<And>i. m < i \<Longrightarrow> i \<le> r \<Longrightarrow> f (ys ! i) < p"
  using part1_f_props_conj[OF assms(2,1)] by auto

lemma partition_f_props:
  assumes "partition_f f xs l r = (zs, m')" "l < r" "r < length xs"
  shows "length zs = length xs" "mset zs = mset xs"
    "\<And>i. i < length xs \<Longrightarrow> i < l \<or> r < i \<Longrightarrow> zs ! i = xs ! i"
    "l \<le> m'" "m' \<le> r"
    "\<And>i. l \<le> i \<Longrightarrow> i < m' \<Longrightarrow> f (zs ! m') \<le> f (zs ! i)"
    "\<And>i. m' < i \<Longrightarrow> i \<le> r \<Longrightarrow> f (zs ! i) < f (zs ! m')"
proof -
  let ?p = "f (xs ! r)"
  obtain ys m where pf: "part1_f f xs l (r - 1) ?p = (ys, m)"
    by (cases "part1_f f xs l (r - 1) ?p") auto
  define m'' where "m'' = (if ?p \<le> f (ys ! m) then m + 1 else m)"
  have zs: "zs = swap_l ys m'' r" "m' = m''"
    using assms(1) pf by (auto simp: partition_f_def m''_def Let_def)
  have r1: "r - 1 < length xs"
    using assms by simp
  note P = part1_f_props[OF pf r1]
  have lm: "l \<le> m" "m \<le> r - 1"
    using P(4) assms(2) by auto
  have ysr: "ys ! r = xs ! r"
    using P(3)[of r] assms(2,3) by auto
  have lenys: "length ys = length xs"
    by (rule P(1))
  have m''r: "l \<le> m''" "m'' \<le> r"
    using lm assms(2) by (auto simp: m''_def)
  have zsn: "\<And>i. i < length xs \<Longrightarrow>
      zs ! i = (if i = r then ys ! m'' else if i = m'' then ys ! r else ys ! i)"
    using zs m''r assms(3) lenys by (auto simp: swap_l_nth)
  have piv: "f (zs ! m') = ?p"
    using zsn[of m''] zs(2) m''r assms(3) ysr by auto
  show "length zs = length xs"
    using zs lenys by simp
  show "mset zs = mset xs"
    using zs m''r assms(3) lenys P(2) by simp
  show "\<And>i. i < length xs \<Longrightarrow> i < l \<or> r < i \<Longrightarrow> zs ! i = xs ! i"
    using zsn m''r P(3) by auto
  show "l \<le> m'" "m' \<le> r"
    using zs(2) m''r by auto
  show "f (zs ! m') \<le> f (zs ! i)" if i: "l \<le> i" "i < m'" for i
  proof -
    have "zs ! i = ys ! i"
      using zsn[of i] i zs(2) m''r assms(3) by auto
    moreover have "?p \<le> f (ys ! i)"
    proof (cases "i < m")
      case True
      thus ?thesis using P(5) i by auto
    next
      case False
      hence "i = m" "m'' = m + 1"
        using i zs(2) by (auto simp: m''_def split: if_splits)
      thus ?thesis
        by (auto simp: m''_def split: if_splits)
    qed
    ultimately show ?thesis
      using piv by simp
  qed
  show "f (zs ! i) < f (zs ! m')" if i: "m' < i" "i \<le> r" for i
  proof (cases "i = r")
    case True
    hence zsr: "zs ! i = ys ! m''"
      using zsn[of r] assms(3) by simp
    show ?thesis
    proof (cases "?p \<le> f (ys ! m)")
      case True
      hence "m'' = m + 1"
        by (simp add: m''_def)
      moreover have "m + 1 \<le> r - 1"
        using i \<open>i = r\<close> zs(2) \<open>m'' = m + 1\<close> by simp
      ultimately show ?thesis
        using P(6)[of "m + 1"] zsr piv by simp
    next
      case False
      thus ?thesis
        using zsr piv by (simp add: m''_def)
    qed
  next
    case False
    hence "zs ! i = ys ! i"
      using zsn[of i] i zs(2) assms(3) by auto
    moreover have "m < i" "i \<le> r - 1"
      using i False zs(2) by (auto simp: m''_def split: if_splits)
    ultimately show ?thesis
      using P(6) piv by simp
  qed
qed

subsubsection \<open>Permutations of Segments\<close>

text \<open>If a list is a permutation of another one and both agree outside a segment, then every
  element in the segment of the first list comes from the segment of the second list.\<close>

lemma segment_perm:
  assumes "length ys = length xs" "mset ys = mset xs"
    "\<And>i. i < length xs \<Longrightarrow> i < l \<or> r < i \<Longrightarrow> ys ! i = xs ! i"
    "r < length xs" "l \<le> i" "i \<le> r"
  shows "\<exists>j. l \<le> j \<and> j \<le> r \<and> ys ! i = xs ! j"
proof -
  have drop_eq: "drop (Suc r) ys = drop (Suc r) xs"
    using assms(1,3) by (intro nth_equalityI) auto
  have take_eq: "take l ys = take l xs"
    using assms(1,3,4,5,6) by (intro nth_equalityI) auto
  have "mset (take (Suc r) ys) = mset (take (Suc r) xs)"
  proof -
    have "mset (take (Suc r) ys) + mset (drop (Suc r) ys) =
          mset (take (Suc r) xs) + mset (drop (Suc r) xs)"
      using assms(2) by (simp flip: mset_append)
    thus ?thesis
      using drop_eq by simp
  qed
  moreover have "\<And>zs. take (Suc r) zs = take l zs @ drop l (take (Suc r) zs)"
    using assms(5,6) by (metis append_take_drop_id min.absorb1 le_SucI order.trans take_take)
  ultimately have "mset (drop l (take (Suc r) ys)) = mset (drop l (take (Suc r) xs))"
    using take_eq by (metis add_left_cancel mset_append)
  hence set_eq: "set (drop l (take (Suc r) ys)) = set (drop l (take (Suc r) xs))"
    by (metis set_mset_mset)
  have "ys ! i \<in> set (drop l (take (Suc r) ys))"
    using assms by (auto simp: in_set_conv_nth intro!: exI[of _ "i - l"])
  then obtain k where k: "k < length (drop l (take (Suc r) xs))"
    "drop l (take (Suc r) xs) ! k = ys ! i"
    using set_eq by (auto simp: in_set_conv_nth)
  thus ?thesis
    using assms(4) by (intro exI[of _ "l + k"]) auto
qed

subsubsection \<open>Sorting\<close>

lemma quicksort_f_props_conj:
  "r < length xs \<Longrightarrow>
    length (quicksort_f f xs l r) = length xs \<and>
    mset (quicksort_f f xs l r) = mset xs \<and>
    (\<forall>i < length xs. i < l \<or> r < i \<longrightarrow> quicksort_f f xs l r ! i = xs ! i) \<and>
    (\<forall>i j. l \<le> i \<and> i < j \<and> j \<le> r \<longrightarrow>
      f (quicksort_f f xs l r ! j) \<le> f (quicksort_f f xs l r ! i))"
proof (induction f xs l r rule: quicksort_f.induct)
  case (1 f xs l r)
  show ?case
  proof (cases "l < r")
    case False
    hence "quicksort_f f xs l r = xs"
      by (simp add: quicksort_f.simps[of f xs l r])
    thus ?thesis
      using False by auto
  next
    case lr: True
    obtain ys m where pf: "partition_f f xs l r = (ys, m)"
      by fastforce
    note P = partition_f_props[OF pf lr "1.prems"]
    have bnd: "l \<le> m \<and> m \<le> r"
      using P(4,5) by simp
    define qs1 where "qs1 = quicksort_f f ys l (m - 1)"
    define zs where "zs = quicksort_f f qs1 (m + 1) r"
    have qs: "quicksort_f f xs l r = zs"
      using pf lr bnd by (simp add: quicksort_f.simps[of f xs l r] qs1_def zs_def)
    have m1: "m - 1 < length ys"
      using P(1) bnd "1.prems" by arith
    have IH1: "length qs1 = length ys" "mset qs1 = mset ys"
      "\<And>i. i < length ys \<Longrightarrow> i < l \<or> m - 1 < i \<Longrightarrow> qs1 ! i = ys ! i"
      "\<And>i j. l \<le> i \<Longrightarrow> i < j \<Longrightarrow> j \<le> m - 1 \<Longrightarrow> f (qs1 ! j) \<le> f (qs1 ! i)"
      using "1.IH"(1)[OF lr pf[symmetric] refl bnd m1] unfolding qs1_def by auto
    have r2: "r < length qs1"
      using IH1(1) P(1) "1.prems" by simp
    have IH2: "length zs = length qs1" "mset zs = mset qs1"
      "\<And>i. i < length qs1 \<Longrightarrow> i < m + 1 \<or> r < i \<Longrightarrow> zs ! i = qs1 ! i"
      "\<And>i j. m + 1 \<le> i \<Longrightarrow> i < j \<Longrightarrow> j \<le> r \<Longrightarrow> f (zs ! j) \<le> f (zs ! i)"
      using "1.IH"(2)[OF lr pf[symmetric] refl bnd] r2 unfolding qs1_def zs_def by auto
    have len: "length zs = length xs" "length qs1 = length xs"
      using IH1(1) IH2(1) P(1) by auto
    have qs1_m: "qs1 ! m = ys ! m"
    proof (cases "m = 0")
      case True
      thus ?thesis
        by (simp add: qs1_def quicksort_f.simps[of f ys l 0])
    next
      case False
      thus ?thesis
        using IH1(3)[of m] bnd "1.prems" P(1) by simp
    qed
    have zs_m: "zs ! m = ys ! m"
      using IH2(3)[of m] qs1_m bnd "1.prems" len by simp
    have left: "f (ys ! m) \<le> f (zs ! i)" if i: "l \<le> i" "i < m" for i
    proof -
      have "zs ! i = qs1 ! i"
        using IH2(3)[of i] i bnd "1.prems" len by simp
      moreover obtain j where j: "l \<le> j" "j \<le> m - 1" "qs1 ! i = ys ! j"
        using segment_perm[of qs1 ys l "m - 1" i, OF IH1(1,2) IH1(3) m1] i by fastforce
      moreover have "j < m"
        using j(2) i by arith
      ultimately show ?thesis
        using P(6)[of j] by simp
    qed
    have right: "f (zs ! i) < f (ys ! m)" if i: "m + 1 \<le> i" "i \<le> r" for i
    proof -
      obtain j where j: "m + 1 \<le> j" "j \<le> r" "zs ! i = qs1 ! j"
        using segment_perm[of zs qs1 "m + 1" r i, OF IH2(1,2) IH2(3) r2] i by auto
      hence "qs1 ! j = ys ! j"
        using IH1(3)[of j] bnd "1.prems" P(1) by simp
      thus ?thesis
        using P(7)[of j] j by simp
    qed
    have sorted: "f (zs ! j) \<le> f (zs ! i)" if ij: "l \<le> i" "i < j" "j \<le> r" for i j
    proof -
      consider "j < m" | "j = m" | "i < m" "m < j" | "m \<le> i"
        using ij by linarith
      thus ?thesis
      proof cases
        case 1
        thus ?thesis
          using IH1(4)[of i j] IH2(3)[of i] IH2(3)[of j] ij "1.prems" len by simp
      next
        case 2
        thus ?thesis
          using left[of i] zs_m ij by simp
      next
        case 3
        thus ?thesis
          using left[of i] right[of j] ij by fastforce
      next
        case 4
        show ?thesis
        proof (cases "i = m")
          case True
          thus ?thesis
            using right[of j] zs_m ij by fastforce
        next
          case False
          thus ?thesis
            using IH2(4)[of i j] 4 ij by simp
        qed
      qed
    qed
    have outer: "zs ! i = xs ! i" if "i < length xs" "i < l \<or> r < i" for i
      using IH2(3)[of i] IH1(3)[of i] P(3)[of i] that bnd len P(1) by auto
    show ?thesis
      unfolding qs using len IH2(2) IH1(2) P(2) outer sorted by auto
  qed
qed

lemma quicksort_f_props:
  assumes "r < length xs"
  shows "length (quicksort_f f xs l r) = length xs"
    "mset (quicksort_f f xs l r) = mset xs"
    "\<And>i. i < length xs \<Longrightarrow> i < l \<or> r < i \<Longrightarrow> quicksort_f f xs l r ! i = xs ! i"
    "\<And>i j. l \<le> i \<Longrightarrow> i < j \<Longrightarrow> j \<le> r \<Longrightarrow>
      f (quicksort_f f xs l r ! j) \<le> f (quicksort_f f xs l r ! i)"
  using quicksort_f_props_conj[OF assms] by blast+

subsubsection \<open>Sorting Whole Lists\<close>

definition qsort_f :: "('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "qsort_f f xs = quicksort_f f xs 0 (length xs - 1)"

lemma qsort_f_mset: "mset (qsort_f f xs) = mset xs"
proof (cases "xs = []")
  case True
  thus ?thesis
    by (simp add: qsort_f_def quicksort_f.simps)
next
  case False
  thus ?thesis
    by (simp add: qsort_f_def quicksort_f_props)
qed

lemma qsort_f_sorted: "sorted_wrt (\<lambda>x y. f y \<le> f x) (qsort_f f xs)"
proof (cases "xs = []")
  case True
  thus ?thesis
    by (simp add: qsort_f_def quicksort_f.simps)
next
  case False
  hence "length xs - 1 < length xs"
    by simp
  note Q = quicksort_f_props[OF this, where f = f and l = 0]
  show ?thesis
    unfolding sorted_wrt_iff_nth_less qsort_f_def
    using Q(1) Q(4) by auto
qed

text \<open>For an injective key function, the descending sorted permutation of a list is unique.\<close>

lemma sorted_desc_unique:
  assumes "inj f" "mset ys = mset xs" "sorted_wrt (\<lambda>x y. f y \<le> f x) ys"
  shows "ys = rev (sort_key f xs)"
proof -
  have "sort_key f xs = rev ys"
  proof (rule properties_for_sort_key)
    show "mset (rev ys) = mset xs"
      using assms(2) by simp
  next
    fix k
    have "\<And>zs. filter (\<lambda>x. f k = f x) zs = filter ((=) k) zs"
      using assms(1) by (metis (mono_tags, lifting) injD)
    thus "filter (\<lambda>x. f k = f x) (rev ys) = filter (\<lambda>x. f k = f x) xs"
      using assms(2)
      by (metis mset_rev replicate_count_mset_eq_filter_eq)
  next
    show "sorted (map f (rev ys))"
      using assms(3) by (simp add: sorted_map sorted_wrt_rev)
  qed
  thus ?thesis
    by simp
qed

text \<open>The key function used for sorting elements by keys from a list \<open>ks\<close>, with ties broken by
  the elements themselves.\<close>

definition qs_key :: "'k list \<Rightarrow> nat \<Rightarrow> 'k \<times> nat" where
  "qs_key ks x = (ks ! x, x)"

lemma qs_key_inj: "inj (qs_key ks)"
  by (auto simp: inj_def qs_key_def)

definition sort_desc_qs :: "(nat \<Rightarrow> 'k::linorder) \<Rightarrow> nat list \<Rightarrow> nat list" where
  "sort_desc_qs c xs = rev (sort_key (\<lambda>e. (c e, e)) xs)"

lemma sort_desc_qs_props:
  "sorted_wrt (\<lambda>x y. c x \<ge> c y) (sort_desc_qs c xs)"
  "set (sort_desc_qs c xs) = set xs"
  "length (sort_desc_qs c xs) = length xs"
proof -
  have "sorted_wrt (\<lambda>x y. (c x, x) \<le> (c y, y)) (sort_key (\<lambda>e. (c e, e)) xs)"
    using sorted_sort_key[of "\<lambda>e. (c e, e)" xs] by (simp add: sorted_map)
  hence "sorted_wrt (\<lambda>x y. c x \<le> c y) (sort_key (\<lambda>e. (c e, e)) xs)"
    by (rule sorted_wrt_mono_rel[rotated]) (auto simp: less_eq_prod_def)
  thus "sorted_wrt (\<lambda>x y. c x \<ge> c y) (sort_desc_qs c xs)"
    by (simp add: sort_desc_qs_def sorted_wrt_rev)
qed (simp_all add: sort_desc_qs_def)

lemma qsort_f_qs_key: "qsort_f (qs_key ks) xs = sort_desc_qs ((!) ks) xs"
proof -
  have "qsort_f (qs_key ks) xs = rev (sort_key (qs_key ks) xs)"
    using sorted_desc_unique[OF qs_key_inj qsort_f_mset qsort_f_sorted] .
  thus ?thesis
    by (simp add: sort_desc_qs_def qs_key_def[abs_def])
qed

subsection \<open>Imperative Algorithm\<close>

text \<open>The array \<open>a\<close> holds the elements to be sorted and the array \<open>k\<close> their keys. Elements are
  compared by \<open>qs_key ks\<close>, i.e. the comparison of an element \<open>v\<close> with the pivot \<open>p\<close> looks up
  the key of \<open>v\<close> in \<open>k\<close> only.\<close>

definition swap_i :: "'a::heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "swap_i a i j = do {
     x \<leftarrow> Array.nth a i;
     y \<leftarrow> Array.nth a j;
     Array.upd i y a;
     Array.upd j x a;
     return ()
   }"

lemma swap_i_rule[sep_heap_rules]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow>
    <a \<mapsto>\<^sub>a xs> swap_i a i j <\<lambda>_. a \<mapsto>\<^sub>a swap_l xs i j>"
  unfolding swap_i_def swap_l_def by sep_auto

partial_function (heap) part1_i ::
  "('k::{linorder, heap}) array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'k \<times> nat \<Rightarrow> nat Heap" where
  "part1_i k a l r p =
    (if r \<le> l then return r
     else do {
       v \<leftarrow> Array.nth a l;
       kv \<leftarrow> Array.nth k v;
       if p \<le> (kv, v) then part1_i k a (l + 1) r p
       else do {
         swap_i a l r;
         part1_i k a l (r - 1) p
       }
     })"

lemma set_swap_l: "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> set (swap_l xs i j) = set xs"
  by (metis swap_l_mset set_mset_mset)

lemma part1_i_rule:
  "f = qs_key ks \<Longrightarrow> r < length xs \<Longrightarrow> \<forall>x \<in> set xs. x < length ks \<Longrightarrow>
    <a \<mapsto>\<^sub>a xs * k \<mapsto>\<^sub>a ks>
      part1_i k a l r p
    <\<lambda>m. a \<mapsto>\<^sub>a fst (part1_f f xs l r p) * k \<mapsto>\<^sub>a ks * \<up>(m = snd (part1_f f xs l r p))>"
proof (induction f xs l r p rule: part1_f.induct)
  case (1 f xs l r p)
  show ?case
  proof (cases "r \<le> l")
    case True
    hence eq: "part1_f f xs l r p = (xs, r)"
      by (simp add: part1_f.simps[of f xs l r p])
    show ?thesis
      unfolding eq using True by (subst part1_i.simps) sep_auto
  next
    case lr: False
    hence l: "l < length xs" "xs ! l < length ks"
      using "1.prems"(2,3) by auto
    show ?thesis
    proof (cases "p \<le> f (xs ! l)")
      case le: True
      hence eq: "part1_f f xs l r p = part1_f f xs (l + 1) r p"
        using lr by (simp add: part1_f.simps[of f xs l r p])
      have le': "p \<le> (ks ! (xs ! l), xs ! l)"
        using le "1.prems"(1) by (simp add: qs_key_def)
      note IH = "1.IH"(1)[OF lr le "1.prems"]
      show ?thesis
        unfolding eq using lr le' l
        by (subst part1_i.simps) (sep_auto heap: IH)
    next
      case le: False
      hence eq: "part1_f f xs l r p = part1_f f (swap_l xs l r) l (r - 1) p"
        using lr by (simp add: part1_f.simps[of f xs l r p])
      have le': "\<not> p \<le> (ks ! (xs ! l), xs ! l)"
        using le "1.prems"(1) by (simp add: qs_key_def)
      have prems: "r - 1 < length (swap_l xs l r)"
        "\<forall>x \<in> set (swap_l xs l r). x < length ks"
        using "1.prems"(2,3) lr by (auto simp: set_swap_l)
      note IH = "1.IH"(2)[OF lr le "1.prems"(1) prems]
      show ?thesis
        unfolding eq using lr le' l "1.prems"(2)
        by (subst part1_i.simps) (sep_auto heap: IH)
    qed
  qed
qed

definition partition_i :: "('k::{linorder, heap}) array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "partition_i k a l r = do {
     pv \<leftarrow> Array.nth a r;
     kp \<leftarrow> Array.nth k pv;
     m \<leftarrow> part1_i k a l (r - 1) (kp, pv);
     v \<leftarrow> Array.nth a m;
     kv \<leftarrow> Array.nth k v;
     let m' = (if (kp, pv) \<le> (kv, v) then m + 1 else m);
     swap_i a m' r;
     return m'
   }"

lemma partition_i_rule:
  assumes "l < r" "r < length xs" "\<forall>x \<in> set xs. x < length ks"
  shows "<a \<mapsto>\<^sub>a xs * k \<mapsto>\<^sub>a ks>
           partition_i k a l r
         <\<lambda>m. a \<mapsto>\<^sub>a fst (partition_f (qs_key ks) xs l r) * k \<mapsto>\<^sub>a ks *
           \<up>(m = snd (partition_f (qs_key ks) xs l r))>"
proof -
  let ?p = "(ks ! (xs ! r), xs ! r)"
  obtain ys m where pf: "part1_f (qs_key ks) xs l (r - 1) ?p = (ys, m)"
    by fastforce
  define m' where "m' = (if ?p \<le> (ks ! (ys ! m), ys ! m) then m + 1 else m)"
  have part_eq: "partition_f (qs_key ks) xs l r = (swap_l ys m' r, m')"
    using pf by (simp add: partition_f_def qs_key_def m'_def Let_def)
  have r1: "r - 1 < length xs"
    using assms by simp
  note P = part1_f_props[OF pf r1]
  have m: "l \<le> m" "m \<le> r - 1"
    using P(4) assms(1) by auto
  have m'r: "m' \<le> r"
    using m assms(1) by (auto simp: m'_def)
  have set_ys: "set ys = set xs"
    using P(2) by (metis set_mset_mset)
  have bnd: "r < length ys" "m < length ys" "xs ! r < length ks" "ys ! m < length ks"
    using P(1) m assms set_ys by auto
  have P1: "<a \<mapsto>\<^sub>a xs * k \<mapsto>\<^sub>a ks> part1_i k a l (r - 1) ?p
      <\<lambda>m''. a \<mapsto>\<^sub>a ys * k \<mapsto>\<^sub>a ks * \<up>(m'' = m)>"
    using part1_i_rule[OF refl r1 assms(3), of a k l ?p] pf by simp
  have m'_lt: "m' < length ys"
    using m'r bnd(1) by simp
  show ?thesis
  proof (cases "?p \<le> (ks ! (ys ! m), ys ! m)")
    case True
    hence "m' = m + 1"
      by (simp add: m'_def)
    thus ?thesis
      unfolding partition_i_def part_eq Let_def using bnd m'_lt True
      by (sep_auto heap: P1)
  next
    case False
    hence "m' = m"
      by (simp add: m'_def)
    thus ?thesis
      unfolding partition_i_def part_eq Let_def using bnd m'_lt False
      by (sep_auto heap: P1)
  qed
qed

partial_function (heap) quicksort_i ::
  "('k::{linorder, heap}) array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "quicksort_i k a l r =
    (if l < r then do {
       m \<leftarrow> partition_i k a l r;
       quicksort_i k a l (m - 1);
       quicksort_i k a (m + 1) r
     }
     else return ())"

lemma quicksort_i_rule:
  "f = qs_key ks \<Longrightarrow> r < length xs \<Longrightarrow> \<forall>x \<in> set xs. x < length ks \<Longrightarrow>
    <a \<mapsto>\<^sub>a xs * k \<mapsto>\<^sub>a ks>
      quicksort_i k a l r
    <\<lambda>_. a \<mapsto>\<^sub>a quicksort_f f xs l r * k \<mapsto>\<^sub>a ks>"
proof (induction f xs l r rule: quicksort_f.induct)
  case (1 f xs l r)
  show ?case
  proof (cases "l < r")
    case False
    hence eq: "quicksort_f f xs l r = xs"
      by (simp add: quicksort_f.simps[of f xs l r])
    show ?thesis
      unfolding eq using False by (subst quicksort_i.simps) sep_auto
  next
    case lr: True
    obtain ys m where pf: "partition_f f xs l r = (ys, m)"
      by fastforce
    note P = partition_f_props[OF pf lr "1.prems"(2)]
    have bnd: "l \<le> m \<and> m \<le> r"
      using P(4,5) by simp
    have eq: "quicksort_f f xs l r = quicksort_f f (quicksort_f f ys l (m - 1)) (m + 1) r"
      using pf lr bnd by (simp add: quicksort_f.simps[of f xs l r])
    have m1: "m - 1 < length ys"
      using P(1) bnd "1.prems"(2) by arith
    have set_ys: "\<forall>x \<in> set ys. x < length ks"
      using P(2) "1.prems"(3) by (metis set_mset_mset)
    note IH1 = "1.IH"(1)[OF lr pf[symmetric] refl bnd "1.prems"(1) m1 set_ys]
    have r2: "r < length (quicksort_f f ys l (m - 1))"
      using quicksort_f_props(1)[OF m1, where f = f and l = l] P(1) "1.prems"(2) by simp
    have set_q: "\<forall>x \<in> set (quicksort_f f ys l (m - 1)). x < length ks"
      using quicksort_f_props(2)[OF m1, where f = f and l = l] set_ys by (metis set_mset_mset)
    note IH2 = "1.IH"(2)[OF lr pf[symmetric] refl bnd "1.prems"(1) r2 set_q]
    have PR: "<a \<mapsto>\<^sub>a xs * k \<mapsto>\<^sub>a ks> partition_i k a l r
        <\<lambda>m'. a \<mapsto>\<^sub>a ys * k \<mapsto>\<^sub>a ks * \<up>(m' = m)>"
      using partition_i_rule[OF lr "1.prems"(2,3), of a k] pf "1.prems"(1) by simp
    show ?thesis
      unfolding eq using lr
      by (subst quicksort_i.simps) (sep_auto heap: PR IH1 IH2)
  qed
qed

text \<open>The array is sorted in-place, and the same array is returned.\<close>

definition qsort_desc :: "('k::{linorder, heap}) array \<Rightarrow> nat array \<Rightarrow> nat array Heap" where
  "qsort_desc k a = do {
     n \<leftarrow> Array.len a;
     quicksort_i k a 0 (n - 1);
     return a
   }"

lemma qsort_desc_rule[sep_heap_rules]:
  assumes "\<forall>x \<in> set xs. x < length ks"
  shows "<a \<mapsto>\<^sub>a xs * k \<mapsto>\<^sub>a ks> qsort_desc k a
    <\<lambda>r. a \<mapsto>\<^sub>a sort_desc_qs ((!) ks) xs * k \<mapsto>\<^sub>a ks * \<up>(r = a)>"
proof (cases "xs = []")
  case True
  thus ?thesis
    unfolding qsort_desc_def
    by (subst quicksort_i.simps) (sep_auto simp: sort_desc_qs_def)
next
  case False
  hence "length xs - 1 < length xs"
    by simp
  note QS = quicksort_i_rule[OF refl this assms, of a k 0]
  show ?thesis
    unfolding qsort_desc_def
    by (sep_auto heap: QS simp: qsort_f_qs_key[symmetric] qsort_f_def)
qed

lemmas [code] = swap_i_def part1_i.simps partition_i_def quicksort_i.simps qsort_desc_def

end
