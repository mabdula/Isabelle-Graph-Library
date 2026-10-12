theory CSR_Buildup
  imports Main
begin

section \<open>Building a CSR Representation of a Multigraph\<close>

text \<open>
  A multigraph is given by a collection of edges of an arbitrary type @{typ 'e}.
  Every edge has a source vertex, and vertices are mapped to indices \<open>0..<n\<close>.
  The CSR representation consists of
  \<^item> an edge array \<open>E\<close> of length \<open>m\<close> where the edges are grouped by (the index of) their source,
  \<^item> a boundary array \<open>B\<close> of length \<open>n+1\<close> with \<open>B!0 = 0\<close> and \<open>B!n = m\<close>,
    such that the edges leaving the vertex with index \<open>i\<close> are exactly \<open>E[B!i..<B!(i+1)]\<close>.

  The edges are not given as a list but by a restartable iterator.
  This covers both an explicit sequence of edges and a counter over a range of edge names.
\<close>

subsection \<open>Iterators\<close>

text \<open>
  An iterator state \<open>s\<close> is abstracted to the list \<open>it_seq s\<close> of elements still to be produced.
\<close>

locale iterator =
  fixes it_next :: "'s \<Rightarrow> ('e \<times> 's) option"
    and it_seq :: "'s \<Rightarrow> 'e list"
    and it_invar :: "'s \<Rightarrow> bool"
  assumes it_next_None: "it_invar s \<Longrightarrow> it_next s = None \<longleftrightarrow> it_seq s = []"
      and it_next_Some: "\<lbrakk>it_invar s; it_next s = Some (e, s')\<rbrakk>
                          \<Longrightarrow> it_invar s' \<and> it_seq s = e # it_seq s'"
begin

partial_function (tailrec) it_fold :: "('e \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 's \<Rightarrow> 'a \<Rightarrow> 'a" where
  "it_fold f s acc =
     (case it_next s of None \<Rightarrow> acc
                      | Some (e, s') \<Rightarrow> it_fold f s' (f e acc))"

lemma it_fold_is_fold:
  assumes "it_invar s"
  shows "it_fold f s acc = fold f (it_seq s) acc"
  using assms
proof (induction "it_seq s" arbitrary: s acc)
  case Nil
  hence "it_next s = None"
    by (simp add: it_next_None)
  thus ?case
    by (subst it_fold.simps) (simp add: Nil.hyps[symmetric])
next
  case (Cons e es)
  obtain e' s' where next_s: "it_next s = Some (e', s')"
    using Cons.prems Cons.hyps(2) it_next_None by (cases "it_next s") fastforce+
  with Cons.prems have "it_invar s'" "it_seq s = e' # it_seq s'"
    by (auto dest: it_next_Some)
  with Cons.hyps have "e' = e" "es = it_seq s'"
    by auto
  with Cons.hyps(1) \<open>it_invar s'\<close> \<open>it_seq s = e' # it_seq s'\<close> show ?case
    by (subst it_fold.simps) (simp add: next_s)
qed

end

subsubsection \<open>Instances\<close>

text \<open>A counter over the range \<open>[lo..<hi]\<close>, needing constant memory.\<close>

definition range_next :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "range_next hi k = (if k < hi then Some (k, Suc k) else None)"

definition range_seq :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "range_seq hi k = [k..<hi]"

interpretation range_it: iterator "range_next hi" "range_seq hi" "\<lambda>_. True"
  by unfold_locales
     (auto simp add: range_next_def range_seq_def upt_conv_Cons split: if_splits)

text \<open>An explicit sequence of edges.\<close>

fun list_next :: "'e list \<Rightarrow> ('e \<times> 'e list) option" where
  "list_next [] = None"
| "list_next (x # xs) = Some (x, xs)"

interpretation list_it: iterator list_next id "\<lambda>_. True"
  by unfold_locales (auto elim: list_next.elims)

subsection \<open>Auxiliary Lemmas on Lists\<close>

lemma concat_eqI:
  assumes "length xs = sum_list (map length Ls)"
      and "\<And>k i. k < length Ls \<Longrightarrow> i < length (Ls ! k)
                \<Longrightarrow> xs ! (sum_list (map length (take k Ls)) + i) = Ls ! k ! i"
  shows "xs = concat Ls"
  using assms
proof (induction Ls arbitrary: xs)
  case Nil
  thus ?case
    by simp
next
  case (Cons L Ls)
  have "take (length L) xs = L"
    using Cons.prems(1) Cons.prems(2)[of 0] by (intro nth_equalityI) auto
  moreover have "drop (length L) xs = concat Ls"
  proof (rule Cons.IH)
    show "length (drop (length L) xs) = sum_list (map length Ls)"
      using Cons.prems(1) by simp
  next
    fix k i
    assume "k < length Ls" "i < length (Ls ! k)"
    hence "xs ! (sum_list (map length (take (Suc k) (L # Ls))) + i) = (L # Ls) ! Suc k ! i"
      by (intro Cons.prems(2)) auto
    thus "drop (length L) xs ! (sum_list (map length (take k Ls)) + i) = Ls ! k ! i"
      using Cons.prems(1) by (simp add: add.assoc)
  qed
  ultimately show ?case
    by (metis append_take_drop_id concat.simps(2))
qed

lemma sum_length_filter_key:
  fixes f :: "'a \<Rightarrow> nat"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> f x < n"
  shows "(\<Sum>k\<in>{0..<n}. length (filter (\<lambda>x. f x = k) xs)) = length xs"
  using assms
proof (induction xs)
  case Nil
  thus ?case
    by simp
next
  case (Cons x xs)
  have "(\<Sum>k\<in>{0..<n}. length (filter (\<lambda>y. f y = k) (x # xs)))
        = (\<Sum>k\<in>{0..<n}. (if f x = k then 1 else 0) + length (filter (\<lambda>y. f y = k) xs))"
    by (rule sum.cong) auto
  also have "\<dots> = (\<Sum>k\<in>{0..<n}. if f x = k then 1 else 0) + length xs"
    using Cons by (simp add: sum.distrib)
  also have "(\<Sum>k\<in>{0..<n}. if f x = k then 1 else (0::nat)) = 1"
    using Cons.prems[of x] by (subst sum.delta') auto
  finally show ?case
    by simp
qed

subsection \<open>Specification\<close>

text \<open>
  The construction only needs a key \<open>key e < n\<close> for every edge,
  which will be the index of the source vertex.
\<close>

locale csr_buildup = iterator it_next it_seq it_invar
  for it_next :: "'s \<Rightarrow> ('e \<times> 's) option"
    and it_seq :: "'s \<Rightarrow> 'e list"
    and it_invar :: "'s \<Rightarrow> bool" +
  fixes key :: "'e \<Rightarrow> nat"
    and n :: nat
    and s0 :: 's
  assumes s0_invar: "it_invar s0"
      and key_bound: "e \<in> set (it_seq s0) \<Longrightarrow> key e < n"
begin

definition "es = it_seq s0"

definition "blk i = filter (\<lambda>e. key e = i) es"

definition "E_spec = concat (map blk [0..<n])"

definition "B_spec = map (\<lambda>i. sum_list (map (length \<circ> blk) [0..<i])) [0..<Suc n]"

subsection \<open>Functional Algorithm\<close>

text \<open>
  A counting sort in three passes that uses no memory beyond \<open>B\<close> and \<open>E\<close>:
  \<^enum> Count: \<open>B!(k+2)\<close> counts the edges with key \<open>k\<close> (for \<open>k+2 \<le> n\<close>), and \<open>m\<close> counts all edges.
  \<^enum> Prefix sums over \<open>B\<close>: afterwards \<open>B!(k+1)\<close> is the start of block \<open>k\<close>.
  \<^enum> Fill with a restarted iterator: \<open>B!(k+1)\<close> serves as the cursor of block \<open>k\<close>.
    Once all edges are placed, \<open>B!(k+1)\<close> is the end of block \<open>k\<close>, i.e.\ the start of block \<open>k+1\<close>.
\<close>

definition count_step :: "'e \<Rightarrow> nat list \<times> nat \<Rightarrow> nat list \<times> nat" where
  "count_step e = (\<lambda>(B, m).
     (let k = key e in if k + 2 \<le> n then B[k + 2 := B ! (k + 2) + 1] else B, Suc m))"

definition "count_edges = it_fold count_step s0 (replicate (Suc n) 0, 0)"

definition prefix_step :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "prefix_step j B = B[j := B ! j + B ! (j - 1)]"

definition prefix_sums :: "nat list \<Rightarrow> nat list" where
  "prefix_sums B = fold prefix_step [1..<Suc n] B"

text \<open>The edge array is initialised with the first edge, so no default element of @{typ 'e} is needed.\<close>

definition init_E :: "nat \<Rightarrow> 'e list" where
  "init_E m = (case it_next s0 of None \<Rightarrow> [] | Some (e, _) \<Rightarrow> replicate m e)"

definition fill_step :: "'e \<Rightarrow> nat list \<times> 'e list \<Rightarrow> nat list \<times> 'e list" where
  "fill_step e = (\<lambda>(B, E).
     (let k = key e; p = B ! (k + 1) in (B[k + 1 := Suc p], E[p := e])))"

definition csr_build :: "nat list \<times> 'e list" where
  "csr_build =
     (let (B, m) = count_edges;
          B = prefix_sums B
      in it_fold fill_step s0 (B, init_E m))"

subsection \<open>Correctness\<close>

definition sel :: "nat \<Rightarrow> 'e list \<Rightarrow> 'e list" where
  "sel k xs = filter (\<lambda>e. key e = k) xs"

lemma sel_Nil[simp]: "sel k [] = []"
  by (simp add: sel_def)

lemma sel_Cons: "sel k (x # xs) = (if key x = k then x # sel k xs else sel k xs)"
  by (simp add: sel_def)

lemma sel_single[simp]: "sel k [x] = (if key x = k then [x] else [])"
  by (simp add: sel_def)

lemma sel_append[simp]: "sel k (xs @ ys) = sel k xs @ sel k ys"
  by (simp add: sel_def)

lemma blk_sel: "blk k = sel k es"
  by (simp add: blk_def sel_def)

lemma it_fold_s0: "it_fold f s0 acc = fold f es acc"
  by (simp add: it_fold_is_fold[OF s0_invar] es_def)

lemma key_es: "x \<in> set es \<Longrightarrow> key x < n"
  using key_bound by (simp add: es_def)

text \<open>Start of the block with key \<open>k\<close> in \<open>E_spec\<close>.\<close>

definition "start k = sum_list (map (length \<circ> blk) [0..<k])"

lemma start_0[simp]: "start 0 = 0"
  by (simp add: start_def)

lemma start_Suc: "start (Suc k) = start k + length (blk k)"
  by (simp add: start_def)

lemma start_mono: "k \<le> k' \<Longrightarrow> start k \<le> start k'"
  by (induction k') (auto simp add: start_Suc le_Suc_eq intro: trans_le_add1)

lemma start_n: "start n = length es"
proof -
  have "start n = (\<Sum>k\<in>{0..<n}. length (filter (\<lambda>x. key x = k) es))"
    by (simp add: start_def blk_def interv_sum_list_conv_sum_set_nat)
  also have "\<dots> = length es"
    using key_es by (rule sum_length_filter_key)
  finally show ?thesis .
qed

lemma start_blk_le: "k < n \<Longrightarrow> start k + length (blk k) \<le> length es"
  using start_mono[of "Suc k" n] by (simp add: start_Suc start_n)

lemma B_spec_start: "B_spec = map start [0..<Suc n]"
  by (simp add: B_spec_def start_def)

subsubsection \<open>Counting\<close>

definition count_B :: "'e list \<Rightarrow> nat list" where
  "count_B xs = map (\<lambda>i. if i < 2 then 0 else length (sel (i - 2) xs)) [0..<Suc n]"

lemma length_count_B[simp]: "length (count_B xs) = Suc n"
  by (simp add: count_B_def)

lemma count_B_nth: "i < Suc n \<Longrightarrow> count_B xs ! i = (if i < 2 then 0 else length (sel (i - 2) xs))"
  unfolding count_B_def by (subst nth_map_upt) auto

lemma count_step_count_B:
  "count_step x (count_B xs, length xs) = (count_B (xs @ [x]), length (xs @ [x]))"
  unfolding count_step_def Let_def
  by (auto intro!: nth_equalityI simp add: count_B_nth nth_list_update)

lemma fold_count_step: "fold count_step xs (replicate (Suc n) 0, 0) = (count_B xs, length xs)"
proof (induction xs rule: rev_induct)
  case Nil
  have "replicate (Suc n) 0 = count_B []"
    by (intro nth_equalityI) (simp_all add: count_B_nth del: replicate_Suc)
  thus ?case
    by simp
next
  case (snoc x xs)
  thus ?case
    by (simp add: count_step_count_B)
qed

lemma count_edges: "count_edges = (count_B es, length es)"
  by (simp add: count_edges_def it_fold_s0 fold_count_step del: replicate_Suc)

subsubsection \<open>Prefix Sums\<close>

lemma fold_prefix_step:
  assumes "j \<le> n"
  shows "fold prefix_step [1..<Suc j] (map g [0..<Suc n])
         = map (\<lambda>i. if i \<le> j then sum_list (map g [0..<Suc i]) else g i) [0..<Suc n]"
  using assms
proof (induction j)
  case 0
  have "[1..<Suc 0] = []"
    by simp
  thus ?case
    by (simp only: fold_Nil id_apply) (intro map_cong, simp_all)
next
  case (Suc j)
  have "fold prefix_step [1..<Suc (Suc j)] (map g [0..<Suc n])
        = prefix_step (Suc j) (fold prefix_step [1..<Suc j] (map g [0..<Suc n]))"
    by simp
  also have "\<dots> = prefix_step (Suc j)
                (map (\<lambda>i. if i \<le> j then sum_list (map g [0..<Suc i]) else g i) [0..<Suc n])"
    using Suc by simp
  also have "\<dots> = map (\<lambda>i. if i \<le> Suc j then sum_list (map g [0..<Suc i]) else g i) [0..<Suc n]"
  proof (rule nth_equalityI)
    fix i
    assume "i < length (prefix_step (Suc j)
                (map (\<lambda>i. if i \<le> j then sum_list (map g [0..<Suc i]) else g i) [0..<Suc n]))"
    hence i: "i < Suc n"
      by (simp add: prefix_step_def del: upt_Suc)
    have "[0..<Suc (Suc j)] = [0..<Suc j] @ [Suc j]"
      by simp
    with i Suc.prems show "prefix_step (Suc j)
                (map (\<lambda>i. if i \<le> j then sum_list (map g [0..<Suc i]) else g i) [0..<Suc n]) ! i
          = map (\<lambda>i. if i \<le> Suc j then sum_list (map g [0..<Suc i]) else g i) [0..<Suc n] ! i"
      by (cases "i = Suc j") (simp_all add: prefix_step_def nth_list_update del: upt_Suc)
  qed (simp add: prefix_step_def del: upt_Suc)
  finally show ?case .
qed

lemma sum_count_B:
  "sum_list (map (\<lambda>l. if l < 2 then 0 else length (blk (l - 2))) [0..<Suc i]) = start (i - 1)"
proof (induction i)
  case 0
  show ?case
    by simp
next
  case (Suc i)
  thus ?case
    by (cases i) (simp_all add: start_Suc)
qed

lemma prefix_sums_count_B: "prefix_sums (count_B es) = map (\<lambda>i. start (i - 1)) [0..<Suc n]"
proof -
  have "count_B es = map (\<lambda>l. if l < 2 then 0 else length (blk (l - 2))) [0..<Suc n]"
    by (simp only: count_B_def blk_sel)
  thus ?thesis
    unfolding prefix_sums_def
    by (simp only: fold_prefix_step[OF order_refl])
       (intro map_cong, simp_all add: sum_count_B del: upt_Suc)
qed

subsubsection \<open>Filling\<close>

definition fill_invar :: "'e list \<Rightarrow> nat list \<times> 'e list \<Rightarrow> bool" where
  "fill_invar xs = (\<lambda>(B, E).
     length B = Suc n \<and> length E = length es \<and> B ! 0 = 0 \<and>
     (\<forall>k<n. B ! Suc k = start k + length (sel k xs)) \<and>
     (\<forall>k<n. \<forall>i<length (sel k xs). E ! (start k + i) = sel k xs ! i))"

lemma length_init_E: "length (init_E (length es)) = length es"
  unfolding init_E_def
  by (auto split: option.split simp add: es_def it_next_None[OF s0_invar])

lemma fill_invar_init: "fill_invar [] (prefix_sums (count_B es), init_E (length es))"
  by (simp add: fill_invar_def prefix_sums_count_B length_init_E del: upt_Suc)

lemma fill_step_invar:
  assumes es: "xs @ x # ys = es"
      and inv: "fill_invar xs (B, E)"
  shows "fill_invar (xs @ [x]) (fill_step x (B, E))"
proof -
  define k where "k = key x"
  have kx[simp]: "key x = k"
    by (simp add: k_def)
  have k_lt: "k < n"
    using key_es[of x] by (simp add: es[symmetric])
  from inv have lenB: "length B = Suc n" and lenE: "length E = length es" and B0: "B ! 0 = 0"
    and Bk: "\<And>k. k < n \<Longrightarrow> B ! Suc k = start k + length (sel k xs)"
    and Ek: "\<And>k i. k < n \<Longrightarrow> i < length (sel k xs) \<Longrightarrow> E ! (start k + i) = sel k xs ! i"
    by (auto simp add: fill_invar_def)
  define p where "p = B ! Suc k"
  have p: "p = start k + length (sel k xs)"
    using Bk k_lt by (simp add: p_def)
  have sel_le: "length (sel k' (xs @ [x])) \<le> length (blk k')" for k'
  proof -
    have "blk k' = sel k' (xs @ [x]) @ sel k' ys"
      unfolding blk_sel es[symmetric] by (simp add: sel_Cons)
    thus ?thesis
      by simp
  qed
  have sel_k: "sel k (xs @ [x]) = sel k xs @ [x]"
    by simp
  have p_blk: "Suc p \<le> start k + length (blk k)"
    using sel_le[of k] by (simp add: p sel_k)
  hence p_lt: "p < length es"
    using start_blk_le[OF k_lt] by simp
  have fs: "fill_step x (B, E) = (B[Suc k := Suc p], E[p := x])"
    by (simp add: fill_step_def p_def Let_def)
  have B': "\<forall>k'<n. B[Suc k := Suc p] ! Suc k' = start k' + length (sel k' (xs @ [x]))"
    using Bk lenB k_lt p by auto
  have E': "\<forall>k'<n. \<forall>i<length (sel k' (xs @ [x])). E[p := x] ! (start k' + i) = sel k' (xs @ [x]) ! i"
  proof (intro allI impI)
    fix k' i
    assume k': "k' < n" and i: "i < length (sel k' (xs @ [x]))"
    show "E[p := x] ! (start k' + i) = sel k' (xs @ [x]) ! i"
    proof (cases "k' = k")
      case True
      show ?thesis
      proof (cases "i = length (sel k xs)")
        case True
        with \<open>k' = k\<close> show ?thesis
          using p p_lt lenE by (simp add: sel_k)
      next
        case False
        with i \<open>k' = k\<close> have "i < length (sel k xs)"
          by (simp add: sel_k)
        with \<open>k' = k\<close> show ?thesis
          using Ek[OF k_lt] p by (simp add: sel_k nth_append)
      qed
    next
      case False
      hence sel_eq: "sel k' (xs @ [x]) = sel k' xs"
        by simp
      have i_blk: "start k' + i < start (Suc k')"
        using i sel_le[of k'] by (simp add: start_Suc)
      have "start k' + i \<noteq> p"
      proof (cases "k' < k")
        case True
        hence "start (Suc k') \<le> start k"
          by (intro start_mono) simp
        thus ?thesis
          using i_blk p by simp
      next
        case False
        with \<open>k' \<noteq> k\<close> have "start (Suc k) \<le> start k'"
          by (intro start_mono) simp
        thus ?thesis
          using p_blk by (simp add: start_Suc)
      qed
      thus ?thesis
        using Ek[OF k'] i \<open>k' \<noteq> k\<close> by auto
    qed
  qed
  show ?thesis
    unfolding fs fill_invar_def using lenB lenE B0 B' E' by simp
qed

text \<open>The array accesses of a fill step are within bounds.\<close>

lemma fill_step_bounds:
  assumes es: "xs @ x # ys = es"
      and inv: "fill_invar xs (B, E)"
  shows "Suc (key x) < length B" "B ! Suc (key x) < length E"
proof -
  have k: "key x < n"
    using key_es[of x] by (simp add: es[symmetric])
  have "blk (key x) = sel (key x) xs @ x # sel (key x) ys"
    unfolding blk_sel es[symmetric] by (simp add: sel_Cons)
  hence "Suc (length (sel (key x) xs)) \<le> length (blk (key x))"
    by simp
  thus "Suc (key x) < length B" "B ! Suc (key x) < length E"
    using inv k start_blk_le[OF k] by (auto simp add: fill_invar_def)
qed

lemma fold_fill:
  assumes "xs @ ys = es"
      and "fill_invar [] S"
  shows "fill_invar xs (fold fill_step xs S)"
  using assms(1)
proof (induction xs arbitrary: ys rule: rev_induct)
  case Nil
  show ?case
    using assms(2) by simp
next
  case (snoc x xs)
  from snoc.prems have es: "xs @ x # ys = es"
    by simp
  obtain B E where BE: "fold fill_step xs S = (B, E)"
    by fastforce
  from snoc.IH[of "x # ys"] es BE have "fill_invar xs (B, E)"
    by simp
  with es BE show ?case
    by (simp add: fill_step_invar)
qed

subsubsection \<open>Main Theorem\<close>

text \<open>The fill pass does not depend on the initial contents of the edge array, only on its length.\<close>

theorem fill_correct:
  assumes "length E0 = length es"
  shows "fold fill_step es (prefix_sums (count_B es), E0) = (B_spec, E_spec)"
proof -
  obtain B E where BE: "fold fill_step es (prefix_sums (count_B es), E0) = (B, E)"
    by fastforce
  have "fill_invar [] (prefix_sums (count_B es), E0)"
    using assms by (simp add: fill_invar_def prefix_sums_count_B del: upt_Suc)
  hence "fill_invar es (B, E)"
    using fold_fill[of es "[]"] BE by fastforce
  hence lenB: "length B = Suc n" and lenE: "length E = length es" and B0: "B ! 0 = 0"
    and Bk: "\<And>k. k < n \<Longrightarrow> B ! Suc k = start (Suc k)"
    and Ek: "\<And>k i. k < n \<Longrightarrow> i < length (blk k) \<Longrightarrow> E ! (start k + i) = blk k ! i"
    by (auto simp add: fill_invar_def start_Suc blk_sel)
  have "B = B_spec"
  proof (rule nth_equalityI)
    show "length B = length B_spec"
      using lenB by (simp add: B_spec_start)
  next
    fix i
    assume "i < length B"
    thus "B ! i = B_spec ! i"
      using lenB B0 Bk by (cases i) (simp_all add: B_spec_start nth_Cons' del: upt_Suc)
  qed
  moreover have "E = E_spec"
    unfolding E_spec_def
  proof (rule concat_eqI)
    show "length E = sum_list (map length (map blk [0..<n]))"
      using lenE start_n by (simp add: start_def)
  next
    fix k i
    assume "k < length (map blk [0..<n])" "i < length (map blk [0..<n] ! k)"
    thus "E ! (sum_list (map length (take k (map blk [0..<n]))) + i) = map blk [0..<n] ! k ! i"
      using Ek by (simp add: take_map start_def)
  qed
  ultimately show ?thesis
    using BE by simp
qed

theorem csr_build_correct: "csr_build = (B_spec, E_spec)"
  using fill_correct[OF length_init_E] by (simp add: csr_build_def count_edges it_fold_s0)

subsubsection \<open>Reading off the Blocks\<close>

lemma E_spec_split:
  assumes "k < n"
  shows "E_spec = concat (map blk [0..<k]) @ blk k @ concat (map blk [Suc k..<n])"
proof -
  have "[0..<n] = [0..<k] @ [k..<n]"
    using assms upt_add_eq_append[of 0 k "n - k"] by simp
  also have "[k..<n] = k # [Suc k..<n]"
    using assms by (metis upt_conv_Cons)
  finally show ?thesis
    by (simp add: E_spec_def)
qed

lemma length_concat_blk: "length (concat (map blk [0..<k])) = start k"
  by (simp add: length_concat start_def)

lemma B_spec_nth: "i \<le> n \<Longrightarrow> B_spec ! i = start i"
  by (simp add: B_spec_start del: upt_Suc)

lemma B_spec_0: "B_spec ! 0 = 0"
  by (simp add: B_spec_nth)

lemma B_spec_n: "B_spec ! n = length es"
  by (simp add: B_spec_nth start_n)

lemma length_B_spec: "length B_spec = Suc n"
  by (simp add: B_spec_start)

lemma length_E_spec: "length E_spec = length es"
  using length_concat_blk[of n] start_n by (simp add: E_spec_def)

lemma csr_block:
  assumes "k < n"
  shows "take (B_spec ! Suc k - B_spec ! k) (drop (B_spec ! k) E_spec) = blk k"
  using assms
  by (simp add: B_spec_nth start_Suc E_spec_split length_concat_blk[symmetric])

corollary csr_build_block:
  assumes "csr_build = (B, E)" "k < n"
  shows "take (B ! Suc k - B ! k) (drop (B ! k) E) = filter (\<lambda>e. key e = k) (it_seq s0)"
  using assms csr_block by (simp add: csr_build_correct blk_def es_def)

end

subsection \<open>Multigraphs\<close>

text \<open>
  The key of an edge is the index of its source vertex.
  Injectivity of the index is only needed to read off the out-edges of a vertex.
  The targets @{term tgt} play no role in the construction.
\<close>

locale csr_multigraph = iterator it_next it_seq it_invar
  for it_next :: "'s \<Rightarrow> ('e \<times> 's) option"
    and it_seq :: "'s \<Rightarrow> 'e list"
    and it_invar :: "'s \<Rightarrow> bool" +
  fixes src :: "'e \<Rightarrow> 'v"
    and tgt :: "'e \<Rightarrow> 'v"
    and V :: "'v set"
    and vidx :: "'v \<Rightarrow> nat"
    and n :: nat
    and s0 :: 's
  assumes s0_invar': "it_invar s0"
      and vidx_inj: "inj_on vidx V"
      and vidx_bound: "v \<in> V \<Longrightarrow> vidx v < n"
      and src_in_V: "e \<in> set (it_seq s0) \<Longrightarrow> src e \<in> V"
begin

sublocale csr: csr_buildup it_next it_seq it_invar "vidx \<circ> src" n s0
  by unfold_locales (auto intro: s0_invar' vidx_bound src_in_V)

definition "out_edges v = filter (\<lambda>e. src e = v) csr.es"

lemma blk_vidx: "v \<in> V \<Longrightarrow> csr.blk (vidx v) = out_edges v"
  unfolding csr.blk_def out_edges_def
  by (intro filter_cong) (auto dest: inj_onD[OF vidx_inj] src_in_V simp add: csr.es_def)

theorem csr_out_edges:
  assumes "csr.csr_build = (B, E)" "v \<in> V"
  shows "take (B ! Suc (vidx v) - B ! vidx v) (drop (B ! vidx v) E) = out_edges v"
  using assms csr.csr_block[of "vidx v"] vidx_bound[of v]
  by (simp add: csr.csr_build_correct blk_vidx)

end

end


