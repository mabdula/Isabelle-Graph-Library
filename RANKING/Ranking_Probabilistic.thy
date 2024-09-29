section \<open>RANKING as Randomized Algorithm\label{sec:prob}\<close>
theory Ranking_Probabilistic
  imports
    Ranking
    Misc
    "HOL-Probability.Random_Permutations"
    "HOL-Probability.Product_PMF"
    "HOL-Real_Asymp.Real_Asymp"
begin
text \<open>
  In this final section we formulate RANKING as a randomized algorithm, and employ the previously
  proven facts to analyze the expected size of the matching produced by it.

  Large parts of this section deal with relating the sizes of different sets of permutations
  (\autoref{sec:prob-perms}).

  The entire probabilistic analysis is presented in~\autoref{sec:prob-wf}. The Monad Normalisation
  AFP entry by Schneider, Eberl, and Lochbihler~\cite{Monad_Normalisation-AFP} proved useful there.

  The final part (\autoref{sec:prob-limit}) considers the competitve ratio in the limit to obtain
  the original $1 - \frac{1}{e}$, which was made a breeze by Eberl's \<^emph>\<open>real\_asymp\<close>~\cite{eberl2019}.
\<close>


translations\<^marker>\<open>tag invisible\<close>
  "n" <= "CONST of_nat n"
  "n" <= "CONST int n"
  "n" <= "CONST real n"
  "n" <= "CONST real_of_nat n"
  "n" <= "CONST real_of_int n"
  "n" <= "CONST of_real n"
  "n" <= "CONST complex_of_real n"

no_syntax\<^marker>\<open>tag invisible\<close>
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /\<mapsto>/ _")
  "_maplets" :: "['a, 'a] \<Rightarrow> maplet"             ("_ /[\<mapsto>]/ _")
  ""         :: "maplet \<Rightarrow> maplets"             ("_")
  "_Maplets" :: "[maplet, maplets] \<Rightarrow> maplets" ("_,/ _")
  "_MapUpd"  :: "['a \<rightharpoonup> 'b, maplets] \<Rightarrow> 'a \<rightharpoonup> 'b" ("_/'(_')" [900, 0] 900)
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"            ("(1[_])")

no_syntax (ASCII)\<^marker>\<open>tag invisible\<close>
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /|->/ _")
  "_maplets" :: "['a, 'a] \<Rightarrow> maplet"             ("_ /[|->]/ _")


subsection \<open>Permutations\label{sec:prob-perms}\<close>
text \<open>
  This first set of lemmas is required to prove that choosing a random permutation \<^term>\<open>\<sigma>::'a list\<close>
  of a set \<^term>\<open>V::'a set\<close>, a random vertex \<^term>\<open>v \<in> V\<close> and putting it at some position \<^term>\<open>t::nat\<close>,
  i.e.\ \<^term>\<open>\<sigma>[v \<mapsto> t]\<close>, is the same as simply choosing a permutation of \<^term>\<open>V::'a set\<close>
  uniformly at random. To that end we show that for any permutation \<^term>\<open>\<sigma>::'a list\<close> of \<^term>\<open>V::'a set\<close>,
  and \<^term>\<open>v \<in> V\<close>
  there are exactly \<^term>\<open>card V\<close> permutations \<^term>\<open>\<sigma>'::'a list\<close> of \<^term>\<open>V::'a set\<close> s.t.
  \<^term>\<open>\<sigma>'[v \<mapsto> t] = \<sigma>\<close>. This follows intuitively from the fact that we can put \<^term>\<open>v\<close> at any one
  of \<^term>\<open>card V\<close> positions in \<^term>\<open>\<sigma>'::'a list\<close> as it will be moved to index \<^term>\<open>t::nat\<close>
  anyways.
\<close>
lemma permutation_move_to:
  assumes "\<sigma> \<in> permutations_of_set V"
  assumes "v \<in> V"
  shows "\<sigma>[v \<mapsto> t] \<in> permutations_of_set V"
  using assms
  by (auto intro!: permutations_of_setI simp: move_to_set dest: permutations_of_setD move_to_distinct)

lemma move_to_eq_unique_vertex:
  assumes "\<sigma>' \<in> permutations_of_set V"
  assumes "\<sigma> \<in> permutations_of_set V"
  assumes "index \<sigma> v = t" "v \<in> V"
  assumes "\<sigma> = \<sigma>'[w \<mapsto> t]"
  shows "v = w"
  using assms
  by (metis distinct_card index_eq_index_conv index_less_size_conv move_to_index_v permutations_of_setD)

lemma permutations_move_to_eq_iff:
  assumes "\<sigma> \<in> permutations_of_set V"
  assumes "t < length \<sigma>"
  assumes "\<sigma>' \<in> permutations_of_set V"
  shows "card (V \<inter> {v. \<sigma> = \<sigma>'[v \<mapsto> t]}) = 1 \<longleftrightarrow> [x <- \<sigma>'. x \<noteq> (THE v. index \<sigma> v = t)] = [x <- \<sigma>. x \<noteq> (THE v. index \<sigma> v = t)]"
proof (rule iffI)
  assume card_1: "card (V \<inter> {v. \<sigma> = \<sigma>'[v \<mapsto> t]}) = 1"
  with assms  obtain w where w: "w \<in> V" "\<sigma> = \<sigma>'[w \<mapsto> t]"
    by (smt (verit) card.empty disjoint_iff_not_equal mem_Collect_eq zero_neq_one)

  with card_1 assms have filter_eq: "[x <- \<sigma>'. x \<noteq> w] = [x <- \<sigma>. x \<noteq> w]"
    by (auto intro!: distinct_order_filter_eq dest: permutations_of_setD permutation_move_to
             simp: distinct_move_to_indices_if_eq)

  from w card_1 assms have "(THE v. index \<sigma> v = t) = w"
  proof (intro the_equality, goal_cases)
    case 1
    then show ?case thm move_to_index_v
      by (auto intro: move_to_index_v dest: permutations_of_setD simp: length_finite_permutations_of_set)
  next
    case (2 v)
    then have "v \<in> V"
      by (metis index_less_size_conv permutations_of_setD(1))
    with 2 show ?case
      by (auto intro: move_to_eq_unique_vertex)
  qed

  with filter_eq show "[x <- \<sigma>'. x \<noteq> (THE v. index \<sigma> v = t)] = [x <- \<sigma>. x \<noteq> (THE v. index \<sigma> v = t)]"
    by blast
next
  assume filter_eq: "[x <- \<sigma>'. x \<noteq> (THE v. index \<sigma> v = t)] = [x <- \<sigma>. x \<noteq> (THE v. index \<sigma> v = t)]"

  from assms obtain v where v: "index \<sigma> v = t" "v \<in> V"
    by (metis index_nth_id nth_mem permutations_of_setD(1) permutations_of_setD(2))

  with \<open>t < length \<sigma>\<close> have "(THE v. index \<sigma> v = t) = v"
    by (auto simp: index_less_size_conv)

  with assms filter_eq v have "\<sigma> = \<sigma>'[v \<mapsto> t]"
    by (metis distinct_count_in_set index_less_size_conv move_to_def move_to_id permutations_of_setD(2))

  have "\<And>v'. \<sigma> = \<sigma>'[v' \<mapsto> t] \<Longrightarrow> v' = v"
  proof (rule move_to_eq_unique_vertex[symmetric, OF assms(3) assms(1) \<open>index \<sigma> v = t\<close>], goal_cases)
    case (1 v')
    with \<open>index \<sigma> v = t\<close> assms(1) assms(2) show ?case
     by (metis  index_less_size_conv permutations_of_setD(1))
  next
    case (2 v')
    then show ?case by blast
  qed

  with v \<open>\<sigma> = \<sigma>'[v \<mapsto> t]\<close> have "{v. \<sigma> = \<sigma>'[v \<mapsto> t]} = {v}"
    by blast
    
  with v show "card (V \<inter> {v. \<sigma> = \<sigma>'[v \<mapsto> t]}) = 1"
    by simp
qed

lemma permutation_vertex_at_tE:
  assumes "\<sigma> \<in> permutations_of_set V" "v \<in> V" "t < length \<sigma>"
  obtains \<sigma>' where "\<sigma>' \<in> permutations_of_set V" "index \<sigma>' v = t" "[x <- \<sigma>'. x \<noteq> v] = [x <- \<sigma>. x \<noteq> v]"
proof
  from assms show perm: "\<sigma>[v \<mapsto> t] \<in> permutations_of_set V"
    by (auto intro!: permutations_of_setI dest: permutations_of_setD simp: move_to_set_eq move_to_distinct)

  from assms show "index \<sigma>[v \<mapsto> t] v = t"
    by (auto intro: move_to_index_v distinct_filter dest: permutations_of_setD)

  from assms perm show "[x <- \<sigma>[v \<mapsto> t]. x \<noteq> v] = [x <- \<sigma>. x \<noteq> v]"
    unfolding move_to_def
    by (simp add: filter_take_filter filter_drop_filter)
qed

lemma permutations_but_v_bij_betw:
  assumes "\<sigma> \<in> permutations_of_set V"
  assumes "v \<in> V"
  shows "bij_betw (\<lambda>\<sigma>'. index \<sigma>' v) {\<sigma>' \<in> permutations_of_set V. [x <- \<sigma>'. x \<noteq> v] = [x <- \<sigma>. x \<noteq> v]} {..<length \<sigma>}" (is "bij_betw ?f ?L ?R")
  unfolding bij_betw_def
proof
  show "inj_on ?f ?L"
    apply (auto intro!: inj_onI)
    apply (smt (verit, del_insts) assms(2) distinct_count_in_set filter_cong mem_Collect_eq move_to_def move_to_id permutations_of_setD(1) permutations_of_setD(2))
    done
next
  from assms show "?f ` ?L = ?R"
    apply (auto)
     apply (metis index_less_size_conv length_finite_permutations_of_set permutations_of_setD(1))
  proof -
    fix x
    assume "x < length \<sigma>"
    with assms obtain \<sigma>' where "\<sigma>' \<in> permutations_of_set V" "index \<sigma>' v = x" "[x <- \<sigma>'. x \<noteq> v] = [x <- \<sigma>. x \<noteq> v]"
      by (auto elim: permutation_vertex_at_tE)

    then show "x \<in> (\<lambda>\<sigma>'. index \<sigma>' v) ` {\<sigma>' \<in> permutations_of_set V. filter (\<lambda>x. x \<noteq> v) \<sigma>' = filter (\<lambda>x. x \<noteq> v) \<sigma>}"
      by blast
  qed
qed

lemma permutations_but_v_card:
  assumes "\<sigma> \<in> permutations_of_set V"
  assumes "v \<in> V"
  shows "card {\<sigma>' \<in> permutations_of_set V. [x <- \<sigma>'. x \<noteq> v] = [x <- \<sigma>. x \<noteq> v]} = card V"
  using assms length_finite_permutations_of_set[OF assms(1)]
  by (auto dest!: permutations_but_v_bij_betw dest: bij_betw_same_card)

lemma matched_indices_set_eq:
  assumes "bipartite M U (set xs)"
  assumes "distinct xs"
  assumes "matching M"
  shows "{..<length xs} \<inter> {t. xs ! t \<in> Vs M} = (index xs) ` \<Union> (((\<inter>) (set xs)) ` M)"
  using assms
  by (auto elim: distinct_indexE intro!: rev_image_eqI simp: Vs_def)

text \<open>
  Another aspect that was not dealt with in~\cite{birnbaum2008} is the fact that the probability
  spaces over all permutations of the offline side changes when removing vertices.
  In the formal proof we can complete the argument by relating the sizes of two sets of
  permutations:
  \<^enum> permutations over the original set of offline vertices \<^term>\<open>V::'a set\<close>
  \<^enum> permutations over the set of remaining offline vertices \<^term>\<open>X \<subseteq> V\<close> in the reduced instance
    with a perfect matching

We want to show that for each permutation \<^term>\<open>\<sigma>' \<in> permutations_of_set X\<close>, there are
  \<^term>\<open>(card V choose card X) * fact (card V - card X) = fact (card V) / fact (card X)\<close>
  permutations \<^term>\<open>\<sigma> \<in> permutations_of_set V\<close>, s.t.\ \<^term>\<open>\<sigma>::'a list\<close> respects the order
  of \<^term>\<open>\<sigma>'::'a list\<close> on the vertices in \<^term>\<open>X::'a set\<close>.

  The intuition behind this number follows from the fact that when the order of the vertices of
  \<^term>\<open>X::'a set\<close> is fixed by \<^term>\<open>\<sigma>'::'a list\<close>, then we can only choose the \<^term>\<open>card X\<close> indices
  for them in \<^term>\<open>\<sigma>::'a list\<close>. The remaining vertices in \<^term>\<open>V - X::'a set\<close> can be ordered
  arbitrarily in \<^term>\<open>\<sigma>::'a list\<close>.

  The proof of this equicardinality is performed by explicitly stating a bijection between
  the set of such \<^term>\<open>\<sigma> \<in> permutations_of_set V\<close> for fixed \<^term>\<open>X::'a set\<close> and
  \<^term>\<open>\<sigma>' \<in> permutations_of_set X\<close>, and the set in the left-hand-side of the following lemma.
\<close>
lemma card_perms_components:
  assumes "finite V" "X \<subseteq> V"
  shows "card {(xs, vs). xs \<subseteq> {0..<card V} \<and> card xs = card X \<and> vs \<in> permutations_of_set (V - X)} = (card V choose card X) * fact (card V - card X)" (is "card ?L = ?R")
proof -
  have "?L = {xs. xs \<subseteq> {0..<card V} \<and> card xs = card X} \<times> permutations_of_set (V-X)"
    by blast

  with assms show ?thesis
    by (auto simp: card_Diff_subset[OF finite_subset] n_subsets)
qed

fun decr :: "nat \<Rightarrow> nat" where
  "decr 0 = 0"
| "decr (Suc n) = n"

lemma decr_leq: "decr n \<le> n"
  by (cases n) auto

lemma decr_le: "n \<noteq> 0 \<Longrightarrow> decr n < n"
  by (cases n) auto

lemma decr_mono: "n \<le> b \<Longrightarrow> decr n \<le> b"
  using decr_leq dual_order.trans by blast

lemma decr_strict_mono: "n < b \<Longrightarrow> decr n < b"
  using decr_leq order_le_less_trans by auto

lemma decr_Suc: "x \<noteq> 0 \<Longrightarrow> Suc (decr x) = x"
  by (cases x) auto

lemma decr_bij_betw: "\<forall>x \<in> X. x \<noteq> 0 \<Longrightarrow> bij_betw decr X (decr ` X)"
  by (rule bij_betwI[where g = Suc]) (auto simp: decr_Suc)

text \<open>
  \<^term>\<open>rebuild\<close> takes a sorted list of indices \<^term>\<open>ns::'a list\<close> (obtained by ordering a finite set), a
  permutation \<^term>\<open>\<sigma>' \<in> permutations_of_set X\<close>, and a permutation \<^term>\<open>\<sigma>'' \<in> permutations_of_set (V - X)\<close>,
  and rebuilds a permutation \<^term>\<open>\<sigma> \<in> permutations_of_set V\<close>, that respects both the orders
  of \<^term>\<open>\<sigma>'\<close> and \<^term>\<open>\<sigma>''\<close>, while also putting the vertices of \<^term>\<open>\<sigma>'\<close> at indices \<^term>\<open>ns::'a list\<close>.

  It serves as the inverse function for mapping a permutation \<^term>\<open>\<sigma> \<in> permutations_of_set V\<close>
  to a pair \<^term>\<open>(index \<sigma> ` X, [v <- \<sigma>. v \<notin> X])\<close>. To show that these two functions are bijective
  between the two sets in question involves some lengthy inductions, but is not necessarily hard.
\<close>
fun rebuild :: "nat list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "rebuild [] [] xs = xs"
| "rebuild (0#ns) (v#\<sigma>') xs = v # rebuild (map decr ns) \<sigma>' xs"
| "rebuild (Suc n#ns) \<sigma>' (x#xs) = x # rebuild (map decr (Suc n#ns)) \<sigma>' xs"
| "rebuild ns \<sigma>' xs = \<sigma>' @ xs"

lemma set_rebuild_subset:
  shows "set (rebuild ns \<sigma>' xs) \<subseteq> set xs \<union> set \<sigma>'"
  by (induction ns \<sigma>' xs rule: rebuild.induct) auto

lemma set_rebuild_subset':
  "v \<in> set (rebuild ns \<sigma>' xs) \<Longrightarrow> v \<in> set xs \<union> set \<sigma>'"
  using set_rebuild_subset by fast

lemma distinct_rebuild:
  assumes "set xs \<inter> set \<sigma>' = {}"
  assumes "distinct \<sigma>'"
  assumes "distinct xs"
  shows "distinct (rebuild ns xs \<sigma>')"
  using assms set_rebuild_subset
  by (induction ns xs \<sigma>' rule: rebuild.induct) force+

lemma decr_gt_if: "0 < n \<Longrightarrow> n < Suc k \<Longrightarrow> decr n < k"
  by (cases n) auto

lemma map_decr_gt: "\<forall>n \<in> set ns. 0 < n \<and> n < Suc k \<Longrightarrow> \<forall>n \<in> set (map decr ns). n < k"
  by (induction ns) (auto dest: decr_gt_if)

lemma map_decr_sorted_wrt: "\<forall>n \<in> set ns. 0 < n \<Longrightarrow> sorted_wrt (<) ns \<Longrightarrow> sorted_wrt (<) (map decr ns)"
  using gr0_conv_Suc
  by (induction ns) fastforce+

lemma set_rebuild:
  assumes "length ns = length \<sigma>'"
  assumes "\<forall>n \<in> set ns. n < length \<sigma>' + length xs"
  assumes "sorted_wrt (<) ns"
  shows "set (rebuild ns \<sigma>' xs) = set xs \<union> set \<sigma>'"
  using assms
proof (induction ns \<sigma>' xs rule: rebuild.induct)
  case (2 ns v \<sigma>' xs)
  then have "\<forall>n\<in>set (map decr ns). n < length \<sigma>' + length xs"
    by (intro map_decr_gt) simp

  with 2 have "set (rebuild (map decr ns) \<sigma>' xs) = set xs \<union> set \<sigma>'"
    by (auto intro: "2.IH" map_decr_sorted_wrt)

  then show ?case
    by simp
next
  case (3 n ns \<sigma>' x xs)
  then have "\<forall>n\<in>set (map decr (Suc n # ns)). n < length \<sigma>' + length xs"
    by (intro map_decr_gt) auto

  with 3 have "set (rebuild (map decr (Suc n # ns)) \<sigma>' xs) = set xs \<union> set \<sigma>'"
  proof (intro "3.IH", goal_cases)
    case 3
    then show ?case
      by (intro map_decr_sorted_wrt) auto
  qed simp

  then show ?case
    by simp
qed auto

lemma set_rebuild_cong:
  assumes "length ns = length \<sigma>'"
  assumes "\<forall>n \<in> set ns. n < length \<sigma>' + length xs"
  assumes "sorted_wrt (<) ns"
  assumes "set xs \<union> set \<sigma>' = V"
  shows "set (rebuild ns \<sigma>' xs) = V"
  using assms
  by (auto dest: set_rebuild)

lemma rebuild_filter_left:
  assumes "sorted_wrt (<) ns"
  assumes "length ns = length \<sigma>'"
  assumes "\<forall>n \<in> set ns. n < length \<sigma>' + length xs"
  assumes "set xs \<inter> X = {}"
  assumes "set \<sigma>' \<subseteq> X"
  \<comment> \<open>The following two assumptions are not strictly necessary but make the proof easier.\<close>
  assumes "distinct \<sigma>'"
  assumes "distinct xs"
  shows "[v <- rebuild ns \<sigma>' xs. v \<in> X] = \<sigma>'"
  using assms
proof (intro distinct_same_order_list_eq, goal_cases)
  case 1
  then show ?case
    by (auto intro!: distinct_filter intro: distinct_rebuild)
next
  case 2
  then show ?case
    by blast
next
  case 3
  then show ?case
    by (simp only: filter_set[symmetric] set_rebuild) auto
next
  case 4
  then show ?case
  proof (induction ns \<sigma>' xs rule: rebuild.induct)
    case (1 xs)
    then have "filter (\<lambda>v. v \<in> X) (rebuild [] [] xs) = []"
      by (auto intro: filter_False)
    then show ?case
      by simp
  next
    case (2 ns v \<sigma>' xs)

    have IH: "\<forall>x y. (index (filter (\<lambda>v. v \<in> X) (rebuild (map decr ns) \<sigma>' xs)) x \<le> index (filter (\<lambda>v. v \<in> X) (rebuild (map decr ns) \<sigma>' xs)) y) = (index \<sigma>' x \<le> index \<sigma>' y)"
    proof (intro "2.IH", goal_cases)
      case 1
      from \<open>sorted_wrt (<) (0 # ns)\<close> show ?case
        by (auto intro: map_decr_sorted_wrt)
    next
      case 3
      from \<open>\<forall>n\<in>set (0 # ns). n < length (v # \<sigma>') + length xs\<close> \<open>sorted_wrt (<) (0 # ns)\<close>
      show ?case
        by (intro map_decr_gt) simp
    qed (use "2.prems" in auto)

    from \<open>set (v # \<sigma>') \<subseteq> X\<close> have filter_cons: "filter (\<lambda>v. v \<in> X) (rebuild (0 # ns) (v # \<sigma>') xs) = v # filter (\<lambda>v. v \<in> X) (rebuild (map decr ns) \<sigma>' xs)"
      by simp

    show ?case
      by (simp only: filter_cons) (auto simp: IH)
  next
    case (3 n ns \<sigma>' x xs)

    have IH: "\<forall>x y. (index (filter (\<lambda>v. v \<in> X) (rebuild (map decr (Suc n # ns)) \<sigma>' xs)) x \<le> index (filter (\<lambda>v. v \<in> X) (rebuild (map decr (Suc n # ns)) \<sigma>' xs)) y) = (index \<sigma>' x \<le> index \<sigma>' y)"
    proof (intro "3.IH", goal_cases)
      case 1
      from \<open>sorted_wrt (<) (Suc n # ns)\<close> show ?case
        by (intro map_decr_sorted_wrt) fastforce+
    next
      case 3
      from \<open>\<forall>n\<in>set (Suc n # ns). n < length \<sigma>' + length (x # xs)\<close> \<open>sorted_wrt (<) (Suc n # ns)\<close>
      show ?case
        by (intro map_decr_gt) fastforce
    qed (use "3.prems" in auto)

    from \<open>set (x # xs) \<inter> X = {}\<close> have filter_cons: "filter (\<lambda>v. v \<in> X) (rebuild (Suc n # ns) \<sigma>' (x # xs)) = filter (\<lambda>v. v \<in> X) (rebuild (map decr (Suc n # ns)) \<sigma>' xs)"
      by simp

    with IH show ?case
      by force
  next
    case ("4_1" n ns \<sigma>')
    then have "filter (\<lambda>v. v \<in> X) (rebuild (Suc n # ns) \<sigma>' []) = \<sigma>'"
      by (auto intro: filter_True)
    then show ?case
      by simp
  next
    case ("4_4" v \<sigma>' xs)
    then have "filter (\<lambda>v. v \<in> X) (rebuild [] (v # \<sigma>') xs) = v # \<sigma>'"
      by (auto intro: filter_True)
    then show ?case
      by simp
  next
    case ("4_5" n ns v \<sigma>')
    then have "filter (\<lambda>v. v \<in> X) (rebuild (Suc n # ns) (v # \<sigma>') []) = v # \<sigma>'"
      by (auto intro: filter_True)
    then show ?case
      by simp
  qed auto
qed

lemma rebuild_filter_right:
  assumes "set \<sigma>' \<subseteq> X"
  assumes "set xs \<inter> X = {}"
  shows "[v <- rebuild ns \<sigma>' xs. v \<notin> X] = xs"
  using assms
  by (induction ns \<sigma>' xs rule: rebuild.induct)
     (auto intro: filter_True filter_False simp add: disjoint_iff subsetD)

lemma filter_permutation_subset: "\<sigma> \<in> permutations_of_set V \<Longrightarrow> X \<subseteq> V \<Longrightarrow> [v <- \<sigma>. v \<in> X] \<in> permutations_of_set X"
  by (rule permutations_of_setI) (auto dest: permutations_of_setD)

lemma filter_permutation_subset_cong: "\<sigma> \<in> permutations_of_set V \<Longrightarrow> X \<subseteq> V \<Longrightarrow> \<sigma>' = [v <- \<sigma>. v \<in> X] \<Longrightarrow> \<sigma>' \<in> permutations_of_set X"
  by (auto intro: filter_permutation_subset)

lemma decr_index_index_tl: "hd \<sigma> \<notin> set \<sigma>' \<Longrightarrow> x \<in> set \<sigma>' \<Longrightarrow> decr (index \<sigma> x) = index (tl \<sigma>) x"
  by (induction \<sigma>) (auto)

lemma map_index_tl_map_decr_0:
  assumes "distinct (v#\<sigma>s)"
  assumes "subseq (v'#\<sigma>'s) (v#\<sigma>s)"
  assumes "map (index \<sigma>) (v'#\<sigma>'s) = (0::nat) # ns"
  assumes "\<sigma> = v # \<sigma>s"
  shows "map decr ns = map (index \<sigma>s) \<sigma>'s"
  using assms
  by (auto split: if_splits simp flip: subseq_singleton_left)

lemma map_index_tl_map_decr_Suc_Cons:
  assumes "distinct (v#\<sigma>)"
  assumes "subseq \<sigma>' (v#\<sigma>)"
  assumes "Suc n # ns = map (index (v#\<sigma>)) \<sigma>'"
  shows "map decr (Suc n # ns) = map (index \<sigma>) \<sigma>'"
  using assms
  by (auto split: if_splits)
     (meson subseq_Cons' subseq_order.dual_order.trans subseq_singleton_left)

lemma map_index_tl_map_decr_Suc:
  assumes "distinct \<sigma>"
  assumes "subseq \<sigma>' \<sigma>"
  assumes "Suc n # ns = map (index \<sigma>) \<sigma>'"
  shows "map decr (Suc n # ns) = map (index (tl \<sigma>)) \<sigma>'"
  using assms
proof (cases \<sigma>)
  case Nil
  with assms show ?thesis by force
next
  case (Cons a list)
  show ?thesis
    by (simp only: Cons, intro map_index_tl_map_decr_Suc_Cons)
       (use assms Cons in force)+
qed

lemma map_decr_map_index_map_index_tl:
  assumes "hd \<sigma> \<notin> set \<sigma>'"
  shows "map decr (map (index \<sigma>) \<sigma>') = map (index (tl \<sigma>)) \<sigma>'"
  using assms
  by (auto simp: decr_index_index_tl)

lemma sorted_list_of_set_is_map_index:
  assumes "distinct \<sigma>"
  assumes "subseq \<sigma>' \<sigma>"
  assumes "\<sigma>' \<in> permutations_of_set X"
  shows "sorted_list_of_set (index \<sigma> ` X) = map (index \<sigma>) \<sigma>'"
proof -
  consider (inf) "infinite X" | (empty) "X = {}" | (fin_nonempty) "finite X \<and> X \<noteq> {}" by blast
  then show ?thesis
  proof cases
    case inf
    with assms have False
      by (auto dest: permutations_of_set_infinite)
    then show ?thesis by blast
  next
    case empty
    with assms show ?thesis
      by simp
  next
    case fin_nonempty
    with assms show ?thesis
    proof (induction \<sigma>' arbitrary: X)
      case Nil
      then show ?case
        by (auto dest: permutations_of_setD)
    next
      case (Cons v \<sigma>')

      consider (single) "X - {v} = {}" | (ind) "X - {v} \<noteq> {}" by blast
      then show ?case
      proof cases
        case single
        with Cons.prems have "X = {v}" by blast
        with Cons.prems have "\<sigma>' = []"
          by (auto dest: permutations_of_setD)

        with \<open>X = {v}\<close> show ?thesis
          by simp
      next
        case ind

        with Cons.prems have fin': "finite' (X - {v})"
          by blast

        from Cons.prems have "subseq \<sigma>' \<sigma>"
          by (auto intro: subseq_Cons')
      
        have perm: "\<sigma>' \<in> permutations_of_set (X - {v})"
        proof (intro permutations_of_setI equalityI subsetI DiffI, goal_cases)
          case (1 x)
          with Cons show ?case
            by (auto dest: permutations_of_setD)
        next
          case (2 x)
          with Cons show ?case
            by (auto dest: permutations_of_setD)
        next
          case (3 x)
          with Cons show ?case
            by (auto dest: permutations_of_setD)
        next
          case 4
          with Cons show ?case
            by (auto dest: permutations_of_setD)
        qed
  
        from Cons.prems have sorted_Cons: "sorted_list_of_set (index \<sigma> ` X) = index \<sigma> v # sorted_list_of_set ((index \<sigma>) ` (X - {v}))"
        proof (intro sorted_list_of_set_image_Cons, goal_cases)
          case 3
          show ?case
          proof (rule ccontr, simp)
            assume "\<exists>x\<in>X. \<not> index \<sigma> v \<le> index \<sigma> x"

            then obtain x where x: "x \<in> X" "index \<sigma> x < index \<sigma> v"
              by force

            then have v_not_in_take: "v \<notin> set (take (Suc (index \<sigma> x)) \<sigma>)"
              by (simp add: index_take)

            have "subseq (v#\<sigma>') (drop (Suc (index \<sigma> x)) \<sigma>)"
            proof (rule list_emb_drop_before_first[where ys = "take (Suc (index \<sigma> x)) \<sigma>"], goal_cases)
              case 1
              from \<open>subseq (v#\<sigma>') \<sigma>\<close> show ?case
                by simp
            next
              case 2
              from v_not_in_take show ?case
                by auto
            qed

            with x \<open>v#\<sigma>' \<in> permutations_of_set X\<close> have after_v: "x \<in> set (drop (Suc (index \<sigma> x)) \<sigma>)"
              by (metis permutations_of_setD(1) subseq_order.dual_order.trans subseq_singleton_left)

            from x \<open>distinct \<sigma>\<close> have "x \<notin> set (drop (Suc (index \<sigma> x)) \<sigma>)"
              by (intro set_drop_if_index) blast+

            with after_v show False
              by blast
          qed
        next
          case 5
          then show ?case
            by (auto dest: permutations_of_setD elim!: list_emb_set intro!: inj_on_index2)
        qed (use Cons in \<open>auto dest: permutations_of_setD\<close>)

        with Cons.IH[OF \<open>distinct \<sigma>\<close> \<open>subseq \<sigma>' \<sigma>\<close> perm fin'] Cons.prems show ?thesis
          by (simp add: sorted_Cons)
      qed
    qed
  qed
qed

lemma rebuild_rebuilds:
  assumes "finite V"
  assumes "X \<subseteq> V"
  assumes "\<sigma> \<in> permutations_of_set V"
  assumes "\<sigma>' = filter (\<lambda>v. v \<in> X) \<sigma>"
  assumes "xs = filter (\<lambda>v. v \<notin> X) \<sigma>"
  shows "rebuild (map (index \<sigma>) \<sigma>') \<sigma>' xs = \<sigma>"
  using assms
proof (induction "map (index \<sigma>) \<sigma>'" \<sigma>' xs arbitrary: \<sigma> X V rule: rebuild.induct)
  case (1 xs)
  then show ?case
    by (auto intro: filter_True simp: empty_filter_conv)
next
  case (2 ns v' \<sigma>' xs)

  then have perm': "v' # \<sigma>' \<in> permutations_of_set X"
    by (auto intro: filter_permutation_subset_cong)

  from 2 have v'_hd: "index \<sigma> v' = 0"
    by force

  with \<open>v' # \<sigma>' = filter (\<lambda>v. v \<in> X) \<sigma>\<close> have \<sigma>_tl: "\<sigma> = v' # tl \<sigma>"
    by (metis filter.simps(1) index_Cons index_eq_index_conv list.exhaust_sel list.set_intros(1) list.simps(3))

  then have \<sigma>_nonempty: "\<sigma> \<noteq> []" by blast

  from 2 \<sigma>_tl have map_decr_ns_map_index_tl: "map decr ns = map (index (tl \<sigma>)) \<sigma>'"
  proof (intro map_index_tl_map_decr_0[where v=v' and v'=v' and \<sigma>=\<sigma>], goal_cases)
    case 1
    then show ?case
      by (auto dest: permutations_of_setD)
  next
    case 2
    then show ?case
      by (metis subseq_filter_left)
  next
    case 3
    then show ?case
      by argo
  next
    case 4
    then show ?case
      by blast
  qed

  have rebuild_tl: "rebuild (map (index (tl \<sigma>)) \<sigma>') \<sigma>' xs = tl \<sigma>"
  proof (rule "2.hyps"(1)[OF map_decr_ns_map_index_tl, where V = "V - {v'}" and X = "X - {v'}"], goal_cases)
    case 1
    from \<open>finite V\<close> show ?case by blast
  next
    case 2
    from \<open>X \<subseteq> V\<close> show ?case by blast
  next
    case 3
    then show ?case
    proof (intro permutations_of_setI equalityI subsetI DiffI, goal_cases)
      case (1 x)
      with \<open>\<sigma> \<in> permutations_of_set V\<close> \<sigma>_nonempty show ?case
        by (auto dest: list.set_sel permutations_of_setD)
    next
      case (2 x)
      with \<sigma>_tl \<open>\<sigma> \<in> permutations_of_set V\<close> show ?case
        by (metis distinct.simps(2) permutations_of_setD(2) singletonD)
    next
      case (3 x)
      with \<open>\<sigma> \<in> permutations_of_set V\<close> \<sigma>_tl show ?case
        by (metis Diff_iff insertI1 permutations_of_setD(1) set_ConsD)
    next
      case 4
      with \<open>\<sigma> \<in> permutations_of_set V\<close> show ?case
        by (auto dest: distinct_tl permutations_of_setD)
    qed
  next
    case 4
    from perm' show ?case
      by (intro filter_tl_without_hd)
         (auto dest: permutations_of_setD intro: \<open>v' # \<sigma>' = filter (\<lambda>v. v \<in> X) \<sigma>\<close>)
  next
    case 5
    show ?case
    proof -
      from perm' have "filter (\<lambda>v. v \<notin> X) \<sigma> = filter (\<lambda>v. v \<notin> X) (tl \<sigma>)"
        by (subst \<sigma>_tl) (auto dest: permutations_of_setD)

      also from \<open>\<sigma> \<in> permutations_of_set V\<close> have "\<dots> = filter (\<lambda>v. v \<notin> X - {v'}) (tl \<sigma>)"
        by (intro filter_cong, blast)
           (subst (asm) \<sigma>_tl, auto dest: permutations_of_setD)

      finally have "filter (\<lambda>v. v \<notin> X) \<sigma> = filter (\<lambda>v. v \<notin> X - {v'}) (tl \<sigma>)" .

      with \<open>xs = filter (\<lambda>v. v \<notin> X) \<sigma>\<close> show ?thesis by blast
    qed
  qed

  note map_map[simp del]
  from \<open>v' # \<sigma>' \<in> permutations_of_set X\<close> have "hd \<sigma> \<notin> set \<sigma>'"
    by (subst \<sigma>_tl) (auto dest!: permutations_of_setD)

  then show ?case
    by (simp add: v'_hd map_decr_map_index_map_index_tl rebuild_tl, subst (2) \<sigma>_tl) blast
next
  case (3 n ns \<sigma>' x xs)

  then have "x \<notin> X"
    by (auto dest: Cons_eq_filterD)

  from 3 have \<sigma>_tl: "\<sigma> = x # tl \<sigma>"
    by (smt (verit, ccfv_SIG) Cons_eq_map_D filter.simps(1) filter.simps(2) index_Cons list.collapse list.inject nat.simps(3))

  then have \<sigma>_nonempty: "\<sigma> \<noteq> []" by blast

  have map_decr_nns_map_index_tl: "map decr (Suc n # ns) = map (index (tl \<sigma>)) \<sigma>'"
  proof (intro map_index_tl_map_decr_Suc, goal_cases)
    case 1
    from \<open>\<sigma> \<in> permutations_of_set V\<close> show ?case
      by (auto dest: permutations_of_setD)
  next
    case 2
    from \<open>\<sigma>' = filter (\<lambda>v. v \<in> X) \<sigma>\<close> subseq_filter_left show ?case
      by blast
  next
    case 3
    from \<open>Suc n # ns = map (index \<sigma>) \<sigma>'\<close> show ?case by blast
  qed

  have rebuild_tl: "rebuild (map (index (tl \<sigma>)) \<sigma>') \<sigma>' xs = tl \<sigma>"
  proof (rule "3.hyps"(1)[OF map_decr_nns_map_index_tl, where V = "V - {x}" and X = X], goal_cases)
    case 1
    from \<open>finite V\<close> show ?case by blast
  next
    case 2
    from \<open>X \<subseteq> V\<close> \<open>x \<notin> X\<close> show ?case by blast
  next
    case 3
    show ?case
    proof (intro permutations_of_setI equalityI subsetI DiffI, goal_cases)
      case (1 y)
      with \<sigma>_nonempty \<open>\<sigma> \<in> permutations_of_set V\<close> show ?case
        by (auto dest: permutations_of_setD list.set_sel)
    next
      case (2 y)
      with \<sigma>_tl \<open>\<sigma> \<in> permutations_of_set V\<close> show ?case
        by (metis distinct.simps(2) permutations_of_setD(2) singletonD)
    next
      case (3 y)
      with \<sigma>_tl \<open>\<sigma> \<in> permutations_of_set V\<close> show ?case
        by (metis DiffD1 DiffD2 insertI1 permutations_of_setD(1) set_ConsD)
    next
      case 4
      from \<open>\<sigma> \<in> permutations_of_set V\<close> show ?case
        by (auto dest: permutations_of_setD distinct_tl)
    qed
  next
    case 4
    from \<sigma>_tl \<open>x \<notin> X\<close> \<open>\<sigma>' = filter (\<lambda>v. v \<in> X) \<sigma>\<close> show ?case
      by (metis filter.simps(2))
  next
    case 5
    from \<sigma>_tl \<open>x \<notin> X\<close> \<open>x # xs = filter (\<lambda>v. v \<notin> X) \<sigma>\<close> show ?case
      by (metis filter.simps(2) list.inject)
  qed

  note list.map[simp del]
  show ?case
    by (simp flip: \<open>Suc n # ns = map (index \<sigma>) \<sigma>'\<close> add: map_decr_nns_map_index_tl, subst \<sigma>_tl, simp add: rebuild_tl)
next
  case ("4_1" n ns \<sigma>')
  then show ?case
    by (metis append.right_neutral filter_True filter_empty_conv rebuild.simps(4))
next
  case ("4_2" ns xs)
  then show ?case
    by blast
next
  case ("4_3" n ns)
  then show ?case
    by blast
next
  case ("4_4" v \<sigma>' xs)
  then show ?case
    by blast
next
  case ("4_5" n ns v \<sigma>')
  then show ?case
    by (metis append.right_neutral filter_True filter_empty_conv rebuild.simps(4))
qed

lemma rebuild_indices:
  assumes "sorted_wrt (<) ns"
  assumes "length ns = length \<sigma>'"
  assumes "\<forall>n \<in> set ns. n < length \<sigma>' + length xs"
  assumes "set xs \<inter> X = {}"
  assumes "set \<sigma>' = X"
  assumes "distinct \<sigma>'"
  shows "index (rebuild ns \<sigma>' xs) ` X = set ns"
  using assms
proof (induction ns \<sigma>' xs arbitrary: X rule: rebuild.induct)
  case (1 xs)
  then show ?case
    by simp
next
  case (2 ns v \<sigma>' xs)

  have IH: "index (rebuild (map decr ns) \<sigma>' xs) ` (X - {v}) = set (map decr ns)"
  proof (intro "2.IH", goal_cases)
    case 1
    from \<open>sorted_wrt (<) (0#ns)\<close> show ?case
      by (auto intro: map_decr_sorted_wrt)
  next
    case 2
    from \<open>length (0#ns) = length (v#\<sigma>')\<close> show ?case by simp
  next
    case 3
    from \<open>\<forall>n \<in> set (0#ns). n < length (v#\<sigma>') + length xs\<close> \<open>sorted_wrt (<) (0 # ns)\<close> show ?case
      by (intro map_decr_gt) auto
  next
    case 4
    from \<open>set xs \<inter> X = {}\<close> show ?case by blast
  next
    case 5
    from \<open>set (v#\<sigma>') = X\<close> \<open>distinct (v#\<sigma>')\<close> show ?case by force
  next
    case 6
    from \<open>distinct (v#\<sigma>')\<close> show ?case by simp
  qed

  from \<open>set (v#\<sigma>') = X\<close> have X_In_v: "X \<inter> {v} = {v}" by fastforce

  have "index (rebuild (0 # ns) (v # \<sigma>') xs) ` X = insert 0 (Suc ` (index (rebuild (map decr ns) \<sigma>' xs) ` (X - {v})))"
    by (auto simp add: X_In_v)

  also have "\<dots> = insert 0 (Suc ` set (map decr ns))"
    by (simp add: IH)

  also have "\<dots> = insert 0 (set ns)"
    using \<open>sorted_wrt (<) (0 # ns)\<close>
    by (auto simp: decr_Suc) (use decr.elims in blast)

  finally show ?case
    by simp
next
  case (3 n ns \<sigma>' x xs)

  have IH: "index (rebuild (map decr (Suc n # ns)) \<sigma>' xs) ` X = set (map decr (Suc n # ns))"
  proof (intro "3.IH", goal_cases)
    case 1
    from \<open>sorted_wrt (<) (Suc n # ns)\<close> show ?case
      by (intro map_decr_sorted_wrt) auto
  next
    case 3
    from "3.prems" show ?case
      by (intro map_decr_gt) auto
  qed (use "3.prems" in auto)

  from \<open>set (x # xs) \<inter> X = {}\<close> have "x \<notin> X" "X \<inter> {x} = {}" by simp+

  then have "index (rebuild (Suc n # ns) \<sigma>' (x#xs)) ` X = Suc ` (index (rebuild (map decr (Suc n # ns)) \<sigma>' xs) ` X)"
    by auto

  also have "\<dots> = Suc ` (set (map decr (Suc n # ns)))"
    by (simp only: IH)

  finally show ?case
    using \<open>sorted_wrt (<) (Suc n # ns)\<close>
    by (auto simp: decr_Suc)
       (metis Suc_lessE decr.simps(2) image_iff)
next
  case ("4_1" n ns \<sigma>')

  then have "length (Suc n#ns) \<le> last (Suc n#ns)"
    by (intro sorted_strict_last_geq_length) auto

  with "4_1" show ?case
    by (metis add.right_neutral last_in_set leD list.distinct(1) list.size(3))
next
  case ("4_2" ns xs)
  then show ?case
    by auto
next
  case ("4_3" n ns)
  then show ?case
    by simp
next
  case ("4_4" v \<sigma>' xs)
  then show ?case
    by simp
next
  case ("4_5" n ns v \<sigma>')

  then have "length (Suc n#ns) \<le> last (Suc n#ns)"
    by (intro sorted_strict_last_geq_length) auto

  with "4_5" show ?case
    by (metis add.right_neutral last_in_set leD list.distinct(1) list.size(3))
qed

lemma card_restrict_permutation_eq_choose:
  assumes "finite V"
  assumes "X \<subseteq> V"
  assumes "\<sigma>' \<in> permutations_of_set X"
    \<comment> \<open>choose positions of X (the vertices we care about), the remaining vertices have arbitrary order\<close>
  shows "card {\<sigma> \<in> permutations_of_set V. [v <- \<sigma>. v \<in> X] = \<sigma>'} = (card V choose card X) * fact (card V - card X)" (is "?L = ?R")
proof -
  have "?L = card {(xs, vs). xs \<subseteq> {0..<card V} \<and> card xs = card X \<and> vs \<in> permutations_of_set (V - X)}"
  proof (intro bij_betw_same_card[where f = "\<lambda>\<sigma>. (index \<sigma> ` X, [v <- \<sigma>. v \<notin> X])"] 
              bij_betwI[where g = "\<lambda>(xs,vs). rebuild (sorted_list_of_set xs) \<sigma>' vs"], goal_cases)
    case 1    
    with assms show ?case
    proof (auto, goal_cases)
      case (1 \<sigma> x)
      then show ?case
        by (auto simp flip: length_finite_permutations_of_set simp: index_less_size_conv dest: permutations_of_setD)
    next
      case (2 \<sigma>)
      then show ?case
        by (intro card_image)
           (simp add: inj_on_def subset_eq permutations_of_setD)
    next
      case (3 \<sigma>)
      then show ?case
        by (auto intro!: permutations_of_setI dest: permutations_of_setD)
      qed
  next
    case 2
    with assms show ?case
    proof (auto, goal_cases)
      case (1 xs vs)
      then show ?case
      proof (intro permutations_of_setI, goal_cases)
        case 1
        then show ?case
        proof (intro set_rebuild_cong, goal_cases)
          case 1
          then show ?case 
            by (simp add: length_finite_permutations_of_set)
        next
          case 2
          with assms have "length \<sigma>' + length vs = card V"
            by (auto simp: length_finite_permutations_of_set card_Diff_subset[OF finite_subset] card_mono)

          with 2 show ?case
            by (auto simp: subset_eq_atLeast0_lessThan_finite)
        next
          case 3
          then show ?case
            by simp
        next
          case 4
          then show ?case
            by (auto dest: permutations_of_setD)
        qed

      next
        case 2
        then show ?case
          by (auto intro!: distinct_rebuild dest: permutations_of_setD)
      qed
    next
      case (2 xs vs)
      then show ?case
      proof (intro rebuild_filter_left, goal_cases)
        case 3
        then show ?case
          by (auto simp: subset_eq_atLeast0_lessThan_finite length_finite_permutations_of_set card_Diff_subset[OF finite_subset])
      qed (auto dest: permutations_of_setD length_finite_permutations_of_set)
    qed
  next
    case (3 \<sigma>)
    with \<open>\<sigma>' \<in> permutations_of_set X\<close> have "sorted_list_of_set (index \<sigma> ` X) = map (index \<sigma>) \<sigma>'"
      by (auto intro: sorted_list_of_set_is_map_index dest: permutations_of_setD)
    
    with 3 assms show ?case
      by (auto intro: rebuild_rebuilds[where V = V and X = X])
  next
    case (4 y)
    then obtain xs vs where "y = (xs,vs)" "xs \<subseteq> {0..<card V}" "card xs = card X" "vs \<in> permutations_of_set (V - X)"
      by blast

    have "index (rebuild (sorted_list_of_set xs) \<sigma>' vs) ` X = set (sorted_list_of_set xs)"
    proof (intro rebuild_indices, goal_cases)
      case 1
      then show ?case by auto
    next
      case 2
      from \<open>card xs = card X\<close> \<open>\<sigma>' \<in> permutations_of_set X\<close> \<open>finite V\<close> \<open>X \<subseteq> V\<close> show ?case
        by (auto simp: length_finite_permutations_of_set)
    next
      case 3
      from \<open>\<sigma>' \<in> permutations_of_set X\<close> \<open>vs \<in> permutations_of_set (V - X)\<close> \<open>finite V\<close> \<open>X \<subseteq> V\<close>
      have "length \<sigma>' + length vs = card V"
        by (auto simp: length_finite_permutations_of_set card_Diff_subset[OF finite_subset] card_mono)
      
      with \<open>xs \<subseteq> {0..<card V}\<close> show ?case
        by (auto simp: subset_eq_atLeast0_lessThan_finite)
    next
      case 4
      from \<open>vs \<in> permutations_of_set (V - X)\<close> show ?case
        by (auto dest: permutations_of_setD)
    next
      case 5
      from \<open>\<sigma>' \<in> permutations_of_set X\<close> show ?case
        by (auto dest: permutations_of_setD)
    next
      case 6
      from \<open>\<sigma>' \<in> permutations_of_set X\<close> show ?case
        by (auto dest: permutations_of_setD)
    qed

    also have "\<dots> = xs"
      using \<open>xs \<subseteq> {0..<card V}\<close>
      by (auto simp: subset_eq_atLeast0_lessThan_finite)

    finally have indices: "index (rebuild (sorted_list_of_set xs) \<sigma>' vs) ` X = xs" .

    from \<open>\<sigma>' \<in> permutations_of_set X\<close> \<open>vs \<in> permutations_of_set (V - X)\<close>
    have filter: "filter (\<lambda>v. v \<notin> X) (rebuild (sorted_list_of_set xs) \<sigma>' vs) = vs"
      by (auto intro!: rebuild_filter_right dest: permutations_of_setD)

    from \<open>y = (xs,vs)\<close> show ?case
      by (auto simp: indices filter)
  qed

  with assms show ?thesis
    by (simp add: card_perms_components)
qed

text \<open>
  Finally, we get the lemma in the form that allows us to go from a probability space over
  permutations over a subset of the offline vertices, to the one over permutations of our original
  offline vertices.
\<close>
lemma card_restrict_permutation_eq_fact:
  assumes "finite V"
  assumes "X \<subseteq> V"
  assumes "\<sigma>' \<in> permutations_of_set X"
  shows "card {\<sigma> \<in> permutations_of_set V. [v <- \<sigma>. v \<in> X] = \<sigma>'} = fact (card V) / fact (card X)" (is "?L = ?R")
proof -
  from assms have choose_eq: "card V choose card X = fact (card V) / ((fact (card X) * fact (card V - card X)))"
    by (auto intro: binomial_fact card_mono)

  from assms have "?L = (card V choose card X) * fact (card V - card X)"
    by (simp add: card_restrict_permutation_eq_choose)

  also have "\<dots> = fact (card V) / (fact (card X) * fact (card V - card X)) * fact (card V - card X)"
    by (simp add: choose_eq)

  finally show ?thesis
    by simp
qed

subsection \<open>Formulation as Randomized Algorithm\label{sec:prob-wf}\<close>
text \<open>
  We phrase the algorithm in a probabilistic setting alongside some conditions for wellformed
  inputs for the online bipartite matching problem in the following locale.
\<close>
locale wf_ranking =
  fixes G \<pi> V M

  assumes bipartite: "bipartite G (set \<pi>) V"
  assumes finite_graph: "finite G"
  assumes vertices: "Vs G = set \<pi> \<union> V"

  assumes max_card_matching: "max_card_matching G M"
begin

definition "ranking \<equiv>
  do {
    \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
    return_pmf (online_match G \<pi> \<sigma>)
  }"

lemma graph_invar_G[simp]: "graph_invar G"
  using finite_graph bipartite bipartite
  by (auto simp add: finite_bipartite_graph_invar elim!: )


lemma graph_abs_M[simp]: "graph_invar M"
  using max_card_matching
  by (auto intro!: graph_invar_subgraph[OF graph_invar_G] dest: max_card_matchingD)

lemma finite[simp]: "finite V"
  using finite_graph vertices
  by (metis finite_Un graph_invar_G graph_abs_def)

lemma online_match_edgeE:
  assumes "e \<in> online_match G \<pi> \<sigma>"
  obtains u v where "e = {u,v}" "u \<in> set \<pi>" "v \<in> V" "v \<in> set \<sigma>"
  using assms bipartite
  by (smt (verit, best) bipartite_disjointD bipartite_edgeE disjoint_iff_not_equal edges_are_Vs_2
          online_match_Vs_subset subgraph_online_match)

lemma bipartite_matching:
  "bipartite M (set \<pi>) V"
  using bipartite max_card_matching
  by (auto intro: bipartite_subgraph dest: max_card_matchingD)

lemma matching_if_perm: "\<sigma> \<in> permutations_of_set V \<Longrightarrow> matching (online_match G \<pi> \<sigma>)"
  using bipartite
  by (auto intro: matching_online_match dest: permutations_of_setD bipartite_disjointD)

lemma bipartite_if_perm: "\<sigma> \<in> permutations_of_set V \<Longrightarrow> bipartite (online_match G \<pi> \<sigma>) (set \<pi>) (set \<sigma>)"
  using bipartite
  by (auto dest: permutations_of_setD intro: bipartite_online_match)

lemma perms_of_V:
  shows "permutations_of_set V \<noteq> {}"
    and "finite (permutations_of_set V)"
  by (auto simp: finite)

end

text \<open>
  On basis of Lemma 2, we restrict to instances where a perfect matching exists for the analysis
  of the competitive ratio.
\<close>
locale ranking_on_perfect_matching = wf_ranking +
  assumes edge_exists:  "G \<noteq> {}"

  assumes perfect_matching: "perfect_matching G M"
begin

lemma non_empty: "V \<noteq> {}"
  using bipartite bipartite_edgeE edge_exists by blast

lemma non_empty_online[simp]: "\<pi> \<noteq> []"
  using bipartite edge_exists
  by (auto simp: bipartite_empty_part_iff_empty)

lemma offline_subset_vs: "v \<in> V \<Longrightarrow> v \<in> Vs G"
  using vertices by simp

lemma online_subset_vs: "u \<in> set \<pi> \<Longrightarrow> u \<in> Vs G"
  using vertices by simp

lemma the_match_offline_Ex:
  assumes "v \<in> V"
  shows "\<exists>u. {u,v} \<in> M \<and> u \<in> set \<pi>"
proof -
  from assms perfect_matching vertices have "v \<in> Vs M"
    unfolding perfect_matching_def
    by fastforce

  then obtain e where e: "e \<in> M" "v \<in> e"
    unfolding Vs_def by blast

  with assms bipartite_matching \<open>v \<in> Vs M\<close> obtain u where "e = {u,v}" "u \<in> set \<pi>"
    by (auto elim: bipartite_edgeE dest: bipartite_vertex)

  with e show "\<exists>u. {u,v} \<in> M \<and> u \<in> set \<pi>" by blast
qed

lemma the_match_offlineE:
  assumes "v \<in> V"
  obtains u where "{u,v} \<in> M" "u \<in> set \<pi>"
  using assms
  by (auto dest: the_match_offline_Ex)

lemma the_match_online_Ex:
  assumes "u \<in> set \<pi>"
  shows "\<exists>v. {u,v} \<in> M \<and> v \<in> V"
  using assms
proof -
  from assms perfect_matching vertices have "u \<in> Vs M"
    unfolding perfect_matching_def
    by fastforce

  then obtain e where e: "e \<in> M" "u \<in> e"
    unfolding Vs_def by blast

  with assms bipartite_matching \<open>u \<in> set \<pi>\<close> obtain v where "e = {u,v}" "v \<in> V"
    by (auto elim!: bipartite_edgeE dest: bipartite_vertex bipartite_disjointD)

  with e show "\<exists>v. {u,v} \<in> M \<and> v \<in> V" by blast
qed

lemma the_match_onlineE:
  assumes "u \<in> set \<pi>"
  obtains v where "{u,v} \<in> M" "v \<in> V"
  using assms
  by (auto dest: the_match_online_Ex)

lemma the_match_online:
  assumes "u \<in> set \<pi>"
  shows "{u, (THE v. {u,v} \<in> M)} \<in> M"
    and "(THE v. {u, v} \<in> M) \<in> V"
  using perfect_matching assms
  by (auto elim!: the_match_onlineE dest: perfect_matchingD the_match')

lemma the_match_offline:
  assumes "v \<in> V"
  shows "{(THE u. {u,v} \<in> M), v} \<in> M"
    and "(THE u. {u, v} \<in> M) \<in> set \<pi>"
  using perfect_matching assms
  by (auto elim!: the_match_offlineE dest: perfect_matchingD the_match)

lemma perfect_matching_bij:
  "bij_betw (\<lambda>u. (THE v. {u,v} \<in> M)) (set \<pi>) V"
proof (intro bij_betwI[where g = "\<lambda>v. (THE u. {u,v} \<in> M)"] funcsetI, goal_cases)
  case (1 x)
  then show ?case
    by (auto dest: the_match_online)
next
  case (2 x)
  then show ?case
    by (auto dest: the_match_offline)
next
  case (3 x)
  with perfect_matching show ?case
    by (auto dest: the_match_online perfect_matchingD the_match)
next
  case (4 y)
  with perfect_matching show ?case
    by (auto dest: the_match_offline perfect_matchingD the_match')
qed

lemma card_online_eq_offline: "card (set \<pi>) = card V"
  using perfect_matching_bij
  by (auto intro: bij_betw_same_card)

text \<open>
  Lemma 5 in~\cite{birnbaum2008} considers the probability of the offline vertex at
  index \<^term>\<open>t::nat\<close> being matched. It is crucial to make the chosen permutation independent
  of the vertex at that index \<^term>\<open>t::nat\<close>. To that end, the following way of drawing a random
  permutation -- which will be shown to be equivalent to drawing one uniformly at random -- is
  introduced.
\<close>
definition random_permutation_t :: "nat \<Rightarrow> ('a list) pmf" where
  "random_permutation_t t \<equiv> 
    do {
      \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
      v \<leftarrow> pmf_of_set V;
      return_pmf \<sigma>[v \<mapsto> t]
  }"

lemma random_permutation_geq_card:
  "card V \<le> t \<Longrightarrow> random_permutation_t t = random_permutation_t (card V - 1)" (is "?geq \<Longrightarrow> ?L = ?R")
proof (intro pmf_eqI)
  fix i
  assume ?geq

  from finite non_empty have "pmf ?L i = (\<Sum>\<sigma>\<in>permutations_of_set V. (\<Sum>x\<in>V. indicat_real {i} \<sigma>[x \<mapsto> t]) / real (card V)) / fact (card V)"
    unfolding random_permutation_t_def
    by (simp add: pmf_bind_pmf_of_set)

  also from \<open>?geq\<close> finite non_empty have "\<dots> = (\<Sum>\<sigma>\<in>permutations_of_set V. (\<Sum>x\<in>V. indicat_real {i} \<sigma>[x \<mapsto> card V - 1]) / real (card V)) / fact (card V)"
    by (intro arg_cong2[where f =  "(/)"] sum.cong arg_cong2[where f = "indicat_real"])
       (auto simp add: length_finite_permutations_of_set move_elem_to_gt_length permutations_of_setD)

  also from finite non_empty have "\<dots> = pmf ?R i"
    unfolding random_permutation_t_def
    by (simp add: pmf_bind_pmf_of_set)

  finally show "pmf ?L i = pmf ?R i" .
qed

lemma move_to_t_eq_uniform_less: "t < card V \<Longrightarrow> random_permutation_t t = pmf_of_set (permutations_of_set V)"
proof (rule pmf_eqI)
  fix \<sigma> :: "'a list"
  assume "t < card V"
  show "pmf (random_permutation_t t) \<sigma> = pmf (pmf_of_set (permutations_of_set V)) \<sigma>"
  proof (cases "\<sigma> \<in> permutations_of_set V")
    case True

    with \<open>t < card V\<close> have "t < length \<sigma>"
      by (simp add: length_finite_permutations_of_set)

    with True have set_eq: "{\<sigma>' \<in> permutations_of_set V. (card (V \<inter> {v. \<sigma> = \<sigma>'[v \<mapsto> t]})) = Suc 0} = {\<sigma>' \<in> permutations_of_set V. [x <- \<sigma>'. x \<noteq> (THE v. index \<sigma> v = t)] = [x <- \<sigma>. x \<noteq> (THE v. index \<sigma> v = t)]}"
      using permutations_move_to_eq_iff
      by auto

    from True \<open>t < length \<sigma>\<close> finite have "(\<Sum>\<sigma>'\<in>permutations_of_set V. real (card (V \<inter> {v. \<sigma> = \<sigma>'[v \<mapsto> t]}))) = real (card V)"
      by (intro sum_eq_card_where_One)
         (auto intro!: permutations_but_v_card
           intro: index_nth_id simp: set_eq the_index[OF permutations_of_setD(2)] move_to_eq_iff dest: permutations_of_setD)

    with True finite non_empty \<open>t < length \<sigma>\<close> show ?thesis
      by (simp add: random_permutation_t_def pmf_bind_pmf_of_set indicator_singleton sum.If_cases
          flip: sum_divide_distrib)
  next
    case False
    with finite non_empty show ?thesis
      by (auto intro!: sum.neutral dest: permutation_move_to simp: random_permutation_t_def pmf_bind_pmf_of_set indicator_singleton sum.If_cases)
  qed
qed

lemma move_to_t_eq_uniform: "random_permutation_t t = pmf_of_set (permutations_of_set V)"
  by (cases "t < card V")
     (auto simp: random_permutation_geq_card card_gt_0_iff finite non_empty intro: move_to_t_eq_uniform_less)

text \<open>
  The proof of Lemma 5 then goes on to relate the probability of the vertex \<^term>\<open>v\<in>V\<close> of rank \<^term>\<open>t::nat\<close>
  being unmatched to the probability that the online vertex \<^term>\<open>u\<in>set \<pi>\<close> which is matched to
  \<^term>\<open>v\<close> in the perfect matching is matched to a vertex \<^term>\<open>\<sigma>'\<in>V\<close> s.t.\ its rank is at most
  \<^term>\<open>t::nat\<close>. The following \<^typ>\<open>bool pmf\<close>s are used to model this in the
  formalization.
\<close>
abbreviation rank_unmatched :: "nat \<Rightarrow> bool pmf" where
  "rank_unmatched t \<equiv>
    do {
      \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
      let R = online_match G \<pi> \<sigma>;
      return_pmf (\<sigma> ! t \<notin> Vs R)
    }"

abbreviation rank_matched :: "nat \<Rightarrow> bool pmf" where
  "rank_matched t \<equiv>
    do {
      \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
      let R = online_match G \<pi> \<sigma>;
      return_pmf (\<sigma> ! t \<in> Vs R)
    }"

definition matched_before :: "nat \<Rightarrow> bool pmf" where
  "matched_before t \<equiv>
    do {
      \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
      v \<leftarrow> pmf_of_set V;
      let R = online_match G \<pi> \<sigma>; 
      let u = (THE u. {u,v} \<in> M);
      return_pmf (u \<in> Vs R \<and> index \<sigma> (THE v. {u,v} \<in> R) \<le> t)
    }"

lemma rank_matched_False_rank_unmatched_True[simplified]: "measure_pmf.prob (rank_matched t) {False} = measure_pmf.prob (rank_unmatched t) {True}"
  using perms_of_V
  by (simp add: measure_pmf_conv_infsetsum pmf_bind_pmf_of_set indicator_singleton)

lemma rank_matched_prob_is_expectation: "measure_pmf.prob (rank_matched t) {True} = measure_pmf.expectation (rank_matched t) of_bool"
  by (simp add: bernoulli_prob_True_expectation)

lemma perms_where_0th_matched_eq_perms: "permutations_of_set V \<inter> {\<sigma>. \<sigma> ! 0 \<in> Vs (online_match G \<pi> \<sigma>)} = permutations_of_set V"
proof (intro equalityI subsetI IntI CollectI)
  fix \<sigma>
  assume perm: "\<sigma> \<in> permutations_of_set V"
  show "\<sigma> ! 0 \<in> Vs (online_match G \<pi> \<sigma>)"
  proof (intro first_rank_always_matched[where G = G and \<pi> = \<pi> and M = "online_match G \<pi> \<sigma>"] ranking_matching_online_match)
    show "bipartite G (set \<pi>) (set \<sigma>)"
      using bipartite perm
      by (auto dest: permutations_of_setD)
  next
    show "\<sigma> \<noteq> []"
      using perm non_empty
      by (auto dest: permutations_of_setD)
  next
    show "\<sigma> ! 0 \<in> Vs G"
      by (metis card_gt_0_iff length_finite_permutations_of_set finite non_empty nth_mem offline_subset_vs perm permutations_of_setD(1))
  qed
qed blast

lemma first_rank_matched_prob_1: "measure_pmf.prob (rank_matched 0) {True} = 1"
  using perms_of_V
  by (auto simp: measure_pmf_conv_infsetsum pmf_bind_pmf_of_set indicator_singleton sum.If_cases perms_where_0th_matched_eq_perms)

lemma the_t:
  assumes "distinct xs"
  assumes "x \<in> set xs"
  shows "index xs x = (THE t. index xs x = t)"
    and "(THE t. index xs x = t) < length xs"
  using assms
  by (auto dest: theI'[OF distinct_Ex1])

lemma the_t_for_edge:
  assumes "\<sigma> \<in> permutations_of_set V"
  assumes "{u,v} \<in> G"
  assumes "u \<in> set \<pi>" "v \<in> set \<sigma>"
  shows "(THE t. \<exists>v'\<in>set \<sigma>. index \<sigma> v' = t \<and> v' \<in> {u,v}) = index \<sigma> v"
  using assms bipartite
  by (auto dest: permutations_of_setD bipartite_disjointD)

lemma v_unmatched_u_matched_before_Ex:
  assumes perm: "\<sigma> \<in> permutations_of_set V"
  assumes v: "v \<in> V"
  assumes "v \<notin> Vs (online_match G \<pi> \<sigma>[v \<mapsto> t])"
  shows "\<exists>v'. {(THE u. {u,v} \<in> M),v'} \<in> online_match G \<pi> \<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v] \<and> index \<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v] v' \<le> index \<sigma>[v \<mapsto> t] v"
proof (rule v_unmatched_edge_matched_earlier)
  show "(THE u. {u,v} \<in> M) \<in> set \<pi>"
    using v perfect_matching
    by (auto elim: the_match_offlineE dest: perfect_matchingD the_match)
next
  show "v \<in> set \<sigma>[v \<mapsto> t]"
    by (simp add: move_to_set)
next
  show "{THE u. {u,v} \<in> M, v} \<in> G"
    using v perfect_matching
    by (auto elim!: the_match_offlineE dest: perfect_matchingD the_match)
next
  show "v \<notin> Vs (online_match G \<pi> \<sigma>[v \<mapsto> t])"
    using assms by blast
next
  show "ranking_matching G (online_match G \<pi> \<sigma>[v \<mapsto> t]) \<pi> \<sigma>[v \<mapsto> t]"
    using perm v bipartite
    by (auto intro!: ranking_matching_online_match simp: move_to_set insert_absorb dest: permutations_of_setD)
next
  show "ranking_matching G (online_match G \<pi> \<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v]) \<pi> \<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v]"
    using perm v bipartite
    by (auto intro!: ranking_matching_online_match simp: move_to_set insert_absorb dest: permutations_of_setD)
qed

lemma v_unmatched_u_matched_before_the:
  assumes perm: "\<sigma> \<in> permutations_of_set V"
  assumes v: "v \<in> V"
  assumes "\<sigma>[v \<mapsto> t] ! t \<notin> Vs (online_match G \<pi> \<sigma>[v \<mapsto> t])"
  assumes "t < length \<sigma>"
  shows "(THE u. {u, v} \<in> M) \<in> Vs (online_match G \<pi> \<sigma>)"
    and "index \<sigma> (THE v'. {THE u. {u, v} \<in> M, v'} \<in> online_match G \<pi> \<sigma>) \<le> t"
proof -
  let ?u = "THE u. {u,v} \<in> M"
  have "\<sigma>[v \<mapsto> t] ! t = v"
    using assms
    by (auto intro: move_to_index_nth dest: permutations_of_setD)

  with assms obtain v' where v': "{?u, v'} \<in> online_match G \<pi> \<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v]"
    "index \<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v] v' \<le> index \<sigma>[v \<mapsto> t] v"
    by (auto dest: v_unmatched_u_matched_before_Ex)

  from perm v have move_to_move_to: "\<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v] = \<sigma>"
    by (auto intro!: move_to_move_back_id dest: permutations_of_setD)

  with v' show "?u \<in> Vs (online_match G \<pi> \<sigma>)"
    by auto

  from v' perm have the_v': "(THE v'. {?u, v'} \<in> online_match G \<pi> \<sigma>) = v'"
    by (auto intro!: the_match' matching_if_perm simp: move_to_move_to)
  
  from assms have "index \<sigma>[v \<mapsto> t] v = t"
    by (auto intro: move_to_index_v dest: permutations_of_setD)

  with v' show "index \<sigma> (THE v'. {?u,v'} \<in> online_match G \<pi> \<sigma>) \<le> t"
    by (auto simp: the_v' move_to_move_to)
qed

lemma online_match_card_is_sum_of_matched_vertices:
  assumes \<sigma>: "\<sigma> \<in> permutations_of_set V"
  shows "card (online_match G \<pi> \<sigma>) = sum (\<lambda>t. of_bool (\<sigma> ! t \<in> Vs (online_match G \<pi> \<sigma>))) {..<card V}"
proof -
  have card_length: "card V = length \<sigma>"
    using assms
    by (simp add: length_finite_permutations_of_set)

  from \<sigma> have matching: "matching (online_match G \<pi> \<sigma>)"
    by (auto intro: matching_if_perm)

  from \<sigma> have bipartite': "bipartite (online_match G \<pi> \<sigma>) (set \<pi>) (set \<sigma>)"
    by (auto intro: bipartite_if_perm)

  have "card (online_match G \<pi> \<sigma>) = card (index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` online_match G \<pi> \<sigma>))"
  proof (rule bij_betw_same_card[of "\<lambda>e. (THE t. \<exists>v \<in> set \<sigma>. index \<sigma> v = t \<and> v \<in> e)"],
         rule bij_betwI[where g = "\<lambda>t. (THE e. e \<in> online_match G \<pi> \<sigma> \<and> \<sigma> ! t \<in> e)"])
    show "(\<lambda>e. THE t. \<exists>v\<in>set \<sigma>. index \<sigma> v = t \<and> v \<in> e) \<in> online_match G \<pi> \<sigma> \<rightarrow> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` online_match G \<pi> \<sigma>)"
    proof (rule Pi_I)
      fix e
      assume edge: "e \<in> online_match G \<pi> \<sigma>"

      then obtain u v where uv: "e = {u,v}" "u \<in> set \<pi>" "v \<in> set \<sigma>"
        by (auto elim: online_match_edgeE)

      with \<sigma> edge have "(THE t. \<exists>v' \<in> set \<sigma>. index \<sigma> v' = t \<and> v' \<in> e) = index \<sigma> v"
        by (auto intro!: the_t_for_edge[simplified] dest: subgraph_online_match)

      with edge uv show "(THE t. \<exists>v \<in> set \<sigma>. index \<sigma> v = t \<and> v \<in> e) \<in> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` online_match G \<pi> \<sigma>)"
        by (auto intro!: imageI)
    qed
  next
    show "(\<lambda>t. THE e. e \<in> online_match G \<pi> \<sigma> \<and> \<sigma> ! t \<in> e) \<in> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` online_match G \<pi> \<sigma>) \<rightarrow> online_match G \<pi> \<sigma>"
    proof (rule Pi_I)
      fix t
      assume t: "t \<in> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` online_match G \<pi> \<sigma>)"

      then obtain v where v: "index \<sigma> v = t" "v \<in> set \<sigma>" "v \<in> Vs (online_match G \<pi> \<sigma>)"
        by blast

      then obtain e where e: "e \<in> online_match G \<pi> \<sigma>" "v \<in> e"
        by (auto elim: vs_member_elim)

      with assms matching have the_e: "\<And>e'. e' \<in> online_match G \<pi> \<sigma> \<and> v \<in> e' \<Longrightarrow> e' = e"
        by (auto dest: matching_unique_match)

      with e v show "(THE e. e \<in> online_match G \<pi> \<sigma> \<and> \<sigma> ! t \<in> e) \<in> online_match G \<pi> \<sigma>"
        by (metis (no_types, lifting) nth_index theI')
    qed
  next
    show "\<And>e. e \<in> online_match G \<pi> \<sigma> \<Longrightarrow> (THE e'. e' \<in> online_match G \<pi> \<sigma> \<and> \<sigma> ! (THE t. \<exists>v \<in> set \<sigma>. index \<sigma> v = t \<and> v \<in> e) \<in> e') = e"
    proof -
      fix e
      assume e: "e \<in> online_match G \<pi> \<sigma>"

      then obtain u v where uv: "u \<in> set \<pi>" "v \<in> set \<sigma>" "e = {u,v}"
        by (auto elim: online_match_edgeE)

      then obtain t where t: "t = index \<sigma> v"
        by blast

      with uv \<sigma> bipartite have the_t: "(THE t. \<exists>v \<in> set \<sigma>. index \<sigma> v = t \<and> v \<in> e) = t"
        by (auto dest: bipartite_disjointD permutations_of_setD)

      from \<sigma> uv matching \<open>e \<in> online_match G \<pi> \<sigma>\<close> have the_e: "\<And>e'. e' \<in> online_match G \<pi> \<sigma> \<and> v \<in> e' \<Longrightarrow> e' = e"
        by (metis insertCI matching_unique_match)

      with e t \<open>v \<in> set \<sigma>\<close> show "(THE e'. e' \<in> online_match G \<pi> \<sigma> \<and> \<sigma> ! (THE t. \<exists>v \<in> set \<sigma>. index \<sigma> v = t \<and> v \<in> e) \<in> e') = e" 
        by (auto simp: the_t intro!: the_equality)
           (use \<open>e = {u,v}\<close> in blast)
    qed
  next
    show "\<And>t. t \<in> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` online_match G \<pi> \<sigma>) \<Longrightarrow> (THE t'. \<exists>v \<in> set \<sigma>. index \<sigma> v = t' \<and> v \<in> (THE e. e \<in> online_match G \<pi> \<sigma> \<and> \<sigma> ! t \<in> e)) = t"
    proof (rule the_equality)
      fix t
      assume t: "t \<in> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` online_match G \<pi> \<sigma>)"

      with matching show "\<exists>v \<in> set \<sigma>. index \<sigma> v = t \<and> v \<in> (THE e. e \<in> online_match G \<pi> \<sigma> \<and> \<sigma> ! t \<in> e)"
        by (auto simp: the_edge)
    next
      show "\<And>t t'. t \<in> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` online_match G \<pi> \<sigma>) \<Longrightarrow> \<exists>v \<in> set \<sigma>. index \<sigma> v = t' \<and> v \<in> (THE e. e \<in> online_match G \<pi> \<sigma> \<and> \<sigma> ! t \<in> e) \<Longrightarrow> t' = t"
      proof -
        fix t t'
        assume t: "t \<in> index \<sigma> ` \<Union> ((\<inter>) (set \<sigma>) ` online_match G \<pi> \<sigma>)"
          and t': "\<exists>v \<in> set \<sigma>. index \<sigma> v = t' \<and> v \<in> (THE e. e \<in> online_match G \<pi> \<sigma> \<and> \<sigma> ! t \<in> e)"

        with \<sigma> matching bipartite' show "t' = t"
          by (auto simp: the_edge intro: bipartite_eqI)
      qed
    qed
  qed

  with \<sigma> bipartite' matching show ?thesis
    by (auto simp: card_length matched_indices_set_eq dest: permutations_of_setD)
qed

lemma rank_t_unmatched_prob_bound_matched_before:
  "t < card V \<Longrightarrow> measure_pmf.prob (rank_matched t) {False} \<le> measure_pmf.prob (matched_before t) {True}" (is "_ \<Longrightarrow> ?L \<le> ?R")
proof -
  assume "t < card V"
  include monad_normalisation

  have "?L = measure_pmf.prob (rank_unmatched t) {True}"
    by (simp add: rank_matched_False_rank_unmatched_True)

  also have "\<dots> = measure_pmf.prob (
    do {
      \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
      v \<leftarrow> pmf_of_set V;
      let R = online_match G \<pi> \<sigma>[v \<mapsto> t];
      return_pmf (\<sigma>[v \<mapsto> t] ! t \<notin> Vs R)
    }) {True}"
    by (subst move_to_t_eq_uniform[symmetric, of t])
       (simp add: random_permutation_t_def)


  also have "\<dots> \<le> ?R"
    unfolding matched_before_def Let_def
    using perms_of_V finite non_empty
    by (intro bool_pmf_imp_prob_leq2)
       (auto simp: \<open>t < card V\<close> length_finite_permutations_of_set v_unmatched_u_matched_before_the)

  finally show ?thesis .
qed

text \<open>
  Due to the (constructed) independence of the random permutation and the vertex of rank
  \<^term>\<open>t::nat\<close>, we can then consider the probability of a uniformly random online vertex
  \<^term>\<open>u \<in> set \<pi>\<close> being matched to a vertex of rank at most \<^term>\<open>t::nat\<close>.
\<close>
lemma matched_before_uniform_u: "matched_before t = do
    {
      \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
      u \<leftarrow> pmf_of_set (set \<pi>);
      let R = online_match G \<pi> \<sigma>;
      return_pmf (u \<in> Vs R \<and> index \<sigma> (THE v. {u,v} \<in> R) \<le> t)
    }" (is "?L = ?R")
proof (rule pmf_eqI)
  fix i

  from finite non_empty have "pmf ?L i =
  (\<Sum>\<sigma>\<in>permutations_of_set V. real (card (V \<inter> {v'. i = ((THE u. {u, v'} \<in> M) \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {THE u. {u, v'} \<in> M, v} \<in> online_match G \<pi> \<sigma>) \<le> t)})) / real (card V)) / fact (card V)"
    unfolding matched_before_def Let_def
    by (simp add: pmf_bind_pmf_of_set indicator_singleton card_online_eq_offline sum.If_cases)

  also have "\<dots> = (\<Sum>\<sigma>\<in>permutations_of_set V. real (card (set \<pi> \<inter> {u. i = (u \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u, v} \<in> online_match G \<pi> \<sigma>) \<le> t)})) / real (card V)) / fact (card V)"
  proof (intro arg_cong2[where f = divide] sum.cong; simp, goal_cases)
    case (1 \<sigma>)
    then show ?case
    proof (intro bij_betw_same_card[where f = "\<lambda>v. (THE u. {u,v} \<in> M)"]
        bij_betwI[where g = "\<lambda>u. (THE v. {u,v} \<in> M)"] funcsetI IntI CollectI, goal_cases)
      case (1 x)
      then show ?case
        by (auto intro: the_match_offline)
    next
      case (2 x)
      then show ?case by auto
    next
      case (3 x)
      then show ?case
        by (auto intro: the_match_online)
    next
      case (4 x)
      with perfect_matching show ?case
        by (intro iffI; simp)
           (metis perfect_matchingD(2) the_match the_match_online(1))+
    next
      case (5 x)
      with perfect_matching show ?case
        by (simp add: perfect_matchingD the_match' the_match_offline)
    next
      case (6 y)
      with perfect_matching show ?case
        by (fastforce simp: perfect_matchingD the_match the_match_online)
    qed
  qed

  also from finite non_empty have "\<dots> = pmf ?R i"
    unfolding Let_def
    by (simp add: pmf_bind_pmf_of_set indicator_singleton card_online_eq_offline sum.If_cases)

  finally show "pmf ?L i = pmf ?R i" .
qed

abbreviation "matched_before_t_set t \<equiv> 
  do {
    \<sigma> \<leftarrow> pmf_of_set (permutations_of_set V);
    let R = online_match G \<pi> \<sigma>;
    return_pmf {u \<in> set \<pi>. u \<in> Vs R \<and> index \<sigma> (THE v. {u,v} \<in> R) \<le> t}
  }"

lemma expected_size_matched_before_sum: "measure_pmf.expectation (matched_before_t_set t) card =
  (\<Sum>\<sigma>\<in>permutations_of_set V. card {u \<in> set \<pi>. u \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> online_match G \<pi> \<sigma>) \<le> t}) / fact (card V)" (is "?L = ?R")
proof -
  have "?L = (\<Sum>\<^sub>aU. (\<Sum>\<^sub>a\<sigma>. indicat_real (permutations_of_set V) \<sigma> * (if U = {u \<in> set \<pi>. u \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u, v} \<in> online_match G \<pi> \<sigma>) \<le> t} then 1 else 0) / fact (card V)) * real (card U))"
    using perms_of_V non_empty
    by (simp add: pmf_expectation_eq_infsetsum pmf_bind Let_def indicator_singleton)

  also have "\<dots> = (\<Sum>\<^sub>aU. (\<Sum>\<sigma>\<in>permutations_of_set V. (if U = {u \<in> set \<pi>. u \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u, v} \<in> online_match G \<pi> \<sigma>) \<le> t} then 1 else 0) / fact (card V)) * (card U))"
  proof (intro infsetsum_cong arg_cong2[where f = "(*)"] infsetsum_sum_cong, goal_cases)
    case (1 x)
    show ?case
      by (rule finite_subset[where B = "permutations_of_set V"])
         (auto simp: indicator_eq_0_iff)
  next
    case (5 x a)
    then show ?case
      by (auto simp: indicator_eq_0_iff)
  qed simp_all

  also have "\<dots> = (\<Sum>U\<in>Pow(set \<pi>). (\<Sum>\<sigma>\<in>permutations_of_set V. (if U = {u \<in> set \<pi>. u \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> online_match G \<pi> \<sigma>) \<le> t} then 1 else 0) / fact (card V)) * (card U))"
    by (intro infsetsum_sum_cong)
       (auto intro!: finite_subset[where B = "Pow(set \<pi>)"] elim: sum.not_neutral_contains_not_neutral split: if_splits)

  also have "\<dots> = (\<Sum>\<sigma>\<in>permutations_of_set V. (\<Sum>U\<in>Pow(set \<pi>). (if U = {u \<in> set \<pi>. u \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> online_match G \<pi> \<sigma>) \<le> t} then 1 else 0) / fact (card V) * (card U)))"
    by (subst sum.swap)
       (simp add:  sum_distrib_right)

  also have "\<dots> = (\<Sum>\<sigma>\<in>permutations_of_set V. card {u \<in> set \<pi>. u \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> online_match G \<pi> \<sigma>) \<le> t} / fact (card V))"
    by (auto simp: mult_delta_left simp flip: sum_divide_distrib)

  finally show ?thesis
    by (auto simp: sum_divide_distrib)
qed

text \<open>
  That probability is simply the expected size of the set of online vertices matched to offline
  vertices of at most rank \<^term>\<open>t::nat\<close> divided by the number of online vertices.
\<close>
lemma matched_before_prob_is_expected_size_div: "measure_pmf.prob (matched_before t) {True} = measure_pmf.expectation (matched_before_t_set t) card / (card V)" (is "?L = ?R")
  using perms_of_V
  by (subst expected_size_matched_before_sum)
     (auto simp add: matched_before_uniform_u pmf_bind_pmf_of_set Let_def measure_pmf_conv_infsetsum
       card_online_eq_offline indicator_singleton sum.If_cases simp flip: sum_divide_distrib 
       intro!: sum.cong arg_cong2[where f = divide] bij_betw_same_card[where f = id] bij_betwI[where g = id])

lemma matched_before_card_eq: "\<sigma> \<in> permutations_of_set V \<Longrightarrow> card {u\<in>set \<pi>. u \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> online_match G \<pi> \<sigma>) \<le> t} = card {v\<in>V. v \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> v \<le> t}"
proof (rule bij_betw_same_card[where f = "\<lambda>u. (THE v. {u,v} \<in> online_match G \<pi> \<sigma>)"],
       rule bij_betwI[where g = "\<lambda>v. (THE u. {u,v} \<in> online_match G \<pi> \<sigma>)"],
       goal_cases)
  case 1
  then show ?case
  proof (intro funcsetI)
    fix u
    assume "u \<in> {u \<in> set \<pi>. u \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u, v} \<in> online_match G \<pi> \<sigma>) \<le> t}"

    then have u: "u \<in> set \<pi>" "u \<in> Vs (online_match G \<pi> \<sigma>)" "index \<sigma> (THE v. {u,v} \<in> online_match G \<pi> \<sigma>) \<le> t"
      by blast+

    then obtain e where e: "e \<in> online_match G \<pi> \<sigma>" "u \<in> e"
      by (auto elim: vs_member_elim)

    with u bipartite obtain v where v: "{u,v} \<in> online_match G \<pi> \<sigma>" "v \<in> V"
      by (metis bipartite_vertex(2) empty_iff insert_iff online_subset_vs online_match_edgeE)

    with 1 have "(THE v. {u,v} \<in> online_match G \<pi> \<sigma>) = v"
      by (auto intro: the_match' dest: matching_if_perm)

    with u v show "(THE v. {u, v} \<in> online_match G \<pi> \<sigma>) \<in> {v \<in> V. v \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> v \<le> t}"
      by auto
  qed
next
  case 2
  then show ?case
  proof (intro funcsetI)
    fix v
    assume "v \<in> {v \<in> V. v \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> v \<le> t}"

    then have v: "v \<in> V" "v \<in> Vs (online_match G \<pi> \<sigma>)" "index \<sigma> v \<le> t"
      by blast+

    then obtain e where e: "e \<in> online_match G \<pi> \<sigma>" " v \<in> e"
      by (auto elim: vs_member_elim)

    with v bipartite obtain u where u: "{u,v} \<in> online_match G \<pi> \<sigma>" "u \<in> set \<pi>"
      by (metis bipartite_vertex(2) doubleton_eq_iff graph_invar_G graph_invar_no_edge_no_vertex 
                graph_abs_online_match offline_subset_vs online_match_edgeE)

    with 2 have "(THE u. {u,v} \<in> online_match G \<pi> \<sigma>) = u" "(THE v. {u,v} \<in> online_match G \<pi> \<sigma>) = v"
      by (auto intro: the_match the_match' dest: matching_if_perm)

    with u v show "(THE u. {u, v} \<in> online_match G \<pi> \<sigma>) \<in> {u \<in> set \<pi>. u \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u, v} \<in> online_match G \<pi> \<sigma>) \<le> t}"
      by auto
  qed
next
  case (3 u)
  then have u: "u \<in> set \<pi>" "u \<in> Vs (online_match G \<pi> \<sigma>)"
    by blast+

  then obtain e where e: "e \<in> online_match G \<pi> \<sigma>" "u \<in> e"
    by (auto elim: vs_member_elim)

  with u bipartite obtain v where "{u,v} \<in> online_match G \<pi> \<sigma>"
    by (meson graph_invar_G graph_invar_no_edge_no_vertex graph_abs_online_match)

  with 3 have "(THE u. {u,v} \<in> online_match G \<pi> \<sigma>) = u" "(THE v. {u,v} \<in> online_match G \<pi> \<sigma>) = v"
    by (auto intro: the_match the_match' dest: matching_if_perm)

  then show ?case
    by simp
next
  case (4 v)
  then have v: "v \<in> V" "v \<in> Vs (online_match G \<pi> \<sigma>)"
    by blast+

  then obtain e where e: "e \<in> online_match G \<pi> \<sigma>" "v \<in> e"
    by (auto elim: vs_member_elim)

  with v obtain u where u: "{u,v} \<in> online_match G \<pi> \<sigma>"
    by (meson graph_invar_G graph_abs_online_match graph_invar_vertex_edgeE')

  with 4 have "(THE u. {u,v} \<in> online_match G \<pi> \<sigma>) = u" "(THE v. {u,v} \<in> online_match G \<pi> \<sigma>) = v"
    by (auto intro: the_match the_match' dest: matching_if_perm)

  then show ?case
    by simp
qed

text \<open>
  The expected size of that set is then again the sum of probabilities of the offline vertices
  of rank at most \<^term>\<open>t::nat\<close> being matched.
\<close>
lemma expected_size_matched_before_is_sum_of_probs: "t < card V \<Longrightarrow> measure_pmf.expectation (matched_before_t_set t) card = (\<Sum>s\<le>t. measure_pmf.prob (rank_matched s) {True})" (is "_ \<Longrightarrow> ?L = ?R")
proof -
  assume t: "t < card V"

  have "?L = (\<Sum>\<sigma>\<in>permutations_of_set V. (card {u\<in>set \<pi>. u \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> (THE v. {u,v} \<in> online_match G \<pi> \<sigma>) \<le> t})) / fact (card V)"
    by (simp add: expected_size_matched_before_sum)

  also have "\<dots> = (\<Sum>\<sigma>\<in>permutations_of_set V. (card {v\<in>V. v \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> v \<le> t})) / fact (card V)"
    by (simp add: matched_before_card_eq)

  also have "\<dots> = (\<Sum>\<sigma>\<in>permutations_of_set V. (\<Sum>s\<le>t. if (\<sigma> ! s \<in> Vs (online_match G \<pi> \<sigma>)) then 1 else 0)) / fact (card V)"
  proof (intro arg_cong2[where f = divide], goal_cases)
    case 1
    have "(\<Sum>\<sigma>\<in>permutations_of_set V. card {v \<in> V. v \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> v \<le> t}) = (\<Sum>\<sigma>\<in>permutations_of_set V. \<Sum>s\<le>t. if \<sigma> ! s \<in> Vs (online_match G \<pi> \<sigma>) then 1 else 0)"
    proof (intro sum.cong, goal_cases)
      case (2 \<sigma>)
      then have "card {v \<in> V. v \<in> Vs (online_match G \<pi> \<sigma>) \<and> index \<sigma> v \<le> t} = card ({..t} \<inter> {s. \<sigma> ! s \<in> Vs (online_match G \<pi> \<sigma>)})"
      proof (intro bij_betw_same_card[where f = "index \<sigma>"] bij_betwI[where g = "(!) \<sigma>"] funcsetI CollectI IntI, goal_cases)
        case (1 x)
        then show ?case by blast
      next
        case (2 x)
        then show ?case
          by (simp add: permutations_of_setD)
      next
        case (3 x)
        with t show ?case
        proof (intro conjI, goal_cases)
          case 1
          then have "\<sigma> ! x \<in> set \<sigma>"
            by (auto intro!: nth_mem simp: length_finite_permutations_of_set)
          with 1 show ?case
            by (auto dest: permutations_of_setD)
        next
          case 3
          then show ?case
            by (auto simp: index_nth_id length_finite_permutations_of_set permutations_of_setD)
        qed simp

      next
        case (4 x)
        then show ?case
          by (simp add: permutations_of_setD)
      next
        case (5 y)
        with t show ?case
          by (auto simp: length_finite_permutations_of_set index_nth_id permutations_of_setD)
      qed
      then show ?case
        by (auto simp: sum.If_cases)
    qed simp

    then show ?case
      by (auto simp: sum.If_cases)
  qed simp

  also have "\<dots> = ?R"
    using perms_of_V
    by (subst sum.swap)
       (simp add: bernoulli_prob_True_expectation pmf_expectation_eq_infsetsum pmf_bind_pmf_of_set indicator_singleton mult_delta_left card_True sum.If_cases flip: sum_divide_distrib)

  finally show ?thesis .
qed

text \<open>
  That closes the circle and yields the bound as shown in Lemma 5 in the paper.
\<close>
lemma rank_t_unmatched_prob_bound: 
  "t < card V \<Longrightarrow> 
     1 - measure_pmf.prob (rank_matched t) {True} \<le> 
        1 / (card V) * (\<Sum>s\<le>t. measure_pmf.prob (rank_matched s) {True})" (is "_ \<Longrightarrow> ?L \<le> ?R")
proof -
  assume t: "t < card V"

  obtain p where "rank_matched t = bernoulli_pmf p" "0 \<le> p" "p \<le> 1"
    using bool_pmf_is_bernoulli_pmf by blast

  then have "?L = measure_pmf.prob (rank_matched t) {False}"
    by (auto simp: measure_pmf_conv_infsetsum)

  also have "\<dots> \<le> measure_pmf.prob (matched_before t) {True}"
    using t
    by (intro rank_t_unmatched_prob_bound_matched_before)

  also have "\<dots> = measure_pmf.expectation (matched_before_t_set t) card / (card V)"
    by (simp add: matched_before_prob_is_expected_size_div)

  also have "\<dots> = ?R"
    using t
    by (simp add: expected_size_matched_before_is_sum_of_probs)

  finally show "?L \<le> ?R" .
qed

lemma expected_size_is_sum_of_matched_ranks: "measure_pmf.expectation ranking card = (\<Sum>s<card V. measure_pmf.prob (rank_matched s) {True})"
proof -
  from perms_of_V have "measure_pmf.expectation ranking card = (\<Sum>\<sigma>\<in>permutations_of_set V. (card (online_match G \<pi> \<sigma>))) / fact (card V)"
    unfolding ranking_def
    by (auto simp: pmf_expectation_bind_pmf_of_set field_simps sum_divide_distrib)    

  also have "\<dots> = (\<Sum>\<sigma>\<in>permutations_of_set V. \<Sum>t<card V. of_bool (\<sigma> ! t \<in> Vs (online_match G \<pi> \<sigma>))) / fact (card V)"
    using online_match_card_is_sum_of_matched_vertices
    by auto

  also have "\<dots> = measure_pmf.expectation (pmf_of_set (permutations_of_set V)) (\<lambda>\<sigma>. \<Sum>t<card V. of_bool (\<sigma> ! t \<in> Vs (online_match G \<pi> \<sigma>)))"
    using perms_of_V
    by (auto simp: integral_pmf_of_set)

  also have "\<dots> = (\<Sum>t<card V. measure_pmf.expectation (pmf_of_set (permutations_of_set V)) (\<lambda>\<sigma>. of_bool (\<sigma> ! t \<in> Vs (online_match G \<pi> \<sigma>))))"
    using expectation_sum_pmf_of_set[OF perms_of_V]
    by fast

  also have "\<dots> = (\<Sum>t<card V. measure_pmf.prob (rank_matched t) {True})"
    by (subst rank_matched_prob_is_expectation)
       (use perms_of_V in \<open>auto simp add: pmf_expectation_bind_pmf_of_set integral_pmf_of_set divide_inverse\<close>)

  finally show ?thesis .
qed

text \<open>
  The upper bound on the probability that the vertex of rank \<^term>\<open>t::nat\<close> is unmatched is then
  used to lower bound the ratio between the expected size of the matching RANKING produces
  and the size of the perfect matching (i.e.\ the competitive ratio).
\<close>
lemma comp_ratio_no_limit: "measure_pmf.expectation ranking card / (card V) \<ge> 1 - (1 - 1/(card V + 1)) ^ (card V)" (is "?L \<ge> ?R")
proof -
  have "?R = ((card V) - (card V) * (1 - 1 / (card V + 1))^(card V)) / card V"
    by (auto simp: diff_divide_distrib)

  also have "\<dots> = ((card V) - (card V) * (card V / (card V + 1)) ^ (card V)) / card V"
    by (simp add: field_simps)

  also have "\<dots> = (\<Sum>s<card V. (1 - 1/(card V + 1))^(s+1)) / card V"
    by (simp only: sum_gp_strict_Suc)

  also have "\<dots> = (\<Sum>s\<le>card V - 1. (1 - 1/(real (card V) + 1))^(s+1)) / card V"
    using non_empty
    by (auto simp: ac_simps simp del: finite)
       (metis (mono_tags, lifting) Suc_pred lessThan_Suc_atMost)

  also have "\<dots> \<le> (\<Sum>s\<le>card V - 1. measure_pmf.prob (rank_matched s) {True}) / card V"
    using non_empty finite
    by (intro divide_right_mono bounded_by_sum_bounds_sum rank_t_unmatched_prob_bound)
       (auto simp: first_rank_matched_prob_1[simplified] card_gt_0_iff)

  also have "\<dots> = ?L"
    by (subst expected_size_is_sum_of_matched_ranks)
       (metis (no_types, lifting) One_nat_def Suc_pred card_gt_0_iff lessThan_Suc_atMost local.finite non_empty)

  finally show ?thesis .
qed

end (* locale ranking_on_perfect_matching *)

lemma sum_split:
  assumes "finite A" "finite B"
  assumes "\<Union>(g ` A) = B"
  assumes "\<And>x x'. x \<in> A \<Longrightarrow> x' \<in> A \<Longrightarrow> x \<noteq> x' \<Longrightarrow> g x \<inter> g x' = {}"
  shows "(\<Sum>x\<in>A. (\<Sum>y\<in>g x. f y)) = (\<Sum>y\<in>B. f y)"
  using assms
  by (smt (verit, ccfv_SIG) finite_UN sum.UNION_disjoint sum.cong)

context wf_ranking
begin

lemma expectation_make_perfect_matching_le:
  defines "G' \<equiv> make_perfect_matching G M"
  shows "measure_pmf.expectation (do {\<sigma> \<leftarrow> pmf_of_set (permutations_of_set (V \<inter> Vs G')); return_pmf (online_match G' \<pi> \<sigma>)}) card \<le>
    measure_pmf.expectation ranking card" (is "?L \<le> ?R")
proof -
  have "?R = (\<Sum>\<sigma>\<in>permutations_of_set V. card (online_match G \<pi> \<sigma>) / fact (card V))"
    unfolding ranking_def
    using perms_of_V
    by (auto simp: pmf_expectation_bind_pmf_of_set field_simps sum_divide_distrib)

  also have "\<dots> = (\<Sum>\<sigma>'\<in>permutations_of_set (V \<inter> Vs G'). (\<Sum>\<sigma>\<in>{\<sigma>\<in>permutations_of_set V. [v <- \<sigma>. v \<in> V \<inter> Vs G'] = \<sigma>'}. card (online_match G \<pi> \<sigma>) / fact (card V)))"
    by (rule sum_split[symmetric], auto; intro permutations_of_setI)
       (auto dest: permutations_of_setD)

  also have "\<dots> \<ge> (\<Sum>\<sigma>'\<in>permutations_of_set (V \<inter> Vs G'). (\<Sum>\<sigma>\<in>{\<sigma>\<in>permutations_of_set V. [v <- \<sigma>. v \<in> V \<inter> Vs G'] = \<sigma>'}. card (online_match G' \<pi> \<sigma>) / fact (card V)))" (is "_ \<ge> ?S")
    unfolding G'_def
  proof (intro sum_mono divide_right_mono, goal_cases)
    case (1 \<sigma>' \<sigma>)
    with bipartite bipartite_subgraph[OF bipartite subgraph_make_perfect_matching, of M]
    show ?case
      by (auto intro!: ranking_matching_card_leq_on_perfect_matching_graph[of G _ \<pi> \<sigma> M] ranking_matching_online_match dest: permutations_of_setD)
  qed simp

  finally have "?S \<le> ?R" .
  note equalityI[rule del]
  have "?S = (\<Sum>\<sigma>'\<in>permutations_of_set (V \<inter> Vs G'). (\<Sum>\<sigma>\<in>{\<sigma>\<in>permutations_of_set V. [v <- \<sigma>. v \<in> V \<inter> Vs G'] = \<sigma>'}. card (online_match G' \<pi> \<sigma>') / fact (card V)))"
    by (intro sum.cong arg_cong2[where f = "(/)"] arg_cong[where f = card] arg_cong[where f = real])
       (auto intro!: online_match_filter_vertices_in_graph_online_match[symmetric] dest: permutations_of_setD)

  also have "\<dots> = (\<Sum>\<sigma>'\<in>permutations_of_set (V \<inter> Vs G'). (fact (card V) / fact (card (V \<inter> Vs G'))) * real (card (online_match G' \<pi> \<sigma>')) / fact (card V))"
  proof (rule sum.cong, goal_cases)
    case (2 x)
    then show ?case
      by (simp only: sum_constant times_divide_eq_right, intro arg_cong2[where f = divide] arg_cong2[where f = times] card_restrict_permutation_eq_fact)
         auto
  qed simp

  also have "\<dots> = (\<Sum>\<sigma>'\<in>permutations_of_set (V \<inter> Vs G'). card (online_match G' \<pi> \<sigma>') / fact (card (V \<inter> Vs G')))"
    by simp

  also have "\<dots> = ?L"
    using perms_of_V
    by (auto simp: pmf_expectation_bind_pmf_of_set field_simps sum_divide_distrib)

  finally have "?S = ?L" .

  with \<open>?S \<le> ?R\<close> show "?L \<le> ?R"
    by linarith
qed

text \<open>
  What remains is to leverage the repeated application of Lemma 2 to obtain the bound for the
  competitive ratio for all instances.
\<close>
theorem\<^marker>\<open>tag important\<close> ranking_comp_ratio: "measure_pmf.expectation ranking card / (card M) \<ge> 1 - (1 - 1/(card M + 1)) ^ (card M)"
proof (cases "G = {}")
  case True
  with max_card_matching have "M = {}"
    by (auto dest: max_card_matchingD)

  then show ?thesis
    by auto
next
  case False

  have "M \<noteq> {}"
    by (rule max_card_matching_non_empty)
       (use max_card_matching False in \<open>auto\<close>)

  define G' where "G' \<equiv> make_perfect_matching G M"

  then have "G' \<subseteq> G"
    by (auto simp: subgraph_make_perfect_matching)

  with bipartite have bipartite_G': "bipartite G' (set \<pi>) V"
    by (auto intro: bipartite_subgraph)

  have perfect_in_G': "perfect_matching G' M"
      unfolding G'_def
      using finite_graph max_card_matching
      by (intro perfect_matching_make_perfect_matching)
         (auto dest: max_card_matchingD)

  have bipartite_G': "bipartite G' (set [u <- \<pi>. u \<in> Vs G']) (V \<inter> Vs G')"
  proof (intro bipartiteI)
    fix e assume e: "e \<in> G'"
    then obtain u v where e_in_G: "e = {u,v}" "u \<in> set \<pi>" "v \<in> V"
      unfolding G'_def
      using bipartite
      by (auto dest!: subgraph_make_perfect_matching[THEN subsetD] elim: bipartite_edgeE)

    with e have "u \<in> Vs G'" "v \<in> Vs G'"
      by blast+

    with e_in_G show "\<exists>u v. e = {u,v} \<and>  u \<in> set [u <- \<pi>. u \<in> Vs G'] \<and> v \<in> V \<inter> Vs G'"
      by auto
  qed (use bipartite in \<open>auto dest: bipartite_disjointD\<close>)

  from bipartite_G' have vs_G':  "Vs G' = (set [u <- \<pi>. u \<in> Vs G']) \<union> (V \<inter> Vs G')"
    by (auto simp: vs_make_perfect_matching dest: bipartite_vertex)

  with perfect_in_G' bipartite_G' have card_eq: "card (V \<inter> Vs G') = card M"
    by (auto dest: perfect_matching_bipartite_card_eq)

  interpret pm: ranking_on_perfect_matching "G'" "[u <- \<pi>. u \<in> Vs G']" "V \<inter> Vs G'"
  proof (unfold_locales)
    show "bipartite G' (set [u <- \<pi>. u \<in> Vs G']) (V \<inter> Vs G')"
      using bipartite_G' by blast
  next
    show "finite G'"
      using finite_graph \<open>G' \<subseteq> G\<close>
      by (auto intro: finite_subset)
  next
    show "max_card_matching G' M"
      unfolding G'_def
      using max_card_matching
      by (auto intro!: max_card_matching_make_perfect_matching dest: max_card_matchingD
               intro: graph_abs.finite_E)

    with \<open>M \<noteq> {}\<close> show "G' \<noteq> {}"
      by (auto dest: max_card_matchingD)
  next
    show "Vs G' = (set [u <- \<pi>. u \<in> Vs G']) \<union> (V \<inter> Vs G')"
      using vs_G' by blast
  next
    show "perfect_matching G' M"
      using \<open>perfect_matching G' M\<close> by blast
  qed

  have "1 - (1 - (1/(card M + 1)))^(card M) \<le> measure_pmf.expectation pm.ranking card / card M"
    using pm.comp_ratio_no_limit[simplified card_eq]
    by blast

  also have "\<dots> \<le> measure_pmf.expectation ranking card / card M"
    unfolding pm.ranking_def
    using G'_def
    by (simp only: online_match_filter_vs, intro divide_right_mono expectation_make_perfect_matching_le)
       auto
  
  finally show ?thesis .
qed

end

subsection \<open>Competitive Ratio in the Limit\label{sec:prob-limit}\<close>
text \<open>
  In the final part of this section we define in dependence of \<^term>\<open>n::nat\<close> arbitrary instances for
  the online bipartite matching problem with a maximum matching of size \<^term>\<open>n::nat\<close>. Subsequently
  we use that definition to prove that the competitive ratio tends to the famous $1 - \frac{1}{e}$.
\<close>
abbreviation matching_instance_nat :: "nat \<Rightarrow> (nat \<times> nat) graph" where
  "matching_instance_nat n \<equiv> {{(0,k),(Suc 0,k)} |k. k < n}"

definition ranking_instances_nat :: "nat \<Rightarrow> (nat \<times> nat) graph set" where
  "ranking_instances_nat n \<equiv> {G. max_card_matching G (matching_instance_nat n) \<and>
     finite G \<and> G \<subseteq> {{(0,k),(Suc 0,l)} |k l. k < 2*n \<and> l < 2*n}}"

definition arrival_orders :: "(nat \<times> nat) graph \<Rightarrow> (nat \<times> nat) list set" where
  "arrival_orders G \<equiv> permutations_of_set {(Suc 0,l) |l. \<exists>k. {(0,k),(Suc 0,l)} \<in> G}"

definition offline_vertices :: "(nat \<times> nat) graph \<Rightarrow> (nat \<times> nat) set" where
  "offline_vertices G \<equiv> {(0, k) |k. \<exists>l. {(0, k),(Suc 0, l)} \<in> G}"

lemma matching_matching_instance_nat[simp]:
  "matching (matching_instance_nat n)"
  unfolding matching_def
  by auto

lemma card_matching_instance_nat:
  "card (matching_instance_nat n) = card {..<n}"
  by (intro bij_betw_same_card[where f = "\<lambda>e. snd (SOME x. x \<in> e)"] bij_betwI[where g = "\<lambda>n. {(0,n),(Suc 0,n)}"])
     (auto simp: snd_some_disj)

lemma ranking_instanceE':
  obtains G where "max_card_matching G (matching_instance_nat n)"
    "finite G" "G \<subseteq> {{(0,k),(Suc 0,l)} |k l. k < 2*n \<and> l < 2*n}"
proof
  show "max_card_matching (matching_instance_nat n) (matching_instance_nat n)"
    by (auto intro: max_card_matchingI intro!: card_mono)
next
  show "finite (matching_instance_nat n)"
    by auto
next
  show "matching_instance_nat n \<subseteq> {{(0,k), (Suc 0,l)} |k l. k < 2*n \<and> l < 2*n}"
    by force
qed

lemma ranking_instanceE:
  obtains G where "G \<in> ranking_instances_nat n"
  unfolding ranking_instances_nat_def
  using ranking_instanceE'[of n thesis]
  by blast

lemma
  assumes "G \<in> ranking_instances_nat n"
  shows max_card_matching_instance: "max_card_matching G (matching_instance_nat n)"
    and finite_instance: "finite G"
    and subset_instance: "G \<subseteq> {{(0,k),(Suc 0,l)} |k l. k < 2 * n \<and> l < 2 * n}"
  using assms
  unfolding ranking_instances_nat_def
  by auto

lemma finite_vs_instance: "G \<in> ranking_instances_nat n \<Longrightarrow> finite (Vs G)"
  using finite_instance subset_instance
  unfolding Vs_def
  by blast

lemma
  assumes "\<pi> \<in> arrival_orders G"
  shows distinct_arrival_order: "distinct \<pi>"
    and set_arrival_order: "set \<pi> = {(Suc 0,k) |k. \<exists>l. {(0,l),(Suc 0,k)} \<in> G}"
  using assms
  unfolding arrival_orders_def
  by (auto dest: permutations_of_setD)

lemma wf_ranking_nat:
  assumes "G \<in> ranking_instances_nat n"
  assumes "\<pi> \<in> arrival_orders G"
  shows "wf_ranking G \<pi> (offline_vertices G) (matching_instance_nat n)"
proof (unfold_locales, goal_cases)
  case 1
  then show bipartite_instance: ?case
  proof (intro bipartiteI, goal_cases)
    case 1
    from assms show ?case
      unfolding offline_vertices_def
      by (auto simp: set_arrival_order)
  next
    case (2 e)
    with assms show ?case
      unfolding offline_vertices_def ranking_instances_nat_def
      using set_arrival_order subsetD by blast
  qed

  case 3
  with assms show ?case
    by (intro equalityI bipartite_vs_subset[OF bipartite_instance])
       (auto simp add: set_arrival_order Vs_def offline_vertices_def intro: bipartite_vs_subset[OF bipartite_instance])
next
  case 2
  from finite_instance assms show ?case by blast
next
  case 4
  from max_card_matching_instance assms show ?case by blast
qed

lemma finite_ranking_instances: "finite (ranking_instances_nat n)"
proof (rule finite_subset)
   show "ranking_instances_nat n \<subseteq> Pow (Pow ({0,1} \<times> {..< Suc (2 * n)}))" (is "_ \<subseteq> ?G")
     unfolding ranking_instances_nat_def by auto
   show "finite ?G" by auto
qed

lemma finite_arrival_orders:
  shows "finite (arrival_orders G)"
  unfolding arrival_orders_def
  by simp

lemma non_empty_arrival_orders:
  assumes "finite (Vs G)"
  shows "arrival_orders G \<noteq> {}"
  using assms
  unfolding arrival_orders_def
  apply (auto)
  apply (rule finite_subset[of _ "Vs G"])
   apply (auto)
  done

definition comp_ratio_nat where
  "comp_ratio_nat n \<equiv> Min {Min {measure_pmf.expectation (wf_ranking.ranking G \<pi> (offline_vertices G)) card / card (matching_instance_nat n) | \<pi>. \<pi> \<in> arrival_orders G} | G. G \<in> ranking_instances_nat n}"

lemma comp_ratio_nat_bound:
  shows "1 - (1 - 1/real (n+1))^n \<le> comp_ratio_nat n"
proof -
  have "1 - (1 - 1/(card (matching_instance_nat n) + 1))^card (matching_instance_nat n) \<le> comp_ratio_nat n"
    unfolding comp_ratio_nat_def
  proof (intro Min.boundedI, goal_cases)
    case 1
    then show ?case
      by (auto intro!: finite_image_set intro: finite_ranking_instances)
  next
    case 2
    obtain G where "G \<in> ranking_instances_nat n"
      using ranking_instanceE by blast

    then show ?case
      by blast
  next
    case (3 c)
    then show ?case
    proof (auto, intro Min.boundedI, goal_cases)
      case (1 G)
      then show ?case
        by (auto intro!: finite_image_set intro: finite_arrival_orders)
    next
      case (2 G)
      then show ?case
        by (auto dest: finite_vs_instance non_empty_arrival_orders)
    next
      case (3 G c')
      then show ?case
        using wf_ranking.ranking_comp_ratio[OF wf_ranking_nat]
        by auto
    qed
  qed    

  then show ?thesis
    by (auto simp add: card_matching_instance_nat field_simps)
qed

find_theorems Cauchy

find_theorems "convergent"
find_theorems "lim _"
find_theorems "_ \<longlonglongrightarrow> _" "THE X. _"

theorem\<^marker>\<open>tag important\<close> comp_ratio_limit:
  assumes "comp_ratio_nat \<longlonglongrightarrow> cr"
  shows "1 - exp(-1) \<le> cr"
proof (rule LIMSEQ_le)
  show "(\<lambda>n::nat. 1 - (1 - 1/(n+1))^n) \<longlonglongrightarrow> 1 - exp(-1)"
    by real_asymp

  from assms show "comp_ratio_nat \<longlonglongrightarrow> cr" by blast

  show "\<exists>N. \<forall>n\<ge>N. 1 - (1 - 1 / real (n+1)) ^ n \<le> comp_ratio_nat n"
    by (intro exI[of _ "0"] allI impI comp_ratio_nat_bound)
qed

theorem\<^marker>\<open>tag important\<close> comp_ratio_limit':
  assumes "convergent comp_ratio_nat"
  shows "1 - exp(-1) \<le> (lim comp_ratio_nat)"
  using assms comp_ratio_limit convergent_LIMSEQ_iff
  by blast

end
