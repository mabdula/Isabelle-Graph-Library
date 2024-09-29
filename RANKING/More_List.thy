subsection \<open>More on Lists\label{sec:more-list}\<close>
theory More_List
  imports
    "List-Index.List_Index"
    "HOL-Library.Sublist"
    "HOL-Library.LaTeXsugar"
begin
text \<open>
  Permutations are modelled as distinct lists over some set in this formalization. That means both
  the arrival order of the online vertices $U$ and the (later random) ordering of the offline
  vertices $V$ are modelled as lists. We don't require \<^term>\<open>distinct\<close>ness for the most part in
  the combinatorial part, but rely quite heavily on it in the probabilistic part.

  To obtain an ordering from a list we use the \<^theory>\<open>List-Index.List_Index\<close> AFP entry by
  Nipkow~\cite{List-Index-AFP}.
\<close>

text \<open>
  An important strategy to prove properties of matchings produced by RANKING is by contradiction
  through construction of an infinite chain of vertices with decreasing (or increasing) index.
  The following two induction schemes are useful to this end. Of course, they are also useful
  on their own as specialized forms of strong induction.
\<close>
lemma index_less_induct[case_names index_less]:
  assumes "\<And>x. (\<And>y. index xs y < index xs x \<Longrightarrow> P y xs) \<Longrightarrow> P x xs"
  shows "P x xs"
  using assms
  by (rule measure_induct_rule)

lemma length_minus_index_less_index_gt:
  "length xs - index xs x < length xs - index xs x' \<longleftrightarrow> index xs x' < index xs x"
  by (induction xs) auto

lemma index_gt_induct[case_names index_gt]: 
  assumes "\<And>x. (\<And>y. index xs x < index xs y \<Longrightarrow> P y xs) \<Longrightarrow> P x xs"
  shows "P x xs"
  using assms
proof (induction "length xs - index xs x" arbitrary: x rule: less_induct)
  case less

  show ?case
  proof (rule less(2), rule less.hyps, goal_cases)
    case (1 y)
    then show ?case
      by (simp add: length_minus_index_less_index_gt)
  next
    case (2 y x')
    with less show ?case
      by fast
  qed
qed

lemma index_less_in_set: "index xs x < index xs x' \<Longrightarrow> x \<in> set xs"
  by (metis index_conv_size_if_notin index_le_size leD)

lemma transp_index_less: "transp (\<lambda>a b. index xs a < index xs b)"
  by (auto intro: transpI)

lemma sorted_wrt_index_less_distinct:
  "sorted_wrt (\<lambda>a b. index \<sigma> a < index \<sigma> b) xs \<Longrightarrow> distinct xs"
  by (induction xs) auto

lemma index_filter_neq: "a \<noteq> v \<Longrightarrow> b \<noteq> v \<Longrightarrow> index xs a \<le> index xs b \<longleftrightarrow> index [x <- xs. x \<noteq> v] a \<le> index [x <- xs. x \<noteq> v] b"
  by (induction xs) auto

lemma length_at_least_two_Cons_Cons: "2 \<le> length xs \<Longrightarrow> \<exists>x x' xs'. xs = x # x' # xs'"
  by (metis Suc_le_length_iff numeral_2_eq_2)

lemma filter_take_filter: "filter P (take i (filter P xs)) = take i (filter P xs)"
  by (auto intro!: filter_True dest: in_set_takeD)

lemma filter_drop_filter: "filter P (drop i (filter P xs)) = drop i (filter P xs)"
  by (auto intro!: filter_True dest: in_set_dropD)

subsubsection \<open>Moving a vertex to a position\<close>
text \<open>
  Moving vertices to some index plays a crucial role in the probabilistic part of the proof.
  It is used to argue about the probability of the vertex at index $t$ being matched. Moving an
  arbitrary vertex to index $t$ in an arbitrary permutation $\sigma$ is needed to ensure the
  independence of certain events.
\<close>
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

(*no_translations\<^marker>\<open>tag invisible\<close>*)
  (*"_MapUpd m (_Maplets xy ms)"  \<rightleftharpoons> "_MapUpd (_MapUpd m xy) ms"*)
  (*"_MapUpd m (_maplet  x y)"    \<rightleftharpoons> "m(x := CONST Some y)"*)
  (*"_Map ms"                     \<rightleftharpoons> "_MapUpd (CONST empty) ms"
  "_Map (_Maplets ms1 ms2)"     \<leftharpoondown> "_MapUpd (_Map ms1) ms2"
  "_Maplets ms1 (_Maplets ms2 ms3)" \<leftharpoondown> "_Maplets (_Maplets ms1 ms2) ms3"*)

definition move_to :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a list" ("_[_ \<mapsto> _]" [100,100]) where 
  "move_to xs v i \<equiv> (take i [x <- xs. x \<noteq> v]) @ v # (drop i [x <- xs. x \<noteq> v])"

text \<open>
  This induction scheme is helpful in proving properties about \<^term>\<open>move_to\<close>.
\<close>
lemma induct_list_nat[case_names nil_zero nil_suc cons_zero cons_suc]:
  assumes "P [] 0"
  assumes "\<And>n. P [] n \<Longrightarrow> P [] (Suc n)"
  assumes "\<And>x xs. P xs 0 \<Longrightarrow> P (x#xs) 0" 
  assumes "\<And>x xs n. P xs n \<Longrightarrow> P (x#xs) (Suc n)"
  shows "P xs n"
  using assms
  by (induction_schema) (pat_completeness, lexicographic_order)

lemma append_cong: "xs = xs' \<Longrightarrow> ys = ys' \<Longrightarrow> xs @ ys = xs' @ ys'"
  by simp

lemma move_to_gt_length:
  "length xs \<le> i \<Longrightarrow> xs[v \<mapsto> i] = xs[v \<mapsto> length xs]"
  unfolding move_to_def
  by (auto intro!: append_cong dest: le_trans[OF length_filter_le])

lemma move_elem_to_gt_length:
  assumes "length xs \<le> i" "v \<in> set xs"
  shows "xs[v \<mapsto> i] = xs[v \<mapsto> length xs - 1]"
  unfolding move_to_def
proof (rule append_cong)
  have "length [x <- xs. x \<noteq> v] < length xs"
    using assms
    by (auto intro: length_filter_less)

  then have l: "length [x <- xs. x \<noteq> v] \<le> length xs - 1"
    by simp

  with assms show "take i [x <- xs. x \<noteq> v] = take (length xs - 1) [x <- xs. x \<noteq> v]"
    by simp

  from assms l show "v # drop i [x <- xs. x \<noteq> v] = v # drop (length xs - 1) [x <- xs. x \<noteq> v]"
    by simp
qed

lemma move_to_Cons_Suc:
  assumes "x \<noteq> v"
  assumes "Suc n = i"
  shows "(x#xs)[v \<mapsto> i] = x # xs[v \<mapsto> n]"
  using assms
  unfolding move_to_def
  by auto

lemma move_to_Cons_Cons_Suc:
  assumes "Suc n = i"
  assumes "x \<noteq> v"
  shows "(x#v#xs)[x \<mapsto> i] = v#xs[x \<mapsto> n]"
  using assms
  unfolding move_to_def
  by auto

lemma move_hd_to:
  "(v#xs)[v \<mapsto> i] = xs[v \<mapsto> i]"
  unfolding move_to_def
  by auto

lemma move_to_neq_0_Cons:
  assumes "x \<noteq> v"
  assumes "i \<noteq> 0"
  shows "(x#xs)[v \<mapsto> i] = x # xs[v \<mapsto> (i - 1)]"
  using assms
  unfolding move_to_def
  by (auto simp: drop_Cons' take_Cons')

lemma move_to_0:
  shows "xs[v \<mapsto> 0] = v # [x <- xs. x \<noteq> v]"
  unfolding move_to_def
  by simp

lemma move_to_Nil:
  shows "[][v \<mapsto> i] = [v]"
  unfolding move_to_def
  by simp

lemma move_to_last:
  shows "xs[v \<mapsto> length xs] = [x <- xs. x \<noteq> v] @ [v]"
  unfolding move_to_def
  by simp

lemma move_to_Cons_eq:
  "(v#xs)[v \<mapsto> i] = xs[v \<mapsto> i]"
  unfolding move_to_def
  by simp

lemma move_to_distinct:
  "distinct xs \<Longrightarrow> distinct xs[x \<mapsto> i]"
  unfolding move_to_def
  by (auto dest: in_set_dropD in_set_takeD distinct_filter set_take_disj_set_drop_if_distinct)

lemma count_list_append: "count_list (xs@ys) x = count_list xs x + count_list ys x"
  by (induction xs) auto

lemma move_to_set: "set xs[x \<mapsto> i] = set xs \<union> {x}"
  unfolding move_to_def
  by (auto dest: in_set_takeD in_set_dropD)
     (metis (mono_tags, lifting) append_take_drop_id filter_set last_index_append last_index_size_conv length_append member_filter)

lemma move_to_set_eq: "x \<in> set xs \<Longrightarrow> set xs[x \<mapsto> i] = set xs"
  by (auto simp: move_to_set)

lemma move_to_insert_before:
  "i \<le> index \<sigma> w \<Longrightarrow> v \<noteq> w \<Longrightarrow> v \<notin> set \<sigma> \<Longrightarrow> index \<sigma>[v \<mapsto> i] w = Suc (index \<sigma> w)"
  by (induction \<sigma> i rule: induct_list_nat)
     (auto simp: move_to_0 move_to_Cons_Suc)

lemma move_to_insert_after:
  "index \<sigma> w < i \<Longrightarrow> i \<le> length \<sigma> \<Longrightarrow> v \<noteq> w \<Longrightarrow> v \<notin> set \<sigma> \<Longrightarrow> index \<sigma>[v \<mapsto> i] w = index \<sigma> w"
  by (induction \<sigma> i rule: induct_list_nat)
     (auto simp: move_to_Cons_Suc)

lemma index_less_filter_eq: "index xs w < index xs v \<Longrightarrow> index [x <- xs. x \<noteq> v] w = index xs w"
  by (induction xs) auto

lemma index_less_filter: "w \<noteq> v \<Longrightarrow> w' \<noteq> v \<Longrightarrow> index xs w < index xs w' \<longleftrightarrow> index [x <- xs. x \<noteq> v] w < index [x <- xs. x \<noteq> v] w'"
  by (induction xs) auto

lemma not_in_take: "x \<notin> set xs \<Longrightarrow> x \<notin> set (take i xs)"
  by (auto dest: in_set_takeD)

lemma not_in_drop: "x \<notin> set xs \<Longrightarrow> x \<notin> set (drop i xs)"
  by (auto dest: in_set_dropD)

lemma not_in_set_filter_length_eq: "v \<notin> set xs \<Longrightarrow> length [x <- xs. x \<noteq> v] = length xs"
  by (induction xs) auto

lemma in_set_distinct_filter_length_eq: "v \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> length [x <- xs. x \<noteq> v] = length xs - 1"
  by (induction xs) (auto simp: not_in_set_filter_length_eq intro!: Suc_pred)

lemma distinct_filter_length: "distinct xs \<Longrightarrow> (length [x <- xs. x \<noteq> v] = length xs \<and> v \<notin> set xs) \<or> (length [x <- xs. x \<noteq> v] = length xs - 1 \<and> v \<in> set xs)"
  by (metis in_set_distinct_filter_length_eq not_in_set_filter_length_eq)

lemma filter_removeAll: "[x <- xs. x \<noteq> v] = removeAll v xs"
  by (induction xs) auto

lemma not_in_set_filter_id: "v \<notin> set xs \<Longrightarrow> [x <- xs. x \<noteq> v] = xs"
  by (simp add: filter_removeAll)

lemma count_zero: "count_list xs v = 0 \<Longrightarrow>  v \<notin> set xs"
  by (induction xs) (auto split: if_splits)

lemma count_in: "v \<in> set xs \<Longrightarrow> count_list xs v \<noteq> 0"
  by (induction xs) auto

lemma Suc_index_filter: "index xs v < index xs w \<Longrightarrow> v \<in> set xs \<Longrightarrow> count_list xs v = 1 \<Longrightarrow> Suc (index [x <- xs. x \<noteq> v] w) = index xs w"
  by (induction xs) (auto simp: not_in_set_filter_id[OF count_zero])

lemma not_Nil_length_SucE: "xs \<noteq> [] \<Longrightarrow> (\<And>n. length xs = Suc n \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction xs) auto

lemma move_to_count_list:
  "count_list xs[x \<mapsto> i] x = 1"
  unfolding move_to_def
  by (auto simp: count_list_append intro!: count_notin simp: not_in_take not_in_drop)

lemma list_eq_count_list_eq:
 "xs = ys \<Longrightarrow> count_list xs x = count_list ys x"
  by simp

lemma move_to_id:
  "count_list \<sigma> v = 1 \<Longrightarrow> \<sigma>[v \<mapsto> index \<sigma> v] = \<sigma>"
  by (induction \<sigma>) (auto simp: move_to_0 filter_id_conv move_to_Cons_Suc count_zero)

lemma move_to_front_less:
  assumes "i < index \<sigma> v"
  assumes "index \<sigma> w < i"
  shows "index \<sigma>[v \<mapsto> i] w = index \<sigma> w"
  using assms
  by (induction \<sigma> arbitrary: i)
     (auto split: if_splits elim: less_natE simp: move_to_Cons_Suc)

lemma move_to_front_between:
  assumes "count_list \<sigma> v \<le> 1"
  assumes "i < index \<sigma> v"
  assumes "i \<le> index \<sigma> w" "index \<sigma> w < index \<sigma> v"
  shows "index \<sigma>[v \<mapsto> i] w = Suc (index \<sigma> w)"
  using assms
  by (induction \<sigma> i rule: induct_list_nat)
     (auto split: if_splits simp: move_to_0 move_to_Cons_Suc)

lemma move_to_front_gr:
  assumes "count_list \<sigma> v = 1"
  assumes "i < index \<sigma> v" 
  assumes "index \<sigma> v < index \<sigma> w"
  shows "index \<sigma>[v \<mapsto> i] w = index \<sigma> w"
proof -
  have "v \<in> set \<sigma>"
    using assms count_notin by fastforce
  then have "count_list \<sigma> v = 1"
    using assms count_zero by blast

  with assms \<open>v \<in> set \<sigma>\<close> show ?thesis
    by (induction \<sigma> i rule: induct_list_nat)
       (auto split: if_splits simp: move_to_0 move_to_Cons_Suc Suc_index_filter)
qed

lemma move_to_back_less:
  assumes "index \<sigma> v < i"
  assumes "index \<sigma> w < index \<sigma> v"
  shows "index \<sigma>[v \<mapsto> i] w = index \<sigma> w"
  using assms
  by (induction \<sigma> arbitrary: i) (auto split: if_splits simp: move_to_neq_0_Cons)

lemma move_to_back_between:
  assumes "count_list \<sigma> v = 1"
  assumes "index \<sigma> v < i"  
  assumes "i < length \<sigma>"
  assumes "index \<sigma> v < index \<sigma> w" "index \<sigma> w \<le> i"
  shows "index \<sigma>[v \<mapsto> i] w + 1 = index \<sigma> w"
proof -
  have "v \<in> set \<sigma>"
    using assms count_notin by fastforce
  then have "count_list \<sigma> v = 1"
    using assms count_zero by blast
  with \<open>v \<in> set \<sigma>\<close> assms show ?thesis
    by (induction \<sigma> arbitrary: i)
       (auto simp: move_to_Cons_eq move_to_neq_0_Cons move_to_insert_after split: if_splits dest!: count_zero)
qed

lemma move_to_back_gr:
  assumes "count_list \<sigma> v = 1"
  assumes "index \<sigma> v < i" "i < length \<sigma>"
  assumes "i < index \<sigma> w"
  shows "index \<sigma>[v \<mapsto> i] w = index \<sigma> w"
  using assms
  by (induction \<sigma> i rule: induct_list_nat)
     (auto split: if_splits dest: count_zero
           simp: move_to_Cons_eq move_to_Cons_Suc move_to_insert_before)

lemma distinct_count_list_le: "distinct xs \<Longrightarrow> count_list xs x \<le> 1"
  by (induction xs) auto

lemma distinct_count_in_set: "distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> count_list xs x = 1"
  by (induction xs) auto

lemma move_to_index_v:
  assumes "distinct \<sigma>"
  assumes "i < length \<sigma>"
  shows "index \<sigma>[v \<mapsto> i] v = i"
  using assms
proof (induction \<sigma> i rule: induct_list_nat)
  case (cons_suc x xs n)
  then show ?case 
    by (cases "x = v")
       (auto simp: move_to_Cons_Suc move_to_Cons_eq move_to_def index_append not_in_set_filter_id 
             dest: in_set_takeD split: if_splits)
qed (auto simp add: move_to_0)

lemma move_to_index_nth:
  assumes "distinct \<sigma>"
  assumes "i < length \<sigma>"
  shows "\<sigma>[v \<mapsto> i] ! i = v"
  using assms
  by (metis count_notin move_to_count_list move_to_index_v nth_index one_neq_zero)

lemma move_to_index_less:
  assumes "distinct \<sigma>"
  assumes "i < length \<sigma>"
  assumes "v \<noteq> w"
  assumes "index \<sigma> w < i"
  shows "index \<sigma>[v \<mapsto> i] w \<le> index \<sigma> w"
  using assms
proof (induction \<sigma> i rule: induct_list_nat)
  case (cons_suc x xs n)
  then show ?case 
    by (auto simp: move_to_Cons_Suc move_to_def index_append not_in_set_filter_id set_take_if_index
             dest: in_set_takeD index_take_if_set  split: if_splits)
qed auto

lemma move_to_front_decompE:
  assumes "distinct xs"
  assumes "xs = ps @ x # ss"
  assumes "i \<le> index xs x"
  obtains pps pss where "xs[x \<mapsto> i] = pps @ x # pss @ ss" "pps @ pss = ps"
  using assms
proof (induction xs i arbitrary: ps thesis rule: induct_list_nat)
  case (cons_zero a xs)
  then show ?case
    by (auto simp: move_to_0 not_in_set_filter_id) blast
next
  case (cons_suc a xs n)
  consider (eq) "a = x" | (neq) "a \<noteq> x" by blast
  then show ?case
  proof cases
    case eq
    with cons_suc.prems have "ps = []" 
      by (auto simp: Cons_eq_append_conv)
    with cons_suc show ?thesis 
      by (auto simp: move_to_0 not_in_set_filter_id)
  next
    case neq

    with cons_suc.prems obtain tl_ps where "ps = a # tl_ps" 
      by (auto simp: Cons_eq_append_conv)

    with cons_suc.prems have "xs = tl_ps @ x # ss" 
      by simp

    have "distinct xs"
      using cons_suc.prems(2) by simp

    have "n \<le> index xs x" 
      using cons_suc.prems(4) neq by auto

    with cons_suc.IH \<open>distinct xs\<close> \<open>xs = tl_ps @ x # ss\<close>
    obtain pps pss where "xs[x \<mapsto> n] = pps @ x # pss @ ss" "pps @ pss = tl_ps"
      by blast

    with cons_suc show ?thesis
      by (metis \<open>ps = a # tl_ps\<close> append_Cons move_to_Cons_Suc neq)
  qed
qed auto

lemma move_to_others_less:
  assumes "v \<noteq> w" "v \<noteq> w'"
  shows "index xs w < index xs w' \<longleftrightarrow> index xs[v \<mapsto> i] w < index xs[v \<mapsto> i] w'"
  using assms
proof (induction xs arbitrary: i)
  case (Cons a xs)
  then show ?case
  proof (cases i)
    case 0
    with Cons show ?thesis
      by (auto simp: move_to_0 index_less_filter)
  next
    case (Suc nat)
    then show ?thesis
    proof (cases "a = v")
      case True
      with Cons show ?thesis
        by (auto simp: move_hd_to)
    next
      case False
      with Cons Suc show ?thesis
        by (auto split: if_splits simp: move_to_Cons_Suc index_less_filter)
    qed
  qed
qed (simp add: move_to_Nil)

lemma move_to_others_leq:
  assumes "v \<noteq> w" "v \<noteq> w'"
  shows "index xs w \<le> index xs w' \<longleftrightarrow> index xs[v \<mapsto> i] w \<le> index xs[v \<mapsto> i] w'"
  using assms
  by (metis linorder_not_le move_to_others_less)

lemma index_less_index_leq_move_to:
  "index \<sigma> w < index \<sigma> v \<Longrightarrow> index \<sigma>[v \<mapsto> i] w \<le> index \<sigma> v"
  by (induction \<sigma> i rule: induct_list_nat)
     (auto split: if_splits simp: move_to_0 move_to_Cons_Suc)

lemma distinct_move_to_filter_id: "distinct xs \<Longrightarrow> x \<notin> set xs \<Longrightarrow> filter (\<lambda>v. v \<noteq> x) (xs[x \<mapsto> i]) = xs"
  by (induction xs i rule: induct_list_nat)
     (auto simp: move_to_0 move_to_Nil move_to_Cons_Suc)

lemma move_to_move_back_id:
  assumes "distinct \<sigma>"
  assumes "v \<in> set \<sigma>"
  shows "\<sigma>[v \<mapsto> t][v \<mapsto> index \<sigma> v] = \<sigma>"
  using assms
proof (induction \<sigma> t rule: induct_list_nat)
  case cons_zero
  then show ?case
    by (auto simp: move_to_0 not_in_set_filter_id move_to_Cons_Suc move_to_Cons_eq)
next
  case (cons_suc _ xs _)
  then show ?case
  proof (cases xs)
    case Nil
    with cons_suc show ?thesis
      by (auto simp: move_to_0 move_to_set_eq)
  next
    case Cons
    with cons_suc show ?thesis
      by (auto simp: move_to_set_eq move_to_0 move_to_Cons_Suc distinct_move_to_filter_id move_to_Cons_Cons_Suc)
  qed
qed auto

lemma the_index:
  assumes "distinct \<sigma>"
  assumes "t < length \<sigma>"
  shows "(THE v. index \<sigma> v = t) = \<sigma> ! t"
  using assms
  by (auto intro: index_nth_id simp: index_less_size_conv)

lemma move_to_eq_if:
  "\<sigma>[v \<mapsto> t] = \<sigma>[w \<mapsto> t] \<Longrightarrow> v = w"
proof (induction \<sigma> t rule: induct_list_nat)
  case (cons_suc x xs n)
  consider "v = w" | "v \<noteq> w \<and> v = x" | "v \<noteq> w \<and> w = x" | "v \<noteq> w \<and> v \<noteq> x \<and> w \<noteq> x" by blast
  then show ?case
  proof cases
    case 2
    show ?thesis
    proof (cases xs)
      case Nil
      with cons_suc 2 show ?thesis
        by (auto simp: move_hd_to move_to_Nil move_to_Cons_Suc)
    next
      case (Cons a as)
      consider (snd_v_1) "v = a \<and> n = 0" | (snd_v_Suc) "v = a \<and> n \<noteq> 0" |
        (snd_not_v_1) "v \<noteq> a \<and> n = 0" | (snd_not_v_Suc) "v \<noteq> a \<and> n \<noteq> 0" by blast
      then show ?thesis
      proof cases
        case snd_v_1
        with cons_suc 2 Cons show ?thesis
          by (auto simp: move_to_0 move_to_Cons_Suc move_to_count_list dest: list_eq_count_list_eq[where x = x])          
      next
        case snd_v_Suc
        then obtain n' where "n = Suc n'" "v = a"
          by (auto dest: gr0_implies_Suc)

        with cons_suc 2 Cons show ?thesis
          by (auto simp: move_hd_to move_to_Cons_Suc move_to_count_list dest: list_eq_count_list_eq[where x = x])
      next
        case snd_not_v_1
        with cons_suc 2 Cons show ?thesis
          by (auto simp: move_hd_to move_to_Cons_Suc)
      next
        case snd_not_v_Suc
        with cons_suc 2 Cons show ?thesis
          by (auto simp: move_hd_to move_to_Cons_Suc)
      qed
    qed
  next
    case 3
    show ?thesis
    proof (cases xs)
      case Nil
      with cons_suc 3 show ?thesis
        by (auto simp: move_hd_to move_to_Nil move_to_Cons_Suc)
    next
      case (Cons a as)
      consider (snd_w_1) "w = a \<and> n = 0" | (snd_w_Suc) "w = a \<and> n \<noteq> 0" |
        (snd_not_w_1) "w \<noteq> a \<and> n = 0" | (snd_not_w_Suc) "w \<noteq> a \<and> n \<noteq> 0" by blast
      then show ?thesis
      proof cases
        case snd_w_1
        with cons_suc 3 Cons show ?thesis
          by (auto simp: move_to_0 move_to_Cons_Suc move_to_count_list dest: list_eq_count_list_eq[where x = x])          
      next
        case snd_w_Suc
        then obtain n' where "n = Suc n'" "w = a"
          by (auto dest: gr0_implies_Suc)

        with cons_suc 3 Cons show ?thesis
          by (auto simp: move_to_0 move_to_Cons_Suc move_to_count_list dest: list_eq_count_list_eq[where x = x])
      next
        case snd_not_w_1
        with cons_suc 3 Cons show ?thesis
          by (auto simp: move_hd_to move_to_Cons_Suc)
      next
        case snd_not_w_Suc
        with cons_suc 3 Cons show ?thesis
          by (auto simp: move_hd_to move_to_Cons_Suc)
      qed
    qed
  next
    case 4
    with cons_suc show ?thesis
      by (auto simp: move_to_Cons_Suc)
  qed simp
qed (auto simp: move_to_0 move_to_Nil)

lemma move_to_eq_iff: "\<sigma>[v \<mapsto> t] = \<sigma>[w \<mapsto> t] \<longleftrightarrow> v = w"
  by (auto dest: move_to_eq_if)

lemma subset_butlast_only_one:
  assumes "set (butlast xs) \<subseteq> X"
  assumes "x \<in> set xs" "y \<in> set xs" "x \<noteq> y" "x \<notin> X"
  shows "y \<in> X"
  using assms
  by (induction xs) (auto split: if_splits)

lemma filter_without_hd:
  assumes "v' \<notin> set \<sigma>'"
  assumes "v' # \<sigma>' = filter (\<lambda>v. v \<in> X) \<sigma>"
  shows "\<sigma>' = filter (\<lambda>v. v \<in> X - {v'}) \<sigma>"
  using assms
  by (induction \<sigma>)
     (auto split: if_splits intro: filter_cong)

lemma filter_tl:
  assumes "\<not>P (hd \<sigma>)"
  shows "filter P \<sigma> = filter P (tl \<sigma>)"
  using assms
  by (cases \<sigma>)
      auto

lemma filter_Cons_hd:
  assumes "P (hd xs)"
  assumes "y # ys = filter P xs"
  shows "hd xs = y"
  using assms
  by (auto dest!: Cons_eq_filterD simp: hd_append)

lemma filter_tl_without_hd:
  assumes "v' \<notin> set \<sigma>'"
  assumes "v' # \<sigma>' = filter (\<lambda>v. v \<in> X) \<sigma>"
  shows "\<sigma>' = filter (\<lambda>v. v \<in> X - {v'}) (tl \<sigma>)"
proof -
  from assms have "\<sigma>' = filter (\<lambda>v. v \<in> X - {v'}) \<sigma>"
    by (intro filter_without_hd)

  also from assms have "\<dots> = filter (\<lambda>v. v \<in> X - {v'}) (tl \<sigma>)"
    by (intro filter_tl, cases "hd \<sigma> \<in> X")
       (auto dest: filter_Cons_hd)

  finally show ?thesis .
qed

lemma sorted_list_of_set_image_Cons:
  assumes "finite X" "X \<noteq> {}"
  assumes "\<forall>x \<in> X. f m \<le> f x"
  assumes "m \<in> X"
  assumes "inj_on f X"
  shows "sorted_list_of_set (f ` X) = f m # sorted_list_of_set (f ` (X - {m}))" (is "?L = ?R")
proof -
  have min_fm: "Min (f ` X) = f m"
    using assms
    by (auto intro: Min_eqI)

  have image_Diff: "(f ` X) - {f m} = f ` (X - {m})"
    using assms
    by (simp add: inj_on_image_set_diff)

  have "?L = Min (f ` X) # sorted_list_of_set ((f ` X) - {Min (f ` X)})"
    using assms
    by (simp add: sorted_list_of_set_nonempty)

  also have "\<dots> = ?R"
    by (simp add: min_fm image_Diff)

  finally show ?thesis .
qed

lemma distinct_indexE:
  assumes "distinct xs"
  assumes "t < length xs"
  obtains x where "index xs x = t" "xs ! t = x" "x \<in> set xs"
proof
  from assms index_nth_id show "index xs (xs ! t) = t"
    by blast
next
  from \<open>t < length xs\<close> show "xs ! t \<in> set xs"
    by simp
qed blast

lemma distinct_same_order_list_eq:
  assumes "distinct xs" "distinct xs'"
  assumes "set xs = set xs'"
  assumes "\<forall>x y. index xs x \<le> index xs y \<longleftrightarrow> index xs' x \<le> index xs' y"
  shows "xs = xs'"
  using assms
proof (induction xs xs' rule: list_induct2')
  case (4 x xs x' xs')
  then have "x = x'"
    by (auto split: if_splits)

  from 4 have distinct: "distinct xs" "distinct xs'"
    by simp_all

  from 4 have "\<forall>x y. (index xs x \<le> index xs y) = (index xs' x \<le> index xs' y)"
    by (auto split: if_splits)
       (metis index_conv_size_if_notin index_le_size index_less_size_conv insert_eq_iff linorder_not_le)+

  with 4 distinct \<open>x = x'\<close> show ?case
    by fastforce
qed auto

lemma list_eq_same_order:
  assumes "xs = xs'"
  shows "\<forall>x y. index xs x \<le> index xs y \<longleftrightarrow> index xs' x \<le> index xs' y"
  using assms
  by blast

lemma move_to_filter_eq: "[x <- xs. x \<noteq> v][v \<mapsto> t] = xs[v \<mapsto> t]"
  by (metis filter_id_conv filter_set member_filter move_to_def)

lemma distinct_order_filter_eq:
  assumes "distinct xs" "distinct xs'"
  assumes "set xs = set xs'"
  assumes "\<forall>x y. x \<noteq> v \<and> y \<noteq> v \<longrightarrow> (index xs x \<le> index xs y \<longleftrightarrow> index xs' x \<le> index xs' y)"
  shows "[x <- xs. x \<noteq> v] = [x <- xs'. x \<noteq> v]"
  using assms
proof (intro distinct_same_order_list_eq, goal_cases)
  case 4
  show ?case
  proof (intro allI)
    fix x y

    consider "x = y" | "x = v \<and> x \<noteq> y" | "y = v \<and> x \<noteq> y" | "x \<noteq> y \<and> x \<noteq> v \<and> y \<noteq> v" by blast
    then show "index [x <- xs. x \<noteq> v] x \<le> index [x <- xs. x \<noteq> v] y \<longleftrightarrow> index [x <- xs'. x \<noteq> v] x \<le> index [x <- xs'. x \<noteq> v] y"
    proof cases
      case 2
      with assms(3) show ?thesis
        by auto
           (metis filter_set index_less_size_conv leD leI)+
    next
      case 3
      with assms(3) show ?thesis
        by (auto simp: index_le_size)
    next
      case 4
      with assms show ?thesis
        by (auto simp flip: index_filter_neq)
    qed blast
  qed
qed auto

lemma distinct_filter_eq_order:
  assumes "distinct xs" "distinct xs'"
  assumes "set xs = set xs'"
  assumes "[x <- xs. x \<noteq> v] = [x <- xs'. x \<noteq> v]"
  shows "\<forall>x y. x \<noteq> v \<and> y \<noteq> v \<longrightarrow> (index xs x \<le> index xs y \<longleftrightarrow> index xs' x \<le> index xs' y)"
  using assms
  by auto (metis index_filter_neq)+

lemma distinct_move_to_eq_if:
  assumes "distinct xs" "distinct xs'"
  assumes "set xs = set xs'"
  assumes "v \<in> set xs" "index xs v = t"
  assumes "\<forall>x y. x \<noteq> v \<and> y \<noteq> v \<longrightarrow> (index xs x \<le> index xs y \<longleftrightarrow> index xs' x \<le> index xs' y)"
  shows "xs'[v \<mapsto> t] = xs"
  using assms
  by (smt (verit, ccfv_SIG) distinct_count_in_set distinct_order_filter_eq move_to_def move_to_id)

lemma distinct_move_to_indices_if_eq:
  assumes "xs'[v \<mapsto> t] = xs"
  shows "\<forall>x y. x \<noteq> v \<and> y \<noteq> v \<longrightarrow> (index xs x \<le> index xs y \<longleftrightarrow> index xs' x \<le> index xs' y)"
  by (metis assms move_to_others_leq)

lemma set_take_insert_drop: "set ((take n xs) @ x # (drop n xs)) = {x} \<union> set xs"
  by (induction xs n rule: induct_list_nat)
     (simp_all add: insert_commute)

lemma list_emb_drop_before_first:
  assumes "list_emb P xs (ys@zs)"
  assumes "\<forall>y \<in> set ys. \<not>P (hd xs) y"
  shows "list_emb P xs zs"
  using assms
  by (induction ys; simp)
     (metis list.exhaust_sel list_emb_Cons_iff2 list_emb_Nil)

lemma sorted_strict_last_geq_length_offset:
  assumes "ns \<noteq> []"
  assumes "sorted_wrt (<) ns"
  assumes "h < hd ns"
  shows "length ns + h \<le> last ns"
  using assms
proof (induction ns arbitrary: h)
  case (Cons n ns)
  note cons' = Cons
  show ?case
  proof (cases ns)
    case Nil
    with Cons show ?thesis
      by simp
  next
    case (Cons n' ns')
    with cons' have "Suc h < hd ns" by simp

    with cons' show ?thesis
      by fastforce
  qed
qed simp

lemma sorted_strict_last_geq_length:
  assumes "ns \<noteq> []"
  assumes "sorted_wrt (<) ns"
  assumes "0 < hd ns"
  shows "length ns \<le> last ns"
  using assms
  by (auto dest: sorted_strict_last_geq_length_offset)

end