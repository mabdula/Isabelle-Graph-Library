theory Graph_Quotient_Lifting
  imports Graph_Quotient Blossom_Misc
begin

provenance human

text \<^marker>\<open>provenance ai\<close> \<open>The functions that lift an augmenting path of a quotient graph to the graph. They are the
  functions of the same names of the quotient locale, made executable: the choice of a cycle
  vertex adjacent to a given vertex takes the first such vertex of the cycle list (adjacency is a
  parameter \<open>adj\<close>), and membership of an edge in the matching is tested with its mate function
  (a parameter \<open>mate\<close>). The locale \<open>quot_lift\<close> ties the two parameters to the graph and to the
  matching.\<close>

definition choose_con_vert :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "choose_con_vert adj C v = (case find (adj v) C of Some x \<Rightarrow> x | None \<Rightarrow> hd C)"

definition \<^marker>\<open>provenance ai\<close> last_edge_matched :: "('a \<Rightarrow> 'a option) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "last_edge_matched mate xs = (case rev xs of b # a # _ \<Rightarrow> mate a = Some b | _ \<Rightarrow> True)"

definition stem2vert_path ::
  "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "stem2vert_path adj mate C v =
     (let find_pfx' = (\<lambda>C'. find_pfx ((=) (choose_con_vert adj C v)) C') in
      if last_edge_matched mate (find_pfx' C) then find_pfx' C else find_pfx' (rev C))"

definition \<^marker>\<open>provenance ai\<close> matched_to_cycle :: "('a \<Rightarrow> 'a option) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  "matched_to_cycle mate C x =
     (x \<notin> set C \<and> (case mate x of Some c \<Rightarrow> c \<in> set C | None \<Rightarrow> False))"

definition replace_cycle ::
  "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace_cycle adj mate C p1 p2 =
     (if p1 = [] then stem2vert_path adj mate C (hd p2) @ p2
      else if p2 = [] then stem2vert_path adj mate C (last p1) @ rev p1
      else if \<not> matched_to_cycle mate C (hd p2) then p1 @ stem2vert_path adj mate C (hd p2) @ p2
      else rev p2 @ stem2vert_path adj mate C (last p1) @ rev p1)"

text\<open>A function to find the shortest prefix of a list which has a given vertex.\<close>

fun pref_suf where
  "pref_suf pref v [] = (pref,[])" |
  "pref_suf pref v (a # l) = (if a = v then (pref, l) else pref_suf (pref @  [a]) v l)"

lemma pref_suf_append_1:
  assumes "v \<notin> set pref"
  shows "fst (pref_suf (pref1 @ pref2) v l) = pref1 @ fst (pref_suf pref2 v l)"
  using \<^marker>\<open>provenance ai\<close> assms
proof(induction l arbitrary: pref2)
  case \<^marker>\<open>provenance ai\<close> Nil
  then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?case
    by auto
next \<^marker>\<open>provenance ai\<close>
  case (Cons a' l')
  then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?case 
    by auto
qed \<^marker>\<open>provenance ai\<close>

lemma pref_suf_append_2:
  "snd (pref_suf pref1 v l) = snd (pref_suf pref2 v l)"
proof(induction l arbitrary: pref1 pref2)
  case \<^marker>\<open>provenance ai\<close> Nil
  then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?case
    by auto
next \<^marker>\<open>provenance ai\<close>
  case (Cons a' l')
  then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?case 
    by auto
qed \<^marker>\<open>provenance ai\<close>

lemma pref_suf_works:
  assumes "v \<in> set l"
  shows "l = fst (pref_suf [] v l) @ v # snd (pref_suf [] v l)"
  using \<^marker>\<open>provenance ai\<close> assms
proof(induction l)
  case \<^marker>\<open>provenance ai\<close> Nil
  then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?case
    by auto
next \<^marker>\<open>provenance ai\<close>
  case (Cons a' l')
  show \<^marker>\<open>provenance ai\<close> ?case
  proof \<^marker>\<open>provenance human\<close>(cases "v = a'")
    case \<^marker>\<open>provenance ai\<close> True
    then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?thesis
      by auto
  next \<^marker>\<open>provenance ai\<close>
    case \<^marker>\<open>provenance ai\<close> False
    then \<^marker>\<open>provenance ai\<close> have "l' = fst (pref_suf [] v l') @ v # snd (pref_suf [] v l')"
      using \<^marker>\<open>provenance ai\<close> Cons
      by \<^marker>\<open>provenance ai\<close> auto
    moreover \<^marker>\<open>provenance ai\<close> have "fst (pref_suf ([a'] @ []) v l') = [a'] @ fst (pref_suf [] v l')"
      using \<^marker>\<open>provenance ai\<close> False
      by \<^marker>\<open>provenance ai\<close> (intro pref_suf_append_1[where pref = "[a']"]) auto
    moreover \<^marker>\<open>provenance ai\<close> have "snd (pref_suf [] v l') = snd (pref_suf l'' v l')" for l''
      using pref_suf_append_2
      by \<^marker>\<open>provenance ai\<close> force
    ultimately \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?thesis
      using False
      by (auto simp: pref_suf_append_2[of "[a']" v l' "[]"])
  qed \<^marker>\<open>provenance ai\<close>
qed \<^marker>\<open>provenance ai\<close>

definition refine ::
  "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "refine adj mate u C p =
     (if u \<in> set p then replace_cycle adj mate C (fst (pref_suf [] u p)) (snd (pref_suf [] u p))
      else p)"

lemmas \<^marker>\<open>provenance ai\<close> [code] = choose_con_vert_def last_edge_matched_def stem2vert_path_def matched_to_cycle_def
  replace_cycle_def refine_def

lemma \<^marker>\<open>provenance ai\<close> last_edges_of_path_snoc2: "last (edges_of_path (ys @ [a, b])) = {a, b}"
proof-
  have "\<exists>es. edges_of_path (ys @ [a, b]) = es @ [{a, b}]"
  proof(induction ys)
    case Nil
    then show ?case
      by simp
  next
    case (Cons x ys)
    then obtain es where es: "edges_of_path (ys @ [a, b]) = es @ [{a, b}]"
      by blast
    show ?case
    proof(cases ys)
      case Nil
      then show ?thesis
        by simp
    next
      case (Cons y ys')
      then show ?thesis
        using es
        by (intro exI[of _ "{x, y} # es"]) simp
    qed
  qed
  thus ?thesis
    by auto
qed

locale \<^marker>\<open>provenance ai\<close> quot_lift = quot E s u for E :: "'a set set" and s u +
  fixes adj :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and mate :: "'a \<Rightarrow> 'a option" and M :: "'a set set"
    and C :: "'a list"
  assumes adj_E: "\<And>v w. adj v w \<longleftrightarrow> {v, w} \<in> E"
      and mate_M: "\<And>v w. mate v = Some w \<longleftrightarrow> {v, w} \<in> M"
      and M_subset_E: "M \<subseteq> E"
      and s_cycle: "s = Vs E - set C"
      and u_fresh: "u \<notin> Vs E"
      and hd_last_cycle: "hd C = last C"
begin

lemma \<^marker>\<open>provenance ai\<close> choose_con_vert_props:
  assumes "\<exists>x \<in> set C. {v, x} \<in> E"
  shows "choose_con_vert adj C v \<in> set C" "{v, choose_con_vert adj C v} \<in> E"
proof-
  have "find (adj v) C \<noteq> None"
    using assms adj_E
    by (auto simp: find_None_iff)
  then obtain x where x: "find (adj v) C = Some x"
    by blast
  hence "x \<in> set C" "adj v x"
    by (auto simp: find_Some_iff intro: nth_mem)
  thus "choose_con_vert adj C v \<in> set C" "{v, choose_con_vert adj C v} \<in> E"
    using x adj_E
    by (auto simp: choose_con_vert_def)
qed

lemma \<^marker>\<open>provenance ai\<close> last_edge_matched_iff:
  "2 \<le> length xs \<Longrightarrow> last_edge_matched mate xs \<longleftrightarrow> last (edges_of_path xs) \<in> M"
proof-
  assume len: "2 \<le> length xs"
  obtain ys a b where xs: "xs = ys @ [a, b]"
  proof-
    obtain b ys' where 1: "xs = ys' @ [b]" "Suc 0 \<le> length ys'"
      using Suc_le_length_iff_snoc2[of "Suc 0" xs] len
      by auto
    obtain a ys where "ys' = ys @ [a]"
      using Suc_le_length_iff_snoc2[of 0 ys'] 1(2)
      by auto
    thus ?thesis
      using that 1(1)
      by simp
  qed
  have "last (edges_of_path xs) = {a, b}"
    by (simp add: xs last_edges_of_path_snoc2)
  moreover have "last_edge_matched mate xs \<longleftrightarrow> mate a = Some b"
    by (simp add: last_edge_matched_def xs)
  ultimately show ?thesis
    by (simp add: mate_M)
qed

lemma \<^marker>\<open>provenance ai\<close> matched_to_cycle_iff:
  "matched_to_cycle mate C x \<longleftrightarrow> {u, x} \<in> quotG M"
proof
  assume m: "matched_to_cycle mate C x"
  then obtain c where c: "x \<notin> set C" "mate x = Some c" "c \<in> set C"
    by (auto simp: matched_to_cycle_def split: option.splits)
  have xc: "{x, c} \<in> M"
    using c(2)
    by (simp add: mate_M)
  hence "x \<in> Vs E"
    using M_subset_E
    by (auto simp: Vs_def)
  hence "x \<noteq> u"
    using u_fresh
    by auto
  have "P ` {x, c} = {x, u}"
    using c(1,3) \<open>x \<in> Vs E\<close> s_cycle
    by auto
  thus "{u, x} \<in> quotG M"
    using xc \<open>x \<noteq> u\<close>
    by (auto simp: quot_graph_def insert_commute doubleton_eq_iff intro!: bexI[of _ "{x, c}"])
next
  assume "{u, x} \<in> quotG M"
  then obtain e where e: "e \<in> M" "{u, x} = P ` e" "{u, x} \<noteq> {u}"
    by (simp only: Diff_iff quot_graph_def mem_Collect_eq singleton_iff) blast
  obtain a b where ab: "e = {a, b}" "mate a = Some b"
    using e(1) M_subset_E dblton_E
    by (auto simp: mate_M elim!: dblton_graphE)
  have "a \<in> Vs E" "b \<in> Vs E"
    using e(1) ab(1) M_subset_E
    by (auto simp: Vs_def)
  have "x \<noteq> u"
    using e(3)
    by auto
  show "matched_to_cycle mate C x"
  proof(cases "a \<in> set C")
    case True
    hence "b \<notin> set C" "x = b"
      using e(2) ab(1) \<open>x \<noteq> u\<close> \<open>b \<in> Vs E\<close> s_cycle
      by (auto simp: doubleton_eq_iff split: if_splits)
    moreover have "mate b = Some a"
      using ab(2)
      by (simp add: mate_M insert_commute)
    ultimately show ?thesis
      using True
      by (simp add: matched_to_cycle_def)
  next
    case False
    have Pa: "P a = a"
      using False \<open>a \<in> Vs E\<close> s_cycle
      by simp
    have eq: "{u, x} = {a, P b}"
      using e(2) ab(1)
      by (simp only: image_insert image_empty Pa)
    have "b \<in> set C"
    proof(rule ccontr)
      assume "b \<notin> set C"
      hence "P b = b"
        using \<open>b \<in> Vs E\<close> s_cycle
        by simp
      hence "u \<in> {a, b}"
        using eq
        by auto
      thus False
        using \<open>a \<in> Vs E\<close> \<open>b \<in> Vs E\<close> u_fresh
        by auto
    qed
    moreover have "x = a"
      using eq \<open>b \<in> set C\<close> \<open>x \<noteq> u\<close> s_cycle u_fresh \<open>b \<in> Vs E\<close>
      by (auto simp: doubleton_eq_iff)
    ultimately show ?thesis
      using False ab(2)
      by (simp add: matched_to_cycle_def)
  qed
qed

text \<^marker>\<open>provenance ai\<close> \<open>In the locale, the lifting functions satisfy the defining equations of their
  counterparts in the original formalisation, in which membership in the matching is tested
  directly.\<close>

lemma stem2vert_path_def':
  "stem2vert_path adj mate C v =
     (let find_pfx' = (\<lambda>C'. find_pfx ((=) (choose_con_vert adj C v)) C') in
      if last (edges_of_path (find_pfx' C)) \<in> M then find_pfx' C else find_pfx' (rev C))"
proof \<^marker>\<open>provenance ai\<close>-
  define \<^marker>\<open>provenance human\<close> w where "w = choose_con_vert adj C v"
  define \<^marker>\<open>provenance human\<close> pfx where "pfx = find_pfx ((=) w) C"
  have \<^marker>\<open>provenance human\<close> pfx_rev: "find_pfx ((=) w) (rev C) = pfx" if "length pfx < 2"
  proof \<^marker>\<open>provenance ai\<close>(cases C)
    case Nil
    then show ?thesis
      by (simp add: pfx_def)
  next
    case (Cons c cs)
    have "hd (rev C) = c"
    proof-
      have \<^marker>\<open>provenance human\<close> "hd (rev C) = last C"
        by \<^marker>\<open>provenance ai\<close> (rule hd_rev)
      also have "\<dots> = hd C"
        using hd_last_cycle
        by simp
      also have "\<dots> = c"
        using Cons
        by simp
      finally show ?thesis .
    qed
    then obtain ds where rev_C: "rev C = c # ds"
      using Cons
      by (cases "rev C") auto
    show ?thesis
    proof(cases "w = c")
      case True
      then show ?thesis
        using Cons rev_C
        by (simp add: pfx_def)
    next
      case False
      have "cs = []"
        using that False Cons
        by \<^marker>\<open>provenance human\<close> (cases cs) (auto simp: pfx_def split: if_splits)
      then show ?thesis
        using Cons False
        by (simp add: pfx_def)
    qed
  qed
  show ?thesis
  proof \<^marker>\<open>provenance human\<close>(cases "2 \<le> length pfx")
    case \<^marker>\<open>provenance ai\<close> True
    then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?thesis
      by \<^marker>\<open>provenance human\<close> (simp add: stem2vert_path_def Let_def w_def[symmetric] pfx_def[symmetric]
                    last_edge_matched_iff)
  next \<^marker>\<open>provenance ai\<close>
    case \<^marker>\<open>provenance ai\<close> False
    hence \<^marker>\<open>provenance ai\<close> "last_edge_matched mate pfx"
      by \<^marker>\<open>provenance human\<close> (cases pfx rule: rev_cases) (auto simp: last_edge_matched_def length_Suc_conv Suc_le_eq)
    then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?thesis
      using pfx_rev False
      by \<^marker>\<open>provenance human\<close> (simp add: stem2vert_path_def Let_def w_def[symmetric] pfx_def[symmetric])
  qed \<^marker>\<open>provenance ai\<close>
qed

lemma replace_cycle_def':
  "replace_cycle adj mate C p1 p2 =
     (let stem2p2 = stem2vert_path adj mate C (hd p2);
          p12stem = stem2vert_path adj mate C (last p1) in
      if p1 = [] then stem2p2 @ p2
      else (if p2 = [] then p12stem @ (rev p1)
            else (if {u, hd p2} \<notin> quotG M then p1 @ stem2p2 @ p2
                  else (rev p2) @ p12stem @ (rev p1))))"
  by (simp add: replace_cycle_def matched_to_cycle_iff Let_def)
end \<^marker>\<open>provenance ai\<close>

context quot_lift
begin

subsubsection \<open>Choosing a neighbour from a given set\<close>

lemma choose_vert_works_1:
  assumes cycle: "distinct (tl C)" and
    quot_aug_path: "p' = (p1 @ u # p2)" "distinct p'" "path (quotG E) p'" "p2 \<noteq> []" and 
    quot: "s = (Vs E) - set C" (*and
    graph: "dblton_graph E"*)
shows "(choose_con_vert adj C (hd p2)) \<in> set C \<and> {hd p2, (choose_con_vert adj C (hd p2))} \<in> E"
  using assms
proof-
  have *: "\<exists>w. {hd p2, w} \<in> E \<and> w \<notin> s"
    using quot_aug_path path_adj_verts_edge edge_in_quot_in_graph_2''
    by \<^marker>\<open>provenance ai\<close> (fastforce intro!: edge_in_quotG_2'_doubleton[where M = E] simp: neq_Nil_conv)
  then obtain w where "w \<in> neighbourhood E (hd p2)" "w \<notin> s"
    by (auto simp: neighbourhood_def insert_commute)
  moreover hence "w \<in> set C"
    using edges_are_Vs quot insert_absorb
    by auto 
  ultimately have "\<exists>x \<in> set C. {hd p2, x} \<in> E"
    by (auto simp: neighbourhood_def insert_commute)
  thus ?thesis
    using choose_con_vert_props
    by \<^marker>\<open>provenance ai\<close> blast
qed

lemma choose_vert_works_2:
  assumes cycle: "distinct (tl C)" and
    quot_aug_path: "p' = (p1 @ u # p2)" "distinct p'" "path (quotG E) p'" "p1 \<noteq> []" and 
    quot: "s = (Vs E) - set C" and
    graph: "\<forall>e\<in>E. \<exists>u v. e = {u, v} \<and> u \<noteq> v"
shows "(choose_con_vert adj C (last p1)) \<in> set C \<and> {last p1, (choose_con_vert adj C (last p1))} \<in> E"
  using assms
proof-
  have *: "\<exists>w. {last p1, w} \<in> E \<and> w \<notin> s"
    using quot_aug_path path_adj_verts_edge edge_in_quot_in_graph_2''
    by \<^marker>\<open>provenance ai\<close> (fastforce intro!: edge_in_quotG_2'_doubleton[where M = E] simp: neq_Nil_conv_2 insert_commute)
  then obtain w where "w \<in> neighbourhood E (last p1)" "w \<notin> s"
    by (auto simp: neighbourhood_def insert_commute)
  moreover hence "w \<in> set C"
    using edges_are_Vs quot insert_absorb
    by auto 
  ultimately have "\<exists>x \<in> set C. {last p1, x} \<in> E"
    by (auto simp: neighbourhood_def insert_commute)
  thus ?thesis
    using choose_con_vert_props
    by \<^marker>\<open>provenance ai\<close> blast
qed \<^marker>\<open>provenance ai\<close>

lemma choose_vert_works_3:
  assumes "distinct (tl C)" "distinct (u # p2)" "path (quotG E) (u # p2)" "p2 \<noteq> []"
    "s = (Vs E) - set C"
  shows "(choose_con_vert adj C (hd p2)) \<in> set C" "{hd p2, (choose_con_vert adj C (hd p2))} \<in> E"
proof \<^marker>\<open>provenance ai\<close>-
  have \<^marker>\<open>provenance human\<close> "choose_con_vert adj C (hd p2) \<in> set C \<and> {hd p2, choose_con_vert adj C (hd p2)} \<in> E"
    by \<^marker>\<open>provenance ai\<close> (rule choose_vert_works_1[OF assms(1) _ assms(2,3,4,5), of "[]"]) simp
  thus "choose_con_vert adj C (hd p2) \<in> set C" "{hd p2, (choose_con_vert adj C (hd p2))} \<in> E"
    by simp_all
qed \<^marker>\<open>provenance human\<close>

subsubsection \<open>Finding an Edge in the Concrete Graph\<close>

text\<open>A function to choose a vertex in the concrete graph connected to a vertex in the quotient graph,
     if the vertex in the quotient graph is connected to the contracted odd cycle.\<close>

lemma find_pfx_subset:
  "set (find_pfx Q l) \<subseteq> set l"
  by \<^marker>\<open>provenance ai\<close> (induction l) auto

lemma stem2vert_path_subset:
  "set (stem2vert_path adj mate C v) \<subseteq> (set C)"
  using find_pfx_subset
  by (simp add: stem2vert_path_def' Let_def; fastforce)

lemma hd_find_pfx: "l \<noteq> [] \<Longrightarrow> hd (find_pfx Q l) = hd l"
  by \<^marker>\<open>provenance ai\<close> (cases l) simp_all

lemma hd_stem2vert_path:
  "C \<noteq> [] \<Longrightarrow> (hd (stem2vert_path adj mate C a2') = hd C \<or> hd (stem2vert_path adj mate C a2') = last C)"
  by (auto simp: stem2vert_path_def' Let_def hd_find_pfx hd_rev)

lemma hd_stem2vert_nempty:
  "C \<noteq> [] \<Longrightarrow> ((stem2vert_path adj mate C a2') \<noteq> [])"
  unfolding stem2vert_path_def' Let_def
  by (cases "rev C"; cases C) auto

subsubsection \<open>Lifting the Path\<close>

text\<open>A function to lift an augmenting path from a quotient to a concrete graph. It does so by
     replacing the contracted odd cycle with a subpath of the cycle that correctly matches the
     polarity of the edges connected to the odd cycle.\<close> 

end

lemma len_find_pfx:
  assumes "l \<noteq> []"
  shows "length (find_pfx Q l) \<ge> 1"
  using assms
proof(induction l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    by simp
qed

context quot_lift
begin

lemma length_replace_cycle:
  assumes "C \<noteq> []" "p1 \<noteq> [] \<or> p2 \<noteq> []"
  shows "length (replace_cycle adj mate C p1 p2) \<ge> length p1 + length p2 + 1"
proof(cases p1)
  case nil1: Nil
  show ?thesis
  proof(cases p2)
    case nil2: Nil
    then show ?thesis
      using nil1 assms
      by(simp add: replace_cycle_def' split: if_splits)
  next
    case cons2: (Cons a1' p1')
    then show ?thesis
      using nil1 assms len_find_pfx
      by (auto simp add: replace_cycle_def' stem2vert_path_def' Let_def split: if_splits)
  qed
next
  case cons1: (Cons a1' p1')
  show ?thesis
  proof(cases p2)
    case nil2: Nil
    then show ?thesis
      using cons1 assms len_find_pfx
      by (auto simp add: replace_cycle_def' stem2vert_path_def' Let_def split: if_splits)
  next
    case cons2: (Cons a list)
    then show ?thesis
      using cons1 assms len_find_pfx
      by (auto simp add: replace_cycle_def' stem2vert_path_def' Let_def split: if_splits)
  qed
qed

end

lemma in_aug_path_in_Vs:
  assumes "matching_augmenting_path M p" "v \<in> set p" "v \<noteq> hd p" "v \<noteq> last p" "p \<noteq> []"
  shows "v \<in> Vs M"
  using alt_path_vert_is_matched'[OF matching_augmenting_path_feats(2)[OF assms(1)] assms(2-5)]
  .

context quot_lift
begin

lemma alt_list_quotG_then_alt_list_1:
  assumes "set p \<subseteq> s" "alt_path (quotG M) p" \<open>M \<subseteq> E\<close>
  shows "alt_path M p"
  using assms(1,3) edge_of_path_in_graph_iff_in_quot
  by (intro alt_list_cong[OF assms(2)] ballI) blast+

lemma alt_list_quotG_then_alt_list_2:
  assumes "set p \<subseteq> s" "alt_list (\<lambda>e. e \<in> (quotG M)) (\<lambda>e. e \<notin> (quotG M)) (edges_of_path p)" "M \<subseteq> E"
  shows "alt_list (\<lambda>e. e : M) (\<lambda>e. e \<notin> M) (edges_of_path p)"
  using assms(1,3) edge_of_path_in_graph_iff_in_quot
  by (intro alt_list_cong[OF assms(2)] ballI) blast+

end

lemma odd_cycle_rev:
  assumes "odd_cycle C"
  shows "odd_cycle (rev C)"
  using assms
  by (auto split: if_splits simp: hd_rev last_rev Suc_le_length_iff numeral_3_eq_3 odd_cycle_def)

lemma odd_cycle_rev_alt_list:
  assumes "odd_cycle C" "alt_path M C"
  shows "alt_path M (rev C)"
  using odd_cycleD(1)[OF assms(1)]
                 
        even_alt_path_rev[OF odd_cycle_even_verts[OF assms(1)] _ assms(2)]
  by (simp add: even_alt_path_rev assms(2))

text\<open>showing that given an augmenting path, "replace cycle" produces an augmeting path.\<close>

context quot_lift
begin

lemma inBetinM:
  assumes cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)" and
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"  and
    (*graph: "dblton_graph E" and*)
    p1_nempty[simp]: "p1 \<noteq> []" and 
    p1_subset_s[simp]: "set p1 \<subseteq> s" and
    inM: "{last p1, u} \<in> quotG M"
  shows "{last p1, hd (stem2vert_path adj mate C (hd p2))} \<in> M"
proof-
  have "dblton_graph M"
    using graph subsetD[OF matching(2)]
    by \<^marker>\<open>provenance ai\<close> auto
  show "{last p1, hd (stem2vert_path adj mate C (hd p2))} \<in> M"
  proof-
    have "last p1 \<in> s"
      using p1_subset_s p1_nempty
      by fastforce
    have *: "\<exists>w. {last p1, w} \<in> M \<and> w \<notin> s"
      using \<^marker>\<open>provenance ai\<close> inM[unfolded insert_commute[of "last p1" u]] \<open>last p1 \<in> s\<close> \<open>M \<subseteq> E\<close>
      by (rule edge_in_quotG_2'_doubleton)
    then obtain vC where vC: "{last p1, vC} \<in> M "" vC \<notin> s"
      by auto
    moreover have vCinC: "vC \<in> set C"
      using quot(1) vC matching(2)
      unfolding Vs_def
      by auto
    have "vC = last C"
    proof(rule ccontr)
      assume ass: "vC \<noteq> last C"
      then have "vC \<noteq> hd C"
        using odd_cycleD(3)[OF cycle(1)]
        by auto
      have "C \<noteq> []"
        using vCinC
        by auto
      obtain e where e: "e \<in> set (edges_of_path C)" "vC \<in> e" "e \<in> M"
        using alt_path_vert_is_matched[OF cycle(2) vCinC \<open>vC \<noteq> hd C\<close> ass(1) \<open>C \<noteq> []\<close>]
        by auto
      moreover have "e \<noteq> {last p1, vC}"
        using p1_subset_s quot(1) e(1) v_in_edge_in_path \<open>last p1 \<in> s\<close>
        by fastforce
      ultimately show False
        using vC(1) matching(1) edges_are_Vs
        unfolding matching_def2
        by \<^marker>\<open>provenance ai\<close> auto
    qed
    moreover have "hd (stem2vert_path adj mate C (hd p2)) = last C"
      using hd_stem2vert_path[OF odd_cycle_nempty[OF cycle(1)]] odd_cycleD[OF cycle(1)]
      by auto
    ultimately show ?thesis
      using vC
      by auto
  qed
qed

lemma rw3:"(edges_of_path (p1 @ u # p2)) = ((edges_of_path (p1 @ [u]))  @ (edges_of_path (u # p2)))" for p1 p2
  using edges_of_path_append_2
  by fastforce

lemma rw4:
  fixes p1 p2::"'a list"
  assumes p1_nempty: "p1 \<noteq> []"
  assumes p2_nempty: "p2 \<noteq> []"
  shows "(edges_of_path (p1 @ u # p2)) = ((edges_of_path p1) @ {last p1, u} # {u, hd p2} # (edges_of_path p2))"
    proof-
      have "p1 = (butlast p1) @ [last p1]"
        using p1_nempty 
        by simp
      moreover have "p2 = hd p2 # (tl p2)"
        using p2_nempty 
        by simp
      show ?thesis
        using p1_nempty p2_nempty
        by (cases p2) (auto simp: edges_of_path_append_3)
    qed

lemma rw5:
  fixes p1 p2::"'a list"
  assumes len_ge_2: "length p1 \<ge> 2"
  shows "edges_of_path (p1 @ u # p2) = ((edges_of_path (butlast p1)) @ {last (butlast p1), last p1} # {last p1, u} # (edges_of_path (u # p2)))"
proof-
  have p1_nempty: "p1 \<noteq> []"
    using assms
    by auto
  show ?thesis 
  proof-
    have butlast: "p = (butlast p) @ [last p]" if "p \<noteq> []" for p::"'a list"
      using that
      by simp
    have butlast_nempty: "butlast p1 \<noteq> []"
      using len_ge_2
      by (cases p1 rule: rev_cases) auto
    have e1: "edges_of_path p1 = edges_of_path (butlast p1) @ [{last (butlast p1), last p1}]"
      using \<^marker>\<open>provenance ai\<close> edges_of_path_snoc[OF butlast_nempty, of "last p1"]
      by (auto simp: append_butlast_last_id[OF p1_nempty])
    show ?thesis
      unfolding rw3[of p1 p2] edges_of_path_snoc[OF p1_nempty, symmetric]
      by \<^marker>\<open>provenance ai\<close> (simp add: e1)
  qed
qed

lemma empty_rev_imp: "C \<noteq> [] \<Longrightarrow> rev C \<noteq> []"
  by simp

lemma stem2vert_path_append_1:
  "last (edges_of_path (find_pfx ((=) (choose_con_vert adj C a2')) C)) \<in> M 
   \<Longrightarrow> \<exists>Ctail. C = (stem2vert_path adj mate C a2') @ Ctail"
  unfolding stem2vert_path_def'
  by (auto split: if_splits intro: find_pfx_append_2)

lemma stem2vert_path_append_2:
  assumes "(choose_con_vert adj C a2') = last C" and "odd_cycle C"
  shows "\<exists>Ctail. C = (stem2vert_path adj mate C a2') @ Ctail"
proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert adj C a2')) C)) \<in> M")
  case True
  then show ?thesis
    by(intro stem2vert_path_append_1)
next
  have "choose_con_vert adj C a2' = hd C \<Longrightarrow> 
                    (find_pfx ((=) (choose_con_vert adj C a2')) C) = [hd C]"
    using odd_cycle_nempty[OF \<open>odd_cycle C\<close>]
    by (auto simp: neq_Nil_conv)
  moreover have "find_pfx ((=) (last C)) (rev C) = [last C]" if "C \<noteq> []"
    using empty_rev_imp[OF that, unfolded neq_Nil_conv]
    by auto
  moreover case False
  ultimately show ?thesis
    using assms(1)
    by (cases "C = []")
        (unfold stem2vert_path_def' Let_def,
         auto split: if_splits simp: neq_Nil_conv odd_cycleD(3)[OF \<open>odd_cycle C\<close>, symmetric])
qed

lemma find_pfx_sing: "find_pfx Q l = [x] \<Longrightarrow> x = hd l"
  by(cases "l"; auto split: if_splits)

lemma find_pfx_hd: "l \<noteq> [] \<Longrightarrow> Q (hd l) \<Longrightarrow> find_pfx Q l = [hd l]"
  by \<^marker>\<open>provenance ai\<close> (cases l) simp_all

lemma \<^marker>\<open>provenance ai\<close> stem2vert_path_eq_pfx:
  assumes "C \<noteq> []"
    "last (edges_of_path (find_pfx ((=) (choose_con_vert adj C v)) C)) \<in> M \<or> choose_con_vert adj C v = last C"
  shows "stem2vert_path adj mate C v = find_pfx ((=) (choose_con_vert adj C v)) C"
proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert adj C v)) C)) \<in> M")
  case True
  then show ?thesis
    by (simp add: stem2vert_path_def' Let_def)
next
  case False
  hence w: "choose_con_vert adj C v = hd C"
    using assms(2) hd_last_cycle
    by simp
  have "find_pfx ((=) (choose_con_vert adj C v)) C = [hd C]"
    using w assms(1)
    by (intro find_pfx_hd) simp_all
  moreover have "find_pfx ((=) (choose_con_vert adj C v)) (rev C) = [hd C]"
    using w assms(1) hd_last_cycle
    by (simp add: find_pfx_hd[of "rev C"] hd_rev)
  ultimately show ?thesis
    by (simp add: stem2vert_path_def' Let_def)
qed

lemma alt_list_replace_cycle:
  assumes cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)" and
    quot_aug_path: "p' = (p1 @ u # p2)" "graph_augmenting_path (quotG E) (quotG M) p'" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C" "set C \<subseteq> Vs E"(* and
    graph: "dblton_graph E"*)
  shows "alt_path M (replace_cycle adj mate C p1 p2)"
proof-

  have \<^marker>\<open>provenance ai\<close> d1: "\<And>C p2 chv. p2 \<noteq> [] \<Longrightarrow> alt_path (quotG M) (u # p2) \<Longrightarrow> distinct (u # p2) \<Longrightarrow>
      path (quotG E) (u # p2) \<Longrightarrow> set p2 \<subseteq> s \<Longrightarrow> odd_cycle C \<Longrightarrow> alt_path M C \<Longrightarrow>
      distinct (tl C) \<Longrightarrow> s = Vs E - set C \<Longrightarrow> chv \<in> set C \<Longrightarrow> {hd p2, chv} \<in> E \<Longrightarrow>
      last (edges_of_path (find_pfx ((=) chv) C)) \<in> M \<or> chv = last C \<Longrightarrow>
      alt_path M (find_pfx ((=) chv) C @ p2)"
  proof-
    fix \<^marker>\<open>provenance human\<close> C fix \<^marker>\<open>provenance human\<close> p1 p2::"'a list"
    fix chv
    assume \<^marker>\<open>provenance human\<close> "p2 \<noteq> []"
    define \<^marker>\<open>provenance human\<close> a2' where "a2' = hd p2"
    define \<^marker>\<open>provenance human\<close> p2' where "p2' = tl p2"
    have \<^marker>\<open>provenance human\<close> Cons: "p2 = a2' # p2'"
      unfolding a2'_def p2'_def
      using \<open>p2 \<noteq> []\<close>
      by auto
    assume \<^marker>\<open>provenance human\<close> quot_aug_path: "alt_path (quotG M) (u # p2)" "distinct (u # p2)" "path (quotG E) (u # p2)"
    assume \<^marker>\<open>provenance human\<close> p2_subset_s: "set p2 \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)"
    have \<^marker>\<open>provenance human\<close> "C \<noteq> []"
      using odd_cycle_nempty(1)[OF cycle(1)] .
    then \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "hd C = hd (rev C)"
      using odd_cycleD(3)[OF cycle(1)] 
      by (simp add: hd_rev)
    assume \<^marker>\<open>provenance human\<close> quot: "s = (Vs E) - set C"
    assume \<^marker>\<open>provenance human\<close> choose_vert_works: "chv \<in> set C" "{a2', chv} \<in> E"
    assume \<^marker>\<open>provenance human\<close> True: "last (edges_of_path (find_pfx ((=) chv) C)) \<in> M \<or> chv = last C"
    have \<^marker>\<open>provenance human\<close> "last (find_pfx ((=) chv) C) = chv"
      using find_pfx_works_1[OF choose_vert_works(1), of "(=) chv"]
      by \<^marker>\<open>provenance ai\<close> simp
    moreover have \<^marker>\<open>provenance human\<close> "find_pfx ((=) chv) C \<noteq> []"
      by (rule find_pfx_nempty[OF choose_vert_works(1)]) simp
    ultimately obtain \<^marker>\<open>provenance human\<close> chp where chp: "find_pfx ((=) chv) C = chp @ [chv]"
      by (intro that[of "butlast (find_pfx ((=) chv) C)"]) (simp add: snoc_eq_iff_butlast')
    have \<^marker>\<open>provenance human\<close> alt_list_p2: "\<And>chp. last (edges_of_path (chp @ [chv])) \<in> M \<and> chp \<noteq> [] \<or> chv = last C \<Longrightarrow>
        set (chp @ [chv]) \<subseteq> set C \<Longrightarrow> alt_path M (chv # a2' # p2')"
    proof \<^marker>\<open>provenance ai\<close>-
      fix \<^marker>\<open>provenance human\<close> chp
      assume \<^marker>\<open>provenance human\<close> ass: "(last (edges_of_path (chp @ [chv])) \<in> M \<and> chp \<noteq> []) \<or> chv = last C" "set (chp @ [chv]) \<subseteq> set C"
      have \<^marker>\<open>provenance human\<close> chva2': "{chv, a2'} \<notin> M"
      proof(cases "chv = last C")
        case T2: True
        then show ?thesis
        proof \<^marker>\<open>provenance ai\<close>-
          have \<^marker>\<open>provenance human\<close> "{u, a2'} \<notin> quotG M"
            using quot_aug_path(1) Cons
            by (simp add: alt_list_step)
          have "a2' \<in> s"
            using p2_subset_s Cons
            by simp
          have "chv \<notin> s"
            using \<^marker>\<open>provenance human\<close> quot choose_vert_works(1)
            by simp
          have \<^marker>\<open>provenance human\<close> eq: "P ` {chv, a2'} = {u, a2'}"
            using \<^marker>\<open>provenance ai\<close> \<open>a2' \<in> s\<close> \<open>chv \<notin> s\<close>
            by \<^marker>\<open>provenance ai\<close> simp
          show ?thesis
          proof
            assume \<^marker>\<open>provenance human\<close> "{chv, a2'} \<in> M"
            hence "P ` {chv, a2'} \<in> quot_graph P M"
              by \<^marker>\<open>provenance human\<close> (rule edge_in_graph_in_quot)
            hence "{u, a2'} \<in> quot_graph P M"
              unfolding eq .
            moreover have \<^marker>\<open>provenance human\<close> "{u, a2'} \<noteq> {u}"
              using \<open>a2' \<in> s\<close> good_quot_map(1)
              by \<^marker>\<open>provenance ai\<close> auto
            ultimately show False
              using \<open>{u, a2'} \<notin> quotG M\<close>
              by simp
          qed
        qed
      next
        case F2: False
        then have True: "last (edges_of_path (chp @ [chv])) \<in> M"
          using ass(1)
          by auto
        have "a2' \<notin> last (edges_of_path (chp @ [chv]))"
        proof(rule ccontr; simp)
          assume "a2' \<in> last (edges_of_path (chp @ [chv]))"
          then have "a2' \<in> set (chp @ [chv])"
            using ass(1) F2 edges_of_path_append_3
            by \<^marker>\<open>provenance ai\<close> fastforce
          then show False
            using ass(2) Cons p2_subset_s quot
            by \<^marker>\<open>provenance ai\<close> auto
        qed
        then have "last (edges_of_path (chp @ [chv])) \<noteq> {chv, a2'}"
          by auto
        moreover have "last (chp @ [chv]) = chv "
          by simp
        moreover have "last (chp @ [chv]) \<in> last (edges_of_path (chp @ [chv]))"
          by (rule last_v_in_last_e; use F2 ass(1) not_less_eq_eq in auto)
        ultimately show ?thesis
          using matching(1) True
          unfolding matching_def2
          by \<^marker>\<open>provenance ai\<close> blast
      qed
      then \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> "alt_path M (chv # a2' # p2')"
      proof(simp add: alt_list_step, intro alt_list_quotG_then_alt_list_2, goal_cases)
        case \<^marker>\<open>provenance ai\<close> 1
        show \<^marker>\<open>provenance ai\<close> ?case
          using \<^marker>\<open>provenance human\<close> Cons quot_aug_path(1) p2_subset_s
          by \<^marker>\<open>provenance human\<close> blast
      next \<^marker>\<open>provenance ai\<close>
        case \<^marker>\<open>provenance ai\<close> 2
        have "alt_path (quotG M) (u # a2' # p2') \<or>
                     alt_list (\<lambda>e. e \<in> quotG M) (\<lambda>e. e \<notin> quotG M) (edges_of_path (u # a2' # p2'))"
          by (rule conjunct2[OF alt_list_append_1[where ?l1.0 = "[]"]];
              use Cons quot_aug_path(1,2) in simp)
        moreover have "{u, a2'} \<notin> quotG M"
          using quot_aug_path(1,2) Cons
          by (simp add: alt_list_step)
        ultimately have "alt_path (quotG M) (u # a2' # p2')"
          by(auto simp add: alt_list_step)
        thus \<^marker>\<open>provenance ai\<close> ?case
          by \<^marker>\<open>provenance human\<close>(auto simp add: alt_list_step)
      next \<^marker>\<open>provenance ai\<close>
        case \<^marker>\<open>provenance ai\<close> 3
        show \<^marker>\<open>provenance ai\<close> ?case
          using \<^marker>\<open>provenance human\<close> \<open>M \<subseteq> E\<close> . \<^marker>\<open>provenance human\<close>
      qed \<^marker>\<open>provenance ai\<close>
    qed
    have \<^marker>\<open>provenance human\<close> e_of_p_chp: "(edges_of_path (chp @ [chv, a2'])) = edges_of_path(chp @ [chv]) @ edges_of_path ([chv, a2'])"
      using edges_of_path_append_2
      by (simp add: edges_of_path_snoc_2)
    obtain \<^marker>\<open>provenance human\<close> Ctail where Ctail: "C = find_pfx ((=) chv) C @ Ctail"
      using \<^marker>\<open>provenance ai\<close> find_pfx_append_2
      by blast
    then \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "edges_of_path C = edges_of_path(chp @ [chv]) @ edges_of_path (chv # Ctail)"
      using edges_of_path_append_2 chp
      by fastforce
    then \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> alt_list_chp_chv: "alt_path M (chp @ [chv])"
      using cycle(2) alt_list_append_1
      by force
    moreover \<^marker>\<open>provenance human\<close> have \<^marker>\<open>provenance human\<close> "alt_path M (chp @ ([chv] @ [a2'] @ p2'))"
    proof-
      have "find_pfx ((=) chv) C = [chv] \<Longrightarrow> chv = hd C"
        by (rule find_pfx_sing)
      then have "chp = [] \<Longrightarrow> last (edges_of_path (chp @ [chv])) \<in> M \<and> chp \<noteq> [] \<or> chv = hd C"
        using chp
        by \<^marker>\<open>provenance ai\<close> simp
      moreover have "chp \<noteq> [] \<Longrightarrow> last (edges_of_path (chp @ [chv])) \<in> M \<and> chp \<noteq> [] \<or> chv = hd C"
        using True chp odd_cycleD(3)[OF cycle(1)]
        by \<^marker>\<open>provenance ai\<close> simp
      ultimately have "last (edges_of_path (chp @ [chv])) \<in> M \<and> chp \<noteq> [] \<or> chv = hd C"
        by auto
      moreover have "set (chp @ [chv]) \<subseteq> set C"
        using \<^marker>\<open>provenance ai\<close> find_pfx_subset[of "(=) chv" C] chp
        by \<^marker>\<open>provenance ai\<close> simp
      ultimately have "alt_path M (chv # a2' # p2')"
        using alt_list_p2[of chp] odd_cycleD(3)[OF cycle(1)]
        by simp
      moreover have "alt_path M (chp @ [chv])"
        using alt_list_chp_chv .
      moreover have "edges_of_path (chp @ [chv]) \<noteq> [] \<longrightarrow> last (edges_of_path (chp @ [chv])) \<in> M"
        proof \<^marker>\<open>provenance ai\<close> (intro impI)
          assume \<^marker>\<open>provenance human\<close> nonempty: "edges_of_path (chp @ [chv]) \<noteq> []"
          have \<^marker>\<open>provenance human\<close> chp_nempty: "chp \<noteq> []"
            using \<^marker>\<open>provenance ai\<close> nonempty
            by \<^marker>\<open>provenance ai\<close> auto
          have \<^marker>\<open>provenance human\<close> "chv \<noteq> hd C"
          proof \<^marker>\<open>provenance ai\<close>
            assume h: "chv = hd C"
            have \<^marker>\<open>provenance human\<close> "find_pfx ((=) chv) C = [chv]"
              using \<open>C \<noteq> []\<close> h
              by \<^marker>\<open>provenance ai\<close> (cases C) auto
            thus False
              using chp chp_nempty
              by simp
          qed
          then show \<^marker>\<open>provenance human\<close> "last (edges_of_path (chp @ [chv])) \<in> M"
            using \<open>last (edges_of_path (chp @ [chv])) \<in> M \<and> chp \<noteq> [] \<or> chv = hd C\<close>
            by \<^marker>\<open>provenance ai\<close> blast
        qed
      moreover have "\<forall>x\<in>set (edges_of_path (chp @ [chv])). (x \<notin> M) = (x \<notin> M)"
        by auto
      ultimately have "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path ((chp @ [chv])) @ edges_of_path (chv # a2' # p2'))"
        by (intro alt_list_append_3; use alternating_list_odd_last in auto)
      moreover have "(edges_of_path (chp @ [chv]) @ edges_of_path (chv # a2' # p2')) =
                           (edges_of_path ((chp @ [chv] @ [a2']) @ p2'))"
        using \<^marker>\<open>provenance ai\<close> edges_of_path_symmetric_split[of chp chv a2' p2']
        by \<^marker>\<open>provenance ai\<close> simp
      ultimately show ?thesis
        by simp
    qed
    ultimately \<^marker>\<open>provenance human\<close> show \<^marker>\<open>provenance human\<close> "alt_path M (find_pfx ((=) chv) C @ p2)"
      using Cons chp
      by \<^marker>\<open>provenance ai\<close> simp
  qed

  have "path (quotG E) (u # p2)"
    using path_suff quot_aug_path
    by blast
  then have "set p2 \<subseteq> Vs (quotG E)"
    using quot
    using  tl_path_is_path
    by (auto intro!: subset_path_Vs dest: tl_path_is_path)
  moreover have u_nin_p2: "u \<notin> set p2"
    using quot_aug_path
    by auto
  ultimately have p2_subset_s: "set p2 \<subseteq> s"
    by (auto intro: in_quotG_neq_u)
  have "path (quotG E) (p1 @ [u])"
    using quot_aug_path
    by (auto simp: path_pref)
  then have "set p1 \<subseteq> Vs (quotG E)"
    using quot
    by (auto intro!: subset_path_Vs dest: path_pref)
  moreover have u_nin_p1: "u \<notin> set (rev p1)"
    using quot_aug_path
    by auto
  ultimately have p1_subset_s: "set (rev p1) \<subseteq> s"
    by (auto intro: in_quotG_neq_u)
  note inBetinM = 
         inBetinM[OF cycle matching quot(1)]


  have \<^marker>\<open>provenance ai\<close> append_works: "\<And>p1 p2. {u, hd p2} \<notin> quotG M \<Longrightarrow> set p1 \<subseteq> s \<Longrightarrow>
      matching_augmenting_path (quotG M) (p1 @ u # p2) \<Longrightarrow> 2 \<le> length p1 \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow>
      alt_path M (stem2vert_path adj mate C (hd p2) @ p2) \<Longrightarrow>
      alt_path M (p1 @ stem2vert_path adj mate C (hd p2) @ p2)"
  proof-
    fix \<^marker>\<open>provenance human\<close> p1 p2 ::"'a list"
    assume \<^marker>\<open>provenance human\<close> up2_nin_M: "{u, hd p2} \<notin> quotG M"
    assume \<^marker>\<open>provenance human\<close> p1_subset_s: "set p1 \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> quot_aug_path: "matching_augmenting_path (quotG M) (p1 @ u # p2)"
    assume \<^marker>\<open>provenance human\<close> len_ge_2: "length p1 \<ge> 2"
    assume \<^marker>\<open>provenance human\<close> p2_nempty: "p2 \<noteq> []"
    assume \<^marker>\<open>provenance human\<close> that: "alt_path M (stem2vert_path adj mate C (hd p2) @ p2)"
    show \<^marker>\<open>provenance human\<close> "alt_path M (p1 @ stem2vert_path adj mate C (hd p2) @ p2)"
    proof-
      have p1_nempty: "p1 \<noteq> []"
        using len_ge_2
        by auto
      show ?thesis
      proof-
        have inM: "{last p1, u} \<in> quotG M"
          using alt_list_append_1'''[OF matching_augmenting_path_feats(2)[OF quot_aug_path, unfolded rw4[OF p1_nempty p2_nempty]] _ up2_nin_M]
          by auto
        define chp where "chp = (stem2vert_path adj mate C (hd p2))"
        have i: "{last p1, hd chp} \<in> M"
          using inBetinM[OF p1_nempty _ inM] p1_subset_s
          unfolding chp_def
          by auto
        have rw: "(edges_of_path (p1 @ chp @ p2)) = (edges_of_path (p1 @ [hd chp]) @ (edges_of_path (chp @ p2)))"
        proof-
          have "C \<noteq> []"
            using odd_cycle_nempty[OF cycle(1)].
          then have "chp \<noteq> []"
            unfolding chp_def
            by (simp add: hd_stem2vert_nempty)
          then have "chp = ((hd chp) # (tl chp))"
            by auto
          then show ?thesis
            using \<^marker>\<open>provenance ai\<close> edges_of_path_append_2'[of "chp @ p2" p1] \<open>chp \<noteq> []\<close>
            by (simp add: hd_append2)
        qed
        have alt_p1hd: "alt_path M (p1 @ [hd chp])"
        proof-
          have rw:"(edges_of_path (p1 @ [hd chp])) = (edges_of_path (p1)  @ [{last p1, hd chp}])"
            unfolding chp_def
            by (simp add: edges_of_path_snoc p1_nempty)
          have rw2:"(edges_of_path (p1 @ l)) = (edges_of_path p1  @ (edges_of_path (last p1 # l)))" for l
            by (simp add: edges_of_path_append_3 p1_nempty)
          have alt_p1: "alt_path M p1"
            using alt_list_quotG_then_alt_list_1[OF _ conjunct1[OF alt_list_append_1[OF matching_augmenting_path_feats(2)[OF quot_aug_path, unfolded rw2]]]]
            using p1_subset_s matching(2)
            by linarith
          show \<^marker>\<open>provenance ai\<close> ?thesis
            unfolding rw
          proof \<^marker>\<open>provenance human\<close>(rule alt_list_append_2, goal_cases)
            case \<^marker>\<open>provenance ai\<close> 1
            show \<^marker>\<open>provenance ai\<close> ?case
              by (rule alt_p1)
          next \<^marker>\<open>provenance ai\<close>
            case \<^marker>\<open>provenance ai\<close> 2
            show \<^marker>\<open>provenance ai\<close> ?case
              using \<^marker>\<open>provenance human\<close> i
              by \<^marker>\<open>provenance human\<close> (simp add: alt_list_step alt_list_empty)
          next \<^marker>\<open>provenance ai\<close>
            case \<^marker>\<open>provenance ai\<close> 3
            show \<^marker>\<open>provenance ai\<close> ?case
            proof \<^marker>\<open>provenance human\<close>-
              have rw6: "last (edges_of_path p1) = {last(butlast p1), last p1}"
                using len_ge_2
                by (cases p1 rule: rev_cases) (auto simp: Suc_le_eq neq_Nil_conv edges_of_path_snoc[symmetric])
              then show ?thesis
              proof \<^marker>\<open>provenance ai\<close>-
                have \<^marker>\<open>provenance human\<close> "last (edges_of_path p1) \<in> set (edges_of_path p1)"
                  using \<^marker>\<open>provenance ai\<close> len_ge_2 edges_of_path_nempty
                  by (intro last_in_set) auto
                moreover have \<^marker>\<open>provenance human\<close> "last (edges_of_path p1) \<notin> quotG M"
                  using alt_list_append_1''''[OF matching_augmenting_path_feats(2)[OF quot_aug_path, unfolded rw5[OF len_ge_2]] _ inM] rw6
                  by \<^marker>\<open>provenance ai\<close> simp
                ultimately have \<^marker>\<open>provenance human\<close> "last (edges_of_path p1) \<notin> M"
                  using edge_of_path_in_graph_iff_in_quot[OF p1_subset_s _ M_subset_E]
                  by \<^marker>\<open>provenance ai\<close> blast
                thus ?thesis
                  using alternating_list_even_last[OF alt_p1] len_ge_2 edges_of_path_nempty
                  by \<^marker>\<open>provenance human\<close> auto
              qed \<^marker>\<open>provenance human\<close>
            qed
          qed \<^marker>\<open>provenance ai\<close>
        qed \<^marker>\<open>provenance ai\<close>
        have "alt_path M (p1 @ chp @ p2)"
          unfolding \<^marker>\<open>provenance ai\<close> rw
        proof \<^marker>\<open>provenance ai\<close>(intro alt_list_append_3, goal_cases)
          case 1
          show ?case
            by (rule alt_p1hd)
        next
          case 2
          show ?case
            using \<^marker>\<open>provenance human\<close> that
            unfolding \<^marker>\<open>provenance human\<close> chp_def
            by \<^marker>\<open>provenance human\<close> auto
        next
          case 3
          show ?case
          proof(rule ccontr)
            assume \<^marker>\<open>provenance human\<close> "\<not> even (length (edges_of_path (p1 @ [hd chp])))"
            hence odd: "odd (length (edges_of_path (p1 @ [hd chp])))"
              by simp
            have \<^marker>\<open>provenance human\<close> "edges_of_path (p1 @ [hd chp]) \<noteq> []"
              using \<^marker>\<open>provenance ai\<close> p1_nempty
              by (cases p1) (auto simp: edges_of_path_nempty)
            hence "last (edges_of_path (p1 @ [hd chp])) \<notin> M"
              using \<^marker>\<open>provenance human\<close> alternating_list_odd_last[OF alt_p1hd odd]
              by blast
            moreover have \<^marker>\<open>provenance human\<close> "last (edges_of_path (p1 @ [hd chp])) = {last p1, hd chp}"
              using \<^marker>\<open>provenance ai\<close> p1_nempty
              by (simp add: edges_of_path_snoc[symmetric])
            ultimately show False
              using \<^marker>\<open>provenance human\<close> i
              by simp
          qed
        qed
        then show ?thesis
          unfolding chp_def
          by auto
      qed
    qed
  qed

  have \<^marker>\<open>provenance ai\<close> replace_cycle_cases: "\<And>p1 p2. set p2 \<subseteq> s \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow>
      {u, hd p2} \<notin> quotG M \<or> p1 = [] \<Longrightarrow> alt_path (quotG M) (u # p2) \<Longrightarrow>
      distinct (u # p2) \<Longrightarrow> path (quotG E) (u # p2) \<Longrightarrow>
      (alt_path M (stem2vert_path adj mate C (hd p2) @ p2) \<Longrightarrow>
        alt_path M (p1 @ stem2vert_path adj mate C (hd p2) @ p2)) \<Longrightarrow>
      alt_path M (replace_cycle adj mate C p1 p2)"
  proof-
    fix \<^marker>\<open>provenance human\<close> p1 p2::"'a list"
    assume \<^marker>\<open>provenance human\<close> p2_subset_s: "set p2 \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> p2_nempty[simp]: "p2 \<noteq> []" "({u, hd p2} \<notin> quotG M) \<or> p1 = []"
    assume \<^marker>\<open>provenance human\<close> quot_aug_path: "alt_path (quotG M) (u # p2)" (is ?p1) "distinct (u # p2)" (is ?p2) "path (quotG E) (u # p2)" (is ?p3)
    assume \<^marker>\<open>provenance human\<close> alt_list_app: "alt_path M (p1 @ stem2vert_path adj mate C (hd p2) @ p2)"
      if  "alt_path M (stem2vert_path adj mate C (hd p2) @ p2)"
    show \<^marker>\<open>provenance human\<close> "alt_path M (replace_cycle adj mate C p1 p2)"
    proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert adj C (hd p2))) C)) \<in> M")
      case T3: True
      then have i: "alt_path M (stem2vert_path adj mate C (hd p2) @ p2)"
        using d1[OF p2_nempty(1) quot_aug_path p2_subset_s cycle quot(1) choose_vert_works_3[OF cycle(3) quot_aug_path(2) quot_aug_path(3) p2_nempty(1) quot(1)]]
        by (simp add: stem2vert_path_def' Let_def)
      with alt_list_app[OF i] p2_nempty show ?thesis
        unfolding replace_cycle_def' Let_def
        by(simp split: if_splits; intro impI conjI)+
    next
      define chv where "chv = (choose_con_vert adj C (hd p2))"
      case F1: False
      show ?thesis
      proof(cases "chv = last C")
        case T2: True
        then have i: "alt_path M (stem2vert_path adj mate C (hd p2) @ p2)"
          using d1[OF p2_nempty(1) quot_aug_path p2_subset_s cycle quot(1) choose_vert_works_3[OF cycle(3) quot_aug_path(2) quot_aug_path(3) p2_nempty(1) quot(1)]]
          by \<^marker>\<open>provenance ai\<close> (simp add: stem2vert_path_eq_pfx[OF odd_cycle_nempty(1)[OF cycle(1)]] chv_def[symmetric])
        with alt_list_app[OF i] p2_nempty show ?thesis
          unfolding replace_cycle_def' Let_def
          by(simp split: if_splits; intro impI conjI)+
      next
        case F2: False
        have choose_vert_works: "chv \<in> set C"
          unfolding chv_def
          using choose_vert_works_1[OF cycle(3) _ _ _ _ quot(1)] quot_aug_path  p2_nempty
          by blast
        moreover have "chv \<noteq> hd C"
          using odd_cycleD(3)[OF cycle(1)] F2
          by auto
        ultimately have i: "last (edges_of_path (find_pfx ((=) chv) (rev C))) \<in> M"
          using F1 find_pfx_edges_of_path_alt_list(2)[OF cycle]
          using chv_def
          by blast
        have ii: "distinct (tl (rev C))"
          using cycle(3) odd_cycleD(3)[OF cycle(1)] tl_distinct_rev
          by auto
        have iii: "s = Vs E - set (rev C)"
          using quot
          by auto
        have cvw: "chv \<in> set (rev C)" "{hd p2, chv} \<in> E"
          using choose_vert_works_3[OF cycle(3) quot_aug_path(2) quot_aug_path(3) p2_nempty(1) quot(1)] chv_def
          by \<^marker>\<open>provenance ai\<close> simp_all
        have i: "alt_path M (stem2vert_path adj mate C (hd p2) @ p2)"
          using F1 d1[OF p2_nempty(1) quot_aug_path p2_subset_s odd_cycle_rev[OF cycle(1)] odd_cycle_rev_alt_list[OF cycle(1,2)] ii iii cvw disjI1[OF i]]
          by (simp add: chv_def stem2vert_path_def' Let_def)
        then show ?thesis
          unfolding replace_cycle_def' Let_def
          using alt_list_app[OF i] p2_nempty
          by (auto split: if_splits)
      qed
    qed
  qed

  have \<^marker>\<open>provenance ai\<close> replace_cycle_cases_p1: "\<And>p1 p2. set (rev p1) \<subseteq> s \<Longrightarrow>
      {u, hd p2} \<in> quotG M \<or> p2 = [] \<Longrightarrow> p1 \<noteq> [] \<Longrightarrow> alt_path (quotG M) (u # rev p1) \<Longrightarrow>
      distinct (u # rev p1) \<Longrightarrow> path (quotG E) (u # rev p1) \<Longrightarrow>
      (alt_path M (stem2vert_path adj mate C (hd (rev p1)) @ rev p1) \<Longrightarrow>
        alt_path M (rev p2 @ stem2vert_path adj mate C (last p1) @ rev p1)) \<Longrightarrow>
      alt_path M (replace_cycle adj mate C p1 p2)"
  proof-
    fix \<^marker>\<open>provenance human\<close> p1 p2::"'a list"
    assume \<^marker>\<open>provenance human\<close> p1_subset_s: "set (rev p1) \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> up2_in_M: "{u, hd p2} \<in> quotG M \<or> p2 = []"
    assume \<^marker>\<open>provenance human\<close> p1_nempty[simp]: "p1 \<noteq> []"
    have \<^marker>\<open>provenance human\<close> rev_p1_nempty: "rev p1 \<noteq> []"
      using p1_nempty
      by auto
    assume \<^marker>\<open>provenance human\<close> quot_aug_path: "alt_path (quotG M) (u # rev p1)" (is ?p1) "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
    assume \<^marker>\<open>provenance human\<close> alt_list_rev: "alt_path M (rev p2 @ stem2vert_path adj mate C (last p1) @ rev p1)"
      if  "alt_path M (stem2vert_path adj mate C (hd (rev p1)) @ rev p1)"
    show \<^marker>\<open>provenance human\<close> "alt_path M (replace_cycle adj mate C p1 p2)"
    proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert adj C (hd (rev p1)))) C)) \<in> M")
      case True
      then have i: "alt_path M (stem2vert_path adj mate C (hd (rev p1)) @ rev p1)"
        using d1[OF rev_p1_nempty quot_aug_path p1_subset_s cycle quot(1) choose_vert_works_3[OF cycle(3) quot_aug_path(2) quot_aug_path(3) rev_p1_nempty quot(1)]]
        by (simp add: stem2vert_path_def' Let_def)
      with alt_list_rev i[unfolded hd_rev] up2_in_M show ?thesis
        unfolding replace_cycle_def' Let_def
        by(simp add: hd_rev split: if_splits; intro impI conjI)+
    next
      define chv where "chv = (choose_con_vert adj C (last p1))"
      case F1: False
      show ?thesis
      proof(cases "chv = last C")
        case True
        then have i: "alt_path M (stem2vert_path adj mate C (hd (rev p1)) @ rev p1)"
          using d1[OF rev_p1_nempty quot_aug_path p1_subset_s cycle quot(1) choose_vert_works_3[OF cycle(3) quot_aug_path(2) quot_aug_path(3) rev_p1_nempty quot(1)]]
          by \<^marker>\<open>provenance ai\<close> (simp add: stem2vert_path_eq_pfx[OF odd_cycle_nempty(1)[OF cycle(1)]] chv_def[symmetric] hd_rev)
        with up2_in_M alt_list_rev i[unfolded hd_rev]  show ?thesis
          unfolding replace_cycle_def' Let_def
          by(simp add: hd_rev split: if_splits; intro impI conjI)+
      next
        case False
        have choose_vert_works: "chv \<in> set C"
          unfolding chv_def
          using choose_vert_works_3(1)[OF cycle(3) quot_aug_path(2) quot_aug_path(3) rev_p1_nempty quot(1)]
          by (simp add: hd_rev)
        moreover have "chv \<noteq> hd C"
          using odd_cycleD(3)[OF cycle(1)] False
          by auto
        ultimately have i: "last (edges_of_path (find_pfx ((=) chv) (rev C))) \<in> M"
          using F1 find_pfx_edges_of_path_alt_list(2)[OF cycle choose_vert_works \<open>chv \<noteq> hd C\<close>]
          by (auto simp: chv_def hd_rev)
        have ii: "distinct (tl (rev C))"
          using cycle(3) odd_cycleD(3)[OF cycle(1)] tl_distinct_rev
          by auto
        have iii: "s = Vs E - set (rev C)"
          using quot
          by auto
        have cvw: "chv \<in> set (rev C)" "{hd (rev p1), chv} \<in> E"
          using choose_vert_works_3[OF cycle(3) quot_aug_path(2) quot_aug_path(3) rev_p1_nempty quot(1)] chv_def
          by (simp_all add: hd_rev)
        have i: "alt_path M (stem2vert_path adj mate C (hd (rev p1)) @ rev p1)"
          using F1 d1[OF rev_p1_nempty quot_aug_path p1_subset_s odd_cycle_rev[OF cycle(1)] odd_cycle_rev_alt_list[OF cycle(1,2)] ii iii cvw disjI1[OF i]]
          by (simp add: chv_def stem2vert_path_def' Let_def hd_rev)
        moreover have " alt_path M (rev p2 @ stem2vert_path adj mate C (last p1) @ rev p1)"
          by (rule alt_list_rev[OF i])
        ultimately show ?thesis
          unfolding replace_cycle_def' Let_def
          using up2_in_M
          by(simp add: hd_rev split: if_splits; intro impI conjI)+
      qed
    qed
  qed \<^marker>\<open>provenance human\<close>
    (*To be able to give up replace_cycle_cases_p1 and use replace_cycle_cases instead of it, we need
    to show that rev (replace_cycle) = replace_cycle.*)

  have "matching_augmenting_path (quotG M) p'" "path (quotG E) p'"
    using quot_aug_path(2)
    by simp+

  note p'_feats = matching_augmenting_path_feats[OF \<open>matching_augmenting_path (quotG M) p'\<close>]

  show ?thesis
  proof(cases "p1 = []")
    case nil1: True
    show ?thesis
    proof(cases "p2 = []")
      case nil2: True
      then show ?thesis
        using p'_feats quot_aug_path(1)
        by (simp add: nil1 )
    next
      case p2_nempty: False
      show ?thesis
        using replace_cycle_cases[OF p2_subset_s p2_nempty _ ] nil1 p'_feats quot_aug_path
        by (auto simp add: p2_nempty nil1)
    qed
  next
    case p1_nempty: False
    show ?thesis
    proof(cases "alt_path (quotG M) (u # p2)")
      case T1: True
      show ?thesis
      proof(cases "p2 = []")
        case T2: True
        have quot_aug_path_p1: "alt_path (quotG M) (u # rev p1)" (is ?p1) "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
        proof-
          have "alt_path (quotG M) (p1 @ [u])"
            using p'_feats quot_aug_path(1) T2
            by simp
          have rw: "edges_of_path p' = (edges_of_path (p1 @ [u])) @ edges_of_path (u # p2)"
            using edges_of_path_append_2 quot_aug_path(1)
            by fastforce
          have eop_nempty: "edges_of_path (p1 @ [u]) \<noteq> []"
            using \<^marker>\<open>provenance ai\<close> p1_nempty
            by (cases p1) (auto simp: edges_of_path_nempty)
          have "alt_path (quotG M) (rev (p1 @ [u]))"
            unfolding edges_of_path_rev[symmetric]
          proof(intro alt_list_rev, goal_cases)
            case \<^marker>\<open>provenance ai\<close> 1
            show \<^marker>\<open>provenance ai\<close> ?case
              using \<^marker>\<open>provenance human\<close> T2 matching_augmenting_path_last_edge_nin quot_aug_path(1) quot_aug_path(2)
                \<open>alt_path (quotG M) (p1 @ [u])\<close>
              by \<^marker>\<open>provenance human\<close> blast
          next \<^marker>\<open>provenance ai\<close>
            case \<^marker>\<open>provenance ai\<close> 2
            show \<^marker>\<open>provenance ai\<close> ?case
              using \<^marker>\<open>provenance human\<close> T2 matching_augmenting_path_odd_length quot_aug_path(1) quot_aug_path(2)
              by \<^marker>\<open>provenance human\<close> blast
          qed \<^marker>\<open>provenance ai\<close>
          then show ?p1
            by simp
          show ?p2
            using quot_aug_path
            by simp
          show ?p3
            using quot_aug_path
            using T2 rev_path_is_path
            by force
        qed
        have rev_p1_nempty: "rev p1 \<noteq> []"
          using p1_nempty
          by simp
        show ?thesis
          using replace_cycle_cases_p1[OF p1_subset_s _ p1_nempty quot_aug_path_p1] T2
          by (simp add: hd_rev)
      next
        case p2_nempty: False
        then have up2_nin_M: "{u, hd p2} \<notin> quotG M"
          using T1
          by(cases p2; auto simp add: alt_list_step)
        show ?thesis
        proof(cases "length p1 \<ge> 2")
          case len_ge_2: True
          have alt_list_app: "alt_path M (p1 @ stem2vert_path adj mate C (hd p2) @ p2)"
            if  "alt_path M (stem2vert_path adj mate C (hd p2) @ p2)"
            using append_works[OF up2_nin_M _ graph_augmenting_path_feats(1)[OF quot_aug_path(2), unfolded quot_aug_path(1)] len_ge_2 p2_nempty] p1_subset_s
            by (simp add: that)
          have quot_aug_path_p2: "alt_path (quotG M) (u # p2)" (is ?p1) "distinct (u # p2)" (is ?p2) "path (quotG E) (u # p2)" (is ?p3)
          proof-
            show ?p1
              using T1
              by blast
            show ?p2
              using quot_aug_path
              by simp
            show ?p3
              using quot_aug_path rev_path_is_path  \<open>path (quotG E) (u # p2)\<close>
              by fastforce
          qed
          show ?thesis
            using replace_cycle_cases[OF p2_subset_s p2_nempty _ quot_aug_path_p2 alt_list_app] up2_nin_M
            by blast
        next
          case False                                                                                                    
          then have "length p1 = 1"
            using \<^marker>\<open>provenance ai\<close> p1_nempty
            by (cases p1) (auto simp: Suc_le_eq)
          then obtain a where "p1 = [a]"
            by \<^marker>\<open>provenance ai\<close> (cases p1) auto
          then have False
            using quot_aug_path(1) p'_feats up2_nin_M p2_nempty
            by(auto simp add: alt_list_step neq_Nil_conv)
          then show ?thesis
            by simp
        qed        
      qed
    next
      case p2_nalt: False
      have last_p1_nin: "alt_path (quotG M) (p1 @ [u])" (is ?p1)
        "last (edges_of_path (p1 @ [u])) \<notin> quotG M" (is ?p2)
      proof-
        have rw: "edges_of_path p' = (edges_of_path (p1 @ [u])) @ edges_of_path (u # p2)"
          using edges_of_path_append_2 quot_aug_path(1)
          by fastforce
        have eop_nempty: "edges_of_path (p1 @ [u]) \<noteq> []"
          using \<^marker>\<open>provenance ai\<close> p1_nempty
          by (cases p1) (auto simp: edges_of_path_nempty)
        show ?p1 ?p2
          using alt_list_append_1'[OF p'_feats(2)[unfolded rw] eop_nempty] p2_nalt
          by blast+
      qed
      have up2_nin_M: "{last p1 , u} \<notin> quotG M"
      proof-
        have "last (edges_of_path (p1 @ [u])) = {last p1, u}"
          using p1_nempty
          by (simp add: edges_of_path_snoc[symmetric] p1_nempty)
        then show ?thesis 
          using last_p1_nin
          by auto
      qed
      have rev_p1_nempty: "rev p1 \<noteq> []"
        using p1_nempty
        by auto
      have up2_in_M: "{u, hd p2} \<in> quotG M" if "p2 \<noteq> []"
        using p'_feats
        unfolding rw4[OF p1_nempty that] quot_aug_path(1)
        using alt_list_append_1'' p2_nalt up2_nin_M
        by \<^marker>\<open>provenance ai\<close> fastforce
      show ?thesis
      proof(cases "length p2 \<ge> 2")
        case len_p2_ge_2: True
        have app_works: "alt_path M (rev p2 @ stem2vert_path adj mate C (last p1) @ rev p1)"
          if  "alt_path M (stem2vert_path adj mate C (last p1) @ rev p1)"
          unfolding hd_rev[symmetric]
        proof(rule append_works, goal_cases)
          case \<^marker>\<open>provenance ai\<close> 1
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> up2_nin_M
            by \<^marker>\<open>provenance human\<close> (simp add: hd_rev p1_nempty insert_commute)
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 2
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> p2_subset_s
            by \<^marker>\<open>provenance human\<close> auto
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 3
          have "rev p2 @ u # rev p1 = rev p'"
            by (simp add: quot_aug_path(1))
          thus \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> quot_aug_path(1,2) matching_augmenting_path_rev
            by \<^marker>\<open>provenance human\<close> force
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 4
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> len_p2_ge_2
            by \<^marker>\<open>provenance human\<close> auto
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 5
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> p1_nempty
            by \<^marker>\<open>provenance human\<close> auto
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 6
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> that[unfolded hd_rev[symmetric]] . \<^marker>\<open>provenance human\<close>
        qed \<^marker>\<open>provenance ai\<close>
        have quot_aug_path_p1: "alt_path (quotG M) (u # rev p1)" (is ?p1) "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
        proof-
          have "alt_path (quotG M) (rev (p1 @ [u]))"
            unfolding edges_of_path_rev[symmetric]
          proof(intro alt_list_rev, goal_cases)
            case \<^marker>\<open>provenance ai\<close> 1
            show \<^marker>\<open>provenance ai\<close> ?case
              using \<^marker>\<open>provenance human\<close> last_p1_nin(1)
              by \<^marker>\<open>provenance human\<close> blast
          next \<^marker>\<open>provenance ai\<close>
            case \<^marker>\<open>provenance ai\<close> 2
            show \<^marker>\<open>provenance ai\<close> ?case
              using \<^marker>\<open>provenance human\<close> alternating_list_even_last edges_of_path_snoc last_p1_nin(1,2) p1_nempty
                snoc_eq_iff_butlast
              by \<^marker>\<open>provenance human\<close> fastforce
          qed \<^marker>\<open>provenance ai\<close>
          then show ?p1
            by simp
          show ?p2
            using quot_aug_path
            by simp
          show ?p3
            using quot_aug_path rev_path_is_path  \<open>path (quotG E) (p1 @ [u])\<close>
            by fastforce
        qed
        show "alt_path M (replace_cycle adj mate C p1 p2)"
          using replace_cycle_cases_p1[OF p1_subset_s _ p1_nempty quot_aug_path_p1 app_works] up2_in_M
          using hd_rev p1_nempty
          by \<^marker>\<open>provenance ai\<close> (auto simp: hd_rev)
      next
        case len_p2_nge_2: False
        show ?thesis
        proof(cases "p2 = []")
          case True
          then have False
            using p2_nalt alt_list.intros(1)
            by auto
          then show ?thesis
            by simp
        next
          case p2_nempty: False
          then have "length p2 = 1"
            using len_p2_nge_2
            by (cases p2) (auto simp: Suc_le_eq)
          then obtain a where "p2 = [a]"
            by \<^marker>\<open>provenance ai\<close> (cases p2) auto
          then have False
          proof \<^marker>\<open>provenance ai\<close>-
            have \<^marker>\<open>provenance human\<close> "{u, a} \<in> quotG M"
              using up2_in_M \<open>p2 = [a]\<close> p2_nempty
              by \<^marker>\<open>provenance ai\<close> auto
            hence \<^marker>\<open>provenance human\<close> "a \<in> Vs (quotG M)"
              by (auto intro: edges_are_Vs insert_commute)
            moreover have "last p' = a"
              using \<^marker>\<open>provenance human\<close> quot_aug_path(1) \<open>p2 = [a]\<close>
              by simp
            ultimately show False
              using p'_feats(4)
              by simp
          qed
          then show ?thesis
            by simp
        qed
      qed
    qed
  qed
qed
end

lemma path_find_pref:
  assumes "path E C"
  shows "path E (find_pfx Q C)"
proof \<^marker>\<open>provenance ai\<close>-
  obtain \<^marker>\<open>provenance human\<close> l2 where l2: "C = find_pfx Q C @ l2"
    using find_pfx_append_2
    by \<^marker>\<open>provenance ai\<close> blast
  have \<^marker>\<open>provenance human\<close> "path E (find_pfx Q C @ l2)"
    by \<^marker>\<open>provenance ai\<close> (rule subst[where P = "path E", OF l2 assms])
  thus ?thesis
    by \<^marker>\<open>provenance human\<close> (rule path_pref)
qed

context quot_lift
begin

lemma path_stem2vert_path:
  assumes "path E C"
  shows "path E (stem2vert_path adj mate C v)"
  unfolding stem2vert_path_def'
  using rev_path_is_path assms path_find_pref
  by (simp add: Let_def; blast)+

lemma path_replace_cycle:
  assumes cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)" "path E C" and
    quot_aug_path: "p' = (p1 @ u # p2)" "graph_augmenting_path (quotG E) (quotG M) p'" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"(*and
    graph: "dblton_graph E"*)
  shows "path E (replace_cycle adj mate C p1 p2)"
proof-


  have \<^marker>\<open>provenance ai\<close> d1: "\<And>C p2 chv. distinct (u # p2) \<Longrightarrow> path (quotG E) (u # p2) \<Longrightarrow> set p2 \<subseteq> s \<Longrightarrow>
      distinct (tl C) \<Longrightarrow> path E C \<Longrightarrow> s = Vs E - set C \<Longrightarrow> chv \<in> set C \<Longrightarrow>
      {hd p2, chv} \<in> E \<Longrightarrow> path E (find_pfx ((=) chv) C @ p2)"
  proof-
    fix \<^marker>\<open>provenance human\<close> C fix \<^marker>\<open>provenance human\<close> p1 p2::"'a list"
    fix chv
    define \<^marker>\<open>provenance human\<close> a2' where "a2' = hd p2"
    assume \<^marker>\<open>provenance human\<close> quot_aug_path: "distinct (u # p2)" "path (quotG E) (u # p2)"
    assume \<^marker>\<open>provenance human\<close> p2_subset_s: "set p2 \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> cycle: "distinct (tl C)" "path E C"
    assume \<^marker>\<open>provenance human\<close> quot: "s = (Vs E) - set C"
    assume choose_vert_works: "chv \<in> set C" "{hd p2, chv} \<in> E"
    define \<^marker>\<open>provenance human\<close> p2' where "p2' = tl p2"
    show \<^marker>\<open>provenance human\<close> "path E (find_pfx ((=) chv) C @ p2)"
    proof(cases "p2 = []")
      case True
      then show ?thesis
        using path_find_pref[OF cycle(2)]
        by simp
    next
      case False
      have Cons: "p2 = a2' # p2'"
        unfolding a2'_def p2'_def
        using \<open>p2 \<noteq> []\<close>
        by auto
      have chv_last: "last (find_pfx ((=) chv) C) = chv"
        using find_pfx_works_1[OF choose_vert_works(1), of "(=) chv"]
        by simp
      moreover have path_p2: "path (quotG E) p2"
        using quot_aug_path tl_path_is_path
        by fastforce
      then have "path E p2"
        by(intro path_is_quot_path'[OF path_p2] p2_subset_s)
      ultimately show ?thesis
      proof(intro path_append)
        show "path E (find_pfx ((=) chv) C)"
          using cycle(2)
          by \<^marker>\<open>provenance ai\<close> (rule path_find_pref)
        show \<^marker>\<open>provenance ai\<close> "path E p2"
          using \<^marker>\<open>provenance human\<close> \<open>path E p2\<close> .
        assume \<^marker>\<open>provenance ai\<close> "find_pfx ((=) chv) C \<noteq> []" "p2 \<noteq> []"
        show \<^marker>\<open>provenance ai\<close> "{last (find_pfx ((=) chv) C), hd p2} \<in> E"
          using \<^marker>\<open>provenance human\<close> chv_last choose_vert_works(2)
          by \<^marker>\<open>provenance human\<close> (simp add: insert_commute)
      qed
    qed \<^marker>\<open>provenance ai\<close>
  qed


  note inBetinM = inBetinM[OF cycle(1-3) matching quot]

  have \<^marker>\<open>provenance ai\<close> append_works: "\<And>p1 p2. {u, hd p2} \<notin> quotG M \<Longrightarrow> set p1 \<subseteq> s \<Longrightarrow>
      matching_augmenting_path (quotG M) (p1 @ u # p2) \<Longrightarrow> path (quotG E) (p1 @ u # p2) \<Longrightarrow>
      2 \<le> length p1 \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> path E (stem2vert_path adj mate C (hd p2) @ p2) \<Longrightarrow>
      path E (p1 @ stem2vert_path adj mate C (hd p2) @ p2)"
  proof-
    fix \<^marker>\<open>provenance human\<close> p1 p2 ::"'a list"
    assume \<^marker>\<open>provenance human\<close> up2_nin_M: "{u, hd p2} \<notin> quotG M"
    assume \<^marker>\<open>provenance human\<close> p1_subset_s: "set p1 \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> quot_aug_path: "matching_augmenting_path (quotG M) (p1 @ u # p2)" "path (quotG E) (p1 @ u # p2)"
    assume \<^marker>\<open>provenance human\<close> len_ge_2: "length p1 \<ge> 2"
    assume \<^marker>\<open>provenance human\<close> p2_nempty: "p2 \<noteq> []"
    assume \<^marker>\<open>provenance human\<close> that: "path E (stem2vert_path adj mate C (hd p2) @ p2)"
    show \<^marker>\<open>provenance human\<close> "path E (p1 @ stem2vert_path adj mate C (hd p2) @ p2)"
    proof-
      have p1_nempty: "p1 \<noteq> []"
        using len_ge_2
        by auto
      show ?thesis
      proof-
        have inM: "{last p1, u} \<in> quotG M"
          using alt_list_append_1'''[OF matching_augmenting_path_feats(2)[OF quot_aug_path(1), unfolded rw4[OF p1_nempty p2_nempty]] _ up2_nin_M]
          by auto
        have i: "{last p1, hd (stem2vert_path adj mate C (hd p2))} \<in> M"
          using inBetinM[OF p1_nempty _ inM] p1_subset_s
          by auto
        show ?thesis
        proof(rule path_append, goal_cases)
          case \<^marker>\<open>provenance ai\<close> 1
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> path_pref[OF quot_aug_path(2)] path_is_quot_path'[OF _ p1_subset_s] quot
            by \<^marker>\<open>provenance human\<close> blast
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 2
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> that . \<^marker>\<open>provenance human\<close>
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 3
          then \<^marker>\<open>provenance ai\<close> show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> i matching(2)
            by \<^marker>\<open>provenance human\<close> (simp add: cycle(1) hd_stem2vert_nempty odd_cycle_nempty subsetD)
        qed
      qed
    qed \<^marker>\<open>provenance ai\<close>
  qed

  have \<^marker>\<open>provenance ai\<close> replace_cycle_cases: "\<And>p1 p2. set p2 \<subseteq> s \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow>
      {u, hd p2} \<notin> quotG M \<or> p1 = [] \<Longrightarrow> alt_path (quotG M) (u # p2) \<Longrightarrow>
      distinct (u # p2) \<Longrightarrow> path (quotG E) (u # p2) \<Longrightarrow>
      (path E (stem2vert_path adj mate C (hd p2) @ p2) \<Longrightarrow>
        path E (p1 @ stem2vert_path adj mate C (hd p2) @ p2)) \<Longrightarrow>
      path E (replace_cycle adj mate C p1 p2)"
  proof-
    fix \<^marker>\<open>provenance human\<close> p1 p2::"'a list"
    assume \<^marker>\<open>provenance human\<close> p2_subset_s: "set p2 \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> p2_nempty[simp]: "p2 \<noteq> []" "({u, hd p2} \<notin> quotG M) \<or> p1 = []"
    assume \<^marker>\<open>provenance human\<close> quot_aug_path: "alt_path (quotG M) (u # p2)" (is ?p1) "distinct (u # p2)" (is ?p2) "path (quotG E) (u # p2)" (is ?p3)
    assume \<^marker>\<open>provenance human\<close> alt_list_app: "path E (p1 @ stem2vert_path adj mate C (hd p2) @ p2)"
      if  "path E (stem2vert_path adj mate C (hd p2) @ p2)"
    show \<^marker>\<open>provenance human\<close> "path E (replace_cycle adj mate C p1 p2)"
    proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert adj C (hd p2))) C)) \<in> M")
      case T3: True
      then have i: "path E (stem2vert_path adj mate C (hd p2) @ p2)"
        using d1 p2_nempty(1) quot_aug_path p2_subset_s cycle quot(1) choose_vert_works_3[OF cycle(3) quot_aug_path(2) quot_aug_path(3) p2_nempty(1) quot(1)]
        by (simp add: stem2vert_path_def' Let_def)
      then show ?thesis
        unfolding replace_cycle_def' Let_def
        using alt_list_app[OF i] p2_nempty
        by (auto split: if_splits)
    next
      define chv where "chv = (choose_con_vert adj C (hd p2))"
      case F1: False
      show ?thesis
      proof(cases "chv = last C")
        case T2: True
        then have i: "path E (stem2vert_path adj mate C (hd p2) @ p2)"
          using d1 p2_nempty(1) quot_aug_path p2_subset_s cycle quot(1) choose_vert_works_3[OF cycle(3) quot_aug_path(2) quot_aug_path(3) p2_nempty(1) quot(1)]
          by \<^marker>\<open>provenance ai\<close> (simp add: stem2vert_path_eq_pfx[OF odd_cycle_nempty(1)[OF cycle(1)]] chv_def[symmetric])
        then show ?thesis
          unfolding replace_cycle_def' Let_def
          using alt_list_app[OF i] p2_nempty
          by (auto split: if_splits)
      next
        case F2: False
        have choose_vert_works: "chv \<in> set C"
          unfolding chv_def
          using choose_vert_works_1[OF cycle(3) _ _ _ _ quot(1)] quot_aug_path  p2_nempty
          by blast
        moreover have "chv \<noteq> hd C"
          using odd_cycleD(3)[OF cycle(1)] F2
          by auto
        ultimately have i: "last (edges_of_path (find_pfx ((=) chv) (rev C))) \<in> M"
          using F1 find_pfx_edges_of_path_alt_list(2)[OF cycle(1,2,3)]
          using chv_def
          by blast
        have ii: "distinct (tl (rev C))"
          using cycle(3) odd_cycleD(3)[OF cycle(1)] tl_distinct_rev
          by auto
        have iii: "s = Vs E - set (rev C)"
          using quot
          by auto
        have iv: "path E (rev C)"
          using cycle(4)
          by (simp add: rev_path_is_path)
        have cvw: "chv \<in> set (rev C)" "{hd p2, chv} \<in> E"
          using choose_vert_works_3[OF cycle(3) quot_aug_path(2) quot_aug_path(3) p2_nempty(1) quot(1)] chv_def
          by \<^marker>\<open>provenance ai\<close> simp_all
        have i: "path E (stem2vert_path adj mate C (hd p2) @ p2)"
          using F1 d1[OF quot_aug_path(2,3) p2_subset_s ii iv iii cvw]
          by (simp add: chv_def stem2vert_path_def' Let_def)
        moreover have "path E (p1 @ stem2vert_path adj mate C (hd p2) @ p2)"
          by (rule alt_list_app[OF i])
        ultimately show ?thesis
          unfolding replace_cycle_def' Let_def
          using p2_nempty
          by (auto split: if_splits)
      qed
    qed
  qed


  have \<^marker>\<open>provenance ai\<close> replace_cycle_cases_p1: "\<And>p1 p2. set (rev p1) \<subseteq> s \<Longrightarrow>
      {u, hd p2} \<in> quotG M \<or> p2 = [] \<Longrightarrow> p1 \<noteq> [] \<Longrightarrow> alt_path (quotG M) (u # rev p1) \<Longrightarrow>
      distinct (u # rev p1) \<Longrightarrow> path (quotG E) (u # rev p1) \<Longrightarrow>
      (path E (stem2vert_path adj mate C (hd (rev p1)) @ rev p1) \<Longrightarrow>
        path E (rev p2 @ stem2vert_path adj mate C (last p1) @ rev p1)) \<Longrightarrow>
      path E (replace_cycle adj mate C p1 p2)"
  proof-
    fix \<^marker>\<open>provenance human\<close> p1 p2::"'a list"
    assume \<^marker>\<open>provenance human\<close> p1_subset_s: "set (rev p1) \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> up2_in_M: "{u, hd p2} \<in> quotG M \<or> p2 = []"
    assume \<^marker>\<open>provenance human\<close> p1_nempty[simp]: "p1 \<noteq> []"
    have \<^marker>\<open>provenance human\<close> rev_p1_nempty: "rev p1 \<noteq> []"
      using p1_nempty
      by auto
    assume \<^marker>\<open>provenance human\<close> quot_aug_path: "alt_path (quotG M) (u # rev p1)" (is ?p1) "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
    assume \<^marker>\<open>provenance human\<close> alt_list_rev: "path E (rev p2 @ stem2vert_path adj mate C (last p1) @ rev p1)"
      if  "path E (stem2vert_path adj mate C (hd (rev p1)) @ rev p1)"
    show \<^marker>\<open>provenance human\<close> "path E (replace_cycle adj mate C p1 p2)"
    proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert adj C (hd (rev p1)))) C)) \<in> M")
      case True
      then have i: "path E (stem2vert_path adj mate C (hd (rev p1)) @ rev p1)"
        using d1 rev_p1_nempty quot_aug_path p1_subset_s cycle quot(1) choose_vert_works_3[OF cycle(3) quot_aug_path(2) quot_aug_path(3) rev_p1_nempty quot(1)]
        by (simp add: stem2vert_path_def' Let_def)
      with up2_in_M alt_list_rev show ?thesis
        unfolding replace_cycle_def' Let_def
        by(simp add: hd_rev split: if_splits; intro impI conjI)+
    next
      define chv where "chv = (choose_con_vert adj C (last p1))"
      case F1: False
      show ?thesis
      proof(cases "chv = last C")
        case True
        then have i: "path E (stem2vert_path adj mate C (hd (rev p1)) @ rev p1)"
          using d1 rev_p1_nempty quot_aug_path p1_subset_s cycle quot(1) choose_vert_works_3[OF cycle(3) quot_aug_path(2) quot_aug_path(3) rev_p1_nempty quot(1)]
          by \<^marker>\<open>provenance ai\<close> (simp add: stem2vert_path_eq_pfx[OF odd_cycle_nempty(1)[OF cycle(1)]] chv_def[symmetric] hd_rev)
        with up2_in_M alt_list_rev show ?thesis
          unfolding replace_cycle_def' Let_def
          by(simp add: hd_rev split: if_splits; intro impI conjI)+
      next
        case False
        have choose_vert_works: "chv \<in> set C"
          unfolding chv_def
          using choose_vert_works_3(1)[OF cycle(3) quot_aug_path(2) quot_aug_path(3) rev_p1_nempty quot(1)]
          by (simp add: hd_rev)
        moreover have "chv \<noteq> hd C"
          using odd_cycleD(3)[OF cycle(1)] False
          by auto
        ultimately have i: "last (edges_of_path (find_pfx ((=) chv) (rev C))) \<in> M"
          using F1 find_pfx_edges_of_path_alt_list(2)[OF cycle(1,2,3) choose_vert_works \<open>chv \<noteq> hd C\<close>]
          by (auto simp: chv_def hd_rev)
        have ii: "distinct (tl (rev C))"
          using cycle(3) odd_cycleD(3)[OF cycle(1)] tl_distinct_rev
          by auto
        have iii: "s = Vs E - set (rev C)"
          using quot
          by auto
        have iv: "path E (rev C)"
          using cycle(4)
          by (simp add: rev_path_is_path)
        have cvw: "chv \<in> set (rev C)" "{hd (rev p1), chv} \<in> E"
          using choose_vert_works_3[OF cycle(3) quot_aug_path(2) quot_aug_path(3) rev_p1_nempty quot(1)] chv_def
          by (simp_all add: hd_rev)
        have i: "path E (stem2vert_path adj mate C (hd (rev p1)) @ rev p1)"
          using F1 d1[OF quot_aug_path(2,3) p1_subset_s ii iv iii cvw]
          by (simp add: chv_def stem2vert_path_def' Let_def hd_rev)
        moreover have "path E (rev p2 @ stem2vert_path adj mate C (last p1) @ rev p1)"
          by (rule alt_list_rev[OF i])
        ultimately show ?thesis
          unfolding replace_cycle_def' Let_def
          using up2_in_M
          by(simp add: hd_rev split: if_splits; intro impI conjI)+
      qed
    qed
  qed \<^marker>\<open>provenance human\<close>
    (*To be able to give up replace_cycle_cases_p1 and use replace_cycle_cases instead of it, we need
    to show that rev (replace_cycle) = replace_cycle.*)




  have "path (quotG E) (u # p2)"
    using path_suff quot_aug_path
    by blast
  then have "set p2 \<subseteq> Vs (quotG E)"
    using quot
    using split_list_first tl_path_is_path
    by (auto intro!: subset_path_Vs dest: tl_path_is_path)
  moreover have u_nin_p2: "u \<notin> set p2"
    using quot_aug_path
    by auto
  ultimately have p2_subset_s[simp]: "set p2 \<subseteq> s"
    by (auto intro: in_quotG_neq_u)
  have "path (quotG E) (p1 @ [u])"
    using quot_aug_path(1) quot_aug_path(2)
    by (auto simp: path_pref)
  then have "set p1 \<subseteq> Vs (quotG E)"
    using quot
    using split_list_first tl_path_is_path
    by (auto intro!: subset_path_Vs dest: path_pref)
  moreover have u_nin_p1: "u \<notin> set (rev p1)"
    using quot_aug_path
    by auto
  ultimately have p1_subset_s: "set (rev p1) \<subseteq> s"
    by (auto intro: in_quotG_neq_u)
  have [simp]: "matching_augmenting_path (quotG M) p'" "path (quotG E) p'"
    using quot_aug_path(2)
    by simp+

  show ?thesis
  proof(cases "p1 = []")
    case nil1: True
    show ?thesis
    proof(cases "p2 = []")
      case nil2: True
      then show ?thesis
        using matching_augmenting_path_feats(1)[OF \<open>matching_augmenting_path (quotG M) p'\<close>] quot_aug_path(1)
        by (simp add: nil1 )
    next
      case p2_nempty: False
      show ?thesis
        using replace_cycle_cases[OF p2_subset_s p2_nempty _ ] matching_augmenting_path_feats(2)[OF \<open>matching_augmenting_path (quotG M) p'\<close>]
              quot_aug_path
        by (simp add: p2_nempty nil1)
    qed
  next
    case p1_nempty[simp]: False
    show ?thesis
    proof(cases "alt_path (quotG M) (u # p2)")
      case T1: True
      show ?thesis
      proof(cases "p2 = []")
        case T2: True
        have quot_aug_path_p1: "alt_path (quotG M) (u # rev p1)" (is ?p1) "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
        proof-
          have "alt_path (quotG M) (p1 @ [u])"
            using matching_augmenting_path_feats[OF \<open>matching_augmenting_path (quotG M) p'\<close>] quot_aug_path(1) T2
            by simp
          have rw: "edges_of_path p' = (edges_of_path (p1 @ [u])) @ edges_of_path (u # p2)"
            using edges_of_path_append_2 quot_aug_path(1)
            by fastforce
          have eop_nempty: "edges_of_path (p1 @ [u]) \<noteq> []"
            using \<^marker>\<open>provenance ai\<close> p1_nempty
            by (cases p1) (auto simp: edges_of_path_nempty)
          have "alt_path (quotG M) (rev (p1 @ [u]))"
            unfolding edges_of_path_rev[symmetric]
          proof(intro alt_list_rev, goal_cases)
            case \<^marker>\<open>provenance ai\<close> 1
            show \<^marker>\<open>provenance ai\<close> ?case
              using \<^marker>\<open>provenance human\<close> T2 matching_augmenting_path_last_edge_nin quot_aug_path(1) quot_aug_path(2)
                \<open>alt_path (quotG M) (p1 @ [u])\<close>
              by \<^marker>\<open>provenance human\<close> fastforce
          next \<^marker>\<open>provenance ai\<close>
            case \<^marker>\<open>provenance ai\<close> 2
            show \<^marker>\<open>provenance ai\<close> ?case
              using \<^marker>\<open>provenance human\<close> T2 matching_augmenting_path_odd_length quot_aug_path(1) quot_aug_path(2)
              by \<^marker>\<open>provenance human\<close> blast
          qed \<^marker>\<open>provenance ai\<close>
          then show ?p1
            by simp
          show ?p2
            using quot_aug_path
            by simp
          show ?p3
            using quot_aug_path
            using T2 rev_path_is_path
            by force
        qed
        have rev_p1_nempty: "rev p1 \<noteq> []"
          using p1_nempty
          by simp
        show ?thesis
          using replace_cycle_cases_p1[OF p1_subset_s _ p1_nempty quot_aug_path_p1] T2
          by (simp add: hd_rev)
      next
        case p2_nempty: False
        then have up2_nin_M: "{u, hd p2} \<notin> quotG M"
          using T1
          by(cases p2; auto simp add: alt_list_step)
        show ?thesis
        proof(cases "length p1 \<ge> 2")
          case len_ge_2: True
          have path_app: "path E (p1 @ stem2vert_path adj mate C (hd p2) @ p2)"
            if  "path E (stem2vert_path adj mate C (hd p2) @ p2)"
            using append_works[OF up2_nin_M _ _ _ len_ge_2 p2_nempty] p1_subset_s
                  quot_aug_path[unfolded quot_aug_path(1)]
            by (simp add: that)
          have quot_aug_path_p2: "alt_path (quotG M) (u # p2)" (is ?p1) "distinct (u # p2)" (is ?p2) "path (quotG E) (u # p2)" (is ?p3)
          proof-
            show ?p1
              using T1
              by blast
            show ?p2
              using quot_aug_path
              by simp
            show ?p3
              using quot_aug_path rev_path_is_path  \<open>path (quotG E) (u # p2)\<close>
              by fastforce
          qed
          show ?thesis
            using replace_cycle_cases[OF p2_subset_s p2_nempty _ quot_aug_path_p2 path_app] up2_nin_M
            by blast
        next
          case False                                                                                                    
          then have "length p1 = 1"
            using \<^marker>\<open>provenance ai\<close> p1_nempty
            by (cases p1) (auto simp: Suc_le_eq)
          then obtain a where "p1 = [a]"
            by \<^marker>\<open>provenance ai\<close> (cases p1) auto
          then have False
            using quot_aug_path(1) matching_augmenting_path_feats(2)[OF \<open>matching_augmenting_path (quotG M) p'\<close>] up2_nin_M p2_nempty
            by(auto simp add: alt_list_step neq_Nil_conv)
          then show ?thesis
            by simp
        qed        
      qed
    next
      case p2_nalt: False
      have last_p1_nin: "alt_path (quotG M) (p1 @ [u])" (is ?p1)
        "last (edges_of_path (p1 @ [u])) \<notin> quotG M" (is ?p2)
      proof-
        have rw: "edges_of_path p' = (edges_of_path (p1 @ [u])) @ edges_of_path (u # p2)"
          using edges_of_path_append_2 quot_aug_path(1)
          by fastforce
        have eop_nempty: "edges_of_path (p1 @ [u]) \<noteq> []"
          using \<^marker>\<open>provenance ai\<close> p1_nempty
          by (cases p1) (auto simp: edges_of_path_nempty)
        show ?p1 ?p2
          using alt_list_append_1'[OF matching_augmenting_path_feats(2)[OF \<open>matching_augmenting_path (quotG M) p'\<close>, unfolded rw] eop_nempty] p2_nalt
          by blast+
      qed
      have up2_nin_M: "{last p1 , u} \<notin> quotG M"
      proof-
        have "last (edges_of_path (p1 @ [u])) = {last p1, u}"
          using p1_nempty
          by (simp add: edges_of_path_snoc[symmetric] p1_nempty)
        then show ?thesis 
          using last_p1_nin
          by auto
      qed
      have rev_p1_nempty: "rev p1 \<noteq> []"
        using p1_nempty
        by auto
      have up2_in_M: "{u, hd p2} \<in> quotG M" if "p2 \<noteq> []"
        using  matching_augmenting_path_feats(2)[OF \<open>matching_augmenting_path (quotG M) p'\<close>]
        unfolding rw4[OF p1_nempty that] quot_aug_path(1)
        using alt_list_append_1'' p2_nalt up2_nin_M
        by \<^marker>\<open>provenance ai\<close> fastforce
      show ?thesis
      proof(cases "length p2 \<ge> 2")
        case len_p2_ge_2[simp]: True
        have *:"rev p2 @ u # rev p1 = rev p'"
          by (simp add: quot_aug_path(1))
        hence "matching_augmenting_path (quotG M) p'"
          using \<open>matching_augmenting_path (quotG M) p'\<close>
          by simp
        moreover have "path (quotG E) p'"
          using \<open>path (quotG E) p'\<close> rev_path_is_path
          by auto
        have "{u, hd (rev p1)} \<notin> quotG M"
          using up2_nin_M
          by (simp add: hd_rev insert_commute)
        then have app_works: "path E (rev p2 @ stem2vert_path adj mate C (last p1) @ rev p1)"
          if  "path E (stem2vert_path adj mate C (last p1) @ rev p1)"
          unfolding hd_rev[symmetric]
          by (rule append_works;
                use that[unfolded hd_rev[symmetric]] in \<open>simp add: * matching_augmenting_path_rev rev_path_is_path\<close>)
        have quot_aug_path_p1: "alt_path (quotG M) (u # rev p1)" (is ?p1) "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
        proof-
          have "alt_path (quotG M) (rev (p1 @ [u]))"
            unfolding edges_of_path_rev[symmetric]
          proof(intro alt_list_rev, goal_cases)
            case \<^marker>\<open>provenance ai\<close> 1
            show \<^marker>\<open>provenance ai\<close> ?case
              using \<^marker>\<open>provenance human\<close> last_p1_nin(1)
              by blast
          next \<^marker>\<open>provenance ai\<close>
            case \<^marker>\<open>provenance ai\<close> 2
            show \<^marker>\<open>provenance ai\<close> ?case
              using \<^marker>\<open>provenance human\<close> alternating_list_even_last[OF last_p1_nin(1)] last_p1_nin(2) p1_nempty
              by \<^marker>\<open>provenance human\<close> (cases p1; auto simp: edges_of_path_nempty)
          qed \<^marker>\<open>provenance ai\<close>
          then show ?p1
            by simp
          show ?p2
            using quot_aug_path
            by simp
          show ?p3
            using quot_aug_path rev_path_is_path  \<open>path (quotG E) (p1 @ [u])\<close>
            by fastforce
        qed
        show "path E (replace_cycle adj mate C p1 p2)"
          using replace_cycle_cases_p1[OF p1_subset_s _ p1_nempty quot_aug_path_p1 app_works] up2_in_M
          using hd_rev p1_nempty
          by \<^marker>\<open>provenance ai\<close> (auto simp: hd_rev)
      next
        case len_p2_nge_2: False
        show ?thesis
        proof(cases "p2 = []")
          case True
          then have False
            using p2_nalt alt_list.intros(1) 
            by auto
          then show ?thesis
            by simp
        next
          case p2_nempty: False
          then have "length p2 = 1"
            using len_p2_nge_2
            by (cases p2) (auto simp: Suc_le_eq)
          then obtain a where "p2 = [a]"
            by \<^marker>\<open>provenance ai\<close> (cases p2) auto
          then have False
          proof \<^marker>\<open>provenance ai\<close>-
            have \<^marker>\<open>provenance human\<close> "{u, a} \<in> quotG M"
              using up2_in_M \<open>p2 = [a]\<close> p2_nempty
              by \<^marker>\<open>provenance ai\<close> auto
            hence \<^marker>\<open>provenance human\<close> "a \<in> Vs (quotG M)"
              by (auto intro: edges_are_Vs insert_commute)
            moreover have "last p' = a"
              using \<^marker>\<open>provenance human\<close> quot_aug_path(1) \<open>p2 = [a]\<close>
              by simp
            ultimately show False
              using \<^marker>\<open>provenance human\<close> matching_augmenting_path_feats(4)[OF \<open>matching_augmenting_path (quotG M) p'\<close>]
              by simp
          qed
          then show ?thesis
            by simp
        qed
      qed
    qed
  qed
qed

end

lemma find_pfx_butlast:
  assumes "\<not> (Q (last C))" "v \<in> set C" "Q v"
  shows "(\<exists>suf. find_pfx Q C @ suf = butlast C)"
  using assms
proof(induction C arbitrary: v)
  case Nil
  then show ?case
    by simp
next
  case (Cons a C)
  then show ?case 
    by auto
qed

context quot_lift
begin

lemma stem2vert_path_pref_or_suc:
  assumes "odd_cycle C" "alt_path M C" "w \<noteq> last C" "w \<in> set C" "w = (choose_con_vert adj C v)"
  shows "(\<exists>pref. pref @ (rev (stem2vert_path adj mate C v)) = tl C) \<or> (\<exists>suf. ((stem2vert_path adj mate C v)) @ suf = butlast C)"
  unfolding stem2vert_path_def'
  proof((simp add: Let_def split: if_splits; intro conjI impI), goal_cases)
    case \<^marker>\<open>provenance ai\<close> 1
    show \<^marker>\<open>provenance ai\<close> ?case
      using \<^marker>\<open>provenance human\<close> odd_cycleD(3)[OF assms(1)] find_pfx_butlast[where Q = "((=) w)", OF assms(3,4)] assms(5)
      by \<^marker>\<open>provenance human\<close> blast
  next \<^marker>\<open>provenance ai\<close>
    case \<^marker>\<open>provenance ai\<close> 2
    have i: "w \<noteq> last (rev C)"
      using odd_cycle_nempty[OF assms(1)] odd_cycleD(3)[OF assms(1)] assms(3)
      by (simp add: last_rev)
    moreover have ii: "w \<in> set (rev C)"
      using assms(4)
      by auto
    show ?case
    proof \<^marker>\<open>provenance ai\<close>-
      obtain suf where sf: "find_pfx ((=) w) (rev C) @ suf = butlast (rev C)"
        using \<^marker>\<open>provenance human\<close> find_pfx_butlast[where Q = "((=) w)", OF i ii]
        by blast
      have \<^marker>\<open>provenance human\<close> "rev (find_pfx ((=) w) (rev C) @ suf) = rev (butlast (rev C))"
        using \<^marker>\<open>provenance ai\<close> sf
        by \<^marker>\<open>provenance ai\<close> simp
      hence "rev suf @ rev (find_pfx ((=) w) (rev C)) = tl C"
        by \<^marker>\<open>provenance human\<close> (simp add: butlast_rev)
      thus \<^marker>\<open>provenance human\<close> ?thesis
        using \<^marker>\<open>provenance ai\<close> assms(5)
        by \<^marker>\<open>provenance ai\<close> (intro disjI1 exI[of _ "rev suf"]) simp
    qed \<^marker>\<open>provenance human\<close>
  qed \<^marker>\<open>provenance ai\<close>

lemma stem2vert_path_distinct_neq_lastC:
  assumes "odd_cycle C" "alt_path M C" "w \<noteq> last C" "w \<in> set C" "w = choose_con_vert adj C v" "distinct (tl C)"
  shows "distinct (stem2vert_path adj mate C v)"
  using stem2vert_path_pref_or_suc[OF assms(1-5)] assms(6)
  using distinct_tl_then_butlast[OF assms(6) odd_cycleD(3)[OF assms(1)] odd_cycle_nempty[OF assms(1)]]
  by (auto simp: distinct_append distinct_rev dest!: arg_cong[where f = distinct])

lemma stem2vert_path_distinct:
  assumes "odd_cycle C" "alt_path M C" "w \<in> set C" "w = choose_con_vert adj C v" "distinct (tl C)"
  shows "distinct (stem2vert_path adj mate C v)"
proof(cases "w = last C")
  case True
  then show ?thesis
  proof \<^marker>\<open>provenance ai\<close>-
    have \<^marker>\<open>provenance human\<close> nem: "C \<noteq> []"
      using odd_cycle_nempty[OF assms(1)] . \<^marker>\<open>provenance ai\<close>
    have \<^marker>\<open>provenance human\<close> ch: "choose_con_vert adj C v = last C"
      using True assms(4)
      by \<^marker>\<open>provenance ai\<close> simp
    have \<^marker>\<open>provenance human\<close> "stem2vert_path adj mate C v = find_pfx ((=) (choose_con_vert adj C v)) C"
      using stem2vert_path_eq_pfx[OF nem] ch
      by \<^marker>\<open>provenance ai\<close> simp
    moreover have \<^marker>\<open>provenance human\<close> "find_pfx ((=) (choose_con_vert adj C v)) C = [hd C]"
      using find_pfx_hd[OF nem] ch hd_last_cycle
      by \<^marker>\<open>provenance ai\<close> simp
    ultimately show ?thesis
      by simp
  qed
next
  case False
  then show ?thesis
    using stem2vert_path_distinct_neq_lastC[OF assms(1,2) False assms(3-5)]
    by auto
qed

lemma distinct_find_pfx_cycle:
  assumes "odd_cycle Cs" "w \<in> set Cs" "distinct (tl Cs)"
  shows "distinct (find_pfx ((=) w) Cs)"
proof(cases "w = last Cs")
  case \<^marker>\<open>provenance ai\<close> True
  hence \<^marker>\<open>provenance ai\<close> "find_pfx ((=) w) Cs = [hd Cs]"
    using \<^marker>\<open>provenance human\<close> odd_cycleD(3)[OF assms(1)] odd_cycle_nempty[OF assms(1)]
    by \<^marker>\<open>provenance human\<close> (intro find_pfx_hd) simp_all
  thus \<^marker>\<open>provenance ai\<close> ?thesis
    by simp
next \<^marker>\<open>provenance ai\<close>
  case \<^marker>\<open>provenance ai\<close> False
  then \<^marker>\<open>provenance ai\<close> obtain \<^marker>\<open>provenance ai\<close> suf where "find_pfx ((=) w) Cs @ suf = butlast Cs"
    using \<^marker>\<open>provenance human\<close> find_pfx_butlast[where Q = "(=) w", OF _ assms(2)]
    by blast
  moreover \<^marker>\<open>provenance ai\<close> have "distinct (butlast Cs)"
    using distinct_tl_then_butlast[OF assms(3) odd_cycleD(3)[OF assms(1)] odd_cycle_nempty[OF assms(1)]] . \<^marker>\<open>provenance ai\<close>
  ultimately \<^marker>\<open>provenance ai\<close> have "distinct (find_pfx ((=) w) Cs @ suf)"
    by \<^marker>\<open>provenance ai\<close> simp
  thus \<^marker>\<open>provenance ai\<close> ?thesis
    by \<^marker>\<open>provenance human\<close> (auto simp: distinct_append)
qed \<^marker>\<open>provenance ai\<close>

lemma distinct_replace_cycle:
  assumes cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)" "path E C" and
    quot_aug_path: "p' = (p1 @ u # p2)" "graph_augmenting_path (quotG E) (quotG M) p'" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"(*  and
    graph: "dblton_graph E"*)
  shows "distinct (replace_cycle adj mate C p1 p2)"
proof-


  have \<^marker>\<open>provenance ai\<close> d1: "\<And>C p2 chv. distinct (u # p2) \<Longrightarrow> path (quotG E) (u # p2) \<Longrightarrow> set p2 \<subseteq> s \<Longrightarrow>
      odd_cycle C \<Longrightarrow> alt_path M C \<Longrightarrow> distinct (tl C) \<Longrightarrow> path E C \<Longrightarrow>
      s = Vs E - set C \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> chv \<in> set C \<Longrightarrow> {hd p2, chv} \<in> E \<Longrightarrow>
      distinct (find_pfx ((=) chv) C @ p2)"
  proof-
    fix \<^marker>\<open>provenance human\<close> C fix \<^marker>\<open>provenance human\<close> p1 p2::"'a list"
    fix chv
    define \<^marker>\<open>provenance human\<close> a2' where "a2' = hd p2"
    assume \<^marker>\<open>provenance human\<close> quot_aug_path: "distinct (u # p2)" "path (quotG E) (u # p2)"
    assume \<^marker>\<open>provenance human\<close> p2_subset_s: "set p2 \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)" "path E C"
    assume \<^marker>\<open>provenance human\<close> quot: "s = (Vs E) - set C"
    assume \<^marker>\<open>provenance human\<close> p2_nempty: "p2 \<noteq> []"
    assume choose_vert_works: "chv \<in> set C" "{hd p2, chv} \<in> E"
    define \<^marker>\<open>provenance human\<close> p2' where "p2' = tl p2"
    have \<^marker>\<open>provenance human\<close> Cons: "p2 = a2' # p2'"
      unfolding a2'_def p2'_def
      using \<open>p2 \<noteq> []\<close>
      by auto
    show \<^marker>\<open>provenance human\<close> "distinct (find_pfx ((=) chv) C @ p2)"
      unfolding distinct_append
      using quot_aug_path(1) quot find_pfx_subset p2_subset_s
        distinct_find_pfx_cycle[OF cycle(1) choose_vert_works(1) cycle(3)]
      by (auto dest: subsetD[OF find_pfx_subset])
  qed

  have \<^marker>\<open>provenance ai\<close> append_works: "\<And>p1 p2. {u, hd p2} \<notin> quotG M \<Longrightarrow> set p1 \<subseteq> s \<Longrightarrow> set p2 \<subseteq> s \<Longrightarrow>
      matching_augmenting_path (quotG M) (p1 @ u # p2) \<Longrightarrow> distinct (p1 @ u # p2) \<Longrightarrow>
      path (quotG E) (p1 @ u # p2) \<Longrightarrow> 2 \<le> length p1 \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow>
      distinct (stem2vert_path adj mate C (hd p2) @ p2) \<Longrightarrow>
      distinct (p1 @ stem2vert_path adj mate C (hd p2) @ p2)"
  proof-
    fix \<^marker>\<open>provenance human\<close> p1 p2 ::"'a list"
    assume \<^marker>\<open>provenance human\<close> up2_nin_M: "{u, hd p2} \<notin> quotG M"
    assume \<^marker>\<open>provenance human\<close> p1_subset_s: "set p1 \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> p2_subset_s: "set p2 \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> quot_aug_path: "matching_augmenting_path (quotG M) (p1 @ u # p2)"  "distinct (p1 @ u # p2)" "path (quotG E) (p1 @ u # p2)"
    assume \<^marker>\<open>provenance human\<close> len_ge_2: "length p1 \<ge> 2"
    assume \<^marker>\<open>provenance human\<close> p2_nempty: "p2 \<noteq> []"
    assume \<^marker>\<open>provenance human\<close> that: "distinct (stem2vert_path adj mate C (hd p2) @ p2)"
    show \<^marker>\<open>provenance human\<close> "distinct (p1 @ stem2vert_path adj mate C (hd p2) @ p2)"
    proof-
      have p1_nempty: "p1 \<noteq> []"
        using len_ge_2
        by auto
      show ?thesis
        unfolding distinct_append
        using quot_aug_path(2) that quot stem2vert_path_subset p1_subset_s p2_subset_s
        by fastforce
    qed
  qed  

  have \<^marker>\<open>provenance ai\<close> replace_cycle_cases: "\<And>p1 p2. set p2 \<subseteq> s \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow>
      {u, hd p2} \<notin> quotG M \<or> p1 = [] \<Longrightarrow> distinct (u # p2) \<Longrightarrow> path (quotG E) (u # p2) \<Longrightarrow>
      (distinct (stem2vert_path adj mate C (hd p2) @ p2) \<Longrightarrow>
        distinct (p1 @ stem2vert_path adj mate C (hd p2) @ p2)) \<Longrightarrow>
      distinct (replace_cycle adj mate C p1 p2)"
  proof-
    fix \<^marker>\<open>provenance human\<close> p1 p2::"'a list"
    assume \<^marker>\<open>provenance human\<close> p2_subset_s: "set p2 \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> p2_nempty: "p2 \<noteq> []" "({u, hd p2} \<notin> quotG M) \<or> p1 = []"
    assume \<^marker>\<open>provenance human\<close> quot_aug_path:  "distinct (u # p2)" (is ?p2) "path (quotG E) (u # p2)" (is ?p3)
    assume \<^marker>\<open>provenance human\<close> distinct_app: "distinct (p1 @ stem2vert_path adj mate C (hd p2) @ p2)"
      if  "distinct (stem2vert_path adj mate C (hd p2) @ p2)"
    show \<^marker>\<open>provenance human\<close> "distinct (replace_cycle adj mate C p1 p2)"
    proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert adj C (hd p2))) C)) \<in> M")
      case T3: True
      then have i: "distinct (stem2vert_path adj mate C (hd p2) @ p2)"
        using \<^marker>\<open>provenance ai\<close> d1[OF quot_aug_path p2_subset_s cycle quot(1) p2_nempty(1) choose_vert_works_3[OF cycle(3) quot_aug_path(1) quot_aug_path(2) p2_nempty(1) quot(1)]]
        by (simp add: stem2vert_path_def' Let_def)
      show ?thesis
        unfolding replace_cycle_def' Let_def
        using p2_nempty i distinct_app[OF i]
        by (auto split: if_splits)
    next
      define chv where "chv = (choose_con_vert adj C (hd p2))"
      case F1: False
      show ?thesis
      proof(cases "chv = last C")
        case T2: True
        then have i: "distinct (stem2vert_path adj mate C (hd p2) @ p2)"
          using \<^marker>\<open>provenance ai\<close> d1[OF quot_aug_path p2_subset_s cycle quot(1) p2_nempty(1) choose_vert_works_3[OF cycle(3) quot_aug_path(1) quot_aug_path(2) p2_nempty(1) quot(1)]]
          by \<^marker>\<open>provenance ai\<close> (simp add: stem2vert_path_eq_pfx[OF odd_cycle_nempty(1)[OF cycle(1)]] chv_def[symmetric])
        show ?thesis
          unfolding replace_cycle_def' Let_def
          using p2_nempty i distinct_app[OF i]
          by (auto split: if_splits)
      next
        case F2: False
        have choose_vert_works: "chv \<in> set C"
          unfolding chv_def
          using choose_vert_works_3(1)[OF cycle(3) quot_aug_path(1) quot_aug_path(2) p2_nempty(1) quot(1)]
          by \<^marker>\<open>provenance ai\<close> simp
        moreover have "chv \<noteq> hd C"
          using odd_cycleD(3)[OF cycle(1)] F2
          by auto
        ultimately have i: "last (edges_of_path (find_pfx ((=) chv) (rev C))) \<in> M"
          using F1 find_pfx_edges_of_path_alt_list(2)[OF cycle(1-3)]
          using chv_def
          by blast
        have ii: "distinct (tl (rev C))"
          using cycle(3) odd_cycleD(3)[OF cycle(1)] tl_distinct_rev
          by auto
        have iii: "s = Vs E - set (rev C)"
          using quot
          by auto
        have iv: "path E (rev C)"
          using cycle(4)
          by (simp add: rev_path_is_path)
        have cvw: "chv \<in> set (rev C)" "{hd p2, chv} \<in> E"
          using choose_vert_works_3[OF cycle(3) quot_aug_path(1) quot_aug_path(2) p2_nempty(1) quot(1)] chv_def
          by simp_all
        have i: "distinct (stem2vert_path adj mate C (hd p2) @ p2)"
          using F1 d1[OF quot_aug_path p2_subset_s odd_cycle_rev[OF cycle(1)] odd_cycle_rev_alt_list[OF cycle(1,2)] ii iv iii p2_nempty(1) cvw]
          by (simp add: chv_def stem2vert_path_def' Let_def)
        show ?thesis
          unfolding replace_cycle_def' Let_def
          using p2_nempty i distinct_app[OF i]
          by (auto split: if_splits)
      qed
    qed
  qed


  have \<^marker>\<open>provenance ai\<close> replace_cycle_cases_p1: "\<And>p1 p2. set (rev p1) \<subseteq> s \<Longrightarrow>
      {u, hd p2} \<in> quotG M \<or> p2 = [] \<Longrightarrow> p1 \<noteq> [] \<Longrightarrow> distinct (u # rev p1) \<Longrightarrow>
      path (quotG E) (u # rev p1) \<Longrightarrow>
      (distinct (stem2vert_path adj mate C (hd (rev p1)) @ rev p1) \<Longrightarrow>
        distinct (rev p2 @ stem2vert_path adj mate C (last p1) @ rev p1)) \<Longrightarrow>
      distinct (replace_cycle adj mate C p1 p2)"
  proof-
    fix \<^marker>\<open>provenance human\<close> p1 p2::"'a list"
    assume \<^marker>\<open>provenance human\<close> p1_subset_s: "set (rev p1) \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> up2_in_M: "{u, hd p2} \<in> quotG M \<or> p2 = []"
    assume \<^marker>\<open>provenance human\<close> p1_nempty: "p1 \<noteq> []"
    have \<^marker>\<open>provenance human\<close> rev_p1_nempty: "rev p1 \<noteq> []"
      using \<^marker>\<open>provenance ai\<close> p1_nempty
      by \<^marker>\<open>provenance ai\<close> auto
    assume \<^marker>\<open>provenance human\<close> quot_aug_path: "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
    assume \<^marker>\<open>provenance human\<close> distinct_rev: "distinct (rev p2 @ stem2vert_path adj mate C (last p1) @ rev p1)"
      if  "distinct (stem2vert_path adj mate C (hd (rev p1)) @ rev p1)"
    show \<^marker>\<open>provenance human\<close> "distinct (replace_cycle adj mate C p1 p2)"
    proof(cases "last (edges_of_path (find_pfx ((=) (choose_con_vert adj C (hd (rev p1)))) C)) \<in> M")
      case \<^marker>\<open>provenance ai\<close> True
      then \<^marker>\<open>provenance ai\<close> have i: "distinct (stem2vert_path adj mate C (hd (rev p1)) @ rev p1)"
        using \<^marker>\<open>provenance ai\<close> d1[OF quot_aug_path p1_subset_s cycle quot(1) rev_p1_nempty choose_vert_works_3[OF cycle(3) quot_aug_path(1) quot_aug_path(2) rev_p1_nempty quot(1)]]
        by (simp add: stem2vert_path_def' Let_def)
      show \<^marker>\<open>provenance ai\<close> ?thesis
        unfolding \<^marker>\<open>provenance human\<close> replace_cycle_def' Let_def
        using \<^marker>\<open>provenance human\<close> p1_nempty i distinct_rev[OF i] up2_in_M
        by \<^marker>\<open>provenance human\<close> (auto split: if_splits)
    next \<^marker>\<open>provenance ai\<close>
      define chv where "chv = (choose_con_vert adj C (last p1))"
      case \<^marker>\<open>provenance ai\<close> F1: False
      show \<^marker>\<open>provenance ai\<close> ?thesis
      proof \<^marker>\<open>provenance human\<close>(cases "chv = last C")
        case \<^marker>\<open>provenance ai\<close> True
        then \<^marker>\<open>provenance ai\<close> have i: "distinct (stem2vert_path adj mate C (hd (rev p1)) @ rev p1)"
          using \<^marker>\<open>provenance ai\<close> d1[OF quot_aug_path p1_subset_s cycle quot(1) rev_p1_nempty choose_vert_works_3[OF cycle(3) quot_aug_path(1) quot_aug_path(2) rev_p1_nempty quot(1)]]
          by \<^marker>\<open>provenance ai\<close> (simp add: stem2vert_path_eq_pfx[OF odd_cycle_nempty(1)[OF cycle(1)]] chv_def[symmetric] hd_rev)
        show \<^marker>\<open>provenance ai\<close> ?thesis
          unfolding \<^marker>\<open>provenance human\<close> replace_cycle_def' Let_def
          using \<^marker>\<open>provenance human\<close> p1_nempty i distinct_rev[OF i] up2_in_M
          by \<^marker>\<open>provenance human\<close> (auto split: if_splits)
      next \<^marker>\<open>provenance ai\<close>
        case \<^marker>\<open>provenance ai\<close> False
        have choose_vert_works: "chv \<in> set C"
          unfolding chv_def
          using choose_vert_works_3(1)[OF cycle(3) quot_aug_path(1) quot_aug_path(2) rev_p1_nempty quot(1)]
          by (simp add: hd_rev)
        moreover \<^marker>\<open>provenance ai\<close> have "chv \<noteq> hd C"
          using odd_cycleD(3)[OF cycle(1)] False
          by \<^marker>\<open>provenance ai\<close> auto
        ultimately \<^marker>\<open>provenance ai\<close> have i: "last (edges_of_path (find_pfx ((=) chv) (rev C))) \<in> M"
          using F1 find_pfx_edges_of_path_alt_list(2)[OF cycle(1-3) choose_vert_works \<open>chv \<noteq> hd C\<close>]
          by (auto simp: chv_def hd_rev)
        have ii: "distinct (tl (rev C))"
          using cycle(3) odd_cycleD(3)[OF cycle(1)] tl_distinct_rev
          by \<^marker>\<open>provenance ai\<close> auto
        have iii: "s = Vs E - set (rev C)"
          using \<^marker>\<open>provenance ai\<close> quot
          by \<^marker>\<open>provenance ai\<close> auto
        have iv: "path E (rev C)"
          using \<^marker>\<open>provenance ai\<close> cycle(4)
          by (simp add: rev_path_is_path)
        have cvw: "chv \<in> set (rev C)" "{hd (rev p1), chv} \<in> E"
          using choose_vert_works_3[OF cycle(3) quot_aug_path(1) quot_aug_path(2) rev_p1_nempty quot(1)] chv_def
          by (simp_all add: hd_rev)
        have i: "distinct (stem2vert_path adj mate C (hd (rev p1)) @ rev p1)"
          using F1 d1[OF quot_aug_path p1_subset_s odd_cycle_rev[OF cycle(1)] odd_cycle_rev_alt_list[OF cycle(1,2)] ii iv iii rev_p1_nempty cvw]
          by (simp add: chv_def stem2vert_path_def' Let_def hd_rev)
        show \<^marker>\<open>provenance ai\<close> ?thesis
          unfolding \<^marker>\<open>provenance human\<close> replace_cycle_def' Let_def
          using \<^marker>\<open>provenance human\<close> p1_nempty i distinct_rev[OF i] up2_in_M
          by \<^marker>\<open>provenance human\<close> (auto split: if_splits)
      qed \<^marker>\<open>provenance ai\<close>
    qed \<^marker>\<open>provenance ai\<close>
  qed \<^marker>\<open>provenance human\<close>
    (*To be able to give up replace_cycle_cases_p1 and use replace_cycle_cases instead of it, we need
    to show that rev (replace_cycle) = replace_cycle.*)

  have "path (quotG E) (u # p2)"
    using path_suff quot_aug_path
    by blast
  then have "set p2 \<subseteq> Vs (quotG E)"
    using quot
    using split_list_first tl_path_is_path
    by (auto intro!: subset_path_Vs dest: tl_path_is_path)
  moreover have u_nin_p2: "u \<notin> set p2"
    using quot_aug_path
    by auto
  ultimately have p2_subset_s: "set p2 \<subseteq> s"
    by (auto intro: in_quotG_neq_u)
  have "path (quotG E) (p1 @ [u])"
    using quot_aug_path
    by (auto simp: path_pref)
  then have "set p1 \<subseteq> Vs (quotG E)"
    using quot
    using split_list_first tl_path_is_path
    by (auto intro!: subset_path_Vs dest: path_pref)
  moreover have u_nin_p1: "u \<notin> set (rev p1)"
    using quot_aug_path
    by auto
  ultimately have p1_subset_s: "set (rev p1) \<subseteq> s"
    by (auto intro: in_quotG_neq_u)
  have "matching_augmenting_path (quotG M) p'"
    using quot_aug_path(2)
    by simp
  note p'_feats = matching_augmenting_path_feats[OF \<open>matching_augmenting_path (quotG M) p'\<close>]

  show ?thesis
  proof(cases "p1 = []")
    case nil1: True
    show ?thesis
    proof(cases "p2 = []")
      case nil2: True
      then show ?thesis
        using quot_aug_path(1) p'_feats
        by (simp add: nil1 )
    next
      case p2_nempty: False
      show ?thesis
        using replace_cycle_cases[OF p2_subset_s p2_nempty _ ] nil1 p'_feats quot_aug_path
        by (simp add: p2_nempty nil1)
    qed
  next
    case p1_nempty: False
    show ?thesis
    proof(cases "alt_path (quotG M) (u # p2)")
      case T1: True
      show ?thesis
      proof(cases "p2 = []")
        case T2: True
        have quot_aug_path_p1: "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
        proof-
          show ?p2
            using quot_aug_path
            by simp
          show ?p3
            using quot_aug_path
            using T2 rev_path_is_path
            by force
        qed
        have rev_p1_nempty: "rev p1 \<noteq> []"
          using p1_nempty
          by simp
        show ?thesis
          using replace_cycle_cases_p1[OF p1_subset_s _ p1_nempty quot_aug_path_p1] T2
          by (simp add: hd_rev)
      next
        case p2_nempty: False
        then have up2_nin_M: "{u, hd p2} \<notin> quotG M"
          using T1
          by(cases p2; auto simp add: alt_list_step)
        show ?thesis
        proof(cases "length p1 \<ge> 2")
          case len_ge_2: True
          have path_app: "distinct (p1 @ stem2vert_path adj mate C (hd p2) @ p2)"
            if  "distinct (stem2vert_path adj mate C (hd p2) @ p2)"
            using append_works up2_nin_M _ p'_feats(2,4)[unfolded quot_aug_path(1)] len_ge_2 p2_nempty p1_subset_s
            using p2_subset_s quot_aug_path(1) quot_aug_path that
            by auto
          have quot_aug_path_p2: "distinct (u # p2)" (is ?p2) "path (quotG E) (u # p2)" (is ?p3)
          proof-
            show ?p2
              using quot_aug_path
              by simp
            show ?p3
              using quot_aug_path rev_path_is_path  \<open>path (quotG E) (u # p2)\<close>
              by fastforce
          qed
          show ?thesis
            using replace_cycle_cases[OF p2_subset_s p2_nempty _ quot_aug_path_p2 path_app] up2_nin_M
            by blast
        next
          case False                                                                                                    
          then have "length p1 = 1"
            using \<^marker>\<open>provenance ai\<close> p1_nempty
            by (cases p1) (auto simp: Suc_le_eq)
          then obtain a where "p1 = [a]"
            by \<^marker>\<open>provenance ai\<close> (cases p1) auto
          then have False
            using quot_aug_path(1) p'_feats up2_nin_M p2_nempty
            by(auto simp add: alt_list_step neq_Nil_conv)
          then show ?thesis
            by simp
        qed        
      qed
    next
      case p2_nalt: False
      have last_p1_nin: "alt_path (quotG M) (p1 @ [u])" (is ?p1)
        "last (edges_of_path (p1 @ [u])) \<notin> quotG M" (is ?p2)
      proof-
        have rw: "edges_of_path p' = (edges_of_path (p1 @ [u])) @ edges_of_path (u # p2)"
          using edges_of_path_append_2 quot_aug_path(1)
          by fastforce
        have eop_nempty: "edges_of_path (p1 @ [u]) \<noteq> []"
          using \<^marker>\<open>provenance ai\<close> p1_nempty
          by (cases p1) (auto simp: edges_of_path_nempty)
        show ?p1 ?p2
          using alt_list_append_1'[OF p'_feats(2)[unfolded rw] eop_nempty] p2_nalt
          by blast+
      qed
      have up2_nin_M: "{last p1 , u} \<notin> quotG M"
      proof-
        have "last (edges_of_path (p1 @ [u])) = {last p1, u}"
          using p1_nempty
          by (simp add: edges_of_path_snoc[symmetric] p1_nempty)
        then show ?thesis 
          using last_p1_nin
          by auto
      qed
      have rev_p1_nempty: "rev p1 \<noteq> []"
        using p1_nempty
        by auto
      have up2_in_M: "{u, hd p2} \<in> quotG M" if "p2 \<noteq> []"
        using p'_feats(2)
        unfolding rw4[OF p1_nempty that] quot_aug_path(1)
        using alt_list_append_1'' p2_nalt up2_nin_M
        by \<^marker>\<open>provenance ai\<close> fastforce
      show ?thesis
      proof(cases "length p2 \<ge> 2")
        case len_p2_ge_2: True
        have app_works: "distinct (rev p2 @ stem2vert_path adj mate C (last p1) @ rev p1)"
          if  "distinct (stem2vert_path adj mate C (last p1) @ rev p1)"
          unfolding hd_rev[symmetric]
        proof(rule append_works, goal_cases)
          case \<^marker>\<open>provenance ai\<close> 1
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> up2_nin_M
            by \<^marker>\<open>provenance human\<close> (simp add: hd_rev p1_nempty insert_commute)
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 2
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> p2_subset_s
            by \<^marker>\<open>provenance human\<close> auto
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 3
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> p1_subset_s
            by \<^marker>\<open>provenance human\<close> auto
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 4
          have "rev p2 @ u # rev p1 = rev p'"
            by (simp add: quot_aug_path(1))
          thus \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> quot_aug_path(1,2) matching_augmenting_path_rev
            by \<^marker>\<open>provenance human\<close> force
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 5
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> quot_aug_path rev_path_is_path
            by \<^marker>\<open>provenance human\<close> fastforce
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 6
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> quot_aug_path rev_path_is_path
            by \<^marker>\<open>provenance human\<close> fastforce
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 7
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> len_p2_ge_2
            by \<^marker>\<open>provenance human\<close> auto
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 8
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> p1_nempty
            by \<^marker>\<open>provenance human\<close> auto
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 9
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> that[unfolded hd_rev[symmetric]] . \<^marker>\<open>provenance human\<close>
        qed \<^marker>\<open>provenance ai\<close>
        have quot_aug_path_p1: "distinct (u # rev p1)" (is ?p2) "path (quotG E) (u # rev p1)" (is ?p3)
        proof-
          show ?p2
            using quot_aug_path
            by simp
          show ?p3
            using quot_aug_path rev_path_is_path  \<open>path (quotG E) (p1 @ [u])\<close>
            by fastforce
        qed
        show "distinct (replace_cycle adj mate C p1 p2)"
          using replace_cycle_cases_p1[OF p1_subset_s _ p1_nempty quot_aug_path_p1 app_works] up2_in_M
          using hd_rev p1_nempty
          by \<^marker>\<open>provenance ai\<close> (auto simp: hd_rev)
      next
        case len_p2_nge_2: False
        show ?thesis
        proof(cases "p2 = []")
          case True
          then have False
            using p2_nalt alt_list.intros(1)
            by auto
          then show ?thesis
            by simp
        next
          case p2_nempty: False
          then have "length p2 = 1"
            using len_p2_nge_2
            by (cases p2) (auto simp: Suc_le_eq)
          then obtain a where "p2 = [a]"
            by \<^marker>\<open>provenance ai\<close> (cases p2) auto
          then have False
          proof \<^marker>\<open>provenance ai\<close>-
            have \<^marker>\<open>provenance human\<close> "{u, a} \<in> quotG M"
              using up2_in_M \<open>p2 = [a]\<close> p2_nempty
              by \<^marker>\<open>provenance ai\<close> auto
            hence \<^marker>\<open>provenance human\<close> "a \<in> Vs (quotG M)"
              by (auto intro: edges_are_Vs insert_commute)
            moreover have "last p' = a"
              using \<^marker>\<open>provenance human\<close> quot_aug_path(1) \<open>p2 = [a]\<close>
              by simp
            ultimately show False
              using \<^marker>\<open>provenance human\<close> p'_feats(4)
              by simp
          qed
          then show ?thesis
            by simp
        qed
      qed
    qed
  qed
qed

lemma hd_nin_last_nin_replace_cycle:
  assumes cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)" "path E C" and
    quot_aug_path: "p' = (p1 @ u # p2)" "graph_augmenting_path (quotG E) (quotG M) p'" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"(*  and
    graph: "dblton_graph E"*)
  shows "hd (replace_cycle adj mate C p1 p2) \<notin> Vs M \<and> last (replace_cycle adj mate C p1 p2) \<notin> Vs M"
proof-
  have \<^marker>\<open>provenance ai\<close> d1: "\<And>C p2. matching_augmenting_path (quotG M) (u # p2) \<Longrightarrow> set p2 \<subseteq> s \<Longrightarrow>
      odd_cycle C \<Longrightarrow> alt_path M C \<Longrightarrow> distinct (tl C) \<Longrightarrow> s = Vs E - set C \<Longrightarrow>
      p2 \<noteq> [] \<Longrightarrow>
      hd (stem2vert_path adj mate C (hd p2) @ p2) \<notin> Vs M \<and>
      last (stem2vert_path adj mate C (hd p2) @ p2) \<notin> Vs M"
  proof-
    fix \<^marker>\<open>provenance human\<close> C fix \<^marker>\<open>provenance human\<close> p1 p2::"'a list"
    define \<^marker>\<open>provenance human\<close> a2' where "a2' = hd p2"
    assume \<^marker>\<open>provenance human\<close> quot_aug_path: "matching_augmenting_path (quotG M) (u # p2)"
    assume \<^marker>\<open>provenance human\<close> p2_subset_s: "set p2 \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)"
    assume \<^marker>\<open>provenance human\<close> quot: "s = (Vs E) - set C"
    interpret Lc: quot_lift E s u adj mate M C
      by (unfold_locales; (rule adj_E mate_M M_subset_E u_fresh | rule quot | rule odd_cycleD(3)[OF cycle(1)])+)
    assume \<^marker>\<open>provenance human\<close> p2_nempty: "p2 \<noteq> []"
    define \<^marker>\<open>provenance human\<close> p2' where "p2' = tl p2"
    have \<^marker>\<open>provenance human\<close> Cons: "p2 = a2' # p2'"
      unfolding a2'_def p2'_def
      using \<open>p2 \<noteq> []\<close>
      by auto
    have \<^marker>\<open>provenance human\<close> hd_stem2vert_path_nin_append: "hd (stem2vert_path adj mate C a2' @ a2' # p2') = hd (stem2vert_path adj mate C a2' @ [a2'])"
      by (simp add: hd_append)
    define \<^marker>\<open>provenance human\<close> chv where "chv = (choose_con_vert adj C a2')"
    show \<^marker>\<open>provenance human\<close> "hd (stem2vert_path adj mate C (hd p2) @ p2) \<notin> Vs M \<and> last (stem2vert_path adj mate C (hd p2) @ p2) \<notin> Vs M"
    proof(intro conjI, goal_cases)
      case \<^marker>\<open>provenance ai\<close> 1
      show \<^marker>\<open>provenance ai\<close> ?case
      proof \<^marker>\<open>provenance human\<close>-
        have "hd (stem2vert_path adj mate C (hd p2) @ p2) = hd C"
          using \<^marker>\<open>provenance ai\<close> Lc.hd_stem2vert_path[OF odd_cycle_nempty(1)[OF cycle(1)], of "hd p2"]
            Lc.hd_stem2vert_nempty[OF odd_cycle_nempty(1)[OF cycle(1)], of "hd p2"]
            odd_cycleD(3)[OF cycle(1)]
          by (simp add: hd_append2)
        then show ?thesis
          using matching_augmenting_path_feats(3)[OF quot_aug_path(1)]
                quot
          using cycle(1-3) graph matching(1) matching(2) odd_cycleD(3) not_in_quot_matching_not_in_matching
          by fastforce
      qed
    next \<^marker>\<open>provenance ai\<close>
      case \<^marker>\<open>provenance ai\<close> 2
      show \<^marker>\<open>provenance ai\<close> ?case
      proof \<^marker>\<open>provenance human\<close>-
        have "last (stem2vert_path adj mate C (hd p2) @ p2) = last p2"
          using p2_nempty
          by simp
        then show ?thesis
        proof \<^marker>\<open>provenance ai\<close>-
          have "last p2 \<in> s"
            using \<^marker>\<open>provenance human\<close> p2_nempty p2_subset_s
            by \<^marker>\<open>provenance human\<close> (auto intro: last_in_set)
          hence \<^marker>\<open>provenance human\<close> "last p2 \<in> Vs M \<longleftrightarrow> last p2 \<in> Vs (quotG M)"
            using \<^marker>\<open>provenance ai\<close> vert_in_graph_iff_in_quot_diff_u M_subset_E
            by \<^marker>\<open>provenance ai\<close> blast
          thus ?thesis
            using \<^marker>\<open>provenance human\<close> matching_augmenting_path_feats(4)[OF quot_aug_path(1)] p2_nempty
              \<open>last (stem2vert_path adj mate C (hd p2) @ p2) = last p2\<close>
            by simp
        qed
      qed \<^marker>\<open>provenance ai\<close>
    qed \<^marker>\<open>provenance ai\<close>
  qed

  have \<^marker>\<open>provenance ai\<close> append_works: "\<And>p1 p2 p3. set p1 \<subseteq> s \<Longrightarrow> set p2 \<subseteq> s \<Longrightarrow>
      matching_augmenting_path (quotG M) (p1 @ u # p2) \<Longrightarrow> p1 \<noteq> [] \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow>
      hd (p1 @ p3 @ p2) \<notin> Vs M \<and> last (p1 @ p3 @ p2) \<notin> Vs M"
  proof-
    fix \<^marker>\<open>provenance human\<close> p1 p2 p3 ::"'a list"
    assume \<^marker>\<open>provenance human\<close> p1_subset_s: "set p1 \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> p2_subset_s: "set p2 \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> quot_aug_path: "matching_augmenting_path (quotG M) (p1 @ u # p2)"
    assume \<^marker>\<open>provenance human\<close> p1_nempty: "p1 \<noteq> []"
    assume \<^marker>\<open>provenance human\<close> p2_nempty: "p2 \<noteq> []"
    show \<^marker>\<open>provenance human\<close> "hd (p1 @ p3 @ p2) \<notin> Vs M \<and> last (p1 @ p3 @ p2) \<notin> Vs M"
    proof(intro conjI, goal_cases)
      case \<^marker>\<open>provenance ai\<close> 1
      show \<^marker>\<open>provenance ai\<close> ?case
      proof-
        have "hd p1 \<in> s"
          using \<^marker>\<open>provenance human\<close> p1_nempty p1_subset_s
          by \<^marker>\<open>provenance human\<close> (auto intro: hd_in_set)
        hence \<^marker>\<open>provenance human\<close> "hd p1 \<in> Vs M \<longleftrightarrow> hd p1 \<in> Vs (quotG M)"
          using \<^marker>\<open>provenance ai\<close> vert_in_graph_iff_in_quot_diff_u M_subset_E
          by \<^marker>\<open>provenance ai\<close> blast
        thus ?thesis
          using \<^marker>\<open>provenance human\<close> matching_augmenting_path_feats(3)[OF quot_aug_path(1)] p1_nempty
          by \<^marker>\<open>provenance human\<close> (simp add: hd_append2)
      qed
    next \<^marker>\<open>provenance ai\<close>
      case \<^marker>\<open>provenance ai\<close> 2
      show \<^marker>\<open>provenance ai\<close> ?case
      proof-
        have "last p2 \<in> s"
          using \<^marker>\<open>provenance human\<close> p2_nempty p2_subset_s
          by \<^marker>\<open>provenance human\<close> (auto intro: last_in_set)
        hence \<^marker>\<open>provenance human\<close> "last p2 \<in> Vs M \<longleftrightarrow> last p2 \<in> Vs (quotG M)"
          using \<^marker>\<open>provenance ai\<close> vert_in_graph_iff_in_quot_diff_u M_subset_E
          by \<^marker>\<open>provenance ai\<close> blast
        thus ?thesis
          using \<^marker>\<open>provenance human\<close> matching_augmenting_path_feats(4)[OF quot_aug_path(1)] p2_nempty
          by simp
      qed
    qed \<^marker>\<open>provenance ai\<close>
  qed

  have \<^marker>\<open>provenance ai\<close> replace_cycle_cases: "\<And>p1 p2. set p2 \<subseteq> s \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow>
      (\<And>p3. hd (p1 @ p3 @ p2) \<notin> Vs M \<and> last (p1 @ p3 @ p2) \<notin> Vs M) \<Longrightarrow>
      hd (replace_cycle adj mate C p1 p2) \<notin> Vs M \<and> last (replace_cycle adj mate C p1 p2) \<notin> Vs M"
  proof-
    fix \<^marker>\<open>provenance human\<close> p1 p2::"'a list"
    assume \<^marker>\<open>provenance human\<close> p2_subset_s: "set p2 \<subseteq> s"
    assume \<^marker>\<open>provenance human\<close> p2_nempty: "p2 \<noteq> []"
    assume \<^marker>\<open>provenance human\<close> nin_app: "hd (p1 @ p3 @ p2) \<notin> Vs M \<and> last (p1 @ p3 @ p2) \<notin> Vs M" for p3
    show \<^marker>\<open>provenance human\<close> "hd (replace_cycle adj mate C p1 p2) \<notin> Vs M \<and> last (replace_cycle adj mate C p1 p2) \<notin> Vs M"
      unfolding replace_cycle_def' Let_def
      using p2_nempty nin_app
      by (auto simp: hd_rev last_rev split: if_splits)
  qed

  have "matching_augmenting_path (quotG M) p'" "path (quotG E) p'"
    using quot_aug_path(2)
    by simp+
  note p'_feats = matching_augmenting_path_feats[OF \<open>matching_augmenting_path (quotG M) p'\<close>]

  have "path (quotG E) (u # p2)"
    using path_suff \<open>path (quotG E) p'\<close> quot_aug_path(1)
    by auto
  then have "set p2 \<subseteq> Vs (quotG E)"
    using quot
    using split_list_first tl_path_is_path
    by (auto intro!: subset_path_Vs dest: tl_path_is_path)
  moreover have u_nin_p2: "u \<notin> set p2"
    using quot_aug_path
    by auto
  ultimately have p2_subset_s: "set p2 \<subseteq> s"
    by (auto intro: in_quotG_neq_u)
  have "path (quotG E) (p1 @ [u])"
    using quot_aug_path
    by (auto simp: path_pref)
  then have "set p1 \<subseteq> Vs (quotG E)"
    using quot
    using split_list_first tl_path_is_path
    by (auto intro!: subset_path_Vs dest: path_pref)
  moreover have u_nin_p1: "u \<notin> set (rev p1)"
    using quot_aug_path
    by auto
  ultimately have p1_subset_s: "set (rev p1) \<subseteq> s"
    by (auto intro: in_quotG_neq_u)
  show ?thesis
  proof(cases "p1 = []")
    case nil1: True
    show ?thesis
    proof(cases "p2 = []")
      case nil2: True
      then show ?thesis
        using p'_feats quot_aug_path(1)
        by (simp add: nil1)
    next
      case p2_nempty: False
      show ?thesis
        using nil1 p'_feats quot_aug_path
        using cycle(1-3) d1 p2_nempty p2_subset_s quot replace_cycle_def'
        by auto
    qed
  next
    case p1_nempty: False
    show ?thesis
    proof(cases "p2 = []")
      case T2: True
      have rev_p1_nempty: "rev p1 \<noteq> []"
        using p1_nempty
        by simp
      show ?thesis
      proof \<^marker>\<open>provenance ai\<close>-
        have \<^marker>\<open>provenance human\<close> mp: "matching_augmenting_path (quotG M) (u # rev p1)"
          using graph_augmenting_path_feats(1)[OF quot_aug_path(2)] quot_aug_path(1) T2
            matching_augmenting_path_rev[of "quotG M" "p1 @ [u]"]
          by \<^marker>\<open>provenance ai\<close> simp
        show ?thesis
          using \<^marker>\<open>provenance human\<close> d1[OF mp p1_subset_s cycle(1-3) quot rev_p1_nempty] T2 p1_nempty
          by \<^marker>\<open>provenance human\<close> (simp add: replace_cycle_def' hd_rev)
      qed
    next
      case p2_nempty: False
      show ?thesis
        proof(rule replace_cycle_cases, goal_cases)
          case \<^marker>\<open>provenance ai\<close> 1
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> p2_subset_s
            by \<^marker>\<open>provenance human\<close> auto
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 2
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> p2_nempty
            by \<^marker>\<open>provenance human\<close> auto
        next \<^marker>\<open>provenance ai\<close>
          case \<^marker>\<open>provenance ai\<close> 3
          show \<^marker>\<open>provenance ai\<close> ?case
            using \<^marker>\<open>provenance human\<close> append_works p1_nempty p1_subset_s p2_nempty p2_subset_s quot_aug_path(1) quot_aug_path(2)
            by \<^marker>\<open>provenance human\<close> auto
        qed
    qed
  qed
qed \<^marker>\<open>provenance ai\<close>

lemma length_replace_cycle_works:
  assumes cycle: "odd_cycle C" and
    quot_aug_path: "p' = (p1 @ u # p2)" "matching_augmenting_path (quotG M) p'"
  shows "2 \<le> length (replace_cycle adj mate C p1 p2)"
proof-
  have "p1 \<noteq> [] \<or> p2 \<noteq> []"
    using quot_aug_path(1,2)
    by(auto simp add: matching_augmenting_path_def split: if_splits)
  moreover have "C \<noteq> []"
    using odd_cycle_nempty[OF cycle(1)].
  ultimately show ?thesis
    using \<^marker>\<open>provenance ai\<close> length_replace_cycle[of p1 p2]
    by (cases p1; cases p2; auto)
qed

text\<open>Lifting a path in case it intersects with a contracted vertex\<close>

lemma replace_cycle_works:
  assumes cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)"
                 "path E C" and
    quot_aug_path: "p' = (p1 @ u # p2)" "graph_augmenting_path (quotG E) (quotG M) p'" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"(*  and
    graph: "dblton_graph E"*)
  shows "matching_augmenting_path M (replace_cycle adj mate C p1 p2) \<and> path E (replace_cycle adj mate C p1 p2) \<and> distinct (replace_cycle adj mate C p1 p2)"
  unfolding matching_augmenting_path_def
  by(intro conjI path_replace_cycle[OF assms]
  distinct_replace_cycle[OF assms]
  conjunct1[OF hd_nin_last_nin_replace_cycle[OF assms]]
  conjunct2[OF hd_nin_last_nin_replace_cycle[OF assms]]
  alt_list_replace_cycle[OF assms(1-3) assms(5-9)]  
  subset_path_Vs assms length_replace_cycle_works[OF _ quot_aug_path(1)]
  graph_augmenting_path_feats[OF quot_aug_path(2)])

text\<open>A function to find the shortest prefix of a list which has a given vertex.\<close>

text\<open>The function the refines an augmenting path from a quotient graph to a concrete one.\<close>

theorem refine:
  assumes cycle: "odd_cycle C" "alt_path M C" "distinct (tl C)" "path E C" and
    quot_aug_path: "graph_augmenting_path (quotG E) (quotG M) p'" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"(*  and
    graph: "dblton_graph G"*)
  shows "graph_augmenting_path E M (refine adj mate u C p')"
proof(cases "u \<in> set p'")
  define aug_path where "aug_path = (replace_cycle adj mate C (fst (pref_suf [] u p')) (snd (pref_suf [] u p')))"
  case True
  then have "matching_augmenting_path M aug_path \<and> path E aug_path \<and> distinct aug_path"
    unfolding aug_path_def
    by (intro replace_cycle_works[OF cycle _ quot_aug_path matching quot] pref_suf_works)
  then show ?thesis
    using True
    unfolding refine_def aug_path_def
    by auto
next
  case False
  then have p_subset_s: "set p' \<subseteq> s"
    using quot(1) mem_path_Vs in_quotG_neq_u quot_aug_path
    by \<^marker>\<open>provenance ai\<close> fast
  then have "path E p'"
    using quot_aug_path
    using qug_path_iff_case_1_ii quot(1)
    by blast
  then show ?thesis
    using quot_aug_path qug_path_iff_case_1_i p_subset_s \<open>M \<subseteq> E\<close>
    by (simp add: False refine_def)
qed

theorem refine_works:
  assumes cycle: "blossom E M stem C" and
    quot_aug_path: "graph_augmenting_path (quotG E) (quotG M) p'" and 
    matching: "matching M" "M \<subseteq> E" and
    quot: "s = (Vs E) - set C"
  shows "graph_augmenting_path E M (refine adj mate u C p')"
proof-

  have *: "tl C = butlast (tl C) @ [last C]"
    using odd_cycleD[OF match_blossomD(3)[OF blossomD(2)[OF cycle]]]
    by (fastforce simp add: eval_nat_numeral Suc_le_length_iff dest!:)

  have butlast_nempty_conv: "butlast xs = x # xs' \<longleftrightarrow> (\<exists>x'. xs = x # xs' @ [x'])" for x xs xs'
    by(cases xs) (auto simp add: snoc_eq_iff_butlast')

  have "distinct (tl (butlast C))"
    using match_blossomD[OF blossomD(2)[OF cycle]] match_blossom_alt_cycle[OF blossomD(2)[OF cycle]]
    by (auto simp add: \<open>alt_path M C\<close> distinct_tl dest!: blossomD odd_cycleD)
  moreover have "hd C \<notin> set (tl (butlast C))"
    using match_blossomD[OF blossomD(2)[OF cycle]]
    by(cases "(butlast C)") (auto simp add: butlast_nempty_conv)
  ultimately have "distinct (tl C)"
    using odd_cycleD(3)[OF match_blossomD(3)[OF blossomD(2)[OF cycle]]]
    by (subst *; simp add: butlast_tl)
  moreover have "path E C"
    using cycle path_suff'
    by auto
  ultimately show ?thesis
    using match_blossomD[OF blossomD(2)[OF cycle]] match_blossom_alt_cycle[OF blossomD(2)[OF cycle]]
    by \<^marker>\<open>provenance ai\<close> (intro refine[OF _ _ _ _ assms(2-)]; auto)
qed

end

end \<^marker>\<open>provenance ai\<close>


