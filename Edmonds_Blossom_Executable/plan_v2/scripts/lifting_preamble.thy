provenance ai

text \<open>The functions that lift an augmenting path of a quotient graph to the graph. They are the
  functions of the same names of the quotient locale, made executable: the choice of a cycle
  vertex adjacent to a given vertex takes the first such vertex of the cycle list (adjacency is a
  parameter \<open>adj\<close>), and membership of an edge in the matching is tested with its mate function
  (a parameter \<open>mate\<close>). The locale \<open>quot_lift\<close> ties the two parameters to the graph and to the
  matching.\<close>

definition choose_con_vert :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "choose_con_vert adj C v = (case find (adj v) C of Some x \<Rightarrow> x | None \<Rightarrow> hd C)"

definition last_edge_matched :: "('a \<Rightarrow> 'a option) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "last_edge_matched mate xs = (case rev xs of b # a # _ \<Rightarrow> mate a = Some b | _ \<Rightarrow> True)"

definition stem2vert_path ::
  "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "stem2vert_path adj mate C v =
     (let find_pfx' = (\<lambda>C'. find_pfx ((=) (choose_con_vert adj C v)) C') in
      if last_edge_matched mate (find_pfx' C) then find_pfx' C else find_pfx' (rev C))"

definition matched_to_cycle :: "('a \<Rightarrow> 'a option) \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool" where
  "matched_to_cycle mate C x =
     (x \<notin> set C \<and> (case mate x of Some c \<Rightarrow> c \<in> set C | None \<Rightarrow> False))"

definition replace_cycle ::
  "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace_cycle adj mate C p1 p2 =
     (if p1 = [] then stem2vert_path adj mate C (hd p2) @ p2
      else if p2 = [] then stem2vert_path adj mate C (last p1) @ rev p1
      else if \<not> matched_to_cycle mate C (hd p2) then p1 @ stem2vert_path adj mate C (hd p2) @ p2
      else rev p2 @ stem2vert_path adj mate C (last p1) @ rev p1)"

provenance human

text\<open>A function to find the shortest prefix of a list which has a given vertex.\<close>

@@PREF_SUF@@

provenance ai

definition refine ::
  "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "refine adj mate u C p =
     (if u \<in> set p then replace_cycle adj mate C (fst (pref_suf [] u p)) (snd (pref_suf [] u p))
      else p)"

lemmas [code] = choose_con_vert_def last_edge_matched_def stem2vert_path_def matched_to_cycle_def
  replace_cycle_def refine_def

lemma last_edges_of_path_snoc2: "last (edges_of_path (ys @ [a, b])) = {a, b}"
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

locale quot_lift = quot E s u for E :: "'a set set" and s u +
  fixes adj :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and mate :: "'a \<Rightarrow> 'a option" and M :: "'a set set"
    and C :: "'a list"
  assumes adj_E: "\<And>v w. adj v w \<longleftrightarrow> {v, w} \<in> E"
      and mate_M: "\<And>v w. mate v = Some w \<longleftrightarrow> {v, w} \<in> M"
      and M_subset_E: "M \<subseteq> E"
      and s_cycle: "s = Vs E - set C"
      and u_fresh: "u \<notin> Vs E"
      and hd_last_cycle: "hd C = last C"
begin

lemma choose_con_vert_props:
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

lemma last_edge_matched_iff:
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

lemma matched_to_cycle_iff:
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

text \<open>In the locale, the lifting functions satisfy the defining equations of their
  counterparts in the original formalisation, in which membership in the matching is tested
  directly.\<close>

lemma stem2vert_path_def':
  "stem2vert_path adj mate C v =
     (let find_pfx' = (\<lambda>C'. find_pfx ((=) (choose_con_vert adj C v)) C') in
      if last (edges_of_path (find_pfx' C)) \<in> M then find_pfx' C else find_pfx' (rev C))"
proof-
  define w where "w = choose_con_vert adj C v"
  define pfx where "pfx = find_pfx ((=) w) C"
  have pfx_rev: "find_pfx ((=) w) (rev C) = pfx" if "length pfx < 2"
  proof(cases C)
    case Nil
    then show ?thesis
      by (simp add: pfx_def)
  next
    case (Cons c cs)
    have "hd (rev C) = c"
    proof-
      have "hd (rev C) = last C"
        by (rule hd_rev)
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
        by (cases cs) (auto simp: pfx_def split: if_splits)
      then show ?thesis
        using Cons False
        by (simp add: pfx_def)
    qed
  qed
  show ?thesis
  proof(cases "2 \<le> length pfx")
    case True
    then show ?thesis
      by (simp add: stem2vert_path_def Let_def w_def[symmetric] pfx_def[symmetric]
                    last_edge_matched_iff)
  next
    case False
    hence "last_edge_matched mate pfx"
      by (cases pfx rule: rev_cases) (auto simp: last_edge_matched_def length_Suc_conv Suc_le_eq)
    then show ?thesis
      using pfx_rev False
      by (simp add: stem2vert_path_def Let_def w_def[symmetric] pfx_def[symmetric])
  qed
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
end

provenance human
