theory Rooted_Arborescense
  imports Rooted_Arborescense_Defs
begin

named_theorems parent_walk_simps

subsection \<open>Threaded tree with subtree sizes (the @{text last}/@{text size} representation)\<close>

text \<open>
  We replace the @{text fst_out} field of the old @{text thread_invar} by two fields:
  \<^item> @{text lst}: for each vertex, the \<^emph>\<open>rightmost descendant\<close> of its subtree in the thread
    (the last node of its contiguous block).  The old @{text fst_out} is now \<^emph>\<open>derived\<close>:
    @{text "fst_out v = nxt (lst v)"}.
  \<^item> @{text sz}: the size (node count) of each subtree.

  @{text lst} is what makes the thread surgery local (only branches, not whole subtrees,
  change), and @{text sz} lets us find the common ancestor by climbing the smaller subtree,
  with no @{text depth} field.
\<close>

subsection \<open>The edge swap (remove one tree edge, insert another, reversing a path)\<close>

text \<open>
  A network-simplex pivot inserts the edge @{term "(i, j)"} and removes the tree edge
  @{term "(p, the (prnt S p))"}.  Here @{term i} (LEMON's @{text u_in}) is the endpoint of the
  entering arc inside the detached subtree, @{term j} (@{text v_in}) is its new parent, @{term p}
  (@{text u_out}) is the top of the detached subtree (lower endpoint of the leaving arc), and
  @{term jn} (@{text join}) is the apex of the pivot cycle.  Rooted-wise this \<^emph>\<open>reverses the
  parent pointers along the path @{term i} {\isasymdots} @{term p}\<close> and re-attaches @{term i} below
  @{term j}.

  The thread surgery below is a direct port of LEMON's \<open>updateTreeStructure\<close>: every step is
  a constant-time pointer update on @{const thrd}/@{const rvth}/@{const prnt}/@{const lsuc}/
  @{const snum}.  A parent chain is walked \<^emph>\<open>only\<close> in the join computation.
\<close>

paragraph \<open>Path computation --- the only place a parent chain is walked.\<close>

text \<open>Executable root-path (ancestor list) \<open>[v, the (T v), ..., r]\<close>, the code-level counterpart
      of @{term "follow T v"}.  This is the one parent-chain walk allowed in the functions; it is
      tail-recursive (the chain length is not structurally bounded).\<close>
partial_function (tailrec) anc_list :: "('a \<rightharpoonup> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow>
  'a list" where
  "anc_list T v acc = (case T v of None \<Rightarrow> rev (v # acc) | Some w \<Rightarrow> anc_list T w (v # acc))"

declare anc_list.simps[code]

definition ancestors :: "('a \<rightharpoonup> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "ancestors T v = anc_list T v []"

lemma follow_dom_ps:
  "parent_spec T \<Longrightarrow> parent_spec_i.follow_dom T w"
  by (rule parent_spec_i.wf_follow_rel)
     (auto simp: parent_spec_def parent_spec_i.follow_rel.simps eq_commute)

lemma parent_walk_induct[consumes 1, case_names step]:
  assumes "parent_spec P" "\<And>u. (\<And>v. P u = Some v \<Longrightarrow> Q v) \<Longrightarrow> Q u"
  shows "Q u"
  by (rule parent_spec_i.follow.pinduct[OF follow_dom_ps[OF assms(1)]])
     (auto intro: assms(2))

lemma follow_ps_simps:
  "parent_spec T \<Longrightarrow> follow T v = (case T v of None \<Rightarrow> [v] | Some w \<Rightarrow> v # follow T
    w)"
  by (simp add: parent_spec_i.follow.psimps[OF follow_dom_ps])

lemma follow_None_ps[parent_walk_simps]:
  "\<lbrakk>parent_spec T; T v = None\<rbrakk> \<Longrightarrow> follow T v = [v]"
  by (subst follow_ps_simps) auto

lemma follow_Some_ps[parent_walk_simps]:
  "\<lbrakk>parent_spec T; T v = Some w\<rbrakk> \<Longrightarrow> follow T v = v # follow T w"
  by (subst follow_ps_simps) auto

lemma follow_ne_ps[parent_walk_simps]:
  "parent_spec T \<Longrightarrow> follow T v \<noteq> []"
  by (subst follow_ps_simps) (auto split: option.splits)

lemma follow_hd_ps[parent_walk_simps]:
  "parent_spec T \<Longrightarrow> hd (follow T v) = v"
  by (subst follow_ps_simps) (auto split: option.splits)

lemma follow_mem_ps[parent_walk_simps]:
  "parent_spec T \<Longrightarrow> v \<in> set (follow T v)"
  by (subst follow_ps_simps) (auto split: option.splits)

lemma follow_distinct_ps[parent_walk_simps]:
  "parent_spec T \<Longrightarrow> distinct (follow T v)"
  by (auto intro: parent.follow_distinct simp: parent_def follow_def)

lemma follow_append_ps:
  "\<lbrakk>parent_spec T; follow T v = p @ u # p'\<rbrakk> \<Longrightarrow> follow T u = u # p'"
  by (auto intro: parent.follow_append simp: parent_def follow_def)

lemma anc_list_acc:
  assumes "parent_spec T"
  shows "anc_list T v acc = rev acc @ follow T v"
  using assms
  by (induction v arbitrary: acc rule: parent_walk_induct;
      subst anc_list.simps; subst follow_ps_simps)
     (auto simp: assms split: option.split)

lemma ancestors_eq_follow:
  "parent_spec T \<Longrightarrow> ancestors T v = follow T v"
  by (simp add: ancestors_def anc_list_acc)

lemma follow_eq_on:
  "\<lbrakk>parent_spec T; parent_spec T'; \<forall>y\<in>set (follow T v). T y = T' y\<rbrakk> \<Longrightarrow>
    follow T v = follow T' v"
  using follow_cong[of T v T']
  by (auto simp: parent_def follow_def follow_dom_ps)

lemma follow_of_rtrancl_parent:
  "\<lbrakk>(a, b) \<in> {(x, y) |x y. Some x = T y}\<^sup>*; parent_spec T\<rbrakk> \<Longrightarrow> a \<in> set
    (follow T b)"
proof(induction rule: rtrancl_induct)
  case (step y z)
  thus ?case
    using follow_Some_ps[of T z y]
    by auto
qed (simp add: follow_mem_ps)

lemma rooted_arborescense_invar_parent_in_V:
  "\<lbrakk>rooted_arborescense_invar r V T; T w = Some w'\<rbrakk> \<Longrightarrow> w' \<in> V"
  by (auto elim!: rooted_arborescense_invarE intro!: dVsI(2)[of w])

lemma rooted_arborescense_invar_child_in_V:
  "\<lbrakk>rooted_arborescense_invar r V T; T w = Some w'\<rbrakk> \<Longrightarrow> w \<in> V"
  by (auto elim!: rooted_arborescense_invarE)

lemma follow_reaches_root:
  assumes "rooted_arborescense_invar r V T"
  shows "\<lbrakk>v \<in> V; v \<noteq> r\<rbrakk> \<Longrightarrow> \<exists>y\<in>set (follow T v). T y = Some r"
  using rooted_arborescense_invar_parent_spec[OF assms]
proof(induction v rule: parent_walk_induct)
  case IH: (step v)
  thus ?case
    using assms rooted_arborescense_invar_parent_in_V[of r V T v]
    by (cases "T v") (auto simp: parent_walk_simps rooted_arborescense_invar_parent_spec[OF assms])
qed

lemma rooted_arborescense_swap_parents:
  assumes "rooted_arborescense_invar r V T" "Some pu = T u" "u \<notin> set (follow T v)" "v \<in> V"
  shows "rooted_arborescense_invar r V (T(u \<mapsto> v))"
    "{(y, x) |x y. Some x = (T(u \<mapsto> v)) y} = {(y, x) |x y. Some x = T y} - {(u, pu)} \<union> {(u, v)}"
proof-
  show "{(y, x) |x y. Some x = (T(u \<mapsto> v)) y} = {(y, x) |x y. Some x = T y} - {(u, pu)} \<union> {(u, v)}"
    using assms(2)[symmetric]
    by auto force
  have "(u, v) \<notin> {(x, y) |x y. Some x = T y}\<^sup>*"
    using assms(1,3) follow_of_rtrancl_parent[of u v T]
    by auto
  hence "(u, v) \<notin> ({(x, y) |x y. Some x = T y} - {(pu, u)})\<^sup>*"
    using rtrancl_mono[OF Diff_subset]
    by blast
  moreover have "{(x, y) |x y. Some x = (T(u \<mapsto> v)) y}
                   = insert (v, u) ({(x, y) |x y. Some x = T y} - {(pu, u)})"
    using assms(2)[symmetric]
    by auto
  ultimately have "parent_spec (T(u \<mapsto> v))"
    using rooted_arborescense_invar_parent_spec[OF assms(1)]
    unfolding parent_spec_def
    by (simp add: wf_insert wf_subset[OF _ Diff_subset])
  moreover have "dVs {(y, x) |x y. Some x = (T(u \<mapsto> v)) y} \<subseteq> V"
    using assms
    by (auto simp: dVs_def split: if_splits
             intro: rooted_arborescense_invar_parent_in_V[OF _ sym]
                    rooted_arborescense_invar_child_in_V[OF _ sym])
  moreover have "V \<subseteq> dVs {(y, x) |x y. Some x = (T(u \<mapsto> v)) y}"
  proof
    fix w
    assume "w \<in> V"
    show "w \<in> dVs {(y, x) |x y. Some x = (T(u \<mapsto> v)) y}"
    proof(cases "w = r")
      case False
      hence "w \<in> dom (T(u \<mapsto> v))"
        using \<open>w \<in> V\<close> assms(1)
        by auto
      thus ?thesis
        by fastforce
    next
      case True
      show ?thesis
      proof(cases "v = r")
        case False
        then obtain y where "y \<in> set (follow T v)" "T y = Some r"
          using follow_reaches_root[OF assms(1,4)]
          by blast
        thus ?thesis
          using assms(3) \<open>w = r\<close>
          by fastforce
      qed (fastforce simp: True)
    qed
  qed
  ultimately show "rooted_arborescense_invar r V (T(u \<mapsto> v))"
    using rooted_arborescense_invar_dom[OF assms(1)] rooted_arborescense_invar_r_in_V[OF assms(1)] assms(2)
    by (intro rooted_arborescense_invarI) auto
qed

lemma arb_invarD:
  assumes "arb_invar r V S"
  shows "rooted_arborescense_invar r V (prnt S)" "parent_spec (prnt S)" "parent_spec (thrd S)"
    "parent_spec (rvth S)" "dom (prnt S) = V - {r}" "r \<in> V" "set (follow (thrd S) r) = V"
    "dom (thrd S) = V - {lsuc S r}" "dom (rvth S) = V - {r}"
    "thrd S v = Some v' \<longleftrightarrow> rvth S v' = Some v" "w \<in> V \<Longrightarrow> lsuc S w \<in> V"
    "w \<in> V \<Longrightarrow> snum S w = card (children (prnt S) w)"
  using assms
  by (auto simp: arb_invar_def)

lemma follow_nth_Suc:
  assumes "parent_spec T" "Suc t < length (follow T v)"
  shows "T (follow T v ! t) = Some (follow T v ! Suc t)"
proof-
  have "follow T (follow T v ! t) = follow T v ! t # drop (Suc t) (follow T v)"
    using assms id_take_nth_drop[of t "follow T v"]
    by (auto intro: follow_append_ps)
  thus ?thesis
    using assms follow_hd_ps[OF assms(1)]
    by (cases "T (follow T v ! t)")
       (auto simp: follow_None_ps follow_Some_ps hd_drop_conv_nth dest!: arg_cong[where f = hd])
qed

lemma follow_eq_of_chain:
  assumes "parent_spec T" "xs \<noteq> []" "\<And>i. Suc i < length xs \<Longrightarrow> T (xs ! i) = Some (xs ! Suc
    i)"
    "T (last xs) = None"
  shows "follow T (hd xs) = xs"
  using assms(2-)
proof(induction xs)
  case (Cons x xs)
  thus ?case
    using assms(1) Cons.prems(2)[of 0] Cons.prems(2)[of "Suc _"]
    by (cases xs) (auto simp: follow_None_ps follow_Some_ps)
qed simp

text \<open>A map whose every edge is a forward step in a \<^emph>\<open>distinct\<close> list is a @{const
  parent_spec},
      because the list position strictly increases along the parent relation.\<close>

lemma parent_spec_of_distinct_chain:
  assumes "distinct xs" "\<And>x y. T x = Some y \<Longrightarrow> \<exists>i. Suc i < length xs \<and> xs ! i = x
    \<and> xs ! Suc i = y"
  shows "parent_spec T"
proof-
  define pos where "pos = (\<lambda>z. THE n. n < length xs \<and> xs ! n = z)"
  have "\<And>n. n < length xs \<Longrightarrow> pos (xs ! n) = n"
    unfolding pos_def
    by (rule the_equality) (auto simp: assms(1) nth_eq_iff_index_eq)
  hence "{(x, y) |x y. Some x = T y} \<subseteq> measure (\<lambda>z. length xs - pos z)"
    by (auto dest!: sym[THEN assms(2)])
  thus ?thesis
    unfolding parent_spec_def
    by (rule wf_subset[OF wf_measure])
qed

lemma parent_spec_reverse_chain:
  assumes "distinct xs"
    "\<And>x y. T x = Some y \<Longrightarrow> \<exists>i. Suc i < length xs \<and> xs ! i = y \<and> xs ! Suc i = x"
  shows "parent_spec T"
proof-
  define pos where "pos = (\<lambda>z. THE n. n < length xs \<and> xs ! n = z)"
  have "\<And>n. n < length xs \<Longrightarrow> pos (xs ! n) = n"
    unfolding pos_def
    by (rule the_equality) (auto simp: assms(1) nth_eq_iff_index_eq)
  hence "{(x, y) |x y. Some x = T y} \<subseteq> measure pos"
    by (auto dest!: sym[THEN assms(2)])
  thus ?thesis
    unfolding parent_spec_def
    by (rule wf_subset[OF wf_measure])
qed

lemma follow_path:
  assumes "parent_spec T" "p \<in> set (follow T i)"
  obtains s k where "s 0 = i" "s k = p" "\<And>t. t < k \<Longrightarrow> T (s t) = Some (s (Suc t))"
    "inj_on s {..k}" "\<And>t. t \<le> k \<Longrightarrow> s t \<in> set (follow T i)"
proof-
  obtain k where "k < length (follow T i)" "follow T i ! k = p"
    using assms(2)
    by (auto simp: in_set_conv_nth)
  thus thesis
    using assms(1) follow_hd_ps[OF assms(1), of i] follow_ne_ps[OF assms(1), of i]
    by (intro that[of "nth (follow T i)" k])
       (auto simp: follow_nth_Suc hd_conv_nth follow_distinct_ps intro!: inj_on_nth)
qed

text \<open>The join (apex / lowest common ancestor) of @{term a} and @{term b}: the first node on
      @{term a}'s root-path that also lies on @{term b}'s root-path.\<close>

definition join_of :: "('a \<rightharpoonup> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "join_of T a b = hd (filter (\<lambda>x. x \<in> set (ancestors T b)) (ancestors T a))"

lemma join_of_follow:
  "parent_spec T \<Longrightarrow> join_of T a b = hd (filter (\<lambda>x. x \<in> set (follow T b)) (follow T a))"
  by (simp add: join_of_def ancestors_eq_follow)

lemma join_of_mem:
  assumes "parent_spec T" "last (follow T a) = last (follow T b)"
  shows "join_of T a b \<in> set (follow T a)" "join_of T a b \<in> set (follow T b)"
proof-
  have "filter (\<lambda>x. x \<in> set (follow T b)) (follow T a) \<noteq> []"
    using last_in_set[OF follow_ne_ps[OF assms(1)], of a] last_in_set[OF follow_ne_ps[OF assms(1)], of b] assms(2)
    by (auto simp: filter_empty_conv)
  thus "join_of T a b \<in> set (follow T a)" "join_of T a b \<in> set (follow T b)"
    using hd_in_set[of "filter (\<lambda>x. x \<in> set (follow T b)) (follow T a)"]
    by (auto simp: join_of_follow[OF assms(1)])
qed

lemma join_of_first:
  assumes "parent_spec T" "x \<in> set (follow T a)" "x \<in> set (follow T b)"
  shows "x \<in> set (follow T (join_of T a b))"
proof-
  obtain ys where "filter (\<lambda>y. y \<in> set (follow T b)) (follow T a) = join_of T a b # ys"
    using assms
    by (cases "filter (\<lambda>y. y \<in> set (follow T b)) (follow T a)")
       (auto simp: join_of_follow filter_empty_conv)
  then obtain us vs where "follow T a = us @ join_of T a b # vs" "\<forall>u\<in>set us. u \<notin> set (follow T b)"
    by (auto simp: filter_eq_Cons_iff)
  thus ?thesis
    using assms follow_append_ps[OF assms(1)]
    by fastforce
qed

lemma ancestor_antisym:
  assumes "parent_spec T" "u \<in> set (follow T v)" "v \<in> set (follow T u)"
  shows "u = v"
proof-
  obtain p1 p2 q1 q2 where "follow T v = p1 @ u # p2" "follow T u = q1 @ v # q2"
    using assms(2,3)
    by (blast dest: split_list)
  moreover hence "follow T u = u # p2" "follow T v = v # q2"
    using follow_append_ps[OF assms(1)]
    by blast+
  ultimately show "u = v"
    by (cases p1) (auto dest!: arg_cong[where f = length])
qed

lemma no_cycle:
  "\<lbrakk>parent_spec T; p \<in> set (follow T i); jn \<in> set (follow T p); jn = join_of T i j; p \<noteq>
    jn\<rbrakk>
     \<Longrightarrow> p \<notin> set (follow T j)"
  using join_of_first[of T p i j] ancestor_antisym[of T p jn]
  by blast

lemma pivot_p_ne_r:
  "\<lbrakk>arb_invar r V S; a \<in> set (follow (prnt S) p); a \<noteq> p\<rbrakk> \<Longrightarrow> p \<noteq> r"
  using follow_None_ps[of "prnt S" r] arb_invarD(2,5)[of r V S]
  by auto

lemma follow_subset_V:
  assumes "rooted_arborescense_invar r V T"
  shows "v \<in> V \<Longrightarrow> set (follow T v) \<subseteq> V"
  using rooted_arborescense_invar_parent_spec[OF assms]
proof(induction v rule: parent_walk_induct)
  case IH: (step v)
  thus ?case
    using assms rooted_arborescense_invar_parent_in_V[of r V T v]
    by (cases "T v") (auto simp: parent_walk_simps rooted_arborescense_invar_parent_spec[OF assms])
qed

lemma children_subset_V:
  assumes "rooted_arborescense_invar r V T" "v \<in> V"
  shows "children T v \<subseteq> V"
  by (insert assms rooted_arborescense_invar_child_in_V[OF assms(1)] follow_None_ps[OF
    rooted_arborescense_invar_parent_spec[OF assms(1)]]; rule subsetI; rename_tac u; case_tac "T u"; auto simp:
    children_def)

subsection \<open>Blocks: the thread is a preorder of the tree (clause J as a contiguity statement)\<close>

text \<open>The \<^emph>\<open>block\<close> of @{term v} is the contiguous thread segment of @{term v}'s subtree: the
      prefix of @{term "follow (thrd S) v"} up to and including @{term "lsuc S v"}.  Under
      @{const arb_invar} (clause J) this prefix is exactly the clause-J witness @{text pre}, and
      its element set is the subtree @{term "children (prnt S) v"}.\<close>
definition block :: "'a ndtree \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "block S v = takeWhile (\<lambda>x. x \<noteq> lsuc S v) (follow (thrd S) v) @ [lsuc S v]"

lemma block_props:
  assumes "arb_invar r V S" "v \<in> V"
  shows "follow (thrd S) v
           = block S v @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    "block S v \<noteq> []" "last (block S v) = lsuc S v" "set (block S v) = children (prnt S) v"
    "hd (block S v) = v"
proof-
  obtain pre where "follow (thrd S) v
           = pre @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
      "pre \<noteq> []" "last pre = lsuc S v" "set pre = children (prnt S) v"
    using assms
    by (auto simp: arb_invar_def)
  moreover hence "block S v = pre"
    using takeWhile_block_aux[OF follow_distinct_ps[OF arb_invarD(3)[OF assms(1)]]]
    by (auto simp: block_def)
  ultimately show "follow (thrd S) v
           = block S v @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    "block S v \<noteq> []" "last (block S v) = lsuc S v" "set (block S v) = children (prnt S) v"
    "hd (block S v) = v"
    using follow_hd_ps[OF arb_invarD(3)[OF assms(1)], of v]
    by (auto simp: hd_append)
qed

lemma follow_trans:
  "\<lbrakk>parent_spec T; c \<in> set (follow T u); v \<in> set (follow T c)\<rbrakk> \<Longrightarrow> v \<in> set
    (follow T u)"
  by (auto dest!: split_list dest: follow_append_ps)

lemma follow_linear:
  assumes "parent_spec T" "a \<in> set (follow T v)" "b \<in> set (follow T v)"
  shows "a \<in> set (follow T b) \<or> b \<in> set (follow T a)"
  by (insert assms follow_append_ps[OF assms(1)]; fastforce dest: split_list)

lemma follow_sub_of_mem:
  "\<lbrakk>parent_spec T; a \<in> set (follow T x)\<rbrakk> \<Longrightarrow> set (follow T a) \<subseteq> set (follow
    T x)"
  by (auto intro: follow_trans)

lemma children_subset:
  "\<lbrakk>parent_spec T; c \<in> children T v\<rbrakk> \<Longrightarrow> children T c \<subseteq> children T v"
  by (auto simp: children_def intro: follow_trans)

subsection \<open>Generic preorder-contiguity engine (surgery-free; clause J's contiguity half)\<close>

text \<open>Preorder key fact 1 --- \<^emph>\<open>ancestors occur earlier\<close>: if @{term xs} is a DFS-preorder of
  tree
      @{term T} (root has no parent; each node's parent lies on the previous node's root-path), then
      every ancestor-or-self of @{term "xs!m"} occurs at some position \<open>\<le> m\<close> in @{term xs}.\<close>

lemma ancestors_earlier:
  assumes "parent_spec T" "T (xs!0) = None"
    "\<And>t. Suc t < length xs \<Longrightarrow> \<exists>a. T (xs!Suc t) = Some a \<and> a \<in> set (follow T
      (xs!t))"
  shows "m < length xs \<Longrightarrow> set (follow T (xs!m)) \<subseteq> (!) xs ` {..m}"
proof(induction m)
  case (Suc t)
  then obtain a where "follow T (xs!Suc t) = xs!Suc t # follow T a"
    "set (follow T a) \<subseteq> set (follow T (xs!t))"
    using assms(3)[of t] follow_sub_of_mem[OF assms(1)] follow_Some_ps[OF assms(1)]
    by blast
  thus ?case
    using Suc image_mono[of "{..t}" "{..Suc t}" "(!) xs"]
    by auto
qed (simp add: assms(2) follow_None_ps[OF assms(1)])

text \<open>Preorder key fact 2 --- \<^emph>\<open>no return\<close>: once a node past the head @{term "ys!0"} fails to
  be a
      descendant of it, every later node also fails.\<close>

lemma not_desc_propagates:
  assumes "parent_spec T" "distinct ys"
    "\<And>t. Suc t < length ys \<Longrightarrow> \<exists>a. T (ys!Suc t) = Some a \<and> a \<in> set (follow T
      (ys!t))"
    "0 < q" "ys!0 \<notin> set (follow T (ys!q))"
  shows "\<lbrakk>q \<le> i; i < length ys\<rbrakk> \<Longrightarrow> ys!0 \<notin> set (follow T (ys!i))"
proof(induction i)
  case (Suc i)
  show ?case
  proof(cases "q = Suc i")
    case False
    then obtain a where "follow T (ys!Suc i) = ys!Suc i # follow T a"
      "set (follow T a) \<subseteq> set (follow T (ys!i))"
      using Suc.prems assms(3)[of i] follow_sub_of_mem[OF assms(1)] follow_Some_ps[OF assms(1)]
      by blast
    thus ?thesis
      using Suc False nth_eq_iff_index_eq[OF assms(2), of 0 "Suc i"]
      by (cases ys) auto
  qed (use assms(5) in simp)
qed (use assms(4) in simp)

text \<open>\<^bold>\<open>Preorder contiguity engine\<close> (generic, surgery-free): if the thread @{term F} realises
  a list
      @{term xs} that is a DFS-preorder of the tree @{term T}, then for every node @{term v} the
      subtree @{term "children T v"} is a non-empty contiguous prefix of @{term "follow F v"} headed
      by @{term v}.  It is the contiguity half of clause J for the post-pivot state.\<close>

lemma preorder_contiguous:
  assumes "parent_spec T" "parent_spec F" "follow F r0 = xs" "T (xs!0) = None"
    "\<And>t. Suc t < length xs \<Longrightarrow> \<exists>a. T (xs!Suc t) = Some a \<and> a \<in> set (follow T
      (xs!t))"
    "v \<in> set xs" "children T v \<subseteq> set xs"
  shows "\<exists>pre suf. follow F v = pre @ suf \<and> set pre = children T v \<and> pre \<noteq> [] \<and> hd pre =
    v"
proof-
  let ?pre = "\<lambda>ys. takeWhile (\<lambda>u. v \<in> set (follow T u)) ys"
  have "distinct xs"
    using follow_distinct_ps[OF assms(2), of r0] assms(3)
    by simp
  obtain pv where "pv < length xs" "xs!pv = v"
    using assms(6)
    by (auto simp: in_set_conv_nth)
  define ys where "ys = drop pv xs"
  have ys: "follow F v = ys" "ys!0 = v" "distinct ys" "ys \<noteq> []"
    "\<And>t. Suc t < length ys \<Longrightarrow> \<exists>a. T (ys!Suc t) = Some a \<and> a \<in> set (follow T
      (ys!t))"
    using assms(2,3,5) follow_append_ps[OF assms(2), of r0 "take pv xs" v "drop (Suc pv) xs"]
          id_take_nth_drop[of pv xs] Cons_nth_drop_Suc[of pv xs] \<open>distinct xs\<close> \<open>pv < length
            xs\<close>
          \<open>xs!pv = v\<close>
    by (auto simp: ys_def)
  have "0 < length (?pre ys)"
    using ys(2,4) follow_mem_ps[OF assms(1), of v]
    by (cases ys) auto
  have "children T v \<subseteq> set (?pre ys)"
  proof
    fix d
    assume "d \<in> children T v"
    moreover then obtain pd where "pd < length xs" "xs!pd = d"
      using assms(7) in_set_conv_nth[of d xs]
      by blast
    moreover hence "pv \<le> pd"
      using \<open>d \<in> children T v\<close> ancestors_earlier[OF assms(1,4,5), of pd] \<open>distinct xs\<close>
        \<open>xs!pv = v\<close>
            \<open>pv < length xs\<close>
      by (auto simp: children_def nth_eq_iff_index_eq)
    moreover have "pd - pv < length (?pre ys)"
      using not_desc_propagates[OF assms(1) ys(3,5) \<open>0 < length (?pre ys)\<close>, of "pd - pv"]
            nth_length_takeWhile[of "\<lambda>u. v \<in> set (follow T u)" ys] ys(2) calculation
      by (fastforce simp: ys_def children_def)
    ultimately show "d \<in> set (?pre ys)"
      using takeWhile_nth[of "pd - pv" "\<lambda>u. v \<in> set (follow T u)" ys] nth_mem
      by (fastforce simp: ys_def)
  qed
  thus ?thesis
    using ys(1,2,4) \<open>0 < length (?pre ys)\<close>
    by (intro exI[of _ "?pre ys"] exI[of _ "dropWhile (\<lambda>u. v \<in> set (follow T u)) ys"])
       (auto simp: children_def hd_conv_nth takeWhile_nth dest: set_takeWhileD)
qed

lemma block_self_similar:
  assumes "arb_invar r V S" "v \<in> V" "c \<in> V" "c \<in> children (prnt S) v"
  shows "\<exists>A B. block S v = A @ block S c @ B"
proof-
  obtain A H where "block S v = A @ c # H"
    using assms(4) block_props(4)[OF assms(1,2)]
    by (blast dest: split_list)
  moreover hence "follow (thrd S) v = A @ follow (thrd S) c"
    "follow (thrd S) c = c # H @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd
      S) w)"
    using block_props(1)[OF assms(1,2)] follow_append_ps[OF arb_invarD(3)[OF assms(1)], of v A c]
    by simp+
  moreover have "set (block S c) \<subseteq> set (block S v)"
    using block_props(4)[OF assms(1,2)] block_props(4)[OF assms(1,3)]
          children_subset[OF arb_invarD(2)[OF assms(1)] assms(4)]
    by simp
  moreover have "set (block S c) \<subseteq> set (follow (thrd S) c)"
    by (subst block_props(1)[OF assms(1,3)]) auto
  moreover have "set A \<inter> set (follow (thrd S) c) = {}"
    using follow_distinct_ps[OF arb_invarD(3)[OF assms(1)], of v] calculation(2)
    by simp
  ultimately have "set (block S c) \<subseteq> set (c # H)"
    by auto
  then obtain B where "c # H = block S c @ B"
    using prefix_mono_set[OF follow_distinct_ps[OF arb_invarD(3)[OF assms(1)], of c]
            block_props(1)[OF assms(1,3), symmetric], of "c # H"] \<open>follow (thrd S) c = c # H @ _\<close>
    by auto
  thus ?thesis
    using \<open>block S v = A @ c # H\<close>
    by auto
qed

lemma block_nest:
  assumes "arb_invar r V S" "v \<in> V" "c \<in> V" "c \<in> children (prnt S) v" "c \<noteq> v"
  shows "\<exists>P Q. block S v = v # P @ block S c @ Q"
  by (insert block_self_similar[OF assms(1-4)] block_props(2,5)[OF assms(1,2)] block_props(2,5)[OF assms(1,3)]
    assms(5); fastforce simp: hd_append neq_Nil_conv)

lemma follow_Cons_Cons_ps:
  "\<lbrakk>parent_spec T; follow T u = u # y # rest\<rbrakk> \<Longrightarrow> T u = Some y"
  by (cases "T u") (auto simp: follow_None_ps follow_Some_ps follow_hd_ps dest!: arg_cong[where f = hd])

lemma arb_dfs_step:
  assumes "arb_invar rr VV (S :: 'a ndtree)" "x \<in> VV" "thrd S x = Some y"
  shows "\<exists>g. prnt S y = Some g \<and> g \<in> set (follow (prnt S) x)"
proof-
  have "y \<in> VV" "y \<noteq> rr"
    using assms arb_invarD(7,9,10)[OF assms(1)] follow_sub_of_mem[OF arb_invarD(3)[OF assms(1)], of x rr]
          follow_Some_ps[OF arb_invarD(3)[OF assms(1)] assms(3)]
    by auto
  then obtain g where "prnt S y = Some g"
    using arb_invarD(5)[OF assms(1)]
    by blast
  moreover hence "g \<in> VV" "y \<noteq> g" "y \<in> children (prnt S) g"
    using rooted_arborescense_invar_parent_in_V[OF arb_invarD(1)[OF assms(1)]]
          follow_Some_ps[OF arb_invarD(2)[OF assms(1)]] follow_mem_ps[OF arb_invarD(2)[OF assms(1)]]
          wf_not_refl[OF parent_specD[OF arb_invarD(2)[OF assms(1)]], of g]
    by (auto simp: children_def)
  moreover obtain P Q where "block S g = P @ y # Q"
    using \<open>y \<in> children (prnt S) g\<close> block_props(4)[OF assms(1) \<open>g \<in> VV\<close>]
    by (blast dest: split_list)
  moreover hence "P \<noteq> []"
    using block_props(5)[OF assms(1) \<open>g \<in> VV\<close>] \<open>y \<noteq> g\<close>
    by auto
  moreover hence "thrd S (last P) = Some y"
    using block_props(1)[OF assms(1) \<open>g \<in> VV\<close>] \<open>block S g = P @ y # Q\<close>
    by (cases P rule: rev_cases)
       (auto dest!: follow_append_ps[OF arb_invarD(3)[OF assms(1)]]
             intro: follow_Cons_Cons_ps[OF arb_invarD(3)[OF assms(1)]])
  ultimately show ?thesis
    using block_props(4)[OF assms(1) \<open>g \<in> VV\<close>] arb_invarD(10)[OF assms(1)] assms(3)
    by (auto simp: children_def)
qed

lemma dirty_pass_unchanged:
  "thrd (dirty_pass S drt) = thrd S \<and> prnt (dirty_pass S drt) = prnt S
   \<and> lsuc (dirty_pass S drt) = lsuc S \<and> snum (dirty_pass S drt) = snum S"
  by (induction drt arbitrary: S) (auto simp: dirty_pass_def split: option.splits)

lemmas dirty_pass_thrd[simp] = dirty_pass_unchanged[THEN conjunct1]
lemmas dirty_pass_prnt[simp] = dirty_pass_unchanged[THEN conjunct2, THEN conjunct1]
lemmas dirty_pass_lsuc[simp] = dirty_pass_unchanged[THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas dirty_pass_snum[simp] = dirty_pass_unchanged[THEN conjunct2, THEN conjunct2, THEN conjunct2]

lemma dirty_pass_rvth_fold:
  "rvth (dirty_pass S ds) = foldl (\<lambda>R u. case thrd S u of None \<Rightarrow> R | Some w \<Rightarrow> R(w
    \<mapsto> u)) (rvth S) ds"
  by (induction ds arbitrary: S) (auto simp: dirty_pass_def split: option.splits)

lemmas [code] =
  stem_loop.simps stem_num_loop.simps last_vin_loop.simps
  last_vout_loop.simps succ_vin_loop.simps succ_vout_loop.simps

lemma follow_Some_notin_ps:
  "\<lbrakk>parent_spec T; T u = Some w\<rbrakk> \<Longrightarrow> \<forall>x\<in>set (follow T w). x \<noteq> u"
  using follow_distinct_ps[of T u]
  by (auto simp: follow_Some_ps)

lemma stem_num_loop_fields:
  assumes "parent_spec P"
  shows "prnt S = P \<longrightarrow>
           (prnt (stem_num_loop S sn0 u iv acc tls) = P
          \<and> thrd (stem_num_loop S sn0 u iv acc tls) = thrd S
          \<and> rvth (stem_num_loop S sn0 u iv acc tls) = rvth S)"
  using assms
proof(induction u arbitrary: S acc rule: parent_walk_induct)
  case IH: (step u)
  thus ?case
    by (auto simp: stem_num_loop.simps[of S] Let_def split: option.splits)
qed

lemma follow_parent_in_tail:
  "\<lbrakk>parent_spec P; x \<in> set (follow P u); P x = Some y\<rbrakk> \<Longrightarrow> y \<in> set (follow P u)
    \<and> y \<noteq> u"
  using follow_trans[of P x u y] follow_Some_ps[of P x y] follow_mem_ps[of P y] ancestor_antisym[of P u x]
        follow_Some_notin_ps[of P x y]
  by auto

lemma stem_num_loop_lsuc:
  assumes "parent_spec P"
  shows "prnt S = P \<longrightarrow> iv \<in> set (follow P u) \<longrightarrow>
    lsuc (stem_num_loop S sn0 u iv acc tls) =
      (\<lambda>x. if x \<in> (\<lambda>y. the (P y)) ` set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P u)) then
        tls else lsuc S x)"
  using assms
proof(induction u arbitrary: S acc rule: parent_walk_induct)
  case IH: (step u)
  thus ?case
    by (cases "P u")
       (auto simp: stem_num_loop.simps[of S] parent_walk_simps assms Let_def fun_eq_iff
             intro: rev_image_eqI)
qed

lemma stem_num_loop_snum:
  assumes "parent_spec P"
  shows "prnt S = P \<longrightarrow> iv \<in> set (follow P u)
    \<longrightarrow> (\<forall> y \<in> set (takeWhile (\<lambda>z. z \<noteq> iv) (follow P u)). P y \<noteq> None
      \<longrightarrow> sn0 (the (P y)) \<le> sn0 y)
    \<longrightarrow> snum (stem_num_loop S sn0 u iv acc tls) =
      (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> iv) (follow P u))
           then acc + sn0 u - sn0 (the (P x)) else snum S x)"
  using assms
proof(induction u arbitrary: S acc rule: parent_walk_induct)
  case IH: (step u)
  thus ?case
    using follow_Some_notin_ps[OF assms, of u]
    by (cases "P u")
       (auto simp: stem_num_loop.simps[of S] parent_walk_simps assms Let_def fun_eq_iff
             dest: set_takeWhileD)
qed

subsection \<open>Fused decoration loops: single-pass equivalents of the four fix-up loops\<close>

text \<open>The fused loops update subtree sizes and last descendants in one parent-chain traversal.
  Their closed field formulas are used directly in both pivot branches.\<close>

lemma fused_vin_loop_props:
  assumes "parent_spec P"
  shows "prnt S = P \<longrightarrow>
    (prnt (fused_vin_loop S u jv jn lso d la sa) = P
     \<and> thrd (fused_vin_loop S u jv jn lso d la sa) = thrd S
     \<and> rvth (fused_vin_loop S u jv jn lso d la sa) = rvth S
     \<and> lsuc (fused_vin_loop S u jv jn lso d la sa) =
       (\<lambda>x. if la \<and> x \<in> set (takeWhile (\<lambda>y. lsuc S y = jv)
         (follow P u)) then lso else lsuc S x)
     \<and> snum (fused_vin_loop S u jv jn lso d la sa) =
       (\<lambda>x. if sa \<and> x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P u))
         then snum S x + d else snum S x))"
  using assms
proof(induction u arbitrary: S la sa rule: parent_walk_induct)
  case IH: (step u)
  thus ?case
    using follow_Some_notin_ps[OF assms, of u]
    by (intro impI conjI; cases "P u")
       (auto simp: fused_vin_loop.simps[of S] parent_walk_simps assms Let_def fun_eq_iff
             cong: takeWhile_cong dest: set_takeWhileD)
qed

lemma fused_vin_props:
  assumes "parent_spec (prnt S)"
  shows "prnt (fused_vin_loop S u jv jn lso d la sa) = prnt S"
    "thrd (fused_vin_loop S u jv jn lso d la sa) = thrd S"
    "rvth (fused_vin_loop S u jv jn lso d la sa) = rvth S"
    "lsuc (fused_vin_loop S u jv jn lso d la sa) =
      (\<lambda>x. if la \<and> x \<in> set (takeWhile (\<lambda>y. lsuc S y = jv) (follow (prnt S) u))
        then lso else lsuc S x)"
    "snum (fused_vin_loop S u jv jn lso d la sa) =
      (\<lambda>x. if sa \<and> x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S) u))
        then snum S x + d else snum S x)"
  using fused_vin_loop_props[OF assms, of S u jv jn lso d la sa]
  by auto

lemma fused_vout_loop_props:
  assumes "parent_spec P"
  shows "prnt S = P \<longrightarrow>
    (prnt (fused_vout_loop S u stp gv sv jn d la sa) = P
     \<and> thrd (fused_vout_loop S u stp gv sv jn d la sa) = thrd S
     \<and> rvth (fused_vout_loop S u stp gv sv jn d la sa) = rvth S
     \<and> lsuc (fused_vout_loop S u stp gv sv jn d la sa) =
       (\<lambda>x. if la \<and> x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv)
         (follow P u)) then sv else lsuc S x)
     \<and> snum (fused_vout_loop S u stp gv sv jn d la sa) =
       (\<lambda>x. if sa \<and> x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P u))
         then snum S x - d else snum S x))"
  using assms
proof(induction u arbitrary: S la sa rule: parent_walk_induct)
  case IH: (step u)
  thus ?case
    using follow_Some_notin_ps[OF assms, of u]
    by (intro impI conjI; cases "P u")
       (auto simp: fused_vout_loop.simps[of S] parent_walk_simps assms Let_def fun_eq_iff
             cong: takeWhile_cong dest: set_takeWhileD)
qed

lemma fused_vout_props:
  assumes "parent_spec (prnt S)"
  shows "prnt (fused_vout_loop S u stp gv sv jn d la sa) = prnt S"
    "thrd (fused_vout_loop S u stp gv sv jn d la sa) = thrd S"
    "rvth (fused_vout_loop S u stp gv sv jn d la sa) = rvth S"
    "lsuc (fused_vout_loop S u stp gv sv jn d la sa) =
      (\<lambda>x. if la \<and> x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc S y = gv)
        (follow (prnt S) u)) then sv else lsuc S x)"
    "snum (fused_vout_loop S u stp gv sv jn d la sa) =
      (\<lambda>x. if sa \<and> x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S) u))
        then snum S x - d else snum S x)"
  using fused_vout_loop_props[OF assms, of S u stp gv sv jn d la sa]
  by auto

subsection \<open>The stem reversal as a closed-form invariant\<close>

text \<open>The path-reversal loop @{const stem_loop} is a @{command partial_function}, so it has no
      generated induction rule.  We fix the pivot data in a locale and characterise the loop's
      effect by a well-founded induction on the variant @{term "k - m"}.  The state after
      @{term m} body iterations is pinned down field-by-field by @{term "Istem m"}: every map is
      @{term "S0"}'s map overlaid (@{text "++"}, highest priority last) with the edits made so far.\<close>

locale stem_setup =
  fixes S0 :: "'a ndtree" and r :: 'a and V :: "'a set"
    and i j p :: 'a and k :: nat and s :: "nat \<Rightarrow> 'a"
  assumes arb:   "arb_invar r V S0"
      and path0: "s 0 = i"
      and pathS: "\<And>t. t < k \<Longrightarrow> prnt S0 (s t) = Some (s (Suc t))"
      and pathk: "s k = p"
      and inj:   "inj_on s {..k}"
      and jnotp: "j \<notin> children (prnt S0) p"
      and pne_r: "p \<noteq> r"
      and iV:    "i \<in> V"
      and jV:    "j \<in> V"
begin

lemmas arbD = arb_invarD[OF arb]
lemmas blockP = block_props[OF arb]
lemmas block_nesting = block_nest[OF arb]
lemmas block_subtree = block_self_similar[OF arb]
lemmas dfs_step = arb_dfs_step[OF arb]
lemmas ppt = arbD(2)
lemmas pst = arbD(3)
lemmas ppt_follow_Some = follow_Some_ps[OF ppt]
lemmas ppt_follow_None = follow_None_ps[OF ppt]
lemmas ppt_follow_ne = follow_ne_ps[OF ppt]
lemmas ppt_follow_mem = follow_mem_ps[OF ppt]
lemmas ppt_follow_distinct = follow_distinct_ps[OF ppt]
lemmas ppt_follow_append = follow_append_ps[OF ppt]
lemmas ppt_follow_trans = follow_trans[OF ppt]
lemmas ppt_follow_linear = follow_linear[OF ppt]
lemmas ppt_children_subset = children_subset[OF ppt]
lemmas ppt_ancestor_antisym = ancestor_antisym[OF ppt]
lemmas ppt_join_of_first = join_of_first[OF ppt]
lemmas ppt_join_of_mem = join_of_mem[OF ppt]
lemmas ppt_follow_eq_on = follow_eq_on[OF ppt]
lemmas ppt_follow_sub_of_mem = follow_sub_of_mem[OF ppt]
lemmas pst_follow_Some = follow_Some_ps[OF pst]
lemmas pst_follow_ne = follow_ne_ps[OF pst]
lemmas pst_follow_hd = follow_hd_ps[OF pst]
lemmas pst_follow_mem = follow_mem_ps[OF pst]
lemmas pst_follow_distinct = follow_distinct_ps[OF pst]
lemmas pst_follow_append = follow_append_ps[OF pst]
lemmas pst_follow_nth_Suc = follow_nth_Suc[OF pst]

text \<open>The path predecessor (@{text pstm}), with the convention @{term "s_pred 0 = j"}.\<close>
definition s_pred :: "nat \<Rightarrow> 'a" where
  "s_pred m = (if m = 0 then j else s (m - 1))"

text \<open>@{term "out t"}: the thread-successor (in @{term S0}) of @{term "s t"}'s last descendant ---
      the node spliced out when @{term "s t"}'s block is detached.\<close>
definition out :: "nat \<Rightarrow> 'a option" where
  "out t = thrd S0 (lsuc S0 (s t))"

text \<open>@{term "lsx t"}: the loop's running @{text lsx} pointer at step @{term t} (the last node of
      the block already threaded), in closed form.\<close>
definition lsx :: "nat \<Rightarrow> 'a" where
  "lsx t = (if t = 0 then lsuc S0 i
            else if lsuc S0 (s t) = lsuc S0 (s (t-1)) then the (rvth S0 (s (t-1)))
            else lsuc S0 (s t))"

definition aftn :: "nat \<Rightarrow> 'a option" where "aftn t = out t"

text \<open>@{term "drt m"}: the deferred-reverse list accumulated after @{term m} iterations.\<close>
definition drt :: "nat \<Rightarrow> 'a list" where "drt m = j # map lsx [0..<m]"

text \<open>@{term "bef t"}: the thread-predecessor (in @{term S0}) of @{term "s t"}.\<close>
definition bef :: "nat \<Rightarrow> 'a" where "bef t = the (rvth S0 (s t))"

text \<open>The thread map after @{term m} iterations, as a fold of @{const fun_upd}s: the j {\isasymmapsto} i
      seam at the bottom, then the bridge (BR) links "bef t {\isasymmapsto} out t (a delete when
      @{term "out t = None"}), then the up-links (UP) "lsx t {\isasymmapsto} s (Suc t)" applied last so
      they win on the single colliding key.\<close>
definition thrd_inv :: "nat \<Rightarrow> ('a \<rightharpoonup> 'a)" where
  "thrd_inv m =
     fold (\<lambda>t T. T(lsx t \<mapsto> s (Suc t))) [0..<m]
       (fold (\<lambda>t T. T(bef t := out t)) [0..<m]
         ((thrd S0)(j \<mapsto> s 0)))"

text \<open>The reverse-thread edits actually installed during the loop (the deferred UP reverses are
      handled later by @{const dirty_pass}); only steps with @{term "out t \<noteq> None"} contribute.
      The loop sets the reverse-thread of @{term "out t"} to @{term "bef t"} on each iteration, so on
      a colliding key (two stem nodes sharing a last-successor, hence the same @{term "out t"}) the
      later write wins.  We therefore reverse the association list before @{const map_of} (which keeps
      the first occurrence), making the closed form last-write-wins to match the loop.\<close>
definition revBR :: "nat \<Rightarrow> ('a \<rightharpoonup> 'a)" where
  "revBR m = map_of (rev (map (\<lambda>t. (the (out t), bef t)) (filter (\<lambda>t. out t \<noteq> None) [0..<m])))"

text \<open>The reversed parent links installed after @{term m} iterations.\<close>
definition REV :: "nat \<Rightarrow> ('a \<rightharpoonup> 'a)" where
  "REV m = map_of (map (\<lambda>t. (s t, s_pred t)) [0..<m])"

definition Istem :: "nat \<Rightarrow> 'a ndtree \<Rightarrow> bool" where
  "Istem m S \<longleftrightarrow> thrd S = thrd_inv m
              \<and> rvth S = rvth S0 ++ revBR m
              \<and> prnt S = prnt S0 ++ REV m
              \<and> lsuc S = lsuc S0 \<and> snum S = snum S0"

definition Sfin :: "'a ndtree" where
  "Sfin = \<lparr> prnt = prnt S0 ++ REV k, thrd = thrd_inv k,
            rvth = rvth S0 ++ revBR k, lsuc = lsuc S0, snum = snum S0 \<rparr>"

lemma Istem_unique:
  "Istem k S \<Longrightarrow> S = Sfin"
  by (cases S) (simp add: Istem_def Sfin_def)

lemma live_prnt:
  "\<lbrakk>m < k; Istem m S\<rbrakk> \<Longrightarrow> prnt S (s m) = Some (s (Suc m))"
  using pathS[of m] inj
  by (auto simp: Istem_def REV_def map_add_def inj_on_eq_iff split: option.splits dest!: map_of_SomeD)

lemma thrd_inv_0[simp]: "thrd_inv 0 = (thrd S0)(j \<mapsto> i)"
  by (simp add: thrd_inv_def path0)

lemma revBR_0[simp]: "revBR 0 = Map.empty"
  by (simp add: revBR_def)
lemma REV_0[simp]: "REV 0 = Map.empty"
  by (simp add: REV_def)

lemma Istem_0: "Istem 0 (S0\<lparr>thrd := (thrd S0)(j \<mapsto> i)\<rparr>)"
  by (simp add: Istem_def   )

lemma REV_Suc:
  "m < k \<Longrightarrow> REV (Suc m) = (REV m)(s m \<mapsto> s_pred m)"
  using inj
  by (auto simp: REV_def map_add_def fun_eq_iff inj_on_eq_iff dest!: map_of_SomeD split: option.splits)
end

text \<open>The locality (geometry) facts the induction quotes directly: the out-nodes are
      disjoint from the stem, the bridge key is not an up-link key, the out-nodes are distinct, and
      a genuinely new last-successor is untouched by the edits.  Per  these are consequences of
      @{const arb_invar} plus the pivot preconditions (clause J etc.); they are assumed here so the
      stem induction can be developed in isolation.\<close>
locale stem_setup_geom = stem_setup +
  assumes out_notin_stem: "\<And>t. t < k \<Longrightarrow> out t \<noteq> None \<Longrightarrow> the (out t) \<notin>
    s ` {..k}"
      and bef_notin_lsx:  "\<And>m. m < k \<Longrightarrow> bef m \<notin> lsx ` {..m}"
      and outnode_fresh:  "\<And>m. m < k \<Longrightarrow> lsuc S0 (s (Suc m)) \<noteq> lsuc S0 (s m)
        \<Longrightarrow>
                             lsuc S0 (s (Suc m)) \<notin> lsx ` {..m}
                           \<and> lsuc S0 (s (Suc m)) \<notin> bef ` {..m}
                           \<and> lsuc S0 (s (Suc m)) \<noteq> j"
begin

lemma revBR_dom: "dom (revBR m) = (\<lambda>t. the (out t)) ` {t. t < m \<and> out t \<noteq> None}"
  unfolding revBR_def dom_map_of_conv_image_fst
  by force

lemma rvth_stem_eq:
  assumes "m' \<le> k" "n \<le> k" "Istem n S"
  shows "rvth S (s m') = rvth S0 (s m')"
proof-
  have "s m' \<notin> dom (revBR n)"
  proof
    assume "s m' \<in> dom (revBR n)"
    then obtain t where "t < n" "out t \<noteq> None" "the (out t) = s m'"
      unfolding revBR_dom
      by auto
    thus False
      using assms(1,2) out_notin_stem[of t]
      by auto
  qed
  thus ?thesis
    using assms(3)
    by (simp add: Istem_def map_add_dom_app_simps)
qed

lemma live_rvth:
  "\<lbrakk>m \<le> k; Istem m S\<rbrakk> \<Longrightarrow> rvth S (s m) = rvth S0 (s m)"
  by (rule rvth_stem_eq)

lemma revBR_Suc_None:
  "out m = None \<Longrightarrow> revBR (Suc m) = revBR m"
  by (simp add: revBR_def upt_Suc_append)

lemma revBR_Suc_Some:
  "out m \<noteq> None \<Longrightarrow> revBR (Suc m) = (revBR m)(the (out m) \<mapsto> bef m)"
  by (simp add: revBR_def upt_Suc_append)

lemma revBR_eval_ex:
  "revBR k w = Some v \<Longrightarrow> \<exists>t < k. out t = Some w \<and> bef t = v"
  by (fastforce simp: revBR_def dest!: map_of_SomeD)

lemma revBR_eval_last:
  "revBR m w = Some v \<Longrightarrow> \<exists>t<m. out t = Some w \<and> bef t = v \<and> (\<forall>t'. t < t'
    \<longrightarrow> t' < m \<longrightarrow> out t' \<noteq> Some w)"
proof(induction m)
  case (Suc m)
  thus ?case
    by (cases "out m")
       (fastforce simp: revBR_Suc_None revBR_Suc_Some less_Suc_eq split: if_splits)+
qed (simp add: revBR_def)

lemma thrd_inv_Suc:
  assumes "m < k"
  shows "thrd_inv (Suc m) = ((thrd_inv m)(lsx m \<mapsto> s (Suc m)))(bef m := out m)"
proof-
  have "bef m \<notin> lsx ` set [0..<m]" "bef m \<noteq> lsx m"
    using bef_notin_lsx[OF assms]
    by auto
  thus ?thesis
    by (simp add: thrd_inv_def fold_upd_commute[symmetric] fun_upd_twist)
qed

lemma thrd_inv_eval_fresh:
  "\<lbrakk>q \<notin> lsx ` set [0..<n]; q \<notin> bef ` set [0..<n]; q \<noteq> j\<rbrakk> \<Longrightarrow>
    thrd_inv n q = thrd S0 q"
  using fold_upd_other[of q lsx "[0..<n]" "\<lambda>t. Some (s (Suc t))"] fold_upd_other[of q bef "[0..<n]" out]
  by (simp add: thrd_inv_def)

lemma aft_lookup:
  assumes "m < k"
  shows "thrd_inv (Suc m) (lsx (Suc m)) = out (Suc m)"
proof(cases "lsuc S0 (s (Suc m)) = lsuc S0 (s m)")
  case True
  thus ?thesis
    using thrd_inv_Suc[OF assms]
    by (simp add: lsx_def bef_def out_def)
next
  case False
  moreover have "set [0..<Suc m] = {..m}"
    by auto
  ultimately show ?thesis
    using thrd_inv_eval_fresh[of "lsuc S0 (s (Suc m))" "Suc m"] outnode_fresh[OF assms]
    by (simp add: lsx_def out_def)
qed

lemma body_pres:
  assumes "m < k" "Istem m S"
  defines "S1 \<equiv> S\<lparr>thrd := (thrd S)(lsx m \<mapsto> the (prnt S (s m)))\<rparr>"
  defines "S2 \<equiv> (case aftn m of None \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 (s m)) :=
    None)\<rparr>
                  | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 (s m)) \<mapsto> a),
                                  rvth := (rvth S1)(a \<mapsto> the (rvth S1 (s m)))\<rparr>)"
  defines "S3 \<equiv> S2\<lparr>prnt := (prnt S2)(s m \<mapsto> s_pred m)\<rparr>"
  shows "Istem (Suc m) S3"
  using assms(1,2) live_prnt[of m S] live_rvth[of m S] thrd_inv_Suc[of m]
    REV_Suc[of m] revBR_Suc_None[of m] revBR_Suc_Some[of m]
  by (cases "out m") (auto simp: Istem_def S1_def S2_def S3_def aftn_def bef_def)

lemma stem_loop_step:
  assumes "m < k" "Istem m S"
  defines "S1 \<equiv> S\<lparr>thrd := (thrd S)(lsx m \<mapsto> the (prnt S (s m)))\<rparr>"
  defines "S2 \<equiv> (case aftn m of None \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 (s m)) :=
    None)\<rparr>
                  | Some a \<Rightarrow> S1\<lparr>thrd := (thrd S1)(the (rvth S1 (s m)) \<mapsto> a),
                                  rvth := (rvth S1)(a \<mapsto> the (rvth S1 (s m)))\<rparr>)"
  defines "S3 \<equiv> S2\<lparr>prnt := (prnt S2)(s m \<mapsto> s_pred m)\<rparr>"
  shows "stem_loop S (s m) (s_pred m) (lsx m) (aftn m) (drt m) p
           = stem_loop S3 (s (Suc m)) (s_pred (Suc m)) (lsx (Suc m)) (aftn (Suc m)) (drt (Suc m)) p"
proof-
  let ?LSX = "if lsuc S3 (the (prnt S (s m))) = lsuc S3 (s m)
                then the (rvth S3 (s m)) else lsuc S3 (the (prnt S (s m)))"
  have "s m \<noteq> p"
    using assms(1) inj pathk
    by (auto simp: inj_on_eq_iff)
  hence "stem_loop S (s m) (s_pred m) (lsx m) (aftn m) (drt m) p
           = stem_loop S3 (the (prnt S (s m))) (s m) ?LSX (thrd S3 ?LSX) (drt m @ [lsx m]) p"
    by (subst stem_loop.simps) (unfold Let_def S1_def S2_def S3_def, simp)
  moreover have "Istem (Suc m) S3"
    unfolding S1_def S2_def S3_def
    using body_pres[OF assms(1,2)]
    by simp
  moreover hence "?LSX = lsx (Suc m)" "thrd S3 (lsx (Suc m)) = aftn (Suc m)"
    using rvth_stem_eq[OF less_imp_le[OF assms(1)] Suc_leI[OF assms(1)]] live_prnt[OF assms(1,2)]
          aft_lookup[OF assms(1)]
    by (auto simp: bef_def Istem_def lsx_def aftn_def)
  ultimately show ?thesis
    using live_prnt[OF assms(1,2)]
    by (simp add: s_pred_def drt_def)
qed

lemma stem_loop_effect:
  "m \<le> k \<Longrightarrow> Istem m S \<Longrightarrow>
     stem_loop S (s m) (s_pred m) (lsx m) (aftn m) (drt m) p
       = (Sfin, s_pred k, lsx k, aftn k, drt k)"
proof(induction "k - m" arbitrary: m S)
  case 0
  thus ?case
    using Istem_unique pathk
    by (subst stem_loop.simps) auto
next
  case (Suc n)
  thus ?case
    using stem_loop_step[of m S] body_pres[of m S] Suc.hyps(1)[of "Suc m"]
    by auto
qed

corollary stem_loop_init:
  "stem_loop (S0\<lparr>thrd := (thrd S0)(j \<mapsto> i)\<rparr>) i j (lsuc S0 i) (thrd S0 (lsuc S0 i)) [j] p
     = (Sfin, s_pred k, lsx k, aftn k, drt k)"
  using stem_loop_effect[OF le0 Istem_0]
  by (simp add: path0 s_pred_def lsx_def aftn_def out_def drt_def)

end

context stem_setup begin

lemma sV[intro]:
  "t \<le> k \<Longrightarrow> s t \<in> V"
  using pathS[of t] pathS[of "k - 1"] arbD(5)
    rooted_arborescense_invar_parent_in_V[OF arbD(1), of "s (k - 1)" "s k"]
  by (cases "k = 0"; cases "t < k") (auto simp: path0 iV)

lemma anc_notin_thread_suffix:
  assumes "u \<in> V" "v \<in> children (prnt S0) u" "u \<noteq> v"
  shows "u \<notin> set (follow (thrd S0) v)"
  using blockP(1,4)[of u] ancestor_antisym[OF pst, of u v] assms
  by auto

lemma stem_chain: "\<lbrakk>b \<le> k; a \<le> b\<rbrakk> \<Longrightarrow> s b \<in> set (follow (prnt S0) (s a))"
proof(induction "b - a" arbitrary: a)
  case (Suc d)
  hence "s b \<in> set (follow (prnt S0) (s (Suc a)))"
    using Suc.hyps(1)[of "Suc a"]
    by simp
  thus ?case
    using Suc.prems Suc.hyps(2) pathS[of a] ppt_follow_Some
    by auto
qed (auto simp: ppt_follow_mem)

lemma out_notin_stem_le:
  assumes "t \<le> k" "0 < k" "out t \<noteq> None"
  shows "the (out t) \<notin> s ` {..k}"
proof
  assume "the (out t) \<in> s ` {..k}"
  then obtain t' where "t' \<le> k" "the (out t) = s t'"
    by auto
  have "follow (thrd S0) (s t) = block S0 (s t) @ follow (thrd S0) (the (out t))"
    using blockP(1)[OF sV[OF assms(1)]] assms(3)
    by (auto simp: out_def)
  hence "the (out t) \<notin> set (block S0 (s t))" "the (out t) \<in> set (follow (thrd S0) (s t))"
    using pst_follow_distinct[of "s t"] pst_follow_mem[of "the (out t)"]
    by auto
  thus False
    using \<open>t' \<le> k\<close> \<open>the (out t) = s t'\<close> stem_chain[of t t'] stem_chain[of t' t] assms(1)
      inj
          blockP(4)[OF sV[OF assms(1)]] anc_notin_thread_suffix[OF sV[OF \<open>t' \<le> k\<close>], of "s t"]
    by (cases "t' \<le> t") (auto simp: children_def inj_on_eq_iff)
qed

lemma geom_out_notin_stem:
  "\<lbrakk>t < k; out t \<noteq> None\<rbrakk> \<Longrightarrow> the (out t) \<notin> s ` {..k}"
  using out_notin_stem_le[of t]
  by auto

lemma bef_pred:
  assumes "m < k"
  shows "thrd S0 (bef m) = Some (s m)" "s m \<noteq> r" "bef m \<in> V" "s m \<in> V"
proof-
  have "s m \<in> V - {r}"
    using pathS[OF assms] arbD(5)
    by auto
  moreover then obtain u where "rvth S0 (s m) = Some u"
    using arbD(9)
    by auto
  ultimately show "thrd S0 (bef m) = Some (s m)" "s m \<noteq> r" "bef m \<in> V" "s m \<in> V"
    using arbD(8,10)
    by (auto simp: bef_def)
qed

lemma bef_notin_block:
  assumes "m < k"
  shows "bef m \<notin> set (block S0 (s m))"
  by (insert bef_pred(1)[OF assms] pst_follow_Some[of "bef m" "s m"] pst_follow_distinct[of "bef m"] blockP(1)[OF
    bef_pred(4)[OF assms]]; fastforce)

lemma bef_inj:
  "\<lbrakk>a < k; b < k; a \<noteq> b\<rbrakk> \<Longrightarrow> bef a \<noteq> bef b"
  using bef_pred(1)[of a] bef_pred(1)[of b] inj
  by (auto simp: inj_on_eq_iff)

lemma lsx_cases:
  assumes "t \<le> m" "m < k"
  shows "(0 < t \<and> lsx t = bef (t - 1)) \<or> lsx t \<in> set (block S0 (s m))"
proof(cases "t \<noteq> 0 \<and> lsuc S0 (s t) = lsuc S0 (s (t-1))")
  case False
  hence "lsx t = lsuc S0 (s t)"
    by (auto simp: lsx_def path0)
  moreover have "lsuc S0 (s t) \<in> set (block S0 (s t))"
    using blockP(2,3)[OF bef_pred(4)[of t]] assms last_in_set[of "block S0 (s t)"]
    by auto
  moreover have "set (block S0 (s t)) \<subseteq> set (block S0 (s m))"
    using stem_chain[of m t] assms ppt_children_subset[of "s t" "s m"]
          blockP(4)[OF bef_pred(4)[of t]] blockP(4)[OF bef_pred(4)[of m]]
    by (auto simp: children_def)
  ultimately show ?thesis
    by auto
qed (auto simp: lsx_def bef_def)

lemma geom_bef_notin_lsx:
  assumes "m < k"
  shows "bef m \<notin> lsx ` {..m}"
proof
  assume "bef m \<in> lsx ` {..m}"
  then obtain t where "t \<le> m" "bef m = lsx t"
    by auto
  moreover hence "t - 1 < k" "t - 1 \<noteq> m \<or> t = 0"
    using assms
    by auto
  ultimately show False
    using lsx_cases[OF \<open>t \<le> m\<close> assms] bef_inj[OF assms, of "t - 1"] bef_notin_block[OF assms]
    by auto
qed

lemma geom_outnode_fresh:
  assumes "m < k" "lsuc S0 (s (Suc m)) \<noteq> lsuc S0 (s m)"
  shows "lsuc S0 (s (Suc m)) \<notin> lsx ` {..m} \<and> lsuc S0 (s (Suc m)) \<notin> bef ` {..m}
           \<and> lsuc S0 (s (Suc m)) \<noteq> j"
proof-
  have "s (Suc m) \<in> V" "s m \<in> V"
    using sV assms(1)
    by auto
  moreover have "s m \<in> children (prnt S0) (s (Suc m))" "s m \<noteq> s (Suc m)"
    using stem_chain[of "Suc m" m] assms(1) inj
    by (auto simp: children_def inj_on_eq_iff)
  ultimately obtain P Q where "block S0 (s (Suc m)) = s (Suc m) # P @ block S0 (s m) @ Q"
    using block_nesting
    by blast
  moreover have "distinct (block S0 (s (Suc m)))"
    using pst_follow_distinct[of "s (Suc m)"]
    by (subst (asm) blockP(1)[OF \<open>s (Suc m) \<in> V\<close>]) simp
  ultimately have "lsuc S0 (s (Suc m)) \<notin> set (block S0 (s m))"
    using assms(2) blockP(2,3)[OF \<open>s (Suc m) \<in> V\<close>] blockP(2,3)[OF \<open>s m \<in> V\<close>]
    by (cases Q rule: rev_cases) auto
  moreover have "lsuc S0 (s (Suc m)) \<notin> bef ` {..m}"
  proof
    assume "lsuc S0 (s (Suc m)) \<in> bef ` {..m}"
    then obtain t where "t \<le> m" "lsuc S0 (s (Suc m)) = bef t"
      by auto
    thus False
      using out_notin_stem_le[of "Suc m"] bef_pred(1)[of t] assms(1)
      by (auto simp: out_def)
  qed
  moreover have "lsuc S0 (s (Suc m)) \<noteq> j"
  proof-
    have "lsuc S0 (s (Suc m)) \<in> children (prnt S0) (s (Suc m))"
      using blockP(2,3,4)[OF \<open>s (Suc m) \<in> V\<close>] last_in_set[of "block S0 (s (Suc m))"]
      by auto
    moreover have "s (Suc m) \<in> children (prnt S0) p"
      using stem_chain[of k "Suc m"] pathk assms(1)
      by (auto simp: children_def)
    ultimately show ?thesis
      using jnotp ppt_children_subset
      by blast
  qed
  ultimately show ?thesis
    using lsx_cases[of _ m] assms(1)
    by fastforce
qed

end

sublocale stem_setup \<subseteq> stem_setup_geom
  using geom_out_notin_stem geom_bef_notin_lsx geom_outnode_fresh
  by unfold_locales blast+

subsection \<open>Clause A: the new parent map is a rooted arborescence (output side, {\isasymsection}15.5)\<close>

text \<open>The new parent map reverses the stem path  "i = s 0, {\isasymdots}, s k = p" to
       "p {\isasymrightarrow} s (k-1) {\isasymrightarrow} {\isasymdots} {\isasymrightarrow} s 0 = i {\isasymrightarrow}
         j", i.e. it is @{term "prnt S0"} overwritten with
      "s t {\isasymmapsto} s\_pred t" for every @{term "t \<le> k"} (= @{term "prnt S0 ++ REV k"} plus the
      top edit  "p {\isasymmapsto} s\_pred k").  Clause A is proved by replaying this as @{term "k+1"}
      single-edge swaps (@{thm rooted_arborescense_swap_parents}) \<^emph>\<open>bottom-up\<close> (@{term i} first):
      each step re-parents @{term "s m"} to @{term "s_pred m"}, which is legal because @{term "s m"}
      is never an ancestor of @{term "s_pred m"} in the partially-reversed tree.  The load-bearing
      geometric fact is that no stem node is an ancestor of @{term j} (else @{term j} would lie in
      @{term p}'s detached subtree, contradicting the no-cycle precondition @{thm stem_setup.jnotp}).\<close>

lemma follow_upd_fresh:
  "\<lbrakk>parent_spec T; parent_spec (T(x \<mapsto> y))\<rbrakk>
     \<Longrightarrow> x \<notin> set (follow T v) \<longrightarrow> follow (T(x \<mapsto> y)) v = follow T v"
  using follow_eq_on[of T "T(x \<mapsto> y)" v]
  by auto

lemma last_follow_root:
  assumes "rooted_arborescense_invar r V T"
  shows "v \<in> V \<Longrightarrow> last (follow T v) = r"
  using rooted_arborescense_invar_parent_spec[OF assms]
proof(induction v rule: parent_walk_induct)
  case IH: (step v)
  thus ?case
    using assms rooted_arborescense_invar_parent_in_V[of r V T v]
    by (cases "T v") (auto simp: parent_walk_simps rooted_arborescense_invar_parent_spec[OF assms])
qed

lemma children_root:
  assumes "rooted_arborescense_invar r V T"
  shows "children T r = V"
  using last_follow_root[OF assms] follow_ne_ps[OF rooted_arborescense_invar_parent_spec[OF assms]]
    children_subset_V[OF assms rooted_arborescense_invar_r_in_V[OF assms]]
  by (fastforce simp: children_def dest: last_in_set)

context stem_setup begin

lemma stem_notin_follow_j:
  "m \<le> k \<Longrightarrow> s m \<notin> set (follow (prnt S0) j)"
  using stem_chain[of k m] pathk jnotp ppt_children_subset[of "s m" p]
  by (auto simp: children_def)

definition Wseq :: "nat \<Rightarrow> ('a \<rightharpoonup> 'a)" where
  "Wseq m = fold (\<lambda>t T. T(s t \<mapsto> s_pred t)) [0..<m] (prnt S0)"

lemma Wseq_0[simp]: "Wseq 0 = prnt S0"
  by (simp add: Wseq_def)

lemma Wseq_Suc: "Wseq (Suc m) = (Wseq m)(s m \<mapsto> s_pred m)"
  by (simp add: Wseq_def upt_Suc_append)

lemma Wseq_fresh: "(\<And>t. t < m \<Longrightarrow> x \<noteq> s t) \<Longrightarrow> Wseq m x = prnt S0 x"
  by (induction m) (auto simp:  Wseq_Suc)

lemma Wseq_eval: "\<lbrakk>m \<le> Suc k; t < m\<rbrakk> \<Longrightarrow> Wseq m (s t) = Some (s_pred t)"
  using inj
  by (induction m) (auto simp: Wseq_Suc less_Suc_eq inj_on_eq_iff)

lemma pV[intro]: "p \<in> V"
  by (cases "0 < k") (use sV[OF order_refl] pathk path0 iV in auto)

lemmas pblock = blockP[OF pV]

lemma prnt_sm_ne_None:
  "m \<le> k \<Longrightarrow> prnt S0 (s m) \<noteq> None"
  using pathS[of m] pV pne_r pathk arbD(5)
  by (cases "m < k") auto

lemma s_pred_in_V:
  "m \<le> k \<Longrightarrow> s_pred m \<in> V"
  by (cases "m = 0") (use jV sV[of "m-1"] in \<open>auto simp: s_pred_def\<close>)

lemma Wseq_step:
  "m \<le> Suc k \<Longrightarrow>
     rooted_arborescense_invar r V (Wseq m)
   \<and> set (follow (Wseq m) (s_pred m)) = s ` {..<m} \<union> set (follow (prnt S0) j)"
proof(induction m)
  case (Suc m)
  hence IH: "m \<le> k" "rooted_arborescense_invar r V (Wseq m)"
    "set (follow (Wseq m) (s_pred m)) = s ` {..<m} \<union> set (follow (prnt S0) j)"
    by auto
  hence "s m \<notin> set (follow (Wseq m) (s_pred m))"
    using stem_notin_follow_j inj
    by (auto simp: inj_on_eq_iff)
  moreover have "Some (the (prnt S0 (s m))) = Wseq m (s m)"
    using Wseq_fresh[of m "s m"] prnt_sm_ne_None[OF IH(1)] inj IH(1)
    by (auto simp: inj_on_eq_iff)
  ultimately have "rooted_arborescense_invar r V (Wseq (Suc m))"
    using rooted_arborescense_swap_parents(1)[OF IH(2) _ _ s_pred_in_V[OF IH(1)]]
    by (simp add: Wseq_Suc)
  moreover hence "follow (Wseq (Suc m)) (s_pred (Suc m)) = s m # follow (Wseq m) (s_pred m)"
    using follow_upd_fresh[OF rooted_arborescense_invar_parent_spec[OF IH(2)], of "s m" "s_pred m" "s_pred m"]
          follow_Some_ps[OF rooted_arborescense_invar_parent_spec, of r V "Wseq (Suc m)" "s m" "s_pred m"]
          \<open>s m \<notin> set (follow (Wseq m) (s_pred m))\<close> rooted_arborescense_invar_parent_spec
    by (auto simp: Wseq_Suc s_pred_def[of "Suc m"])
  ultimately show ?case
    using IH(3)
    by (auto simp: lessThan_Suc)
qed (simp add:  s_pred_def arbD(1))

lemma REV_Suc_le:
  "m \<le> k \<Longrightarrow> REV (Suc m) = (REV m)(s m \<mapsto> s_pred m)"
  using inj
  by (auto simp: REV_def map_add_def fun_eq_iff inj_on_eq_iff dest!: map_of_SomeD split: option.splits)

lemma Wseq_eq_REV: "m \<le> Suc k \<Longrightarrow> Wseq m = prnt S0 ++ REV m"
  by (induction m) (auto simp:   Wseq_Suc REV_Suc_le)

lemma newprnt_eq: "Wseq (Suc k) = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
  using Wseq_eq_REV[of "Suc k"] REV_Suc_le[of k] pathk
  by simp

lemma clauseA: "rooted_arborescense_invar r V ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
  using Wseq_step[of "Suc k"]
  by (simp add: newprnt_eq)

lemma i_in_follow_newprnt:
  "i \<in> set (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p)"
  using Wseq_step[of "Suc k"] newprnt_eq path0 pathk
  by (force simp: s_pred_def)

lemma spine_lemma:
  assumes "lsuc S0 a = w" "a \<in> V" "b \<in> V" "b \<in> set (follow (prnt S0) w)" "a \<in> set (follow (prnt S0) b)"
  shows "lsuc S0 b = w"
proof-
  obtain A B where "block S0 a = A @ block S0 b @ B"
    using block_subtree[OF assms(2,3)] assms(5)
    by (auto simp: children_def)
  moreover have "distinct (block S0 a)"
    using pst_follow_distinct[of a]
    by (subst (asm) blockP(1)[OF assms(2)]) simp
  ultimately show ?thesis
    using assms(1,4) blockP(2,3,4)[OF assms(2)] blockP(2,3,4)[OF assms(3)]
    by (cases B rule: rev_cases) (auto simp: children_def)
qed

lemma Wseq_follow_Suc:
  assumes "m \<le> k"
  shows "follow (Wseq (Suc m)) (s_pred (Suc m)) = s m # follow (Wseq m) (s_pred m)"
proof-
  have "parent_spec (Wseq m)" "parent_spec (Wseq (Suc m))"
    using Wseq_step[of m] Wseq_step[of "Suc m"] assms rooted_arborescense_invar_parent_spec
    by auto
  moreover have "s m \<notin> set (follow (Wseq m) (s_pred m))"
    using Wseq_step[of m] assms stem_notin_follow_j inj
    by (auto simp: inj_on_eq_iff)
  ultimately show ?thesis
    using follow_upd_fresh[of "Wseq m" "s m" "s_pred m" "s_pred m"] follow_Some_ps[of "Wseq (Suc m)" "s m" "s_pred m"]
    by (auto simp: Wseq_Suc s_pred_def[of "Suc m"])
qed

lemma Wseq_follow_list:
  "m \<le> Suc k \<Longrightarrow> follow (Wseq m) (s_pred m) = map s (rev [0..<m]) @ follow (prnt S0) j"
  by (induction m) (auto simp: Wseq_follow_Suc  s_pred_def[of 0])

lemma chainStem_eq:
  "takeWhile (\<lambda>x. x \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p) = map s (rev [1..<Suc
    k])"
proof-
  have "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p = map s (rev [1..<Suc k]) @ i # follow (prnt S0) j"
    using Wseq_follow_list[of "Suc k"] newprnt_eq pathk path0
    by (cases "k = 0") (simp_all add: s_pred_def upt_conv_Cons)
  moreover have "\<forall>a\<in>set (map s (rev [1..<Suc k])). a \<noteq> i"
    using inj path0
    by (auto simp: inj_on_eq_iff)
  ultimately show ?thesis
    using takeWhile_append2[of "map s (rev [1..<Suc k])" "\<lambda>x. x \<noteq> i" "i # follow (prnt S0) j"]
    by (fastforce simp del: upt_Suc)
qed

lemma chainStem_set:
  "set (takeWhile (\<lambda>x. x \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p)) = s ` {1..<Suc k}"
  unfolding chainStem_eq
  by (simp del: upt_Suc)

lemma stem_chain_snum_mono:
  "\<forall> y \<in> set (takeWhile (\<lambda>z. z \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p)).
      ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y \<noteq> None
      \<longrightarrow> snum S0 (the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)) \<le> snum S0 y"
proof(intro ballI impI)
  fix y
  assume "y \<in> set (takeWhile (\<lambda>z. z \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))"
  then obtain t where "1 \<le> t" "t \<le> k" "y = s t"
    unfolding chainStem_set
    by auto
  moreover hence "((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y = Some (s (t - 1))"
    using Wseq_eval[of "Suc k" t] newprnt_eq
    by (simp add: s_pred_def)
  moreover have "children (prnt S0) (s (t - 1)) \<subseteq> children (prnt S0) (s t)"
    using ppt_children_subset stem_chain[of t "t - 1"] \<open>t \<le> k\<close>
    by (auto simp: children_def)
  moreover have "finite (children (prnt S0) (s t))"
    using blockP(4)[OF sV[of t]] \<open>1 \<le> t\<close> \<open>t \<le> k\<close> List.finite_set[of "block S0 (s t)"]
    by auto
  ultimately show "snum S0 (the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)) \<le> snum S0 y"
    using arbD(12) sV[of t] sV[of "t - 1"] card_mono
    by auto
qed

lemma inep_aux: "0 < k \<Longrightarrow> i \<noteq> p"
  using path0 pathk inj
  by (auto simp: inj_on_def)

definition final_thrd where
  "final_thrd = (let tc = (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j);
        b1 = (case tc of None \<Rightarrow> (thrd_inv k)(lsx k := None) | Some a \<Rightarrow> (thrd_inv k)(lsx k
          \<mapsto> a)) in (if the (rvth S0 p) \<noteq> j then (case aftn k of None \<Rightarrow> b1(the (rvth S0 p) :=
          None) | Some a \<Rightarrow> b1(the (rvth S0 p) \<mapsto> a)) else b1))"

definition final_rvth where
  "final_rvth = (let tc = (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j);
        r1 = (case tc of None \<Rightarrow> rvth Sfin | Some a \<Rightarrow> (rvth Sfin)(a \<mapsto> lsx k));
        r2 = (if the (rvth S0 p) \<noteq> j then (case aftn k of None \<Rightarrow> r1 | Some a \<Rightarrow> r1(a
          \<mapsto> the (rvth S0 p))) else r1) in foldl (\<lambda>R u. case final_thrd u of None \<Rightarrow> R | Some
          w \<Rightarrow> R(w \<mapsto> u)) r2 (drt k))"

definition final_snum where
  "final_snum jn = (let P = (prnt S0 ++ REV k)(p \<mapsto> s_pred k);
        vout = the (prnt S0 p);
        on = snum S0 p;
        su = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> i) (follow P p)) then on - snum S0 (the (P
          x)) else snum S0 x);
        sv = (\<lambda>x. if x = i then on else su x);
        s4 = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P j)) then sv x + on else sv x)
          in (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow P vout)) then s4 x - on else s4
          x))"

definition lsuc_stem where "lsuc_stem = (\<lambda>x.
  if x \<in> (\<lambda>y. the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)) `
         set (takeWhile (\<lambda>z. z \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) p))
  then lsx k else ((lsuc S0)(p := lsx k)) x)"

definition lsuc_in where "lsuc_in = (\<lambda>x.
  if x \<in> set (takeWhile (\<lambda>y. lsuc_stem y = j) (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j))
  then lsuc_stem p else lsuc_stem x)"

definition final_lsuc where "final_lsuc jn = (let stp = (if lsuc_stem jn = j then Some jn else None);
  upd = (\<lambda>sv x. if x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> stp \<and> lsuc_in y = lsuc S0 p)
                                       (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p))))
                then sv else lsuc_in x)
  in (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then upd (the (rvth S0 p))
      else if lsuc_stem p \<noteq> lsuc S0 p then upd (lsuc_stem p) else lsuc_in))"

lemma update_tree_fields:
  assumes "0 < k"
  shows "prnt (update_tree S0 i j p jn) = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    "thrd (update_tree S0 i j p jn) = final_thrd"
    "rvth (update_tree S0 i j p jn) = final_rvth"
    "snum (update_tree S0 i j p jn) = final_snum jn"
    "lsuc (update_tree S0 i j p jn) = final_lsuc jn"
proof-
  have psN: "parent_spec ((prnt S0 ++ REV k)(p \<mapsto> s_pred k))"
    using clauseA rooted_arborescense_invar_parent_spec
    by auto
  define Sp where "Sp = Sfin\<lparr>prnt := (prnt Sfin)(p \<mapsto> s_pred k)\<rparr>"
  define Sq where "Sq = (case (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j) of
                           None \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k := None)\<rparr>
                         | Some a \<Rightarrow> Sp\<lparr>thrd := (thrd Sp)(lsx k \<mapsto> a), rvth := (rvth Sp)(a
                           \<mapsto> lsx k)\<rparr>)"
  define Sr where "Sr = Sq\<lparr>lsuc := (lsuc Sq)(p := lsx k)\<rparr>"
  define Ss where "Ss = (if the (rvth S0 p) \<noteq> j
                         then (case aftn k of
                                 None \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) := None)\<rparr>
                               | Some a \<Rightarrow> Sr\<lparr>thrd := (thrd Sr)(the (rvth S0 p) \<mapsto> a), rvth :=
                                 (rvth Sr)(a \<mapsto> the (rvth S0 p))\<rparr>)
                         else Sr)"
  define St where "St = dirty_pass Ss (drt k)"
  define Su where "Su = stem_num_loop St (snum S0) p i 0 (lsuc St p)"
  define Sv where "Sv = Su\<lparr>snum := (snum Su)(i := snum S0 p)\<rparr>"
  define Sa where "Sa = fused_vin_loop Sv j j jn (lsuc Sv p) (snum S0 p) True True"
  define Sb where "Sb = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then fused_vout_loop Sa (the
    (prnt S0 p)) (if lsuc Sv jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) jn (snum S0 p) True True else
    if lsuc Sv p \<noteq> lsuc S0 p then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j then Some jn else
    None) (lsuc S0 p) (lsuc Sv p) jn (snum S0 p) True True else fused_vout_loop Sa (the (prnt S0 p)) (if lsuc Sv jn = j
    then Some jn else None) (lsuc S0 p) (lsuc S0 p) jn (snum S0 p) False True)"
  have "prnt Ss = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" "snum Ss = snum S0" "thrd Ss = final_thrd"
    "foldl (\<lambda>R u. case final_thrd u of None \<Rightarrow> R | Some w \<Rightarrow> R(w \<mapsto> u)) (rvth Ss)
      (drt k) = final_rvth"
    "lsuc Ss = (lsuc S0)(p := lsx k)"
    by (simp_all add: Ss_def Sr_def Sq_def Sp_def Sfin_def final_thrd_def final_rvth_def Let_def
             split: option.split)
  hence St: "prnt St = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" "snum St = snum S0" "thrd St = final_thrd"
    "rvth St = final_rvth" "lsuc St = (lsuc S0)(p := lsx k)"
    using dirty_pass_rvth_fold[of Ss "drt k"]
    by (simp_all add: St_def)
  hence Sv: "prnt Sv = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)" "thrd Sv = final_thrd" "rvth Sv = final_rvth"
    "snum Sv = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> i) (follow ((prnt S0 ++ REV k)(p
      \<mapsto> s_pred k)) p))
                     then snum S0 p - snum S0 (the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) x)) else snum S0 x)
                 (i := snum S0 p)"
    using stem_num_loop_fields[OF psN, of St] i_in_follow_newprnt stem_chain_snum_mono
          stem_num_loop_snum[OF psN, of St i p "snum S0" 0 "lsuc St p"]
    by (simp_all add: Sv_def Su_def) (simp add: fun_eq_iff)
  have lSv: "lsuc Sv = (\<lambda>x. if x \<in> (\<lambda>y. the (((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) y)) `
                                  set (takeWhile (\<lambda>z. z \<noteq> i) (follow ((prnt S0 ++ REV k)(p \<mapsto>
                                    s_pred k)) p))
                             then lsx k else ((lsuc S0)(p := lsx k)) x)"
    using stem_num_loop_lsuc[OF psN, of St i p] i_in_follow_newprnt St(1,5)
    by (auto simp: Sv_def Su_def fun_eq_iff)
  have UT: "update_tree S0 i j p jn = Sb"
    using inep_aux[OF assms]
    by (simp only: update_tree_def Let_def if_False if_True stem_loop_init prod.case Sb_def Sa_def Sv_def
                   Su_def St_def Ss_def Sr_def Sq_def Sp_def)
  have psSv: "parent_spec (prnt Sv)"
    using psN Sv(1)
    by simp
  have Sa: "prnt Sa = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    "thrd Sa = final_thrd" "rvth Sa = final_rvth" "lsuc Sa = lsuc_in"
    "snum Sa = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn)
      (follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j)) then snum Sv x + snum S0 p else snum Sv x)"
    using fused_vin_props[OF psSv, of j j jn "lsuc Sv p" "snum S0 p" True True] Sv(1-3) lSv
    by (auto simp: Sa_def lsuc_in_def lsuc_stem_def)
  have psSa: "parent_spec (prnt Sa)"
    using psN Sa(1)
    by simp
  show "prnt (update_tree S0 i j p jn) = (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"
    "thrd (update_tree S0 i j p jn) = final_thrd"
    "rvth (update_tree S0 i j p jn) = final_rvth"
    unfolding UT Sb_def
    using Sa(1-3)
    by (simp_all add: fused_vout_props[OF psSa] split: if_splits)
  have snumSb: "snum Sb = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn)
      (follow (prnt Sa) (the (prnt S0 p)))) then snum Sa x - snum S0 p else snum Sa x)"
    by (simp add: Sb_def fused_vout_props(5)[OF psSa] if_distrib[of snum])
  show "snum (update_tree S0 i j p jn) = final_snum jn"
    unfolding UT snumSb Sa(1,5) Sv(4) final_snum_def Let_def
    by (simp add: fun_eq_iff)
  show "lsuc (update_tree S0 i j p jn) = final_lsuc jn"
    unfolding UT Sb_def
    by (simp only: if_distrib[of lsuc] fused_vout_props(4)[OF psSa]
       Sa(1,4) lSv final_lsuc_def lsuc_stem_def Let_def simp_thms if_True if_False)
qed

lemmas update_tree_prnt = update_tree_fields(1)
lemmas update_tree_thrd = update_tree_fields(2)
lemmas update_tree_rvth = update_tree_fields(3)
lemmas update_tree_snum = update_tree_fields(4)
lemmas update_tree_lsuc = update_tree_fields(5)

lemma update_tree_prnt_i:
  "0 < k \<Longrightarrow> prnt (update_tree S0 i j p jn) i = Some j"
  using update_tree_prnt[of jn] inep_aux newprnt_eq[symmetric] Wseq_eval[of "Suc k" 0] path0
  by (simp add: s_pred_def)

abbreviation newprnt where "newprnt \<equiv> (prnt S0 ++ REV k)(p \<mapsto> s_pred k)"

lemma below_jn_gen:
  assumes "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) w))" "jn \<in> set (follow (prnt S0)
    w)"
  shows "jn \<in> set (follow (prnt S0) v) \<and> v \<noteq> jn"
proof-
  obtain A B where "takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) w) = A @ v # B"
    using assms(1)
    by (blast dest: split_list)
  hence "follow (prnt S0) w = A @ v # B @ dropWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) w)"
    using takeWhile_dropWhile_id[of "\<lambda>x. x \<noteq> jn" "follow (prnt S0) w"]
    by simp
  hence "follow (prnt S0) v = v # B @ dropWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) w)"
    by (rule ppt_follow_append)
  thus ?thesis
    using in_dropWhile_neq[OF assms(2)] takeWhile_holds[OF assms(1)]
    by simp
qed

lemma on_card: "card (set (block S0 p)) = snum S0 p"
  using pblock(4) arbD(12)[OF pV]
  by simp

lemma rinv0: "rooted_arborescense_invar r V (prnt S0)"
  using arbD(1) .

lemma children_finite: "v \<in> V \<Longrightarrow> finite (children (prnt S0) v)"
  using blockP(4)[of v] List.finite_set[of "block S0 v"]
  by simp

lemma follow_p_vout: "follow (prnt S0) p = p # follow (prnt S0) (the (prnt S0 p))"
  using prnt_sm_ne_None[of k] pathk ppt_follow_Some[of p]
  by auto

lemma block_notin_follow_j:
  "w \<in> set (block S0 p) \<Longrightarrow> w \<notin> set (follow (prnt S0) j)"
  using pblock(4) ppt_children_subset jnotp
  by (auto simp: children_def)

lemma follow_dropWhile:
  assumes "parent_spec T" "x \<in> set (follow T w)"
  shows "dropWhile (\<lambda>y. y \<noteq> x) (follow T w) = follow T x"
  using assms follow_append_ps[OF assms(1)] follow_distinct_ps[OF assms(1), of w]
  by (fastforce simp: dropWhile_append3 dropWhile_eq_Nil_conv dest: split_list)

lemma join_facts:
  assumes "jn = join_of (prnt S0) i j"
  shows "jn \<in> set (follow (prnt S0) j)" "jn \<in> set (follow (prnt S0) p)" "p \<noteq> jn"
proof-
  have "last (follow (prnt S0) i) = last (follow (prnt S0) j)"
    using last_follow_root[OF rinv0 iV] last_follow_root[OF rinv0 jV]
    by simp
  hence "jn \<in> set (follow (prnt S0) i)" "jn \<in> set (follow (prnt S0) j)"
    using ppt_join_of_mem assms
    by auto
  moreover have "p \<notin> set (follow (prnt S0) jn)"
    using jnotp ppt_children_subset[of jn p] calculation(2)
    by (auto simp: children_def)
  ultimately show "jn \<in> set (follow (prnt S0) j)" "jn \<in> set (follow (prnt S0) p)" "p \<noteq> jn"
    using ppt_follow_linear[of jn i p] stem_chain[of k 0] pathk path0 jnotp
    by (auto simp: children_def)
qed

lemma oldlist_block_p: "\<exists>A B. follow (thrd S0) r = A @ block S0 p @ B"
proof-
  have "p \<in> children (prnt S0) r"
    using last_in_set[OF ppt_follow_ne[of p]] last_follow_root[OF rinv0 pV]
    by (simp add: children_def)
  moreover have "thrd S0 (lsuc S0 r) = None"
    using arbD(8)
    by auto
  ultimately show ?thesis
    using block_subtree[OF arbD(6) pV] blockP(1)[OF arbD(6)]
    by auto
qed

lemma j_notin_block_p: "j \<notin> set (block S0 p)"
  using pblock(4) jnotp
  by simp

lemma thread_link:
  "\<lbrakk>parent_spec T; follow T v = G @ x # y # H\<rbrakk> \<Longrightarrow> T x = Some y"
  by (auto intro: follow_Cons_Cons_ps follow_append_ps)

definition defP :: "nat \<Rightarrow> 'a list" where
  "defP m = (SOME P. \<exists>Q. block S0 (s (Suc m)) = s (Suc m) # P @ block S0 (s m) @ Q)"
definition defQ :: "nat \<Rightarrow> 'a list" where
  "defQ m = (SOME Q. block S0 (s (Suc m)) = s (Suc m) # defP m @ block S0 (s m) @ Q)"

definition contrib :: "nat \<Rightarrow> 'a list" where
  "contrib m = (if m = 0 then block S0 i else s m # defP (m-1) @ defQ (m-1))"
definition newblock :: "'a list" where "newblock = concat (map contrib [0..<Suc k])"

definition alpha :: "'a list" where "alpha = takeWhile (\<lambda>x. x \<noteq> p) (follow (thrd S0) r)"
definition beta :: "'a list" where
  "beta = drop (length (block S0 p)) (dropWhile (\<lambda>x. x \<noteq> p) (follow (thrd S0) r))"

lemma oldlist_split_eq: "follow (thrd S0) r = alpha @ block S0 p @ beta"
proof-
  obtain A B where AB: "follow (thrd S0) r = A @ block S0 p @ B"
    using oldlist_block_p
    by blast
  moreover obtain rest where bp: "block S0 p = p # rest"
    using pblock(2,5)
    by (cases "block S0 p") auto
  moreover have "\<forall>x\<in>set A. x \<noteq> p"
    using AB bp pst_follow_distinct[of r]
    by auto
  ultimately show ?thesis
    by (simp add: alpha_def beta_def takeWhile_append2 dropWhile_append2)
qed

definition holed :: "'a list" where "holed = alpha @ beta"
definition newlist :: "'a list" where
  "newlist = takeWhile (\<lambda>x. x \<noteq> j) holed @ j # newblock @ tl (dropWhile (\<lambda>x. x \<noteq> j)
    holed)"

lemma oldlist_distinct[simp]: "distinct (follow (thrd S0) r)"
  using pst_follow_distinct
  by simp

lemma oldlist_set_V[simp]: "set (follow (thrd S0) r) = V"
  using arbD(7)
  by simp

lemma holed_distinct[simp]: "distinct holed"
  using oldlist_distinct oldlist_split_eq
  by (auto simp: holed_def)

lemma holed_set: "set holed = V - set (block S0 p)"
  using oldlist_distinct oldlist_split_eq oldlist_set_V
  by (auto simp: holed_def)

lemma j_in_holed: "j \<in> set holed"
  using holed_set jV j_notin_block_p
  by simp

lemma holed_split: "holed = takeWhile (\<lambda>x. x \<noteq> j) holed @ j # tl (dropWhile (\<lambda>x. x \<noteq> j)
  holed)"
proof-
  have "xs = takeWhile (\<lambda>x. x \<noteq> j) xs @ j # tl (dropWhile (\<lambda>x. x \<noteq> j) xs)" if "j \<in>
    set xs" for xs
    using that
    by (induction xs) auto
  thus ?thesis
    using j_in_holed
    by blast
qed

lemma block_p_subset_V: "set (block S0 p) \<subseteq> V"
  using oldlist_split_eq oldlist_set_V
  by auto

lemma set_holed_split: "set holed = set (takeWhile (\<lambda>x. x \<noteq> j) holed) \<union> {j} \<union> set (tl
  (dropWhile (\<lambda>x. x \<noteq> j) holed))"
  by (subst holed_split) auto

lemma hd_holed[simp]: "hd holed = r"
  using pst_follow_hd[of r] pst_follow_ne[of r] pne_r
  by (cases "follow (thrd S0) r") (auto simp: holed_def alpha_def)

lemma oldlist_link:
  "Suc t < length (follow (thrd S0) r) \<Longrightarrow> thrd S0 (follow (thrd S0) r ! t) = Some (follow (thrd S0) r !
    Suc t)"
  by (rule pst_follow_nth_Suc)

lemma alpha_link: "Suc t < length alpha \<Longrightarrow> thrd S0 (alpha ! t) = Some (alpha ! Suc t)"
  using oldlist_link[of t] oldlist_split_eq
  by (simp add: nth_append)

lemma beta_link: "Suc t < length beta \<Longrightarrow> thrd S0 (beta ! t) = Some (beta ! Suc t)"
  using oldlist_link[of "length alpha + length (block S0 p) + t"] oldlist_split_eq
  by (simp add: nth_append)

lemma alpha_ne: "alpha \<noteq> []"
  using pst_follow_hd[of r] pst_follow_ne[of r] pne_r
  by (cases "follow (thrd S0) r") (auto simp: alpha_def)

lemma old_rev_last_alpha: "the (rvth S0 p) = last alpha"
proof-
  obtain rest where "block S0 p = p # rest"
    using pblock(2,5)
    by (cases "block S0 p") auto
  hence "thrd S0 (last alpha) = Some p"
    using thread_link[OF pst, of r "butlast alpha" "last alpha" p "rest @ beta"] oldlist_split_eq alpha_ne
    by (cases alpha rule: rev_cases) auto
  thus ?thesis
    using arbD(10)
    by simp
qed

lemma beta_out: "beta \<noteq> [] \<Longrightarrow> aftn k = Some (hd beta)"
  using thread_link[OF pst, of r "alpha @ butlast (block S0 p)" "lsuc S0 p" "hd beta" "tl beta"]
        oldlist_split_eq pblock(2,3)
  by (cases beta; cases "block S0 p" rule: rev_cases) (auto simp: aftn_def out_def pathk)

lemma holed_old_adj:
  "\<lbrakk>Suc t < length holed; holed ! t \<noteq> the (rvth S0 p)\<rbrakk> \<Longrightarrow> thrd S0 (holed !
    t) = Some (holed ! Suc t)"
  using alpha_link[of t] beta_link[of "t - length alpha"] old_rev_last_alpha alpha_ne
  by (cases t "length alpha - 1" rule: linorder_cases)
     (auto simp: holed_def nth_append last_conv_nth Suc_diff_le)

lemma block_distinct_V: "v \<in> V \<Longrightarrow> distinct (block S0 v)"
  using blockP(1)[of v] pst_follow_distinct[of v]
  by simp

lemma concat_linked:
  assumes "\<And>ys. ys \<in> set xss \<Longrightarrow> ys \<noteq> []"
    "\<And>ys q. ys \<in> set xss \<Longrightarrow> Suc q < length ys \<Longrightarrow> R (ys ! q) (ys ! Suc q)"
    "\<And>i. Suc i < length xss \<Longrightarrow> R (last (xss ! i)) (hd (xss ! Suc i))"
    "Suc t < length (concat xss)"
  shows "R (concat xss ! t) (concat xss ! Suc t)"
  using assms
proof(induction xss arbitrary: t)
  case (Cons x xs)
  consider "Suc t < length x" | "Suc t = length x" | "length x \<le> t"
    by linarith
  thus ?case
  proof cases
    case 1
    thus ?thesis
      using Cons.prems(2)[of x t]
      by (simp add: nth_append)
  next
    case 2
    then obtain y ys where "xs = y # ys" "y \<noteq> []" "t = length x - 1"
      using Cons.prems(1,4)
      by (cases xs) auto
    thus ?thesis
      using Cons.prems(3)[of 0] Cons.prems(1)[of x]
      by (simp add: nth_append last_conv_nth hd_conv_nth)
  next
    case 3
    have "R (last (xs ! i)) (hd (xs ! Suc i))" if "Suc i < length xs" for i
      using Cons.prems(3)[of "Suc i"] that
      by simp
    thus ?thesis
      using 3 Cons.IH[of "t - length x"] Cons.prems(1,2,4)
      by (simp add: nth_append Suc_diff_le)
  qed
qed simp

lemma block_link:
  "\<lbrakk>v \<in> V; Suc q < length (block S0 v)\<rbrakk> \<Longrightarrow> thrd S0 (block S0 v ! q) = Some (block S0
    v ! Suc q)"
  using pst_follow_nth_Suc[of q v] blockP(1)[of v]
  by (simp add: nth_append)

lemma old_rev_notin_block_p: "the (rvth S0 p) \<notin> set (block S0 p)"
  using oldlist_distinct oldlist_split_eq old_rev_last_alpha last_in_set[OF alpha_ne]
  by auto

lemma follow_last_None:
  assumes "parent_spec T"
  shows "T (last (follow T v)) = None"
  by (insert follow_append_ps[OF assms, of v "butlast (follow T v)" "last (follow T v)" "[]"] append_butlast_last_id[OF
    follow_ne_ps[OF assms], of v] follow_ps_simps[OF assms, of "last (follow T v)"] follow_ne_ps[OF assms]; auto split:
    option.splits)

lemma dom_of_chain:
  assumes "xs \<noteq> []" "set xs = V" "\<And>t. Suc t < length xs \<Longrightarrow> T (xs ! t) = Some (xs ! Suc t)"
    "T (last xs) = None" "\<And>x. x \<notin> V \<Longrightarrow> T x = None"
  shows "dom T = V - {last xs}"
proof-
  have "x \<in> dom T" if x: "x \<in> V" "x \<noteq> last xs" for x
  proof-
    obtain n where n: "n < length xs" "xs ! n = x"
      using in_set_conv_nth[of x xs] x(1) assms(2)
      by blast
    moreover have "Suc n < length xs"
    proof(rule ccontr)
      assume "\<not> Suc n < length xs"
      hence "n = length xs - 1"
        using n(1)
        by simp
      thus False
        using n(2) x(2) assms(1)
        by (simp add: last_conv_nth)
    qed
    ultimately show ?thesis
      using assms(3)
      by auto
  qed
  thus ?thesis
    using assms(4,5)
    by (fastforce simp: dom_def)
qed

lemma last_follow_thrd0_None: "thrd S0 (last (follow (thrd S0) r)) = None"
  by (rule follow_last_None[OF pst])

lemma thrd_lsuc_p_None_of_beta_nil: "beta = [] \<Longrightarrow> thrd S0 (lsuc S0 p) = None"
  using last_follow_thrd0_None oldlist_split_eq pblock(2,3)
  by simp

lemma thrd_last_beta_None: "beta \<noteq> [] \<Longrightarrow> thrd S0 (last beta) = None"
  using last_follow_thrd0_None oldlist_split_eq
  by simp

lemma last_holed_nil: "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = [] \<Longrightarrow> last holed = j"
  by (subst holed_split) simp

lemma last_holed_ne_j:
  assumes "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) \<noteq> []"
  shows "last holed \<noteq> j"
proof-
  obtain A B where h: "holed = A @ j # B" "B \<noteq> []"
    using holed_split assms
    by blast
  hence "last holed = last B" "j \<notin> set B"
    using holed_distinct
    by auto
  thus ?thesis
    using last_in_set[OF h(2)]
    by auto
qed

lemma last_holed_beta: "beta \<noteq> [] \<Longrightarrow> last holed = last beta"
  by (simp add: holed_def)

lemma last_holed_old_rev: "beta = [] \<Longrightarrow> last holed = the (rvth S0 p)"
  using old_rev_last_alpha alpha_ne
  by (simp add: holed_def)

lemma aftn_eq_thrd_lsuc_p[simp]: "aftn k = thrd S0 (lsuc S0 p)"
  by (simp add: aftn_def out_def pathk)

lemma alpha_beta_disjoint: "set alpha \<inter> set beta = {}"
  using oldlist_distinct oldlist_split_eq
  by (simp add: Int_Un_distrib)

lemma set_beta_holed: "set beta \<subseteq> set holed"
  by (simp add: holed_def)

lemma old_rev_in_V[intro]: "the (rvth S0 p) \<in> V"
  using old_rev_last_alpha last_in_set[OF alpha_ne] oldlist_split_eq oldlist_set_V
  by auto

lemma thrd_old_rev[simp]: "thrd S0 (the (rvth S0 p)) = Some p"
proof-
  have "p \<in> dom (rvth S0)"
    using arbD(9) pV pne_r
    by simp
  thus ?thesis
    using arbD(10)
    by auto
qed

lemma splice_dfs:
  assumes "beta \<noteq> []"
  shows "\<exists>g. prnt S0 (hd beta) = Some g \<and> g \<in> set (follow (prnt S0) (the (rvth S0 p)))"
proof-
  have l: "lsuc S0 p \<in> set (block S0 p)"
    using pblock(2,3) last_in_set[of "block S0 p"]
    by simp
  obtain g where g: "prnt S0 (hd beta) = Some g" "g \<in> set (follow (prnt S0) (lsuc S0 p))"
    using dfs_step[OF subsetD[OF block_p_subset_V l]] beta_out[OF assms]
    by (auto simp: aftn_def out_def pathk)
  have "hd beta \<notin> set (block S0 p)"
    using hd_in_set[OF assms] set_beta_holed holed_set
    by auto
  hence "p \<notin> set (follow (prnt S0) g)"
    using pblock(4) ppt_follow_Some[OF g(1)]
    by (auto simp: children_def)
  moreover have "p \<in> set (follow (prnt S0) (lsuc S0 p))"
    using l pblock(4)
    by (simp add: children_def)
  ultimately have "g \<in> set (follow (prnt S0) (the (prnt S0 p)))"
    using ppt_follow_linear[OF g(2), of p] follow_p_vout ppt_follow_mem[of g]
    by auto
  moreover obtain w where w: "rvth S0 p = Some w"
    using domD[of p "rvth S0"] arbD(9) pV pne_r
    by auto
  then obtain pp where "prnt S0 p = Some pp" "pp \<in> set (follow (prnt S0) w)"
    using dfs_step[OF _ arbD(10)[THEN iffD2]] old_rev_in_V
    by force
  ultimately show ?thesis
    using g(1) w ppt_follow_sub_of_mem
    by auto
qed

lemma holed_dfs_old:
  assumes "Suc t < length holed"
  shows "\<exists>a. prnt S0 (holed ! Suc t) = Some a \<and> a \<in> set (follow (prnt S0) (holed ! t))"
proof(cases "holed ! t = the (rvth S0 p)")
  case True
  have "0 < length alpha" "holed ! (length alpha - 1) = the (rvth S0 p)"
    using alpha_ne old_rev_last_alpha
    by (auto simp: holed_def nth_append last_conv_nth)
  hence "Suc t = length alpha"
    using nth_eq_iff_index_eq[OF holed_distinct, of t "length alpha - 1"] True assms
    by (auto simp: holed_def)
  hence "beta \<noteq> []" "holed ! Suc t = hd beta"
    using assms
    by (auto simp: holed_def nth_append hd_conv_nth)
  thus ?thesis
    using splice_dfs True
    by simp
next
  case False
  have "holed ! t \<in> V"
    using nth_mem[of t holed] assms holed_set
    by auto
  thus ?thesis
    using dfs_step[OF _ holed_old_adj[OF assms False]]
    by simp
qed

lemma holed_nb: "t < length holed \<Longrightarrow> holed ! t \<notin> set (block S0 p)"
  using nth_mem[of t holed] holed_set
  by auto

lemma clauseJ_from_lsuc:
  assumes "parent_spec (thrd S)"
    and "\<And>v. v \<in> V \<Longrightarrow> \<exists>pre suf. follow (thrd S) v = pre @ suf \<and> set pre = children
      (prnt S) v
                                   \<and> pre \<noteq> [] \<and> hd pre = v"
    and "\<And>v pre suf. \<lbrakk>v \<in> V; follow (thrd S) v = pre @ suf; set pre = children (prnt S) v\<rbrakk>
                \<Longrightarrow> lsuc S v = last pre"
  shows "\<forall>v\<in>V. \<exists>pre. follow (thrd S) v = pre @ (case thrd S (lsuc S v) of None \<Rightarrow> [] |
    Some w \<Rightarrow> follow (thrd S) w)
           \<and> pre \<noteq> [] \<and> last pre = lsuc S v \<and> set pre = children (prnt S) v"
proof
  fix v
  assume v: "v \<in> V"
  then obtain pre suf where P: "follow (thrd S) v = pre @ suf" "set pre = children (prnt S) v" "pre \<noteq> []"
    using assms(2)
    by blast
  have "(case thrd S (last pre) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w) = suf"
  proof(cases suf)
    case Nil
    thus ?thesis
      using follow_last_None[OF assms(1), of v] P(1)
      by simp
  next
    case (Cons y ys)
    thus ?thesis
      using thread_link[OF assms(1), of v "butlast pre" "last pre" y ys] follow_append_ps[OF assms(1), of v pre y ys]
        P(1,3)
      by (cases pre rule: rev_cases) auto
  qed
  thus "\<exists>pre. follow (thrd S) v = pre @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow>
    follow (thrd S) w)
          \<and> pre \<noteq> [] \<and> last pre = lsuc S v \<and> set pre = children (prnt S) v"
    using P assms(3)[OF v P(1,2)]
    by auto
qed

lemma rV[intro]: "r \<in> V"
  using oldlist_set_V pst_follow_mem[of r]
  by simp

lemma set_takeWhile_spine:
  assumes "x \<in> V" and "x \<in> set (follow (prnt S0) c)"
  shows "set (takeWhile (\<lambda>y. lsuc S0 y = c) (follow (prnt S0) x)) = {y \<in> set (follow (prnt S0) x). lsuc S0
    y = c}"
proof(rule set_takeWhile_closed)
  fix us w ws u
  assume a: "follow (prnt S0) x = us @ w # ws" "lsuc S0 w = c" "u \<in> set us"
  from a(3) obtain us1 us2 where "us = us1 @ u # us2"
    by (auto dest: split_list)
  hence "w \<in> set (follow (prnt S0) u)"
    using a(1) ppt_follow_append[of x us1 u "us2 @ w # ws"]
    by simp
  moreover have "u \<in> V" "w \<in> V" "u \<in> set (follow (prnt S0) c)"
    using a(1,3) follow_subset_V[OF rinv0 assms(1)] ppt_follow_trans[OF assms(2), of u]
    by auto
  ultimately show "lsuc S0 u = c"
    using spine_lemma[OF a(2)]
    by blast
qed

lemma in_chain_iff:
  "v \<in> V \<Longrightarrow> v \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j))
    \<longleftrightarrow> lsuc S0 v = j"
  using blockP(2,3,4)[of v] last_in_set[of "block S0 v"] set_takeWhile_spine[OF jV ppt_follow_mem[of j]]
  by (auto simp: children_def)

lemma out_chain_set:
  assumes "jn = join_of (prnt S0) a j" and "p \<in> set (follow (prnt S0) a)"
    and "jn \<in> set (follow (prnt S0) j)" and "jn \<in> set (follow (prnt S0) p)" and "p \<noteq> jn"
  shows "set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc S0 jn = j then Some jn else None)
                              \<and> (if lsuc S0 y = j then X else lsuc S0 y) = lsuc S0 p)
                   (follow (prnt S0) (the (prnt S0 p))))
         = {y \<in> set (follow (prnt S0) (the (prnt S0 p))). lsuc S0 y = lsuc S0 p}"
proof-
  define L where "L = follow (prnt S0) (the (prnt S0 p))"
  define P where "P = (\<lambda>y. Some y \<noteq> (if lsuc S0 jn = j then Some jn else None)
                            \<and> (if lsuc S0 y = j then X else lsuc S0 y) = lsuc S0 p)"
  obtain vo where "prnt S0 p = Some vo"
    using prnt_sm_ne_None[of k] pathk
    by blast
  hence fp: "follow (prnt S0) p = p # L"
    using ppt_follow_Some
    by (simp add: L_def)
  have lspin: "lsuc S0 p \<in> set (block S0 p)"
    by (simp add: block_def)
  have "p \<in> set (follow (prnt S0) (lsuc S0 p))"
    using pblock(4) lspin
    by (simp add: children_def)
  note anc = ppt_follow_trans[OF this] ppt_follow_trans[OF assms(2)]
  have LV: "set L \<subseteq> V" and jnV: "jn \<in> V"
    using follow_subset_V[OF rinv0 pV] follow_subset_V[OF rinv0 jV] fp assms(3)
    by auto
  have voc: "the (prnt S0 p) \<in> V" "the (prnt S0 p) \<in> set (follow (prnt S0) (lsuc S0 p))"
    using ppt_follow_mem[of "the (prnt S0 p)"] LV anc(1) fp
    by (auto simp: L_def)
  have Lj: "y \<in> set (follow (prnt S0) jn) \<and> lsuc S0 jn = j" if "y \<in> set L" "lsuc S0 y = j" for y
  proof-
    have yV: "y \<in> V"
      using that(1) LV
      by auto
    hence "y \<in> set (follow (prnt S0) j)"
      using in_chain_iff[OF yV] that(2)
      by (auto dest: set_takeWhileD)
    hence "y \<in> set (follow (prnt S0) jn)"
      using ppt_join_of_first[OF anc(2)] that(1) fp assms(1)
      by simp
    thus ?thesis
      using spine_lemma[OF that(2) yV jnV assms(3)]
      by simp
  qed
  obtain A B where AB: "L = A @ jn # B"
    using split_list[of jn L] assms(4) assms(5) fp
    by auto
  have "takeWhile P L = takeWhile (\<lambda>y. lsuc S0 y = lsuc S0 p) L"
  proof(cases "lsuc S0 jn = j")
    case True
    have "lsuc S0 y \<noteq> j" if "y \<in> set A" for y
      using Lj[of y] AB ppt_follow_distinct[of "the (prnt S0 p)"] that
            ppt_follow_append[of "the (prnt S0 p)" A jn B]
      by (auto simp: L_def)
    hence "P y = (lsuc S0 y = lsuc S0 p)" if "y \<in> set A" for y
      using AB that ppt_follow_distinct[of "the (prnt S0 p)"] True
      by (auto simp: P_def L_def)
    moreover have "\<not> P jn" "lsuc S0 jn \<noteq> lsuc S0 p"
      using True lspin j_notin_block_p
      by (auto simp: P_def)
    ultimately show ?thesis
      using takeWhile_cong[of A A P "\<lambda>y. lsuc S0 y = lsuc S0 p"]
      by (simp add: AB takeWhile_append)
  next
    case False
    hence "P y = (lsuc S0 y = lsuc S0 p)" if "y \<in> set L" for y
      using Lj[OF that]
      by (auto simp: P_def)
    thus ?thesis
      by (rule takeWhile_cong[OF refl])
  qed
  thus ?thesis
    using set_takeWhile_spine[OF voc]
    by (simp add: P_def L_def)
qed

lemma succ_exits_is_last:
  assumes "parent_spec (thrd S)" and "follow (thrd S) v = pre @ suf"
    and "x \<in> set pre" and "thrd S x = None \<or> the (thrd S x) \<notin> set pre"
  shows "x = last pre"
proof(rule ccontr)
  assume xl: "x \<noteq> last pre"
  from assms(3) obtain A C where AC: "pre = A @ x # C"
    by (auto dest: split_list)
  with xl obtain y B where C: "C = y # B"
    by (cases C) auto
  hence "follow (thrd S) v = A @ x # y # (B @ suf)"
    using assms(2) AC
    by simp
  from thread_link[OF assms(1) this]
  show False
    using assms(4) AC C
    by simp
qed

lemma succ_lsuc_exits_block:
  "\<lbrakk>u \<in> V; thrd S0 (lsuc S0 u) = Some w\<rbrakk> \<Longrightarrow> w \<notin> children (prnt S0) u"
  using pst_follow_distinct[of u] blockP(1,4)[of u] pst_follow_mem[of w]
  by auto

lemma successive_block_exit:
  "\<lbrakk>v \<in> V; u \<in> V; thrd S0 (lsuc S0 v) = Some u;
    thrd S0 (lsuc S0 u) = Some w\<rbrakk> \<Longrightarrow> w \<notin> children (prnt S0) v"
  using blockP(1,4)[of v] blockP(1)[of u] pst_follow_distinct[of v] pst_follow_mem[of w]
  by auto

lemma pred_in_block:
  assumes "u \<in> V" and "thrd S0 z = Some w" and "w \<in> set (block S0 u)" and "w \<noteq> u"
  shows "z \<in> set (block S0 u)"
proof-
  obtain q where q: "q < length (block S0 u)" "block S0 u ! q = w"
    using assms(3)
    by (auto simp: in_set_conv_nth)
  hence "0 < q"
    using blockP(2,5)[OF assms(1)] assms(4)
    by (cases q) (auto simp: hd_conv_nth)
  hence "thrd S0 (block S0 u ! (q - 1)) = Some w"
    using block_link[OF assms(1), of "q - 1"] q
    by simp
  hence "z = block S0 u ! (q - 1)"
    using assms(2) arbD(10)
    by auto
  thus ?thesis
    using q(1) nth_mem[of "q - 1" "block S0 u"]
    by simp
qed

lemma old_rev_in_block_anc:
  "\<lbrakk>v \<in> V; v \<in> set (follow (prnt S0) p); p \<noteq> v\<rbrakk> \<Longrightarrow> the (rvth S0 p)
    \<in> set (block S0 v)"
  using pred_in_block[of v "the (rvth S0 p)" p] blockP(4)[of v] thrd_old_rev
  by (auto simp: children_def)

lemma old_rev_ne_jn:
  assumes "jn \<in> set (follow (prnt S0) j)" "jn \<in> set (follow (prnt S0) p)" "p \<noteq> jn"
    and "v \<in> V" and "v \<in> set (follow (prnt S0) p)"
    and "p \<noteq> v" and "lsuc S0 v = lsuc S0 p" and "j \<noteq> the (rvth S0 p)"
  shows "jn \<noteq> the (rvth S0 p)"
proof
  assume jn: "jn = the (rvth S0 p)"
  have jnV: "jn \<in> V"
    using old_rev_in_V jn
    by simp
  have lspin: "lsuc S0 p \<in> set (block S0 p)"
    by (simp add: block_def)
  have "v \<in> set (follow (prnt S0) jn)"
    using old_rev_in_block_anc[OF assms(4) assms(5) assms(6)] blockP(4)[OF assms(4)] jn
    by (simp add: children_def)
  moreover have "jn \<in> set (follow (prnt S0) (lsuc S0 p))"
    using pblock(4) lspin ppt_follow_trans[OF _ assms(2)]
    by (auto simp: children_def)
  ultimately have "lsuc S0 jn = lsuc S0 p"
    using spine_lemma[OF assms(7) assms(4) jnV]
    by blast
  moreover have "jn \<notin> set (block S0 p)"
    using ppt_ancestor_antisym[OF assms(2)] assms(3) pblock(4)
    by (auto simp: children_def)
  ultimately have "block S0 jn = jn # block S0 p"
    using pst_follow_Some[OF thrd_old_rev] jn lspin
    by (auto simp: block_def)
  moreover have "j \<in> set (block S0 jn)"
    using blockP(4)[OF jnV] assms(1)
    by (simp add: children_def)
  ultimately show False
    using assms(8) jn j_notin_block_p
    by simp
qed

definition rvth_pre where
  "rvth_pre = (let tc = (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j);
        r1 = (case tc of None \<Rightarrow> rvth Sfin | Some a \<Rightarrow> (rvth Sfin)(a \<mapsto> lsx k)) in (if the
          (rvth S0 p) \<noteq> j then (case aftn k of None \<Rightarrow> r1 | Some a \<Rightarrow> r1(a \<mapsto> the
          (rvth S0 p))) else r1))"

lemma lsuc_in_children:
  "u \<in> V \<Longrightarrow> lsuc S0 u \<in> children (prnt S0) u"
  using blockP(2,3,4)[of u] last_in_set[of "block S0 u"]
  by (auto)

lemma lsuc_off_block:
  assumes "v \<in> V" "v \<notin> set (block S0 p)"
    "\<not> (v \<in> set (follow (prnt S0) (the (prnt S0 p))) \<and> lsuc S0 v = lsuc S0 p)"
  shows "lsuc S0 v \<notin> set (block S0 p)"
proof
  assume "lsuc S0 v \<in> set (block S0 p)"
  hence anc: "p \<in> set (follow (prnt S0) (lsuc S0 v))"
    "v \<in> set (follow (prnt S0) (lsuc S0 v))"
    using pblock(4) lsuc_in_children[OF assms(1)]
    by (auto simp: children_def)
  hence "v \<in> set (follow (prnt S0) p)" "v \<noteq> p"
    using ppt_follow_linear[OF anc] assms(2) pblock(4) ppt_follow_mem[of p]
    by (auto simp: children_def)
  thus False
    using spine_lemma[OF refl assms(1) pV anc(1)] assms(3) follow_p_vout
    by (auto)
qed

lemma last_descendant_selector:
  assumes "v \<in> V" "jn \<in> set (follow (prnt S0) j)"
    "jn \<in> set (follow (prnt S0) p)" "p \<noteq> jn"
    "\<lbrakk>v \<in> set (follow (prnt S0) j);
       lsuc S0 v = j \<or> (the (rvth S0 p) = j \<and> lsuc S0 v = lsuc S0 p)\<rbrakk> \<Longrightarrow> E L"
    "\<lbrakk>v \<in> set (follow (prnt S0) p); p \<noteq> v;
       lsuc S0 v = lsuc S0 p; the (rvth S0 p) \<noteq> j\<rbrakk> \<Longrightarrow> E (the (rvth S0 p))"
    "v \<in> M \<Longrightarrow> E L"
    "\<lbrakk>lsuc S0 v \<notin> set (block S0 p); lsuc S0 v \<noteq> j\<rbrakk> \<Longrightarrow> E (lsuc S0 v)"
    "\<lbrakk>v \<in> set (block S0 p); v \<notin> M\<rbrakk> \<Longrightarrow> E (lsuc S0 v)"
  shows "E (if v \<in> set (follow (prnt S0) (the (prnt S0 p))) \<and> lsuc S0 v = lsuc S0 p
    then (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then the (rvth S0 p) else L)
    else if lsuc S0 v = j \<or> v \<in> M then L else lsuc S0 v)"
proof(cases "v \<in> set (follow (prnt S0) (the (prnt S0 p))) \<and> lsuc S0 v = lsuc S0 p")
  case True
  hence vp: "v \<in> set (follow (prnt S0) p)" "p \<noteq> v" "lsuc S0 v = lsuc S0 p"
    using follow_p_vout ppt_follow_distinct[of p]
    by (auto)
  have "the (rvth S0 p) = j \<Longrightarrow> v \<in> set (follow (prnt S0) j)"
    using old_rev_in_block_anc[OF assms(1) vp(1,2)] blockP(4)[OF assms(1)]
    by (auto simp: children_def)
  thus ?thesis
    using True vp assms(5,6) old_rev_ne_jn[OF assms(2-4,1) vp]
    by (cases "the (rvth S0 p) = j"; auto)
next
  case False
  have "lsuc S0 v = j \<Longrightarrow> v \<in> set (follow (prnt S0) j)"
    using lsuc_in_children[OF assms(1)]
    by (auto simp: children_def)
  thus ?thesis
    using False assms(5,7-9) lsuc_off_block[OF assms(1) _ False]
    by (auto split: if_splits)
qed

lemma chain_edge_iff:
  assumes "xs \<noteq> []" "set xs = V"
    "\<And>n. Suc n < length xs \<Longrightarrow> T (xs ! n) = Some (xs ! Suc n)"
    "T (last xs) = None" "\<And>x. x \<notin> V \<Longrightarrow> T x = None"
  shows "T x = Some y \<longleftrightarrow> (\<exists>n. Suc n < length xs \<and> xs ! n = x \<and> xs ! Suc n = y)"
proof
  assume edge: "T x = Some y"
  then obtain n where n: "n < length xs" "xs ! n = x"
    using assms(2,5)
    by (force simp: in_set_conv_nth)
  hence "Suc n < length xs"
    using edge assms(1,4)
    by (cases "n = length xs - 1"; auto simp: last_conv_nth)
  thus "\<exists>n. Suc n < length xs \<and> xs ! n = x \<and> xs ! Suc n = y"
    using n edge assms(3)
    by (force)
qed (use assms(3) in \<open>auto\<close>)

lemma chain_properties:
  assumes "distinct xs" "xs \<noteq> []" "set xs = V"
    "\<And>n. Suc n < length xs \<Longrightarrow> T (xs ! n) = Some (xs ! Suc n)"
    "T (last xs) = None" "\<And>x. x \<notin> V \<Longrightarrow> T x = None"
  shows "parent_spec T" "follow T (hd xs) = xs" "dom T = V - {last xs}" "ran T = V - {hd xs}"
proof-
  have edge: "T x = Some y \<longleftrightarrow>
      (\<exists>n. Suc n < length xs \<and> xs ! n = x \<and> xs ! Suc n = y)" for x y
    by (rule chain_edge_iff) (use assms in \<open>auto\<close>)
  show "parent_spec T"
    by (rule parent_spec_of_distinct_chain[OF assms(1)])
       (use edge in \<open>auto\<close>)
  thus "follow T (hd xs) = xs"
    using assms(2,4,5)
    by (auto intro: follow_eq_of_chain)
  show "dom T = V - {last xs}"
    by (rule dom_of_chain) (use assms in \<open>auto\<close>)
  have "ran T = set (tl xs)"
    using assms(2)
    by (cases xs; auto simp: ran_def edge in_set_conv_nth)
  thus "ran T = V - {hd xs}"
    using assms(1-3)
    by (cases xs; auto)
qed

definition splice :: "'a list \<Rightarrow> 'a list" where
  "splice B = takeWhile (\<lambda>x. x \<noteq> j) holed @
    j # B @ tl (dropWhile (\<lambda>x. x \<noteq> j) holed)"

lemma splice_set:
  "set B = set (block S0 p) \<Longrightarrow> set (splice B) = V"
  using set_holed_split holed_set block_p_subset_V
  by (auto simp: splice_def)

lemma splice_distinct:
  assumes "set B = set (block S0 p)" "distinct B"
  shows "distinct (splice B)"
proof-
  have "distinct (takeWhile (\<lambda>x. x \<noteq> j) holed @
      j # tl (dropWhile (\<lambda>x. x \<noteq> j) holed))"
    using holed_distinct holed_split
    by (simp only:)
  thus ?thesis
    using assms holed_set set_holed_split
    by (auto simp: splice_def)
qed

lemma splice_hd[simp]: "hd (splice B) = r"
  using hd_holed j_in_holed
  by (cases holed; auto simp: splice_def)

lemma splice_ne: "splice B \<noteq> []"
  by (simp add: splice_def)

lemma newlist_splice: "newlist = splice newblock"
  by (simp add: newlist_def splice_def)

lemma splice_adjacent:
  assumes "B \<noteq> []"
    "\<And>q. Suc q < length B \<Longrightarrow> R (B ! q) (B ! Suc q)"
    "\<And>q. \<lbrakk>Suc q < length holed; holed ! q \<noteq> j\<rbrakk> \<Longrightarrow>
       R (holed ! q) (holed ! Suc q)"
    "R j (hd B)"
    "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) \<noteq> [] \<Longrightarrow>
       R (last B) (hd (tl (dropWhile (\<lambda>x. x \<noteq> j) holed)))"
    "Suc t < length (splice B)"
  shows "R (splice B ! t) (splice B ! Suc t)"
proof-
  define A where "A = takeWhile (\<lambda>x. x \<noteq> j) holed"
  define C where "C = tl (dropWhile (\<lambda>x. x \<noteq> j) holed)"
  define xss where "xss = (A @ [j]) # B # (if C = [] then [] else [C])"
  have split: "holed = A @ j # C" "splice B = concat xss"
    unfolding A_def C_def xss_def splice_def
    by (rule holed_split) simp
  have links: "R (holed ! q) (holed ! Suc q)"
    if "Suc q < length holed" "q \<noteq> length A" for q
    using assms(3)[OF that(1)] nth_eq_iff_index_eq[OF holed_distinct, of q "length A"] that split(1)
    by (auto simp: nth_append)
  have "R (concat xss ! t) (concat xss ! Suc t)"
  proof(rule concat_linked[where R = R])
    fix ys q
    assume "ys \<in> set xss" "Suc q < length ys"
    thus "R (ys ! q) (ys ! Suc q)"
      using assms(2)[of q] links[of q] links[of "Suc (length A + q)"] split(1)
      by (auto simp: xss_def nth_append split: if_splits)
  next
    fix n
    assume "Suc n < length xss"
    hence "n = 0 \<or> (n = 1 \<and> C \<noteq> [])"
      by (auto simp: xss_def split: if_splits)
    thus "R (last (xss ! n)) (hd (xss ! Suc n))"
      using assms(4,5)
      by (auto simp: xss_def C_def)
  qed (use assms(1,6) split(2) in \<open>auto simp: xss_def split: if_splits\<close>)
  thus ?thesis
    using split(2)
    by simp
qed

lemma splice_preorder:
  assumes "parent_spec P" "B \<noteq> []" "P (hd B) = Some j"
    "j \<in> set (follow P (last B))"
    "\<And>q. Suc q < length B \<Longrightarrow>
      \<exists>a. P (B ! Suc q) = Some a \<and> a \<in> set (follow P (B ! q))"
    "\<And>q. Suc q < length holed \<Longrightarrow>
      \<exists>a. P (holed ! Suc q) = Some a \<and> a \<in> set (follow P (holed ! q))"
    "Suc t < length (splice B)"
  shows "\<exists>a. P (splice B ! Suc t) = Some a \<and> a \<in> set (follow P (splice B ! t))"
proof-
  define A where "A = takeWhile (\<lambda>x. x \<noteq> j) holed"
  define C where "C = tl (dropWhile (\<lambda>x. x \<noteq> j) holed)"
  have split: "holed = A @ j # C"
    unfolding A_def C_def
    by (rule holed_split)
  have tail: "\<exists>a. P (hd C) = Some a \<and> a \<in> set (follow P (last B))" if "C \<noteq> []"
    using assms(6)[of "length A"] follow_sub_of_mem[OF assms(1,4)] split that
    by (auto simp: nth_append hd_conv_nth)
  show ?thesis
    by (rule splice_adjacent[where R = "\<lambda>x y. \<exists>a. P y = Some a \<and> a \<in> set (follow P x)"])
       (use assms tail follow_mem_ps[OF assms(1)] in \<open>auto simp: C_def\<close>)
qed

lemma splice_last_None:
  assumes "B \<noteq> []"
    "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = [] \<Longrightarrow> T (last B) = None"
    "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) \<noteq> [] \<Longrightarrow> T (last holed) = None"
  shows "T (last (splice B)) = None"
proof(cases "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = []")
  case False
  hence "last holed = last (tl (dropWhile (\<lambda>x. x \<noteq> j) holed))"
    by (subst holed_split) (simp)
  thus ?thesis
    using assms False
    by (simp add: splice_def)
qed (use assms in \<open>simp add: splice_def\<close>)

lemma splice_terminal:
  assumes "B \<noteq> []"
    "T (last B) = (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j)"
    "the (rvth S0 p) \<noteq> j \<Longrightarrow> T (the (rvth S0 p)) = thrd S0 (lsuc S0 p)"
    "\<And>x. \<lbrakk>x \<in> set holed; x \<noteq> j; x \<noteq> the (rvth S0 p)\<rbrakk> \<Longrightarrow> T x =
      thrd S0 x"
  shows "T (last (splice B)) = None"
proof(rule splice_last_None[OF assms(1)])
  assume "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = []"
  hence "last holed = j"
    by (rule last_holed_nil)
  thus "T (last B) = None"
    using assms(2) last_holed_old_rev last_holed_beta thrd_lsuc_p_None_of_beta_nil
      thrd_last_beta_None old_rev_last_alpha alpha_beta_disjoint[unfolded disjoint_iff]
      last_in_set[OF alpha_ne] last_in_set[of beta]
    by (cases "beta = []") auto
next
  assume "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) \<noteq> []"
  hence z: "last holed \<noteq> j"
    by (rule last_holed_ne_j)
  show "T (last holed) = None"
  proof(cases "beta = []")
    case True
    thus ?thesis
      using z assms(3) last_holed_old_rev thrd_lsuc_p_None_of_beta_nil
      by simp
  next
    case False
    have "last beta \<noteq> the (rvth S0 p)" "last beta \<in> set holed"
      using alpha_beta_disjoint last_in_set[OF False] last_in_set[OF alpha_ne]
        old_rev_last_alpha set_beta_holed
        by auto
    thus ?thesis
      using z last_holed_beta[OF False] assms(4)[of "last holed"] thrd_last_beta_None[OF False]
      by simp
  qed
qed

lemma rooted_newtree_ip: "rooted_arborescense_invar r V ((prnt S0)(p \<mapsto> j))"
  by (insert prnt_sm_ne_None[of k] pathk jV jnotp; cases "prnt S0 p"; auto simp: children_def intro:
    rooted_arborescense_swap_parents(1)[OF rinv0])

lemmas parent_spec_newtree_ip = rooted_arborescense_invar_parent_spec[OF rooted_newtree_ip]

definition move_S1 :: "'a ndtree" where
  "move_S1 = (let Sa = S0\<lparr>prnt := (prnt S0)(p \<mapsto> j)\<rparr> in (if thrd Sa j = Some p then Sa else (let
    aft1 = thrd Sa (lsuc S0 p);
        Sb = (case aft1 of None \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(the (rvth S0 p) := None)\<rparr> | Some a
          \<Rightarrow> Sa\<lparr>thrd := (thrd Sa)(the (rvth S0 p) \<mapsto> a), rvth := (rvth Sa)(a \<mapsto> the
          (rvth S0 p))\<rparr>);
        aft2 = thrd Sb j;
        Sc = Sb\<lparr>thrd := (thrd Sb)(j \<mapsto> p), rvth := (rvth Sb)(p \<mapsto> j)\<rparr> in (case aft2 of None
          \<Rightarrow> Sc\<lparr>thrd := (thrd Sc)(lsuc S0 p := None)\<rparr> | Some a \<Rightarrow> Sc\<lparr>thrd :=
          (thrd Sc)(lsuc S0 p \<mapsto> a), rvth := (rvth Sc)(a \<mapsto> lsuc S0 p)\<rparr>))))"

lemma move_prnt_S1[simp]: "prnt move_S1 = (prnt S0)(p \<mapsto> j)"
  by (auto simp add: move_S1_def Let_def split: option.split)
lemma move_lsuc_S1[simp]: "lsuc move_S1 = lsuc S0"
  by (auto simp add: move_S1_def Let_def split: option.split)
lemma move_snum_S1[simp]: "snum move_S1 = snum S0"
  by (auto simp add: move_S1_def Let_def split: option.split)

lemma move_UT_fields:
  shows "prnt (update_tree S0 p j p jn) = (prnt S0)(p \<mapsto> j)" "thrd (update_tree S0 p j p jn) = thrd move_S1"
    "rvth (update_tree S0 p j p jn) = rvth move_S1"
    "lsuc (update_tree S0 p j p jn) x =
       (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p)
           \<and> x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc S0 jn = j then Some jn else None)
                    \<and> (if y \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow ((prnt S0)(p \<mapsto> j))
                      j)) then lsuc S0 p
                       else lsuc S0 y) = lsuc S0 p) (follow ((prnt S0)(p \<mapsto> j)) (the (prnt S0 p))))
        then the (rvth S0 p)
        else if x \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow ((prnt S0)(p \<mapsto> j)) j)) then lsuc S0
          p
        else lsuc S0 x)" (is "_ = ?lrhs")
    "snum (update_tree S0 p j p jn) x =
       (if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0)(p \<mapsto> j)) j)) then snum S0 x +
         snum S0 p
        else snum S0 x)
       - (if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow ((prnt S0)(p \<mapsto> j)) (the (prnt S0 p))))
         then snum S0 p
          else 0)" (is "_ = ?srhs")
proof-
  have psM: "parent_spec (prnt move_S1)"
    using parent_spec_newtree_ip move_prnt_S1
    by simp
  define Sa where "Sa = fused_vin_loop move_S1 j j jn (lsuc move_S1 p) (snum S0 p) True True"
  define Sb where "Sb = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then fused_vout_loop Sa (the
    (prnt S0 p)) (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (the (rvth S0 p)) jn (snum S0 p) True True
    else if lsuc move_S1 p \<noteq> lsuc S0 p then fused_vout_loop Sa (the (prnt S0 p)) (if lsuc move_S1 jn = j then
    Some jn else None) (lsuc S0 p) (lsuc move_S1 p) jn (snum S0 p) True True else fused_vout_loop Sa (the (prnt S0 p))
    (if lsuc move_S1 jn = j then Some jn else None) (lsuc S0 p) (lsuc S0 p) jn (snum S0 p) False True)"
  have peq: "(p = p) = True"
  by simp
  have UT: "update_tree S0 p j p jn = Sb"
    by (simp only: update_tree_def Let_def peq if_True Sb_def Sa_def move_S1_def)
  have Sa: "prnt Sa = (prnt S0)(p \<mapsto> j)" "thrd Sa = thrd move_S1" "rvth Sa = rvth move_S1"
    "lsuc Sa = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j)
       (follow ((prnt S0)(p \<mapsto> j)) j)) then lsuc S0 p else lsuc S0 x)"
    "snum Sa = (\<lambda>x. if x \<in> set (takeWhile (\<lambda>y. y \<noteq> jn)
       (follow ((prnt S0)(p \<mapsto> j)) j)) then snum S0 x + snum S0 p else snum S0 x)"
    using fused_vin_props[OF psM, of j j jn "lsuc move_S1 p" "snum S0 p" True True,
      unfolded move_prnt_S1 move_lsuc_S1 move_snum_S1]
    by (simp_all add: Sa_def move_lsuc_S1)
  have psSa: "parent_spec (prnt Sa)"
    using parent_spec_newtree_ip Sa(1)
    by simp
  show "prnt (update_tree S0 p j p jn) = (prnt S0)(p \<mapsto> j)"
    "thrd (update_tree S0 p j p jn) = thrd move_S1"
    "rvth (update_tree S0 p j p jn) = rvth move_S1"
    "lsuc (update_tree S0 p j p jn) x = ?lrhs"
    "snum (update_tree S0 p j p jn) x = ?srhs"
    unfolding UT Sb_def move_lsuc_S1
    using Sa
    by (simp_all add: fused_vout_props[OF psSa] if_distrib[of prnt] if_distrib[of thrd]
      if_distrib[of rvth] if_distrib[of lsuc] if_distrib[of snum])
qed

lemmas move_prnt = move_UT_fields(1)
lemmas move_thrd = move_UT_fields(2)
lemmas move_rvth = move_UT_fields(3)

definition movlist :: "'a list" where
  "movlist = takeWhile (\<lambda>x. x \<noteq> j) holed @ j # block S0 p @ tl (dropWhile (\<lambda>x. x \<noteq> j)
    holed)"

lemma move_S1_zero_fields:
  assumes "k = 0"
  shows "thrd move_S1 = final_thrd" "rvth move_S1 = final_rvth"
proof-
  have ip: "i = p"
    using assms path0 pathk
    by simp
  have jl: "j \<noteq> lsuc S0 p" and rl: "the (rvth S0 p) \<noteq> lsuc S0 p"
    using j_notin_block_p old_rev_notin_block_p
    by (auto simp: block_def)
  have "p \<in> dom (rvth S0)"
    by (simp add: arbD(9) pV pne_r)
  then obtain old where rev: "rvth S0 p = Some old"
    by auto
  have jp: "thrd S0 j = Some p \<longleftrightarrow> the (rvth S0 p) = j"
    using arbD(10)[of j p] rev
    by auto
  have inject: "thrd S0 a = Some x \<Longrightarrow> thrd S0 b = Some x \<Longrightarrow> a = b" for a b x
    using arbD(10)[of a x] arbD(10)[of b x]
    by auto
  show "thrd move_S1 = final_thrd"
    unfolding move_S1_def final_thrd_def thrd_inv_def lsx_def aftn_def out_def
    using jl rl jp
    by (auto simp: Let_def assms path0 ip fun_eq_iff split: option.splits)
  have last_np: "thrd S0 (lsuc S0 p) \<noteq> Some p"
    using arbD(10)[of "lsuc S0 p" p] rev rl
    by (auto)
  show "rvth move_S1 = final_rvth"
    unfolding move_S1_def final_rvth_def final_thrd_def Sfin_def drt_def
      thrd_inv_def revBR_def lsx_def aftn_def out_def
    using jl rl jp rev last_np
    by (cases "thrd S0 j"; cases "thrd S0 (lsuc S0 p)")
       (auto simp: Let_def assms path0 ip fun_eq_iff dest: inject arbD(10)[THEN iffD1])
qed

lemma zero_follow_stem:
  "k = 0 \<Longrightarrow> takeWhile (\<lambda>x. x \<noteq> i) (follow newprnt p) = []"
  using follow_hd_ps[OF rooted_arborescense_invar_parent_spec[OF clauseA], of p]
    follow_ne_ps[OF rooted_arborescense_invar_parent_spec[OF clauseA], of p] path0 pathk
  by (simp add: takeWhile_eq_Nil_iff)

lemma update_tree_zero_fields:
  assumes "k = 0"
  shows "prnt (update_tree S0 i j p jn) = newprnt"
    "thrd (update_tree S0 i j p jn) = final_thrd"
    "rvth (update_tree S0 i j p jn) = final_rvth"
    "snum (update_tree S0 i j p jn) = final_snum jn"
    "lsuc (update_tree S0 i j p jn) = final_lsuc jn"
proof-
  have ip: "i = p"
  using assms path0 pathk
  by simp
  have pref: "takeWhile (\<lambda>x. x \<noteq> i) (follow newprnt p) = []"
    by (rule zero_follow_stem[OF assms])
  have l: "lsuc_stem = lsuc S0"
    unfolding lsuc_stem_def pref lsx_def
    by (simp add: assms ip)
  show "prnt (update_tree S0 i j p jn) = newprnt"
    "thrd (update_tree S0 i j p jn) = final_thrd"
    "rvth (update_tree S0 i j p jn) = final_rvth"
    using move_UT_fields(1-3) move_S1_zero_fields[OF assms]
    by (simp_all add: ip assms REV_0 s_pred_def)
  show "snum (update_tree S0 i j p jn) = final_snum jn"
    unfolding final_snum_def Let_def pref
    using move_UT_fields(5)[of jn]
    by (auto simp: assms  s_pred_def ip fun_eq_iff)
  show "lsuc (update_tree S0 i j p jn) = final_lsuc jn"
    unfolding final_lsuc_def lsuc_in_def Let_def l
    using move_UT_fields(4)[of jn]
    by (auto simp: assms  s_pred_def ip fun_eq_iff)
qed

lemma update_tree_fields_all:
  "prnt (update_tree S0 i j p jn) = newprnt"
  "thrd (update_tree S0 i j p jn) = final_thrd"
  "rvth (update_tree S0 i j p jn) = final_rvth"
  "snum (update_tree S0 i j p jn) = final_snum jn"
  "lsuc (update_tree S0 i j p jn) = final_lsuc jn"
  by (cases "k = 0"; use update_tree_zero_fields update_tree_fields in auto)+

end

subsection \<open>A shared invariant proof for all pivot stems\<close>

locale stem_pivot = stem_setup_geom +
  fixes jn :: 'a
  assumes jneq: "jn = join_of (prnt S0) i j"
      and jnp: "jn \<in> set (follow (prnt S0) p)"
      and pjn: "p \<noteq> jn"
begin

lemmas update_tree_fields = update_tree_fields_all
lemmas update_tree_prnt = update_tree_fields(1)
lemmas update_tree_thrd = update_tree_fields(2)
lemmas update_tree_rvth = update_tree_fields(3)
lemmas update_tree_snum = update_tree_fields(4)
lemmas update_tree_lsuc = update_tree_fields(5)

lemmas jnj = join_facts(1)[OF jneq]
lemmas pivot_prems =  jneq jnp pjn jnj

lemma follow_newprnt_free:
  assumes "\<forall>m\<le>k. s m \<notin> set (follow (prnt S0) u)"
  shows "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) u = follow (prnt S0) u"
proof-
  have "\<forall>y\<in>set (follow (prnt S0) u). prnt S0 y = Wseq (Suc k) y"
    using assms
    by (fastforce intro!: Wseq_fresh[symmetric] simp: less_Suc_eq_le)
  thus ?thesis
    using ppt_follow_eq_on[OF rooted_arborescense_invar_parent_spec[OF clauseA]] newprnt_eq
    by simp
qed

lemma follow_newprnt_j:
  "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) j = follow (prnt S0) j"
  using follow_newprnt_free stem_notin_follow_j
  by blast

lemma stem_notin_follow_vout:
  assumes "m \<le> k"
  shows "s m \<notin> set (follow (prnt S0) (the (prnt S0 p)))"
proof
  assume "s m \<in> set (follow (prnt S0) (the (prnt S0 p)))"
  hence "p \<in> set (follow (prnt S0) (the (prnt S0 p)))"
    using ppt_follow_trans[OF _ stem_chain[OF order_refl assms(1)]] pathk
    by simp
  thus False
    using prnt_sm_ne_None[of k] pathk ppt_follow_Some[of p] ppt_follow_distinct[of p]
    by auto
qed

lemma follow_newprnt_vout:
  "follow ((prnt S0 ++ REV k)(p \<mapsto> s_pred k)) (the (prnt S0 p)) = follow (prnt S0) (the (prnt S0 p))"
  using pivot_prems
    follow_newprnt_free stem_notin_follow_vout
  by blast

lemma r_notin_stem: "r \<notin> s ` {..k}"
  using ppt_follow_None[of r] arbD(5) stem_chain[of k] pathk pne_r
  by (force)

lemma jn_notin_stem:
  "jn \<notin> s ` {..k}"
  using pivot_prems
    stem_chain[of k] pathk ppt_ancestor_antisym[of p jn]
  by auto

lemma newprnt_ps: "parent_spec newprnt"
  using clauseA rooted_arborescense_invar_parent_spec
  by auto

lemma newprnt_i[simp]: "newprnt i = Some j"
  using fun_cong[OF newprnt_eq, of i] Wseq_eval[of "Suc k" 0] path0
  by (simp add: s_pred_def)

lemma follow_newprnt_off_block:
  assumes "u \<notin> set (block S0 p)"
  shows "follow newprnt u = follow (prnt S0) u"
  by (rule follow_newprnt_free; use assms stem_chain[of k] pathk ppt_children_subset pblock(4) in \<open>fastforce
    simp: children_def\<close>)

lemma follow_newprnt_i:
  "follow newprnt i = i # follow (prnt S0) j"
  using follow_Some_ps[OF newprnt_ps newprnt_i] follow_newprnt_j
  by (simp only:)

lemma children_newprnt_i_sub:
   "children newprnt i \<subseteq> set (block S0 p)"
  using stem_chain[of k 0] pathk path0 follow_newprnt_off_block ppt_children_subset[of i p] pblock(4)
  by (fastforce simp: children_def)

lemma block_p_newprnt_step:
  assumes "u \<in> set (block S0 p)" "u \<noteq> i"
  shows "\<exists>w. newprnt u = Some w \<and> w \<in> set (block S0 p)"
proof(cases "u \<in> s ` {..k}")
  case True
  then obtain m where "m \<le> k" "u = s m"
    by auto
  moreover hence "0 < m"
    using assms(2) path0
    by (cases m) auto
  moreover have "newprnt (s m) = Some (s (m - 1))"
    using fun_cong[OF newprnt_eq, of "s m"] Wseq_eval[of "Suc k" m] \<open>m \<le> k\<close> \<open>0 < m\<close>
    by (simp add: s_pred_def)
  ultimately show ?thesis
    using stem_chain[of k "m - 1"] pathk pblock(4)
    by (auto simp: children_def)
next
  case False
  hence "newprnt u = prnt S0 u"
    using fun_cong[OF newprnt_eq, of u] Wseq_fresh[of "Suc k" u]
    by (simp add: image_iff less_Suc_eq_le)
  moreover have "p \<in> set (follow (prnt S0) u)" "u \<noteq> p"
    using assms(1) pblock(4) False pathk
    by (auto simp: children_def)
  ultimately show ?thesis
    using pblock(4)
    by (cases "prnt S0 u") (auto simp: ppt_follow_None ppt_follow_Some children_def)
qed

lemma block_p_under_i:
   "u \<in> set (block S0 p) \<longrightarrow> i \<in> set (follow newprnt u)"
  using newprnt_ps
proof(induction u rule: parent_walk_induct)
  case IH: (step u)
  thus ?case
    using block_p_newprnt_step[of u]
    by (cases "u = i") (auto simp: parent_walk_simps newprnt_ps simp del: fun_upd_apply)
qed

lemma children_newprnt_i:
  "children newprnt i = set (block S0 p)"
  using pivot_prems
    children_newprnt_i_sub block_p_under_i
  by (auto simp: children_def)

lemma card_children_newprnt_i:
  "card (children newprnt i) = snum S0 p"
  using pivot_prems
    children_newprnt_i pblock(4) arbD(12)[OF pV]
  by simp

lemma children_newprnt_decomp:
   "children newprnt v =
     (children (prnt S0) v - set (block S0 p)) \<union> {u \<in> set (block S0 p). v \<in> set (follow newprnt u)}"
  by (auto simp: children_def; (rename_tac x; case_tac "x \<in> set (block S0 p)"; auto simp:
    follow_newprnt_off_block))

lemma block_p_desc_of_j:
  "\<lbrakk>v \<in> set (follow (prnt S0) j); u \<in> set (block S0 p)\<rbrakk> \<Longrightarrow> v \<in> set
    (follow newprnt u)"
  using follow_trans[OF newprnt_ps, of i u v] block_p_under_i[of u] follow_newprnt_i
  by auto

lemma children_newprnt_jpath:
  "v \<in> set (follow (prnt S0) j) \<Longrightarrow> children newprnt v = children (prnt S0) v \<union> set (block S0
    p)"
  using pivot_prems
    children_newprnt_decomp[of v] block_p_desc_of_j[of v]
  by auto

lemmas below_jn = below_jn_gen[where w = j]

lemma inchain_block_disjoint:
  assumes "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) j))"
  shows "children (prnt S0) v \<inter> set (block S0 p) = {}"
proof-
  have "v \<in> set (follow (prnt S0) j)" "jn \<in> set (follow (prnt S0) v)" "v \<noteq> jn"
    using set_takeWhileD[OF assms(1)] below_jn_gen[OF assms(1) jnj]
    by auto
  moreover hence "p \<notin> set (follow (prnt S0) v)"
    using jnotp ppt_children_subset[of v p]
    by (auto simp: children_def)
  moreover have "v \<notin> set (follow (prnt S0) p)"
  proof
    assume "v \<in> set (follow (prnt S0) p)"
    hence "v \<in> set (follow (prnt S0) i)"
      using ppt_follow_trans[OF _ \<open>v \<in> set (follow (prnt S0) p)\<close>] stem_chain[of k 0] pathk path0
      by simp
    thus False
      using ppt_join_of_first[OF _ \<open>v \<in> set (follow (prnt S0) j)\<close>] ppt_ancestor_antisym[of v jn]
            calculation jneq
      by auto
  qed
  ultimately show ?thesis
    using ppt_follow_linear[of v _ p] pblock(4)
    by (auto simp: children_def)
qed

lemma i_in_block[intro]: "i \<in> set (block S0 p)"
  using stem_chain[of k 0] pathk path0 pblock(4)
  by (auto simp: children_def)

lemma card_children_newprnt_INchain:
  assumes "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) j))"
  shows "card (children newprnt v) = snum S0 v + snum S0 p"
proof-
  have "v \<in> set (follow (prnt S0) j)"
    using set_takeWhileD[OF assms(1)]
    by simp
  moreover hence "v \<in> V"
    using follow_subset_V[OF rinv0 jV]
    by auto
  ultimately show ?thesis
    using children_newprnt_jpath inchain_block_disjoint[OF assms(1)] children_finite on_card
          arbD(12)
    by (simp add: card_Un_disjoint)
qed

lemma newprnt_follow_dichotomy:
  "\<lbrakk>u \<in> set (block S0 p); v \<in> set (follow newprnt u)\<rbrakk> \<Longrightarrow> v \<in> set (block
    S0 p) \<or> v \<in> set (follow (prnt S0) j)"
  using follow_linear[OF newprnt_ps, of v u i] block_p_under_i[of u] follow_newprnt_i
    children_newprnt_i i_in_block
  by (auto simp: children_def)

lemma children_newprnt_off_jpath:
  "\<lbrakk>v \<notin> set (block S0 p); v \<notin> set (follow (prnt S0) j)\<rbrakk> \<Longrightarrow> children
    newprnt v = children (prnt S0) v - set (block S0 p)"
  using pivot_prems
    children_newprnt_decomp[of v] newprnt_follow_dichotomy[of _ v]
  by auto

lemma card_children_newprnt_OUTchain:
  assumes "v \<in> set (takeWhile (\<lambda>x. x \<noteq> jn) (follow (prnt S0) (the (prnt S0 p))))"
  shows "card (children newprnt v) = snum S0 v - snum S0 p"
proof-
  have "v \<in> set (follow (prnt S0) (the (prnt S0 p)))"
    using set_takeWhileD[OF assms(1)]
    by simp
  moreover hence "jn \<in> set (follow (prnt S0) v)" "v \<noteq> jn" "v \<in> set (follow (prnt S0) p)"
    using below_jn_gen[OF assms(1)] jnp pjn follow_p_vout
    by auto
  moreover hence "v \<in> V"
    using follow_subset_V[OF rinv0 pV]
    by auto
  moreover have "v \<notin> set (block S0 p)"
  proof
    assume "v \<in> set (block S0 p)"
    hence "p \<in> set (follow (prnt S0) (the (prnt S0 p)))"
      using ppt_follow_trans[OF \<open>v \<in> set (follow (prnt S0) (the (prnt S0 p)))\<close>] pblock(4)
      by (auto simp: children_def)
    thus False
      using follow_p_vout ppt_follow_distinct[of p]
      by simp
  qed
  moreover have "v \<notin> set (follow (prnt S0) j)"
  proof
    assume "v \<in> set (follow (prnt S0) j)"
    moreover have "v \<in> set (follow (prnt S0) i)"
      using ppt_follow_trans[OF _ \<open>v \<in> set (follow (prnt S0) p)\<close>] stem_chain[of k 0] pathk path0
      by simp
    ultimately show False
      using ppt_join_of_first[of v i j] ppt_ancestor_antisym[of v jn] jneq
            \<open>jn \<in> set (follow (prnt S0) v)\<close> \<open>v \<noteq> jn\<close>
      by auto
  qed
  moreover have "set (block S0 p) \<subseteq> children (prnt S0) v"
    using ppt_follow_trans[OF _ \<open>v \<in> set (follow (prnt S0) p)\<close>] pblock(4)
    by (auto simp: children_def)
  ultimately show ?thesis
    using children_newprnt_off_jpath on_card arbD(12)
          card_Diff_subset[OF finite_set \<open>set (block S0 p) \<subseteq> children (prnt S0) v\<close>]
    by simp
qed

lemma card_children_newprnt_jpath_above:
  "\<lbrakk>v \<in> set (follow (prnt S0) j); set (block S0 p) \<subseteq> children (prnt S0) v; v \<in> V\<rbrakk>
    \<Longrightarrow> card (children newprnt v) = snum S0 v"
  using pivot_prems
    children_newprnt_jpath[of v] arbD(12)
  by (simp add: Un_absorb2)

lemma card_children_newprnt_disjoint:
  "\<lbrakk>v \<notin> set (block S0 p); v \<notin> set (follow (prnt S0) j); set (block S0 p) \<inter> children (prnt
    S0) v = {}; v \<in> V\<rbrakk> \<Longrightarrow> card (children newprnt v) = snum S0 v"
  using pivot_prems
    children_newprnt_off_jpath[of v] arbD(12)
  by (simp add: Diff_triv Int_commute)

lemma stem_follow_iff:
  "\<lbrakk>a \<le> k; b \<le> k\<rbrakk> \<Longrightarrow> (s a \<in> set (follow (prnt S0) (s b))) = (b \<le> a)"
  using stem_chain[of a b] stem_chain[of b a] ppt_ancestor_antisym[of "s a" "s b"] inj
  by (cases "b \<le> a") (auto simp: inj_on_eq_iff)

lemma follow_stem_prefix:
  "a \<le> k \<Longrightarrow> follow (prnt S0) (s a) = map s [a..<Suc k] @ follow (prnt S0) (the (prnt S0 p))"
proof(induction rule: inc_induct)
  case (step n)
  thus ?case
    using pathS[of n] ppt_follow_Some[of "s n" "s (Suc n)"]
    by (simp add: upt_conv_Cons)
qed (simp add: follow_p_vout pathk)

lemma block_notin_follow_i:
  "\<lbrakk>w \<in> set (block S0 p); w \<notin> s ` {..k}\<rbrakk> \<Longrightarrow> w \<notin> set (follow (prnt S0)
    i)"
  using follow_stem_prefix[of 0] path0 ppt_follow_trans[of w "the (prnt S0 p)" p] follow_p_vout
        ppt_follow_distinct[of p] pblock(4)
  by (auto simp: children_def atMost_upto)

lemma stem_notin_jpath:
  "t \<le> k \<Longrightarrow> s t \<notin> set (follow (prnt S0) j)"
  using pivot_prems
    stem_chain[of t 0] stem_chain[of k t] path0 pathk ppt_join_of_first[of "s t" i j]
        ppt_follow_trans[of p "s t" jn] ppt_ancestor_antisym[of "s t" jn]
        ppt_ancestor_antisym[of p jn]
  by auto

lemma stem_index:
  assumes "u \<in> s ` {..k}" "u \<noteq> i"
  shows "\<exists>m. 0 < m \<and> m \<le> k \<and> u = s m"
proof-
  obtain m where "m \<le> k" "u = s m"
    using assms(1)
    by auto
  moreover hence "0 < m"
    using assms(2) path0
    by (cases m) auto
  ultimately show ?thesis
    by blast
qed

lemma newprnt_stem: "\<lbrakk>0 < m; m \<le> k\<rbrakk> \<Longrightarrow> newprnt (s m) = Some (s (m - 1))"
  using fun_cong[OF newprnt_eq, of "s m"] Wseq_eval[of "Suc k" m]
  by (simp add: s_pred_def)

lemma newprnt_off_stem: "u \<notin> s ` {..k} \<Longrightarrow> newprnt u = prnt S0 u"
  using fun_cong[OF newprnt_eq, of u] Wseq_fresh[of "Suc k" u]
  by (simp add: image_iff less_Suc_eq_le)

lemma lsuc_stem_eq: "lsuc_stem x = (if x \<in> s ` {..k} then lsx k else lsuc S0 x)"
proof-
  have "x \<in> (\<lambda>y. the (newprnt y)) ` set (takeWhile (\<lambda>x. x \<noteq> i) (follow newprnt p))
    \<longleftrightarrow> x \<in> s ` {..<k}"
  proof
    assume "x \<in> (\<lambda>y. the (newprnt y)) ` set (takeWhile (\<lambda>x. x \<noteq> i) (follow newprnt p))"
    then obtain t where "t \<in> {1..<Suc k}" "x = the (newprnt (s t))"
      unfolding chainStem_set
      by blast
    thus "x \<in> s ` {..<k}"
      using newprnt_stem[of t]
      by (force simp del: fun_upd_apply)
  next
    assume "x \<in> s ` {..<k}"
    then obtain t where t: "t < k" "x = s t"
      by auto
    hence "s (Suc t) \<in> set (takeWhile (\<lambda>x. x \<noteq> i) (follow newprnt p))"
      by (auto simp: chainStem_set)
    from rev_image_eqI[OF this, of x "\<lambda>y. the (newprnt y)"]
    show "x \<in> (\<lambda>y. the (newprnt y)) ` set (takeWhile (\<lambda>x. x \<noteq> i) (follow newprnt p))"
      using newprnt_stem[of "Suc t"] t
      by (simp del: fun_upd_apply)
  qed
  thus ?thesis
    using pathk
    by (auto simp: lsuc_stem_def lessThan_Suc_atMost[symmetric] lessThan_Suc fun_upd_apply[of "lsuc S0"]
             simp del: fun_upd_apply)
qed

lemma lsuc_in_eq:
  "lsuc_in x = (if x \<in> set (takeWhile (\<lambda>y. lsuc S0 y = j) (follow (prnt S0) j)) then lsx k else lsuc_stem
    x)"
proof-
  have "takeWhile (\<lambda>y. lsuc_stem y = j) (follow newprnt j) = takeWhile (\<lambda>y. lsuc S0 y = j) (follow
    (prnt S0) j)"
    using stem_notin_follow_j
    by (auto simp: follow_newprnt_j lsuc_stem_eq intro!: takeWhile_cong)
  thus ?thesis
    using pathk rev_image_eqI[of k "{..k}" p s]
    by (simp add: lsuc_in_def lsuc_stem_eq)
qed

lemma final_lsuc_off:
  assumes "x \<notin> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc_stem jn = j then Some jn else None) \<and>
    lsuc_in y = lsuc S0 p)
                              (follow newprnt (the (prnt S0 p))))"
  shows "final_lsuc jn x = lsuc_in x"
  unfolding final_lsuc_def Let_def
  by (simp only: if_distrib[where f = "\<lambda>h. h x"] assms if_False if_cancel)

lemma final_lsuc_on:
  assumes "x \<in> set (takeWhile (\<lambda>y. Some y \<noteq> (if lsuc_stem jn = j then Some jn else None) \<and>
    lsuc_in y = lsuc S0 p)
                              (follow newprnt (the (prnt S0 p))))"
  shows "final_lsuc jn x = (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then the (rvth S0 p) else
    lsx k)"
proof-
  have "lsuc_in x = lsuc S0 p" "lsuc_stem p = lsx k" "(if lsx k \<noteq> lsuc S0 p then lsx k else lsuc S0 p) = lsx k"
    using takeWhile_holds[OF assms] lsuc_stem_eq[of p] pathk
    by auto
  thus ?thesis
    unfolding final_lsuc_def Let_def
    by (simp only: if_distrib[where f = "\<lambda>h. h x"] assms if_True)
qed
lemma newpath_stem_char:
   "u \<in> set (block S0 p) \<longrightarrow> (\<forall>t. 1 \<le> t \<and> t \<le> k \<longrightarrow>
           (s t \<in> set (follow newprnt u)) = (s (t - 1) \<notin> set (follow (prnt S0) u)))"
  using newprnt_ps
proof(induction u rule: parent_walk_induct)
  case IH: (step u)
  show ?case
  proof(intro impI allI, cases "u = i")
    fix t
    assume "u \<in> set (block S0 p)" "u \<noteq> i" "1 \<le> t \<and> t \<le> k"
    then obtain w where w: "newprnt u = Some w" "w \<in> set (block S0 p)"
      using block_p_newprnt_step
      by blast
    hence step: "(s t \<in> set (follow newprnt u)) = (s t = u \<or> s (t - 1) \<notin> set (follow (prnt S0) w))"
      using IH[OF w(1)] \<open>1 \<le> t \<and> t \<le> k\<close>
      by (simp only: follow_Some_ps[OF newprnt_ps w(1)] list.set(2) insert_iff)
    show "(s t \<in> set (follow newprnt u)) = (s (t - 1) \<notin> set (follow (prnt S0) u))"
    proof(cases "u \<in> s ` {..k}")
      case True
      then obtain m where "0 < m" "m \<le> k" "u = s m"
        using stem_index \<open>u \<noteq> i\<close>
        by blast
      moreover hence "w = s (m - 1)" "t - 1 \<le> k" "m - 1 \<le> k"
        using w(1) newprnt_stem[of m] \<open>1 \<le> t \<and> t \<le> k\<close>
        by auto
      ultimately have "(s t \<in> set (follow newprnt u)) = (t = m \<or> \<not> m - 1 \<le> t - 1)"
        "(s (t - 1) \<notin> set (follow (prnt S0) u)) = (\<not> m \<le> t - 1)"
        using step stem_follow_iff[of "t - 1" m] stem_follow_iff[of "t - 1" "m - 1"]
              inj_on_eq_iff[OF inj, of t m] \<open>1 \<le> t \<and> t \<le> k\<close>
        by simp_all
      thus ?thesis
        using \<open>0 < m\<close> \<open>1 \<le> t \<and> t \<le> k\<close>
        by linarith
    next
      case False
      hence "prnt S0 u = Some w"
        using newprnt_off_stem w(1)
        by simp
      thus ?thesis
        using step ppt_follow_Some False \<open>1 \<le> t \<and> t \<le> k\<close>
        by auto
    qed
  next
    fix t
    assume "u = i" "1 \<le> t \<and> t \<le> k"
    moreover hence "t - 1 \<le> k"
      by linarith
    ultimately show "(s t \<in> set (follow newprnt u)) = (s (t - 1) \<notin> set (follow (prnt S0) u))"
      using follow_newprnt_i stem_notin_jpath stem_chain[of "t - 1" 0] path0 inj
      by (auto simp: inj_on_eq_iff)
  qed
qed

lemma children_newprnt_stem:
  assumes "1 \<le> t" "t \<le> k"
  shows "children newprnt (s t) = set (block S0 p) - set (block S0 (s (t - 1)))"
proof-
  have "children newprnt (s t) \<subseteq> set (block S0 p)"
  proof
    fix u
    assume "u \<in> children newprnt (s t)"
    thus "u \<in> set (block S0 p)"
      using follow_newprnt_off_block[of u] stem_chain[of k t] pathk assms(2)
            ppt_children_subset[of "s t" p] pblock(4)
      by (auto simp: children_def)
  qed
  thus ?thesis
    using newpath_stem_char assms(1) assms(2) blockP(4)[OF sV[of "t - 1"]]
    by (auto simp: children_def)
qed

lemma card_children_newprnt_stem:
  assumes "1 \<le> t" "t \<le> k"
  shows "card (children newprnt (s t)) = snum S0 p - snum S0 (s (t - 1))"
proof-
  have "set (block S0 (s (t - 1))) \<subseteq> set (block S0 p)"
    using stem_chain[of k "t - 1"] pathk assms(2) ppt_children_subset[of "s (t - 1)" p]
          pblock(4) blockP(4)[OF sV[of "t - 1"]]
    by (auto simp: children_def)
  thus ?thesis
    using children_newprnt_stem[OF assms(1) assms(2)] card_Diff_subset[OF finite_set \<open>set (block S0 (s (t - 1)))
      \<subseteq> _\<close>]
          on_card arbD(12)[OF sV[of "t - 1"]] blockP(4)[OF sV[of "t - 1"]]  assms(2)
    by simp
qed

lemma newpath_nonstem_char:
  assumes "w \<in> set (block S0 p)" "w \<notin> s ` {..k}"
  shows "u \<in> set (block S0 p) \<longrightarrow> (w \<in> set (follow newprnt u)) = (w \<in> set (follow (prnt S0)
    u))"
  using newprnt_ps
proof(induction u rule: parent_walk_induct)
  case IH: (step u)
  show ?case
  proof(intro impI, cases "u = i")
    assume "u \<in> set (block S0 p)" "u \<noteq> i"
    then obtain v where v: "newprnt u = Some v" "v \<in> set (block S0 p)"
      using block_p_newprnt_step
      by blast
    hence step: "(w \<in> set (follow newprnt u)) = (w = u \<or> w \<in> set (follow (prnt S0) v))"
      using IH[OF v(1)]
      by (simp only: follow_Some_ps[OF newprnt_ps v(1)] list.set(2) insert_iff)
    show "(w \<in> set (follow newprnt u)) = (w \<in> set (follow (prnt S0) u))"
    proof(cases "u \<in> s ` {..k}")
      case True
      then obtain m where "0 < m" "m \<le> k" "u = s m"
        using stem_index \<open>u \<noteq> i\<close>
        by blast
      moreover hence "v = s (m - 1)" "prnt S0 (s (m - 1)) = Some u"
        using v(1) newprnt_stem[of m] pathS[of "m - 1"]
        by auto
      ultimately show ?thesis
        using step ppt_follow_Some[of "s (m - 1)" u] assms(2)
        by auto
    next
      case False
      thus ?thesis
        using step newprnt_off_stem v(1) ppt_follow_Some[of u v]
        by auto
    qed
  next
    assume "u = i"
    thus "(w \<in> set (follow newprnt u)) = (w \<in> set (follow (prnt S0) u))"
      using follow_newprnt_i block_notin_follow_j[OF assms(1)] block_notin_follow_i[OF assms(1) assms(2)] assms(2)
            path0
      by auto
  qed
qed

lemma card_children_newprnt_nonstem_block:
  assumes "w \<in> set (block S0 p)" "w \<notin> s ` {..k}"
  shows "card (children newprnt w) = snum S0 w"
proof-
  have "(w \<in> set (follow newprnt u)) = (w \<in> set (follow (prnt S0) u))" for u
    using newpath_nonstem_char[OF assms(1) assms(2), of u] follow_newprnt_off_block[of u]
    by (cases "u \<in> set (block S0 p)") auto
  moreover have "w \<in> V"
    using assms(1) pblock(4) ppt_follow_None[of w] arbD(5) pV
    by (cases "w \<in> V") (auto simp: children_def)
  ultimately show ?thesis
    using arbD(12)
    by (simp add: children_def)
qed

lemma jpath_above_block_sub:
  assumes "v \<in> set (follow (prnt S0) j)" "v \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0)
    j))"
  shows "set (block S0 p) \<subseteq> children (prnt S0) v"
  using notin_takeWhile_dropWhile[OF assms(1) assms(2)] follow_dropWhile[OF ppt jnj]
        ppt_follow_trans[OF jnp, of v] ppt_children_subset[of p v] pblock(4)
  by (simp add: children_def)

lemma disjoint_block_int:
  assumes "v \<notin> set (follow (prnt S0) j)" "v \<notin> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt
    S0) (the (prnt S0 p))))" "v \<notin> set (block S0 p)"
  shows "set (block S0 p) \<inter> children (prnt S0) v = {}"
proof-
  have jnvo: "jn \<in> set (follow (prnt S0) (the (prnt S0 p)))"
    using jnp pjn follow_p_vout
    by simp
  have "v \<notin> set (follow (prnt S0) p)"
  proof
    assume "v \<in> set (follow (prnt S0) p)"
    hence "v \<in> set (follow (prnt S0) (the (prnt S0 p)))"
      using assms(3) follow_p_vout hd_in_set[OF pblock(2)] pblock(5)
      by auto
    thus False
      using notin_takeWhile_dropWhile[OF _ assms(2)] follow_dropWhile[OF ppt jnvo]
            ppt_follow_trans[OF jnj, of v] assms(1)
      by simp
  qed
  moreover have "v \<notin> children (prnt S0) p"
    using assms(3) pblock(4)
    by simp
  ultimately show ?thesis
  proof(intro equals0I)
    fix x
    assume "x \<in> set (block S0 p) \<inter> children (prnt S0) v"
    hence vx: "v \<in> set (follow (prnt S0) x)" and px: "p \<in> set (follow (prnt S0) x)"
      using pblock(4)
      by (auto simp: children_def)
    show False
      using ppt_follow_linear[OF vx px] \<open>v \<notin> set (follow (prnt S0) p)\<close> \<open>v \<notin> children
        (prnt S0) p\<close>
      by (simp add: children_def)
  qed
qed

lemma in_out_disjoint:
  assumes "v \<in> set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) j))" "v \<in> set (takeWhile
    (\<lambda>y. y \<noteq> jn) (follow (prnt S0) (the (prnt S0 p))))"
  shows False
proof-
  have "v \<in> set (follow (prnt S0) i)"
    using set_takeWhileD[OF assms(2)] follow_p_vout ppt_follow_trans[of p i v] stem_chain[of k 0] pathk path0
    by simp
  thus False
    using ppt_join_of_first[OF _ conjunct1[OF set_takeWhileD[OF assms(1)]]]
          below_jn[OF assms(1) join_facts(1)[OF jneq]] ppt_ancestor_antisym[of v jn] jneq
    by auto
qed

lemma snum_card_match:
  assumes "v \<in> V"
  shows "final_snum jn v = card (children newprnt v)"
proof-
  note jf = join_facts[OF jneq]
  note fs = final_snum_def Let_def chainStem_set follow_newprnt_j follow_newprnt_vout
  let ?IN = "set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) j))"
  let ?OUT = "set (takeWhile (\<lambda>y. y \<noteq> jn) (follow (prnt S0) (the (prnt S0 p))))"
  have rest: "card (children newprnt v) = snum S0 v" if "v \<notin> s ` {..k}" "v \<notin> ?IN" "v \<notin> ?OUT"
    using card_children_newprnt_nonstem_block[OF _ that(1)]
          card_children_newprnt_jpath_above[OF _ jpath_above_block_sub[OF _ that(2)] assms(1)]
          card_children_newprnt_disjoint[OF _ _ disjoint_block_int[OF _ that(3) _] assms(1)]
    by blast
  show ?thesis
  proof(cases "v \<in> s ` {..k}")
    case True
    hence "v \<notin> ?IN" "v \<notin> ?OUT"
      using stem_notin_follow_j stem_notin_follow_vout
      by (auto dest: set_takeWhileD)
    moreover have "v \<noteq> i \<Longrightarrow> v \<in> s ` {1..<Suc k}"
      using stem_index[OF True]
      by fastforce
    ultimately have "final_snum jn v = (if v = i then snum S0 p else snum S0 p - snum S0 (the (newprnt v)))"
      using path0
      by (auto simp: fs simp del: fun_upd_apply)
    thus ?thesis
      using stem_index[OF True] newprnt_stem card_children_newprnt_i
            card_children_newprnt_stem
      by (cases "v = i") (auto simp del: fun_upd_apply)
  next
    case False
    moreover hence "v \<notin> s ` {1..<Suc k}" "v \<noteq> i"
      using path0
      by auto
    ultimately show ?thesis
      using rest in_out_disjoint card_children_newprnt_INchain[OF _]
            card_children_newprnt_OUTchain
      by (auto simp: fs)
  qed
qed

lemma clauseI:
  "\<forall>v\<in>V. snum (update_tree S0 i j p jn) v = card (children (prnt (update_tree S0 i j p jn)) v)"
  using pivot_prems
    update_tree_snum update_tree_prnt snum_card_match
  by simp

lemma final_thrd_fresh:
  assumes "q \<notin> lsx ` {..k}" "q \<notin> bef ` set [0..<k]" "q \<noteq> j" "q \<noteq> the (rvth S0 p)"
  shows "final_thrd q = thrd S0 q"
proof-
  have "thrd_inv k q = thrd S0 q"
    using thrd_inv_eval_fresh[OF _ assms(2,3)] assms(1)
    by force
  thus ?thesis
    using assms
    by (auto simp: final_thrd_def Let_def split: option.split)
qed

lemma block_decomp:
  assumes "m < k"
  shows "block S0 (s (Suc m)) = s (Suc m) # defP m @ block S0 (s m) @ defQ m"
proof-
  have "\<exists>P Q. block S0 (s (Suc m)) = s (Suc m) # P @ block S0 (s m) @ Q"
    using block_nesting[of "s (Suc m)" "s m"] sV[of "Suc m"] sV[of m] stem_chain[of "Suc m" m] inj assms
    by (auto simp: children_def inj_on_eq_iff)
  hence "\<exists>Q. block S0 (s (Suc m)) = s (Suc m) # defP m @ block S0 (s m) @ Q"
    unfolding defP_def
    by (rule someI_ex)
  thus ?thesis
    unfolding defQ_def
    by (rule someI_ex)
qed

lemma contrib_set_unroll:
  "m \<le> k \<Longrightarrow> set (concat (map contrib [0..<Suc m])) = set (block S0 (s m))"
proof(induction m)
  case (Suc m)
  hence mk: "m < k"
    by simp
  have "set (concat (map contrib [0..<Suc (Suc m)])) = set (concat (map contrib [0..<Suc m])) \<union> set (contrib
    (Suc m))"
    by (simp del: upt_Suc add: upt_Suc_append Un_assoc)
  also have "\<dots> = set (block S0 (s (Suc m)))"
    unfolding Suc.IH[OF less_imp_le[OF mk]] block_decomp[OF mk] contrib_def
    by auto
  finally show ?case .
qed (simp add: contrib_def path0)

lemma contrib_len_unroll:
  "m \<le> k \<Longrightarrow> length (concat (map contrib [0..<Suc m])) = length (block S0 (s m))"
  by (induction m; auto simp: contrib_def path0 upt_Suc_append block_decomp simp del: upt_Suc)

lemma newblock_set[simp]: "set newblock = set (block S0 p)"
  using contrib_set_unroll[of k]
  by (simp add: newblock_def pathk)

lemma newblock_len[simp]: "length newblock = length (block S0 p)"
  using contrib_len_unroll[of k]
  by (simp add: newblock_def pathk)

lemma block_p_distinct[simp]: "distinct (block S0 p)"
  by (rule block_distinct_V[OF pV])

lemma newblock_distinct[simp]: "distinct newblock"
  using newblock_set block_p_distinct newblock_len
  by (simp add: distinct_card card_distinct)

lemma set_newlist[simp]: "set newlist = V"
  by (simp add: newlist_splice splice_set )

lemma distinct_newlist[simp]: "distinct newlist"
  by (simp add: newlist_splice splice_distinct  )

lemma hd_newlist[simp]: "hd newlist = r"
  by (simp add: newlist_splice  )

lemma newlist_ne: "newlist \<noteq> []"
  by (simp add: newlist_splice splice_ne )

lemma block_step_mono:
  "m < k \<Longrightarrow> set (block S0 (s m)) \<subseteq> set (block S0 (s (Suc m)))"
  using block_decomp
  by auto

lemma block_mono:
  "\<lbrakk>a \<le> b; b \<le> k\<rbrakk> \<Longrightarrow> set (block S0 (s a)) \<subseteq> set (block S0 (s b))"
  by (induction b) (auto simp: le_Suc_eq Suc_le_eq dest!: block_step_mono)

lemma block_in_p[intro]:
  "a \<le> k \<Longrightarrow> set (block S0 (s a)) \<subseteq> set (block S0 p)"
  using block_mono[of a k] pathk
  by simp

lemma lsuc_in_block_p[intro]:
  "t \<le> k \<Longrightarrow> lsuc S0 (s t) \<in> set (block S0 p)"
  using pivot_prems
    blockP(2,3)[OF sV[of t]] block_in_p[of t] last_in_set[of "block S0 (s t)"]
  by auto

lemma bef_last_pre:
  assumes "m < k"
  shows "bef m = last (s (Suc m) # defP m)"
proof-
  obtain Rv where "follow (thrd S0) (s (Suc m)) = block S0 (s (Suc m)) @ Rv"
    using blockP(1)[OF sV[of "Suc m"]] assms
    by auto
  moreover obtain rest where "block S0 (s m) = s m # rest"
    using blockP(2,5)[OF bef_pred(4)[OF assms]]
    by (cases "block S0 (s m)") auto
  ultimately have "thrd S0 (last (s (Suc m) # defP m)) = Some (s m)"
    using thread_link[OF pst, of "s (Suc m)" "butlast (s (Suc m) # defP m)" "last (s (Suc m) # defP m)" "s m"
                                 "rest @ defQ m @ Rv"] block_decomp[OF assms]
    by (cases "defP m" rule: rev_cases) auto
  thus ?thesis
    using arbD(10)
    by (simp add: bef_def)
qed

lemma bef_in_block_p[intro]:
  "m < k \<Longrightarrow> bef m \<in> set (block S0 p)"
  using bef_last_pre[of m] last_in_set[of "s (Suc m) # defP m"] block_decomp[of m] block_in_p[of "Suc m"]
  by auto

lemma lsx_in_block_p[intro]:
  "t \<le> k \<Longrightarrow> lsx t \<in> set (block S0 p)"
  using pivot_prems
    lsuc_in_block_p[of t] lsuc_in_block_p[of 0] bef_in_block_p[of "t - 1"]
  by (auto simp: lsx_def path0 bef_def)

lemma lsx_k_in_V[intro]:
  "lsx k \<in> V"
  using pivot_prems
    lsx_in_block_p[of k] block_p_subset_V
  by auto

lemma holed_fresh:
  "\<lbrakk>v \<in> set holed; v \<noteq> j; v \<noteq> the (rvth S0 p)\<rbrakk> \<Longrightarrow> final_thrd v =
    thrd S0 v"
  using holed_set lsx_in_block_p bef_in_block_p
  by (fastforce intro: final_thrd_fresh)

lemma j_notin_lsx_img: "j \<notin> lsx ` set [0..<k]"
  using pivot_prems
    lsx_in_block_p j_notin_block_p
  by fastforce

lemma j_notin_bef_img: "j \<notin> bef ` set [0..<k]"
  using bef_in_block_p j_notin_block_p
  by fastforce

lemma thrd_inv_j: "thrd_inv k j = Some i"
  using pivot_prems
    fold_upd_other[of j lsx "[0..<k]" "\<lambda>t. Some (s (Suc t))"] fold_upd_other[of j bef "[0..<k]" out]
        j_notin_lsx_img j_notin_bef_img path0
  by (simp add: thrd_inv_def)

lemma final_thrd_j: "final_thrd j = Some i"
  using pivot_prems
    thrd_inv_j lsx_in_block_p[of k] j_notin_block_p
  by (auto simp: final_thrd_def Let_def split: option.split)

lemma hd_newblock[simp]: "hd newblock = i"
  using blockP(2,5)[OF iV]
  by (simp add: newblock_def upt_conv_Cons contrib_def hd_append del: upt_Suc)

lemma final_thrd_oldrev:
  "the (rvth S0 p) \<noteq> j \<Longrightarrow> final_thrd (the (rvth S0 p)) = aftn k"
  by (simp add: final_thrd_def Let_def split: option.split)

lemma holed_adj_final:
  assumes "Suc t < length holed" "holed ! t \<noteq> j"
  shows "final_thrd (holed ! t) = Some (holed ! Suc t)"
proof(cases "holed ! t = the (rvth S0 p)")
  case True
  moreover have "holed ! (length alpha - 1) = the (rvth S0 p)"
    using alpha_ne old_rev_last_alpha
    by (simp add: holed_def nth_append last_conv_nth)
  ultimately have "Suc t = length alpha"
    using nth_eq_iff_index_eq[OF holed_distinct, of t "length alpha - 1"] assms(1) alpha_ne
    by (simp add: holed_def)
  thus ?thesis
    using final_thrd_oldrev assms(1) assms(2) True beta_out
    by (cases beta) (auto simp: holed_def nth_append)
next
  case False
  thus ?thesis
    using holed_fresh[OF nth_mem assms(2) False] holed_old_adj[OF assms(1) False] assms(1)
    by simp
qed

lemma defQ_last: "\<lbrakk>m < k; defQ m \<noteq> []\<rbrakk> \<Longrightarrow> last (defQ m) = lsuc S0 (s (Suc m))"
  using block_decomp[of m] blockP(3)[OF sV[of "Suc m"]]
  by simp

lemma defQ_empty: "\<lbrakk>m < k; defQ m = []\<rbrakk> \<Longrightarrow> lsuc S0 (s m) = lsuc S0 (s (Suc m))"
  using block_decomp[of m] blockP(2,3)[OF bef_pred(4)] blockP(3)[OF sV[of "Suc m"]]
  by simp

lemma defQ_ne_lsuc: "\<lbrakk>m < k; defQ m \<noteq> []\<rbrakk> \<Longrightarrow> lsuc S0 (s (Suc m)) \<noteq> lsuc S0
  (s m)"
  using block_distinct_V[OF sV[of "Suc m"]] block_decomp[of m] defQ_last[of m]
        blockP(2,3)[OF bef_pred(4)] last_in_set[of "defQ m"] last_in_set[of "block S0 (s m)"]
  by auto

lemma lsx_last_contrib: "t \<le> k \<Longrightarrow> lsx t = last (contrib t)"
  using blockP(3)[OF iV] defQ_last[of "t - 1"] defQ_ne_lsuc[of "t - 1"] defQ_empty[of "t - 1"]
        bef_last_pre[of "t - 1"]
  by (cases "defQ (t - 1) = []"; cases t) (auto simp: lsx_def path0 contrib_def bef_def)

lemma upt_split0: "b \<le> n \<Longrightarrow> [0..<n] = [0..<b] @ [b..<n]"
  using upt_add_eq_append[of 0 b "n - b"]
  by simp

lemma contrib_ne: "contrib t \<noteq> []"
  by (cases t) (auto simp: contrib_def blockP(2)[OF iV])

lemma newblock_seg:
  "t \<le> k \<Longrightarrow> newblock = concat (map contrib [0..<t]) @ contrib t @ concat (map contrib [Suc t..<Suc
    k])"
  using upt_split0[of t "Suc k"] upt_conv_Cons[of t "Suc k"]
  by (simp del: upt_Suc add: newblock_def)

lemma contrib_distinct: "t \<le> k \<Longrightarrow> distinct (contrib t)"
  using newblock_distinct newblock_seg[of t]
  by simp

lemma contrib_seg_disjoint:
  "\<lbrakk>a < b; b \<le> k\<rbrakk> \<Longrightarrow> set (contrib a) \<inter> set (contrib b) = {}"
  using newblock_distinct newblock_seg[of b]
  by fastforce

lemma lsx_inj_le: "\<lbrakk>a \<le> k; b \<le> k; a \<noteq> b\<rbrakk> \<Longrightarrow> lsx a \<noteq> lsx b"
  using lsx_last_contrib[of a] lsx_last_contrib[of b] contrib_seg_disjoint[of a b] contrib_seg_disjoint[of b a]
        last_in_set[OF contrib_ne, of a] last_in_set[OF contrib_ne, of b]
  by (cases a b rule: linorder_cases) auto

lemma thrd_inv_up_aux: "\<lbrakk>t < n; n \<le> k\<rbrakk> \<Longrightarrow> thrd_inv n (lsx t) = Some (s (Suc t))"
proof(induction n)
  case (Suc n)
  have nk: "n < k" "t \<in> {..n}"
    using Suc.prems
    by auto
  have "lsx t \<noteq> bef n"
    by (rule contrapos_nn[OF bef_notin_lsx[OF nk(1)]]) (erule subst, rule imageI[OF nk(2)])
  thus ?case
    using Suc thrd_inv_Suc[OF nk(1)] lsx_inj_le[of t n]
    by (cases "t = n") (auto simp: less_Suc_eq)
qed simp

lemmas thrd_inv_up = thrd_inv_up_aux[OF _ order.refl]

lemma bef_in_contrib_Suc: "m < k \<Longrightarrow> bef m \<in> set (contrib (Suc m))"
  using bef_last_pre[of m] last_in_set[of "s (Suc m) # defP m"]
  by (auto simp: contrib_def)

lemma bef_ne_last_contrib_Suc:
  assumes "m < k" "defQ m \<noteq> []"
  shows "bef m \<noteq> last (contrib (Suc m))"
proof-
  have dj: "set (s (Suc m) # defP m) \<inter> set (defQ m) = {}"
    using contrib_distinct[of "Suc m"] assms(1)
    by (auto simp: contrib_def)
  have "bef m \<in> set (s (Suc m) # defP m)" "last (contrib (Suc m)) \<in> set (defQ m)"
    using bef_last_pre[OF assms(1)] last_in_set[of "s (Suc m) # defP m"] last_in_set[OF assms(2)] assms(2)
    by (simp_all add: contrib_def)
  thus ?thesis
    using equals0D[OF dj, of "bef m"]
    by auto
qed

lemma bef_notin_lsx_all:
  assumes "m < k" "defQ m \<noteq> []"
  shows "bef m \<notin> lsx ` {..k}"
proof
  assume "bef m \<in> lsx ` {..k}"
  then obtain t where "t \<le> k" "bef m = last (contrib t)"
    using lsx_last_contrib
    by auto
  moreover hence "t = Suc m"
    using last_in_set[OF contrib_ne, of t] bef_in_contrib_Suc[OF assms(1)] contrib_seg_disjoint[of t "Suc m"]
          contrib_seg_disjoint[of "Suc m" t] assms(1)
    by (cases t "Suc m" rule: linorder_cases) auto
  ultimately show False
    using bef_ne_last_contrib_Suc[OF assms]
    by simp
qed

lemma thrd_inv_br_aux: "\<lbrakk>m < n; n \<le> k; defQ m \<noteq> []\<rbrakk> \<Longrightarrow> thrd_inv n (bef m) =
  out m"
proof(induction n)
  case (Suc n)
  thus ?case
    using thrd_inv_Suc[of n] bef_notin_lsx_all[of m] bef_inj[of m n]
    by (cases "m = n") (auto simp: less_Suc_eq image_iff)
qed simp

lemma thrd_inv_br: "\<lbrakk>m < k; defQ m \<noteq> []\<rbrakk> \<Longrightarrow> thrd_inv k (bef m) = out m"
  using thrd_inv_br_aux
  by blast

lemma final_thrd_off: "\<lbrakk>x \<noteq> lsx k; x \<noteq> the (rvth S0 p)\<rbrakk> \<Longrightarrow> final_thrd x =
  thrd_inv k x"
  by (simp add: final_thrd_def Let_def split: option.split)

lemma s_in_block_iff:
  assumes "t \<le> k" "n \<le> k"
  shows "s t \<in> set (block S0 (s n)) \<longleftrightarrow> t \<le> n"
proof
  assume "s t \<in> set (block S0 (s n))"
  moreover have "s t \<notin> set (block S0 (s n))" if "n < t"
    using anc_notin_thread_suffix[OF sV[of t], of "s n"] stem_chain[of t n] blockP(1)[OF sV[of n]]
          inj that assms(1) assms(2)
    by (auto simp: children_def inj_on_eq_iff)
  ultimately show "t \<le> n"
    by force
next
  assume "t \<le> n"
  thus "s t \<in> set (block S0 (s n))"
    using stem_chain[of n t] blockP(4)[OF sV[of n]] assms(1) assms(2)
    by (simp add: children_def)
qed

lemma defQ_no_stem: "\<lbrakk>m < k; t \<le> k\<rbrakk> \<Longrightarrow> s t \<notin> set (defQ m)"
  using block_distinct_V[OF sV[of "Suc m"]] block_decomp[of m] s_in_block_iff[of t "Suc m"] s_in_block_iff[of t m]
  by (auto simp: le_Suc_eq)

lemma contrib_subset_nb[intro]: "t \<le> k \<Longrightarrow> set (contrib t) \<subseteq> set newblock"
  using newblock_seg[of t]
  by auto

lemma out_eq_hd_defQ:
  assumes "m < k" "defQ m \<noteq> []"
  shows "out m = Some (hd (defQ m))"
proof-
  obtain C where "follow (thrd S0) (s (Suc m)) = block S0 (s (Suc m)) @ C"
    using blockP(1)[OF sV[of "Suc m"]] assms
    by auto
  thus ?thesis
    using thread_link[OF pst, of "s (Suc m)" "s (Suc m) # defP m @ butlast (block S0 (s m))" "lsuc S0 (s m)"
                                 "hd (defQ m)" "tl (defQ m) @ C"]
          block_decomp[OF assms(1)] blockP(2,3)[OF bef_pred(4)[OF assms(1)]] assms(2)
    by (cases "defQ m"; cases "block S0 (s m)" rule: rev_cases) (auto simp: out_def)
qed

lemma final_thrd_lsx:
  assumes "t < k"
  shows "final_thrd (lsx t) = Some (s (Suc t))"
  by (insert assms lsx_inj_le[of t k] lsx_in_block_p[of t] old_rev_notin_block_p thrd_inv_up[OF assms]; rule trans[OF
    final_thrd_off]; auto)

lemma contrib_seam:
  "t < k \<Longrightarrow> final_thrd (last (contrib t)) = Some (hd (contrib (Suc t)))"
  using lsx_last_contrib[of t] final_thrd_lsx[of t]
  by (simp add: contrib_def)

lemma contrib_fresh:
  "\<lbrakk>x \<in> set (contrib t); t \<le> k; x \<notin> lsx ` {..k}; x \<notin> bef ` set [0..<k]\<rbrakk>
    \<Longrightarrow> final_thrd x = thrd S0 x"
  using final_thrd_fresh contrib_subset_nb newblock_set j_notin_block_p old_rev_notin_block_p
  by blast

lemma contrib_disj_sym: "\<lbrakk>a \<le> k; b \<le> k; a \<noteq> b\<rbrakk> \<Longrightarrow> set (contrib a)
  \<inter> set (contrib b) = {}"
  using contrib_seg_disjoint[of a b] contrib_seg_disjoint[of b a]
  by (cases a b rule: linorder_cases) auto

lemma interior_notin_lsx:
  "\<lbrakk>x \<in> set (contrib t); t \<le> k; x \<noteq> last (contrib t)\<rbrakk> \<Longrightarrow> x \<notin>
    lsx ` {..k}"
  using lsx_last_contrib contrib_disj_sym[of t] last_in_set[OF contrib_ne]
  by fastforce

lemma interior_notin_bef:
  assumes "x \<in> set (contrib t)" "t \<le> k" "\<And>m. m < k \<Longrightarrow> t = Suc m \<Longrightarrow> x
    \<noteq> bef m"
  shows "x \<notin> bef ` set [0..<k]"
proof
  assume "x \<in> bef ` set [0..<k]"
  then obtain m where "m < k" "x = bef m"
    by auto
  thus False
    using assms contrib_disj_sym[of t "Suc m"] bef_in_contrib_Suc[of m]
    by (cases "t = Suc m") auto
qed

lemma final_thrd_bef: "\<lbrakk>m < k; defQ m \<noteq> []\<rbrakk> \<Longrightarrow> final_thrd (bef m) = Some (hd
  (defQ m))"
  using final_thrd_off[of "bef m"] bef_notin_lsx_all[of m] bef_in_block_p[of m] old_rev_notin_block_p
        thrd_inv_br[of m] out_eq_hd_defQ[of m]
  by force

lemma bef_eq_contrib_junction: "m < k \<Longrightarrow> bef m = contrib (Suc m) ! length (defP m)"
  using bef_last_pre[of m]
  by (cases "defP m" rule: rev_cases) (auto simp: contrib_def)

lemma contrib_old_link:
  assumes "t \<le> k" "Suc q < length (contrib t)" "\<And>m. t = Suc m \<Longrightarrow> q \<noteq> length (defP m)"
  shows "thrd S0 (contrib t ! q) = Some (contrib t ! Suc q)"
proof(cases t)
  case 0
  thus ?thesis
    using block_link[OF iV] assms(2)
    by (simp add: contrib_def)
next
  case (Suc m)
  define P where "P = s (Suc m) # defP m"
  have sm: "s (Suc m) \<in> V" and c: "contrib t = P @ defQ m"
    and b: "block S0 (s (Suc m)) = P @ block S0 (s m) @ defQ m"
    using assms(1) sV[of "Suc m"] block_decomp[of m] Suc
    by (simp_all add: contrib_def P_def)
  show ?thesis
  proof(cases "Suc q < length P")
    case True
    thus ?thesis
      using block_link[OF sm, of q] assms(2)
      unfolding c b
      by (simp add: nth_append)
  next
    case False
    hence "length P \<le> q"
      using assms(3)[OF Suc]
      by (auto simp: P_def)
    then obtain d where "q = length P + d"
      by (auto simp: le_iff_add)
    thus ?thesis
      using block_link[OF sm, of "length P + length (block S0 (s m)) + d"] assms(2)
      unfolding c b
      by (simp add: nth_append)
  qed
qed

lemma contrib_internal_link:
  assumes "t \<le> k" "Suc q < length (contrib t)"
  shows "final_thrd (contrib t ! q) = Some (contrib t ! Suc q)"
proof(cases "\<exists>m. t = Suc m \<and> q = length (defP m)")
  case True
  then obtain m where m: "t = Suc m" "q = length (defP m)"
    by blast
  hence "m < k" "defQ m \<noteq> []" "contrib t ! Suc q = hd (defQ m)"
    using assms
    by (auto simp: contrib_def nth_append hd_conv_nth)
  thus ?thesis
    using final_thrd_bef bef_eq_contrib_junction m
    by simp
next
  case False
  have d: "distinct (contrib t)" "q < length (contrib t)" "length (contrib t) - 1 < length (contrib t)"
    using contrib_distinct[OF assms(1)] assms(2)
    by auto
  have "contrib t ! q \<notin> lsx ` {..k}"
    using interior_notin_lsx[OF nth_mem[OF d(2)] assms(1)] nth_eq_iff_index_eq[OF d] assms(2) contrib_ne[of t]
    by (simp add: last_conv_nth)
  moreover have "contrib t ! q \<notin> bef ` set [0..<k]"
  proof(rule interior_notin_bef[OF nth_mem[OF d(2)] assms(1)])
    fix m
    assume m: "m < k" "t = Suc m"
    hence "length (defP m) < length (contrib t)"
      by (simp add: contrib_def)
    thus "contrib t ! q \<noteq> bef m"
      using bef_eq_contrib_junction[OF m(1)] nth_eq_iff_index_eq[OF d(1,2)] False m(2)
      by auto
  qed
  moreover have "\<And>m. t = Suc m \<Longrightarrow> q \<noteq> length (defP m)"
    using False
    by blast
  ultimately show ?thesis
    using contrib_fresh[OF nth_mem[OF d(2)] assms(1)] contrib_old_link[OF assms]
    by simp
qed

lemma newblock_link:
  assumes "Suc t < length newblock"
  shows "final_thrd (newblock ! t) = Some (newblock ! Suc t)"
  by (unfold newblock_def; rule concat_linked; use assms contrib_internal_link contrib_ne contrib_seam in \<open>auto
    simp: newblock_def simp del: upt_Suc\<close>)

lemma contrib_in_block: "t \<le> k \<Longrightarrow> set (contrib t) \<subseteq> set (block S0 (s t))"
  using contrib_set_unroll[of t]
  by auto

lemma contrib_notin_prev:
  assumes "Suc m \<le> k" "u \<in> set (contrib (Suc m))"
  shows "u \<notin> set (block S0 (s m))"
proof
  assume "u \<in> set (block S0 (s m))"
  then obtain a where "a \<le> m" "u \<in> set (contrib a)"
    using contrib_set_unroll[of m, symmetric] assms(1)
    by (auto simp del: upt_Suc simp: less_Suc_eq_le)
  thus False
    using contrib_seg_disjoint[of a "Suc m"] assms
    by auto
qed

lemma block_layer:
  "\<lbrakk>t \<le> k; u \<in> set (block S0 (s t)); \<And>m. t = Suc m \<Longrightarrow> u \<notin> set (block S0
    (s m))\<rbrakk> \<Longrightarrow> u \<in> set (contrib t)"
  using block_decomp[of "t - 1"]
  by (cases t) (auto simp: contrib_def path0)

lemma contrib_hd: "t \<le> k \<Longrightarrow> contrib t ! 0 = s t"
  using blockP(2,5)[OF iV] path0
  by (cases t) (auto simp: contrib_def hd_conv_nth)

lemma contrib_stem:
  assumes "t \<le> k" "t' \<le> k" "s t' \<in> set (contrib t)"
  shows "t' = t"
proof(cases "k = 0")
  case False
  hence "t' \<le> t"
    using contrib_in_block[OF assms(1)] s_in_block_iff[OF assms(2) assms(1)] assms(3)
    by auto
  moreover have "\<not> t' < t"
  proof
    assume "t' < t"
    then obtain m where "t = Suc m" "t' \<le> m"
      by (cases t) auto
    thus False
      using contrib_notin_prev[of m "s t'"] s_in_block_iff[of t' m] assms False
      by auto
  qed
  ultimately show ?thesis
    by simp
qed (use assms in simp)

lemma contrib_sub_children_stem:
  "t \<le> k \<Longrightarrow> set (contrib t) \<subseteq> children newprnt (s t)"
  using contrib_in_block[of t] block_in_p[of t] children_newprnt_i path0 contrib_notin_prev
    children_newprnt_stem[of t]
  by (cases t) auto

lemma defQ_hd_parent:
  assumes "m < k" "defQ m \<noteq> []"
  shows "prnt S0 (hd (defQ m)) = Some (s (Suc m))"
proof-
  have sm: "s m \<in> V" "s (Suc m) \<in> V"
    using sV assms(1)
    by auto
  have hq: "hd (defQ m) \<in> set (block S0 (s (Suc m)))" "hd (defQ m) \<notin> set (block S0 (s m))"
    "hd (defQ m) \<noteq> s (Suc m)"
    using block_decomp[OF assms(1)] block_distinct_V[OF sm(2)] hd_in_set[OF assms(2)]
    by auto
  have l: "lsuc S0 (s m) \<in> set (block S0 (s m))" "lsuc S0 (s m) \<in> V"
    using blockP(2,3)[OF sm(1)] last_in_set[of "block S0 (s m)"] lsuc_in_block_p[of m]
          block_p_subset_V assms(1)
    by auto
  obtain g where g: "prnt S0 (hd (defQ m)) = Some g" "g \<in> set (follow (prnt S0) (lsuc S0 (s m)))"
    using dfs_step[OF l(2)] out_eq_hd_defQ[OF assms]
    by (auto simp: out_def)
  have "s m \<notin> set (follow (prnt S0) g)"
    using hq(2) blockP(4)[OF sm(1)] ppt_follow_Some[OF g(1)]
    by (auto simp: children_def)
  moreover have "s m \<in> set (follow (prnt S0) (lsuc S0 (s m)))"
    using l(1) blockP(4)[OF sm(1)]
    by (simp add: children_def)
  ultimately have "g \<in> set (follow (prnt S0) (s (Suc m)))"
    using ppt_follow_linear[OF g(2), of "s m"] ppt_follow_Some[OF pathS[OF assms(1)]] ppt_follow_mem[of g]
    by auto
  moreover have "s (Suc m) \<in> set (follow (prnt S0) g)"
    using hq(1,3) blockP(4)[OF sm(2)] ppt_follow_Some[OF g(1)]
    by (auto simp: children_def)
  ultimately show ?thesis
    using g(1) ppt_ancestor_antisym[of g "s (Suc m)"]
    by simp
qed

lemma newblock_seam_dfs:
  "m < k \<Longrightarrow> \<exists>a. newprnt (hd (contrib (Suc m))) = Some a \<and> a \<in> set (follow newprnt
    (last (contrib m)))"
  using contrib_sub_children_stem[of m] last_in_set[OF contrib_ne, of m] newprnt_stem[of "Suc m"]
  by (auto simp: contrib_def children_def simp del: fun_upd_apply)

lemma newblock_hole_dfs:
  assumes "m < k" "defQ m \<noteq> []"
  shows "\<exists>a. newprnt (hd (defQ m)) = Some a \<and> a \<in> set (follow newprnt (bef m))"
proof-
  have "hd (defQ m) \<notin> s ` {..k}"
    using defQ_no_stem[OF assms(1)] hd_in_set[OF assms(2)]
    by auto
  moreover have "bef m \<in> children newprnt (s (Suc m))"
    using contrib_sub_children_stem[of "Suc m"] bef_in_contrib_Suc[OF assms(1)] assms(1)
    by auto
  ultimately show ?thesis
    using newprnt_off_stem[of "hd (defQ m)"] defQ_hd_parent[OF assms(1) assms(2)]
    by (auto simp: children_def)
qed

lemma newblock_internal_oldedge_dfs:
  assumes "t \<le> k" "x \<in> set (contrib t)" "y \<in> set (contrib t)" "y \<noteq> s t" "thrd S0 x = Some y"
  shows "\<exists>a. newprnt y = Some a \<and> a \<in> set (follow newprnt x)"
proof-
  have stV: "s t \<in> V" and xp: "x \<in> set (block S0 p)"
    using sV contrib_in_block[OF assms(1)] block_in_p[OF assms(1)]  assms(1) assms(2)
    by auto
  then obtain g where g: "prnt S0 y = Some g" "g \<in> set (follow (prnt S0) x)"
    using dfs_step[OF _ assms(5)] block_p_subset_V
    by blast
  have gst: "s t \<in> set (follow (prnt S0) g)"
    using contrib_in_block[OF assms(1)] assms(3) assms(4) blockP(4)[OF stV] ppt_follow_Some[OF g(1)]
    by (auto simp: children_def)
  have "g \<in> set (contrib t)"
  proof(rule block_layer[OF assms(1)])
    show "g \<in> set (block S0 (s t))"
      using gst blockP(4)[OF stV]
      by (simp add: children_def)
    fix m
    assume "t = Suc m"
    thus "g \<notin> set (block S0 (s m))"
      using contrib_notin_prev[of m y]  assms(1) assms(3) ppt_follow_Some[OF g(1)] blockP(4)[OF sV[of m]]
      by (auto simp: children_def)
  qed
  hence "g = s t \<or> (g \<notin> s ` {..k} \<and> g \<in> set (block S0 p))"
    using contrib_stem[OF assms(1)] contrib_in_block[OF assms(1)] block_in_p[OF assms(1)]
    by auto
  hence "g \<in> set (follow newprnt x)"
    using contrib_sub_children_stem[OF assms(1)] assms(2) newpath_nonstem_char[of g x] xp g(2)
    by (auto simp: children_def)
  moreover have "y \<notin> s ` {..k}"
    using contrib_stem[OF assms(1)] assms(3) assms(4)
    by auto
  ultimately show ?thesis
    using g(1) newprnt_off_stem
    by simp
qed

lemma contrib_internal_dfs:
  assumes "t \<le> k" "Suc q < length (contrib t)"
  shows "\<exists>a. newprnt (contrib t ! Suc q) = Some a \<and> a \<in> set (follow newprnt (contrib t ! q))"
proof(cases "\<exists>m. t = Suc m \<and> q = length (defP m)")
  case True
  then obtain m where m: "t = Suc m" "q = length (defP m)"
    by blast
  hence "m < k" "defQ m \<noteq> []" "contrib t ! Suc q = hd (defQ m)"
    using assms(1) assms(2)
    by (auto simp: contrib_def nth_append hd_conv_nth)
  thus ?thesis
    using newblock_hole_dfs bef_eq_contrib_junction m
    by simp
next
  case False
  hence h: "\<And>m. t = Suc m \<Longrightarrow> q \<noteq> length (defP m)"
    by blast
  have "contrib t ! Suc q \<noteq> s t"
    using nth_eq_iff_index_eq[OF contrib_distinct[OF assms(1)], of "Suc q" 0] contrib_hd[OF assms(1)]
          contrib_ne[of t] assms(2)
    by auto
  from newblock_internal_oldedge_dfs[OF assms(1) nth_mem nth_mem this contrib_old_link[OF assms(1) assms(2) h]]
  show ?thesis
    using assms(2)
    by simp
qed

lemma newblock_dfs:
  assumes "Suc t < length newblock"
  shows "\<exists>a. newprnt (newblock ! Suc t) = Some a \<and> a \<in> set (follow newprnt (newblock ! t))"
proof-
  have "\<exists>a. newprnt (concat (map contrib [0..<Suc k]) ! Suc t) = Some a
          \<and> a \<in> set (follow newprnt (concat (map contrib [0..<Suc k]) ! t))"
  proof(rule concat_linked[where R = "\<lambda>x y. \<exists>a. newprnt y = Some a \<and> a \<in> set (follow newprnt
    x)"])
    fix ys q
    assume "ys \<in> set (map contrib [0..<Suc k])" "Suc q < length ys"
    thus "\<exists>a. newprnt (ys ! Suc q) = Some a \<and> a \<in> set (follow newprnt (ys ! q))"
      using contrib_internal_dfs
      by (auto simp del: fun_upd_apply)
  qed (use  jneq assms(1) contrib_ne newblock_seam_dfs in
       \<open>auto simp: newblock_def simp del: upt_Suc fun_upd_apply\<close>)
  thus ?thesis
    by (simp add: newblock_def)
qed

lemma newtree_r_None[simp]: "newprnt r = None"
  using newprnt_off_stem[OF r_notin_stem] rooted_arborescense_invar_dom[OF rinv0]
  by auto

lemma final_thrd_lsx_k:
  "final_thrd (lsx k) = (if the (rvth S0 p) = j then thrd S0 (lsuc S0 p) else thrd S0 j)"
  using pivot_prems
    lsx_in_block_p[of k] old_rev_notin_block_p
  by (auto simp: final_thrd_def Let_def split: option.split)

lemma tail_seam:
  assumes "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) \<noteq> []"
  shows "final_thrd (lsx k) = Some (hd (tl (dropWhile (\<lambda>x. x \<noteq> j) holed)))"
proof(cases "the (rvth S0 p) = j")
  case True
  have "dropWhile (\<lambda>x. x \<noteq> j) holed = j # beta"
    using holed_distinct old_rev_last_alpha alpha_ne True
    by (cases alpha rule: rev_cases) (auto simp: holed_def dropWhile_append3)
  thus ?thesis
    using final_thrd_lsx_k True beta_out assms(1)
    by (auto simp: aftn_def out_def pathk)
next
  case False
  define A where "A = takeWhile (\<lambda>x. x \<noteq> j) holed"
  define B where "B = tl (dropWhile (\<lambda>x. x \<noteq> j) holed)"
  have "holed = A @ j # B" "B \<noteq> []"
    unfolding A_def B_def
    by (rule holed_split, rule assms(1))
  hence "holed ! length A = j" "holed ! Suc (length A) = hd B" "Suc (length A) < length holed"
    by (auto simp: nth_append hd_conv_nth)
  thus ?thesis
    using holed_old_adj[of "length A"] final_thrd_lsx_k False
    by (simp add: B_def[symmetric])
qed

lemma newblock_split_last: "newblock = concat (map contrib [0..<k]) @ contrib k"
  by (simp add: newblock_def)

lemma newblock_ne: "newblock \<noteq> []"
  using newblock_split_last contrib_ne
  by simp

lemma last_newblock[simp]: "last newblock = lsx k"
  using newblock_split_last contrib_ne lsx_last_contrib[of k]
  by simp

lemma newlist_link:
  "Suc t < length newlist \<Longrightarrow> final_thrd (newlist ! t) = Some (newlist ! Suc t)"
  unfolding newlist_splice
  by (rule splice_adjacent[where R = "\<lambda>x y. final_thrd x = Some y"])
     (use newblock_ne newblock_link holed_adj_final final_thrd_j
          hd_newblock last_newblock tail_seam in auto)

lemma last_newlist_nil: "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = [] \<Longrightarrow> last newlist = lsx k"
  using newblock_ne last_newblock
  by (simp add: newlist_def)

lemma newlist_last_None: "final_thrd (last newlist) = None"
  unfolding newlist_splice
  by (rule splice_terminal)
     (use newblock_ne last_newblock final_thrd_lsx_k final_thrd_oldrev
       aftn_eq_thrd_lsuc_p holed_fresh in auto)

lemma final_thrd_dom_V:
  assumes "x \<notin> V"
  shows "final_thrd x = None"
proof-
  have x: "x \<notin> set (block S0 p)" "x \<noteq> j" "x \<noteq> the (rvth S0 p)" "x \<notin> dom (thrd S0)"
    using  assms(1) block_p_subset_V jV old_rev_in_V arbD(8)
    by auto
  hence "x \<notin> lsx ` {..k}" "x \<notin> bef ` set [0..<k]"
    using lsx_in_block_p[OF _] bef_in_block_p
    by auto
  thus ?thesis
    using final_thrd_fresh[of x] x
    by (simp add: domIff)
qed

lemma final_thrd_reverse_chain:
  "final_thrd x = Some y \<Longrightarrow>
   \<exists>i. Suc i < length newlist \<and> newlist ! i = x \<and> newlist ! Suc i = y"
  using chain_edge_iff[of newlist "final_thrd"] newlist_ne set_newlist newlist_link newlist_last_None final_thrd_dom_V
  by auto

lemma newlist_chain:
  "parent_spec (final_thrd)" "follow (final_thrd) (hd newlist) = newlist"
  "dom (final_thrd) = V - {last newlist}" "ran (final_thrd) = V - {hd newlist}"
  by (rule chain_properties;
      use distinct_newlist newlist_ne set_newlist newlist_link newlist_last_None final_thrd_dom_V in auto)+

lemmas parent_spec_final_thrd = newlist_chain(1)

lemma clauseB: "parent_spec (thrd (update_tree S0 i j p jn))"
  using pivot_prems
    update_tree_thrd parent_spec_final_thrd
  by simp

lemma out_edge: "follow (final_thrd) r = newlist"
  using newlist_chain(2) hd_newlist
  by simp

lemma stem_in_block[intro]: "t \<le> k \<Longrightarrow> s t \<in> set (block S0 p)"
  using pivot_prems
    s_in_block_iff[of t k] pathk
  by simp

lemma off_block_off_stem: "u \<notin> set (block S0 p) \<Longrightarrow> u \<notin> s ` {..k}"
  using pivot_prems
    stem_in_block
  by blast

lemma holed_dfs:
  "Suc t < length holed \<Longrightarrow> \<exists>a. newprnt (holed ! Suc t) = Some a \<and> a \<in> set (follow
    newprnt (holed ! t))"
  using pivot_prems
    holed_dfs_old[of t] newprnt_off_stem[OF off_block_off_stem[OF holed_nb]] follow_newprnt_off_block[OF holed_nb]
  by simp

lemma j_in_follow_newtree_lsxk:
   "j \<in> set (follow newprnt (lsx k))"
proof-
  have "i \<in> set (follow newprnt (lsx k))"
    using block_p_under_i lsx_in_block_p[OF _, of k]
    by simp
  from follow_sub_of_mem[OF newprnt_ps this] show ?thesis
    using follow_Some_ps[OF newprnt_ps newprnt_i] follow_mem_ps[OF newprnt_ps, of j]
    by (auto simp del: fun_upd_apply)
qed

lemma newlist_dfs:
  "Suc t < length newlist \<Longrightarrow>
   \<exists>a. newprnt (newlist ! Suc t) = Some a \<and> a \<in> set (follow newprnt (newlist ! t))"
  unfolding newlist_splice
  by (rule splice_preorder[where P = newprnt])
     (use newprnt_ps newblock_ne newprnt_i hd_newblock last_newblock
          j_in_follow_newtree_lsxk newblock_dfs holed_dfs in \<open>auto simp del: fun_upd_apply\<close>)

lemma clauseJ_contig:
  assumes "v \<in> V"
  shows "\<exists>pre suf. follow (thrd (update_tree S0 i j p jn)) v = pre @ suf
           \<and> set pre = children (prnt (update_tree S0 i j p jn)) v \<and> pre \<noteq> [] \<and> hd pre = v"
proof-
  have "newprnt (newlist ! 0) = None"
    by (simp only: hd_conv_nth[OF newlist_ne, symmetric] hd_newlist newtree_r_None)
  from preorder_contiguous[OF newprnt_ps parent_spec_final_thrd out_edge this
                           newlist_dfs]
  show ?thesis
    using set_newlist children_subset_V[OF clauseA assms(1)] assms(1) update_tree_thrd
          update_tree_prnt
    by (simp del: fun_upd_apply)
qed

lemma clauseD: "set (follow (thrd (update_tree S0 i j p jn)) r) = V"
  using pivot_prems
    update_tree_thrd out_edge set_newlist
  by simp

lemma dom_thrd_update_tree:
   "dom (thrd (update_tree S0 i j p jn)) = V - {last newlist}"
  using newlist_chain(3)
        update_tree_thrd
  by simp

lemma lsuc_update_tree_eval:
  assumes "v \<in> V"
  shows "lsuc (update_tree S0 i j p jn) v =
    (if v \<in> set (follow (prnt S0) (the (prnt S0 p))) \<and> lsuc S0 v = lsuc S0 p
     then (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then the (rvth S0 p) else lsx k)
     else if lsuc S0 v = j \<or> v \<in> s ` {..k} then lsx k else lsuc S0 v)"
proof-
  define L where "L = follow (prnt S0) (the (prnt S0 p))"
  note jf = join_facts[OF jneq]
  have lin: "lsuc_in y = (if lsuc S0 y = j \<or> y \<in> s ` {..k} then lsx k else lsuc S0 y)" if "y \<in> V" for y
    using lsuc_in_eq[of y] lsuc_stem_eq[of y] in_chain_iff[OF that]
    by simp
  have Lin: "lsuc_in y = (if lsuc S0 y = j then lsx k else lsuc S0 y)" if "y \<in> set L" for y
    using lin[of y] that stem_notin_follow_vout follow_subset_V[OF rinv0 pV]
          ppt_follow_Some prnt_sm_ne_None[of k] pathk
    by (force simp: L_def)
  have jns: "lsuc_stem jn = lsuc S0 jn"
    using lsuc_stem_eq jn_notin_stem
    by simp
  have "p \<in> set (follow (prnt S0) i)"
    using pblock(4) i_in_block
    by (simp add: children_def)
  note out = out_chain_set[OF jneq this jf, of "lsx k", folded L_def]
  define P where "P = (\<lambda>y. Some y \<noteq> (if lsuc_stem jn = j then Some jn else None) \<and> lsuc_in y = lsuc
    S0 p)"
  have "takeWhile P L = takeWhile (\<lambda>y. Some y \<noteq> (if lsuc S0 jn = j then Some jn else None)
                                       \<and> (if lsuc S0 y = j then lsx k else lsuc S0 y) = lsuc S0 p) L"
    by (rule takeWhile_cong[OF refl]) (simp add: P_def Lin jns)
  hence OUT: "v \<in> set (takeWhile P L) \<longleftrightarrow> v \<in> set L \<and> lsuc S0 v = lsuc S0 p"
    using out
    by simp
  note fin = update_tree_lsuc follow_newprnt_vout[folded L_def]
  show ?thesis
    using final_lsuc_on[of v, unfolded fin(2), folded P_def] final_lsuc_off[of v, unfolded fin(2), folded P_def]
          OUT fin(1) lin[OF assms(1)]
    by (cases "v \<in> set L \<and> lsuc S0 v = lsuc S0 p") (simp_all add: L_def)
qed

lemma stem_anc_p_std:
  "t \<le> k \<Longrightarrow> s t \<in> set (follow newprnt p)"
  using chainStem_set i_in_follow_newprnt path0
  by (cases t) (auto dest: set_takeWhileD)

lemma stem_desc_lsxk:
  "t \<le> k \<Longrightarrow> lsx k \<in> children newprnt (s t)"
  using contrib_sub_children_stem[OF le_refl] last_in_set[OF contrib_ne[of k]] pathk
    stem_anc_p_std[of t] follow_sub_of_mem[OF newprnt_ps]
  by (fastforce simp: children_def lsx_last_contrib)

lemma children_stem_sub_blockp:
  "t \<le> k \<Longrightarrow> children newprnt (s t) \<subseteq> set (block S0 p)"
  using children_newprnt_i children_newprnt_stem[of t] path0
  by (cases t) auto

lemma final_thrd_lsxk_exits:
   "final_thrd (lsx k) = None \<or> the (final_thrd (lsx k)) \<notin> set (block S0 p)"
proof(cases "tl (dropWhile (\<lambda>x. x \<noteq> j) holed) = []")
  case True
  thus ?thesis
    using follow_last_None[OF parent_spec_final_thrd, of r] out_edge last_newlist_nil
    by simp
next
  case False
  have "hd (tl (dropWhile (\<lambda>x. x \<noteq> j) holed)) \<in> set holed"
    using hd_in_set[OF False] set_holed_split
    by blast
  thus ?thesis
    using tail_seam[OF False] holed_set
    by simp
qed

lemma in_desc_lsxk:
  "v \<in> set (follow (prnt S0) j) \<Longrightarrow> lsx k \<in> children newprnt v"
  using children_newprnt_jpath[of v] lsx_in_block_p[OF le_refl]
  by simp

lemma final_thrd_lsxk_notin_INdesc:
  assumes "v \<in> V" "lsuc S0 v = j"
  shows "final_thrd (lsx k) = None \<or> the (final_thrd (lsx k)) \<notin> children (prnt S0) v"
  using assms final_thrd_lsx_k succ_lsuc_exits_block[of v]
    successive_block_exit[of v p] thrd_old_rev pV
  by (cases "the (rvth S0 p) = j"; cases "thrd S0 j"; cases "thrd S0 (lsuc S0 p)") auto

lemma children_newprnt_supseteq:
   "children (prnt S0) v - set (block S0 p) \<subseteq> children newprnt v"
  using follow_newprnt_off_block
  by (auto simp: children_def)

lemma untouched_i_desc:
  "\<lbrakk>v \<in> V; lsuc S0 v \<notin> set (block S0 p)\<rbrakk> \<Longrightarrow> lsuc S0 v \<in> children
    newprnt v"
  using children_newprnt_supseteq blockP(2,3,4)[of v] last_in_set[of "block S0 v"]
  by auto

lemma untouched_ii_exit:
  assumes "v \<in> V" "lsuc S0 v \<notin> set (block S0 p)" "lsuc S0 v \<notin> lsx ` {..k}" "lsuc S0 v \<notin> bef `
    set [0..<k]" "lsuc S0 v \<noteq> j" "lsuc S0 v \<noteq> the (rvth S0 p)"
  shows "final_thrd (lsuc S0 v) = None \<or> the (final_thrd (lsuc S0 v)) \<notin> children newprnt v"
proof(cases "thrd S0 (lsuc S0 v)")
  case (Some w)
  have "w \<noteq> p"
    using Some assms(6) thrd_old_rev arbD(10)
    by auto
  hence "w \<notin> set (block S0 p)"
    using pred_in_block[OF pV Some] assms(2) assms(3) assms(4) assms(5)
    by blast
  thus ?thesis
    using final_thrd_fresh[OF assms(3) assms(4) assms(5) assms(6)] succ_lsuc_exits_block[OF assms(1) Some]
      children_newprnt_decomp Some
    by auto
qed (use final_thrd_fresh[OF assms(3) assms(4) assms(5) assms(6)] in simp)

lemma blockv_offstem_no_stem:
  assumes "v \<notin> s ` {..k}" and "v \<in> V" and "v \<in> set (block S0 p)" and "t \<le> k"
  shows "s t \<notin> set (block S0 v)"
  using assms blockP(4)[of v] follow_stem_prefix[of t]
    ppt_follow_Some[of p] prnt_sm_ne_None[of k] pathk pblock(4)
    ppt_ancestor_antisym[of v p]
  by (auto simp: children_def)

lemma bef_collision:
  "\<lbrakk>t < k; defQ t = []\<rbrakk> \<Longrightarrow> bef t = lsx (Suc t)"
  by (simp add: defQ_empty lsx_def bef_def)

lemma lsuc_last:
  assumes "v \<in> V" "follow (thrd (update_tree S0 i j p jn)) v = pre @ suf" "set pre = children (prnt (update_tree S0 i j p jn)) v"
  shows "lsuc (update_tree S0 i j p jn) v = last pre"
proof-
  define C where "C = children newprnt v"
  define ex where "ex = (\<lambda>x. x \<in> C \<and> (final_thrd x = None \<or> the (final_thrd x) \<notin> C))"
  note ev = lsuc_update_tree_eval[OF assms(1)]
  have exl: "x = last pre" if "ex x" for x
    using succ_exits_is_last[OF clauseB assms(2), of x] that assms(3)
    by (simp add: ex_def C_def update_tree_fields)
  have Csub: "C \<subseteq> children (prnt S0) v \<union> set (block S0 p)"
    using children_newprnt_decomp
    by (auto simp: C_def)
  have succ_p: "w \<notin> C" if "thrd S0 (lsuc S0 p) = Some w" "lsuc S0 v = lsuc S0 p" for w
    using succ_lsuc_exits_block[OF assms(1)] succ_lsuc_exits_block[OF pV that(1)] pblock(4) Csub that
    by auto
  text \<open>IN-chain, and OUT-chain when @{term j} was the old thread predecessor of @{term p}.\<close>
  have lsxk: "ex (lsx k)" if vj: "v \<in> set (follow (prnt S0) j)"
    and lv: "lsuc S0 v = j \<or> (the (rvth S0 p) = j \<and> lsuc S0 v = lsuc S0 p)"
  proof-
    have C: "C = children (prnt S0) v \<union> set (block S0 p)"
      using children_newprnt_jpath[OF vj]
      by (simp add: C_def)
    have "final_thrd (lsx k) = None \<or> the (final_thrd (lsx k)) \<notin> C"
    proof(cases "lsuc S0 v = j")
      case True
      thus ?thesis
        using final_thrd_lsxk_notin_INdesc[OF assms(1) True] final_thrd_lsxk_exits C
        by auto
    next
      case False
      thus ?thesis
        using lv final_thrd_lsx_k succ_p
        by (cases "thrd S0 (lsuc S0 p)") auto
    qed
    thus ?thesis
      using in_desc_lsxk[OF vj]
      by (simp add: ex_def C_def)
  qed
  text \<open>OUT-chain otherwise.\<close>
  have out_rv: "ex (the (rvth S0 p))"
    if vp: "v \<in> set (follow (prnt S0) p)" "p \<noteq> v" "lsuc S0 v = lsuc S0 p" and jrv: "the (rvth S0 p) \<noteq> j"
  proof-
    have "the (rvth S0 p) \<in> C"
      using old_rev_in_block_anc[OF assms(1) vp(1,2)] blockP(4)[OF assms(1)] old_rev_notin_block_p
            children_newprnt_supseteq[of v]
      by (auto simp: C_def)
    thus ?thesis
      using final_thrd_oldrev[OF jrv] aftn_eq_thrd_lsuc_p succ_p[OF _ vp(3)]
      by (cases "thrd S0 (lsuc S0 p)") (auto simp: ex_def)
  qed
  text \<open>Stem.\<close>
  have stem: "ex (lsx k)" if vs: "v \<in> s ` {..k}"
    using vs stem_desc_lsxk children_stem_sub_blockp final_thrd_lsxk_exits
    by (auto simp: ex_def C_def)
  text \<open>Nodes whose old last descendant lies outside @{term "block S0 p"}.\<close>
  have unt: "ex (lsuc S0 v)" if lnb: "lsuc S0 v \<notin> set (block S0 p)" and lnj: "lsuc S0 v \<noteq> j"
  proof(cases "lsuc S0 v = the (rvth S0 p)")
    case False
    moreover have "lsuc S0 v \<notin> lsx ` {..k}" "lsuc S0 v \<notin> bef ` set [0..<k]"
      using lsx_in_block_p[OF _] bef_in_block_p lnb
      by auto
    ultimately show ?thesis
      using untouched_i_desc[OF assms(1) lnb] untouched_ii_exit[OF assms(1) lnb _ _ lnj]
      by (simp add: ex_def C_def)
  next
    case True
    have "w \<notin> C" if "thrd S0 (lsuc S0 p) = Some w" for w
      using successive_block_exit[OF assms(1) pV, of w] thrd_old_rev True that
        succ_lsuc_exits_block[OF pV] pblock(4) Csub
      by auto
    thus ?thesis
      using untouched_i_desc[OF assms(1) lnb] final_thrd_oldrev aftn_eq_thrd_lsuc_p True lnj
      by (cases "thrd S0 (lsuc S0 p)") (auto simp: ex_def C_def)
  qed
  text \<open>Off-stem nodes inside @{term "block S0 p"}.\<close>
  have blk: "ex (lsuc S0 v)" if vb: "v \<in> set (block S0 p)" and vns: "v \<notin> s ` {..k}"
  proof-
    have "v \<in> set (follow newprnt u) \<longleftrightarrow> v \<in> set (follow (prnt S0) u)" for u
      using newpath_nonstem_char[OF vb vns, of u] follow_newprnt_off_block[of u]
      by (cases "u \<in> set (block S0 p)") simp_all
    hence Cv: "C = children (prnt S0) v"
      by (simp add: C_def children_def)
    have sub: "children (prnt S0) v \<subseteq> set (block S0 p)"
      using ppt_children_subset[of v p] vb pblock(4)
      by simp
    have "final_thrd (lsuc S0 v) = None \<or> the (final_thrd (lsuc S0 v)) \<notin> children (prnt S0) v"
    proof(cases "lsuc S0 v \<in> lsx ` {..k}")
      case True
      then obtain t where "t \<le> k" "lsuc S0 v = lsx t"
        by auto
      thus ?thesis
        using final_thrd_lsx[of t] blockv_offstem_no_stem[OF vns assms(1) vb, of "Suc t"]
              final_thrd_lsxk_exits sub blockP(4)[OF assms(1)]
        by (cases "t = k") auto
    next
      case notlsx: False
      show ?thesis
      proof(cases "lsuc S0 v \<in> bef ` set [0..<k]")
        case True
        then obtain m where m: "m < k" "lsuc S0 v = bef m"
          by auto
        hence dq: "defQ m \<noteq> []"
          using bef_collision[of m] notlsx
          by force
        show ?thesis
          using successive_block_exit[OF assms(1) bef_pred(4)[OF m(1)]] bef_pred(1)[OF m(1)]
            final_thrd_bef[OF m(1) dq] out_eq_hd_defQ[OF m(1) dq] m(2)
          by (auto simp: out_def)

      next
        case False
        have "lsuc S0 v \<in> set (concat (map contrib [0..<Suc k]))"
          using lsuc_in_children[OF assms(1)] sub newblock_set
          by (auto simp: newblock_def simp del: upt_Suc)
        then obtain t where "t \<le> k" "lsuc S0 v \<in> set (contrib t)"
          by (auto simp: less_Suc_eq_le simp del: upt_Suc)
        thus ?thesis
          using contrib_fresh[OF _ _ notlsx False] succ_lsuc_exits_block[OF assms(1)]
          by (cases "thrd S0 (lsuc S0 v)") auto
      qed
    qed
    thus ?thesis
      using lsuc_in_children[OF assms(1)] Cv
      by (simp add: ex_def)
  qed
  have "ex (if v \<in> set (follow (prnt S0) (the (prnt S0 p))) \<and> lsuc S0 v = lsuc S0 p
      then (if jn \<noteq> the (rvth S0 p) \<and> j \<noteq> the (rvth S0 p) then the (rvth S0 p) else lsx k)
      else if lsuc S0 v = j \<or> v \<in> s ` {..k} then lsx k else lsuc S0 v)"
    by (rule last_descendant_selector[OF assms(1) jnj jnp pjn])
       (use lsxk out_rv stem unt blk in auto)
  thus ?thesis
    using exl ev
    by simp
qed

lemma lsuc_update_tree_r:
  "lsuc (update_tree S0 i j p jn) r = last newlist"
  using lsuc_last[OF rV, of newlist "[]"] out_edge set_newlist children_root[OF clauseA]
  by (simp add: update_tree_thrd update_tree_prnt)

lemma clauseE:
   "dom (thrd (update_tree S0 i j p jn)) = V - {lsuc (update_tree S0 i j p jn) r}"
  using dom_thrd_update_tree lsuc_update_tree_r
  by simp

lemma clauseJ:
   "\<forall>v\<in>V. \<exists>pre. follow (thrd (update_tree S0 i j p jn)) v
           = pre @ (case thrd (update_tree S0 i j p jn) (lsuc (update_tree S0 i j p jn) v) of
                      None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd (update_tree S0 i j p jn)) w)
           \<and> pre \<noteq> [] \<and> last pre = lsuc (update_tree S0 i j p jn) v
           \<and> set pre = children (prnt (update_tree S0 i j p jn)) v"
  by (rule clauseJ_from_lsuc[OF clauseB clauseJ_contig lsuc_last])

lemma set_drt_k: "set (drt k) = insert j (lsx ` {..<k})"
  by (auto simp: drt_def)

lemma distinct_drt_k[simp]:
   "distinct (drt k)"
  using j_notin_lsx_img lsx_inj_le
  by (fastforce simp: drt_def distinct_map inj_on_def)

lemma final_thrd_target:
  "final_thrd x = Some y \<Longrightarrow> y \<in> V \<and> y \<noteq> r"
  using newlist_chain(4) hd_newlist
  by (auto simp: ran_def)

lemma final_thrd_inj:
  "\<lbrakk>final_thrd v = Some w; final_thrd v' = Some w\<rbrakk> \<Longrightarrow> v = v'"
  using distinct_newlist
  by (fastforce dest: final_thrd_reverse_chain simp: nth_eq_iff_index_eq)

lemma ran_final_thrd_ge:
  "\<lbrakk>v' \<in> V; v' \<noteq> r\<rbrakk> \<Longrightarrow> \<exists>v. final_thrd v = Some v'"
  using newlist_chain(4) hd_newlist
  by (auto simp: ran_def)

lemma final_rvth_eval:
  "final_rvth w = (if \<exists>u\<in>set (drt k). final_thrd u = Some w
                   then Some (last (filter (\<lambda>u. final_thrd u = Some w) (drt k))) else rvth_pre w)"
  using foldl_upd_eval[of final_thrd rvth_pre "drt k" w]
  by (simp add: final_rvth_def rvth_pre_def Let_def)

lemma final_rvth_at_dirty_target:
  assumes "u \<in> set (drt k)" "final_thrd u = Some w"
  shows "final_rvth w = Some u"
proof-
  have "filter (\<lambda>u'. final_thrd u' = Some w) (drt k) = filter (\<lambda>u'. u' = u) (drt k)"
  proof(rule filter_cong[OF refl])
    fix u'
    show "(final_thrd u' = Some w) = (u' = u)"
      using final_thrd_inj[OF _ assms(2), of u'] assms(2)
      by blast
  qed
  moreover have "\<exists>u'\<in>set (drt k). final_thrd u' = Some w"
    using assms(1) assms(2)
    by blast
  ultimately show ?thesis
    using final_rvth_eval[of w] filter_eq_self_single[OF distinct_drt_k assms(1)]
    by simp
qed

lemma rvth_pre_at_Sq:
  assumes "final_thrd (lsx k) = Some w"
  shows "rvth_pre w = Some (lsx k)"
proof(cases "the (rvth S0 p) = j")
  case False
  have tc: "thrd S0 j = Some w"
    using final_thrd_lsx_k assms(1) False
    by simp
  have "aftn k \<noteq> Some w"
    using final_thrd_oldrev[OF False] final_thrd_inj[OF assms(1), of "the (rvth S0 p)"] lsx_in_block_p[of k]
          old_rev_notin_block_p
    by auto
  thus ?thesis
    using tc False
    by (cases "aftn k") (simp_all add: rvth_pre_def Let_def)
next
  case True
  hence "thrd S0 (lsuc S0 p) = Some w"
    using final_thrd_lsx_k assms(1)
    by simp
  thus ?thesis
    using True
    by (simp add: rvth_pre_def Let_def)
qed

lemma rvth_pre_at_Ss:
  "\<lbrakk>the (rvth S0 p) \<noteq> j; final_thrd (the (rvth S0 p)) = Some w\<rbrakk> \<Longrightarrow> rvth_pre
    w = Some (the (rvth S0 p))"
  using final_thrd_oldrev
  by (simp add: rvth_pre_def Let_def)

lemma rvth_pre_off_splice:
  "\<lbrakk>final_thrd (lsx k) \<noteq> Some v'; the (rvth S0 p) \<noteq> j \<Longrightarrow> aftn k \<noteq> Some
    v'\<rbrakk> \<Longrightarrow> rvth_pre v' = (rvth S0 ++ revBR k) v'"
  using final_thrd_lsx_k
  by (cases "the (rvth S0 p) = j") (auto simp: rvth_pre_def Let_def Sfin_def split: option.split)

lemma out_collision:
  "\<lbrakk>t < k; defQ t = []\<rbrakk> \<Longrightarrow> out t = out (Suc t)"
  by (simp add: defQ_empty out_def)

lemma bef_non_dirty_defQ:
  "\<lbrakk>t < k; bef t \<notin> set (drt k); bef t \<noteq> lsx k\<rbrakk> \<Longrightarrow> defQ t \<noteq> []"
  using bef_collision[of t]
  by (cases "Suc t = k") (auto simp: set_drt_k)

lemma final_thrd_of_revBR:
  assumes "revBR k v' = Some v" "v \<noteq> lsx k"
  shows "final_thrd v = Some v'"
proof-
  obtain t where t: "t < k" "out t = Some v'" "bef t = v" "\<forall>t'. t < t' \<longrightarrow> t' < k
    \<longrightarrow> out t' \<noteq> Some v'"
    using revBR_eval_last[OF assms(1)]
    by blast
  have dq: "defQ t \<noteq> []"
  proof
    assume dq: "defQ t = []"
    thus False
      using bef_collision[OF t(1) dq] out_collision[OF t(1) dq] t assms(2)
      by (cases "Suc t = k") auto
  qed
  thus ?thesis
    using final_thrd_bef[OF t(1) dq] out_eq_hd_defQ[OF t(1) dq] t(2,3)
    by simp
qed

lemma revBR_lsxk_splice:
  assumes "revBR k v' = Some (lsx k)"
  shows "final_thrd (lsx k) = Some v' \<or> aftn k = Some v'"
proof-
  obtain t where t: "t < k" "out t = Some v'" "bef t = lsx k"
    using revBR_eval_ex[OF assms(1)]
    by blast
  show ?thesis
  proof(cases "defQ t = []")
    case True
    hence "Suc t = k"
      using bef_collision[OF t(1)] t(1,3) lsx_inj_le[of "Suc t" k]
      by fastforce
    thus ?thesis
      using out_collision[OF t(1) True] t(2)
      by (simp add: aftn_def)
  next
    case False
    thus ?thesis
      using final_thrd_bef[OF t(1) False] out_eq_hd_defQ[OF t(1) False] t
      by simp
  qed
qed

lemma clauseG_fwd:
  assumes "final_thrd v = Some v'"
  shows "final_rvth v' = Some v"
proof(cases "v \<in> set (drt k)")
  case notdirty: False
  have inj: "u = v" if "final_thrd u = Some v'" for u
    using final_thrd_inj[OF that assms(1)] .
  have "\<not> (\<exists>u\<in>set (drt k). final_thrd u = Some v')"
    using inj notdirty
    by blast
  hence FRE: "final_rvth v' = rvth_pre v'"
    using final_rvth_eval[of v']
    by simp
  consider "v = lsx k" | "v = the (rvth S0 p)" | "v \<noteq> lsx k" "v \<noteq> the (rvth S0 p)"
    by blast
  thus ?thesis
  proof cases
    case 1
    thus ?thesis
      using rvth_pre_at_Sq assms(1) FRE
      by simp
  next
    case 2
    hence "the (rvth S0 p) \<noteq> j"
      using notdirty
      by (auto simp: drt_def)
    thus ?thesis
      using rvth_pre_at_Ss assms(1) FRE 2
      by simp
  next
    case rest: 3
    have tcne: "final_thrd (lsx k) \<noteq> Some v'" and aftne: "the (rvth S0 p) \<noteq> j \<Longrightarrow> aftn k
      \<noteq> Some v'"
      using inj[of "lsx k"] inj[of "the (rvth S0 p)"] final_thrd_oldrev rest
      by auto
    note RP = rvth_pre_off_splice[OF tcne aftne]
    show ?thesis
    proof(cases "revBR k v'")
      case (Some w0)
      have "w0 \<noteq> lsx k"
        using revBR_lsxk_splice final_thrd_lsx_k aftn_eq_thrd_lsuc_p tcne aftne Some
        by (cases "the (rvth S0 p) = j") auto
      thus ?thesis
        using inj[OF final_thrd_of_revBR[OF Some]] FRE RP Some
        by simp
    next
      case None
      have "v \<notin> lsx ` {..k}"
        using notdirty rest
        by (auto simp: set_drt_k le_less)
      moreover have "v \<notin> bef ` set [0..<k]"
      proof
        assume "v \<in> bef ` set [0..<k]"
        then obtain t where t: "t < k" "v = bef t"
          by auto
        hence "defQ t \<noteq> []"
          using bef_non_dirty_defQ notdirty rest
          by blast
        hence "out t = Some v'"
          using final_thrd_bef[OF t(1)] out_eq_hd_defQ[OF t(1)] assms(1) t(2)
          by simp
        hence "v' \<in> dom (revBR k)"
          using t(1)
          unfolding revBR_dom
          by force
        thus False
          using None
          by auto
      qed
      ultimately have "thrd S0 v = Some v'"
        using final_thrd_fresh[of v] notdirty rest assms(1)
        by (simp add: drt_def)
      thus ?thesis
        using arbD(10) FRE RP None
        by (simp add: map_add_def)
    qed
  qed
qed (rule final_rvth_at_dirty_target[OF _ assms(1)])

lemma rvth_pre_dom:
  assumes "rvth_pre v' = Some v"
  shows "v' \<in> V \<and> v' \<noteq> r"
  using assms rvth_pre_off_splice[of v'] revBR_eval_ex[of v' v] arbD(9,10)
    final_thrd_oldrev final_thrd_target
  by (cases "final_thrd (lsx k) = Some v'";
      cases "the (rvth S0 p) \<noteq> j \<and> aftn k = Some v'";
      cases "revBR k v'") (auto simp: map_add_def out_def dom_def)

lemma clauseG:
   "final_thrd v = Some v' \<longleftrightarrow> final_rvth v' = Some v"
proof
  assume "final_rvth v' = Some v"
  hence "v' \<in> V - {r}"
    using final_rvth_eval[of v'] rvth_pre_dom[of v' v] final_thrd_target
    by (cases "\<exists>u\<in>set (drt k). final_thrd u = Some v'") auto
  thus "final_thrd v = Some v'"
    using ran_final_thrd_ge clauseG_fwd \<open>final_rvth v' = Some v\<close>
    by fastforce
qed (rule clauseG_fwd)

lemma dom_final_rvth:
   "dom final_rvth = V - {r}"
  using clauseG newlist_chain(4) hd_newlist
  by (auto simp: dom_def ran_def)

lemma parent_spec_final_rvth: "parent_spec final_rvth"
  by (rule parent_spec_reverse_chain[OF distinct_newlist])
     (use clauseG final_thrd_reverse_chain in blast)

lemma clauseC:
   "parent_spec (rvth (update_tree S0 i j p jn))"
  using update_tree_rvth parent_spec_final_rvth
  by simp

lemma clauseF:
   "dom (rvth (update_tree S0 i j p jn)) = V - {r}"
  using update_tree_rvth dom_final_rvth
  by simp

lemma arb_invar_update_tree:
   "arb_invar r V (update_tree S0 i j p jn)"
  by (rule arb_invarI[OF _ clauseB clauseC clauseD clauseE
                         clauseF _ _ clauseI clauseJ])
     (simp_all add: clauseA update_tree_prnt update_tree_thrd update_tree_rvth
                    clauseG lsuc_update_tree_eval arbD(11)
                    old_rev_in_V lsx_k_in_V)

end

context stem_setup begin

lemma arb_invar_update_tree:
  assumes "jn = join_of (prnt S0) i j"
  shows "arb_invar r V (update_tree S0 i j p jn)"
  by (rule stem_pivot.arb_invar_update_tree)
     (unfold_locales; use assms join_facts in auto)

lemma prnt_ip: "prnt (update_tree S0 p j p jn) p = Some j"
  by (simp add: move_prnt)

end

lemma pivot_stem_setup:
  assumes "arb_invar r V S0" and "i \<in> V" "j \<in> V" and "p \<in> set (follow (prnt S0) i)"
    and "jn \<in> set (follow (prnt S0) p)" and "jn = join_of (prnt S0) i j" "p \<noteq> jn"
  obtains s k where "stem_setup S0 r V i j p k s"
proof-
  obtain s k where "s 0 = i" "s k = p" "\<And>t. t < k \<Longrightarrow> prnt S0 (s t) = Some (s (Suc t))" "inj_on s
    {..k}"
    by (rule follow_path[OF arb_invarD(2)[OF assms(1)] assms(4)]) blast
  moreover have "j \<notin> children (prnt S0) p"
    using no_cycle[OF arb_invarD(2)[OF assms(1)] assms(4) assms(5) assms(6,7)]
    by (simp add: children_def)
  ultimately have "stem_setup S0 r V i j p k s"
    using pivot_p_ne_r[OF assms(1) assms(5) not_sym[OF assms(7)]] assms(1) assms(2,3)
    by (simp add: stem_setup_def)
  thus ?thesis
    by (rule that)
qed

subsection \<open>Correctness: the swap preserves the invariant\<close>

text \<open>@{term jn} is the apex of the cycle, @{term p} an ancestor-or-self of @{term i} strictly below
      it, so the leaving edge @{term "(p, the (prnt S p))"} sits on the cycle below the apex.\<close>

lemma update_tree_preserves_arb_invar:
  assumes "arb_invar r V S" and "i \<in> V" and "j \<in> V" and "jn = join_of (prnt S) i j"
    and "p \<in> set (follow (prnt S) i)" and "jn \<in> set (follow (prnt S) p)" and "p \<noteq> jn"
  shows "arb_invar r V (update_tree S i j p jn)" "prnt (update_tree S i j p jn) i = Some j"
proof-
  obtain s k where "stem_setup S r V i j p k s"
    by (rule pivot_stem_setup[OF assms(1) assms(2) assms(3) assms(5) assms(6) assms(4) assms(7)])
  then interpret ss: stem_setup S r V i j p k s .
  have kpos: "0 < k" if "i \<noteq> p"
    using that ss.path0 ss.pathk
    by (cases k) auto
  show "arb_invar r V (update_tree S i j p jn)"
    by (rule ss.arb_invar_update_tree[OF assms(4)])
  show "prnt (update_tree S i j p jn) i = Some j"
    using kpos ss.prnt_ip ss.update_tree_prnt_i
    by (cases "i = p") auto
qed

section \<open>Basic properties of the subtree iteration and the pair-of-paths search\<close>

subsection \<open>The subtree iteration folds over the children (subtree) in thread order\<close>

lemma subtree_fold_follow:
  assumes "parent_spec (thrd S)" and "follow (thrd S) u = bl @ stp # rest" and "stp \<notin> set bl"
  shows "subtree_fold S stp u f acc = foldl (\<lambda>a x. f x a) acc (bl @ [stp])"
  using assms(2) assms(3)
proof(induction bl arbitrary: u acc)
  case Nil
  thus ?case
    using follow_hd_ps[OF assms(1), of u]
    by (subst subtree_fold.simps) (auto simp: Let_def)
next
  case (Cons b bs)
  hence "u = b" "u \<noteq> stp"
    using follow_hd_ps[OF assms(1), of u]
    by auto
  moreover then obtain w where "thrd S u = Some w" "follow (thrd S) w = bs @ stp # rest"
    using Cons.prems(1) follow_ps_simps[OF assms(1), of u]
    by (cases "thrd S u") auto
  ultimately show ?case
    using Cons
    by (subst subtree_fold.simps) (simp add: Let_def)
qed

lemma iterate_root_opposed_impl_block:
  assumes "arb_invar r V S" and "v \<in> V"
  shows "iterate_root_opposed_impl S v f acc = foldl (\<lambda>a x. f x a) acc (block S v)"
proof-
  define bl where "bl = butlast (block S v)"
  have bl: "block S v = bl @ [lsuc S v]"
    using append_butlast_last_id[OF block_props(2)[OF assms(1) assms(2)]] block_props(3)[OF assms(1) assms(2)]
    by (simp add: bl_def)
  hence L: "follow (thrd S) v = bl @ lsuc S v # (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow>
    follow (thrd S) w)"
    using block_props(1)[OF assms(1) assms(2)]
    by simp
  hence "lsuc S v \<notin> set bl"
    using follow_distinct_ps[OF arb_invarD(3)[OF assms(1)], of v]
    by simp
  thus ?thesis
    using subtree_fold_follow[OF arb_invarD(3)[OF assms(1)] L] bl
    by (simp add: iterate_root_opposed_impl_def)
qed

theorem iterate_root_opposed_impl_foldr:
  assumes "arb_invar r V S" "v \<in> V"
  shows "\<exists>xs. distinct xs \<and> set xs = children (prnt S) v \<and>
    iterate_root_opposed_impl S v f acc = foldr f xs acc"
  using follow_distinct_ps[OF arb_invarD(3)[OF assms(1)], of v] block_props(1,4)[OF assms]
    iterate_root_opposed_impl_block[OF assms]
  by (intro exI[of _ "rev (block S v)"] conjI) (auto simp: foldr_conv_foldl)

subsection \<open>The pair-of-paths search returns the two branches up to the join\<close>

text \<open>A proper ancestor has a strictly larger subtree, so the @{const snum}-guided climb never
      lifts the join.\<close>

lemma snum_proper_anc_lt:
  assumes "arb_invar r V (S :: 'a ndtree)" and "a \<in> V"
    and "a \<in> set (follow (prnt S) b)" and "a \<noteq> b"
  shows "snum S b < snum S a"
proof-
  have ps: "parent_spec (prnt S)"
    by (rule arb_invarD(2)[OF assms(1)])
  have "b \<in> V"
    using follow_None_ps[OF ps, of b] rooted_arborescense_invar_child_in_V[OF arb_invarD(1)[OF assms(1)], of b]
      assms(3) assms(4)
    by (cases "prnt S b") auto
  moreover have "children (prnt S) b \<subset> children (prnt S) a"
    using children_subset[OF ps, of b a] follow_mem_ps[OF ps, of a] ancestor_antisym[OF ps assms(3)] assms(3) assms(4)
    by (auto simp: children_def)
  moreover have "finite (children (prnt S) a)"
    using block_props(4)[OF assms(1) assms(2)] List.finite_set[of "block S a"]
    by simp
  ultimately show ?thesis
    using psubset_card_mono arb_invarD(12)[OF assms(1)] assms(2)
    by simp
qed

lemma follow_cons_of_anc:
  assumes "parent_spec T" and "j \<in> set (follow T x)" and "x \<noteq> j"
  shows "\<exists>w. T x = Some w \<and> follow T x = x # follow T w \<and> j \<in> set (follow T w)"
  using follow_ps_simps[OF assms(1), of x] assms(2) assms(3)
  by (cases "T x") auto

lemma follow_last_root:
  assumes "arb_invar r V S" "u \<in> V"
  shows "last (follow (prnt S) u) = r"
  by (rule last_follow_root[OF arb_invarD(1)[OF assms(1)] assms(2)])

lemma join_paths_loop_eval:
  assumes "arb_invar r V S" and "cu0 \<in> V" and "cv0 \<in> V"
    and "j \<in> set (follow (prnt S) cu0)" and "j \<in> set (follow (prnt S) cv0)"
    and "set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cu0))
                \<inter> set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cv0)) = {}"
  shows "join_paths_loop S cu0 cv0 acc1 acc2
          = (rev acc1 @ takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cu0),
             rev acc2 @ takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) cv0))"
proof-
  define W where "W = (\<lambda>x. takeWhile (\<lambda>y. y \<noteq> j) (follow (prnt S) x))"
  have ps: "parent_spec (prnt S)"
    by (rule arb_invarD(2)[OF assms(1)])
  have jV: "j \<in> V"
    using follow_subset_V[OF arb_invarD(1)[OF assms(1)] assms(2)] assms(4)
    by auto
  have "join_paths_loop S cu cv a1 a2 = (rev a1 @ W cu, rev a2 @ W cv)"
    if "cu \<in> V" "cv \<in> V" "j \<in> set (follow (prnt S) cu)" "j \<in> set (follow (prnt S) cv)"
      "set (W cu) \<inter> set (W cv) = {}" for cu cv a1 a2
    using that
  proof(induction "length (follow (prnt S) cu) + length (follow (prnt S) cv)" arbitrary: cu cv a1 a2
         rule: less_induct)
    case less
    show ?case
    proof(cases "cu = cv")
      case True
      moreover have "cu = j"
        using True less.prems(3,5) follow_hd_ps[OF ps, of cu] follow_ne_ps[OF ps, of cu]
        by (cases "follow (prnt S) cu") (auto simp: W_def split: if_splits)
      ultimately show ?thesis
          using follow_hd_ps[OF ps, of j] follow_ne_ps[OF ps, of j]
        by (subst join_paths_loop.simps) (simp add: W_def takeWhile_eq_Nil_iff)
    next
      case ne: False
      show ?thesis
      proof(cases "snum S cu \<le> snum S cv")
        case le: True
        have "cu \<noteq> j"
          using snum_proper_anc_lt[OF assms(1) jV less.prems(4)] ne le
          by auto
        then obtain w where "prnt S cu = Some w" "follow (prnt S) cu = cu # follow (prnt S) w"
            "j \<in> set (follow (prnt S) w)"
          using follow_cons_of_anc[OF ps less.prems(3)]
          by blast
        moreover hence "w \<in> V" "set (W w) \<inter> set (W cv) = {}"
          using follow_subset_V[OF arb_invarD(1)[OF assms(1)] less.prems(1)] follow_mem_ps[OF ps, of w]
                less.prems(5) \<open>cu \<noteq> j\<close>
          by (auto simp: W_def)
        ultimately show ?thesis
          using less.hyps[of w cv] less.prems(2,4) ne le \<open>cu \<noteq> j\<close>
          by (simp add: W_def join_paths_loop.simps[of S cu cv])
      next
        case nle: False
        have "cv \<noteq> j"
          using snum_proper_anc_lt[OF assms(1) jV less.prems(3)] ne nle
          by auto
        then obtain w where "prnt S cv = Some w" "follow (prnt S) cv = cv # follow (prnt S) w"
            "j \<in> set (follow (prnt S) w)"
          using follow_cons_of_anc[OF ps less.prems(4)]
          by blast
        moreover hence "w \<in> V" "set (W cu) \<inter> set (W w) = {}"
          using follow_subset_V[OF arb_invarD(1)[OF assms(1)] less.prems(2)] follow_mem_ps[OF ps, of w]
                less.prems(5) \<open>cv \<noteq> j\<close>
          by (auto simp: W_def)
        ultimately show ?thesis
          using less.hyps[of cu w] less.prems(1,3) ne nle \<open>cv \<noteq> j\<close>
          by (simp add: W_def join_paths_loop.simps[of S cu cv])
      qed
    qed
  qed
  from this[OF assms(2) assms(3) assms(4) assms(5)]
  show ?thesis
    using assms(6)
    by (simp add: W_def)
qed

lemma follow_split_at_j:
  assumes "parent_spec T" and "j \<in> set (follow T u)"
  shows "follow T u = takeWhile (\<lambda>x. x \<noteq> j) (follow T u) @ follow T j"
proof-
  obtain A C where "follow T u = A @ j # C" "\<forall>x\<in>set A. x \<noteq> j"
    using split_list_first[OF assms(2)]
    by blast
  thus ?thesis
    using follow_append_ps[OF assms(1), of u A j C] takeWhile_append2[of A "\<lambda>x. x \<noteq> j" "j # C"]
    by simp
qed

lemma join_takeWhile_disjoint:
  assumes "arb_invar r V S" and "u \<in> V" and "v \<in> V" and "j = join_of (prnt S) u v"
  shows "set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) u))
        \<inter> set (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) v)) = {}"
proof-
  have ps: "parent_spec (prnt S)"
    by (rule arb_invarD(2)[OF assms(1)])
  have "j \<in> set (follow (prnt S) u)"
    using join_of_mem(1)[OF ps] follow_last_root[OF assms(1) assms(2)] follow_last_root[OF assms(1) assms(3)] assms(4)
    by simp
  hence "distinct (takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) u) @ follow (prnt S) j)"
    using follow_distinct_ps[OF ps, of u]
    by (subst (asm) follow_split_at_j[OF ps])
  thus ?thesis
    using join_of_first[OF ps, of _ u v] assms(4)
    by (auto dest: set_takeWhileD)
qed

theorem get_path_pair_impl_correct:
  assumes "arb_invar r V S" and "u \<in> V" and "v \<in> V"
    and "get_path_pair_impl S u v = (p1, p2)"
  defines "j \<equiv> join_of (prnt S) u v"
  shows "follow (prnt S) u = p1 @ follow (prnt S) j" "follow (prnt S) v = p2 @ follow (prnt S) j"
    "distinct (p1 @ [j])" "distinct (p2 @ [j])" "set p1 \<inter> set p2 = {}"
    "set (p1 @ [j]) \<inter> set (p2 @ [j]) = {j}"
proof-
  have ps: "parent_spec (prnt S)"
    by (rule arb_invarD(2)[OF assms(1)])
  have ju: "j \<in> set (follow (prnt S) u)" and jv: "j \<in> set (follow (prnt S) v)"
    using join_of_mem[OF ps] follow_last_root[OF assms(1) assms(2)] follow_last_root[OF assms(1) assms(3)]
    by (simp_all add: j_def)
  note disj = join_takeWhile_disjoint[OF assms(1) assms(2) assms(3) j_def[THEN meta_eq_to_obj_eq]]
  have p12: "p1 = takeWhile (\<lambda>x. x \<noteq> j) (follow (prnt S) u)" "p2 = takeWhile (\<lambda>x. x \<noteq> j)
    (follow (prnt S) v)"
    using join_paths_loop_eval[OF assms(1) assms(2) assms(3) ju jv disj, of "[]" "[]"] assms(4)
    by (simp_all add: get_path_pair_impl_def)
  show P1: "follow (prnt S) u = p1 @ follow (prnt S) j"
    unfolding p12(1)
    by (rule follow_split_at_j[OF ps ju])
  show P2: "follow (prnt S) v = p2 @ follow (prnt S) j"
    unfolding p12(2)
    by (rule follow_split_at_j[OF ps jv])
  have "distinct (p1 @ follow (prnt S) j)" "distinct (p2 @ follow (prnt S) j)"
    using follow_distinct_ps[OF ps, of u] follow_distinct_ps[OF ps, of v]
    by (simp_all only: P1 P2)
  thus "distinct (p1 @ [j])" "distinct (p2 @ [j])" "set p1 \<inter> set p2 = {}" "set (p1 @ [j]) \<inter> set (p2 @
    [j]) = {j}"
    using disj p12 follow_mem_ps[OF ps, of j]
    by auto
qed

end
