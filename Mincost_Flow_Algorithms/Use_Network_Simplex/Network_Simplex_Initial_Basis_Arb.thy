theory Network_Simplex_Initial_Basis_Arb
  imports Network_Simplex_Initial_Basis_Correct
begin

context initial_basis_correct
begin

section \<open>Assembling the abstract arborescence from the finished tree\<close>

text \<open>The DFS produces five vertex-indexed arrays (@{const ds_prnt}, @{const ds_thrd}, @{const ds_rvth},
      @{const ds_lsuc}, @{const ds_snum}); here we read them off @{const build_tree} into the abstract
      @{typ \<open>nat ndtree\<close>} @{term Sarb}, with root @{term \<open>vcount\<close>} and vertex set
      @{term \<open>Varb\<close>}. The vertex set is based on the \<^emph>\<open>seen\<close> set @{term Vseen} (which
      coincides with the real vertices \<open>set vs_list\<close> --- a bridge deferred to the network-simplex layer);
      this makes @{const follow} over the parent map and @{const children} coincide \<^emph>\<open>directly\<close>
      with the array-level @{const pstep}/@{const desc} machinery of the correctness theory. We then discharge the
      @{const arb_invar} obligations (via @{thm arb_invarI}) that do not require the explicit emission order; the
      thread-side ones are flagged at the end.\<close>

definition Vseen :: "nat set" where
  "Vseen = {y. y < vcount \<and> ds_seen (build_tree acyc_flow) ! y}"

definition Varb :: "nat set" where
  "Varb = insert vcount Vseen"

definition Sprnt :: "nat \<Rightarrow> nat option" where
  "Sprnt v = (if v \<in> Vseen then Some (ds_prnt (build_tree acyc_flow) ! v) else None)"

definition Sthrd :: "nat \<Rightarrow> nat option" where
  "Sthrd v = (if v \<in> Varb \<and> ds_thrd (build_tree acyc_flow) ! v \<noteq> 0
    then Some (ds_thrd (build_tree acyc_flow) ! v) else None)"

definition Srvth :: "nat \<Rightarrow> nat option" where
  "Srvth v = (if v \<in> Varb \<and> ds_rvth (build_tree acyc_flow) ! v \<noteq> 0
    then Some (ds_rvth (build_tree acyc_flow) ! v) else None)"

definition Sarb :: "nat ndtree" where
  "Sarb = \<lparr> prnt = Sprnt, thrd = Sthrd, rvth = Srvth,
            lsuc = (\<lambda>v. ds_lsuc (build_tree acyc_flow) ! v),
            snum = (\<lambda>v. ds_snum (build_tree acyc_flow) ! v) \<rparr>"

lemma Sarb_sel: "prnt Sarb = Sprnt" "thrd Sarb = Sthrd" "rvth Sarb = Srvth"
  "lsuc Sarb = (\<lambda>v. ds_lsuc (build_tree acyc_flow) ! v)"
  "snum Sarb = (\<lambda>v. ds_snum (build_tree acyc_flow) ! v)"
  by (simp_all add: Sarb_def)

lemma r_in_V: "vcount \<in> Varb"
  by (simp add: Varb_def)

lemma Vseen_finite: "finite Vseen"
  by (rule finite_subset[of _ "{..<vcount}"]) (auto simp: Vseen_def)

lemma pstep_eq_Sprnt: "pstep (build_tree acyc_flow) = {(x, y) |x y. Some y = Sprnt x}"
  by (auto simp: pstep_def Sprnt_def Vseen_def split: if_splits)

subsection \<open>Parent map: @{const parent_spec} via acyclicity of the parent step\<close>

text \<open>@{const parent_spec} of @{term \<open>prnt Sarb\<close>} is wellfoundedness of the parent relation, i.e.\
      acyclicity of @{term \<open>pstep (build_tree acyc_flow)\<close>} (child {\isasymrightarrow} parent).
      @{const pstep} is single-valued and every emitted vertex reaches the root through it
      (\<open>build_tree_reaches_root\<close>, I6), and the root has no outgoing parent step --- a single-valued
      relation in which every point reaches a sink has no cycle.\<close>

lemma orbit_returns:
  "\<lbrakk>single_valued R; (a, b) \<in> R\<^sup>*; (a, a) \<in> R\<^sup>+\<rbrakk>
    \<Longrightarrow> (b, a) \<in> R\<^sup>*"
proof(rotate_tac 1, induction rule: rtrancl_induct)
  case (step b c)
  then obtain d where "(b, d) \<in> R" "(d, a) \<in> R\<^sup>*" by (blast dest: tranclD rtrancl_trancl_trancl)
  with step show ?case by (auto simp: single_valued_def)
qed simp

lemma sink_no_cycle:
  "\<lbrakk>single_valued R; (a, z) \<in> R\<^sup>*; z \<notin> Domain R\<rbrakk>
    \<Longrightarrow> (a, a) \<notin> R\<^sup>+"
  by (blast dest: orbit_returns tranclD elim: converse_rtranclE)

lemma pstep_acyclic: "acyclic (pstep (build_tree acyc_flow))"
  unfolding acyclic_def
proof(intro allI notI)
  fix x assume "(x, x) \<in> (pstep (build_tree acyc_flow))\<^sup>+"
  moreover from this have "x < vcount" "ds_seen (build_tree acyc_flow) ! x"
    by (auto dest!: tranclD simp: pstep_def)
  ultimately show False
    using sink_no_cycle[OF pstep_single_valued build_tree_reaches_root] by (auto simp: pstep_def)
qed

lemma sub_pstep: "{(x, y) |x y. Some x = Sprnt y}\<inverse> \<subseteq> pstep (build_tree acyc_flow)"
  by (auto simp: Sprnt_def pstep_def Vseen_def split: if_splits)

lemma parent_spec_Sprnt: "parent_spec Sprnt"
proof-
  have "{(x, y) |x y. Some x = Sprnt y} \<subseteq> (\<lambda>y. (ds_prnt (build_tree acyc_flow) ! y, y)) ` Vseen"
    by (auto simp: Sprnt_def split: if_splits)
  then have "finite {(x, y) |x y. Some x = Sprnt y}" by (rule finite_subset) (simp add: Vseen_finite)
  then show ?thesis
    unfolding parent_spec_def using acyclic_subset[OF pstep_acyclic sub_pstep]
    by (simp add: finite_acyclic_wf)
qed

subsection \<open>Bridge: @{const follow} of the parent map is the @{const pstep} ancestor set\<close>

text \<open>A generic fact: under @{const parent_spec}, the root-path @{term \<open>follow T u\<close>} enumerates
      exactly the ancestors of @{term u} --- the reflexive-transitive closure of the one-step parent relation.\<close>

lemma follow_set_rtrancl:
  assumes "parent_spec T" shows "set (follow T u) = {z. (u, z) \<in> {(x, y). T x = Some y}\<^sup>*}"
proof(induction u rule: wf_induct[OF assms[unfolded parent_spec_def]])
  case (1 u)
  show ?case
  proof(cases "T u")
    case None
    then show ?thesis using assms by (auto simp: follow_ps_simps elim: converse_rtranclE)
  next
    case (Some w)
    then show ?thesis using assms 1[rule_format, of w]
      by (auto simp: follow_ps_simps elim: converse_rtranclE intro: converse_rtrancl_into_rtrancl)
  qed
qed

lemma follow_Sprnt_pstep: "set (follow Sprnt u) = {z. (u, z) \<in> (pstep (build_tree acyc_flow))\<^sup>*}"
proof-
  have "{(x, y). Sprnt x = Some y} = pstep (build_tree acyc_flow)" using pstep_eq_Sprnt by auto
  then show ?thesis using follow_set_rtrancl[OF parent_spec_Sprnt, of u] by simp
qed

lemma children_Sprnt_desc: "v \<in> Vseen \<Longrightarrow> children Sprnt v = desc (build_tree acyc_flow) v"
  by (auto simp: children_def follow_Sprnt_pstep desc_def Vseen_def pstep_def elim: converse_rtranclE)

subsection \<open>@{const arb_invar} obligations discharged so far\<close>

text \<open>Root membership, the parent-map domain, the subtree-size obligation, and last-successor membership
      --- all on the interior (seen) vertices.\<close>

lemma dom_Sprnt: "dom Sprnt = Varb - {vcount}"
  by (auto simp: Sprnt_def Varb_def Vseen_def dom_def)

lemma snum_eq_children: "v \<in> Vseen \<Longrightarrow> snum Sarb v = card (children (prnt Sarb) v)"
  using build_tree_snum by (simp add: Sarb_sel children_Sprnt_desc dcard_def Vseen_def)

lemma lsuc_in_V: "v \<in> Vseen \<Longrightarrow> lsuc Sarb v \<in> Varb"
  using build_tree_lsuc[of v] by (auto simp: Sarb_sel desc_def Varb_def Vseen_def)

subsection \<open>Thread spanning: the forward thread from the root visits every tree vertex\<close>

text \<open>The DFS builds the thread by \<^emph>\<open>append at the end\<close>: each @{const dfs_discover} /
      @{const open_tree_component} splices the new vertex after @{const ds_prev} and makes it the new @{const ds_prev}.
      Hence the forward-thread relation @{term thrdstep} only ever grows by one edge
      @{term \<open>(ds_prev s, w)\<close>} at the current last vertex, and the set of vertices reachable from the root
      @{term vcount} grows by exactly that new vertex. We carry this reachability invariant @{term tspan} through the
      whole build (alongside @{const dfs_inv}), giving \<^emph>\<open>thread spanning\<close> at @{const build_tree}.
      This is what makes the thread's @{const follow} enumerate all of @{term Varb} (obligation 4) and --- with
      injectivity --- makes the thread relation acyclic (obligations 2, 3).\<close>

definition thrdstep :: "'n dfs_state \<Rightarrow> (nat \<times> nat) set" where
  "thrdstep s = {(x, ds_thrd s ! x) |x. x < Suc vcount \<and> (x = vcount \<or> ds_seen s ! x)
    \<and> ds_thrd s ! x \<noteq> 0}"

lemma thrdstep_iff:
  "(x, z) \<in> thrdstep s \<longleftrightarrow> x < Suc vcount \<and> (x = vcount \<or> ds_seen s ! x)
    \<and> ds_thrd s ! x \<noteq> 0 \<and> z = ds_thrd s ! x"
  by (auto simp: thrdstep_def)

lemma build_tree_thrd_prev0: "ds_thrd (build_tree acyc_flow) ! (ds_prev (build_tree acyc_flow)) = 0"
  using build_tree_thread_inv by (simp add: thread_inv_def)

lemma dfs_inv_wf_sized: "dfs_inv fl s \<Longrightarrow> dfs_wf fl s \<and> dfs_sized s"
  by (simp add: dfs_inv_def)

lemma dfs_inv_prev:
  "dfs_inv fl s \<Longrightarrow> ds_prev s < Suc vcount \<and> (ds_prev s = vcount \<or> ds_seen s ! ds_prev s)
    \<and> ds_thrd s ! ds_prev s = 0 \<and> length (ds_seen s) = Suc vcount \<and> length (ds_thrd s) = Suc vcount"
  by (simp add: dfs_inv_def thread_inv_def dfs_sized_def)

lemma dfs_inv_thrd_unseen:
  "\<lbrakk>dfs_inv fl s; w < vcount; \<not> ds_seen s ! w\<rbrakk> \<Longrightarrow> ds_thrd s ! w = 0"
  by (simp add: dfs_inv_def thread_inv_def)

lemma thrdstep_append:
  "\<lbrakk>dfs_inv fl s; w < vcount; w \<noteq> 0; \<not> ds_seen s ! w; ds_seen t = (ds_seen s)[w := True];
    ds_thrd t = (ds_thrd s)[ds_prev s := w]\<rbrakk> \<Longrightarrow> thrdstep t = insert (ds_prev s, w) (thrdstep s)"
  by (frule dfs_inv_prev) (auto simp: set_eq_iff thrdstep_iff nth_list_update dfs_inv_thrd_unseen)

definition tspan :: "'n dfs_state \<Rightarrow> bool" where
  "tspan s \<longleftrightarrow>
    (\<forall>y. (y = vcount \<or> (y < vcount \<and> ds_seen s ! y))
      \<longrightarrow> (vcount, y) \<in> (thrdstep s)\<^sup>*)"

lemma tspan_append:
  assumes "dfs_inv fl s" "tspan s" "w < vcount" "w \<noteq> 0" "\<not> ds_seen s ! w"
    "ds_seen t = (ds_seen s)[w := True]" "ds_thrd t = (ds_thrd s)[ds_prev s := w]"
  shows "tspan t"
proof-
  have R: "thrdstep t = insert (ds_prev s, w) (thrdstep s)" "length (ds_seen s) = Suc vcount"
    "ds_prev s = vcount \<or> (ds_prev s < vcount \<and> ds_seen s ! ds_prev s)"
    using assms(1) thrdstep_append[OF assms(1,3-7)] dfs_inv_prev[of fl s] by (auto simp: less_Suc_eq)
  then have "(vcount, y) \<in> (thrdstep t)\<^sup>*" if "y = vcount \<or> y < vcount \<and> ds_seen s ! y" for y
    using that assms(2) rtrancl_mono[of "thrdstep s" "thrdstep t"] by (auto simp: tspan_def)
  moreover from this R have "(vcount, w) \<in> (thrdstep t)\<^sup>*"
    by (auto intro: rtrancl_into_rtrancl[of _ "ds_prev s"])
  ultimately show ?thesis using assms(6) unfolding tspan_def by (intro allI impI, case_tac "w = y") auto
qed

lemma thrdstep_cong:
  "\<lbrakk>ds_thrd s = ds_thrd t; ds_seen s = ds_seen t\<rbrakk> \<Longrightarrow> thrdstep s = thrdstep t"
  by (simp add: thrdstep_def)

lemma tspan_cong: "\<lbrakk>ds_thrd s = ds_thrd t; ds_seen s = ds_seen t\<rbrakk> \<Longrightarrow> tspan s = tspan t"
  by (simp add: tspan_def thrdstep_def)

lemma dfs_finish_tspan: "tspan s \<Longrightarrow> tspan (dfs_finish s v rest)"
  by (rule tspan_cong[THEN iffD1, rotated -1]) (simp_all add: dfs_finish_def Let_def)

lemma emit_U_edge_tspan: "tspan s \<Longrightarrow> tspan (emit_U_edge s v)"
  by (rule tspan_cong[THEN iffD1, rotated -1]) (simp_all add: emit_U_edge_def Let_def)

lemma bd_upd1_tspan:
  assumes "dfs_inv fl s" "tspan s" "bd_call1_conds fl s"
  shows "tspan (bd_upd1 fl s)"
proof-
  have "dfs_wf fl s" using assms(1) by (simp add: dfs_inv_def)
  then obtain v rest e w c' where "ds_stk s = v # rest" "e < m" "snd_list ! e = w" "w < vcount"
    "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr> else dfs_discover
        (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    using assms(3) by (rule bd_upd1_eq)
  then show ?thesis
    using assms(1,2) snd_list_nz tspan_cong[of "s\<lparr>ds_oc := c'\<rparr>" s]
      tspan_append[of fl s w "dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e"]
    by (auto simp: dfs_discover_def dfs_push_def Let_def)
qed

lemma bd_upd2_tspan:
  assumes "dfs_inv fl s" "tspan s" "bd_call2_conds fl s"
  shows "tspan (bd_upd2 fl s)"
proof-
  have "dfs_wf fl s" using assms(1) by (simp add: dfs_inv_def)
  then obtain v rest e w c' where "ds_stk s = v # rest" "e < m" "fst_list ! e = w" "w < vcount"
    "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr> else dfs_discover
        (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    using assms(3) by (rule bd_upd2_eq)
  then show ?thesis
    using assms(1,2) fst_list_nz tspan_cong[of "s\<lparr>ds_ic := c'\<rparr>" s]
      tspan_append[of fl s w "dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e"]
    by (auto simp: dfs_discover_def dfs_push_def Let_def)
qed

lemma bd_upd3_tspan: "\<lbrakk>tspan s; bd_call3_conds fl s\<rbrakk> \<Longrightarrow> tspan (bd_upd3 s)"
  by (erule bd_upd3_eq) (simp add: dfs_finish_tspan)

text \<open>Every state invariant that the three DFS steps preserve (under @{const dfs_inv}) survives a whole
      @{const build_dfs} run, and every invariant that both phase steps preserve survives the two phases.\<close>

lemma build_dfs_preserve:
  assumes "build_dfs_dom (fl, s)" "dfs_inv fl s" "Q s"
    "\<And>fl s. \<lbrakk>dfs_inv fl s; Q s; bd_call1_conds fl s\<rbrakk> \<Longrightarrow> Q (bd_upd1 fl s)"
    "\<And>fl s. \<lbrakk>dfs_inv fl s; Q s; bd_call2_conds fl s\<rbrakk> \<Longrightarrow> Q (bd_upd2 fl s)"
    "\<And>fl s. \<lbrakk>dfs_inv fl s; Q s; bd_call3_conds fl s\<rbrakk> \<Longrightarrow> Q (bd_upd3 s)"
  shows "Q (build_dfs fl s)"
  using assms(1-3)
proof(induct rule: bd_induct[consumes 1])
  case IH: (1 fl s)
  show ?case
    by (rule bd_cases[where s = s and fl = fl])
      (auto intro!: IH(2-4) bd_upd1_inv bd_upd2_inv bd_upd3_inv assms(4-6) IH(5,6) simp: bd_simps[OF IH(1)])
qed

lemma phases_preserve:
  assumes "Q dfs_init"
    "\<And>v s. \<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s \<and> ds_stk s = []; Q s\<rbrakk>
      \<Longrightarrow> Q (phase1_step acyc_flow v s)"
    "\<And>v s. \<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s \<and> ds_stk s = []; Q s\<rbrakk>
      \<Longrightarrow> Q (phase2_step acyc_flow v s)"
  shows "Q (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
proof-
  let ?P = "\<lambda>s. (dfs_inv acyc_flow s \<and> ds_stk s = []) \<and> Q s"
  have "?P (phase1 acyc_flow dfs_init)"
    unfolding phase1_def
    by (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = ?P])
      (use dfs_init_inv assms(1) in \<open>simp_all add: dfs_init_def phase1_step_inv assms(2)\<close>)
  then have "?P (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
    unfolding phase2_def
    by (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = ?P, rotated])
      (simp_all add: phase2_step_inv assms(3))
  then show ?thesis by simp
qed

lemma build_dfs_tspan:
  "\<lbrakk>build_dfs_dom (fl, s); dfs_inv fl s; tspan s\<rbrakk> \<Longrightarrow> tspan (build_dfs fl s)"
  by (rule build_dfs_preserve) (auto intro: bd_upd1_tspan bd_upd2_tspan bd_upd3_tspan)

lemma open_tree_component_tspan:
  "\<lbrakk>dfs_inv acyc_flow s; tspan s; c < vcount; \<not> ds_seen s ! c; c \<noteq> 0; ds_stk s = []\<rbrakk>
    \<Longrightarrow> tspan (open_tree_component acyc_flow s c)"
  by (rule open_tree_component_seed[of acyc_flow s c])
    (auto simp: dfs_inv_def[of acyc_flow s]
      intro!: build_dfs_tspan tspan_append[where fl = acyc_flow and s = s and w = c])

lemma dfs_init_tspan: "tspan dfs_init"
  by (auto simp: tspan_def thrdstep_def dfs_init_def simp del: replicate_Suc)

lemma phase1_step_tspan:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s \<and> ds_stk s = []; tspan s\<rbrakk>
    \<Longrightarrow> tspan (phase1_step acyc_flow v s)"
  using vs_less_vcount no_zero_node emit_U_edge_tspan open_tree_component_tspan[of s v]
  by (auto simp: phase1_step_def)

lemma phase2_step_tspan:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s \<and> ds_stk s = []; tspan s\<rbrakk>
    \<Longrightarrow> tspan (phase2_step acyc_flow v s)"
  using vs_less_vcount no_zero_node open_tree_component_tspan[of s v] by (auto simp: phase2_step_def)

lemma build_tree_tspan: "tspan (build_tree acyc_flow)"
  using phases_preserve[where Q = tspan, OF dfs_init_tspan phase1_step_tspan phase2_step_tspan]
  by (rule tspan_cong[THEN iffD1, rotated 2]) (simp_all add: build_tree_def Let_def)

subsection \<open>The thread relation is single-valued, injective, and (with spanning) acyclic\<close>

lemma thrdstep_single_valued: "single_valued (thrdstep (build_tree acyc_flow))"
  by (auto simp: single_valued_def thrdstep_def)

lemma thrdstepD:
  assumes "(x, z) \<in> thrdstep s"
  shows "z = ds_thrd s ! x" and "x < Suc vcount" and "x = vcount \<or> ds_seen s ! x" and "ds_thrd s ! x \<noteq> 0"
  using assms by (simp_all add: thrdstep_def)

lemma thrdstep_rvth:
  "(x, z) \<in> thrdstep (build_tree acyc_flow) \<Longrightarrow> ds_rvth (build_tree acyc_flow) ! z = x"
  using build_tree_thrd_prev0
  by (cases "x = ds_prev (build_tree acyc_flow)") (auto simp: thrdstep_iff build_tree_thread_inverse)

lemma thrdstep_inj: "single_valued ((thrdstep (build_tree acyc_flow))\<inverse>)"
  by (auto simp: single_valued_def dest!: thrdstep_rvth)

lemma vcount_notin_range: "vcount \<notin> Range (thrdstep (build_tree acyc_flow))"
proof
  assume "vcount \<in> Range (thrdstep (build_tree acyc_flow))"
  then obtain x where "(x, vcount) \<in> thrdstep (build_tree acyc_flow)" by blast
  moreover from this have "x = 0" using build_tree_root_no_pred[of acyc_flow] by (auto dest: thrdstep_rvth)
  moreover have "vcount \<noteq> 0" "\<not> ds_seen (build_tree acyc_flow) ! 0"
    using build_tree_thread_inv[of acyc_flow] by (simp_all add: vcount_def thread_inv_def)
  ultimately show False by (simp add: thrdstep_iff)
qed

lemma thrdstep_acyclic: "acyclic (thrdstep (build_tree acyc_flow))"
  unfolding acyclic_def
proof(intro allI notI)
  fix x assume cyc: "(x, x) \<in> (thrdstep (build_tree acyc_flow))\<^sup>+"
  then have r: "(vcount, x) \<in> (thrdstep (build_tree acyc_flow))\<^sup>*"
    using build_tree_tspan build_tree_root_unseen[of acyc_flow]
    by (auto simp: tspan_def thrdstep_iff less_Suc_eq dest!: tranclD)
  with cyc have "(x, vcount) \<in> (thrdstep (build_tree acyc_flow))\<^sup>*"
    using orbit_returns[OF thrdstep_inj, of x vcount] by (simp add: rtrancl_converse trancl_converse)
  then have "(vcount, vcount) \<in> (thrdstep (build_tree acyc_flow))\<^sup>+"
    by (rule trancl_rtrancl_trancl[OF rtrancl_trancl_trancl[OF r cyc]])
  then show False using vcount_notin_range by (auto dest: tranclD2)
qed

lemma thrdstep_finite: "finite (thrdstep (build_tree acyc_flow))"
  by (rule finite_subset[of _ "(\<lambda>x. (x, ds_thrd (build_tree acyc_flow) ! x)) ` {..<Suc vcount}"])
    (auto simp: thrdstep_def)

subsection \<open>Thread parent maps: @{const parent_spec}, spanning, domains, and the thread/rev-thread
  inverse\<close>

lemma thrdstep_eq_Sthrd: "thrdstep (build_tree acyc_flow) = {(x, y) |x y. Some y = Sthrd x}"
  by (auto simp: thrdstep_def Sthrd_def Varb_def Vseen_def split: if_splits)

lemma parent_spec_Sthrd: "parent_spec Sthrd"
proof-
  have "{(x, y) |x y. Some x = Sthrd y} = (thrdstep (build_tree acyc_flow))\<inverse>" using thrdstep_eq_Sthrd by auto
  then show ?thesis
    unfolding parent_spec_def using finite_acyclic_wf_converse[OF thrdstep_finite thrdstep_acyclic] by simp
qed

lemma follow_Sthrd_thrdstep: "set (follow Sthrd u) = {z. (u, z) \<in> (thrdstep (build_tree acyc_flow))\<^sup>*}"
proof-
  have "{(x, y). Sthrd x = Some y} = thrdstep (build_tree acyc_flow)" using thrdstep_eq_Sthrd by auto
  then show ?thesis using follow_set_rtrancl[OF parent_spec_Sthrd, of u] by simp
qed

lemma vcount_nz: "vcount \<noteq> 0"
  by (simp add: vcount_def)

lemma build_tree_seen0: "\<not> ds_seen (build_tree acyc_flow) ! 0"
  using build_tree_thread_inv by (simp add: thread_inv_def)

lemma build_tree_seen_pos: "ds_seen (build_tree acyc_flow) ! z \<Longrightarrow> 0 < z"
  using build_tree_seen0 by (cases z) auto

lemma Varb_elem_props:
  assumes "z \<in> Varb"
  shows "z < Suc vcount" and "z = vcount \<or> ds_seen (build_tree acyc_flow) ! z" and "z \<noteq> 0"
  using assms vcount_nz by (auto simp: Varb_def Vseen_def build_tree_seen_pos)

lemma zero_notin_Varb: "0 \<notin> Varb"
  using Varb_elem_props(3) by blast

lemma build_tree_thrd_Varb:
  "\<lbrakk>x \<in> Varb; x \<noteq> ds_prev (build_tree acyc_flow)\<rbrakk> \<Longrightarrow>
    ds_thrd (build_tree acyc_flow) ! x \<in> Varb"
  by (frule Varb_elem_props(1), frule Varb_elem_props(2), frule (2) build_tree_thread_inverse(1),
      frule (2) build_tree_thread_inverse(2)) (auto simp: Varb_def Vseen_def)

lemma build_tree_rvth_Varb:
  "\<lbrakk>x \<in> Varb; x \<noteq> vcount\<rbrakk> \<Longrightarrow> ds_rvth (build_tree acyc_flow) ! x \<in> Varb"
  by (frule Varb_elem_props(1), frule Varb_elem_props(2), frule (2) build_tree_rev_thread_inverse(1),
      frule (2) build_tree_rev_thread_inverse(2)) (auto simp: Varb_def Vseen_def)

lemma thrdstep_Varb: "(x, z) \<in> thrdstep (build_tree acyc_flow) \<Longrightarrow> x \<in> Varb \<and> z \<in> Varb"
proof-
  assume "(x, z) \<in> thrdstep (build_tree acyc_flow)"
  moreover from this have "x \<in> Varb" "x \<noteq> ds_prev (build_tree acyc_flow)"
    using build_tree_thrd_prev0 by (auto simp: thrdstep_iff Varb_def Vseen_def less_Suc_eq)
  ultimately show ?thesis by (simp add: thrdstep_iff build_tree_thrd_Varb)
qed

lemma thrdstep_reach_Varb: "(vcount, z) \<in> (thrdstep (build_tree acyc_flow))\<^sup>* \<Longrightarrow> z \<in> Varb"
  by (induction rule: rtrancl_induct) (auto simp: r_in_V dest: thrdstep_Varb)

lemma follow_Sthrd_spans: "set (follow Sthrd vcount) = Varb"
  using thrdstep_reach_Varb build_tree_tspan by (auto simp: follow_Sthrd_thrdstep tspan_def Varb_def Vseen_def)

lemma Varb_rvth_thrdstep:
  "\<lbrakk>y \<in> Varb; ds_rvth (build_tree acyc_flow) ! y \<noteq> 0\<rbrakk> \<Longrightarrow>
    (ds_rvth (build_tree acyc_flow) ! y, y) \<in> thrdstep (build_tree acyc_flow)"
  using build_tree_root_no_pred[of acyc_flow]
  by (cases "y = vcount")
    (auto simp: thrdstep_iff build_tree_rev_thread_inverse Varb_def Vseen_def build_tree_seen_pos)

lemma Srvth_rel_eq: "{(x, y) |x y. Some x = Srvth y} = thrdstep (build_tree acyc_flow)"
proof(intro equalityI subsetI)
  fix p assume "p \<in> {(x, y) |x y. Some x = Srvth y}"
  then show "p \<in> thrdstep (build_tree acyc_flow)"
    by (auto simp: Srvth_def intro: Varb_rvth_thrdstep split: if_splits)
next
  fix p assume "p \<in> thrdstep (build_tree acyc_flow)"
  moreover obtain x y where "p = (x, y)" by fastforce
  ultimately show "p \<in> {(x, y) |x y. Some x = Srvth y}"
    using thrdstep_Varb[of x y] thrdstep_rvth[of x y] Varb_elem_props(3)[of x] by (auto simp: Srvth_def)
qed

lemma parent_spec_Srvth: "parent_spec Srvth"
  unfolding parent_spec_def Srvth_rel_eq
  by (rule finite_acyclic_wf[OF thrdstep_finite thrdstep_acyclic])

lemma lsuc_root_eq_prev: "ds_lsuc (build_tree acyc_flow) ! vcount = ds_prev (build_tree acyc_flow)"
  using build_tree_phases[of acyc_flow] by (simp add: build_tree_def Let_def dfs_inv_def dfs_sized_def)

lemma thrd_nz_of_Varb:
  "\<lbrakk>x \<in> Varb; x \<noteq> ds_prev (build_tree acyc_flow)\<rbrakk>
    \<Longrightarrow> ds_thrd (build_tree acyc_flow) ! x \<noteq> 0"
  by (rule Varb_elem_props(3)[OF build_tree_thrd_Varb])

lemma rvth_nz_of_Varb:
  "\<lbrakk>x \<in> Varb; x \<noteq> vcount\<rbrakk> \<Longrightarrow> ds_rvth (build_tree acyc_flow) ! x \<noteq> 0"
  by (rule Varb_elem_props(3)[OF build_tree_rvth_Varb])

lemma dom_Sthrd: "dom Sthrd = Varb - {ds_prev (build_tree acyc_flow)}"
  by (auto simp: Sthrd_def dom_def build_tree_thrd_prev0 intro: thrd_nz_of_Varb[simplified] split: if_splits)

lemma dom_Srvth: "dom Srvth = Varb - {vcount}"
  using build_tree_root_no_pred[of acyc_flow]
  by (auto simp: Srvth_def dom_def intro: rvth_nz_of_Varb[simplified] split: if_splits)

lemma thrd_rvth_inverse: "\<forall>v v'. Sthrd v = Some v' \<longleftrightarrow> Srvth v' = Some v"
proof(intro allI)
  fix v v'
  have "Sthrd v = Some v' \<longleftrightarrow> (v, v') \<in> thrdstep (build_tree acyc_flow)"
    unfolding thrdstep_eq_Sthrd by (simp add: eq_commute)
  moreover have "Srvth v' = Some v \<longleftrightarrow> (v, v') \<in> thrdstep (build_tree acyc_flow)"
    unfolding Srvth_rel_eq[symmetric] by (simp add: eq_commute)
  ultimately show "Sthrd v = Some v' \<longleftrightarrow> Srvth v' = Some v" by simp
qed

lemma prev_in_Varb: "ds_prev (build_tree acyc_flow) \<in> Varb"
  using build_tree_thread_inv[of acyc_flow] by (auto simp: thread_inv_def Varb_def Vseen_def less_Suc_eq)

lemma lsuc_in_V_all: "v \<in> Varb \<Longrightarrow> lsuc Sarb v \<in> Varb"
  using lsuc_in_V lsuc_root_eq_prev prev_in_Varb by (cases "v = vcount") (auto simp: Sarb_sel Varb_def)

subsection \<open>Edge-set spanning: obligation 1 completed (@{const dVs})\<close>

text \<open>The remaining ingredient of @{const rooted_arborescense_invar} is that the parent edges span the
      vertex set. The @{term fst} projection of the edge set is exactly @{term Vseen} (the domain of
      @{term Sprnt}); the @{term snd} projection is the set of stored parents, each of which is either
      @{term vcount} or a seen vertex. The graph has at least one edge (@{thm num_edges_gtr_0}), hence at
      least one real vertex, so @{term Vseen} is non-empty and --- following any parent chain to the root ---
      some component root has @{term vcount} as its parent, putting @{term vcount} into the edge set.\<close>

lemma Vseen_nonempty: "Vseen \<noteq> {}"
proof-
  have "fst_list ! 0 \<in> set fst_list" using length_fst length_edges num_edges_gtr_0 by simp
  moreover from this have "fst_list ! 0 \<in> set vs_list" using fst_snd_vs by auto
  ultimately have "fst_list ! 0 \<in> Vseen" by (simp add: Vseen_def vs_less_vcount build_tree_spans edged_not_lonely)
  then show ?thesis by blast
qed

lemma exists_root_child: "\<exists>z. z \<in> Vseen \<and> ds_prnt (build_tree acyc_flow) ! z = vcount"
proof-
  obtain u where "u \<in> Vseen" using Vseen_nonempty by blast
  then have "(u, vcount) \<in> (pstep (build_tree acyc_flow))\<^sup>+"
    using build_tree_reaches_root by (auto simp: Vseen_def rtrancl_eq_or_trancl)
  then obtain z where "(z, vcount) \<in> pstep (build_tree acyc_flow)" by (blast dest: tranclD2)
  then show ?thesis by (auto simp: Vseen_def pstep_def)
qed

lemma dVs_Sprnt: "dVs {(y, x) |x y. Some x = Sprnt y} = Varb"
proof-
  have "{(y, x) |x y. Some x = Sprnt y} = (\<lambda>y. (y, ds_prnt (build_tree acyc_flow) ! y)) ` Vseen"
    by (auto simp: Sprnt_def split: if_splits)
  moreover obtain z where "z \<in> Vseen" "ds_prnt (build_tree acyc_flow) ! z = vcount"
    using exists_root_child by blast
  ultimately show ?thesis
    using build_tree_parent_in_seen[of _ acyc_flow]
    by (auto simp: dVs_eq image_image Varb_def Vseen_def intro: rev_image_eqI)
qed

text \<open>Obligation 1 assembled: @{term Sprnt} is a rooted arborescence on @{term Varb}.\<close>

lemma rooted_arb_invar_Sprnt: "rooted_arborescense_invar vcount Varb Sprnt"
  by (rule rooted_arborescense_invarI) (simp_all add: parent_spec_Sprnt r_in_V dom_Sprnt dVs_Sprnt)

subsection \<open>Clause J: obligation 10 (preorder contiguity of the thread blocks)\<close>

text \<open>The tenth @{const arb_invar} obligation says the thread @{term \<open>follow Sthrd v\<close>} starts with a
      non-empty contiguous block whose set is @{term v}'s subtree and whose last element is
      @{term \<open>lsuc Sarb v\<close>}, after which the thread continues at
      @{term \<open>thrd Sarb (lsuc Sarb v)\<close>}. We feed the generic @{thm preorder_contiguous} engine with the
      array-level DFS order (@{thm build_tree_emit_order}, lifted to abstract @{const follow} through
      @{thm thrd_rvth_inverse} and @{thm follow_Sprnt_pstep}); it returns the block as a prefix headed by @{term v},
      and @{thm build_tree_lsuc} (block-last) pins its last element to @{term \<open>lsuc Sarb v\<close>}, whence the
      suffix shape follows.\<close>

lemma last_of_prefix_Sthrd:
  assumes "follow Sthrd v = pre @ suf" "L \<in> set pre"
    "case Sthrd L of None \<Rightarrow> True | Some w \<Rightarrow> w \<notin> set pre"
  shows "L = last pre"
proof(rule ccontr)
  assume "L \<noteq> last pre"
  moreover obtain p1 p2 where "pre = p1 @ L # p2" using assms(2) by (blast dest: split_list)
  ultimately obtain w p3 where pre: "pre = p1 @ L # w # p3" by (cases p2) auto
  have "follow Sthrd L = L # w # p3 @ suf"
    by (rule follow_append_ps[OF parent_spec_Sthrd, of v p1]) (use assms(1) pre in simp)
  then have "Sthrd L = Some w"
    by (cases "Sthrd L")
      (auto simp: follow_None_ps follow_Some_ps follow_hd_ps parent_spec_Sthrd dest: arg_cong[where f = hd])
  with assms(3) pre show False by simp
qed

lemma emit_dfs_premise:
  assumes "Suc t < length (follow Sthrd vcount)"
  shows "\<exists>a. Sprnt (follow Sthrd vcount ! Suc t) = Some a
    \<and> a \<in> set (follow Sprnt (follow Sthrd vcount ! t))"
proof-
  let ?u = "follow Sthrd vcount ! t" and ?w = "follow Sthrd vcount ! Suc t"
  have "Srvth ?w = Some ?u" using follow_nth_Suc[OF parent_spec_Sthrd assms] thrd_rvth_inverse by blast
  then have "?w \<in> Vseen" "ds_rvth (build_tree acyc_flow) ! ?w = ?u"
    using build_tree_root_no_pred[of acyc_flow] by (auto simp: Srvth_def Varb_def split: if_splits)
  then show ?thesis
    using build_tree_emit_order[of ?w acyc_flow] by (auto simp: Sprnt_def Vseen_def follow_Sprnt_pstep)
qed

lemma children_sub_Varb: "v \<in> Varb \<Longrightarrow> children Sprnt v \<subseteq> Varb"
  by (auto simp: children_def follow_Sprnt_pstep Varb_def Vseen_def pstep_def elim: converse_rtranclE)

lemma lsuc_in_children:
  assumes "v \<in> Varb" shows "lsuc Sarb v \<in> children Sprnt v"
proof(cases "v = vcount")
  case True
  then show ?thesis
    using prev_in_Varb build_tree_reaches_root[of "ds_prev (build_tree acyc_flow)" acyc_flow]
    by (auto simp: Sarb_sel lsuc_root_eq_prev children_def follow_Sprnt_pstep Varb_def Vseen_def)
next
  case False
  with assms show ?thesis
    using build_tree_lsuc[of v acyc_flow] children_Sprnt_desc[of v] by (auto simp: Sarb_sel Varb_def Vseen_def)
qed

lemma thrd_lsuc_out:
  assumes "v \<in> Varb"
  shows "case Sthrd (lsuc Sarb v) of None \<Rightarrow> True | Some w \<Rightarrow> w \<notin> children Sprnt v"
proof(cases "v = vcount")
  case True
  then show ?thesis by (simp add: Sarb_sel lsuc_root_eq_prev build_tree_thrd_prev0 Sthrd_def)
next
  case False
  with assms show ?thesis
    using build_tree_lsuc[of v acyc_flow] children_Sprnt_desc[of v]
    by (auto simp: Sarb_sel Sthrd_def Varb_def Vseen_def split: option.splits if_splits)
qed

lemma clause_J:
  assumes "v \<in> Varb"
  shows "\<exists>pre. follow Sthrd v
      = pre @ (case Sthrd (lsuc Sarb v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow Sthrd w)
             \<and> pre \<noteq> [] \<and> last pre = lsuc Sarb v \<and> set pre = children Sprnt v"
proof-
  have N: "Sprnt (follow Sthrd vcount ! 0) = None"
    using follow_ne_ps[OF parent_spec_Sthrd, of vcount] follow_hd_ps[OF parent_spec_Sthrd, of vcount]
    by (simp add: hd_conv_nth Sprnt_def Vseen_def)
  have V: "v \<in> set (follow Sthrd vcount)" "children Sprnt v \<subseteq> set (follow Sthrd vcount)"
    using assms children_sub_Varb[of v] by (simp_all add: follow_Sthrd_spans)
  obtain pre suf where R: "follow Sthrd v = pre @ suf" "set pre = children Sprnt v" "pre \<noteq> []"
    using preorder_contiguous[OF parent_spec_Sprnt parent_spec_Sthrd refl N emit_dfs_premise V] by auto
  moreover have "lsuc Sarb v = last pre"
    by (rule last_of_prefix_Sthrd[OF R(1)])
      (use assms lsuc_in_children[of v] thrd_lsuc_out[of v] R(2) in \<open>simp_all split: option.splits\<close>)
  moreover obtain pre' L where "pre = pre' @ [L]" using R(3) by (cases pre rule: rev_cases) auto
  moreover have "follow Sthrd L = L # suf"
    by (rule follow_append_ps[OF parent_spec_Sthrd, of v pre']) (use R(1) \<open>pre = pre' @ [L]\<close> in simp)
  ultimately show ?thesis
    using follow_ps_simps[OF parent_spec_Sthrd, of L] by (auto intro!: exI[of _ pre] split: option.splits)
qed

subsection \<open>Root subtree size: obligation 9 at the root (@{const ds_snum} accumulation)\<close>

text \<open>The subtree-size obligation for interior vertices is @{thm snum_eq_children}; the root case needs
      @{term \<open>ds_snum (build_tree acyc_flow) ! vcount = card Varb\<close>}, which @{const snum_inv} does not
      track (it ranges over \<open>v < vcount\<close>). We carry a dedicated invariant @{term rootacc} through the
      whole build (mirroring the @{const tspan} carry): at every state,
      @{term \<open>Suc (card (seen vertices))\<close>} equals the root's running count plus the subtree size of the
      \<^emph>\<open>bottom\<close> (component-root) stack frame --- the vertices of the currently-open component, not
      yet added to the root. A discovery grows both sides by one (the fresh vertex joins the bottom frame's subtree via
      @{thm stk_top_reaches} / @{thm desc_discover}); finishing a component root adds its size to the root; opening a
      component reseeds the bottom frame. At @{const build_tree} the stack is empty, so the bottom term is @{term 0}
      and the root count is the whole tree.\<close>

definition rootacc :: "'n dfs_state \<Rightarrow> bool" where
  "rootacc s \<longleftrightarrow> Suc (card {y. y < vcount \<and> ds_seen s ! y})
     = ds_snum s ! vcount + (if ds_stk s = [] then 0 else dcard s (last (ds_stk s)))"

lemma dfs_init_rootacc: "rootacc dfs_init"
  by (auto simp: rootacc_def dfs_init_def simp del: replicate_Suc)

lemma rootacc_discover_core:
  "\<lbrakk>rootacc s; {y. y < vcount \<and> ds_seen t ! y} = insert w {y. y < vcount \<and> ds_seen s ! y};
    w < vcount; \<not> ds_seen s ! w; ds_snum t ! vcount = ds_snum s ! vcount; ds_stk t \<noteq> []; ds_stk s \<noteq> [];
    last (ds_stk t) = last (ds_stk s); dcard t (last (ds_stk s)) = Suc (dcard s (last (ds_stk s)))\<rbrakk>
    \<Longrightarrow> rootacc t"
  by (simp add: rootacc_def)

lemma rootacc_append:
  assumes "dfs_inv fl s" "rootacc s" "ds_stk s = v0 # rest" "w < vcount" "\<not> ds_seen s ! w"
    "ds_seen t = (ds_seen s)[w := True]" "ds_prnt t = (ds_prnt s)[w := v0]" "ds_snum t = (ds_snum s)[w := 1]"
    "ds_stk t = w # v0 # rest"
  shows "rootacc t"
proof-
  have R: "dfs_wf fl s" "tree_seen_inv s" "stk_prnt_inv s" "length (ds_seen s) = Suc vcount"
    "length (ds_prnt s) = Suc vcount" "length (ds_snum s) = Suc vcount"
    using assms(1) by (auto simp: dfs_inv_def dfs_sized_def)
  then have "ds_seen s ! v0" "(v0, last (ds_stk s)) \<in> (pstep s)\<^sup>*"
    using assms(3) stkverts_props[of fl s v0] stk_top_reaches[of s fl v0 rest "last (ds_stk s)"]
    by (auto simp: stkverts_def)
  with R assms(4-7) have "desc t (last (ds_stk s)) = insert w (desc s (last (ds_stk s)))"
    using desc_discover[of s w v0 t "last (ds_stk s)"] by auto
  with R assms show ?thesis
    by (intro rootacc_discover_core[of s t w]) (auto simp: nth_list_update dcard_def desc_finite desc_def)
qed

lemma rootacc_cong:
  "\<lbrakk>ds_seen t = ds_seen s; ds_snum t = ds_snum s; ds_prnt t = ds_prnt s; ds_stk t = ds_stk s\<rbrakk>
    \<Longrightarrow> rootacc t = rootacc s"
  by (simp add: rootacc_def dcard_def desc_def pstep_def)

lemma emit_U_edge_rootacc: "rootacc s \<Longrightarrow> rootacc (emit_U_edge s v)"
  by (rule rootacc_cong[THEN iffD2, rotated -1]) (simp_all add: emit_U_edge_def Let_def)

lemma bd_upd3_rootacc:
  assumes "dfs_inv fl s" "rootacc s" "bd_call3_conds fl s"
  shows "rootacc (bd_upd3 s)"
proof-
  obtain v rest where "ds_stk s = v # rest" "bd_upd3 s = dfs_finish s v rest" using assms(3) by (rule bd_upd3_eq)
  moreover from this have "vchain (ds_prnt s) (v # rest)" "dcard s v = ds_snum s ! v"
    "length (ds_snum s) = Suc vcount" "\<forall>g \<in> set rest. g < vcount"
    using assms(1) stkverts_props[of fl s]
    by (auto simp: dfs_inv_def stk_prnt_inv_def snum_inv_def dfs_sized_def stkverts_def)
  ultimately show ?thesis
    using assms(2)
    by (cases rest) (auto simp: rootacc_def dfs_finish_def Let_def dcard_def desc_def pstep_def nth_list_update)
qed

lemma bd_upd1_rootacc:
  assumes "dfs_inv fl s" "rootacc s" "bd_call1_conds fl s"
  shows "rootacc (bd_upd1 fl s)"
proof-
  have "dfs_wf fl s" using assms(1) by (simp add: dfs_inv_def)
  then obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount"
    "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr> else dfs_discover
        (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    using assms(3) by (rule bd_upd1_eq)
  then show ?thesis
    using assms(1,2) rootacc_cong[of "s\<lparr>ds_oc := c'\<rparr>" s]
      rootacc_append[of fl s v rest w "dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e"]
    by (auto simp: dfs_discover_def dfs_push_def Let_def)
qed

lemma bd_upd2_rootacc:
  assumes "dfs_inv fl s" "rootacc s" "bd_call2_conds fl s"
  shows "rootacc (bd_upd2 fl s)"
proof-
  have "dfs_wf fl s" using assms(1) by (simp add: dfs_inv_def)
  then obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount"
    "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr> else dfs_discover
        (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    using assms(3) by (rule bd_upd2_eq)
  then show ?thesis
    using assms(1,2) rootacc_cong[of "s\<lparr>ds_ic := c'\<rparr>" s]
      rootacc_append[of fl s v rest w "dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e"]
    by (auto simp: dfs_discover_def dfs_push_def Let_def)
qed

lemma build_dfs_rootacc:
  "\<lbrakk>build_dfs_dom (fl, s); dfs_inv fl s; rootacc s\<rbrakk> \<Longrightarrow> rootacc (build_dfs fl s)"
  by (rule build_dfs_preserve) (auto intro: bd_upd1_rootacc bd_upd2_rootacc bd_upd3_rootacc)

lemma rootacc_seed:
  assumes "dfs_inv acyc_flow s" "rootacc s" "ds_stk s = []" "c < vcount" "\<not> ds_seen s ! c"
    "ds_seen t = (ds_seen s)[c := True]" "ds_prnt t = (ds_prnt s)[c := vcount]" "ds_snum t = (ds_snum s)[c := 1]"
    "ds_stk t = [c]"
  shows "rootacc t"
proof-
  have R: "tree_seen_inv s" "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
    using assms(1) by (auto simp: dfs_inv_def dfs_sized_def)
  then have "desc t c = {c}" "{y. y < vcount \<and> ds_seen t ! y} = insert c {y. y < vcount \<and> ds_seen s ! y}"
    using assms(4-7) desc_discover[of s c vcount t c] desc_fresh_empty[of s c] by (auto simp: nth_list_update)
  with assms(2-5,8,9) show ?thesis by (simp add: rootacc_def dcard_def nth_list_update)
qed

lemma open_tree_component_rootacc:
  "\<lbrakk>dfs_inv acyc_flow s; rootacc s; c < vcount; \<not> ds_seen s ! c; c \<noteq> 0; ds_stk s = []\<rbrakk>
    \<Longrightarrow> rootacc (open_tree_component acyc_flow s c)"
  by (rule open_tree_component_seed[of acyc_flow s c])
    (auto simp: dfs_inv_def[of acyc_flow s] intro!: build_dfs_rootacc rootacc_seed[where s = s and c = c])

lemma phase1_step_rootacc:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s \<and> ds_stk s = []; rootacc s\<rbrakk>
    \<Longrightarrow> rootacc (phase1_step acyc_flow v s)"
  using vs_less_vcount no_zero_node emit_U_edge_rootacc open_tree_component_rootacc[of s v]
  by (auto simp: phase1_step_def)

lemma phase2_step_rootacc:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s \<and> ds_stk s = []; rootacc s\<rbrakk>
    \<Longrightarrow> rootacc (phase2_step acyc_flow v s)"
  using vs_less_vcount no_zero_node open_tree_component_rootacc[of s v] by (auto simp: phase2_step_def)

lemma build_tree_rootacc: "rootacc (build_tree acyc_flow)"
  using phases_preserve[where Q = rootacc, OF dfs_init_rootacc phase1_step_rootacc phase2_step_rootacc]
  by (rule rootacc_cong[THEN iffD2, rotated 4]) (simp_all add: build_tree_def Let_def)

lemma build_tree_root_snum: "ds_snum (build_tree acyc_flow) ! vcount = card Varb"
  using build_tree_rootacc build_tree_stk_empty by (simp add: rootacc_def Varb_def Vseen_def)

lemma children_Sprnt_root: "children Sprnt vcount = Varb"
  using children_sub_Varb[OF r_in_V] build_tree_reaches_root[of _ acyc_flow]
  by (auto simp: children_def follow_Sprnt_pstep Varb_def Vseen_def)

lemma snum_eq_children_all: "v \<in> Varb \<Longrightarrow> snum Sarb v = card (children (prnt Sarb) v)"
  using snum_eq_children build_tree_root_snum children_Sprnt_root
  by (cases "v = vcount") (auto simp: Sarb_sel Varb_def)

subsection \<open>The complete @{const arb_invar} assembly\<close>

text \<open>All ten obligations of @{thm arb_invarI} now discharged: @{term Sarb} is a valid threaded rooted
      arborescence on @{term Varb} with root @{term vcount}.\<close>

lemma arb_invar_Sarb: "arb_invar vcount Varb Sarb"
  using clause_J lsuc_in_V_all snum_eq_children_all
  by (intro arb_invarI, unfold Sarb_sel(1-4))
    (auto simp: rooted_arb_invar_Sprnt parent_spec_Sthrd parent_spec_Srvth follow_Sthrd_spans dom_Sthrd dom_Srvth
      thrd_rvth_inverse lsuc_root_eq_prev)

subsection \<open>Assembly substrate: the DFS body leaves the artificial-edge tails untouched\<close>

text \<open>Towards the @{const network_simplex_init} obligations for the constructed basis: the artificial-edge tails
      (@{const ds_afst} / @{const ds_asnd} / @{const ds_acap} / @{const ds_aflw} / @{const ds_aest}) and the cursor
      @{const ds_nxt} are written only by @{const open_tree_component} / @{const emit_U_edge}; the traversal
      @{const build_dfs} preserves them. This is the base for characterising which artificial edges the build emits
      (needed by \<open>init_bflow\<close> / \<open>init_partition\<close> / \<open>init_flow_fits\<close>).\<close>

abbreviation art_same :: "'n dfs_state \<Rightarrow> 'n dfs_state \<Rightarrow> bool" where
  "art_same t s \<equiv> ds_nxt t = ds_nxt s \<and> ds_afst t = ds_afst s \<and> ds_asnd t = ds_asnd s
     \<and> ds_acap t = ds_acap s \<and> ds_aflw t = ds_aflw s \<and> ds_aest t = ds_aest s"

lemma bd_upd1_art: "bd_call1_conds fl s \<Longrightarrow> art_same (bd_upd1 fl s) s"
  by (auto simp: bd_upd1_def bd_call1_conds_def dfs_discover_def dfs_push_def Let_def split: list.splits)

lemma bd_upd2_art: "bd_call2_conds fl s \<Longrightarrow> art_same (bd_upd2 fl s) s"
  by (auto simp: bd_upd2_def bd_call2_conds_def dfs_discover_def dfs_push_def Let_def split: list.splits)

lemma bd_upd3_art: "bd_call3_conds fl s \<Longrightarrow> art_same (bd_upd3 s) s"
  by (erule bd_upd3_eq) (simp add: dfs_finish_def Let_def)

lemma build_dfs_art: "build_dfs_dom (fl, s) \<Longrightarrow> art_same (build_dfs fl s) s"
proof(induct rule: bd_induct[consumes 1])
  case IH: (1 fl s)
  show ?case
    by (rule bd_cases[where s = s and fl = fl])
      (auto simp: bd_simps[OF IH(1)] bd_ret_conds_def IH(2-4) bd_upd1_art bd_upd2_art bd_upd3_art)
qed

text \<open>So opening a component writes exactly its own artificial edge, at the cursor.\<close>

lemma open_tree_component_art:
  assumes "dfs_inv fl s" "c < vcount"
  shows "ds_nxt (open_tree_component fl s c) = Suc (ds_nxt s)"
    and "ds_afst (open_tree_component fl s c) = (ds_afst s)[ds_nxt s := (if art_dir c then c else vcount)]"
    and "ds_asnd (open_tree_component fl s c) = (ds_asnd s)[ds_nxt s := (if art_dir c then vcount else c)]"
    and "ds_acap (open_tree_component fl s c) = (ds_acap s)[ds_nxt s := art_tree_cap c]"
    and "ds_aflw (open_tree_component fl s c) = (ds_aflw s)[ds_nxt s := art_flow c]"
    and "ds_aest (open_tree_component fl s c) = (ds_aest s)[ds_nxt s := InTree]"
  using assms dfs_inv_wf_sized[of fl s]
  by (auto elim!: open_tree_component_seed[of fl s c] dest!: build_dfs_art)

subsection \<open>Assembly substrate: the artificial-edge count is in bounds\<close>

text \<open>Each @{const open_tree_component} / @{const emit_U_edge} increments the artificial-edge cursor
      @{const ds_nxt} by exactly one and leaves its subject vertex seen; @{const build_dfs} preserves it. Since every
      vertex of @{term vs_list} is the subject of at most one emission (opened XOR emitted-as-U in phase 1, or
      opened-if-unseen in phase 2), the total number of artificial edges
      @{term \<open>ds_nxt (build_tree acyc_flow)\<close>} is at most @{term \<open>length vs_list\<close>} --- so the
      pre-sized artificial tails (length @{term \<open>length vs_list\<close>}) hold every emitted edge without
      dropping any.\<close>

lemma emit_U_edge_nxt: "ds_nxt (emit_U_edge s v) = Suc (ds_nxt s)"
  by (simp add: emit_U_edge_def Let_def)

lemma phase1_step_seen_mono:
  "\<lbrakk>dfs_inv acyc_flow s; v < vcount; ds_seen s ! x\<rbrakk>
    \<Longrightarrow> ds_seen (phase1_step acyc_flow v s) ! x"
  by (simp add: phase1_step_def emit_U_edge_def Let_def open_tree_component_seen_mono)

lemma phase1_step_nxt:
  "\<lbrakk>dfs_inv acyc_flow s; v < vcount\<rbrakk> \<Longrightarrow> ds_nxt (phase1_step acyc_flow v s) = ds_nxt s
    \<or> (ds_nxt (phase1_step acyc_flow v s) = Suc (ds_nxt s) \<and> ds_seen (phase1_step acyc_flow v s) ! v)"
  by (simp add: phase1_step_def emit_U_edge_def Let_def open_tree_component_art(1) open_tree_component_marks)

lemma phase2_step_nxt2:
  "\<lbrakk>dfs_inv acyc_flow s; v < vcount\<rbrakk> \<Longrightarrow> ds_nxt (phase2_step acyc_flow v s) = ds_nxt s
    \<or> (ds_nxt (phase2_step acyc_flow v s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! v
        \<and> ds_seen (phase2_step acyc_flow v s) ! v)"
  by (simp add: phase2_step_def open_tree_component_art(1) open_tree_component_marks)

text \<open>Fold-level emission bound (distinctness freshness, for phase 1): the number of artificial edges emitted by
      a scan over @{term vs_list} equals the cardinality of a set of \<^emph>\<open>seen\<close> @{term vs_list}
      vertices (the emission subjects), each fresh because @{term vs_list} is distinct.\<close>

lemma fold_emit_bnd:
  assumes "\<And>v t. \<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow t; ds_stk t = []\<rbrakk> \<Longrightarrow>
      dfs_inv acyc_flow (g v t) \<and> ds_stk (g v t) = []"
    "\<And>v t y. \<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow t; ds_seen t ! y\<rbrakk>
      \<Longrightarrow> ds_seen (g v t) ! y"
    "\<And>v t. \<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow t; ds_stk t = []\<rbrakk> \<Longrightarrow>
      ds_nxt (g v t) = ds_nxt t \<or> (ds_nxt (g v t) = Suc (ds_nxt t) \<and> ds_seen (g v t) ! v)"
    "distinct xs" "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
    "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "E \<inter> set xs = {}" "ds_nxt s = card E"
  shows "\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold g xs s) ! v}
    \<and> ds_nxt (fold g xs s) = card E'"
  using assms(4-11)
proof(induct xs arbitrary: s E)
  case (Cons x rest)
  have R: "x \<in> set vs_list" "dfs_inv acyc_flow (g x s)" "ds_stk (g x s) = []"
    "E \<subseteq> {v \<in> set vs_list. ds_seen (g x s) ! v}"
    using Cons.prems(2-4,6) assms(1)[of x s] assms(2)[of x s] by auto
  from assms(3)[OF R(1) Cons.prems(3,4)] show ?case
  proof
    assume "ds_nxt (g x s) = ds_nxt s"
    then show ?thesis using Cons.prems(1,2,5,7,8) Cons.hyps[OF _ _ R(2,3) _ R(4)] by simp
  next
    assume "ds_nxt (g x s) = Suc (ds_nxt s) \<and> ds_seen (g x s) ! x"
    then show ?thesis using Cons.prems(1,2,5,7,8) R Cons.hyps[OF _ _ R(2,3), of "insert x E"] by simp
  qed
qed auto

text \<open>Fold-level emission bound (seen freshness, for phase 2): here the scan only emits for
      \<^emph>\<open>unseen\<close> vertices (it opens them), so the new subject is fresh because the accumulated set
      is a set of seen vertices --- no distinctness needed, and the initial set may already meet
      @{term vs_list}.\<close>

lemma fold_emit_bnd2:
  assumes "\<And>v t. \<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow t; ds_stk t = []\<rbrakk> \<Longrightarrow>
      dfs_inv acyc_flow (g v t) \<and> ds_stk (g v t) = []"
    "\<And>v t y. \<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow t; ds_seen t ! y\<rbrakk>
      \<Longrightarrow> ds_seen (g v t) ! y"
    "\<And>v t. \<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow t; ds_stk t = []\<rbrakk> \<Longrightarrow>
      ds_nxt (g v t) = ds_nxt t
      \<or> (ds_nxt (g v t) = Suc (ds_nxt t) \<and> \<not> ds_seen t ! v \<and> ds_seen (g v t) ! v)"
    "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
    "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "ds_nxt s = card E"
  shows "\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold g xs s) ! v}
    \<and> ds_nxt (fold g xs s) = card E'"
  using assms(4-9)
proof(induct xs arbitrary: s E)
  case (Cons x rest)
  have R: "x \<in> set vs_list" "dfs_inv acyc_flow (g x s)" "ds_stk (g x s) = []"
    "E \<subseteq> {v \<in> set vs_list. ds_seen (g x s) ! v}"
    using Cons.prems(1-3,5) assms(1)[of x s] assms(2)[of x s] by auto
  from assms(3)[OF R(1) Cons.prems(2,3)] show ?case
  proof
    assume "ds_nxt (g x s) = ds_nxt s"
    then show ?thesis using Cons.prems(1,4,6) Cons.hyps[OF _ R(2,3) _ R(4)] by simp
  next
    assume B: "ds_nxt (g x s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! x \<and> ds_seen (g x s) ! x"
    with Cons.prems(5) have "x \<notin> E" by auto
    with B show ?thesis using Cons.prems(1,4,6) R Cons.hyps[OF _ R(2,3), of "insert x E"] by simp
  qed
qed auto

lemma phase1_emit:
  "\<exists>E. finite E \<and> E \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}
    \<and> ds_nxt (phase1 acyc_flow dfs_init) = card E"
  unfolding phase1_def using dfs_init_inv[of acyc_flow] distinct_vs_list
  by (intro fold_emit_bnd[where E = "{}"])
    (simp_all add: dfs_init_def phase1_step_inv phase1_step_seen_mono phase1_step_nxt vs_less_vcount)

lemma build_tree_nxt_le: "ds_nxt (build_tree acyc_flow) \<le> length vs_list"
proof-
  obtain E1 where "finite E1" "E1 \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}"
    "ds_nxt (phase1 acyc_flow dfs_init) = card E1"
    using phase1_emit by blast
  moreover have "dfs_inv acyc_flow (phase1 acyc_flow dfs_init) \<and> ds_stk (phase1 acyc_flow dfs_init) = []"
    using dfs_init_inv by (intro phase1_inv) (simp add: dfs_init_def)
  ultimately have "\<exists>E. finite E
      \<and> E \<subseteq> {v \<in> set vs_list. ds_seen (phase2 acyc_flow (phase1 acyc_flow dfs_init)) ! v}
      \<and> ds_nxt (phase2 acyc_flow (phase1 acyc_flow dfs_init)) = card E"
    unfolding phase2_def
    by (intro fold_emit_bnd2[where E = E1])
      (simp_all add: phase2_step_inv phase2_step_seen_mono phase2_step_nxt2 vs_less_vcount)
  then show ?thesis
    using distinct_vs_list
    by (auto simp: build_tree_def Let_def distinct_card[symmetric] intro!: card_mono elim!: order.trans[rotated])
qed

subsection \<open>Assembly substrate: the artificial-edge tails keep length
  @{term \<open>length vs_list\<close>}\<close>

text \<open>The tails are pre-sized to @{term \<open>length vs_list\<close>} at @{const dfs_init} and only ever updated
      in place (@{const List.list_update}) or left untouched by @{const build_dfs}, so their length is
      invariant. With @{thm build_tree_nxt_le} this shows every artificial edge the build emits lands
      inside the tails --- the well-formedness the augmented edge arrays need.\<close>

definition art_len :: "'n dfs_state \<Rightarrow> bool" where
  "art_len s \<longleftrightarrow> length (ds_afst s) = length vs_list \<and> length (ds_asnd s) = length vs_list
     \<and> length (ds_acap s) = length vs_list \<and> length (ds_aflw s) = length vs_list
     \<and> length (ds_aest s) = length vs_list"

lemma dfs_init_art_len: "art_len dfs_init"
  by (simp add: art_len_def dfs_init_def)

lemma emit_U_edge_art_len: "art_len s \<Longrightarrow> art_len (emit_U_edge s v)"
  by (simp add: art_len_def emit_U_edge_def Let_def)

lemma open_tree_component_art_len:
  "\<lbrakk>dfs_inv acyc_flow s; c < vcount; art_len s\<rbrakk>
    \<Longrightarrow> art_len (open_tree_component acyc_flow s c)"
  by (simp add: art_len_def open_tree_component_art)

lemma phase1_step_art_len:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; art_len s\<rbrakk>
    \<Longrightarrow> art_len (phase1_step acyc_flow v s)"
  by (simp add: phase1_step_def emit_U_edge_art_len open_tree_component_art_len vs_less_vcount)

lemma phase2_step_art_len:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; art_len s\<rbrakk>
    \<Longrightarrow> art_len (phase2_step acyc_flow v s)"
  by (simp add: phase2_step_def open_tree_component_art_len vs_less_vcount)

lemma phase1_art_len:
  "\<lbrakk>dfs_inv acyc_flow s \<and> ds_stk s = []; art_len s\<rbrakk>
    \<Longrightarrow> art_len (phase1 acyc_flow s)"
  unfolding phase1_def
  by (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list"
        and P = "\<lambda>s. (dfs_inv acyc_flow s \<and> ds_stk s = []) \<and> art_len s", THEN conjunct2])
    (simp_all add: phase1_step_inv phase1_step_art_len)

lemma build_tree_art_len: "art_len (build_tree acyc_flow)"
proof-
  have "art_len (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
    by (rule phases_preserve[where Q = art_len])
      (simp_all add: dfs_init_art_len phase1_step_art_len phase2_step_art_len)
  then show ?thesis by (simp add: build_tree_def Let_def art_len_def)
qed

subsection \<open>Assembly substrate: what each emission writes into the artificial tails\<close>

text \<open>Each @{const open_tree_component} (a component-tree edge, tag @{const InTree}) and each
      @{const emit_U_edge} (a saturated bound edge, tag @{const InU}) records, at the artificial cursor
      @{const ds_nxt}, exactly the subject vertex's @{const art_dir}-oriented endpoints together with its
      @{const art_flow} / @{const art_tree_cap}. These per-emission content facts feed \<open>init_bflow\<close> /
      \<open>init_partition\<close> / \<open>init_flow_fits\<close> / \<open>init_pot_fits\<close>.\<close>

lemma open_tree_component_afst_at:
  "\<lbrakk>dfs_inv acyc_flow s; c < vcount; ds_nxt s < length vs_list; art_len s\<rbrakk> \<Longrightarrow>
    ds_afst (open_tree_component acyc_flow s c) ! (ds_nxt s) = (if art_dir c then c else vcount)"
  by (simp add: open_tree_component_art art_len_def)

lemma open_tree_component_asnd_at:
  "\<lbrakk>dfs_inv acyc_flow s; c < vcount; ds_nxt s < length vs_list; art_len s\<rbrakk> \<Longrightarrow>
    ds_asnd (open_tree_component acyc_flow s c) ! (ds_nxt s) = (if art_dir c then vcount else c)"
  by (simp add: open_tree_component_art art_len_def)

lemma open_tree_component_aflw_at:
  "\<lbrakk>dfs_inv acyc_flow s; c < vcount; ds_nxt s < length vs_list; art_len s\<rbrakk> \<Longrightarrow>
    ds_aflw (open_tree_component acyc_flow s c) ! (ds_nxt s) = art_flow c"
  by (simp add: open_tree_component_art art_len_def)

subsection \<open>Assembly substrate: the full artificial-edge tail content\<close>

text \<open>Lifting the per-emission content facts to the whole build: every artificial edge index
      @{term \<open>k < ds_nxt (build_tree acyc_flow)\<close>} stores a well-formed edge --- one endpoint the
      artificial root @{const vcount}, the other a genuine vertex @{term \<open>subj < vcount\<close>}, oriented by
      @{const art_dir}, carrying @{const art_flow} and (on tree edges) @{const art_tree_cap}. During the build we only
      track the indices below the tail length (@{term tail_content_upto}); the bound @{thm build_tree_nxt_le} shows at
      the end that these are all emitted indices.\<close>

definition tail_edge_ok :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> bool" where
  "tail_edge_ok s k \<longleftrightarrow>
     (\<exists>subj. subj < vcount
        \<and> ds_afst s ! k = (if art_dir subj then subj else vcount)
        \<and> ds_asnd s ! k = (if art_dir subj then vcount else subj)
        \<and> ds_aflw s ! k = art_flow subj
        \<and> ((ds_aest s ! k = InTree \<and> ds_acap s ! k = art_tree_cap subj)
           \<or> (ds_aest s ! k = InU \<and> ds_acap s ! k = art_flow subj)))"

definition tail_content :: "'n dfs_state \<Rightarrow> bool" where
  "tail_content s \<longleftrightarrow> (\<forall>k < ds_nxt s. tail_edge_ok s k)"

definition tail_content_upto :: "'n dfs_state \<Rightarrow> bool" where
  "tail_content_upto s \<longleftrightarrow> (\<forall>k < min (ds_nxt s) (length vs_list). tail_edge_ok s k)"

lemma emit_U_edge_tail_edge_ok_old:
  "\<lbrakk>k < ds_nxt s; tail_edge_ok s k\<rbrakk> \<Longrightarrow> tail_edge_ok (emit_U_edge s v) k"
  by (simp add: tail_edge_ok_def emit_U_edge_def Let_def)

lemma open_tree_component_afst_old:
  "\<lbrakk>dfs_inv acyc_flow s; c < vcount; k < ds_nxt s\<rbrakk>
      \<Longrightarrow> ds_afst (open_tree_component acyc_flow s c) ! k = ds_afst s ! k"
  by (simp add: open_tree_component_art)

lemma open_tree_component_asnd_old:
  "\<lbrakk>dfs_inv acyc_flow s; c < vcount; k < ds_nxt s\<rbrakk>
      \<Longrightarrow> ds_asnd (open_tree_component acyc_flow s c) ! k = ds_asnd s ! k"
  by (simp add: open_tree_component_art)

lemma open_tree_component_aflw_old:
  "\<lbrakk>dfs_inv acyc_flow s; c < vcount; k < ds_nxt s\<rbrakk>
      \<Longrightarrow> ds_aflw (open_tree_component acyc_flow s c) ! k = ds_aflw s ! k"
  by (simp add: open_tree_component_art)

lemma open_tree_component_tail_edge_ok_old:
  "\<lbrakk>dfs_inv acyc_flow s; c < vcount; k < ds_nxt s; tail_edge_ok s k\<rbrakk> \<Longrightarrow>
    tail_edge_ok (open_tree_component acyc_flow s c) k"
  by (simp add: tail_edge_ok_def open_tree_component_art)

lemma emit_U_edge_tail_edge_ok_new:
  "\<lbrakk>v < vcount; ds_nxt s < length vs_list; art_len s\<rbrakk>
      \<Longrightarrow> tail_edge_ok (emit_U_edge s v) (ds_nxt s)"
  by (auto simp: tail_edge_ok_def emit_U_edge_def Let_def art_len_def art_dir_def art_flow_def intro!: exI[of _ v])

lemma open_tree_component_tail_edge_ok_new:
  "\<lbrakk>dfs_inv acyc_flow s; c < vcount; ds_nxt s < length vs_list; art_len s\<rbrakk> \<Longrightarrow>
    tail_edge_ok (open_tree_component acyc_flow s c) (ds_nxt s)"
  by (auto simp: tail_edge_ok_def open_tree_component_art art_len_def intro!: exI[of _ c])

lemma emit_U_edge_tcu: "\<lbrakk>v < vcount; art_len s; tail_content_upto s\<rbrakk>
  \<Longrightarrow> tail_content_upto (emit_U_edge s v)"
  by (auto simp: tail_content_upto_def emit_U_edge_nxt less_Suc_eq
      intro: emit_U_edge_tail_edge_ok_old emit_U_edge_tail_edge_ok_new)

lemma open_tree_component_tcu:
  "\<lbrakk>dfs_inv acyc_flow s; c < vcount; art_len s; tail_content_upto s\<rbrakk> \<Longrightarrow>
    tail_content_upto (open_tree_component acyc_flow s c)"
  by (auto simp: tail_content_upto_def open_tree_component_art(1) less_Suc_eq
      intro: open_tree_component_tail_edge_ok_old open_tree_component_tail_edge_ok_new)

lemma phase1_step_tcu:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s \<and> ds_stk s = [];
    art_len s \<and> tail_content_upto s\<rbrakk>
    \<Longrightarrow> art_len (phase1_step acyc_flow v s) \<and> tail_content_upto (phase1_step acyc_flow v s)"
  by (simp add: phase1_step_def emit_U_edge_art_len open_tree_component_art_len emit_U_edge_tcu
      open_tree_component_tcu vs_less_vcount)

lemma phase2_step_tcu:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s \<and> ds_stk s = [];
    art_len s \<and> tail_content_upto s\<rbrakk>
    \<Longrightarrow> art_len (phase2_step acyc_flow v s) \<and> tail_content_upto (phase2_step acyc_flow v s)"
  by (simp add: phase2_step_def open_tree_component_art_len open_tree_component_tcu vs_less_vcount)

lemma card_sub_vs_le: "A \<subseteq> set vs_list \<Longrightarrow> card A \<le> length vs_list"
  by (drule card_mono[rotated]) (simp_all add: distinct_card distinct_vs_list)

lemma build_tree_tail_content: "tail_content (build_tree acyc_flow)"
proof-
  have "tail_content_upto dfs_init" by (simp add: tail_content_upto_def dfs_init_def)
  then have "art_len (phase2 acyc_flow (phase1 acyc_flow dfs_init))
      \<and> tail_content_upto (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
    by (intro phases_preserve[where Q = "\<lambda>s. art_len s \<and> tail_content_upto s"])
      (simp_all add: dfs_init_art_len phase1_step_tcu phase2_step_tcu)
  then show ?thesis
    using build_tree_nxt_le
    by (simp add: build_tree_def Let_def tail_content_def tail_content_upto_def tail_edge_ok_def min_def)
qed

subsection \<open>The acyclified flow the tree is built from\<close>

text \<open>The builder runs on @{const acyc_flow} --- the acyclifier's output --- never on the raw input
      @{term flow_list}.  Its length is @{term m} on \<^emph>\<open>both\<close> branches: on @{term None} it is the
      input list itself, and on @{term Some} the acyclifier's own flow-array invariant (which pins the
      length) is carried through the loop by @{thm make_acyclic_flow_invar}.  So the augmented-array
      glue below needs no case split on the acyclifier's verdict.  Likewise it is capacity-complying on
      both branches (@{thm make_acyclic_feasible}): cancelling cycles never pushes an arc outside its bounds,
      so acyclicity is the only property that is genuinely \<^emph>\<open>Some\<close>-only.\<close>

lemma af_cap_feasible_flow_list: "af_cap_feasible flow_list"
  using flow_nonneg flow_le_cap by (fastforce simp: af_cap_feasible_def)

lemma distinct_edged_vs_list: "distinct edged_vs_list"
  unfolding edged_vs_list_def by (rule distinct_filter[OF distinct_vs_list])

lemma acyc_flow_props: "length acyc_flow = m \<and> af_cap_feasible acyc_flow"
proof(cases acyc_flow_opt)
  case (Some f')
  moreover have "lc_invar \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr>"
    "lc_abstract \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr> \<subseteq> original_network.\<V>"
    "lc_iterated \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr> = {}" "length flow_list = m"
    using length_flow length_edges
    by (simp_all add: lc_invar_def distinct_edged_vs_list lc_abstract_def V_orig_eq_edged lc_iterated_def)
  ultimately show ?thesis
    using make_acyclic_flow_invar[OF multigraph_inv_csr _ af_cap_feasible_flow_list]
      make_acyclic_feasible[OF multigraph_inv_csr _ af_cap_feasible_flow_list]
    by (simp add: acyc_flow_def acyc_flow_opt_def)
qed (use length_flow length_edges af_cap_feasible_flow_list in \<open>simp add: acyc_flow_def\<close>)

lemma length_acyc_flow[simp]: "length acyc_flow = m"
  using acyc_flow_props by simp

lemma af_cap_feasible_acyc_flow: "af_cap_feasible acyc_flow"
  using acyc_flow_props by simp

lemma acyc_flow_nonneg: "e < m \<Longrightarrow> 0 \<le> acyc_flow ! e"
  using af_cap_feasible_acyc_flow by (simp add: af_cap_feasible_def)

lemma acyc_flow_le_cap:
  "\<lbrakk>e < m; capacity_list ! e \<noteq> - 1\<rbrakk> \<Longrightarrow> acyc_flow ! e \<le> capacity_list ! e"
  using af_cap_feasible_acyc_flow by (force simp: af_cap_feasible_def)

subsection \<open>Thin glue: the unified augmented edge arrays (real part @ artificial tail)\<close>

text \<open>The design ({\isasymsection}5, Network\_Simplex\_Initial\_Basis.thy) calls for the augmented network's
      endpoints, capacity, flow, cost and edge-state to be single length-@{term \<open>m + Kart\<close>} arrays --- the
      input lists followed by the @{const build_tree} artificial tail truncated to its live prefix
      @{term \<open>Kart = ds_nxt (build_tree acyc_flow)\<close>}. Real indices @{term \<open>e < m\<close>} read the
      input lists; artificial indices @{term \<open>m + e\<close>} (@{term \<open>e < Kart\<close>}) read the built
      tail, characterised by \<open>tail_edge_ok_build_tree\<close>: one endpoint the artificial root @{const vcount},
      the other a genuine vertex, oriented by @{const art_dir}, carrying @{const art_flow} /
      @{const art_tree_cap}.\<close>

lemma Kart_le: "Kart \<le> length vs_list"
  using build_tree_nxt_le by (simp add: Kart_def)

lemma len_afst_bt: "length (ds_afst (build_tree acyc_flow)) = length vs_list"
  using build_tree_art_len by (simp add: art_len_def)

lemma len_asnd_bt: "length (ds_asnd (build_tree acyc_flow)) = length vs_list"
  using build_tree_art_len by (simp add: art_len_def)

lemma len_acap_bt: "length (ds_acap (build_tree acyc_flow)) = length vs_list"
  using build_tree_art_len by (simp add: art_len_def)

lemma len_aflw_bt: "length (ds_aflw (build_tree acyc_flow)) = length vs_list"
  using build_tree_art_len by (simp add: art_len_def)

lemma len_aest_bt: "length (ds_aest (build_tree acyc_flow)) = length vs_list"
  using build_tree_art_len by (simp add: art_len_def)

definition cost_all :: "real list" where "cost_all = map h cost_list @ replicate Kart bigM"

lemma length_fst_list_m[simp]: "length fst_list = m" using length_fst length_edges by simp

lemma length_snd_list_m[simp]: "length snd_list = m" using length_snd length_edges by simp

lemma length_cost_list_m[simp]: "length cost_list = m" using length_cost length_edges by simp

lemma length_fst_all[simp]: "length fst_all = m + Kart"
  using Kart_le len_afst_bt by (simp add: fst_all_def)

lemma length_snd_all[simp]: "length snd_all = m + Kart"
  using Kart_le len_asnd_bt by (simp add: snd_all_def)

lemma length_cap_all[simp]: "length cap_all = m + Kart"
  using Kart_le len_acap_bt length_edges by (simp add: cap_all_def)

lemma length_flow_all[simp]: "length flow_all = m + Kart"
  using Kart_le len_aflw_bt by (simp add: flow_all_def)

lemma length_state_all[simp]: "length state_all = m + Kart"
  using Kart_le len_aest_bt by (simp add: state_all_def)

lemma length_cost_all[simp]: "length cost_all = m + Kart"
  by (simp add: cost_all_def)

lemma fst_all_real: "e < m \<Longrightarrow> fst_all ! e = fst_list ! e" by (simp add: fst_all_def nth_append)

lemma snd_all_real: "e < m \<Longrightarrow> snd_all ! e = snd_list ! e" by (simp add: snd_all_def nth_append)

lemma cap_all_real: "e < m \<Longrightarrow> cap_all ! e = capacity_list ! e"
  by (simp add: cap_all_def nth_append length_edges)

lemma flow_all_real: "e < m \<Longrightarrow> flow_all ! e = acyc_flow ! e" by (simp add: flow_all_def nth_append)

lemma state_all_real: "e < m \<Longrightarrow> state_all ! e = (edge_state acyc_flow) ! e"
  by (simp add: state_all_def nth_append)

lemma cost_all_real: "e < m \<Longrightarrow> cost_all ! e = h (cost_list ! e)" by (simp add: cost_all_def nth_append)

lemma fst_all_art: "e < Kart \<Longrightarrow> fst_all ! (m + e) = ds_afst (build_tree acyc_flow) ! e"
  using Kart_le len_afst_bt by (simp add: fst_all_def nth_append)

lemma snd_all_art: "e < Kart \<Longrightarrow> snd_all ! (m + e) = ds_asnd (build_tree acyc_flow) ! e"
  using Kart_le len_asnd_bt by (simp add: snd_all_def nth_append)

lemma cap_all_art: "e < Kart \<Longrightarrow> cap_all ! (m + e) = ds_acap (build_tree acyc_flow) ! e"
  using Kart_le len_acap_bt length_edges by (simp add: cap_all_def nth_append)

lemma flow_all_art: "e < Kart \<Longrightarrow> flow_all ! (m + e) = ds_aflw (build_tree acyc_flow) ! e"
  using Kart_le len_aflw_bt by (simp add: flow_all_def nth_append)

lemma state_all_art: "e < Kart \<Longrightarrow> state_all ! (m + e) = ds_aest (build_tree acyc_flow) ! e"
  using Kart_le len_aest_bt by (simp add: state_all_def nth_append)

lemma cost_all_art: "e < Kart \<Longrightarrow> cost_all ! (m + e) = bigM"
  by (simp add: cost_all_def nth_append)

lemma tail_edge_ok_build_tree: "e < Kart \<Longrightarrow> tail_edge_ok (build_tree acyc_flow) e"
  using build_tree_tail_content by (simp add: tail_content_def Kart_def)

text \<open>\<^bold>\<open>Status of the @{const arb_invar} obligations --- all discharged
      (@{thm arb_invar_Sarb}).\<close> The deferred bridge \<open>Vseen = set vs_list\<close> belongs to the
      network-simplex vertex layer, where \<open>arb_invar_Sarb\<close> feeds the \<open>arborescense_adt\<close>
      instantiation of \<open>network_simplex_init\<close>.\<close>

section \<open>Instantiating the spanning-tree ADT with the threaded arborescence\<close>

text \<open>We discharge every axiom of the abstract spanning-tree ADT @{locale arborescense_adt}
      (\<^theory>\<open>Mincost_Flow_Algorithms.Network_Simplex\<close>) for the concrete threaded
      @{typ \<open>'a ndtree\<close>} satisfying @{const arb_invar}. The abstract (undirected) arborescence
      \<open>abstract_arb\<close> is the set of undirected parent edges; the executable operations are the snum-driven
      \<open>get_path_pair_impl\<close>, the thread-recursive \<open>iterate_root_opposed_impl\<close>, and the
      branch-reversing \<open>swap_edge_impl\<close> (a wrapper around @{const update_tree}). The pivotal bridge is
      \<open>unique_walk_to_root\<close>: every distinct walk to the root \<^emph>\<open>is\<close> the @{const follow}
      path, from which the fundamental-cycle, uniqueness, iteration and edge-swap axioms all follow. The development is
      generic over \<open>arb_invar r V S\<close>; the final interpretation specialises it at the initial basis
      \<open>Sarb\<close> on \<open>Varb\<close> with root \<open>vcount\<close>.\<close>

definition abstract_arb :: "'a ndtree \<Rightarrow> 'a set set" where
  "abstract_arb S = {{x, y} |x y. prnt S x = Some y}"

lemma abstract_arb_edge: "prnt S x = Some y \<Longrightarrow> {x, y} \<in> abstract_arb S"
  by (auto simp: abstract_arb_def)

lemma abstract_arb_alt: "abstract_arb S = {{x, y} |x y. Some x = prnt S y}"
  unfolding abstract_arb_def by (auto simp: eq_commute insert_commute)

lemma parent_spec_neq: "\<lbrakk>parent_spec T; T x = Some y\<rbrakk> \<Longrightarrow> x \<noteq> y"
  by (auto simp: parent_spec_def dest: wf_not_refl[of _ x])

lemma dblton_abstract_arb: "arb_invar r V S \<Longrightarrow> dblton_graph (abstract_arb S)"
  using parent_spec_neq[OF arb_invarD(2)] by (fastforce simp: dblton_graph_def abstract_arb_def)

lemma Vs_abstract_arb:
  "arb_invar r V S \<Longrightarrow> Vs (abstract_arb S) = V"
  by (drule arb_invarD(1), drule rooted_arborescense_invar_dVs) (auto simp: Vs_def dVs_def abstract_arb_def eq_commute)

lemma finite_V_arb: "arb_invar r V S \<Longrightarrow> finite V"
  by (auto dest!: arb_invarD(7))

lemma graph_invar_abstract_arb: "arb_invar r V S \<Longrightarrow> graph_invar (abstract_arb S)"
  by (frule dblton_abstract_arb, frule Vs_abstract_arb, drule finite_V_arb) simp

lemma follow_walk_root:
  assumes "arb_invar r V S" "v \<in> V" shows "walk_betw (abstract_arb S) v (follow (prnt S) v) r"
proof-
  interpret P: parent "prnt S" "\<lambda>_ _. True" using arb_invarD(2)[OF assms(1)] by unfold_locales
  have "{{x, y} |x y. parent_spec_i.follow_rel (prnt S) x y} = abstract_arb S"
    unfolding abstract_arb_alt by (simp add: P.parent_eq_follow_rel)
  then show ?thesis
    using P.follow_walk_betw[of v] follow_last_root[OF assms] Vs_abstract_arb[OF assms(1)] assms(2)
    by (cases "follow (prnt S) v = [v]") (auto simp: follow_def walk_reflexive)
qed

lemma follow_root_singleton: "arb_invar r V S \<Longrightarrow> follow (prnt S) r = [r]"
  by (frule arb_invarD(2), drule arb_invarD(5)) (cases "prnt S r"; auto simp: follow_None_ps dom_def set_eq_iff)

lemma parent_in_V: "\<lbrakk>arb_invar r V S; y \<in> V; prnt S y = Some w\<rbrakk> \<Longrightarrow> w \<in> V"
  by (rule rooted_arborescense_invar_parent_in_V[OF arb_invarD(1)])

lemma abstract_arb_edgeD: "\<lbrakk>parent_spec (prnt S); {y, z} \<in> abstract_arb S\<rbrakk>
  \<Longrightarrow> prnt S y = Some z \<or> prnt S z = Some y"
  using parent_spec_neq[of "prnt S"] by (auto simp: abstract_arb_def doubleton_eq_iff)

lemma subtree_cut:
  assumes "parent_spec (prnt S)"
  shows "\<lbrakk>path (abstract_arb S) q; y \<notin> set q; hd q \<in> children (prnt S) y\<rbrakk>
    \<Longrightarrow> set q \<subseteq> children (prnt S) y"
proof(induction q)
  case (Cons a q)
  note IH = Cons.IH and P = Cons.prems
  show ?case
  proof(cases q)
    case (Cons b q')
    with P have "y \<in> set (follow (prnt S) a)" "y \<noteq> a" "{a, b} \<in> abstract_arb S"
      by (auto simp: children_def)
    with assms have "b \<in> children (prnt S) y"
      by (auto simp: children_def follow_Some_ps dest!: abstract_arb_edgeD[OF assms])
    with IH P Cons show ?thesis by simp
  qed (use P in simp)
qed simp

lemma co_cut:
  assumes "parent_spec (prnt S)"
  shows "\<lbrakk>path (abstract_arb S) q; y \<notin> set q; hd q \<notin> children (prnt S) y\<rbrakk>
    \<Longrightarrow> set q \<inter> children (prnt S) y = {}"
proof(induction q)
  case (Cons a q)
  note IH = Cons.IH and P = Cons.prems
  show ?case
  proof(cases q)
    case (Cons b q')
    with P have "y \<notin> set (follow (prnt S) a)" "y \<noteq> b" "{a, b} \<in> abstract_arb S"
      by (auto simp: children_def)
    with assms have "b \<notin> children (prnt S) y"
      by (auto simp: children_def follow_Some_ps dest!: abstract_arb_edgeD[OF assms])
    with IH P Cons show ?thesis by auto
  qed (use P in simp)
qed simp

lemma unique_walk_to_root:
  assumes "arb_invar r V S"
  shows "\<lbrakk>y \<in> V; walk_betw (abstract_arb S) y p r; distinct p\<rbrakk>
    \<Longrightarrow> p = follow (prnt S) y"
proof(induction p arbitrary: y)
  case (Cons a p)
  note IH = Cons.IH and P = Cons.prems
  have ps: "parent_spec (prnt S)" and fr: "follow (prnt S) r = [r]"
    using assms by (simp_all add: arb_invarD(2) follow_root_singleton)
  from P have R: "a = y" "path (abstract_arb S) (y # p)" "last (y # p) = r" by (auto simp: walk_betw_def)
  show ?case
  proof(cases p)
    case Nil
    with R fr show ?thesis by simp
  next
    case (Cons b q)
    with R have E: "{y, b} \<in> abstract_arb S" "path (abstract_arb S) p" "walk_betw (abstract_arb S) b p r"
      by (auto simp: walk_betw_def)
    from abstract_arb_edgeD[OF ps E(1)] show ?thesis
    proof
      assume "prnt S y = Some b"
      with E(3) P R(1) show ?thesis using ps IH[of b] parent_in_V[OF assms] by (simp add: follow_Some_ps)
    next
      assume "prnt S b = Some y"
      with ps have "b \<in> children (prnt S) y" by (simp add: children_def follow_Some_ps follow_mem_ps)
      then have "set p \<subseteq> children (prnt S) y" using subtree_cut[OF ps E(2)] P(3) R(1) Cons by simp
      then have "y \<in> set (follow (prnt S) r)" using R(3) Cons last_in_set[of p] by (auto simp: children_def)
      with fr P(3) R Cons last_in_set[of p] show ?thesis by auto
    qed
  qed
qed (simp add: walk_betw_def)

lemma children_subset_V:
  "\<lbrakk>arb_invar r V S; v \<in> V\<rbrakk> \<Longrightarrow> children (prnt S) v \<subseteq> V"
  by (rule Rooted_Arborescense.children_subset_V[OF arb_invarD(1)])

lemma iterate_set_eq:
  assumes "arb_invar r V S" "v \<in> V"
  shows "{x |x p. walk_betw (abstract_arb S) x p r \<and> distinct p \<and> v \<in> set p} = children (prnt S) v"
proof(intro equalityI subsetI)
  fix x assume "x \<in> {x |x p. walk_betw (abstract_arb S) x p r \<and> distinct p \<and> v \<in> set p}"
  then show "x \<in> children (prnt S) v"
    using unique_walk_to_root[OF assms(1)] Vs_abstract_arb[OF assms(1)] by (fastforce simp: children_def)
next
  fix x assume "x \<in> children (prnt S) v"
  moreover from this have "x \<in> V" using children_subset_V[OF assms] by auto
  ultimately show "x \<in> {x |x p. walk_betw (abstract_arb S) x p r \<and> distinct p \<and> v \<in> set p}"
    using follow_walk_root[OF assms(1)] follow_distinct_ps[OF arb_invarD(2)[OF assms(1)]]
    by (fastforce simp: children_def)
qed

lemma join_of_sym:
  assumes "arb_invar r V S" "a \<in> V" "b \<in> V" shows "join_of (prnt S) a b = join_of (prnt S) b a"
proof-
  have ps: "parent_spec (prnt S)" using assms(1) by (rule arb_invarD(2))
  have l: "last (follow (prnt S) a) = last (follow (prnt S) b)"
    using follow_last_root[OF assms(1,2)] follow_last_root[OF assms(1,3)] by simp
  then show ?thesis
    using join_of_mem[OF ps l] join_of_mem[OF ps l[symmetric]]
    by (blast intro: ancestor_antisym[OF ps] join_of_first[OF ps])
qed

lemma get_path_pair_impl_eval:
  assumes "arb_invar r V S" "u \<in> V" "v \<in> V"
  shows "get_path_pair_impl S u v = (takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) u),
    takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) v))"
  using follow_last_root[OF assms(1,2)] follow_last_root[OF assms(1,3)] join_of_mem[OF arb_invarD(2)[OF assms(1)]]
    join_paths_loop_eval[OF assms _ _ join_takeWhile_disjoint[OF assms refl], of "[]" "[]"]
  by (simp add: get_path_pair_impl_def)

lemma get_path_pair_axiom1:
  assumes "arb_invar r V S" "get_path_pair_impl S u v = (p1, p2)" "u \<noteq> v" "u \<in> V" "v \<in> V"
  shows "\<exists>a p3. walk_betw (abstract_arb S) u (p1 @ a # p3) r
      \<and> walk_betw (abstract_arb S) v (p2 @ a # p3) r \<and>
    distinct (p1 @ a # p3) \<and> distinct (p2 @ a # p3) \<and> set p1 \<inter> set p2 = {}"
proof-
  have ps: "parent_spec (prnt S)" using assms(1) by (rule arb_invarD(2))
  obtain t where "follow (prnt S) (join_of (prnt S) u v) = join_of (prnt S) u v # t"
    using follow_hd_ps[OF ps, of "join_of (prnt S) u v"] follow_ne_ps[OF ps, of "join_of (prnt S) u v"]
    by (cases "follow (prnt S) (join_of (prnt S) u v)") auto
  then show ?thesis
    using get_path_pair_impl_correct(1,2,5)[OF assms(1,4,5,2)] follow_walk_root[OF assms(1,4)]
      follow_walk_root[OF assms(1,5)] follow_distinct_ps[OF ps, of u] follow_distinct_ps[OF ps, of v]
    by auto
qed

lemma get_path_pair_axiom2:
  "\<lbrakk>arb_invar r V S; get_path_pair_impl S u v = (p1, p2); u \<noteq> v; u \<in> V; v \<in> V\<rbrakk>
    \<Longrightarrow> get_path_pair_impl S v u = (p2, p1)"
  by (simp add: get_path_pair_impl_eval join_of_sym[of r V S v u])

lemma iterate_axiom:
  "\<lbrakk>arb_invar r V S; v \<in> V\<rbrakk> \<Longrightarrow>
    \<exists>xs. set xs = {x |x p. walk_betw (abstract_arb S) x p r \<and> distinct p \<and> v \<in> set p}
      \<and> distinct xs \<and> iterate_root_opposed_impl S v f acc = foldr f xs acc"
  by (subst iterate_set_eq, assumption+, frule (1) iterate_root_opposed_impl_foldr[where f = f and acc = acc]) blast

text \<open>The custom two-loop potential shift @{const shift_pot_impl} (one loop adding, one subtracting)
      coincides with the generic subtree iteration once the @{term up} flag is fixed: reconstruct the
      thread-block decomposition of @{term v}'s subtree (as in @{thm [source]
      iterate_root_opposed_impl_block}) and feed it to the per-loop equivalences proved in the code
      theory.  This is the promised equivalence to the ``old tree fold''.\<close>
lemma shift_pot_impl_eq_iterate:
  assumes "arb_invar r V S" "v \<in> V"
  shows "shift_pot_impl S v pa g up = iterate_root_opposed_impl S v
    (\<lambda>x acc. acc[x := (if up then pval_plus (acc ! x) g else pval_minus (acc ! x) g)]) pa"
proof-
  have T: "parent_spec (thrd S)" using assms(1) by (rule arb_invarD(3))
  obtain bl where "block S v = bl @ [lsuc S v]"
    using block_props(2,3)[OF assms] by (cases "block S v" rule: rev_cases) auto
  then have "follow (thrd S) v
      = bl @ lsuc S v # (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    using block_props(1)[OF assms] by simp
  moreover from this have "lsuc S v \<notin> set bl" using follow_distinct_ps[OF T, of v] by simp
  ultimately show ?thesis
    using shift_pot_up_loop_subtree_fold[OF T] shift_pot_down_loop_subtree_fold[OF T]
    by (cases up) (simp_all add: shift_pot_impl_def iterate_root_opposed_impl_def)
qed

text \<open>Hence @{const shift_pot_impl} satisfies the @{text shift_pot_spec} obligation of
      @{locale network_simplex_spec}: it is a @{const foldr} over a distinct enumeration of exactly the
      subtree of @{term v} (the nodes whose path to the root passes through @{term v}), whose per-node
      step reads/shifts/writes the potential.\<close>
lemma shift_pot_impl_spec:
  assumes "arb_invar r V S" "v \<in> V"
  shows "\<exists>xs. set xs = {x. \<exists>p. walk_betw (abstract_arb S) x p r \<and> distinct p \<and> v \<in> set p}
    \<and> distinct xs
    \<and> shift_pot_impl S v pa g up
      = foldr (\<lambda>x acc. acc[x := (if up then pval_plus else pval_minus) (acc ! x) g]) xs pa"
proof-
  let ?F = "\<lambda>x acc. acc[x := (if up then pval_plus (acc ! x) g else pval_minus (acc ! x) g)]"
  obtain xs where "set xs = {x |x p. walk_betw (abstract_arb S) x p r \<and> distinct p \<and> v \<in> set p}"
    "distinct xs" "iterate_root_opposed_impl S v ?F pa = foldr ?F xs pa"
    using iterate_axiom[OF assms, of ?F pa] by blast
  moreover have "?F = (\<lambda>x acc. acc[x := (if up then pval_plus else pval_minus) (acc ! x) g])"
    by (cases up) auto
  ultimately show ?thesis by (intro exI[of _ xs]) (simp add: shift_pot_impl_eq_iterate[OF assms])
qed

lemma child_pred_unique:
  assumes "parent_spec T" "T b = Some y" "T b' = Some y" "b \<in> set (follow T x)" "b' \<in> set (follow T x)"
  shows "b = b'"
proof-
  obtain A B A' B' where "follow T x = A @ b # B" "follow T x = A' @ b' # B'"
    using assms(4,5) by (blast dest: split_list)
  moreover from this have "follow T b = b # B" "follow T b' = b' # B'" using follow_append_ps[OF assms(1)] by blast+
  ultimately have "(A @ [b]) @ follow T y = (A' @ [b']) @ follow T y"
    using assms by (simp add: follow_Some_ps)
  then show ?thesis by simp
qed

lemma first_step_char:
  assumes "arb_invar r V S" "parent_spec (prnt S)" "walk_betw (abstract_arb S) y p x" "distinct p" "p = y # b # p''"
  shows "(x \<in> children (prnt S) y \<and> prnt S b = Some y \<and> x \<in> children (prnt S) b)
    \<or> (x \<notin> children (prnt S) y \<and> prnt S y = Some b)"
proof-
  have R: "{y, b} \<in> abstract_arb S" "path (abstract_arb S) (b # p'')" "last (b # p'') = x"
    "y \<notin> set (b # p'')"
    using assms(3-5) by (auto simp: walk_betw_def)
  from abstract_arb_edgeD[OF assms(2) R(1)] show ?thesis
  proof
    assume "prnt S y = Some b"
    moreover from this have "b \<notin> children (prnt S) y"
      using assms(2) follow_distinct_ps[OF assms(2), of y] by (simp add: children_def follow_Some_ps)
    ultimately show ?thesis using co_cut[OF assms(2) R(2,4)] R(3) last_in_set[of "b # p''"] by auto
  next
    assume "prnt S b = Some y"
    moreover from this have "b \<in> children (prnt S) y"
      using assms(2) by (simp add: children_def follow_Some_ps follow_mem_ps)
    moreover have "x \<in> children (prnt S) b"
    proof(cases p'')
      case (Cons c q)
      with R \<open>prnt S b = Some y\<close> have "prnt S c = Some b"
        using abstract_arb_edgeD[OF assms(2), of b c] by auto
      then have "set p'' \<subseteq> children (prnt S) b"
        using assms(2) subtree_cut[OF assms(2), of p'' b] R(2) assms(4,5) Cons
        by (simp add: children_def follow_Some_ps follow_mem_ps)
      with R(3) Cons show ?thesis using last_in_set[of p''] by auto
    qed (use R(3) assms(2) in \<open>simp add: children_def follow_mem_ps\<close>)
    ultimately show ?thesis using children_subset[OF assms(2)] by blast
  qed
qed

lemma closed_distinct_walk:
  "\<lbrakk>p \<noteq> []; hd p = z; last p = z; distinct p\<rbrakk> \<Longrightarrow> p = [z]"
  by (cases p rule: rev_cases) (auto simp: hd_append dest!: hd_in_set split: if_splits)

lemma walk_unique:
  assumes "arb_invar r V S" "x \<in> V"
  shows "\<lbrakk>y \<in> V; walk_betw (abstract_arb S) y p x; distinct p; walk_betw (abstract_arb S) y q x;
    distinct q\<rbrakk> \<Longrightarrow> p = q"
proof(induction p arbitrary: y q)
  case (Cons a p)
  note IH = Cons.IH and P = Cons.prems
  have ps: "parent_spec (prnt S)" using assms(1) by (rule arb_invarD(2))
  show ?case
  proof(cases "y = x")
    case True
    have "a # p = [x]" using P(3) True walk_between_nonempty_pathD[OF P(2)] by (intro closed_distinct_walk) simp_all
    moreover have "q = [x]" using P(5) True walk_between_nonempty_pathD[OF P(4)]
      by (intro closed_distinct_walk) simp_all
    ultimately show ?thesis by simp
  next
    case False
    obtain b pp where p: "p = b # pp" using P(2) False by (cases p) (auto simp: walk_betw_def)
    obtain b' qq where q: "q = y # b' # qq"
      using P(4) False by (cases q rule: remdups_adj.cases) (auto simp: walk_betw_def)
    have a: "a = y" using P(2) by (simp add: walk_betw_def)
    with p have pq: "a # p = y # b # pp" by simp
    have W: "walk_betw (abstract_arb S) b p x" "walk_betw (abstract_arb S) b' (b' # qq) x"
      using P(2,4) a p q by (auto simp: walk_betw_def)
    have "b = b'"
      using first_step_char[OF assms(1) ps P(2,3) pq] first_step_char[OF assms(1) ps P(4,5) q]
      by (auto simp: children_def intro: child_pred_unique[OF ps])
    with W P(3,5) a p q show ?thesis
      using Vs_abstract_arb[OF assms(1)] walk_endpoints(1)[OF W(1)] IH[of b "b' # qq"] by auto
  qed
qed (simp add: walk_betw_def)

lemma follow_prefix_walk:
  "\<lbrakk>arb_invar r V S; v \<in> V; follow (prnt S) v = pfx @ [jn] @ sfx\<rbrakk> \<Longrightarrow>
    walk_betw (abstract_arb S) v (pfx @ [jn]) jn"
  by (frule (1) follow_walk_root, drule arb_invarD(2), frule follow_hd_ps[where v = v])
    (use path_pref[of "abstract_arb S" "pfx @ [jn]" sfx] in \<open>cases pfx; auto simp: walk_betw_def\<close>)

lemma walk_exists:
  assumes "arb_invar r V S" "y \<in> V" "x \<in> V"
  shows "\<exists>p. walk_betw (abstract_arb S) y p x \<and> distinct p"
proof-
  let ?j = "join_of (prnt S) y x"
  obtain q1 q2 where gp: "get_path_pair_impl S y x = (q1, q2)" by fastforce
  have ps: "parent_spec (prnt S)" using assms(1) by (rule arb_invarD(2))
  obtain t where t: "follow (prnt S) ?j = ?j # t" using follow_hd_ps[OF ps, of ?j] follow_ne_ps[OF ps, of ?j]
    by (cases "follow (prnt S) ?j") auto
  have W: "walk_betw (abstract_arb S) y (q1 @ [?j]) ?j" "walk_betw (abstract_arb S) x (q2 @ [?j]) ?j"
    using t get_path_pair_impl_correct(1,2)[OF assms gp]
      follow_prefix_walk[OF assms(1,2), of q1 ?j t] follow_prefix_walk[OF assms(1,3), of q2 ?j t]
    by simp_all
  then have "walk_betw (abstract_arb S) y (q1 @ ?j # rev q2) x"
    using walk_transitive[OF W(1) walk_symmetric[OF W(2)]] by simp
  with get_path_pair_impl_correct(3-5)[OF assms gp] show ?thesis by auto
qed

lemma general_axiom3: "\<lbrakk>arb_invar r V S; x \<in> V; y \<in> V\<rbrakk>
  \<Longrightarrow> \<exists>!p. walk_betw (abstract_arb S) y p x \<and> distinct p"
  using walk_exists[of r V S y x] walk_unique[of r V S x y] by blast

lemma follow_edge_parent: "\<lbrakk>parent_spec T; (x, y) \<in> set (edges_of_vwalk (follow T u))\<rbrakk>
  \<Longrightarrow> T x = Some y"
  by (auto simp: in_set_conv_nth edges_of_vwalk_length edges_of_vwalk_index follow_nth_Suc)

text \<open>The pivot edge @{term \<open>(x, y)\<close>} on @{term u}'s branch below the join is a parent edge, and
      @{term x} lies strictly between @{term u} and the join: the setting of
      @{thm update_tree_preserves_arb_invar}.\<close>

lemma swap_edge_setup:
  assumes "arb_invar r V S" "get_path_pair_impl S u v = (p1, p2)" "walk_betw (abstract_arb S) u (p1 @ a # p3) r"
    "distinct (p1 @ a # p3)" "(x, y) \<in> set (edges_of_vwalk (p1 @ [a]))" "u \<in> V" "v \<in> V"
  shows "x \<in> set (follow (prnt S) u)" "join_of (prnt S) u v \<in> set (follow (prnt S) x)"
    "x \<noteq> join_of (prnt S) u v" "prnt S x = Some y"
proof-
  have ps: "parent_spec (prnt S)" using assms(1) by (rule arb_invarD(2))
  let ?j = "join_of (prnt S) u v"
  have F: "follow (prnt S) u = p1 @ a # p3" "follow (prnt S) ?j = a # p3"
    using unique_walk_to_root[OF assms(1,6,3,4)] get_path_pair_impl_correct(1)[OF assms(1,6,7,2)] by simp_all
  have a: "a = ?j" using F(2) follow_hd_ps[OF ps, of ?j] by simp
  have x: "x \<in> set p1"
  proof(cases p1 rule: rev_cases)
    case (snoc q b)
    with assms(5) show ?thesis using edges_of_vwalk_append_3[of p1 "[a]"] by (auto dest: v_in_edge_in_vwalk)
  qed (use assms(5) in simp)
  then obtain A B where "follow (prnt S) u = A @ x # (B @ a # p3)" using F(1) by (auto dest: split_list)
  then have "follow (prnt S) x = x # B @ a # p3" by (rule follow_append_ps[OF ps])
  with x a F(1) assms(4) show "x \<in> set (follow (prnt S) u)" "?j \<in> set (follow (prnt S) x)" "x \<noteq> ?j"
    by auto
  have "(x, y) \<in> set (edges_of_vwalk (follow (prnt S) u))"
    using F(1) assms(5) edges_of_vwalk_append_3[of "p1 @ [a]" p3] by auto
  then show "prnt S x = Some y" by (rule follow_edge_parent[OF ps])
qed

lemma swap_edge_axiom1:
  assumes "arb_invar r V S" "get_path_pair_impl S u v = (p1, p2)" "u \<noteq> v"
    "walk_betw (abstract_arb S) u (p1 @ a # p3) r" "distinct (p1 @ a # p3)"
    "(x, y) \<in> set (edges_of_vwalk (p1 @ [a]))" "u \<in> V" "v \<in> V"
  shows "arb_invar r V (swap_edge_impl S x u v)"
  using update_tree_preserves_arb_invar(1)[OF assms(1,7,8) refl swap_edge_setup(1-3)[OF assms(1,2,4-8)]]
  by (simp add: swap_edge_impl_def)

lemma spine_reindex_gen:
  assumes "0 < k"
  shows "{{s t, if t = 0 then a else s (t - 1)} |t. t \<le> k} = insert {s 0, a} {{s t, s (Suc t)} |t. t < k}"
proof(intro equalityI subsetI)
  fix e assume "e \<in> {{s t, if t = 0 then a else s (t - 1)} |t. t \<le> k}"
  then obtain t where "t \<le> k" "e = {s t, if t = 0 then a else s (t - 1)}" by blast
  then show "e \<in> insert {s 0, a} {{s t, s (Suc t)} |t. t < k}"
    by (cases t) (auto simp: insert_commute)
next
  fix e assume "e \<in> insert {s 0, a} {{s t, s (Suc t)} |t. t < k}"
  then consider "e = {s 0, a}" | t where "t < k" "e = {s t, s (Suc t)}" by blast
  then show "e \<in> {{s t, if t = 0 then a else s (t - 1)} |t. t \<le> k}"
  proof cases
    case (2 t)
    then have "e = {s (Suc t), if Suc t = 0 then a else s (Suc t - 1)}" "Suc t \<le> k"
        by (simp_all add: insert_commute)
    then show ?thesis by blast
  qed (use assms in \<open>auto intro!: exI[where x = 0]\<close>)
qed

lemma no_2cycle:
  assumes "parent_spec T" "T a = Some b" "T b = Some a" shows False
proof-
  have "b \<in> set (follow T a)" by (subst follow_Some_ps[OF assms(1,2)]) (use assms(1) in \<open>simp add: follow_mem_ps\<close>)
  moreover have "a \<in> set (follow T b)"
    by (subst follow_Some_ps[OF assms(1,3)]) (use assms(1) in \<open>simp add: follow_mem_ps\<close>)
  ultimately show False using ancestor_antisym[OF assms(1)] parent_spec_neq[OF assms(1,2)] by blast
qed

lemma abstract_edge_swap:
  assumes "stem_setup S0 rr VV ii jj pp k s" "0 < k" "prnt S0 pp = Some y0"
  shows "abstract_arb (update_tree S0 ii jj pp jn) = abstract_arb S0 - {{pp, y0}} \<union> {{ii, jj}}"
proof-
  interpret ss: stem_setup S0 rr VV ii jj pp k s by (rule assms(1))
  have ps: "parent_spec (prnt S0)" using ss.arb by (rule arb_invarD(2))
  define NP where "NP = (prnt S0 ++ ss.REV k)(pp \<mapsto> ss.s_pred k)"
  define ST where "ST = s ` {0..k}"
  define OFF where "OFF = {{z, w} |z w. z \<notin> ST \<and> prnt S0 z = Some w}"
  define SPINE where "SPINE = {{s t, s (Suc t)} |t. t < k}"
  have split: "{{z, w} |z w. T z = Some w}
      = {{z, w} |z w. z \<notin> ST \<and> T z = Some w} \<union> {{z, w} |z w. z \<in> ST \<and> T z = Some w}" for T
    by blast
  have revdom: "dom (ss.REV k) = s ` {0..<k}"
    unfolding ss.REV_def by (simp add: dom_map_of_conv_image_fst image_image)
  have spp: "s t \<noteq> pp" if "t < k" for t
    using that ss.inj ss.pathk[symmetric] by (auto simp: inj_on_eq_iff)
  have NP: "NP (s t) = Some (ss.s_pred t)" if "t \<le> k" for t
  proof(cases "t = k")
    case False
    with that have "ss.REV k (s t) = Some (ss.s_pred t)"
      unfolding ss.REV_def using ss.inj by (intro map_of_is_SomeI) (auto simp: distinct_map inj_on_def)
    with that False revdom spp[of t] show ?thesis by (auto simp: NP_def map_add_dom_app_simps)
  qed (simp add: NP_def ss.pathk)
  have "NP z = prnt S0 z" if "z \<notin> ST" for z
  proof-
    have "z \<notin> dom (ss.REV k)" "z \<noteq> pp" using that ss.pathk by (auto simp: revdom ST_def)
    then show ?thesis by (simp add: NP_def map_add_dom_app_simps)
  qed
  then have "{{z, w} |z w. z \<notin> ST \<and> NP z = Some w} = OFF" by (simp add: OFF_def cong: conj_cong)
  moreover have "{{z, w} |z w. z \<in> ST \<and> NP z = Some w} = {{s t, ss.s_pred t} |t. t \<le> k}"
    using NP by (fastforce simp: ST_def)
  moreover have "{{z, w} |z w. z \<in> ST \<and> prnt S0 z = Some w} = insert {pp, y0} SPINE"
    using assms(3) ss.pathk ss.pathS by (fastforce simp: ST_def SPINE_def le_less)
  moreover have "{pp, y0} \<notin> OFF" "{pp, y0} \<notin> SPINE"
    using assms(3) ss.pathk ss.pathS spp no_2cycle[OF ps] parent_spec_neq[OF ps]
    by (fastforce simp: OFF_def ST_def SPINE_def doubleton_eq_iff)+
  ultimately show ?thesis
    unfolding abstract_arb_def ss.update_tree_prnt[OF assms(2)] NP_def[symmetric] split[of NP] split[of "prnt S0"]
    using spine_reindex_gen[OF assms(2), of s jj] ss.path0
    by (simp add: ss.s_pred_def SPINE_def[symmetric] OFF_def[symmetric] Un_Diff)
qed

lemma abstract_reparent:
  assumes "parent_spec T" "T i = Some y0"
  shows "{{z, w} |z w. (T(i \<mapsto> j)) z = Some w} = {{z, w} |z w. T z = Some w} - {{i, y0}} \<union> {{i, j}}"
proof(intro equalityI subsetI)
  fix e assume "e \<in> {{z, w} |z w. (T(i \<mapsto> j)) z = Some w}"
  then obtain z w where "e = {z, w}" "(T(i \<mapsto> j)) z = Some w" by blast
  moreover have "T y0 \<noteq> Some i" using no_2cycle[OF assms] by blast
  ultimately show "e \<in> {{z, w} |z w. T z = Some w} - {{i, y0}} \<union> {{i, j}}"
    by (cases "z = i") (auto simp: doubleton_eq_iff)
next
  fix e assume "e \<in> {{z, w} |z w. T z = Some w} - {{i, y0}} \<union> {{i, j}}"
  then consider "e = {i, j}" | z w where "e = {z, w}" "T z = Some w" "{z, w} \<noteq> {i, y0}" by blast
  then show "e \<in> {{z, w} |z w. (T(i \<mapsto> j)) z = Some w}"
  proof cases
    case (2 z w)
    then have "z \<noteq> i" using assms(2) by auto
    with 2 show ?thesis by auto
  qed auto
qed

lemma swap_edge_axiom2:
  assumes "arb_invar r V S" "get_path_pair_impl S u v = (p1, p2)" "u \<noteq> v"
    "walk_betw (abstract_arb S) u (p1 @ a # p3) r" "distinct (p1 @ a # p3)"
    "(x, y) \<in> set (edges_of_vwalk (p1 @ [a]))" "u \<in> V" "v \<in> V"
  shows "abstract_arb (swap_edge_impl S x u v) = abstract_arb S - {{x, y}} \<union> {{u, v}}"
proof-
  note S = swap_edge_setup[OF assms(1,2,4-8)]
  obtain ss_s ss_k where SS: "stem_setup S r V u v x ss_k ss_s"
    by (rule pivot_stem_setup[OF assms(1,7,8) S(1,2) refl S(3)])
  interpret ss: stem_setup S r V u v x ss_k ss_s by (rule SS)
  show ?thesis
  proof(cases "0 < ss_k")
    case True
    then show ?thesis using abstract_edge_swap[OF SS True S(4)] by (simp add: swap_edge_impl_def)
  next
    case False
    then have "u = x" using ss.path0 ss.pathk by simp
    then show ?thesis
      using ss.move_prnt abstract_reparent[OF arb_invarD(2)[OF assms(1)] S(4), of v]
      by (simp add: swap_edge_impl_def abstract_arb_def)
  qed
qed

text \<open>All nine axioms are now available; the interpretation exhibits the built initial tree as a
      concrete @{locale arborescense_adt}.\<close>

interpretation Sarb_adt: arborescense_adt Varb vcount "arb_invar vcount Varb"
    abstract_arb get_path_pair_impl swap_edge_impl
  by unfold_locales
    (assumption | rule r_in_V graph_invar_abstract_arb general_axiom3 Vs_abstract_arb get_path_pair_axiom1
      get_path_pair_axiom2 swap_edge_axiom1 swap_edge_axiom2)+


section \<open>Big-M potential arithmetic: the pot\_value\_plus/minus specifications\<close>

text \<open>The abstract potential/reduced-cost descriptor is the tagged pair \<open>pval\<close>, read as
      \<open>pval_abstract bigM p = of_mtag (fst p) * bigM + snd p\<close>. With \<open>bigM\<close> chosen larger than
      \<open>6 * sum_list (map abs cost_list)\<close>, the ordinary parts of a potential (bounded by
      \<open>2 * sum_list (map abs cost_list)\<close>, \<open>pv_invar\<close>) and of a reduced cost (bounded by
      \<open>3 * sum_list (map abs cost_list)\<close>, \<open>rc_invar\<close>) are too small to disturb the
      big-M coefficient. Under the network-simplex guard (\<open>good_pot_val\<close>: the resulting value is a signed
      cost sum over augmented edges touching the root \<open>vcount\<close> at most once), the big-M coefficient of the
      result stays in \<open>{- 1, 0, 1}\<close>, so the clamping \<open>tag_add\<close> / \<open>tag_sub\<close> act
      faithfully. These are exactly the spec-level obligations \<open>pot_value_plus_spec\<close> /
      \<open>pot_value_minus_spec\<close> of the locale \<open>network_simplex_spec\<close>.\<close>

lemma of_mtag_mtag_of: "\<lbrakk>- 2 \<le> i; i \<le> 2\<rbrakk> \<Longrightarrow> of_mtag (mtag_of i) = i"
  by (auto simp: mtag_of_def)

lemma len_fst_list_m: "length fst_list = m"
  using length_fst length_edges by simp

lemma len_snd_list_m: "length snd_list = m"
  using length_snd length_edges by simp

lemma real_fst_lt_vcount: "e < m \<Longrightarrow> fst_all ! e < vcount"
  using fst_snd_vs by (auto simp: fst_all_real intro!: vs_less_vcount)

lemma real_snd_lt_vcount: "e < m \<Longrightarrow> snd_all ! e < vcount"
  using fst_snd_vs by (auto simp: snd_all_real intro!: vs_less_vcount)

text \<open>For an augmented edge, touching the artificial root @{term vcount} is exactly being an
      artificial edge (index @{term "e \<ge> m"}).\<close>

lemma touches_root_iff:
  assumes "e < m + Kart" shows "(fst_all ! e = vcount \<or> snd_all ! e = vcount) \<longleftrightarrow> \<not> e < m"
proof(cases "e < m")
  case False
  then obtain k where "e = m + k" "k < Kart" using assms le_Suc_ex[of m e] by auto
  with tail_edge_ok_build_tree[of k] show ?thesis
    by (auto simp: tail_edge_ok_def fst_all_art snd_all_art split: if_splits)
qed (use real_fst_lt_vcount[of e] real_snd_lt_vcount[of e] in auto)

lemma cost_all_art': "\<lbrakk>m \<le> e; e < m + Kart\<rbrakk> \<Longrightarrow> cost_all ! e = bigM"
  using cost_all_art[of "e - m"] by simp

lemma h_abs: "h \<bar>a\<bar> = \<bar>h a\<bar>"
  by (cases "0 \<le> a") auto

lemma h_of_nat [simp]: "h (of_nat nn) = of_nat nn"
  by (induction nn) (simp_all add: h_add)

lemma h_numeral [simp]: "h (numeral k) = numeral k"
  using h_of_nat[of "numeral k"] by simp

lemma real_diff_bound:
  assumes "A \<subseteq> {0..<m}" "D \<subseteq> {0..<m}"
  shows "\<bar>(\<Sum>e\<in>A. cost_list ! e) - (\<Sum>e\<in>D. cost_list ! e)\<bar>
    \<le> sum_list (map abs cost_list)"
proof-
  have "\<bar>(\<Sum>e\<in>A. cost_list ! e) - (\<Sum>e\<in>D. cost_list ! e)\<bar>
      = \<bar>\<Sum>e\<in>{0..<m}. (if e \<in> A then cost_list ! e else 0)
          - (if e \<in> D then cost_list ! e else 0)\<bar>"
    using assms by (simp add: sum_subtractf sum.inter_restrict[symmetric] Int_absorb1)
  also have "\<dots> \<le> (\<Sum>e\<in>{0..<m}. \<bar>(if e \<in> A then cost_list ! e else 0)
      - (if e \<in> D then cost_list ! e else 0)\<bar>)"
    by (rule sum_abs)
  also have "\<dots> \<le> (\<Sum>e\<in>{0..<m}. \<bar>cost_list ! e\<bar>)" by (rule sum_mono) auto
  finally show ?thesis by (simp add: sum_list_sum_nth)
qed

lemma cost_decompose:
  assumes "A \<subseteq> {0..<m + Kart}" "D \<subseteq> {0..<m + Kart}"
    "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1"
  shows "\<exists>\<epsilon> R. \<epsilon> \<in> {- 1, 0, 1}
    \<and> \<bar>R\<bar> \<le> h (sum_list (map abs cost_list))
    \<and> (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e) = real_of_int \<epsilon> * bigM + R"
proof-
  let ?art = "{m..<m + Kart}" and ?c = "\<lambda>S. \<Sum>e\<in>S \<inter> {0..<m}. cost_list ! e"
  have S: "(\<Sum>e\<in>S. cost_all ! e) = h (?c S) + real (card (S \<inter> ?art)) * bigM"
    if "S \<subseteq> {0..<m + Kart}" for S
  proof-
    have "S - {0..<m} = S \<inter> ?art" using that by auto
    then show ?thesis using sum.Int_Diff[OF finite_subset[OF that], of "(!) cost_all" "{0..<m}"]
      by (simp add: cost_all_real cost_all_art' h_sum)
  qed
  have "(fst_all ! e = vcount \<or> snd_all ! e = vcount) \<longleftrightarrow> e \<in> ?art"
    if "e \<in> A \<union> D" for e
    using that assms(1,2) touches_root_iff[of e] by auto
  then have "{e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} = (A \<union> D) \<inter> ?art"
    by blast
  then have "card ((A \<union> D) \<inter> ?art) \<le> 1" using assms(3) by simp
  moreover have "card (A \<inter> ?art) \<le> card ((A \<union> D) \<inter> ?art)"
      "card (D \<inter> ?art) \<le> card ((A \<union> D) \<inter> ?art)"
    by (intro card_mono; auto)+
  ultimately have "card (A \<inter> ?art) \<le> 1" "card (D \<inter> ?art) \<le> 1" by linarith+
  moreover have "\<bar>h (?c A) - h (?c D)\<bar> \<le> h (sum_list (map abs cost_list))"
    using real_diff_bound[of "A \<inter> {0..<m}" "D \<inter> {0..<m}"] by (simp add: h_abs[symmetric] flip: h_diff)
  ultimately show ?thesis
    by (intro exI[of _ "int (card (A \<inter> ?art)) - int (card (D \<inter> ?art))"] exI[of _ "h (?c A) - h (?c D)"])
      (auto simp: S assms(1,2) le_Suc_eq algebra_simps)
qed

definition pv_invar :: "mtag \<times> 'n \<Rightarrow> bool" where
  "pv_invar p \<longleftrightarrow> \<bar>snd p\<bar> \<le> 2 * sum_list (map abs cost_list)"

definition rc_invar :: "mtag \<times> 'n \<Rightarrow> bool" where
  "rc_invar g \<longleftrightarrow> \<bar>snd g\<bar> \<le> 3 * sum_list (map abs cost_list)"

lemma sabs_nonneg: "0 \<le> sum_list (map abs cost_list)"
  by (rule sum_list_nonneg) auto

lemma bigM_pos: "bigM > 0"
  using h_nonneg[OF sabs_nonneg] unfolding bigM_def by linarith

lemma h_pv_bound: "pv_invar p \<Longrightarrow> \<bar>h (snd p)\<bar> \<le> 2 * h (sum_list (map abs cost_list))"
  using h_mono[of "\<bar>snd p\<bar>" "2 * sum_list (map abs cost_list)"] by (simp add: pv_invar_def h_abs h_mult)

lemma h_rc_bound: "rc_invar g \<Longrightarrow> \<bar>h (snd g)\<bar> \<le> 3 * h (sum_list (map abs cost_list))"
  using h_mono[of "\<bar>snd g\<bar>" "3 * sum_list (map abs cost_list)"] by (simp add: rc_invar_def h_abs h_mult)

text \<open>The big-M coefficient of a value is unique as long as the ordinary parts stay below
      @{term bigM}; under the guard, a clamped tag operation therefore acts faithfully.\<close>

lemma bigM_unique:
  assumes "real_of_int c * bigM + x = real_of_int \<epsilon> * bigM + R" "\<epsilon> \<in> {- 1, 0, 1}"
    "\<bar>x\<bar> \<le> 5 * h (sum_list (map abs cost_list))" "\<bar>R\<bar> \<le> h (sum_list (map abs cost_list))"
  shows "of_mtag (mtag_of c) = c" "x = R"
proof-
  define d where "d = c - \<epsilon>"
  have "R - x = real_of_int d * bigM" using assms(1) by (simp add: d_def algebra_simps)
  moreover have "\<bar>R - x\<bar> < bigM" using assms(3,4) unfolding bigM_def abs_le_iff abs_less_iff by linarith
  ultimately have "\<bar>real_of_int d\<bar> < 1" using bigM_pos by (simp add: abs_mult)
  then have "\<bar>d\<bar> < 1" by (simp only: of_int_abs[symmetric] of_int_less_1_iff)
  then have "c = \<epsilon>" unfolding d_def abs_less_iff by linarith
  then show "of_mtag (mtag_of c) = c" "x = R" using assms(1,2) by (auto simp: of_mtag_mtag_of)
qed

lemma pot_plus_faithful:
  assumes "pv_invar p" "rc_invar g"
    "\<exists>A D. A \<subseteq> {0..<m + Kart} \<and> D \<subseteq> {0..<m + Kart}
       \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1
       \<and> pval_abstract bigM p + pval_abstract bigM g
         = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)"
  shows "pval_abstract bigM (pval_plus p g) = pval_abstract bigM p + pval_abstract bigM g
         \<and> pv_invar (pval_plus p g)"
proof-
  obtain A D where AD: "A \<subseteq> {0..<m + Kart}" "D \<subseteq> {0..<m + Kart}"
      "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1"
      "pval_abstract bigM p + pval_abstract bigM g = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)"
    using assms(3) by blast
  obtain \<epsilon> R where "\<epsilon> \<in> {- 1, 0, 1}" "\<bar>R\<bar> \<le> h (sum_list (map abs cost_list))"
      "pval_abstract bigM p + pval_abstract bigM g = real_of_int \<epsilon> * bigM + R"
    using cost_decompose[OF AD(1-3)] AD(4) by auto
  moreover have "\<bar>h (snd p) + h (snd g)\<bar> \<le> 5 * h (sum_list (map abs cost_list))"
    using h_pv_bound[OF assms(1)] h_rc_bound[OF assms(2)] unfolding abs_le_iff by linarith
  ultimately have "of_mtag (tag_add (fst p) (fst g)) = of_mtag (fst p) + of_mtag (fst g)"
      "h \<bar>snd p + snd g\<bar> \<le> h (sum_list (map abs cost_list))"
    using bigM_unique[of "of_mtag (fst p) + of_mtag (fst g)" "h (snd p) + h (snd g)" \<epsilon> R]
    by (simp_all add: tag_add_def pval_abstract_def algebra_simps h_add h_abs)
  then show ?thesis using sabs_nonneg
    by (simp add: pval_abstract_def pval_plus_def pv_invar_def h_add algebra_simps)
qed

lemma pot_minus_faithful:
  assumes "pv_invar p" "rc_invar g"
    "\<exists>A D. A \<subseteq> {0..<m + Kart} \<and> D \<subseteq> {0..<m + Kart}
       \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1
       \<and> pval_abstract bigM p - pval_abstract bigM g
         = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)"
  shows "pval_abstract bigM (pval_minus p g) = pval_abstract bigM p - pval_abstract bigM g
         \<and> pv_invar (pval_minus p g)"
proof-
  obtain A D where AD: "A \<subseteq> {0..<m + Kart}" "D \<subseteq> {0..<m + Kart}"
      "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1"
      "pval_abstract bigM p - pval_abstract bigM g = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)"
    using assms(3) by blast
  obtain \<epsilon> R where "\<epsilon> \<in> {- 1, 0, 1}" "\<bar>R\<bar> \<le> h (sum_list (map abs cost_list))"
      "pval_abstract bigM p - pval_abstract bigM g = real_of_int \<epsilon> * bigM + R"
    using cost_decompose[OF AD(1-3)] AD(4) by auto
  moreover have "\<bar>h (snd p) - h (snd g)\<bar> \<le> 5 * h (sum_list (map abs cost_list))"
    using h_pv_bound[OF assms(1)] h_rc_bound[OF assms(2)] unfolding abs_le_iff by linarith
  ultimately have "of_mtag (tag_sub (fst p) (fst g)) = of_mtag (fst p) - of_mtag (fst g)"
      "h \<bar>snd p - snd g\<bar> \<le> h (sum_list (map abs cost_list))"
    using bigM_unique[of "of_mtag (fst p) - of_mtag (fst g)" "h (snd p) - h (snd g)" \<epsilon> R]
    by (simp_all add: tag_sub_def pval_abstract_def algebra_simps h_abs)
  then show ?thesis using sabs_nonneg
    by (simp add: pval_abstract_def pval_minus_def pv_invar_def) (simp add: algebra_simps)
qed

subsection \<open>Obligation 11 (init\_pot\_fits): reduced cost 0 on every tree edge\<close>

text \<open>An interior tree vertex's parent edge is a real free edge; by the potential recursion @{thm build_tree_pot}
      its reduced cost is zero. A component root @{term c} (\<open>prnt = vcount\<close>) hangs at the artificial edge
      @{term \<open>ds_par (build_tree acyc_flow) ! c - m\<close>} with cost @{term bigM}, and its seed potential
      \<open>\<plusminus> bigM\<close> cancels that cost. The carried invariant \<open>comproot_inv\<close> records the
      seed data; @{const build_dfs} freezes it for every existing component root (\<open>build_dfs_cr\<close>).\<close>

lemma len_pot_bt: "length (ds_pot (build_tree acyc_flow)) = Suc vcount"
  using build_tree_inv by (simp add: dfs_inv_def dfs_sized_def)

lemma plook_pot: "v < Suc vcount
  \<Longrightarrow> nth (ds_pot (build_tree acyc_flow)) v = ds_pot (build_tree acyc_flow) ! v"
  by simp

lemma pval_plus_M0: "pval_abstract bigM (pval_plus x (M_0, s)) = pval_abstract bigM x + h s"
  by (cases "fst x") (simp_all add: pval_abstract_def pval_plus_def tag_add_def mtag_of_def h_add)

lemma bd_upd1_cr:
  assumes "dfs_inv fl s" "bd_call1_conds fl s" "x < vcount" "ds_seen (bd_upd1 fl s) ! x"
    "ds_prnt (bd_upd1 fl s) ! x = vcount"
  shows "ds_seen s ! x \<and> ds_prnt s ! x = vcount
         \<and> ds_par (bd_upd1 fl s) ! x = ds_par s ! x \<and> ds_pot (bd_upd1 fl s) ! x = ds_pot s ! x"
proof-
  have "dfs_wf fl s" using assms(1) by (simp add: dfs_inv_def)
  then obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount"
    "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr> else dfs_discover
        (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    using assms(2) by (rule bd_upd1_eq)
  moreover from this(1) have "v < vcount" using \<open>dfs_wf fl s\<close> stkverts_props[of fl s v]
    by (simp add: stkverts_def)
  ultimately show ?thesis
    using assms(1,4,5) by (auto simp: dfs_discover_def dfs_push_def Let_def dfs_inv_def dfs_sized_def nth_list_update
        split: if_splits)
qed

lemma bd_upd2_cr:
  assumes "dfs_inv fl s" "bd_call2_conds fl s" "x < vcount" "ds_seen (bd_upd2 fl s) ! x"
    "ds_prnt (bd_upd2 fl s) ! x = vcount"
  shows "ds_seen s ! x \<and> ds_prnt s ! x = vcount
         \<and> ds_par (bd_upd2 fl s) ! x = ds_par s ! x \<and> ds_pot (bd_upd2 fl s) ! x = ds_pot s ! x"
proof-
  have "dfs_wf fl s" using assms(1) by (simp add: dfs_inv_def)
  then obtain v rest e w c' where "ds_stk s = v # rest" "w < vcount"
    "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr> else dfs_discover
        (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    using assms(2) by (rule bd_upd2_eq)
  moreover from this(1) have "v < vcount" using \<open>dfs_wf fl s\<close> stkverts_props[of fl s v]
    by (simp add: stkverts_def)
  ultimately show ?thesis
    using assms(1,4,5) by (auto simp: dfs_discover_def dfs_push_def Let_def dfs_inv_def dfs_sized_def nth_list_update
        split: if_splits)
qed

lemma bd_upd3_cr:
  "\<lbrakk>bd_call3_conds fl s; ds_seen (bd_upd3 s) ! x; ds_prnt (bd_upd3 s) ! x = vcount\<rbrakk> \<Longrightarrow>
    ds_seen s ! x \<and> ds_prnt s ! x = vcount \<and> ds_par (bd_upd3 s) ! x = ds_par s ! x
        \<and> ds_pot (bd_upd3 s) ! x = ds_pot s ! x"
  by (erule bd_upd3_eq) (simp add: dfs_finish_def Let_def)

lemma build_dfs_cr:
  assumes "build_dfs_dom (fl, s)" "dfs_inv fl s" "x < vcount" "ds_seen (build_dfs fl s) ! x"
    "ds_prnt (build_dfs fl s) ! x = vcount"
  shows "ds_seen s ! x \<and> ds_prnt s ! x = vcount
         \<and> ds_par (build_dfs fl s) ! x = ds_par s ! x \<and> ds_pot (build_dfs fl s) ! x = ds_pot s ! x"
proof-
  let ?Q = "\<lambda>t. \<forall>x<vcount. ds_seen t ! x \<longrightarrow> ds_prnt t ! x = vcount
      \<longrightarrow> ds_seen s ! x \<and> ds_prnt s ! x = vcount
    \<and> ds_par t ! x = ds_par s ! x \<and> ds_pot t ! x = ds_pot s ! x"
  have "?Q (build_dfs fl s)"
  proof(rule build_dfs_preserve[OF assms(1,2)])
    fix fl t assume "dfs_inv fl t" "?Q t"
    then show "bd_call1_conds fl t \<Longrightarrow> ?Q (bd_upd1 fl t)"
      "bd_call2_conds fl t \<Longrightarrow> ?Q (bd_upd2 fl t)" "bd_call3_conds fl t \<Longrightarrow> ?Q (bd_upd3 t)"
      by (simp_all add: bd_upd1_cr bd_upd2_cr bd_upd3_cr)
  qed simp
  then show ?thesis using assms(3-5) by blast
qed

definition comproot_edge_ok :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> bool" where
  "comproot_edge_ok s c \<longleftrightarrow>
     m \<le> ds_par s ! c \<and> ds_par s ! c - m < ds_nxt s
     \<and> ds_pot s ! c = (if art_dir c then pval_negM else pval_M)
     \<and> ds_afst s ! (ds_par s ! c - m) = (if art_dir c then c else vcount)
     \<and> ds_asnd s ! (ds_par s ! c - m) = (if art_dir c then vcount else c)"

definition comproot_inv :: "'n dfs_state \<Rightarrow> bool" where
  "comproot_inv s \<longleftrightarrow> (\<forall>c<vcount. ds_seen s ! c \<longrightarrow> ds_prnt s ! c = vcount
      \<longrightarrow> comproot_edge_ok s c)"

lemma emit_U_edge_cri: "comproot_inv s \<Longrightarrow> comproot_inv (emit_U_edge s v)"
  by (auto simp: comproot_inv_def comproot_edge_ok_def emit_U_edge_def Let_def)

lemma open_tree_component_cri:
  assumes "dfs_inv acyc_flow s" "c < vcount" "\<not> ds_seen s ! c" "c \<noteq> 0" "ds_stk s = []" "art_len s"
    "ds_nxt s < length vs_list" "comproot_inv s"
  shows "comproot_inv (open_tree_component acyc_flow s c)"
proof-
  have W: "dfs_wf acyc_flow s" "dfs_sized s" using assms(1) by (simp_all add: dfs_inv_def)
  obtain sd where sd: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd" "build_dfs_dom (acyc_flow, sd)"
      "dfs_inv acyc_flow sd" "ds_nxt sd = Suc (ds_nxt s)" "ds_seen sd = (ds_seen s)[c := True]"
      "ds_prnt sd = (ds_prnt s)[c := vcount]" "ds_par sd = (ds_par s)[c := m + ds_nxt s]"
      "ds_pot sd = (ds_pot s)[c := (if art_dir c then pval_negM else pval_M)]"
      "ds_afst sd = (ds_afst s)[ds_nxt s := (if art_dir c then c else vcount)]"
      "ds_asnd sd = (ds_asnd s)[ds_nxt s := (if art_dir c then vcount else c)]"
    by (rule open_tree_component_seed[OF W assms(2)]) (use assms(1,3-5) in blast)
  have L: "length (ds_par s) = Suc vcount" "length (ds_pot s) = Suc vcount"
    "length (ds_afst s) = length vs_list" "length (ds_asnd s) = length vs_list"
    using W(2) assms(6) by (simp_all add: dfs_sized_def art_len_def)
  show ?thesis
    unfolding comproot_inv_def sd(1)
  proof(intro allI impI)
    fix w assume "w < vcount" "ds_seen (build_dfs acyc_flow sd) ! w" "ds_prnt (build_dfs acyc_flow sd) ! w = vcount"
    with build_dfs_cr[OF sd(2,3)] have "ds_seen sd ! w" "ds_prnt sd ! w = vcount"
      "ds_par (build_dfs acyc_flow sd) ! w = ds_par sd ! w" "ds_pot (build_dfs acyc_flow sd) ! w = ds_pot sd ! w"
      by auto
    then show "comproot_edge_ok (build_dfs acyc_flow sd) w"
      using \<open>w < vcount\<close> assms(2,7,8) L build_dfs_art[OF sd(2)] sd(4-10)
      by (cases "w = c") (auto simp: comproot_inv_def comproot_edge_ok_def nth_list_update)
  qed
qed

lemma phase1_step_cri:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; ds_stk s = []; art_len s; comproot_inv s;
    ds_nxt (phase1_step acyc_flow v s) \<le> length vs_list\<rbrakk>
        \<Longrightarrow> comproot_inv (phase1_step acyc_flow v s)"
  using vs_less_vcount[of v] no_zero_node open_tree_component_art(1)[of acyc_flow s v]
  by (cases "v = 0") (auto simp: phase1_step_def emit_U_edge_cri intro!: open_tree_component_cri)

lemma phase2_step_cri:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; ds_stk s = []; art_len s; comproot_inv s;
    ds_nxt (phase2_step acyc_flow v s) \<le> length vs_list\<rbrakk>
        \<Longrightarrow> comproot_inv (phase2_step acyc_flow v s)"
  using vs_less_vcount[of v] no_zero_node open_tree_component_art(1)[of acyc_flow s v]
  by (cases "v = 0") (auto simp: phase2_step_def intro!: open_tree_component_cri)

text \<open>Along the phases we carry \<open>comproot_inv\<close> only while the emission cursor stays inside the
      tails; @{thm build_tree_nxt_le} shows at the end that it always did.\<close>

lemma build_tree_comproot_inv: "comproot_inv (build_tree acyc_flow)"
proof-
  let ?Q = "\<lambda>s. art_len s \<and> (ds_nxt s \<le> length vs_list \<longrightarrow> comproot_inv s)"
  have "?Q (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
  proof(rule phases_preserve[where Q = ?Q])
    fix v s assume "v \<in> set vs_list" "dfs_inv acyc_flow s \<and> ds_stk s = []" "?Q s"
    then show "?Q (phase1_step acyc_flow v s)" "?Q (phase2_step acyc_flow v s)"
      using phase1_step_nxt[of s v] phase2_step_nxt2[of s v] vs_less_vcount[of v]
      by (auto simp: phase1_step_art_len phase2_step_art_len intro: phase1_step_cri phase2_step_cri)
  qed (use dfs_init_art_len in \<open>simp add: comproot_inv_def dfs_init_def del: replicate_Suc\<close>)
  then show ?thesis
    using build_tree_nxt_le by (simp add: build_tree_def Let_def comproot_inv_def comproot_edge_ok_def)
qed

lemma build_tree_rc_zero:
  assumes "w < vcount" "ds_seen (build_tree acyc_flow) ! w"
  shows "cost_all ! (ds_par (build_tree acyc_flow) ! w)
    + pval_abstract bigM (nth (ds_pot (build_tree acyc_flow)) (fst_all ! (ds_par (build_tree acyc_flow) ! w)))
    - pval_abstract bigM (nth (ds_pot (build_tree acyc_flow)) (snd_all ! (ds_par (build_tree acyc_flow) ! w))) = 0"
proof(cases "ds_prnt (build_tree acyc_flow) ! w < vcount")
  case True
  have "ds_prnt (build_tree acyc_flow) ! w \<noteq> w"
    using parent_spec_neq[OF parent_spec_Sprnt, of w] assms by (auto simp: Sprnt_def Vseen_def)
  with build_tree_par_edge[OF assms True] build_tree_pot[OF assms True] show ?thesis
    by (cases "ds_dir (build_tree acyc_flow) ! w") (auto simp: pval_plus_M0 cost_all_real fst_all_real snd_all_real)
next
  case False
  then have "ds_prnt (build_tree acyc_flow) ! w = vcount"
    using build_tree_inv[of acyc_flow] assms by (auto simp: dfs_inv_def tree_seen_inv_def)
  then have "comproot_edge_ok (build_tree acyc_flow) w" using build_tree_comproot_inv assms
      by (simp add: comproot_inv_def)
  moreover define k where "k = ds_par (build_tree acyc_flow) ! w - m"
  ultimately have "ds_par (build_tree acyc_flow) ! w = m + k" "k < Kart"
    "ds_pot (build_tree acyc_flow) ! w = (if art_dir w then pval_negM else pval_M)"
    "ds_afst (build_tree acyc_flow) ! k = (if art_dir w then w else vcount)"
    "ds_asnd (build_tree acyc_flow) ! k = (if art_dir w then vcount else w)"
    by (auto simp: comproot_edge_ok_def Kart_def)
  then show ?thesis
    using build_tree_root_pot[of acyc_flow]
    by (cases "art_dir w") (simp_all add: cost_all_art fst_all_art snd_all_art pval_abstract_def pval_negM_def
        pval_M_def pval_zero_def)
qed

subsection \<open>Assembly substrate: seen vertices are real vertices
  (@{term \<open>Vseen = original_network.\<V>\<close>})\<close>

text \<open>Every vertex the builder marks \<^emph>\<open>seen\<close> is an edge endpoint: a discovery marks a
      free-edge endpoint, and a component root is opened only for a vertex of nonzero @{const imbalance}, which carries
      an edge (a name without edges, @{const is_lonely}, has zero @{const excess} and zero balance by
      @{thm isolated_zero}). Conversely every edged vertex is spanned, so the seen set is exactly the vertex set of the
      original network.\<close>

lemma excess_lonely:
  assumes "v \<in> set vs_list" "is_lonely v" shows "excess ! v = 0"
proof-
  have "fst_list ! e \<noteq> v" "snd_list ! e \<noteq> v" if "e < m" for e
    using that assms by (auto simp: is_lonely_iff)
  then show ?thesis using vs_less_vcount[OF assms(1)] by (simp add: excess_nth flip: sum_set_upt_conv_sum_list_nat)
qed

lemma nth_vs_list: "i < n \<Longrightarrow> vs_list ! i = Suc i"
  using map_Suc_upt[of 0 n] by (simp add: vs_list_def del: upt_Suc)

lemma foldl_scatter_hit:
  "\<lbrakk>distinct (map fst ps); (k, x) \<in> set ps; k < length init\<rbrakk> \<Longrightarrow>
    foldl (\<lambda> arr (v, y). arr[v := y]) init ps ! k = x"
proof(induct ps arbitrary: init)
  case (Cons p ps)
  obtain v y where p: "p = (v, y)" by fastforce
  show ?case
  proof(cases "k = v")
    case True
    have "x = y" using Cons.prems(1,2) p True by (force simp: image_iff)
    moreover have "foldl (\<lambda> arr (v, y). arr[v := y]) (init[v := y]) ps ! k = init[v := y] ! k"
      using Cons.prems(1) p True by (intro foldl_scatter_miss) (force simp: image_iff)
    ultimately show ?thesis using True Cons.prems(3) p by simp
  qed (use Cons p in auto)
qed simp

lemma b_lookup_nth:
  assumes "v \<in> set vs_list" shows "b_lookup v = b_list ! (v - 1)"
proof-
  have "v - 1 < n" "Suc (v - 1) = v" using assms by (auto simp: set_vs_list)
  then have "zip vs_list b_list ! (v - 1) = (v, b_list ! (v - 1))" using length_vs_list length_b nth_vs_list by simp
  then have "(v, b_list ! (v - 1)) \<in> set (zip vs_list b_list)"
    using nth_mem[of "v - 1" "zip vs_list b_list"] \<open>v - 1 < n\<close> length_vs_list length_b by simp
  then show ?thesis
    unfolding b_lookup_def b_arr_def using distinct_vs_list length_vs_list length_b vs_less_vcount[OF assms]
    by (intro foldl_scatter_hit) simp_all
qed

lemma lonely_imbalance_zero:
  "\<lbrakk>v \<in> set vs_list; is_lonely v\<rbrakk> \<Longrightarrow> imbalance ! v = 0"
  using isolated_zero[of "v - 1"]
  by (auto simp: imbalance_nth vs_less_vcount excess_lonely b_lookup_nth is_lonely_iff set_vs_list)

lemma imbalance_nz_edged: "\<lbrakk>v \<in> set vs_list; imbalance ! v \<noteq> 0\<rbrakk>
  \<Longrightarrow> v \<in> set fst_list \<union> set snd_list"
  using lonely_imbalance_zero is_lonely_iff by blast

lemma nth_update_True: "xs[i := True] ! y \<Longrightarrow> y = i \<or> xs ! y"
  by (cases "y = i") auto

definition seen_sub :: "'n dfs_state \<Rightarrow> bool" where
  "seen_sub s \<longleftrightarrow> (\<forall>y<vcount. ds_seen s ! y
      \<longrightarrow> y \<in> set fst_list \<union> set snd_list)"

lemma bd_upd1_seen_sub:
  assumes "dfs_inv fl s" "bd_call1_conds fl s" "seen_sub s"
  shows "seen_sub (bd_upd1 fl s)"
proof-
  have "dfs_wf fl s" using assms(1) by (simp add: dfs_inv_def)
  then obtain v e w c' where "e < m" "snd_list ! e = w"
    "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr> else dfs_discover
        (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    using assms(2) by (rule bd_upd1_eq)
  then show ?thesis
    using assms(3) by (auto simp: seen_sub_def dfs_discover_def dfs_push_def Let_def dest!: nth_update_True)
qed

lemma bd_upd2_seen_sub:
  assumes "dfs_inv fl s" "bd_call2_conds fl s" "seen_sub s"
  shows "seen_sub (bd_upd2 fl s)"
proof-
  have "dfs_wf fl s" using assms(1) by (simp add: dfs_inv_def)
  then obtain v e w c' where "e < m" "fst_list ! e = w"
    "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr> else dfs_discover
        (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    using assms(2) by (rule bd_upd2_eq)
  then show ?thesis
    using assms(3) by (auto simp: seen_sub_def dfs_discover_def dfs_push_def Let_def dest!: nth_update_True)
qed

lemma bd_upd3_seen_sub: "\<lbrakk>bd_call3_conds fl s; seen_sub s\<rbrakk> \<Longrightarrow> seen_sub (bd_upd3 s)"
  by (erule bd_upd3_eq) (simp add: seen_sub_def dfs_finish_def Let_def)

lemma build_dfs_seen_sub: "\<lbrakk>build_dfs_dom (fl, s); dfs_inv fl s; seen_sub s\<rbrakk>
  \<Longrightarrow> seen_sub (build_dfs fl s)"
  by (rule build_dfs_preserve) (auto intro: bd_upd1_seen_sub bd_upd2_seen_sub bd_upd3_seen_sub)

lemma emit_U_edge_seen_sub: "seen_sub s \<Longrightarrow> seen_sub (emit_U_edge s v)"
  by (simp add: seen_sub_def emit_U_edge_def Let_def)

lemma open_tree_component_seen_sub:
  assumes "dfs_inv acyc_flow s" "c < vcount" "\<not> ds_seen s ! c" "c \<noteq> 0" "ds_stk s = []"
    "c \<in> set fst_list \<union> set snd_list" "seen_sub s"
  shows "seen_sub (open_tree_component acyc_flow s c)"
proof-
  have W: "dfs_wf acyc_flow s" "dfs_sized s" using assms(1) by (simp_all add: dfs_inv_def)
  obtain sd where "open_tree_component acyc_flow s c = build_dfs acyc_flow sd" "build_dfs_dom (acyc_flow, sd)"
      "dfs_inv acyc_flow sd" "ds_seen sd = (ds_seen s)[c := True]"
    by (rule open_tree_component_seed[OF W assms(2)]) (use assms(1,3-5) in blast)
  moreover from this(4) have "seen_sub sd" using assms(6,7) by (auto simp: seen_sub_def dest!: nth_update_True)
  ultimately show ?thesis by (simp add: build_dfs_seen_sub)
qed

lemma phase1_step_seen_sub:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; ds_stk s = []; seen_sub s\<rbrakk>
      \<Longrightarrow> seen_sub (phase1_step acyc_flow v s)"
  using vs_less_vcount[of v] no_zero_node imbalance_nz_edged[of v]
  by (cases "v = 0") (auto simp: phase1_step_def emit_U_edge_seen_sub intro!: open_tree_component_seen_sub)

lemma phase2_step_seen_sub:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; ds_stk s = []; seen_sub s\<rbrakk>
      \<Longrightarrow> seen_sub (phase2_step acyc_flow v s)"
  using vs_less_vcount[of v] no_zero_node not_lonely_edged[of v]
  by (cases "v = 0") (auto simp: phase2_step_def intro!: open_tree_component_seen_sub)

lemma build_tree_seen_sub: "seen_sub (build_tree acyc_flow)"
proof-
  have "seen_sub (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
    by (rule phases_preserve[where Q = seen_sub])
      (simp add: seen_sub_def dfs_init_def del: replicate_Suc, simp_all add: phase1_step_seen_sub phase2_step_seen_sub)
  then show ?thesis by (simp add: build_tree_def Let_def seen_sub_def)
qed

lemma V_sub_Vseen: "original_network.\<V> \<subseteq> Vseen"
proof
  fix v assume "v \<in> original_network.\<V>"
  then have "v \<in> set fst_list \<union> set snd_list" "v \<in> set vs_list"
      using fst_snd_vs by (auto simp: V_orig_eq)
  then show "v \<in> Vseen" using build_tree_spans edged_not_lonely vs_less_vcount by (simp add: Vseen_def)
qed

lemma Vseen_eq_V: "Vseen = original_network.\<V>"
  using build_tree_seen_sub V_sub_Vseen by (auto simp: V_orig_eq Vseen_def seen_sub_def)

subsection \<open>Assembly substrate: artificial-edge endpoints are seen vertices or the root\<close>

text \<open>Every stored artificial edge runs between the root @{const vcount} and an already visited vertex
      (a component root just opened, or a visited imbalanced vertex). Visitedness only grows, so this
      survives to @{const build_tree}, where the seen set is exactly @{const Vseen}. As for
      \<open>comproot_inv\<close>, the invariant is carried only while the cursor stays inside the tails.\<close>

definition seen_set :: "'n dfs_state \<Rightarrow> nat set" where
  "seen_set s = {v. v < vcount \<and> ds_seen s ! v}"

lemma seen_set_build_tree: "seen_set (build_tree acyc_flow) = Vseen"
  by (simp add: seen_set_def Vseen_def)

definition tail_sub :: "'n dfs_state \<Rightarrow> bool" where
  "tail_sub s \<longleftrightarrow> (\<forall>k<ds_nxt s. ds_afst s ! k \<in> insert vcount (seen_set s)
                              \<and> ds_asnd s ! k \<in> insert vcount (seen_set s))"

lemma emit_U_edge_tail_sub:
  "\<lbrakk>v < vcount; ds_seen s ! v; ds_nxt s < length vs_list; art_len s; tail_sub s\<rbrakk>
      \<Longrightarrow> tail_sub (emit_U_edge s v)"
  by (auto simp: tail_sub_def seen_set_def emit_U_edge_def Let_def art_len_def nth_list_update less_Suc_eq)

lemma open_tree_component_tail_sub:
  "\<lbrakk>dfs_inv acyc_flow s; v < vcount; ds_nxt s < length vs_list; art_len s; tail_sub s\<rbrakk>
    \<Longrightarrow> tail_sub (open_tree_component acyc_flow s v)"
  by (auto simp: tail_sub_def seen_set_def open_tree_component_art art_len_def nth_list_update less_Suc_eq
      open_tree_component_seen_mono open_tree_component_marks)

lemma phase1_step_tail_sub:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; art_len s; tail_sub s;
      ds_nxt (phase1_step acyc_flow v s) \<le> length vs_list\<rbrakk>
    \<Longrightarrow> tail_sub (phase1_step acyc_flow v s)"
  using vs_less_vcount[of v] open_tree_component_art(1)[of acyc_flow s v]
  by (auto simp: phase1_step_def emit_U_edge_nxt intro!: emit_U_edge_tail_sub open_tree_component_tail_sub)

lemma phase2_step_tail_sub:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; art_len s; tail_sub s;
      ds_nxt (phase2_step acyc_flow v s) \<le> length vs_list\<rbrakk>
    \<Longrightarrow> tail_sub (phase2_step acyc_flow v s)"
  using vs_less_vcount[of v] open_tree_component_art(1)[of acyc_flow s v]
  by (auto simp: phase2_step_def intro!: open_tree_component_tail_sub)

lemma build_tree_tail_sub: "tail_sub (build_tree acyc_flow)"
proof-
  let ?Q = "\<lambda>s. art_len s \<and> (ds_nxt s \<le> length vs_list \<longrightarrow> tail_sub s)"
  have "?Q (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
  proof(rule phases_preserve[where Q = ?Q])
    fix v s assume "v \<in> set vs_list" "dfs_inv acyc_flow s \<and> ds_stk s = []" "?Q s"
    then show "?Q (phase1_step acyc_flow v s)" "?Q (phase2_step acyc_flow v s)"
      using phase1_step_nxt[of s v] phase2_step_nxt2[of s v] vs_less_vcount[of v]
      by (auto simp: phase1_step_art_len phase2_step_art_len intro: phase1_step_tail_sub phase2_step_tail_sub)
  qed (use dfs_init_art_len in \<open>simp add: tail_sub_def dfs_init_def\<close>)
  then show ?thesis using build_tree_nxt_le by (simp add: build_tree_def Let_def tail_sub_def seen_set_def)
qed

lemma Kart_pos: "0 < Kart"
proof-
  have "fst_list ! 0 \<in> set vs_list" "fst_list ! 0 \<in> set fst_list" using num_edges_gtr_0 fst_snd_vs by auto
  then have "fst_list ! 0 < vcount" "ds_seen (build_tree acyc_flow) ! (fst_list ! 0)"
    using vs_less_vcount build_tree_spans edged_not_lonely by auto
  then have "(fst_list ! 0, vcount) \<in> (pstep (build_tree acyc_flow))\<^sup>+"
    using build_tree_reaches_root by (auto simp: rtrancl_eq_or_trancl)
  then obtain c where "(c, vcount) \<in> pstep (build_tree acyc_flow)" by (auto dest: tranclD2)
  then show ?thesis
    using build_tree_comproot_inv by (auto simp: pstep_def comproot_inv_def comproot_edge_ok_def Kart_def)
qed

section \<open>The interpretation layer: the augmented network as a @{locale network_simplex_spec}\<close>

text \<open>The simplex loop runs over the \<^emph>\<open>augmented\<close> edge set
      @{term \<open>{0..<m+Kart}\<close>} (real edges plus the @{term Kart} artificial big-@{term \<open>M\<close>}
      edges), read through the unified arrays @{const fst_all} / @{const snd_all} / @{const cap_all} /
      @{const cost_all}. Capacity decodes @{term \<open>- 1\<close>} as @{term \<open>\<infinity>\<close>}, and
      \<open>create_edge\<close> sends an out-of-range pair to a synthetic infinite-capacity edge.\<close>

lemma cap_all_nonneg: "e < m + Kart \<Longrightarrow> 0 \<le> cap_all ! e \<or> cap_all ! e = - 1"
proof(cases "e < m")
  case False
  moreover assume "e < m + Kart"
  ultimately obtain k where "e = m + k" "k < Kart" using le_Suc_ex[of m e] by auto
  then show ?thesis
    using tail_edge_ok_build_tree[of k] by (auto simp: cap_all_art tail_edge_ok_def art_tree_cap_def art_flow_def)
qed (use cap_neg nth_mem[of e capacity_list] length_edges in \<open>auto simp: cap_all_real\<close>)

interpretation NSg: cost_flow_network
  where \<E>           = "{0..<m+Kart}"
    and fst          = "\<lambda> e. if e < m+Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m+Kart)))"
    and snd          = "\<lambda> e. if e < m+Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m+Kart)))"
    and create_edge  = "\<lambda> u v. (m+Kart) + prod_encode (u, v)"
    and \<u>           = "\<lambda> e. if e < m+Kart then (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all
        ! e))) else \<infinity>"
    and \<c>           = "\<lambda> e. cost_all ! e"
  by unfold_locales (auto simp: zero_ereal_def num_edges_gtr_0 dest: cap_all_nonneg)

text \<open>The augmented graph's vertex set is the arborescence vertex set @{term Varb}: real edges contribute
      the seen vertices, artificial edges contribute @{const vcount} together with seen subjects, and
      @{thm Kart_pos} guarantees an artificial edge, so @{const vcount} itself is present.\<close>

lemma NSg_verts: "NSg.\<V> = insert vcount Vseen"
proof-
  have dvs: "NSg.\<V> = (\<Union>e\<in>{0..<m+Kart}. {fst_all!e, snd_all!e})"
      by (auto simp: dVs_def NSg.make_pair_function)
  have A: "{fst_all!e, snd_all!e} \<subseteq> insert vcount Vseen" if "e \<in> {0..<m+Kart}" for e
  proof(cases "e < m")
    case False
    then obtain k where "e = m + k" "k < Kart" using \<open>e \<in> {0..<m+Kart}\<close> le_Suc_ex[of m e] by auto
    then show ?thesis
      using build_tree_tail_sub by (simp add: tail_sub_def Kart_def seen_set_build_tree fst_all_art snd_all_art)
  qed (use Vseen_eq_V V_orig_eq in \<open>simp add: fst_all_real snd_all_real\<close>)
  have "vcount \<in> {fst_all ! m, snd_all ! m}"
    using Kart_pos tail_edge_ok_build_tree[of 0] fst_all_art[of 0] snd_all_art[of 0]
    by (auto simp: tail_edge_ok_def split: if_splits)
  then have "vcount \<in> NSg.\<V>" unfolding dvs using Kart_pos by (intro UN_I[of m]) auto
  moreover have "Vseen \<subseteq> NSg.\<V>"
  proof
    fix x assume "x \<in> Vseen"
    then consider i where "i < m" "x = fst_list ! i" | i where "i < m" "x = snd_list ! i"
      using Vseen_eq_V V_orig_eq by (auto simp: in_set_conv_nth)
    then show "x \<in> NSg.\<V>" unfolding dvs by cases (force simp flip: fst_all_real snd_all_real)+
  qed
  moreover have "NSg.\<V> \<subseteq> insert vcount Vseen" unfolding dvs by (rule UN_least[OF A])
  ultimately show ?thesis by blast
qed

lemma NSg_verts_Varb: "NSg.\<V> = Varb"
  using NSg_verts by (simp add: Varb_def)

end
end

