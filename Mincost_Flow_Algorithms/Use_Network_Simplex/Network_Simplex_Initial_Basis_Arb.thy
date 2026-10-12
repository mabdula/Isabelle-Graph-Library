theory Network_Simplex_Initial_Basis_Arb
  imports Network_Simplex_Initial_Basis_Correct
begin

context initial_basis_correct
begin

section \<open>Assembling the abstract arborescence from the finished tree\<close>

text \<open>The DFS produces five vertex-indexed arrays (@{const ds_prnt}, @{const ds_thrd}, @{const ds_rvth},
      @{const ds_lsuc}, @{const ds_snum}); here we read them off @{const build_tree} into the abstract
      @{typ \<open>nat ndtree\<close>} @{term Sarb}, with root @{term \<open>vcount\<close>} and vertex set @{term \<open>Varb\<close>}. The vertex
      set is based on the \<^emph>\<open>seen\<close> set @{term Vseen} (which coincides with the real vertices \<open>set vs_list\<close> ---
      a bridge deferred to the network-simplex layer); this makes @{const follow} over the parent map and
      @{const children} coincide \<^emph>\<open>directly\<close> with the array-level @{const pstep}/@{const desc} machinery of
      the correctness theory. We then discharge the @{const arb_invar} obligations (via @{thm arb_invarI})
      that do not require the explicit emission order; the thread-side ones are flagged at the end.\<close>

definition Vseen :: "nat set" where
  "Vseen = {y. y < vcount \<and> ds_seen (build_tree acyc_flow) ! y}"

definition Varb :: "nat set" where
  "Varb = insert vcount Vseen"

definition Sprnt :: "nat \<Rightarrow> nat option" where
  "Sprnt v = (if v \<in> Vseen then Some (ds_prnt (build_tree acyc_flow) ! v) else None)"

definition Sthrd :: "nat \<Rightarrow> nat option" where
  "Sthrd v = (if v \<in> Varb \<and> ds_thrd (build_tree acyc_flow) ! v \<noteq> 0 then Some (ds_thrd (build_tree acyc_flow) ! v) else None)"

definition Srvth :: "nat \<Rightarrow> nat option" where
  "Srvth v = (if v \<in> Varb \<and> ds_rvth (build_tree acyc_flow) ! v \<noteq> 0 then Some (ds_rvth (build_tree acyc_flow) ! v) else None)"

definition Sarb :: "nat ndtree" where
  "Sarb = \<lparr> prnt = Sprnt, thrd = Sthrd, rvth = Srvth,
            lsuc = (\<lambda>v. ds_lsuc (build_tree acyc_flow) ! v), snum = (\<lambda>v. ds_snum (build_tree acyc_flow) ! v) \<rparr>"

lemma Sarb_sel: "prnt Sarb = Sprnt" "thrd Sarb = Sthrd" "rvth Sarb = Srvth"
  "lsuc Sarb = (\<lambda>v. ds_lsuc (build_tree acyc_flow) ! v)" "snum Sarb = (\<lambda>v. ds_snum (build_tree acyc_flow) ! v)"
  by (simp_all add: Sarb_def)

lemma r_in_V: "vcount \<in> Varb" by (simp add: Varb_def)

lemma Vseen_finite: "finite Vseen"
  by (rule finite_subset[of _ "{..<vcount}"]) (auto simp: Vseen_def)

lemma pstep_eq_Sprnt: "pstep (build_tree acyc_flow) = {(x, y) |x y. Some y = Sprnt x}"
  by (auto simp: pstep_def Sprnt_def Vseen_def split: if_splits)

subsection \<open>Parent map: @{const parent_spec} via acyclicity of the parent step\<close>

text \<open>@{const parent_spec} of @{term \<open>prnt Sarb\<close>} is wellfoundedness of the parent relation, i.e.\
      acyclicity of @{term \<open>pstep (build_tree acyc_flow)\<close>} (child {\isasymrightarrow} parent). @{const pstep} is single-valued and every
      emitted vertex reaches the root through it (\<open>build_tree_reaches_root\<close>, I6), and the root has no
      outgoing parent step --- a single-valued relation in which every point reaches a sink has no cycle.\<close>

lemma orbit_returns:
  assumes sv: "single_valued R" and reach: "(a, b) \<in> R\<^sup>*" and cyc: "(a, a) \<in> R\<^sup>+"
  shows "(b, a) \<in> R\<^sup>*"
  using reach
proof (induct rule: rtrancl_induct)
  case base thus ?case by simp
next
  case (step b c)
  have "(b, a) \<in> R\<^sup>*" using step.hyps(3) .
  show ?case
  proof (cases "b = a")
    case True
    from cyc obtain d where "(a, d) \<in> R" "(d, a) \<in> R\<^sup>*" by (meson tranclD)
    hence "d = c" using step.hyps(2) True sv by (auto simp: single_valued_def)
    thus ?thesis using \<open>(d, a) \<in> R\<^sup>*\<close> by simp
  next
    case False
    from \<open>(b, a) \<in> R\<^sup>*\<close> False obtain d where "(b, d) \<in> R" "(d, a) \<in> R\<^sup>*"
      by (metis converse_rtranclE)
    hence "d = c" using step.hyps(2) sv by (auto simp: single_valued_def)
    thus ?thesis using \<open>(d, a) \<in> R\<^sup>*\<close> by simp
  qed
qed

lemma sink_no_cycle:
  assumes sv: "single_valued R" and reach: "(a, z) \<in> R\<^sup>*" and sink: "z \<notin> Domain R"
  shows "(a, a) \<notin> R\<^sup>+"
proof
  assume cyc: "(a, a) \<in> R\<^sup>+"
  have "(z, a) \<in> R\<^sup>*" using orbit_returns[OF sv reach cyc] .
  have "a \<in> Domain R" using cyc by (meson Domain.DomainI tranclD)
  hence "z \<in> Domain R"
    using \<open>(z, a) \<in> R\<^sup>*\<close> by (metis Domain.simps converse_rtranclE)
  thus False using sink by simp
qed

lemma pstep_acyclic: "acyclic (pstep (build_tree acyc_flow))"
  unfolding acyclic_def
proof (intro allI notI)
  fix x assume cyc: "(x, x) \<in> (pstep (build_tree acyc_flow))\<^sup>+"
  then obtain y where "(x, y) \<in> pstep (build_tree acyc_flow)" by (meson tranclD)
  hence xlt: "x < vcount" and xseen: "ds_seen (build_tree acyc_flow) ! x" by (auto simp: pstep_def)
  have "(x, vcount) \<in> (pstep (build_tree acyc_flow))\<^sup>*" using build_tree_reaches_root[OF xlt xseen] .
  moreover have "vcount \<notin> Domain (pstep (build_tree acyc_flow))" by (auto simp: pstep_def)
  ultimately show False using sink_no_cycle[OF pstep_single_valued] cyc by blast
qed

lemma sub_pstep: "{(x, y) |x y. Some x = Sprnt y}\<inverse> \<subseteq> pstep (build_tree acyc_flow)"
proof
  fix e assume "e \<in> {(x, y) |x y. Some x = Sprnt y}\<inverse>"
  then obtain x y where e: "e = (y, x)" and "Some x = Sprnt y" by auto
  hence "y \<in> Vseen" and "x = ds_prnt (build_tree acyc_flow) ! y" by (auto simp: Sprnt_def split: if_splits)
  thus "e \<in> pstep (build_tree acyc_flow)" using e by (auto simp: pstep_def Vseen_def)
qed

lemma parent_spec_Sprnt: "parent_spec Sprnt"
proof -
  let ?R = "{(x, y) |x y. Some x = Sprnt y}"
  have "acyclic (?R\<inverse>)" using acyclic_subset[OF pstep_acyclic sub_pstep] .
  hence acyc: "acyclic ?R" by (simp only: acyclic_converse)
  have fin: "finite ?R"
  proof -
    have "?R \<subseteq> (\<lambda>y. (ds_prnt (build_tree acyc_flow) ! y, y)) ` Vseen"
      by (auto simp: Sprnt_def split: if_splits)
    thus ?thesis by (meson Vseen_finite finite_imageI finite_subset)
  qed
  show ?thesis unfolding parent_spec_def using fin acyc by (rule finite_acyclic_wf)
qed

subsection \<open>Bridge: @{const follow} of the parent map is the @{const pstep} ancestor set\<close>

text \<open>A generic fact: under @{const parent_spec}, the root-path @{term \<open>follow T u\<close>} enumerates exactly the
      ancestors of @{term u} --- the reflexive-transitive closure of the one-step parent relation.\<close>

lemma follow_set_rtrancl:
  assumes ps: "parent_spec T"
  shows "set (follow T u) = {z. (u, z) \<in> {(x, y). T x = Some y}\<^sup>*}"
proof (induct u rule: wf_induct[OF ps[unfolded parent_spec_def]])
  case (1 u)
  let ?step = "{(x, y). T x = Some y}"
  show ?case
  proof (cases "T u")
    case None
    hence fu: "follow T u = [u]" using ps by (simp add: follow_ps_simps)
    have "z = u" if "(u, z) \<in> ?step\<^sup>*" for z
      using that None by (induct rule: rtrancl_induct) auto
    hence "{z. (u, z) \<in> ?step\<^sup>*} = {u}" by auto
    thus ?thesis using fu by simp
  next
    case (Some w)
    have fu: "follow T u = u # follow T w" using ps Some by (simp add: follow_ps_simps)
    have wu: "(w, u) \<in> {(x, y) |x y. Some x = T y}" using Some by auto
    have IH: "set (follow T w) = {z. (w, z) \<in> ?step\<^sup>*}" using "1.hyps"[rule_format, OF wu] by simp
    have setu: "{z. (u, z) \<in> ?step\<^sup>*} = insert u {z. (w, z) \<in> ?step\<^sup>*}"
    proof (intro equalityI subsetI)
      fix z assume "z \<in> {z. (u, z) \<in> ?step\<^sup>*}"
      hence "(u, z) \<in> ?step\<^sup>*" by simp
      thus "z \<in> insert u {z. (w, z) \<in> ?step\<^sup>*}"
      proof (induct rule: rtrancl_induct)
        case base thus ?case by simp
      next
        case (step y z)
        show ?case
        proof (cases "y = u")
          case True
          have "(u, z) \<in> {(x, y). T x = Some y}" using step.hyps(2) \<open>y = u\<close> by simp
          hence "z = w" using Some by auto
          thus ?thesis by simp
        next
          case False
          hence "(w, y) \<in> ?step\<^sup>*" using step.hyps(3) by simp
          hence "(w, z) \<in> ?step\<^sup>*" using step.hyps(2) by (simp add: rtrancl_into_rtrancl)
          thus ?thesis by simp
        qed
      qed
    next
      fix z assume z: "z \<in> insert u {z. (w, z) \<in> ?step\<^sup>*}"
      show "z \<in> {z. (u, z) \<in> ?step\<^sup>*}"
      proof (cases "z = u")
        case True thus ?thesis by simp
      next
        case False
        hence "(w, z) \<in> ?step\<^sup>*" using z by simp
        moreover have "(u, w) \<in> ?step" using Some by simp
        ultimately show ?thesis by (simp add: converse_rtrancl_into_rtrancl)
      qed
    qed
    thus ?thesis using fu IH by simp
  qed
qed

lemma follow_Sprnt_pstep: "set (follow Sprnt u) = {z. (u, z) \<in> (pstep (build_tree acyc_flow))\<^sup>*}"
proof -
  have "{(x, y). Sprnt x = Some y} = pstep (build_tree acyc_flow)" using pstep_eq_Sprnt by auto
  thus ?thesis using follow_set_rtrancl[OF parent_spec_Sprnt, of u] by simp
qed

lemma children_Sprnt_desc:
  assumes vs: "v \<in> Vseen" shows "children Sprnt v = desc (build_tree acyc_flow) v"
proof -
  have "children Sprnt v = {u. (u, v) \<in> (pstep (build_tree acyc_flow))\<^sup>*}"
    by (auto simp: children_def follow_Sprnt_pstep)
  also have "... = desc (build_tree acyc_flow) v"
  proof (intro equalityI subsetI)
    fix u assume "u \<in> {u. (u, v) \<in> (pstep (build_tree acyc_flow))\<^sup>*}"
    hence uv: "(u, v) \<in> (pstep (build_tree acyc_flow))\<^sup>*" by simp
    show "u \<in> desc (build_tree acyc_flow) v"
    proof (cases "u = v")
      case True thus ?thesis using vs by (auto simp: desc_def Vseen_def)
    next
      case False
      hence "(u, v) \<in> (pstep (build_tree acyc_flow))\<^sup>+" using uv by (metis rtranclD)
      then obtain z where "(u, z) \<in> pstep (build_tree acyc_flow)" by (meson tranclD)
      hence "u < vcount \<and> ds_seen (build_tree acyc_flow) ! u" by (auto simp: pstep_def)
      thus ?thesis using uv by (auto simp: desc_def)
    qed
  next
    fix u assume "u \<in> desc (build_tree acyc_flow) v"
    thus "u \<in> {u. (u, v) \<in> (pstep (build_tree acyc_flow))\<^sup>*}" by (auto simp: desc_def)
  qed
  finally show ?thesis .
qed

subsection \<open>@{const arb_invar} obligations discharged so far\<close>

text \<open>Root membership, the parent-map domain, the subtree-size obligation, and last-successor membership
      --- all on the interior (seen) vertices.\<close>

lemma dom_Sprnt: "dom Sprnt = Varb - {vcount}"
  by (auto simp: Sprnt_def Varb_def Vseen_def dom_def)

lemma snum_eq_children:
  assumes vs: "v \<in> Vseen" shows "snum Sarb v = card (children (prnt Sarb) v)"
proof -
  have "v < vcount" and "ds_seen (build_tree acyc_flow) ! v" using vs by (auto simp: Vseen_def)
  hence "ds_snum (build_tree acyc_flow) ! v = dcard (build_tree acyc_flow) v" using build_tree_snum by simp
  thus ?thesis using children_Sprnt_desc[OF vs] by (simp add: Sarb_sel dcard_def)
qed

lemma lsuc_in_V:
  assumes vs: "v \<in> Vseen" shows "lsuc Sarb v \<in> Varb"
proof -
  have "v < vcount" and "ds_seen (build_tree acyc_flow) ! v" using vs by (auto simp: Vseen_def)
  hence "ds_lsuc (build_tree acyc_flow) ! v \<in> desc (build_tree acyc_flow) v" using build_tree_lsuc by simp
  thus ?thesis by (auto simp: Sarb_sel desc_def Varb_def Vseen_def)
qed

subsection \<open>Thread spanning: the forward thread from the root visits every tree vertex\<close>

text \<open>The DFS builds the thread by \<^emph>\<open>append at the end\<close>: each @{const dfs_discover} /
      @{const open_tree_component} splices the new vertex after @{const ds_prev} and makes it the new
      @{const ds_prev}. Hence the forward-thread relation @{term thrdstep} only ever grows by one edge
      @{term \<open>(ds_prev s, w)\<close>} at the current last vertex, and the set of vertices reachable from the
      root @{term vcount} grows by exactly that new vertex. We carry this reachability invariant
      @{term tspan} through the whole build (alongside @{const dfs_inv}), giving \<^emph>\<open>thread spanning\<close> at
      @{const build_tree}. This is what makes the thread's @{const follow} enumerate all of @{term Varb}
      (obligation 4) and --- with injectivity --- makes the thread relation acyclic (obligations 2, 3).\<close>

definition thrdstep :: "'n dfs_state \<Rightarrow> (nat \<times> nat) set" where
  "thrdstep s = {(x, ds_thrd s ! x) |x. x < Suc vcount \<and> (x = vcount \<or> ds_seen s ! x) \<and> ds_thrd s ! x \<noteq> 0}"

lemma thrdstep_append:
  assumes inv: "dfs_inv fl s"
      and wlt: "w < vcount" and wnz: "w \<noteq> 0" and unseen: "\<not> ds_seen s ! w"
      and P_seen: "ds_seen t = (ds_seen s)[w := True]"
      and P_thrd: "ds_thrd t = (ds_thrd s)[ds_prev s := w]"
  shows "thrdstep t = insert (ds_prev s, w) (thrdstep s)"
proof -
  have thi: "thread_inv s" and sz: "dfs_sized s" using inv by (auto simp: dfs_inv_def)
  have lens: "length (ds_seen s) = Suc vcount" "length (ds_thrd s) = Suc vcount" using sz by (auto simp: dfs_sized_def)
  have pvlt: "ds_prev s < Suc vcount" and prevthrd: "ds_thrd s ! (ds_prev s) = 0"
    and pvmem: "ds_prev s = vcount \<or> ds_seen s ! (ds_prev s)" using thi by (auto simp: thread_inv_def)
  have wthrd0: "ds_thrd s ! w = 0" using thi wlt unseen by (auto simp: thread_inv_def)
  have wnotpv: "w \<noteq> ds_prev s" using unseen pvmem wlt by auto
  show ?thesis
  proof (intro equalityI subsetI)
    fix p assume "p \<in> thrdstep t"
    then obtain x where px: "p = (x, ds_thrd t ! x)" and xlt: "x < Suc vcount"
        and xmem: "x = vcount \<or> ds_seen t ! x" and xthrd: "ds_thrd t ! x \<noteq> 0" by (auto simp: thrdstep_def)
    show "p \<in> insert (ds_prev s, w) (thrdstep s)"
    proof (cases "x = ds_prev s")
      case True
      have "ds_thrd t ! x = w" using P_thrd True pvlt lens by (simp add: nth_list_update)
      thus ?thesis using px True by simp
    next
      case False
      have tx: "ds_thrd t ! x = ds_thrd s ! x" using P_thrd False by (simp add: nth_list_update)
      have sx: "ds_seen s ! x" if "x \<noteq> vcount"
      proof -
        have "ds_seen t ! x" using xmem that by simp
        moreover have "x \<noteq> w" using tx xthrd wthrd0 False by auto
        ultimately show ?thesis using P_seen by (simp add: nth_list_update)
      qed
      have "(x, ds_thrd s ! x) \<in> thrdstep s" using xlt xmem sx tx xthrd by (auto simp: thrdstep_def)
      thus ?thesis using px tx by simp
    qed
  next
    fix p assume "p \<in> insert (ds_prev s, w) (thrdstep s)"
    thus "p \<in> thrdstep t"
    proof
      assume "p = (ds_prev s, w)"
      moreover have "ds_thrd t ! (ds_prev s) = w" using P_thrd pvlt lens by (simp add: nth_list_update)
      moreover have "ds_seen t ! (ds_prev s) = ds_seen s ! (ds_prev s) \<or> ds_prev s = vcount"
        using P_seen wnotpv by (auto simp: nth_list_update)
      ultimately show ?thesis using pvlt pvmem wnz by (auto simp: thrdstep_def)
    next
      assume "p \<in> thrdstep s"
      then obtain x where px: "p = (x, ds_thrd s ! x)" and xlt: "x < Suc vcount"
          and xmem: "x = vcount \<or> ds_seen s ! x" and xthrd: "ds_thrd s ! x \<noteq> 0" by (auto simp: thrdstep_def)
      have xnw: "x \<noteq> w" using xthrd wthrd0 by auto
      have xnpv: "x \<noteq> ds_prev s" using xthrd prevthrd by auto
      have tx: "ds_thrd t ! x = ds_thrd s ! x" using P_thrd xnpv by (simp add: nth_list_update)
      have "ds_seen t ! x = ds_seen s ! x" using P_seen xnw by (simp add: nth_list_update)
      thus ?thesis using px xlt xmem xthrd tx by (auto simp: thrdstep_def)
    qed
  qed
qed

definition tspan :: "'n dfs_state \<Rightarrow> bool" where
  "tspan s \<longleftrightarrow> (\<forall>y. (y = vcount \<or> (y < vcount \<and> ds_seen s ! y)) \<longrightarrow> (vcount, y) \<in> (thrdstep s)\<^sup>*)"

lemma tspan_append:
  assumes inv: "dfs_inv fl s" and tsp: "tspan s"
      and wlt: "w < vcount" and wnz: "w \<noteq> 0" and unseen: "\<not> ds_seen s ! w"
      and P_seen: "ds_seen t = (ds_seen s)[w := True]"
      and P_thrd: "ds_thrd t = (ds_thrd s)[ds_prev s := w]"
  shows "tspan t"
proof -
  have step: "thrdstep t = insert (ds_prev s, w) (thrdstep s)"
    using thrdstep_append[OF inv wlt wnz unseen P_seen P_thrd] .
  have sub: "thrdstep s \<subseteq> thrdstep t" using step by auto
  have thi: "thread_inv s" and sz: "dfs_sized s" using inv by (auto simp: dfs_inv_def)
  have pvlt: "ds_prev s < Suc vcount" and pvmem: "ds_prev s = vcount \<or> ds_seen s ! (ds_prev s)"
    using thi by (auto simp: thread_inv_def)
  have lens: "length (ds_seen s) = Suc vcount" using sz by (auto simp: dfs_sized_def)
  have pvV: "ds_prev s = vcount \<or> (ds_prev s < vcount \<and> ds_seen s ! (ds_prev s))"
    using pvmem pvlt by auto
  have reach_pv: "(vcount, ds_prev s) \<in> (thrdstep t)\<^sup>*"
    using tsp pvV rtrancl_mono[OF sub] by (auto simp: tspan_def)
  have reach_w: "(vcount, w) \<in> (thrdstep t)\<^sup>*"
    using reach_pv step by (simp add: rtrancl_into_rtrancl)
  show ?thesis unfolding tspan_def
  proof (intro allI impI)
    fix y assume ymem: "y = vcount \<or> (y < vcount \<and> ds_seen t ! y)"
    show "(vcount, y) \<in> (thrdstep t)\<^sup>*"
    proof (cases "y = vcount")
      case True thus ?thesis by simp
    next
      case False
      hence ylt: "y < vcount" and yseen: "ds_seen t ! y" using ymem by auto
      show ?thesis
      proof (cases "y = w")
        case True thus ?thesis using reach_w by simp
      next
        case False
        hence "ds_seen s ! y" using yseen P_seen ylt lens by (simp add: nth_list_update)
        hence "(vcount, y) \<in> (thrdstep s)\<^sup>*" using tsp ylt by (auto simp: tspan_def)
        thus ?thesis using rtrancl_mono[OF sub] by auto
      qed
    qed
  qed
qed

lemma thrdstep_cong: "ds_thrd s = ds_thrd t \<Longrightarrow> ds_seen s = ds_seen t \<Longrightarrow> thrdstep s = thrdstep t"
  by (simp add: thrdstep_def)

lemma tspan_cong:
  assumes "ds_thrd s = ds_thrd t" and "ds_seen s = ds_seen t"
  shows "tspan s = tspan t"
  unfolding tspan_def using thrdstep_cong[OF assms] assms(2) by simp

lemma dfs_finish_tspan: "tspan s \<Longrightarrow> tspan (dfs_finish s v rest)"
  by (rule tspan_cong[THEN iffD1, rotated -1]) (simp_all add: dfs_finish_def Let_def)

lemma emit_U_edge_tspan: "tspan s \<Longrightarrow> tspan (emit_U_edge s v)"
  by (rule tspan_cong[THEN iffD1, rotated -1]) (simp_all add: emit_U_edge_def Let_def)

lemma dfs_discover_tspan:
  assumes inv: "dfs_inv acyc_flow s" and tsp: "tspan s"
      and wlt: "w < vcount" and wnz: "w \<noteq> 0" and unseen: "\<not> ds_seen s ! w"
  shows "tspan (dfs_discover s v w e)"
  by (rule tspan_append[OF inv tsp wlt wnz unseen]) (simp_all add: dfs_discover_def dfs_push_def Let_def)

lemma bd_upd1_tspan:
  assumes inv: "dfs_inv fl s" and tsp: "tspan s" and c: "bd_call1_conds fl s"
  shows "tspan (bd_upd1 fl s)"
proof -
  have wf: "dfs_wf fl s" using inv by (simp add: dfs_inv_def)
  obtain v rest e w c' where e: "e < m" "snd_list ! e = w" and wlt: "w < vcount"
    and up: "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr> else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (rule bd_upd1_eq[OF wf c])
  have wnz: "w \<noteq> 0" using snd_list_nz e by blast
  show ?thesis
  proof (cases "ds_seen s ! w")
    case True thus ?thesis using tsp up by (simp add: tspan_def thrdstep_def)
  next
    case False
    have "tspan (dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
      by (rule tspan_append[OF inv tsp wlt wnz False]) (simp_all add: dfs_discover_def dfs_push_def Let_def)
    thus ?thesis using up False by simp
  qed
qed

lemma bd_upd2_tspan:
  assumes inv: "dfs_inv fl s" and tsp: "tspan s" and c: "bd_call2_conds fl s"
  shows "tspan (bd_upd2 fl s)"
proof -
  have wf: "dfs_wf fl s" using inv by (simp add: dfs_inv_def)
  obtain v rest e w c' where e: "e < m" "fst_list ! e = w" and wlt: "w < vcount"
    and up: "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr> else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    by (rule bd_upd2_eq[OF wf c])
  have wnz: "w \<noteq> 0" using fst_list_nz e by blast
  show ?thesis
  proof (cases "ds_seen s ! w")
    case True thus ?thesis using tsp up by (simp add: tspan_def thrdstep_def)
  next
    case False
    have "tspan (dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
      by (rule tspan_append[OF inv tsp wlt wnz False]) (simp_all add: dfs_discover_def dfs_push_def Let_def)
    thus ?thesis using up False by simp
  qed
qed

lemma bd_upd3_tspan:
  assumes tsp: "tspan s" and c: "bd_call3_conds fl s"
  shows "tspan (bd_upd3 s)"
proof -
  obtain v rest where "bd_upd3 s = dfs_finish s v rest" by (rule bd_upd3_eq[OF c])
  thus ?thesis using dfs_finish_tspan[OF tsp] by simp
qed

lemma build_dfs_tspan:
  assumes dom: "build_dfs_dom (fl, s)" and inv: "dfs_inv fl s" and tsp: "tspan s"
  shows "tspan (build_dfs fl s)"
  using inv tsp
proof (induct rule: bd_induct[OF dom])
  case IH: (1 fl s)
  show ?case
    apply (rule bd_cases[where s = s and fl = fl])
    by (auto intro!: IH(2-4) bd_upd1_inv bd_upd2_inv bd_upd3_inv
                     bd_upd1_tspan bd_upd2_tspan bd_upd3_tspan IH(5) IH(6)
             simp: bd_simps[OF IH(1)])
qed

lemma open_tree_component_tspan:
  assumes inv: "dfs_inv acyc_flow s" and tsp: "tspan s" and c: "c < vcount"
      and unseen: "\<not> ds_seen s ! c" and cnz: "c \<noteq> 0" and stke: "ds_stk s = []"
  shows "tspan (open_tree_component acyc_flow s c)"
proof -
  have "dfs_wf acyc_flow s" "dfs_sized s" using inv by (simp_all add: dfs_inv_def)
  then obtain sd where opd: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd"
    and dom: "build_dfs_dom (acyc_flow, sd)"
    and I: "(dfs_inv acyc_flow s \<and> \<not> ds_seen s ! c \<and> c \<noteq> 0 \<and> ds_stk s = []) \<longrightarrow> dfs_inv acyc_flow sd"
    and seen: "ds_seen sd = (ds_seen s)[c := True]" and thrd: "ds_thrd sd = (ds_thrd s)[ds_prev s := c]"
    using c by (rule open_tree_component_seed)
  have "tspan sd" by (rule tspan_append[OF inv tsp c cnz unseen seen thrd])
  thus ?thesis unfolding opd using build_dfs_tspan[OF dom] I inv unseen cnz stke by blast
qed

lemma dfs_init_tspan: "tspan dfs_init"
  by (auto simp: tspan_def thrdstep_def dfs_init_def simp del: replicate_Suc)

lemma phase1_step_tspan:
  assumes v: "v \<in> set vs_list" and pre: "dfs_inv acyc_flow s \<and> ds_stk s = []" and tsp: "tspan s"
  shows "tspan (phase1_step acyc_flow v s)"
proof -
  have inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" using pre by auto
  show ?thesis
  proof (cases "imbalance ! v = 0")
    case True thus ?thesis using tsp by (simp add: phase1_step_def)
  next
    case nz: False
    show ?thesis
    proof (cases "ds_seen s ! v")
      case True thus ?thesis using nz emit_U_edge_tspan[OF tsp] by (simp add: phase1_step_def)
    next
      case False
      have vlt: "v < vcount" using vs_less_vcount[OF v] .
      have vnz: "v \<noteq> 0" using v no_zero_node by metis
      thus ?thesis using nz False open_tree_component_tspan[OF inv tsp vlt False vnz stke]
        by (simp add: phase1_step_def)
    qed
  qed
qed

lemma phase2_step_tspan:
  assumes v: "v \<in> set vs_list" and pre: "dfs_inv acyc_flow s \<and> ds_stk s = []" and tsp: "tspan s"
  shows "tspan (phase2_step acyc_flow v s)"
proof -
  have inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" using pre by auto
  show ?thesis
  proof (cases "ds_seen s ! v")
    case True thus ?thesis using tsp by (simp add: phase2_step_def)
  next
    case False
    note ns = this
    have vlt: "v < vcount" using vs_less_vcount[OF v] .
    show ?thesis
    proof (cases "is_lonely v")
      case True thus ?thesis using tsp by (simp add: phase2_step_def)
    next
      case False
      note nl = this
      have vnz: "v \<noteq> 0" using v no_zero_node by metis
      have eq: "phase2_step acyc_flow v s = open_tree_component acyc_flow s v" by (simp add: phase2_step_def ns nl)
      thus ?thesis using open_tree_component_tspan[OF inv tsp vlt ns vnz stke] by simp
    qed
  qed
qed

lemma phase1_tspan:
  assumes pre: "dfs_inv acyc_flow s \<and> ds_stk s = []" and tsp: "tspan s"
  shows "tspan (phase1 acyc_flow s)"
proof -
  let ?P = "\<lambda>s. (dfs_inv acyc_flow s \<and> ds_stk s = []) \<and> tspan s"
  have "?P (fold (phase1_step acyc_flow) vs_list s)"
  proof (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = ?P])
    show "\<And>x. x \<in> set vs_list \<Longrightarrow> x \<in> set vs_list" by simp
    show "?P s" using pre tsp by simp
    fix x t assume x: "x \<in> set vs_list" and Pt: "?P t"
    show "?P (phase1_step acyc_flow x t)"
      using phase1_step_inv[OF x conjunct1[OF Pt]] phase1_step_tspan[OF x conjunct1[OF Pt] conjunct2[OF Pt]]
      by simp
  qed
  thus ?thesis unfolding phase1_def by simp
qed

lemma phase2_tspan:
  assumes pre: "dfs_inv acyc_flow s \<and> ds_stk s = []" and tsp: "tspan s"
  shows "tspan (phase2 acyc_flow s)"
proof -
  let ?P = "\<lambda>s. (dfs_inv acyc_flow s \<and> ds_stk s = []) \<and> tspan s"
  have "?P (fold (phase2_step acyc_flow) vs_list s)"
  proof (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = ?P])
    show "\<And>x. x \<in> set vs_list \<Longrightarrow> x \<in> set vs_list" by simp
    show "?P s" using pre tsp by simp
    fix x t assume x: "x \<in> set vs_list" and Pt: "?P t"
    show "?P (phase2_step acyc_flow x t)"
      using phase2_step_inv[OF x conjunct1[OF Pt]] phase2_step_tspan[OF x conjunct1[OF Pt] conjunct2[OF Pt]]
      by simp
  qed
  thus ?thesis unfolding phase2_def by simp
qed

lemma build_tree_tspan: "tspan (build_tree acyc_flow)"
proof -
  have i0: "dfs_inv acyc_flow dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have p1: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init) \<and> ds_stk (phase1 acyc_flow dfs_init) = []" using phase1_inv[OF i0] .
  have t1: "tspan (phase1 acyc_flow dfs_init)" using phase1_tspan[OF i0 dfs_init_tspan] .
  have t2: "tspan (phase2 acyc_flow (phase1 acyc_flow dfs_init))" using phase2_tspan[OF p1 t1] .
  have "ds_thrd (phase2 acyc_flow (phase1 acyc_flow dfs_init)) = ds_thrd (build_tree acyc_flow)"
       "ds_seen (phase2 acyc_flow (phase1 acyc_flow dfs_init)) = ds_seen (build_tree acyc_flow)"
    by (simp_all add: build_tree_def Let_def)
  thus ?thesis using tspan_cong t2 by blast
qed


subsection \<open>The thread relation is single-valued, injective, and (with spanning) acyclic\<close>

lemma thrdstep_single_valued: "single_valued (thrdstep (build_tree acyc_flow))"
proof (rule single_valuedI)
  fix x y z assume a: "(x, y) \<in> thrdstep (build_tree acyc_flow)" and b: "(x, z) \<in> thrdstep (build_tree acyc_flow)"
  from a have y: "y = ds_thrd (build_tree acyc_flow) ! x" by (simp add: thrdstep_def)
  from b have z: "z = ds_thrd (build_tree acyc_flow) ! x" by (simp add: thrdstep_def)
  show "y = z" using y z by simp
qed

lemma thrdstepD:
  assumes "(x, z) \<in> thrdstep s"
  shows "z = ds_thrd s ! x" and "x < Suc vcount" and "x = vcount \<or> ds_seen s ! x" and "ds_thrd s ! x \<noteq> 0"
  using assms by (simp_all add: thrdstep_def)

lemma thrdstep_inj: "single_valued ((thrdstep (build_tree acyc_flow))\<inverse>)"
proof (rule single_valuedI)
  fix z x y assume "(z, x) \<in> (thrdstep (build_tree acyc_flow))\<inverse>" and "(z, y) \<in> (thrdstep (build_tree acyc_flow))\<inverse>"
  hence xt: "(x, z) \<in> thrdstep (build_tree acyc_flow)" and yt: "(y, z) \<in> thrdstep (build_tree acyc_flow)" by simp_all
  have thrdprev0: "ds_thrd (build_tree acyc_flow) ! (ds_prev (build_tree acyc_flow)) = 0"
    using build_tree_thread_inv by (simp add: thread_inv_def)
  have xnprev: "x \<noteq> ds_prev (build_tree acyc_flow)" using thrdstepD(4)[OF xt] thrdprev0 by metis
  have ynprev: "y \<noteq> ds_prev (build_tree acyc_flow)" using thrdstepD(4)[OF yt] thrdprev0 by metis
  have "ds_rvth (build_tree acyc_flow) ! z = x"
    using build_tree_thread_inverse(3)[OF thrdstepD(2)[OF xt] thrdstepD(3)[OF xt] xnprev] thrdstepD(1)[OF xt] by simp
  moreover have "ds_rvth (build_tree acyc_flow) ! z = y"
    using build_tree_thread_inverse(3)[OF thrdstepD(2)[OF yt] thrdstepD(3)[OF yt] ynprev] thrdstepD(1)[OF yt] by simp
  ultimately show "x = y" by simp
qed

lemma vcount_notin_range: "vcount \<notin> Range (thrdstep (build_tree acyc_flow))"
proof
  assume "vcount \<in> Range (thrdstep (build_tree acyc_flow))"
  then obtain x where xt: "(x, vcount) \<in> thrdstep (build_tree acyc_flow)" unfolding Range_iff by (elim exE)
  have thrdprev0: "ds_thrd (build_tree acyc_flow) ! (ds_prev (build_tree acyc_flow)) = 0"
    using build_tree_thread_inv by (simp add: thread_inv_def)
  have xnprev: "x \<noteq> ds_prev (build_tree acyc_flow)" using thrdstepD(4)[OF xt] thrdprev0 by metis
  have "ds_rvth (build_tree acyc_flow) ! (ds_thrd (build_tree acyc_flow) ! x) = x"
    using build_tree_thread_inverse(3)[OF thrdstepD(2)[OF xt] thrdstepD(3)[OF xt] xnprev] .
  hence "ds_rvth (build_tree acyc_flow) ! vcount = x" using thrdstepD(1)[OF xt] by simp
  hence x0: "x = 0" using build_tree_root_no_pred by simp
  have "vcount \<noteq> 0" by (simp add: vcount_def)
  moreover have "\<not> ds_seen (build_tree acyc_flow) ! 0" using build_tree_thread_inv by (simp add: thread_inv_def)
  ultimately show False using thrdstepD(3)[OF xt] x0 by simp
qed

lemma thrdstep_acyclic: "acyclic (thrdstep (build_tree acyc_flow))"
  unfolding acyclic_def
proof (intro allI notI)
  fix x assume cyc: "(x, x) \<in> (thrdstep (build_tree acyc_flow))\<^sup>+"
  from cyc obtain y where xy: "(x, y) \<in> thrdstep (build_tree acyc_flow)" by (meson tranclD)
  have xmem: "x = vcount \<or> (x < vcount \<and> ds_seen (build_tree acyc_flow) ! x)"
  proof (cases "x = vcount")
    case True thus ?thesis by simp
  next
    case False
    have "ds_seen (build_tree acyc_flow) ! x" using thrdstepD(3)[OF xy] False by simp
    moreover have "x < vcount" using thrdstepD(2)[OF xy] False by simp
    ultimately show ?thesis by simp
  qed
  have reach: "(vcount, x) \<in> (thrdstep (build_tree acyc_flow))\<^sup>*"
    using build_tree_tspan[unfolded tspan_def, rule_format, OF xmem] .
  have rc: "(x, vcount) \<in> ((thrdstep (build_tree acyc_flow))\<inverse>)\<^sup>*" using reach by (simp add: rtrancl_converse)
  have cc: "(x, x) \<in> ((thrdstep (build_tree acyc_flow))\<inverse>)\<^sup>+" using cyc by (simp add: trancl_converse)
  have vx: "(vcount, x) \<in> ((thrdstep (build_tree acyc_flow))\<inverse>)\<^sup>*" using orbit_returns[OF thrdstep_inj rc cc] .
  have bk: "(x, vcount) \<in> (thrdstep (build_tree acyc_flow))\<^sup>*" using vx by (simp add: rtrancl_converse)
  have "(vcount, x) \<in> (thrdstep (build_tree acyc_flow))\<^sup>+" using reach cyc by (meson rtrancl_trancl_trancl)
  hence "(vcount, vcount) \<in> (thrdstep (build_tree acyc_flow))\<^sup>+" using bk by (meson trancl_rtrancl_trancl)
  hence "vcount \<in> Range (thrdstep (build_tree acyc_flow))" by (meson tranclD2 RangeI)
  thus False using vcount_notin_range by simp
qed

lemma thrdstep_finite: "finite (thrdstep (build_tree acyc_flow))"
proof -
  have "thrdstep (build_tree acyc_flow) \<subseteq> (\<lambda>x. (x, ds_thrd (build_tree acyc_flow) ! x)) ` {..<Suc vcount}"
    by (auto simp: thrdstep_def)
  thus ?thesis by (meson finite_imageI finite_lessThan finite_subset)
qed

subsection \<open>Thread parent maps: @{const parent_spec}, spanning, domains, and the thread/rev-thread inverse\<close>

lemma thrdstep_eq_Sthrd: "thrdstep (build_tree acyc_flow) = {(x, y) |x y. Some y = Sthrd x}"
  by (auto simp: thrdstep_def Sthrd_def Varb_def Vseen_def split: if_splits)

lemma parent_spec_Sthrd: "parent_spec Sthrd"
proof -
  have eq: "{(x, y) |x y. Some x = Sthrd y} = (thrdstep (build_tree acyc_flow))\<inverse>"
    using thrdstep_eq_Sthrd by auto
  show ?thesis unfolding parent_spec_def eq
    by (rule finite_acyclic_wf_converse[OF thrdstep_finite thrdstep_acyclic])
qed

lemma follow_Sthrd_thrdstep: "set (follow Sthrd u) = {z. (u, z) \<in> (thrdstep (build_tree acyc_flow))\<^sup>*}"
proof -
  have "{(x, y). Sthrd x = Some y} = thrdstep (build_tree acyc_flow)" using thrdstep_eq_Sthrd by auto
  thus ?thesis using follow_set_rtrancl[OF parent_spec_Sthrd, of u] by simp
qed

lemma zero_notin_Varb: "0 \<notin> Varb"
proof -
  have "\<not> ds_seen (build_tree acyc_flow) ! 0" using build_tree_thread_inv by (simp add: thread_inv_def)
  moreover have "vcount \<noteq> 0" by (simp add: vcount_def)
  ultimately show ?thesis by (simp add: Varb_def Vseen_def)
qed

lemma Varb_elem_props:
  assumes "z \<in> Varb"
  shows "z < Suc vcount" and "z = vcount \<or> ds_seen (build_tree acyc_flow) ! z" and "z \<noteq> 0"
proof -
  show "z \<noteq> 0" using assms zero_notin_Varb by metis
  show "z < Suc vcount" using assms by (auto simp: Varb_def Vseen_def)
  show "z = vcount \<or> ds_seen (build_tree acyc_flow) ! z" using assms by (auto simp: Varb_def Vseen_def)
qed

lemma thrdstep_reach_Varb:
  assumes "(vcount, z) \<in> (thrdstep (build_tree acyc_flow))\<^sup>*" shows "z \<in> Varb"
  using assms
proof (induct rule: rtrancl_induct)
  case base thus ?case by (simp add: Varb_def)
next
  case (step a b)
  have ab: "(a, b) \<in> thrdstep (build_tree acyc_flow)" by (rule step.hyps(2))
  have thrdprev0: "ds_thrd (build_tree acyc_flow) ! (ds_prev (build_tree acyc_flow)) = 0"
    using build_tree_thread_inv by (simp add: thread_inv_def)
  have anprev: "a \<noteq> ds_prev (build_tree acyc_flow)" using thrdstepD(4)[OF ab] thrdprev0 by metis
  have blt: "ds_thrd (build_tree acyc_flow) ! a < Suc vcount"
    using build_tree_thread_inverse(1)[OF thrdstepD(2)[OF ab] thrdstepD(3)[OF ab] anprev] .
  have bmem: "ds_thrd (build_tree acyc_flow) ! a = vcount \<or> ds_seen (build_tree acyc_flow) ! (ds_thrd (build_tree acyc_flow) ! a)"
    using build_tree_thread_inverse(2)[OF thrdstepD(2)[OF ab] thrdstepD(3)[OF ab] anprev] .
  have "b = ds_thrd (build_tree acyc_flow) ! a" by (rule thrdstepD(1)[OF ab])
  thus "b \<in> Varb" using blt bmem by (auto simp: Varb_def Vseen_def)
qed

lemma follow_Sthrd_spans: "set (follow Sthrd vcount) = Varb"
proof -
  have "set (follow Sthrd vcount) = {z. (vcount, z) \<in> (thrdstep (build_tree acyc_flow))\<^sup>*}"
    by (rule follow_Sthrd_thrdstep)
  moreover have "{z. (vcount, z) \<in> (thrdstep (build_tree acyc_flow))\<^sup>*} = Varb"
  proof (intro equalityI subsetI)
    fix z assume "z \<in> {z. (vcount, z) \<in> (thrdstep (build_tree acyc_flow))\<^sup>*}"
    thus "z \<in> Varb" using thrdstep_reach_Varb by simp
  next
    fix z assume "z \<in> Varb"
    hence "z = vcount \<or> (z < vcount \<and> ds_seen (build_tree acyc_flow) ! z)" by (auto simp: Varb_def Vseen_def)
    thus "z \<in> {z. (vcount, z) \<in> (thrdstep (build_tree acyc_flow))\<^sup>*}"
      using build_tree_tspan[unfolded tspan_def, rule_format] by simp
  qed
  ultimately show ?thesis by simp
qed

lemma Srvth_rel_eq: "{(x, y) |x y. Some x = Srvth y} = thrdstep (build_tree acyc_flow)"
proof (intro equalityI subsetI)
  fix p assume "p \<in> {(x, y) |x y. Some x = Srvth y}"
  then obtain x y where p: "p = (x, y)" and s: "Some x = Srvth y" by auto
  from s have yV: "y \<in> Varb" and rnz: "ds_rvth (build_tree acyc_flow) ! y \<noteq> 0" and xr: "x = ds_rvth (build_tree acyc_flow) ! y"
    by (auto simp: Srvth_def split: if_splits)
  have ynv: "y \<noteq> vcount" using rnz build_tree_root_no_pred by metis
  have ylt: "y < Suc vcount" and ymem: "y = vcount \<or> ds_seen (build_tree acyc_flow) ! y"
    using Varb_elem_props[OF yV] by auto
  have ynz: "y \<noteq> 0" using Varb_elem_props(3)[OF yV] .
  have thy: "ds_thrd (build_tree acyc_flow) ! x = y"
    using build_tree_rev_thread_inverse(3)[OF ylt ymem ynv] xr by simp
  have xlt: "x < Suc vcount" using build_tree_rev_thread_inverse(1)[OF ylt ymem ynv] xr by simp
  have xmem: "x = vcount \<or> ds_seen (build_tree acyc_flow) ! x"
    using build_tree_rev_thread_inverse(2)[OF ylt ymem ynv] xr by simp
  show "p \<in> thrdstep (build_tree acyc_flow)" using p thy xlt xmem ynz by (simp add: thrdstep_def)
next
  fix p assume "p \<in> thrdstep (build_tree acyc_flow)"
  then obtain a where p: "p = (a, ds_thrd (build_tree acyc_flow) ! a)" and alt: "a < Suc vcount"
      and amem: "a = vcount \<or> ds_seen (build_tree acyc_flow) ! a" and anz: "ds_thrd (build_tree acyc_flow) ! a \<noteq> 0"
    by (auto simp: thrdstep_def)
  have thrdprev0: "ds_thrd (build_tree acyc_flow) ! (ds_prev (build_tree acyc_flow)) = 0"
    using build_tree_thread_inv by (simp add: thread_inv_def)
  have anprev: "a \<noteq> ds_prev (build_tree acyc_flow)" using anz thrdprev0 by metis
  have rva: "ds_rvth (build_tree acyc_flow) ! (ds_thrd (build_tree acyc_flow) ! a) = a"
    using build_tree_thread_inverse(3)[OF alt amem anprev] .
  have blt: "ds_thrd (build_tree acyc_flow) ! a < Suc vcount"
    using build_tree_thread_inverse(1)[OF alt amem anprev] .
  have bmem: "ds_thrd (build_tree acyc_flow) ! a = vcount \<or> ds_seen (build_tree acyc_flow) ! (ds_thrd (build_tree acyc_flow) ! a)"
    using build_tree_thread_inverse(2)[OF alt amem anprev] .
  have az: "a \<noteq> 0"
  proof
    assume "a = 0"
    hence "0 = vcount \<or> ds_seen (build_tree acyc_flow) ! 0" using amem by simp
    moreover have "vcount \<noteq> 0" by (simp add: vcount_def)
    moreover have "\<not> ds_seen (build_tree acyc_flow) ! 0" using build_tree_thread_inv by (simp add: thread_inv_def)
    ultimately show False by simp
  qed
  have bV: "ds_thrd (build_tree acyc_flow) ! a \<in> Varb" using blt bmem by (auto simp: Varb_def Vseen_def)
  have "Some a = Srvth (ds_thrd (build_tree acyc_flow) ! a)"
    using bV anz rva az by (simp add: Srvth_def)
  thus "p \<in> {(x, y) |x y. Some x = Srvth y}" using p by auto
qed

lemma parent_spec_Srvth: "parent_spec Srvth"
  unfolding parent_spec_def Srvth_rel_eq
  by (rule finite_acyclic_wf[OF thrdstep_finite thrdstep_acyclic])

lemma build_tree_thrd_prev0: "ds_thrd (build_tree acyc_flow) ! (ds_prev (build_tree acyc_flow)) = 0"
  using build_tree_thread_inv by (simp add: thread_inv_def)

lemma lsuc_root_eq_prev: "ds_lsuc (build_tree acyc_flow) ! vcount = ds_prev (build_tree acyc_flow)"
proof -
  have i0: "dfs_inv acyc_flow dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have "dfs_inv acyc_flow (phase2 acyc_flow (phase1 acyc_flow dfs_init))" using phase2_inv[OF phase1_inv[OF i0]] by simp
  hence "length (ds_lsuc (phase2 acyc_flow (phase1 acyc_flow dfs_init))) = Suc vcount" by (simp add: dfs_inv_def dfs_sized_def)
  thus ?thesis by (simp add: build_tree_def Let_def)
qed

lemma thrd_nz_of_Varb:
  assumes xV: "x \<in> Varb" and xnp: "x \<noteq> ds_prev (build_tree acyc_flow)"
  shows "ds_thrd (build_tree acyc_flow) ! x \<noteq> 0"
proof
  assume z: "ds_thrd (build_tree acyc_flow) ! x = 0"
  have xlt: "x < Suc vcount" and xmem: "x = vcount \<or> ds_seen (build_tree acyc_flow) ! x" using Varb_elem_props[OF xV] by auto
  have "vcount \<noteq> 0" by (simp add: vcount_def)
  moreover have "\<not> ds_seen (build_tree acyc_flow) ! 0" using build_tree_thread_inv by (simp add: thread_inv_def)
  ultimately show False using build_tree_thread_inverse(2)[OF xlt xmem xnp] z by simp
qed

lemma rvth_nz_of_Varb:
  assumes xV: "x \<in> Varb" and xnr: "x \<noteq> vcount"
  shows "ds_rvth (build_tree acyc_flow) ! x \<noteq> 0"
proof
  assume z: "ds_rvth (build_tree acyc_flow) ! x = 0"
  have xlt: "x < Suc vcount" and xmem: "x = vcount \<or> ds_seen (build_tree acyc_flow) ! x" using Varb_elem_props[OF xV] by auto
  have "vcount \<noteq> 0" by (simp add: vcount_def)
  moreover have "\<not> ds_seen (build_tree acyc_flow) ! 0" using build_tree_thread_inv by (simp add: thread_inv_def)
  ultimately show False using build_tree_rev_thread_inverse(2)[OF xlt xmem xnr] z by simp
qed

lemma dom_Sthrd: "dom Sthrd = Varb - {ds_prev (build_tree acyc_flow)}"
proof (intro equalityI subsetI)
  fix x assume "x \<in> dom Sthrd"
  then obtain y where "Sthrd x = Some y" by (auto simp: dom_def)
  hence xV: "x \<in> Varb" and nz: "ds_thrd (build_tree acyc_flow) ! x \<noteq> 0" by (auto simp: Sthrd_def split: if_splits)
  have "x \<noteq> ds_prev (build_tree acyc_flow)" using nz build_tree_thrd_prev0 by metis
  thus "x \<in> Varb - {ds_prev (build_tree acyc_flow)}" using xV by simp
next
  fix x assume x: "x \<in> Varb - {ds_prev (build_tree acyc_flow)}"
  hence "ds_thrd (build_tree acyc_flow) ! x \<noteq> 0" using thrd_nz_of_Varb by simp
  thus "x \<in> dom Sthrd" using x by (auto simp: Sthrd_def dom_def)
qed

lemma dom_Srvth: "dom Srvth = Varb - {vcount}"
proof (intro equalityI subsetI)
  fix x assume "x \<in> dom Srvth"
  then obtain y where "Srvth x = Some y" by (auto simp: dom_def)
  hence xV: "x \<in> Varb" and nz: "ds_rvth (build_tree acyc_flow) ! x \<noteq> 0" by (auto simp: Srvth_def split: if_splits)
  have "x \<noteq> vcount" using nz build_tree_root_no_pred by metis
  thus "x \<in> Varb - {vcount}" using xV by simp
next
  fix x assume x: "x \<in> Varb - {vcount}"
  hence "ds_rvth (build_tree acyc_flow) ! x \<noteq> 0" using rvth_nz_of_Varb by simp
  thus "x \<in> dom Srvth" using x by (auto simp: Srvth_def dom_def)
qed

lemma thrd_rvth_inverse: "\<forall>v v'. Sthrd v = Some v' \<longleftrightarrow> Srvth v' = Some v"
proof (intro allI)
  fix v v'
  have A: "Sthrd v = Some v' \<longleftrightarrow> (v, v') \<in> thrdstep (build_tree acyc_flow)"
    unfolding thrdstep_eq_Sthrd by (simp add: eq_commute)
  have B: "Srvth v' = Some v \<longleftrightarrow> (v, v') \<in> thrdstep (build_tree acyc_flow)"
    unfolding Srvth_rel_eq[symmetric] by (simp add: eq_commute)
  from A B show "Sthrd v = Some v' \<longleftrightarrow> Srvth v' = Some v" by simp
qed

lemma prev_in_Varb: "ds_prev (build_tree acyc_flow) \<in> Varb"
proof -
  have "ds_prev (build_tree acyc_flow) < Suc vcount"
   and "ds_prev (build_tree acyc_flow) = vcount \<or> ds_seen (build_tree acyc_flow) ! (ds_prev (build_tree acyc_flow))"
    using build_tree_thread_inv by (auto simp: thread_inv_def)
  thus ?thesis by (auto simp: Varb_def Vseen_def)
qed

lemma lsuc_in_V_all:
  assumes "v \<in> Varb" shows "lsuc Sarb v \<in> Varb"
proof (cases "v = vcount")
  case True
  have "lsuc Sarb v = ds_prev (build_tree acyc_flow)" using True lsuc_root_eq_prev by (simp add: Sarb_sel)
  thus ?thesis using prev_in_Varb by simp
next
  case False
  hence "v \<in> Vseen" using assms by (simp add: Varb_def)
  thus ?thesis using lsuc_in_V by simp
qed

subsection \<open>Edge-set spanning: obligation 1 completed (@{const dVs})\<close>

text \<open>The remaining ingredient of @{const rooted_arborescense_invar} is that the parent edges span the
      vertex set. The @{term fst} projection of the edge set is exactly @{term Vseen} (the domain of
      @{term Sprnt}); the @{term snd} projection is the set of stored parents, each of which is either
      @{term vcount} or a seen vertex. The graph has at least one edge (@{thm num_edges_gtr_0}), hence at
      least one real vertex, so @{term Vseen} is non-empty and --- following any parent chain to the root ---
      some component root has @{term vcount} as its parent, putting @{term vcount} into the edge set.\<close>

lemma Vseen_nonempty: "Vseen \<noteq> {}"
proof -
  have "0 < length fst_list" using length_fst length_edges num_edges_gtr_0 by simp
  hence f0: "fst_list ! 0 \<in> set fst_list" by simp
  hence e: "fst_list ! 0 \<in> set fst_list \<union> set snd_list" by simp
  from f0 have v: "fst_list ! 0 \<in> set vs_list" using fst_snd_vs by auto
  have nl: "\<not> is_lonely (fst_list ! 0)" using edged_not_lonely[OF e] .
  have "fst_list ! 0 < vcount" using vs_less_vcount[OF v] .
  moreover have "ds_seen (build_tree acyc_flow) ! (fst_list ! 0)" using build_tree_spans[OF v nl] .
  ultimately show ?thesis by (auto simp: Vseen_def)
qed

lemma exists_root_child: "\<exists>z. z \<in> Vseen \<and> ds_prnt (build_tree acyc_flow) ! z = vcount"
proof -
  obtain u where u: "u \<in> Vseen" using Vseen_nonempty by blast
  hence ult: "u < vcount" and useen: "ds_seen (build_tree acyc_flow) ! u" by (auto simp: Vseen_def)
  have reach: "(u, vcount) \<in> (pstep (build_tree acyc_flow))\<^sup>*" using build_tree_reaches_root[OF ult useen] .
  have "u \<noteq> vcount" using ult by simp
  then obtain z where zstep: "(z, vcount) \<in> pstep (build_tree acyc_flow)" using reach by (metis rtranclE)
  hence "z < vcount \<and> ds_seen (build_tree acyc_flow) ! z \<and> ds_prnt (build_tree acyc_flow) ! z = vcount" by (auto simp: pstep_def)
  thus ?thesis by (auto simp: Vseen_def)
qed

lemma dVs_Sprnt: "dVs {(y, x) |x y. Some x = Sprnt y} = Varb"
proof -
  let ?E = "{(y, x) |x y. Some x = Sprnt y}"
  have fstE: "fst ` ?E = Vseen"
  proof (rule equalityI; rule subsetI)
    fix p assume "p \<in> fst ` ?E"
    then obtain x where "Some x = Sprnt p" by auto
    thus "p \<in> Vseen" by (auto simp: Sprnt_def split: if_splits)
  next
    fix p assume pv: "p \<in> Vseen"
    hence "Some (ds_prnt (build_tree acyc_flow) ! p) = Sprnt p" by (simp add: Sprnt_def)
    hence "(p, ds_prnt (build_tree acyc_flow) ! p) \<in> ?E" by auto
    thus "p \<in> fst ` ?E" by (force intro: image_eqI)
  qed
  have sndE_sub: "snd ` ?E \<subseteq> Varb"
  proof
    fix b assume "b \<in> snd ` ?E"
    then obtain y where sy: "Some b = Sprnt y" by auto
    hence yv: "y \<in> Vseen" and b: "b = ds_prnt (build_tree acyc_flow) ! y" by (auto simp: Sprnt_def split: if_splits)
    hence "y < vcount \<and> ds_seen (build_tree acyc_flow) ! y" by (auto simp: Vseen_def)
    thus "b \<in> Varb" using build_tree_parent_in_seen b by (auto simp: Varb_def Vseen_def)
  qed
  have vcount_in: "vcount \<in> snd ` ?E"
  proof -
    obtain z where zv: "z \<in> Vseen" and zp: "ds_prnt (build_tree acyc_flow) ! z = vcount" using exists_root_child by blast
    hence "Some vcount = Sprnt z" by (auto simp: Sprnt_def)
    hence "(z, vcount) \<in> ?E" by auto
    thus ?thesis by (force intro: image_eqI)
  qed
  have "dVs ?E = fst ` ?E \<union> snd ` ?E" by (rule dVs_eq)
  also have "... = Varb" unfolding fstE using sndE_sub vcount_in by (auto simp: Varb_def)
  finally show ?thesis .
qed

text \<open>Obligation 1 assembled: @{term Sprnt} is a rooted arborescence on @{term Varb}.\<close>

lemma rooted_arb_invar_Sprnt: "rooted_arborescense_invar vcount Varb Sprnt"
proof (rule rooted_arborescense_invarI)
  show "parent_spec Sprnt" by (rule parent_spec_Sprnt)
  show "vcount \<in> Varb" by (rule r_in_V)
  show "dom Sprnt = Varb - {vcount}" by (rule dom_Sprnt)
  show "dVs {(y, x) |x y. Some x = Sprnt y} = Varb" by (rule dVs_Sprnt)
qed

subsection \<open>Clause J: obligation 10 (preorder contiguity of the thread blocks)\<close>

text \<open>The tenth @{const arb_invar} obligation says the thread @{term \<open>follow Sthrd v\<close>} starts with a
      non-empty contiguous block whose set is @{term v}'s subtree and whose last element is
      @{term \<open>lsuc Sarb v\<close>}, after which the thread continues at @{term \<open>thrd Sarb (lsuc Sarb v)\<close>}. We feed
      the generic @{thm preorder_contiguous} engine with the array-level DFS order (@{thm build_tree_emit_order},
      lifted to abstract @{const follow} through @{thm thrd_rvth_inverse} and @{thm follow_Sprnt_pstep}); it
      returns the block as a prefix headed by @{term v}, and @{thm build_tree_lsuc} (block-last) pins its last
      element to @{term \<open>lsuc Sarb v\<close>}, whence the suffix shape follows.\<close>

lemma last_of_prefix_Sthrd:
  assumes decomp: "follow Sthrd v = pre @ suf"
    and Lin: "L \<in> set pre"
    and Lout: "case Sthrd L of None \<Rightarrow> True | Some w \<Rightarrow> w \<notin> set pre"
  shows "L = last pre"
proof (rule ccontr)
  assume ne: "L \<noteq> last pre"
  from Lin obtain p1 p2 where pre_eq: "pre = p1 @ L # p2" by (meson split_list)
  have p2ne: "p2 \<noteq> []"
  proof (rule ccontr)
    assume "\<not> p2 \<noteq> []"
    hence "pre = p1 @ [L]" using pre_eq by simp
    hence "last pre = L" by simp
    thus False using ne by simp
  qed
  have "follow Sthrd v = p1 @ L # (p2 @ suf)" using decomp pre_eq by simp
  hence fL: "follow Sthrd L = L # (p2 @ suf)" using follow_append_ps[OF parent_spec_Sthrd] by blast
  have fps: "follow Sthrd L = (case Sthrd L of None \<Rightarrow> [L] | Some w \<Rightarrow> L # follow Sthrd w)" by (rule follow_ps_simps[OF parent_spec_Sthrd])
  have p2sufne: "p2 @ suf \<noteq> []" using p2ne by simp
  have "\<exists>w. Sthrd L = Some w \<and> follow Sthrd w = p2 @ suf" using fL fps p2sufne by (auto split: option.splits)
  then obtain w where FL: "Sthrd L = Some w" and fw: "follow Sthrd w = p2 @ suf" by blast
  have "w = hd (p2 @ suf)" using fw follow_hd_ps[OF parent_spec_Sthrd, of w] by simp
  hence "w = hd p2" using p2ne by (simp add: hd_append2)
  hence "w \<in> set p2" using p2ne by (simp add: list.set_sel(1))
  hence "w \<in> set pre" using pre_eq by auto
  thus False using FL Lout by simp
qed

lemma emit_dfs_premise:
  assumes lt: "Suc t < length (follow Sthrd vcount)"
  shows "\<exists>a. Sprnt (follow Sthrd vcount ! Suc t) = Some a \<and> a \<in> set (follow Sprnt (follow Sthrd vcount ! t))"
proof -
  define xs where "xs = follow Sthrd vcount"
  define u where "u = xs ! t"
  define w where "w = xs ! Suc t"
  have ltx: "Suc t < length xs" using lt by (simp add: xs_def)
  have con: "Sthrd u = Some w" using follow_nth_Suc[OF parent_spec_Sthrd lt] by (simp add: u_def w_def xs_def)
  have dist: "distinct xs" unfolding xs_def by (rule follow_distinct_ps[OF parent_spec_Sthrd])
  have hd0: "xs ! 0 = vcount"
    by (simp add: xs_def hd_conv_nth[symmetric] follow_ne_ps[OF parent_spec_Sthrd]
                  follow_hd_ps[OF parent_spec_Sthrd])
  have w_ne: "w \<noteq> vcount"
  proof -
    have pos: "0 < length xs" using ltx by linarith
    have "(xs ! Suc t = xs ! 0) = (Suc t = 0)" using nth_eq_iff_index_eq[OF dist, of "Suc t" 0] ltx pos by simp
    thus ?thesis using hd0 w_def by simp
  qed
  have wxs: "w \<in> set xs" using ltx w_def by (metis nth_mem)
  have wV: "w \<in> Varb" using wxs follow_Sthrd_spans by (simp add: xs_def)
  hence wseen: "w \<in> Vseen" using w_ne by (auto simp: Varb_def)
  have "Srvth w = Some u" using con thrd_rvth_inverse by blast
  hence rvth_eq: "ds_rvth (build_tree acyc_flow) ! w = u" by (auto simp: Srvth_def split: if_splits)
  have wlt: "w < vcount" and wsn: "ds_seen (build_tree acyc_flow) ! w" using wseen by (auto simp: Vseen_def)
  have emit: "(ds_rvth (build_tree acyc_flow) ! w, ds_prnt (build_tree acyc_flow) ! w) \<in> (pstep (build_tree acyc_flow))\<^sup>*" using build_tree_emit_order[OF wlt wsn] .
  have sprnt_w: "Sprnt w = Some (ds_prnt (build_tree acyc_flow) ! w)" using wseen by (simp add: Sprnt_def)
  have "(u, ds_prnt (build_tree acyc_flow) ! w) \<in> (pstep (build_tree acyc_flow))\<^sup>*" using emit rvth_eq by simp
  hence "ds_prnt (build_tree acyc_flow) ! w \<in> set (follow Sprnt u)" by (simp add: follow_Sprnt_pstep)
  thus ?thesis using sprnt_w by (auto simp: xs_def u_def w_def)
qed

lemma children_sub_Varb:
  assumes "v \<in> Varb" shows "children Sprnt v \<subseteq> Varb"
proof
  fix u assume "u \<in> children Sprnt v"
  hence uv: "(u, v) \<in> (pstep (build_tree acyc_flow))\<^sup>*" by (auto simp: children_def follow_Sprnt_pstep)
  show "u \<in> Varb"
  proof (cases "u = v")
    case True thus ?thesis using assms by simp
  next
    case False
    hence "(u, v) \<in> (pstep (build_tree acyc_flow))\<^sup>+" using uv by (metis rtranclD)
    then obtain z where "(u, z) \<in> pstep (build_tree acyc_flow)" by (meson tranclD)
    hence "u < vcount \<and> ds_seen (build_tree acyc_flow) ! u" by (auto simp: pstep_def)
    thus ?thesis by (auto simp: Varb_def Vseen_def)
  qed
qed

lemma lsuc_in_children:
  assumes "v \<in> Varb" shows "lsuc Sarb v \<in> children Sprnt v"
proof (cases "v = vcount")
  case True
  have lp: "lsuc Sarb vcount = ds_prev (build_tree acyc_flow)" by (simp add: Sarb_sel lsuc_root_eq_prev)
  have "(ds_prev (build_tree acyc_flow), vcount) \<in> (pstep (build_tree acyc_flow))\<^sup>*"
  proof (cases "ds_prev (build_tree acyc_flow) = vcount")
    case True thus ?thesis by simp
  next
    case False
    have "ds_prev (build_tree acyc_flow) \<in> Vseen" using prev_in_Varb False by (auto simp: Varb_def)
    hence "ds_prev (build_tree acyc_flow) < vcount \<and> ds_seen (build_tree acyc_flow) ! (ds_prev (build_tree acyc_flow))" by (auto simp: Vseen_def)
    thus ?thesis using build_tree_reaches_root by auto
  qed
  thus ?thesis using True lp by (auto simp: children_def follow_Sprnt_pstep)
next
  case False
  hence vs: "v \<in> Vseen" using assms by (auto simp: Varb_def)
  hence "v < vcount" "ds_seen (build_tree acyc_flow) ! v" by (auto simp: Vseen_def)
  hence "ds_lsuc (build_tree acyc_flow) ! v \<in> desc (build_tree acyc_flow) v" using build_tree_lsuc by simp
  hence "lsuc Sarb v \<in> desc (build_tree acyc_flow) v" by (simp add: Sarb_sel)
  thus ?thesis using children_Sprnt_desc[OF vs] by simp
qed

lemma thrd_lsuc_out:
  assumes "v \<in> Varb"
  shows "case Sthrd (lsuc Sarb v) of None \<Rightarrow> True | Some w \<Rightarrow> w \<notin> children Sprnt v"
proof (cases "v = vcount")
  case True
  have "lsuc Sarb vcount = ds_prev (build_tree acyc_flow)" by (simp add: Sarb_sel lsuc_root_eq_prev)
  moreover have "ds_thrd (build_tree acyc_flow) ! (ds_prev (build_tree acyc_flow)) = 0" by (rule build_tree_thrd_prev0)
  ultimately have "Sthrd (lsuc Sarb v) = None" using True by (simp add: Sthrd_def)
  thus ?thesis by simp
next
  case False
  hence vs: "v \<in> Vseen" using assms by (auto simp: Varb_def)
  hence vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" by (auto simp: Vseen_def)
  have out: "ds_thrd (build_tree acyc_flow) ! (ds_lsuc (build_tree acyc_flow) ! v) \<notin> desc (build_tree acyc_flow) v" using build_tree_lsuc[OF vlt vseen] by simp
  have ch: "children Sprnt v = desc (build_tree acyc_flow) v" using children_Sprnt_desc[OF vs] .
  show ?thesis
  proof (cases "Sthrd (lsuc Sarb v)")
    case None thus ?thesis by simp
  next
    case (Some w)
    have "lsuc Sarb v = ds_lsuc (build_tree acyc_flow) ! v" by (simp add: Sarb_sel)
    hence "w = ds_thrd (build_tree acyc_flow) ! (ds_lsuc (build_tree acyc_flow) ! v)" using Some by (auto simp: Sthrd_def split: if_splits)
    thus ?thesis using Some out ch by simp
  qed
qed

lemma clause_J:
  assumes vV: "v \<in> Varb"
  shows "\<exists>pre. follow Sthrd v = pre @ (case Sthrd (lsuc Sarb v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow Sthrd w)
             \<and> pre \<noteq> [] \<and> last pre = lsuc Sarb v \<and> set pre = children Sprnt v"
proof -
  have subv: "children Sprnt v \<subseteq> set (follow Sthrd vcount)"
    using children_sub_Varb[OF vV] follow_Sthrd_spans by simp
  have vin: "v \<in> set (follow Sthrd vcount)" using vV follow_Sthrd_spans by simp
  have root0: "Sprnt (follow Sthrd vcount ! 0) = None"
  proof -
    have "follow Sthrd vcount ! 0 = vcount" using follow_hd_ps[OF parent_spec_Sthrd, of vcount] follow_ne_ps[OF parent_spec_Sthrd, of vcount] by (metis hd_conv_nth)
    thus ?thesis by (simp add: Sprnt_def Vseen_def)
  qed
  obtain pre suf where
    dec: "follow Sthrd v = pre @ suf" and setpre: "set pre = children Sprnt v"
    and prene: "pre \<noteq> []"
    using preorder_contiguous[OF parent_spec_Sprnt parent_spec_Sthrd refl root0 emit_dfs_premise vin subv] by blast
  have Lin: "lsuc Sarb v \<in> set pre" using lsuc_in_children[OF vV] setpre by simp
  have Lout: "case Sthrd (lsuc Sarb v) of None \<Rightarrow> True | Some w \<Rightarrow> w \<notin> set pre"
    using thrd_lsuc_out[OF vV] setpre by (simp split: option.splits)
  have lastpre: "lsuc Sarb v = last pre" using last_of_prefix_Sthrd[OF dec Lin Lout] .
  define L where "L = lsuc Sarb v"
  have preL: "pre = butlast pre @ [L]" using prene lastpre L_def by (metis append_butlast_last_id)
  have dec2: "follow Sthrd v = butlast pre @ L # suf" using dec preL by simp
  have fL: "follow Sthrd L = L # suf" using follow_append_ps[OF parent_spec_Sthrd] dec2 by blast
  have fps: "follow Sthrd L = (case Sthrd L of None \<Rightarrow> [L] | Some w \<Rightarrow> L # follow Sthrd w)" by (rule follow_ps_simps[OF parent_spec_Sthrd])
  have sufeq: "suf = (case Sthrd L of None \<Rightarrow> [] | Some w \<Rightarrow> follow Sthrd w)"
    using fL fps by (auto split: option.splits)
  show ?thesis
  proof (intro exI conjI)
    show "follow Sthrd v = pre @ (case Sthrd (lsuc Sarb v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow Sthrd w)"
      using dec sufeq L_def by simp
    show "pre \<noteq> []" using prene .
    show "last pre = lsuc Sarb v" using lastpre by simp
    show "set pre = children Sprnt v" using setpre .
  qed
qed

subsection \<open>Root subtree size: obligation 9 at the root (@{const ds_snum} accumulation)\<close>

text \<open>The subtree-size obligation for interior vertices is @{thm snum_eq_children}; the root case needs
      @{term \<open>ds_snum (build_tree acyc_flow) ! vcount = card Varb\<close>}, which @{const snum_inv} does not track (it ranges
      over \<open>v < vcount\<close>). We carry a dedicated invariant @{term rootacc} through the whole build (mirroring
      the @{const tspan} carry): at every state, @{term \<open>Suc (card (seen vertices))\<close>} equals the root's
      running count plus the subtree size of the \<^emph>\<open>bottom\<close> (component-root) stack frame --- the vertices of
      the currently-open component, not yet added to the root. A discovery grows both sides by one (the
      fresh vertex joins the bottom frame's subtree via @{thm stk_top_reaches} / @{thm desc_discover});
      finishing a component root adds its size to the root; opening a component reseeds the bottom frame.
      At @{const build_tree} the stack is empty, so the bottom term is @{term 0} and the root count is the
      whole tree.\<close>

definition rootacc :: "'n dfs_state \<Rightarrow> bool" where
  "rootacc s \<longleftrightarrow> Suc (card {y. y < vcount \<and> ds_seen s ! y})
     = ds_snum s ! vcount + (if ds_stk s = [] then 0 else dcard s (last (ds_stk s)))"

lemma dfs_init_rootacc: "rootacc dfs_init"
  by (auto simp: rootacc_def dfs_init_def simp del: replicate_Suc)

lemma rootacc_discover_core:
  assumes ra: "rootacc s"
    and Vseen_grow: "{y. y < vcount \<and> ds_seen t ! y} = insert w {y. y < vcount \<and> ds_seen s ! y}"
    and w_fresh: "w < vcount" "\<not> ds_seen s ! w"
    and snum_root: "ds_snum t ! vcount = ds_snum s ! vcount"
    and stk_ne: "ds_stk t \<noteq> []" and stk_s_ne: "ds_stk s \<noteq> []"
    and bot_eq: "last (ds_stk t) = last (ds_stk s)"
    and dcard_bot: "dcard t (last (ds_stk s)) = Suc (dcard s (last (ds_stk s)))"
  shows "rootacc t"
proof -
  let ?b = "last (ds_stk s)"
  have fin: "finite {y. y < vcount \<and> ds_seen s ! y}" by simp
  have wnotin: "w \<notin> {y. y < vcount \<and> ds_seen s ! y}" using w_fresh by simp
  have card_grow: "card {y. y < vcount \<and> ds_seen t ! y} = Suc (card {y. y < vcount \<and> ds_seen s ! y})"
    using Vseen_grow fin wnotin by simp
  from ra have "Suc (card {y. y < vcount \<and> ds_seen s ! y}) = ds_snum s ! vcount + dcard s ?b"
    using stk_s_ne by (simp add: rootacc_def)
  hence "Suc (card {y. y < vcount \<and> ds_seen t ! y}) = ds_snum s ! vcount + Suc (dcard s ?b)"
    using card_grow by simp
  also have "... = ds_snum t ! vcount + dcard t ?b" using snum_root dcard_bot by simp
  finally show ?thesis using stk_ne bot_eq by (simp add: rootacc_def)
qed

lemma rootacc_append:
  assumes inv: "dfs_inv fl s" and ra: "rootacc s"
      and stk: "ds_stk s = v0 # rest"
      and wlt: "w < vcount" and unseen: "\<not> ds_seen s ! w"
      and t_seen: "ds_seen t = (ds_seen s)[w := True]"
      and t_prnt: "ds_prnt t = (ds_prnt s)[w := v0]"
      and t_snum: "ds_snum t = (ds_snum s)[w := 1]"
      and t_stk:  "ds_stk t = w # v0 # rest"
  shows "rootacc t"
proof -
  have wf: "dfs_wf fl s" and sz: "dfs_sized s" and tsi: "tree_seen_inv s" and spi: "stk_prnt_inv s"
    using inv by (auto simp: dfs_inv_def)
  have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount" "length (ds_snum s) = Suc vcount"
    using sz by (auto simp: dfs_sized_def)
  define b where "b = last (ds_stk s)"
  have b_in: "b \<in> stkverts s" using last_in_set[of "ds_stk s"] stk by (simp add: b_def stkverts_def)
  have v0in: "v0 \<in> stkverts s" using stk by (simp add: stkverts_def)
  have v0seen: "ds_seen s ! v0" using stkverts_props[OF wf v0in] by simp
  have v0nw: "v0 \<noteq> w" using v0seen unseen by auto
  have reach: "(v0, b) \<in> (pstep s)\<^sup>*" using stk_top_reaches[OF spi wf stk b_in] .
  have Vg: "{y. y < vcount \<and> ds_seen t ! y} = insert w {y. y < vcount \<and> ds_seen s ! y}"
    using t_seen wlt lens by (auto simp: nth_list_update)
  have snr: "ds_snum t ! vcount = ds_snum s ! vcount" using t_snum wlt by (simp add: nth_list_update)
  have stk_ne: "ds_stk t \<noteq> []" by (simp add: t_stk)
  have stk_s_ne: "ds_stk s \<noteq> []" by (simp add: stk)
  have bot_eq: "last (ds_stk t) = last (ds_stk s)" using t_stk stk by simp
  have desct: "desc t b = insert w (desc s b)"
  proof -
    have "desc t b = (if b = w \<or> (v0, b) \<in> (pstep s)\<^sup>* then insert w (desc s b) else desc s b)"
      by (rule desc_discover[OF tsi wlt unseen v0nw lens(1) lens(2) t_prnt t_seen])
    thus ?thesis using reach by simp
  qed
  have wnd: "w \<notin> desc s b" using unseen by (auto simp: desc_def)
  have dcard_bot: "dcard t (last (ds_stk s)) = Suc (dcard s (last (ds_stk s)))"
    using desct wnd b_def by (simp add: dcard_def desc_finite)
  show ?thesis using rootacc_discover_core[OF ra Vg wlt unseen snr stk_ne stk_s_ne bot_eq dcard_bot] .
qed

lemma rootacc_cong:
  assumes se: "ds_seen t = ds_seen s" and su: "ds_snum t = ds_snum s" and pr: "ds_prnt t = ds_prnt s"
      and sv: "ds_stk t = ds_stk s"
  shows "rootacc t = rootacc s"
proof -
  have pe: "pstep t = pstep s" using se pr by (simp add: pstep_def)
  have de: "\<And>x. desc t x = desc s x" using se pe by (simp add: desc_def)
  show ?thesis using se su de sv by (simp add: rootacc_def dcard_def)
qed

lemma emit_U_edge_rootacc: "rootacc s \<Longrightarrow> rootacc (emit_U_edge s v)"
  by (rule rootacc_cong[THEN iffD2, rotated -1]) (simp_all add: emit_U_edge_def Let_def)

lemma bd_upd3_rootacc:
  assumes inv: "dfs_inv fl s" and ra: "rootacc s" and c: "bd_call3_conds fl s"
  shows "rootacc (bd_upd3 s)"
proof -
  obtain v rest where stk: "ds_stk s = v # rest" and bu: "bd_upd3 s = dfs_finish s v rest"
    by (rule bd_upd3_eq[OF c])
  have wf: "dfs_wf fl s" and sz: "dfs_sized s" and spi: "stk_prnt_inv s" and sni: "snum_inv s"
    using inv by (auto simp: dfs_inv_def)
  have lens: "length (ds_snum s) = Suc vcount" using sz by (simp add: dfs_sized_def)
  define t where "t = dfs_finish s v rest"
  define p where "p = ds_prnt s ! v"
  have t_seen: "ds_seen t = ds_seen s" by (simp add: t_def dfs_finish_def Let_def)
  have t_prnt: "ds_prnt t = ds_prnt s" by (simp add: t_def dfs_finish_def Let_def)
  have t_snum: "ds_snum t = (ds_snum s)[p := ds_snum s ! p + ds_snum s ! v]" by (simp add: t_def dfs_finish_def Let_def p_def)
  have t_stk: "ds_stk t = rest" by (simp add: t_def dfs_finish_def Let_def)
  have pe: "pstep t = pstep s" using t_seen t_prnt by (simp add: pstep_def)
  have de: "\<And>x. desc t x = desc s x" using t_seen pe by (simp add: desc_def)
  have Ve: "{y. y < vcount \<and> ds_seen t ! y} = {y. y < vcount \<and> ds_seen s ! y}" using t_seen by simp
  have vc: "vchain (ds_prnt s) (v # rest)" using spi stk by (simp add: stk_prnt_inv_def)
  have snchk0: "snchk s 0 (v # rest)" using sni stk by (simp add: snum_inv_def del: snchk.simps)
  have dcv: "dcard s v = ds_snum s ! v" using snchk0 by simp
  have raU: "Suc (card {y. y < vcount \<and> ds_seen s ! y}) = ds_snum s ! vcount + dcard s (last (ds_stk s))"
    using ra stk by (simp add: rootacc_def)
  show "rootacc (bd_upd3 s)"
    unfolding bu t_def[symmetric]
  proof (cases rest)
    case Nil
    have pvc: "p = vcount" using vc Nil p_def by simp
    have snr: "ds_snum t ! vcount = ds_snum s ! vcount + ds_snum s ! v" using t_snum pvc lens by (simp add: nth_list_update)
    show "rootacc t" unfolding rootacc_def using Ve snr t_stk Nil raU stk dcv by simp
  next
    case (Cons gv rest2)
    have pg: "p = gv" using vc Cons p_def by simp
    have gin: "gv \<in> stkverts s" using stk Cons by (simp add: stkverts_def)
    have glt: "gv < vcount" using stkverts_props[OF wf gin] by simp
    have snr: "ds_snum t ! vcount = ds_snum s ! vcount" using t_snum pg glt by (simp add: nth_list_update)
    show "rootacc t" unfolding rootacc_def using Ve snr t_stk Cons raU stk de by (simp add: dcard_def)
  qed
qed

lemma bd_upd1_rootacc:
  assumes inv: "dfs_inv fl s" and ra: "rootacc s" and c: "bd_call1_conds fl s"
  shows "rootacc (bd_upd1 fl s)"
proof -
  have wf: "dfs_wf fl s" using inv by (simp add: dfs_inv_def)
  obtain v rest e w c' where stk: "ds_stk s = v # rest" and wlt: "w < vcount"
    and up: "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr> else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (rule bd_upd1_eq[OF wf c])
  show ?thesis
  proof (cases "ds_seen s ! w")
    case True
    have "rootacc (s\<lparr>ds_oc := c'\<rparr>) = rootacc s" by (rule rootacc_cong) simp_all
    thus ?thesis using up True ra by simp
  next
    case False
    have "rootacc (dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
      by (rule rootacc_append[OF inv ra stk wlt False]) (simp_all add: stk dfs_discover_def dfs_push_def Let_def)
    thus ?thesis using up False by simp
  qed
qed

lemma bd_upd2_rootacc:
  assumes inv: "dfs_inv fl s" and ra: "rootacc s" and c: "bd_call2_conds fl s"
  shows "rootacc (bd_upd2 fl s)"
proof -
  have wf: "dfs_wf fl s" using inv by (simp add: dfs_inv_def)
  obtain v rest e w c' where stk: "ds_stk s = v # rest" and wlt: "w < vcount"
    and up: "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr> else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    by (rule bd_upd2_eq[OF wf c])
  show ?thesis
  proof (cases "ds_seen s ! w")
    case True
    have "rootacc (s\<lparr>ds_ic := c'\<rparr>) = rootacc s" by (rule rootacc_cong) simp_all
    thus ?thesis using up True ra by simp
  next
    case False
    have "rootacc (dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
      by (rule rootacc_append[OF inv ra stk wlt False]) (simp_all add: stk dfs_discover_def dfs_push_def Let_def)
    thus ?thesis using up False by simp
  qed
qed

lemma build_dfs_rootacc:
  assumes dom: "build_dfs_dom (fl, s)" and inv: "dfs_inv fl s" and ra: "rootacc s"
  shows "rootacc (build_dfs fl s)"
  using inv ra
proof (induct rule: bd_induct[OF dom])
  case IH: (1 fl s)
  show ?case
    apply (rule bd_cases[where s = s and fl = fl])
    by (auto intro!: IH(2-4) bd_upd1_inv bd_upd2_inv bd_upd3_inv
                     bd_upd1_rootacc bd_upd2_rootacc bd_upd3_rootacc IH(5) IH(6)
             simp: bd_simps[OF IH(1)])
qed

lemma rootacc_seed:
  assumes inv: "dfs_inv acyc_flow s" and ra: "rootacc s" and stke: "ds_stk s = []"
      and c: "c < vcount" and unseen: "\<not> ds_seen s ! c"
      and t_seen: "ds_seen t = (ds_seen s)[c := True]"
      and t_prnt: "ds_prnt t = (ds_prnt s)[c := vcount]"
      and t_snum: "ds_snum t = (ds_snum s)[c := 1]"
      and t_stk:  "ds_stk t = [c]"
  shows "rootacc t"
proof -
  have sz: "dfs_sized s" and tsi: "tree_seen_inv s" using inv by (auto simp: dfs_inv_def)
  have lens: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount" using sz by (auto simp: dfs_sized_def)
  have Vg: "{y. y < vcount \<and> ds_seen t ! y} = insert c {y. y < vcount \<and> ds_seen s ! y}"
    using t_seen c lens by (auto simp: nth_list_update)
  have cnotin: "c \<notin> {y. y < vcount \<and> ds_seen s ! y}" using unseen by simp
  have cardg: "card {y. y < vcount \<and> ds_seen t ! y} = Suc (card {y. y < vcount \<and> ds_seen s ! y})"
    using Vg cnotin by simp
  have snr: "ds_snum t ! vcount = ds_snum s ! vcount" using t_snum c by (simp add: nth_list_update)
  have vne: "vcount \<noteq> c" using c by simp
  have "desc t c = (if c = c \<or> (vcount, c) \<in> (pstep s)\<^sup>* then insert c (desc s c) else desc s c)"
    by (rule desc_discover[OF tsi c unseen vne lens(1) lens(2) t_prnt t_seen])
  hence dtc: "desc t c = insert c (desc s c)" by simp
  have "desc s c = {}" using desc_fresh_empty[OF tsi c unseen] .
  hence dcard_c: "dcard t c = 1" using dtc by (simp add: dcard_def)
  have raU: "Suc (card {y. y < vcount \<and> ds_seen s ! y}) = ds_snum s ! vcount" using ra stke by (simp add: rootacc_def)
  have "Suc (card {y. y < vcount \<and> ds_seen t ! y}) = ds_snum t ! vcount + dcard t c"
    using cardg snr dcard_c raU by simp
  thus ?thesis using t_stk by (simp add: rootacc_def)
qed

lemma open_tree_component_rootacc:
  assumes inv: "dfs_inv acyc_flow s" and ra: "rootacc s" and c: "c < vcount"
      and unseen: "\<not> ds_seen s ! c" and cnz: "c \<noteq> 0" and stke: "ds_stk s = []"
  shows "rootacc (open_tree_component acyc_flow s c)"
proof -
  have "dfs_wf acyc_flow s" "dfs_sized s" using inv by (simp_all add: dfs_inv_def)
  then obtain sd where opd: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd"
    and dom: "build_dfs_dom (acyc_flow, sd)"
    and I: "(dfs_inv acyc_flow s \<and> \<not> ds_seen s ! c \<and> c \<noteq> 0 \<and> ds_stk s = []) \<longrightarrow> dfs_inv acyc_flow sd"
    and stk: "ds_stk sd = [c]" and seen: "ds_seen sd = (ds_seen s)[c := True]"
    and prnt: "ds_prnt sd = (ds_prnt s)[c := vcount]" and snum: "ds_snum sd = (ds_snum s)[c := 1]"
    using c by (rule open_tree_component_seed)
  have "rootacc sd" by (rule rootacc_seed[OF inv ra stke c unseen seen prnt snum stk])
  thus ?thesis unfolding opd using build_dfs_rootacc[OF dom] I inv unseen cnz stke by blast
qed

lemma phase1_step_rootacc:
  assumes v: "v \<in> set vs_list" and pre: "dfs_inv acyc_flow s \<and> ds_stk s = []" and ra: "rootacc s"
  shows "rootacc (phase1_step acyc_flow v s)"
proof -
  have inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" using pre by auto
  show ?thesis
  proof (cases "imbalance ! v = 0")
    case True thus ?thesis using ra by (simp add: phase1_step_def)
  next
    case nz: False
    show ?thesis
    proof (cases "ds_seen s ! v")
      case True thus ?thesis using nz emit_U_edge_rootacc[OF ra] by (simp add: phase1_step_def)
    next
      case False
      have vlt: "v < vcount" using vs_less_vcount[OF v] .
      have vnz: "v \<noteq> 0" using v no_zero_node by metis
      thus ?thesis using nz False open_tree_component_rootacc[OF inv ra vlt False vnz stke]
        by (simp add: phase1_step_def)
    qed
  qed
qed

lemma phase2_step_rootacc:
  assumes v: "v \<in> set vs_list" and pre: "dfs_inv acyc_flow s \<and> ds_stk s = []" and ra: "rootacc s"
  shows "rootacc (phase2_step acyc_flow v s)"
proof -
  have inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" using pre by auto
  show ?thesis
  proof (cases "ds_seen s ! v")
    case True thus ?thesis using ra by (simp add: phase2_step_def)
  next
    case False
    note ns = this
    have vlt: "v < vcount" using vs_less_vcount[OF v] .
    show ?thesis
    proof (cases "is_lonely v")
      case True thus ?thesis using ra by (simp add: phase2_step_def)
    next
      case False
      note nl = this
      have vnz: "v \<noteq> 0" using v no_zero_node by metis
      have eq: "phase2_step acyc_flow v s = open_tree_component acyc_flow s v" by (simp add: phase2_step_def ns nl)
      thus ?thesis using open_tree_component_rootacc[OF inv ra vlt ns vnz stke] by simp
    qed
  qed
qed

lemma phase1_rootacc:
  assumes pre: "dfs_inv acyc_flow s \<and> ds_stk s = []" and ra: "rootacc s"
  shows "rootacc (phase1 acyc_flow s)"
proof -
  let ?P = "\<lambda>s. (dfs_inv acyc_flow s \<and> ds_stk s = []) \<and> rootacc s"
  have "?P (fold (phase1_step acyc_flow) vs_list s)"
  proof (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = ?P])
    show "\<And>x. x \<in> set vs_list \<Longrightarrow> x \<in> set vs_list" by simp
    show "?P s" using pre ra by simp
    fix x t assume x: "x \<in> set vs_list" and Pt: "?P t"
    show "?P (phase1_step acyc_flow x t)"
      using phase1_step_inv[OF x conjunct1[OF Pt]] phase1_step_rootacc[OF x conjunct1[OF Pt] conjunct2[OF Pt]]
      by simp
  qed
  thus ?thesis unfolding phase1_def by simp
qed

lemma phase2_rootacc:
  assumes pre: "dfs_inv acyc_flow s \<and> ds_stk s = []" and ra: "rootacc s"
  shows "rootacc (phase2 acyc_flow s)"
proof -
  let ?P = "\<lambda>s. (dfs_inv acyc_flow s \<and> ds_stk s = []) \<and> rootacc s"
  have "?P (fold (phase2_step acyc_flow) vs_list s)"
  proof (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = ?P])
    show "\<And>x. x \<in> set vs_list \<Longrightarrow> x \<in> set vs_list" by simp
    show "?P s" using pre ra by simp
    fix x t assume x: "x \<in> set vs_list" and Pt: "?P t"
    show "?P (phase2_step acyc_flow x t)"
      using phase2_step_inv[OF x conjunct1[OF Pt]] phase2_step_rootacc[OF x conjunct1[OF Pt] conjunct2[OF Pt]]
      by simp
  qed
  thus ?thesis unfolding phase2_def by simp
qed

lemma build_tree_rootacc: "rootacc (build_tree acyc_flow)"
proof -
  have i0: "dfs_inv acyc_flow dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have p1: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init) \<and> ds_stk (phase1 acyc_flow dfs_init) = []" using phase1_inv[OF i0] .
  have r1: "rootacc (phase1 acyc_flow dfs_init)" using phase1_rootacc[OF i0 dfs_init_rootacc] .
  have r2: "rootacc (phase2 acyc_flow (phase1 acyc_flow dfs_init))" using phase2_rootacc[OF p1 r1] .
  have "rootacc (build_tree acyc_flow) = rootacc (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
    unfolding build_tree_def Let_def by (rule rootacc_cong) simp_all
  thus ?thesis using r2 by simp
qed

lemma build_tree_root_snum: "ds_snum (build_tree acyc_flow) ! vcount = card Varb"
proof -
  have "Suc (card {y. y < vcount \<and> ds_seen (build_tree acyc_flow) ! y}) = ds_snum (build_tree acyc_flow) ! vcount + 0"
    using build_tree_rootacc build_tree_stk_empty by (simp add: rootacc_def)
  hence "ds_snum (build_tree acyc_flow) ! vcount = Suc (card Vseen)" by (simp add: Vseen_def)
  also have "... = card Varb"
  proof -
    have "vcount \<notin> Vseen" by (simp add: Vseen_def)
    thus ?thesis using Vseen_finite by (simp add: Varb_def)
  qed
  finally show ?thesis .
qed

lemma children_Sprnt_root: "children Sprnt vcount = Varb"
proof (rule equalityI)
  show "children Sprnt vcount \<subseteq> Varb" using children_sub_Varb[OF r_in_V] .
next
  show "Varb \<subseteq> children Sprnt vcount"
  proof
    fix u assume uV: "u \<in> Varb"
    have "(u, vcount) \<in> (pstep (build_tree acyc_flow))\<^sup>*"
    proof (cases "u = vcount")
      case True thus ?thesis by simp
    next
      case False
      hence "u \<in> Vseen" using uV by (auto simp: Varb_def)
      hence "u < vcount \<and> ds_seen (build_tree acyc_flow) ! u" by (auto simp: Vseen_def)
      thus ?thesis using build_tree_reaches_root by auto
    qed
    thus "u \<in> children Sprnt vcount" by (auto simp: children_def follow_Sprnt_pstep)
  qed
qed

lemma snum_eq_children_all:
  assumes "v \<in> Varb" shows "snum Sarb v = card (children (prnt Sarb) v)"
proof (cases "v = vcount")
  case True
  have "snum Sarb vcount = card Varb" using build_tree_root_snum by (simp add: Sarb_sel)
  thus ?thesis using True children_Sprnt_root by (simp add: Sarb_sel)
next
  case False
  hence "v \<in> Vseen" using assms by (auto simp: Varb_def)
  thus ?thesis using snum_eq_children by simp
qed

subsection \<open>The complete @{const arb_invar} assembly\<close>

text \<open>All ten obligations of @{thm arb_invarI} now discharged: @{term Sarb} is a valid threaded rooted
      arborescence on @{term Varb} with root @{term vcount}.\<close>

lemma arb_invar_Sarb: "arb_invar vcount Varb Sarb"
proof (rule arb_invarI)
  show "rooted_arborescense_invar vcount Varb (prnt Sarb)"
    using rooted_arb_invar_Sprnt by (simp add: Sarb_sel)
  show "parent_spec (thrd Sarb)" using parent_spec_Sthrd by (simp add: Sarb_sel)
  show "parent_spec (rvth Sarb)" using parent_spec_Srvth by (simp add: Sarb_sel)
  show "set (follow (thrd Sarb) vcount) = Varb" using follow_Sthrd_spans by (simp add: Sarb_sel)
  show "dom (thrd Sarb) = Varb - {lsuc Sarb vcount}"
    using dom_Sthrd lsuc_root_eq_prev by (simp add: Sarb_sel)
  show "dom (rvth Sarb) = Varb - {vcount}" using dom_Srvth by (simp add: Sarb_sel)
  show "\<forall>v v'. thrd Sarb v = Some v' \<longleftrightarrow> rvth Sarb v' = Some v"
    using thrd_rvth_inverse by (simp add: Sarb_sel)
  show "\<forall>v \<in> Varb. lsuc Sarb v \<in> Varb" using lsuc_in_V_all by simp
  show "\<forall>v \<in> Varb. snum Sarb v = card (children (prnt Sarb) v)" using snum_eq_children_all by simp
  show "\<forall>v \<in> Varb. \<exists>pre. follow (thrd Sarb) v
           = pre @ (case thrd Sarb (lsuc Sarb v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd Sarb) w)
         \<and> pre \<noteq> [] \<and> last pre = lsuc Sarb v \<and> set pre = children (prnt Sarb) v"
    unfolding Sarb_sel(1) Sarb_sel(2) using clause_J by blast
qed

subsection \<open>Assembly substrate: the DFS body leaves the artificial-edge tails untouched\<close>

text \<open>Towards the @{const network_simplex_init} obligations for the constructed basis: the artificial-edge
      tails (@{const ds_afst} / @{const ds_asnd} / @{const ds_acap} / @{const ds_aflw} / @{const ds_aest})
      and the cursor @{const ds_nxt} are written only by @{const open_tree_component} / @{const emit_U_edge};
      the traversal @{const build_dfs} preserves them. This is the base for characterising which artificial
      edges the build emits (needed by \<open>init_bflow\<close> / \<open>init_partition\<close> / \<open>init_flow_fits\<close>).\<close>

lemma bd_upd1_art:
  assumes "bd_call1_conds fl s"
  shows "ds_nxt (bd_upd1 fl s) = ds_nxt s \<and> ds_afst (bd_upd1 fl s) = ds_afst s \<and> ds_asnd (bd_upd1 fl s) = ds_asnd s \<and> ds_acap (bd_upd1 fl s) = ds_acap s \<and> ds_aflw (bd_upd1 fl s) = ds_aflw s \<and> ds_aest (bd_upd1 fl s) = ds_aest s"
  using assms by (auto simp: bd_upd1_def bd_call1_conds_def dfs_discover_def dfs_push_def Let_def split: list.splits)

lemma bd_upd2_art:
  assumes "bd_call2_conds fl s"
  shows "ds_nxt (bd_upd2 fl s) = ds_nxt s \<and> ds_afst (bd_upd2 fl s) = ds_afst s \<and> ds_asnd (bd_upd2 fl s) = ds_asnd s \<and> ds_acap (bd_upd2 fl s) = ds_acap s \<and> ds_aflw (bd_upd2 fl s) = ds_aflw s \<and> ds_aest (bd_upd2 fl s) = ds_aest s"
  using assms by (auto simp: bd_upd2_def bd_call2_conds_def dfs_discover_def dfs_push_def Let_def split: list.splits)

lemma bd_upd3_art:
  assumes "bd_call3_conds fl s"
  shows "ds_nxt (bd_upd3 s) = ds_nxt s \<and> ds_afst (bd_upd3 s) = ds_afst s \<and> ds_asnd (bd_upd3 s) = ds_asnd s \<and> ds_acap (bd_upd3 s) = ds_acap s \<and> ds_aflw (bd_upd3 s) = ds_aflw s \<and> ds_aest (bd_upd3 s) = ds_aest s"
proof -
  obtain v rest where "bd_upd3 s = dfs_finish s v rest" by (rule bd_upd3_eq[OF assms])
  thus ?thesis by (simp add: dfs_finish_def Let_def)
qed

lemma build_dfs_art:
  assumes dom: "build_dfs_dom (fl, s)"
  shows "ds_nxt (build_dfs fl s) = ds_nxt s \<and> ds_afst (build_dfs fl s) = ds_afst s \<and> ds_asnd (build_dfs fl s) = ds_asnd s
         \<and> ds_acap (build_dfs fl s) = ds_acap s \<and> ds_aflw (build_dfs fl s) = ds_aflw s \<and> ds_aest (build_dfs fl s) = ds_aest s"
proof (induct rule: bd_induct[OF dom])
  case IH: (1 fl s)
  show ?case
    apply (rule bd_cases[where s = s and fl = fl])
    by (auto simp: bd_simps[OF IH(1)] bd_ret_conds_def IH(2) IH(3) IH(4) bd_upd1_art bd_upd2_art bd_upd3_art)
qed

text \<open>So opening a component writes exactly its own artificial edge, at the cursor.\<close>

lemma open_tree_component_art:
  assumes inv: "dfs_inv fl s" and c: "c < vcount"
  shows "ds_nxt (open_tree_component fl s c) = Suc (ds_nxt s)"
    and "ds_afst (open_tree_component fl s c) = (ds_afst s)[ds_nxt s := (if art_dir c then c else vcount)]"
    and "ds_asnd (open_tree_component fl s c) = (ds_asnd s)[ds_nxt s := (if art_dir c then vcount else c)]"
    and "ds_acap (open_tree_component fl s c) = (ds_acap s)[ds_nxt s := art_tree_cap c]"
    and "ds_aflw (open_tree_component fl s c) = (ds_aflw s)[ds_nxt s := art_flow c]"
    and "ds_aest (open_tree_component fl s c) = (ds_aest s)[ds_nxt s := InTree]"
proof -
  have "dfs_wf fl s" "dfs_sized s" using inv by (simp_all add: dfs_inv_def)
  then obtain sd where opd: "open_tree_component fl s c = build_dfs fl sd" and dom: "build_dfs_dom (fl, sd)"
    and "ds_nxt sd = Suc (ds_nxt s)"
    and "ds_afst sd = (ds_afst s)[ds_nxt s := (if art_dir c then c else vcount)]"
    and "ds_asnd sd = (ds_asnd s)[ds_nxt s := (if art_dir c then vcount else c)]"
    and "ds_acap sd = (ds_acap s)[ds_nxt s := art_tree_cap c]"
    and "ds_aflw sd = (ds_aflw s)[ds_nxt s := art_flow c]"
    and "ds_aest sd = (ds_aest s)[ds_nxt s := InTree]"
    using c by (rule open_tree_component_seed)
  moreover note build_dfs_art[OF dom]
  ultimately show "ds_nxt (open_tree_component fl s c) = Suc (ds_nxt s)"
    and "ds_afst (open_tree_component fl s c) = (ds_afst s)[ds_nxt s := (if art_dir c then c else vcount)]"
    and "ds_asnd (open_tree_component fl s c) = (ds_asnd s)[ds_nxt s := (if art_dir c then vcount else c)]"
    and "ds_acap (open_tree_component fl s c) = (ds_acap s)[ds_nxt s := art_tree_cap c]"
    and "ds_aflw (open_tree_component fl s c) = (ds_aflw s)[ds_nxt s := art_flow c]"
    and "ds_aest (open_tree_component fl s c) = (ds_aest s)[ds_nxt s := InTree]"
    by simp_all
qed

subsection \<open>Assembly substrate: the artificial-edge count is in bounds\<close>

text \<open>Each @{const open_tree_component} / @{const emit_U_edge} increments the artificial-edge cursor
      @{const ds_nxt} by exactly one and leaves its subject vertex seen; @{const build_dfs} preserves it.
      Since every vertex of @{term vs_list} is the subject of at most one emission (opened XOR emitted-as-U
      in phase 1, or opened-if-unseen in phase 2), the total number of artificial edges
      @{term \<open>ds_nxt (build_tree acyc_flow)\<close>} is at most @{term \<open>length vs_list\<close>} --- so the pre-sized artificial tails
      (length @{term \<open>length vs_list\<close>}) hold every emitted edge without dropping any.\<close>

lemma emit_U_edge_nxt: "ds_nxt (emit_U_edge s v) = Suc (ds_nxt s)"
  by (simp add: emit_U_edge_def Let_def)

lemma phase1_step_seen_mono:
  assumes "dfs_inv acyc_flow s" "v < vcount" "ds_seen s ! x"
  shows "ds_seen (phase1_step acyc_flow v s) ! x"
proof (cases "imbalance ! v = 0")
  case True thus ?thesis using assms(3) by (simp add: phase1_step_def)
next
  case nz: False
  show ?thesis
  proof (cases "ds_seen s ! v")
    case True thus ?thesis using assms(3) nz by (simp add: phase1_step_def emit_U_edge_def Let_def)
  next
    case Fv: False
    thus ?thesis using nz open_tree_component_seen_mono[OF assms(1) assms(2) assms(3)] by (simp add: phase1_step_def)
  qed
qed

lemma phase1_step_nxt:
  assumes inv: "dfs_inv acyc_flow s" and v: "v < vcount"
  shows "ds_nxt (phase1_step acyc_flow v s) = ds_nxt s \<or> (ds_nxt (phase1_step acyc_flow v s) = Suc (ds_nxt s) \<and> ds_seen (phase1_step acyc_flow v s) ! v)"
proof (cases "imbalance ! v = 0")
  case True thus ?thesis by (simp add: phase1_step_def)
next
  case nz: False
  show ?thesis
  proof (cases "ds_seen s ! v")
    case True
    have "ds_nxt (phase1_step acyc_flow v s) = Suc (ds_nxt s)" using nz True by (simp add: phase1_step_def emit_U_edge_nxt)
    moreover have "ds_seen (phase1_step acyc_flow v s) ! v" using nz True by (simp add: phase1_step_def emit_U_edge_def Let_def)
    ultimately show ?thesis by simp
  next
    case Fv: False
    have "ds_nxt (phase1_step acyc_flow v s) = Suc (ds_nxt s)" using nz Fv open_tree_component_art(1)[OF inv v] by (simp add: phase1_step_def)
    moreover have "ds_seen (phase1_step acyc_flow v s) ! v" using nz Fv open_tree_component_marks[OF inv v] by (simp add: phase1_step_def)
    ultimately show ?thesis by simp
  qed
qed

lemma phase2_step_nxt2:
  assumes inv: "dfs_inv acyc_flow s" and v: "v < vcount"
  shows "ds_nxt (phase2_step acyc_flow v s) = ds_nxt s \<or> (ds_nxt (phase2_step acyc_flow v s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! v \<and> ds_seen (phase2_step acyc_flow v s) ! v)"
proof (cases "ds_seen s ! v")
  case True thus ?thesis by (simp add: phase2_step_def)
next
  case notseen: False
  show ?thesis
  proof (cases "is_lonely v")
    case True
    hence "phase2_step acyc_flow v s = s" using notseen by (simp add: phase2_step_def)
    thus ?thesis by simp
  next
    case False
    have "ds_nxt (phase2_step acyc_flow v s) = Suc (ds_nxt s)" using notseen False open_tree_component_art(1)[OF inv v] by (simp add: phase2_step_def)
    moreover have "ds_seen (phase2_step acyc_flow v s) ! v" using notseen False open_tree_component_marks[OF inv v] by (simp add: phase2_step_def)
    ultimately show ?thesis using notseen by simp
  qed
qed

text \<open>Fold-level emission bound (distinctness freshness, for phase 1): the number of artificial edges
      emitted by a scan over @{term vs_list} equals the cardinality of a set of \<^emph>\<open>seen\<close> @{term vs_list}
      vertices (the emission subjects), each fresh because @{term vs_list} is distinct.\<close>

lemma fold_emit_bnd:
  assumes step_inv: "\<And>v t. v \<in> set vs_list \<Longrightarrow> dfs_inv acyc_flow t \<Longrightarrow> ds_stk t = [] \<Longrightarrow> dfs_inv acyc_flow (g v t) \<and> ds_stk (g v t) = []"
      and step_mono: "\<And>v t y. v \<in> set vs_list \<Longrightarrow> dfs_inv acyc_flow t \<Longrightarrow> ds_seen t ! y \<Longrightarrow> ds_seen (g v t) ! y"
      and step_nxt: "\<And>v t. v \<in> set vs_list \<Longrightarrow> dfs_inv acyc_flow t \<Longrightarrow> ds_stk t = [] \<Longrightarrow>
                        ds_nxt (g v t) = ds_nxt t \<or> (ds_nxt (g v t) = Suc (ds_nxt t) \<and> ds_seen (g v t) ! v)"
      and "distinct xs" "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      and "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "E \<inter> set xs = {}" "ds_nxt s = card E"
  shows "\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold g xs s) ! v} \<and> ds_nxt (fold g xs s) = card E'"
  using assms(4-11)
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(2) by simp
  have inv1: "dfs_inv acyc_flow (g x s)" "ds_stk (g x s) = []" using step_inv[OF xvs Cons.prems(3,4)] by auto
  have Emono: "E \<subseteq> {v \<in> set vs_list. ds_seen (g x s) ! v}" using Cons.prems(6) step_mono[OF xvs Cons.prems(3)] by auto
  have Edisj: "E \<inter> set rest = {}" using Cons.prems(7) by auto
  have distr: "distinct rest" using Cons.prems(1) by simp
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(2) by simp
  from step_nxt[OF xvs Cons.prems(3,4)] show ?case
  proof
    assume A: "ds_nxt (g x s) = ds_nxt s"
    have "ds_nxt (g x s) = card E" using A Cons.prems(8) by simp
    thus ?thesis using Cons.hyps[OF distr subr inv1(1) inv1(2) Cons.prems(5) Emono Edisj] by simp
  next
    assume B: "ds_nxt (g x s) = Suc (ds_nxt s) \<and> ds_seen (g x s) ! x"
    define E2 where "E2 = insert x E"
    have xnotE: "x \<notin> E" using Cons.prems(7) by auto
    have fin2: "finite E2" using Cons.prems(5) by (simp add: E2_def)
    have E2seen: "E2 \<subseteq> {v \<in> set vs_list. ds_seen (g x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have E2disj: "E2 \<inter> set rest = {}" using Edisj Cons.prems(1) by (auto simp: E2_def)
    have card2: "ds_nxt (g x s) = card E2" using B Cons.prems(8) xnotE Cons.prems(5) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF distr subr inv1(1) inv1(2) fin2 E2seen E2disj card2] by simp
  qed
qed

text \<open>Fold-level emission bound (seen freshness, for phase 2): here the scan only emits for \<^emph>\<open>unseen\<close>
      vertices (it opens them), so the new subject is fresh because the accumulated set is a set of seen
      vertices --- no distinctness needed, and the initial set may already meet @{term vs_list}.\<close>

lemma fold_emit_bnd2:
  assumes step_inv: "\<And>v t. v \<in> set vs_list \<Longrightarrow> dfs_inv acyc_flow t \<Longrightarrow> ds_stk t = [] \<Longrightarrow> dfs_inv acyc_flow (g v t) \<and> ds_stk (g v t) = []"
      and step_mono: "\<And>v t y. v \<in> set vs_list \<Longrightarrow> dfs_inv acyc_flow t \<Longrightarrow> ds_seen t ! y \<Longrightarrow> ds_seen (g v t) ! y"
      and step_nxt2: "\<And>v t. v \<in> set vs_list \<Longrightarrow> dfs_inv acyc_flow t \<Longrightarrow> ds_stk t = [] \<Longrightarrow>
                        ds_nxt (g v t) = ds_nxt t \<or> (ds_nxt (g v t) = Suc (ds_nxt t) \<and> \<not> ds_seen t ! v \<and> ds_seen (g v t) ! v)"
      and "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      and "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "ds_nxt s = card E"
  shows "\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold g xs s) ! v} \<and> ds_nxt (fold g xs s) = card E'"
  using assms(4-9)
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(1) by simp
  have inv1: "dfs_inv acyc_flow (g x s)" "ds_stk (g x s) = []" using step_inv[OF xvs Cons.prems(2,3)] by auto
  have Emono: "E \<subseteq> {v \<in> set vs_list. ds_seen (g x s) ! v}" using Cons.prems(5) step_mono[OF xvs Cons.prems(2)] by auto
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(1) by simp
  from step_nxt2[OF xvs Cons.prems(2,3)] show ?case
  proof
    assume A: "ds_nxt (g x s) = ds_nxt s"
    have "ds_nxt (g x s) = card E" using A Cons.prems(6) by simp
    thus ?thesis using Cons.hyps[OF subr inv1(1) inv1(2) Cons.prems(4) Emono] by simp
  next
    assume B: "ds_nxt (g x s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! x \<and> ds_seen (g x s) ! x"
    define E2 where "E2 = insert x E"
    have xnotE: "x \<notin> E" using B Cons.prems(5) by auto
    have fin2: "finite E2" using Cons.prems(4) by (simp add: E2_def)
    have E2seen: "E2 \<subseteq> {v \<in> set vs_list. ds_seen (g x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have card2: "ds_nxt (g x s) = card E2" using B Cons.prems(6) xnotE Cons.prems(4) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF subr inv1(1) inv1(2) fin2 E2seen card2] by simp
  qed
qed

lemma phase1_emit:
  "\<exists>E. finite E \<and> E \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v} \<and> ds_nxt (phase1 acyc_flow dfs_init) = card E"
  unfolding phase1_def
  apply (rule fold_emit_bnd[where E = "{}"])
  subgoal by (metis phase1_step_inv)
  subgoal by (metis phase1_step_seen_mono vs_less_vcount)
  subgoal by (metis phase1_step_nxt vs_less_vcount)
  subgoal by (rule distinct_vs_list)
  subgoal by simp
  subgoal using dfs_init_inv by (simp add: dfs_init_def)
  subgoal by (simp add: dfs_init_def)
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal by (simp add: dfs_init_def)
  done

lemma build_tree_nxt_le: "ds_nxt (build_tree acyc_flow) \<le> length vs_list"
proof -
  have i0: "dfs_inv acyc_flow dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have p1: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init) \<and> ds_stk (phase1 acyc_flow dfs_init) = []" using phase1_inv[OF i0] .
  obtain E1 where E1f: "finite E1" and E1s: "E1 \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}"
    and E1n: "ds_nxt (phase1 acyc_flow dfs_init) = card E1"
    using phase1_emit by metis
  have E2ex: "\<exists>E. finite E \<and> E \<subseteq> {v \<in> set vs_list. ds_seen (phase2 acyc_flow (phase1 acyc_flow dfs_init)) ! v} \<and> ds_nxt (phase2 acyc_flow (phase1 acyc_flow dfs_init)) = card E"
    unfolding phase2_def
    apply (rule fold_emit_bnd2[where E = E1 and s = "phase1 acyc_flow dfs_init"])
    subgoal by (metis phase2_step_inv)
    subgoal by (metis phase2_step_seen_mono vs_less_vcount)
    subgoal by (metis phase2_step_nxt2 vs_less_vcount)
    subgoal by simp
    subgoal using p1 by simp
    subgoal using p1 by simp
    subgoal by (rule E1f)
    subgoal by (rule E1s)
    subgoal by (rule E1n)
    done
  from E2ex obtain E2 where E2f: "finite E2"
    and E2s: "E2 \<subseteq> {v \<in> set vs_list. ds_seen (phase2 acyc_flow (phase1 acyc_flow dfs_init)) ! v}"
    and E2n: "ds_nxt (phase2 acyc_flow (phase1 acyc_flow dfs_init)) = card E2" by blast
  have "E2 \<subseteq> set vs_list" by (rule subset_trans[OF E2s Collect_subset])
  hence "card E2 \<le> card (set vs_list)" by (simp add: card_mono)
  hence "ds_nxt (phase2 acyc_flow (phase1 acyc_flow dfs_init)) \<le> length vs_list"
    using E2n distinct_vs_list by (simp add: distinct_card)
  thus ?thesis by (simp add: build_tree_def Let_def)
qed

subsection \<open>Assembly substrate: the artificial-edge tails keep length @{term \<open>length vs_list\<close>}\<close>

text \<open>The tails are pre-sized to @{term \<open>length vs_list\<close>} at @{const dfs_init} and only ever updated
      in place (@{const List.list_update}) or left untouched by @{const build_dfs}, so their length is
      invariant. With @{thm build_tree_nxt_le} this shows every artificial edge the build emits lands
      inside the tails --- the well-formedness the augmented edge arrays need.\<close>

definition art_len :: "'n dfs_state \<Rightarrow> bool" where
  "art_len s \<longleftrightarrow> length (ds_afst s) = length vs_list \<and> length (ds_asnd s) = length vs_list
     \<and> length (ds_acap s) = length vs_list \<and> length (ds_aflw s) = length vs_list \<and> length (ds_aest s) = length vs_list"

lemma dfs_init_art_len: "art_len dfs_init"
  by (simp add: art_len_def dfs_init_def)

lemma emit_U_edge_art_len: "art_len s \<Longrightarrow> art_len (emit_U_edge s v)"
  by (simp add: art_len_def emit_U_edge_def Let_def)

lemma open_tree_component_art_len:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and al: "art_len s"
  shows "art_len (open_tree_component acyc_flow s c)"
  using open_tree_component_art[OF inv c] al by (simp add: art_len_def)

lemma phase1_step_art_len:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and al: "art_len s"
  shows "art_len (phase1_step acyc_flow v s)"
proof (cases "imbalance ! v = 0")
  case True thus ?thesis using al by (simp add: phase1_step_def)
next
  case nz: False
  show ?thesis
  proof (cases "ds_seen s ! v")
    case True thus ?thesis using nz al emit_U_edge_art_len by (simp add: phase1_step_def)
  next
    case False
    have vlt: "v < vcount" using v vs_less_vcount by simp
    thus ?thesis using nz False open_tree_component_art_len[OF inv vlt al] by (simp add: phase1_step_def)
  qed
qed

lemma phase2_step_art_len:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and al: "art_len s"
  shows "art_len (phase2_step acyc_flow v s)"
proof (cases "ds_seen s ! v \<or> is_lonely v")
  case True thus ?thesis using al by (simp add: phase2_step_def)
next
  case False
  hence notseen: "\<not> ds_seen s ! v" and nl: "\<not> is_lonely v" by auto
  have vlt: "v < vcount" using v vs_less_vcount by simp
  thus ?thesis using notseen nl open_tree_component_art_len[OF inv vlt al] by (simp add: phase2_step_def)
qed

lemma phase1_art_len:
  assumes pre: "dfs_inv acyc_flow s \<and> ds_stk s = []" and al: "art_len s"
  shows "art_len (phase1 acyc_flow s)"
proof -
  let ?P = "\<lambda>s. (dfs_inv acyc_flow s \<and> ds_stk s = []) \<and> art_len s"
  have "?P (fold (phase1_step acyc_flow) vs_list s)"
  proof (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = ?P])
    show "\<And>x. x \<in> set vs_list \<Longrightarrow> x \<in> set vs_list" by simp
    show "?P s" using pre al by simp
    fix x t assume x: "x \<in> set vs_list" and Pt: "?P t"
    show "?P (phase1_step acyc_flow x t)"
      using phase1_step_inv[OF x conjunct1[OF Pt]] phase1_step_art_len[OF x conjunct1[OF conjunct1[OF Pt]] conjunct2[OF Pt]]
      by simp
  qed
  thus ?thesis unfolding phase1_def by simp
qed

lemma phase2_art_len:
  assumes pre: "dfs_inv acyc_flow s \<and> ds_stk s = []" and al: "art_len s"
  shows "art_len (phase2 acyc_flow s)"
proof -
  let ?P = "\<lambda>s. (dfs_inv acyc_flow s \<and> ds_stk s = []) \<and> art_len s"
  have "?P (fold (phase2_step acyc_flow) vs_list s)"
  proof (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = ?P])
    show "\<And>x. x \<in> set vs_list \<Longrightarrow> x \<in> set vs_list" by simp
    show "?P s" using pre al by simp
    fix x t assume x: "x \<in> set vs_list" and Pt: "?P t"
    show "?P (phase2_step acyc_flow x t)"
      using phase2_step_inv[OF x conjunct1[OF Pt]] phase2_step_art_len[OF x conjunct1[OF conjunct1[OF Pt]] conjunct2[OF Pt]]
      by simp
  qed
  thus ?thesis unfolding phase2_def by simp
qed

lemma build_tree_art_len: "art_len (build_tree acyc_flow)"
proof -
  have i0: "dfs_inv acyc_flow dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have p1: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init) \<and> ds_stk (phase1 acyc_flow dfs_init) = []" using phase1_inv[OF i0] .
  have a1: "art_len (phase1 acyc_flow dfs_init)" using phase1_art_len[OF i0 dfs_init_art_len] .
  have a2: "art_len (phase2 acyc_flow (phase1 acyc_flow dfs_init))" using phase2_art_len[OF p1 a1] .
  thus ?thesis by (simp add: build_tree_def Let_def art_len_def)
qed

subsection \<open>Assembly substrate: what each emission writes into the artificial tails\<close>

text \<open>Each @{const open_tree_component} (a component-tree edge, tag @{const InTree}) and each
      @{const emit_U_edge} (a saturated bound edge, tag @{const InU}) records, at the artificial cursor
      @{const ds_nxt}, exactly the subject vertex's @{const art_dir}-oriented endpoints together with its
      @{const art_flow} / @{const art_tree_cap}. These per-emission content facts feed \<open>init_bflow\<close> /
      \<open>init_partition\<close> / \<open>init_flow_fits\<close> / \<open>init_pot_fits\<close>.\<close>

lemma open_tree_component_afst_at:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and inb: "ds_nxt s < length vs_list" and al: "art_len s"
  shows "ds_afst (open_tree_component acyc_flow s c) ! (ds_nxt s) = (if art_dir c then c else vcount)"
  using open_tree_component_art(2)[OF inv c] inb al by (simp add: art_dir_def art_len_def)

lemma open_tree_component_asnd_at:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and inb: "ds_nxt s < length vs_list" and al: "art_len s"
  shows "ds_asnd (open_tree_component acyc_flow s c) ! (ds_nxt s) = (if art_dir c then vcount else c)"
  using open_tree_component_art(3)[OF inv c] inb al by (simp add: art_dir_def art_len_def)

lemma open_tree_component_acap_at:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and inb: "ds_nxt s < length vs_list" and al: "art_len s"
  shows "ds_acap (open_tree_component acyc_flow s c) ! (ds_nxt s) = (art_tree_cap c)"
  using open_tree_component_art(4)[OF inv c] inb al
  by (simp add: art_tree_cap_def art_flow_def art_dir_def art_len_def)

lemma open_tree_component_aflw_at:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and inb: "ds_nxt s < length vs_list" and al: "art_len s"
  shows "ds_aflw (open_tree_component acyc_flow s c) ! (ds_nxt s) = (art_flow c)"
  using open_tree_component_art(5)[OF inv c] inb al by (simp add: art_flow_def art_len_def)

lemma open_tree_component_aest_at:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and inb: "ds_nxt s < length vs_list" and al: "art_len s"
  shows "ds_aest (open_tree_component acyc_flow s c) ! (ds_nxt s) = (InTree)"
  using open_tree_component_art(6)[OF inv c] inb al by (simp add: art_len_def)

lemma emit_U_edge_afst_at:
  assumes inb: "ds_nxt s < length vs_list" and al: "art_len s"
  shows "ds_afst (emit_U_edge s v) ! (ds_nxt s) = (if art_dir v then v else vcount)"
  using inb al by (simp add: emit_U_edge_def Let_def art_dir_def art_len_def nth_list_update)

lemma emit_U_edge_asnd_at:
  assumes inb: "ds_nxt s < length vs_list" and al: "art_len s"
  shows "ds_asnd (emit_U_edge s v) ! (ds_nxt s) = (if art_dir v then vcount else v)"
  using inb al by (simp add: emit_U_edge_def Let_def art_dir_def art_len_def nth_list_update)

lemma emit_U_edge_acap_at:
  assumes inb: "ds_nxt s < length vs_list" and al: "art_len s"
  shows "ds_acap (emit_U_edge s v) ! (ds_nxt s) = (art_flow v)"
  using inb al by (simp add: emit_U_edge_def Let_def art_flow_def art_len_def nth_list_update)

lemma emit_U_edge_aflw_at:
  assumes inb: "ds_nxt s < length vs_list" and al: "art_len s"
  shows "ds_aflw (emit_U_edge s v) ! (ds_nxt s) = (art_flow v)"
  using inb al by (simp add: emit_U_edge_def Let_def art_flow_def art_len_def nth_list_update)

lemma emit_U_edge_aest_at:
  assumes inb: "ds_nxt s < length vs_list" and al: "art_len s"
  shows "ds_aest (emit_U_edge s v) ! (ds_nxt s) = (InU)"
  using inb al by (simp add: emit_U_edge_def Let_def  art_len_def nth_list_update)

subsection \<open>Assembly substrate: the full artificial-edge tail content\<close>

text \<open>Lifting the per-emission content facts to the whole build: every artificial edge index
      @{term \<open>k < ds_nxt (build_tree acyc_flow)\<close>} stores a well-formed edge --- one endpoint the artificial root
      @{const vcount}, the other a genuine vertex @{term \<open>subj < vcount\<close>}, oriented by @{const art_dir},
      carrying @{const art_flow} and (on tree edges) @{const art_tree_cap}. The bound
      @{thm build_tree_nxt_le} supplies the in-bounds premise at each emission via the same carried
      ghost set that proved it, so nothing is dropped and every stored edge is characterised.\<close>

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

lemma emit_U_edge_tail_edge_ok_old:
  assumes k: "k < ds_nxt s" and ok: "tail_edge_ok s k"
  shows "tail_edge_ok (emit_U_edge s v) k"
  using ok k by (simp add: tail_edge_ok_def emit_U_edge_def Let_def nth_list_update_neq)

lemma open_tree_component_afst_old:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and k: "k < ds_nxt s"
  shows "ds_afst (open_tree_component acyc_flow s c) ! k = ds_afst s ! k"
  using open_tree_component_art(2)[OF inv c] k by simp

lemma open_tree_component_asnd_old:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and k: "k < ds_nxt s"
  shows "ds_asnd (open_tree_component acyc_flow s c) ! k = ds_asnd s ! k"
  using open_tree_component_art(3)[OF inv c] k by simp

lemma open_tree_component_acap_old:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and k: "k < ds_nxt s"
  shows "ds_acap (open_tree_component acyc_flow s c) ! k = ds_acap s ! k"
  using open_tree_component_art(4)[OF inv c] k by simp

lemma open_tree_component_aflw_old:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and k: "k < ds_nxt s"
  shows "ds_aflw (open_tree_component acyc_flow s c) ! k = ds_aflw s ! k"
  using open_tree_component_art(5)[OF inv c] k by simp

lemma open_tree_component_aest_old:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and k: "k < ds_nxt s"
  shows "ds_aest (open_tree_component acyc_flow s c) ! k = ds_aest s ! k"
  using open_tree_component_art(6)[OF inv c] k by simp

lemma open_tree_component_tail_edge_ok_old:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and k: "k < ds_nxt s" and ok: "tail_edge_ok s k"
  shows "tail_edge_ok (open_tree_component acyc_flow s c) k"
  using ok
  unfolding tail_edge_ok_def
  by (simp add: open_tree_component_afst_old[OF inv c k] open_tree_component_asnd_old[OF inv c k]
                open_tree_component_acap_old[OF inv c k] open_tree_component_aflw_old[OF inv c k]
                open_tree_component_aest_old[OF inv c k])

lemma emit_U_edge_tail_edge_ok_new:
  assumes v: "v < vcount" and inb: "ds_nxt s < length vs_list" and al: "art_len s"
  shows "tail_edge_ok (emit_U_edge s v) (ds_nxt s)"
  unfolding tail_edge_ok_def
  apply (rule exI[where x=v])
  using v by (simp add: emit_U_edge_afst_at[OF inb al] emit_U_edge_asnd_at[OF inb al]
                emit_U_edge_acap_at[OF inb al] emit_U_edge_aflw_at[OF inb al] emit_U_edge_aest_at[OF inb al])

lemma open_tree_component_tail_edge_ok_new:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and inb: "ds_nxt s < length vs_list" and al: "art_len s"
  shows "tail_edge_ok (open_tree_component acyc_flow s c) (ds_nxt s)"
  unfolding tail_edge_ok_def
  apply (rule exI[where x=c])
  using c by (simp add: open_tree_component_afst_at[OF inv c inb al] open_tree_component_asnd_at[OF inv c inb al]
                open_tree_component_acap_at[OF inv c inb al] open_tree_component_aflw_at[OF inv c inb al]
                open_tree_component_aest_at[OF inv c inb al])

lemma phase1_step_tail_content:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and al: "art_len s"
      and tc: "tail_content s" and inb: "ds_nxt (phase1_step acyc_flow v s) \<le> length vs_list"
  shows "tail_content (phase1_step acyc_flow v s)"
proof (cases "imbalance ! v = 0")
  case True thus ?thesis using tc by (simp add: phase1_step_def)
next
  case nz: False
  have vlt: "v < vcount" using v vs_less_vcount by simp
  show ?thesis
  proof (cases "ds_seen s ! v")
    case seen: True
    have eq: "phase1_step acyc_flow v s = emit_U_edge s v" using nz seen by (simp add: phase1_step_def)
    have nxt: "ds_nxt (emit_U_edge s v) = Suc (ds_nxt s)" by (rule emit_U_edge_nxt)
    have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
    show ?thesis
      unfolding eq tail_content_def
    proof (intro allI impI)
      fix k assume "k < ds_nxt (emit_U_edge s v)"
      hence kl: "k < Suc (ds_nxt s)" using nxt by simp
      show "tail_edge_ok (emit_U_edge s v) k"
      proof (cases "k < ds_nxt s")
        case True
        have tok: "tail_edge_ok s k" using tc True by (simp add: tail_content_def)
        show ?thesis using emit_U_edge_tail_edge_ok_old[OF True tok] .
      next
        case False
        hence "k = ds_nxt s" using kl by simp
        thus ?thesis using emit_U_edge_tail_edge_ok_new[OF vlt inbs al] by simp
      qed
    qed
  next
    case notseen: False
    have eq: "phase1_step acyc_flow v s = open_tree_component acyc_flow s v" using nz notseen by (simp add: phase1_step_def)
    have nxt: "ds_nxt (open_tree_component acyc_flow s v) = Suc (ds_nxt s)" using open_tree_component_art(1)[OF inv vlt] .
    have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
    show ?thesis
      unfolding eq tail_content_def
    proof (intro allI impI)
      fix k assume "k < ds_nxt (open_tree_component acyc_flow s v)"
      hence kl: "k < Suc (ds_nxt s)" using nxt by simp
      show "tail_edge_ok (open_tree_component acyc_flow s v) k"
      proof (cases "k < ds_nxt s")
        case True
        have tok: "tail_edge_ok s k" using tc True by (simp add: tail_content_def)
        show ?thesis using open_tree_component_tail_edge_ok_old[OF inv vlt True tok] .
      next
        case False
        hence "k = ds_nxt s" using kl by simp
        thus ?thesis using open_tree_component_tail_edge_ok_new[OF inv vlt inbs al] by simp
      qed
    qed
  qed
qed

lemma phase2_step_tail_content:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and al: "art_len s"
      and tc: "tail_content s" and inb: "ds_nxt (phase2_step acyc_flow v s) \<le> length vs_list"
  shows "tail_content (phase2_step acyc_flow v s)"
proof (cases "ds_seen s ! v \<or> is_lonely v")
  case True thus ?thesis using tc by (simp add: phase2_step_def)
next
  case False
  hence notseen: "\<not> ds_seen s ! v" and nl: "\<not> is_lonely v" by auto
  have vlt: "v < vcount" using v vs_less_vcount by simp
  have eq: "phase2_step acyc_flow v s = open_tree_component acyc_flow s v" using notseen nl by (simp add: phase2_step_def)
  have nxt: "ds_nxt (open_tree_component acyc_flow s v) = Suc (ds_nxt s)" using open_tree_component_art(1)[OF inv vlt] .
  have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
  show ?thesis
    unfolding eq tail_content_def
  proof (intro allI impI)
    fix k assume "k < ds_nxt (open_tree_component acyc_flow s v)"
    hence kl: "k < Suc (ds_nxt s)" using nxt by simp
    show "tail_edge_ok (open_tree_component acyc_flow s v) k"
    proof (cases "k < ds_nxt s")
      case True
      have tok: "tail_edge_ok s k" using tc True by (simp add: tail_content_def)
      show ?thesis using open_tree_component_tail_edge_ok_old[OF inv vlt True tok] .
    next
      case False
      hence "k = ds_nxt s" using kl by simp
      thus ?thesis using open_tree_component_tail_edge_ok_new[OF inv vlt inbs al] by simp
    qed
  qed
qed

lemma card_sub_vs_le:
  assumes "A \<subseteq> set vs_list" shows "card A \<le> length vs_list"
proof -
  have "card A \<le> card (set vs_list)" using assms by (simp add: card_mono)
  thus ?thesis by (simp add: distinct_card distinct_vs_list)
qed

lemma fold_emit_content1:
  assumes "distinct xs" "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "tail_content s"
      "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "E \<inter> set xs = {}" "ds_nxt s = card E"
  shows "art_len (fold (phase1_step acyc_flow) xs s) \<and> tail_content (fold (phase1_step acyc_flow) xs s)
         \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase1_step acyc_flow) xs s) ! v}
                 \<and> ds_nxt (fold (phase1_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(2) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv1: "dfs_inv acyc_flow (phase1_step acyc_flow x s)" "ds_stk (phase1_step acyc_flow x s) = []"
    using phase1_step_inv[OF xvs conjI[OF Cons.prems(3) Cons.prems(4)]] by auto
  have al1: "art_len (phase1_step acyc_flow x s)" using phase1_step_art_len[OF xvs Cons.prems(3) Cons.prems(5)] .
  have Emono: "E \<subseteq> {v \<in> set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}"
    using Cons.prems(8) phase1_step_seen_mono[OF Cons.prems(3) xlt] by auto
  have Edisj: "E \<inter> set rest = {}" using Cons.prems(9) by auto
  have distr: "distinct rest" using Cons.prems(1) by simp
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(2) by simp
  have Esub: "E \<subseteq> set vs_list" using Cons.prems(8) by auto
  have xnotE: "x \<notin> E" using Cons.prems(9) by auto
  have step_inb: "ds_nxt (phase1_step acyc_flow x s) \<le> length vs_list"
    using phase1_step_nxt[OF Cons.prems(3) xlt]
  proof
    assume "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(10) card_sub_vs_le[OF Esub] by simp
  next
    assume A: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) \<and> ds_seen (phase1_step acyc_flow x s) ! x"
    have "insert x E \<subseteq> set vs_list" using Esub xvs by auto
    hence "card (insert x E) \<le> length vs_list" by (rule card_sub_vs_le)
    thus ?thesis using A Cons.prems(10) xnotE Cons.prems(7) by (simp add: card_insert_disjoint)
  qed
  have tc1: "tail_content (phase1_step acyc_flow x s)"
    using phase1_step_tail_content[OF xvs Cons.prems(3) Cons.prems(5) Cons.prems(6) step_inb] .
  from phase1_step_nxt[OF Cons.prems(3) xlt] show ?case
  proof
    assume A: "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase1_step acyc_flow x s) = card E" using A Cons.prems(10) by simp
    show ?thesis
      using Cons.hyps[OF distr subr inv1(1) inv1(2) al1 tc1 Cons.prems(7) Emono Edisj card1] by simp
  next
    assume B: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) \<and> ds_seen (phase1_step acyc_flow x s) ! x"
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(7) by (simp add: E2_def)
    have E2seen: "E2 \<subseteq> {v \<in> set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have E2disj: "E2 \<inter> set rest = {}" using Edisj Cons.prems(1) by (auto simp: E2_def)
    have card2: "ds_nxt (phase1_step acyc_flow x s) = card E2" using B Cons.prems(10) xnotE Cons.prems(7) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF distr subr inv1(1) inv1(2) al1 tc1 fin2 E2seen E2disj card2] by simp
  qed
qed

lemma fold_emit_content2:
  assumes "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "tail_content s"
      "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "ds_nxt s = card E"
  shows "art_len (fold (phase2_step acyc_flow) xs s) \<and> tail_content (fold (phase2_step acyc_flow) xs s)
         \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase2_step acyc_flow) xs s) ! v}
                 \<and> ds_nxt (fold (phase2_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(1) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv1: "dfs_inv acyc_flow (phase2_step acyc_flow x s)" "ds_stk (phase2_step acyc_flow x s) = []"
    using phase2_step_inv[OF xvs conjI[OF Cons.prems(2) Cons.prems(3)]] by auto
  have al1: "art_len (phase2_step acyc_flow x s)" using phase2_step_art_len[OF xvs Cons.prems(2) Cons.prems(4)] .
  have Emono: "E \<subseteq> {v \<in> set vs_list. ds_seen (phase2_step acyc_flow x s) ! v}"
    using Cons.prems(7) phase2_step_seen_mono[OF Cons.prems(2) xlt] by auto
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(1) by simp
  have Esub: "E \<subseteq> set vs_list" using Cons.prems(7) by auto
  have step_inb: "ds_nxt (phase2_step acyc_flow x s) \<le> length vs_list"
    using phase2_step_nxt2[OF Cons.prems(2) xlt]
  proof
    assume "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(8) card_sub_vs_le[OF Esub] by simp
  next
    assume A: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! x \<and> ds_seen (phase2_step acyc_flow x s) ! x"
    have xnotE: "x \<notin> E" using A Cons.prems(7) by auto
    have "insert x E \<subseteq> set vs_list" using Esub xvs by auto
    hence "card (insert x E) \<le> length vs_list" by (rule card_sub_vs_le)
    thus ?thesis using A Cons.prems(8) xnotE Cons.prems(6) by (simp add: card_insert_disjoint)
  qed
  have tc1: "tail_content (phase2_step acyc_flow x s)"
    using phase2_step_tail_content[OF xvs Cons.prems(2) Cons.prems(4) Cons.prems(5) step_inb] .
  from phase2_step_nxt2[OF Cons.prems(2) xlt] show ?case
  proof
    assume A: "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase2_step acyc_flow x s) = card E" using A Cons.prems(8) by simp
    show ?thesis
      using Cons.hyps[OF subr inv1(1) inv1(2) al1 tc1 Cons.prems(6) Emono card1] by simp
  next
    assume B: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! x \<and> ds_seen (phase2_step acyc_flow x s) ! x"
    have xnotE: "x \<notin> E" using B Cons.prems(7) by auto
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(6) by (simp add: E2_def)
    have E2seen: "E2 \<subseteq> {v \<in> set vs_list. ds_seen (phase2_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have card2: "ds_nxt (phase2_step acyc_flow x s) = card E2" using B Cons.prems(8) xnotE Cons.prems(6) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF subr inv1(1) inv1(2) al1 tc1 fin2 E2seen card2] by simp
  qed
qed

lemma build_tree_tail_content: "tail_content (build_tree acyc_flow)"
proof -
  have i0: "dfs_inv acyc_flow dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have al0: "art_len dfs_init" by (rule dfs_init_art_len)
  have tc0: "tail_content dfs_init" by (simp add: tail_content_def dfs_init_def)
  have C1: "art_len (fold (phase1_step acyc_flow) vs_list dfs_init) \<and> tail_content (fold (phase1_step acyc_flow) vs_list dfs_init)
        \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase1_step acyc_flow) vs_list dfs_init) ! v}
                \<and> ds_nxt (fold (phase1_step acyc_flow) vs_list dfs_init) = card E')"
    apply (rule fold_emit_content1[where E="{}"])
    subgoal by (rule distinct_vs_list)
    subgoal by simp
    subgoal using i0 by simp
    subgoal using i0 by simp
    subgoal by (rule al0)
    subgoal by (rule tc0)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: dfs_init_def)
    done
  have P1: "art_len (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have TC1: "tail_content (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have E1ex: "\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}
                \<and> ds_nxt (phase1 acyc_flow dfs_init) = card E'" using C1 by (simp add: phase1_def)
  have p1inv: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init) \<and> ds_stk (phase1 acyc_flow dfs_init) = []" using phase1_inv[OF i0] .
  obtain E1 where E1f: "finite E1" and E1s: "E1 \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}"
    and E1n: "ds_nxt (phase1 acyc_flow dfs_init) = card E1" using E1ex by blast
  have C2: "art_len (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        \<and> tail_content (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init)) ! v}
                \<and> ds_nxt (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init)) = card E')"
    apply (rule fold_emit_content2[where E=E1 and s="phase1 acyc_flow dfs_init"])
    subgoal by simp
    subgoal using p1inv by simp
    subgoal using p1inv by simp
    subgoal by (rule P1)
    subgoal by (rule TC1)
    subgoal by (rule E1f)
    subgoal by (rule E1s)
    subgoal by (rule E1n)
    done
  have "tail_content (phase2 acyc_flow (phase1 acyc_flow dfs_init))" using C2 by (simp add: phase2_def)
  thus ?thesis by (simp add: build_tree_def Let_def tail_content_def tail_edge_ok_def)
qed

subsection \<open>The acyclified flow the tree is built from\<close>

text \<open>The builder runs on @{const acyc_flow} --- the acyclifier's output --- never on the raw input
      @{term flow_list}.  Its length is @{term m} on \<^emph>\<open>both\<close> branches: on @{term None} it is the
      input list itself, and on @{term Some} the acyclifier's own flow-array invariant (which pins the
      length) is carried through the loop by @{thm make_acyclic_flow_invar}.  So the augmented-array
      glue below needs no case split on the acyclifier's verdict.\<close>

lemma af_cap_feasible_flow_list: "af_cap_feasible flow_list"
  unfolding af_cap_feasible_def
proof (intro ballI conjI)
  fix a assume a: "a \<in> {0..<m}"
  hence am: "a < m" by simp
  show "0 \<le> flow_list ! a" using flow_nonneg[OF am] by simp
  show "capacity_list ! a = - 1 \<or> flow_list ! a \<le> capacity_list ! a"
    using flow_le_cap[OF am] by auto
qed

lemma distinct_edged_vs_list: "distinct edged_vs_list"
  unfolding edged_vs_list_def by (rule distinct_filter[OF distinct_vs_list])

lemma length_acyc_flow[simp]: "length acyc_flow = m"
proof (cases acyc_flow_opt)
  case None
  thus ?thesis using length_flow length_edges by (simp add: acyc_flow_def)
next
  case (Some f')
  have vv: "lc_invar \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr>"
    by (simp add: lc_invar_def distinct_edged_vs_list)
  have vab: "lc_abstract \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr> \<subseteq> original_network.\<V>"
    by (simp add: lc_abstract_def V_orig_eq_edged)
  have vit0: "lc_iterated \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr> = {}"
    by (simp add: lc_iterated_def)
  have ff: "length flow_list = m" using length_flow length_edges by simp
  have res: "make_acyclic flow_list = Some f'" using Some by (simp add: acyc_flow_opt_def)
  have "length f' = m"
    using make_acyclic_flow_invar[OF multigraph_inv_csr ff af_cap_feasible_flow_list vv vab vit0 res] .
  thus ?thesis using Some by (simp add: acyc_flow_def)
qed


text \<open>The acyclified flow is capacity-complying on \<^emph>\<open>both\<close> branches, just as its length is fixed on
      both: on @{term None} it is the input list, which is capacity-complying by hypothesis; on
      @{term Some} the acyclifier returns a capacity-complying flow (@{thm make_acyclic_feasible}).
      Cancelling cycles never pushes an arc outside its bounds, so no case split on the acyclifier's
      verdict is needed here --- acyclicity is the only property that is genuinely \<^emph>\<open>Some\<close>-only.\<close>

lemma af_cap_feasible_acyc_flow: "af_cap_feasible acyc_flow"
proof (cases acyc_flow_opt)
  case None
  thus ?thesis using af_cap_feasible_flow_list by (simp add: acyc_flow_def)
next
  case (Some f')
  have vv: "lc_invar \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr>"
    by (simp add: lc_invar_def distinct_edged_vs_list)
  have vab: "lc_abstract \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr> \<subseteq> original_network.\<V>"
    by (simp add: lc_abstract_def V_orig_eq_edged)
  have ff: "length flow_list = m" using length_flow length_edges by simp
  have res: "make_acyclic flow_list = Some f'" using Some by (simp add: acyc_flow_opt_def)
  have "af_cap_feasible f'"
    using make_acyclic_feasible[OF multigraph_inv_csr ff af_cap_feasible_flow_list vv vab res] .
  thus ?thesis using Some by (simp add: acyc_flow_def)
qed

lemma acyc_flow_nonneg: "e < m \<Longrightarrow> 0 \<le> acyc_flow ! e"
  using af_cap_feasible_acyc_flow by (simp add: af_cap_feasible_def)

lemma acyc_flow_le_cap: "e < m \<Longrightarrow> capacity_list ! e \<noteq> - 1 \<Longrightarrow> acyc_flow ! e \<le> capacity_list ! e"
  using af_cap_feasible_acyc_flow by (force simp: af_cap_feasible_def)subsection \<open>Thin glue: the unified augmented edge arrays (real part @ artificial tail)\<close>

text \<open>The design ({\isasymsection}5, Network\_Simplex\_Initial\_Basis.thy) calls for the augmented network's endpoints,
      capacity, flow, cost and edge-state to be single length-@{term \<open>m + Kart\<close>} arrays --- the input
      lists followed by the @{const build_tree} artificial tail truncated to its live prefix
      @{term \<open>Kart = ds_nxt (build_tree acyc_flow)\<close>}. Real indices @{term \<open>e < m\<close>} read the input lists; artificial
      indices @{term \<open>m + e\<close>} (@{term \<open>e < Kart\<close>}) read the built tail, characterised by
      \<open>tail_edge_ok_build_tree\<close>: one endpoint the artificial root @{const vcount}, the other a
      genuine vertex, oriented by @{const art_dir}, carrying @{const art_flow} / @{const art_tree_cap}.\<close>

lemma Kart_le: "Kart \<le> length vs_list" using build_tree_nxt_le by (simp add: Kart_def)

lemma len_afst_bt: "length (ds_afst (build_tree acyc_flow)) = length vs_list" using build_tree_art_len by (simp add: art_len_def)

lemma len_asnd_bt: "length (ds_asnd (build_tree acyc_flow)) = length vs_list" using build_tree_art_len by (simp add: art_len_def)

lemma len_acap_bt: "length (ds_acap (build_tree acyc_flow)) = length vs_list" using build_tree_art_len by (simp add: art_len_def)

lemma len_aflw_bt: "length (ds_aflw (build_tree acyc_flow)) = length vs_list" using build_tree_art_len by (simp add: art_len_def)

lemma len_aest_bt: "length (ds_aest (build_tree acyc_flow)) = length vs_list" using build_tree_art_len by (simp add: art_len_def)

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

lemma cap_all_real: "e < m \<Longrightarrow> cap_all ! e = capacity_list ! e" by (simp add: cap_all_def nth_append length_edges)

lemma flow_all_real: "e < m \<Longrightarrow> flow_all ! e = acyc_flow ! e" by (simp add: flow_all_def nth_append)

lemma state_all_real: "e < m \<Longrightarrow> state_all ! e = (edge_state acyc_flow) ! e" by (simp add: state_all_def nth_append)

lemma cost_all_real: "e < m \<Longrightarrow> cost_all ! e = h (cost_list ! e)" by (simp add: cost_all_def nth_append)

lemma fst_all_art: "e < Kart \<Longrightarrow> fst_all ! (m + e) = ds_afst (build_tree acyc_flow) ! e"
  using Kart_le len_afst_bt by (simp add: fst_all_def nth_append nth_take)

lemma snd_all_art: "e < Kart \<Longrightarrow> snd_all ! (m + e) = ds_asnd (build_tree acyc_flow) ! e"
  using Kart_le len_asnd_bt by (simp add: snd_all_def nth_append nth_take)

lemma cap_all_art: "e < Kart \<Longrightarrow> cap_all ! (m + e) = ds_acap (build_tree acyc_flow) ! e"
  using Kart_le len_acap_bt length_edges by (simp add: cap_all_def nth_append nth_take)

lemma flow_all_art: "e < Kart \<Longrightarrow> flow_all ! (m + e) = ds_aflw (build_tree acyc_flow) ! e"
  using Kart_le len_aflw_bt by (simp add: flow_all_def nth_append nth_take)

lemma state_all_art: "e < Kart \<Longrightarrow> state_all ! (m + e) = ds_aest (build_tree acyc_flow) ! e"
  using Kart_le len_aest_bt by (simp add: state_all_def nth_append nth_take)

lemma cost_all_art: "e < Kart \<Longrightarrow> cost_all ! (m + e) = bigM"
  by (simp add: cost_all_def nth_append)

lemma tail_edge_ok_build_tree: "e < Kart \<Longrightarrow> tail_edge_ok (build_tree acyc_flow) e"
  using build_tree_tail_content by (simp add: tail_content_def Kart_def)

text \<open>\<^bold>\<open>Status of the @{const arb_invar} obligations --- all discharged (@{thm arb_invar_Sarb}).\<close>
      Obligation 1 = \<open>rooted_arb_invar_Sprnt\<close> (\<open>parent_spec_Sprnt\<close>, \<open>r_in_V\<close>, \<open>dom_Sprnt\<close>, edge-set spanning
      \<open>dVs_Sprnt\<close>); 2 = \<open>parent_spec_Sthrd\<close>; 3 = \<open>parent_spec_Srvth\<close>; 4 = \<open>follow_Sthrd_spans\<close>; domains 5/6 =
      \<open>dom_Sthrd\<close> (with \<open>lsuc_root_eq_prev\<close>) / \<open>dom_Srvth\<close>; thread/rev-thread inverse 7 = \<open>thrd_rvth_inverse\<close>;
      last-successor membership 8 = \<open>lsuc_in_V_all\<close>; subtree size 9 = \<open>snum_eq_children_all\<close> (interior
      \<open>snum_eq_children\<close>; root \<open>build_tree_root_snum\<close> via the carried \<open>rootacc\<close> invariant, with
      \<open>children_Sprnt_root\<close>); clause J 10 = \<open>clause_J\<close>. The deferred bridge \<open>Vseen = set vs_list\<close> still
      belongs to the network-simplex vertex layer, where \<open>arb_invar_Sarb\<close> feeds the \<open>arborescense_adt\<close>
      instantiation of \<open>network_simplex_init\<close>.\<close>



section \<open>Instantiating the spanning-tree ADT with the threaded arborescence\<close>

text \<open>We discharge every axiom of the abstract spanning-tree ADT @{locale arborescense_adt}
      (\<^theory>\<open>Mincost_Flow_Algorithms.Network_Simplex\<close>) for the concrete threaded @{typ \<open>'a ndtree\<close>}
      satisfying @{const arb_invar}.  The abstract (undirected) arborescence \<open>abstract_arb\<close> is the
      set of undirected parent edges; the executable operations are the snum-driven
      \<open>get_path_pair_impl\<close>, the thread-recursive \<open>iterate_root_opposed_impl\<close>, and the
      branch-reversing \<open>swap_edge_impl\<close> (a wrapper around @{const update_tree}).  The pivotal
      bridge is \<open>unique_walk_to_root\<close>: every distinct walk to the root \<^emph>\<open>is\<close> the @{const follow}
      path, from which the fundamental-cycle, uniqueness, iteration and edge-swap axioms all follow.
      The development is generic over \<open>arb_invar r V S\<close>; the final interpretation specialises it
      at the initial basis \<open>Sarb\<close> on \<open>Varb\<close> with root \<open>vcount\<close>.\<close>

definition abstract_arb :: "'a ndtree \<Rightarrow> 'a set set" where
  "abstract_arb S = {{x, y} |x y. prnt S x = Some y}"

lemma abstract_arb_edge: "prnt S x = Some y \<Longrightarrow> {x, y} \<in> abstract_arb S"
  by (auto simp: abstract_arb_def)

lemma abstract_arb_alt: "abstract_arb S = {{x, y} |x y. Some x = prnt S y}"
  unfolding abstract_arb_def by (auto simp: eq_commute insert_commute)

lemma parent_spec_neq:
  assumes "parent_spec T" and "T x = Some y" shows "x \<noteq> y"
proof
  assume "x = y"
  hence "(x, x) \<in> {(a, b) |a b. Some a = T b}" using assms(2) by auto
  moreover have "wf {(a, b) |a b. Some a = T b}" using assms(1) by (simp add: parent_spec_def)
  ultimately show False by (meson wf_not_refl)
qed

lemma dblton_abstract_arb:
  assumes inv: "arb_invar r V S" shows "dblton_graph (abstract_arb S)"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  show ?thesis unfolding dblton_graph_def abstract_arb_def
    using parent_spec_neq[OF ps] by fastforce
qed

lemma Vs_abstract_arb:
  assumes inv: "arb_invar r V S" shows "Vs (abstract_arb S) = V"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have dVs: "dVs {(y, x) |x y. Some x = prnt S y} = V"
    using rinv unfolding rooted_arborescense_invar_def by simp
  have eq: "abstract_arb S = {{v1, v2} |v1 v2. (v1, v2) \<in> {(y, x) |x y. Some x = prnt S y}}"
    unfolding abstract_arb_def by (auto simp: eq_commute)
  have "Vs (abstract_arb S) = dVs {(y, x) |x y. Some x = prnt S y}"
    unfolding Vs_def dVs_def eq by simp
  thus ?thesis using dVs by simp
qed

lemma finite_V_arb:
  assumes inv: "arb_invar r V S" shows "finite V"
proof -
  have "set (follow (thrd S) r) = V" using inv unfolding arb_invar_def by simp
  thus ?thesis by (metis List.finite_set)
qed

lemma graph_invar_abstract_arb:
  assumes inv: "arb_invar r V S" shows "graph_invar (abstract_arb S)"
  using dblton_abstract_arb[OF inv] Vs_abstract_arb[OF inv] finite_V_arb[OF inv] by simp

lemma follow_walk_root:
  assumes inv: "arb_invar r V S" and vV: "v \<in> V"
  shows "walk_betw (abstract_arb S) v (follow (prnt S) v) r"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  interpret P: parent "prnt S" "\<lambda>_ _. True" using ps by unfold_locales
  have es: "{{x, y} |x y. parent_spec_i.follow_rel (prnt S) x y} = abstract_arb S"
    unfolding abstract_arb_alt by (simp add: P.parent_eq_follow_rel)
  have fl: "last (follow (prnt S) v) = r" by (rule follow_last_root[OF inv vV])
  have disj: "walk_betw (abstract_arb S) v (follow (prnt S) v) (last (follow (prnt S) v))
              \<or> follow (prnt S) v = [v]"
    using P.follow_walk_betw[of v] es by (simp add: follow_def)
  show ?thesis
  proof (cases "follow (prnt S) v = [v]")
    case True
    hence "v = r" using fl by simp
    hence "r \<in> Vs (abstract_arb S)" using Vs_abstract_arb[OF inv] vV by simp
    thus ?thesis using True \<open>v = r\<close> by (simp add: walk_reflexive)
  next
    case False
    hence "walk_betw (abstract_arb S) v (follow (prnt S) v) (last (follow (prnt S) v))"
      using disj by simp
    thus ?thesis using fl by simp
  qed
qed

lemma follow_root_singleton:
  assumes inv: "arb_invar r V S" shows "follow (prnt S) r = [r]"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have "r \<notin> dom (prnt S)" using rinv unfolding rooted_arborescense_invar_def by simp
  hence "prnt S r = None" by (simp add: domIff)
  thus ?thesis by (simp add: follow_ps_simps[OF ps])
qed

lemma parent_in_V:
  assumes inv: "arb_invar r V S" and yV: "y \<in> V" and pe: "prnt S y = Some w"
  shows "w \<in> V"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have "follow (prnt S) y = y # follow (prnt S) w" by (simp add: follow_ps_simps[OF ps] pe)
  hence "w \<in> set (follow (prnt S) y)"
    using follow_ne_ps[OF ps, of w] follow_hd_ps[OF ps, of w] by (metis hd_in_set list.set_intros(2))
  thus ?thesis using follow_subset_V[OF rinv yV] by auto
qed

lemma abstract_arb_edgeD:
  assumes ps: "parent_spec (prnt S)" and e: "{y, z} \<in> abstract_arb S"
  shows "prnt S y = Some z \<or> prnt S z = Some y"
  using e parent_spec_neq[OF ps] by (auto simp: abstract_arb_def doubleton_eq_iff)

lemma subtree_cut:
  assumes ps: "parent_spec (prnt S)"
  shows "path (abstract_arb S) q \<Longrightarrow> y \<notin> set q \<Longrightarrow> hd q \<in> children (prnt S) y
          \<Longrightarrow> set q \<subseteq> children (prnt S) y"
proof (induct q)
  case Nil thus ?case by simp
next
  case (Cons a q')
  have aC: "a \<in> children (prnt S) y" using Cons.prems(3) by simp
  show ?case
  proof (cases q')
    case Nil thus ?thesis using aC by simp
  next
    case (Cons b rest)
    have qeq: "q' = b # rest" by (rule Cons)
    have edge: "{a, b} \<in> abstract_arb S" using Cons.prems(1) qeq by (simp add: path_2)
    have pq': "path (abstract_arb S) q'" using Cons.prems(1) qeq by (simp add: path_2)
    have ayf: "y \<in> set (follow (prnt S) a)" using aC by (simp add: children_def)
    have ynota: "y \<noteq> a" using Cons.prems(2) by auto
    have bC: "b \<in> children (prnt S) y"
    proof -
      from abstract_arb_edgeD[OF ps edge] show ?thesis
      proof
        assume "prnt S a = Some b"
        hence "follow (prnt S) a = a # follow (prnt S) b" by (simp add: follow_ps_simps[OF ps])
        hence "y \<in> set (follow (prnt S) b)" using ayf ynota by simp
        thus ?thesis by (simp add: children_def)
      next
        assume "prnt S b = Some a"
        hence "follow (prnt S) b = b # follow (prnt S) a" by (simp add: follow_ps_simps[OF ps])
        hence "y \<in> set (follow (prnt S) b)" using ayf by simp
        thus ?thesis by (simp add: children_def)
      qed
    qed
    have ynot': "y \<notin> set q'" using Cons.prems(2) by simp
    have hdq': "hd q' \<in> children (prnt S) y" using bC qeq by simp
    have "set q' \<subseteq> children (prnt S) y" using Cons.hyps[OF pq' ynot' hdq'] .
    thus ?thesis using aC by simp
  qed
qed

lemma unique_walk_to_root:
  assumes inv: "arb_invar r V S"
  shows "\<And>y p. y \<in> V \<Longrightarrow> walk_betw (abstract_arb S) y p r \<Longrightarrow> distinct p
              \<Longrightarrow> p = follow (prnt S) y"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have froot: "follow (prnt S) r = [r]" by (rule follow_root_singleton[OF inv])
  { fix n y p
    have "length (follow (prnt S) y) = n \<Longrightarrow> y \<in> V \<Longrightarrow>
          walk_betw (abstract_arb S) y p r \<Longrightarrow> distinct p \<Longrightarrow> p = follow (prnt S) y"
    proof (induct n arbitrary: y p rule: less_induct)
      case (less n y p)
      note eqn = less.prems(1) and yV = less.prems(2) and wb = less.prems(3) and dp = less.prems(4)
      have pne: "p \<noteq> []" and pth: "path (abstract_arb S) p"
        and hdp: "hd p = y" and lstp: "last p = r"
        using wb by (auto simp: walk_betw_def)
      show ?case
      proof (cases "y = r")
        case True
        have "p = [r]"
        proof (cases p)
          case Nil thus ?thesis using pne by simp
        next
          case (Cons a rest)
          have ar: "a = r" using hdp Cons True by simp
          have "rest = []"
          proof (rule ccontr)
            assume rne: "rest \<noteq> []"
            have "last rest \<in> set rest" using rne last_in_set by simp
            moreover have "last rest = r" using Cons rne lstp by simp
            moreover have "a \<notin> set rest" using dp Cons by simp
            ultimately show False using ar by simp
          qed
          thus ?thesis using Cons ar by simp
        qed
        thus ?thesis using True froot by simp
      next
        case False
        have ydom: "y \<in> dom (prnt S)"
        proof -
          have "dom (prnt S) = V - {r}" using rinv unfolding rooted_arborescense_invar_def by simp
          thus ?thesis using yV False by simp
        qed
        then obtain w where pw: "prnt S y = Some w" by (auto simp: dom_def)
        have fy: "follow (prnt S) y = y # follow (prnt S) w"
          by (simp add: follow_ps_simps[OF ps] pw)
        have wV: "w \<in> V" by (rule parent_in_V[OF inv yV pw])
        have lenw: "length (follow (prnt S) w) < n" using fy eqn by simp
        obtain p' where pP: "p = y # p'" using hdp pne by (cases p) auto
        have p'ne: "p' \<noteq> []"
        proof
          assume "p' = []"
          hence "p = [y]" using pP by simp
          hence "r = y" using lstp by simp
          thus False using False by simp
        qed
        obtain b p'' where p'P: "p' = b # p''" using p'ne by (cases p') auto
        have edge: "{y, b} \<in> abstract_arb S" using pth pP p'P by (simp add: path_2)
        have pthp': "path (abstract_arb S) p'" using tl_path_is_path[OF pth] pP by simp
        have dp': "distinct p'" using dp pP by simp
        have lstp': "last p' = r" using lstp pP p'ne by simp
        from abstract_arb_edgeD[OF ps edge] show ?thesis
        proof
          assume "prnt S y = Some b"
          hence bw: "b = w" using pw by simp
          have hdp': "hd p' = w" using p'P bw by simp
          have wbp': "walk_betw (abstract_arb S) w p' r"
            using pthp' p'ne hdp' lstp' by (simp add: walk_betw_def)
          have "p' = follow (prnt S) w" using less.hyps[OF lenw refl wV wbp' dp'] .
          thus ?thesis using pP bw fy by simp
        next
          assume child: "prnt S b = Some y"
          have yinfy: "y \<in> set (follow (prnt S) y)"
            using follow_ne_ps[OF ps] follow_hd_ps[OF ps] by (metis hd_in_set)
          have bC: "b \<in> children (prnt S) y"
          proof -
            have "follow (prnt S) b = b # follow (prnt S) y"
              by (simp add: follow_ps_simps[OF ps] child)
            hence "y \<in> set (follow (prnt S) b)" using yinfy by simp
            thus ?thesis by (simp add: children_def)
          qed
          have ynotp': "y \<notin> set p'" using dp pP by simp
          have hdp'b: "hd p' \<in> children (prnt S) y" using p'P bC by simp
          have subeq: "set p' \<subseteq> children (prnt S) y"
            using subtree_cut[OF ps pthp' ynotp' hdp'b] .
          have "r \<in> set p'" using lstp' p'ne last_in_set by metis
          hence "r \<in> children (prnt S) y" using subeq by auto
          hence "y \<in> set (follow (prnt S) r)" by (simp add: children_def)
          hence "y = r" using froot by simp
          thus ?thesis using False by simp
        qed
      qed
    qed }
  note KEY = this
  fix y p
  assume "y \<in> V" "walk_betw (abstract_arb S) y p r" "distinct p"
  thus "p = follow (prnt S) y" using KEY[OF refl] by blast
qed

lemma children_subset_V:
  assumes inv: "arb_invar r V S" and vV: "v \<in> V"
  shows "children (prnt S) v \<subseteq> V"
proof
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have domeq: "dom (prnt S) = V - {r}" by (rule rooted_arborescense_invar_dom[OF rinv])
  fix u assume "u \<in> children (prnt S) v"
  hence vf: "v \<in> set (follow (prnt S) u)" unfolding children_def by simp
  show "u \<in> V"
  proof (rule ccontr)
    assume "u \<notin> V"
    hence "prnt S u = None" using domeq by auto
    hence "follow (prnt S) u = [u]" by (subst follow_ps_simps[OF ps]) simp
    hence "v = u" using vf by simp
    thus False using vV \<open>u \<notin> V\<close> by simp
  qed
qed

lemma iterate_set_eq:
  assumes inv: "arb_invar r V S" and vV: "v \<in> V"
  shows "{x |x p. walk_betw (abstract_arb S) x p r \<and> distinct p \<and> v \<in> set p}
         = children (prnt S) v"
proof (rule Set.set_eqI, rule iffI)
  fix x assume "x \<in> {x |x p. walk_betw (abstract_arb S) x p r \<and> distinct p \<and> v \<in> set p}"
  then obtain p where wb: "walk_betw (abstract_arb S) x p r" and dp: "distinct p"
    and vp: "v \<in> set p" by blast
  have xVs: "x \<in> Vs (abstract_arb S)" using wb by (rule walk_endpoints)
  have xV: "x \<in> V" using xVs Vs_abstract_arb[OF inv] by simp
  have "p = follow (prnt S) x" by (rule unique_walk_to_root[OF inv xV wb dp])
  hence "v \<in> set (follow (prnt S) x)" using vp by simp
  thus "x \<in> children (prnt S) v" by (simp add: children_def)
next
  fix x assume xc: "x \<in> children (prnt S) v"
  have xV: "x \<in> V" using children_subset_V[OF inv vV] xc by auto
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have wb: "walk_betw (abstract_arb S) x (follow (prnt S) x) r" by (rule follow_walk_root[OF inv xV])
  have dp: "distinct (follow (prnt S) x)" by (rule follow_distinct_ps[OF ps])
  have vp: "v \<in> set (follow (prnt S) x)" using xc by (simp add: children_def)
  show "x \<in> {x |x p. walk_betw (abstract_arb S) x p r \<and> distinct p \<and> v \<in> set p}"
    using wb dp vp by blast
qed

lemma join_of_sym:
  assumes inv: "arb_invar r V S" and aV: "a \<in> V" and bV: "b \<in> V"
  shows "join_of (prnt S) a b = join_of (prnt S) b a"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have lab: "last (follow (prnt S) a) = last (follow (prnt S) b)"
    using follow_last_root[OF inv aV] follow_last_root[OF inv bV] by simp
  have lba: "last (follow (prnt S) b) = last (follow (prnt S) a)" using lab by simp
  have ja: "join_of (prnt S) a b \<in> set (follow (prnt S) a)"
    and jb: "join_of (prnt S) a b \<in> set (follow (prnt S) b)"
    using join_of_mem[OF ps lab] by auto
  have j'b: "join_of (prnt S) b a \<in> set (follow (prnt S) b)"
    and j'a: "join_of (prnt S) b a \<in> set (follow (prnt S) a)"
    using join_of_mem[OF ps lba] by auto
  have "join_of (prnt S) b a \<in> set (follow (prnt S) (join_of (prnt S) a b))"
    by (rule join_of_first[OF ps lab j'a j'b])
  moreover have "join_of (prnt S) a b \<in> set (follow (prnt S) (join_of (prnt S) b a))"
    by (rule join_of_first[OF ps lba jb ja])
  ultimately show ?thesis using ancestor_antisym[OF ps] by auto
qed

lemma get_path_pair_impl_eval:
  assumes inv: "arb_invar r V S" and uV: "u \<in> V" and vV: "v \<in> V"
  shows "get_path_pair_impl S u v
          = (takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) u),
             takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) v))"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have lst: "last (follow (prnt S) u) = last (follow (prnt S) v)"
    using follow_last_root[OF inv uV] follow_last_root[OF inv vV] by simp
  have ju: "join_of (prnt S) u v \<in> set (follow (prnt S) u)" using join_of_mem(1)[OF ps lst] by simp
  have jv: "join_of (prnt S) u v \<in> set (follow (prnt S) v)" using join_of_mem(2)[OF ps lst] by simp
  have disjj: "set (takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) u))
              \<inter> set (takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) v)) = {}"
    by (rule join_takeWhile_disjoint[OF inv uV vV refl])
  have "join_paths_loop S u v [] []
        = (takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) u),
           takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) v))"
    using join_paths_loop_eval[OF inv uV vV ju jv disjj, of "[]" "[]"] by simp
  thus ?thesis by (simp add: get_path_pair_impl_def)
qed

lemma get_path_pair_axiom1:
  assumes inv: "arb_invar r V S" and gp: "get_path_pair_impl S u v = (p1, p2)"
    and une: "u \<noteq> v" and uV: "u \<in> V" and vV: "v \<in> V"
  shows "\<exists>a p3. walk_betw (abstract_arb S) u (p1 @ a # p3) r \<and>
                walk_betw (abstract_arb S) v (p2 @ a # p3) r \<and>
                distinct (p1 @ a # p3) \<and> distinct (p2 @ a # p3) \<and>
                set p1 \<inter> set p2 = {}"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  define j where "j = join_of (prnt S) u v"
  have fu: "follow (prnt S) u = p1 @ follow (prnt S) j"
    using get_path_pair_impl_correct(1)[OF inv uV vV gp] by (simp add: j_def)
  have fv: "follow (prnt S) v = p2 @ follow (prnt S) j"
    using get_path_pair_impl_correct(2)[OF inv uV vV gp] by (simp add: j_def)
  have disj: "set p1 \<inter> set p2 = {}"
    using get_path_pair_impl_correct(5)[OF inv uV vV gp] .
  have fj: "follow (prnt S) j = j # tl (follow (prnt S) j)"
    using follow_ne_ps[OF ps] follow_hd_ps[OF ps] by (metis hd_Cons_tl)
  have wu: "walk_betw (abstract_arb S) u (follow (prnt S) u) r" by (rule follow_walk_root[OF inv uV])
  have wv: "walk_betw (abstract_arb S) v (follow (prnt S) v) r" by (rule follow_walk_root[OF inv vV])
  have du: "distinct (follow (prnt S) u)" by (rule follow_distinct_ps[OF ps])
  have dv: "distinct (follow (prnt S) v)" by (rule follow_distinct_ps[OF ps])
  have eu: "follow (prnt S) u = p1 @ j # tl (follow (prnt S) j)" using fu fj by simp
  have ev: "follow (prnt S) v = p2 @ j # tl (follow (prnt S) j)" using fv fj by simp
  have g1: "walk_betw (abstract_arb S) u (p1 @ j # tl (follow (prnt S) j)) r" using wu eu by metis
  have g2: "walk_betw (abstract_arb S) v (p2 @ j # tl (follow (prnt S) j)) r" using wv ev by metis
  have g3: "distinct (p1 @ j # tl (follow (prnt S) j))" using du eu by metis
  have g4: "distinct (p2 @ j # tl (follow (prnt S) j))" using dv ev by metis
  show ?thesis using g1 g2 g3 g4 disj by blast
qed

lemma get_path_pair_axiom2:
  assumes inv: "arb_invar r V S" and gp: "get_path_pair_impl S u v = (p1, p2)"
    and une: "u \<noteq> v" and uV: "u \<in> V" and vV: "v \<in> V"
  shows "get_path_pair_impl S v u = (p2, p1)"
proof -
  have e1: "get_path_pair_impl S u v
        = (takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) u),
           takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) v))"
    by (rule get_path_pair_impl_eval[OF inv uV vV])
  have e2: "get_path_pair_impl S v u
        = (takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) v u) (follow (prnt S) v),
           takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) v u) (follow (prnt S) u))"
    by (rule get_path_pair_impl_eval[OF inv vV uV])
  have jsym: "join_of (prnt S) v u = join_of (prnt S) u v" by (rule join_of_sym[OF inv vV uV])
  have p1: "p1 = takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) u)"
    and p2: "p2 = takeWhile (\<lambda>x. x \<noteq> join_of (prnt S) u v) (follow (prnt S) v)"
    using gp e1 by auto
  show ?thesis using e2 jsym p1 p2 by simp
qed

lemma iterate_axiom:
  assumes inv: "arb_invar r V S" and vV: "v \<in> V"
  shows "\<exists>xs. set xs = {x |x p. walk_betw (abstract_arb S) x p r \<and> distinct p \<and> v \<in> set p}
              \<and> distinct xs \<and> iterate_root_opposed_impl S v f acc = foldr f xs acc"
  using iterate_root_opposed_impl_foldr[OF inv vV, of f acc] iterate_set_eq[OF inv vV] by auto

text \<open>The custom two-loop potential shift @{const shift_pot_impl} (one loop adding, one subtracting)
      coincides with the generic subtree iteration once the @{term up} flag is fixed: reconstruct the
      thread-block decomposition of @{term v}'s subtree (as in @{thm [source]
      iterate_root_opposed_impl_block}) and feed it to the per-loop equivalences proved in the code
      theory.  This is the promised equivalence to the ``old tree fold''.\<close>
lemma shift_pot_impl_eq_iterate:
  assumes inv: "arb_invar r V S" and vV: "v \<in> V"
  shows "shift_pot_impl S v pa g up
          = iterate_root_opposed_impl S v
              (\<lambda>x acc. acc[x := (if up then pval_plus (acc ! x) g else pval_minus (acc ! x) g)]) pa"
proof -
  have pst: "parent_spec (thrd S)" using inv unfolding arb_invar_def by simp
  have bne: "block S v \<noteq> []" by (rule block_props(2)[OF inv vV])
  have blast': "last (block S v) = lsuc S v" by (rule block_props(3)[OF inv vV])
  have decomp: "follow (thrd S) v = block S v @ (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    by (rule block_props(1)[OF inv vV])
  define bl where "bl = butlast (block S v)"
  have blk: "block S v = bl @ [lsuc S v]"
    unfolding bl_def using append_butlast_last_id[OF bne] blast' by simp
  have distf: "distinct (follow (thrd S) v)" by (rule follow_distinct_ps[OF pst])
  have distb: "distinct (block S v)" using distf decomp by (metis distinct_append)
  have notin: "lsuc S v \<notin> set bl" using distb blk by simp
  have L: "follow (thrd S) v = bl @ lsuc S v # (case thrd S (lsuc S v) of None \<Rightarrow> [] | Some w \<Rightarrow> follow (thrd S) w)"
    using decomp blk by simp
  show ?thesis
  proof (cases up)
    case True
    have "shift_pot_up_loop S (lsuc S v) g v pa
            = subtree_fold S (lsuc S v) v (\<lambda>x acc. acc[x := pval_plus (acc ! x) g]) pa"
      by (rule shift_pot_up_loop_subtree_fold[OF pst L notin])
    thus ?thesis using True by (simp add: shift_pot_impl_def iterate_root_opposed_impl_def)
  next
    case False
    have "shift_pot_down_loop S (lsuc S v) g v pa
            = subtree_fold S (lsuc S v) v (\<lambda>x acc. acc[x := pval_minus (acc ! x) g]) pa"
      by (rule shift_pot_down_loop_subtree_fold[OF pst L notin])
    thus ?thesis using False by (simp add: shift_pot_impl_def iterate_root_opposed_impl_def)
  qed
qed

text \<open>Hence @{const shift_pot_impl} satisfies the @{text shift_pot_spec} obligation of
      @{locale network_simplex_spec}: it is a @{const foldr} over a distinct enumeration of exactly the
      subtree of @{term v} (the nodes whose path to the root passes through @{term v}), whose per-node
      step reads/shifts/writes the potential.\<close>
lemma shift_pot_impl_spec:
  assumes inv: "arb_invar r V S" and vV: "v \<in> V"
  shows "\<exists>xs. set xs = {x. \<exists>p. walk_betw (abstract_arb S) x p r \<and> distinct p \<and> v \<in> set p}
              \<and> distinct xs
              \<and> shift_pot_impl S v pa g up
                  = foldr (\<lambda>x acc. acc[x := (if up then pval_plus else pval_minus) (acc ! x) g]) xs pa"
proof -
  let ?F = "\<lambda>x acc. acc[x := (if up then pval_plus (acc ! x) g else pval_minus (acc ! x) g)]"
  have eq: "shift_pot_impl S v pa g up = iterate_root_opposed_impl S v ?F pa"
    by (rule shift_pot_impl_eq_iterate[OF inv vV])
  obtain xs where xs: "set xs = {x |x p. walk_betw (abstract_arb S) x p r \<and> distinct p \<and> v \<in> set p}"
     "distinct xs" "iterate_root_opposed_impl S v ?F pa = foldr ?F xs pa"
    using iterate_axiom[OF inv vV, of ?F pa] by blast
  have setEq: "{x |x p. walk_betw (abstract_arb S) x p r \<and> distinct p \<and> v \<in> set p}
             = {x. \<exists>p. walk_betw (abstract_arb S) x p r \<and> distinct p \<and> v \<in> set p}" by blast
  have FG: "?F = (\<lambda>x acc. acc[x := (if up then pval_plus else pval_minus) (acc ! x) g])"
    by (cases up) auto
  show ?thesis using xs eq FG setEq by (intro exI[of _ xs]) simp
qed

lemma co_cut:
  assumes ps: "parent_spec (prnt S)"
  shows "path (abstract_arb S) q \<Longrightarrow> y \<notin> set q \<Longrightarrow> hd q \<notin> children (prnt S) y
          \<Longrightarrow> set q \<inter> children (prnt S) y = {}"
proof (induct q)
  case Nil thus ?case by simp
next
  case (Cons a q')
  have aNC: "a \<notin> children (prnt S) y" using Cons.prems(3) by simp
  show ?case
  proof (cases q')
    case Nil thus ?thesis using aNC by simp
  next
    case (Cons b rest)
    have qeq: "q' = b # rest" by (rule Cons)
    have edge: "{a, b} \<in> abstract_arb S" using Cons.prems(1) qeq by (simp add: path_2)
    have pq': "path (abstract_arb S) q'" using Cons.prems(1) qeq by (simp add: path_2)
    have bNC: "b \<notin> children (prnt S) y"
    proof -
      from abstract_arb_edgeD[OF ps edge] show ?thesis
      proof
        assume pa: "prnt S a = Some b"
        have "y \<notin> set (follow (prnt S) a)" using aNC by (simp add: children_def)
        moreover have "follow (prnt S) a = a # follow (prnt S) b"
          using pa by (simp add: follow_ps_simps[OF ps])
        ultimately have "y \<notin> set (follow (prnt S) b)" by simp
        thus ?thesis by (simp add: children_def)
      next
        assume pb: "prnt S b = Some a"
        have fb: "follow (prnt S) b = b # follow (prnt S) a" using pb by (simp add: follow_ps_simps[OF ps])
        have yna: "y \<notin> set (follow (prnt S) a)" using aNC by (simp add: children_def)
        have ynb: "y \<noteq> b" using Cons.prems(2) qeq by simp
        have "y \<notin> set (follow (prnt S) b)" using fb yna ynb by simp
        thus ?thesis by (simp add: children_def)
      qed
    qed
    have ynot': "y \<notin> set q'" using Cons.prems(2) by simp
    have hdNC: "hd q' \<notin> children (prnt S) y" using bNC qeq by simp
    have "set q' \<inter> children (prnt S) y = {}" using Cons.hyps[OF pq' ynot' hdNC] .
    thus ?thesis using aNC by auto
  qed
qed

lemma child_pred_unique:
  assumes ps: "parent_spec T"
    and pb: "T b = Some y" and pb': "T b' = Some y"
    and xb: "b \<in> set (follow T x)" and xb': "b' \<in> set (follow T x)"
  shows "b = b'"
proof -
  from xb obtain A B where dA: "follow T x = A @ b # B" by (meson split_list)
  have "follow T b = b # B" using follow_append_ps[OF ps dA] .
  moreover have "follow T b = b # follow T y" using pb by (simp add: follow_ps_simps[OF ps])
  ultimately have "B = follow T y" by simp
  hence dx1: "follow T x = A @ b # follow T y" using dA by simp
  from xb' obtain A' B' where dA': "follow T x = A' @ b' # B'" by (meson split_list)
  have "follow T b' = b' # B'" using follow_append_ps[OF ps dA'] .
  moreover have "follow T b' = b' # follow T y" using pb' by (simp add: follow_ps_simps[OF ps])
  ultimately have "B' = follow T y" by simp
  hence dx2: "follow T x = A' @ b' # follow T y" using dA' by simp
  have "(A @ [b]) @ follow T y = (A' @ [b']) @ follow T y" using dx1 dx2 by simp
  hence "A @ [b] = A' @ [b']" by simp
  thus "b = b'" by (metis last_snoc)
qed

lemma first_step_char:
  assumes inv: "arb_invar r V S" and ps: "parent_spec (prnt S)"
    and wb: "walk_betw (abstract_arb S) y p x" and dist: "distinct p" and pP: "p = y # b # p''"
  shows "(x \<in> children (prnt S) y \<and> prnt S b = Some y \<and> x \<in> children (prnt S) b)
       \<or> (x \<notin> children (prnt S) y \<and> prnt S y = Some b)"
proof -
  have pth: "path (abstract_arb S) p" and lst: "last p = x" using wb by (auto simp: walk_betw_def)
  have edge: "{y, b} \<in> abstract_arb S" using pth pP by (simp add: path_2)
  have pthrest: "path (abstract_arb S) (b # p'')" using pth pP by (simp add: path_2)
  have lstrest: "last (b # p'') = x" using lst pP by simp
  have ynotrest: "y \<notin> set (b # p'')" using dist pP by simp
  have yinfy: "y \<in> set (follow (prnt S) y)"
    using follow_ne_ps[OF ps] follow_hd_ps[OF ps] by (metis hd_in_set)
  from abstract_arb_edgeD[OF ps edge] show ?thesis
  proof
    assume pyb: "prnt S y = Some b"
    have bNC: "b \<notin> children (prnt S) y"
    proof -
      have fy: "follow (prnt S) y = y # follow (prnt S) b" using pyb by (simp add: follow_ps_simps[OF ps])
      have "distinct (follow (prnt S) y)" by (rule follow_distinct_ps[OF ps])
      hence "y \<notin> set (follow (prnt S) b)" using fy by simp
      thus ?thesis by (simp add: children_def)
    qed
    have "set (b # p'') \<inter> children (prnt S) y = {}"
      using co_cut[OF ps pthrest ynotrest] bNC by simp
    hence "x \<notin> children (prnt S) y" using lstrest last_in_set by (metis IntI empty_iff list.distinct(1))
    thus ?thesis using pyb by blast
  next
    assume pby: "prnt S b = Some y"
    have bC: "b \<in> children (prnt S) y"
    proof -
      have "follow (prnt S) b = b # follow (prnt S) y" using pby by (simp add: follow_ps_simps[OF ps])
      hence "y \<in> set (follow (prnt S) b)" using yinfy by simp
      thus ?thesis by (simp add: children_def)
    qed
    have binfb: "b \<in> set (follow (prnt S) b)"
      using follow_ne_ps[OF ps] follow_hd_ps[OF ps] by (metis hd_in_set)
    have xCb: "x \<in> children (prnt S) b"
    proof (cases p'')
      case Nil
      have "x = b" using lstrest Nil by simp
      thus ?thesis using binfb by (simp add: children_def)
    next
      case (Cons c rest2)
      have edgebc: "{b, c} \<in> abstract_arb S" using pthrest Cons by (simp add: path_2)
      have pc: "path (abstract_arb S) p''" using pthrest Cons by (simp add: path_2)
      have bnotp'': "b \<notin> set p''" using dist pP by simp
      have cchild: "prnt S c = Some b"
      proof -
        from abstract_arb_edgeD[OF ps edgebc] show ?thesis
        proof
          assume ac: "prnt S b = Some c"
          have "c = y" using ac pby by simp
          moreover have "c \<in> set (b # p'')" using Cons by simp
          ultimately have False using ynotrest by simp
          thus ?thesis by simp
        next
          assume "prnt S c = Some b" thus ?thesis .
        qed
      qed
      have cCb: "c \<in> children (prnt S) b"
      proof -
        have "follow (prnt S) c = c # follow (prnt S) b" using cchild by (simp add: follow_ps_simps[OF ps])
        hence "b \<in> set (follow (prnt S) c)" using binfb by simp
        thus ?thesis by (simp add: children_def)
      qed
      have hdc: "hd p'' \<in> children (prnt S) b" using cCb Cons by simp
      have subeq: "set p'' \<subseteq> children (prnt S) b"
        using subtree_cut[OF ps pc bnotp'' hdc] .
      have "x \<in> set p''" using lstrest Cons last_in_set by (metis last_ConsR list.distinct(1))
      thus ?thesis using subeq by auto
    qed
    have xCy: "x \<in> children (prnt S) y" using xCb children_subset[OF ps bC] by auto
    show ?thesis using xCy pby xCb by blast
  qed
qed

lemma closed_distinct_walk:
  assumes "p \<noteq> []" and "hd p = z" and "last p = z" and "distinct p"
  shows "p = [z]"
proof (cases p)
  case Nil thus ?thesis using assms(1) by simp
next
  case (Cons a rest)
  have az: "a = z" using assms(2) Cons by simp
  have "rest = []"
  proof (rule ccontr)
    assume rne: "rest \<noteq> []"
    have "last rest \<in> set rest" using rne last_in_set by simp
    moreover have "last rest = z" using Cons rne assms(3) by simp
    moreover have "a \<notin> set rest" using assms(4) Cons by simp
    ultimately show False using az by simp
  qed
  thus ?thesis using Cons az by simp
qed

lemma walk_unique:
  assumes inv: "arb_invar r V S" and xV: "x \<in> V"
  shows "\<And>y p q. y \<in> V \<Longrightarrow> walk_betw (abstract_arb S) y p x \<Longrightarrow> distinct p
              \<Longrightarrow> walk_betw (abstract_arb S) y q x \<Longrightarrow> distinct q \<Longrightarrow> p = q"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  { fix n y p q
    have "length p = n \<Longrightarrow> y \<in> V \<Longrightarrow> walk_betw (abstract_arb S) y p x \<Longrightarrow> distinct p \<Longrightarrow>
          walk_betw (abstract_arb S) y q x \<Longrightarrow> distinct q \<Longrightarrow> p = q"
    proof (induct n arbitrary: y p q rule: less_induct)
      case (less n y p q)
      note eqn = less.prems(1) and yV = less.prems(2) and wp = less.prems(3)
        and dp = less.prems(4) and wq = less.prems(5) and dq = less.prems(6)
      have pne: "p \<noteq> []" and hdp: "hd p = y" and lstp: "last p = x"
        using wp by (auto simp: walk_betw_def)
      have qne: "q \<noteq> []" and hdq: "hd q = y" and lstq: "last q = x"
        using wq by (auto simp: walk_betw_def)
      show ?case
      proof (cases "y = x")
        case True
        have "p = [y]" using closed_distinct_walk[OF pne hdp _ dp] lstp True by simp
        moreover have "q = [y]" using closed_distinct_walk[OF qne hdq _ dq] lstq True by simp
        ultimately show ?thesis by simp
      next
        case False
        obtain p' where pP: "p = y # p'" using hdp pne by (cases p) auto
        obtain q' where qP: "q = y # q'" using hdq qne by (cases q) auto
        have p'ne: "p' \<noteq> []" using pP lstp False by (cases p') auto
        have q'ne: "q' \<noteq> []" using qP lstq False by (cases q') auto
        obtain b pp where pP2: "p = y # b # pp" using pP p'ne by (cases p') auto
        obtain b' qq where qP2: "q = y # b' # qq" using qP q'ne by (cases q') auto
        have cb: "(x \<in> children (prnt S) y \<and> prnt S b = Some y \<and> x \<in> children (prnt S) b)
                \<or> (x \<notin> children (prnt S) y \<and> prnt S y = Some b)"
          by (rule first_step_char[OF inv ps wp dp pP2])
        have cb': "(x \<in> children (prnt S) y \<and> prnt S b' = Some y \<and> x \<in> children (prnt S) b')
                \<or> (x \<notin> children (prnt S) y \<and> prnt S y = Some b')"
          by (rule first_step_char[OF inv ps wq dq qP2])
        have bb': "b = b'"
        proof (cases "x \<in> children (prnt S) y")
          case True
          have c1: "prnt S b = Some y" "x \<in> children (prnt S) b" using cb True by auto
          have c2: "prnt S b' = Some y" "x \<in> children (prnt S) b'" using cb' True by auto
          have "b \<in> set (follow (prnt S) x)" using c1(2) by (simp add: children_def)
          moreover have "b' \<in> set (follow (prnt S) x)" using c2(2) by (simp add: children_def)
          ultimately show ?thesis using child_pred_unique[OF ps c1(1) c2(1)] by blast
        next
          case False
          have "prnt S y = Some b" using cb False by auto
          moreover have "prnt S y = Some b'" using cb' False by auto
          ultimately show ?thesis by simp
        qed
        have p'eq: "p' = b # pp" using pP pP2 by simp
        have q'eq: "q' = b' # qq" using qP qP2 by simp
        have bVs: "b \<in> Vs (abstract_arb S)" using walk_in_Vs[OF wp] pP2 by auto
        have bV: "b \<in> V" using bVs Vs_abstract_arb[OF inv] by simp
        have wpp: "walk_betw (abstract_arb S) b p' x"
        proof -
          have "path (abstract_arb S) p'" using wp pP by (metis tl_path_is_path walk_betw_def list.sel(3))
          moreover have "hd p' = b" using p'eq by simp
          moreover have "last p' = x" using lstp pP p'ne by simp
          ultimately show ?thesis using p'ne by (simp add: walk_betw_def)
        qed
        have wqq: "walk_betw (abstract_arb S) b q' x"
        proof -
          have "path (abstract_arb S) q'" using wq qP by (metis tl_path_is_path walk_betw_def list.sel(3))
          moreover have "hd q' = b" using q'eq bb' by simp
          moreover have "last q' = x" using lstq qP q'ne by simp
          ultimately show ?thesis using q'ne by (simp add: walk_betw_def)
        qed
        have dpp: "distinct p'" using dp pP by simp
        have dqq: "distinct q'" using dq qP by simp
        have lenlt: "length p' < n" using eqn pP by simp
        have "p' = q'" by (rule less.hyps[OF lenlt refl bV wpp dpp wqq dqq])
        thus ?thesis using pP qP by simp
      qed
    qed }
  note KEY = this
  fix y p q
  assume "y \<in> V" "walk_betw (abstract_arb S) y p x" "distinct p"
         "walk_betw (abstract_arb S) y q x" "distinct q"
  thus "p = q" using KEY[OF refl] by blast
qed

lemma follow_prefix_walk:
  assumes inv: "arb_invar r V S" and vV: "v \<in> V"
    and pref: "follow (prnt S) v = pfx @ [jn] @ sfx"
  shows "walk_betw (abstract_arb S) v (pfx @ [jn]) jn"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have wv: "walk_betw (abstract_arb S) v (follow (prnt S) v) r" by (rule follow_walk_root[OF inv vV])
  have pth_all: "path (abstract_arb S) (follow (prnt S) v)" using wv by (simp add: walk_betw_def)
  have "path (abstract_arb S) ((pfx @ [jn]) @ sfx)" using pth_all pref by simp
  hence pthpre: "path (abstract_arb S) (pfx @ [jn])" by (rule path_pref)
  have hdv: "hd (pfx @ [jn]) = v"
  proof (cases pfx)
    case Nil
    have "follow (prnt S) v = jn # sfx" using pref Nil by simp
    hence "v = jn" using follow_hd_ps[OF ps] by (metis list.sel(1))
    thus ?thesis using Nil by simp
  next
    case (Cons a as)
    have "hd (follow (prnt S) v) = v" by (rule follow_hd_ps[OF ps])
    thus ?thesis using pref Cons by simp
  qed
  show ?thesis using pthpre hdv by (simp add: walk_betw_def)
qed

lemma walk_exists:
  assumes inv: "arb_invar r V S" and yV: "y \<in> V" and xV: "x \<in> V"
  shows "\<exists>p. walk_betw (abstract_arb S) y p x \<and> distinct p"
proof (cases "y = x")
  case True
  have "walk_betw (abstract_arb S) y [y] x \<and> distinct [y]"
    using True xV Vs_abstract_arb[OF inv] by (simp add: walk_reflexive)
  thus ?thesis by blast
next
  case False
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  obtain q1 q2 where gp: "get_path_pair_impl S y x = (q1, q2)" by fastforce
  define j where "j = join_of (prnt S) y x"
  have fy: "follow (prnt S) y = q1 @ follow (prnt S) j"
    using get_path_pair_impl_correct(1)[OF inv yV xV gp] by (simp add: j_def)
  have fx: "follow (prnt S) x = q2 @ follow (prnt S) j"
    using get_path_pair_impl_correct(2)[OF inv yV xV gp] by (simp add: j_def)
  have dq1j: "distinct (q1 @ [j])" using get_path_pair_impl_correct(3)[OF inv yV xV gp] by (simp add: j_def)
  have dq2j: "distinct (q2 @ [j])" using get_path_pair_impl_correct(4)[OF inv yV xV gp] by (simp add: j_def)
  have disj: "set q1 \<inter> set q2 = {}" using get_path_pair_impl_correct(5)[OF inv yV xV gp] .
  have fj: "follow (prnt S) j = j # tl (follow (prnt S) j)"
    using follow_ne_ps[OF ps] follow_hd_ps[OF ps] by (metis hd_Cons_tl)
  have prefy: "follow (prnt S) y = q1 @ [j] @ tl (follow (prnt S) j)" using fy fj by simp
  have prefx: "follow (prnt S) x = q2 @ [j] @ tl (follow (prnt S) j)" using fx fj by simp
  have wyj: "walk_betw (abstract_arb S) y (q1 @ [j]) j" by (rule follow_prefix_walk[OF inv yV prefy])
  have wxj: "walk_betw (abstract_arb S) x (q2 @ [j]) j" by (rule follow_prefix_walk[OF inv xV prefx])
  have wjx: "walk_betw (abstract_arb S) j (j # rev q2) x"
    using walk_symmetric[OF wxj] by simp
  have wyx: "walk_betw (abstract_arb S) y ((q1 @ [j]) @ tl (j # rev q2)) x"
    by (rule walk_transitive[OF wyj wjx])
  have cw: "(q1 @ [j]) @ tl (j # rev q2) = q1 @ j # rev q2" by simp
  have dcw: "distinct (q1 @ j # rev q2)"
  proof -
    have jq1: "j \<notin> set q1" using dq1j by (auto simp: distinct_append)
    have jq2: "j \<notin> set q2" using dq2j by (auto simp: distinct_append)
    have d1: "distinct q1" using dq1j by (auto simp: distinct_append)
    have d2: "distinct q2" using dq2j by (auto simp: distinct_append)
    show ?thesis using jq1 jq2 d1 d2 disj by (auto simp: distinct_append)
  qed
  have "walk_betw (abstract_arb S) y (q1 @ j # rev q2) x \<and> distinct (q1 @ j # rev q2)"
    using wyx cw dcw by simp
  thus ?thesis by blast
qed

lemma general_axiom3:
  assumes inv: "arb_invar r V S" and xV: "x \<in> V" and yV: "y \<in> V"
  shows "\<exists>! p. walk_betw (abstract_arb S) y p x \<and> distinct p"
proof -
  obtain p where p: "walk_betw (abstract_arb S) y p x \<and> distinct p"
    using walk_exists[OF inv yV xV] by blast
  show ?thesis
  proof (rule ex1I[of _ p])
    show "walk_betw (abstract_arb S) y p x \<and> distinct p" by (rule p)
  next
    fix q assume q: "walk_betw (abstract_arb S) y q x \<and> distinct q"
    show "q = p" using walk_unique[OF inv xV yV] q p by blast
  qed
qed

lemma swap_edge_axiom1:
  assumes inv: "arb_invar r V S" and gp: "get_path_pair_impl S u v = (p1, p2)"
    and une: "u \<noteq> v"
    and wu: "walk_betw (abstract_arb S) u (p1 @ a # p3) r"
    and dist: "distinct (p1 @ a # p3)"
    and em: "(x, y) \<in> set (edges_of_vwalk (p1 @ [a]))"
    and uV: "u \<in> V" and vV: "v \<in> V"
  shows "arb_invar r V (swap_edge_impl S x u v)"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have wfu: "p1 @ a # p3 = follow (prnt S) u" by (rule unique_walk_to_root[OF inv uV wu dist])
  define j where "j = join_of (prnt S) u v"
  have fu_split: "follow (prnt S) u = p1 @ follow (prnt S) j"
    using get_path_pair_impl_correct(1)[OF inv uV vV gp] by (simp add: j_def)
  have "p1 @ a # p3 = p1 @ follow (prnt S) j" using wfu fu_split by simp
  hence fj: "follow (prnt S) j = a # p3" by simp
  have aj: "a = j" using fj follow_hd_ps[OF ps] by (metis list.sel(1))
  have p1ne: "p1 \<noteq> []"
  proof (rule ccontr)
    assume "\<not> p1 \<noteq> []" hence "p1 = []" by simp
    hence "edges_of_vwalk (p1 @ [a]) = []" by simp
    thus False using em by simp
  qed
  have ev_dec: "edges_of_vwalk (p1 @ [a]) = edges_of_vwalk p1 @ [(last p1, a)]"
    using edges_of_vwalk_append_3[OF p1ne, of "[a]"] p1ne by simp
  have xp1: "x \<in> set p1"
  proof -
    from em ev_dec have "(x, y) \<in> set (edges_of_vwalk p1) \<or> (x, y) = (last p1, a)" by auto
    thus ?thesis
    proof
      assume "(x, y) \<in> set (edges_of_vwalk p1)" thus ?thesis using v_in_edge_in_vwalk by fast
    next
      assume "(x, y) = (last p1, a)" thus ?thesis using p1ne last_in_set by auto
    qed
  qed
  have xfu: "x \<in> set (follow (prnt S) u)"
  proof -
    have "x \<in> set (p1 @ a # p3)" using xp1 by simp
    thus ?thesis using wfu by simp
  qed
  have anotp1: "a \<notin> set p1" using dist by (auto simp: distinct_append)
  have xnej: "x \<noteq> j" using xp1 anotp1 aj by auto
  have jfx: "j \<in> set (follow (prnt S) x)"
  proof -
    from xp1 obtain A1 A2 where p1split: "p1 = A1 @ x # A2" by (meson split_list)
    have "follow (prnt S) u = A1 @ x # (A2 @ follow (prnt S) j)" using fu_split p1split by simp
    hence fx: "follow (prnt S) x = x # (A2 @ follow (prnt S) j)" using follow_append_ps[OF ps] by blast
    have "j \<in> set (follow (prnt S) j)"
      using follow_ne_ps[OF ps] follow_hd_ps[OF ps] by (metis hd_in_set)
    thus ?thesis using fx by simp
  qed
  have jneq: "j = join_of (prnt S) u v" by (simp add: j_def)
  have "arb_invar r V (update_tree S u v x j)"
    by (rule update_tree_preserves_arb_invar(1)[OF inv uV vV jneq xfu jfx xnej])
  thus ?thesis by (simp add: swap_edge_impl_def j_def)
qed

lemma spine_reindex_gen:
  assumes kpos: "0 < k"
  shows "{{s t, if t = 0 then a else s (t - 1)} |t. t \<le> k}
       = insert {s 0, a} {{s t, s (Suc t)} |t. t < k}"
proof (rule Set.set_eqI, rule iffI)
  fix e assume "e \<in> {{s t, if t = 0 then a else s (t - 1)} |t. t \<le> k}"
  then obtain t where tk: "t \<le> k" and e: "e = {s t, if t = 0 then a else s (t - 1)}" by blast
  show "e \<in> insert {s 0, a} {{s t, s (Suc t)} |t. t < k}"
  proof (cases "t = 0")
    case True thus ?thesis using e by simp
  next
    case False
    then obtain u where tu: "t = Suc u" using not0_implies_Suc by blast
    have "u < k" using tu tk by simp
    have "e = {s (Suc u), s u}" using e tu False by simp
    hence "e = {s u, s (Suc u)}" by (simp add: insert_commute)
    thus ?thesis using \<open>u < k\<close> by blast
  qed
next
  fix e assume "e \<in> insert {s 0, a} {{s t, s (Suc t)} |t. t < k}"
  then consider "e = {s 0, a}" | t where "t < k" "e = {s t, s (Suc t)}" by blast
  thus "e \<in> {{s t, if t = 0 then a else s (t - 1)} |t. t \<le> k}"
  proof cases
    case 1 thus ?thesis using kpos by (auto intro!: exI[where x=0])
  next
    case (2 t)
    have "e = {s (Suc t), if Suc t = 0 then a else s (Suc t - 1)}" using 2 by (simp add: insert_commute)
    moreover have "Suc t \<le> k" using 2 by simp
    ultimately show ?thesis by blast
  qed
qed

lemma no_2cycle:
  assumes ps: "parent_spec T" and ab: "T a = Some b" and ba: "T b = Some a"
  shows False
proof -
  have fa: "follow T a = a # follow T b" using ab by (simp add: follow_ps_simps[OF ps])
  hence bfa: "b \<in> set (follow T a)"
    using follow_ne_ps[OF ps] follow_hd_ps[OF ps] by (metis hd_in_set list.set_intros(2))
  have fb: "follow T b = b # follow T a" using ba by (simp add: follow_ps_simps[OF ps])
  hence afb: "a \<in> set (follow T b)"
    using follow_ne_ps[OF ps] follow_hd_ps[OF ps] by (metis hd_in_set list.set_intros(2))
  have "a = b" by (rule ancestor_antisym[OF ps afb bfa])
  thus False using ab parent_spec_neq[OF ps ab] by simp
qed

lemma abstract_edge_swap:
  assumes SS: "stem_setup S0 rr VV ii jj pp k s" and kpos: "0 < k"
    and y0: "prnt S0 pp = Some y0"
  shows "abstract_arb (update_tree S0 ii jj pp jn)
         = abstract_arb S0 - {{pp, y0}} \<union> {{ii, jj}}"
proof -
  interpret ss: stem_setup S0 rr VV ii jj pp k s by (rule SS)
  have rinv: "rooted_arborescense_invar rr VV (prnt S0)" using ss.arb unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S0)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  define NP where "NP = (prnt S0 ++ ss.REV k)(pp \<mapsto> ss.s_pred k)"
  have prnt_ut: "prnt (update_tree S0 ii jj pp jn) = NP"
    using ss.update_tree_prnt[OF kpos] by (simp add: NP_def)
  have skp: "s k = pp" by (rule ss.pathk)
  have s0i: "s 0 = ii" by (rule ss.path0)
  have inj_sk: "inj_on s {..k}" by (rule ss.inj)
  have rev_dom: "dom (ss.REV k) = s ` {0..<k}"
  proof -
    have "dom (ss.REV k) = fst ` set (map (\<lambda>t. (s t, ss.s_pred t)) [0..<k])"
      unfolding ss.REV_def by (rule dom_map_of_conv_image_fst)
    also have "\<dots> = s ` {0..<k}" by (simp add: image_image)
    finally show ?thesis .
  qed
  have rev_look: "\<And>t. t < k \<Longrightarrow> ss.REV k (s t) = Some (ss.s_pred t)"
  proof -
    fix t assume t: "t < k"
    have "distinct (map fst (map (\<lambda>t. (s t, ss.s_pred t)) [0..<k]))"
      using inj_sk by (auto simp: distinct_map inj_on_def)
    moreover have "(s t, ss.s_pred t) \<in> set (map (\<lambda>t. (s t, ss.s_pred t)) [0..<k])" using t by auto
    ultimately show "ss.REV k (s t) = Some (ss.s_pred t)"
      unfolding ss.REV_def by (rule map_of_is_SomeI)
  qed
  have np_all: "\<And>t. t \<le> k \<Longrightarrow> NP (s t) = Some (ss.s_pred t)"
  proof -
    fix t assume t: "t \<le> k"
    show "NP (s t) = Some (ss.s_pred t)"
    proof (cases "t = k")
      case True thus ?thesis using skp by (simp add: NP_def)
    next
      case False
      hence tk: "t < k" using t by simp
      have "s t \<noteq> pp"
      proof
        assume "s t = pp" hence "s t = s k" using skp by simp
        hence "t = k" using inj_sk tk by (auto simp: inj_on_eq_iff)
        thus False using tk by simp
      qed
      moreover have "s t \<in> dom (ss.REV k)" using tk rev_dom by auto
      ultimately show ?thesis using rev_look[OF tk] by (simp add: NP_def map_add_dom_app_simps)
    qed
  qed
  have np_off: "\<And>z. z \<notin> s ` {0..k} \<Longrightarrow> NP z = prnt S0 z"
  proof -
    fix z assume z: "z \<notin> s ` {0..k}"
    have "z \<noteq> pp" using z skp by auto
    moreover have "z \<notin> dom (ss.REV k)" using z rev_dom by auto
    ultimately show "NP z = prnt S0 z" by (simp add: NP_def map_add_dom_app_simps)
  qed
  define ST where "ST = s ` {0..k}"
  define OFF where "OFF = {{z, w} |z w. z \<notin> ST \<and> prnt S0 z = Some w}"
  define SPINE where "SPINE = {{s t, s (Suc t)} |t. t < k}"
  have STmem: "\<And>z. z \<in> ST \<Longrightarrow> \<exists>t. t \<le> k \<and> z = s t" by (auto simp: ST_def)
  have ppST: "pp \<in> ST" using skp by (auto simp: ST_def)
  have spred_eq: "\<And>t. ss.s_pred t = (if t = 0 then jj else s (t - 1))" by (simp add: ss.s_pred_def)
  have STedges_np: "{{z, w} |z w. z \<in> ST \<and> NP z = Some w} = insert {ii, jj} SPINE"
  proof -
    have "{{z, w} |z w. z \<in> ST \<and> NP z = Some w} = {{s t, ss.s_pred t} |t. t \<le> k}"
    proof (rule Set.set_eqI, rule iffI)
      fix e assume "e \<in> {{z, w} |z w. z \<in> ST \<and> NP z = Some w}"
      then obtain z w where zST: "z \<in> ST" and npz: "NP z = Some w" and e: "e = {z, w}" by blast
      from STmem[OF zST] obtain t where tk: "t \<le> k" and zt: "z = s t" by blast
      have "w = ss.s_pred t" using npz np_all[OF tk] zt by simp
      thus "e \<in> {{s t, ss.s_pred t} |t. t \<le> k}" using e zt tk by blast
    next
      fix e assume "e \<in> {{s t, ss.s_pred t} |t. t \<le> k}"
      then obtain t where tk: "t \<le> k" and e: "e = {s t, ss.s_pred t}" by blast
      have "s t \<in> ST" using tk by (auto simp: ST_def)
      moreover have "NP (s t) = Some (ss.s_pred t)" by (rule np_all[OF tk])
      ultimately show "e \<in> {{z, w} |z w. z \<in> ST \<and> NP z = Some w}" using e by blast
    qed
    also have "\<dots> = {{s t, if t = 0 then jj else s (t - 1)} |t. t \<le> k}" by (simp add: spred_eq)
    also have "\<dots> = insert {s 0, jj} {{s t, s (Suc t)} |t. t < k}" by (rule spine_reindex_gen[OF kpos])
    also have "\<dots> = insert {ii, jj} SPINE" using s0i by (simp add: SPINE_def)
    finally show ?thesis .
  qed
  have STedges_0: "{{z, w} |z w. z \<in> ST \<and> prnt S0 z = Some w} = insert {pp, y0} SPINE"
  proof (rule Set.set_eqI, rule iffI)
    fix e assume "e \<in> {{z, w} |z w. z \<in> ST \<and> prnt S0 z = Some w}"
    then obtain z w where zST: "z \<in> ST" and pz: "prnt S0 z = Some w" and e: "e = {z, w}" by blast
    from STmem[OF zST] obtain t where tk: "t \<le> k" and zt: "z = s t" by blast
    show "e \<in> insert {pp, y0} SPINE"
    proof (cases "t = k")
      case True
      have "z = pp" using zt True skp by simp
      hence "w = y0" using pz y0 by simp
      thus ?thesis using e \<open>z = pp\<close> by simp
    next
      case False
      hence tk': "t < k" using tk by simp
      have "prnt S0 (s t) = Some (s (Suc t))" by (rule ss.pathS[OF tk'])
      hence "w = s (Suc t)" using pz zt by simp
      thus ?thesis using e zt tk' by (auto simp: SPINE_def)
    qed
  next
    fix e assume "e \<in> insert {pp, y0} SPINE"
    then consider "e = {pp, y0}" | t where "t < k" "e = {s t, s (Suc t)}" by (auto simp: SPINE_def)
    thus "e \<in> {{z, w} |z w. z \<in> ST \<and> prnt S0 z = Some w}"
    proof cases
      case 1 thus ?thesis using ppST y0 by blast
    next
      case (2 t)
      have "s t \<in> ST" using 2 by (auto simp: ST_def)
      moreover have "prnt S0 (s t) = Some (s (Suc t))" by (rule ss.pathS[OF \<open>t < k\<close>])
      ultimately show ?thesis using 2 by blast
    qed
  qed
  have P1: "{{z, w} |z w. NP z = Some w} = OFF \<union> insert {ii, jj} SPINE"
  proof -
    have offeq: "{{z, w} |z w. z \<notin> ST \<and> NP z = Some w} = OFF"
    proof (rule Set.set_eqI, rule iffI)
      fix e assume "e \<in> {{z, w} |z w. z \<notin> ST \<and> NP z = Some w}"
      then obtain z w where zn: "z \<notin> ST" and npz: "NP z = Some w" and e: "e = {z, w}" by blast
      have "z \<notin> s ` {0..k}" using zn by (simp add: ST_def)
      hence "prnt S0 z = Some w" using npz np_off by simp
      thus "e \<in> OFF" using zn e by (auto simp: OFF_def)
    next
      fix e assume "e \<in> OFF"
      then obtain z w where zn: "z \<notin> ST" and pz: "prnt S0 z = Some w" and e: "e = {z, w}"
        by (auto simp: OFF_def)
      have "z \<notin> s ` {0..k}" using zn by (simp add: ST_def)
      hence "NP z = Some w" using pz np_off by simp
      thus "e \<in> {{z, w} |z w. z \<notin> ST \<and> NP z = Some w}" using zn e by blast
    qed
    have "{{z, w} |z w. NP z = Some w}
        = {{z, w} |z w. z \<notin> ST \<and> NP z = Some w} \<union> {{z, w} |z w. z \<in> ST \<and> NP z = Some w}"
      by blast
    also have "\<dots> = OFF \<union> insert {ii, jj} SPINE" using offeq STedges_np by simp
    finally show ?thesis .
  qed
  have P2: "{{z, w} |z w. prnt S0 z = Some w} = OFF \<union> insert {pp, y0} SPINE"
  proof -
    have "{{z, w} |z w. prnt S0 z = Some w}
        = {{z, w} |z w. z \<notin> ST \<and> prnt S0 z = Some w} \<union> {{z, w} |z w. z \<in> ST \<and> prnt S0 z = Some w}"
      by blast
    also have "{{z, w} |z w. z \<notin> ST \<and> prnt S0 z = Some w} = OFF" by (simp add: OFF_def)
    finally show ?thesis using STedges_0 by simp
  qed
  have P3: "{pp, y0} \<notin> OFF"
  proof
    assume "{pp, y0} \<in> OFF"
    then obtain z w where zn: "z \<notin> ST" and pz: "prnt S0 z = Some w" and e: "{pp, y0} = {z, w}"
      by (auto simp: OFF_def)
    have "z \<noteq> pp" using zn ppST by auto
    hence "z = y0" using e by (metis empty_iff insert_iff)
    hence "prnt S0 y0 = Some w" using pz by simp
    have "w \<in> {pp, y0}" using e by blast
    hence "w = pp \<or> w = y0" by blast
    thus False
    proof
      assume "w = pp" thus False using \<open>prnt S0 y0 = Some w\<close> y0 no_2cycle[OF ps] by blast
    next
      assume "w = y0" thus False using \<open>prnt S0 y0 = Some w\<close> parent_spec_neq[OF ps] by blast
    qed
  qed
  have P4: "{pp, y0} \<notin> SPINE"
  proof
    assume "{pp, y0} \<in> SPINE"
    then obtain t where tk: "t < k" and e: "{pp, y0} = {s t, s (Suc t)}" by (auto simp: SPINE_def)
    have "pp \<in> {s t, s (Suc t)}" using e by blast
    hence "pp = s t \<or> pp = s (Suc t)" by blast
    thus False
    proof
      assume "pp = s t"
      hence "s k = s t" using skp by simp
      hence "k = t" using inj_sk tk by (auto simp: inj_on_eq_iff)
      thus False using tk by simp
    next
      assume ppst: "pp = s (Suc t)"
      have "prnt S0 (s t) = Some (s (Suc t))" by (rule ss.pathS[OF tk])
      hence "prnt S0 (s t) = Some pp" using ppst by simp
      moreover have "y0 = s t"
      proof -
        have y0ne: "y0 \<noteq> pp" using y0 parent_spec_neq[OF ps] by blast
        have "y0 \<in> {s t, s (Suc t)}" using e by blast
        thus ?thesis using ppst y0ne by blast
      qed
      ultimately have "prnt S0 y0 = Some pp" by simp
      thus False using y0 no_2cycle[OF ps] by blast
    qed
  qed
  have absNP: "abstract_arb (update_tree S0 ii jj pp jn) = {{z, w} |z w. NP z = Some w}"
    unfolding abstract_arb_def prnt_ut by simp
  have abs0: "abstract_arb S0 = {{z, w} |z w. prnt S0 z = Some w}"
    unfolding abstract_arb_def by simp
  have "abstract_arb (update_tree S0 ii jj pp jn) = OFF \<union> insert {ii, jj} SPINE"
    using absNP P1 by simp
  moreover have "abstract_arb S0 - {{pp, y0}} \<union> {{ii, jj}} = OFF \<union> insert {ii, jj} SPINE"
    using abs0 P2 P3 P4 by auto
  ultimately show ?thesis by simp
qed

lemma follow_edge_parent:
  assumes ps: "parent_spec T" and em: "(x, y) \<in> set (edges_of_vwalk (follow T u))"
  shows "T x = Some y"
proof -
  obtain i where ilen: "i < length (edges_of_vwalk (follow T u))"
    and ei: "edges_of_vwalk (follow T u) ! i = (x, y)"
    using em by (meson in_set_conv_nth)
  have si: "Suc i < length (follow T u)" using ilen by (simp add: edges_of_vwalk_length)
  have "edges_of_vwalk (follow T u) ! i = (follow T u ! i, follow T u ! Suc i)"
    by (rule edges_of_vwalk_index[OF si])
  hence xy: "x = follow T u ! i" "y = follow T u ! Suc i" using ei by auto
  have "T (follow T u ! i) = Some (follow T u ! Suc i)" by (rule follow_nth_Suc[OF ps si])
  thus ?thesis using xy by simp
qed

lemma abstract_reparent:
  assumes ps: "parent_spec T" and iy: "T i = Some y0"
  shows "{{z, w} |z w. (T(i \<mapsto> j)) z = Some w} = {{z, w} |z w. T z = Some w} - {{i, y0}} \<union> {{i, j}}"
proof (rule Set.set_eqI, rule iffI)
  fix e assume "e \<in> {{z, w} |z w. (T(i \<mapsto> j)) z = Some w}"
  then obtain z w where zw: "(T(i \<mapsto> j)) z = Some w" and e: "e = {z, w}" by blast
  show "e \<in> {{z, w} |z w. T z = Some w} - {{i, y0}} \<union> {{i, j}}"
  proof (cases "z = i")
    case True hence "e = {i, j}" using zw e by simp
    thus ?thesis by simp
  next
    case False
    hence tz: "T z = Some w" using zw by simp
    hence mem: "e \<in> {{z, w} |z w. T z = Some w}" using e by blast
    have "e \<noteq> {i, y0}"
    proof
      assume ei: "e = {i, y0}"
      have "z = y0" using ei e False by (metis empty_iff insert_iff)
      have "w = i" using ei e \<open>z = y0\<close> False by (metis doubleton_eq_iff)
      hence "T y0 = Some i" using tz \<open>z = y0\<close> by simp
      thus False using iy no_2cycle[OF ps] by blast
    qed
    thus ?thesis using mem by simp
  qed
next
  fix e assume "e \<in> {{z, w} |z w. T z = Some w} - {{i, y0}} \<union> {{i, j}}"
  then consider "e \<in> {{z, w} |z w. T z = Some w} \<and> e \<noteq> {i, y0}" | "e = {i, j}" by blast
  thus "e \<in> {{z, w} |z w. (T(i \<mapsto> j)) z = Some w}"
  proof cases
    case 1
    then obtain z w where tz: "T z = Some w" and e: "e = {z, w}" and ne: "e \<noteq> {i, y0}" by blast
    have "z \<noteq> i"
    proof
      assume "z = i"
      hence "w = y0" using tz iy by simp
      hence "e = {i, y0}" using e \<open>z = i\<close> by simp
      thus False using ne by simp
    qed
    hence "(T(i \<mapsto> j)) z = Some w" using tz by simp
    thus ?thesis using e by blast
  next
    case 2
    have "(T(i \<mapsto> j)) i = Some j" by simp
    thus ?thesis using 2 by blast
  qed
qed

lemma swap_edge_axiom2:
  assumes inv: "arb_invar r V S" and gp: "get_path_pair_impl S u v = (p1, p2)"
    and une: "u \<noteq> v"
    and wu: "walk_betw (abstract_arb S) u (p1 @ a # p3) r"
    and dist: "distinct (p1 @ a # p3)"
    and em: "(x, y) \<in> set (edges_of_vwalk (p1 @ [a]))"
    and uV: "u \<in> V" and vV: "v \<in> V"
  shows "abstract_arb (swap_edge_impl S x u v) = abstract_arb S - {{x, y}} \<union> {{u, v}}"
proof -
  have rinv: "rooted_arborescense_invar r V (prnt S)" using inv unfolding arb_invar_def by simp
  have ps: "parent_spec (prnt S)" by (rule rooted_arborescense_invar_parent_spec[OF rinv])
  have wfu: "p1 @ a # p3 = follow (prnt S) u" by (rule unique_walk_to_root[OF inv uV wu dist])
  define j where "j = join_of (prnt S) u v"
  have fu_split: "follow (prnt S) u = p1 @ follow (prnt S) j"
    using get_path_pair_impl_correct(1)[OF inv uV vV gp] by (simp add: j_def)
  have "p1 @ a # p3 = p1 @ follow (prnt S) j" using wfu fu_split by simp
  hence fj: "follow (prnt S) j = a # p3" by simp
  have aj: "a = j" using fj follow_hd_ps[OF ps] by (metis list.sel(1))
  have p1ne: "p1 \<noteq> []"
  proof (rule ccontr)
    assume "\<not> p1 \<noteq> []" hence "p1 = []" by simp
    hence "edges_of_vwalk (p1 @ [a]) = []" by simp
    thus False using em by simp
  qed
  have ev_dec: "edges_of_vwalk (p1 @ [a]) = edges_of_vwalk p1 @ [(last p1, a)]"
    using edges_of_vwalk_append_3[OF p1ne, of "[a]"] p1ne by simp
  have xp1: "x \<in> set p1"
  proof -
    from em ev_dec have "(x, y) \<in> set (edges_of_vwalk p1) \<or> (x, y) = (last p1, a)" by auto
    thus ?thesis
    proof
      assume "(x, y) \<in> set (edges_of_vwalk p1)" thus ?thesis using v_in_edge_in_vwalk by fast
    next
      assume "(x, y) = (last p1, a)" thus ?thesis using p1ne last_in_set by auto
    qed
  qed
  have xfu: "x \<in> set (follow (prnt S) u)"
  proof -
    have "x \<in> set (p1 @ a # p3)" using xp1 by simp
    thus ?thesis using wfu by simp
  qed
  have anotp1: "a \<notin> set p1" using dist by (auto simp: distinct_append)
  have xnej: "x \<noteq> j" using xp1 anotp1 aj by auto
  have jfx: "j \<in> set (follow (prnt S) x)"
  proof -
    from xp1 obtain A1 A2 where p1split: "p1 = A1 @ x # A2" by (meson split_list)
    have "follow (prnt S) u = A1 @ x # (A2 @ follow (prnt S) j)" using fu_split p1split by simp
    hence fx: "follow (prnt S) x = x # (A2 @ follow (prnt S) j)" using follow_append_ps[OF ps] by blast
    have "j \<in> set (follow (prnt S) j)"
      using follow_ne_ps[OF ps] follow_hd_ps[OF ps] by (metis hd_in_set)
    thus ?thesis using fx by simp
  qed
  have pxy: "prnt S x = Some y"
  proof -
    have "follow (prnt S) u = (p1 @ [a]) @ p3" using wfu by simp
    hence "edges_of_vwalk (follow (prnt S) u)
             = edges_of_vwalk (p1 @ [a]) @ edges_of_vwalk (last (p1 @ [a]) # p3)"
      using edges_of_vwalk_append_3[OF _, of "p1 @ [a]" p3] by simp
    hence "(x, y) \<in> set (edges_of_vwalk (follow (prnt S) u))" using em by auto
    thus ?thesis by (rule follow_edge_parent[OF ps])
  qed
  have jneq: "j = join_of (prnt S) u v" by (simp add: j_def)
  have swap_eq: "swap_edge_impl S x u v = update_tree S u v x j" by (simp add: swap_edge_impl_def j_def)
  obtain ss_s ss_k where SS: "stem_setup S r V u v x ss_k ss_s"
    using pivot_stem_setup[OF inv uV vV xfu jfx jneq xnej] by blast
  interpret ss: stem_setup S r V u v x ss_k ss_s by (rule SS)
  show ?thesis
  proof (cases "0 < ss_k")
    case True
    have "abstract_arb (update_tree S u v x j) = abstract_arb S - {{x, y}} \<union> {{u, v}}"
      by (rule abstract_edge_swap[OF SS True pxy])
    thus ?thesis using swap_eq by simp
  next
    case False
    hence k0: "ss_k = 0" by simp
    have ux: "u = x" using ss.path0 ss.pathk k0 by simp
    define Tx where "Tx = (prnt S)(x \<mapsto> v)"
    have movp: "prnt (update_tree S x v x j) = Tx" unfolding Tx_def by (rule ss.move_prnt)
    have "abstract_arb (update_tree S u v x j) = {{z, w} |z w. Tx z = Some w}"
      using movp ux by (simp add: abstract_arb_def)
    also have "\<dots> = {{z, w} |z w. prnt S z = Some w} - {{x, y}} \<union> {{x, v}}"
      unfolding Tx_def by (rule abstract_reparent[OF ps pxy])
    also have "\<dots> = abstract_arb S - {{x, y}} \<union> {{u, v}}"
      using ux by (simp add: abstract_arb_def)
    finally show ?thesis using swap_eq by simp
  qed
qed


text \<open>All nine axioms are now available; the interpretation exhibits the built initial tree as a
      concrete @{locale arborescense_adt}.\<close>

interpretation Sarb_adt: arborescense_adt Varb vcount "arb_invar vcount Varb"
    abstract_arb get_path_pair_impl swap_edge_impl
proof (unfold_locales, goal_cases)
  case 1 show ?case by (rule r_in_V)
next
  case (2 T) then show ?case by (rule graph_invar_abstract_arb)
next
  case (3 T x y) then show ?case by (rule general_axiom3)
next
  case (4 T) then show ?case by (rule Vs_abstract_arb)
next
  case (5 T p1 p2 u v) then show ?case by (rule get_path_pair_axiom1)
next
  case (6 T p1 p2 u v) then show ?case by (rule get_path_pair_axiom2)
next
  case (7 T p1 p2 p3 a u v x y) then show ?case by (rule swap_edge_axiom1)
next
  case (8 T p1 p2 p3 a u v x y) then show ?case by (rule swap_edge_axiom2)
qed


section \<open>Big-M potential arithmetic: the pot\_value\_plus/minus specifications\<close>

text \<open>The abstract potential/reduced-cost descriptor is the tagged pair \<open>pval\<close>, read as
      \<open>pval_abstract bigM p = of_mtag (fst p) * bigM + snd p\<close>.  With \<open>bigM\<close> chosen larger than
      \<open>6 * sum_list (map abs cost_list)\<close>, the ordinary parts of a potential (bounded by
      \<open>2 * sum_list (map abs cost_list)\<close>, invariant \<open>pv_invar\<close>) and of a reduced cost (bounded by
      \<open>3 * sum_list (map abs cost_list)\<close>, invariant \<open>rc_invar\<close>) are too small to disturb the big-M
      coefficient.  Under the network-simplex guard (\<open>good_pot_val\<close>: the resulting value is a signed
      cost sum over augmented edges touching the root \<open>vcount\<close> at most once), the big-M coefficient
      of the result stays in \<open>{- 1, 0, 1}\<close>, so the clamping \<open>tag_add\<close> / \<open>tag_sub\<close> act faithfully.
      These are exactly the spec-level obligations \<open>pot_value_plus_spec\<close> / \<open>pot_value_minus_spec\<close> of
      the locale \<open>network_simplex_spec\<close>.\<close>

lemma of_mtag_bounds: "- 2 \<le> of_mtag t \<and> of_mtag t \<le> 2"
  by (cases t) auto

lemma of_mtag_mtag_of: "- 2 \<le> i \<Longrightarrow> i \<le> 2 \<Longrightarrow> of_mtag (mtag_of i) = i"
  by (auto simp: mtag_of_def)

lemma len_fst_list_m: "length fst_list = m"
  using length_fst length_edges by simp

lemma len_snd_list_m: "length snd_list = m"
  using length_snd length_edges by simp

lemma real_fst_lt_vcount: "e < m \<Longrightarrow> fst_all ! e < vcount"
proof -
  assume e: "e < m"
  have "fst_list ! e \<in> set fst_list" using e len_fst_list_m by (metis nth_mem)
  hence "fst_list ! e \<in> set vs_list" using fst_snd_vs by auto
  thus ?thesis using vs_less_vcount e by (simp add: fst_all_real)
qed

lemma real_snd_lt_vcount: "e < m \<Longrightarrow> snd_all ! e < vcount"
proof -
  assume e: "e < m"
  have "snd_list ! e \<in> set snd_list" using e len_snd_list_m by (metis nth_mem)
  hence "snd_list ! e \<in> set vs_list" using fst_snd_vs by auto
  thus ?thesis using vs_less_vcount e by (simp add: snd_all_real)
qed

text \<open>For an augmented edge, touching the artificial root @{term vcount} is exactly being an
      artificial edge (index @{term "e \<ge> m"}).\<close>

lemma touches_root_iff:
  assumes "e < m + Kart"
  shows "(fst_all ! e = vcount \<or> snd_all ! e = vcount) \<longleftrightarrow> \<not> e < m"
proof
  assume "fst_all ! e = vcount \<or> snd_all ! e = vcount"
  thus "\<not> e < m" using real_fst_lt_vcount[of e] real_snd_lt_vcount[of e] by auto
next
  assume nlt: "\<not> e < m"
  then obtain k where k: "e = m + k" "k < Kart" using assms by (metis add.commute le_Suc_ex not_le nat_add_left_cancel_less add_diff_inverse_nat)
  have tok: "tail_edge_ok (build_tree acyc_flow) k" using k(2) tail_edge_ok_build_tree by simp
  then obtain subj where "subj < vcount"
      "ds_afst (build_tree acyc_flow) ! k = (if art_dir subj then subj else vcount)"
      "ds_asnd (build_tree acyc_flow) ! k = (if art_dir subj then vcount else subj)"
    unfolding tail_edge_ok_def by blast
  hence "fst_all ! e = vcount \<or> snd_all ! e = vcount"
    using k by (cases "art_dir subj") (auto simp: fst_all_art snd_all_art)
  thus "fst_all ! e = vcount \<or> snd_all ! e = vcount" .
qed

lemma cost_all_art': "m \<le> e \<Longrightarrow> e < m + Kart \<Longrightarrow> cost_all ! e = bigM"
  using cost_all_art[of "e - m"] by simp

lemma csum_split:
  assumes "S \<subseteq> {0..<m + Kart}"
  shows "(\<Sum>e\<in>S. cost_all ! e)
           = (\<Sum>e\<in>S \<inter> {0..<m}. h (cost_list ! e)) + bigM * real (card (S \<inter> {m..<m + Kart}))"
proof -
  have fin: "finite S" using assms by (simp add: finite_subset)
  let ?S1 = "S \<inter> {0..<m}" and ?S2 = "S \<inter> {m..<m + Kart}"
  have un: "S = ?S1 \<union> ?S2" using assms by auto
  have dj: "?S1 \<inter> ?S2 = {}" by auto
  have "(\<Sum>e\<in>S. cost_all ! e) = (\<Sum>e\<in>?S1. cost_all ! e) + (\<Sum>e\<in>?S2. cost_all ! e)"
    using fin dj by (subst un, subst sum.union_disjoint) auto
  moreover have "(\<Sum>e\<in>?S1. cost_all ! e) = (\<Sum>e\<in>?S1. h (cost_list ! e))"
    by (rule sum.cong) (auto simp: cost_all_real)
  moreover have "(\<Sum>e\<in>?S2. cost_all ! e) = (\<Sum>e\<in>?S2. bigM)"
    by (rule sum.cong) (auto simp: cost_all_art')
  ultimately show ?thesis by simp
qed

lemma sabs_eq: "sum_list (map abs cost_list) = (\<Sum>e\<in>{0..<m}. \<bar>cost_list ! e\<bar>)"
proof -
  have "sum_list (map abs cost_list) = (\<Sum>e = 0..<length (map abs cost_list). (map abs cost_list) ! e)"
    by (rule sum_list_sum_nth)
  also have "\<dots> = (\<Sum>e\<in>{0..<m}. \<bar>cost_list ! e\<bar>)"
    using len_fst_list_m length_cost length_fst by simp
  finally show ?thesis .
qed

lemma real_diff_bound:
  assumes "A \<subseteq> {0..<m}" "D \<subseteq> {0..<m}"
  shows "\<bar>(\<Sum>e\<in>A. cost_list ! e) - (\<Sum>e\<in>D. cost_list ! e)\<bar> \<le> sum_list (map abs cost_list)"
proof -
  have rA: "(\<Sum>e\<in>{0..<m}. if e\<in>A then cost_list ! e else 0) = (\<Sum>e\<in>A. cost_list ! e)"
  proof -
    have "(\<Sum>e\<in>{0..<m}. if e\<in>A then cost_list ! e else 0) = (\<Sum>e\<in>{0..<m} \<inter> A. cost_list ! e)"
      by (simp add: sum.inter_restrict)
    also have "{0..<m} \<inter> A = A" using assms(1) by (simp add: Int_absorb1)
    finally show ?thesis .
  qed
  have rD: "(\<Sum>e\<in>{0..<m}. if e\<in>D then cost_list ! e else 0) = (\<Sum>e\<in>D. cost_list ! e)"
  proof -
    have "(\<Sum>e\<in>{0..<m}. if e\<in>D then cost_list ! e else 0) = (\<Sum>e\<in>{0..<m} \<inter> D. cost_list ! e)"
      by (simp add: sum.inter_restrict)
    also have "{0..<m} \<inter> D = D" using assms(2) by (simp add: Int_absorb1)
    finally show ?thesis .
  qed
  have "\<bar>(\<Sum>e\<in>A. cost_list ! e) - (\<Sum>e\<in>D. cost_list ! e)\<bar>
        = \<bar>(\<Sum>e\<in>{0..<m}. (if e\<in>A then cost_list ! e else 0) - (if e\<in>D then cost_list ! e else 0))\<bar>"
    by (simp add: rA[symmetric] rD[symmetric] sum_subtractf)
  also have "\<dots> \<le> (\<Sum>e\<in>{0..<m}. \<bar>(if e\<in>A then cost_list ! e else 0) - (if e\<in>D then cost_list ! e else 0)\<bar>)"
    by (rule sum_abs)
  also have "\<dots> \<le> (\<Sum>e\<in>{0..<m}. \<bar>cost_list ! e\<bar>)"
    by (rule sum_mono) auto
  also have "\<dots> = sum_list (map abs cost_list)" by (simp add: sabs_eq)
  finally show ?thesis .
qed

lemma root_touch_set_eq:
  assumes "A \<subseteq> {0..<m + Kart}" "D \<subseteq> {0..<m + Kart}"
  shows "{e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} = (A \<union> D) \<inter> {m..<m + Kart}"
proof -
  have "\<And>e. e \<in> A \<union> D \<Longrightarrow> ((fst_all ! e = vcount \<or> snd_all ! e = vcount) \<longleftrightarrow> e \<in> {m..<m + Kart})"
  proof -
    fix e assume e: "e \<in> A \<union> D"
    hence lt: "e < m + Kart" using assms by auto
    show "((fst_all ! e = vcount \<or> snd_all ! e = vcount) \<longleftrightarrow> e \<in> {m..<m + Kart})"
      using touches_root_iff[OF lt] lt by auto
  qed
  thus ?thesis by blast
qed

lemma h_abs: "h \<bar>a\<bar> = \<bar>h a\<bar>"
  by (cases "0 \<le> a") (auto simp: abs_of_nonneg abs_of_nonpos)

lemma h_of_nat [simp]: "h (of_nat nn) = of_nat nn"
  by (induction nn) (simp_all add: h_add)

lemma h_numeral [simp]: "h (numeral k) = numeral k"
  by (metis h_of_nat of_nat_numeral)

lemma cost_decompose:
  assumes A: "A \<subseteq> {0..<m + Kart}" and D: "D \<subseteq> {0..<m + Kart}"
    and rt: "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1"
  shows "\<exists>\<epsilon> R. \<epsilon> \<in> {- 1, 0, 1} \<and> \<bar>R\<bar> \<le> h (sum_list (map abs cost_list))
          \<and> (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e) = real_of_int \<epsilon> * bigM + R"
proof -
  let ?art = "{m..<m + Kart}"
  have finU: "finite ((A \<union> D) \<inter> ?art)" by simp
  have card_un: "card ((A \<union> D) \<inter> ?art) \<le> 1" using rt root_touch_set_eq[OF A D] by simp
  have Asub: "A \<inter> ?art \<subseteq> (A \<union> D) \<inter> ?art" and Dsub: "D \<inter> ?art \<subseteq> (A \<union> D) \<inter> ?art" by auto
  have cA1: "card (A \<inter> ?art) \<le> 1" using card_mono[OF finU Asub] card_un by simp
  have cD1: "card (D \<inter> ?art) \<le> 1" using card_mono[OF finU Dsub] card_un by simp
  define \<epsilon> where "\<epsilon> = int (card (A \<inter> ?art)) - int (card (D \<inter> ?art))"
  define R where "R = (\<Sum>e\<in>A \<inter> {0..<m}. h (cost_list ! e)) - (\<Sum>e\<in>D \<inter> {0..<m}. h (cost_list ! e))"
  have eps: "\<epsilon> \<in> {- 1, 0, 1}" using cA1 cD1 unfolding \<epsilon>_def by auto
  have Rbnd: "\<bar>R\<bar> \<le> h (sum_list (map abs cost_list))"
  proof -
    let ?SA = "(\<Sum>e\<in>A \<inter> {0..<m}. cost_list ! e)" and ?SD = "(\<Sum>e\<in>D \<inter> {0..<m}. cost_list ! e)"
    have "R = h ?SA - h ?SD" by (simp add: R_def h_sum)
    hence "\<bar>R\<bar> = h \<bar>?SA - ?SD\<bar>" by (simp add: h_abs[symmetric] flip: h_diff)
    also have "\<dots> \<le> h (sum_list (map abs cost_list))"
      using real_diff_bound[of "A \<inter> {0..<m}" "D \<inter> {0..<m}"] by simp
    finally show ?thesis .
  qed
  have "(\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)
        = ((\<Sum>e\<in>A \<inter> {0..<m}. h (cost_list ! e)) + bigM * real (card (A \<inter> ?art)))
          - ((\<Sum>e\<in>D \<inter> {0..<m}. h (cost_list ! e)) + bigM * real (card (D \<inter> ?art)))"
    by (simp add: csum_split[OF A] csum_split[OF D])
  also have "\<dots> = R + bigM * (real (card (A \<inter> ?art)) - real (card (D \<inter> ?art)))"
    by (simp add: R_def algebra_simps)
  also have "\<dots> = real_of_int \<epsilon> * bigM + R"
    unfolding \<epsilon>_def by (simp add: algebra_simps)
  finally show ?thesis using eps Rbnd by blast
qed

definition pv_invar :: "mtag \<times> 'n \<Rightarrow> bool" where
  "pv_invar p \<longleftrightarrow> \<bar>snd p\<bar> \<le> 2 * sum_list (map abs cost_list)"

definition rc_invar :: "mtag \<times> 'n \<Rightarrow> bool" where
  "rc_invar g \<longleftrightarrow> \<bar>snd g\<bar> \<le> 3 * sum_list (map abs cost_list)"

lemma sabs_nonneg: "0 \<le> sum_list (map abs cost_list)"
  by (rule sum_list_nonneg) auto

lemma bigM_pos: "bigM > 0"
proof -
  have hn: "0 \<le> h (sum_list (map abs cost_list))" using sabs_nonneg by simp
  have "0 < 6 * h (sum_list (map abs cost_list)) + 1" using hn by linarith
  thus ?thesis by (simp add: bigM_def)
qed

lemma h_pv_bound:
  assumes "pv_invar p" shows "\<bar>h (snd p)\<bar> \<le> 2 * h (sum_list (map abs cost_list))"
proof -
  have "\<bar>snd p\<bar> \<le> 2 * sum_list (map abs cost_list)" using assms by (simp add: pv_invar_def)
  hence "h \<bar>snd p\<bar> \<le> h (2 * sum_list (map abs cost_list))" by (rule h_mono)
  thus ?thesis by (simp add: h_abs h_mult)
qed

lemma h_rc_bound:
  assumes "rc_invar g" shows "\<bar>h (snd g)\<bar> \<le> 3 * h (sum_list (map abs cost_list))"
proof -
  have "\<bar>snd g\<bar> \<le> 3 * sum_list (map abs cost_list)" using assms by (simp add: rc_invar_def)
  hence "h \<bar>snd g\<bar> \<le> h (3 * sum_list (map abs cost_list))" by (rule h_mono)
  thus ?thesis by (simp add: h_abs h_mult)
qed

lemma pot_plus_faithful:
  assumes pv: "pv_invar p" and rc: "rc_invar g"
    and gd: "\<exists>A D. A \<subseteq> {0..<m + Kart} \<and> D \<subseteq> {0..<m + Kart}
              \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1
              \<and> pval_abstract bigM p + pval_abstract bigM g
                  = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)"
  shows "pval_abstract bigM (pval_plus p g) = pval_abstract bigM p + pval_abstract bigM g
         \<and> pv_invar (pval_plus p g)"
proof -
  define sabs where "sabs = h (sum_list (map abs cost_list))"
  have sabs0: "0 \<le> sabs" using sabs_nonneg by (simp add: sabs_def)
  have bM: "bigM = 6 * sabs + 1" by (simp add: bigM_def sabs_def)
  obtain A D where AD: "A \<subseteq> {0..<m + Kart}" "D \<subseteq> {0..<m + Kart}"
      "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1"
      "pval_abstract bigM p + pval_abstract bigM g = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)"
    using gd by blast
  obtain \<epsilon> R where dec: "\<epsilon> \<in> {- 1, 0, 1}" "\<bar>R\<bar> \<le> sabs"
      "(\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e) = real_of_int \<epsilon> * bigM + R"
    using cost_decompose[OF AD(1) AD(2) AD(3)] by (auto simp: sabs_def)
  define cp where "cp = of_mtag (fst p)"
  define cg where "cg = of_mtag (fst g)"
  have absp: "pval_abstract bigM p = real_of_int cp * bigM + h (snd p)" by (simp add: pval_abstract_def cp_def)
  have absg: "pval_abstract bigM g = real_of_int cg * bigM + h (snd g)" by (simp add: pval_abstract_def cg_def)
  have pb: "\<bar>h (snd p)\<bar> \<le> 2 * sabs" using h_pv_bound[OF pv] by (simp add: sabs_def)
  have gb: "\<bar>h (snd g)\<bar> \<le> 3 * sabs" using h_rc_bound[OF rc] by (simp add: sabs_def)
  have key: "real_of_int (cp + cg) * bigM + (h (snd p) + h (snd g)) = real_of_int \<epsilon> * bigM + R"
    using AD(4) dec(3) absp absg by (simp add: algebra_simps)
  hence eqn: "real_of_int (cp + cg - \<epsilon>) * bigM = R - (h (snd p) + h (snd g))"
    by (simp add: algebra_simps)
  have bnd: "\<bar>R - (h (snd p) + h (snd g))\<bar> < bigM"
  proof -
    have "\<bar>R - (h (snd p) + h (snd g))\<bar> \<le> \<bar>R\<bar> + \<bar>h (snd p)\<bar> + \<bar>h (snd g)\<bar>" by simp
    also have "\<dots> \<le> sabs + 2 * sabs + 3 * sabs" using dec(2) pb gb by linarith
    also have "\<dots> < bigM" using bM by simp
    finally show ?thesis .
  qed
  have "\<bar>real_of_int (cp + cg - \<epsilon>)\<bar> * bigM < bigM" using eqn bnd by (simp add: abs_mult)
  hence lt1: "\<bar>real_of_int (cp + cg - \<epsilon>)\<bar> < 1" using bigM_pos by simp
  have n0: "cp + cg - \<epsilon> = 0"
  proof -
    have "real_of_int \<bar>cp + cg - \<epsilon>\<bar> < 1" using lt1 by (simp add: of_int_abs)
    hence "\<bar>cp + cg - \<epsilon>\<bar> < 1" by (metis of_int_1 of_int_less_iff)
    thus ?thesis by linarith
  qed
  hence cpcg: "cp + cg = \<epsilon>" by simp
  have Req: "R = h (snd p) + h (snd g)" using eqn n0 by simp
  have rng: "- 2 \<le> cp + cg \<and> cp + cg \<le> 2" using dec(1) cpcg by auto
  have tag: "of_mtag (tag_add (fst p) (fst g)) = cp + cg"
    unfolding tag_add_def cp_def cg_def using rng by (simp add: of_mtag_mtag_of cp_def cg_def)
  have fst_eq: "pval_abstract bigM (pval_plus p g) = real_of_int (cp + cg) * bigM + h (snd p + snd g)"
    by (simp add: pval_abstract_def pval_plus_def tag cp_def cg_def)
  have faith: "pval_abstract bigM (pval_plus p g) = pval_abstract bigM p + pval_abstract bigM g"
    using fst_eq absp absg by (simp add: algebra_simps h_add)
  have inv: "pv_invar (pval_plus p g)"
  proof -
    have "\<bar>h (snd p + snd g)\<bar> \<le> sabs" using Req dec(2) by (simp add: h_add)
    hence "\<bar>snd p + snd g\<bar> \<le> sum_list (map abs cost_list)" by (simp add: h_abs[symmetric] sabs_def)
    thus ?thesis using sabs_nonneg by (simp add: pv_invar_def pval_plus_def)
  qed
  show ?thesis using faith inv by blast
qed

lemma pot_minus_faithful:
  assumes pv: "pv_invar p" and rc: "rc_invar g"
    and gd: "\<exists>A D. A \<subseteq> {0..<m + Kart} \<and> D \<subseteq> {0..<m + Kart}
              \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1
              \<and> pval_abstract bigM p - pval_abstract bigM g
                  = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)"
  shows "pval_abstract bigM (pval_minus p g) = pval_abstract bigM p - pval_abstract bigM g
         \<and> pv_invar (pval_minus p g)"
proof -
  define sabs where "sabs = h (sum_list (map abs cost_list))"
  have sabs0: "0 \<le> sabs" using sabs_nonneg by (simp add: sabs_def)
  have bM: "bigM = 6 * sabs + 1" by (simp add: bigM_def sabs_def)
  obtain A D where AD: "A \<subseteq> {0..<m + Kart}" "D \<subseteq> {0..<m + Kart}"
      "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1"
      "pval_abstract bigM p - pval_abstract bigM g = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)"
    using gd by blast
  obtain \<epsilon> R where dec: "\<epsilon> \<in> {- 1, 0, 1}" "\<bar>R\<bar> \<le> sabs"
      "(\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e) = real_of_int \<epsilon> * bigM + R"
    using cost_decompose[OF AD(1) AD(2) AD(3)] by (auto simp: sabs_def)
  define cp where "cp = of_mtag (fst p)"
  define cg where "cg = of_mtag (fst g)"
  have absp: "pval_abstract bigM p = real_of_int cp * bigM + h (snd p)" by (simp add: pval_abstract_def cp_def)
  have absg: "pval_abstract bigM g = real_of_int cg * bigM + h (snd g)" by (simp add: pval_abstract_def cg_def)
  have pb: "\<bar>h (snd p)\<bar> \<le> 2 * sabs" using h_pv_bound[OF pv] by (simp add: sabs_def)
  have gb: "\<bar>h (snd g)\<bar> \<le> 3 * sabs" using h_rc_bound[OF rc] by (simp add: sabs_def)
  have key: "real_of_int (cp - cg) * bigM + (h (snd p) - h (snd g)) = real_of_int \<epsilon> * bigM + R"
    using AD(4) dec(3) absp absg by (simp add: algebra_simps)
  hence eqn: "real_of_int (cp - cg - \<epsilon>) * bigM = R - (h (snd p) - h (snd g))"
    by (simp add: algebra_simps)
  have bnd: "\<bar>R - (h (snd p) - h (snd g))\<bar> < bigM"
  proof -
    have "\<bar>R - (h (snd p) - h (snd g))\<bar> \<le> \<bar>R\<bar> + \<bar>h (snd p)\<bar> + \<bar>h (snd g)\<bar>" by simp
    also have "\<dots> \<le> sabs + 2 * sabs + 3 * sabs" using dec(2) pb gb by linarith
    also have "\<dots> < bigM" using bM by simp
    finally show ?thesis .
  qed
  have "\<bar>real_of_int (cp - cg - \<epsilon>)\<bar> * bigM < bigM" using eqn bnd by (simp add: abs_mult)
  hence lt1: "\<bar>real_of_int (cp - cg - \<epsilon>)\<bar> < 1" using bigM_pos by simp
  have n0: "cp - cg - \<epsilon> = 0"
  proof -
    have "real_of_int \<bar>cp - cg - \<epsilon>\<bar> < 1" using lt1 by (simp add: of_int_abs)
    hence "\<bar>cp - cg - \<epsilon>\<bar> < 1" by (metis of_int_1 of_int_less_iff)
    thus ?thesis by linarith
  qed
  hence cpcg: "cp - cg = \<epsilon>" by simp
  have Req: "R = h (snd p) - h (snd g)" using eqn n0 by simp
  have rng: "- 2 \<le> cp - cg \<and> cp - cg \<le> 2" using dec(1) cpcg by auto
  have tag: "of_mtag (tag_sub (fst p) (fst g)) = cp - cg"
    unfolding tag_sub_def cp_def cg_def using rng by (simp add: of_mtag_mtag_of cp_def cg_def)
  have fst_eq: "pval_abstract bigM (pval_minus p g) = real_of_int (cp - cg) * bigM + h (snd p - snd g)"
    by (simp add: pval_abstract_def pval_minus_def tag cp_def cg_def)
  have faith: "pval_abstract bigM (pval_minus p g) = pval_abstract bigM p - pval_abstract bigM g"
    using fst_eq absp absg by (simp add: algebra_simps)
  have inv: "pv_invar (pval_minus p g)"
  proof -
    have "\<bar>h (snd p - snd g)\<bar> \<le> sabs" using Req dec(2) by simp
    hence "\<bar>snd p - snd g\<bar> \<le> sum_list (map abs cost_list)" by (simp add: h_abs[symmetric] sabs_def flip: h_diff)
    thus ?thesis using sabs_nonneg by (simp add: pv_invar_def pval_minus_def)
  qed
  show ?thesis using faith inv by blast
qed


text \<open>Design-notes obligation 11 (init\_pot\_fits), interior case: every interior tree vertex's stored
      parent edge is a real free edge whose reduced cost @{term \<open>\<c> e + \<pi>(fst e) - \<pi>(snd e)\<close>} is
      \<^emph>\<open>zero\<close> in the abstract.  This follows directly from the potential recursion @{thm build_tree_pot}
      (the parent's potential plus the @{term M_0}-tagged signed edge cost), so the increment is
      coefficient-0 and hence faithful (\<open>pval_plus_M0\<close>); the two orientations cancel the cost.\<close>

lemma len_pot_bt: "length (ds_pot (build_tree acyc_flow)) = Suc vcount" using build_tree_inv by (simp add: dfs_inv_def dfs_sized_def)

lemma plook_pot: "v < Suc vcount \<Longrightarrow> nth (ds_pot (build_tree acyc_flow)) v = ds_pot (build_tree acyc_flow) ! v" by simp

lemma pval_plus_M0: "pval_abstract bigM (pval_plus x (M_0, s)) = pval_abstract bigM x + h s"
proof -
  have "of_mtag (tag_add (fst x) M_0) = of_mtag (fst x)" unfolding tag_add_def using of_mtag_bounds[of "fst x"] by (simp add: of_mtag_mtag_of)
  thus ?thesis by (simp add: pval_abstract_def pval_plus_def h_add)
qed

lemma build_tree_interior_rc_zero:
  assumes w: "w < vcount" "ds_seen (build_tree acyc_flow) ! w" "ds_prnt (build_tree acyc_flow) ! w < vcount"
  shows "cost_all ! (ds_par (build_tree acyc_flow) ! w) + pval_abstract bigM (nth (ds_pot (build_tree acyc_flow)) (fst_all ! (ds_par (build_tree acyc_flow) ! w))) - pval_abstract bigM (nth (ds_pot (build_tree acyc_flow)) (snd_all ! (ds_par (build_tree acyc_flow) ! w))) = 0"
proof -
  define par where "par = ds_par (build_tree acyc_flow) ! w"
  define prnt where "prnt = ds_prnt (build_tree acyc_flow) ! w"
  define pott where "pott = ds_pot (build_tree acyc_flow)"
  have prntv: "prnt < vcount" using w(3) by (simp add: prnt_def)
  note bpe = build_tree_par_edge[OF w, folded par_def prnt_def]
  have pe1: "par < m" by (rule bpe[THEN conjunct1])
  have pe4: "fst_list ! par = (if ds_dir (build_tree acyc_flow) ! w then w else prnt)" by (rule bpe[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1])
  have pe5: "snd_list ! par = (if ds_dir (build_tree acyc_flow) ! w then prnt else w)" by (rule bpe[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2])
  have wne: "w \<noteq> prnt"
  proof
    assume eq: "w = prnt"
    have "Sprnt w = Some prnt" using w(1) w(2) by (simp add: Sprnt_def Vseen_def prnt_def)
    hence "(w, prnt) \<in> pstep (build_tree acyc_flow)" by (simp add: pstep_eq_Sprnt)
    thus False using eq pstep_acyclic by (metis acyclic_def trancl.r_into_trancl)
  qed
  have cst: "cost_all ! par = h (cost_list ! par)" using pe1 by (simp add: cost_all_real)
  have fa: "fst_all ! par = fst_list ! par" and sa: "snd_all ! par = snd_list ! par" using pe1 by (simp_all add: fst_all_real snd_all_real)
  note potw = build_tree_pot[OF w, folded par_def prnt_def pott_def]
  have absw: "pval_abstract bigM (pott ! w) = pval_abstract bigM (pott ! prnt) + h (if prnt = fst_list ! par then cost_list ! par else - cost_list ! par)"
    by (metis potw pval_plus_M0)
  have lw: "nth pott w = pott ! w" using plook_pot[of w, folded pott_def] w(1) by simp
  have lp: "nth pott prnt = pott ! prnt" using plook_pot[of prnt, folded pott_def] prntv by simp
  show ?thesis
  proof (cases "ds_dir (build_tree acyc_flow) ! w")
    case True
    have f: "fst_all ! par = w" and s: "snd_all ! par = prnt" using pe4 pe5 True fa sa by simp_all
    have "prnt \<noteq> fst_list ! par" using pe4 True wne by simp
    hence "pval_abstract bigM (pott ! w) = pval_abstract bigM (pott ! prnt) - h (cost_list ! par)" using absw by simp
    thus ?thesis using cst f s lw lp by (simp add: par_def pott_def)
  next
    case False
    have f: "fst_all ! par = prnt" and s: "snd_all ! par = w" using pe4 pe5 False fa sa by simp_all
    have "prnt = fst_list ! par" using pe4 False by simp
    hence "pval_abstract bigM (pott ! w) = pval_abstract bigM (pott ! prnt) + h (cost_list ! par)" using absw by simp
    thus ?thesis using cst f s lw lp by (simp add: par_def pott_def)
  qed
qed


text \<open>Obligation 11 (init\_pot\_fits), component-root case: the parent edge of a component root @{term c}
      (\<open>prnt = vcount\<close>) is the \<^emph>\<open>artificial\<close> edge @{term \<open>ds_par (build_tree acyc_flow) ! c = m + k\<close>} joining @{term c}
      to the root, with cost @{term bigM}, and @{term c}'s potential is the seed \<open>\<plusminus> bigM\<close>
      (\<open>pval_negM\<close>/\<open>pval_M\<close>) so that the big-\<open>M\<close> terms cancel and the reduced cost is zero.  The three
      hypotheses (seed value, and the artificial edge realising \<open>c \<leftrightarrow> vcount\<close> per @{term \<open>art_dir c\<close>})
      are exactly what @{const open_tree_component} writes at the seed and what a carried
      \<open>comproot_inv\<close> DFS invariant preserves (mirror of \<open>pot_inv\<close>/\<open>par_edge_inv acyc_flow\<close>, interior-only).\<close>

lemma build_tree_comproot_rc_zero:
  assumes c: "c < vcount"
    and seed: "ds_pot (build_tree acyc_flow) ! c = (if art_dir c then pval_negM else pval_M)"
    and pfa: "ds_par (build_tree acyc_flow) ! c = m + k" and kK: "k < Kart"
    and afst: "ds_afst (build_tree acyc_flow) ! k = (if art_dir c then c else vcount)"
    and asnd: "ds_asnd (build_tree acyc_flow) ! k = (if art_dir c then vcount else c)"
  shows "cost_all ! (ds_par (build_tree acyc_flow) ! c) + pval_abstract bigM (nth (ds_pot (build_tree acyc_flow)) (fst_all ! (ds_par (build_tree acyc_flow) ! c))) - pval_abstract bigM (nth (ds_pot (build_tree acyc_flow)) (snd_all ! (ds_par (build_tree acyc_flow) ! c))) = 0"
proof -
  have cost: "cost_all ! (ds_par (build_tree acyc_flow) ! c) = bigM" using pfa kK by (simp add: cost_all_art')
  have fst_eq: "fst_all ! (ds_par (build_tree acyc_flow) ! c) = (if art_dir c then c else vcount)" using pfa kK afst by (simp add: fst_all_art)
  have snd_eq: "snd_all ! (ds_par (build_tree acyc_flow) ! c) = (if art_dir c then vcount else c)" using pfa kK asnd by (simp add: snd_all_art)
  have pc: "nth (ds_pot (build_tree acyc_flow)) c = (if art_dir c then pval_negM else pval_M)"
    by (rule seed)
  have pv: "nth (ds_pot (build_tree acyc_flow)) vcount = pval_zero"
    by (rule build_tree_root_pot)
  show ?thesis
  proof (cases "art_dir c")
    case True
    have "nth (ds_pot (build_tree acyc_flow)) (fst_all ! (ds_par (build_tree acyc_flow) ! c)) = pval_negM" using fst_eq pc True by simp
    moreover have "nth (ds_pot (build_tree acyc_flow)) (snd_all ! (ds_par (build_tree acyc_flow) ! c)) = pval_zero" using snd_eq pv True by simp
    ultimately show ?thesis using cost by (simp add: pval_abstract_def pval_negM_def pval_zero_def)
  next
    case False
    have "nth (ds_pot (build_tree acyc_flow)) (fst_all ! (ds_par (build_tree acyc_flow) ! c)) = pval_zero" using fst_eq pv False by simp
    moreover have "nth (ds_pot (build_tree acyc_flow)) (snd_all ! (ds_par (build_tree acyc_flow) ! c)) = pval_M" using snd_eq pc False by simp
    ultimately show ?thesis using cost by (simp add: pval_abstract_def pval_M_def pval_zero_def)
  qed
qed

subsection \<open>Obligation 11 (init\_pot\_fits): reduced cost 0 on every tree edge\<close>

text \<open>The interior case (@{thm build_tree_interior_rc_zero}) and the component-root case
      (@{thm build_tree_comproot_rc_zero}) above are now combined into \<open>build_tree_rc_zero\<close>,
      the unconditional statement that \<^emph>\<open>every\<close> seen non-root vertex's parent edge has zero
      reduced cost. The five hypotheses of @{thm build_tree_comproot_rc_zero} are discharged by a
      carried DFS invariant \<open>comproot_inv\<close>: at each @{const open_tree_component} the new
      component root @{term c} gets @{term \<open>ds_par (build_tree acyc_flow) ! c = m + k\<close>} pointing at its freshly
      emitted artificial edge @{term k} (subject @{term c}) and the seed potential \<open>\<minusplus> bigM\<close>;
      every later step frames those fields (@{const build_dfs} freezes seen vertices' @{const ds_par}
      / @{const ds_pot} / @{const ds_prnt} and never creates a new component root -- \<open>build_dfs_cr\<close>).\<close>


lemma bd_upd1_cr:
  assumes inv: "dfs_inv fl s" and c: "bd_call1_conds fl s" and x: "x < vcount"
      and sx: "ds_seen (bd_upd1 fl s) ! x" and px: "ds_prnt (bd_upd1 fl s) ! x = vcount"
  shows "ds_seen s ! x \<and> ds_prnt s ! x = vcount
         \<and> ds_par (bd_upd1 fl s) ! x = ds_par s ! x \<and> ds_pot (bd_upd1 fl s) ! x = ds_pot s ! x"
proof -
  have wf: "dfs_wf fl s" and sz: "dfs_sized s" using inv by (auto simp: dfs_inv_def)
  obtain v rest e w c' where stk: "ds_stk s = v # rest" and wlt: "w < vcount"
    and up: "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr> else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (rule bd_upd1_eq[OF wf c])
  have vlt: "v < vcount" using stkverts_props[OF wf, of v] stk by (simp add: stkverts_def)
  have lenp: "length (ds_prnt s) = Suc vcount" using sz by (simp add: dfs_sized_def)
  show ?thesis
  proof (cases "ds_seen s ! w")
    case True thus ?thesis using up sx px by simp
  next
    case False
    have up': "bd_upd1 fl s = dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e" using up False by simp
    have xnw: "x \<noteq> w"
    proof
      assume "x = w"
      moreover have "ds_prnt (bd_upd1 fl s) ! w = v" using up' wlt lenp by (simp add: dfs_discover_def dfs_push_def Let_def)
      ultimately show False using px vlt by simp
    qed
    thus ?thesis using up' sx px by (simp add: dfs_discover_def dfs_push_def Let_def)
  qed
qed

lemma bd_upd2_cr:
  assumes inv: "dfs_inv fl s" and c: "bd_call2_conds fl s" and x: "x < vcount"
      and sx: "ds_seen (bd_upd2 fl s) ! x" and px: "ds_prnt (bd_upd2 fl s) ! x = vcount"
  shows "ds_seen s ! x \<and> ds_prnt s ! x = vcount
         \<and> ds_par (bd_upd2 fl s) ! x = ds_par s ! x \<and> ds_pot (bd_upd2 fl s) ! x = ds_pot s ! x"
proof -
  have wf: "dfs_wf fl s" and sz: "dfs_sized s" using inv by (auto simp: dfs_inv_def)
  obtain v rest e w c' where stk: "ds_stk s = v # rest" and wlt: "w < vcount"
    and up: "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr> else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    by (rule bd_upd2_eq[OF wf c])
  have vlt: "v < vcount" using stkverts_props[OF wf, of v] stk by (simp add: stkverts_def)
  have lenp: "length (ds_prnt s) = Suc vcount" using sz by (simp add: dfs_sized_def)
  show ?thesis
  proof (cases "ds_seen s ! w")
    case True thus ?thesis using up sx px by simp
  next
    case False
    have up': "bd_upd2 fl s = dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e" using up False by simp
    have xnw: "x \<noteq> w"
    proof
      assume "x = w"
      moreover have "ds_prnt (bd_upd2 fl s) ! w = v" using up' wlt lenp by (simp add: dfs_discover_def dfs_push_def Let_def)
      ultimately show False using px vlt by simp
    qed
    thus ?thesis using up' sx px by (simp add: dfs_discover_def dfs_push_def Let_def)
  qed
qed

lemma bd_upd3_cr:
  assumes c: "bd_call3_conds fl s"
      and sx: "ds_seen (bd_upd3 s) ! x" and px: "ds_prnt (bd_upd3 s) ! x = vcount"
  shows "ds_seen s ! x \<and> ds_prnt s ! x = vcount
         \<and> ds_par (bd_upd3 s) ! x = ds_par s ! x \<and> ds_pot (bd_upd3 s) ! x = ds_pot s ! x"
proof -
  obtain v rest where "bd_upd3 s = dfs_finish s v rest" by (rule bd_upd3_eq[OF c])
  thus ?thesis using sx px by (simp add: dfs_finish_def Let_def)
qed

lemma build_dfs_cr:
  assumes dom: "build_dfs_dom (fl, s)" and invs0: "dfs_inv fl s" and xlt: "x < vcount"
      and sb0: "ds_seen (build_dfs fl s) ! x" and pb0: "ds_prnt (build_dfs fl s) ! x = vcount"
  shows "ds_seen s ! x \<and> ds_prnt s ! x = vcount
         \<and> ds_par (build_dfs fl s) ! x = ds_par s ! x \<and> ds_pot (build_dfs fl s) ! x = ds_pot s ! x"
proof -
  have "dfs_inv fl s \<longrightarrow> ds_seen (build_dfs fl s) ! x \<longrightarrow> ds_prnt (build_dfs fl s) ! x = vcount
         \<longrightarrow> (ds_seen s ! x \<and> ds_prnt s ! x = vcount
              \<and> ds_par (build_dfs fl s) ! x = ds_par s ! x \<and> ds_pot (build_dfs fl s) ! x = ds_pot s ! x)"
  proof (induct rule: bd_induct[OF dom])
    case IH: (1 fl s)
    show ?case
    proof (intro impI)
      assume invs: "dfs_inv fl s" and sb: "ds_seen (build_dfs fl s) ! x" and pb: "ds_prnt (build_dfs fl s) ! x = vcount"
      show "ds_seen s ! x \<and> ds_prnt s ! x = vcount
            \<and> ds_par (build_dfs fl s) ! x = ds_par s ! x \<and> ds_pot (build_dfs fl s) ! x = ds_pot s ! x"
      proof (rule bd_cases[where s=s and fl=fl])
        assume c: "bd_call1_conds fl s"
        have step: "build_dfs fl s = build_dfs fl (bd_upd1 fl s)" using bd_simps(1)[OF IH(1) c] .
        have inv1: "dfs_inv fl (bd_upd1 fl s)" using bd_upd1_inv[OF invs c] .
        have s1: "ds_seen (build_dfs fl (bd_upd1 fl s)) ! x" using sb step by simp
        have p1: "ds_prnt (build_dfs fl (bd_upd1 fl s)) ! x = vcount" using pb step by simp
        have Q1: "ds_seen (bd_upd1 fl s) ! x \<and> ds_prnt (bd_upd1 fl s) ! x = vcount
                 \<and> ds_par (build_dfs fl (bd_upd1 fl s)) ! x = ds_par (bd_upd1 fl s) ! x
                 \<and> ds_pot (build_dfs fl (bd_upd1 fl s)) ! x = ds_pot (bd_upd1 fl s) ! x"
          using IH(2)[OF c] inv1 s1 p1 by blast
        have St: "ds_seen s ! x \<and> ds_prnt s ! x = vcount
                 \<and> ds_par (bd_upd1 fl s) ! x = ds_par s ! x \<and> ds_pot (bd_upd1 fl s) ! x = ds_pot s ! x"
          using bd_upd1_cr[OF invs c xlt] Q1 by blast
        show ?thesis using Q1 St step by simp
      next
        assume c: "bd_call2_conds fl s"
        have step: "build_dfs fl s = build_dfs fl (bd_upd2 fl s)" using bd_simps(2)[OF IH(1) c] .
        have inv1: "dfs_inv fl (bd_upd2 fl s)" using bd_upd2_inv[OF invs c] .
        have s1: "ds_seen (build_dfs fl (bd_upd2 fl s)) ! x" using sb step by simp
        have p1: "ds_prnt (build_dfs fl (bd_upd2 fl s)) ! x = vcount" using pb step by simp
        have Q1: "ds_seen (bd_upd2 fl s) ! x \<and> ds_prnt (bd_upd2 fl s) ! x = vcount
                 \<and> ds_par (build_dfs fl (bd_upd2 fl s)) ! x = ds_par (bd_upd2 fl s) ! x
                 \<and> ds_pot (build_dfs fl (bd_upd2 fl s)) ! x = ds_pot (bd_upd2 fl s) ! x"
          using IH(3)[OF c] inv1 s1 p1 by blast
        have St: "ds_seen s ! x \<and> ds_prnt s ! x = vcount
                 \<and> ds_par (bd_upd2 fl s) ! x = ds_par s ! x \<and> ds_pot (bd_upd2 fl s) ! x = ds_pot s ! x"
          using bd_upd2_cr[OF invs c xlt] Q1 by blast
        show ?thesis using Q1 St step by simp
      next
        assume c: "bd_call3_conds fl s"
        have step: "build_dfs fl s = build_dfs fl (bd_upd3 s)" using bd_simps(3)[OF IH(1) c] .
        have inv1: "dfs_inv fl (bd_upd3 s)" using bd_upd3_inv[OF invs c] .
        have s1: "ds_seen (build_dfs fl (bd_upd3 s)) ! x" using sb step by simp
        have p1: "ds_prnt (build_dfs fl (bd_upd3 s)) ! x = vcount" using pb step by simp
        have Q1: "ds_seen (bd_upd3 s) ! x \<and> ds_prnt (bd_upd3 s) ! x = vcount
                 \<and> ds_par (build_dfs fl (bd_upd3 s)) ! x = ds_par (bd_upd3 s) ! x
                 \<and> ds_pot (build_dfs fl (bd_upd3 s)) ! x = ds_pot (bd_upd3 s) ! x"
          using IH(4)[OF c] inv1 s1 p1 by blast
        have St: "ds_seen s ! x \<and> ds_prnt s ! x = vcount
                 \<and> ds_par (bd_upd3 s) ! x = ds_par s ! x \<and> ds_pot (bd_upd3 s) ! x = ds_pot s ! x"
          using bd_upd3_cr[OF c] Q1 by blast
        show ?thesis using Q1 St step by simp
      next
        assume c: "bd_ret_conds s"
        have "build_dfs fl s = s" using bd_simps(4)[OF IH(1) c] .
        thus ?thesis using sb pb by simp
      qed
    qed
  qed
  thus ?thesis using invs0 sb0 pb0 by blast
qed

definition comproot_edge_ok :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> bool" where
  "comproot_edge_ok s c \<longleftrightarrow>
     m \<le> ds_par s ! c \<and> ds_par s ! c - m < ds_nxt s
     \<and> ds_pot s ! c = (if art_dir c then pval_negM else pval_M)
     \<and> ds_afst s ! (ds_par s ! c - m) = (if art_dir c then c else vcount)
     \<and> ds_asnd s ! (ds_par s ! c - m) = (if art_dir c then vcount else c)"

definition comproot_inv :: "'n dfs_state \<Rightarrow> bool" where
  "comproot_inv s \<longleftrightarrow> (\<forall>c<vcount. ds_seen s ! c \<longrightarrow> ds_prnt s ! c = vcount \<longrightarrow> comproot_edge_ok s c)"

lemma emit_U_edge_cri:
  assumes ci: "comproot_inv s"
  shows "comproot_inv (emit_U_edge s v)"
  unfolding comproot_inv_def
proof (intro allI impI)
  fix c assume clt: "c < vcount" and sc: "ds_seen (emit_U_edge s v) ! c"
      and pc: "ds_prnt (emit_U_edge s v) ! c = vcount"
  have seq: "ds_seen (emit_U_edge s v) = ds_seen s" "ds_prnt (emit_U_edge s v) = ds_prnt s"
            "ds_par (emit_U_edge s v) = ds_par s" "ds_pot (emit_U_edge s v) = ds_pot s"
    by (simp_all add: emit_U_edge_def Let_def)
  have sc': "ds_seen s ! c" and pc': "ds_prnt s ! c = vcount" using sc pc seq by simp_all
  have ok: "comproot_edge_ok s c" using ci clt sc' pc' by (simp add: comproot_inv_def)
  have pm: "m \<le> ds_par s ! c" and bnd: "ds_par s ! c - m < ds_nxt s"
    and potc: "ds_pot s ! c = (if art_dir c then pval_negM else pval_M)"
    and afc: "ds_afst s ! (ds_par s ! c - m) = (if art_dir c then c else vcount)"
    and asc: "ds_asnd s ! (ds_par s ! c - m) = (if art_dir c then vcount else c)"
    using ok by (simp_all add: comproot_edge_ok_def)
  have nxt: "ds_nxt (emit_U_edge s v) = Suc (ds_nxt s)" by (rule emit_U_edge_nxt)
  have afeq: "ds_afst (emit_U_edge s v) ! (ds_par s ! c - m) = ds_afst s ! (ds_par s ! c - m)"
    using bnd by (simp add: emit_U_edge_def Let_def nth_list_update_neq)
  have aseq: "ds_asnd (emit_U_edge s v) ! (ds_par s ! c - m) = ds_asnd s ! (ds_par s ! c - m)"
    using bnd by (simp add: emit_U_edge_def Let_def nth_list_update_neq)
  show "comproot_edge_ok (emit_U_edge s v) c"
    unfolding comproot_edge_ok_def
    using pm bnd potc afc asc nxt afeq aseq seq by simp
qed

lemma open_tree_component_cri:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and unseen: "\<not> ds_seen s ! c" and cnz: "c \<noteq> 0"
      and stke: "ds_stk s = []" and al: "art_len s" and inb: "ds_nxt s < length vs_list"
      and ci: "comproot_inv s"
  shows "comproot_inv (open_tree_component acyc_flow s c)"
proof -
  have "dfs_wf acyc_flow s" "dfs_sized s" using inv by (simp_all add: dfs_inv_def)
  then obtain sd where opd: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd"
      and dom: "build_dfs_dom (acyc_flow, sd)"
      and I: "(dfs_inv acyc_flow s \<and> \<not> ds_seen s ! c \<and> c \<noteq> 0 \<and> ds_stk s = []) \<longrightarrow> dfs_inv acyc_flow sd"
      and nxtsd: "ds_nxt sd = Suc (ds_nxt s)"
      and seensd: "ds_seen sd = (ds_seen s)[c := True]"
      and prntsd: "ds_prnt sd = (ds_prnt s)[c := vcount]"
      and parsd: "ds_par sd = (ds_par s)[c := m + ds_nxt s]"
      and potsd: "ds_pot sd = (ds_pot s)[c := (if art_dir c then pval_negM else pval_M)]"
      and afstsd: "ds_afst sd = (ds_afst s)[ds_nxt s := (if art_dir c then c else vcount)]"
      and asndsd: "ds_asnd sd = (ds_asnd s)[ds_nxt s := (if art_dir c then vcount else c)]"
    using c by (rule open_tree_component_seed)
  have invsd: "dfs_inv acyc_flow sd" using I inv unseen cnz stke by blast
  have art: "ds_nxt (build_dfs acyc_flow sd) = ds_nxt sd \<and> ds_afst (build_dfs acyc_flow sd) = ds_afst sd \<and> ds_asnd (build_dfs acyc_flow sd) = ds_asnd sd
             \<and> ds_acap (build_dfs acyc_flow sd) = ds_acap sd \<and> ds_aflw (build_dfs acyc_flow sd) = ds_aflw sd \<and> ds_aest (build_dfs acyc_flow sd) = ds_aest sd"
    using build_dfs_art[OF dom] .
  have onxt: "ds_nxt (open_tree_component acyc_flow s c) = Suc (ds_nxt s)" using opd art nxtsd by simp
  have oafst: "ds_afst (open_tree_component acyc_flow s c) = (ds_afst s)[ds_nxt s := (if art_dir c then c else vcount)]"
    using opd art afstsd by simp
  have oasnd: "ds_asnd (open_tree_component acyc_flow s c) = (ds_asnd s)[ds_nxt s := (if art_dir c then vcount else c)]"
    using opd art asndsd by simp
  have lpar: "length (ds_par s) = Suc vcount" and lpot: "length (ds_pot s) = Suc vcount"
    using inv by (simp_all add: dfs_inv_def dfs_sized_def)
  have lafst: "length (ds_afst s) = length vs_list" and lasnd: "length (ds_asnd s) = length vs_list"
    using al by (simp_all add: art_len_def)
  show ?thesis
    unfolding comproot_inv_def
  proof (intro allI impI)
    fix w assume wlt: "w < vcount" and sw: "ds_seen (open_tree_component acyc_flow s c) ! w"
        and pw: "ds_prnt (open_tree_component acyc_flow s c) ! w = vcount"
    have bw: "ds_seen (build_dfs acyc_flow sd) ! w" using sw opd by simp
    have bpw: "ds_prnt (build_dfs acyc_flow sd) ! w = vcount" using pw opd by simp
    have cr: "ds_seen sd ! w \<and> ds_prnt sd ! w = vcount
              \<and> ds_par (build_dfs acyc_flow sd) ! w = ds_par sd ! w \<and> ds_pot (build_dfs acyc_flow sd) ! w = ds_pot sd ! w"
      using build_dfs_cr[OF dom invsd wlt bw bpw] .
    have parw: "ds_par (open_tree_component acyc_flow s c) ! w = ds_par sd ! w"
      and potw: "ds_pot (open_tree_component acyc_flow s c) ! w = ds_pot sd ! w"
      using cr opd by simp_all
    show "comproot_edge_ok (open_tree_component acyc_flow s c) w"
    proof (cases "w = c")
      case True
      have pval: "ds_par (open_tree_component acyc_flow s c) ! w = m + ds_nxt s"
        using parw parsd True c lpar by (simp add: nth_list_update_eq)
      have potval: "ds_pot (open_tree_component acyc_flow s c) ! w = (if art_dir c then pval_negM else pval_M)"
        using potw potsd True c lpot by (simp add: nth_list_update_eq)
      have idx: "ds_par (open_tree_component acyc_flow s c) ! w - m = ds_nxt s" using pval by simp
      have af: "ds_afst (open_tree_component acyc_flow s c) ! (ds_par (open_tree_component acyc_flow s c) ! w - m) = (if art_dir c then c else vcount)"
        using idx oafst lafst inb by (simp add: nth_list_update_eq)
      have as: "ds_asnd (open_tree_component acyc_flow s c) ! (ds_par (open_tree_component acyc_flow s c) ! w - m) = (if art_dir c then vcount else c)"
        using idx oasnd lasnd inb by (simp add: nth_list_update_eq)
      show ?thesis
        unfolding comproot_edge_ok_def
        using pval potval af as idx onxt True by simp
    next
      case False
      have swseed: "ds_seen s ! w" using cr seensd False by (simp add: nth_list_update_neq)
      have pwseed: "ds_prnt s ! w = vcount" using cr prntsd False by (simp add: nth_list_update_neq)
      have okw: "comproot_edge_ok s w" using ci wlt swseed pwseed by (simp add: comproot_inv_def)
      have pmw: "m \<le> ds_par s ! w" and bndw: "ds_par s ! w - m < ds_nxt s"
        and potcw: "ds_pot s ! w = (if art_dir w then pval_negM else pval_M)"
        and afcw: "ds_afst s ! (ds_par s ! w - m) = (if art_dir w then w else vcount)"
        and ascw: "ds_asnd s ! (ds_par s ! w - m) = (if art_dir w then vcount else w)"
        using okw by (simp_all add: comproot_edge_ok_def)
      have parw2: "ds_par (open_tree_component acyc_flow s c) ! w = ds_par s ! w"
        using parw parsd False by (simp add: nth_list_update_neq)
      have potw2: "ds_pot (open_tree_component acyc_flow s c) ! w = ds_pot s ! w"
        using potw potsd False by (simp add: nth_list_update_neq)
      have idxne: "ds_par s ! w - m \<noteq> ds_nxt s" using bndw by simp
      have af: "ds_afst (open_tree_component acyc_flow s c) ! (ds_par s ! w - m) = ds_afst s ! (ds_par s ! w - m)"
        using oafst idxne by (simp add: nth_list_update_neq)
      have as: "ds_asnd (open_tree_component acyc_flow s c) ! (ds_par s ! w - m) = ds_asnd s ! (ds_par s ! w - m)"
        using oasnd idxne by (simp add: nth_list_update_neq)
      show ?thesis
        unfolding comproot_edge_ok_def
        using pmw bndw potcw afcw ascw parw2 potw2 af as onxt by simp
    qed
  qed
qed

lemma phase1_step_cri:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" and al: "art_len s"
      and ci: "comproot_inv s" and inb: "ds_nxt (phase1_step acyc_flow v s) \<le> length vs_list"
  shows "comproot_inv (phase1_step acyc_flow v s)"
proof (cases "imbalance ! v = 0")
  case True thus ?thesis using ci by (simp add: phase1_step_def)
next
  case nz: False
  have vlt: "v < vcount" using v vs_less_vcount by simp
  show ?thesis
  proof (cases "ds_seen s ! v")
    case seen: True
    have eq: "phase1_step acyc_flow v s = emit_U_edge s v" using nz seen by (simp add: phase1_step_def)
    thus ?thesis using emit_U_edge_cri[OF ci] by simp
  next
    case notseen: False
    have vnz: "v \<noteq> 0" using v no_zero_node by metis
    have eq: "phase1_step acyc_flow v s = open_tree_component acyc_flow s v" using nz notseen by (simp add: phase1_step_def)
    have nxt: "ds_nxt (open_tree_component acyc_flow s v) = Suc (ds_nxt s)" using open_tree_component_art(1)[OF inv vlt] .
    have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
    show ?thesis using eq open_tree_component_cri[OF inv vlt notseen vnz stke al inbs ci] by simp
  qed
qed

lemma phase2_step_cri:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" and al: "art_len s"
      and ci: "comproot_inv s" and inb: "ds_nxt (phase2_step acyc_flow v s) \<le> length vs_list"
  shows "comproot_inv (phase2_step acyc_flow v s)"
proof (cases "ds_seen s ! v \<or> is_lonely v")
  case True thus ?thesis using ci by (simp add: phase2_step_def)
next
  case False
  hence notseen: "\<not> ds_seen s ! v" and nl: "\<not> is_lonely v" by auto
  have vlt: "v < vcount" using v vs_less_vcount by simp
  have vnz: "v \<noteq> 0" using v no_zero_node by metis
  have eq: "phase2_step acyc_flow v s = open_tree_component acyc_flow s v" using notseen nl by (simp add: phase2_step_def)
  have nxt: "ds_nxt (open_tree_component acyc_flow s v) = Suc (ds_nxt s)" using open_tree_component_art(1)[OF inv vlt] .
  have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
  show ?thesis using eq open_tree_component_cri[OF inv vlt notseen vnz stke al inbs ci] by simp
qed

lemma fold_emit_cri1:
  assumes "distinct xs" "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "comproot_inv s"
      "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "E \<inter> set xs = {}" "ds_nxt s = card E"
  shows "art_len (fold (phase1_step acyc_flow) xs s) \<and> comproot_inv (fold (phase1_step acyc_flow) xs s)
         \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase1_step acyc_flow) xs s) ! v}
                 \<and> ds_nxt (fold (phase1_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(2) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv1: "dfs_inv acyc_flow (phase1_step acyc_flow x s)" "ds_stk (phase1_step acyc_flow x s) = []"
    using phase1_step_inv[OF xvs conjI[OF Cons.prems(3) Cons.prems(4)]] by auto
  have al1: "art_len (phase1_step acyc_flow x s)" using phase1_step_art_len[OF xvs Cons.prems(3) Cons.prems(5)] .
  have Emono: "E \<subseteq> {v \<in> set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}"
    using Cons.prems(8) phase1_step_seen_mono[OF Cons.prems(3) xlt] by auto
  have Edisj: "E \<inter> set rest = {}" using Cons.prems(9) by auto
  have distr: "distinct rest" using Cons.prems(1) by simp
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(2) by simp
  have Esub: "E \<subseteq> set vs_list" using Cons.prems(8) by auto
  have xnotE: "x \<notin> E" using Cons.prems(9) by auto
  have step_inb: "ds_nxt (phase1_step acyc_flow x s) \<le> length vs_list"
    using phase1_step_nxt[OF Cons.prems(3) xlt]
  proof
    assume "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(10) card_sub_vs_le[OF Esub] by simp
  next
    assume A: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) \<and> ds_seen (phase1_step acyc_flow x s) ! x"
    have "insert x E \<subseteq> set vs_list" using Esub xvs by auto
    hence "card (insert x E) \<le> length vs_list" by (rule card_sub_vs_le)
    thus ?thesis using A Cons.prems(10) xnotE Cons.prems(7) by (simp add: card_insert_disjoint)
  qed
  have ci1: "comproot_inv (phase1_step acyc_flow x s)"
    using phase1_step_cri[OF xvs Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) step_inb] .
  from phase1_step_nxt[OF Cons.prems(3) xlt] show ?case
  proof
    assume A: "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase1_step acyc_flow x s) = card E" using A Cons.prems(10) by simp
    show ?thesis
      using Cons.hyps[OF distr subr inv1(1) inv1(2) al1 ci1 Cons.prems(7) Emono Edisj card1] by simp
  next
    assume B: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) \<and> ds_seen (phase1_step acyc_flow x s) ! x"
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(7) by (simp add: E2_def)
    have E2seen: "E2 \<subseteq> {v \<in> set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have E2disj: "E2 \<inter> set rest = {}" using Edisj Cons.prems(1) by (auto simp: E2_def)
    have card2: "ds_nxt (phase1_step acyc_flow x s) = card E2" using B Cons.prems(10) xnotE Cons.prems(7) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF distr subr inv1(1) inv1(2) al1 ci1 fin2 E2seen E2disj card2] by simp
  qed
qed

lemma fold_emit_cri2:
  assumes "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "comproot_inv s"
      "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "ds_nxt s = card E"
  shows "art_len (fold (phase2_step acyc_flow) xs s) \<and> comproot_inv (fold (phase2_step acyc_flow) xs s)
         \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase2_step acyc_flow) xs s) ! v}
                 \<and> ds_nxt (fold (phase2_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(1) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv1: "dfs_inv acyc_flow (phase2_step acyc_flow x s)" "ds_stk (phase2_step acyc_flow x s) = []"
    using phase2_step_inv[OF xvs conjI[OF Cons.prems(2) Cons.prems(3)]] by auto
  have al1: "art_len (phase2_step acyc_flow x s)" using phase2_step_art_len[OF xvs Cons.prems(2) Cons.prems(4)] .
  have Emono: "E \<subseteq> {v \<in> set vs_list. ds_seen (phase2_step acyc_flow x s) ! v}"
    using Cons.prems(7) phase2_step_seen_mono[OF Cons.prems(2) xlt] by auto
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(1) by simp
  have Esub: "E \<subseteq> set vs_list" using Cons.prems(7) by auto
  have step_inb: "ds_nxt (phase2_step acyc_flow x s) \<le> length vs_list"
    using phase2_step_nxt2[OF Cons.prems(2) xlt]
  proof
    assume "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(8) card_sub_vs_le[OF Esub] by simp
  next
    assume A: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! x \<and> ds_seen (phase2_step acyc_flow x s) ! x"
    have xnotE: "x \<notin> E" using A Cons.prems(7) by auto
    have "insert x E \<subseteq> set vs_list" using Esub xvs by auto
    hence "card (insert x E) \<le> length vs_list" by (rule card_sub_vs_le)
    thus ?thesis using A Cons.prems(8) xnotE Cons.prems(6) by (simp add: card_insert_disjoint)
  qed
  have ci1: "comproot_inv (phase2_step acyc_flow x s)"
    using phase2_step_cri[OF xvs Cons.prems(2) Cons.prems(3) Cons.prems(4) Cons.prems(5) step_inb] .
  from phase2_step_nxt2[OF Cons.prems(2) xlt] show ?case
  proof
    assume A: "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase2_step acyc_flow x s) = card E" using A Cons.prems(8) by simp
    show ?thesis
      using Cons.hyps[OF subr inv1(1) inv1(2) al1 ci1 Cons.prems(6) Emono card1] by simp
  next
    assume B: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! x \<and> ds_seen (phase2_step acyc_flow x s) ! x"
    have xnotE: "x \<notin> E" using B Cons.prems(7) by auto
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(6) by (simp add: E2_def)
    have E2seen: "E2 \<subseteq> {v \<in> set vs_list. ds_seen (phase2_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have card2: "ds_nxt (phase2_step acyc_flow x s) = card E2" using B Cons.prems(8) xnotE Cons.prems(6) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF subr inv1(1) inv1(2) al1 ci1 fin2 E2seen card2] by simp
  qed
qed

lemma build_tree_comproot_inv: "comproot_inv (build_tree acyc_flow)"
proof -
  have i0: "dfs_inv acyc_flow dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have al0: "art_len dfs_init" by (rule dfs_init_art_len)
  have ci0: "comproot_inv dfs_init" by (simp add: comproot_inv_def dfs_init_def del: replicate_Suc)
  have C1: "art_len (fold (phase1_step acyc_flow) vs_list dfs_init) \<and> comproot_inv (fold (phase1_step acyc_flow) vs_list dfs_init)
        \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase1_step acyc_flow) vs_list dfs_init) ! v}
                \<and> ds_nxt (fold (phase1_step acyc_flow) vs_list dfs_init) = card E')"
    apply (rule fold_emit_cri1[where E="{}"])
    subgoal by (rule distinct_vs_list)
    subgoal by simp
    subgoal using i0 by simp
    subgoal using i0 by simp
    subgoal by (rule al0)
    subgoal by (rule ci0)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: dfs_init_def)
    done
  have P1: "art_len (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have CI1: "comproot_inv (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have E1ex: "\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}
                \<and> ds_nxt (phase1 acyc_flow dfs_init) = card E'" using C1 by (simp add: phase1_def)
  have p1inv: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init) \<and> ds_stk (phase1 acyc_flow dfs_init) = []" using phase1_inv[OF i0] .
  obtain E1 where E1f: "finite E1" and E1s: "E1 \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}"
    and E1n: "ds_nxt (phase1 acyc_flow dfs_init) = card E1" using E1ex by blast
  have C2: "art_len (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        \<and> comproot_inv (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init)) ! v}
                \<and> ds_nxt (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init)) = card E')"
    apply (rule fold_emit_cri2[where E=E1 and s="phase1 acyc_flow dfs_init"])
    subgoal by simp
    subgoal using p1inv by simp
    subgoal using p1inv by simp
    subgoal by (rule P1)
    subgoal by (rule CI1)
    subgoal by (rule E1f)
    subgoal by (rule E1s)
    subgoal by (rule E1n)
    done
  have "comproot_inv (phase2 acyc_flow (phase1 acyc_flow dfs_init))" using C2 by (simp add: phase2_def)
  thus ?thesis by (simp add: build_tree_def Let_def comproot_inv_def comproot_edge_ok_def)
qed

lemma build_tree_comproot_rc_zero_uncond:
  assumes w: "w < vcount" "ds_seen (build_tree acyc_flow) ! w" "ds_prnt (build_tree acyc_flow) ! w = vcount"
  shows "cost_all ! (ds_par (build_tree acyc_flow) ! w) + pval_abstract bigM (nth (ds_pot (build_tree acyc_flow)) (fst_all ! (ds_par (build_tree acyc_flow) ! w))) - pval_abstract bigM (nth (ds_pot (build_tree acyc_flow)) (snd_all ! (ds_par (build_tree acyc_flow) ! w))) = 0"
proof -
  have ok: "comproot_edge_ok (build_tree acyc_flow) w" using build_tree_comproot_inv w by (simp add: comproot_inv_def)
  have pm: "m \<le> ds_par (build_tree acyc_flow) ! w" and bnd: "ds_par (build_tree acyc_flow) ! w - m < ds_nxt (build_tree acyc_flow)"
    and seed: "ds_pot (build_tree acyc_flow) ! w = (if art_dir w then pval_negM else pval_M)"
    and afst: "ds_afst (build_tree acyc_flow) ! (ds_par (build_tree acyc_flow) ! w - m) = (if art_dir w then w else vcount)"
    and asnd: "ds_asnd (build_tree acyc_flow) ! (ds_par (build_tree acyc_flow) ! w - m) = (if art_dir w then vcount else w)"
    using ok by (simp_all add: comproot_edge_ok_def)
  define k where "k = ds_par (build_tree acyc_flow) ! w - m"
  have pfa: "ds_par (build_tree acyc_flow) ! w = m + k" using pm by (simp add: k_def)
  have kK: "k < Kart" using bnd by (simp add: k_def Kart_def)
  have afk: "ds_afst (build_tree acyc_flow) ! k = (if art_dir w then w else vcount)" using afst by (simp add: k_def)
  have ask: "ds_asnd (build_tree acyc_flow) ! k = (if art_dir w then vcount else w)" using asnd by (simp add: k_def)
  show ?thesis
    using build_tree_comproot_rc_zero[OF w(1) seed pfa kK afk ask] .
qed

lemma build_tree_rc_zero:
  assumes w: "w < vcount" "ds_seen (build_tree acyc_flow) ! w"
  shows "cost_all ! (ds_par (build_tree acyc_flow) ! w) + pval_abstract bigM (nth (ds_pot (build_tree acyc_flow)) (fst_all ! (ds_par (build_tree acyc_flow) ! w))) - pval_abstract bigM (nth (ds_pot (build_tree acyc_flow)) (snd_all ! (ds_par (build_tree acyc_flow) ! w))) = 0"
proof (cases "ds_prnt (build_tree acyc_flow) ! w < vcount")
  case True
  show ?thesis using build_tree_interior_rc_zero[OF w(1) w(2) True] .
next
  case False
  have tsi: "tree_seen_inv (build_tree acyc_flow)" using build_tree_inv by (simp add: dfs_inv_def)
  have "ds_prnt (build_tree acyc_flow) ! w = vcount \<or> (ds_prnt (build_tree acyc_flow) ! w < vcount \<and> ds_seen (build_tree acyc_flow) ! (ds_prnt (build_tree acyc_flow) ! w))"
    using tsi w by (simp add: tree_seen_inv_def)
  hence "ds_prnt (build_tree acyc_flow) ! w = vcount" using False by simp
  thus ?thesis using build_tree_comproot_rc_zero_uncond[OF w(1) w(2)] by simp
qed

subsection \<open>Assembly substrate: seen vertices are real vertices (@{term \<open>Vseen = set vs_list\<close>})\<close>

text \<open>Every vertex the builder ever marks \<^emph>\<open>seen\<close> (below @{const vcount}) is one of the input
      vertices @{term \<open>set vs_list\<close>}: a discovery marks a free-edge endpoint (@{term snd_list} /
      @{term fst_list}, both subsets of @{term \<open>set vs_list\<close>} via @{thm fst_snd_vs}), and every component
      root opened by @{const open_tree_component} is a fold element of @{term vs_list}. Combined with
      \<open>vs_sub_Vseen\<close> this pins @{term Vseen} to exactly @{term \<open>set vs_list\<close>}.\<close>

text \<open>Under the dense model a name of @{term vs_list} that carries no edge (@{const is_lonely}) is a
      genuine non-vertex: it has zero @{const excess} (no incident edge contributes) and zero balance
      (@{thm isolated_zero}), hence zero @{const imbalance}, so the builder never opens it --- the seen
      set is exactly the edged vertices.  The lemmas below package this for the seen-set invariant.\<close>

lemma excess_lonely:
  assumes v: "v \<in> set vs_list" and lon: "is_lonely v"
  shows "excess ! v = 0"
proof -
  have vv: "v < Suc vcount" using vs_less_vcount[OF v] by simp
  have ne: "v \<notin> set fst_list \<union> set snd_list" using is_lonely_iff[OF v] lon by simp
  have s1: "(\<Sum>e\<leftarrow>[0..<m]. if snd_list ! e = v then flow_list ! e else 0) = 0"
  proof -
    have "(\<Sum>e\<leftarrow>[0..<m]. if snd_list ! e = v then flow_list ! e else 0) = (\<Sum>e\<leftarrow>[0..<m]. (0::'n))"
      using ne by (intro arg_cong[where f = sum_list] map_cong refl)
                  (metis UnCI atLeastLessThan_iff len_snd_list_m nth_mem set_upt)
    thus ?thesis by simp
  qed
  have s2: "(\<Sum>e\<leftarrow>[0..<m]. if fst_list ! e = v then flow_list ! e else 0) = 0"
  proof -
    have "(\<Sum>e\<leftarrow>[0..<m]. if fst_list ! e = v then flow_list ! e else 0) = (\<Sum>e\<leftarrow>[0..<m]. (0::'n))"
      using ne by (intro arg_cong[where f = sum_list] map_cong refl)
                  (metis UnCI atLeastLessThan_iff len_fst_list_m nth_mem set_upt)
    thus ?thesis by simp
  qed
  show ?thesis by (simp add: excess_nth[OF vv] s1 s2)
qed

lemma nth_vs_list: "i < n \<Longrightarrow> vs_list ! i = Suc i"
  using map_Suc_upt[of 0 n] by (simp add: vs_list_def del: upt_Suc)

lemma foldl_scatter_hit:
  assumes "distinct (map fst ps)" and "(k, x) \<in> set ps" and "k < length init"
  shows "foldl (\<lambda> arr (v, y). arr[v := y]) init ps ! k = x"
  using assms
proof (induct ps arbitrary: init)
  case Nil thus ?case by simp
next
  case (Cons p ps)
  obtain v y where p: "p = (v, y)" by (cases p)
  have vnp: "v \<notin> set (map fst ps)" using Cons.prems(1) p by simp
  show ?case
  proof (cases "k = v")
    case True
    have kx: "x = y" using Cons.prems(2) p True vnp by (force simp: image_iff)
    have miss: "\<And>v' x'. (v', x') \<in> set ps \<Longrightarrow> v' \<noteq> k" using vnp True by (force simp: image_iff)
    have "foldl (\<lambda> arr (v, y). arr[v := y]) (init[v := y]) ps ! k = init[v := y] ! k"
      by (rule foldl_scatter_miss[OF miss])
    also have "\<dots> = y" using True Cons.prems(3) by simp
    finally show ?thesis using p kx by simp
  next
    case False
    have inps: "(k, x) \<in> set ps" using Cons.prems(2) p False by auto
    have dm: "distinct (map fst ps)" using Cons.prems(1) p by simp
    have kl: "k < length (init[v := y])" using Cons.prems(3) by simp
    have "foldl (\<lambda> arr (v, y). arr[v := y]) (init[v := y]) ps ! k = x"
      by (rule Cons.hyps[OF dm inps kl])
    thus ?thesis using p by simp
  qed
qed

lemma b_lookup_nth:
  assumes v: "v \<in> set vs_list"
  shows "b_lookup v = b_list ! (v - 1)"
proof -
  from v obtain i where i: "i < n" and vvs: "vs_list ! i = v"
    by (auto simp: set_conv_nth length_vs_list)
  have vi: "v = Suc i" using vvs nth_vs_list[OF i] by simp
  have ilen: "i < length (zip vs_list b_list)" using i length_vs_list length_b by simp
  have "zip vs_list b_list ! i = (v, b_list ! i)" using i vvs length_vs_list length_b by simp
  hence zin: "(v, b_list ! i) \<in> set (zip vs_list b_list)" using ilen by (metis nth_mem)
  have dist: "distinct (map fst (zip vs_list b_list))"
    using distinct_vs_list length_vs_list length_b by (simp add: map_fst_zip)
  have vl: "v < length (replicate (Suc vcount) (0::'n))" using vs_less_vcount[OF v] by simp
  have "b_arr ! v = b_list ! i" unfolding b_arr_def by (rule foldl_scatter_hit[OF dist zin vl])
  thus ?thesis using vi by (simp add: b_lookup_def)
qed

lemma b_lookup_isolated:
  assumes v: "v \<in> set vs_list" and ne: "v \<notin> set fst_list \<union> set snd_list"
  shows "b_lookup v = 0"
proof -
  from v obtain i where i: "i < n" and vvs: "vs_list ! i = v"
    by (auto simp: set_conv_nth length_vs_list)
  have vi: "v = Suc i" using vvs nth_vs_list[OF i] by simp
  have "b_list ! i = 0" using isolated_zero[OF i] ne vi by simp
  thus ?thesis using b_lookup_nth[OF v] vi by simp
qed

lemma lonely_imbalance_zero:
  assumes v: "v \<in> set vs_list" and lon: "is_lonely v"
  shows "imbalance ! v = 0"
proof -
  have vlt: "v < vcount" using vs_less_vcount[OF v] .
  have ne: "v \<notin> set fst_list \<union> set snd_list" using is_lonely_iff[OF v] lon by simp
  show ?thesis using imbalance_nth[OF vlt] excess_lonely[OF v lon] b_lookup_isolated[OF v ne] by simp
qed

lemma imbalance_nz_edged:
  assumes v: "v \<in> set vs_list" and nz: "imbalance ! v \<noteq> 0"
  shows "v \<in> set fst_list \<union> set snd_list"
proof (rule ccontr)
  assume "v \<notin> set fst_list \<union> set snd_list"
  hence "is_lonely v" using is_lonely_iff[OF v] by simp
  thus False using lonely_imbalance_zero[OF v] nz by simp
qed

definition seen_sub :: "'n dfs_state \<Rightarrow> bool" where
  "seen_sub s \<longleftrightarrow> (\<forall>y<vcount. ds_seen s ! y \<longrightarrow> y \<in> set fst_list \<union> set snd_list)"

lemma bd_upd1_seen_sub:
  assumes inv: "dfs_inv fl s" and c: "bd_call1_conds fl s" and ss: "seen_sub s"
  shows "seen_sub (bd_upd1 fl s)"
  unfolding seen_sub_def
proof (intro allI impI)
  fix y assume ylt: "y < vcount" and sy: "ds_seen (bd_upd1 fl s) ! y"
  have wf: "dfs_wf fl s" using inv by (simp add: dfs_inv_def)
  obtain v rest e w c' where e: "e < m" "snd_list ! e = w"
    and up: "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr> else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (rule bd_upd1_eq[OF wf c])
  show "y \<in> set fst_list \<union> set snd_list"
  proof (cases "y = w")
    case True thus ?thesis using e by (metis UnI2 len_snd_list_m nth_mem)
  next
    case False
    hence "ds_seen s ! y" using sy up by (simp add: dfs_discover_def dfs_push_def Let_def split: if_splits)
    thus ?thesis using ss ylt by (simp add: seen_sub_def)
  qed
qed

lemma bd_upd2_seen_sub:
  assumes inv: "dfs_inv fl s" and c: "bd_call2_conds fl s" and ss: "seen_sub s"
  shows "seen_sub (bd_upd2 fl s)"
  unfolding seen_sub_def
proof (intro allI impI)
  fix y assume ylt: "y < vcount" and sy: "ds_seen (bd_upd2 fl s) ! y"
  have wf: "dfs_wf fl s" using inv by (simp add: dfs_inv_def)
  obtain v rest e w c' where e: "e < m" "fst_list ! e = w"
    and up: "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr> else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    by (rule bd_upd2_eq[OF wf c])
  show "y \<in> set fst_list \<union> set snd_list"
  proof (cases "y = w")
    case True thus ?thesis using e by (metis UnI1 len_fst_list_m nth_mem)
  next
    case False
    hence "ds_seen s ! y" using sy up by (simp add: dfs_discover_def dfs_push_def Let_def split: if_splits)
    thus ?thesis using ss ylt by (simp add: seen_sub_def)
  qed
qed

lemma bd_upd3_seen_sub:
  assumes c: "bd_call3_conds fl s" and ss: "seen_sub s"
  shows "seen_sub (bd_upd3 s)"
proof -
  obtain v rest where "bd_upd3 s = dfs_finish s v rest" by (rule bd_upd3_eq[OF c])
  thus ?thesis using ss by (simp add: seen_sub_def dfs_finish_def Let_def)
qed

lemma build_dfs_seen_sub:
  assumes dom: "build_dfs_dom (fl, s)" and inv: "dfs_inv fl s" and ss: "seen_sub s"
  shows "seen_sub (build_dfs fl s)"
proof -
  have "dfs_inv fl s \<longrightarrow> seen_sub s \<longrightarrow> seen_sub (build_dfs fl s)"
  proof (induct rule: bd_induct[OF dom])
    case IH: (1 fl s)
    show ?case
    proof (intro impI)
      assume invs: "dfs_inv fl s" and sss: "seen_sub s"
      show "seen_sub (build_dfs fl s)"
      proof (rule bd_cases[where s=s and fl=fl])
        assume c: "bd_call1_conds fl s"
        have step: "build_dfs fl s = build_dfs fl (bd_upd1 fl s)" using bd_simps(1)[OF IH(1) c] .
        have "seen_sub (build_dfs fl (bd_upd1 fl s))"
          using IH(2)[OF c] bd_upd1_inv[OF invs c] bd_upd1_seen_sub[OF invs c sss] by blast
        thus ?thesis using step by simp
      next
        assume c: "bd_call2_conds fl s"
        have step: "build_dfs fl s = build_dfs fl (bd_upd2 fl s)" using bd_simps(2)[OF IH(1) c] .
        have "seen_sub (build_dfs fl (bd_upd2 fl s))"
          using IH(3)[OF c] bd_upd2_inv[OF invs c] bd_upd2_seen_sub[OF invs c sss] by blast
        thus ?thesis using step by simp
      next
        assume c: "bd_call3_conds fl s"
        have step: "build_dfs fl s = build_dfs fl (bd_upd3 s)" using bd_simps(3)[OF IH(1) c] .
        have "seen_sub (build_dfs fl (bd_upd3 s))"
          using IH(4)[OF c] bd_upd3_inv[OF invs c] bd_upd3_seen_sub[OF c sss] by blast
        thus ?thesis using step by simp
      next
        assume c: "bd_ret_conds s"
        have "build_dfs fl s = s" using bd_simps(4)[OF IH(1) c] .
        thus ?thesis using sss by simp
      qed
    qed
  qed
  thus ?thesis using inv ss by blast
qed

lemma emit_U_edge_seen_sub:
  assumes ss: "seen_sub s"
  shows "seen_sub (emit_U_edge s v)"
proof -
  have "ds_seen (emit_U_edge s v) = ds_seen s" by (simp add: emit_U_edge_def Let_def)
  thus ?thesis using ss by (simp add: seen_sub_def)
qed

lemma open_tree_component_seen_sub:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and unseen: "\<not> ds_seen s ! c" and cnz: "c \<noteq> 0"
      and stke: "ds_stk s = []" and cin: "c \<in> set fst_list \<union> set snd_list" and ss: "seen_sub s"
  shows "seen_sub (open_tree_component acyc_flow s c)"
proof -
  have "dfs_wf acyc_flow s" "dfs_sized s" using inv by (simp_all add: dfs_inv_def)
  then obtain sd where opd: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd"
      and dom: "build_dfs_dom (acyc_flow, sd)"
      and I: "(dfs_inv acyc_flow s \<and> \<not> ds_seen s ! c \<and> c \<noteq> 0 \<and> ds_stk s = []) \<longrightarrow> dfs_inv acyc_flow sd"
      and nxtsd: "ds_nxt sd = Suc (ds_nxt s)"
      and seensd: "ds_seen sd = (ds_seen s)[c := True]"
      and prntsd: "ds_prnt sd = (ds_prnt s)[c := vcount]"
      and parsd: "ds_par sd = (ds_par s)[c := m + ds_nxt s]"
      and potsd: "ds_pot sd = (ds_pot s)[c := (if art_dir c then pval_negM else pval_M)]"
      and afstsd: "ds_afst sd = (ds_afst s)[ds_nxt s := (if art_dir c then c else vcount)]"
      and asndsd: "ds_asnd sd = (ds_asnd s)[ds_nxt s := (if art_dir c then vcount else c)]"
    using c by (rule open_tree_component_seed)
  have invsd: "dfs_inv acyc_flow sd" using I inv unseen cnz stke by blast
  have sssd: "seen_sub sd"
  proof (unfold seen_sub_def, intro allI impI)
    fix y assume ylt: "y < vcount" and sy: "ds_seen sd ! y"
    show "y \<in> set fst_list \<union> set snd_list"
    proof (cases "y = c")
      case True thus ?thesis using cin by simp
    next
      case False
      have "ds_seen sd ! y = ds_seen s ! y" using seensd False by (simp add: nth_list_update_neq)
      hence "ds_seen s ! y" using sy by simp
      thus ?thesis using ss ylt by (simp add: seen_sub_def)
    qed
  qed
  show ?thesis using opd build_dfs_seen_sub[OF dom invsd sssd] by simp
qed

lemma phase1_step_seen_sub:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" and ss: "seen_sub s"
  shows "seen_sub (phase1_step acyc_flow v s)"
proof (cases "imbalance ! v = 0")
  case True thus ?thesis using ss by (simp add: phase1_step_def)
next
  case nz: False
  have vlt: "v < vcount" using v vs_less_vcount by simp
  show ?thesis
  proof (cases "ds_seen s ! v")
    case seen: True
    have "phase1_step acyc_flow v s = emit_U_edge s v" using nz seen by (simp add: phase1_step_def)
    thus ?thesis using emit_U_edge_seen_sub[OF ss] by simp
  next
    case notseen: False
    have vnz: "v \<noteq> 0" using v no_zero_node by metis
    have edged_v: "v \<in> set fst_list \<union> set snd_list" using imbalance_nz_edged[OF v nz] .
    have "phase1_step acyc_flow v s = open_tree_component acyc_flow s v" using nz notseen by (simp add: phase1_step_def)
    thus ?thesis using open_tree_component_seen_sub[OF inv vlt notseen vnz stke edged_v ss] by simp
  qed
qed

lemma phase2_step_seen_sub:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" and ss: "seen_sub s"
  shows "seen_sub (phase2_step acyc_flow v s)"
proof (cases "ds_seen s ! v \<or> is_lonely v")
  case True thus ?thesis using ss by (simp add: phase2_step_def)
next
  case False
  hence notseen: "\<not> ds_seen s ! v" and nl: "\<not> is_lonely v" by auto
  have vlt: "v < vcount" using v vs_less_vcount by simp
  have vnz: "v \<noteq> 0" using v no_zero_node by metis
  have edged_v: "v \<in> set fst_list \<union> set snd_list" using not_lonely_edged[OF vlt nl] .
  have "phase2_step acyc_flow v s = open_tree_component acyc_flow s v" using notseen nl by (simp add: phase2_step_def)
  thus ?thesis using open_tree_component_seen_sub[OF inv vlt notseen vnz stke edged_v ss] by simp
qed

lemma fold_phase1_seen_sub:
  assumes "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s \<and> ds_stk s = []" "seen_sub s"
  shows "seen_sub (fold (phase1_step acyc_flow) xs s)"
  using assms
proof (induct xs arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(1) by simp
  have inv1: "dfs_inv acyc_flow (phase1_step acyc_flow x s) \<and> ds_stk (phase1_step acyc_flow x s) = []"
    using phase1_step_inv[OF xvs Cons.prems(2)] .
  have ss1: "seen_sub (phase1_step acyc_flow x s)"
    using phase1_step_seen_sub[OF xvs conjunct1[OF Cons.prems(2)] conjunct2[OF Cons.prems(2)] Cons.prems(3)] .
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(1) by simp
  show ?case using Cons.hyps[OF subr inv1 ss1] by simp
qed

lemma fold_phase2_seen_sub:
  assumes "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s \<and> ds_stk s = []" "seen_sub s"
  shows "seen_sub (fold (phase2_step acyc_flow) xs s)"
  using assms
proof (induct xs arbitrary: s)
  case Nil thus ?case by simp
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(1) by simp
  have inv1: "dfs_inv acyc_flow (phase2_step acyc_flow x s) \<and> ds_stk (phase2_step acyc_flow x s) = []"
    using phase2_step_inv[OF xvs Cons.prems(2)] .
  have ss1: "seen_sub (phase2_step acyc_flow x s)"
    using phase2_step_seen_sub[OF xvs conjunct1[OF Cons.prems(2)] conjunct2[OF Cons.prems(2)] Cons.prems(3)] .
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(1) by simp
  show ?case using Cons.hyps[OF subr inv1 ss1] by simp
qed

lemma build_tree_seen_sub: "seen_sub (build_tree acyc_flow)"
proof -
  have i0: "dfs_inv acyc_flow dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have ss0: "seen_sub dfs_init" by (simp add: seen_sub_def dfs_init_def del: replicate_Suc)
  have p1inv: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init) \<and> ds_stk (phase1 acyc_flow dfs_init) = []" using phase1_inv[OF i0] .
  have ss1: "seen_sub (phase1 acyc_flow dfs_init)"
    unfolding phase1_def using fold_phase1_seen_sub[OF subset_refl i0 ss0] .
  have ss2: "seen_sub (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
    unfolding phase2_def using fold_phase2_seen_sub[OF subset_refl p1inv ss1] .
  thus ?thesis by (simp add: build_tree_def Let_def seen_sub_def)
qed

lemma V_sub_Vseen: "original_network.\<V> \<subseteq> Vseen"
proof
  fix v assume "v \<in> original_network.\<V>"
  hence e: "v \<in> set fst_list \<union> set snd_list" using V_orig_eq by simp
  have vvs: "v \<in> set vs_list" using e fst_snd_vs by blast
  have nl: "\<not> is_lonely v" using edged_not_lonely[OF e] .
  show "v \<in> Vseen" using build_tree_spans[OF vvs nl] vs_less_vcount[OF vvs] by (simp add: Vseen_def)
qed

text \<open>The seen set is exactly the graph vertex set: every edged vertex is spanned (@{thm V_sub_Vseen})
      and, by the strengthened @{thm build_tree_seen_sub}, every seen name is an edge endpoint.  This
      replaces the old \<open>Vseen = set vs_list\<close> (false once edge-less names are kept).\<close>

lemma Vseen_eq_V: "Vseen = original_network.\<V>"
proof
  show "Vseen \<subseteq> original_network.\<V>"
    using build_tree_seen_sub V_orig_eq by (auto simp: Vseen_def seen_sub_def)
next
  show "original_network.\<V> \<subseteq> Vseen" by (rule V_sub_Vseen)
qed

subsection \<open>Assembly substrate: artificial-edge endpoints are real vertices or the root\<close>

text \<open>Every stored artificial edge (index @{term \<open>k < Kart\<close>}) has both endpoints in
      @{term \<open>insert vcount (set vs_list)\<close>}: one is the artificial root @{const vcount}, the other the
      emission subject, which is always a fold element of @{term vs_list}. This is the endpoint bound
      the graph-vertex identity \<open>NSg_verts\<close> needs on the artificial half.\<close>

definition seen_set :: "'n dfs_state \<Rightarrow> nat set" where
  "seen_set s = {v. v < vcount \<and> ds_seen s ! v}"

lemma seen_set_build_tree: "seen_set (build_tree acyc_flow) = Vseen"
  by (simp add: seen_set_def Vseen_def)

text \<open>Strengthened to the \<^emph>\<open>seen\<close> set: every stored artificial edge runs between the root and a
      vertex that is already visited (a component root just opened, or a still-visited imbalanced
      vertex).  Because visitedness only grows this survives to @{const build_tree}, where the seen
      set is exactly @{const Vseen} --- the fact that identifies the augmented vertex set with @{const Varb}.\<close>

definition tail_sub :: "'n dfs_state \<Rightarrow> bool" where
  "tail_sub s \<longleftrightarrow> (\<forall>k<ds_nxt s. ds_afst s ! k \<in> insert vcount (seen_set s)
                              \<and> ds_asnd s ! k \<in> insert vcount (seen_set s))"

lemma emit_U_edge_tail_sub_old:
  assumes k: "k < ds_nxt s"
  shows "ds_afst (emit_U_edge s v) ! k = ds_afst s ! k \<and> ds_asnd (emit_U_edge s v) ! k = ds_asnd s ! k"
  using k by (simp add: emit_U_edge_def Let_def nth_list_update_neq)

lemma phase1_step_tail_sub:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and al: "art_len s"
      and ts: "tail_sub s" and inb: "ds_nxt (phase1_step acyc_flow v s) \<le> length vs_list"
  shows "tail_sub (phase1_step acyc_flow v s)"
proof (cases "imbalance ! v = 0")
  case True thus ?thesis using ts by (simp add: phase1_step_def)
next
  case nz: False
  have vlt: "v < vcount" using v vs_less_vcount by simp
  show ?thesis
  proof (cases "ds_seen s ! v")
    case seen: True
    have eq: "phase1_step acyc_flow v s = emit_U_edge s v" using nz seen by (simp add: phase1_step_def)
    have nxt: "ds_nxt (emit_U_edge s v) = Suc (ds_nxt s)" by (rule emit_U_edge_nxt)
    have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
    have sseq: "seen_set (emit_U_edge s v) = seen_set s" by (simp add: seen_set_def emit_U_edge_def Let_def)
    have "v \<in> seen_set s" using seen vlt by (simp add: seen_set_def)
    hence vin: "v \<in> seen_set (emit_U_edge s v)" using sseq by simp
    show ?thesis
      unfolding eq tail_sub_def
    proof (intro allI impI)
      fix k assume "k < ds_nxt (emit_U_edge s v)"
      hence kl: "k < Suc (ds_nxt s)" using nxt by simp
      show "ds_afst (emit_U_edge s v) ! k \<in> insert vcount (seen_set (emit_U_edge s v))
          \<and> ds_asnd (emit_U_edge s v) ! k \<in> insert vcount (seen_set (emit_U_edge s v))"
      proof (cases "k < ds_nxt s")
        case True
        have "ds_afst s ! k \<in> insert vcount (seen_set s) \<and> ds_asnd s ! k \<in> insert vcount (seen_set s)"
          using ts True by (simp add: tail_sub_def)
        thus ?thesis using emit_U_edge_tail_sub_old[OF True] sseq by simp
      next
        case False
        hence keq: "k = ds_nxt s" using kl by simp
        show ?thesis using vin
          by (auto simp: keq emit_U_edge_afst_at[OF inbs al] emit_U_edge_asnd_at[OF inbs al])
      qed
    qed
  next
    case notseen: False
    have eq: "phase1_step acyc_flow v s = open_tree_component acyc_flow s v" using nz notseen by (simp add: phase1_step_def)
    have nxt: "ds_nxt (open_tree_component acyc_flow s v) = Suc (ds_nxt s)" using open_tree_component_art(1)[OF inv vlt] .
    have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
    have mono: "seen_set s \<subseteq> seen_set (open_tree_component acyc_flow s v)"
      by (auto simp: seen_set_def dest: open_tree_component_seen_mono[OF inv vlt])
    have vin: "v \<in> seen_set (open_tree_component acyc_flow s v)"
      using open_tree_component_marks[OF inv vlt] vlt by (simp add: seen_set_def)
    show ?thesis
      unfolding eq tail_sub_def
    proof (intro allI impI)
      fix k assume "k < ds_nxt (open_tree_component acyc_flow s v)"
      hence kl: "k < Suc (ds_nxt s)" using nxt by simp
      show "ds_afst (open_tree_component acyc_flow s v) ! k \<in> insert vcount (seen_set (open_tree_component acyc_flow s v))
          \<and> ds_asnd (open_tree_component acyc_flow s v) ! k \<in> insert vcount (seen_set (open_tree_component acyc_flow s v))"
      proof (cases "k < ds_nxt s")
        case True
        have old: "ds_afst s ! k \<in> insert vcount (seen_set s) \<and> ds_asnd s ! k \<in> insert vcount (seen_set s)"
          using ts True by (simp add: tail_sub_def)
        show ?thesis
          using old mono open_tree_component_afst_old[OF inv vlt True] open_tree_component_asnd_old[OF inv vlt True]
          by auto
      next
        case False
        hence keq: "k = ds_nxt s" using kl by simp
        show ?thesis using vin
          by (auto simp: keq open_tree_component_afst_at[OF inv vlt inbs al]
                         open_tree_component_asnd_at[OF inv vlt inbs al])
      qed
    qed
  qed
qed

lemma phase2_step_tail_sub:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and al: "art_len s"
      and ts: "tail_sub s" and inb: "ds_nxt (phase2_step acyc_flow v s) \<le> length vs_list"
  shows "tail_sub (phase2_step acyc_flow v s)"
proof (cases "ds_seen s ! v \<or> is_lonely v")
  case True thus ?thesis using ts by (simp add: phase2_step_def)
next
  case False
  hence notseen: "\<not> ds_seen s ! v" and nl: "\<not> is_lonely v" by auto
  have vlt: "v < vcount" using v vs_less_vcount by simp
  have eq: "phase2_step acyc_flow v s = open_tree_component acyc_flow s v" using notseen nl by (simp add: phase2_step_def)
  have nxt: "ds_nxt (open_tree_component acyc_flow s v) = Suc (ds_nxt s)" using open_tree_component_art(1)[OF inv vlt] .
  have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
  have mono: "seen_set s \<subseteq> seen_set (open_tree_component acyc_flow s v)"
    by (auto simp: seen_set_def dest: open_tree_component_seen_mono[OF inv vlt])
  have vin: "v \<in> seen_set (open_tree_component acyc_flow s v)"
    using open_tree_component_marks[OF inv vlt] vlt by (simp add: seen_set_def)
  show ?thesis
    unfolding eq tail_sub_def
  proof (intro allI impI)
    fix k assume "k < ds_nxt (open_tree_component acyc_flow s v)"
    hence kl: "k < Suc (ds_nxt s)" using nxt by simp
    show "ds_afst (open_tree_component acyc_flow s v) ! k \<in> insert vcount (seen_set (open_tree_component acyc_flow s v))
        \<and> ds_asnd (open_tree_component acyc_flow s v) ! k \<in> insert vcount (seen_set (open_tree_component acyc_flow s v))"
    proof (cases "k < ds_nxt s")
      case True
      have old: "ds_afst s ! k \<in> insert vcount (seen_set s) \<and> ds_asnd s ! k \<in> insert vcount (seen_set s)"
        using ts True by (simp add: tail_sub_def)
      show ?thesis
        using old mono open_tree_component_afst_old[OF inv vlt True] open_tree_component_asnd_old[OF inv vlt True]
        by auto
    next
      case False
      hence keq: "k = ds_nxt s" using kl by simp
      show ?thesis using vin
        by (auto simp: keq open_tree_component_afst_at[OF inv vlt inbs al]
                       open_tree_component_asnd_at[OF inv vlt inbs al])
    qed
  qed
qed

lemma fold_emit_sub1:
  assumes "distinct xs" "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "tail_sub s"
      "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "E \<inter> set xs = {}" "ds_nxt s = card E"
  shows "art_len (fold (phase1_step acyc_flow) xs s) \<and> tail_sub (fold (phase1_step acyc_flow) xs s)
         \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase1_step acyc_flow) xs s) ! v}
                 \<and> ds_nxt (fold (phase1_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(2) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv1: "dfs_inv acyc_flow (phase1_step acyc_flow x s)" "ds_stk (phase1_step acyc_flow x s) = []"
    using phase1_step_inv[OF xvs conjI[OF Cons.prems(3) Cons.prems(4)]] by auto
  have al1: "art_len (phase1_step acyc_flow x s)" using phase1_step_art_len[OF xvs Cons.prems(3) Cons.prems(5)] .
  have Emono: "E \<subseteq> {v \<in> set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}"
    using Cons.prems(8) phase1_step_seen_mono[OF Cons.prems(3) xlt] by auto
  have Edisj: "E \<inter> set rest = {}" using Cons.prems(9) by auto
  have distr: "distinct rest" using Cons.prems(1) by simp
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(2) by simp
  have Esub: "E \<subseteq> set vs_list" using Cons.prems(8) by auto
  have xnotE: "x \<notin> E" using Cons.prems(9) by auto
  have step_inb: "ds_nxt (phase1_step acyc_flow x s) \<le> length vs_list"
    using phase1_step_nxt[OF Cons.prems(3) xlt]
  proof
    assume "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(10) card_sub_vs_le[OF Esub] by simp
  next
    assume A: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) \<and> ds_seen (phase1_step acyc_flow x s) ! x"
    have "insert x E \<subseteq> set vs_list" using Esub xvs by auto
    hence "card (insert x E) \<le> length vs_list" by (rule card_sub_vs_le)
    thus ?thesis using A Cons.prems(10) xnotE Cons.prems(7) by (simp add: card_insert_disjoint)
  qed
  have ts1: "tail_sub (phase1_step acyc_flow x s)"
    using phase1_step_tail_sub[OF xvs Cons.prems(3) Cons.prems(5) Cons.prems(6) step_inb] .
  from phase1_step_nxt[OF Cons.prems(3) xlt] show ?case
  proof
    assume A: "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase1_step acyc_flow x s) = card E" using A Cons.prems(10) by simp
    show ?thesis
      using Cons.hyps[OF distr subr inv1(1) inv1(2) al1 ts1 Cons.prems(7) Emono Edisj card1] by simp
  next
    assume B: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) \<and> ds_seen (phase1_step acyc_flow x s) ! x"
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(7) by (simp add: E2_def)
    have E2seen: "E2 \<subseteq> {v \<in> set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have E2disj: "E2 \<inter> set rest = {}" using Edisj Cons.prems(1) by (auto simp: E2_def)
    have card2: "ds_nxt (phase1_step acyc_flow x s) = card E2" using B Cons.prems(10) xnotE Cons.prems(7) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF distr subr inv1(1) inv1(2) al1 ts1 fin2 E2seen E2disj card2] by simp
  qed
qed

lemma fold_emit_sub2:
  assumes "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "tail_sub s"
      "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "ds_nxt s = card E"
  shows "art_len (fold (phase2_step acyc_flow) xs s) \<and> tail_sub (fold (phase2_step acyc_flow) xs s)
         \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase2_step acyc_flow) xs s) ! v}
                 \<and> ds_nxt (fold (phase2_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(1) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv1: "dfs_inv acyc_flow (phase2_step acyc_flow x s)" "ds_stk (phase2_step acyc_flow x s) = []"
    using phase2_step_inv[OF xvs conjI[OF Cons.prems(2) Cons.prems(3)]] by auto
  have al1: "art_len (phase2_step acyc_flow x s)" using phase2_step_art_len[OF xvs Cons.prems(2) Cons.prems(4)] .
  have Emono: "E \<subseteq> {v \<in> set vs_list. ds_seen (phase2_step acyc_flow x s) ! v}"
    using Cons.prems(7) phase2_step_seen_mono[OF Cons.prems(2) xlt] by auto
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(1) by simp
  have Esub: "E \<subseteq> set vs_list" using Cons.prems(7) by auto
  have step_inb: "ds_nxt (phase2_step acyc_flow x s) \<le> length vs_list"
    using phase2_step_nxt2[OF Cons.prems(2) xlt]
  proof
    assume "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(8) card_sub_vs_le[OF Esub] by simp
  next
    assume A: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! x \<and> ds_seen (phase2_step acyc_flow x s) ! x"
    have xnotE: "x \<notin> E" using A Cons.prems(7) by auto
    have "insert x E \<subseteq> set vs_list" using Esub xvs by auto
    hence "card (insert x E) \<le> length vs_list" by (rule card_sub_vs_le)
    thus ?thesis using A Cons.prems(8) xnotE Cons.prems(6) by (simp add: card_insert_disjoint)
  qed
  have ts1: "tail_sub (phase2_step acyc_flow x s)"
    using phase2_step_tail_sub[OF xvs Cons.prems(2) Cons.prems(4) Cons.prems(5) step_inb] .
  from phase2_step_nxt2[OF Cons.prems(2) xlt] show ?case
  proof
    assume A: "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase2_step acyc_flow x s) = card E" using A Cons.prems(8) by simp
    show ?thesis
      using Cons.hyps[OF subr inv1(1) inv1(2) al1 ts1 Cons.prems(6) Emono card1] by simp
  next
    assume B: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! x \<and> ds_seen (phase2_step acyc_flow x s) ! x"
    have xnotE: "x \<notin> E" using B Cons.prems(7) by auto
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(6) by (simp add: E2_def)
    have E2seen: "E2 \<subseteq> {v \<in> set vs_list. ds_seen (phase2_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have card2: "ds_nxt (phase2_step acyc_flow x s) = card E2" using B Cons.prems(8) xnotE Cons.prems(6) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF subr inv1(1) inv1(2) al1 ts1 fin2 E2seen card2] by simp
  qed
qed

lemma build_tree_tail_sub: "tail_sub (build_tree acyc_flow)"
proof -
  have i0: "dfs_inv acyc_flow dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have al0: "art_len dfs_init" by (rule dfs_init_art_len)
  have ts0: "tail_sub dfs_init" by (simp add: tail_sub_def dfs_init_def)
  have C1: "art_len (fold (phase1_step acyc_flow) vs_list dfs_init) \<and> tail_sub (fold (phase1_step acyc_flow) vs_list dfs_init)
        \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase1_step acyc_flow) vs_list dfs_init) ! v}
                \<and> ds_nxt (fold (phase1_step acyc_flow) vs_list dfs_init) = card E')"
    apply (rule fold_emit_sub1[where E="{}"])
    subgoal by (rule distinct_vs_list)
    subgoal by simp
    subgoal using i0 by simp
    subgoal using i0 by simp
    subgoal by (rule al0)
    subgoal by (rule ts0)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: dfs_init_def)
    done
  have P1: "art_len (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have TS1: "tail_sub (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have E1ex: "\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}
                \<and> ds_nxt (phase1 acyc_flow dfs_init) = card E'" using C1 by (simp add: phase1_def)
  have p1inv: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init) \<and> ds_stk (phase1 acyc_flow dfs_init) = []" using phase1_inv[OF i0] .
  obtain E1 where E1f: "finite E1" and E1s: "E1 \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}"
    and E1n: "ds_nxt (phase1 acyc_flow dfs_init) = card E1" using E1ex by blast
  have C2: "art_len (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        \<and> tail_sub (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init)) ! v}
                \<and> ds_nxt (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init)) = card E')"
    apply (rule fold_emit_sub2[where E=E1 and s="phase1 acyc_flow dfs_init"])
    subgoal by simp
    subgoal using p1inv by simp
    subgoal using p1inv by simp
    subgoal by (rule P1)
    subgoal by (rule TS1)
    subgoal by (rule E1f)
    subgoal by (rule E1s)
    subgoal by (rule E1n)
    done
  have "tail_sub (phase2 acyc_flow (phase1 acyc_flow dfs_init))" using C2 by (simp add: phase2_def)
  thus ?thesis by (simp add: build_tree_def Let_def tail_sub_def seen_set_def)
qed

lemma Kart_pos: "0 < Kart"
proof -
  have m0: "0 < m" by (rule num_edges_gtr_0)
  have "fst_list ! 0 \<in> set fst_list" using m0 by (metis len_fst_list_m nth_mem)
  hence v0vs: "fst_list ! 0 \<in> set vs_list" using fst_snd_vs by blast
  define v0 where "v0 = fst_list ! 0"
  have v0vs': "v0 \<in> set vs_list" using v0vs by (simp add: v0_def)
  have v0e: "v0 \<in> set fst_list \<union> set snd_list" using m0 by (metis UnI1 len_fst_list_m nth_mem v0_def)
  have v0nl: "\<not> is_lonely v0" using edged_not_lonely[OF v0e] .
  have v0lt: "v0 < vcount" using v0vs' vs_less_vcount by simp
  have v0seen: "ds_seen (build_tree acyc_flow) ! v0" using build_tree_spans[OF v0vs' v0nl] .
  have v0nr: "v0 \<noteq> vcount" using v0lt by simp
  have reach: "(v0, vcount) \<in> (pstep (build_tree acyc_flow))\<^sup>*" using build_tree_reaches_root[OF v0lt v0seen] .
  obtain c where cstep: "(c, vcount) \<in> pstep (build_tree acyc_flow)" using reach v0nr by (metis rtranclE)
  have clt: "c < vcount" and cseen: "ds_seen (build_tree acyc_flow) ! c" and cpr: "ds_prnt (build_tree acyc_flow) ! c = vcount"
    using cstep by (auto simp: pstep_def)
  have "comproot_edge_ok (build_tree acyc_flow) c"
    using build_tree_comproot_inv clt cseen cpr by (simp add: comproot_inv_def)
  hence "ds_par (build_tree acyc_flow) ! c - m < ds_nxt (build_tree acyc_flow)" by (simp add: comproot_edge_ok_def)
  thus ?thesis by (simp add: Kart_def)
qed

section \<open>The interpretation layer: the augmented network as a @{locale network_simplex_spec}\<close>

text \<open>The simplex loop runs over the \<^emph>\<open>augmented\<close> edge set @{term \<open>{0..<m+Kart}\<close>} (real
      edges @{term \<open>{0..<m}\<close>} plus the @{term Kart} artificial big-@{term \<open>M\<close>} edges), read through
      the unified arrays @{const fst_all} / @{const snd_all} / @{const cap_all} / @{const cost_all}.  This
      is a fresh @{locale cost_flow_network} (the base sublocale covered only the real edges
      @{term \<open>{0..<m}\<close>}): endpoints and cost read the arrays, capacity decodes @{term \<open>- 1\<close>} as
      @{term \<open>\<infinity>\<close>}, and \<open>create_edge\<close> sends an out-of-range pair to a synthetic
      infinite-capacity edge.\<close>

lemma cap_all_nonneg:
  assumes e: "e < m + Kart" shows "0 \<le> cap_all ! e \<or> cap_all ! e = - 1"
proof (cases "e < m")
  case True
  have "cap_all ! e = capacity_list ! e" using True by (rule cap_all_real)
  moreover have "capacity_list ! e \<in> set capacity_list" using True length_edges by (metis nth_mem)
  ultimately show ?thesis using cap_neg by auto
next
  case False
  then obtain k where ek: "e = m + k" by (metis add.commute le_Suc_ex not_less)
  have kK: "k < Kart" using e ek by simp
  have "cap_all ! e = ds_acap (build_tree acyc_flow) ! k" using ek kK by (simp add: cap_all_art)
  moreover have "0 \<le> ds_acap (build_tree acyc_flow) ! k"
    using tail_edge_ok_build_tree[OF kK] by (auto simp: tail_edge_ok_def art_tree_cap_def art_flow_def)
  ultimately show ?thesis by simp
qed

interpretation NSg: cost_flow_network
  where \<E>           = "{0..<m+Kart}"
    and fst          = "\<lambda> e. if e < m+Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m+Kart)))"
    and snd          = "\<lambda> e. if e < m+Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m+Kart)))"
    and create_edge  = "\<lambda> u v. (m+Kart) + prod_encode (u, v)"
    and \<u>           = "\<lambda> e. if e < m+Kart then (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) else \<infinity>"
    and \<c>           = "\<lambda> e. cost_all ! e"
proof(unfold_locales, goal_cases)
  case (1 x y)
  show ?case by simp
next
  case (2 x y)
  show ?case by simp
next
  case 3
  show ?case by simp
next
  case 4
  show ?case using num_edges_gtr_0 by simp
next
  case (5 e)
  show ?case
  proof(cases "e < m + Kart")
    case True
    thus ?thesis using cap_all_nonneg[of e] by (auto simp add: zero_ereal_def)
  next
    case False
    thus ?thesis by simp
  qed
qed

text \<open>The augmented graph's vertex set @{term \<open>NSg.\<V>\<close>} --- the endpoint set of all @{term \<open>m + Kart\<close>}
      edges --- is exactly the arborescence vertex set @{term Varb} (@{term \<open>insert vcount (set vs_list)\<close>}):
      real edges contribute @{term \<open>set vs_list\<close>} (@{thm fst_snd_vs}), artificial edges contribute
      @{const vcount} together with their subjects, and @{thm Kart_pos} guarantees at least one
      artificial edge so that @{const vcount} itself is present. This is the identity that lets the
      @{locale cost_flow_network} vertex set and the @{term Sarb} arborescence share one carrier.\<close>

lemma NSg_verts: "NSg.\<V> = insert vcount Vseen"
proof -
  have dvs: "NSg.\<V> = (\<Union>e\<in>{0..<m+Kart}. {fst_all!e, snd_all!e})"
    by (auto simp: dVs_def NSg.make_pair_function)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> NSg.\<V>"
    then obtain e where e: "e < m+Kart" and xe: "x = fst_all!e \<or> x = snd_all!e"
      using dvs by auto
    show "x \<in> insert vcount Vseen"
    proof (cases "e < m")
      case True
      have fe: "fst_all!e = fst_list!e" and se: "snd_all!e = snd_list!e"
        using True by (simp_all add: fst_all_real snd_all_real)
      have "fst_list!e \<in> set fst_list \<union> set snd_list" using True by (metis UnI1 len_fst_list_m nth_mem)
      moreover have "snd_list!e \<in> set fst_list \<union> set snd_list" using True by (metis UnI2 len_snd_list_m nth_mem)
      ultimately have "fst_list!e \<in> Vseen" "snd_list!e \<in> Vseen"
        using edged_in_V V_sub_Vseen by auto
      thus ?thesis using xe fe se by auto
    next
      case False
      define k where "k = e - m"
      have kK: "k < Kart" using e False by (simp add: k_def)
      have em: "e = m + k" using False by (simp add: k_def)
      have "fst_all!e = ds_afst (build_tree acyc_flow)!k" using kK em by (simp add: fst_all_art)
      moreover have "snd_all!e = ds_asnd (build_tree acyc_flow)!k" using kK em by (simp add: snd_all_art)
      moreover have "ds_afst (build_tree acyc_flow)!k \<in> insert vcount Vseen
                     \<and> ds_asnd (build_tree acyc_flow)!k \<in> insert vcount Vseen"
        using build_tree_tail_sub kK by (simp add: tail_sub_def Kart_def seen_set_build_tree)
      ultimately show ?thesis using xe by auto
    qed
  next
    fix x assume "x \<in> insert vcount Vseen"
    hence "x = vcount \<or> x \<in> Vseen" by simp
    thus "x \<in> NSg.\<V>"
    proof
      assume xv: "x = vcount"
      have k0: "0 < Kart" by (rule Kart_pos)
      have tok: "tail_edge_ok (build_tree acyc_flow) 0" using build_tree_tail_content k0 by (simp add: tail_content_def Kart_def)
      then obtain subj where subj: "subj < vcount"
        and af: "ds_afst (build_tree acyc_flow)!0 = (if art_dir subj then subj else vcount)"
        and as: "ds_asnd (build_tree acyc_flow)!0 = (if art_dir subj then vcount else subj)"
        by (auto simp: tail_edge_ok_def)
      have am: "fst_all!m = ds_afst (build_tree acyc_flow)!0" using k0 fst_all_art[of 0] by simp
      have sm: "snd_all!m = ds_asnd (build_tree acyc_flow)!0" using k0 snd_all_art[of 0] by simp
      have "vcount = fst_all!m \<or> vcount = snd_all!m"
        using af as am sm by (cases "art_dir subj") auto
      moreover have "m \<in> {0..<m+Kart}" using k0 by simp
      ultimately show ?thesis using dvs xv by auto
    next
      assume "x \<in> Vseen"
      hence xed: "x \<in> set fst_list \<union> set snd_list" using Vseen_eq_V V_orig_eq by simp
      have "\<exists>e<m. x = fst_all!e \<or> x = snd_all!e"
      proof -
        from xed have "x \<in> set fst_list \<or> x \<in> set snd_list" by blast
        thus ?thesis
        proof
          assume "x \<in> set fst_list"
          then obtain e where e0: "e < length fst_list" and ex: "fst_list!e = x"
            by (auto simp: in_set_conv_nth)
          have e: "e < m" using e0 len_fst_list_m by simp
          hence "x = fst_all!e" using fst_all_real[OF e] ex by simp
          thus ?thesis using e by auto
        next
          assume "x \<in> set snd_list"
          then obtain e where e0: "e < length snd_list" and ex: "snd_list!e = x"
            by (auto simp: in_set_conv_nth)
          have e: "e < m" using e0 len_snd_list_m by simp
          hence "x = snd_all!e" using snd_all_real[OF e] ex by simp
          thus ?thesis using e by auto
        qed
      qed
      then obtain e where elt: "e < m" and xe: "x = fst_all!e \<or> x = snd_all!e" by blast
      have "e \<in> {0..<m+Kart}" using elt by simp
      thus ?thesis using dvs xe by auto
    qed
  qed
qed

lemma NSg_verts_Varb: "NSg.\<V> = Varb"
  using NSg_verts by (simp add: Varb_def)

end
end

