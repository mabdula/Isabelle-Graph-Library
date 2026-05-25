theory Parent_Map
  imports "HOL-Data_Structures.Map_Specs"  "HOL-Data_Structures.Set_Specs"
          Undirected_Set_Graphs.Directed_Undirected
begin

definition parent_spec::"('a \<Rightarrow> 'a option) \<Rightarrow> bool" where
  "parent_spec parent = wf {(x, y) |x y. (Some x = parent y)}"

locale parent_spec = 
  fixes parent::"'a \<Rightarrow> 'a option" and
    parent_rel::"'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

function (domintros) follow where
  "follow v = (case (parent v) of Some v' \<Rightarrow> v # (follow v') | _  \<Rightarrow> [v])"
  by pat_completeness auto

partial_function (tailrec) follow_impl_loop  where
  "follow_impl_loop v acc =  
  (case (parent v) of Some v' \<Rightarrow> (follow_impl_loop v' (v#acc)) 
     | _  \<Rightarrow> v#acc)"

lemma follow_dom_impl_same_loop:
  assumes "follow_dom v"
  shows   "follow_impl_loop v acc = rev (rev acc @ follow v)"
  apply(induction arbitrary: acc rule: follow.pinduct[OF assms(1)])
  apply(subst follow_impl_loop.simps)
  by(auto simp add: follow.psimps split: option.split)

definition "follow_impl v = rev (follow_impl_loop v Nil)"

lemma follow_dom_impl_same: "follow_dom v \<Longrightarrow> follow_impl v = follow v"
  by(auto simp add: follow_impl_def follow_dom_impl_same_loop)

lemmas [code] = follow_impl_def follow_impl_loop.simps

lemma assumes "parent v = None"
  shows "follow_dom v"
  apply(rule follow.domintros)
  using assms
  by auto

lemma assumes "parent v' = Some v" "follow_dom v"
  shows "Wellfounded.accp follow_rel v'"
  apply(rule follow.domintros)
  using assms
  by auto

lemma wfP_follow_rel:
  assumes "wfP follow_rel"
  shows "follow_dom v"
  using accp_wfpD[OF assms]
  by blast

lemma wf_follow_rel:
  assumes "wf {(x,y) | x y. follow_rel x y}"
  shows "follow_dom v"
  using wfP_follow_rel assms
  unfolding wfp_def
  by force

end

global_interpretation parent_spec_i: parent_spec parent parent_rel for parent parent_rel
  defines follow_impl = parent_spec_i.follow_impl
    and follow_impl_loop = parent_spec_i.follow_impl_loop
    and follow = parent_spec_i.follow
  done

value "follow_impl (\<lambda> (x::nat). if x = 3 then Some 2 
                                else if x = 2 then Some 1 
                                else if x = 1 then Some 0 
                                else None) 
                   3"


locale parent = 
  parent_spec+
  assumes parent_rel:
    "parent_spec parent"
begin

lemma parent_eq_follow_rel: "follow_rel = (\<lambda>v' v. Some v' = parent v)"
  unfolding parent_rel follow_rel.simps
  apply simp
  apply(rule HOL.ext)+
  by auto

lemma wf_found_rel:
  "wf {(x,y) | x y. follow_rel x y}"
  unfolding parent_eq_follow_rel
  using parent_rel[unfolded parent_spec_def]
  by simp

lemma follow_dom:
  "follow_dom v"
  using wf_found_rel wf_follow_rel
  by force

lemma follow_impl_is_follow:
  "follow_impl = follow"
  by(auto simp add: follow_dom_impl_same parent.follow_dom parent_axioms)

lemma follow_cons:
  "follow u = v # p \<Longrightarrow> v = u"
  by (auto simp: follow.psimps[OF follow_dom] split: option.splits)

lemma follow_cons_2:
  "follow v = v # v' # p \<Longrightarrow> follow v' = v' # p"
  "follow v = v # v' # p \<Longrightarrow> parent v = Some v'"
  by(cases "parent v"; simp add: follow.psimps[OF follow_dom]; clarsimp split: option.splits)+

lemma follow_append:
  "follow v = p @ u # p' \<Longrightarrow> follow u = u # p'"
proof(induction "follow v" arbitrary: v p)
  case nil1: Nil
  then show ?case 
    by auto
next
  case cons1: (Cons v' follow_v')
  then have "v' = v"
    using follow_cons
    by metis
  show ?case
  proof (cases follow_v')
    case nil2: Nil
    then have "v = u" "p = []"
      using cons1 \<open>v' = v\<close>
      by (simp add: Cons_eq_append_conv)+
    then show ?thesis
      using cons1
      by auto
  next
    case cons2: (Cons v'' follow_v'')
    then show ?thesis
      using cons1
      by (metis \<open>v' = v\<close> append_eq_Cons_conv follow_cons_2 list.sel(1))
  qed
qed

lemma from_tree:
  assumes "follow v1 = p1 @ u # p1'" "follow v2 = p2 @ u # p2'"
  shows "p1' = p2'"
  using follow_append follow_append
    assms parent_axioms
  by fastforce

lemma follow_psimps:
  "follow v = (case parent v of None \<Rightarrow> [v] | Some v' \<Rightarrow> v # follow v')"
  using follow.psimps[OF follow_dom] .

lemma follow_hd: "hd (follow  v) = v"
  by(auto simp add:  follow_psimps split: option.split)

lemma follow_nempty: "follow v \<noteq> []"
  apply(subst follow.psimps[OF follow_dom])
  by(auto simp add: option.case_eq_if split: if_splits)

lemma follow_None:
  "follow v = [v'] \<Longrightarrow> parent v = None"
  apply(subst (asm) follow.psimps[OF follow_dom])
  by(auto simp add: follow_nempty option.case_eq_if split: if_splits)

lemma nin_ancestors: 
 "\<lbrakk>\<forall>v2\<in>set (follow v1). parent v2 \<noteq> Some v3; v3 \<noteq> v1\<rbrakk> \<Longrightarrow>  v3 \<notin> set (follow v1)"
proof(induction rule: follow.pinduct[OF follow_dom[of v1]])
  case (1 v)
  then show ?case
  proof (cases "parent v")
    case None
    then show ?thesis
      using 1
      by (simp add: follow_psimps)
  next
    case (Some a)
    then show ?thesis
      using 1
      using follow_psimps by auto
  qed
qed

lemma follow_walk_betw:
  "walk_betw {{x, y}| x y. follow_rel x y} v (follow v) (last (follow v)) \<or> 
   follow v = [v]"
proof(induction rule: follow.pinduct[OF follow_dom])
  case (1 v)
  show ?case 
  proof(cases "parent v")
    case None
    then show ?thesis 
      by (simp add: follow_psimps)
  next
    case (Some u)
    have one_step: "walk_betw { {x, y} | x y. (follow_rel x y)} v [v, u] u"
      using Some
      by(fastforce intro!: edges_are_walks simp add: parent_eq_follow_rel)
    show ?thesis 
      using 1(2)[OF Some]
      by(auto simp add: follow_psimps[of v, simplified Some, simplified]
          intro: walk_transitive_3[OF _ one_step, simplified] one_step)
  qed
qed
  
lemma follow_valk_bet:
  "vwalk_bet {(y, x)| x y. follow_rel x y} v (follow v) (last (follow v)) \<or> 
   follow v = [v]"
proof(induction rule: follow.pinduct[OF follow_dom])
  case (1 v)
  show ?case 
  proof(cases "parent v")
    case None
    then show ?thesis 
      by (simp add: follow_psimps)
  next
    case (Some u)
    have one_step: "vwalk_bet { (y, x) | x y. (follow_rel x y)} v [v, u] u"
      using Some
      by(force intro!: edges_are_vwalk_bet simp add: parent_eq_follow_rel)
    show ?thesis 
      using 1(2)[OF Some] hd_of_vwalk_bet one_step
      by(force simp add: follow_psimps[of v, simplified Some, simplified])
  qed
qed

lemma follow_R_one_star:
  assumes "follow v = p1@[x]@p2"
  shows "(v, x) \<in> {(x, y) | x y. (follow_rel y x)}\<^sup>*"
  using assms
proof(induction arbitrary:  x p1 p2 rule: follow.pinduct[OF follow_dom])
  case (1 v x p1 p2)
  show ?case 
  proof(cases p1)
    case Nil
    hence "v = x"
      using "1.prems" follow_cons by auto
    then show ?thesis by simp
  next
    case (Cons a list)
    show ?thesis
    proof(cases "parent v")
      case None
      then show ?thesis 
        using 1(3)
        by(auto simp add: follow_psimps[of v] append_eq_Cons_conv Cons_eq_append_conv)
    next
      case (Some u)
      have "(u, x) \<in> {(x, y) | x y. (follow_rel y x)}\<^sup>*"
        using Some Cons 1(3)
        by(force intro!:  1(2)[of u list x p2]  simp add: follow_psimps[of v])
      moreover have "(v, u) \<in> {(x, y) | x y. (follow_rel y x)}\<^sup>*" 
        using Some by(auto simp add: parent_eq_follow_rel)
      ultimately show ?thesis by auto
    qed
  qed
qed

lemma follow_R_two_plus:
  assumes "follow v = p1@[x]@p2@[y]@p3"
  shows "(x, y) \<in> {(x, y) | x y. (follow_rel y x)}\<^sup>+"
  using assms
proof(induction arbitrary:  x p1 p2 p2 y rule: follow.pinduct[OF follow_dom])
  case (1 v)
  show ?case 
  proof(cases "parent v")
    case None
    then show ?thesis 
      using 1(3)
      by (simp add: follow_psimps)
  next
    case (Some u)
    show ?thesis
    proof(cases p1)
      case Nil
      hence "v = x"
        using "1.prems" follow_cons by auto
      moreover hence "(u, y) \<in> {(x, y) | x y. (follow_rel y x)}\<^sup>*"
        using 1(3) Some Nil 
        by(force intro!:  follow_R_one_star[of u "p2" y p3] simp add:  follow_psimps[of x])
      moreover have "(v, u)\<in> {(x, y) | x y. (follow_rel y x)}\<^sup>+" 
        by (simp add: Some parent_eq_follow_rel trancl.r_into_trancl)
      ultimately show ?thesis by simp
    next
      case (Cons a list)
      show ?thesis 
        using Cons 1(3) Some
        by(force intro!: 1(2)[OF Some, of list x p2 y] simp add:  follow_psimps[of v])
    qed
  qed
qed

lemma follow_distinct: "distinct (follow v)"
proof(rule ccontr, goal_cases)
  case 1
  then obtain p1 x p2 p3 where split: "follow v = p1@[x]@p2@[x]@p3"
    using not_distinct_decomp by blast
  hence "follow x = [x]@p2@[x]@p3" 
    by (simp add: follow_append)
  moreover have "follow x = [x]@p3"
    by (metis append.assoc append_Cons calculation follow_append)
  ultimately show False 
    by simp
qed

end

lemma follow_cong:
  assumes "parent par" "parent_spec.follow_dom par v"
  shows "\<lbrakk>(\<forall>v'\<in>set(parent_spec.follow par v). par v' = par' v'); parent par'\<rbrakk>
          \<Longrightarrow> parent_spec.follow par v = parent_spec.follow par' v"
  using assms(2)
proof(induction rule: parent_spec.follow.pinduct[OF assms(2)])
  case (1 v)
  then show ?case
  proof(cases "par v")
    case None
    then show ?thesis
      apply( simp add: parent.follow_psimps[OF 1(4)])
      by (metis (mono_tags, lifting) "1.hyps" "1.prems"(1) assms(1) list.set_intros(1) option.case_eq_if 
          parent_spec.follow.psimps)
  next
    case (Some a)
    have "\<forall>v\<in>set (parent_spec.follow par a). par v = par' v"
      by (simp add: "1.prems"(1) "1.prems"(3) Some assms(1) parent_spec.follow.psimps)
    moreover have "parent_spec.follow_dom par a"
      by (simp add: assms(1) parent.follow_dom)
    ultimately have "parent_spec.follow par a = parent_spec.follow par' a" 
      using 1
      using Some by blast
    moreover have "par' v = Some a"
      using "1.hyps" "1.prems"(1) Some assms(1) parent_spec.follow.psimps by fastforce
    ultimately show ?thesis
      using 1(4) Some
      by(auto simp add: parent.follow_psimps[OF assms(1)] parent.follow_psimps[OF 1(4)] )
  qed
qed

lemma v2_nin_ancestors:
  assumes "parent par" "\<forall>v''. par v'' \<noteq> Some v2" "v2 \<noteq> v"
  shows "\<forall>v'\<in>set(parent_spec.follow par v). v' \<noteq> v2"
  using assms
proof(induction v rule: parent_spec.follow.pinduct[OF parent.follow_dom[OF assms(1)]])
  case (1 v)
  show ?case
  proof(cases "par v")
    case None
    then show ?thesis
      using 1(5)
      by(simp add: parent.follow_psimps[OF 1(3)])
  next
    case (Some a)
    have "\<forall>v\<in>set (parent_spec.follow par a). v \<noteq> v2"
      using "1.IH" Some assms(1) assms(2) by blast
    then show ?thesis
      using "1.hyps" "1.prems"(3) Some assms(1) parent_spec.follow.psimps by fastforce
  qed    
qed

lemma ancestors_unaffected_1:
  assumes "parent par" "\<forall>v'\<in>set(parent_spec.follow par v). v' \<noteq> v2"
  and f': "f' = (f(v2 \<mapsto> v1))"
  shows "\<forall>v'\<in>set(parent_spec.follow par v). f v' = f' v'"
  using assms
proof(induction v rule: parent_spec.follow.pinduct[OF  parent.follow_dom[OF assms(1)]])
  case (1 v)
  show ?case
  proof(cases "par v")
    case None
    then show ?thesis
      using 1
      by( simp add: parent.follow_psimps[OF 1(3)])
  next
    case (Some a)
    then have "\<forall>v\<in>set (parent_spec.follow par a). f v = f' v"
      apply(intro 1)
      using 1(4)
      by (simp add: f' parent.follow_psimps[OF 1(3)])+
    then show ?thesis
      by (simp add: "1.prems"(2) "1.prems"(3))
  qed
qed

lemma no_children_not_in_follow:
  assumes "parent par" "\<forall>v''. par v'' \<noteq> Some v2" "v2 \<noteq> v"
  and par': "par' = (par(v2 \<mapsto> v1))"
  shows "\<forall>v'\<in>set(parent_spec.follow par v). par v' = par' v'"
  using assms
proof(induction  rule: parent_spec.follow.pinduct[OF parent.follow_dom[OF assms(1)]])
  case (1 v)
  show ?case
  proof(cases "par v")
    case None
    then show ?thesis
      using 1
      by( simp add: parent.follow_psimps[OF 1(3)])
  next
    case (Some a)
    have "\<forall>v\<in>set (parent_spec.follow par a). par v = par' v"
      using "1.IH" Some assms(1) assms(2) par' by blast
    then show ?thesis
      using "1.hyps" "1.prems"(3) Some assms(1) par' parent_spec.follow.psimps by fastforce
  qed    
qed

lemma wf_par':
  assumes wf: "parent_spec par" 
  and par': "par' = par(v2 := Some v1, v3 := Some v2)"
  and neq: "v1 \<noteq> v2" "v2 \<noteq> v3" "v1 \<noteq> v3"
  and no_ances: "\<forall>v. par v \<noteq> Some v2" "\<forall>v. par v \<noteq> Some v3"
  and no_par: "par v2 = None" "par v3 = None"
  shows "parent_spec par'" (is ?g1) "parent_spec (par(v2 := Some v1))" (is ?g2)
proof-
  have "(v2, v1) \<notin> {(x,y) | x y. (Some x = par y)}\<^sup>*"
    using neq(1) no_ances(1)
    apply clarsimp
    by (metis (mono_tags, lifting) converse_rtranclE mem_Collect_eq old.prod.case)
  then have wf_v2_v1: "wf (insert (v1, v2) {(x,y) | x y. (Some x = par y)})"
    using wf[unfolded parent_spec_def] by blast
  moreover have "{(x, y) |x y. Some x = (par(v2 \<mapsto> v1)) y} = (insert (v1, v2) {(x, y) |x y. Some x = par y})"
    using neq(1) no_par
    by auto
  ultimately show ?g2
    unfolding parent_spec_def
    by simp
  have "(v3, v2) \<notin> {(x,y) | x y. (Some x = par y)}\<^sup>*"
    using neq(2) no_ances(2)
    apply clarsimp
    by (metis (mono_tags, lifting) converse_rtranclE mem_Collect_eq old.prod.case)
  moreover have "(v3, v2) \<notin>  {(x, y). (x, v1) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>* \<and> (v2, y) \<in> {(x,y) | x y. (Some x = par y)}\<^sup>*}"
    using neq(3) no_ances(2)
    apply clarsimp
    by (metis (mono_tags, lifting) converse_rtranclE mem_Collect_eq old.prod.case)
  ultimately have "(v3, v2) \<notin> (insert (v1, v2) {(x,y) | x y. (Some x = par y)})\<^sup>*"
    unfolding rtrancl_insert
    by simp
  then have "wf (insert (v2, v3) (insert (v1, v2) {(x,y) | x y. (Some x = par y)}))"
    apply(subst wf_insert)
    using wf_v2_v1
    by simp
  moreover have "{(x,y) | x y. (Some x = par' y)} = insert (v2, v3) (insert (v1, v2) {(x,y) | x y. (Some x = par y)})"
    using neq(1,2) no_par
    by(auto simp add: par')
  ultimately show ?g1
    unfolding parent_spec_def
    by simp
qed

lemma parent_specD:
  "parent_spec parent \<Longrightarrow> wf {(x, y) |x y. (Some x = parent y)}"
  and parent_specE:
  "parent_spec parent \<Longrightarrow> (wf {(x, y) |x y. (Some x = parent y)} \<Longrightarrow> P) \<Longrightarrow> P"
  and parent_specI:
  "wf {(x, y) |x y. (Some x = parent y)} \<Longrightarrow> parent_spec parent" for parent
  by(auto simp add: parent_spec_def)

end