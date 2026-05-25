theory Bipartite_Alternating_Lists
  imports Alternating_Lists Undirected_Set_Graphs.Bipartite
begin

lemma bipartite_alternation:
  assumes "bipartite G X Y" "walk_betw G s p t"
  shows   "s \<in> X \<Longrightarrow> alt_list (\<lambda> x. x \<in> X) (\<lambda> x. x \<in> Y) p"
          "s \<in> Y \<Longrightarrow> alt_list (\<lambda> x. x \<in> Y) (\<lambda> x. x \<in> X) p"
  using assms(2)
proof(induction rule: induct_walk_betw , goal_cases)
  case (1 s)
  then show ?case 
    by (simp add: alt_list.intros(1,2))
next
  case (2 s)
  then show ?case
    by (simp add: alt_list.intros(1,2))
next
  case (3 x y p t)
  have XY: "x \<in> X" "y \<in> Y"
    using  3(1,5) assms(1) bipartite_edgeD(1) by fastforce+
  show ?case 
    by(auto intro!: 3(4) intro: alt_list.intros(2) simp add: XY)
next
  case (4 x y p t)
  have XY: "x \<in> Y" "y \<in> X"
    using  4(1,5) assms(1) bipartite_edgeD(2) by fastforce+
  show ?case 
    by(auto intro!: 4(3) intro: alt_list.intros(2) simp add: XY)
qed

lemma bipartite_ends_and_lengths:
  assumes "bipartite G X Y" "walk_betw G s p t"
  shows   "\<lbrakk>s \<in> X; even (length p)\<rbrakk> \<Longrightarrow> t \<in> Y"
    "\<lbrakk>s \<in> X; odd (length p)\<rbrakk> \<Longrightarrow> t \<in> X"
    "\<lbrakk>s \<in> Y; even (length p)\<rbrakk> \<Longrightarrow> t \<in> X"
    "\<lbrakk>s \<in> Y; odd (length p)\<rbrakk> \<Longrightarrow> t \<in> Y"
    "\<lbrakk>s \<in> X; t \<in> Y\<rbrakk> \<Longrightarrow> even (length p)"
    "\<lbrakk>s \<in> X; t \<in> X\<rbrakk> \<Longrightarrow> odd (length p)"
    "\<lbrakk>s \<in> Y; t \<in> X\<rbrakk> \<Longrightarrow> even (length p)"
    "\<lbrakk>s \<in> Y; t \<in> Y\<rbrakk> \<Longrightarrow> odd (length p)"
  using bipartite_alternation[OF assms]
    alternating_list_odd_last[of _ _ p]
    alternating_list_even_last[of _ _ p] assms(2)
    bipartite_vertex(1)[OF walk_endpoints(1) assms(1)] walk_symmetric[OF assms(2)] 
  by (fastforce simp add: walk_between_nonempty_pathD(4)[OF assms(2)])+
end