theory Matching_Specs
  imports Matching
begin

section \<open>Read-only Access to a Matching\<close>

text \<open>The representation and invariant of a matching are abstract. Partner lookup returns
  the sentinel \<open>nil\<close> at a free vertex. The interface requires no update, allocation,
  augmentation, contraction or expansion operations.\<close>

locale Matching_Specs =
  fixes K :: "'v set" and nil :: 'v
    and matching_invar :: "'v set set \<Rightarrow> 'matching \<Rightarrow> bool"
    and matching_abstract :: "'matching \<Rightarrow> 'v set set"
    and get_partner :: "'matching \<Rightarrow> 'v \<Rightarrow> 'v"
  assumes nil: "nil \<notin> K"
    and matching: "\<And>G M. matching_invar G M \<Longrightarrow> graph_matching G (matching_abstract M)"
    and universe: "\<And>G M. matching_invar G M \<Longrightarrow> Vs G \<subseteq> K"
    and get_partner:
      "\<And>G M u v. matching_invar G M \<Longrightarrow>
       {u, v} \<in> matching_abstract M \<longleftrightarrow> get_partner M u = v \<and> v \<noteq> nil"
begin

lemma Vs_iff:
  assumes "matching_invar G M" "dblton_graph G"
  shows "v \<in> Vs (matching_abstract M) \<longleftrightarrow> get_partner M v \<noteq> nil"
proof
  assume "v \<in> Vs (matching_abstract M)"  then obtain e where edge: "e \<in> matching_abstract M" "v \<in> e"
    by (auto simp: Vs_def)
  have "e \<in> G"
    using matching[OF assms(1)] edge(1) by auto
  then obtain x y where "e = {x, y}"
    by (elim dblton_graphE[OF assms(2)])
  then obtain u where "{v, u} \<in> matching_abstract M"
    using edge by (auto simp: insert_commute)
then show "get_partner M v \<noteq> nil"
    by (simp add: get_partner[OF assms(1)])
next
  assume "get_partner M v \<noteq> nil"
  then have "{v, get_partner M v} \<in> matching_abstract M"
    by (simp add: get_partner[OF assms(1)])
  then show "v \<in> Vs (matching_abstract M)"
    by (rule edges_are_Vs)
qed

end

end
