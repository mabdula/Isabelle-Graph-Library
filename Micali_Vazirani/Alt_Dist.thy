theory Alt_Dist
  imports "Directed_Set_Graphs.enat_misc" Alternating_Lists.Alternating_Lists Directed_Set_Graphs.Dist
          "HOL-Library.Multiset" 
begin

provenance human

section \<open>Alternating Distances\<close>

subsection \<open>Alternating Distance from a vertex\<close>

named_theorems parity_simps

datatype parity = Even | Odd

definition of_parity[parity_simps]: "of_parity parity = (case parity of Even \<Rightarrow> even | Odd \<Rightarrow> odd)"

definition other_parity[parity_simps]: "other_parity parity = (case parity of Even \<Rightarrow> Odd | Odd \<Rightarrow> Even)"

definition next_alt_list_parity[parity_simps]: 
  "next_alt_list_parity prev_parity f P1 P2 = (case prev_parity of Even \<Rightarrow> f P1 P2 | Odd \<Rightarrow> f P2 P1)"

locale alt_dist =
  fixes P1 P2::"('a \<times> 'a) \<Rightarrow> bool"
begin

definition
  "alt_vwalk_bet parity G u p v =
     (Vwalk.vwalk_bet G u p v \<and> alt_list P1 P2 (edges_of_vwalk p) \<and> of_parity (other_parity parity) (length p))"

lemma alt_vwalk_betE: 
  "alt_vwalk_bet parity G u p v \<Longrightarrow>
    \<lbrakk>\<lbrakk>Vwalk.vwalk_bet G u p v; alt_list P1 P2 (edges_of_vwalk p); of_parity (other_parity parity) (length p)\<rbrakk> \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by (auto simp: alt_vwalk_bet_def)

lemma alt_vwalk_betI: 
  "\<lbrakk>Vwalk.vwalk_bet G u p v; alt_list P1 P2 (edges_of_vwalk p); of_parity (other_parity parity) (length p)\<rbrakk> 
    \<Longrightarrow> alt_vwalk_bet parity G u p v"
  by (auto simp: alt_vwalk_bet_def)

definition
  "alt_distance (parity:: parity) G u v = 
  (INF p. if alt_vwalk_bet parity G u p v
          then length p - 1
          else \<infinity>)"

lemma dist_le_odd_dist: "distance G u v \<le> alt_distance parity G u v"
  unfolding distance_def alt_distance_def
proof(rule INF_mono')
  fix p
  show "(if Vwalk.vwalk_bet G u p v then length p - 1 else \<infinity>)
          \<le> (if alt_vwalk_bet parity G u p v then length p - 1 else \<infinity>)"
    by (auto simp: alt_vwalk_bet_def)
qed

lemma alt_vwalk_bet_alt_dist:
  "\<lbrakk>alt_vwalk_bet parity G u p v\<rbrakk> \<Longrightarrow> 
     alt_distance parity G u v \<le> length p - 1"
  by (auto simp: alt_distance_def image_def alt_vwalk_bet_def
           intro!: complete_lattice_class.Inf_lower enat_ile)

lemma alt_vwalk_bet_subset:
  "\<lbrakk>alt_vwalk_bet parity G u p v; G \<subseteq> G'\<rbrakk> \<Longrightarrow> alt_vwalk_bet parity G' u p v"
  using vwalk_bet_subset
  by (auto simp: alt_vwalk_bet_def)

definition 
  "alt_reachable parity G u v = (\<exists>p. alt_vwalk_bet parity G u p v)"

lemma alt_reachable_vwalk_bet_iff:
  "alt_reachable parity G u v \<longleftrightarrow> (\<exists>p. alt_vwalk_bet parity G u p v)"
  by (auto simp: alt_reachable_def)

lemma alt_reachableE:
  "alt_reachable parity G u v \<Longrightarrow> \<lbrakk>\<And>p. alt_vwalk_bet parity G u p v \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: alt_reachable_def)

lemma alt_reachable_vwalk_betD:
  "alt_vwalk_bet parity G u p v \<Longrightarrow> alt_reachable parity G u v"
  using iffD2[OF alt_reachable_vwalk_bet_iff]
  by force

lemma alt_reachable_dist:
  "alt_reachable parity G u v \<Longrightarrow> alt_distance parity G u v < \<infinity>"
  apply(clarsimp simp add: alt_reachable_vwalk_bet_iff)
  by (auto simp: alt_distance_def image_def alt_vwalk_bet_def intro!: complete_lattice_class.Inf_lower enat_ile)

lemma alt_unreachable_dist:
  "\<not>alt_reachable parity G u v \<Longrightarrow> alt_distance parity G u v = \<infinity>"
proof-
  assume "\<not>alt_reachable parity G u v"
  hence "\<And>p. \<not> alt_vwalk_bet parity G u p v"
    by(auto simp: alt_reachable_def)
  thus "alt_distance parity G u v = \<infinity>"
    by(simp add: alt_distance_def)
qed

lemma alt_dist_reachable:
  "alt_distance parity G u v < \<infinity> \<Longrightarrow> alt_reachable parity G u v"
proof(rule ccontr)
  assume h: "alt_distance parity G u v < \<infinity>" "\<not> alt_reachable parity G u v"
  hence "alt_distance parity G u v = \<infinity>"
    by(intro alt_unreachable_dist)
  thus False
    using h(1) by simp
qed

lemma alt_reachable_dist_2:
  assumes "alt_reachable parity G u v"
  obtains p where "alt_vwalk_bet parity G u p v""alt_distance parity G u v = length p - 1"
proof-
  let ?f = "\<lambda>p. if alt_vwalk_bet parity G u p v then length p - 1 else (\<infinity>::enat)"
  obtain p0 where p0: "alt_vwalk_bet parity G u p0 v"
    using assms by(auto simp: alt_reachable_def)
  have dist_eq: "alt_distance parity G u v = Inf (range ?f)"
    by(simp add: alt_distance_def)
  have "Inf (range ?f) \<in> range ?f"
    by(rule wellorder_InfI[of "?f p0"]) auto
  then obtain p1 where p1: "Inf (range ?f) = ?f p1"
    by(fastforce simp: image_def)
  have "Inf (range ?f) \<le> ?f p0"
    by(rule wellorder_Inf_le1) auto
  also have "... < \<infinity>"
    using p0 by simp
  finally have "?f p1 < \<infinity>"
    using p1 by simp
  hence bet: "alt_vwalk_bet parity G u p1 v"
    by(auto split: if_splits)
  hence "alt_distance parity G u v = length p1 - 1"
    using dist_eq p1 by simp
  with bet show ?thesis
    using that by blast
qed

lemma alt_reachable_reachable_in_dVs:
  assumes "alt_reachable parity G u v"
  shows "reachable G u v"
  using assms
  by (auto elim!: alt_reachableE alt_vwalk_betE simp: reachable_vwalk_betD)

lemma alt_reachable_in_dVs:
  assumes "alt_reachable parity G u v"
  shows "u \<in> dVs G" "v \<in> dVs G"
  using reachable_in_dVs[OF alt_reachable_reachable_in_dVs[OF assms]]
  by auto

lemma alt_vwalk_bet_nonempty'[simp]: "\<not> alt_vwalk_bet parity E u [] v" 
  unfolding alt_vwalk_bet_def by simp

lemma hd_of_alt_vwalk_bet:
  "alt_vwalk_bet parity dG v p v' \<Longrightarrow> \<exists>p'. p = v # p'"
  by(auto elim!: alt_vwalk_betE simp: hd_of_vwalk_bet)

lemma hd_of_alt_vwalk_bet': 
  "alt_vwalk_bet parity dG v p v' \<Longrightarrow> v = hd p"
  by(auto elim!: alt_vwalk_betE simp: hd_of_vwalk_bet')

lemma hd_of_alt_vwalk_bet'': "alt_vwalk_bet parity dG u p v \<Longrightarrow> u \<in> set p"
  using hd_of_alt_vwalk_bet
  by force 

lemma last_of_alt_vwalk_bet: 
  "alt_vwalk_bet parity dG v p v' \<Longrightarrow> v' = last p"
  by(auto simp: neq_Nil_conv alt_vwalk_bet_def dest: last_of_vwalk_bet)

lemma last_of_alt_vwalk_bet': 
  "alt_vwalk_bet parity dG v p v' \<Longrightarrow> \<exists>p'. p = p' @ [v']"
  by(auto simp: alt_vwalk_bet_def dest: append_butlast_last_id[symmetric] last_of_vwalk_bet')

end

find_theorems name: edges_of_vwalk length

lemma alt_vwalk_bet_append_1:
  assumes "alt_dist.alt_vwalk_bet P1 P2 Even G u (p1 @ p2) v" "p1 \<noteq> []"
  shows                (*"alt_dist.alt_vwalk_bet P1 P2 parity' G u p1 (last p1)"*)
  "\<exists>parity'.
    alt_dist.alt_vwalk_bet P1 P2 parity' G u p1 (last p1) \<and>
    next_alt_list_parity parity' alt_dist.alt_vwalk_bet P1 P2 parity' G (last p1) (last p1 # p2) v"
proof-
  have walk: "Vwalk.vwalk_bet G u (p1 @ p2) v"
    and alt: "alt_list P1 P2 (edges_of_vwalk (p1 @ p2))"
    and len: "odd (length p1 + length p2)"
    using assms(1)
    by(auto elim!: alt_dist.alt_vwalk_betE simp: parity_simps)
  have walk_pre: "Vwalk.vwalk_bet G u p1 (last p1)"
    using assms(2) walk
    by(rule vwalk_bet_prefix_is_vwalk_bet)
  have walk_suf: "Vwalk.vwalk_bet G (last p1) (last p1 # p2) v"
  proof-
    have "Vwalk.vwalk_bet G u (butlast p1 @ (last p1 # p2)) v"
      using walk assms(2) by(simp add: append_butlast_last_cancel)
    from vwalk_bet_suffix_is_vwalk_bet[OF _ this]
    show ?thesis by simp
  qed
  have edges_split: "edges_of_vwalk (p1 @ p2) = edges_of_vwalk p1 @ edges_of_vwalk (last p1 # p2)"
    using assms(2)
    by(rule edges_of_vwalk_append_3)
  have alt_pre: "alt_list P1 P2 (edges_of_vwalk p1)"
    using alt_list_append_1[of P1 P2 "edges_of_vwalk p1" "edges_of_vwalk (last p1 # p2)"] alt
    by(simp add: edges_split)
  have len_pre: "length (edges_of_vwalk p1) + 1 = length p1"
    using assms(2)
    by(rule edges_of_vwalk_length')
  show ?thesis
  proof(cases "even (length p1)")
    case False
    hence even_edges_pre: "even (length (edges_of_vwalk p1))"
      using len_pre by presburger
    have alt_suf: "alt_list P1 P2 (edges_of_vwalk (last p1 # p2))"
      using alt[unfolded edges_split] even_edges_pre
      by(rule alt_list_split_1)
    have "alt_dist.alt_vwalk_bet P1 P2 Even G u p1 (last p1)"
      using walk_pre alt_pre False
      by(auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
    moreover have "alt_dist.alt_vwalk_bet P1 P2 Even G (last p1) (last p1 # p2) v"
      using walk_suf alt_suf len False
      by(auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
    ultimately show ?thesis
      by(auto simp: parity_simps intro!: exI[where x = Even])
  next
    case True
    hence odd_edges_pre: "odd (length (edges_of_vwalk p1))"
      using len_pre by presburger
    have alt_suf: "alt_list P2 P1 (edges_of_vwalk (last p1 # p2))"
      using alt[unfolded edges_split] odd_edges_pre
      by(rule alt_list_split_2)
    have "alt_dist.alt_vwalk_bet P1 P2 Odd G u p1 (last p1)"
      using walk_pre alt_pre True
      by(auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
    moreover have "alt_dist.alt_vwalk_bet P2 P1 Odd G (last p1) (last p1 # p2) v"
      using walk_suf alt_suf len True
      by(auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
    ultimately show ?thesis
      by(auto simp: parity_simps intro!: exI[where x = Odd])
  qed
qed

lemma alt_vwalk_bet_appendE_1:
  assumes "alt_dist.alt_vwalk_bet P1 P2 Even G u (p1 @ p2) v" "p1 \<noteq> []"
  obtains parity' where
    "alt_dist.alt_vwalk_bet P1 P2 parity' G u p1 (last p1)"
    "next_alt_list_parity parity' alt_dist.alt_vwalk_bet P1 P2 parity' G (last p1) (last p1 # p2) v"
  using alt_vwalk_bet_append_1[OF assms]
  by auto

lemma alt_vwalk_bet_append_1':
  assumes "alt_dist.alt_vwalk_bet P1 P2 Odd G u (p1 @ p2) v" "p1 \<noteq> []"
  shows                (*"alt_dist.alt_vwalk_bet P1 P2 parity' G u p1 (last p1)"*)
  "\<exists>parity'.
    alt_dist.alt_vwalk_bet P1 P2 parity' G u p1 (last p1) \<and>
    next_alt_list_parity parity' alt_dist.alt_vwalk_bet P1 P2 (other_parity parity') G (last p1) (last p1 # p2) v"
proof-
  have walk: "Vwalk.vwalk_bet G u (p1 @ p2) v"
    and alt: "alt_list P1 P2 (edges_of_vwalk (p1 @ p2))"
    and len: "even (length p1 + length p2)"
    using assms(1)
    by(auto elim!: alt_dist.alt_vwalk_betE simp: parity_simps)
  have walk_pre: "Vwalk.vwalk_bet G u p1 (last p1)"
    using assms(2) walk
    by(rule vwalk_bet_prefix_is_vwalk_bet)
  have walk_suf: "Vwalk.vwalk_bet G (last p1) (last p1 # p2) v"
  proof-
    have "Vwalk.vwalk_bet G u (butlast p1 @ (last p1 # p2)) v"
      using walk assms(2) by(simp add: append_butlast_last_cancel)
    from vwalk_bet_suffix_is_vwalk_bet[OF _ this]
    show ?thesis by simp
  qed
  have edges_split: "edges_of_vwalk (p1 @ p2) = edges_of_vwalk p1 @ edges_of_vwalk (last p1 # p2)"
    using assms(2)
    by(rule edges_of_vwalk_append_3)
  have alt_pre: "alt_list P1 P2 (edges_of_vwalk p1)"
    using alt_list_append_1[of P1 P2 "edges_of_vwalk p1" "edges_of_vwalk (last p1 # p2)"] alt
    by(simp add: edges_split)
  have len_pre: "length (edges_of_vwalk p1) + 1 = length p1"
    using assms(2)
    by(rule edges_of_vwalk_length')
  show ?thesis
  proof(cases "even (length p1)")
    case False
    hence even_edges_pre: "even (length (edges_of_vwalk p1))"
      using len_pre by presburger
    have alt_suf: "alt_list P1 P2 (edges_of_vwalk (last p1 # p2))"
      using alt[unfolded edges_split] even_edges_pre
      by(rule alt_list_split_1)
    have "alt_dist.alt_vwalk_bet P1 P2 Even G u p1 (last p1)"
      using walk_pre alt_pre False
      by(auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
    moreover have "alt_dist.alt_vwalk_bet P1 P2 Odd G (last p1) (last p1 # p2) v"
      using walk_suf alt_suf len False
      by(auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
    ultimately show ?thesis
      by(auto simp: parity_simps intro!: exI[where x = Even])
  next
    case True
    hence odd_edges_pre: "odd (length (edges_of_vwalk p1))"
      using len_pre by presburger
    have alt_suf: "alt_list P2 P1 (edges_of_vwalk (last p1 # p2))"
      using alt[unfolded edges_split] odd_edges_pre
      by(rule alt_list_split_2)
    have "alt_dist.alt_vwalk_bet P1 P2 Odd G u p1 (last p1)"
      using walk_pre alt_pre True
      by(auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
    moreover have "alt_dist.alt_vwalk_bet P2 P1 Even G (last p1) (last p1 # p2) v"
      using walk_suf alt_suf len True
      by(auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
    ultimately show ?thesis
      by(auto simp: parity_simps intro!: exI[where x = Odd])
  qed
qed

lemma alt_vwalk_bet_appendE_1':
  assumes "alt_dist.alt_vwalk_bet P1 P2 Odd G u (p1 @ p2) v" "p1 \<noteq> []"
  obtains parity' where
  "alt_dist.alt_vwalk_bet P1 P2 parity' G u p1 (last p1)"
  "next_alt_list_parity parity' alt_dist.alt_vwalk_bet P1 P2 (other_parity parity') G (last p1) (last p1 # p2) v"
  using alt_vwalk_bet_append_1'[OF assms]
  by auto

lemma alt_vwalk_bet_append_2:
  assumes
    "alt_dist.alt_vwalk_bet P1 P2 parity G u p1 (last p1)"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G (last p1) (last p1 # p2) v"
    "p1 \<noteq> []"
  shows "alt_dist.alt_vwalk_bet P1 P2 Even G u (p1 @ p2) v"
proof(cases parity)
  case Even
  have walk_pre: "Vwalk.vwalk_bet G u p1 (last p1)"
    and alt_pre: "alt_list P1 P2 (edges_of_vwalk p1)"
    and len_pre: "odd (length p1)"
    using assms(1)
    by(auto elim!: alt_dist.alt_vwalk_betE simp: Even parity_simps)
  have walk_suf: "Vwalk.vwalk_bet G (last p1) (last p1 # p2) v"
    and alt_suf: "alt_list P1 P2 (edges_of_vwalk (last p1 # p2))"
    and len_suf: "even (length p2)"
    using assms(2)
    by(auto elim!: alt_dist.alt_vwalk_betE simp: Even parity_simps)
  have walk_all: "Vwalk.vwalk_bet G u (p1 @ p2) v"
    using vwalk_bet_transitive[OF walk_pre walk_suf]
    by simp
  have edges_split: "edges_of_vwalk (p1 @ p2) = edges_of_vwalk p1 @ edges_of_vwalk (last p1 # p2)"
    using assms(3)
    by(rule edges_of_vwalk_append_3)
  have len_pre_edges: "length (edges_of_vwalk p1) + 1 = length p1"
    using assms(3)
    by(rule edges_of_vwalk_length')
  have even_edges_pre: "even (length (edges_of_vwalk p1))"
    using len_pre len_pre_edges by presburger
  have alt_all: "alt_list P1 P2 (edges_of_vwalk (p1 @ p2))"
    unfolding edges_split
    by(rule alt_list_append_3[OF alt_pre alt_suf even_edges_pre])
  have len_all: "odd (length (p1 @ p2))"
    using len_pre len_suf by simp
  show ?thesis
    using walk_all alt_all len_all
    by(auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
next
  case Odd
  have walk_pre: "Vwalk.vwalk_bet G u p1 (last p1)"
    and alt_pre: "alt_list P1 P2 (edges_of_vwalk p1)"
    and len_pre: "even (length p1)"
    using assms(1)
    by(auto elim!: alt_dist.alt_vwalk_betE simp: Odd parity_simps)
  have walk_suf: "Vwalk.vwalk_bet G (last p1) (last p1 # p2) v"
    and alt_suf: "alt_list P2 P1 (edges_of_vwalk (last p1 # p2))"
    and len_suf: "odd (length p2)"
    using assms(2)
    by(auto elim!: alt_dist.alt_vwalk_betE simp: Odd parity_simps)
  have walk_all: "Vwalk.vwalk_bet G u (p1 @ p2) v"
    using vwalk_bet_transitive[OF walk_pre walk_suf]
    by simp
  have edges_split: "edges_of_vwalk (p1 @ p2) = edges_of_vwalk p1 @ edges_of_vwalk (last p1 # p2)"
    using assms(3)
    by(rule edges_of_vwalk_append_3)
  have len_pre_edges: "length (edges_of_vwalk p1) + 1 = length p1"
    using assms(3)
    by(rule edges_of_vwalk_length')
  have odd_edges_pre: "odd (length (edges_of_vwalk p1))"
    using len_pre len_pre_edges by presburger
  have alt_all: "alt_list P1 P2 (edges_of_vwalk (p1 @ p2))"
    unfolding edges_split
    by(rule alt_list_append_2[OF alt_pre alt_suf odd_edges_pre])
  have len_all: "odd (length (p1 @ p2))"
    using len_pre len_suf by simp
  show ?thesis
    using walk_all alt_all len_all
    by(auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
qed

lemma alt_vwalk_bet_append_3:
  assumes 
    "alt_dist.alt_vwalk_bet P1 P2 parity G u p1 (last p1)"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G (last p1) (last p1 # p2) v"
    "p1 \<noteq> []"
  shows "alt_dist.alt_vwalk_bet P1 P2 Odd G u (p1 @ p2) v"
proof(cases parity)
  case Even
  have walk_pre: "Vwalk.vwalk_bet G u p1 (last p1)"
    and alt_pre: "alt_list P1 P2 (edges_of_vwalk p1)"
    and len_pre: "odd (length p1)"
    using assms(1)
    by(auto elim!: alt_dist.alt_vwalk_betE simp: Even parity_simps)
  have walk_suf: "Vwalk.vwalk_bet G (last p1) (last p1 # p2) v"
    and alt_suf: "alt_list P1 P2 (edges_of_vwalk (last p1 # p2))"
    and len_suf: "odd (length p2)"
    using assms(2)
    by(auto elim!: alt_dist.alt_vwalk_betE simp: Even parity_simps)
  have walk_all: "Vwalk.vwalk_bet G u (p1 @ p2) v"
    using vwalk_bet_transitive[OF walk_pre walk_suf]
    by simp
  have edges_split: "edges_of_vwalk (p1 @ p2) = edges_of_vwalk p1 @ edges_of_vwalk (last p1 # p2)"
    using assms(3)
    by(rule edges_of_vwalk_append_3)
  have len_pre_edges: "length (edges_of_vwalk p1) + 1 = length p1"
    using assms(3)
    by(rule edges_of_vwalk_length')
  have even_edges_pre: "even (length (edges_of_vwalk p1))"
    using len_pre len_pre_edges by presburger
  have alt_all: "alt_list P1 P2 (edges_of_vwalk (p1 @ p2))"
    unfolding edges_split
    by(rule alt_list_append_3[OF alt_pre alt_suf even_edges_pre])
  have len_all: "even (length (p1 @ p2))"
    using len_pre len_suf by simp
  show ?thesis
    using walk_all alt_all len_all
    by(auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
next
  case Odd
  have walk_pre: "Vwalk.vwalk_bet G u p1 (last p1)"
    and alt_pre: "alt_list P1 P2 (edges_of_vwalk p1)"
    and len_pre: "even (length p1)"
    using assms(1)
    by(auto elim!: alt_dist.alt_vwalk_betE simp: Odd parity_simps)
  have walk_suf: "Vwalk.vwalk_bet G (last p1) (last p1 # p2) v"
    and alt_suf: "alt_list P2 P1 (edges_of_vwalk (last p1 # p2))"
    and len_suf: "even (length p2)"
    using assms(2)
    by(auto elim!: alt_dist.alt_vwalk_betE simp: Odd parity_simps)
  have walk_all: "Vwalk.vwalk_bet G u (p1 @ p2) v"
    using vwalk_bet_transitive[OF walk_pre walk_suf]
    by simp
  have edges_split: "edges_of_vwalk (p1 @ p2) = edges_of_vwalk p1 @ edges_of_vwalk (last p1 # p2)"
    using assms(3)
    by(rule edges_of_vwalk_append_3)
  have len_pre_edges: "length (edges_of_vwalk p1) + 1 = length p1"
    using assms(3)
    by(rule edges_of_vwalk_length')
  have odd_edges_pre: "odd (length (edges_of_vwalk p1))"
    using len_pre len_pre_edges by presburger
  have alt_all: "alt_list P1 P2 (edges_of_vwalk (p1 @ p2))"
    unfolding edges_split
    by(rule alt_list_append_2[OF alt_pre alt_suf odd_edges_pre])
  have len_all: "even (length (p1 @ p2))"
    using len_pre len_suf by simp
  show ?thesis
    using walk_all alt_all len_all
    by(auto simp: alt_dist.alt_vwalk_bet_def parity_simps)
qed

lemma alternating_list_even_last:
  assumes "alt_dist.alt_vwalk_bet P1 P2 Even G u p v" "length p \<ge> 2"
  shows "P2 (last (edges_of_vwalk p))"
  using assms
  apply(elim alt_dist.alt_vwalk_betE)
  apply(auto dest!: alternating_list_even_last simp: parity_simps edges_of_vwalk_length)
  apply(auto simp: eval_nat_numeral Suc_le_length_iff)
  done

lemma alternating_list_odd_last:
  assumes "alt_dist.alt_vwalk_bet P1 P2 Odd G u p v" "length p \<ge> 2"
  shows "P1 (last (edges_of_vwalk p))"
  using assms
  apply(elim alt_dist.alt_vwalk_betE)
  by(auto dest!: alternating_list_odd_last simp: parity_simps edges_of_vwalk_length)

lemma alt_triangle_ineq_reachable_1: 
  assumes "alt_dist.alt_reachable P1 P2 parity G u v" "next_alt_list_parity parity alt_dist.alt_reachable P1 P2 (other_parity parity) G v w"
  shows "alt_dist.alt_distance P1 P2 Odd G u w \<le> 
           alt_dist.alt_distance P1 P2 parity G u v + next_alt_list_parity parity alt_dist.alt_distance P1 P2 (other_parity parity) G v w"
proof-
  obtain p q
    where p_q: "alt_dist.alt_vwalk_bet P1 P2 parity G u p v"
               "alt_dist.alt_distance P1 P2 parity G u v = length p - 1"
          "(next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2) (other_parity parity) G v q w"
          "next_alt_list_parity parity alt_dist.alt_distance P1 P2 (other_parity parity) G v w = length q - 1"
    using assms
    by (cases parity) (auto elim!: alt_dist.alt_reachable_dist_2 simp: parity_simps)
  have "alt_dist.alt_vwalk_bet P1 P2 Odd G u (p @ tl q) w"
  proof-
    have q_ne: "q \<noteq> []"
      using p_q(3)
      by(cases parity)
        (auto elim!: alt_dist.alt_vwalk_betE simp: parity_simps vwalk_bet_def)
    have q_hd: "hd q = v"
      using p_q(3)
      by(cases parity)
        (auto dest: alt_dist.hd_of_alt_vwalk_bet' simp: parity_simps)
    have q_shape: "q = v # tl q"
      using q_ne q_hd
      by(cases q) auto
    have p_last: "v = last p"
      by(rule alt_dist.last_of_alt_vwalk_bet[OF p_q(1)])
    have p_ne: "p \<noteq> []"
      using p_q(1)
      by(auto elim!: alt_dist.alt_vwalk_betE simp: vwalk_bet_def)
    have p_bet: "alt_dist.alt_vwalk_bet P1 P2 parity G u p (last p)"
      using p_q(1)
      by(simp add: p_last[symmetric])
    have suf_bet: "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G (last p) (last p # tl q) w"
      using p_q(3)
      by(simp add: p_last[symmetric] q_shape[symmetric])
    show ?thesis
      by(rule alt_vwalk_bet_append_3[OF p_bet suf_bet p_ne])
  qed
  hence "alt_dist.alt_distance P1 P2 Odd G u w \<le> length (p @ tl q) - 1"
    by(intro alt_dist.alt_vwalk_bet_alt_dist) auto
  moreover have "length (p @ tl q) = length p + (length q - 1)"
    using p_q(2)
    by (cases q; auto)
  ultimately have "alt_dist.alt_distance P1 P2 Odd G u w \<le> length p + (length q - 1) - 1"
    by (auto simp: eval_nat_numeral)
  thus ?thesis
    using p_q
    by(cases p; auto elim!:alt_dist.alt_vwalk_betE simp add: eval_nat_numeral)
qed

lemma alt_triangle_ineq_reachable_2: 
  assumes "alt_dist.alt_reachable P1 P2 parity G u v" "next_alt_list_parity parity alt_dist.alt_reachable P1 P2 parity G v w"
  shows "alt_dist.alt_distance P1 P2 Even G u w \<le> 
           alt_dist.alt_distance P1 P2 parity G u v + next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G v w"
proof-
  obtain p q
    where p_q: "alt_dist.alt_vwalk_bet P1 P2 parity G u p v"
               "alt_dist.alt_distance P1 P2 parity G u v = length p - 1"
          "(next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2) parity G v q w"
          "next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G v w = length q - 1"
    using assms
    by (cases parity) (auto elim!: alt_dist.alt_reachable_dist_2 simp: parity_simps)
  have "alt_dist.alt_vwalk_bet P1 P2 Even G u (p @ tl q) w"
  proof-
    have q_ne: "q \<noteq> []"
      using p_q(3)
      by(cases parity)
        (auto elim!: alt_dist.alt_vwalk_betE simp: parity_simps vwalk_bet_def)+
    have q_hd: "hd q = v"
      using p_q(3)
      by(cases parity)
        (auto dest: alt_dist.hd_of_alt_vwalk_bet' simp: parity_simps)
    have q_shape: "q = v # tl q"
      using q_ne q_hd
      by(cases q) auto
    have p_last: "v = last p"
      by(rule alt_dist.last_of_alt_vwalk_bet[OF p_q(1)])
    have p_ne: "p \<noteq> []"
      using p_q(1)
      by(auto elim!: alt_dist.alt_vwalk_betE simp: vwalk_bet_def)
    have p_bet: "alt_dist.alt_vwalk_bet P1 P2 parity G u p (last p)"
      using p_q(1)
      by(simp add: p_last[symmetric])
    have suf_bet: "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G (last p) (last p # tl q) w"
      using p_q(3)
      by(simp add: p_last[symmetric] q_shape[symmetric])
    show ?thesis
      by(rule alt_vwalk_bet_append_2[OF p_bet suf_bet p_ne])
  qed
  hence "alt_dist.alt_distance P1 P2 Even G u w \<le> length (p @ tl q) - 1"
    by(intro alt_dist.alt_vwalk_bet_alt_dist) auto
  moreover have "length (p @ tl q) = length p + (length q - 1)"
    using p_q(2)
    by (cases q; auto)
  ultimately have "alt_dist.alt_distance P1 P2 Even G u w \<le> length p + (length q - 1) - 1"
    by (auto simp: eval_nat_numeral)
  thus ?thesis
    using p_q
    by(cases p; auto elim!:alt_dist.alt_vwalk_betE simp add: eval_nat_numeral)
qed

lemma alt_triangle_ineq_1:
  "alt_dist.alt_distance P1 P2 Odd G u w \<le> 
           alt_dist.alt_distance P1 P2 parity G u v + next_alt_list_parity parity alt_dist.alt_distance P1 P2 (other_parity parity) G v w"
 proof(cases "alt_dist.alt_reachable P1 P2 parity G u v")
  case reach_u_v: True
  then show ?thesis
  proof(cases "next_alt_list_parity parity alt_dist.alt_reachable P1 P2 (other_parity parity) G v w")
    case reach_v_w: True
    then show ?thesis
      using alt_triangle_ineq_reachable_1[OF reach_u_v reach_v_w]
      by auto
  next
    case not_reach_v_w: False
    hence "next_alt_list_parity parity alt_dist.alt_distance P1 P2 (other_parity parity) G v w = \<infinity>"
      apply (cases parity)
      by (auto simp add: alt_dist.alt_unreachable_dist parity_simps)
    then show ?thesis
      by simp
  qed
next
  case not_reach_u_v: False
  hence "alt_dist.alt_distance P1 P2 parity G u v = \<infinity>"
    apply (cases parity)
    by (auto simp add: alt_dist.alt_unreachable_dist parity_simps)
  then show ?thesis
    by simp
qed

lemma alt_triangle_ineq_2:
  "alt_dist.alt_distance P1 P2 Even G u w \<le> 
           alt_dist.alt_distance P1 P2 parity G u v + next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G v w"
 proof(cases "alt_dist.alt_reachable P1 P2 parity G u v")
  case reach_u_v: True
  then show ?thesis
  proof(cases "next_alt_list_parity parity alt_dist.alt_reachable P1 P2 parity G v w")
    case reach_v_w: True
    then show ?thesis
      using alt_triangle_ineq_reachable_2[OF reach_u_v reach_v_w]
      by auto
  next
    case not_reach_v_w: False
    hence "next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G v w = \<infinity>"
      apply (cases parity)
      by (auto simp add: alt_dist.alt_unreachable_dist parity_simps)
    then show ?thesis
      by simp
  qed
next
  case not_reach_u_v: False
  hence "alt_dist.alt_distance P1 P2 parity G u v = \<infinity>"
    apply (cases parity)
    by (auto simp add: alt_dist.alt_unreachable_dist parity_simps)
  then show ?thesis
    by simp
qed


lemma distance_split_1:
  "\<lbrakk>alt_dist.alt_distance P1 P2 Even G u v \<noteq> \<infinity>; 
    alt_dist.alt_distance P1 P2 Even G u v =
      alt_dist.alt_distance P1 P2 parity G u w +
      next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G w v \<rbrakk> \<Longrightarrow>
       \<exists>w'. alt_dist.alt_reachable P1 P2 parity G u w' \<and>
            alt_dist.alt_distance P1 P2 parity G u w' = alt_dist.alt_distance P1 P2 parity G u w \<and>
            next_alt_list_parity parity alt_dist.alt_reachable P1 P2 parity G w' v \<and>
            next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G w' v = 
            next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G w v "
proof(goal_cases)
  case 1
  have both_fin: "alt_dist.alt_distance P1 P2 parity G u w \<noteq> \<infinity>"
    "next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G w v \<noteq> \<infinity>"
    using 1 by(auto simp: plus_eq_infty_iff_enat)
  have r1: "alt_dist.alt_reachable P1 P2 parity G u w"
    using both_fin(1) alt_dist.alt_unreachable_dist
    by force
  have r2: "next_alt_list_parity parity alt_dist.alt_reachable P1 P2 parity G w v"
    using both_fin(2) alt_dist.alt_unreachable_dist
    by(cases parity) (force simp: parity_simps)+
  show ?case
    using r1 r2
    by(intro exI[where x = w]) auto
qed

lemma alt_dist_inf: "v \<notin> dVs G \<Longrightarrow> alt_dist.alt_distance P1 P2 parity G u v = \<infinity>"
proof(rule ccontr, goal_cases)
  case 1
  hence "alt_dist.alt_reachable P1 P2 parity G u v"
    by(auto intro!: alt_dist.alt_dist_reachable)
  hence "v \<in>dVs G"
    by (simp add: alt_dist.alt_reachable_in_dVs(2))
  then show ?case
    using 1
    by auto
qed

lemma alt_dist_inf_2: "v \<notin> dVs G \<Longrightarrow> alt_dist.alt_distance P1 P2 parity G v u = \<infinity>"
proof(rule ccontr, goal_cases)
  case 1
  hence "alt_dist.alt_reachable P1 P2 parity G v u"
    by(auto intro!: alt_dist.alt_dist_reachable)
  hence "v \<in>dVs G"
    by (simp add: alt_dist.alt_reachable_in_dVs(1))
  then show ?case
    using 1
    by auto
qed

lemma alt_dist_eq: "\<lbrakk>\<And>p. alt_dist.alt_vwalk_bet P1 P2 parity G' u p v \<Longrightarrow> alt_dist.alt_vwalk_bet P1 P2 parity G u (map f p) v\<rbrakk> \<Longrightarrow>
                   alt_dist.alt_distance P1 P2 parity G u v \<le> alt_dist.alt_distance P1 P2 parity G' u v"
proof(goal_cases)
  case 1
  have "alt_dist.alt_distance P1 P2 parity G u v
          \<le> (if alt_dist.alt_vwalk_bet P1 P2 parity G' u p v then length p - 1 else \<infinity>)" for p
  proof(cases "alt_dist.alt_vwalk_bet P1 P2 parity G' u p v")
    case True
    have "alt_dist.alt_distance P1 P2 parity G u v \<le> length (map f p) - 1"
      by(rule alt_dist.alt_vwalk_bet_alt_dist[OF 1[OF True]])
    thus ?thesis
      using True by simp
  next
    case False
    thus ?thesis by simp
  qed
  hence "alt_dist.alt_distance P1 P2 parity G u v
          \<le> (INF p. if alt_dist.alt_vwalk_bet P1 P2 parity G' u p v then length p - 1 else \<infinity>)"
    by(intro INF_greatest) blast
  thus ?case
    by(simp add: alt_dist.alt_distance_def)
qed

lemma alt_distance_subset: "G \<subseteq> G' \<Longrightarrow> alt_dist.alt_distance P1 P2 parity G' u v \<le> alt_dist.alt_distance P1 P2 parity G u v"
proof(goal_cases)
  case 1
  show ?case
  proof(cases "alt_dist.alt_reachable P1 P2 parity G u v")
    case True
    obtain p where p: "alt_dist.alt_vwalk_bet P1 P2 parity G u p v"
      "alt_dist.alt_distance P1 P2 parity G u v = length p - 1"
      using True by(rule alt_dist.alt_reachable_dist_2)
    have "alt_dist.alt_vwalk_bet P1 P2 parity G' u p v"
      by(rule alt_dist.alt_vwalk_bet_subset[OF p(1) 1])
    hence "alt_dist.alt_distance P1 P2 parity G' u v \<le> length p - 1"
      by(rule alt_dist.alt_vwalk_bet_alt_dist)
    thus ?thesis
      by(simp add: p(2))
  next
    case False
    thus ?thesis
      by(simp add: alt_dist.alt_unreachable_dist)
  qed
qed

lemma odd_alt_distance_neighbourhood:
  "\<lbrakk>v \<in> neighbourhood G u; P1 (u,v)\<rbrakk> \<Longrightarrow> alt_dist.alt_distance P1 P2 Odd G u v \<le> 1"
proof(goal_cases)
  case 1
  hence "vwalk_bet G u [u,v] v"
    by auto
  moreover have "P1 (u,v)"
    using 1(2) .
  ultimately have "alt_dist.alt_vwalk_bet P1 P2 Odd G u [u,v] v"
    by (auto intro!: alt_dist.alt_vwalk_betI simp: parity_simps alt_list_step alt_list_empty split: parity.splits)
  moreover have "length [u,v] = 2"
    by auto
  ultimately show ?case
    by(force dest!: alt_dist.alt_vwalk_bet_alt_dist simp: one_enat_def)
qed

lemma even_alt_distance_neighbourhood:
  "\<lbrakk>w \<in> neighbourhood G v; v \<in> neighbourhood G u; P1 (u,v); P2 (v,w)\<rbrakk> \<Longrightarrow> alt_dist.alt_distance P1 P2 Even G u w \<le> 2"
proof(goal_cases)
  case 1
  hence "vwalk_bet G u [u,v,w] w"
    by auto
  moreover have "P1 (u,v)"
    using 1(3) .
  moreover have "P2 (v,w)"
    using 1(4) .
  ultimately have "alt_dist.alt_vwalk_bet P1 P2 Even G u [u,v,w] w"
    by (auto intro!: alt_dist.alt_vwalk_betI simp: parity_simps alt_list_step alt_list_empty split: parity.splits)
  moreover have "length [u,v,w] = 3"
    by auto
  ultimately show ?case
    by(auto dest!: alt_dist.alt_vwalk_bet_alt_dist simp: one_enat_def eval_enat_numeral)
qed

subsection \<open>Shortest Paths\<close>
context alt_dist
begin

definition "alt_shortest_path parity G u p v = (alt_distance parity G u v = length p -1 \<and> alt_vwalk_bet parity G u p v)"

lemma alt_shortest_path_props[elim]:
  "alt_shortest_path parity G u p v \<Longrightarrow> (\<lbrakk>alt_distance parity G u v = length p -1; alt_vwalk_bet parity G u p v\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: alt_shortest_path_def)

lemma alt_shortest_path_intro:
  "\<lbrakk>alt_distance parity G u v = length p -1; alt_vwalk_bet parity G u p v\<rbrakk> \<Longrightarrow> alt_shortest_path parity G u p v"
  by (auto simp: alt_shortest_path_def)

lemma alt_shortest_path_vwalk: "alt_shortest_path parity G u p v \<Longrightarrow> alt_vwalk_bet parity G u p v"
  by auto

lemma alt_shortest_path_dist: "alt_shortest_path parity G u p v \<Longrightarrow> alt_distance parity G u v = length p - 1"
  by auto

end

lemma alt_shortest_path_split_1:
  "\<lbrakk>alt_dist.alt_shortest_path P1 P2 Even G u (p1 @ x # p2) v\<rbrakk> \<Longrightarrow>
     \<exists>parity'.
       alt_dist.alt_shortest_path P1 P2 parity' G u (p1 @ [x]) x \<and> 
       next_alt_list_parity parity' alt_dist.alt_shortest_path P1 P2 parity' G x (x # p2) v"
proof(goal_cases)
  case 1
  then obtain parity where 
         "alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x"
         "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G x (x # p2) v"
    by (auto dest!: alt_dist.alt_shortest_path_vwalk simp: split_vwalk vwalk_bet_pref
                elim!: alt_vwalk_bet_appendE_1[where ?p1.0 = "p1 @ [x]", simplified])

  hence "alt_dist.alt_reachable P1 P2 parity G u x" 
        "next_alt_list_parity parity alt_dist.alt_reachable P1 P2 parity G x v"
    by (auto dest!: alt_dist.alt_reachable_vwalk_betD simp: parity_simps split: parity.splits)

  have "alt_dist.alt_distance P1 P2 parity G u x \<ge> length (p1 @ [x]) - 1"
  proof(rule ccontr, goal_cases)
    case 1
    moreover from \<open>alt_dist.alt_reachable P1 P2 parity G u x\<close>
    obtain p where 
       "alt_dist.alt_vwalk_bet P1 P2 parity G u p x"
       "alt_dist.alt_distance P1 P2 parity G u x = enat (length p - 1)"
      by (auto intro: alt_dist.alt_reachable_dist_2 simp: parity_simps split: parity.splits)
    ultimately have "length p - 1 < length (p1 @ [x]) - 1"
      by auto 
    hence "length (p @ p2) - 1 < length (p1 @ x # p2) - 1"
      by auto
    have p_ne: "p \<noteq> []"
      using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u p x\<close>
      by(auto elim!: alt_dist.alt_vwalk_betE simp: vwalk_bet_def)
    have p_last: "x = last p"
      by(rule alt_dist.last_of_alt_vwalk_bet[OF \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u p x\<close>])
    have p_snoc: "p = butlast p @ [x]"
      using p_ne by(simp add: p_last)
    have "alt_dist.alt_vwalk_bet P1 P2 Even G u ((butlast p @ [x]) @ p2) v"
    proof(rule alt_vwalk_bet_append_2)
      show "alt_dist.alt_vwalk_bet P1 P2 parity G u (butlast p @ [x]) (last (butlast p @ [x]))"
        using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u p x\<close>
        by(simp add: p_snoc[symmetric] p_last[symmetric])
      show "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G (last (butlast p @ [x])) (last (butlast p @ [x]) # p2) v"
        using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G x (x # p2) v\<close>
        by simp
      show "butlast p @ [x] \<noteq> []"
        by simp
    qed
    hence "alt_dist.alt_distance P1 P2 Even G u v \<le> length ((butlast p @ [x]) @ p2) - 1"
      by(rule alt_dist.alt_vwalk_bet_alt_dist)
    hence "alt_dist.alt_distance P1 P2 Even G u v \<le> length (p @ p2) - 1"
      by(simp add: p_snoc[symmetric])
    moreover have "alt_dist.alt_distance P1 P2 Even G u v = length (p1 @ x # p2) - 1"
      using \<open>alt_dist.alt_shortest_path P1 P2 Even G u (p1 @ x # p2) v\<close>
      by (rule alt_dist.alt_shortest_path_dist)
    ultimately show ?case
      using \<open>length (p @ p2) - 1 < length (p1 @ x # p2) - 1\<close>
      by auto 
  qed
  moreover have "alt_dist.alt_distance P1 P2 parity G u x \<le> length (p1 @ [x]) - 1"
    using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x\<close>
    by (auto intro!: alt_dist.alt_vwalk_bet_alt_dist simp only: parity_simps split: parity.splits)

  moreover have "next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G x v \<ge> length (x # p2) - 1"
  proof(rule ccontr, goal_cases)
    case 1
    moreover from \<open>next_alt_list_parity parity alt_dist.alt_reachable P1 P2 parity G x v\<close>
    obtain p where 
       "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G x p v"
       "next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G x v = enat (length p - 1)"
      by (auto intro: alt_dist.alt_reachable_dist_2 simp: parity_simps split: parity.splits)
    ultimately have "length p - 1 < length (x # p2) - 1"
      by auto 
    hence "length (p1 @ p) - 1 < length (p1 @ x # p2) - 1"
      by auto
    have p_cons: "p = x # (tl p)"
      using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G x p v\<close> 
      by (fastforce dest!: alt_dist.hd_of_alt_vwalk_bet simp: parity_simps split: parity.splits)
    have "alt_dist.alt_vwalk_bet P1 P2 Even G u ((p1 @ [x]) @ (tl p)) v"
    proof(rule alt_vwalk_bet_append_2)
      show "alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) (last (p1 @ [x]))"
        using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x\<close>
        by simp
      show "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G (last (p1 @ [x])) (last (p1 @ [x]) # tl p) v"
        using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G x p v\<close>
        by(simp add: p_cons[symmetric])
      show "p1 @ [x] \<noteq> []"
        by simp
    qed
    hence "alt_dist.alt_distance P1 P2 Even G u v \<le> length ((p1 @ [x]) @ tl p) - 1"
      by(rule alt_dist.alt_vwalk_bet_alt_dist)
    hence "alt_dist.alt_distance P1 P2 Even G u v \<le> length (p1 @ p) - 1"
      using p_cons by simp
    moreover have "alt_dist.alt_distance P1 P2 Even G u v = length (p1 @ x # p2) - 1"
      using \<open>alt_dist.alt_shortest_path P1 P2 Even G u (p1 @ x # p2) v\<close>
      by (rule alt_dist.alt_shortest_path_dist)
    ultimately show ?case
      using \<open>length (p1 @ p) - 1 < length (p1 @ x # p2) - 1\<close>
      by auto 
  qed
  moreover have "next_alt_list_parity parity alt_dist.alt_distance P1 P2 parity G x v \<le> length (x # p2) - 1"
    using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G x (x # p2) v\<close>
    by (auto intro!: alt_dist.alt_vwalk_bet_alt_dist simp only: parity_simps split: parity.splits)
  ultimately show ?case
    using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x\<close>
          \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G x (x # p2) v\<close>
    by (auto simp add: alt_dist.alt_shortest_path_def parity_simps intro!: exI[where x = parity] split: parity.splits)
qed


lemma alt_shortest_path_split_2:
  "\<lbrakk>alt_dist.alt_shortest_path P1 P2 Odd G u (p1 @ x # p2) v\<rbrakk> \<Longrightarrow>
     \<exists>parity'.
       alt_dist.alt_shortest_path P1 P2 parity' G u (p1 @ [x]) x \<and>
       next_alt_list_parity parity' alt_dist.alt_shortest_path P1 P2 (other_parity parity') G x (x # p2) v"
proof(goal_cases)
  case 1
  then obtain parity where 
         "alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x"
         "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G x (x # p2) v"
    by (auto dest!: alt_dist.alt_shortest_path_vwalk simp: split_vwalk vwalk_bet_pref
                elim!: alt_vwalk_bet_appendE_1'[where ?p1.0 = "p1 @ [x]", simplified])

  hence "alt_dist.alt_reachable P1 P2 parity G u x" 
        "next_alt_list_parity parity alt_dist.alt_reachable P1 P2 (other_parity parity) G x v"
    by (auto dest!: alt_dist.alt_reachable_vwalk_betD simp: parity_simps split: parity.splits)

  have "alt_dist.alt_distance P1 P2 parity G u x \<ge> length (p1 @ [x]) - 1"
  proof(rule ccontr, goal_cases)
    case 1
    moreover from \<open>alt_dist.alt_reachable P1 P2 parity G u x\<close>
    obtain p where 
       "alt_dist.alt_vwalk_bet P1 P2 parity G u p x"
       "alt_dist.alt_distance P1 P2 parity G u x = enat (length p - 1)"
      by (auto intro: alt_dist.alt_reachable_dist_2 simp: parity_simps split: parity.splits)
    ultimately have "length p - 1 < length (p1 @ [x]) - 1"
      by auto 
    hence "length (p @ p2) - 1 < length (p1 @ x # p2) - 1"
      by auto
    have p_ne: "p \<noteq> []"
      using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u p x\<close>
      by(auto elim!: alt_dist.alt_vwalk_betE simp: vwalk_bet_def)
    have p_last: "x = last p"
      by(rule alt_dist.last_of_alt_vwalk_bet[OF \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u p x\<close>])
    have p_snoc: "p = butlast p @ [x]"
      using p_ne by(simp add: p_last)
    have "alt_dist.alt_vwalk_bet P1 P2 Odd G u ((butlast p @ [x]) @ p2) v"
    proof(rule alt_vwalk_bet_append_3)
      show "alt_dist.alt_vwalk_bet P1 P2 parity G u (butlast p @ [x]) (last (butlast p @ [x]))"
        using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u p x\<close>
        by(simp add: p_snoc[symmetric] p_last[symmetric])
      show "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G (last (butlast p @ [x])) (last (butlast p @ [x]) # p2) v"
        using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G x (x # p2) v\<close>
        by simp
      show "butlast p @ [x] \<noteq> []"
        by simp
    qed
    hence "alt_dist.alt_distance P1 P2 Odd G u v \<le> length ((butlast p @ [x]) @ p2) - 1"
      by(rule alt_dist.alt_vwalk_bet_alt_dist)
    hence "alt_dist.alt_distance P1 P2 Odd G u v \<le> length (p @ p2) - 1"
      by(simp add: p_snoc[symmetric])
    moreover have "alt_dist.alt_distance P1 P2 Odd G u v = length (p1 @ x # p2) - 1"
      using \<open>alt_dist.alt_shortest_path P1 P2 Odd G u (p1 @ x # p2) v\<close>
      by (rule alt_dist.alt_shortest_path_dist)
    ultimately show ?case
      using \<open>length (p @ p2) - 1 < length (p1 @ x # p2) - 1\<close>
      by auto 
  qed
  moreover have "alt_dist.alt_distance P1 P2 parity G u x \<le> length (p1 @ [x]) - 1"
    using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x\<close>
    by (auto intro!: alt_dist.alt_vwalk_bet_alt_dist simp only: parity_simps split: parity.splits)

  moreover have "next_alt_list_parity parity alt_dist.alt_distance P1 P2 (other_parity parity) G x v \<ge> length (x # p2) - 1"
  proof(rule ccontr, goal_cases)
    case 1
    moreover from \<open>next_alt_list_parity parity alt_dist.alt_reachable P1 P2 (other_parity parity) G x v\<close>
    obtain p where 
       "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G x p v"
       "next_alt_list_parity parity alt_dist.alt_distance P1 P2 (other_parity parity) G x v = enat (length p - 1)"
      by (auto intro: alt_dist.alt_reachable_dist_2 simp: parity_simps split: parity.splits)
    ultimately have "length p - 1 < length (x # p2) - 1"
      by auto 
    hence "length (p1 @ p) - 1 < length (p1 @ x # p2) - 1"
      by auto
    have p_cons: "p = x # (tl p)"
      using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G x p v\<close> 
      by (fastforce dest!: alt_dist.hd_of_alt_vwalk_bet simp: parity_simps split: parity.splits)
    have "alt_dist.alt_vwalk_bet P1 P2 Odd G u ((p1 @ [x]) @ (tl p)) v"
    proof(rule alt_vwalk_bet_append_3)
      show "alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) (last (p1 @ [x]))"
        using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x\<close>
        by simp
      show "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G (last (p1 @ [x])) (last (p1 @ [x]) # tl p) v"
        using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G x p v\<close>
        by(simp add: p_cons[symmetric])
      show "p1 @ [x] \<noteq> []"
        by simp
    qed
    hence "alt_dist.alt_distance P1 P2 Odd G u v \<le> length ((p1 @ [x]) @ tl p) - 1"
      by(rule alt_dist.alt_vwalk_bet_alt_dist)
    hence "alt_dist.alt_distance P1 P2 Odd G u v \<le> length (p1 @ p) - 1"
      using p_cons by simp
    moreover have "alt_dist.alt_distance P1 P2 Odd G u v = length (p1 @ x # p2) - 1"
      using \<open>alt_dist.alt_shortest_path P1 P2 Odd G u (p1 @ x # p2) v\<close>
      by (rule alt_dist.alt_shortest_path_dist)
    ultimately show ?case
      using \<open>length (p1 @ p) - 1 < length (p1 @ x # p2) - 1\<close>
      by auto 
  qed
  moreover have "next_alt_list_parity parity alt_dist.alt_distance P1 P2 (other_parity parity) G x v \<le> length (x # p2) - 1"
    using \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G x (x # p2) v\<close>
    by (auto intro!: alt_dist.alt_vwalk_bet_alt_dist simp only: parity_simps split: parity.splits)
  ultimately show ?case
    using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u (p1 @ [x]) x\<close>
          \<open>next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G x (x # p2) v\<close>
    by (auto simp add: alt_dist.alt_shortest_path_def parity_simps intro!: exI[where x = parity] split: parity.splits)
qed

lemma alt_shortest_path_split_alt_distance:
  "\<lbrakk>alt_dist.alt_shortest_path P1 P2 parity G u (p1 @ x # p2) v\<rbrakk> \<Longrightarrow> 
    (\<exists>parity'. alt_dist.alt_distance P1 P2 parity' G u x \<le> alt_dist.alt_distance P1 P2 parity G u v)"
proof(goal_cases)
  case 1
  then show ?case
  proof(cases parity)
    case Even
    obtain parity' where sp: "alt_dist.alt_shortest_path P1 P2 parity' G u (p1 @ [x]) x"
      using alt_shortest_path_split_1[OF 1[simplified Even]]
      by auto
    have "alt_dist.alt_distance P1 P2 parity' G u x \<le> alt_dist.alt_distance P1 P2 parity G u v"
      using alt_dist.alt_shortest_path_dist[OF sp] alt_dist.alt_shortest_path_dist[OF 1]
      by simp
    then show ?thesis
      by blast
  next
    case Odd
    obtain parity' where sp: "alt_dist.alt_shortest_path P1 P2 parity' G u (p1 @ [x]) x"
      using alt_shortest_path_split_2[OF 1[simplified Odd]]
      by auto
    have "alt_dist.alt_distance P1 P2 parity' G u x \<le> alt_dist.alt_distance P1 P2 parity G u v"
      using alt_dist.alt_shortest_path_dist[OF sp] alt_dist.alt_shortest_path_dist[OF 1]
      by simp
    then show ?thesis
      by blast
  qed
qed


lemma shortest_path_split_distance':
  "\<lbrakk>x \<in> set p; alt_dist.alt_shortest_path P1 P2 parity G u p v\<rbrakk> \<Longrightarrow> (\<exists>parity'. alt_dist.alt_distance P1 P2 parity' G u x \<le> alt_dist.alt_distance P1 P2 parity G u v)"
  apply(subst (asm) in_set_conv_decomp_last)
  by (auto simp: alt_shortest_path_split_alt_distance)

lemma alt_shortest_path_exists:
  assumes "alt_dist.alt_reachable P1 P2 parity G u v"
  obtains p where "alt_dist.alt_shortest_path P1 P2 parity G u p v"
  using assms 
  by (force elim!: alt_dist.alt_reachable_dist_2 simp: alt_dist.alt_shortest_path_def)

lemma alt_shortest_path_exists_2:
  assumes "alt_dist.alt_distance P1 P2 parity G u v < \<infinity>"
  obtains p where "alt_dist.alt_shortest_path P1 P2 parity G u p v"
  using assms 
  by (force dest!: alt_dist.alt_dist_reachable elim!: alt_shortest_path_exists simp: alt_dist.alt_shortest_path_def)

lemma not_distinct_props: 
  "\<not>distinct xs \<Longrightarrow> (\<And>x1 x2 xs1 xs2 xs3. \<lbrakk>xs = xs1 @ x1# xs2 @ x2 # xs3; x1 = x2\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  using not_distinct_decomp
  by fastforce

datatype 'a labelled_vtx = Vtx (label: "parity") (vtx: "'a")

lemma alt_vwalk_bet_vertex_decompE_1:
  assumes p_vwalk: "alt_dist.alt_vwalk_bet P1 P2 Even G u (xs @ y # ys) v"
  obtains parity q r where
    "(xs @ y # ys) = q @ tl r"
    "q = xs @ [y]"
    "r = y # ys"
    "alt_dist.alt_vwalk_bet P1 P2 parity G u q y"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G y r v"
proof-
  obtain par where
    "alt_dist.alt_vwalk_bet P1 P2 par G u (xs @ [y]) y"
    "next_alt_list_parity par alt_dist.alt_vwalk_bet P1 P2 par G y (y # ys) v"
    using p_vwalk
    by(auto elim!: alt_vwalk_bet_appendE_1[where ?p1.0 = "xs @ [y]", simplified])
  thus ?thesis
    by(intro that[of "xs @ [y]" "y # ys" par]) auto
qed

lemma alt_vwalk_bet_vertex_decompE_1_test:
  assumes p_vwalk: "alt_dist.alt_vwalk_bet P1 P2 parity' G u (xs @ y # ys) v" "parity' = Even"
  obtains parity q r where
    "(xs @ y # ys) = q @ tl r"
    "q = xs @ [y]"
    "r = y # ys"
    "alt_dist.alt_vwalk_bet P1 P2 parity G u q y"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G y r v"
proof-
  from p_vwalk have "alt_dist.alt_vwalk_bet P1 P2 Even G u (xs @ y # ys) v"
    by simp
  from alt_vwalk_bet_vertex_decompE_1[OF this that] show ?thesis .
qed

lemma alt_vwalk_bet_vertex_decompE_2:
  assumes p_vwalk: "alt_dist.alt_vwalk_bet P1 P2 Odd G u (xs @ y # ys) v"
  obtains parity q r where
    "(xs @ y # ys) = q @ tl r"
    "q = xs @ [y]"
    "r = y # ys"
    "alt_dist.alt_vwalk_bet P1 P2 parity G u q y"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G y r v"
proof-
  obtain par where
    "alt_dist.alt_vwalk_bet P1 P2 par G u (xs @ [y]) y"
    "next_alt_list_parity par alt_dist.alt_vwalk_bet P1 P2 (other_parity par) G y (y # ys) v"
    using p_vwalk
    by(auto elim!: alt_vwalk_bet_appendE_1'[where ?p1.0 = "xs @ [y]", simplified])
  thus ?thesis
    by(intro that[of "xs @ [y]" "y # ys" par]) auto
qed

lemma True_imp: "P \<Longrightarrow> (x = x \<longrightarrow> P)"
  by auto

lemma True_imp_2: "P \<Longrightarrow> (True \<longrightarrow> P)"
  by auto

lemma False_imp: "True \<Longrightarrow> (Even = Odd \<longrightarrow> P)"
  by auto

lemma False_imp_2: "True \<Longrightarrow> (Odd = Even \<longrightarrow> P)"
  by auto

lemma closed_alt_vwalk_bet_decomp_1:
  assumes p_vwalk: "alt_dist.alt_vwalk_bet P1 P2 Even G u (xs @ y # ys @ y # zs) v"
  shows
    "\<exists>parity parity' parity''.
    alt_dist.alt_vwalk_bet P1 P2 parity G u (xs @ [y]) y \<and>
    next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity' G y (y # ys @ [y]) y \<and>
    next_alt_list_parity parity' (next_alt_list_parity parity alt_dist.alt_vwalk_bet) P1 P2 parity'' G y (y # zs) v \<and>
    (({# parity,parity',parity'' #} = {# Odd, Odd, Even #}) \<or> 
     ({# parity,parity',parity'' #} = {# Even, Even, Even #}))"
proof-
  obtain parity q r where dec1:
    "xs @ y # ys @ y # zs = q @ tl r"
    "q = xs @ [y]"
    "r = y # ys @ y # zs"
    "alt_dist.alt_vwalk_bet P1 P2 parity G u q y"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity G y r v"
    by(rule alt_vwalk_bet_vertex_decompE_1[OF p_vwalk])
  have c1: "alt_dist.alt_vwalk_bet P1 P2 parity G u (xs @ [y]) y"
    using dec1(4) by(simp add: dec1(2))
  show ?thesis
  proof(cases parity)
    case Even
    have B: "alt_dist.alt_vwalk_bet P1 P2 Even G y ((y # ys) @ y # zs) v"
      using dec1(5) by(simp add: dec1(3) Even parity_simps)
    obtain parity2 q2 r2 where dec2:
      "(y # ys) @ y # zs = q2 @ tl r2"
      "q2 = (y # ys) @ [y]"
      "r2 = y # zs"
      "alt_dist.alt_vwalk_bet P1 P2 parity2 G y q2 y"
      "next_alt_list_parity parity2 alt_dist.alt_vwalk_bet P1 P2 parity2 G y r2 v"
      by(rule alt_vwalk_bet_vertex_decompE_1[OF B])
    have c2: "next_alt_list_parity Even alt_dist.alt_vwalk_bet P1 P2 parity2 G y (y # ys @ [y]) y"
      using dec2(4) by(simp add: dec2(2) parity_simps)
    show ?thesis
    proof(cases parity2)
      case Even2: Even
      have c3: "next_alt_list_parity Even (next_alt_list_parity Even alt_dist.alt_vwalk_bet) P1 P2 Even G y (y # zs) v"
        using dec2(5) by(simp add: dec2(3) Even2 parity_simps)
      have "alt_dist.alt_vwalk_bet P1 P2 Even G u (xs @ [y]) y \<and>
            next_alt_list_parity Even alt_dist.alt_vwalk_bet P1 P2 Even G y (y # ys @ [y]) y \<and>
            next_alt_list_parity Even (next_alt_list_parity Even alt_dist.alt_vwalk_bet) P1 P2 Even G y (y # zs) v \<and>
            ({# Even, Even, Even #} = {# Odd, Odd, Even #} \<or> {# Even, Even, Even #} = {# Even, Even, Even #})"
        using c1 c2 c3 by(simp add: Even Even2)
      thus ?thesis by blast
    next
      case Odd2: Odd
      have c3: "next_alt_list_parity Odd (next_alt_list_parity Even alt_dist.alt_vwalk_bet) P1 P2 Odd G y (y # zs) v"
        using dec2(5) by(simp add: dec2(3) Odd2 parity_simps)
      have "alt_dist.alt_vwalk_bet P1 P2 Even G u (xs @ [y]) y \<and>
            next_alt_list_parity Even alt_dist.alt_vwalk_bet P1 P2 Odd G y (y # ys @ [y]) y \<and>
            next_alt_list_parity Odd (next_alt_list_parity Even alt_dist.alt_vwalk_bet) P1 P2 Odd G y (y # zs) v \<and>
            ({# Even, Odd, Odd #} = {# Odd, Odd, Even #} \<or> {# Even, Odd, Odd #} = {# Even, Even, Even #})"
        using c1 c2 c3 by(simp add: Even Odd2 add_mset_commute)
      thus ?thesis by blast
    qed
  next
    case Odd
    have B: "alt_dist.alt_vwalk_bet P2 P1 Odd G y ((y # ys) @ y # zs) v"
      using dec1(5) by(simp add: dec1(3) Odd parity_simps)
    obtain parity2 q2 r2 where dec2:
      "(y # ys) @ y # zs = q2 @ tl r2"
      "q2 = (y # ys) @ [y]"
      "r2 = y # zs"
      "alt_dist.alt_vwalk_bet P2 P1 parity2 G y q2 y"
      "next_alt_list_parity parity2 alt_dist.alt_vwalk_bet P2 P1 (other_parity parity2) G y r2 v"
      by(rule alt_vwalk_bet_vertex_decompE_2[OF B])
    have c2: "next_alt_list_parity Odd alt_dist.alt_vwalk_bet P1 P2 parity2 G y (y # ys @ [y]) y"
      using dec2(4) by(simp add: dec2(2) parity_simps)
    show ?thesis
    proof(cases parity2)
      case Even2: Even
      have c3: "next_alt_list_parity Even (next_alt_list_parity Odd alt_dist.alt_vwalk_bet) P1 P2 Odd G y (y # zs) v"
        using dec2(5) by(simp add: dec2(3) Even2 parity_simps)
      have "alt_dist.alt_vwalk_bet P1 P2 Odd G u (xs @ [y]) y \<and>
            next_alt_list_parity Odd alt_dist.alt_vwalk_bet P1 P2 Even G y (y # ys @ [y]) y \<and>
            next_alt_list_parity Even (next_alt_list_parity Odd alt_dist.alt_vwalk_bet) P1 P2 Odd G y (y # zs) v \<and>
            ({# Odd, Even, Odd #} = {# Odd, Odd, Even #} \<or> {# Odd, Even, Odd #} = {# Even, Even, Even #})"
        using c1 c2 c3 by(simp add: Odd Even2 add_mset_commute)
      thus ?thesis by blast
    next
      case Odd2: Odd
      have c3: "next_alt_list_parity Odd (next_alt_list_parity Odd alt_dist.alt_vwalk_bet) P1 P2 Even G y (y # zs) v"
        using dec2(5) by(simp add: dec2(3) Odd2 parity_simps)
      have "alt_dist.alt_vwalk_bet P1 P2 Odd G u (xs @ [y]) y \<and>
            next_alt_list_parity Odd alt_dist.alt_vwalk_bet P1 P2 Odd G y (y # ys @ [y]) y \<and>
            next_alt_list_parity Odd (next_alt_list_parity Odd alt_dist.alt_vwalk_bet) P1 P2 Even G y (y # zs) v \<and>
            ({# Odd, Odd, Even #} = {# Odd, Odd, Even #} \<or> {# Odd, Odd, Even #} = {# Even, Even, Even #})"
        using c1 c2 c3 by(simp add: Odd Odd2)
      thus ?thesis by blast
    qed
  qed
qed

lemma closed_alt_vwalk_bet_decompE_1:
  assumes p_vwalk: "alt_dist.alt_vwalk_bet P1 P2 Even G u (xs @ y # ys @ y # zs) v"
  obtains parity parity' parity'' where
    "alt_dist.alt_vwalk_bet P1 P2 parity G u (xs @ [y]) y"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity' G y (y # ys @ [y]) y"
    "next_alt_list_parity parity' (next_alt_list_parity parity alt_dist.alt_vwalk_bet) P1 P2 parity'' G y (y # zs) v"
    "(({# parity,parity',parity'' #} = {# Odd, Odd, Even #}) \<or> 
     ({# parity,parity',parity'' #} = {# Even, Even, Even #}))"
  using closed_alt_vwalk_bet_decomp_1[OF assms]
  by auto

lemma closed_alt_vwalk_bet_decompE_1':
  "alt_dist.alt_vwalk_bet P1 P2 Even G u (xs @ y # ys @ y # zs) v \<Longrightarrow>
   \<lbrakk>\<And>parity parity' parity''.
     \<lbrakk>alt_dist.alt_vwalk_bet P1 P2 parity G u (xs @ [y]) y;
      next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity' G y (y # ys @ [y]) y;
      next_alt_list_parity parity' (next_alt_list_parity parity alt_dist.alt_vwalk_bet) P1 P2 parity'' G y (y # zs) v;
      (({# parity,parity',parity'' #} = {# Odd, Odd, Even #}) \<or> 
       ({# parity,parity',parity'' #} = {# Even, Even, Even #}))\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(rule closed_alt_vwalk_bet_decompE_1)

lemma three_parity_crunch_1[case_names EEE OOE OEO EOO]:
  "({# parity,parity',parity'' #} = {# Odd, Odd, Even #}) \<or> 
       ({# parity,parity',parity'' #} = {# Even, Even, Even #}) \<Longrightarrow>
       \<lbrakk>\<lbrakk>parity = Even; parity' = Even; parity'' = Even\<rbrakk> \<Longrightarrow> P;
        \<lbrakk>parity = Odd; parity' = Odd; parity'' = Even\<rbrakk> \<Longrightarrow> P;
        \<lbrakk>parity = Odd; parity' = Even; parity'' = Odd\<rbrakk> \<Longrightarrow> P;
        \<lbrakk>parity = Even; parity' = Odd; parity'' = Odd\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(cases parity; cases parity'; cases parity'')
    (auto simp: add_mset_commute add_mset_add_mset_same_iff add_eq_conv_ex)

lemma closed_alt_vwalk_bet_decomp_2:
  assumes p_vwalk: "alt_dist.alt_vwalk_bet P1 P2 Odd G u (xs @ y # ys @ y # zs) v"
  shows
    "\<exists>parity parity' parity''.
    alt_dist.alt_vwalk_bet P1 P2 parity G u (xs @ [y]) y \<and>
    next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity' G y (y # ys @ [y]) y \<and>
    next_alt_list_parity parity' (next_alt_list_parity parity alt_dist.alt_vwalk_bet) P1 P2 parity'' G y (y # zs) v \<and>
    (({# parity,parity',parity'' #} = {# Odd, Odd, Odd #}) \<or> 
     ({# parity,parity',parity'' #} = {# Even, Odd, Even #}))"
proof-
  obtain parity q r where dec1:
    "xs @ y # ys @ y # zs = q @ tl r"
    "q = xs @ [y]"
    "r = y # ys @ y # zs"
    "alt_dist.alt_vwalk_bet P1 P2 parity G u q y"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 (other_parity parity) G y r v"
    by(rule alt_vwalk_bet_vertex_decompE_2[OF p_vwalk])
  have c1: "alt_dist.alt_vwalk_bet P1 P2 parity G u (xs @ [y]) y"
    using dec1(4) by(simp add: dec1(2))
  show ?thesis
  proof(cases parity)
    case Even
    have B: "alt_dist.alt_vwalk_bet P1 P2 Odd G y ((y # ys) @ y # zs) v"
      using dec1(5) by(simp add: dec1(3) Even parity_simps)
    obtain parity2 q2 r2 where dec2:
      "(y # ys) @ y # zs = q2 @ tl r2"
      "q2 = (y # ys) @ [y]"
      "r2 = y # zs"
      "alt_dist.alt_vwalk_bet P1 P2 parity2 G y q2 y"
      "next_alt_list_parity parity2 alt_dist.alt_vwalk_bet P1 P2 (other_parity parity2) G y r2 v"
      by(rule alt_vwalk_bet_vertex_decompE_2[OF B])
    have c2: "next_alt_list_parity Even alt_dist.alt_vwalk_bet P1 P2 parity2 G y (y # ys @ [y]) y"
      using dec2(4) by(simp add: dec2(2) parity_simps)
    show ?thesis
    proof(cases parity2)
      case Even2: Even
      have c3: "next_alt_list_parity Even (next_alt_list_parity Even alt_dist.alt_vwalk_bet) P1 P2 Odd G y (y # zs) v"
        using dec2(5) by(simp add: dec2(3) Even2 parity_simps)
      have "alt_dist.alt_vwalk_bet P1 P2 Even G u (xs @ [y]) y \<and>
            next_alt_list_parity Even alt_dist.alt_vwalk_bet P1 P2 Even G y (y # ys @ [y]) y \<and>
            next_alt_list_parity Even (next_alt_list_parity Even alt_dist.alt_vwalk_bet) P1 P2 Odd G y (y # zs) v \<and>
            ({# Even, Even, Odd #} = {# Odd, Odd, Odd #} \<or> {# Even, Even, Odd #} = {# Even, Odd, Even #})"
        using c1 c2 c3 by(simp add: Even Even2 add_mset_commute)
      thus ?thesis by blast
    next
      case Odd2: Odd
      have c3: "next_alt_list_parity Odd (next_alt_list_parity Even alt_dist.alt_vwalk_bet) P1 P2 Even G y (y # zs) v"
        using dec2(5) by(simp add: dec2(3) Odd2 parity_simps)
      have "alt_dist.alt_vwalk_bet P1 P2 Even G u (xs @ [y]) y \<and>
            next_alt_list_parity Even alt_dist.alt_vwalk_bet P1 P2 Odd G y (y # ys @ [y]) y \<and>
            next_alt_list_parity Odd (next_alt_list_parity Even alt_dist.alt_vwalk_bet) P1 P2 Even G y (y # zs) v \<and>
            ({# Even, Odd, Even #} = {# Odd, Odd, Odd #} \<or> {# Even, Odd, Even #} = {# Even, Odd, Even #})"
        using c1 c2 c3 by(simp add: Even Odd2)
      thus ?thesis by blast
    qed
  next
    case Odd
    have B: "alt_dist.alt_vwalk_bet P2 P1 Even G y ((y # ys) @ y # zs) v"
      using dec1(5) by(simp add: dec1(3) Odd parity_simps)
    obtain parity2 q2 r2 where dec2:
      "(y # ys) @ y # zs = q2 @ tl r2"
      "q2 = (y # ys) @ [y]"
      "r2 = y # zs"
      "alt_dist.alt_vwalk_bet P2 P1 parity2 G y q2 y"
      "next_alt_list_parity parity2 alt_dist.alt_vwalk_bet P2 P1 parity2 G y r2 v"
      by(rule alt_vwalk_bet_vertex_decompE_1[OF B])
    have c2: "next_alt_list_parity Odd alt_dist.alt_vwalk_bet P1 P2 parity2 G y (y # ys @ [y]) y"
      using dec2(4) by(simp add: dec2(2) parity_simps)
    show ?thesis
    proof(cases parity2)
      case Even2: Even
      have c3: "next_alt_list_parity Even (next_alt_list_parity Odd alt_dist.alt_vwalk_bet) P1 P2 Even G y (y # zs) v"
        using dec2(5) by(simp add: dec2(3) Even2 parity_simps)
      have "alt_dist.alt_vwalk_bet P1 P2 Odd G u (xs @ [y]) y \<and>
            next_alt_list_parity Odd alt_dist.alt_vwalk_bet P1 P2 Even G y (y # ys @ [y]) y \<and>
            next_alt_list_parity Even (next_alt_list_parity Odd alt_dist.alt_vwalk_bet) P1 P2 Even G y (y # zs) v \<and>
            ({# Odd, Even, Even #} = {# Odd, Odd, Odd #} \<or> {# Odd, Even, Even #} = {# Even, Odd, Even #})"
        using c1 c2 c3 by(simp add: Odd Even2 add_mset_commute)
      thus ?thesis by blast
    next
      case Odd2: Odd
      have c3: "next_alt_list_parity Odd (next_alt_list_parity Odd alt_dist.alt_vwalk_bet) P1 P2 Odd G y (y # zs) v"
        using dec2(5) by(simp add: dec2(3) Odd2 parity_simps)
      have "alt_dist.alt_vwalk_bet P1 P2 Odd G u (xs @ [y]) y \<and>
            next_alt_list_parity Odd alt_dist.alt_vwalk_bet P1 P2 Odd G y (y # ys @ [y]) y \<and>
            next_alt_list_parity Odd (next_alt_list_parity Odd alt_dist.alt_vwalk_bet) P1 P2 Odd G y (y # zs) v \<and>
            ({# Odd, Odd, Odd #} = {# Odd, Odd, Odd #} \<or> {# Odd, Odd, Odd #} = {# Even, Odd, Even #})"
        using c1 c2 c3 by(simp add: Odd Odd2)
      thus ?thesis by blast
    qed
  qed
qed

lemma closed_alt_vwalk_bet_decompE_2:
  assumes p_vwalk: "alt_dist.alt_vwalk_bet P1 P2 Odd G u (xs @ y # ys @ y # zs) v"
  obtains parity parity' parity'' where
    "alt_dist.alt_vwalk_bet P1 P2 parity G u (xs @ [y]) y"
    "next_alt_list_parity parity alt_dist.alt_vwalk_bet P1 P2 parity' G y (y # ys @ [y]) y"
    "next_alt_list_parity parity' (next_alt_list_parity parity alt_dist.alt_vwalk_bet) P1 P2 parity'' G y (y # zs) v"
    "(({# parity,parity',parity'' #} = {# Odd, Odd, Odd #}) \<or> 
     ({# parity,parity',parity'' #} = {# Even, Odd, Even #}))"
  using closed_alt_vwalk_bet_decomp_2[OF assms]
  by auto

lemma three_parity_crunch_2[case_names OOO EEO EOE OEE]:
  "({# parity,parity',parity'' #} = {# Odd, Odd, Odd#}) \<or>
   ({#parity,parity',parity'' #} = {# Even, Odd, Even #}) \<Longrightarrow>
       \<lbrakk>\<lbrakk>parity = Odd; parity' = Odd; parity'' = Odd\<rbrakk> \<Longrightarrow> P;
        \<lbrakk>parity = Even; parity' = Even; parity'' = Odd\<rbrakk> \<Longrightarrow> P;
        \<lbrakk>parity = Even; parity' = Odd; parity'' = Even\<rbrakk> \<Longrightarrow> P;
        \<lbrakk>parity = Odd; parity' = Even; parity'' = Even\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(cases parity; cases parity'; cases parity'')
    (auto simp: add_mset_commute add_mset_add_mset_same_iff add_eq_conv_ex)

locale labelled_alt_dist = alt_dist P1 P2 for P1 P2::"'a labelled_vtx \<times> 'a labelled_vtx \<Rightarrow> bool"
begin

(*lemma split_alt_vwalk:
  "alt_vwalk_bet parity dG v1 (p1 @ v2 # p2) v3 \<Longrightarrow> alt_vwalk_bet parity dG v2 (v2 # p2) v3"
  unfolding vwalk_bet_def
proof (induction p1)
  case (Cons v p1)
  then show ?case 
    by (auto intro: append_vwalk_suff[where ?p1.0 = "v1 # p1"] simp add: vwalk_then_in_dVs vwalk_bet_def)
qed auto*)

definition "labelled p =     
    ((\<forall>v \<in> set p. \<forall>label v'. (v = (Vtx label v') \<and> (label = Odd) \<longrightarrow> (\<forall>(u,v)\<in>set (edges_of_vwalk p). P1 (u,v)))) \<and> 
     (\<forall>v \<in> set p. \<forall>label v'. (v = (Vtx label v') \<and>  (label = Even) \<longrightarrow> (\<forall>(u,v)\<in>set (edges_of_vwalk p). P2 (u,v)))))"

(*lemma labelledE: 
  "labelled p \<Longrightarrow> 
     \<lbrakk>\<And>label v' x. 
         \<lbrakk>(Vtx label v') \<in> set p; (x,(Vtx label v'))\<in>set (edges_of_vwalk p)\<rbrakk> \<Longrightarrow> (label = Odd) \<longleftrightarrow> P1 (x,v) \<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply (auto simp: labelled_def split: labelled_vtx.splits parity.splits)
  by blast
*)

definition "op_on es = (\<forall>e \<in> set es. P1 e \<longleftrightarrow> \<not> P2 e)"

lemma op_onE: "op_on es \<Longrightarrow> \<lbrakk>\<lbrakk>\<And>e. e \<in> set es \<Longrightarrow> P1 e \<longleftrightarrow> \<not> P2 e\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" 
  by (auto simp: op_on_def)

lemma labelledE: 
  "labelled p \<Longrightarrow>
     \<lbrakk>\<lbrakk>\<And>label v' x. 
         (\<lbrakk>(Vtx label v') \<in> set p; (x,(Vtx label v'))\<in>set (edges_of_vwalk p); label = Odd\<rbrakk> \<Longrightarrow> P1 (x,(Vtx label v')));
       \<And>label v' x.
         (\<lbrakk>(Vtx label v') \<in> set p; (x,(Vtx label v'))\<in>set (edges_of_vwalk p); (label = Even)\<rbrakk> \<Longrightarrow> P2 (x,(Vtx label v')))\<rbrakk> \<Longrightarrow> P\<rbrakk>
     \<Longrightarrow> P"
  by (auto simp: labelled_def elim!: op_onE split: labelled_vtx.splits parity.splits)


lemma labelled_op_works:
  assumes "labelled p" "op_on (edges_of_vwalk p)" 
          "(u,v) \<in> set (edges_of_vwalk p)" 
          "(w,v) \<in> set (edges_of_vwalk p)" "P1 (u,v)"
    shows "\<not> P2 (w,v)"
proof(cases v)
  case (Vtx label vtx_name)
  then show ?thesis
    using assms
    apply(cases label)
    subgoal
      apply(erule labelledE)
      subgoal
        using assms
        apply (auto elim!: op_onE)
      by (meson v_in_edge_in_vwalk(2))
    done
    subgoal
      apply(erule labelledE)
      subgoal
        using assms
        apply (auto elim!: op_onE)
        by (meson v_in_edge_in_vwalk(2))
    done
  done
qed

definition "on_path parity p pre v suff= (p = pre @ (Vtx parity v) # suff)"

lemma on_pathE: "on_path parity p pre v suff \<Longrightarrow> (p = pre @ (Vtx parity v) # suff \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: on_path_def)

lemma on_pathI: "(p = pre @ (Vtx parity v) # suff \<Longrightarrow> on_path parity p pre v suff)"
  by (auto simp: on_path_def)

(*lemma
  assumes "on_path parity' p pre w suff" "labelled p" "alt_vwalk_bet Even G u p v"
  shows "alt_vwalk_bet parity' G u (pre @ [(Vtx parity' w)]) (Vtx parity' w)"
proof(cases parity')
  case Even
  obtain parity'' where parity'': "alt_vwalk_bet parity'' G u (pre @ [Vtx Even w]) (Vtx Even w)"
    using assms
    apply(elim on_pathE)
    by (metis Even alt_vwalk_bet_vertex_decompE_1)
  moreover have "parity'' = Odd"
  proof(rule ccontr, goal_cases)
    case 1
    hence "parity'' = Even"
      using parity.exhaust
      by auto
    hence "odd (length (pre @ [Vtx Even w]))"
      using parity''
      by (auto elim!: alt_vwalk_betE simp: parity_simps)
    hence "even (length (edges_of_vwalk (pre @ [Vtx Even w])))"
      by (simp add: edges_of_vwalk_length)
    moreover have "alt_list P1 P2 (edges_of_vwalk (pre @ [Vtx Even w]))"
      using parity''
      by (auto elim!: alt_vwalk_betE simp: parity_simps)
    moreover have "(edges_of_vwalk (pre @ [Vtx Even w])) \<noteq> []"
    proof(cases pre)
      case Nil
      then show ?thesis
    using assms
    apply(elim on_pathE labelledE alt_vwalk_betE)
    apply simp
    sledgehammer


    next
      case (Cons a list)
      then show ?thesis sorry
    qed
    moreover have "last (edges_of_vwalk (pre @ [Vtx Even w])) = (last pre, Vtx Even w)"
      by (metis One_nat_def Suc_1 calculation(3) edges_of_vwalk.simps(2) edges_of_vwalk.simps(3) 
                edges_of_vwalk_append_3 last_snoc le_add1 list.size(3) list_sing_conv(1) not_less_eq_eq plus_1_eq_Suc)
    ultimately have "P2 (last pre, Vtx Even w)"
      by (metis Alternating_Lists.alternating_list_even_last linorder_not_less list.size(3) pos2)
    then show ?case sorry
  qed
  then show ?thesis
    using assms
    apply(elim on_pathE)
    apply auto
next
  case Odd
  then show ?thesis sorry
qed
*)
end

lemma alt_shortest_path_distinct:
  "\<lbrakk>labelled_alt_dist.op_on P1 P2 (edges_of_vwalk p); labelled_alt_dist.labelled P1 P2 p;
    alt_dist.alt_shortest_path P1 P2 parity G u p v; \<forall>x. (x, x) \<notin> G\<rbrakk>
    \<Longrightarrow> distinct p"
proof(rule ccontr, goal_cases)
  case 1
  have walk: "Vwalk.vwalk_bet G u p v"
    and alt: "alt_list P1 P2 (edges_of_vwalk p)"
    using 1(3)
    by(auto simp: alt_dist.alt_shortest_path_def elim!: alt_dist.alt_vwalk_betE)
  obtain x1 x2 xs1 xs2 xs3 where decomp: "p = xs1 @ x1 # xs2 @ x2 # xs3" "x1 = x2"
    using 1(5)
    by(rule not_distinct_props)
  show False
  proof(cases "3 \<le> length p")
    case True
    hence "2 \<le> length (edges_of_vwalk p)"
      by(simp add: edges_of_vwalk_length)
    then obtain e1 e2 es where edges: "edges_of_vwalk p = e1 # e2 # es"
      by(auto simp: numeral_2_eq_2 Suc_le_length_iff)
    have P1e1: "P1 e1" and P2e2: "P2 e2"
      using alt by(auto simp: edges alt_list_step)
    have e1_in: "e1 \<in> set (edges_of_vwalk p)" and e2_in: "e2 \<in> set (edges_of_vwalk p)"
      by(auto simp: edges)
    obtain label name where x2_lab: "x2 = Vtx label name"
      by(cases x2) auto
    have x2_in: "x2 \<in> set p"
      by(auto simp: decomp(1))
    show False
    proof(cases label)
      case Odd
      have "P1 e2"
        using 1(2) x2_in x2_lab e2_in
        by(cases e2) (auto simp: labelled_alt_dist.labelled_def Odd)
      thus False
        using 1(1) e2_in P2e2
        by(auto simp: labelled_alt_dist.op_on_def)
    next
      case Even
      have "P2 e1"
        using 1(2) x2_in x2_lab e1_in
        by(cases e1) (auto simp: labelled_alt_dist.labelled_def Even)
      thus False
        using 1(1) e1_in P1e1
        by(auto simp: labelled_alt_dist.op_on_def)
    qed
  next
    case False
    have len_p: "length p \<le> 2" using False by simp
    have empties: "xs1 = []" "xs2 = []" "xs3 = []"
      using len_p decomp(1) by(simp add: length_append; linarith)+
    hence "p = [x2, x2]"
      by(simp add: decomp)
    hence "(x2, x2) \<in> G"
      using vwalk_bet_edges_in_edges[OF walk]
      by(auto simp: \<open>p = [x2, x2]\<close>)
    thus False
      using 1(4) by blast
  qed
qed

lemma diet_eq': "\<lbrakk>\<And>p. \<lbrakk>alt_dist.alt_shortest_path P1 P2 parity G' u p v\<rbrakk>
                   \<Longrightarrow> alt_dist.alt_shortest_path P1 P2 parity G u (map f p) v\<rbrakk> \<Longrightarrow>
                   alt_dist.alt_distance P1 P2 parity G u v \<le> alt_dist.alt_distance P1 P2 parity G' u v"
proof(goal_cases)
  case 1
  show ?case
  proof(cases "alt_dist.alt_reachable P1 P2 parity G' u v")
    case True
    obtain p where p: "alt_dist.alt_vwalk_bet P1 P2 parity G' u p v"
      "alt_dist.alt_distance P1 P2 parity G' u v = length p - 1"
      using True by(rule alt_dist.alt_reachable_dist_2)
    hence sp: "alt_dist.alt_shortest_path P1 P2 parity G' u p v"
      by(simp add: alt_dist.alt_shortest_path_def)
    have "alt_dist.alt_shortest_path P1 P2 parity G u (map f p) v"
      by(rule 1[OF sp])
    hence "alt_dist.alt_distance P1 P2 parity G u v = length (map f p) - 1"
      by(auto simp: alt_dist.alt_shortest_path_def)
    thus ?thesis
      by(simp add: p(2))
  next
    case False
    thus ?thesis
      by(simp add: alt_dist.alt_unreachable_dist)
  qed
qed

context alt_dist
begin
lemma alt_vwalk_bet_singleton[simp]: "v \<in> dVs G \<Longrightarrow> alt_vwalk_bet Even G v [v] v"
  by (auto intro!: alt_vwalk_betI simp: alt_list_empty parity_simps split: parity.splits)

end

declare alt_dist.alt_vwalk_bet_singleton[simp]

lemma even_alt_distance_0:
  "(u = v \<and> v \<in> dVs G) \<longleftrightarrow> alt_dist.alt_distance P1 P2 Even G u v = 0"
proof(safe, goal_cases)
  case 1
  hence "alt_dist.alt_vwalk_bet P1 P2 Even G v [v] v"
    by auto
  moreover have "length [v] = 1"
    by auto
  ultimately show ?case
    using zero_enat_def
    by(auto dest!: alt_dist.alt_vwalk_bet_alt_dist simp: )
next
  case 2
  hence "alt_dist.alt_distance P1 P2 Even G u v < \<infinity>"
    by auto
  then obtain p where "alt_dist.alt_shortest_path P1 P2 Even G u p v"
    by(erule alt_shortest_path_exists_2)
  hence walk: "vwalk_bet G u p v"
    by(auto simp: alt_dist.alt_shortest_path_def elim!: alt_dist.alt_vwalk_betE)
  have "length p = 1"
  proof-
    have "alt_dist.alt_distance P1 P2 Even G u v = length p - 1"
      using \<open>alt_dist.alt_shortest_path P1 P2 Even G u p v\<close>
      by(rule alt_dist.alt_shortest_path_dist)
    hence "length p - 1 = 0"
      using \<open>alt_dist.alt_distance P1 P2 Even G u v = 0\<close>
      by(simp add: zero_enat_def)
    moreover have "p \<noteq> []"
      using walk by(auto simp: vwalk_bet_def)
    ultimately show ?thesis
      by(cases p) auto
  qed
  then obtain x where "p = [x]"
    by (auto simp: length_Suc_conv)
  then have "x = u" "x = v" "x \<in> dVs G"
    using \<open>vwalk_bet G u p v\<close> hd_of_vwalk_bet last_of_vwalk_bet
    by (fastforce simp: vwalk_bet_in_vertices)+
  then show "u = v"  "v \<in> dVs G"
    by auto
qed

lemma even_alt_distance_neighbourhood':
  assumes "v \<in> neighbourhood G u" "P2 (u,v)" 
  shows "alt_dist.alt_distance P1 P2 Even G x v \<le> 
          alt_dist.alt_distance P1 P2 Odd G x u + 1"
  using assms
proof-
  have "alt_dist.alt_distance P1 P2 Even G x v \<le>
           alt_dist.alt_distance P1 P2 Odd G x u +
             next_alt_list_parity Odd alt_dist.alt_distance P1 P2 Odd G u v"
    by(rule alt_triangle_ineq_2)
  moreover have "alt_dist.alt_distance P2 P1 Odd G u v \<le> 1"
    using assms
    by (auto intro!: odd_alt_distance_neighbourhood simp add: parity_simps)

  ultimately show ?thesis
    using order_subst1 
    by(fastforce simp add: parity_simps split: parity.splits)
qed

lemma odd_alt_distance_neighbourhood':
  assumes "v \<in> neighbourhood G u" "P1 (u,v)" 
  shows "alt_dist.alt_distance P1 P2 Odd G x v \<le> 
          alt_dist.alt_distance P1 P2 Even G x u + 1"
  using assms
proof-
  have "alt_dist.alt_distance P1 P2 Odd G x v \<le>
           alt_dist.alt_distance P1 P2 Even G x u +
             next_alt_list_parity Even alt_dist.alt_distance P1 P2 (other_parity Even) G u v"
    by(rule alt_triangle_ineq_1)
  moreover have "alt_dist.alt_distance P1 P2 Odd G u v \<le> 1"
    using assms
    by (auto intro!: odd_alt_distance_neighbourhood simp add: parity_simps)

  ultimately show ?thesis
    using order_subst1 
    by(fastforce simp add: parity_simps split: parity.splits)
qed

lemma Suc_le_length_iff_2:
  "(Suc n \<le> length xs) = (\<exists>x ys. xs = ys @ [x] \<and> n \<le> length ys)"
proof
  assume "Suc n \<le> length xs"
  then obtain m where "length xs = Suc m" "n \<le> m"
    by(cases "length xs") auto
  then obtain x ys where "xs = ys @ [x]" "length ys = m"
    by(auto simp: length_Suc_conv_rev)
  thus "\<exists>x ys. xs = ys @ [x] \<and> n \<le> length ys"
    using \<open>n \<le> m\<close> by auto
next
  assume "\<exists>x ys. xs = ys @ [x] \<and> n \<le> length ys"
  thus "Suc n \<le> length xs"
    by auto
qed

context alt_dist
begin

lemma alt_vwalk_bet_last[simp]: "alt_dist.alt_vwalk_bet P1 P2 parity G u p v \<Longrightarrow> last p = v"
    apply -
    apply(erule alt_dist.alt_vwalk_betE)
    by auto

lemma alt_vwalk_bet_hd[simp]: "alt_dist.alt_vwalk_bet P1 P2 parity G u p v \<Longrightarrow> hd p = u"
    apply -
    apply(erule alt_dist.alt_vwalk_betE)
    by auto

lemma alt_shortest_path_last[simp]: "alt_shortest_path parity G u p v \<Longrightarrow> last p = v"
    by auto

lemma alt_shortest_path_hd[simp]: "alt_shortest_path parity G u p v \<Longrightarrow> hd p = u"
    by auto
end

declare alt_dist.alt_vwalk_bet_last[simp]
declare alt_dist.alt_vwalk_bet_hd[simp]
declare alt_dist.alt_shortest_path_last[simp]
declare alt_dist.alt_shortest_path_hd[simp]

lemma even_alt_distance_parent: 
 "\<lbrakk>alt_dist.alt_distance P1 P2 Even G u v < \<infinity>; u \<noteq> v\<rbrakk> \<Longrightarrow> 
     \<exists>w. alt_dist.alt_distance P1 P2 Even G u v = alt_dist.alt_distance P1 P2 Odd G u w + 1 \<and>
         v \<in> neighbourhood G w \<and> P2 (w, v)"
proof(goal_cases)
  case 1
  then obtain p where p: "alt_dist.alt_shortest_path P1 P2 Even G u p v"
    by(force dest!: alt_dist.alt_dist_reachable elim!: alt_shortest_path_exists)
  hence "length p \<ge> 2"
    using \<open>u\<noteq>v\<close> 
    by(auto dest!: alt_dist.alt_shortest_path_vwalk 
               simp: Suc_le_length_iff eval_nat_numeral parity_simps 
               elim!: alt_dist.alt_vwalk_betE elim: vwalk_betE split: parity.splits)
  moreover have "last p = v"
    using p
    by auto
  ultimately obtain p' w where "p = p' @ [w, v]"
    by(auto simp: Suc_le_length_iff_2 eval_nat_numeral)

  obtain parity where "alt_dist.alt_shortest_path P1 P2 parity G u (p' @ [w]) w"
    using \<open>alt_dist.alt_shortest_path P1 P2 Even G u p v\<close>
    by (auto dest: alt_shortest_path_split_1 simp: \<open>p = p' @ [w, v]\<close> parity_simps split: parity.splits)

  moreover have "parity = Odd"
  proof(rule ccontr, goal_cases)
    case 1
    hence "parity = Even" using parity.exhaust by auto
    hence "odd (length (p' @ [w]))"
      using \<open>alt_dist.alt_shortest_path P1 P2 parity G u (p' @ [w]) w\<close>
      by (auto dest!: alt_dist.alt_shortest_path_vwalk elim!: alt_dist.alt_vwalk_betE simp: parity_simps)
    moreover have "odd (length p)"
      using p 
      by (auto dest!: alt_dist.alt_shortest_path_vwalk elim!: alt_dist.alt_vwalk_betE simp: parity_simps)
    hence "even (length (p' @ [w]))"
      by (auto simp: \<open>p= p' @ [w, v]\<close>)
    ultimately show ?case
      by auto
  qed

  hence "alt_dist.alt_distance P1 P2 (other_parity parity) G u v = alt_dist.alt_distance P1 P2 parity G u w + 1"
  proof -
    have eq1: "alt_dist.alt_distance P1 P2 Even G u v = enat (length p' + 1)"
      using alt_dist.alt_shortest_path_dist[OF \<open>alt_dist.alt_shortest_path P1 P2 Even G u p v\<close>]
            \<open>p = p' @ [w,v]\<close>
      by simp
    have eq2: "alt_dist.alt_distance P1 P2 Odd G u w = enat (length p')"
      using alt_dist.alt_shortest_path_dist[OF \<open>alt_dist.alt_shortest_path P1 P2 parity G u (p' @ [w]) w\<close>]
            \<open>parity = Odd\<close>
      by simp
    show ?thesis
      using eq1 eq2
      by(simp add: \<open>parity = Odd\<close> parity_simps eSuc_plus_1 eSuc_enat)
  qed
  moreover have "v \<in> neighbourhood G w"
    using \<open>alt_dist.alt_shortest_path P1 P2 Even G u p v\<close> \<open>p = p' @ [w,v]\<close> vwalk_bet_suffix_is_vwalk_bet
    by(fastforce elim: alt_dist.alt_vwalk_betE
                 simp: \<open>p = p' @ [w,v]\<close> 
                 dest!: alt_dist.alt_shortest_path_vwalk)
  moreover have "P2 (w, v)"
  proof-
    have bet: "alt_dist.alt_vwalk_bet P1 P2 Even G u p v"
      using \<open>alt_dist.alt_shortest_path P1 P2 Even G u p v\<close>
      by(rule alt_dist.alt_shortest_path_vwalk)
    have "P2 (last (edges_of_vwalk p))"
      using bet \<open>2 \<le> length p\<close>
      by(rule alternating_list_even_last)
    moreover have "last (edges_of_vwalk p) = (w, v)"
    proof -
      have "last (edges_of_vwalk (p' @ [w, v])) = (w, v)"
      proof(induction p' rule: rev_induct)
        case Nil
        show ?case by simp
      next
        case (snoc x xs)
        show ?case
          using edges_of_vwalk_append_two_vertices[of "xs @ [x]" w v]
          by simp
      qed
      thus ?thesis using \<open>p = p' @ [w, v]\<close> by simp
    qed
    ultimately show ?thesis by simp
  qed
  ultimately show ?thesis
    by (auto simp: \<open>parity = Odd\<close> parity_simps)
qed

lemma odd_alt_distance_parent: 
 "\<lbrakk>alt_dist.alt_distance P1 P2 Odd G u v < \<infinity>; u \<noteq> v\<rbrakk> \<Longrightarrow> 
     \<exists>w. alt_dist.alt_distance P1 P2 Odd G u v = alt_dist.alt_distance P1 P2 Even G u w + 1 \<and>
         v \<in> neighbourhood G w \<and> P1 (w, v)"
proof(goal_cases)
  case 1
  then obtain p where p: "alt_dist.alt_shortest_path P1 P2 Odd G u p v"
    by(force dest!: alt_dist.alt_dist_reachable elim!: alt_shortest_path_exists)
  hence "length p \<ge> 2"
    using \<open>u\<noteq>v\<close> 
    by(auto dest!: alt_dist.alt_shortest_path_vwalk 
               simp: Suc_le_length_iff eval_nat_numeral parity_simps 
               elim!: alt_dist.alt_vwalk_betE elim: vwalk_betE split: parity.splits)
  moreover have "last p = v"
    using p
    by auto
  ultimately obtain p' w where "p = p' @ [w, v]"
    by(auto simp: Suc_le_length_iff_2 eval_nat_numeral)

  obtain parity where "alt_dist.alt_shortest_path P1 P2 parity G u (p' @ [w]) w"
    using \<open>alt_dist.alt_shortest_path P1 P2 Odd G u p v\<close>
    by (auto dest: alt_shortest_path_split_2 simp: \<open>p = p' @ [w, v]\<close> parity_simps split: parity.splits)

  moreover have "parity = Even"
  proof(rule ccontr, goal_cases)
    case 1
    hence "parity = Odd" using parity.exhaust by auto
    hence "even (length (p' @ [w]))"
      using \<open>alt_dist.alt_shortest_path P1 P2 parity G u (p' @ [w]) w\<close>
      by (auto dest!: alt_dist.alt_shortest_path_vwalk elim!: alt_dist.alt_vwalk_betE simp: parity_simps)
    moreover have "even (length p)"
      using p 
      by (auto dest!: alt_dist.alt_shortest_path_vwalk elim!: alt_dist.alt_vwalk_betE simp: parity_simps)
    hence "odd (length (p' @ [w]))"
      by (auto simp: \<open>p= p' @ [w, v]\<close>)
    ultimately show ?case
      by auto
  qed

  hence "alt_dist.alt_distance P1 P2 (other_parity parity) G u v = alt_dist.alt_distance P1 P2 parity G u w + 1"
  proof -
    have eq1: "alt_dist.alt_distance P1 P2 Odd G u v = enat (length p' + 1)"
      using alt_dist.alt_shortest_path_dist[OF \<open>alt_dist.alt_shortest_path P1 P2 Odd G u p v\<close>]
            \<open>p = p' @ [w,v]\<close>
      by simp
    have eq2: "alt_dist.alt_distance P1 P2 Even G u w = enat (length p')"
      using alt_dist.alt_shortest_path_dist[OF \<open>alt_dist.alt_shortest_path P1 P2 parity G u (p' @ [w]) w\<close>]
            \<open>parity = Even\<close>
      by simp
    show ?thesis
      using eq1 eq2
      by(simp add: \<open>parity = Even\<close> parity_simps eSuc_plus_1 eSuc_enat)
  qed
  moreover have "v \<in> neighbourhood G w"
    using \<open>alt_dist.alt_shortest_path P1 P2 Odd G u p v\<close> \<open>p = p' @ [w,v]\<close> vwalk_bet_suffix_is_vwalk_bet
    by(fastforce elim: alt_dist.alt_vwalk_betE
                 simp: \<open>p = p' @ [w,v]\<close> 
                 dest!: alt_dist.alt_shortest_path_vwalk)
  moreover have "P1 (w, v)"
  proof-
    have bet: "alt_dist.alt_vwalk_bet P1 P2 Odd G u p v"
      using \<open>alt_dist.alt_shortest_path P1 P2 Odd G u p v\<close>
      by(rule alt_dist.alt_shortest_path_vwalk)
    have "P1 (last (edges_of_vwalk p))"
      using bet \<open>2 \<le> length p\<close>
      by(rule alternating_list_odd_last)
    moreover have "last (edges_of_vwalk p) = (w, v)"
    proof -
      have "last (edges_of_vwalk (p' @ [w, v])) = (w, v)"
      proof(induction p' rule: rev_induct)
        case Nil
        show ?case by simp
      next
        case (snoc x xs)
        show ?case
          using edges_of_vwalk_append_two_vertices[of "xs @ [x]" w v]
          by simp
      qed
      thus ?thesis using \<open>p = p' @ [w, v]\<close> by simp
    qed
    ultimately show ?thesis by simp
  qed
  ultimately show ?thesis
    by (auto simp: \<open>parity = Even\<close> parity_simps)
qed

subsection \<open>Distance from a set of vertices\<close>

context alt_dist
begin

definition "alt_distance_set parity G U v = ( INF u\<in>U. alt_distance parity G u v)"
                                                               
(*TODO: intro rule*)

lemma alt_dist_set_inf: "v \<notin> dVs G \<Longrightarrow> alt_distance_set parity G U v = \<infinity>"
  by(auto simp: alt_distance_set_def INF_eqI alt_dist_inf)

lemma alt_dist_set_mem[intro]: "u \<in> U \<Longrightarrow> alt_distance_set parity G U v \<le> alt_distance parity G u v"
  by (auto simp: alt_distance_set_def wellorder_Inf_le1)
end

lemma even_dist_not_inf'':
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 Even G U v \<noteq> \<infinity>; u\<in>U; 
    alt_dist.alt_distance P1 P2 Even G u v = alt_dist.alt_distance_set P1 P2 Even G U v\<rbrakk>
    \<Longrightarrow> \<exists>p. alt_dist.alt_vwalk_bet P1 P2 Even G u (u#p) v \<and>
            length p = alt_dist.alt_distance P1 P2 Even G u v \<and>
            (\<forall>p1 w p2. p = p1 @ w # p2 \<and>
                       alt_dist.alt_vwalk_bet P1 P2 Even G w (w # p2) v
                           \<longrightarrow> w \<notin> U)"
proof(goal_cases)
  case main: 1
  then obtain p where "alt_dist.alt_vwalk_bet P1 P2 Even G u (u#p) v"
                      "length p = alt_dist.alt_distance P1 P2 Even G u v"
  proof(goal_cases)
    case 1
    have "alt_dist.alt_distance P1 P2 Even G u v < \<infinity>"
      using main(1) main(3) by (simp add: less_le)
    then obtain q where q_sp: "alt_dist.alt_shortest_path P1 P2 Even G u q v"
      by(rule alt_shortest_path_exists_2)
    have q_ne: "q \<noteq> []"
      using q_sp
      by(auto simp: alt_dist.alt_shortest_path_def vwalk_bet_def elim!: alt_dist.alt_vwalk_betE)
    have q_hd: "hd q = u"
      using alt_dist.alt_shortest_path_hd[OF q_sp] by simp
    have q_cons: "q = u # tl q"
      using q_ne q_hd by(cases q) auto
    have bet: "alt_dist.alt_vwalk_bet P1 P2 Even G u (u # tl q) v"
      by(subst q_cons[symmetric]) (rule alt_dist.alt_shortest_path_vwalk[OF q_sp])
    have len: "length (tl q) = alt_dist.alt_distance P1 P2 Even G u v"
      using alt_dist.alt_shortest_path_dist[OF q_sp] q_ne
      by(simp add: length_tl)
    show ?case
      by(rule 1[OF bet len])
  qed

  moreover have "w \<notin> U" if "p = p1 @ w # p2" "alt_dist.alt_vwalk_bet P1 P2 Even G w (w # p2) v" for p1 w p2
  proof(rule ccontr, goal_cases)
    case 1
    have "length (w#p2) < length (u#p)"
      using that
      by auto
    moreover have "alt_dist.alt_vwalk_bet P1 P2 Even G w (w # p2) v"
      using that
      by fastforce
    hence "alt_dist.alt_distance P1 P2 Even G w v \<le> length p2"
      by(auto dest!: alt_dist.alt_vwalk_bet_alt_dist)
    ultimately have "alt_dist.alt_distance_set P1 P2 Even G U v \<le> length p2"
      using 1
      by(auto dest!: alt_dist.alt_dist_set_mem dest: order.trans)
    moreover have "length p \<le> alt_dist.alt_distance_set P1 P2 Even G U v"
      by (simp add: \<open>enat (length p) = alt_dist.alt_distance P1 P2 Even G u v\<close> main(3))
    moreover have " enat (length p2) < eSuc (enat (length p1 + length p2))"
      by auto
    ultimately have le: "enat (length p) \<le> enat (length p2)"
      by(blast intro: order.trans)
    moreover have "length p = length p1 + Suc (length p2)"
      using \<open>p = p1 @ w # p2\<close> by simp
    ultimately show ?case
      by (simp add: not_less[symmetric])
  qed
  ultimately show ?thesis
    by auto
qed

lemma even_dist_not_inf''':
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 Even G U v \<noteq> \<infinity>; u\<in>U;
    alt_dist.alt_distance P1 P2 Even G u v = alt_dist.alt_distance_set P1 P2 Even G U v\<rbrakk>
      \<Longrightarrow> \<exists>p. alt_dist.alt_shortest_path P1 P2 Even G u (u#p) v \<and> 
              (\<forall>p1 w p2. p = p1 @ w # p2 \<and> alt_dist.alt_vwalk_bet P1 P2 Even G w (w # p2) v
                           \<longrightarrow> w \<notin> U)"
proof(goal_cases)
  case 1
  obtain p where p: "alt_dist.alt_vwalk_bet P1 P2 Even G u (u#p) v"
    "length p = alt_dist.alt_distance P1 P2 Even G u v"
    "\<forall>p1 w p2. p = p1 @ w # p2 \<and> alt_dist.alt_vwalk_bet P1 P2 Even G w (w # p2) v \<longrightarrow> w \<notin> U"
    using even_dist_not_inf''[OF 1] by blast
  have "alt_dist.alt_shortest_path P1 P2 Even G u (u#p) v"
    using p(1) p(2) by(auto simp: alt_dist.alt_shortest_path_def)
  thus ?case
    using p(3) by blast
qed

lemma odd_dist_not_inf'':
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 Odd G U v \<noteq> \<infinity>; u\<in>U; 
    alt_dist.alt_distance P1 P2 Odd G u v = alt_dist.alt_distance_set P1 P2 Odd G U v\<rbrakk>
    \<Longrightarrow> \<exists>p. alt_dist.alt_vwalk_bet P1 P2 Odd G u (u#p) v \<and>
            length p = alt_dist.alt_distance P1 P2 Odd G u v \<and>
            (\<forall>p1 w p2. p = p1 @ w # p2 \<and> alt_dist.alt_vwalk_bet P1 P2 Odd G w (w # p2) v
                           \<longrightarrow> w \<notin> U)"
proof(goal_cases)
  case main: 1
  then obtain p where "alt_dist.alt_vwalk_bet P1 P2 Odd G u (u#p) v"
                      "length p = alt_dist.alt_distance P1 P2 Odd G u v"
  proof(goal_cases)
    case 1
    have "alt_dist.alt_distance P1 P2 Odd G u v < \<infinity>"
      using main(1) main(3) by (simp add: less_le)
    then obtain q where q_sp: "alt_dist.alt_shortest_path P1 P2 Odd G u q v"
      by(rule alt_shortest_path_exists_2)
    have q_ne: "q \<noteq> []"
      using q_sp
      by(auto simp: alt_dist.alt_shortest_path_def vwalk_bet_def elim!: alt_dist.alt_vwalk_betE)
    have q_hd: "hd q = u"
      using alt_dist.alt_shortest_path_hd[OF q_sp] by simp
    have q_cons: "q = u # tl q"
      using q_ne q_hd by(cases q) auto
    have bet: "alt_dist.alt_vwalk_bet P1 P2 Odd G u (u # tl q) v"
      by(subst q_cons[symmetric]) (rule alt_dist.alt_shortest_path_vwalk[OF q_sp])
    have len: "length (tl q) = alt_dist.alt_distance P1 P2 Odd G u v"
      using alt_dist.alt_shortest_path_dist[OF q_sp] q_ne
      by(simp add: length_tl)
    show ?case
      by(rule 1[OF bet len])
  qed

  moreover have "w \<notin> U" if "p = p1 @ w # p2" "alt_dist.alt_vwalk_bet P1 P2 Odd G w (w # p2) v" for p1 w p2
  proof(rule ccontr, goal_cases)
    case 1
    have "length (w#p2) < length (u#p)"
      using that
      by auto
    moreover have "alt_dist.alt_vwalk_bet P1 P2 Odd G w (w # p2) v"
      using that
      by fastforce
    hence "alt_dist.alt_distance P1 P2 Odd G w v \<le> length p2"
      by(auto dest!: alt_dist.alt_vwalk_bet_alt_dist)
    ultimately have "alt_dist.alt_distance_set P1 P2 Odd G U v \<le> length p2"
      using 1
      by(auto dest!: alt_dist.alt_dist_set_mem dest: order.trans)
    moreover have "length p \<le> alt_dist.alt_distance_set P1 P2 Odd G U v"
      by (simp add: \<open>enat (length p) = alt_dist.alt_distance P1 P2 Odd G u v\<close> main(3))
    moreover have " enat (length p2) < eSuc (enat (length p1 + length p2))"
      by auto
    ultimately have le: "enat (length p) \<le> enat (length p2)"
      by(blast intro: order.trans)
    moreover have "length p = length p1 + Suc (length p2)"
      using \<open>p = p1 @ w # p2\<close> by simp
    ultimately show ?case
      by (simp add: not_less[symmetric])
  qed
  ultimately show ?thesis
    by auto
qed

lemma odd_dist_not_inf''':
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 Odd G U v \<noteq> \<infinity>; u\<in>U;
    alt_dist.alt_distance P1 P2 Odd G u v = alt_dist.alt_distance_set P1 P2 Odd G U v\<rbrakk>
      \<Longrightarrow> \<exists>p. alt_dist.alt_shortest_path P1 P2 Odd G u (u#p) v \<and> 
              (\<forall>p1 w p2. p = p1 @ w # p2 \<and> alt_dist.alt_vwalk_bet P1 P2 Odd G w (w # p2) v
                           \<longrightarrow> w \<notin> U)"
proof(goal_cases)
  case 1
  obtain p where p: "alt_dist.alt_vwalk_bet P1 P2 Odd G u (u#p) v"
    "length p = alt_dist.alt_distance P1 P2 Odd G u v"
    "\<forall>p1 w p2. p = p1 @ w # p2 \<and> alt_dist.alt_vwalk_bet P1 P2 Odd G w (w # p2) v \<longrightarrow> w \<notin> U"
    using odd_dist_not_inf''[OF 1] by blast
  have "alt_dist.alt_shortest_path P1 P2 Odd G u (u#p) v"
    using p(1) p(2) by(auto simp: alt_dist.alt_shortest_path_def)
  thus ?case
    using p(3) by blast
qed

(*lemma distance_set_split:
  "\<lbrakk>distance_set G U v \<noteq> \<infinity>; distance_set G U v = distance_set G U w + distance_set G U' v; w \<in> U' \<rbrakk> \<Longrightarrow>
       \<exists>w'\<in>U'. reachable G u w' \<and> distance G u w' = distance G u w \<and>
            reachable G w' v \<and> distance G w' v = distance G w' v"
proof(goal_cases)
  case 1
  hence "distance_set G U' v \<noteq> \<infinity>"
    by (simp add: plus_eq_infty_iff_enat)
  then obtain w' where "w' \<in> U'" "distance_set G U' v = distance G w' v" "reachable G w' v"
    using 1
    by (metis dist_not_inf')
*)

lemma alt_distance_set_union:
  "alt_dist.alt_distance_set P1 P2 parity G (U \<union> V) v \<le> alt_dist.alt_distance_set P1 P2 parity G U v"
  by (simp add: alt_dist.alt_distance_set_def INF_superset_mono)   

lemma lt_lt_infnty: "x < (y::enat) \<Longrightarrow> x < \<infinity>"
  using enat_ord_code(3) order_less_le_trans
  by blast

lemma finite_alt_dist_nempty:
  "alt_dist.alt_distance_set P1 P2 parity G V v \<noteq> \<infinity> \<Longrightarrow> V \<noteq> {}"
  by (auto simp: alt_dist.alt_distance_set_def top_enat_def)

lemma alt_distance_set_wit: 
  assumes "v \<in> V"
  obtains v' where "v' \<in> V" "alt_dist.alt_distance_set P1 P2 parity G V x = alt_dist.alt_distance P1 P2 parity G v' x"
  using assms wellorder_InfI[of "alt_dist.alt_distance P1 P2 parity G v x" "(%v. alt_dist.alt_distance P1 P2 parity G v x) ` V"]
  by (auto simp: alt_dist.alt_distance_set_def image_def dest!: )

lemma alt_distance_set_wit':
  assumes "alt_dist.alt_distance_set P1 P2 parity G V v \<noteq> \<infinity>"
  obtains v' where "v' \<in> V" "alt_dist.alt_distance_set P1 P2 parity G V x = alt_dist.alt_distance P1 P2 parity G v' x"
  using finite_alt_dist_nempty[OF assms]
  by (auto elim: alt_distance_set_wit)

lemma alt_dist_set_not_inf: 
  "alt_dist.alt_distance_set P1 P2 parity G U v \<noteq> \<infinity> 
   \<Longrightarrow> \<exists>u\<in>U. alt_dist.alt_distance P1 P2 parity G u v = alt_dist.alt_distance_set P1 P2 parity G U v"
proof(goal_cases)
  case 1
  then obtain u where "u \<in> U"
    "alt_dist.alt_distance_set P1 P2 parity G U v = alt_dist.alt_distance P1 P2 parity G u v"
    by(rule alt_distance_set_wit')
  thus ?case
    by force
qed

lemma alt_dist_not_inf':
  "alt_dist.alt_distance_set P1 P2 parity G U v \<noteq> \<infinity> \<Longrightarrow>
     \<exists>u\<in>U. alt_dist.alt_distance P1 P2 parity G u v = alt_dist.alt_distance_set P1 P2 parity G U v \<and> alt_dist.alt_reachable P1 P2 parity G u v"
proof(goal_cases)
  case 1
  from alt_dist_set_not_inf[OF 1] obtain u where u: "u \<in> U"
    "alt_dist.alt_distance P1 P2 parity G u v = alt_dist.alt_distance_set P1 P2 parity G U v"
    by(auto)
  have "alt_dist.alt_distance P1 P2 parity G u v < \<infinity>"
    using u(2) 1 by (simp add: less_le)
  hence "alt_dist.alt_reachable P1 P2 parity G u v"
    by(rule alt_dist.alt_dist_reachable)
  thus ?case
    using u by auto
qed

lemma alt_shortest_path_Parity: 
  "alt_dist.alt_shortest_path P1 P2 parity G u (p1 @[x]) x \<Longrightarrow> of_parity (other_parity parity) (length (p1 @ [x]))"
  by (auto elim!: alt_dist.alt_shortest_path_props alt_dist.alt_vwalk_betE)

lemma alt_distance_on_vwalk:
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 parity G U v = alt_dist.alt_distance P1 P2 parity G u v; u \<in> U;
    alt_dist.alt_shortest_path P1 P2 parity G u (p1 @ x # p2) v\<rbrakk>
       \<Longrightarrow> \<exists>parity'. alt_dist.alt_distance_set P1 P2 parity' G U x = alt_dist.alt_distance P1 P2 parity' G u x \<and>
                     of_parity (other_parity parity') (length (p1 @ [x]))"
proof(goal_cases)
  case assms: 1
  moreover have 
    "\<exists>parity'. alt_dist.alt_distance P1 P2 parity' G u x \<le> alt_dist.alt_distance_set P1 P2 parity' G U x \<and>
               of_parity (other_parity parity') (length (p1 @ [x]))"
  proof(rule ccontr, goal_cases)
    case alt_dist_gt: 1

    have "\<exists>parity'. alt_dist.alt_distance_set P1 P2 parity' G U x \<noteq> \<infinity> \<and>
                     of_parity (other_parity parity') (length (p1 @ [x]))"
    proof-
      obtain parityw where pw: "of_parity (other_parity parityw) (length (p1 @ [x]))"
      proof(cases "even (length (p1 @ [x]))")
        case True
        thus ?thesis by(intro that[of Odd]) (simp add: parity_simps)
      next
        case False
        thus ?thesis by(intro that[of Even]) (simp add: parity_simps)
      qed
      have "\<not> alt_dist.alt_distance P1 P2 parityw G u x \<le> alt_dist.alt_distance_set P1 P2 parityw G U x"
        using alt_dist_gt pw by blast
      hence "alt_dist.alt_distance_set P1 P2 parityw G U x \<noteq> \<infinity>"
        by(force simp: linorder_not_le dest: lt_lt_infnty)
      thus ?thesis
        using pw by blast
    qed

    then obtain u' parity' where 
          "u' \<in> U"
          "alt_dist.alt_distance P1 P2 parity' G u' x < alt_dist.alt_distance P1 P2 parity' G u x"
          "of_parity (other_parity parity') (length (p1 @ [x]))"
    proof(goal_cases)
      case 1
      from \<open>\<exists>parity'. alt_dist.alt_distance_set P1 P2 parity' G U x \<noteq> \<infinity> \<and>
                     of_parity (other_parity parity') (length (p1 @ [x]))\<close>
      obtain parity' where par: "alt_dist.alt_distance_set P1 P2 parity' G U x \<noteq> \<infinity>"
        "of_parity (other_parity parity') (length (p1 @ [x]))"
        by blast
      obtain u' where u': "u' \<in> U"
        "alt_dist.alt_distance P1 P2 parity' G u' x = alt_dist.alt_distance_set P1 P2 parity' G U x"
        using alt_dist_set_not_inf[OF par(1)] by blast
      have "\<not> alt_dist.alt_distance P1 P2 parity' G u x \<le> alt_dist.alt_distance_set P1 P2 parity' G U x"
        using alt_dist_gt par(2) by blast
      hence "alt_dist.alt_distance P1 P2 parity' G u' x < alt_dist.alt_distance P1 P2 parity' G u x"
        using u'(2) by(simp add: linorder_not_le)
      from 1[OF u'(1) this par(2)] show ?case .
    qed
    moreover then obtain p' where p': "alt_dist.alt_shortest_path P1 P2 parity' G u' p' x"
      by (fastforce dest: lt_lt_infnty elim!: alt_shortest_path_exists_2)


    have "alt_dist.alt_vwalk_bet P1 P2 parity G u' (p' @ tl ([x] @ p2)) v"
    proof-
      have "alt_list P1 P2 (edges_of_vwalk p')"
        using p'
        by(auto elim!: alt_dist.alt_vwalk_betE dest!: alt_dist.alt_shortest_path_vwalk)

      moreover have "alt_list P1 P2 (edges_of_vwalk (p1 @ x # p2))"
        using \<open>alt_dist.alt_shortest_path P1 P2 parity G u (p1 @ x # p2) v\<close>
        by(auto elim!: alt_dist.alt_vwalk_betE dest!: alt_dist.alt_shortest_path_vwalk)

      obtain parity'' where "alt_dist.alt_shortest_path P1 P2 parity'' G u (p1 @[x]) x"
        "parity = Odd \<Longrightarrow> next_alt_list_parity parity'' alt_dist.alt_shortest_path P1 P2 (other_parity parity'') G x (x # p2) v"
        "parity = Even \<Longrightarrow> next_alt_list_parity parity'' alt_dist.alt_shortest_path P1 P2 parity'' G x (x # p2) v"
        using \<open>alt_dist.alt_shortest_path P1 P2 parity G u (p1 @ x # p2) v\<close>
        by (cases parity) (auto dest!: alt_shortest_path_split_1 alt_shortest_path_split_2)
      moreover hence "parity'' = parity'"
        using \<open>of_parity (other_parity parity') (length (p1 @ [x]))\<close>
        by (auto dest!: alt_shortest_path_Parity simp: parity_simps split: parity.splits)
      ultimately have alt_vwalks: 
        "alt_dist.alt_shortest_path P1 P2 parity' G u (p1 @[x]) x"
        "parity = Odd \<Longrightarrow> next_alt_list_parity parity' alt_dist.alt_shortest_path P1 P2 (other_parity parity') G x (x # p2) v"
        "parity = Even \<Longrightarrow> next_alt_list_parity parity' alt_dist.alt_shortest_path P1 P2 parity' G x (x # p2) v"
        by auto

      have "last p' = x"
        using p' by auto
    
      have "alt_dist.alt_vwalk_bet P1 P2 Odd G u' (p' @ tl ([x] @ p2)) v" if "parity = Odd"
      proof(rule alt_vwalk_bet_append_3[where parity = parity'])
        show "alt_dist.alt_vwalk_bet P1 P2 parity' G u' p' (last p')"
          using p' that
          by(auto elim!: alt_dist.alt_shortest_path_props simp add: \<open>last p' = x\<close>)
        show "next_alt_list_parity parity' alt_dist.alt_vwalk_bet P1 P2 (other_parity parity') G (last p') (last p' # tl ([x] @ p2)) v"
          using p' that alt_vwalks(2,3)
          by(auto elim!: alt_dist.alt_shortest_path_props simp add: parity_simps \<open>last p' = x\<close> split: parity.splits)
        show "p' \<noteq> []"
          using p'
          by(auto simp: alt_dist.alt_shortest_path_def vwalk_bet_def elim!: alt_dist.alt_vwalk_betE)
      qed

      moreover have "alt_dist.alt_vwalk_bet P1 P2 Even G u' (p' @ tl ([x] @ p2)) v" if "parity = Even"
      proof(rule alt_vwalk_bet_append_2[where parity = parity'])
        show "alt_dist.alt_vwalk_bet P1 P2 parity' G u' p' (last p')"
          using p' that
          by(auto elim!: alt_dist.alt_shortest_path_props simp add: \<open>last p' = x\<close>)
        show "next_alt_list_parity parity' alt_dist.alt_vwalk_bet P1 P2 parity' G (last p') (last p' # tl ([x] @ p2)) v"
          using p' that alt_vwalks(2,3)
          by(auto elim!: alt_dist.alt_shortest_path_props simp add: parity_simps \<open>last p' = x\<close> split: parity.splits)
        show "p' \<noteq> []"
          using p'
          by(auto simp: alt_dist.alt_shortest_path_def vwalk_bet_def elim!: alt_dist.alt_vwalk_betE)
      qed
      ultimately show ?thesis
        by (cases parity, auto)
    qed


    obtain parity'' where *: "alt_dist.alt_shortest_path P1 P2 parity'' G u (p1 @[x]) x"
      using \<open>alt_dist.alt_shortest_path P1 P2 parity G u (p1 @ x # p2) v\<close>
      by (cases parity) (auto dest!: alt_shortest_path_split_1 alt_shortest_path_split_2)
    moreover hence "parity'' = parity'"
      using \<open>of_parity (other_parity parity') (length (p1 @ [x]))\<close>
      by (auto dest!: alt_shortest_path_Parity simp: parity_simps split: parity.splits)

    ultimately have "length (p' @ tl ([x] @ p2)) - 1 < length (p1 @ x # p2) - 1"
      using \<open>alt_dist.alt_shortest_path P1 P2 parity' G u' p' x\<close>
            \<open>alt_dist.alt_distance P1 P2 parity' G u' x < alt_dist.alt_distance P1 P2 parity' G u x\<close>
      by(auto dest!: alt_dist.alt_shortest_path_dist)
    hence "length (p' @ tl ([x] @ p2)) - 1 < alt_dist.alt_distance_set P1 P2 parity G U v"
      using assms(1,3) alt_dist.alt_shortest_path_dist
      by force
    moreover have "alt_dist.alt_distance P1 P2 parity G u' v \<le> length (p' @ tl ([x] @ p2)) - 1"
      using \<open>alt_dist.alt_vwalk_bet P1 P2 parity G u' (p' @ tl ([x] @ p2)) v\<close>
      by(rule alt_dist.alt_vwalk_bet_alt_dist)
    moreover have "alt_dist.alt_distance_set P1 P2 parity G U v \<le> alt_dist.alt_distance P1 P2 parity G u' v"
      by(rule alt_dist.alt_dist_set_mem[OF \<open>u' \<in> U\<close>])
    ultimately show False
      by(auto simp: leD dest: order.trans)
  qed
  ultimately show ?thesis
  proof-
    from \<open>\<exists>parity'. alt_dist.alt_distance P1 P2 parity' G u x \<le> alt_dist.alt_distance_set P1 P2 parity' G U x \<and>
               of_parity (other_parity parity') (length (p1 @ [x]))\<close>
    obtain parity' where le: "alt_dist.alt_distance P1 P2 parity' G u x \<le> alt_dist.alt_distance_set P1 P2 parity' G U x"
      and par: "of_parity (other_parity parity') (length (p1 @ [x]))"
      by blast
    have "alt_dist.alt_distance_set P1 P2 parity' G U x = alt_dist.alt_distance P1 P2 parity' G u x"
      using alt_dist.alt_dist_set_mem[OF assms(2)] le
      by(rule antisym)
    thus ?thesis
      using par by blast
  qed
qed

lemma even_alt_distance_set_neighbourhood:
  "\<lbrakk>v \<in> neighbourhood G u; vs \<noteq> {}; P2 (u, v)\<rbrakk> \<Longrightarrow>
    alt_dist.alt_distance_set P1 P2 Even G vs v \<le> alt_dist.alt_distance_set P1 P2 Odd G vs u + 1"
proof(goal_cases)
  case assms: 1
  hence "(INF w\<in> vs. alt_dist.alt_distance P1 P2 Even G w v) \<le> (INF w\<in> vs. alt_dist.alt_distance P1 P2 Odd G w u + 1)"
    by (auto simp add: even_alt_distance_neighbourhood' intro!: INF_mono')
  also have "... = (INF w\<in> vs.  alt_dist.alt_distance P1 P2 Odd G w u) + (1::enat)"
    using \<open>vs \<noteq> {}\<close> 
    by (auto simp: INF_plus_enat)
  finally show ?case
    by(simp only: alt_dist.alt_distance_set_def)
qed

lemma odd_alt_distance_set_neighbourhood:
  "\<lbrakk>v \<in> neighbourhood G u; vs \<noteq> {}; P1 (u, v)\<rbrakk> \<Longrightarrow>
    alt_dist.alt_distance_set P1 P2 Odd G vs v \<le> alt_dist.alt_distance_set P1 P2 Even G vs u + 1"
proof(goal_cases)
  case assms: 1
  hence "(INF w\<in> vs. alt_dist.alt_distance P1 P2 Odd G w v) \<le> (INF w\<in> vs. alt_dist.alt_distance P1 P2 Even G w u + 1)"
    by (auto simp add: odd_alt_distance_neighbourhood' intro!: INF_mono')
  also have "... = (INF w\<in> vs.  alt_dist.alt_distance P1 P2 Even G w u) + (1::enat)"
    using \<open>vs \<noteq> {}\<close> 
    by (auto simp: INF_plus_enat)
  finally show ?case
    by(simp only: alt_dist.alt_distance_set_def)
qed

lemma even_alt_distance_set_parent:
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 Even G vs v < \<infinity>; vs \<noteq> {}; v \<notin> vs\<rbrakk> \<Longrightarrow> 
     \<exists>w. alt_dist.alt_distance_set P1 P2 Odd G vs w + 1 = alt_dist.alt_distance_set P1 P2 Even G vs v \<and> v \<in> neighbourhood G w \<and> P2 (w, v)"
proof(goal_cases)
  case 1
  moreover hence "alt_dist.alt_distance_set P1 P2 Even G vs v \<noteq> \<infinity>"
    by auto
  ultimately obtain u where \<open>u \<in> vs\<close> \<open>alt_dist.alt_distance_set P1 P2 Even G vs v = alt_dist.alt_distance P1 P2 Even G u v \<close> \<open>u \<noteq> v\<close>
    by(fastforce elim!: alt_distance_set_wit')
  moreover then obtain w where "alt_dist.alt_distance P1 P2 Odd G u w + 1 = alt_dist.alt_distance P1 P2 Even G u v" "v \<in> neighbourhood G w" "P2 (w, v)"
    using 1 even_alt_distance_parent
    by fastforce
  moreover have "alt_dist.alt_distance_set P1 P2 Odd G vs w + 1 = alt_dist.alt_distance_set P1 P2 Even G vs v"
  proof(rule antisym)
    have "alt_dist.alt_distance_set P1 P2 Odd G vs w \<le> alt_dist.alt_distance P1 P2 Odd G u w"
      using \<open>u \<in> vs\<close> by(rule alt_dist.alt_dist_set_mem)
    hence "alt_dist.alt_distance_set P1 P2 Odd G vs w + 1 \<le> alt_dist.alt_distance P1 P2 Odd G u w + 1"
      by(simp add: add_right_mono)
    thus "alt_dist.alt_distance_set P1 P2 Odd G vs w + 1 \<le> alt_dist.alt_distance_set P1 P2 Even G vs v"
      by(simp add: \<open>alt_dist.alt_distance P1 P2 Odd G u w + 1 = alt_dist.alt_distance P1 P2 Even G u v\<close>
                   \<open>alt_dist.alt_distance_set P1 P2 Even G vs v = alt_dist.alt_distance P1 P2 Even G u v \<close>)
    show "alt_dist.alt_distance_set P1 P2 Even G vs v \<le> alt_dist.alt_distance_set P1 P2 Odd G vs w + 1"
      using \<open>v \<in> neighbourhood G w\<close> 1(2) \<open>P2 (w, v)\<close>
      by(intro even_alt_distance_set_neighbourhood)
  qed
  ultimately show ?thesis
    by blast
qed

lemma odd_alt_distance_set_parent:
  "\<lbrakk>alt_dist.alt_distance_set P1 P2 Odd G vs v < \<infinity>; vs \<noteq> {}; v \<notin> vs\<rbrakk> \<Longrightarrow> 
     \<exists>w. alt_dist.alt_distance_set P1 P2 Even G vs w + 1 = alt_dist.alt_distance_set P1 P2 Odd G vs v \<and> v \<in> neighbourhood G w \<and> P1 (w, v)"
proof(goal_cases)
  case 1
  moreover hence "alt_dist.alt_distance_set P1 P2 Odd G vs v \<noteq> \<infinity>"
    by auto
  ultimately obtain u where \<open>u \<in> vs\<close> \<open>alt_dist.alt_distance_set P1 P2 Odd G vs v = alt_dist.alt_distance P1 P2 Odd G u v \<close> \<open>u \<noteq> v\<close>
    by(fastforce elim!: alt_distance_set_wit')
  moreover then obtain w where "alt_dist.alt_distance P1 P2 Even G u w + 1 = alt_dist.alt_distance P1 P2 Odd G u v" "v \<in> neighbourhood G w" "P1 (w, v)"
    using 1 odd_alt_distance_parent
    by fastforce
  moreover have "alt_dist.alt_distance_set P1 P2 Even G vs w + 1 = alt_dist.alt_distance_set P1 P2 Odd G vs v"
  proof(rule antisym)
    have "alt_dist.alt_distance_set P1 P2 Even G vs w \<le> alt_dist.alt_distance P1 P2 Even G u w"
      using \<open>u \<in> vs\<close> by(rule alt_dist.alt_dist_set_mem)
    hence "alt_dist.alt_distance_set P1 P2 Even G vs w + 1 \<le> alt_dist.alt_distance P1 P2 Even G u w + 1"
      by(simp add: add_right_mono)
    thus "alt_dist.alt_distance_set P1 P2 Even G vs w + 1 \<le> alt_dist.alt_distance_set P1 P2 Odd G vs v"
      by(simp add: \<open>alt_dist.alt_distance P1 P2 Even G u w + 1 = alt_dist.alt_distance P1 P2 Odd G u v\<close>
                   \<open>alt_dist.alt_distance_set P1 P2 Odd G vs v = alt_dist.alt_distance P1 P2 Odd G u v \<close>)
    show "alt_dist.alt_distance_set P1 P2 Odd G vs v \<le> alt_dist.alt_distance_set P1 P2 Even G vs w + 1"
      using \<open>v \<in> neighbourhood G w\<close> 1(2) \<open>P1 (w, v)\<close>
      by(intro odd_alt_distance_set_neighbourhood)
  qed
  ultimately show ?thesis
    by blast
qed

lemma even_alt_distance_set_parent':
  "\<lbrakk>0 < alt_dist.alt_distance_set P1 P2 Even G vs v; alt_dist.alt_distance_set P1 P2 Even G vs v < \<infinity>; vs \<noteq> {}\<rbrakk> \<Longrightarrow> 
     \<exists>w. alt_dist.alt_distance_set P1 P2 Odd G vs w + 1 = alt_dist.alt_distance_set P1 P2 Even G vs v \<and> v \<in> neighbourhood G w \<and> P2 (w,v)"
proof(goal_cases)
  case 1
  have "v \<notin> vs"
  proof
    assume "v \<in> vs"
    show False
    proof(cases "v \<in> dVs G")
      case True
      hence eq0: "alt_dist.alt_distance P1 P2 Even G v v = 0"
        using even_alt_distance_0[where u=v] by simp
      have leq0: "alt_dist.alt_distance_set P1 P2 Even G vs v \<le> alt_dist.alt_distance P1 P2 Even G v v"
        using \<open>v \<in> vs\<close> by(rule alt_dist.alt_dist_set_mem)
      thus False
        using 1(1) eq0 by (simp add: leq0)
    next
      case False
      hence "alt_dist.alt_distance_set P1 P2 Even G vs v = \<infinity>"
        by(rule alt_dist.alt_dist_set_inf)
      thus False
        using 1(2) by simp
    qed
  qed
  from even_alt_distance_set_parent[OF 1(2) 1(3) this] show ?case .
qed

lemma distance_set_0[simp]: "\<lbrakk>v \<in> dVs G\<rbrakk> \<Longrightarrow> alt_dist.alt_distance_set P1 P2 Even G vs v = 0 \<longleftrightarrow> v \<in> vs"
proof(safe, goal_cases)
  case 2
  have eq0: "alt_dist.alt_distance P1 P2 Even G v v = 0"
    using 2(1) even_alt_distance_0[where u=v] by simp
  have leq: "alt_dist.alt_distance_set P1 P2 Even G vs v \<le> alt_dist.alt_distance P1 P2 Even G v v"
    using 2(2) by(rule alt_dist.alt_dist_set_mem)
  thus ?case
    by (simp add: leq eq0)
next
  case 1
  have "alt_dist.alt_distance_set P1 P2 Even G vs v \<noteq> \<infinity>"
    by(simp add: 1(2))
  from alt_dist_set_not_inf[OF this] obtain u where u: "u \<in> vs"
    "alt_dist.alt_distance P1 P2 Even G u v = alt_dist.alt_distance_set P1 P2 Even G vs v"
    by auto
  hence eq0u: "alt_dist.alt_distance P1 P2 Even G u v = 0"
    by(simp add: 1(2))
  hence "u = v"
    using even_alt_distance_0[where u=u] 1(1) by simp
  thus ?case
    using u(1) by simp
qed

lemma alt_dist_set_leq: 
  "\<lbrakk>\<And>u. u \<in> vs \<Longrightarrow> alt_dist.alt_distance P1 P2 parity G u v \<le> alt_dist.alt_distance P1 P2 parity G' u v\<rbrakk> \<Longrightarrow> alt_dist.alt_distance_set P1 P2 parity G vs v \<le> alt_dist.alt_distance_set P1 P2 parity G' vs v"
  by(auto simp: alt_dist.alt_distance_set_def INF_superset_mono)             

lemma alt_dist_set_eq: 
  "\<lbrakk>\<And>u. u \<in> vs \<Longrightarrow> alt_dist.alt_distance P1 P2 parity G u v = alt_dist.alt_distance P1 P2 parity G' u v\<rbrakk> \<Longrightarrow> alt_dist.alt_distance_set P1 P2 parity G vs v = alt_dist.alt_distance_set P1 P2 parity G' vs v"
proof(goal_cases)
  case 1
  have "alt_dist.alt_distance_set P1 P2 parity G vs v \<le> alt_dist.alt_distance_set P1 P2 parity G' vs v"
    by(intro alt_dist_set_leq) (auto simp: 1)
  moreover have "alt_dist.alt_distance_set P1 P2 parity G' vs v \<le> alt_dist.alt_distance_set P1 P2 parity G vs v"
    by(intro alt_dist_set_leq) (auto simp: 1)
  ultimately show ?case
    by(rule antisym)
qed

lemma alt_distance_set_subset: "G \<subseteq> G' \<Longrightarrow> alt_dist.alt_distance_set P1 P2 parity G' vs v \<le> alt_dist.alt_distance_set P1 P2 parity G vs v"
  by (simp add: alt_dist_set_leq alt_distance_subset)

lemma alt_vwalk_bet_alt_dist_set:
  "\<lbrakk>alt_dist.alt_vwalk_bet P1 P2 parity G u p v; u \<in> U\<rbrakk> \<Longrightarrow> alt_dist.alt_distance_set P1 P2 parity G U v \<le> length p - 1"
proof(goal_cases)
  case 1
  have "alt_dist.alt_distance_set P1 P2 parity G U v \<le> alt_dist.alt_distance P1 P2 parity G u v"
    using 1(2) by(rule alt_dist.alt_dist_set_mem)
  also have "... \<le> length p - 1"
    using 1(1) by(rule alt_dist.alt_vwalk_bet_alt_dist)
  finally show ?case .
qed
end