section \<open>Supplementary Theory for Orlin's Algorithm\<close>

theory IntermediateSummary
  imports PathAugOpt Berge_Lemma.Berge  "HOL-Data_Structures.Set_Specs" 
          Undirected_Set_Graphs.Pair_Graph_Berge_Adaptor  Directed_Set_Graphs.Pair_Graph_Specs        
begin

context flow_network
begin
lemmas number_of_comps_anti_mono_strict=number_of_comps_anti_mono_strict[OF  _ _ _ _ _ \<V>_finite]
lemmas number_of_comps_anti_mono = number_of_comps_anti_mono[OF _ _ \<V>_finite]
end

subsection \<open>Program States and Invariants\<close>

datatype return = success | failure | notyetterm

text \<open>Then we setup the program state.\<close>

record ('b, 'actives, 'forest, 'edge_type) Algo_state = current_flow :: "'edge_type \<Rightarrow> real" 
                            balance :: "'b \<Rightarrow> real"
                                  \<FF> :: "'b set set"
                             conv_to_rdg :: "'b \<times> 'b \<Rightarrow> 'edge_type flow_network_spec.Redge"
                             actives:: 'actives
                             return :: return
                             current_\<gamma>::real
                             representative::"'b \<Rightarrow> 'b"
                             comp_card::"'b \<Rightarrow> nat"
                                  \<FF>_imp :: 'forest
                             not_blocked:: "'edge_type \<Rightarrow> bool"

definition "to_rdgs to_pair to_rdg F = 
\<Union> ((\<lambda> vs. (if \<exists> u v. u \<noteq> v \<and> {u, v} = vs 
           then {to_rdg (to_pair vs), to_rdg (prod.swap (to_pair vs))}  else {} )) 
   ` F)"

lemma  to_rdg_mono: "A \<subseteq> B \<Longrightarrow> to_rdgs  a b A \<subseteq> to_rdgs a b B" for A B a b
    unfolding to_rdgs_def by auto

record ('f, 'b, '\<FF>, 'conv_to_rdg, 'actives, 'representative_comp_card, 'not_blocked)
          Algo_state_impl = current_flow_impl :: 'f
                            balance_impl :: 'b
                                  \<FF>_impl :: '\<FF>
                             conv_to_rdg_impl :: 'conv_to_rdg
                             actives_impl:: 'actives
                             return_impl:: return
                             current_\<gamma>_impl::real
                             representative_comp_card_impl::'representative_comp_card
                             not_blocked_impl::'not_blocked


locale Set3 = 
fixes get_from_set   :: "('a \<Rightarrow> bool) \<Rightarrow> 'actives  \<Rightarrow> 'a option"
fixes filter:: "('a => bool) =>'actives  => 'actives "
fixes are_all:: "('a \<Rightarrow> bool) \<Rightarrow> 'actives \<Rightarrow> bool"
fixes set_invar
fixes to_set

assumes set_get:   "\<lbrakk> set_invar s1; \<exists> x. x \<in> to_set s1 \<and> P x \<rbrakk> \<Longrightarrow> \<exists> y. get_from_set P s1 = Some y"
                   "\<lbrakk> set_invar s1; get_from_set P s1 = Some x\<rbrakk> \<Longrightarrow> x \<in> to_set s1"
                   "\<lbrakk> set_invar s1; get_from_set P s1 = Some x\<rbrakk> \<Longrightarrow> P x"
                   "\<lbrakk> set_invar s1; \<And> x. x \<in> to_set s1 \<Longrightarrow> P x = Q x\<rbrakk> 
                     \<Longrightarrow> get_from_set P s1 = get_from_set Q s1"                   
    assumes set_filter:   "\<lbrakk> set_invar s1 \<rbrakk> \<Longrightarrow> to_set(filter P s1) = to_set s1 - {x. x \<in> to_set s1 \<and> \<not> P x}"
                          "\<lbrakk> set_invar s1; \<And> x. x \<in> to_set s1 \<Longrightarrow> P x =  Q x \<rbrakk> 
                           \<Longrightarrow> filter P s1 = filter Q s1"
   assumes invar_filter: "\<lbrakk> set_invar s1\<rbrakk> \<Longrightarrow> set_invar(filter P s1)"
 assumes are_all: "\<lbrakk> set_invar S\<rbrakk> \<Longrightarrow> are_all P S \<longleftrightarrow> (\<forall> x \<in> to_set S. P x)"
begin
lemma set_get':"\<lbrakk> set_invar s1; s1= s2; \<And> x. x \<in> to_set s1 \<Longrightarrow> P x = Q x\<rbrakk> 
                     \<Longrightarrow> get_from_set P s1 = get_from_set Q s2"   
  using set_get by blast
end

context cost_flow_network
begin

definition "consist conv_to_rdg = ((\<forall> x y. \<exists> e. ((conv_to_rdg (x,y) = F e \<and> make_pair e = (x,y)) \<or>
                                     conv_to_rdg (x,y) = B e \<and> make_pair e = (y,x))) \<and>
                             (\<forall> x y e. x \<noteq> y \<longrightarrow> (conv_to_rdg (x,y) = F e \<longleftrightarrow>
                                     conv_to_rdg (y,x) = B e)))" for conv_to_rdg

lemma consistencyE:
  assumes "consist to_rdg" 
          "(\<And> x y.  \<exists> e. ((to_rdg (x,y) = F e \<and> make_pair e = (x,y)) \<or>
                                     to_rdg (x,y) = B e \<and> make_pair e = (y,x)) ) \<Longrightarrow>
                (\<And> x y e.  x \<noteq> y \<Longrightarrow> (to_rdg (x,y) = B e) = (to_rdg (y, x) = F e)) \<Longrightarrow> P"
        shows P
  using assms by(auto simp add:  consist_def )

lemma consist_conv_inj:"consist conv \<Longrightarrow> conv a = conv b \<Longrightarrow> a = b"
  unfolding consist_def
  apply(rule Redge.induct[of _ "conv a"])
  apply(all \<open>rule Redge.induct[ of _ "conv b"]\<close>)
  apply(all \<open>cases a\<close>, all \<open>cases b\<close>)
  using Redge.inject Redge.distinct
  by (metis swap_simp)+

end

locale alg = cost_flow_spec  where fst=fst for fst::"'edge_type \<Rightarrow> 'a"+ 
  fixes
   edge_map_update:: "'a \<Rightarrow> 'edge_vset \<Rightarrow> 'edges \<Rightarrow> 'edges" and
     vset_empty :: "'vset"  ("\<emptyset>\<^sub>N") and vset_delete :: "'a \<Rightarrow> 'vset \<Rightarrow> 'vset" and
     vset_insert and vset_inv and isin 
begin
end

locale Map' =
fixes update :: "'a \<Rightarrow> 'b \<Rightarrow> 'm \<Rightarrow> 'm"
fixes lookup :: "'m \<Rightarrow> 'a \<Rightarrow> 'b option"
fixes invar :: "'m \<Rightarrow> bool"
assumes
map_update: "invar m \<Longrightarrow> lookup(update a b m) = (lookup m)(a := Some b)"
and invar_update: "invar m \<Longrightarrow> invar(update a b m)"

lemmas (in Map) map_specs' =
  map_empty map_update map_delete invar_empty invar_update invar_delete

locale Adj_Map_Specs2 = 
 adjmap: Map' 
 where update = update and invar = adjmap_inv +


 vset: Set_Choose
 where empty = vset_empty and delete = vset_delete and insert = vset_insert and invar = vset_inv
      and isin = isin

 for update :: "'a \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap" and adjmap_inv :: "'adjmap \<Rightarrow> bool"  and

     vset_empty :: "'vset"  ("\<emptyset>\<^sub>N") and vset_delete :: "'a \<Rightarrow> 'vset \<Rightarrow> 'vset" and
     vset_insert and vset_inv and isin
begin
notation vset_empty ("\<emptyset>\<^sub>N")
notation empty ("\<emptyset>\<^sub>G")

abbreviation isin' (infixl "\<in>\<^sub>G" 50) where "isin' G v \<equiv> isin v G" 
abbreviation not_isin' (infixl "\<notin>\<^sub>G" 50) where "not_isin' G v \<equiv> \<not> isin' G v"

definition neighbourhood::"'adjmap \<Rightarrow> 'a \<Rightarrow> 'vset" where
  "neighbourhood G v = (case (lookup G v) of Some vset \<Rightarrow> vset | _ \<Rightarrow> vset_empty)"

notation "neighbourhood" ("\<N>\<^sub>G _ _" 100)

definition digraph_abs ("[_]\<^sub>g") where "digraph_abs G = {(u,v). v \<in>\<^sub>G (\<N>\<^sub>G G u)}" 

definition "to_set_of_adjacency E =  { (u, v) | u v. isin (the (lookup E u)) v }"

definition "to_graph Forest = { {u, v} | u v. isin (the (lookup Forest u)) v 
                                            \<or> isin (the (lookup Forest u)) v}"

end

locale algo_spec = alg where fst=fst +  Set3 +
 Adj_Map_Specs2 where  update =  "edge_map_update::'a \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'd"
for fst::"'edge_type \<Rightarrow> 'a" +
  fixes
           \<b>::"'a \<Rightarrow> real" and
           to_pair::"'a set \<Rightarrow> 'a \<times> 'a" and
           \<epsilon>::real
    and \<E>_impl::'b 
    and empty_forest::"'d"
    and N::nat
fixes default_conv_to_rdg::"'a \<times> 'a \<Rightarrow> 'edge_type Redge"
begin

end

locale algo =  cost_flow_network where fst = fst +
 algo_spec where fst=fst and edge_map_update = "edge_map_update::'a \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'd"+  Set3 +
 Adj_Map_Specs2 where  update =  "edge_map_update::'a \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'd"
for fst::"'edge_type \<Rightarrow> 'a" and edge_map_update +
   assumes 
         infinite_u:  "\<And> e. \<u> e = PInfty"
       and
         to_pair_axioms: "\<And> u v vs. u \<noteq> v  \<Longrightarrow> {u, v} = vs 
                                     \<Longrightarrow> to_pair vs = (u,v) \<or> to_pair vs = (v,u)"
       and \<epsilon>_axiom: "0 < \<epsilon>" "\<epsilon> \<le> 1 / 2" "\<epsilon> \<le> 1/ card \<V>" "\<epsilon> < 1/2"
     and conservative_weights: "\<nexists> C. closed_w (make_pair ` \<E>) (map make_pair C) \<and> (set C \<subseteq> \<E>) \<and> foldr (\<lambda> e acc. acc + \<c> e) C 0 < 0"
  and \<E>_impl_meaning: "to_set \<E>_impl = \<E>"
                      "set_invar \<E>_impl"   and 
      empty_forest_axioms:   "\<And> v. lookup empty_forest v = Some vset_empty"
                             (* "\<And> v. lookup empty_forest v = None"*)
                             "adjmap_inv empty_forest"
 and default_conv_to_rdg: "consist default_conv_to_rdg" 
and N_def: "N = card \<V>"
begin 

(*definition "to_graph Forest = { {u, v} | u v. (u, v) \<in> digraph_abs Forest}"*)

find_theorems lookup

definition "validF state = graph_invar (to_graph (\<FF>_imp state))"

lemma N_gtr_0: "N > 0"
  using cardV_0
  by (simp add: N_def )

definition "invar_aux1 state = (to_set (actives state) \<subseteq> \<E>)"

lemma invar_aux1I: "to_set (actives state) \<subseteq> \<E> \<Longrightarrow> invar_aux1 state"
  unfolding invar_aux1_def by auto

lemma invar_aux1E: "invar_aux1 state \<Longrightarrow> (to_set (actives state) \<subseteq> \<E> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding invar_aux1_def by auto

abbreviation "\<F> state \<equiv>  oedge ` (to_rdgs to_pair (conv_to_rdg state) (to_graph (\<FF>_imp state)))"

definition "invar_aux2 state = ( to_rdgs to_pair (conv_to_rdg state) (to_graph (\<FF>_imp state)) \<subseteq> \<EE>)"

lemma invar_aux2I: "to_rdgs to_pair (conv_to_rdg state) (to_graph (\<FF>_imp state)) \<subseteq> \<EE> \<Longrightarrow> invar_aux2 state"
  unfolding invar_aux2_def by auto

lemma invar_aux2E: "invar_aux2 state \<Longrightarrow>
 (to_rdgs to_pair (conv_to_rdg state) (to_graph (\<FF>_imp state)) \<subseteq> \<EE>\<Longrightarrow> P) \<Longrightarrow> P"
  unfolding invar_aux2_def by auto

definition "invar_aux3 state =( \<F> state \<subseteq> \<E>)"

lemma invar_aux3I: "\<F> state \<subseteq> \<E>\<Longrightarrow> invar_aux3 state"
  unfolding invar_aux3_def by auto

lemma invar_aux3E: "invar_aux3 state \<Longrightarrow> (\<F> state \<subseteq> \<E> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding invar_aux3_def by auto

definition "invar_aux4 state =( \<F> state \<inter> to_set (actives state) = {})"

lemma invar_aux4I: "\<F> state \<inter> to_set (actives state) = {} \<Longrightarrow> invar_aux4 state"
  unfolding invar_aux4_def by auto

lemma invar_aux4E: "invar_aux4 state \<Longrightarrow> (\<F> state \<inter> to_set (actives state) = {} \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding invar_aux4_def by auto

definition "invar_aux5 state = finite (to_graph (\<FF>_imp state))"

lemma invar_aux5I: "finite (to_graph (\<FF>_imp state)) \<Longrightarrow> invar_aux5 state"
  unfolding invar_aux5_def by auto

lemma invar_aux5E: "invar_aux5 state \<Longrightarrow> (finite (to_graph (\<FF>_imp state)) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding invar_aux5_def by auto

definition "invar_aux6 state = consist (conv_to_rdg state)"

thm invar_aux6_def[simplified consist_def]

lemma invar_aux6I: "(\<And> x y. \<exists>e. conv_to_rdg state (x, y) = F e \<and> make_pair e = (x, y) \<or>
           conv_to_rdg state (x, y) = B e \<and> make_pair e = (y, x))  \<Longrightarrow>
        (\<And> x y e. x \<noteq> y  \<Longrightarrow>  
(conv_to_rdg state (x, y) = F e) = (conv_to_rdg state (y, x) = B e)) \<Longrightarrow> invar_aux6 state"
  unfolding invar_aux6_def consist_def by simp

lemma invar_aux6E: "invar_aux6 state \<Longrightarrow> to_rdg = conv_to_rdg state \<Longrightarrow>(
                                         (\<And> x y. \<exists> e. (to_rdg (x,y) = F e \<and> make_pair e = (x,y) \<or>
                                     to_rdg (x,y) = B e  \<and> make_pair e = (y,x)))  \<Longrightarrow>
                             (\<And> x y e. x \<noteq> y \<Longrightarrow> (to_rdg (x,y) = F e \<longleftrightarrow>
                                     to_rdg (y,x) = B e)) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding invar_aux6_def consist_def by simp

definition "invar_aux7 state = (\<forall> u v. reachable (to_graph (\<FF>_imp state)) u v \<longrightarrow>
                                       (representative state) u =
                                       (representative state) v)"

lemma invar_aux7I: "(\<And>u v. reachable (to_graph (\<FF>_imp state)) u v \<longrightarrow>
                                       (representative state) u =
                                       (representative state) v) \<Longrightarrow> invar_aux7 state"
  unfolding invar_aux7_def by simp

lemma invar_aux7E: "invar_aux7 state \<Longrightarrow> ((\<And>u v. reachable (to_graph (\<FF>_imp state)) u v \<longrightarrow>
                                       (representative state) u =
                                       (representative state) v) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding invar_aux7_def by simp

definition "invar_aux8 state = (\<forall> v. reachable (to_graph (\<FF>_imp state)) v ((representative state) v) \<or> 
                                                           v = (representative state) v)"

lemma invar_aux8I: "(\<And> v. reachable (to_graph (\<FF>_imp state)) v ((representative state) v) \<or> 
                                                           v = (representative state) v)
                    \<Longrightarrow> invar_aux8 state"
  unfolding invar_aux8_def by auto

lemma invar_aux8E: "invar_aux8 state \<Longrightarrow> ((\<And> v. reachable (to_graph (\<FF>_imp state)) v ((representative state) v) \<or> 
                                                           v = (representative state) v)
                                         \<Longrightarrow> P)
                    \<Longrightarrow>P"
  unfolding invar_aux8_def by auto

definition "invar_aux9 state = (\<forall> v \<in> \<V>. representative state v \<in> \<V>)"

lemma invar_aux9I: "(\<And>v. v \<in> \<V> \<Longrightarrow> representative state v \<in> \<V>) \<Longrightarrow> invar_aux9 state"
  unfolding invar_aux9_def by auto

lemma invar_aux9E: "invar_aux9 state \<Longrightarrow>
                      ((\<And>v. v \<in> \<V> \<Longrightarrow> representative state v \<in> \<V> ) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding invar_aux9_def by auto

definition "invar_aux10 state = (\<forall> v \<in> \<V>. connected_component (to_graph (\<FF>_imp state)) v \<subseteq> \<V>)"

lemma invar_aux10I: "(\<And>v. v \<in> \<V> \<Longrightarrow> connected_component (to_graph (\<FF>_imp state)) v \<subseteq> \<V>) \<Longrightarrow> invar_aux10 state"
  unfolding invar_aux10_def by auto

lemma invar_aux10E: "invar_aux10 state \<Longrightarrow>
                      ((\<And>v. v \<in> \<V> \<Longrightarrow>  connected_component (to_graph (\<FF>_imp state)) v \<subseteq> \<V>) ==> P) \<Longrightarrow> P"
  unfolding invar_aux10_def by auto

definition "invar_aux11 state =
               (\<forall> e \<in> to_set (actives state). connected_component (to_graph (\<FF>_imp state)) (fst e) \<noteq>
                                     connected_component (to_graph (\<FF>_imp state)) (snd e))"

lemma invar_aux11I: "(\<And> e. e \<in> to_set (actives state) \<Longrightarrow> connected_component (to_graph (\<FF>_imp state)) (fst e) \<noteq>
                                     connected_component (to_graph (\<FF>_imp state)) (snd e)) \<Longrightarrow>
                      invar_aux11 state"
  unfolding invar_aux11_def by simp

lemma invar_aux11E: "invar_aux11 state \<Longrightarrow>
                     ((\<And> e. e \<in> to_set (actives state) \<Longrightarrow> connected_component (to_graph (\<FF>_imp state)) (fst e) \<noteq>
                                     connected_component (to_graph (\<FF>_imp state)) (snd e)) \<Longrightarrow> P) \<Longrightarrow>
                      P"
  unfolding invar_aux11_def 
  by blast


definition "invar_aux12 state = (\<forall> v \<in> \<V>. (balance state v \<noteq> 0 \<longrightarrow> representative state v = v))"

lemma invar_aux12E:"invar_aux12 state 
\<Longrightarrow>((\<And> v.  v \<in> \<V> \<Longrightarrow> balance state v \<noteq> 0 \<Longrightarrow> representative state v = v) \<Longrightarrow> P) \<Longrightarrow>P"
  unfolding invar_aux12_def by simp

lemma invar_aux12I:
"(\<And> v.  v \<in> \<V> \<Longrightarrow> balance state v \<noteq> 0 \<Longrightarrow> representative state v = v) \<Longrightarrow> invar_aux12 state"
  unfolding invar_aux12_def by simp

definition "invar_aux13 state = 
               (\<forall>  e \<in> \<E> - to_set (actives state). connected_component (to_graph (\<FF>_imp state)) (fst e) =
                                          connected_component (to_graph (\<FF>_imp state)) (snd e))"

lemma invar_aux13I: "(\<And> e. e \<in> \<E> - to_set (actives state) \<Longrightarrow> connected_component (to_graph (\<FF>_imp state)) (fst e) =
                                     connected_component (to_graph (\<FF>_imp state)) (snd e)) \<Longrightarrow>
                      invar_aux13 state"
  unfolding invar_aux13_def by simp

lemma invar_aux13E: "invar_aux13 state \<Longrightarrow>
                     ((\<And> e. e \<in> \<E> - to_set (actives state) \<Longrightarrow> connected_component (to_graph (\<FF>_imp state)) (fst e) =
                                     connected_component (to_graph (\<FF>_imp state)) (snd e)) \<Longrightarrow> P) \<Longrightarrow>
                      P"
  unfolding invar_aux13_def by simp

definition "invar_aux14 state = (validF state)"

lemma invar_aux14E: "invar_aux14 state \<Longrightarrow> (validF state \<Longrightarrow> P) \<Longrightarrow> P"
  using invar_aux14_def by auto

definition "invar_aux15 state =( Vs (to_graph (\<FF>_imp state)) \<subseteq> \<V>)"

lemma invar_aux15E: "invar_aux15 state \<Longrightarrow> (Vs (to_graph (\<FF>_imp state)) \<subseteq> \<V>\<Longrightarrow> P) \<Longrightarrow> P"
  using invar_aux15_def by auto

definition "invar_aux16 state = (\<forall> x \<in> \<V>. comp_card state x = 
                       card (connected_component (to_graph (\<FF>_imp state)) x))"

lemma invar_aux16E: "invar_aux16 state \<Longrightarrow> ((\<And> x. x \<in> \<V> ==> comp_card state x = 
                       card (connected_component (to_graph (\<FF>_imp state)) x)) \<Longrightarrow> P) \<Longrightarrow> P"
  using invar_aux16_def by auto

definition "invar_aux17 state = set_invar (actives state)"

lemma invar_aux17E: "invar_aux17 state \<Longrightarrow> (set_invar (actives state) \<Longrightarrow> P) \<Longrightarrow> P"
  using invar_aux17_def by auto

definition "invar_aux18 state = adjmap_inv (\<FF>_imp state)"

lemma invar_aux18E: "invar_aux18 state \<Longrightarrow> (adjmap_inv (\<FF>_imp state) \<Longrightarrow> P) \<Longrightarrow> P"
  using invar_aux18_def by auto

definition "invar_aux19 state = (\<forall> v. lookup (\<FF>_imp state) v \<noteq> None \<and> vset_inv (the (lookup (\<FF>_imp state) v)))"

lemma invar_aux19E: "invar_aux19 state \<Longrightarrow> ((\<And>v. lookup (\<FF>_imp state) v \<noteq> None) \<Longrightarrow>
                                             (\<And> v. vset_inv (the (lookup (\<FF>_imp state) v))) \<Longrightarrow> P) \<Longrightarrow> P"
  using invar_aux19_def by auto

definition "invar_aux20 state = (\<forall> u v. isin (the (lookup (\<FF>_imp state) u)) v \<longleftrightarrow> {u, v} \<in> \<FF> state)"

lemma invar_aux20E: "invar_aux20 state \<Longrightarrow>
 ((\<And> u v. isin (the (lookup (\<FF>_imp state) u)) v \<longleftrightarrow> {u, v} \<in> \<FF> state) \<Longrightarrow> P) \<Longrightarrow> P"
  using invar_aux20_def by auto
                                             
definition "invar_aux21 state = (\<FF> state = to_graph (\<FF>_imp state))"

lemma invar_aux21E: "invar_aux21 state \<Longrightarrow> (\<FF> state = to_graph (\<FF>_imp state) \<Longrightarrow> P) \<Longrightarrow> P"
  using invar_aux21_def by auto

definition "invar_aux22 state = (\<forall> e. not_blocked state e \<longleftrightarrow> e \<in> \<F> state \<union> to_set (actives state))"

lemma invar_aux22E: "invar_aux22 state \<Longrightarrow> 
                         ((\<And> e. not_blocked state e \<longleftrightarrow> e \<in> \<F> state \<union> to_set (actives state)) \<Longrightarrow> P) \<Longrightarrow> P"
  using invar_aux22_def by auto

definition "fit_together ff ff_imp =
            ((\<forall> v. lookup ff_imp v \<noteq> None \<and> vset_inv (the (lookup ff_imp v)))\<and>
            (\<forall> u v. isin (the (lookup ff_imp u)) v \<longleftrightarrow> {u, v} \<in> ff))"

definition "aux_invar state =(  invar_aux1 state
                              \<and> invar_aux2 state \<and> invar_aux3 state \<and> invar_aux4 state
                              \<and> invar_aux6 state \<and> invar_aux8 state \<and>
                              invar_aux7 state \<and> invar_aux9 state \<and> invar_aux5 state
                              \<and> invar_aux10 state \<and> invar_aux11 state \<and> invar_aux12 state \<and>
                              invar_aux13 state \<and> invar_aux14 state \<and> invar_aux15 state \<and> invar_aux16 state
                              \<and> invar_aux17 state \<and> invar_aux18 state \<and> invar_aux19 state \<and> invar_aux20 state
                              \<and> invar_aux21 state \<and> invar_aux22 state)"

lemma aux_invarI: "invar_aux1 state \<Longrightarrow> invar_aux2 state \<Longrightarrow> invar_aux3 state 
                  \<Longrightarrow> invar_aux4 state \<Longrightarrow> invar_aux6 state \<Longrightarrow> invar_aux8 state \<Longrightarrow> 
                   invar_aux7 state \<Longrightarrow> invar_aux9 state \<Longrightarrow> invar_aux5 state\<Longrightarrow> invar_aux10 state
                     \<Longrightarrow> invar_aux11 state \<Longrightarrow> invar_aux12 state \<Longrightarrow> invar_aux13 state \<Longrightarrow>  invar_aux14 state
                  \<Longrightarrow>invar_aux15 state\<Longrightarrow> invar_aux16 state\<Longrightarrow> invar_aux17 state \<Longrightarrow>
                     invar_aux18 state \<Longrightarrow> invar_aux19 state \<Longrightarrow> invar_aux20 state \<Longrightarrow> invar_aux21 state 
                  \<Longrightarrow> invar_aux22 state \<Longrightarrow> 
 aux_invar state"
  unfolding aux_invar_def by simp

lemma aux_invarE: "aux_invar state \<Longrightarrow>
                  ( invar_aux1 state \<Longrightarrow> invar_aux2 state \<Longrightarrow> invar_aux3 state 
                  \<Longrightarrow> invar_aux4 state \<Longrightarrow> invar_aux6 state \<Longrightarrow> invar_aux8 state \<Longrightarrow>
                    invar_aux7 state \<Longrightarrow> invar_aux9 state \<Longrightarrow> invar_aux5 state \<Longrightarrow> invar_aux10 state
                  \<Longrightarrow> invar_aux11 state \<Longrightarrow> invar_aux12 state \<Longrightarrow> invar_aux13 state \<Longrightarrow>  invar_aux14 state
                 \<Longrightarrow> invar_aux15 state \<Longrightarrow> invar_aux16 state \<Longrightarrow> invar_aux17 state \<Longrightarrow>
                    invar_aux18 state \<Longrightarrow> invar_aux19 state \<Longrightarrow> invar_aux20 state \<Longrightarrow>
                   invar_aux21 state \<Longrightarrow> invar_aux22 state \<Longrightarrow> P)
                  \<Longrightarrow> P"
  unfolding aux_invar_def by simp

lemma "aux_invar state \<Longrightarrow> e \<notin> \<E> \<Longrightarrow> \<not> not_blocked state e"
  unfolding  aux_invar_def invar_aux22_def invar_aux1_def invar_aux3_def by blast

named_theorems from_aux_invar

lemma invar_aux1_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux1 state"
  unfolding aux_invar_def by simp
lemma invar_aux2_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux2 state"
  unfolding aux_invar_def by simp
lemma invar_aux3_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux3 state"
  unfolding aux_invar_def by simp
lemma invar_aux4_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux4 state"
  unfolding aux_invar_def by simp
lemma invar_aux5_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux5 state"
  unfolding aux_invar_def by simp
lemma invar_aux6_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux6 state"
  unfolding aux_invar_def by simp
lemma invar_aux7_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux7 state"
  unfolding aux_invar_def by simp
lemma invar_aux8_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux8 state"
  unfolding aux_invar_def by simp
lemma invar_aux9_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux9 state"
  unfolding aux_invar_def by simp
lemma invar_aux10_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux10 state"
  unfolding aux_invar_def by simp
lemma invar_aux11_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux11 state"
  unfolding aux_invar_def by simp
lemma invar_aux12_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux12 state"
  unfolding aux_invar_def by simp
lemma invar_aux13_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux13 state"
  unfolding aux_invar_def by simp
lemma invar_aux14_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux14 state"
  unfolding aux_invar_def by simp
lemma invar_aux15_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux15 state"
  unfolding aux_invar_def by simp
lemma invar_aux16_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux16 state"
  unfolding aux_invar_def by simp
lemma invar_aux17_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux17 state"
  unfolding aux_invar_def by simp
lemma invar_aux18_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux18 state"
  unfolding aux_invar_def by simp
lemma invar_aux19_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux19 state"
  unfolding aux_invar_def by simp
lemma invar_aux20_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux20 state"
  unfolding aux_invar_def by simp
lemma invar_aux21_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux21 state"
  unfolding aux_invar_def by simp
lemma invar_aux22_from_aux_invar[from_aux_invar]: 
"aux_invar state \<Longrightarrow> invar_aux22 state"
  unfolding aux_invar_def by simp

lemmas from_aux_invar'= from_aux_invar[simplified invar_aux1_def invar_aux2_def invar_aux3_def 
                        invar_aux4_def invar_aux5_def invar_aux6_def invar_aux7_def invar_aux8_def
                        invar_aux9_def invar_aux10_def invar_aux11_def invar_aux12_def invar_aux13_def
                        invar_aux14_def invar_aux15_def invar_aux16_def invar_aux17_def invar_aux18_def
                        invar_aux19_def invar_aux20_def invar_aux21_def invar_aux22_def]

lemmas invar_auxE = invar_aux1E invar_aux2E invar_aux3E invar_aux4E invar_aux5E
                    invar_aux6E invar_aux7E invar_aux8E invar_aux9E invar_aux10E
                    invar_aux11E invar_aux12E invar_aux13E invar_aux14E invar_aux15E
                    invar_aux16E invar_aux17E invar_aux18E invar_aux19E invar_aux20E
                    invar_aux21E invar_aux22E


lemmas invar_aux1I' = invar_aux1E[OF _  invar_aux1I]
lemmas invar_aux2I' = invar_aux2E[OF _  invar_aux2I]
lemmas invar_aux3I' = invar_aux3E[OF _  invar_aux3I]
lemmas invar_aux4I' = invar_aux4E[OF _  invar_aux4I]
lemmas invar_aux5I' = invar_aux5E[OF _  invar_aux5I]
lemmas invar_aux6I' = invar_aux6E[OF _  _ invar_aux6I]
lemmas invar_aux7I' = invar_aux7E[OF _  invar_aux7I]
lemmas invar_aux8I' = invar_aux8E[OF _  invar_aux8I]
lemmas invar_aux9I' = invar_aux9E[OF _  invar_aux9I]
lemmas invar_aux10I' = invar_aux10E[OF _  invar_aux10I]
lemmas invar_aux11I' = invar_aux11E[OF _  invar_aux11I]
lemmas invar_aux12I' = invar_aux12E[OF _  invar_aux12I]
lemmas invar_aux13I' = invar_aux13E[OF _  invar_aux13I]

lemma invar_aux14I: "validF state \<Longrightarrow> invar_aux14 state"
  unfolding invar_aux14_def by simp

lemmas invar_aux14I' = invar_aux14E[OF _  invar_aux14I]

lemma invar_aux15I: "Vs (to_graph (\<FF>_imp state)) \<subseteq> \<V> \<Longrightarrow> invar_aux15 state"
  unfolding invar_aux15_def by simp

lemmas invar_aux15I' = invar_aux15E[OF _  invar_aux15I]

lemma invar_aux16I: "(\<And> x. x \<in> \<V> \<Longrightarrow>
 card (connected_component (to_graph (\<FF>_imp state)) x) = comp_card state x ) \<Longrightarrow>
                    invar_aux16 state"
  unfolding invar_aux16_def by simp

lemmas invar_aux16I' = invar_aux16E[OF _  invar_aux16I]

lemma invar_aux17I: "(set_invar (actives state)) \<Longrightarrow>
                    invar_aux17 state"
  unfolding invar_aux17_def by simp

lemmas invar_aux17I' = invar_aux17E[OF _  invar_aux17I]

lemma invar_aux18I: "adjmap_inv (\<FF>_imp state) \<Longrightarrow>
                    invar_aux18 state"
  unfolding invar_aux18_def by simp

lemmas invar_aux18I' = invar_aux18E[OF _  invar_aux18I]

lemma invar_aux19I: "(\<And> v. lookup (\<FF>_imp state) v \<noteq> None) \<Longrightarrow>
                     (\<And> v.  vset_inv (the (lookup (\<FF>_imp state) v))) \<Longrightarrow>
                    invar_aux19 state"
  unfolding invar_aux19_def by simp

lemmas invar_aux19I' = invar_aux19E[OF _  invar_aux19I]

lemma invar_aux20I: "(\<And> u v. (isin (the (lookup (\<FF>_imp state) u)) v) = ({u, v} \<in> \<FF> state)) \<Longrightarrow>
                    invar_aux20 state"
  unfolding invar_aux20_def by simp

lemma invar_aux21I: "\<FF> state = to_graph (\<FF>_imp state) \<Longrightarrow> invar_aux21 state"
  unfolding invar_aux21_def by simp

lemma invar_aux22I: "(\<And> e. not_blocked state e \<longleftrightarrow> e \<in> \<F> state \<union> to_set (actives state)) \<Longrightarrow>
                        invar_aux22 state"
  unfolding invar_aux22_def by simp

lemmas invar_aux20I' = invar_aux20E[OF _  invar_aux20I]
lemmas invar_aux21I' = invar_aux21E[OF _  invar_aux21I]
lemmas invar_aux22I' = invar_aux22E[OF _  invar_aux22I]

lemmas aux_invar_pres = aux_invarE[OF _  aux_invarI[OF invar_aux1I' invar_aux2I' invar_aux3I' invar_aux4I' invar_aux6I' 
                                   invar_aux8I' invar_aux7I' invar_aux9I' invar_aux5I' invar_aux10I'
                                   invar_aux11I' invar_aux12I' invar_aux13I' invar_aux14I'
                                   invar_aux15I' invar_aux16I' invar_aux17I' invar_aux18I'
                                   invar_aux19I' invar_aux20I' invar_aux21I' invar_aux22I']]


lemma aux_invar_gamma: "aux_invar state \<Longrightarrow> aux_invar (state\<lparr> current_\<gamma> := \<gamma>\<rparr>)"
  unfolding aux_invar_def validF_def invar_aux1_def invar_aux2_def invar_aux3_def invar_aux4_def
               invar_aux6_def invar_aux8_def invar_aux7_def invar_aux10_def invar_aux11_def 
               invar_aux5_def invar_aux9_def invar_aux12_def invar_aux13_def  invar_aux14_def 
               invar_aux15_def invar_aux16_def invar_aux17_def invar_aux18_def invar_aux19_def
               invar_aux20_def invar_aux21_def invar_aux22_def consist_def by auto

lemma invar_aux6_conv_to_rdg_fstv: "invar_aux6 state \<Longrightarrow> fstv ((conv_to_rdg state) (x,y) ) = x"
  unfolding invar_aux6_def consist_def 
  by (metis fst_conv fstv.simps(1) fstv.simps(2) make_pair' snd_conv)

lemma invar_aux6_conv_to_rdg_sndv: "invar_aux6 state \<Longrightarrow> sndv ((conv_to_rdg state) (x,y) ) = y"
  unfolding invar_aux6_def consist_def 
  by (metis fst_conv make_pair' snd_conv sndv.simps(1) sndv.simps(2))

lemma consist_fstv: "consist to_rdg \<Longrightarrow> fstv (to_rdg (u, v)) = u"
  unfolding consist_def 
  by (metis fst_conv fstv.simps(1) fstv.simps(2) make_pair' snd_conv)

lemma consist_sndv: "consist to_rdg \<Longrightarrow> sndv (to_rdg (u, v)) = v"
  unfolding consist_def 
  by (metis fst_conv make_pair' snd_conv sndv.simps(1) sndv.simps(2)) 

lemma consistE: "consist to_rdg \<Longrightarrow> x \<noteq> y \<Longrightarrow>
                (\<And> e. to_rdg (x,y) = F e \<Longrightarrow> to_rdg (y, x) = B e \<Longrightarrow> make_pair e = (x,y) \<Longrightarrow> P x y) \<Longrightarrow>
                (\<And> e. to_rdg (x,y) = B e \<Longrightarrow> to_rdg (y, x) = F e  \<Longrightarrow> make_pair e = (y,x) \<Longrightarrow>P x y)
                \<Longrightarrow> P x y"
  unfolding consist_def 
  by metis

lemma consist_oedge_set: "consist to_rdg \<Longrightarrow> u \<noteq> v \<Longrightarrow>
     to_vertex_pair ` {to_rdg  (to_pair {u, v}), to_rdg (prod.swap (to_pair {u, v}))}
     \<subseteq> {(u, v), (v, u)}"
  by(rule disjE[OF local.to_pair_axioms(1)], auto elim: consistE)


lemma consist_oedge_set_cong: "consist to_rdg \<Longrightarrow> u \<noteq> v \<Longrightarrow>  ss = {u, v} \<Longrightarrow>
     to_vertex_pair ` {to_rdg  (to_pair ss), to_rdg (prod.swap (to_pair ss))}
     \<subseteq> {(u, v), (v, u)}"
  using consist_oedge_set by simp

lemma consist_edge_in_vertex_in:
  assumes "consist (conv_to_rdg state)" "u \<noteq> v" "{u, v} \<in> (to_graph (\<FF>_imp state))"
  shows     "u \<in> dVs (to_vertex_pair ` (to_rdgs to_pair (conv_to_rdg state) (to_graph (\<FF>_imp state))))"
proof-
  have 1:" {conv_to_rdg state (to_pair {u, v}), conv_to_rdg state (prod.swap (to_pair {u, v}))}
        \<subseteq> (to_rdgs to_pair (conv_to_rdg state) (to_graph (\<FF>_imp state)))"
    using assms unfolding consist_def  to_rdgs_def dVs_def by auto
 have 2:"to_vertex_pair ` {conv_to_rdg state (to_pair {u, v}), conv_to_rdg state (prod.swap (to_pair {u, v}))}
        \<subseteq> {(u, v), (v, u)}"
    using assms(1-2)  consist_oedge_set by simp
  show ?thesis
    apply(rule piar_setE[OF 2])
    using image_mono[OF 1, of to_vertex_pair] dVsI'
          by  auto
qed

lemma consist_update_reduce[simp]:"consist to_rdg \<Longrightarrow> 
fst e \<noteq> snd e \<Longrightarrow> to_rdgs to_pair (\<lambda>d. if d = make_pair e then F e else if prod.swap d = make_pair e then B e else to_rdg d) 
           {{fst e, snd e}} =
       {F e, B e}"
    unfolding invar_aux6_def consist_def to_rdgs_def 
    apply(subst UN_insert, subst if_P[where P="\<exists>u v. u \<noteq> v \<and> {u, v} = {fst e, snd e}"])
    apply fast
    apply(cases rule: disjE[OF to_pair_axioms(1)[of "fst e" "snd e" "{fst e, snd e}"]], simp)
    using swap_simp[of "fst e" "snd e"] make_pair
    by force+

fun to_redge_path where
"to_redge_path to_rdg [u,v] = [to_rdg (u,v)]"|
"to_redge_path to_rdg (u#v#vs) = (to_rdg (u,v) # to_redge_path to_rdg (v#vs))"|
"to_redge_path  _ _ = []"

lemma proper_path_some_redges:"length l \<ge> 2 \<Longrightarrow> (to_redge_path to_rdg' l) \<noteq> []" for l to_rdg' Q
        apply(induction to_rdg' l rule: to_redge_path.induct)
         apply (metis list.simps(3) to_redge_path.simps(1))
        apply (metis list.distinct(1) to_redge_path.simps(2))
      by auto

lemma perpath_to_redgepath:
"invar_aux6 state \<Longrightarrow> walk_betw FFF u p v \<Longrightarrow> length p \<ge> 2 \<Longrightarrow>
           prepath (to_redge_path (conv_to_rdg state) p)"
  unfolding walk_betw_def
proof(induction p arbitrary: u)
  case (Cons a p u)
  then show ?case
        using path_pref[of "FFF " "[a]" p] 
        by (cases rule: list_cases4[of p], auto intro: prepath_intros 
              simp add: invar_aux6_conv_to_rdg_fstv invar_aux6_conv_to_rdg_sndv)
qed simp

lemma concretize_walk:"validF state  \<Longrightarrow>walk_betw (to_graph (\<FF>_imp state)) u p v \<Longrightarrow> length p \<ge> 2 \<Longrightarrow>
       set (to_redge_path (conv_to_rdg state) p) \<subseteq> to_rdgs to_pair (conv_to_rdg state) (to_graph (\<FF>_imp state))"
  unfolding walk_betw_def
proof(induction "(conv_to_rdg state)" p arbitrary: u rule: to_redge_path.induct)
  case (1 u va ua)
  hence "{u, va} \<in> (to_graph (\<FF>_imp state))" "u \<noteq> va"
    using 1 path_2[of "(to_graph (\<FF>_imp state))" u va Nil] 
    unfolding validF_def by auto
  moreover have "set (to_redge_path (conv_to_rdg state) [u, va])  =
        {(conv_to_rdg state) (u, va)}" by simp
  moreover have " {(conv_to_rdg state) (u, va)} \<subseteq> 
                  {conv_to_rdg state (to_pair {u, va}),
                       conv_to_rdg state (prod.swap (to_pair {u, va}))}"
     using to_pair_axioms[of u va "{u, va}"]  calculation(2) by fastforce
  ultimately show ?case unfolding to_rdgs_def 
    by auto
next
  case (2 u v w vs ua)
  hence "{u, v} \<in> (to_graph (\<FF>_imp state))" "u \<noteq> v"
    using 2 path_2[of "\<FF> state" u v Nil] 
    unfolding validF_def by auto
  moreover have "set (to_redge_path (conv_to_rdg state) [u, v])  =
        {(conv_to_rdg state) (u, v)}" by simp
  moreover have " {(conv_to_rdg state) (u, v)} \<subseteq> 
                  {conv_to_rdg state (to_pair {u, v}),
                       conv_to_rdg state (prod.swap (to_pair {u, v}))}"
    using to_pair_axioms[of u v "{u, v}"]  calculation(2) by fastforce
  moreover have "    set (to_redge_path (conv_to_rdg state) (v # w # vs))
               \<subseteq> to_rdgs to_pair (conv_to_rdg state) (to_graph (\<FF>_imp state))"
    using  2 walk_betw_def 
    by (auto intro: 2(1)[of v])
  ultimately show ?case 
    unfolding to_rdgs_def by auto
qed simp+
  
lemma consist_to_rdg_costs_negation:
 "consist to_rdg \<Longrightarrow> u \<noteq> v \<Longrightarrow> \<cc> (to_rdg (u, v)) = -  \<cc> (to_rdg (prod.swap (u, v)))"
  unfolding consist_def 
  by (smt (verit, del_insts) \<cc>.simps(1) \<cc>.simps(2) swap_simp)

lemma foldr_last_append: "\<cc> d + foldr (\<lambda>e. (+) (\<cc> e)) xs 0 = 
                           foldr (\<lambda>e. (+) (\<cc> e)) (xs@[d]) 0"
  by(induction xs) auto

lemma to_redge_path_last_append: "length xs \<ge> 2 \<Longrightarrow> last xs = v \<Longrightarrow>
                               to_redge_path to_rdg xs @[to_rdg (v, u)] =
                               to_redge_path to_rdg (xs@[u])"
  by(induction to_rdg xs rule: to_redge_path.induct) auto

lemma to_redge_path_costs:"consist to_rdg \<Longrightarrow> length p \<ge> 2 \<Longrightarrow> distinct p \<Longrightarrow>
                          foldr (\<lambda> e acc. \<cc> e + acc) (to_redge_path to_rdg p) 0 
                      = - foldr (\<lambda> e acc. \<cc> e + acc) (to_redge_path to_rdg (rev p)) 0"
proof(induction to_rdg p rule: to_redge_path.induct)
  case (1 to_rdg u v)
  moreover hence "u \<noteq> v" by simp
  ultimately show ?case 
    using consist_to_rdg_costs_negation[of to_rdg u v] by simp 
next
  case (2 to_rdg u v w vs)
  hence  u_neq_v:"u \<noteq> v" by simp
  have " foldr (\<lambda>e. (+) (\<cc> e)) (to_redge_path to_rdg (u#v # w # vs)) 0 = 
         ( \<cc> (to_rdg (u, v))) + foldr (\<lambda>e. (+) (\<cc> e)) (to_redge_path to_rdg ( v#w # vs)) 0" 
    by simp
  also have "... =  - ( \<cc> (to_rdg (v, u))) - 
                     foldr (\<lambda>e. (+) (\<cc> e)) (to_redge_path to_rdg ( rev (v#w # vs))) 0"
    using consist_to_rdg_costs_negation[of to_rdg  u v ] 2 u_neq_v  by simp
  also have "\<dots> = - ( (\<cc> (to_rdg (v, u))) +
                     foldr (\<lambda>e. (+) (\<cc> e)) (to_redge_path to_rdg ( rev (v#w # vs))) 0)"
    by simp
  also have "... = - (foldr (\<lambda>e. (+) (\<cc> e)) 
                       ((to_redge_path to_rdg ( (rev (v#w # vs))))@[(to_rdg (v, u))]) 0)"
    using foldr_last_append by simp
  also have "\<dots> =  - (foldr (\<lambda>e. (+) (\<cc> e)) 
                       ((to_redge_path to_rdg ( (rev (v#w # vs)) @[u]))) 0)"     
  using to_redge_path_last_append[of "rev (v # w # vs)" v to_rdg u] by simp
  finally show ?case by simp
qed simp+

lemma to_rdg_hd: "consist to_rdg \<Longrightarrow> length p \<ge> 2 \<Longrightarrow> fstv (hd (to_redge_path to_rdg p)) =  hd p"
  apply(induction to_rdg p rule: to_redge_path.induct)
  using consist_fstv
  by auto

lemma to_rdg_last_cons: " (last (to_rdg (u, v) # to_redge_path to_rdg (v # va # vb))) =
                          (last (to_redge_path to_rdg (v # va # vb)))"
  by (smt (verit, best) last_ConsR list.discI list.inject to_redge_path.elims)

lemma to_rdg_last: "consist to_rdg \<Longrightarrow> length p \<ge> 2 \<Longrightarrow>
                        sndv (last (to_redge_path to_rdg p)) =  last p"
  apply(induction to_rdg p rule: to_redge_path.induct)
  subgoal for to_rdg u v
  using consist_sndv by simp
  subgoal for to_rdg u v va vb
    using to_rdg_last_cons[of to_rdg u v va vb] by auto
  by auto

lemma to_rdg_not_in: "consist to_rdg  \<Longrightarrow> length p \<ge> 2 \<Longrightarrow>
       distinct (u # p) \<Longrightarrow> to_rdg (u, v) \<notin> set (to_redge_path to_rdg p)"
proof(induction to_rdg p rule: to_redge_path.induct)
  case (1 to_rdg ua va)
  then show ?case 
    using  consist_conv_inj[of to_rdg]  list.set(1)  to_redge_path.simps(1)[of to_rdg ua va]
    by (force simp add: consist_def)
next
  case (2 to_rdg ua va vaa vb)
  then show ?case
    using  consist_conv_inj[of to_rdg]  to_redge_path.simps(2)
    by(force simp add: consist_def)
qed auto

lemma to_rdg_distinct: "consist to_rdg  \<Longrightarrow> distinct p \<Longrightarrow>
                         distinct (to_redge_path to_rdg p)"
  apply(induction to_rdg p rule: to_redge_path.induct)
  using to_rdg_not_in[of _ "(_ # _ # _)" ] by force+

lemma consist_oedge:"consist to_rdg' \<Longrightarrow> v \<noteq> v' \<Longrightarrow> {oedge (to_rdg' (v, v'))} =
    oedge `(if \<exists>u va. u \<noteq> va \<and> {u, va} = {v, v'}
        then {to_rdg' (to_pair {v, v'}), to_rdg' (prod.swap (to_pair {v, v'}))} else {})"
  by (smt (z3) algo.to_pair_axioms(1) algo_axioms consist_def insert_commute oedge.simps(1)
            oedge.simps(2) oedge_both_redges_image swap_simp)

lemma in_oedge_F_to_in_undirected_F:
  fixes F 
  assumes "d \<in> oedge ` to_rdgs to_pair to_rdg F" 
          "consist to_rdg"
  shows "{fst d, snd d} \<in> F" 
  using assms to_pair_axioms unfolding to_rdgs_def consist_def image_def
  by auto (smt (verit, best) assms(2) consist_sndv empty_iff insert_commute insert_iff oedge.elims sndv.simps(1) sndv.simps(2) swap_simp)

lemma  oedge_of_to_redgepath_subset:
"distinct Q \<Longrightarrow> consist to_rdg' \<Longrightarrow>oedge ` set (to_redge_path to_rdg' Q) = 
          oedge ` to_rdgs to_pair to_rdg' (set (edges_of_path Q))" 
proof(induction Q rule: edges_of_path.induct)
  case (3 v v' l)
  then show ?case 
  proof(cases l)
    case Nil
    then show ?thesis 
          using 3 consist_oedge [of to_rdg' v v'] 
          unfolding to_rdgs_def  consist_def  by auto
   next
     case (Cons a list)
     show ?thesis
     proof(rule trans[of _ "oedge ` set (to_redge_path to_rdg' (v # v' # a#list))"],
           goal_cases)
       case 2
       show ?case
       using Cons 3 
          apply(subst to_redge_path.simps(2), subst set_simps(2))
          apply(subst edges_of_path.simps, subst set_simps(2), subst image_insert)
          unfolding to_rdgs_def 
          by (subst UN_insert, subst insert_is_Un, 
              auto    intro: set_union_eq_cong 
                    simp add: to_rdgs_def[of to_pair to_rdg' "set (edges_of_path (v' # l))"]
                           consist_oedge [of to_rdg' v v'])
      qed (simp add: Cons 3)
      qed
    qed (auto simp add: to_rdgs_def)

lemma to_redgepath_subset:"distinct Q \<Longrightarrow> consist to_rdg' \<Longrightarrow>
         set (to_redge_path to_rdg' Q) \<subseteq>
           to_rdgs to_pair to_rdg' (set (edges_of_path Q))" 
proof(induction Q rule: edges_of_path.induct)
  case (3 v v' l)
  then show ?case 
  proof(cases l)
    case Nil
    then show ?thesis 
         using  3 to_redge_path.simps(1) local.to_pair_axioms(1)
         unfolding to_rdgs_def consist_def
         by fastforce
     next
       case (Cons a list)
       show ?thesis
       proof(rule subset_trans[of _ "set (to_redge_path to_rdg' (v # v' # a#list))"],
             goal_cases)
         case 2
         show ?case 
          apply(subst to_redge_path.simps(2), subst set_simps(2), 
                subst edges_of_path.simps, subst set_simps(2))
          unfolding to_rdgs_def
          apply(subst UN_insert)
          using 3 Cons
          unfolding sym[OF to_rdgs_def[of to_pair to_rdg' "set (edges_of_path (v' # l))"]]
          using local.to_pair_axioms(1) by fastforce+
     qed (simp add: 3 Cons)
   qed
 qed (auto simp add: to_rdgs_def)

lemma to_redgepath_rev_subset:"distinct Q \<Longrightarrow> consist to_rdg' \<Longrightarrow>
         set (to_redge_path to_rdg' (rev Q)) \<subseteq> to_rdgs to_pair to_rdg' (set (edges_of_path Q))"
proof(induction Q rule: edges_of_path.induct)
  case (3 v v' l)
  then show ?case 
  proof(cases l)
    case Nil
    then show ?thesis 
          using 3 local.to_pair_axioms(1)
          unfolding to_rdgs_def consist_def by fastforce
      next
        case (Cons  a list)
        show ?thesis
        proof(rule subset_trans[of _ "set (to_redge_path to_rdg' (rev(v' # a#list) @ [v]))"],
              goal_cases)
          case 2
          show ?case 
          apply(subst edges_of_path.simps, subst set_simps(2))
          apply(subst sym[OF to_redge_path_last_append], simp, simp, subst set_append,
                subst Un_commute)
          unfolding to_rdgs_def
          apply(subst UN_insert)
          unfolding sym[OF to_rdgs_def[of to_pair to_rdg' "set (edges_of_path (v' # l))"]]  
          using local.to_pair_axioms(1) Cons 3 by fastforce
      qed(auto simp add: 3 Cons)
    qed
   qed (auto simp add: to_rdgs_def)

lemma to_redge_path_simp: "to_redge_path to (u#v#ws) = to (u, v) # to_redge_path to (v#ws)"
      for u v ws to 
  by(cases ws) auto

lemma oedge_of_to_redge_path_rev:"distinct Q \<Longrightarrow> consist to_rdg' 
\<Longrightarrow> oedge ` set (to_redge_path to_rdg' (rev Q)) = oedge ` set (to_redge_path to_rdg' Q)" for Q to_rdg'

proof(rule sym, induction "length Q" arbitrary: Q)
  case (Suc n Q)
  show ?case 
  proof(cases rule: edges_of_path.cases[of Q])
    case (3 u v Q')
    show ?thesis
    proof(rule trans[of _ "oedge ` (insert (to_rdg' (u, v)) (set (to_redge_path to_rdg' (v#Q'))))"],
          goal_cases)
        case 2
          show ?case
          proof(rule trans[of _ "{oedge (to_rdg' (u, v))} \<union>
                               oedge ` set (to_redge_path to_rdg' (v#Q'))"], fast, goal_cases)
            case 1
            then show ?case 
            proof(subst Un_commute, rule trans[of _ "oedge ` set (to_redge_path to_rdg' (rev Q'@[v])) \<union> 
                  {oedge (to_rdg' (v, u))}"], goal_cases)
              case 1
              then show ?case 
                apply(rule set_union_eq_cong, subst sym[OF rev.simps(2)], rule Suc(1))
                using Suc 3 
                by (auto elim: consistE[of to_rdg'])
          next
            case 2
            then show ?case
            using 3 Suc
          proof(cases Q')
            case (Cons a list)
            then show ?thesis      
            apply(subst sym[OF  image_sigleton[of oedge]], subst sym[OF image_Un])
            apply(subst sym[OF set_singleton_list[of "to_rdg' (v, u)"]], subst sym[OF set_append])
            using 2 3 Suc to_redge_path_last_append[of "rev Q' @ [v]"  v to_rdg'] 
            by auto
       qed simp
      qed
     qed
    qed (auto simp add: 3 to_redge_path_simp[of to_rdg' u v Q'] 
                        set_simps(2)[of " to_rdg' (u, v)" ])
  qed (auto simp add: Suc)
qed simp

lemma to_pair_elim: "a \<noteq> b \<Longrightarrow> ((a, b) = to_pair {a,b}  \<Longrightarrow> P (a, b)) \<Longrightarrow>
                                  ((b, a) = to_pair {a,b}  \<Longrightarrow> P (b, a)) \<Longrightarrow> P (to_pair {a, b})"
      for a b P 
  using to_pair_axioms by metis

lemma dVs_single_edge:"dVs {(u, v)} = {u, v}" 
  unfolding dVs_def by simp

lemma conv_to_rdg_coincide:
      "(\<And> x y. {x, y} \<in> set (edges_of_path Q) \<Longrightarrow> to_rdg (x, y) = to_rdg' (x, y)) \<Longrightarrow>
       to_redge_path to_rdg Q = to_redge_path to_rdg' Q"
  apply(induction Q, simp)
  subgoal for a Q
    apply(cases Q, simp)
    subgoal for aa list
      by(cases list, auto) 
    done
  done

lemma consist_dVs_path:"consist to_rdg' \<Longrightarrow> distinct Q \<Longrightarrow> 
          dVs (to_vertex_pair ` to_rdgs to_pair to_rdg' (set (edges_of_path Q))) \<subseteq> set Q" for to_rdg' Q
proof(induction Q rule: edges_of_path.induct)
  case (3 v v' l)
  then show ?case 
      apply(subst edges_of_path.simps, subst set_simps(2))
      unfolding to_rdgs_def 
      apply(subst Union_image_insert)
          unfolding sym[OF to_rdgs_def[of to_pair to_rdg' "set (edges_of_path (v' # l))"]]
      apply(subst image_Un, subst dVs_union_distr)
        proof(rule Un_least, goal_cases)
          case 1
          then show ?case  
            apply(subst if_P, fastforce) 
            apply(rule to_pair_elim, simp)
            subgoal
             apply(rule consistE[of to_rdg'], simp, simp)             
              using oedge_both_redges_image[of , simplified swap_simp] 
                    dVs_single_edge[of v v']  dVs_single_edge[of v' v] 
                    oedge_both_redges_image[of , simplified swap_simp] 
              make_pair consist_oedge_set[of to_rdg' v v'] dVs_empty 
              unfolding dVs_def image_def 
               by auto (all \<open>insert "3.prems"(1)\<close>, blast+)
            subgoal
             apply(rule consistE[of to_rdg'], simp, simp)             
              using oedge_both_redges_image[of _, simplified swap_simp] 
                                  dVs_single_edge[of v v'] oedge_both_redges_image[of _, simplified swap_simp] 
                                  dVs_single_edge[of v' v] 
              make_pair consist_oedge_set[of to_rdg' v v'] dVs_empty 
              unfolding dVs_def image_def 
               by auto (all \<open>insert "3.prems"(1)\<close>, blast+)
            done
        qed auto
      qed (auto simp add: to_rdgs_def)

lemma to_rdgs_update_not_in[simp]:
      "consist to_rdg \<Longrightarrow> to_rdgs to_pair (\<lambda> d. if d = make_pair e then F e
                                             else if prod.swap d = make_pair e then B e 
                                             else to_rdg d) (X - {{fst e, snd e}})
                          = to_rdgs to_pair to_rdg (X - {{fst e, snd e}})"
  apply(rule sym)
  unfolding to_rdgs_def consist_def
  by (smt (verit, ccfv_threshold) DiffD2 Inf.INF_cong Pair_inject insert_commute insert_iff make_pair' swap_simp to_pair_axioms)

lemma edge_not_in_edges_in_path:
"a \<notin> set p \<or> b \<notin> set p \<Longrightarrow> {a, b} \<notin> set (edges_of_path p)"
  by(induction p rule: edges_of_path.induct) auto

lemma 
reachable_after_insert:
"\<not> reachable E u v \<Longrightarrow> reachable (insert {a, b} E) u v \<Longrightarrow> \<not> (reachable E u a) \<Longrightarrow>
               u \<noteq> v \<Longrightarrow>   reachable E u b \<or> u = a \<or> u = b"
proof-
  assume asm:"\<not> reachable E u v"
         "reachable (insert {a, b} E) u v" "\<not> reachable E u a" "u \<noteq> v "
  then obtain p where p_prop:"walk_betw (insert {a, b} E) u p v" 
    using asm  unfolding reachable_def by auto
  hence "\<not> walk_betw E u p v" 
    by (meson \<open>\<not> reachable E u v\<close> reachableI)
  have "set (edges_of_path p) \<subseteq> (insert {a, b} E)"
    using path_edges_subset p_prop unfolding walk_betw_def by auto
  have length_p: "length p \<ge> 2"
  proof(rule ccontr)
    assume " \<not> 2 \<le> length p"
    hence "length p \<le> 1" by simp
    hence "length p = 1"
      using   p_prop  unfolding walk_betw_def 
      by (cases p) auto
    hence "hd p = last p" 
      by (cases p) auto
    thus False
      using p_prop asm unfolding walk_betw_def by simp
  qed
  have 12:"path (set (edges_of_path p)) p"
    by(auto intro: path_edges_of_path_refl simp add: length_p)
  have "\<not> set (edges_of_path p) \<subseteq> E"
  proof
    assume "set (edges_of_path p) \<subseteq> E"
    hence "path E p" 
      using "12" path_subset by blast
    hence "reachable E u v"
      unfolding reachable_def walk_betw_def 
      by (metis p_prop walk_betw_def)
    thus False using asm by simp
  qed
  hence "{a, b} \<in> set (edges_of_path p)" 
    using \<open>set (edges_of_path p) \<subseteq> insert {a, b} E\<close> by blast
  hence "a \<in> set p" "b \<in> set p"
    by (meson insertCI v_in_edge_in_path_gen)+
  then obtain p' x q where p'xq:"p = p'@[x]@q" "x = a \<or> x = b" "a \<notin> set p'" "b \<notin> set p'"
    using extract_first_x[of a p "\<lambda> x. x = a \<or> x = b"]
    by blast
  have 13:"{a, b} \<notin> set (edges_of_path (p'@[x]))" 
    apply(cases "a=b")
    using p'xq  edges_of_path.simps(2)[of x] edges_of_path.simps(3)[of "last p'" x Nil]
             edges_of_path_append_3[of p' "[x]"]   v_in_edge_in_path[of a b "p'@[x]"]
             v_in_edge_in_path[of a b "p'"] edge_not_in_edges_in_path[of a "p'@[x]" b] 
    by(cases p', force, auto)
  show "reachable E u b \<or> u = a\<or> u = b"
  proof(cases "x = b")
    case True
    have "path (insert {a,b} E) (p' @ [x])" 
      using p'xq(1) p_prop walk_between_nonempty_pathD(1)[of "insert {a,b} E" u "p'@[x]" x]
             walk_pref[of "insert {a,b} E" u p' x q v] by simp
    show ?thesis 
    proof(cases "u = b")
      case False
      hence p'_not_empt:"p' \<noteq> []" 
        using True  p'xq(1) p_prop  walk_betw_def[of "insert {a,b} E" u p v] by force
    have "path E (p' @ [x])" 
      apply(rule path_subset, rule path_edges_of_path_refl)
      using  p'_not_empt  "13" \<open>path (insert {a, b} E) (p' @ [x])\<close> path_edges_subset 
      by (auto  simp add: Suc_leI)
    hence "walk_betw E u (p'@[x]) b"
      unfolding walk_betw_def
      using True p'_not_empt p'xq(1) p_prop
                walk_between_nonempty_pathD(3)[of "insert {a,b} E" u p v] by simp
    then show ?thesis unfolding reachable_def by auto
  qed simp
next
  case False
  note false = this
  show ?thesis
  proof(cases "x = a")
    case True
    have "path (insert {a,b} E) (p' @ [x])"
      using p'xq(1) p_prop walk_between_nonempty_pathD(1)[of "insert {a,b} E" u "p'@[x]" x]
            walk_pref[of "insert {a,b} E" u p' x q v] by simp
    show ?thesis 
    proof(cases "u = a")
      case False
      hence p'_not_empt:"p' \<noteq> []" 
        using True  p'xq(1) p_prop  walk_betw_def[of "insert {a,b} E" u p v] by force
     have "path E (p' @ [x])" 
      apply(rule path_subset, rule path_edges_of_path_refl)
      using  p'_not_empt  "13" \<open>path (insert {a, b} E) (p' @ [x])\<close> path_edges_subset 
      by (auto  simp add: Suc_leI)
    hence "walk_betw E u (p'@[x]) a"
      unfolding walk_betw_def 
      using True  p'_not_empt p'xq(1) p_prop 
             walk_between_nonempty_pathD(3)[of "insert {a,b} E" u p v] by simp
    then show ?thesis using asm unfolding reachable_def by auto
  qed simp
next 
  case False
  then show ?thesis using false p'xq by simp
qed
qed
qed

lemma  undirected_of_directed_of_undirected_idem: 
       "graph_invar A \<Longrightarrow> {{v1, v2} |v1 v2. (v1,v2) \<in> {(u, v). {u, v} \<in> A}} = A" for A
      by fast

lemma vwalk_bet_reflexive_cong: "w \<in> dVs E \<Longrightarrow> a = w \<Longrightarrow> b = w \<Longrightarrow> vwalk_bet E a [w] b" for w a b E
  by (meson vwalk_bet_reflexive)

lemma  edges_are_vwalk_bet_cong: "(v,w)\<in> E \<Longrightarrow> a = v \<Longrightarrow> b = w \<Longrightarrow> vwalk_bet E a [v, w] b" for v E w a b
  using edges_are_vwalk_bet by auto

definition "goodF F = ((\<forall> v . \<exists> vset . (lookup F v = Some vset))
                       \<and> (\<forall> v vset. lookup F v = Some vset \<longrightarrow> vset_inv vset))" for F

lemma  from_undirected_edge_to_directed: 
  assumes "fit_together ff ff_imp"  "goodF ff_imp"
  shows "{a, b} \<in> ff \<Longrightarrow> (a, b) \<in> digraph_abs ff_imp" 
  using assms unfolding fit_together_def goodF_def  digraph_abs_def
   neighbourhood_def
  by (metis case_prod_conv mem_Collect_eq option.sel option.simps(5))

lemma  from_directed_edge_to_undirected: 
  assumes "fit_together ff ff_imp"  "goodF ff_imp"
  shows "(a, b) \<in> digraph_abs ff_imp \<Longrightarrow> {a, b} \<in> ff " 
  using assms unfolding fit_together_def goodF_def digraph_abs_def neighbourhood_def
  by (metis case_prod_conv mem_Collect_eq option.sel option.simps(5))

lemma from_undirected_walk_to_directed_walk:
  assumes "fit_together ff ff_imp" "goodF ff_imp" "graph_invar ff"
  shows "walk_betw ff i q j \<Longrightarrow> vwalk_bet (digraph_abs ff_imp) i q j"
proof(induction q arbitrary: i)
  case (Cons a q)
  note IH = this
  show ?case 
  proof(cases q)
    case Nil
    show ?thesis 
          apply(insert Nil, simp, rule vwalk_bet_reflexive_cong)
      using assms(1)  Cons  undirected_of_directed_of_undirected_idem[OF assms(3)]  walk_in_Vs [of ff i "[a]" j]
            walk_between_nonempty_pathD(3)[OF Cons.prems]  walk_between_nonempty_pathD(4)[OF Cons.prems] 
      by(auto simp add: case_simp(1) Vs_def  dVs_def fit_together_def invar_aux14_def validF_def goodF_def
                digraph_abs_def neighbourhood_def) 
  next
    case (Cons aa list)
    then show ?thesis
    apply(subst sym[OF hd_Cons_tl[of q]], simp)
    apply(subst sym[OF single_in_append], subst (2) sym[OF single_in_append])
    apply(subst sym[OF append.assoc],subst append_two)
      using path_2 walk_between_nonempty_pathD(1)[OF  IH(2)[simplified Cons]]
            path_2 walk_between_nonempty_pathD(3)[OF  IH(2)[simplified Cons]] 
          IH(2)[simplified Cons] iffD1[OF walk_betw_cons, OF IH(2)[simplified Cons]] 
          IH(1)[of "hd q"] 
      by (fastforce intro!: vwalk_bet_transitive[of _ _ _ "hd q"] 
          edges_are_vwalk_bet_cong from_undirected_edge_to_directed[OF assms(1) assms(2)])
  qed
qed(auto simp add: walk_betw_def)

lemma from_reachable_to_dircted_walk:
  assumes "fit_together ff ff_imp" "goodF ff_imp" "graph_invar ff"
  shows "reachable ff a b \<Longrightarrow> \<exists> q. vwalk_bet (digraph_abs ff_imp) a q b"
  using assms
    by (meson reachable_def from_undirected_walk_to_directed_walk)

lemma walk_reflexive_cong: "w \<in> Vs E \<Longrightarrow> a = w \<Longrightarrow> b = w \<Longrightarrow>  walk_betw E a [w] b"
  using walk_reflexive by simp

lemma edges_are_walks_cong:
  "{v, w} \<in> E \<Longrightarrow> a = v \<Longrightarrow> w = b \<Longrightarrow> walk_betw E a [v, w] b"
  using edges_are_walks by fast

lemma from_directed_walk_to_undirected_walk:
  assumes "fit_together ff ff_imp" "goodF ff_imp" "graph_invar ff"
  shows "vwalk_bet (digraph_abs ff_imp) i q j \<Longrightarrow> walk_betw ff i q j"
proof(induction q arbitrary: i)
  case (Cons a q)
  note IH = this
  show ?case 
  proof(cases q)
    case Nil
    thus ?thesis 
      using assms(1)  Cons(2)  undirected_of_directed_of_undirected_idem[OF assms(3)]  
            vwalk_bet_in_dVs[of "(digraph_abs ff_imp)" i "[a]" j]
            vwalk_bet_nonempty_vwalk(3)[OF Cons.prems]  last_of_vwalk_bet[OF Cons.prems]
      by(auto intro: walk_reflexive_cong simp add: case_simp(1) Vs_def  dVs_def fit_together_def invar_aux14_def validF_def validF_def goodF_def digraph_abs_def
                neighbourhood_def) 
  next
    case (Cons aa list)
    then show ?thesis
    apply(subst sym[OF hd_Cons_tl[of q]], simp)
    apply(subst sym[OF single_in_append], subst (2) sym[OF single_in_append])
    apply(subst sym[OF append.assoc],subst append_two)
      using  IH(2)[simplified vwalk_bet_def ] vwalk_2  hd_of_vwalk_bet' [OF IH(2)]
              IH(2)[simplified hd_of_vwalk_bet'[OF IH(2)], simplified]
              vwalk_bet_cons[of _  a q j] IH(1)
      by (fastforce intro!: edges_are_walks_cong walk_transitive[of _ _ _ "hd q"] 
                      from_directed_edge_to_undirected[OF assms(1) assms(2)])
  qed
qed(fastforce simp add: vwalk_bet_def)

lemma from_directed_walk_to_reachable:
  assumes "fit_together ff ff_imp" "goodF ff_imp" "graph_invar ff"
  shows "\<exists> q. vwalk_bet (digraph_abs ff_imp) a q b \<Longrightarrow> reachable ff a b  "
  using assms
  by (meson from_directed_walk_to_undirected_walk reachableI)


definition "insert_undirected_edge u v forst = (let vsets_u = the (lookup forst u);
                                                    vsets_v = the (lookup forst v);
                                                    vset_u_new = vset_insert v vsets_u;
                                                    vset_v_new = vset_insert u vsets_v
                                                 in edge_map_update v vset_v_new (
                                                    edge_map_update u vset_u_new forst))"


lemma insert_abstraction[simp]:
  assumes "adjmap_inv ff " 
          "(\<And> x. vset_inv (the (lookup ff x)))"
        shows "to_graph (insert_undirected_edge u v ff) = insert {u, v} (to_graph ff)"
(*proof(rule, all \<open>rule\<close>, goal_cases)
  case (1 e) 
  then obtain x y where "e = {x, y}" "(x, y) \<in> digraph_abs (insert_undirected_edge u v ff)" 
    by(auto simp add: to_graph_def)
  hence a:"lookup (insert_undirected_edge u v ff) x \<noteq> None"
        and b: "isin (the (lookup (insert_undirected_edge u v ff) x)) y"
   by(auto simp add: digraph_abs_def neighbourhood_def
       option.split[where option = "lookup (insert_undirected_edge u v ff) x", 
       of "\<lambda> x. y \<in>\<^sub>G x"] vset.set.invar_empty vset.set.set_empty vset.set.set_isin)
  have "(x = u \<and> y = v) \<or> (y = u \<and> x= v) \<or>
        (x = u \<and> y \<noteq> v \<and> isin (the (lookup ff u)) y) \<or> (y = u \<and> x \<noteq> v \<and> isin (the (lookup ff u)) )"


 

  have "x = u \<or> x = v \<or> (x \<noteq> u \<and> x \<noteq>  v \<and> (lookup ff x) \<noteq> None)"
    using a unfolding insert_undirected_edge_def Let_def
    by(subst (asm) adjmap.map_update)(auto intro: adjmap.invar_update[OF assms(1)] simp add: adjmap.map_update[OF assms(1)])
  moreover have "y = u \<or> y = v \<or> (y \<noteq> u \<and> y \<noteq> v \<and> isin (the (lookup ff x)) y)"
    using b unfolding insert_undirected_edge_def Let_def
    apply(subst (asm) adjmap.map_update)
     apply(rule adjmap.invar_update[OF assms(1)])
    apply(subst (asm) adjmap.map_update[OF assms(1)])
   by( rule case_split[of "x= u"] , auto intro: case_split[of "x = v"]
      simp add: assms(2) vset.set.invar_insert vset.set.set_insert vset.set.set_isin)
  ultimately show ?case 
    unfolding to_graph_def neighbourhood_def digraph_abs_def 
    apply(auto split: option.split simp add:  \<open>e = {x, y}\<close>)
    using  \<open>x = u \<or> x = v \<or> x \<noteq> u \<and> x \<noteq> v \<and> lookup ff x \<noteq> None\<close>
 adjmap.invar_update adjmap.map_update assms(1) b fun_upd_other 
insert_undirected_edge_def option.sel

next
  case (2 x)
  then show ?case sorry
qed*)
  unfolding to_graph_def insert_undirected_edge_def 
  apply(simp, rule, rule)

    apply(subst (asm) adjmap.map_update)
     apply(rule adjmap.invar_update[OF assms(1)])
    apply(subst (asm) adjmap.map_update[OF assms(1)])
    apply simp
    apply(subst (asm) if_distrib[of the], subst (asm) option.sel)
    apply(subst (asm) fun_upd_apply)
   apply(subst (asm) if_distrib[of the], subst (asm) option.sel)
    apply(subst vset.set.set_isin) (*prior without .set.*)
    using assms(2) apply simp
     apply(subst (asm) vset.set.set_isin)
    using assms(2) vset.set.invar_insert apply simp (*prior without invar*)
    apply(subst (asm) if_distrib[of "\<lambda> x. _ \<in> _ x"])
    apply(subst (asm) (2) if_distrib[of "\<lambda> x. _ \<in> _ x"])
    apply(subst (asm) vset.set.set_insert)
    using assms(2) vset.set.invar_insert apply simp
    apply(subst (asm) vset.set.set_insert)
    using assms(2) 
    apply simp 
    apply (metis Un_iff doubleton_eq_iff empty_iff insert_iff)
  
    using assms(2) vset.set.set_isin adjmap.map_update adjmap.invar_update assms(1) 
          vset.set.set_insert vset.set.invar_insert 
    by auto

lemma insert_adjacency_set[simp]:
  assumes "adjmap_inv ff " 
          "(\<And> x. vset_inv (the (lookup ff x)))"
        shows "to_set_of_adjacency (insert_undirected_edge u v ff) =
                    {(u, v), (v, u)} \<union> (to_set_of_adjacency ff)"
  unfolding to_set_of_adjacency_def insert_undirected_edge_def Let_def
    apply(subst  adjmap.map_update)
     apply(rule adjmap.invar_update[OF assms(1)])
    apply(subst  adjmap.map_update[OF assms(1)])
  apply rule
   apply rule apply simp
    apply(subst (asm) if_distrib[of the], subst (asm) option.sel)
    apply(subst (asm) fun_upd_apply)
   apply(subst (asm) if_distrib[of the], subst (asm) option.sel)
    apply(subst (asm) if_distrib[of isin])
   apply(subst (asm) if_distrib[of isin])
   apply(subst (asm)  split_beta)
   apply(subst split_beta) 
   apply(subst (asm) if_distribR)
   apply(subst (asm) if_distribR)
   apply(subst (asm) vset.set.set_isin , simp add: assms(2) vset.set.invar_insert)+
  apply(subst vset.set.set_isin, simp add: assms(2)  vset.set.invar_insert)
  apply(subst (asm) vset.set.set_insert, simp add: assms(2)  vset.set.invar_insert)+
  apply (metis UnE equals0D insert_iff prod.exhaust_sel)
  using assms(2) adjmap.map_update adjmap.invar_update assms(1) vset.set.invar_insert 
        vset.set.set_insert vset.set.set_isin 
  by auto

lemma  vertex_path_to_redge_path_over_set_of_edges_subset:
      "set (edges_of_path p) \<subseteq> FF \<Longrightarrow> consist to_rdg \<Longrightarrow> distinct p 
       \<Longrightarrow> set (to_redge_path  to_rdg p ) \<subseteq> to_rdgs to_pair to_rdg FF"
  apply(induction p, simp)
  by (meson order.trans to_rdg_mono to_redgepath_subset)

lemma predicate_cong: "a = b \<Longrightarrow> c = d \<Longrightarrow> P a c \<Longrightarrow> P b d"
  by simp

lemma fit_together_pres:
"fit_together X Y \<Longrightarrow> adjmap_inv Y \<Longrightarrow> fit_together (insert {x, y} X)
     (insert_undirected_edge x y Y)" if "goodF Y"
  unfolding fit_together_def insert_undirected_edge_def Let_def 
  using adjmap.map_update adjmap.invar_update  vset.set.invar_insert that vset.set.invar_insert 
        vset.set.set_insert vset.set.set_isin
  by (auto simp add: doubleton_eq_iff goodF_def)

lemma Pair_graph_specs_from_aux_invar:
"aux_invar state \<Longrightarrow> goodF (\<FF>_imp state)"
  unfolding goodF_def  
            aux_invar_def invar_aux19_def invar_aux18_def
  by (metis option.exhaust option.sel)

lemma Pair_Graph_Specs_insert_undirected_edge_pres:
"goodF F \<Longrightarrow> goodF (insert_undirected_edge x y F)" if "adjmap_inv F" for F 
  unfolding goodF_def  insert_undirected_edge_def Let_def
  apply(subst adjmap.map_update, ((rule adjmap.invar_update,  simp add: that) | simp add: that))+
  by(auto intro: adjmap.invar_update vset.set.invar_insert)

lemma neighbourhood_pres:
      "(\<And>x. lookup F x \<noteq> None \<and> vset_inv (the (lookup F x ))) \<Longrightarrow> adjmap_inv F 
      \<Longrightarrow> (\<And>x. lookup (insert_undirected_edge y z F) x \<noteq> None \<and> 
                vset_inv (the (lookup (insert_undirected_edge y z F) x)))" for F
  unfolding insert_undirected_edge_def Let_def 
  apply rule
  by((subst adjmap.map_update, ((rule adjmap.invar_update,  simp) | simp))+; auto intro: vset.set.invar_insert)+

lemma adjmap_inv_pres_insert_undirected_edge:"adjmap_inv ff \<Longrightarrow> adjmap_inv (insert_undirected_edge a b ff)"
  unfolding insert_undirected_edge_def
  by(auto intro: adjmap.invar_update)

lemma vset_inv_pres_insert_undirected_edge:"adjmap_inv ff\<Longrightarrow> (\<And> x. vset_inv (the (lookup ff x))) \<Longrightarrow>
           vset_inv (the (lookup (insert_undirected_edge a b ff) x))"
  unfolding insert_undirected_edge_def 
  using adjmap.invar_update adjmap.map_update
  by (auto simp add: vset.set.invar_insert)

definition "invar_gamma state = (current_\<gamma> state > 0)"

definition "invar_non_zero_b state =( \<not> (\<forall>v\<in>\<V>. balance state v = 0))"

definition "invar_forest state =
                (\<forall> e \<in> oedge ` (to_rdgs to_pair (conv_to_rdg state) (to_graph (\<FF>_imp state))).
                               (current_flow state) e > 4 * N * (current_\<gamma> state))"

definition "invar_integral state = (\<forall> e \<in> to_set (actives state).
                               \<exists> n::nat. (current_flow state) e = n * (current_\<gamma> state))"

lemma invar_integralI: "(\<And> e. e \<in> to_set (actives state) \<Longrightarrow> \<exists> n::nat. (current_flow state) e = n * (current_\<gamma> state)) \<Longrightarrow>
                invar_integral state"
  unfolding invar_integral_def by simp

lemma invar_integralE: " invar_integral state \<Longrightarrow>
           ((\<And> e. e \<in> to_set (actives state) \<Longrightarrow> \<exists> n::nat. (current_flow state) e = n * (current_\<gamma> state)) \<Longrightarrow>
                P ) \<Longrightarrow> P"
  unfolding invar_integral_def by blast

definition "invar_isOptflow state = is_Opt (\<b> - balance state) (current_flow state)"

definition "\<Phi> state = (\<Sum> v \<in>  \<V>. \<lceil> \<bar> balance state v\<bar> / (current_\<gamma> state) - (1 - \<epsilon>)\<rceil>)"

definition "loopA_entry state = (\<forall> e \<in> oedge ` (to_rdgs to_pair (conv_to_rdg state)
                                       (to_graph (Algo_state.\<FF>_imp state))).
                                current_flow state e > 8*N*current_\<gamma> state)"

definition "loopB_entryF state = (\<forall> e \<in> oedge ` (to_rdgs to_pair (conv_to_rdg state) 
                                      (to_graph (Algo_state.\<FF>_imp state))).
                                current_flow state e > 6*N*current_\<gamma> state)"

definition "orlins_entry state = (\<forall> v \<in> \<V>. \<bar> balance state v \<bar> \<le> (1 - \<epsilon>) * current_\<gamma> state)"

definition "invarA_1 (thr::real) state = (\<forall> v \<in> \<V>. \<bar> balance state v \<bar> \<le> 
                                  thr * card (connected_component (to_graph (Algo_state.\<FF>_imp state)) v))"

definition "invarA_2 (thr1::real) (thr2::real) state = 
                   (\<forall> e \<in> oedge ` (to_rdgs to_pair (conv_to_rdg state) (to_graph (Algo_state.\<FF>_imp state))).
                               (current_flow state) e > thr1 - thr2 * 
                                card (connected_component (to_graph (Algo_state.\<FF>_imp state)) (fst e)))"

lemma Phi_nonneg: "invar_gamma state\<Longrightarrow> \<Phi> state \<ge> 0"
  unfolding \<Phi>_def invar_gamma_def
  apply(rule sum_nonneg) 
  by (smt (verit, ccfv_threshold) \<epsilon>_axiom(1) divide_nonneg_pos zero_le_ceiling)

lemma invar_isOpt_gamma_change:
"invar_isOptflow state \<Longrightarrow> invar_isOptflow (state \<lparr>current_\<gamma> :=gamma \<rparr>)"
  unfolding invar_isOptflow_def by simp

definition add_fst ("_ +++ _") where
"add_fst c ab = (c + prod.fst ab, prod.snd ab)"

lemma add_fst_snd_same: "prod.snd (c +++ ab) = prod.snd ab"
  unfolding add_fst_def by simp

lemma "aux_invar state \<Longrightarrow> aux_invar (state \<lparr> current_\<gamma>:= new\<rparr>)"
  using aux_invar_gamma by blast

lemma forest_paths_are_optimum:
  assumes "invar_isOptflow state"
          "\<forall> e \<in> \<F> state. current_flow state e > 0"
          "walk_betw (\<FF> state) x' Q y'"
          "aux_invar state"
          "x' \<noteq> y'"
          "distinct Q"
    shows "is_min_path (current_flow state) x' y' (to_redge_path (conv_to_rdg state) Q)"
proof-
  have lengthQ: "2 \<le> length Q"
    by (meson assms(3) assms(5) walk_betw_length)
  have prepath:"prepath (to_redge_path (conv_to_rdg state) Q)"
    using assms(4) invar_aux6_from_aux_invar lengthQ
    by(auto intro: perpath_to_redgepath[OF _ assms(3), of state])
  have prepath_rev:"prepath (to_redge_path (conv_to_rdg state) (rev Q))"
    using assms(4) invar_aux6_from_aux_invar lengthQ walk_symmetric[OF assms(3)] perpath_to_redgepath 
    by fastforce
  have Q_in_F:"set (edges_of_path Q) \<subseteq> to_graph (\<FF>_imp state)"
    using path_edges_subset[OF walk_between_nonempty_pathD(1)[OF assms(3)]]
         from_aux_invar(20)[OF assms(4), simplified invar_aux20_def[simplified]]
    by (auto simp add: to_graph_def, metis subsetD v_in_edge_in_path_inj)
  have Q_in_F_rev:"set (edges_of_path (rev Q)) \<subseteq> to_graph (\<FF>_imp state)"
    using path_edges_subset[OF walk_between_nonempty_pathD(1)[OF assms(3)], simplified  edges_of_path_rev]
         from_aux_invar(20)[OF assms(4), simplified invar_aux20_def[simplified]]
    by(auto simp add: to_graph_def, metis edges_of_path_rev set_rev subsetD v_in_edge_in_path_inj)
  have F_subs_E:"\<F> state  \<subseteq> \<E>" 
    by (simp add: assms(4) from_aux_invar'(3))
  have oedge_in_F:"oedge ` (set (to_redge_path (conv_to_rdg state) Q)) \<subseteq> \<F> state" 
    apply(rule order.trans, rule image_mono[OF to_redgepath_subset[OF assms(6)]])
    using Q_in_F by (auto simp add: to_rdgs_def assms(4) from_aux_invar'(6))
  have oedge_in_F_rev:"oedge ` (set (to_redge_path (conv_to_rdg state) (rev Q))) \<subseteq> \<F> state" 
    apply(rule order.trans, rule image_mono[OF to_redgepath_subset[OF]])
    using Q_in_F_rev assms(6) by (auto simp add: to_rdgs_def assms(4) from_aux_invar'(6))
  have Rcap: "0 < Rcap (current_flow state) (set (to_redge_path (conv_to_rdg state) Q))"
    unfolding Rcap_def
    apply(subst linorder_class.Min_gr_iff, simp, simp, auto)
    subgoal for e
      using oedge_in_F assms(2)  infinite_u  oedge_in_F 
      by (cases e) auto
    done
  have Rcap_rev: "0 < Rcap (current_flow state) (set (to_redge_path (conv_to_rdg state) (rev Q)))"
    unfolding Rcap_def
    apply(subst linorder_class.Min_gr_iff, simp, simp, auto)
    subgoal for e
      using oedge_in_F_rev assms(2)  infinite_u  oedge_in_F 
      by (cases e) auto
    done
  have a1: "augpath (current_flow state) (to_redge_path (conv_to_rdg state) Q)"
    using Rcap prepath by (auto simp add: augpath_def )
  have a2: "set (to_redge_path (conv_to_rdg state) Q) \<subseteq> \<EE>"
    using assms(4) assms(6) from_aux_invar'(2) from_aux_invar'(6)
          vertex_path_to_redge_path_over_set_of_edges_subset[OF Q_in_F ] by fast
  have a3:"fstv (hd (to_redge_path (conv_to_rdg state) Q)) = x'"
    using   lengthQ to_rdg_hd[OF from_aux_invar'(6)[OF assms(4)]]
             walk_between_nonempty_pathD(3)[OF assms(3)] by simp
  have a4: " sndv (last (to_redge_path (conv_to_rdg state) Q)) = y'" 
    using   lengthQ to_rdg_last[OF from_aux_invar'(6)[OF assms(4)]]
             walk_between_nonempty_pathD(4)[OF assms(3)] by simp
  have a5: "distinct (to_redge_path (conv_to_rdg state) Q)"
    by (simp add: assms(4) assms(6) from_aux_invar'(6) to_rdg_distinct)
  have C_Q_rev_Q:"\<CC> (to_redge_path (conv_to_rdg state) Q) = - \<CC> (to_redge_path (conv_to_rdg state) (rev Q))"
    using to_redge_path_costs[of "(conv_to_rdg state)" Q, OF _ lengthQ assms(6)]
          to_rdg_distinct[of "(conv_to_rdg state)" Q, OF _ assms(6)]
          to_rdg_distinct[of "(conv_to_rdg state)""rev Q", OF _, 
                      simplified distinct_rev[of Q], OF _ assms(6)] distinct_sum2[of _ \<cc>] 
    by(simp add: \<CC>_def assms(4) from_aux_invar'(6))
 have b1: "augpath (current_flow state) (to_redge_path (conv_to_rdg state) (rev Q))"
   using Rcap_rev prepath_rev
   by (auto simp add: augpath_def )
  have b2: "set (to_redge_path (conv_to_rdg state) (rev Q)) \<subseteq> \<EE>"
    using assms(4) assms(6) from_aux_invar'(2) from_aux_invar'(6)
          vertex_path_to_redge_path_over_set_of_edges_subset[OF Q_in_F_rev ] by force
  have b3:"fstv (hd (to_redge_path (conv_to_rdg state) (rev Q))) = y'"
    using   lengthQ to_rdg_hd[OF from_aux_invar'(6)[OF assms(4)]]
             walk_between_nonempty_pathD(3)[OF walk_symmetric[OF assms(3)]] by simp
  have b4: " sndv (last (to_redge_path (conv_to_rdg state) (rev Q))) = x'" 
    using   lengthQ to_rdg_last[OF from_aux_invar'(6)[OF assms(4)]]
             walk_between_nonempty_pathD(4)[OF  walk_symmetric[OF assms(3)]] by simp
  have b5: "distinct (to_redge_path (conv_to_rdg state) (rev Q))"
    by (simp add: assms(4) assms(6) from_aux_invar'(6) to_rdg_distinct)
  have is_s_t_path_rev_Q: "is_s_t_path (current_flow state) y' x' (to_redge_path (conv_to_rdg state) (rev Q))"
    by (simp add: b1 b2 b3 b4 b5 is_s_t_path_def)
  have C_Q_rev_Q:"\<CC> (to_redge_path (conv_to_rdg state) Q) = - \<CC> (to_redge_path (conv_to_rdg state) (rev Q))"
    using to_redge_path_costs[of "(conv_to_rdg state)" Q, OF _ lengthQ assms(6)]
          to_rdg_distinct[of "(conv_to_rdg state)" Q, OF _ assms(6)]
          to_rdg_distinct[of "(conv_to_rdg state)""rev Q", OF _, 
                      simplified distinct_rev[of Q], OF _ assms(6)] distinct_sum2[of _ \<cc>] 
    by(simp add: \<CC>_def assms(4) from_aux_invar'(6))
  show ?thesis
        unfolding is_min_path_def
      proof(rule, goal_cases)
        case 1
        then show ?case 
        using a1 a2 a3 a4 a5 by(auto simp add: is_s_t_path_def)
      next
        case 2
        then show ?case 
        proof(rule, rule)
          fix P' 
          assume P'_asm: "is_s_t_path (current_flow state) x' y' P'"
          show "\<CC> (to_redge_path  (conv_to_rdg state) Q) \<le> \<CC> P'"
          proof(rule ccontr)
            assume lesser_cost_asm:"\<not> \<CC> (to_redge_path (conv_to_rdg state) Q) \<le> \<CC> P'"
            hence costs:"\<CC> (to_redge_path (conv_to_rdg state) (rev Q)) + \<CC> P' < 0" 
              using C_Q_rev_Q by fastforce
            define Q' where "Q' = to_redge_path (conv_to_rdg state) (rev Q)"
            define Qpp where "Qpp = map PP (to_redge_path (conv_to_rdg state) (rev Q))"
            define P'cc where "P'cc = map CC P'"
            have markers_removeQ: "to_redge_path (conv_to_rdg state) (rev Q) = map to_redge Qpp"
              unfolding Qpp_def sym[OF Q'_def]
              by(induction Q') auto
            have markers_removeP: "P' = map to_redge P'cc"
              unfolding P'cc_def
               by(induction P') auto
            have markers_remove: "to_redge_path (conv_to_rdg state) (rev Q) @ P' = map to_redge (Qpp @ P'cc)"
              unfolding Qpp_def sym[OF Q'_def]
              using markers_removeP 
              by (induction Q') auto
            have hpath: "hpath (Qpp @ P'cc)"
              using hpath_first_node[of P'cc] P'_asm markers_removeP hpath_last_node[of Qpp] 
                    is_s_t_path_rev_Q markers_removeQ augpath_to_hpath_CC[of "current_flow state"] 
                    augpath_to_hpath_PP[of "current_flow state"]
              unfolding is_s_t_path_def Qpp_def P'cc_def 
              by (auto intro: h_path_append)
            have distinct:"distinct (Qpp @ P'cc)"
               using is_s_t_path_rev_Q distinct_map[of ] P'_asm distinct_append
               unfolding Qpp_def P'cc_def is_s_t_path_def inj_on_def 
               by auto
             have setE:"List.set (to_redge_path (conv_to_rdg state) (rev Q) @ P') \<subseteq> \<EE>"
               using P'_asm is_s_t_path_rev_Q
               unfolding is_s_t_path_def by simp
             have fstvv_x':"fstvv (hd (Qpp @ P'cc)) = y'"
               using b5 is_s_t_path_rev_Q unfolding Qpp_def is_s_t_path_def augpath_def prepath_def
               by (simp add: list.map_sel(1))
             have sndvv_x':"sndvv (last (Qpp @ P'cc)) = y'"
               using P'_asm  unfolding P'cc_def is_s_t_path_def augpath_def prepath_def
               by (simp add: last_map)
            have "\<exists>PP CCC.
                  Ball (List.set CCC) precycle \<and>
                  prepath PP \<and>
                  distinct PP \<and>
                  sum cc (List.set (Qpp@P'cc)) = \<CC> PP + foldr (\<lambda>D. (+) (\<CC> D)) CCC 0 \<and>
                  List.set ((to_redge_path (conv_to_rdg state) (rev Q))@P') = List.set PP \<union> \<Union> {List.set D |D. D \<in> List.set CCC} \<and> 
                  fstv (hd PP) = y' \<and> sndv (last PP) = y'"
              using markers_remove  hpath  distinct  setE fstvv_x' sndvv_x' 
              by (fastforce intro!: distinct_hpath_to_distinct_augpath_and_augcycles)
            then obtain P'' CCC where all_props:" Ball (List.set CCC) precycle"
                  "prepath P''"
                  "distinct P''"
                  "sum cc (List.set (Qpp@P'cc)) = \<CC> P'' + foldr (\<lambda>D. (+) (\<CC> D)) CCC 0"
                  "List.set ((to_redge_path (conv_to_rdg state) (rev Q))@P') = List.set P'' \<union> \<Union> {List.set D |D. D \<in> List.set CCC}"
                  "fstv (hd P'') = y'" "sndv (last P'') = y'" by auto
            have "sum cc (List.set (Qpp@P'cc)) = \<CC> (to_redge_path (conv_to_rdg state) (rev Q)) + \<CC> P'"
              using distinct_CC_sum distinct_PP_sum Qpp_def P'cc_def
                    P'_asm is_s_t_path_rev_Q unfolding is_s_t_path_def augpath_def prepath_def  \<CC>_def 
              by (subst set_append, subst sum.union_disjoint) auto
            then obtain C where C_prop:"(C = P'') \<or> C \<in> List.set CCC" "\<CC> C < 0"
              using costs all_props(4) fold_sum_neg_neg_element[of \<CC> CCC]
              by force
            have Rcap_pos:"Rcap (current_flow state) (List.set C) > 0"
              using is_s_t_path_rev_Q  C_prop  P'_asm sym[OF all_props(5)]
              unfolding augcycle_def augpath_def precycle_def is_s_t_path_def prepath_def \<CC>_def
              by (intro Rcap_subset[of "List.set P'' \<union> \<Union> {List.set D |D. D \<in> List.set CCC}" "List.set C"], 
                auto intro: Rcap_union[of "List.set (to_redge_path (conv_to_rdg state) (rev Q))" "List.set P'"])
            have "augcycle (current_flow state) C"
              using C_prop all_props P'_asm is_s_t_path_rev_Q Rcap_pos
              by (auto simp add: augcycle_def augpath_def precycle_def is_s_t_path_def)
            thus False 
              using assms(1) min_cost_flow_no_augcycle by (auto simp add: invar_isOptflow_def)
          qed
        qed
      qed
    qed


fun cnt_P where
  "cnt_P [] _ = 0" |
  "cnt_P (x#xs) P = (if P x then Suc (cnt_P xs P) else cnt_P xs P)"

lemma cnt_P_add: "cnt_P (xs@ys) P = cnt_P xs P + cnt_P ys P"
  by(induction xs) auto

lemma cnt_P_0:"\<not>(\<exists> x \<in> set xs. P x) \<Longrightarrow> cnt_P xs P = 0"
  by(induction xs, auto)

lemma cnt_P_0_set:"cnt_P xs (\<lambda> x.  \<not> P x) = 0  \<Longrightarrow> set xs \<subseteq> {x.  P x}"
  apply(induction xs, simp)
  apply(subst (asm) cnt_P.simps)
  subgoal for a xs
    by(cases "P a", simp, simp) 
  done

lemma cnt_P_0_set2:"set xs \<subseteq> {x.  P x} \<Longrightarrow> cnt_P xs (\<lambda> x.  \<not> P x) = 0"
  apply(induction xs, simp)
  apply(subst  cnt_P.simps)
  subgoal for a xs
    by(cases "P a", simp, simp) 
  done

lemma cnt_P_subset: 
  assumes "set ys \<subseteq> set xs"
          "cnt_P xs (\<lambda> x.  P x) = 0" 
    shows "cnt_P ys (\<lambda> x.  P x) = 0"
proof(rule ccontr, goal_cases)
  case 1
  have "set xs \<subseteq> {x. \<not> P x}"
    using cnt_P_0_set[of xs "\<lambda> x. \<not> P x"] assms by simp
  moreover have "\<not> set ys \<subseteq> {x. \<not> P x}"
    using cnt_P_0_set2[of ys "\<lambda> x. \<not> P x"] 1 by auto
  ultimately show False using assms(1) by simp
qed

lemma aux_invar_subs: 
  assumes     "aux_invar state"
               "\<FF>i = \<FF> state"
               "f = current_flow state"
               "E' = actives state"
               "to_rdg = conv_to_rdg state"
               "FF = (to_rdgs to_pair (conv_to_rdg state) \<FF>i)"
               "E'' = {e | e. e \<in> \<EE> \<and> oedge e \<in> to_set E'}"
               "EE = E'' \<union> FF"
             shows "EE \<subseteq> \<EE>"
    using assms(1)   assms(7)
    by(auto simp add: assms(6) assms(2) assms(1) assms(8) aux_invar_def invar_aux2_def to_graph_def  invar_aux21_def)
 
lemma simulate_inactives:
  assumes  "augpath f pp" "fstv (hd pp) = s" "sndv (last pp) = t" "set pp \<subseteq> \<EE>"
               "aux_invar state"
               "\<FF>i = \<FF> state"
               "f = current_flow state"
               "E' = actives state"
               "to_rdg = conv_to_rdg state"
               "FF = (to_rdgs to_pair (conv_to_rdg state) \<FF>i)"
               "E'' = {e | e. e \<in> \<EE> \<and> oedge e \<in> to_set E'}"
               "EE = E'' \<union> FF"
               "ca = cnt_P pp (\<lambda> e. e \<notin> EE)"
               "s \<noteq> t" "\<forall> e \<in> \<F> state. f e > 0"
         shows "\<exists> qq.  augpath f qq \<and> fstv (hd qq) = s \<and> sndv (last qq) = t \<and> set qq \<subseteq> EE \<and> qq \<noteq> []"
  using assms
proof(induction ca arbitrary: pp s t rule: less_induct)
  case (less ca)
  have EE_sub:"EE \<subseteq> \<EE>"
    using aux_invar_subs[OF less(6-13)] by simp
  hence EE_finite:"finite EE"
    by (simp add: finite_\<EE> finite_subset)
  then show ?case 
  proof(cases "ca = 0")
    case True
    hence pp_EE:"set pp \<subseteq> EE" 
      unfolding less
      by (metis Collect_mem_eq assms(10) cnt_P_0_set less.prems(6))
    show ?thesis 
      apply(rule exI[of _ pp])
      using less pp_EE 
      by (meson augpath_def prepath_def)
  next
    case False
    then obtain e where e_prop:"e \<in> set pp" "e \<notin> (to_rdgs to_pair (conv_to_rdg state) \<FF>i)"
                                "e \<notin> {e | e. e \<in> \<EE> \<and> oedge e \<in> to_set E'}"
      unfolding less 
      by (metis (mono_tags, lifting) Un_iff cnt_P_0)
    hence "oedge e \<in> \<E> - to_set (actives state)"
      using EE_sub less(5) unfolding less 
      using o_edge_res by auto
    hence "connected_component (\<FF> state) (fst (oedge e)) =
           connected_component (\<FF> state) (snd  (oedge e))"
      using less(6) unfolding aux_invar_def invar_aux13_def less invar_aux21_def
      by simp
    hence "connected_component (\<FF> state) (fstv e) =
           connected_component (\<FF> state) (sndv e)"
      by(cases e, auto)
    hence or_reach:"fstv e = sndv e \<or> reachable  (\<FF> state) (fstv e) (sndv e)"
      by (metis in_connected_componentE in_connected_componentI2)
    obtain p1 p2 where p1p2:"p1@[e]@p2 = pp"
      by (metis \<open>e \<in> set pp\<close> in_set_conv_decomp_last single_in_append)
    show ?thesis 
    proof(cases rule: orE'[OF  Meson.disj_comm[OF or_reach]])
      case 2
      have a1: "e # p2 = pp \<Longrightarrow> p1 = [] \<Longrightarrow> fstv e = sndv e \<Longrightarrow> augpath f pp \<Longrightarrow> augpath f p2"
          apply(rule augpath_split2[of f "p1@[e]"])
        using p1p2 less  by auto
      have a2: "augpath f pp \<Longrightarrow> p1 \<noteq> [] \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> sndv (last p1) = fstv (hd p2)"
        using 2 p1p2  augpath_split3[of f p1 "[e]@p2"] augpath_split3[of f "p1@[e]" "p2"] 
        by simp
      have a3: "p1 \<noteq>[] \<Longrightarrow> p2 = [] \<Longrightarrow> augpath f p1"
           apply(rule augpath_split1[of  f _ "[e]@p2"])
            using p1p2 less by auto
     have a:"augpath f (p1@p2)" 
        using p1p2 less(2) 2
        apply(cases p1, simp add: a1)
        subgoal for p pp1
           using a3 augpath_split1[of f "p1" "[e]@p2"]  augpath_split2[of f "p1@[e]" p2] a2 
           by (cases p2) (simp,intro augpath_app, auto)
            done
      moreover have b:" fstv (hd (p1@p2)) = s"  
          using p1p2 less(3, 4, 2) 2  augpath_split3[of f "[e]" p2]  less.prems(1) less.prems(14) 
          by (cases p1) force+
        moreover have c:"sndv (last (p1@p2)) = t"
          using p1p2 less(3, 4, 2) 2  augpath_split3[of f p1 "[e]"]  less.prems(1) less.prems(14) 
          by (cases p2) force+
      moreover have d:"set (p1@p2) \<subseteq> \<EE>"
        using less.prems(4) p1p2 by auto
      moreover have e: "cnt_P (p1 @ p2) (\<lambda>e. e \<notin> EE) < ca"
        apply(subst less(14), subst sym[OF p1p2(1)],
              subst cnt_P_add[of p1 "[e]@p2" "(\<lambda>e. e \<notin> EE)"], subst cnt_P_add[of "[e]" "p2" "(\<lambda>e. e \<notin> EE)"])
        apply(subst cnt_P_add, simp)
        using e_prop unfolding less by simp
      have "\<exists>qq. augpath f qq \<and> fstv (hd qq) = s \<and> sndv (last qq) = t \<and> set qq \<subseteq> EE \<and> qq \<noteq> []"
        using less(1)[of "cnt_P (p1@p2) (\<lambda> e. e \<notin> EE)" "p1@p2" s t, 
                      OF e a b c d less(6) less(7-13) _ less(15) less(16)] by simp
      thus ?thesis by simp
    next
      case 1
      obtain Q where Qpr:"walk_betw (\<FF> state) (fstv e) Q (sndv e)" 
        using 1 unfolding reachable_def by auto
      find_theorems walk_betw distinct
      hence Qend:"hd Q = fstv e" "last Q = sndv e" unfolding walk_betw_def by auto
      have QQpre:"prepath (to_redge_path (conv_to_rdg state) Q)"
        using less(6)[simplified aux_invar_def] 1(2) Qpr 
        by (auto intro: perpath_to_redgepath[of state _ "fstv e" Q "sndv e"]  
              simp add: walk_betw_length)
      define QQ where "QQ= to_redge_path (conv_to_rdg state) Q"
      have Qlength: "2 \<le> length Q" 
        by (meson "1"(2) Qpr walk_betw_length)
      have QQleng:"length QQ > 0" unfolding QQ_def
        using Qlength 
        by(cases rule: list_cases4[of Q], auto) 
      have QQE: "set QQ \<subseteq> to_rdgs to_pair (conv_to_rdg state) (\<FF> state)"
        apply(subst from_aux_invar'(21)[OF assms(5)])
        unfolding QQ_def 
        using Qpr  Qlength  less(6) 
        by(intro concretize_walk[of state "fstv e" Q "sndv e"])
          (auto simp add: from_aux_invar'(21)[OF assms(5)] aux_invar_def invar_aux14_def invar_aux2_def )         
        hence QQcap: " e \<in> set QQ \<Longrightarrow> 0 < \<uu>\<^bsub>f\<^esub>e" for e
          using less(16) oedge.simps rcap.simps infinite_u  from_aux_invar'(21)[OF assms(5)]
          by (cases rule: \<cc>.cases[of e])  force+
        have QQ_aug: "augpath f QQ"
        using QQpre  Rcap_strictI[of "set QQ" 0 f]  Rcap_strictI[of "set QQ" 0 f] QQcap QQleng
        unfolding QQ_def augpath_def by simp
      have Qfirst:"fstv (hd QQ) = hd Q" 
        unfolding QQ_def
        using less(6)[simplified aux_invar_def invar_aux6_def] Qlength
        by (auto intro: to_rdg_hd)
      have Qlast:"sndv (last QQ) = last Q" 
        unfolding QQ_def
        using less(6)[simplified aux_invar_def invar_aux6_def] Qlength
        by (auto intro: to_rdg_last)    
      have p2fst: "p2 \<noteq> [] \<Longrightarrow> fstv (hd p2) = sndv e" 
        using less.prems(1)  p1p2 augpath_split2[of f p1 "[e]@p2"] augpath_split3[of f "[e]" p2] by simp
      have p2snd: "p2 \<noteq> [] \<Longrightarrow> sndv (last p2) = t" 
        using less.prems(3) p1p2 by force
      have p2pre: "p2 \<noteq> [] \<Longrightarrow> augpath f p2" 
        using less.prems(1) p1p2 augpath_split2[of f "p1@[e]" p2] by simp
      have p1pre: "p1 \<noteq> [] \<Longrightarrow> augpath f p1"
        using less.prems(1) p1p2 augpath_split1 flow_network_axioms by blast
      have p1fst: "p1 \<noteq> [] \<Longrightarrow> fstv (hd p1) = s"
        using less.prems(2) p1p2 by auto
      have p1last: "p1 \<noteq> [] \<Longrightarrow> sndv (last p1) = fstv e"
        using less.prems(1) p1p2 augpath_split3 by force
      have A:"augpath f (p1@QQ@p2)"
        apply(cases p1, cases p2, simp add: QQpre QQ_def)
        using p2fst Qlast p2pre QQ_aug QQ_def augpath_app[of f QQ p2] Qend 
          apply simp apply simp
        subgoal
          using p1pre  QQ_aug QQ_def p2pre p2fst Qlast Qend QQleng Qfirst p1last 
          by(fastforce intro!: augpath_app)
        by (rule augpath_app, 
            insert p1pre  QQ_aug QQ_def p2pre p2fst Qlast Qend QQleng Qfirst p1last,
            simp , cases p2, auto intro: augpath_app)
      have B:"fstv (hd ((p1@QQ@p2))) = s"  
          using Qfirst Qend(1) p1p2 less(3) QQleng by (cases p1, auto)
      have C:"sndv (last ((p1@QQ@p2))) = t"  
        using Qlast Qend(2) p1p2 less(4) QQleng by(cases p2, auto)
      have QQE:"set QQ \<subseteq> \<EE>"
          unfolding QQ_def
          apply(rule subset_trans, rule concretize_walk[of state "fstv e" Q "sndv e"])
          using Qpr  Qlength  less(6) from_aux_invar'(21)[OF assms(5)] 
          by(auto simp add: aux_invar_def invar_aux14_def invar_aux2_def)
      have D:"set (p1@QQ@p2) \<subseteq> \<EE>"
        using p1p2 less(5) QQE  by auto
      have cnt0:"cnt_P QQ (\<lambda>e. e \<notin> EE) = 0"
        apply(rule cnt_P_0)
        using concretize_walk[of state "fstv e" Q "sndv e"] Qpr  Qlength  less(6) from_aux_invar'(21)[OF assms(5)]
        unfolding aux_invar_def invar_aux14_def invar_aux2_def less QQ_def
        by auto
      have E: "cnt_P (p1 @ QQ@ p2) (\<lambda>e. e \<notin> EE) < ca"
        apply(subst less(14), subst sym[OF p1p2(1)],
              subst cnt_P_add[of p1 "[e]@p2" "(\<lambda>e. e \<notin> EE)"], subst cnt_P_add[of "[e]" "p2" "(\<lambda>e. e \<notin> EE)"])       
        apply(subst cnt_P_add, subst cnt_P_add)
        using cnt0 e_prop unfolding less by simp
      have "\<exists>qq. augpath f qq \<and> fstv (hd qq) = s \<and> sndv (last qq) = t \<and> set qq \<subseteq> EE \<and> qq \<noteq> []"
        using less(1)[of "cnt_P (p1@QQ@p2) (\<lambda> e. e \<notin> EE)" "p1@QQ@p2" s t, 
                      OF E A B C D less(6) less(7-13) _ less(15) less(16)] by simp
      then show ?thesis by simp
    qed
  qed
qed

lemma simulate_inactives_costs:
  assumes  "augpath f pp" "fstv (hd pp) = s" "sndv (last pp) = t" "set pp \<subseteq> \<EE>"
               "aux_invar state"
               "\<FF>i = \<FF> state"
               "f = current_flow state"
               "E' = actives state"
               "to_rdg = conv_to_rdg state"
               "FF = (to_rdgs to_pair (conv_to_rdg state) \<FF>i)"
               "E'' = {e | e. e \<in> \<EE> \<and> oedge e \<in> to_set E'}"
               "EE = E'' \<union> FF"
               "ca = cnt_P pp (\<lambda> e. e \<notin> EE)"
               "s \<noteq> t" "\<forall> e \<in> \<F> state. f e > 0" "\<nexists> C. augcycle f C"
         shows "\<exists> qq.  augpath f qq \<and> fstv (hd qq) = s \<and> sndv (last qq) = t \<and> set qq \<subseteq> EE \<and>  
                       (foldr (\<lambda>x. (+) (\<cc> x)) qq 0) \<le>  (foldr (\<lambda>x. (+) (\<cc> x)) pp 0) \<and> qq \<noteq> []"
  using assms
proof(induction ca arbitrary: pp s t rule: less_induct)
  case (less ca)
  have EE_sub:"EE \<subseteq> \<EE>"
    using aux_invar_subs[OF less(6-13)] by simp
  hence EE_finite:"finite EE"
    by (simp add: finite_\<EE> finite_subset)
  then show ?case 
  proof(cases "ca = 0")
    case True
    hence pp_EE:"set pp \<subseteq> EE" 
      unfolding less 
    proof -
      assume "cnt_P pp (\<lambda>e. e \<notin> {e |e. e \<in> \<EE> \<and> oedge e \<in> to_set (actives state)} \<union> to_rdgs to_pair (conv_to_rdg state) (\<FF> state)) = 0"
      then have "set pp \<subseteq> {r. r \<in> {r |r. r \<in> \<EE> \<and> oedge r \<in> to_set (actives state)} \<union> to_rdgs to_pair (conv_to_rdg state) (\<FF> state)}"
        by (simp add: cnt_P_0_set)
      then show "set pp \<subseteq> {r |r. r \<in> \<EE> \<and> oedge r \<in> to_set (actives state)} \<union> to_rdgs to_pair (conv_to_rdg state) (\<FF> state)"
        by blast
    qed
    show ?thesis 
      apply(rule exI[of _ pp])
      using less pp_EE  augpath_cases by force
  next
    case False
    then obtain e where e_prop:"e \<in> set pp" "e \<notin> (to_rdgs to_pair (conv_to_rdg state) \<FF>i)"
                                "e \<notin> {e | e. e \<in> \<EE> \<and> oedge e \<in> to_set E'}"
      unfolding less 
      by (metis (mono_tags, lifting) Un_iff cnt_P_0)
    hence "oedge e \<in> \<E> - to_set (actives state)"
      using EE_sub less(5) less  o_edge_res by auto
    hence "connected_component (\<FF> state) (fst (oedge e)) = connected_component (\<FF> state) (snd  (oedge e))"
      using less(6) 
      by (auto simp  add: aux_invar_def invar_aux13_def less invar_aux21_def)
    hence "connected_component (\<FF> state) (fstv e) = connected_component (\<FF> state) (sndv e)"
      by(cases e, auto)
    hence or_reach:"fstv e = sndv e \<or> reachable  (\<FF> state) (fstv e) (sndv e)"
      by (metis in_connected_componentE in_connected_componentI2)  
    have e_rcap: "rcap f e > 0" 
      using augpath_rcap_pos_strict e_prop(1) less.prems(1) by blast
    obtain p1 p2 where p1p2:"p1@[e]@p2 = pp"
      by (metis \<open>e \<in> set pp\<close> in_set_conv_decomp_last single_in_append)
    hence costs_split: "foldr (\<lambda>x. (+) (\<cc> x)) pp 0 =
                      foldr (\<lambda>x. (+) (\<cc> x)) p1 0 + \<cc> e + foldr (\<lambda>x. (+) (\<cc> x)) p2 0"
      by(induction p1, auto, metis foldr_append foldr_last_append map_sum_split)  
    have costs_split2: "foldr (\<lambda>x. (+) (\<cc> x)) (p1@p2) 0 =
                      foldr (\<lambda>x. (+) (\<cc> x)) p1 0 + foldr (\<lambda>x. (+) (\<cc> x)) p2 0"
        by(induction p1, auto)  
    show ?thesis 
    proof(cases rule: orE'[OF  Meson.disj_comm[OF or_reach]])
      case 2
      have a1: "e # p2 = pp \<Longrightarrow> p1 = [] \<Longrightarrow> fstv e = sndv e \<Longrightarrow> augpath f pp \<Longrightarrow> augpath f p2"
          apply(rule augpath_split2[of f "p1@[e]"])
        using p1p2 less  by auto
      have a2: "augpath f pp \<Longrightarrow> p1 \<noteq> [] \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> sndv (last p1) = fstv (hd p2)"
        using 2 p1p2  augpath_split3[of f p1 "[e]@p2"] augpath_split3[of f "p1@[e]" "p2"] 
        by simp
      have a3: "p1 \<noteq>[] \<Longrightarrow> p2 = [] \<Longrightarrow> augpath f p1"
           apply(rule augpath_split1[of  f _ "[e]@p2"])
            using p1p2 less by auto
     have a:"augpath f (p1@p2)" 
        using p1p2 less(2) 2
        apply(cases p1, simp add: a1)
        subgoal for p pp1
           using a3 augpath_split1[of f "p1" "[e]@p2"]  augpath_split2[of f "p1@[e]" p2] a2 
           by (cases p2) (simp,intro augpath_app, auto)
            done
      moreover have b:" fstv (hd (p1@p2)) = s"  
          using p1p2 less(3, 4, 2) 2  augpath_split3[of f "[e]" p2]  less.prems(1) less.prems(14) 
          by (cases p1) force+
        moreover have c:"sndv (last (p1@p2)) = t"
          using p1p2 less(3, 4, 2) 2  augpath_split3[of f p1 "[e]"]  less.prems(1) less.prems(14) 
          by (cases p2) force+
      moreover have d:"set (p1@p2) \<subseteq> \<EE>"
        using less.prems(4) p1p2 by auto
      moreover have e: "cnt_P (p1 @ p2) (\<lambda>e. e \<notin> EE) < ca"
        apply(subst less(14), subst sym[OF p1p2(1)],
              subst cnt_P_add[of p1 "[e]@p2" "(\<lambda>e. e \<notin> EE)"], subst cnt_P_add[of "[e]" "p2" "(\<lambda>e. e \<notin> EE)"])
        apply(subst cnt_P_add, simp)
        using e_prop  less by simp
      have ce:"\<cc> e \<ge> 0"
        apply(rule ccontr, rule sufficientE[of "augcycle f [e]"])
        using less(17,2,5) e_prop(1) rcap_extr_strict[of e pp 0 f] prepath_intros(1)[of e] 
              Rcap_strictI[of "set [e]" 0 f] 2 
        by(fastforce simp add: augpath_def augcycle_def \<CC>_def)+
      have F: "foldr (\<lambda>x. (+) (\<cc> x)) (p1@p2) 0 \<le> foldr (\<lambda>x. (+) (\<cc> x)) pp 0"
        using costs_split2 costs_split ce by simp
     have "\<exists>qq. augpath f qq \<and> fstv (hd qq) = s \<and> sndv (last qq) = t \<and> set qq \<subseteq> EE \<and>
                foldr (\<lambda>x. (+) (\<cc> x)) qq 0 \<le> foldr (\<lambda>x. (+) (\<cc> x)) (p1@p2) 0 \<and> qq \<noteq> []"
        using less(1)[of "cnt_P (p1@p2) (\<lambda> e. e \<notin> EE)" "p1@p2" s t, 
                      OF e a b c d less(6) less(7-13) _ less(15) less(16) less(17)] by simp       
      thus ?thesis using F by auto
    next
      case 1
      obtain Q where Qpr:"walk_betw (\<FF> state) (fstv e) Q (sndv e)" 
        using 1  by (auto simp add: reachable_def)
      hence Qend:"hd Q = fstv e" "last Q = sndv e"  by (auto simp add: walk_betw_def)
      have QQpre:"prepath (to_redge_path (conv_to_rdg state) Q)"
        using less(6)[simplified aux_invar_def] 1(2) Qpr 
        by (auto intro: perpath_to_redgepath[of state _ "fstv e" Q "sndv e"]  
              simp add: walk_betw_length)
      define QQ where "QQ= to_redge_path (conv_to_rdg state) Q"
      have Qlength: "2 \<le> length Q" 
        by (meson "1"(2) Qpr walk_betw_length)
      have QQleng:"length QQ > 0" 
        using Qlength 
        by(cases rule: list_cases4[of Q], auto simp add: QQ_def) 
      have to_graph_remove:"(to_graph (\<FF>_imp state)) = \<FF> state"
        by (simp add: from_aux_invar'(21) less.prems(5))
      have QQF: "set QQ \<subseteq> to_rdgs to_pair (conv_to_rdg state) (\<FF> state)"
          using concretize_walk[of state "fstv e" Q "sndv e", simplified to_graph_remove]  Qpr  Qlength  less(6)
          by(auto simp add: aux_invar_def invar_aux14_def invar_aux2_def  QQ_def)
        hence QQcap: " e \<in> set QQ \<Longrightarrow> 0 < \<uu>\<^bsub>f\<^esub>e" for e
          using less(16) oedge.simps rcap.simps infinite_u to_graph_remove
          by (cases rule: \<cc>.cases[of e])  force+
      have Qfirst:"fstv (hd QQ) = hd Q" 
        unfolding QQ_def
        using less(6)[simplified aux_invar_def invar_aux6_def] Qlength
        by (auto intro: to_rdg_hd)
      have Qlast:"sndv (last QQ) = last Q" 
        unfolding QQ_def
        using less(6)[simplified aux_invar_def invar_aux6_def] Qlength
        by (auto intro: to_rdg_last)  
      obtain QQ' where QQ'_prop:"prepath QQ'" "distinct QQ'" "set QQ' \<subseteq> set QQ"
       "fstv (hd QQ) = fstv (hd QQ')" "sndv (last QQ) = sndv (last QQ')"  "QQ' \<noteq> []"
        using QQ_def QQpre QQleng prepath_drop_cycles[of QQ "set QQ"] by auto    
      have QQ_aug: "augpath f QQ'"
        using QQpre  Rcap_strictI[of "set QQ'" 0 f]  QQcap QQleng QQ'_prop
        unfolding QQ_def augpath_def by auto
      have p2fst: "p2 \<noteq> [] \<Longrightarrow> fstv (hd p2) = sndv e" 
        using less.prems(1)  p1p2 augpath_split2[of f p1 "[e]@p2"] augpath_split3[of f "[e]" p2] by simp
      have p2snd: "p2 \<noteq> [] \<Longrightarrow> sndv (last p2) = t" 
        using less.prems(3) p1p2 by force
      have p2pre: "p2 \<noteq> [] \<Longrightarrow> augpath f p2" 
        using less.prems(1) p1p2 augpath_split2[of f "p1@[e]" p2] by simp
      have p1pre: "p1 \<noteq> [] \<Longrightarrow> augpath f p1"
        using less.prems(1) p1p2 augpath_split1 flow_network_axioms by blast
      have p1fst: "p1 \<noteq> [] \<Longrightarrow> fstv (hd p1) = s"
        using less.prems(2) p1p2 by auto
      have p1last: "p1 \<noteq> [] \<Longrightarrow> sndv (last p1) = fstv e"
        using less.prems(1) p1p2 augpath_split3 by force
      have A:"augpath f (p1@QQ'@p2)"
        apply(cases p1, cases p2, simp add: QQpre QQ_def)
        using p2fst Qlast p2pre QQ_aug QQ_def augpath_app[of f QQ p2] Qend 
          apply simp apply simp
        subgoal
          using p1pre  QQ_aug QQ_def p2pre p2fst Qlast Qend QQleng Qfirst p1last QQ'_prop
          by(fastforce intro!: augpath_app)
        by (rule augpath_app, 
            insert p1pre  QQ_aug QQ_def p2pre p2fst Qlast Qend QQleng Qfirst p1last QQ'_prop,
            simp , cases p2, auto intro: augpath_app)
      have B:"fstv (hd ((p1@QQ'@p2))) = s"  
          using Qfirst Qend(1) p1p2 less(3) QQleng QQ'_prop by (cases p1, auto)
      have C:"sndv (last ((p1@QQ'@p2))) = t"  
        using Qlast Qend(2) p1p2 less(4) QQleng QQ'_prop by(cases p2, auto)
      have QQE:"set QQ \<subseteq> \<EE>"
          unfolding QQ_def
          apply(rule subset_trans, rule concretize_walk[of state "fstv e" Q "sndv e"])
          using Qpr  Qlength  less(6) to_graph_remove 
          by(auto simp add: aux_invar_def invar_aux14_def invar_aux2_def )
        hence QQE:"set QQ' \<subseteq> \<EE>"
          using QQ'_prop by simp
      have D:"set (p1@QQ'@p2) \<subseteq> \<EE>"
        using p1p2 less(5) QQE  by auto
      have cnt0:"cnt_P QQ (\<lambda>e. e \<notin> EE) = 0"
        using concretize_walk[of state "fstv e" Q "sndv e"] Qpr  Qlength  less(6) to_graph_remove
        by(auto intro: cnt_P_0 simp add: aux_invar_def invar_aux14_def invar_aux2_def less QQ_def)
      hence cnt0:"cnt_P QQ' (\<lambda>e. e \<notin> EE) = 0" 
        using cnt_P_subset[of QQ' QQ] QQ'_prop by simp
      have E: "cnt_P (p1 @ QQ'@ p2) (\<lambda>e. e \<notin> EE) < ca"
        apply(subst less(14), subst sym[OF p1p2(1)],
              subst cnt_P_add[of p1 "[e]@p2" "(\<lambda>e. e \<notin> EE)"], subst cnt_P_add[of "[e]" "p2" "(\<lambda>e. e \<notin> EE)"])       
        apply(subst cnt_P_add, subst cnt_P_add)
        using cnt0 e_prop unfolding less by simp
      have "\<exists>qq. augpath f qq \<and> fstv (hd qq) = s \<and> sndv (last qq) = t \<and> set qq \<subseteq> EE \<and>
                 set qq \<subseteq> EE \<and> foldr (\<lambda>x. (+) (\<cc> x)) qq 0 \<le> foldr (\<lambda>x. (+) (\<cc> x)) (p1 @ QQ' @ p2) 0 \<and> qq \<noteq> []"
        using less(1)[of "cnt_P (p1@QQ'@p2) (\<lambda> e. e \<notin> EE)" "p1@QQ'@p2" s t, 
                      OF E A B C D less(6) less(7-13) _ less(15) less(16) less(17)] by simp
      moreover have costs_split3: "foldr (\<lambda>x. (+) (\<cc> x)) (p1 @ QQ' @ p2) 0 =
             foldr (\<lambda>x. (+) (\<cc> x)) p1 0 + foldr (\<lambda>x. (+) (\<cc> x)) QQ' 0 + foldr (\<lambda>x. (+) (\<cc> x)) p2 0"
        by (metis append_eq_appendI map_sum_split)
      moreover have "foldr (\<lambda>x. (+) (\<cc> x)) QQ' 0 \<le> \<cc> e"
      proof(rule ccontr, goal_cases)
        case 1
        hence costeQQ':"foldr (\<lambda>x. (+) (\<cc> x)) QQ' 0 > \<cc> e" by simp
        define QQrev where "QQrev = rev (map erev QQ')"
        define QQpp where "QQpp = map PP QQrev"
        define ecc where "ecc = map CC [e]"
        have markers_removeQ: "QQrev = map to_redge QQpp"
              unfolding QQpp_def 
              by(induction QQrev) auto
       have markers_removeP: "[e] = map to_redge ecc"
         unfolding ecc_def by simp
       have markers_remove: "QQrev @ [e] = map to_redge (QQpp@ecc)"
           unfolding QQpp_def 
           using markers_removeP 
           by (induction QQrev) auto
         have QQpp_last:"sndvv (last QQpp) = fstv (hd QQ')"
           using QQ'_prop(6) unfolding QQpp_def QQrev_def 
           by(induction QQ', auto simp add: vs_erev)
         have QQpp_fst:"fstvv (hd QQpp) = sndv (last QQ')"
           using QQ'_prop(6) unfolding QQpp_def QQrev_def 
           by(induction QQ', auto simp add: vs_erev)
         have QQrev_cap: "e \<in> set QQrev \<Longrightarrow> rcap f e > 0" for e
         proof(goal_cases)
           case 1
           then obtain d where dpr:"e = erev d" "d \<in> set QQ'" by(auto simp add: QQrev_def)
           hence "oedge d  \<in> \<F> state" 
             using QQ'_prop(3) QQF to_graph_remove  by auto
           hence "f (oedge d) > 0" using less by auto
           then show ?case 
             by(cases rule: erev.cases[of e], simp add: infinite_u)
               (cases rule: erev.cases[of d], auto simp add: dpr(1))
         qed
         have QQrevpre: "prepath QQrev" 
           using QQ'_prop(6) QQ'_prop(1) unfolding QQrev_def 
           apply(induction QQ', simp, simp)
           subgoal for a QQ'a
             apply(cases "QQ'a", simp, rule prepath_intros(1))
             subgoal for aa list
             using prepath_split2[of "[a]"  QQ'a]  prepath_split3[of "[a]" QQ'a] vs_erev(2)[of a] vs_erev(1)[of aa]
             by(intro prepath_append , auto intro: prepath_intros(1))
           done
         done
       have QQrev_leng: "length QQrev > 0" 
         by (metis QQrevpre length_greater_0_conv list.simps(3) prepath_simps)
       hence augpathQQrev: "augpath f QQrev"
           using QQrevpre QQrev_cap Rcap_strictI[of "set QQrev" 0 f] 
           unfolding augpath_def by simp
       have hpath: "hpath (QQpp @ ecc)"
             using QQpp_last QQ'_prop(4) Qfirst Qend(1) augpathQQrev
             unfolding ecc_def QQpp_def
             by(auto intro: h_path_append augpath_to_hpath_PP[of f] hpath_intros(1))

       have distinctQQrev: "distinct QQrev"
         unfolding QQrev_def
         apply(subst distinct_rev, subst distinct_map)
         using QQ'_prop(2) inj_erev unfolding inj_on_def by auto
      have distinct:"distinct (QQpp @ ecc)"
           using distinct_map[of ] distinct_append distinctQQrev
           unfolding QQpp_def  ecc_def is_s_t_path_def inj_on_def 
           by auto
         have to_redge_PP_id: "to_redge \<circ> PP = id"
           by auto
         have b1: "QQrev @ [e] = map to_redge (QQpp @ ecc)"
          unfolding QQrev_def ecc_def QQpp_def 
          by(simp, subst to_redge_PP_id, subst list.map_id0, simp)
        have b2: "e \<in> \<EE>" 
          using e_prop(1) less.prems(4) by blast
        have b2a:"set QQ \<subseteq> \<EE>"
          using QQF assms(5) to_graph_remove by(auto simp add: aux_invar_def invar_aux2_def)
        have b3: "set QQrev \<subseteq> \<EE>"
          using subset_trans[OF QQ'_prop(3) b2a] unfolding QQrev_def
          by(induction QQ', auto simp add: erev_\<EE>)      
      have "\<exists>PP CCC.
                  Ball (set CCC) precycle \<and>
                  prepath PP \<and>
                  distinct PP \<and>
                  sum cc (set (QQpp@ecc)) = \<CC> PP + foldr (\<lambda>D. (+) (\<CC> D)) CCC 0 \<and>
                  set (QQrev@[e]) = set PP \<union> \<Union> {set D |D. D \<in> set CCC} \<and> 
                  fstv (hd PP) = sndv e \<and> sndv (last PP) = sndv e"   
        using b1  hpath  distinct b3 b2 QQpp_fst QQ'_prop Qlast Qend(2) Qlast vs_erev(1)[of e]
        unfolding QQpp_def QQrev_def ecc_def 
        by (intro distinct_hpath_to_distinct_augpath_and_augcycles, auto)
       then obtain P'' CCC where all_props:" Ball (set CCC) precycle"
                  "prepath P''"
                  "distinct P''"
                  "sum cc (set (QQpp@ecc)) = \<CC> P'' + foldr (\<lambda>D. (+) (\<CC> D)) CCC 0"
                  "set (QQrev@[e]) = set P'' \<union> \<Union> {set D |D. D \<in> set CCC}"
                  "fstv (hd P'') = sndv e" "sndv (last P'') = sndv e" by auto
            have "sum cc (set (QQpp@ecc)) = \<CC> (QQrev) + \<cc> e"
              unfolding \<CC>_def 
              using distinct_CC_sum distinct_PP_sum QQpp_def ecc_def
                    1 distinctQQrev
              by (subst set_append, subst sum.union_disjoint, auto)
            have costs_negated: "foldr (\<lambda>x. (+) (\<cc> x)) QQrev 0 = 
                                 - foldr (\<lambda>x. (+) (\<cc> x)) QQ' 0"
              unfolding QQrev_def
              by(induction QQ', simp, subst list.map(2), subst rev.simps(2), 
                    subst sym[OF foldr_last_append], simp add: erev_costs) 
            have below_zero:"foldr (\<lambda>x. (+) (\<cc> x)) QQrev 0 + \<cc> e < 0"
              using costeQQ' costs_negated by auto
            have sum_flod:"sum cc (set (QQpp @ ecc)) = foldr (\<lambda>x. (+) (cc x))  (QQpp @ ecc) 0" 
              using distinct distinct_sum2 by blast
            have "foldr (\<lambda>x. (+) (cc x))  (QQpp @ ecc) 0 = foldr (\<lambda>x. (+) (\<cc> x)) QQrev 0 + \<cc> e" 
              unfolding QQpp_def ecc_def
              by(induction QQrev, auto)
            then obtain C where C_prop:"(C = P'') \<or> C \<in> set CCC" "\<CC> C < 0"
              using all_props(4) fold_sum_neg_neg_element[of \<CC> CCC] below_zero sum_flod
              by(cases "\<CC> P''  < 0", auto)
            have Rcap_pos:"Rcap f (set C) > 0"
              using all_props(1,2) C_prop all_props(5) Rcap_union[of "set QQrev" "set [e]" 0 f]
                    QQrev_leng QQrev_cap Rcap_strictI[of "set QQrev" 0 f] Rcap_strictI[of "{e}" 0 f] 
                    e_rcap 
              by (intro Rcap_subset[of "set P'' \<union> \<Union> {set D |D. D \<in> set CCC}" "set C"], auto simp add: precycle_def prepath_def)
            hence "augcycle f C"
              using C_prop all_props b2 b3
              unfolding augcycle_def augpath_def precycle_def  by auto
            thus False 
              using assms(16) by simp
          qed
      moreover hence "foldr (\<lambda>x. (+) (\<cc> x)) p1 0 + foldr (\<lambda>x. (+) (\<cc> x)) QQ' 0 
                                     + foldr (\<lambda>x. (+) (\<cc> x)) p2 0 \<le> 
                         foldr (\<lambda>x. (+) (\<cc> x)) pp 0"
        using costs_split by auto
      ultimately show ?thesis by auto
    qed
  qed
qed

end
end