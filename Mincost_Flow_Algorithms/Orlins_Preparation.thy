section \<open>Supplementary Theory for Orlin's Algorithm\<close>

theory Orlins_Preparation
  imports Path_Aug_Opt "HOL-Data_Structures.Set_Specs" 
          Undirected_Set_Graphs.Pair_Graph_Berge_Adaptor Directed_Set_Graphs.Pair_Graph_Specs  
          Undirected_Set_Graphs.Connected_Components
          Undirected_Set_Graphs.Directed_Undirected
begin

context 
  flow_network
begin
lemmas number_of_comps_anti_mono_strict=number_of_comps_anti_mono_strict[OF  _ _ _ _ _ \<V>_finite]
lemmas number_of_comps_anti_mono = number_of_comps_anti_mono[OF _ _ \<V>_finite]
end

subsection \<open>Program States and Invariants\<close>

datatype return = success | infeasible | notyetterm

text \<open>Then we setup the program state.\<close>

record ('f, 'b, '\<FF>, 'conv_to_rdg, 'actives, 'rep_comp_card, 'not_blocked)
          Algo_state = current_flow :: 'f
                            balance :: 'b
                                  \<FF> :: '\<FF>
                             conv_to_rdg :: 'conv_to_rdg
                             actives:: 'actives
                             return:: return
                             current_\<gamma>::real
                             rep_comp_card::'rep_comp_card
                             not_blocked::'not_blocked

locale Set_with_predicate = 
fixes get_from_set   :: "('a \<Rightarrow> bool) \<Rightarrow> 'actives  \<Rightarrow> 'a option"
fixes filter:: "('a => bool) =>'actives  => 'actives "
fixes are_all:: "('a \<Rightarrow> bool) \<Rightarrow> 'actives \<Rightarrow> bool"
fixes set_invar
fixes to_set

assumes set_get:   
  "\<lbrakk> set_invar s1; \<exists> x. x \<in> to_set s1 \<and> P x \<rbrakk> \<Longrightarrow> \<exists> y. get_from_set P s1 = Some y"
  "\<lbrakk> set_invar s1; get_from_set P s1 = Some x\<rbrakk> \<Longrightarrow> x \<in> to_set s1"
  "\<lbrakk> set_invar s1; get_from_set P s1 = Some x\<rbrakk> \<Longrightarrow> P x"              
assumes set_filter:   
  "\<lbrakk> set_invar s1 \<rbrakk> \<Longrightarrow> to_set(filter P s1) = to_set s1 - {x. x \<in> to_set s1 \<and> \<not> P x}"
assumes invar_filter: "\<lbrakk> set_invar s1\<rbrakk> \<Longrightarrow> set_invar(filter P s1)"
assumes are_all: "\<lbrakk> set_invar S\<rbrakk> \<Longrightarrow> are_all P S \<longleftrightarrow> (\<forall> x \<in> to_set S. P x)"

locale map_update_all = map:
 Map map_empty "update::'a \<Rightarrow> 'b \<Rightarrow> 'map \<Rightarrow> 'map" delete lookup map_invar
  for map_empty update delete lookup map_invar +
fixes update_all::"('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>  'map \<Rightarrow> 'map"
assumes update_all: 
    "\<And> rep f x. \<lbrakk>map_invar rep ; x \<in> dom (lookup rep)\<rbrakk> 
                  \<Longrightarrow> lookup (update_all f rep) x =
                           Some (f x (the (lookup rep x)))"
    "\<And> rep f g. \<lbrakk>map_invar rep;
                (\<And> x. x \<in> dom (lookup rep)  \<Longrightarrow>
                     f x (the (lookup rep x)) = g x (the (lookup rep x)))\<rbrakk> \<Longrightarrow>
          update_all f rep = update_all g rep "
   "\<And> rep f. map_invar rep \<Longrightarrow> map_invar (update_all f rep)"
   "\<And> rep f. map_invar rep \<Longrightarrow> dom (lookup (update_all f rep))
                                    = dom (lookup rep)"

context cost_flow_spec
begin

definition "consist E conv_to_rdg = ((\<forall> (x, y) \<in> E. \<exists> e. ((conv_to_rdg (x,y) = F e \<and> make_pair e = (x,y)) \<or>
                                     conv_to_rdg (x,y) = B e \<and> make_pair e = (y,x))) \<and>
                             (\<forall> x y e. (x, y) \<in> E \<and> x \<noteq> y \<longrightarrow> (conv_to_rdg (x,y) = F e \<longleftrightarrow>
                                     conv_to_rdg (y,x) = B e)))" for conv_to_rdg

lemma consistE:
  assumes "consist E to_rdg" 
          "\<lbrakk>(\<And> x y. (x, y) \<in> E \<Longrightarrow> \<exists> e. ((to_rdg (x,y) = F e \<and> make_pair e = (x,y)) \<or>
                                     to_rdg (x,y) = B e \<and> make_pair e = (y,x)) );
           (\<And> x y e. (x, y) \<in> E \<Longrightarrow> x \<noteq> y \<Longrightarrow> (to_rdg (x,y) = F e) = (to_rdg (y, x) = B e))\<rbrakk> \<Longrightarrow> P"
        shows P
  using assms by(force simp add:  consist_def split: prod.split)

lemma consistD:
  assumes "consist E to_rdg" 
  shows  "(x, y) \<in> E \<Longrightarrow> \<exists> e. ((to_rdg (x,y) = F e \<and> make_pair e = (x,y)) \<or>
                                     to_rdg (x,y) = B e \<and> make_pair e = (y,x))"
         "\<lbrakk>(x, y) \<in> E; x \<noteq> y\<rbrakk> \<Longrightarrow> (to_rdg (x,y) = F e) = (to_rdg (y, x) = B e)"
  by(meson assms consistE)+

lemma consistI:
  assumes "(\<And> x y. (x, y) \<in> E \<Longrightarrow> \<exists> e. ((to_rdg (x,y) = F e \<and> make_pair e = (x,y)) \<or>
                                     to_rdg (x,y) = B e \<and> make_pair e = (y,x)) )" 
         "(\<And> x y e. \<lbrakk>(x, y) \<in> E; x \<noteq> y\<rbrakk> \<Longrightarrow> (to_rdg (x,y) = F e) = (to_rdg (y, x) = B e))"
   shows "consist E to_rdg"
  using assms by(force simp add:  consist_def split: prod.split) 

lemma consist_conv_inj:"consist E conv \<Longrightarrow> a \<in> E \<Longrightarrow> b \<in> E \<Longrightarrow> conv a = conv b \<Longrightarrow> a = b"
  unfolding consist_def
  apply(rule Redge.induct[of _ "conv a"])
  apply(all \<open>rule Redge.induct[ of _ "conv b"]\<close>)
  apply(all \<open>cases a\<close>, all \<open>cases b\<close>)
  using Redge.inject Redge.distinct
  by (smt (verit) case_prod_conv prod.inject)+

end

locale alg = cost_flow_spec  where fst=fst for fst::"'edge \<Rightarrow> 'a"+ 
  fixes edge_map_update:: "'a \<Rightarrow> 'edge_vset \<Rightarrow> 'edges \<Rightarrow> 'edges" 
    and vset_empty :: "'vset"  ("\<emptyset>\<^sub>N") 
    and vset_delete :: "'a \<Rightarrow> 'vset \<Rightarrow> 'vset" 
    and vset_insert and vset_inv and isin 
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
 adjmap: Map'  where update = update and invar = adjmap_inv +
 vset: Set_Choose where empty = vset_empty and delete = vset_delete and insert = vset_insert  and 
                        invar = vset_inv and isin = isin
for update :: "'a \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'adjmap" and 
    adjmap_inv :: "'adjmap \<Rightarrow> bool"  and
    vset_empty :: "'vset"  ("\<emptyset>\<^sub>N") and 
    vset_delete :: "'a \<Rightarrow> 'vset \<Rightarrow> 'vset" and
    vset_insert and 
    vset_inv and 
    isin
begin
notation vset_empty ("\<emptyset>\<^sub>N")

abbreviation isin' (infixl "\<in>\<^sub>G" 50) where "isin' G v \<equiv> isin v G" 
abbreviation not_isin' (infixl "\<notin>\<^sub>G" 50) where "not_isin' G v \<equiv> \<not> isin' G v"

definition neighbourhood::"'adjmap \<Rightarrow> 'a \<Rightarrow> 'vset" where
  "neighbourhood G v = (case (lookup G v) of Some vset \<Rightarrow> vset | _ \<Rightarrow> vset_empty)"

notation "neighbourhood" ("\<N>\<^sub>G _ _" 100)

definition digraph_abs ("[_]\<^sub>g") where "digraph_abs G = {(u,v). v \<in>\<^sub>G (\<N>\<^sub>G G u)}" 

definition "to_graph Forest = UD (digraph_abs Forest)"

lemma to_graph'_def:  "to_graph Forest = { {u, v} | u v. (u, v) \<in> digraph_abs Forest}"
  by(auto simp add: to_graph_def UD_def)

lemma in_to_graphE: 
"\<lbrakk>{u, v} \<in> to_graph F; ((u, v) \<in> digraph_abs F \<Longrightarrow> P); ((v, u) \<in> digraph_abs F \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P" for F
  by(auto simp add: to_graph'_def doubleton_eq_iff)

lemma dVs_Vs_same: "dVs (digraph_abs G) = Vs (to_graph G)"
  by(auto simp add: to_graph'_def Vs_def dVs_def)

definition "good_graph_invar G = ( (adjmap_inv G \<and>
               (\<forall> v N. lookup G v = Some N \<longrightarrow> vset_inv N) \<and>
               finite {v. (lookup G v) \<noteq> None} \<and>
               (\<forall> v N. (lookup G v) = Some N \<longrightarrow> finite (t_set N))))"

lemma good_graph_invarE: 
 "\<lbrakk>good_graph_invar G;
  (\<lbrakk>adjmap_inv G; (\<And> v N. lookup G v = Some N \<Longrightarrow> vset_inv N); finite {v. (lookup G v) \<noteq> None};
    (\<And> v N. (lookup G v) = Some N \<Longrightarrow> finite (t_set N))\<rbrakk> \<Longrightarrow> P)\<rbrakk> 
   \<Longrightarrow> P"
  by(auto simp add: good_graph_invar_def)

lemma good_graph_invarI: 
 "\<lbrakk>adjmap_inv G ; (\<And> v N. lookup G v = Some N \<Longrightarrow> vset_inv N);
   finite {v. (lookup G v) \<noteq> None} ; (\<And> v N. (lookup G v) = Some N \<Longrightarrow> finite (t_set N))\<rbrakk>
   \<Longrightarrow> good_graph_invar G"
  by(auto simp add: good_graph_invar_def)

definition "insert_undirected_edge u v forst = (let vsets_u = neighbourhood forst u;
                                                    vsets_v = neighbourhood forst v;
                                                    vset_u_new = vset_insert v vsets_u;
                                                    vset_v_new = vset_insert u vsets_v
                                                 in update v vset_v_new (
                                                    update u vset_u_new forst))"
lemmas [code] = neighbourhood_def insert_undirected_edge_def
lemma insert_digraph_abstraction[simp]:
  assumes "adjmap_inv ff " 
          "(\<And> x N. lookup ff x = Some N \<longrightarrow> vset_inv N)"
   shows "digraph_abs (insert_undirected_edge u v ff) =  (digraph_abs ff) \<union> {(u, v), (v, u)}"
  unfolding insert_undirected_edge_def Let_def neighbourhood_def digraph_abs_def
proof(rule, all \<open>rule\<close>,  goal_cases)
  case (1 e)
  then show ?case 
  proof(cases e,  goal_cases)
    case (1 a b)
    then show ?case 
      apply(cases "lookup ff v")
      apply(all \<open>cases "lookup ff a"\<close>)
      apply(all \<open>cases "lookup ff u"\<close>)
      apply(all \<open>cases "a = v"\<close>)
      apply(all \<open>cases "a = u"\<close>)
      by (auto simp add: adjmap.map_update[OF adjmap.invar_update[OF assms(1)]]
                         adjmap.map_update[OF assms(1)] 
                         vset.set.set_isin[OF vset.set.invar_insert[OF vset.set.invar_empty]]
                         vset.set.set_insert[OF vset.set.invar_empty] vset.set.set_empty
                          assms(2) vset.set.invar_insert vset.set.set_insert vset.set.set_isin)     
  qed
next
  case (2 e)
  then show ?case 
  proof(cases e,  goal_cases)
    case (1 a b)
    then show ?case 
      apply(cases "lookup ff v")
      apply(all \<open>cases "lookup ff a"\<close>)
      apply(all \<open>cases "lookup ff u"\<close>)
      apply(all \<open>cases "a = v"\<close>)
      apply(all \<open>cases "a = u"\<close>)
      by (auto simp add: adjmap.map_update[OF adjmap.invar_update[OF assms(1)]]
                         adjmap.map_update[OF assms(1)] 
                         vset.set.set_isin[OF vset.set.invar_insert[OF vset.set.invar_empty]]
                         vset.set.set_insert[OF vset.set.invar_empty] vset.set.set_empty
                          assms(2) vset.set.invar_insert vset.set.set_insert vset.set.set_isin 
                          vset.emptyD(3) vset.set.invar_empty)
  qed
qed

lemma insert_abstraction[simp]:
  assumes "adjmap_inv ff " 
          "(\<And> x N. lookup ff x = Some N \<longrightarrow> vset_inv N)"
    shows "to_graph (insert_undirected_edge u v ff) = insert {u, v} (to_graph ff)"
  by(auto simp add: to_graph'_def insert_digraph_abstraction[OF assms])

lemma insert_abstraction':
  assumes "good_graph_invar ff"
  shows "to_graph (insert_undirected_edge u v ff) = insert {u, v} (to_graph ff)"
  using assms  by (auto elim: good_graph_invarE)

lemma predicate_cong: "a = b \<Longrightarrow> c = d \<Longrightarrow> P a c \<Longrightarrow> P b d"
  by simp

lemma insert_undirected_edge_symmetric:
  assumes "adjmap_inv ff " 
          "(\<And> x N. lookup ff x = Some N \<longrightarrow> vset_inv N)"
          "\<And> x y. (x, y) \<in> digraph_abs ff \<Longrightarrow> (y, x) \<in> digraph_abs ff"
    shows "\<And> x y. (x, y) \<in> digraph_abs (insert_undirected_edge x y ff) 
                   \<Longrightarrow> (y, x) \<in> digraph_abs (insert_undirected_edge x y ff)"
  by (simp add: assms(1,2))

lemma adjmap_inv_pres_insert_undirected_edge:"adjmap_inv ff \<Longrightarrow> adjmap_inv (insert_undirected_edge a b ff)"
  unfolding insert_undirected_edge_def
  by(auto intro: adjmap.invar_update)

lemma insert_undirected_edge_good_graph_invar_pres:
  assumes "good_graph_invar ff" 
  shows "good_graph_invar (insert_undirected_edge a b ff)"
proof(rule  good_graph_invarI, goal_cases)
  case 1
  then show ?case 
    using adjmap_inv_pres_insert_undirected_edge assms good_graph_invar_def by blast
next
  case (2 v N)
  have adjmap_inv: "adjmap_inv ff " 
     and vset_inv: "\<And>v N. lookup ff v = Some N \<Longrightarrow> vset_inv N"
    using good_graph_invarE[OF assms(1)] by auto
  from 2 show ?case
    apply(cases "lookup ff b")
     apply(all \<open>cases "lookup ff a"\<close>)
    apply(all \<open>cases "v = b"\<close>)
    apply(all \<open>cases "v = a"\<close>)
    by(auto simp add: insert_undirected_edge_def neighbourhood_def
            adjmap.map_update[OF adjmap.invar_update[OF adjmap_inv]]
                         adjmap.map_update[OF adjmap_inv] 
                         vset.set.set_isin[OF vset.set.invar_insert[OF vset.set.invar_empty]]
                         vset.set.set_insert[OF vset.set.invar_empty] vset.set.set_empty
                         vset.set.invar_insert vset.set.set_insert vset.set.set_isin 
                         vset.emptyD(3) vset.set.invar_empty
         intro: vset_inv vset.set.invar_insert)
next
  case 3
  have adjmap_inv: "adjmap_inv ff " 
     and vset_inv: "\<And>v N. lookup ff v = Some N \<Longrightarrow> vset_inv N"
       and finite: "finite {v. lookup ff v \<noteq> None}"
    using good_graph_invarE[OF assms(1)] by auto
  have finite_after: "finite {v. v \<noteq> a \<longrightarrow> v \<noteq> b \<longrightarrow> (\<exists>y. lookup ff v = Some y)}"
    using finite by (auto intro: rev_finite_subset[of "{v. lookup ff v \<noteq> None} \<union> {a, b}"])
  from 3 show ?case
    apply(cases "lookup ff b")
    apply(all \<open>cases "lookup ff a"\<close>)
    using  finite_after
    by(auto simp add: insert_undirected_edge_def neighbourhood_def
            adjmap.map_update[OF adjmap.invar_update[OF adjmap_inv]]
                         adjmap.map_update[OF adjmap_inv])
next
  case (4 v N)
  have adjmap_inv: "adjmap_inv ff " 
     and vset_inv: "\<And>v N. lookup ff v = Some N \<Longrightarrow> vset_inv N"
       and finite: "finite {v. lookup ff v \<noteq> None}"
and finite_neighbs: "\<And>v N. lookup ff v = Some N \<Longrightarrow> finite [N]\<^sub>s"
    using good_graph_invarE[OF assms(1)] by auto
  from 4 show ?case 
    apply(cases "lookup ff b")
    apply(all \<open>cases "lookup ff a"\<close>)
    apply(all \<open>cases "v = b"\<close>)
    apply(all \<open>cases "v = a"\<close>)
    by(auto simp add: insert_undirected_edge_def neighbourhood_def
            adjmap.map_update[OF adjmap.invar_update[OF adjmap_inv]]
                         adjmap.map_update[OF adjmap_inv]
           vset.set.invar_empty vset.set.set_empty vset.set.set_insert
           finite_neighbs  vset_inv
            intro:  finite_neighbs)
qed
end

context Map
begin
bundle automation' = map_empty[simp] map_update[simp] map_delete[simp]
                    invar_empty[simp] invar_update[simp] invar_delete[simp]
end 

locale 
algo_spec = 
 alg where fst="fst::'edge \<Rightarrow> 'v" +  

 Set_with_predicate
     where get_from_set = "get_from_set::('edge \<Rightarrow> bool) \<Rightarrow> 'e \<Rightarrow> 'edge option"  +

 adj_map_specs: Adj_Map_Specs2 
     where  update =  "edge_map_update::'v \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'd" +

 flow_map: map_update_all flow_empty "flow_update::'edge \<Rightarrow> real \<Rightarrow> 'f_impl \<Rightarrow> 'f_impl"
                          flow_delete flow_lookup flow_invar flow_update_all+

 bal_map: Map  bal_empty "bal_update:: 'v \<Rightarrow> real \<Rightarrow> 'b_impl \<Rightarrow> 'b_impl" 
               bal_delete bal_lookup bal_invar +

 rep_comp_map: map_update_all rep_comp_empty "rep_comp_update::'v \<Rightarrow> ('v \<times> nat) \<Rightarrow> 'r_comp_impl \<Rightarrow> 'r_comp_impl"
                              rep_comp_delete rep_comp_lookup rep_comp_invar rep_comp_upd_all +

 conv_map: Map  conv_empty "conv_update::('v \<times> 'v) \<Rightarrow> 'edge Redge \<Rightarrow> 'conv_impl \<Rightarrow> 'conv_impl"
                conv_delete conv_lookup conv_invar +

 not_blocked_map: map_update_all  not_blocked_empty "not_blocked_update::'edge \<Rightarrow> bool \<Rightarrow> 'not_blocked_impl\<Rightarrow> 'not_blocked_impl"
                                  not_blocked_delete not_blocked_lookup not_blocked_invar not_blocked_upd_all
for flow_empty 
    flow_update 
    flow_delete 
    flow_lookup 
    flow_invar

    bal_empty 
    bal_update 
    bal_delete 
    bal_lookup 
    bal_invar 

    rep_comp_empty 
    rep_comp_update 
    rep_comp_delete 
    rep_comp_lookup 
    rep_comp_invar 

    conv_empty 
    conv_update 
    conv_delete 
    conv_lookup 
    conv_invar 

    not_blocked_update 
    not_blocked_empty 
    not_blocked_delete 
    not_blocked_lookup 
    not_blocked_invar 

    fst 

    rep_comp_upd_all 
    flow_update_all 
    not_blocked_upd_all 

    get_from_set  +
fixes \<b>::"'v \<Rightarrow> real" and  
      get_max::"('v \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'b_impl \<Rightarrow> real" and 
      \<epsilon>::real and 
      \<E>_impl::'e and 
      empty_forest::"'d" and 
      N::nat
begin

abbreviation "digraph_abs \<equiv> adj_map_specs.digraph_abs"
abbreviation "to_graph \<equiv> adj_map_specs.to_graph"
abbreviation "neighbourhood' \<equiv> adj_map_specs.neighbourhood"
abbreviation "insert_undirected_edge \<equiv> adj_map_specs.insert_undirected_edge"
abbreviation "good_graph_invar \<equiv> adj_map_specs.good_graph_invar"

lemmas in_to_graphE = adj_map_specs.in_to_graphE
lemmas good_graph_invarE=adj_map_specs.good_graph_invarE
lemmas to_graph_def=adj_map_specs.to_graph_def
lemmas good_graph_invar_def=adj_map_specs.good_graph_invar_def
lemmas digraph_abs_def=adj_map_specs.digraph_abs_def
lemmas insert_undirected_edge_def=adj_map_specs.insert_undirected_edge_def
lemmas neighbourhood'_def=adj_map_specs.neighbourhood_def
lemmas good_graph_invarI=adj_map_specs.good_graph_invarI
lemmas to_graph'_def=adj_map_specs.to_graph'_def
lemmas dVs_Vs_same=adj_map_specs.dVs_Vs_same
lemmas insert_abstraction'=adj_map_specs.insert_abstraction'
lemmas insert_undirected_edge_good_graph_invar_pres=
     adj_map_specs.insert_undirected_edge_good_graph_invar_pres

lemmas rep_comp_upd_all = rep_comp_map.update_all
lemmas not_blocked_upd_all = not_blocked_map.update_all
lemmas flow_update_all=flow_map.update_all

abbreviation "abstract_flow_map mp == (abstract_real_map (flow_lookup mp))"

abbreviation "abstract_bal_map mp == (abstract_real_map (bal_lookup mp))"

definition "abstract_conv_map mp = (\<lambda> e. if conv_lookup mp e \<noteq> None 
                                         then the (conv_lookup mp e)
                                         else undefined)"

abbreviation "abstract_not_blocked_map mp \<equiv>
    (abstract_bool_map (not_blocked_lookup mp))"

lemma abstract_not_blocked_map_def: "abstract_not_blocked_map mp =
 (\<lambda> e. if not_blocked_lookup mp e = None then False
                                                 else the (not_blocked_lookup mp e))"
  by(auto simp add: abstract_bool_map_def split: option.split)

abbreviation "not_blocked_dom mp \<equiv> dom (not_blocked_lookup mp)"

lemma in_not_blocked_dom_same_as_lookup:
"e \<in> dom (not_blocked_lookup mp) \<Longrightarrow> abstract_not_blocked_map mp e = the (not_blocked_lookup mp e)"
  by(auto simp add: abstract_not_blocked_map_def)

definition "abstract_rep_map mp = (\<lambda> x. if rep_comp_lookup mp x \<noteq> None 
                                         then prod.fst (the (rep_comp_lookup mp x))
                                         else  x)"

definition "abstract_comp_map mp = (\<lambda> x. if rep_comp_lookup mp x \<noteq> None 
                                         then prod.snd (the (rep_comp_lookup mp x))
                                         else  1)"

definition "move_balance b x y = (let bx = abstract_bal_map  b x;
                                      by = abstract_bal_map b y in
                                          (bal_update x 0 (bal_update y (bx + by) b)))"


fun augment_edge_impl::"'f_impl \<Rightarrow> real \<Rightarrow>'edge Redge \<Rightarrow> 'f_impl" where
"augment_edge_impl f \<gamma> e = 
  ((case e of F e \<Rightarrow> flow_update e ((abstract_flow_map  f e) + \<gamma>) f |
              B e \<Rightarrow> flow_update e ((abstract_flow_map f e) - \<gamma>) f))"
   
fun augment_edges_impl::"'f_impl\<Rightarrow> real \<Rightarrow>('edge Redge) list \<Rightarrow> 'f_impl" where
"augment_edges_impl f \<gamma> [] = f"|
"augment_edges_impl f \<gamma> (e#es) = augment_edge_impl (augment_edges_impl f \<gamma> es) \<gamma> e"

definition "add_direction to_rdg x y e= 
          (conv_update (x, y) (F e) (conv_update (y, x) (B e) to_rdg))"

definition "move b \<gamma> x y = (let bx = abstract_bal_map b x;
                                by = abstract_bal_map b y in
                           (bal_update x (bx - \<gamma>) (bal_update y (by + \<gamma>) b)))"

abbreviation "flow_domain edg_mp \<equiv> dom( flow_lookup edg_mp)"
abbreviation "rep_comp_domain edg_mp \<equiv> dom (rep_comp_lookup edg_mp)"
abbreviation "bal_domain edg_mp \<equiv> dom (bal_lookup edg_mp)"
abbreviation "conv_domain edg_mp \<equiv> dom (conv_lookup edg_mp)"


fun to_redge_path where
"to_redge_path to_rdg [u,v] = [abstract_conv_map to_rdg (u,v)]"|
"to_redge_path to_rdg (u#v#vs) = ((abstract_conv_map to_rdg (u,v)) # to_redge_path to_rdg (v#vs))"|
"to_redge_path  _ _ = []"

definition "\<F> (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state)
     \<equiv>  oedge ` ((abstract_conv_map (conv_to_rdg state)) ` (digraph_abs (\<FF> state)))"

definition "\<F>_redges (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state)
     \<equiv> (abstract_conv_map (conv_to_rdg state)) ` (digraph_abs (\<FF> state))"
lemmas F_def = \<F>_def
lemmas F_redges_def = \<F>_redges_def

lemma update_gamma_same_F:
  "\<F> (state \<lparr> current_\<gamma> := gamma \<rparr>) = \<F> state"
  "\<F>_redges (state \<lparr> current_\<gamma> := gamma \<rparr>) = \<F>_redges state"
  by(auto simp add: \<F>_def \<F>_redges_def)

definition "implementation_invar (state_impl::
       ('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
           ( \<E> = flow_domain (current_flow state_impl)
          \<and> flow_invar (current_flow state_impl) 
          \<and> \<V> = bal_domain (balance state_impl)
          \<and> bal_invar (balance state_impl)
          \<and> digraph_abs (\<FF> state_impl) = conv_domain (conv_to_rdg state_impl)
          \<and> conv_invar (conv_to_rdg state_impl)
          \<and> \<V> = rep_comp_domain (rep_comp_card state_impl)
          \<and> rep_comp_invar (rep_comp_card state_impl)
          \<and> not_blocked_invar (not_blocked state_impl)
          \<and> \<E> = not_blocked_dom (not_blocked state_impl))"

lemma implementation_invarI[simp]:
  "\<lbrakk>\<E> = flow_domain (current_flow state_impl);
    flow_invar (current_flow state_impl); 
    \<V> = bal_domain (balance state_impl);
    bal_invar (balance state_impl);
    digraph_abs (\<FF> state_impl) = conv_domain (conv_to_rdg state_impl);
    conv_invar (conv_to_rdg state_impl);
    \<V> = rep_comp_domain (rep_comp_card state_impl);
    rep_comp_invar (rep_comp_card state_impl);
    not_blocked_invar (not_blocked state_impl);
    \<E>  = not_blocked_dom (not_blocked state_impl)\<rbrakk>
   \<Longrightarrow> implementation_invar state_impl"
  unfolding implementation_invar_def by simp

lemma implementation_invarE[simp, elim]:
  "implementation_invar state_impl \<Longrightarrow>
     (\<lbrakk>\<E> = flow_domain (current_flow state_impl);
       flow_invar (current_flow state_impl); 
       \<V> = bal_domain (balance state_impl);
       bal_invar (balance state_impl);
       digraph_abs (\<FF> state_impl) = conv_domain (conv_to_rdg state_impl);
       conv_invar (conv_to_rdg state_impl);
       \<V>  = rep_comp_domain (rep_comp_card state_impl);
       rep_comp_invar (rep_comp_card state_impl);
       not_blocked_invar (not_blocked state_impl);
       \<E>  = not_blocked_dom (not_blocked state_impl)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding implementation_invar_def by auto

lemma implementation_invar_partialE:
  "implementation_invar state_impl \<Longrightarrow>(\<E>  = flow_domain (current_flow state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
  "implementation_invar state_impl \<Longrightarrow>(flow_invar (current_flow state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
  "implementation_invar state_impl \<Longrightarrow>(\<V>  = bal_domain (balance state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
  "implementation_invar state_impl \<Longrightarrow>(bal_invar (balance state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
  "implementation_invar state_impl \<Longrightarrow>(digraph_abs (\<FF> state_impl) =
                     conv_domain (conv_to_rdg state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
  "implementation_invar state_impl \<Longrightarrow> (conv_invar (conv_to_rdg state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
  "implementation_invar state_impl \<Longrightarrow> (\<V>  = rep_comp_domain (rep_comp_card state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
  "implementation_invar state_impl \<Longrightarrow> (rep_comp_invar (rep_comp_card state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
  "implementation_invar state_impl \<Longrightarrow> (not_blocked_invar (not_blocked state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
  "implementation_invar state_impl \<Longrightarrow> (\<E>  = not_blocked_dom (not_blocked state_impl) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding implementation_invar_def by auto

lemma implementation_invar_partial_props:
  "implementation_invar state_impl \<Longrightarrow>\<E> = flow_domain (current_flow state_impl)"
  "implementation_invar state_impl \<Longrightarrow>flow_invar (current_flow state_impl)"
  "implementation_invar state_impl \<Longrightarrow>\<V> =bal_domain (balance state_impl)"
  "implementation_invar state_impl \<Longrightarrow>bal_invar (balance state_impl)"
  "implementation_invar state_impl \<Longrightarrow>digraph_abs (\<FF> state_impl) =
                     conv_domain (conv_to_rdg state_impl)"
  "implementation_invar state_impl \<Longrightarrow> conv_invar (conv_to_rdg state_impl)"
  "implementation_invar state_impl \<Longrightarrow> \<V>  = rep_comp_domain (rep_comp_card state_impl)"
  "implementation_invar state_impl \<Longrightarrow> rep_comp_invar (rep_comp_card state_impl)"
  "implementation_invar state_impl \<Longrightarrow> not_blocked_invar (not_blocked state_impl)"
  "implementation_invar state_impl \<Longrightarrow> \<E>  = not_blocked_dom (not_blocked state_impl)"
  unfolding implementation_invar_def by auto

lemma implementation_invar_gamm_upd:
  "implementation_invar state_impl  \<Longrightarrow> implementation_invar (state_impl\<lparr> current_\<gamma> := gamma \<rparr>)"
  by(unfold implementation_invar_def) auto

definition "validF (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state)
                 = graph_invar (to_graph (\<FF> state))"

lemma validFE: "validF state \<Longrightarrow> (graph_invar (to_graph (\<FF> state)) \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: validF_def)
lemma validFI: "graph_invar (to_graph (\<FF> state)) \<Longrightarrow> validF state"
  by(auto simp add: validF_def)
lemma validFD: "validF state \<Longrightarrow> graph_invar (to_graph (\<FF> state))"
  by(auto simp add: validF_def)

definition "inv_actives_in_E (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state)
             = (to_set (actives state) \<subseteq> \<E>)"

lemma inv_actives_in_EI: "to_set (actives state) \<subseteq> \<E> \<Longrightarrow> inv_actives_in_E state"
  unfolding inv_actives_in_E_def by auto

lemma inv_actives_in_EE: 
  "\<lbrakk>inv_actives_in_E state; (to_set (actives state) \<subseteq> \<E> \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  unfolding inv_actives_in_E_def by auto

definition "inv_digraph_abs_F_in_E (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state)
        = (((abstract_conv_map (conv_to_rdg state)) ` (digraph_abs (\<FF> state))) \<subseteq> \<EE>)"

lemma inv_digraph_abs_F_in_EI: "((abstract_conv_map (conv_to_rdg state)) ` (digraph_abs (\<FF> state))) \<subseteq> \<EE> \<Longrightarrow> inv_digraph_abs_F_in_E state"
  unfolding inv_digraph_abs_F_in_E_def by auto

lemma inv_digraph_abs_F_in_EE: "inv_digraph_abs_F_in_E state \<Longrightarrow>
  ((abstract_conv_map (conv_to_rdg state)) ` (digraph_abs (\<FF> state)) \<subseteq> \<EE>\<Longrightarrow> P) \<Longrightarrow> P"
  unfolding inv_digraph_abs_F_in_E_def by auto

definition "inv_forest_in_E (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =( \<F> state \<subseteq> \<E>)"

lemma inv_forest_in_EI: "\<F> state \<subseteq> \<E>\<Longrightarrow> inv_forest_in_E state"
  unfolding inv_forest_in_E_def by auto

lemma inv_forest_in_EE: "inv_forest_in_E state \<Longrightarrow> (\<F> state \<subseteq> \<E> \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding inv_forest_in_E_def by auto

definition "inv_forest_actives_disjoint (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state)
            =( \<F> state \<inter> to_set (actives state) = {})"

lemma inv_forest_actives_disjointI: "\<F> state \<inter> to_set (actives state) = {} \<Longrightarrow> inv_forest_actives_disjoint state"
  unfolding inv_forest_actives_disjoint_def by auto

lemma inv_forest_actives_disjointE: 
  "inv_forest_actives_disjoint state \<Longrightarrow> (\<F> state \<inter> to_set (actives state) = {} \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding inv_forest_actives_disjoint_def by auto

definition "inv_finite_forest (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state)
                 = finite (to_graph (\<FF> state))"

lemma inv_finite_forestI: "finite (to_graph (\<FF> state)) \<Longrightarrow> inv_finite_forest state"
  unfolding inv_finite_forest_def by auto

lemma inv_finite_forestE: 
  "\<lbrakk>inv_finite_forest state; (finite (to_graph (\<FF> state)) \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  unfolding inv_finite_forest_def by auto

abbreviation "a_conv_to_rdg state \<equiv> (\<lambda> e. (abstract_conv_map (conv_to_rdg state)) e)"

definition "inv_conversion_consistent (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state)
                = consist  (digraph_abs (\<FF> state)) (abstract_conv_map (conv_to_rdg state))"

lemma inv_conversion_consistentI: 
  assumes "(\<And> x y. (x, y) \<in> (digraph_abs (\<FF> state)) \<Longrightarrow>
              \<exists>e. (abstract_conv_map (conv_to_rdg state)) (x, y) = F e 
           \<and> make_pair e = (x, y) \<or>
           (abstract_conv_map (conv_to_rdg state)) (x, y) = B e \<and> make_pair e = (y, x))"
  and  "(\<And> x y e. \<lbrakk>(x, y) \<in> (digraph_abs (\<FF> state)); x \<noteq> y\<rbrakk>  \<Longrightarrow>  
          ((abstract_conv_map (conv_to_rdg state)) (x, y) = F e) =
          ((abstract_conv_map (conv_to_rdg state)) (y, x) = B e))" 
 shows "inv_conversion_consistent state"
  using assms by(auto simp add: inv_conversion_consistent_def consist_def)

lemma inv_conversion_consistentE: 
 "\<lbrakk>inv_conversion_consistent state; to_rdg = abstract_conv_map (conv_to_rdg state);
  ((\<And> x y. (x, y) \<in> (digraph_abs (\<FF> state)) \<Longrightarrow> \<exists> e. (to_rdg (x,y) = F e \<and> make_pair e = (x,y) \<or>
                                     to_rdg (x,y) = B e  \<and> make_pair e = (y,x)))  \<Longrightarrow>
     (\<And> x y e. \<lbrakk>(x, y) \<in> (digraph_abs (\<FF> state)); x \<noteq> y\<rbrakk> \<Longrightarrow> (to_rdg (x,y) = F e \<longleftrightarrow>
                                     to_rdg (y,x) = B e)) \<Longrightarrow> P)\<rbrakk>
   \<Longrightarrow> P"
  by(force simp add: inv_conversion_consistent_def consist_def)

lemma inv_conversion_consistentI'': 
 " consist  (digraph_abs (\<FF> state)) (abstract_conv_map (conv_to_rdg state))
                    \<Longrightarrow> inv_conversion_consistent state"
  by(auto simp add: inv_conversion_consistent_def)

lemma inv_conversion_consistentE'':
 "\<lbrakk>inv_conversion_consistent state;
   (consist  (digraph_abs (\<FF> state)) (abstract_conv_map (conv_to_rdg state)) \<Longrightarrow> P)\<rbrakk>
  \<Longrightarrow> P"
  by(auto simp add: inv_conversion_consistent_def)

abbreviation "representative state ==
 (\<lambda> u.  (abstract_rep_map (rep_comp_card state) u))"

definition "inv_reachable_same_rep (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state)
                  = (\<forall> u v. reachable (to_graph (\<FF> state)) u v \<longrightarrow>
                      (representative state) u =
                                       (representative state) v)"

lemma inv_reachable_same_repI: 
"(\<And>u v. reachable (to_graph (\<FF> state)) u v \<Longrightarrow>(representative state) u = (representative state) v) 
 \<Longrightarrow> inv_reachable_same_rep state"
  unfolding inv_reachable_same_rep_def by simp

lemma inv_reachable_same_repE: 
 "\<lbrakk>inv_reachable_same_rep state;
   ((\<And>u v. reachable (to_graph (\<FF> state)) u v \<Longrightarrow> 
                     (representative state) u = (representative state) v) \<Longrightarrow> P)\<rbrakk>
   \<Longrightarrow> P"
  unfolding inv_reachable_same_rep_def by simp

lemma inv_reachable_same_repD: 
 "\<lbrakk>inv_reachable_same_rep state; reachable (to_graph (\<FF> state)) u v\<rbrakk>
   \<Longrightarrow> (representative state) u = (representative state) v"
  unfolding inv_reachable_same_rep_def by simp

definition "inv_rep_reachable (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
                  (\<forall> v. reachable (to_graph (\<FF> state)) v ((representative state) v) \<or> 
                                                           v = (representative state) v)"

lemma inv_rep_reachableI: 
  "(\<And> v. reachable (to_graph (\<FF> state)) v ((representative state) v) \<or> 
                                                           v = (representative state) v)
  \<Longrightarrow> inv_rep_reachable state"
  unfolding inv_rep_reachable_def by auto

lemma inv_rep_reachableE: 
 "\<lbrakk>inv_rep_reachable state;
   ((\<And> v. reachable (to_graph (\<FF> state)) v ((representative state) v) \<or> 
                                                           v = (representative state) v)
   \<Longrightarrow> P)\<rbrakk>
  \<Longrightarrow>P"
  unfolding inv_rep_reachable_def by auto

lemma inv_rep_reachableD: "inv_rep_reachable state \<Longrightarrow> 
       reachable (to_graph (\<FF> state)) v ((representative state) v) \<or> 
       v = (representative state) v"
  unfolding inv_rep_reachable_def by auto

definition "inv_reps_in_V (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
  (\<forall> v \<in> \<V>. representative state v \<in> \<V>)"

lemma inv_reps_in_VI: 
  "(\<And>v. v \<in> \<V> \<Longrightarrow> representative state v \<in> \<V>) \<Longrightarrow> inv_reps_in_V state"
  unfolding inv_reps_in_V_def by auto

lemma inv_reps_in_VE: 
 "\<lbrakk>inv_reps_in_V state; ((\<And>v. v \<in> \<V> \<Longrightarrow> representative state v \<in> \<V> ) \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  unfolding inv_reps_in_V_def by auto

lemma inv_reps_in_VD: 
  "\<lbrakk>inv_reps_in_V state; v \<in> \<V>\<rbrakk> \<Longrightarrow> representative state v \<in> \<V>"
  unfolding inv_reps_in_V_def by auto

definition "inv_components_in_V (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
                    (\<forall> v \<in> \<V>. connected_component (to_graph (\<FF> state)) v \<subseteq> \<V>)"

lemma inv_components_in_VI:
 "(\<And>v. v \<in> \<V> \<Longrightarrow> connected_component (to_graph (\<FF> state)) v \<subseteq> \<V>) \<Longrightarrow> inv_components_in_V state"
  unfolding inv_components_in_V_def by auto

lemma inv_components_in_VE: 
 "\<lbrakk>inv_components_in_V state;
   ((\<And>v. v \<in> \<V> \<Longrightarrow>  connected_component (to_graph (\<FF> state)) v \<subseteq> \<V>) \<Longrightarrow> P)\<rbrakk>
  \<Longrightarrow> P"
  unfolding inv_components_in_V_def by auto

lemma inv_components_in_VD: 
 "\<lbrakk>inv_components_in_V state; v \<in> \<V>\<rbrakk> \<Longrightarrow> connected_component (to_graph (\<FF> state)) v \<subseteq> \<V>"
  unfolding inv_components_in_V_def by auto

definition "inv_active_different_comps (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
     (\<forall> e \<in> to_set (actives state). connected_component (to_graph (\<FF> state)) (fst e) \<noteq>
                                     connected_component (to_graph (\<FF> state)) (snd e))"

lemma inv_active_different_compsI: 
 "(\<And> e. e \<in> to_set (actives state) \<Longrightarrow> connected_component (to_graph (\<FF> state)) (fst e) \<noteq>
                                     connected_component (to_graph (\<FF> state)) (snd e)) 
  \<Longrightarrow> inv_active_different_comps state"
  unfolding inv_active_different_comps_def by simp

lemma inv_active_different_compsE: 
 "\<lbrakk>inv_active_different_comps state;
   ((\<And> e. e \<in> to_set (actives state) \<Longrightarrow> connected_component (to_graph (\<FF> state)) (fst e) \<noteq>
           connected_component (to_graph (\<FF> state)) (snd e)) \<Longrightarrow> P)\<rbrakk>
   \<Longrightarrow> P"
  unfolding inv_active_different_comps_def 
  by blast


definition "inv_pos_bal_rep (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
          (\<forall> v \<in> \<V>. (abstract_real_map (bal_lookup (balance state)) v \<noteq> 0 
               \<longrightarrow> representative state v = v))"

lemma inv_pos_bal_repE:
  "\<lbrakk>inv_pos_bal_rep state ;
    ((\<And> v.  \<lbrakk>v \<in> \<V>; abstract_real_map (bal_lookup (balance state)) v \<noteq> 0\<rbrakk> 
        \<Longrightarrow> representative state v = v) \<Longrightarrow> P)\<rbrakk>
   \<Longrightarrow>P"
  unfolding inv_pos_bal_rep_def by simp

lemma inv_pos_bal_repI:
"(\<And> v.  \<lbrakk>v \<in> \<V>; abstract_real_map (bal_lookup (balance state)) v \<noteq> 0\<rbrakk>\<Longrightarrow>
       representative state v = v) 
  \<Longrightarrow> inv_pos_bal_rep state"
  unfolding inv_pos_bal_rep_def by simp

definition "inv_inactive_same_component (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) = 
               (\<forall>  e \<in> \<E> - to_set (actives state). connected_component (to_graph (\<FF> state)) (fst e) =
                                          connected_component (to_graph (\<FF> state)) (snd e))"

lemma inv_inactive_same_componentI: 
 "(\<And> e. e \<in> \<E> - to_set (actives state) \<Longrightarrow> connected_component (to_graph (\<FF> state)) (fst e) =
                                     connected_component (to_graph (\<FF> state)) (snd e)) 
 \<Longrightarrow> inv_inactive_same_component state"
  unfolding inv_inactive_same_component_def by simp

lemma inv_inactive_same_componentE: 
 "\<lbrakk>inv_inactive_same_component state;
   ((\<And> e. e \<in> \<E> - to_set (actives state) \<Longrightarrow> connected_component (to_graph (\<FF> state)) (fst e) =
             connected_component (to_graph (\<FF> state)) (snd e)) \<Longrightarrow> P)\<rbrakk>
  \<Longrightarrow> P"
  unfolding inv_inactive_same_component_def by simp

definition "inv_dbltn_graph_forest (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) = (validF state)"

lemma inv_dbltn_graph_forestE: 
  "\<lbrakk>inv_dbltn_graph_forest state; (validF state \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  using inv_dbltn_graph_forest_def by auto

lemma inv_dbltn_graph_forestI: "validF state \<Longrightarrow> inv_dbltn_graph_forest state"
  using inv_dbltn_graph_forest_def by auto

definition "inv_forest_in_V (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
                ( Vs (to_graph (\<FF> state)) \<subseteq> \<V>)"

lemma inv_forest_in_VE: 
 "\<lbrakk>inv_forest_in_V state; (Vs (to_graph (\<FF> state)) \<subseteq> \<V>\<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  using inv_forest_in_V_def by auto

lemma inv_forest_in_VI: 
  "Vs (to_graph (\<FF> state)) \<subseteq> \<V>\<Longrightarrow> inv_forest_in_V state"
  using inv_forest_in_V_def by auto

abbreviation "comp_card state ==
 (\<lambda> u.  (abstract_comp_map (rep_comp_card state) u))"

definition "inv_comp_card_correct (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
        (\<forall> x \<in> \<V>. comp_card state x = 
                       card (connected_component (to_graph (\<FF> state)) x))"

lemma inv_comp_card_correctE: 
  "\<lbrakk>inv_comp_card_correct state;
     ((\<And> x. x \<in> \<V> \<Longrightarrow> comp_card state x = 
                       card (connected_component (to_graph (\<FF> state)) x)) \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  using inv_comp_card_correct_def by auto

lemma inv_comp_card_correctD: 
  "\<lbrakk>inv_comp_card_correct state; x \<in> \<V>\<rbrakk> 
   \<Longrightarrow> comp_card state x = card (connected_component (to_graph (\<FF> state)) x)"
  using inv_comp_card_correct_def by auto

lemma inv_comp_card_correctI: 
  "(\<And> x. x \<in> \<V> \<Longrightarrow> comp_card state x =  card (connected_component (to_graph (\<FF> state)) x)) 
   \<Longrightarrow> inv_comp_card_correct state"
  using inv_comp_card_correct_def by auto

definition "inv_set_invar_actives (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state)
           = set_invar (actives state)"

lemma inv_set_invar_activesE: 
 "\<lbrakk>inv_set_invar_actives state; (set_invar (actives state) \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  using inv_set_invar_actives_def by auto

lemma inv_set_invar_activesI: 
  "(set_invar (actives state)) \<Longrightarrow> inv_set_invar_actives state"
  unfolding inv_set_invar_actives_def by simp

definition "inv_forest_good_graph (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
               good_graph_invar (\<FF> state)"

lemma inv_forest_good_graphE: 
"\<lbrakk>inv_forest_good_graph state;
   (\<lbrakk>adjmap_inv (\<FF> state);
     (\<And>v N. lookup (\<FF> state) v = Some N \<Longrightarrow> vset_inv N);
      finite {v. (lookup (\<FF> state) v) \<noteq> None};
     (\<And> v N. (lookup (\<FF> state) v) = Some N \<longrightarrow> finite (t_set N))\<rbrakk> 
    \<Longrightarrow> P)\<rbrakk> 
   \<Longrightarrow> P"
  using inv_forest_good_graph_def by (force elim!: good_graph_invarE)

lemma inv_forest_good_graphI: 
 "\<lbrakk>adjmap_inv (\<FF> state);
  (\<And>v N. lookup (\<FF> state) v = Some N \<Longrightarrow> vset_inv N);
   finite {v. (lookup (\<FF> state) v) \<noteq> None};
  (\<And> v N. (lookup (\<FF> state) v) = Some N \<longrightarrow> finite (t_set N))\<rbrakk>
  \<Longrightarrow> inv_forest_good_graph state "
  by(auto simp add: inv_forest_good_graph_def  good_graph_invar_def)

lemma inv_forest_good_graphE'': 
 "\<lbrakk>inv_forest_good_graph  state; (good_graph_invar (\<FF> state) \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  by(auto simp add: inv_forest_good_graph_def)
lemma inv_forest_good_graphI'': 
  "good_graph_invar (\<FF> state) \<Longrightarrow> inv_forest_good_graph  state"
  by(auto simp add: inv_forest_good_graph_def)
lemma inv_forest_good_graphD'': 
  "inv_forest_good_graph  state \<Longrightarrow> good_graph_invar (\<FF> state)"
  by(auto simp add: inv_forest_good_graph_def)

definition "inv_digraph_abs_\<FF>_sym (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state)
             = symmetric_digraph (digraph_abs (\<FF> state))"

lemma inv_digraph_abs_\<FF>_symE: 
 "\<lbrakk>inv_digraph_abs_\<FF>_sym state; (symmetric_digraph (digraph_abs (\<FF> state)) \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  using inv_digraph_abs_\<FF>_sym_def by auto

lemma inv_digraph_abs_\<FF>_symI: 
  "symmetric_digraph (digraph_abs (\<FF> state)) \<Longrightarrow> inv_digraph_abs_\<FF>_sym state"
  using inv_digraph_abs_\<FF>_sym_def by auto

lemma inv_digraph_abs_\<FF>_sym_applied: 
  "inv_digraph_abs_\<FF>_sym state \<Longrightarrow> symmetric_digraph (digraph_abs (\<FF> state))"
  by(auto elim!: inv_digraph_abs_\<FF>_symE in_to_graphE)

lemma inv_digraph_abs_\<FF>_symE': "inv_digraph_abs_\<FF>_sym state \<Longrightarrow>
 ((\<And> u v. (u, v) \<in> digraph_abs (\<FF> state) \<Longrightarrow> (v, u) \<in> digraph_abs (\<FF> state)) \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: inv_digraph_abs_\<FF>_sym_def symmetric_digraph_def)

lemma inv_digraph_abs_\<FF>_symI': 
  "(\<And> u v. (u, v) \<in> digraph_abs (\<FF> state) \<Longrightarrow> (v, u) \<in> digraph_abs (\<FF> state)) 
  \<Longrightarrow> inv_digraph_abs_\<FF>_sym state"
  by(auto simp add: inv_digraph_abs_\<FF>_sym_def symmetric_digraph_def)

lemma inv_digraph_abs_\<FF>_sym_applied': 
  "\<lbrakk>inv_digraph_abs_\<FF>_sym state; {u, v} \<in> to_graph (\<FF> state)\<rbrakk> \<Longrightarrow> (u, v) \<in> digraph_abs (\<FF> state)"
  by(auto simp add: inv_digraph_abs_\<FF>_sym_def to_graph_def intro!: in_UD_symD)

abbreviation "a_not_blocked (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state)
               == (\<lambda> e. (abstract_not_blocked_map (not_blocked state) e))"

definition "inv_unbl_iff_forest_active (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
      (\<forall> e. a_not_blocked state e \<longleftrightarrow> e \<in> \<F> state \<union> to_set (actives state))"

lemma inv_unbl_iff_forest_activeE: 
  "\<lbrakk>inv_unbl_iff_forest_active state;
     ((\<And> e. a_not_blocked state e \<longleftrightarrow> e \<in> \<F> state \<union> to_set (actives state)) \<Longrightarrow> P)\<rbrakk>
    \<Longrightarrow> P"
  using inv_unbl_iff_forest_active_def by auto

lemma inv_unbl_iff_forest_activeI: 
  "(\<And> e. a_not_blocked state e \<longleftrightarrow> e \<in> \<F> state \<union> to_set (actives state))
  \<Longrightarrow> inv_unbl_iff_forest_active state"
  using inv_unbl_iff_forest_active_def by auto

lemma inv_unbl_iff_forest_activeD: 
  "inv_unbl_iff_forest_active state 
   \<Longrightarrow> a_not_blocked state e \<longleftrightarrow> e \<in> \<F> state \<union> to_set (actives state)"
  using inv_unbl_iff_forest_active_def by auto

definition "underlying_invars (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
           (inv_actives_in_E state
                              \<and> inv_digraph_abs_F_in_E state \<and> inv_forest_in_E state \<and> inv_forest_actives_disjoint state
                              \<and> inv_conversion_consistent state \<and> inv_rep_reachable state \<and>
                              inv_reachable_same_rep state \<and> inv_reps_in_V state \<and> inv_finite_forest state
                              \<and> inv_components_in_V state \<and> inv_active_different_comps state \<and> inv_pos_bal_rep state \<and>
                              inv_inactive_same_component state \<and> inv_dbltn_graph_forest state \<and> inv_forest_in_V state \<and> inv_comp_card_correct state
                              \<and> inv_set_invar_actives state \<and> inv_forest_good_graph state \<and>  inv_digraph_abs_\<FF>_sym state \<and>
                               inv_unbl_iff_forest_active state)"

lemma underlying_invarsI: 
 "\<lbrakk>inv_actives_in_E state; inv_digraph_abs_F_in_E state; inv_forest_in_E state; 
   inv_forest_actives_disjoint state; inv_conversion_consistent state; inv_rep_reachable state;
   inv_reachable_same_rep state; inv_reps_in_V state; inv_finite_forest state; 
   inv_components_in_V state; inv_active_different_comps state; inv_pos_bal_rep state;
   inv_inactive_same_component state; inv_dbltn_graph_forest state; inv_forest_in_V state;
   inv_comp_card_correct state; inv_set_invar_actives state; inv_forest_good_graph state;
   inv_digraph_abs_\<FF>_sym state; inv_unbl_iff_forest_active state\<rbrakk>
   \<Longrightarrow>  underlying_invars state"
  unfolding underlying_invars_def by simp

lemma underlying_invarsE: 
 "underlying_invars state \<Longrightarrow>
 (\<lbrakk>inv_actives_in_E state; inv_digraph_abs_F_in_E state; inv_forest_in_E state;
   inv_forest_actives_disjoint state; inv_conversion_consistent state; inv_rep_reachable state;
   inv_reachable_same_rep state; inv_reps_in_V state; inv_finite_forest state; 
   inv_components_in_V state; inv_active_different_comps state; inv_pos_bal_rep state;
   inv_inactive_same_component state; inv_dbltn_graph_forest state; inv_forest_in_V state;
   inv_comp_card_correct state; inv_set_invar_actives state; inv_forest_good_graph state;
   inv_digraph_abs_\<FF>_sym state; inv_unbl_iff_forest_active state\<rbrakk>
   \<Longrightarrow> P)
  \<Longrightarrow> P"
  unfolding underlying_invars_def by simp

lemma not_in_E_blocked:
  "\<lbrakk>underlying_invars state; e \<notin> \<E>\<rbrakk> \<Longrightarrow> \<not> a_not_blocked state e"
  unfolding  underlying_invars_def inv_unbl_iff_forest_active_def inv_actives_in_E_def inv_forest_in_E_def by blast

named_theorems from_underlying_invars

lemma inv_actives_in_E_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_actives_in_E state"
  unfolding underlying_invars_def by simp
lemma inv_digraph_abs_F_in_E_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_digraph_abs_F_in_E state"
  unfolding underlying_invars_def by simp
lemma inv_forest_in_E_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_forest_in_E state"
  unfolding underlying_invars_def by simp
lemma inv_forest_actives_disjoint_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_forest_actives_disjoint state"
  unfolding underlying_invars_def by simp
lemma inv_finite_forest_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_finite_forest state"
  unfolding underlying_invars_def by simp
lemma inv_conversion_consistent_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_conversion_consistent state"
  unfolding underlying_invars_def by simp
lemma inv_reachable_same_rep_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_reachable_same_rep state"
  unfolding underlying_invars_def by simp
lemma inv_rep_reachable_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_rep_reachable state"
  unfolding underlying_invars_def by simp
lemma inv_reps_in_V_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_reps_in_V state"
  unfolding underlying_invars_def by simp
lemma inv_components_in_V_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_components_in_V state"
  unfolding underlying_invars_def by simp
lemma inv_active_different_comps_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_active_different_comps state"
  unfolding underlying_invars_def by simp
lemma inv_pos_bal_rep_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_pos_bal_rep state"
  unfolding underlying_invars_def by simp
lemma inv_inactive_same_component_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_inactive_same_component state"
  unfolding underlying_invars_def by simp
lemma inv_dbltn_graph_forest_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_dbltn_graph_forest state"
  unfolding underlying_invars_def by simp
lemma inv_forest_in_V_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_forest_in_V state"
  unfolding underlying_invars_def by simp
lemma inv_comp_card_correct_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_comp_card_correct state"
  unfolding underlying_invars_def by simp
lemma inv_set_invar_actives_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_set_invar_actives state"
  unfolding underlying_invars_def by simp
lemma inv_forest_good_graph_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_forest_good_graph state"
  unfolding underlying_invars_def by simp
lemma inv_digraph_abs_\<FF>_sym_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_digraph_abs_\<FF>_sym state"
  unfolding underlying_invars_def by simp
lemma inv_unbl_iff_forest_active_from_underlying_invars[from_underlying_invars]: 
"underlying_invars state \<Longrightarrow> inv_unbl_iff_forest_active state"
  unfolding underlying_invars_def by simp

lemmas from_underlying_invars'= from_underlying_invars[simplified inv_actives_in_E_def inv_digraph_abs_F_in_E_def inv_forest_in_E_def 
                        inv_forest_actives_disjoint_def inv_finite_forest_def inv_conversion_consistent_def inv_reachable_same_rep_def inv_rep_reachable_def
                        inv_reps_in_V_def inv_components_in_V_def inv_active_different_comps_def inv_pos_bal_rep_def inv_inactive_same_component_def
                        inv_dbltn_graph_forest_def inv_forest_in_V_def inv_comp_card_correct_def inv_set_invar_actives_def inv_forest_good_graph_def
                        inv_digraph_abs_\<FF>_sym_def inv_unbl_iff_forest_active_def]

lemmas invar_auxE = inv_actives_in_EE inv_digraph_abs_F_in_EE inv_forest_in_EE inv_forest_actives_disjointE inv_finite_forestE
                    inv_conversion_consistentE inv_reachable_same_repE inv_rep_reachableE inv_reps_in_VE inv_components_in_VE
                    inv_active_different_compsE inv_pos_bal_repE inv_inactive_same_componentE inv_dbltn_graph_forestE inv_forest_in_VE
                    inv_comp_card_correctE inv_set_invar_activesE inv_forest_good_graphE inv_digraph_abs_\<FF>_symE
                     inv_unbl_iff_forest_activeE


lemmas inv_actives_in_EI' = inv_actives_in_EE[OF _  inv_actives_in_EI]
lemmas inv_digraph_abs_F_in_EI' = inv_digraph_abs_F_in_EE[OF _  inv_digraph_abs_F_in_EI]
lemmas inv_forest_in_EI' = inv_forest_in_EE[OF _  inv_forest_in_EI]
lemmas inv_forest_actives_disjointI' = inv_forest_actives_disjointE[OF _  inv_forest_actives_disjointI]
lemmas inv_finite_forestI' = inv_finite_forestE[OF _  inv_finite_forestI]
lemmas inv_conversion_consistentI' = inv_conversion_consistentE[OF _  _ inv_conversion_consistentI]
lemmas inv_reachable_same_repI' = inv_reachable_same_repE[OF _  inv_reachable_same_repI]
lemmas inv_rep_reachableI' = inv_rep_reachableE[OF _  inv_rep_reachableI]
lemmas inv_reps_in_VI' = inv_reps_in_VE[OF _  inv_reps_in_VI]
lemmas inv_components_in_VI' = inv_components_in_VE[OF _  inv_components_in_VI]
lemmas inv_active_different_compsI' = inv_active_different_compsE[OF _  inv_active_different_compsI]
lemmas inv_pos_bal_repI' = inv_pos_bal_repE[OF _  inv_pos_bal_repI]
lemmas inv_inactive_same_componentI' = inv_inactive_same_componentE[OF _  inv_inactive_same_componentI]
lemmas inv_dbltn_graph_forestI' = inv_dbltn_graph_forestE[OF _  inv_dbltn_graph_forestI]
lemmas inv_forest_in_VI' = inv_forest_in_VE[OF _  inv_forest_in_VI]
lemmas inv_comp_card_correctI' = inv_comp_card_correctE[OF _  inv_comp_card_correctI]
lemmas inv_set_invar_activesI' = inv_set_invar_activesE[OF _  inv_set_invar_activesI]
lemmas inv_forest_good_graphI' = inv_forest_good_graphE[OF _  inv_forest_good_graphI]
lemmas inv_unbl_iff_forest_activeI' = inv_unbl_iff_forest_activeE[OF _  inv_unbl_iff_forest_activeI]

lemmas underlying_invars_pres = underlying_invarsE[OF _  underlying_invarsI[OF inv_actives_in_EI' inv_digraph_abs_F_in_EI' inv_forest_in_EI' inv_forest_actives_disjointI' inv_conversion_consistentI' 
                                   inv_rep_reachableI' inv_reachable_same_repI' inv_reps_in_VI' inv_finite_forestI' inv_components_in_VI'
                                   inv_active_different_compsI' inv_pos_bal_repI' inv_inactive_same_componentI' inv_dbltn_graph_forestI'
                                   inv_forest_in_VI' inv_comp_card_correctI' inv_set_invar_activesI' inv_forest_good_graphI'
                                    inv_digraph_abs_\<FF>_symI' inv_unbl_iff_forest_activeI']]


lemma underlying_invars_gamma: "underlying_invars state \<Longrightarrow> underlying_invars (state\<lparr> current_\<gamma> := \<gamma>\<rparr>)"
  unfolding underlying_invars_def validF_def inv_actives_in_E_def inv_digraph_abs_F_in_E_def inv_forest_in_E_def inv_forest_actives_disjoint_def
               inv_conversion_consistent_def inv_rep_reachable_def inv_reachable_same_rep_def inv_components_in_V_def inv_active_different_comps_def 
               inv_finite_forest_def inv_reps_in_V_def inv_pos_bal_rep_def inv_inactive_same_component_def  inv_dbltn_graph_forest_def 
               inv_forest_in_V_def inv_comp_card_correct_def inv_set_invar_actives_def inv_forest_good_graph_def 
               inv_digraph_abs_\<FF>_sym_def  inv_unbl_iff_forest_active_def consist_def
               F_def F_redges_def by auto

definition "invar_gamma (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) = (current_\<gamma> state > 0)"

lemma invar_gammaE: "\<lbrakk>invar_gamma state; (current_\<gamma> state > 0 \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
and invar_gammaI: "current_\<gamma> state > 0 \<Longrightarrow> invar_gamma state"
and  invar_gammaD: "invar_gamma state \<Longrightarrow> current_\<gamma> state > 0"
  by(auto simp add: invar_gamma_def)

abbreviation "a_balance state \<equiv> (\<lambda> v. abstract_real_map (bal_lookup (balance state)) v)"
abbreviation "a_current_flow state \<equiv> (\<lambda> v. abstract_real_map (flow_lookup (current_flow state)) v)"

definition "invar_non_zero_b (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
          ( \<not> (\<forall>v\<in>\<V>. a_balance state v = 0))"

lemma invar_non_zero_bI:
"\<not> (\<forall>v\<in>\<V>. a_balance state v = 0) \<Longrightarrow> invar_non_zero_b state"
and invar_non_zero_bE:
"\<lbrakk>invar_non_zero_b state; (\<not> (\<forall>v\<in>\<V>. a_balance state v = 0) \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
and invar_non_zero_bE':
"\<lbrakk>invar_non_zero_b state; (\<And> v. v\<in>\<V> \<Longrightarrow> a_balance state v \<noteq> 0 \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  by(auto simp add: invar_non_zero_b_def)

definition "invar_forest (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
                (\<forall> e \<in> \<F> state. (a_current_flow state) e > 4 * N * (current_\<gamma> state))"

lemma invar_forestE:
"\<lbrakk>invar_forest state;
((\<And> e. e \<in> \<F> state \<Longrightarrow> (a_current_flow state) e > 4 * N * (current_\<gamma> state))\<Longrightarrow> P)\<rbrakk>
 \<Longrightarrow> P"
and invar_forestI: 
"(\<And> e. e \<in> \<F> state \<Longrightarrow> (a_current_flow state) e > 4 * N * (current_\<gamma> state)) \<Longrightarrow> invar_forest state"
and invar_forestD:
"\<lbrakk>invar_forest state; e \<in> \<F> state\<rbrakk> \<Longrightarrow> (a_current_flow state) e > 4 * N * (current_\<gamma> state)"
  by(auto simp add: invar_forest_def)

definition "invar_integral (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) = 
                        (\<forall> e \<in> to_set (actives state).
                               \<exists> n::nat. (a_current_flow state) e = n * (current_\<gamma> state))"

lemma invar_integralI: 
  "(\<And> e. e \<in> to_set (actives state) \<Longrightarrow> \<exists> n::nat. (a_current_flow state) e = n * (current_\<gamma> state)) 
  \<Longrightarrow> invar_integral state"
  unfolding invar_integral_def by simp

lemma invar_integralE: 
"\<lbrakk>invar_integral state;
  ((\<And> e. e \<in> to_set (actives state) \<Longrightarrow> 
           \<exists> n::nat. (a_current_flow state) e = n * (current_\<gamma> state))
   \<Longrightarrow> P)\<rbrakk>
  \<Longrightarrow> P"
  unfolding invar_integral_def by blast

lemma invar_integralD: 
  "\<lbrakk>invar_integral state; e \<in> to_set (actives state)\<rbrakk>
  \<Longrightarrow> \<exists> n::nat. (a_current_flow state) e = n * (current_\<gamma> state)"
  unfolding invar_integral_def by blast

definition "invar_isOptflow (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
            is_Opt (\<b> - a_balance state) (a_current_flow state)"

lemma invar_isOptflowE:
  "\<lbrakk>invar_isOptflow state;
  (is_Opt (\<b> - a_balance state) (a_current_flow state) \<Longrightarrow> P)\<rbrakk>
  \<Longrightarrow> P"
and invar_isOptflowI:
"is_Opt (\<b> - a_balance state) (a_current_flow state) \<Longrightarrow> invar_isOptflow state"
and invar_isOptflowD:
"invar_isOptflow state \<Longrightarrow> is_Opt (\<b> - a_balance state) (a_current_flow state)"
  by(auto simp add: invar_isOptflow_def)

definition "\<Phi> (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
              (\<Sum> v \<in>  \<V>. \<lceil> \<bar> a_balance state v\<bar> / (current_\<gamma> state) - (1 - \<epsilon>)\<rceil>)"

definition "maintain_forest_entry (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
              (\<forall> e \<in> \<F> state. a_current_flow state e > 8*N*current_\<gamma> state)"

lemma maintain_forest_entryE:
  "\<lbrakk>maintain_forest_entry state;
   ((\<And> e. e \<in> \<F> state \<Longrightarrow> a_current_flow state e > 8*N*current_\<gamma> state) \<Longrightarrow> P)\<rbrakk>
  \<Longrightarrow> P"
  by(auto simp add: maintain_forest_entry_def)

lemma maintain_forest_entryI:
  "(\<And> e. e \<in> \<F> state \<Longrightarrow> a_current_flow state e > 8*N*current_\<gamma> state)
   \<Longrightarrow> maintain_forest_entry state"
  by(auto simp add: maintain_forest_entry_def)

lemma maintain_forest_entryD:
  "\<lbrakk>maintain_forest_entry state; e \<in> \<F> state\<rbrakk> \<Longrightarrow> a_current_flow state e > 8*N*current_\<gamma> state"
  by(auto simp add: maintain_forest_entry_def)

definition "send_flow_entryF (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state)
            = (\<forall> e \<in> \<F> state. a_current_flow state e > 6*N*current_\<gamma> state)"

lemma send_flow_entryFE:
  "\<lbrakk>send_flow_entryF state;
  ((\<And> e. e \<in> \<F> state \<Longrightarrow> a_current_flow state e > 6*N*current_\<gamma> state) \<Longrightarrow> P)\<rbrakk>
  \<Longrightarrow> P"
  by(auto simp add: send_flow_entryF_def)

lemma send_flow_entryFI:
  "(\<And> e. e \<in> \<F> state \<Longrightarrow> a_current_flow state e > 6*N*current_\<gamma> state) \<Longrightarrow> send_flow_entryF state"
  by(auto simp add: send_flow_entryF_def)

lemma send_flow_entryFD:
  "\<lbrakk>send_flow_entryF state; e \<in> \<F> state\<rbrakk> \<Longrightarrow> a_current_flow state e > 6*N*current_\<gamma> state"
  by(auto simp add: send_flow_entryF_def)

definition "orlins_entry (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
               (\<forall> v \<in> \<V>. \<bar> a_balance state v \<bar> \<le> (1 - \<epsilon>) * current_\<gamma> state)"

lemma orlins_entryI:
  "(\<And> v. v \<in> \<V> \<Longrightarrow> \<bar> a_balance state v \<bar> \<le> (1 - \<epsilon>) * current_\<gamma> state) \<Longrightarrow> orlins_entry state"
 and  orlins_entryE:
  "\<lbrakk>orlins_entry state; 
   ((\<And> v. v \<in> \<V> \<Longrightarrow> \<bar> a_balance state v \<bar> \<le> (1 - \<epsilon>) * current_\<gamma> state) \<Longrightarrow>P)\<rbrakk>
   \<Longrightarrow> P"
and  orlins_entryD:
  "\<lbrakk>orlins_entry state; v \<in> \<V>\<rbrakk> \<Longrightarrow> \<bar> a_balance state v \<bar> \<le> (1 - \<epsilon>) * current_\<gamma> state"
  by(auto simp add: orlins_entry_def)

definition "invar_F1 (thr::real) (state::('f_impl, 'b_impl, 'd, 'conv_impl, 'e, 'r_comp_impl, 'not_blocked_impl) Algo_state) =
             (\<forall> v \<in> \<V>. \<bar> a_balance state v \<bar> \<le> 
                                  thr * card (connected_component (to_graph (\<FF> state)) v))"

lemma invar_F1E:
  "\<lbrakk>invar_F1 (thr::real) state;
   ((\<And> v. v \<in> \<V> \<Longrightarrow> \<bar> a_balance state v \<bar> \<le> 
                     thr * card (connected_component (to_graph (\<FF> state)) v)) \<Longrightarrow> P)\<rbrakk>
  \<Longrightarrow> P"
  by(auto simp add: invar_F1_def)

lemma invar_F1I:
  "(\<And> v. v \<in> \<V> \<Longrightarrow> \<bar> a_balance state v \<bar> \<le> 
     (thr::real) * card (connected_component (to_graph (\<FF> state)) v)) \<Longrightarrow>
  invar_F1 thr state"
  by(auto simp add: invar_F1_def)

lemma invar_F1D:
  "\<lbrakk>invar_F1 (thr::real) state; v \<in> \<V>\<rbrakk>
   \<Longrightarrow> \<bar>a_balance state v\<bar> \<le> thr * card (connected_component (to_graph (\<FF> state)) v)"
  by(auto simp add: invar_F1_def)

definition "invar_F2 (thr1::real) (thr2::real) state = 
                   (\<forall> e \<in> \<F> state.
                               (a_current_flow state) e > thr1 - thr2 * 
                                card (connected_component (to_graph (\<FF> state)) (fst e)))"

lemma invar_F2E: 
  "\<lbrakk>invar_F2 (thr1::real) (thr2::real) state;
   ((\<And> e.  e \<in> \<F> state \<Longrightarrow> (a_current_flow state) e > thr1 - thr2 * 
             card (connected_component (to_graph (\<FF> state)) (fst e))) \<Longrightarrow> P)\<rbrakk>
   \<Longrightarrow> P"
  by(auto simp add: invar_F2_def)

lemma invar_F2I: 
  "(\<And> e. e \<in> \<F> state \<Longrightarrow> (a_current_flow state) e > (thr1::real) - (thr2::real) * 
             card (connected_component (to_graph (\<FF> state)) (fst e)))
  \<Longrightarrow> invar_F2 (thr1::real) (thr2::real) state"
  by(auto simp add: invar_F2_def) 

lemma invar_F2D: 
  "\<lbrakk>invar_F2 (thr1::real) (thr2::real) state; e \<in> \<F> state\<rbrakk> 
     \<Longrightarrow> (a_current_flow state) e > thr1 - thr2 * 
             card (connected_component (to_graph (\<FF> state)) (fst e))"
  by(auto simp add: invar_F2_def)

lemma invar_isOpt_gamma_change:
"invar_isOptflow state \<Longrightarrow> invar_isOptflow (state \<lparr>current_\<gamma> :=gamma \<rparr>)"
  unfolding invar_isOptflow_def by simp

definition "pos_flow_F state  = (\<forall>e\<in>\<F> state. 0 < a_current_flow state e)"

lemma pos_flow_FI: "(\<And> e. e\<in>\<F> state \<Longrightarrow> 0 < a_current_flow state e) \<Longrightarrow> pos_flow_F state"
  by(auto simp add: pos_flow_F_def)

lemma pos_flow_FE: 
  "\<lbrakk>pos_flow_F state;
    ((\<And> e. e\<in>\<F> state \<Longrightarrow> 0 < a_current_flow state e) \<Longrightarrow> P)\<rbrakk>
   \<Longrightarrow> P"
  by(auto simp add: pos_flow_F_def)

definition "invar_above_6Ngamma state =
(\<forall> e \<in> \<F> state. a_current_flow state e >  
            6*N*current_\<gamma> state - (2*N  - \<Phi> state)*current_\<gamma> state)"

lemma invar_above_6NgammaI: 
  "(\<And> e. e \<in> \<F> state \<Longrightarrow>
   a_current_flow state e >  6*N*current_\<gamma> state - (2*N  - \<Phi> state)*current_\<gamma> state)
  \<Longrightarrow> invar_above_6Ngamma state"
  by(auto simp add: invar_above_6Ngamma_def)

lemma invar_above_6NgammaE: 
  "\<lbrakk>invar_above_6Ngamma state;
     ((\<And> e. e \<in> \<F> state \<Longrightarrow> a_current_flow state e > 
                6*N*current_\<gamma> state - (2*N  - \<Phi> state)*current_\<gamma> state) \<Longrightarrow> P)\<rbrakk>
   \<Longrightarrow> P"
  by(auto simp add: invar_above_6Ngamma_def)

lemma invar_above_6NgammaD: 
  "\<lbrakk>invar_above_6Ngamma state; e \<in> \<F> state\<rbrakk>
   \<Longrightarrow> a_current_flow state e >  6*N*current_\<gamma> state - (2*N  - \<Phi> state)*current_\<gamma> state"
  by(auto simp add: invar_above_6Ngamma_def)

lemmas [code] = abstract_conv_map_def
abstract_not_blocked_map_def
abstract_rep_map_def
abstract_comp_map_def
move_balance_def
augment_edge_impl.simps
add_direction_def
move_def
to_redge_path.simps
insert_undirected_edge_def
neighbourhood'_def
end

locale 
algo =  
 cost_flow_network where fst = fst +

 algo_spec where fst=fst and edge_map_update = "edge_map_update::'v \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'd"+  

 Set_with_predicate +

 Adj_Map_Specs2 where  update =  "edge_map_update::'v \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'd"

for fst::"'edge \<Rightarrow> 'v" and edge_map_update +
assumes       infinite_u:  "\<And> e. \<u> e = PInfty" and 
                 \<epsilon>_axiom: "0 < \<epsilon>" "\<epsilon> \<le> 1 / 2" "\<epsilon> \<le> 1/ (real (card \<V>))" "\<epsilon> < 1/2" and 
    conservative_weights: "\<not> has_neg_cycle make_pair \<E> \<c>" and 
          \<E>_impl_meaning: "to_set \<E>_impl = \<E>" "set_invar \<E>_impl" and 
     empty_forest_axioms:   "\<And> v. lookup empty_forest v = None" "adjmap_inv empty_forest" and 
                   N_def: "N = card \<V>"
begin 

lemma subset_V_card_leq_N: "X \<subseteq> \<V> \<Longrightarrow> card X \<le> N"
  using N_def \<V>_finite card_mono by blast

lemma empty_forest_empty: "digraph_abs empty_forest = {}"
                          "to_graph empty_forest = {}"
 by(auto simp add: digraph_abs_def to_graph_def UD_def neighbourhood'_def
                   empty_forest_axioms(1) adj_map_specs.vset.set.invar_empty adj_map_specs.vset.set.set_empty
                   adj_map_specs.vset.set.set_isin)

lemma empty_forest_good_graph:
"good_graph_invar empty_forest"
  using empty_forest_axioms(2) 
  by(auto intro!: good_graph_invarI simp add: empty_forest_axioms)

lemma N_gtr_0: "N > 0"
  using cardV_0
  by (simp add: N_def )

lemma forest_symmetic: 
  "\<lbrakk>inv_digraph_abs_\<FF>_sym state; (u, v) \<in> [\<FF> state]\<^sub>g\<rbrakk> \<Longrightarrow> (v, u) \<in> [\<FF> state]\<^sub>g"
  by(auto elim: inv_digraph_abs_\<FF>_symE')

lemma inv_conversion_consistent_conv_to_rdg_fstv:
  assumes "inv_conversion_consistent state" "(x, y) \<in> (digraph_abs (\<FF> state))"
  shows "fstv ((a_conv_to_rdg state) (x,y) ) = x"
  apply(rule inv_conversion_consistentE[OF assms(1) refl])
  using assms(2) vs_to_vertex_pair_pres(1) 
  by fastforce

lemma inv_conversion_consistent_conv_to_rdg_sndv: 
  assumes "inv_conversion_consistent state" "(x, y) \<in> (digraph_abs (\<FF> state))"
  shows "sndv ((a_conv_to_rdg state) (x,y) ) = y"
  apply(rule inv_conversion_consistentE[OF assms(1) refl])
  using assms(2) vs_to_vertex_pair_pres(2) 
  by fastforce

lemma consist_fstv: 
  assumes "consist E to_rdg" "(u, v) \<in> E" 
  shows   "fstv (to_rdg (u, v)) = u"
  apply(rule consistE[OF assms(1)])
  using assms(2) vs_to_vertex_pair_pres(1) 
  by fastforce

lemma consist_sndv: 
  assumes "consist E to_rdg" "(u, v) \<in> E" 
  shows   "sndv (to_rdg (u, v)) = v"
  apply(rule consistE[OF assms(1)])
  using assms(2) vs_to_vertex_pair_pres(2) 
  by fastforce

lemma consist_edge_in_vertex_in:
  assumes "consist (digraph_abs (\<FF> state)) (a_conv_to_rdg state)" "u \<noteq> v" 
          "(u, v) \<in> digraph_abs (\<FF> state)"  "(v, u) \<in> digraph_abs (\<FF> state)"
          "inv_digraph_abs_\<FF>_sym state"
  shows   "u \<in> dVs (to_vertex_pair ` ((a_conv_to_rdg state) ` (digraph_abs (\<FF> state))))"
proof-
  have "to_vertex_pair ((a_conv_to_rdg state) (u, v)) = (u, v)"
    using consistD(1)[OF assms(1,3)] by auto
  then show ?thesis
    using assms(3) by(auto intro!: dVsI(1)[of u v] image_eqI)
qed

lemma proper_path_some_redges:
  "length l \<ge> 2 \<Longrightarrow> (to_redge_path to_rdg' l) \<noteq> []" for l to_rdg' Q
   apply(induction to_rdg' l rule: to_redge_path.induct)
   apply (metis list.simps(3) to_redge_path.simps(1))
   apply (metis list.distinct(1) to_redge_path.simps(2))
   by auto

lemma perpath_to_redgepath:
  "\<lbrakk>inv_conversion_consistent state; inv_digraph_abs_\<FF>_sym state; 
    walk_betw (to_graph (\<FF> state)) u p v; length p \<ge> 2\<rbrakk>
    \<Longrightarrow>  prepath (to_redge_path (conv_to_rdg state) p)"
  unfolding walk_betw_def
proof(induction p arbitrary: u)
  case (Cons a p u)
  then show ?case
        using path_pref[of "(to_graph (\<FF> state))" "[a]" p] 
        apply (cases rule: list_cases4[of p])
        apply(auto intro!: prepath_intros)
        by(auto intro!: prepath_intros elim!: in_to_graphE inv_digraph_abs_\<FF>_symE symmetric_digraphE
             simp add: inv_conversion_consistent_conv_to_rdg_fstv[simplified o_apply]
                        inv_conversion_consistent_conv_to_rdg_sndv[simplified o_apply])
qed simp

lemma concretize_walk:
  "\<lbrakk>validF state; walk_betw (to_graph (\<FF> state)) u p v; length p \<ge> 2;
    inv_digraph_abs_\<FF>_sym state\<rbrakk>
    \<Longrightarrow> set (to_redge_path (conv_to_rdg state) p) \<subseteq> 
        (a_conv_to_rdg state) ` (digraph_abs (\<FF> state))"
  unfolding walk_betw_def
proof(induction "(conv_to_rdg state)" p arbitrary: u rule: to_redge_path.induct)
  case (1 u va ua)
  hence "{u, va} \<in> (to_graph (\<FF> state))" "u \<noteq> va"
    using 1 path_2[of "(to_graph (\<FF> state))" u va Nil] 
    unfolding validF_def by auto
  moreover have "set (to_redge_path (conv_to_rdg state) [u, va])  =
        {(a_conv_to_rdg state) (u, va)}" by simp
  moreover have " {(a_conv_to_rdg state) (u, va)} \<subseteq>  a_conv_to_rdg state ` [\<FF> state]\<^sub>g"
    by (simp add: "1.prems"(4) calculation(1) inv_digraph_abs_\<FF>_sym_applied')
  ultimately show ?case 
    using "1.prems"(4) inv_digraph_abs_\<FF>_sym_applied' by auto
next
  case (2 u v w vs ua)
  hence "{u, v} \<in> (to_graph (\<FF> state))" "u \<noteq> v"
    using 2 path_2[of "to_graph (\<FF> state)" u v Nil] 
    by(auto simp add: validF_def)
  moreover have "set (to_redge_path (conv_to_rdg state) [u, v])  =
        {(a_conv_to_rdg state) (u, v)}" by simp
  moreover have " {(a_conv_to_rdg state) (u, v)} \<subseteq>  a_conv_to_rdg state ` [\<FF> state]\<^sub>g"
    by (simp add: "2.prems"(4) calculation(1) inv_digraph_abs_\<FF>_sym_applied')
  moreover have "    set (to_redge_path (conv_to_rdg state) (v # w # vs))
               \<subseteq>  (a_conv_to_rdg state) ` (digraph_abs (\<FF> state))"
    using "2.prems" 
    by(intro 2(1)[of v]) auto
  ultimately show ?case 
    using "2.prems"(4) inv_digraph_abs_\<FF>_sym_applied' by auto
qed simp+
  
lemma consist_to_rdg_costs_negation:
  assumes  "consist E to_rdg" "u \<noteq> v" "(u, v) \<in> E" "(v, u) \<in> E"
  shows    "\<cc> (to_rdg (u, v)) = -  \<cc> (to_rdg (prod.swap (u, v)))"
  apply(rule consistE[OF assms(1)])
  apply(cases "to_rdg (u, v)") 
  using assms(2-4) 
  by fastforce+

lemma foldr_last_append: "\<cc> d + foldr (\<lambda>e. (+) (\<cc> e)) xs 0 = 
                           foldr (\<lambda>e. (+) (\<cc> e)) (xs@[d]) 0"
  by(induction xs) auto

lemma to_redge_path_last_append: 
  "\<lbrakk>length xs \<ge> 2; last xs = v\<rbrakk>
    \<Longrightarrow> to_redge_path to_rdg xs @[abstract_conv_map  to_rdg (v, u)] =
        to_redge_path to_rdg (xs@[u])"
  by(induction to_rdg xs rule: to_redge_path.induct) auto

lemma to_redge_path_costs:
  assumes "consist E (abstract_conv_map to_rdg)" "length p \<ge> 2" "distinct p"
          "\<And> x y. (x, y) \<in> E \<Longrightarrow> (y, x) \<in> E"
          "set (edges_of_vwalk p) \<subseteq> E"
  shows   "foldr (\<lambda> e acc. \<cc> e + acc) (to_redge_path to_rdg p) 0 
                      = - foldr (\<lambda> e acc. \<cc> e + acc) (to_redge_path to_rdg (rev p)) 0"
  using assms
proof(induction to_rdg p rule: to_redge_path.induct)
  case (1 to_rdg u v)
  moreover hence "u \<noteq> v" by simp
  ultimately show ?case 
    using consist_to_rdg_costs_negation[of E "abstract_conv_map to_rdg" u v] by fastforce
next
  case (2 to_rdg u v w vs)
  hence  u_neq_v:"u \<noteq> v" by simp
  have " foldr (\<lambda>e. (+) (\<cc> e)) (to_redge_path to_rdg (u#v # w # vs)) 0 = 
         ( \<cc> (abstract_conv_map to_rdg (u, v))) + foldr (\<lambda>e. (+) (\<cc> e)) (to_redge_path to_rdg ( v#w # vs)) 0" 
    by simp
  also have "... =  - ( \<cc> ((abstract_conv_map to_rdg (v, u)))) - 
                     foldr (\<lambda>e. (+) (\<cc> e)) (to_redge_path to_rdg ( rev (v#w # vs))) 0"
    using consist_to_rdg_costs_negation[of E "abstract_conv_map to_rdg"  u v ] 2 u_neq_v  by simp
  also have "\<dots> = - ( (\<cc> (abstract_conv_map to_rdg (v, u))) +
                     foldr (\<lambda>e. (+) (\<cc> e)) (to_redge_path to_rdg ( rev (v#w # vs))) 0)"
    by simp
  also have "... = - (foldr (\<lambda>e. (+) (\<cc> e)) 
                       ((to_redge_path to_rdg ( (rev (v#w # vs))))@[(abstract_conv_map to_rdg (v, u))]) 0)"
    using foldr_last_append by simp
  also have "\<dots> =  - (foldr (\<lambda>e. (+) (\<cc> e)) 
                       ((to_redge_path to_rdg ( (rev (v#w # vs)) @[u]))) 0)"     
  using to_redge_path_last_append[of "rev (v # w # vs)" v to_rdg u] by simp
  finally show ?case by simp
qed simp+

lemma to_rdg_hd: 
  assumes "consist E (abstract_conv_map to_rdg)" "length p \<ge> 2"
          "set (edges_of_vwalk p) \<subseteq> E"
  shows   "fstv (hd (to_redge_path to_rdg p)) =  hd p"
  using assms
  apply(induction to_rdg p rule: to_redge_path.induct)
  using consist_fstv by fastforce+

lemma to_rdg_last_cons: " (last (abstract_conv_map to_rdg (u, v) # to_redge_path to_rdg (v # va # vb))) =
                          (last (to_redge_path to_rdg (v # va # vb)))"
  by (smt (verit, best) last_ConsR list.discI list.inject to_redge_path.elims)

lemma to_rdg_last: 
  assumes "consist E (abstract_conv_map to_rdg)" "length p \<ge> 2"
          "set (edges_of_vwalk p) \<subseteq> E"
    shows "sndv (last (to_redge_path to_rdg p)) =  last p"
  using assms
  apply(induction to_rdg p rule: to_redge_path.induct)
  subgoal for to_rdg u v
  using consist_sndv by fastforce
  subgoal for to_rdg u v va vb
    using to_rdg_last_cons[of to_rdg u v va vb] by auto
  by auto

lemma to_rdg_not_in: 
  assumes "consist E (abstract_conv_map to_rdg)" "length p \<ge> 2"
          "distinct (u # p)" "(u, v) \<in> E" "set (edges_of_vwalk p ) \<subseteq> E"
    shows "abstract_conv_map to_rdg (u, v) \<notin> set (to_redge_path to_rdg p)"
  using assms
proof(induction to_rdg p rule: to_redge_path.induct)
  case (1 to_rdg ua va)
  then show ?case 
    using  consist_conv_inj[of E "abstract_conv_map to_rdg"]  consist_fstv[OF 1(1,4)]
           to_rdg_hd[OF 1(1,2)] by auto
next
  case (2 to_rdg ua va vaa vb)
  then show ?case
    using  consist_conv_inj[of E "abstract_conv_map to_rdg"]  consist_fstv[OF 2(2,5)]
           to_rdg_hd[OF 2(2,3)] 
    by auto
qed auto

lemma to_rdg_distinct: 
  assumes "consist E (abstract_conv_map to_rdg)" "distinct p" 
          "set (edges_of_vwalk p) \<subseteq> E"
  shows   "distinct (to_redge_path to_rdg p)"
  using assms
  apply(induction to_rdg p rule: to_redge_path.induct)
  using to_rdg_not_in[of _ _ "(_ # _ # _)" ] by force+

lemma consist_oedge:
  assumes "consist E to_rdg'" "v \<noteq> v'" "(v, v') \<in> E" "(v', v) \<in> E"
    shows "{oedge (to_rdg' (v, v'))} = oedge ` {to_rdg' (v', v), to_rdg' (v, v')}"
  apply(rule consistE[OF assms(1)])
  using   assms(2,3,4)
  by (smt (verit, best) insert_commute oedge_both_redges_image oedge.simps(1,2) swap_simp)

lemma  oedge_of_to_redgepath_subset:
  assumes "distinct Q" "consist E (abstract_conv_map to_rdg')" 
  shows "oedge ` set (to_redge_path to_rdg' Q) = 
          oedge ` (abstract_conv_map to_rdg') ` (set (edges_of_vwalk Q))" 
  using assms
proof(induction Q rule: edges_of_path.induct)
  case (3 v v' l)
  then show ?case 
  proof(cases l)
    case Nil
    then show ?thesis 
      using 3 consist_oedge [of E "abstract_conv_map to_rdg'" v v'] 
      by simp
   next
     case (Cons a list)
     show ?thesis
     proof(rule trans[of _ "oedge ` set (to_redge_path to_rdg' (v # v' # a#list))"],
           goal_cases)
       case 2
       show ?case
       using Cons 3 
          apply(subst to_redge_path.simps(2), subst set_simps(2))
          apply(subst edges_of_vwalk.simps, subst set_simps(2), subst image_insert)
          by (subst subst insert_is_Un, 
              auto    intro: set_union_eq_cong 
                    simp add:  consist_oedge [of E "abstract_conv_map to_rdg'" v v'])
      qed (simp add: Cons 3)
   qed
 qed auto

lemma to_redgepath_subset:
  assumes "distinct Q" "consist E (abstract_conv_map to_rdg')"
    shows "set (to_redge_path to_rdg' Q) \<subseteq>
           (abstract_conv_map to_rdg') ` (set (edges_of_vwalk Q))" 
  using assms
proof(induction Q rule: edges_of_path.induct)
  case (3 v v' l)
  then show ?case 
  proof(cases l)
    case Nil
    then show ?thesis 
      using 3 
      by auto
     next
       case (Cons a list)
       show ?thesis
       proof(rule subset_trans[of _ "set (to_redge_path to_rdg' (v # v' # a#list))"],
             goal_cases)
         case 2
         show ?case 
          using 3 Cons by fastforce
     qed (simp add: 3 Cons)
   qed
 qed auto

lemma to_redge_path_simp: "to_redge_path to (u#v#ws) = (abstract_conv_map to (u, v)) # to_redge_path to (v#ws)"
      for u v ws to 
  by(cases ws) auto

lemma oedge_of_to_redge_path_rev:
  assumes "distinct Q" "consist E (abstract_conv_map to_rdg')"
          "set (edges_of_vwalk Q) \<subseteq> E" "prod.swap ` set (edges_of_vwalk Q) \<subseteq> E"
     shows " oedge ` set (to_redge_path to_rdg' (rev Q)) = oedge ` set (to_redge_path to_rdg' Q)" 
proof(insert assms, rule sym, induction "length Q" arbitrary: Q)
  case (Suc n Q)
  show ?case 
  proof(cases rule: edges_of_path.cases[of Q])
    case (3 u v Q')
    have consist_oedge_props: "u \<noteq> v" "(u, v) \<in> E" "v \<noteq> u" "(v, u) \<in> E"
      using  "3" Suc.prems(1,4,3) by auto
    show ?thesis
    proof(rule trans[of _ "oedge ` (insert (abstract_conv_map to_rdg' (u, v))
                                       (set (to_redge_path to_rdg' (v#Q'))))"],
          goal_cases)
        case 2
          show ?case
          proof(rule trans[of _ "{oedge (abstract_conv_map to_rdg' (u, v))} \<union>
                               oedge ` set (to_redge_path to_rdg' (v#Q'))"], fast, goal_cases)
            case 1
            then show ?case 
            proof(subst Un_commute, 
                  rule trans[of _ "oedge ` set (to_redge_path to_rdg' (rev Q'@[v])) \<union> 
                  {oedge (abstract_conv_map to_rdg' (v, u))}"], goal_cases)
              case 1
              moreover have "{oedge (abstract_conv_map to_rdg' (u, v))} = {oedge (abstract_conv_map to_rdg' (v, u))}"
                using Suc.prems(2) consistD(2) consist_oedge consist_oedge_props(2,4) by fastforce
             ultimately show ?case
               using Suc 3 by auto
          next
            case 2
            then show ?case
            using 3 Suc
          proof(cases Q')
            case (Cons a list)
            then show ?thesis      
            apply(subst sym[OF  image_singleton[of oedge]], subst sym[OF image_Un])
            apply(subst sym[OF set_singleton_list[of "abstract_conv_map to_rdg' (v, u)"]],
                subst sym[OF set_append])
            using 2 3 Suc to_redge_path_last_append[of "rev Q' @ [v]"  v to_rdg'] 
            by auto
       qed simp
      qed
     qed
    qed (auto simp add: 3 to_redge_path_simp[of to_rdg' u v Q'] 
                        set_simps(2)[of " abstract_conv_map to_rdg' (u, v)" ])
  qed (auto simp add: Suc)
qed simp

lemma dVs_single_edge:"dVs {(u, v)} = {u, v}" 
  unfolding dVs_def by simp

lemma conv_to_rdg_coincide:
  "(\<And> x y. {x, y} \<in> set (edges_of_path Q) 
        \<Longrightarrow> abstract_conv_map to_rdg (x, y) = abstract_conv_map to_rdg' (x, y)) 
    \<Longrightarrow> to_redge_path to_rdg Q = to_redge_path to_rdg' Q"
  apply(induction Q, simp)
  subgoal for a Q
    apply(cases Q, simp)
    subgoal for aa list
      by(cases list, auto) 
    done
  done

lemma consist_dVs_path:
  "\<lbrakk>consist E (abstract_conv_map to_rdg'); distinct Q; set (edges_of_vwalk Q) \<subseteq> E\<rbrakk>
    \<Longrightarrow> dVs (to_vertex_pair ` (abstract_conv_map to_rdg') ` (set (edges_of_vwalk Q))) \<subseteq> set Q" for to_rdg' Q
proof(induction Q rule: edges_of_path.induct)
  case (3 v v' l)
  then show ?case 
    apply(subst edges_of_vwalk.simps, subst set_simps(2))
    apply(subst image_insert)+
    apply(subst insert_is_Un)
      apply(subst dVs_union_distr)
        proof(rule Un_least, goal_cases)
          case 1
          show ?case
            using "3.prems"(1,3) consist_fstv to_vertex_pair_fst_snd  consist_sndv 
           by (auto simp add: dVs_def)
    qed auto
 qed auto

lemma Phi_nonneg: "invar_gamma state\<Longrightarrow> \<Phi> state \<ge> 0"
  unfolding \<Phi>_def invar_gamma_def
  apply(rule sum_nonneg) 
  by (smt (verit, ccfv_threshold) \<epsilon>_axiom(1) divide_nonneg_pos zero_le_ceiling)

definition add_fst ("_ +++ _") where
"add_fst c ab = (c + prod.fst ab, prod.snd ab)"

lemma add_fst_snd_same: "prod.snd (c +++ ab) = prod.snd ab"
  unfolding add_fst_def by simp

lemma "underlying_invars state \<Longrightarrow> underlying_invars (state \<lparr> current_\<gamma>:= new\<rparr>)"
  using underlying_invars_gamma by blast

lemma oedge_of_path_in_F: 
  assumes "underlying_invars state"
          "walk_betw (to_graph (\<FF> state)) x' Q y'" "distinct Q"
  shows "oedge ` (set (to_redge_path (conv_to_rdg state) Q)) \<subseteq> \<F> state" 
  apply(rule order.trans, rule image_mono[OF to_redgepath_subset[OF assms(3)]])
   apply(rule  from_underlying_invars'(6)[OF assms(1)])
  apply(unfold F_def F_redges_def)
  apply(rule image_mono)+
  apply(rule undirected_edges_subset_directed_edges_subset)
  using  from_underlying_invars'(19)[OF assms(1)] assms(2) 
  by (auto intro!: path_edges_subset[OF walk_between_nonempty_pathD(1)] 
           elim:  symmetric_digraphE
        simp add: to_graph_def)

lemma oedge_of_rev_path_in_F: 
  assumes "underlying_invars state"
          "walk_betw (to_graph (\<FF> state)) x' Q y'" "distinct Q"
  shows "oedge ` (set (to_redge_path (conv_to_rdg state) (rev Q))) \<subseteq> \<F> state" 
  apply(rule order.trans, rule image_mono[OF to_redgepath_subset])
  using assms(3) apply simp
   apply(rule from_underlying_invars'(6)[OF assms(1)])
  apply(unfold F_def F_redges_def)
  apply(rule image_mono)+
  apply(rule undirected_edges_subset_directed_edges_subset)
  using  from_underlying_invars'(19)[OF assms(1)] assms(2)
  by (auto intro!: path_edges_subset[OF walk_between_nonempty_pathD(1)] 
             elim:  symmetric_digraphE
        simp add: to_graph_def edges_of_path_rev[symmetric] )

lemma forest_paths_are_optimum:
  assumes "invar_isOptflow state"
          "\<forall> e \<in> \<F> state. a_current_flow state e > 0"
          "walk_betw (to_graph (\<FF> state)) x' Q y'"
          "underlying_invars state"
          "x' \<noteq> y'"
          "distinct Q"
    shows "is_min_path (a_current_flow state) x' y' (to_redge_path (conv_to_rdg state) Q)"
proof-
  have inv_digraph_abs_\<FF>_sym: "inv_digraph_abs_\<FF>_sym state"
    using assms(4) underlying_invars_def by blast
  note forest_symmetric1 = forest_symmetic[OF inv_digraph_abs_\<FF>_sym] 
  have lengthQ: "2 \<le> length Q"
    by (meson assms(3) assms(5) walk_betw_length)
  have prepath:"prepath (to_redge_path (conv_to_rdg state) Q)"
    using assms(4) inv_conversion_consistent_from_underlying_invars inv_digraph_abs_\<FF>_sym_from_underlying_invars lengthQ assms(3)
          perpath_to_redgepath[of state] by auto
  have prepath_rev:"prepath (to_redge_path (conv_to_rdg state) (rev Q))"
    using assms(4) inv_conversion_consistent_from_underlying_invars lengthQ walk_symmetric[OF assms(3)]
          perpath_to_redgepath inv_digraph_abs_\<FF>_sym_from_underlying_invars
    by fastforce
  have Q_in_F:"set (edges_of_path Q) \<subseteq> to_graph (\<FF> state)"
    using path_edges_subset[OF walk_between_nonempty_pathD(1)[OF assms(3)]]
         from_underlying_invars(20)[OF assms(4), simplified inv_digraph_abs_\<FF>_sym_def[simplified]]
    by simp
  have Q_in_F_rev:"set (edges_of_path (rev Q)) \<subseteq> to_graph (\<FF> state)"
    using path_edges_subset[OF walk_between_nonempty_pathD(1)[OF assms(3)], simplified  edges_of_path_rev]
         from_underlying_invars(20)[OF assms(4), simplified inv_digraph_abs_\<FF>_sym_def[simplified]]
    using edges_of_path_rev[of Q] set_rev by fastforce
   have F_subs_E:"\<F> state  \<subseteq> \<E>"
     using assms(4) from_underlying_invars'(3) by presburger
  have oedge_in_F:"oedge ` (set (to_redge_path (conv_to_rdg state) Q)) \<subseteq> \<F> state"
    by (meson assms(3,4,6) oedge_of_path_in_F)
  have oedge_in_F_rev:"oedge ` (set (to_redge_path (conv_to_rdg state) (rev Q))) \<subseteq> \<F> state" 
    by (meson assms(3,4,6) oedge_of_rev_path_in_F)
  have dir_edges_in_F: "set (edges_of_vwalk Q) \<subseteq> [\<FF> state]\<^sub>g"
    using Q_in_F forest_symmetric1 
    by (intro undirected_edges_subset_directed_edges_subset)
       (auto simp add:  to_graph_def intro!: symmetric_digraphI)
  have rev_dir_edges_in_F: "set (edges_of_vwalk (rev Q)) \<subseteq> [\<FF> state]\<^sub>g"
    using Q_in_F_rev forest_symmetric1 
    by (intro undirected_edges_subset_directed_edges_subset)
       (auto simp add:  to_graph_def intro!: symmetric_digraphI)
   have Rcap: "0 < Rcap (a_current_flow state) (set (to_redge_path (conv_to_rdg state) Q))"
    unfolding Rcap_def
    apply(subst linorder_class.Min_gr_iff, simp, simp, auto)
    subgoal for e
      using oedge_in_F assms(2)  infinite_u  oedge_in_F 
      by (cases e) auto
    done
  have Rcap_rev: "0 < Rcap (a_current_flow state) (set (to_redge_path (conv_to_rdg state) (rev Q)))"
    unfolding Rcap_def
    apply(subst linorder_class.Min_gr_iff, simp, simp, auto)
    subgoal for e
      using oedge_in_F_rev assms(2)  infinite_u  oedge_in_F 
      by (cases e) auto
    done
  have a1: "augpath (a_current_flow state) (to_redge_path (conv_to_rdg state) Q)"
    using Rcap prepath by (auto simp add: augpath_def )
  have a2: "set (to_redge_path (conv_to_rdg state) Q) \<subseteq> \<EE>"
    using assms(4) assms(6) from_underlying_invars'(2)[OF assms(4)] from_underlying_invars'(6)[OF assms(4)]
          F_subs_E image_subset_iff o_edge_res[symmetric] oedge_in_F  
    by fastforce
  have a3:"fstv (hd (to_redge_path (conv_to_rdg state) Q)) = x'"
    using   lengthQ to_rdg_hd[OF from_underlying_invars'(6)[OF assms(4)] _ dir_edges_in_F]
             walk_between_nonempty_pathD(3)[OF assms(3)] 
    by simp
  have a4: " sndv (last (to_redge_path (conv_to_rdg state) Q)) = y'" 
    using   lengthQ to_rdg_last[OF from_underlying_invars'(6)[OF assms(4)]_ dir_edges_in_F]
             walk_between_nonempty_pathD(4)[OF assms(3)] by simp
  have a5: "distinct (to_redge_path (conv_to_rdg state) Q)"
    using assms(4,6) dir_edges_in_F from_underlying_invars'(6) to_rdg_distinct by blast
  have C_Q_rev_Q:"\<CC> (to_redge_path (conv_to_rdg state) Q) = - \<CC> (to_redge_path (conv_to_rdg state) (rev Q))"
    using to_redge_path_costs[of "digraph_abs (\<FF> state)" "(conv_to_rdg state)" Q, OF _ lengthQ assms(6) _ dir_edges_in_F]
          to_rdg_distinct[of "digraph_abs (\<FF> state)" "(conv_to_rdg state)" Q, OF _  assms(6), OF _ dir_edges_in_F ]
          to_rdg_distinct[of "digraph_abs (\<FF> state)" "(conv_to_rdg state)""rev Q", OF _, 
                      simplified distinct_rev[of Q], OF _ assms(6)  rev_dir_edges_in_F] distinct_sum2[of _ \<cc>] 
    by(auto simp add: \<CC>_def assms(4) from_underlying_invars'(6) intro: forest_symmetric1)
 have b1: "augpath (a_current_flow state) (to_redge_path (conv_to_rdg state) (rev Q))"
   using Rcap_rev prepath_rev
   by (auto simp add: augpath_def )
  have b2: "set (to_redge_path (conv_to_rdg state) (rev Q)) \<subseteq> \<EE>"
    using assms(4) assms(6) from_underlying_invars'(2)[OF assms(4)] from_underlying_invars'(6)[OF assms(4)]
          F_subs_E image_subset_iff o_edge_res[symmetric] oedge_in_F_rev  
    by fastforce
  have b3:"fstv (hd (to_redge_path (conv_to_rdg state) (rev Q))) = y'"
    using   lengthQ to_rdg_hd[OF from_underlying_invars'(6)[OF assms(4)] _ ] 
             walk_between_nonempty_pathD(3)[OF walk_symmetric[OF assms(3)]] rev_dir_edges_in_F by simp
  have b4: " sndv (last (to_redge_path (conv_to_rdg state) (rev Q))) = x'" 
    using   lengthQ to_rdg_last[OF from_underlying_invars'(6)[OF assms(4)]] rev_dir_edges_in_F
             walk_between_nonempty_pathD(4)[OF  walk_symmetric[OF assms(3)]] by simp
  have b5: "distinct (to_redge_path (conv_to_rdg state) (rev Q))"
    by (simp add: assms(4) assms(6) from_underlying_invars'(6) to_rdg_distinct[OF _ _ rev_dir_edges_in_F])
  have is_s_t_path_rev_Q: "is_s_t_path (a_current_flow state) y' x' (to_redge_path (conv_to_rdg state) (rev Q))"
    by (simp add: b1 b2 b3 b4 b5 is_s_t_path_def)
  have C_Q_rev_Q:"\<CC> (to_redge_path (conv_to_rdg state) Q) = - \<CC> (to_redge_path (conv_to_rdg state) (rev Q))"
    using to_redge_path_costs[of "digraph_abs (\<FF> state)" "(conv_to_rdg state)" Q, OF _ lengthQ assms(6) _ dir_edges_in_F]
          to_rdg_distinct[of "digraph_abs (\<FF> state)" "(conv_to_rdg state)" Q, OF _ assms(6)  dir_edges_in_F]
          to_rdg_distinct[of "digraph_abs (\<FF> state)" "(conv_to_rdg state)""rev Q", OF _ _ rev_dir_edges_in_F, 
                      simplified distinct_rev[of Q], OF _ assms(6)] distinct_sum2[of _ \<cc>] 
    by(auto simp add: \<CC>_def assms(4) from_underlying_invars'(6) intro: forest_symmetric1)
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
          assume P'_asm: "is_s_t_path (a_current_flow state) x' y' P'"
          show "\<CC> (to_redge_path  (conv_to_rdg state) Q) \<le> \<CC> P'"
          proof(rule ccontr)
            assume lesser_cost_asm:"\<not> \<CC> (to_redge_path (conv_to_rdg state) Q) \<le> \<CC> P'"
            hence costs:"\<CC> (to_redge_path (conv_to_rdg state) (rev Q)) + \<CC> P' < 0" 
              using C_Q_rev_Q by fastforce
            define Q' where "Q' = to_redge_path (conv_to_rdg state) (rev Q)"
            define Qpp where "Qpp = map blue (to_redge_path (conv_to_rdg state) (rev Q))"
            define P'cc where "P'cc = map red P'"
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
                    is_s_t_path_rev_Q markers_removeQ augpath_to_hpath_red[of "a_current_flow state"] 
                    augpath_to_hpath_blue[of "a_current_flow state"]
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
            have "\<exists>blue redC.
                  Ball (List.set redC) precycle \<and>
                  prepath blue \<and>
                  distinct blue \<and>
                  sum cc (List.set (Qpp@P'cc)) = \<CC> blue + foldr (\<lambda>D. (+) (\<CC> D)) redC 0 \<and>
                  List.set ((to_redge_path (conv_to_rdg state) (rev Q))@P') = List.set blue \<union> \<Union> {List.set D |D. D \<in> List.set redC} \<and> 
                  fstv (hd blue) = y' \<and> sndv (last blue) = y'"
              using markers_remove  hpath  distinct  setE fstvv_x' sndvv_x' 
              by (fastforce intro!: distinct_hpath_to_distinct_augpath_and_augcycles)
            then obtain P'' redC where all_props:" Ball (List.set redC) precycle"
                  "prepath P''"
                  "distinct P''"
                  "sum cc (List.set (Qpp@P'cc)) = \<CC> P'' + foldr (\<lambda>D. (+) (\<CC> D)) redC 0"
                  "List.set ((to_redge_path (conv_to_rdg state) (rev Q))@P') = List.set P'' \<union> \<Union> {List.set D |D. D \<in> List.set redC}"
                  "fstv (hd P'') = y'" "sndv (last P'') = y'" by auto
            have "sum cc (List.set (Qpp@P'cc)) = \<CC> (to_redge_path (conv_to_rdg state) (rev Q)) + \<CC> P'"
              using distinct_red_sum distinct_blue_sum Qpp_def P'cc_def
                    P'_asm is_s_t_path_rev_Q unfolding is_s_t_path_def augpath_def prepath_def  \<CC>_def 
              by (subst set_append, subst sum.union_disjoint) auto
            then obtain C where C_prop:"(C = P'') \<or> C \<in> List.set redC" "\<CC> C < 0"
              using costs all_props(4) fold_sum_neg_neg_element[of \<CC> redC]
              by force
            have Rcap_pos:"Rcap (a_current_flow state) (List.set C) > 0"
              using is_s_t_path_rev_Q  C_prop  P'_asm sym[OF all_props(5)]
              unfolding augcycle_def augpath_def precycle_def is_s_t_path_def prepath_def \<CC>_def
              by (intro Rcap_subset[of "List.set P'' \<union> \<Union> {List.set D |D. D \<in> List.set redC}" "List.set C"], 
                auto intro: Rcap_union[of "List.set (to_redge_path (conv_to_rdg state) (rev Q))" "List.set P'"])
            have "augcycle (a_current_flow state) C"
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

lemma underlying_invars_subs: 
  assumes     "underlying_invars state"
               "\<FF>_state = \<FF> state"
               "actives_state = actives state"
               "to_rdg = conv_to_rdg state"
               "\<F>_state =  \<F>_redges state"
               "actives_state' = {e | e. e \<in> \<EE> \<and> oedge e \<in> to_set actives_state}"
               "allowed = actives_state' \<union> \<F>_state"
         shows "allowed \<subseteq> \<EE>"
    using  assms(1,2,5,7,6) from_underlying_invars'(2)  by (auto simp add: F_def F_redges_def)
 
lemma simulate_inactives:
  assumes  "augpath f p" "fstv (hd p) = s" "sndv (last p) = t" "set p \<subseteq> \<EE>"
           "underlying_invars state"
           "\<FF>_state = \<FF> state"
           "f = a_current_flow state"
           "actives_state = actives state"
           "to_rdg = conv_to_rdg state"
           "\<F>_state = \<F>_redges state"
           "actives_state' = {e | e. e \<in> \<EE> \<and> oedge e \<in> to_set actives_state}"
           "allowed_edges = actives_state' \<union> \<F>_state"
           "number_not_allowed = cnt_P p (\<lambda> e. e \<notin> allowed_edges)"
           "s \<noteq> t" "\<And> e . e \<in> \<F> state \<Longrightarrow> f e > 0"
     shows "\<exists> qq.  augpath f qq \<and> fstv (hd qq) = s \<and> sndv (last qq) = t \<and> set qq \<subseteq> allowed_edges \<and> qq \<noteq> []"
  using assms
proof(induction number_not_allowed arbitrary: p s t rule: less_induct)
  case (less number_not_allowed)
  have inv_digraph_abs_\<FF>_sym: "inv_digraph_abs_\<FF>_sym state"
    using less underlying_invars_def by blast
  note forest_symmetric1 = forest_symmetic[OF inv_digraph_abs_\<FF>_sym]
  have allowed_edges_sub:"allowed_edges \<subseteq> \<EE>"
    using underlying_invars_subs less(6-13) by simp
  hence allowed_edges_finite:"finite allowed_edges"
    by (simp add: finite_\<EE> finite_subset)
  then show ?case 
  proof(cases "number_not_allowed = 0")
    case True
    hence p_allowed_edges:"set p \<subseteq> allowed_edges" 
      unfolding less
      by (metis Collect_mem_eq assms(10) cnt_P_0_set less.prems(6))
    show ?thesis 
      apply(rule exI[of _ p])
      using less p_allowed_edges 
      by (meson augpath_def prepath_def)
  next
    case False
    then obtain e where e_prop:"e \<in> set p" "e \<notin> \<F>_redges state"
                                "e \<notin> {e | e. e \<in> \<EE> \<and> oedge e \<in> to_set actives_state}"
      unfolding less 
      by (metis (mono_tags, lifting) Un_iff cnt_P_0)
    hence "oedge e \<in> \<E> - to_set (actives state)"
      using allowed_edges_sub less(5) unfolding less 
      using o_edge_res by auto
    hence "connected_component (to_graph (\<FF> state)) (fst (oedge e)) =
           connected_component (to_graph (\<FF> state)) (snd  (oedge e))"
      using less(6) by(simp add: underlying_invars_def inv_inactive_same_component_def less) 
    hence "connected_component (to_graph (\<FF> state)) (fstv e) =
           connected_component (to_graph (\<FF> state)) (sndv e)"
      by(cases e, auto)
    hence or_reach:"fstv e = sndv e \<or> reachable  (to_graph (\<FF> state)) (fstv e) (sndv e)"
      by (metis in_connected_componentE in_connected_componentI2)
    obtain p1 p2 where p1p2:"p1@[e]@p2 = p"
      by (metis \<open>e \<in> set p\<close> in_set_conv_decomp_last single_in_append)
    show ?thesis 
    proof(cases rule: orE'[OF  Meson.disj_comm[OF or_reach]])
      case 2
      have a1: "e # p2 = p \<Longrightarrow> p1 = [] \<Longrightarrow> fstv e = sndv e \<Longrightarrow> augpath f p \<Longrightarrow> augpath f p2"
          apply(rule augpath_split2[of f "p1@[e]"])
        using p1p2 less  by auto
      have a2: "augpath f p \<Longrightarrow> p1 \<noteq> [] \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> sndv (last p1) = fstv (hd p2)"
        using 2 p1p2  augpath_split3[of f p1 "[e]@p2"] augpath_split3[of f "p1@[e]" "p2"] 
        by simp
      have a3: "p1 \<noteq>[] \<Longrightarrow> p2 = [] \<Longrightarrow> augpath f p1"
           apply(rule augpath_split1[of  f _ "[e]@p2"])
            using p1p2 less by auto
     have a:"augpath f (p1@p2)" 
        using p1p2 less(2) 2
        apply(cases p1, simp add: a1)
        subgoal for pp pp1
           using a3 augpath_split1[of f "p1" "[e]@p2"]  augpath_split2[of f "p1@[e]" p2] a2 
           by (cases p2)(simp,intro augpath_app, auto)
        done
      moreover have b:" fstv (hd (p1@p2)) = s"  
          using p1p2 less(3, 4, 2) 2  augpath_split3[of f "[e]" p2]  less.prems(1) less.prems(14) 
          by (cases p1) force+
        moreover have c:"sndv (last (p1@p2)) = t"
          using p1p2 less(3, 4, 2) 2  augpath_split3[of f p1 "[e]"]  less.prems(1) less.prems(14) 
          by (cases p2) force+
      moreover have d:"set (p1@p2) \<subseteq> \<EE>"
        using less.prems(4) p1p2 by auto
      moreover have e: "cnt_P (p1 @ p2) (\<lambda>e. e \<notin> allowed_edges) < number_not_allowed"
        apply(subst less(14), subst sym[OF p1p2(1)],
              subst cnt_P_add[of p1 "[e]@p2" "(\<lambda>e. e \<notin> allowed_edges)"], subst cnt_P_add[of "[e]" "p2" "(\<lambda>e. e \<notin> allowed_edges)"])
        apply(subst cnt_P_add, simp)
        using e_prop unfolding less by simp
      have "\<exists>qq. augpath f qq \<and> fstv (hd qq) = s \<and> sndv (last qq) = t \<and> set qq \<subseteq> allowed_edges \<and> qq \<noteq> []"
        using less(1)[of "cnt_P (p1@p2) (\<lambda> e. e \<notin> allowed_edges)" "p1@p2" s t, 
                      OF e a b c d less(6) less(7-13) _ less(15) less(16)] by simp
      thus ?thesis by simp
    next
      case 1
      obtain Q where Qpr:"walk_betw (to_graph (\<FF> state)) (fstv e) Q (sndv e)" 
        using 1 unfolding reachable_def by auto
      hence Qend:"hd Q = fstv e" "last Q = sndv e" unfolding walk_betw_def by auto
      have QQpre:"prepath (to_redge_path (conv_to_rdg state) Q)"
        using less(6)[simplified underlying_invars_def] 1(2) Qpr 
        by (auto intro: perpath_to_redgepath[of state  "fstv e" Q "sndv e"]  
              simp add: walk_betw_length)
      define QQ where "QQ= to_redge_path (conv_to_rdg state) Q"
      have Qlength: "2 \<le> length Q" 
        by (meson "1"(2) Qpr walk_betw_length)
      have QQleng:"length QQ > 0" unfolding QQ_def
        using Qlength 
        by(cases rule: list_cases4[of Q], auto) 
      have QQE: "set QQ \<subseteq> \<F>_redges state"
        unfolding QQ_def 
        using Qpr  Qlength  less(6) 
        by(unfold F_redges_def, intro concretize_walk[of state "fstv e" Q "sndv e"])
          (auto simp add:  underlying_invars_def inv_dbltn_graph_forest_def inv_digraph_abs_F_in_E_def)         
        hence QQnumber_not_allowedp: " e \<in> set QQ \<Longrightarrow> 0 < \<uu>\<^bsub>f\<^esub>e" for e
          using less(16) oedge.simps rcap.simps infinite_u 
          by(cases rule: \<cc>.cases[of e]) 
            (auto intro!: less.prems(15) rev_image_eqI[of "B _"] simp add: F_redges_def F_def) 
        have QQ_aug: "augpath f QQ"
        using QQpre  Rcap_strictI[of "set QQ" 0 f]  Rcap_strictI[of "set QQ" 0 f] QQnumber_not_allowedp QQleng
        unfolding QQ_def augpath_def by simp
      have Q_in_F: "set (edges_of_path Q) \<subseteq> to_graph (\<FF> state)"
        using Qpr by(auto intro!: path_edges_subset simp add: walk_betw_def)
      have Q_in_F_rev: "set (edges_of_path (rev Q)) \<subseteq> to_graph (\<FF> state)"
        using Qpr by(auto intro!: path_edges_subset rev_path_is_path simp add: walk_betw_def)
    have dir_edges_in_F: "set (edges_of_vwalk Q) \<subseteq> [\<FF> state]\<^sub>g"
      using forest_symmetric1 Q_in_F
      by (intro undirected_edges_subset_directed_edges_subset)
         (auto simp add:  to_graph_def intro: symmetric_digraphI)
    have rev_dir_edges_in_F: "set (edges_of_vwalk (rev Q)) \<subseteq> [\<FF> state]\<^sub>g"
      using Q_in_F_rev forest_symmetric1 
      by (intro undirected_edges_subset_directed_edges_subset)
         (auto simp add:  to_graph_def intro: symmetric_digraphI)
      have Qfirst:"fstv (hd QQ) = hd Q"
        using less(6)[simplified underlying_invars_def inv_conversion_consistent_def] Qlength dir_edges_in_F
        by(auto intro!: to_rdg_hd simp add: QQ_def) 
      have Qlast:"sndv (last QQ) = last Q" 
        using less(6)[simplified underlying_invars_def inv_conversion_consistent_def] Qlength dir_edges_in_F
        by (auto intro: to_rdg_last simp add: QQ_def)    
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
          using Qpr  Qlength  less(6) 
          by(auto simp add: underlying_invars_def inv_dbltn_graph_forest_def inv_digraph_abs_F_in_E_def)
      have D:"set (p1@QQ@p2) \<subseteq> \<EE>"
        using p1p2 less(5) QQE  by auto
      have cnt0:"cnt_P QQ (\<lambda>e. e \<notin> allowed_edges) = 0"
        apply(rule cnt_P_0)
        using concretize_walk[of state "fstv e" Q "sndv e"] Qpr  Qlength  less(6) 
        by(auto simp add: underlying_invars_def inv_dbltn_graph_forest_def inv_digraph_abs_F_in_E_def less QQ_def F_def F_redges_def)
      have E: "cnt_P (p1 @ QQ@ p2) (\<lambda>e. e \<notin> allowed_edges) < number_not_allowed"
        apply(subst less(14), subst sym[OF p1p2(1)],
              subst cnt_P_add[of p1 "[e]@p2" "(\<lambda>e. e \<notin> allowed_edges)"], subst cnt_P_add[of "[e]" "p2" "(\<lambda>e. e \<notin> allowed_edges)"])       
        apply(subst cnt_P_add, subst cnt_P_add)
        using cnt0 e_prop by(simp add: less)
      have "\<exists>qq. augpath f qq \<and> fstv (hd qq) = s \<and> sndv (last qq) = t \<and> set qq \<subseteq> allowed_edges \<and> qq \<noteq> []"
        using less(1)[of "cnt_P (p1@QQ@p2) (\<lambda> e. e \<notin> allowed_edges)" "p1@QQ@p2" s t, 
                      OF E A B C D less(6) less(7-13) _ less(15) less(16)] by simp
      then show ?thesis by simp
    qed
  qed
qed

lemma simulate_inactives_costs:
  assumes  "augpath f p" "fstv (hd p) = s" "sndv (last p) = t" "set p \<subseteq> \<EE>"
           "underlying_invars state"
           "\<FF>_state = \<FF> state"
           "f = a_current_flow state"
           "actives_state = actives state"
           "to_rdg = conv_to_rdg state"
           "\<F>_state = \<F>_redges state"
           "actives_state' = {e | e. e \<in> \<EE> \<and> oedge e \<in> to_set actives_state}"
           "allowed_edges = actives_state' \<union> \<F>_state"
           "number_not_allowed = cnt_P p (\<lambda> e. e \<notin> allowed_edges)"
           "s \<noteq> t" "\<And> e. e \<in> \<F> state \<Longrightarrow> f e > 0" "\<nexists> C. augcycle f C"
     shows "\<exists> qq.  augpath f qq \<and> fstv (hd qq) = s \<and> sndv (last qq) = t \<and> set qq \<subseteq> allowed_edges \<and>  
                       (foldr (\<lambda>x. (+) (\<cc> x)) qq 0) \<le>  (foldr (\<lambda>x. (+) (\<cc> x)) p 0) \<and> qq \<noteq> []"
  using assms
proof(induction number_not_allowed arbitrary: p s t rule: less_induct)
  case (less number_not_allowed)
  have inv_digraph_abs_\<FF>_sym: "inv_digraph_abs_\<FF>_sym state"
    using less underlying_invars_def by blast
  note forest_symmetric1 = forest_symmetic[OF inv_digraph_abs_\<FF>_sym]
  have allowed_edges_sub:"allowed_edges \<subseteq> \<EE>"
    using underlying_invars_subs less(6-13) by simp
  hence allowed_edges_finite:"finite allowed_edges"
    by (simp add: finite_\<EE> finite_subset)
  then show ?case 
  proof(cases "number_not_allowed = 0")
    case True
    hence p_allowed_edges:"set p \<subseteq> allowed_edges" 
      unfolding less 
    proof -
      assume "cnt_P p (\<lambda>e. e \<notin> {e |e. e \<in> \<EE> \<and> oedge e \<in> to_set (actives state)} \<union> \<F>_redges state) = 0"
      then have "set p \<subseteq> {r. r \<in> {r |r. r \<in> \<EE> \<and> oedge r \<in> to_set (actives state)} \<union> \<F>_redges state}"
        by (simp add: cnt_P_0_set)
      then show "set p \<subseteq> {r |r. r \<in> \<EE> \<and> oedge r \<in> to_set (actives state)} \<union> \<F>_redges state"
        by blast
    qed
    show ?thesis 
      apply(rule exI[of _ p])
      using less p_allowed_edges  augpath_cases by force
  next
    case False
    then obtain e where e_prop:"e \<in> set p" "e \<notin> \<F>_redges state"
                                "e \<notin> {e | e. e \<in> \<EE> \<and> oedge e \<in> to_set actives_state}"
      unfolding less 
      by (metis (mono_tags, lifting) Un_iff cnt_P_0)
    hence "oedge e \<in> \<E> - to_set (actives state)"
      using allowed_edges_sub less(5) less  o_edge_res by auto
    hence "connected_component (to_graph (\<FF> state)) (fst (oedge e)) 
             = connected_component (to_graph (\<FF> state)) (snd  (oedge e))"
      using less(6) 
      by (auto simp  add: underlying_invars_def inv_inactive_same_component_def less)
    hence "connected_component (to_graph (\<FF> state)) (fstv e) 
          = connected_component (to_graph (\<FF> state)) (sndv e)"
      by(cases e, auto)
    hence or_reach:"fstv e = sndv e \<or> reachable (to_graph (\<FF> state)) (fstv e) (sndv e)"
      by (metis in_connected_componentE in_connected_componentI2)  
    have e_rcap: "rcap f e > 0" 
      using augpath_rcap_pos_strict e_prop(1) less.prems(1) by blast
    obtain p1 p2 where p1p2:"p1@[e]@p2 = p"
      by (metis \<open>e \<in> set p\<close> in_set_conv_decomp_last single_in_append)
    hence costs_split: "foldr (\<lambda>x. (+) (\<cc> x)) p 0 =
                      foldr (\<lambda>x. (+) (\<cc> x)) p1 0 + \<cc> e + foldr (\<lambda>x. (+) (\<cc> x)) p2 0"
      by(induction p1, auto, metis foldr_append foldr_last_append map_sum_split)  
    have costs_split2: "foldr (\<lambda>x. (+) (\<cc> x)) (p1@p2) 0 =
                      foldr (\<lambda>x. (+) (\<cc> x)) p1 0 + foldr (\<lambda>x. (+) (\<cc> x)) p2 0"
        by(induction p1, auto)  
    show ?thesis 
    proof(cases rule: orE'[OF  Meson.disj_comm[OF or_reach]])
      case 2
      have a1: "e # p2 = p \<Longrightarrow> p1 = [] \<Longrightarrow> fstv e = sndv e \<Longrightarrow> augpath f p \<Longrightarrow> augpath f p2"
          apply(rule augpath_split2[of f "p1@[e]"])
        using p1p2 less  by auto
      have a2: "augpath f p \<Longrightarrow> p1 \<noteq> [] \<Longrightarrow> p2 \<noteq> [] \<Longrightarrow> sndv (last p1) = fstv (hd p2)"
        using 2 p1p2  augpath_split3[of f p1 "[e]@p2"] augpath_split3[of f "p1@[e]" "p2"] 
        by simp
      have a3: "p1 \<noteq>[] \<Longrightarrow> p2 = [] \<Longrightarrow> augpath f p1"
           apply(rule augpath_split1[of  f _ "[e]@p2"])
            using p1p2 less by auto
     have a:"augpath f (p1@p2)" 
        using p1p2 less(2) 2
        apply(cases p1, simp add: a1)
        subgoal for pp pp1
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
      moreover have e: "cnt_P (p1 @ p2) (\<lambda>e. e \<notin> allowed_edges) < number_not_allowed"
        apply(subst less(14), subst sym[OF p1p2(1)],
              subst cnt_P_add[of p1 "[e]@p2" "(\<lambda>e. e \<notin> allowed_edges)"], subst cnt_P_add[of "[e]" "p2" "(\<lambda>e. e \<notin> allowed_edges)"])
        apply(subst cnt_P_add, simp)
        using e_prop  less by simp
      have ce:"\<cc> e \<ge> 0"
        apply(rule ccontr, rule sufficientE[of "augcycle f [e]"])
        using less(17,2,5) e_prop(1) rcap_extr_strict[of e p 0 f] prepath_intros(1)[of e] 
              Rcap_strictI[of "set [e]" 0 f] 2 
        by(fastforce simp add: augpath_def augcycle_def \<CC>_def)+
      have F: "foldr (\<lambda>x. (+) (\<cc> x)) (p1@p2) 0 \<le> foldr (\<lambda>x. (+) (\<cc> x)) p 0"
        using costs_split2 costs_split ce by simp
     have "\<exists>qq. augpath f qq \<and> fstv (hd qq) = s \<and> sndv (last qq) = t \<and> set qq \<subseteq> allowed_edges \<and>
                foldr (\<lambda>x. (+) (\<cc> x)) qq 0 \<le> foldr (\<lambda>x. (+) (\<cc> x)) (p1@p2) 0 \<and> qq \<noteq> []"
        using less(1)[of "cnt_P (p1@p2) (\<lambda> e. e \<notin> allowed_edges)" "p1@p2" s t, 
                      OF e a b c d less(6) less(7-13) _ less(15) less(16) less(17)] by simp       
      thus ?thesis using F by auto
    next
      case 1
      obtain Q where Qpr:"walk_betw (to_graph (\<FF> state)) (fstv e) Q (sndv e)" 
        using 1  by (auto simp add: reachable_def)
      hence Qend:"hd Q = fstv e" "last Q = sndv e"  by (auto simp add: walk_betw_def)
      have QQpre:"prepath (to_redge_path (conv_to_rdg state) Q)"
        using less(6)[simplified underlying_invars_def] 1(2) Qpr 
        by (auto intro: perpath_to_redgepath[of state  "fstv e" Q "sndv e"]  
              simp add: walk_betw_length)
      define QQ where "QQ= to_redge_path (conv_to_rdg state) Q"
      have Qlength: "2 \<le> length Q" 
        by (meson "1"(2) Qpr walk_betw_length)
      have QQleng:"length QQ > 0" 
        using Qlength 
        by(cases rule: list_cases4[of Q], auto simp add: QQ_def) 
      have QQF: "set QQ \<subseteq> \<F>_redges state"
          using concretize_walk[of state "fstv e" Q "sndv e"]  Qpr  Qlength  less(6)
          by(auto simp add: underlying_invars_def inv_dbltn_graph_forest_def inv_digraph_abs_F_in_E_def  QQ_def F_def F_redges_def)
        hence QQnumber_not_allowedp: " e \<in> set QQ \<Longrightarrow> 0 < \<uu>\<^bsub>f\<^esub>e" for e
          using less(16) oedge.simps rcap.simps infinite_u 
          by (cases rule: \<cc>.cases[of e]) (force simp add: F_def F_redges_def)+
      have Q_in_F: "set (edges_of_path Q) \<subseteq> to_graph (\<FF> state)"
        using Qpr by(auto intro!: path_edges_subset simp add: walk_betw_def)
      have Q_in_F_rev: "set (edges_of_path (rev Q)) \<subseteq> to_graph (\<FF> state)"
        using Qpr by(auto intro!: path_edges_subset rev_path_is_path simp add: walk_betw_def)
    have dir_edges_in_F: "set (edges_of_vwalk Q) \<subseteq> [\<FF> state]\<^sub>g"
      using forest_symmetric1 Q_in_F
      by (intro undirected_edges_subset_directed_edges_subset)
         (auto simp add:  to_graph_def intro!: symmetric_digraphI)
    have rev_dir_edges_in_F: "set (edges_of_vwalk (rev Q)) \<subseteq> [\<FF> state]\<^sub>g"
      using Q_in_F_rev forest_symmetric1 
      by (intro undirected_edges_subset_directed_edges_subset)
         (auto simp add:  to_graph_def intro!: symmetric_digraphI)
      have Qfirst:"fstv (hd QQ) = hd Q"
        using less(6)[simplified underlying_invars_def inv_conversion_consistent_def] Qlength dir_edges_in_F
        by(auto intro!: to_rdg_hd simp add: QQ_def) 
      have Qlast:"sndv (last QQ) = last Q" 
        using less(6)[simplified underlying_invars_def inv_conversion_consistent_def] Qlength dir_edges_in_F
        by (auto intro: to_rdg_last simp add: QQ_def)
      obtain QQ' where QQ'_prop:"prepath QQ'" "distinct QQ'" "set QQ' \<subseteq> set QQ"
       "fstv (hd QQ) = fstv (hd QQ')" "sndv (last QQ) = sndv (last QQ')"  "QQ' \<noteq> []"
        using QQ_def QQpre QQleng prepath_drop_cycles[of QQ "set QQ"] by auto    
      have QQ_aug: "augpath f QQ'"
        using QQpre  Rcap_strictI[of "set QQ'" 0 f]  QQnumber_not_allowedp QQleng QQ'_prop
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
          using Qpr  Qlength  less(6)
          by(auto simp add: underlying_invars_def inv_dbltn_graph_forest_def inv_digraph_abs_F_in_E_def )
      hence QQE:"set QQ' \<subseteq> \<EE>"
          using QQ'_prop by simp
      have D:"set (p1@QQ'@p2) \<subseteq> \<EE>"
        using p1p2 less(5) QQE  by auto
      have cnt0:"cnt_P QQ (\<lambda>e. e \<notin> allowed_edges) = 0"
        using concretize_walk[of state "fstv e" Q "sndv e"] Qpr  Qlength  less(6)
        by(force intro: cnt_P_0 elim!: underlying_invarsE inv_dbltn_graph_forestE inv_digraph_abs_F_in_EE
         simp add:  less QQ_def F_def F_redges_def)
      hence cnt0:"cnt_P QQ' (\<lambda>e. e \<notin> allowed_edges) = 0" 
        using cnt_P_subset[of QQ' QQ] QQ'_prop by simp
      have E: "cnt_P (p1 @ QQ'@ p2) (\<lambda>e. e \<notin> allowed_edges) < number_not_allowed"
        apply(subst less(14), subst sym[OF p1p2(1)],
              subst cnt_P_add[of p1 "[e]@p2" "(\<lambda>e. e \<notin> allowed_edges)"], subst cnt_P_add[of "[e]" "p2" "(\<lambda>e. e \<notin> allowed_edges)"])       
        apply(subst cnt_P_add, subst cnt_P_add)
        using cnt0 e_prop unfolding less by simp
      have "\<exists>qq. augpath f qq \<and> fstv (hd qq) = s \<and> sndv (last qq) = t \<and> set qq \<subseteq> allowed_edges \<and>
                 set qq \<subseteq> allowed_edges \<and> foldr (\<lambda>x. (+) (\<cc> x)) qq 0 \<le> foldr (\<lambda>x. (+) (\<cc> x)) (p1 @ QQ' @ p2) 0 \<and> qq \<noteq> []"
        using less(1)[of "cnt_P (p1@QQ'@p2) (\<lambda> e. e \<notin> allowed_edges)" "p1@QQ'@p2" s t, 
                      OF E A B C D less(6) less(7-13) _ less(15) less(16) less(17)] by simp
      moreover have costs_split3: "foldr (\<lambda>x. (+) (\<cc> x)) (p1 @ QQ' @ p2) 0 =
             foldr (\<lambda>x. (+) (\<cc> x)) p1 0 + foldr (\<lambda>x. (+) (\<cc> x)) QQ' 0 + foldr (\<lambda>x. (+) (\<cc> x)) p2 0"
        by (metis append_eq_appendI map_sum_split)
      moreover have "foldr (\<lambda>x. (+) (\<cc> x)) QQ' 0 \<le> \<cc> e"
      proof(rule ccontr, goal_cases)
        case 1
        hence costeQQ':"foldr (\<lambda>x. (+) (\<cc> x)) QQ' 0 > \<cc> e" by simp
        define QQrev where "QQrev = rev (map erev QQ')"
        define QQp where "QQp = map blue QQrev"
        define ecc where "ecc = map red [e]"
        have markers_removeQ: "QQrev = map to_redge QQp"
              unfolding QQp_def 
              by(induction QQrev) auto
       have markers_removeP: "[e] = map to_redge ecc"
         unfolding ecc_def by simp
       have markers_remove: "QQrev @ [e] = map to_redge (QQp@ecc)"
           unfolding QQp_def 
           using markers_removeP 
           by (induction QQrev) auto
         have QQp_last:"sndvv (last QQp) = fstv (hd QQ')"
           using QQ'_prop(6) unfolding QQp_def QQrev_def 
           by(induction QQ', auto simp add: vs_erev)
         have QQp_fst:"fstvv (hd QQp) = sndv (last QQ')"
           using QQ'_prop(6) unfolding QQp_def QQrev_def 
           by(induction QQ', auto simp add: vs_erev)
         have QQrev_number_not_allowedp: "e \<in> set QQrev \<Longrightarrow> rcap f e > 0" for e
         proof(goal_cases)
           case 1
           then obtain d where dpr:"e = erev d" "d \<in> set QQ'" by(auto simp add: QQrev_def)
           hence "oedge d  \<in> \<F> state" 
             using QQ'_prop(3) QQF  by (auto simp add: F_def F_redges_def)
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
           using QQrevpre QQrev_number_not_allowedp Rcap_strictI[of "set QQrev" 0 f] 
           unfolding augpath_def by simp
       have hpath: "hpath (QQp @ ecc)"
             using QQp_last QQ'_prop(4) Qfirst Qend(1) augpathQQrev
             unfolding ecc_def QQp_def
             by(auto intro: h_path_append augpath_to_hpath_blue[of f] hpath_intros(1))
       have distinctQQrev: "distinct QQrev"
         unfolding QQrev_def
         apply(subst distinct_rev, subst distinct_map)
         using QQ'_prop(2) inj_erev unfolding inj_on_def by auto
      have distinct:"distinct (QQp @ ecc)"
           using distinct_map[of ] distinct_append distinctQQrev
           unfolding QQp_def  ecc_def is_s_t_path_def inj_on_def 
           by auto
         have to_redge_blue_id: "to_redge \<circ> blue = id"
           by auto
         have b1: "QQrev @ [e] = map to_redge (QQp @ ecc)"
          unfolding QQrev_def ecc_def QQp_def 
          by(simp, subst to_redge_blue_id, subst list.map_id0, simp)
        have b2: "e \<in> \<EE>" 
          using e_prop(1) less.prems(4) by blast
        have b2a:"set QQ \<subseteq> \<EE>"
          using QQF assms(5)  
          by(auto elim!: underlying_invarsE inv_digraph_abs_F_in_EE simp add: F_def F_redges_def)
        have b3: "set QQrev \<subseteq> \<EE>"
          using subset_trans[OF QQ'_prop(3) b2a] unfolding QQrev_def
          by(induction QQ', auto simp add: erev_\<EE>)      
      have "\<exists>blue redC.
                  Ball (set redC) precycle \<and>
                  prepath blue \<and>
                  distinct blue \<and>
                  sum cc (set (QQp@ecc)) = \<CC> blue + foldr (\<lambda>D. (+) (\<CC> D)) redC 0 \<and>
                  set (QQrev@[e]) = set blue \<union> \<Union> {set D |D. D \<in> set redC} \<and> 
                  fstv (hd blue) = sndv e \<and> sndv (last blue) = sndv e"   
        using b1  hpath  distinct b3 b2 QQp_fst QQ'_prop Qlast Qend(2) Qlast vs_erev(1)[of e]
        unfolding QQp_def QQrev_def ecc_def 
        by (intro distinct_hpath_to_distinct_augpath_and_augcycles, auto)
       then obtain P'' redC where all_props:" Ball (set redC) precycle"
                  "prepath P''"
                  "distinct P''"
                  "sum cc (set (QQp@ecc)) = \<CC> P'' + foldr (\<lambda>D. (+) (\<CC> D)) redC 0"
                  "set (QQrev@[e]) = set P'' \<union> \<Union> {set D |D. D \<in> set redC}"
                  "fstv (hd P'') = sndv e" "sndv (last P'') = sndv e" by auto
            have "sum cc (set (QQp@ecc)) = \<CC> (QQrev) + \<cc> e"
              unfolding \<CC>_def 
              using distinct_red_sum distinct_blue_sum QQp_def ecc_def
                    1 distinctQQrev
              by (subst set_append, subst sum.union_disjoint, auto)
            have costs_negated: "foldr (\<lambda>x. (+) (\<cc> x)) QQrev 0 = 
                                 - foldr (\<lambda>x. (+) (\<cc> x)) QQ' 0"
              unfolding QQrev_def
              by(induction QQ', simp, subst list.map(2), subst rev.simps(2), 
                    subst sym[OF foldr_last_append], simp add: erev_costs) 
            have below_zero:"foldr (\<lambda>x. (+) (\<cc> x)) QQrev 0 + \<cc> e < 0"
              using costeQQ' costs_negated by auto
            have sum_flod:"sum cc (set (QQp @ ecc)) = foldr (\<lambda>x. (+) (cc x))  (QQp @ ecc) 0" 
              using distinct distinct_sum2 by blast
            have "foldr (\<lambda>x. (+) (cc x))  (QQp @ ecc) 0 = foldr (\<lambda>x. (+) (\<cc> x)) QQrev 0 + \<cc> e" 
              unfolding QQp_def ecc_def
              by(induction QQrev, auto)
            then obtain C where C_prop:"(C = P'') \<or> C \<in> set redC" "\<CC> C < 0"
              using all_props(4) fold_sum_neg_neg_element[of \<CC> redC] below_zero sum_flod
              by(cases "\<CC> P''  < 0", auto)
            have Rcap_pos:"Rcap f (set C) > 0"
              using all_props(1,2) C_prop all_props(5) Rcap_union[of "set QQrev" "set [e]" 0 f]
                    QQrev_leng QQrev_number_not_allowedp Rcap_strictI[of "set QQrev" 0 f] Rcap_strictI[of "{e}" 0 f] 
                    e_rcap 
              by (intro Rcap_subset[of "set P'' \<union> \<Union> {set D |D. D \<in> set redC}" "set C"], auto simp add: precycle_def prepath_def)
            hence "augcycle f C"
              using C_prop all_props b2 b3
              unfolding augcycle_def augpath_def precycle_def  by auto
            thus False 
              using assms(16) by simp
          qed
      moreover hence "foldr (\<lambda>x. (+) (\<cc> x)) p1 0 + foldr (\<lambda>x. (+) (\<cc> x)) QQ' 0 
                                     + foldr (\<lambda>x. (+) (\<cc> x)) p2 0 \<le> 
                         foldr (\<lambda>x. (+) (\<cc> x)) p 0"
        using costs_split by auto
      ultimately show ?thesis by auto
    qed
  qed
qed

context
  includes flow_map.map.automation and bal_map.automation and rep_comp_map.map.automation and conv_map.automation
       and not_blocked_map.map.automation
begin

lemma augment_edge_impl_domain:
   "\<lbrakk>e = oedge ee; e \<in> flow_domain f; flow_invar f\<rbrakk>
    \<Longrightarrow> flow_domain (augment_edge_impl  f \<gamma> ee) = flow_domain f" 
  by(auto split: Redge.split simp add: redge_case_flip)
  
lemma augment_edge_impl_invar:
  "\<lbrakk>e = oedge ee; e \<in> flow_domain f; flow_invar f\<rbrakk>
    \<Longrightarrow> flow_invar (augment_edge_impl  f \<gamma> ee)"
  by(auto split: Redge.split simp add: redge_case_flip)

lemma augment_edge_abstract_homo:
  "\<lbrakk>e = oedge ee; e \<in> flow_domain f; flow_invar f\<rbrakk>
   \<Longrightarrow> augment_edge (abstract_flow_map f) \<gamma> ee = 
       abstract_flow_map (augment_edge_impl  f \<gamma> ee)"
  by(auto intro!: ext split: Redge.split 
     simp add: redge_case_flip  abstract_real_map_def)

lemma augment_edges_impl_domain_invar[simp]:
   "\<lbrakk>set(map oedge es) \<subseteq> flow_domain f; flow_invar f\<rbrakk>
     \<Longrightarrow>  flow_domain (augment_edges_impl  f \<gamma> es) = flow_domain f \<and>
          flow_invar (augment_edges_impl  f \<gamma> es)"
  using augment_edge_impl_domain augment_edge_impl_invar
  by(induction es)
    (auto simp add:  augment_edge_impl_domain augment_edge_impl_invar)

lemmas  augment_edges_impl_domain[simp] = conjunct1[OF augment_edges_impl_domain_invar]
lemmas  augment_edges_impl_invar[intro] = conjunct2[OF augment_edges_impl_domain_invar]

lemma augment_edges_homo[simp]:
 "\<lbrakk>set(map oedge es) \<subseteq> flow_domain f; flow_invar f\<rbrakk>
   \<Longrightarrow> abstract_flow_map (augment_edges_impl f \<gamma> es) = augment_edges (abstract_flow_map f) \<gamma> es"
  apply(rule sym)
  using augment_edges_impl_domain_invar augment_edge_abstract_homo
  by(induction es) auto

lemma flow_abstract[simp]: 
  "e \<in> flow_domain f_impl \<Longrightarrow> abstract_flow_map  f_impl e = (abstract_flow_map f_impl) e"
  by auto

lemma abstract_bal_map_homo[simp, intro]: 
 "\<lbrakk>bal_invar b;  abstract_bal_map b = b_abs\<rbrakk>
    \<Longrightarrow> abstract_bal_map (move_balance b x y) =  (\<lambda> v. if v= x then 0 
                                                       else if v = y then b_abs y + b_abs x
                                                       else b_abs v)"
  by(auto simp add: move_balance_def Let_def abstract_real_map_def)

lemma abstract_bal_invar[simp, intro]: 
  "\<lbrakk>bal_invar b; abstract_bal_map b = b_abs\<rbrakk>
    \<Longrightarrow> bal_invar (move_balance b x y)"
  by(auto simp add:  move_balance_def Let_def)

lemma abstract_bal_map_domain_exact[simp]: 
 "\<lbrakk>bal_invar b; abstract_bal_map b = b_abs\<rbrakk>
   \<Longrightarrow> bal_domain (move_balance b x y) = bal_domain b \<union> {x, y}"
  unfolding  move_balance_def Let_def
  by auto

lemma abstract_bal_map_domain[simp]: 
  "\<lbrakk>bal_invar b; x \<in> bal_domain b; y \<in> bal_domain b; abstract_bal_map b = b_abs\<rbrakk>
    \<Longrightarrow> bal_domain (move_balance b x y) = bal_domain b"
  unfolding  move_balance_def Let_def
  by auto

lemma abstract_balance[simp, intro]:  
  "\<lbrakk>x \<in> bal_domain b_impl; abstract_bal_map b_impl = b\<rbrakk>
    \<Longrightarrow> abstract_bal_map b_impl x = b x"
   by auto

lemma abstract_bal_map_homo_move_gamma[simp, intro]: 
  "\<lbrakk>bal_invar b; abstract_bal_map b =  b_abs\<rbrakk>
   \<Longrightarrow> abstract_bal_map (move b \<gamma> s t) =  (\<lambda> v. if v = s then b_abs s - \<gamma> 
                                                else if v = t then b_abs t + \<gamma>
                                                else b_abs v)"
  by(auto simp add:  move_def Let_def abstract_real_map_def)

lemma abstract_bal_invar_move[intro]: 
  "\<lbrakk>bal_invar b; b_abs = abstract_bal_map b\<rbrakk>
    \<Longrightarrow> bal_invar (move b \<gamma> x y)"
  by(auto simp add: move_def Let_def)

lemma abstract_bal_map_domain_move[simp, intro]: 
  "\<lbrakk>bal_invar b; x \<in> bal_domain b; y \<in> bal_domain b; abstract_bal_map b = b_abs\<rbrakk>
    \<Longrightarrow> bal_domain (move b \<gamma> x y) = bal_domain b"
  by(auto simp add: move_def Let_def)

lemma abstract_conv_invar[simp]: 
  "conv_invar to_rdg  \<Longrightarrow> conv_invar (add_direction to_rdg  x y e)"
  unfolding  abstract_conv_map_def add_direction_def Let_def
  by auto

lemma abstract_conv_map_domain[simp]: 
 "conv_invar to_rdg \<Longrightarrow> conv_domain (add_direction to_rdg  x y e) = 
                        conv_domain to_rdg \<union> {(x, y), (y, x)}"
  unfolding abstract_conv_map_def add_direction_def Let_def
  by auto

lemma add_direction_result: 
  assumes "conv_invar to_rdg"
  shows   "abstract_conv_map (add_direction to_rdg x y e) =
           (\<lambda> d. if d = (x, y) then F e
                 else if d = (y, x) then B e
                 else abstract_conv_map to_rdg d)"
proof-
  have conv_invar_one_step: "conv_invar (conv_update (y, x) (B e) to_rdg)"
      by (simp add: assms(1))
  show ?thesis
  unfolding abstract_conv_map_def add_direction_def
            conv_map.map_update[OF conv_invar_one_step] 
                        conv_map.map_update[OF assms(1)]
  by (auto split: if_split intro!: ext)
qed

lemma abstract_conv_map_change: 
  assumes "conv_invar to_rdg"
  shows   "abstract_conv_map (add_direction to_rdg x y e) =
            (\<lambda> d. if d = (x, y) then F e
                  else if d = (y, x) then B e
                  else abstract_conv_map to_rdg d)"
proof-
  have conv_invar_one_step: "conv_invar (conv_update (y, x) (B e) to_rdg)"
      by (simp add: assms(1))
  show ?thesis
  unfolding abstract_conv_map_def add_direction_def
            conv_map.map_update[OF conv_invar_one_step] 
                        conv_map.map_update[OF assms(1)]
  by (auto split: if_split intro!: ext)
qed

lemma abstract_conv_consist: 
  assumes "conv_invar to_rdg" "consist E (abstract_conv_map to_rdg)"
          "to_rdg' =  add_direction to_rdg x y e" "make_pair e = (x,y)" "x \<noteq> y"
    shows "consist (E \<union> {(x, y), (y, x)}) (abstract_conv_map to_rdg')"
  unfolding  add_direction_def Let_def
proof(goal_cases)
  case 1
  have conv_invar_one_step: "conv_invar (conv_update (y, x) (B e) to_rdg)"
    by (simp add: assms(1))
  show ?thesis
  proof(rule consistI, goal_cases)
    case (1 u v)
    show ?case 
    proof(cases "(u, v) \<in> {(x, y), (y, x)}")
      case True
      then show ?thesis 
        using assms(4)
        by(auto simp add: assms(3) abstract_conv_map_change[OF assms(1)])
    next
      case False
      hence a:"(u, v) \<in> E"
        using 1 by auto
        show ?thesis 
          using a assms(5,4)
         by(auto intro: consistE[OF assms(2)] 
                 simp add: assms(3) abstract_conv_map_change[OF assms(1)])
    qed
  next
    case (2 u v ee)
    then show ?case 
    proof(cases "(u, v) \<in> {(x, y), (y, x)}")
      case True
      then show ?thesis 
        using assms(5)
        by(auto simp add: assms(3) abstract_conv_map_change[OF assms(1)])
    next
      case False
      hence a:"(u, v) \<in> E"
        using 2 by auto
      show ?thesis 
        using assms(5) 2(2) a assms(2)
        by(auto simp add: abstract_conv_map_change[OF assms(1)] assms(3)
                   intro: consistE[OF assms(2)])
    qed
  qed
qed

lemma abstract_conv_homo_complex: 
  "\<lbrakk>conv_invar to_rdg; to_rdg_abs = abstract_conv_map to_rdg; 
    to_rdg'_abs = abstract_conv_map (add_direction to_rdg x y e); make_pair e = (x, y)\<rbrakk>
     \<Longrightarrow>  to_rdg'_abs = (\<lambda> d. if d = make_pair e then F e
                              else if prod.swap d = make_pair e then B e
                              else to_rdg_abs d)"
  unfolding  abstract_conv_map_def add_direction_def Let_def
  by fastforce

lemmas abstract_conv_homo[simp] = abstract_conv_homo_complex[OF _ _ refl]

lemma abstract_rep: 
  "\<lbrakk>x \<in> rep_comp_domain rc_impl; r = abstract_rep_map rc_impl\<rbrakk>
    \<Longrightarrow> abstract_rep_map rc_impl x = r x"
  unfolding abstract_rep_map_def by auto

lemma abstract_card: 
  "\<lbrakk>x \<in> rep_comp_domain rc_impl; r = abstract_comp_map rc_impl\<rbrakk>
    \<Longrightarrow> abstract_comp_map rc_impl x = r x"
  unfolding abstract_comp_map_def by auto

lemma not_in_dom_id: 
  "x \<notin> dom (rep_comp_lookup r_card_impl) \<Longrightarrow> abstract_rep_map r_card_impl x =  x" for x r_card_impl 
    by (simp add: abstract_rep_map_def domIff)
lemma not_in_dom_1:
  "x \<notin> dom (rep_comp_lookup r_card_impl) \<Longrightarrow> abstract_comp_map r_card_impl x = 1" for x r_card_impl 
  by (simp add: abstract_comp_map_def domIff)

lemma
  assumes "rep_comp_invar r_card" 
  shows  abstract_rep_map_rep_comp_upd_all:
         "abstract_rep_map (rep_comp_upd_all f r_card) x =
          (if x \<in> rep_comp_domain r_card then
           prod.fst (f x (abstract_rep_map r_card x, abstract_comp_map r_card x))
          else abstract_rep_map r_card x)"
  and abstract_comp_map_rep_comp_upd_all:
          "abstract_comp_map (rep_comp_upd_all f r_card) x =
          (if x \<in> rep_comp_domain r_card then
           prod.snd (f x (abstract_rep_map r_card x, abstract_comp_map r_card x))
          else abstract_comp_map r_card x)"
  using rep_comp_upd_all(4)[OF assms]
  apply(all \<open>cases "x \<in> rep_comp_domain r_card"\<close>)
  by (auto simp add: abstract_rep_map_def abstract_comp_map_def rep_comp_upd_all(1)[OF assms] )


lemma  reachable_to_Vs:
  assumes "reachable (to_graph E) u v"
  shows   "u \<in> Vs (to_graph E)"  "v \<in> Vs (to_graph E)"
          "u \<in> dVs (digraph_abs E)" "v \<in> dVs (digraph_abs E)"
  using reachable_in_Vs[OF assms]
  by(auto simp add: to_graph'_def Vs_def)

lemma not_blocket_update_all_abstract_not_blocked_map:
  assumes "not_blocked_invar nb"
  shows   "abstract_not_blocked_map (not_blocked_upd_all f nb) =
          (\<lambda> e. if e \<in> not_blocked_dom nb then f e (the (not_blocked_lookup nb e))
                else abstract_not_blocked_map nb e)"
  apply(rule ext)
  using not_blocked_upd_all(1,4)[OF assms]
  by(auto simp add: abstract_not_blocked_map_def) force 
end
end
end
