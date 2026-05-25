(*Authors: Mohammad Abdulaziz, Thomas Ammer, Christoph Madlener, Adem Rimpapa,*)
theory Undirected_Set_Graphs
  imports Misc
begin

section\<open>Undirected Graphs\<close>

type_synonym 'a graph = "'a set set"

subsection \<open>Vertices\<close>

definition Vs where "Vs G = \<Union> G"

lemma Vs_subset:
  "G \<subseteq> G' \<Longrightarrow> Vs G \<subseteq> Vs G'"
  by (auto simp: Vs_def)

lemma vs_member[iff?]: "v \<in> Vs G \<longleftrightarrow> (\<exists>e \<in> G. v \<in> e)"
  unfolding Vs_def by simp

lemma vs_member_elim[elim?]:
  assumes "v \<in> Vs G"
  obtains e where "v \<in> e" "e \<in> G"
  using assms
  by(auto simp: vs_member)

lemma vs_member_intro[intro]:
  "\<lbrakk>v \<in> e; e \<in> G\<rbrakk> \<Longrightarrow> v \<in> Vs G"
  using vs_member
  by force

lemma vs_transport:
  "\<lbrakk>u \<in> Vs G; \<And>e. \<lbrakk>u \<in> e; e \<in> G\<rbrakk> \<Longrightarrow> \<exists>g \<in> F. u \<in> g\<rbrakk> \<Longrightarrow>u \<in> Vs F"
  by (auto simp: vs_member)

lemma edges_are_Vs:
  assumes "{v, v'} \<in> G"
  shows "v \<in> Vs G"
  using assms by blast

lemma edges_are_Vs_2:
  assumes "{v', v} \<in> G"
  shows "v \<in> Vs G"
  using assms by blast

lemma finite_Vs_then_finite:
  assumes "finite (Vs G)"
  shows "finite G"
  using assms
  by (metis Vs_def finite_UnionD)

lemma edge_commute: "{u,v} \<in> G \<Longrightarrow> {v,u} \<in> G"
  by (simp add: insert_commute)

lemma vs_empty[simp]: "Vs {} = {}"
  by (simp add: Vs_def)

lemma vs_insert: "Vs (insert e E) = e \<union> Vs E"
  unfolding Vs_def by simp

lemma vs_union: "Vs (A \<union> B) = Vs A \<union> Vs B"
  unfolding Vs_def by simp

lemma vs_compr: "Vs {{u, v} |v. v \<in> ns} = (if ns = {} then {} else {u} \<union> ns)"
  unfolding Vs_def by auto

lemma card_Vs_diff: 
  "\<lbrakk>G \<subseteq> G'; finite (Vs G)\<rbrakk> \<Longrightarrow> card (Vs G' - Vs G) = card (Vs G') - card (Vs G)"
  by(auto intro!: card_Diff_subset[OF _ Vs_subset])

lemma in_Vs_insertE:
  "\<lbrakk>v \<in> Vs (insert e G); v \<in> e \<Longrightarrow> P; v \<in> Vs G \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: Vs_def)

lemma in_Vs_unionE:
  "\<lbrakk>v \<in> Vs (G1 \<union> G2); v \<in> Vs G1 \<Longrightarrow> P; v \<in> Vs G2 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: Vs_def)

lemma in_Vs_insert: "x \<in> Vs G \<Longrightarrow> x \<in> Vs (insert e G)"
  by (auto simp: Vs_def)

lemma vs_neq_graphs_neq:
  "\<lbrakk>x \<in> Vs G; x \<notin> Vs H\<rbrakk> \<Longrightarrow> G \<noteq> H"
  by blast

lemma subgraph_vs_subset_eq:
  assumes "M \<subseteq> G"
  assumes "Vs G \<subseteq> Vs M"
  shows "Vs G = Vs M"
  using assms
  unfolding Vs_def
  by auto

subsection \<open>Degrees\<close>

definition degree where
  "degree G v = card' ({e. v \<in> e} \<inter> G)"

lemma degree_def2: "degree G v \<equiv> card' {e \<in> G. v \<in> e}"
  unfolding degree_def
  by (simp add: Collect_conj_eq Int_commute)

lemma degree_Vs: "degree G v \<ge> 1" if "v \<in> Vs G"
proof-
  obtain e where "e \<in> G" "v \<in> e"
    using \<open>v \<in> Vs G\<close>
    by (auto simp: Vs_def)
  hence "{e} \<subseteq> {e \<in> G. v \<in> e}" by simp
  moreover have "card' {e} = 1" by (simp add: one_enat_def)
  ultimately show ?thesis
    by(fastforce dest!: card'_mono simp: degree_def2)
qed

lemma degree_not_Vs: "v \<notin> Vs G \<Longrightarrow> degree G v = 0"
  by (fastforce simp only: Vs_def degree_def)

lemma degree_insert: "\<lbrakk>v \<in> a; a \<notin> G\<rbrakk> \<Longrightarrow> degree (insert a G) v = eSuc (degree G v)"
  by (simp add: degree_def)

lemma degree_empty[simp]: "degree {} a = 0"
  unfolding degree_def by (simp add: zero_enat_def)

lemma degree_card_all:
  assumes "card G \<ge> numeral m"
  assumes "\<forall>e \<in> G. a \<in> e"
  assumes "finite G"
  shows "degree G a \<ge> numeral m"
  using assms unfolding degree_def
  by (simp add: card'_finite inf.absorb2 subsetI)

lemma subset_edges_less_degree:
  "G' \<subseteq> G \<Longrightarrow> degree G' v \<le> degree G v"
  by (auto intro: card'_mono simp: degree_def)

lemma less_edges_less_degree:
  shows "degree (G - G') v \<le> degree G v"
  by (intro subset_edges_less_degree)
     (simp add: subset_edges_less_degree)

lemma degree_insert_leq: "degree G e \<le> degree (insert e' G) e"
  by (simp add: subset_edges_less_degree subset_insertI)

lemma at_least_two_edges_degree_geq_2:
  "\<lbrakk>x \<in> e; e\<in> G;x \<in> e'; e' \<in> G; e \<noteq> e'\<rbrakk> \<Longrightarrow> degree G x \<ge> 2"
proof(goal_cases)
  case 1
  note one = this
  have collection_is:"Collect ((\<in>) x) \<inter> G \<supseteq> {e, e'}"
  proof(rule, goal_cases)
    case (1 ee)
    then show ?case 
      using one by auto
  qed
  show ?thesis
    using collection_is 
    by(auto simp add: degree_def card'_def one(5)
        intro!: order.trans[of 2 "card {e, e'}" "card (Collect ((\<in>) x) \<inter> G)"] card_mono)
qed

lemma unique_edge_degree_one:
  "\<lbrakk>x \<in> e; e\<in> G; \<And> e'. \<lbrakk>x \<in> e'; e' \<in> G\<rbrakk> \<Longrightarrow> e = e'\<rbrakk> \<Longrightarrow> degree G x = 1"
proof(goal_cases)
  case 1
  note one = this
  have collection_is:"Collect ((\<in>) x) \<inter> G = {e}"
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 e')
    then show ?case 
      using one(3)[of e'] by simp
  next
    case (2 x)
    then show ?case 
      using one(1,2) by simp
  qed
  show ?thesis
    by(auto simp add: degree_def card'_def collection_is enat_0 one_eSuc)
qed

lemma general_handshaking_lemma:
  assumes "finite (Vs G)"
  shows "sum (degree G) (Vs G) = sum card G"
  unfolding degree_def
proof(subst comm_monoid_add_class.sum.cong[OF refl,
      of "Vs G" _ "\<lambda> x. enat (card (Collect ((\<in>) x) \<inter> G))"], goal_cases)
  case 2
  show ?case 
  proof(subst enat_sum_distr, goal_cases)
    case 2
    show ?case
    proof(rule arg_cong[of _ _  enat], goal_cases)
      case 1
      have "finite G" 
        by (simp add: assms finite_Vs_then_finite)
      thus ?case
        using assms
        unfolding semiring_0_class.sum_distrib_left monoid_mult_class.mult_1_right
      proof(induction G rule: finite_induct)
        case (insert e F)
        have Vs_insert:"Vs (insert e F) = e \<union> (Vs F - e)"
          by (simp add: vs_insert)
        have finite_Vs: "finite (Vs F)"
          using insert.prems
          by (simp add: vs_insert)
        have finite_e: "finite e" 
          using Vs_insert insert.prems by force
        have finite_neighbs_of_e's_verts: "x \<in> e \<Longrightarrow> finite (Collect ((\<in>) x) \<inter> F)" for x
          by (simp add: insert.hyps(1))
        have e_not_in_collect: "e \<notin> (Collect ((\<in>) x) \<inter> F)" for x
          by (simp add: insert.hyps(2))
        have rw1:"(\<Sum>x\<in>Vs (insert e F). card ({a. x \<in> a} \<inter> insert e F)) = 
             (\<Sum>x\<in>(Vs F - e). card ({a. x \<in> a} \<inter> insert e F)) + 
             (\<Sum>x\<in> e. card ({a. x \<in> a} \<inter> insert e F))"
          using finite_Vs  finite_e unfolding Vs_insert 
          by(subst comm_monoid_add_class.sum.union_disjoint) auto 
        have rw2:"(\<Sum>x\<in>(Vs F - e). card ({a. x \<in> a} \<inter> insert e F))
                     = (\<Sum>x\<in>(Vs F - e). card ({a. x \<in> a} \<inter> F))"
          by(auto intro!: comm_monoid_add_class.sum.cong)
         have rw3:"(\<Sum>x\<in> e. card ({a. x \<in> a} \<inter> insert e F)) = 
                       (\<Sum>x\<in> e. (card ({a. x \<in> a} \<inter> F) + 1))"
          by(auto intro!: comm_monoid_add_class.sum.cong[OF refl] 
                 simp add:  card_insert_disjoint[OF
                           finite_neighbs_of_e's_verts e_not_in_collect])
       have rw4:"(\<Sum>x\<in> e. (card ({a. x \<in> a} \<inter> F) + 1)) = 
                       (\<Sum>x\<in> e. (card ({a. x \<in> a} \<inter> F))) +  card e"
          unfolding comm_monoid_add_class.sum.distrib 
          by auto
        have rw5: "sum card (insert e F) = sum card F + card e"
          by (simp add: insert.hyps(1,2))
        have rw6: "sum card F = (\<Sum>x\<in>Vs F. card ({a. x \<in> a} \<inter> F))"
          by (auto intro: insert(3)[symmetric] simp add: finite_Vs)
        have rw7: "(\<Sum>x\<in>Vs F - e. card (Collect ((\<in>) x) \<inter> F)) 
                   + (\<Sum>x\<in>e. card (Collect ((\<in>) x) \<inter> F)) =
                   (\<Sum>x\<in>Vs F. card (Collect ((\<in>) x) \<inter> F))"
          using finite_e
        proof(induction e rule: finite_induct)
          case empty
          then show ?case by simp
        next
          case (insert x e)
            have rw1: "(\<Sum>x\<in>insert x e. card ({a. x \<in> a} \<inter> F)) = 
                  (\<Sum>x\<in> e. card ({a. x \<in> a} \<inter> F)) +  card ({a. x \<in> a} \<inter> F)"
              by (simp add: insert.hyps(1,2))
          show ?case 
          proof(cases "x \<in> Vs F")
            case True
            have "(\<Sum>x\<in>Vs F - e. card (Collect ((\<in>) x) \<inter> F)) =
                 (\<Sum>x\<in>Vs F - insert x e \<union> {x}. card (Collect ((\<in>) x) \<inter> F))"
              using True insert(2) by (auto intro!: arg_cong[of _ _ "sum _ "])
            hence "(\<Sum>x\<in>Vs F - e. card (Collect ((\<in>) x) \<inter> F)) = 
                  (\<Sum>x\<in>Vs F - insert x e. card (Collect ((\<in>) x) \<inter> F))
                  + (\<Sum>x\<in>{x}. card (Collect ((\<in>) x) \<inter> F))"
              using finite_Vs by (auto simp add: sum.union_disjoint[symmetric])
            thus  ?thesis
              by(auto simp add: rw1 insert(3)[symmetric])
           next
             case False
             hence "Collect ((\<in>) x) \<inter> F = {}"
               by blast
             thus ?thesis
               using False
               by(auto simp add: rw1 insert(3)[symmetric])
          qed
        qed
        show ?case
          using rw4 rw3
          by (auto simp add: rw1 rw2 rw5 rw6 rw7)
      qed simp
    qed
  qed (simp add: assms)
qed (simp add: assms finite_Vs_then_finite)

lemma degree_neq_zeroI: "\<lbrakk>e \<in> G; v \<in> e\<rbrakk> \<Longrightarrow> degree G v \<noteq> 0"
  by (auto simp add: degree_def)

lemma degree_one_unique:
  assumes "degree G v = 1"
  shows "\<exists>!e \<in> G. v \<in> e"
  using assms
proof-
  from assms obtain e where "{e} = {e. v \<in> e} \<inter> G"
    by (fastforce simp only: degree_def elim!: card'_1_singletonE)
  thus ?thesis
    by (auto simp: exists_Unique_iff)
qed

lemma degree_inc:
  assumes "finite G1" "e \<notin> G1" "v \<in> e"
  shows "degree (insert e G1) v = degree G1 v + 1"
  using assms
  by (simp add: degree_insert eSuc_plus_1)

lemma degree_2: "\<lbrakk>{u,v} \<in> G; {v,w} \<in> G; distinct [u,v]; u \<noteq> w; v \<noteq> w\<rbrakk> \<Longrightarrow>2 \<le> degree G v"
  using degree_insert[where a = "{u,v}" and G = "G - {{u,v}}"]
  using degree_insert[where a = "{v,w}" and G = "(G - {{u,v}}) - {{v,w}}"]
  by (auto simp: degree_def doubleton_eq_iff eval_enat_numeral one_eSuc split: if_splits)

lemma degree_3:
 "\<lbrakk>{u,v} \<in> G; {v,w} \<in> G; {v, x} \<in> G; distinct [u,v,w]; u \<noteq> x; v \<noteq> x; w \<noteq> x\<rbrakk> \<Longrightarrow> 3 \<le> degree G v"
  using degree_insert[where a = "{u,v}" and G = "G - {{u,v}}"]
  using degree_insert[where a = "{v,w}" and G = "(G - {{u,v}}) - {{v,w}}"]
  using degree_insert[where a = "{v,x}" and G = "((G - {{u,v}}) - {{v,w}}) - {{v, x}}"]
  by (auto simp: degree_def doubleton_eq_iff eval_enat_numeral one_eSuc split: if_splits)


subsection \<open>Neighbours\<close>

definition "neighbourhood G v = {u. {u,v} \<in> G}"

lemma in_neighD[dest]: "v \<in> neighbourhood G u \<Longrightarrow> {u, v} \<in> G"
"v \<in> neighbourhood G u \<Longrightarrow> {v, u} \<in> G"
  by (auto simp: neighbourhood_def insert_commute)

definition "Neighbourhood G V = {v | v u. {u, v} \<in> G \<and> u \<in> V \<and> v \<notin> V}"

lemma not_in_NeighbourhoodE: 
 "v \<notin> Neighbourhood G V \<Longrightarrow>
 ((\<And> u. \<lbrakk>{u, v} \<in> G; u \<in> V; v \<notin> V\<rbrakk> \<Longrightarrow> False) \<Longrightarrow> P)
  \<Longrightarrow> P"
  by(auto simp add: Neighbourhood_def)

lemma Neighbourhood_in_G: "Neighbourhood G X \<subseteq> Vs G"
  by(auto simp add: Neighbourhood_def)

lemma in_NeighbourhoodE: 
  "\<lbrakk>y \<in> Neighbourhood G X;
    \<And> x. \<lbrakk>{x, y} \<in> G; x \<in> X; y \<notin> X\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto simp add: Neighbourhood_def)

lemma in_NeighbourhoodI: 
  "\<lbrakk>{x, y} \<in> G; x \<in> X; y \<notin> X\<rbrakk> \<Longrightarrow> y \<in> Neighbourhood G X"
  by(auto simp add: Neighbourhood_def)

lemma self_not_in_Neighbourhood:
  "x \<in> V \<Longrightarrow> x \<notin> Neighbourhood G V"
  by(auto simp add: Neighbourhood_def)

lemma Neighbourhood_neighbourhood_union_inter:
  "Neighbourhood G V = \<Union> (neighbourhood G ` V) - V"
  by(auto simp add: Neighbourhood_def neighbourhood_def insert_commute)

definition neighbours_of_Vs where
  "neighbours_of_Vs G X  = {v. \<exists> u \<in> X. \<exists> e \<in> G. v \<noteq> u \<and> u \<in> e \<and> v\<in> e}"

lemma neighbours_of_Vs_is_union:
  shows "neighbours_of_Vs G X = \<Union> {r. \<exists> x\<in>X. r = (neighbours_of_Vs G {x})}"
proof -
  show ?thesis unfolding neighbours_of_Vs_def by blast
qed

lemma neighbours_of_Vs_subset:
  assumes "A \<subseteq> X"
  shows "neighbours_of_Vs G A \<subseteq> neighbours_of_Vs G X"
  unfolding neighbours_of_Vs_def 
  by (smt (verit, best) Collect_mono assms subset_eq)

lemma neighbours_of_Vs_insert: 
  "neighbours_of_Vs M (insert x F) = neighbours_of_Vs M F \<union> neighbours_of_Vs M {x}"
  unfolding neighbours_of_Vs_def  by blast

lemma graph_subs_reach:
  assumes "M \<subseteq> G"
  shows "neighbours_of_Vs M X \<subseteq> neighbours_of_Vs G X"
  using assms subset_eq unfolding neighbours_of_Vs_def  by fastforce

lemma neighbours_of_Vs_un: 
  "neighbours_of_Vs G (Y \<union> X) = (neighbours_of_Vs G Y - neighbours_of_Vs G X) \<union> neighbours_of_Vs G X"
  unfolding neighbours_of_Vs_def using UnE by blast

definition "deltas G X = {e | u e. e \<in> G \<and> u\<in> X \<and> u \<in> e}"

lemma deltas_subset: "deltas G x \<subseteq> G"
  by(auto simp add: deltas_def)

definition "Delta G X = {{u, v} | u v. {u, v} \<in> G \<and> u \<in> X \<and> v \<notin> X}"

lemma in_DeltaI: 
  "\<lbrakk>e = {u, v}; e \<in> G; u \<in> X; v \<notin> X\<rbrakk> \<Longrightarrow> e \<in> Delta G X"
and in_DeltaE: 
  "\<lbrakk>e \<in> Delta G X; \<And> u v. \<lbrakk>e = {u, v}; e \<in> G; u \<in> X; v \<notin> X\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
and in_DeltaD: 
  "e \<in> Delta G X \<Longrightarrow> \<exists> u v. e = {u, v} \<and> u \<in> X \<and> v \<notin> X"
  "e \<in> Delta G X \<Longrightarrow> e \<in> G"
  by (auto simp add: Delta_def)

lemma Delta_finite:
  "finite G \<Longrightarrow> finite (Delta G X)"
  by(auto intro!: finite_subset[of  _ G] simp add: Delta_def)

subsection \<open>Removing Vertices\<close>

definition remove_vertices_graph :: "'a graph \<Rightarrow> 'a set \<Rightarrow> 'a graph" (infixl "\<setminus>" 60) where
  "G \<setminus> X = {e \<in> G. e \<inter> X = {}}"

lemma remove_vertices_empty[simp]:
  "G \<setminus> {} = G"
  unfolding remove_vertices_graph_def by simp

lemma remove_vertices_not_vs:
  "v \<in> X \<Longrightarrow> v \<notin> Vs (G \<setminus> X)"
  unfolding Vs_def remove_vertices_graph_def by blast

lemma remove_vertices_not_vs':
  "\<lbrakk>v \<in> X; v \<in> Vs (G \<setminus> X)\<rbrakk> \<Longrightarrow> False"
  using remove_vertices_not_vs by force

lemma remove_vertices_subgraph:
  "G \<setminus> X \<subseteq> G"
  unfolding remove_vertices_graph_def
  by simp

lemma remove_vertices_subgraph':
  "e \<in> G \<setminus> X \<Longrightarrow> e \<in> G"
  using remove_vertices_subgraph 
  by fast

lemma remove_vertices_subgraph_Vs:
  "v \<in> Vs (G \<setminus> X) \<Longrightarrow> v \<in> Vs G" 
  using Vs_subset[OF remove_vertices_subgraph]
  by fast

lemma in_remove_verticesI:
  "\<lbrakk>e \<in> G; e \<inter> X = {}\<rbrakk> \<Longrightarrow> e \<in> G \<setminus> X"
  unfolding remove_vertices_graph_def
  by blast

lemma in_remove_vertices_subsetI:
  "\<lbrakk>X' \<subseteq> X; e \<in> G \<setminus> X'; e \<inter> X - X' = {}\<rbrakk> \<Longrightarrow> e \<in> G \<setminus> X"
  unfolding remove_vertices_graph_def
  by blast

lemma in_remove_vertices_vsI:
  "\<lbrakk>e \<in> G; e \<inter> X = {}; u \<in> e\<rbrakk> \<Longrightarrow> u \<in> Vs (G \<setminus> X)"
  by (auto dest: in_remove_verticesI)

lemma remove_vertices_only_vs:
  "G \<setminus> X = G \<setminus> (X \<inter> Vs G)"
  unfolding remove_vertices_graph_def Vs_def
  by blast

lemma remove_vertices_mono:
  "\<lbrakk>G' \<subseteq> G; e \<in> G' \<setminus> X\<rbrakk> \<Longrightarrow> e \<in> G \<setminus> X"
  unfolding remove_vertices_graph_def by blast

lemma remove_vertices_inv_mono:
  "\<lbrakk>X \<subseteq> X'; e \<in> G \<setminus> X'\<rbrakk> \<Longrightarrow> e \<in> G \<setminus> X"
  unfolding remove_vertices_graph_def by blast

lemma remove_vertices_inv_mono':
  "X \<subseteq> X' \<Longrightarrow> G \<setminus> X' \<subseteq> G \<setminus> X"
  by (auto dest: remove_vertices_inv_mono)

lemma remove_vertices_graph_disjoint: "X \<inter> Vs G = {} \<Longrightarrow> G \<setminus> X = G"
  unfolding Vs_def remove_vertices_graph_def by blast

lemma remove_vertex_not_in_graph: "x \<notin> Vs G \<Longrightarrow> G \<setminus> {x} = G"
  by (auto intro!: remove_vertices_graph_disjoint)

lemma remove_vertex_psubset: "\<lbrakk>x \<in> Vs G; x \<in> X\<rbrakk> \<Longrightarrow> G \<setminus> X \<subset> G"
  by (auto intro: remove_vertices_subgraph' dest: remove_vertices_not_vs vs_neq_graphs_neq)

lemma remove_vertex_card_less: "\<lbrakk>finite G; x \<in> Vs G; x \<in> X\<rbrakk> \<Longrightarrow> card (G \<setminus> X) < card G"
  by (auto intro: psubset_card_mono intro!: remove_vertex_psubset)

lemma subgraph_remove_some_ex:
  "\<exists>x. x \<in> Vs G \<and> x \<notin> Vs M \<Longrightarrow> M \<subseteq> G \<Longrightarrow> M \<subseteq> G \<setminus> {SOME x. x \<in> Vs G \<and> x \<notin> Vs M}"
  by (auto intro: in_remove_verticesI dest!: someI_ex)

lemma finite_remove_vertices:
  "finite G \<Longrightarrow> finite (G \<setminus> X)"
  by (auto intro: finite_subset[OF remove_vertices_subgraph])

lemma remove_remove_union: "G \<setminus> X \<setminus> Y = G \<setminus> X \<union> Y"
  unfolding remove_vertices_graph_def by blast

lemma remove_vertices_in_diff: "{u,v} \<in> G \<setminus> X \<Longrightarrow> {u,v} \<notin> G \<setminus> X' \<Longrightarrow> u \<in> X' - X \<or> v \<in> X' - X"
  unfolding remove_vertices_graph_def
  by simp

subsection \<open>Subgraphs\<close>

definition "graph_inter_Vs G X = {e | e. e \<in> G \<and> e \<subseteq> X}"

lemma graph_inter_Vs_subset: "graph_inter_Vs G X \<subseteq> G" "Vs (graph_inter_Vs G X) \<subseteq> X"
  by(auto simp add: graph_inter_Vs_def  vs_member)

lemma graph_inter_subset:
  "G \<subseteq> G' \<Longrightarrow> graph_inter_Vs G X \<subseteq> graph_inter_Vs G' X"
  by(auto simp add: graph_inter_Vs_def)

subsection \<open>Bigraphs\<close>

locale graph_defs =
  fixes G :: "'a set set"

definition "dblton_graph G = (\<forall>e\<in>G. \<exists>u v. e = {u, v} \<and> u \<noteq> v)"

lemma dblton_graphE[elim]:
  assumes "dblton_graph G" "e \<in> G"
  obtains u v where "e = {u,v}" "u \<noteq> v"
  using assms
  by (auto simp: dblton_graph_def)

lemma dblton_graphI:
 assumes "\<And>e. e \<in> G \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  shows "dblton_graph G"
  using assms
  by (auto simp: dblton_graph_def)

lemma dblton_graph_finite_Vs:
 assumes "dblton_graph G"
  shows "finite G \<longleftrightarrow> finite (Vs G)"
  using assms
  by (auto simp: dblton_graph_def Vs_def dest: finite_UnionD)

lemma finite_dbl_finite_verts: "\<lbrakk>finite G; dblton_graph G\<rbrakk> \<Longrightarrow> finite (Vs G)"
  by (auto simp: Vs_def dblton_graph_def)

lemma dblton_graph_subset[intro]:
  "\<lbrakk>dblton_graph G1; G2 \<subseteq> G1\<rbrakk> \<Longrightarrow> dblton_graph G2"
  by (auto elim!: dblton_graphE intro!: dblton_graphI) 

lemma doublton_inj:
  "\<lbrakk>inj_on f (Vs E); dblton_graph E\<rbrakk> \<Longrightarrow> dblton_graph ((image f) ` E)"
proof(rule dblton_graphI, goal_cases)
  case (1 e)
  then obtain e' where e': "e' \<in> E" "e = f ` e'" by blast
  moreover then obtain u v where "e' = {u, v}" "u \<noteq> v"
    using 1(2) by auto
  moreover hence "f u \<noteq> f v"
    using e'(1) 
    by(subst inj_on_eq_iff[OF 1(1)])(auto intro: edges_are_Vs)
  ultimately show ?case 
    by auto
qed

abbreviation "graph_invar G \<equiv> dblton_graph G \<and> finite (Vs G)"

lemma graph_invar_finite_Vs:
 assumes "graph_invar G"
  shows "finite (Vs G)"
  using assms dblton_graph_finite_Vs
  by auto

lemma graph_invar_dblton:
 assumes "graph_invar G"
  shows "dblton_graph G"
  using assms dblton_graph_finite_Vs
  by auto

lemma graph_invar_finite:
 assumes "graph_invar G"
  shows "finite G"
  using assms dblton_graph_finite_Vs
  by auto
   
lemma graph_invar_subset[intro]:
  "\<lbrakk>graph_invar G1; G2 \<subseteq> G1\<rbrakk> \<Longrightarrow> graph_invar G2"
  using dblton_graph_subset
  by (metis dblton_graph_finite_Vs finite_subset)

lemma graph_invar_diff: "graph_invar G \<Longrightarrow> graph_invar (G - X)"
  using Vs_subset[of "G - X" G]
  by (auto intro!: finite_subset[of "Vs (G - X)" "Vs G"])

lemma  undirected_of_directed_of_undirected_idem: 
  "graph_invar G \<Longrightarrow> {{v1, v2} |v1 v2. (v1,v2) \<in> {(u, v). {u, v} \<in> G}} = G" 
  by fast

locale graph_abs =
  graph_defs +
  assumes graph: "graph_invar G"
begin                  

lemma finite_E: "finite G"
  using finite_UnionD graph
  unfolding Vs_def
  by blast

lemma dblton_E: "dblton_graph G"
  using finite_UnionD graph
  unfolding Vs_def
  by blast

lemma dblton_graphE[elim]:
  assumes "e \<in> G"
  obtains u v where "e = {u,v}" "u \<noteq> v"
  using dblton_graphE[OF dblton_E assms] .

lemma finite_Vs: "finite (Vs G)"
  by (simp add: graph)

lemma finite_G_Vsb: "finite (Vs G) = finite G"
  using graph
  using finite_E by auto

lemma subset_edges_G:
  "\<lbrakk>X \<subseteq> G; e \<in> X\<rbrakk> \<Longrightarrow> \<exists>u v. e = {u, v} \<and> u \<noteq> v"
  using graph by blast

end

lemma graph_abs_mono: "\<lbrakk>graph_abs G; F \<subseteq> G\<rbrakk> \<Longrightarrow> graph_abs F"
  unfolding graph_abs_def
  by (auto simp: Vs_subset rev_finite_subset)
                                              
lemma graph_invar_insert[simp]: "\<lbrakk>u \<noteq> v; graph_invar G\<rbrakk> \<Longrightarrow> graph_invar (insert {u,v} G)"
  unfolding graph_abs_def
  by (fastforce simp: Vs_def  intro!: dblton_graphI)

lemma graph_abs_empty[simp]: "graph_invar {}"
  by (simp add: dblton_graph_def)

lemma dblton_graph_union: "\<lbrakk>dblton_graph G; dblton_graph H\<rbrakk> \<Longrightarrow> dblton_graph (G \<union> H)"
  by (auto simp: graph_abs_def Vs_def dblton_graph_def)

lemma graph_invar_union: "\<lbrakk>graph_abs G; graph_abs H\<rbrakk> \<Longrightarrow> graph_abs (G \<union> H)"
  by (auto simp: graph_abs_def Vs_def dblton_graph_union)

lemma graph_invar_compr: "\<lbrakk>u \<notin> ns; finite ns\<rbrakk> \<Longrightarrow> graph_invar {{u, v} |v. v \<in> ns}"
  by (auto simp: Vs_def dblton_graph_def)

lemma graph_invar_subgraph: "\<lbrakk>graph_invar G; G' \<subseteq> G\<rbrakk> \<Longrightarrow> graph_invar G'"
  using graph_invar_subset.

lemma graph_invar_edgeD: "\<lbrakk>graph_invar G; {u,v} \<in> G\<rbrakk> \<Longrightarrow> u \<noteq> v"
  by auto

lemma graph_invar_no_edge_no_vertex:
  "\<lbrakk>graph_invar G; \<forall>v. {u,v} \<notin> G\<rbrakk> \<Longrightarrow> u \<notin> Vs G"
  unfolding graph_abs_def Vs_def
  by (auto simp: insert_commute)

lemma graph_invar_vertex_edgeE:
  assumes "graph_invar G"
  assumes "u \<in> Vs G"
  obtains v where "{u,v} \<in> G"
  using assms
  by (meson graph_invar_no_edge_no_vertex)

lemma graph_invar_vertex_edgeE':
  assumes "graph_invar G"
  assumes "v \<in> Vs G"
  obtains u where "{u,v} \<in> G"
  using assms 
  apply (auto elim!: graph_invar_vertex_edgeE dest!: edge_commute)
  by (meson edge_commute graph_invar_vertex_edgeE)

lemma card_of_non_empty_graph_geq_2:
  assumes "graph_invar G"  "G \<noteq> {}"
    shows "card (Vs G) \<ge> 2"
proof-
  obtain e where e_in_G:"e \<in> G"
    using assms(2) by auto
  then obtain u v where "e = {u, v}" "u \<noteq> v"
    using assms(1) by blast
  hence "card e = 2" by simp
  moreover have "card (Vs G) \<ge> card e"
    using e_in_G assms(1)
    by(auto intro!: card_mono)
  ultimately show ?thesis 
    by simp
qed

lemma graph_abs_no_empty:
  "graph_abs M \<Longrightarrow> {} \<notin> M"
  "\<lbrakk>graph_abs M; {} \<in> M\<rbrakk> \<Longrightarrow> False"
  by(auto simp add: graph_abs_def)

lemma finite_neighbours_of_Vs:
  assumes" M \<subseteq> G"
  assumes "graph_invar G"
  shows "finite (neighbours_of_Vs M X)" 
proof -
  have 1: "finite (Vs M)"
    by (meson Vs_subset assms(2) assms(1) finite_subset)
  have 2: "(neighbours_of_Vs M X) \<subseteq> Vs M" 
    by (smt (verit, best) mem_Collect_eq neighbours_of_Vs_def subsetI vs_member)
  then show ?thesis using  1 2 
    using finite_subset by blast
qed

lemma card_edge:
  assumes "graph_invar G" "e \<in> G"
  shows "card e = 2"
  using assms 
  by (auto simp add: assms card_2_iff dblton_graph_def)

lemma neighbours_of_Vs_remove_vert:
  assumes "graph_invar G"
  assumes "S \<inter> X = {}"
  shows "neighbours_of_Vs G X \<subseteq> S \<union> neighbours_of_Vs (G - {e. e \<in> G \<and> e \<inter> S \<noteq> {}}) X"
proof 
  fix y
  assume "y \<in> neighbours_of_Vs G X"
  then obtain x e  where x_e: "x \<in> X \<and> e \<in> G \<and> x \<noteq> y \<and> x \<in> e \<and> y \<in> e" 
    unfolding neighbours_of_Vs_def by blast
  then have e: "e = {x, y}"
    using assms(1) by fastforce
  then have "x \<notin> S" 
    using assms(2)  x_e by blast
  show "y \<in> S \<union> neighbours_of_Vs (G - {e. e \<in> G \<and> e \<inter> S \<noteq> {}}) X" 
  proof(cases "y \<in> S")
    case True
    then show ?thesis 
      by blast
  next
    case False 
    then have "e \<inter> S = {}" 
      using `x \<notin> S` e by blast
    then have "e \<notin> {e. e \<in> G \<and> e \<inter> S \<noteq> {}}" 
      using False \<open>x \<notin> S\<close> e  
      by blast  
    then show ?thesis 
      unfolding neighbours_of_Vs_def using False \<open>x \<notin> S\<close> x_e by force
  qed
qed

lemma dblton_graph_remove_vertices:
  "dblton_graph G \<Longrightarrow> dblton_graph (G \<setminus> X)"
  by (simp add: dblton_graph_def graph_invar_subgraph remove_vertices_graph_def)

lemma graph_invar_remove_vertices:
  "graph_invar G \<Longrightarrow> graph_invar (G \<setminus> X)"
  by (simp add: dblton_graph_def graph_invar_subgraph remove_vertices_graph_def)

lemma graph_invar_graph_inter_Vs:
  assumes "graph_invar G" 
  shows "graph_invar (graph_inter_Vs G X)"
  by(rule graph_invar_subset[OF assms graph_inter_Vs_subset(1)])

lemma graph_invar_deltas:
  assumes "graph_invar G" 
  shows "graph_invar (deltas G X)"
  by(rule graph_invar_subset[OF assms deltas_subset])

lemma doublton_graph_edge_card_sums:
 assumes "graph_invar G"
 shows "sum card G = 2 * card G"
  using assms 
  by(subst comm_monoid_add_class.sum.cong[OF refl, of _ _ "\<lambda> e. 2"])
    (auto intro!: card_edge)

lemma bigraph_handshaking_lemma:
  assumes "graph_invar G"
  shows "sum (degree G) (Vs G) = 2 * card G"
  using assms
  by(subst general_handshaking_lemma)
    (auto simp add: doublton_graph_edge_card_sums)

end