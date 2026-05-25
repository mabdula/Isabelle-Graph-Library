theory Jarnik_Prim
  imports Arborescense Greedoids.Greedoids_Optimisation  "HOL-Library.Product_Lexorder"
    Directed_Set_Graphs.Pair_Graph_RBT
    Undirected_Set_Graphs.Directed_Undirected
begin
hide_const RBT_Set.insert

lemmas [simp] = set_of_pair_def

section \<open>The Jarnik-Prim Algorithm for Maximum Spanning Tree\<close>

text \<open>Since Arborescences are strong exchange greedoids,
 we can use the greedy algorithm for greedoids to find a maximum weight solution.
This is also known as the Jarnik-Prim Algorithm.\<close>

locale jarnik_prim_functions_spec = 
  fixes t_set::"'T \<Rightarrow> ('a::linorder \<times> 'a) set"
    and   t_invar::"'T \<Rightarrow> bool"
    and   t_insert::"'a \<times> 'a  \<Rightarrow> 'T \<Rightarrow> 'T"
    and   t_empty::"'T"
    and   es::"('a \<times> 'a) list"
    and   seed::'a
begin

definition "JP_empty = (vset_insert seed (empty::('a \<times> color) tree), t_empty)"
fun JP_invar where  "JP_invar (vs::('a \<times> color) tree, T) = 
        (Tree2.set_tree vs = Set.insert seed (Vs (set_of_pair ` t_set T)) \<and> t_invar T \<and> vset_inv vs)"
fun JP_insert where "JP_insert (x::'a, y::'a) (vs::('a \<times> color) tree, T)
                                = (vset_insert y (vset_insert x vs), t_insert (x, y) T)"
fun JP_set where "JP_set  (vs::('a \<times> color) tree, T) = t_set T"

definition "JP_full_compl = es"
definition "JP_compl_del x xs = (filter (\<lambda> y. y \<noteq> x) xs)"
definition "JP_compl_inv xs = (distinct xs \<and> set xs \<subseteq> set es)"
definition "JP_compl_iterate  = foldr"
definition "JP_compl_set = set"
definition "JP_flaten_compl=id"

fun  JP_oracle where 
  "JP_oracle (x, y) (vs, T) = (if isin vs x \<and> \<not> isin vs y then True
                             else if isin vs y \<and> \<not> isin vs x then True
                             else False)"
end

global_interpretation basic_functions: jarnik_prim_functions_spec
  where t_empty = t_empty and t_set = t_set and t_invar=t_invar
    and t_insert=t_insert and es = es and seed = seed
  for t_empty t_set t_invar t_insert es seed
  defines JP_empty = basic_functions.JP_empty
    and   JP_insert=basic_functions.JP_insert
    and   JP_invar = basic_functions.JP_invar
    and JP_full_compl=basic_functions.JP_full_compl
    and JP_compl_del=basic_functions.JP_compl_del
    and JP_compl_inv=basic_functions.JP_compl_inv
    and JP_compl_iterate=basic_functions.JP_compl_iterate
    and JP_oracle= "basic_functions.JP_oracle"
  done

term JP_insert
term JP_oracle

global_interpretation jarnik_prim_spec: greedoid_greedy_impl_spec
  where c_impl = c_impl 
    and compl_iterate = JP_compl_iterate 
    and orcl_impl=JP_oracle
    and compl_del = JP_compl_del 
    and sol_insert = "JP_insert t_insert"
    and sol_empty = "JP_empty seed t_empty"
    and full_compl="JP_full_compl es"
  for c_impl t_insert es t_empty seed
  defines jp_candidate=jarnik_prim_spec.find_best_candidate_impl
    and jarnik_prim=jarnik_prim_spec.greedoid_greedy_impl
    and jarnik_prim_init=jarnik_prim_spec.greedoid_init
  done

definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (9, 8), (8, 1), (4,5), (5,10), (10,1)]"

definition "G = foldr (\<lambda> x tree. vset_insert x  tree) edges empty"

definition "c_list = [((0::nat, 1::nat), 1::real), ((0, 2), 0.5), ((2, 3), 5/8), ((2,4), 3), ((2,1), -1/3),
                      ((1,5), 4), ((5,8), 2), ((8,7), 0.1), ((7,1), 1.3),
                     ((7,2), 3), ((7,4), 3), ((4,3), 2), ((3,4), 1), ((3,3), 0), ((9, 8),2.5),
                      ((8, 1), 0), ((4,5), 2), ((5,10), 3), ((10,1), 1000)]"

definition "c_impl = foldr (\<lambda> xy tree. update (prod.fst xy) (prod.snd xy) tree) c_list Leaf"
value "c_impl"

definition "costs  e =  (case (lookup c_impl e) of Some c \<Rightarrow> c | None \<Rightarrow> 0)"

definition  "init = jarnik_prim_init edges 1 (vset_empty::((nat \<times> nat )\<times> color) tree)"
definition  "stree= jarnik_prim costs vset_insert init"

value "costs (10,1)"
value "costs (5,10)"
value "jp_candidate costs (fst init) (snd init)"
value "init"
value "stree"
value "inorder (snd stree)"
value "inorder (fst stree)"

locale jarnik_prim_correctness =
  jarnik_prim_functions_spec where es = "es" for es::"('a::linorder \<times> 'a) list" + 
fixes c_impl::"('a \<times>'a) \<Rightarrow> real"
assumes t_set: "t_set t_empty = {}"
  "\<And> x T. t_invar T \<Longrightarrow> t_invar (t_insert x T)"
  "\<And> x T. t_invar T \<Longrightarrow> t_set (t_insert x T) = Set.insert x (t_set T)" 
  "t_invar t_empty"
  and    es:     "distinct es"
  "\<And> x y. (x, y) \<in> set es \<Longrightarrow> (y, x) \<notin> set es"
  and    seed:   "\<exists> e \<in> set es. seed = fst e \<or> seed = snd e"
begin

definition "E = set es"
definition "abstract_E = set_of_pair ` E"
definition "cc = sum c_impl"

interpretation jp_graph: graph_abs where G = abstract_E 
  using es(2) 
  by(fastforce intro!: graph_abs.intro simp add: dblton_graph_def abstract_E_def E_def Vs_def)

definition "jp_arborescence X = ((X \<subseteq> E) \<and> jp_graph.arborescence seed (set_of_pair `X))"
definition "F = {X | X. jp_arborescence X}"
definition "orcl e X = jp_arborescence (Set.insert e X)"

lemma M1: "{} \<in> F" 
  by (simp add: F_def jp_graph.contains_empty jp_arborescence_def)

lemma M3: 
  assumes "jp_arborescence S" "jp_arborescence T" "card S < card T" 
  shows   "\<exists>e\<in>T - S. S \<union> {e} \<in> F" 
proof-
  have assms_unfolded: "S \<subseteq> E" "T \<subseteq> E" 
    "jp_graph.arborescence seed (set_of_pair `S)"
    "jp_graph.arborescence seed (set_of_pair `T)"
    using assms(1,2) by(auto simp add: jp_arborescence_def)
  have to_dbltn_inj: "inj_on (\<lambda>(x, y). {x, y}) E"
  proof(rule inj_onI, goal_cases)
    case (1 e d)
    note one=this
    show ?case 
    proof(cases e, cases d, goal_cases)
      case (1 a b aa ba)
      show ?case 
        using one es(2) by(auto simp add: E_def doubleton_eq_iff 1)
    qed
  qed
  have inj_ST:"inj_on (\<lambda>(x, y). {x, y}) S" "inj_on (\<lambda>(x, y). {x, y}) T"
    using assms_unfolded(1,2) 
    by(force intro!: inj_on_subset[OF to_dbltn_inj ])+
  have card_abstract_less:"card ((\<lambda>(x, y). {x, y}) ` S) < card ((\<lambda>(x, y). {x, y}) ` T)"
    using card_image[OF inj_ST(1)] card_image[OF inj_ST(2)] assms(3) by simp
  obtain e where e_prop:"e \<in> (\<lambda>(x, y). {x, y}) ` T - (\<lambda>(x, y). {x, y}) ` S"
    "jp_graph.arborescence seed ((\<lambda>(x, y). {x, y}) ` S \<union> {e})"
    using  jp_graph.extension_property_one[OF assms_unfolded(3,4)] card_abstract_less by auto
  then obtain x y where xy: "e = {x, y}"  "(x, y) \<in> T"
    by auto
  moreover hence "(x, y) \<notin> S"
    using e_prop(1) by auto
  ultimately have "(x, y) \<in> T - S" by auto
  moreover hence "insert (x, y) S \<subseteq> E" 
    using assms_unfolded(1,2) by blast
  moreover hence "jp_arborescence (insert (x, y) S)"
    using e_prop(2) by(simp add: jp_arborescence_def xy(1))
  ultimately show ?thesis
    by(auto simp add: F_def) 
qed

lemma jp_set_system: "set_system E F"
  by (simp add: E_def F_def jp_arborescence_def set_system_def)

lemma jp_greedoid: "greedoid E F"
  using M1 M3 jp_set_system by(auto intro!: greedoid.intro  simp add: F_def)

lemma jp_algo_axioms: "greedoid_algorithm_axioms E F orcl"
  by(auto intro: greedoid_algorithm_axioms.intro simp add: orcl_def F_def)

lemma orcl_impl_correct: 
  assumes"JP_set T \<subseteq> E"
    "e \<in> E - JP_set T"
    "JP_set T \<in> F"
    "local.JP_invar T" 
  shows"local.JP_oracle e T = orcl e (JP_set T)"
  using assms
proof(induction e, induction T, goal_cases)
  case (1 vs eds x y)
  have a1: "insert (x, y) (JP_set (vs, eds)) \<subseteq> E"
    using 1 assms(2) by auto
  have a2: "jp_graph.arborescence seed (set_of_pair ` JP_set (vs, eds))"
    using F_def 1 jp_arborescence_def by blast
  have a3:"{x, y} \<in> abstract_E"
    using 1 by(auto simp add:  abstract_E_def)
  have a4: "{x, y} \<notin> (\<lambda>(x, y). {x, y}) ` JP_set (vs, eds)" 
    using es(2) 1 by (auto simp add:  doubleton_eq_iff E_def)
  have a5: "G.isin' x vs = ( x \<in> Set.insert seed (Vs (set_of_pair ` t_set eds)))" for x
    using 1 set.set_isin by auto
  show ?case 
    using  jp_graph.arborescence_extend_one_characterisation[OF a2 a3] a4 a1 
    by(auto simp add: a5 jp_arborescence_def  orcl_def)
qed 

lemma JP_empty: "JP_set local.JP_empty = {}" "local.JP_invar local.JP_empty"
  by (auto simp add: local.JP_empty_def t_set Vs_def set.set_insert
      RBT_Set.empty_def  set.invar_empty set.invar_insert)

lemma JP_insert_invar: "local.JP_invar X \<Longrightarrow> local.JP_invar (local.JP_insert x X)"
proof(induction X, induction x, goal_cases)
  case (1 x y vs eds)
  hence known: "vset_inv vs" "t_invar eds" 
    " Pair_Graph_RBT.t_set vs = insert seed (Vs ((\<lambda>(x, y). {x, y}) ` t_set  eds))"by auto
  have " Pair_Graph_RBT.t_set (vset_insert y (vset_insert x vs)) =
    insert seed (Vs ((\<lambda>(x, y). {x, y}) ` t_set (t_insert (x, y) eds)))"
    using known(3) t_set(3)[OF known(2)] set.set_insert[OF  known(1)]
      set.set_insert[OF set.invar_insert[OF known(1)]]
    by(auto simp add: Vs_def)
  moreover have "t_invar (t_insert (x, y) eds)"
    by (simp add: known(2) t_set(2))
  moreover have "vset_inv (vset_insert y (vset_insert x vs))"
    by (simp add: known(1) set.invar_insert)
  ultimately show ?case by simp
qed

lemma JP_insert_set: "local.JP_invar X \<Longrightarrow> JP_set (local.JP_insert x X) = insert x (JP_set X)"
  by(induction X, induction x, simp add: t_set(3))

lemma JP_full_compl: "local.JP_compl_inv local.JP_full_compl"
  by (simp add: es(1) local.JP_compl_inv_def local.JP_full_compl_def)

lemma JP_initial_compl: "JP_flaten_compl local.JP_full_compl = es"
  by (simp add: JP_flaten_compl_def local.JP_full_compl_def)

lemma JP_compl_del_inv: "local.JP_compl_inv X \<Longrightarrow> local.JP_compl_inv (local.JP_compl_del x X)"
  by(auto simp add: JP_compl_inv_def JP_compl_del_def)

lemma JP_coml_del_set: "local.JP_compl_inv X \<Longrightarrow> JP_compl_set (local.JP_compl_del x X) = JP_compl_set X - {x}"
  by(auto simp add: JP_compl_inv_def JP_compl_del_def JP_compl_set_def)

lemma JP_compl_iterate:"local.JP_compl_inv X 
\<Longrightarrow> local.JP_compl_iterate f X init = foldr f (JP_flaten_compl X) init" for init
  by(auto simp add: JP_compl_iterate_def JP_flaten_compl_def)

lemma JP_compl_flaten_distinct: "local.JP_compl_inv X \<Longrightarrow> distinct (JP_flaten_compl X)"
  by(auto simp add: JP_compl_inv_def JP_flaten_compl_def)

lemma JP_compl_flaten_set: "local.JP_compl_inv X \<Longrightarrow> set (JP_flaten_compl X) = JP_compl_set X"
  by(auto simp add: JP_compl_inv_def JP_flaten_compl_def JP_compl_set_def)

lemma JP_compl_del_stable:
  assumes "local.JP_compl_inv X"  "x \<in> JP_compl_set X"
  shows "\<exists>xs1 xs2.
              JP_flaten_compl X = xs1 @ [x] @ xs2 \<and> JP_flaten_compl (local.JP_compl_del x X) = xs1 @ xs2"
proof-
  obtain xs1 xs2 where xs1xs2: "JP_flaten_compl X = xs1 @ [x] @ xs2 "
    by (metis JP_compl_flaten_set append_Cons append_Nil assms(1,2) in_set_conv_decomp_first)
  have a1: "\<forall>xa\<in>set xs1. xa \<noteq> x"
    using JP_compl_flaten_distinct assms(1) xs1xs2 by fastforce
  have a2: "\<forall>xa\<in>set xs2. xa \<noteq> x"
    using JP_compl_flaten_distinct assms(1) xs1xs2 by fastforce
  show ?thesis
    using xs1xs2 assms 
    by(auto intro!: exI[of "\<lambda> xs1. \<exists> xs2. _xs2 xs1" xs1] exI[of "\<lambda> xs2. _ xs2 \<and> _ xs2" xs2]
        simp add: JP_flaten_compl_def JP_compl_del_def JP_compl_inv_def JP_compl_set_def  
        filter_True[OF a1]  filter_True[OF a2])
qed

lemma cc_single: "c_impl x = cc {x}" 
  by(auto simp add: cc_def)

lemma basis_equiv: 
  "(basis {T | T . jp_graph.arborescence seed T}  (set_of_pair `T)  \<and> T \<subseteq> E)
   \<longleftrightarrow> basis F T" 
proof(rule sym, rule, goal_cases)
  case 1
  hence one: "T \<subseteq> E" "jp_graph.arborescence seed ((\<lambda>(x, y). {x, y}) ` T)"
    "T \<subset> S \<Longrightarrow> S \<subseteq> E \<Longrightarrow> jp_graph.arborescence seed ((\<lambda>(x, y). {x, y}) ` S) \<Longrightarrow> False" for S
    using  1[simplified F_def basis_def jp_arborescence_def] by auto
  have helper:"set_of_pair ` T \<subseteq> X \<Longrightarrow>
           x \<in> X \<Longrightarrow> x \<notin> set_of_pair ` T 
           \<Longrightarrow> jp_graph.arborescence seed X \<Longrightarrow> False" for x X
  proof(goal_cases)
    case 1
    note top=this
    hence one': "X \<subseteq> abstract_E" "(\<nexists>u c. decycle X u c)" "Vs X = connected_component X seed"
      using 1(4)[simplified jp_graph.arborescence_def jp_graph.has_no_cycle_def] by auto
    then obtain X_impl where X_impl: "X = set_of_pair ` X_impl" "X_impl \<subseteq> E"
      by(auto simp add: abstract_E_def subset_image_iff)
    have strict_subs:"T \<subset> X_impl"
    proof-
      have subs:"T \<subseteq> X_impl"
      proof(rule, goal_cases)
        case (1 e)
        then obtain u v where e:"e = (u, v)" by force
        hence uv:"{u, v} \<in> X" "{u, v} \<in> abstract_E"
          using "1" top(1)   jp_graph.has_no_cycle_indep_subset_carrier one(2) 
          by (fastforce simp add: jp_graph.arborescence_def)+
        hence "(u, v) \<in> X_impl \<or>  (v, u) \<in> X_impl"
          using X_impl(1) by (auto simp add: doubleton_eq_iff)
        hence "(u, v) \<in> X_impl" 
          using  "1"  X_impl(2) e es(2) one(1) by(auto simp add: E_def)
        then show ?case
          using e by auto
      qed
      moreover obtain u v where "x = {u, v}" "(u, v) \<in> X_impl"
        using X_impl(1) top(2) by force
      moreover hence "(u, v) \<notin> T" 
        using top(3) by auto
      ultimately show ?thesis by blast
    qed
    show ?case 
      using X_impl(1) top(4) 
      by (intro one(3)[OF strict_subs])(auto simp add: X_impl(2))
  qed 
  show ?case 
    using one(1,2) helper
    by(auto simp add:  F_def jp_arborescence_def basis_def jp_graph.arborescence_def jp_graph.has_no_cycle_def  abstract_E_def)
next
  case 2
  have two: "jp_graph.arborescence seed (set_of_pair ` T)" "T \<subseteq> E"
    "set_of_pair ` T \<subset> S \<Longrightarrow>  jp_graph.arborescence seed S \<Longrightarrow> False" for S
    using 2[simplified basis_def] by auto
  have "jp_arborescence T"
    using "2" by(auto simp add: basis_def jp_arborescence_def)
  moreover have "T \<subset> S \<Longrightarrow>  jp_arborescence S \<Longrightarrow> False" for S
  proof(goal_cases)
    case 1
    hence one_unfolded: "T \<subset> S" "S \<subseteq> E" "jp_graph.arborescence seed (set_of_pair ` S)"
      using 1[simplified jp_arborescence_def] by auto
    then obtain u v where uv:"(u, v) \<in> S" "(u, v) \<notin> T" by auto
    have strict_subset: "set_of_pair ` T \<subset> set_of_pair ` S"
    proof-
      have "set_of_pair ` T \<subseteq> set_of_pair ` S" 
        using "1"(1) by blast
      moreover have "{u, v} \<notin> set_of_pair ` T" 
      proof(rule ccontr, goal_cases)
        case 1
        hence "(v, u) \<in> T"
          using jp_graph.undirected_iff uv(2) by force
        hence "(v, u) \<in> E"
          using two(2) by force
        moreover have "(u, v) \<in> E"
          using one_unfolded(2) uv(1) by auto
        ultimately show False 
          using es(2) by(auto simp add: E_def)
      qed
      moreover have "{u, v} \<in> set_of_pair ` S"
        using uv(1) by auto
      ultimately show ?thesis by auto
    qed

    show ?case
      using one_unfolded(3) by(auto intro: two(3)[OF strict_subset])
  qed
  ultimately show ?case 
    by(auto simp add: basis_def F_def)
qed

lemma seed_in: "seed \<in> Vs abstract_E" 
  using seed by(auto simp add: abstract_E_def Vs_def E_def)

lemma strong_exchange: "strong_exchange_property E F"
proof(rule strong_exchange_propertyI, goal_cases)
  case (1 S T e)
  hence one: "S \<subseteq> E" "jp_graph.arborescence seed (set_of_pair ` S)"
    "T \<subseteq> E" "jp_graph.arborescence seed (set_of_pair ` T)"
    "S \<subseteq> T"
    "basis {uu. uu \<subseteq> E \<and> jp_graph.arborescence seed (set_of_pair ` uu)} T"
    "e \<in> E" "e \<notin> T"
    "e \<in> E"
    "S \<subseteq> E" "jp_graph.arborescence seed (insert (case e of (x, y) \<Rightarrow> {x, y}) (set_of_pair ` S))"
    using 1[simplified F_def jp_arborescence_def, simplified] by auto

  show ?case 
  proof(rule strong_exchange_propertyE[OF jp_graph.strong_exchange[OF seed_in], simplified], goal_cases)
    case 1
    note bigI=this
    have e_not_in_T:"{fst e, snd e} \<notin> set_of_pair ` T"
    proof(rule ccontr, goal_cases)
      case 1
      hence "(fst e, snd e) \<in> T\<or> (snd e, fst e) \<in> T"
        using jp_graph.undirected_iff by fastforce
      hence "(snd e, fst e) \<in> T"
        by (simp add: one(8))
      hence "(snd e, fst e) \<in> E" 
        using one(3) by auto
      then show ?case
        using E_def es(2) one(7) by auto
    qed
    have "\<exists>y\<in> set_of_pair ` T - set_of_pair ` S.
            jp_graph.arborescence seed (insert y (set_of_pair ` S)) \<and>
            jp_graph.arborescence seed (insert {fst e, snd e} (set_of_pair` T - {y}))"
      using basis_equiv  one(6)  one(7) e_not_in_T  one(11) 
      by(intro bigI[OF one(2,4), of "{fst e, snd e}"])
        (auto simp add: F_def  jp_arborescence_def  abstract_E_def
          case_prod_unfold image_mono one(5))
    then obtain d where d_prop: "d \<in> set_of_pair ` T - set_of_pair ` S"
      "jp_graph.arborescence seed (insert d (set_of_pair ` S))"
      "jp_graph.arborescence seed (insert {fst e, snd e} (set_of_pair` T - {d}))"
      by auto
    then obtain d1 d2 where d_split: "d = {d1, d2}" "(d1, d2) \<in> T - S" 
      by auto
    hence d_in_E:"(d1, d2) \<in> E"
      using one(3) by auto
    have "set_of_pair ` T - {d} = set_of_pair ` (T - {(d1, d2)})"
    proof(rule, all \<open>rule\<close>, goal_cases)
      case (1 ee)
      then obtain ee1 ee2 where ee_split:"ee = {ee1, ee2}" "(ee1, ee2) \<in> T" by auto
      moreover have "(ee1, ee2) \<noteq> (d1, d2)"
        using "1" d_split(1) ee_split(1) by blast
      ultimately show ?case by auto
    next
      case (2 ee)
      then obtain ee1 ee2 where ee_split:"ee = {ee1, ee2}" "(ee1, ee2) \<in> T"
        "(ee1, ee2) \<noteq> (d1, d2)"by auto
      hence "ee \<in> set_of_pair ` T" by auto
      moreover have "ee \<noteq> d" 
        using   d_in_E d_split(1) doubleton_eq_iff ee_split(1,2,3) es(2)  one(3)
        by(auto simp add: E_def doubleton_eq_iff)
      ultimately show ?case by simp
    qed
    hence  same_set_T:"(insert {fst e, snd e} (set_of_pair` T - {d})) 
               = (insert (set_of_pair e) (set_of_pair ` (T - {(d1, d2)})))"  by force
    have "S \<union> {(d1, d2)} \<in> F"
      using d_in_E one(1) d_prop(2) d_split  by(auto simp add: F_def jp_arborescence_def)
    moreover have "T - {(d1, d2)} \<union> {e} \<in> F" 
      using one(3) d_prop(3) d_split(1)   same_set_T
      by(auto simp add: F_def jp_arborescence_def  one(7) )
    ultimately show  ?case 
      by(auto intro!: bexI[OF _ d_split(2)])
  qed
qed

interpretation jarnik_prim: greedoid_greedy_impl
  where to_sol_set= JP_set
    and sol_inv = JP_invar
    and sol_empty= JP_empty
    and sol_insert = JP_insert
    and to_compl_set=JP_compl_set
    and compl_inv = JP_compl_inv
    and compl_del=JP_compl_del
    and full_compl=JP_full_compl
    and compl_iterate=JP_compl_iterate
    and flaten_compl=JP_flaten_compl
    and c_impl = c_impl
    and cc = cc
    and E = E
    and F = F
    and orcl=orcl
    and orcl_impl=JP_oracle
  using  jp_greedoid  jp_algo_axioms  orcl_impl_correct JP_empty  JP_insert_invar 
    JP_insert_set  JP_full_compl  JP_compl_del_inv  JP_coml_del_set  JP_compl_iterate 
    JP_compl_flaten_distinct JP_compl_flaten_set  JP_compl_del_stable  cc_single 
  by (auto intro!: greedoid_greedy_impl.intro 
      greedoid_greedy_impl_axioms.intro greedoid_algorithm.intro)

definition "final_arborescence =
 (JP_set (jarnik_prim.greedoid_greedy_impl (local.JP_empty, local.JP_full_compl)))"

lemmas jarnik_prim_gives_opt = 
  mp[OF HOL.spec[OF HOL.spec[OF iffD2[OF 
          jarnik_prim.greedoid_characterisation, OF strong_exchange]]]]

lemma modular_weight: "valid_modular_weight_func E cc"
  by (simp add: cc_def jarnik_prim.sum_is_modular)

lemma final_arborescene_is: 
  "final_arborescence = set (jarnik_prim.greedoid_greedy es cc [])"
  by (simp add: E_def JP_initial_compl es(1) final_arborescence_def jarnik_prim.same_result)

theorem jp_correctness:
  "basis F final_arborescence" (is ?thesis1)
  "\<nexists> B. basis F B \<and> cc B > cc final_arborescence" (is ?thesis2)
proof-
  have "jarnik_prim.opt_basis cc (set (jarnik_prim.greedoid_greedy es cc []))"
    using jarnik_prim_gives_opt[of cc es]  E_def es(1) modular_weight by blast
  thus ?thesis1 ?thesis2
    by(auto simp add: jarnik_prim.opt_basis_def final_arborescene_is)
qed

definition "stree_around_seed T = 
   (  connected_component abstract_E seed = connected_component (set_of_pair ` T) seed 
    \<and> jp_graph.has_no_cycle (set_of_pair ` T)
    \<and> connected (set_of_pair ` T) 
    \<and> T \<subseteq> E
   )"

lemma stree_basis: "basis F T \<longleftrightarrow> stree_around_seed T"
  by(unfold stree_around_seed_def basis_equiv[symmetric]
      jp_graph.basis_is[OF seed_in, symmetric]) simp

theorem jp_maximum_stree:
  "stree_around_seed final_arborescence"
  "\<nexists> T. stree_around_seed T \<and> cc T > cc final_arborescence"
  using jp_correctness
  by(simp_all add: stree_basis)
end
end
