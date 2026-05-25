theory WBP_Matching_Reductions_Exec
  imports Directed_Set_Graphs.More_Arith Undirected_Set_Graphs.Directed_Undirected
          Directed_Set_Graphs.Pair_Graph_RBT Graph_Algorithms_Dev.RBT_Map_Extension
          Weighted_Matchings_Reductions
begin

section \<open>Reductions for Weighted Bipartite Matching Executable\<close>

hide_const R

notation abstract_real_map ("\<Parallel>_\<Parallel>")

hide_const vertex_wrapper.the_vertex
(*TODO MOVE*)
lemma not_new_vertex_old_the_vertex:
  "\<not> is_new_bp_vertex x \<Longrightarrow> old_vertex (the_vertex x) = x"
  by(cases x) auto
(*
abbreviation "\<v>\<e>\<r>\<t>\<i> \<equiv> pick_one"
abbreviation "\<v>\<e>\<r>\<t>\<i>\<i> \<equiv> pick_another"
*)
abbreviation "parify e \<equiv> (pick_one e, pick_another e)"
abbreviation "rev_parify e \<equiv> (pick_another e, pick_one e)"
notation parify ("\<langle>_\<rangle>")
notation rev_parify ("\<langle>_\<rangle>\<^sub>R")

abbreviation "setify_weight w \<equiv> (\<lambda> e. (w (pick_one e) (pick_another e))::real)"

notation setify_weight ("\<lbrace>_\<rbrace>")

lemma abstract_real_map_of_if_map:
  "abstract_real_map (\<lambda> x. if P x then Some (f x) else g x)
  = (\<lambda> x. if P x then f x else abstract_real_map g x)"
  by(auto simp add: abstract_real_map_def)

locale Set_Iterable = 
  fixes set_invar::"'set \<Rightarrow> bool"
  and   to_set::"'set \<Rightarrow> 'a set"
  and set_fold::"('a \<Rightarrow> 'res \<Rightarrow> 'res) \<Rightarrow> 'set \<Rightarrow> 'res \<Rightarrow> 'res"
assumes set_fold:"\<And> S f acc. set_invar S \<Longrightarrow>
       \<exists> ss. to_set S = set ss \<and> distinct ss \<and>
             set_fold f S acc = foldr f ss acc"

locale Map_Iterable = 
  fixes map_invar::"'map \<Rightarrow> bool"
  and   lookup::"'map \<Rightarrow>'a \<Rightarrow> 'b option"
  and   map_fold::"('a \<Rightarrow> 'b \<Rightarrow> 'res \<Rightarrow> 'res) \<Rightarrow> 'map \<Rightarrow> 'res \<Rightarrow> 'res"
assumes "\<And> M f acc. map_invar M \<Longrightarrow>
       \<exists> ms. {(a, b) | a b. lookup M a = Some b} = set ms \<and> distinct ms \<and>
             map_fold f M acc = foldr (\<lambda> ab acc. f (fst ab) (snd ab) acc) ms acc"
subsection \<open>Function Definition\<close>
locale graph_completer_spec = 
new_graph: Pair_Graph_Specs where empty = empty
and vset_empty = vset_empty and insert=insert  +
old_graph: Pair_Graph_Specs oempty odelete olookup oinsert oisin ot_set osel oupdate 
                            oadjmap_inv ovset_empty ovset_delete ovset_inv +
vset_iterable_reals: Set_Iterable ovset_inv ot_set ovset_fold_reals +
cost_map: Map cempty cupdate cdelete clookup cinvar +
new_match_map: Map bempty bupdate bdelete blookup binvar +
old_match_map: Map obempty obupdate obdelete oblookup obinvar
for  empty::'adj2 and vset_empty::'vset2
and insert :: "'v bp_vertex_wrapper \<Rightarrow> 'vset2 \<Rightarrow> 'vset2"
and oempty odelete and olookup :: "'adj \<Rightarrow> 'v \<Rightarrow> 'vset option" and 
 oinsert oisin ot_set osel oupdate oadjmap_inv ovset_empty ovset_delete ovset_inv
and ovset_fold_reals::"('v \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'vset \<Rightarrow> real \<Rightarrow> real"
and cempty cupdate cdelete and clookup::"'cm \<Rightarrow> 'v bp_vertex_wrapper\<times>'v bp_vertex_wrapper
          \<Rightarrow> real option"
and cinvar
and bempty bupdate bdelete and blookup::"'bud \<Rightarrow> 'v bp_vertex_wrapper 
         \<Rightarrow> 'v bp_vertex_wrapper option" and binvar
and obempty obupdate obdelete and oblookup::"'obud \<Rightarrow> 'v \<Rightarrow> 'v option" and obinvar
+
fixes left right::'vset
and edge_costs::"'v\<Rightarrow>'v\<Rightarrow>real"
and vset_to_list::"'vset \<Rightarrow> 'v list"
and Gimpl::'adj
begin

definition "lsize = length (vset_to_list left)"
definition "rsize = length (vset_to_list right)"

definition "new_left_list = (map old_vertex (vset_to_list left)) @ map new_vertex [0..< rsize-lsize]"
definition "new_right_list = (map old_vertex (vset_to_list right)) @ map new_vertex [0..< lsize-rsize]"
definition "new_edge_list = [(x, y). x <- new_left_list, y<-new_right_list]"
definition "bp_perfected_exec = new_graph.from_list new_edge_list"

definition "new_left = foldl (\<lambda> L x. insert x L) vset_empty new_left_list"
definition "new_right = foldl (\<lambda> L x. insert x L) vset_empty new_right_list"

abbreviation "L \<equiv> set (vset_to_list left)"
abbreviation "R \<equiv> set (vset_to_list right)"

definition "max_abs_weight = ovset_fold_reals (\<lambda> u mx. 
                               ovset_fold_reals (\<lambda> v mx. max \<bar> edge_costs u v \<bar> mx) 
                                (old_graph.neighbourhood Gimpl u) mx) left 0"

definition "penalty_exec = ((lsize+rsize)/2*max_abs_weight+1)"

definition "new_costs_mcst (e::('v bp_vertex_wrapper \<times> 'v bp_vertex_wrapper))
                       = (if is_new_bp_vertex (fst e) \<or>
                             is_new_bp_vertex (snd e)
                          then 0
                          else (let u = (the_vertex (fst e));
                                   v = (the_vertex (snd e))
                           in 
                          (if oisin (old_graph.neighbourhood Gimpl u) v
                          then min 0 (edge_costs u v)
                          else 0)))"

definition "bp_min_costs_to_min_perfect_costs_exec =
           foldl (\<lambda> cm e. cupdate (prod.swap e) (new_costs_mcst e) 
                      (cupdate e (new_costs_mcst e) cm)) cempty new_edge_list"

definition "new_costs_mcmc (e::('v bp_vertex_wrapper \<times> 'v bp_vertex_wrapper))
                       = (if is_new_bp_vertex (fst e) \<or>
                             is_new_bp_vertex (snd e)
                          then 2*penalty_exec
                          else (let u = (the_vertex (fst e));
                                   v = (the_vertex (snd e))
                           in 
                          (if oisin (old_graph.neighbourhood Gimpl u) v
                          then (edge_costs u v)
                          else 2*penalty_exec)))"

definition "bp_min_max_card_costs_to_min_perfect_costs_exec =
            foldl (\<lambda> cm e. cupdate (prod.swap e) (new_costs_mcmc e) 
                      (cupdate e (new_costs_mcmc e) cm)) cempty new_edge_list"

definition "extract_mw_matching M =
           foldl (\<lambda> M' u. case blookup M (old_vertex u) of
                          None \<Rightarrow> M'|
                          Some vv \<Rightarrow>
                          if is_new_bp_vertex vv then M'
                          else
                          (let v = the_vertex vv
                          in (if old_graph.isin' v (old_graph.neighbourhood Gimpl u) 
                                 \<and> edge_costs u v < 0
                             then obupdate v u (obupdate u v M')
                             else M')))
                obempty (vset_to_list left)"

definition "extract_mwmc_matching M =
           foldl (\<lambda> M' u. case blookup M (old_vertex u) of
                          None \<Rightarrow> M'|
                          Some vv \<Rightarrow>
                          if is_new_bp_vertex vv then M'
                          else (let v = (the_vertex vv)
                           in if old_graph.isin' v (old_graph.neighbourhood Gimpl u) 
                          then obupdate v u (obupdate u v M')
                          else M'))
                obempty (vset_to_list left)"

lemmas [code] = 
lsize_def
rsize_def
new_left_list_def
new_right_list_def
new_edge_list_def
bp_perfected_exec_def
new_left_def
new_right_def
max_abs_weight_def
penalty_exec_def
new_costs_mcst_def
bp_min_costs_to_min_perfect_costs_exec_def
new_costs_mcmc_def
bp_min_max_card_costs_to_min_perfect_costs_exec_def
extract_mw_matching_def
extract_mwmc_matching_def

end

subsection \<open>Proofs\<close>

locale graph_completer = 
graph_completer_spec where left = left and ot_set = ot_set
for left::'vset and  ot_set::"'vset \<Rightarrow> 'v set"+
fixes G::"'v set set"
assumes 
vset: "ovset_inv V \<Longrightarrow> distinct (vset_to_list V)"
       "ovset_inv V \<Longrightarrow> set(vset_to_list V) = ot_set V"
and invar_left: "ovset_inv left"
and invar_right: "ovset_inv right"
and G: "G = { {u, v} | u v. u \<in> ot_set left \<and> (u, v) \<in> old_graph.digraph_abs Gimpl}"
       "bipartite G L R"
       "\<And> v. \<lbrakk>v\<in> ot_set left; olookup Gimpl v= Some N\<rbrakk> \<Longrightarrow> ovset_inv N"
       "old_graph.finite_vsets Gimpl"
       "L \<union> R \<subseteq> Vs G"
begin

lemma LR_is_G: "L \<union> R = Vs G"
  using G(2,5) bipartite_vs_subset by blast

lemma cards: "lsize = card L" "rsize = card R"
  by (auto simp add: distinct_card invar_left lsize_def invar_right rsize_def vset(1))+

lemma cardL_plus_cardR:"card L + card R = card (Vs G)" 
  using G(2) LR_is_G
  by(auto simp add: bipartite_def  card_Un_disjoint[symmetric])

lemma vertex_lists_correct:
 "set new_left_list = bp_perfected_L L R"
 "set new_right_list = bp_perfected_R L R"
   by(auto simp add: new_left_list_def new_right_list_def 
       bp_perfected_L_def bp_perfected_R_def cards)

lemma bp_perfected_exec_correct:
 "new_graph.graph_inv bp_perfected_exec"
 "new_graph.finite_graph bp_perfected_exec"
 "new_graph.finite_vsets bp_perfected_exec"
 "UD (new_graph.digraph_abs bp_perfected_exec) = bp_perfected_G L R"
 "t_set new_left = bp_perfected_L L R" "vset_inv new_left"
 "t_set new_right = bp_perfected_R L R"  "vset_inv new_right"
 "UD (set new_edge_list) = bp_perfected_G L R"
  by(fastforce simp add: new_graph.from_list_correct bp_perfected_exec_def bp_perfected_G_def
                            vertex_lists_correct bp_perfected_L_def bp_perfected_R_def 
                            UD_def doubleton_eq_iff new_edge_list_def
                            new_graph.vset_list_fold[OF  new_graph.vset.set.invar_empty]
                            new_graph.vset.emptyD(3)[OF refl]  new_left_def new_right_def)+

lemma finite_L: "finite L" and finite_R: "finite R"
  by simp+

lemmas bp_perfected_props = balanced_complete_bipartite_perfected[OF G(2) finite_L finite_R]

lemma bipartite_perfected: 
  "bipartite (bp_perfected_G L R) (bp_perfected_L L R) (bp_perfected_R L R)"
  using G'_bipartite G(2) by blast

definition "\<w> = setify_weight edge_costs"

lemma pick_from_e_in_G:
  assumes "{u, v} \<in> G" 
  shows "{u, v} = {pick_one {u, v}, pick_another {u, v}}"
  apply(rule pick_one_and_another_props(3)[of "{u, v}"])
  using bipartite_edgeE[OF assms G(2)] 
  by fastforce

(*TODO MOVE*)

lemma Max_of_insert_Max:
  "\<lbrakk>finite B; finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> Max (Set.insert (Max A) B ) = Max (A \<union> B)" for A B
  by(cases "B = {}")
    (auto intro: linorder_class.Max_Un[symmetric])

lemma finite_pairs_of_f_set:
  assumes "(\<And> x. x \<in> set xs \<Longrightarrow> finite (f x))" 
  shows "finite {(x, y) | x y. x \<in> set xs \<and> y \<in> f x}"
proof-
  have "{(x, y) | x y. x \<in> set xs \<and> y \<in> f x} = \<Union> ((\<lambda> x. {(x, y) | y. y \<in> f x}) ` (set xs))"
    by auto
  moreover have "finite ( \<Union> ((\<lambda> x. {(x, y) | y. y \<in> f x}) ` (set xs)))"
    using assms by(auto simp add: finite_UN)
  ultimately show ?thesis
    by simp
qed

lemma new_edge_list_is:
 "set new_edge_list = bp_perfected_L L R \<times> bp_perfected_R L R"
  by(auto simp add: new_edge_list_def  bp_perfected_L_def
 bp_perfected_R_def new_left_list_def new_right_list_def cards)

lemma in_new_edgesE: 
"(x, y) \<in> set new_edge_list \<Longrightarrow> 
(\<lbrakk>x \<in> bp_perfected_L L R; y \<in> bp_perfected_R L R; {x, y} \<in> bp_perfected_G L R\<rbrakk> \<Longrightarrow> P)
\<Longrightarrow> P"
  by(auto simp add: bp_perfected_G_def bp_perfected_R_def bp_perfected_L_def
                    new_edge_list_is doubleton_eq_iff)+

lemma not_new_vertexD:
  "\<lbrakk>\<not> is_new_bp_vertex x; x \<in> bp_perfected_L L R\<rbrakk> \<Longrightarrow> 
   \<exists> x' \<in> L. x = old_vertex x'"
  "\<lbrakk>\<not> is_new_bp_vertex x; x \<in> bp_perfected_R L R\<rbrakk> \<Longrightarrow> 
   \<exists> x' \<in> R. x = old_vertex x'"
  by(auto simp add: bp_perfected_L_def bp_perfected_R_def)

(*TODO MOVE*)
lemma double_exI:
"P x y \<Longrightarrow> \<exists> x y. P x y"
  by auto

lemma ot_set_left: "ot_set left = L"
  by (simp add: invar_left vset(2))

lemma neighbourhood_of_LD:
"\<lbrakk>old_graph.isin' y (old_graph.neighbourhood Gimpl x); x \<in> L\<rbrakk> \<Longrightarrow> {x, y} \<in> G \<and> x \<in> L \<and> y \<in> R"
proof(goal_cases)
  case 1
  have "{x, y} \<in> G \<and> x \<in> L"
    using 1
    by(auto  simp add: G(1) old_graph.neighbourhood_def old_graph.digraph_abs_def
       option.split[of "\<lambda> x. old_graph.isin' y x" _ _ "olookup Gimpl _"] ot_set_left
       old_graph.vset.set.invar_empty old_graph.vset.set.set_empty
       old_graph.vset.set.set_isin
       intro!:  double_exI[of _ x y])
  moreover hence "y \<in> R"
    using G(2)
    by(fastforce simp add: bipartite_def)
  ultimately show ?thesis
    by simp
qed

lemma not_in_neighbourhood_of_LD:
"\<lbrakk>\<not> old_graph.isin' y (old_graph.neighbourhood Gimpl x); x \<in> L\<rbrakk> \<Longrightarrow> {x, y} \<notin> G \<and> x \<in> L"
  using  G(2) neighbourhood_of_LD[of y x]
  by(auto  simp add: G(1) old_graph.neighbourhood_def old_graph.digraph_abs_def
        ot_set_left option.split[of "\<lambda> x. old_graph.not_isin' _ x" _ _ "olookup Gimpl _"]
          option.split[of "\<lambda> x. old_graph.isin' _ x" _ _ "olookup Gimpl _"]
        doubleton_eq_iff bipartite_def)

lemma uv_in_G_then_in_new_edges:
 "{u, v}\<in> G \<Longrightarrow> (old_vertex u, old_vertex v) \<in> set new_edge_list \<or>
                (old_vertex v, old_vertex u) \<in> set new_edge_list "
  by(auto simp add: new_edge_list_is bp_perfected_L_def bp_perfected_R_def
             elim!: bipartite_edgeE[OF _ G(2)])

lemma one_onleft_neighb_digraph_abs:
  "u \<in> ot_set left \<Longrightarrow> v \<in> ot_set (old_graph.neighbourhood Gimpl u)
                       \<longleftrightarrow> (u,v) \<in> old_graph.digraph_abs Gimpl"
 "\<lbrakk>u \<in> ot_set left; olookup Gimpl u = Some V\<rbrakk> \<Longrightarrow> v \<in> ot_set V
                       \<longleftrightarrow> (u,v) \<in> old_graph.digraph_abs Gimpl"
  using G(3)[of u]
  by(all \<open>cases "olookup Gimpl u"\<close>)
    (auto simp add: old_graph.neighbourhood_def
 old_graph.digraph_abs_def 
 old_graph.vset.set.invar_empty old_graph.vset.set.set_empty
      old_graph.vset.set.set_isin)

lemma directed_perfected: 
"new_graph.digraph_abs bp_perfected_exec =  bp_perfected_L L R \<times>  bp_perfected_R L R "
  using bp_perfected_exec_def new_edge_list_is new_graph.from_list_correct(4) by presburger

lemma lefts_have_neighb_set:
  assumes "u \<in> bp_perfected_L L R" 
shows "new_graph.has_neighb_set bp_perfected_exec u"
proof-
  obtain v where "{u, v} \<in> bp_perfected_G L R"
    using assms bp_perfected_exec_correct(9) complete_bipartite_G'[OF G(2) finite_L finite_R]
          finite_R'[OF G(2) finite_L finite_R] 
          perfected_vertices_empty_same[OF finite_L finite_R] 
   by(force simp add: complete_bipartite_def elim!:  in_UDE )
  hence "(u, v) \<in> set new_edge_list \<or> (v, u) \<in> set new_edge_list"
    using  directed_perfected  bp_perfected_exec_correct(9)
    by(auto elim!: in_UDE simp add: new_edge_list_is )
  hence "(u, v) \<in> set new_edge_list" 
    using  assms bipartite_perfected
    by(auto elim: in_new_edgesE simp add:  bipartite_def)
  thus ?thesis
  by(force intro!: new_graph.from_list_correct simp add:  bp_perfected_exec_def)
qed

context
  assumes symmetric_weights: "\<And> u v. {u, v} \<in> G \<Longrightarrow> edge_costs u v = edge_costs v u"
begin

 lemma w_props: 
  assumes "{u, v} \<in> G" 
  shows   "\<w> {u, v} = edge_costs u v"
  using pick_from_e_in_G[OF assms] assms
  by(auto simp add: \<w>_def doubleton_eq_iff symmetric_weights[symmetric])

lemma max_abs_weight_is: "max_abs_weight = Max ({0} \<union> { \<bar>\<w> e\<bar> | e. (e \<in> G)})"
proof-
  have one_step:"ovset_fold_reals (\<lambda>v. max \<bar>edge_costs u v\<bar>) V mx = 
        Max (Set.insert mx { \<bar>edge_costs u v\<bar> | v. v \<in> ot_set V})" 
    if asm: "ovset_inv V"for u mx V
  proof-
    obtain ss where ss: "ot_set V = set ss" "distinct ss"
       "ovset_fold_reals (\<lambda>v. max \<bar>edge_costs u v\<bar>) V mx = foldr (\<lambda>v. max \<bar>edge_costs u v\<bar>) ss mx"
      using vset_iterable_reals.set_fold[OF asm(1), of "\<lambda>v. max \<bar>edge_costs u v\<bar>" mx] by auto

    show ?thesis 
      unfolding ss 
      by(induction ss)
        (auto intro: arg_cong[of _ _ Max] simp add: linorder_class.Max_insert[symmetric] simp del: linorder_class.Max_insert)
  qed
  obtain ss where ss:"ot_set left = set ss" "distinct ss"
       "ovset_fold_reals
        (\<lambda>u. ovset_fold_reals (\<lambda>v. max \<bar>edge_costs u v\<bar>) (old_graph.neighbourhood Gimpl u)) left 0 =
       foldr (\<lambda>u. ovset_fold_reals (\<lambda>v. max \<bar>edge_costs u v\<bar>) (old_graph.neighbourhood Gimpl u)) ss 0"
    using vset_iterable_reals.set_fold[OF invar_left, of 
      "\<lambda>u. ovset_fold_reals (\<lambda>v. max \<bar>edge_costs u v\<bar>) (old_graph.neighbourhood Gimpl u)" 0] by auto
  have overall_Max: "foldr (\<lambda>u. ovset_fold_reals (\<lambda>v. max \<bar>edge_costs u v\<bar>)
                 (old_graph.neighbourhood Gimpl u)) ss acc =
    Max ({acc} \<union> { \<bar> edge_costs u v\<bar> | u v. 
           u \<in> set ss \<and> v \<in> ot_set (old_graph.neighbourhood Gimpl u)})" for acc
    using equalityD2[OF ss(1)] 
  proof(induction ss arbitrary: acc)
    case (Cons v vs)
    have vset_inv: "ovset_inv (old_graph.neighbourhood Gimpl v)"
      using Cons(2) G(3)
      by(auto simp add: old_graph.neighbourhood_def  old_graph.vset.set.invar_empty split: option.split)
    have still_subset: "set vs \<subseteq> ot_set left"
      using Cons(2) by simp
    show ?case
    proof(subst foldr.simps, subst o_apply,
         subst Cons(1)[OF still_subset], subst one_step[OF vset_inv], goal_cases)
      case 1
      show ?case
      proof(subst Max_of_insert_Max, goal_cases)
        case 1
        then show ?case
          by (simp add: G(4) old_graph.finite_neighbourhoods)
      next
        case 2
        have "finite {(u, v) | u v. u \<in> set vs \<and> v \<in> ot_set (old_graph.neighbourhood Gimpl u)}"
          by (intro finite_pairs_of_f_set)( simp add: G(4) old_graph.finite_neighbourhoods)
        moreover have "(\<lambda>e. \<bar>edge_costs (fst e) (snd e)\<bar>) `
            { (u, v) | u v. (u \<in> set vs \<and> v \<in> ot_set (old_graph.neighbourhood Gimpl u))} =
            {\<bar>edge_costs u v\<bar> | u v.  (u \<in> set vs \<and> v \<in> ot_set (old_graph.neighbourhood Gimpl u))}"
          by auto force+
        ultimately show ?case 
          by(auto dest!: finite_imageI[of _ "\<lambda> e. \<bar>edge_costs (fst e) (snd e)\<bar>"]) 
      next
        case 3
        then show ?case by simp
      next
        case 4
        then show ?case 
          by(auto intro!: arg_cong[of _ _ Max])
      qed
    qed
  qed simp
  show ?thesis
    using  G(1,4) one_onleft_neighb_digraph_abs
    unfolding max_abs_weight_def ss overall_Max
    by(auto intro!:  arg_cong[of _ _ Max]  
                     exI[of "\<lambda> e. \<bar>edge_costs u v\<bar> = \<bar>\<w> e\<bar> \<and> _ e" "{u, v}" for u v]
                     arg_cong[OF w_props[symmetric], of _ _ abs]
                     arg_cong[OF w_props, of _ _ abs]
                     exI[of "\<lambda> x. \<exists> y. _ x y", OF exI,
                       of "\<lambda> ua va. \<bar>\<w> {u, v}\<bar> = \<bar>edge_costs ua va\<bar> \<and> _ ua va" u v for u v]
             dest!:  neighbourhoodI ) 
qed

lemma penalty_exec_correct: "penalty_exec = penalty G \<w>"
  by(auto simp add: penalty_exec_def max_abs_weight_is penalty_def cards cardL_plus_cardR)


lemma bp_min_costs_to_min_perfect_costs_exec_correct:
 "cinvar bp_min_costs_to_min_perfect_costs_exec" (is ?ths1)
 "\<And> e. e \<in> bp_perfected_G L R \<Longrightarrow>
  \<lbrace>curry (abstract_real_map (clookup bp_min_costs_to_min_perfect_costs_exec))\<rbrace> e = 
  bp_min_costs_to_min_perfect_costs G \<w> e" (is "\<And> e. ?asm1 e \<Longrightarrow> ?ths2 e")
 "\<And> u v. {u, v} \<in> bp_perfected_G L R \<Longrightarrow>
  curry (abstract_real_map (clookup bp_min_costs_to_min_perfect_costs_exec)) u v = 
  curry (abstract_real_map (clookup bp_min_costs_to_min_perfect_costs_exec)) v u" 
       (is "\<And> u v. ?asm2 u v \<Longrightarrow> ?ths3 u v")
proof-
  have cinvar_pres: "cinvar cinit \<Longrightarrow>
         cinvar (foldr (\<lambda>e cm. cupdate (prod.swap e) (new_costs_mcst e) 
                          (cupdate e (new_costs_mcst e) cm)) list cinit)" for cinit list
    by(induction list)
      (auto intro: cost_map.invar_update)
  have clookup:
      "\<lbrakk>cinvar cinit; \<And> e. \<lbrakk>e \<in> set list; prod.swap e \<in> set list\<rbrakk> \<Longrightarrow> False\<rbrakk>
         \<Longrightarrow> clookup (foldr (\<lambda>e cm. cupdate (prod.swap e) (new_costs_mcst e) 
                          (cupdate e (new_costs_mcst e) cm)) list cinit)
           = (\<lambda> e. if e \<in> set list then Some (new_costs_mcst e) 
                   else if prod.swap e \<in> set list 
                   then Some (new_costs_mcst (prod.swap e)) else clookup cinit e) " for list cinit
  proof(induction list)
    case (Cons e list)
    show ?case
    proof(rule ext, goal_cases)
      case (1 e')
      show ?case 
      proof((subst cost_map.invar_update[OF cinvar_pres ] 
         cost_map.map_update cinvar_pres foldr.simps o_apply | intro TrueI Cons(2))+, goal_cases)
        case 1
        show ?case
          apply(subst Cons(1)[OF Cons(2)])
          subgoal for e
            using Cons(3)[of e] by simp
          using Cons(3) 
          by fastforce
      qed
    qed
  qed simp
  show ?ths1
    by(auto simp add: bp_min_costs_to_min_perfect_costs_exec_def
                      bp_min_costs_to_min_perfect_costs_def
                      foldl_conv_foldr cinvar_pres[OF cost_map.invar_empty])
  have new_edge_list_no_swaps:
    "\<lbrakk>e \<in> set new_edge_list; prod.swap e \<in> set new_edge_list\<rbrakk> \<Longrightarrow> False" for e
    using G(2) L'_R'_disjoint 
    by(force simp add: new_edge_list_def new_costs_mcst_def vertex_lists_correct)
    show  "\<And> u v. ?asm2 u v \<Longrightarrow> ?ths3 u v"
    unfolding bp_min_costs_to_min_perfect_costs_exec_def
              bp_min_costs_to_min_perfect_costs_def foldl_conv_foldr
              clookup[OF cost_map.invar_empty] cost_map.map_empty
  proof(subst clookup[OF cost_map.invar_empty], goal_cases)
    case (1 u v e)
    then show ?case 
      using new_edge_list_no_swaps by fastforce
  next
    case (2 u v)
    then show ?case 
  proof(subst clookup[OF cost_map.invar_empty], goal_cases)
    case (1  e)
    then show ?case 
      using new_edge_list_no_swaps by fastforce
  next
    case 2
    note two = this
    show ?case
      unfolding abstract_real_map_of_if_map  cost_map.map_empty abstract_real_map_empty curry_conv
      proof(rule P_of_ifI, goal_cases)
        case 1
        hence c1:"(u, v) \<notin> set (rev new_edge_list)" "prod.swap (u, v) \<in> set (rev new_edge_list)"
          using new_edge_list_no_swaps by fastforce+
        thus ?case 
          by simp
      next
        case 2
        hence c1: "(u, v) \<in> set (rev new_edge_list)"
          using bp_perfected_exec_correct(9)  two
          by(auto elim!: in_UDE)
        show ?case
          using c1 by simp
      qed
    qed
  qed
  show  "\<And> e. ?asm1 e \<Longrightarrow> ?ths2 e"
    unfolding bp_min_costs_to_min_perfect_costs_exec_def
              bp_min_costs_to_min_perfect_costs_def foldl_conv_foldr
              clookup[OF cost_map.invar_empty] cost_map.map_empty
  proof(subst clookup[OF cost_map.invar_empty], goal_cases)
    case (1 e)
    thus ?case
      using new_edge_list_no_swaps by fastforce
  next
    case (2 e)
    note two = this
    show ?case
      unfolding abstract_real_map_of_if_map  cost_map.map_empty abstract_real_map_empty
      proof(rule P_of_ifI, goal_cases)
        case 1
        have "is_new_bp_vertex (pick_one e) \<or> is_new_bp_vertex (pick_another e)"
          apply(rule bipartite_edgeE[OF 2 bipartite_perfected])
          subgoal for x y
          using "1" pick_one_and_another_props(3)[of e, OF exI, OF exI, of x y] 
          by(fastforce simp add: is_new_bp_vertex_def)
        done
        then show ?case 
          by(auto simp add: new_costs_mcst_def)
      next
        case 2
        have not_new_vertex:"\<not> is_new_bp_vertex (pick_one e) \<and> \<not> is_new_bp_vertex (pick_another e)"
          apply(rule bipartite_edgeE[OF two bipartite_perfected])
          subgoal for x y
          using 2 pick_one_and_another_props(3)[of e, OF exI, OF exI, of x y] 
          by(fastforce simp add: is_new_bp_vertex_def)
        done
      have the_vertex_of_e_is:
          "the_vertex ` e = {the_vertex (pick_one e), the_vertex (pick_another e)}"
      proof(rule bipartite_edgeE[OF two bipartite_perfected], goal_cases)
        case (1 x y)
        hence helper: "e = {pick_one e, pick_another e}"
          by(auto intro!: pick_one_and_another_props(3))
        show ?case 
          by(subst helper) auto
      qed
      from not_new_vertex show ?case 
        by (auto dest: new_edge_list_no_swaps , 
            auto simp add: new_costs_mcst_def the_vertex_of_e_is elim!: in_new_edgesE)
           (force dest:  not_new_vertexD not_in_neighbourhood_of_LD neighbourhood_of_LD
                         uv_in_G_then_in_new_edges 
              simp add:  w_props symmetric_weights insert_commute not_new_vertex_old_the_vertex)+
    qed
  qed
qed

lemma bp_min_max_card_to_min_perfect_costs_exec_correct:
 "cinvar bp_min_max_card_costs_to_min_perfect_costs_exec" (is ?ths1)
 "\<And> e. e \<in> bp_perfected_G L R \<Longrightarrow>
  \<lbrace>curry (abstract_real_map (clookup bp_min_max_card_costs_to_min_perfect_costs_exec))\<rbrace> e = 
  bp_min_max_card_costs_to_min_perfect_costs G \<w> e" (is "\<And> e. ?asm1 e \<Longrightarrow> ?ths2 e")
 "\<And> u v. {u, v} \<in> bp_perfected_G L R \<Longrightarrow>
  curry (abstract_real_map (clookup bp_min_max_card_costs_to_min_perfect_costs_exec)) u v = 
  curry (abstract_real_map (clookup bp_min_max_card_costs_to_min_perfect_costs_exec)) v u" 
       (is "\<And> u v. ?asm2 u v \<Longrightarrow> ?ths3 u v")
proof-
  have cinvar_pres: "cinvar cinit \<Longrightarrow>
         cinvar (foldr (\<lambda>e cm. cupdate (prod.swap e) (new_costs_mcmc e) 
                          (cupdate e (new_costs_mcmc e) cm)) list cinit)" for cinit list
    by(induction list)
      (auto intro: cost_map.invar_update)
  have clookup:
      "\<lbrakk>cinvar cinit; \<And> e. \<lbrakk>e \<in> set list; prod.swap e \<in> set list\<rbrakk> \<Longrightarrow> False\<rbrakk>
         \<Longrightarrow> clookup (foldr (\<lambda>e cm. cupdate (prod.swap e) (new_costs_mcmc e) 
                          (cupdate e (new_costs_mcmc e) cm)) list cinit)
           = (\<lambda> e. if e \<in> set list then Some (new_costs_mcmc e) 
                   else if prod.swap e \<in> set list 
                   then Some (new_costs_mcmc (prod.swap e)) else clookup cinit e) " for list cinit
  proof(induction list)
    case (Cons e list)
    show ?case
    proof(rule ext, goal_cases)
      case (1 e')
      show ?case 
      proof((subst cost_map.invar_update[OF cinvar_pres ] 
         cost_map.map_update cinvar_pres foldr.simps o_apply | intro TrueI Cons(2))+, goal_cases)
        case 1
        show ?case
          apply(subst Cons(1)[OF Cons(2)])
          subgoal for e
            using Cons(3)[of e] by simp
          using Cons(3) 
          by fastforce
      qed
    qed
  qed simp
  show ?ths1
    by(auto simp add: bp_min_max_card_costs_to_min_perfect_costs_def
                      bp_min_max_card_costs_to_min_perfect_costs_exec_def
                      foldl_conv_foldr cinvar_pres[OF cost_map.invar_empty])
  have new_edge_list_no_swaps:
    "\<lbrakk>e \<in> set new_edge_list; prod.swap e \<in> set new_edge_list\<rbrakk> \<Longrightarrow> False" for e
    using G(2) L'_R'_disjoint 
    by(force simp add: new_edge_list_def new_costs_mcst_def vertex_lists_correct)
    show  "\<And> u v. ?asm2 u v \<Longrightarrow> ?ths3 u v"
    unfolding bp_min_max_card_costs_to_min_perfect_costs_exec_def
              bp_min_max_card_costs_to_min_perfect_costs_def foldl_conv_foldr
              clookup[OF cost_map.invar_empty] cost_map.map_empty
  proof(subst clookup[OF cost_map.invar_empty], goal_cases)
    case (1 u v e)
    then show ?case 
      using new_edge_list_no_swaps by fastforce
  next
    case (2 u v)
    then show ?case 
  proof(subst clookup[OF cost_map.invar_empty], goal_cases)
    case (1  e)
    then show ?case 
      using new_edge_list_no_swaps by fastforce
  next
    case 2
    note two = this
    show ?case
      unfolding abstract_real_map_of_if_map  cost_map.map_empty abstract_real_map_empty curry_conv
      proof(rule P_of_ifI, goal_cases)
        case 1
        hence c1:"(u, v) \<notin> set (rev new_edge_list)" "prod.swap (u, v) \<in> set (rev new_edge_list)"
          using new_edge_list_no_swaps by fastforce+
        thus ?case by simp
      next
        case 2
        hence c1: "(u, v) \<in> set (rev new_edge_list)"
          using bp_perfected_exec_correct(9)  two
          by(auto elim!: in_UDE)
        show ?case
          using c1 by simp
      qed
    qed
  qed
  show  "\<And> e. ?asm1 e \<Longrightarrow> ?ths2 e"
    unfolding bp_min_max_card_costs_to_min_perfect_costs_exec_def
              bp_min_max_card_costs_to_min_perfect_costs_def foldl_conv_foldr
              clookup[OF cost_map.invar_empty] cost_map.map_empty
  proof(subst clookup[OF cost_map.invar_empty], goal_cases)
    case (1 e)
    thus ?case
      using new_edge_list_no_swaps by fastforce
  next
    case (2 e)
    note two = this
    hence ehelper: "e = {pick_one e, pick_another e}"
      using bipartite_perfected 
      by(auto elim!: bipartite_edgeE intro!: pick_one_and_another_props(3))
    show ?case
      unfolding abstract_real_map_of_if_map  cost_map.map_empty abstract_real_map_empty
      proof(rule P_of_ifI, goal_cases)
        case 1
        have helper:"is_new_bp_vertex (pick_one e) \<or> is_new_bp_vertex (pick_another e)"
          apply(rule bipartite_edgeE[OF 2 bipartite_perfected])
          subgoal for x y
          using "1" pick_one_and_another_props(3)[of e, OF exI, OF exI, of x y] 
          by(fastforce simp add: is_new_bp_vertex_def)
        done
      moreover have "(pick_another e, pick_one e) \<in> set (rev new_edge_list) \<or> 
          (pick_one e, pick_another e) \<in> set (rev new_edge_list)"
        using ehelper two
        by(auto intro:  bipartite_edgeE[OF two bipartite_perfected]
                        in_UDE[of _ _ "set new_edge_list", 
               simplified bp_perfected_exec_correct(9), of "pick_one e" "pick_another e"]) 
      ultimately show ?case 
        by(auto simp add: new_costs_mcmc_def penalty_exec_correct)
      next
        case 2
        have not_new_vertex:"\<not> is_new_bp_vertex (pick_one e) \<and> \<not> is_new_bp_vertex (pick_another e)"
          apply(rule bipartite_edgeE[OF two bipartite_perfected])
          subgoal for x y
          using 2 pick_one_and_another_props(3)[of e, OF exI, OF exI, of x y] 
          by(fastforce simp add: is_new_bp_vertex_def)
        done
      have the_vertex_of_e_is:
          "the_vertex ` e = {the_vertex (pick_one e), the_vertex (pick_another e)}"
      proof(rule bipartite_edgeE[OF two bipartite_perfected], goal_cases)
        case (1 x y)
        hence helper: "e = {pick_one e, pick_another e}"
          by(auto intro!: pick_one_and_another_props(3))
        show ?case 
          by(subst helper) auto
      qed
      from not_new_vertex show ?case 
        using two ehelper bp_perfected_exec_correct(9)[symmetric] (*ugly*)
        by (auto dest: new_edge_list_no_swaps , 
            auto  simp add: new_costs_mcmc_def the_vertex_of_e_is penalty_exec_correct 
                            symmetric_weights w_props 
               elim!: in_new_edgesE)
           (force elim: in_UDE dest: not_new_vertexD neighbourhood_of_LD not_in_neighbourhood_of_LD 
                  simp add: insert_commute)+
    qed
  qed
qed

lemma extract_mw_matching_correct:
  assumes  "\<And> u v. blookup M u = Some v \<longleftrightarrow>  blookup M v = Some u"
           "upairs_of_map (blookup M) \<subseteq> bp_perfected_G L R"
  shows "obinvar (extract_mw_matching M)"
  "upairs_of_map (oblookup (extract_mw_matching M)) = 
    project_to_old (upairs_of_map (blookup  M)) \<inter> {e |e. \<w> e < 0} \<inter> G"
proof-
  define f where "f =  (\<lambda>x y. case blookup M (old_vertex x) of None \<Rightarrow> y
               | Some vv \<Rightarrow>
                   if is_new_bp_vertex vv
                   then y
                   else let v = the_vertex vv
                        in 
                        if old_graph.isin' v (old_graph.neighbourhood Gimpl x)
                               \<and> edge_costs x v < 0 
                        then obupdate v x (obupdate x v y) else y)"
  have obinvar_iterated:
      "obinvar B \<Longrightarrow> obinvar (foldr f vs B)" for B vs
    by(induction vs )
      (auto split: option.split simp add: f_def intro: old_match_map.invar_update)
  show  "obinvar (extract_mw_matching M)"
    by(auto intro: obinvar_iterated[simplified f_def] old_match_map.invar_empty 
         simp add: extract_mw_matching_def foldl_conv_foldr)
  have operation_effect:
      "dpairs_of_map  (oblookup (foldr f vs obempty)) = 
       \<Union> {{(u, v), (v, u)} | u v. u \<in> set vs \<and> blookup M (old_vertex u) = Some (old_vertex v) 
             \<and> edge_costs u v < 0 \<and> old_graph.isin' v (old_graph.neighbourhood Gimpl u)}"
    if "distinct vs"
       "\<And> u v. \<lbrakk>u\<in> set vs; blookup M (old_vertex u) = Some (old_vertex v)\<rbrakk> \<Longrightarrow> v \<notin> set vs"
    for vs
    using that(1,2)
  proof(induction vs)
    case Nil
    then show ?case 
      by (simp add: old_match_map.map_empty dpairs_of_map_def)
  next
    case (Cons u us)
    have IH_applied: "dpairs_of_map  (oblookup (foldr f us obempty)) = 
        \<Union> {{(u, v), (v, u)} | u v. u \<in> set us \<and> blookup M (old_vertex u) = Some (old_vertex v) 
             \<and> edge_costs u v < 0 \<and> old_graph.isin' v (old_graph.neighbourhood Gimpl u)}"
    proof(rule Cons(1), goal_cases)
      case 1
      thus ?case
        using Cons(2) by simp
      next
        case (2 u v)
        thus ?case
          using Cons(3)[of u v] by simp
      qed
    show ?case 
      apply(subst foldr.simps, subst o_apply, subst f_def)
    proof(cases "blookup M (old_vertex u)", goal_cases)
      case 1
      then show ?case 
        by (auto simp add: IH_applied)
    next
      case (2 vv)
      note two = this
      show ?case 
        unfolding 2 option.case(2)
      proof(rule P_of_ifI, goal_cases)
        case 1
        then show ?case 
          using 2
          by (auto simp add: IH_applied is_new_bp_vertex_def)      
      next
        case 2
        show ?case
          unfolding Let_def
          proof(rule P_of_ifI, goal_cases)
            case 1
            have lookup_u_something:"oblookup (foldr f us obempty) u = Some b \<Longrightarrow> False" for b
            proof(goal_cases)
              case 1
              hence "(u \<in> set us \<and> blookup M (old_vertex u) = Some (old_vertex b) )
                       \<or> (b \<in> set us \<and> blookup M (old_vertex b) = Some (old_vertex u))"
                using IH_applied by(auto simp add: dpairs_of_map_def)
              thus False
                using Cons.prems(1) Cons.prems(2)[of b u] 
                by auto
            qed
            have lookup_vv_something:"\<lbrakk>oblookup (foldr f us obempty) (the_vertex vv) = Some b; the_vertex vv \<noteq> u\<rbrakk>
                      \<Longrightarrow> False" for b
           proof(goal_cases)
              case 1
              hence "((the_vertex vv) \<in> set us \<and> blookup M (old_vertex (the_vertex vv)) = Some (old_vertex b) )
                       \<or> (b \<in> set us \<and> blookup M (old_vertex b) = Some (old_vertex (the_vertex vv)))"
                using IH_applied by(auto simp add: dpairs_of_map_def)
              thus False
                using Cons.prems(1) Cons.prems(2)[of "(the_vertex vv)" b]  two
                       Cons.prems(2)[of u  "(the_vertex vv)"] not_new_vertex_old_the_vertex[OF 2]
                by (auto simp add: assms)
            qed
            have pairs_helper:
               "dpairs_of_map ((oblookup (foldr f us obempty))(u \<mapsto> the_vertex vv, the_vertex vv \<mapsto> u)) =
                 {(u, the_vertex vv), (the_vertex vv, u)} \<union> (dpairs_of_map (oblookup (foldr f us obempty)))"
            proof(rule, goal_cases)
              case 1
              show ?case
              using  Cons.prems(1)
              by(auto simp add: dpairs_of_map_def if_split[of "\<lambda> x. x= Some _"] )
          next
            case 2
            show ?case
             by(auto simp add: dpairs_of_map_def dest!: lookup_u_something lookup_vv_something)
         qed
          show ?case 
          by(subst old_match_map.map_update)
            (auto simp add: obinvar_iterated old_match_map.invar_update old_match_map.map_update
                            "2" not_new_vertex_old_the_vertex two 1  
                             pairs_helper IH_applied obinvar_iterated old_match_map.invar_empty
              intro!: exI[of _ "{(u, the_vertex vv), (the_vertex vv, u)}"] 
                      double_exI[of _ u "the_vertex vv"])
      next
        case 2
        show ?case
          using 2 two
          by (auto simp add: IH_applied is_new_bp_vertex_def)      
      qed
      qed
    qed
  qed
  show  "upairs_of_map (oblookup (extract_mw_matching M)) = 
    project_to_old (upairs_of_map (blookup  M)) \<inter> {e |e. \<w> e < 0} \<inter> G"
    unfolding extract_mw_matching_def foldl_conv_foldr f_def[symmetric]
              upairs_dpairs_of_map
  proof(subst operation_effect, goal_cases)
    case 1
    then show ?case 
      by (simp add: invar_left vset(1))
  next
    case (2 u v)
    hence a1:"old_vertex u \<in> bp_perfected_L L R"
      by (simp add: bp_perfected_L_def)
    hence a2: "{old_vertex u, old_vertex v} \<in> bp_perfected_G L R"
      using assms(2) 2 by(auto simp add: upairs_of_map_def)
    have a3: "old_vertex v \<in> bp_perfected_R L R" 
      using bipartite_edgeD[OF a2 bipartite_perfected] a1
      by (auto simp add: doubleton_eq_iff)
    then show ?case
      using bipartite_disjointD[OF G(2)] not_new_vertexD(2)[of "old_vertex v"] 
      by auto
  next
    case 3
    have helper:"\<lbrakk>old_graph.isin' va (old_graph.neighbourhood Gimpl ua);
           ua \<in> L\<rbrakk> \<Longrightarrow> {ua, va} \<in> G" for ua va
    proof(goal_cases)
      case 1
      hence "ua \<in> ot_set left \<and> (ua, va) \<in> old_graph.digraph_abs Gimpl"
        using G(3) ot_set_left one_onleft_neighb_digraph_abs(1)[of ua va]
        by (simp add: old_graph.digraph_abs_def)
      thus ?case
        by(auto simp add: G(1)) 
    qed
    show ?case
    proof(rule, all \<open>rule\<close>, goal_cases)
      case (1 e)
      thus ?case
        by(auto simp add: project_to_old_def UD_def dpairs_of_map_def insert_commute w_props
                     intro!: exI[of _ "old_vertex ` e"] dest!: helper)
    next
      case (2 e)
      then obtain u v where uv: "e = {the_vertex u, the_vertex v}"
        by(auto simp add: project_to_old_def UD_def)
      have Ghelper: "\<lbrakk>u\<in>L; {u, v} \<in> G\<rbrakk> \<Longrightarrow>
         old_graph.isin' v (old_graph.neighbourhood Gimpl u)" for u v
        using not_in_neighbourhood_of_LD by auto
      obtain u v where  "e = {the_vertex u, the_vertex v}" "the_vertex u \<in> L" "the_vertex v \<in> R"
        apply(rule bipartite_edgeE[OF _ G(2), of e])
        using 2 
       by (auto simp add: uv  doubleton_eq_iff )
      thus ?case
        using 2 
        by (auto simp add: doubleton_eq_iff insert_commute
                           no_new_vertex_old_vertex_new_vertex_inverse w_props assms(1)
                           project_to_old_def UD_def dpairs_of_map_def
                   intro!: double_exI[of _  "the_vertex u" "the_vertex v"] Ghelper
                           exI[of _ "{(the_vertex u, the_vertex v), (the_vertex v, the_vertex u)}"])
    qed
  qed
qed

lemma extract_mwmc_matching_correct:
  assumes  "\<And> u v. blookup M u = Some v \<longleftrightarrow>  blookup M v = Some u"
           "upairs_of_map (blookup M) \<subseteq> bp_perfected_G L R"
  shows "obinvar (extract_mwmc_matching M)"
  "upairs_of_map (oblookup (extract_mwmc_matching M)) = 
    project_to_old (upairs_of_map (blookup  M)) \<inter> G"
proof-
  define f where "f =   (\<lambda> u M'. case blookup M (old_vertex u) of
                          None \<Rightarrow> M'|
                          Some vv \<Rightarrow>
                          if is_new_bp_vertex vv then M'
                          else (let v = (the_vertex vv)
                           in if old_graph.isin' v (old_graph.neighbourhood Gimpl u) 
                          then obupdate v u (obupdate u v M')
                          else M'))"
  have obinvar_iterated:
      "obinvar B \<Longrightarrow> obinvar (foldr f vs B)" for B vs
    by(induction vs )
      (auto split: option.split simp add: f_def intro: old_match_map.invar_update)
  show  "obinvar (extract_mwmc_matching M)"
    by(auto intro: obinvar_iterated[simplified f_def] old_match_map.invar_empty 
         simp add: extract_mwmc_matching_def foldl_conv_foldr)
  have operation_effect:
      "dpairs_of_map  (oblookup (foldr f vs obempty)) = 
       \<Union> {{(u, v), (v, u)} | u v. u \<in> set vs \<and> blookup M (old_vertex u) = Some (old_vertex v) 
             \<and> old_graph.isin' v (old_graph.neighbourhood Gimpl u)}"
    if "distinct vs"
       "\<And> u v. \<lbrakk>u\<in> set vs; blookup M (old_vertex u) = Some (old_vertex v)\<rbrakk> \<Longrightarrow> v \<notin> set vs"
    for vs
    using that(1,2)
  proof(induction vs)
    case Nil
    then show ?case 
      by (simp add: old_match_map.map_empty dpairs_of_map_def)
  next
    case (Cons u us)
    have IH_applied: "dpairs_of_map  (oblookup (foldr f us obempty)) = 
        \<Union> {{(u, v), (v, u)} | u v. u \<in> set us \<and> blookup M (old_vertex u) = Some (old_vertex v) 
             \<and>  old_graph.isin' v (old_graph.neighbourhood Gimpl u)}"
    proof(rule Cons(1), goal_cases)
      case 1
      thus ?case
        using Cons(2) by simp
      next
        case (2 u v)
        thus ?case
          using Cons(3)[of u v] by simp
      qed
    show ?case 
      apply(subst foldr.simps, subst o_apply, subst f_def)
    proof(cases "blookup M (old_vertex u)", goal_cases)
      case 1
      then show ?case 
        by (auto simp add: IH_applied)
    next
      case (2 vv)
      note two = this
      show ?case 
        unfolding 2 option.case(2)
      proof(rule P_of_ifI, goal_cases)
        case 1
        then show ?case 
          using 2
          by (auto simp add: IH_applied is_new_bp_vertex_def)      
      next
        case 2
        show ?case
          unfolding Let_def
          proof(rule P_of_ifI, goal_cases)
            case 1
            have lookup_u_something:"oblookup (foldr f us obempty) u = Some b \<Longrightarrow> False" for b
            proof(goal_cases)
              case 1
              hence "(u \<in> set us \<and> blookup M (old_vertex u) = Some (old_vertex b) )
                       \<or> (b \<in> set us \<and> blookup M (old_vertex b) = Some (old_vertex u))"
                using IH_applied by(auto simp add: dpairs_of_map_def)
              thus False
                using Cons.prems(1) Cons.prems(2)[of b u] 
                by auto
            qed
            have lookup_vv_something:"\<lbrakk>oblookup (foldr f us obempty) (the_vertex vv) = Some b; the_vertex vv \<noteq> u\<rbrakk>
                      \<Longrightarrow> False" for b
           proof(goal_cases)
              case 1
              hence "((the_vertex vv) \<in> set us \<and> blookup M (old_vertex (the_vertex vv)) = Some (old_vertex b) )
                       \<or> (b \<in> set us \<and> blookup M (old_vertex b) = Some (old_vertex (the_vertex vv)))"
                using IH_applied by(auto simp add: dpairs_of_map_def)
              thus False
                using Cons.prems(1) Cons.prems(2)[of "(the_vertex vv)" b]  two
                       Cons.prems(2)[of u  "(the_vertex vv)"] not_new_vertex_old_the_vertex[OF 2]
                by (auto simp add: assms)
            qed
            have pairs_helper:
               "dpairs_of_map ((oblookup (foldr f us obempty))(u \<mapsto> the_vertex vv, the_vertex vv \<mapsto> u)) =
                 {(u, the_vertex vv), (the_vertex vv, u)} \<union> (dpairs_of_map (oblookup (foldr f us obempty)))"
            proof(rule, goal_cases)
              case 1
              show ?case
              using  Cons.prems(1)
              by(auto simp add: dpairs_of_map_def if_split[of "\<lambda> x. x= Some _"] )
          next
            case 2
            show ?case
             by(auto simp add: dpairs_of_map_def dest!: lookup_u_something lookup_vv_something)
         qed
          show ?case 
          by(subst old_match_map.map_update)
            (auto simp add: obinvar_iterated old_match_map.invar_update old_match_map.map_update
                            "2" not_new_vertex_old_the_vertex two 1  
                             pairs_helper IH_applied obinvar_iterated old_match_map.invar_empty
              intro!: exI[of _ "{(u, the_vertex vv), (the_vertex vv, u)}"] 
                      double_exI[of _ u "the_vertex vv"])
      next
        case 2
        show ?case
          using 2 two
          by (auto simp add: IH_applied is_new_bp_vertex_def)      
      qed
      qed
    qed
  qed
  show  "upairs_of_map (oblookup (extract_mwmc_matching M)) = 
    project_to_old (upairs_of_map (blookup  M)) \<inter> G"
    unfolding extract_mwmc_matching_def foldl_conv_foldr f_def[symmetric]
              upairs_dpairs_of_map
  proof(subst operation_effect, goal_cases)
    case 1
    then show ?case 
      by (simp add: invar_left vset(1))
  next
    case (2 u v)
    hence a1:"old_vertex u \<in> bp_perfected_L L R"
      by (simp add: bp_perfected_L_def)
    hence a2: "{old_vertex u, old_vertex v} \<in> bp_perfected_G L R"
      using assms(2) 2 by(auto simp add: upairs_of_map_def)
    have a3: "old_vertex v \<in> bp_perfected_R L R" 
      using bipartite_edgeD[OF a2 bipartite_perfected] a1
      by (auto simp add: doubleton_eq_iff)
    then show ?case
      using bipartite_disjointD[OF G(2)] not_new_vertexD(2)[of "old_vertex v"] 
      by auto
  next
    case 3
    have helper:"\<lbrakk>old_graph.isin' va (old_graph.neighbourhood Gimpl ua);
           ua \<in> L\<rbrakk> \<Longrightarrow> {ua, va} \<in> G" for ua va
    proof(goal_cases)
      case 1
      hence "ua \<in> ot_set left \<and> (ua, va) \<in> old_graph.digraph_abs Gimpl"
        using 1 G(3) ot_set_left one_onleft_neighb_digraph_abs(1)[of ua va]
        by (simp add: old_graph.digraph_abs_def)
      thus ?case
        by(auto simp add: G(1)) 
    qed
    show ?case
    proof(rule, all \<open>rule\<close>, goal_cases)
      case (1 e)
      thus ?case
        by(auto simp add: project_to_old_def UD_def dpairs_of_map_def insert_commute w_props
                     intro!: exI[of _ "old_vertex ` e"] dest!: helper)
    next
      case (2 e)
      then obtain u v where uv: "e = {the_vertex u, the_vertex v}"
        by(auto simp add: project_to_old_def UD_def)
      have Ghelper: "\<lbrakk>u\<in>L; {u, v} \<in> G\<rbrakk> \<Longrightarrow>
         old_graph.isin' v (old_graph.neighbourhood Gimpl u)" for u v
        using not_in_neighbourhood_of_LD by auto
      obtain u v where  "e = {the_vertex u, the_vertex v}" "the_vertex u \<in> L" "the_vertex v \<in> R"
        apply(rule bipartite_edgeE[OF _ G(2), of e])
        using 2 
       by (auto simp add: uv  doubleton_eq_iff )
      thus ?case
        using 2 
        by (auto simp add: doubleton_eq_iff insert_commute
                           no_new_vertex_old_vertex_new_vertex_inverse w_props assms(1)
                           project_to_old_def UD_def dpairs_of_map_def
                   intro!: double_exI[of _  "the_vertex u" "the_vertex v"] Ghelper
                           exI[of _ "{(the_vertex u, the_vertex v), (the_vertex v, the_vertex u)}"])
    qed
  qed
qed

lemma minimum_weight_matching:
  assumes  "\<And> u v. blookup M u = Some v \<longleftrightarrow>  blookup M v = Some u"
           "min_weight_perfect_matching (bp_perfected_G L R) 
           \<lbrace>curry (abstract_real_map (clookup bp_min_costs_to_min_perfect_costs_exec))\<rbrace>
           (upairs_of_map (blookup M))"
  shows   "min_weight_matching G \<w> (upairs_of_map (oblookup (extract_mw_matching M)))"
proof-
  have other_weight_mwp:
       "min_weight_perfect_matching (bp_perfected_G L R) 
          (bp_min_costs_to_min_perfect_costs G \<w>) (upairs_of_map (blookup M))"
    by(auto intro!: iffD2[OF weighted_matchings_over_coinciding_weights(4), OF _ assms(2)]
              bp_min_costs_to_min_perfect_costs_exec_correct(2))
  note mwm_reduced = min_weight_perfect_implies_min_weight(1)[OF
                   G(2) finite_L finite_R other_weight_mwp]
  show ?thesis
  proof(subst extract_mw_matching_correct(2), goal_cases)
    case (1 u v)
    then show ?case 
      using assms(1) by simp
  next
    case 2
    then show ?case 
      using assms(2)
      by(auto elim!:  min_weight_perfect_matchingE perfect_matchingE)
  next
    case 3
    then show ?case 
      using mwm_reduced by simp
  qed
qed

lemma minimum_weight_max_card_matching:
  assumes  "\<And> u v. blookup M u = Some v \<longleftrightarrow>  blookup M v = Some u"
           "min_weight_perfect_matching (bp_perfected_G L R) 
           \<lbrace>curry (abstract_real_map (clookup bp_min_max_card_costs_to_min_perfect_costs_exec))\<rbrace>
           (upairs_of_map (blookup M))"
  shows   "min_weight_max_card_matching G \<w> (upairs_of_map (oblookup (extract_mwmc_matching M)))"
proof-
  have other_weight_mwmc:
       "min_weight_perfect_matching (bp_perfected_G L R) 
          (bp_min_max_card_costs_to_min_perfect_costs G \<w>) (upairs_of_map (blookup M))"
    by(auto intro!: iffD2[OF weighted_matchings_over_coinciding_weights(4), OF _ assms(2)]
              bp_min_max_card_to_min_perfect_costs_exec_correct(2))
  note mwm_reduced = min_weight_perfect_gives_min_weight_max_card_matching(1)[OF
                   G(2) finite_L finite_R other_weight_mwmc]
  show ?thesis
  proof(subst extract_mwmc_matching_correct(2), goal_cases)
    case (1 u v)
    then show ?case 
      using assms(1) by simp
  next
    case 2
    then show ?case 
      using assms(2)
      by(auto elim!:  min_weight_perfect_matchingE perfect_matchingE)
  next
    case 3
    then show ?case 
      using mwm_reduced by simp
  qed
qed

end
end

subsection \<open>Cost Inverter\<close>

locale cost_inverter = 
Map_iterator where lookup = lookup
for lookup::"'map \<Rightarrow> 'v \<Rightarrow> real option"
begin
(*TODO MOVE*)
lemma update_all_simp_if:
  assumes "invar m"
  shows "lookup (update_all f m) = 
               (\<lambda> v. case lookup m v of Some val => Some (f v val)
                     | None => None)"
  using  update_all(4)[OF assms]
  by(auto intro!: ext split: option.split simp add: update_all(1)[OF assms, OF domI])+

definition "inverted_costs c =  update_all (\<lambda> _ val. -val) c"

lemma inverted_costs_correct:
  assumes "invar c"
  shows   "invar (inverted_costs c)" 
          "abstract_real_map (lookup (inverted_costs c)) =
          - abstract_real_map (lookup c)"
  using assms
  by(auto simp add: inverted_costs_def abstract_real_map_def update_all_simp_if
             intro: update_all intro!: ext split: option.split)
 
end

end