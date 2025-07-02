section \<open>Formalisation of Forest Maintenance\<close>

theory Maintain_Forest
  imports Intermediate_Summary
begin

subsection \<open>The Locale\<close>

locale maintain_forest_spec = algo_spec where fst="fst::'edge_type \<Rightarrow> 'a" 
and get_from_set = "get_from_set::('edge_type \<Rightarrow> bool) \<Rightarrow> 'd \<Rightarrow> 'edge_type option"
and empty_forest = "empty_forest :: 'c"
and \<E>_impl = "\<E>_impl :: 'd"
for fst  get_from_set empty_forest \<E>_impl+
fixes get_path::"'a \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'a list" 
begin
definition "maintain_forest_get_path_cond u v E p q =
      (vwalk_bet (digraph_abs  E) u q v \<and> adjmap_inv E \<and>
       p = get_path u v E \<and> u \<in> Vs (to_graph E) \<and>
       (\<forall> x. lookup E x \<noteq> None \<and> vset_inv (the (lookup E x))) \<and> u \<noteq> v)"

lemma maintain_forest_get_path_condI:
"vwalk_bet (digraph_abs E) u q v \<Longrightarrow> 
                       adjmap_inv E \<Longrightarrow> p = get_path u v E \<Longrightarrow> u \<in> Vs (to_graph E) \<Longrightarrow>
                        (\<And> x. lookup E x \<noteq> None \<and> vset_inv (the (lookup E x))) \<Longrightarrow> u \<noteq> v \<Longrightarrow>
      maintain_forest_get_path_cond u v E p q"
  by(auto simp add: maintain_forest_get_path_cond_def)

lemma maintain_forest_get_path_condE:
"maintain_forest_get_path_cond u v E p q \<Longrightarrow> 
(vwalk_bet (digraph_abs E) u q v \<Longrightarrow> 
                       adjmap_inv E \<Longrightarrow> p = get_path u v E \<Longrightarrow> u \<in> Vs (to_graph E) \<Longrightarrow>
                        (\<And> x. lookup E x \<noteq> None \<and> vset_inv (the (lookup E x))) \<Longrightarrow> u \<noteq> v \<Longrightarrow>
    P) \<Longrightarrow> P"
  by(auto simp add: maintain_forest_get_path_cond_def)

lemma maintain_forest_get_path_cond_unfold_meta:
  assumes "maintain_forest_get_path_cond u v E p q"
  shows "vwalk_bet (digraph_abs E) u q v" "adjmap_inv E" "p = get_path u v E" 
        "u \<in> Vs (to_graph E)"
        "(\<And> x. lookup E x \<noteq> None \<and> vset_inv (the (lookup E x)))" 
        "u \<noteq> v"
  using maintain_forest_get_path_condE[OF assms(1)] by auto
end

locale maintain_forest = 
maintain_forest_spec where fst ="fst::'edge_type \<Rightarrow> 'a" +
algo where fst = fst  for fst +
assumes get_path_axioms:
        "\<And> u v E p q. maintain_forest_get_path_cond u v E p q\<Longrightarrow>vwalk_bet (digraph_abs  E) u p v"
        "\<And> u v E p q. maintain_forest_get_path_cond u v E p q \<Longrightarrow> distinct p"
begin

lemmas get_path_axioms_unfolded=get_path_axioms[OF maintain_forest_get_path_condI]

term "Pair_Graph_Specs.digraph_abs lookup isin_vset"

find_theorems Pair_Graph_Specs.digraph_abs 

subsection \<open>Function and Setup\<close>
function (domintros) maintain_forest::"('a,'d, 'c, 'edge_type) Algo_state \<Rightarrow> ('a, 'd, 'c, 'edge_type) Algo_state" where
"maintain_forest state = (let \<FF> = \<FF> state;
                    f = current_flow state;
                    b = balance state;
                    r = representative state;
                    E' = actives state;
                    to_rdg = conv_to_rdg state;
                    \<gamma> = current_\<gamma> state;
                    cards = comp_card state;
                    \<FF>_imp = \<FF>_imp state                  
                in (if \<exists> aa. get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E' = Some aa
                    then let e = the ( get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E');
                             x = fst e; y = snd e;
                             to_rdg' = (\<lambda> d. if d = make_pair e then F e
                                             else if prod.swap d = make_pair e then B e 
                                             else to_rdg d);
                             (x, y) = (if cards x \<le> cards y
                                       then (x,y) else (y,x));
\<comment> \<open>comments\<close>
                              \<FF>' = insert {fst  e, snd e} \<FF>;
                             \<FF>_imp' = insert_undirected_edge (fst e) (snd e) \<FF>_imp;
                             x' = r x; y' = r y;
                             Q = get_path x' y' \<FF>_imp';
                             f' = (if b x' > 0 
                                   then augment_edges f (b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges f (- b x') (to_redge_path to_rdg' (rev Q)));
                             b' = (\<lambda> v. if v= x' then 0 
                                        else if v = y' then b y' + b x'
                                        else b v);
                            E'' = filter (\<lambda> d. {r (fst d) , r (snd d)} \<noteq> {x', y'}) E';
                            r' = (\<lambda> v. if r v = x' \<or> r v = y' then y' else r v);
                            cards'= (\<lambda> v. if r' v = y' then cards x + cards y else cards v);
                            nb = not_blocked state;
                            nb' = (\<lambda> d. if e = d then True
                                        else if {r (fst d) , r (snd d)} = {x', y'} then False
                                        else nb d);
                            state' = state \<lparr>  \<FF> := \<FF>', current_flow := f',
                                    balance := b',  representative := r',
                                    actives := E'', conv_to_rdg := to_rdg', comp_card := cards',
                                    \<FF>_imp:= \<FF>_imp', not_blocked := nb'\<rparr>
                            in maintain_forest state'
                    else state))"
  by auto

definition "maintain_forest_ret_cond state = (let \<FF> = \<FF> state;
                    f = current_flow state;
                    b = balance state;
                    r = representative state;
                    E' = actives state;
                    to_rdg = conv_to_rdg state;
                    \<gamma> = current_\<gamma> state;
                    cards = comp_card state;
                    \<FF>_imp = \<FF>_imp state
                in (if \<exists> aa. get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E' = Some aa
                    then False
                    else True))"

lemma maintain_forest_ret_condE: 
"maintain_forest_ret_cond state \<Longrightarrow> (\<And> f b r E' to_rdg \<gamma> cards.
                    f = current_flow state \<Longrightarrow>
                    b = balance state \<Longrightarrow>
                    r = representative state \<Longrightarrow>
                    E' = actives state \<Longrightarrow>
                    to_rdg = conv_to_rdg state \<Longrightarrow>
                    \<gamma> = current_\<gamma> state \<Longrightarrow>
                    cards = comp_card state \<Longrightarrow>
                    \<not> (\<exists> aa. get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E' = Some aa) \<Longrightarrow>P)
                \<Longrightarrow> P"
  unfolding maintain_forest_ret_cond_def Let_def 
  by presburger
  
lemma maintain_forest_ret_condI: " f = current_flow state\<Longrightarrow>
                    E' = actives state\<Longrightarrow>
                    \<gamma> = current_\<gamma> state \<Longrightarrow>
                    \<not> (\<exists> aa. get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E' = Some aa) \<Longrightarrow>cards = comp_card state\<Longrightarrow> maintain_forest_ret_cond state" 
  by(simp add: maintain_forest_ret_cond_def)

definition "(maintain_forest_call_cond (state::('a, 'd, 'c, 'edge_type) Algo_state)) = 
                   ((let \<FF> = \<FF> state;
                    f = current_flow state;
                    b = balance state;
                    r = representative state;
                    E' = actives state;
                    to_rdg = conv_to_rdg state;
                    \<gamma> = current_\<gamma> state;
                    cards = comp_card state;
                    \<FF>_imp = \<FF>_imp state
                in (if \<exists> aa. get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E' = Some aa
                    then let e = the(get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E');
                             x = fst e; y= snd e;
                             to_rdg' = (\<lambda> d. if d = make_pair e then F e
                                             else if prod.swap d = make_pair e then B e
                                             else to_rdg d);
                             (x, y) = (if cards x \<le> cards y
                                       then (x,y) else (y,x));
                              \<FF>' = insert {fst  e, snd e} \<FF>;
                              \<FF>_imp' = insert_undirected_edge (fst e) (snd e) \<FF>_imp;
                             x' = r x; y' = r y;
                             Q = get_path x' y' \<FF>_imp';
                             f' = (if b x' > 0 
                                   then augment_edges f (b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges f (- b x') (to_redge_path to_rdg' (rev Q)));
                             b' = (\<lambda> v. if v= x' then 0 
                                        else if v = y' then b y' + b x'
                                        else b v);
                            E'' = filter (\<lambda> d. {r (fst d), r (snd d)} \<noteq> {x', y'}) E';
                            r' = (\<lambda> v. if r v = x' \<or> r v = y' then y' else r v);
                            cards'= (\<lambda> v. if r' v = y' then cards x + cards y else cards v);
                            nb = not_blocked state;
                            nb' = (\<lambda> d. if e = d then True
                                        else if {r (fst d) , r (snd d)} = {x', y'} then False
                                        else nb d);
                            state' = state \<lparr>  \<FF> := \<FF>', current_flow := f',
                                    balance := b',  representative := r',
                                    actives := E'', conv_to_rdg := to_rdg', comp_card := cards',
                                    \<FF>_imp:= \<FF>_imp', not_blocked := nb'\<rparr>
                          in True
                    else False)))"

lemma maintain_forest_call_condE:
  assumes 
"maintain_forest_call_cond state" "(\<And> f b r E' to_rdg \<gamma> e x y xx yy to_rdg' \<FF>' x' y' f' b' r' Q E''
                             state' cards cards' \<FF>_imp' nb nb'.
                    f = current_flow state \<Longrightarrow>
                    b = balance state \<Longrightarrow>
                    r = representative state \<Longrightarrow>
                    E' = actives state \<Longrightarrow>
                    to_rdg = conv_to_rdg state \<Longrightarrow>
                    (\<gamma>::real) = current_\<gamma> state \<Longrightarrow>
                     cards = comp_card state \<Longrightarrow>
                    \<exists> aa. get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E' = Some aa \<Longrightarrow>
                     e = the ( get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E') \<Longrightarrow>
                    x = fst e \<Longrightarrow> y= snd e \<Longrightarrow>
                    to_rdg' = (\<lambda> d. if d = make_pair e then F e
                                             else if prod.swap d = make_pair e then B e
                                             else to_rdg d) \<Longrightarrow>
                    (xx, yy) = (if cards x \<le> cards y
                                       then (x,y) else (y,x)) \<Longrightarrow>
                              \<FF>' = insert {fst  e, snd e} (\<FF> state) \<Longrightarrow>
                              \<FF>_imp' = insert_undirected_edge (fst e) (snd e) (\<FF>_imp state)\<Longrightarrow>
                             x' = r xx \<Longrightarrow> y' = r yy\<Longrightarrow>
                             Q = get_path x' y' \<FF>_imp' \<Longrightarrow>
                             f' = (if b x' > 0 
                                   then augment_edges f (b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges f (- b x') (to_redge_path to_rdg' (rev Q))) \<Longrightarrow>
                             b' = (\<lambda> v. if v= x' then 0 
                                        else if v = y' then b y' + b x'
                                        else b v) \<Longrightarrow>
                            E'' = filter (\<lambda> d. {r (fst d), r (snd d)} \<noteq> {x', y'}) E'\<Longrightarrow>
                            r' = (\<lambda> v. if r v = x' \<or> r v = y' then y' else r v) \<Longrightarrow>
                            cards'= (\<lambda> v. if r' v = y' then cards x + cards y else cards v) \<Longrightarrow>
                                                        nb = not_blocked state \<Longrightarrow>
                            nb = not_blocked state \<Longrightarrow>
                            nb' = (\<lambda> d. if e = d then True
                                        else if {r (fst d) , r (snd d)} = {x', y'} then False
                                        else nb d) \<Longrightarrow>
                            state' = state \<lparr>  \<FF> := \<FF>', current_flow := f',
                                    balance := b',  representative := r',
                                    actives := E'', conv_to_rdg := to_rdg', comp_card := cards',
                                    \<FF>_imp:= \<FF>_imp', not_blocked := nb'\<rparr> \<Longrightarrow> P)"
shows P
  using assms
  unfolding maintain_forest_call_cond_def Let_def
  by (simp, metis (no_types, lifting))

lemma maintain_forest_call_condI: " f = current_flow state \<Longrightarrow>
                    b = balance state \<Longrightarrow>
                    r = representative state \<Longrightarrow>
                    E' = actives state \<Longrightarrow>
                    to_rdg = conv_to_rdg state \<Longrightarrow>
                    (\<gamma>::real) = current_\<gamma> state \<Longrightarrow>
                    cards = comp_card state \<Longrightarrow>
                     \<exists> aa. get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E' = Some aa \<Longrightarrow>
                     maintain_forest_call_cond state"
  by(simp add: maintain_forest_call_cond_def Let_def)
 
 lemma maintain_forest_cases:
  assumes
   "maintain_forest_ret_cond state \<Longrightarrow> P"
   "maintain_forest_call_cond state \<Longrightarrow> P"
 shows P
proof-
  have "maintain_forest_call_cond state  \<or> maintain_forest_ret_cond state "
    by (auto simp add: maintain_forest_call_cond_def maintain_forest_ret_cond_def
                       Let_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms
    by auto
qed

definition "maintain_forest_upd state = (let \<FF> = \<FF> state;
                    f = current_flow state;
                    b = balance state;
                    r = representative state;
                    E' = actives state;
                    to_rdg = conv_to_rdg state;
                    \<gamma> = current_\<gamma> state;
                    cards = comp_card state;
                    \<FF>_imp = \<FF>_imp state;
                    e = the(get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E');
                    x = fst e; y= snd e;
                    to_rdg' = (\<lambda> d. if d = make_pair e then F e
                                             else if prod.swap d = make_pair e then B e 
                                             else to_rdg d);
                    (x, y) = (if cards x \<le> cards y
                                       then (x,y) else (y,x));
                    \<FF>' = insert {fst  e, snd e} \<FF>;
                    \<FF>_imp' = insert_undirected_edge (fst e) (snd e) \<FF>_imp;
                    x' = r x; y' = r y;
                    Q = get_path x' y' \<FF>_imp';
                    f' = (if b x' > 0 
                                   then augment_edges f (b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges f (- b x') (to_redge_path to_rdg' (rev Q)));
                    b' = (\<lambda> v. if v= x' then 0 
                                        else if v = y' then b y' + b x'
                                        else b v);
                    E'' = filter (\<lambda> d. {r (fst d), r (snd d)} \<noteq> {x', y'}) E';
                    r' = (\<lambda> v. if r v = x' \<or> r v = y' then y' else r v);
                    cards'= (\<lambda> v. if r' v = y' then cards x + cards y else cards v);
                    nb = not_blocked state;
                    nb' = (\<lambda> d. if e = d then True
                                        else if {r (fst d) , r (snd d)} = {x', y'} then False
                                        else nb d);
                            state' = state \<lparr>  \<FF> := \<FF>', current_flow := f',
                                    balance := b',  representative := r',
                                    actives := E'', conv_to_rdg := to_rdg', comp_card := cards',
                                    \<FF>_imp:= \<FF>_imp', not_blocked := nb'\<rparr>
                    in state')"

lemma maintain_forest_simps:
  "maintain_forest_dom state \<Longrightarrow>maintain_forest_call_cond state \<Longrightarrow> maintain_forest state = maintain_forest (maintain_forest_upd state)"
  "maintain_forest_ret_cond state \<Longrightarrow> maintain_forest state =  state"
proof(goal_cases)
  case 1
  note assms = this
  show ?case 
    apply(insert assms(2))
    apply(subst maintain_forest.psimps[OF assms(1)])
    unfolding maintain_forest_upd_def Let_def
    apply(rule maintain_forest_call_condE, simp) 
    apply(auto split: if_splits prod.splits)
    done 
next
  case 2
  show ?case
    apply(subst maintain_forest.psimps)
    subgoal
      apply(rule maintain_forest.domintros)
      using 2 by(auto simp add:maintain_forest_ret_cond_def Let_def)
    using 2 by(auto simp add:maintain_forest_ret_cond_def Let_def)
qed

lemma maintain_forest_upd_Forest'_destr:
assumes 
  "state' = maintain_forest_upd state"

  "\<FF>a = Algo_state.\<FF> state"
  "f = current_flow state"
  "E' = actives state"
  "\<gamma> = current_\<gamma> state"
  "e = the ( get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
shows 
"\<FF> state'= (let sth =sth in insert {fst e, snd e} \<FF>a )"
    using assms by(auto simp add: maintain_forest_upd_def Let_def split: prod.splits)

lemma maintain_forest_upd_Forest'_unfold:
  assumes "\<FF>a = Algo_state.\<FF> state"
   "f = current_flow state"
  "E' = actives state"
  "\<gamma> = current_\<gamma> state"
  "e = the (get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  "\<FF>' = insert {fst e, snd e} \<FF>a" 
shows "\<FF>' = \<FF> (maintain_forest_upd state)"
  using assms by(auto simp add: maintain_forest_upd_def Let_def split: prod.splits)

lemma maintain_forest_upd_Forest'_impl_unfold:
  assumes "\<FF>a_imp = Algo_state.\<FF>_imp state"
   "f = current_flow state"
  "E' = actives state"
  "\<gamma> = current_\<gamma> state"
  "e = the (get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  "\<FF>_imp' = insert_undirected_edge (fst e) (snd e) \<FF>a_imp" 
shows "\<FF>_imp' = \<FF>_imp (maintain_forest_upd state)"
  using assms by(simp add: maintain_forest_upd_def Let_def split: prod.splits)

lemma maintain_forest_upd_conv_to_rdg_unfold:
  assumes "\<FF>a = Algo_state.\<FF> state"
   "f = current_flow state"
  "E' = actives state"
  "to_rdg = conv_to_rdg state"
  "\<gamma> = current_\<gamma> state"
  "e = the ( get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  "to_rdg' = (\<lambda> d. if d = make_pair e then F e else if prod.swap d = make_pair e then B e 
                                             else to_rdg d)"
shows "to_rdg' = conv_to_rdg (maintain_forest_upd state)"
  using assms by(auto simp add: maintain_forest_upd_def Let_def split: prod.split)

lemma   maintain_forest_upd_flow_unfold:
  assumes "\<FF>a_imp = Algo_state.\<FF>_imp state"
   "f = current_flow state"
  "b = balance state"
  "r = representative state"
  "E' = actives state"
  "to_rdg = conv_to_rdg state"
  "\<gamma> = current_\<gamma> state"
  "cards = comp_card state"
  "e = the ( get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  "x = fst e" "y= snd e"
  "to_rdg' = (\<lambda> d. if d = make_pair e then F e else if prod.swap d = make_pair e then B e 
                                             else to_rdg d)"
  "xy = (if cards x \<le> cards y then (x,y) else (y,x))"
  "xx = prod.fst xy"
  "yy = prod.snd xy"
  "\<FF>_imp' = insert_undirected_edge (fst e) (snd e) \<FF>a_imp"
  "x' = r xx"
  "y' = r yy"
  "Q = get_path x' y' \<FF>_imp'"
  "f' = (if b x' > 0 then augment_edges f (b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges f (- b x') (to_redge_path to_rdg' (rev Q)))"
shows "f' = current_flow (maintain_forest_upd state)"
  using assms by(auto simp add: maintain_forest_upd_def Let_def split: prod.split)

lemma   maintain_forest_upd_balance_unfold:
   assumes "\<FF>a = Algo_state.\<FF> state"
   "f = current_flow state"
  "b = balance state"
  "r = representative state"
  "E' = actives state"
  "\<gamma> = current_\<gamma> state"
  "cards = comp_card state"
  "e = the (get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  "x = fst e" "y= snd e"
  "xy = (if cards x\<le> cards y then (x,y) else (y,x))"
  "xx = prod.fst xy"
  "yy = prod.snd xy"
  "x' = r xx"
  "y' = r yy"
  "b' = (\<lambda> v. if v= x' then 0 else if v = y' then b y' + b x'
                                        else b v)"
shows "b' = balance (maintain_forest_upd state)"
  using assms by(auto simp add:  maintain_forest_upd_def Let_def split: prod.split)

lemma maintain_forest_upd_actives_unfold:
  assumes 
  "\<FF>a = Algo_state.\<FF> state"
  "f = current_flow state"
  "r = representative state"
  "\<gamma> = current_\<gamma> state"
  "E' = actives state"
  "cards = comp_card state"
  "e = the (get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  "x = fst e" "y= snd e"
  "xy = (if cards x \<le> cards y then (x,y) else (y,x))"
  "xx = prod.fst xy"
  "yy = prod.snd xy"
  "x' = r xx"
  "y' = r yy"
  "E'' = filter (\<lambda> d. {r (fst d), r (snd d)} \<noteq> {x', y'}) E'"
shows "E'' = actives (maintain_forest_upd state)"
  using assms by(auto simp add: maintain_forest_upd_def Let_def split: prod.splits)

lemma maintain_forest_upd_current_gamma_unfold: 
"current_\<gamma> state = current_\<gamma> (maintain_forest_upd state)"
  by(auto simp add: maintain_forest_upd_def Let_def split: prod.split)

lemma maintain_forest_upd_return_unfold: 
"return state = return  (maintain_forest_upd state)"
  by(auto simp add: maintain_forest_upd_def Let_def split: prod.split)

lemma maintain_forest_upd_more_unfold: 
"Algo_state.more state = Algo_state.more  (maintain_forest_upd state)"
  by(auto simp add: maintain_forest_upd_def Let_def split: prod.split)

method intro_simp uses subst intro simp = 
((subst subst; simp)?; intro intro; auto simp add: simp)

lemma maintain_forest_upd_representative_unfold:
  assumes 
  "\<FF>a = Algo_state.\<FF> state"
  "f = current_flow state"
  "r = representative state"
  "E' = actives state"
  "to_rdg = conv_to_rdg state"
  "\<gamma> = current_\<gamma> state"
  "cards = comp_card state"
  "e = the (get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  "x = fst e" "y= snd e"
  "to_rdg' = (\<lambda> d. if d = make_pair e then F e else if prod.swap d = make_pair e then B e 
                                             else to_rdg d)"
  "xy = (if cards x \<le> cards y then (x,y) else (y,x))"
  "xx = prod.fst xy"
  "yy = prod.snd xy"
 "\<FF>' = insert {fst e, snd e} \<FF>a"
  "x' = r xx"
  "y' = r yy"
  "r' = (\<lambda> v. if r v = x' \<or> r v = y' then y' else r v)"

shows "r' = representative (maintain_forest_upd state)"
  using assms by(auto simp add: maintain_forest_upd_def Let_def split: prod.split)

lemma maintain_forest_upd_comp_card_unfold:
  assumes 
  "\<FF>a = Algo_state.\<FF> state"
  "f = current_flow state"
  "r = representative state"
  "E' = actives state"
  "to_rdg = conv_to_rdg state"
  "\<gamma> = current_\<gamma> state"
  "cards = comp_card state"
  "e = the (get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  "x = fst e" "y= snd e"
  "to_rdg' = (\<lambda> d. if d = make_pair e then F e else if prod.swap d = make_pair e then B e
                                             else to_rdg d)"
  "xy = (if cards x \<le> cards y then (x,y) else (y,x))"
  "xx = prod.fst xy"
  "yy = prod.snd xy"
 "\<FF>' = insert {fst e, snd e} \<FF>a"
  "x' = r xx"
  "y' = r yy"
  "r' = (\<lambda> v. if r v = x' \<or> r v = y' then y' else r v)"
  "cards' = (\<lambda> v. if r' v = y' then cards x + cards y else cards v)"

shows "cards' = comp_card (maintain_forest_upd state)"
  using assms by(auto simp add: maintain_forest_upd_def Let_def split: prod.split)

lemma   maintain_forest_not_blocked_upd_unfold:
  assumes   "f = current_flow state"
  "r = representative state"
  "E' = actives state"
  "\<gamma> = current_\<gamma> state"
  "cards = comp_card state"
  "e = the (get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  "x = fst e" "y= snd e"
  "xy = (if cards x \<le> cards y then (x,y) else (y,x))"
  "xx = prod.fst xy"
  "yy = prod.snd xy"
  "x' = r xx"
  "y' = r yy"
  "nb = not_blocked state"
  "nb' = (\<lambda> d. if e = d then True
          else if {r (fst d) , r (snd d)} = {x', y'} then False
          else nb d)"
shows "nb' = not_blocked (maintain_forest_upd state)"
  using assms
  by(auto simp add: maintain_forest_upd_def Let_def split: prod.split)

lemma   maintain_forest_upd_unfold:
  assumes "\<FF>a = Algo_state.\<FF> state"
   "f = current_flow state"
  "b = balance state"
  "r = representative state"
  "E' = actives state"
  "to_rdg = conv_to_rdg state"
  "\<gamma> = current_\<gamma> state"
  "cards = comp_card state"
  "\<FF>a_imp = \<FF>_imp state"
  "e = the (get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  "x = fst e" "y= snd e"
  "to_rdg' = (\<lambda> d. if d = make_pair e then F e else if prod.swap d = make_pair e then B e 
                                             else to_rdg d)"
  "xy = (if cards x \<le> cards y then (x,y) else (y,x))"
  "xx = prod.fst xy"
  "yy = prod.snd xy"
  "\<FF>' = insert {fst e, snd e} \<FF>a"
  "\<FF>_imp' = insert_undirected_edge (fst e) (snd e) \<FF>a_imp"
  "x' = r xx"
  "y' = r yy"
  "Q = get_path x' y' \<FF>_imp'"
  "f' = (if b x' > 0 then augment_edges f (b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges f (- b x') (to_redge_path to_rdg' (rev Q)))"
  "b' = (\<lambda> v. if v= x' then 0 else if v = y' then b y' + b x'
                                        else b v)"
  "E'' = filter (\<lambda> d. {r (fst d), r (snd d)} \<noteq> {x', y'}) E'"
  "r' = (\<lambda> v. if r v = x' \<or> r v = y' then y' else r v)"
  "cards' = (\<lambda> v. if r' v = y' then cards x + cards y else cards v)"
  "nb = not_blocked state"
  "nb' = (\<lambda> d. if e = d then True
          else if {r (fst d) , r (snd d)} = {x', y'} then False
          else nb d)"
  "state' = state \<lparr> \<FF> := \<FF>', current_flow := f',
                    balance := b',  representative := r',
                    actives := E'', conv_to_rdg := to_rdg', comp_card := cards',
                    \<FF>_imp:= \<FF>_imp', not_blocked := nb'\<rparr>" 
shows "state' = maintain_forest_upd state"
  by(intro Algo_state.equality) 
    (intro_simp subst:  assms(29) 
                intro: maintain_forest_upd_representative_unfold[of \<FF>a state f  r E' to_rdg \<gamma> cards e x y
                                         to_rdg' xy xx yy \<FF>' x' y' r'] 
                       maintain_forest_upd_more_unfold
                       maintain_forest_upd_conv_to_rdg_unfold[of \<FF>a state f  E' to_rdg \<gamma> e to_rdg']
                       maintain_forest_upd_current_gamma_unfold maintain_forest_upd_return_unfold
                       maintain_forest_upd_actives_unfold[of \<FF>a state f r \<gamma> E' cards e x y xy xx yy x' y' E'']
                       maintain_forest_upd_Forest'_unfold[of \<FF>a state f  E'  \<gamma> e \<FF>']
                       maintain_forest_upd_Forest'_impl_unfold[of \<FF>a_imp state f  E'  \<gamma> e \<FF>_imp']
                       maintain_forest_upd_balance_unfold[of \<FF>a state f b r E'  \<gamma> cards e x y xy xx yy  x' y']
                       maintain_forest_upd_comp_card_unfold[of \<FF>a state f r E' to_rdg \<gamma> cards e x y to_rdg' xy xx yy \<FF>'
                                                     x' y' r' cards']
                       maintain_forest_upd_flow_unfold[of \<FF>a_imp state f b r E' to_rdg \<gamma> cards e x y
                                                            to_rdg' xy xx yy \<FF>_imp' x' y' Q]
                       maintain_forest_not_blocked_upd_unfold[of f state r E'  \<gamma> cards e x y
                                                            xy xx yy  x' y' nb nb']   
          simp: assms)+

lemma maintain_forest_induct: 
  assumes "maintain_forest_dom state"
  assumes "\<And>state. \<lbrakk>maintain_forest_dom state;
                     maintain_forest_call_cond state \<Longrightarrow> P (maintain_forest_upd state)\<rbrakk> \<Longrightarrow> P state"
  shows "P state"
proof(rule maintain_forest.pinduct, goal_cases)
  case 1
  then show ?case using assms by simp
next
  case (2 state)
  define \<FF> where "\<FF> = Algo_state.\<FF> state"
  define f where "f = current_flow state"
  define b where "b = balance state"
  define r where "r = representative state"
  define E' where "E' = actives state"
  define to_rdg where "to_rdg = conv_to_rdg state"
  define \<gamma> where "\<gamma> = current_\<gamma> state"
  define cards where "cards = comp_card state"
  define \<FF>_imp where "\<FF>_imp = Algo_state.\<FF>_imp state"
  define e where "e = the ( get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  define x where "x = fst e"
  define y where "y= snd e"
  define to_rdg' where "to_rdg' = (\<lambda> d. if d = make_pair e then F e
                                             else if prod.swap d = make_pair e then B e 
                                             else to_rdg d)"
  define xy where "xy = (if cards x \<le> cards y 
                                       then (x,y) else (y,x))"
  define xx where "xx = prod.fst xy"
  define yy where "yy = prod.snd xy"
  define \<FF>' where  "\<FF>' = insert {fst e, snd e} \<FF>"
  define \<FF>_imp' where "\<FF>_imp' = insert_undirected_edge (fst e) (snd e) \<FF>_imp"
  define x' where "x' = r xx"
  define y' where  "y' = r yy"
  define Q where  "Q = get_path x' y' \<FF>_imp'"
  define f' where "f' = (if b x' > 0 
                                   then augment_edges f (b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges f (- b x') (to_redge_path to_rdg' (rev Q)))"
  define b' where "b' = (\<lambda> v. if v= x' then 0 
                                        else if v = y' then b y' + b x'
                                        else b v)"
  define E'' where "E'' = filter (\<lambda> d. {r (fst d), r (snd d)} \<noteq> {x', y'}) E'"
  define r' where "r' = (\<lambda> v. if r v = x' \<or> r v = y' then y' else r v)"
  define cards' where "cards' = (\<lambda> v. if r' v = y' then cards x + cards y else cards v)"
  define nb where "nb = not_blocked state"
  define nb' where "nb' = (\<lambda> d. if e = d then True
                                        else if {r (fst d) , r (snd d)} = {x', y'} then False
                                        else nb d)"
  define state' where "state' = state \<lparr>  \<FF> := \<FF>', current_flow := f',
                                    balance := b',  representative := r',
                                    actives := E'', conv_to_rdg := to_rdg', comp_card := cards',
                                    \<FF>_imp:= \<FF>_imp', not_blocked := nb'\<rparr>"
  have same_card_sum:"cards x + cards y = cards xx + cards yy"
    unfolding xx_def yy_def xy_def by auto
  show ?case 
    apply(rule assms(2), simp add: 2)
    apply(rule back_subst[where a = state'])
    apply(rule 2(2)[of \<FF> f b r E' to_rdg \<gamma> cards \<FF>_imp e x y to_rdg' xy xx yy \<FF>' \<FF>_imp' x' y' Q f' b' E'' r' cards' nb nb' state'])  
     using maintain_forest_upd_unfold[of \<FF> state f b r E' to_rdg \<gamma> cards \<FF>_imp e x y to_rdg' xy xx yy \<FF>' \<FF>_imp' x' y' Q f' b'
                              E'' r' cards' nb nb' state']
     (*Takes some time*)
     by (auto elim!: maintain_forest_call_condE[of state] 
            simp add:  \<FF>_def f_def  b_def  r_def  E'_def to_rdg_def \<gamma>_def  e_def  x_def 
                 y_def to_rdg'_def xy_def  xx_def yy_def  \<FF>'_def x'_def y'_def Q_def f'_def  b'_def
                 E''_def r'_def  state'_def cards'_def cards_def same_card_sum \<FF>_imp_def \<FF>_imp'_def
                 nb_def nb'_def)
 qed

text \<open>The basic invariants are interdependent\<close>

subsection \<open>Invariants and Monotone Properties\<close>

lemma invar_aux_pres_one_step:
  assumes "aux_invar state"
          "maintain_forest_call_cond state"
  shows   "aux_invar (maintain_forest_upd state)"
proof-
  have all_invars: "invar_aux1 state" "invar_aux2 state" "invar_aux3 state" "invar_aux4 state"
                   "invar_aux6 state" "invar_aux8 state" "invar_aux7 state" "invar_aux9 state "
                   "invar_aux5 state" "invar_aux10 state" "invar_aux11 state" "invar_aux12 state"
                   "invar_aux13 state" "invar_aux16 state" "invar_aux17 state" "invar_aux18 state"
                   "invar_aux19 state" "invar_aux20 state" "invar_aux14 state" "invar_aux21 state"
                   "invar_aux22 state"
    using assms by(auto simp add: aux_invar_def)

  define a\<FF> where "a\<FF> = Algo_state.\<FF> state"
  define f where "f = current_flow state"
  define b where "b = balance state"
  define r where "r = representative state"
  define E' where "E' = actives state"
  define to_rdg where "to_rdg = conv_to_rdg state"
  define cards where "cards = comp_card state"
  define \<FF>_imp where "\<FF>_imp = Algo_state.\<FF>_imp state"
  define \<gamma> where "\<gamma> = current_\<gamma> state"
  define e where "e = the (get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  define x where "x = fst e"
  define y where "y= snd e"
  define to_rdg' where "to_rdg' = (\<lambda> d. if d = make_pair e then F e
                                             else if prod.swap d = make_pair e then B e 
                                             else to_rdg d)"
  define xy where "xy = (if cards x \<le> cards y 
                                       then (x,y) else (y,x))"
  define xx where "xx = prod.fst xy"
  define yy where "yy = prod.snd xy"
  define a\<FF>' where  "a\<FF>' = insert {fst e, snd e} a\<FF>"
  define \<FF>_imp' where "\<FF>_imp' = insert_undirected_edge (fst e) (snd e) \<FF>_imp"
  define x' where "x' = r xx"
  define y' where  "y' = r yy"
  define Q where  "Q = get_path x' y' \<FF>_imp'"
  define f' where "f' = (if b x' > 0 
                                   then augment_edges f (b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges f (- b x') (to_redge_path to_rdg' (rev Q)))"
  define b' where "b' = (\<lambda> v. if v= x' then 0 
                                        else if v = y' then b y' + b x'
                                        else b v)"
  define E'' where "E'' = filter (\<lambda> d. {r (fst d), r (snd d)} \<noteq> {x', y'})E'"
  define r' where "r' = (\<lambda> v. if r v = x' \<or> r v = y'  then y' else r v)"
  define cards' where "cards' = (\<lambda> v. if r' v = y' then cards x + cards y else cards v)"
  define nb where "nb = not_blocked state"
  define nb' where "nb' = (\<lambda> d. if e = d then True
                                        else if {r (fst d) , r (snd d)} = {x', y'} then False
                                        else nb d)"
  define state' where "state' = state \<lparr>  \<FF> := a\<FF>', current_flow := f',
                                    balance := b',  representative := r',
                                    actives := E'', conv_to_rdg := to_rdg', comp_card := cards',
                                    \<FF>_imp:= \<FF>_imp', not_blocked := nb'\<rparr>"
  have 10:"state' = maintain_forest_upd state"
    by(rule maintain_forest_upd_unfold[OF a\<FF>_def f_def b_def r_def E'_def to_rdg_def \<gamma>_def cards_def \<FF>_imp_def e_def x_def y_def
                                to_rdg'_def xy_def xx_def yy_def a\<FF>'_def \<FF>_imp'_def x'_def y'_def Q_def f'_def
                                b'_def E''_def r'_def cards'_def nb_def nb'_def state'_def])
  define \<FF> where "\<FF> = to_graph \<FF>_imp" 
  define  \<FF>' where "\<FF>' = insert {fst e, snd e} \<FF>"
  have F_rewrite[simp]: "to_graph \<FF>_imp' = \<FF>'"
    by (simp add: assms(1) from_aux_invar'(18,19) local.\<FF>_imp_def \<FF>_imp'_def \<FF>'_def \<FF>_def)+

  have set_invar_E'[simp]: "set_invar E'"
    using E'_def all_invars(15) invar_aux17_def by blast

  have E'_substE:"to_set E' \<subseteq> \<E>"
    using all_invars(1) by(simp add: E'_def invar_aux1_def)

  have "\<exists> e. e \<in> to_set E' \<and> 8 * real N * \<gamma> < f e"
    unfolding E'_def \<gamma>_def f_def
    apply(rule maintain_forest_call_condE[OF assms(2)])
    using set_get(1-3)[OF set_invar_E', simplified E'_def] 
    by fastforce

  then obtain ee where ee_prop:" ee \<in> to_set E' \<and> 8 * real N * \<gamma> < f ee"
    by auto

  have e_prop: "e \<in> to_set E' \<and> f e > 8 * real N *\<gamma>"
    apply(rule maintain_forest_call_condE[OF assms(2)])
    using   ee_prop E'_substE set_get(1-3)[OF set_invar_E'] 
    by (fastforce simp add: E'_def f_def e_def \<gamma>_def)
  have fste_V[simp]: "fst e \<in> \<V>" 
    using E'_substE dVsI'(1) e_prop make_pair[OF refl refl] by auto 
  have snde_V[simp]: "snd e \<in> \<V>"
    using E'_substE dVsI'(2) e_prop make_pair[OF refl refl] by auto
  have e_in_E'[simp]:"e \<in> to_set E'"
    using e_prop by simp
  hence einE[simp]: "e \<in> \<E>" 
    using E'_substE by blast

  hence eeinfracE: "{F e, B e} \<subseteq> \<EE>"
    unfolding \<EE>_def 
    by simp

  have x_not_y: "fst e \<noteq> snd e" 
    using all_invars(11)  e_in_E' 
    by(force simp add: invar_aux11_def E'_def )

  have 11:"to_rdgs to_pair (\<lambda>d. if d = make_pair e then F e else
                 if prod.swap d = make_pair e then B e else to_rdg d) 
           {{fst e, snd e}} =
       {F e, B e}" 
    using all_invars(5) 
    by (simp add: x_not_y x_def y_def to_rdg_def invar_aux6_def)

   have aa: "to_rdgs to_pair to_rdg' (insert {fst e, snd e} \<FF>) = 
          to_rdgs to_pair to_rdg' {{fst e, snd e}} \<union> to_rdgs to_pair to_rdg' (\<FF>-{{fst e, snd e}})" 
      unfolding to_rdgs_def by blast
    have bb: "to_rdgs to_pair to_rdg' (\<FF>-{{fst e, snd e}}) = 
            to_rdgs to_pair to_rdg (\<FF>-{{fst e, snd e}})"
      using all_invars(5) by(auto simp add: invar_aux6_def to_rdg_def to_rdg'_def)
    have 110:"to_rdgs to_pair to_rdg' (insert {fst e, snd e} \<FF>) = 
          to_rdgs to_pair to_rdg'{{fst e, snd e}} \<union> to_rdgs to_pair to_rdg (\<FF> - {{fst e, snd e}})"  
      using 11 aa bb by simp
  also  have 111: "... = {F e, B e}
          \<union> to_rdgs to_pair to_rdg (\<FF> - {{fst e, snd e}}) "
    using 11 to_rdg'_def by simp

  have to_rdg'_F_Efrac: "to_rdgs to_pair to_rdg' \<FF>' \<subseteq> \<EE>"
      unfolding to_rdg'_def \<FF>'_def 
      apply(subst 110[simplified to_rdg'_def]) apply( subst 111[simplified to_rdg'_def])
      using all_invars(2) to_rdg_def \<FF>_def eeinfracE \<FF>_imp_def
      by(auto simp add: to_rdgs_def invar_aux2_def)

    have 112: "oedge ` to_rdgs to_pair to_rdg' \<FF>' =
              {e} \<union> oedge ` to_rdgs to_pair to_rdg (\<FF> - {{fst e, snd e}})"
    unfolding \<FF>'_def
    apply(subst 110, subst  111)
    using oedge_both_redges_image by fast

  have 114: "{x', y'} = {r (fst e), r(snd e)}"
    by(auto simp add: x'_def y'_def xx_def yy_def xy_def x_def y_def)

  have 113: "to_set E'' \<subseteq> to_set E' - {e}"
    using 114 set_filter(1)[OF set_invar_E']
    by(auto simp add: E''_def)

  have a113a: "to_set E'' = to_set E' - {d| d. {r (fst d), r (snd d)} = {x', y'}}"
    using 114 set_filter(1)[OF set_invar_E']
    by(auto simp add: E''_def)

  have invar_aux7_state':"invar_aux7 state'"
  proof-
    have 1110:"reachable \<FF> v x \<Longrightarrow> reachable \<FF>' v x" for v x
      by (auto simp add: reachable_subset subset_insertI  \<FF>'_def)
    show ?thesis 
      unfolding invar_aux7_def
    proof(rule, rule, rule)
      fix u v
      assume asm: "reachable (to_graph (Algo_state.\<FF>_imp state')) u v"
      hence asm': "reachable (to_graph (Algo_state.\<FF>_imp state')) v u" 
        by (simp add: reachable_sym)
      show "representative state' u = representative state' v"
      proof(cases "reachable (to_graph (Algo_state.\<FF>_imp state)) u v")
        case True
        note true=this
        hence same_r:"r u =  r v"  
          using all_invars(7) by(simp add: r_def invar_aux7_def)
        then show ?thesis by(simp add:r_def state'_def r'_def)
      next
        case False
        hence False': "\<not> reachable (to_graph (Algo_state.\<FF>_imp state)) v u" 
          by (simp add: reachable_sym)

        have fste_sndexy:"{fst e, snd e} = {prod.fst xy, prod.snd xy}"
          unfolding xy_def x_def y_def
          by(auto split: if_split)

        have reach_rpop:"\<not> reachable \<FF> u xx \<Longrightarrow> u \<noteq> v \<Longrightarrow> reachable \<FF> u yy \<or> u = xx \<or> u = yy"
          apply(rule reachable_after_insert[where v = v])
          using False  asm fste_sndexy F_rewrite
          by(auto simp add: state'_def \<FF>'_def \<FF>_def  xx_def yy_def \<FF>_imp_def)

        have reach_rpop':"\<not> reachable \<FF> v xx \<Longrightarrow> v \<noteq> u \<Longrightarrow>
                                        reachable \<FF> v yy \<or> v = xx \<or> v = yy"
          apply(rule reachable_after_insert[where v = u])
          using False' asm' fste_sndexy F_rewrite
          by(auto simp add:state'_def \<FF>'_def \<FF>_def  xx_def yy_def \<FF>_imp_def \<FF>_imp'_def)

        have reach_xx_yy: "reachable \<FF>' xx yy"
          by(auto split: if_split simp add: edges_reachable x_def y_def reachable_sym  \<FF>'_def xx_def yy_def xy_def)

        have rachbale_with_reps:"reachable \<FF>' xx (r xx) \<or> r xx = xx"
                                "reachable \<FF>' yy (r yy) \<or> r yy = yy"
          using "1110"  invar_aux8_def[of state]  all_invars(6) local.\<FF>_def r_def 
                \<FF>_imp_def by force+
        have rachbale_with_reps:"reachable \<FF> xx (r xx) \<or> r xx = xx"
                                "reachable \<FF> yy (r yy) \<or> r yy = yy"
          using "1110"  invar_aux8_def[of state]  all_invars(6) local.\<FF>_def r_def 
                 \<FF>_imp_def
          by force+
        have rachbale_with_reps:"reachable \<FF> xx (r xx) \<or> r xx = xx"
                                "reachable \<FF> yy (r yy) \<or> r yy = yy"
          using "1110"  invar_aux8_def[of state]  all_invars(6) local.\<FF>_def r_def \<FF>_imp_def
          by force+
        thus ?thesis
          using reach_rpop reach_rpop' all_invars(7) 
          by (auto simp add: state'_def r'_def local.\<FF>_def \<FF>_imp_def r_def x'_def y'_def invar_aux7_def)        
      qed 
    qed 
  qed
  have comps_mod:" comps \<V> (insert {fst e, snd e} \<FF>) =
    comps \<V> \<FF> - {connected_component \<FF> (fst e), connected_component \<FF> (snd e)} \<union>
    {connected_component \<FF> (fst e) \<union> connected_component \<FF> (snd e)}"
      apply(rule new_component_insert_edge)
       using all_invars(11) e_prop  fste_V snde_V  F_rewrite
       by(auto simp add: invar_aux11_def \<FF>_def  E'_def  \<FF>_imp_def)

  have cards_same_cond: "card (connected_component \<FF> x) \<le> card (connected_component \<FF> y) \<longleftrightarrow>
                          cards x \<le> cards y"
      using assms(1) F_rewrite
      by (simp add: cards_def \<FF>_def aux_invar_def invar_aux16_def \<FF>_imp_def x_def y_def)

    have same_reachability: "r v = x' \<or> r v = y' \<longleftrightarrow> reachable \<FF>' y' v" for v
    proof
      show "r v = x' \<or> r v = y' \<Longrightarrow> reachable \<FF>' y' v"
      proof(goal_cases)
        case 1
        hence "reachable \<FF> v x' \<or> v = x' \<or> reachable \<FF> v y' \<or> v = y'"
          using all_invars(6) F_rewrite
          unfolding x'_def y'_def  invar_aux8_def \<FF>_def r_def \<FF>_imp_def
          by metis
        hence "reachable \<FF> v x \<or> v = x \<or> reachable \<FF> v y \<or> v = y"
          using all_invars(6) F_rewrite
          unfolding x'_def y'_def r_def xx_def yy_def xy_def invar_aux8_def \<FF>_imp_def \<FF>_def
          by (smt (verit, ccfv_threshold) reachable_trans fst_swap reachable_sym snd_conv swap_simp)
        hence "reachable \<FF>' v x \<or> v = x "
          unfolding \<FF>'_def x_def y_def 
          by (smt (verit) reachable_trans Diff_single_insert Diff_subset in_con_comp_insert 
               in_connected_componentE reachable_subset reachable_sym)
        hence "reachable \<FF>' v y "
          unfolding \<FF>'_def x_def y_def 
          by (meson reachable_trans in_con_comp_insert in_connected_componentE x_not_y)
        moreover hence "reachable \<FF>' v x"
          unfolding \<FF>'_def x_def y_def 
          using reachable_refl \<FF>'_def \<open>reachable \<FF>' v x \<or> v = x\<close> reachable_in_Vs(1) x_def by force
        ultimately have "reachable \<FF>' v y'"
          using all_invars(6) F_rewrite
          unfolding y'_def yy_def xy_def r_def invar_aux8_def \<FF>'_def \<FF>_def x_def y_def \<FF>_imp_def
          by (smt (verit, best) reachable_trans reachable_subset snd_conv subset_insertI)
        thus ?thesis
          by (simp add: reachable_sym)
      qed
      show "reachable \<FF>' y' v \<Longrightarrow> r v = x' \<or> r v = y'"
      proof(goal_cases)
        case 1
        have "connected_component \<FF>' (snd e) = connected_component \<FF> (fst e) \<union> connected_component \<FF> (snd e)"
          by (metis \<FF>'_def insert_edge_endpoints_same_component new_edge_disjoint_components)
        moreover have "reachable \<FF>' (snd e) v \<or> reachable \<FF>' (fst e) v"
          using 1
          by (metis reachable_trans Diff_single_insert Diff_subset \<FF>'_def all_invars(6) invar_aux8_def
                    local.\<FF>_def \<FF>_imp_def r_def reachable_subset snd_eqD x_def xy_def y'_def y_def yy_def)
        ultimately have "reachable \<FF> (snd e) v \<or> reachable \<FF> (fst e) v \<or> fst e = v \<or> snd e = v"
          by (metis \<FF>'_def reachable_after_insert reachable_sym)
        hence "reachable \<FF> x' v \<or> reachable \<FF> y' v \<or> y' = v \<or> x' = v"
          by (smt (verit) "114" all_invars(6) all_invars(7) doubleton_eq_iff
            invar_aux7E invar_aux8E local.\<FF>_def r_def reachable_sym F_rewrite \<FF>_imp_def)
        then show ?case 
          by (metis "114" \<open>reachable \<FF> (snd e) v \<or> reachable \<FF> (fst e) v \<or> fst e = v \<or> snd e = v\<close> 
           all_invars(7) doubleton_eq_iff invar_aux7_def local.\<FF>_def r_def \<FF>_imp_def)
      qed
    qed

    have x'_neq_y': "x' \<noteq> y'" 
    proof(rule ccontr, goal_cases)
      case 1
      hence "reachable \<FF> x y \<or> x = y"
        using x'_def y'_def r_def xx_def yy_def xy_def 
              all_invars(6)[simplified invar_aux8_def sym[OF \<FF>_imp_def] sym[OF \<FF>_def]] 
        using "114" reachable_trans doubleton_eq_iff reachable_sym x_def y_def
        by metis
      moreover have "connected_component \<FF> x \<noteq> connected_component \<FF> y" 
        using all_invars(11)[simplified invar_aux11_def sym[OF \<FF>_imp_def] sym[OF \<FF>_def]]
              x_def y_def e_in_E' E'_def by simp
      ultimately show False 
        by (metis connected_components_member_eq in_connected_componentI)
    qed 

      have e_not_in_F: "{x, y} \<notin> \<FF>"
      proof(rule ccontr, goal_cases)
        case 1
        hence "{x, y} \<in> \<FF>" by auto
        note 1 = this
        hence "e \<in> \<F> state"
          using new_edge_disjoint_components[OF refl refl refl, of x y \<FF>] 
                e_in_E' E'_def \<FF>_def
                x_def y_def \<FF>_imp_def all_invars(11)[simplified invar_aux11_def]
          by (fastforce simp add: insert_absorb)
        thus False 
          using "1" E'_def \<FF>'_def all_invars(11)[simplified invar_aux11_def]
                e_in_E' insert_absorb \<FF>_def \<FF>_imp_def  x_def y_def 
                new_edge_disjoint_components[OF refl refl refl, of x y \<FF>] 
          by fastforce
      qed

  have invar8: "invar_aux8 state'"
  proof-
    have 1110:"reachable \<FF> v x \<Longrightarrow> reachable \<FF>' v x" for v x
      unfolding \<FF>'_def
      by (meson reachable_subset subset_insertI)
    have 1111:"reachable \<FF>' v (r' v) \<or> v = r' v"  for v
    proof(cases "r' v = r v")
      case True
      then show ?thesis 
        using all_invars(6) 1110[of v "r v"] F_rewrite
        by(auto simp add: invar_aux8_def  \<FF>_imp_def r_def \<FF>_def)
    next
      case False
      hence "reachable \<FF>' y' v" "r' v = y'"
        using same_reachability
        by(force simp add: r'_def \<FF>'_def y'_def state'_def)+
      then show ?thesis 
        by (simp add: reachable_sym)
    qed
    then show ?thesis 
      by(simp add: invar_aux8_def state'_def)
  qed

  have "aux_invar state'" 
  proof(rule aux_invarI, goal_cases)
    case 1
    then show ?case 
      using all_invars(1) set_filter(1)[OF set_invar_E']
      by(auto simp add: invar_aux1_def state'_def E''_def E'_def)    
  next
    case 2
   from 2 show ?case
     using to_rdg'_F_Efrac F_rewrite 
     by (simp add: invar_aux2_def state'_def )
  next
    case 3
    then show ?case 
      using to_rdg'_F_Efrac F_rewrite
      by(auto simp add: \<EE>_def invar_aux3_def state'_def)
  next
    case 4
    have 1110:"oedge ` to_rdgs to_pair to_rdg \<FF> \<inter> to_set E'= {}"
      using all_invars(4) F_rewrite
      by(simp add: invar_aux4_def  to_rdg_def \<FF>_imp_def E'_def \<FF>_def)
    show ?case 
      unfolding invar_aux4_def state'_def apply simp
      using  112 \<FF>'_def F_rewrite 113 1110 unfolding to_rdgs_def by blast
  next
    case 5
    then show ?case 
      using all_invars(5) 
      by(auto simp add:  make_pair state'_def to_rdg'_def consist_def  invar_aux6_def  to_rdg_def)
  next
    case 6
    then show ?case using invar8 by simp
  next
    case 7 
    show ?case using invar_aux7_state' by simp
  next
    case 8
    have "x \<in> \<V>" 
      by (simp add: dVsI'(1) x_def)
    moreover have "y \<in> \<V>" 
      using dVsI'(2)[of "make_pair e"] einE y_def make_pair[OF refl refl] by simp 
    ultimately have "yy \<in> \<V>" by(simp add: yy_def xy_def)
    hence "y' \<in> \<V>" 
      using all_invars(8)
     by(auto simp add:invar_aux9_def r_def y'_def) 
   then show ?case using all_invars(8)
     by(auto simp add: invar_aux9_def state'_def r'_def r_def)
  next
    case 9
    show ?case 
      using all_invars(9) F_rewrite 
      by(auto simp add: invar_aux5_def state'_def \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def)
  next
    case 10
    have "connected_component \<FF> (fst e) \<subseteq> \<V>"
      using all_invars(10) dVsI'(1)[of "make_pair e"] einE make_pair[OF refl refl]
      by(simp add: invar_aux10_def \<FF>_def  \<FF>_imp_def)
    moreover have "connected_component \<FF> (snd e) \<subseteq> \<V>"
      using all_invars(10) unfolding invar_aux10_def \<FF>_imp_def \<FF>_def
      using dVsI'(2)[of "make_pair e"] einE make_pair[OF refl refl] by simp
    ultimately show ?case
      using all_invars(10)
      apply(simp add: state'_def invar_aux10_def \<FF>'_def \<FF>_def)
    proof(rule, goal_cases)
      case (1 v)
      then show ?case 
      proof(cases " v \<in> connected_component (to_graph (Algo_state.\<FF>_imp state)) (fst e)", goal_cases)
        case True
        then show ?thesis 
          using 1 insert_edge_endpoints_same_component[of "insert {fst e, snd e} (to_graph (Algo_state.\<FF>_imp state))"  "fst e" "snd e" 
                       "(to_graph (Algo_state.\<FF>_imp state))"]  F_rewrite
                 connected_components_member_eq[of v "insert {fst e, snd e} (to_graph (Algo_state.\<FF>_imp state))" "fst e"] 
          unfolding \<FF>_imp_def \<FF>_imp'_def \<FF>'_def \<FF>_def 
          by (metis UnI1 Un_least)
      next
        case False
        then show ?thesis using 1
           insert_edge_endpoints_same_component[of "insert {fst e, snd e} (to_graph (Algo_state.\<FF>_imp state))" "snd e" "fst e" 
                "to_graph (Algo_state.\<FF>_imp state)"]
           connected_components_member_eq[of v  "insert {fst e, snd e} (to_graph (Algo_state.\<FF>_imp state))" "snd e"] 
           unite_disjoint_components_by_new_edge[of "fst e" "to_graph (Algo_state.\<FF>_imp state)" v "snd e"] 
           connected_components_member_sym[of _ "to_graph (Algo_state.\<FF>_imp state)" v] F_rewrite
          apply(cases " v \<in> connected_component (to_graph (Algo_state.\<FF>_imp state)) (snd e)") 
          unfolding \<FF>'_def \<FF>_def \<FF>_imp'_def \<FF>_imp_def 
           apply (smt (verit, del_insts) Un_iff insert_commute le_sup_iff)+
          done
    qed
  qed
  next
    case 11 
    show "invar_aux11 state'"
      unfolding invar_aux11_def
    proof(rule, rule)
      fix d
      assume assm: "d \<in> to_set (actives state')"
                   "connected_component (to_graph (Algo_state.\<FF>_imp state')) (fst d) =
                    connected_component (to_graph (Algo_state.\<FF>_imp state')) (snd d)"
      hence "d \<in> to_set E''" unfolding state'_def by simp
      hence dE:"d \<in> to_set E'" "{r (fst d), r (snd d)} \<noteq> {x', y'}" 
        using  set_filter(1)[OF set_invar_E']
        unfolding E''_def by auto
      have different_comps: "connected_component \<FF> (fst d) \<noteq> connected_component \<FF> (snd d)"
        using all_invars(11) F_rewrite
        unfolding invar_aux11_def
        by (metis E'_def \<open>d \<in> to_set E'\<close>  local.\<FF>_def \<FF>_imp_def)
      have different_reps_before: "r (fst d) \<noteq> r (snd d)"
      proof
        assume "r (fst d) = r (snd d)"
        hence "reachable \<FF> (fst d) (snd d) \<or> fst d = snd d"
          using  reachable_trans[of "to_graph (Algo_state.\<FF>_imp state)" "fst d" 
                      "representative state (fst d)" "snd d"] 
                 reachable_sym[of "to_graph (Algo_state.\<FF>_imp state)" "snd d" "representative state (snd d)"] 
                  spec[OF all_invars(6)[simplified invar_aux8_def], of "fst d"]
                  spec[OF all_invars(6)[simplified invar_aux8_def], of "snd d"]
          by(auto simp add: state'_def  r_def \<FF>_def \<FF>_imp_def)
        thus False 
          using connected_components_member_eq[of "snd d" \<FF> "fst d"] 
                different_comps in_connected_componentI[of \<FF> "fst d" "snd d"] by auto
      qed
 
      have "connected_component \<FF>' (fst d) =
                     connected_component \<FF>'  (snd d)"
        using assm(2) F_rewrite  unfolding state'_def  by simp
      hence "fst d \<noteq>  snd d \<Longrightarrow> reachable \<FF>' (fst d)  (snd d)"
        using  in_connected_componentE[of "snd d" \<FF>' "fst d"] 
               in_own_connected_component[of "snd d" \<FF>'] by auto 
      hence "r' (fst d) = r' (snd d)"
          using   invar_aux7_state'  F_rewrite
          unfolding aux_invar_def invar_aux7_def state'_def
          by (cases "fst d \<noteq>  snd d", auto)
      hence lst:"reachable \<FF>' y' (fst d) \<and> reachable \<FF>' y' (snd d)" 
        using different_reps_before  reachable_trans[of \<FF>' y' "fst d" "snd d"] 
              reachable_trans[of \<FF>' y' "snd d" "fst d"] reachable_sym[of \<FF>' "fst d" "snd d"]
              \<open>fst d \<noteq> snd d \<Longrightarrow> reachable \<FF>' (fst d) (snd d)\<close> same_reachability
        by (force simp add: r'_def)
      hence "connected_component (to_graph (Algo_state.\<FF>_imp state')) (fst d) = 
                   connected_component \<FF> (fst e) \<union> connected_component \<FF> (snd e)" 
      proof(cases "card (connected_component \<FF> x) \<le> card (connected_component \<FF> y)")
        case True
        then show ?thesis  
        using insert_edge_endpoints_same_component[of \<FF>' "fst e" "snd e" \<FF>] sym[OF connected_components_member_eq[of y' \<FF>' "fst d"]]
              lst reachable_trans \<FF>'_def \<FF>_def edges_reachable[of "fst e" "snd e"]
              reachable_subset[of \<FF> "snd e" "representative state (snd e)" \<FF>'] 
              reachable_trans[of \<FF>' "fst e" "snd e" "r y"] cards_same_cond F_rewrite
        unfolding y_def r_def y'_def yy_def xy_def state'_def \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def
        apply (simp add: in_connected_componentI reachable_sym) 
        apply(intro connected_components_member_eq in_connected_componentI)
        apply(cases rule: disjE[OF spec[OF all_invars(6)[simplified invar_aux8_def], of "snd e"]])
        by auto
    next
      case False
      then show ?thesis 
        apply(subst Un_commute , subst insert_edge_endpoints_same_component[of \<FF>' "snd e" "fst e" \<FF>])
        subgoal
        by (simp add: insert_commute \<FF>'_def )
        unfolding state'_def apply simp
      proof(subst sym[OF connected_components_member_eq[of y' \<FF>' "fst d"]], goal_cases)
        case 1
        then show ?case 
          using connected_component_rechability lst r_def reachable_sym xy_def y'_def yy_def  F_rewrite
          by (fastforce simp add:  y'_def r_def yy_def xy_def )
      next
        case 2
        hence " \<not> cards x \<le> cards y"
          using cards_same_cond by simp
        then show ?case
          apply(cases "y = y'") defer
           apply(rule connected_components_member_eq)
          apply(rule in_connected_componentI, subst reachable_sym) 
          using same_reachability[of y] x'_def xx_def xy_def y_def by auto
      qed
    qed
  moreover hence "connected_component (to_graph (Algo_state.\<FF>_imp state')) (snd d) = 
                   connected_component \<FF> (fst e) \<union> connected_component \<FF> (snd e)" 
        using assm(2) F_rewrite \<FF>_def \<FF>'_def \<FF>_imp_def by simp
  ultimately have fst_snd_d_in_comp:"{fst d, snd d} \<subseteq> connected_component \<FF> (fst e) \<union> connected_component \<FF> (snd e)"
    using in_connected_componentI2[of "fst d" "fst d" "to_graph (Algo_state.\<FF>_imp state')"] 
          in_connected_componentI2[of "snd d" "snd d" "to_graph (Algo_state.\<FF>_imp state')"] by simp
  show "False"
      proof(rule pair_set_subsetE[OF fst_snd_d_in_comp], goal_cases)
        case 1
        then show ?case 
          using all_invars(11) dE  connected_components_member_eq [of "fst d"]
                connected_components_member_eq [of "snd d"]
          by(auto simp add:  E'_def invar_aux11_def \<FF>_def  \<FF>_imp_def)
      next
        case 2 
        hence "r (fst d) = r (fst e)"
          using assms(2) "2"(1) all_invars(7)[simplified invar_aux7_def] 
               in_connected_componentE[of "fst d" \<FF> "fst e"]  local.\<FF>_def \<FF>_imp_def
          by(force simp add: aux_invar_def invar_aux8_def r_def connected_component_def)
        moreover hence "r (snd d) = r (snd e)"
          using assms(2) 2 "2"(2) all_invars(7)[simplified invar_aux7_def] 
                in_connected_componentE[of "snd d" \<FF> "snd e"] local.\<FF>_def \<FF>_imp_def
          by(force simp add: aux_invar_def invar_aux8_def r_def connected_component_def)
        ultimately have "{ r (fst d) , r (snd d)} = {x', y'}"
          by(auto simp add: x'_def y'_def xx_def yy_def xy_def x_def y_def split: if_split)
        then show ?case using dE by simp
      next
        case 3
        hence "r (fst d) = r (snd e)"
          using assms(2) "3"(1)  all_invars(7)[simplified invar_aux7_def]
                in_connected_componentE[of "fst d" \<FF> "snd e"]  local.\<FF>_def \<FF>_imp_def
          by(force simp add: aux_invar_def invar_aux8_def r_def connected_component_def)
        moreover hence "r (snd d) = r (fst e)"
          using assms(2) 3 "3"(2)  all_invars(7)[simplified invar_aux7_def]
                in_connected_componentE[of "snd d" \<FF> "fst e"] local.\<FF>_def \<FF>_imp_def
          by(force simp add: aux_invar_def invar_aux8_def r_def connected_component_def)
        ultimately have "{ r (fst d) , r (snd d)} = {x', y'}"
          unfolding x'_def y'_def xx_def yy_def xy_def x_def y_def
          by(auto split: if_split)
        then show ?case using dE by simp
      next
        case 4
        then show ?case 
          using all_invars(11) dE connected_components_member_eq [of "fst d"]
                connected_components_member_eq [of "snd d"] 
          by(auto simp add: E'_def invar_aux11_def \<FF>_def \<FF>_imp_def)
      qed
    qed
  next
    case 12
    show "invar_aux12 state'"
    proof(rule invar_aux12I, goal_cases)
      case (1 v) 
      have y'_y'_reach:"reachable \<FF>' y' y'" 
        apply(cases "y' = yy")
        subgoal
         using reachable_refl[of y \<FF>'] \<FF>'_def edges_reachable[of "fst e" "snd e" \<FF>']
         reachable_in_Vs(2)[of \<FF>' "fst e" "snd e"] 
         reachable_refl[of x \<FF>'] reachable_in_Vs[of \<FF>' "snd e" "fst e"] y_def x_def yy_def xy_def 
         by(auto split: if_split)
        apply(rule reachable_refl[of y' \<FF>'], rule reachable_in_Vs(2)[of \<FF>' yy y'])
        apply(rule reachable_subset[of \<FF> yy y' \<FF>'], rule invar_aux8E[OF all_invars(6)])
        using  \<FF>'_def  \<FF>_def r_def  y'_def \<FF>_imp_def by force+
      show ?case 
      proof(cases "v = y'")
        case True
        then show ?thesis using y'_y'_reach same_reachability
          by(simp add: state'_def r'_def )
      next
        case False 
        have not_x': "v \<noteq> x'" using b'_def 1 state'_def by auto
        hence "b' v =b v" using b'_def False by simp
        hence "b v \<noteq> 0" using b'_def False 1 state'_def not_x' by simp
        hence same_r:"r v = v" using all_invars(12) 1 
         by(auto simp add: b_def r_def invar_aux12_def)
        have not_reach_y: "reachable \<FF> v y \<Longrightarrow> False"
        proof-
          assume "reachable \<FF> v y"
          hence "r y = v"
            using all_invars(7) invar_aux7_def local.\<FF>_def r_def same_r \<FF>_imp_def by fastforce
          hence "v = r xx \<or> v = r yy" 
            by(auto split: if_split simp add: xx_def yy_def xy_def)
          thus False using not_x' False y'_def x'_def by simp
        qed
        have not_reach_x:"reachable \<FF> v x \<Longrightarrow> False"
        proof-
          assume "reachable \<FF> v x"
          hence "r x = v"
            using all_invars(7) invar_aux7_def local.\<FF>_def r_def same_r \<FF>_imp_def by fastforce
          hence "v = r xx \<or> v = r yy"
            by(auto split: if_split simp add: xx_def yy_def xy_def)
          thus False using not_x' False  y'_def x'_def by simp
        qed
        have "reachable \<FF>' v y' \<Longrightarrow> False" 
        proof(rule invar_aux7E[OF all_invars(7)], rule invar_aux8E[OF all_invars(6)],
              goal_cases)
          case 1
          hence "reachable \<FF> v y' \<or> reachable \<FF> v y \<or> reachable \<FF> v x" 
            using "114" False \<FF>'_def  not_x' reachable_after_insert[of \<FF> v y' x y]
                   same_r x_def y_def by fastforce
          hence "representative state v  = representative state y' \<or>
                 representative state v  = representative state y \<or>
                 representative state v  = representative state x" 
            using 1(2) \<FF>_def \<FF>_imp_def by auto
          hence "representative state v = representative state y' \<or>
                representative state v = y' \<or> representative state v = x'"
            using "114" r_def x_def y_def by blast
          moreover have "representative state v = representative state y' \<Longrightarrow>
                reachable \<FF> v y "
            using "1"(2)[of yy y'] "1"(3)[of yy] False r_def same_r y'_def by simp
          ultimately have "representative state v = y' \<or> representative state v = x'"
            using not_reach_y by blast
          then show ?case 
            using False not_x' r_def same_r by force
        qed
        then show ?thesis unfolding state'_def r'_def
          using reachable_sym[of \<FF>' v y'] same_r same_reachability by auto
      qed
    qed
  next
    case 13
    show "invar_aux13 state'"
      unfolding invar_aux13_def
    proof(rule, goal_cases)
      case (1 d)
      then show ?case 
      proof(cases "d \<in> \<E> - to_set (actives state)")
        case True
        hence "connected_component \<FF> (fst d) = connected_component \<FF>  (snd d)"
          using invar_aux13_def algo_axioms all_invars(13) \<FF>_def \<FF>_imp_def by blast
        hence "(snd d) \<in> connected_component \<FF> (fst d)" 
          by (simp add: in_connected_componentI2)
        hence "reachable \<FF> (snd d) (fst d) \<or> fst d = snd d"
          by (meson in_connected_componentE reachable_sym)
        hence "reachable \<FF>' (snd d) (fst d) \<or> fst d = snd d" unfolding \<FF>'_def
          by (meson reachable_subset subset_insertI)
        hence "connected_component \<FF>' (fst d) = connected_component \<FF>' (snd d)"
          using connected_components_member_eq[OF in_connected_componentI, of "\<FF>'" "(snd d)" "(fst d)"] 
          by auto
        then show ?thesis using F_rewrite 
          by(simp add: state'_def \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def)
      next
        case False
        hence dd:"d \<in> {d| d. {r (fst d), r (snd d)} = {x', y'}}"
          using 1  set_filter(1)[OF set_invar_E'] unfolding state'_def E''_def E'_def by auto
        hence "r (fst d) = x' \<or> r (fst d) = y'"
          by fastforce
        hence "reachable \<FF> (fst d) x' \<or> fst d = x' \<or> fst d = y' \<or> reachable \<FF> (fst d) y'" 
          using all_invars(6) invar_aux8E local.\<FF>_def r_def \<FF>_imp_def by blast
        moreover have a1:"reachable \<FF> x' xx \<or> x' = xx" 
          using all_invars(6) invar_aux8_def local.\<FF>_def r_def reachable_sym x'_def \<FF>_imp_def by fastforce 
        moreover have a2:"reachable \<FF>' xx y'"
        proof-
          have "cards x \<le> cards y \<Longrightarrow> Undirected_Set_Graphs.reachable (insert {fst e, snd e} \<FF>) x (r y)"
            using all_invars(6) invar_aux8_def[of state] \<FF>_def r_def 
            reachable_subset[of \<FF> y "r y" "insert {fst e, snd e} \<FF>"]
            by( cases "y = r y", simp add: edges_reachable insert_commute x_def y_def, 
              intro reachable_trans[of _  y x "r x"] reachable_trans[of _  x y "r y"],
              auto simp add: edges_reachable insert_commute x_def y_def \<FF>_imp_def)
          moreover have "\<not> cards x \<le> cards y \<Longrightarrow> Undirected_Set_Graphs.reachable (insert {fst e, snd e} \<FF>) y (r x)"
            using all_invars(6) invar_aux8_def[of state] \<FF>_def r_def reachable_subset[of \<FF> x "r x" "insert {fst e, snd e} \<FF>"]
            by( cases "x = r x", simp add: edges_reachable insert_commute x_def y_def, 
              intro reachable_trans[of _  y x "r x"],
              auto simp add: edges_reachable insert_commute x_def y_def \<FF>_imp_def)
          ultimately show ?thesis
            by(auto split: if_split simp add:  xx_def xy_def y'_def yy_def \<FF>'_def)
        qed
        ultimately have  fst_y: "reachable \<FF>' (fst d) y' \<or> fst d = y'" 
          by (metis reachable_trans \<FF>'_def reachable_subset subset_insertI)
        have "r (snd d) = x' \<or> r (snd d) = y'"
          using dd by force
        hence "reachable \<FF> (snd d) x' \<or> snd d = x' \<or> snd d = y' \<or> reachable \<FF> (snd d) y'" 
          using all_invars(6) invar_aux8E local.\<FF>_def r_def \<FF>_imp_def by blast
        hence  "reachable \<FF>' (snd d) y' \<or> snd d = y'" 
          using a1 a2
          by (metis reachable_trans \<FF>'_def reachable_subset subset_insertI)
        then show ?thesis using fst_y F_rewrite unfolding state'_def 
          by (simp, metis connected_components_member_eq in_connected_componentI)
      qed
    qed
  next 
    case 14
    show "invar_aux14 state'"
      using x_not_y  assms(1)  all_invars(9) invar_aux5_def  assms(1) 
            finite_UnionD[of "to_graph( Algo_state.\<FF>_imp state)"]  F_rewrite from_aux_invar'(14)
      by (auto simp add: invar_aux14_def validF_def 
               Vs_def state'_def  \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def)
  next
    case 15
    show ?case
      using assms fste_V snde_V F_rewrite
      by(simp add:  aux_invar_def invar_aux15_def state'_def \<FF>'_def \<FF>_def Vs_def \<FF>_imp'_def \<FF>_imp_def)
  next
    case 16
    have "v \<in> \<V> \<Longrightarrow> y' = r' v \<Longrightarrow> cards x + cards y = card (connected_component \<FF>' v)"
      for v
    proof(goal_cases)
     case 1
      hence comp_is:"(connected_component \<FF>' v) = (connected_component \<FF> x) \<union> (connected_component \<FF> y)"      
        by (metis \<FF>'_def connected_components_member_eq fst_conv in_connected_componentI
              insert_edge_endpoints_same_component new_edge_disjoint_components
                r'_def same_reachability x'_def x_def xx_def xy_def y_def)
     show ?case
        apply(subst comp_is,subst card_Un_disjnt)
        using 1 all_invars(14) all_invars(10)  fste_V snde_V  all_invars(11)  e_in_E' 
              unequal_components_disjoint[of "to_graph (Algo_state.\<FF>_imp state)" "fst e" "snd e" UNIV, simplified] 
        by (auto intro!: finite_subset[of "connected_component _ _", OF _ \<V>_finite]
                 simp add: invar_aux16_def invar_aux11_def E'_def disjnt_def cards_def
                            \<FF>_imp_def \<FF>_def invar_aux10_def x_def y_def )
    qed
    moreover have "v \<in> \<V> \<Longrightarrow> r' v \<noteq> y' \<Longrightarrow> cards v = card (connected_component \<FF>' v) " for v
    proof(goal_cases)
      case 1
      note 2 = this
      hence neither_x'_nor_y':"r v \<noteq> x'" "r v \<noteq> y'"
        unfolding r'_def by auto
      have " x \<notin> connected_component \<FF> v" 
        apply(rule, rule in_connected_componentE[of x \<FF> v ], simp)
        using  all_invars(7)  neither_x'_nor_y' F_rewrite
        unfolding  invar_aux7_def r_def x'_def y'_def xx_def yy_def xy_def \<FF>_def \<FF>_imp_def
        by(cases "cards x \<le> cards y", simp, simp, cases "cards x \<le> cards y", auto)
      moreover have " y \<notin> connected_component \<FF> v"
        apply(rule, rule in_connected_componentE[of y \<FF> v ], simp)
        using  all_invars(7)  neither_x'_nor_y'
        unfolding  invar_aux7_def r_def x'_def y'_def xx_def yy_def xy_def \<FF>_def \<FF>_imp_def
        by(cases "cards x \<le> cards y", simp, simp, cases "cards x \<le> cards y", auto)
      ultimately have "(connected_component \<FF>' v) = (connected_component \<FF> v)" 
        using  unite_disjoint_components_by_new_edge[of x \<FF> v y] x_def y_def by (auto simp add: \<FF>'_def)
      then show ?case 
        using all_invars(14) 2(1) F_rewrite 
        by (simp add: cards_def invar_aux16_def \<FF>_def \<FF>_imp_def)
    qed
    ultimately
      show ?case
        by(auto simp add: invar_aux16_def state'_def cards'_def)
  next
    case 17
    show ?case
      using all_invars(15) invar_filter[OF set_invar_E']
      by(simp add: invar_aux17_def state'_def E''_def E'_def)
  next
    case 18
    show ?case
      using all_invars(16)
      by(auto intro: adjmap.invar_update simp add: invar_aux18_def state'_def \<FF>_imp'_def \<FF>_imp_def 
                insert_undirected_edge_def Let_def )
  next
    case 19
    show ?case
      unfolding invar_aux19_def
    proof(rule, rule, goal_cases)
      case (1 v)
      then show ?case 
         using all_invars(16) all_invars(17) 
         unfolding invar_aux18_def state'_def \<FF>_imp'_def \<FF>_imp_def state'_def 
                insert_undirected_edge_def Let_def  invar_aux19_def 
       by(simp, subst adjmap.map_update, auto intro: adjmap.invar_update simp add: adjmap.map_update)
    next
      case (2 v)
      then show ?case 
      using all_invars(16) x_not_y  all_invars(17) 
      unfolding invar_aux19_def invar_aux18_def state'_def \<FF>_imp'_def \<FF>_imp_def 
                insert_undirected_edge_def Let_def state'_def
      by (simp, subst  adjmap.map_update, auto intro: adjmap.invar_update vset.set.invar_insert 
                                         simp add: adjmap.map_update)
    qed
  next
    case 20
    find_theorems "_ (_ := _)"
    have new_F_rewrite:"lookup (Algo_state.\<FF>_imp state') =
     (lookup ((Algo_state.\<FF>_imp state)))
         ((fst e) \<mapsto> vset_insert (snd e) (the (lookup (Algo_state.\<FF>_imp state) (fst e))), 
          (snd e) \<mapsto> vset_insert (fst e) (the (lookup (Algo_state.\<FF>_imp state) (snd e))))"
      using all_invars(16) x_not_y  all_invars(17) 
      unfolding invar_aux19_def invar_aux18_def state'_def \<FF>_imp'_def \<FF>_imp_def 
                insert_undirected_edge_def Let_def state'_def
      by (simp, subst  adjmap.map_update, auto intro: adjmap.invar_update vset.set.invar_insert 
                                         simp add: adjmap.map_update)
    have vset_inv_init:"vset_inv (the (lookup \<FF>_imp ua))" for ua
      using all_invars(16) x_not_y  all_invars(17) fste_V snde_V \<FF>_imp_def
      by ( auto intro: adjmap.invar_update vset.set.invar_insert 
                                         simp add: adjmap.map_update invar_aux19_def invar_aux18_def)
    show ?case
      unfolding invar_aux20_def 
    proof(subst new_F_rewrite, rule, rule, rule, goal_cases)
      case (1 u v)
      show ?case 
      proof(cases "u = snd e")
        case True
        then show ?thesis 
          using 1  sym[OF F_rewrite] all_invars(16) x_not_y  all_invars(17) fste_V snde_V  all_invars(18) 
                vset_inv_init vset.set.invar_insert       
          by (auto intro: adjmap.invar_update vset.set.invar_insert 
                simp add: adjmap.map_update vset.set.set_isin vset.set.set_insert
                          invar_aux19_def invar_aux18_def  state'_def \<FF>'_def \<FF>_def \<FF>_imp_def invar_aux20_def 
                          \<FF>_imp'_def a\<FF>_def a\<FF>'_def)  
      next
        case False
        note false = this
        show ?thesis 
           using 1  false all_invars(16) x_not_y  all_invars(17) fste_V snde_V  all_invars(18) vset_inv_init
          by(cases "u = fst e") (auto intro: adjmap.invar_update vset.set.invar_insert
                simp add: adjmap.map_update  vset.set.invar_insert vset.set.set_insert vset.set.set_isin
                         invar_aux19_def invar_aux18_def  state'_def \<FF>'_def \<FF>_def \<FF>_imp_def
                         invar_aux20_def a\<FF>_def a\<FF>'_def)
      qed
    next
      case (2 u v)
      show ?case 
      proof(cases "{u, v} = {fst e, snd e}")
        case True
        then show ?thesis
          using  all_invars(17) 
          by(auto simp add: doubleton_eq_iff vset.set.invar_insert adjmap.invar_update 
                           vset.set.set_isin  vset.set.set_insert invar_aux19_def )
      next
        case False
        hence "{u, v} \<in> a\<FF>"
          using 2 F_rewrite all_invars(20)
          by(simp add: \<FF>'_def state'_def \<FF>_imp'_def invar_aux21_def \<FF>_def a\<FF>_def a\<FF>'_def)
        then show ?thesis 
          using all_invars(17)   all_invars(18)
          by(auto simp add: doubleton_eq_iff vset.set.invar_insert adjmap.invar_update 
                           vset.set.set_isin  vset.set.set_insert invar_aux19_def  a\<FF>_def  invar_aux20_def)
      qed      
    qed     
  next 
    case 21
    show "invar_aux21 state'"
      using all_invars(20) F_rewrite 
      by(simp add: invar_aux21_def state'_def a\<FF>'_def a\<FF>_def \<FF>_imp'_def \<FF>_imp_def \<FF>'_def \<FF>_def)
  next case 22
    show "invar_aux22 state'"
      unfolding invar_aux22_def
    proof(rule)
      fix d
      show "not_blocked state' d = (d \<in> \<F> state' \<union> to_set (actives state'))"
        unfolding state'_def 
      proof(cases "e = d", goal_cases)
        case 1
        then show ?case
          using  nb'_def "112" F_rewrite by auto
      next
        case 2
        note e_neq_d= this
        then show ?case 
        proof(cases "{r (fst d), r (snd d)} = {x', y'}")
          case True
          have " d \<notin> to_set E''" 
            by (simp add: E''_def True local.set_filter(1) split_beta)
          have "d \<notin> oedge ` to_rdgs to_pair to_rdg \<FF>"
          proof(rule ccontr,  goal_cases)
            case 1
            hence "{fst d, snd d} \<in> \<FF>"
              using in_oedge_F_to_in_undirected_F invar_aux6_def to_rdg_def all_invars(5) 
              by fast
            hence "reachable \<FF> (fst d) (snd d)"
              by (meson edges_reachable)
            hence "r (fst d) =  r (snd d)"
              using r_def invar_aux7_def all_invars(7) \<FF>_def \<FF>_imp_def by auto
            thus ?case
              using True x'_neq_y' by simp
          qed
          hence "d \<notin> oedge ` to_rdgs to_pair to_rdg' (to_graph \<FF>_imp')" 
            using 112 F_rewrite e_neq_d 
                  to_rdg_mono[of "\<FF> - {{fst e, snd e}}" \<FF>,simplified, of to_pair to_rdg] 
            by auto
          then show ?thesis 
            by (simp add: True \<open>d \<notin> to_set E''\<close> e_neq_d nb'_def)
        next
          case False
          have "nb' d = nb d" 
            by (simp add: e_neq_d nb'_def False)
          also have "... = (d \<in> oedge ` to_rdgs to_pair to_rdg \<FF>
                                \<or> d \<in> to_set E')"
            using all_invars(21)[simplified invar_aux22_def] nb_def to_rdg_def \<FF>_def E'_def
                  \<FF>_imp_def
            by fast
          also have "... = (d \<in> oedge ` to_rdgs to_pair to_rdg' \<FF>'
                                \<or> d \<in> to_set E'')"
          proof(rule arg_cong2[where ?f="(\<or>)" and ?a="d  \<in> _"], goal_cases)
            case 1
            show ?case
              using 112 e_not_in_F x_def y_def e_neq_d by simp
          next
            case 2
            show ?case 
              using a113a False by fastforce
          qed
          finally show ?thesis 
            using F_rewrite by simp
        qed
      qed
    qed
  qed
  thus ?thesis using 10 by simp
qed

lemma maintain_forest_dom_upd:
  assumes "maintain_forest_dom (maintain_forest_upd state)" "maintain_forest_call_cond state" 
  shows "maintain_forest_dom state"
proof-
  define \<FF> where "\<FF> = Algo_state.\<FF> state"
  define f where "f = current_flow state"
  define b where "b = balance state"
  define r where "r = representative state"
  define E' where "E' = actives state"
  define to_rdg where "to_rdg = conv_to_rdg state"
  define \<gamma> where "\<gamma> = current_\<gamma> state"
  define cards where "cards = comp_card state"
  define \<FF>_imp where "\<FF>_imp = Algo_state.\<FF>_imp state"
  define e where "e = the ( get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  define x where "x = fst e"
  define y where "y= snd e"
  define to_rdg' where "to_rdg' = (\<lambda> d. if d = make_pair e then F e
                                             else if prod.swap d = make_pair e then B e 
                                             else to_rdg d)"
  define xy where "xy = (if cards x \<le> cards y 
                                       then (x,y) else (y,x))"
  define xx where "xx = prod.fst xy"
  define yy where "yy = prod.snd xy"
  define \<FF>' where  "\<FF>' = insert {fst e, snd e} \<FF>"
  define \<FF>_imp' where "\<FF>_imp' = insert_undirected_edge (fst e) (snd e) \<FF>_imp"
  define x' where "x' = r xx"
  define y' where  "y' = r yy"
  define Q where  "Q = get_path x' y' \<FF>_imp'"
  define f' where "f' = (if b x' > 0 
                                   then augment_edges f (b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges f (- b x') (to_redge_path to_rdg' (rev Q)))"
  define b' where "b' = (\<lambda> v. if v= x' then 0 
                                        else if v = y' then b y' + b x'
                                        else b v)"
  define E'' where "E'' = filter (\<lambda> d. {r (fst d), r (snd d)} \<noteq> {x', y'}) E'"
  define r' where "r' = (\<lambda> v. if r v = x' \<or> r v = y' then y' else r v)"
  define cards' where "cards' = (\<lambda> v. if r' v = y' then cards x + cards y else cards v)"
  define nb where "nb = not_blocked state"
  define nb' where "nb' = (\<lambda> d. if e = d then True
                                        else if {r (fst d) , r (snd d)} = {x', y'} then False
                                        else nb d)"
  define state' where "state' = state \<lparr>  \<FF> := \<FF>', current_flow := f',
                                    balance := b',  representative := r',
                                    actives := E'', conv_to_rdg := to_rdg', comp_card := cards',
                                    \<FF>_imp:= \<FF>_imp', not_blocked := nb'\<rparr>"
  have 10:"state' = maintain_forest_upd state"
    by(rule maintain_forest_upd_unfold[OF \<FF>_def f_def b_def r_def E'_def to_rdg_def \<gamma>_def cards_def \<FF>_imp_def e_def x_def y_def
                                to_rdg'_def xy_def xx_def yy_def \<FF>'_def \<FF>_imp'_def x'_def y'_def Q_def f'_def
                                b'_def E''_def r'_def cards'_def nb_def nb'_def state'_def])

  have 12: "maintain_forest_dom state'"
    using assms 10 by simp

  have 13: "e = the ( get_from_set (\<lambda> e. 8 * real N * current_\<gamma> state < current_flow state e) (actives state))"
    by(simp add: e_def E'_def \<gamma>_def f_def)

  show "maintain_forest_dom state"
  proof(rule maintain_forest.domintros, goal_cases)
    case (1 g h xeb ya)
    show ?case 
      apply(rule HOL.forw_subst[of _ state'])
      apply(insert 1)  
      apply(subst (asm) sym[OF 13] option.sel)+
      apply(subst sym[OF r_def] sym[OF f_def] sym[OF b_def] sym[OF E'_def]  
                  sym[OF to_rdg_def] sym[OF x_def]  sym[OF y_def] )+
      subgoal
          apply(rule Algo_state.equality) 
          unfolding state'_def to_rdg'_def \<FF>'_def b_def r_def b'_def f'_def Q_def xx_def to_rdg_def
                     e_def f_def  E'_def r'_def y'_def x'_def xy_def yy_def y_def x_def \<FF>_def E''_def cards_def cards'_def
                     \<gamma>_def \<FF>_imp_def \<FF>_imp'_def nb_def nb'_def
          by ((auto; ((subst sym[OF arg_cong[OF sym[OF 1(3)], of the, simplified]])+ | simp)+), auto)
       using 12 by simp
    next
    case (2 g h xeb ya )
    show ?case
      apply(rule HOL.forw_subst[of _ state'])
      apply(insert 2)
       apply(subst (asm) sym[OF 13])+
      subgoal
          apply(rule Algo_state.equality) 
          unfolding state'_def to_rdg'_def \<FF>'_def b_def r_def b'_def f'_def Q_def xx_def to_rdg_def
                     e_def f_def  E'_def r'_def y'_def x'_def xy_def yy_def y_def x_def \<FF>_def 
                     E''_def cards_def cards'_def \<FF>_imp_def \<FF>_imp'_def nb_def nb'_def
          \<gamma>_def by ((auto; ((subst sym[OF arg_cong[OF sym[OF 2(3)], of the, simplified]])+ | simp)+), auto)
       using 12 by simp
  qed
qed

lemma maintain_forest_invar_aux_pres:
  assumes "maintain_forest_dom state"
          "aux_invar state"
  shows   "aux_invar (maintain_forest state)"
  using assms(2) 
  apply(induction rule: maintain_forest_induct[OF assms(1)])
     using maintain_forest_simps  invar_aux_pres_one_step 
     by (fastforce intro: maintain_forest_cases)

lemma termination_of_maintain_forest:
  assumes "invar_aux1 state"
          "n = card (to_set (actives state))"
          "invar_aux17 state"
  shows "maintain_forest_dom state"
  using assms 
proof(induction n arbitrary: state rule: less_induct)
  case (less n)
  then show ?case 
  proof(cases "maintain_forest_call_cond state")
    case True
    define \<FF> where "\<FF> = Algo_state.\<FF> state"
  define f where "f = current_flow state"
  define r where "r = representative state"
  define E' where "E' = actives state"
  define \<gamma> where "\<gamma> = current_\<gamma> state"
  define cards where "cards = comp_card state"
  define \<FF>_imp where "\<FF>_imp  = Algo_state.\<FF>_imp state"
  define e where "e = the ( get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  define x where "x = fst e"
  define y where "y= snd e"
  define xy where "xy = (if cards x \<le> cards y 
                                       then (x,y) else (y,x))"
  define xx where "xx = prod.fst xy"
  define yy where "yy = prod.snd xy"
  define \<FF>' where  "\<FF>' = insert {fst e, snd e} \<FF>"
  define \<FF>_imp' where "\<FF>_imp' = insert_undirected_edge (fst e) (snd e) \<FF>_imp"
  define x' where "x' = r xx"
  define y' where  "y' = r yy"
  define E'' where "E'' = filter (\<lambda> d. {r (fst d), r (snd d)} \<noteq> {x', y'}) E'"

  have actives_upd:"E'' = actives (maintain_forest_upd state)"
    using \<FF>_def f_def  r_def E'_def  \<gamma>_def e_def x_def y_def
                                 xy_def xx_def yy_def \<FF>'_def x'_def y'_def  E''_def cards_def 
    by(intro maintain_forest_upd_actives_unfold[of \<FF> state f r \<gamma> E' cards e x y xy xx], simp+)

  have set_invar_E': "set_invar E'"
    using E'_def less invar_aux17_def by blast

  have E'_substE:"to_set E' \<subseteq> \<E>"
    using less by(simp add: E'_def invar_aux1_def)

  have "\<exists> e. e \<in> to_set E' \<and> 8 * real N * \<gamma> < f e"
    unfolding E'_def \<gamma>_def f_def
    apply(rule maintain_forest_call_condE[OF True])
    using set_get(1-3)[OF set_invar_E', simplified E'_def] 
    by fastforce

  then obtain ee where ee_prop:" ee \<in> to_set E' \<and> 8 * real N * \<gamma> < f ee"
    by auto

  have e_prop: "e \<in> to_set E' \<and> f e > 8 * real N *\<gamma>"
    apply(rule maintain_forest_call_condE[OF True])
    using   ee_prop E'_substE set_get(1-3)[OF set_invar_E'] 
    by(fastforce simp add: E'_def f_def e_def \<gamma>_def)

  have e_in_E:"e \<in> to_set E'"
    apply(rule maintain_forest_call_condE[OF True])
    using  set_get(1-3)[OF set_invar_E', simplified E'_def]
    by(auto simp add:  e_def E'_def f_def \<gamma>_def)

  hence einE: "e \<in> \<E>"
    using less by(auto simp add:  invar_aux1_def E'_def)

  have 114: "{x', y'} = {r (fst e), r(snd e)}"
    by(auto simp add: x'_def y'_def xx_def yy_def xy_def x_def y_def)

  have 113: "to_set E'' \<subseteq> to_set E' - {e}"
    using 114 set_filter(1)[OF set_invar_E'] E''_def  by force

  moreover have "finite (to_set E')"
    using  E'_substE finite_E rev_finite_subset[of \<E> "to_set E'"] by simp

  ultimately have 115: "card (to_set E'') < card (to_set E')"
    using e_in_E psubset_card_mono[of "to_set E'" "to_set E''"] by auto

  have card_less: "card (to_set (actives (maintain_forest_upd state))) < n"
    using actives_upd 115 less(3)  E'_def by simp

  have inva_aux1: "invar_aux1 (maintain_forest_upd state)"
    using actives_upd 113 less(2) E'_def 
    by(auto elim: invar_aux1E intro: invar_aux1I)

  have invar_aux17: "invar_aux17 (maintain_forest_upd state)"
    using actives_upd  invar_filter[OF set_invar_E', of "(\<lambda> d. {r (fst d), r (snd d)} \<noteq> {x', y'})"]
    by(simp add:invar_aux17_def E''_def)
   
  have "maintain_forest_dom (maintain_forest_upd state)"
     using card_less invar_aux1_def[of state]  "113" E'_substE 
           invar_aux_pres_one_step[of state] inva_aux1 invar_aux17
    by (auto intro: less(1)[of "card (to_set (actives (maintain_forest_upd state)))"])

  thus ?thesis 
    by(auto intro: maintain_forest_dom_upd simp add: True)
  next
    case False
   define \<FF> where "\<FF> = Algo_state.\<FF> state"
   define f where "f = current_flow state"
   define E' where "E' = actives state"
   define \<gamma> where "\<gamma> = current_\<gamma> state"
   have "\<nexists> aa. get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E' = Some aa"
     using False option.collapse
     by(force split: if_split prod.splits simp add: E'_def f_def \<gamma>_def maintain_forest_call_cond_def Let_def)  
   thus ?thesis
    by (auto intro: maintain_forest.domintros simp add: E'_def \<gamma>_def f_def )
  qed
qed

lemma termination_of_maintain_forest':
  assumes "aux_invar state"
  shows "maintain_forest_dom state"
  using assms termination_of_maintain_forest 
  by(simp add: aux_invar_def)

lemma invar_gamma_pres_one_step:
  assumes "maintain_forest_call_cond state"
          "invar_gamma state" 
    shows "invar_gamma (maintain_forest_upd state)"
  using assms(2) 
  by(auto elim: maintain_forest_call_condE[OF assms(1)] 
         split: if_split prod.split simp add: maintain_forest_upd_def Let_def invar_gamma_def)

lemma invars_pres_one_step:
  assumes "maintain_forest_call_cond state"
          "aux_invar state"
  shows 
        "thr \<ge> 0 \<Longrightarrow> invarA_1 thr state \<Longrightarrow> invarA_1 thr (maintain_forest_upd state)"

        "thr2 \<ge> 0 \<Longrightarrow> invarA_1 thr2 state \<Longrightarrow> invarA_2 thr1 thr2 state 
         \<Longrightarrow> thr2 \<le> 2 * current_\<gamma> state \<Longrightarrow> thr1 \<le> 8*real N * current_\<gamma> state 
         \<Longrightarrow> invarA_2 thr1 thr2 (maintain_forest_upd state)"

        "invar_gamma state \<Longrightarrow> thr2 \<ge> 0  \<Longrightarrow>invarA_1 thr2 state \<Longrightarrow> invarA_2 thr1 thr2 state \<Longrightarrow>
         thr2 \<le> 2 * current_\<gamma> state \<Longrightarrow> thr1 = 8*real N * current_\<gamma> state \<Longrightarrow>
         invar_isOptflow state \<Longrightarrow> invar_isOptflow (maintain_forest_upd state)"
proof-
  define a\<FF> where "a\<FF> = Algo_state.\<FF> state"
  define f where "f = current_flow state"
  define b where "b = balance state"
  define r where "r = representative state"
  define E' where "E' = actives state"
  define to_rdg where "to_rdg = conv_to_rdg state"
  define \<gamma> where "\<gamma> = current_\<gamma> state"
  define cards where "cards = comp_card state"
  define \<FF>_imp where "\<FF>_imp = Algo_state.\<FF>_imp state"
  define e where "e = the ( get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  define x where "x = fst e"
  define y where "y= snd e"
  define to_rdg' where "to_rdg' = (\<lambda> d. if d = make_pair e then F e
                                             else if prod.swap d = make_pair e then B e 
                                             else to_rdg d)"
  define xy where "xy = (if cards x \<le> cards y
                                       then (x,y) else (y,x))"
  define xx where "xx = prod.fst xy"
  define yy where "yy = prod.snd xy"
  define a\<FF>' where  "a\<FF>' = insert {fst e, snd e} a\<FF>"
  define \<FF>_imp' where "\<FF>_imp' = insert_undirected_edge (fst e) (snd e) \<FF>_imp"
  define x' where "x' = r xx"
  define y' where  "y' = r yy"
  define Q where  "Q = get_path x' y' \<FF>_imp'"
  define f' where "f' = (if b x' > 0 
                                   then augment_edges f (b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges f (- b x') (to_redge_path to_rdg' (rev Q)))"
  define b' where "b' = (\<lambda> v. if v= x' then 0 
                                        else if v = y' then b y' + b x'
                                        else b v)"
  define E'' where "E'' = filter (\<lambda> d. {r (fst d), r (snd d)} \<noteq> {x', y'}) E'"
  define r' where "r' = (\<lambda> v. if r v = x' \<or> r v = y' then y' else r v)"
  define cards' where "cards' = (\<lambda> v. if r' v = y' then cards x +cards y else cards v)"
  define nb where "nb = not_blocked state"
  define nb' where "nb' = (\<lambda> d. if e = d then True
                                        else if {r (fst d) , r (snd d)} = {x', y'} then False
                                        else nb d)"
  define state' where "state' = state \<lparr>  \<FF> := a\<FF>', current_flow := f',
                                    balance := b',  representative := r',
                                    actives := E'', conv_to_rdg := to_rdg', comp_card := cards',
                                    \<FF>_imp:= \<FF>_imp', not_blocked := nb'\<rparr>"
  have state_state':"state' = maintain_forest_upd state"
      by(rule maintain_forest_upd_unfold[OF a\<FF>_def f_def b_def r_def E'_def to_rdg_def \<gamma>_def cards_def \<FF>_imp_def e_def x_def y_def
                                to_rdg'_def xy_def xx_def yy_def a\<FF>'_def \<FF>_imp'_def x'_def y'_def Q_def f'_def
                                b'_def E''_def r'_def cards'_def nb_def nb'_def state'_def])

have set_invar_E': "set_invar E'"
    using E'_def assms aux_invar_def invar_aux17_def by blast

  have E'_substE:"to_set E' \<subseteq> \<E>"
    using assms by(simp add: E'_def aux_invar_def invar_aux1_def)

  define \<FF> where  "\<FF> = to_graph \<FF>_imp"
  define \<FF>' where "\<FF>' = to_graph \<FF>_imp'"

  have F_rewrite:  "\<FF>' = insert {fst e, snd e} \<FF>"
    unfolding \<FF>_imp'_def \<FF>'_def \<FF>_def \<FF>_imp_def
    apply(subst insert_abstraction)
    using assms(2)
    by(auto simp add:  aux_invar_def invar_aux21_def invar_aux20_def invar_aux19_def invar_aux18_def
                       invar_aux17_def)

  have "\<exists> e. e \<in> to_set E' \<and> 8 * real N * \<gamma> < f e"
    unfolding E'_def \<gamma>_def f_def
    apply(rule maintain_forest_call_condE[OF assms(1)])
    using set_get(1-3)[OF set_invar_E', simplified E'_def] 
    by fastforce

  then obtain ee where ee_prop:" ee \<in> to_set E' \<and> 8 * real N * \<gamma> < f ee"
    by auto

  have e_prop: "e \<in> to_set E' \<and> f e > 8 * real N *\<gamma>"
    apply(rule maintain_forest_call_condE[OF assms(1)])
    using   ee_prop E'_substE set_get(1-3)[OF set_invar_E'] 
    by(fastforce simp add: E'_def f_def e_def \<gamma>_def)

  have fste_V: "fst e \<in> \<V>" 
    apply(rule aux_invarE[OF assms(2)])
    using e_prop dVsI' dVsI' make_pair[OF refl refl ]
    by(auto simp add: invar_aux1_def  E'_def )

  have snde_V: "snd e \<in> \<V>" 
    apply(rule aux_invarE[OF assms(2)])
    using e_prop dVsI'  make_pair[OF refl refl ]
    by(auto simp add: invar_aux1_def  E'_def)

  have "xx \<in> \<V>" 
    by (simp add: xx_def xy_def x_def y_def fste_V snde_V)

  hence x'_inV: "x' \<in> \<V>"
    using assms(2) by(simp add:x'_def aux_invar_def invar_aux9_def r_def)

  have "yy \<in> \<V>" unfolding yy_def xy_def x_def y_def
    by (simp add: fste_V snde_V yy_def xy_def x_def y_def)

  hence y'_inV: "y' \<in> \<V>"
    using assms(2)by(simp add: y'_def aux_invar_def invar_aux9_def r_def)

  have 01:"reachable \<FF> xx x' \<or> xx = x'"
    using assms(2) F_rewrite[simplified \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def] 
    by(simp add:aux_invar_def invar_aux8_def \<FF>_def x'_def r_def \<FF>_imp_def)

  have 02:"reachable \<FF> yy y' \<or> yy = y'"
    using assms(2) F_rewrite[simplified \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def] 
    by(simp add: aux_invar_def invar_aux8_def \<FF>_def y'_def r_def \<FF>_imp_def)

  hence 1100:"connected_component \<FF> (fst e) \<noteq> connected_component \<FF> (snd e)"
    using e_prop assms(2)
    by(simp add: invar_aux11_def aux_invar_def \<FF>_imp_def \<FF>_imp'_def \<FF>'_def E'_def \<FF>_def)

  have fst_snd_e_neq: "fst e \<noteq> snd e"
    using  1100 by auto

  hence x_not_y:"x \<noteq> y"
    using x_def y_def by simp

  have 11:"to_rdgs to_pair (\<lambda>d. if d = make_pair e then F e else
                            if prod.swap d = make_pair e then B e else to_rdg d) 
           {{fst e, snd e}} =
       {F e, B  e}"
    using assms(2) to_rdg_def x_def x_not_y y_def 
    by (auto simp add: aux_invar_def  invar_aux6_def )

    have aa: "to_rdgs to_pair to_rdg' (insert {fst e, snd e} \<FF>) = 
          to_rdgs to_pair to_rdg' {{fst e, snd e}} \<union> to_rdgs to_pair to_rdg' (\<FF>-{{fst e, snd e}})" 
      unfolding to_rdgs_def by blast
    have bb: "to_rdgs to_pair to_rdg' (\<FF>-{{fst e, snd e}}) = 
            to_rdgs to_pair to_rdg (\<FF>-{{fst e, snd e}})"
      using to_rdgs_update_not_in[of to_rdg e \<FF>] assms(2) 
        by(simp add: aux_invar_def invar_aux6_def to_rdg_def to_rdg'_def)
    have 110:"to_rdgs to_pair to_rdg' (insert {fst e, snd e} \<FF>) = 
          to_rdgs to_pair to_rdg'{{fst e, snd e}} \<union> to_rdgs to_pair to_rdg (\<FF> - {{fst e, snd e}})"  
      using 11 aa bb by simp
   have 111: "... = {F e, B e}
          \<union> to_rdgs to_pair to_rdg (\<FF> - {{fst e, snd e}}) "
    using 11 to_rdg'_def by simp

    have asm': "invar_aux11 state" using assms  aux_invar_def by auto

    have cards_same_cond: "card (connected_component \<FF> x) \<le> card (connected_component \<FF> y) \<longleftrightarrow>
                          cards x \<le> cards y"
      using assms(2) F_rewrite
      by (simp add: cards_def \<FF>_def aux_invar_def invar_aux16_def \<FF>_imp_def fste_V snde_V x_def y_def)

    have x'_not_y':"x' \<noteq> y'" 
      proof
        assume " x' = y'"
        hence "connected_component \<FF> x = connected_component \<FF> y"
          using 01 02 xx_def yy_def xy_def cards_same_cond
           connected_components_member_eq[of x' \<FF> xx]  in_connected_componentI[of \<FF> xx x'] 
           connected_components_member_eq[of y' \<FF> yy]  in_connected_componentI[of \<FF> yy y']
          by(cases "card (connected_component \<FF> x) \<le> card (connected_component \<FF> y)", auto)
        thus False
          using asm' e_prop F_rewrite[simplified \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def] 
          by(simp add:invar_aux11_def x_def y_def  E'_def \<FF>_def \<FF>_imp_def)
     qed
     have comps_inter_empt:"connected_component \<FF> y' \<inter> connected_component \<FF> x' = {}" 
       using "01" "02" "1100" x_def xx_def xy_def  y_def yy_def cards_same_cond
             connected_components_member_eq[of y' \<FF> yy, OF in_connected_componentI[of \<FF> yy y']]  
             connected_components_member_eq[of x' \<FF> xx, OF in_connected_componentI[of \<FF> xx x']]
       by(intro unequal_components_disjoint[where X=UNIV], 
          cases "card (connected_component \<FF> x) \<le> card (connected_component \<FF> y)", auto)
     have comp_y_y':"connected_component (insert {fst e, snd e} \<FF>) y' =
          connected_component (insert {fst e, snd e} \<FF>) y"
      apply(subst connected_components_member_eq[ of y' \<FF>' yy, simplified F_rewrite] )
      using "02" in_connected_componentI[of \<FF>' yy y'] reachable_subset[of \<FF> yy y' \<FF>'] \<FF>'_def 
      in_connected_componentI2[of yy y' \<FF>'] new_edge_disjoint_components[of x y \<FF>]  x_def xy_def y_def yy_def
        F_rewrite \<FF>_def \<FF>'_def
      by (fastforce, auto)
     have comps_union:"connected_component \<FF>' y' =
                      connected_component \<FF> y' \<union> connected_component \<FF> x'"
      apply(subst connected_components_member_eq[of x' \<FF> xx])
      subgoal 
        using "01" in_connected_componentI[of \<FF> xx x'] in_own_connected_component[of x' \<FF>]
        by auto
      apply(subst connected_components_member_eq[of y' \<FF> yy])
      subgoal 
        using "02" in_connected_componentI[of \<FF> yy y'] in_own_connected_component[of y' \<FF>]
        by auto
      apply(rule trans[of _ "connected_component (insert {fst e, snd e} \<FF>) y"])
      subgoal using comp_y_y' F_rewrite \<FF>'_def by simp 
      apply(rule trans, rule sym[OF insert_edge_endpoints_same_component[of "(insert {fst e, snd e} \<FF>)" _ x \<FF>]])
      using x_def y_def  xx_def xy_def yy_def  
      by(auto split: if_split simp add: insert_commute)

     have "fst e \<noteq> snd e"
      using 1100  by auto
    hence concretization_of_F': "to_rdgs to_pair to_rdg' \<FF>' =
                                { F e, B e} \<union> to_rdgs to_pair to_rdg (\<FF> - {{fst e, snd e}}) "
      using 111 110 bb aa F_rewrite unfolding \<FF>'_def \<FF>_imp_def by simp

    have consist_to_rdg':"consist to_rdg'" 
      using  invar_aux_pres_one_step[of state, OF assms(2) assms(1), simplified sym[OF state_state']] 
      unfolding state'_def aux_invar_def invar_aux6_def by simp

    have axioms_conds1: "x' \<in> Vs \<FF>'" 
      using comps_union in_connected_component_in_edges[of x' \<FF>' y'] x'_not_y' in_own_connected_component[of x' \<FF>]
      by simp
    have axioms_conds2: "Vs \<FF>' \<subseteq> \<V> "
      using assms(2) fste_V snde_V F_rewrite[simplified \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def] 
      unfolding aux_invar_def invar_aux15_def \<FF>'_def \<FF>_def Vs_def \<FF>_imp_def \<FF>_imp'_def
      by simp
    have axioms_conds3: "graph_invar \<FF>'"
      using assms(2) F_rewrite[simplified \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def] 
      unfolding aux_invar_def invar_aux14_def \<FF>'_def \<FF>_def validF_def 
      using \<FF>'_def \<V>_finite axioms_conds2 finite_subset fst_snd_e_neq local.\<FF>_def 
      unfolding \<FF>_imp_def \<FF>_imp'_def \<FF>_def \<FF>'_def by fastforce

    have goodF:"goodF \<FF>_imp" 
      by (simp add: Pair_graph_specs_from_aux_invar assms(2) local.\<FF>_imp_def)
    have adjmap_invF: "adjmap_inv \<FF>_imp"
      by (simp add: assms(2) from_aux_invar'(18) local.\<FF>_imp_def)
    have goodF':"goodF \<FF>_imp'"
      using  \<FF>_imp_def goodF
      by (auto intro: Pair_Graph_Specs_insert_undirected_edge_pres 
            simp add: \<FF>_imp'_def assms(2) from_aux_invar'(18) \<FF>_imp_def goodF)
      
    have fit_together: "fit_together \<FF>' \<FF>_imp'"
      using invar_aux_pres_one_step[OF assms(2) assms(1), simplified sym[OF state_state']]
      by(simp add: aux_invar_def invar_aux19_def invar_aux20_def state'_def
                fit_together_def \<FF>'_def \<FF>_imp'_def invar_aux21_def)

  obtain qqq where qqq_prop:"vwalk_bet (digraph_abs  \<FF>_imp') x' qqq y'"
    using comps_union connected_components_member_sym[of x' \<FF>' y'] 
          axioms_conds1 axioms_conds2 axioms_conds3
           in_connected_componentE[of y' \<FF>' x'] in_connected_componentI2[of x' x' \<FF>]  x'_not_y' 
          from_reachable_to_dircted_walk[OF fit_together, of x' y'] goodF'
    by auto

  have finiteF: "finite (to_graph \<FF>_imp')" 
    using \<FF>'_def axioms_conds3 graph_abs.finite_E graph_abs.intro by auto

  have x'_inVs:"x' \<in> Vs (to_graph \<FF>_imp')"
    using Vs_def \<FF>'_def axioms_conds1 by fastforce

   have distinctQ: "distinct Q"
     using qqq_prop  invar_aux_pres_one_step[OF assms(2) assms(1), simplified sym[OF state_state']] 
           x'_inVs x'_not_y'
      by (auto intro: get_path_axioms_unfolded(2)[of \<FF>_imp' x' qqq y'] 
            simp add:  aux_invar_def invar_aux19_def invar_aux18_def state'_def Q_def )

    have oedge_of_Q:"oedge ` List.set (to_redge_path to_rdg' Q) = 
          oedge ` to_rdgs to_pair to_rdg' (List.set (edges_of_path Q))"
      using oedge_of_to_redgepath_subset[of Q to_rdg'] consist_to_rdg' distinctQ by simp

    have redge_of_Q:"List.set (to_redge_path to_rdg' Q) \<subseteq> 
          to_rdgs to_pair to_rdg' (List.set (edges_of_path Q))"
      using to_redgepath_subset[of Q to_rdg'] consist_to_rdg' distinctQ by auto

    have redge_of_Q_rev:"List.set (to_redge_path to_rdg' (rev Q)) \<subseteq> 
          to_rdgs to_pair to_rdg' (List.set (edges_of_path Q))"
      using to_redgepath_rev_subset[of Q to_rdg'] consist_to_rdg' distinctQ by auto

    have oedge_of_Q_rev: "oedge ` List.set (to_redge_path to_rdg' (rev Q)) = 
          oedge ` to_rdgs to_pair to_rdg' (List.set (edges_of_path Q))"
      using oedge_of_to_redgepath_subset[of Q to_rdg'] consist_to_rdg' distinctQ
            oedge_of_to_redge_path_rev[of Q to_rdg'] by simp
          
    have flow_change_in_Q:"f' d \<noteq> f d \<Longrightarrow> d \<in> oedge ` to_rdgs to_pair to_rdg' (List.set (edges_of_path Q))" for d
      unfolding f'_def
      using e_not_in_es_flow_not_change[of "(to_redge_path to_rdg' Q)" d f "b x'"]
            e_not_in_es_flow_not_change[of "(to_redge_path to_rdg' (rev Q))" d f "- b x'"]
            oedge_of_Q oedge_of_Q_rev
      by (smt (verit, del_insts) image_eqI)  
   
    have Q_subset_F':"List.set Q \<subseteq> connected_component \<FF>' y'"
    proof(subst sym[OF connected_components_member_eq[of x' \<FF>' y']], goal_cases)
      case 1
      then show ?case 
      using comps_union in_own_connected_component[of _ \<FF>] 
            by simp
  next
    case 2
    show ?case
      using  invar_aux_pres_one_step[OF assms(2) assms(1), simplified sym[OF state_state']] qqq_prop 
      unfolding Q_def           
      apply (intro walk_betw_subset_conn_comp[of \<FF>' x' "get_path x' y' \<FF>_imp'" y', 
               OF from_directed_walk_to_undirected_walk[OF fit_together goodF']]) 
      by(auto intro!: get_path_axioms_unfolded(1)[of \<FF>_imp' x' qqq y', OF _ _ _ x'_inVs _ x'_not_y', simplified \<FF>_imp_def \<FF>_imp'_def \<FF>'_def ]
               simp add: \<FF>_def \<FF>_imp_def \<FF>_imp'_def \<FF>'_def validF_def  invar_aux14_def state'_def
                         aux_invar_def invar_aux19_def invar_aux18_def) 
  qed

    have dVs_Q:"dVs (to_vertex_pair ` to_rdgs to_pair to_rdg' (List.set (edges_of_path Q))) \<subseteq> List.set Q"
        using consist_dVs_path consist_to_rdg' distinctQ by blast
            
      hence f_change_comp_y':"f' d \<noteq> f d \<Longrightarrow> fst d \<in> connected_component \<FF>' y'" for d
        using  Q_subset_F'  flow_change_in_Q[of d]  v_in_edge_in_path_gen[of  "{fst d, snd d}" Q "fst d"] 
                consist_to_rdg' in_oedge_F_to_in_undirected_F[of d to_rdg']
        by auto

    have comps_representative:"connected_component \<FF> v = connected_component \<FF> (r v)" for v
      apply(rule aux_invarE[of state, OF assms(2), simplified invar_aux8_def] )
      using connected_components_member_eq[of "r v" \<FF> v, OF in_connected_componentI[of \<FF> v "r v"]]
            local.\<FF>_def r_def  F_rewrite[simplified \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def]
      unfolding \<FF>_imp_def
      by force
      
    have 144:"connected_component \<FF> v \<subseteq> connected_component \<FF>' v" for v
           unfolding \<FF>'_def 
           using  con_comp_subset subset_insertI F_rewrite \<FF>_def \<FF>'_def \<FF>_imp'_def
           by metis
    have 154:"v \<in> \<V> \<Longrightarrow> connected_component \<FF>' v \<subseteq> \<V>" for v
      using invar_aux_pres_one_step[OF assms(2) assms(1), simplified sym[OF state_state']]
      by(simp add: aux_invar_def invar_aux10_def  state'_def  \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def)
    have 157:"v \<in> \<V> \<Longrightarrow> connected_component \<FF> v \<subseteq> \<V>" for v
      using "144" "154" by blast
    have 155: "card (connected_component \<FF> y') \<ge> card (connected_component \<FF> x')"
            using comps_representative cards_same_cond
            by(auto simp add: y'_def x'_def xx_def yy_def xy_def split: if_split)

    have Q_inF':"(List.set (edges_of_path Q)) \<subseteq>  \<FF>'"   
      using from_directed_walk_to_undirected_walk[OF fit_together goodF' 
              axioms_conds3 get_path_axioms_unfolded(1)[of \<FF>_imp' x' qqq y' Q, simplified Q_def, OF qqq_prop]]
              invar_aux_pres_one_step[OF assms(2) assms(1), simplified sym[OF state_state']] qqq_prop 
              x'_inVs x'_not_y'
      by(auto intro!: path_edges_subset simp add: aux_invar_def invar_aux19_def invar_aux18_def state'_def walk_betw_def Q_def)

      have x'_y'_reachable:"reachable \<FF>' x' y'"
        using comps_union in_connected_componentE[of x' \<FF>' y']
              in_connected_componentI2[of x' x' \<FF>] reachable_sym[of \<FF>' y' x']  x'_not_y' by auto

      have lengthQ:"length Q \<ge> 2"
        apply(rule ccontr, rule sufficientE[of "length Q = 0 \<or> length Q = 1"], linarith)
        using get_path_axioms_unfolded(1)[of \<FF>_imp' x' qqq y' Q, simplified Q_def, OF qqq_prop] x'_not_y' 
             hd_last_same[of Q] x'_inVs
             invar_aux_pres_one_step[OF assms(2) assms(1), simplified sym[OF state_state']] 
       by(auto simp add: aux_invar_def invar_aux19_def invar_aux18_def state'_def vwalk_bet_def Q_def)
     
  show "thr \<ge> 0  \<Longrightarrow> invarA_1 thr state \<Longrightarrow> invarA_1 thr (maintain_forest_upd state)"
  proof-
    assume asm: "thr \<ge> 0"  "invarA_1 thr state"
    have bx':"\<bar> b x' \<bar> \<le> thr*card (connected_component \<FF> x')"
      using asm x'_inV F_rewrite \<FF>'_def unfolding  invarA_1_def b_def \<FF>_imp_def \<FF>_def
      by simp
    have by':"\<bar> b y' \<bar> \<le> thr*card (connected_component \<FF> y')"
      using asm y'_inV unfolding invarA_1_def b_def \<FF>_def \<FF>_imp_def
      by simp
   have y'_card:"\<bar> b' y'\<bar> \<le> thr * card (connected_component \<FF>' y')"
      apply(subst comps_union, subst card_Un_disjnt)
      using comps_inter_empt x'_not_y' bx' by' comps_inter_empt assms(2) x'_inV \<V>_finite
            finite_subset y'_inV  F_rewrite[simplified \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def]
      by(auto simp add: algebra_simps card_Un_disjnt disjnt_def  b'_def  aux_invar_def invar_aux10_def  
                      \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def) blast+
   moreover have 16:"v \<in> \<V> \<Longrightarrow> v \<noteq> x'  \<Longrightarrow> v \<noteq> y' \<Longrightarrow> \<bar> b' v \<bar>\<le> thr * card (connected_component \<FF>' v)" for v
      unfolding b'_def apply simp
      apply(rule order.trans[of _ "thr * real (card (connected_component \<FF> v))"])
      subgoal
        using asm  \<V>_finite \<FF>_imp_def  by (auto simp add:  invarA_1_def b_def \<FF>'_def \<FF>_def )
      subgoal
        using 144[of v] 154[of v] asm(1) \<V>_finite 
              card_mono[of "connected_component \<FF>' v" "connected_component \<FF> v"] rev_finite_subset
        by (intro mult_left_mono, auto intro: mult_left_mono)
      done
    ultimately show "invarA_1 thr (maintain_forest_upd state)"
      using sym[OF state_state'] asm(1) sym[OF F_rewrite]
      unfolding invarA_1_def state'_def \<FF>_imp_def  b'_def \<FF>_def \<FF>_imp'_def \<FF>'_def
      by auto
  qed
    
  show "thr2 \<ge> 0  \<Longrightarrow>invarA_1 thr2 state \<Longrightarrow> invarA_2 thr1 thr2 state \<Longrightarrow>
        thr2 \<le> 2 * current_\<gamma> state \<Longrightarrow> thr1 \<le> 8*real N * current_\<gamma> state
               \<Longrightarrow>invarA_2 thr1 thr2 (maintain_forest_upd state)"    
    proof-
      assume asm: "thr2 \<ge> 0"  "invarA_1 thr2 state" "invarA_2 thr1 thr2 state"
                  "thr2 \<le> 2 * current_\<gamma> state" "thr1 \<le> 8*real N * current_\<gamma> state"
    show " invarA_2 thr1 thr2 (maintain_forest_upd state)"
    proof-
      have "d \<in> to_rdgs to_pair to_rdg' (to_graph \<FF>_imp') \<Longrightarrow>
         thr1 - thr2 * real (card (connected_component (to_graph \<FF>_imp') (fst (oedge d)))) < f' (oedge d)" for d
      proof-
      assume asm2:"d \<in> to_rdgs to_pair to_rdg' (to_graph \<FF>_imp')"
      hence "d \<in> \<EE>" 
        using invar_aux_pres_one_step[OF assms(2) assms(1), simplified sym[OF state_state']]
        by (auto simp add: aux_invar_def invar_aux2_def state'_def  \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def)
      hence fstdV:"fst (oedge d) \<in> \<V>" 
        using dVsI'(1)[of ] o_edge_res make_pair[OF refl refl]  fst_E_V by presburger
      hence compd:"connected_component \<FF>' (fst (oedge d)) \<subseteq> \<V>"
        using invar_aux_pres_one_step[OF assms(2) assms(1), simplified sym[OF state_state']]
        by(auto simp add: aux_invar_def invar_aux10_def state'_def \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def)
      hence finite_compd:"finite (connected_component \<FF>' (fst (oedge d)) )" 
        using \<V>_finite finite_subset by blast
       have d_prop:"d \<in> to_rdgs to_pair to_rdg' \<FF> \<or> oedge d = e"
         using concretization_of_F' \<FF>_def F_rewrite
          by (smt (verit, ccfv_threshold) Diff_empty Diff_insert0 Un_iff \<FF>'_def asm2 bb insert_absorb insert_iff insert_not_empty oedge.simps(1) oedge.simps(2) prod.collapse prod.swap_def)       
      show "thr1 - thr2 * real (card (connected_component (to_graph \<FF>_imp') (fst (oedge d)))) < f' (oedge d)"
      proof(cases "f (oedge d) = f' (oedge d)")
        case True
       have "d \<in> to_rdgs to_pair to_rdg' \<FF> \<Longrightarrow> 
             thr1 - thr2 * real (card (connected_component \<FF> (fst (oedge d)))) < f (oedge d)"
        proof-
          assume "d \<in> to_rdgs to_pair to_rdg' \<FF>"
          hence "oedge d \<in> oedge ` to_rdgs to_pair (conv_to_rdg state) \<FF>" 
            using F_rewrite
            by (metis Int_iff Un_iff  bb comps_inter_empt comps_union empty_iff image_eqI 
                      in_connected_componentI2 insert_absorb  single_diff_remove to_rdg_def)
          thus "thr1 - thr2 * real (card (connected_component \<FF> (fst (oedge d)))) < f (oedge d)"
            using asm(3) unfolding invarA_2_def \<FF>_def  f_def \<FF>_imp_def
            by auto
        qed
        moreover have "oedge d = e \<Longrightarrow> f (oedge d) > thr1" 
          using \<gamma>_def asm(5) e_prop by auto
        moreover have "card (connected_component \<FF> (fst (oedge d))) \<le> 
             card (connected_component \<FF>' (fst (oedge d)))"
          using F_rewrite
          by (metis  card_mono con_comp_subset finite_compd subset_insertI)
        ultimately show ?thesis using asm finite_compd d_prop True 
           F_rewrite \<FF>_def \<FF>'_def
          by (smt (verit, best) True mult_nonneg_nonneg of_nat_0_le_iff of_nat_le_iff 
              ordered_comm_semiring_class.comm_mult_left_mono)
      next
        case False
        hence 101:"fst (oedge d) \<in> connected_component \<FF>' y'" using f_change_comp_y' by simp
        hence 102:"fst (oedge d) \<in> connected_component \<FF> y' \<or>
               fst (oedge d) \<in> connected_component \<FF> x'" 
          by (simp add: comps_union)
        hence 106: "connected_component \<FF>' (fst (oedge d)) = connected_component \<FF>' y'"
          using 101 
          by (meson connected_components_member_eq)
        have 107: "connected_component \<FF> (fst (oedge d)) = connected_component \<FF> y'  \<or>
                   connected_component \<FF> (fst (oedge d)) =  connected_component \<FF> x'" 
          using 102
          by (meson connected_components_member_eq)
        have 103:"\<bar> b x'\<bar>  \<le> thr2 * real (card (connected_component \<FF> x'))"
          using asm(2) x'_inV
          by (simp add: \<FF>_def \<FF>'_def \<FF>_imp_def \<FF>_imp'_def  invarA_1_def  b_def)
        have 110:"f' (oedge d)  \<ge> f (oedge d) - \<bar> b x' \<bar>"
            using distinct_path_augment[of "to_redge_path to_rdg' Q" " \<bar> b x' \<bar>" f "oedge d"]
                  distinct_path_augment[of "to_redge_path to_rdg' (rev Q)" " \<bar> b x' \<bar>" f "oedge d"]
                  to_rdg_distinct[of to_rdg' Q] to_rdg_distinct[of to_rdg' "rev Q"]
                  consist_to_rdg' distinctQ 
            by(auto simp add: f'_def split: if_split)
        show ?thesis 
        proof(rule orE'[OF d_prop], goal_cases)
          case 1
          hence 109:"f (oedge d) > thr1 - thr2 * real (card (connected_component \<FF> (fst (oedge d))))"
            using asm(3) F_rewrite unfolding invarA_2_def  \<FF>_def
            to_rdg'_def f_def to_rdg_def 
            by (metis (no_types, lifting) "1"(1) "1100"  \<FF>_imp_def bb insert_edge_endpoints_same_component doubleton_eq_iff imageI inf_sup_aci(5) insert_absorb local.\<FF>_def single_diff_remove to_rdg_def)
          show ?case 
            apply(subst  106[simplified \<FF>'_def])
            apply(subst comps_union[simplified \<FF>'_def])
            apply(subst card_Un_disjnt)
            using comps_inter_empt  144[of x'] 144[of y']
                  154[OF x'_inV] 154[OF y'_inV]  \<V>_finite 
                  finite_subset[of "connected_component \<FF> _"] finite_subset[of "connected_component \<FF>' _"]
            unfolding disjnt_def  
            apply(simp, simp, simp)

            apply(cases rule: orE[OF 107])
            subgoal
              using 103 110 109           
              apply(auto simp add: algebra_simps)
              done
            subgoal 
              apply(rule order.strict_trans2[of _ "f (oedge d) - \<bar>b x'\<bar>", OF  _ 110])
              apply(rule order.strict_trans1[of _ "thr1 -
                        thr2 * real (card (connected_component \<FF> (fst (oedge d)))) - \<bar> b x' \<bar>"])              
              using 103 109 155 asm(1) 
              apply (smt (verit, best) distrib_left mult_left_mono of_nat_add real_mono)
              using 103 109  asm(1) by simp
            done
        next
          case 2
          have strict_non_strict_mono: "(a::real) < b \<Longrightarrow> c \<ge> d \<Longrightarrow> a -c < b -d" for a b c d by simp
          show ?case 
            apply(subst  106[simplified \<FF>'_def], subst comps_union[simplified \<FF>'_def], subst card_Un_disjnt)
            using comps_inter_empt  144[of x'] 144[of y'] e_prop asm 2 103  154[OF x'_inV] 154[OF y'_inV]  \<V>_finite 
                  finite_subset[of "connected_component \<FF> _"] finite_subset[of "connected_component \<FF>' _"] 
              by (auto intro!: order.strict_trans2[OF _ 110]  strict_non_strict_mono 
                     simp add: add_increasing distrib_left  \<gamma>_def  disjnt_def  )
        qed
      qed
    qed
    thus ?thesis
    by(auto simp add: sym[OF state_state'] invarA_2_def state'_def)
  qed
  qed

  have "invar_gamma state \<Longrightarrow> thr2 \<ge> 0  \<Longrightarrow>invarA_1 thr2 state \<Longrightarrow> invarA_2 thr1 thr2 state \<Longrightarrow>
        thr2 \<le> 2 * current_\<gamma> state \<Longrightarrow> thr1 = 8*real N * current_\<gamma> state \<Longrightarrow>
        is_Opt (\<b> - b) f \<Longrightarrow> is_Opt (\<b> - b') f'" 
  proof-
    assume asm: "invar_gamma state" "thr2 \<ge> 0" "invarA_1 thr2 state" "invarA_2 thr1 thr2 state"
        "thr2 \<le> 2 * current_\<gamma> state" "thr1 = 8*real N * current_\<gamma> state"
        "is_Opt (\<b> - b) f"
    hence \<gamma>_geq_0: "\<gamma> \<ge> 0" unfolding invar_gamma_def \<gamma>_def by auto
    have d_oedge_inE:"d \<in> to_rdgs to_pair (conv_to_rdg state) (to_graph (Algo_state.\<FF>_imp state) - {{fst e, snd e}}) \<Longrightarrow>
                 oedge d \<in> \<E>" for d
      using assms(2) to_rdg_mono[of "to_graph (Algo_state.\<FF>_imp state) - {{fst e, snd e}}"
                                    "to_graph (Algo_state.\<FF>_imp state)"
                                    "to_pair" "(conv_to_rdg state)"]  
      by (auto simp add: aux_invar_def \<EE>_def  invar_aux2_def   \<FF>'_def \<FF>_def \<FF>_imp_def \<FF>_imp'_def )
      
    hence d_oedge_V:"d \<in> to_rdgs to_pair (conv_to_rdg state) (to_graph (Algo_state.\<FF>_imp state) - {{fst e, snd e}}) \<Longrightarrow>
              fst (oedge d) \<in> \<V>" for d 
      using fst_E_V by presburger
    have d_oedge_card:"d \<in> to_rdgs to_pair (conv_to_rdg state) (to_graph (Algo_state.\<FF>_imp state) - {{fst e, snd e}}) \<Longrightarrow>
         card (connected_component (to_graph (Algo_state.\<FF>_imp state)) (fst (oedge d))) \<le> N"for d 
      using assms(2) d_oedge_V[of d]  \<V>_finite 
      by (simp add: card_mono  aux_invar_def  invar_aux10_def \<EE>_def N_def )

    have V_non_empt: "\<V> \<noteq> {}"
      by (simp add: E_not_empty)

    have d_inF'_rcap:"d \<in> to_rdgs to_pair to_rdg' \<FF>' \<Longrightarrow> rcap f d > 6 * N * \<gamma>" for d
      apply(subst (asm)  concretization_of_F', simp)
      apply(rule disjE, simp)
      subgoal
        using infinite_u[of e] e_prop
              assms(2) unfolding aux_invar_def invar_aux1_def E'_def by auto
      apply(rule disjE, simp)
      subgoal 
          apply(insert e_prop) 
          apply(rule Orderings.xt1(1)[of _  "ereal (f _)"])
        using rcap.simps(2)[of f ] apply simp
        apply(subst less_ereal.simps(1))
        apply(rule order.strict_trans[of _ "(8 * real N * \<gamma>)"]) 
        using asm(1) V_non_empt \<V>_finite 
        by(auto intro: mult_less_le_imp_less simp add: invar_gamma_def \<gamma>_def N_def)
        subgoal
          apply(cases rule: oedge.cases[of d])        
          using d_oedge_card[of d] infinite_u[of "oedge d"]  asm(4)  asm(5) 
          apply (auto)[1]
          apply(rule order.strict_trans2[of _ "ereal (current_flow state (oedge d))"])
          apply(rule order.strict_trans1[of _ "ereal (8 * real (card \<V>) * current_\<gamma> state -
                 thr2 * real (card (connected_component (to_graph (Algo_state.\<FF>_imp state)) (fst (oedge d)))))"])      
          using d_oedge_card[of d] asm(5) asm(1) asm(2) 
                asm(4) to_rdg_mono[of "to_graph (Algo_state.\<FF>_imp state) - {{fst e, snd e}}"
                                      "to_graph (Algo_state.\<FF>_imp state)"
                                 to_pair "conv_to_rdg state", simplified]
       by(force intro: mult_mono simp add: aux_invar_def invarA_2_def f_def \<gamma>_def asm(6) N_def
                        invar_gamma_def \<FF>_imp_def to_rdg_def semiring_normalization_rules(18) \<FF>_def)+  
        done

    have revQ_subs:"List.set (to_redge_path to_rdg' (rev Q)) \<subseteq> to_rdgs to_pair to_rdg' \<FF>'"
      using  Q_inF'
      by (force intro!:  subset_trans[OF redge_of_Q_rev] simp add: to_rdgs_def)

    have Q_subs:"List.set (to_redge_path to_rdg' Q) \<subseteq> to_rdgs to_pair to_rdg' \<FF>'"
      apply(rule subset_trans[OF redge_of_Q])
      using  Q_inF'
      by(force intro!: subset_trans[OF redge_of_Q] simp add: to_rdgs_def)
    
    have to_rdg_rev_Q_non_empt:"List.set (to_redge_path to_rdg' (rev Q)) \<noteq> {}"
      using lengthQ 
      by (simp add: proper_path_some_redges)

    have Rcap_rev_Q:"ereal \<bar> b x'\<bar> < Rcap f (List.set (to_redge_path to_rdg' (rev Q)))"
        apply(rule Rcap_strictI)
        apply blast
      subgoal using to_rdg_rev_Q_non_empt by simp
      subgoal for d
        apply(rule order.strict_trans1[of _ "ereal (real (6 * N) * current_\<gamma> state)"])
         apply(rule order_trans[of _ "ereal (thr2 * real (card (connected_component 
                                         (to_graph (Algo_state.\<FF>_imp state)) x')))"])
      subgoal
          using asm(3) asm(5) asm(2) 157[of x'] x'_inV   \<gamma>_geq_0 N_def \<V>_finite 
          by(simp add: invarA_1_def b_def  \<FF>_imp_def \<FF>_def \<gamma>_def)
      subgoal
       apply(subst ereal_less_eq(3))
       apply(rule order_trans[of _ "2 * current_\<gamma> state * N"])
        using asm(5)  157[of x'] x'_inV   \<gamma>_geq_0 N_def \<V>_finite card_mono[of  \<V>]
        by(auto intro: mult_mono simp add: invarA_1_def b_def  \<FF>_def \<gamma>_def \<FF>_imp_def)
             
     using  d_inF'_rcap[of d] revQ_subs
     by(auto simp add: invarA_1_def b_def  \<FF>_def  \<gamma>_def)
    done

    have to_rdg_Q_non_empt: "List.set (to_redge_path to_rdg' Q) \<noteq> {}"
        using lengthQ
        by (simp add: proper_path_some_redges)

    have Rcap_Q:"ereal \<bar> b x'\<bar> < Rcap f (List.set (to_redge_path to_rdg' Q))"
        apply(rule Rcap_strictI)
        apply blast
      subgoal
        using to_rdg_Q_non_empt by simp
      subgoal for d
        apply(rule order.strict_trans1[of _ "ereal (real (6 * N) * current_\<gamma> state)"])
         apply(rule order_trans[of _ "ereal (thr2 * real (card (connected_component 
                                         (to_graph (Algo_state.\<FF>_imp state)) x')))"])
        using asm(3) asm(5) asm(2) 157[of x'] x'_inV   \<gamma>_geq_0 N_def \<V>_finite 
        apply(simp add:  invarA_1_def b_def  \<FF>_def \<gamma>_def)
      subgoal
       apply(subst ereal_less_eq(3))
       apply(rule order_trans[of _ "2 * current_\<gamma> state * N"])
       using asm(5)  157[of x'] x'_inV   \<gamma>_geq_0 N_def \<V>_finite card_mono[of  \<V>]
       by(auto intro: mult_mono simp add: invarA_1_def b_def  \<FF>_def \<gamma>_def \<FF>_imp_def)
       
     using  d_inF'_rcap[of d] Q_subs
     by(auto simp add: invarA_1_def b_def  \<FF>_def  \<gamma>_def)
    done

  have to_redg'_def': "to_rdg' = conv_to_rdg state'"
    unfolding state'_def by simp

  have walk_betwQ: "walk_betw \<FF>' x' Q y'"
    apply(rule from_directed_walk_to_undirected_walk[OF fit_together goodF' ])
    using qqq_prop invar_aux_pres_one_step[OF assms(2) assms(1), simplified sym[OF state_state']] x'_inVs x'_not_y'
    by(auto intro: get_path_axioms_unfolded(1) 
         simp add: aux_invar_def invar_aux19_def invar_aux18_def state'_def Q_def
                                                invar_aux14_def validF_def \<FF>'_def)
   
  have hd_rev_Q:"hd (rev Q) = y'"
    by(auto intro!: walk_between_nonempty_pathD(3)[of \<FF>' y' "rev Q" x'] 
                    walk_betwQ walk_symmetric)

  have last_rev_Q:"last (rev Q) = x'"
    by(auto intro!: walk_between_nonempty_pathD(4)[of \<FF>' y' "rev Q" x'] 
                    walk_betwQ walk_symmetric)

  have hd_Q:"hd Q = x'"
    by(auto intro!: walk_between_nonempty_pathD(3)[of \<FF>' x' Q y'] 
                    walk_betwQ)

  have last_Q:"last Q = y'"
    by(auto intro!: walk_between_nonempty_pathD(4)[of \<FF>' x' Q  y'] 
                    walk_betwQ)

  have C_Q_rev_Q:"\<CC> (to_redge_path to_rdg' Q) = - \<CC> (to_redge_path to_rdg' (rev Q))"
    using to_redge_path_costs[of to_rdg' Q, OF consist_to_rdg' lengthQ distinctQ]
          to_rdg_distinct[of to_rdg' Q, OF consist_to_rdg' distinctQ]
          to_rdg_distinct[of to_rdg' "rev Q", OF consist_to_rdg', 
                      simplified distinct_rev[of Q], OF distinctQ] distinct_sum2[of _ \<cc>] 
    by (simp add: \<CC>_def)

      hence a1:"ereal (- b x') \<le> Rcap f (List.set (to_redge_path to_rdg' (rev Q)))"
        using Rcap_rev_Q  ereal_less_le linorder_le_less_linear not_less_iff_gr_or_eq by fastforce
      have a2: "augpath f (to_redge_path to_rdg' (rev Q))"
        unfolding augpath_def apply rule
        subgoal unfolding to_redg'_def'
          using invar_aux_pres_one_step[of state, OF assms(2) assms(1), 
                           simplified sym[OF state_state']]  walk_betwQ lengthQ 
          by (fastforce intro!:  perpath_to_redgepath walk_symmetric simp add:  state'_def  aux_invar_def )
        using Rcap_rev_Q abs_ereal_pos[of "b x'"] 
              order.strict_trans1[of 0 "\<bar>ereal (b x')\<bar>"]
        by auto
      have a3: "List.set (to_redge_path to_rdg' (rev Q)) \<subseteq> \<EE>"
        using invar_aux_pres_one_step[of state, OF assms(2) assms(1), 
                           simplified sym[OF state_state']] \<FF>'_def 
        by (fastforce intro!:  subset_trans[OF revQ_subs] simp add: aux_invar_def invar_aux2_def state'_def )
      have a4: "distinct (to_redge_path to_rdg' (rev Q))"
        using consist_to_rdg' distinctQ
        by(auto intro: to_rdg_distinct)
      have a5:"fstv (hd (to_redge_path to_rdg' (rev Q))) = y'"
        using consist_to_rdg'  lengthQ hd_rev_Q 
        by (auto intro: to_rdg_hd)
      have a6: "sndv (last (to_redge_path to_rdg' (rev Q))) = x'"
        using consist_to_rdg'  lengthQ last_rev_Q 
        by (auto intro: to_rdg_last)

      hence b1:"ereal ( b x') \<le> Rcap f (List.set (to_redge_path to_rdg' Q))"
        using Rcap_Q
        by (simp add: ereal_less_le order_less_imp_le)
      have b2: "augpath f (to_redge_path to_rdg' Q)"
        unfolding augpath_def apply rule
        subgoal unfolding to_redg'_def'
          using invar_aux_pres_one_step[of state, OF assms(2) assms(1), 
                           simplified sym[OF state_state']]  walk_betwQ lengthQ 
          by (fastforce intro!: perpath_to_redgepath simp add: state'_def  aux_invar_def )
        using Rcap_Q abs_ereal_pos[of "b x'"] 
              order.strict_trans1[of 0 "\<bar>ereal (b x')\<bar>"]
        by auto
      have b3: "List.set (to_redge_path to_rdg'  Q) \<subseteq> \<EE>"
        using invar_aux_pres_one_step[of state, OF assms(2) assms(1), 
                           simplified sym[OF state_state']] \<FF>'_def
        by (fastforce intro!:  subset_trans[OF Q_subs] simp add: aux_invar_def invar_aux2_def state'_def )
      have b4: "distinct (to_redge_path to_rdg' Q)"
        using consist_to_rdg' distinctQ
        by(auto intro: to_rdg_distinct)
      have b5:"fstv (hd (to_redge_path to_rdg' Q)) = x'"
        using consist_to_rdg'  lengthQ hd_Q 
        by (auto intro: to_rdg_hd)
      have b6: "sndv (last (to_redge_path to_rdg' Q)) = y'"
        using consist_to_rdg'  lengthQ last_Q 
        by (auto intro: to_rdg_last)

      have is_s_t_path_rev_Q: "is_s_t_path f y' x' (to_redge_path to_rdg' (rev Q))"
        using a2 a3 a4 a5 a6 by (auto simp add: is_s_t_path_def)

      have is_s_t_path_Q: "is_s_t_path f x' y' (to_redge_path to_rdg' Q)"
        using b2 b3 b4 b5 b6 by (auto simp add: is_s_t_path_def)

    show "is_Opt (\<b> - b') f'" 
    unfolding f'_def
    apply(cases "0 < b x'", subst if_P, simp)
    defer
  proof(subst if_not_P, goal_cases)
    case 2
    note 1 = 2

      have min_path:"is_min_path f y' x' (to_redge_path to_rdg' (rev Q))"
        unfolding is_min_path_def
      proof(rule, goal_cases)
        case 1
        then show ?case unfolding is_s_t_path_def
        using a2 a3 a4 a5 a6 by auto
      next
        case 2
        then show ?case 
        proof(rule, rule)
          fix P' 
          assume P'_asm: "is_s_t_path f y' x' P'"
          show "\<CC> (to_redge_path to_rdg' (rev Q)) \<le> \<CC> P'"
          proof(rule ccontr)
            assume lesser_cost_asm:"\<not> \<CC> (to_redge_path to_rdg' (rev Q)) \<le> \<CC> P'"
            hence costs:"\<CC> (to_redge_path to_rdg' Q) + \<CC> P' < 0" 
              using C_Q_rev_Q by fastforce
            define Q' where "Q' = to_redge_path to_rdg' Q"
            define Qpp where "Qpp = map PP (to_redge_path to_rdg' Q)"
            define P'cc where "P'cc = map CC P'"
            have markers_removeQ: "to_redge_path to_rdg' Q = map to_redge Qpp"
              unfolding Qpp_def sym[OF Q'_def]
              by(induction Q') auto
            have markers_removeP: "P' = map to_redge P'cc"
              unfolding P'cc_def
               by(induction P') auto
            have markers_remove: "to_redge_path to_rdg' Q @ P' = map to_redge (Qpp @ P'cc)"
              unfolding Qpp_def sym[OF Q'_def]
              using markers_removeP 
              by (induction Q') auto
            have hpath: "hpath (Qpp @ P'cc)"
              using hpath_first_node[of P'cc] P'_asm markers_removeP hpath_last_node[of Qpp] 
                    is_s_t_path_Q markers_removeQ augpath_to_hpath_CC[of f] augpath_to_hpath_PP[of f]
              unfolding is_s_t_path_def Qpp_def P'cc_def 
              by (auto intro: h_path_append)
            have distinct:"distinct (Qpp @ P'cc)"
               using is_s_t_path_Q distinct_map[of ] P'_asm distinct_append
               unfolding Qpp_def P'cc_def is_s_t_path_def inj_on_def 
               by auto
             have setE:"List.set (to_redge_path to_rdg' Q @ P') \<subseteq> \<EE>"
               using P'_asm is_s_t_path_Q
               unfolding is_s_t_path_def by simp
             have fstvv_x':"fstvv (hd (Qpp @ P'cc)) = x'"
               using b5 is_s_t_path_Q unfolding Qpp_def is_s_t_path_def augpath_def prepath_def
               by (simp add: list.map_sel(1))
             have sndvv_x':"sndvv (last (Qpp @ P'cc)) = x'"
               using P'_asm  unfolding P'cc_def is_s_t_path_def augpath_def prepath_def
               by (simp add: last_map)
            have "\<exists>PP CCC.
                  Ball (List.set CCC) precycle \<and>
                  prepath PP \<and>
                  distinct PP \<and>
                  sum cc (List.set (Qpp@P'cc)) = \<CC> PP + foldr (\<lambda>D. (+) (\<CC> D)) CCC 0 \<and>
                  List.set ((to_redge_path to_rdg' Q)@P') = List.set PP \<union> \<Union> {List.set D |D. D \<in> List.set CCC} \<and> 
                  fstv (hd PP) = x' \<and> sndv (last PP) = x'"
              using markers_remove  hpath  distinct  setE fstvv_x' sndvv_x' 
              by (fastforce intro!: distinct_hpath_to_distinct_augpath_and_augcycles)
            then obtain P'' CCC where all_props:" Ball (List.set CCC) precycle"
                  "prepath P''"
                  "distinct P''"
                  "sum cc (List.set (Qpp@P'cc)) = \<CC> P'' + foldr (\<lambda>D. (+) (\<CC> D)) CCC 0"
                  "List.set ((to_redge_path to_rdg' Q)@P') = List.set P'' \<union> \<Union> {List.set D |D. D \<in> List.set CCC}"
                  "fstv (hd P'') = x'" "sndv (last P'') = x'" by auto
            have "sum cc (List.set (Qpp@P'cc)) = \<CC> (to_redge_path to_rdg' Q) + \<CC> P'"
              using distinct_CC_sum distinct_PP_sum Qpp_def P'cc_def
                    P'_asm is_s_t_path_Q unfolding is_s_t_path_def augpath_def prepath_def  \<CC>_def 
              by (subst set_append, subst sum.union_disjoint) auto
            then obtain C where C_prop:"(C = P'') \<or> C \<in> List.set CCC" "\<CC> C < 0"
              using costs all_props(4) fold_sum_neg_neg_element[of \<CC> CCC]
              by force
            have Rcap_pos:"Rcap f (List.set C) > 0"
              using is_s_t_path_Q  C_prop  P'_asm is_s_t_path_Q sym[OF all_props(5)]
              unfolding augcycle_def augpath_def precycle_def is_s_t_path_def prepath_def \<CC>_def
              by (intro Rcap_subset[of "List.set P'' \<union> \<Union> {List.set D |D. D \<in> List.set CCC}" "List.set C"], 
                auto intro: Rcap_union[of "List.set (to_redge_path to_rdg' Q)" "List.set P'"])
            have "augcycle f C"
              using C_prop all_props P'_asm is_s_t_path_Q Rcap_pos
              by (auto simp add: augcycle_def augpath_def precycle_def is_s_t_path_def)
            thus False using asm(7) min_cost_flow_no_augcycle by simp
          qed
        qed
      qed
        
      have "is_Opt (\<b> - b') f'"
        using x'_not_y'  asm(7)  a1  min_path  x'_not_y' a5 a6 1 
        by (auto intro!: path_aug_opt_pres[of y' x' "\<b> - b" f "- b x'" ] simp add: b'_def f'_def)

      thus ?case using 1 unfolding f'_def by simp
    next
      case 3
      note 2 = 3

      have min_path:"is_min_path f x' y' (to_redge_path to_rdg' Q)"
        unfolding is_min_path_def
      proof(rule, goal_cases)
        case 1
        then show ?case unfolding is_s_t_path_def
        using b2 b3 b4 b5 b6 by auto
      next
        case 2
        then show ?case 
        proof(rule, rule)
          fix P' 
          assume P'_asm: "is_s_t_path f x' y' P'"
          show "\<CC> (to_redge_path to_rdg' Q) \<le> \<CC> P'"
          proof(rule ccontr)
            assume lesser_cost_asm:"\<not> \<CC> (to_redge_path to_rdg' Q) \<le> \<CC> P'"
            hence costs:"\<CC> (to_redge_path to_rdg' (rev Q)) + \<CC> P' < 0" 
              using C_Q_rev_Q by fastforce
            define Q' where "Q' = to_redge_path to_rdg' (rev Q)"
            define Qpp where "Qpp = map PP (to_redge_path to_rdg' (rev Q))"
            define P'cc where "P'cc = map CC P'"
            have markers_removeQ: "to_redge_path to_rdg' (rev Q) = map to_redge Qpp"
              unfolding Qpp_def sym[OF Q'_def]
              by(induction Q') auto
            have markers_removeP: "P' = map to_redge P'cc"
              unfolding P'cc_def
               by(induction P') auto
            have markers_remove: "to_redge_path to_rdg' (rev Q) @ P' = map to_redge (Qpp @ P'cc)"
              unfolding Qpp_def sym[OF Q'_def]
              using markers_removeP 
              by (induction Q') auto
            have hpath: "hpath (Qpp @ P'cc)"
              using hpath_first_node[of P'cc] P'_asm markers_removeP hpath_last_node[of Qpp] a2 a6
                    is_s_t_path_Q markers_removeQ augpath_to_hpath_CC[of f] augpath_to_hpath_PP[of f]
              unfolding is_s_t_path_def Qpp_def P'cc_def 
              by (auto intro: h_path_append)
            have distinct:"distinct (Qpp @ P'cc)"
              using is_s_t_path_rev_Q distinct_map[of ] P'_asm distinct_append
              by(auto simp add: Qpp_def P'cc_def is_s_t_path_def inj_on_def  )
             have setE:"List.set (to_redge_path to_rdg' Q @ P') \<subseteq> \<EE>"
               using P'_asm is_s_t_path_Q by (simp add: is_s_t_path_def)
             have setE_rev:"List.set (to_redge_path to_rdg' (rev Q) @ P') \<subseteq> \<EE>"
               using P'_asm is_s_t_path_rev_Q by(simp add: is_s_t_path_def)
             have fstvv_x':"fstvv (hd (Qpp @ P'cc)) = y'"
               using a5 is_s_t_path_rev_Q              
               by (simp add: list.map_sel(1) Qpp_def is_s_t_path_def augpath_def prepath_def)
             have sndvv_x':"sndvv (last (Qpp @ P'cc)) = y'"
               using P'_asm
               by (simp add: last_map P'cc_def is_s_t_path_def augpath_def prepath_def)
            have "\<exists>PP CCC.
                  Ball (List.set CCC) precycle \<and>
                  prepath PP \<and>
                  distinct PP \<and>
                  sum cc (List.set (Qpp@P'cc)) = \<CC> PP + foldr (\<lambda>D. (+) (\<CC> D)) CCC 0 \<and>
                  List.set ((to_redge_path to_rdg' (rev Q))@P') = List.set PP \<union> \<Union> {List.set D |D. D \<in> List.set CCC} \<and> 
                  fstv (hd PP) = y' \<and> sndv (last PP) = y'"
              using markers_remove  hpath  distinct  setE_rev fstvv_x' sndvv_x' 
              by (fastforce intro!: distinct_hpath_to_distinct_augpath_and_augcycles)
            then obtain P'' CCC where all_props:" Ball (List.set CCC) precycle"
                  "prepath P''"
                  "distinct P''"
                  "sum cc (List.set (Qpp@P'cc)) = \<CC> P'' + foldr (\<lambda>D. (+) (\<CC> D)) CCC 0"
                  "List.set ((to_redge_path to_rdg' (rev Q))@P') = List.set P'' \<union> \<Union> {List.set D |D. D \<in> List.set CCC}"
                  "fstv (hd P'') = y'" "sndv (last P'') = y'" by auto
            have "sum cc (List.set (Qpp@P'cc)) = \<CC> (to_redge_path to_rdg' (rev Q)) + \<CC> P'"
              unfolding \<CC>_def 
              using distinct_CC_sum distinct_PP_sum Qpp_def P'cc_def
                    P'_asm is_s_t_path_rev_Q unfolding is_s_t_path_def augpath_def prepath_def
              by (subst set_append, subst sum.union_disjoint) auto
            then obtain C where C_prop:"(C = P'') \<or> C \<in> List.set CCC" "\<CC> C < 0"
              using costs all_props(4) fold_sum_neg_neg_element[of \<CC> CCC]
              by force
            have Rcap_pos:"Rcap f (List.set C) > 0"
              using is_s_t_path_rev_Q  C_prop  P'_asm is_s_t_path_Q sym[OF all_props(5)]
              unfolding augcycle_def augpath_def precycle_def is_s_t_path_def prepath_def \<CC>_def
              by (intro Rcap_subset[of "List.set P'' \<union> \<Union> {List.set D |D. D \<in> List.set CCC}" "List.set C"], 
                    auto intro: Rcap_union[of "List.set (to_redge_path to_rdg' (rev Q))" "List.set P'"])
            have "augcycle f C"
              using C_prop all_props P'_asm is_s_t_path_rev_Q Rcap_pos
              by (auto simp add:  augcycle_def augpath_def precycle_def is_s_t_path_def)
            thus False using asm(7) min_cost_flow_no_augcycle by simp
          qed
        qed
      qed
        
      have "is_Opt (\<b> - b') f'"
        using x'_not_y'  asm(7)  b1  min_path  x'_not_y' b5 b6 2
        by (auto intro!: path_aug_opt_pres[of x' y' "\<b> - b" f "b x'" ] simp add: b'_def f'_def )
      
      thus ?case
        using 2 by (simp add: f'_def)
   qed
qed

  thus "invar_gamma state \<Longrightarrow> thr2 \<ge> 0  \<Longrightarrow>invarA_1 thr2 state \<Longrightarrow> invarA_2 thr1 thr2 state \<Longrightarrow>
         thr2 \<le> 2 * current_\<gamma> state \<Longrightarrow> thr1 = 8*real N * current_\<gamma> state \<Longrightarrow>
         invar_isOptflow state \<Longrightarrow> invar_isOptflow (maintain_forest_upd state)"
    using sym[OF state_state']
    by(simp add: invar_isOptflow_def state'_def f_def b_def)
qed 

text \<open>The monotone properties\<close>

lemma mono_one_step_gamma:
  assumes "maintain_forest_call_cond state"
  shows "current_\<gamma> state = current_\<gamma> (maintain_forest_upd state)"
  by(auto elim: maintain_forest_call_condE[OF assms] 
         split: if_split prod.splits
         simp add: maintain_forest_upd_def Let_def)

lemma mono_one_step_actives:
  assumes "maintain_forest_call_cond state" "invar_aux17 state"
  shows "to_set (actives (maintain_forest_upd state)) \<subseteq> to_set (actives state)"
  using set_filter(1)[OF assms(2)[simplified invar_aux17_def]]
  by(auto elim: maintain_forest_call_condE[OF assms(1)] 
         split: if_split prod.splits simp add: maintain_forest_upd_def Let_def)

lemma mono_one_step:
  assumes "maintain_forest_call_cond state"
          "aux_invar state" 
  shows 
        "invar_gamma state \<Longrightarrow> \<Phi> (maintain_forest_upd state) \<le> \<Phi> state + 1" 

        "(to_rdgs to_pair (conv_to_rdg state) (to_graph (\<FF>_imp state))) \<subseteq> 
         (to_rdgs to_pair (conv_to_rdg (maintain_forest_upd state)) (to_graph (\<FF>_imp (maintain_forest_upd state))))"

        "card (comps \<V> (to_graph (\<FF>_imp (maintain_forest_upd state)))) +1 = card (comps \<V> (to_graph (\<FF>_imp state)))"

        "invar_gamma state \<Longrightarrow> \<Phi> (maintain_forest_upd state) \<le> \<Phi> state + (card (comps \<V> (to_graph (\<FF>_imp state)))) - 
                                                     (card (comps \<V> (to_graph (\<FF>_imp (maintain_forest_upd state)))))"

        "\<And> d. d \<in> (UNIV -  oedge ` (to_rdgs to_pair (conv_to_rdg (maintain_forest_upd state)) 
                                  (to_graph (\<FF>_imp(maintain_forest_upd state))) ))  \<Longrightarrow>
               current_flow (maintain_forest_upd state) d =  current_flow state d"
        "to_graph (\<FF>_imp (maintain_forest_upd state)) \<supset> to_graph (\<FF>_imp state)"
        "\<exists> e . e \<in> to_set (actives state) \<and> 8 * real N * current_\<gamma> state < current_flow state e 
               \<and> connected_component (to_graph (\<FF>_imp  state)) (fst e)
              \<subset> connected_component (to_graph (\<FF>_imp (maintain_forest_upd state))) (fst e)"
proof-
  define a\<FF> where "a\<FF> = Algo_state.\<FF> state"
  define f where "f = current_flow state"
  define b where "b = balance state"
  define r where "r = representative state"
  define E' where "E' = actives state"
  define to_rdg where "to_rdg = conv_to_rdg state"
  define \<gamma> where "\<gamma> = current_\<gamma> state"
  define cards where "cards = comp_card state"
  define \<FF>_imp where "\<FF>_imp = Algo_state.\<FF>_imp state"
  define e where "e = the ( get_from_set (\<lambda> e. f e > 8 * real N *\<gamma>) E')"
  define x where "x = fst e"
  define y where "y= snd e"
  define to_rdg' where "to_rdg' = (\<lambda> d. if d = make_pair e then F e
                                             else if prod.swap d = make_pair e then B e 
                                             else to_rdg d)"
  define xy where "xy = (if cards x \<le> cards y 
                                       then (x,y) else (y,x))"
  define xx where "xx = prod.fst xy"
  define yy where "yy = prod.snd xy"
  define a\<FF>' where  "a\<FF>' = insert {fst e, snd e} a\<FF>"
  define \<FF>_imp' where "\<FF>_imp' = insert_undirected_edge (fst e) (snd e) \<FF>_imp"
  define x' where "x' = r xx"
  define y' where  "y' = r yy"
  define Q where  "Q = get_path x' y' \<FF>_imp'"
  define f' where "f' = (if b x' > 0 
                                   then augment_edges f (b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges f (- b x') (to_redge_path to_rdg' (rev Q)))"
  define b' where "b' = (\<lambda> v. if v= x' then 0 
                                        else if v = y' then b y' + b x'
                                        else b v)"
  define E'' where "E'' = filter (\<lambda> d. {r (fst d), r (snd d)} \<noteq>  {x', y'}) E'"
  define r' where "r' = (\<lambda> v. if r v = x' \<or> r v = y' then y' else r v)"
  define cards' where "cards' = (\<lambda>  v. if r' v = y' then cards x + cards y else cards v)"
  define nb where "nb = not_blocked state"
  define nb' where "nb' = (\<lambda> d. if e = d then True
                                        else if {r (fst d) , r (snd d)} = {x', y'} then False
                                        else nb d)"
  define state' where "state' = state \<lparr>  \<FF> := a\<FF>', current_flow := f',
                                    balance := b',  representative := r',
                                    actives := E'', conv_to_rdg := to_rdg', comp_card := cards',
                                    \<FF>_imp:= \<FF>_imp', not_blocked := nb'\<rparr>"
  have state_state':"state' = maintain_forest_upd state"
    by(rule maintain_forest_upd_unfold[OF a\<FF>_def f_def b_def r_def E'_def to_rdg_def  \<gamma>_def cards_def \<FF>_imp_def e_def x_def y_def
                                to_rdg'_def xy_def xx_def yy_def a\<FF>'_def \<FF>_imp'_def x'_def y'_def Q_def f'_def
                                b'_def E''_def r'_def cards'_def nb_def nb'_def state'_def])

have set_invar_E': "set_invar E'"
    using E'_def assms aux_invar_def invar_aux17_def by blast

  have E'_substE:"to_set E' \<subseteq> \<E>"
    using assms by(simp add: E'_def invar_aux1_def aux_invar_def)

  have "\<exists> e. e \<in> to_set E' \<and> 8 * real N * \<gamma> < f e"
    unfolding E'_def \<gamma>_def f_def
    apply(rule maintain_forest_call_condE[OF assms(1)])
    using set_get(1-3)[OF set_invar_E', simplified E'_def] 
    by fastforce

  then obtain ee where ee_prop:" ee \<in> to_set E' \<and> 8 * real N * \<gamma> < f ee"
    by auto

  have e_prop: "e \<in> to_set E' \<and> f e > 8 * real N *\<gamma>"
    apply(rule maintain_forest_call_condE[OF assms(1)])
    using ee_prop E'_substE set_get(1-3)[OF set_invar_E'] 
    by (fastforce simp add: E'_def f_def e_def \<gamma>_def)

  have fste_V: "fst e \<in> \<V>" 
    using  aux_invarE[OF assms(2)] e_prop dVsI' make_pair[OF refl refl]
    by(auto simp add: invar_aux1_def  E'_def)

  have snde_V: "snd e \<in> \<V>" 
    apply(rule aux_invarE[OF assms(2)])
    using e_prop dVsI' make_pair[OF refl refl]
    by(auto simp add: invar_aux1_def  E'_def)

   define \<FF> where "\<FF> = to_graph \<FF>_imp" 
  define  \<FF>' where "\<FF>' = insert {fst e, snd e} \<FF>"
  have F_rewrite: "to_graph \<FF>_imp' = \<FF>'"
    using assms(2)
    by(auto simp add: \<FF>_imp'_def \<FF>'_def \<FF>_def  aux_invar_def invar_aux18_def invar_aux19_def \<FF>_imp_def)

    have cards_same_cond: "card (connected_component \<FF> x) \<le> card (connected_component \<FF> y) \<longleftrightarrow>
                          cards x \<le> cards y"
      using assms(2)
      by (simp add: cards_def \<FF>_def aux_invar_def invar_aux16_def \<FF>_imp_def fste_V snde_V x_def y_def)

  have "xx \<in> \<V>" 
    by (simp add: xx_def xy_def x_def y_def fste_V snde_V)

  hence x'_inV: "x' \<in> \<V>"
    using assms(2) by(simp add: x'_def aux_invar_def invar_aux9_def r_def)

  have "yy \<in> \<V>"
    by (simp add: yy_def xy_def x_def y_def fste_V snde_V)

  hence y'_inV: "y' \<in> \<V>"
    using assms(2) by(simp add: y'_def  aux_invar_def invar_aux9_def r_def)

  have 01:"reachable \<FF> xx x' \<or> xx = x'"
    using assms(2) by(simp add: aux_invar_def invar_aux8_def \<FF>_def x'_def r_def \<FF>_imp_def)

  have 02:"reachable \<FF> yy y' \<or> yy = y'"
    using assms(2) by(simp add: aux_invar_def invar_aux8_def \<FF>_def y'_def r_def \<FF>_imp_def)

  hence 1100:"connected_component \<FF> (fst e) \<noteq> connected_component \<FF> (snd e)"
    using e_prop assms(2) 
    by(simp add:invar_aux11_def aux_invar_def  E'_def \<FF>_def \<FF>_imp_def)

  have fst_snd_e_neq: "fst e \<noteq> snd e"
    using  1100 by auto

  hence x_not_y:"x \<noteq> y"
    by(simp add: x_def y_def)

  have 11:"to_rdgs to_pair (\<lambda>d. if d = make_pair e then F e else 
                   if prod.swap d = make_pair e then B e else to_rdg d) 
           {{fst e, snd e}} =
       {F e, B e}"
  using assms(2) to_rdg_def x_def x_not_y y_def 
  by (auto simp add: aux_invar_def  invar_aux6_def )

    have aa: "to_rdgs to_pair to_rdg' (insert {fst e, snd e} \<FF>) = 
          to_rdgs to_pair to_rdg' {{fst e, snd e}} \<union> to_rdgs to_pair to_rdg' (\<FF>-{{fst e, snd e}})" 
      unfolding to_rdgs_def by blast
    have bb: "to_rdgs to_pair to_rdg' (\<FF>-{{fst e, snd e}}) = 
            to_rdgs to_pair to_rdg (\<FF>-{{fst e, snd e}})"
      using to_rdgs_update_not_in[of to_rdg e] assms(2) 
      by(simp add: aux_invar_def invar_aux6_def to_rdg_def to_rdg'_def)
    have 110:"to_rdgs to_pair to_rdg' (insert {fst e, snd e} \<FF>) = 
          to_rdgs to_pair to_rdg'{{fst e, snd e}} \<union> to_rdgs to_pair to_rdg (\<FF> - {{fst e, snd e}})"  
      using 11 aa bb by simp
   have 111: "... = {F e, B e}
          \<union> to_rdgs to_pair to_rdg (\<FF> - {{fst e, snd e}}) "
    using 11 by(simp add: to_rdg'_def)
    have asm': "invar_aux11 state" using assms by(simp add:  aux_invar_def)
    have x'_not_y':"x' \<noteq> y'" 
      proof
        assume " x' = y'"
        hence "connected_component \<FF> x = connected_component \<FF> y"
          using 01 02 xx_def yy_def xy_def cards_same_cond
           connected_components_member_eq[of x' \<FF> xx]  in_connected_componentI[of \<FF> xx x'] 
           connected_components_member_eq[of y' \<FF> yy]  in_connected_componentI[of \<FF> yy y']
          by(cases "card (connected_component \<FF> x) \<le> card (connected_component \<FF> y)", auto)
        thus False
         using asm' e_prop unfolding invar_aux11_def x_def y_def  E'_def \<FF>_def \<FF>_imp_def
          by simp
     qed
     have comps_inter_empt:"connected_component \<FF> y' \<inter> connected_component \<FF> x' = {}" 
       using "01" "02" "1100" x_def xx_def xy_def  y_def yy_def  cards_same_cond
             connected_components_member_eq[of y' \<FF> yy, OF in_connected_componentI[of \<FF> yy y']]  
             connected_components_member_eq[of x' \<FF> xx, OF in_connected_componentI[of \<FF> xx x']]
       by(intro unequal_components_disjoint[where X=UNIV], 
          cases "card (connected_component \<FF> x) \<le> card (connected_component \<FF> y)", auto)
     have comp_y_y':"connected_component (insert {fst e, snd e} \<FF>) y' =
          connected_component (insert {fst e, snd e} \<FF>) y"
      apply(subst connected_components_member_eq[ of y' \<FF>' yy, simplified \<FF>'_def] )
      using "02" in_connected_componentI[of \<FF>' yy y'] reachable_subset[of \<FF> yy y' \<FF>'] \<FF>'_def 
      in_connected_componentI2[of yy y' \<FF>'] new_edge_disjoint_components[of x y \<FF>]  x_def xy_def y_def yy_def 
      by (fast, auto)
     have comps_union:"connected_component \<FF>' y' =
                      connected_component \<FF> y' \<union> connected_component \<FF> x'"
       unfolding \<FF>'_def
      apply(subst connected_components_member_eq[of x' \<FF> xx])
      subgoal 
        using "01" in_connected_componentI[of \<FF> xx x'] in_own_connected_component[of x' \<FF>]
        by auto
      apply(subst connected_components_member_eq[of y' \<FF> yy])
      subgoal 
        using "02" in_connected_componentI[of \<FF> yy y'] in_own_connected_component[of y' \<FF>]
        by auto
      apply(rule trans[of _ "connected_component (insert {fst e, snd e} \<FF>) y"])
      subgoal using comp_y_y' by simp 
      apply(rule trans, rule sym[OF insert_edge_endpoints_same_component[of "(insert {fst e, snd e} \<FF>)" _ x \<FF>]])
      using x_def y_def  xx_def xy_def yy_def  
      by(auto split: if_split simp add: insert_commute)

     have "fst e \<noteq> snd e"
      using 1100  by auto
        hence concretization_of_F': "to_rdgs to_pair to_rdg' \<FF>' =
                                { F e, B e} \<union> to_rdgs to_pair to_rdg (\<FF> - {{fst e, snd e}}) "
      using 111 110 bb aa by(simp add: \<FF>'_def)

    have consist_to_rdg':"consist to_rdg'" 
      using  invar_aux_pres_one_step[of state, OF assms(2) assms(1), simplified sym[OF state_state']] 
      by(simp add: state'_def aux_invar_def invar_aux6_def)

    have axioms_conds1: "x' \<in> Vs \<FF>'" 
      by(metis comps_union insert_edge_endpoints_same_component in_con_comp_insert in_connected_component_in_edges x'_not_y')
    have axioms_conds2: "Vs \<FF>' \<subseteq> \<V> "
      using assms(2) fste_V snde_V 
      by(simp add: aux_invar_def invar_aux15_def \<FF>'_def \<FF>_def Vs_def \<FF>_imp_def)
    have axioms_conds3: "graph_invar \<FF>'"
      using assms(2)  \<V>_finite axioms_conds2 finite_subset fst_snd_e_neq
      by (auto simp add: aux_invar_def invar_aux14_def \<FF>'_def \<FF>_def validF_def  \<FF>_imp_def)

    have goodF:"goodF \<FF>_imp" 
      by (simp add: Pair_graph_specs_from_aux_invar assms(2) local.\<FF>_imp_def)
    have adjmap_invF: "adjmap_inv \<FF>_imp"
      by (simp add: assms(2) from_aux_invar'(18) local.\<FF>_imp_def)
    have goodF':"goodF \<FF>_imp'"
      using  \<FF>_imp_def goodF
      by (auto intro: Pair_Graph_Specs_insert_undirected_edge_pres 
            simp add: \<FF>_imp'_def assms(2) from_aux_invar'(18) \<FF>_imp_def goodF)

    have fit_together: "fit_together \<FF>' \<FF>_imp'"
      using invar_aux_pres_one_step[OF assms(2) assms(1), simplified sym[OF state_state']]
            sym[OF F_rewrite]
      by(simp add: aux_invar_def invar_aux19_def invar_aux20_def invar_aux21_def state'_def
                   fit_together_def \<FF>_def \<FF>_imp_def \<FF>'_def \<FF>_imp'_def)

  obtain qqq where qqq_prop:"vwalk_bet (digraph_abs \<FF>_imp') x' qqq y'"
    using comps_union connected_components_member_sym[of x' \<FF>' y'] 
          axioms_conds1 axioms_conds2 axioms_conds3
           in_connected_componentE[of y' \<FF>' x'] in_connected_componentI2[of x' x' \<FF>]  x'_not_y' 
          from_reachable_to_dircted_walk[OF fit_together goodF', of x' y'] by auto

  have finiteF: "finite (to_graph \<FF>_imp')" 
    using F_rewrite axioms_conds3 graph_abs.finite_E graph_abs.intro by blast
  have x'_inVs:"x' \<in> Vs (to_graph \<FF>_imp')"
    using F_rewrite axioms_conds1 by blast
   have distinctQ: "distinct Q"
     using qqq_prop  invar_aux_pres_one_step[OF assms(2) assms(1), simplified sym[OF state_state']] 
           x'_inVs x'_not_y'
      by (auto intro: get_path_axioms_unfolded(2)[of \<FF>_imp' x' qqq y'] simp add: aux_invar_def invar_aux19_def invar_aux18_def state'_def Q_def )
     
    have oedge_of_Q:"oedge ` List.set (to_redge_path to_rdg' Q) = 
          oedge ` to_rdgs to_pair to_rdg' (List.set (edges_of_path Q))"
      using oedge_of_to_redgepath_subset[of Q to_rdg'] consist_to_rdg' distinctQ by simp

    have oedge_of_Q_rev: "oedge ` List.set (to_redge_path to_rdg' (rev Q)) = 
          oedge ` to_rdgs to_pair to_rdg' (List.set (edges_of_path Q))"
      using oedge_of_to_redgepath_subset[of Q to_rdg'] consist_to_rdg' distinctQ
            oedge_of_to_redge_path_rev[of Q to_rdg'] by simp
          
    have flow_change_in_Q:"f' d \<noteq> f d \<Longrightarrow> d \<in> oedge ` to_rdgs to_pair to_rdg' (List.set (edges_of_path Q))" for d
      unfolding f'_def
      using e_not_in_es_flow_not_change[of "(to_redge_path to_rdg' Q)" d f "b x'"]
            e_not_in_es_flow_not_change[of "(to_redge_path to_rdg' (rev Q))" d f "- b x'"]
            oedge_of_Q oedge_of_Q_rev
      by (smt (verit, del_insts) image_eqI)  

    have comps_representative:"connected_component \<FF> v = connected_component \<FF> (r v)" for v
      apply(rule aux_invarE[of state, OF assms(2), simplified invar_aux8_def] )
      using connected_components_member_eq[of "r v" \<FF> v, OF in_connected_componentI[of \<FF> v "r v"]]
            local.\<FF>_def r_def \<FF>_imp_def
      by force
      
    have 144:"connected_component \<FF> v \<subseteq> connected_component \<FF>' v" for v 
           by (simp add: \<FF>'_def  con_comp_subset subset_insertI)
    have 154:"v \<in> \<V> \<Longrightarrow> connected_component \<FF>' v \<subseteq> \<V>" for v
      using invar_aux_pres_one_step[OF assms(2) assms(1), simplified sym[OF state_state']]
            F_rewrite
      by(simp add: aux_invar_def invar_aux10_def  state'_def \<FF>'_def \<FF>_imp_def \<FF>_imp'_def)
    have 157:"v \<in> \<V> \<Longrightarrow> connected_component \<FF> v \<subseteq> \<V>" for v
      using "144" "154" by blast
    have 155: "card (connected_component \<FF> y') \<ge> card (connected_component \<FF> x')"
            using comps_representative cards_same_cond
            by(auto split: if_split simp add:  y'_def x'_def xx_def yy_def xy_def)

  show goal3:" invar_gamma state \<Longrightarrow> \<Phi> (maintain_forest_upd state) \<le> \<Phi> state + 1"
  proof-
    assume invar_gamma_asm: "invar_gamma state "
    have invar6_asm: "invar_aux11 state" using assms unfolding aux_invar_def by simp
    have 10:"\<Phi> state = 
          (\<Sum> v \<in>  \<V> - {x', y'}. \<lceil> \<bar> balance state v\<bar> / (current_\<gamma> state) - (1 - \<epsilon>)\<rceil>) +
          \<lceil> \<bar> balance state x'\<bar> / (current_\<gamma> state) - (1 - \<epsilon>)\<rceil> + 
          \<lceil> \<bar> balance state y'\<bar> / (current_\<gamma> state) - (1 - \<epsilon>)\<rceil>"
      using x'_inV y'_inV  x'_not_y' \<V>_finite 
      by (auto  intro: sum_except_two simp add: \<Phi>_def)

    have 11:"(\<Sum> v \<in>  \<V> - {x', y'}. \<lceil> \<bar> balance state v\<bar> / (current_\<gamma> state) - (1 - \<epsilon>)\<rceil>) = 
          (\<Sum> v \<in>  \<V> - {x', y'}. \<lceil> \<bar> balance state' v\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>)"
      by(simp add: state'_def b'_def b_def)

     have 12:"\<Phi> state' = 
          (\<Sum> v \<in>  \<V> - {x', y'}. \<lceil> \<bar> balance state' v\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>) +
          \<lceil> \<bar> balance state' x'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil> + 
          \<lceil> \<bar> balance state' y'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>"
      using x'_inV y'_inV  x'_not_y' \<V>_finite 
      by (auto intro: sum_except_two simp add: \<Phi>_def)

    have "\<lceil> \<bar> balance state' x'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil> + 
          \<lceil> \<bar> balance state' y'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil> = 
         \<lceil> 0 - (1 - \<epsilon>)\<rceil> + 
          \<lceil> \<bar> balance state' y'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>"
      by (simp add: state'_def b'_def)
    also have "... = \<lceil> \<bar> balance state' y'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>"
      using \<epsilon>_axiom by linarith
    also have "... = \<lceil> \<bar> b y' + b x'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>"
      using x'_not_y' by (simp add: state'_def b'_def)
    also have "...  \<le>  \<lceil> (\<bar> b y' \<bar> + \<bar> b x'\<bar>) / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>"
      using invar_gamma_asm unfolding invar_gamma_def state'_def 
      by (auto intro!: ceiling_mono divide_right_mono)
    also have "... = \<lceil> \<bar> b y' \<bar> / (current_\<gamma> state')  + (\<bar> b x'\<bar>/ (current_\<gamma> state')- (1 - \<epsilon>))\<rceil>"
      by argo
    also  have "... \<le> \<lceil> \<bar> b y' \<bar> / (current_\<gamma> state')\<rceil>
                      + \<lceil> \<bar> b x'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>"
      by(auto intro:  ceiling_add_le)
    also have "... \<le> \<lceil> \<bar> b y' \<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil> + 1
                      + \<lceil> \<bar> b x'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>"
      using \<epsilon>_axiom by linarith
    finally have ineq:"\<lceil> \<bar> balance state' x'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil> + 
          \<lceil> \<bar> balance state' y'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil> \<le>
           \<lceil> \<bar> balance state y' \<bar> / (current_\<gamma> state) - (1 - \<epsilon>)\<rceil> + 1
                      + \<lceil> \<bar> balance state x'\<bar> / (current_\<gamma> state) - (1 - \<epsilon>)\<rceil>"
      unfolding state'_def b_def by simp
    show "\<Phi> (maintain_forest_upd state) \<le> \<Phi> state + 1"
      using sym[OF state_state'] ineq by (auto simp add: 10 11 12)
  qed

   show goal4:"card (comps \<V> (to_graph (Algo_state.\<FF>_imp (maintain_forest_upd state)))) +1 = 
                                   card (comps \<V> (to_graph (Algo_state.\<FF>_imp state))) "
    proof-
      have invar6_asm:"invar_aux11 state"
        using assms(2) by (simp add: aux_invar_def invar_aux11_def)
      show "card (comps \<V> (to_graph (Algo_state.\<FF>_imp (maintain_forest_upd state)))) +1 = 
                   card (comps \<V> (to_graph (Algo_state.\<FF>_imp state)))"
        using  sym[OF state_state'] 1100 invar6_asm fste_V snde_V  \<V>_finite assms(2)  F_rewrite 
       by (auto intro: card_decrease_component_join[simplified]
             simp add: state'_def  \<FF>'_def \<FF>_def aux_invar_def invar_aux5_def \<FF>_imp_def \<FF>_imp'_def) 
    qed

    show "invar_gamma state \<Longrightarrow> \<Phi> (maintain_forest_upd state) \<le> \<Phi> state +
  (card (comps \<V> (to_graph (Algo_state.\<FF>_imp state)))) - 
                                            (card (comps \<V> (to_graph (Algo_state.\<FF>_imp (maintain_forest_upd state)))))"
    proof-
      assume invar6_asm: "invar_gamma state"   
      have invar6_asm':"invar_aux11 state"
        using assms(2) by (simp add:  aux_invar_def invar_aux11_def)   
      moreover have "connected_component (to_graph \<FF>_imp) (fst e) \<in> 
               (comps \<V> (to_graph (Algo_state.\<FF>_imp state)))"
        using fste_V by (simp add: comps_def \<FF>_imp_def )
      moreover have "connected_component (to_graph \<FF>_imp) (snd e) \<in> 
                (comps \<V> (to_graph (Algo_state.\<FF>_imp state)))"
        using snde_V by (simp add: comps_def \<FF>_imp_def)
      ultimately show " \<Phi> (maintain_forest_upd state) \<le> \<Phi> state + card (comps \<V> (to_graph (Algo_state.\<FF>_imp state))) - 
                                           card (comps \<V> (to_graph (Algo_state.\<FF>_imp (maintain_forest_upd state))))"       
      using goal4 goal3 invar6_asm
      by simp
  qed

    have Q_inF':"(List.set (edges_of_path Q)) \<subseteq>  \<FF>'"   
      using from_directed_walk_to_undirected_walk[OF fit_together goodF'
              axioms_conds3 get_path_axioms_unfolded(1)[of \<FF>_imp' x' qqq y' Q, simplified Q_def, OF qqq_prop]]
              invar_aux_pres_one_step[OF assms(2) assms(1), simplified sym[OF state_state']] qqq_prop 
              x'_inVs x'_not_y'
      by(fastforce intro!: path_edges_subset[of \<FF>' Q] 
                 simp add: aux_invar_def invar_aux19_def invar_aux18_def state'_def walk_betw_def Q_def)

  have same_flow:"\<And> d.  d \<in> (UNIV -  oedge ` (to_rdgs to_pair to_rdg' \<FF>' )) \<Longrightarrow> f' d =  f d"
  proof-
    fix d
    assume asm:"d \<in> (UNIV -  oedge ` (to_rdgs to_pair to_rdg' \<FF>' ))"
    hence d_not_F':"d \<notin>  oedge ` (to_rdgs to_pair to_rdg' \<FF>' )" by auto
    show "f' d = f d"
    proof(rule ccontr)
      assume " f' d \<noteq> f d"
      hence "d \<in> oedge ` to_rdgs to_pair to_rdg' (List.set (edges_of_path Q))"
        using flow_change_in_Q by simp
      thus False using d_not_F' Q_inF' by(fastforce simp add: to_rdgs_def)
    qed
  qed

  thus "\<And> d. d\<in>UNIV - oedge ` to_rdgs to_pair (conv_to_rdg (maintain_forest_upd state))
                                                   (to_graph (Algo_state.\<FF>_imp (maintain_forest_upd state))) \<Longrightarrow>
       current_flow (maintain_forest_upd state) d = current_flow state d"
    apply(subst sym[OF state_state'])+
    apply(subst (asm)sym[OF state_state'])+
    by(simp add: F_rewrite state'_def  f_def \<FF>'_def \<FF>_def)

  show "to_rdgs to_pair (conv_to_rdg state) (to_graph (Algo_state.\<FF>_imp state))
        \<subseteq> to_rdgs to_pair (conv_to_rdg (maintain_forest_upd state)) (to_graph (Algo_state.\<FF>_imp (maintain_forest_upd state)))"
    apply(subst sym[OF state_state']|subst state'_def)+
     apply simp
    apply(subst concretization_of_F'[simplified sym[OF F_rewrite]])
    using "1100" new_edge_disjoint_components[of "fst e" "snd e"]  local.\<FF>_def F_rewrite
    unfolding to_rdg_def \<FF>_def  to_rdgs_def \<FF>_imp_def 
    by (metis (no_types, lifting) Un_iff insert_absorb single_diff_remove subsetI)
  show "to_graph (Algo_state.\<FF>_imp state) \<subset> to_graph (Algo_state.\<FF>_imp (maintain_forest_upd state))"
    using  add_eq_self_zero goal4 less_one 
    maintain_forest_upd_Forest'_impl_unfold[OF \<FF>_imp_def f_def E'_def \<gamma>_def e_def \<FF>_imp'_def]
    order_less_irrefl psubsetI subset_insertI \<FF>'_def \<FF>_def F_rewrite \<FF>_imp_def by auto
  show "\<exists>e. e \<in> to_set (actives state) \<and>
        8 * real N * current_\<gamma> state < current_flow state e \<and>
        connected_component (to_graph (Algo_state.\<FF>_imp  state)) (fst e)
        \<subset> connected_component (to_graph (Algo_state.\<FF>_imp (maintain_forest_upd state))) (fst e)"
    using E'_def  \<gamma>_def e_prop f_def F_rewrite sym[OF state_state']  1100  
          connected_components_member_eq[of "snd e"  "to_graph (Algo_state.\<FF>_imp state)" "fst e"] 
          insert_edge_endpoints_same_component[OF reflexive, of "to_graph (Algo_state.\<FF>_imp state)" "fst e" "snd e"]
          in_connected_componentI2[OF refl, of "snd e" "to_graph (Algo_state.\<FF>_imp state)"] 
    by (intro  exI[of _ e]) (auto simp add: \<FF>_def \<FF>'_def state'_def \<FF>_imp_def \<FF>_imp'_def)
qed

lemma gamma_pres: 
  assumes "aux_invar state"
  shows "current_\<gamma> (maintain_forest state) = current_\<gamma> state"
  using assms
  apply(induction rule: maintain_forest_induct)
 subgoal
  using  assms termination_of_maintain_forest[OF _ refl]
  by(simp add: aux_invar_def)
  subgoal for state
    using  mono_one_step_gamma[of state]
           invar_aux_pres_one_step[of state] 
    by (auto intro: maintain_forest_cases[of state] 
          simp add: maintain_forest_simps)
  done

theorem maintain_forest_invar_gamma_pres:
  assumes "aux_invar state"
  shows "invar_gamma state \<Longrightarrow> invar_gamma (maintain_forest state)"
  using assms 
  apply(induction rule: maintain_forest_induct[of state])
  subgoal
  using  assms termination_of_maintain_forest[OF _ refl]
 by(simp add: aux_invar_def)
  subgoal for state
    using  invar_gamma_pres_one_step[of state]
           invar_aux_pres_one_step[of state] 
    by (auto intro: maintain_forest_cases[of state] 
          simp add: maintain_forest_simps)
  done

lemma invarA2_pres: 
  assumes 
   "aux_invar state"
   "0 \<le> thr2"
   "invarA_1 thr2 state"
   "invarA_2 thr1 thr2 state"
   "thr2 \<le> 2 * current_\<gamma> state"
   "thr1 \<le> 8 * real N * current_\<gamma> state"
shows
     "invarA_2 thr1 thr2 (maintain_forest state)"
using assms proof(induction rule: maintain_forest_induct[where state=state])
  case 1
  then show ?case 
  using  assms termination_of_maintain_forest[OF _ refl]
  by(simp add: aux_invar_def)
next
  case (2 state)
  note IH = this
  show ?case 
  proof(cases rule: maintain_forest_cases[of state])
    case 1
    then show ?thesis 
      using 2 
      by (auto simp add: maintain_forest_simps(2))
  next
    case 2
    then show ?thesis 
        using invar_aux_pres_one_step[of state]
              invars_pres_one_step(2)[of state thr2] 
              invars_pres_one_step(1)[of state thr2] 
              mono_one_step_gamma[of state] IH 2
        by (auto  elim:  aux_invarE 
                 intro: IH(2) 
              simp add: maintain_forest_simps(1))
  qed 
qed

theorem send_flow_entryF: 
  assumes "aux_invar state" 
          "maintain_forest_entry state"
          "invar_gamma state"
          "(\<gamma>::real) = current_\<gamma> state"
          "invarA_1 (2 * (\<gamma>::real)) state"
          "invarA_2 (8 * N * (\<gamma>::real))  (2 * (\<gamma>::real)) state"
  shows "send_flow_entryF (maintain_forest state)"
  unfolding send_flow_entryF_def
  proof(rule, goal_cases)
    case (1 e)
    hence e_in_E:"e \<in>  \<E>"
      using invar_aux3_def[of "maintain_forest state"]
            maintain_forest_invar_aux_pres[of state, OF _  assms(1)]
            termination_of_maintain_forest[OF _ refl]
            assms(1) by(auto simp add: aux_invar_def)     
    have gamma_same_after_maintain_forest: "current_\<gamma> (maintain_forest state) = \<gamma>"
      using assms gamma_pres[OF assms(1)] by simp
    have " invarA_2 (real (8 * N) * \<gamma>) (2 * \<gamma>) (local.maintain_forest state)"
      using assms
      by(intro invarA2_pres[OF assms(1), of "2*\<gamma> " "8*N*\<gamma> "], auto simp add: invar_gamma_def)
    hence aa:"(current_flow (local.maintain_forest state)) e > 
             8*N*\<gamma> - 2 * \<gamma> * card (connected_component (to_graph (\<FF>_imp (local.maintain_forest state))) (fst e))"
      using 1 by(auto simp add: invarA_2_def)
    have bb:"card (connected_component (to_graph (\<FF>_imp (local.maintain_forest state))) (fst e)) \<le> N"
      using \<V>_finite  invar_aux10_def[of "(local.maintain_forest state)"] e_in_E
            maintain_forest_invar_aux_pres[of state, OF _  assms(1)]
            termination_of_maintain_forest[OF _ refl] assms(1) make_pair[OF refl refl, of e]
      by(auto simp add: aux_invar_def  N_def image_def dVs_def) (smt (z3) card_mono insertI1)
    show ?case 
      using assms gamma_same_after_maintain_forest  bb aa assms 
      by (auto intro: order.strict_trans1[of _ 
                 " 8*N*\<gamma> - 2 * \<gamma> * card (_ (_ (_ (_ state))) (fst e))"] simp add: invar_gamma_def )
  qed

lemma Phi_increase: 
  assumes "aux_invar state"
          "invar_gamma state"
    shows "\<Phi> (maintain_forest state) \<le> \<Phi> state + (card (comps \<V> (to_graph (\<FF>_imp state)))) - 
                                    (card (comps \<V> (to_graph (\<FF>_imp(maintain_forest state)))))"
  using assms 
  apply(induction rule: maintain_forest_induct[of state])
  subgoal using assms termination_of_maintain_forest[OF _ refl]
      by(simp add: aux_invar_def)
  subgoal for state
      using maintain_forest_simps[of state] 
           invar_aux_pres_one_step[of state]
           invar_gamma_pres_one_step[of state]
           mono_one_step(4)[of state] 
      by (auto intro: maintain_forest_cases[of state])
    done  

theorem Phi_increase_below_N:
 assumes "aux_invar state"
         "invar_gamma state"
   shows "\<Phi> (maintain_forest state) \<le> \<Phi> state + N"
  using  Phi_increase[of state, OF assms] maintain_forest_invar_aux_pres[of state] assms
         number_comps_below_vertex_card[of "to_graph (\<FF>_imp state)" \<V>, OF _ \<V>_finite]
         termination_of_maintain_forest
  by(simp add:  aux_invar_def invar_aux5_def N_def)

lemma to_rdgs_mono: "A \<subseteq> B \<Longrightarrow> to_rdgs t1 t2 A \<subseteq> to_rdgs t1 t2 B" for A B
  unfolding to_rdgs_def by auto

lemma F_superset:
  assumes "aux_invar state"
  shows "to_rdgs to_pair (conv_to_rdg state) (to_graph (\<FF>_imp state)) \<subseteq> 
         to_rdgs to_pair (conv_to_rdg (maintain_forest state)) (to_graph (\<FF>_imp (maintain_forest state)))"
  using assms 
  apply(induction rule: maintain_forest_induct[of state])
  subgoal using assms termination_of_maintain_forest
    by(simp add: aux_invar_def)
  subgoal for state
     using mono_one_step(2)[of state] maintain_forest_simps[of state] 
           invar_aux_pres_one_step(1)[of state]
      by (fastforce intro: maintain_forest_cases[of state])    
    done 

lemma actives_superset:
  assumes "aux_invar state"
  shows "to_set (actives (maintain_forest state)) \<subseteq> to_set (actives state)"
  using assms 
  apply(induction rule: maintain_forest_induct[of state])
  subgoal using assms termination_of_maintain_forest
    by(simp add: aux_invar_def)
  subgoal for state
     using mono_one_step_actives[of state, OF _ invar_aux17_from_aux_invar] maintain_forest_simps[of state] 
           invar_aux_pres_one_step(1)[of state] 
      by (cases rule: maintain_forest_cases[of state], auto)    
    done 

lemma outside_F_no_flow_change:
  assumes "aux_invar state"
  shows   "\<And> d. d \<in> (UNIV -  oedge ` (to_rdgs to_pair (conv_to_rdg (maintain_forest state))
                                  (to_graph (\<FF>_imp(maintain_forest state))))) \<Longrightarrow>
               current_flow (maintain_forest state) d =  current_flow state d"
  using assms 
proof(induction rule: maintain_forest_induct[of state, 
        OF termination_of_maintain_forest[of _ "card (to_set  (actives state))"], simplified])
  case 1
  then show ?case 
    using assms unfolding aux_invar_def by simp
next
  case 2
  then show ?case 
    using assms unfolding aux_invar_def by simp
next
  case (3 state)
  note IH = this
  then show ?case 
  proof(cases rule: maintain_forest_cases[of state])
    case 1
    then show ?thesis 
    using maintain_forest_simps(2)maintain_forest_simps(2) IH by auto
  next
    case 2
    have dom:"maintain_forest_dom state"
    using IH termination_of_maintain_forest
    unfolding aux_invar_def by simp
    then show ?thesis 
    apply(subst maintain_forest_simps(1)[of state], simp add: dom, simp add: 2)+
    proof(goal_cases)
      case 1
      have cc:"to_rdgs to_pair (conv_to_rdg (maintain_forest_upd state)) (to_graph (\<FF>_imp (maintain_forest_upd state)))
            \<subseteq> to_rdgs to_pair (conv_to_rdg (local.maintain_forest (maintain_forest_upd state)))
           (to_graph (\<FF>_imp (local.maintain_forest (maintain_forest_upd state))))"
        using invar_aux_pres_one_step[of state] IH 2 
        by(auto intro!:  F_superset[of "maintain_forest_upd state"])
      have "current_flow (local.maintain_forest (maintain_forest_upd state)) d = current_flow (maintain_forest_upd state) d"
        using 2  cc IH(3) maintain_forest_simps(1)[of state, OF dom 2] 
              invar_aux_pres_one_step[of state, OF IH(4) 2] 
        by (auto intro: IH(2))
      moreover have "current_flow (maintain_forest_upd state) d = current_flow state d"
        using mono_one_step(5)[of state d, OF 2 IH(4)]  3(3) cc 
              2 dom maintain_forest_simps(1) by auto    
      ultimately show ?case by simp
    qed
  qed    
qed 
   
theorem maintain_forest_invar_integral_pres:
  assumes "aux_invar state" "invar_integral state"
  shows "invar_integral (maintain_forest state)"
  unfolding invar_integral_def
proof
  fix e
  assume e_asm:" e \<in> to_set (actives (maintain_forest state))"
  hence "e \<notin> oedge ` to_rdgs to_pair (conv_to_rdg (maintain_forest state)) (to_graph (\<FF>_imp (maintain_forest state)))"
    using maintain_forest_invar_aux_pres[of state, OF termination_of_maintain_forest]
          assms(1) 
    unfolding aux_invar_def invar_aux4_def 
    by auto
  hence "current_flow (maintain_forest state) e = current_flow state e"
    using outside_F_no_flow_change[of state e] assms(1) by simp
  moreover have "current_\<gamma> (local.maintain_forest state) = current_\<gamma>  state"
    using gamma_pres[OF assms(1)] by simp
  moreover obtain x where "current_flow state e = real x * current_\<gamma> state"
    using assms(2) actives_superset[OF assms(1)] e_asm unfolding invar_integral_def by auto
  ultimately show  "\<exists>x. current_flow (local.maintain_forest state) e = real x * current_\<gamma> (local.maintain_forest state)"
    by simp
qed

lemma "oedge e \<in> \<E> \<Longrightarrow> f (oedge e ) \<ge> thr \<Longrightarrow> rcap f e \<ge> thr"
  using infinite_u[of "oedge e"]   
  by(cases rule: oedge.cases[of e], auto)

lemma flow_optimatlity_pres: 
  assumes 
   "aux_invar (state)"
   "0 \<le> thr2"
   "invarA_1 thr2 state"
   "invar_isOptflow state"
   "thr2 \<le> 2 * current_\<gamma> state"
   "thr1 = 8 * real N * current_\<gamma> state"
   "invarA_2 thr1 thr2 state"
   "invar_gamma state"
 shows "invar_isOptflow (maintain_forest state)"
  using assms 
proof(induction rule: maintain_forest_induct[where state=state])
  case 1
  then show ?case 
  using  assms termination_of_maintain_forest
  by(simp add: aux_invar_def)
next
  case (2 state)
  note IH = this
  show ?case 
  proof(cases rule: maintain_forest_cases[of state])
    case 1
    then show ?thesis 
      using 2 by (auto simp add: maintain_forest_simps(2))
  next
    case 2
    show ?thesis 
      using maintain_forest_simps(1) invar_aux_pres_one_step[of state]
            invars_pres_one_step(1)[of state thr2] invars_pres_one_step(3)[of state]
            mono_one_step_gamma[of state] invars_pres_one_step(2)[of state thr2 thr1] 
            invar_gamma_pres_one_step[of state ] IH 2 
      by(auto intro!: IH(2) 
               intro: invars_pres_one_step(3)[of state thr2 thr1, OF 2 IH(3) _ IH(4)])
  qed 
qed

lemma forest_increase: 
  assumes "maintain_forest_dom state" "aux_invar state"
  shows   "to_graph (\<FF>_imp (maintain_forest state)) \<supseteq> to_graph (\<FF>_imp state)"
  using assms(2) 
  apply(induction rule: maintain_forest_induct[OF assms(1)])
  subgoal for state
    apply(cases rule: maintain_forest_cases[of state])
    using maintain_forest_simps(2) maintain_forest_simps(1)  mono_one_step(6)[of state] invar_aux_pres_one_step[of state]
    by auto
  done

lemma card_decrease: 
  assumes "maintain_forest_dom state" "aux_invar state"
  shows   "card (comps \<V> (to_graph (\<FF>_imp(maintain_forest state)))) \<le> card (comps \<V> (to_graph (\<FF>_imp state)))"
  using assms(2) 
  apply(induction rule: maintain_forest_induct[OF assms(1)])
  subgoal for state
    apply(cases rule: maintain_forest_cases[of state])
    using maintain_forest_simps(2) maintain_forest_simps(1)  mono_one_step(3)[of state] invar_aux_pres_one_step[of state]
    by auto
  done

lemma card_strict_decrease: 
  assumes "maintain_forest_dom state" "aux_invar state"
          "maintain_forest_call_cond state"
  shows   "card (comps \<V>  (to_graph (\<FF>_imp (maintain_forest state)))) < card (comps \<V> (to_graph (\<FF>_imp state)))"
  apply(subst maintain_forest_simps(1)[OF assms(1) assms(3)])
  using mono_one_step(3)[of state, OF assms(3) assms(2)] assms(2,3)
        card_decrease[of "maintain_forest_upd state",
                         OF termination_of_maintain_forest] invar_aux_pres_one_step[of state]
  by(simp add: aux_invar_def)

lemma component_strict_increase: 
  assumes "maintain_forest_dom state" "aux_invar state"
          "maintain_forest_call_cond state"
          "e \<in> to_set (actives state)"
          "current_flow state e > 8 * real N * current_\<gamma> state"
        shows   "connected_component (to_graph (\<FF>_imp (maintain_forest state))) (fst e) = 
                 connected_component (to_graph (\<FF>_imp (maintain_forest state))) (snd e)"
  using assms(2-)
proof(induction rule: maintain_forest_induct[OF assms(1)])
  case (1 state)
  note IH = this
  have maintain_forest_dom_upd:"maintain_forest_dom (maintain_forest_upd state)"
    using  invar_aux_pres_one_step[OF IH(3) IH(4)]
            termination_of_maintain_forest[OF _ refl, of "maintain_forest_upd state"] aux_invar_def by auto
  have e_in_E:"e \<in> \<E>" 
    using  IH(5) aux_invarE[OF IH(3)] invar_aux1E by auto
  show ?case
  proof(subst maintain_forest_simps(1)[OF IH(1) IH(4)], subst maintain_forest_simps(1)[OF IH(1) IH(4)], goal_cases)
    case 1
    then show ?case 
     proof(cases "\<not> e \<in> to_set (actives (maintain_forest_upd state))")
       case True
       hence "connected_component (to_graph (\<FF>_imp  (maintain_forest_upd state))) (fst e) =
              connected_component (to_graph (\<FF>_imp (maintain_forest_upd state))) (snd e)"
         using  IH(5)  invar_aux_pres_one_step[OF IH(3) IH(4)] e_in_E
         by(simp add: aux_invar_def  invar_aux13_def)
       then show ?thesis       
      using  invar_aux_pres_one_step[OF IH(3) IH(4)]
             maintain_forest_dom_upd  same_component_set_mono[OF forest_increase[of "maintain_forest_upd state"]] 
      by blast
  next
    case False
    hence e_active_upd:"e \<in> to_set (actives (maintain_forest_upd state))" by simp
    have same_flow:"current_flow (maintain_forest_upd state) e = current_flow state e"
      using  invar_aux_pres_one_step[OF IH(3) IH(4)] e_active_upd 
      by (auto intro: mono_one_step(5)[OF IH(4) IH(3), of e] simp add: aux_invar_def invar_aux4_def )
    have same_gamma: "current_\<gamma> (maintain_forest_upd state) = current_\<gamma> state"
      using IH(4) mono_one_step_gamma by force
    show ?thesis
      using  invar_aux_pres_one_step[OF IH(3) IH(4)] IH(6) same_flow same_gamma e_active_upd         
             set_get(1)[OF invar_aux17_from_aux_invar[simplified invar_aux17_def], of "maintain_forest_upd state" 
                   "(\<lambda>e. 8 * real N * current_\<gamma> state < current_flow (maintain_forest_upd state) e)"]   
      by (intro IH(2)[OF IH(4)])
         (fastforce intro!: bexI[of _ e] maintain_forest_call_condI[OF refl refl refl refl refl refl])+
    qed
  qed
qed

lemma same_number_comps_abort:
  assumes "aux_invar state" "maintain_forest_dom state"
          "card (comps \<V> (to_graph (\<FF>_imp (maintain_forest state)))) = card (comps \<V> (to_graph (\<FF>_imp state)))"
    shows "maintain_forest_ret_cond state"
  using assms apply(cases rule: maintain_forest_cases[of state], simp)
  using card_strict_decrease[of state] assms by simp
end
end