section \<open>Formalisation of Forest Maintenance\<close>

theory Maintain_Forest
  imports Intermediate_Summary
begin
subsection \<open>Setup\<close>

locale maintain_forest_spec = algo_spec where fst="fst::'edge_type \<Rightarrow> 'a" 
and get_from_set = "get_from_set::('edge_type \<Rightarrow> bool) \<Rightarrow> 'd \<Rightarrow> 'edge_type option"
and empty_forest = "empty_forest :: 'c"
and \<E>_impl = "\<E>_impl :: 'd"
for fst  get_from_set empty_forest \<E>_impl+
fixes get_path::"'a \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'a list" 
begin
definition "maintain_forest_get_path_cond u v E p q =
      (vwalk_bet (digraph_abs  E) u q v \<and> 
       p = get_path u v E \<and> u \<in> Vs (to_graph E) \<and>
       good_graph_invar E \<and> u \<noteq> v)"

lemma maintain_forest_get_path_condI:
"vwalk_bet (digraph_abs E) u q v \<Longrightarrow>  p = get_path u v E \<Longrightarrow> u \<in> Vs (to_graph E) \<Longrightarrow>
                        good_graph_invar E \<Longrightarrow> u \<noteq> v \<Longrightarrow>
      maintain_forest_get_path_cond u v E p q"
  by(auto simp add: maintain_forest_get_path_cond_def)

lemma maintain_forest_get_path_condE:
"maintain_forest_get_path_cond u v E p q \<Longrightarrow> 
(vwalk_bet (digraph_abs E) u q v \<Longrightarrow>  p = get_path u v E \<Longrightarrow> u \<in> Vs (to_graph E) \<Longrightarrow>
  good_graph_invar E \<Longrightarrow> u \<noteq> v \<Longrightarrow>
    P) \<Longrightarrow> P"
  by(auto simp add: maintain_forest_get_path_cond_def)

lemma maintain_forest_get_path_cond_unfold_meta:
  assumes "maintain_forest_get_path_cond u v E p q"
  shows "vwalk_bet (digraph_abs E) u q v"  "p = get_path u v E" 
        "u \<in> Vs (to_graph E)"
        "good_graph_invar E" 
        "u \<noteq> v"
  using maintain_forest_get_path_condE[OF assms(1)] by auto 

function (domintros) maintain_forest::"('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state 
\<Rightarrow>('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state" where
"maintain_forest state = (let \<FF> = \<FF> state;
                    f = current_flow state;
                    b = balance state;
                    r_card = rep_comp_card state;
                    E' = actives state;
                    to_rdg = conv_to_rdg state;
                    \<gamma> = current_\<gamma> state
                in (
case get_from_set  (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E'  of (Some e) \<Rightarrow>
                            (let  x = fst e; y = snd e;
                             to_rdg' = add_direction to_rdg x y e;
                             cardx = abstract_comp_map r_card x;
                             cardy = abstract_comp_map r_card y;
                             (x, y) = (if cardx \<le> cardy 
                                       then (x,y) else (y,x));
                              \<FF>' =insert_undirected_edge (fst e) (snd e) \<FF>;
                             x' = abstract_rep_map r_card x; 
                             y' = abstract_rep_map r_card y;
                             Q = get_path x' y' \<FF>';
                             f' = (if abstract_bal_map b x' > 0 
                                   then augment_edges_impl f (abstract_bal_map b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges_impl f (- abstract_bal_map b x') (to_redge_path to_rdg' (itrev Q)));
                             b' = move_balance b x' y';
                            E'' = filter (\<lambda> d. {abstract_rep_map r_card (fst d) ,
                                                abstract_rep_map r_card (snd d)}
                                                 \<noteq> {x', y'} ) E';
                            r_card' = rep_comp_upd_all 
                                (\<lambda> u urc. if prod.fst (urc) = x' \<or> prod.fst (urc) = y'
                                    then (y', cardx + cardy) else urc) r_card;
                            nb = not_blocked state;
                            nb' = not_blocked_upd_all (\<lambda> d b. 
                                   if d = e then True
                                   else if {abstract_rep_map r_card (fst d) ,
                                            abstract_rep_map r_card (snd d)} = {x', y'} 
                                   then False
                                   else b) nb;
                            state' = state \<lparr>  \<FF> := \<FF>', current_flow := f',
                                    balance := b', 
                                    actives := E'', conv_to_rdg := to_rdg',
                                    rep_comp_card:= r_card',
                                    not_blocked := nb'\<rparr>
                            in maintain_forest state')
                            | None \<Rightarrow> state))"
  by pat_completeness auto

partial_function (tailrec) maintain_forest_impl::"('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state 
\<Rightarrow>('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state" where
"maintain_forest_impl state = (let \<FF> = \<FF> state;
                    f = current_flow state;
                    b = balance state;
                    r_card = rep_comp_card state;
                    E' = actives state;
                    to_rdg = conv_to_rdg state;
                    \<gamma> = current_\<gamma> state
                in (
case get_from_set  (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E'  of (Some e) \<Rightarrow>
                            (let  x = fst e; y = snd e;
                             to_rdg' = add_direction to_rdg x y e;
                             cardx = abstract_comp_map r_card x;
                             cardy = abstract_comp_map r_card y;
                             (x, y) = (if cardx \<le> cardy 
                                       then (x,y) else (y,x));
                              \<FF>' =insert_undirected_edge (fst e) (snd e) \<FF>;
                             x' = abstract_rep_map r_card x; 
                             y' = abstract_rep_map r_card y;
                             Q = get_path x' y' \<FF>';
                             f' = (if abstract_bal_map b x' > 0 
                                   then augment_edges_impl f (abstract_bal_map b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges_impl f (- abstract_bal_map b x') (to_redge_path to_rdg' (itrev Q)));
                             b' = move_balance b x' y';
                            E'' = filter (\<lambda> d. {abstract_rep_map r_card (fst d) ,
                                                abstract_rep_map r_card (snd d)}
                                                 \<noteq> {x', y'} ) E';
                            r_card' = rep_comp_upd_all 
                                (\<lambda> u urc. if prod.fst (urc) = x' \<or> prod.fst (urc) = y'
                                    then (y', cardx + cardy) else urc) r_card;
                            nb = not_blocked state;
                            nb' = not_blocked_upd_all (\<lambda> d b. 
                                   if d = e then True
                                   else if {abstract_rep_map r_card (fst d),
                                    abstract_rep_map r_card (snd d)} = {x', y'} 
                                   then False
                                   else b) nb;
                            state' = state \<lparr>  \<FF> := \<FF>', current_flow := f',
                                    balance := b', 
                                    actives := E'', conv_to_rdg := to_rdg',
                                    rep_comp_card:= r_card',
                                    not_blocked := nb'\<rparr>
                            in maintain_forest_impl state')
                            | None \<Rightarrow> state))"

lemmas [code] = maintain_forest_impl.simps

lemma maintain_forest_dom_impl_same:
"maintain_forest_dom state \<Longrightarrow> maintain_forest_impl state = maintain_forest state"
proof(induction state rule: maintain_forest.pinduct)
  case (1 state)
  show ?case 
    apply(subst maintain_forest_impl.simps)
    apply(subst maintain_forest.psimps[OF 1(1)])
    by(auto simp add: Let_def option.split 
              intro!: 1(2)[OF refl refl refl refl refl refl refl _ refl
                          refl refl refl refl refl _ refl refl refl 
                          refl refl refl refl refl refl refl])
qed

end

locale maintain_forest = 
maintain_forest_spec where fst ="fst::'edge_type \<Rightarrow> 'a" +
algo where fst = fst  for fst +
assumes get_path_axioms:
        "\<And> u v E p q. maintain_forest_get_path_cond u v E p q\<Longrightarrow>vwalk_bet (digraph_abs  E) u p v"
        "\<And> u v E p q. maintain_forest_get_path_cond u v E p q \<Longrightarrow> distinct p"
begin

lemmas get_path_axioms_unfolded=get_path_axioms[OF maintain_forest_get_path_condI]

definition "maintain_forest_ret_cond state = (let \<FF> = \<FF> state;
                    f = current_flow state;
                    b = balance state;
                    r_card = rep_comp_card state;
                    E' = actives state;
                    to_rdg = conv_to_rdg state;
                    \<gamma> = current_\<gamma> state
                in (
            case get_from_set  (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E' 
                   of (Some e) \<Rightarrow> False
                    | None \<Rightarrow> True ))"

lemma maintain_forest_ret_condE: 
"maintain_forest_ret_cond state \<Longrightarrow> 
(\<And> f b r_card E' to_rdg \<gamma> cards.
   \<lbrakk>f = current_flow state;  r_card = rep_comp_card state;
    E' = actives state;  \<gamma> = current_\<gamma> state;
    get_from_set  (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E' = None \<rbrakk>\<Longrightarrow>P)
                \<Longrightarrow> P"
  by(fastforce simp add: maintain_forest_ret_cond_def Let_def)

lemma maintain_forest_ret_condI: 
"\<lbrakk> f = current_flow state; r_card = rep_comp_card state;  E' = actives state;
   \<gamma> = current_\<gamma> state; get_from_set  (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E' = None\<rbrakk>
          \<Longrightarrow> maintain_forest_ret_cond state"
  by(fastforce simp add: maintain_forest_ret_cond_def Let_def)

definition "maintain_forest_call_cond state = (let \<FF> = \<FF> state;
                    f = current_flow state;
                    b = balance state;
                    r_card = rep_comp_card state;
                    E' = actives state;
                    to_rdg = conv_to_rdg state;
                    \<gamma> = current_\<gamma> state
                in (
            case get_from_set  (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E' 
                   of (Some e) \<Rightarrow> True
                    | None \<Rightarrow> False))"

lemma maintain_forest_call_condE: 
"maintain_forest_call_cond state \<Longrightarrow> 
(\<And> f b r_card E' to_rdg \<gamma> cards a.
   \<lbrakk>f = current_flow state;  r_card = rep_comp_card state;
    E' = actives state;  \<gamma> = current_\<gamma> state;
    get_from_set  (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E' = Some a \<rbrakk>\<Longrightarrow>P)
                \<Longrightarrow> P"
  by(fastforce simp add: maintain_forest_call_cond_def Let_def)

lemma maintain_forest_call_condI: 
"\<lbrakk> f = current_flow state; r_card = rep_comp_card state;  E' = actives state;
   \<gamma> = current_\<gamma> state; get_from_set  (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E' = Some a\<rbrakk>
          \<Longrightarrow> maintain_forest_call_cond state"
  by(fastforce simp add: maintain_forest_call_cond_def Let_def)
 
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
                    r_card = rep_comp_card state;
                    E' = actives state;
                    to_rdg = conv_to_rdg state;
                    \<gamma> = current_\<gamma> state;
                    e = the (get_from_set  (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E');
                    x = fst e; y = snd e;
                    to_rdg' = add_direction to_rdg x y e;
                    cardx = abstract_comp_map r_card x;
                    cardy = abstract_comp_map r_card y;
                    (x, y) = (if cardx \<le> cardy then (x,y) else (y,x));
                    \<FF>' =insert_undirected_edge (fst e) (snd e) \<FF>;
                    x' = abstract_rep_map r_card x; 
                    y' = abstract_rep_map r_card y;
                    Q = get_path x' y' \<FF>';
                    f' = (if abstract_bal_map b x' > 0 
                          then augment_edges_impl f (abstract_bal_map b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges_impl f (- abstract_bal_map b x') (to_redge_path to_rdg' (itrev Q)));
                             b' = move_balance b x' y';
                            E'' = filter (\<lambda> d. {abstract_rep_map r_card (fst d) ,
                                                abstract_rep_map r_card (snd d)}
                                                 \<noteq> {x', y'} ) E';
                            r_card' = rep_comp_upd_all 
                                (\<lambda> u urc. if prod.fst (urc) = x' \<or> prod.fst (urc) = y'
                                    then (y', cardx + cardy) else urc) r_card;
                            nb = not_blocked state;
                            nb' = not_blocked_upd_all (\<lambda> d b. 
                                   if d = e then True
                                   else if 
                                 {abstract_rep_map r_card (fst d),
                                  abstract_rep_map r_card (snd d)}
                                 = {x', y'} 
                                   then False
                                   else b) nb;
                            state' = state \<lparr>  \<FF> := \<FF>', current_flow := f',
                                    balance := b', 
                                    actives := E'', conv_to_rdg := to_rdg',
                                    rep_comp_card:= r_card',
                                    not_blocked := nb'\<rparr>
                            in  state')"

lemma maintain_forest_simps:
  "maintain_forest_dom state \<Longrightarrow>maintain_forest_call_cond state \<Longrightarrow> maintain_forest state = maintain_forest (maintain_forest_upd state)"
  "maintain_forest_ret_cond state \<Longrightarrow> maintain_forest state =  state"
proof(goal_cases)
  case 1
  note assms = this
  show ?case 
    apply(subst maintain_forest.psimps[OF assms(1)])
    apply(subst maintain_forest_upd_def Let_def case_prod_beta)+
    apply(subst option_some_simp(1))
    by (auto split: option.split if_split 
             intro: maintain_forest_call_condE[OF 1(2)])
next
  case 2
  show ?case
    apply(subst maintain_forest.psimps)
    subgoal
      apply(rule maintain_forest.domintros)
      using 2 by(auto simp add:maintain_forest_ret_cond_def Let_def)
    using 2 by(auto simp add:maintain_forest_ret_cond_def Let_def split: option.split)
qed

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
  show ?case
    apply(rule assms(2)[OF 2(1)])
    apply(rule 2(2)[OF refl refl refl refl refl refl refl option.collapse[symmetric] 
                       refl refl refl refl refl refl prod.collapse
                       refl refl refl refl refl refl refl refl refl refl, rotated])
    apply(rule Algo_state.equality)
    by (auto  elim!: maintain_forest_call_condE
            intro!: cong[OF cong, OF refl, of _ _ _ _ rep_comp_upd_all] 
                    ext Algo_state.equality
          simp add: maintain_forest_upd_def Let_def)
 qed

text \<open>The basic invariants are interdependent\<close>

subsection \<open>Auxiliary Invariant for One Step\<close>

lemma invar_aux_pres_one_step:
  assumes "aux_invar state"
          "maintain_forest_call_cond state"
          "implementation_invar state"
  shows   "aux_invar (maintain_forest_upd state)"
proof-
  have all_invars: "invar_aux1 state" "invar_aux2 state" "invar_aux3 state" "invar_aux4 state"
                   "invar_aux6 state" "invar_aux8 state" "invar_aux7 state" "invar_aux9 state "
                   "invar_aux5 state" "invar_aux10 state" "invar_aux11 state" "invar_aux12 state"
                   "invar_aux13 state" "invar_aux16 state" "invar_aux17 state" "invar_aux18 state"
                    "invar_aux20 state" "invar_aux14 state"
                   "invar_aux22 state"
    using assms by(auto simp add: aux_invar_def)

  define  \<FF> where  "\<FF> = Algo_state.\<FF> state"
  define f where "f = current_flow state"
  define b where "b = balance state"
  define r_card where "r_card = rep_comp_card state"
  define E' where "E' = actives state"
  define to_rdg where "to_rdg = conv_to_rdg state"
  define \<gamma> where "\<gamma> = current_\<gamma> state"
  define e where "e = the( get_from_set 
                            (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E')"
  define x where "x = fst e"
  define y where "y = snd e"
  define to_rdg' where "to_rdg' = add_direction to_rdg x y e"
  define cardx where "cardx = abstract_comp_map r_card x"
  define cardy where "cardy = abstract_comp_map r_card y"
  define xy where " xy = (if cardx \<le> cardy then (x,y) else (y,x))"
  define xx where "xx = prod.fst xy"
  define yy where "yy = prod.snd xy"
  define \<FF>' where "\<FF>' =insert_undirected_edge (fst e) (snd e) \<FF>"
  define x' where "x' = abstract_rep_map r_card xx" 
  define y' where "y' = abstract_rep_map r_card yy"
  define Q where "Q = get_path x' y' \<FF>'"
  define f' where  "f' = (if abstract_bal_map b x' > 0 
                                   then augment_edges_impl f (abstract_bal_map b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges_impl f (- abstract_bal_map b x') (to_redge_path to_rdg' (itrev Q)))"
  define b' where "b' = move_balance b x' y'"
  define E'' where "E'' = filter (\<lambda> d. 
{abstract_rep_map r_card (fst d) , abstract_rep_map r_card (snd d) } \<noteq> {x', y'} ) E'"
  define r_card' where "r_card' = rep_comp_upd_all 
                                (\<lambda> u urc. if prod.fst (urc) = x' \<or> prod.fst (urc) = y'
                                    then (y', cardx + cardy) else urc) r_card"
  define nb where "nb = not_blocked state"
  define nb' where "nb' = not_blocked_upd_all (\<lambda> d b. 
                                   if d =  e then True
                                   else if {abstract_rep_map r_card (fst d) , abstract_rep_map r_card (snd d) } = {x', y'} 
                                   then False
                                   else b) nb"
  define state' where "state' = state 
              \<lparr>  \<FF> := \<FF>', current_flow := f',
                balance := b',
                actives := E'', conv_to_rdg := to_rdg', 
                rep_comp_card := r_card',
                not_blocked := nb'\<rparr>"

  note defs_impl = state'_def \<FF>'_def e_def \<gamma>_def E'_def
              f_def \<FF>_def f'_def b_def x'_def r_card'_def r_card_def
              xx_def xy_def  x_def y_def b'_def Q_def cardx_def cardy_def
              to_rdg'_def y'_def to_rdg_def yy_def E''_def nb_def
              nb'_def

   have state'_is: "state' = maintain_forest_upd state"
    apply(rule Algo_state.equality)
    by (auto intro!: cong[OF cong, OF refl, of _ _ _ _ rep_comp_upd_all] ext 
          simp add: maintain_forest_upd_def Let_def defs_impl)
  note 10= state'_is

  have set_invar_E'[simp]: "set_invar E'"
    using E'_def all_invars(15) invar_aux17_def by blast

  have E'_substE:"to_set E' \<subseteq> \<E>"
    using all_invars(1) by(simp add: E'_def invar_aux1_def)
  have e_prop: "e \<in> to_set E'" "abstract_flow_map f e > 8 * real N *\<gamma>"
                "get_from_set (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E' = Some e"
    apply(all \<open>rule maintain_forest_call_condE[OF assms(2)]\<close>)
    using set_get(2,3)[OF set_invar_E'] 
    by(auto simp add: f_def e_def \<gamma>_def E'_def)
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
  have rep_comp_invar_r_card: "rep_comp_invar r_card"
    using assms(3) r_card_def by blast
  have not_blocked_invar_nb: "not_blocked_invar nb"
    using assms(3) nb_def by blast
  have in_V_rep_dom: "a \<in> \<V> \<Longrightarrow> a \<in> rep_comp_domain r_card" for a
    using assms(3) by(auto simp add: r_card_def)
  have good_graphF: "good_graph_invar \<FF>"
    using all_invars(16) invar_aux18_def local.\<FF>_def by force
  have F'_digraph_abs_is:"[\<FF>']\<^sub>g = [\<FF>]\<^sub>g \<union> {(fst e, snd e), (snd e, fst e)}"
    using good_graphF by (auto simp add: \<FF>'_def good_graph_invar_def)
  hence F'_to_graph_is:"to_graph \<FF>' = to_graph \<FF> \<union> {{fst e, snd e}}"
      by (auto simp add: to_graph'_def)
  have to_rdg'_is: "abstract_conv_map to_rdg' = 
      (\<lambda>d. if d = (x, y) then F e else if d = (y, x) then B e else abstract_conv_map to_rdg d)"
    using assms(3) 
    by(subst to_rdg'_def  add_direction_result)+
      (auto simp add: add_direction_result to_rdg_def)
  have forest_edges_neq_e:"{a, b} \<in> to_graph \<FF> \<Longrightarrow> {a, b} \<noteq> {x, y}" for a b
    using  assms(1) e_in_E' from_aux_invar'(11)  mk_disjoint_insert
        new_edge_disjoint_components[OF refl refl refl]
    by(fastforce simp add: x_def y_def local.\<FF>_def E'_def)
  hence dir_forest_edges_neq_e:"(a, b) \<in> digraph_abs \<FF> \<Longrightarrow> (a, b) \<noteq> (x, y)" 
                               "(a, b) \<in> digraph_abs \<FF> \<Longrightarrow> (a, b) \<noteq> (y, x)" for a b
    by(auto simp add: to_graph'_def)
  have res_edges_new_forest_are:"abstract_conv_map to_rdg' ` [\<FF>']\<^sub>g  
         = {F e, B e} \<union> abstract_conv_map to_rdg ` [\<FF>]\<^sub>g"
    using x_not_y dir_forest_edges_neq_e 
    by((subst to_rdg'_is  F'_digraph_abs_is)+)
      (auto simp add:  \<FF>'_def to_rdg'_def to_rdg_def \<FF>_def x_def y_def)
  have 114: "{x', y'} = {abstract_rep_map r_card (fst e), abstract_rep_map r_card (snd e)}"
    by(auto simp add: x'_def y'_def xx_def yy_def xy_def x_def y_def)
  have 113: "to_set E'' \<subseteq> to_set E' - {e}"
    using 114 set_filter(1)[OF set_invar_E']
    by(auto simp add: E''_def)
  have a113a: "to_set E'' = to_set E' - {d| d. {abstract_rep_map r_card (fst d), abstract_rep_map r_card (snd d)} = {x', y'}}"
    using 114 set_filter(1)[OF set_invar_E']
    by(auto simp add: E''_def)
  have reachable_in_forest_fst_in_V:"reachable (to_graph \<FF>) a b \<Longrightarrow> a \<in> \<V>" for a b 
    using assms(1) from_aux_invar'(15) local.\<FF>_def reachable_to_Vs(1) by blast
  have reachable_in_forest_snd_in_V:"reachable (to_graph \<FF>) a b \<Longrightarrow> b \<in> \<V>" for a b 
    using reachable_in_forest_fst_in_V reachable_sym by fast
  have new_forest_Vs_in_V: "dVs (digraph_abs (Algo_state.\<FF> state')) \<subseteq> \<V>"
    by (auto intro:  invar_aux15E aux_invarE[OF assms(1)] 
             simp add: state'_def F'_digraph_abs_is insert_edge_dVs dVs_Vs_same \<FF>_def)
  have 1110:"reachable (to_graph \<FF>) v x \<Longrightarrow> reachable (to_graph \<FF>') v x" for v x
      by (auto simp add: reachable_subset subset_insertI  \<FF>'_def
                            insert_abstraction'[OF good_graphF])
    have x'_y'_in_V:"x' \<in> \<V>"  "y' \<in> \<V>" 
      using "114"  from_aux_invar'(9)[OF assms(1)] fste_V snde_V
      by(auto simp add: r_card_def doubleton_eq_iff)
    have new_balance_is: "a_balance state' = (\<lambda>v. if v = x' then 0
          else if v = y' then abstract_bal_map b y' + abstract_bal_map b x'
               else abstract_bal_map b v)"
      using assms(3)
      by(auto simp add:state'_def b'_def  abstract_bal_map_homo[OF  _  refl] b_def)
    have new_redge_F_is:"oedge ` abstract_conv_map to_rdg' ` [\<FF>']\<^sub>g =
              Set.insert e (oedge ` abstract_conv_map to_rdg ` [\<FF>]\<^sub>g)"
      using dir_forest_edges_neq_e(1,2) 
      by (auto simp add: to_rdg'_is F'_digraph_abs_is x_def y_def)

  have invar_aux7_state':"invar_aux7 state'"
  proof-
    show ?thesis 
    proof(rule invar_aux7I)
      fix u v
      assume asm: "reachable (to_graph (Algo_state.\<FF> state')) u v"
      hence asm': "reachable (to_graph (Algo_state.\<FF> state')) v u" 
        by (simp add: reachable_sym)
      show "representative state' u = representative state' v"
      proof(cases "u = v")
        case True
        then show ?thesis by simp
      next
        case False
        note u_neq_v = False
        show ?thesis 
      proof(cases "reachable (to_graph (Algo_state.\<FF> state)) u v")
        case True
        note true=this
        hence same_r:"abstract_rep_map r_card u =  abstract_rep_map r_card v"  
          using all_invars(7) by(simp add: r_card_def invar_aux7_def)
         have reps_dom:"u \<in> rep_comp_domain (rep_comp_card state)"
                      "v \<in> rep_comp_domain (rep_comp_card state)"
          apply(all \<open>rule implementation_invar_partialE(7)[OF assms(3)]\<close>)
          using True reachable_in_forest_fst_in_V reachable_in_forest_snd_in_V
          by(auto simp add: \<FF>_def)
         show ?thesis
          using assms(3) same_r reps_dom
          by(force simp add:r_card_def state'_def r_card'_def  abstract_rep_map_rep_comp_upd_all) 
      next
        case False
        hence False': "\<not> reachable (to_graph (Algo_state.\<FF> state)) v u" 
          by (simp add: reachable_sym)
        have fste_sndexy:"{fst e, snd e} = {prod.fst xy, prod.snd xy}"
          unfolding xy_def x_def y_def
          by(auto split: if_split)
        have reach_rpop:"\<not> reachable (to_graph \<FF>) u xx \<Longrightarrow> u \<noteq> v \<Longrightarrow> reachable (to_graph \<FF>) u yy \<or> u = xx \<or> u = yy"
          apply(rule reachable_after_insert[where v = v])
          using False  asm fste_sndexy  insert_abstraction'[OF good_graphF]
          by(auto simp add: state'_def \<FF>'_def \<FF>_def  xx_def yy_def )        
        have reach_rpop':"\<not> reachable (to_graph \<FF>) v xx \<Longrightarrow> v \<noteq> u \<Longrightarrow>
                                        reachable (to_graph \<FF>) v yy \<or> v = xx \<or> v = yy"
          apply(rule reachable_after_insert[where v = u])
          using False'  asm' fste_sndexy  insert_abstraction'[OF good_graphF]
          by(auto simp add: state'_def \<FF>'_def \<FF>_def  xx_def yy_def )       
        have reach_xx_yy: "reachable (to_graph \<FF>') xx yy"
          by(auto split: if_split 
               simp add: edges_reachable x_def y_def reachable_sym
                         \<FF>'_def xx_def yy_def xy_def  edges_reachable good_graphF insert_abstraction')
        have rachbale_with_reps:"reachable (to_graph \<FF>') xx (abstract_rep_map r_card xx)
                                   \<or> abstract_rep_map r_card xx = xx"
                                "reachable (to_graph \<FF>') yy (abstract_rep_map r_card yy) 
                                   \<or> abstract_rep_map r_card yy = yy"
          using "1110"  invar_aux8_def[of state]  all_invars(6) local.\<FF>_def r_card_def 
                \<FF>_def by force+
        have rachbale_with_reps:"reachable (to_graph \<FF>) xx (abstract_rep_map r_card xx) \<or> abstract_rep_map r_card xx = xx"
                                "reachable (to_graph \<FF>) yy (abstract_rep_map r_card yy) \<or> abstract_rep_map r_card yy = yy"
          using "1110"  invar_aux8_def[of state]  all_invars(6) local.\<FF>_def r_card_def 
                 \<FF>_def
          by force+
        have rachbale_with_reps:"reachable (to_graph \<FF>) xx (abstract_rep_map r_card xx) \<or> abstract_rep_map r_card xx = xx"
                                "reachable (to_graph \<FF>) yy (abstract_rep_map r_card yy) \<or> abstract_rep_map r_card yy = yy"
          using "1110"  invar_aux8_def[of state]  all_invars(6) local.\<FF>_def r_card_def \<FF>_def
          by force+
        have reps_dom:"u \<in> rep_comp_domain (rep_comp_card state)"
                      "v \<in> rep_comp_domain (rep_comp_card state)"
          apply(all \<open>rule implementation_invar_partialE(7)[OF assms(3)]\<close>)
          using  reachable_in_forest_fst_in_V reachable_in_forest_snd_in_V  asm' 
               new_forest_Vs_in_V reachable_to_Vs(4)[of _ v]  asm reachable_to_Vs(4)[of _ u]  
          by fastforce+

        show ?thesis
          apply(all \<open>rule implementation_invar_partialE(8)[OF assms(3)]\<close>)
          using reps_dom  assms(3)
                invar_aux7D[OF all_invars(7), of u xx] invar_aux7D[OF all_invars(7), of u yy]
                invar_aux7D[OF all_invars(7), of v xx] invar_aux7D[OF all_invars(7), of v yy]
                reach_rpop reach_rpop'
          by (auto  simp add:state'_def r_card'_def abstract_rep_map_rep_comp_upd_all local.\<FF>_def r_card_def x'_def y'_def)     
      qed 
    qed 
  qed
qed
  have comps_mod:" comps \<V> (insert {fst e, snd e} (to_graph \<FF>)) =
    comps \<V> (to_graph \<FF>) - {connected_component (to_graph \<FF>) (fst e), connected_component (to_graph \<FF>) (snd e)} \<union>
    {connected_component (to_graph \<FF>) (fst e) \<union> connected_component (to_graph \<FF>) (snd e)}"
       using all_invars(11) e_prop  fste_V snde_V 
      by(intro new_component_insert_edge)(auto simp add: invar_aux11_def \<FF>_def  E'_def )
    have cards_same_cond: "card (connected_component (to_graph \<FF>) x) 
                          \<le> card (connected_component (to_graph \<FF>) y) \<longleftrightarrow>
                          abstract_comp_map r_card x \<le> abstract_comp_map r_card y"
      using assms(1) 
      by (simp add: r_card_def \<FF>_def aux_invar_def invar_aux16_def x_def y_def)

    have same_reachability: "abstract_rep_map r_card v = x' \<or> abstract_rep_map r_card v = y'
                                \<longleftrightarrow> reachable (to_graph \<FF>') y' v" for v
    proof
      show "abstract_rep_map r_card v = x' \<or> abstract_rep_map r_card v = y' \<Longrightarrow> reachable (to_graph \<FF>') y' v"
      proof(goal_cases)
        case 1
        hence reachable_to_reps:"reachable (to_graph \<FF>) v x' \<or> v = x' \<or> reachable (to_graph \<FF>) v y' \<or> v = y'"
          using all_invars(6) by(auto elim: invar_aux8E simp add: local.\<FF>_def r_card_def)
        have "reachable (to_graph \<FF>) v x \<or> v = x \<or> reachable (to_graph \<FF>) v y \<or> v = y"
          using reachable_to_reps 
          unfolding x'_def xx_def xy_def y'_def yy_def r_card_def local.\<FF>_def
          apply(cases "cardx \<le> cardy") 
          apply auto
          using invar_aux8D[OF all_invars(6)]  reachable_trans[OF _ iffD2[OF reachable_sym]] 
                reachable_sym       
          by fastforce+
        hence "reachable (to_graph \<FF>') v x \<or> v = x "
          using "1110"[of v y] "1110"[of v x] reachable_trans[of _ v y x]
               edges_reachable[of x y] reachable_sym[of _ x y]
          by(auto simp add: \<FF>'_def x_def y_def  insert_abstraction'[OF  good_graphF])  
        hence "reachable  (to_graph \<FF>') v y "
          using reachable_trans[of _ v x y]  edges_reachable[of x y] 
          by(auto simp add: x_def y_def \<FF>'_def insert_abstraction'[OF  good_graphF]) 
        moreover hence "reachable (to_graph \<FF>') v x"
          using reachable_refl  \<open>reachable  (to_graph \<FF>') v x \<or> v = x\<close> reachable_in_Vs(1)
          by (force simp add:  \<FF>'_def x_def y_def )
        ultimately have "reachable (to_graph \<FF>') v y'" (*REMOVE METIS, if possible*)
          by (metis "1110" reachable_trans all_invars(6) invar_aux8D local.\<FF>_def
              prod.sel(2) r_card_def xy_def y'_def yy_def)
         thus ?thesis
          by (simp add: reachable_sym)
      qed
      show "reachable (to_graph \<FF>') y' v \<Longrightarrow> abstract_rep_map r_card v = x' \<or> abstract_rep_map r_card v = y'"
      proof(goal_cases)
        case 1
        have "connected_component (to_graph \<FF>') (snd e) 
               = connected_component (to_graph \<FF>) (fst e) \<union> connected_component (to_graph \<FF>) (snd e)"
          using insert_edge_endpoints_same_component[OF reflexive, of _ "fst e" "snd e"]
              new_edge_disjoint_components[OF refl refl refl]
          by(force simp add: insert_abstraction'[OF good_graphF]   \<FF>'_def) 
        moreover have "reachable (to_graph \<FF>') (snd e) v \<or> reachable (to_graph \<FF>') (fst e) v"
          using 1 
          by (metis 1110 Undirected_Set_Graphs.reachable_trans all_invars(6) invar_aux8E local.\<FF>_def
              r_card_def snd_conv x_def xy_def y'_def y_def yy_def)
        ultimately have "reachable (to_graph \<FF>) (snd e) v \<or> 
                reachable (to_graph \<FF>) (fst e) v \<or> fst e = v \<or> snd e = v"
          using Un_iff  in_connected_componentE in_connected_componentI
              insert_abstraction'[OF good_graphF] new_edge_disjoint_components[OF refl refl refl]
          unfolding \<FF>'_def 
          by metis
        hence "reachable (to_graph \<FF>) x' v \<or> reachable (to_graph \<FF>) y' v \<or> y' = v \<or> x' = v"
          by (smt (verit, best) Undirected_Set_Graphs.reachable_trans all_invars(6) fst_conv invar_aux8E
              local.\<FF>_def r_card_def reachable_sym snd_conv x'_def x_def xx_def xy_def y'_def y_def
              yy_def)
         then show ?case 
           using invar_aux7D[OF all_invars(7)]
                 invar_aux8D[OF all_invars(6), of xx]
                 invar_aux8D[OF all_invars(6), of yy]
           unfolding  local.\<FF>_def r_card_def x'_def y'_def 
           by metis
      qed
    qed

    have x'_neq_y': "x' \<noteq> y'" 
    proof(rule ccontr, goal_cases)
      case 1
      hence "reachable (to_graph \<FF>) x y \<or> x = y"
        using  invar_aux8D[OF all_invars(6)] 
        using reachable_trans fst_conv reachable_sym
            snd_conv
        unfolding x'_def y'_def  xx_def yy_def xy_def r_card_def local.\<FF>_def 
        by (smt (verit, best))
      moreover have "connected_component (to_graph \<FF>) x \<noteq> connected_component (to_graph \<FF>) y"
        using all_invars(11)[simplified invar_aux11_def ] E'_def e_in_E'
        by(fastforce simp add: x_def y_def  E'_def local.\<FF>_def)
      ultimately show False 
        using connected_components_member_eq in_connected_componentI by fast
    qed 
      have e_not_in_F: "{x, y} \<notin> (to_graph \<FF>)" 
        using  e_in_E' from_aux_invar'(11)[OF assms(1)] insert_absorb
            new_edge_disjoint_components[OF refl refl refl, of x y "to_graph \<FF>"]
        by(fastforce simp add: x_def y_def E'_def local.\<FF>_def)

  have invar8: "invar_aux8 state'"
  proof-
    have 1111:"reachable (to_graph \<FF>') v (abstract_rep_map r_card' v) 
                 \<or> v = abstract_rep_map r_card' v"  for v
    proof(cases "abstract_rep_map r_card' v = abstract_rep_map r_card v")
      case True
      then show ?thesis 
        using "1110" all_invars(6) invar_aux8D
        by(auto simp add: local.\<FF>_def r_card_def)
    next
      case False
      hence "v \<in> rep_comp_domain r_card" 
        using  rep_comp_invar_r_card not_in_dom_id [of v r_card'] not_in_dom_id [of v r_card]
            rep_comp_upd_all(4)[OF rep_comp_invar_r_card]
        by(force simp add: r_card'_def r_card_def) 
      hence "reachable (to_graph \<FF>') y' v" "abstract_rep_map r_card' v = y'"
        using same_reachability[of v] False
                 abstract_rep_map_rep_comp_upd_all[OF rep_comp_invar_r_card, of _ v]
        by(auto simp add: r_card'_def \<FF>'_def y'_def r_card_def )
      then show ?thesis 
        by (simp add: reachable_sym)
    qed
    then show ?thesis 
      by(simp add: invar_aux8_def state'_def)
  qed

   have y'_y'_reach:"reachable (to_graph \<FF>') y' y'" 
   proof(cases "y' = yy")
     case True
     then show ?thesis
      using reachable_refl[of y "to_graph \<FF>'"] \<FF>'_def edges_reachable[of "fst e" "snd e" "to_graph \<FF>'"]
         reachable_in_Vs(2)[of "to_graph \<FF>'" "fst e" "snd e"] 
         reachable_refl[of x "to_graph \<FF>'"] reachable_in_Vs[of "to_graph \<FF>'" "snd e" "fst e"]
           F'_to_graph_is
      by(auto simp add:  y_def x_def yy_def xy_def)
  next 
    case False
     show ?thesis
        apply(rule reachable_refl[of y' "to_graph \<FF>'"], rule reachable_in_Vs(2)[of "to_graph \<FF>'" yy y'])
        apply(rule reachable_subset[of "to_graph \<FF>" yy y' "to_graph \<FF>'"], rule invar_aux8E[OF all_invars(6)])
        using False F'_to_graph_is
        by(fastforce simp add: y'_def \<FF>'_def  \<FF>_def r_card_def)+
  qed

  have "aux_invar state'" 
  proof(rule aux_invarI)
    show "invar_aux1 state'" 
      using all_invars(1) set_filter(1)[OF set_invar_E']
      by(auto simp add: invar_aux1_def state'_def E''_def E'_def)    
    show "invar_aux2 state'" 
      using res_edges_new_forest_are  eeinfracE all_invars(2)
      by(auto intro!: invar_aux2I simp add: state'_def to_rdg_def invar_aux2_def local.\<FF>_def )
    show "invar_aux3 state'" 
      using all_invars(2) eeinfracE   o_edge_res 
      by(intro invar_aux3I)
        (auto simp add: to_rdg_def local.\<FF>_def res_edges_new_forest_are  state'_def F_def F_redges_def
                 elim!: invar_aux2E) 
    show "invar_aux4 state'" 
      using "113" from_aux_invar'(4)[OF assms(1)]
      by(intro  invar_aux4I)
        (auto  simp add: to_rdg_def res_edges_new_forest_are local.\<FF>_def 
               image_Un oedge_both_redges_image
                E'_def  state'_def F_def F_redges_def )
    have "consist ([\<FF>]\<^sub>g \<union> {(fst e, snd e), (snd e, fst e)})
     (abstract_conv_map (add_direction to_rdg (fst e) (snd e) e))"
      using assms(3)  assms(1) from_aux_invar'(6)  x_not_y 
      by(intro abstract_conv_consist[OF _ _ refl]) (auto simp add: make_pair' local.\<FF>_def to_rdg_def)   
    thus "invar_aux6 state'"
      by(auto  intro!: invar_aux6I'' simp add:state'_def to_rdg'_def  F'_digraph_abs_is x_def y_def)
    show "invar_aux8 state'" using invar8 by simp
    show "invar_aux7 state'" 
      using invar_aux7_state' by blast
    have "x \<in> \<V>" 
      by (simp add: dVsI'(1) x_def)
    moreover have "y \<in> \<V>" 
      using dVsI'(2)[of "make_pair e"] einE y_def make_pair[OF refl refl] by simp 
    ultimately have "yy \<in> \<V>" by(simp add: yy_def xy_def)
    hence y'_in_V:"y' \<in> \<V>" 
      using all_invars(8)
      by(auto elim: invar_aux9E simp add: r_card_def y'_def)
    show"invar_aux9 state'" 
    proof(rule invar_aux9I, goal_cases)
      case (1 v)
      then show ?case 
      using invar_aux8D[OF invar8, of v] set_mp[OF new_forest_Vs_in_V reachable_to_Vs(4)] y'_in_V
      by auto
  qed
  show "invar_aux5 state'"
      by(auto intro!: invar_aux5I simp add: state'_def F'_to_graph_is
                assms(1) from_aux_invar'(5) local.\<FF>_def)
    have "connected_component (to_graph \<FF>) (fst e) \<subseteq> \<V>"
      using all_invars(10) dVsI'(1)[of "make_pair e"] einE make_pair[OF refl refl]
      by(simp add: invar_aux10_def \<FF>_def )
    moreover have snd_comp_in_V:"connected_component (to_graph \<FF>) (snd e) \<subseteq> \<V>"
      using all_invars(10)  dVsI'(2)[of "make_pair e"] einE make_pair[OF refl refl] 
      by (simp add: invar_aux10_def \<FF>_def)
    ultimately show "invar_aux10 state'"
      using all_invars(10)
      apply(simp add: state'_def invar_aux10_def \<FF>'_def \<FF>_def)
    proof(rule, goal_cases)
      case (1 v)
      then show ?case 
      proof(cases " v \<in> connected_component (to_graph (Algo_state.\<FF> state)) (fst e)", goal_cases)
        case True
        then show ?thesis 
          using 1 insert_edge_endpoints_same_component[of "insert {fst e, snd e} (to_graph (Algo_state.\<FF> state))"  "fst e" "snd e" 
                       "(to_graph (Algo_state.\<FF> state))"]  
                 connected_components_member_eq[of v "insert {fst e, snd e} (to_graph (Algo_state.\<FF> state))" "fst e"] 
          unfolding  \<FF>'_def \<FF>'_def \<FF>_def 
          by (metis Un_iff \<open>connected_component (to_graph \<FF>) (snd e) \<subseteq> \<V>\<close> connected_components_member_eq
              good_graphF insert_abstraction' local.\<FF>_def sup.bounded_iff)
      next
        case False
        then show ?thesis using 1 (*Fix at some point if possible*)
           insert_edge_endpoints_same_component[of "insert {fst e, snd e} (to_graph (Algo_state.\<FF> state))" "snd e" "fst e" 
                "to_graph (Algo_state.\<FF> state)"]
           connected_components_member_eq[of v  "insert {fst e, snd e} (to_graph (Algo_state.\<FF> state))" "snd e"] 
           unite_disjoint_components_by_new_edge[of "fst e" "to_graph (Algo_state.\<FF> state)" v "snd e"] 
           connected_components_member_sym[of _ "to_graph (Algo_state.\<FF> state)" v] 
          apply(cases " v \<in> connected_component (to_graph (Algo_state.\<FF> state)) (snd e)") 
          unfolding \<FF>'_def \<FF>_def 
          by (smt (verit, best) Un_iff \<open>connected_component (to_graph \<FF>) (fst e) \<subseteq> \<V>\<close> good_graphF
              insert_abstraction' insert_commute local.\<FF>_def snd_comp_in_V sup.bounded_iff)+
    qed
  qed 
    show "invar_aux11 state'"
    proof(rule invar_aux11I, rule ccontr, unfold neg_neq)
      fix d
      assume assm: "d \<in> to_set (actives state')"
                   "connected_component (to_graph (Algo_state.\<FF> state')) (fst d) =
                    connected_component (to_graph (Algo_state.\<FF> state')) (snd d)"
      hence "d \<in> to_set E''" unfolding state'_def by simp
      hence dE:"d \<in> to_set E'" "{abstract_rep_map r_card (fst d), abstract_rep_map r_card (snd d)} \<noteq> {x', y'}" 
        using  set_filter(1)[OF set_invar_E']
        unfolding E''_def by auto
      have different_comps: "connected_component (to_graph \<FF>) (fst d) 
                         \<noteq> connected_component (to_graph \<FF>) (snd d)"
        using assms(1) dE(1) from_aux_invar'(11)
        by(auto simp add: E'_def local.\<FF>_def)
     have different_reps_before: "abstract_rep_map r_card (fst d) \<noteq> abstract_rep_map r_card (snd d)"
      proof
        assume "abstract_rep_map r_card (fst d) = abstract_rep_map r_card (snd d)"
        hence "reachable (to_graph \<FF>) (fst d) (snd d) \<or> fst d = snd d"
          using  reachable_trans[of "to_graph (Algo_state.\<FF> state)" "fst d" 
                      "representative state (fst d)" "snd d"] 
                 reachable_sym[of "to_graph (Algo_state.\<FF> state)" "snd d" "representative state (snd d)"] 
                  spec[OF all_invars(6)[simplified invar_aux8_def], of "fst d"]
                  spec[OF all_invars(6)[simplified invar_aux8_def], of "snd d"]
          by(auto simp add: state'_def  r_card_def \<FF>_def)
        thus False 
          using connected_components_member_eq[of "snd d" "to_graph \<FF>" "fst d"] 
                different_comps in_connected_componentI[of "to_graph \<FF>" "fst d" "snd d"] by auto
      qed
       have "connected_component (to_graph \<FF>') (fst d) =
                     connected_component (to_graph \<FF>')  (snd d)"
        using  assm(2) by(simp add: state'_def)
      hence "fst d \<noteq>  snd d \<Longrightarrow> reachable (to_graph \<FF>') (fst d)  (snd d)"
        using  in_connected_componentE[of "snd d" "to_graph \<FF>'" "fst d"] 
               in_own_connected_component[of "snd d" "to_graph \<FF>'"] by auto 
      hence "abstract_rep_map r_card' (fst d) = abstract_rep_map r_card' (snd d)"
          using   invar_aux7_state'
          by (cases "fst d \<noteq>  snd d", auto elim: invar_aux7E simp add: state'_def)
      hence lst:"reachable (to_graph \<FF>') y' (fst d) \<and> reachable (to_graph \<FF>') y' (snd d)" 
        using different_reps_before  reachable_trans[of "(to_graph \<FF>')" y' "fst d" "snd d"] 
              reachable_trans[of "(to_graph \<FF>')" y' "snd d" "fst d"] reachable_sym[of "(to_graph \<FF>')" "fst d" "snd d"]
              \<open>fst d \<noteq> snd d \<Longrightarrow> reachable (to_graph \<FF>') (fst d) (snd d)\<close> same_reachability
         apply (cases "fst d \<in> rep_comp_domain r_card", all \<open>cases "snd d \<in> rep_comp_domain r_card"\<close>) 
          by (simp_all add: r_card'_def abstract_rep_map_rep_comp_upd_all[OF rep_comp_invar_r_card]) 
               fastforce+
      show False 
        using dE(2) different_reps_before insert_commute lst same_reachability[of "fst d"] 
              same_reachability[of "snd d"] 
        by auto
    qed
    show "invar_aux12 state'"
    proof(rule invar_aux12I, goal_cases)
      case (1 v) 
     
      show ?case 
      proof(cases "v = y'")
        case True
        then show ?thesis using y'_y'_reach same_reachability
          by(simp add: state'_def r_card'_def 
                abstract_rep_map_rep_comp_upd_all not_in_dom_id rep_comp_invar_r_card)
      next
        case False 
        moreover have not_x': "v \<noteq> x'" using b'_def 1 state'_def new_balance_is by auto
        ultimately have "abstract_bal_map b' v = abstract_bal_map b v" 
          using new_balance_is by(simp add: state'_def)
        hence "abstract_bal_map b v \<noteq> 0" using b'_def False 1 state'_def not_x' by simp
        hence same_r:"abstract_rep_map r_card v = v" using all_invars(12) 1 
         by(auto simp add: b_def r_card_def invar_aux12_def)
        have not_reach_y: "reachable (to_graph \<FF>) v y \<Longrightarrow> False"
        proof-
          assume "reachable (to_graph \<FF>) v y"
          hence "abstract_rep_map r_card y = v"
            using all_invars(7) same_r
            by(fastforce simp add: invar_aux7_def local.\<FF>_def r_card_def )
          hence "v = abstract_rep_map r_card xx \<or> v = abstract_rep_map r_card yy" 
            by(auto split: if_split simp add: xx_def yy_def xy_def)
          thus False using not_x' False y'_def x'_def by simp
        qed
        have not_reach_x:"reachable (to_graph \<FF>) v x \<Longrightarrow> False"
        proof-
          assume "reachable (to_graph \<FF>) v x"
          hence "abstract_rep_map r_card x = v"
            using all_invars(7) same_r
            by(fastforce simp add: invar_aux7_def local.\<FF>_def r_card_def )
          hence "v = abstract_rep_map r_card xx \<or> v = abstract_rep_map r_card yy"
            by(auto split: if_split simp add: xx_def yy_def xy_def)
          thus False using not_x' False by(simp add: y'_def x'_def)
        qed
        have "reachable (to_graph \<FF>') v y' \<Longrightarrow> False" 
         using  "1"(1) False not_x' reachable_sym[of _ v y'] same_r same_reachability[of v]
            by simp
          moreover have "v \<in> rep_comp_domain r_card"
            using "1"(1) assms(3) r_card_def by blast
          ultimately show ?thesis
           unfolding abstract_rep_map_rep_comp_upd_all[OF rep_comp_invar_r_card]
            using reachable_sym[of "to_graph \<FF>'" v y'] same_r same_reachability[of ]
            by (auto simp add: state'_def r_card'_def  abstract_rep_map_rep_comp_upd_all[OF rep_comp_invar_r_card])
      qed
    qed
    show "invar_aux13 state'"
      unfolding invar_aux13_def
    proof(rule, goal_cases)
      case (1 d)
      then show ?case 
      proof(cases "d \<in> \<E> - to_set (actives state)")
        case True
        hence "connected_component (to_graph \<FF>) (fst d) = connected_component (to_graph \<FF>)  (snd d)"
          using invar_aux13_def  all_invars(13) \<FF>_def by blast
        hence "(snd d) \<in> connected_component  (to_graph \<FF>) (fst d)" 
          by (simp add: in_connected_componentI2)
        hence "reachable  (to_graph \<FF>) (snd d) (fst d) \<or> fst d = snd d"
          by (meson in_connected_componentE reachable_sym)
        hence "reachable (to_graph \<FF>') (snd d) (fst d) \<or> fst d = snd d" 
          using "1110" \<FF>'_def by blast
        hence "connected_component (to_graph \<FF>') (fst d) = connected_component (to_graph \<FF>') (snd d)"
          using connected_components_member_eq[OF in_connected_componentI, of "(to_graph \<FF>')" "(snd d)" "(fst d)"] 
          by auto
        then show ?thesis 
          by(simp add: state'_def \<FF>'_def \<FF>_def )
      next
        case False
        hence dd:"d \<in> {d| d. {abstract_rep_map r_card (fst d), abstract_rep_map r_card (snd d)} = {x', y'}}"
          using 1  set_filter(1)[OF set_invar_E'] by(auto simp add: state'_def E''_def E'_def)
        hence "abstract_rep_map r_card (fst d) = x' \<or> abstract_rep_map r_card (fst d) = y'"
          by fastforce
        hence "reachable (to_graph \<FF>) (fst d) x' \<or> fst d = x' \<or> fst d = y' \<or> reachable (to_graph \<FF>) (fst d) y'" 
          using all_invars(6) by(auto elim: invar_aux8E simp add: local.\<FF>_def r_card_def)
        moreover have a1:"reachable (to_graph \<FF>) x' xx \<or> x' = xx" 
          using all_invars(6) invar_aux8_def local.\<FF>_def r_card_def reachable_sym x'_def  by fastforce 
        moreover have a2:"reachable (to_graph \<FF>') xx y'"
        proof-
          have "abstract_comp_map r_card x \<le> abstract_comp_map r_card y 
              \<Longrightarrow> reachable (insert {fst e, snd e} (to_graph \<FF>)) 
                         x (abstract_rep_map r_card y)"
            using all_invars(6) invar_aux8_def[of state] \<FF>_def r_card_def 
            reachable_subset[of " (to_graph \<FF>)" y "abstract_rep_map r_card y" 
                             "insert {fst e, snd e}  (to_graph \<FF>)"]
            by( cases "y = abstract_rep_map r_card y", simp add: edges_reachable insert_commute x_def y_def, 
              intro reachable_trans[of _  y x "abstract_rep_map r_card x"]
                     reachable_trans[of _  x y "abstract_rep_map r_card y"],
              auto simp add: edges_reachable insert_commute x_def y_def)
          moreover have "\<not> abstract_comp_map r_card x \<le> abstract_comp_map r_card y \<Longrightarrow> 
                          reachable (insert {fst e, snd e} (to_graph \<FF>)) y (abstract_rep_map r_card x)"
            using all_invars(6) invar_aux8_def[of state] \<FF>_def r_card_def
              reachable_subset[of "(to_graph \<FF>)" x "abstract_rep_map r_card x" "insert {fst e, snd e} (to_graph \<FF>)"]
            by( cases "x = abstract_rep_map r_card x", simp add: edges_reachable insert_commute x_def y_def, 
              intro reachable_trans[of _  y x "abstract_rep_map r_card x"],
              auto simp add: edges_reachable insert_commute x_def y_def )
          ultimately show ?thesis 
            by (simp add: \<FF>'_def cardx_def cardy_def good_graphF
                insert_abstraction' xx_def xy_def y'_def yy_def)
        qed
        ultimately have  fst_y: "reachable (to_graph \<FF>') (fst d) y' \<or> fst d = y'" 
          using "1110"  invar_aux7D[OF all_invars(7), of] reachable_sym[of _ y']
              same_reachability[of "fst d"]  same_reachability[of xx]
          by(auto simp add: local.\<FF>_def r_card_def)
        have "abstract_rep_map r_card (snd d) = x' \<or> abstract_rep_map r_card (snd d) = y'"
          using dd by force
        hence "reachable (to_graph \<FF>) (snd d) x' \<or> snd d = x' \<or> snd d = y' 
                       \<or> reachable (to_graph \<FF>) (snd d) y'" 
          using all_invars(6) by(auto elim: invar_aux8E simp add: local.\<FF>_def r_card_def)
        hence  "reachable (to_graph \<FF>') (snd d) y' \<or> snd d = y'" 
          using a1 a2  "1110"  invar_aux7D[OF all_invars(7), of] reachable_sym[of _ y']
              same_reachability[of "snd d"]  same_reachability[of xx]
          by(auto simp add: local.\<FF>_def r_card_def)
        then show ?thesis
          using fst_y
          by (auto intro!: connected_components_member_eq 
                  intro: in_connected_componentI reachable_trans[OF _ iffD1[OF reachable_sym]]
                            connected_components_member_sym
               simp add:  state'_def in_own_connected_component)
      qed
    qed
    show "invar_aux14 state'"
      apply(rule invar_aux14I, rule validFI)
      using  x_not_y 
      by (auto intro!:  graph_invar_insert 
                intro: invar_aux14E[OF all_invars(18)] validFE 
             simp add: \<FF>_def  state'_def  F'_to_graph_is)
    show "invar_aux15 state'"
      using  new_forest_Vs_in_V
      by(auto intro: invar_aux15I simp add: dVs_Vs_same)
    have a1:"v \<in> \<V> \<Longrightarrow> y' = abstract_rep_map r_card' v 
               \<Longrightarrow> abstract_comp_map r_card x +  abstract_comp_map r_card y 
               = card (connected_component (to_graph \<FF>') v)"
      for v
    proof(goal_cases)
      case 1
      moreover hence "v \<in> rep_comp_domain r_card" 
        using assms(3) r_card_def by auto
      ultimately have comp_is:"(connected_component (to_graph \<FF>') v)
               = (connected_component (to_graph \<FF>) x) \<union> (connected_component (to_graph \<FF>) y)" 
       using  connected_components_member_eq[OF in_connected_componentI[of "to_graph \<FF>'" y' x]]
              connected_components_member_eq[OF in_connected_componentI[of "to_graph \<FF>'" y' ]]
           insert_edge_endpoints_same_component[OF reflexive, of "to_graph \<FF>" x y]
           new_edge_disjoint_components[OF refl refl refl, of x y] 
            same_reachability[of x]  same_reachability[of v] 
            same_reachability[of y] 
       by(auto simp add: x'_def x_def xx_def xy_def y_def r_card'_def   F'_to_graph_is
                 abstract_rep_map_rep_comp_upd_all[OF rep_comp_invar_r_card])
     show ?case
        apply(subst comp_is,subst card_Un_disjnt)
        using 1 all_invars(14) all_invars(10)  fste_V snde_V  all_invars(11)  e_in_E' 
              unequal_components_disjoint[of "to_graph (Algo_state.\<FF> state)" "fst e" "snd e" UNIV, simplified] 
        by (auto intro!: finite_subset[of "connected_component _ _", OF _ \<V>_finite]
                 elim!: invar_aux16E invar_aux11E
                 simp add:  E'_def disjnt_def r_card_def \<FF>_def invar_aux10_def x_def y_def )
    qed
    have a2:"v \<in> \<V> \<Longrightarrow> abstract_rep_map r_card' v \<noteq> y' 
               \<Longrightarrow> abstract_comp_map r_card v = card (connected_component (to_graph \<FF>') v) " for v
    proof(goal_cases)
      case 1
      note 2 = this
      moreover hence "v \<in> rep_comp_domain r_card" 
        using assms(3) r_card_def by auto
     ultimately have neither_x'_nor_y':"abstract_rep_map r_card v \<noteq> x'" "abstract_rep_map r_card v \<noteq> y'"
       using abstract_rep_map_rep_comp_upd_all[OF rep_comp_invar_r_card] 
       by(auto simp add: r_card'_def)
     have " x \<notin> connected_component (to_graph \<FF>) v" 
          " y \<notin> connected_component (to_graph \<FF>) v"
        using  all_invars(7)  neither_x'_nor_y' 
        by(auto intro: case_split[of "cardx \<le> cardy"]
                 elim!: invar_aux7E in_connected_componentE
              simp add: r_card_def x'_def y'_def xx_def yy_def xy_def \<FF>_def)
      hence "(connected_component (to_graph \<FF>') v) = (connected_component (to_graph \<FF>) v)" 
        using  unite_disjoint_components_by_new_edge[of x "to_graph \<FF>" v y]
        by (auto simp add: F'_to_graph_is  x_def y_def)
      then show ?case 
        by (simp add: "2"(1) assms(1) from_aux_invar'(16) local.\<FF>_def r_card_def)
    qed
    show "invar_aux16 state'"
    proof(rule invar_aux16I, goal_cases)
      case (1 a)
      hence a_ind_dom: "a \<in> rep_comp_domain r_card"
        by(auto intro!: in_V_rep_dom)
      show ?case 
        using a1[OF 1] a2[OF 1] in_V_rep_dom[OF 1]
        apply(unfold state'_def, simp)
        apply(unfold r_card'_def abstract_comp_map_rep_comp_upd_all[OF rep_comp_invar_r_card]
                  abstract_rep_map_rep_comp_upd_all[OF rep_comp_invar_r_card]) 
        by simp(fastforce simp add:  cardx_def cardy_def if_P[OF  a_ind_dom]  \<FF>'_def F'_to_graph_is state'_def r_card'_def)+
    qed
    show "invar_aux17 state'"
      using all_invars(15) invar_filter[OF set_invar_E']
      by(simp add: invar_aux17_def state'_def E''_def E'_def)
    show "invar_aux18 state'" 
      by(auto intro!: invar_aux18I'' insert_undirected_edge_good_graph_invar_pres
                 simp add: state'_def  \<FF>'_def good_graphF)
    show "invar_aux20 state'"
      using  forest_symmetic[OF all_invars(17)]
      by(auto intro!: invar_aux20I' 
                 simp add: state'_def  good_graphF F'_digraph_abs_is \<FF>_def)
    show "invar_aux22 state'"
      unfolding invar_aux22_def
    proof(rule)
      fix d
      show "a_not_blocked state' d = (d \<in> \<F> state' \<union> to_set (actives state'))"
        unfolding state'_def 
      proof(cases "e = d", goal_cases)
        case 1
        moreover have "e = d \<Longrightarrow> \<not> abstract_not_blocked_map nb d \<Longrightarrow> \<exists>y. not_blocked_lookup nb d = Some y"
          using assms(3) einE nb_def by blast
        ultimately show ?case 
          by (auto simp add: res_edges_new_forest_are  nb'_def F_def F_redges_def
                             not_blocket_update_all_abstract_not_blocked_map[OF not_blocked_invar_nb])
      next
        case 2
        note e_neq_d= this
        then have "abstract_not_blocked_map nb' d =
                  (d \<in> oedge ` abstract_conv_map to_rdg' ` [\<FF>']\<^sub>g \<or> d \<in> to_set E'')"
            unfolding nb'_def  not_blocket_update_all_abstract_not_blocked_map[OF not_blocked_invar_nb]
          proof(cases "d \<in> not_blocked_dom nb", goal_cases)
            case 1
            show ?case 
            proof(subst if_P[OF 1(2)], subst if_not_P[OF e_neq_d[symmetric]],
                  rule P_of_ifI, goal_cases)
          case 1
          note one = this
          have " d \<notin> to_set E''" 
            by (simp add: E''_def 1 local.set_filter(1) split_beta)
          moreover have "d \<notin> oedge ` abstract_conv_map to_rdg ` [\<FF>]\<^sub>g"
          proof(rule ccontr, goal_cases)
            case 1
            then obtain a b where ab: "(a, b) \<in> [\<FF>]\<^sub>g" "oedge ( abstract_conv_map to_rdg (a, b)) = d" by auto
            have "{a, b} = {fst d, snd d}" 
              using  ab(1) invar_aux6_conv_to_rdg_fstv[OF all_invars(5), of a b] 
                  invar_aux6_conv_to_rdg_sndv[OF all_invars(5), of a b]
               by(auto intro: oedge.elims[OF ab(2)]simp add: to_rdg_def local.\<FF>_def)
            hence "{fst d, snd d} \<in> to_graph \<FF>" 
              using ab(1)  by (auto simp add: doubleton_eq_iff to_graph'_def)
            hence "reachable (to_graph \<FF>) (fst d) (snd d)"
              by(auto intro!: edges_reachable)
            hence "abstract_rep_map r_card (fst d) = abstract_rep_map r_card (snd d)"
              using assms(1)by(auto dest:  from_aux_invar'(7) simp add: local.\<FF>_def r_card_def)
            hence "x' = y'" 
              using one by auto
            thus False 
              using x'_neq_y' by auto
          qed
          ultimately show ?case 
            using  e_neq_d new_redge_F_is by auto
        next
          case 2
          have same_amp:"abstract_not_blocked_map nb' d = abstract_not_blocked_map nb d" 
            using "2" e_neq_d
            by (auto simp add: nb'_def not_blocket_update_all_abstract_not_blocked_map[OF
                                not_blocked_invar_nb] in_not_blocked_dom_same_as_lookup)
          also have "... = (d \<in> oedge ` abstract_conv_map to_rdg ` digraph_abs \<FF>
                                \<or> d \<in> to_set E')"
            by (simp add: E'_def assms(1) from_aux_invar'(20) local.\<FF>_def nb_def to_rdg_def F_def F_redges_def)
          also have "... = (d \<in> oedge ` abstract_conv_map to_rdg' ` digraph_abs \<FF>'
                                \<or> d \<in> to_set E'')" 
            using "2" a113a e_neq_d new_redge_F_is by auto
          finally show ?case
            using "1"(2) same_amp in_not_blocked_dom_same_as_lookup by simp
        qed
      next
        case 2
        thus ?case 
          using  E'_substE  implementation_invar_partial_props(10)[OF assms(3)]
          by (auto simp add: to_rdg_def local.\<FF>_def nb_def new_redge_F_is
                            invar_aux22D[OF all_invars(19)]  a113a E'_def F_def F_redges_def)
      qed
      thus ?case by (simp add: F_def F_redges_def)
    qed
  qed
qed
  thus ?thesis 
    using state'_is by force
qed

lemma maintain_forest_dom_upd:
  assumes "maintain_forest_dom (maintain_forest_upd state)" "maintain_forest_call_cond state" 
  shows "maintain_forest_dom state"
  apply(rule maintain_forest.domintros)
  by(rule back_subst[of maintain_forest_dom , OF assms(1)];
     auto simp add: maintain_forest_upd_def Let_def
     elim!: maintain_forest_call_condE[OF assms(2)]
     intro!: Algo_state.equality cong[OF cong, OF refl, of _ _ _ _ rep_comp_upd_all] ext)+

lemma maintain_forest_dom_ret:
  assumes "maintain_forest_ret_cond state" 
  shows "maintain_forest_dom state"
  apply(rule maintain_forest.domintros)
  by (auto intro:  maintain_forest_ret_condE[OF assms(1)])

subsection \<open>Invariants for One Step\<close>

lemma invar_gamma_pres_one_step:
  assumes "maintain_forest_call_cond state"
          "invar_gamma state" 
    shows "invar_gamma (maintain_forest_upd state)"
  using assms(2) 
  by(auto elim: maintain_forest_call_condE[OF assms(1)] 
         split: if_split prod.split simp add: maintain_forest_upd_def Let_def invar_gamma_def)

lemma invars_pres_one_step:
  assumes "maintain_forest_call_cond state"
          "aux_invar state" "implementation_invar state"
   shows "implementation_invar (maintain_forest_upd state)"
    
        "thr \<ge> 0 \<Longrightarrow> invarA_1 thr state \<Longrightarrow> invarA_1 thr (maintain_forest_upd state)"

        "thr2 \<ge> 0 \<Longrightarrow> invarA_1 thr2 state \<Longrightarrow> invarA_2 thr1 thr2 state 
         \<Longrightarrow> thr2 \<le> 2 * current_\<gamma> state \<Longrightarrow> thr1 \<le> 8*real N * current_\<gamma> state 
         \<Longrightarrow> invarA_2 thr1 thr2 (maintain_forest_upd state)"

        "invar_gamma state \<Longrightarrow> thr2 \<ge> 0  \<Longrightarrow>invarA_1 thr2 state \<Longrightarrow> invarA_2 thr1 thr2 state \<Longrightarrow>
         thr2 \<le> 2 * current_\<gamma> state \<Longrightarrow> thr1 = 8*real N * current_\<gamma> state \<Longrightarrow>
         invar_isOptflow state \<Longrightarrow> invar_isOptflow (maintain_forest_upd state)"
proof-
  have all_invars: "invar_aux1 state" "invar_aux2 state" "invar_aux3 state" "invar_aux4 state"
                   "invar_aux6 state" "invar_aux8 state" "invar_aux7 state" "invar_aux9 state "
                   "invar_aux5 state" "invar_aux10 state" "invar_aux11 state" "invar_aux12 state"
                   "invar_aux13 state" "invar_aux16 state" "invar_aux17 state" "invar_aux18 state"
                    "invar_aux20 state" "invar_aux14 state"
                   "invar_aux22 state"
    using assms by(auto simp add: aux_invar_def)
  define  \<FF> where  "\<FF> = Algo_state.\<FF> state"
  define f where "f = current_flow state"
  define b where "b = balance state"
  define r_card where "r_card = rep_comp_card state"
  define E' where "E' = actives state"
  define to_rdg where "to_rdg = conv_to_rdg state"
  define \<gamma> where "\<gamma> = current_\<gamma> state"
  define e where "e = the( get_from_set 
                            (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E')"
  define x where "x = fst e"
  define y where "y = snd e"
  define to_rdg' where "to_rdg' = add_direction to_rdg x y e"
  define cardx where "cardx = abstract_comp_map r_card x"
  define cardy where "cardy = abstract_comp_map r_card y"
  define xy where " xy = (if cardx \<le> cardy then (x,y) else (y,x))"
  define xx where "xx = prod.fst xy"
  define yy where "yy = prod.snd xy"
  define \<FF>' where "\<FF>' =insert_undirected_edge (fst e) (snd e) \<FF>"
  define x' where "x' = abstract_rep_map r_card xx" 
  define y' where "y' = abstract_rep_map r_card yy"
  define Q where "Q = get_path x' y' \<FF>'"
  define f' where  "f' = (if abstract_bal_map b x' > 0 
                                   then augment_edges_impl f (abstract_bal_map b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges_impl f (- abstract_bal_map b x') (to_redge_path to_rdg' (itrev Q)))"
  define b' where "b' = move_balance b x' y'"
  define E'' where "E'' = filter (\<lambda> d. 
{abstract_rep_map r_card (fst d) , abstract_rep_map r_card (snd d) } \<noteq> {x', y'} ) E'"
  define r_card' where "r_card' = rep_comp_upd_all 
                                (\<lambda> u urc. if prod.fst (urc) = x' \<or> prod.fst (urc) = y'
                                    then (y', cardx + cardy) else urc) r_card"
  define nb where "nb = not_blocked state"
  define nb' where "nb' = not_blocked_upd_all (\<lambda> d b. 
                                   if d =  e then True
                                   else if {abstract_rep_map r_card (fst d) , abstract_rep_map r_card (snd d) } = {x', y'} 
                                   then False
                                   else b) nb"
  define state' where "state' = state 
              \<lparr>  \<FF> := \<FF>', current_flow := f',
                balance := b',
                actives := E'', conv_to_rdg := to_rdg', 
                rep_comp_card := r_card',
                not_blocked := nb'\<rparr>"

  note defs_impl = state'_def \<FF>'_def e_def \<gamma>_def E'_def
              f_def \<FF>_def f'_def b_def x'_def r_card'_def r_card_def
              xx_def xy_def  x_def y_def b'_def Q_def cardx_def cardy_def
              to_rdg'_def y'_def to_rdg_def yy_def E''_def nb_def
              nb'_def

   have state'_is: "state' = maintain_forest_upd state"
    apply(rule Algo_state.equality)
    by (auto intro!: cong[OF cong, OF refl, of _ _ _ _ rep_comp_upd_all] ext 
          simp add: maintain_forest_upd_def Let_def defs_impl)
  note 10= state'_is

  have set_invar_E'[simp]: "set_invar E'"
    using E'_def all_invars(15) invar_aux17_def by blast

  have E'_substE:"to_set E' \<subseteq> \<E>"
    using all_invars(1) by(simp add: E'_def invar_aux1_def)
  have e_prop: "e \<in> to_set E'" "abstract_flow_map f e > 8 * real N *\<gamma>"
                "get_from_set (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E' = Some e"
    apply(all \<open>rule maintain_forest_call_condE[OF assms(1)]\<close>)
    using set_get(2,3)[OF set_invar_E'] 
    by(auto simp add: f_def e_def \<gamma>_def E'_def)
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
  have rep_comp_invar_r_card: "rep_comp_invar r_card"
    using assms(3) r_card_def by blast
  have not_blocked_invar_nb: "not_blocked_invar nb"
    using assms(3) nb_def by blast
  have in_V_rep_dom: "a \<in> \<V> \<Longrightarrow> a \<in> rep_comp_domain r_card" for a
    using assms(3) by(auto simp add: r_card_def)
  have good_graphF: "good_graph_invar \<FF>"
    using all_invars(16) invar_aux18_def local.\<FF>_def by force
  have F'_digraph_abs_is:"[\<FF>']\<^sub>g = [\<FF>]\<^sub>g \<union> {(fst e, snd e), (snd e, fst e)}"
    using good_graphF by (auto simp add: \<FF>'_def good_graph_invar_def)
  hence F'_to_graph_is:"to_graph \<FF>' = to_graph \<FF> \<union> {{fst e, snd e}}"
    by (auto simp add: to_graph'_def)
  hence F_rewrite:"to_graph \<FF>' = Set.insert {fst e, snd e} (to_graph \<FF>)"
    by simp
  have to_rdg'_is: "abstract_conv_map to_rdg' = 
      (\<lambda>d. if d = (x, y) then F e else if d = (y, x) then B e else abstract_conv_map to_rdg d)"
    using assms(3) 
    by(subst to_rdg'_def  add_direction_result)+
      (auto simp add: add_direction_result to_rdg_def)
  have forest_edges_neq_e:"{a, b} \<in> to_graph \<FF> \<Longrightarrow> {a, b} \<noteq> {x, y}" for a b
    using  assms(2) e_in_E' from_aux_invar'(11)  mk_disjoint_insert
        new_edge_disjoint_components[OF refl refl refl]
    by(fastforce simp add: x_def y_def local.\<FF>_def E'_def)
  hence dir_forest_edges_neq_e:"(a, b) \<in> digraph_abs \<FF> \<Longrightarrow> (a, b) \<noteq> (x, y)" 
                               "(a, b) \<in> digraph_abs \<FF> \<Longrightarrow> (a, b) \<noteq> (y, x)" for a b
    by(auto simp add: to_graph'_def)
  have res_edges_new_forest_are:"abstract_conv_map to_rdg' ` [\<FF>']\<^sub>g  
         = {F e, B e} \<union> abstract_conv_map to_rdg ` [\<FF>]\<^sub>g"
    using x_not_y dir_forest_edges_neq_e 
    by((subst to_rdg'_is  F'_digraph_abs_is)+)
      (auto simp add:  \<FF>'_def to_rdg'_def to_rdg_def \<FF>_def x_def y_def)
  have 114: "{x', y'} = {abstract_rep_map r_card (fst e), abstract_rep_map r_card (snd e)}"
    by(auto simp add: x'_def y'_def xx_def yy_def xy_def x_def y_def)
  have 113: "to_set E'' \<subseteq> to_set E' - {e}"
    using 114 set_filter(1)[OF set_invar_E']
    by(auto simp add: E''_def)
  have a113a: "to_set E'' = to_set E' - {d| d. {abstract_rep_map r_card (fst d), abstract_rep_map r_card (snd d)} = {x', y'}}"
    using 114 set_filter(1)[OF set_invar_E']
    by(auto simp add: E''_def)
  have reachable_in_forest_fst_in_V:"reachable (to_graph \<FF>) a b \<Longrightarrow> a \<in> \<V>" for a b 
    using assms(2) from_aux_invar'(15) local.\<FF>_def reachable_to_Vs(1) by blast
  have reachable_in_forest_snd_in_V:"reachable (to_graph \<FF>) a b \<Longrightarrow> b \<in> \<V>" for a b 
    using reachable_in_forest_fst_in_V reachable_sym by fast
  have new_forest_Vs_in_V: "dVs (digraph_abs (Algo_state.\<FF> state')) \<subseteq> \<V>"
    by (auto intro:  invar_aux15E aux_invarE[OF assms(2)] 
             simp add: state'_def F'_digraph_abs_is insert_edge_dVs dVs_Vs_same \<FF>_def)
  have 1110:"reachable (to_graph \<FF>) v x \<Longrightarrow> reachable (to_graph \<FF>') v x" for v x
      by (auto simp add: reachable_subset subset_insertI  \<FF>'_def
                            insert_abstraction'[OF good_graphF])
    have x'_y'_in_V:"x' \<in> \<V>"  "y' \<in> \<V>" 
      using "114"  from_aux_invar'(9)[OF assms(2)] fste_V snde_V
      by(auto simp add: r_card_def doubleton_eq_iff)
    have new_balance_is: "a_balance state' = (\<lambda>v. if v = x' then 0
          else if v = y' then abstract_bal_map b y' + abstract_bal_map b x'
               else abstract_bal_map b v)"
      using assms(3)
      by(auto simp add:state'_def b'_def  abstract_bal_map_homo[OF  _  refl] b_def)
    have new_redge_F_is:"oedge ` abstract_conv_map to_rdg' ` [\<FF>']\<^sub>g =
              Set.insert e (oedge ` abstract_conv_map to_rdg ` [\<FF>]\<^sub>g)"
      using dir_forest_edges_neq_e(1,2) 
      by (auto simp add: to_rdg'_is F'_digraph_abs_is x_def y_def)
    note state_state' = state'_is
   have set_invar_E': "set_invar E'"
    using E'_def assms aux_invar_def invar_aux17_def by blast
  have E'_substE:"to_set E' \<subseteq> \<E>"
    using assms by(simp add: E'_def aux_invar_def invar_aux1_def)
  have 01:"reachable (to_graph \<FF>) xx x' \<or> xx = x'"
    by (simp add: assms(2) from_aux_invar'(8) local.\<FF>_def r_card_def x'_def)
  have 02:"reachable (to_graph \<FF>) yy y' \<or> yy = y'"
    by (simp add: assms(2) from_aux_invar'(8) local.\<FF>_def r_card_def y'_def)
  hence 1100:"connected_component (to_graph \<FF>) (fst e) \<noteq> connected_component (to_graph \<FF>) (snd e)"
    using e_prop assms(2)
    by(simp add: invar_aux11_def aux_invar_def  \<FF>'_def E'_def \<FF>_def)
  have fst_snd_e_neq: "fst e \<noteq> snd e"
    using  1100 by auto
  hence x_not_y:"x \<noteq> y"
    using x_def y_def by simp
    have asm': "invar_aux11 state" using assms  aux_invar_def by auto

    have cards_same_cond: "card (connected_component (to_graph \<FF>) x)
                           \<le> card (connected_component (to_graph \<FF>) y) \<longleftrightarrow>
                          abstract_comp_map r_card x \<le> abstract_comp_map r_card y" 
      using "01" "02"  invar_aux16D[OF all_invars(14), of x]
            invar_aux16D[OF all_invars(14), of y]
            reachable_in_forest_fst_in_V x'_y'_in_V(1,2)
      by(cases "cardx \<le> cardy") (auto simp add: xx_def xy_def yy_def  local.\<FF>_def r_card_def)
 
    have x'_not_y':"x' \<noteq> y'" 
      proof
        assume " x' = y'"
        hence "connected_component (to_graph \<FF>) x = connected_component (to_graph \<FF>) y"
          using 01 02 cards_same_cond
           connected_components_member_eq[of x' "(to_graph \<FF>)" xx] 
           in_connected_componentI[of "(to_graph \<FF>)" xx x'] 
           connected_components_member_eq[of y' "(to_graph \<FF>)" yy]
           in_connected_componentI[of "(to_graph \<FF>)" yy y']
          by(cases "cardx \<le> cardy") (auto simp add: xx_def yy_def xy_def)
        thus False
          by (simp add: "1100" x_def y_def)
     qed
     have comps_inter_empt:"connected_component (to_graph \<FF>) y' \<inter> connected_component (to_graph \<FF>) x' = {}" 
       using "01" "02" "1100" x_def xx_def xy_def  y_def yy_def cards_same_cond
             connected_components_member_eq[of y' "(to_graph \<FF>)" yy, 
                                   OF in_connected_componentI[of "(to_graph \<FF>)" yy y']]  
             connected_components_member_eq[of x' "(to_graph \<FF>)" xx,
                    OF in_connected_componentI[of "(to_graph \<FF>)" xx x']]
       apply(intro unequal_components_disjoint[where X=UNIV])
       by(cases "cardx \<le> cardy") (auto simp add: xx_def yy_def xy_def)
     have comp_y_y':"connected_component (insert {fst e, snd e} (to_graph \<FF>)) y' =
          connected_component (insert {fst e, snd e} (to_graph \<FF>)) y"
      apply(subst connected_components_member_eq[ of y' "(to_graph \<FF>')" yy, simplified F_rewrite])
       using "02" in_connected_componentI[of "(to_graph \<FF>')" yy y']
                  reachable_subset[of "(to_graph \<FF>)" yy y' "(to_graph \<FF>')"]
                  in_connected_componentI2[of yy y' "(to_graph \<FF>')"]
                new_edge_disjoint_components[of x y "(to_graph \<FF>)"]  x_def xy_def y_def yy_def
        F_rewrite 
       by (fastforce, auto)
     have reps_inxx_yy_comps: "x' \<in> connected_component (to_graph \<FF>) xx"
                              "y' \<in> connected_component (to_graph \<FF>) yy"
        using "01" in_connected_componentI[of "(to_graph \<FF>)" xx x']
             in_own_connected_component[of x' "(to_graph \<FF>)"]
             "02" in_connected_componentI[of "(to_graph \<FF>)" yy y']
             in_own_connected_component[of y' "(to_graph \<FF>)"]
        by auto
     have comps_union:"connected_component (to_graph \<FF>') y' =
                      connected_component (to_graph \<FF>) y' \<union> connected_component (to_graph \<FF>) x'"
     proof(subst connected_components_member_eq[OF reps_inxx_yy_comps(1)],
          subst connected_components_member_eq[OF reps_inxx_yy_comps(2)], 
          rule trans[of _ "connected_component (insert {fst e, snd e} (to_graph \<FF>)) y"], goal_cases)
       case 1
      show ?case
        using F_rewrite comp_y_y' by auto
    next
      case 2
      show ?case
      by(intro trans[OF sym[OF insert_edge_endpoints_same_component[of
                                "(insert {fst e, snd e} (to_graph \<FF>))" _ x "(to_graph \<FF>)"]]])
         (auto split: if_split simp add: insert_commute x_def y_def  xx_def xy_def yy_def  )
  qed
     note concretization_of_F' = res_edges_new_forest_are
     have consist_to_rdg':"consist (digraph_abs \<FF>') (abstract_conv_map to_rdg')"
       using invar_aux_pres_one_step[OF assms(2,1,3), simplified state'_is[symmetric]]
       by(auto elim!: invar_aux6E''  aux_invarE simp add: state'_def)
    have axioms_conds1: "x' \<in> Vs (to_graph \<FF>')" 
      using comps_union in_connected_component_in_edges[of x' "(to_graph \<FF>')" y']
             x'_not_y' in_own_connected_component[of x' "(to_graph \<FF>)"]
      by simp
    have axioms_conds2: "Vs (to_graph \<FF>') \<subseteq> \<V> " 
       using invar_aux_pres_one_step[OF assms(2,1,3), simplified state'_is[symmetric]]
       by(auto elim!:  aux_invarE invar_aux15E simp add: state'_def)
     have axioms_conds3: "graph_invar (to_graph \<FF>')"
       using invar_aux_pres_one_step[OF assms(2,1,3), simplified state'_is[symmetric]] 
             validFD[of state'] 
       by(auto elim!: aux_invarE invar_aux14E simp add: state'_def)
     have good_graphF': "good_graph_invar \<FF>'"
       using invar_aux_pres_one_step[OF assms(2,1,3), simplified state'_is[symmetric]] 
       by(auto elim!: aux_invarE invar_aux18E'' simp add: state'_def)
     obtain qqq_u where qqq_prop_u:"walk_betw (to_graph  \<FF>') x' qqq_u y'"
    using comps_union connected_components_member_sym[of x' "to_graph \<FF>'" y'] 
          axioms_conds1 axioms_conds2 axioms_conds3
           in_connected_componentE[of y' "to_graph  \<FF>'" x']
            in_connected_componentI2[of x' x' "to_graph \<FF>"]  x'_not_y' 
    by(auto intro: in_connected_component_has_walk)
  have symmetric_F': "symmetric_digraph (digraph_abs \<FF>')" 
       using invar_aux_pres_one_step[OF assms(2,1,3), simplified state'_is[symmetric]] 
       by(auto elim!: aux_invarE invar_aux20E simp add: state'_def)
  obtain qqq where qqq_prop:"vwalk_bet (digraph_abs  \<FF>') x' qqq y'"
    using symmetric_digraph_walk_betw_vwalk_bet symmetric_F' qqq_prop_u 
    by(force simp add: to_graph_def) 
  have finiteF: "finite (to_graph \<FF>')" 
    using \<FF>'_def axioms_conds3 graph_abs.finite_E graph_abs.intro by auto
  note x'_inVs = axioms_conds1
  have distinctQ: "distinct Q" and vwalk_bet_Q: "vwalk_bet [\<FF>']\<^sub>g x' Q y'"
     using qqq_prop x'_inVs x'_not_y'  good_graphF'
     by (auto intro!: get_path_axioms_unfolded[of \<FF>' x' qqq y']  Q_def )
   hence vwalk_bet_rev_Q: "vwalk_bet [\<FF>']\<^sub>g y' (rev Q) x'"
     by (simp add: symmetric_F' symmetric_digraph_vwalk_bet_vwalk_bet)
   have oedge_of_Q:"oedge ` List.set (to_redge_path to_rdg' Q) = 
          oedge ` abstract_conv_map to_rdg' ` (List.set (edges_of_vwalk Q))"
     using consist_to_rdg' distinctQ oedge_of_to_redgepath_subset by auto
    have redge_of_Q:"List.set (to_redge_path to_rdg' Q) \<subseteq> 
          abstract_conv_map to_rdg' ` (List.set (edges_of_vwalk Q))"
      using consist_to_rdg' distinctQ to_redgepath_subset by blast
    have redge_of_Q_rev:"List.set (to_redge_path to_rdg' (rev Q)) \<subseteq> 
          abstract_conv_map to_rdg' ` (List.set (edges_of_vwalk (rev Q)))"
      using consist_to_rdg' distinctQ to_redgepath_subset by simp
    have edges_of_Q_in_F': "set (edges_of_vwalk Q) \<subseteq> [\<FF>']\<^sub>g" and
          edges_of_Q_rev_in_F': "set (edges_of_vwalk (rev Q)) \<subseteq> [\<FF>']\<^sub>g" 
      using vwalk_bet_Q  vwalk_bet_rev_Q by(auto intro!: vwalk_bet_edges_in_edges)
    hence swap_edges_of_Q_in_F': "prod.swap ` set (edges_of_vwalk Q) \<subseteq> [\<FF>']\<^sub>g"
       and swap_edges_of_rev_Q_in_F': "prod.swap ` set (edges_of_vwalk (rev Q)) \<subseteq> [\<FF>']\<^sub>g"
      using symmetric_digraphD[OF symmetric_F'] by auto
    have oedge_of_Q_rev: "oedge ` List.set (to_redge_path to_rdg' (rev Q)) = 
          oedge ` abstract_conv_map to_rdg' ` (List.set (edges_of_vwalk Q))"
      using oedge_of_to_redgepath_subset[of Q "digraph_abs \<FF>'" to_rdg'] consist_to_rdg' distinctQ
            oedge_of_to_redge_path_rev[of Q "digraph_abs \<FF>'" to_rdg'] edges_of_Q_in_F'
            swap_edges_of_Q_in_F' 
      by simp
    have Q_redges_in_F:"set (to_redge_path to_rdg' Q) \<subseteq> \<F>_redges state'" 
      using redge_of_Q  edges_of_Q_in_F' by(auto simp add: state'_def F_def F_redges_def)
    hence  Q_oedges_in_E:"set (map oedge (to_redge_path to_rdg' Q)) \<subseteq> \<E>" 
      using invar_aux_pres_one_step[OF assms(2,1,3), simplified state'_is[symmetric]] 
      by(auto elim!: invar_aux3E[OF invar_aux3_from_aux_invar] 
           simp add: state'_def  image_subset_iff F_def F_redges_def)
    have Q_rev_redges_in_F:"set (to_redge_path to_rdg' (rev Q)) \<subseteq> \<F>_redges state'" 
      using redge_of_Q_rev  edges_of_Q_rev_in_F' by(auto simp add: state'_def F_def F_redges_def)
    hence  Q_rev_oedges_in_E:"set (map oedge (to_redge_path to_rdg' (rev Q))) \<subseteq> \<E>" 
      using invar_aux_pres_one_step[OF assms(2,1,3), simplified state'_is[symmetric]] 
      by(auto elim!: invar_aux3E[OF invar_aux3_from_aux_invar] 
           simp add: state'_def  image_subset_iff F_def F_redges_def)
    have f'_is:
   "abstract_flow_map (augment_edges_impl f (abstract_bal_map b x') (to_redge_path to_rdg' Q)) =
    augment_edges (abstract_flow_map f) (abstract_bal_map b x') (to_redge_path to_rdg' Q)"
   "abstract_flow_map (augment_edges_impl f (- abstract_bal_map b x') (to_redge_path to_rdg' (rev Q))) =
    augment_edges (abstract_flow_map f) (- abstract_bal_map b x') (to_redge_path to_rdg' (rev Q))"
      using Q_oedges_in_E assms(3) Q_rev_oedges_in_E
      by (auto intro:  augment_edges_homo simp add: f_def)
    have flow_change_in_Q:"abstract_flow_map f' d \<noteq> abstract_flow_map f d \<Longrightarrow> d \<in> 
             oedge ` abstract_conv_map to_rdg' ` (List.set (edges_of_vwalk Q))" for d
      unfolding f'_def
      using e_not_in_es_flow_not_change[of "(to_redge_path to_rdg' Q)" d "abstract_flow_map f" "abstract_bal_map b x'"]
            e_not_in_es_flow_not_change[of "(to_redge_path to_rdg' (rev Q))" d  "abstract_flow_map f" "- abstract_bal_map b x'"]
            oedge_of_Q oedge_of_Q_rev  f'_is 
      by(cases "0 < abstract_bal_map b x'") auto
   
    have Q_subset_F':"List.set Q \<subseteq> connected_component (to_graph \<FF>') y'"
    proof(subst sym[OF connected_components_member_eq[of x' "to_graph \<FF>'" y']], goal_cases)
      case 1
      then show ?case 
      using comps_union in_own_connected_component[of _ "to_graph \<FF>"] 
            by simp
  next
    case 2
    show ?case
      using symmetric_digraph_vwalk_betw_walk_betw[OF symmetric_F'  vwalk_bet_Q] 
      by (auto intro!: walk_betw_subset_conn_comp simp add:  to_graph_def)
  qed
  have dVs_Q:"dVs (to_vertex_pair ` abstract_conv_map to_rdg' ` 
               (List.set (edges_of_vwalk Q))) \<subseteq> List.set Q"
    using consist_dVs_path consist_to_rdg' distinctQ edges_of_Q_in_F' by blast
            
  hence f_change_comp_y':"abstract_flow_map f' d \<noteq> abstract_flow_map f d
                  \<Longrightarrow> fst d \<in> connected_component (to_graph \<FF>') y'" for d
  proof(goal_cases)
    case 1
    then obtain v1 v2 where v1v2: "d = oedge ( abstract_conv_map to_rdg' (v1, v2))"
                            "(v1, v2) \<in> set (edges_of_vwalk Q)" 
      using flow_change_in_Q[of d] by auto
    moreover hence "(v1, v2) \<in> [\<FF>']\<^sub>g"
      using edges_of_Q_in_F' by blast
    moreover have "F d = abstract_conv_map to_rdg' (v1, v2) \<or> 
                     B d = abstract_conv_map to_rdg' (v1, v2)"
      by (metis oedge.elims v1v2(1))
   ultimately have "{fst d, snd d} = {v1, v2}"
     using  consist_to_rdg' make_pair' by(fastforce elim!: consistE ) 
   moreover have "{v1, v2} \<in> set( edges_of_path Q)"
     using graph_abs.not_in_edges_of_path_not_in_edges_of_vwalk[OF graph_abs.intro[OF axioms_conds3] , 
            of v2]  v1v2(2)
     by (auto simp add: insert_commute)
   ultimately have "fst d \<in> set Q"
    using  v_in_edge_in_path_gen[of  "{fst d, snd d}" Q "fst d"]
    by auto
      thus ?case 
     using Q_subset_F' by auto
 qed     
   have 144:"connected_component (to_graph \<FF>) v \<subseteq> connected_component (to_graph \<FF>') v" for v
     by (simp add: F_rewrite con_comp_subset subset_insertI)
    have 154:"v \<in> \<V> \<Longrightarrow> connected_component (to_graph \<FF>') v \<subseteq> \<V>" for v
      using axioms_conds2 in_connected_component_in_edges[of _ _ v]
      by auto
    have 157:"v \<in> \<V> \<Longrightarrow> connected_component (to_graph \<FF>) v \<subseteq> \<V>" for v 
      using "144" "154" by blast
    have 155: "card (connected_component (to_graph \<FF>) y') \<ge> card (connected_component (to_graph \<FF>) x')"
      using cards_same_cond  connected_components_member_eq[of x' _ ]
            connected_components_member_eq[of y'] reps_inxx_yy_comps(1,2) 
      by(auto simp add: xx_def xy_def yy_def cardx_def cardy_def)
    have Q_inF':"(List.set (edges_of_path Q)) \<subseteq>  (to_graph \<FF>')" 
      using directed_edges_subset_undirected_edges_subset[OF edges_of_Q_rev_in_F']          
      by(auto simp add: edges_of_path_rev[symmetric]  to_graph_def)    
      have x'_y'_reachable:"reachable (to_graph \<FF>') x' y'"
        by (meson qqq_prop_u reachableI)
    have lengthQ:"length Q \<ge> 2" 
      using vwalk_bet_Q x'_not_y' by(auto intro:  vwalk_bet_diff_verts_length_geq_2)  
    have b'_is: "abstract_bal_map (move_balance b x' y') =
                  (\<lambda>v. if v = x' then 0
                       else if v = y' then abstract_bal_map b y' + abstract_bal_map b x' 
                       else abstract_bal_map b v)"
      using assms(3) 
      by(auto simp add: b_def intro:  abstract_bal_map_homo[OF _ refl, of b x' y'])
    have finite_old_comps:"finite (connected_component (to_graph \<FF>) y')"
         "finite (connected_component (to_graph \<FF>) x')"
      using "157" \<V>_finite x'_y'_in_V by (auto intro:  finite_subset)
    have old_comps_disjnt:"disjnt (connected_component (to_graph \<FF>) y') (connected_component (to_graph \<FF>) x')"
      by (simp add: comps_inter_empt disjnt_def)
    note aux_invar_state' = invar_aux_pres_one_step[of state, OF assms(2,1,3), 
                           simplified sym[OF state_state']]
  show "thr \<ge> 0  \<Longrightarrow> invarA_1 thr state \<Longrightarrow> invarA_1 thr (maintain_forest_upd state)"
  proof-
    assume asm: "thr \<ge> 0"  "invarA_1 thr state"
    have bx':"\<bar>abstract_bal_map b x' \<bar> \<le> thr*card (connected_component (to_graph \<FF>) x')"
      using asm(2) b_def invarA_1_def local.\<FF>_def x'_y'_in_V(1) by blast
    have by':"\<bar>abstract_bal_map b y' \<bar> \<le> thr*card (connected_component (to_graph \<FF>) y')"
      using asm(2) b_def invarA_1_def local.\<FF>_def x'_y'_in_V(2) by blast
    have y'_card:"\<bar>abstract_bal_map b' y'\<bar> \<le> thr * card (connected_component (to_graph \<FF>') y')"
      apply(subst comps_union, subst card_Un_disjnt)
      using comps_inter_empt x'_not_y' bx' by' comps_inter_empt assms(2)  \<V>_finite
            finite_subset  x'_y'_in_V
      by(auto simp add: algebra_simps card_Un_disjnt disjnt_def  b'_def  \<FF>'_def \<FF>_def b'_is 
                 elim!: aux_invarE invar_aux10E)
    moreover have 16:"v \<in> \<V> \<Longrightarrow> v \<noteq> x'  \<Longrightarrow> v \<noteq> y' \<Longrightarrow>
                \<bar>abstract_bal_map b' v \<bar>\<le> thr * card (connected_component (to_graph \<FF>') v)" for v
    proof(rule order.trans[of _ "thr * real (card (connected_component (to_graph \<FF>) v))"], goal_cases)
      case 1
      then show ?case 
        using invarA_1D[OF asm(2), of v] \<V>_finite b'_is
        by(auto simp add: b_def local.\<FF>_def b'_def) 
    next
      case 2
      thus ?case
        using 144[of v] 154[of v] asm(1) \<V>_finite 
              card_mono[of "connected_component (to_graph \<FF>') v" "connected_component (to_graph \<FF>) v"] rev_finite_subset
        by (intro mult_left_mono, auto intro: mult_left_mono)
    qed
    ultimately show "invarA_1 thr (maintain_forest_upd state)"
      using  asm(1) b'_is[simplified b'_def [symmetric]]
      by(auto intro!: invarA_1I simp add: 10[symmetric] state'_def)
  qed
     
  show "thr2 \<ge> 0  \<Longrightarrow>invarA_1 thr2 state \<Longrightarrow> invarA_2 thr1 thr2 state \<Longrightarrow>
        thr2 \<le> 2 * current_\<gamma> state \<Longrightarrow> thr1 \<le> 8*real N * current_\<gamma> state
               \<Longrightarrow>invarA_2 thr1 thr2 (maintain_forest_upd state)"    
    proof-
      assume asm: "thr2 \<ge> 0"  "invarA_1 thr2 state" "invarA_2 thr1 thr2 state"
                  "thr2 \<le> 2 * current_\<gamma> state" "thr1 \<le> 8*real N * current_\<gamma> state"
    show " invarA_2 thr1 thr2 (maintain_forest_upd state)"
    proof-
      have "d \<in> abstract_conv_map to_rdg' ` (digraph_abs \<FF>') \<Longrightarrow>
         thr1 - thr2 * real (card (connected_component (to_graph \<FF>') (fst (oedge d)))) <
            abstract_flow_map f' (oedge d)" for d
      proof-
      assume asm2:"d \<in> abstract_conv_map to_rdg' ` (digraph_abs \<FF>')"
      hence "d \<in> \<EE>" 
        using  eeinfracE res_edges_new_forest_are
        by (auto  intro: invar_aux2E[OF all_invars(2)] simp add: to_rdg_def  local.\<FF>_def)
      hence fstdV:"fst (oedge d) \<in> \<V>" 
        using dVsI'(1)[of ] o_edge_res make_pair[OF refl refl]  fst_E_V by presburger
      hence compd:"connected_component (to_graph \<FF>') (fst (oedge d)) \<subseteq> \<V>"
        using "154" by blast
      hence finite_compd:"finite (connected_component (to_graph \<FF>') (fst (oedge d)) )" 
        using \<V>_finite finite_subset by blast
       have d_prop:"d \<in>  abstract_conv_map to_rdg ` (digraph_abs \<FF>) \<or> oedge d = e"
         using asm2 res_edges_new_forest_are by auto
       show "thr1 - thr2 * real (card (connected_component (to_graph \<FF>') (fst (oedge d)))) 
                < abstract_flow_map f' (oedge d)"
      proof(cases "abstract_flow_map f (oedge d) = abstract_flow_map f' (oedge d)")
        case True
       have "d \<in>  abstract_conv_map to_rdg ` (digraph_abs \<FF>) \<Longrightarrow> 
             thr1 - thr2 * real (card (connected_component (to_graph \<FF>) (fst (oedge d)))) <
                abstract_flow_map f (oedge d)"
         using asm(3)  
         by (auto elim: invarA_2E simp add: f_def  local.\<FF>_def to_rdg_def F_def F_redges_def)
        moreover have "oedge d = e \<Longrightarrow> abstract_flow_map f (oedge d) > thr1" 
          using \<gamma>_def asm(5) e_prop by auto
        moreover have "card (connected_component (to_graph \<FF>) (fst (oedge d))) \<le> 
             card (connected_component (to_graph \<FF>') (fst (oedge d)))"
          using  finite_compd con_comp_subset[of "to_graph \<FF>" "to_graph \<FF>'"]  
          by(auto intro!: card_mono simp add: F_rewrite)
        ultimately show ?thesis 
          using asm finite_compd d_prop True F_rewrite \<FF>_def \<FF>'_def 
          by (smt (verit, best) True mult_nonneg_nonneg of_nat_0_le_iff of_nat_le_iff 
              ordered_comm_semiring_class.comm_mult_left_mono)
      next
        case False
        hence 101:"fst (oedge d) \<in> connected_component (to_graph \<FF>') y'" 
           using f_change_comp_y' by simp
        hence 102:"fst (oedge d) \<in> connected_component (to_graph \<FF>) y' \<or>
               fst (oedge d) \<in> connected_component (to_graph \<FF>) x'" 
          by (simp add: comps_union)
        hence 106: "connected_component (to_graph \<FF>') (fst (oedge d)) =
                     connected_component (to_graph \<FF>') y'"
          using 101 by (auto intro!: connected_components_member_eq)
        have 107: "connected_component (to_graph \<FF>) (fst (oedge d)) =
                                            connected_component (to_graph \<FF>) y'  \<or>
                   connected_component (to_graph \<FF>) (fst (oedge d)) = 
                                            connected_component (to_graph \<FF>) x'" 
          using 102 by (auto intro!: connected_components_member_eq)
        have 103:"\<bar>abstract_bal_map b x'\<bar>  \<le>
                      thr2 * real (card (connected_component (to_graph \<FF>) x'))"
          using  invarA_1D[OF asm(2)] x'_y'_in_V(1) 
          by(auto simp add: local.\<FF>_def  b_def)
        have 110:"abstract_flow_map f' (oedge d)  \<ge> abstract_flow_map f (oedge d) - \<bar>abstract_bal_map b x' \<bar>"
          using distinct_path_augment[of "to_redge_path to_rdg' Q" " \<bar>abstract_bal_map b x' \<bar>"
                                              "abstract_flow_map f" "oedge d"]
                 distinct_path_augment[of "to_redge_path to_rdg' (rev Q)" " \<bar>abstract_bal_map b x' \<bar>"
                                              "abstract_flow_map f" "oedge d"]
                 distinctQ edges_of_Q_in_F'  edges_of_Q_rev_in_F'  to_rdg_distinct[OF consist_to_rdg']
          by (auto split: if_split simp add: f'_is f'_def)
        show ?thesis 
        proof(unfold 106 comps_union card_Un_disjnt[OF  finite_old_comps old_comps_disjnt],
              rule orE'[OF d_prop], goal_cases)
          case 1
          hence 109:"abstract_flow_map f (oedge d) > 
                 thr1 - thr2 * real (card (connected_component (to_graph \<FF>) (fst (oedge d))))"
            using  asm(3) 
            by (auto simp add: f_def invarA_2D local.\<FF>_def to_rdg_def F_def F_redges_def)
          show ?case 
            apply(cases rule: orE[OF 107])
            subgoal
              using 103 110 109           
              apply(auto simp add: algebra_simps)
              done
            subgoal 
              apply(rule order.strict_trans2[of _ "abstract_flow_map f (oedge d) - \<bar>abstract_bal_map b x'\<bar>", OF  _ 110])
              apply(rule order.strict_trans1[of _ "thr1 -
                        thr2 * real (card (connected_component (to_graph \<FF>) (fst (oedge d)))) 
                                 - \<bar>abstract_bal_map b x' \<bar>"])              
              using 103 109 155 asm(1)
              apply (smt (verit, best) distrib_left mult_left_mono of_nat_add real_mono)
              using 103 109  asm(1) by simp
            done
        next
          case 2
          have strict_non_strict_mono: "(a::real) < b \<Longrightarrow> c \<ge> d \<Longrightarrow> a -c < b -d" for a b c d by simp
          show ?case 
            using 144[of x'] 144[of y'] e_prop asm 2 103 
                  finite_subset[of "connected_component (to_graph \<FF>) _"] 
                  finite_subset[of "connected_component (to_graph \<FF>') _"] 
              by (auto intro!: order.strict_trans2[OF _ 110]  strict_non_strict_mono 
                     simp add: add_increasing distrib_left \<gamma>_def )
        qed
      qed
    qed
    thus ?thesis 
      by(auto simp add: sym[OF state_state'] state'_def F_def F_redges_def intro!: invarA_2I)
  qed
  qed

  have "is_Opt (\<b> - abstract_bal_map b') (abstract_flow_map f')"
    if asm: "invar_gamma state" "thr2 \<ge> 0" "invarA_1 thr2 state" "invarA_2 thr1 thr2 state"
        "thr2 \<le> 2 * current_\<gamma> state" "thr1 = 8*real N * current_\<gamma> state" 
        "is_Opt (\<b> - (abstract_bal_map b)) (abstract_flow_map f)"
  proof-
    from asm have \<gamma>_geq_0: "\<gamma> \<ge> 0" unfolding invar_gamma_def \<gamma>_def by auto
    have d_oedge_inE:
     "d \<in> abstract_conv_map to_rdg ` (digraph_abs \<FF> - {(fst e, snd e), (fst e, snd e)}) \<Longrightarrow>
                 oedge d \<in> \<E>" for d 
      using all_invars(2) o_edge_res  by (auto elim!: invar_aux2E simp add: local.\<FF>_def to_rdg_def)
    hence d_oedge_V:"d \<in> abstract_conv_map to_rdg ` (digraph_abs \<FF> - {(fst e, snd e), (fst e, snd e)}) \<Longrightarrow>
              fst (oedge d) \<in> \<V>" for d 
      using fst_E_V by presburger
    have d_oedge_card:"d \<in>  abstract_conv_map to_rdg ` (digraph_abs \<FF> - {(fst e, snd e), (fst e, snd e)}) \<Longrightarrow>
         card (connected_component (to_graph \<FF>) (fst (oedge d))) \<le> N"for d 
      using  d_oedge_V[of d]  \<V>_finite "157" card_mono 
      by (force simp add: N_def)
     have d_oedge_inE':
     "d \<in> abstract_conv_map to_rdg ` (digraph_abs \<FF>) \<Longrightarrow>
                 oedge d \<in> \<E>" for d 
      using all_invars(2) o_edge_res  by (auto elim!: invar_aux2E simp add: local.\<FF>_def to_rdg_def)
    hence d_oedge_V':"d \<in> abstract_conv_map to_rdg ` (digraph_abs \<FF>) \<Longrightarrow>
              fst (oedge d) \<in> \<V>" for d 
      using fst_E_V by presburger
    have d_oedge_card':"d \<in>  abstract_conv_map to_rdg ` (digraph_abs \<FF>) \<Longrightarrow>
         card (connected_component (to_graph \<FF>) (fst (oedge d))) \<le> N"for d 
      using  d_oedge_V'[of d]  \<V>_finite "157" card_mono 
      by (force simp add: N_def)
    have d_inF'_rcap:" rcap (abstract_flow_map f) d > 6 * N * \<gamma>" if
                   asmy:"d \<in> abstract_conv_map to_rdg' ` (digraph_abs \<FF>')" for d
    proof-
      have "d = F e \<Longrightarrow> ereal (6 * real N * \<gamma>) < \<uu>\<^bsub>abstract_flow_map f\<^esub>d"
        using asmy  infinite_u[of e] e_prop  assms(2) by auto
      moreover have "d = B e \<Longrightarrow> ereal (6 * real N * \<gamma>) < \<uu>\<^bsub>abstract_flow_map f\<^esub>d"
        apply(insert e_prop) 
        apply(rule Orderings.xt1(1)[of _  "ereal (abstract_flow_map f _)"])
        using rcap.simps(2)[of "abstract_flow_map f" ] apply simp
        apply(subst less_ereal.simps(1))
        apply(rule order.strict_trans[of _ "(8 * real N * \<gamma>)"]) 
        using asm(1) V_non_empt \<V>_finite 
        by(auto intro:  order.strict_trans[of _ "(8 * real N * \<gamma>)"] mult_less_le_imp_less simp add: invar_gamma_def \<gamma>_def N_def)
      moreover have "ereal (6 * real N * \<gamma>) < \<uu>\<^bsub>abstract_flow_map f\<^esub>d"
        if asm1: "d \<in> abstract_conv_map to_rdg ` [\<FF>]\<^sub>g"
        using asmy 
      proof(cases rule: oedge.cases[of d])
        case (1 e)
        then show ?thesis 
        using d_oedge_card[of d] infinite_u[of "oedge d"]  asm(4)  asm(5) by auto
      next
        case (2 e)
        have "ereal (6 * real N * \<gamma>) \<le> ereal
        (8 * real (card \<V>) * current_\<gamma> state -
         thr2 * real (card (connected_component (to_graph \<FF>) (fst (oedge d)))))"
          using d_oedge_card'[of d] asm(2,5) asm1 
          by(auto intro: mult_mono simp add:  \<gamma>_def N_def semiring_normalization_rules(18) )
        moreover have "ereal (8 * real (card \<V>) * current_\<gamma> state -
            thr2 * real (card (connected_component (to_graph \<FF>) (fst (oedge d)))))
             < ereal (abstract_flow_map f (oedge d))"
          using   asm1  asm(4) 
          by (force simp add: invarA_2_def  f_def asm(6) N_def  to_rdg_def  \<FF>_def F_def F_redges_def)
        moreover have "ereal (abstract_flow_map f (oedge d)) \<le> \<uu>\<^bsub>abstract_flow_map f\<^esub>d"
          using 2 by simp
        ultimately show ?thesis 
          by(auto intro: order.strict_trans2[of _ "ereal (abstract_flow_map f (oedge d))"])
      qed
      ultimately show ?thesis
        using asmy  concretization_of_F' by auto
    qed

    have revQ_subs:"List.set (to_redge_path to_rdg' (rev Q)) \<subseteq> 
                    abstract_conv_map to_rdg' ` (digraph_abs \<FF>')"
      using edges_of_Q_rev_in_F'  redge_of_Q_rev by force
    have Q_subs:"List.set (to_redge_path to_rdg' Q) \<subseteq> 
             abstract_conv_map to_rdg' ` (digraph_abs \<FF>')"
      using edges_of_Q_in_F' image_mono redge_of_Q by fastforce
    have to_rdg_rev_Q_non_empt:"List.set (to_redge_path to_rdg' (rev Q)) \<noteq> {}"
      using lengthQ by (simp add: proper_path_some_redges)

    have Rcap_rev_Q:"ereal \<bar>abstract_bal_map b x'\<bar> <
                 Rcap (abstract_flow_map f) (List.set (to_redge_path to_rdg' (rev Q)))"
    proof(rule Rcap_strictI, goal_cases)
      case 1
      then show ?case by blast
    next
      case 2
      thus ?case
        using to_rdg_rev_Q_non_empt by simp
    next
      case (3 d)
      have "ereal \<bar>abstract_bal_map b x'\<bar> \<le> ereal (thr2 * real (card (connected_component (to_graph \<FF>) x')))"
        using b_def ereal_less_eq(3) invarA_1D local.\<FF>_def that(3) x'_y'_in_V(1) by blast
      moreover have " ereal (thr2 * real (card (connected_component (to_graph \<FF>) x')))
                     \<le> ereal (real (6 * N) * current_\<gamma> state)"
        apply(subst ereal_less_eq(3))
        apply(rule order_trans[of _ "2 * current_\<gamma> state * N"])
        using  157[of x']  \<gamma>_geq_0 
        by(auto intro: mult_mono 
             simp add: \<gamma>_def "157" N_def \<V>_finite card_mono mult_mono' that(2,5) x'_y'_in_V(1) )
      moreover have "ereal (real (6 * N) * current_\<gamma> state) < \<uu>\<^bsub>abstract_flow_map f\<^esub>d"
         using  d_inF'_rcap[of d] revQ_subs 3
         by(auto simp add:   \<gamma>_def) 
       ultimately show ?case by order
     qed
    have to_rdg_Q_non_empt: "List.set (to_redge_path to_rdg' Q) \<noteq> {}"
        using lengthQ
        by (simp add: proper_path_some_redges)

    have Rcap_Q:"ereal \<bar>abstract_bal_map b x'\<bar> < Rcap (abstract_flow_map f) (List.set (to_redge_path to_rdg' Q))"
    proof(rule Rcap_strictI, goal_cases)
      case 1
      show ?case by blast
    next
      case 2
      show ?case 
        using to_rdg_Q_non_empt by simp
    next
      case (3 d)
      have "ereal \<bar>abstract_bal_map b x'\<bar> \<le>
                ereal (thr2 * real (card (connected_component (to_graph \<FF>) x')))"
        using asm(3) x'_y'_in_V(1)
        by(auto elim!: invarA_1E simp add:  b_def  \<FF>_def)
      moreover have "ereal (thr2 * real (card (connected_component (to_graph \<FF>) x')))
                    \<le> ereal (real (6 * N) * current_\<gamma> state)"
       apply(subst ereal_less_eq(3))
       apply(rule order_trans[of _ "2 * current_\<gamma> state * N"])
       using asm(5)  157[of x'] x'_y'_in_V(1) \<gamma>_geq_0 N_def \<V>_finite card_mono[of  \<V>]
       by(auto intro: mult_mono simp add: invarA_1_def b_def  \<FF>_def \<gamma>_def)
     moreover have "ereal (real (6 * N) * current_\<gamma> state) < \<uu>\<^bsub>abstract_flow_map f\<^esub>d"
       using  d_inF'_rcap[of d] Q_subs 3
       by(auto simp add:\<gamma>_def)
     ultimately show ?case by order
   qed
  have to_redg'_def': "to_rdg' = conv_to_rdg state'"
    unfolding state'_def by simp
  have walk_betwQ: "walk_betw (to_graph \<FF>') x' Q y'" 
    by (simp add: symmetric_F' symmetric_digraph_vwalk_betw_walk_betw to_graph_def vwalk_bet_Q)
  hence walk_betwQ_rev: "walk_betw (to_graph \<FF>') y' (rev Q) x'"
    by (simp add: walk_symmetric)
  have hd_rev_Q:"hd (rev Q) = y'"
    by(auto intro!: walk_between_nonempty_pathD(3)[of "to_graph \<FF>'" y' "rev Q" x'] 
                    walk_betwQ walk_symmetric)
  have last_rev_Q:"last (rev Q) = x'"
    by(auto intro!: walk_between_nonempty_pathD(4)[of "to_graph \<FF>'" y' "rev Q" x'] 
                    walk_betwQ walk_symmetric)
  have hd_Q:"hd Q = x'"
    by(auto intro!: walk_between_nonempty_pathD(3)[of "to_graph \<FF>'" x' Q y']  walk_betwQ)
  have last_Q:"last Q = y'"
    by(auto intro!: walk_between_nonempty_pathD(4)[of "to_graph \<FF>'" x' Q  y']  walk_betwQ)
  have C_Q_rev_Q:"\<CC> (to_redge_path to_rdg' Q) = - \<CC> (to_redge_path to_rdg' (rev Q))"
    using to_redge_path_costs[of "digraph_abs \<FF>'" to_rdg' Q, OF consist_to_rdg' lengthQ distinctQ]
          to_rdg_distinct[of  "digraph_abs \<FF>'" to_rdg' Q, OF consist_to_rdg' distinctQ]
          to_rdg_distinct[of  "digraph_abs \<FF>'" to_rdg' "rev Q", OF consist_to_rdg', 
                      simplified distinct_rev[of Q], OF distinctQ] distinct_sum2[of _ \<cc>] 
    by (simp add: \<CC>_def  edges_of_Q_in_F' edges_of_Q_rev_in_F' symmetric_F' symmetric_digraphD)
  hence a1:"ereal (- abstract_bal_map b x') \<le>
                   Rcap (abstract_flow_map f) (List.set (to_redge_path to_rdg' (rev Q)))"
      using Rcap_rev_Q  ereal_less_le linorder_le_less_linear not_less_iff_gr_or_eq by fastforce
    have a2: "augpath (abstract_flow_map f) (to_redge_path to_rdg' (rev Q))"
    proof(rule augpathI, goal_cases)
      case 1
      then show ?case 
         unfolding to_redg'_def'
         using aux_invar_state' walk_betwQ_rev lengthQ  
         by(fastforce intro!:  perpath_to_redgepath simp add: state'_def invar_aux6_from_aux_invar invar_aux20_from_aux_invar)
     next
       case 2
       show ?case  using Rcap_rev_Q abs_ereal_pos[of "abstract_bal_map b x'"]
              order.strict_trans1[of 0 "\<bar>ereal (abstract_bal_map b x')\<bar>"]
         by auto
     qed
      have a3: "List.set (to_redge_path to_rdg' (rev Q)) \<subseteq> \<EE>"
        using aux_invar_state' Q_rev_redges_in_F assms(3) from_aux_invar'(2)
        by(auto simp add: F_def F_redges_def)
      have a4: "distinct (to_redge_path to_rdg' (rev Q))"
        using consist_to_rdg' distinctQ
        by (simp add: edges_of_Q_rev_in_F' to_rdg_distinct)
      have a5:"fstv (hd (to_redge_path to_rdg' (rev Q))) = y'"
        using consist_to_rdg'  lengthQ hd_rev_Q
        by (simp add: edges_of_Q_rev_in_F' to_rdg_hd)
      have a6: "sndv (last (to_redge_path to_rdg' (rev Q))) = x'"
        using consist_to_rdg'  lengthQ last_rev_Q
        by (simp add: edges_of_Q_rev_in_F' to_rdg_last)

      hence b1:"ereal (abstract_bal_map b x') \<le>
                Rcap (abstract_flow_map f) (List.set (to_redge_path to_rdg' Q))"
        using Rcap_Q by (simp add: ereal_less_le order_less_imp_le)
      have b2: "augpath (abstract_flow_map f) (to_redge_path to_rdg' Q)"
    proof(rule augpathI, goal_cases)
      case 1
      then show ?case 
         unfolding to_redg'_def'
         using aux_invar_state' walk_betwQ lengthQ  
         by(fastforce intro!:  perpath_to_redgepath simp add: state'_def invar_aux6_from_aux_invar invar_aux20_from_aux_invar)
     next
       case 2
       show ?case  using Rcap_Q abs_ereal_pos[of "abstract_bal_map b x'"]
              order.strict_trans1[of 0 "\<bar>ereal (abstract_bal_map b x')\<bar>"]
         by auto
     qed
     have b3: "List.set (to_redge_path to_rdg'  Q) \<subseteq> \<EE>"
       using Q_oedges_in_E o_edge_res by auto
     have b4: "distinct (to_redge_path to_rdg' Q)"
       using consist_to_rdg' distinctQ edges_of_Q_in_F' to_rdg_distinct by auto
      have b5:"fstv (hd (to_redge_path to_rdg' Q)) = x'"
        using consist_to_rdg'  lengthQ hd_Q
        by (simp add: edges_of_Q_in_F' to_rdg_hd)
      have b6: "sndv (last (to_redge_path to_rdg' Q)) = y'"
        using consist_to_rdg'  lengthQ last_Q
        by (simp add: edges_of_Q_in_F' to_rdg_last)
      have is_s_t_path_rev_Q: "is_s_t_path (abstract_flow_map f) y' x' (to_redge_path to_rdg' (rev Q))"
        using a2 a3 a4 a5 a6 by (auto intro: is_s_t_pathI)
      have is_s_t_path_Q: "is_s_t_path (abstract_flow_map f) x' y' (to_redge_path to_rdg' Q)"        using b2 b3 b4 b5 b6 by (auto intro: is_s_t_pathI)

    show "is_Opt (\<b> - abstract_bal_map b') (abstract_flow_map f')" 
    unfolding f'_def
    apply(cases "0 < abstract_bal_map b x'", subst if_P, simp_all)
  proof( goal_cases)
    case 2
    note 1 = 2
      have min_path:"is_min_path (abstract_flow_map f) y' x' (to_redge_path to_rdg' (rev Q))"
      proof(rule is_min_pathI, goal_cases)
        case 1
        then show ?case
          using is_s_t_path_rev_Q by force
      next
        case (2 P')
          note P'_asm = this
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
                    is_s_t_path_Q markers_removeQ augpath_to_hpath_CC[of "(abstract_flow_map f)"]
                     augpath_to_hpath_PP[of "(abstract_flow_map f)"]
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
            have Rcap_pos:"Rcap (abstract_flow_map f) (List.set C) > 0"
              using is_s_t_path_Q  C_prop  P'_asm is_s_t_path_Q sym[OF all_props(5)]
              unfolding augcycle_def augpath_def precycle_def is_s_t_path_def prepath_def \<CC>_def
              by (intro Rcap_subset[of "List.set P'' \<union> \<Union> {List.set D |D. D \<in> List.set CCC}" "List.set C"], 
                auto intro: Rcap_union[of "List.set (to_redge_path to_rdg' Q)" "List.set P'"])
            have "augcycle (abstract_flow_map f) C"
              using C_prop all_props P'_asm is_s_t_path_Q Rcap_pos
              by (auto simp add: augcycle_def augpath_def precycle_def is_s_t_path_def)
            thus False using asm(7) min_cost_flow_no_augcycle by simp
          qed
        qed     
        have "is_Opt (\<b> - abstract_bal_map b') (abstract_flow_map f')"
        using x'_not_y'  asm(7)  a1  min_path  a5 a6 1 
        by (auto intro!: path_aug_opt_pres[of y' x' "\<b> - abstract_bal_map b"
                          "(abstract_flow_map f)"  ] 
               simp add: b'_def f'_def b'_is f'_is)
      thus ?case using 1 by(simp add: f'_def)
    next
      case 1
      note 2 = 1

      have min_path:"is_min_path (abstract_flow_map f) x' y' (to_redge_path to_rdg' Q)"
      proof(rule is_min_pathI, goal_cases)
        case 1
        then show ?case
          by (simp add: is_s_t_path_Q)
      next
        case (2 P')
          note P'_asm = this
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
                    is_s_t_path_Q markers_removeQ augpath_to_hpath_CC[of "(abstract_flow_map f)"]
                     augpath_to_hpath_PP[of "(abstract_flow_map f)"]
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
            have Rcap_pos:"Rcap (abstract_flow_map f) (List.set C) > 0"
              using is_s_t_path_rev_Q  C_prop  P'_asm is_s_t_path_Q sym[OF all_props(5)]
              unfolding augcycle_def augpath_def precycle_def is_s_t_path_def prepath_def \<CC>_def
              by (intro Rcap_subset[of "List.set P'' \<union> \<Union> {List.set D |D. D \<in> List.set CCC}" "List.set C"], 
                    auto intro: Rcap_union[of "List.set (to_redge_path to_rdg' (rev Q))" "List.set P'"])
            have "augcycle (abstract_flow_map f) C"
              using C_prop all_props P'_asm is_s_t_path_rev_Q Rcap_pos
              by (auto simp add:  augcycle_def augpath_def precycle_def is_s_t_path_def)
            thus False using asm(7) min_cost_flow_no_augcycle by simp
          qed
        qed     
      have "is_Opt (\<b> - abstract_bal_map b') (abstract_flow_map f')"
        using x'_not_y'  asm(7)  b1  min_path  x'_not_y' b5 b6 2
        by (auto intro!: path_aug_opt_pres[of x' y' "\<b> - abstract_bal_map b" "(abstract_flow_map f)" ]
                    simp add: b'_def f'_def f'_is b'_is)     
      thus ?case
        using 2 by (simp add: f'_def)
   qed
 qed
  thus "invar_gamma state \<Longrightarrow> thr2 \<ge> 0  \<Longrightarrow>invarA_1 thr2 state \<Longrightarrow> invarA_2 thr1 thr2 state \<Longrightarrow>
         thr2 \<le> 2 * current_\<gamma> state \<Longrightarrow> thr1 = 8*real N * current_\<gamma> state \<Longrightarrow>
         invar_isOptflow state \<Longrightarrow> invar_isOptflow (maintain_forest_upd state)"
    using sym[OF state_state']
    by(simp add: invar_isOptflow_def state'_def f_def b_def)

  have flow_domain: "set (map oedge (to_redge_path to_rdg' Q)) \<subseteq> flow_domain f"
                    "set (map oedge (to_redge_path to_rdg' (rev Q))) \<subseteq> flow_domain f"
    using  Q_oedges_in_E   Q_rev_oedges_in_E implementation_invar_partialE(2)[OF assms(3)]
        implementation_invar_partial_props(1)[OF assms(3)] f_def
    by fastforce+
  have flow_invar_f: "flow_invar f"
    using assms(3) f_def by blast
  have bal_invar_b: "bal_invar b"
    using assms(3) b_def by force
  show "implementation_invar (maintain_forest_upd state)"
    unfolding 10[symmetric]
  proof(rule implementation_invarI)

  have "\<E> = flow_domain f'"
    using   oedge_of_to_redge_path_rev[OF distinctQ consist_to_rdg'] 
          Q_oedges_in_E Q_rev_oedges_in_E  
        augment_edges_impl_domain[OF flow_domain(1) flow_invar_f]
        augment_edges_impl_domain[OF flow_domain(2) flow_invar_f]
        implementation_invar_partialE(2)[OF assms(3) flow_invar_f]
        implementation_invar_partial_props(1)[OF assms(3)]
    by (auto simp add:  f_def f'_def)
  thus " \<E> = flow_domain (current_flow state')"
    by(auto simp add: state'_def)
  show "\<V> = bal_domain (balance state')"
    using assms(3) x'_y'_in_V(1,2)  abstract_bal_map_domain_exact[OF bal_invar_b refl]
    by (auto simp add: state'_def b'_def  b_def)
  show "flow_invar  (current_flow state')"
    using Q_oedges_in_E Q_rev_oedges_in_E assms(3) 
    by (auto simp add: f'_def f_def state'_def)
  show "bal_invar (balance state')" 
    using abstract_bal_invar[OF bal_invar_b refl]
    by(auto simp add:  state'_def b'_def)
  show "[Algo_state.\<FF> state']\<^sub>g = conv_domain (conv_to_rdg state')"
    using F'_digraph_abs_is assms(3) 
    by (auto simp add: state'_def  implementation_invar_def local.\<FF>_def to_rdg'_def to_rdg_def x_def y_def)
  show "conv_invar (conv_to_rdg state')"
    using abstract_conv_invar assms(3) 
    by (auto simp add: state'_def to_rdg'_def to_rdg_def)
  note  rep_comp_upd_all(1,3,4)[simp]
  show "\<V> = rep_comp_domain (rep_comp_card state')"
    using assms(3)  rep_comp_invar_r_card 
    by (force simp add: r_card'_def r_card_def state'_def)
  show "rep_comp_invar (rep_comp_card state')"
    by (simp add: state'_def r_card'_def rep_comp_invar_r_card)
  note  not_blocked_upd_all(1,3,4)[simp]
  show "not_blocked_invar (not_blocked state')"
    by (simp add: state'_def nb'_def not_blocked_invar_nb)
  show "\<E> = not_blocked_dom (not_blocked state')"
    using assms(3)  
    by (force simp add: state'_def implementation_invar_def nb'_def nb_def) 
 qed 
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
          "aux_invar state" "implementation_invar state"
  shows "invar_gamma state \<Longrightarrow> \<Phi> (maintain_forest_upd state) \<le> \<Phi> state + 1" 
        "\<F>_redges state \<subseteq> \<F>_redges(maintain_forest_upd state)"
        "card (comps \<V> (to_graph (\<FF> (maintain_forest_upd state)))) +1 =
          card (comps \<V> (to_graph (\<FF> state)))"
        "invar_gamma state \<Longrightarrow> \<Phi> (maintain_forest_upd state) \<le>
                                  \<Phi> state + (card (comps \<V> (to_graph (\<FF> state)))) - 
                            (card (comps \<V> (to_graph (\<FF> (maintain_forest_upd state)))))"
        "\<And> d. d \<in> (UNIV -  \<F>(maintain_forest_upd state))  \<Longrightarrow>
               a_current_flow (maintain_forest_upd state) d =  a_current_flow state d"
        "to_graph (\<FF> (maintain_forest_upd state)) \<supset> to_graph (\<FF> state)"
        "\<exists> e . e \<in> to_set (actives state) \<and> 8 * real N * current_\<gamma> state < a_current_flow state e 
               \<and> connected_component (to_graph (\<FF>  state)) (fst e)
              \<subset> connected_component (to_graph (\<FF> (maintain_forest_upd state))) (fst e)"
proof-
  have all_invars: "invar_aux1 state" "invar_aux2 state" "invar_aux3 state" "invar_aux4 state"
                   "invar_aux6 state" "invar_aux8 state" "invar_aux7 state" "invar_aux9 state "
                   "invar_aux5 state" "invar_aux10 state" "invar_aux11 state" "invar_aux12 state"
                   "invar_aux13 state" "invar_aux16 state" "invar_aux17 state" "invar_aux18 state"
                    "invar_aux20 state" "invar_aux14 state"
                   "invar_aux22 state"
    using assms by(auto simp add: aux_invar_def)
  define  \<FF> where  "\<FF> = Algo_state.\<FF> state"
  define f where "f = current_flow state"
  define b where "b = balance state"
  define r_card where "r_card = rep_comp_card state"
  define E' where "E' = actives state"
  define to_rdg where "to_rdg = conv_to_rdg state"
  define \<gamma> where "\<gamma> = current_\<gamma> state"
  define e where "e = the( get_from_set 
                            (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E')"
  define x where "x = fst e"
  define y where "y = snd e"
  define to_rdg' where "to_rdg' = add_direction to_rdg x y e"
  define cardx where "cardx = abstract_comp_map r_card x"
  define cardy where "cardy = abstract_comp_map r_card y"
  define xy where " xy = (if cardx \<le> cardy then (x,y) else (y,x))"
  define xx where "xx = prod.fst xy"
  define yy where "yy = prod.snd xy"
  define \<FF>' where "\<FF>' =insert_undirected_edge (fst e) (snd e) \<FF>"
  define x' where "x' = abstract_rep_map r_card xx" 
  define y' where "y' = abstract_rep_map r_card yy"
  define Q where "Q = get_path x' y' \<FF>'"
  define f' where  "f' = (if abstract_bal_map b x' > 0 
                                   then augment_edges_impl f (abstract_bal_map b x') (to_redge_path to_rdg' Q) 
                                   else augment_edges_impl f (- abstract_bal_map b x') (to_redge_path to_rdg' (itrev Q)))"
  define b' where "b' = move_balance b x' y'"
  define E'' where "E'' = filter (\<lambda> d. 
{abstract_rep_map r_card (fst d) , abstract_rep_map r_card (snd d) } \<noteq> {x', y'} ) E'"
  define r_card' where "r_card' = rep_comp_upd_all 
                                (\<lambda> u urc. if prod.fst (urc) = x' \<or> prod.fst (urc) = y'
                                    then (y', cardx + cardy) else urc) r_card"
  define nb where "nb = not_blocked state"
  define nb' where "nb' = not_blocked_upd_all (\<lambda> d b. 
                                   if d =  e then True
                                   else if {abstract_rep_map r_card (fst d) , abstract_rep_map r_card (snd d) } = {x', y'} 
                                   then False
                                   else b) nb"
  define state' where "state' = state 
              \<lparr>  \<FF> := \<FF>', current_flow := f',
                balance := b',
                actives := E'', conv_to_rdg := to_rdg', 
                rep_comp_card := r_card',
                not_blocked := nb'\<rparr>"

  note defs_impl = state'_def \<FF>'_def e_def \<gamma>_def E'_def
              f_def \<FF>_def f'_def b_def x'_def r_card'_def r_card_def
              xx_def xy_def  x_def y_def b'_def Q_def cardx_def cardy_def
              to_rdg'_def y'_def to_rdg_def yy_def E''_def nb_def
              nb'_def

   have state'_is: "state' = maintain_forest_upd state"
    apply(rule Algo_state.equality)
    by (auto intro!: cong[OF cong, OF refl, of _ _ _ _ rep_comp_upd_all] ext 
          simp add: maintain_forest_upd_def Let_def defs_impl)
  note 10= state'_is
  have set_invar_E'[simp]: "set_invar E'"
    using E'_def all_invars(15) invar_aux17_def by blast
  have E'_substE:"to_set E' \<subseteq> \<E>"
    using all_invars(1) by(simp add: E'_def invar_aux1_def)
  have e_prop: "e \<in> to_set E'" "abstract_flow_map f e > 8 * real N *\<gamma>"
                "get_from_set (\<lambda> e. abstract_flow_map f e > 8 * real N *\<gamma>) E' = Some e"
    apply(all \<open>rule maintain_forest_call_condE[OF assms(1)]\<close>)
    using set_get(2,3)[OF set_invar_E'] 
    by(auto simp add: f_def e_def \<gamma>_def E'_def)
  have fste_V[simp]: "fst e \<in> \<V>" 
    using E'_substE dVsI'(1) e_prop make_pair[OF refl refl] by auto 
  have snde_V[simp]: "snd e \<in> \<V>"
    using E'_substE dVsI'(2) e_prop make_pair[OF refl refl] by auto
  have e_in_E'[simp]:"e \<in> to_set E'"
    using e_prop by simp
  have x_not_y: "fst e \<noteq> snd e" 
    using all_invars(11)  e_in_E' 
    by(force simp add: invar_aux11_def E'_def )
  have good_graphF: "good_graph_invar \<FF>"
    using all_invars(16) invar_aux18_def local.\<FF>_def by force
  have F'_digraph_abs_is:"[\<FF>']\<^sub>g = [\<FF>]\<^sub>g \<union> {(fst e, snd e), (snd e, fst e)}"
    using good_graphF by (auto simp add: \<FF>'_def good_graph_invar_def)
  hence F'_to_graph_is:"to_graph \<FF>' = to_graph \<FF> \<union> {{fst e, snd e}}"
    by (auto simp add: to_graph'_def)
  hence F_rewrite:"to_graph \<FF>' = Set.insert {fst e, snd e} (to_graph \<FF>)"
    by simp
  have to_rdg'_is: "abstract_conv_map to_rdg' = 
      (\<lambda>d. if d = (x, y) then F e else if d = (y, x) then B e else abstract_conv_map to_rdg d)"
    using assms(3) 
    by(subst to_rdg'_def  add_direction_result)+
      (auto simp add: add_direction_result to_rdg_def)
  have forest_edges_neq_e:"{a, b} \<in> to_graph \<FF> \<Longrightarrow> {a, b} \<noteq> {x, y}" for a b
    using  assms(2) e_in_E' from_aux_invar'(11)  mk_disjoint_insert
        new_edge_disjoint_components[OF refl refl refl]
    by(fastforce simp add: x_def y_def local.\<FF>_def E'_def)
  hence dir_forest_edges_neq_e:"(a, b) \<in> digraph_abs \<FF> \<Longrightarrow> (a, b) \<noteq> (x, y)" 
                               "(a, b) \<in> digraph_abs \<FF> \<Longrightarrow> (a, b) \<noteq> (y, x)" for a b
    by(auto simp add: to_graph'_def)
  have res_edges_new_forest_are:"abstract_conv_map to_rdg' ` [\<FF>']\<^sub>g  
         = {F e, B e} \<union> abstract_conv_map to_rdg ` [\<FF>]\<^sub>g"
    using x_not_y dir_forest_edges_neq_e 
    by((subst to_rdg'_is  F'_digraph_abs_is)+)
      (auto simp add:  \<FF>'_def to_rdg'_def to_rdg_def \<FF>_def x_def y_def)
  have 114: "{x', y'} = {abstract_rep_map r_card (fst e), abstract_rep_map r_card (snd e)}"
    by(auto simp add: x'_def y'_def xx_def yy_def xy_def x_def y_def)
  have reachable_in_forest_fst_in_V:"reachable (to_graph \<FF>) a b \<Longrightarrow> a \<in> \<V>" for a b 
    using assms(2) from_aux_invar'(15) local.\<FF>_def reachable_to_Vs(1) by blast
    have x'_y'_in_V:"x' \<in> \<V>"  "y' \<in> \<V>" 
      using "114"  from_aux_invar'(9)[OF assms(2)] fste_V snde_V
      by(auto simp add: r_card_def doubleton_eq_iff)
    have new_balance_is: "a_balance state' = (\<lambda>v. if v = x' then 0
          else if v = y' then abstract_bal_map b y' + abstract_bal_map b x'
               else abstract_bal_map b v)"
      using assms(3)
      by(auto simp add:state'_def b'_def  abstract_bal_map_homo[OF  _  refl] b_def)
    note state_state' = state'_is
  have 01:"reachable (to_graph \<FF>) xx x' \<or> xx = x'"
    by (simp add: assms(2) from_aux_invar'(8) local.\<FF>_def r_card_def x'_def)
  have 02:"reachable (to_graph \<FF>) yy y' \<or> yy = y'"
    by (simp add: assms(2) from_aux_invar'(8) local.\<FF>_def r_card_def y'_def)
  hence 1100:"connected_component (to_graph \<FF>) (fst e) \<noteq> connected_component (to_graph \<FF>) (snd e)"
    using e_prop assms(2)
    by(simp add: invar_aux11_def aux_invar_def  \<FF>'_def E'_def \<FF>_def)
  have fst_snd_e_neq: "fst e \<noteq> snd e"
    using  1100 by auto
    have asm': "invar_aux11 state" using assms  aux_invar_def by auto

    have cards_same_cond: "card (connected_component (to_graph \<FF>) x)
                           \<le> card (connected_component (to_graph \<FF>) y) \<longleftrightarrow>
                          abstract_comp_map r_card x \<le> abstract_comp_map r_card y" 
      using "01" "02"  invar_aux16D[OF all_invars(14), of x]
            invar_aux16D[OF all_invars(14), of y]
            reachable_in_forest_fst_in_V x'_y'_in_V(1,2)
      by(cases "cardx \<le> cardy") (auto simp add: xx_def xy_def yy_def  local.\<FF>_def r_card_def)
    have x'_not_y':"x' \<noteq> y'" 
      proof
        assume " x' = y'"
        hence "connected_component (to_graph \<FF>) x = connected_component (to_graph \<FF>) y"
          using 01 02 cards_same_cond
           connected_components_member_eq[of x' "(to_graph \<FF>)" xx] 
           in_connected_componentI[of "(to_graph \<FF>)" xx x'] 
           connected_components_member_eq[of y' "(to_graph \<FF>)" yy]
           in_connected_componentI[of "(to_graph \<FF>)" yy y']
          by(cases "cardx \<le> cardy") (auto simp add: xx_def yy_def xy_def)
        thus False
          by (simp add: "1100" x_def y_def)
      qed
     have comp_y_y':"connected_component (insert {fst e, snd e} (to_graph \<FF>)) y' =
          connected_component (insert {fst e, snd e} (to_graph \<FF>)) y"
      apply(subst connected_components_member_eq[ of y' "(to_graph \<FF>')" yy, simplified F_rewrite])
       using "02" in_connected_componentI[of "(to_graph \<FF>')" yy y']
                  reachable_subset[of "(to_graph \<FF>)" yy y' "(to_graph \<FF>')"]
                  in_connected_componentI2[of yy y' "(to_graph \<FF>')"]
                new_edge_disjoint_components[of x y "(to_graph \<FF>)"]  x_def xy_def y_def yy_def
        F_rewrite 
       by (fastforce, auto)
     have reps_inxx_yy_comps: "x' \<in> connected_component (to_graph \<FF>) xx"
                              "y' \<in> connected_component (to_graph \<FF>) yy"
        using "01" in_connected_componentI[of "(to_graph \<FF>)" xx x']
             in_own_connected_component[of x' "(to_graph \<FF>)"]
             "02" in_connected_componentI[of "(to_graph \<FF>)" yy y']
             in_own_connected_component[of y' "(to_graph \<FF>)"]
        by auto
     have comps_union:"connected_component (to_graph \<FF>') y' =
                      connected_component (to_graph \<FF>) y' \<union> connected_component (to_graph \<FF>) x'"
     proof(subst connected_components_member_eq[OF reps_inxx_yy_comps(1)],
          subst connected_components_member_eq[OF reps_inxx_yy_comps(2)], 
          rule trans[of _ "connected_component (insert {fst e, snd e} (to_graph \<FF>)) y"], goal_cases)
       case 1
      show ?case
        using F_rewrite comp_y_y' by auto
    next
      case 2
      show ?case
      by(intro trans[OF sym[OF insert_edge_endpoints_same_component[of
                                "(insert {fst e, snd e} (to_graph \<FF>))" _ x "(to_graph \<FF>)"]]])
         (auto split: if_split simp add: insert_commute x_def y_def  xx_def xy_def yy_def  )
  qed
     note concretization_of_F' = res_edges_new_forest_are
     have consist_to_rdg':"consist (digraph_abs \<FF>') (abstract_conv_map to_rdg')"
       using invar_aux_pres_one_step[OF assms(2,1,3), simplified state'_is[symmetric]]
       by(auto elim!: invar_aux6E''  aux_invarE simp add: state'_def)
    have axioms_conds1: "x' \<in> Vs (to_graph \<FF>')" 
      using comps_union in_connected_component_in_edges[of x' "(to_graph \<FF>')" y']
             x'_not_y' in_own_connected_component[of x' "(to_graph \<FF>)"]
      by simp
    have axioms_conds2: "Vs (to_graph \<FF>') \<subseteq> \<V> " 
       using invar_aux_pres_one_step[OF assms(2,1,3), simplified state'_is[symmetric]]
       by(auto elim!:  aux_invarE invar_aux15E simp add: state'_def)
     have axioms_conds3: "graph_invar (to_graph \<FF>')"
       using invar_aux_pres_one_step[OF assms(2,1,3), simplified state'_is[symmetric]] 
             validFD[of state'] 
       by(auto elim!: aux_invarE invar_aux14E simp add: state'_def)
     have good_graphF': "good_graph_invar \<FF>'"
       using invar_aux_pres_one_step[OF assms(2,1,3), simplified state'_is[symmetric]] 
       by(auto elim!: aux_invarE invar_aux18E'' simp add: state'_def)
     obtain qqq_u where qqq_prop_u:"walk_betw (to_graph  \<FF>') x' qqq_u y'"
    using comps_union connected_components_member_sym[of x' "to_graph \<FF>'" y'] 
          axioms_conds1 axioms_conds2 axioms_conds3
           in_connected_componentE[of y' "to_graph  \<FF>'" x']
            in_connected_componentI2[of x' x' "to_graph \<FF>"]  x'_not_y' 
    by(auto intro: in_connected_component_has_walk)
  have symmetric_F': "symmetric_digraph (digraph_abs \<FF>')" 
       using invar_aux_pres_one_step[OF assms(2,1,3), simplified state'_is[symmetric]] 
       by(auto elim!: aux_invarE invar_aux20E simp add: state'_def)
  obtain qqq where qqq_prop:"vwalk_bet (digraph_abs  \<FF>') x' qqq y'"
    using symmetric_digraph_walk_betw_vwalk_bet symmetric_F' qqq_prop_u 
    by(force simp add: to_graph_def) 
  note x'_inVs = axioms_conds1
  have distinctQ: "distinct Q" and vwalk_bet_Q: "vwalk_bet [\<FF>']\<^sub>g x' Q y'"
     using qqq_prop x'_inVs x'_not_y'  good_graphF'
     by (auto intro!: get_path_axioms_unfolded[of \<FF>' x' qqq y']  Q_def )
   hence vwalk_bet_rev_Q: "vwalk_bet [\<FF>']\<^sub>g y' (rev Q) x'"
     by (simp add: symmetric_F' symmetric_digraph_vwalk_bet_vwalk_bet)
   have oedge_of_Q:"oedge ` List.set (to_redge_path to_rdg' Q) = 
          oedge ` abstract_conv_map to_rdg' ` (List.set (edges_of_vwalk Q))"
     using consist_to_rdg' distinctQ oedge_of_to_redgepath_subset by auto
    have redge_of_Q:"List.set (to_redge_path to_rdg' Q) \<subseteq> 
          abstract_conv_map to_rdg' ` (List.set (edges_of_vwalk Q))"
      using consist_to_rdg' distinctQ to_redgepath_subset by blast
    have redge_of_Q_rev:"List.set (to_redge_path to_rdg' (rev Q)) \<subseteq> 
          abstract_conv_map to_rdg' ` (List.set (edges_of_vwalk (rev Q)))"
      using consist_to_rdg' distinctQ to_redgepath_subset by simp
    have edges_of_Q_in_F': "set (edges_of_vwalk Q) \<subseteq> [\<FF>']\<^sub>g" and
          edges_of_Q_rev_in_F': "set (edges_of_vwalk (rev Q)) \<subseteq> [\<FF>']\<^sub>g" 
      using vwalk_bet_Q  vwalk_bet_rev_Q by(auto intro!: vwalk_bet_edges_in_edges)
    hence swap_edges_of_Q_in_F': "prod.swap ` set (edges_of_vwalk Q) \<subseteq> [\<FF>']\<^sub>g"
       and swap_edges_of_rev_Q_in_F': "prod.swap ` set (edges_of_vwalk (rev Q)) \<subseteq> [\<FF>']\<^sub>g"
      using symmetric_digraphD[OF symmetric_F'] by auto
    have oedge_of_Q_rev: "oedge ` List.set (to_redge_path to_rdg' (rev Q)) = 
          oedge ` abstract_conv_map to_rdg' ` (List.set (edges_of_vwalk Q))"
      using oedge_of_to_redgepath_subset[of Q "digraph_abs \<FF>'" to_rdg'] consist_to_rdg' distinctQ
            oedge_of_to_redge_path_rev[of Q "digraph_abs \<FF>'" to_rdg'] edges_of_Q_in_F'
            swap_edges_of_Q_in_F' 
      by simp
    have Q_redges_in_F:"set (to_redge_path to_rdg' Q) \<subseteq> \<F>_redges state'" 
      using redge_of_Q  edges_of_Q_in_F' by(auto simp add: state'_def F_def F_redges_def)
    hence  Q_oedges_in_E:"set (map oedge (to_redge_path to_rdg' Q)) \<subseteq> \<E>" 
      using invar_aux_pres_one_step[OF assms(2,1,3), simplified state'_is[symmetric]] 
      by(auto elim!: invar_aux3E[OF invar_aux3_from_aux_invar] 
           simp add: state'_def  image_subset_iff F_def F_redges_def)
    have Q_rev_redges_in_F:"set (to_redge_path to_rdg' (rev Q)) \<subseteq> \<F>_redges state'" 
      using redge_of_Q_rev  edges_of_Q_rev_in_F' by(auto simp add: state'_def F_def F_redges_def)
    hence  Q_rev_oedges_in_E:"set (map oedge (to_redge_path to_rdg' (rev Q))) \<subseteq> \<E>" 
      using invar_aux_pres_one_step[OF assms(2,1,3), simplified state'_is[symmetric]] 
      by(auto elim!: invar_aux3E[OF invar_aux3_from_aux_invar] 
           simp add: state'_def  image_subset_iff F_def F_redges_def)
    have f'_is:
   "abstract_flow_map (augment_edges_impl f (abstract_bal_map b x') (to_redge_path to_rdg' Q)) =
    augment_edges (abstract_flow_map f) (abstract_bal_map b x') (to_redge_path to_rdg' Q)"
   "abstract_flow_map (augment_edges_impl f (- abstract_bal_map b x') (to_redge_path to_rdg' (rev Q))) =
    augment_edges (abstract_flow_map f) (- abstract_bal_map b x') (to_redge_path to_rdg' (rev Q))"
      using Q_oedges_in_E assms(3) Q_rev_oedges_in_E
      by (auto intro:  augment_edges_homo simp add: f_def)
    have flow_change_in_Q:"abstract_flow_map f' d \<noteq> abstract_flow_map f d \<Longrightarrow> d \<in> 
             oedge ` abstract_conv_map to_rdg' ` (List.set (edges_of_vwalk Q))" for d
      unfolding f'_def
      using e_not_in_es_flow_not_change[of "(to_redge_path to_rdg' Q)" d "abstract_flow_map f" "abstract_bal_map b x'"]
            e_not_in_es_flow_not_change[of "(to_redge_path to_rdg' (rev Q))" d  "abstract_flow_map f" "- abstract_bal_map b x'"]
            oedge_of_Q oedge_of_Q_rev  f'_is 
      by(cases "0 < abstract_bal_map b x'") auto
   

    have Q_inF':"(List.set (edges_of_path Q)) \<subseteq>  (to_graph \<FF>')" 
      using directed_edges_subset_undirected_edges_subset[OF edges_of_Q_rev_in_F']          
      by(auto simp add: edges_of_path_rev[symmetric]  to_graph_def)    
      have x'_y'_reachable:"reachable (to_graph \<FF>') x' y'"
        by (meson qqq_prop_u reachableI)

  show goal3:" invar_gamma state \<Longrightarrow> \<Phi> (maintain_forest_upd state) \<le> \<Phi> state + 1"
  proof-
    assume invar_gamma_asm: "invar_gamma state "
    have invar6_asm: "invar_aux11 state"
      by (simp add: asm')
    have 10:"\<Phi> state = 
          (\<Sum> v \<in>  \<V> - {x', y'}. \<lceil> \<bar> a_balance state v\<bar> / (current_\<gamma> state) - (1 - \<epsilon>)\<rceil>) +
          \<lceil> \<bar> a_balance state x'\<bar> / (current_\<gamma> state) - (1 - \<epsilon>)\<rceil> + 
          \<lceil> \<bar> a_balance state y'\<bar> / (current_\<gamma> state) - (1 - \<epsilon>)\<rceil>"
      using x'_y'_in_V \<V>_finite x'_not_y' 
      by(auto  intro: sum_except_two simp add: \<Phi>_def)
    have 11:"(\<Sum> v \<in>  \<V> - {x', y'}. \<lceil> \<bar> a_balance state v\<bar> / (current_\<gamma> state) - (1 - \<epsilon>)\<rceil>) = 
          (\<Sum> v \<in>  \<V> - {x', y'}. \<lceil> \<bar> a_balance state' v\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>)"
      using new_balance_is
      by(simp add: state'_def b'_def b_def new_balance_is)
     have 12:"\<Phi> state' = 
          (\<Sum> v \<in>  \<V> - {x', y'}. \<lceil> \<bar> a_balance state' v\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>) +
          \<lceil> \<bar> a_balance state' x'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil> + 
          \<lceil> \<bar> a_balance state' y'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>"
      using  x'_y'_in_V \<V>_finite x'_not_y' 
      by (auto intro: sum_except_two simp add: \<Phi>_def)
    have "\<lceil> \<bar> a_balance state' x'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil> + 
          \<lceil> \<bar> a_balance state' y'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil> = 
         \<lceil> 0 - (1 - \<epsilon>)\<rceil> + 
          \<lceil> \<bar> a_balance state' y'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>"
      using new_balance_is
      by (simp add: state'_def b'_def)
    also have "... = \<lceil> \<bar> a_balance state' y'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>"
      using \<epsilon>_axiom by linarith
    also have "... = \<lceil> \<bar> abstract_bal_map b y' + abstract_bal_map b x'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>"
      using x'_not_y' new_balance_is  by (simp add: state'_def b'_def)
    also have "...  \<le>  \<lceil> (\<bar> abstract_bal_map b y' \<bar> + \<bar> abstract_bal_map b x'\<bar>) / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>"
      using invar_gamma_asm
      by (auto elim!: invar_gammaE intro!: ceiling_mono divide_right_mono simp add:  state'_def )
    also have "... = \<lceil> \<bar> abstract_bal_map b y' \<bar> / (current_\<gamma> state')  + (\<bar> abstract_bal_map b x'\<bar>/ (current_\<gamma> state')- (1 - \<epsilon>))\<rceil>"
      by argo
    also  have "... \<le> \<lceil> \<bar> abstract_bal_map b y' \<bar> / (current_\<gamma> state')\<rceil>
                      + \<lceil> \<bar> abstract_bal_map b x'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>"
      by(auto intro:  ceiling_add_le)
    also have "... \<le> \<lceil> \<bar> abstract_bal_map b y' \<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil> + 1
                      + \<lceil> \<bar> abstract_bal_map b x'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil>"
      using \<epsilon>_axiom by linarith
    finally have ineq:"\<lceil> \<bar> a_balance state' x'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil> + 
          \<lceil> \<bar> a_balance state' y'\<bar> / (current_\<gamma> state') - (1 - \<epsilon>)\<rceil> \<le>
           \<lceil> \<bar> a_balance state y' \<bar> / (current_\<gamma> state) - (1 - \<epsilon>)\<rceil> + 1
                      + \<lceil> \<bar> a_balance state x'\<bar> / (current_\<gamma> state) - (1 - \<epsilon>)\<rceil>"
      unfolding state'_def b_def by simp
    show "\<Phi> (maintain_forest_upd state) \<le> \<Phi> state + 1"
      using sym[OF state_state'] ineq by (auto simp add: 10 11 12)
  qed
   show goal4:"card (comps \<V> (to_graph (Algo_state.\<FF> (maintain_forest_upd state)))) +1 = 
                                   card (comps \<V> (to_graph (Algo_state.\<FF> state))) "
    proof-
      have invar6_asm:"invar_aux11 state"
        using assms(2) by (simp add: aux_invar_def invar_aux11_def)
      show "card (comps \<V> (to_graph (Algo_state.\<FF> (maintain_forest_upd state)))) +1 = 
                   card (comps \<V> (to_graph (Algo_state.\<FF> state)))"
        using  sym[OF state_state'] 1100 invar6_asm fste_V snde_V  \<V>_finite assms(2)  F_rewrite 
       by (auto intro: card_decrease_component_join[simplified]
             simp add: state'_def  \<FF>'_def \<FF>_def aux_invar_def invar_aux5_def) 
   qed
    show "invar_gamma state \<Longrightarrow> \<Phi> (maintain_forest_upd state) \<le> \<Phi> state +
                 (card (comps \<V> (to_graph (Algo_state.\<FF> state)))) - 
                 (card (comps \<V> (to_graph (Algo_state.\<FF> (maintain_forest_upd state)))))"
    proof-
      assume invar6_asm: "invar_gamma state"   
      have invar6_asm':"invar_aux11 state"
        using assms(2) by (simp add:  aux_invar_def invar_aux11_def)   
      moreover have "connected_component (to_graph \<FF>) (fst e) \<in> 
               (comps \<V> (to_graph (Algo_state.\<FF> state)))"
        using fste_V by (simp add: comps_def \<FF>_def)
      moreover have "connected_component (to_graph \<FF>) (snd e) \<in> 
                (comps \<V> (to_graph (Algo_state.\<FF> state)))"
        using snde_V by (simp add: comps_def \<FF>_def)
      ultimately show " \<Phi> (maintain_forest_upd state) \<le> 
             \<Phi> state + card (comps \<V> (to_graph (Algo_state.\<FF> state))) 
                  - card (comps \<V> (to_graph (Algo_state.\<FF> (maintain_forest_upd state))))"       
      using goal4 goal3 invar6_asm
      by simp
  qed
  have same_flow:"\<And> d.  d \<in> (UNIV -  oedge ` (abstract_conv_map to_rdg') ` (digraph_abs \<FF>' ))
                 \<Longrightarrow> abstract_flow_map f' d =  abstract_flow_map f d"
  proof(goal_cases)
    case (1 d)
    note asm = this
    hence d_not_F':"d \<notin> oedge ` (abstract_conv_map to_rdg') ` (digraph_abs \<FF>' )" by auto
    show "abstract_flow_map f' d = abstract_flow_map f d"
    proof(rule ccontr)
      assume "abstract_flow_map f' d \<noteq> abstract_flow_map f d"
      hence "d \<in> oedge ` (abstract_conv_map to_rdg') ` (List.set (edges_of_vwalk Q))"
        using flow_change_in_Q by simp
      thus False 
        using d_not_F' Q_inF' edges_of_Q_in_F' by blast
    qed
  qed
  thus "\<And> d. d \<in> UNIV - \<F> (maintain_forest_upd state) \<Longrightarrow>
         a_current_flow (maintain_forest_upd state) d = a_current_flow state d"
    apply(subst sym[OF state_state'])+
    apply(subst (asm) sym[OF state_state'])+
    by(simp add: F_rewrite state'_def f_def \<FF>'_def \<FF>_def F_def F_redges_def)

  show "\<F>_redges state \<subseteq> \<F>_redges (maintain_forest_upd state)"
    apply(subst sym[OF state_state']|subst state'_def)+
    using "1100" new_edge_disjoint_components[of "fst e" "snd e"]  
    by(auto simp add: concretization_of_F'[simplified sym[OF F_rewrite]] 
                      to_rdg_def \<FF>_def F_rewrite F_def F_redges_def)
  show "to_graph (Algo_state.\<FF> state) \<subset> to_graph (Algo_state.\<FF> (maintain_forest_upd state))"
    using "1100" same_component_after_insert[OF fste_V snde_V refl, of "to_graph \<FF>"]
    by(auto simp add: F'_to_graph_is 10[symmetric] \<FF>_def[symmetric]  state'_def )

  show "\<exists>e. e \<in> to_set (actives state) \<and>
        8 * real N * current_\<gamma> state < a_current_flow state e \<and>
        connected_component (to_graph (Algo_state.\<FF>  state)) (fst e)
        \<subset> connected_component (to_graph (Algo_state.\<FF> (maintain_forest_upd state))) (fst e)"
    using E'_def  \<gamma>_def e_prop f_def F_rewrite sym[OF state_state']  1100  
          connected_components_member_eq[of "snd e"  "to_graph (Algo_state.\<FF> state)" "fst e"] 
          insert_edge_endpoints_same_component[OF reflexive, of "to_graph (Algo_state.\<FF> state)" "fst e" "snd e"]
          in_connected_componentI2[OF refl, of "snd e" "to_graph (Algo_state.\<FF> state)"] 
    by (intro  exI[of _ e]) (auto simp add: \<FF>_def \<FF>'_def state'_def)
qed

lemma maintain_forest_invar_aux_pres:
  assumes "maintain_forest_dom state"
          "aux_invar state" "implementation_invar state"
  shows   "aux_invar (maintain_forest state)"
  using assms(2-) 
proof(induction rule: maintain_forest_induct[OF assms(1)])
  case (1 state)
  show ?case 
    by(cases state rule:  maintain_forest_cases)
      (auto intro!: 1 invar_aux_pres_one_step invars_pres_one_step 
              simp add: maintain_forest_simps(1)[OF 1(1)] maintain_forest_simps(2))
qed

subsection \<open>Inductions\<close>

lemma maintain_forest_implementation_invar_pres:
  assumes "maintain_forest_dom state"
          "aux_invar state" "implementation_invar state"
  shows   "implementation_invar (maintain_forest state)"
  using assms(2-) 
proof(induction rule: maintain_forest_induct[OF assms(1)])
  case (1 state)
  show ?case 
    by(cases state rule:  maintain_forest_cases)
      (auto intro!: 1 invar_aux_pres_one_step invars_pres_one_step 
              simp add: maintain_forest_simps(1)[OF 1(1)] maintain_forest_simps(2))
qed

lemma termination_of_maintain_forest:
  assumes "aux_invar state" "implementation_invar state"
          "n = card (comps \<V> (to_graph (\<FF> state)))"
  shows "maintain_forest_dom state"
  using assms 
proof(induction n arbitrary: state rule: less_induct)
  case (less n)
  then show ?case 
  proof(cases state rule: maintain_forest_cases)
    case 1
    then show ?thesis 
      by(auto intro: maintain_forest_dom_ret)
  next
    case 2
    have less_comps: "card (comps \<V> (to_graph (\<FF> (maintain_forest_upd state)))) < n"
      using mono_one_step(3)  less(2,3) 2 
      by (force simp add: less(4))     
    show ?thesis 
      using 2 less.prems(1,2) 
      by(auto intro: maintain_forest_dom_upd less(1)[OF less_comps] 
                     invar_aux_pres_one_step invars_pres_one_step(1))
  qed
qed

lemma termination_of_maintain_forest':
  assumes "aux_invar state" "implementation_invar state"
  shows "maintain_forest_dom state"
  using assms termination_of_maintain_forest 
  by(simp add: aux_invar_def)

lemma gamma_pres: 
  assumes "aux_invar state" "implementation_invar state"
  shows "current_\<gamma> (maintain_forest state) = current_\<gamma> state"
  using assms
proof(induction rule: maintain_forest_induct[OF
                            termination_of_maintain_forest[OF assms refl]])
  case (1 state)
  then show ?case 
    using  mono_one_step_gamma[of state] invar_aux_pres_one_step[of state] 
           invars_pres_one_step(1)[of state]
    by (auto intro: maintain_forest_cases[of state] 
          simp add: maintain_forest_simps)
qed

theorem maintain_forest_invar_gamma_pres:
  assumes "aux_invar state" "implementation_invar state"
  shows "invar_gamma state \<Longrightarrow> invar_gamma (maintain_forest state)"
  using assms 
proof(induction rule: maintain_forest_induct[OF
                            termination_of_maintain_forest[OF assms refl]])
  case (1 state)
  then show ?case 
    using  invar_gamma_pres_one_step[of state] invar_aux_pres_one_step[of state] 
           invars_pres_one_step(1)[of state]
    by (auto intro: maintain_forest_cases[of state] 
          simp add: maintain_forest_simps)
qed

lemma invarA2_pres: 
  assumes "aux_invar state"
          "0 \<le> thr2"
          "invarA_1 thr2 state"
          "invarA_2 thr1 thr2 state"
          "thr2 \<le> 2 * current_\<gamma> state"
          "thr1 \<le> 8 * real N * current_\<gamma> state"
          "implementation_invar state"
   shows  "invarA_2 thr1 thr2 (maintain_forest state)"
  using assms 
proof(induction rule: maintain_forest_induct[where state=state])
  case 1
  then show ?case 
    using  assms termination_of_maintain_forest
    by simp
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
      using invar_aux_pres_one_step[of state]  invars_pres_one_step(1)[of state]
            invars_pres_one_step(3)[of state thr2] invars_pres_one_step(2)[of state thr2] 
            mono_one_step_gamma[of state] IH(1,3-)
        by (auto intro: IH(2) 
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
          "implementation_invar state"
  shows "send_flow_entryF (maintain_forest state)"
  proof(rule send_flow_entryFI, goal_cases)
    case (1 e)
    hence e_in_E:"e \<in>  \<E>"
      using maintain_forest_invar_aux_pres[of state] termination_of_maintain_forest assms(1,7) 
      by(auto elim!: aux_invarE invar_aux3E)     
    have gamma_same_after_maintain_forest: "current_\<gamma> (maintain_forest state) = \<gamma>"
      using assms gamma_pres[OF assms(1)] by simp
    have " invarA_2 (real (8 * N) * \<gamma>) (2 * \<gamma>) (local.maintain_forest state)"
      using assms
      by(intro invarA2_pres[OF assms(1), of "2*\<gamma> " "8*N*\<gamma> "], auto simp add: invar_gamma_def)
    hence aa:"(a_current_flow (local.maintain_forest state)) e > 
             8*N*\<gamma> - 2 * \<gamma> * card (connected_component (to_graph (\<FF> (local.maintain_forest state))) (fst e))"
      using 1 by(auto simp add: invarA_2_def)
    have bb:"card (connected_component (to_graph (\<FF> (local.maintain_forest state))) (fst e)) \<le> N"
      using \<V>_finite  invar_aux10_def[of "(local.maintain_forest state)"] e_in_E
            maintain_forest_invar_aux_pres[of state, OF _  assms(1,7)]
            termination_of_maintain_forest[OF assms(1,7) refl] assms(1) make_pair[OF refl refl, of e]
      by(auto simp add: aux_invar_def  N_def image_def dVs_def) (smt (z3) card_mono insertI1)
    show ?case 
      using assms gamma_same_after_maintain_forest  bb aa assms 
      by (auto intro: order.strict_trans1[of _ 
                 " 8*N*\<gamma> - 2 * \<gamma> * card (_ (_ (_ (_ state))) (fst e))"] simp add: invar_gamma_def )
  qed

lemma Phi_increase: 
  assumes "aux_invar state" "invar_gamma state" "implementation_invar state"
    shows "\<Phi> (maintain_forest state) \<le> \<Phi> state + (card (comps \<V> (to_graph (\<FF> state)))) - 
                                    (card (comps \<V> (to_graph (\<FF>(maintain_forest state)))))"
  using assms 
proof(induction rule: maintain_forest_induct[of state])
  case 1
  then show ?case 
    using assms termination_of_maintain_forest by simp
next
  case (2 state)
  note IH = this
  show ?case
  proof(cases state rule:  maintain_forest_cases)
    case 1
    then show ?thesis 
      by(simp add: maintain_forest_simps(2))
  next
    case 2
    show ?thesis
      using maintain_forest_simps(1)[OF IH(1) 2] 
           invar_aux_pres_one_step[OF IH(3) 2 IH(5)] 
           invars_pres_one_step(1)[OF 2 IH(3,5)]
           invar_gamma_pres_one_step[OF 2 IH(4)] 2
           mono_one_step(4)[OF 2 IH(3,5,4)] IH(2) 
      by auto
  qed
qed

theorem Phi_increase_below_N:
 assumes "aux_invar state" "invar_gamma state" "implementation_invar state"
   shows "\<Phi> (maintain_forest state) \<le> \<Phi> state + N"
  using  Phi_increase[of state, OF assms] maintain_forest_invar_aux_pres[of state] assms
         number_comps_below_vertex_card[of "to_graph (\<FF> state)" \<V>, OF _ \<V>_finite]
         termination_of_maintain_forest
  by(simp add:  aux_invar_def invar_aux5_def N_def)

lemma F_superset:
  assumes "aux_invar state" "implementation_invar state"
  shows "\<F>_redges state \<subseteq> \<F>_redges (maintain_forest state)"
  using assms 
proof(induction rule: maintain_forest_induct[of state])
  case 1
  then show ?case 
    using assms termination_of_maintain_forest by simp
next
  case (2 state)
  note IH = this
  show ?case
  proof(cases state rule:  maintain_forest_cases)
    case 1
    then show ?thesis 
      by(simp add: maintain_forest_simps(2))
  next
    case 2
    show ?thesis
      using maintain_forest_simps(1)[OF IH(1) 2] 
           invar_aux_pres_one_step[OF IH(3) 2 IH(4)] 
           invars_pres_one_step(1)[OF 2 IH(3,4)]
           invar_gamma_pres_one_step[OF 2 ] 2
           mono_one_step(2)[OF 2 IH(3,4)] IH(2) 
      by auto
  qed
qed

lemma actives_superset:
  assumes "aux_invar state" "implementation_invar state"
  shows "to_set (actives (maintain_forest state)) \<subseteq> to_set (actives state)"
  using assms
proof(induction rule: maintain_forest_induct[of state])
  case 1
  then show ?case 
    using assms termination_of_maintain_forest by simp
next
  case (2 state)
  note IH = this
  show ?case
  proof(cases state rule:  maintain_forest_cases)
    case 1
    then show ?thesis 
      by(simp add: maintain_forest_simps(2))
  next
    case 2
    show ?thesis
      using maintain_forest_simps(1)[OF IH(1) 2] 
           invar_aux_pres_one_step[OF IH(3) 2 IH(4)] 
           invars_pres_one_step(1)[OF 2 IH(3,4)]
           invar_gamma_pres_one_step[OF 2 ] 2
           mono_one_step(6)[OF 2 IH(3,4)] IH(2) 
           mono_one_step_actives[OF 2 from_aux_invar(17)[OF IH(3)]]
      by auto
  qed
qed

lemma outside_F_no_flow_change:
  assumes "aux_invar state" "implementation_invar state"
  shows   "\<And> d. d \<in> (UNIV -  \<F> (maintain_forest state)) \<Longrightarrow>
               a_current_flow (maintain_forest state) d =  a_current_flow state d"
  using assms 
proof(induction rule: maintain_forest_induct)
  case 1
  then show ?case 
    using  termination_of_maintain_forest assms by simp
  case (2 state)
  note IH = this
  then show ?case 
  proof(cases rule: maintain_forest_cases[of state])
    case 1
    then show ?thesis 
    using maintain_forest_simps(2) IH by auto
  next
    case 2
    have dom:"maintain_forest_dom state"
       using IH termination_of_maintain_forest by auto
    show ?thesis 
    proof(subst maintain_forest_simps(1)[OF dom 2])
      have cc:"\<F> (maintain_forest_upd state)
            \<subseteq> \<F> (maintain_forest (maintain_forest_upd state))"
        using invar_aux_pres_one_step[of state] IH(3-) 2
              invars_pres_one_step(1)[of state] image_mono[OF F_superset, of _ oedge]
        by(auto simp add: F_def F_redges_def)
      have "a_current_flow (maintain_forest (maintain_forest_upd state)) d =
            a_current_flow (maintain_forest_upd state) d"
        using 2 cc IH(3) maintain_forest_simps(1)[of state, OF dom 2] 
              invar_aux_pres_one_step[of state, OF IH(4) 2 IH(5)] 
              invars_pres_one_step(1)[of state, OF 2 IH(4,5)] 
        by (auto intro: IH(2))
      moreover have "a_current_flow (maintain_forest_upd state) d = a_current_flow state d"
        using mono_one_step(5)[of state d, OF 2 IH(4,5)]  IH(3) cc 
              2 dom maintain_forest_simps(1) by auto    
      ultimately show 
            "a_current_flow (maintain_forest (maintain_forest_upd state)) d = 
                    a_current_flow state d" 
        by simp
    qed
  qed    
qed 
   
theorem maintain_forest_invar_integral_pres:
  assumes "aux_invar state" "invar_integral state" "implementation_invar state"
  shows "invar_integral (maintain_forest state)"
  unfolding invar_integral_def
proof
  fix e
  assume e_asm:" e \<in> to_set (actives (maintain_forest state))"
  hence "e \<notin> \<F> (maintain_forest state)"
    using maintain_forest_invar_aux_pres[of state, OF termination_of_maintain_forest']
          assms(1,3) 
    by(auto elim!: aux_invarE invar_aux4E)
  hence "a_current_flow (maintain_forest state) e = a_current_flow state e"
    using outside_F_no_flow_change[of state e] assms(1,3) by simp
  moreover have "current_\<gamma> (maintain_forest state) = current_\<gamma>  state"
    using gamma_pres[OF assms(1,3)] by simp
  moreover obtain x where "a_current_flow state e = real x * current_\<gamma> state"
    using assms(2) actives_superset[OF assms(1,3)] e_asm 
    by(auto elim!: invar_integralE)
  ultimately show  "\<exists>x. a_current_flow (maintain_forest state) e 
                     = real x * current_\<gamma> (maintain_forest state)"
    by simp
qed

lemma flow_optimatlity_pres: 
  assumes "aux_invar (state)"
          "0 \<le> thr2"
          "invarA_1 thr2 state"
          "invar_isOptflow state"
          "thr2 \<le> 2 * current_\<gamma> state"
          "thr1 = 8 * real N * current_\<gamma> state"
          "invarA_2 thr1 thr2 state"
          "invar_gamma state"
          "implementation_invar state"
 shows "invar_isOptflow (maintain_forest state)"
  using assms 
proof(induction rule: maintain_forest_induct[where state=state])
  case 1
  then show ?case 
   using  assms termination_of_maintain_forest' by simp
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
            invars_pres_one_step(1)[of state]
            invars_pres_one_step(2)[of state thr2] invars_pres_one_step(4)[of state]
            mono_one_step_gamma[of state] invars_pres_one_step(3)[of state thr2 thr1] 
            invar_gamma_pres_one_step[of state ] IH 2 
      by(auto intro!: IH(2) 
               intro: invars_pres_one_step(3)[of state thr2 thr1, OF 2 IH(3) _ IH(4)])
  qed 
qed

lemma forest_increase: 
  assumes "maintain_forest_dom state" "aux_invar state" 
          "implementation_invar state"
  shows   "to_graph (\<FF> (maintain_forest state)) \<supseteq> to_graph (\<FF> state)"
  using assms(2-) 
proof(induction rule: maintain_forest_induct[OF assms(1)])
  case (1 state)
  then show ?case 
    apply(cases rule: maintain_forest_cases[of state])
    using maintain_forest_simps(2) maintain_forest_simps(1) 
          mono_one_step(6)[of state] invar_aux_pres_one_step[of state]
          invars_pres_one_step(1)[of state] 
    by auto
qed

lemma card_decrease: 
  assumes "maintain_forest_dom state" "aux_invar state" "implementation_invar state"
  shows   "card (comps \<V> (to_graph (\<FF>(maintain_forest state))))
                   \<le> card (comps \<V> (to_graph (\<FF> state)))"
  using assms(2-)
proof(induction rule: maintain_forest_induct[OF assms(1)])
  case (1 state)
  then show ?case
    apply(cases rule: maintain_forest_cases[of state])
    using maintain_forest_simps(2) maintain_forest_simps(1) 
          mono_one_step(3)[of state] invar_aux_pres_one_step[of state]
          invars_pres_one_step(1)[of state]
    by auto
qed

lemma card_strict_decrease: 
  assumes "maintain_forest_dom state" "aux_invar state"
          "maintain_forest_call_cond state" "implementation_invar state"
  shows   "card (comps \<V>  (to_graph (\<FF> (maintain_forest state)))) 
                   < card (comps \<V> (to_graph (\<FF> state)))"
  apply(subst maintain_forest_simps(1)[OF assms(1) assms(3)])
  using mono_one_step(3)[of state, OF assms(3) assms(2)] assms(2,3)
        card_decrease[of "maintain_forest_upd state",
                         OF termination_of_maintain_forest] 
       invar_aux_pres_one_step[of state] invars_pres_one_step(1)[of state]
  by (simp add: assms(4))

lemma component_strict_increase: 
  assumes "maintain_forest_dom state" "aux_invar state"
          "maintain_forest_call_cond state"
          "e \<in> to_set (actives state)"
          "a_current_flow state e > 8 * real N * current_\<gamma> state"
          "implementation_invar state"
  shows   "connected_component (to_graph (\<FF> (maintain_forest state))) (fst e) = 
           connected_component (to_graph (\<FF> (maintain_forest state))) (snd e)"
  using assms(2-)
proof(induction rule: maintain_forest_induct[OF assms(1)])
  case (1 state)
  note IH = this
  have maintain_forest_dom_upd:"maintain_forest_dom (maintain_forest_upd state)"
    using  invar_aux_pres_one_step[OF IH(3,4,7)]
           invars_pres_one_step(1)[OF IH(4,3,7)]
            termination_of_maintain_forest' 
    by simp
  have e_in_E:"e \<in> \<E>" 
    using  IH(5) by(auto intro: aux_invarE[OF IH(3)] invar_aux1E)
  show ?case
  proof(subst maintain_forest_simps(1)[OF IH(1) IH(4)], 
        subst maintain_forest_simps(1)[OF IH(1) IH(4)], goal_cases)
    case 1
    then show ?case 
     proof(cases "\<not> e \<in> to_set (actives (maintain_forest_upd state))")
       case True
       hence "connected_component (to_graph (\<FF>  (maintain_forest_upd state))) (fst e) =
              connected_component (to_graph (\<FF> (maintain_forest_upd state))) (snd e)"
         using  IH(5)  invar_aux_pres_one_step[OF IH(3,4,7)] e_in_E
         by(simp add: aux_invar_def  invar_aux13_def)
       then show ?thesis       
         using  invar_aux_pres_one_step[OF IH(3,4,7)]
                invars_pres_one_step(1)[OF IH(4,3,7)]
                maintain_forest_dom_upd 
                same_component_set_mono[OF forest_increase[of "maintain_forest_upd state"]]
         by blast
  next
    case False
    hence e_active_upd:"e \<in> to_set (actives (maintain_forest_upd state))" by simp
    have same_flow:"a_current_flow (maintain_forest_upd state) e = a_current_flow state e"
      using  invar_aux_pres_one_step[OF IH(3,4,7)] e_active_upd 
      by (auto intro: mono_one_step(5)[OF IH(4,3,7), of e] simp add: aux_invar_def invar_aux4_def )
    have same_gamma: "current_\<gamma> (maintain_forest_upd state) = current_\<gamma> state"
      using IH(4) mono_one_step_gamma by force
    have "\<exists>y. get_from_set (\<lambda>e. 8 * real N * current_\<gamma> state < a_current_flow (maintain_forest_upd state) e)
       (actives (maintain_forest_upd state)) =
         Some y"
      using  invar_aux_pres_one_step[OF IH(3,4,7)] IH(6) same_flow  e_active_upd   
      by (auto intro!: set_get(1) elim: aux_invarE invar_aux17E)
    hence "maintain_forest_call_cond (maintain_forest_upd state)"
      using same_gamma 
      by(auto intro: maintain_forest_call_condI[OF refl refl refl refl])
    then show ?thesis
      using  invar_aux_pres_one_step[OF IH(3,4,7)] IH(6) same_flow same_gamma e_active_upd   
             invars_pres_one_step(1)[OF IH(4,3,7)] 
      by(intro IH(2)[OF IH(4)]) auto
    qed
  qed
qed

lemma same_number_comps_abort:
  assumes "aux_invar state" "maintain_forest_dom state" 
          "card (comps \<V> (to_graph (\<FF> (maintain_forest state)))) = 
              card (comps \<V> (to_graph (\<FF> state)))" "implementation_invar state"
    shows "maintain_forest_ret_cond state"
  using assms apply(cases rule: maintain_forest_cases[of state], simp)
  using card_strict_decrease[of state] assms by simp

lemma all_actives_zero_flow_same_state:
  assumes "\<forall>e\<in>to_set (actives state). a_current_flow state e = 0"
          "aux_invar state" "invar_gamma state" 
  shows   "maintain_forest state = state"
proof(subst maintain_forest_simps(2)[OF maintain_forest_ret_condI, OF refl refl refl refl], goal_cases)
  case 1
  show ?case
  proof(rule ccontr, clarsimp, goal_cases)
    case (1 e)
    have set_invar:"set_invar (actives state)" 
      by (simp add: assms(2) from_aux_invar'(17))
    have "8 * real N * current_\<gamma> state < a_current_flow state e" "e \<in> to_set (actives state)"
      using set_get(2,3)[OF set_invar 1] by auto
    moreover have "current_\<gamma> state > 0"
      using assms(3) invar_gammaD by auto
    ultimately show False
      using assms(1) 
      by (simp add: mult_less_0_iff)
  qed
qed simp
  
end
end