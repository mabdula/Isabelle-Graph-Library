section \<open>Implementation with Abstract Datatypes\<close>

theory Orlins_Implementation
  imports IntermediateSummary LoopA LoopB Orlins
begin
context Map
begin
bundle automation' = map_empty[simp] map_update[simp] map_delete[simp]
                    invar_empty[simp] invar_update[simp] invar_delete[simp]
end

locale algo_impl_spec =
algo_spec where fst = "fst::'edge_type \<Rightarrow> 'a"+ 
flow_map: Map  flow_empty "flow_update::'edge_type \<Rightarrow> real \<Rightarrow> 'f_impl \<Rightarrow> 'f_impl"
                flow_delete flow_lookup flow_invar +
bal_map: Map  bal_empty "bal_update:: 'a \<Rightarrow> real \<Rightarrow> 'b_impl \<Rightarrow> 'b_impl" 
               bal_delete bal_lookup bal_invar +
rep_comp_map: Map  rep_comp_empty "rep_comp_update::'a \<Rightarrow> ('a \<times> nat) \<Rightarrow> 'r_comp_impl \<Rightarrow> 'r_comp_impl"
              rep_comp_delete rep_comp_lookup rep_comp_invar +
conv_map: Map  conv_empty "conv_update::('a \<times> 'a) \<Rightarrow> 'edge_type Redge \<Rightarrow> 'conv_impl \<Rightarrow> 'conv_impl"
              conv_delete conv_lookup conv_invar +
not_blocked_map: Map  not_blocked_empty "not_blocked_update::'edge_type \<Rightarrow> bool \<Rightarrow> 'not_blocked_impl\<Rightarrow> 'not_blocked_impl"
              not_blocked_delete not_blocked_lookup not_blocked_invar 
for flow_empty flow_update flow_delete flow_lookup flow_invar bal_empty bal_update bal_delete 
    bal_lookup bal_invar rep_comp_empty rep_comp_update rep_comp_delete rep_comp_lookup 
    rep_comp_invar conv_empty conv_update conv_delete conv_lookup conv_invar not_blocked_update 
    not_blocked_empty not_blocked_delete not_blocked_lookup not_blocked_invar fst+
fixes rep_comp_update_all::"('a \<Rightarrow> ('a \<times> nat) \<Rightarrow> ('a \<times> nat)) \<Rightarrow>  'r_comp_impl \<Rightarrow> 'r_comp_impl"
fixes not_blocked_update_all::"('edge_type \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> 'not_blocked_impl \<Rightarrow> 'not_blocked_impl"
fixes flow_update_all::"('edge_type \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'f_impl \<Rightarrow> 'f_impl"
fixes get_max::"('a \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'b_impl \<Rightarrow> real"
assumes  rep_comp_update_all: 
    "\<And> rep f. rep_comp_invar rep \<Longrightarrow> (\<And> x. x \<in> dom (rep_comp_lookup rep) 
                  \<Longrightarrow> rep_comp_lookup (rep_comp_update_all f rep) x =
                      Some (f x (the (rep_comp_lookup rep x))))"
    "\<And> rep f g. rep_comp_invar rep \<Longrightarrow> (\<And> x. x \<in> dom (rep_comp_lookup rep)  \<Longrightarrow>
                     f x (the (rep_comp_lookup rep x)) = g x (the (rep_comp_lookup rep x))) \<Longrightarrow>
          rep_comp_update_all f rep = rep_comp_update_all g rep "
   "\<And> rep f. rep_comp_invar rep \<Longrightarrow> rep_comp_invar (rep_comp_update_all f rep)"
   "\<And> rep f. rep_comp_invar rep \<Longrightarrow> dom (rep_comp_lookup (rep_comp_update_all f rep))
                              = dom (rep_comp_lookup rep)"
 and not_blocked_update_all: 
    "\<And> nblckd f. not_blocked_invar nblckd \<Longrightarrow> (\<And> x. x \<in> dom (not_blocked_lookup nblckd) 
                  \<Longrightarrow> not_blocked_lookup (not_blocked_update_all f nblckd) x =
                      Some (f x (the (not_blocked_lookup nblckd x))))"
    "\<And> nblckd f g. not_blocked_invar nblckd \<Longrightarrow> (\<And> x. x \<in> dom (not_blocked_lookup nblckd)  \<Longrightarrow>
                     f x (the (not_blocked_lookup nblckd x)) = g x (the (not_blocked_lookup nblckd x))) \<Longrightarrow>
          not_blocked_update_all f nblckd = not_blocked_update_all g nblckd "
   "\<And> nblckd f. not_blocked_invar nblckd \<Longrightarrow> not_blocked_invar (not_blocked_update_all f nblckd)"
   "\<And> nblckd f. not_blocked_invar nblckd \<Longrightarrow> dom (not_blocked_lookup (not_blocked_update_all f nblckd))
                              = dom (not_blocked_lookup nblckd)"
 and flow_update_all: 
    "\<And> fl f. flow_invar fl \<Longrightarrow> (\<And> x. x \<in> dom (flow_lookup fl) 
                  \<Longrightarrow> flow_lookup (flow_update_all f fl) x =
                      Some (f x (the (flow_lookup fl x))))"
    "\<And> fl f g. flow_invar fl \<Longrightarrow> (\<And> x. x \<in> dom (flow_lookup fl)  \<Longrightarrow>
                     f x (the (flow_lookup fl x)) = g x (the (flow_lookup fl x))) \<Longrightarrow>
          flow_update_all f fl = flow_update_all g fl "
   "\<And> fl f. flow_invar fl \<Longrightarrow> flow_invar (flow_update_all f fl)"
   "\<And> fl f. flow_invar fl \<Longrightarrow> dom (flow_lookup (flow_update_all f fl))
                              = dom (flow_lookup fl)"
and get_max: "\<And> b f. bal_invar b \<Longrightarrow> dom (bal_lookup b) \<noteq> {}
 \<Longrightarrow> get_max f b = Max {f y (the (bal_lookup b y)) | y. y \<in> dom (bal_lookup b)}"
begin
context
  includes flow_map.automation bal_map.automation rep_comp_map.automation conv_map.automation
           not_blocked_map.automation
begin

definition "insert_undirected_edge_impl u v forst \<equiv> (let neighbs_u = the (lookup forst u);
                                                    neighbs_v = the (lookup forst v);
                                                    neighb_u_new = neighb_insert v neighbs_u;
                                                    neighb_v_new = neighb_insert u neighbs_v
                                                 in edge_map_update v neighb_v_new (
                                                    edge_map_update u neighb_u_new forst))"

definition "move_balance b x y = (let bx = the (bal_lookup b x);
                                      by = the (bal_lookup b y) in
                                          (bal_update x 0 (bal_update y (bx + by) b)))"


fun augment_edge_impl::"'f_impl \<Rightarrow> real \<Rightarrow>'edge_type Redge \<Rightarrow> 'f_impl" where
"augment_edge_impl f \<gamma> e = 
  ((case e of F e \<Rightarrow> flow_update e (the (flow_lookup f e) + \<gamma>) f |
              B e \<Rightarrow> flow_update e (the (flow_lookup f e) - \<gamma>) f))"


fun to_redge_path_impl where
"to_redge_path_impl to_rdg [u,v] = [the (conv_lookup to_rdg (u,v))]"|
"to_redge_path_impl to_rdg (u#v#vs) = (the (conv_lookup to_rdg (u,v)) # to_redge_path_impl to_rdg (v#vs))"|
"to_redge_path_impl  _ _ = []"

   
fun augment_edges_impl::"'f_impl\<Rightarrow> real \<Rightarrow>('edge_type Redge) list \<Rightarrow> 'f_impl" where
"augment_edges_impl f \<gamma> [] = f"|
"augment_edges_impl f \<gamma> (e#es) = augment_edge_impl (augment_edges_impl f \<gamma> es) \<gamma> e"

definition "add_direction to_rdg x y e= 
          (conv_update (x, y) (F e) (conv_update (y, x) (B e) to_rdg))"

definition "move b \<gamma> x y = (let bx = the (bal_lookup b x);
                                      by = the (bal_lookup b y) in
                           (bal_update x (bx - \<gamma>) (bal_update y (by + \<gamma>) b)))"

abbreviation "flow_domain edg_mp \<equiv> dom( flow_lookup edg_mp)"
abbreviation "rep_comp_domain edg_mp \<equiv> dom (rep_comp_lookup edg_mp)"
abbreviation "bal_domain edg_mp \<equiv> dom (bal_lookup edg_mp)"
abbreviation "conv_domain edg_mp \<equiv> dom (conv_lookup edg_mp)"

definition "abstract_flow_map mp = (\<lambda> e. if flow_lookup mp e \<noteq> None 
                                              then the (flow_lookup mp e)
                                              else 0)"
end
end

locale algo_impl = algo_impl_spec where rep_comp_update_all = 
"rep_comp_update_all::('a \<Rightarrow> ('a \<times> nat) \<Rightarrow> ('a \<times> nat)) \<Rightarrow>  'r_comp_impl \<Rightarrow> 'r_comp_impl" and
not_blocked_update_all="not_blocked_update_all::('edge_type \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> 'not_blocked_impl \<Rightarrow> 'not_blocked_impl" and
 flow_update_all="flow_update_all::('edge_type \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'f_impl \<Rightarrow> 'f_impl" and
 get_max="get_max::('a \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> 'b_impl \<Rightarrow> real"
and conv_empty = "conv_empty::'conv_impl"
 + algo
for rep_comp_update_all not_blocked_update_all flow_update_all get_max conv_empty
begin
context
  includes flow_map.automation bal_map.automation rep_comp_map.automation conv_map.automation
           not_blocked_map.automation
begin

lemma insert_undirected_edge_equivalent[simp]: "insert_undirected_edge_impl = insert_undirected_edge"
  using insert_undirected_edge_def insert_undirected_edge_impl_def by presburger


lemma augment_edge_impl_domain:
      "e = oedge ee \<Longrightarrow> e \<in> flow_domain f \<Longrightarrow> flow_invar f \<Longrightarrow>
      flow_domain (augment_edge_impl  f \<gamma> ee) = flow_domain f" 
  by(auto split: Redge.split simp add: redge_case_flip)
  
lemma augment_edge_impl_invar:
      "e = oedge ee \<Longrightarrow> e \<in> flow_domain f \<Longrightarrow> flow_invar f \<Longrightarrow>
      flow_invar (augment_edge_impl  f \<gamma> ee)"
  by(auto split: Redge.split simp add: redge_case_flip)

lemma augment_edge_abstract_homo:
      "e = oedge ee \<Longrightarrow> e \<in> flow_domain f \<Longrightarrow> flow_invar f \<Longrightarrow>
      augment_edge (abstract_flow_map f) \<gamma> ee = 
      abstract_flow_map (augment_edge_impl  f \<gamma> ee)"
  unfolding abstract_flow_map_def 
  by(auto intro!: ext split: Redge.split simp add: redge_case_flip)

lemma augment_edges_impl_domain_invar[simp]:
      "set(map oedge es) \<subseteq> flow_domain f \<Longrightarrow> flow_invar f \<Longrightarrow>
      flow_domain (augment_edges_impl  f \<gamma> es) = flow_domain f \<and>
      flow_invar (augment_edges_impl  f \<gamma> es)"
  using augment_edge_impl_domain augment_edge_impl_invar
  by(induction es)
    (auto simp add:  augment_edge_impl_domain augment_edge_impl_invar)

lemmas  augment_edges_impl_domain[simp] = conjunct1[OF augment_edges_impl_domain_invar]
lemmas  augment_edges_impl_invar[intro] = conjunct2[OF augment_edges_impl_domain_invar]

lemma augment_edges_homo[simp]:
      "set(map oedge es) \<subseteq> flow_domain f \<Longrightarrow> flow_invar f \<Longrightarrow>
      abstract_flow_map (augment_edges_impl f \<gamma> es) = augment_edges (abstract_flow_map f) \<gamma> es"
    apply(rule sym)
    using augment_edges_impl_domain_invar augment_edge_abstract_homo
    by(induction es) auto

lemma flow_abstract[simp]: "e \<in> flow_domain f_impl \<Longrightarrow> the (flow_lookup f_impl e) = (abstract_flow_map f_impl) e"
  unfolding  abstract_flow_map_def by auto

definition "abstract_bal_map mp = (\<lambda> x. if bal_lookup mp x \<noteq> None 
                                              then the (bal_lookup mp x)
                                              else \<b> x)"

lemma abstract_bal_map_homo[simp, intro]: "bal_invar b \<Longrightarrow> x \<in> bal_domain b \<Longrightarrow>
                             y \<in> bal_domain b \<Longrightarrow> abstract_bal_map b = b_abs \<Longrightarrow>
               abstract_bal_map (move_balance b x y) = 
               (\<lambda> v. if v= x then 0 
                     else if v = y then b_abs y + b_abs x
                     else b_abs v)"
  unfolding  abstract_bal_map_def move_balance_def Let_def 
  by auto

lemma abstract_bal_invar[simp, intro]: "bal_invar b \<Longrightarrow> abstract_bal_map b = b_abs \<Longrightarrow>
              bal_invar (move_balance b x y)"
  unfolding  abstract_bal_map_def move_balance_def Let_def
  by auto

lemma abstract_bal_map_domain[simp]: "bal_invar b \<Longrightarrow> x \<in> bal_domain b \<Longrightarrow>
                             y \<in> bal_domain b \<Longrightarrow> abstract_bal_map b = b_abs \<Longrightarrow>
               bal_domain (move_balance b x y) = bal_domain b"
  unfolding  abstract_bal_map_def move_balance_def Let_def
  by auto

lemma abstract_balance[simp, intro]:  "x \<in> bal_domain b_impl \<Longrightarrow> abstract_bal_map b_impl = b \<Longrightarrow>
                                the (bal_lookup b_impl x) = b x"
  unfolding abstract_bal_map_def by auto

lemma abstract_bal_map_homo_move_gamma[simp, intro]: "bal_invar b \<Longrightarrow> s \<in> bal_domain b \<Longrightarrow>
                             t \<in> bal_domain b \<Longrightarrow>abstract_bal_map b =  b_abs \<Longrightarrow>
               abstract_bal_map (move b \<gamma> s t) = 
               (\<lambda> v. if v = s then b_abs s - \<gamma> 
                                  else if v = t then b_abs t + \<gamma>
                                  else b_abs v)"
  unfolding abstract_bal_map_def move_def Let_def
  by auto

lemma abstract_bal_invar_move[intro]: "bal_invar b \<Longrightarrow> b_abs = abstract_bal_map b \<Longrightarrow>
              bal_invar (move b \<gamma> x y)"
  unfolding abstract_bal_map_def move_def Let_def
  by auto

lemma abstract_bal_map_domain_move[simp, intro]: "bal_invar b \<Longrightarrow> x \<in> bal_domain b \<Longrightarrow>
                             y \<in> bal_domain b \<Longrightarrow>abstract_bal_map b =  b_abs  \<Longrightarrow>
               bal_domain (move b \<gamma> x y) = bal_domain b"
  unfolding abstract_bal_map_def move_def Let_def
  by auto
 
definition "abstract_conv_map mp = (\<lambda> e. if conv_lookup mp e \<noteq> None 
                                         then the (conv_lookup mp e)
                                         else default_conv_to_rdg e)"

definition "abstract_not_blocked_map mp = (\<lambda> e. if not_blocked_lookup mp e = None then False
                                                 else the (not_blocked_lookup mp e))"

abbreviation "not_blocked_dom mp \<equiv> dom (not_blocked_lookup mp)"

lemma  not_blocked_update_all_homo_card_old:
       assumes "nb = abstract_not_blocked_map nb_impl" "not_blocked_invar nb_impl"
       "nb_impl' = not_blocked_update_all f nb_impl"
       "(\<And> v. v \<notin> not_blocked_dom nb_impl \<Longrightarrow> nb' v = False)"
       "(\<And> v. v \<in> not_blocked_dom nb_impl \<Longrightarrow> (f v (the (not_blocked_lookup nb_impl v))) = nb' v)"
       shows "nb' = abstract_not_blocked_map nb_impl'"
  unfolding abstract_not_blocked_map_def
  apply (rule ext)
  subgoal for x
    apply(rule P_of_ifI)
    subgoal 
      using assms(2) not_blocked_update_all(4) 
      by (intro assms(4), auto simp add:  assms(3) )
    subgoal
      apply(subst assms(3), subst not_blocked_update_all(1))
      using assms  not_blocked_update_all(4) 
      by (simp?, fastforce intro!: sym[OF assms(5)])+
    done
  done

lemma  not_blocked_update_all_homo_card[intro]:
       assumes "abstract_not_blocked_map nb_impl = nb" "not_blocked_invar nb_impl"
       "nb_impl' = not_blocked_update_all f nb_impl"
       "(\<And> v. v \<notin> not_blocked_dom nb_impl \<Longrightarrow> nb' v = False)"
       "(\<And> v. v \<in> not_blocked_dom nb_impl \<Longrightarrow> (f v (the (not_blocked_lookup nb_impl v))) = nb' v)"
     shows "abstract_not_blocked_map nb_impl' = nb'"
  using assms not_blocked_update_all_homo_card_old
  by force

lemma abstract_conv_invar[simp]: "conv_invar to_rdg  \<Longrightarrow>
              conv_invar (add_direction to_rdg  x y e)"
  unfolding  abstract_conv_map_def add_direction_def Let_def
  by auto

lemma abstract_conv_map_domain[simp]: "conv_invar to_rdg \<Longrightarrow>
               conv_domain (add_direction to_rdg  x y e) = 
               conv_domain to_rdg \<union> {(x, y), (y, x)}"
  unfolding abstract_conv_map_def add_direction_def Let_def
  by auto

lemma abstract_conv_consist: "conv_invar to_rdg \<Longrightarrow>  to_rdg_abs = abstract_conv_map to_rdg  
                 \<Longrightarrow> consist to_rdg_abs 
                 \<Longrightarrow> to_rdg'_abs = abstract_conv_map ( add_direction to_rdg x y e)\<Longrightarrow>
                 make_pair e = (x,y) \<Longrightarrow>
                 consist to_rdg'_abs"
  unfolding  abstract_conv_map_def add_direction_def Let_def
proof(goal_cases)
  case 1
  have helper:"consist to_rdg'_abs" if assms:"conv_invar to_rdg"
    "to_rdg_abs =
    (\<lambda>e. if conv_lookup to_rdg e \<noteq> None then the (conv_lookup to_rdg e)
          else default_conv_to_rdg e)"
    "consist to_rdg_abs"
    "to_rdg'_abs =
    (\<lambda>ea. if ((conv_lookup to_rdg)((y, x) \<mapsto> B e, (x, y) \<mapsto> F e)) ea \<noteq> None
           then the (((conv_lookup to_rdg)((y, x) \<mapsto> B e, (x, y) \<mapsto> F e)) ea)
           else default_conv_to_rdg ea)"
    "make_pair e = (x, y)" "consist default_conv_to_rdg"
  proof(insert assms, goal_cases)
  case 1
  note top=this
  show ?case
  unfolding consist_def 
  proof(rule conjI, goal_cases)
   case 1
   show ?case 
     apply(insert top 1, rule allI, rule allI)
     unfolding consist_def
     by (smt (verit) fun_upd_other fun_upd_same option.sel swap_simp)
  next
   case 2
   show ?case 
     apply(insert top 1, rule allI, rule allI)
     unfolding consist_def 
     by (smt (z3) consist_fstv consist_sndv default_conv_to_rdg erev.simps(1)
 erev.simps(2) fun_upd_apply option.distinct(1) option.sel)
 qed
qed
  show ?thesis
   by(insert 1, (subst (asm) conv_map.map_update, 
         (force intro: conv_map.invar_update)?)+, (insert default_conv_to_rdg),
         intro helper) auto
qed

lemma abstract_conv_homo_complex: "conv_invar to_rdg \<Longrightarrow>  to_rdg_abs = abstract_conv_map to_rdg  
                 \<Longrightarrow> to_rdg'_abs = abstract_conv_map (add_direction to_rdg x y e)\<Longrightarrow>
                    make_pair e = (x, y) \<Longrightarrow> 
                 to_rdg'_abs = (\<lambda> d. if d = make_pair e then F e
                                     else if prod.swap d = make_pair e then B e
                                     else to_rdg_abs d)"
  unfolding  abstract_conv_map_def add_direction_def Let_def
  by fastforce

lemmas abstract_conv_homo[simp] = abstract_conv_homo_complex[OF _ _ refl]

definition "abstract_rep_map mp = (\<lambda> x. if rep_comp_lookup mp x \<noteq> None 
                                         then prod.fst (the (rep_comp_lookup mp x))
                                         else  x)"

definition "abstract_comp_map mp = (\<lambda> x. if rep_comp_lookup mp x \<noteq> None 
                                         then prod.snd (the (rep_comp_lookup mp x))
                                         else  1)"

lemma abstract_rep[simp]: "x \<in> rep_comp_domain rc_impl \<Longrightarrow> r = abstract_rep_map rc_impl \<Longrightarrow> 
                    prod.fst (the (rep_comp_lookup rc_impl x)) = r x"
  unfolding abstract_rep_map_def by auto

lemma abstract_card[simp]: "x \<in> rep_comp_domain rc_impl \<Longrightarrow> r = abstract_comp_map rc_impl \<Longrightarrow> 
                    prod.snd (the (rep_comp_lookup rc_impl x)) = r x"
  unfolding abstract_comp_map_def by auto

lemma  r_card_update_all_homo_rep_old:
       assumes "r = abstract_rep_map r_card_impl" "rep_comp_invar r_card_impl"
       "r_card_impl' = rep_comp_update_all f r_card_impl"
       "(\<And> v. v \<notin> rep_comp_domain r_card_impl \<Longrightarrow> r' v = v)"
       "(\<And> v. v \<in> rep_comp_domain r_card_impl \<Longrightarrow> prod.fst (f v (the (rep_comp_lookup r_card_impl v))) = r' v)"
       shows "r' = abstract_rep_map r_card_impl'"
  unfolding abstract_rep_map_def
  apply (rule ext)
  subgoal for x
    apply(rule P_of_ifI)
    subgoal 
      apply(subst assms(3), subst rep_comp_update_all(1))
      using assms(2) assms(3) domIff rep_comp_update_all(4) 
      by (fastforce intro: sym[OF assms(5)] simp add: rep_comp_update_all(1))+
    subgoal
      using assms(2) assms(3) option.distinct(1) rep_comp_update_all(1) 
      by (intro assms(4), fast)
    done
  done

lemma  r_card_update_all_homo_rep_complex:
       assumes "abstract_rep_map r_card_impl = r" "rep_comp_invar r_card_impl"
       "r_card_impl' = rep_comp_update_all f r_card_impl"
       "(\<And> v. v \<notin> rep_comp_domain r_card_impl \<Longrightarrow> r' v = v)"
       "(\<And> v. v \<in> rep_comp_domain r_card_impl \<Longrightarrow> prod.fst (f v (the (rep_comp_lookup r_card_impl v))) = r' v)"
     shows "abstract_rep_map r_card_impl' = r'"
  using assms r_card_update_all_homo_rep_old by force

lemmas  r_card_update_all_homo_rep[simp, intro] =  r_card_update_all_homo_rep_complex[OF refl _ refl]

lemma  r_card_update_all_homo_card_old:
       assumes "c = abstract_comp_map r_card_impl" "rep_comp_invar r_card_impl"
       "r_card_impl' = rep_comp_update_all f r_card_impl"
       "(\<And> v. v \<notin> rep_comp_domain r_card_impl \<Longrightarrow> c' v = 1)"
       "(\<And> v. v \<in> rep_comp_domain r_card_impl \<Longrightarrow> prod.snd (f v (the (rep_comp_lookup r_card_impl v))) = c' v)"
       shows "c' = abstract_comp_map r_card_impl'"
  unfolding abstract_comp_map_def
  apply (rule ext)
  subgoal for x
    apply(rule P_of_ifI)
    subgoal 
      using assms(2) assms(3) assms(5) rep_comp_update_all(1,2,4) 
      by fastforce
    subgoal
      using assms(2) assms(3) option.distinct(1) rep_comp_update_all(1) 
      by (intro assms(4), fast)
    done
  done

lemma  r_card_update_all_homo_card_complex:
       assumes "abstract_comp_map r_card_impl = c" "rep_comp_invar r_card_impl"
       "r_card_impl' = rep_comp_update_all f r_card_impl"
       "(\<And> v. v \<notin> rep_comp_domain r_card_impl \<Longrightarrow> c' v = 1)"
       "(\<And> v. v \<in> rep_comp_domain r_card_impl \<Longrightarrow> prod.snd (f v (the (rep_comp_lookup r_card_impl v))) = c' v)"
     shows "abstract_comp_map r_card_impl' = c'"
  using r_card_update_all_homo_card_old assms by force

lemmas r_card_update_all_homo_card[simp, intro] = r_card_update_all_homo_card_complex[OF refl _  refl]

lemma to_redge_path_homo[simp]:
  assumes "to_rdg = abstract_conv_map to_rdg_impl"
          "set (vwalk_arcs P) \<subseteq> dom (conv_lookup to_rdg_impl)"   
    shows "to_redge_path_impl to_rdg_impl P = to_redge_path to_rdg P"
  using assms
  apply(induction P, simp)
  subgoal for a P
    apply(cases P, simp)
    subgoal for b Q
      unfolding dom_def  abstract_conv_map_def 
      by (cases Q, auto simp add: abstract_conv_map_def domIff)
    done
  done

definition abstract::"('f_impl, 'b_impl, 'c, 'conv_impl, 'd, 'r_comp_impl, 'not_blocked_impl) Algo_state_impl 
                       \<Rightarrow> ('a, 'd, 'c, 'edge_type) Algo_state"
  where "abstract state =
         (let \<FF> = \<FF>_impl state;
                    f = abstract_flow_map (current_flow_impl state);
                    b = abstract_bal_map (balance_impl state);
                    r = abstract_rep_map (representative_comp_card_impl state);
                    E' = actives_impl state;
                    to_rdg = abstract_conv_map (conv_to_rdg_impl state);
                    \<gamma> = current_\<gamma>_impl state;
                    return = return_impl state;
                    cards = abstract_comp_map (representative_comp_card_impl state);
                    not_blocked = abstract_not_blocked_map (not_blocked_impl state) in
            \<lparr> current_flow = f, balance = b, \<FF> = to_graph \<FF>, conv_to_rdg = to_rdg, actives =  E', 
              return = return, current_\<gamma> = \<gamma>, representative = r,
              comp_card = cards, \<FF>_imp = \<FF>, not_blocked = not_blocked\<rparr>)"

lemma abstractE_extensive:
  fixes F
  assumes "state = abstract state_impl"
          "current_flow state = f" "f_impl = current_flow_impl state_impl" "f_impl_abs = abstract_flow_map f_impl"
 "current_flow state = f" "f_impl = current_flow_impl state_impl" "f_impl_abs = abstract_flow_map f_impl"
 "balance state = b" "b_impl = balance_impl state_impl" "b_impl_abs = abstract_bal_map b_impl"
 "representative state = r" "r_card_impl = (representative_comp_card_impl state_impl)" "r_impl_abs = abstract_rep_map  r_card_impl"
 "cards = comp_card state"  "card_impl_abs = abstract_comp_map r_card_impl"                          
 "F = \<FF> state" "F_impl = \<FF>_impl state_impl" "F_impl_abs = to_graph F_impl" "F_imp = \<FF>_imp state"
 "to_rdg = conv_to_rdg state" "to_rdg_impl = conv_to_rdg_impl state_impl" "to_rdg_impl_abs = abstract_conv_map to_rdg_impl"
 "E' = actives state" "E'_impl = actives_impl state_impl"
 "ret = return state" "ret_impl = return_impl state_impl"
 "curr_g = current_\<gamma> state" "curr_g_impl = current_\<gamma>_impl state_impl"
 "nb = not_blocked state" "nb_impl = not_blocked_impl state_impl" "nb_impl_abs = abstract_not_blocked_map nb_impl"
shows   "f = f_impl_abs"
        "b = b_impl_abs"
       "r = r_impl_abs"
        "cards = card_impl_abs" 
        "F = F_impl_abs"
        "F_imp = F_impl"
        "to_rdg = to_rdg_impl_abs"
        "E' = E'_impl"
        "ret = ret_impl"
        "curr_g = curr_g_impl"
        "nb = nb_impl_abs"
  using assms unfolding Let_def abstract_def by auto

lemmas abstractE[simp] = abstractE_extensive[OF refl refl refl refl refl refl refl refl refl refl refl refl refl refl
                                          refl refl refl refl refl refl refl refl refl refl refl refl refl refl
                                          refl refl refl, simplified HOL.eq_commute]

lemmas abstractE' = abstractE_extensive[OF refl refl refl refl refl refl refl refl refl refl refl refl refl refl
                                          refl refl refl refl refl refl refl refl refl refl refl refl refl refl
                                          refl refl refl]



find_theorems "(_ = _) = (_ = _)"


definition "implementation_invar state_impl \<equiv> 
            adj_inv (\<FF>_impl state_impl) 
          \<and> (\<forall> x. neighb_inv (the (lookup (\<FF>_impl state_impl) x))) 
          \<and> set_invar (actives_impl state_impl)
          \<and> \<E> = flow_domain (current_flow_impl state_impl)
          \<and> flow_invar (current_flow_impl state_impl) 
          \<and> \<V> = bal_domain (balance_impl state_impl)
          \<and> bal_invar (balance_impl state_impl)
          \<and> to_set_of_adjacency (\<FF>_impl state_impl) = conv_domain (conv_to_rdg_impl state_impl)
          \<and> conv_invar (conv_to_rdg_impl state_impl)
          \<and> \<V> = rep_comp_domain (representative_comp_card_impl state_impl)
          \<and> rep_comp_invar (representative_comp_card_impl state_impl)
          \<and> not_blocked_invar (not_blocked_impl state_impl)
          \<and> \<E> = not_blocked_dom (not_blocked_impl state_impl)"

lemma implementation_invarI[simp]:
     "adj_inv (\<FF>_impl state_impl) 
          \<Longrightarrow> (\<forall> x. neighb_inv (the (lookup (\<FF>_impl state_impl) x))) 
          \<Longrightarrow> set_invar (actives_impl state_impl)
          \<Longrightarrow> \<E>= flow_domain (current_flow_impl state_impl)
          \<Longrightarrow> flow_invar (current_flow_impl state_impl) 
          \<Longrightarrow> \<V> = bal_domain (balance_impl state_impl)
          \<Longrightarrow> bal_invar (balance_impl state_impl)
          \<Longrightarrow> to_set_of_adjacency (\<FF>_impl state_impl) = conv_domain (conv_to_rdg_impl state_impl)
          \<Longrightarrow> conv_invar (conv_to_rdg_impl state_impl)
          \<Longrightarrow> \<V> = rep_comp_domain (representative_comp_card_impl state_impl)
          \<Longrightarrow> rep_comp_invar (representative_comp_card_impl state_impl)
          \<Longrightarrow> not_blocked_invar (not_blocked_impl state_impl)
          \<Longrightarrow> \<E> = not_blocked_dom (not_blocked_impl state_impl) \<Longrightarrow> implementation_invar state_impl"
  unfolding implementation_invar_def by simp

lemma implementation_invarE[simp, elim]:
     " implementation_invar state_impl \<Longrightarrow> 
          (adj_inv (\<FF>_impl state_impl) 
          \<Longrightarrow> (\<forall> x. neighb_inv (the (lookup (\<FF>_impl state_impl) x))) 
          \<Longrightarrow> set_invar (actives_impl state_impl)
          \<Longrightarrow> \<E> = flow_domain (current_flow_impl state_impl)
          \<Longrightarrow> flow_invar (current_flow_impl state_impl) 
          \<Longrightarrow> \<V> = bal_domain (balance_impl state_impl)
          \<Longrightarrow> bal_invar (balance_impl state_impl)
          \<Longrightarrow> to_set_of_adjacency (\<FF>_impl state_impl) = conv_domain (conv_to_rdg_impl state_impl)
          \<Longrightarrow> conv_invar (conv_to_rdg_impl state_impl)
          \<Longrightarrow> \<V> = rep_comp_domain (representative_comp_card_impl state_impl)
          \<Longrightarrow> rep_comp_invar (representative_comp_card_impl state_impl)
          \<Longrightarrow> not_blocked_invar (not_blocked_impl state_impl)
          \<Longrightarrow> \<E> = not_blocked_dom (not_blocked_impl state_impl) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding implementation_invar_def by auto

lemma implementation_invar_partialE:
      "implementation_invar state_impl \<Longrightarrow>((adj_inv (\<FF>_impl state_impl)) \<Longrightarrow> P ) \<Longrightarrow> P"
      "implementation_invar state_impl \<Longrightarrow>((\<forall> x. neighb_inv (the (lookup (\<FF>_impl state_impl) x)))\<Longrightarrow> P ) \<Longrightarrow> P"
      "implementation_invar state_impl \<Longrightarrow>(set_invar (actives_impl state_impl) \<Longrightarrow> P ) \<Longrightarrow> P"
      "implementation_invar state_impl \<Longrightarrow>(\<E> = flow_domain (current_flow_impl state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
      "implementation_invar state_impl \<Longrightarrow>(flow_invar (current_flow_impl state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
      "implementation_invar state_impl \<Longrightarrow>(\<V> = bal_domain (balance_impl state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
      "implementation_invar state_impl \<Longrightarrow>(bal_invar (balance_impl state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
      "implementation_invar state_impl \<Longrightarrow>(to_set_of_adjacency (\<FF>_impl state_impl) =
                     conv_domain (conv_to_rdg_impl state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
      "implementation_invar state_impl \<Longrightarrow> (conv_invar (conv_to_rdg_impl state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
      "implementation_invar state_impl \<Longrightarrow> (\<V> = rep_comp_domain (representative_comp_card_impl state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
      "implementation_invar state_impl \<Longrightarrow> (rep_comp_invar (representative_comp_card_impl state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
      "implementation_invar state_impl \<Longrightarrow> (not_blocked_invar (not_blocked_impl state_impl)\<Longrightarrow> P ) \<Longrightarrow> P"
      "implementation_invar state_impl \<Longrightarrow> (\<E> = not_blocked_dom (not_blocked_impl state_impl) \<Longrightarrow> P) \<Longrightarrow> P"
  unfolding implementation_invar_def by auto

lemma implementation_invar_partial_props:
      "implementation_invar state_impl \<Longrightarrow>(adj_inv (\<FF>_impl state_impl))"
      "implementation_invar state_impl \<Longrightarrow>(\<forall> x. neighb_inv (the (lookup (\<FF>_impl state_impl) x)))"
      "implementation_invar state_impl \<Longrightarrow>set_invar (actives_impl state_impl)"
      "implementation_invar state_impl \<Longrightarrow>\<E> = flow_domain (current_flow_impl state_impl)"
      "implementation_invar state_impl \<Longrightarrow>flow_invar (current_flow_impl state_impl)"
      "implementation_invar state_impl \<Longrightarrow>\<V> = bal_domain (balance_impl state_impl)"
      "implementation_invar state_impl \<Longrightarrow>bal_invar (balance_impl state_impl)"
      "implementation_invar state_impl \<Longrightarrow>to_set_of_adjacency (\<FF>_impl state_impl) =
                     conv_domain (conv_to_rdg_impl state_impl)"
      "implementation_invar state_impl \<Longrightarrow> conv_invar (conv_to_rdg_impl state_impl)"
      "implementation_invar state_impl \<Longrightarrow> \<V> = rep_comp_domain (representative_comp_card_impl state_impl)"
      "implementation_invar state_impl \<Longrightarrow> rep_comp_invar (representative_comp_card_impl state_impl)"
      "implementation_invar state_impl \<Longrightarrow> not_blocked_invar (not_blocked_impl state_impl)"
      "implementation_invar state_impl \<Longrightarrow> \<E> = not_blocked_dom (not_blocked_impl state_impl)"
  unfolding implementation_invar_def by auto

lemma  same_flow_provided_domain[simp]:
        assumes "state = abstract state_impl"
        shows " xa \<in> flow_domain (current_flow_impl state_impl) \<Longrightarrow>
        the (flow_lookup (current_flow_impl state_impl) xa) = current_flow state xa"
  using assms by simp

lemma same_gamma_abstract: "state = abstract state_impl \<Longrightarrow>
                  current_\<gamma>_impl state_impl = current_\<gamma> state"
  by simp

lemma same_actives_abstract: "state = abstract state_impl \<Longrightarrow>
                  actives_impl state_impl= actives state"
  by simp

lemma not_in_dom_id[simp]:"x \<notin> dom (rep_comp_lookup r_card_impl) \<Longrightarrow> abstract_rep_map r_card_impl x =  x"
    for x r_card_impl 
    by (simp add: abstract_rep_map_def domIff)
lemma not_in_dom_1[simp]:"x \<notin> dom (rep_comp_lookup r_card_impl) \<Longrightarrow> abstract_comp_map r_card_impl x = 1"
    for x r_card_impl 
    by (simp add: abstract_comp_map_def domIff)

end
end

subsection \<open>Forest Maintenance\<close>

locale loopA_impl_spec = 
loopA_spec where fst=fst +
algo_impl_spec where fst=fst
for fst::"'edge_type \<Rightarrow> 'a"
begin

lemmas update_alls[simp, intro] = rep_comp_update_all(1,3,4) not_blocked_update_all(1,3,4)

partial_function (tailrec) loopA_impl::"('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state_impl  
\<Rightarrow> ('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state_impl " where
"loopA_impl state = (let \<FF> = \<FF>_impl state;
                    f = current_flow_impl state;
                    b = balance_impl state;
                    r_card = representative_comp_card_impl state;
                    E' = actives_impl state;
                    to_rdg = conv_to_rdg_impl state;
                    \<gamma> = current_\<gamma>_impl state
                in (
case get_from_set  (\<lambda> e. the (flow_lookup f e) > 8 * real N *\<gamma>) E'  of (Some e) \<Rightarrow>
                            (let  x = fst e; y = snd e;
                             to_rdg' = add_direction to_rdg x y e;
                             cardx = prod.snd (the (rep_comp_lookup r_card x));
                             cardy = prod.snd (the (rep_comp_lookup r_card y));
                             (x, y) = (if cardx \<le> cardy 
                                       then (x,y) else (y,x));
                              \<FF>' =insert_undirected_edge_impl (fst e) (snd e) \<FF>;
                             x' = prod.fst (the (rep_comp_lookup r_card x)); 
                             y' = prod.fst (the (rep_comp_lookup r_card y));
                             Q = get_path x' y' \<FF>';
                             f' = (if the (bal_lookup b x') > 0 
                                   then augment_edges_impl f (the (bal_lookup b x')) (to_redge_path_impl to_rdg' Q) 
                                   else augment_edges_impl f (- the (bal_lookup b x')) (to_redge_path_impl to_rdg' (rev Q)));
                             b' = move_balance b x' y';
                            E'' = filter (\<lambda> d. {prod.fst (the (rep_comp_lookup r_card (fst d))) ,
                                                prod.fst (the (rep_comp_lookup r_card (snd d)))}
                                                 \<noteq> {x', y'} ) E';
                            r_card' = rep_comp_update_all 
                                (\<lambda> u urc. if prod.fst (urc) = x' \<or> prod.fst (urc) = y'
                                    then (y', cardx + cardy) else urc) r_card;
                            nb = not_blocked_impl state;
                            nb' = not_blocked_update_all (\<lambda> d b. 
                                   if d = e then True
                                   else if 
                                 {prod.fst (the (rep_comp_lookup r_card (fst d))),
                                  prod.fst (the (rep_comp_lookup r_card (snd d)))}
                                 = {x', y'} 
                                   then False
                                   else b) nb;
                            state' = state \<lparr>  \<FF>_impl := \<FF>', current_flow_impl := f',
                                    balance_impl := b', 
                                    actives_impl := E'', conv_to_rdg_impl := to_rdg',
                                    representative_comp_card_impl:= r_card',
                                    not_blocked_impl := nb'\<rparr>
                            in loopA_impl state')
                            | None \<Rightarrow> state))"

lemmas [code] = loopA_impl.simps
end

locale loopA_impl =
loopA where fst=fst +
loopA_impl_spec where fst=fst +
algo_impl where fst = fst 
for fst::"'edge_type \<Rightarrow> 'a"
begin


definition loopA_impl_upd::"('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state_impl  
\<Rightarrow> ('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state_impl " where
"loopA_impl_upd state = (let \<FF> = \<FF>_impl state;
                                     f = current_flow_impl state;
                    b = balance_impl state;
                    r_card = representative_comp_card_impl state;
                    E' = actives_impl state;
                    to_rdg = conv_to_rdg_impl state;
                    \<gamma> = current_\<gamma>_impl state;
                e = the (get_from_set  (\<lambda> e. the (flow_lookup f e) > 8 * real N *\<gamma>) E');
                     x = fst e; y = snd e;
                             to_rdg' = add_direction to_rdg x y e;
                             cardx = prod.snd (the (rep_comp_lookup r_card x));
                             cardy = prod.snd (the (rep_comp_lookup r_card y));
                             (x, y) = (if cardx \<le> cardy 
                                       then (x,y) else (y,x));
                              \<FF>' =insert_undirected_edge_impl (fst e) (snd e) \<FF>;
                             x' = prod.fst (the (rep_comp_lookup r_card x)); 
                             y' = prod.fst (the (rep_comp_lookup r_card y));
                             Q = get_path x' y' \<FF>';
                             f' = (if the (bal_lookup b x') > 0 
                                   then augment_edges_impl f (the (bal_lookup b x')) (to_redge_path_impl to_rdg' Q) 
                                   else augment_edges_impl f (- the (bal_lookup b x')) (to_redge_path_impl to_rdg' (rev Q)));
                             b' = move_balance b x' y';
                            E'' = filter (\<lambda> d.
                                    {prod.fst (the (rep_comp_lookup r_card (fst d))) , 
                                     prod.fst (the (rep_comp_lookup r_card (snd d)))} 
                                  \<noteq> {x', y'} ) E';
                            r_card' = rep_comp_update_all 
                                (\<lambda> u urc. if prod.fst (urc) = x' \<or> prod.fst (urc) = y'
                                    then (y', cardx + cardy) else urc) r_card;
                            nb = not_blocked_impl state;
                            nb' = not_blocked_update_all (\<lambda> d b. 
                                   if d = e then True
                                   else if 
                                 {prod.fst (the (rep_comp_lookup r_card (fst d))) ,
                                  prod.fst (the (rep_comp_lookup r_card (snd d)))}
                                 = {x', y'} 
                                   then False
                                   else b) nb;
                            state' = state \<lparr>  \<FF>_impl := \<FF>', current_flow_impl := f',
                                    balance_impl := b', 
                                    actives_impl := E'', conv_to_rdg_impl := to_rdg',
                                    representative_comp_card_impl:= r_card',
                                    not_blocked_impl := nb'\<rparr>
                            in  state')"

lemma loopA_impl_upd_compatible_with_abstr:
  assumes " abstract state_impl = state"
          "loopA_call_cond state"
          "adj_inv (\<FF>_impl state_impl)"
           "(\<And> x. neighb_inv (the (lookup (\<FF>_impl state_impl) x)))"
          "set_invar (actives state)"
          "\<E> = flow_domain (current_flow_impl state_impl)"
          "flow_invar (current_flow_impl state_impl)"
          "aux_invar state"
          "\<V> = bal_domain (balance_impl state_impl)"
          "bal_invar (balance_impl state_impl)"
          "to_set_of_adjacency (\<FF>_impl state_impl) = conv_domain (conv_to_rdg_impl state_impl)"
          "conv_invar (conv_to_rdg_impl state_impl)"
          "\<V> = rep_comp_domain (representative_comp_card_impl state_impl)"
          "rep_comp_invar (representative_comp_card_impl state_impl)"
          "not_blocked_invar (not_blocked_impl state_impl)"
          "\<E> = not_blocked_dom (not_blocked_impl state_impl)"

  shows   "abstract (loopA_impl_upd state_impl) = loopA_upd state"  
     "adj_inv (\<FF>_impl (loopA_impl_upd state_impl))" 
     "(\<forall> x. neighb_inv (the (lookup (\<FF>_impl (loopA_impl_upd state_impl)) x)))"        
      "set_invar (actives (loopA_upd state ))" 
      "\<E> = flow_domain (current_flow_impl (loopA_impl_upd state_impl))" 
      "flow_invar (current_flow_impl (loopA_impl_upd state_impl))"
      "\<V> = bal_domain (balance_impl (loopA_impl_upd state_impl))"
      "bal_invar (balance_impl (loopA_impl_upd state_impl))"
      "to_set_of_adjacency (\<FF>_impl (loopA_impl_upd state_impl)) 
       = conv_domain (conv_to_rdg_impl (loopA_impl_upd state_impl))"
      "conv_invar (conv_to_rdg_impl (loopA_impl_upd state_impl))"
      "\<V> = rep_comp_domain (representative_comp_card_impl (loopA_impl_upd state_impl))"
      "rep_comp_invar (representative_comp_card_impl (loopA_impl_upd state_impl))"
      "not_blocked_invar (not_blocked_impl (loopA_impl_upd state_impl))"
      "\<E> = not_blocked_dom (not_blocked_impl (loopA_impl_upd state_impl))"

proof(all \<open>rule loopA_call_condE[OF assms(2)]\<close>, goal_cases)
  case (1 f b r E' to_rdg \<gamma> e x y xx yy to_rdg' \<FF>' x' y' f' b' r' Q E'' state' cards
          cards' \<FF>_imp' nb nb')
  note state=this
  note defs = 1(1,2,3,4,5,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,26,27)
  define xy where "xy = (if cards x \<le> cards y then (x, y) else (y, x))"
  have xx_def: "xx =  prod.fst xy"
    using xy_def 1 by auto
  have yy_def: "yy =  prod.snd xy"
    using xy_def 1 by auto
  have F_rewrite[simp]: "to_graph \<FF>_imp' = \<FF>'"
    using insert_abstraction assms 1 
    by (auto simp add: from_aux_invar'(21))
     
  have e_in_E':"e \<in> to_set E'"
    using "1"(4) "1"(8) "1"(9) assms(5) set_get(2) by auto

  hence e_in_E: "e \<in> \<E>"
    using assms(8)  1 aux_invar_def invar_aux1_def by auto

  have E'_subs_E: "to_set E' \<subseteq> \<E>"
    using assms(8) defs aux_invar_def invar_aux1_def by auto

  have in_V[simp]: "x \<in> \<V>" "y \<in> \<V>" "xx \<in> \<V>" "yy \<in> \<V>"
    using "1"(10) e_in_E fst_E_V[of e] "1"(11) dVsI'(2)[of "make_pair e" "make_pair ` \<E>"]
           e_in_E defs make_pair[OF refl refl]
    by(auto simp add: xx_def yy_def xy_def)

  have x'_in_V[simp]:"x' \<in> \<V>" and y'_in_V[simp]:"y' \<in> \<V>" 
    using  1  from_aux_invar'(9) assms(8) by force+

  have forest_fit_together:"fit_together (\<FF> state) (\<FF>_imp state)"
    using from_aux_invar'(19,20) assms(8) fit_together_def
    by force

  have goodF:"goodF (\<FF>_imp state)" 
    by (simp add: Pair_graph_specs_from_aux_invar assms(8))
    have adj_invF: "adj_inv (\<FF>_imp state)"
      using assms(8) from_aux_invar'(18) by auto
    have goodF':"goodF \<FF>_imp'"
      by(auto intro: Pair_Graph_Specs_insert_undirected_edge_pres simp add: 1(15)  goodF adj_invF)
    have forest'_fit_together: "fit_together \<FF>' \<FF>_imp'" 
    using forest_fit_together 
    by (auto intro: fit_together_pres simp add:  defs(14,13)  goodF' goodF adj_invF)
  have x_not_y: "x \<noteq> y" 
    using e_in_E' assms(8) 
    unfolding 1(10) 1(11) aux_invar_def invar_aux11_def 1(4) by auto

  have x'_not_y': "x' \<noteq> y'"
  proof(rule,  goal_cases)
    case 1
    have "reachable (\<FF> state) x x' \<or> x = x'"
      using from_aux_invar(8,21)[OF assms(8), simplified invar_aux8_def invar_aux21_def]
             e_in_E' x_not_y xx_def yy_def xy_def state(3,10,11,16,17) 
      by(cases "cards x \<le> cards y")(force, insert 1, force)
    moreover have "reachable (\<FF> state) y y' \<or> y = y'"
      using  e_in_E' x_not_y from_aux_invar(8,21)[OF assms(8), simplified invar_aux8_def invar_aux21_def]
             state(3,10,11,16,17) xx_def yy_def xy_def
      by(cases "cards x \<le> cards y", simp) (auto simp add: 1)
    ultimately have " connected_component (\<FF> state) x = connected_component  (\<FF> state) y"
    using  1 reachable_trans[of _ x x' y] reachable_trans[of _ y y' x] reachable_sym[of _ y y']
             reachable_sym[of _ x y] 
    unfolding connected_component_def 
    by (smt (verit, best) reachable_trans Collect_cong)
  thus False
    using e_in_E' x_not_y from_aux_invar(11,21)[OF assms(8), simplified invar_aux11_def invar_aux21_def]
          state(4,10,11) xx_def yy_def xy_def 
    by simp
 qed

  have graph_invar_F':"graph_invar \<FF>'"
    using  x_not_y from_aux_invar'(14,21)[OF assms(8)] 1
    by(auto simp add: validF_def Vs_def)

  have adj_inv_F_imp':"adj_inv \<FF>_imp'"
    using 1(15) adj.invar_update assms(3) from_aux_invar'(18) assms(1,8)
    by (auto intro: adj_inv_pres_insert_undirected_edge)

   have superfluous_asm:"\<And>x. lookup \<FF>_imp' x \<noteq> None \<and> neighb_inv (the (lookup \<FF>_imp' x))"
     using fit_together_def forest'_fit_together by blast

   have " reachable \<FF>' x' xx \<or> xx =x'" 
     using in_V(3,4) assms(8) reachable_subset[of "\<FF> state" x' xx \<FF>']  reachable_sym 
           from_aux_invar'(8,21)  1(3,10,11,14,16)
     by force
   moreover have " reachable \<FF>' y' yy \<or> yy =y'" 
     using in_V(3,4) assms(8) reachable_subset[of "\<FF> state" y' yy \<FF>']  reachable_sym 
           from_aux_invar'(8,21)  1(3,10,11,14,17)
     by force
   moreover have " reachable \<FF>' xx yy" 
     by (simp add:  1(17) 1(16) 1(14) xx_def  yy_def xy_def 1(10) 1(11) edges_reachable insert_commute)
   ultimately have x'_reaches_y':" reachable \<FF>' x' y'" 
     by (meson reachable_trans reachable_sym)

   have there_is_q:"\<exists>q. vwalk_bet (digraph_abs \<FF>_imp') x' q y'"
     using x'_reaches_y'
     by(auto intro: from_reachable_to_dircted_walk[OF forest'_fit_together goodF'
                 graph_invar_F', of x' y'])

   then obtain q where q_prop:"vwalk_bet (digraph_abs \<FF>_imp') x' q y'"
     by auto

   have finiteF: "finite (to_graph \<FF>_imp')" 
     using F_rewrite graph_abs.finite_E graph_abs.intro graph_invar_F' by blast
  have x'_inVs:"x' \<in> Vs (to_graph \<FF>_imp')"
    using F_rewrite reachable_in_Vs(1)[OF x'_reaches_y'] by auto
   have walk_betw_Q: " walk_betw \<FF>' x' Q y'"
      using forest'_fit_together goodF' graph_invar_F'  q_prop  adj_inv_F_imp' 
             1(18) superfluous_asm x'_inVs x'_not_y'
      by (intro from_directed_walk_to_undirected_walk[OF _ _
              _ get_path_axioms(1)[of \<FF>_imp' x' _ y' Q]])

    hence Q_inF':"(List.set (edges_of_path Q)) \<subseteq>  \<FF>'"   
      by(auto intro!:  path_edges_subset[of \<FF>' Q] walk_between_nonempty_pathD(1))

   have distinct_Q[simp]: "distinct Q"
      using forest'_fit_together goodF' graph_invar_F'  q_prop  adj_inv_F_imp' 
             1(18) superfluous_asm x'_inVs x'_not_y'
      by (intro get_path_axioms(2)[of \<FF>_imp' x' _ y' Q])
     
    have Q_length: "length Q \<ge> 2" 
      using walk_betw_Q x'_not_y' 
      by (simp add: walk_betw_length)

    have Vs_F: "Vs \<FF>' \<subseteq> \<V>"
      using assms(8) in_V from_aux_invar'(15,21)[OF assms(8)] make_pair[OF refl refl, of e] state(10,11)
      by(auto simp add: dVsI'(1) dVsI'(2) e_in_E 1(14)  Vs_def)

    have Q_subset_V: "set Q \<subseteq> \<V>"
      using Vs_F in_edges_of_path'[OF _ Q_length] Vs_subset[OF Q_inF'] by blast

    have consist_to_rdg'[simp]: "consist to_rdg'"
      using from_aux_invar'(6)[OF assms(8)] make_pair[OF refl refl]
      by (auto simp add: assms(1-15) 1(12)  1(5) consist_def)

    have oedge_of_F_in_E: "oedge ` (to_rdgs to_pair to_rdg' \<FF>') \<subseteq> \<E>"
    proof(rule, goal_cases)
      case (1 d)
      then obtain rd where rd_props:"rd \<in> (to_rdgs to_pair to_rdg' \<FF>')" "oedge rd = d" by auto
      hence cases:"rd \<in> {to_rdg' (to_pair {x, y}), to_rdg' (prod.swap (to_pair {x,y}))} \<or>
             rd \<in> (to_rdgs to_pair to_rdg' (\<FF> state))"
         by (force simp add: to_rdgs_def state(14) state(10,11))
       show ?case
       proof(rule disjE[OF cases], goal_cases)
         case 1
         then show ?case 
           using  oedge_on_\<EE>  x_not_y e_in_E oedge_both_redges_image[of e] rd_props to_rdgs_def 
                  state(5,10,11,12)  assms(1-15) from_aux_invar'(2,21)[]  to_pair_axioms[of x y] 
                  make_pair[OF refl refl]
          by auto
       next
         case 2
         then obtain aa bb where aa_bb_prop:"aa \<noteq> bb" "rd \<in> {to_rdg' (to_pair {aa,bb}), to_rdg' (prod.swap (to_pair {aa,bb}))}"
                                 "{aa,bb} \<in> \<FF> state"
           by (auto simp add: to_rdgs_def)
         show ?case
         proof(cases "(aa,bb) = make_pair e \<or> (bb, aa) = make_pair e")
           case True
           hence aa_bb_is_x_y:"{aa, bb} = {x,y}"
             using state(10) state(11) make_pair[OF refl refl] by auto
           hence " oedge (to_rdg' (to_pair {aa,bb})) = e " "oedge (to_rdg' (prod.swap (to_pair {aa,bb}))) = e"
             using  to_pair_axioms  x_not_y  state (12,10,11) make_pair[OF refl refl]
             by force+         
           hence " oedge ` {to_rdg' (to_pair {aa,bb}), to_rdg' (prod.swap (to_pair {aa,bb}))} = {e}" 
             by simp
           thus ?thesis
             using aa_bb_prop(2) e_in_E rd_props(2) by auto
         next
           case False
           hence "to_rdg' (to_pair {aa,bb}) = to_rdg (to_pair {aa,bb})"
                 "to_rdg' (prod.swap (to_pair {aa,bb})) = to_rdg (prod.swap (to_pair {aa,bb}))"
             using  to_pair_axioms[of aa bb, OF aa_bb_prop(1) refl]  state(10,11) aa_bb_prop(2-)
             by(auto simp add:  state(12))
           hence "rd \<in> (to_rdgs to_pair to_rdg (\<FF> state))"
             using  aa_bb_prop by (auto simp add: to_rdgs_def)
           then show ?thesis 
             using from_aux_invar'(3,21) assms(8) state(5) rd_props(2)
             by force
         qed
       qed
     qed

      have pair_edges_of_Q_in_F:"set (vwalk_arcs Q) \<subseteq> to_set_of_adjacency \<FF>_imp'"
      proof(rule, goal_cases )
        case (1 d)
        hence "{prod.fst d, prod.snd d} \<in> set (edges_of_path Q)" 
          using vwalk_arcs_to_edges_of_path by fast
        then show ?case 
          using forest'_fit_together Q_inF'  F_rewrite vwalk_arcs_to_edges_of_path
          by (auto simp add: to_graph_def to_set_of_adjacency_def fit_together_def)
      qed

      have pair_edges_of_rev_Q_in_F:"set (vwalk_arcs (rev Q)) \<subseteq> to_set_of_adjacency \<FF>_imp'"
      proof(rule, goal_cases )
        case (1 d)
        hence "{prod.fst d, prod.snd d} \<in> set (edges_of_path (rev Q))" 
          using vwalk_arcs_to_edges_of_path by fast
        then show ?case 
          using  forest'_fit_together set_rev[of " (edges_of_path Q)"] Q_inF' edges_of_path_rev[of Q]
          by (auto simp add: to_graph_def to_set_of_adjacency_def fit_together_def)
      qed

  have from_edge_to_verts: "a \<in> \<V>" "b \<in> \<V>" if "(a, b) \<in> make_pair ` \<E>" for a b
    using that by auto

  define  \<FF>_impl where  "\<FF>_impl = Algo_state_impl.\<FF>_impl state_impl"
  define f_impl where "f_impl = current_flow_impl state_impl"
  define b_impl where "b_impl = balance_impl state_impl"
  define r_card_impl where "r_card_impl = representative_comp_card_impl state_impl"
  define E'_impl where "E'_impl = actives_impl state_impl"
  define to_rdg_impl where "to_rdg_impl = conv_to_rdg_impl state_impl"
  define \<gamma>_impl where "\<gamma>_impl = current_\<gamma>_impl state_impl"
  define e_impl where "e_impl = the( get_from_set 
                            (\<lambda> e. the (flow_lookup f_impl e) > 8 * real N *\<gamma>_impl) E'_impl)"
  define x_impl where "x_impl = fst e_impl"
  define y_impl where "y_impl = snd e_impl"
  define to_rdg'_impl where "to_rdg'_impl = add_direction to_rdg_impl x_impl y_impl e_impl"
  define cardx where "cardx = prod.snd (the (rep_comp_lookup r_card_impl x_impl))"
  define cardy where "cardy = prod.snd (the (rep_comp_lookup r_card_impl y_impl))"
  define xy_impl where " xy_impl = (if cardx \<le> cardy
                                       then (x_impl,y_impl) else (y_impl,x_impl))"
  define xx_impl where "xx_impl = prod.fst xy_impl"
  define yy_impl where "yy_impl = prod.snd xy_impl"
  define \<FF>'_impl where "\<FF>'_impl =insert_undirected_edge (fst e_impl) (snd e_impl) \<FF>_impl"
  define x'_impl where "x'_impl = prod.fst (the (rep_comp_lookup r_card_impl xx_impl))" 
  define y'_impl where "y'_impl = prod.fst (the (rep_comp_lookup r_card_impl yy_impl))"
  define Q_impl where "Q_impl = get_path x'_impl y'_impl \<FF>'_impl"
  define f'_impl where  "f'_impl = (if (the (bal_lookup b_impl x'_impl)) > 0 
                                   then augment_edges_impl f_impl (the (bal_lookup b_impl x'_impl)) (to_redge_path_impl to_rdg'_impl Q_impl) 
                                   else augment_edges_impl f_impl (- (the (bal_lookup b_impl x'_impl))) (to_redge_path_impl to_rdg'_impl (rev Q_impl)))"
  define b'_impl where "b'_impl = move_balance b_impl x'_impl y'_impl"
  define E''_impl where "E''_impl = filter (\<lambda> d. 
{prod.fst (the (rep_comp_lookup r_card_impl (fst d))) ,
 prod.fst (the (rep_comp_lookup r_card_impl (snd d)))} \<noteq> {x'_impl, y'_impl} ) E'_impl"
  define r_card'_impl where "r_card'_impl = rep_comp_update_all 
                                (\<lambda> u urc. if prod.fst (urc) = x'_impl \<or> prod.fst (urc) = y'_impl
                                    then (y'_impl, cardx + cardy) else urc) r_card_impl"
  define nb_impl where "nb_impl = not_blocked_impl state_impl"
  define nb'_impl where "nb'_impl = not_blocked_update_all (\<lambda> d b. 
                                   if d =  e_impl then True
                                   else if 
{prod.fst (the (rep_comp_lookup r_card_impl (fst d))) , prod.fst (the (rep_comp_lookup r_card_impl (snd d)))}
                                 = {x'_impl, y'_impl} 
                                   then False
                                   else b) nb_impl"
  define state'_impl where "state'_impl = state_impl 
              \<lparr>  \<FF>_impl := \<FF>'_impl, current_flow_impl := f'_impl,
                balance_impl := b'_impl,
                actives_impl := E''_impl, conv_to_rdg_impl := to_rdg'_impl, 
                representative_comp_card_impl := r_card'_impl,
                not_blocked_impl := nb'_impl\<rparr>"
  note defs_impl = state'_impl_def \<FF>'_impl_def e_impl_def \<gamma>_impl_def E'_impl_def
              f_impl_def \<FF>_impl_def f'_impl_def b_impl_def x'_impl_def r_card'_impl_def r_card_impl_def
              xx_impl_def xy_impl_def  x_impl_def y_impl_def b'_impl_def Q_impl_def cardx_def cardy_def
              to_rdg'_impl_def y'_impl_def to_rdg_impl_def yy_impl_def E''_impl_def nb_impl_def
              nb'_impl_def

   have state'_is: "state' = loopA_upd state"
    unfolding loopA_upd_def Let_def 1 xx_def yy_def xy_def 
    apply(rule Algo_state.equality)
    by(auto split: prod.split)

  have state'_impl_is:"state'_impl = loopA_impl_upd state_impl"
    unfolding loopA_impl_upd_def Let_def defs_impl  
    apply(subst split_beta)+
    apply(rule Algo_state_impl.equality)
    by(auto split: prod.split)    

  text \<open>basic reductions\<close>

 have gammas_coincide[simp]: "\<gamma>_impl = \<gamma>" "current_\<gamma> state = current_\<gamma>_impl state_impl"
   using defs defs_impl assms(1) same_gamma_abstract by presburger+
  have actives_coincide[simp]: "E'_impl = E'"
    using 1 E'_impl_def assms  same_actives_abstract by fast
  have Fs_coincide[simp]: " \<FF>_impl = \<FF>_imp state" 
    using assms \<FF>_impl_def by auto
   have f_is[simp]: "abstract_flow_map f_impl = f"
     using assms f_impl_def 1(1) by simp
    have impl_coincidence[simp]: "abstract_not_blocked_map nb_impl = nb"
      by (simp add: assms(1) nb_impl_def state(24))
    have returns_coincide[simp]: "return state = return_impl state_impl"
      by (simp add: assms(1))
    have reps_coincide[simp]:"abstract_rep_map r_card_impl = r"
      by (simp add: assms(1) r_card_impl_def state(3))
    have cards_coincide[simp]: "abstract_comp_map r_card_impl = cards"
      by (simp add: assms(1) r_card_impl_def state(7))
    have balanc_coincide[simp]: "abstract_bal_map b_impl = b"
      by (simp add: assms(1) b_impl_def state(2))
    have to_rdg_coincide[simp]: "abstract_conv_map to_rdg_impl = to_rdg"
      by (simp add: assms(1) state(5) to_rdg_impl_def)
    text\<open>Invariants\<close>

    have impl_invars[simp]: "not_blocked_invar nb_impl"
      by (simp add: assms(15) nb_impl_def)
    have flow_invar[simp]: "flow_invar f_impl"
      by (simp add: assms(7) f_impl_def)
    have set_invar_E'[simp]:"set_invar E'"
      by (simp add: assms(5) state(4))
    have r_comp_impl_inv[simp]: "rep_comp_invar  r_card_impl" 
      by (simp add: assms(14) r_card_impl_def)
    have bal_invar[simp]: "bal_invar b_impl"
      by (simp add: assms(10) b_impl_def)
    have to_rdg_inv[simp]: "conv_invar to_rdg_impl"
      by (simp add: assms(12) to_rdg_impl_def)

  text \<open>Basic reductions applied\<close>

   have flows_coincide[simp]: "\<And> e. e \<in> \<E> \<Longrightarrow> the (flow_lookup f_impl e) = f e"
    using "1"(1) assms(1) assms(6) f_impl_def  elem_mono same_flow_provided_domain
    by (simp add: subsetD)
   have balances_coincide[simp]: "\<And> x. x \<in> \<V> \<Longrightarrow> the (bal_lookup b_impl x) = b x"
     using assms(9) 1(2) b_impl_def assms(1)
     by auto
  have cards_coincide': "\<And> x. x \<in> dom (rep_comp_lookup r_card_impl) 
                 \<Longrightarrow> prod.snd (the (rep_comp_lookup r_card_impl x)) = cards x "
    using abstractE(4) abstract_card assms(1) r_card_impl_def state(7) by simp
  have cards_coincide[simp]: "\<And> x. x \<in> \<V> \<Longrightarrow>prod.snd (the (rep_comp_lookup r_card_impl x)) = cards x"
    using assms(13) cards_coincide' r_card_impl_def by blast
  have reps_coincide'[simp]: "\<And> x. x \<in> dom (rep_comp_lookup r_card_impl) 
                        \<Longrightarrow> prod.fst (the (rep_comp_lookup r_card_impl x)) = r x"
    using abstractE(3) abstract_rep assms(1) r_card_impl_def state(3) by simp
  hence reps_coincide[simp]: "\<And> x. x \<in> \<V> \<Longrightarrow>prod.fst (the (rep_comp_lookup r_card_impl x)) = r x"
    using assms(13) 
    by (simp add: domIff r_card_impl_def  subset_iff)
    have V_subs_dom: "\<V> \<subseteq> dom (rep_comp_lookup r_card_impl)"
      by (simp add: assms(13) r_card_impl_def)
    have e_not_blocked_vertes_in_rep_dom[simp]:
              "e \<in> not_blocked_dom nb_impl \<Longrightarrow> fst e \<in> rep_comp_domain r_card_impl"
              "e \<in> not_blocked_dom nb_impl \<Longrightarrow> snd e \<in> rep_comp_domain r_card_impl" for e
      using  fst_E_V  V_subs_dom assms(16) nb_impl_def snd_E_V by fast+
   have not_blocked_in_dom[simp]:"v \<in> not_blocked_dom nb_impl \<Longrightarrow> the (not_blocked_lookup nb_impl v) = nb v" for v
     using abstract_not_blocked_map_def[of nb_impl] assms(1) nb_impl_def state(24)
     by auto
    have card_is_1_outside_dom: "v \<notin> rep_comp_domain r_card_impl \<Longrightarrow> cards v = 1" for v
      using assms(1) r_card_impl_def state(7)  not_in_dom_1 by fastforce
   have predicates_coincide: "d \<in> to_set E' \<Longrightarrow> (8 * real N * \<gamma>  < f d) = (8 * real N * \<gamma>_impl < the (flow_lookup f_impl d))" for d
     using flows_coincide  E'_subs_E by fastforce

   text \<open>intermediate reductions\<close>

   have es_coincide[simp]: "e_impl = e"
     unfolding e_impl_def 1(9)
     apply(rule arg_cong[OF set_get']) 
     using e_impl_def predicates_coincide f_impl_def assms 1(1-10) 
     by fastforce+
  have xs_coincide[simp]: "x_impl = x" and ys_coincide[simp]: "y_impl = y"
    using "1"(10) x_impl_def  "1"(11)  y_impl_def by auto  
  have x's_coincide[simp]: "x'_impl = x'" and y's_coincide[simp]: "y'_impl = y'"
    using  cardx_def cardy_def state(16,17) x'_impl_def xx_def xx_impl_def xy_def xy_impl_def 
           y'_impl_def yy_def yy_impl_def 
    by auto
  have Fs_coincide[simp]: "\<FF>'_impl = \<FF>_imp'"
    using  Fs_coincide by (auto simp add: 1(15) \<FF>'_impl_def)
  have Qs_coincideee[simp]: "Q_impl = Q"
    by (auto simp add: 1(18) Q_impl_def)

  text \<open>Preconditions\<close>
  have e_is_x_y: "make_pair e = (x,y)"
    by (simp add: state(10) state(11) make_pair)
  have oedges_of_Q_in_domain[simp]: "oedge ` set (to_redge_path to_rdg' Q) \<subseteq> flow_domain f_impl"
      using oedge_of_to_redgepath_subset[OF distinct_Q consist_to_rdg'] oedge_of_F_in_E 
            assms(6) f_impl_def  image_mono[OF to_rdg_mono[OF Q_inF', of to_pair to_rdg'], of oedge]  
      by auto
    have set_of_oedges_in_domainnnn:"set (map oedge (to_redge_path to_rdg' Q)) \<subseteq> flow_domain f_impl"
      by simp
    have x'_y'_bal_domain[simp]:"x' \<in> bal_domain b_impl" "y' \<in>bal_domain b_impl"
      using assms(9) b_impl_def by(auto simp add: in_mono)   
    have to_rdg'_coincide[simp]: "abstract_conv_map to_rdg'_impl = to_rdg'" 
      using 1(12) e_is_x_y to_rdg'_impl_def by simp
    have"x \<notin> rep_comp_domain r_card_impl \<Longrightarrow> r x = x" for x
      using assms(1) not_in_dom_id by fastforce
    hence outside_rep_dom[simp]:"v \<notin> rep_comp_domain r_card_impl \<Longrightarrow> (if r v = x' \<or> r v = y' then y' else r v) = v" for v
      using V_subs_dom x'_in_V y'_in_V
      by(subst if_not_P, fastforce, simp)
   have symmetric_set_of_F'_in_domain:"to_set_of_adjacency \<FF>_imp' = conv_domain to_rdg'_impl"
     using  assms(1,3,4,11)  x_not_y 
       by (auto simp add: assms(12) to_rdg_impl_def 1(15,10,11) to_rdg'_impl_def)
   have transformed_paths_coincide[simp]:
       "to_redge_path_impl to_rdg'_impl Q = to_redge_path to_rdg' Q"
        "to_redge_path_impl to_rdg'_impl (rev Q) = to_redge_path to_rdg' (rev Q)"
     using   symmetric_set_of_F'_in_domain  pair_edges_of_Q_in_F  pair_edges_of_rev_Q_in_F 
             e_is_x_y   by (auto simp add: 1(12) to_rdg'_impl_def)
  have filter_predicates_coincide': "d \<in> \<E> \<Longrightarrow> u = fst d \<Longrightarrow> v = snd d \<Longrightarrow>
          ( {prod.fst (the (rep_comp_lookup r_card_impl u)) ,
     prod.fst (the (rep_comp_lookup r_card_impl v))} = {x', y'} ) = ({r u, r v} = {x', y'})" for u v d
    using from_edge_to_verts make_pair[OF refl refl] 
    by (simp add: assms(16) nb_impl_def)
  have filter_predicates_coincide''a[simp]: "d \<in> not_blocked_dom nb_impl \<Longrightarrow>
               make_pair d = (u, v) \<Longrightarrow>
         ( {prod.fst (the (rep_comp_lookup r_card_impl u)) ,
     prod.fst (the (rep_comp_lookup r_card_impl v))} = {x', y'} ) = ({r u, r v} = {x', y'})" for u v d
    using from_edge_to_verts[of u v] make_pair[OF refl refl, of d] 
          reps_coincide[of u] reps_coincide[of v]
    by (simp add: assms(16) filter_predicates_coincide' nb_impl_def)

    have outside_card_dom:"v \<notin> rep_comp_domain r_card_impl 
             \<Longrightarrow> (if r' v = y' then cards x + cards y else cards v) = 1" for v
      apply(subst if_not_P, subst state(22), subst outside_rep_dom, simp) 
      using V_subs_dom card_is_1_outside_dom  y'_in_V by fast+ 
   have not_blocked_outside_dom:"v \<notin> not_blocked_dom nb_impl \<Longrightarrow> nb' v = False" for v
     using abstract_not_blocked_map_def[of nb_impl] assms(1) assms(16) e_in_E nb_impl_def state(24)
           state(26) by auto
  have not_blocked_coincide[simp]: "abstract_not_blocked_map nb'_impl = nb'"
    apply(rule not_blocked_update_all_homo_card[of nb_impl, OF refl])
    using  nb'_impl_def 
    using 1(26)  not_blocked_outside_dom by simp+

  have new_flows_coincide[simp]:"abstract_flow_map f'_impl = f'"
    by (auto simp: f'_impl_def  1(19) oedge_of_to_redge_path_rev)

  have new_balances_coincide[simp]: " abstract_bal_map b'_impl = b'"
    by (auto simp add: b'_impl_def 1(20))

  have new_actives_coincide[simp]: "E''_impl = E''"
    using filter_predicates_coincide' E'_subs_E         
    by(auto simp add: 1(21) E''_impl_def intro!: set_filter(2)) blast+

  have new_reps_coincide[simp]: "abstract_rep_map r_card'_impl = r'"
    by (auto simp add: r_card'_impl_def  state(22) )

  have new_cards_coincide[simp]: "abstract_comp_map r_card'_impl = cards'"
    using  outside_card_dom      
    by (auto simp add: state(22,23) r_card'_impl_def  cardx_def cardy_def)
          
  have "abstract state'_impl = state'"
    apply(subst 1(27), subst state'_impl_def)
    by(auto simp add: abstractE' simp del: abstractE)
   
   thus "abstract (loopA_impl_upd state_impl) = loopA_upd state"
     using state'_is state'_impl_is by simp

  show "adj_inv (Algo_state_impl.\<FF>_impl (loopA_impl_upd state_impl))"
    using sym[OF state'_impl_is] 1(24) state'_impl_def adj_inv_F_imp' 
    by(auto simp add: abstractE' simp del: abstractE)

  show "\<forall> x. neighb_inv (the (lookup (Algo_state_impl.\<FF>_impl (loopA_impl_upd state_impl)) x))" 
    using  sym[OF state'_impl_is] 1(24) state'_impl_def  superfluous_asm 
    by(auto simp add: abstractE' simp del: abstractE)

  show "set_invar (actives (loopA_upd state))"
    using sym[OF state'_is]  1(27) state'_impl_def 
    by (simp add: assms(5) invar_filter state(21) state(4))

  have "\<E> = flow_domain f'_impl"
    using   oedge_of_to_redge_path_rev[OF distinct_Q consist_to_rdg'] assms(7)  assms(6) 
          f_impl_def f'_impl_def oedges_of_Q_in_domain by auto
    
  thus " \<E> = flow_domain (current_flow_impl (loopA_impl_upd state_impl))"
    using state'_impl_is state'_impl_def  by force

  show "\<V> = bal_domain (balance_impl (loopA_impl_upd state_impl))"
    using sym[OF state'_impl_is] 1(24) state'_impl_def  b'_impl_def  assms(10) assms(9) b_impl_def 
          x'_y'_bal_domain by simp

  show "flow_invar (current_flow_impl (loopA_impl_upd state_impl))"
    using state'_impl_is state'_impl_def  assms(7)  f'_impl_def f_impl_def 
          oedge_of_to_redge_path_rev[OF distinct_Q consist_to_rdg'] oedges_of_Q_in_domain transformed_paths_coincide(1)
          transformed_paths_coincide(2) by force

  show "bal_invar (balance_impl (loopA_impl_upd state_impl))"
    using  sym[OF state'_impl_is] 1(24) state'_impl_def  b'_impl_def  assms(10) b_impl_def
    by auto

  show "to_set_of_adjacency (Algo_state_impl.\<FF>_impl (loopA_impl_upd state_impl))
       = conv_domain (conv_to_rdg_impl (loopA_impl_upd state_impl))"
    using sym[OF state'_impl_is] state'_impl_def symmetric_set_of_F'_in_domain 
    by(auto simp add: abstractE' simp del: abstractE)

  show "conv_invar (conv_to_rdg_impl (loopA_impl_upd state_impl))"
    using sym[OF state'_impl_is] state'_impl_def assms(12) to_rdg'_impl_def to_rdg_impl_def
    by simp
  note  rep_comp_update_all(1,3,4)[simp]
  show "\<V> = rep_comp_domain (representative_comp_card_impl (loopA_impl_upd state_impl))"
    using  assms(13) assms(14) sym[OF state'_impl_is] 
          state'_impl_def r_card'_impl_def  r_card_impl_def 
    by simp

  show "rep_comp_invar (representative_comp_card_impl (loopA_impl_upd state_impl))"
    using  rep_comp_update_all(3)  assms(13) assms(14) sym[OF state'_impl_is] state'_impl_def 
           r_card'_impl_def  r_card_impl_def 
    by simp
  note  not_blocked_update_all(1,3,4)[simp]
  show "not_blocked_invar (not_blocked_impl (loopA_impl_upd state_impl))"
    using  assms(15) sym[OF state'_impl_is] state'_impl_def nb_impl_def nb'_impl_def
    by simp

  show "\<E> = not_blocked_dom (not_blocked_impl (loopA_impl_upd state_impl))"
    using  assms(15) assms(16)  nb_impl_def nb'_impl_def sym[OF state'_impl_is] state'_impl_def 
    by simp    
qed   

lemma loopA_impl_upd_compatible_with_abstr':
  assumes "abstract state_impl = state"
          "loopA_call_cond state"
          "aux_invar state"
          "implementation_invar state_impl"

  shows   "abstract (loopA_impl_upd state_impl) = loopA_upd state"  
          "implementation_invar (loopA_impl_upd state_impl)"
  subgoal first
  using loopA_impl_upd_compatible_with_abstr[of state_impl state] assms from_aux_invar'(17)
  by(auto simp add: implementation_invar_def abstract_def Let_def abstractE' simp del: abstractE)
  subgoal
  apply(rule implementation_invarI)
  prefer 4
    subgoal
      using assms 
      by (intro loopA_impl_upd_compatible_with_abstr(5)[of state_impl state])
         (auto simp add: implementation_invar_def)
    using assms invar_aux_pres_one_step 
               apply( all\<open>(intro loopA_impl_upd_compatible_with_abstr[of state_impl state]; 
                           auto simp add: implementation_invar_def from_aux_invar'(17) invar_aux_pres_one_step)?\<close>)
    by(auto simp add: first from_aux_invar'(17) invar_aux_pres_one_step)
  done

lemma loopA_impl_upd_compatible_with_abstr'':
  assumes "state = abstract state_impl"
          "loopA_call_cond state"
          "aux_invar state"
          "implementation_invar state_impl"

shows   "loopA_upd state = abstract (loopA_impl_upd state_impl) \<and>
        implementation_invar (loopA_impl_upd state_impl)"
  using loopA_impl_upd_compatible_with_abstr' assms by auto

lemma abstract_impl_same_whole_loopA:
  assumes "loopA_dom state"
          "abstract state_impl = state"
          "aux_invar state"
          "implementation_invar state_impl"

shows   "loopA state = abstract (loopA_impl state_impl) \<and>
         implementation_invar (loopA_impl state_impl)"
  using assms(2-)
proof(induction arbitrary: state_impl rule: loopA_induct[OF assms(1)])
  case (1 state)
  note IH=this
  have actives_subs_E:"to_set (actives state) \<subseteq> \<E>"
    using IH(5)[simplified implementation_invar_def] IH(3)[simplified abstract_def Let_def]
          IH(4)[simplified aux_invar_def invar_aux1_def]
    by simp
    have same_actives:"actives_impl state_impl = actives state"
      unfolding sym[OF IH(3)] abstract_def Let_def by auto
    have choice_coincidence:" \<And> e. e \<in> to_set (actives_impl state_impl) \<Longrightarrow> 
                (8 * real N * current_\<gamma>_impl state_impl
              < the (flow_lookup (current_flow_impl state_impl) e)) =
                  ( 8 * real N * current_\<gamma> state
              < current_flow state e)"
      using actives_subs_E  IH(5)[simplified implementation_invar_def]
      by(auto simp add:abstract_flow_map_def sym[OF IH(3)] abstract_def Let_def abstractE' simp del: abstractE)
    have gamma_coincidence: " current_\<gamma> state =  current_\<gamma>_impl state_impl"
      by(auto simp add: sym[OF IH(3)] abstract_def Let_def abstractE' simp del: abstractE)
    have flows_coincide: "current_flow state = 
                          abstract_flow_map (current_flow_impl state_impl)"
      by(auto simp add: sym[OF IH(3)] abstract_def Let_def abstractE' simp del: abstractE)
    have set_invar: "set_invar (actives state)"
      using "1.prems"(2) invar_aux17_def invar_aux17_from_aux_invar by auto
    have set_invar_impl: "set_invar (actives_impl state_impl)"
      using \<open>actives_impl state_impl = actives state\<close> set_invar by force
  show ?case
  proof(cases rule: loopA_cases[of state])
    case 1
    then show ?thesis 
      unfolding  IH(3) 
      apply(subst loopA_simps(2), simp add: IH(1,3))
      apply(rule loopA_ret_condE, simp)
      apply(subst loopA_impl.simps)+
      using choice_coincidence[simplified gamma_coincidence flows_coincide]
            set_get(4)[OF set_invar,
                       OF  choice_coincidence[simplified gamma_coincidence flows_coincide]]
            sym[OF IH(3)] IH(5)
      by (auto simp add: case_simp(2) abstract_def Let_def  abstractE' simp del: abstractE)
   next
     case 2
     note call=this
     have set_inv_abstr:"set_invar (actives (abstract state_impl))"
       using IH(5)[simplified implementation_invar_def]  IH(3) 
       by(auto simp add: abstract_def Let_def abstractE' simp del: abstractE)
     then show ?thesis
       apply(subst loopA_simps(1)[OF IH(1) 2])
       apply(subst loopA_impl.simps)
       apply(subst loopA_impl.simps)
       apply(rule loopA_call_condE[OF 2])
       unfolding Let_def
       apply(subst case_simp(1))
       subgoal
         using choice_coincidence[simplified gamma_coincidence flows_coincide] 
            set_get(4)[OF set_invar[simplified sym[OF IH(3)] abstract_def Let_def, simplified],
                       OF  choice_coincidence[simplified gamma_coincidence flows_coincide]]  
         by(auto simp add: abstract_def Let_def sym[OF IH(3)] abstractE' simp del: abstractE)
       apply(subst case_simp(1))
       subgoal
         using choice_coincidence[simplified gamma_coincidence flows_coincide] 
            set_get(4)[OF set_invar[simplified sym[OF IH(3)] abstract_def Let_def, simplified],
                       OF  choice_coincidence[simplified gamma_coincidence flows_coincide]]
            same_actives IH(3) 
         by auto
       apply(rule P_of_case_prod_I[of "if _ then _ else _"])
       apply(rule iffD2[rotated])
       apply( rule IH(2)[OF 2, of "loopA_impl_upd state_impl"])
       using loopA_impl_upd_compatible_with_abstr'(1)[OF IH(3) call IH(4) IH(5)] 
             invar_aux_pres_one_step[OF IH(4) call] 
             loopA_impl_upd_compatible_with_abstr''[OF sym[OF IH(3)] call IH(4) IH(5)] 
      unfolding loopA_impl_upd_def Let_def by auto       
   qed
 qed

lemma abstract_impl_same_whole_loopA':
  assumes "loopA_dom state"
          "abstract state_impl = state"
          "aux_invar state"
          "implementation_invar state_impl"

shows   "abstract (loopA_impl state_impl) = loopA state"
        "implementation_invar (loopA_impl state_impl)"
  using abstract_impl_same_whole_loopA assms by auto

lemma abstract_impl_same_sholw_loop:
  assumes "loopA_dom state" 
          "(abstract state_impl) = state"
          " adj_inv (\<FF>_impl state_impl)"
          "(\<And> x. neighb_inv (the (lookup (\<FF>_impl state_impl) x)))"
          "set_invar (actives state)"
          "\<E> = flow_domain (current_flow_impl state_impl)"
          "flow_invar (current_flow_impl state_impl)"
          "aux_invar state"
          "\<V> = bal_domain (balance_impl state_impl)"
          "bal_invar (balance_impl state_impl)"
          "to_set_of_adjacency (\<FF>_impl state_impl) = conv_domain (conv_to_rdg_impl state_impl)"
          "conv_invar (conv_to_rdg_impl state_impl)"
          "\<V> = rep_comp_domain (representative_comp_card_impl state_impl)"
          "rep_comp_invar (representative_comp_card_impl state_impl)"
          "not_blocked_invar (not_blocked_impl state_impl)"
          "\<E> = not_blocked_dom (not_blocked_impl state_impl)"
    shows "abstract (loopA_impl state_impl) = loopA (abstract state_impl)"
  using abstract_impl_same_whole_loopA[OF assms(1,2,8)] assms
  unfolding implementation_invar_def abstract_def Let_def
  by auto
end

subsection \<open>Ordinary Augmentations\<close>

locale loopB_impl_spec = 
algo_spec where fst = fst and get_from_set = get_from_set and \<E>_impl = "\<E>_impl ::'d" +
 algo_impl_spec where fst = fst and get_from_set= "get_from_set ::('edge_type \<Rightarrow> bool) \<Rightarrow> 'd \<Rightarrow> 'edge_type option"
and flow_empty = "flow_empty::'e" and bal_empty = "bal_empty::'f" and rep_comp_empty = "rep_comp_empty::'g"
and conv_empty = "conv_empty::'h" and not_blocked_empty = "not_blocked_empty::'i"
for fst::"'edge_type \<Rightarrow> 'a" and get_from_set
and flow_empty and bal_empty and rep_comp_empty and conv_empty and not_blocked_empty
+
  fixes get_source_target_path_a_impl
        ::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl  \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'edge_type Redge list) option" 
    and get_source_target_path_b_impl
        ::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl  \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'edge_type Redge list) option" 
and get_source_impl::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl \<Rightarrow> 'a option"
and get_target_impl::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl \<Rightarrow> 'a option"
and test_all_vertices_zero_balance::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl \<Rightarrow> bool"
begin
partial_function (tailrec) loopB_impl::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl  
\<Rightarrow> ('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl " where
  "loopB_impl state = (let
                    f = current_flow_impl state;
                    b = balance_impl state;
                    \<gamma> = current_\<gamma>_impl state
 in (if test_all_vertices_zero_balance state then state \<lparr> return_impl:=success\<rparr> 
     else (case get_source_impl state of Some s \<Rightarrow> 
            (case get_source_target_path_a_impl state s of Some (t, P) \<Rightarrow>
                   (let f' = augment_edges_impl f \<gamma> P;
                       b' = move b \<gamma> s t;
                       state' = state \<lparr> current_flow_impl := f', balance_impl := b'\<rparr> in   
                           loopB_impl state')
                 | None \<Rightarrow> state \<lparr> return_impl := failure\<rparr>) 
     | None \<Rightarrow> 
          (case get_target_impl state of Some t \<Rightarrow> 
            (case get_source_target_path_b_impl state t of Some (s, P) \<Rightarrow>
                   (let f' = augment_edges_impl f \<gamma> P;
                       b' = move b \<gamma> s t;
                       state' = state \<lparr> current_flow_impl := f', balance_impl := b'\<rparr> in   
                           loopB_impl state')
                 | None \<Rightarrow> state \<lparr> return_impl := failure\<rparr>)
         | None \<Rightarrow> state \<lparr> return_impl := notyetterm\<rparr>
    ))))"

lemmas [code] = loopB_impl.simps

definition loopB_succ_impl::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl 
\<Rightarrow> ('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl " where
  "loopB_succ_impl state = (let
                    f = current_flow_impl state;
                    b = balance_impl state;
                    \<gamma> = current_\<gamma>_impl state
                       in state \<lparr> return_impl:=success\<rparr>)"

definition loopB_fail_impl::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl  
\<Rightarrow> ('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl " where
  "loopB_fail_impl state = (let
                    f = current_flow_impl state;
                    b = balance_impl state;
                    \<gamma> = current_\<gamma>_impl state
                       in state \<lparr> return_impl:=failure\<rparr>)"

definition loopB_call1_upd_impl::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl 
\<Rightarrow> ('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl " where
  "loopB_call1_upd_impl state = (let
                    f = current_flow_impl state;
                    b = balance_impl state;
                    \<gamma> = current_\<gamma>_impl state;
                    s = the (get_source_impl state); 
                    (t, P) =  the (get_source_target_path_a_impl state s);
                    f' = augment_edges_impl f \<gamma> P;
                       b' = move b \<gamma> s t;
                       state' = state \<lparr> current_flow_impl := f', balance_impl := b'\<rparr> in   
                           state')"

definition loopB_call2_upd_impl::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl  
\<Rightarrow> ('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl" where
  "loopB_call2_upd_impl state = (let
                    f = current_flow_impl state;
                    b = balance_impl state;
                    \<gamma> = current_\<gamma>_impl state;
                    t = the (get_target_impl state); 
                    (s, P) =  the (get_source_target_path_b_impl state t);
                    f' = augment_edges_impl f \<gamma> P;
                       b' = move b \<gamma> s t;
                       state' = state \<lparr> current_flow_impl := f', balance_impl := b'\<rparr> in   
                           state')"

definition loopB_cont_impl::"('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl 
\<Rightarrow> ('e, 'f, 'c, 'h, 'd, 'g, 'i) Algo_state_impl " where
  "loopB_cont_impl state = (let
                    f = current_flow_impl state;
                    b = balance_impl state;
                    \<gamma> = current_\<gamma>_impl state;
                    t = the (get_target_impl state)
                   in state \<lparr> return_impl := notyetterm\<rparr>)"

end

locale loopB_impl = 
loopB_Reasoning where fst = fst and empty_forest = "empty_forest::'c"+ 
loopB_impl_spec where fst = fst and empty_forest = empty_forest+
algo_impl where fst = fst and empty_forest=empty_forest 
for fst::"'edge_type \<Rightarrow> 'a" and empty_forest +
assumes
 abstract_impl_correspond_a:
"\<And> state state_impl s t P P_impl t_impl b \<gamma> f. get_source_target_path_a_cond state s t P b \<gamma> f \<Longrightarrow> 
    get_source_target_path_a_impl state_impl s = Some (t_impl, P_impl) \<Longrightarrow>  invar_isOptflow state
    \<Longrightarrow> implementation_invar state_impl \<Longrightarrow> state = abstract state_impl \<Longrightarrow>P_impl= P \<and> t_impl = t"
and impl_a_None:
"\<And> state state_impl s b \<gamma> f. \<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state;
            abstract state_impl = state; s \<in> \<V>; aux_invar state; (\<forall> e \<in> \<F> state . f e > 0);
            loopB_call1_cond state \<or> loopB_fail1_cond state; s = get_source state;
            implementation_invar state_impl; invar_gamma state\<rbrakk>
    \<Longrightarrow> \<not> (\<exists> t \<in> \<V>. b t < - \<epsilon> * \<gamma> \<and> resreach f s t) \<longleftrightarrow> get_source_target_path_a_impl state_impl s = None"
and
abstract_impl_correspond_b:
"\<And> state state_impl s t P P_impl s_impl b \<gamma> f. get_source_target_path_b_cond state s t P b \<gamma> f  \<Longrightarrow> 
    get_source_target_path_b_impl state_impl t = Some (s_impl, P_impl) \<Longrightarrow> invar_isOptflow state
    \<Longrightarrow> implementation_invar state_impl \<Longrightarrow> state = abstract state_impl \<Longrightarrow>P_impl = P \<and> s_impl = s"
and impl_b_None:
"\<And> state state_impl t b \<gamma> f. \<lbrakk>b = balance state; \<gamma> = current_\<gamma> state; f = current_flow state;
             abstract state_impl = state; t \<in> \<V>; aux_invar state; (\<forall> e \<in> \<F> state . f e > 0);
             loopB_call2_cond state \<or> loopB_fail2_cond state; t = get_target state;
             implementation_invar state_impl; invar_gamma state \<rbrakk>
     \<Longrightarrow> \<not> (\<exists> s \<in> \<V>. b s > \<epsilon> * \<gamma> \<and> resreach f s t) \<longleftrightarrow> get_source_target_path_b_impl state_impl t = None"
and
get_source_impl_axioms:
"\<And> state b \<gamma> state_impl. \<lbrakk>abstract state_impl = state; b = balance state; \<gamma> = current_\<gamma> state;
              \<exists> s \<in> \<V>. b s > (1 - \<epsilon>) * \<gamma>;implementation_invar state_impl\<rbrakk> \<Longrightarrow> get_source state = the (get_source_impl state_impl )"
"\<And> state b \<gamma> state_impl. \<lbrakk>abstract state_impl = state; b = balance state; \<gamma> = current_\<gamma> state;
                          implementation_invar state_impl\<rbrakk>
   \<Longrightarrow> \<not> (\<exists> s \<in> \<V>. b s > (1 - \<epsilon>) * \<gamma>) \<longleftrightarrow> ((get_source_impl state_impl) = None )"
and
get_target_impl_axioms:
"\<And> state b \<gamma> state_impl. \<lbrakk>abstract state_impl = state; b = balance state; \<gamma> = current_\<gamma> state;
              \<exists> t \<in> \<V>. b t < -(1 - \<epsilon>) * \<gamma> ; implementation_invar state_impl\<rbrakk> \<Longrightarrow> get_target state = the (get_target_impl state_impl)"
"\<And> state b \<gamma> state_impl. \<lbrakk>abstract state_impl = state; b = balance state; \<gamma> = current_\<gamma> state;
                         implementation_invar state_impl \<rbrakk>
      \<Longrightarrow> \<not> (\<exists> t \<in> \<V>. b t < -(1 - \<epsilon>) * \<gamma>) \<longleftrightarrow> ((get_target_impl state_impl) = None)"
and test_all_vertices_zero_balance:
"\<And> state b state_impl. \<lbrakk>abstract state_impl = state; b = balance state; implementation_invar state_impl\<rbrakk>
        \<Longrightarrow> test_all_vertices_zero_balance state_impl \<longleftrightarrow> (\<forall> v \<in> \<V>. b v = 0)"
begin

lemma loopB_call1_abstract_corresp:
  assumes "abstract state_impl = state"
          "loopB_call1_cond state"
          "aux_invar state"
          "implementation_invar state_impl"
          "invar_gamma state"
          "\<forall>e\<in>\<F> state. 0 < current_flow state e"
          "invar_isOptflow state"
    shows "abstract (loopB_call1_upd_impl state_impl) = loopB_call1_upd state"
          "implementation_invar (loopB_call1_upd_impl state_impl)"
proof(all \<open>rule loopB_call1_condE[OF assms(2)]\<close>, goal_cases)
  case (1 f b \<gamma> s t P f' b' state')
define f_impl where "f_impl = current_flow_impl state_impl"
  define b_impl where "b_impl = balance_impl state_impl"
  define \<gamma>_impl where "\<gamma>_impl = current_\<gamma>_impl state_impl"
  define s_impl where "s_impl = the (get_source_impl state_impl)"
  define tP where "tP =  the (get_source_target_path_a_impl state_impl s_impl)"
  define t_impl where "t_impl = prod.fst tP"
  define P_impl where "P_impl = prod.snd tP"
  define f'_impl where "f'_impl = augment_edges_impl f_impl \<gamma>_impl P_impl"
  define b'_impl where "b'_impl = move b_impl \<gamma>_impl s_impl t_impl"
  define state'_impl where "state'_impl = state_impl \<lparr> current_flow_impl := f'_impl, balance_impl := b'_impl\<rparr>"

  have state'_impl_is:"state'_impl = loopB_call1_upd_impl state_impl"
    unfolding state'_impl_def b'_impl_def f'_impl_def P_impl_def t_impl_def tP_def s_impl_def
              \<gamma>_impl_def b_impl_def f_impl_def loopB_call1_upd_impl_def Let_def 
    by(auto split: prod.split)

  have state'_is:"state' =loopB_call1_upd state "
    unfolding 1 loopB_call1_upd_def Let_def by simp

  have sources_coincide[simp]: "s_impl = s"
    using get_source_impl_axioms(1)[OF assms(1) refl refl] 1 s_impl_def assms(4)  by simp

  have gamma_gtr_0: "\<gamma> > 0"
    using "1"(3) assms(5) invar_gamma_def by auto
  have s_in_V: "s \<in> \<V>" 
    using "1"(2) "1"(3) "1"(5) "1"(6) get_source_axioms assms(2) by blast
  have t_in_V: "t \<in> \<V>"
    using "1"(1) "1"(2) "1"(3) "1"(5) "1"(6) "1"(7) "1"(8) get_target_for_source_axioms assms(2,5) by blast
  have t_prop:"t \<in> \<V>" "b t < - \<epsilon> * \<gamma>" "resreach f s t"
    using get_target_for_source_axioms[OF 1(2,3,1,6)] assms(2,5) 1 by auto
  have s_prop: "s \<in> \<V> \<and> (1 - \<epsilon>) * \<gamma> < b s"
    using get_source_axioms[OF 1(2,3,6)] assms(2) by auto
  have s_neq_t:"s \<noteq> t" 
    by (smt (verit) gamma_gtr_0 left_diff_distrib s_prop t_prop(2) zero_less_mult_iff) 
  have there_are_target_and_path: 
       "get_source_target_path_a_impl state_impl s = Some (t_impl, P_impl)"
    using impl_a_None[OF 1(2,3,1) assms(1) s_in_V] assms s_in_V  t_impl_def
          P_impl_def tP_def sources_coincide 1 
    by auto
  have  "P_impl = P \<and> t_impl = t"
    apply(rule abstract_impl_correspond_a[of state s t P b \<gamma> f])
    using t_in_V  s_neq_t assms 1 t_prop there_are_target_and_path  s_in_V assms(2)
    by (auto intro!: get_source_target_path_a_condI)
  hence targets_coincide[simp]: "P_impl = P" "t_impl = t"
    by simp+
  have same_Gamma[simp]: "\<gamma>_impl = \<gamma>"
    using assms \<gamma>_impl_def 1 by auto
  have in_F_and_actives: "oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
    using  s_neq_t  s_in_V  t_in_V  assms(6,3,5) "1" t_prop(3) assms(2)
    by (fastforce intro!: get_source_target_path_a_axioms(3) get_source_target_path_a_condI)
  have alloweds_in_E: "to_set (actives state) \<union> \<F> state \<subseteq> \<E>" 
    using assms(3)
    unfolding aux_invar_def invar_aux1_def invar_aux3_def
    by simp
  have E_in_f_dom: "\<E> = flow_domain f_impl"
    using assms(4) f_impl_def implementation_invar_def by blast
  have flow_invar_f[simp]: "flow_invar f_impl" and bal_invar_b[simp]: "bal_invar b_impl"
    using assms(4) f_impl_def b_impl_def implementation_invar_def by blast+
  have in_dom[simp]: "oedge ` set P_impl \<subseteq> flow_domain f_impl"
   using in_F_and_actives alloweds_in_E E_in_f_dom targets_coincide(1) 
   by blast 
  have old_coincide[simp]: "abstract_flow_map f_impl = f" 
    using assms 1 f_impl_def by auto
  have in_dom2[simp]:"s \<in> bal_domain b_impl" "t \<in> bal_domain b_impl" 
    using s_in_V t_in_V b_impl_def assms(4) 
    by auto
   have flows_coincide: "abstract_flow_map f'_impl = f'"
     using in_dom by (auto simp add: 1(10) f'_impl_def assms)
  have balances_coincide: "abstract_bal_map b'_impl = b'"
    using "1"(11) b'_impl_def sources_coincide in_dom2  1(2) b_impl_def assms(1) 
           1(2) assms b_impl_def
   by(auto simp add: implementation_invar_def)
  have "state' = abstract state'_impl"
    using 1(12) state'_impl_def balances_coincide flows_coincide assms(1)
    by (auto simp del: abstractE simp add: abstractE')
    
  thus "abstract (loopB_call1_upd_impl state_impl) = loopB_call1_upd state" 
    using state'_is state'_impl_is by simp
 
  show "implementation_invar (loopB_call1_upd_impl state_impl)" 
  proof(subst sym[OF state'_impl_is], rule implementation_invarI, goal_cases)
    case 1
    show ?case 
      using assms(4) state'_impl_def
      by(auto  simp add: abstractE'  simp del: abstractE)
  next
    case 2
    then show ?case 
      using assms(4) state'_impl_def
      by(auto  simp add: abstractE'  simp del: abstractE)
  next
    case 3
    then show ?case 
      using assms(4) state'_impl_def
      by(auto  simp add: abstractE'  simp del: abstractE)
  next
    case 4
    then show ?case 
      apply(subst state'_impl_def, simp, subst f'_impl_def)
      apply(subst conjunct1[OF augment_edges_impl_domain_invar])
      using in_F_and_actives[simplified  targets_coincide(1) sym[OF set_map]] alloweds_in_E
            E_in_f_dom flow_invar_f apply auto by blast
  next
    case 5
    then show ?case 
      apply(subst state'_impl_def, simp, subst f'_impl_def)
      apply(subst conjunct2[OF augment_edges_impl_domain_invar])
      using in_F_and_actives[simplified  targets_coincide(1) sym[OF set_map]] alloweds_in_E
            E_in_f_dom flow_invar_f apply auto by blast
  next
    case 6
    then show ?case
      apply(simp add: state'_impl_def b'_impl_def)
      using assms b_impl_def by auto
  next
    case 7
    then show ?case 
      apply(simp add: state'_impl_def b'_impl_def)
      using assms b_impl_def by auto
  next
    case 8
    then show ?case
      using assms(4) state'_impl_def 
      by(fastforce simp add: abstractE' simp del: abstractE) 
  next
    case 9
    then show ?case 
      using assms(4) state'_impl_def
      by auto
  next
    case 10
    then show ?case 
      using assms(4) state'_impl_def
      by fastforce
  next
    case 11
    then show ?case 
      using assms(4) state'_impl_def
      by auto
  next
    case 12
    then show ?case 
      using assms(4) state'_impl_def
      by auto
  next
    case 13
    then show ?case
      using assms(4) state'_impl_def
      by (auto elim!: implementation_invarE)
  qed
qed

lemma loopB_call2_abstract_corresp:
  assumes "abstract state_impl = state"
          "loopB_call2_cond state"
          "aux_invar state"
          "implementation_invar state_impl"
          "invar_gamma state"
          "\<forall>e\<in>\<F> state. 0 < current_flow state e"
          "invar_isOptflow state"
    shows "abstract (loopB_call2_upd_impl state_impl) = loopB_call2_upd state"
          "implementation_invar (loopB_call2_upd_impl state_impl)"
proof(all \<open>rule loopB_call2_condE[OF assms(2)]\<close>, goal_cases)
  case (1 f b \<gamma> t s P f' b' state')
define f_impl where "f_impl = current_flow_impl state_impl"
  define b_impl where "b_impl = balance_impl state_impl"
  define \<gamma>_impl where "\<gamma>_impl = current_\<gamma>_impl state_impl"
  define t_impl where "t_impl = the (get_target_impl state_impl)"
  define sP where "sP =  the (get_source_target_path_b_impl state_impl t_impl)"
  define s_impl where "s_impl = prod.fst sP"
  define P_impl where "P_impl = prod.snd sP"
  define f'_impl where "f'_impl = augment_edges_impl f_impl \<gamma>_impl P_impl"
  define b'_impl where "b'_impl = move b_impl \<gamma>_impl s_impl t_impl"
  define state'_impl where "state'_impl = state_impl \<lparr> current_flow_impl := f'_impl, balance_impl := b'_impl\<rparr>"

  have state'_impl_is:"state'_impl = loopB_call2_upd_impl state_impl"
    unfolding state'_impl_def b'_impl_def f'_impl_def P_impl_def t_impl_def sP_def s_impl_def
              \<gamma>_impl_def b_impl_def f_impl_def loopB_call2_upd_impl_def Let_def 
    by(auto split: prod.split)

  have state'_is:"state' =loopB_call2_upd state "
    unfolding 1 loopB_call2_upd_def Let_def by simp

  have targets_coincide[simp]: "t_impl = t"
    using get_target_impl_axioms(1)[OF assms(1) refl refl] 1 t_impl_def assms(4) by simp
  have flow_coincide[simp]:"abstract_flow_map f_impl = f"
    using 1(1) f_impl_def assms by simp

  have gamma_gtr_0: "\<gamma> > 0"
    using "1"(3) assms(5) invar_gamma_def by auto
  have t_in_V[simp]: "t \<in> \<V>" 
    using 1(2,3,5,6,7) get_target_axioms assms(2)by blast
  have s_in_V[simp]: "s \<in> \<V>"
    using "1"(1) "1"(2) "1"(3) "1"(6) "1"(7) "1"(8) "1"(9) get_source_for_target_axioms assms(2,5) by blast
  have s_prop[simp]:"s \<in> \<V>" "b s > \<epsilon> * \<gamma>" "resreach f s t"
    using get_source_for_target_axioms[OF 1(2,3,1,7,9)] assms(2,5) 1 by auto
  have t_prop: "t \<in> \<V> \<and> - (1 - \<epsilon>) * \<gamma> > b t"
    using get_target_axioms[OF 1(2,3,7)] assms(2) by auto
  have gammas_coincide[simp]: "\<gamma>_impl = \<gamma>" 
    using \<gamma>_impl_def 1(3) assms by auto
  have s_neq_t:"s \<noteq> t" 
    by (smt (verit) gamma_gtr_0 left_diff_distrib s_prop(2) t_prop zero_less_mult_iff) 
  have there_are_target_and_path: 
       "get_source_target_path_b_impl state_impl t= Some (s_impl, P_impl)"
    using impl_b_None[OF 1(2,3,1) assms(1)] t_in_V  s_impl_def P_impl_def sP_def  assms 1 
    by auto
  have  "P_impl = P \<and> s_impl = s"
    apply(rule abstract_impl_correspond_b[of state s t P b \<gamma> f])
    using s_in_V t_in_V s_neq_t assms 1 s_prop there_are_target_and_path
    by (auto intro!: get_source_target_path_b_condI)
  hence sources_coincide[simp]: "P_impl = P" "s_impl = s"
    by simp+
  have in_F_and_actives: "oedge ` set P \<subseteq> to_set (actives state) \<union> \<F> state"
    using get_source_target_path_b_axioms(3) get_source_target_path_b_condI assms(2) 1 s_neq_t 
          s_in_V  t_in_V  assms(3,6,5) s_prop(3) 
    by blast
  have alloweds_in_E: "to_set (actives state) \<union> \<F> state \<subseteq> \<E>" 
    using assms(3)
    by(simp add:  aux_invar_def invar_aux1_def invar_aux3_def)
  have E_in_f_dom: "\<E> = flow_domain f_impl"
    using assms(4) f_impl_def implementation_invar_def by blast
  have flow_invar_f[simp]: "flow_invar f_impl" and bal_invar_b[simp]: "bal_invar b_impl"
    using assms(4) f_impl_def implementation_invar_def b_impl_def by blast+
  have P_in_f_dom[simp]: " oedge ` set P \<subseteq> flow_domain f_impl"
    using alloweds_in_E in_F_and_actives E_in_f_dom  by blast
  have flows_coincide[simp]: "abstract_flow_map f'_impl = f'"
    by(simp add:1(11) f'_impl_def)
  have old_bals_coincide[simp]: "abstract_bal_map b_impl = b"
    using 1(2) b_impl_def assms by simp
  have s_t_in_dom[simp]:"s \<in> bal_domain b_impl" "t \<in> bal_domain b_impl"
    using s_prop t_prop assms b_impl_def by blast+
  have balances_coincide[simp]: "abstract_bal_map b'_impl = b'"
    using b'_impl_def 1(12) by simp

  have "abstract state'_impl = state'"
    using assms(1) 
    by(auto simp add: abstractE' 1(13) state'_impl_def  simp del: abstractE)
    
  thus "abstract (loopB_call2_upd_impl state_impl) = loopB_call2_upd state" 
    using state'_is state'_impl_is by simp
 
  show "implementation_invar (loopB_call2_upd_impl state_impl)" 
  proof(subst sym[OF state'_impl_is], rule implementation_invarI, goal_cases)
    case 1
    show ?case 
      using assms(4) state'_impl_def
      by(auto simp add: abstractE' simp del: abstractE)
  next
    case 2
    then show ?case 
      using assms(4) state'_impl_def
      by(auto simp add: abstractE' simp del: abstractE)
  next
    case 3
    then show ?case 
      using assms(4) state'_impl_def
      by(auto simp add: abstractE' simp del: abstractE)
  next
    case 4
    then show ?case 
      by(simp add: state'_impl_def f'_impl_def E_in_f_dom)
  next
    case 5
    then show ?case 
     by(simp add: state'_impl_def f'_impl_def E_in_f_dom)
  next
    case 6
    then show ?case
      apply(simp add: state'_impl_def b'_impl_def)
      using assms b_impl_def by auto
  next
    case 7
    then show ?case 
      apply(simp add: state'_impl_def b'_impl_def)
      using assms b_impl_def by auto
    case 8
    then show ?case
      using assms(4) state'_impl_def
      by(fastforce simp add: abstractE' simp del: abstractE)
  next
    case 9
    then show ?case 
      using assms(4) state'_impl_def
      by(auto simp add: abstractE' simp del: abstractE)
  next
    case 10
    then show ?case 
      using assms(4) state'_impl_def
      by(fastforce simp add: abstractE' simp del: abstractE)
  next
    case 11
    then show ?case 
      using assms(4) state'_impl_def
      by(auto simp add: abstractE' simp del: abstractE)
  next
    case 12
    then show ?case 
      using assms(4) state'_impl_def
      by(auto simp add: abstractE' simp del: abstractE)
  next
    case 13
    then show ?case
      using assms(4) state'_impl_def
      by(auto elim!: implementation_invarE simp add: abstractE' simp del: abstractE)
  qed
qed

lemma loopB_fail1_abstract_corresp:
  assumes "abstract state_impl = state"
          "loopB_fail1_cond state"
          "implementation_invar state_impl"
    shows "abstract (loopB_fail_impl state_impl) = loopB_fail_upd state"
          "implementation_invar (loopB_fail_impl state_impl)"
proof(all \<open>rule loopB_fail1_condE[OF assms(2)]\<close>, goal_cases)
 case (1 f b \<gamma> s)
  define f_impl where "f_impl = current_flow_impl state_impl"
  define b_impl where "b_impl = balance_impl state_impl"
  define \<gamma>_impl where "\<gamma>_impl = current_\<gamma>_impl state_impl"
  define s_impl where "s_impl = the (get_target_impl state_impl)"
  define tP where "tP =  the (get_source_target_path_a_impl state_impl s_impl)"
  define state'_impl where "state'_impl = state_impl \<lparr> return_impl := failure\<rparr>"

  define state' where "state' = state \<lparr>return := failure \<rparr>"

  have state'_impl_is:"state'_impl = loopB_fail_impl state_impl"
    unfolding state'_impl_def  tP_def s_impl_def
              \<gamma>_impl_def b_impl_def f_impl_def loopB_fail_impl_def Let_def 
    by(auto split: prod.split)

  have state'_is:"state' =loopB_fail_upd state "
    unfolding state'_def loopB_fail_upd_def Let_def by simp

  show "abstract (loopB_fail_impl state_impl) = loopB_fail_upd state" 
    apply(subst sym[OF state'_is], subst sym[OF state'_impl_is]) 
    unfolding state'_def state'_impl_def abstract_def Let_def sym[OF assms(1)]
    by(auto simp add: abstractE' simp del: abstractE)
    
  show "implementation_invar (loopB_fail_impl state_impl)"
    apply(subst sym[OF state'_impl_is]) 
    using assms(3)
    unfolding state'_def state'_impl_def abstract_def Let_def sym[OF assms(1)] implementation_invar_def
    by(auto simp add: abstractE' simp del: abstractE)
qed

lemma loopB_fail2_abstract_corresp:
  assumes "abstract state_impl = state"
          "loopB_fail2_cond state"
          "implementation_invar state_impl"
    shows "abstract (loopB_fail_impl state_impl) = loopB_fail_upd state"
          "implementation_invar (loopB_fail_impl state_impl)"
proof(all \<open>rule loopB_fail2_condE[OF assms(2)]\<close>, goal_cases)
 case (1 f b \<gamma> s)
  define f_impl where "f_impl = current_flow_impl state_impl"
  define b_impl where "b_impl = balance_impl state_impl"
  define \<gamma>_impl where "\<gamma>_impl = current_\<gamma>_impl state_impl"
  define s_impl where "s_impl = the (get_target_impl state_impl)"
  define tP where "tP =  the (get_source_target_path_a_impl state_impl s_impl)"
  define state'_impl where "state'_impl = state_impl \<lparr> return_impl := failure\<rparr>"

  define state' where "state' = state \<lparr>return := failure \<rparr>"

  have state'_impl_is:"state'_impl = loopB_fail_impl state_impl"
    unfolding state'_impl_def  tP_def s_impl_def
              \<gamma>_impl_def b_impl_def f_impl_def loopB_fail_impl_def Let_def 
    by(auto split: prod.split)

  have state'_is:"state' =loopB_fail_upd state "
    unfolding state'_def loopB_fail_upd_def Let_def by simp

  show "abstract (loopB_fail_impl state_impl) = loopB_fail_upd state" 
    apply(subst sym[OF state'_is], subst sym[OF state'_impl_is]) 
    unfolding state'_def state'_impl_def abstract_def Let_def sym[OF assms(1)]
    by(auto simp add: abstractE' simp del: abstractE)
    
  show "implementation_invar (loopB_fail_impl state_impl)"
    apply(subst sym[OF state'_impl_is]) 
    using assms(3)
    unfolding state'_def state'_impl_def abstract_def Let_def sym[OF assms(1)] implementation_invar_def
    by(auto simp add: abstractE' simp del: abstractE)
qed

lemma loopB_succ_abstract_corresp:
  assumes "abstract state_impl = state"
          "loopB_succ_cond state"
          "implementation_invar state_impl"
    shows "abstract (loopB_succ_impl state_impl) = loopB_succ_upd state"
          "implementation_invar (loopB_succ_impl state_impl)"
proof(all \<open>rule loopB_succ_condE[OF assms(2)]\<close>, goal_cases)
 case (1 f b \<gamma> )
  define f_impl where "f_impl = current_flow_impl state_impl"
  define b_impl where "b_impl = balance_impl state_impl"
  define \<gamma>_impl where "\<gamma>_impl = current_\<gamma>_impl state_impl"
  define state'_impl where "state'_impl = state_impl \<lparr> return_impl := success\<rparr>"

  define state' where "state' = state \<lparr>return := success \<rparr>"

  have state'_impl_is:"state'_impl = loopB_succ_impl state_impl"
    unfolding state'_impl_def 
              \<gamma>_impl_def b_impl_def f_impl_def loopB_succ_impl_def Let_def 
    by(auto split: prod.split)

  have state'_is:"state' =loopB_succ_upd state "
    unfolding state'_def loopB_succ_upd_def Let_def by simp

  show "abstract (loopB_succ_impl state_impl) = loopB_succ_upd state" 
    apply(subst sym[OF state'_is], subst sym[OF state'_impl_is]) 
    unfolding state'_def state'_impl_def abstract_def Let_def sym[OF assms(1)]
    by(auto simp add: abstractE' simp del: abstractE)
    
  show "implementation_invar (loopB_succ_impl state_impl)"
    apply(subst sym[OF state'_impl_is]) 
    using assms(3)
    unfolding state'_def state'_impl_def abstract_def Let_def sym[OF assms(1)] implementation_invar_def
    by(auto simp add: abstractE' simp del: abstractE)
qed

lemma loopB_cont_abstract_corresp:
  assumes "abstract state_impl = state"
          "loopB_cont_cond state"
          "implementation_invar state_impl"
    shows "abstract (loopB_cont_impl state_impl) = loopB_cont_upd state"
          "implementation_invar (loopB_cont_impl state_impl)"
proof(all \<open>rule loopB_cont_condE[OF assms(2)]\<close>, goal_cases)
 case (1 f b \<gamma>)
  define f_impl where "f_impl = current_flow_impl state_impl"
  define b_impl where "b_impl = balance_impl state_impl"
  define s_impl where "s_impl = the (get_target_impl state_impl)"
  define tP where "tP =  the (get_source_target_path_a_impl state_impl s_impl)"
  define state'_impl where "state'_impl = state_impl \<lparr> return_impl := notyetterm\<rparr>"

  define state' where "state' = state \<lparr>return := notyetterm \<rparr>"

  have state'_impl_is:"state'_impl = loopB_cont_impl state_impl"
    unfolding state'_impl_def  tP_def s_impl_def
               b_impl_def f_impl_def loopB_cont_impl_def Let_def 
    by(auto split: prod.split)

  have state'_is:"state' =loopB_cont_upd state "
    unfolding state'_def loopB_cont_upd_def Let_def by simp

  show "abstract (loopB_cont_impl state_impl) = loopB_cont_upd state" 
    apply(subst sym[OF state'_is], subst sym[OF state'_impl_is]) 
    unfolding state'_def state'_impl_def abstract_def Let_def sym[OF assms(1)]
    by(auto simp add: abstractE' simp del: abstractE)
    
  show "implementation_invar (loopB_cont_impl state_impl)"
    apply(subst sym[OF state'_impl_is]) 
    using assms(3)
    unfolding state'_def state'_impl_def abstract_def Let_def sym[OF assms(1)] implementation_invar_def
    by(auto simp add: abstractE' simp del: abstractE)
qed  

lemma loopB_impl_simps_succ: 
  assumes "abstract state_impl = state"
          "implementation_invar state_impl"
  shows   "loopB_succ_cond state \<Longrightarrow> loopB_impl state_impl = (loopB_succ_impl state_impl)" 
    by (auto intro: loopB_succ_condE
          simp add: sym[OF assms(1)] abstract_def Let_def loopB_succ_impl_def
                    test_all_vertices_zero_balance[OF refl refl assms(2)]
                    loopB_impl.simps abstractE' simp del: abstractE)

lemma loopB_impl_simps: 
  assumes "abstract state_impl = state"
          "implementation_invar state_impl"
          "invar_gamma state"
  shows   "loopB_succ_cond state \<Longrightarrow> loopB_impl state_impl = (loopB_succ_impl state_impl)" 
          "loopB_cont_cond state \<Longrightarrow>  loopB_impl state_impl = (loopB_cont_impl state_impl)"
          "loopB_fail1_cond state \<Longrightarrow> aux_invar state \<Longrightarrow> \<forall>e\<in>\<F> state. 0 < current_flow state e \<Longrightarrow>
                                      loopB_impl state_impl = (loopB_fail_impl state_impl)"
          "loopB_fail2_cond state \<Longrightarrow> aux_invar state \<Longrightarrow> \<forall>e\<in>\<F> state. 0 < current_flow state e \<Longrightarrow>
                                      loopB_impl state_impl = (loopB_fail_impl state_impl)"
          "loopB_call1_cond state \<Longrightarrow> aux_invar state \<Longrightarrow> \<forall>e\<in>\<F> state. 0 < current_flow state e \<Longrightarrow>
                                      loopB_impl state_impl = loopB_impl (loopB_call1_upd_impl state_impl)"
          "loopB_call2_cond state \<Longrightarrow> aux_invar state \<Longrightarrow> \<forall>e\<in>\<F> state. 0 < current_flow state e \<Longrightarrow>
                                      loopB_impl state_impl = loopB_impl (loopB_call2_upd_impl state_impl)"
proof(goal_cases)
  case 1
  show ?case 
    by (auto intro: loopB_succ_condE[OF 1] 
          simp add: sym[OF assms(1)] abstract_def Let_def loopB_succ_impl_def
                    test_all_vertices_zero_balance[OF refl refl assms(2)]
                    loopB_impl.simps abstractE' simp del: abstractE)
next
  case 2
  have no_source:"get_source_impl state_impl = None"
    using  assms(2,3) get_source_impl_axioms(2)[OF assms(1) refl refl]
    by(auto intro: loopB_cont_condE[OF 2] simp add: abstract_def Let_def abstractE' simp del: abstractE)
  have still_a_vertex: "\<not> test_all_vertices_zero_balance state_impl"
    using test_all_vertices_zero_balance[OF refl refl assms(2)]
    by (auto intro: loopB_cont_condE[OF 2] simp add: sym[OF assms(1)] abstract_def Let_def 
abstractE' simp del: abstractE)
  have no_target: " get_target_impl state_impl =  None"
    using  assms(2,3) get_target_impl_axioms(2)[OF assms(1) refl refl]
    by(auto intro: loopB_cont_condE[OF 2] simp add: abstract_def Let_def abstractE' simp del: abstractE)
  show ?case 
    using no_source still_a_vertex  no_target 
    by (auto simp add: case_simp(2) Let_def loopB_cont_impl_def loopB_impl.simps)
next
  case 3
  show ?case
  proof(rule loopB_fail1_condE[OF 3(1)], goal_cases)
    case (1 f b \<gamma> s)
     define b_impl where "b_impl = balance_impl state_impl"
     define \<gamma>_impl where "\<gamma>_impl = current_\<gamma>_impl state_impl"
     define s_impl where "s_impl = the (get_source_impl state_impl)"

  have sources_coincide: "s = s_impl"
    using get_source_impl_axioms(1)[OF assms(1) refl refl] 1 s_impl_def assms(2) by simp
  have s_in_V: "s \<in> \<V>" 
    using "1"(2) "1"(3) "1"(5) "1"(6) get_source_axioms 3 by blast
  have source:"get_source_impl state_impl \<noteq> None"
    using  assms(2,3) get_source_impl_axioms(2)[OF assms(1) refl refl] 
    by(auto intro: loopB_fail1_condE[OF 3(1)] simp add: abstract_def Let_def abstractE' simp del: abstractE)
  have still_a_vertex: "\<not> test_all_vertices_zero_balance state_impl"
    using test_all_vertices_zero_balance[OF refl refl assms(2)]
    by (auto intro: loopB_fail1_condE[OF 3(1)] simp add: sym[OF assms(1)] abstract_def Let_def abstractE' simp del: abstractE)
  have no_target: " get_source_target_path_a_impl state_impl s =  None"
    using  assms(1,2,3) impl_a_None[OF refl refl refl assms(1) s_in_V 3(2) 3(3)] 1 3
    by (auto intro: loopB_fail1_condE[OF 3(1)])
  show ?case 
    using still_a_vertex  source  no_target s_impl_def sources_coincide 
    by (auto simp add: Let_def loopB_fail_upd_def loopB_fail_impl_def
                       loopB_impl.simps)
  qed
next
  case 4
  show ?case 
  proof(rule loopB_fail2_condE[OF 4(1)], goal_cases)
    case (1 f b \<gamma> t)
     define b_impl where "b_impl = balance_impl state_impl"
     define \<gamma>_impl where "\<gamma>_impl = current_\<gamma>_impl state_impl"
     define t_impl where "t_impl = the (get_target_impl state_impl)"

  have no_source:"get_source_impl state_impl = None"
    using  assms(1,2) get_source_impl_axioms(2)[OF assms(1) refl refl]
    by(auto intro: loopB_fail2_condE[OF 4(1)] simp add: abstract_def Let_def abstractE' simp del: abstractE)
  have sources_coincide: "t = t_impl"
    using get_target_impl_axioms(1)[OF assms(1) refl refl] 1 t_impl_def assms(2) by simp
  have t_in_V: "t \<in> \<V>"
    using "1"(2) "1"(3) "1"(6) "1"(7) get_target_axioms 4 by presburger
  have target:"get_target_impl state_impl \<noteq> None"
    using  assms(2) get_target_impl_axioms(2)[OF assms(1) refl refl]
    by(auto intro: loopB_fail2_condE[OF 4(1)] simp add: abstract_def Let_def abstractE' simp del: abstractE)
  have still_a_vertex: "\<not> test_all_vertices_zero_balance state_impl"
    using test_all_vertices_zero_balance[OF refl refl assms(2)]
    by (auto intro: loopB_fail2_condE[OF 4(1)] simp add: sym[OF assms(1)] abstract_def Let_def abstractE' simp del: abstractE)
  have no_source2: " get_source_target_path_b_impl state_impl t =  None"
    using  assms(1,2,3) impl_b_None[OF refl refl refl assms(1) t_in_V 4(2) 4(3)] 1 4
    by (auto intro: loopB_fail2_condE[OF 4(1)])
  show ?case 
    using still_a_vertex target no_source no_source2 t_impl_def sources_coincide 
    by (auto simp add: Let_def loopB_fail_upd_def loopB_fail_impl_def
                      loopB_impl.simps)
  qed
next
  case 5
  show ?case
  proof(rule loopB_call1_condE[OF 5(1)], goal_cases)
    case (1 f b \<gamma> s t P f' b' state')
     define b_impl where "b_impl = balance_impl state_impl"
     define \<gamma>_impl where "\<gamma>_impl = current_\<gamma>_impl state_impl"
     define s_impl where "s_impl = the (get_source_impl state_impl)"

  have sources_coincide: "s = s_impl"
    using get_source_impl_axioms(1)[OF assms(1) refl refl] 1 s_impl_def assms(2)  by simp
  have s_in_V: "s \<in> \<V>" 
    using "1"(2) "1"(3) "1"(5) "1"(6) get_source_axioms 5 by blast
  have source:"get_source_impl state_impl \<noteq> None"
    using  assms(1,2) get_source_impl_axioms(2)[OF assms(1) refl refl]
    by(auto intro: loopB_call1_condE[OF 5(1)] simp add: abstract_def Let_def abstractE' simp del: abstractE)
  have still_a_vertex: "\<not> test_all_vertices_zero_balance state_impl"
    using test_all_vertices_zero_balance[OF refl refl assms(2)]
    by (auto intro: loopB_call1_condE[OF 5(1)] simp add: sym[OF assms(1)] abstract_def Let_def abstractE' simp del: abstractE)
  have target: " get_source_target_path_a_impl state_impl s \<noteq>  None"
    using  assms(1-3) impl_a_None[OF refl refl refl assms(1) s_in_V 5(2) 5(3)] 1 5
    by (auto intro: loopB_call1_condE[OF 5(1)])
  show ?case 
    using still_a_vertex  source  target s_impl_def sources_coincide 
    by(fastforce simp add: Let_def loopB_call1_upd_def loopB_call1_upd_impl_def
                       loopB_impl.simps)
  qed
next
  case 6
  show ?case
  proof(rule loopB_call2_condE[OF 6(1)], goal_cases)
    case (1 f b \<gamma> t s P f' b' state')
     define b_impl where "b_impl = balance_impl state_impl"
     define \<gamma>_impl where "\<gamma>_impl = current_\<gamma>_impl state_impl"
     define t_impl where "t_impl = the (get_target_impl state_impl)"

  have no_source:"get_source_impl state_impl = None"
    using  assms(1,2) get_source_impl_axioms(2)[OF assms(1) refl refl]
    by(auto intro: loopB_call2_condE[OF 6(1)] simp add: abstract_def Let_def abstractE' simp del: abstractE)
  have sources_coincide: "t = t_impl"
    using get_target_impl_axioms(1)[OF assms(1) refl refl] 1 t_impl_def assms(2) by simp
  have t_in_V: "t \<in> \<V>"
    using "1"(2) "1"(3) "1"(6) "1"(7) get_target_axioms 6 by presburger
  have target:"get_target_impl state_impl \<noteq> None"
    using  assms(2,3) get_target_impl_axioms(2)[OF assms(1) refl refl]
    by(auto intro: loopB_call2_condE[OF 6(1)] simp add: abstract_def Let_def abstractE' simp del: abstractE)
  have still_a_vertex: "\<not> test_all_vertices_zero_balance state_impl"
    using test_all_vertices_zero_balance[OF refl refl assms(2)]
    by (auto intro: loopB_call2_condE[OF 6(1)] simp add: sym[OF assms(1)] abstract_def Let_def abstractE' simp del: abstractE)
  have no_source2: " get_source_target_path_b_impl state_impl t \<noteq>  None"
    using  assms(1-3) impl_b_None[OF refl refl refl assms(1) t_in_V 6(2) 6(3)] 1 6
    by (auto intro: loopB_call2_condE[OF 6(1)])
  show ?case 
    using still_a_vertex target no_source no_source2 t_impl_def sources_coincide 
    by (fastforce simp add: Let_def loopB_call2_upd_def loopB_call2_upd_impl_def
                       loopB_impl.simps)
  qed
qed

lemma loopB_abstract_corresp_result_with_conj:
  assumes "loopB_dom state"
          "abstract state_impl = state"
          "aux_invar state"
          "implementation_invar state_impl"
          "invar_gamma state"
          "\<And> e. e \<in> \<F> state \<Longrightarrow> current_flow state e \<ge>
                                 6*N*current_\<gamma> state - (2*N  - \<Phi> state)*current_\<gamma> state"
          "invar_isOptflow state" 
          "invar_integral state"          
        shows "abstract (loopB_impl state_impl) = loopB state \<and>
               implementation_invar (loopB_impl state_impl)"
  using assms(2-)
proof(induction  arbitrary: state_impl rule: loopB_induct[OF assms(1)])
  case (1 state)
  note IH = this
  have gamma_0: "current_\<gamma> state > 0" 
    using IH(7) invar_gamma_def by blast
  have gamma_flow:"e \<in> \<F> state \<Longrightarrow> current_\<gamma> state \<le> current_flow state e" for e
    apply(rule order.trans[of _ "4*N*current_\<gamma> state"])
    using IH(8)[of e] gamma_0 Phi_nonneg[of state, OF IH(7)] N_gtr_0 apply simp
    using  gamma_0 Phi_nonneg[of state, OF IH(7)] N_gtr_0
    by(intro order.trans[OF _ IH(8)[of e]] )(auto simp add: mult.commute right_diff_distrib')
  show ?case 
  proof(rule loopB_cases[of state], goal_cases)
    case 1
    show ?case
      using loopB_impl_simps(2)[OF IH(4) IH(6,7) 1]
            loopB_simps(2)[OF IH(1) 1]
            loopB_cont_abstract_corresp[OF IH(4) 1 IH(6)] 
      by auto
  next
    case 2
    then show ?case 
           using loopB_impl_simps(1)[OF  IH(4) IH(6,7) 2]
            loopB_simps(1)[OF IH(1) 2]
            loopB_succ_abstract_corresp[OF IH(4) 2 IH(6)] 
      by auto
  next
    case 3
    have a1: "aux_invar (loopB_call1_upd state)"
      using invar_aux_pres_call1[of state] IH 3 by simp
    have flowF:  " \<forall>e\<in>\<F> state. 0 < current_flow state e"
      using gamma_0 gamma_flow by fastforce
    have gamma_Phi_flow: "e \<in> \<F> (loopB_call1_upd state) \<Longrightarrow>
         real (6 * N) * current_\<gamma> (loopB_call1_upd state) -
         real_of_int (int (2 * N) - \<Phi> (loopB_call1_upd state)) * current_\<gamma> (loopB_call1_upd state)
         \<le> current_flow (loopB_call1_upd state) e" for e
         apply(rule order.trans) defer
         apply(rule loopB_call1_cond_flow_Phi[OF 3])
         using IH(5)  IH(8)[of e] loopB_call1_upd_changes(6)[of state] 
               loopB_call1_upd_changes(4)[of state]  loopB_call1_cond_Phi_decr[OF 3 IH(7)] IH(7)
         by (auto simp add: left_diff_distrib' flowF)
       show ?case 
         apply(subst loopB_impl_simps(5)[OF IH(4) IH(6,7) 3 IH(5) flowF])+
         apply(subst loopB_simps(5)[OF IH(1) 3])
         using IH(4-10) 3 flowF a1 gamma_Phi_flow gamma_flow
         by(intro IH(2)[OF 3]  invar_gamma_pres_call1 loopB_call1_abstract_corresp
                  loopB_call1_invar_integral_pres loopB_invar_isOptflow_call1
           | simp)+
  next
    case 4
    have a1: "aux_invar (loopB_call2_upd state)"
      using invar_aux_pres_call2[of state] IH 4 by simp
    have flowF:  " \<forall>e\<in>\<F> state. 0 < current_flow state e"
      using gamma_0 gamma_flow by fastforce
    have gamma_Phi_flow: "e \<in> \<F> (loopB_call2_upd state) \<Longrightarrow>
         real (6 * N) * current_\<gamma> (loopB_call2_upd state) -
         real_of_int (int (2 * N) - \<Phi> (loopB_call2_upd state)) * current_\<gamma> (loopB_call2_upd state)
         \<le> current_flow (loopB_call2_upd state) e" for e
         apply(rule order.trans) defer
         apply(rule loopB_call2_cond_flow_Phi[OF 4])
         using IH(5)  IH(8)[of e] loopB_call2_upd_changes(6)[of state] 
               loopB_call2_upd_changes(4)[of state]  loopB_call2_cond_Phi_decr[OF 4 IH(7)] IH(7)
         by (auto simp add: left_diff_distrib' flowF)
       show ?case 
         apply(subst loopB_impl_simps(6)[OF IH(4) IH(6,7) 4 IH(5) flowF])+
         apply(subst loopB_simps(6)[OF IH(1) 4])
         using IH(4-10) 4 flowF a1 gamma_Phi_flow gamma_flow
         by(intro IH(3)[OF 4]  invar_gamma_pres_call2 loopB_call2_abstract_corresp
                  loopB_call2_invar_integral_pres loopB_invar_isOptflow_call2
           | simp)+
  next
    case 5
    have flowF:  " \<forall>e\<in>\<F> state. 0 < current_flow state e"
      using gamma_0 gamma_flow by fastforce
    show ?case 
      using loopB_impl_simps(3)[OF IH(4) IH(6,7) 5 IH(5) flowF]  loopB_simps(3)[OF IH(1) 5]
            IH(4-7) 5 flowF loopB_fail1_abstract_corresp 
      by auto
  next
    case 6
    have flowF:  " \<forall>e\<in>\<F> state. 0 < current_flow state e"
      using gamma_0 gamma_flow by fastforce
    show ?case 
      using loopB_impl_simps(4)[OF IH(4) IH(6,7) 6 IH(5) flowF]  loopB_simps(4)[OF IH(1) 6]
            IH(4-7) 6 flowF loopB_fail2_abstract_corresp 
      by auto
  qed
qed

lemmas loopB_abstract_corresp_result = conjunct1[OF loopB_abstract_corresp_result_with_conj]
                                       conjunct2[OF loopB_abstract_corresp_result_with_conj]
end

subsection \<open>Top Loop\<close>

locale orlins_impl_spec = loopA_impl_spec where fst = fst + 
                     loopB_impl_spec where fst = fst 
                   for fst ::"'edge_type \<Rightarrow> 'a"+
  fixes init_flow :: "'e"
    and init_bal :: "'f"
    and init_rep_card :: "'g"
    and init_not_blocked :: "'i"
begin

partial_function (tailrec) orlins_impl::"('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state_impl  
\<Rightarrow> ('e, 'f, 'c,'h, 'd, 'g, 'i) Algo_state_impl  " where
"orlins_impl state = (if return_impl state = success then state 
                 else if return_impl state= failure then state
                 else (let f = current_flow_impl state;
                      b = balance_impl state;
                      \<gamma> = current_\<gamma>_impl state;
                      E' = actives_impl state;
                      \<gamma>' = (if are_all (\<lambda> e. the (flow_lookup f e) = (0::real)) E' then
                             min (\<gamma> / 2) (get_max (\<lambda> x bx. \<bar> bx \<bar>) b)
                             else (\<gamma> / 2));
                      state' = loopA_impl (state \<lparr>current_\<gamma>_impl := \<gamma>' \<rparr>);
                      state'' = loopB_impl state' 
                      in orlins_impl state''))"

definition "initial_impl = \<lparr> current_flow_impl = flow_update_all (\<lambda> e fe. 0) init_flow, 
                             balance_impl = init_bal,  \<FF>_impl = empty_forest,
                             conv_to_rdg_impl = conv_empty,
                             actives_impl = filter (\<lambda> e. fst e \<noteq> snd e) \<E>_impl,
                             return_impl = notyetterm, 
                             current_\<gamma>_impl = (get_max (\<lambda> x bx. \<bar> bx \<bar>) init_bal),
                             representative_comp_card_impl = rep_comp_update_all (\<lambda> x val. (x, 1)) init_rep_card, 
                             not_blocked_impl = not_blocked_update_all 
                                (\<lambda> e b . if fst e \<noteq> snd e then True else False) init_not_blocked\<rparr>"

lemmas [code] = orlins_impl.simps initial_impl_def

end

locale orlins_impl = loopA_impl where fst = fst + 
                     loopB_impl where fst = fst +
                     orlins where fst = fst +
                     orlins_impl_spec where fst = fst
                   for fst ::"'edge_type \<Rightarrow> 'a"+
  assumes init_flow: "flow_invar init_flow" "flow_domain init_flow = \<E>"
  assumes init_bal: "bal_invar init_bal" "bal_domain init_bal = \<V>" 
                    "\<And> x. x \<in> \<V> \<Longrightarrow> the (bal_lookup init_bal x) = \<b> x"
  assumes init_rep_card: "rep_comp_invar init_rep_card" "rep_comp_domain init_rep_card = \<V>"
  assumes init_not_blocked: "not_blocked_invar init_not_blocked" "not_blocked_dom init_not_blocked = \<E>"
            "\<And> e. e \<in> not_blocked_dom init_not_blocked \<Longrightarrow> the (not_blocked_lookup init_not_blocked e) = False"
begin

definition "orlins_impl_ret state = state"

definition "orlins_upd_impl state \<equiv>
                     (let f = current_flow_impl state;
                      b = balance_impl state;
                      \<gamma> = current_\<gamma>_impl state;
                      E' = actives_impl state;
                      \<gamma>' = (if are_all (\<lambda> e. the (flow_lookup f e) = (0::real)) E' then
                             min (\<gamma> / 2) (get_max (\<lambda> x bx. \<bar> bx \<bar>) b)
                             else (\<gamma> / 2));
                      state' = loopA_impl (state \<lparr>current_\<gamma>_impl := \<gamma>' \<rparr>);
                      state'' = loopB_impl state' 
                      in state'')"

lemma orlins_step_corresp:
  assumes "abstract state_impl = state"
          "orlins_call_cond state" 
          "implementation_invar state_impl"
          "aux_invar state"
          "invar_non_zero_b state"
          "invar_gamma state"
          "orlins_entry state"
          "invar_forest state"
          "invar_isOptflow state"
          "invar_integral state"
 shows    "abstract (orlins_upd_impl state_impl) = orlins_upd state"
          "implementation_invar  (orlins_upd_impl state_impl)"
          "return (orlins_upd state) = notyetterm \<Longrightarrow> invar_non_zero_b (orlins_upd state)"
proof(all \<open>rule orlins_call_condE[OF assms(2)]\<close>, goal_cases)
  case (1 f b \<gamma> E' \<gamma>' state' state'')
  have state''_is:"state'' = orlins_upd state"
    by(auto simp add: orlins_upd_def 1 Let_def)
  define f_impl where "f_impl = current_flow_impl state_impl"
  define b_impl where "b_impl = balance_impl state_impl"
  define \<gamma>_impl where "\<gamma>_impl = current_\<gamma>_impl state_impl"
  define E'_impl where "E'_impl = actives_impl state_impl"
  define \<gamma>'_impl where "\<gamma>'_impl = (if are_all (\<lambda> e. the (flow_lookup f_impl e) = (0::real)) E'_impl then
                             min (\<gamma>_impl / 2) (get_max (\<lambda> x bx. \<bar> bx \<bar>) b_impl)
                             else (\<gamma>_impl / 2))"
  define state'_impl where "state'_impl = loopA_impl (state_impl\<lparr>current_\<gamma>_impl := \<gamma>'_impl\<rparr>)"
  define state''_impl where "state''_impl = loopB_impl state'_impl"
  have state''_impl_is: "state''_impl = orlins_upd_impl state_impl"
    by(auto simp add: state''_impl_def state'_impl_def \<gamma>'_impl_def E'_impl_def \<gamma>_impl_def 
                      b_impl_def f_impl_def orlins_upd_impl_def Let_def)

  text \<open>Correspondences\<close>
  have f0_coincide[simp]: "abstract_flow_map f_impl = f"
    using assms(1) 1 f_impl_def by simp
  have b0_coincide[simp]: "abstract_bal_map b_impl = b"
    using assms(1) 1 b_impl_def by simp
  have g0_coincide[simp]: "\<gamma>_impl = \<gamma>"
    using assms(1) 1 \<gamma>_impl_def by simp
  have E'_coincide[simp]: "E'_impl = E'"
    using 1 E'_impl_def assms(1) by simp
  have E_flow_coincide[simp]: "e \<in> \<E> \<Longrightarrow> the (flow_lookup f_impl e) = f e" for e
    using assms(3)  sym[OF f0_coincide]
    by (auto simp add: f_impl_def implementation_invar_def)
  have E'_in_E[simp]:"to_set E' \<subseteq> \<E>"
    using assms(4) by(auto elim: aux_invarE invar_aux1E simp add: 1(5))
  have E'_flow_coincide[simp]: "e \<in> to_set E' \<Longrightarrow> the (flow_lookup f_impl e) = f e" for e
    using E_flow_coincide E'_in_E by blast
  have bal_domain_is_V: "bal_domain b_impl = \<V>"
    using assms b_impl_def by auto
  have bal_coincide: "x \<in> bal_domain b_impl \<Longrightarrow> the (bal_lookup b_impl x) = b x" for x
    using assms b_impl_def
    using b0_coincide by blast
  have bal_invar[simp]: "bal_invar b_impl" 
    using assms b_impl_def by blast
  have g'_coincide[simp]: "\<gamma>'_impl = \<gamma>'"
    unfolding 1(6) \<gamma>'_impl_def
  proof(rule if_cong, goal_cases)
    case 1
    then show ?case 
      using assms E'_impl_def 
      by (auto simp add: are_all)
  next
    case 2
    show ?case
      apply(insert 2, rule cong[of "min _" "min _"], simp)
      apply(subst get_max, simp)
      using  V_non_empt bal_domain_is_V apply simp
      apply(rule arg_cong[of _ _ Max], subst bal_domain_is_V)
      using bal_coincide[simplified bal_domain_is_V] by force
  qed simp
  have new_gamma_gamma': "\<gamma>' = new_\<gamma> state"
    by(simp add: 1 new_\<gamma>_def Let_def)

  have aux_invar_g[simp]: "aux_invar (state\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    using assms aux_invar_gamma by auto
  hence loopA_g_dom[simp]:"loopA_dom (state\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    using termination_of_loopA' by blast
  have abstract_g[simp]: "abstract (state_impl\<lparr>current_\<gamma>_impl := \<gamma>'\<rparr>) = state\<lparr>current_\<gamma> := \<gamma>'\<rparr>"
    using assms by(auto simp add: abstractE' simp del: abstractE)
  have impl_inv_abstr[simp]: " implementation_invar (state_impl\<lparr>current_\<gamma>_impl := \<gamma>'\<rparr>)"
    by(rule  implementation_invarI)
      (rule implementation_invarE[OF assms(3)], simp add: abstractE' del: abstractE)+
  have invar_Gamma_g[simp]: "invar_gamma (state\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    using assms by ((subst 1)+, intro gamma_upd_aux_invar_pres) auto
  have state'_coincide[simp]: "abstract state'_impl = state'"
    by(auto intro: abstract_impl_same_whole_loopA'(1) simp add: state'_impl_def 1(7))
  have impl_inv_state'[simp]: "implementation_invar state'_impl"
    by(auto intro!: abstract_impl_same_whole_loopA'(2) simp add: state'_impl_def 1(7))
  have invar_gamma_state'[simp]: "invar_gamma state'"
    using assms(5-6) 
    by (auto intro: loopA_invar_gamma_pres simp add: 1(7)) 
  have loopB_dom_state'[simp]: "loopB_dom state'"
    by(auto intro: loopB_termination)
  have aux_invar_state'[simp]:"aux_invar state'"
    by(auto intro: loopA_invar_aux_pres simp add: 1(7))


 have aux_invar_gamma_upd: "aux_invar (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    by(auto intro: aux_invar_gamma simp add: assms)
  have invar_gamma_gamma_upd: "invar_gamma (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding new_\<gamma>_def Let_def
    by(fastforce intro: gamma_upd_aux_invar_pres simp add: assms)
  hence new_gamma_0: "new_\<gamma> state > 0" unfolding invar_gamma_def by auto
  have same_gamma_loopA: "current_\<gamma> (loopA (state \<lparr>current_\<gamma> := \<gamma>'\<rparr>)) =
                            \<gamma>'"
    using gamma_pres aux_invar_g
    by auto
  have init_Phi_below_N:"\<Phi> (state\<lparr>current_\<gamma> := \<gamma>'\<rparr>) \<le> N"
    by((subst 1)+, intro Phi_init[simplified new_\<gamma>_def Let_def]) (auto simp add: assms)
  have Phi_after_below2N: " \<Phi> ((loopA (state \<lparr>current_\<gamma> := \<gamma>'\<rparr>))) \<le> 2*N"
    using Phi_increase_below_N init_Phi_below_N aux_invar_g  init_Phi_below_N by fastforce
  have card_below_N: "v \<in> \<V> \<Longrightarrow> card (connected_component (to_graph (\<FF>_imp state)) v) \<le> N" for v
    using N_def assms aux_invar_def[of state] invar_aux10_def[of state] 
     card_mono[OF \<V>_finite, of "connected_component (to_graph (\<FF>_imp state)) v"] by simp
  have card_above_0: "v \<in> \<V> \<Longrightarrow> card (connected_component (to_graph (\<FF>_imp state)) v) > 0" for v
    using  assms aux_invar_def[of state] invar_aux10_def[of state] 
      \<V>_finite V_non_empt finite_subset
     by (fastforce simp add: connected_component_def)
  have invarA_1:"invarA_1 (2 * new_\<gamma> state) (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding invarA_1_def apply rule
    subgoal for v 
    apply(simp, rule order.trans[OF balance_less_new_gamma[OF _ assms(7)]], simp)
      using card_above_0[of v]  new_gamma_0 by fastforce
    done  
  have invar_A2:"invarA_2 (8 * real N * new_\<gamma> state) (2 * new_\<gamma> state) (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding invarA_2_def
    apply (rule, rule order.strict_trans1[of _ " 8 * real N * new_\<gamma> state"]) 
    using new_gamma_0 new_gamma_below_half_gamma[of state]  N_gtr_0 assms(8)[simplified invar_forest_def] 
    by(auto intro:  order.strict_trans1[of _ "8* real N * (current_\<gamma> state / 2)"]
         simp add: algebra_simps)
   have loopA_entry: "loopA_entry (state\<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    unfolding loopA_entry_def
    using new_gamma_0 new_gamma_below_half_gamma[of state]  N_gtr_0 assms(8)[simplified invar_forest_def] 
    by(auto intro:  order.strict_trans1[of _ "8* real N * (current_\<gamma> state / 2)"]
         simp add: algebra_simps)
  have loopB_entryF:"loopB_entryF (loopA (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)) "
    using invarA_1 invar_A2 
    by(auto intro: loopB_entryF[OF aux_invar_gamma_upd loopA_entry invar_gamma_gamma_upd refl])
  have Phi_N_diff_pos:"real_of_int (int (2 * N) - \<Phi> state') * current_\<gamma> state' \<ge> 0"
    using invar_gamma_state' Phi_after_below2N 
    by(auto simp add: invar_gamma_def 1 new_\<gamma>_def Let_def )
  have forest_flow: "e \<in> \<F> state' \<Longrightarrow>
         real (6 * N) * current_\<gamma> state' - real_of_int (int (2 * N) - \<Phi> state') * current_\<gamma> state'
         \<le> current_flow state' e" for e
    apply(rule order.trans[of _ "real (6 * N) * current_\<gamma> state'"])
    using Phi_N_diff_pos apply simp
    apply(rule order.strict_implies_order)
    using loopB_entryF  unfolding loopB_entryF new_\<gamma>_def 1 Let_def loopB_entryF_def 
    by force
  have optflow_state_upd[simp]: "invar_isOptflow (state\<lparr>current_\<gamma> := \<gamma>'\<rparr>)"
    using assms(9) by(simp add: invar_isOptflow_def)

  have optflow_state'[simp]: "invar_isOptflow state'"
    unfolding 1(7)
    using invarA_1 sym[OF new_gamma_gamma'] invar_A2 new_gamma_0 
    by(intro flow_optimatlity_pres) auto

  have invar_integralbeforeA[simp]: "invar_integral (state \<lparr>current_\<gamma> := new_\<gamma> state\<rparr>)"
    using assms(10)
    unfolding new_\<gamma>_def invar_integral_def Let_def
    by(auto intro: is_multiple_multiple[of "current_flow state _"  "current_\<gamma> state"]) 

  have integral_state'[simp]: "invar_integral state'"
    unfolding 1(7)
    using invarA_1 sym[OF new_gamma_gamma'] invar_A2 new_gamma_0 
    by(intro loopA_invar_integral_pres) auto
    
  have state''_coincide[simp]: "abstract state''_impl = state''"
    using forest_flow 
    by(fastforce intro!: loopB_abstract_corresp_result(1) simp add: state''_impl_def 1(8))

  have impl_inv_state''[simp]:"implementation_invar state''_impl"
    using forest_flow 
    by (fastforce intro!: loopB_abstract_corresp_result(2)[of state'] simp add: state''_impl_def 1(8))

  show "abstract (orlins_upd_impl state_impl) = orlins_upd state"
    using sym[OF state''_is] sym[OF state''_impl_is] by simp

  show "implementation_invar (orlins_upd_impl state_impl)" 
    using sym[OF state''_impl_is] by simp

  have "return state'' = notyetterm \<Longrightarrow> invar_non_zero_b state''"
    by(force intro: remaining_balance_after_loopB[OF _ refl] simp add:  1(8))

  thus "return (orlins_upd state) = notyetterm \<Longrightarrow> invar_non_zero_b (orlins_upd state)"
    using sym[OF state''_is] by simp
qed

lemma orlins_upd_orlins_one_step: "orlins_one_step state = orlins_upd state "
  by(auto simp add: orlins_upd_def orlins_one_step_def Let_def)

lemmas aux_invar_pres_orlins_upd_step = aux_invar_pres_orlins_one_step[simplified orlins_upd_orlins_one_step]

lemmas invar_gamma_pres_orlins_one_step' = invar_gamma_pres_orlins_one_step[simplified orlins_upd_orlins_one_step]

lemmas orlins_entry_after_upd = orlins_entry_ofter_one_step[simplified orlins_upd_orlins_one_step]
lemmas invar_forest_pres_orlins_upd = invar_forest_pres_orlins_one_step[simplified orlins_upd_orlins_one_step]

lemma orlins_impl_corresp_general:
  assumes  "orlins_dom state" 
           "abstract state_impl = state"
           "implementation_invar state_impl"
           "aux_invar state"
           "return state = notyetterm \<Longrightarrow> invar_non_zero_b state"
           "invar_gamma state"
           "return state = notyetterm \<Longrightarrow> orlins_entry state"
           "invar_forest state"
          "invar_isOptflow state"
          "invar_integral state"
        shows "abstract (orlins_impl state_impl) = orlins state \<and> 
              implementation_invar (orlins_impl state_impl)"
  using assms(2-)
proof(induction arbitrary: state_impl rule: orlins_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case 
  proof(cases rule: orlins_cases[of state])
    case 1
    show ?thesis 
      apply(subst orlins_impl.simps,subst orlins_impl.simps,
            subst orlins.psimps[OF IH(1)])
      by(auto intro: orlins_ret1_condE[OF 1] simp add: IH(3) Let_def  IH(4))
  next
    case 2
    show ?thesis 
      apply(subst orlins_impl.simps,subst orlins_impl.simps,
            subst orlins.psimps[OF IH(1)])
      by(auto intro: orlins_ret2_condE[OF 2] simp add: IH(3) Let_def IH(4))
  next
    case 3
    have ret_notyetterm:"return state = notyetterm" "return_impl state_impl = notyetterm"
      using IH(3) by(auto intro: orlins_call_condE[OF 3])
    show ?thesis 
      apply(subst orlins_impl.simps)
      apply(subst orlins.psimps[OF IH(1)])
      apply(subst if_not_P[of "_ = _"], simp add: ret_notyetterm IH(3))+
      apply(subst Let_def)+
      apply(subst symmetric[OF orlins_upd_def[simplified Let_def]])
      apply(subst symmetric[OF orlins_upd_impl_def[simplified Let_def]])
      apply(subst (2) orlins_impl.simps)
      apply(subst if_not_P[of "_ = _"], simp add: ret_notyetterm IH(3))+
      apply(subst Let_def)+
      apply(subst symmetric[OF orlins_upd_impl_def[simplified Let_def]])
      apply(rule IH(2))
      using IH(3-) 3 ret_notyetterm
      by(auto intro: IH(2)[OF 3] aux_invar_pres_orlins_upd_step invar_gamma_pres_orlins_one_step'
                            orlins_entry_after_upd  invar_forest_pres_orlins_upd orlins_step_corresp 
                            optimality_pres_orlins_one_step[simplified orlins_upd_orlins_one_step]
                            invar_integral_pres_orlins_one_step[simplified orlins_upd_orlins_one_step])
 qed
qed

lemmas orlins_impl_corresp=conjunct1[OF orlins_impl_corresp_general]
lemmas orlins_impl_impl_invar=conjunct2[OF orlins_impl_corresp_general]

lemma initial_corresp: "abstract initial_impl = initial"
  unfolding initial_impl_def initial_def abstract_def Let_def
proof(rule Algo_state.equality, goal_cases)
  case 1
  show ?case 
    using flow_update_all(1,4)[OF init_flow(1)] 
    by (subst abstract_flow_map_def)
       (fastforce simp add: dom_def)
next
  case 2
  show ?case 
        using init_bal[simplified dom_def]
    by (subst abstract_bal_map_def) fastforce    
next
  case 7
  show ?case
    apply(simp del: abstractE)
    apply(subst get_max[OF init_bal(1)])
    using init_bal  V_non_empt apply simp
    apply(subst init_bal(2))
    using init_bal(3)[simplified init_bal(2)] by metis
next
  case 8
  show ?case 
    apply(simp del: abstractE )
    unfolding abstract_rep_map_def  id_def
    apply(rule ext, rule P_of_ifI)
    apply(subst rep_comp_update_all(1)[OF init_rep_card(1), simplified dom_def])
    using domIff init_rep_card(1) update_alls(3)[OF init_rep_card(1), simplified dom_def]
    by fastforce+
next
  case 9
  show ?case 
    apply(simp del: abstractE )
    unfolding abstract_comp_map_def 
    apply(rule ext, rule P_of_ifI)
    apply(subst rep_comp_update_all(1)[OF init_rep_card(1), simplified dom_def])
    using domIff init_rep_card(1) update_alls(3)[OF init_rep_card(1), simplified dom_def]
    by fastforce+
next
  case 11
  show ?case 
    apply(simp del: abstractE )
    unfolding abstract_not_blocked_map_def 
    apply(rule ext, rule P_of_ifI)
    using not_blocked_update_all(4)[OF init_not_blocked(1)] dom_def
          init_not_blocked(2) apply fast
    apply(subst not_blocked_update_all(1)[OF init_not_blocked(1), simplified dom_def]) 
    using not_blocked_update_all(4)[OF init_not_blocked(1), simplified dom_def] init_not_blocked(2)
    unfolding dom_def 
    by fastforce+
qed (simp del: abstractE  add: abstract_flow_map_def abstract_conv_map_def dom_def  conv_map.map_empty
                               to_graph_def empty_forest_axioms(1) neighb.emptyD(3) neighb.set.invar_empty 
                               neighb.set.set_isin  abstract_def Let_def )+

lemma initial_impl_implementation_invar: "implementation_invar initial_impl"
  apply(subst initial_impl_def, rule implementation_invarI, simp_all del: abstractE)
  apply(auto intro: flow_update_all(3) invar_filter
          simp add: flow_update_all(4) init_flow init_bal \<E>_impl_meaning(2) empty_forest_axioms
                     neighb.set.invar_empty)[7]
  apply(auto simp add: to_set_of_adjacency_def dom_def empty_forest_axioms(1) neighb.set.set_isin 
                       neighb.set.invar_empty neighb.set.set_empty  conv_map.map_empty )[1]
  by (auto intro: rep_comp_update_all(3)
           simp add: conv_map.invar_empty init_rep_card rep_comp_update_all(4) init_not_blocked
                     not_blocked_update_all(4))

lemma init_orlins_impl_corresp_general:
"abstract (orlins_impl (loopB_impl initial_impl)) = orlins (loopB initial)
\<and> implementation_invar (orlins_impl (loopB_impl initial_impl))"
proof(cases "\<forall> v \<in> \<V>. \<b> v = 0")
  case True
  hence succ_Cond:"loopB_succ_cond initial"
    by(auto intro: loopB_succ_condI simp add: initial_def)
  hence dom:"loopB_dom initial" 
    by(auto intro: loopB.domintros simp add: True initial_def)
  have sorresp:"abstract (loopB_impl initial_impl) = loopB initial"
    apply(subst loopB_simps(1)[OF dom succ_Cond], subst loopB_impl_simps_succ)
    using dom initial_corresp aux_invar_initial initial_impl_implementation_invar succ_Cond
    by(auto intro: loopB_succ_abstract_corresp(1))
  moreover have "return (loopB initial) = success"
    by(auto simp add: loopB_simps'(1)[OF succ_Cond] loopB_succ_upd_def Let_def)
  moreover hence "return_impl (loopB_impl initial_impl) = success" 
    by(auto simp add: sorresp)
  moreover have " implementation_invar (local.loopB_impl initial_impl)"
    using initial_corresp initial_impl_implementation_invar
           loopB_impl_simps_succ loopB_succ_abstract_corresp(2) succ_Cond by presburger
  ultimately show ?thesis
    by(subst orlins.psimps)      
      (auto simp add: Let_def orlins_impl.simps intro: orlins.domintros)
next
  case False
  hence invar_gamma_initial:"invar_gamma initial"
    by(auto intro: invar_gamma_initial)
  have emptyF: "\<F> initial  = {}"
    by (auto simp add:  initial_def to_graph_def empty_forest_axioms(1) to_rdgs_def 
                        neighb.set.set_empty neighb.set.set_isin neighb.set.invar_empty)
  have corresp_after_loopB:"abstract (loopB_impl initial_impl) = loopB initial"
    by(intro loopB_abstract_corresp_result(1))
      (auto intro: loopB_termination 
         simp add: invar_gamma_initial invar_isOptflow_initial   invar_integral_initial initial_corresp 
                   initial_impl_implementation_invar aux_invar_initial emptyF)
  have impl_inv_after_loopB:"implementation_invar (loopB_impl initial_impl)"
    using emptyF by(intro loopB_abstract_corresp_result(2))
      (auto intro: loopB_termination 
         simp add: invar_gamma_initial invar_isOptflow_initial  invar_integral_initial initial_corresp 
                   initial_impl_implementation_invar   aux_invar_initial)
  show ?thesis
  proof(cases "return (loopB initial) \<noteq> notyetterm")
    case True
    thus ?thesis 
      using corresp_after_loopB impl_inv_after_loopB
      apply(subst orlins.psimps)
      subgoal
        apply(rule orlins.domintros) 
        by(auto intro: return.exhaust)
      by(auto simp add: orlins_impl.simps intro: return.exhaust[of "return (local.loopB initial)"])
  next
    case False
    hence notyetterm: "return (loopB initial) = notyetterm"
      by(auto intro: return.exhaust)
    have invar_Forest_after_loopB: "invar_forest (loopB initial)"
      using  emptyF
      by(subst invar_forest_def, subst loopB_changes_\<F>) 
        (auto intro!:  loopB_termination simp add: invar_gamma_initial notyetterm)
    show ?thesis 
      using emptyF
      by(auto intro!: orlins_impl_corresp remaining_balance_after_loopB[OF _ refl] loopB_termination
                      loopB_invar_aux_pres loopB_invar_gamma_pres orlins_entry_after_loopB[OF _ refl]  
                        loopB_invar_isOpt_pres loopB_invar_integral_pres orlins_impl_impl_invar
             simp add: invar_gamma_initial invar_Forest_after_loopB notyetterm aux_invar_initial
                      impl_inv_after_loopB corresp_after_loopB initial_state_orlins_dom_and_results(1)[OF refl]
                      invar_isOptflow_initial  invar_integral_initial )
  qed
qed

lemmas init_orlins_impl_corresp = conjunct1[OF init_orlins_impl_corresp_general]
lemmas final_implementation_invar = conjunct2[OF init_orlins_impl_corresp_general]

corollary orlins_impl_is_correct:
  assumes "state' = orlins_impl (loopB_impl initial_impl)"
    shows "return_impl state' = success \<Longrightarrow> is_Opt \<b> (abstract_flow_map (current_flow_impl state'))"
          "return_impl state' = failure \<Longrightarrow> \<nexists> f. f is \<b> flow"
          "return_impl state' = notyetterm \<Longrightarrow> False"
  using  assms  init_orlins_impl_corresp initial_state_orlins_dom_and_results[OF refl]
  by auto 

lemma final_flow_domain: "flow_domain (current_flow_impl (orlins_impl (loopB_impl initial_impl))) = \<E>"
  using final_implementation_invar
  by(simp add: implementation_invar_def)

lemmas code_lemmas[code] = loopB_impl.simps loopA_impl.simps orlins_impl.simps
                           augment_edges_impl.simps 
end
end