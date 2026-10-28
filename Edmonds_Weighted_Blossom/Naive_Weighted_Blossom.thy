theory Naive_Weighted_Blossom
  imports Laminar_Family.Laminar_Family Matching_LPs.Edmonds_Matching_LP
    "HOL-Library.Disjoint_Sets" Data_Structures.More_Arith Partition_Quotient_Graph
begin

section \<open>Outline of the Weighted Matching Algorithm (see KV)\<close>

lemma near_perfect_matching_odd:
  assumes "dblton_graph M" "matching M" "Vs M = X - {x}" "x \<in> X" "finite X"
  shows "odd (card X)"
proof-
  have "card X = card (X - {x}) + 1"
    using assms(4,5) Suc_eq_plus1[of "card (X - {x})"] card.remove[of X x]
    by linarith
  also have "card (X - {x}) = card (Vs M)"
    using assms(3) by argo
  also have "card (Vs M) = 2 * card M" 
    using assms(1,2,3,5) graph_inter_Vs_subset(1)
    by(force intro!: graph_abs.matching_card_vs[symmetric] simp add: graph_abs_def)+
  finally show ?thesis
    by simp
qed

lemma maximal_sets_in_laminar_family_are_global_partition:
  assumes "laminar U \<X>" "finite U"
  shows "partition_on (\<Union> \<X>) (maximal_sets \<X>)"
proof-

  show ?thesis
  proof(rule partition_onI, goal_cases)
    case 1
    then show ?case
      using finite_U_finite_family[OF assms(2,1)]
      by(auto simp add: maximal_sets_def)(auto dest!: finite_has_maximal2[of \<X>] )
  next
    case (2 X Y)
    then show ?case 
      using assms(1) 
      by(auto simp add: disjnt_def dest: laminar_maximal_sets_disjoint)
  next
    case 3
    then show ?case 
      using assms(1) laminar_maximal_sets_nempty by auto
  qed
qed

subsection \<open>Definition of Main Loop, Setup\<close>

datatype 'a MOD = match "'a set set" | decomp "'a set set"

locale find_matching_or_decomposition_spec =
  fixes find_matching_or_decomposition::"'v set set \<Rightarrow> 'v MOD"
  assumes find_matching_or_decomposition_correct:
    "\<And> E. \<lbrakk>graph_invar E; \<exists> M. perfect_matching E M\<rbrakk> 
         \<Longrightarrow> \<exists> M. find_matching_or_decomposition E = match M"
    "\<And> E. \<lbrakk>graph_invar E; \<nexists> M. perfect_matching E M\<rbrakk> 
         \<Longrightarrow> \<exists> D. find_matching_or_decomposition E = decomp D"
    "\<And> E M. \<lbrakk>graph_invar E; find_matching_or_decomposition E = match M\<rbrakk> \<Longrightarrow>
           perfect_matching E M"  
    "\<And> E D.  \<lbrakk>graph_invar E; find_matching_or_decomposition E = decomp D\<rbrakk> \<Longrightarrow>
          disjoint D"
    "\<And> E D.  \<lbrakk>graph_invar E; find_matching_or_decomposition E = decomp D\<rbrakk> \<Longrightarrow>
          \<Union> D \<subseteq> Vs E"
    "\<And> E D X Y.  \<lbrakk>graph_invar E; find_matching_or_decomposition E = decomp D; X \<in> D; Y \<in> D; X \<noteq> Y\<rbrakk> \<Longrightarrow>
          \<nexists> u v. {u, v} \<in> E \<and> u \<in> X \<and> v \<in> Y"
    "\<And> E D.  \<lbrakk>graph_invar E; find_matching_or_decomposition E = decomp D\<rbrakk> \<Longrightarrow>
          card D > card (Neighbourhood E (\<Union> D))"  
    "\<And> E D X x.  \<lbrakk>graph_invar E; find_matching_or_decomposition E = decomp D; X \<in> D; x \<in> X\<rbrakk> \<Longrightarrow>
          \<exists> M. graph_matching (E\<lbrakk>X\<rbrakk>) M \<and> Vs M = X - {x}"   
    "\<And> E D X.  \<lbrakk>graph_invar E; find_matching_or_decomposition E = decomp D; X \<in> D\<rbrakk> \<Longrightarrow> X\<noteq>{}" 

locale naive_weighted_blossom_main_loop =
  graph_abs where G = G +
  find_matching_or_decomposition_spec where 
  find_matching_or_decomposition = find_matching_or_decomposition
for G::"'v set set" and find_matching_or_decomposition::"'v set set set \<Rightarrow> 'v set MOD" + 
fixes w::"'v set \<Rightarrow> real"
  and sel::"('v set \<Rightarrow> bool) \<Rightarrow> 'v set set \<Rightarrow> 'v set"
assumes sel_correct: "\<And> P X. \<lbrakk>\<exists> x \<in> X. P x;finite X\<rbrakk> \<Longrightarrow> sel P X \<in> X"
  "\<And> P X. \<lbrakk>\<exists> x \<in> X. P x;finite X\<rbrakk> \<Longrightarrow> P (sel P X)"
begin

definition "\<w> \<pi> = (\<lambda> e. w e - sum \<pi> (end_sets G e))"

function (domintros) top_loop::"(('v set \<Rightarrow> real) \<times> 'v set set) 
           \<Rightarrow> (('v set \<Rightarrow> real) \<times> 'v set set set \<times> 'v set set) option"
  where 
    "top_loop (\<pi>, \<OO>) = 
    (let Gt = odd_tight_subgraph G w \<pi>;
         maxes = maximal_sets \<OO> in 
         (if (\<exists> Blos. Blos \<in> maxes \<and> \<not> (\<exists> e. e \<in> Gt \<and> e \<in> Delta G Blos))
         then (let Blos = sel (\<lambda> Blos. \<not> (\<exists> e. e \<in> Gt \<and> e \<in> Delta G Blos)) maxes
              in (if Delta G Blos = {} then None
                 else let \<epsilon> = Min ((if card Blos > 1 then {\<pi> Blos} else {}) \<union> {\<w> \<pi> e | e. e \<in> Delta G Blos});
                          \<pi>' = (\<lambda> X. if X = Blos then \<pi> Blos + \<epsilon> else \<pi> X)
                      in top_loop (\<pi>', \<OO>)))
         else (case find_matching_or_decomposition (Gt \<sslash> maxes) of 
                    match M \<Rightarrow> Some (\<pi>, M, \<OO>)
                   | decomp D \<Rightarrow> 
                     if (\<forall> X \<in> D. Neighbourhood G (\<Union> X) \<subseteq> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)))
                       \<and> \<not> (\<exists> X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D). 1 < card X)
                     then None
                     else let \<epsilon> = Min ({\<pi> X | X. X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<and> card X > 1}
                               \<union> {1/2 * \<w> \<pi> {u, v} | u v X Y. X \<in> D \<and> Y \<in> D \<and> X \<noteq> Y \<and> u \<in> \<Union> X 
                                          \<and> v \<in> \<Union> Y \<and> {u, v} \<in> G}
                               \<union> {\<w> \<pi> {u, v} | u v. u \<in>(\<Union> (\<Union> D)) 
                                       \<and> v \<notin> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)) \<union> (\<Union> (\<Union> D)) 
                                       \<and> {u, v} \<in> G});
                         \<pi>' = (\<lambda> X. if \<exists> XX. XX \<in> D \<and> \<Union> XX = X then \<pi> X + \<epsilon> 
                                    else if X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) then \<pi> X - \<epsilon>
                                    else \<pi> X);
                         \<OO>' = \<OO> - {X | X. X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<and> \<pi> X = \<epsilon> \<and> card X > 1}
                               \<union> {\<Union> X | X. X \<in> D}
                     in top_loop (\<pi>', \<OO>'))))"
  by pat_completeness auto

definition top_loop_ret_None_1_cond :: "('v set \<Rightarrow> real) \<Rightarrow> 'v set set \<Rightarrow> bool" where
  "top_loop_ret_None_1_cond \<pi> \<OO> \<equiv> 
  let Gt = odd_tight_subgraph G w \<pi>;
      maxes = maximal_sets \<OO>
  in (\<exists> Blos. Blos \<in> maxes \<and> \<not> (\<exists> e. e \<in> Gt \<and> e \<in> Delta G Blos)) \<and> 
     Delta G (sel (\<lambda> Blos. \<not> (\<exists> e. e \<in> Gt \<and> e \<in> Delta G Blos)) maxes) = {}"

definition top_loop_ret_None :: "('v set \<Rightarrow> real) \<Rightarrow> 'v set set \<Rightarrow> (('v set \<Rightarrow> real) \<times> 'v set set set\<times> 'v set set) option" where
  "top_loop_ret_None \<pi> \<OO> \<equiv> None"

definition top_loop_call1_cond :: "('v set \<Rightarrow> real) \<Rightarrow> 'v set set \<Rightarrow> bool" where
  "top_loop_call1_cond \<pi> \<OO> \<equiv> 
  let Gt = odd_tight_subgraph G w \<pi>;
      maxes = maximal_sets \<OO>
  in (\<exists> Blos. Blos \<in> maxes \<and> \<not> (\<exists> e. e \<in> Gt \<and> e \<in> Delta G Blos)) \<and> 
     Delta G (sel (\<lambda> Blos. \<not> (\<exists> e. e \<in> Gt \<and> e \<in> Delta G Blos)) maxes) \<noteq> {}"

definition top_loop_call1 :: "('v set \<Rightarrow> real) \<Rightarrow> 'v set set \<Rightarrow> (('v set \<Rightarrow> real) \<times> 'v set set)" where
  "top_loop_call1 \<pi> \<OO> \<equiv> 
  let Gt = odd_tight_subgraph G w \<pi>;
      maxes = maximal_sets \<OO>;
      Blos = sel (\<lambda> Blos. \<not> (\<exists> e. e \<in> Gt \<and> e \<in> Delta G Blos)) maxes;
      \<epsilon> = Min ((if card Blos > 1 then {\<pi> Blos} else {}) \<union> {\<w> \<pi> e | e. e \<in> Delta G Blos});
      \<pi>' = (\<lambda> X. if X = Blos then \<pi> Blos + \<epsilon> else \<pi> X)
  in (\<pi>', \<OO>)"

definition top_loop_ret_Some_cond :: "('v set \<Rightarrow> real) \<Rightarrow> 'v set set \<Rightarrow> bool" where
  "top_loop_ret_Some_cond \<pi> \<OO> \<equiv> 
  let Gt = odd_tight_subgraph G w \<pi>;
      maxes = maximal_sets \<OO>
  in \<not> (\<exists> Blos. Blos \<in> maxes \<and> \<not> (\<exists> e. e \<in> Gt \<and> e \<in> Delta G Blos)) \<and> 
     (\<exists> M. find_matching_or_decomposition (Gt \<sslash> maxes) = match M)"

definition to_loop_ret_Some :: "('v set \<Rightarrow> real) \<Rightarrow> 'v set set
 \<Rightarrow> (('v set \<Rightarrow> real) \<times> 'v set set set \<times> 'v set set)" where
  "to_loop_ret_Some \<pi> \<OO> \<equiv> 
  let Gt = odd_tight_subgraph G w \<pi>;
      maxes = maximal_sets \<OO>
  in case find_matching_or_decomposition (Gt \<sslash> maxes) of 
       match M \<Rightarrow> (\<pi>, M, \<OO>)"

definition top_loop_ret_None_2_cond :: "('v set \<Rightarrow> real) \<Rightarrow> 'v set set \<Rightarrow> bool" where
  "top_loop_ret_None_2_cond \<pi> \<OO> \<equiv> 
  let Gt = odd_tight_subgraph G w \<pi>;
      maxes = maximal_sets \<OO>
  in \<not> (\<exists> Blos. Blos \<in> maxes \<and> \<not> (\<exists> e. e \<in> Gt \<and> e \<in> Delta G Blos)) \<and> 
     (\<exists> D. find_matching_or_decomposition (Gt \<sslash> maxes) = decomp D \<and>
       (\<forall> X \<in> D. Neighbourhood G (\<Union> X) \<subseteq> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)))
       \<and> \<not> (\<exists> X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D). 1 < card X))"

definition top_loop_call2_cond :: "('v set \<Rightarrow> real) \<Rightarrow> 'v set set \<Rightarrow> bool" where
  "top_loop_call2_cond \<pi> \<OO> \<equiv> 
  let Gt = odd_tight_subgraph G w \<pi>;
      maxes = maximal_sets \<OO>
  in \<not> (\<exists> Blos. Blos \<in> maxes \<and> \<not> (\<exists> e. e \<in> Gt \<and> e \<in> Delta G Blos)) \<and> 
     (\<exists> D. find_matching_or_decomposition (Gt \<sslash> maxes) = decomp D \<and>
       (\<not> (\<forall> X \<in> D. Neighbourhood G (\<Union> X) \<subseteq> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)))
        \<or> (\<exists> X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D). 1 < card X)))"

definition top_loop_call2 :: "('v set \<Rightarrow> real) \<Rightarrow> 'v set set \<Rightarrow> (('v set \<Rightarrow> real) \<times> 'v set set)" where
  "top_loop_call2 \<pi> \<OO> \<equiv> 
  let Gt = odd_tight_subgraph G w \<pi>;
      maxes = maximal_sets \<OO>;
      D = (case find_matching_or_decomposition (Gt \<sslash> maxes) of decomp D \<Rightarrow> D);
      \<epsilon> = Min ({\<pi> X | X. X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<and> card X > 1}
             \<union> {1/2 * \<w> \<pi> {u, v} | u v X Y. X \<in> D \<and> Y \<in> D \<and> X \<noteq> Y \<and> u \<in> \<Union> X \<and> v \<in> \<Union> Y\<and> {u, v} \<in> G}
             \<union> {\<w> \<pi> {u, v} | u v. u \<in>(\<Union> (\<Union> D)) 
                                       \<and> v \<notin> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)) \<union> (\<Union> (\<Union> D)) 
                                       \<and> {u, v} \<in> G});
      \<pi>' = (\<lambda> X. if \<exists> XX. XX \<in> D \<and> \<Union> XX = X then \<pi> X + \<epsilon> 
                 else if X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) then \<pi> X - \<epsilon>
                 else \<pi> X);
      \<OO>' = \<OO> - {X | X. X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<and> \<pi> X = \<epsilon> \<and> card X > 1}
                               \<union> {\<Union> X | X. X \<in> D}
  in (\<pi>', \<OO>')"

lemma anti_arg_cong: "f x \<noteq> f y \<Longrightarrow> x \<noteq> y"
  by auto

lemma anti_arg_congE: "\<lbrakk>f x \<noteq> f y; x \<noteq> y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

lemma top_loop_simps:
  assumes "top_loop_dom (\<pi>, \<OO>)"
  shows "top_loop_ret_None_1_cond \<pi> \<OO> \<Longrightarrow> top_loop (\<pi>, \<OO>) = top_loop_ret_None \<pi> \<OO>"
    and "top_loop_call1_cond \<pi> \<OO> \<Longrightarrow> top_loop (\<pi>, \<OO>) = top_loop (top_loop_call1 \<pi> \<OO>)"
    and "top_loop_ret_Some_cond \<pi> \<OO> \<Longrightarrow> top_loop (\<pi>, \<OO>) = Some (to_loop_ret_Some \<pi> \<OO>)"
    and "top_loop_ret_None_2_cond \<pi> \<OO> \<Longrightarrow> top_loop (\<pi>, \<OO>) = top_loop_ret_None \<pi> \<OO>"
    and "top_loop_call2_cond \<pi> \<OO> \<Longrightarrow> top_loop (\<pi>, \<OO>) = top_loop (top_loop_call2 \<pi> \<OO>)"
proof(goal_cases)
  case 5
  define Gt where "Gt = odd_tight_subgraph G w \<pi>"
  define maxes where "maxes = maximal_sets \<OO>"
  obtain D where D_def: "find_matching_or_decomposition (Gt \<sslash> maxes) = decomp D"
    using 5 by(force simp add: Gt_def maxes_def top_loop_call2_cond_def Let_def)
  show ?case 
    unfolding top_loop.psimps[OF assms] Gt_def[symmetric] maxes_def[symmetric]
  proof(subst Let_def, subst Let_def,
      cases "\<exists>Blos. Blos \<in> maxes \<and> (\<nexists>e. e \<in> Gt \<and> e \<in> Delta G Blos)", goal_cases)
    case 1
    thus ?case
      using 5 by(auto simp add: Gt_def maxes_def top_loop_call2_cond_def Let_def)
  next
    case 2
    thus ?case
    proof(subst (4) if_not_P, goal_cases)
      case 2
      thus ?case
        unfolding D_def MOD.case
      proof(cases "\<forall>X\<in>D. Neighbourhood G (\<Union> X) \<subseteq> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)) \<and>
                     \<not> (\<exists>X\<in>Neighbourhood (Gt \<sslash> maxes) (\<Union> D). 1 < card X)", goal_cases)
        case 1
        thus ?case
          using 5 D_def in_NeighbourhoodE 
          by(fastforce simp add: Gt_def maxes_def top_loop_call2_cond_def Let_def)
      next
        case 2
        thus ?case
        proof(subst if_not_P, goal_cases)
          case 2
          thus ?case
            unfolding Let_def
          proof(intro arg_cong[of _ _ top_loop], unfold top_loop_call2_def Let_def, 
              intro arg_cong2[where f = Pair], goal_cases)
            case 1 
            thus ?case
              using D_def
              by (intro ext)(auto split: if_split simp add: maxes_def Gt_def)
          next
            case 2
            thus ?case
              using D_def
              by (auto split: if_split simp add: maxes_def Gt_def)
          qed
        qed auto
      qed
    qed
  qed
qed (auto simp add: top_loop.psimps[OF assms] top_loop_ret_None_def top_loop_call1_def
    to_loop_ret_Some_def top_loop_call2_def Let_def
    top_loop_ret_None_1_cond_def top_loop_ret_None_2_cond_def top_loop_call1_cond_def
    top_loop_ret_Some_cond_def top_loop_call2_cond_def
    split!: if_split MOD.split)

lemma top_loop_induct_fst_snd:
  assumes dom: "top_loop_dom (\<pi>, \<OO>)"
  assumes ret_None_1: "\<And>\<pi> \<OO>. \<lbrakk>top_loop_dom (\<pi>, \<OO>); top_loop_ret_None_1_cond \<pi> \<OO>\<rbrakk> \<Longrightarrow> P \<pi> \<OO>"
  assumes ret_None_2: "\<And>\<pi> \<OO>. \<lbrakk>top_loop_dom (\<pi>, \<OO>); top_loop_ret_None_2_cond \<pi> \<OO>\<rbrakk> \<Longrightarrow> P \<pi> \<OO>"
  assumes call1: "\<And>\<pi> \<OO>. \<lbrakk>top_loop_dom (\<pi>, \<OO>); top_loop_call1_cond \<pi> \<OO>;
                         P (fst (top_loop_call1 \<pi> \<OO>)) (snd (top_loop_call1 \<pi> \<OO>))\<rbrakk> \<Longrightarrow> P \<pi> \<OO>"
  assumes ret_Some: "\<And>\<pi> \<OO>. top_loop_dom (\<pi>, \<OO>) \<Longrightarrow> top_loop_ret_Some_cond \<pi> \<OO> \<Longrightarrow> P \<pi> \<OO>"
  assumes call2: "\<And>\<pi> \<OO>. \<lbrakk>top_loop_dom (\<pi>, \<OO>); top_loop_call2_cond \<pi> \<OO>;
                         P (fst (top_loop_call2 \<pi> \<OO>)) (snd (top_loop_call2 \<pi> \<OO>))\<rbrakk> \<Longrightarrow> P \<pi> \<OO>"
  shows "P \<pi> \<OO>"
  using dom
proof (induction "(\<pi>, \<OO>)" arbitrary: \<pi> \<OO> rule: top_loop.pinduct)
  case (1 \<pi> \<OO>)
  note IH = this
  show ?case
  proof (cases "top_loop_ret_None_1_cond \<pi> \<OO>")
    case True
    then show ?thesis 
      using ret_None_1 "1.hyps" by blast
  next
    case False
    note not_None = this
    show ?thesis
    proof (cases "top_loop_call1_cond \<pi> \<OO>")
      case True
      then show ?thesis 
        using call1 IH
        by(auto simp add: top_loop_call1_cond_def top_loop_call1_def Let_def)
    next
      case False
      note not_call1 = this
      show ?thesis
      proof (cases "top_loop_ret_Some_cond \<pi> \<OO>")
        case True
        then show ?thesis 
          using ret_Some "1.hyps" by blast
      next
        case False
        note not_ret_Some_cond = this
        show ?thesis
        proof(cases  "top_loop_ret_None_2_cond \<pi> \<OO>")
          case True
          then show ?thesis 
            by (simp add: IH(1) ret_None_2)
        next
          case False
          note not_Some = this

          have cond:"top_loop_call2_cond \<pi> \<OO>"
            using not_None not_call1 not_Some not_ret_Some_cond
            unfolding top_loop_ret_None_1_cond_def top_loop_call1_cond_def 
              top_loop_ret_Some_cond_def top_loop_call2_cond_def Let_def
              top_loop_ret_None_2_cond_def
            by (cases "find_matching_or_decomposition (odd_tight_subgraph G w \<pi> \<sslash> maximal_sets \<OO>)") auto

          have forw_subst2: "\<lbrakk>a = b ; c = d; P a c\<rbrakk> \<Longrightarrow> P b d" for a b c d by auto

          obtain D where D: "find_matching_or_decomposition (odd_tight_subgraph G w \<pi> \<sslash> maximal_sets \<OO>) = decomp D"
            using cond by(auto simp add: top_loop_call2_cond_def Let_def)

          show ?thesis
            using cond
          proof(intro call2[OF  IH(1) cond],  intro IH(3)[OF refl refl _ D _ refl], goal_cases)
            case 3
            then show ?case 
              by(intro ext)
                (auto simp add: top_loop_call2_cond_def top_loop_call2_def Let_def D 
                  split: if_split)
          qed (auto intro!: ext simp add: top_loop_call2_cond_def top_loop_call2_def Let_def D 
              split: if_split)
        qed
      qed
    qed
  qed
qed

lemma top_loop_induct:
  assumes dom: "top_loop_dom (\<pi>, \<OO>)"
  assumes ret_None_1: "\<And>\<pi> \<OO>. \<lbrakk>top_loop_dom (\<pi>, \<OO>); top_loop_ret_None_1_cond \<pi> \<OO>\<rbrakk> \<Longrightarrow> P (\<pi>, \<OO>)"
  assumes ret_None_2: "\<And>\<pi> \<OO>. \<lbrakk>top_loop_dom (\<pi>, \<OO>); top_loop_ret_None_2_cond \<pi> \<OO>\<rbrakk> \<Longrightarrow> P (\<pi>, \<OO>)"
  assumes call1: 
    "\<And>\<pi> \<OO>. \<lbrakk>top_loop_dom (\<pi>, \<OO>); top_loop_call1_cond \<pi> \<OO>; P (top_loop_call1 \<pi> \<OO>)\<rbrakk> \<Longrightarrow>  P (\<pi>, \<OO>)"
  assumes ret_Some: "\<And>\<pi> \<OO>. top_loop_dom (\<pi>, \<OO>) \<Longrightarrow> top_loop_ret_Some_cond \<pi> \<OO> \<Longrightarrow>  P (\<pi>, \<OO>)"
  assumes call2: 
    "\<And>\<pi> \<OO>. \<lbrakk>top_loop_dom (\<pi>, \<OO>); top_loop_call2_cond \<pi> \<OO>; P (top_loop_call2 \<pi> \<OO>)\<rbrakk> \<Longrightarrow>  P (\<pi>, \<OO>)"
  shows "P (\<pi>, \<OO>)"
  using assms
  by (auto intro: top_loop_induct_fst_snd[where P = "\<lambda> x y. P (x, y)"])

definition "odds_invar = (\<lambda> (\<pi>, \<OO>).
laminar (Vs G) \<OO> \<and> (\<forall> Bls \<in> \<OO>. odd (card Bls)) \<and> composed_family \<OO> \<and> \<Union>\<OO> = Vs G)"

lemma  odds_invarI: 
  "\<lbrakk>laminar (Vs G) \<OO>; \<forall>Bls \<in> \<OO>. odd (card Bls); composed_family \<OO>; \<Union>\<OO> = Vs G\<rbrakk> \<Longrightarrow> odds_invar (\<pi>, \<OO>)"
  and odds_invarE: 
  "\<lbrakk>odds_invar (\<pi>, \<OO>); 
      \<lbrakk>laminar (Vs G) \<OO>; \<forall>Bls \<in> \<OO>. odd (card Bls); composed_family \<OO>; \<Union>\<OO> = Vs G\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and odds_invarD: 
  "odds_invar (\<pi>, \<OO>) \<Longrightarrow> laminar (Vs G) \<OO>"
  "\<lbrakk>odds_invar (\<pi>, \<OO>); Bls \<in> \<OO>\<rbrakk> \<Longrightarrow> odd (card Bls)"
  "odds_invar (\<pi>, \<OO>) \<Longrightarrow> composed_family \<OO>"
  "odds_invar (\<pi>, \<OO>) \<Longrightarrow> \<Union>\<OO> = Vs G"
  unfolding odds_invar_def by auto

definition "odd_factor_critical_invar = (\<lambda> (\<pi>, \<OO>).
      (\<forall> X \<in> \<OO>. card X > 1 \<longrightarrow>
        (\<forall> Y \<in> immediate_subsets \<OO> X.
            (\<exists> M. graph_matching (odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk>\<sslash>(immediate_subsets \<OO> X)) M \<and>
                   Vs M = immediate_subsets \<OO> X - {Y}))))"

lemma odd_factor_critical_invarI: 
  "(\<And>X Y. \<lbrakk>X \<in> \<OO>; card X > 1; Y \<in> immediate_subsets \<OO> X\<rbrakk> \<Longrightarrow> 
      \<exists>M. graph_matching (odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk>\<sslash>(immediate_subsets \<OO> X)) M
     \<and> Vs M = immediate_subsets \<OO> X - {Y}) 
    \<Longrightarrow> odd_factor_critical_invar (\<pi>, \<OO>)"
  and odd_factor_critical_invarE: 
  "\<lbrakk>odd_factor_critical_invar (\<pi>, \<OO>); 
      (\<And> X Y. \<lbrakk>X \<in> \<OO>; card X > 1; Y \<in> immediate_subsets \<OO> X\<rbrakk> \<Longrightarrow> 
        \<exists>M. graph_matching (odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk>\<sslash>(immediate_subsets \<OO> X)) M
             \<and> Vs M = immediate_subsets \<OO> X - {Y}) \<Longrightarrow> P\<rbrakk> 
    \<Longrightarrow> P"
  and odd_factor_critical_invarD:
  "\<lbrakk>odd_factor_critical_invar (\<pi>, \<OO>); X \<in> \<OO>; card X > 1; Y \<in> immediate_subsets \<OO> X\<rbrakk> \<Longrightarrow> 
      \<exists>M. graph_matching (odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk>\<sslash>(immediate_subsets \<OO> X)) M \<and> Vs M = immediate_subsets \<OO> X - {Y}"
  unfolding odd_factor_critical_invar_def by auto

definition "invar_strict_odd_pos = (\<lambda> (\<pi>, \<OO>).
        \<forall> Bls \<in> \<OO>. card Bls > 1 \<longrightarrow> \<pi> Bls > 0)"

lemma 
  invar_strict_odd_posI: 
  "(\<And>Bls. \<lbrakk>Bls \<in> \<OO>; card Bls > 1\<rbrakk> \<Longrightarrow> \<pi> Bls > 0) \<Longrightarrow> invar_strict_odd_pos (\<pi>, \<OO>)"
  and invar_strict_odd_posE: 
  "\<lbrakk>invar_strict_odd_pos (\<pi>, \<OO>); (\<And> Bls. \<lbrakk>Bls \<in> \<OO>; card Bls > 1\<rbrakk> \<Longrightarrow> \<pi> Bls > 0) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and invar_strict_odd_posD: 
  "\<lbrakk>invar_strict_odd_pos (\<pi>, \<OO>); Bls \<in> \<OO>; card Bls > 1\<rbrakk> \<Longrightarrow> \<pi> Bls > 0"
  unfolding invar_strict_odd_pos_def by auto

definition "invar_non_zero_pi_in_odd = (\<lambda> (\<pi>, \<OO>). \<forall> X. \<pi> X \<noteq> 0 \<longrightarrow> X \<in> \<OO>)"

lemma 
  invar_non_zero_pi_in_oddI: 
  "(\<And>X. \<pi> X \<noteq> 0 \<Longrightarrow> X \<in> \<OO>) \<Longrightarrow> invar_non_zero_pi_in_odd (\<pi>, \<OO>)"
  and invar_non_zero_pi_in_oddE: 
  "\<lbrakk>invar_non_zero_pi_in_odd (\<pi>, \<OO>); (\<And> X. \<pi> X \<noteq> 0 \<Longrightarrow> X \<in> \<OO>) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and invar_non_zero_pi_in_oddD: 
  "\<lbrakk>invar_non_zero_pi_in_odd (\<pi>, \<OO>); \<pi> X \<noteq> 0\<rbrakk> \<Longrightarrow> X \<in> \<OO>"
  unfolding invar_non_zero_pi_in_odd_def by auto

definition "invar_feasible_pi = (\<lambda> (\<pi>, \<OO>). feasible_min_perfect_dual_edmonds G w \<pi>)"

lemma 
  invar_feasible_piI: 
  "feasible_min_perfect_dual_edmonds G w \<pi> \<Longrightarrow> invar_feasible_pi (\<pi>, \<OO>)"
  and invar_feasible_piE: 
  "\<lbrakk>invar_feasible_pi (\<pi>, \<OO>); feasible_min_perfect_dual_edmonds G w \<pi> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and invar_feasible_piD: 
  "invar_feasible_pi (\<pi>, \<OO>) \<Longrightarrow> feasible_min_perfect_dual_edmonds G w \<pi>"
  unfolding invar_feasible_pi_def by auto

lemma odd_invar_omega:
  assumes "odds_invar (\<pi>, \<OO>)" "X \<in> \<OO>"
  shows "X \<in> \<Omega> (Vs G)"
  using assms
  by (auto intro!: in_odd_subsetsI elim!: odds_invarE)

subsection \<open>Invariant Preservation\<close>

lemma top_loop_call1_pres:
  assumes "top_loop_call1_cond \<pi> \<OO>"
    "odds_invar (\<pi>, \<OO>)"
    "odd_factor_critical_invar (\<pi>, \<OO>)"
    "invar_strict_odd_pos (\<pi>, \<OO>)"
    "invar_non_zero_pi_in_odd (\<pi>, \<OO>)"
    "invar_feasible_pi (\<pi>, \<OO>)"
  shows  "odds_invar (top_loop_call1 \<pi> \<OO>)" (is ?th1)
    "odd_factor_critical_invar (top_loop_call1 \<pi> \<OO>)" (is ?th2)
    "invar_strict_odd_pos (top_loop_call1 \<pi> \<OO>)" (is ?th3)
    "invar_non_zero_pi_in_odd (top_loop_call1 \<pi> \<OO>)" (is ?th4)
    "invar_feasible_pi (top_loop_call1 \<pi> \<OO>)" (is ?th5)
proof-

  define Gt where "Gt = odd_tight_subgraph G w \<pi>"
  define maxes where "maxes = maximal_sets \<OO>"
  define Blos where "Blos = sel (\<lambda>Blos. \<nexists>e. e \<in> Gt \<and> e \<in> Delta G Blos) maxes"
  define \<epsilon> where "\<epsilon> = Min ((if 1 < card Blos then {\<pi> Blos} else {}) \<union> {\<w> \<pi> e |e. e \<in> Delta G Blos})"
  define \<pi>' where "\<pi>' = (\<lambda>X. if X = Blos then \<pi> Blos + \<epsilon> else \<pi> X)"

  have top_loop_call1_def: "top_loop_call1 \<pi> \<OO> = (\<pi>', \<OO>)"
    by(auto simp add: top_loop_call1_def Let_def \<pi>'_def Blos_def Gt_def maxes_def \<epsilon>_def)

  have Blos_in_maxes: "Blos \<in> maxes"
    using assms(1,2) finite_Vs union_split_with_maximal_sets[of \<OO>] finite_UnionD[of "maximal_sets \<OO>"]
      finite_UnionD[of \<OO>] odds_invarD(4)[of \<pi> \<OO>]
    unfolding Blos_def
    by(intro sel_correct(1))
      (auto simp add:  top_loop_call1_cond_def Gt_def maxes_def Let_def)

  have  Blos_props:"\<nexists>e. e \<in> Gt \<and> e \<in> Delta G Blos" 
    using assms(1,2) finite_Vs union_split_with_maximal_sets[of \<OO>] finite_UnionD[of "maximal_sets \<OO>"]
      finite_UnionD[of \<OO>] odds_invarD(4)[of \<pi> \<OO>]
    unfolding Blos_def
    by(intro sel_correct(2))
      (auto simp add:  top_loop_call1_cond_def Gt_def maxes_def Let_def)

  have more_blos_props: "Blos \<in> maximal_sets \<OO>" "Blos \<in> \<OO>"
    using Blos_in_maxes maxes_def in_maximal_setsE by auto

  show ?th1
    unfolding top_loop_call1_def
    using assms(2) 
    by(auto elim: odds_invarE intro: odds_invarI)

  note odds_invar_here = odds_invarD[OF assms(2)]

  have in_odd_same_weight: "\<lbrakk>X \<in> \<OO>; e \<subseteq> X; e \<in> G\<rbrakk> \<Longrightarrow> \<w> \<pi>' e = \<w> \<pi> e" for e X
  proof(goal_cases)
    case 1
    note one = this
    have pc1:"\<exists>u v. e = {u, v} \<and> u \<noteq> v"
      using "1"(3) by fastforce
    then obtain u v where pc2: "e = {u, v}" "u \<noteq> v"
      by auto
    show ?case 
    proof(cases rule: edmonds_primal_dual_cases[OF pc1, of "{Blos}" _ "{}", simplified])
      case (1 XX u v)
      hence "sum \<pi>' (end_sets G e) = sum \<pi> (end_sets G e)"
        using more_blos_props(2) one(3)  finite_Vs
        by(intro edmonds_primal_dual_adjustment_result(1)[of "{Blos}" "{}", simplified, of \<pi>' \<pi> \<epsilon> G _ _ _ XX,
              OF _ _ pc2 _ _ _ _ pc2])
          (auto intro!: odd_invar_omega[OF assms(2)] simp add: \<pi>'_def)
      then show ?thesis 
        by(auto  simp add: \<w>_def)
    next
      case (2 u v)
      hence "sum \<pi>' (end_sets G e) = sum \<pi> (end_sets G e)"
        using more_blos_props(2) one(3)  finite_Vs
        by(intro edmonds_primal_dual_adjustment_result(6)[of "{Blos}" "{}", simplified, of \<pi>' \<pi> \<epsilon> G e u v u v])
          (auto intro!: odd_invar_omega[OF assms(2)] simp add: \<pi>'_def)
      then show ?thesis 
        by(auto simp add: \<w>_def)
    next
      case (3 u v)
      hence "X \<inter> Blos \<noteq> {}" 
        using one by auto
      hence "Blos \<subseteq> X \<or> X \<subseteq> Blos" 
        using more_blos_props(2) odds_invar_here(1) one(1) by(auto elim!: laminarE)
      hence "Blos \<subset> X"
        using "3"(2,3) one(2) by auto
      hence False 
        using Blos_in_maxes in_maximal_setsE maxes_def one(1) by auto
      then show ?thesis
        by simp
    qed
  qed

  show ?th2
    unfolding top_loop_call1_def
  proof(rule odd_factor_critical_invarI, goal_cases)
    case (1 X Y)
    note one = this
    obtain M where M: "graph_matching ( odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk> \<sslash> immediate_subsets \<OO> X) M"
      "Vs M = immediate_subsets \<OO> X - {Y}"
      using  odd_factor_critical_invarD[OF assms(3) 1] by auto
    have "odd_tight_subgraph G w \<pi>' \<lbrakk>X\<rbrakk> = odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk>"
    proof(rule graph_inter_cong, goal_cases)
      case (1 e)
      then show ?case
      proof(cases "e \<subseteq> X", goal_cases)
        case 1
        show ?case
          using  in_odd_same_weight[OF one(1) 1]
          by(auto simp add:  odd_tight_subgraph_def \<w>_def)
      qed auto
    qed
    then show ?case
      using M by auto
  qed

  have Delta_nempty: "Delta G Blos \<noteq> {}"
    using assms(1) by(auto simp add: top_loop_call1_cond_def Blos_def maxes_def Let_def Gt_def)

  have epsilon_props: "1 < card Blos \<Longrightarrow> \<epsilon> \<le> \<pi> Blos" (is "?as1 \<Longrightarrow> ?t1")
    "\<And> e. e \<in> Delta G Blos \<Longrightarrow> \<epsilon> \<le> \<w> \<pi> e" (is "\<And> e. ?as2 e \<Longrightarrow> ?th2 e")
    "\<epsilon> \<ge> 0" (is ?t3)
  proof-

    have finite_min: "finite ((if 1 < card Blos then {\<pi> Blos} else {}) \<union> {\<w> \<pi> e |e. e \<in> Delta G Blos})"
      by (auto simp add: Delta_finite finite_E)

    show "\<epsilon> \<le> \<pi> Blos" if "1 < card Blos"
      using that finite_min unfolding \<epsilon>_def
      by(intro linorder_class.Min.coboundedI) auto

    show "?th2 e" if "?as2 e" for e
      using that finite_min unfolding \<epsilon>_def
      by(intro linorder_class.Min.coboundedI) auto

    show ?t3
      unfolding \<epsilon>_def
    proof(rule linorder_class.Min.boundedI[OF finite_min], goal_cases)
      case 1
      then show ?case
        using Delta_nempty by auto
    next
      case 2
      then show ?case 
        using  assms(4) more_blos_props(2) invar_feasible_piD[OF assms(6)]
        by (auto intro!: feasible_min_perfect_dual_edmondsD(1)
            simp add: if_split \<w>_def 
            dest: invar_strict_odd_posD in_DeltaD(2))
    qed
  qed

  show ?th3
    unfolding top_loop_call1_def
  proof(rule invar_strict_odd_posI, goal_cases)
    case (1 X)
    then show ?case 
    proof(cases "X = Blos")
      case True
      then show ?thesis
        using  "1"(1,2) assms(4) epsilon_props(3) 
        by(auto simp add: \<pi>'_def dest: invar_strict_odd_posD)
    next
      case False
      then show ?thesis 
        using "1"(1,2) assms(4)
        by(auto simp add: \<pi>'_def dest: invar_strict_odd_posD)
    qed
  qed

  show ?th4
    unfolding top_loop_call1_def
    using assms(5)  more_blos_props(2)
    by(auto intro!: invar_non_zero_pi_in_oddI 
        elim!: invar_non_zero_pi_in_oddE 
        simp add: \<pi>'_def if_split[of "\<lambda> x. x \<noteq> 0"])

  show ?th5
    unfolding top_loop_call1_def
  proof(rule invar_feasible_piI,
      rule edmonds_primal_dual_adjustment_feasibility[of G w \<pi> "{Blos}" "{}", simplified, of \<pi>' \<epsilon>],
      goal_cases)
    case 1
    then show ?case 
      using assms(6) by(auto dest: invar_feasible_piD)
  next
    case 2
    then show ?case 
      by(auto simp add: \<pi>'_def)
  next
    case 3
    then show ?case 
      using assms(2) more_blos_props(2) 
      by(auto intro!: odd_invar_omega)
  next
    case 4
    then show ?case 
      by (simp add: graph)
  next
    case 5
    then show ?case 
      by (simp add: epsilon_props(3))
  next
    case (6 u v X)
    then show ?case 
      by(auto intro!: epsilon_props(2)[of "{u, v}", simplified \<w>_def] simp add: in_DeltaI)
  qed
qed

lemma top_loop_ret_None_1_dual_unbounded:
  assumes "top_loop_ret_None_1_cond \<pi> \<OO>" "odds_invar (\<pi>, \<OO>)" "invar_feasible_pi (\<pi>, \<OO>)"
  shows "\<exists> \<pi>'. feasible_min_perfect_dual_edmonds G w \<pi>' \<and> sum \<pi>' (\<Omega> Vs G) > B"
proof-

  define Gt where "Gt = odd_tight_subgraph G w \<pi>"
  define maxes where "maxes = maximal_sets \<OO>"
  define Blos where "Blos = sel (\<lambda>Blos. \<nexists>e. e \<in> Gt \<and> e \<in> Delta G Blos) maxes"
  define \<epsilon> where "\<epsilon> = \<bar>B\<bar> + 1 + \<bar> sum \<pi> (\<Omega> Vs G) \<bar>"
  define \<pi>' where "\<pi>' = (\<lambda>X. if X = Blos then \<pi> Blos + \<epsilon> else \<pi> X)"

  have Blos_in_maxes: "Blos \<in> maxes"
    using assms(1,2) finite_Vs union_split_with_maximal_sets[of \<OO>] finite_UnionD[of "maximal_sets \<OO>"]
      finite_UnionD[of \<OO>] odds_invarD(4)[of \<pi> \<OO>]
    unfolding Blos_def
    by(intro sel_correct(1))
      (auto simp add:  top_loop_ret_None_1_cond_def Gt_def maxes_def Let_def)

  have  Blos_props:"\<nexists>e. e \<in> Delta G Blos" 
    using assms(1,2) finite_Vs union_split_with_maximal_sets[of \<OO>] finite_UnionD[of "maximal_sets \<OO>"]
      finite_UnionD[of \<OO>] odds_invarD(4)[of \<pi> \<OO>]
    unfolding Blos_def
    by(intro sel_correct(2))
      (auto simp add:  top_loop_ret_None_1_cond_def Gt_def maxes_def Let_def)

  have more_blos_props: "Blos \<in> maximal_sets \<OO>" "Blos \<in> \<OO>"
    using Blos_in_maxes maxes_def in_maximal_setsE by auto

  have epsilon_gtr_0: "\<epsilon> > 0"
    by (auto simp add: \<epsilon>_def)

  have "feasible_min_perfect_dual_edmonds G w \<pi>'"
  proof(rule edmonds_primal_dual_adjustment_feasibility[of G w \<pi> "{Blos}" "{}", simplified, of \<pi>' \<epsilon>],
      goal_cases)
    case 1
    then show ?case 
      using assms(3) by(auto dest: invar_feasible_piD)
  next
    case 2
    then show ?case 
      by(auto simp add: \<pi>'_def)
  next
    case 3
    then show ?case 
      using assms(2) more_blos_props(2) 
      by(auto intro!: odd_invar_omega)
  next
    case 4
    then show ?case 
      by (simp add: graph)
  next
    case 5
    then show ?case 
      using epsilon_gtr_0 by auto
  next
    case (6 u v X)
    text \<open>impossible case\<close>
    hence "{u, v} \<in> Delta G Blos"
      by (simp add: in_DeltaI)
    hence False
      using Blos_props by auto
    then show ?case 
      by simp
  qed

  moreover have "B < sum \<pi>' (\<Omega> Vs G)"
  proof-
    have "sum \<pi>' (\<Omega> Vs G) =  \<pi>' Blos + sum \<pi>' ((\<Omega> Vs G) - {Blos})"
      using assms(2) more_blos_props(2)
      by (auto intro: arg_cong[where f = "sum \<pi>'"] odd_invar_omega
          simp add: finite_Vs odd_subsets_finite comm_monoid_add_class.sum.insert_remove[symmetric])
    moreover have " \<pi>' Blos  > \<pi> Blos + B + \<bar> sum \<pi> (\<Omega> Vs G) \<bar>"
      by(auto simp add: \<pi>'_def \<epsilon>_def)
    moreover have "sum \<pi>' ((\<Omega> Vs G) - {Blos}) = sum \<pi> ((\<Omega> Vs G) - {Blos})"
      by(auto intro!: comm_monoid_add_class.sum.cong[OF refl] simp add: \<pi>'_def)
    moreover have "sum \<pi> (\<Omega> Vs G) =  \<pi> Blos + sum \<pi> ((\<Omega> Vs G) - {Blos})"
      using assms(2) more_blos_props(2)
      by (auto intro: arg_cong[where f = "sum \<pi>"] odd_invar_omega
          simp add: finite_Vs odd_subsets_finite comm_monoid_add_class.sum.insert_remove[symmetric])
    ultimately show ?thesis
      by auto
  qed
  ultimately show ?thesis
    by auto
qed

lemma two_Unions_disjoint:
  "(\<And> X Y. \<lbrakk>X \<in> \<X>; Y \<in> \<Y>\<rbrakk> \<Longrightarrow> X \<inter> Y = {}) \<Longrightarrow> \<Union> \<X> \<inter> \<Union> \<Y> = {}"
  by auto

lemma union_with_Union_disjoint:
  "(\<And> X. X \<in> \<X> \<Longrightarrow> X \<inter> Y = {}) \<Longrightarrow> \<Union> \<X> \<inter> Y = {}"
  "(\<And> Y. Y \<in> \<Y> \<Longrightarrow> X \<inter> Y = {}) \<Longrightarrow> X \<inter> \<Union> \<Y> = {}"
  by auto

lemma top_loop_ret_None_2_dual_unbounded:
  assumes "top_loop_ret_None_2_cond \<pi> \<OO>"
    "odds_invar (\<pi>, \<OO>)"
    "invar_feasible_pi (\<pi>, \<OO>)"
  shows "\<exists> \<pi>'. feasible_min_perfect_dual_edmonds G w \<pi>' \<and> sum \<pi>' (\<Omega> Vs G) > B"
proof-

  define Gt where "Gt = odd_tight_subgraph G w \<pi>"
  define maxes where "maxes = maximal_sets \<OO>"

  obtain D where D_def: "find_matching_or_decomposition (Gt \<sslash> maxes) = decomp D"
    using assms(1) by(auto simp add: top_loop_ret_None_2_cond_def Gt_def maxes_def Let_def)

  have graph_invar_tight: "graph_invar Gt"
    by (simp add: Gt_def graph graph_invar_odd_tight_subgraph)

  have maxes_have_crossings:
    "\<And> Blos. Blos \<in> maxes \<Longrightarrow> \<exists> e. e \<in> Gt \<and> e \<in> Delta G Blos"
    and unbounded:"\<And> X. X \<in> D \<Longrightarrow> Neighbourhood G (\<Union> X) \<subseteq> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D))"
    "\<And> X. X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<Longrightarrow> 1 \<ge> card X"
    using assms(1) D_def by(auto simp add: top_loop_ret_None_2_cond_def Gt_def maxes_def Let_def)

  note odds_invar_hereD = odds_invarD[OF assms(2)]

  have part:"partition_on (Vs G) maxes"
    using maximal_sets_in_laminar_family_are_global_partition[OF odds_invar_hereD(1)]
    by (simp add: finite_Vs odds_invar_hereD(4) maxes_def)

  have graph_invar_quot: "graph_invar (Gt \<sslash> maxes)"
    using part finite_Vs
    by(auto intro!: partition_quotient_graph_graph_invar[of "Vs G"])

  note D_props = find_matching_or_decomposition_correct(4-)[OF graph_invar_quot D_def]

  hence card_neighb_D_leq_card_D: "card (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)) \<le> card D"
    by auto

  have D_nempty:"D \<noteq> {}"
  proof(rule ccontr, goal_cases)
    case 1
    hence "card D = 0"
      by auto
    then show ?case
      using D_props(4) by auto
  qed

  define \<epsilon> where "\<epsilon> = \<bar>B\<bar> + 1 + \<bar> sum \<pi> (\<Omega> Vs G) \<bar>"
  define \<pi>' where "\<pi>' = (\<lambda> X. if \<exists> XX. XX \<in> D \<and> \<Union> XX = X then \<pi> X + \<epsilon> 
                                    else if X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) then \<pi> X - \<epsilon>
                                    else \<pi> X)"

  have maxes_disjoint: "\<lbrakk>X \<in> maxes; Y \<in> maxes; X\<noteq> Y\<rbrakk> \<Longrightarrow> X \<inter> Y = {}" for X Y
    using disjointD part partition_on_def by blast
  have maxes_eq: "\<lbrakk>X \<in> maxes; Y \<in> maxes; X \<inter> Y \<noteq> {}\<rbrakk> \<Longrightarrow> X = Y" for X Y
    using disjointD part partition_on_def by blast

  have Ds_are_partition: "X \<in> D \<Longrightarrow> partition_on (\<Union> X) X" for X
    using  order.trans[OF D_props(2) Vs_partition_quotient_graph [of Gt maxes]] part
    by(auto simp add: partition_on_def disjoint_def) blast+

  have D_in_maxes: "X \<in> D \<Longrightarrow> X \<subseteq> maxes" for X
    using D_props(2) Vs_partition_quotient_graph by blast
  have Vs_of_contracted_in_maxes: "X \<in> Vs (G \<sslash> maxes) \<Longrightarrow> X \<in> maxes" for X
    using Vs_partition_quotient_graph by blast
  have nbhd_in_maxes:"Neighbourhood (G \<sslash> maxes) X \<subseteq> maxes" for X
    using Neighbourhood_in_G Vs_partition_quotient_graph by fastforce
  have nbh_nothin_with_d: "Neighbourhood (G \<sslash> maxes) (\<Union> D) \<inter> (\<Union> D) = {}"
    using self_not_in_Neighbourhood[of _ "\<Union> D"] by auto

  have finiteD: "finite D" 
    using D_props(2) graph_invar_quot rev_finite_subset[of "Vs (Gt \<sslash> maxes)" "\<Union> D"] finite_UnionD[of D]
    by simp

  have nbhd_in_maxes_tight:"Neighbourhood (Gt \<sslash> maxes) X \<subseteq> maxes" for X
    using Neighbourhood_in_G Vs_partition_quotient_graph by fastforce
  have nbh_nothin_with_d_tight: "Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<inter> (\<Union> D) = {}"
    using self_not_in_Neighbourhood[of _ "\<Union> D"] by auto

  have inj_on_Union_D_pre:"\<lbrakk>D1 \<in> D; D2 \<in> D; \<Union> D1 = \<Union> D2; X \<in> D1\<rbrakk> \<Longrightarrow> X \<in> D2" for D1 D2 X
  proof(goal_cases)
    case 1
    then obtain x where x: "x \<in> X"
      using ex_in_conv[of X] Ds_are_partition[of D1] partition_onD3[of "\<Union> D1" D1] 
      by auto
    then obtain Y where Y: "Y \<in> D2" "x \<in> Y"
      using "1"(3,4) by auto
    have "X \<in> maxes"
      using "1"(1,4) D_in_maxes by blast
    moreover have "Y \<in> maxes"
      using "1"(2) D_in_maxes Y(1) by blast
    ultimately have "X = Y" 
      using x Y(2) maxes_disjoint[of Y X]
      by auto
    thus ?thesis
      by (simp add: Y(1))
  qed
  hence inj_on_Union_D_pre':"\<lbrakk>D1 \<in> D; D2 \<in> D; \<Union> D2 = \<Union> D1; X \<in> D1\<rbrakk> \<Longrightarrow> X \<in> D2" for D1 D2 X
    by blast

  have inj_union_D: "inj_on \<Union> D"
    by(auto simp add: inj_on_def dest: inj_on_Union_D_pre inj_on_Union_D_pre')

  have adjustment_pc1: "\<lbrakk>X \<in> {\<Union> X |X. X \<in> D} \<union> Neighbourhood (Gt \<sslash> maxes) (\<Union> D);
          Y \<in> {\<Union> X |X. X \<in> D} \<union> Neighbourhood (Gt \<sslash> maxes) (\<Union> D); X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<inter> Y = {}" for X Y
  proof(goal_cases)
    case 1
    then show ?case
    proof(elim UnE, goal_cases)
      case 1
      then obtain X' Y' where XY:"X' \<in> D" "X = \<Union> X'"  "Y' \<in> D" "Y = \<Union> Y'" by auto
      show ?case
        unfolding XY
        using D_in_maxes "1"(1) D_props(1) XY(1,2,3,4) 
        by (intro two_Unions_disjoint maxes_disjoint)(auto dest: disjointD)
    next
      case 2
      then obtain X' where X': "X' \<in> D" "X = \<Union> X'" by auto
      have Y: "Y \<in> maxes"
        using "2"(3) nbhd_in_maxes_tight by blast
      show ?case 
        unfolding X'
        using D_in_maxes X'(1)  "2"(3) nbh_nothin_with_d_tight 
        by (intro  union_with_Union_disjoint(1) maxes_disjoint[OF _ Y]) auto
    next
      case 3
      then obtain Y' where Y': "Y' \<in> D" "Y = \<Union> Y'" by auto
      have X: "X \<in> maxes"
        using "3"(2) nbhd_in_maxes_tight by blast
      show ?case 
        unfolding Y'
        using D_in_maxes Y'(1)  "3"(2) nbh_nothin_with_d_tight 
        by (intro  union_with_Union_disjoint(2) maxes_disjoint[OF X]) auto
    next
      case 4
      then show ?case
        using maxes_disjoint nbhd_in_maxes_tight by blast
    qed
  qed

  have adjustment_pc2: "{\<Union> X |X. X \<in> D} \<inter> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) = {}"
  proof(rule ccontr,  goal_cases)
    case 1
    then obtain X where X: "X \<in> {\<Union> X |X. X \<in> D} \<inter> Neighbourhood (Gt \<sslash> maxes) (\<Union> D)"
      by auto
    then obtain X' where X': "X' \<in> D" "X = \<Union> X'"
      by blast
    obtain XX where "XX \<in> X'" 
      using D_props(6) X'(1) by auto
    moreover hence "XX \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D)"
      using X'(1,2) X part inf.order_iff[of X' maxes] inf.order_iff[of XX X]
        nbhd_in_maxes_tight[of "\<Union> D"] D_in_maxes[of X'] maxes_disjoint[of XX X] Union_upper[of XX X']
      by (auto simp add: partition_on_def)
    ultimately show ?case 
      using X'(1) by(auto elim: in_NeighbourhoodE)
  qed

  have \<pi>'_def': "\<pi>' =
  (\<lambda>X. if \<exists>Xa. X = \<Union> Xa \<and> Xa \<in> D then \<pi> X + \<epsilon>
        else if X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) then \<pi> X - \<epsilon> else \<pi> X)"
    by(auto intro!: ext simp add: \<pi>'_def)

  have finite_maxes: "finite maxes"
    using finite_elements graph part by auto

  have odds_in_D:"X \<in> D \<Longrightarrow> odd (card X)" for X
  proof(goal_cases)
    case 1
    obtain x where x: "x \<in> X"
      using "1" D_props(6) by auto
    obtain M where M: "graph_matching ( Gt \<sslash> maxes \<lbrakk>X\<rbrakk>) M" "Vs M = X - {x}"
      using D_props(5)[OF 1 x] by auto
    hence "dblton_graph M"
      using graph_invar_quot dblton_graph_subset[of " Gt \<sslash> maxes \<lbrakk>X\<rbrakk>" M]
        graph_invar_graph_inter_Vs[of "Gt \<sslash> maxes" X] 
      by simp
    thus ?case
      using graph_invar_quot finite_maxes D_in_maxes[OF 1 ] M x
      by(intro near_perfect_matching_odd[of M X x]) (auto simp add: finite_subset)
  qed

  have odd_Union_in_D: "odd (card (\<Union> X'))"  if X': "X' \<in> D" for X'
  proof(rule odd_disjoint_Union, goal_cases)
    case 1
    then show ?case
      by (simp add: that odds_in_D)
  next
    case (2 XX)
    hence "XX \<in> maxes"
      using D_in_maxes that  by blast
    then show ?case
      using maximal_sets_subset odds_invar_hereD(2) 
      by (auto simp add: maxes_def)
  next
    case (3 X Y)
    then show ?case 
      using D_in_maxes that 
      by(intro maxes_disjoint) auto
  qed


  have adjustment_pc4: "{\<Union> X |X. X \<in> D} \<subseteq> \<Omega> Vs G \<and> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<subseteq> \<Omega> Vs G"
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 X)
    then obtain X' where X': "X = \<Union> X'"  "X' \<in> D"
      by auto
    show ?case 
      unfolding X'
    proof(rule in_odd_subsetsI, goal_cases)
      case 1
      then show ?case
        using X'(2) part D_in_maxes[of X'] partition_onD1[of "Vs G" maxes] Sup_subset_mono[of X' maxes]
        by simp
    next
      case 2
      then show ?case 
        using odd_Union_in_D X' by simp
    qed
  next
    case (2 X)
    hence "X \<in> maxes"
      using nbhd_in_maxes_tight by blast
    then show ?case 
      using odd_invar_omega assms(2)
      by(auto elim!: in_maximal_setsE simp add: maxes_def)
  qed

  note edmonds_primal_dual_adjustment_result_here = 
    edmonds_primal_dual_adjustment_result[of "{\<Union> X | X. X \<in> D}" "Neighbourhood (Gt \<sslash> maxes) (\<Union> D)" \<pi>' \<pi> \<epsilon>, 
      OF adjustment_pc1  adjustment_pc2, simplified, OF \<pi>'_def' adjustment_pc4 _ _ _ finite_Vs]

  note feasible_dual = invar_feasible_piD[OF assms(3)]

  have edges_between_Ds_not_tight:
    "\<lbrakk>u\<in> \<Union> X; X \<in> D; v\<in> \<Union> Y; Y \<in> D; {u, v} \<in> G; X \<noteq> Y\<rbrakk> \<Longrightarrow> sum \<pi> (end_sets G {u, v}) \<noteq> w {u, v}" for X Y u v
  proof(rule ccontr, goal_cases)
    case 1
    note one = this
    then obtain XX YY where XX_YY:"XX \<in> X" "u \<in> XX" "YY \<in> Y" "v \<in> YY"
      by auto
    have XX_neq_YY:"XX \<noteq> YY"
    proof(rule ccontr, goal_cases)
      case 1
      have "XX \<noteq> {}"
        using XX_YY by auto
      hence "X \<inter> Y \<noteq> {}"
        using "1" XX_YY by blast
      hence "X = Y"
        using D_props(1) disjointD one(2,4) by auto
      then show ?case 
        by (simp add: one(6))
    qed
    have "{XX, YY} \<in> (Gt \<sslash> maxes)"
      using "1"(2,4) D_in_maxes XX_YY one(5,7) XX_neq_YY
      by(auto  intro!: exI[of _ XX, OF exI[of _ YY]] bexI[of _ "{u, v}"]  in_odd_tight_subgraphI
          simp add: partition_quotient_graph_def Gt_def)
    thus False 
      using D_props(3) XX_YY(1,3) one(2,4,6) by blast
  qed

  have eps_gtr_0: "0 < \<epsilon>"
    by(simp add: \<epsilon>_def)
  hence eps_geq_0: "\<epsilon> \<ge> 0"
    by auto

(*all three epsilon cases hold because the assumptions are contradictory. The assumed edges don't exist.*)

  have eps_cond1:
    "\<epsilon> * 2 \<le> w {u, v} - sum \<pi> (end_sets G {u, v})"
    if asm: "{u, v} \<in> G" "u \<in> X" "\<exists>Xa. X = \<Union> Xa \<and> Xa \<in> D"
      "v \<in> Y" "\<exists>X. Y = \<Union> X \<and> X \<in> D" "X \<noteq> Y"
    for u v X Y 
  proof-
    have "X \<inter> Y = {}" 
    proof(rule ccontr, goal_cases)
      case 1
      then obtain X' Xa Y' Ya x where props:"X' \<in> Xa" "\<Union> Xa = X" "Xa \<in> D"
        "Y' \<in> Ya" "\<Union> Ya = Y" "Ya \<in> D" "x \<in> X'" "x \<in> Y'"
        using asm(3,5) by blast
      hence "Y' = X'" 
        using D_in_maxes D_props(1) that(3,5,6)
        by(intro maxes_eq) auto
      thus False
        using D_props(1) props(1,2,3,4,5,6) that(6)
        by(auto simp add: disjoint_def)
    qed
    hence "v \<in> Neighbourhood G X"
      using asm by(auto intro!:  in_NeighbourhoodI)
    hence "v \<in> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D))"
      using that(3) unbounded(1) by auto
    then obtain V U' where VU': "U' \<in> \<Union> D" "V \<notin> \<Union> D" "{U', V} \<in> (Gt \<sslash> maxes)" "v \<in> V"
      by(auto simp add: Neighbourhood_def)
    hence V_in_max:"V \<in> maxes"
      using Vs_partition_quotient_graph[of Gt maxes]
        edges_are_Vs_2[of U' V "Gt \<sslash> maxes"] 
      by auto
    obtain YY V' where YYV':"V' \<in> YY" "v \<in> V'" "Y = \<Union> YY" "YY \<in> D"
      using asm(4,5) by auto
    hence "V' \<in> maxes"
      using D_in_maxes by blast
    hence "V = V'" 
      using  VU'(4) V_in_max YYV'(2)
      by(intro maxes_eq) auto
    hence False
      using \<open>V \<notin> \<Union> D\<close> \<open>V' \<in> YY\<close> \<open>YY \<in> D\<close> by blast
    thus ?thesis
      by simp
  qed

  have eps_cond2:
    "\<epsilon> \<le> w {u, v} - sum \<pi> (end_sets G {u, v})"
    if asms: "{u, v} \<in> G" "u \<in> X" "\<exists>XD. X = \<Union> XD \<and> XD \<in> D" 
      "\<forall>Y. (\<forall>Xa. Y = \<Union> Xa \<longrightarrow> Xa \<notin> D) \<and> Y \<notin> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<or> v \<notin> Y" for u v X
  proof-
    have"v \<in> Neighbourhood G X"
      using  that(1,2,3,4)
      by (auto intro!: in_NeighbourhoodI)
    hence vN: "v \<in> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D))"
      using  that(3) unbounded(1) by auto
    then obtain V U' where VU': "U' \<in> \<Union> D" "V \<notin> \<Union> D" "{U', V} \<in> (Gt \<sslash> maxes)" "v \<in> V"
      by(auto simp add: Neighbourhood_def)
    hence False
      using that(4) vN by auto
    thus ?thesis
      by simp
  qed

  have eps_cond3: "\<lbrakk>Xa \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D); Suc 0 < card Xa\<rbrakk> \<Longrightarrow> \<epsilon> \<le> \<pi> Xa" for Xa
    using One_nat_def less_le_not_le[of "Suc 0" "card Xa"] unbounded(2)[of Xa] 
    by linarith

  note fsbl_after= edmonds_primal_dual_adjustment_feasibility[OF feasible_dual,
      of "{\<Union> X | X. X \<in> D}" "Neighbourhood (Gt \<sslash> maxes) (\<Union> D)" \<pi>' \<epsilon>,
      OF adjustment_pc1 adjustment_pc2, simplified, OF \<pi>'_def' adjustment_pc4 graph  eps_geq_0]

  have "feasible_min_perfect_dual_edmonds G w
   (\<lambda>X. if \<exists>Xa. X = \<Union> Xa \<and> Xa \<in> D then \<pi> X + \<epsilon>
         else if X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) then \<pi> X - \<epsilon> else \<pi> X)"
  proof(rule fsbl_after, goal_cases)
    case 1
    thus ?case
      by(rule eps_cond1)
  next
    case 2
    thus ?case
      by(rule eps_cond2)
  next
    case 3
    thus ?case
      by(rule eps_cond3)
  qed

  hence "feasible_min_perfect_dual_edmonds G w \<pi>'"
    by (simp add: \<pi>'_def')
      (*take dual change out as lemma*)
  moreover have "B < sum \<pi>' \<Omega> Vs G"
  proof-
    have rw1: "sum \<pi> \<Omega> Vs G = sum \<pi> (Union ` D) + sum \<pi> (\<Omega> Vs G - (Union ` D))" for \<pi>
    proof(subst comm_monoid_add_class.sum.union_disjoint[symmetric], goal_cases)
      case 4
      then show ?case
        using adjustment_pc4
        by(auto intro!:  arg_cong[of _ _ "sum _"])
    qed  (auto intro!: finite_imageI simp add: finiteD graph odd_subsets_finite)
    have rw2: "sum \<pi> (\<Omega> Vs G - (Union ` D)) =
            sum \<pi> (\<Omega> Vs G - (Union ` D) - Neighbourhood (Gt \<sslash> maxes) (\<Union> D)) +
            sum \<pi> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D))" for \<pi>
    proof(subst comm_monoid_add_class.sum.union_disjoint[symmetric], goal_cases)
      case 4
      then show ?case
        using adjustment_pc4 adjustment_pc2
        by(auto intro!:  arg_cong[of _ _ "sum _"])
    next
      case 2
      show ?case 
        using Neighbourhood_in_G finite_subset graph_invar_quot by fast
    qed  (auto intro!: finite_imageI simp add: finiteD graph odd_subsets_finite)
    have rw3:  "sum \<pi>' (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)) = 
                    sum \<pi> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D))
                       - \<epsilon> * card (Neighbourhood (Gt \<sslash> maxes) (\<Union> D))"
      unfolding \<pi>'_def
    proof(subst sum_if_not_P, goal_cases)
      case (1 x)
      then show ?case
        using adjustment_pc2 by blast
    next
      case 2
      then show ?case 
        by (simp add: sum_subtractf[of _ "\<lambda> x. \<epsilon>"])
    qed
    have rw4: "sum \<pi>' (Union ` D) = sum \<pi> (Union ` D) + \<epsilon> * card D"
      unfolding \<pi>'_def 
      by(subst sum_if_P)
        (auto simp add: sum_inj_on[OF  inj_union_D] card_image[OF  inj_union_D]
          comm_monoid_add_class.sum.distrib[where h = "\<lambda> x. \<epsilon>"])
    have rw5: "sum \<pi>' (\<Omega> Vs G - \<Union> ` D - Neighbourhood (Gt \<sslash> maxes) (\<Union> D)) =
                 sum \<pi> (\<Omega> Vs G - \<Union> ` D - Neighbourhood (Gt \<sslash> maxes) (\<Union> D))"
      unfolding \<pi>'_def 
      by(subst sum_if_not_P) auto

    have "sum \<pi>' \<Omega> Vs G = sum \<pi> \<Omega> Vs G +
                   \<epsilon> * ( card D - card (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)))"
      unfolding rw1 rw2 rw3 rw4 rw5
      by (auto simp add: real_of_minus_distrib[OF  card_neighb_D_leq_card_D]  algebra_simps)
    moreover have "... \<ge> sum \<pi> \<Omega> Vs G + \<epsilon>"
      using D_props(4) eps_gtr_0 by auto
    moreover have "sum \<pi> \<Omega> Vs G + \<epsilon> > B"
      by(auto simp add: \<epsilon>_def)
    ultimately show ?thesis 
      by simp
  qed
  ultimately show ?thesis
    by auto
qed

lemma card_gtr_1_two_elems:
  assumes "card X > Suc 0"
  shows "\<exists> a b. a \<in> X \<and> b \<in> X \<and> a \<noteq> b"
proof(cases "finite X")
  case True
  then show ?thesis 
    using True assms
  proof(induction X rule: finite_induct)
    case empty
    then show ?case
      by simp
  next
    case (insert x F)
    then show ?case 
    proof(induction F rule: finite_induct, goal_cases)
      case 1
      then show ?case
        by auto
    next
      case (2 x F)
      then show ?case
        by auto
    qed
  qed
next
  case False
  show ?thesis
  proof(rule ccontr, goal_cases)
    case 1
    hence "\<exists> x. X = {x} \<or> X = {}" 
      by blast
    then show ?case
      using False 
      by auto
  qed
qed

lemma UnE_second_strict:"\<lbrakk>x \<in> A \<union> B; x \<in> A \<Longrightarrow> P; x \<in> B - A \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto


lemma top_loop_call2_pres:
  assumes "top_loop_call2_cond \<pi> \<OO>"
    "odds_invar (\<pi>, \<OO>)"
    "odd_factor_critical_invar (\<pi>, \<OO>)"
    "invar_strict_odd_pos (\<pi>, \<OO>)"
    "invar_non_zero_pi_in_odd (\<pi>, \<OO>)"
    "invar_feasible_pi (\<pi>, \<OO>)"
  shows  "odds_invar (top_loop_call2 \<pi> \<OO>)" (is ?th1)
    "odd_factor_critical_invar (top_loop_call2 \<pi> \<OO>)" (is ?th2)
    "invar_strict_odd_pos (top_loop_call2 \<pi> \<OO>)" (is ?th3)
    "invar_non_zero_pi_in_odd (top_loop_call2 \<pi> \<OO>)" (is ?th4)
    "invar_feasible_pi (top_loop_call2 \<pi> \<OO>)" (is ?th5)
proof-

  define Gt where "Gt = odd_tight_subgraph G w \<pi>"
  define maxes where "maxes = maximal_sets \<OO>"

  obtain D where D_def: "find_matching_or_decomposition (Gt \<sslash> maxes) = decomp D"
    using assms(1) by(auto simp add: top_loop_call2_cond_def Gt_def maxes_def Let_def)

  have graph_invar_tight: "graph_invar Gt"
    by (simp add: Gt_def graph graph_invar_odd_tight_subgraph)

  have maxes_have_crossings:
    "\<And> Blos. Blos \<in> maxes \<Longrightarrow> \<exists> e. e \<in> Gt \<and> e \<in> Delta G Blos"
    and not_unbounded:"\<not> (\<forall> X \<in> D. Neighbourhood G (\<Union> X) \<subseteq> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)))
          \<or> (\<exists> X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D). 1 < card X)"
    using assms(1) D_def by(auto simp add: top_loop_call2_cond_def Gt_def maxes_def Let_def)

  note odds_invar_hereD = odds_invarD[OF assms(2)]

  have part:"partition_on (Vs G) maxes"
    using maximal_sets_in_laminar_family_are_global_partition[OF odds_invar_hereD(1)]
    by (simp add: finite_Vs odds_invar_hereD(4) maxes_def)

  have graph_invar_quot: "graph_invar (Gt \<sslash> maxes)"
    using part finite_Vs
    by(auto intro!: partition_quotient_graph_graph_invar[of "Vs G"])

  note D_props = find_matching_or_decomposition_correct(4-)[OF graph_invar_quot D_def]

  have D_nempty:"D \<noteq> {}"
  proof(rule ccontr, goal_cases)
    case 1
    hence "card D = 0"
      by auto
    then show ?case
      using D_props(4) by auto
  qed

  have finite_D: "finite D"
    using  graph_invar_quot
    by(auto intro!: finite_UnionD[OF finite_subset[OF D_props(2)]])

  have finite_in_D: "X \<in> D \<Longrightarrow> finite X" for X
    using graph_invar_quot
    by(auto intro: finite_subset[of _ "\<Union> D"]   finite_subset[OF D_props(2)])

  define \<epsilon> where "\<epsilon> = Min ({\<pi> X | X. X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<and> card X > 1}
                               \<union> {1/2 * \<w> \<pi> {u, v} | u v X Y. X \<in> D \<and> Y \<in> D \<and> X \<noteq> Y \<and> u \<in> \<Union> X \<and> v \<in> \<Union> Y\<and> {u, v} \<in> G}
                               \<union> {\<w> \<pi> {u, v} | u v. u \<in>(\<Union> (\<Union> D)) 
                                       \<and> v \<notin> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)) \<union> (\<Union> (\<Union> D)) 
                                       \<and> {u, v} \<in> G})"
  define \<pi>' where "\<pi>' = (\<lambda> X. if \<exists> XX. XX \<in> D \<and> \<Union> XX = X then \<pi> X + \<epsilon> 
                                    else if X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) then \<pi> X - \<epsilon>
                                    else \<pi> X)"
  define \<OO>' where "\<OO>' = \<OO> - {X | X. X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<and> \<pi> X = \<epsilon> \<and> card X > 1}
                               \<union> {\<Union> X | X. X \<in> D}"

  have top_loop_call2_def: "top_loop_call2 \<pi> \<OO> = (\<pi>', \<OO>')"
    using D_def
    by(auto intro!: ext simp add: top_loop_call2_def \<pi>'_def \<OO>'_def \<epsilon>_def Gt_def maxes_def Let_def)

  have maxes_disjoint: "\<lbrakk>X \<in> maxes; Y \<in> maxes; X\<noteq> Y\<rbrakk> \<Longrightarrow> X \<inter> Y = {}" for X Y
    using disjointD part partition_on_def by blast

  have Ds_are_partition: "X \<in> D \<Longrightarrow> partition_on (\<Union> X) X" for X
    using  order.trans[OF D_props(2) Vs_partition_quotient_graph [of Gt maxes]] part
    by(auto simp add: partition_on_def disjoint_def) blast+
  have D_in_maxes: "X \<in> D \<Longrightarrow> X \<subseteq> maxes" for X
    using D_props(2) Vs_partition_quotient_graph by blast
  have Vs_of_contracted_in_maxes: "X \<in> Vs (G \<sslash> maxes) \<Longrightarrow> X \<in> maxes" for X
    using Vs_partition_quotient_graph by blast
  have nbhd_in_maxes:"Neighbourhood (G \<sslash> maxes) X \<subseteq> maxes" for X
    using Neighbourhood_in_G Vs_partition_quotient_graph by fastforce
  have nbh_nothin_with_d: "Neighbourhood (G \<sslash> maxes) (\<Union> D) \<inter> (\<Union> D) = {}"
    using self_not_in_Neighbourhood[of _ "\<Union> D"] by auto

  have nbhd_in_maxes_tight:"Neighbourhood (Gt \<sslash> maxes) X \<subseteq> maxes" for X
    using Neighbourhood_in_G Vs_partition_quotient_graph by fastforce
  have nbh_nothin_with_d_tight: "Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<inter> (\<Union> D) = {}"
    using self_not_in_Neighbourhood[of _ "\<Union> D"] by auto

  have adjustment_pc1: "\<lbrakk>X \<in> {\<Union> X |X. X \<in> D} \<union> Neighbourhood (Gt \<sslash> maxes) (\<Union> D);
          Y \<in> {\<Union> X |X. X \<in> D} \<union> Neighbourhood (Gt \<sslash> maxes) (\<Union> D); X \<noteq> Y\<rbrakk> \<Longrightarrow> X \<inter> Y = {}" for X Y
  proof(goal_cases)
    case 1
    then show ?case
    proof(elim UnE, goal_cases)
      case 1
      then obtain X' Y' where XY:"X' \<in> D" "X = \<Union> X'"  "Y' \<in> D" "Y = \<Union> Y'" by auto
      show ?case
        unfolding XY
        using D_in_maxes "1"(1) D_props(1) XY(1,2,3,4) 
        by (intro two_Unions_disjoint maxes_disjoint)(auto dest: disjointD)
    next
      case 2
      then obtain X' where X': "X' \<in> D" "X = \<Union> X'" by auto
      have Y: "Y \<in> maxes"
        using "2"(3) nbhd_in_maxes_tight by blast
      show ?case 
        unfolding X'
        using D_in_maxes X'(1)  "2"(3) nbh_nothin_with_d_tight 
        by (intro  union_with_Union_disjoint(1) maxes_disjoint[OF _ Y]) auto
    next
      case 3
      then obtain Y' where Y': "Y' \<in> D" "Y = \<Union> Y'" by auto
      have X: "X \<in> maxes"
        using "3"(2) nbhd_in_maxes_tight by blast
      show ?case 
        unfolding Y'
        using D_in_maxes Y'(1)  "3"(2) nbh_nothin_with_d_tight 
        by (intro  union_with_Union_disjoint(2) maxes_disjoint[OF X]) auto
    next
      case 4
      then show ?case
        using maxes_disjoint nbhd_in_maxes_tight by blast
    qed
  qed

  have adjustment_pc2: "{\<Union> X |X. X \<in> D} \<inter> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) = {}"
  proof(rule ccontr,  goal_cases)
    case 1
    then obtain X where X: "X \<in> {\<Union> X |X. X \<in> D} \<inter> Neighbourhood (Gt \<sslash> maxes) (\<Union> D)"
      by auto
    then obtain X' where X': "X' \<in> D" "X = \<Union> X'"
      by blast
    obtain XX where "XX \<in> X'" 
      using D_props(6) X'(1) by auto
    moreover hence "XX \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D)"
      using X'(1,2) X part inf.order_iff[of X' maxes] inf.order_iff[of XX X]
        nbhd_in_maxes_tight[of "\<Union> D"] D_in_maxes[of X'] maxes_disjoint[of XX X] Union_upper[of XX X']
      by (auto simp add: partition_on_def)
    ultimately show ?case 
      using X'(1) by(auto elim: in_NeighbourhoodE)
  qed

  have \<pi>'_def': "\<pi>' =
  (\<lambda>X. if \<exists>Xa. X = \<Union> Xa \<and> Xa \<in> D then \<pi> X + \<epsilon>
        else if X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) then \<pi> X - \<epsilon> else \<pi> X)"
    by(auto intro!: ext simp add: \<pi>'_def)

  have finite_maxes: "finite maxes"
    using finite_elements graph part by auto

  have odds_in_D:"X \<in> D \<Longrightarrow> odd (card X)" for X
  proof(goal_cases)
    case 1
    obtain x where x: "x \<in> X"
      using "1" D_props(6) by auto
    obtain M where M: "graph_matching ( Gt \<sslash> maxes \<lbrakk>X\<rbrakk>) M" "Vs M = X - {x}"
      using D_props(5)[OF 1 x] by auto
    hence "dblton_graph M"
      using graph_invar_quot dblton_graph_subset[of " Gt \<sslash> maxes \<lbrakk>X\<rbrakk>" M]
        graph_invar_graph_inter_Vs[of "Gt \<sslash> maxes" X] 
      by simp
    thus ?case
      using graph_invar_quot finite_maxes D_in_maxes[OF 1 ] M x
      by(intro near_perfect_matching_odd[of M X x]) (auto simp add: finite_subset)
  qed

  have odd_Union_in_D: "odd (card (\<Union> X'))"  if X': "X' \<in> D" for X'
  proof(rule odd_disjoint_Union, goal_cases)
    case 1
    then show ?case
      by (simp add: that odds_in_D)
  next
    case (2 XX)
    hence "XX \<in> maxes"
      using D_in_maxes that  by blast
    then show ?case
      using maxes_def maximal_sets_subset odds_invar_hereD(2) by auto
  next
    case (3 X Y)
    then show ?case 
      using D_in_maxes that 
      by(intro maxes_disjoint) auto
  qed

  have adjustment_pc4: "{\<Union> X |X. X \<in> D} \<subseteq> \<Omega> Vs G \<and> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<subseteq> \<Omega> Vs G"
  proof(rule, all \<open>rule\<close>, goal_cases)
    case (1 X)
    then obtain X' where X': "X = \<Union> X'"  "X' \<in> D"
      by auto
    show ?case 
      unfolding X'
    proof(rule in_odd_subsetsI, goal_cases)
      case 1
      then show ?case
        using X'(2) part D_in_maxes[of X'] partition_onD1[of "Vs G" maxes]
        by auto
    next
      case 2
      then show ?case 
        using odd_Union_in_D X' by simp
    qed
  next
    case (2 X)
    hence "X \<in> maxes"
      using nbhd_in_maxes_tight by blast
    then show ?case 
      using odd_invar_omega assms(2)
      by (auto elim!: in_maximal_setsE simp add: maxes_def)
  qed

  note edmonds_primal_dual_adjustment_result_here = 
    edmonds_primal_dual_adjustment_result[of "{\<Union> X | X. X \<in> D}" "Neighbourhood (Gt \<sslash> maxes) (\<Union> D)" \<pi>' \<pi> \<epsilon>, 
      OF adjustment_pc1  adjustment_pc2, simplified, OF \<pi>'_def' adjustment_pc4 _ _ _ finite_Vs]

  note feasible_dual = invar_feasible_piD[OF assms(6)]

  let ?min_contributors = "{\<pi> X |X. X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<and> 1 < card X} \<union>
      { 1 / 2 * \<w> \<pi> {u, v} | u v X Y. X \<in> D \<and> Y \<in> D \<and> X \<noteq> Y \<and> u \<in> \<Union> X \<and> v \<in> \<Union> Y \<and> {u, v} \<in> G} \<union>
      {\<w> \<pi> {u, v} | u v. u \<in>(\<Union> (\<Union> D)) \<and> v \<notin> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)) \<union> (\<Union> (\<Union> D)) 
                                       \<and> {u, v} \<in> G}"

  let  "?min1 \<union> ?min2 \<union> ?min3" = ?min_contributors

  have finite_Min_contributors:
    "finite ?min_contributors"
  proof(rule finite_UnI, all \<open>(rule finite_UnI)?\<close>, goal_cases)
    case 1
    then show ?case 
      unfolding image_Collect[symmetric]
      using nbhd_in_maxes_tight 
      by(force intro: finite_subset[of _ maxes] simp add: finite_maxes)
  next
    case 2
    then show ?case
    proof(rule forw_subst[of _ "(\<lambda> e.  1 / 2 * \<w> \<pi> e) ` {{u, v}
                 | u v X Y. X \<in> D \<and> Y \<in> D \<and> X \<noteq> Y \<and> u \<in> \<Union> X \<and> v \<in> \<Union> Y \<and> {u, v} \<in> G}"], goal_cases)
      case 1
      then show ?case
        unfolding image_def by blast
    next
      case 2
      then show ?case 
        by(auto intro!: finite_imageI intro:  finite_subset[of _ G] simp add: finite_E)
    qed
  next
    case 3
    then show ?case 
    proof(rule forw_subst[of _ "\<w> \<pi> ` {{u, v} | u v. u \<in>(\<Union> (\<Union> D)) 
                                       \<and> v \<notin> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)) \<union> (\<Union> (\<Union> D)) 
                                       \<and> {u, v} \<in> G}"], goal_cases)
      case 1
      then show ?case
        by(auto intro!: image_eqI[of "\<w> \<pi> {u, v}" "\<w> \<pi>" "{v, u}" for u v] simp add: insert_commute)
    next
      case 2
      then show ?case 
        by(auto intro!: finite_imageI intro: finite_subset[of _ G] 
            dest: in_DeltaD(2) 
            simp add: finite_E)
    qed
  qed

  have edges_between_Ds_not_tight:
    "\<lbrakk>u\<in> \<Union> X; X \<in> D; v\<in> \<Union> Y; Y \<in> D; {u, v} \<in> G; X \<noteq> Y\<rbrakk> \<Longrightarrow> sum \<pi> (end_sets G {u, v}) \<noteq> w {u, v}" for X Y u v
  proof(rule ccontr, goal_cases)
    case 1
    note one = this
    then obtain XX YY where XX_YY:"XX \<in> X" "u \<in> XX" "YY \<in> Y" "v \<in> YY"
      by auto
    have XX_neq_YY:"XX \<noteq> YY"
    proof(rule ccontr, goal_cases)
      case 1
      have "XX \<noteq> {}"
        using XX_YY by auto
      hence "X \<inter> Y \<noteq> {}"
        using "1" XX_YY by blast
      hence "X = Y"
        using D_props(1) disjointD one(2,4) by auto
      then show ?case 
        by (simp add: one(6))
    qed
    have "{XX, YY} \<in> (Gt \<sslash> maxes)"
      using "1"(2,4) D_in_maxes XX_YY one(5,7) XX_neq_YY
      by(auto  intro!: exI[of _ XX, OF exI[of _ YY]] bexI[of _ "{u, v}"]  in_odd_tight_subgraphI
          simp add: partition_quotient_graph_def Gt_def)
    thus False 
      using D_props(3) XX_YY(1,3) one(2,4,6) by blast
  qed

  have min_contributors_nempty:
    "?min_contributors \<noteq> {}"
  proof(rule disjE[OF not_unbounded], goal_cases)
    case 1
    note not_unbounded = this
    obtain X v where X:"X \<in> D" and  v': "v \<in> Neighbourhood G (\<Union> X)" "v \<notin> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D))"
      using not_unbounded by blast
    obtain u where u: "u \<in> \<Union> X" "{u, v} \<in> G"
      using v'(1) by(auto elim!: in_NeighbourhoodE)
    show ?thesis
    proof(cases "\<exists> Y \<in> D. v \<in> \<Union> Y")
      case True
      hence "1 / 2 * \<w> \<pi> {u, v} \<in> ?min2"
        using X u(1,2) v'(1) by(auto intro!: exI[of _ u, OF exI[of _ v]] elim!: in_NeighbourhoodE)
      then show ?thesis
        by blast
    next
      case False
      hence "\<w> \<pi> {u, v} \<in> ?min3"
        using feasible_min_perfect_dual_edmondsD(1)[OF feasible_dual, of "{u, v}"] X u(1,2)  v'(2)
        by (auto intro!: exI[of _ "{u, v}"] exI[of _ u, OF exI[of _ v]] 
            feasible_min_perfect_dual_edmondsD(1)
            simp add: Delta_def \<w>_def) 
      thus ?thesis
        unfolding Un_empty de_Morgan_conj
        by (intro disjI2) auto
    qed
  qed auto

  have eps_gtr_0:"0 < \<epsilon>"
    unfolding \<epsilon>_def
  proof(subst linorder_class.Min_gr_iff[OF finite_Min_contributors min_contributors_nempty], 
      rule ballI, elim UnE, goal_cases)
    case (1 pi)
    then show ?case 
      using  nbhd_in_maxes_tight[of "\<Union> D"]
      by (auto elim: in_maximal_setsE[OF set_mp] 
          intro!: invar_strict_odd_posD[OF assms(4)]
          simp add: maxes_def)
  next
    case (2 pi)
    then obtain X Y u v XX YY where pi: "X \<in> D" "Y \<in> D" "X \<noteq> Y" "u \<in> \<Union> X" "v \<in> \<Union> Y" "{u, v} \<in> G"
      "pi = 1 / 2 * \<w> \<pi> {u, v}" "XX \<in> X" "u \<in> XX" "YY \<in> Y" "v \<in> YY"
      by blast
    moreover hence "\<w> \<pi> {u, v} \<ge> 0" 
      by (simp add: \<w>_def feasible_dual feasible_min_perfect_dual_edmondsD(1))
    moreover have "\<w> \<pi> {u, v} = 0 \<Longrightarrow> False"
    proof(goal_cases)
      case 1
      hence "{u, v} \<in> Gt"
        by (simp add: Gt_def \<w>_def in_odd_tight_subgraphI pi(6))
      hence "{XX, YY} \<in> Gt \<sslash> maxes" 
        using D_in_maxes pi(1,2,8,9,10,11) pi(3) D_props(1)
        by(force intro!: exI[of _ XX, OF exI[of _ YY]] bexI[of _ "{u, v}" ] 
            simp add: partition_quotient_graph_def disjoint_def)
      then show ?case 
        using D_props(3)[of X Y]
        using pi(1,10,2,3,8) by blast
    qed
    ultimately show ?case
      by auto
  next
    case (3 pi)
    then obtain u v U UU where pi: "pi = \<w> \<pi> {u, v}"
      "v \<notin> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)) \<union> \<Union> (\<Union> D)" "{u, v} \<in> G"
      "u \<in> U" "U \<in> UU" "UU \<in> D"
      by blast
    moreover hence "\<w> \<pi> {u, v} \<ge> 0" 
      by (simp add: \<w>_def feasible_dual feasible_min_perfect_dual_edmondsD(1))
    moreover have "\<w> \<pi> {u, v} = 0 \<Longrightarrow> False"
    proof(goal_cases)
      case 1
      hence "{u, v} \<in> Gt"
        by (simp add: Gt_def \<w>_def in_odd_tight_subgraphI pi(3))
      moreover obtain V where V:"V \<in> maxes" "v \<in> V" 
        using part pi(3)
        by(auto dest!: edges_are_Vs_2 simp add: partition_on_def)
      ultimately have "{U, V} \<in> Gt \<sslash> maxes" 
        using D_in_maxes pi(2,4,5,6)
        by(auto intro!: exI[of _ U, OF exI[of _ V]] bexI[of _ "{u, v}" ] 
            simp add: partition_quotient_graph_def)
      hence "V \<in> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)) \<or> V \<in> (\<Union> D)"
        using  pi(5,6) by(auto intro!: in_NeighbourhoodI)
      hence "v \<in> \<Union> (Neighbourhood (Gt \<sslash> maxes) (\<Union> D)) \<union> \<Union> (\<Union> D)"
        using  V by blast
      then show False
        using pi(2) by force
    qed
    ultimately show ?case 
      by argo
  qed

  hence  eps_geq_0:"0 \<le> \<epsilon>"
    by auto

  have Union_of_D_part_not_in_maxes:
    "\<lbrakk>X \<in> D; card X > 1\<rbrakk> \<Longrightarrow>  (\<Union> X) \<notin> maxes" for X
  proof(goal_cases)
    case 1
    then obtain A B where AB: "A \<in> X" "B \<in> X" "A \<noteq> B"
      using card_gtr_1_two_elems[of X]
      by auto
    hence "A \<in> maxes" "B \<in> maxes"
      using "1" D_in_maxes by auto
    thus ?case
      using AB
      by (auto elim!: in_maximal_setsE simp add: maxes_def)
  qed

  have pi_of_D_part_geq_0: "\<lbrakk>X \<in> D; card (\<Union> X) > 1\<rbrakk> \<Longrightarrow> \<pi> (\<Union> X) \<ge> 0" for X
  proof(goal_cases)
    case 1
    thus ?case
      using 1 odd_Union_in_D[OF 1(1)] D_in_maxes[OF 1(1)] D_props(6)[OF 1(1)]
      by(auto intro!: feasible_min_perfect_dual_edmondsD(2)[OF feasible_dual]
          in_odd_subsets_strictI
          intro: nat_geq_3I
          simp add:  partition_onD1[OF part])+
  qed

  have \<pi>'_of_those_in_D:"\<lbrakk>X \<in> D; card (\<Union> X) > 1\<rbrakk> \<Longrightarrow> \<pi>' (\<Union> X) > 0" for X
    using pi_of_D_part_geq_0[of X] eps_gtr_0
    by (auto simp add: \<pi>'_def)

  show ?th1
    unfolding top_loop_call2_def
  proof(rule odds_invarI, goal_cases)
    case 1
    then show ?case 
      unfolding \<OO>'_def
    proof(rule laminar_subset[of "Vs G" "\<OO> \<union> {\<Union> X |X. X \<in> D}"], goal_cases)
      case 1
      have "laminar (Vs G) ({\<Union> X |X. X \<in> D} \<union> \<OO>)"
      proof(rule  laminar_extension_with_set_of_maximal_sets[OF odds_invar_hereD(1)], goal_cases)
        case 1
        then show ?case
          using D_in_maxes maxes_def by blast
      next
        case (2 X Xa)
        then show ?case 
          using D_props(1) disjointD by blast
      next
        case (3 X)
        then show ?case 
          by (simp add: D_props(6))
      qed
      then show ?case 
        unfolding Un_commute[of \<OO>]
        by simp
    qed auto
  next
    case 2
    then show ?case
      unfolding \<OO>'_def
    proof(rule ballI, goal_cases)
      case (1 Bls)
      hence "Bls \<in> \<OO> \<union> {\<Union> X |X. X \<in> D}"
        by auto
      then show ?case
      proof(elim UnE, goal_cases)
        case 1
        then show ?case 
          by (simp add: odds_invar_hereD(2))
      next
        case 2
        then show ?case 
          using odd_Union_in_D by auto
      qed
    qed
  next
    case 3
    then show ?case 
      unfolding \<OO>'_def
    proof(rule composed_family_contract_more_sets, goal_cases)
      case 2
      then show ?case 
        using  D_in_maxes
        by (auto elim!: in_NeighbourhoodE  in_maximal_setsE simp add: maxes_def)
    next
      case 1
      then show ?case 
      proof(rule composed_family_expand_some_maximals, goal_cases)
        case 1
        then show ?case 
          by (simp add: odds_invar_hereD(3))
      next
        case 2
        then show ?case
          using  nbhd_in_maxes_tight by(auto simp add: maxes_def)
      qed
    qed
  next
    case 4
    have helper:"\<exists>X\<in>\<OO> - {uu \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D). \<pi> uu = \<epsilon> \<and> Suc 0 < card uu}. x \<in> X" 
      if asm: "x \<in> \<Union> \<OO>"  "\<And> xa. (\<forall>X. xa = \<Union> X \<longrightarrow> X \<notin> D) \<or> x \<notin> xa" for x
    proof-
      obtain X where X: "X \<in> maxes" "x \<in> X"
        using asm(1) odds_invar_hereD(4) part
        by(auto simp add: partition_on_def)
      then show ?thesis
      proof(cases "\<epsilon> = \<pi> X")
        case True
        note true = this
        then show ?thesis
        proof(cases "Suc 0 < card X")
          case True
          have "\<exists>\<Y>\<subseteq>\<OO> - {X}. \<Union> \<Y> = X"
            using X(1,2) True 
            by(intro composed_familyD[OF odds_invar_hereD(3), of X])
              (auto elim: in_maximal_setsE simp add: maxes_def)
          then obtain \<Y> where Ycal:"\<Y>\<subseteq>\<OO> - {X}" "\<Union> \<Y> = X"
            by auto
          then obtain Y where Y: "Y \<in> \<Y>" "x \<in> Y" "Y \<noteq> X"
            using X(2) by blast
          hence "Y \<subset> X" 
            using Ycal by blast
          then show ?thesis 
            using Y(1,2) X(1) Ycal(1)   nbhd_in_maxes_tight[of "\<Union> D"]
            by (auto intro: bexI[of _ Y] 
                elim!: in_maximal_setsE in_maximal_setsE[of Y \<OO>, OF set_mp] 
                simp add:  maxes_def)
        next
          case False
          then show ?thesis
            using X(1,2) in_maximal_setsE maxes_def by auto
        qed
      next
        case False
        then show ?thesis
          using X
          by(auto intro!: bexI[of _ X] elim: in_maximal_setsE simp add: maxes_def)
      qed
    qed
    then show ?case
      using odds_invar_hereD(4)
      by (auto intro!: helper 
          elim!: in_maximal_setsE[of _ \<OO>, OF set_mp, OF D_in_maxes[simplified maxes_def]]
          simp add: \<OO>'_def)
  qed

  have eps_cond_1:"\<epsilon> * 2 \<le> w {u, v} - sum \<pi> (end_sets G {u, v})"
    if asm: "{u, v} \<in> G" "u \<in> X" "\<exists>Xa. X = \<Union> Xa \<and> Xa \<in> D"
      "v \<in> Y" "\<exists>X. Y = \<Union> X \<and> X \<in> D" "X \<noteq> Y" for u v X Y
  proof-
    have "\<epsilon>  \<le> 1/2 * (w {u, v} - sum \<pi> (end_sets G {u, v}))"
      unfolding \<epsilon>_def
    proof(rule linorder_class.Min.coboundedI[OF finite_Min_contributors], goal_cases)
      case 1
      then show ?case
      proof(rule UnI1, rule UnI2, goal_cases)
        case 1
        then show ?case 
          using asm by (auto intro!: exI[of _ u, OF exI[of _ v]] simp add: \<w>_def)
      qed
    qed
    thus ?thesis
      by auto
  qed

  have eps_cond_2:
    "\<epsilon> \<le> w {u, v} - sum \<pi> (end_sets G {u, v})"
    if asm: "{u, v} \<in> G" "u \<in> X" "\<exists>Xa. X = \<Union> Xa \<and> Xa \<in> D"
      "\<forall>Y. (\<forall>X. Y = \<Union> X \<longrightarrow> X \<notin> D) \<and> Y \<notin> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<or> v \<notin> Y" for u v X
    unfolding \<epsilon>_def
  proof(rule linorder_class.Min.coboundedI[OF finite_Min_contributors], goal_cases)
    case 1
    then show ?case
    proof(rule UnI2, goal_cases)
      case 1
      then show ?case 
        using asm
        by (auto intro!: exI[of _ u, OF exI[of _ v]] simp add: \<w>_def)
    qed
  qed

  have eps_cond_3: "\<epsilon> \<le> \<pi> X" if asm: "X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D)" "Suc 0 < card X"for X
    unfolding \<epsilon>_def
  proof(rule linorder_class.Min.coboundedI[OF finite_Min_contributors], goal_cases)
    case 1
    then show ?case
    proof(rule UnI1, goal_cases)
      case 1
      then show ?case 
        using asm
        by (auto simp add: \<w>_def)
    qed
  qed      

  note feasible_after = edmonds_primal_dual_adjustment_feasibility[OF feasible_dual,
      of "{\<Union> X | X. X \<in> D}" "Neighbourhood (Gt \<sslash> maxes) (\<Union> D)" \<pi>' \<epsilon>,
      OF adjustment_pc1 adjustment_pc2, simplified, OF \<pi>'_def' adjustment_pc4 graph eps_geq_0]

  have "feasible_min_perfect_dual_edmonds G w
   (\<lambda>X. if \<exists>Xa. X = \<Union> Xa \<and> Xa \<in> D then \<pi> X + \<epsilon>
         else if X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) then \<pi> X - \<epsilon> else \<pi> X)"
    by(intro feasible_after eps_cond_1 eps_cond_2 eps_cond_3) auto

  hence "feasible_min_perfect_dual_edmonds G w \<pi>'"
    by (simp add: \<pi>'_def')
  thus ?th5
    unfolding top_loop_call2_def
    by(rule invar_feasible_piI)

  note in_D_maximalE= in_maximal_setsE[OF set_mp, OF D_in_maxes[simplified maxes_def]]

  show ?th2
    unfolding top_loop_call2_def
  proof(rule odd_factor_critical_invarI, goal_cases)
    case (1 X Y)
    then show ?case
      unfolding \<OO>'_def
    proof(elim UnE_second_strict, goal_cases)
      case 1
      note one = this
      have immediate_subsets_same:"immediate_subsets
          (\<OO> - {X |X. X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<and> \<pi> X = \<epsilon> \<and> 1 < card X} \<union> {\<Union> X |X. X \<in> D}) X =
          immediate_subsets \<OO> X"
      proof(subst immediate_subsets_same_add_more, goal_cases)
        case (1 X')
        have helper:
          "\<exists>xa\<in>Xa. x \<in> xa"
          if asm: "X \<in> \<OO>" "Xa \<in> D" "X' = \<Union> Xa" "\<Union> Xa \<subseteq> X" "x \<in> X" for Xa x
        proof-
          obtain xa where "xa\<in>Xa"
            using D_props(6) asm(2) by fastforce
          thus ?thesis
            using  that(1,2,4,5)
            by(auto intro!: bexI[of _ xa] elim: in_D_maximalE[OF asm(2)])
        qed
        show ?case 
          using 1  one(1,3) by(auto intro: helper)
      next
        case 2
        thus ?case
          using  one(3)
          by (intro immediate_subsets_remove)
            (auto elim: in_maximal_setsE 
              dest!: set_mp[OF nbhd_in_maxes_tight, simplified maxes_def] 
              simp add: maxes_def)
      qed

      obtain M where M: "graph_matching (odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk> \<sslash> immediate_subsets \<OO> X) M"
        "Vs M = immediate_subsets \<OO> X - {Y}" 
        using odd_factor_critical_invarD[OF assms(3), of X] one(1,2,3)
        by(unfold immediate_subsets_same) force

      have "e \<in> odd_tight_subgraph G w \<pi>' \<lbrakk>X\<rbrakk> \<sslash> immediate_subsets \<OO> X"
        if asm: "e \<in> M" for e
      proof-
        have "e \<in> odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk> \<sslash> immediate_subsets \<OO> X"
          using asm M(1) by auto
        then obtain U V ee where UVee:"U \<in> immediate_subsets \<OO> X"
          "V \<in> immediate_subsets \<OO> X" "U \<noteq> V" "ee\<in> odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk>"
          "U \<inter> ee \<noteq> {}" "V \<inter> ee \<noteq> {}" "e = {U, V}"
          by(auto simp add: partition_quotient_graph_def)
        obtain u v where uv: "ee = {u, v}" "u \<noteq> v" 
          using Gt_def UVee(4) graph_invar_tight by(auto simp add: graph_inter_Vs_def)
        hence case_rule_pc: "\<exists>u v. ee = {u, v} \<and> u \<noteq> v" by auto
        have uv_in_X: "u \<in> X" "v \<in> X" 
          using uv UVee(3,4,5,6) immediate_subsets_subset(2)[OF UVee(1)]
            immediate_subsets_subset(2)[OF UVee(2)]
            immediate_subsets_laminar_disjoint[OF odds_invar_hereD(1) UVee(1,2)]
          by auto


        have "sum \<pi>' (end_sets G ee) = sum \<pi> (end_sets G ee)"
        proof(cases rule: edmonds_primal_dual_cases[OF case_rule_pc, 
              of "{\<Union> X |X. X \<in> D}" _ "Neighbourhood (Gt \<sslash> maxes) (\<Union> D)"], goal_cases)
          case (1 X u v)
          then show ?case 
            using UVee(4) 
            by(intro edmonds_primal_dual_adjustment_result(1)[OF adjustment_pc1 adjustment_pc2, simplified, OF \<pi>'_def',
                  OF adjustment_pc4 uv _ _ _ _ uv, where X = X])
              (auto simp add: odd_tight_subgraph_def graph_inter_Vs_def finite_Vs)
        next
          case (2 X u v)
          then show ?case 
            using UVee(4) 
            by(intro edmonds_primal_dual_adjustment_result(2)[OF adjustment_pc1 adjustment_pc2, simplified, OF \<pi>'_def',
                  OF adjustment_pc4 uv _ _ _ _ uv, where X = X])
              (auto simp add: odd_tight_subgraph_def graph_inter_Vs_def finite_Vs)
        next
          case (3 u v X Y)
          then show ?case
            using UVee(4)
            by(intro edmonds_primal_dual_adjustment_result(3)[OF adjustment_pc1 adjustment_pc2,
                  simplified, OF \<pi>'_def', OF adjustment_pc4 3(6,7) _ _ _ _ _ _ _ 3(6,7), where X = X and Y = Y])
              (auto simp add: odd_tight_subgraph_def graph_inter_Vs_def finite_Vs)
        next
          case (4 u v X Y)
            (*impossible case*)
          then obtain XX YY where "X = \<Union> XX" "XX \<in> D" "Y = \<Union> YY" "YY \<in> D"
            by auto
          hence False
            using  UVee(4) "4"(2,4,5,6) edges_between_Ds_not_tight[of u XX v YY]
            by(auto elim!: in_odd_tight_subgraphE simp add: graph_inter_Vs_def)+
          then show ?case
            by simp
        next
          case (5 u v Xa Ya)
            (*impossible case*)
          hence in_max: "Xa \<in> maxes" "Ya \<in> maxes"
            using nbhd_in_maxes_tight by blast+
          have "Xa \<supseteq> X"
            using 5(2,4-) uv_in_X uv one(3) in_max(1)
            by(intro laminar_inter_maximal_set[OF odds_invar_hereD(1)])
              (auto simp add: maxes_def doubleton_eq_iff)
          moreover have "Ya \<supseteq> X"
            using 5(2,4-) uv_in_X uv one(3) in_max(2)
            by(intro laminar_inter_maximal_set[OF odds_invar_hereD(1)])
              (auto simp add: maxes_def doubleton_eq_iff)
          ultimately have "Ya = Xa" 
            using  maxes_disjoint[OF in_max(1,2)]  uv_in_X(1)
            by auto
          hence False
            using 5 by simp
          thus ?case
            by simp
        next
          case (6 u v)
          then show ?case 
            using UVee(4) 
            by(intro edmonds_primal_dual_adjustment_result(6)[OF adjustment_pc1 adjustment_pc2,
                  simplified, OF \<pi>'_def', OF adjustment_pc4, OF 6(3,4)])
              (auto simp add: odd_tight_subgraph_def graph_inter_Vs_def finite_Vs)
        next
          case (7 u v X')
            (*impossible case*)
          then obtain XX Xa where XX_Xa: "XX \<in> D" "Xa \<in> XX" "u \<in> Xa"
            by auto
          hence "Xa \<in> maxes"
            using D_in_maxes by blast
          hence "Xa \<supseteq> X" 
            using "7"(4)  XX_Xa(3) one(3) uv(1) uv_in_X(1,2)
            by(intro laminar_inter_maximal_set[OF odds_invar_hereD(1)] )
              (auto simp add: doubleton_eq_iff maxes_def)
          hence "u \<in> X'" "v \<in> X'"
            using uv(1) uv_in_X XX_Xa  "7"(3)
            by (auto simp add: "7"(2,4) doubleton_eq_iff)
          hence False
            using "7"(1,3) by blast
          thus ?case
            by auto
        next
          case (8 u v Y')
            (*impossible case*)
          hence "Y' \<in> maxes"
            using nbhd_in_maxes_tight by blast
          hence "Y' \<supseteq> X" 
            using "8"(3,4) one(3) uv(1) uv_in_X(1,2)
            by(intro laminar_inter_maximal_set[OF odds_invar_hereD(1)])
              (auto simp add:  maxes_def doubleton_eq_iff)
          hence "u \<in> Y'"
            using "8"(4) uv(1) uv_in_X(1,2) by fastforce
          hence False
            using "8"(1,2) by blast
          then show ?case 
            by simp
        qed
        hence "ee \<in>  odd_tight_subgraph G w \<pi>' \<lbrakk>X\<rbrakk>"
          using UVee(4)
          by(auto simp add: graph_inter_Vs_def odd_tight_subgraph_def)
        thus ?thesis
          using UVee(1-3,5-)
          by(auto simp add: partition_quotient_graph_def)
      qed
      thus ?case 
        using 1 M 
        by(unfold immediate_subsets_same) auto
    next
      case 2
      then obtain XD where XD: "XD \<in> D" "X = \<Union> XD"
        by auto
      have X_not_singleton: "X \<in> XD \<Longrightarrow> False"
      proof(goal_cases)
        case 1
        hence "X \<in> \<OO>"
          using XD(1) in_D_maximalE by auto
        moreover have "\<not> (X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<and> \<pi> X = \<epsilon> \<and> 1 < card X)"
          using 1 XD(1) by(auto elim!: in_NeighbourhoodE)
        ultimately show ?case
          using "2"(3) by fastforce
      qed
      hence XD_composed: "XD \<noteq> {X}"
        by auto

      have immediate_subsets_D:
        "immediate_subsets
          (\<OO> - {X |X. X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<and> \<pi> X = \<epsilon> \<and> 1 < card X} \<union> {\<Union> X |X. X \<in> D}) X
           = immediate_subsets {Y | Y. Y \<in> \<OO> \<and> Y \<subseteq> X} X" 
      proof-
        have rw1: "\<OO> - {X |X. X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<and> \<pi> X = \<epsilon> \<and> 1 < card X} \<union> {\<Union> X |X. X \<in> D} = 
             {Z | Z. Z \<in> \<OO> \<and> Z \<inter> \<Union> (\<Union> D) = {}} 
             - {X |X. X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D) \<and> \<pi> X = \<epsilon> \<and> 1 < card X} \<union>
             ({\<Union> X |X. X \<in> D} \<union>  {Z | Z. Z \<in> \<OO> \<and> Z \<inter> \<Union> (\<Union> D) \<noteq> {}})"
        proof-
          have "\<lbrakk>x \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D); xa \<in> x; xa \<in> X; X \<in> Xa; Xa \<in> D\<rbrakk> \<Longrightarrow> False"
            for x xa X Xa
          proof(goal_cases)
            case 1
            have "x \<in> maxes"
              using "1"(1) nbhd_in_maxes_tight by blast
            moreover have "X \<in> maxes"
              using "1"(5,4) D_in_maxes by auto
            moreover have "X \<noteq> x"
              using "1"(1,5,4) by(auto elim!: in_NeighbourhoodE)
            ultimately show ?case 
              using "1"(3,2) by(auto dest: maxes_disjoint)
          qed
          thus ?thesis
            by (auto dest: set_mp[OF nbhd_in_maxes_tight[of "\<Union> D"]])+
        qed
        show ?thesis
          unfolding rw1
        proof(subst immediate_subsets_same_add_more', goal_cases)
          case (1 X')
          hence "X' \<in> \<OO>"
            by auto
          then obtain x where x: "x \<in> X'"
            using empty_nin_laminar[OF odds_invar_hereD(1)] by force
          have False if asm: "X' \<inter> \<Union> (\<Union> D) = {}" "X' \<subseteq> X"
          proof-
            have "x \<in> X"
              using that(2) x by fastforce
            hence "x \<in> \<Union> (\<Union> D)"
              using XD(1,2) by auto
            thus False
              using asm(1) x
              by auto
          qed
          thus ?case 
            using 1 by auto
        next
          case 2
          have rw2:"{Z |Z. Z \<in> \<OO> \<and> Z \<inter> \<Union> (\<Union> D) \<noteq> {}} = {Z |Z. Z \<in> \<OO> \<and> Z \<subseteq> \<Union> (\<Union> D)}"
          proof-
            have helper:"\<lbrakk>x \<in> \<OO>; xa \<in> x; xa \<in> X; X \<in> Xa; Xa \<in> D; xb \<in> x\<rbrakk> \<Longrightarrow> \<exists>y\<in>D. \<exists>x\<in>y. xb \<in> x"
              for x xa X Xa xb
            proof(goal_cases)
              case 1
              moreover hence XO: "X \<in> \<OO>"
                using in_D_maximalE by blast
              moreover hence "xb \<in> X"
                using 1 XO odds_invar_hereD(1)
                by(elim laminarE)(rule in_D_maximalE[OF 1(5,4)], fastforce)
              ultimately show ?case 
                by(auto intro!: bexI[of _ Xa] bexI[of _ X])
            qed
            show ?thesis
              using odds_invar_hereD(1)
              by(auto intro: helper)(force elim!: laminarE in_D_maximalE) 
          qed
          have rw3:"{\<Union> X |X. X \<in> D} \<union> {Z |Z. Z \<in> \<OO> \<and> Z  \<subseteq> \<Union> (\<Union> D)} = 
             {\<Union> X |X. X \<in> D} \<union> {Z |Z. Z \<in> \<OO> \<and> Z \<subseteq> \<Union> (\<Union> D) \<and> {Z} \<notin> D}"
            by auto
          show ?case
            unfolding rw2
            unfolding rw3 
          proof(rule immediate_subsets_remove_lowers_2, goal_cases)
            case (1 Y)
            thus ?case
            proof(elim UnE, goal_cases)
              case 1
              moreover hence "Y \<inter> X = {}"
                using XD(1,2)
                by(intro adjustment_pc1[OF UnI1 UnI1]) auto
              moreover have "Y \<noteq> {}" 
                using  "1"(3)  D_props(6) Ds_are_partition 
                by (force simp add: partition_on_def)
              ultimately have False
                by auto
              thus ?case
                by simp
            next
              case 2
              thus ?case
                by blast
            qed
          next
            case 2
            thus ?case 
              using XD(1,2) by auto blast
          qed
        qed
      qed

      have maximal_sets_helper: "maximal_sets {Y |Y. Y \<in> {XX | XX. XX \<subset> X \<and> XX \<in> \<OO> \<and> XX \<subseteq> X} \<and> Y \<subset> X} \<subseteq> XD"
      proof(rule, goal_cases)
        case (1 Y)
        hence Y: "Y \<subset> X" "Y \<in> \<OO>" "Y \<subseteq> X" "Y \<subset> X"
          by(auto simp add: maximal_sets_def)
        obtain X' where X': "X' \<in> XD" "X' \<inter> Y \<noteq> {}"
          using XD(2) Y(2,3) empty_nin_laminar[OF odds_invar_hereD(1)]
            inf_commute[of Y] union_with_Union_disjoint(2)[of XD Y] Int_absorb1[of Y X]
          by auto
        hence X': "X' \<in> XD" "X' \<supseteq> Y" 
          using  odds_invar_hereD(1) laminar_inter_maximal_set[OF odds_invar_hereD(1)]
            D_props(2) XD(1,2) Y(2,3) Vs_partition_quotient_graph[of Gt maxes]
          by(auto elim!: laminarE simp add:  maxes_def)blast
        have "X' \<in> {Y |Y. Y \<in> {XX |XX. XX \<subset> X \<and> XX \<in> \<OO> \<and> XX \<subseteq> X} \<and> Y \<subset> X}"
          using  X'(1) XD(1,2) X_not_singleton
          by(auto elim: in_D_maximalE)
        hence "X' \<supset> Y \<Longrightarrow> ?case"
          using 1 by(auto elim!: in_maximal_setsE)
        moreover have "X' = Y \<Longrightarrow> ?case" 
          using \<open>X' \<in> XD\<close> by fastforce
        ultimately show ?case 
          using X'(2) by auto
      qed


      have immediate_subsets_XD: "immediate_subsets {Y | Y. Y \<in> \<OO> \<and> Y \<subseteq> X} X = XD"
      proof(subst immediate_subsets_restrict_to_set, rule, goal_cases)
        case 1
        thus ?case
          using maximal_sets_helper
          by(auto simp add: immediate_subsets_are_maximals)
      next
        case 2
        thus ?case
          using XD(2,1)  X_not_singleton 
          by (auto elim: in_D_maximalE simp add: immediate_subsets_def)
      qed

      have Y_in_XD: "Y \<in> XD"
        using "2"(2) immediate_subsets_D immediate_subsets_XD by blast

      have commute_pcs: "XD \<subseteq> maxes" "dblton_graph (odd_tight_subgraph G w \<pi>)"
        "disjoint maxes"
        using D_in_maxes XD(1) graph_invar_tight
        by (auto simp add: Gt_def disjoint_def maxes_disjoint)

      obtain M where M: "graph_matching ( odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk> \<sslash> XD) M" "Vs M = XD - {Y}"
        using D_props(5)[OF XD(1) Y_in_XD] XD(2) unfolding Gt_def
          partition_quotient_graph_inter_Vs_commute[OF commute_pcs]
        by auto

      moreover have "e \<in> odd_tight_subgraph G w \<pi>' \<lbrakk>X\<rbrakk> \<sslash> XD" if asm: "e \<in> M" for e
      proof-
        have "e \<in> odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk> \<sslash> XD"
          using asm M(1) by auto
        then obtain U V ee where UVee:"U \<in> XD"
          "V \<in> XD" "U \<noteq> V" "ee\<in> odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk>"
          "U \<inter> ee \<noteq> {}" "V \<inter> ee \<noteq> {}" "e = {U, V}"
          by(auto simp add: partition_quotient_graph_def)
        obtain u v where uv: "ee = {u, v}" "u \<noteq> v" 
          using Gt_def UVee(4) graph_invar_tight by(auto simp add: graph_inter_Vs_def)
        hence case_rule_pc: "\<exists>u v. ee = {u, v} \<and> u \<noteq> v" by auto
        have uv_in_X: "u \<in> X" "v \<in> X" 
          using UVee(1,2,3,5,6)commute_pcs(1) XD(2) uv(1) 
          by(auto dest: maxes_disjoint)

        have "sum \<pi>' (end_sets G ee) = sum \<pi> (end_sets G ee)"
          using UVee(4) XD(1,2)
          by(intro edmonds_primal_dual_adjustment_result(1)[OF adjustment_pc1 adjustment_pc2, simplified, OF \<pi>'_def',
                OF adjustment_pc4 uv _ _ _ _ uv, where X = X])
            (auto simp add: odd_tight_subgraph_def graph_inter_Vs_def finite_Vs)
        hence "ee \<in>  odd_tight_subgraph G w \<pi>' \<lbrakk>X\<rbrakk>"
          using UVee(4)
          by(auto simp add: graph_inter_Vs_def odd_tight_subgraph_def)
        thus ?thesis
          using UVee(1-3,5-)
          by(auto simp add: partition_quotient_graph_def)
      qed
      ultimately show ?case
        unfolding immediate_subsets_D immediate_subsets_XD
        by auto
    qed
  qed


  show ?th3
    unfolding top_loop_call2_def \<OO>'_def
  proof(rule invar_strict_odd_posI, elim UnE, goal_cases)
    case (1 Bls)
    note one = this
    show ?case
    proof(cases "\<exists>XX. XX \<in> D \<and> \<Union> XX = Bls")
      case True
      then show ?thesis 
        using 1(1)
        by(auto intro!: \<pi>'_of_those_in_D)
    next
      case False
      show ?thesis 
        unfolding \<pi>'_def if_not_P[OF False]
      proof(cases "Bls \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D)", goal_cases)
        case 1
        hence "\<pi> Bls \<noteq> \<epsilon>"
          using one by auto
        moreover have "\<pi> Bls \<ge> \<epsilon>"
          using "1" one(1) by(auto intro!: eps_cond_3)
        ultimately show ?case 
          using 1 by auto
      next
        case 2
        thus ?case
          using one(1,2) assms(4)
          by(auto intro!: invar_strict_odd_posD)
      qed
    qed
  next
    case (2 Bls)
    then obtain X where X: "X \<in> D" "Bls = \<Union> X"
      by auto
    then show ?case 
      using adjustment_pc2  \<pi>'_of_those_in_D[of X] "2"(1)
      by(auto dest:  simp add: \<pi>'_def if_split)
  qed

  show ?th4
    unfolding top_loop_call2_def
  proof(rule invar_non_zero_pi_in_oddI, goal_cases)
    case (1 X)
    then show ?case
      unfolding \<pi>'_def
    proof(cases "\<exists>XX. XX \<in> D \<and> \<Union> XX = X", goal_cases)
      case 1
      then show ?case 
        by(auto simp add: \<OO>'_def)
    next
      case 2
      show ?case
        using 2(1) unfolding if_not_P[OF 2(2)]
      proof(cases "X \<in> Neighbourhood (Gt \<sslash> maxes) (\<Union> D)", goal_cases)
        case 1
        then show ?case
          using nbhd_in_maxes_tight[of "\<Union> D"]  maximal_sets_subset
          by(auto simp add: \<OO>'_def maxes_def)
      next
        case 2
        thus ?case
          using assms(5)
          by(auto elim:  invar_non_zero_pi_in_oddE simp add: \<OO>'_def)
      qed
    qed
  qed
qed

subsection \<open>Properties upon Termination\<close>

definition "odds_invar_cleanup = (\<lambda> (\<pi>, M, \<OO>).
laminar (Vs G) \<OO> \<and> (\<forall> Bls \<in> \<OO>. odd (card Bls)) \<and> composed_family \<OO> \<and> \<Union>\<OO> = Vs G \<and>
  laminar (Vs G) ({U | U. U \<in> (\<Omega>\<^sub>\<ge>\<^sub>3 Vs G) \<and> \<pi> U > 0} \<union> \<OO>))"

lemma odds_invar_cleanupI: 
  "\<lbrakk>laminar (Vs G) \<OO>; \<forall>Bls \<in> \<OO>. odd (card Bls); composed_family \<OO>; \<Union>\<OO> = Vs G;
 laminar (Vs G) ({U | U. U \<in> (\<Omega>\<^sub>\<ge>\<^sub>3 Vs G) \<and> \<pi> U > 0} \<union> \<OO>)\<rbrakk> \<Longrightarrow> odds_invar_cleanup (\<pi>,M, \<OO>)"
  and odds_invar_cleanupE: 
  "\<lbrakk>odds_invar_cleanup (\<pi>, M, \<OO>); 
      \<lbrakk>laminar (Vs G) \<OO>; \<forall>Bls \<in> \<OO>. odd (card Bls); composed_family \<OO>; \<Union>\<OO> = Vs G;
       laminar (Vs G) ({U | U. U \<in> (\<Omega>\<^sub>\<ge>\<^sub>3 Vs G) \<and> \<pi> U > 0} \<union> \<OO>)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and odds_invar_cleanupD: 
  "odds_invar_cleanup (\<pi>, M, \<OO>) \<Longrightarrow> laminar (Vs G) \<OO>"
  "\<lbrakk>odds_invar_cleanup (\<pi>, M, \<OO>); Bls \<in> \<OO>\<rbrakk> \<Longrightarrow> odd (card Bls)"
  "odds_invar_cleanup (\<pi>, M, \<OO>) \<Longrightarrow> composed_family \<OO>"
  "odds_invar_cleanup (\<pi>, M, \<OO>) \<Longrightarrow> \<Union>\<OO> = Vs G"
  "odds_invar_cleanup (\<pi>, M, \<OO>) \<Longrightarrow> laminar (Vs G) ({U | U. U \<in> (\<Omega>\<^sub>\<ge>\<^sub>3 Vs G) \<and> \<pi> U > 0} \<union> \<OO>)"
  unfolding odds_invar_cleanup_def by auto

definition "odd_factor_critical_invar_cleanup = (\<lambda> (\<pi>, M, \<OO>).
      (\<forall> X \<in> \<OO>. card X > 1 \<longrightarrow>
        (\<forall> Y \<in> immediate_subsets \<OO> X.
            (\<exists> M. graph_matching (odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk>\<sslash>(immediate_subsets \<OO> X)) M \<and>
                   Vs M = immediate_subsets \<OO> X - {Y}))))"

lemma odd_factor_critical_invar_cleanupI: 
  "(\<And>X Y. \<lbrakk>X \<in> \<OO>; card X > 1; Y \<in> immediate_subsets \<OO> X\<rbrakk> \<Longrightarrow> 
      \<exists>M. graph_matching (odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk>\<sslash>(immediate_subsets \<OO> X)) M
     \<and> Vs M = immediate_subsets \<OO> X - {Y}) 
    \<Longrightarrow> odd_factor_critical_invar_cleanup (\<pi>, M, \<OO>)"
  and odd_factor_critical_invar_cleanupE: 
  "\<lbrakk>odd_factor_critical_invar_cleanup (\<pi>, M, \<OO>); 
      (\<And> X Y. \<lbrakk>X \<in> \<OO>; card X > 1; Y \<in> immediate_subsets \<OO> X\<rbrakk> \<Longrightarrow> 
        \<exists>M. graph_matching (odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk>\<sslash>(immediate_subsets \<OO> X)) M
             \<and> Vs M = immediate_subsets \<OO> X - {Y}) \<Longrightarrow> P\<rbrakk> 
    \<Longrightarrow> P"
  and odd_factor_critical_invar_cleanupD:
  "\<lbrakk>odd_factor_critical_invar_cleanup (\<pi>, M, \<OO>); X \<in> \<OO>; card X > 1; Y \<in> immediate_subsets \<OO> X\<rbrakk> \<Longrightarrow> 
      \<exists>M. graph_matching (odd_tight_subgraph G w \<pi> \<lbrakk>X\<rbrakk>\<sslash>(immediate_subsets \<OO> X)) M \<and> Vs M = immediate_subsets \<OO> X - {Y}"
  unfolding odd_factor_critical_invar_cleanup_def by auto

definition "invar_matching_delta_of_non_zero_sets_cleanup =
           (\<lambda> (\<pi>, M, \<OO>).  \<forall> Bls \<in> (\<Omega>\<^sub>\<ge>\<^sub>3 Vs G) - \<OO>. \<pi> Bls \<noteq> 0 \<longrightarrow> 
                    card {{U, V} | U V. {U, V} \<in> M \<and> U \<subseteq> Bls \<and> \<not> V \<subseteq> Bls} = 1)"

lemma invar_matching_delta_of_non_zero_sets_cleanupI:
  "(\<And>Bls. \<lbrakk>Bls \<in> \<Omega>\<^sub>\<ge>\<^sub>3 Vs G - \<OO>; \<pi> Bls \<noteq> 0\<rbrakk>
       \<Longrightarrow> card {{U, V} | U V. {U, V} \<in> M \<and> U \<subseteq> Bls \<and> \<not> V \<subseteq> Bls} = 1) 
     \<Longrightarrow> invar_matching_delta_of_non_zero_sets_cleanup (\<pi>, M, \<OO>)"
  and invar_matching_delta_of_non_zero_sets_cleanupE:
  "\<lbrakk> invar_matching_delta_of_non_zero_sets_cleanup (\<pi>, M, \<OO>);
           (\<And>Bls. \<lbrakk> Bls \<in> \<Omega>\<^sub>\<ge>\<^sub>3 Vs G - \<OO>; \<pi> Bls \<noteq> 0 \<rbrakk>
            \<Longrightarrow> card {{U, V} | U V. {U, V} \<in> M \<and> U \<subseteq> Bls \<and> \<not> V \<subseteq> Bls} = 1) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  and invar_matching_delta_of_non_zero_sets_cleanupD:
  "\<lbrakk>invar_matching_delta_of_non_zero_sets_cleanup (\<pi>, M, \<OO>); Bls \<in> \<Omega>\<^sub>\<ge>\<^sub>3 Vs G - \<OO>; \<pi> Bls \<noteq> 0\<rbrakk>
       \<Longrightarrow> card {{U, V} | U V. {U, V} \<in> M \<and> U \<subseteq> Bls \<and> \<not> V \<subseteq> Bls} = 1"
  unfolding invar_matching_delta_of_non_zero_sets_cleanup_def by auto

definition "invar_strict_odd_pos_cleanup = (\<lambda> (\<pi>, M, \<OO>).
        \<forall> Bls \<in> \<OO>. card Bls > 1 \<longrightarrow> \<pi> Bls > 0)"

lemma 
  invar_strict_odd_pos_cleanupI: 
  "(\<And>Bls. \<lbrakk>Bls \<in> \<OO>; card Bls > 1\<rbrakk> \<Longrightarrow> \<pi> Bls > 0) \<Longrightarrow> invar_strict_odd_pos_cleanup (\<pi>,M, \<OO>)"
  and invar_strict_odd_pos_cleanupE: 
  "\<lbrakk>invar_strict_odd_pos_cleanup (\<pi>,M, \<OO>); (\<And> Bls. \<lbrakk>Bls \<in> \<OO>; card Bls > 1\<rbrakk> \<Longrightarrow> \<pi> Bls > 0) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and invar_strict_odd_pos_cleanupD: 
  "\<lbrakk>invar_strict_odd_pos_cleanup (\<pi>,M, \<OO>); Bls \<in> \<OO>; card Bls > 1\<rbrakk> \<Longrightarrow> \<pi> Bls > 0"
  unfolding invar_strict_odd_pos_cleanup_def by auto

definition "invar_feasible_pi_cleanup = (\<lambda> (\<pi>, M, \<OO>). feasible_min_perfect_dual_edmonds G w \<pi>)"

lemma 
  invar_feasible_pi_cleanupI: 
  "feasible_min_perfect_dual_edmonds G w \<pi> \<Longrightarrow> invar_feasible_pi_cleanup (\<pi>,M, \<OO>)"
  and invar_feasible_pi_cleanupE: 
  "\<lbrakk>invar_feasible_pi_cleanup (\<pi>,M, \<OO>); feasible_min_perfect_dual_edmonds G w \<pi> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  and invar_feasible_pi_cleanupD: 
  "invar_feasible_pi_cleanup (\<pi>,M, \<OO>) \<Longrightarrow> feasible_min_perfect_dual_edmonds G w \<pi>"
  unfolding invar_feasible_pi_cleanup_def by auto

definition "invar_tight_matching_cleanup =
            (\<lambda> (\<pi>, M, \<OO>). perfect_matching (odd_tight_subgraph G w \<pi> \<sslash> maximal_sets \<OO>) M \<and>
                          Vs M = maximal_sets \<OO>)"

lemma invar_tight_matching_cleanupI:
  "\<lbrakk> perfect_matching (odd_tight_subgraph G w \<pi> \<sslash> maximal_sets \<OO>) M; Vs M = maximal_sets \<OO> \<rbrakk> 
    \<Longrightarrow> invar_tight_matching_cleanup (\<pi>, M, \<OO>)"
  and invar_tight_matching_cleanupE:
  "\<lbrakk> invar_tight_matching_cleanup (\<pi>, M, \<OO>); 
        \<lbrakk> perfect_matching (odd_tight_subgraph G w \<pi> \<sslash> maximal_sets \<OO>) M; Vs M = maximal_sets \<OO> \<rbrakk> \<Longrightarrow> P \<rbrakk> 
      \<Longrightarrow> P"
  and invar_tight_matching_cleanupD:
  "invar_tight_matching_cleanup (\<pi>, M, \<OO>)
     \<Longrightarrow> perfect_matching (odd_tight_subgraph G w \<pi> \<sslash> maximal_sets \<OO>) M"
  "invar_tight_matching_cleanup (\<pi>, M, \<OO>) \<Longrightarrow> Vs M = maximal_sets \<OO>"
  unfolding invar_tight_matching_cleanup_def by auto

lemma odd_invar_omega_cleanup:
  assumes "odds_invar_cleanup (\<pi>, M, \<OO>)" "X \<in> \<OO>"
  shows "X \<in> \<Omega> (Vs G)"
  using assms
  by (auto intro!: in_odd_subsetsI elim!: odds_invar_cleanupE)

lemma top_loop_return_Some:
  assumes "top_loop_ret_Some_cond \<pi> \<OO>"
    "odds_invar (\<pi>, \<OO>)"
    "odd_factor_critical_invar (\<pi>, \<OO>)"
    "invar_strict_odd_pos (\<pi>, \<OO>)"
    "invar_non_zero_pi_in_odd (\<pi>, \<OO>)"
    "invar_feasible_pi (\<pi>, \<OO>)"
  shows  "odds_invar_cleanup (to_loop_ret_Some \<pi> \<OO>)" (is ?th1)
    "odd_factor_critical_invar_cleanup (to_loop_ret_Some \<pi> \<OO>)" (is ?th2)
    "invar_matching_delta_of_non_zero_sets_cleanup (to_loop_ret_Some \<pi> \<OO>)" (is ?th3)
    "invar_strict_odd_pos_cleanup (to_loop_ret_Some \<pi> \<OO>)" (is ?th4)
    "invar_feasible_pi_cleanup (to_loop_ret_Some \<pi> \<OO>)" (is ?th5)
    "invar_tight_matching_cleanup (to_loop_ret_Some \<pi> \<OO>)" (is ?th6)
proof-
  define Gt where "Gt = odd_tight_subgraph G w \<pi>"
  define maxes where "maxes = maximal_sets \<OO>"

  obtain M where M_def: "find_matching_or_decomposition (Gt \<sslash> maxes) = match M"
    using assms(1) by(auto simp add: top_loop_ret_Some_cond_def Gt_def maxes_def Let_def)

  have graph_invar_tight: "graph_invar Gt"
    by (simp add: Gt_def graph graph_invar_odd_tight_subgraph)

  have maxes_have_crossings:
    "\<And> Blos. Blos \<in> maxes \<Longrightarrow> \<exists> e. e \<in> Gt \<and> e \<in> Delta G Blos"
    using assms(1) by(auto simp add: top_loop_ret_Some_cond_def Gt_def maxes_def Let_def)

  note odds_invar_hereD = odds_invarD[OF assms(2)]

  have part:"partition_on (Vs G) maxes"
    using maximal_sets_in_laminar_family_are_global_partition[OF odds_invar_hereD(1)]
    by (simp add: finite_Vs odds_invar_hereD(4) maxes_def)

  have graph_invar_quot: "graph_invar (Gt \<sslash> maxes)"
    using part finite_Vs
    by(auto intro!: partition_quotient_graph_graph_invar[of "Vs G"])

  note M_perfect = find_matching_or_decomposition_correct(3)[OF graph_invar_quot M_def]

  have to_loop_ret_Some_def: "to_loop_ret_Some \<pi> \<OO> = (\<pi>, M, \<OO>)"
    using M_def by(auto simp add: to_loop_ret_Some_def Gt_def maxes_def)

  have helper:"{U | U. U \<in> (\<Omega>\<^sub>\<ge>\<^sub>3 Vs G) \<and> \<pi> U > 0} \<subseteq> \<OO>"
    using assms(5)
    by(auto elim!: invar_non_zero_pi_in_oddE)

  show ?th1
    using assms(2) helper
    by(auto elim!: odds_invarE 
        intro!: odds_invar_cleanupI 
        simp add: to_loop_ret_Some_def laminar_subset)


  show ?th3
    unfolding to_loop_ret_Some_def
  proof(rule invar_matching_delta_of_non_zero_sets_cleanupI, goal_cases)
    case (1 Bls)
      (*yet, there is no such Bls*)
    hence False 
      using assms(5) invar_non_zero_pi_in_oddE by auto
    then show ?case 
      by auto
  qed

  show ?th2
    unfolding to_loop_ret_Some_def
  proof(rule odd_factor_critical_invar_cleanupI, goal_cases)
    case (1 X Y)
    then show ?case
      by(intro odd_factor_critical_invarD[OF assms(3)]) auto
  qed

  show ?th4
    unfolding to_loop_ret_Some_def
  proof(rule invar_strict_odd_pos_cleanupI, goal_cases)
    case (1 Bls)
    then show ?case 
      using assms(4) invar_strict_odd_posD by blast
  qed

  show ?th5
    using assms(6)
    by(auto elim!: invar_feasible_piE 
        intro!: invar_feasible_pi_cleanupI 
        simp add: to_loop_ret_Some_def)

  have max_set_in_quot_Vs: 
    "Bls \<in> Vs (Gt \<sslash> maxes)" if asm: "Bls \<in> maxes" for Bls
  proof-
    obtain e where e: "e \<in> Gt" "e \<in> Delta G Bls"
      using asm maxes_have_crossings by blast
    then obtain u v where "e ={u, v}" "u \<noteq> v"
      using graph_invar_tight by blast
    then obtain u v where uv: "e ={u, v}" "u \<noteq> v" "u \<in> Bls" "v \<notin> Bls" "{u, v} \<in> G"
      using e by (auto elim!: in_DeltaE simp add: doubleton_eq_iff)+
    obtain V where V: "v \<in> V" "V \<in> maxes" 
      using  part uv(5)
      by(auto dest!: partition_onD1 edges_are_Vs_2)
    have "{Bls, V} \<in> Gt \<sslash> maxes"
      using V asm uv e(1)
      by(auto intro!: exI[of _ Bls, OF exI[of _ V]] bexI[of _ e] 
          simp add: partition_quotient_graph_def)
    thus ?thesis
      by auto
  qed

  show ?th6
    using  M_perfect Vs_partition_quotient_graph[of Gt maxes] max_set_in_quot_Vs
    by(auto elim!: perfect_matchingE 
        intro!: invar_tight_matching_cleanupI perfect_matchingI 
        simp add: Gt_def maxes_def to_loop_ret_Some_def)
qed

lemma top_loop_None_dual_unbounded:
  assumes "top_loop_dom (\<pi>, \<OO>)"
    "odds_invar (\<pi>, \<OO>)"
    "odd_factor_critical_invar (\<pi>, \<OO>)"
    "invar_strict_odd_pos (\<pi>, \<OO>)"
    "invar_non_zero_pi_in_odd (\<pi>, \<OO>)"
    "invar_feasible_pi (\<pi>, \<OO>)"
    "top_loop (\<pi>, \<OO>) = None"
  shows "\<exists> \<pi>'. feasible_min_perfect_dual_edmonds G w \<pi>' \<and> sum \<pi>' (\<Omega> Vs G) > B"
  using assms(2-)
  by(induction rule: top_loop_induct[OF assms(1)])
    (auto intro: top_loop_call1_pres top_loop_call2_pres top_loop_ret_None_1_dual_unbounded 
      top_loop_ret_None_2_dual_unbounded
      simp add: top_loop_simps)

definition "invars_for_second_loop state =
        (odds_invar_cleanup state \<and>
        odd_factor_critical_invar_cleanup state \<and>
        invar_matching_delta_of_non_zero_sets_cleanup state \<and>
        invar_strict_odd_pos_cleanup state \<and>
        invar_feasible_pi_cleanup state \<and>
        invar_tight_matching_cleanup state)"

lemma invars_for_second_loopI:
  "\<lbrakk> odds_invar_cleanup state; 
     odd_factor_critical_invar_cleanup state; 
     invar_matching_delta_of_non_zero_sets_cleanup state; 
     invar_strict_odd_pos_cleanup state; 
     invar_feasible_pi_cleanup state; 
     invar_tight_matching_cleanup state \<rbrakk> \<Longrightarrow> invars_for_second_loop state"
  and invars_for_second_loopE:"\<lbrakk> invars_for_second_loop state; 
         \<lbrakk> odds_invar_cleanup state; 
           odd_factor_critical_invar_cleanup state; 
           invar_matching_delta_of_non_zero_sets_cleanup state; 
           invar_strict_odd_pos_cleanup state; 
           invar_feasible_pi_cleanup state; 
           invar_tight_matching_cleanup state \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  and invars_for_second_loopD:
  "invars_for_second_loop state \<Longrightarrow> odds_invar_cleanup state"
  "invars_for_second_loop state \<Longrightarrow> odd_factor_critical_invar_cleanup state"
  "invars_for_second_loop state \<Longrightarrow> invar_matching_delta_of_non_zero_sets_cleanup state"
  "invars_for_second_loop state \<Longrightarrow> invar_strict_odd_pos_cleanup state"
  "invars_for_second_loop state \<Longrightarrow> invar_feasible_pi_cleanup state"
  "invars_for_second_loop state \<Longrightarrow> invar_tight_matching_cleanup state"
  unfolding invars_for_second_loop_def by auto

lemma top_loop_ret_None_neq_Some: "top_loop_ret_None \<pi> \<OO> = Some result \<Longrightarrow> False"
  by(auto simp add: top_loop_ret_None_def)

subsection \<open>Correctness of First Loop\<close>

lemma top_loop_Some_result:
  assumes "top_loop_dom (\<pi>, \<OO>)"
    "odds_invar (\<pi>, \<OO>)"
    "odd_factor_critical_invar (\<pi>, \<OO>)"
    "invar_strict_odd_pos (\<pi>, \<OO>)"
    "invar_non_zero_pi_in_odd (\<pi>, \<OO>)"
    "invar_feasible_pi (\<pi>, \<OO>)"
    "top_loop (\<pi>, \<OO>) = Some result"
  shows "invars_for_second_loop result"
  using assms(2-) 
  by(induction rule: top_loop_induct[OF assms(1)])
    (auto intro: top_loop_return_Some
      intro: invars_for_second_loopI
      top_loop_call1_pres top_loop_call2_pres top_loop_ret_None_1_dual_unbounded 
      top_loop_ret_None_2_dual_unbounded
      dest: top_loop_ret_None_neq_Some
      simp add: top_loop_simps)

end

subsection \<open>The Final Expansion Loop: Setup\<close>

text \<open>After the primal-dual adjustments, there might still be a few contracted sets left.
      These need to be expanded for a matching in the actual graph.\<close>

locale naive_weighted_blossom_with_cleanup =
  naive_weighted_blossom_main_loop where G = G 
for G :: "'v set set"+
fixes remove_set::"'v set \<Rightarrow> 'v"
assumes remove_set: "\<And> x. remove_set {x} = x"

begin

lemmas sel_True = sel_correct(1)[where P = "\<lambda> x. True", simplified] 

lemma sel_True_singleton: "sel (\<lambda>x. True) {u} = u"
  using sel_True by auto

lemma "(image remove_set) ` {{{u}, {v}}} = {{u, v}}"
  using remove_set 
  by auto

lemma image_sel_true_simp:
  "(image remove_set) ` {{{u}, {v}} | u v. P u v} = {{u, v} | u v. P u v}"
proof-
  have "P u v \<Longrightarrow> 
        \<exists>x. (\<exists>u v. x = {{u}, {v}} \<and> P u v) \<and> {u, v} = {y. \<exists>x\<in>x. y = remove_set x}" for u v
    by(rule exI[of _ "{_, _}"]) (auto  simp add: remove_set)+
  thus ?thesis
    by(auto simp add: remove_set doubleton_eq_iff image_def)+
qed

lemma image_sel_true_dblton_simp:
  "dblton_graph E \<Longrightarrow> (image remove_set) ` {{{u}, {v}} | u v. {u, v} \<in> E} = E"
  by(force elim!: simp add:  image_sel_true_simp)

lemma remove_set_of_singletons:"remove_set ` {{v} |v. v \<in> X} = X"
  by(auto intro!: image_eqI simp add: remove_set)

function (domintros) cleanup_loop::"(('v set \<Rightarrow> real) \<times> 'v set set set \<times> 'v set set) \<Rightarrow>
          (('v set \<Rightarrow> real) \<times> 'v set set)"
  where
    "cleanup_loop (\<pi>, M, \<OO>) =
      (if \<exists> Bls \<in> \<OO>. card Bls > 1 then
          let Gt = odd_tight_subgraph G w \<pi>;
              maxes = maximal_sets \<OO>;
              Bls = sel (\<lambda> Bls. card Bls > 1) maxes;
              Bls' = sel (\<lambda> Bls'. {Bls, Bls'} \<in> M) maxes;
              Blses = immediate_subsets \<OO> Bls;
              \<OO>' = \<OO> - {Bls};
              bls = sel (\<lambda> bls. {bls, Bls'} \<in> Gt \<sslash> maximal_sets \<OO>') Blses;
              M' = (case find_matching_or_decomposition ((Gt \<sslash> maximal_sets \<OO>') \<lbrakk>Blses - {bls}\<rbrakk>)
                     of match M \<Rightarrow> M);
              M'' = M - {{Bls, Bls'}} \<union> {{bls, Bls'}} \<union> M'
           in cleanup_loop (\<pi>, M'', \<OO>')
       else (\<pi>, (image remove_set) ` M))"
  by pat_completeness auto

definition cleanup_loop_call_cond :: "(('v set \<Rightarrow> real) \<times> 'v set set set \<times> 'v set set) \<Rightarrow> bool" 
  where
    "cleanup_loop_call_cond \<equiv> \<lambda>(\<pi>, M, \<OO>). \<exists> Bls \<in> \<OO>. card Bls > 1"

definition cleanup_loop_ret_cond :: "(('v set \<Rightarrow> real) \<times> 'v set set set \<times> 'v set set) \<Rightarrow> bool" 
  where
    "cleanup_loop_ret_cond \<equiv> \<lambda>(\<pi>, M, \<OO>). \<not> (\<exists> Bls \<in> \<OO>. card Bls > 1)"

definition cleanup_loop_upd:: "(('v set \<Rightarrow> real) \<times> 'v set set set \<times> 'v set set) \<Rightarrow> 
                                 (('v set \<Rightarrow> real) \<times> 'v set set set \<times> 'v set set)" 
  where
    "cleanup_loop_upd \<equiv> \<lambda>(\<pi>, M, \<OO>).
      let Gt = odd_tight_subgraph G w \<pi>;
          maxes = maximal_sets \<OO>;
          Bls = sel (\<lambda> Bls. card Bls > 1) maxes;
          Bls' = sel (\<lambda> Bls'. {Bls, Bls'} \<in> M) maxes;
          Blses = immediate_subsets \<OO> Bls;
          \<OO>' = \<OO> - {Bls};
          bls = sel (\<lambda> bls. {bls, Bls'} \<in> Gt \<sslash> maximal_sets \<OO>') Blses;
          M' = (case find_matching_or_decomposition ((Gt \<sslash> maximal_sets \<OO>') \<lbrakk>Blses - {bls}\<rbrakk>)
                 of match M \<Rightarrow> M);
          M'' = M - {{Bls, Bls'}} \<union> {{bls, Bls'}} \<union> M'
       in (\<pi>, M'', \<OO>')"

definition cleanup_loop_ret :: "(('v set \<Rightarrow> real) \<times> 'v set set set \<times> 'v set set) \<Rightarrow> 
                                 (('v set \<Rightarrow> real) \<times> 'v set set)" 
  where
    "cleanup_loop_ret \<equiv> \<lambda>(\<pi>, M, \<OO>). (\<pi>, (image remove_set) ` M)"

lemma cleanup_loop_simps:
  assumes "cleanup_loop_dom (\<pi>, M, \<OO>)"
  shows "cleanup_loop_call_cond (\<pi>, M, \<OO>) \<Longrightarrow>
           cleanup_loop (\<pi>, M, \<OO>) = cleanup_loop (cleanup_loop_upd (\<pi>, M, \<OO>))"
    and "cleanup_loop_ret_cond (\<pi>, M, \<OO>) \<Longrightarrow> cleanup_loop (\<pi>, M, \<OO>) = cleanup_loop_ret (\<pi>, M, \<OO>)"
  by (auto simp add: cleanup_loop_call_cond_def  cleanup_loop.psimps[OF assms]
      cleanup_loop_upd_def cleanup_loop_ret_cond_def cleanup_loop_ret_def Let_def)

lemma cleanup_loop_induct:
  assumes dom: "cleanup_loop_dom (\<pi>, M, \<OO>)"
  assumes step: "\<And>\<pi> M \<OO>. cleanup_loop_dom (\<pi>, M, \<OO>) \<Longrightarrow> 
                   cleanup_loop_call_cond (\<pi>, M, \<OO>) \<Longrightarrow> 
                   P (cleanup_loop_upd (\<pi>, M, \<OO>)) \<Longrightarrow> P (\<pi>, M, \<OO>)"
  assumes base: "\<And>\<pi> M \<OO>. cleanup_loop_dom (\<pi>, M, \<OO>) \<Longrightarrow> 
                   cleanup_loop_ret_cond (\<pi>, M, \<OO>) \<Longrightarrow> P (\<pi>, M, \<OO>)"
  shows "P (\<pi>, M, \<OO>)"
proof (induction rule: cleanup_loop.pinduct[OF dom])
  case (1 \<pi> M \<OO>)
  show ?case
  proof (cases "cleanup_loop_call_cond (\<pi>, M, \<OO>)")
    case True
    then have "\<exists>Bls\<in>\<OO>. 1 < card Bls" 
      unfolding cleanup_loop_call_cond_def by simp

\<comment> \<open>Extract the induction hypothesis by unfolding your custom state update\<close>
    with 1 True have "P (cleanup_loop_upd (\<pi>, M, \<OO>))"
      unfolding cleanup_loop_upd_def Let_def by auto

    with True 1 step show ?thesis 
      by blast
  next
    case False
    then have "cleanup_loop_ret_cond (\<pi>, M, \<OO>)"
      unfolding cleanup_loop_call_cond_def cleanup_loop_ret_cond_def by simp

    with False 1 base show ?thesis 
      by blast
  qed
qed

lemma cleanup_loop_upd_pres:
  assumes "cleanup_loop_call_cond (\<pi>, M, \<OO>)"
    "odds_invar_cleanup (\<pi>, M, \<OO>)"
    "odd_factor_critical_invar_cleanup (\<pi>, M, \<OO>)" 
    "invar_matching_delta_of_non_zero_sets_cleanup (\<pi>, M, \<OO>)"
    "invar_strict_odd_pos_cleanup (\<pi>, M, \<OO>)"
    "invar_feasible_pi_cleanup (\<pi>, M, \<OO>)" 
    "invar_tight_matching_cleanup (\<pi>, M, \<OO>)"
  shows  "odds_invar_cleanup (cleanup_loop_upd (\<pi>, M, \<OO>))" (is ?th1)
    "odd_factor_critical_invar_cleanup (cleanup_loop_upd (\<pi>, M, \<OO>))" (is ?th2)
    "invar_matching_delta_of_non_zero_sets_cleanup (cleanup_loop_upd (\<pi>, M, \<OO>))" (is ?th3)
    "invar_strict_odd_pos_cleanup (cleanup_loop_upd (\<pi>, M, \<OO>))" (is ?th4)
    "invar_feasible_pi_cleanup (cleanup_loop_upd (\<pi>, M, \<OO>))" (is ?th5)
    "invar_tight_matching_cleanup (cleanup_loop_upd (\<pi>, M, \<OO>))" (is ?th6)
    "card (snd (snd (\<pi>, M, \<OO>))) > card (snd (snd (cleanup_loop_upd (\<pi>, M, \<OO>))))" (is ?th7)
proof-

  define Gt where "Gt = odd_tight_subgraph G w \<pi>"
  define maxes where "maxes = maximal_sets \<OO>"
  define Bls where "Bls = sel (\<lambda> Bls. card Bls > 1) maxes"

  note odds_invar_cleanupD = odds_invar_cleanupD[OF assms(2)]
  note odd_factor_critical_invar_cleanupD = odd_factor_critical_invar_cleanupD[OF assms(3)]
  note invar_matching_delta_of_non_zero_sets_cleanupD =
    invar_matching_delta_of_non_zero_sets_cleanupD[OF assms(4)]
  note invar_strict_odd_pos_cleanupD = invar_strict_odd_pos_cleanupD[OF assms(5)]
  note invar_feasible_pi_cleanupD=invar_feasible_pi_cleanupD[OF assms(6)]
  note invar_tight_matching_cleanupD=invar_tight_matching_cleanupD[OF assms(7)]

  have not_all_singletons:"\<exists> Bls \<in> \<OO>. card Bls > 1"
    using assms(1) by(auto simp add: cleanup_loop_call_cond_def)

  have sets_in_O_in_G: "X \<in> \<OO> \<Longrightarrow> X \<subseteq> Vs G" for X
    using odds_invar_cleanupD(4) by auto
  have set_in_maxes_in_G: "X \<in> maxes \<Longrightarrow> X \<subseteq> Vs G" for X
    using  sets_in_O_in_G by(auto elim!: in_maximal_setsE simp add: maxes_def)

  have there_is_max_gtr_1:"\<exists> Bls \<in> maxes. card Bls > 1"
  proof-
    obtain Bls where "Bls \<in> \<OO>" "card Bls > 1"
      using not_all_singletons by auto
    moreover then obtain Blss where "Blss \<in> maxes" "Blss \<supseteq> Bls" 
      using finite_Vs
        finite_there_is_maximal_set[OF finite_U_finite_family, OF _ odds_invar_cleanupD(1)]
      by(auto simp add: maxes_def)
    moreover hence "card Blss \<ge> card Bls"
      using finite_Vs finite_subset set_in_maxes_in_G
      by(auto intro!: card_mono)
    ultimately show ?thesis 
      by(auto intro!: bexI[of _ Blss])
  qed
  have finite_maxes: "finite maxes" 
    using finite_Vs odds_invar_cleanupD(4) union_split_with_maximal_sets[of \<OO>]
    by (fastforce intro!: finite_UnionD simp add: maxes_def)
  have Bls_prop: "Bls \<in> maxes" "card Bls > 1"
    using sel_correct[OF there_is_max_gtr_1] finite_maxes
    by(auto simp add: Bls_def)
  have dblton_graph_Gt: "dblton_graph (Gt \<sslash> maximal_sets \<OO>)"
    by (simp add: partition_quotient_graph_is_dblton)
  have M_in_tight_quot:"M \<subseteq> (Gt \<sslash> maximal_sets \<OO>)"
    using Gt_def invar_tight_matching_cleanupD(1) perfect_matchingE by auto
  hence dblton_graph_M: "dblton_graph M"
    using dblton_graph_Gt by blast

  define Bls' where "Bls' = sel (\<lambda> Bls'. {Bls, Bls'} \<in> M) maxes"

  have Bls_partner:"\<exists> Bls' \<in> maxes. {Bls, Bls'} \<in> M"
  proof-
    obtain e where "e \<in> M" "Bls \<in> e"
      using invar_tight_matching_cleanupD(2)[symmetric] Bls_prop(1) 
      by(auto simp add: maxes_def vs_member Gt_def)
    moreover then obtain Bls' where "e = {Bls, Bls'}" "Bls \<noteq> Bls'" 
      using dblton_graph_M
      by(auto elim: Undirected_Set_Graphs.dblton_graphE)
    ultimately show ?thesis
      by(auto intro: bexI[of _ Bls'] 
          simp add: edges_are_Vs_2 maxes_def invar_tight_matching_cleanupD(2)[symmetric])
  qed
  have Bls'_props: "Bls' \<in> maxes" "{Bls, Bls'} \<in> M"
    using sel_correct[OF Bls_partner] finite_maxes by(auto simp add: Bls'_def)
  hence Bls_Bls'_in_Gt_quot:"{Bls, Bls'} \<in> (Gt \<sslash> maximal_sets \<OO>)"
    using M_in_tight_quot by blast

  define Blses where "Blses = immediate_subsets \<OO> Bls"
  define \<OO>' where "\<OO>' = \<OO> - {Bls}"

  have Bls_Union_of_immediate_subsets:"Bls = \<Union> (immediate_subsets \<OO> Bls)"
    using Bls_prop(1) Bls_prop(2)
    by(intro composed_family_Union_of_immediate_subsets)
      (auto elim: in_maximal_setsE 
        simp add: odds_invar_cleanupD(3,4) maxes_def finite_UnionD finite_Vs)

  have maximal_sets_after_are:
    "maximal_sets \<OO>' = maxes - {Bls} \<union> (immediate_subsets \<OO> Bls)"
    using Bls_prop(1)
    unfolding \<OO>'_def maxes_def
    by(intro remove_maximal_set_from_laminar_family[OF odds_invar_cleanupD(1)]) simp

  have bls_in_Gt:"\<exists> bls \<in> Blses. {bls, Bls'} \<in> Gt \<sslash> maximal_sets \<OO>'"
  proof-
    obtain e where e:"e \<in> Gt" "Bls \<in> maximal_sets \<OO>" "Bls' \<in> maximal_sets \<OO>"
      "e \<inter> Bls \<noteq> {}" "e \<inter> Bls' \<noteq> {}" "Bls \<noteq> Bls'"
      using Bls_Bls'_in_Gt_quot
      by (auto simp add: partition_quotient_graph_def doubleton_eq_iff)
    then obtain bls where bls: "bls \<in> immediate_subsets \<OO> Bls" "e \<inter> bls \<noteq> {}"
      using Bls_Union_of_immediate_subsets by auto
    have bls_maximal:"bls \<in> maximal_sets \<OO>'"
      by (simp add: bls(1) maximal_sets_after_are)
    moreover have "Bls' \<in> maximal_sets \<OO>'"
      using Bls'_props(1) e(6) maximal_sets_after_are by force
    moreover have "bls \<noteq> Bls'"
      using e(2,3) bls(1) in_maximal_setsE[of Bls \<OO>] in_maximal_setsE[of Bls' \<OO>]
        immediate_subsets_subset(1)[of Bls' \<OO> Bls]
      by auto
    ultimately have "{bls, Bls'} \<in> Gt \<sslash> maximal_sets \<OO>'"
      using bls(2) e(1,5)
      by(auto intro!: exI[of _ bls, OF exI[of _ Bls']] bexI[of _ e]
          simp add: partition_quotient_graph_def doubleton_eq_iff)
    thus ?thesis
      using Blses_def bls(1) by auto
  qed

  define bls where "bls = sel (\<lambda> bls. {bls, Bls'} \<in> Gt \<sslash> maximal_sets \<OO>') Blses"
  have finite_Blses: "finite Blses" 
    using finite_Vs Bls_prop(1) Bls_Union_of_immediate_subsets  finite_UnionD[of Blses]
      set_in_maxes_in_G[of Bls] finite_subset[of Bls "Vs G"]
    by (auto simp add: Blses_def)
  have bls_prop:"{bls, Bls'} \<in> Gt \<sslash> maximal_sets \<OO>'" "bls \<in> Blses"
    using sel_correct[OF bls_in_Gt finite_Blses] 
    by(auto simp add: bls_def)

  define M' where "M' = (case find_matching_or_decomposition ((Gt \<sslash> maximal_sets \<OO>') \<lbrakk>Blses - {bls}\<rbrakk>)
                 of match M \<Rightarrow> M)"

  have Bls_is_Union_Blses:"Bls = \<Union> Blses"
    using Bls_Union_of_immediate_subsets Blses_def by fastforce
  have laminar_maxes_after: "laminar (Vs G) \<OO>'"
    by(intro laminar_subset[OF odds_invar_cleanupD(1)]) (auto simp add: \<OO>'_def)
  have dlbton_Gt: " dblton_graph Gt"
    by (simp add: Gt_def graph graph_invar_odd_tight_subgraph)
  have disjoint_Blses: "disjoint Blses"
    using finite_Vs disjoint_unionD2
      maximal_sets_in_laminar_family_are_global_partition[of "Vs G" \<OO>']
    by(auto simp add: partition_on_def Blses_def laminar_maxes_after maximal_sets_after_are)
  have graph_invar_Gt: "graph_invar (Gt \<sslash> maximal_sets \<OO>')"
    using finite_Vs laminar_Union_finite
    by(intro partition_quotient_graph_graph_invar[OF _
          maximal_sets_in_laminar_family_are_global_partition[OF laminar_maxes_after]])
      (auto intro!: laminar_Union_finite [OF  _ laminar_maxes_after] simp add: finite_Vs)
  hence graph_invar_Gt_on_Bls: "graph_invar ((Gt \<sslash> maximal_sets \<OO>') \<lbrakk>Blses - {bls}\<rbrakk>)"
    by (simp add: graph_invar_graph_inter_Vs)

  have hlper: "\<lbrakk>M \<subseteq> (Gt \<lbrakk>\<Union> Blses\<rbrakk> \<sslash> Blses); Vs M = Blses - {bls}\<rbrakk>
              \<Longrightarrow> M \<subseteq>  Gt \<sslash> Blses - {bls} \<lbrakk>Blses - {bls}\<rbrakk>" for M
  proof(subst (asm) partition_quotient_graph_inter_Vs_commute[symmetric, where \<P> = "Blses"], goal_cases)
    case 4
    show ?case 
    proof(rule, rule in_graph_inter_VsI, goal_cases)
      case (1 e)
      then show ?case 
        using 4
        by(subst edge_in_quot_remove_irrelevant_areas)(auto elim: in_graph_inter_VsE[OF set_mp])
    next
      case 2
      thus ?case
        using 4 by auto
    qed
  qed (auto simp add: dlbton_Gt disjoint_Blses)
  have matching_inter_Blses:
    "\<exists>M. perfect_matching ( Gt \<sslash> maximal_sets \<OO>' \<lbrakk>Blses - {bls}\<rbrakk>) M" (is ?thesis1)
    and Vs_Blses_minus_bls:"Vs ((Gt \<sslash> maximal_sets \<OO>') \<lbrakk>Blses - {bls}\<rbrakk>) = Blses - {bls}" (is ?thesis2)
  proof-
    have "\<exists>M. graph_matching ( odd_tight_subgraph G w \<pi> \<lbrakk>Bls\<rbrakk> \<sslash> immediate_subsets \<OO> Bls) M \<and>
      Vs M = immediate_subsets \<OO> Bls - {bls}"
      using Bls_prop(1,2)  bls_prop(2)
      by(intro odd_factor_critical_invar_cleanupD)
        (auto elim: in_maximal_setsE simp add: maxes_def  Blses_def)
    then obtain M where M: "graph_matching ( odd_tight_subgraph G w \<pi> \<lbrakk>Bls\<rbrakk> \<sslash> immediate_subsets \<OO> Bls) M"
      "Vs M = immediate_subsets \<OO> Bls - {bls}"
      by auto
    from M have th1: "perfect_matching ( Gt \<sslash> maximal_sets \<OO>' \<lbrakk>Blses - {bls}\<rbrakk>) M"
    proof(subst partition_quotient_graph_inter_Vs_commute, goal_cases)
      case 1
      then show ?case 
        by (simp add: Blses_def le_supI1 maximal_sets_after_are sup_commute)
    next
      case 2
      then show ?case 
        by (simp add: Gt_def graph graph_invar_odd_tight_subgraph)
    next
      case 3
      then show ?case
        by(intro disjointI, intro laminar_maximal_sets_disjoint[OF laminar_maxes_after]) simp+
    next
      case 4
      thus ?case
      proof(intro perfect_matchingI, goal_cases)
        case 1
        then show ?case 
          unfolding Gt_def[symmetric] Blses_def[symmetric] 
          unfolding Bls_is_Union_Blses
        proof(subst partition_quotient_graph_inter_Vs_commute[symmetric, where \<P> = "Blses - {bls}"], goal_cases)
          case 3
          then show ?case
            using  disjoint_Blses by(auto simp add: disjoint_def)
        next
          case 4
          then show ?case 
            using hlper by auto
        qed (auto simp add: dlbton_Gt)
      next
        case 3
        thus ?case 
          using dlbton_Gt disjoint_Blses bls_prop(2) Bls_is_Union_Blses Blses_def Gt_def
            graph_inter_Vs_subset(2)[of "Gt \<sslash> Vs M" "Vs M"] pairwise_insert[of disjnt bls "Vs M"]
            insert_Diff[of bls Blses] partition_quotient_graph_inter_Vs_commute[of "Vs M" "Vs M" Gt]
            subgraph_vs_subset_eq[of M " Gt \<sslash> Vs M \<lbrakk>Vs M\<rbrakk>"] hlper 
          by force
      qed auto
    qed
    thus ?thesis1
      by auto
    show ?thesis2
      using Blses_def M(2) th1 perfect_matchingD(3)
      by force
  qed
  have M'_def: "find_matching_or_decomposition ((Gt \<sslash> maximal_sets \<OO>') \<lbrakk>Blses - {bls}\<rbrakk>) = match M'"
    using find_matching_or_decomposition_correct(1)[OF graph_invar_Gt_on_Bls matching_inter_Blses]
    by(auto simp add: M'_def) 

  note M_perfect = find_matching_or_decomposition_correct(3)[OF graph_invar_Gt_on_Bls M'_def]

  hence Vs_M'_is:"Vs M' = Blses - {bls}" 
    using Vs_Blses_minus_bls
    by (simp add: perfect_matchingD(3))

  define M'' where "M'' = M - {{Bls, Bls'}} \<union> {{bls, Bls'}} \<union> M'"
  have cleanup_loop_upd_def: "cleanup_loop_upd (\<pi>, M, \<OO>) = (\<pi>, M'', \<OO>')"
    using M'_def
    by(auto simp add: cleanup_loop_upd_def M''_def \<OO>'_def M'_def Bls_def Bls'_def maxes_def
        bls_def Blses_def Gt_def Let_def)

  show ?th1
    unfolding cleanup_loop_upd_def
  proof(rule odds_invar_cleanupI, goal_cases)
    case 1
    then show ?case 
      by (simp add: laminar_maxes_after)
  next
    case 2
    then show ?case 
      by (simp add: \<OO>'_def odds_invar_cleanupD(2))
  next
    case 3
    then show ?case
      using Bls_prop(1) composed_family_expand_maximal odds_invar_cleanupD(3) 
      by(auto simp add: maxes_def \<OO>'_def)
  next
    case 4
    then show ?case
      unfolding \<OO>'_def
      using Bls_prop 
      by (subst composed_family_expand_maximal_same_universe)
        (auto simp add: odds_invar_cleanupD(3,4)  maxes_def)
  next
    case 5
    thus ?case
      using odds_invar_cleanupD(5) 
      by(auto intro:  laminar_subset simp add: \<OO>'_def)
  qed

  have same_immediate_subsets:"X \<in> \<OO>' \<Longrightarrow> immediate_subsets \<OO>' X = immediate_subsets \<OO> X" for X
    unfolding \<OO>'_def
    using Bls_prop(1) 
    by(intro same_immediate_subsets_remove)
      (auto elim!: in_maximal_setsE simp add: maxes_def)

  show ?th2
    unfolding cleanup_loop_upd_def
  proof(rule odd_factor_critical_invar_cleanupI, goal_cases)
    case (1 X Y)
    then show ?case 
      using same_immediate_subsets odd_factor_critical_invar_cleanupD 
      by (auto simp add: \<OO>'_def same_immediate_subsets)
  qed

  have VsM_in_maxes:"Vs M \<subseteq> maxes"
    by (simp add: invar_tight_matching_cleanupD(2) maxes_def)
  moreover have Bls'_neq_Bls:"Bls' \<noteq> Bls"
    using Bls_Bls'_in_Gt_quot partition_quotient_graphD by fastforce
  ultimately have Bls'_inter_Bls_empty: "Bls' \<inter> Bls = {}"
    using odds_invar_cleanupD(1) Bls'_props(1) Bls_prop(1) 
    by(intro  laminar_maximal_sets_disjoint[of "Vs G" \<OO> Bls' Bls])(auto simp add: maxes_def)
  have Vs_M_inter_M'_empty: "Vs (M - {{Bls, Bls'}}) \<inter> Vs M' = {}"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain x where x: "x \<in> Vs (M - {{Bls, Bls'}})" "x \<in> Vs M'" by auto
    hence "x \<in> maxes" 
      using invar_tight_matching_cleanupD(2) Bls'_props(2) insert_Diff[of "{Bls, Bls'}" M]
        in_Vs_insert[of x "M - {{Bls, Bls'}}" "{Bls, Bls'}"]
      by (auto simp add: maxes_def)
    moreover have "x \<subset> Bls" 
      using Vs_M'_is x(2)
      by(intro immediate_subsets_subset(1))(auto simp add: Blses_def)
    ultimately show False 
      using Bls_prop(1) 
      by(auto elim: in_maximal_setsE simp add: maxes_def)
  qed
  have M_inter_M'_empty: "M \<inter> M' = {}"
  proof(rule ccontr, goal_cases)
    case 1
    then obtain e where e: "e \<in> M" "e \<in> M'" by auto
    hence "e \<subseteq> maxes"
      using VsM_in_maxes by blast
    moreover have "e \<subseteq> immediate_subsets \<OO> Bls"
      using Blses_def Vs_M'_is e(2) by blast
    moreover obtain x where "x \<in> e"
      using dblton_graph_M e(1) by blast
    ultimately show False 
      using Bls_prop(1) immediate_subsets_subset(1)[of x \<OO> Bls]  in_maximal_setsE[of x \<OO>] 
        subsetD[of e "maximal_sets \<OO>" x] subsetD[of e "immediate_subsets \<OO> Bls" x]
        in_maximal_setsE[of Bls \<OO>] in_maximal_setsE[of x \<OO>]
      by(auto simp add:  maxes_def) 
  qed

  show ?th3
    unfolding cleanup_loop_upd_def
  proof(rule invar_matching_delta_of_non_zero_sets_cleanupI, goal_cases)
    case (1 Bls_here)
    then show ?case 
    proof(cases "Bls_here = Bls", goal_cases)
      case 1
      note one = this
      show ?case 
        unfolding M''_def
      proof(rule forw_subst[of _ "{{bls, Bls'}}"], goal_cases)
        case 1
        then show ?case
        proof(rule, goal_cases)
          case 1
          then show ?case
          proof(rule, goal_cases)
            case (1 e)
            then obtain U V where UV:
              "{U, V} \<in> M - {{Bls, Bls'}} \<union> {{bls, Bls'}} \<union> M'" "U \<subseteq> Bls_here" "\<not> V \<subseteq> Bls_here"
              "e = {U, V}" by (auto simp add: doubleton_eq_iff)
            then show ?case 
            proof(elim UnE, goal_cases)
              case 1
              hence "{U, V} \<subseteq> maxes" 
                using  invar_tight_matching_cleanupD(2)[symmetric]
                by(auto simp add: maxes_def)
              hence "U = Bls"
                using one(3) Bls_prop(1) UV(2) odds_invar_cleanupD(1)
                  laminar_maximal_sets_nempty[of "Vs G" \<OO> "{}"] laminar_maximal_sets_disjoint[of "Vs G" \<OO> U Bls]
                by (force elim: inf.orderE[of U Bls] simp add:  maxes_def)
              hence "{U, V} = {Bls, Bls'}"
                using 1(1,4) invar_tight_matching_cleanupD(1)  Bls'_props(2)
                by(intro matching_revD[of M]) (auto elim!: perfect_matchingE)
              hence False
                using 1 by simp
              thus ?case
                by simp
            next
              case 2
              then show ?case
                by simp
            next
              case 3
              hence "U \<subset> Bls"
                using  Vs_M'_is 
                by(intro immediate_subsets_subset(1))
                  (auto simp add: Blses_def edges_are_Vs)
              hence False
                using  "3"(4) Bls_is_Union_Blses UV(3) edges_are_Vs_2[of U V M']  
                by(auto simp add:  Vs_M'_is  one(3))
              thus ?case
                by simp
            qed
          qed
        next
          case 2
          then show ?case 
            using Bls_is_Union_Blses bls_prop(2) one(3) Bls'_neq_Bls Bls'_props(1) Bls_prop(1) 
            by(auto intro!: exI[of _ bls, OF exI[of _ Bls']] 
                elim!: in_maximal_setsE 
                simp add: maxes_def)
        qed
      next
        case 2
        then show ?case
          by simp
      qed
    next
      case 2
      note two = this
      hence Bls_here_before:"Bls_here \<in> \<Omega>\<^sub>\<ge>\<^sub>3 Vs G - \<OO>"
        using \<OO>'_def by blast
      hence pi_Bls_here: "\<pi> Bls_here > 0" 
        using assms(6) invar_feasible_pi_cleanupD 2(2)
        by(auto dest!: feasible_min_perfect_dual_edmondsD(2)[where U = Bls_here])
      obtain U' V' where U'V': "{U', V'} \<in> M" "U' \<subseteq> Bls_here" "\<not> V' \<subseteq> Bls_here"
        using invar_matching_delta_of_non_zero_sets_cleanupD[OF Bls_here_before 2(2)] 
        by(auto elim!: card_1_singletonE[simplified] dest!: singleton_not_emptyD)
      hence U'_V'_maxes:"U' \<in> maxes" "V' \<in> maxes"
        using invar_tight_matching_cleanupD(2)
        by(auto simp add: maxes_def edges_are_Vs edges_are_Vs_2)
      have M''_no_crossing:
        "{{U, V} |U V. {U, V} \<in> M' \<and> U \<subseteq> Bls_here \<and> \<not> V \<subseteq> Bls_here} = {}"
      proof(rule ccontr, goal_cases)
        case 1
        then obtain U V where UV: " {U, V} \<in> M'" "U \<subseteq> Bls_here" "\<not> V \<subseteq> Bls_here"
          by auto
        hence UBls: "U \<in> Blses - {bls}" and VBls: "V \<in> Blses - {bls}"
          using Vs_M'_is by(auto simp add: edges_are_Vs edges_are_Vs_2)
        have inter_nempty: "Bls_here \<inter> Bls \<noteq> {}"
          using UV(2) Bls_is_Union_Blses UBls odds_invar_cleanupD(1) 
            immediate_subsets_laminar_disjoint[of "Vs G" \<OO> U Bls U]
          by (auto simp add:  Blses_def)
        hence "Bls_here \<supseteq> Bls \<or> Bls_here \<subset> Bls"
          using odds_invar_cleanupD(5) Bls_here_before pi_Bls_here  Bls_prop(1)
            maximal_sets_subset[of \<OO>]
          by(auto elim!: laminarE simp add:  maxes_def)
        then show ?case 
        proof(elim disjE, goal_cases)
          case 1
          then show ?thesis
            using Bls_is_Union_Blses UV(3) VBls by blast
        next
          case 2
          then show ?case 
            using Bls_prop(1) U'V'(2) U'_V'_maxes(1)
            by(force elim!: in_maximal_setsE simp add: maxes_def)
        qed
      qed
      hence M''_delta_is:"{{U, V} |U V. {U, V} \<in> M'' \<and> U \<subseteq> Bls_here \<and> \<not> V \<subseteq> Bls_here} =
                      {{U, V} |U V. {U, V} \<in> M - {{Bls, Bls'}} \<union> {{bls, Bls'}}
                         \<and> U \<subseteq> Bls_here \<and> \<not> V \<subseteq> Bls_here}"
        unfolding M''_def Un_iff[of _ ] conj_disj_distribR binary_collection_disj_union
        by auto
      define f where "f = (\<lambda> e. if e = {bls, Bls'} then {Bls, Bls'} else e)"
      have same_card:"card {{U, V} |U V. {U, V} \<in> M - {{Bls, Bls'}} \<union> {{bls, Bls'}}
                         \<and> U \<subseteq> Bls_here \<and> \<not> V \<subseteq> Bls_here} = 
            card {{U, V} |U V. {U, V} \<in> M \<and> U \<subseteq> Bls_here \<and> \<not> V \<subseteq> Bls_here}"
      proof(rule bij_betw_same_card[where f = f],
          unfold bij_betw_def, rule, goal_cases)
        case 1
        then show ?case
        proof(rule inj_onI, goal_cases)
          case (1 e1 e2)
          obtain U V  where UV:
            "{U, V} \<in> M - {{Bls, Bls'}} \<union> {{bls, Bls'}}" "U \<subseteq> Bls_here" "\<not> V \<subseteq> Bls_here" "e1 = {U, V}"
            using 1(1) by (auto simp add: doubleton_eq_iff)
          obtain U' V' where U'V':
            "{U', V'} \<in> M - {{Bls, Bls'}} \<union> {{bls, Bls'}}" "U' \<subseteq> Bls_here" "\<not> V' \<subseteq> Bls_here" "e2 = {U', V'}"
            using 1(2) by (auto simp add: doubleton_eq_iff)  
          show ?case 
            using 1(3) U'V'(1,4)  UV(1,4) 
            by (cases "e1 = {bls, Bls'}", all \<open>cases "e2 = {bls, Bls'}"\<close>) (auto simp add: f_def)
        qed
      next
        case 2
        then show ?case
        proof(rule, all \<open>rule\<close>, goal_cases)
          case (1 e)
          then obtain U V where UV:
            "{U, V} \<in> M - {{Bls, Bls'}} \<union> {{bls, Bls'}}" "U \<subseteq> Bls_here" "\<not> V \<subseteq> Bls_here"
            "e = f {U, V}"
            by (auto simp add: doubleton_eq_iff)
          show ?case 
            using UV(4) unfolding f_def
          proof(cases "{U, V} = {bls, Bls'}", goal_cases)
            case 1
            hence "e = {Bls, Bls'}" by auto
            then show ?case 
              using 1(2) unfolding doubleton_eq_iff
            proof(elim disjE, goal_cases)
              case 1
              moreover hence "Bls \<inter> Bls_here \<noteq> {}"
                using bls_prop(2) UV(2) Bls_is_Union_Blses Blses_def odds_invar_cleanupD(1)
                  empty_nin_laminar[of "Vs G" \<OO>]
                  inter_nemptyI[of U Bls Bls_here] in_immediate_subsetsD(1)[of "{}" \<OO> Bls]
                by force
              moreover hence "Bls \<subseteq> Bls_here \<or> Bls_here \<subset> Bls"
                using odds_invar_cleanupD(5) Bls_here_before pi_Bls_here  Bls_prop(1)
                  maximal_sets_subset[of \<OO>]
                by(auto elim!: laminarE simp add:  maxes_def)
              ultimately show ?case 
                using Bls'_props(2) U'_V'_maxes(1) Bls_prop(1) U'V'(2) UV(3)
                by(auto intro!: exI[of _ Bls, OF exI[of _ Bls']] 
                    elim: in_maximal_setsE 
                    simp add: maxes_def)
            next
              case 2
              moreover hence "Bls' \<inter> Bls_here \<noteq> {}"
                using Bls'_props(1) UV(2)  odds_invar_cleanupD(1)
                  inter_nemptyI[of Bls' Bls' Bls_here] laminar_maximal_sets_nempty[of "Vs G" \<OO> "{}"]
                by (auto simp add: maxes_def)
              moreover hence "Bls' \<subseteq> Bls_here \<or> Bls_here \<subset> Bls'"
                using odds_invar_cleanupD(5) Bls_here_before pi_Bls_here 
                  maximal_sets_subset[of \<OO>] UV(2) calculation(2)
                by(auto elim!: laminarE simp add:  maxes_def)
              ultimately show ?case 
                using Bls_is_Union_Blses UV(2,3) bls_prop(2)  Bls'_props(2)
                by (auto intro!: exI[of _ Bls', OF exI[of _ Bls]] 
                    simp add: insert_commute)
            qed
          next
            case 2
            hence e_is_UV: "e = {U, V}"
              by auto
            moreover hence "e \<noteq> {bls, Bls'}"
              using "2"(2) by auto
            ultimately show ?case
              using UV(1-3)
              by (simp, intro exI[of _ U, OF exI[of _ V]]) auto
          qed
        next
          case (2 e)
          then obtain U V where UV: "{U, V} \<in> M" "U \<subseteq> Bls_here" "\<not> V \<subseteq> Bls_here" "e = {U, V}"
            by auto
          hence UV_in_maxes: "U \<in> maxes" "V \<in> maxes"
            using VsM_in_maxes in_mono by blast+
          show ?case
          proof(cases "e = {Bls, Bls'}")
            case True
            hence e_is:"e = f {bls, Bls'}"
              by (auto simp add: f_def)
            have "{Bls, Bls'} = {U, V}"
              using True UV(4) by auto
            then show ?thesis 
              unfolding doubleton_eq_iff
            proof(elim disjE, goal_cases)
              case 1
              then show ?case 
                using Bls_is_Union_Blses  bls_prop(2)  UV(2,3) 
                by (auto intro!: imageI exI[of _ bls, OF exI[of _ V]] simp add: e_is)
            next
              case 2
              have "\<not> bls \<subseteq> Bls_here"
              proof(rule ccontr, goal_cases)
                case 1
                hence "bls \<inter> Bls_here \<noteq> {}"
                  using bls_prop(2)  odds_invar_cleanupD(1) inter_nemptyI[of bls bls Bls_here] 
                    immediate_subsets_laminar_disjoint[of "Vs G" \<OO> "{}" Bls "{}"]
                  by(auto simp add:  Blses_def)
                hence "Bls \<inter> Bls_here \<noteq> {}"
                  using Bls_is_Union_Blses bls_prop(2) by blast
                hence "Bls \<subseteq> Bls_here \<or> Bls_here \<subset> Bls"
                  using pi_Bls_here Bls_here_before odds_invar_cleanupD(5) Bls_prop(1)
                    maximal_sets_subset[of \<OO>]
                  by(auto elim!: laminarE simp add:  maxes_def)
                thus False
                  using "2" Bls'_props(1) Bls_prop(1) UV(2,3) 
                  by(auto elim: in_maximal_setsE simp add: maxes_def)
              qed
              then show ?case
                using 2
                using UV(2) 
                by (auto intro!: imageI exI[of _ U, OF exI[of _ bls]] simp add: e_is)
            qed
          next
            case False
            hence "e \<noteq> {bls, Bls'}"
              using Bls_is_Union_Blses bls_prop(2)  Bls_prop(1) UV_in_maxes(1,2)
                immediate_subsets_subset(1)[of \<OO>]
              by(auto elim!: in_maximal_setsE simp add: UV(4) doubleton_eq_iff maxes_def)
            hence e_is: "e = f e"
              by(auto simp add: f_def)
            show ?thesis
              using False UV(1,2,3,4) 
              by (intro rev_image_eqI[of e _ e f, OF _ e_is])
                (force intro!: exI[of _ U, OF exI[of _ V]])
          qed
        qed
      qed

      show ?case
        using Bls_here_before two(2)
        unfolding M''_delta_is same_card
        by(intro invar_matching_delta_of_non_zero_sets_cleanupD)
    qed
  qed

  show ?th4
    by(auto intro!: invar_strict_odd_pos_cleanupI
        simp add: \<OO>'_def invar_strict_odd_pos_cleanupD cleanup_loop_upd_def)

  show ?th5
    by(auto intro!: invar_feasible_pi_cleanupI 
        simp add: cleanup_loop_upd_def invar_feasible_pi_cleanupD)
  obtain e where e: "e \<in>  odd_tight_subgraph G w \<pi>" "e \<inter> bls \<noteq> {}" "e \<inter> Bls' \<noteq> {}"
    using bls_prop(1) 
    by(auto simp add: partition_quotient_graph_def Gt_def doubleton_eq_iff)
  moreover have "bls \<inter> Bls' = {}"
    using Bls'_inter_Bls_empty Bls_is_Union_Blses bls_prop(2) by auto
  moreover obtain x y where "e = {x, y}" "x \<noteq> y"
    using e(1) by(auto elim!: in_odd_tight_subgraphE local.dblton_graphE)
  ultimately obtain x y where xy: "{x, y} \<in> odd_tight_subgraph G w \<pi>" "x \<in> bls" "y \<in> Bls'" "x \<noteq> y"
    using  insert_commute[of x y "{}"] by force

  have Vs_M_without_Bls_Bls': "Vs (M - {{Bls, Bls'}}) = maxes - {Bls, Bls'}"
    using  Bls'_props(2) invar_tight_matching_cleanupD(1,2)
    by(auto elim!: perfect_matchingE simp add:  maxes_def remove_matching_edge_Vs)

  have Vs_M'_immediate_Bls:"Vs M' = immediate_subsets \<OO> Bls - {bls}"
    by (simp add: Blses_def Vs_M'_is)
  have Vs_M''_maximal_O': "Vs M'' = maximal_sets \<OO>'"
    unfolding \<OO>'_def M''_def vs_union  Vs_M_without_Bls_Bls' Vs_of_edge
      Vs_M'_immediate_Bls
    using Bls_prop(1) Bls'_neq_Bls Bls'_props(1) bls_prop(2)
    by (subst remove_maximal_set_from_laminar_family[of "Vs G"])
      (fastforce simp add: maxes_def Blses_def odds_invar_cleanupD(1))+

  show ?th6
    unfolding cleanup_loop_upd_def
  proof(rule invar_tight_matching_cleanupI, goal_cases)
    case 1
    then show ?case 
      unfolding M''_def maximal_sets_after_are insert_commute[of Bls Bls' Set.empty]
        insert_commute[of bls Bls' Set.empty]
    proof(rule partition_quotient_matching_refine_factor_critical[where x = x and y = y], goal_cases)
      case 1
      then show ?case
        by (simp add: graph graph_invar_odd_tight_subgraph)
    next
      case 2
      then show ?case 
      proof(rule prepartition_onI, goal_cases)
        case 1
        have "finite \<OO>" 
          by (simp add: finite_UnionD finite_Vs odds_invar_cleanupD(4))
        then show ?case
          using Vs_subset[OF odd_tight_subgraph_in_graph, of G w \<pi>] odds_invar_cleanupD(4,5) 
          by(simp add:  maxes_def  union_split_with_maximal_sets[symmetric, of " \<OO>"])
      next
        case (2 p q)
        then show ?case 
          using odds_invar_cleanupD(1) laminar_maximal_sets_disjoint[of "Vs G" \<OO> p q]
          by(auto simp add: disjnt_def maxes_def)
      next
        case 3
        then show ?case 
          using laminar_maximal_sets_nempty maxes_def odds_invar_cleanupD(1) by blast
      qed
    next
      case 3
      have "Blses = (immediate_subsets \<OO> (\<Union> Blses))"
        using Bls_is_Union_Blses Blses_def by blast
      hence Bls_helper: "\<Union> Blses = \<Union> {Y |Y. Y \<in> \<OO> \<and> Y \<subset> \<Union> Blses}"
        by (auto elim!: in_immediate_subsetsE)
      show ?case 
        unfolding Bls_is_Union_Blses
      proof(subst Bls_helper, unfold immediate_subsets_are_maximals,
          rule maximal_sets_in_laminar_family_are_global_partition[of Bls], goal_cases)
        case 1
        then show ?case 
        proof(rule laminar_subset'[OF odds_invar_cleanupD(1)], goal_cases)
          case 1
          then show ?case 
            by auto
        next
          case 2
          then show ?case 
            using Bls_is_Union_Blses by auto
        qed
      next
        case 2
        then show ?case
          using Bls_prop(1) finite_Vs finite_subset set_in_maxes_in_G by blast
      qed
    next
      case 4
      then show ?case 
        by (simp add: invar_tight_matching_cleanupD(1) maxes_def)
    next
      case 5
      then show ?case 
        by (simp add: Bls'_props(2) edge_commute)
    next
      case 6
      then show ?case
        using Blses_def bls_prop(2) by auto
    next
      case 7
      then show ?case 
        by (simp add: xy(2))
    next
      case 8
      then show ?case 
        by (simp add: xy(3))
    next
      case 9
      then show ?case 
        by (simp add: xy(1))
    next
      case 10
      have rw1: "maximal_sets \<OO>' \<inter> Blses = Blses"
        by (simp add: Blses_def maximal_sets_after_are)
      then show ?case 
        using M_perfect
        unfolding Gt_def 
      proof(subst  Bls_is_Union_Blses, unfold graph_inter_vert_minus,
          subst Blses_def,
          subst partition_quotient_graph_inter_Vs_commute[symmetric, of _ "immediate_subsets \<OO> Bls"],
          goal_cases)
        case 2
        then show ?case 
          using Gt_def dlbton_Gt by blast
      next
        case 3
        then show ?case
          using Blses_def disjoint_Blses by blast
      next
        case 4
        then show ?case 
          unfolding Blses_def[symmetric]
            partition_quotient_graph_Vs_inter_intersection rw1
          by(auto elim!: perfect_matchingE)
      qed simp
    next
      case 11
      then show ?case 
        using Blses_def Vs_M'_is by blast
    qed
  next
    case 2
    then show ?case
      by (simp add: Vs_M''_maximal_O')
  qed
  show ?th7
    using Bls_prop(1)
    by(auto elim!: in_maximal_setsE 
        simp add: cleanup_loop_upd_def \<OO>'_def card_Diff1_less_iff
        finite_UnionD finite_Vs odds_invar_cleanupD(4) maxes_def)
qed

lemma Vs_image: "Vs (image f ` E) = f ` Vs E"
  by(auto simp add: Vs_def)

subsection \<open>Invariant Preservation\<close>

lemma cleanup_loop_upd_return:
  assumes "cleanup_loop_ret_cond (\<pi>, M, \<OO>)"
    "odds_invar_cleanup (\<pi>, M, \<OO>)" 
    "invar_matching_delta_of_non_zero_sets_cleanup (\<pi>, M, \<OO>)"
    "invar_feasible_pi_cleanup (\<pi>, M, \<OO>)" 
    "invar_tight_matching_cleanup (\<pi>, M, \<OO>)"
    "cleanup_loop_ret (\<pi>, M, \<OO>) = (\<pi>', M')"
  shows "perfect_matching G M'" (is ?th1)
    "feasible_min_perfect_dual_edmonds G w \<pi>'" (is ?th2)
    "\<And>U. \<lbrakk>U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 Vs G; \<pi>' U \<noteq> 0\<rbrakk> \<Longrightarrow> card (Delta M' U) = 1" 
    "M' \<subseteq> odd_tight_subgraph G w \<pi>'" (is ?th4)
proof-
  have pi'_is:"\<pi>' = \<pi>" and M'_def: "M' = (image remove_set) ` M"
    using assms(6)
    by (auto simp add: cleanup_loop_ret_def)

  note odds_invar_cleanupD = odds_invar_cleanupD[OF assms(2)]
  note invar_matching_delta_of_non_zero_sets_cleanupD =
    invar_matching_delta_of_non_zero_sets_cleanupD[OF assms(3)]
  note invar_feasible_pi_cleanupD=invar_feasible_pi_cleanupD[OF assms(4)]
  note invar_tight_matching_cleanupD=invar_tight_matching_cleanupD[OF assms(5)]

  have odds_singletons:"X \<in> \<OO> \<Longrightarrow> \<exists> x. X = {x}" for X
    using assms(1) odds_invar_cleanupD(1,2) 
      card_1_singleton_iff[of X] odd_pos[of "card X"] 
    by(auto elim!: laminarE simp add: cleanup_loop_ret_cond_def)

  have O_is:"\<OO> = {{v} | v. v \<in> Vs G}"
    using odds_invar_cleanupD(4) insert_subset[of _ "{}" "Vs G"] odds_singletons Union_upper[of "{_}" \<OO>]
    by (auto dest: odds_singletons) force 
  hence O_max_is: "maximal_sets \<OO> = {{v} |v. v \<in> Vs G}"
    by(auto simp add: maximal_sets_def)
  have card_O_one:"\<And> X. X \<in> \<OO> \<Longrightarrow> card X = 1"
    by(auto simp add: O_is)

  have e_in_ME:
    "\<lbrakk>e \<in> M; \<And> u v. \<lbrakk>{u, v} \<in> odd_tight_subgraph G w \<pi>; u \<noteq> v; e ={{u}, {v}}; 
           {u} \<in> \<OO>; {v} \<in> \<OO>\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" for e P
  proof(goal_cases)
    case 1
    note one = this
    hence "e \<in> odd_tight_subgraph G w \<pi> \<sslash> maximal_sets \<OO>"
      using invar_tight_matching_cleanupD(1) perfect_matching_subgraphD by blast
    then show ?case 
    proof(elim in_partition_quotient_graphE, goal_cases)
      case (1 ee U V)
      then obtain u v where "ee = {u, v}" "u \<noteq> v"
        using local.dblton_graphE odd_tight_subgraph_in_graph by blast
      then obtain  u v where "ee = {u, v}" "u \<noteq> v" "u \<in> U" "v \<in> V" "U = {u}" "V ={v}" "U \<in> \<OO>"
        "V \<in> \<OO>"
        using 1 odds_singletons
        by(auto elim!: in_maximal_setsE simp add: doubleton_eq_iff)
      then show ?case
        using 1 by(auto intro!: one(2)[of u v])
    qed
  qed

  have inj_on_O: " inj_on remove_set \<OO>"
    by(auto intro!: inj_onI dest!: odds_singletons simp add: remove_set)

  show ?th1
  proof(rule perfect_matchingI, goal_cases)
    case 1
    then show ?case
      by(auto elim!: e_in_ME  in_odd_tight_subgraphE 
          simp add: M'_def remove_set)
  next
    case 2
    then show ?case
      using invar_tight_matching_cleanupD(1,2)
      by(auto intro!: matching_image inj_on_subset[OF inj_on_O] 
          dest!: perfect_matchingD(2)
          elim: in_maximal_setsE 
          simp add: M'_def)
  next
    case 3
    then show ?case
      unfolding O_max_is M'_def Vs_image invar_tight_matching_cleanupD(2)
      by(auto simp add: remove_set_of_singletons)
  qed

  show ?th2
    by (simp add: invar_feasible_pi_cleanupD pi'_is)

  have edge_in_remove_set_rw:
    "{ua, va} \<in> (`) remove_set ` M \<longleftrightarrow> {{ua}, {va}} \<in> M" for ua va
  proof(rule, goal_cases)
    case 1
    then obtain e where e: "e \<in> M" "{ua, va} = remove_set ` e"
      by auto
    then show ?case 
    proof(elim e_in_ME, goal_cases)
      case (1 u v)
      then show ?case 
        using e(1)
        by (auto simp add: doubleton_eq_iff remove_set insert_commute)
    qed
  next
    case 2
    then show ?case
      by(auto intro!: rev_image_eqI[of "{{ua}, {va}}"] 
          simp add: remove_set)
  qed

  show "\<lbrakk>X \<in> \<Omega>\<^sub>\<ge>\<^sub>3 Vs G; \<pi>' X \<noteq> 0\<rbrakk> \<Longrightarrow> card (Delta M' X) = 1" for X
  proof(goal_cases)
    case 1
    hence "card {{U, V} |U V. {U, V} \<in> M \<and> U \<subseteq> X \<and> \<not> V \<subseteq> X} = 1"
      by(intro invar_matching_delta_of_non_zero_sets_cleanupD)
        (auto elim!: in_odd_subsets_strictE dest: card_O_one simp add: pi'_is)
    moreover have "card {{U, V} |U V. {U, V} \<in> M \<and> U \<subseteq> X \<and> \<not> V \<subseteq> X} = 
         card (Delta M' X)"
    proof(rule bij_betw_same_card[of "image remove_set"], unfold bij_betw_def, rule, goal_cases)
      case 1
      then show ?case 
        by(auto elim!: e_in_ME 
            intro!: inj_onI 
            simp add: doubleton_eq_iff remove_set)
    next
      case 2
      then show ?case
      proof(rule, all \<open>rule\<close>, elim imageE, goal_cases)
        case (1 e ee)
        note one = this
        then obtain U V where UV: "ee = {U, V}" "{U, V} \<in> M" "U \<subseteq> X" "\<not> V \<subseteq> X"
          by auto
        then show ?case 
        proof(elim e_in_ME, goal_cases)
          case (1 u v)
          then show ?case 
            using one
            by(auto simp add: Delta_def M'_def doubleton_eq_iff remove_set edge_in_remove_set_rw)
        qed
      next
        case (2 e)
        thus ?case
          unfolding M'_def
        proof(elim in_DeltaE, elim imageE, goal_cases)
          case (1 u v ee )
          note one = this
          then show ?case 
          proof(elim e_in_ME, goal_cases)
            case (1 ua va)
            then show ?case 
              by (auto simp add: remove_set doubleton_eq_iff, insert one(6,5))
                (auto intro!: exI[of _ u, OF exI[of _ v]] rev_image_eqI[where x = "{{u}, {v}}"]
                  simp add: remove_set insert_commute)
          qed
        qed
      qed
    qed
    ultimately show ?case
      by simp
  qed

  show ?th4
    by(auto elim!: imageE e_in_ME simp add: M'_def remove_set pi'_is)
qed

lemma cleanup_loop_upd_termination:
  assumes "odds_invar_cleanup (\<pi>, M, \<OO>)"
    "odd_factor_critical_invar_cleanup (\<pi>, M, \<OO>)" 
    "invar_matching_delta_of_non_zero_sets_cleanup (\<pi>, M, \<OO>)"
    "invar_strict_odd_pos_cleanup (\<pi>, M, \<OO>)"
    "invar_feasible_pi_cleanup (\<pi>, M, \<OO>)" 
    "invar_tight_matching_cleanup (\<pi>, M, \<OO>)"
  shows "cleanup_loop_dom (\<pi>, M, \<OO>)"
proof-
  define n where "n = card \<OO>"
  thus ?thesis
    using assms
  proof(induction n arbitrary: \<pi> M \<OO> rule: less_induct)
    case (less n \<pi> M \<OO>)
    show ?case
    proof(cases "cleanup_loop_ret_cond (\<pi>, M, \<OO>)")
      case True
      then show ?thesis
        by(auto intro: cleanup_loop.domintros 
            simp add: cleanup_loop_ret_cond_def)
    next
      case False
      hence call_cond:"cleanup_loop_call_cond (\<pi>, M, \<OO>)"
        by(auto simp add: cleanup_loop_call_cond_def cleanup_loop_ret_cond_def)
      show ?thesis 
      proof(rule cleanup_loop.domintros, rule forw_subst[of _ "cleanup_loop_upd (\<pi>, M, \<OO>)"], goal_cases)
        case (1 Bls)
        then show ?case
          by(auto simp add: cleanup_loop_upd_def Let_def)
      next
        case (2 Bls)
        show ?case 
        proof(cases "cleanup_loop_upd (\<pi>, M, \<OO>)")
          case (fields \<pi>' M' \<OO>')
          moreover note cleanup_loop_upd_pres = cleanup_loop_upd_pres[OF call_cond less(3-)]
          ultimately show ?thesis 
            by(auto intro!: less(1)[of "card \<OO>'", OF _ refl] 
                simp add: less(2))
        qed
      qed
    qed
  qed
qed

lemma cleanup_loop_upd_correct:
  assumes "odds_invar_cleanup (\<pi>, M, \<OO>)"
    "odd_factor_critical_invar_cleanup (\<pi>, M, \<OO>)" 
    "invar_matching_delta_of_non_zero_sets_cleanup (\<pi>, M, \<OO>)"
    "invar_strict_odd_pos_cleanup (\<pi>, M, \<OO>)"
    "invar_feasible_pi_cleanup (\<pi>, M, \<OO>)" 
    "invar_tight_matching_cleanup (\<pi>, M, \<OO>)"
    "cleanup_loop (\<pi>, M, \<OO>) = (\<pi>', M')"
  shows "perfect_matching G M'" (is ?th1)
    "feasible_min_perfect_dual_edmonds G w \<pi>'" (is ?th2)
    "\<And>U. \<lbrakk>U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 Vs G; \<pi>' U \<noteq> 0\<rbrakk> \<Longrightarrow> card (Delta M' U) = 1" 
    "M' \<subseteq> odd_tight_subgraph G w \<pi>'" (is ?th4)
proof-
  have "perfect_matching G M' \<and> feasible_min_perfect_dual_edmonds G w \<pi>'
      \<and> (\<forall> U. (U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 Vs G \<and> \<pi>' U \<noteq> 0) \<longrightarrow> card (Delta M' U) = 1) \<and>
          M' \<subseteq> odd_tight_subgraph G w \<pi>'"
    using assms
  proof(induction arbitrary: 
      rule: cleanup_loop_induct[OF cleanup_loop_upd_termination, OF assms(1-6)], goal_cases)
    case (1 \<pi> M \<OO>)
    note IH = this
    show ?case 
      using  cleanup_loop_upd_pres[OF IH(2,4-9)] IH(1,10,2) 
      by(intro IH(3)) 
        (auto simp add: cleanup_loop_simps(1))
  next
    case (2 \<pi> M \<OO>)
    note base = this
    hence ret_is: "cleanup_loop_ret (\<pi>, M, \<OO>) = (\<pi>', M')"
      by(auto simp add: cleanup_loop_simps(2))
    show ?case
      using cleanup_loop_upd_return[OF base(2,3,5,7,8) ret_is]
      by auto
  qed
  thus ?th1 ?th2 ?th4
    "\<And>U. \<lbrakk>U \<in> \<Omega>\<^sub>\<ge>\<^sub>3 Vs G; \<pi>' U \<noteq> 0\<rbrakk> \<Longrightarrow> card (Delta M' U) = 1" 
    by auto
qed

definition "\<pi>\<^sub>0 = (\<lambda> X. if \<exists> x \<in> Vs G. X = {x} 
                       then let x = (SOME x. x \<in> Vs G \<and> X = {x})
                            in 1/2 * Min {w e | e. e \<in> Delta G {x}}
                       else 0)"

lemma pi0_leq_half_of_edge_weight:
  assumes "u \<in> Vs G" "u \<noteq> v" "{u,v} \<in> G"
  shows "\<pi>\<^sub>0 {u} \<le> 1/2 * w {u, v}"
proof-
  have SOME_is:"(SOME x. x \<in> Vs G \<and> u = x) = u"
    using assms by auto
  have uv_in_Delta:"{u, v} \<in> Delta G {u}"
    using assms(2,3)
    by(auto intro: in_DeltaI)
  show ?thesis
    using assms finite_E uv_in_Delta
    by(auto intro!:  exI[of _ "{u, v}"] linorder_class.Min.coboundedI finite_img Delta_finite 
        simp add: \<pi>\<^sub>0_def  SOME_is)
qed

lemma initial_pi_feasible:
  "feasible_min_perfect_dual_edmonds G w \<pi>\<^sub>0"
proof(rule feasible_min_perfect_dual_edmondsI, goal_cases)
  case (1 e)
  then obtain u v where uv: "e = {u, v}" "u \<noteq> v"
    by auto
  have "sum \<pi>\<^sub>0 (end_sets_strict G {u, v}) = 0"
  proof(rule comm_monoid_add_class.sum.neutral, rule ballI, goal_cases)
    case (1 X)
    then show ?case 
      by(auto elim!: in_end_sets_strictE in_odd_subsets_strictE simp add: \<pi>\<^sub>0_def)
  qed
  moreover have "\<pi>\<^sub>0 {u} + \<pi>\<^sub>0 {v} \<le> w e"
    using uv pi0_leq_half_of_edge_weight[of u v] 1 pi0_leq_half_of_edge_weight[of v u]
    by(auto simp add: insert_commute edges_are_Vs edges_are_Vs_2)
  ultimately show ?case 
    using 1 uv finite_Vs
    by(auto simp add: sum_potential_end_sets_split_off_eps)
next
  case (2 U)
  thus ?case
    by(auto elim: in_odd_subsets_strictE simp add: \<pi>\<^sub>0_def)
qed

definition "\<OO>\<^sub>0 = {{v}| v. v \<in> Vs G}"

subsection \<open>Initial State\<close>

lemma initial_invars:
  "odds_invar (\<pi>\<^sub>0, \<OO>\<^sub>0)" (is ?th1)
  "odd_factor_critical_invar (\<pi>\<^sub>0, \<OO>\<^sub>0)" (is ?th2)
  "invar_strict_odd_pos (\<pi>\<^sub>0, \<OO>\<^sub>0)" (is ?th3)
  "invar_non_zero_pi_in_odd (\<pi>\<^sub>0, \<OO>\<^sub>0)" (is ?th4)
  "invar_feasible_pi (\<pi>\<^sub>0, \<OO>\<^sub>0)" (is ?th5)
proof-
  show ?th1
    by(auto intro!: odds_invarI laminarI simp add: \<OO>\<^sub>0_def)
  show ?th2
    by(auto intro!: odd_factor_critical_invarI simp add: \<OO>\<^sub>0_def)
  show ?th3
    by(auto intro!: invar_strict_odd_posI simp add: \<OO>\<^sub>0_def)
  show ?th4
    by(auto intro!: invar_non_zero_pi_in_oddI 
        simp add: \<pi>\<^sub>0_def if_split[of "\<lambda> x. x \<noteq> _"] \<OO>\<^sub>0_def)
  show ?th5
    by(auto intro!: invar_feasible_piI initial_pi_feasible)
qed

subsection \<open>Correctness\<close>

text \<open>Unfortunately, we can give a partial correctness statement only.
     We took an abstract perspective at the algorithm,
     but this comes at the cost of losing nice termination proofs.
     We experienced something similar but less severe for weighted bipartite matching:
     for the abstract algorithm we could guarantee termination only if all weights are multiples 
     of the same real constant,
     whereas for the implementation, a.k.a. the Hungarian Method, we had strongly polynomial time.
  \<close>

definition "naive_min_weight_perfect_matching =
  (let intermed = top_loop (\<pi>\<^sub>0, \<OO>\<^sub>0)
   in case intermed of None \<Rightarrow> None
     | Some (\<pi>, M, \<OO>) \<Rightarrow>
        let (\<pi>', M')  = cleanup_loop (\<pi>, M, \<OO>)
         in Some M')"

theorem naive_min_weight_perfect_matching_partial_correctness:
  assumes "top_loop_dom (\<pi>\<^sub>0, \<OO>\<^sub>0)"
  shows "naive_min_weight_perfect_matching = None 
          \<Longrightarrow> \<nexists> M. perfect_matching G M"
    "naive_min_weight_perfect_matching = Some M 
          \<Longrightarrow> min_weight_perfect_matching G w M"
proof(goal_cases)
  case 1
  hence top_loop_None:"top_loop (\<pi>\<^sub>0, \<OO>\<^sub>0) = None"
    using top_loop.cases[of "cleanup_loop (_, _, _)"]
    by(cases "top_loop (\<pi>\<^sub>0, \<OO>\<^sub>0)")
      (auto simp add: naive_min_weight_perfect_matching_def prod.split[of "\<lambda> x. x = None"], blast)
  show ?case 
  proof(rule ccontr, goal_cases)
    case 1
    then obtain M where M: "perfect_matching G M"
      by auto
    define B where "B = sum w M"
    obtain \<pi> where pi: "feasible_min_perfect_dual_edmonds G w \<pi>" "B < sum \<pi> \<Omega> Vs G"
      using top_loop_None_dual_unbounded[OF assms initial_invars top_loop_None]
      by auto
    moreover have "sum \<pi> \<Omega> Vs G \<le> B"
      by(auto intro!: edmonds_weak_duality 
          simp add: B_def pi(1) M dblton_E finite_Vs)
    ultimately show False
      by simp
  qed
next
  case 2
  then obtain \<pi> M' \<OO> \<pi>'' where results: "top_loop (\<pi>\<^sub>0, \<OO>\<^sub>0) = Some (\<pi>, M', \<OO>)"
    "cleanup_loop (\<pi>, M', \<OO>) = (\<pi>'', M)"
    by(cases "top_loop (\<pi>\<^sub>0, \<OO>\<^sub>0)")
      (auto simp add: naive_min_weight_perfect_matching_def case_prod_beta' split_pairs2)

  note invars_for_second_loop = invars_for_second_loopD[OF 
      top_loop_Some_result[OF assms(1) initial_invars results(1)]]

  note final_correctness_conditions = 
    cleanup_loop_upd_correct[OF invars_for_second_loop results(2)]

  show ?case
    by(auto intro!: edmonds_min_weight_perfect_matching_criterion[where \<pi> = \<pi>'']
        final_correctness_conditions graph)
qed

end
end