theory Init_Potential_Imperative
  imports
    Init_Potential_Collection
    Data_Structures.Fixed_Univ_Map_Specs_Imp
    Data_Structures.Fixed_Univ_Set_Iterate_Imp
    Directed_Set_Graphs.Weighted_Neighbourhoods_Imperative_Spec
    Data_Structures.Real_Embedding
begin

section \<open>Imperative Computation of the Initial Potential\<close>

text \<open>The imperative counterpart of @{locale init_potential_coll}. The weights are read at the
      cursor of the collection. The potential is an imperative fixed-universe map that is updated
      in place, the left vertices an imperative fixed-universe set iterated in the order
      @{term lst}. The program does not allocate: the potential handle is passed in, and
      represents the empty potential.\<close>

locale init_potential_imp_code =
  fixes has_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and current_cost_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> 'n::linordered_idom Heap"
    and move_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and reset_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and pot_get_imp :: "'pi \<Rightarrow> 'v \<Rightarrow> 'n Heap"
    and pot_upd_imp :: "'pi \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and left_it_init :: "'li \<Rightarrow> 'lit Heap"
    and left_it_has_next :: "'lit \<Rightarrow> bool Heap"
    and left_it_next :: "'lit \<Rightarrow> ('v \<times> 'lit) Heap"
begin

definition "upd_min_imp Pti u c = do {
   r \<leftarrow> pot_get_imp Pti u;
   (if r \<le> c then return () else pot_upd_imp Pti u c) }"

partial_function (heap) scan_min_imp :: "'ci \<Rightarrow> 'pi \<Rightarrow> 'v \<Rightarrow> unit Heap" where
  "scan_min_imp Ci Pti u = do {
     b \<leftarrow> has_imp Ci u;
     (if b then do { c \<leftarrow> current_cost_imp Ci u;
                     move_imp Ci u;
                     upd_min_imp Pti u c;
                     scan_min_imp Ci Pti u }
      else return ()) }"

text \<open>The first neighbour sets the value of @{term u}, the others can only decrease it.\<close>

definition "init_pot_step Ci Pti u (x::unit) = do {
   reset_imp Ci u;
   b \<leftarrow> has_imp Ci u;
   (if b then do { c \<leftarrow> current_cost_imp Ci u;
                   move_imp Ci u;
                   pot_upd_imp Pti u c;
                   scan_min_imp Ci Pti u }
    else return ()) }"

definition "init_pot_imp Ci Li Pti = do {
   it \<leftarrow> left_it_init Li;
   iter_fold left_it_has_next left_it_next (init_pot_step Ci Pti) it () }"

end

locale init_potential_imp =
  init_potential_coll where cost = cost and vset_to_set = vset_to_set +
  real_embedding h +
  nb: weighted_neighbourhoods_imp_spec
    where idx_invar = rnb_invar and idx_abstract = rnb_abstract and idx_current = rnb_current
      and idx_has = rnb_has and idx_iterated = rnb_iterated and idx_remaining = rnb_remaining
      and idx_move = rnb_move and idx_reset = rnb_reset and K = K
      and cost = cost and wval = h and nb_init = nb_init and nb_assn = nb_assn
      and has_imp = has_imp and current_imp = current_imp and current_cost_imp = current_cost_imp
      and move_imp = move_imp and reset_imp = reset_imp and reset_all_imp = reset_all_imp +
  pot: fixed_univ_map_imp
    where K = K and fixed_univ_map_invar = potential_invar
      and fixed_univ_map_upd = potential_upd and fixed_univ_map_lookup = potential_get
      and fixed_univ_map_val = h and fixed_univ_map_assn = pot_assn
      and fixed_univ_map_upd_imp = pot_upd_imp and fixed_univ_map_lookup_imp = pot_get_imp +
  left: fixed_univ_set_iterate_imp
    where U = K and set_invar = vset_invar and set_abstract = vset_to_set
      and set_empty = vset_empty and set_insert = vset_insert and set_delete = vset_delete
      and set_isin = vset_isin and set_assn = vset_assn and set_empty_imp = vset_empty_imp
      and set_insert_imp = vset_insert_imp and set_delete_imp = vset_delete_imp
      and set_isin_imp = vset_isin_imp and lst = lst and is_it = left_is_it
      and it_init = left_it_init and it_has_next = left_it_has_next and it_next = left_it_next
  for cost :: "'v::heap \<Rightarrow> 'v \<Rightarrow> real" and vset_to_set :: "'vset \<Rightarrow> 'v set"
    and h :: "'n::{linordered_idom, heap} \<Rightarrow> real"
    and nb_init nb_assn has_imp current_imp current_cost_imp move_imp reset_imp reset_all_imp
    and pot_assn pot_upd_imp pot_get_imp
    and vset_empty vset_insert vset_delete vset_isin
    and vset_assn vset_empty_imp vset_insert_imp vset_delete_imp vset_isin_imp
    and left_is_it left_it_init left_it_has_next left_it_next

sublocale init_potential_imp \<subseteq> code: init_potential_imp_code
  has_imp current_cost_imp move_imp reset_imp pot_get_imp pot_upd_imp
  left_it_init left_it_has_next left_it_next .

context init_potential_imp
begin

lemma upd_min_imp_rule:
  assumes "potential_invar \<pi>" "u \<in> K"
  shows "<pot_assn \<pi> Pti> code.upd_min_imp Pti u c <\<lambda>_. pot_assn (upd_min u (h c) \<pi>) Pti>"
proof-
  have get: "<pot_assn \<pi> Pti> pot_get_imp Pti u
             <\<lambda>r. pot_assn \<pi> Pti * \<up>(potential_get \<pi> u = h r)>"
    using pot.fixed_univ_map_lookup_rule[OF assms] by (simp add: eq_commute)
  show ?thesis
    unfolding code.upd_min_imp_def
    supply pot.fixed_univ_map_lookup_rule[sep_heap_rules del]
    using assms by (sep_auto heap: get simp: upd_min_def)
qed

lemma upd_min_invar: "\<lbrakk>potential_invar \<pi>; u \<in> K\<rbrakk> \<Longrightarrow> potential_invar (upd_min u c \<pi>)"
  by (auto simp: upd_min_def pot.fixed_univ_map_upd_invar)

lemma scan_min_imp_rule:
  assumes "rnb_invar C" "u \<in> K" "finite (rnb_remaining C u)" "potential_invar \<pi>"
  shows "<nb_assn C Ci * pot_assn \<pi> Pti> code.scan_min_imp Ci Pti u
         <\<lambda>_. nb_assn (fst (scan_min u C \<pi>)) Ci * pot_assn (snd (scan_min u C \<pi>)) Pti>"
  using assms
proof(induction "card (rnb_remaining C u)" arbitrary: C \<pi> rule: less_induct)
  case less
  show ?case
  proof(cases "rnb_has C u")
    case True
    have ne: "rnb_remaining C u \<noteq> {}" using rnb.idx_has[OF less.prems(1,2)] True by simp
    have x_in: "rnb_current C u \<in> rnb_remaining C u"
      using rnb.idx_current[OF less.prems(1,2) ne] .
    have C': "rnb_invar (rnb_move C u)"
             "rnb_remaining (rnb_move C u) u = rnb_remaining C u - {rnb_current C u}"
      using rnb.idx_move_invar[OF less.prems(1,2)] rnb.idx_move_remaining[OF less.prems(1,2) ne]
      by auto
    have card_less: "card (rnb_remaining (rnb_move C u) u) < card (rnb_remaining C u)"
      using card_Diff1_less[OF less.prems(3) x_in] by (simp add: C'(2))
    have fin': "finite (rnb_remaining (rnb_move C u) u)" using less.prems(3) by (simp add: C'(2))
    have eq: "scan_min u C \<pi> = scan_min u (rnb_move C u) (upd_min u (cost u (rnb_current C u)) \<pi>)"
      by (simp add: scan_min.simps[of u C \<pi>] True)
    note IH = less.hyps[OF card_less C'(1) less.prems(2) fin' upd_min_invar[OF less.prems(4,2)]]
    note um = upd_min_imp_rule[OF less.prems(4,2)]
    show ?thesis
      apply(subst code.scan_min_imp.simps)
      apply(sep_auto heap: nb.idx_has_rule nb.current_cost_rule nb.idx_move_rule
                     simp: less.prems(1,2) True ne)
      apply(sep_auto heap: um)
      by (sep_auto heap: IH simp: eq True)
  next
    case False
    have eq: "scan_min u C \<pi> = (C, \<pi>)" by (simp add: scan_min.simps[of u C \<pi>] False)
    show ?thesis
      apply(subst code.scan_min_imp.simps)
      by (sep_auto heap: nb.idx_has_rule simp: less.prems(1,2) False eq)
  qed
qed

lemma init_pot_step_rule:
  assumes "rnb_invar C" "rnb_abstract C = rnb_abstract C0" "u \<in> K"
          "finite (rnb_abstract C0 u)" "potential_invar \<pi>"
  shows "<nb_assn C Ci * pot_assn \<pi> Pti> code.init_pot_step Ci Pti u x
         <\<lambda>_. nb_assn (fst (init_step (C, \<pi>) u)) Ci * pot_assn (snd (init_step (C, \<pi>) u)) Pti>"
proof-
  define C1 where "C1 = rnb_reset C u"
  have C1: "rnb_invar C1" "finite (rnb_remaining C1 u)"
    using rnb.idx_reset_invar[OF assms(1,3)] rnb.idx_reset_remaining[OF assms(1,3)] assms(2,4)
    by (auto simp: C1_def)
  show ?thesis
  proof(cases "rnb_has C1 u")
    case True
    have ne: "rnb_remaining C1 u \<noteq> {}" using rnb.idx_has[OF C1(1) assms(3)] True by simp
    have C2: "rnb_invar (rnb_move C1 u)" "finite (rnb_remaining (rnb_move C1 u) u)"
      using rnb.idx_move_invar[OF C1(1) assms(3)] rnb.idx_move_remaining[OF C1(1) assms(3) ne]
            C1(2)
      by auto
    have pinv: "potential_invar (potential_upd \<pi> u c)" for c
      using pot.fixed_univ_map_upd_invar[OF assms(5,3)] .
    note sc = scan_min_imp_rule[OF C2(1) assms(3) C2(2) pinv]
    have eq: "init_step (C, \<pi>) u =
              scan_min u (rnb_move C1 u) (potential_upd \<pi> u (cost u (rnb_current C1 u)))"
      by (simp add: init_step_def Let_def C1_def[symmetric] True)
    show ?thesis
      unfolding code.init_pot_step_def
      by (sep_auto heap: nb.idx_reset_rule nb.idx_has_rule nb.current_cost_rule nb.idx_move_rule sc
                   simp: assms(1,3,5) C1_def[symmetric] C1(1) True ne eq)
  next
    case False
    have eq: "init_step (C, \<pi>) u = (C1, \<pi>)"
      by (simp add: init_step_def Let_def C1_def[symmetric] False)
    show ?thesis
      unfolding code.init_pot_step_def
      by (sep_auto heap: nb.idx_reset_rule nb.idx_has_rule
                   simp: assms(1,3) C1_def[symmetric] C1(1) False eq)
  qed
qed

definition "init_pre C0 u Cp =
  (u \<in> K \<and> finite (rnb_abstract C0 u) \<and> rnb_invar (fst Cp) \<and>
   rnb_abstract (fst Cp) = rnb_abstract C0 \<and> potential_invar (snd Cp))"

lemma init_fold_pre_imp:
  "\<lbrakk>init_inv C0 pot0 S Cp; set xs \<subseteq> K; \<forall>u\<in>set xs. finite (rnb_abstract C0 u)\<rbrakk> \<Longrightarrow>
   fold_pre (init_pre C0) init_step Cp xs"
proof(induction xs arbitrary: S Cp)
  case (Cons x xs)
  have "init_inv C0 pot0 (insert x S) (init_step Cp x)"
    using init_step_inv[OF Cons.prems(1)] Cons.prems(2,3) by simp
  hence "fold_pre (init_pre C0) init_step (init_step Cp x) xs"
    using Cons.IH Cons.prems(2,3) by simp
  moreover have "init_pre C0 x Cp"
    using Cons.prems by (auto simp: init_pre_def init_inv_def)
  ultimately show ?case by simp
qed simp

theorem init_pot_imp_rule:
  assumes "rnb_invar C0" "vset_invar left" "finite (vset_to_set left)"
          "\<And>u. u \<in> vset_to_set left \<Longrightarrow> finite (rnb_abstract C0 u)"
  shows "<nb_assn C0 Ci * pot_assn potential_empty Pti * vset_assn left Li>
         code.init_pot_imp Ci Li Pti
         <\<lambda>_. nb_assn (fst (init_potential_coll C0 potential_empty left)) Ci *
              pot_assn (snd (init_potential_coll C0 potential_empty left)) Pti *
              vset_assn left Li>"
proof-
  have sub: "vset_to_set left \<subseteq> K" using left.fixed_univ_set_universe[OF assms(2)] .
  have i0: "init_inv C0 potential_empty {} (C0, potential_empty)"
    using assms(1) potential_empty by (auto simp: init_inv_def)
  have res: "init_potential_coll C0 potential_empty left =
             foldl init_step (C0, potential_empty) (lst (vset_to_set left))"
    by (simp add: init_potential_coll_def vset_iterate_lst[OF assms(2)])
  have pre: "fold_pre (init_pre C0) init_step (C0, potential_empty) (lst (vset_to_set left))"
    using init_fold_pre_imp[OF i0] sub assms(4) lst_set[OF assms(3)] by auto
  have step: "\<And>u Cp x. init_pre C0 u Cp \<Longrightarrow>
     <nb_assn (fst Cp) Ci * pot_assn (snd Cp) Pti> code.init_pot_step Ci Pti u x
     <\<lambda>_. nb_assn (fst (init_step Cp u)) Ci * pot_assn (snd (init_step Cp u)) Pti>"
  proof-
    fix u Cp x assume a: "init_pre C0 u Cp"
    obtain C \<pi> where Cp: "Cp = (C, \<pi>)" by (cases Cp) auto
    show "<nb_assn (fst Cp) Ci * pot_assn (snd Cp) Pti> code.init_pot_step Ci Pti u x
     <\<lambda>_. nb_assn (fst (init_step Cp u)) Ci * pot_assn (snd (init_step Cp u)) Pti>"
      using a init_pot_step_rule[of C C0 u \<pi> Ci Pti x] by (simp add: init_pre_def Cp)
  qed
  note fold = iter_fold_rule_gen[where I = "left_is_it left Li" and Q = "vset_assn left Li"
      and A = "\<lambda>Cp (x::unit). nb_assn (fst Cp) Ci * pot_assn (snd Cp) Pti",
      OF left.it_has_next_rule left.it_next_rule left.quit_iteration step pre]
  show ?thesis
    unfolding code.init_pot_imp_def res
    by (sep_auto heap: left.it_init_rule fold[simplified] simp: assms(2))
qed

end

end

