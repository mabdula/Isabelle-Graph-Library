theory Init_Potential_Imperative
  imports
    Init_Potential_Collection
    Data_Structures.Fixed_Univ_Map_Specs_Imp
    Data_Structures.Fixed_Univ_Set_Iterate_Imp
    Directed_Set_Graphs.Weighted_Neighbourhoods_Imperative_Spec
    Data_Structures.Real_Embedding
begin

provenance ai


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

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) scan_min_imp :: "'ci \<Rightarrow> 'pi \<Rightarrow> 'v \<Rightarrow> unit Heap" where
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
      and set_assn = vset_assn and lst = lst and is_it = left_is_it
      and it_init = left_it_init and it_has_next = left_it_has_next and it_next = left_it_next
  for cost :: "'v::heap \<Rightarrow> 'v \<Rightarrow> real" and vset_to_set :: "'vset \<Rightarrow> 'v set"
    and h :: "'n::{linordered_idom, heap} \<Rightarrow> real"
    and nb_init nb_assn has_imp current_imp current_cost_imp move_imp reset_imp reset_all_imp
    and pot_assn pot_upd_imp pot_get_imp
    and vset_assn
    and left_is_it left_it_init left_it_has_next left_it_next

sublocale init_potential_imp \<subseteq> code: init_potential_imp_code
  has_imp current_cost_imp move_imp reset_imp pot_get_imp pot_upd_imp
  left_it_init left_it_has_next left_it_next .

context init_potential_imp
begin

lemma \<^marker>\<open>provenance ai_human\<close> pot_get_rule:
  "\<lbrakk>potential_invar \<pi>; u \<in> K\<rbrakk> \<Longrightarrow>
     <pot_assn \<pi> Pti> pot_get_imp Pti u <\<lambda>r. pot_assn \<pi> Pti * \<up>(potential_get \<pi> u = h r)>"
  using pot.fixed_univ_map_lookup_rule[of \<pi> u Pti]
  by (simp add: eq_commute)

lemma \<^marker>\<open>provenance ai_human\<close> upd_min_imp_rule:
  assumes "potential_invar \<pi>" "u \<in> K"
  shows "<pot_assn \<pi> Pti> code.upd_min_imp Pti u c <\<lambda>_. pot_assn (upd_min u (h c) \<pi>) Pti>"
  unfolding code.upd_min_imp_def
  supply pot.fixed_univ_map_lookup_rule[sep_heap_rules del]
  using assms
  by (sep_auto heap: pot_get_rule[OF assms] simp: upd_min_def)

lemma upd_min_invar: "\<lbrakk>potential_invar \<pi>; u \<in> K\<rbrakk> \<Longrightarrow> potential_invar (upd_min u c \<pi>)"
  by (auto simp: upd_min_def pot.fixed_univ_map_upd_invar)

lemma rnb_move_props:
  assumes "rnb_invar C" "u \<in> K" "rnb_has C u" "finite (rnb_remaining C u)"
  shows "rnb_remaining C u \<noteq> {}" "rnb_invar (rnb_move C u)" "finite (rnb_remaining (rnb_move C u) u)"
        "card (rnb_remaining (rnb_move C u) u) < card (rnb_remaining C u)"
  using assms rnb.idx_current[of C u] card_Diff1_less[of "rnb_remaining C u" "rnb_current C u"]
  by (simp_all add: rnb.idx_has rnb.idx_move_invar rnb.idx_move_remaining)

lemma rnb_reset_props:
  assumes "rnb_invar C" "u \<in> K" "rnb_abstract C = rnb_abstract C0" "finite (rnb_abstract C0 u)"
  shows "rnb_invar (rnb_reset C u)" "finite (rnb_remaining (rnb_reset C u) u)"
  using assms rnb.idx_reset_invar[of C u] rnb.idx_reset_remaining[of C u]
  by auto

lemma init_step_split:
  "init_step (C, \<pi>) u =
     (if rnb_has (rnb_reset C u) u
      then scan_min u (rnb_move (rnb_reset C u) u) (potential_upd \<pi> u (cost u (rnb_current (rnb_reset C u) u)))
      else (rnb_reset C u, \<pi>))"
  by (simp add: init_step_def Let_def)

lemma \<^marker>\<open>provenance ai_human\<close> scan_min_imp_rule:
  assumes "rnb_invar C" "u \<in> K" "finite (rnb_remaining C u)" "potential_invar \<pi>"
  shows "<nb_assn C Ci * pot_assn \<pi> Pti> code.scan_min_imp Ci Pti u
         <\<lambda>_. nb_assn (fst (scan_min u C \<pi>)) Ci * pot_assn (snd (scan_min u C \<pi>)) Pti>"
  using assms
proof(induction "card (rnb_remaining C u)" arbitrary: C \<pi> rule: less_induct)
  case less
  show ?case
  proof(cases "rnb_has C u")
    case True
    note M = rnb_move_props[OF less.prems(1,2) True less.prems(3)]
    note IH = less.hyps[OF M(4,2) less.prems(2) M(3) upd_min_invar[OF less.prems(4,2)]]
    show ?thesis
      apply(subst code.scan_min_imp.simps)
      apply(sep_auto heap: nb.idx_has_rule nb.current_cost_rule nb.idx_move_rule
                     simp: less.prems(1,2) True M(1))
      apply(sep_auto heap: upd_min_imp_rule[OF less.prems(4,2)])
      by (sep_auto heap: IH simp: scan_min.simps[of u C \<pi>] True)
  next
    case False
    show ?thesis
      apply(subst code.scan_min_imp.simps)
      by (sep_auto heap: nb.idx_has_rule simp: less.prems(1,2) False scan_min.simps[of u C \<pi>])
  qed
qed

lemma \<^marker>\<open>provenance ai_human\<close> init_pot_step_rule:
  assumes "rnb_invar C" "rnb_abstract C = rnb_abstract C0" "u \<in> K"
          "finite (rnb_abstract C0 u)" "potential_invar \<pi>"
  shows "<nb_assn C Ci * pot_assn \<pi> Pti> code.init_pot_step Ci Pti u x
         <\<lambda>_. nb_assn (fst (init_step (C, \<pi>) u)) Ci * pot_assn (snd (init_step (C, \<pi>) u)) Pti>"
proof(cases "rnb_has (rnb_reset C u) u")
  case True
  note R = rnb_reset_props[OF assms(1,3,2,4)]
  note M = rnb_move_props[OF R(1) assms(3) True R(2)]
  note sc = scan_min_imp_rule[OF M(2) assms(3) M(3) pot.fixed_univ_map_upd_invar[OF assms(5,3)]]
  show ?thesis
    unfolding code.init_pot_step_def
    by (sep_auto heap: nb.idx_reset_rule nb.idx_has_rule nb.current_cost_rule nb.idx_move_rule sc
                 simp: assms(1,3,5) R(1) True M(1) init_step_split)
next
  case False
  show ?thesis
    unfolding code.init_pot_step_def
    using rnb_reset_props[OF assms(1,3,2,4)]
    by (sep_auto heap: nb.idx_reset_rule nb.idx_has_rule simp: assms(1,3) False init_step_split)
qed

definition "init_pre C0 u Cp =
  (u \<in> K \<and> finite (rnb_abstract C0 u) \<and> rnb_invar (fst Cp) \<and>
   rnb_abstract (fst Cp) = rnb_abstract C0 \<and> potential_invar (snd Cp))"

lemma \<^marker>\<open>provenance ai_human\<close> init_pot_step_pre_rule:
  "init_pre C0 u Cp \<Longrightarrow>
     <nb_assn (fst Cp) Ci * pot_assn (snd Cp) Pti> code.init_pot_step Ci Pti u x
     <\<lambda>_. nb_assn (fst (init_step Cp u)) Ci * pot_assn (snd (init_step Cp u)) Pti>"
  by (cases Cp) (simp add: init_pre_def init_pot_step_rule)

lemma init_inv_pre:
  "\<lbrakk>init_inv C0 pot0 S Cp; u \<in> K; finite (rnb_abstract C0 u)\<rbrakk> \<Longrightarrow> init_pre C0 u Cp"
  by (simp add: init_pre_def init_inv_def)

lemma init_fold_pre_imp:
  "\<lbrakk>init_inv C0 pot0 S Cp; set xs \<subseteq> K; \<forall>u\<in>set xs. finite (rnb_abstract C0 u)\<rbrakk> \<Longrightarrow>
   fold_pre (init_pre C0) init_step Cp xs"
proof(induction xs arbitrary: S Cp)
  case (Cons x xs)
  thus ?case
    using Cons.IH[of "insert x S" "init_step Cp x"] init_step_inv[of C0 pot0 S Cp x]
    by (simp add: init_inv_pre)
qed simp

lemma init_fold_pre_start:
  assumes "rnb_invar C0" "vset_invar left" "finite (vset_to_set left)"
          "\<And>u. u \<in> vset_to_set left \<Longrightarrow> finite (rnb_abstract C0 u)"
  shows "fold_pre (init_pre C0) init_step (C0, potential_empty) (lst (vset_to_set left))"
  using init_fold_pre_imp[of C0 potential_empty "{}" "(C0, potential_empty)"] assms
        left.fixed_univ_set_universe[of left] lst_set[of "vset_to_set left"] potential_empty
  by (auto simp: init_inv_def)

lemma init_potential_coll_lst:
  "vset_invar left \<Longrightarrow>
     init_potential_coll C0 potential_empty left = foldl init_step (C0, potential_empty) (lst (vset_to_set left))"
  by (simp add: init_potential_coll_def vset_iterate_lst)

lemma \<^marker>\<open>provenance ai_human\<close> init_pot_imp_rule:
  assumes "rnb_invar C0" "vset_invar left" "finite (vset_to_set left)"
          "\<And>u. u \<in> vset_to_set left \<Longrightarrow> finite (rnb_abstract C0 u)"
  shows "<nb_assn C0 Ci * pot_assn potential_empty Pti * vset_assn left Li>
         code.init_pot_imp Ci Li Pti
         <\<lambda>_. nb_assn (fst (init_potential_coll C0 potential_empty left)) Ci *
              pot_assn (snd (init_potential_coll C0 potential_empty left)) Pti *
              vset_assn left Li>"
proof-
  note fold = iter_fold_rule_gen[where I = "\<lambda>xs it. vset_assn left Li * left_is_it (vset_to_set left) Li xs it"
      and Q = "vset_assn left Li" and A = "\<lambda>Cp (x::unit). nb_assn (fst Cp) Ci * pot_assn (snd Cp) Pti",
      OF left.it_has_next_rule left.it_next_rule left.quit_iteration init_pot_step_pre_rule
         init_fold_pre_start[OF assms]]
  show ?thesis
    unfolding code.init_pot_imp_def init_potential_coll_lst[OF assms(2)]
    by (sep_auto heap: left.it_init_rule fold[simplified] simp: assms(2))
qed

end

end

