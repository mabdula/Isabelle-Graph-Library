(*
  Author: Adem Rimpapa
  Author: Thomas Ammer
*)

theory BestInGreedy_exec
  imports BestInGreedy_base
begin

provenance human

section \<open>The Best-In-Greedy Algorithm with a Weak Independence Oracle\<close>

locale BestInGreedy_exec = 
  BestInGreedy_base where set_empty = "set_empty::'s" and set_insert= "set_insert::('a::linorder) \<Rightarrow> 's \<Rightarrow> 's"
for set_empty set_insert  +
fixes local_indep_oracle::"'a \<Rightarrow> 'wrps \<Rightarrow> bool"
  and   remove_wrapper::"'wrps \<Rightarrow> 's"
  and  wrapper_invar::"'wrps \<Rightarrow> bool"
  and wrapper_insert::"'a::linorder \<Rightarrow> 'wrps \<Rightarrow> 'wrps"
  and wrapper_empty::"'wrps"
assumes wrapper_axioms:
  "\<And> S x. wrapper_invar S \<Longrightarrow> x \<in> to_set carrier \<Longrightarrow> indep_fn (set_insert x (remove_wrapper S))
     \<Longrightarrow> wrapper_invar (wrapper_insert x S)"
  "\<And> S. wrapper_invar S \<Longrightarrow> set_inv (remove_wrapper S)"
  "\<And> S x. wrapper_invar S \<Longrightarrow> remove_wrapper (wrapper_insert x S) = set_insert x (remove_wrapper S)"
  "set_empty = remove_wrapper wrapper_empty"
  "wrapper_invar wrapper_empty"
begin

definition "to_ordinary (state::('a, 'wrps) best_in_greedy_state) = \<lparr>carrier_list = carrier_list state, result = remove_wrapper (result state) \<rparr>"

partial_function (tailrec) BestInGreedy_exec :: 
  "('a, 'wrps) best_in_greedy_state \<Rightarrow> ('a, 'wrps) best_in_greedy_state" where
  "BestInGreedy_exec best_in_greedy_state = 
    (case (carrier_list best_in_greedy_state) of
      [] \<Rightarrow> best_in_greedy_state
    | (x # xs) \<Rightarrow> 
        (if local_indep_oracle x (result best_in_greedy_state) then
          let
            new_result = (wrapper_insert x (result best_in_greedy_state))
          in
            BestInGreedy_exec (best_in_greedy_state \<lparr>carrier_list := xs, result := new_result\<rparr>)
        else
          BestInGreedy_exec (best_in_greedy_state \<lparr>carrier_list := xs\<rparr>)
        )
    )"

definition "BestInGreedy_exec_upd1 (best_in_greedy_state::('a, 'wrps) best_in_greedy_state) = (
  let
    x = hd (carrier_list best_in_greedy_state);
    xs = tl (carrier_list best_in_greedy_state);
    new_result = (wrapper_insert x (result best_in_greedy_state))
  in
    best_in_greedy_state \<lparr>carrier_list := xs, result := new_result\<rparr>
  )"

definition "initial_state' c order = \<lparr>carrier_list = (sort_desc c order), result = wrapper_empty\<rparr>"


lemmas [code] = initial_state'_def BestInGreedy_exec.simps
context 
  assumes local_indep_oracle:
    "\<And> S x. wrapper_invar S \<Longrightarrow> indep' (remove_wrapper S) \<Longrightarrow> subseteq (remove_wrapper S) carrier \<Longrightarrow>
         \<not> x \<in> to_set (remove_wrapper S) \<Longrightarrow> x \<in> to_set carrier
    \<Longrightarrow> (local_indep_oracle x S
 \<longleftrightarrow> indep' (set_insert x (remove_wrapper S)))"
    and carrier_inv: "set_inv carrier"
begin

lemma BestInGreedy_exec_corresp_general:
  assumes 
    "BestInGreedy_base_dom state'" 
    "indep' (result state')" "wrapper_invar  (result state)" 
    "subseteq (result state') carrier"
    "set (carrier_list state) \<subseteq> to_set carrier"
    "state' = to_ordinary state"
    "to_set (result state') \<inter> set (carrier_list state) = {}"
    "distinct (carrier_list state)"
  shows "to_ordinary (BestInGreedy_exec state) = BestInGreedy_base state'"
  using assms(2-)
proof(induction arbitrary: state rule: BestInGreedy_base_induct[OF assms(1)])
  case (1 state')
  note IH = this
  show ?case
  proof(cases state' rule: BestInGreedy_base_cases)
    case 1
    note c1 =this
    show ?thesis
    proof(rule BestInGreedy_base_call_1_conds[OF 1], goal_cases)
      case 1
      then obtain x xs where 1: "carrier_list state' = x # xs"
        "indep' (set_insert (hd (carrier_list state')) (result state'))" by auto
      have new_state_is:"state'\<lparr>carrier_list := xs, result := set_insert x (result state')\<rparr>
           = BestInGreedy_base_upd1 state'"
        by (simp add: "1"(1) BestInGreedy_base_upd1_def)
      have x_not_in_result:"x \<notin> to_set (remove_wrapper (result state))"
        using "1"(1) IH(8) IH(9) by(force simp add: to_ordinary_def)
      have x_in_carrier: "x \<in> to_set carrier"
        using "1"(1) IH(7) IH(8) by(auto simp add: to_ordinary_def)
      have indep_new_state:"indep' (result (BestInGreedy_base_upd1 state'))"
        by (simp add: "1"(2) BestInGreedy_base_upd1_def)
      hence "indep' (set_insert x (result state'))"
        using "1"(1) "1"(2) by fastforce
      hence local_indep_oracle:"local_indep_oracle x (result state)"
        using local_indep_oracle[of "result state" x] IH(4,5,6,8) x_not_in_result x_in_carrier
        by(auto simp add: to_ordinary_def) 
      have 11: "subseteq (set_insert (hd (carrier_list state')) (result state')) carrier"
        using "1"(1) IH(6) IH(7)  carrier_inv matroid.set.set_insert matroid.set.set_subseteq IH(5) 
        by(subst matroid.set.set_subseteq)
          (auto intro: matroid.set.invar_insert simp add:  IH(8) wrapper_axioms(2) to_ordinary_def carrier_inv)+
      have 12: "to_set (result (BestInGreedy_base_upd1 state')) \<inter> 
                  set (carrier_list (BestInGreedy_exec_upd1 state)) = {}"
        using "1"(1) IH(10) IH(8) IH(9) to_ordinary_def  
        by(auto simp add: BestInGreedy_base_upd1_def BestInGreedy_exec_upd1_def matroid.set.set_insert IH(5) IH(8) to_ordinary_def wrapper_axioms(2))
      have 13: "distinct (carrier_list (BestInGreedy_exec_upd1 state))" 
        using "1"(1)  IH(10) IH(8)  by (auto simp add: to_ordinary_def BestInGreedy_exec_upd1_def)
      have "to_ordinary (BestInGreedy_exec (BestInGreedy_exec_upd1 state)) =
             BestInGreedy_base (BestInGreedy_base_upd1 state')"
        using "1"(1) IH(7) 11 12 13 x_in_carrier \<open>indep' (set_insert x (result state'))\<close>
        by(fastforce intro!: IH(2)[OF c1  indep_new_state] simp add: BestInGreedy_base_upd1_def BestInGreedy_exec_upd1_def
            IH(8) wrapper_axioms to_ordinary_def IH(5))
      then show ?case 
        using 1(1) local_indep_oracle IH(8)
        by(subst BestInGreedy_base_simps(1)[OF IH(1) c1], subst BestInGreedy_exec.simps)
          (auto simp add: BestInGreedy_base_upd1_def  BestInGreedy_exec_upd1_def to_ordinary_def)
    qed
  next
    case 2
    show ?thesis
    proof(cases rule: BestInGreedy_base_call_2_conds[OF 2])
      case 1
      then obtain x xs where 1:"carrier_list state' = x # xs"
        "\<not> indep' (set_insert (hd (carrier_list state')) (result state'))" by auto
      have new_state_is:"state'\<lparr>carrier_list := xs\<rparr>
           = BestInGreedy_base_upd2 state'"
        by (simp add: "1"(1) BestInGreedy_base_upd2_def)
      hence "\<not> indep' (set_insert x (result state'))"
        using "1"(1) "1"(2) by fastforce
      hence local_indep_oracle:"\<not> local_indep_oracle x (result state)"
        using local_indep_oracle[of "result state" ] IH(4,5,6,7,8, 9)1 by (simp add: to_ordinary_def)
      have same_result:"to_ordinary (BestInGreedy_exec (BestInGreedy_base_upd2 state)) = BestInGreedy_base (BestInGreedy_base_upd2 state')"
        using IH(4-) 1(1) new_state_is  IH(3)[OF 2]
        by(auto simp add: BestInGreedy_base_upd2_def to_ordinary_def)
      show ?thesis 
        using 1  local_indep_oracle  same_result 2 BestInGreedy_base_simps(2)[OF IH(1) 2]
        by(subst BestInGreedy_exec.simps)
          (auto intro!: IH(3) simp add: IH(8) new_state_is  to_ordinary_def  BestInGreedy_base_upd2_def) 
    qed
  next
    case 3
    then show ?thesis 
      using BestInGreedy_base_simps(3)[OF IH(1) 3] IH(8) 
      by(subst BestInGreedy_exec.simps)
        (auto intro: BestInGreedy_base_ret_1_conds simp add:  BestInGreedy_base_ret1_def to_ordinary_def)
  qed
qed

lemma indep'_empty: "matroid.indep_system_axioms carrier indep_fn \<Longrightarrow> indep' set_empty"
  using  matroid.set.invar_empty  matroid.set.set_empty matroid.set.set_subseteq
  by(unfold matroid.indep_system_axioms_def) fast

lemma BestInGreedy_exec_corresp:
  assumes BestInGreedy_base_axioms sort_desc_axioms
    "matroid.indep_system_axioms carrier indep_fn"
    "nonnegative c" "valid_order  order"
  shows "to_ordinary (BestInGreedy_exec (initial_state' c order)) = BestInGreedy_base (initial_state c order)"
  by(auto intro!: BestInGreedy_exec_corresp_general  initial_state_props(5)
      simp add: assms,
      auto intro: indep'_empty[OF assms(3)] 
      simp add: initial_state_def matroid.set.invar_empty  carrier_inv 
      matroid.set.set_empty matroid.set.set_subseteq  carrier_sorted_set[OF assms(1-5)]
      indep'_empty initial_state'_def  to_ordinary_def)
    (auto simp add: wrapper_axioms carrier_sorted_distinct[OF assms(1-5)])
end
end

end
