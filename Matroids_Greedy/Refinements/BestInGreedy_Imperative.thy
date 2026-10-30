theory BestInGreedy_Imperative
  imports Matroids_Greedy.BestInGreedy_exec
          Separation_Logic_Imperative_HOL_Partial.Sep_Main
          "HOL-Library.Rewrite"
begin

provenance ai_human

no_notation Ref.update (\<open>_ := _\<close> 62)

section \<open>Imperative Best-In-Greedy Locale\<close>

subsection \<open>Setup\<close>

(* The imperative state.

  The carrier list of the functional state is refined by an array together with a pointer into
  that array: the part of the array starting at the pointer is the carrier list.
  Advancing in the carrier list is thus implemented by incrementing the pointer.

  The result of the functional state (of type 'wrps) is refined by an imperative 
  data structure (of type 'wrpsi), connected via the assertion wrapper_assn.
*)

record ('a, 'wrpsi) best_in_greedy_state_imp = 
  carrier_array :: "'a array" carrier_ptr :: nat result_impl :: 'wrpsi

(* We assume imperative implementations of the operations on the result set that are used by 
   BestInGreedy_exec, i.e. creating the empty result, inserting an element, and the independence 
   oracle, together with Hoare triples relating them to their functional counterparts.

   Additionally, we assume an imperative sorting function sort_desc_impl, which takes an imperative 
   cost function c_impl and an array holding the order list. The sorting is done in-place, i.e.
   afterwards, the same array holds the sorted list sort_desc c order.

   The imperative cost function c_impl (of type 'ci) refines the functional cost function c via
   the assertion cost_assn. This allows c_impl to be backed by data on the heap, e.g. it may be
   instantiated with a function that reads the heap, or with an array of costs. 
   The sorting function only reads the cost function, i.e. cost_assn is preserved.

   The imperative operations on the result only require an implementation invariant
   wrapper_impl_invar, which is independent of wrapper_invar from BestInGreedy_exec. 
   (wrapper_invar is only preserved by the insertions that are done by the algorithm, which
   depends on the correctness of the independence oracle.) The implementation invariant has to 
   hold for the empty result and has to be preserved by inserting any element of the carrier. *)

locale BestInGreedy_Imperative = BestInGreedy_exec 
  where wrapper_empty = "wrapper_empty :: 'wrps" 
    and wrapper_insert = "wrapper_insert :: ('a::{linorder, heap}) \<Rightarrow> 'wrps \<Rightarrow> 'wrps"
  for wrapper_empty wrapper_insert +
  fixes wrapper_impl_invar :: "'wrps \<Rightarrow> bool"
    and wrapper_assn :: "'wrps \<Rightarrow> 'wrpsi \<Rightarrow> assn"
    and wrapper_empty_impl :: "'wrpsi Heap"
    and wrapper_insert_impl :: "'a \<Rightarrow> 'wrpsi \<Rightarrow> 'wrpsi Heap"
    and local_indep_oracle_impl :: "'a \<Rightarrow> 'wrpsi \<Rightarrow> bool Heap"
    and cost_assn :: "('a \<Rightarrow> rat) \<Rightarrow> 'ci \<Rightarrow> assn"
    and sort_desc_impl :: "'ci \<Rightarrow> 'a array \<Rightarrow> 'a array Heap"
  assumes wrapper_impl_invar_empty: "wrapper_impl_invar wrapper_empty"
  and wrapper_impl_invar_insert: 
    "wrapper_impl_invar S \<Longrightarrow> x \<in> to_set carrier \<Longrightarrow> wrapper_impl_invar (wrapper_insert x S)"
  and wrapper_empty_impl_rule[sep_heap_rules]: 
    "<emp> wrapper_empty_impl <wrapper_assn wrapper_empty>"
  and wrapper_insert_impl_rule[sep_heap_rules]: 
    "wrapper_impl_invar S \<Longrightarrow> x \<in> to_set carrier \<Longrightarrow>
      <wrapper_assn S Si> wrapper_insert_impl x Si <wrapper_assn (wrapper_insert x S)>"
  and local_indep_oracle_impl_rule[sep_heap_rules]: 
    "wrapper_impl_invar S \<Longrightarrow> x \<in> to_set carrier \<Longrightarrow> 
      <wrapper_assn S Si> local_indep_oracle_impl x Si 
      <\<lambda>r. wrapper_assn S Si * \<up>(r = local_indep_oracle x S)>"
  and sort_desc_impl_rule[sep_heap_rules]:
    "<cost_assn c c_impl * order_array \<mapsto>\<^sub>a order> sort_desc_impl c_impl order_array 
     <\<lambda>r. cost_assn c c_impl * order_array \<mapsto>\<^sub>a sort_desc c order * \<up>(r = order_array)>"
begin

subsection \<open>State\<close>

(* The array holds some list ys, whose suffix starting at the pointer is the carrier list.
   The prefix of ys (the elements already processed) is irrelevant. 
   The remaining carrier list only contains elements of the carrier. *)

definition "BestInGreedy_state_assn s si \<equiv> 
    (\<exists>\<^sub>Ays. carrier_array si \<mapsto>\<^sub>a ys 
       * \<up>(carrier_ptr si \<le> length ys \<and> drop (carrier_ptr si) ys = carrier_list s))
  * wrapper_assn (result s) (result_impl si)
  * \<up>(wrapper_impl_invar (result s) \<and> set (carrier_list s) \<subseteq> to_set carrier)"

(* The initial state is created from an array holding the order list and an imperative cost 
   function. The array is sorted in-place, and then becomes the carrier array. *)

definition "BestInGreedy_initial_state_impl c_impl order_array = do {
  carrier_array \<leftarrow> sort_desc_impl c_impl order_array;
  result \<leftarrow> wrapper_empty_impl;
  Heap_Monad.return \<lparr> carrier_array = carrier_array, carrier_ptr = 0, result_impl = result \<rparr>
}"

subsection \<open>Main Algorithm\<close>

partial_function (heap) BestInGreedy_imperative :: 
  "('a, 'wrpsi) best_in_greedy_state_imp \<Rightarrow> ('a, 'wrpsi) best_in_greedy_state_imp Heap" where
  "BestInGreedy_imperative best_in_greedy_state = do {
     len \<leftarrow> Array.len (carrier_array best_in_greedy_state);
     (if carrier_ptr best_in_greedy_state < len then do {
        x \<leftarrow> Array.nth (carrier_array best_in_greedy_state) (carrier_ptr best_in_greedy_state);
        b \<leftarrow> local_indep_oracle_impl x (result_impl best_in_greedy_state);
        (if b then do {
           new_result \<leftarrow> wrapper_insert_impl x (result_impl best_in_greedy_state);
           BestInGreedy_imperative (best_in_greedy_state 
             \<lparr>carrier_ptr := carrier_ptr best_in_greedy_state + 1, result_impl := new_result\<rparr>)
         }
         else 
           BestInGreedy_imperative (best_in_greedy_state 
             \<lparr>carrier_ptr := carrier_ptr best_in_greedy_state + 1\<rparr>))
      }
      else Heap_Monad.return best_in_greedy_state)
  }"

lemmas [code] = BestInGreedy_imperative.simps BestInGreedy_exec.simps initial_state'_def

lemma BestInGreedy_initial_state_rule[sep_heap_rules]: 
  "set (sort_desc c order) \<subseteq> to_set carrier \<Longrightarrow>
   <cost_assn c c_impl * order_array \<mapsto>\<^sub>a order> 
     BestInGreedy_initial_state_impl c_impl order_array 
   <\<lambda>si. cost_assn c c_impl * BestInGreedy_state_assn (initial_state' c order) si>"
  unfolding BestInGreedy_initial_state_impl_def initial_state'_def BestInGreedy_state_assn_def
  by (sep_auto simp: wrapper_impl_invar_empty)

(* Reading the head of the carrier list from the array. *)
lemma drop_eq_Cons_conv:
  "drop p ys = x # xs \<longleftrightarrow> p < length ys \<and> ys ! p = x \<and> drop (Suc p) ys = xs"
  by (metis Cons_nth_drop_Suc drop_all leI list.distinct(1) list.inject)

lemma BestInGreedy_imperative_rule[sep_heap_rules]: 
  "<BestInGreedy_state_assn state statei> 
     BestInGreedy_imperative statei 
   <\<lambda>ri. BestInGreedy_state_assn (BestInGreedy_exec state) ri>"
proof (induction arbitrary: state statei rule: BestInGreedy_imperative.fixp_induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 f)

  (* As for DFS, we unfold the state assertion for the whole proof. *)
  note IH = "3.IH"[of "\<lparr>carrier_list = cl, result = r\<rparr>" 
                     "\<lparr>carrier_array = ca, carrier_ptr = p, result_impl = ri\<rparr>" for cl r ca p ri]
  note IH[sep_heap_rules] = IH[unfolded BestInGreedy_state_assn_def, simplified, rule_format]

  let "<?P> ?body <\<lambda>r. ?post (BestInGreedy_exec state) r>" = ?case
  define P where "P=?P"
  define body where "body=?body"
  define post where "post=?post"

  note IMP_DEFS = P_def body_def post_def BestInGreedy_state_assn_def

  show "<P> body <\<lambda>r. post (BestInGreedy_exec state) r>"
    apply (cases state; cases statei; simp)
    subgoal for carrier_list result carrier_array carrier_ptr result_impl
      (* Abstract algorithm controls splitting! *)
      apply (rewrite in "<_> _ <\<hole>>" BestInGreedy_exec.simps)
      apply (clarsimp split!: list.split if_split simp: Let_def)

      (* Now let concrete algorithm follow. *)

      subgoal (* carrier_list = [] *)
        unfolding IMP_DEFS by sep_auto

      subgoal (* carrier_list = x # xs, x can be added to the result *)
        unfolding IMP_DEFS by (sep_auto simp: drop_eq_Cons_conv wrapper_impl_invar_insert)

      subgoal (* carrier_list = x # xs, x cannot be added to the result *)
        unfolding IMP_DEFS by (sep_auto simp: drop_eq_Cons_conv)
      done
    done
qed

subsection \<open>Algorithm combined with Initial State\<close>

definition "BestInGreedy_imperative' c_impl order_array \<equiv> do { 
  state \<leftarrow> BestInGreedy_initial_state_impl c_impl order_array; 
  BestInGreedy_imperative state 
}"

lemma BestInGreedy_imperative'_rule[sep_heap_rules]:
  "set (sort_desc c order) \<subseteq> to_set carrier \<Longrightarrow>
   <cost_assn c c_impl * order_array \<mapsto>\<^sub>a order> 
     BestInGreedy_imperative' c_impl order_array 
   <\<lambda>ri. cost_assn c c_impl * BestInGreedy_state_assn (BestInGreedy_exec (initial_state' c order)) ri>"
  unfolding BestInGreedy_imperative'_def by sep_auto

end


section \<open>Combined Correctness Theorem\<close>

(* We add the assumptions that are needed for the correctness of the functional algorithm 
   and its correspondence to BestInGreedy_exec. *)

locale BestInGreedy_Imperative_thms = BestInGreedy_Imperative +
  assumes local_indep_oracle_correct:
    "\<And> S x. wrapper_invar S \<Longrightarrow> indep' (remove_wrapper S) \<Longrightarrow> subseteq (remove_wrapper S) carrier \<Longrightarrow>
         \<not> x \<in> to_set (remove_wrapper S) \<Longrightarrow> x \<in> to_set carrier
    \<Longrightarrow> (local_indep_oracle x S \<longleftrightarrow> indep' (set_insert x (remove_wrapper S)))"
  and carrier_inv: "set_inv carrier"
  and BestInGreedy_base_axioms: "BestInGreedy_base_axioms"
  and sort_desc_axioms: "sort_desc_axioms"
  and indep_system_axioms: "matroid.indep_system_axioms carrier indep_fn"
begin

lemma BestInGreedy_exec_corresp_inst:
  assumes "nonnegative c" "valid_order order"
  shows "to_ordinary (BestInGreedy_exec (initial_state' c order)) = BestInGreedy_base (initial_state c order)"
  by (rule BestInGreedy_exec_corresp[OF _ carrier_inv BestInGreedy_base_axioms 
                                       sort_desc_axioms indep_system_axioms assms])
     (rule local_indep_oracle_correct)

lemma sort_desc_in_carrier:
  "valid_order order \<Longrightarrow> set (sort_desc c order) \<subseteq> to_set carrier"
  using sort_desc_axioms by (simp add: sort_desc_axioms_def valid_order_def)

lemmas BestInGreedy_base_correct_inst = 
  BestInGreedy_base_correct_1[OF BestInGreedy_base_axioms sort_desc_axioms indep_system_axioms]
  BestInGreedy_base_correct_2[OF BestInGreedy_base_axioms sort_desc_axioms indep_system_axioms]
  BestInGreedy_base_correct_3[OF BestInGreedy_base_axioms sort_desc_axioms indep_system_axioms]

lemmas BestInGreedy_base_correct_matroid_inst = 
  BestInGreedy_base_correct_matroid[OF BestInGreedy_base_axioms sort_desc_axioms]

(* The final imperative state refines a functional state which, after removing the wrapper,
   is exactly the result of the functional algorithm BestInGreedy_base. 
   Hence, all correctness properties of BestInGreedy_base carry over to the imperative algorithm. *)

lemma BestInGreedy_imperative'_absrl:
  assumes "nonnegative c" "valid_order order"
  shows 
    "<cost_assn c c_impl * order_array \<mapsto>\<^sub>a order> BestInGreedy_imperative' c_impl order_array 
     <\<lambda>ri. cost_assn c c_impl * (\<exists>\<^sub>Astate. BestInGreedy_state_assn state ri * \<up>(
        to_ordinary state = BestInGreedy_base (initial_state c order) 
      \<and> valid_solution (remove_wrapper (result state))
      \<and> indep_system.basis_in (matroid.indep_abs indep_fn) (matroid.carrier_abs carrier) 
          (to_set (remove_wrapper (result state)))
      \<and> (\<forall>X. valid_solution X \<longrightarrow> 
          indep_system.rank_quotient (matroid.carrier_abs carrier) (matroid.indep_abs indep_fn) 
            * c_set c (to_set X)
          \<le> c_set c (to_set (remove_wrapper (result state))))))>"
proof -
  have corresp: "to_ordinary (BestInGreedy_exec (initial_state' c order)) 
                 = BestInGreedy_base (initial_state c order)"
    using BestInGreedy_exec_corresp_inst[OF assms] .
  have result_is: "remove_wrapper (result (BestInGreedy_exec (initial_state' c order))) 
                   = result (BestInGreedy_base (initial_state c order))"
    using arg_cong[OF corresp, of result] by (simp add: to_ordinary_def)
  show ?thesis
    apply (rule ht_cons_post_prec[OF BestInGreedy_imperative'_rule[OF sort_desc_in_carrier[OF assms(2)]]])
    apply (rule ent_star_mono[OF ent_refl])
    apply (rule ent_ex_postI[where x = "BestInGreedy_exec (initial_state' c order)"])
    using corresp BestInGreedy_base_correct_inst[OF assms]
    by (sep_auto simp: result_is)
qed

(* If the independence system is a matroid, the result of the imperative algorithm 
   is an optimal solution. *)

lemma BestInGreedy_imperative'_matroid_opt:
  assumes "matroid.matroid_axioms carrier indep_fn" "nonnegative c" "valid_order order"
  shows 
    "<cost_assn c c_impl * order_array \<mapsto>\<^sub>a order> BestInGreedy_imperative' c_impl order_array 
     <\<lambda>ri. cost_assn c c_impl * (\<exists>\<^sub>Astate. BestInGreedy_state_assn state ri * \<up>(
        to_ordinary state = BestInGreedy_base (initial_state c order) 
      \<and> (\<forall>X. valid_solution X \<longrightarrow> 
          c_set c (to_set X) \<le> c_set c (to_set (remove_wrapper (result state))))))>"
proof -
  have corresp: "to_ordinary (BestInGreedy_exec (initial_state' c order)) 
                 = BestInGreedy_base (initial_state c order)"
    using BestInGreedy_exec_corresp_inst[OF assms(2,3)] .
  have result_is: "remove_wrapper (result (BestInGreedy_exec (initial_state' c order))) 
                   = result (BestInGreedy_base (initial_state c order))"
    using arg_cong[OF corresp, of result] by (simp add: to_ordinary_def)
  show ?thesis
    apply (rule ht_cons_post_prec[OF BestInGreedy_imperative'_rule[OF sort_desc_in_carrier[OF assms(3)]]])
    apply (rule ent_star_mono[OF ent_refl])
    apply (rule ent_ex_postI[where x = "BestInGreedy_exec (initial_state' c order)"])
    using corresp BestInGreedy_base_correct_matroid_inst[OF assms]
    by (sep_auto simp: result_is)
qed

end

end
