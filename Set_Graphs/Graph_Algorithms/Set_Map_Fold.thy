theory Set_Map_Fold
  imports Imperative.Imperative_DS
begin

locale set_fold_locale = 
imp_set_iterate where is_set = is_set and it_next = it_next +
imp_set_ins where ins = ins and is_set = is_set +
imp_set_empty where empty = empty and is_set = is_set
for is_set :: "'a set \<Rightarrow> 'simpl \<Rightarrow> assn" 
and ins :: "'a \<Rightarrow> 'simpl \<Rightarrow> 'simpl Heap"
and empty :: "'simpl Heap"
and it_next :: "'it \<Rightarrow> ('a \<times> 'it) Heap"
begin


partial_function (heap) set_fold_loop ::"'it \<Rightarrow>('a => 'b => 'b Heap) \<Rightarrow> 'b  \<Rightarrow> 'b Heap"
  where
"set_fold_loop it f acc = 
  (do {b <- it_has_next it;
       if \<not> b then  return acc
       else  do {
         (x, it') <- it_next it;
          acc' <- f x acc;
           set_fold_loop it' f acc'
       }})"

definition "simple_prog f acc it = 
  do {
         (x, it') <- it_next it;
          acc' <- f x acc;
          return acc'}"

lemma it_next_rule_empty_in_ass:
    "<is_it s p s' it  * \<up> (s' \<noteq> {})> 
      it_next it 
    <\<lambda>(a,it'). is_it s p (s' - {a}) it' * \<up>(a \<in> s')>"
  by sep_auto

lemma 
assumes "\<And> x y. <true>fimpl x y <\<lambda> r. \<up> (r = f x y)>"
shows "<is_it S Simpl S' it * \<up> (S' \<noteq> {})> simple_prog fimpl acc it
 <\<lambda>r. \<exists>\<^sub>A x. \<up> (x \<in> S' \<and> r = f x acc)  * is_set S Simpl>"
  unfolding simple_prog_def
  apply(rule ht_bind)
   apply(rule it_next_rule_empty_in_ass)
  subgoal for x
    apply(cases x)
    subgoal for x it
      apply simp
      apply(rule ht_cons_post[of _ _ 
           "\<lambda>r. \<up> ( r = f x acc) * (\<up> (x \<in> S')* is_set S Simpl)"])
        apply(rule ht_cons_pre[OF _ ht_frame[OF assms[of x acc]]])
        by(sep_auto intro: quit_iteration)
      done
    done

definition "set_fold Simpl= (\<lambda> f acc. 
         do {it_init <- it_init Simpl;
             set_fold_loop it_init f acc})"

lemmas [code] = set_fold_loop.simps set_fold_def

lemma weaken_conditions_and_frame:
  assumes "P1 \<Longrightarrow>\<^sub>A P1'*P"
          "\<And> r. P1'*Q r \<Longrightarrow>\<^sub>A P1'' r"
          "<P>c<Q>" 
     shows "<P1>c<P1''>"
  apply(rule ht_cons_prec[of P1 "P*P1'" "\<lambda> r. Q r*P1'" P1'' c ])
  using assms by(sep_auto intro: fr_refl ent_star_mono simp: star_aci(2))

lemma pure_assn_adjunct_concl:
"P \<Longrightarrow>\<^sub>A \<up>Q1*true \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q2 \<Longrightarrow> P \<Longrightarrow>\<^sub>A \<up> Q1*Q2"
  by sep_auto

lemma pure_assn_adjunct_prec:
"\<lbrakk> P1 \<Longrightarrow> P2 \<Longrightarrow>\<^sub>A Q\<rbrakk> \<Longrightarrow> \<up>P1*P2 \<Longrightarrow>\<^sub>A Q"
"\<lbrakk> P1 \<Longrightarrow> P2 \<Longrightarrow>\<^sub>A Q\<rbrakk> \<Longrightarrow> P2*\<up>P1 \<Longrightarrow>\<^sub>A Q"
  by sep_auto

lemma pure_conclI: 
  "Q \<Longrightarrow> P \<Longrightarrow>\<^sub>A \<up> Q * true"
  apply sep_auto
  done

lemma  set_fold_loop_correct:
assumes "\<And> x y. <true>fimpl x y <\<lambda> r. \<up> (r = f x y)>"
shows "<is_it S Simpl S' it> set_fold_loop it fimpl acc
 <\<lambda>r. (\<exists>\<^sub>Axs. \<up> (set xs = S' \<and> r = foldl (\<lambda> x y. f y x) acc xs)) * is_set S Simpl>"
proof(induction arbitrary: S' acc it rule: set_fold_loop.fixp_induct, goal_cases)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 others S' acc)
  show ?case
    apply(rule ht_bind)
     apply(rule it_has_next_rule)
    subgoal for b
      apply(cases b)
      subgoal
        apply(subst if_not_P)
         apply simp
        apply(rule ht_bind)
         apply (cases "S' = {}")
        apply simp
        apply(rule ht_frame)
         apply(rule it_next_rule)
         apply simp
        subgoal for x
          apply(cases x)
          subgoal for x it
            apply simp
            apply(rule ht_bind[of _ _ "\<lambda> r. \<up> (r = f x acc) * (is_it S Simpl (S' - {x}) it * \<up> (x \<in> S') * \<up> (S' \<noteq> {}))"])
            subgoal 
              apply(rule weaken_conditions_and_frame[OF _ _ assms(1), of _ "(is_it S Simpl (S' - {x}) it * \<up> (x \<in> S') * \<up> (S' \<noteq> {}))"])
              by sep_auto
            subgoal for xb
              apply(rule weaken_conditions_and_frame[OF _ _ 3, of _ "\<up> (x \<in> S') * \<up> (S' \<noteq> {})*\<up> (xb = f x acc)" "S' - {x}"])
              subgoal
                by sep_auto
              apply simp
              apply(rule ent_ex_preI)
              subgoal for r xs
              apply(rule ent_ex_postI[of _ _ "x#xs"])
               by sep_auto
             done
           done
         done
       done
     subgoal
       apply simp
       apply(rule ht_cons_post[of _ _ 
           "\<lambda>r. \<up> (r = acc) * (\<up> (S' = {})* is_set S Simpl)"])
        apply(rule ht_cons_pre[OF _ ht_frame[OF ], of _ true])
         by(sep_auto intro: quit_iteration)
       done
     done
 qed

lemma set_fold_correct:
  assumes "\<And> x y. <true>fimpl x y <\<lambda> r. \<up> (r = f x y)>"
  shows "<is_set S Simpl>
          set_fold Simpl fimpl acc 
         <\<lambda> r.(\<exists>\<^sub>A xs. \<up> (set xs = S \<and> r = foldl (\<lambda> x y. f y x) acc xs)) * is_set S Simpl>"
  unfolding set_fold_def 
  using set_fold_loop_correct[of fimpl f S Simpl S _ acc, OF assms] 
 by (sep_auto intro: it_init_rule)


end



(*interpretation hs: imp_set_iterate 
  is_hashset hs_is_it hs_it_init hs_it_has_next hs_it_next
  by (rule hs_iterate_impl)*)

definition "from_list_impl (xs:: nat list) \<equiv>
  do {S <- hs_new; foldM (\<lambda> x S. hs_ins  x S) xs S }"

  setup Locale_Code.open_block  
interpretation sfl: set_fold_locale
 hs_is_it hs_it_init hs_it_has_next is_hashset hs_ins hs_new hs_it_next
  by unfold_locales
setup Locale_Code.close_block

definition "set_fold_loop = 
  (sfl.set_fold_loop::
   nat \<times> (nat \<times> unit) list \<times> (nat, unit) hashtable 
    \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat Heap) \<Rightarrow> nat \<Rightarrow> nat Heap)"

definition "set_fold = (sfl.set_fold::
            ((nat, unit) hashtable \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat Heap) \<Rightarrow> nat \<Rightarrow> nat Heap))"(*(\<lambda> f acc. 
         do {it_init <- hs_it_init simpl;
             set_fold_loop it_init f acc})"*)

definition "f_here (x::nat) y = do{return (x+y)}"

(*definition "sinit = from_list_impl [1,2,3,4]"*)
                           
definition "hs_it_init_nat = (hs_it_init::(nat, unit) hashtable
   \<Rightarrow> (nat \<times> (nat \<times> unit) list \<times> (nat, unit) hashtable) Heap)"(* do {s <- sinit; it <- hs_it_init s; return it}"*)

definition "hs_new_nat = (hs_new::(nat, unit) hashtable Heap)"

 export_code set_fold set_fold_loop from_list_impl hs_it_init_nat hs_new_nat f_here checking SML_imp

 ML_val \<open>
    val noi = @{code nat_of_integer}
    val from_list_impl  = @{code from_list_impl} o map  noi
    val set_fold_loop = @{code set_fold_loop}
    val set_fold = @{code set_fold}
    val hs_it_init = @{code hs_it_init_nat}
    val hs_new = @{code hs_new_nat}
    val f_here = @{code f_here}
   
    val S = from_list_impl [0,1,2,3,4,5] ()
    val all_sum = set_fold S f_here (noi 3) ()
  
  \<close>


end