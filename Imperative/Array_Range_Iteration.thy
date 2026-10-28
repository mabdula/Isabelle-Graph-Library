theory Array_Range_Iteration
  imports Separation_Logic_Imperative_HOL_Partial.Sep_Main
begin

section \<open>Iterating over a Range of an Array\<close>

text \<open>Folds of a heap function over the entries of an array between two positions, together
      with lemmas on the corresponding sublists.\<close>

lemma intervall_rw1:"{0..ed} = {..< Suc ed}"
  by auto

lemma intervall_rw2:"{j. j \<le> n} = {..<Suc n}"
  by auto

lemma nths_intervall_as_drop_and_take:
  "nths list {start..ed} = drop (start) (take (Suc ed) list)"
  apply(induction list arbitrary: start ed)
  subgoal
    by simp
  subgoal for a list start ed
    apply(cases start)
     apply(all \<open>cases ed\<close>)
       apply (auto simp add: nths_Cons)
    subgoal
      by(auto simp add: intervall_rw2)
    by(auto simp add: nths_def)
  done

lemma nths_intervall_strict_as_drop_and_take:
  "nths list {start..<ed} = drop (start) (take ed list)"
  by(cases ed)
    (simp_all add: atLeastLessThanSuc_atLeastAtMost nths_intervall_as_drop_and_take)

lemma nths_intervall_split_off_first:
  assumes "start \<le> end" "end < length list"
  shows "(nths list {start..end}) =  (list ! start # nths list {Suc start..end})"
  unfolding nths_intervall_as_drop_and_take
  apply(subst Cons_nth_drop_Suc[of start, symmetric])
  using assms(1,2)
  by (auto intro!: arg_cong2[where f = Cons] simp add: assms(1) le_imp_less_Suc)

lemma nths_intervall_strict_split_off_first:
  assumes "start < end" "end < length list"
  shows "(nths list {start..<end}) =  (list ! start # nths list {Suc start..<end})"
  unfolding nths_intervall_strict_as_drop_and_take
  apply(subst Cons_nth_drop_Suc[of start, symmetric])
  using assms(1,2)
  by (auto intro!: arg_cong2[where f = Cons] simp add: assms(1) le_imp_less_Suc)

lemma nth_shifted_by_lower_bound_of_nths_intervall:
  assumes "u < length xs" "i \<ge> l" "i \<le> u"
  shows "nths xs {l..u} ! (i -l) = xs ! i" 
  unfolding nths_intervall_as_drop_and_take
  using assms
  by (subst nth_drop)(auto simp add: le_imp_less_Suc)

lemma nth_of_nths_intervall_shifted_by_lower_bound:
  assumes "u < length xs" "l + i \<le> u" 
  shows "nths xs {l..u} ! (i) = xs ! (i + l)" 
  unfolding nths_intervall_as_drop_and_take
  using assms
  by (subst nth_drop)(auto simp add: le_imp_less_Suc algebra_simps)

lemma zip_foldl_map:
     "ys = map y xs \<Longrightarrow> foldl (\<lambda>acc a. case a of (x, y) \<Rightarrow> f x y acc) acc (zip xs ys)
      = foldl (\<lambda>acc x. f x (y x) acc) acc xs"
  by(induction xs arbitrary: acc ys) auto

lemma length_nths_of_intervall:
  assumes  "u < length xs"
  shows "length (nths xs {l..u})  = (u + 1) - l" 
  using assms
  by(auto simp add: nths_intervall_as_drop_and_take)

partial_function (heap) iterate_range where
  "iterate_range arr start end fi acc=
    (if start \<le> end then
      do{ current \<leftarrow> Array.nth arr start;
          acc' \<leftarrow> fi current acc;
          iterate_range arr (Suc start) end fi acc'}
     else return acc)"
(*
definition "put arr new = Array.upd arr 0 new"
*)

lemma iterate_range_rule:
  assumes "\<And> acc acci x. x \<in> set (nths list {start..end}) \<Longrightarrow> <acc_assn acc acci * F> fi x acci 
            <\<lambda> r. acc_assn (f acc x) r * F>"
  shows "<arr \<mapsto>\<^sub>a list * \<up> (start \<le> length list \<and> end < length list) *F * acc_assn acc acci>
          iterate_range arr start end fi acci 
         <\<lambda> r. arr \<mapsto>\<^sub>a list * acc_assn (foldl f acc (nths list {start..end})) r *  F>"
  using assms
proof(induction arbitrary: start acc acci rule: iterate_range.fixp_induct, goal_cases)
  case 1
  then show ?case
    by simp
next
  case 2
  then show ?case 
    by simp
next
  case (3 fi start acc acci)
  note IH = this
  show ?case 
     using  IH(1)[of "Suc start" "f acc _"] IH(2)
     by (sep_auto simp: nths_intervall_split_off_first[of start] split: if_split)
 qed

partial_function (heap) iterate_range_strict where
  "iterate_range_strict arr start end fi acc=
    (if start < end then
      do{ current \<leftarrow> Array.nth arr start;
          acc' \<leftarrow> fi current acc;
          iterate_range_strict arr (Suc start) end fi acc'}
     else return acc)"

lemma iterate_range_strict_rule:
 assumes "\<And> acc acci x. x \<in> set (nths list {start..<end}) \<Longrightarrow> <acc_assn acc acci * F> fi x acci 
            <\<lambda> r. acc_assn (f acc x) r * F>"
  shows "<arr \<mapsto>\<^sub>a list * \<up> (end < length list) *F * acc_assn acc acci>
          iterate_range_strict arr start end fi acci 
         <\<lambda> r. arr \<mapsto>\<^sub>a list * acc_assn (foldl f acc (nths list {start..<end})) r *  F>"
  using assms
proof(induction arbitrary: start acc acci rule: iterate_range_strict.fixp_induct, goal_cases)
  case 1
  then show ?case
    by simp
next
  case 2
  then show ?case 
    by simp
next
  case (3 fi start acc acci)
  note IH = this
  show ?case 
     using  IH(1)[of "Suc start" "f acc _"] IH(2)
     by (sep_auto simp: nths_intervall_strict_split_off_first[of start] split: if_split)
 qed

partial_function (heap) iterate_range_infoed where
  "iterate_range_infoed arr info_arr start end fi acc=
    (if start \<le> end then
      do{ current \<leftarrow> Array.nth arr start;
          current_info \<leftarrow> Array.nth info_arr start;
          acc' \<leftarrow> fi current current_info acc;
          iterate_range_infoed arr info_arr (Suc start) end fi acc'}
     else return acc)"

lemma iterate_range_infoed_rule:
  assumes "\<And> acc acci x y. <acc_assn acc acci * F> fi x y acci 
            <\<lambda> r. acc_assn (f acc (x, y)) r * F>"
  shows "<arr \<mapsto>\<^sub>a list * info_arr \<mapsto>\<^sub>a info_list *
          \<up> (start \<le> length list \<and> end < length list \<and>
             start \<le> length info_list \<and> end < length info_list) *F * acc_assn acc acci>
          iterate_range_infoed arr info_arr start end fi acci 
       <\<lambda> r. arr \<mapsto>\<^sub>a list *  info_arr \<mapsto>\<^sub>a info_list * 
        acc_assn (foldl f acc (zip (nths list {start..end}) (nths info_list {start..end}))) r * F>"
proof(induction arbitrary: start acc acci rule: iterate_range_infoed.fixp_induct, goal_cases)
  case 1
  then show ?case
    by simp
next
  case 2
  then show ?case 
    by simp
next
  case (3 fi start acc acci)
  note IH = this
  show ?case 
     using assms(1) IH(1)[of "Suc start" "f acc _"]
     by (sep_auto simp: nths_intervall_split_off_first[of start] split: if_split)
 qed

(*TODO MOVE*)
lemma ht_ex_pre_and_post_I:
  "(\<And> x. <P x> c <\<lambda> r. Q x r>) \<Longrightarrow> <\<exists>\<^sub>A x. P x> c <\<lambda> r. \<exists>\<^sub>A x. Q x r>"
 by sep_auto

end
