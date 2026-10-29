theory Array_Map_Set_Addons
  imports More_Lists Imp_Map_Set_Addons
          Separation_Logic_Imperative_HOL_Partial.Array_Map_Impl
          Separation_Logic_Imperative_HOL_Partial.Array_Set_Impl
begin

section \<open>Array Maps and Array Sets: Clearing, Ordered Iteration, Functional Models\<close>

text \<open>The array maps @{const is_iam} and array sets @{const is_ias} of the separation logic library
      are extended by

        \<^item> clear operations, which overwrite the existing array and allocate nothing,
        \<^item> an iteration over array sets in increasing order, which scans the array, and
        \<^item> the functional models they represent: maps @{typ \<open>'k \<rightharpoonup> 'v\<close>} and finite sets.

      If all keys are below the length of the arrays, updates and insertions never grow them.\<close>

subsection \<open>Filling an Array\<close>

partial_function (heap) array_fill :: "'a::heap array \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "array_fill a x i l =
     (if i < l then do { Array.upd i x a; array_fill a x (Suc i) l } else return ())"

lemma array_fill_rule:
  "i \<le> length xs \<Longrightarrow>
   <a \<mapsto>\<^sub>a xs> array_fill a x i (length xs) <\<lambda>_. a \<mapsto>\<^sub>a (take i xs @ replicate (length xs - i) x)>"
proof(induction "length xs - i" arbitrary: i xs)
  case (Suc d)
  hence "i < length xs" "d = length xs - Suc i"
    by simp_all
  thus ?case
    by (subst array_fill.simps)
       (sep_auto heap: Suc.hyps(1)[of "xs[i := x]" "Suc i", unfolded length_list_update]
          simp: take_Suc_conv_app_nth list_update_append replicate_diff_Suc)
qed (subst array_fill.simps, sep_auto)

lemma array_fill_all_rule:
  "<a \<mapsto>\<^sub>a xs> array_fill a x 0 (length xs) <\<lambda>_. a \<mapsto>\<^sub>a replicate (length xs) x>"
  using array_fill_rule[of 0 xs a x]
  by simp

subsection \<open>Clearing\<close>

definition "iam_clear a = do { l \<leftarrow> Array.len a; array_fill a None 0 l; return a }"

definition "ias_clear a = do { l \<leftarrow> Array.len a; array_fill a False 0 l; return a }"

lemma iam_clear_rule: "<is_iam m a> iam_clear a <is_iam Map.empty>"
  unfolding iam_clear_def is_iam_def
  by (sep_auto heap: array_fill_all_rule simp: iam_new_abs)

lemma ias_clear_rule: "<is_ias s a> ias_clear a <is_ias {}>"
  unfolding ias_clear_def is_ias_def
  by (sep_auto heap: array_fill_all_rule simp: ias_new_abs)

lemma iam_imp_map_clear: "imp_map_clear is_iam iam_clear"
  by unfold_locales (rule iam_clear_rule)

lemma ias_imp_set_clear: "imp_set_clear is_ias ias_clear"
  by unfold_locales (rule ias_clear_rule)

subsection \<open>Ordered Iteration over Array Sets\<close>

text \<open>The iterator is the array, its length and the position of the next element, or the length
      if there is none. @{term ias_scan} finds the next element.\<close>

partial_function (heap) ias_scan :: "bool array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "ias_scan a l i =
     (if i < l then do { b \<leftarrow> Array.nth a i; if b then return i else ias_scan a l (Suc i) }
      else return i)"

definition "ias_it_init a = do { l \<leftarrow> Array.len a; i \<leftarrow> ias_scan a l 0; return (a, l, i) }"

definition "ias_it_has_next it = (case it of (a, l, i) \<Rightarrow> return (i < l))"

definition "ias_it_next it = (case it of (a, l, i) \<Rightarrow>
   do { j \<leftarrow> ias_scan a l (Suc i); return (i, (a, l, j)) })"

definition "ias_is_it s p xs it = (case it of (a, l, i) \<Rightarrow>
   \<exists>\<^sub>Als. p \<mapsto>\<^sub>a ls * \<up>(a = p \<and> l = length ls \<and> s = ias_of_list ls \<and> i \<le> l \<and>
                          (i < l \<longrightarrow> ls ! i) \<and> xs = filter ((!) ls) [i..<l]))"

lemma ias_scan_rule:
  "i \<le> length ls \<Longrightarrow>
   <p \<mapsto>\<^sub>a ls> ias_scan p (length ls) i
   <\<lambda>j. p \<mapsto>\<^sub>a ls * \<up>(i \<le> j \<and> j \<le> length ls \<and> (j < length ls \<longrightarrow> ls ! j) \<and>
                    filter ((!) ls) [i..<length ls] = filter ((!) ls) [j..<length ls])>"
proof(induction "length ls - i" arbitrary: i)
  case (Suc d)
  hence "i < length ls" "d = length ls - Suc i"
    by simp_all
  thus ?case
    by (subst ias_scan.simps) (sep_auto heap: Suc.hyps(1)[of "Suc i"] simp: upt_conv_Cons)
qed (subst ias_scan.simps, sep_auto)

lemma sorted_list_of_ias: "sorted_list_of_set (ias_of_list ls) = filter ((!) ls) [0..<length ls]"
  by (rule sorted_distinct_set_unique)
     (auto simp: ias_of_list_def sorted_wrt_filter)

lemma ias_it_init_rule:
  "<is_ias s p> ias_it_init p <ias_is_it s p (sorted_list_of_set s)>"
  unfolding ias_it_init_def is_ias_def ias_is_it_def
  by (sep_auto heap: ias_scan_rule simp: sorted_list_of_ias)

lemma ias_it_next_rule:
  "<ias_is_it s p (x # xs) it> ias_it_next it <\<lambda>(y, it'). ias_is_it s p xs it' * \<up>(y = x)>"
  unfolding ias_it_next_def ias_is_it_def
  by (cases it; cases "snd (snd it) < fst (snd it)")
     (sep_auto heap: ias_scan_rule simp: upt_conv_Cons)+

lemma ias_it_has_next_rule:
  "<ias_is_it s p xs it> ias_it_has_next it <\<lambda>r. ias_is_it s p xs it * \<up>(r \<longleftrightarrow> xs \<noteq> [])>"
  unfolding ias_it_has_next_def ias_is_it_def
  by (cases it) (sep_auto simp: upt_conv_Cons filter_empty_conv)

lemma ias_quit_iteration: "ias_is_it s p xs it \<Longrightarrow>\<^sub>A is_ias s p"
  unfolding ias_is_it_def is_ias_def
  by (cases it) sep_auto

lemma ias_imp_set_ordered_iterate:
  "imp_set_ordered_iterate is_ias sorted_list_of_set ias_is_it ias_it_init ias_it_has_next
     ias_it_next"
  by (intro imp_set_ordered_iterate.intro imp_set_ordered_iterate_axioms.intro sorted_list_of_set_order)
     (rule ias_it_init_rule ias_it_next_rule ias_it_has_next_rule ias_quit_iteration)+

subsection \<open>Functional Models\<close>

text \<open>The functional models are maps @{typ \<open>'k \<rightharpoonup> 'v\<close>} and finite sets. They are not executed;
      they only serve as the functional ADT instances in the proofs.\<close>

definition "fmap_update k v (m :: 'k \<rightharpoonup> 'v) = m(k \<mapsto> v)"
definition "fmap_delete k (m :: 'k \<rightharpoonup> 'v) = m(k := None)"
definition "fmap_lookup (m :: 'k \<rightharpoonup> 'v) = m"
definition "fmap_invar (m :: 'k \<rightharpoonup> 'v) = True"

lemma fmap_Map: "Map Map.empty fmap_update fmap_delete fmap_lookup fmap_invar"
  by unfold_locales (auto simp: fmap_update_def fmap_delete_def fmap_lookup_def fmap_invar_def)

definition "fset_insert x (s :: 'a set) = insert x s"
definition "fset_delete x (s :: 'a set) = s - {x}"
definition "fset_isin (s :: 'a set) x = (x \<in> s)"
definition "fset_set (s :: 'a set) = s"

lemma fset_Set: "Set {} fset_insert fset_delete fset_isin fset_set finite"
  by unfold_locales (auto simp: fset_insert_def fset_delete_def fset_isin_def fset_set_def)

subsection \<open>The Connections\<close>

lemma ias_imp_set_conn:
  "imp_set_conn {} fset_insert fset_delete fset_isin fset_set finite is_ias ias_memb ias_ins
     ias_clear sorted_list_of_set ias_is_it ias_it_init ias_it_has_next ias_it_next"
  unfolding imp_set_conn_def
  using fset_Set ias_memb_impl ias_ins_impl ias_imp_set_clear ias_imp_set_ordered_iterate
  by (simp add: fset_set_def fset_insert_def)

lemma iam_imp_map_conn_clear:
  assumes "\<And>m k v. m_invar m \<Longrightarrow> m_invar (m_update k v m)"
      and "\<And>m k v. m_invar m \<Longrightarrow> m_lookup (m_update k v m) = (m_lookup m)(k \<mapsto> v)"
      and "m_invar m_empty" "m_lookup m_empty = Map.empty"
  shows "imp_map_conn_clear is_iam iam_lookup iam_update m_update m_lookup m_invar iam_clear
           m_empty"
  using assms
  by (intro imp_map_conn_clear.intro imp_map_conn.intro imp_map_conn_clear_axioms.intro
            imp_map_conn_axioms.intro iam.imp_map_lookup_axioms iam.imp_map_update_axioms
            iam_imp_map_clear) auto

lemma iam_imp_map_conn:
  assumes "\<And>m k v. m_invar m \<Longrightarrow> m_invar (m_update k v m)"
      and "\<And>m k v. m_invar m \<Longrightarrow> m_lookup (m_update k v m) = (m_lookup m)(k \<mapsto> v)"
  shows "imp_map_conn is_iam iam_lookup iam_update m_update m_lookup m_invar"
  using assms
  by (intro imp_map_conn.intro imp_map_conn_axioms.intro iam.imp_map_lookup_axioms
            iam.imp_map_update_axioms) auto

lemma fmap_conn_facts:
  "fmap_invar m \<Longrightarrow> fmap_invar (fmap_update k v m)"
  "fmap_invar m \<Longrightarrow> fmap_lookup (fmap_update k v m) = (fmap_lookup m)(k \<mapsto> v)"
  "fmap_invar Map.empty" "fmap_lookup Map.empty = Map.empty"
  by (auto simp: fmap_update_def fmap_lookup_def fmap_invar_def)

end
