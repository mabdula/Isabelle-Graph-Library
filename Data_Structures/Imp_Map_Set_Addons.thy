theory Imp_Map_Set_Addons
  imports Separation_Logic_Imperative_HOL_Partial.Imp_Set_Spec
          Separation_Logic_Imperative_HOL_Partial.Imp_Map_Spec
          "HOL-Data_Structures.Set_Specs" "HOL-Data_Structures.Map_Specs"
          More_Lists
begin

section \<open>Additions to the Imperative Map and Set Interfaces\<close>

text \<open>This theory extends the interfaces for imperative maps and sets of the separation logic
      library by

        \<^item> clear operations, which empty a data structure in place, without allocation,
        \<^item> an iteration over sets in a fixed order @{term lst}, together with a fold combinator, and
        \<^item> the connection to the functional ADTs @{locale Set} and @{locale Map}, whose types stay
          abstract.\<close>

subsection \<open>Clearing\<close>

locale imp_map_clear = imp_map +
  constrains is_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'm \<Rightarrow> assn"
  fixes clear :: "'m \<Rightarrow> 'm Heap"
  assumes clear_rule[sep_heap_rules]: "<is_map m p> clear p <is_map Map.empty>"

locale imp_set_clear = imp_set +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes clear :: "'s \<Rightarrow> 's Heap"
  assumes clear_rule[sep_heap_rules]: "<is_set s p> clear p <is_set {}>"

subsection \<open>Ordered Iteration\<close>

text \<open>A fixed order of the elements of finite sets that is compatible with filtering.\<close>

locale set_order =
  fixes lst :: "'a set \<Rightarrow> 'a list"
  assumes lst_distinct: "finite S \<Longrightarrow> distinct (lst S)"
      and lst_set: "finite S \<Longrightarrow> set (lst S) = S"
      and lst_filter: "finite S \<Longrightarrow> lst (S \<inter> Collect P) = filter P (lst S)"

lemma sorted_list_of_set_order: "set_order sorted_list_of_set"
  by unfold_locales (auto intro!: sorted_distinct_set_unique sorted_wrt_filter)

text \<open>The iterator visits the elements in the order @{term lst}, like
      @{locale imp_map_iterate'} for maps. Leaving the iteration gives back exactly the set.\<close>

locale imp_set_ordered_iterate = imp_set + set_order lst
  for lst :: "'a set \<Rightarrow> 'a list" +
  constrains is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn"
  fixes is_it :: "'a set \<Rightarrow> 's \<Rightarrow> 'a list \<Rightarrow> 'it \<Rightarrow> assn"
  fixes it_init :: "'s \<Rightarrow> 'it Heap"
  fixes it_has_next :: "'it \<Rightarrow> bool Heap"
  fixes it_next :: "'it \<Rightarrow> ('a \<times> 'it) Heap"
  assumes it_init_rule[sep_heap_rules]:
    "<is_set s p> it_init p <is_it s p (lst s)>"
  assumes it_next_rule[sep_heap_rules]:
    "<is_it s p (x # xs) it> it_next it <\<lambda>(y, it'). is_it s p xs it' * \<up>(y = x)>"
  assumes it_has_next_rule[sep_heap_rules]:
    "<is_it s p xs it> it_has_next it <\<lambda>r. is_it s p xs it * \<up>(r \<longleftrightarrow> xs \<noteq> [])>"
  assumes quit_iteration:
    "is_it s p xs it \<Longrightarrow>\<^sub>A is_set s p"

subsection \<open>A Fold Combinator over Iterators\<close>

text \<open>@{term fold_pre} collects the preconditions of the single steps of a fold.\<close>

fun fold_pre :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> bool" where
  "fold_pre P g b [] = True"
| "fold_pre P g b (x # xs) = (P x b \<and> fold_pre P g (g b x) xs)"

partial_function (heap) iter_fold ::
  "('it \<Rightarrow> bool Heap) \<Rightarrow> ('it \<Rightarrow> ('a \<times> 'it) Heap) \<Rightarrow> ('a \<Rightarrow> 'c \<Rightarrow> 'c Heap) \<Rightarrow>
   'it \<Rightarrow> 'c \<Rightarrow> 'c Heap" where
  "iter_fold has_next next f it c =
     do { b \<leftarrow> has_next it;
          if b then do { (x, it') \<leftarrow> next it;
                         c' \<leftarrow> f x c;
                         iter_fold has_next next f it' c' }
          else return c }"

text \<open>The rule for @{const iter_fold}, for an arbitrary iterator assertion @{term I} indexed by
      the list of elements that remain to be visited.\<close>

lemma iter_fold_rule_gen:
  assumes "\<And>xs it. <I xs it> has_next it <\<lambda>r. I xs it * \<up>(r \<longleftrightarrow> xs \<noteq> [])>"
      and "\<And>x xs it. <I (x # xs) it> next it <\<lambda>(y, it'). I xs it' * \<up>(y = x)>"
      and "\<And>it. I [] it \<Longrightarrow>\<^sub>A Q"
      and "\<And>x b c. P x b \<Longrightarrow> <A b c> f x c <A (g b x)>"
      and "fold_pre P g b xs"
    shows "<I xs it * A b c> iter_fold has_next next f it c
           <\<lambda>c'. Q * A (foldl g b xs) c'>"
  using assms(5)
proof(induction xs arbitrary: it b c)
  case Nil
  show ?case
    by (subst iter_fold.simps, sep_auto heap: assms(1), sep_frame_fwd rule: assms(3), sep_auto)
next
  case (Cons x xs)
  thus ?case
    by (subst iter_fold.simps) (sep_auto heap: assms(1,2) assms(4)[of x b] Cons.IH)
qed

partial_function (heap) iter_find ::
  "('it \<Rightarrow> bool Heap) \<Rightarrow> ('it \<Rightarrow> ('a \<times> 'it) Heap) \<Rightarrow> ('a \<Rightarrow> 'b option Heap) \<Rightarrow>
   'it \<Rightarrow> ('a \<times> 'b) option Heap" where
  "iter_find has_next next f it =
     do { b \<leftarrow> has_next it;
          if b then do { (x, it') \<leftarrow> next it;
                         r \<leftarrow> f x;
                         (case r of None \<Rightarrow> iter_find has_next next f it'
                                  | Some y \<Rightarrow> return (Some (x, y))) }
          else return None }"

lemma iter_find_rule_gen:
  assumes "\<And>xs it. <I xs it> has_next it <\<lambda>r. I xs it * \<up>(r \<longleftrightarrow> xs \<noteq> [])>"
      and "\<And>x xs it. <I (x # xs) it> next it <\<lambda>(y, it'). I xs it' * \<up>(y = x)>"
      and "\<And>xs it. I xs it \<Longrightarrow>\<^sub>A Q"
      and "\<And>x s. \<lbrakk>x \<in> set xs; P s\<rbrakk> \<Longrightarrow>
             <A s> f x <\<lambda>r. A (fst (g s x)) * \<up>(rel_option Rel r (snd (g s x)))>"
      and "\<And>x s. \<lbrakk>x \<in> set xs; P s\<rbrakk> \<Longrightarrow> P (fst (g s x))"
      and "P s"
    shows "<I xs it * A s> iter_find has_next next f it
           <\<lambda>r. Q * A (fst (foldl (\<lambda>(s, r) x. case r of
                                None \<Rightarrow> (case g s x of (s', y) \<Rightarrow> (s', map_option (Pair x) y))
                              | Some _ \<Rightarrow> (s, r)) (s, None) xs)) *
                \<up>(rel_option (rel_prod (=) Rel) r
                   (snd (foldl (\<lambda>(s, r) x. case r of
                                  None \<Rightarrow> (case g s x of (s', y) \<Rightarrow> (s', map_option (Pair x) y))
                                | Some _ \<Rightarrow> (s, r)) (s, None) xs)))>"
  using assms(4-6)
proof(induction xs arbitrary: it s)
  case Nil
  show ?case
    by (subst iter_find.simps, sep_auto heap: assms(1), sep_frame_fwd rule: assms(3), sep_auto)
next
  case (Cons x xs)
  show ?case
    using Cons.prems(2)[of x s] Cons.prems(3)
    by (cases "g s x"; cases "snd (g s x)")
       (subst iter_find.simps, sep_auto heap: assms(1,2) Cons.prems(1)[of x s]
          Cons.IH[OF Cons.prems(1,2)[OF list.set_intros(2)]] simp: split_beta foldl_fixed,
        (sep_frame_fwd rule: assms(3), sep_auto)?)+
qed

context imp_set_ordered_iterate
begin

definition "set_fold p f c = do { it \<leftarrow> it_init p; iter_fold it_has_next it_next f it c }"

lemma iter_fold_rule:
  assumes "\<And>x b c. P x b \<Longrightarrow> <A b c> f x c <A (g b x)>"
      and "fold_pre P g b xs"
    shows "<is_it s p xs it * A b c> iter_fold it_has_next it_next f it c
           <\<lambda>c'. is_set s p * A (foldl g b xs) c'>"
  by (rule iter_fold_rule_gen[OF it_has_next_rule it_next_rule quit_iteration assms])

lemma set_fold_rule:
  assumes "\<And>x b c. P x b \<Longrightarrow> <A b c> f x c <A (g b x)>"
      and "fold_pre P g b (lst s)"
    shows "<is_set s p * A b c> set_fold p f c <\<lambda>c'. is_set s p * A (foldl g b (lst s)) c'>"
  unfolding set_fold_def
  by (sep_auto heap: iter_fold_rule[OF assms])

end

subsection \<open>Connection to the Functional ADTs\<close>

text \<open>A functional set @{term V} is represented by an imperative set of its elements. The
      functional type stays abstract; the relation goes through the abstraction function.\<close>

locale imp_set_conn =
  Set s_empty s_insert s_delete s_isin s_set s_invar +
  imp_set_memb is_set memb_imp +
  imp_set_ins is_set ins_imp +
  imp_set_clear is_set clear_imp +
  imp_set_ordered_iterate is_set lst is_it it_init it_has_next it_next
  for s_empty s_insert s_delete s_isin and s_set :: "'vset \<Rightarrow> 'a set" and s_invar
  and is_set :: "'a set \<Rightarrow> 's \<Rightarrow> assn" and memb_imp ins_imp clear_imp lst
  and is_it :: "'a set \<Rightarrow> 's \<Rightarrow> 'a list \<Rightarrow> 'it \<Rightarrow> assn" and it_init it_has_next it_next
begin

definition "set_assn V Vi = \<up>(s_invar V) * is_set (s_set V) Vi"

lemma set_assn_memb_rule[sep_heap_rules]:
  "<set_assn V Vi> memb_imp x Vi <\<lambda>r. set_assn V Vi * \<up>(r = s_isin V x)>"
  by (sep_auto simp: set_assn_def set_isin)

lemma set_assn_ins_rule[sep_heap_rules]:
  "<set_assn V Vi> ins_imp x Vi <set_assn (s_insert x V)>"
  by (sep_auto simp: set_assn_def set_insert invar_insert)

lemma set_assn_clear_rule[sep_heap_rules]:
  "<set_assn V Vi> clear_imp Vi <set_assn s_empty>"
  by (sep_auto simp: set_assn_def set_empty invar_empty)

lemma set_assn_fold_rule:
  assumes "\<And>x b c. P x b \<Longrightarrow> <A b c> f x c <A (g b x)>"
      and "fold_pre P g b (lst (s_set V))"
    shows "<set_assn V Vi * A b c> set_fold Vi f c
           <\<lambda>c'. set_assn V Vi * A (foldl g b (lst (s_set V))) c'>"
  unfolding set_assn_def
  by (sep_auto heap: set_fold_rule[OF assms])

end

text \<open>A functional map @{term m} is represented by an imperative map @{term mm} whose values are
      related to the functional ones by a relation @{term R}, which may depend on the key. This
      covers value abstractions (such as the embedding of the executable numbers into the reals)
      as well as additional data cached in the imperative values.\<close>

locale imp_map_conn =
  imp_map_lookup is_map lookup_imp +
  imp_map_update is_map update_imp
  for is_map :: "('k \<rightharpoonup> 'vi) \<Rightarrow> 'mi \<Rightarrow> assn" and lookup_imp update_imp +
  fixes m_update :: "'k \<Rightarrow> 'v \<Rightarrow> 'm \<Rightarrow> 'm"
    and m_lookup :: "'m \<Rightarrow> 'k \<Rightarrow> 'v option"
    and m_invar :: "'m \<Rightarrow> bool"
    and R :: "'k \<Rightarrow> 'vi \<Rightarrow> 'v \<Rightarrow> bool"
  assumes m_invar_update: "\<And>m k v. m_invar m \<Longrightarrow> m_invar (m_update k v m)"
      and m_lookup_update:
        "\<And>m k v. m_invar m \<Longrightarrow> m_lookup (m_update k v m) = (m_lookup m)(k \<mapsto> v)"
begin

definition "map_assn m mi =
   \<up>(m_invar m) * (\<exists>\<^sub>A mm. is_map mm mi * \<up>(\<forall>k. rel_option (R k) (mm k) (m_lookup m k)))"

lemma map_assn_lookup_rule[sep_heap_rules]:
  "<map_assn m mi> lookup_imp k mi <\<lambda>r. map_assn m mi * \<up>(rel_option (R k) r (m_lookup m k))>"
  by (sep_auto simp: map_assn_def)

lemma map_assn_update_rule[sep_heap_rules]:
  "R k vi v \<Longrightarrow> <map_assn m mi> update_imp k vi mi <map_assn (m_update k v m)>"
  by (sep_auto simp: map_assn_def m_lookup_update m_invar_update)

lemma map_assn_empty_eq:
  assumes "m_invar m" "\<And>k. m_lookup m k = None"
  shows "map_assn m mi = is_map Map.empty mi"
  using assms
  unfolding map_assn_def
  by (intro ent_iffI) (sep_auto simp: option.rel_sel Option.is_none_def fun_eq_iff[of _ Map.empty, symmetric])+

end

locale imp_map_conn_clear = imp_map_conn + imp_map_clear is_map clear_imp
  for clear_imp +
  fixes m_empty
  assumes m_invar_empty: "m_invar m_empty"
      and m_lookup_empty: "m_lookup m_empty = Map.empty"
begin

lemma map_assn_clear_rule[sep_heap_rules]:
  "<map_assn m mi> clear_imp mi <map_assn m_empty>"
  by (sep_auto simp: map_assn_def m_lookup_empty m_invar_empty)

end

text \<open>Every functional @{locale Map} satisfies the assumptions on the functional side.\<close>

lemma (in Map) imp_map_conn_axioms:
  "imp_map_conn_axioms update lookup invar"
  by (auto simp: imp_map_conn_axioms_def map_update invar_update)

lemma (in Map) imp_map_conn_clear_axioms:
  "imp_map_conn_clear_axioms lookup invar empty"
  by (auto simp: imp_map_conn_clear_axioms_def map_empty invar_empty)

end
