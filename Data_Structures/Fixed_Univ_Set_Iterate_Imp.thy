theory Fixed_Univ_Set_Iterate_Imp
  imports
    Fixed_Univ_Set_Specs_Imp
    More_Lists
begin

section \<open>Ordered Iteration over Imperative Fixed-Universe Sets\<close>

text \<open>A fixed order of the elements of finite sets that is compatible with filtering.\<close>

locale set_order =
  fixes lst :: "'a set \<Rightarrow> 'a list"
  assumes lst_distinct: "finite S \<Longrightarrow> distinct (lst S)"
      and lst_set: "finite S \<Longrightarrow> set (lst S) = S"
      and lst_filter: "finite S \<Longrightarrow> lst (S \<inter> Collect P) = filter P (lst S)"

lemma sorted_list_of_set_order: "set_order sorted_list_of_set"
  by unfold_locales (auto intro!: sorted_distinct_set_unique sorted_wrt_filter)


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

subsection \<open>Iterators over Fixed-Universe Sets\<close>

text \<open>The iterator visits the elements of a set in the order @{term lst}. It is stated next to
      the set, which stays available during the iteration. The iterator assertion refers to the
      abstraction of the set only, so a representation that is determined up to its abstraction
      can be iterated. Leaving the iteration gives back exactly the set.\<close>

locale fixed_univ_set_iterate_imp =
  set_order lst
  for U :: "'a set" and set_invar :: "'set \<Rightarrow> bool" and set_abstract :: "'set \<Rightarrow> 'a set"
    and set_assn :: "'set \<Rightarrow> 'seti \<Rightarrow> assn" and lst :: "'a set \<Rightarrow> 'a list" +
  fixes is_it :: "'a set \<Rightarrow> 'seti \<Rightarrow> 'a list \<Rightarrow> 'it \<Rightarrow> assn"
    and it_init :: "'seti \<Rightarrow> 'it Heap"
    and it_has_next :: "'it \<Rightarrow> bool Heap"
    and it_next :: "'it \<Rightarrow> ('a \<times> 'it) Heap"
  assumes fixed_univ_set_universe: "set_invar S \<Longrightarrow> set_abstract S \<subseteq> U"
    and it_init_rule[sep_heap_rules]:
      "set_invar S \<Longrightarrow>
       <set_assn S Si> it_init Si
       <\<lambda>it. set_assn S Si * is_it (set_abstract S) Si (lst (set_abstract S)) it>"
    and it_next_rule[sep_heap_rules]:
      "<set_assn S Si * is_it (set_abstract S) Si (x # xs) it> it_next it
       <\<lambda>(y, it'). set_assn S Si * is_it (set_abstract S) Si xs it' * \<up>(y = x)>"
    and it_has_next_rule[sep_heap_rules]:
      "<set_assn S Si * is_it (set_abstract S) Si xs it> it_has_next it
       <\<lambda>r. set_assn S Si * is_it (set_abstract S) Si xs it * \<up>(r \<longleftrightarrow> xs \<noteq> [])>"
    and quit_iteration:
      "set_assn S Si * is_it (set_abstract S) Si xs it \<Longrightarrow>\<^sub>A set_assn S Si"

subsection \<open>Folds over Finite Sets\<close>

text \<open>An imperative fold @{term fld_imp} over the elements of @{term S}, whose own data are
      described by @{term M}, implements the functional fold @{term fld} for every step whose
      functional part preserves an invariant indexed by the set of elements visited so far. Thus a
      step may rely on visiting each element once.\<close>

definition set_fold_imp_rule ::
  "'a set \<Rightarrow> assn \<Rightarrow> (('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> unit Heap) \<Rightarrow> unit Heap) \<Rightarrow> bool"
  where
  "set_fold_imp_rule S M fld fld_imp \<longleftrightarrow>
     (\<forall> g g_imp P R acc. P {} acc \<longrightarrow>
        (\<forall> W a v. P W a \<longrightarrow> W \<subseteq> S \<longrightarrow> v \<in> S \<longrightarrow> v \<notin> W \<longrightarrow>
           P (insert v W) (g a v) \<and> <R a> g_imp v <\<lambda>_. R (g a v)>) \<longrightarrow>
        <M * R acc> fld_imp g_imp <\<lambda>_. M * R (fld g acc)>)"

lemma set_fold_imp_ruleI:
  assumes "\<And> g g_imp P R acc.
             \<lbrakk>P {} acc;
              \<And> W a v. \<lbrakk>P W a; W \<subseteq> S; v \<in> S; v \<notin> W\<rbrakk> \<Longrightarrow>
                P (insert v W) (g a v) \<and> <R a> g_imp v <\<lambda>_. R (g a v)>\<rbrakk> \<Longrightarrow>
             <M * R acc> fld_imp g_imp <\<lambda>_. M * R (fld g acc)>"
  shows "set_fold_imp_rule S M fld fld_imp"
  using assms
  by (unfold set_fold_imp_rule_def) blast

lemma set_fold_imp_ruleD:
  assumes "set_fold_imp_rule S M fld fld_imp" "P {} acc"
    "\<And> W a v. \<lbrakk>P W a; W \<subseteq> S; v \<in> S; v \<notin> W\<rbrakk> \<Longrightarrow>
       P (insert v W) (g a v) \<and> <R a> g_imp v <\<lambda>_. R (g a v)>"
  shows "<M * R acc> fld_imp g_imp <\<lambda>_. M * R (fld g acc)>"
  using assms
  by (unfold set_fold_imp_rule_def) blast

lemma fold_pre_visited:
  assumes "distinct xs" "set xs \<inter> W = {}" "W \<union> set xs \<subseteq> S" "P W b"
    "\<And> W a v. \<lbrakk>P W a; W \<subseteq> S; v \<in> S; v \<notin> W\<rbrakk> \<Longrightarrow> P (insert v W) (g a v)"
  shows "fold_pre (\<lambda> x b. \<exists> W. P W b \<and> W \<subseteq> S \<and> x \<in> S \<and> x \<notin> W) g b xs"
  using assms(1-4)
proof(induction xs arbitrary: W b)
  case (Cons x xs)
  have "fold_pre (\<lambda> x b. \<exists> W. P W b \<and> W \<subseteq> S \<and> x \<in> S \<and> x \<notin> W) g (g b x) xs"
    by (rule Cons.IH[of "insert x W"]) (use Cons.prems assms(5)[of W b x] in auto)
  with Cons.prems show ?case
    by auto
qed simp

lemma (in set_order) fold_pre_lst:
  "\<lbrakk>finite S; P {} b;
    \<And> W a v. \<lbrakk>P W a; W \<subseteq> S; v \<in> S; v \<notin> W\<rbrakk> \<Longrightarrow>
      P (insert v W) (g a v)\<rbrakk> \<Longrightarrow>
   fold_pre (\<lambda> x b. \<exists> W. P W b \<and> W \<subseteq> S \<and> x \<in> S \<and> x \<notin> W) g b (lst S)"
  by (rule fold_pre_visited[where W = "{}"]) (simp_all add: lst_distinct lst_set)
text \<open>The fold by an iterator over a set.\<close>

definition iter_set_fold_imp ::
  "('seti \<Rightarrow> 'it Heap) \<Rightarrow> ('it \<Rightarrow> bool Heap) \<Rightarrow> ('it \<Rightarrow> ('a \<times> 'it) Heap) \<Rightarrow> 'seti \<Rightarrow>
   ('a \<Rightarrow> unit Heap) \<Rightarrow> unit Heap" where
  "iter_set_fold_imp it_init has_next next Si g_imp =
     do { it \<leftarrow> it_init Si; iter_fold has_next next (\<lambda> x _. g_imp x) it () }"

lemma (in fixed_univ_set_iterate_imp) iter_set_fold_imp_rule:
  assumes "set_invar X" "finite (set_abstract X)"
  shows "set_fold_imp_rule (set_abstract X) (set_assn X Si)
           (\<lambda> g acc. foldl g acc (lst (set_abstract X)))
           (iter_set_fold_imp it_init it_has_next it_next Si)"
proof(rule set_fold_imp_ruleI)
  fix g P R and acc :: 'acc and g_imp :: "'a \<Rightarrow> unit Heap"
  assume "P {} acc"
    and step: "\<And> W a v. \<lbrakk>P W a; W \<subseteq> set_abstract X; v \<in> set_abstract X; v \<notin> W\<rbrakk> \<Longrightarrow>
                 P (insert v W) (g a v) \<and> <R a> g_imp v <\<lambda>_. R (g a v)>"
  have "<R b> g_imp x <\<lambda>_. R (g b x)>"
    if "\<exists> W. P W b \<and> W \<subseteq> set_abstract X \<and> x \<in> set_abstract X \<and> x \<notin> W" for x b
    using that step
    by auto
  moreover have "fold_pre (\<lambda> x b. \<exists> W. P W b \<and> W \<subseteq> set_abstract X \<and> x \<in> set_abstract X \<and> x \<notin> W)
                   g acc (lst (set_abstract X))"
    using \<open>P {} acc\<close> step assms(2)
    by (intro fold_pre_lst) auto
  ultimately show "<set_assn X Si * R acc> iter_set_fold_imp it_init it_has_next it_next Si g_imp
        <\<lambda>_. set_assn X Si * R (foldl g acc (lst (set_abstract X)))>"
    unfolding iter_set_fold_imp_def
    by (sep_auto heap: it_init_rule[OF assms(1)] iter_fold_rule_gen[where
          I = "\<lambda> xs it. set_assn X Si * is_it (set_abstract X) Si xs it" and A = "\<lambda> b (_::unit). R b"
          and P = "\<lambda> x b. \<exists> W. P W b \<and> W \<subseteq> set_abstract X \<and> x \<in> set_abstract X \<and> x \<notin> W",
          OF it_has_next_rule it_next_rule quit_iteration])
qed

end
