theory Alternating_Forest_Imperative_Spec
  imports
    Basic_Matching.Alternating_Forest_Spec
    Data_Structures.Fixed_Univ_Set_Iterate_Imp
begin

section \<open>Imperative Alternating Forests\<close>

text \<open>The functional specification of alternating forests with ordinary extensions,
      @{locale alternating_forest_ordinary_extension_spec}, is extended by a representation
      assertion @{term forest_assn} and imperative operations. The functional types of forests
      and vertex sets stay abstract.

        \<^item> The forest is cleared in place and then built up from its roots, one root at a time.
          The functional forest is @{term \<open>empty_forest R\<close>} for the set of roots @{term R}; the
          representation after adding a root only depends on the elements of @{term R}.
        \<^item> The even and the odd vertices can be iterated in the order @{term lst}, each by an
          ordered set iterator (@{locale fixed_univ_set_iterate_imp}) over the forest.
        \<^item> @{term get_path_imp} writes the path of the forest from an even vertex to its root into an
          array at a given position and returns the position after the path. It does not
          allocate: the array belongs to the caller.

      The only allocating operation is @{term forest_empty_imp}, which is used during
      initialisation only.\<close>

datatype forest_part = Evens | Odds

locale alternating_forest_imp_spec =
  alternating_forest_ordinary_extension_spec
    where evens = evens and get_path = get_path +
  set_order lst +
  ev: fixed_univ_set_iterate_imp forest_univ "\<lambda> F. vset_invar (evens F)"
    "\<lambda> F. vset_to_set (evens F)" forest_assn lst "forest_is_it Evens" "forest_it_init Evens"
    forest_it_has_next forest_it_next +
  od: fixed_univ_set_iterate_imp forest_univ "\<lambda> F. vset_invar (odds F)"
    "\<lambda> F. vset_to_set (odds F)" forest_assn lst "forest_is_it Odds" "forest_it_init Odds"
    forest_it_has_next forest_it_next
  for get_path :: "'forest \<Rightarrow> 'v::heap \<Rightarrow> 'v list" and evens :: "'forest \<Rightarrow> 'vset"
    and lst :: "'v set \<Rightarrow> 'v list"
    and forest_assn :: "'forest \<Rightarrow> 'fi \<Rightarrow> assn"
    and forest_is_it :: "forest_part \<Rightarrow> 'v set \<Rightarrow> 'fi \<Rightarrow> 'v list \<Rightarrow> 'fit \<Rightarrow> assn"
    and forest_it_init :: "forest_part \<Rightarrow> 'fi \<Rightarrow> 'fit Heap"
    and forest_it_has_next :: "'fit \<Rightarrow> bool Heap"
    and forest_it_next :: "'fit \<Rightarrow> ('v \<times> 'fit) Heap" +
  fixes forest_empty_imp :: "'fi Heap"
    and forest_clear_imp :: "'fi \<Rightarrow> 'fi Heap"
    and forest_add_root_imp :: "'v \<Rightarrow> 'fi \<Rightarrow> 'fi Heap"
    and forest_extend_imp :: "'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'fi \<Rightarrow> 'fi Heap"
    and evens_memb_imp :: "'v \<Rightarrow> 'fi \<Rightarrow> bool Heap"
    and odds_memb_imp :: "'v \<Rightarrow> 'fi \<Rightarrow> bool Heap"
    and get_path_imp :: "'fi \<Rightarrow> 'v array \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> nat Heap"
  assumes forest_empty_rule[sep_heap_rules]:
      "\<lbrakk>vset_invar R; vset_to_set R = {}\<rbrakk> \<Longrightarrow>
       <emp> forest_empty_imp <forest_assn (empty_forest R)>"
    and forest_clear_rule[sep_heap_rules]:
      "\<lbrakk>vset_invar R; vset_to_set R = {}\<rbrakk> \<Longrightarrow>
       <forest_assn F Fi> forest_clear_imp Fi <forest_assn (empty_forest R)>"
    and forest_empty_cong:
      "\<lbrakk>vset_invar R; vset_invar R'; vset_to_set R = vset_to_set R'\<rbrakk> \<Longrightarrow>
       forest_assn (empty_forest R) = forest_assn (empty_forest R')"
    and forest_add_root_rule[sep_heap_rules]:
      "\<lbrakk>vset_invar R; vset_invar R'; vset_to_set R' = insert v (vset_to_set R)\<rbrakk> \<Longrightarrow>
       <forest_assn (empty_forest R) Fi> forest_add_root_imp v Fi
       <forest_assn (empty_forest R')>"
    and forest_extend_rule[sep_heap_rules]:
      "forest_extension_precond F M x y z \<Longrightarrow>
       <forest_assn F Fi> forest_extend_imp x y z Fi
       <forest_assn (extend_forest_even_unclassified F x y z)>"
    and evens_memb_rule[sep_heap_rules]:
      "v \<in> forest_univ \<Longrightarrow>
       <forest_assn F Fi> evens_memb_imp v Fi
       <\<lambda>r. forest_assn F Fi * \<up>(r \<longleftrightarrow> v \<in> vset_to_set (evens F))>"
    and odds_memb_rule[sep_heap_rules]:
      "v \<in> forest_univ \<Longrightarrow>
       <forest_assn F Fi> odds_memb_imp v Fi
       <\<lambda>r. forest_assn F Fi * \<up>(r \<longleftrightarrow> v \<in> vset_to_set (odds F))>"
    and get_path_rule[sep_heap_rules]:
      "\<lbrakk>forest_invar M F; v \<in> vset_to_set (evens F); k + length (get_path F v) \<le> length xs\<rbrakk> \<Longrightarrow>
       <forest_assn F Fi * Ra \<mapsto>\<^sub>a xs> get_path_imp Fi Ra k v
       <\<lambda>k'. forest_assn F Fi * Ra \<mapsto>\<^sub>a (take k xs @ get_path F v @ drop k' xs) *
             \<up>(k' = k + length (get_path F v))>"
begin

definition "part_set F p = vset_to_set (case p of Evens \<Rightarrow> evens F | Odds \<Rightarrow> odds F)"

definition "forest_fold p Fi f c =
  do { it \<leftarrow> forest_it_init p Fi; iter_fold forest_it_has_next forest_it_next f it c }"

lemma forest_fold_rule:
  assumes inv: "vset_invar (case p of Evens \<Rightarrow> evens F | Odds \<Rightarrow> odds F)"
      and step: "\<And>x b c. P x b \<Longrightarrow> <A b c> f x c <A (g b x)>"
      and pre: "fold_pre P g b (lst (part_set F p))"
    shows "<forest_assn F Fi * A b c> forest_fold p Fi f c
           <\<lambda>c'. forest_assn F Fi * A (foldl g b (lst (part_set F p))) c'>"
proof-
  have init: "<forest_assn F Fi> forest_it_init p Fi
              <\<lambda>it. forest_assn F Fi * forest_is_it p (part_set F p) Fi (lst (part_set F p)) it>"
    using inv by (cases p) (auto simp: part_set_def intro: ev.it_init_rule od.it_init_rule)
  have has_next: "<forest_assn F Fi * forest_is_it p (part_set F p) Fi xs it> forest_it_has_next it
                  <\<lambda>r. forest_assn F Fi * forest_is_it p (part_set F p) Fi xs it *
                       \<up>(r \<longleftrightarrow> xs \<noteq> [])>" for xs it
    by (cases p) (auto simp: part_set_def intro: ev.it_has_next_rule od.it_has_next_rule)
  have nxt: "<forest_assn F Fi * forest_is_it p (part_set F p) Fi (x # xs) it> forest_it_next it
             <\<lambda>(y, it'). forest_assn F Fi * forest_is_it p (part_set F p) Fi xs it' * \<up>(y = x)>"
    for x xs it
    by (cases p) (auto simp: part_set_def intro: ev.it_next_rule od.it_next_rule)
  have quit: "forest_assn F Fi * forest_is_it p (part_set F p) Fi xs it \<Longrightarrow>\<^sub>A forest_assn F Fi"
    for xs it
    by (cases p) (auto simp: part_set_def intro: ev.quit_iteration od.quit_iteration)
  show ?thesis
    unfolding forest_fold_def
    by (sep_auto heap: init iter_fold_rule_gen[where I = "\<lambda>xs it. forest_assn F Fi *
                         forest_is_it p (part_set F p) Fi xs it", OF has_next nxt quit step pre])
qed

end

end
