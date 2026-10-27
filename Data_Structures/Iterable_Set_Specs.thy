theory Iterable_Set_Specs
  imports Main
begin

locale iterable_set =
  fixes iterable_set_invar::"'iset \<Rightarrow> bool"
  and iterable_set_abstract::"'iset \<Rightarrow> 'a set"
  and current_element::"'iset \<Rightarrow> 'a"
  and has_current::"'iset \<Rightarrow> bool"
  and iterated::"'iset \<Rightarrow> 'a set"
  and remaining::"'iset \<Rightarrow> 'a set"
  and move_on::"'iset \<Rightarrow> 'iset"
assumes
  iterable_set_abstract:
    "\<And> S. iterable_set_invar S \<Longrightarrow>
      iterated S \<inter> remaining S = {}"
    "\<And> S. iterable_set_invar S \<Longrightarrow>
      iterated S \<union> remaining S = iterable_set_abstract S"
  and has_current:
   "\<And> S. iterable_set_invar S \<Longrightarrow> has_current S \<longleftrightarrow> remaining S \<noteq> {}" 
  and current_element:
    "\<And> S. \<lbrakk>iterable_set_invar S; remaining S \<noteq> {}\<rbrakk> \<Longrightarrow>
         current_element S \<in> remaining S"
  and move_on:
    "\<And> S. \<lbrakk>iterable_set_invar S; remaining S \<noteq> {}\<rbrakk> \<Longrightarrow>
      iterable_set_abstract (move_on S) = iterable_set_abstract S"
    "\<And> S. \<lbrakk>iterable_set_invar S; remaining S \<noteq> {}\<rbrakk> \<Longrightarrow>
      remaining (move_on S) = remaining S - {current_element S}"
    "\<And> S. \<lbrakk>iterable_set_invar S; remaining S \<noteq> {}\<rbrakk> \<Longrightarrow>
      iterated (move_on S) = iterated S \<union> {current_element S}"
  and move_on_invar:
    "\<And> S. \<lbrakk>iterable_set_invar S; remaining S \<noteq> {}\<rbrakk> \<Longrightarrow>
      iterable_set_invar (move_on S)"



section \<open>An Indexed Collection of Sets\<close>

text \<open>A collection of sets indexed by \<open>K\<close>. The features of such collections are specified in
      separate layers on top of the static description: folding over all elements of a set,
      iterating by a cursor, resetting a cursor, and setting a cursor to an element. The layers
      are independent, so a structure provides each feature under the weakest assumptions it
      needs, and an algorithm asks only for the features it uses. Layers that share operations
      are combined by locale expressions.\<close>

locale indexed_set_collection =
  fixes idx_invar     :: "'coll \<Rightarrow> bool"
    and idx_abstract  :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and K             :: "'i set"

subsection \<open>Folding over all elements\<close>

text \<open>A fold over the elements of a set. It visits them in some order, a list with the elements
      of the set, possibly with repetitions, which is the same for all folds over that set. The
      order is only said to exist: it is not a function of the locale.\<close>

locale indexed_set_fold =
  indexed_set_collection where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
  for idx_invar     :: "'coll \<Rightarrow> bool"
    and idx_abstract  :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and K             :: "'i set" +
  fixes idx_fold      :: "'coll \<Rightarrow> 'i \<Rightarrow>
                          ('a \<Rightarrow> 'acc \<Rightarrow> 'acc) \<Rightarrow> 'acc \<Rightarrow> 'acc"
  assumes idx_fold:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow>
         \<exists>xs. set xs = idx_abstract C i \<and>
           (\<forall>f acc. idx_fold C i f acc = foldl (\<lambda>acc x. f x acc) acc xs)"

subsection \<open>Iterating by a cursor\<close>

text \<open>Each set has a cursor that splits it into the iterated and the remaining elements.\<close>

locale indexed_set_cursor =
  indexed_set_collection where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
  for idx_invar     :: "'coll \<Rightarrow> bool"
    and idx_abstract  :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and K             :: "'i set" +
  fixes idx_current   :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a"
    and idx_has       :: "'coll \<Rightarrow> 'i \<Rightarrow> bool"
    and idx_iterated  :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_remaining :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_move      :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
  assumes idx_partition_disjoint:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow>
          idx_iterated C i \<inter> idx_remaining C i = {}"
    and idx_partition_union:
      "\<And>C i.\<lbrakk>idx_invar C; i \<in> K\<rbrakk>  \<Longrightarrow>
          idx_iterated C i \<union> idx_remaining C i = idx_abstract C i"
    and idx_has:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K\<rbrakk>  \<Longrightarrow>
          idx_has C i \<longleftrightarrow> idx_remaining C i \<noteq> {}"
    and idx_current:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K; idx_remaining C i \<noteq> {}\<rbrakk> \<Longrightarrow>
          idx_current C i \<in> idx_remaining C i"
    and idx_move_invar:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow> idx_invar (idx_move C i)"
    and idx_move_abstract:
      "\<And>C i j. \<lbrakk>idx_invar C; i \<in> K; idx_remaining C i \<noteq> {}\<rbrakk> \<Longrightarrow>
          idx_abstract (idx_move C i) j = idx_abstract C j"
    and idx_move_remaining:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K; idx_remaining C i \<noteq> {}\<rbrakk> \<Longrightarrow>
          idx_remaining (idx_move C i) i = idx_remaining C i - {idx_current C i}"
    and idx_move_iterated:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K; idx_remaining C i \<noteq> {}\<rbrakk> \<Longrightarrow>
          idx_iterated (idx_move C i) i = idx_iterated C i \<union> {idx_current C i}"
    and idx_move_remaining_other:
      "\<And>C i j. \<lbrakk>idx_invar C;i \<in> K; idx_remaining C i \<noteq> {};
          j \<noteq> i\<rbrakk> \<Longrightarrow> idx_remaining (idx_move C i) j = idx_remaining C j"
    and idx_move_iterated_other:
      "\<And>C i j. \<lbrakk>idx_invar C;i \<in> K; idx_remaining C i \<noteq> {};
          j \<noteq> i\<rbrakk> \<Longrightarrow> idx_iterated (idx_move C i) j = idx_iterated C j"

subsection \<open>Resetting a cursor\<close>

text \<open>After a reset, nothing of the set is iterated and all of it remains. This layer does not
      ask the iterated and the remaining elements to partition the set.\<close>

locale indexed_set_reset =
  indexed_set_collection where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
  for idx_invar     :: "'coll \<Rightarrow> bool"
    and idx_abstract  :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and K             :: "'i set" +
  fixes idx_iterated  :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_remaining :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_reset     :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
  assumes idx_reset_invar:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow> idx_invar (idx_reset C i)"
    and idx_reset_abstract:
      "\<And>C i j. \<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow>
          idx_abstract (idx_reset C i) j = idx_abstract C j"
    and idx_reset_iterated:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow> idx_iterated (idx_reset C i) i = {}"
    and idx_reset_remaining:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow>
          idx_remaining (idx_reset C i) i = idx_abstract C i"
    and idx_reset_remaining_other:
      "\<And>C i j. \<lbrakk>idx_invar C; i \<in> K; j \<noteq> i\<rbrakk> \<Longrightarrow>
          idx_remaining (idx_reset C i) j = idx_remaining C j"
    and idx_reset_iterated_other:
      "\<And>C i j. \<lbrakk>idx_invar C; i \<in> K; j \<noteq> i\<rbrakk> \<Longrightarrow>
          idx_iterated (idx_reset C i) j = idx_iterated C j"

subsection \<open>Iterable sets: cursor and reset\<close>

locale indexed_iterable_set =
  indexed_set_cursor where idx_invar = idx_invar and idx_abstract = idx_abstract
    and idx_current = idx_current and idx_has = idx_has and idx_iterated = idx_iterated
    and idx_remaining = idx_remaining and idx_move = idx_move and K = K +
  indexed_set_reset where idx_invar = idx_invar and idx_abstract = idx_abstract
    and idx_iterated = idx_iterated and idx_remaining = idx_remaining and idx_reset = idx_reset
    and K = K
  for idx_invar     :: "'coll \<Rightarrow> bool"
    and idx_abstract  :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_current   :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a"
    and idx_has       :: "'coll \<Rightarrow> 'i \<Rightarrow> bool"
    and idx_iterated  :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_remaining :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_move      :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and idx_reset     :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and K             :: "'i set"
begin

text \<open>The axioms only speak about indices in @{term K}, so they hold for every subset.\<close>

lemma indexed_iterable_set_restrict:
  "K' \<subseteq> K \<Longrightarrow> indexed_iterable_set idx_invar idx_abstract idx_current idx_has idx_iterated
     idx_remaining idx_move idx_reset K'"
  by (unfold_locales;
      (rule idx_partition_disjoint idx_partition_union idx_has idx_current idx_move_invar
            idx_move_abstract idx_move_remaining idx_move_iterated idx_move_remaining_other
            idx_move_iterated_other idx_reset_invar idx_reset_abstract idx_reset_iterated
            idx_reset_remaining idx_reset_remaining_other idx_reset_iterated_other;
       (assumption | erule subsetD)))

end

subsection \<open>Setting a cursor to an element\<close>

text \<open>A layer on top of the cursor layer @{locale indexed_set_cursor}: an operation that sets the
      cursor of an index to one of its elements \<open>x\<close>. Afterwards the cursor looks like any valid
      collection with the same elements at that index in which \<open>x\<close> is next: same iterated
      elements, same current element \<open>x\<close>, same remaining elements. Nothing is said about the
      order within the iterated or the remaining part.

      This presupposes that the iteration order at an index is the same for all valid
      collections with the same elements there, e.g. because the order is stored in a constant
      array and the collection only holds the cursors. An array implementation sets the cursor to
      the position of \<open>x\<close>, which it reads from a position array built once.\<close>

locale indexed_set_reset_to =
  indexed_set_cursor where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
    and idx_current = idx_current and idx_has = idx_has and idx_iterated = idx_iterated
    and idx_remaining = idx_remaining and idx_move = idx_move
  for idx_invar :: "'coll \<Rightarrow> bool"
    and idx_abstract :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and K :: "'i set"
    and idx_current :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a"
    and idx_has :: "'coll \<Rightarrow> 'i \<Rightarrow> bool"
    and idx_iterated :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_remaining :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_move :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll" +
  fixes idx_reset_to :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> 'coll"
  assumes idx_reset_to_invar:
      "\<And> C i x. \<lbrakk>idx_invar C; i \<in> K; x \<in> idx_abstract C i\<rbrakk> \<Longrightarrow>
         idx_invar (idx_reset_to C i x)"
    and idx_reset_to_abstract:
      "\<And> C i x j. \<lbrakk>idx_invar C; i \<in> K; x \<in> idx_abstract C i\<rbrakk> \<Longrightarrow>
         idx_abstract (idx_reset_to C i x) j = idx_abstract C j"
    and idx_reset_to_like:
      "\<And> C C' i x. \<lbrakk>idx_invar C; i \<in> K; idx_invar C'; idx_abstract C' i = idx_abstract C i;
         idx_has C' i; idx_current C' i = x\<rbrakk> \<Longrightarrow>
         idx_iterated (idx_reset_to C i x) i = idx_iterated C' i \<and>
         idx_has (idx_reset_to C i x) i \<and>
         idx_current (idx_reset_to C i x) i = x \<and>
         idx_remaining (idx_reset_to C i x) i = idx_remaining C' i"
    and idx_reset_to_iterated_other:
      "\<And> C i x j. \<lbrakk>idx_invar C; i \<in> K; x \<in> idx_abstract C i;
         j \<noteq> i\<rbrakk> \<Longrightarrow>
         idx_iterated (idx_reset_to C i x) j = idx_iterated C j"
    and idx_reset_to_remaining_other:
      "\<And> C i x j. \<lbrakk>idx_invar C; i \<in> K; x \<in> idx_abstract C i;
         j \<noteq> i\<rbrakk> \<Longrightarrow>
         idx_remaining (idx_reset_to C i x) j = idx_remaining C j"

subsection \<open>Iterable sets with both resets\<close>

locale indexed_iterable_set_reset_to =
  indexed_iterable_set where idx_invar = idx_invar
    and idx_abstract = idx_abstract
    and idx_current = idx_current
    and idx_has = idx_has
    and idx_iterated = idx_iterated
    and idx_remaining = idx_remaining
    and idx_move = idx_move
    and idx_reset = idx_reset
    and K = K +
  indexed_set_reset_to where idx_invar = idx_invar and idx_abstract = idx_abstract and K = K
    and idx_current = idx_current and idx_has = idx_has and idx_iterated = idx_iterated
    and idx_remaining = idx_remaining and idx_move = idx_move and idx_reset_to = idx_reset_to
  for idx_invar :: "'coll \<Rightarrow> bool"
    and idx_abstract :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_current :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a"
    and idx_has :: "'coll \<Rightarrow> 'i \<Rightarrow> bool"
    and idx_iterated :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_remaining :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_move :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and idx_reset :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and K :: "'i set"
    and idx_reset_to :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> 'coll"
end