theory Iterable_Set_Reset_To_Specs
  imports
    Iterable_Set_Specs
begin

section \<open>Indexed Iterable Sets with Jumping to an Element\<close>

text \<open>An extension of @{locale indexed_iterable_set} by an operation that sets the iterator of an
      index to one of its elements \<open>x\<close>. Afterwards the iterator looks like any valid collection
      with the same elements at that index in which \<open>x\<close> is next: same iterated elements, same
      current element \<open>x\<close>, same remaining elements. Nothing is said about the order within the
      iterated or the remaining part.

      This presupposes that the iteration order at an index is the same for all valid
      collections with the same elements there, e.g. because the order is stored in a constant
      array and the collection only holds the cursors. An array implementation sets the cursor to
      the position of \<open>x\<close>, which it reads from a position array built once.\<close>

locale indexed_iterable_set_reset_to =
  indexed_iterable_set where idx_invar = idx_invar
    and idx_abstract = idx_abstract
    and idx_current = idx_current
    and idx_has = idx_has
    and idx_iterated = idx_iterated
    and idx_remaining = idx_remaining
    and idx_move = idx_move
    and idx_reset = idx_reset
    and K = K
  for idx_invar :: "'coll \<Rightarrow> bool"
    and idx_abstract :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_current :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a"
    and idx_has :: "'coll \<Rightarrow> 'i \<Rightarrow> bool"
    and idx_iterated :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_remaining :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_move :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and idx_reset :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and K :: "'i set" +
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
      "\<And> C i x j. \<lbrakk>idx_invar C; i \<in> K; x \<in> idx_abstract C i; j \<noteq> i\<rbrakk> \<Longrightarrow>
         idx_iterated (idx_reset_to C i x) j = idx_iterated C j"
    and idx_reset_to_remaining_other:
      "\<And> C i x j. \<lbrakk>idx_invar C; i \<in> K; x \<in> idx_abstract C i; j \<noteq> i\<rbrakk> \<Longrightarrow>
         idx_remaining (idx_reset_to C i x) j = idx_remaining C j"

end
