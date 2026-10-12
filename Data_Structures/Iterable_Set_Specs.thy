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



section \<open>An Indexed Collection of Iterable Sets\<close>

locale indexed_iterable_set =
  fixes idx_invar     :: "'coll \<Rightarrow> bool"
    and idx_abstract  :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_current   :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a"
    and idx_has       :: "'coll \<Rightarrow> 'i \<Rightarrow> bool"
    and idx_iterated  :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_remaining :: "'coll \<Rightarrow> 'i \<Rightarrow> 'a set"
    and idx_move      :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and idx_reset     :: "'coll \<Rightarrow> 'i \<Rightarrow> 'coll"
    and K             :: "'i set"
  assumes idx_partition_disjoint:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow> idx_iterated C i \<inter> idx_remaining C i = {}"
    and idx_partition_union:
      "\<And>C i.\<lbrakk>idx_invar C; i \<in> K\<rbrakk>  \<Longrightarrow> idx_iterated C i \<union> idx_remaining C i = idx_abstract C i"
    and idx_has:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K\<rbrakk>  \<Longrightarrow> idx_has C i \<longleftrightarrow> idx_remaining C i \<noteq> {}"
    and idx_current:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K; idx_remaining C i \<noteq> {}\<rbrakk> \<Longrightarrow> idx_current C i \<in> idx_remaining C i"
    and idx_move_invar:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow> idx_invar (idx_move C i)"
    and idx_move_abstract:
      "\<And>C i j. \<lbrakk>idx_invar C; i \<in> K; idx_remaining C i \<noteq> {}\<rbrakk> \<Longrightarrow> idx_abstract (idx_move C i) j = idx_abstract C j"
    and idx_move_remaining:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K; idx_remaining C i \<noteq> {}\<rbrakk> \<Longrightarrow> idx_remaining (idx_move C i) i = idx_remaining C i - {idx_current C i}"
    and idx_move_iterated:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K; idx_remaining C i \<noteq> {}\<rbrakk> \<Longrightarrow> idx_iterated (idx_move C i) i = idx_iterated C i \<union> {idx_current C i}"
    and idx_move_remaining_other:
      "\<And>C i j. \<lbrakk>idx_invar C;i \<in> K; idx_remaining C i \<noteq> {}; j \<noteq> i\<rbrakk> \<Longrightarrow> idx_remaining (idx_move C i) j = idx_remaining C j"
    and idx_move_iterated_other:
      "\<And>C i j. \<lbrakk>idx_invar C;i \<in> K; idx_remaining C i \<noteq> {}; j \<noteq> i\<rbrakk> \<Longrightarrow> idx_iterated (idx_move C i) j = idx_iterated C j"
    and idx_reset_invar:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow> idx_invar (idx_reset C i)"
    and idx_reset_abstract:
      "\<And>C i j. \<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow> idx_abstract (idx_reset C i) j = idx_abstract C j"
    and idx_reset_iterated:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow> idx_iterated (idx_reset C i) i = {}"
    and idx_reset_remaining:
      "\<And>C i. \<lbrakk>idx_invar C; i \<in> K\<rbrakk> \<Longrightarrow> idx_remaining (idx_reset C i) i = idx_abstract C i"
    and idx_reset_remaining_other:
      "\<And>C i j. \<lbrakk>idx_invar C; i \<in> K; j \<noteq> i\<rbrakk> \<Longrightarrow> idx_remaining (idx_reset C i) j = idx_remaining C j"
    and idx_reset_iterated_other:
      "\<And>C i j. \<lbrakk>idx_invar C; i \<in> K; j \<noteq> i\<rbrakk> \<Longrightarrow> idx_iterated (idx_reset C i) j = idx_iterated C j"
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
end