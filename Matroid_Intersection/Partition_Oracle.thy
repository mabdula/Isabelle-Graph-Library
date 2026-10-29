theory Partition_Oracle
  imports Exchange_Oracles
begin

section \<open>Oracles for Unit Partition Matroids\<close>

text \<open>The carrier is partitioned into blocks by \<open>blk\<close>. A set is independent iff it 
  contains at most one element per block. The prepared context is the set of covered 
  blocks, the insertion query is a membership test and the exchange query (only asked 
  for a dependent \<open>X + y\<close>) compares two blocks.\<close>

subsection \<open>The Matroid\<close>

locale unit_partition_matroid =
  fixes carrier :: "'a set"
    and blk :: "'a \<Rightarrow> 'b"
  assumes carrier_finite: "finite carrier"
begin

definition "part_indep X = (X \<subseteq> carrier \<and> inj_on blk X)"

lemma part_matroid: "matroid carrier part_indep"
proof(unfold_locales, goal_cases)
  case (5 X Y)
  hence "\<not> blk ` X \<subseteq> blk ` Y"
    using carrier_finite card_mono[of "blk ` Y" "blk ` X"]
    by (auto simp: part_indep_def card_image intro: finite_subset)
  then obtain x where "x \<in> X" "blk x \<notin> blk ` Y"
    by blast
  thus ?case
    using 5
    by (auto simp: part_indep_def)
qed (auto simp: part_indep_def carrier_finite intro: inj_on_subset)

sublocale part: matroid carrier part_indep
  by (rule part_matroid)

lemma part_indep_insert:
  "\<lbrakk>part_indep X; y \<in> carrier - X\<rbrakk> \<Longrightarrow>
     part_indep (insert y X) \<longleftrightarrow> blk y \<notin> blk ` X"
  by (simp add: part_indep_def Diff_triv)

lemma part_indep_exch:
  "\<lbrakk>part_indep X; y \<in> carrier - X; x \<in> X; blk y \<in> blk ` X\<rbrakk> \<Longrightarrow>
     part_indep (insert y (X - {x})) \<longleftrightarrow> blk x = blk y"
  by (auto simp: part_indep_def inj_on_def)

end

subsection \<open>The Oracle\<close>

locale unit_partition_oracle_spec =
  fixes blk :: "'a \<Rightarrow> 'b"
    and to_list :: "'mset \<Rightarrow> 'a list"
    and bset_empty :: "'bset"
    and bset_insert :: "'b \<Rightarrow> 'bset \<Rightarrow> 'bset"
    and bset_memb :: "'b \<Rightarrow> 'bset \<Rightarrow> bool"
begin

definition "part_prep X = foldr (\<lambda> x. bset_insert (blk x)) (to_list X) bset_empty"
definition "part_ins c y = (\<not> bset_memb (blk y) c)"
definition "part_exch (c::'bset) x y = (blk x = blk y)"

end

lemmas [code] = unit_partition_oracle_spec.part_prep_def unit_partition_oracle_spec.part_ins_def
  unit_partition_oracle_spec.part_exch_def

locale unit_partition_oracle =
  unit_partition_oracle_spec blk to_list bset_empty bset_insert bset_memb +
  unit_partition_matroid carrier blk +
  set_insert_spec bset_inv bset_abs bset_empty bset_insert
  for blk :: "'a \<Rightarrow> 'b"
    and to_list :: "'mset \<Rightarrow> 'a list"
    and bset_empty :: "'bset"
    and bset_insert :: "'b \<Rightarrow> 'bset \<Rightarrow> 'bset"
    and bset_memb :: "'b \<Rightarrow> 'bset \<Rightarrow> bool"
    and carrier :: "'a set"
    and to_set :: "'mset \<Rightarrow> 'a set"
    and set_invar :: "'mset \<Rightarrow> bool"
    and bset_inv :: "'bset \<Rightarrow> bool"
    and bset_abs :: "'bset \<Rightarrow> 'b set" +
  assumes to_list: "\<And> X. set_invar X \<Longrightarrow> set (to_list X) = to_set X"
  assumes bset_memb: "\<And> s b. bset_inv s \<Longrightarrow> bset_memb b s \<longleftrightarrow> b \<in> bset_abs s"
begin

lemma part_prep:
  "set_invar X \<Longrightarrow> bset_inv (part_prep X)"
  "set_invar X \<Longrightarrow> bset_abs (part_prep X) = blk ` to_set X"
  by (simp_all add: part_prep_def foldr_bset flip: to_list)

lemma part_ins:
  "set_invar X \<Longrightarrow> part_ins (part_prep X) y \<longleftrightarrow> blk y \<notin> blk ` to_set X"
  by (simp add: part_ins_def bset_memb part_prep)

sublocale indep_oracle part_prep part_ins part_exch carrier part_indep to_set set_invar
  by unfold_locales (auto simp: part_indep_insert part_ins part_indep_exch part_exch_def)

end

end
