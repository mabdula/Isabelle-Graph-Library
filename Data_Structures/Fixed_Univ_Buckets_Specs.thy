theory Fixed_Univ_Buckets_Specs
  imports
    Main
begin

section \<open>Buckets over a Fixed Universe\<close>

text \<open>Elements of a fixed universe @{term U} distributed into buckets with keys from a fixed
      universe @{term K}; every element lies in at most one bucket. The abstraction maps an
      element to the key of its bucket, if any. An implementation may be one doubly-linked list
      per bucket, stored in successor and predecessor arrays over @{term U} and a head array over
      @{term K}, all allocated once. Moving all elements of one bucket into another then walks
      the first bucket to its tail and splices it into the second one.\<close>

locale fixed_univ_buckets =
  fixes U :: "'a set"
  and K :: "'k set"
  and buckets_invar :: "'b \<Rightarrow> bool"
  and buckets_abstract :: "'b \<Rightarrow> 'a \<Rightarrow> 'k option"
  and buckets_empty :: "'b"
  and buckets_insert :: "'b \<Rightarrow> 'a \<Rightarrow> 'k \<Rightarrow> 'b"
  and buckets_remove :: "'b \<Rightarrow> 'a \<Rightarrow> 'k \<Rightarrow> 'b"
  and buckets_pick :: "'b \<Rightarrow> 'k \<Rightarrow> 'a option"
  and buckets_move :: "'b \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> 'b"
  assumes buckets_universe:
      "\<And> B x k. \<lbrakk>buckets_invar B; buckets_abstract B x = Some k\<rbrakk> \<Longrightarrow> x \<in> U \<and> k \<in> K"
  and buckets_empty:
      "buckets_invar buckets_empty"
      "buckets_abstract buckets_empty = (\<lambda> x. None)"
  and buckets_insert:
      "\<And> B x k. \<lbrakk>buckets_invar B; x \<in> U; k \<in> K; buckets_abstract B x = None\<rbrakk> \<Longrightarrow>
          buckets_invar (buckets_insert B x k)"
      "\<And> B x k. \<lbrakk>buckets_invar B; x \<in> U; k \<in> K; buckets_abstract B x = None\<rbrakk> \<Longrightarrow>
          buckets_abstract (buckets_insert B x k) = (buckets_abstract B)(x := Some k)"
  and buckets_remove:
      "\<And> B x k. \<lbrakk>buckets_invar B; buckets_abstract B x = Some k\<rbrakk> \<Longrightarrow>
          buckets_invar (buckets_remove B x k)"
      "\<And> B x k. \<lbrakk>buckets_invar B; buckets_abstract B x = Some k\<rbrakk> \<Longrightarrow>
          buckets_abstract (buckets_remove B x k) = (buckets_abstract B)(x := None)"
  and buckets_pick:
      "\<And> B k. \<lbrakk>buckets_invar B; k \<in> K\<rbrakk> \<Longrightarrow>
          buckets_pick B k = None \<longleftrightarrow> (\<forall> x. buckets_abstract B x \<noteq> Some k)"
      "\<And> B k x. \<lbrakk>buckets_invar B; k \<in> K; buckets_pick B k = Some x\<rbrakk> \<Longrightarrow>
          buckets_abstract B x = Some k"
  and buckets_move:
      "\<And> B j j'. \<lbrakk>buckets_invar B; j \<in> K; j' \<in> K; j \<noteq> j'\<rbrakk> \<Longrightarrow>
          buckets_invar (buckets_move B j j')"
      "\<And> B j j'. \<lbrakk>buckets_invar B; j \<in> K; j' \<in> K; j \<noteq> j'\<rbrakk> \<Longrightarrow>
          buckets_abstract (buckets_move B j j') =
          (\<lambda> x. if buckets_abstract B x = Some j then Some j' else buckets_abstract B x)"

text \<open>Restricting the elements to a smaller universe @{term U'}: the invariant additionally
      requires that only elements of @{term U'} lie in buckets.\<close>

definition "restr_buckets_invar U' buckets_invar buckets_abstract B =
  (buckets_invar B \<and> (\<forall> x k. buckets_abstract B x = Some k \<longrightarrow> x \<in> U'))"

lemma (in fixed_univ_buckets) fixed_univ_buckets_restrict:
  assumes "U' \<subseteq> U"
  shows "fixed_univ_buckets U' K (restr_buckets_invar U' buckets_invar buckets_abstract)
           buckets_abstract buckets_empty buckets_insert buckets_remove buckets_pick buckets_move"
proof(unfold_locales, goal_cases)
  case (1 B x k) then show ?case
    using buckets_universe by (auto simp add: restr_buckets_invar_def)
next
  case 2 show ?case
    using buckets_empty by (simp add: restr_buckets_invar_def)
next
  case 3 show ?case
    using buckets_empty by simp
next
  case (4 B x k)
  have "x \<in> U"
    using 4 assms by auto
  thus ?case
    using 4 buckets_insert[of B x k] by (auto simp add: restr_buckets_invar_def split: if_splits)
next
  case (5 B x k)
  have "x \<in> U"
    using 5 assms by auto
  thus ?case
    using 5 buckets_insert(2)[of B x k] by (simp add: restr_buckets_invar_def)
next
  case (6 B x k) then show ?case
    using buckets_remove[of B x k] by (auto simp add: restr_buckets_invar_def)
next
  case (7 B x k) then show ?case
    using buckets_remove(2)[of B x k] by (simp add: restr_buckets_invar_def)
next
  case (8 B k) then show ?case
    using buckets_pick(1)[of B k] by (simp add: restr_buckets_invar_def)
next
  case (9 B k x) then show ?case
    using buckets_pick(2)[of B k x] by (simp add: restr_buckets_invar_def)
next
  case (10 B j j') then show ?case
    using buckets_move[of B j j'] by (auto simp add: restr_buckets_invar_def split: if_splits)
next
  case (11 B j j') then show ?case
    using buckets_move(2)[of B j j'] by (simp add: restr_buckets_invar_def)
qed

end

