theory More_Lists
  imports Main
begin

lemma list_2_preds_aux:
  "\<lbrakk>x' \<in> set xs; P1 x'; \<And>xs1 x xs2. \<lbrakk>xs = xs1 @ [x] @ xs2; P1 x\<rbrakk> \<Longrightarrow>
      \<exists>ys1 y ys2. x # xs2 = ys1 @ [y] @ ys2 \<and> P2 y\<rbrakk> \<Longrightarrow> 
     \<exists> xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
proof(goal_cases)
  case assms: 1

  define property 
       where "property xs \<equiv>
                (\<forall>xs2 xs1 x. (xs = xs1 @ [x] @ xs2 \<and> P1 x) \<longrightarrow>
                   (\<exists>ys1 y ys2. x#xs2 = ys1 @ [y] @ ys2 \<and> P2 y))"
       for xs

  have propE: "\<lbrakk>property xs;
               (\<And>xs1 x xs2. \<lbrakk>xs = xs1 @ [x] @ xs2; P1 x\<rbrakk> \<Longrightarrow>
                  \<exists>ys1 y ys2. x#xs2 = ys1 @ [y] @ ys2 \<and> P2 y) \<Longrightarrow> P\<rbrakk>
              \<Longrightarrow> P" for xs P
    by(auto simp add: property_def)

  have property_append: "property (xs @ ys) \<Longrightarrow> property ys" for xs ys
    by(auto simp: property_def)

  have "property xs"
    using assms(3)
    by (force simp: property_def)



  thus  ?thesis
    using assms(1,2)
  proof(induction xs arbitrary: x')
    case Nil
    then show ?case 
      by auto
  next
    case (Cons a xs)
    hence "property xs" 
      by(auto intro: property_append[where xs = "[a]"])

    show ?case
    proof(cases "x' = a")
      case x_eq_a: True

      then obtain ys1 y ys2 where "x'#xs = ys1 @ [y] @ ys2" "P2 y"
        using \<open>property (a # xs)\<close> \<open>P1 x'\<close>
        apply(elim propE)
        by (auto 10 10)

      show ?thesis
      proof(cases "ys1 = []")
        case ys1_empty: True
        hence "xs = ys2"
          using \<open>x'#xs = ys1 @ [y] @ ys2\<close>
          by auto
        then show ?thesis
        proof(cases "\<exists>x\<in>set ys2. P1 x")
          case x_in_ys2: True
          then obtain x where "x \<in> set ys2" "P1 x"
            by auto
          hence "\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            using \<open>property xs\<close> \<open>xs = ys2\<close> \<open>P2 y\<close>
            apply(intro Cons(1))
            by auto
          then obtain xs1 x xs2 where "(a # xs) = (a #xs1) @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            by auto
          then show ?thesis
            by metis
        next
          case x_notin_ys2: False
          hence "a # xs = a#ys2 \<and> P2 y \<and> (\<forall>y\<in>set ys2. \<not> P1 y)"
            using \<open>xs = ys2\<close> \<open>P2 y\<close>
            by auto
          then show ?thesis
            using \<open>x' # xs = ys1 @ [y] @ ys2\<close> x_eq_a
            by blast
        qed
      next
        case ys2_nempty: False
        then obtain ys1' where "xs = ys1' @ [y] @ ys2"
          using \<open>x'#xs = ys1 @ [y] @ ys2\<close>
          by (auto simp: neq_Nil_conv)
        show ?thesis
        proof(cases "\<exists>x\<in>set ys2. P1 x")
          case x_in_ys2: True
          then obtain x where "x \<in> set ys2" "P1 x"
            by auto
          hence "\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            using \<open>property xs\<close> \<open>xs = ys1' @ [y] @ ys2\<close> \<open>P2 y\<close>
            apply(intro Cons(1))
            by auto
          then obtain xs1 x xs2 where "(a # xs) = (a #xs1) @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
            by auto
          then show ?thesis
            by metis
        next
          case x_notin_ys2: False
          hence "a # xs = (a# ys1') @ [y] @ ys2 \<and> P2 y \<and> (\<forall>y\<in>set ys2. \<not> P1 y)"
            using \<open>xs = ys1' @ [y] @ ys2\<close> \<open>P2 y\<close>
            by auto
          then show ?thesis
            by metis
        qed
      qed
    next
      case x_neq_a: False
      hence "x' \<in> set xs"
        using Cons
        by auto
      then obtain xs1 x xs2 where "xs = xs1 @ [x] @ xs2" "P2 x" "(\<forall>y\<in>set xs2. \<not> P1 y)"
        using Cons \<open>property xs\<close>
        by blast
      hence "a # xs = (a # xs1) @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
        by auto
      thus ?thesis
        by metis
    qed
  qed
qed

lemma list_2_preds:
  "\<lbrakk> x\<in>set xs; P1 x; \<And>xs1 x xs2. \<lbrakk>xs = xs1 @ [x] @ xs2; P1 x\<rbrakk> \<Longrightarrow> \<exists>ys1 y ys2. x#xs2 = ys1 @ [y] @ ys2 \<and> P2 y\<rbrakk> \<Longrightarrow> 
     \<exists> xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y \<and> \<not> P2 y)"
proof(goal_cases)
  case assms: 1
  hence "\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> P2 x \<and> (\<forall>y\<in>set xs2. \<not> P1 y)"
    by (fastforce intro!: list_2_preds_aux)
  then obtain xs1 x xs2 where "xs = xs1 @ [x] @ xs2" "P2 x" "(\<forall>y\<in>set xs2. \<not> P1 y)"
    by auto
  hence "\<exists>ys1 y ys2. x # xs2 = ys1 @ [y] @ ys2 \<and> P2 y \<and> (\<forall>z\<in>set ys2. \<not> P2 z)"
    by (auto intro!: split_list_last_prop)
  then obtain ys1 y ys2 where "x # xs2 = ys1 @ [y] @ ys2" "P2 y" "(\<forall>z\<in>set ys2. \<not> P2 z)"
    by auto
  hence "(\<forall>z\<in>set ys2. \<not>P1 z \<and> \<not> P2 z)"
    using \<open>(\<forall>y\<in>set xs2. \<not> P1 y)\<close> \<open>P2 x\<close>
    by (metis Un_iff insert_iff list.simps(15) set_append)
  moreover have "xs = (xs1 @ ys1) @ [y] @ ys2"
    using \<open>xs = xs1 @ [x] @ xs2\<close> \<open>x # xs2 = ys1 @ [y] @ ys2\<close>
    by auto
  ultimately show ?case
    using \<open>P2 y\<close>
    by fastforce
qed

lemma list_inter_mem_iff: "set xs \<inter> s \<noteq> {} \<longleftrightarrow> (\<exists>xs1 x xs2. xs = xs1 @ [x] @ xs2 \<and> x \<in> s)"
  by (metis append.left_neutral append_Cons disjoint_iff in_set_conv_decomp)
end