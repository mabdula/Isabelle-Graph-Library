theory Bipartite_Matchings_Existence
  imports Basic_Matching.Berge "HOL.Set" Alternating_Lists.Bipartite_Alternating_Lists
begin

section \<open>Existence of Certain Matchings in Bipartite Graphs\<close>

subsection \<open>Existence of One-Sided Cover Matchings: Hall's Theorem\<close>

lemma hall1:
  fixes G :: "'a set set"
  assumes "cover_matching G M A" "graph_invar G"
  shows "\<forall> X \<subseteq> A. card (neighbours_of_Vs G X) \<ge> card X"
proof rule+
  fix X
  assume "X \<subseteq> A"
  show "card X \<le> card (neighbours_of_Vs G X)"
  proof -
    have 1:"finite (neighbours_of_Vs M X)" 
      by (meson assms cover_matching_def finite_neighbours_of_Vs)
    have "G \<subseteq> G" by auto
    then have 2:"finite (neighbours_of_Vs G X)"
      by (meson assms cover_matching_def finite_neighbours_of_Vs)
    have "neighbours_of_Vs M X \<subseteq> neighbours_of_Vs G X" 
      by (meson assms cover_matching_def graph_subs_reach)
    then have 3: "card (neighbours_of_Vs M X) \<le> card (neighbours_of_Vs G X)" using 1 2 
      by (simp add: card_mono)
    have "card X = card (neighbours_of_Vs M X)" 
      by (metis \<open>X \<subseteq> A\<close> assms cover_matching_neighbours_of_Vs_card)
    then show ?thesis using 3 by auto
  qed
qed

lemma hall2:
  fixes G :: "'a set set"
  assumes "partitioned_bipartite G A"
  assumes  "\<forall> X \<subseteq> A. card (neighbours_of_Vs G X) \<ge> card X"
  assumes "graph_invar G"
  shows  "\<exists> M. cover_matching G M A"
  using assms
proof(induct "card A" arbitrary: A G rule: less_induct)
  case less
  have graphE: "graph_invar G" 
    using less.prems(1,3) unfolding partitioned_bipartite_def 
    by linarith
  have Asubs: "A \<subseteq> Vs G" 
    using less.prems(1) unfolding partitioned_bipartite_def
    by linarith
  then show ?case
  proof(cases "\<forall> X \<subset> A. X \<noteq> {} \<longrightarrow>  card (neighbours_of_Vs G X) > card X")
    case True
    have 7:"\<forall> X \<subset> A. X \<noteq> {} \<longrightarrow> card (neighbours_of_Vs G X) > card X"
      by (simp add: True)
    then show ?thesis
    proof (cases "G = {}") 
      case True
      then show ?thesis 
        by (metis cover_matching_def equals0D graphE Asubs matching_def subset_empty)
    next
      case False
      have "\<exists> e. e \<in> G" 
        using False by blast
      then obtain e where e:"\<exists>u v. e \<in> G \<and> e = {u, v} \<and> u \<in> A \<and> v \<in> Vs G - A"
        by (metis less.prems(1) partitioned_bipartite_def)
      then obtain u v where u_v: "e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs G - A)" 
        by auto
      then  have "(u \<in> A \<and> v \<in> Vs G - A)" by auto
      have " {u, v} \<in> G" using e u_v by fastforce
      let ?E_s = "G - {e. e \<in> G \<and> (u \<in> e \<or> v \<in> e)}"

      let ?A_s = "A \<inter> Vs ?E_s"
      let ?B_s = "Vs ?E_s - ?A_s"
      have 0:"?E_s \<subseteq> G" 
        by force
      have "u \<notin> Vs ?E_s"
        by (smt (verit, best) DiffD1 DiffD2 mem_Collect_eq vs_member)
      then have "u \<notin> ?A_s" by auto
      have "v \<notin> Vs ?E_s"
        by (smt (verit, best) DiffD1 DiffD2 mem_Collect_eq vs_member)
      then have "v \<notin> ?B_s" by auto
      have "card ?A_s < card A" 
        by (smt (verit, best) DiffD1 DiffD2 IntE \<open>u \<in> A \<and> v \<in> Vs G - A\<close> finite_subset inf_le1 
            graphE Asubs mem_Collect_eq psubsetI psubset_card_mono vs_member)

      have "partitioned_bipartite ?E_s ?A_s"
        using less.prems(1,3) part_bipartite_diff by blast
      then have graph_E': "graph_invar ?E_s" 
        using less.prems(3) graph_invar_diff
        by auto
      have "neighbours_of_Vs ?E_s ?A_s = Vs ?E_s - ?A_s" 
        using part_bipartite_diff
        by (metis (no_types, lifting) less.prems(1,3) neighbours_of_Vs_bipartite) 
      have 6:"?A_s \<subset> A" 
        using \<open>card ?A_s < card A\<close> by fastforce

      have " \<forall>X\<subseteq>?A_s. card X \<le> card (neighbours_of_Vs ?E_s X)" 
      proof rule+
        fix X
        assume "X \<subseteq> ?A_s"
        then  have " X \<subset> A" using 6
          by (meson subset_psubset_trans)
        show "card X \<le> card (neighbours_of_Vs ?E_s X)"
        proof(cases "X = {}")
          case True
          then show ?thesis 
            by simp
        next
          case False
          have "X \<noteq> {}" 
            by (simp add: False)
          then have "card X < card (neighbours_of_Vs G X)"
            by (simp add: "7" `X \<noteq> {}` `X \<subset> A`)
          then have "card X \<le> card (neighbours_of_Vs G X) - 1" 
            by linarith
          have "finite (neighbours_of_Vs G X)" 
            using finite_neighbours_of_Vs graphE by auto

          have "(neighbours_of_Vs ?E_s X) \<subseteq> (neighbours_of_Vs G X)" 
            unfolding neighbours_of_Vs_def
            using 0 by blast

          have "{u, v} \<inter> X = {}" 
            by (metis (no_types, lifting) DiffD2 Int_ac(3) Int_subset_iff 
                \<open>X \<subseteq> ?A_s\<close> \<open>u \<notin> ?A_s\<close> disjoint_insert(1) inf_bot_right subsetD u_v)

          then have "neighbours_of_Vs G X \<subseteq> {u,v} \<union> neighbours_of_Vs ?E_s X" 
            using neighbours_of_Vs_remove_vert[of G "{u,v}" X] 
            using `{u, v} \<inter> X = {}` graphE
            by auto
          have "neighbours_of_Vs G A \<subseteq> Vs G - A" 
            by (simp add: less.prems(1) neighbours_of_Vs_bipartite)

          then have "u \<notin> neighbours_of_Vs G X" using neighbours_of_Vs_subset[of X A G]  
            using \<open>X \<subset> A\<close> \<open>u \<in> A \<and> v \<in> Vs G - A\<close> by blast

          then have "neighbours_of_Vs G X \<subseteq> {v} \<union> neighbours_of_Vs ?E_s X"  
            using \<open>neighbours_of_Vs G X \<subseteq> {u, v} \<union> neighbours_of_Vs (G - {e \<in> G. u \<in> e \<or> v \<in> e}) X\<close> by fastforce

          then have "card (neighbours_of_Vs G X) - 1 \<le> card (neighbours_of_Vs ?E_s X)"
            by (smt (z3) \<open>finite (neighbours_of_Vs G X)\<close> \<open>neighbours_of_Vs (G - {e \<in> G. u \<in> e \<or> v \<in> e}) X \<subseteq> neighbours_of_Vs G X\<close> card_Diff_singleton diff_le_self insert_is_Un insert_subset order_refl subset_antisym subset_insert_iff)

          then show " card X \<le> card (neighbours_of_Vs ?E_s X)" 
            using \<open>card X \<le> card (neighbours_of_Vs G X) - 1\<close> le_trans by blast
        qed
      qed
      then have " \<exists>M. cover_matching ?E_s M ?A_s" 
        using graph_E' \<open>card ?A_s < card A\<close> \<open>partitioned_bipartite ?E_s ?A_s\<close> less.hyps by auto
      then  obtain M where "cover_matching ?E_s M ?A_s" by auto

      have "?A_s = A - {u}" 
      proof - 
        have " A - {u} \<subseteq> Vs ?E_s" 
        proof
          fix a 
          assume "a \<in> A - {u}"
          then have "{a} \<subset> A" 
            using \<open>u \<in> A \<and> v \<in> Vs G - A\<close> by blast
          then have "card (neighbours_of_Vs G {a}) > card {a}" 
            using "7" by blast
          then have "card (neighbours_of_Vs G {a}) \<ge> 2" 
            by simp
          then obtain v1 v2 where v1_v2:"v1 \<noteq> v2 \<and> v1 \<in> neighbours_of_Vs G {a} \<and> v2 \<in> neighbours_of_Vs G {a}"
            by (metis One_nat_def card.infinite card_le_Suc0_iff_eq not_less_eq_eq numerals(2) 
                order_less_imp_le zero_less_one)
          then have "v1 \<noteq> v \<or> v2 \<noteq> v" 
            by blast
          then have "\<exists> v'. v' \<noteq> v \<and> (\<exists> u \<in> {a}. \<exists> e \<in> G. v' \<noteq> u \<and> u \<in> e \<and> v' \<in> e)"
            by (smt (verit, ccfv_SIG) v1_v2 mem_Collect_eq neighbours_of_Vs_def)
          then obtain v' e' where v'_e: "v' \<noteq> v \<and> e' \<in> G \<and>  v' \<noteq> a \<and> a \<in> e' \<and> v' \<in> e'" 
            by blast
          then have "e' = {a, v'}"
            using graphE by fastforce
          then have "a \<in> A \<and> v' \<in> Vs G - A"
            using `partitioned_bipartite G A` 
            unfolding partitioned_bipartite_def neighbours_of_Vs_def 
            by (metis Diff_iff \<open>a \<in> A - {u}\<close> v'_e doubleton_eq_iff)   
          have "v' \<in> Vs G - A"
            using \<open>a \<in> A \<and> v' \<in> Vs G - A\<close> by blast
          have "v' \<noteq> u" 
            using u_v \<open>v' \<in> Vs G - A\<close> by blast
          then have "e' \<in> G \<and> a \<in> e' \<and> u \<notin> e' \<and> v \<notin> e'"
            using \<open>a \<in> A - {u}\<close>  \<open>(u \<in> A \<and> v \<in> Vs G - A)\<close> \<open>{a} \<subset> A\<close> \<open>e' = {a, v'}\<close> v'_e 
            by fast
          then show "a \<in> Vs ?E_s" by blast
        qed   
        then show ?thesis 
          using \<open>u \<notin> Vs ?E_s\<close> by blast
      qed
      have "cover_matching G M ?A_s" 
        using `cover_matching ?E_s M ?A_s`
        unfolding cover_matching_def using graphE by blast
      then have "cover_matching G M (A - {u})" 
        by (simp add: \<open>?A_s = A - {u}\<close>)
      then have "A - {u} \<subseteq> Vs M" 
        by (simp add: cover_matching_def)
      have "M \<subseteq> G" 
        using \<open>cover_matching G M ?A_s\<close> cover_matching_def by blast
      have "matching M" 
        using \<open>cover_matching G M ?A_s\<close> cover_matching_def by blast
      have "\<forall> e \<in> M. u \<notin> e \<and> v \<notin> e "
        by (metis (no_types, lifting) \<open>cover_matching ?E_s M ?A_s\<close> cover_matching_def 
            mem_Collect_eq set_diff_eq subset_iff)
      then have "\<forall> e \<in> M. e \<noteq> {u, v} \<longrightarrow> e \<inter> {u, v} = {}" 
        by simp
      then have 8:"matching (insert {u, v} M)"
        using `matching M` unfolding matching_def  
        by auto 
      then have "A \<subseteq> Vs (insert {u, v} M)"
        using `A - {u} \<subseteq> Vs M` 
        by (smt (verit, ccfv_threshold) Sup_insert UnCI Vs_def u_v
            insertCI insertE insert_Diff subset_iff)
      have "insert {u, v} M \<subseteq> G" 
        using `{u, v} \<in> G`  \<open>M \<subseteq> G\<close> by blast
      then have "cover_matching G (insert {u, v} M) A"
        unfolding cover_matching_def using  `graph_invar G` 8 
        using \<open>A \<subseteq> Vs (insert {u, v} M)\<close> by blast
      then show ?thesis by auto
    qed
  next
    case False
    have "\<exists> X \<subset> A. X \<noteq> {} \<and> card (neighbours_of_Vs G X) \<le> card X" 
      using False le_less_linear by blast
    then obtain X where X:"X \<subset> A \<and> X \<noteq> {}\<and> card (neighbours_of_Vs G X) = card X"
      by (meson antisym less.prems(2) psubset_imp_subset)
    then have "X \<subset> A" by auto
    have "card X = card (neighbours_of_Vs G X)"
      by (simp add: \<open>X \<subset> A \<and> X \<noteq> {} \<and> card (neighbours_of_Vs G X) = card X\<close>)
    show ?thesis
    proof -

      let  ?X_gr = "{e \<in> G. \<exists>x \<in> X. x \<in> e}"
      have "?X_gr \<subseteq> G" by auto
      have "\<forall> Y \<subseteq> A. card Y \<le> card (neighbours_of_Vs G Y)"
        using less.prems(2) by blast
      then  have  "\<forall> Y \<subseteq> X. card Y \<le> card (neighbours_of_Vs G Y)" 
        by (meson \<open>X \<subset> A\<close> psubsetE subset_psubset_trans)
      have 1:"\<forall> Y \<subseteq> X. (neighbours_of_Vs G Y) = neighbours_of_Vs ?X_gr Y"
        unfolding neighbours_of_Vs_def 
        by(safe, blast+)
      have "card X < card A" using `X \<subset> A` 
        by (meson finite_subset graphE Asubs psubset_card_mono)
      have "graph_invar ?X_gr" 
        using \<open>?X_gr \<subseteq> G\<close>
        by (meson graphE graph_invar_subset)
      have "X \<subseteq> Vs ?X_gr" 
        by (smt (verit, best) vs_member_elim X  Asubs mem_Collect_eq
            psubsetD subset_iff vs_transport)
      have "(\<forall>e\<in> ?X_gr. \<exists>u v. e = {u, v} \<and> (u \<in> X \<and> v \<in> Vs {e \<in> G. \<exists>x\<in>X. x \<in> e} - X))"
      proof 
        fix e
        assume "e \<in> ?X_gr"
        have "e \<in> G" 
          using \<open>e \<in> {e \<in> G. \<exists>x\<in>X. x \<in> e}\<close> by blast
        then obtain u v where u_v: " e = {u, v}  \<and> (u \<in> A \<and> v \<in> Vs G - A)"
          using `partitioned_bipartite G A` unfolding partitioned_bipartite_def by meson
        have "v \<in> Vs ?X_gr" 
          using \<open>e \<in> ?X_gr\<close> u_v vs_member by fastforce
        then have "v \<in>  Vs ?X_gr - X" 
          using \<open>X \<subset> A\<close> u_v by blast
        then  show "( \<exists>u v. e = {u, v} \<and> (u \<in> X \<and> v \<in> Vs ?X_gr - X))" 
          using \<open>e \<in> ?X_gr\<close> u_v by blast
      qed   
      then  have "partitioned_bipartite ?X_gr X"
        unfolding partitioned_bipartite_def
        by (simp add: \<open>X \<subseteq> Vs {e \<in> G. \<exists>x\<in>X. x \<in> e}\<close> \<open>graph_invar {e \<in> G. \<exists>x\<in>X. x \<in> e}\<close> )

      then have "\<exists>M. cover_matching ?X_gr M X" using
          ` card X < card A` `X \<subseteq> Vs ?X_gr`
        using `graph_invar ?X_gr` less.hyps 1 
        using \<open>\<forall>Y\<subseteq>X. card Y \<le> card (neighbours_of_Vs G Y)\<close> by presburger
      let ?AX_gr = "{e. e \<in> G \<and> (\<exists> x \<in> A - X. \<exists> y \<in> Vs G - (neighbours_of_Vs G X) - A. y \<in> e \<and>  x \<in> e)}"
      have "?X_gr \<inter> ?AX_gr = {}"
        apply (safe; auto simp: neighbours_of_Vs_def) 
        using \<open>X \<subset> A\<close> by auto
      have "?AX_gr \<subseteq> G" 
        by blast
      have "X \<noteq> {}"
        by (simp add: \<open>X \<subset> A \<and> X \<noteq> {} \<and> card (neighbours_of_Vs G X) = card X\<close>)
      have " card (A - X) < card A"
        by (metis \<open>X \<noteq> {}\<close> \<open>X \<subset> A\<close> card_Diff_subset card_gt_0_iff diff_less 
            dual_order.strict_implies_order finite_subset graphE Asubs subset_empty)
      have A_X_graph:"graph_invar ?AX_gr" using `?AX_gr \<subseteq> G`
        by (meson graphE graph_invar_subset)
      have A_X_vs:"A - X \<subseteq> Vs ?AX_gr"
      proof
        fix x
        assume "x \<in> A - X"
        then have"card (neighbours_of_Vs G (X \<union> {x})) \<ge> card (X \<union> {x})"
          using X less.prems(2) by force
        then have "card (neighbours_of_Vs G (X \<union> {x})) > card X" 
          using \<open>X \<subseteq> Vs ?X_gr\<close> \<open>graph_invar ?X_gr\<close> \<open>x \<in> A - X\<close> card_seteq 
            finite.emptyI finite_subset by fastforce
        then have card_gr:"card (neighbours_of_Vs G (X \<union> {x})) > card (neighbours_of_Vs G X)"
          by (simp add: X)
        then  have  "(neighbours_of_Vs G (X)) \<subseteq> (neighbours_of_Vs G (X \<union> {x})) "
          unfolding neighbours_of_Vs_def by blast
        then have "(neighbours_of_Vs G (X)) \<subset> (neighbours_of_Vs G (X \<union> {x})) "
          using card_gr   by force
        then obtain z where z:"z\<in> neighbours_of_Vs G (X \<union> {x}) \<and> z\<notin> neighbours_of_Vs G (X)"
          by blast
        then obtain x' e where x'_e:"x' \<in> {x} \<and> e \<in> G \<and> z \<noteq> x' \<and> x' \<in> e \<and> z\<in> e"
          using z unfolding neighbours_of_Vs_def 
          by blast
        then have "e = {x, z}"
          using x'_e graphE by fastforce
        have "z \<in> Vs G - A" 
          using less.prems(1) z unfolding partitioned_bipartite_def
          by (metis Diff_iff \<open>e = {x, z}\<close> \<open>x \<in> A - X\<close> doubleton_eq_iff x'_e)
        then have "e \<in> G \<and> x\<in>A - X \<and>  z \<in> Vs G - neighbours_of_Vs G X - A \<and>  z \<in> e \<and> x \<in> e" 
          using \<open>x \<in> A - X\<close> x'_e z by blast
        then show "x \<in> Vs ?AX_gr"
          by blast
      qed
      have "Vs G - neighbours_of_Vs G X - A \<subseteq> Vs ?AX_gr" 
      proof
        fix x
        assume asm:"x \<in> Vs G - neighbours_of_Vs G X - A" 
        then obtain e where e:"e \<in> G \<and> x \<in> e" 
          by (meson DiffD1 vs_member_elim)
        then  have "\<nexists> u . u \<in> X \<and> ( \<exists> e \<in> G. x \<noteq> u \<and> u \<in> e \<and> x\<in> e)"                    
          using neighbours_of_Vs_def asm by force
        then have "\<exists> u. u \<in> (A - X) \<and>  x \<noteq> u \<and> u \<in> e \<and> x\<in> e"
          using e less.prems(1) unfolding partitioned_bipartite_def 
          by (metis Diff_iff asm insertCI )
        then have "e \<in> ?AX_gr"
          using e asm by blast
        then show "x \<in> Vs ?AX_gr"
          by (meson e vs_member_intro)
      qed
      then have vs_subs: "Vs G - neighbours_of_Vs G X - A \<subseteq> Vs ?AX_gr - (A - X)"
        by blast
      have AX_unfold:"\<forall>e\<in> ?AX_gr. \<exists>u v. e = {u, v} \<and> (u \<in> A - X \<and> v \<in> Vs ?AX_gr - (A - X))" 
        using less.prems(1)
        unfolding partitioned_bipartite_def
        apply safe
        by (smt (verit, best) DiffI insert_iff singletonD subsetD vs_subs)
      then have AX_partb:"partitioned_bipartite ?AX_gr (A - X)"
        unfolding partitioned_bipartite_def 
        using A_X_graph A_X_vs by fastforce

      have "\<forall>Y\<subseteq>(A-X). card Y \<le> card (neighbours_of_Vs ?AX_gr Y)"
      proof rule+
        fix Y
        assume "Y \<subseteq> (A-X)"
        have reach_AX_Y:"neighbours_of_Vs ?AX_gr Y = neighbours_of_Vs G Y - neighbours_of_Vs G X"
        proof
          show "neighbours_of_Vs ?AX_gr Y \<subseteq> neighbours_of_Vs G Y - neighbours_of_Vs G X"
          proof
            fix x
            assume asm: "x \<in> neighbours_of_Vs ?AX_gr Y"
            have "neighbours_of_Vs ?AX_gr Y \<subseteq> neighbours_of_Vs G Y"
              using `?AX_gr \<subseteq> G` unfolding neighbours_of_Vs_def
              by blast
            then have "x \<in> neighbours_of_Vs G Y" 
              using asm by blast
            obtain u e where u_e:" u \<in> Y \<and>  e \<in> ?AX_gr \<and> x \<noteq> u \<and> u \<in> e \<and> x\<in> e"
              using asm unfolding neighbours_of_Vs_def 
              by blast
            then have "\<exists>x\<in>A - X. \<exists>y\<in>Vs G - neighbours_of_Vs G X - A. y \<in> e \<and> x \<in> e" 
              by blast
            then have "x \<in> Vs G - neighbours_of_Vs G X - A" 
              using A_X_graph DiffD2 \<open>Y \<subseteq> A - X\<close> u_e  by auto
            then  show "x \<in> neighbours_of_Vs G Y - neighbours_of_Vs G X"
              by (simp add: \<open>x \<in> neighbours_of_Vs G Y\<close>) 
          qed
          show "neighbours_of_Vs G Y - neighbours_of_Vs G X \<subseteq> neighbours_of_Vs ?AX_gr Y"
          proof
            fix x
            assume asm: "x \<in> neighbours_of_Vs G Y - neighbours_of_Vs G X"
            have "neighbours_of_Vs G Y \<subseteq> Vs G - A"
              using neighbours_of_Vs_bipartite[OF less.prems(1)] 
                neighbours_of_Vs_subset[of Y A G] \<open>Y \<subseteq> A - X\<close> by auto   
            then obtain u e where u_e:"u \<in> Y \<and>  e \<in> G \<and> x \<noteq> u \<and> u \<in> e \<and> x\<in> e"
              using asm unfolding neighbours_of_Vs_def  by auto
            then have "e \<in> ?AX_gr" 
              using asm  \<open>Y \<subseteq> A - X\<close> \<open>neighbours_of_Vs G Y \<subseteq> Vs G - A\<close> by auto 
            then show "x \<in> neighbours_of_Vs ?AX_gr Y" 
              unfolding neighbours_of_Vs_def using u_e by blast 
          qed
        qed
        then have "card (neighbours_of_Vs ?AX_gr Y) = card (neighbours_of_Vs G Y - neighbours_of_Vs G X)"
          by presburger

        have "(neighbours_of_Vs G Y - neighbours_of_Vs G X) \<inter> neighbours_of_Vs G X = {}"  by auto
        then have "card (neighbours_of_Vs G (Y \<union> X))  = 
                   card (neighbours_of_Vs G Y - neighbours_of_Vs G X) + card (neighbours_of_Vs G X)"
          by (metis (no_types, lifting) \<open>X \<noteq> {}\<close> \<open>X \<subset> A\<close> \<open>card X = card (neighbours_of_Vs G X)\<close> 
              \<open>?AX_gr \<subseteq> G\<close>  card.infinite card_0_eq card_Un_disjoint finite_neighbours_of_Vs finite_subset
              graphE Asubs psubset_imp_subset reach_AX_Y neighbours_of_Vs_un)
        then have card_diff:"card (neighbours_of_Vs G Y - neighbours_of_Vs G X) = 
                   card (neighbours_of_Vs G (Y \<union> X)) - card (neighbours_of_Vs G X)" by auto
        have "card (neighbours_of_Vs G (Y \<union> X)) \<ge> card (Y \<union> X)"
          by (metis Diff_subset \<open>X \<subset> A\<close> \<open>Y \<subseteq> A - X\<close> le_sup_iff less.prems(2) 
              psubset_imp_subset subset_Un_eq)
        then have "card (neighbours_of_Vs G (Y \<union> X)) - card (neighbours_of_Vs G X) \<ge> card (Y \<union> X) - card X"
          using `card X = card (neighbours_of_Vs G X)` by auto
        moreover have "X \<inter> Y = {}"
          by (metis Diff_eq Int_commute Int_subset_iff \<open>Y \<subseteq> A - X\<close> disjoint_eq_subset_Compl)
        moreover have "card (Y \<union> X) - card X = card Y" 
          by (metis (no_types, lifting) A_X_graph A_X_vs Un_commute \<open>X \<inter> Y = {}\<close> \<open>X \<subset> A\<close> 
              \<open>Y \<subseteq> A - X\<close> add_diff_cancel_left' card_Un_disjoint finite_subset graphE Asubs
              psubset_imp_subset)
        ultimately show "card Y \<le> card (neighbours_of_Vs ?AX_gr Y)" 
          using card_diff reach_AX_Y by presburger
      qed

      then have "\<exists>M. cover_matching ?AX_gr M (A-X)" 
        using AX_partb A_X_graph A_X_vs \<open>card (A - X) < card A\<close> less.hyps by presburger
      then obtain M' where M':"cover_matching ?AX_gr M'(A-X)" by auto
      obtain M where M:"cover_matching ?X_gr M X"
        using \<open>\<exists>M. cover_matching {e \<in> G. \<exists>x\<in>X. x \<in> e} M X\<close> by blast

      have Vs_inter:"Vs ?X_gr \<inter> Vs ?AX_gr = {}"
      proof(rule ccontr)
        assume "Vs ?X_gr \<inter> Vs ?AX_gr \<noteq> {}"
        then obtain z where z: "z \<in> Vs ?X_gr \<and> z\<in> Vs ?AX_gr" 
          by auto
        then have "\<exists> e \<in> G. \<exists>x\<in>X. x \<in> e \<and> z \<in> e"
          by (smt (verit, ccfv_SIG) mem_Collect_eq vs_member_elim)
        then obtain e' x' where e'_x':"e' \<in> G \<and> x'\<in>X \<and> x' \<in> e' \<and> z \<in> e'" 
          by auto
        then obtain e x y where e:"e \<in> G \<and> z \<in> e \<and> x \<in> A - X \<and> 
                               y \<in> Vs G - neighbours_of_Vs G X - A \<and> y \<in> e \<and> x \<in> e"
          by (smt (verit) mem_Collect_eq vs_member z)
        then have "z = x \<or> z = y"
          using graphE by fastforce
        then have "z \<in> A - X \<or> z\<in> Vs G - neighbours_of_Vs G X - A" using e by presburger
        show False
        proof (cases "z \<in> X")
          case True
          have "z \<notin> A" using `z \<in> A - X \<or> z\<in> Vs G - neighbours_of_Vs G X - A` 
            using True by blast
          then show ?thesis
            using True \<open>X \<subset> A\<close> by blast
        next
          case False
          then have "z \<in> neighbours_of_Vs G X"
            using e'_x' neighbours_of_Vs_def by fastforce
          then have " z \<in> A - X" using `z \<in> A - X \<or> z\<in> Vs G - neighbours_of_Vs G X - A` by blast
          have "\<exists>u v. e' = {u, v} \<and> (u \<in> A \<and> v \<in> Vs G - A)"
            using less.prems(1) unfolding partitioned_bipartite_def
            using e'_x' by blast
          then show ?thesis
            using \<open>z \<in> A - X\<close>  False \<open>X \<subset> A\<close> e'_x' by blast 
        qed
      qed
      then have Vs_M: "Vs M \<subseteq> Vs ?X_gr" 
        using M unfolding cover_matching_def 
        by (meson Vs_subset)
      have Vs_M': "Vs M' \<subseteq> Vs ?AX_gr"
        using M' unfolding cover_matching_def 
        by (meson Vs_subset)
      then have "Vs M \<inter> Vs M' = {}" 
        using Vs_M Vs_inter by blast
      then have "Vs M \<union> Vs M' = Vs (M \<union> M')"
        by (simp add: Vs_def)
      have "\<forall>v \<in> Vs (M \<union> M'). \<exists>!e\<in>(M \<union> M'). v \<in> e" 
      proof 
        fix v
        assume "v \<in> Vs (M \<union> M')" 
        show " \<exists>!e\<in>(M \<union> M'). v \<in> e"
        proof(cases "v \<in> Vs M")
          case True
          have "\<exists>!e\<in>(M). v \<in> e" 
            using M unfolding cover_matching_def 
            by (simp add: True matching_def2)  
          then show ?thesis using True
            using \<open>Vs M \<inter> Vs M' = {}\<close> disjoint_iff_not_equal vs_member by auto
        next
          case False
          have "\<exists>!e\<in>(M'). v \<in> e" 
            using M' unfolding cover_matching_def 
            by (metis (no_types, lifting) False UnE \<open>Vs M \<union> Vs M' = Vs (M \<union> M')\<close> 
                \<open>v \<in> Vs (M \<union> M')\<close> matching_def2)
          then show ?thesis 
            using False \<open>Vs M \<inter> Vs M' = {}\<close> UnE by blast
        qed
      qed
      then  have "matching (M \<union> M')" 
        by (simp add: matching_def2)
      have "M \<union> M' \<subseteq> G" 
        using M M' unfolding cover_matching_def
        by fast
      have "A \<subseteq> Vs (M \<union> M')" 
        using M M' unfolding cover_matching_def
        by (metis (no_types, lifting) Diff_partition Un_mono 
            \<open>Vs M \<union> Vs M' = Vs (M \<union> M')\<close> \<open>X \<subset> A\<close> psubset_imp_subset)
      then have "cover_matching G (M \<union> M') A" 
        unfolding cover_matching_def 
        using \<open>M \<union> M' \<subseteq> G\<close> \<open>matching (M \<union> M')\<close> graphE by fastforce
      then show "\<exists>M. cover_matching G M A" by auto
    qed
  qed
qed

theorem hall:
  fixes G :: "'a set set"
  assumes "partitioned_bipartite G A" "graph_invar G"
  shows "(\<exists> M. cover_matching G M A) \<longleftrightarrow> (\<forall> X \<subseteq> A. card (neighbours_of_Vs G X) \<ge> card X)"
  using hall1[OF _ assms(2)] hall2[OF assms(1) _ assms(2)]
  by blast

lemma partitioned_bipartite_from_bipartite:
  assumes "bipartite G L R" "L \<subseteq> Vs G"
  shows "partitioned_bipartite G L"
proof(rule partitioned_bipartiteI[OF assms(2)], goal_cases)
  case (1 e)
  then obtain u v where "e = {u, v}" "u \<in> L" "v \<in> R" "L \<inter> R = {}" "e \<in> G"
    using assms(1)
    by(auto  elim!: bipartiteE)
  then show ?case
    by(auto intro!: exI[of "\<lambda> ua. \<exists>va. {u, v} = {ua, va} \<and> _ ua va" u]
                    exI[of "\<lambda> va. {u, v} = {u, va} \<and> _ va" v])
qed

theorem hall_standard_bipartite:
  assumes "bipartite G L R" "graph_invar G"
  shows  "(\<exists> M. cover_matching G M L) \<longleftrightarrow> (\<forall> X \<subseteq> L. card (neighbours_of_Vs G X) \<ge> card X)"
proof-
  show  "(\<exists> M. cover_matching G M L) \<longleftrightarrow> (\<forall> X \<subseteq> L. card (neighbours_of_Vs G X) \<ge> card X)"
  proof(cases "L \<subseteq> Vs G")
    case True
    note part_bib = partitioned_bipartite_from_bipartite[OF assms(1) True]
    then show ?thesis 
      using hall assms(2) by auto
  next
    case False
    then obtain x where x: "x \<in> L" "x \<notin> Vs G" by auto
    have "cover_matching G M L \<Longrightarrow> False" for M
    proof(goal_cases)
      case 1
      hence "x \<in> Vs M" "M \<subseteq> G"
        using x(1)
        by(auto elim!: cover_matchingE)
      then obtain e where "e \<in> G" "x \<in> e"
        using Vs_subset x(2) by blast
      hence "x \<in> Vs G"
        by (simp add: vs_member_intro)
      thus False
        using x(2) by simp
    qed
    hence "\<not> (\<exists>M. cover_matching G M L)" by auto
    moreover have "{x} \<subseteq> L" "card {x} > card (neighbours_of_Vs G {x})"
      using x by(auto simp add: neighbours_of_Vs_def vs_member)
    ultimately show ?thesis
      by auto
  qed
qed

subsection \<open>Existence of Arbitrary Cover Matchings\<close>

theorem schrijver_corollary_16_8a:
  assumes "partitioned_bipartite G A" "graph_invar G" "X \<subseteq> Vs G"
  shows   "(\<exists> M. cover_matching G M X) \<longleftrightarrow> 
           ((\<forall> S \<subseteq> A \<inter> X. card (Neighbourhood G S) \<ge> card S) \<and> 
             (\<forall> S \<subseteq> (Vs G - A) \<inter> X. card (Neighbourhood G S) \<ge> card S))"
proof(rule, goal_cases)
  case 1
  note one = this
  then obtain M where M: "cover_matching G M X" by auto
  hence M_graph_matching: "graph_matching G M"
    using cover_matching_is_graph_matching by auto
  have "\<lbrakk>M \<subseteq> G; X \<subseteq> Vs M; x \<in> A; x \<in> X\<rbrakk> \<Longrightarrow> x \<in> Vs (M \<inter> deltas G (A \<inter> X))" for x
    by(rule vs_member_elim[of _ M])
      (auto elim!: vs_member_elim[of _ M] simp add: deltas_def)
  hence cover_match_red: "cover_matching (deltas G (A \<inter> X)) (M \<inter> deltas G (A \<inter> X)) (A \<inter> X)"
    using M
    by(auto intro!: cover_matchingI elim!: cover_matchingE intro: matching_subgraph)
  have "\<lbrakk>M \<subseteq> G; X \<subseteq> Vs M; x \<in> X; x \<in> Vs G; x \<notin> A\<rbrakk> \<Longrightarrow> x \<in> Vs (M \<inter> deltas G ((Vs G - A) \<inter> X))" 
    for x
    by(rule vs_member_elim[of _ M])
      (auto elim!: vs_member_elim[of _ M] simp add: deltas_def)
  hence cover_match_red': "cover_matching (deltas G ((Vs G - A) \<inter> X)) (M \<inter> deltas G ((Vs G - A) \<inter> X)) ((Vs G - A) \<inter> X)"
    using M
    by(auto intro!: cover_matchingI elim!: cover_matchingE intro: matching_subgraph)
  have finite_G: "finite G"
    by (simp add: assms(2) finite_Vs_then_finite)
  show ?case
  proof(rule, all \<open>rule\<close>, all \<open>rule\<close>, goal_cases)
    case (1 S)
    have "card S \<le> card (neighbours_of_Vs (deltas G (A \<inter> X)) S)"
      using cover_match_red  1
      by (auto intro!: mp[OF spec[OF hall1[of ]], of _ _ "A \<inter> X"] 
          simp add: assms(2) graph_invar_deltas)
    also have "... \<le> card (neighbours_of_Vs G S)"
      using assms(2) finite_neighbours_of_Vs deltas_subset[of G "A \<inter> X"]
      by(auto intro!: card_mono graph_subs_reach)
    also have "... = card (Neighbourhood G S)" 
      apply(rule arg_cong[of _ _  card])
      apply(rule bipartite_neighbours_of_Vs_Neighbourhood[OF assms(1)])
      using 1 by blast
    finally show ?case 
      by simp
  next
    case (2 S)
    hence "card S \<le> card (neighbours_of_Vs (deltas G ((Vs G - A) \<inter> X)) S)"
      by (auto simp add: assms(2) graph_invar_deltas 
          intro: mp[OF spec[OF hall1[of ]], of _ _ "(Vs G - A) \<inter> X"] cover_match_red')
    also have "... \<le> card (neighbours_of_Vs G S)"
      using assms(2) finite_neighbours_of_Vs deltas_subset[of G "(Vs G - A) \<inter> X"]
      by(auto intro!: card_mono graph_subs_reach)
    also have "... = card (Neighbourhood G S)" 
      apply(rule arg_cong[of _ _  card])
      apply(rule bipartite_neighbours_of_Vs_Neighbourhood[ 
            OF partitioned_bipartite_swap [OF assms(1)]])
      using 2 by blast
    finally show ?case 
      by simp
  qed
next
  case 2
  have partitioned_neighbs_of_left_X:
    "partitioned_bipartite (deltas G (A \<inter> X)) (A \<inter> X)"
    by (simp add: assms(1) partitioned_bipartite_project_to_verts)
  moreover have card_neighb_left:
    "S \<subseteq> A \<inter> X \<Longrightarrow> card S \<le> card (neighbours_of_Vs (deltas G (A \<inter> X)) S)" for S
  proof(goal_cases)
    case 1
    hence "card S \<le> card (Neighbourhood G S)"
      using 2 by auto
    also have "... = card (neighbours_of_Vs G S)"
      apply(rule arg_cong[of  _ _ card])
      apply(rule bipartite_neighbours_of_Vs_Neighbourhood[OF assms(1), symmetric])
      using 1 by blast
    also have "... = card (neighbours_of_Vs (deltas G (A \<inter> X)) S)"
      using 1
      by(force intro!: arg_cong[of  _ _ card] simp add: neighbours_of_Vs_def deltas_def)
    finally show ?case 
      by simp
  qed
  moreover have graph_invar_left: "graph_invar (deltas G (A \<inter> X))"
    by (simp add: assms(2) graph_invar_deltas)
  ultimately obtain M where M: "cover_matching (deltas G (A \<inter> X)) M (A \<inter> X)"
    using hall2[OF partitioned_neighbs_of_left_X] 
    by auto
  have partitioned_neighbs_of_right_X:
    "partitioned_bipartite (deltas G ((Vs G - A) \<inter> X)) ((Vs G - A) \<inter> X)"
    by (simp add: assms(1) partitioned_bipartite_project_to_verts partitioned_bipartite_swap)
  moreover have card_neighb_reight:
    "S \<subseteq> (Vs G - A) \<inter> X \<Longrightarrow> card S \<le> card (neighbours_of_Vs (deltas G ((Vs G - A) \<inter> X)) S)" for S
  proof(goal_cases)
    case 1
    hence "card S \<le> card (Neighbourhood G S)"
      using 2 by auto
    also have "... = card (neighbours_of_Vs G S)"
      apply(rule arg_cong[of  _ _ card])
      apply(rule bipartite_neighbours_of_Vs_Neighbourhood[OF
            partitioned_bipartite_swap[OF assms(1)], symmetric])
      using 1 by blast
    also have "... = card (neighbours_of_Vs (deltas G ((Vs G - A) \<inter> X)) S)"
      using 1
      by(force intro!: arg_cong[of  _ _ card] simp add: neighbours_of_Vs_def deltas_def)
    finally show ?case 
      by simp
  qed
  moreover have graph_inv_right: "graph_invar (deltas G ((Vs G - A) \<inter> X))"
    by (simp add: assms(2) graph_invar_deltas)
  ultimately obtain M' where M': "cover_matching (deltas G ((Vs G - A) \<inter> X)) M' ((Vs G - A) \<inter> X)"
    using hall2[OF partitioned_neighbs_of_right_X]
    by auto
  have M_cover_left: "cover_matching G M (A \<inter> X)" 
    and M'_cover_right: "cover_matching G M' ((Vs G - A) \<inter> X)" 
    using M M' deltas_subset by(auto intro: cover_matching_bigger_graph)
  have finite_G: "finite G"
    by (simp add: assms(2) finite_Vs_then_finite)
  obtain M where  M_cover_left_most_of_X: 
    "cover_matching G M (A \<inter> X)" 
    "\<And> M'. cover_matching G M' (A \<inter> X) \<Longrightarrow> card (X \<inter> Vs M') \<le> card (X \<inter> Vs M)"
    apply(rule maximiser_of_function_nempty_finite[of 
          "Collect (\<lambda> M. cover_matching G M (A \<inter> X))" "\<lambda> M. card (X \<inter> Vs M)"])
    using finite_G  finite_number_of_cover_matchings  M_cover_left by auto
  have "X \<subseteq> Vs M" 
  proof(rule ccontr, goal_cases)
    case 1
    then obtain x where x: "x \<in> X" "x \<notin> Vs M"
      by auto
    hence x_right: "x \<in> (Vs G - A) \<inter> X" "x \<in> (Vs G - A)"
      using  M_cover_left_most_of_X(1) assms(3) by(auto elim!: cover_matchingE)
    have x_inVs_M_M':"x \<in> Vs (M \<union> M')" 
      using  M'_cover_right x_right
      by(auto elim!: cover_matchingE simp add: vs_union)
    define C where "C = connected_component (M \<union> M') x"
    have x_in_C: "x \<in> C"
      by (simp add: C_def in_own_connected_component)
    interpret graph_abs_MM': graph_abs "M \<union> M'"
      using M_cover_left_most_of_X(1) assms(2) M'_cover_right
      by(auto intro: graph_invar_union graph_abs_mono graph_abs.intro elim!: cover_matchingE)
    have C_is_component: "C \<in> connected_components (M \<union> M')" 
      by (simp add: C_def connected_component_in_components x_inVs_M_M')
    have deg_in_MM': "degree (M \<union> M') v \<le> 2" for v
      using M'_cover_right M_cover_left_most_of_X(1)
      by(auto elim!: cover_matchingE intro!: degree_matching_union)
    define p where "p = (component_path' (M \<union> M') C)"
    note p_props = graph_abs_MM'.component_path'_works[OF C_is_component deg_in_MM', folded p_def]
    have p_not_Nil: "p \<noteq> []" 
      using p_props(2) x_in_C by fastforce
    have "x = hd p \<or> x = last p"
    proof(rule ccontr, goal_cases)
      case 1
      then obtain p1 p2 y z where p_split: "p = p1@[y,x,z]@p2" 
        by (metis element_of_list_cases last_ConsL last_appendR list.sel(1) not_Cons_self2 p_props(2)
            x_in_C)
      have "{y, x} \<in> set (edges_of_path p)"  "{x, z} \<in> set (edges_of_path p)"
        using edges_of_path_append_subset p_split by fastforce+
      moreover have "set (edges_of_path p) \<subseteq> M \<union> M'"
        by (simp add: p_props(1) path_edges_subset)
      ultimately have "{y, x} \<in> M \<union> M'"  "{x, z} \<in> M \<union> M'" by auto
      hence yx_xz_in_M': "{y, x} \<in> M'"  "{x, z} \<in> M'" 
        using vs_member x(2) by fastforce+
      hence "{y, x} \<noteq> {x, z}" 
        using p_props(3) p_split yx_xz_in_M' by (auto simp add: doubleton_eq_iff)
      thus False 
        using  M'_cover_right yx_xz_in_M'(1,2)
        by(force elim!: cover_matchingE matchingE) 
    qed
    hence "\<exists> p. path (M \<union> M') p \<and> set p = C \<and> distinct p \<and> p \<noteq> Nil \<and> hd p = x"
      using p_not_Nil p_props
      by (auto  intro: exI[of _ "rev p"] rev_path_is_path simp add: hd_rev)
    then obtain p where p_props:"path (M \<union> M') p" "set p = C" "distinct p" "p \<noteq> Nil" "hd p = x"
      by auto
    obtain e where e_for_x: "x \<in> e" "e \<in> M'"
      using  x(2) x_inVs_M_M' by(auto elim!: in_Vs_unionE  simp add: vs_member[of x])
    then obtain y where yx:"y \<in> e" "x \<noteq> y"
      using graph_abs_MM'.subset_edges_G by auto
    hence e_is_xy:"e = {x, y}" 
      using e_for_x(1,2) graph_abs_MM'.subset_edges_G[of "{e}" e]
      by auto
    hence "reachable (M \<union> M') x y" 
      using e_for_x
      by(auto intro!: edges_reachable)
    hence "x \<in> set p" "y \<in> set p"
      using x_in_C
      by (auto simp add: p_props(2) C_def in_connected_componentI)
    hence length_p: "2 \<le> length p"
      using yx(2) by(cases p rule: list_cases3) auto
    have alt_path_M_p: "alt_path M p" 
      and alt_list_M_M'_p: 
      "alt_list (\<lambda>e. e \<in> M' \<and> e \<notin> M) (\<lambda>e. e \<in> M \<and> e \<notin> M') (edges_of_path p)"
      using M_cover_left_most_of_X(1) p_props(1,3,5) M' length_p x(2) assms(2) graph_inv_right
      by(all \<open>intro union_of_matchings_alt_path[of M M'] union_of_matchings_alt_list_M'_M[of M M']\<close>)
        (auto elim!: cover_matchingE)
    have matching_M: "matching M"
      using M_cover_left_most_of_X(1) cover_matchingE by auto
    note p_applied = rematch_atl_path_Vs_change[OF matching_M alt_path_M_p p_props(3) length_p] 
    have bipartite_M_M': "bipartite (M\<union>M') A (Vs G - A)" 
      using  M'_cover_right assms(1) M_cover_left_most_of_X(1)
      by(auto intro!: bipartiteI elim!: cover_matchingE partitioned_bipartiteE)
    have walk_p: "walk_betw (M \<union> M') x p (last p)"
      by (simp add: nonempty_path_walk_between p_props(1,4,5))
    note MM'_ends_and_lengths = bipartite_ends_and_lengths(3,4,7,8)[OF
        bipartite_M_M', OF walk_p x_right(2)]
    have p_degree: "x \<in> set p \<Longrightarrow> degree (M \<union> M') x \<le> 2" for x
      by (simp add: deg_in_MM')
    note x_and_last_degr_same =
      component_walk_vertex_degress(3)[OF p_degree length_p p_props(3) walk_p
        p_props(2)[simplified C_def] graph_abs_MM'.graph, simplified]
    moreover have degree_x: "degree (M\<union>M') x = 1"
      using x(2) M'_cover_right e_for_x
      by(auto intro!: unique_edge_degree_one[of _ e]
          elim!: cover_matchingE 
          dest: matching_unique_match)
    ultimately have degree_last_p:"degree (M\<union>M') (last p) = 1"
      by auto
    have edges_p_in_G: "set (edges_of_path p) \<subseteq> G" 
      and in_G_rematch: "M \<oplus> set (edges_of_path p) \<subseteq> G" 
      using  M'_cover_right M_cover_left_most_of_X(1) 
        p_props(1) path_edges_subset[of "M\<union>M'" p]
      by(auto elim!: cover_matchingE  simp add: symmetric_diff_def)
    have hd_p_in_X: "hd p \<in> X"
      by (simp add: p_props(5) x(1))
    have finite_X_last_p_M:"finite (X \<inter> insert (last p) (Vs M))"
      "finite (X \<inter> (insert (hd p) (Vs M) - {last p}))"
      using assms(2,3) rev_finite_subset by fastforce+
    have ep1:"(edges_of_path p) ! (length p -2) = {p!(length p -2), p ! (length p -1)}"
      using length_p 
      by (subst edges_of_path_index[of "length p -2" p]) 
        (auto simp add: Suc_diff_Suc numeral_2_eq_2)
    have ep2: "(edges_of_path p) ! (length p -2) = last (edges_of_path p)"
      using length_p 
      by(subst last_conv_nth, cases p rule: list_cases3)
        (auto simp add: edges_of_path_length numeral_2_eq_2 )
    have ep4: "last p \<in>  last (edges_of_path p)" 
      by (simp add: last_v_in_last_e length_p)
    show ?case
    proof(rule ccontr, cases "last p \<in> A", goal_cases)
      case 1
      note last_in_A = this
      have even_length_p:"even (length p)" 
        by (simp add: MM'_ends_and_lengths(3) 1)
      hence odd_edges_length:"odd (length (edges_of_path p))"
        by (simp add: edges_of_path_length' p_props(4))
      hence last_edge_not_in_M:"last (edges_of_path p) \<notin> M" 
        using alt_path_M_p alternating_list_odd_last by blast
      have ep3: "last (edges_of_path p) \<in> M'" 
        using edges_of_path_nempty last_edge_not_in_M last_in_set length_p p_props(1)
          path_edges_subset
        by fastforce
      have last_not_in_M: "last p \<notin> Vs M"
      proof(rule ccontr, goal_cases)
        case 1
        then obtain e' where "last p \<in> e'" "e' \<in> M"
          by (auto simp add: vs_member)
        moreover hence "last (edges_of_path p) \<noteq> e'"
          using last_edge_not_in_M by blast
        ultimately have "degree (M\<union>M') (last p) \<ge> 2"
          using at_least_two_edges_degree_geq_2[of "last p" "last (edges_of_path p)" "M \<union> M'" e']
            ep4 ep3 
          by simp
        thus False
          by (simp add: degree_last_p)
      qed
      hence last_p_not_in_X:"last p \<notin> X"
        using obtain_covering_edge[OF M_cover_left_most_of_X(1)] last_in_A by auto
      have matching_rematch: "matching (M \<oplus> (set (edges_of_path p)))"
        using even_length_p last_not_in_M  p_props(3)
        by(auto intro!: symm_diff_is_matching simp add: alt_path_M_p matching_M p_props(5) x(2))
      note rematched_Vs =
        rematch_atl_path_Vs_change[OF matching_M alt_path_M_p p_props(3) length_p,
          simplified if_P[OF even_length_p]]
      have cover_matching_rematch: "cover_matching G (M \<oplus> set (edges_of_path p)) (A \<inter> X)"
        using in_G_rematch hd_p_in_X last_p_not_in_X  M_cover_left_most_of_X(1)
        by(auto intro!: cover_matchingI matching_rematch 
            elim!: cover_matchingE 
            simp add: rematched_Vs)
      moreover have "card (X \<inter> Vs (M \<oplus> set (edges_of_path p))) > card (X \<inter> Vs M)"
        using assms(2,3) p_props(5) x(1,2) finite_X_last_p_M
        by(auto intro!: psubset_card_mono simp add: rematched_Vs)
      ultimately show False
        using M_cover_left_most_of_X(2) 
        by force
    next
      case 2
      note last_not_in_A = this(2)
      have odd_length_p:"odd (length p)" 
        using MM'_ends_and_lengths(1) last_not_in_A by auto
      hence even_edges_length:"even (length (edges_of_path p))"
        by (simp add: edges_of_path_length' p_props(4))
      hence last_edge_in_M:"last (edges_of_path p) \<in> M" 
        using alt_path_M_p alternating_list_even_last edges_of_path_nempty length_p by auto 
      have ep3: "last (edges_of_path p) \<notin> M'" 
        using alt_list_M_M'_p  edges_of_path_nempty length_p 
          alternating_list_even_last even_edges_length 
        by blast
      have last_not_in_M: "last p \<notin> Vs M'"
      proof(rule ccontr, goal_cases)
        case 1
        then obtain e' where "last p \<in> e'" "e' \<in> M'"
          by (auto simp add: vs_member)
        moreover hence "last (edges_of_path p) \<noteq> e'"
          using  ep3 by blast
        ultimately have "degree (M\<union>M') (last p) \<ge> 2"
          using at_least_two_edges_degree_geq_2[of "last p" "last (edges_of_path p)" "M \<union> M'" e']
            ep4 last_edge_in_M 
          by simp
        thus False
          by (simp add: degree_last_p)
      qed
      hence last_p_not_in_X:"last p \<notin> X"
        using M'_cover_right assms(3) last_not_in_A 
        by(auto elim!: cover_matchingE)
      have matching_rematch: "matching (M \<oplus> (set (edges_of_path p)))"
        using  p_props(3) odd_length_p
        by(auto intro!: symm_diff_is_matching simp add: alt_path_M_p matching_M p_props(5) x(2))
      note rematched_Vs =
        rematch_atl_path_Vs_change[OF matching_M alt_path_M_p p_props(3) length_p,
          simplified if_not_P[OF odd_length_p]]
      have cover_matching_rematch: "cover_matching G (M \<oplus> set (edges_of_path p)) (A \<inter> X)"
        using in_G_rematch hd_p_in_X   M_cover_left_most_of_X(1) last_p_not_in_X
        by(auto intro!: cover_matchingI matching_rematch 
            elim!: cover_matchingE 
            simp add: rematched_Vs)
      moreover have "card (X \<inter> Vs (M \<oplus> set (edges_of_path p))) > card (X \<inter> Vs M)"
        using assms(2,3) p_props(5) x(1,2) finite_X_last_p_M last_p_not_in_X
        by(auto intro!: psubset_card_mono simp add: rematched_Vs)
      ultimately show False
        using M_cover_left_most_of_X(2) 
        by force
    qed
  qed
  thus ?case
    using M_cover_left_most_of_X(1)
    by(auto intro!: exI[of _ M] cover_matchingI elim!: cover_matchingE)
qed

theorem schrijver_corollary_16_8a_standard_bipartite:
  assumes "bipartite G L R" "graph_invar G" "X \<subseteq> L \<union> R"
  shows  "(\<exists> M. cover_matching G M X) \<longleftrightarrow> 
           ((\<forall> S \<subseteq> L \<inter> X. card (Neighbourhood G S) \<ge> card S) \<and> 
             (\<forall> S \<subseteq> R \<inter> X. card (Neighbourhood G S) \<ge> card S))"
proof-
  show ?thesis
  proof(cases "X \<subseteq> Vs G")
    case True
    hence L_in_G: "L \<inter> Vs G \<subseteq> Vs G" by auto
    have X_in_G: "X \<subseteq> Vs G" 
      using True assms(3) by auto
    have new_LX_is: "L \<inter> Vs G \<inter> X = L \<inter> X"
      using X_in_G by auto
    have new_RX_is: "(Vs G - L \<inter> Vs G) \<inter> X = R \<inter> X"
      using True assms(1)
      by(auto elim!: bipartiteE dest: bipartite_vertex(4)[OF _  assms(1)])
    have bip_red:"bipartite G (L \<inter> Vs G) R" 
    proof(rule bipartiteI, goal_cases)
      case 1
      then show ?case 
        using bipartite_disjointD[OF assms(1)] by auto
    next
      case (2 e)
      then show ?case 
      proof(elim bipartite_edgeE[OF _ assms(1)], goal_cases)
        case (1 x y)
        then show ?case 
          using edges_are_Vs[of x y G] 2
          by auto
      qed
    qed
    note part_bib = partitioned_bipartite_from_bipartite[OF bip_red  L_in_G]
    note schrijver_corollary_16_8a = schrijver_corollary_16_8a[OF part_bib assms(2) X_in_G]
    then show ?thesis
      by(auto simp add: new_LX_is new_RX_is)
  next
    case False
    then obtain x where x: "x \<in> X" "x \<notin> Vs G" by auto
    have "cover_matching G M X \<Longrightarrow> False" for M
    proof(goal_cases)
      case 1
      hence "x \<in> Vs M" "M \<subseteq> G"
        using x(1) by(auto elim!: cover_matchingE)
      then obtain e where "e \<in> G" "x \<in> e"
        using Vs_subset x(2) by blast
      hence "x \<in> Vs G"
        by (simp add: vs_member_intro)
      thus False
        using x(2) by simp
    qed
    hence no_match: "\<not> (\<exists>M. cover_matching G M X)" by auto
    have finite_NG_x:"finite (Neighbourhood G {x})"
      using assms(2) by (auto intro!: finite_subset[OF Neighbourhood_in_G])
    hence x_counter: "{x} \<subseteq> L \<inter> X  \<or> {x} \<subseteq> R \<inter> X" "card {x} > card (Neighbourhood G {x})"
      using x assms(3) by (auto elim!: in_NeighbourhoodE)
    have "\<not>((\<forall>S\<subseteq>L \<inter> X. card S \<le> card (Neighbourhood G S)) 
            \<and> (\<forall>S\<subseteq>R \<inter> X. card S \<le> card (Neighbourhood G S)))" 
    proof(rule ccontr, goal_cases)
      case 1
      hence cards: "S \<subseteq> L \<inter> X \<Longrightarrow> card S \<le> card (Neighbourhood G S)"
                   "S \<subseteq> R \<inter> X \<Longrightarrow> card S \<le> card (Neighbourhood G S)" for S
        by auto
      have "card {x} \<le> card (Neighbourhood G {x})"
        using cards[of "{x}"]  x_counter(1) by blast
      then show ?case 
        using x_counter(2) by simp
    qed
    thus ?thesis
      using no_match by blast
  qed
qed

subsection \<open>Existence of Perfect Matchings: Frobenius' Theorem\<close>

theorem frobenius_matching:
  fixes G :: "'a set set"
  assumes "partitioned_bipartite G A" "graph_invar G"
  shows "(\<exists> M. perfect_matching G M) \<longleftrightarrow> 
         (\<forall> X \<subseteq> A. card (neighbours_of_Vs G X) \<ge> card X) \<and> (card A) = card (Vs G - A)"
proof
  show "\<exists>M. perfect_matching G M \<Longrightarrow> 
        (\<forall>X\<subseteq>A. card X  \<le> card (neighbours_of_Vs G X)) \<and> card A = card (Vs G - A)"
  proof -
    assume "\<exists>M. perfect_matching G M"
    show "(\<forall>X\<subseteq>A. card X  \<le> card (neighbours_of_Vs G X)) \<and> card A = card (Vs G - A)"
    proof
      obtain M where "perfect_matching G M"
        using \<open>\<exists>M. perfect_matching G M\<close> by auto
      then  have "Vs M = Vs G" 
        unfolding perfect_matching_def by auto
      then have "A \<subseteq> Vs M"
        using assms partitioned_bipartite_def by fastforce
      then have "cover_matching G M A"
        by (meson \<open>perfect_matching G M\<close> cover_matching_def perfect_matching_def)
      then show "\<forall>X\<subseteq>A. card X  \<le> card (neighbours_of_Vs G X)"
        using assms hall by auto

      have "Vs G - A = neighbours_of_Vs G A" 
        by (simp add: assms neighbours_of_Vs_bipartite)
      have "partitioned_bipartite G (Vs G - A)" 
        by (simp add: assms partitioned_bipartite_swap)
      then have "cover_matching G M (Vs G - A)"
        using \<open>cover_matching G M A\<close> unfolding cover_matching_def
        by (simp add: \<open>Vs M = Vs G\<close>)
      then have "card (Vs G - A) \<le> card (neighbours_of_Vs G (Vs G - A))"
        using hall \<open>partitioned_bipartite G (Vs G - A)\<close>  assms(2)
        by blast
      moreover have "card A  \<le> card (neighbours_of_Vs G A)"
        by (simp add: \<open>\<forall>X\<subseteq>A. card X \<le> card (neighbours_of_Vs G X)\<close>)
      moreover have "A = neighbours_of_Vs G (Vs G - A)" 
        using neighbours_of_Vs_bipartite assms
        unfolding partitioned_bipartite_def 
        by (simp add: Diff_Diff_Int \<open>partitioned_bipartite G (Vs G - A)\<close>
            inf.absorb_iff2 neighbours_of_Vs_bipartite)  
      ultimately show "card A = card (Vs G - A)" 
        using \<open>Vs G - A = neighbours_of_Vs G A\<close> by auto
    qed
  qed
  show "(\<forall>X\<subseteq>A. card X \<le> card (neighbours_of_Vs G X)) \<and> card A = card (Vs G - A) \<Longrightarrow> 
        \<exists>M. perfect_matching G M"
  proof -
    assume asm: "(\<forall>X\<subseteq>A. card X \<le> card (neighbours_of_Vs G X)) \<and> card A = card (Vs G - A)"
    then  have "\<forall>X\<subseteq>A. card X \<le> card (neighbours_of_Vs G X)" 
      by auto
    then have "\<exists>M. cover_matching G M A"
      using hall assms by auto
    then obtain M where M:"cover_matching G M A"
      by auto
    then have "card A = card (neighbours_of_Vs M A)" 
      by (simp add: cover_matching_neighbours_of_Vs_card assms(2)) 
    have "neighbours_of_Vs M A \<subseteq> neighbours_of_Vs G A"
      by (meson M cover_matching_def graph_subs_reach)
    have "Vs G - A = neighbours_of_Vs G A" 
      by (simp add: assms neighbours_of_Vs_bipartite)
    then have "neighbours_of_Vs M A = Vs G - A" 
      using M unfolding cover_matching_def 
      by (metis \<open>card A = card (neighbours_of_Vs M A)\<close> \<open>neighbours_of_Vs M A \<subseteq> neighbours_of_Vs G A\<close> assms(2) asm card_subset_eq finite_Diff)
    have "Vs G = Vs M" 
      using neighbours_of_Vs_bipartite[OF part_bipart_of_cover_matching[OF assms(1) M]] 
        M assms unfolding partitioned_bipartite_def cover_matching_def
      using assms M unfolding partitioned_bipartite_def cover_matching_def
      by (metis Diff_partition \<open>neighbours_of_Vs M A = Vs G - A\<close>)
    then show "\<exists>M. perfect_matching G M"
      using \<open>cover_matching G M A\<close> unfolding cover_matching_def perfect_matching_def
      by auto
  qed
qed

theorem frobenius_standard_bipartite:
  assumes "bipartite G L R" "graph_invar G"
  shows "(\<exists> M. perfect_matching G M) \<longleftrightarrow> 
         (\<forall> X \<subseteq> L \<inter> Vs G. card (Neighbourhood G X) \<ge> card X) \<and> card (L \<inter> Vs G) = card (R \<inter> Vs G)"
proof-

  have fb1:"partitioned_bipartite G (L \<inter> Vs G)" 
    using assms(1)
    by(auto intro: partitioned_bipartite_from_bipartite dest: bipartite_reduced_to_vs)
  have in_LX:"X \<subseteq> L \<inter> Vs G \<Longrightarrow> neighbours_of_Vs G X = Neighbourhood G X" for X
    using bipartite_neighbours_of_Vs_Neighbourhood fb1 by blast
  have RG_is:"Vs G - L \<inter> Vs G = R \<inter> Vs G"
    using assms(1) 
    by (auto dest: bipartite_vertex)
  show ?thesis 
    using in_LX
    by(auto simp add: frobenius_matching[OF fb1 assms(2)] RG_is)
qed

end