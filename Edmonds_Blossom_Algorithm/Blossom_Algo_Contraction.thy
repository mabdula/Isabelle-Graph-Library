theory Blossom_Algo_Contraction
  imports Blossom_Algo_Main_Loop Graph_Quotient
begin
subsection\<open>Contracting blossoms and lifting found augmenting paths\<close>

text\<open>We refine the algorithm \<open>aug_path_search\<close>. Here we only handle contracting \<open>match_blossoms\<close> and lifting
     abstract augmenting paths.\<close>

datatype 'a match_blossom_res =
   Path "'a list" 
| Blossom (stem_vs: "'a list") (cycle_vs: "'a list")

locale create_vert = 
  fixes create_vert::"'a set \<Rightarrow> 'a"
  assumes create_vert_works:
    "finite vs \<Longrightarrow> create_vert vs \<notin> vs" (*It has to be finite, otherwise that is a contradiction*)

text \<open>Here we cannot fix the graph nor the matching as they change as the algorithm executes.\<close>

locale find_aug_path = choose sel+
  create_vert create_vert 
  for sel::"'a set \<Rightarrow> 'a" and create_vert::"'a set \<Rightarrow> 'a" +
  fixes blos_search::"'a set set \<Rightarrow> 'a set set \<Rightarrow>  ('a match_blossom_res) option"
  assumes
    bloss_algo_complete: 
    "\<lbrakk>graph_invar G; matching M; M \<subseteq> G;
        (\<exists>p. graph_augmenting_path G M p)\<rbrakk>
     \<Longrightarrow> (\<exists>blos_comp. blos_search G M = Some blos_comp)" and
    bloss_algo_sound:
    "\<lbrakk>graph_invar G; matching M; M \<subseteq> G; blos_search G M = Some (Path p)\<rbrakk> \<Longrightarrow>
     graph_augmenting_path G M p"
    "\<lbrakk>graph_invar G; matching M; M \<subseteq> G; blos_search G M = Some (Blossom stem C)\<rbrakk> \<Longrightarrow>
     blossom G M stem C"
begin

lemma bloss_algo_sound_2:
    "\<lbrakk>graph_invar G; matching M; M \<subseteq> G; blos_search G M = Some (Blossom stem C)\<rbrakk> 
    \<Longrightarrow> (path G (stem @ C) \<and> (matching M \<longrightarrow> match_blossom M stem C))"
  using bloss_algo_sound
  by meson

text\<open>A function to contract vertices\<close>

(*abbreviation "quot_fun s u v \<equiv> (if v \<notin> s then u else v)"*)

text\<open>This function is parameterised on another function that computes an augmenting path or a
     \<open>match_blossom\<close> if either one exists. It returns an optional \<open>match_blossom_comp\<close>, i.e. a \<open>match_blossom\<close> or an
     augmenting path or nothing.\<close>

function (domintros) find_aug_path where
  "find_aug_path G M = 
     (case blos_search G M of Some match_blossom_res \<Rightarrow>
        case match_blossom_res of Path p \<Rightarrow> Some p
        | Blossom stem cyc \<Rightarrow>
            let u = create_vert (Vs G);
                s = Vs G - (set cyc);
                quotG = quot.quotG s (create_vert (Vs G));
                refine = quot.refine sel G s (create_vert (Vs G)) cyc M
            in (case find_aug_path (quotG G) (quotG M) of Some p' \<Rightarrow> Some (refine p')
                | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)"
  by pat_completeness auto

definition "find_aug_path_meas G = card (Vs G)"

(*lemma quot_sat:
  assumes "finite vs" "u = (create_vert vs)" "s \<subseteq> vs"
  shows "quot (quot_fun s u) s u"
  using assms
  unfolding quot_def
  using create_vert_works[OF assms(1)] assms by auto
*)

context 
  fixes s::"'a set" and E::"'a set set"
  assumes quot_assms: "s\<subset>Vs E" "graph_invar E"
begin
interpretation quot: quot sel E s "(create_vert (Vs E))"
  apply(unfold_locales)
  using quot_assms create_vert_works 
  by auto


lemma card_Vs_lt:
  assumes "1 < card (Vs E - s)"
  shows "find_aug_path_meas (quot.quotG E) < find_aug_path_meas E"
  unfolding find_aug_path_meas_def
  apply (rule quot.card_Vs_quotG)
  using quot_assms assms
  by auto

lemmas matching_quotM=quot.matching_quotM

lemmas doublton_quot = quot.doubleton_quot

lemmas aug_path_works_in_contraction = quot.aug_path_works_in_contraction

lemmas finite_quot = quot.finite_quot

lemmas doubleton_quot = quot.doubleton_quot

lemmas refine = quot.refine

end

lemma find_aug_path_dom_step:
  assumes "let u = (create_vert (Vs G));
               s = (Vs G - (set (cycle_vs (the (blos_search G M)))));
               quotG = quot.quotG s u
           in find_aug_path_dom (quotG G, quotG M)"
  shows "find_aug_path_dom (G, M)"
  using assms
  by (auto simp add: Let_def intro: find_aug_path.domintros)

lemma blossom_cycle_longer_2:
  assumes \<open>match_blossom M stem cyc\<close> 
  shows "card (set cyc) \<ge> 2"
proof-
  have "distinct (butlast cyc)"
    using match_blossomD(2)[OF \<open>match_blossom M stem cyc\<close>] distinct_append
    by blast
  then have "length (butlast cyc) = card (set (butlast cyc))"
    by (simp add: distinct_card)
  have "length (butlast cyc) = length cyc - 1"
    using length_butlast by blast
  then have "length (butlast cyc) \<ge> 2"
    using odd_cycleD(1)[OF match_blossomD(3)[OF \<open>match_blossom M stem cyc\<close>]] 
    by auto
  then have "card (set (butlast cyc)) \<ge> 2"
    using \<open>length (butlast cyc) = card (set (butlast cyc))\<close>
    by auto
  moreover have "set cyc = insert (last cyc) (set (butlast cyc))"
  proof-
    have "cyc = (butlast cyc) @ [last cyc]"
    proof -
      have cyc_nempty: "cyc \<noteq> []"
        using match_blossomD(3)[OF \<open>match_blossom M stem cyc\<close>]
        by (rule odd_cycle_nempty)
      show ?thesis
        using cyc_nempty
        by (simp add: append_butlast_last_id)
    qed
    then have "set cyc = set (butlast cyc @ [last cyc])"
      by (rule arg_cong)
    then show ?thesis
      by simp
  qed
  ultimately show ?thesis
    using card_insert_le order.trans by fastforce
qed

lemma blossom_diff: 
assumes
  "graph_invar E" 
  "match_blossom M stem cyc"
  "path E (stem @ cyc)"
shows "((Vs E) - set cyc) \<subset> (Vs E)" (is "?s \<subset> _")
proof-  
  have "path E cyc"
    using path_suff[OF assms(3)] .
  then have "set cyc \<subseteq> Vs E"
    using subset_path_Vs by blast
  then have "Vs E - ?s = set cyc"
    by auto
  moreover have "?s \<subseteq> Vs E"
    by auto
  moreover have "card (set cyc) \<ge> 2"
    using blossom_cycle_longer_2[OF \<open>match_blossom M stem cyc\<close>] .
  moreover have "finite (Vs E)"
    by (simp add: assms)
  ultimately show ?thesis
    by auto
qed

lemma find_aug_path_dom:
  assumes "matching M" "M \<subseteq> E" "graph_invar E" 
  shows "find_aug_path_dom (E,M)"
  using assms
proof(induction "find_aug_path_meas E" arbitrary: E M rule: nat_less_induct)
  case 1
  show ?case
  proof(cases "(blos_search E M) = None")
    case T1: True
    then show ?thesis
      by (auto intro: find_aug_path.domintros)
  next
    case F1: False
    then obtain blos_comp where blos_comp: "(blos_search E M) = Some blos_comp"
      by auto
    show ?thesis
    proof(cases "\<exists>p. blos_comp = Path p")
      case T2: True
      then show ?thesis
      proof -
        from T2 obtain p where p: "blos_comp = Path p"
          by blast
        show ?thesis
          using blos_comp p
          by (auto intro: find_aug_path.domintros)
      qed
    next
      let ?u = "(create_vert (Vs E))"
      case F2: False
      then obtain stem cyc where stem_cyc: "blos_comp = Blossom stem cyc"
        using match_blossom_res.exhaust_sel by blast
      let ?s = "(Vs E - (set cyc))"
      have "match_blossom M stem cyc"
        "path E (stem @ cyc)"
        using bloss_algo_sound(2) blos_comp stem_cyc "1.prems"
        by auto
      then have "set cyc \<subseteq> Vs E"
        using path_suff subset_path_Vs
        using path_suff subset_path_Vs by blast
      then have "Vs E - ?s = set cyc"
        by auto
      moreover have "?s \<subseteq> Vs E"
        by auto
      moreover have "card (set cyc) \<ge> 2"
        using blossom_cycle_longer_2[OF \<open>match_blossom M stem cyc\<close>] .
      moreover have "finite (Vs E)"
        by (simp add: "1.prems"(3))
      ultimately have "find_aug_path_meas (quot.quotG ?s ?u E) < find_aug_path_meas E"
        using 1              
        by (fastforce intro!: card_Vs_lt)

      moreover have "finite (quot.quotG ?s ?u E)"
        using "1.prems"
        using quot_graph_finite'[OF graph_invar_finite_Vs[OF "1.prems"(3)]]
        by auto
      moreover have "((Vs E) - set cyc) \<subset> (Vs E)"
        using blossom_diff[OF \<open>graph_invar E\<close> \<open>match_blossom M stem cyc\<close> \<open>path E (stem@cyc)\<close>].  
      hence "dblton_graph (quot.quotG ?s ?u E)"
        apply(intro doublton_quot[where E = E])
        using \<open>graph_invar E\<close> create_vert_works
        by auto


      ultimately have dom_quot: "find_aug_path_dom (quot.quotG ?s ?u E, M')" 
        if "matching M'" "M' \<subseteq> quot.quotG ?s ?u E" for M'
        using 1 that
        by (simp add: finite_dbl_finite_verts)
      moreover have "matching (quot.quotG ?s ?u M)"
        apply (intro matching_quotM[where s = ?s and stem = stem and C=cyc and E=E])
        subgoal using \<open>((Vs E) - set cyc) \<subset> (Vs E)\<close> .
        subgoal using \<open>graph_invar E\<close> .
        subgoal using \<open>match_blossom M stem cyc\<close> .
        subgoal using 1(2) .
        subgoal using "1.prems"(2) by blast
        subgoal ..
        done
      moreover have "(quot.quotG ?s ?u M) \<subseteq> quot.quotG ?s ?u E"
        by (simp add: "1.prems"(2) Diff_mono graph_subset_quot_subset)
      ultimately show ?thesis
        using blos_comp stem_cyc 1(2)
        by (fastforce intro!: find_aug_path_dom_step)
    qed
  qed
qed

lemma find_aug_path_complete:
  assumes aug_path: "graph_augmenting_path G M p" and
    matching: "matching M" "M \<subseteq> G" and
    graph: "graph_invar G"
  shows "\<exists>p'. find_aug_path G M = Some p'"
proof-
  have "find_aug_path_dom (G,M)"
    using find_aug_path_dom[OF matching(1,2) \<open>graph_invar G\<close>]
    by simp
  then show ?thesis
    using assms
  proof (induction arbitrary: p rule: find_aug_path.pinduct)
    case (1 G M)
    show ?case
    proof(cases "(blos_search G M) = None")
      case T1: True
      then show ?thesis
        using 1 bloss_algo_complete
      proof -
        obtain blos_comp where "blos_search G M = Some blos_comp"
          using bloss_algo_complete[OF "1.prems"(4,2,3)] "1.prems"(1)
          by blast
        then show ?thesis
          using T1 by simp
      qed
    next
      case F1: False
      then obtain blos_comp where blos_comp: "(blos_search G M) = Some blos_comp"
        by auto
      show ?thesis
      proof(cases "\<exists>p. blos_comp = Path p")
        case T2: True
        then show ?thesis
          apply(simp add: find_aug_path.psimps[OF 1(1)])
          using blos_comp bloss_algo_sound
          by force
      next
        let ?u = "(create_vert (Vs G))"
        case F2: False
        then obtain stem cyc where stem_cyc: "blos_comp = Blossom stem cyc"
          using match_blossom_res.exhaust_sel by blast
        define s where "s = (Vs G - (set cyc))"
        have blos: "blossom G M stem cyc"
          using bloss_algo_sound(2) blos_comp stem_cyc 1
        proof -
          have blos_search_eq: "blos_search G M = Some (Blossom stem cyc)"
            using blos_comp stem_cyc by simp
          show "blossom G M stem cyc"
            using bloss_algo_sound(2)[OF \<open>graph_invar G\<close> \<open>matching M\<close> \<open>M \<subseteq> G\<close> blos_search_eq] .
        qed
        then have "set cyc \<subseteq> Vs G"
          using path_suff subset_path_Vs
        proof -
          have "path G (stem @ cyc)"
            using blossomD(1)[OF blos] .
          then have "path G cyc"
            using path_suff by blast
          then show ?thesis
            using subset_path_Vs by blast
        qed
        then have "Vs G - s = set cyc"
          unfolding s_def
          by auto
        have "((Vs G) - set cyc) \<subset> (Vs G)"
          using blossom_diff[OF \<open>graph_invar G\<close> blossomD(2,1)[OF blos]] .
        moreover have "graph_invar G"
          using \<open>graph_invar G\<close> .
        moreover have "?u \<notin> Vs G"
          using create_vert_works \<open>graph_invar G\<close>
          by simp
        moreover have "finite M"
         using graph_invar_finite_Vs[OF \<open>graph_invar G\<close>] graph_invar_dblton[OF\<open>graph_invar G\<close>] \<open>M \<subseteq> G\<close>
          by (simp add: dblton_graph_finite_Vs finite_subset)
        ultimately obtain p' where p': "graph_augmenting_path (quot.quotG s ?u G) (quot.quotG s ?u M) p'"
          using aug_path_works_in_contraction[OF _ _ blos \<open>graph_augmenting_path G M p\<close> \<open>matching M\<close>] 
          using "1.prems"(3) s_def
          by auto
        have "finite (quot.quotG s ?u M)"
          using finite_quot[OF \<open>((Vs G) - set cyc) \<subset> (Vs G)\<close> \<open>graph_invar G\<close> \<open>finite M\<close>]
          by (auto simp add: s_def)
        moreover have "dblton_graph (quot.quotG s ?u G)"
          using doubleton_quot[OF \<open>((Vs G) - set cyc) \<subset> (Vs G)\<close> \<open>graph_invar G\<close>]
          by (auto simp: s_def)
        moreover have "finite (quot.quotG s ?u G)"
          using quot_graph_finite'[OF graph_invar_finite_Vs[OF \<open>graph_invar G\<close>]]
          by auto
        moreover have "(quot.quotG s ?u M) \<subseteq> (quot.quotG s ?u G)"
          using graph_subset_quot_subset[OF \<open>M \<subseteq> G\<close>]
          by auto
        moreover have "matching (quot.quotG s ?u M)"
          using matching_quotM[OF \<open>((Vs G) - set cyc) \<subset> (Vs G)\<close> \<open>graph_invar G\<close> blossomD(2)[OF blos]] 
                1 s_def
          by blast
        ultimately obtain p'' where "find_aug_path (quot.quotG s ?u G) (quot.quotG s ?u M) = Some p''"
          using s_def 1(2)[OF blos_comp stem_cyc _ _ _ _ p'] dblton_graph_finite_Vs
          by fastforce
        then show ?thesis
          apply(intro exI[where x="quot.refine sel G s ?u cyc M p''"])
          by(force simp add: s_def blos_comp stem_cyc find_aug_path.psimps[OF 1(1)] Let_def split: option.splits)
      qed
    qed
  qed
qed

end

lemma match_blossom_distinct_tl:
  assumes "match_blossom M stem cyc"
  shows "distinct (tl cyc)"
proof-
  have "distinct (butlast cyc)" "hd cyc = last cyc"
    using match_blossomD[OF assms] odd_cycleD
    unfolding distinct_append[symmetric] 
    by auto
  then have "distinct (tl (butlast cyc))" "hd cyc \<notin> set (tl (butlast cyc))"
    using distinct_tl
  proof -
    have cyc_nempty: "cyc \<noteq> []"
      using match_blossomD(3)[OF assms] odd_cycle_nempty by blast
    have len_butlast: "length (butlast cyc) \<ge> 2"
    proof -
      have "length (butlast cyc) = length cyc - 1"
        using length_butlast by blast
      then show ?thesis
        using odd_cycleD(1)[OF match_blossomD(3)[OF assms]] by auto
    qed
    have butlast_nempty: "butlast cyc \<noteq> []"
    proof
      assume "butlast cyc = []"
      then have "length (butlast cyc) = 0" by simp
      with len_butlast show False by simp
    qed
    have cyc_eq: "cyc = butlast cyc @ [last cyc]"
      using append_butlast_last_id[OF cyc_nempty] by simp
    have hd_eq: "hd cyc = hd (butlast cyc)"
    proof -
      have "hd cyc = hd (butlast cyc @ [last cyc])"
        by (rule arg_cong[OF cyc_eq])
      also have "\<dots> = hd (butlast cyc)"
        by (rule hd_append2[OF butlast_nempty])
      finally show ?thesis .
    qed
    have distinct_consed: "distinct (hd (butlast cyc) # tl (butlast cyc))"
      using \<open>distinct (butlast cyc)\<close> list.collapse[OF butlast_nempty] by simp
    have hd_notin: "hd (butlast cyc) \<notin> set (tl (butlast cyc))"
      using distinct_consed by simp
    have distinct_tl_butlast: "distinct (tl (butlast cyc))"
      using distinct_consed by simp
    show "distinct (tl (butlast cyc))"
      using distinct_tl_butlast .
    show "hd cyc \<notin> set (tl (butlast cyc))"
      using hd_eq hd_notin by simp
  qed
  then have "distinct ((tl (butlast cyc)) @ [last cyc])"
    using \<open>hd cyc = last cyc\<close>
    by auto
  moreover have "(tl (butlast cyc)) @ [last cyc] = tl cyc" if "length cyc \<ge> 3" for cyc::"'a list"
    using that
  proof(induction cyc)
    case Nil
    then show ?case by auto
  next
    case (Cons a' cyc')
    then show ?case 
      by auto
  qed
  moreover have "length cyc \<ge> 3"
    using odd_cycleD(1)[OF match_blossomD(3)[OF assms]]
    by auto
  ultimately show ?thesis
    by auto
qed

lemma cycle_set_tl_eq_butlast:
  assumes "match_blossom M stem cyc"
  shows "set (tl cyc) = set (butlast cyc)"
proof -
  have oc: "odd_cycle cyc"
    using match_blossomD(3)[OF assms] .
  have nempty: "cyc \<noteq> []"
    using odd_cycle_nempty[OF oc] .
  have len_ge3: "3 \<le> length cyc"
    using odd_cycleD(1)[OF oc] .
  have hd_eq_last: "hd cyc = last cyc"
    using odd_cycleD(3)[OF oc] .
  have tl_nempty: "tl cyc \<noteq> []"
    using len_ge3 nempty by (cases cyc) auto
  have bl_nempty: "butlast cyc \<noteq> []"
    using len_ge3 nempty by (cases cyc) auto
  have but_eq: "cyc = butlast cyc @ [last cyc]"
    using nempty by (simp add: append_butlast_last_id)
  have rot: "rotate1 cyc = tl cyc @ [hd cyc]"
  proof (cases cyc)
    case Nil
    then show ?thesis using nempty by simp
  next
    case (Cons x xs)
    then show ?thesis by (simp add: rotate1.simps(2))
  qed
  have set_eq1: "set cyc = set (tl cyc) \<union> {hd cyc}"
  proof -
    have "set cyc = set (rotate1 cyc)"
      by (simp add: set_rotate1)
    also have "\<dots> = set (tl cyc @ [hd cyc])"
      by (simp add: rot)
    also have "\<dots> = set (tl cyc) \<union> {hd cyc}"
      by simp
    finally show ?thesis .
  qed
  have set_eq2: "set cyc = set (butlast cyc) \<union> {last cyc}"
    using arg_cong[OF but_eq, of set] by simp
  have combined: "set (tl cyc) \<union> {hd cyc} = set (butlast cyc) \<union> {hd cyc}"
    using set_eq1 set_eq2 hd_eq_last by simp
  have x_in_tl: "hd cyc \<in> set (tl cyc)"
  proof -
    have "last (tl cyc) = last cyc"
      using nempty tl_nempty by (auto simp: last_tl)
    also have "\<dots> = hd cyc"
      using hd_eq_last by simp
    finally have last_tl_eq: "last (tl cyc) = hd cyc" .
    have "last (tl cyc) \<in> set (tl cyc)"
      using tl_nempty by (simp add: last_in_set)
    then show ?thesis
      using last_tl_eq by simp
  qed
  have x_in_bl: "hd cyc \<in> set (butlast cyc)"
  proof -
    obtain y ys where y_ys: "butlast cyc = y # ys"
      using bl_nempty by (cases "butlast cyc") auto
    then have "cyc = y # (ys @ [last cyc])"
      using but_eq by simp
    then have "hd cyc = y"
      by (cases cyc) auto
    then show ?thesis
      using y_ys by simp
  qed
  have "set (tl cyc) = set (tl cyc) \<union> {hd cyc}"
    using x_in_tl by auto
  also have "\<dots> = set (butlast cyc) \<union> {hd cyc}"
    using combined by simp
  also have "\<dots> = set (butlast cyc)"
    using x_in_bl by auto
  finally show ?thesis .
qed

context find_aug_path
begin

lemma find_aug_path_sound:
  assumes matching: "matching M" "M \<subseteq> G" "finite M" and
    graph: "graph_invar G" and
    find_aug_path: "find_aug_path G M = Some p"
  shows "graph_augmenting_path G M p"
proof-
  have "find_aug_path_dom (G,M)"
    using find_aug_path_dom[OF matching(1,2) graph]
    by simp
  then show ?thesis
    using assms
  proof (induction arbitrary: p rule: find_aug_path.pinduct)
    case (1 G M)
    show ?case
    proof(cases "(blos_search G M) = None")
      case T1: True
      then show ?thesis
        using 1(1,7) 
        by(simp add: find_aug_path.psimps)
    next
      case F1: False
      then obtain blos_comp where blos_comp: "(blos_search G M) = Some blos_comp"
        by auto
      show ?thesis
      proof(cases "\<exists>p. blos_comp = Path p")
        case T2: True
        then show ?thesis
          using 1(1,7)
          apply(simp add: find_aug_path.psimps)
          using blos_comp bloss_algo_sound 1
          by auto
      next
        let ?u = "(create_vert (Vs G))"
        case F2: False
        then obtain stem cyc where stem_cyc: "blos_comp = Blossom stem cyc"
          using match_blossom_res.exhaust_sel by blast
        let ?s = "(Vs G - (set cyc))"
        have blos: "path G (stem @ cyc)" "match_blossom M stem cyc"
          using bloss_algo_sound(2) blos_comp stem_cyc 1
          by auto
        (*then have "set cyc \<subseteq> Vs G"
          using path_suff subset_path_Vs
          using cons1(1) by fastforce
        then have "Vs G - s = set cyc"
          unfolding s_def
          by auto
        have s_subset_VsG: "s \<subseteq> Vs G"
          unfolding s_def
          by auto
        moreover have "finite (Vs G)"
          using dblton_graph_finite_Vs \<open>graph_invar G\<close>
          by auto
        ultimately have "quot s u"
          using 1 u_def quotF_def
          by simp*)
        have "?s \<subset> (Vs G)"
          using blossom_diff[OF \<open>graph_invar G\<close> blos(2,1)] .
        moreover have "graph_invar G"
          using \<open>graph_invar G\<close> .
        moreover have "?u \<notin> Vs G"
          using create_vert_works \<open>graph_invar G\<close>
          by simp
       moreover have "finite M"
         using graph_invar_finite_Vs[OF \<open>graph_invar G\<close>] graph_invar_dblton[OF\<open>graph_invar G\<close>] \<open>M \<subseteq> G\<close>
          by (simp add: dblton_graph_finite_Vs finite_subset)

        ultimately have "finite (quot.quotG ?s ?u M)"
          apply(intro finite_quot)
          by auto

        moreover have "dblton_graph (quot.quotG ?s ?u G)"
          using doubleton_quot[OF \<open>?s \<subset> Vs G\<close>] 1
          by simp
        moreover have "finite (quot.quotG ?s ?u G)"
          using "1.prems"(4) quot_graph_finite'
          by auto
        moreover have "(quot.quotG ?s ?u M) \<subseteq> (quot.quotG ?s ?u G)"
          by (simp add: "1.prems"(2) Diff_mono graph_subset_quot_subset)
        moreover have "matching (quot.quotG ?s ?u M)"
          using matching_quotM[OF \<open>?s \<subset> Vs G\<close> \<open>graph_invar G\<close> blos(2)] 1
          by blast
        moreover obtain p' where p': "find_aug_path (quot.quotG ?s ?u G) (quot.quotG ?s ?u M) = Some p'"
          using 1(7)
          by (simp add: blos_comp stem_cyc find_aug_path.psimps[OF 1(1)] Let_def split: option.splits)
        ultimately have "matching_augmenting_path (quot.quotG ?s ?u M) p' \<and>
                         path (quot.quotG ?s ?u G) p' \<and> distinct p'"
          using 1(2)[OF blos_comp stem_cyc _ _ _ _]
          by (meson dblton_graph_finite_Vs)
        then have "matching_augmenting_path M (quot.refine sel G ?s ?u cyc M p') \<and>
                   path G (quot.refine sel G ?s ?u cyc M p') \<and>
                   distinct (quot.refine sel G ?s ?u cyc M p')"
          using refine[OF \<open>?s \<subset> Vs G\<close>] match_blossomD[OF blos(2)]
            match_blossom_alt_cycle[OF blos(2)] match_blossom_distinct_tl[OF blos(2)]
            path_suff[OF blos(1)] 1
          by(auto simp add: )
        then show ?thesis
          using 1(7) p'
          by(simp add: blos_comp stem_cyc find_aug_path.psimps[OF 1(1)] Let_def split: option.splits)
      qed
    qed
  qed
qed

end

text\<open>the function terminates on a finite graph\<close>

locale find_aug_path_use = find_aug_path sel +
  graph_abs E for sel::"'a set \<Rightarrow> 'a" and E::"'a set set"
begin

interpretation find_max_match_intrp: find_max_match E find_aug_path
  apply unfold_locales
  subgoal using find_aug_path_complete[OF _ _ _ graph] by force
  subgoal using find_aug_path_sound[OF _ _ _ graph] by force
  done
(*
lemma find_max_match_sat:
  assumes "graph_invar G"
  shows "find_max_match G find_aug_path"
  unfolding find_max_match_def
  using find_aug_path_sound[OF _ _ _ assms] find_aug_path_complete[OF _ _ _ assms]
    finite_dbl_finite_verts[]
  by auto

*)
text\<open>The function can be plugged in the main function from above.\<close>

(*TODO: there must be a better way to use conclusions from the interpretation
        other than renaming everyithng*) 

abbreviation "find_max_matching \<equiv> find_max_match_intrp.find_max_matching"

lemmas find_max_matching_works = find_max_match_intrp.find_max_matching_works
(*lemma find_max_matching_2_works:
  shows "find_max_matching {} \<subseteq> G"
    "matching (find_max_matching {})"
    "finite (find_max_matching {})"
    "\<forall>M. matching M \<and> M \<subseteq> G \<and> finite M \<longrightarrow> card M \<le> card (find_max_matching {})"
  using find_max_matching_works
  by auto*)


end

lemma creat_vert_fun:
  "\<And>vs::nat set. finite vs \<Longrightarrow> (\<lambda>vs. Max vs +1) vs \<notin> vs"
  using Max_ge Suc_le_eq by auto

text\<open>This is a naive function to ascend the given blossom. It takes time quadratic in the size of
     the blossom.\<close>

fun longest_disj_pfx where
  "longest_disj_pfx l1 [] = (None,None)"
| "longest_disj_pfx [] l2 = (None,None)"
| "longest_disj_pfx l1 (h#l2) = 
    (let l1_pfx = (find_pfx ((=) h) l1) in
       if (last l1_pfx = h) then
         (Some l1_pfx,Some [h])
       else (let (l1_pfx,l2_pfx) = (longest_disj_pfx l1 l2) in
               case l2_pfx of Some pfx2 \<Rightarrow> (l1_pfx,Some (h#pfx2))
                            | _ \<Rightarrow> (l1_pfx, l2_pfx)))"

text\<open>This is a function to do the same task in linear time in the blossom.\<close>

fun longest_disj_pfx_lin where
  "longest_disj_pfx_lin l1 [] = (None, None)"
| "longest_disj_pfx_lin [] l2 = (None, None)"
| "longest_disj_pfx_lin (x#xs) (y#ys) =
    (if x = y then
       (Some [x], Some [x])
     else
       (let (l1_pfx,l2_pfx) = (longest_disj_pfx_lin xs ys)
        in
          case l1_pfx of Some pfx1 \<Rightarrow>
            (case l2_pfx of Some pfx2 \<Rightarrow> 
              (Some (x#pfx1), Some (y#ys)))
          | _ \<Rightarrow> (None, None)))"

lemma no_first_pfx_then_no_snd_pfx:
  "(None,l2_pfx) = (longest_disj_pfx l1 l2) \<Longrightarrow> \<exists>pfx2. l2_pfx = None"
proof(induction l2 arbitrary: l1 l2_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1
      apply (auto simp add: Let_def split: if_splits prod.splits option.splits)
      by (drule sym [where s = "longest_disj_pfx (a1' # l1') l2"], drule cons1.IH, simp)+
  qed
qed

lemma first_pfx_then_snd_pfx:
  "(Some pfx1,l2_pfx) = (longest_disj_pfx l1 l2) \<Longrightarrow> \<exists>pfx2. l2_pfx = Some pfx2"
proof(induction l2 arbitrary: l1 pfx1 l2_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1
      apply (auto simp add: Let_def split: if_splits prod.splits option.splits)
      by (metis option.simps(3))+
  qed
qed

lemma first_pfx_nempty:
  "(Some pfx1,l2_pfx) = (longest_disj_pfx l1 l2) \<Longrightarrow> pfx1 \<noteq> []"
proof(induction l2 arbitrary: l1 pfx1 l2_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    obtain l1_pfx' l2_pfx' where rec: "longest_disj_pfx l1 l2 = (l1_pfx', l2_pfx')"
      by (cases "longest_disj_pfx l1 l2") auto
    have unfold: "longest_disj_pfx l1 (a2 # l2) =
        (if last (find_pfx ((=) a2) (a1' # l1')) = a2
         then (Some (find_pfx ((=) a2) (a1' # l1')), Some [a2])
         else (case l2_pfx' of Some pfx2 \<Rightarrow> (l1_pfx', Some (a2 # pfx2)) | None \<Rightarrow> (l1_pfx', l2_pfx')))"
      using Cons rec
      by (simp add: Let_def)
    show ?thesis
    proof(cases "last (find_pfx ((=) a2) (a1' # l1')) = a2")
      case True
      then have "longest_disj_pfx l1 (a2 # l2) = (Some (find_pfx ((=) a2) (a1' # l1')), Some [a2])"
        using unfold
        by simp
      then have "pfx1 = find_pfx ((=) a2) (a1' # l1')"
        using cons1.prems
        by simp
      then show ?thesis
        by simp
    next
      case False
      then have unfold': "longest_disj_pfx l1 (a2 # l2) =
          (case l2_pfx' of Some pfx2 \<Rightarrow> (l1_pfx', Some (a2 # pfx2)) | None \<Rightarrow> (l1_pfx', l2_pfx'))"
        using unfold
        by simp
      show ?thesis
      proof(cases l2_pfx')
        case (Some pfx2)
        then have "longest_disj_pfx l1 (a2 # l2) = (l1_pfx', Some (a2 # pfx2))"
          using unfold'
          by simp
        then have "Some pfx1 = l1_pfx'"
          using cons1.prems
          by simp
        then have "(Some pfx1, Some pfx2) = longest_disj_pfx l1 l2"
          using rec Some
          by simp
        then show ?thesis
          using cons1.IH
          by blast
      next
        case None
        then have "longest_disj_pfx l1 (a2 # l2) = (l1_pfx', None)"
          using unfold'
          by simp
        then have "Some pfx1 = l1_pfx'"
          using cons1.prems
          by simp
        then have "(Some pfx1, None) = longest_disj_pfx l1 l2"
          using rec None
          by simp
        then show ?thesis
          using cons1.IH
          by blast
      qed
    qed
  qed
qed

lemma snd_pfx_nempty:
  "(l1_pfx, Some pfx2) = (longest_disj_pfx l1 l2) \<Longrightarrow> pfx2 \<noteq> []"
proof(induction l2 arbitrary: l1 l1_pfx pfx2)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1
      by (auto simp add: Let_def split: if_splits prod.splits option.splits)
  qed
qed

lemma pfx_common_end:
  "(Some pfx1, l2_pfx) = (longest_disj_pfx l1 l2) \<Longrightarrow> last pfx1 = last (the l2_pfx)"
proof(induction l2 arbitrary: l1 pfx1 l2_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1 
      apply (clarsimp simp add: Let_def split: if_splits prod.splits option.splits)
      subgoal by (rule cons1.IH[of _ None "a1'#l1'"], simp)
      subgoal premises prems for x2a
      proof -
        have rec: "(Some pfx1, Some x2a) = longest_disj_pfx (a1' # l1') l2"
          using prems by simp
        hence ne: "x2a \<noteq> []"
          using snd_pfx_nempty by blast
        have l: "last pfx1 = last (the (Some x2a))"
          using prems rec by blast
        then have l': "last pfx1 = last x2a" by simp
        then show "(x2a = [] \<longrightarrow> last pfx1 = a2) \<and> (x2a \<noteq> [] \<longrightarrow> last pfx1 = last x2a)"
          using ne by blast
      qed
      subgoal by (rule cons1.IH[of _ None "a1'#l1'"], simp)
      subgoal premises prems for x2a
      proof -
        have rec: "(Some pfx1, Some x2a) = longest_disj_pfx (a1' # l1') l2"
          using prems by simp
        hence ne: "x2a \<noteq> []"
          using snd_pfx_nempty by blast
        have "last pfx1 = last (the (Some x2a))"
          using cons1.IH[of pfx1 "Some x2a" "a1'#l1'"] rec by simp
        then have l': "last pfx1 = last x2a" by simp
        then show "(x2a = [] \<longrightarrow> last pfx1 = a2) \<and> (x2a \<noteq> [] \<longrightarrow> last pfx1 = last x2a)"
          using ne by simp
      qed
      done
  qed
qed

lemma find_pfx_nempty: "l \<noteq> [] \<Longrightarrow> find_pfx Q l \<noteq> []"
  by(induction l; auto)

lemma find_pfx_empty: "find_pfx Q l = [] \<Longrightarrow> l = []"
  using find_pfx_nempty by auto

lemma disj_pref_append1:
  assumes "(Some pfx1, l2_pfx) = (longest_disj_pfx l1 l2)"
  shows "\<exists>l1'. l1 = pfx1@l1'"
  using assms
proof(induction l2 arbitrary: l1 pfx1 l2_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1
      by (auto simp add: find_pfx_append_2 Let_def split: if_splits prod.splits option.splits)
  qed
qed

lemma disj_pref_append2:
  assumes "(l1_pfx, Some pfx2) = (longest_disj_pfx l1 l2)"
  shows "\<exists>l2'. l2 = pfx2@l2'"
  using assms
proof(induction l2 arbitrary: l1 pfx2 l1_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1
      proof(cases "last (find_pfx ((=) a2) (a1' # l1')) = a2")
        case True
        then have "pfx2 = [a2]"
          using cons1.prems Cons
          by (auto simp add: Let_def)
        then show ?thesis
          by (intro exI[where x = l2]) simp
      next
        case False
        obtain l1_pfx'' l2_pfx'' where rec: "longest_disj_pfx (a1' # l1') l2 = (l1_pfx'', l2_pfx'')"
          by (rule prod.exhaust)
        show ?thesis
        proof(cases l2_pfx'')
          case None
          then have "Some pfx2 = None"
            using cons1.prems Cons False rec
            by (auto simp add: Let_def)
          then show ?thesis
            by simp
        next
          case (Some pfx2'')
          then have pfx2_eq: "pfx2 = a2 # pfx2''"
            using cons1.prems Cons False rec
            by (auto simp add: Let_def)
          have eq2: "(l1_pfx'', Some pfx2'') = longest_disj_pfx (a1' # l1') l2"
            using rec Some by simp
          then obtain l2' where "l2 = pfx2'' @ l2'"
            using cons1.IH by blast
          then have "a2 # l2 = pfx2 @ l2'"
            by (simp add: pfx2_eq)
          then show ?thesis
            by blast
        qed
      qed
  qed
qed

lemma disj_pfx_are_disj_1:
  assumes "(Some pfx1, l2_pfx) = (longest_disj_pfx l1 l2)"
  shows "set pfx1 \<inter> set (butlast (the l2_pfx)) = {}"
  using assms
proof(induction l2 arbitrary: l1 pfx1 l2_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1(1,2)
      apply (clarsimp simp add: Let_def split: if_splits prod.splits option.splits)
      subgoal using cons1.prems by fastforce
      subgoal premises prems for x2a
      proof -
        have "l1' = []"
          using find_pfx_empty prems by blast
        moreover have eq: "(Some pfx1, Some x2a) = longest_disj_pfx (a1' # l1') l2"
          using prems by simp
        moreover obtain t where t: "a1' # l1' = pfx1 @ t"
          using disj_pref_append1 eq by blast
        have "a2 \<notin> set pfx1"
        proof
          assume "a2 \<in> set pfx1"
          then have "a2 \<in> set (pfx1 @ t)"
            by simp
          then have "a2 \<in> set (a1' # l1')"
            using t by simp
          then have "a2 = a1'"
            using \<open>l1' = []\<close> by simp
          then show False
            using prems by auto
        qed
        moreover have "set pfx1 \<inter> set (butlast x2a) = {}"
        proof -
          have "set pfx1 \<inter> set (butlast (the (Some x2a))) = {}"
            using eq prems by blast
          then show ?thesis
            by simp
        qed
        ultimately show ?thesis
          by blast
      qed
      subgoal premises prems
      proof -
        have eq: "(Some pfx1, None) = longest_disj_pfx (a1' # l1') l2"
          using prems by simp
        then show ?thesis
          using cons1(1) by blast
      qed
      subgoal premises prems for pfx2'
      proof -
        have rec: "longest_disj_pfx (a1' # l1') l2 = (Some pfx1, Some pfx2')"
          using prems by simp
        have not_last: "last (find_pfx ((=) a2) (a1' # l1')) \<noteq> a2"
          using prems by simp
        have pfx2'_nempty: "pfx2' \<noteq> []"
          using snd_pfx_nempty[of "Some pfx1" pfx2' "a1' # l1'" l2] rec
          by simp
        have a2_notin_l1: "a2 \<notin> set (a1' # l1')"
        proof (rule notI)
          assume "a2 \<in> set (a1' # l1')"
          then have em: "a2 = a1' \<or> a2 \<in> set l1'" by simp
          then show False
          proof (cases "a2 = a1'")
            case True
            then show False
              using not_last by simp
          next
            case False
            then have fp: "find_pfx ((=) a2) (a1' # l1') = a1' # find_pfx ((=) a2) l1'"
              by simp
            from em have in_l1: "a2 \<in> set l1'"
              using False by simp
            have ne: "find_pfx ((=) a2) l1' \<noteq> []"
              using Graph_Quotient.find_pfx_nempty [OF in_l1, of "(=) a2"] by simp
            have las: "last (find_pfx ((=) a2) l1') = a2"
              using find_pfx_works_1 [OF in_l1, of "(=) a2"] by simp
            have "last (find_pfx ((=) a2) (a1' # l1')) = a2"
              using fp ne las by simp
            then show False
              using not_last by simp
          qed
        qed
        obtain l1'' where pfx1_pfx: "a1' # l1' = pfx1 @ l1''"
          using disj_pref_append1[of pfx1 "Some pfx2'" "a1' # l1'" l2] rec
          by fastforce
        have a2_notin_pfx1: "a2 \<notin> set pfx1"
          using a2_notin_l1 pfx1_pfx
          by auto
        have ih: "set pfx1 \<inter> set (butlast pfx2') = {}"
          using cons1.IH[of pfx1 "Some pfx2'" "a1' # l1'"] rec
          by simp
        have "butlast (a2 # pfx2') = a2 # butlast pfx2'"
          using pfx2'_nempty
          by simp
        then show ?thesis
          using a2_notin_pfx1 ih prems
          by auto
      qed
      done
  qed
qed

lemma find_pfx_butlast_2:
  assumes "x \<in> set (butlast (find_pfx Q l))"
  shows "\<not>Q x"
  using assms
proof(induction l)
  case Nil
  then show ?case
    by auto
next
  case (Cons a' l')
  show ?case
  proof(cases "x = a'")
    case True
    then show ?thesis
      using Cons
      by auto
  next
    case False
    then show ?thesis
      using Cons
      by (auto split: if_splits)
  qed
qed

lemma disj_pfx_are_disj_2:
  assumes "(Some pfx1, Some pfx2) = (longest_disj_pfx l1 l2)"
  shows "set (butlast pfx1) \<inter> set pfx2 = {}"
  using assms
proof(induction l2 arbitrary: l1 pfx1 pfx2)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1(1,2)
      apply (clarsimp simp add: Let_def split: if_splits prod.splits option.splits)
      subgoal using find_pfx_butlast_2 by fastforce
      subgoal premises prems for x2a
      proof -
        have rec: "longest_disj_pfx (a1' # l1') l2 = (Some pfx1, Some x2a)"
          using prems by simp
        have ih: "set (butlast pfx1) \<inter> set x2a = {}"
          using prems(2)[of pfx1 x2a "a1' # l1'"] rec by simp
        have a2_notin_l1: "a2 \<notin> set (a1' # l1')"
        proof (rule notI)
          assume "a2 \<in> set (a1' # l1')"
          then have em: "a2 = a1' \<or> a2 \<in> set l1'" by simp
          then show False
          proof (cases "a2 = a1'")
            case True
            then show False using prems by auto
          next
            case False
            then have in_l1: "a2 \<in> set l1'" using em by simp
            have las: "last (find_pfx ((=) a2) l1') = a2"
              using find_pfx_works_1[OF in_l1, of "(=) a2"] by simp
            have ne: "find_pfx ((=) a2) l1' \<noteq> []"
              using Graph_Quotient.find_pfx_nempty[OF in_l1, of "(=) a2"] by simp
            then show False
              using prems las by auto
          qed
        qed
        obtain l1'' where pfx1_pfx: "a1' # l1' = pfx1 @ l1''"
          using disj_pref_append1[of pfx1 "Some x2a" "a1' # l1'" l2] rec
          by fastforce
        have a2_notin_pfx1: "a2 \<notin> set pfx1"
          using a2_notin_l1 pfx1_pfx
          by auto
        have "a2 \<notin> set (butlast pfx1)"
          using a2_notin_pfx1 by (blast dest: in_set_butlastD)
        then show ?thesis
          using ih by auto
      qed
      subgoal by (metis butlast.simps(2) cons1.prems disj_pfx_are_disj_1 disjoint_iff_not_equal in_set_butlastD list.set_intros(1) option.sel snd_pfx_nempty)
      done
  qed
qed

lemma disj_pfx_are_disj_3:
  assumes "(Some pfx1, l2_pfx) = (longest_disj_pfx l1 l2)"
  shows "set (butlast pfx1) \<inter> set (butlast (the l2_pfx)) = {}"
  using assms disj_pfx_are_disj_1
proof -
  have "set pfx1 \<inter> set (butlast (the l2_pfx)) = {}"
    using disj_pfx_are_disj_1[OF assms] .
  then show ?thesis
    using in_set_butlastD by fastforce
qed

lemma disj_pfx_is_complete:
  assumes "(None, l2_pfx) = (longest_disj_pfx l1 l2)"
  shows "set l1 \<inter> set l2 = {}"
  using assms
proof(induction l2 arbitrary: l1 l2_pfx)
  case Nil
  then show ?case by auto
next
  case cons1: (Cons a2 l2)
  show ?case
  proof(cases l1)
    case Nil
    then show ?thesis
      using cons1
      by (auto simp add: Let_def)
  next
    case (Cons a1' l1')
    then show ?thesis
      using cons1(1,2)
      apply (clarsimp simp add: Let_def split: if_splits prod.splits option.splits)
      subgoal premises pre
      proof -
        from pre have "l1' = []" by (auto dest: find_pfx_empty)
        then have a2n: "a2 \<notin> set l1'" by simp
        from pre(5) have iheq: "(None, None) = longest_disj_pfx (a1' # l1') l2"
          by (rule sym)
        have ihdisj: "set (a1' # l1') \<inter> set l2 = {}"
          using pre iheq by blast
        from a2n ihdisj show "a2 \<notin> set l1' \<and> a1' \<notin> set l2 \<and> set l1' \<inter> set l2 = {}"
          by auto
      qed
      subgoal by (metis IntI empty_iff empty_set find_pfx_empty inf_right_idem list.set_intros(1))
      subgoal premises prems
      proof -
        from prems have ne: "last (find_pfx ((=) a2) l1') \<noteq> a2" by blast
        have "a2 \<notin> set l1'"
        proof
          assume "a2 \<in> set l1'"
          then have "a2 = last (find_pfx ((=) a2) l1')"
            by (auto intro: find_pfx_works_1)
          with ne show False by simp
        qed
        moreover have "set (a1' # l1') \<inter> set l2 = {}"
        proof -
          from prems have "(None, None) = longest_disj_pfx (a1' # l1') l2" by simp
          with prems show "set (a1' # l1') \<inter> set l2 = {}" by blast
        qed
        ultimately show "a2 \<notin> set l1' \<and> a1' \<notin> set l2 \<and> set l1' \<inter> set l2 = {}"
          by auto
      qed
      subgoal premises prems
      proof -
        from prems have ne: "last (find_pfx ((=) a2) l1') \<noteq> a2" by blast
        have a2n: "a2 \<notin> set l1'"
        proof
          assume "a2 \<in> set l1'"
          then have "a2 = last (find_pfx ((=) a2) l1')"
            by (auto intro: find_pfx_works_1)
          with ne show False by simp
        qed
        moreover have ihdisj: "set (a1' # l1') \<inter> set l2 = {}"
        proof -
          from prems have "longest_disj_pfx (a1' # l1') l2
              = (None, snd (longest_disj_pfx (a1' # l1') l2))"
            by (cases "longest_disj_pfx (a1' # l1') l2") auto
          then have iheq: "(None, snd (longest_disj_pfx (a1' # l1') l2))
              = longest_disj_pfx (a1' # l1') l2"
            by (rule sym)
          with prems show "set (a1' # l1') \<inter> set l2 = {}" by blast
        qed
        ultimately show "a2 \<notin> set l1' \<and> a1' \<notin> set l2 \<and> set l1' \<inter> set l2 = {}"
          by auto
      qed
      done
  qed
qed

lemma back_subst_2: "(Q a b \<Longrightarrow> P a b) \<Longrightarrow> Q c d \<Longrightarrow> a = c \<Longrightarrow> b = d \<Longrightarrow> P c d"
  by simp

lemma pfxs_alt_path':
  assumes
    pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2" and
    alt_paths: "alt_path M (hd p2 # p1)" "alt_path M (hd p1 # p2)"
    "last p1 \<notin> Vs M" and
    odd_lens: "odd (length p1)" "odd (length p2)"
  shows "alt_path M (rev (drop (length pfx1) p1) @ rev pfx1 @ pfx2)"
proof-
  have "(rev (drop (length pfx1) p1)) @ rev pfx1 = rev p1"
    using assms(1) disj_pref_append1 by fastforce
  moreover have "alt_path M ((rev p1) @ pfx2)"
  proof(cases pfx2)
    case Nil
    then show ?thesis
      using snd_pfx_nempty pfxs_are_pfxs
      by auto
  next
    have "p1 \<noteq> []"
      using disj_pref_append1 first_pfx_nempty pfxs_are_pfxs by fastforce
    then have eqop_append: "edges_of_path (rev p1 @ pfx2) = edges_of_path (rev p1) @ edges_of_path (hd p1 # pfx2)"
      using edges_of_path_append_2 edges_of_path_rev
  proof -
    have p1_nempty: "p1 \<noteq> []"
      using disj_pref_append1 first_pfx_nempty pfxs_are_pfxs by fastforce
    hence rev_p1_nempty: "rev p1 \<noteq> []"
      by simp
    hence "edges_of_path (rev p1 @ pfx2) = edges_of_path (rev p1) @ edges_of_path (last (rev p1) # pfx2)"
      using edges_of_path_append_3[OF rev_p1_nempty, of pfx2] by simp
    moreover have "last (rev p1) = hd p1"
      using p1_nempty by (simp add: last_rev)
    ultimately show ?thesis
      by simp
  qed
    case (Cons a' pfx2')
    then have "hd (edges_of_path p1) \<in> M" if "edges_of_path (rev p1) \<noteq> []"
      using alt_paths(1) that[unfolded edges_of_path_rev[symmetric]] \<open>p1 \<noteq> []\<close>
      by(auto simp add: neq_Nil_conv alt_list_step)
    then have "last (edges_of_path (rev p1)) \<in> M" if "edges_of_path (rev p1) \<noteq> []"
      using that Cons
      by(simp add: edges_of_path_rev[symmetric] last_rev)
    moreover have "alt_path M (rev p1)" if "edges_of_path (rev p1) \<noteq> []"
      apply(intro odd_alt_path_rev)
      subgoal using odd_lens(1) .
      subgoal using that
        by (simp add: edges_of_path_nempty)
      subgoal using alt_paths
        by(intro alt_path_cons_odd[where p = p1 and v = "hd p2"] odd_lens(1); simp)+
      done
    moreover have "alt_path M ((hd p1)#pfx2)"
    proof -
      obtain p2' where "p2 = pfx2 @ p2'"
        using disj_pref_append2[OF pfxs_are_pfxs]
        by rule
      have *:"butlast (hd p1 # pfx2) @ [last (hd p1 # pfx2)] = (hd p1 # pfx2)"
        by simp
      have **:"b # l1 @ a # l2 = b # (l1 @ [a]) @ l2" for l1 l2 a b
        by simp
      have "edges_of_path ((hd p1 # pfx2) @ p2') = edges_of_path (hd p1 # pfx2) @ edges_of_path (last (hd p1 # pfx2) # p2')" (is "?a = ?b")
        using edges_of_path_append_2[where ?p = "butlast (hd p1 # pfx2)" and ?p' = "last (hd p1 # pfx2) # p2'", unfolded *]
        apply (simp add: Cons split: if_splits)
        by (simp add: "**")
      then show ?thesis
        apply(subst conjunct1[OF alt_list_append_1[where ?l2.0 = "edges_of_path (last (hd p1 # pfx2) # p2')"]])
        using alt_paths(2)
        by (simp add: \<open>p2 = pfx2 @ p2'\<close>)+
    qed
    ultimately show ?thesis
      using alternating_list_odd_last odd_pos
      by (fastforce simp: eqop_append alt_list_empty intro!: alt_list_append_3)+
  qed
  ultimately show ?thesis
    using \<open>alt_path M (rev p1 @ pfx2)\<close> \<open>rev (drop (length pfx1) p1) @ rev pfx1 = rev p1\<close>
    by (simp only: append.assoc[symmetric])
qed

lemma pfxs_path:
  assumes
    pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2" and
    paths: "path G p1" "path G p2"
    "{hd p1, hd p2} \<in> G"
  shows "path G (rev (drop (length pfx1) p1) @ rev pfx1 @ pfx2)"
proof-
  have "(rev (drop (length pfx1) p1)) @ rev pfx1 = rev p1"
    using assms(1) disj_pref_append1 by fastforce
  moreover have "path G ((rev p1) @ pfx2)"
  proof(cases pfx2)
    case Nil
    then show ?thesis
      using snd_pfx_nempty pfxs_are_pfxs
      by auto
  next
    case (Cons a' pfx2')
    have "p1 \<noteq> []"
      using disj_pref_append1 first_pfx_nempty pfxs_are_pfxs by fastforce
    moreover have "path G (rev p1)"
      by (simp add: paths(1) rev_path_is_path)
    moreover have "hd pfx2 = hd p2"
      using Cons disj_pref_append2
        pfxs_are_pfxs
      by fastforce
    moreover have "path G pfx2"
      using disj_pref_append2[OF pfxs_are_pfxs] path_pref paths(2)
      by auto
    ultimately show ?thesis
      apply(intro path_append)
      using paths(3)
      by (simp add: last_rev edges_of_path_rev[symmetric])+
  qed
  ultimately show ?thesis
    by (simp add: append.assoc[symmetric])
qed

lemma pfxs_distinct:
  assumes
    pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2" and
    distinct: "distinct p1" "distinct p2"
    "p1 = pfx1 @ p'" "p2 = pfx2 @ p'"
  shows "distinct (rev (drop (length pfx1) p1) @ butlast (rev pfx1 @ pfx2))"
proof-
  have "(rev (drop (length pfx1) p1)) @ rev pfx1 = rev p1"
    using assms(1) disj_pref_append1 by fastforce
  moreover have "butlast (rev pfx1 @ pfx2) = (rev pfx1 @ (butlast pfx2))"
    using assms
    by (metis butlast_append snd_pfx_nempty)
  moreover have "distinct ((rev p1) @ (butlast pfx2))"
    apply(simp add: )
    by (smt Un_iff append_butlast_last_id butlast.simps(1) disj_pfx_are_disj_1 disjoint_iff_not_equal distinct(1) distinct(2) distinct(3) distinct(4) distinct_append option.sel pfxs_are_pfxs set_append)
  ultimately show ?thesis
    by (metis append.assoc)
qed

lemma pfxs_odd_cycle':
  assumes pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2" and
    from_tree: "p1 = pfx1 @ p" "p2 = pfx2 @ p" and
    alt_paths: "alt_path (-M) p1" "alt_path (-M) p2"
    "{hd p1, hd p2} \<notin> M" and 
    hds_neq: "hd p1 \<noteq> hd p2" and
    even_lens: "odd (length p1)" "odd (length p2)"
  shows "odd_cycle (rev pfx1 @ pfx2)"
proof-
  have "length (rev pfx1 @ pfx2) \<ge> 3"
  proof(rule ccontr)
    assume "\<not> 3 \<le> length (rev pfx1 @ pfx2)"
    moreover have "rev pfx1 \<noteq> []"
      using first_pfx_nempty pfxs_are_pfxs by auto
    moreover have "pfx2 \<noteq> []"
      using snd_pfx_nempty pfxs_are_pfxs by auto
    ultimately have "length (rev pfx1 @ pfx2) = 2"
      apply(cases pfx1; cases pfx2; simp)
      using le_simps(3) by blast+
    then obtain a1 a2 where a1a2: "pfx2 = [a2]" "pfx1 = [a1]"
      using \<open>rev pfx1 \<noteq> []\<close> \<open>pfx2 \<noteq> []\<close>
      by (cases pfx1; cases pfx2; auto)
    then have "a1 = a2"
      using pfx_common_end pfxs_are_pfxs by fastforce
    moreover have "a1 = hd p1"
      using a1a2
      using disj_pref_append1 pfxs_are_pfxs by fastforce
    moreover have "a2 = hd p2"
      using a1a2
      using disj_pref_append2 pfxs_are_pfxs by fastforce
    ultimately show False
      using hds_neq
      by auto
  qed
  moreover have "hd ((rev pfx1) @ pfx2) = last ((rev pfx1) @ pfx2)"
  proof-
    have "rev pfx1 \<noteq> []"
      using first_pfx_nempty pfxs_are_pfxs by auto
    moreover have "pfx2 \<noteq> []"
      using snd_pfx_nempty pfxs_are_pfxs by auto
    moreover have "hd (rev pfx1) = last pfx2" 
      using hd_rev pfx_common_end pfxs_are_pfxs
      by (metis option.sel)
    ultimately show ?thesis
      by auto
  qed
  moreover have "odd (length (edges_of_path ((rev pfx1) @ pfx2)))"
  proof(cases "odd (length pfx1) \<and> odd (length pfx2)")
    case T1: True
    then have "odd (length (rev pfx1))"
      by simp
    then have "even (length ((rev pfx1) @ pfx2))"
      using T1
      by simp
    then show ?thesis
      by (metis Nil_is_append_conv T1 edges_of_path_length' even_add odd_one)
  next
    case F1: False
    moreover{
      assume ass: "even (length pfx1)" "odd (length pfx2)"
      then have False
        using alt_paths(2) from_tree(2)
          even_lens from_tree(1)
        by auto
    }
    moreover{
      assume ass: "odd (length pfx1)" "even (length pfx2)"
      then have False
        using alt_paths(2) from_tree(2)
          even_lens from_tree(1)
        by auto
    }
    ultimately show ?thesis
      by (metis Nil_is_append_conv edges_of_path_length' even_add from_tree(1) from_tree(2) hds_neq
                length_append length_rev odd_one rev_is_Nil_conv)
  qed
  ultimately show ?thesis
    unfolding odd_cycle_def
    by simp
qed

lemma pfxs_even_stem':
  assumes pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2" and
    from_tree: "p1 = pfx1 @ p" "p2 = pfx2 @ p" and
    alt_paths: "alt_path M (hd p2 # p1)" "alt_path M (hd p1 # p2)"
    "last p1 \<notin> Vs M" and 
    hds_neq: "hd p1 \<noteq> hd p2" and
    odd_lens: "odd (length p1)" "odd (length p2)" and
    distinct: "distinct p1" "distinct p2" and
    matching: "matching M"
  shows "even (length (edges_of_path (rev (drop (length pfx1) p1) @ [hd (rev pfx1 @ pfx2)])))"
proof-
  have "hd (rev pfx1 @ pfx2) = hd (rev pfx1)"
    using first_pfx_nempty hd_append2 pfxs_are_pfxs by blast
  moreover have "(drop (length pfx1) p1) = p"
    by (simp add: from_tree(1))
  have pfx1_nempty: "pfx1 \<noteq> []"
    using pfxs_are_pfxs first_pfx_nempty snd_pfx_nempty
    by auto
  have pfx2_nempty: "pfx2 \<noteq> []"
    using pfxs_are_pfxs snd_pfx_nempty
    by auto

  have last_pfx1_eq: "last pfx1 = last pfx2"
    using pfx_common_end pfxs_are_pfxs by fastforce

  have last_pfxs_neq: "last (butlast pfx2) \<noteq> last (butlast pfx1)"
                      if "length pfx1 \<ge> 2" "length pfx2 \<ge> 2" "set (butlast pfx1) \<inter> set pfx2 = {}"
                      for pfx1 pfx2
    using that
    by (metis Suc_1 diff_is_0_eq disjoint_iff in_set_butlastD last_in_set length_butlast list.size(3)
              not_less_eq_eq)

  {
    fix p1 pfx1 p2 pfx2::"'a list"
    assume "p \<noteq> []"
    assume "length pfx1 \<ge> 2"
    then have pfx1_nempty: "pfx1 \<noteq> []"
      by auto
    assume pfx2_nempty: "pfx2 \<noteq> []"
    assume from_tree: "p1 = pfx1 @ p" "p2 = pfx2 @ p"
    assume odd_lens: "odd (length p1)" "odd (length p2)"
    assume last_pfx1_eq: "last pfx1 = last pfx2"
    assume hds_neq: "hd p1 \<noteq> hd p2"
    assume pfxs_disj: "set (butlast pfx1) \<inter> set pfx2 = {}"
    assume distinct: "distinct p1"
    {
      fix p1 pfx1::"'a list"
      assume from_tree: "p1 = pfx1 @ p"
      assume odd_lens: "odd (length p1)"
      assume alt_paths: "alt_path (-M) p1" "last p1 \<notin> Vs M"
      assume "length pfx1 \<ge> 2"
      then have "pfx1 \<noteq> []"
        by auto
      have "alt_path M ((rev p) @ [last pfx1, last (butlast pfx1)])"
      proof-
        have "last (edges_of_path ((last pfx1) # p)) = last (edges_of_path p1)"
          apply( simp add: from_tree(1) edges_of_path_append_2[OF \<open>p \<noteq> []\<close>])
          using \<open>pfx1 \<noteq> []\<close> \<open>p \<noteq> []\<close>
          by (metis edges_of_path.simps(3) edges_of_path_append_2 edges_of_path_append_3 last_appendR neq_Nil_conv)
        moreover have "last (edges_of_path p1) \<notin> M"
        proof-
          have "(edges_of_path p1) \<noteq> []"
            by (simp add: \<open>2 \<le> length pfx1\<close> \<open>pfx1 \<noteq> []\<close> edges_of_path_append_3 edges_of_path_nempty from_tree)
          then show ?thesis
            using alt_paths(2) edges_of_path_nempty last_edge_in_last_vert_in
            by auto
        qed
        ultimately have "last (edges_of_path ((last pfx1) # p)) \<notin> M"
          by auto
        moreover have "length p1 \<ge> 2"
          using \<open>2 \<le> length pfx1\<close> from_tree
          by simp
        ultimately have revp1_alt: "alt_path M (rev p1)"
          apply(intro odd_alt_path_rev alt_paths odd_lens)
          by simp+
        have "\<exists>pfx1'. rev pfx1 = [last pfx1, last (butlast pfx1)] @ pfx1'"
        proof-
          have "length (rev pfx1) \<ge>  2"
            using \<open>length pfx1 \<ge>  2\<close>
            by simp
          then obtain a b pfx1'' where "rev pfx1 = a # b # pfx1''"
            apply (simp only: numeral_2_eq_2 Suc_le_length_iff)
            by fastforce
          then have pfx1'': "pfx1 = ((rev pfx1'') @ [b]) @ [a]"
            by auto
          then have "a = last pfx1" "b = last (butlast pfx1)"
            by (simp only: butlast_snoc last_snoc)+
          then show ?thesis
            using pfx1''
            by fastforce
        qed
        then obtain pfx1' where "rev pfx1 = ([last pfx1, last (butlast pfx1)]) @ pfx1'"
          by metis
        then have revp1_eq: "rev p1 = (rev p @ [last pfx1, last (butlast pfx1)]) @pfx1'"
          using from_tree(1)
          by auto
        have eop_cat: "edges_of_path ((rev p @ [last pfx1, last (butlast pfx1)]) @ pfx1') = (edges_of_path (rev p @ [last pfx1, last (butlast pfx1)]) @ (edges_of_path ((last (butlast pfx1)) # pfx1')))"
          using edges_of_path_append_2
          by (smt (verit, best) append_is_Nil_conv edges_of_path_append_3 last.simps last_append list.discI)
        show ?thesis
          apply(rule conjunct1[OF alt_list_append_1])
          using revp1_alt
          by (simp only: eop_cat revp1_eq)
      qed
    }note * = this
    assume alt_paths: "alt_path M (hd p2 # p1)" "alt_path M (hd p1 # p2)" "last p1 \<notin> Vs M" 
    then have alt_paths': "alt_path (-M) p1" "alt_path (-M) p2" "{hd p1, hd p2} \<notin> M"
      by(intro alt_path_cons_odd[where p = p1 and v = "hd p2"] alt_path_cons_odd[where p = p2 and v = "hd p1"] odd_lens; simp)+
    have alt_path_pfx1: "alt_path M (rev p @ [last pfx1, last (butlast pfx1)])"
      using *[OF from_tree(1) odd_lens(1) alt_paths'(1) alt_paths(3) \<open>length pfx1 \<ge> 2\<close>]
      by simp
    have "alt_path M (rev p @ [last pfx1])"
      using alt_path_pfx1
      by (metis alt_list_append_1 edges_of_path_append_2 list.sel(1) list.simps(3))
    moreover assume odd_length: "odd (length (edges_of_path ((last pfx1) # p)))"
    ultimately have "last (edges_of_path ((rev p) @ [last pfx1])) \<notin> M"
      using alternating_list_gt_last[OF alternating_gt_odd]
      by (metis One_nat_def edges_of_path_rev even_Suc length_rev list.size(3) odd_one rev.simps(2))
    have "even (length (edges_of_path ((rev p) @ [last pfx1, last (butlast pfx1)])))"
      using odd_length
      by (metis One_nat_def append.assoc append_Cons append_Nil edges_of_path.simps(3) edges_of_path_rev length_rev list.size(4) odd_even_add odd_one rev.simps(2))
    then have "last (edges_of_path ((rev p) @ [last pfx1, last (butlast pfx1)])) \<in> M"
      using alt_path_pfx1
      by (metis Nil_is_append_conv \<open>p \<noteq> []\<close> alternating_list_even_last edges_of_path.simps(3) edges_of_path_append_3 list.simps(3) rev_is_Nil_conv)
    then have last_pfx1_matched: "{last pfx1, last (butlast pfx1)} \<in> M"
      by (metis edges_of_path.simps(2) edges_of_path.simps(3) edges_of_path_append last_snoc)
    have False
    proof(cases "length pfx2 > 1")
      case gt_1: True
      then have "length pfx2 \<ge> 2"
        by auto
      show ?thesis
      proof(cases "{last pfx2, last (butlast pfx2)} \<in> M")
        case last_pfx2_matched: True
        have "last (butlast pfx2) \<noteq> last (butlast pfx1)"
          using last_pfxs_neq[OF \<open>2 \<le> length pfx1\<close> \<open>2 \<le> length pfx2\<close> pfxs_disj]
          by blast
        then have "{last pfx2, last (butlast pfx2)} \<noteq> {last pfx1, last (butlast pfx1)}"
          using last_pfx1_eq
          by (auto simp add: doubleton_eq_iff)
        then show ?thesis 
          using matching last_pfx1_matched last_pfx2_matched \<open>last pfx1 = last pfx2\<close>
          by (metis edges_are_Vs insertI1 matching_def2)
      next
        have "last p2 \<notin> Vs M"
          using from_tree alt_paths(3) 
          by (simp add: \<open>p \<noteq> []\<close>)
        then have alt_path_pfx2: "alt_path M (rev p @ [last pfx2, last (butlast pfx2)])"
          using *[OF from_tree(2) odd_lens(2) alt_paths'(2) _ \<open>length pfx2 \<ge> 2\<close>]
          by simp
        moreover have "even (length (edges_of_path (rev p @ [last pfx2, last (butlast pfx2)])))"
          using odd_length \<open>last pfx1 = last pfx2\<close>
          by (metis One_nat_def append.assoc append_Cons append_Nil edges_of_path.simps(3) edges_of_path_rev length_rev list.size(4) odd_even_add odd_one rev.simps(2))
        moreover have "last (edges_of_path (rev p @ [last pfx2, last (butlast pfx2)])) = {last pfx2, last (butlast pfx2)}"
          by (metis edges_of_path.simps(2) edges_of_path.simps(3) edges_of_path_append last_snoc)
        ultimately have "{last pfx2, last (butlast pfx2)} \<in> M"
          using alternating_list_even_last edges_of_path_nempty by fastforce
        moreover case last_pfx2_unmatched: False
        ultimately show ?thesis
          by auto
      qed
    next
      case False
      then have "length pfx2 \<le> 1"
        by auto
      then have "length pfx2 = 1"
        using pfx2_nempty
        by (simp add: le_less)
      then have "hd pfx2 = last pfx2"
        by (auto simp add: numeral_2_eq_2 length_Suc_conv)
      then have "{hd pfx1, last pfx2} \<notin> M"
        using alt_paths'(3) from_tree(1) from_tree(2) pfx1_nempty pfx2_nempty
        by auto
      moreover have "{last pfx2, hd p} \<notin> M"
        by (metis (no_types, lifting) Nil_is_rev_conv \<open>last (edges_of_path (rev p @ [last pfx1])) \<notin> M\<close> \<open>p \<noteq> []\<close> edges_of_path_snoc insert_commute last_pfx1_eq last_rev snoc_eq_iff_butlast)
      ultimately show ?thesis
        using alt_paths(2) \<open>length pfx1 \<ge> 2\<close> \<open>length pfx2 = 1\<close> \<open>p \<noteq> []\<close>
        by(auto simp add: from_tree numeral_2_eq_2 Suc_le_length_iff length_Suc_conv neq_Nil_conv alt_list_step alt_list_empty)
    qed
  } note p_nempty_even = this

  show ?thesis
  proof(cases "p = []")
    case p_empty: True
    then show ?thesis
      by (simp add: \<open>drop (length pfx1) p1 = p\<close>)
  next
    case p_nempty: False
    show ?thesis
    proof(cases "2 \<le> length pfx1")
      case len_pf1_ge_2: True
      have "set (butlast pfx1) \<inter> set pfx2 = {}"
        by (simp add: disj_pfx_are_disj_2 pfxs_are_pfxs)
      show ?thesis
        using p_nempty_even[OF p_nempty len_pf1_ge_2 pfx2_nempty from_tree odd_lens \<open>last pfx1 = last pfx2\<close> hds_neq \<open>set (butlast pfx1) \<inter> set pfx2 = {}\<close> distinct(1) alt_paths(1,2,3)]
        by (metis \<open>drop (length pfx1) p1 = p\<close> calculation edges_of_path_rev hd_rev length_rev pfx1_nempty rev.simps(2))
    next
      case False
      then have len_pf1_le_1: "length pfx1 \<le> 1"
        by auto
      show ?thesis
      proof(cases "2 \<le> length pfx2")
        case len_pf2_ge_2: True
        have "set (butlast pfx2) \<inter> set pfx1 = {}"
          using disj_pfx_are_disj_1 pfxs_are_pfxs by fastforce
        have "{hd p2, hd p1} \<notin> M"
          by(intro alt_path_cons_odd alt_paths(1) odd_lens)
        have "last p2 \<notin> Vs M"
          using assms(6) from_tree(1) from_tree(2) p_nempty by auto
        have "last pfx2 = last pfx1"
          by (simp add: last_pfx1_eq)
        show ?thesis
          using p_nempty_even[OF p_nempty len_pf2_ge_2 pfx1_nempty from_tree(2,1) odd_lens(2,1) \<open>last pfx2 = last pfx1\<close> hds_neq[symmetric] \<open>set (butlast pfx2) \<inter> set pfx1 = {}\<close> distinct(2) alt_paths(2,1) \<open>last p2 \<notin> Vs M\<close>]
          by (metis \<open>drop (length pfx1) p1 = p\<close> calculation edges_of_path_rev hd_rev last_pfx1_eq length_rev pfx1_nempty rev.simps(2))
      next
        case len_pf2_le_1: False
        then show ?thesis
          by (metis One_nat_def Suc_1 append_Nil drop0 drop_all from_tree(1) from_tree(2) hds_neq
                    impossible_Cons last_pfx1_eq len_pf1_le_1 list.exhaust_sel not_less_eq_eq
                    order_antisym pfx1_nempty pfx2_nempty snoc_eq_iff_butlast)
      qed
    qed
  qed
qed

lemma common_pfxs_form_match_blossom':
  assumes pfxs_are_pfxs: "(Some pfx1, Some pfx2) = longest_disj_pfx p1 p2" and
    from_tree: "p1 = pfx1 @ p" "p2 = pfx2 @ p" and
    alt_paths: "alt_path M (hd p2 # p1)" "alt_path M (hd p1 # p2)"
    "last p1 \<notin> Vs M" and
    hds_neq: "hd p1 \<noteq> hd p2" and
    odd_lens: "odd (length p1)" "odd (length p2)" and
    distinct: "distinct p1" "distinct p2" and
    matching: "matching M"
  shows "match_blossom M (rev (drop (length pfx1) p1)) (rev pfx1 @ pfx2)"
proof-
  have alt_paths': "alt_path (-M) p1" "alt_path (-M) p2" "{hd p1, hd p2} \<notin> M"
    by(intro alt_path_cons_odd[OF odd_lens(1) alt_paths(1)] alt_path_cons_odd[OF odd_lens(2) alt_paths(2)])+
  have "(rev (drop (length pfx1) p1)) @ rev pfx1 = rev p1"
    using assms(1) disj_pref_append1 by fastforce
  then have " (rev (drop (length pfx1) p1) @ rev pfx1 @ pfx2) = rev p1 @ pfx2"
    by auto
  moreover have "p1 \<noteq> []"
    using first_pfx_nempty from_tree(1) pfxs_are_pfxs by auto
  ultimately have "hd (rev (drop (length pfx1) p1) @ rev pfx1 @ pfx2) = last p1"
    by (simp add: \<open>rev (drop (length pfx1) p1) @ rev pfx1 @ pfx2 = rev p1 @ pfx2\<close> hd_rev)
  then show ?thesis
    unfolding match_blossom_def      
    apply(intro conjI pfxs_even_stem'[OF assms(1-5) _ hds_neq odd_lens distinct matching]
        pfxs_odd_cycle'[OF pfxs_are_pfxs from_tree alt_paths'(1,2,3) hds_neq odd_lens]
        pfxs_distinct[OF pfxs_are_pfxs distinct from_tree] 
        pfxs_alt_path'[OF pfxs_are_pfxs alt_paths(1,2) ]
        alt_paths(3))
    subgoal using odd_lens(1) .
    subgoal using odd_lens(2) .
    subgoal by (simp add: assms(6))
    done
qed

lemma construct_aug_path:
  assumes
    disj_paths: "set p1 \<inter> set p2 = {}" and
    nempty: "p1 \<noteq> []" "p2 \<noteq> []" and
    alt_paths: "alt_path M p1" "alt_path M p2"
    "last p1 \<notin> Vs M" "last p2 \<notin> Vs M"
    "{hd p1, hd p2} \<in> M" and 
    even_lens: "even (length p1)" "even (length p2)"
  shows "matching_augmenting_path M ((rev p1) @ p2)"
proof-
  have "length p1 \<ge> 2"
    using alt_paths(3,5) nempty
    apply (auto simp add: Vs_def numeral_2_eq_2 Suc_le_length_iff)
    by (metis edges_of_path.cases insertI1 last.simps list.sel(1))
  then have "last (edges_of_path p1) \<notin> M"
    using alt_paths
    by (meson last_edge_in_last_vert_in)
  then have "alt_path M (rev p1)"
    using alt_paths(1) alt_list_rev
    by (simp add: \<open>2 \<le> length p1\<close> even_alt_path_rev even_lens(1))
  moreover have "last (edges_of_path (rev p1)) \<notin> M"
    apply(simp add: edges_of_path_rev[symmetric])
    by (metis \<open>last (edges_of_path p1) \<notin> M\<close> alt_list_step assms(4) last_rev list.exhaust_sel rev.simps(1))
  moreover have "alt_path (-M) (hd p1 # p2)"
    using alt_paths(2,5)
    by(cases p2; auto simp add: alt_list_step alt_list_empty)
  moreover have "edges_of_path ((rev p1) @ p2) = (edges_of_path (rev p1)) @ (edges_of_path (hd p1 # p2))"
    by (metis (no_types, lifting) edges_of_path_append_2 edges_of_path_rev nempty(1) rev.simps(2) rev_append rev_rev_ident)
  ultimately have "alt_path M ((rev p1) @ p2)"
    apply simp
    apply(intro alt_list_append_2)
    subgoal by auto
    subgoal by auto
    subgoal using  even_lens(1)
      by (simp add: edges_of_path_length'[OF nempty(1)])
    done
  moreover have " 2 \<le> length (rev p1 @ p2)"
    using \<open>2 \<le> length p1\<close> by auto
  moreover have "hd (rev p1 @ p2) \<notin> Vs M"
    by (simp add: assms(6) hd_rev nempty(1))
  moreover have "last (rev p1 @ p2) \<notin> Vs M"
    by (simp add: assms(7) nempty(2))
  ultimately show ?thesis
    unfolding matching_augmenting_path_def
    by simp
qed

lemma construct_aug_path':
  assumes
    disj_paths: "set p1 \<inter> set p2 = {}" and
    nempty: "p1 \<noteq> []" "p2 \<noteq> []" and
    alt_paths: "alt_path M (hd p2 # p1)" "alt_path M (hd p1 # p2)"
    "last p1 \<notin> Vs M" "last p2 \<notin> Vs M" and 
    odd_lens: "odd (length p1)" "odd (length p2)"
  shows "matching_augmenting_path M ((rev p1) @ p2)"
proof(cases "length p1 \<ge> 2")
  case True
  then have "alt_path (-M) p1"
    using alt_paths(1)
    using alt_path_cons_odd(1) odd_lens(1) by fastforce
  have "last (edges_of_path p1) \<notin> M"
    using alt_paths True
    by (meson last_edge_in_last_vert_in)
  moreover have "(edges_of_path p1) \<noteq> []"
    using True
    by (simp add: edges_of_path_nempty)
  ultimately have "last (edges_of_path (rev p1)) \<in> M"
    using \<open>alt_path (-M) p1\<close>
    apply(simp add: edges_of_path_rev[symmetric] last_rev)
    by (metis alt_list_step list.exhaust_sel)  
  moreover have "edges_of_path ((rev p1) @ p2) = (edges_of_path (rev p1)) @ (edges_of_path (hd p1 # p2))"
    by (metis (no_types, lifting) edges_of_path_append_2 edges_of_path_rev nempty(1) rev.simps(2) rev_append rev_rev_ident)
  moreover have "alt_path M (rev p1)"
    using alt_paths(1) alt_list_rev \<open>alt_path (-M) p1\<close>
    by (simp add: True odd_alt_path_rev odd_lens(1))
  ultimately have "alt_path M ((rev p1) @ p2)"
    apply simp
    apply(intro alt_list_append_3)
    subgoal by auto
    subgoal using alt_paths(2) .
    subgoal using alternating_list_odd_last by blast
    done
  moreover have " 2 \<le> length (rev p1 @ p2)"
    using \<open>2 \<le> length p1\<close> by auto
  moreover have "hd (rev p1 @ p2) \<notin> Vs M"
    by (simp add: assms(6) hd_rev nempty(1))
  moreover have "last (rev p1 @ p2) \<notin> Vs M"
    by (simp add: assms(7) nempty(2))
  ultimately show ?thesis
    unfolding matching_augmenting_path_def
    by simp
next
  case False
  then have "p1 = [hd p1]"
    using odd_lens(1)
    by (metis Suc_eq_plus1 edges_of_path_length' edges_of_path_nempty length_0_conv length_Suc_conv
              list.sel(1) nempty(1))
  have "alt_path M ((rev p1) @ p2)"
    using alt_paths(2)
    apply(subst \<open>p1 = [hd p1]\<close>)
    by simp
  moreover have " 2 \<le> length (rev p1 @ p2)"
    using odd_lens(2)
    by (metis False Nil_is_append_conv edges_of_path_length' edges_of_path_nempty even_add
              length_append length_rev nempty(1))
  moreover have "hd (rev p1 @ p2) \<notin> Vs M"
    by (simp add: assms(6) hd_rev nempty(1))
  moreover have "last (rev p1 @ p2) \<notin> Vs M"
    by (simp add: assms(7) nempty(2))
  ultimately show ?thesis
    unfolding matching_augmenting_path_def
    by simp
qed

lemma odd_cycle_length_edges_ge_3:
  assumes "odd_cycle p"
  shows "length (edges_of_path p) \<ge> 3"
  using odd_cycleD[OF assms]
  by (metis One_nat_def Suc_le_eq Suc_pred assms edges_of_path_length gt_zero linorder_neqE_nat
            linorder_not_le odd_cycle_even_verts odd_numeral)

lemma odd_cycle_length_verts_ge_4:
  assumes "odd_cycle p"
  shows "length p \<ge> 4"
  using odd_cycle_length_edges_ge_3[OF assms]
  by (metis Suc_leI assms le_eq_less_or_eq numeral_3_eq_3 numeral_4_eq_4 odd_cycle_def
            odd_cycle_even_verts odd_numeral)

lemma odd_cycle_set_butlast_tl:
  assumes "odd_cycle C"
  shows "set (butlast C) = set (tl C)"
  using odd_cycleD[OF assms] odd_cycle_nempty[OF assms]
  by (simp add: set_butlast_tl)

locale match = graph_abs G for G+ 
  fixes M
  assumes matching: "matching M" "M \<subseteq> G"

end