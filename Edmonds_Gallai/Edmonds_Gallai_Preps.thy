theory Edmonds_Gallai_Preps
  imports Blossom.Blossom_Algo_Contraction 
begin

section \<open>Preparations for the Edmonds-Gallai Decomposition\<close>

subsection \<open>General Even Vertices and Blossoms\<close>

text \<open>Recall that in the Blossom Algorithm, there are even and and odd vertices.
  We generalise that to vertices that are \textit{even w.r.t. a matching} 
 instead of an alternating forest. 
We will later see that both notions of evenness coincide.\<close>

definition 
  "even_vert G M v = (\<exists> p. odd (length p)\<and>
     alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p) \<and> 
     hd p \<notin> Vs M \<and> last p = v \<and> distinct p \<and> (path G p \<or> length p = 1))"

lemma  even_vertI: 
  "\<lbrakk>odd (length p); alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p);
    hd p \<notin> Vs M; last p = v; distinct p; path G p \<or> length p = 1\<rbrakk> \<Longrightarrow> even_vert G M v"
  and even_vertE: 
  "even_vert G M v \<Longrightarrow> 
   (\<And>p. \<lbrakk> odd (length p); alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p); 
          hd p \<notin> Vs M; last p = v; distinct p; path G p \<or> length p = 1\<rbrakk> \<Longrightarrow> R) \<Longrightarrow> R"
  and even_vertD:
  "even_vert G M v \<Longrightarrow> \<exists>p. odd (length p) \<and> alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path p) \<and> 
                           hd p \<notin> Vs M \<and> last p = v \<and> distinct p \<and> (path G p \<or> length p = 1)"
  by(auto simp add: even_vert_def)

definition "even_verts G M = {u | u. even_vert G M u}"

definition "even_alt_path G M s p t =
         ((path G p \<or> length p = 1) \<and> alt_path M p \<and> 
          hd p = s \<and> last p = t \<and>
          odd (length p) \<and> s \<notin> Vs M \<and> distinct p)"

lemma even_alt_pathE:
  "\<lbrakk>even_alt_path G M s p t;
  (\<lbrakk>path G p \<or> length p = 1; alt_path M p; p \<noteq> []; hd p = s; last p = t;
    odd (length p); s \<notin> Vs M; distinct p \<rbrakk> \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
  and even_alt_pathI:
  "(\<lbrakk>path G p \<or> length p = 1; alt_path M p;  hd p = s; last p = t;
    odd (length p); s \<notin> Vs M; distinct p \<rbrakk> \<Longrightarrow> even_alt_path G M s p t) "
  by(cases p)(auto simp add: even_alt_path_def)

lemma even_vert_even_alt_path:
  "even_vert G M v \<longleftrightarrow> (\<exists> u p. (even_alt_path G M u p v))"
proof(rule, all \<open> elim even_vertE | elim exE, elim even_alt_pathE\<close>, goal_cases)
  case (1 p)
  then show ?case
    by(auto intro!: even_alt_pathI exI)
next
  case (2 u p)
  then show ?case 
    by(cases p rule: rev_cases)(auto intro!: even_vertI)
qed

lemma even_vert_image:
  assumes topas:"inj_on f (Vs G \<union> Vs M \<union> {v})" "dblton_graph G"
  shows "even_vert ((`) f ` G) ((`) f ` M) (f v) \<longleftrightarrow> even_vert G M v"
proof-
  have assms:  "inj_on f (Vs G \<union> Vs M)" "dblton_graph G"
    using assms  by (auto simp add: inj_on_Un)
  note big_inj = assms(1)
  show ?thesis
  proof(rule, goal_cases)
    case 1
    then obtain p where p: "odd (length p)" "alt_path ((`) f ` M) p"
      "hd p \<notin> Vs ((`) f ` M)" "last p = (f v)" "distinct p"
      "((path ((`) f ` G) p \<and> length p \<noteq> 1) \<or> length p = 1)"
      by(auto simp add:  even_vert_def)
    thus ?case 
    proof(cases "v \<in> Vs (G \<union> M)", goal_cases)
      case 1
      thus ?case
      proof(elim disjE, goal_cases)
        case 1
        then obtain q where q: "path G q" "p = map f q "
          using path_in_image_to_original_path[of G f p]
            assms(1,2) inj_on_subset[of f "Vs G \<union> Vs M" "Vs G"] 
          by blast
        moreover have "inj_on f (Vs M \<union> set q)"
          using q(1)  subset_path_Vs
          by(auto intro!: inj_on_subset[OF assms(1)])
        moreover have "hd (map f q) = f (hd q)" 
          using 1 q by(cases q rule: list_cases3) auto
        moreover have "last (map f q) = f (last q)"
          using 1 q by(cases q rule: rev_cases) auto
        moreover have "f (last q) = f v \<Longrightarrow> last q = v"
          using 1 q assms(1) sup_ge1[of G M] vs_union[of G M] inj_on_contraD[of f "Vs (G \<union> M)" _ v]
            path_subset[of G "_ @ [_]" "G \<union> M"] v_in_apath_in_Vs_append[of "G \<union> M" _ _ "[]"]
          by(cases q rule: rev_cases) fastforce+
        moreover have "distinct q" 
          using 1(5) by(auto simp add: distinct_map q)
        ultimately show ?case
          using 1 
          by(auto intro!: exI[of _ q] simp add: even_vert_def alt_path_image Vs_of_imaged_graph)
      next
        case 2
        then show ?case 
          by(auto intro!: exI[of _ "[v]"] simp add: even_vert_def alt_list.intros(1) Vs_of_imaged_graph hd_last_same)
      qed
    next
      case 2
      show ?case
        using 2(7)
        by(auto intro!: exI[of _ "[v]"] simp add: even_vert_def alt_list.intros(1) vs_union)
    qed
  next
    case 2
    then obtain p where "odd (length p)" "alt_path M p" "hd p \<notin> Vs M" "last p = v" "distinct p" 
      "path G p \<or> length p = 1"
      by(auto simp add:  even_vert_def)
    then show ?case
    proof(cases "f v \<in> Vs ((`) f ` M)",goal_cases)
      case 1
      thus ?case
      proof(elim disjE, goal_cases)
        case 1
        moreover have "inj_on f (Vs M \<union> set p)" 
          using calculation(7) assms(1) sup.idem[of "Vs M"]
            sup.commute[of "set p" "Vs M"] subset_path_Vs[of G p]
            inj_on_subset[of f "Vs G \<union> Vs M" "set p \<union> Vs M"] 
          by auto
        moreover have "hd (map f p) = f (hd p)"
          using 1 by(cases p) auto
        moreover have "\<lbrakk>f x = f (hd p); x \<in> Vs M\<rbrakk> \<Longrightarrow> x = hd p" for x 
          using "1"(1) calculation(8) even_zero list.set_sel(1)[of p]
            inj_on_eq_iff[of f "Vs M \<union> set p" "hd p" x] 
          by fastforce
        moreover have "last (map f p) = f (last p)"
          using 1 by(cases p rule: rev_cases) auto
        moreover have "distinct (map f p)"
          using 1 calculation(8) inj_on_Un
          by(auto simp add: distinct_map)
        moreover have "path ((`) f ` G) (map f p)"
          using 1 assms(1) inj_on_Un[of f "Vs G" "Vs M"] subset_path_Vs[of G p]
            sup.orderE[of "set p" "Vs G"]
          by (subst path_image)force
        ultimately show ?case 
          by(auto intro!: exI[of _ "map f p"] 
              simp add: even_vert_def alt_path_image Vs_of_imaged_graph) auto
      next
        case 2
        thus ?case 
          using topas(1) inj_on_image_mem_iff[of f "Vs G \<union> Vs M \<union> {v}" v "Vs M"] hd_last_same[of p]
          by (auto simp add: Vs_def)
      qed
    next
      case 2
      thus ?case
        using assms(1) Vs_of_imaged_graph[of f M] Un_iff[of v "Vs G" "Vs M"]
          inj_on_image_mem_iff[of f "Vs G \<union> Vs M" v "Vs M"]
        by(cases p)(auto intro!: exI[of _ "[f v]"] simp add: even_vert_def alt_list.intros(1))
    qed
  qed
qed

text \<open>All vertices in a blossom are even.\<close>

lemma blossom_verts_are_even:
  assumes  "blossom G M stem C" 
  shows "set C \<subseteq> even_verts G M \<inter> Vs G"
proof(rule, goal_cases)
  case (1 x)
  note assms_rev = flower_reverse_blossom[OF assms(1)]
  note blossomD_rev = blossomD[OF assms_rev]
  note match_blossomD_rev = match_blossomD[OF blossomD(2)]
  note blossomD = blossomD[OF assms(1)]
  note match_blossomD = match_blossomD[OF blossomD(2)]

  obtain i where i: "C ! i = x" "i + 1 < length C"
    using 1 match_blossomD(3) 
    by(cases "x = last C", all \<open>cases C rule: rev_cases\<close>)
      (force elim!:list_cases2_both_sides simp add: odd_cycle_def in_set_conv_nth nth_append)+
  then obtain C1 C2 where C1C2: "C = C1 @[x]@C2" "C2 \<noteq> []" "length C1 = i"
    using id_take_nth_drop[of i C] by auto

  show ?case
  proof(cases "even i")
    case True
    moreover have "odd (length (stem @ C1 @ [x]))"
      using  C1C2(3) True  match_blossomD(5) edges_of_path_length'[of "stem @ [hd C]"]
      by auto
    moreover have "alt_path M (stem @ C1 @ [x])"
      using match_blossomD(1)
      by(simp add: C1C2(1) alt_path_prefix)
    moreover have "hd (stem @ C1 @ [x]) \<notin> Vs M" 
      using match_blossomD(4) 
      by (auto simp add: C1C2(1) hd_append[of "_ @ _" "_ # _", simplified])
    moreover have "distinct (stem @ C1 @ [x])" 
      using match_blossomD(2)
      by(auto simp add: C1C2(1) butlast_append C1C2(2))
    moreover have "path G (stem @ C1 @ [x]) \<or> length (stem @ C1 @ [x]) = 1"
      using C1C2(1) blossomD(1) path_pref[of G "(stem @ C1) @ [x]" C2] by auto
    moreover have "x \<in> Vs G" 
      using "1" local.blossomD(1) mem_path_Vs by fastforce
    ultimately show ?thesis 
      by(auto intro!: even_vertI[where p = "stem@C1 @[x]"] simp add: even_verts_def)
  next
    case False
    hence  C1C2_rev: "rev C = rev C2 @[x]@ rev C1" "C1 \<noteq> []" "even (length C2)"
      using C1C2 False match_blossomD(3) odd_cycle_even_verts by force+
    moreover have "odd (length (stem @ rev C2 @ [x]))"
      using  C1C2_rev(3) match_blossomD(5) edges_of_path_length'[of "stem @ [hd C]"]
      by auto
    moreover have "alt_path M (stem @ rev C2 @ [x])" 
      using calculation(1) blossomD_rev(2)
        Graph_Quotient.match_blossomD(1)[of M stem "(rev C2 @ [x]) @ rev C1"]
        alt_path_prefix[of M "stem @ rev C2 @ [x]" "rev C1"]
      by auto
    moreover have "hd (stem @ rev C2 @ [x]) \<notin> Vs M" 
      using match_blossomD(3,4) C1C2(2) calculation(1) hd_rev[of C] 
        odd_cycleD(3)[of C] hd_append2[of stem C] hd_append2[of stem "rev C2 @ [x]"]
      by fastforce
    moreover have "distinct (stem @ rev C2 @ [x])"
      using calculation(2) C1C2(1) List.butlast_rev[of "C1 @ x # C2"] assms_rev  
        Graph_Quotient.match_blossomD(2)[of M stem "rev (C1 @ x # C2)"]
      by auto
    moreover have "path G (stem @ rev C2 @ [x]) \<or> length (stem @ rev C2 @ [x]) = 1"
      using blossomD_rev(1) calculation(1) path_pref[of G "stem @ rev C2 @ [x]" "rev C1"]
      by auto
    moreover have "x \<in> Vs G" 
      using "1" local.blossomD(1) mem_path_Vs by fastforce
    ultimately show ?thesis 
      by(auto intro!: even_vertI[where p = "stem@ rev C2 @[x]"] 
          simp add: even_verts_def)
  qed
qed

lemma blossom_verts_even_alt_path:
  assumes "blossom G M stem C" "x \<in> set C"
  shows "\<exists> p s. even_alt_path G M s p x"
  using blossom_verts_are_even[OF assms(1)] assms(2)
  by(auto simp add: even_verts_def even_vert_def even_alt_path_def)

subsection \<open>Matchings In Blossoms\<close>

text \<open>Also, odd cycles are factor-critical.\<close>

lemma odd_cycle_graph_near_perfect_matching:
  assumes "dblton_graph G" "odd_cycle p" "set p = Vs G" "distinct (butlast p)" "path G p"
  shows "\<exists> M. graph_matching G M \<and> Vs M = set p - {hd p}"
proof-
  define M where 
    "M = {edges_of_path (butlast p) ! i | i. 0 \<le> i \<and> i + 1 <length (butlast p) \<and> odd i}"
  have path_butlast: "path G (butlast p)" 
    using assms(2,5) odd_cycle_nempty[of "[]"] append_butlast_last_id[of p]
      path_pref[of G "butlast p" "[last p]"]
    by fastforce
  show ?thesis
  proof(rule exI[of _ M], goal_cases)
    case 1
    then show ?case
    proof(rule, goal_cases)
      case 1
      then show ?case
      proof(rule graph_matchingI, goal_cases)
        case 1
        then show ?case
          using assms(4)
          by(auto intro!: odd_edges_of_distinct_path_are_matching[of "butlast _", simplified]
              simp add: M_def)
      next
        case 2
        then show ?case
          unfolding M_def
        proof(rule, goal_cases)
          case (1 e)
          then obtain i where "e = edges_of_path (butlast p) ! i"
            "0 \<le> i" "i + 1 < length (butlast p)" "odd i"
            by auto
          hence "e \<in> set (edges_of_path (butlast p))"
            by (simp add: edges_of_path_length)
          moreover have " set (edges_of_path (butlast p)) \<subseteq>  set (edges_of_path p)"
            using assms(2) edges_of_path_append_subset_2[of "butlast p" "[last p]"]
              append_butlast_last_id[of p]
            by fastforce
          moreover have " set (edges_of_path p) \<subseteq> G"
            by (simp add: assms(5) path_edges_subset)
          ultimately show ?case
            by auto
        qed
      qed
    next
      case 2
      have len_rw:"{edges_of_path (butlast p) ! i |i. 0 \<le> i \<and> i + 1 < length (butlast p) \<and> odd i} =
            {edges_of_path (butlast p) ! i |i. i < length (butlast p) - 1 \<and> odd i}"
        by auto
      have Vs_M_rw: "Vs M = set (butlast (tl p))"
        unfolding M_def len_rw verts_of_odd_edges[of "butlast p"]
        by (auto simp add: assms(2) odd_cycle_even_verts odd_cycle_nempty butlast_tl)
      have p_unfold: "p = hd p # butlast (tl p) @[last p]"
        using assms(2) odd_cycleD(2) odd_cycle_nempty
        by(cases p rule: list_cases3) fastforce+
      hence "hd p \<notin> set (butlast (tl p))" 
        using assms(4) snoc_eq_iff_butlast[of "hd p # butlast (tl p)"
            "last p" "(hd p # butlast (tl p)) @ [last p]"]
        by simp
      thus ?case
        unfolding Vs_M_rw
        by(subst (2) p_unfold)(auto simp add: assms(2) odd_cycleD(3))
    qed
  qed
qed

lemma odd_cycle_graph_factor_critical:
  assumes "dblton_graph G" "odd_cycle p" "set p = Vs G" "distinct (butlast p)"
    "path G p" "x \<in> Vs G"
  shows "\<exists> M. graph_matching G M \<and> Vs M = Vs G - {x}"
proof(cases "x = hd p")
  case True
  then show ?thesis 
    using odd_cycle_graph_near_perfect_matching[OF assms(1,2,3,4,5)] assms(3) 
    by auto
next
  case False
  obtain p1 p2 where p1p2: "p = [hd p]@p1@[x]@p2@[hd p]"
    using False assms(2,3,6) odd_cycleD(3)[of p] split_list_last[of x] 
    by(cases p rule: list_cases_hd_and_last)(force simp add: assms(2) odd_cycle_nempty)+
  have same_length: "length ([x] @ p2 @ [hd p] @ p1 @ [x]) = length p"
    by(subst (2) p1p2) auto
  have new_oc:"odd_cycle ([x] @ p2 @ [hd p] @ p1 @ [x])"
    unfolding odd_cycle_def edges_of_path_length same_length
    by (auto simp add: assms(2) odd_cycleD odd_cycle_nempty odd_cycle_even_verts)
  have distinct_new_oc:"distinct (butlast ([x] @ p2 @ [hd p] @ p1 @ [x]))" 
    using  assms(4) 
    by(subst (asm) p1p2)(auto simp add: butlast_snoc[of "_ @ _ # _", simplified] False)
  have new_path:"path G ([x] @ p2 @ [hd p] @ p1 @ [x])"
    using p1p2 assms(5)
    by(auto intro!: path_concat_2[of G "[x]@p2@[hd p]" "[hd p] @ p1 @ [x]", simplified]
        path_pref[of G "[hd p]@p1@[x]" "p2@[hd p]", simplified]
        path_suff[of G "[hd p]@p1" "[x]@p2@[hd p]", simplified])
  have set_Vs:"set ([x] @ p2 @ [hd p] @ p1 @ [x]) = Vs G"
    using assms(2,3) p1p2 by(cases p)(auto simp add: assms(6)  odd_cycle_nempty)
  hence "insert (hd p) (insert x (set p2 \<union> set p1)) =  Vs G"
    by auto
  thus ?thesis
    using odd_cycle_graph_near_perfect_matching[OF
        assms(1) new_oc set_Vs distinct_new_oc new_path, simplified]
    by simp
qed

subsection \<open>Evenness and Blossom Contraction\<close>

text \<open>Now, we analyse how blossom contraction affects evenness.\<close>

context quot
begin

text \<open>If a vertex is even before contraction w.r.t. a maximum cardinality matching,
  it (or its representative in the quotient) will be even after contraction a blossom.
  We prove this by a reduction to the blossom contraction lemma, which said that there is an
  augmenting path before contraction iff there is one after contraction.
  Because the matching is maximum, there is no augmenting path.
  If a vertex $v$ is even, it is reachable by an even length alternating path
  from an unmatched vertex $s$.
  We turn this path into an augmenting path by adding one vertex $v'$ and 
  the edge $\lbrace v, v'\rbrace$.
  There is an augmenting path after contraction.
  This path must contain $\lbrace v, v'\rbrace$ or the representative thereof,
  otherwise there would be an augmenting path in the original graph.
  We then obtain an even length alternating path to $v$ (or its representative) 
  in the contracted graph.
\<close>

theorem reachbale_by_even_alt_path_contraction:
  assumes match_blossom: "blossom E M stem C" and
    alt_path:  "even_alt_path E M start p target" and 
    matching:  "max_card_matching E M" and
    quot: "s = (Vs E) - set C" "u \<notin>  Vs E"  "u' \<notin> Vs E" "u' \<noteq> u" 
    "target' = (if target \<notin> Vs E then target else 
              if target \<notin> s then u else target)" "target \<noteq> u"
  shows "\<exists>p' start'. even_alt_path (quotG E) (quotG M) start' p' target'"
proof-
  have p_props:
    "path E p \<or> length p = 1" "alt_path M p"
    "hd p = start" "last p = target" "odd (length p)" "start \<notin> Vs M" "distinct p"
    "p\<noteq>[]"
    using alt_path by(auto elim!: even_alt_pathE)
  show ?thesis
  proof(cases "target \<in> Vs E")
    case False
    hence "length p = 1" 
      using mem_path_Vs p_props(1,4,8) by fastforce
    moreover have "target' = target" 
      using quot(5) False by auto

    ultimately show ?thesis 
      using alt_path alt_path False in_quotG_neq_u[of target] quot(1,6)
      by(cases p)
        (auto intro!: exI[of _ p] exI[of _ target] 
          even_alt_pathI alt_list.intros(1) elim: even_alt_pathE) 
  next
    case True
    have p_props:
      "path E p" "alt_path M p"
      "hd p = start" "last p = target" "odd (length p)" "start \<notin> Vs M" "distinct p"
      "p\<noteq>[]"
      using p_props True
      by(auto intro: list.exhaust[of p])
    have M_props: "M \<subseteq> E" "matching M" "\<And> M'. \<lbrakk>M' \<subseteq> E;matching M'\<rbrakk>\<Longrightarrow> card M' \<le> card M"
      "finite M"
      using matching[simplified max_card_matching_def] finite_E finite_subset by auto
    note target_in_E = True
    have target'_def: "target' = (if target \<notin> s then u else target)" 
      using quot(5) True by auto
    hence target_not_u': " target \<noteq> u'"
      using target'_def  quot(3) target_in_E by blast
    have u'_not_in_M: "u' \<notin> Vs M" 
      using M_props(1) Vs_subset quot(3) by blast
    have P_target: "P target = target'" 
      unfolding target'_def by auto
    have interpret_helpers: "dblton_graph ({{target, u'}} \<union> E)"  "finite (Vs ({{target, u'}} \<union> E))"
      using  graph_invar_insert[OF target_not_u' graph]
      by auto
    have quot'_axioms: "quot_axioms ({{target, u'}} \<union> E) (insert u' s) u"
      using quot(3,4) good_quot_map(2) target_not_u'
      by (intro quot_axioms.intro)
        (auto simp add: good_quot_map(1) in_Vs_insert target_in_E vs_insert)
    interpret quot': quot sel "insert {target, u'} E" "insert u' s" u
      using quot'_axioms interpret_helpers 
      by(intro quot.intro pre_quot.intro graph_abs.intro
          interpret_helpers  choose_axioms| simp )+
    have new_blossom: "blossom ({{target, u'}} \<union> E) M stem C"
      using match_blossom path_subset[of E "stem@C" "{{target, u'}} \<union> E"] 
      by auto
    have longer_path: "path ({{target, u'}} \<union> E) (p @ [u'])" 
      using p_props(4) 
      by(auto intro!: path_append path_subset[OF p_props(1)] edges_are_Vs_2)
    have new_edge_not_in_E: "{last p, u'} \<notin> E" "{last p, u'} \<notin> M"
      using quot(3) M_props(1) by (auto simp add:  vs_member')
    have longer_match_path: "matching_augmenting_path M (p @ [u'])"
      using p_props(2,3,5,6,8) new_edge_not_in_E(2) u'_not_in_M
      by (auto intro!: matching_augmenting_pathI alt_list_append_3 alt_list_singleton
          simp add: Suc_le_eq edges_of_path_append_3 edges_of_path_length)
    have new_aug_path: "graph_augmenting_path ({{target, u'}} \<union> E) M (p @ [u'])"
      using longer_path mem_path_Vs'[OF p_props(1), of u'] quot(3)
      by (auto  simp add: p_props(7) longer_match_path)
    have new_untouched_are: "{u'} \<union> s = Vs ({{target, u'}} \<union> E) - set C"
      using match_blossom mem_path_Vs' path_suff quot(3) target_in_E quot(1) 
      by (auto simp add: vs_insert)
    have u_not_in_new_Vs: "u \<notin> Vs ({{target, u'}} \<union> E)"
      using  in_Vs_insertE[of u] quot(2,4) target_in_E 
      by auto
    have quot'_Es_are:"(quot'.quotG ({{target, u'}} \<union> E)) = insert ({target', u'}) (quotG E)"
    proof(rule, all \<open>rule\<close>, goal_cases)
      case (1 e)
      then obtain e' where e': "e' \<in> insert {target, u'} E" "quot'.P ` e' = e" "e' \<noteq> {u}"
        by(auto simp add: quot_graph_def)
      show ?case
      proof(cases "e' = {target, u'}")
        case True
        hence "e = {target', u'}" 
          using e'(2) target'_def target_not_u' by force
        then show ?thesis by simp
      next
        case False
        hence e'_in_E:"e' \<in> E" 
          using e'(1) by auto
        moreover have "u' \<notin> e'" 
          using calculation quot(3) by auto
        ultimately have same_P:"quot'.P ` e' = P ` e'"
          using False e'(2) by auto
        have "e \<in> quotG E"
          using e'_in_E e'(2,3) 1 same_P
          by (auto intro!: bexI[of _ e'] simp add: quot_graph_def)
        thus ?thesis by simp
      qed
    next
      case (2 e)
      show ?case
      proof(cases "e = {target', u'}")
        case True
        hence e_not_u:"e \<noteq> {u}"
          by (simp add: quot(4))
        moreover have "quot'.P ` {target, u'} = e" 
          using True   P_target target_not_u' by auto
        ultimately show ?thesis 
          by(auto simp add: quot_graph_def)
      next
        case False
        then obtain e' where "e' \<in> E" "P ` e' = e" "e \<noteq> {u}"
          using 2 by(auto simp add: quot_graph_def)
        moreover have "quot'.P ` e' = e" 
          using calculation(1,2)  
          by (auto intro: not_in_VsE[OF quot(3)])
        ultimately have "e \<in> quot_graph quot'.P ({{target, u'}} \<union> E)"
          unfolding quot_graph_def by blast
        thus ?thesis
          using \<open>e \<noteq> {u}\<close> by blast
      qed
    qed
    have M_edges_P_same:"e \<in> M \<Longrightarrow> quot'.P ` e = P ` e" for e
      using u'_not_in_M by auto
    have quot'_M_are:"quot'.quotG M = quotG M"
      by(intro arg_cong[of _ _ "\<lambda> x. x - {{u}}"] quot_graph_cong M_edges_P_same)
    have new_Vs_superset: "Vs (quot'.quotG ({{target, u'}} \<union> E)) 
          \<supseteq> insert u' (Vs (quotG E))" 
      unfolding quot'_Es_are
      by (simp add: subset_insertI vs_insert)
    have "\<exists>p'. graph_augmenting_path (quot'.quotG ({{target, u'}} \<union> E))
          (quot'.quotG M ) p'" 
      using M_props(1,2,4) quot(2,4,6) new_untouched_are new_blossom new_aug_path
        subset_insertI2[of M E "{target, u'}"] in_Vs_insertE[of u "{target, u'}" E]
        quot'.aug_path_works_in_contraction[of stem C M "p @ [u']"]
      by force
    then obtain p' where p': "graph_augmenting_path (quot'.quotG ({{target, u'}} \<union> E))
          (quot'.quotG M ) p'" by auto
    have u'_in_p':"u' \<in> set p'"
    proof(rule ccontr, goal_cases)
      case 1
      have "set (edges_of_path p') \<subseteq> quot'.quotG ({{target, u'}} \<union> E)"
        using p' path_edges_subset by blast
      hence e_o_p:"set (edges_of_path p') \<subseteq> (quot_graph P E - {{u}})"
        using 1 unfolding quot'_Es_are 
        by (simp add: edge_not_in_edges_in_path subset_insert)
      have path_old:"path (quot_graph P E - {{u}}) p'"
        using p' matching_augmenting_path_def p'  e_o_p 
        by (intro path_mono[of "quot'.quotG ({{target, u'}} \<union> E)" _ "quotG E"])auto
      have aupath_old:"graph_augmenting_path (quotG E) (quotG M ) p'"
        using p' quot'_M_are
        by (auto simp add:  path_old p')
      have distinct_tl:"distinct (tl C)"
        using match_blossom 
        by(auto simp add: match_blossom_def odd_cycle_def intro: list_cases2_both_sides[of C])
      have big_aug_path: "graph_augmenting_path E M (refine C M p')"
        using match_blossom match_blossomD(3)  match_blossom_alt_cycle 
          distinct_tl  match_blossom path_suff  aupath_old  M_props(1,2) quot(1) 
        by (intro refine)fastforce+
      then obtain M' where "M'\<subseteq>E" "matching M'" "card M < card M'"
        using Berge[OF M_props(4,2,1) dblton_E finite_Vs] by auto
      thus False
        using M_props(3)[of M'] by simp 
    qed
    have "u' = hd p' \<or> u' = last p'"
    proof(rule ccontr, goal_cases)
      case 1
      then obtain p1 p2 where "p' = p1@[u']@p2" "p1\<noteq> []" "p2 \<noteq> []"
        using  split_list_last[OF u'_in_p'] 
        by force
      hence "u' \<in> Vs (quot'.quotG M)"
        using p'  by(auto intro!: in_aug_path_in_Vs[of _ p' u'])
      hence "u' \<in> Vs M" 
        by (simp add: M_props(1) quot'.vert_in_graph_iff_in_quot_diff_u subset_insertI2)
      thus False
        by (simp add: u'_not_in_M)
    qed
    hence "\<exists> p'. graph_augmenting_path (quot'.quotG ({{target, u'}} \<union> E))
          (quot'.quotG M ) p' \<and> last p' = u'"
      using p'
      by(auto intro: exI[of _ "rev p'"] rev_path_is_path
          matching_augmenting_path_rev simp add: last_rev)
    then obtain p' where p':" graph_augmenting_path (quot'.quotG ({{target, u'}} \<union> E))
          (quot'.quotG M ) p'" "last p' = u'" by auto
    then obtain x p'' where xp'':"p' = p''@[x, u']" 
      by (auto elim!: matching_augmenting_pathE intro: list_split_off_last_two)
    hence xu'_in_p':"{x, u'} \<in> set (edges_of_path p')"
      by (simp add: edges_of_path_snoc_2)
    have "{x, u'} \<in> quot'.quotG ({{target, u'}} \<union> E)"
      using path_edges_subset p'(1)  xu'_in_p' by auto
    hence xu'_in_where:"{x, u'} \<in> insert ({target', u'}) (quotG E)"
      using quot'_Es_are by argo
    moreover have "u' \<notin> Vs (quotG E)" "\<nexists> e. e \<in> quotG E \<and> u' \<in> e"
      using in_quotG_neq_u quot(1,3,4) by blast+
    moreover have "x \<noteq> u'" 
      using p' xp'' by auto
    ultimately have x_is_target': "x = target'" by auto
    have butlast_p': "p' = butlast (butlast p') @[x, u']" 
      by (simp add: butlast_append xp'')
    have "even_alt_path (quotG E) (quotG M) (hd p') (butlast p') target'"
    proof(cases "target' \<in> Vs (quotG E)")
      case False
      have path_is_target'_only:"butlast p' = [target']" 
      proof(rule ccontr, goal_cases)
        case 1
        note one = this
        obtain p''' y where "butlast p' = p'''@[y, target']"
        proof(rule list_split_off_last_two[of "butlast p'"], goal_cases)
          case 1
          thus ?case 
            using x_is_target' xp'' one 
            by (all \<open>cases "butlast p'" rule: list_cases3\<close>)(auto simp add: butlast_append)
        next
          case 2
          thus ?case
            using x_is_target' xp'' 1 
            by (auto simp add: butlast_append)
        qed
        hence y_target'_in_p':"{y, target'} \<in> set (edges_of_path (p''@[target']))" 
          unfolding xp'' butlast_append 
          by (simp add: edges_of_path_snoc_2)
        have "{y, target'} \<in> quot'.quotG ({{target, u'}} \<union> E)"
          using set_mp[OF path_edges_subset, of _ p'] p'(1) y_target'_in_p' 
          by (fastforce simp add: edges_of_path_snoc_2 x_is_target' xp'' y_target'_in_p')
        hence yt'_in_big_quot:"{y, target'} \<in> insert ({target', u'}) (quotG E)"
          using quot'_Es_are by argo
        moreover have "y \<noteq> u'"
          using p'(1) v_in_edge_in_path x_is_target' xp'' y_target'_in_p' by fastforce
        ultimately have "{y, target'} \<noteq> {target', u'}"
          by (force simp add: doubleton_eq_iff)
        hence "{y, target'} \<in> quotG E"
          using yt'_in_big_quot by force
        thus False
          using False 
          by blast
      qed
      hence "hd p' = target'" by(cases p' rule: list_cases3) auto
      moreover hence "target' \<notin> Vs (quot_graph P M - {{u}})"
        using False  M_props(1) Vs_subset in_mono quotG_mono[of M E]
        by blast
      ultimately show ?thesis 
        by(auto intro!: even_alt_pathI alt_list.intros(1) 
            simp add: path_is_target'_only)
    next
      case True
      have path_to_target': "path (quot_graph P E - {{u}}) (butlast p')"
      proof(cases p' rule: list_cases4, goal_cases)
        case (4 x y z xs)
        have butlast_p':"butlast p' @ [last p'] = p'"
          using 4 by simp
        hence "set (edges_of_path (butlast p')) \<subseteq> insert ({target', u'}) (quotG E)"
          using edges_of_path_append_subset_2[of "butlast p'" "[last p']"]
            edges_of_path_append_subset_2 p'(1)
            path_edges_subset [of "insert ({target', u'}) (quotG E)" p']
          unfolding quot'_Es_are 
          by simp
        moreover have "{target', u'} \<notin> set (edges_of_path (butlast p'))" 
          using edge_not_in_edges_in_path[of target' "butlast p'" u']  butlast_p' 
            distinct_append[of "butlast p'" "[last p']"] p'(1,2) 
          by simp
        ultimately have edges_in_old_quot: 
          "set (edges_of_path (butlast p')) \<subseteq> quot_graph P E - {{u}}"
          by auto
        show ?case
        proof(rule path_mono[of "quot'.quotG ({{target, u'}} \<union> E)"],
            rule path_pref[of _ _ "[last p']"], goal_cases)
          case 1
          then show ?case 
            using 4  p'(1)  edges_in_old_quot  
            by auto
        next
          case 2
          then show ?case 
            using 4  p'(1)  edges_in_old_quot  
            by auto
        next
          case 3
          then show ?case 
            using 4  p'(1)  edges_in_old_quot  
            by auto
        qed
      next
        case (3 x y )
        thus ?case 
          using True x_is_target' xp'' by force
      qed auto
      moreover have "alt_path (quot_graph P M - {{u}}) (butlast p')"
      proof-
        have "alt_path (quot_graph P M - {{u}}) p'"
          using p'(1)by(unfold matching_augmenting_path_def quot'_M_are) simp
        thus ?thesis
          using butlast_p' alt_list_split_last_off[of _ _ _ "{x, u'}"]
          by (simp add: butlast_append xp'' edges_of_path_snoc_2)
      qed
      moreover have "hd (butlast p') = hd p'" 
        unfolding xp'' by(cases p'') auto
      moreover have "last (butlast p') = target'"
        by (simp add: butlast_append x_is_target' xp'')
      moreover have "odd (length (butlast p'))"
        using aug_paths_are_even p'(1) xp'' by fastforce
      moreover have "hd p' \<notin> Vs (quot_graph P M - {{u}})"
        using matching_augmenting_path_def p'(1) quot'_M_are by auto
      moreover have "distinct (butlast p')"
        by (simp add: distinct_butlast p'(1))
      ultimately show ?thesis
        by(auto intro!: even_alt_pathI)
    qed
    thus ?thesis by auto
  qed
qed

theorem even_vertex_blossom_contraction:
  assumes  "blossom E M stem C" "even_vert E M x" "x \<in> Vs E"
    "max_card_matching E M"
    "s = (Vs E) - set C" "u \<notin>  Vs E"  "u' \<notin> Vs E" "u' \<noteq> u" 
  shows "even_vert (quotG E) (quotG M) (P x)"
proof-
  obtain start p where start_p: "even_alt_path E M start p x"
    using assms(2) by(auto simp add: even_vert_even_alt_path)
  have iffy:"P x = (if x \<notin> Vs E then x else if x \<notin> s then u else x)"
    using assms(3) by auto
  have "x \<noteq> u"
    using assms(3,6) by auto
  then obtain start' p' where
    "even_alt_path (quotG E) (quotG M) start' p' (P x)"
    using reachbale_by_even_alt_path_contraction[OF assms(1) start_p(1) assms(4,5,6,7,8)iffy ]
    by auto
  thus ?thesis
    by(auto intro!: exI simp add: even_vert_even_alt_path)
qed

theorem even_vertices_blossom_contraction:
  assumes  "blossom E M stem C" 
    "max_card_matching E M"
    "s = (Vs E) - set C" "u \<notin>  Vs E"  "u' \<notin> Vs E" "u' \<noteq> u" 
  shows "even_verts (quotG E) (quotG M) \<supseteq> P ` (even_verts E M \<inter> Vs E) "
proof-
  have "even_vert (quotG E) (quotG M) x" 
    if "x \<in> s" "x \<in> Vs E" "even_vert E M x" for x
  proof-
    note again_even =
      even_vertex_blossom_contraction[OF assms(1) _ _ assms(2,3,4,5,6), of x, 
        simplified if_P[OF that(1)]]
    show ?thesis 
      using that assms(3) 
      by (intro again_even)
  qed
  moreover have "even_vert (quotG E) (quotG M) u" if
    "x \<in> Vs E" "x \<notin> s" "even_vert E M x" for x
  proof-
    note again_even =
      even_vertex_blossom_contraction[OF assms(1) _ _ assms(2,3,4,5,6), of x,
        simplified if_not_P[OF that(2)]]
    show ?thesis 
      using that assms
      by (intro again_even) auto
  qed
  ultimately show ?thesis
    by(auto simp add: even_verts_def)
qed

text \<open>We now prove the reverse direction by the same argument:
      If a vertex (or its representative) is even after contraction,
      if is even before, too.\<close>

theorem reachbale_by_even_alt_path_contraction_reverse:
  assumes match_blossom: "blossom E M stem C" and
    alt_path:  "even_alt_path (quotG E) (quotG M) start p target'" and 
    matching:  "max_card_matching E M" and
    quot: "s = (Vs E) - set C" "u \<notin>  Vs E"  "u' \<notin> Vs E" "u' \<noteq> u" 
    "target' = (if target \<notin> Vs E then target else 
              if target \<notin> s then u else target)" "target \<noteq> u"
  shows "\<exists>p' start'. even_alt_path E M start' p' target"
proof-
  have p_props:
    "path (quotG E) p \<or> length p = 1" "alt_path (quotG M) p"
    "hd p = start" "last p = target'" "odd (length p)" "start \<notin> Vs (quotG M)" "distinct p"
    "p\<noteq>[]"
    using alt_path by(auto elim!: even_alt_pathE)
  have matching_contracted: "max_card_matching (quotG E) (quotG M)"
    using quot(1,2) match_blossom matching
    by(subst max_card_matching_equiv_blossom_contraction) 
      (auto dest: max_card_matchingD)
  note matching_props = max_card_matchingD[OF matching]

  show ?thesis
  proof(cases "target \<in> Vs E")
    case False
    thus ?thesis
      using Vs_subset matching_props
      by(auto intro!: exI[of _ "[target]"] exI[of _ "target"] even_alt_pathI alt_list.intros(1))
  next
    case True
    note true = this
    show ?thesis
    proof(cases "target \<in> set C")
      case True
      then show ?thesis
        using match_blossom
        by(intro blossom_verts_even_alt_path) auto

    next
      case False
      note false = this
      have p_props:
        "path (quotG E) p" "alt_path (quotG M) p"
        "hd p = start" "last p = target'" "odd (length p)" "start \<notin> Vs (quotG M)" "distinct p"
        "p\<noteq>[]"
        using p_props True false quot(1,5) quot_Vs_in_s
        by(all \<open>cases p\<close>) auto
      have M_props: "M \<subseteq> E" "matching M" "\<And> M'. \<lbrakk>M' \<subseteq> E;matching M'\<rbrakk>\<Longrightarrow> card M' \<le> card M"
        "finite M"
        using matching[simplified max_card_matching_def] finite_E finite_subset by auto
      note target_in_E = True
      have target'_def: "target' = (if target \<notin> s then u else target)" 
        using quot(5) True by auto
      hence target_not_u': " target \<noteq> u'"
        using target'_def  quot(3) target_in_E by blast
      have u'_not_in_M: "u' \<notin> Vs M" 
        using M_props(1) Vs_subset quot(3) by blast
      have P_target: "P target = target'" 
        unfolding target'_def by auto
      have interpret_helpers: "dblton_graph ({{target, u'}} \<union> E)" 
        "finite (Vs ({{target, u'}} \<union> E))"
        using  graph_invar_insert[OF target_not_u' graph]
        by auto
      have quot'_axioms: "quot_axioms ({{target, u'}} \<union> E) (insert u' s) u"
        using quot(3,4) good_quot_map(2) target_not_u'
        by (intro quot_axioms.intro)
          (auto simp add: good_quot_map(1) in_Vs_insert target_in_E vs_insert)
      interpret quot': quot sel "insert {target, u'} E" "insert u' s" u
        using quot'_axioms interpret_helpers 
        by(intro quot.intro pre_quot.intro graph_abs.intro
            interpret_helpers  choose_axioms| simp )+
      have new_blossom: "blossom ({{target, u'}} \<union> E) M stem C"
        using match_blossom path_subset[of E "stem@C" "{{target, u'}} \<union> E"] 
        by auto
      have longer_path: "path ({{target', u'}} \<union> quotG E) (p @ [u'])" 
        using p_props(4) 
        by(auto intro!: path_append path_subset[OF p_props(1)] edges_are_Vs_2)
      have new_edge_not_in_E: "{last p, u'} \<notin> E" "{last p, u'} \<notin> M"
        using quot(3) M_props(1) by (auto simp add:  vs_member')
      have new_edge_not_in_quotE: "{last p, u'} \<notin> quotG E" "{last p, u'} \<notin> quotG M" 
        using neq_u_notin_quotG quot(1,3,4) edges_are_Vs_2 in_quotG_neq_u  by blast+
      have u'_not_in_quot:"u' \<notin> Vs (quot_graph P M - {{u}})"
        using in_quotG_neq_u quot(1,3,4) by blast
      have longer_match_path: "matching_augmenting_path (quotG M) (p @ [u'])"
        using  p_props(2,3,5,6,8)  u'_not_in_quot
        by(auto intro!:  matching_augmenting_pathI alt_list_append_3  alt_list_singleton
            simp add: Suc_le_eq p_props(8) edges_of_path_append_3 edges_of_path_length')
      have u'_not_in_p: "u' \<notin> set p"
        using mem_path_Vs neq_u_notin_quotG p_props(1) quot(1,3,4) by fastforce
      have new_aug_path: "graph_augmenting_path ({{target', u'}} \<union> quotG E) (quotG M) (p @ [u'])"
        using longer_path  p_props(1) quot(3) u'_not_in_p
        by (auto  simp add: p_props(7) longer_match_path)
      have new_untouched_are: "{u'} \<union> s = Vs ({{target, u'}} \<union> E) - set C"
        using match_blossom mem_path_Vs' path_suff quot(3) target_in_E quot(1) 
        by (auto simp add: vs_insert)
      have u_not_in_new_Vs: "u \<notin> Vs ({{target, u'}} \<union> E)"
        using  in_Vs_insertE[of u] quot(2,4) target_in_E 
        by auto
      have quot'_Es_are:"(quot'.quotG ({{target, u'}} \<union> E)) = insert ({target', u'}) (quotG E)"
      proof(rule, all \<open>rule\<close>, goal_cases)
        case (1 e)
        then obtain e' where e': "e' \<in> insert {target, u'} E" "quot'.P ` e' = e" "e' \<noteq> {u}"
          by(auto simp add: quot_graph_def)
        show ?case
        proof(cases "e' = {target, u'}")
          case True
          hence "e = {target', u'}" 
            using e'(2) target'_def target_not_u' by force
          then show ?thesis by simp
        next
          case False
          hence e'_in_E:"e' \<in> E" 
            using e'(1) by auto
          moreover have "u' \<notin> e'" 
            using calculation quot(3) by auto
          ultimately have same_P:"quot'.P ` e' = P ` e'"
            using False e'(2) by auto
          have "e \<in> quotG E"
            using e'_in_E e'(2,3) 1 same_P 
            by (auto intro!:  bexI[of _ e'] simp add: quot_graph_def)
          thus ?thesis by simp
        qed
      next
        case (2 e)
        show ?case
        proof(cases "e = {target', u'}")
          case True
          hence e_not_u:"e \<noteq> {u}"
            by (simp add: quot(4))
          moreover have "quot'.P ` {target, u'} = e" 
            using True   P_target target_not_u' by auto
          ultimately show ?thesis 
            by(auto simp add: quot_graph_def)
        next
          case False
          then obtain e' where "e' \<in> E" "P ` e' = e" "e \<noteq> {u}"
            using 2 by(auto simp add: quot_graph_def)
          moreover have "quot'.P ` e' = e" 
            using calculation(1,2)  
            by (auto intro: not_in_VsE[OF quot(3)])
          ultimately have "e \<in> quot_graph quot'.P ({{target, u'}} \<union> E)"
            unfolding quot_graph_def by blast
          thus ?thesis
            using \<open>e \<noteq> {u}\<close> by blast
        qed
      qed
      have M_edges_P_same:"e \<in> M \<Longrightarrow> quot'.P ` e = P ` e" for e
        using u'_not_in_M by auto
      have quot'_M_are:"quot'.quotG M = quotG M"
        by(intro arg_cong[of _ _ "\<lambda> x. x - {{u}}"]  quot_graph_cong M_edges_P_same)
      have new_Vs_superset: "Vs (quot'.quotG ({{target, u'}} \<union> E)) 
          \<supseteq> insert u' (Vs (quotG E))" 
        unfolding quot'_Es_are
        by (simp add: subset_insertI vs_insert)
      have new_untouched_are': "insert u' s = Vs (insert {target, u'} E) - set C"
        using new_untouched_are by auto
      have path_in_old:
        "graph_augmenting_path (insert {target, u'} E) M (quot'.refine C M (p @ [u']))"
        using new_blossom new_aug_path quot'_Es_are quot'_M_are new_untouched_are'
        by(intro quot'.refine_works[of stem C M "p@[u']"])
          (simp_all add: matching_props subset_insertI2)
      hence refined_edges_in:
        "set (edges_of_path (quot'.refine C M (p @ [u']))) \<subseteq> (insert {target, u'} E)"
        by (simp add: path_edges_subset matching_augmenting_path_def)
      have last_is_or_hd_is: 
        "last (quot'.refine C M (p @ [u'])) = u' \<or> hd (quot'.refine C M (p @ [u'])) = u'"
      proof(cases "u \<in> set (p@[u'])")
        case True
        then show ?thesis
          using quot(4) 
          by (intro quot'.last_not_u_refine)(auto simp add: p_props(7) u'_not_in_p)
      qed(auto simp add: quot'.refine_def)
      have length: "length (quot'.refine C M (p @ [u'])) \<ge> 2" 
        using path_in_old by (auto elim!: matching_augmenting_pathE)
      have target_u'_not_in_E:"{target, u'} \<notin> E" 
        using quot(3) vs_member' by fastforce
      hence x_new_then_u':"\<lbrakk>x \<in> Vs (insert {target, u'} E); x \<notin> Vs E\<rbrakk> \<Longrightarrow> x = u'" for x
        using true by (auto simp add: vs_member)

      show ?thesis proof(cases rule: disjE[OF last_is_or_hd_is])
        case 1
        note One = this
        hence lst_edge_is:"last (edges_of_path (quot'.refine C M (p @ [u']))) =
         {last (butlast (quot'.refine C M (p @ [u']))), u'}"
          by(auto simp add: last_edge_is[OF  length])
        hence last_edge_in:"{last (butlast (quot'.refine C M (p @ [u']))), u'} 
                       \<in>  (insert {target, u'} E)"
          using last_edge_in_edges[OF length] "1" refined_edges_in by auto
        hence penultimate_is:"last (butlast (quot'.refine C M (p @ [u']))) = target" 
          using quot(3) by(auto simp add: vs_member' doubleton_eq_iff)
        then show ?thesis 
        proof(intro exI[of _ "butlast (quot'.refine C M (p @ [u']))"],
            intro exI[of _ "hd (quot'.refine C M (p @ [u']))"], goal_cases)
          case 1
          note one = this
          then show ?case 
          proof(intro even_alt_pathI, goal_cases)
            case 1
            then show ?case 
            proof(cases "length (quot'.refine C M (p @ [u'])) = 2")
              case True
              then show ?thesis 
                by simp
            next
              case False
              have "path (insert {target, u'} E) (butlast (quot'.refine C M (p @ [u'])))"
                using path_in_old append_butlast_last_id[of "quot'.refine C M (p @ [u'])"]
                  path_pref[of _ "butlast (quot'.refine C M (p @ [u']))"
                    "[last (quot'.refine C M (p @ [u']))]"]
                by fastforce
              moreover have "2 \<le> length (butlast (quot'.refine C M (p @ [u'])))"
                using length False by auto
              moreover have "set (edges_of_path (butlast (quot'.refine C M (p @ [u'])))) \<subseteq> E"
              proof(rule ccontr, goal_cases)
                case 1
                hence "{target, u'} \<in> set (edges_of_path (butlast (quot'.refine C M (p @ [u']))))"
                  using calculation(1) path_edges_subset by fastforce
                hence "u' \<in> set (butlast (quot'.refine C M (p @ [u'])))"
                  using edge_not_in_edges_in_path by force
                hence "\<not> distinct (quot'.refine C M (p @ [u']))"
                  using One  target_not_u' penultimate_is 
                    append_butlast_last_id[of "quot'.refine C M (p @ [u'])"]
                    not_distinct_conv_prefix[of
                      "butlast (quot'.refine C M (p @ [u'])) @ [last
                                     (quot'.refine C M (p @ [u']))]"]
                  by force
                then show ?case 
                  using path_in_old by auto
              qed
              ultimately have "path E (butlast (quot'.refine C M (p @ [u'])))"
                by(intro path_mono[of "insert {target, u'} E" "butlast (quot'.refine C M (p @ [u']))" E])
                  auto
              then show ?thesis 
                by simp
            qed
          next
            case 2
            thus ?case
              using path_in_old 
              by (auto intro!: alt_path_split_off_last simp add: matching_augmenting_path_def)
          next
            case 3
            thus ?case
              using length
              by(cases "(quot'.refine C M (p @ [u']))" rule: list_cases3) auto
          next
            case 4
            thus ?case
              by simp
          next
            case 5
            thus ?case
              using length path_in_old  aug_paths_are_even
              by auto
          next
            case 6
            thus ?case
              using path_in_old
              by (auto simp add: matching_augmenting_path_def)
          next
            case 7
            thus ?case
              using path_in_old distinct_butlast by blast
          qed
        qed
      next
        case 2
        note Two = this
        hence "hd (edges_of_path (quot'.refine C M (p @ [u']))) =
         {u', hd (tl (quot'.refine C M (p @ [u'])))}"
          "{u', hd (tl (quot'.refine C M (p @ [u'])))} \<in>  (insert {target, u'} E)"
          using length refined_edges_in
          by(all \<open>cases "quot'.refine C M (p @ [u'])" rule: list_cases3\<close>) auto
        hence "hd (tl (quot'.refine C M (p @ [u']))) = target" 
          using quot(3) by(auto simp add: vs_member doubleton_eq_iff)
        hence second_is:"hd (tl (quot'.refine C M (p @ [u']))) = target" 
          using quot(3) by(auto simp add: vs_member' doubleton_eq_iff)
        then show ?thesis 
        proof(intro exI[of _ "rev (tl (quot'.refine C M (p @ [u'])))"],
            intro exI[of _ "last (quot'.refine C M (p @ [u']))"], goal_cases)
          case 1
          note one = this
          then show ?case 
          proof(intro even_alt_pathI, goal_cases)
            case 1
            then show ?case 
            proof(cases "length (quot'.refine C M (p @ [u'])) = 2")
              case True
              then show ?thesis 
                by simp
            next
              case False
              have "path (insert {target, u'} E) (tl (quot'.refine C M (p @ [u'])))"
                by (simp add: path_in_old tl_path_is_path)
              moreover have "2 \<le> length (tl (quot'.refine C M (p @ [u'])))"
                using length False by auto
              moreover have "set (edges_of_path (tl (quot'.refine C M (p @ [u'])))) \<subseteq> E"
              proof(rule ccontr, goal_cases)
                case 1
                hence "{target, u'} \<in> set (edges_of_path (tl (quot'.refine C M (p @ [u']))))"
                  using calculation(1) path_edges_subset by fastforce
                hence "u' \<in> set (tl (quot'.refine C M (p @ [u'])))"
                  using edge_not_in_edges_in_path by force
                hence "\<not> distinct (quot'.refine C M (p @ [u']))"
                  using Two  by(cases "quot'.refine C M (p @ [u'])") auto
                then show ?case 
                  using path_in_old by auto
              qed
              ultimately have "path E (rev (tl (quot'.refine C M (p @ [u']))))"
                unfolding rev_path_is_path_iff
                by(intro path_mono[of "insert {target, u'} E" "tl (quot'.refine C M (p @ [u']))" E])
                  auto
              then show ?thesis 
                by simp
            qed
          next
            case 2
            have "graph_augmenting_path (insert {target, u'} E) M (rev (quot'.refine C M (p @ [u'])))"
              using path_in_old graph_augmenting_path_rev_iff  by auto
            thus ?case
              unfolding butlast_rev[symmetric]
              by(intro alt_path_split_off_last)
                (auto simp add: matching_augmenting_path_def)
          next
            case 3
            thus ?case
              using length
              by(cases "(quot'.refine C M (p @ [u']))" rule: list_cases_both_sides) auto
          next
            case 4
            thus ?case 
              by (auto simp add: last_rev)
          next
            case 5
            thus ?case
              using length path_in_old  aug_paths_are_even
              by auto
          next
            case 6
            thus ?case
              using path_in_old
              by (auto simp add: matching_augmenting_path_def)
          next
            case 7
            thus ?case
              using path_in_old
              by (auto intro!: distinct_tl)
          qed
        qed
      qed
    qed
  qed
qed

theorem even_vertex_blossom_contraction_reverse:
  assumes  "blossom E M stem C"  "even_vert (quotG E) (quotG M) (P x)" "x \<in> Vs E"
    "max_card_matching E M"
    "s = (Vs E) - set C" "u \<notin> Vs E"  "u' \<notin> Vs E" "u' \<noteq> u" 
  shows "even_vert E M x"
proof-
  obtain start p where start_p: "even_alt_path (quotG E) (quotG M) start p (P x)"
    using assms(2) by(auto simp add: even_vert_even_alt_path)
  have iffy:"P x = (if x \<notin> Vs E then x else if x \<notin> s then u else x)"
    using assms(3) by auto
  have "x \<noteq> u"
    using assms(3,6) by auto
  then obtain start' p' where
    "even_alt_path E M start' p' x"
    using reachbale_by_even_alt_path_contraction_reverse[OF assms(1) start_p(1) assms(4,5,6,7,8)iffy ]
    by auto
  thus ?thesis
    by(auto intro!: exI simp add: even_vert_even_alt_path)
qed
end

end