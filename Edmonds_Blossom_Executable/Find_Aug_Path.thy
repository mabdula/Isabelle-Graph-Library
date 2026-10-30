theory Find_Aug_Path
  imports Graph_Matching_Specs Graph_Quotient_Lifting Blossom_Prefixes
begin

provenance ai

section \<open>Searching for an augmenting path by shrinking blossoms\<close>

text \<open>The search calls a procedure that returns an augmenting path, a blossom, or nothing. When
  it returns a blossom, the cycle of the blossom is contracted to a vertex of the universe that
  is not a vertex of the current graph, in the graph and in the matching, and the search is
  repeated on the contracted graph. Such a vertex exists as long as the vertices of the graph are
  a strict subset of the universe, which a contraction preserves: it replaces the at least two
  vertices of the cycle by one vertex. The contractions are
  recorded on a stack. When an augmenting path of the contracted graph is found, it is lifted
  through the recorded contractions, from the last one to the first, to an augmenting path of the
  input graph. A contraction preserves the existence of augmenting paths, so if the procedure
  returns nothing, the input graph has no augmenting path.

  A path is lifted through one contraction by the function @{const refine} of the theory of
  graph quotients, whose correctness is @{thm [source] quot_lift.refine_works}.\<close>

subsection \<open>Contracting an edge list\<close>

definition \<^marker>\<open>provenance ai_human\<close> "quotient_vertex C u v = (if v \<in> set C then u else v)"

definition \<^marker>\<open>provenance ai_human\<close> "quotient_edges C u es =
  filter (\<lambda>(a, b). a \<noteq> b) (map (\<lambda>(a, b). (quotient_vertex C u a, quotient_vertex C u b)) es)"

lemmas [code] = quotient_vertex_def quotient_edges_def

lemma set_quotient_edges:
  "set (quotient_edges C u es) =
     {(quotient_vertex C u a, quotient_vertex C u b) | a b.
        (a, b) \<in> set es \<and> quotient_vertex C u a \<noteq> quotient_vertex C u b}"
  by (auto simp: quotient_edges_def)

lemma quotient_edges_sym:
  "\<lbrakk>\<And>a b. (a, b) \<in> set es \<Longrightarrow> (b, a) \<in> set es;
    (a, b) \<in> set (quotient_edges C u es)\<rbrakk> \<Longrightarrow> (b, a) \<in> set (quotient_edges C u es)"
  by (fastforce simp: set_quotient_edges)

lemma quotient_edges_irrefl: "(a, a) \<notin> set (quotient_edges C u es)"
  by (auto simp: set_quotient_edges)

lemma dVs_quotient_edges:
  "dVs (set (quotient_edges C u es)) \<subseteq> insert u (dVs (set es) - set C)"
proof
  fix x
  assume "x \<in> dVs (set (quotient_edges C u es))"
  then obtain a b where "(a, b) \<in> set es" "quotient_vertex C u a \<noteq> quotient_vertex C u b"
    "x = quotient_vertex C u a \<or> x = quotient_vertex C u b"
    by (auto simp: dVs_eq set_quotient_edges)
  thus "x \<in> insert u (dVs (set es) - set C)"
    by (force simp: quotient_vertex_def dVs_eq split: if_splits intro: rev_image_eqI)
qed

lemma quotient_edges_quot_graph:
  assumes "set es = D" "\<And>a b. (a, b) \<in> D \<Longrightarrow> (b, a) \<in> D" "\<And>a. (a, a) \<notin> D"
          "\<And>v. v \<in> dVs D \<Longrightarrow> v \<in> s \<longleftrightarrow> v \<notin> set C" "u \<notin> s"
  shows "{{a, b} | a b. (a, b) \<in> set (quotient_edges C u es)} =
           quot_graph (\<lambda>v. if v \<in> s then v else u) {{a, b} | a b. (a, b) \<in> D} - {{u}}"
    (is "?L = ?R")
proof-
  define P where "P = (\<lambda>v. if v \<in> s then v else u)"
  have endpoints: "P a = quotient_vertex C u a \<and> P b = quotient_vertex C u b"
    if "(a, b) \<in> D" for a b
    using assms(4)[OF Pair_Graph.dVsI(1)[OF that]]
      assms(4)[OF Pair_Graph.dVsI(2)[OF that]]
    by (simp add: P_def quotient_vertex_def)
  have nonloop: "{P a, P b} \<noteq> {u} \<longleftrightarrow> P a \<noteq> P b"
    if "(a, b) \<in> D" for a b
    using assms(3)[of a] that by (auto simp: P_def split: if_splits)
  have "?L = quot_graph P {{a, b} | a b. (a, b) \<in> D} - {{u}}"
  proof (rule equalityI; rule subsetI)
    fix e
    assume "e \<in> ?L"
    then obtain a b where edge: "e = {quotient_vertex C u a, quotient_vertex C u b}"
      "(a, b) \<in> D" "quotient_vertex C u a \<noteq> quotient_vertex C u b"
      using assms(1) by (auto simp: set_quotient_edges)
    have source: "{a, b} \<in> {{a, b} | a b. (a, b) \<in> D}"
      using edge(2) by blast
    have "e \<in> quot_graph P {{a, b} | a b. (a, b) \<in> D}"
      using edge_in_graph_in_quot[OF source, of P] endpoints[OF edge(2)] edge(1) by simp
    then show "e \<in> quot_graph P {{a, b} | a b. (a, b) \<in> D} - {{u}}"
      using edge(1,3) by auto
  next
    fix e
    assume "e \<in> quot_graph P {{a, b} | a b. (a, b) \<in> D} - {{u}}"
    then obtain a b where edge: "e = P ` {a, b}" "(a, b) \<in> D" "e \<noteq> {u}"
      by (auto simp: quot_graph_def)
    have neq: "P a \<noteq> P b"
      using nonloop[OF edge(2)] edge(1,3) by simp
    have pair: "(quotient_vertex C u a, quotient_vertex C u b) \<in> set (quotient_edges C u es)"
      unfolding set_quotient_edges
      by (intro CollectI exI[of _ a] exI[of _ b])
         (use edge(2) neq endpoints[OF edge(2)] assms(1) in auto)
    show "e \<in> ?L"
      by (intro CollectI exI[of _ "quotient_vertex C u a"] exI[of _ "quotient_vertex C u b"])
         (use edge(1) endpoints[OF edge(2)] pair in auto)
  qed
  then show ?thesis by (simp only: P_def)
qed

subsection \<open>The program state\<close>

record ('adjmap, 'mate, 'v) Find_Aug_Path_state =
  search_graph :: 'adjmap
  search_vertices :: "'v list"
  search_matching :: 'mate
  contractions :: "('adjmap \<times> 'mate \<times> 'v list \<times> 'v) list"
  search_result :: "'v match_blossom_res option"

subsection \<open>Setup for automation\<close>

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_props_elims
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros

subsection \<open>The loop\<close>

locale Find_Aug_Path = Graph_Matching_Specs where lookup = lookup and mate_empty = mate_empty
  for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" and mate_empty :: 'mate +
  fixes G :: 'adjmap and vs :: "'v list" and M :: 'mate
    and blos_search :: "'adjmap \<Rightarrow> 'v list \<Rightarrow> 'mate \<Rightarrow> 'v match_blossom_res option"
    and create_vert :: "'v list \<Rightarrow> 'v"
  assumes blos_search:
    "\<And>G' vs' M' p. \<lbrakk>graph_input G' vs'; matching_invar G' M'; blos_search G' vs' M' = Some (Path p)\<rbrakk>
       \<Longrightarrow> graph_augmenting_path (ugraph_abs G') (matching_abs M') p"
    "\<And>G' vs' M' stem C. \<lbrakk>graph_input G' vs'; matching_invar G' M';
                         blos_search G' vs' M' = Some (Blossom stem C)\<rbrakk>
       \<Longrightarrow> blossom (ugraph_abs G') (matching_abs M') stem C"
    "\<And>G' vs' M'. \<lbrakk>graph_input G' vs'; matching_invar G' M';
                  \<exists>p. graph_augmenting_path (ugraph_abs G') (matching_abs M') p\<rbrakk>
       \<Longrightarrow> blos_search G' vs' M' \<noteq> None"
  and create_vert: "\<And>vs'. set vs' \<subset> K \<Longrightarrow> create_vert vs' \<notin> set vs'"
  and create_vert_in_univ: "\<And>vs'. set vs' \<subset> K \<Longrightarrow> create_vert vs' \<in> K"
begin

definition "Find_Aug_Path_axiom \<longleftrightarrow> graph_input G vs \<and> matching_invar G M \<and> set vs \<subset> K"

subsubsection \<open>Contraction\<close>

definition \<^marker>\<open>provenance ai_human\<close> "contract_vertices vs' C u = u # filter (\<lambda>v. v \<notin> set C) vs'"

definition \<^marker>\<open>provenance ai_human\<close> "contract_graph G' vs' C u = Graph.from_list (quotient_edges C u (adjacency_edges G' vs'))"

definition \<^marker>\<open>provenance ai_human\<close> "contract_matching M' C u =
  mate_contract M' (butlast C) u"


subsubsection \<open>Lifting\<close>

fun \<^marker>\<open>provenance ai_human\<close> lift_path where
  "lift_path [] p = p"
| "lift_path ((E, N, C, u) # cs) p =
     lift_path cs (refine (\<lambda>v. isin (Graph.neighbourhood E v)) (mate_lookup N) u C p)"

lemmas [code] = contract_vertices_def contract_graph_def contract_matching_def lift_path.simps

subsubsection \<open>One contraction\<close>

context
  fixes E N C u vs' stem
  assumes contraction:
    "graph_input E vs'" "matching_invar E N" "blossom (ugraph_abs E) (matching_abs N) stem C"
    "u \<notin> set vs' - set C" "u \<in> K"
begin

lemma contraction_facts:
  "graph_invar (ugraph_abs E)" "set C \<subseteq> Vs (ugraph_abs E)" "C \<noteq> []" "hd C = last C"
  "2 \<le> card (set C)" "u \<notin> Vs (ugraph_abs E) - set C" "matching_invar_abs (ugraph_abs E) N"
  "matching (matching_abs N)" "matching_abs N \<subseteq> ugraph_abs E" "finite (matching_abs N)"
  "u \<in> K"
proof-
  show "graph_invar (ugraph_abs E)"
    by (rule ugraph_abs_graph_invar[OF contraction(1)])
  show "set C \<subseteq> Vs (ugraph_abs E)"
    by (rule subset_path_Vs[OF path_suff[OF blossomD(1)[OF contraction(3)]]])
  show "C \<noteq> []" "hd C = last C" "2 \<le> card (set C)"
    using odd_cycle_nempty[OF match_blossomD(3)[OF blossomD(2)[OF contraction(3)]]]
      odd_cycleD(3)[OF match_blossomD(3)[OF blossomD(2)[OF contraction(3)]]]
      blossom_cycle_longer_2[OF blossomD(2)[OF contraction(3)]]
    by simp_all
  show "u \<notin> Vs (ugraph_abs E) - set C"
    using contraction(4) Vs_ugraph_abs_subset_vs[OF contraction(1)]
    by blast
  show "u \<in> K"
    by (rule contraction(5))
  show "matching_invar_abs (ugraph_abs E) N"
    using contraction(2)
    by (simp add: matching_invar_def)
  show "matching (matching_abs N)" "matching_abs N \<subseteq> ugraph_abs E" "finite (matching_abs N)"
    using matching_invar_props[OF contraction(2)] contraction(1)
    by simp_all
qed

lemma quot_here: "quot (ugraph_abs E) (Vs (ugraph_abs E) - set C) u"
  apply unfold_locales
  using contraction_facts(1,2,3,6)
  by (auto simp: neq_Nil_conv)

interpretation Q: quot "ugraph_abs E" "Vs (ugraph_abs E) - set C" u
  by (rule quot_here)

lemma contract_graph_abs:
  "ugraph_abs (contract_graph E vs' C u) = Q.quotG (ugraph_abs E)"
proof-
  have e: "{{a, b} | a b. (a, b) \<in> Graph.digraph_abs E} = ugraph_abs E"
    by (simp add: ugraph_abs_def)
  have cond: "v \<in> Vs (ugraph_abs E) - set C \<longleftrightarrow> v \<notin> set C"
    if "v \<in> dVs (Graph.digraph_abs E)" for v
    using that Vs_ugraph_abs
    by simp
  have u_nin: "u \<notin> Vs (ugraph_abs E) - set C"
    using contraction_facts(6)
    by simp
  have "{{a, b} | a b. (a, b) \<in> set (quotient_edges C u (adjacency_edges E vs'))} =
        quot_graph (\<lambda>v. if v \<in> Vs (ugraph_abs E) - set C then v else u)
          {{a, b} | a b. (a, b) \<in> Graph.digraph_abs E} - {{u}}"
    by (rule quotient_edges_quot_graph[OF adjacency_edges[OF contraction(1)]
                                          graph_inputD(4,5)[OF contraction(1)] cond u_nin])
  thus ?thesis
    unfolding e
    by (simp add: contract_graph_def ugraph_abs_from_list)
qed

lemma contract_graph_input:
  "graph_input (contract_graph E vs' C u) (contract_vertices vs' C u)"
  unfolding contract_graph_def
proof(rule from_list_graph_input)
  have sym: "\<And>a b. (a, b) \<in> set (adjacency_edges E vs') \<Longrightarrow> (b, a) \<in> set (adjacency_edges E vs')"
    using graph_inputD(4)[OF contraction(1)]
    by (simp add: adjacency_edges[OF contraction(1)])
  show "\<And>a b. (a, b) \<in> set (quotient_edges C u (adjacency_edges E vs')) \<Longrightarrow>
              (b, a) \<in> set (quotient_edges C u (adjacency_edges E vs'))"
    using quotient_edges_sym[OF sym]
    by blast
  show "\<And>a. (a, a) \<notin> set (quotient_edges C u (adjacency_edges E vs'))"
    by (rule quotient_edges_irrefl)
  have "dVs (set (adjacency_edges E vs')) \<subseteq> set vs'"
    using adjacency_edges[OF contraction(1)] graph_inputD(6)[OF contraction(1)]
    by simp
  thus "dVs (set (quotient_edges C u (adjacency_edges E vs'))) \<subseteq> set (contract_vertices vs' C u)"
    using dVs_quotient_edges[of C u "adjacency_edges E vs'"]
    by (auto simp: contract_vertices_def)
  show "set (contract_vertices vs' C u) \<subseteq> K"
    using graph_inputD(7)[OF contraction(1)] contraction_facts(11)
    by (auto simp: contract_vertices_def)
qed

text \<open>A contraction replaces the at least two vertices of the cycle by one vertex, so a vertex
  list that is a strict subset of the universe stays one.\<close>

lemma contract_vertices_strict:
  assumes "set vs' \<subset> K"
  shows "set (contract_vertices vs' C u) \<subset> K"
proof-
  have eq: "set (contract_vertices vs' C u) = Set.insert u (set vs' - set C)"
    by (auto simp: contract_vertices_def)
  have sub: "set (contract_vertices vs' C u) \<subseteq> K"
    using assms contraction(5)
    by (auto simp: contract_vertices_def)
  have C: "set C \<subseteq> set vs'"
    using contraction_facts(2) Vs_ugraph_abs_subset_vs[OF contraction(1)]
    by blast
  have "card (Set.insert u (set vs' - set C)) \<le> Suc (card (set vs' - set C))"
    by (simp add: card_insert_if)
  moreover have "card (set vs' - set C) = card (set vs') - card (set C)"
    using C
    by (simp add: card_Diff_subset)
  moreover have "card (set C) \<le> card (set vs')"
    using C
    by (simp add: card_mono)
  ultimately have less: "card (set (contract_vertices vs' C u)) < card (set vs')"
    using contraction_facts(5)
    by (simp add: eq)
  show ?thesis
  proof(rule psubsetI[OF sub], rule notI)
    assume K: "set (contract_vertices vs' C u) = K"
    hence "card (set vs') \<le> card K"
      using assms
      by (metis List.finite_set card_mono psubset_imp_subset)
    thus False
      using K less
      by simp
  qed
qed

lemma contract_matching_abs:
  "matching_abs (contract_matching N C u) = Q.quotG (matching_abs N)"
  and contract_matching_invar:
  "matching_invar (contract_graph E vs' C u) (contract_matching N C u)"
proof-
  have cycle: "odd_cycle C"
    by (rule match_blossomD(3)[OF blossomD(2)[OF contraction(3)]])
  have path: "alt_path (matching_abs N) (butlast C)"
    by (rule alt_path_split_off_last[OF match_blossom_alt_cycle[OF blossomD(2)[OF contraction(3)]]])
  have cycle_props: "set (butlast C) = set C"
    "odd (length (butlast C))" "distinct (butlast C)"
    by (cases C rule: list_cases_hd_and_last;
        insert odd_cycleD[OF cycle] odd_cycle_even_verts[OF cycle]
          match_blossomD(2)[OF blossomD(2)[OF contraction(3)]]; auto)+
  have in_univ: "set (butlast C) \<subseteq> K"
    using cycle_props(1) contraction_facts(2) graph_inputD(7)[OF contraction(1)]
      Vs_ugraph_abs_subset_vs[OF contraction(1)] by blast
  have fresh: "u \<notin> Vs (matching_abs N) - set (butlast C)"
    using contraction_facts(6,9) Vs_subset cycle_props(1) by blast
  let ?contr = "\<lambda>x. if x \<in> set (butlast C) then u else x"
  have quot_eq: "quot_graph ?contr X - {{u}} = Q.quotG X" if "X \<subseteq> ugraph_abs E" for X
  proof (rule arg_cong[where f="\<lambda>A. A - {{u}}"], rule quot_graph_cong)
    fix e
    assume "e \<in> X"
    hence sub: "e \<subseteq> Vs (ugraph_abs E)"
      using that by (auto simp: Vs_def)
    show "?contr ` e = Q.P ` e"
      by (rule image_cong; insert sub cycle_props(1); auto)
  qed
  have precond: "Mate.contract_path_precond (ugraph_abs E) N (butlast C) u ?contr"
    by (rule Mate.contract_path_precondI[
          OF contraction_facts(7) path cycle_props(2,3) fresh refl in_univ contraction_facts(11)])
  show "matching_abs (contract_matching N C u) = Q.quotG (matching_abs N)"
    using Mate.contract(2)[OF precond] quot_eq[OF contraction_facts(9)]
    by (simp add: contract_matching_def)
  show "matching_invar (contract_graph E vs' C u) (contract_matching N C u)"
    using Mate.contract(1)[OF precond] quot_eq[OF subset_refl]
    by (simp add: matching_invar_def contract_graph_abs contract_matching_def)
qed

lemma contract_card_Vs:
  "card (Vs (ugraph_abs (contract_graph E vs' C u))) < card (Vs (ugraph_abs E))"
proof-
  have "Vs (ugraph_abs E) - (Vs (ugraph_abs E) - set C) = set C"
    using contraction_facts(2)
    by blast
  hence "1 < card (Vs (ugraph_abs E) - (Vs (ugraph_abs E) - set C))"
    using contraction_facts(5)
    by simp
  thus ?thesis
    using Q.card_Vs_quotG contraction_facts(1)
    by (simp add: contract_graph_abs)
qed

lemma contract_complete:
  assumes "\<exists>p. graph_augmenting_path (ugraph_abs E) (matching_abs N) p"
  shows "\<exists>p. graph_augmenting_path (ugraph_abs (contract_graph E vs' C u))
                (matching_abs (contract_matching N C u)) p"
proof-
  obtain p where p: "graph_augmenting_path (ugraph_abs E) (matching_abs N) p"
    using assms
    by blast
  have "\<exists>p'. graph_augmenting_path (Q.quotG (ugraph_abs E)) (Q.quotG (matching_abs N)) p'"
    by (rule Q.aug_path_works_in_contraction[OF contraction(3) p contraction_facts(8,9,10) refl
                                              contraction_facts(6)])
  thus ?thesis
    by (simp add: contract_graph_abs contract_matching_abs)
qed

lemma quot_lift_here:
  "quot_lift (ugraph_abs E) (Vs (ugraph_abs E) - set C) u (\<lambda>v. isin (Graph.neighbourhood E v))
     (mate_lookup N) (matching_abs N) C"
proof(intro quot_lift.intro quot_here quot_lift_axioms.intro)
  show "isin (Graph.neighbourhood E v) w \<longleftrightarrow> {v, w} \<in> ugraph_abs E" for v w
    by (simp add: isin_neighbourhood_iff in_ugraph_abs_iff[OF contraction(1)])
  show "mate_lookup N v = Some w \<longleftrightarrow> {v, w} \<in> matching_abs N" for v w
    by (simp add: matching_abs_iff[OF contraction_facts(7)])
  show "matching_abs N \<subseteq> ugraph_abs E"
    by (rule contraction_facts(9))
  show "hd C = last C"
    by (rule contraction_facts(4))
qed simp

lemma refine_correct:
  assumes "graph_augmenting_path (ugraph_abs (contract_graph E vs' C u))
             (matching_abs (contract_matching N C u)) p"
  shows "graph_augmenting_path (ugraph_abs E) (matching_abs N)
           (refine (\<lambda>v. isin (Graph.neighbourhood E v)) (mate_lookup N) u C p)"
proof-
  interpret L: quot_lift "ugraph_abs E" "Vs (ugraph_abs E) - set C" u
                 "\<lambda>v. isin (Graph.neighbourhood E v)" "mate_lookup N" "matching_abs N" C
    by (rule quot_lift_here)
  have "graph_augmenting_path (Q.quotG (ugraph_abs E)) (Q.quotG (matching_abs N)) p"
    using assms
    by (simp add: contract_graph_abs contract_matching_abs)
  thus ?thesis
    by (rule L.refine_works[OF contraction(3) _ contraction_facts(8,9) refl])
qed

end

subsubsection \<open>The loop\<close>

function \<^marker>\<open>provenance ai_human\<close> (domintros) Find_Aug_Path ::
  "('adjmap, 'mate, 'v) Find_Aug_Path_state \<Rightarrow>
   ('adjmap, 'mate, 'v) Find_Aug_Path_state" where
  "Find_Aug_Path state =
     (case search_result state of
        Some (Blossom stem C) \<Rightarrow>
          (let u = create_vert (search_vertices state);
               G' = contract_graph (search_graph state) (search_vertices state) C u;
               vs' = contract_vertices (search_vertices state) C u;
               M' = contract_matching (search_matching state) C u
           in Find_Aug_Path
                (state \<lparr>search_graph := G', search_vertices := vs', search_matching := M',
                        contractions := (search_graph state, search_matching state, C, u)
                                          # contractions state,
                        search_result := blos_search G' vs' M'\<rparr>))
      | _ \<Rightarrow> state)"
  by pat_completeness auto

partial_function \<^marker>\<open>provenance ai_human\<close> (tailrec) Find_Aug_Path_impl ::
  "('adjmap, 'mate, 'v) Find_Aug_Path_state \<Rightarrow>
   ('adjmap, 'mate, 'v) Find_Aug_Path_state" where
  "Find_Aug_Path_impl state =
     (case search_result state of
        Some (Blossom stem C) \<Rightarrow>
          (let u = create_vert (search_vertices state);
               G' = contract_graph (search_graph state) (search_vertices state) C u;
               vs' = contract_vertices (search_vertices state) C u;
               M' = contract_matching (search_matching state) C u
           in Find_Aug_Path_impl
                (state \<lparr>search_graph := G', search_vertices := vs', search_matching := M',
                        contractions := (search_graph state, search_matching state, C, u)
                                          # contractions state,
                        search_result := blos_search G' vs' M'\<rparr>))
      | _ \<Rightarrow> state)"

lemma Find_Aug_Path_impl_same:
  assumes "Find_Aug_Path_dom state"
  shows "Find_Aug_Path_impl state = Find_Aug_Path state"
  apply(induction rule: Find_Aug_Path.pinduct[OF assms])
  apply(subst Find_Aug_Path_impl.simps)
  by (auto simp: Find_Aug_Path.psimps Let_def
          split: option.splits match_blossom_res.splits)

definition \<^marker>\<open>provenance ai_human\<close> "initial_state =
  \<lparr>search_graph = G, search_vertices = vs, search_matching = M, contractions = [],
   search_result = blos_search G vs M\<rparr>"

text \<open>The answer is read off the final state.\<close>

definition \<^marker>\<open>provenance ai_human\<close> "augmenting_path state =
  (case search_result state of
     Some (Path p) \<Rightarrow> Some (lift_path (contractions state) p)
   | _ \<Rightarrow> None)"

definition \<^marker>\<open>provenance ai_human\<close> "Find_Aug_Path_run = augmenting_path (Find_Aug_Path initial_state)"

definition \<^marker>\<open>provenance ai_human\<close> "Find_Aug_Path_run_impl =
  augmenting_path (Find_Aug_Path_impl initial_state)"

lemmas [code] = Find_Aug_Path_impl.simps initial_state_def augmenting_path_def
  Find_Aug_Path_run_impl_def

definition "Find_Aug_Path_call_1_conds state =
  (\<exists>stem C. search_result state = Some (Blossom stem C))"

definition "Find_Aug_Path_upd1 state =
  (case search_result state of
     Some (Blossom stem C) \<Rightarrow>
       (let u = create_vert (search_vertices state);
            G' = contract_graph (search_graph state) (search_vertices state) C u;
            vs' = contract_vertices (search_vertices state) C u;
            M' = contract_matching (search_matching state) C u
        in state \<lparr>search_graph := G', search_vertices := vs', search_matching := M',
                  contractions := (search_graph state, search_matching state, C, u)
                                    # contractions state,
                  search_result := blos_search G' vs' M'\<rparr>)
   | _ \<Rightarrow> state)"

definition "Find_Aug_Path_ret_1_conds state =
  (\<exists>p. search_result state = Some (Path p))"

abbreviation "Find_Aug_Path_ret1 state \<equiv> state"

definition "Find_Aug_Path_ret_2_conds state = (search_result state = None)"

abbreviation "Find_Aug_Path_ret2 state \<equiv> state"

definition "invar_1 state \<longleftrightarrow>
  graph_input (search_graph state) (search_vertices state) \<and>
  matching_invar (search_graph state) (search_matching state) \<and>
  set (search_vertices state) \<subset> K"

definition "invar_search state \<longleftrightarrow>
  search_result state =
    blos_search (search_graph state) (search_vertices state) (search_matching state)"

definition "invar_lift state \<longleftrightarrow>
  (\<forall>p. graph_augmenting_path (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) p
       \<longrightarrow> graph_augmenting_path (ugraph_abs G) (matching_abs M) (lift_path (contractions state) p))"

definition "invar_complete state \<longleftrightarrow>
  ((\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p) \<longrightarrow>
   (\<exists>p. graph_augmenting_path (ugraph_abs (search_graph state))
          (matching_abs (search_matching state)) p))"

definition "call_1_measure state = card (Vs (ugraph_abs (search_graph state)))"

definition "Find_Aug_Path_term_rel' = call_1_measure <*mlex*> {}"

lemma Find_Aug_Path_call_1_conds[call_cond_elims]:
  "Find_Aug_Path_call_1_conds state \<Longrightarrow>
   ((\<exists>stem C. search_result state = Some (Blossom stem C)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Find_Aug_Path_call_1_conds_def)

lemma Find_Aug_Path_call_1_condsI[call_cond_intros]:
  "search_result state = Some (Blossom stem C) \<Longrightarrow> Find_Aug_Path_call_1_conds state"
  by (auto simp: Find_Aug_Path_call_1_conds_def)

lemma Find_Aug_Path_ret_1_conds[call_cond_elims]:
  "Find_Aug_Path_ret_1_conds state \<Longrightarrow>
   ((\<exists>p. search_result state = Some (Path p)) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Find_Aug_Path_ret_1_conds_def)

lemma Find_Aug_Path_ret_1_condsI[call_cond_intros]:
  "search_result state = Some (Path p) \<Longrightarrow> Find_Aug_Path_ret_1_conds state"
  by (auto simp: Find_Aug_Path_ret_1_conds_def)

lemma Find_Aug_Path_ret_2_conds[call_cond_elims]:
  "Find_Aug_Path_ret_2_conds state \<Longrightarrow> (search_result state = None \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: Find_Aug_Path_ret_2_conds_def)

lemma Find_Aug_Path_ret_2_condsI[call_cond_intros]:
  "search_result state = None \<Longrightarrow> Find_Aug_Path_ret_2_conds state"
  by (auto simp: Find_Aug_Path_ret_2_conds_def)

lemma Find_Aug_Path_cases:
  assumes "Find_Aug_Path_call_1_conds state \<Longrightarrow> P"
          "Find_Aug_Path_ret_1_conds state \<Longrightarrow> P"
          "Find_Aug_Path_ret_2_conds state \<Longrightarrow> P"
  shows "P"
proof(cases "search_result state")
  case None
  then show ?thesis
    using assms(3)
    by (auto simp: Find_Aug_Path_ret_2_conds_def)
next
  case (Some res)
  then show ?thesis
    using assms(1,2)
    by (cases res)
       (auto simp: Find_Aug_Path_call_1_conds_def Find_Aug_Path_ret_1_conds_def)
qed

lemma Find_Aug_Path_simps:
  assumes "Find_Aug_Path_dom state"
  shows "Find_Aug_Path_call_1_conds state \<Longrightarrow>
           Find_Aug_Path state =
             Find_Aug_Path (Find_Aug_Path_upd1 state)"
        "Find_Aug_Path_ret_1_conds state \<Longrightarrow>
           Find_Aug_Path state = Find_Aug_Path_ret1 state"
        "Find_Aug_Path_ret_2_conds state \<Longrightarrow>
           Find_Aug_Path state = Find_Aug_Path_ret2 state"
  by (auto simp: Find_Aug_Path.psimps[OF assms] Let_def Find_Aug_Path_upd1_def
                 Find_Aug_Path_call_1_conds_def Find_Aug_Path_ret_1_conds_def
                 Find_Aug_Path_ret_2_conds_def)

lemma Find_Aug_Path_induct:
  assumes "Find_Aug_Path_dom state"
  assumes "\<And>state. \<lbrakk>Find_Aug_Path_dom state;
                     Find_Aug_Path_call_1_conds state \<Longrightarrow>
                       P (Find_Aug_Path_upd1 state)\<rbrakk>
                    \<Longrightarrow> P state"
  shows "P state"
  apply(rule Find_Aug_Path.pinduct[OF assms(1)])
  apply(rule assms(2))
  by (auto simp: Let_def Find_Aug_Path_call_1_conds_def Find_Aug_Path_upd1_def)

lemma Find_Aug_Path_domintros:
  assumes "Find_Aug_Path_call_1_conds state \<Longrightarrow>
             Find_Aug_Path_dom (Find_Aug_Path_upd1 state)"
  shows "Find_Aug_Path_dom state"
  using assms
  by (auto intro: Find_Aug_Path.domintros
           simp: Let_def Find_Aug_Path_call_1_conds_def Find_Aug_Path_upd1_def)

subsubsection \<open>Proofs\<close>

context
  assumes Find_Aug_Path_axiom: Find_Aug_Path_axiom
begin

lemma graph_input_G[simp]: "graph_input G vs"
  and matching_invar_M[simp]: "matching_invar G M"
  and vs_strict[simp]: "set vs \<subset> K"
  using Find_Aug_Path_axiom
  by (simp_all add: Find_Aug_Path_axiom_def)

lemma call_1_facts:
  assumes "Find_Aug_Path_call_1_conds state" "invar_1 state" "invar_search state"
  obtains stem C where
    "search_result state = Some (Blossom stem C)"
    "graph_input (search_graph state) (search_vertices state)"
    "matching_invar (search_graph state) (search_matching state)"
    "blossom (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) stem C"
    "create_vert (search_vertices state) \<notin> set (search_vertices state) - set C"
    "create_vert (search_vertices state) \<in> K"
proof-
  obtain stem C where sc: "search_result state = Some (Blossom stem C)"
    using assms(1)
    by (auto elim!: call_cond_elims)
  have g: "graph_input (search_graph state) (search_vertices state)"
          "matching_invar (search_graph state) (search_matching state)"
    using assms(2)
    by (auto simp: invar_1_def)
  have b: "blossom (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) stem C"
    using blos_search(2) assms(2,3) sc
    by (auto simp: invar_1_def invar_search_def)
  have strict: "set (search_vertices state) \<subset> K"
    using assms(2)
    by (simp add: invar_1_def)
  have "create_vert (search_vertices state) \<notin> set (search_vertices state) - set C"
    using create_vert[OF strict]
    by blast
  thus ?thesis
    by (rule that[OF sc g b _ create_vert_in_univ[OF strict]])
qed

lemma upd1_fields:
  assumes "search_result state = Some (Blossom stem C)"
  shows "search_graph (Find_Aug_Path_upd1 state) =
           contract_graph (search_graph state) (search_vertices state) C
             (create_vert (search_vertices state))"
        "search_vertices (Find_Aug_Path_upd1 state) =
           contract_vertices (search_vertices state) C (create_vert (search_vertices state))"
        "search_matching (Find_Aug_Path_upd1 state) =
           contract_matching (search_matching state) C
             (create_vert (search_vertices state))"
        "contractions (Find_Aug_Path_upd1 state) =
           (search_graph state, search_matching state, C, create_vert (search_vertices state))
             # contractions state"
        "search_result (Find_Aug_Path_upd1 state) =
           blos_search (search_graph (Find_Aug_Path_upd1 state))
             (search_vertices (Find_Aug_Path_upd1 state))
             (search_matching (Find_Aug_Path_upd1 state))"
  using assms
  by (simp_all add: Find_Aug_Path_upd1_def Let_def)

subsubsection \<open>The representation invariant\<close>

lemma invar_1_props[invar_props_elims]:
  "\<lbrakk>invar_1 state;
   (\<lbrakk>graph_input (search_graph state) (search_vertices state);
     matching_invar (search_graph state) (search_matching state);
     set (search_vertices state) \<subset> K\<rbrakk> \<Longrightarrow> P) \<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]:
  "\<lbrakk>graph_input (search_graph state) (search_vertices state);
    matching_invar (search_graph state) (search_matching state);
    set (search_vertices state) \<subset> K\<rbrakk> \<Longrightarrow> invar_1 state"
  by (auto simp: invar_1_def)

lemma invar_1_holds_1[invar_holds_intros]:
  assumes "Find_Aug_Path_call_1_conds state" "invar_1 state" "invar_search state"
  shows "invar_1 (Find_Aug_Path_upd1 state)"
proof-
  obtain stem C where result: "search_result state = Some (Blossom stem C)"
    and contract:
    "graph_input (search_graph state) (search_vertices state)"
    "matching_invar (search_graph state) (search_matching state)"
    "blossom (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) stem C"
    "create_vert (search_vertices state) \<notin> set (search_vertices state) - set C"
    "create_vert (search_vertices state) \<in> K"
    by (rule call_1_facts[OF assms])
  note upd = upd1_fields[OF result]
  have strict: "set (search_vertices state) \<subset> K"
    using assms(2)
    by (simp add: invar_1_def)
  show ?thesis
    using contract_graph_input[OF contract] contract_matching_invar[OF contract]
      contract_vertices_strict[OF contract strict]
    by (auto intro!: invar_props_intros simp: upd)
qed

subsubsection \<open>The stored search result\<close>

lemma invar_search_props[invar_props_elims]:
  "\<lbrakk>invar_search state;
   (search_result state =
      blos_search (search_graph state) (search_vertices state) (search_matching state) \<Longrightarrow> P)
   \<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_search_def)

lemma invar_search_intro[invar_props_intros]:
  "search_result state =
     blos_search (search_graph state) (search_vertices state) (search_matching state)
   \<Longrightarrow> invar_search state"
  by (auto simp: invar_search_def)

lemma invar_search_holds_1[invar_holds_intros]:
  "\<lbrakk>Find_Aug_Path_call_1_conds state; invar_search state\<rbrakk>
   \<Longrightarrow> invar_search (Find_Aug_Path_upd1 state)"
proof-
  assume "Find_Aug_Path_call_1_conds state" "invar_search state"
  then obtain stem C where f: "search_result state = Some (Blossom stem C)"
    by (auto elim!: call_cond_elims)
  show "invar_search (Find_Aug_Path_upd1 state)"
    unfolding invar_search_def
    by (rule upd1_fields(5)[OF f])
qed

lemma invar_search_holds[invar_holds_intros]:
  assumes "Find_Aug_Path_dom state" "invar_search state"
  shows "invar_search (Find_Aug_Path state)"
  using assms(2-)
proof(induction rule: Find_Aug_Path_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Find_Aug_Path_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Find_Aug_Path_simps[OF IH(1)])
qed

lemma invar_1_holds[invar_holds_intros]:
  assumes "Find_Aug_Path_dom state" "invar_1 state" "invar_search state"
  shows "invar_1 (Find_Aug_Path state)"
  using assms(2-)
proof(induction rule: Find_Aug_Path_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Find_Aug_Path_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Find_Aug_Path_simps[OF IH(1)])
qed

subsubsection \<open>Lifting gives augmenting paths of the input\<close>

lemma invar_lift_props[invar_props_elims]:
  "\<lbrakk>invar_lift state;
   ((\<forall>p. graph_augmenting_path (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) p
         \<longrightarrow> graph_augmenting_path (ugraph_abs G) (matching_abs M) (lift_path (contractions state) p))
    \<Longrightarrow> P) \<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_lift_def)

lemma invar_lift_intro[invar_props_intros]:
  "(\<forall>p. graph_augmenting_path (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) p
        \<longrightarrow> graph_augmenting_path (ugraph_abs G) (matching_abs M) (lift_path (contractions state) p))
   \<Longrightarrow> invar_lift state"
  by (auto simp: invar_lift_def)

lemma invar_lift_holds_1[invar_holds_intros]:
  assumes "Find_Aug_Path_call_1_conds state" "invar_1 state" "invar_search state"
          "invar_lift state"
  shows "invar_lift (Find_Aug_Path_upd1 state)"
proof-
  obtain stem C where result: "search_result state = Some (Blossom stem C)"
    and contract:
    "graph_input (search_graph state) (search_vertices state)"
    "matching_invar (search_graph state) (search_matching state)"
    "blossom (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) stem C"
    "create_vert (search_vertices state) \<notin> set (search_vertices state) - set C"
    "create_vert (search_vertices state) \<in> K"
    by (rule call_1_facts[OF assms(1-3)])
  note upd = upd1_fields[OF result]
  show ?thesis
    using refine_correct[OF contract] assms(4)
    by (auto intro!: invar_props_intros elim!: invar_props_elims simp: upd)
qed

lemma invar_lift_holds[invar_holds_intros]:
  assumes "Find_Aug_Path_dom state" "invar_1 state" "invar_search state"
          "invar_lift state"
  shows "invar_lift (Find_Aug_Path state)"
  using assms(2-)
proof(induction rule: Find_Aug_Path_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Find_Aug_Path_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Find_Aug_Path_simps[OF IH(1)])
qed

subsubsection \<open>Contraction preserves the existence of augmenting paths\<close>

lemma invar_complete_props[invar_props_elims]:
  "\<lbrakk>invar_complete state;
   (((\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p) \<longrightarrow>
     (\<exists>p. graph_augmenting_path (ugraph_abs (search_graph state))
            (matching_abs (search_matching state)) p)) \<Longrightarrow> P) \<rbrakk> \<Longrightarrow> P"
  by (auto simp: invar_complete_def)

lemma invar_complete_intro[invar_props_intros]:
  "((\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p) \<longrightarrow>
    (\<exists>p. graph_augmenting_path (ugraph_abs (search_graph state))
           (matching_abs (search_matching state)) p))
   \<Longrightarrow> invar_complete state"
  by (auto simp: invar_complete_def)

lemma invar_complete_holds_1[invar_holds_intros]:
  assumes "Find_Aug_Path_call_1_conds state" "invar_1 state" "invar_search state"
          "invar_complete state"
  shows "invar_complete (Find_Aug_Path_upd1 state)"
proof-
  obtain stem C where result: "search_result state = Some (Blossom stem C)"
    and contract:
    "graph_input (search_graph state) (search_vertices state)"
    "matching_invar (search_graph state) (search_matching state)"
    "blossom (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) stem C"
    "create_vert (search_vertices state) \<notin> set (search_vertices state) - set C"
    "create_vert (search_vertices state) \<in> K"
    by (rule call_1_facts[OF assms(1-3)])
  note upd = upd1_fields[OF result]
  have comp: "(\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p) \<longrightarrow>
              (\<exists>p. graph_augmenting_path (ugraph_abs (search_graph state))
                     (matching_abs (search_matching state)) p)"
    using assms(4)
    unfolding invar_complete_def .
  show ?thesis
    unfolding invar_complete_def upd(1,3)
  proof(intro impI)
    assume "\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
    hence "\<exists>p. graph_augmenting_path (ugraph_abs (search_graph state))
                   (matching_abs (search_matching state)) p"
      using comp
      by blast
    thus "\<exists>p. graph_augmenting_path
                 (ugraph_abs (contract_graph (search_graph state) (search_vertices state) C
                                (create_vert (search_vertices state))))
                 (matching_abs (contract_matching (search_matching state) C
                                  (create_vert (search_vertices state)))) p"
      by (rule contract_complete[OF contract])
  qed
qed

lemma invar_complete_holds[invar_holds_intros]:
  assumes "Find_Aug_Path_dom state" "invar_1 state" "invar_search state"
          "invar_complete state"
  shows "invar_complete (Find_Aug_Path state)"
  using assms(2-)
proof(induction rule: Find_Aug_Path_induct[OF assms(1)])
  case IH: (1 state)
  show ?case
    apply(rule Find_Aug_Path_cases[where state = state])
    by (auto intro!: IH(2-) intro: invar_holds_intros simp: Find_Aug_Path_simps[OF IH(1)])
qed

subsubsection \<open>Termination\<close>

named_theorems termination_intros

lemma call_1_terminates[termination_intros]:
  assumes "Find_Aug_Path_call_1_conds state" "invar_1 state" "invar_search state"
  shows "(Find_Aug_Path_upd1 state, state) \<in> call_1_measure <*mlex*> r"
proof-
  obtain stem C where result: "search_result state = Some (Blossom stem C)"
    and contract:
    "graph_input (search_graph state) (search_vertices state)"
    "matching_invar (search_graph state) (search_matching state)"
    "blossom (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) stem C"
    "create_vert (search_vertices state) \<notin> set (search_vertices state) - set C"
    "create_vert (search_vertices state) \<in> K"
    by (rule call_1_facts[OF assms])
  note upd = upd1_fields[OF result]
  show ?thesis
    using contract_card_Vs[OF contract]
    by (intro mlex_less) (simp add: call_1_measure_def upd)
qed

lemma wf_term_rel: "wf Find_Aug_Path_term_rel'"
  by (auto simp: wf_mlex Find_Aug_Path_term_rel'_def)

lemma in_Find_Aug_Path_term_rel'[termination_intros]:
  "\<lbrakk>Find_Aug_Path_call_1_conds state; invar_1 state; invar_search state\<rbrakk> \<Longrightarrow>
     (Find_Aug_Path_upd1 state, state) \<in> Find_Aug_Path_term_rel'"
  by (simp add: Find_Aug_Path_term_rel'_def termination_intros)

lemma Find_Aug_Path_terminates[termination_intros]:
  assumes "invar_1 state" "invar_search state"
  shows "Find_Aug_Path_dom state"
  using wf_term_rel assms
proof(induction rule: wf_induct_rule)
  case (less x)
  show ?case
  proof(rule Find_Aug_Path_domintros)
    assume c: "Find_Aug_Path_call_1_conds x"
    have "(Find_Aug_Path_upd1 x, x) \<in> Find_Aug_Path_term_rel'"
      by (rule in_Find_Aug_Path_term_rel'[OF c less(2,3)])
    moreover have "invar_1 (Find_Aug_Path_upd1 x)"
      by (rule invar_1_holds_1[OF c less(2,3)])
    moreover have "invar_search (Find_Aug_Path_upd1 x)"
      by (rule invar_search_holds_1[OF c less(3)])
    ultimately show "Find_Aug_Path_dom (Find_Aug_Path_upd1 x)"
      by (rule less(1))
  qed
qed

subsubsection \<open>Correctness\<close>

lemma Find_Aug_Path_correct_ret_1:
  assumes "invar_1 state" "invar_search state" "invar_lift state"
          "Find_Aug_Path_ret_1_conds state" "augmenting_path state = Some q"
  shows "graph_augmenting_path (ugraph_abs G) (matching_abs M) q"
proof-
  obtain p where p: "search_result state = Some (Path p)"
    using assms(4)
    by (auto elim!: call_cond_elims)
  have "graph_augmenting_path (ugraph_abs (search_graph state)) (matching_abs (search_matching state)) p"
    using blos_search(1) assms(1,2) p
    by (auto elim!: invar_props_elims)
  moreover have "q = lift_path (contractions state) p"
    using assms(5) p
    by (simp add: augmenting_path_def)
  ultimately show ?thesis
    using assms(3)
    by (auto elim!: invar_props_elims)
qed

lemma Find_Aug_Path_correct_ret_2:
  assumes "invar_1 state" "invar_search state" "invar_complete state"
          "Find_Aug_Path_ret_2_conds state"
  shows "augmenting_path state = None"
        "\<nexists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
proof-
  have none: "search_result state = None"
    using assms(4)
    by (auto elim!: call_cond_elims)
  thus "augmenting_path state = None"
    by (simp add: augmenting_path_def)
  have g: "graph_input (search_graph state) (search_vertices state)"
          "matching_invar (search_graph state) (search_matching state)"
    using assms(1)
    by (auto elim!: invar_props_elims)
  have bs: "blos_search (search_graph state) (search_vertices state) (search_matching state) = None"
    using assms(2) none
    unfolding invar_search_def
    by simp
  have "\<nexists>p. graph_augmenting_path (ugraph_abs (search_graph state))
               (matching_abs (search_matching state)) p"
    using blos_search(3)[OF g] bs
    by blast
  moreover have "(\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p) \<longrightarrow>
                 (\<exists>p. graph_augmenting_path (ugraph_abs (search_graph state))
                        (matching_abs (search_matching state)) p)"
    using assms(3)
    unfolding invar_complete_def .
  ultimately show "\<nexists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
    by blast
qed

lemma ret_holds[ret_holds_intros]:
  assumes "Find_Aug_Path_dom state"
  shows "Find_Aug_Path_ret_1_conds (Find_Aug_Path state) \<or>
         Find_Aug_Path_ret_2_conds (Find_Aug_Path state)"
proof(induction rule: Find_Aug_Path_induct[OF assms])
  case IH: (1 state)
  show ?case
    apply(rule Find_Aug_Path_cases[where state = state])
    by (auto dest: IH(2) simp: Find_Aug_Path_simps[OF IH(1)])
qed

subsubsection \<open>The initial state\<close>

lemma initial_state_props[invar_holds_intros, termination_intros]:
  "invar_1 initial_state" "invar_search initial_state" "invar_lift initial_state"
  "invar_complete initial_state" "Find_Aug_Path_dom initial_state"
proof-
  show inv1: "invar_1 initial_state"
    by (rule invar_1_intro) (simp_all add: initial_state_def)
  show invs: "invar_search initial_state"
    by (auto intro!: invar_props_intros simp: initial_state_def)
  show "invar_lift initial_state"
    by (auto intro!: invar_props_intros simp: initial_state_def)
  show "invar_complete initial_state"
    by (auto intro!: invar_props_intros simp: initial_state_def)
  show "Find_Aug_Path_dom initial_state"
    by (rule Find_Aug_Path_terminates[OF inv1 invs])
qed

lemma Find_Aug_Path_impl_to_Find_Aug_Path:
  "Find_Aug_Path_impl initial_state = Find_Aug_Path initial_state"
  by (auto intro!: Find_Aug_Path_impl_same initial_state_props)

subsubsection \<open>Final correctness\<close>

lemma final_state_invars:
  "invar_1 (Find_Aug_Path initial_state)"
  "invar_search (Find_Aug_Path initial_state)"
  "invar_lift (Find_Aug_Path initial_state)"
  "invar_complete (Find_Aug_Path initial_state)"
  by (intro invar_1_holds invar_search_holds invar_lift_holds invar_complete_holds
            initial_state_props)+

lemma Find_Aug_Path_correct_1:
  assumes "augmenting_path (Find_Aug_Path initial_state) = Some q"
  shows "graph_augmenting_path (ugraph_abs G) (matching_abs M) q"
  using ret_holds[OF initial_state_props(5)] assms
        Find_Aug_Path_correct_ret_1[OF final_state_invars(1-3)]
        Find_Aug_Path_correct_ret_2(1)[OF final_state_invars(1,2,4)]
  by auto

lemma Find_Aug_Path_correct_2:
  assumes "\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p"
  shows "augmenting_path (Find_Aug_Path initial_state) \<noteq> None"
proof-
  have "\<not> Find_Aug_Path_ret_2_conds (Find_Aug_Path initial_state)"
    using Find_Aug_Path_correct_ret_2(2)[OF final_state_invars(1,2,4)] assms
    by blast
  hence "Find_Aug_Path_ret_1_conds (Find_Aug_Path initial_state)"
    using ret_holds[OF initial_state_props(5)]
    by blast
  thus ?thesis
    by (auto elim!: call_cond_elims simp: augmenting_path_def)
qed

lemma Find_Aug_Path_run_impl_correct:
  "Find_Aug_Path_run_impl = Some q \<Longrightarrow>
     graph_augmenting_path (ugraph_abs G) (matching_abs M) q"
  "\<exists>p. graph_augmenting_path (ugraph_abs G) (matching_abs M) p \<Longrightarrow>
     Find_Aug_Path_run_impl \<noteq> None"
  using Find_Aug_Path_correct_1 Find_Aug_Path_correct_2
  by (simp_all add: Find_Aug_Path_run_impl_def
                    Find_Aug_Path_impl_to_Find_Aug_Path)

end

end

end
