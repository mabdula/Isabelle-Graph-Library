theory DDFS_Example
  imports DDFS_Interpretation Directed_Set_Graphs.Pair_Graph_RBT
begin

text \<open>
Executable end-to-end DDFS demo at the RBT backend.
This file defines concrete plain-set digraphs (diamond, chain), their RBT
adjacency-map counterparts, and the bridge lemmas connecting the two
representations.  Interpretations and value-level demos arrive in later phases.
\<close>

section \<open>Concrete layered digraphs\<close>

subsection \<open>Diamond graph\<close>

definition dG_diamond :: "(nat \<times> nat) set" where
  "dG_diamond = {(3,2),(3,1),(2,0),(1,0)}"

abbreviation "lev_id \<equiv> (id :: nat \<Rightarrow> nat)"

lemma dG_diamond_L1: "(v, v') \<in> dG_diamond \<Longrightarrow> id v' < id v"
  by (auto simp: dG_diamond_def)

lemma dG_diamond_L2: "finite (dVs dG_diamond)"
  by (rule finite_subset[of _ "{0,1,2,3}"]) (auto simp: dG_diamond_def dVs_def)

lemma dG_diamond_dVs: "dVs dG_diamond = {0,1,2,3}"
  by (auto simp: dG_diamond_def dVs_def)

lemma dG_diamond_L3:
  "v \<in> dVs dG_diamond \<Longrightarrow> \<exists>p v'. p \<noteq> [] \<and> dpath_bet dG_diamond p v v' \<and> id v' = 0"
proof -
  assume vin: "v \<in> dVs dG_diamond"
  have mem: "v \<in> {0,1,2,3}" using dG_diamond_dVs vin by auto
  then consider (v0) "v = 0" | (v1) "v = 1" | (v2) "v = 2" | (v3) "v = 3" by blast
  then show ?thesis
  proof cases
    case v0
    show ?thesis
      by (intro exI[of _ "[0]"] exI[of _ "0"])
         (auto simp: v0 vwalk_bet_def dG_diamond_def)
  next
    case v1
    show ?thesis
      by (intro exI[of _ "[1,0]"] exI[of _ "0"])
         (auto simp: v1 vwalk_bet_def dG_diamond_def)
  next
    case v2
    show ?thesis
      by (intro exI[of _ "[2,0]"] exI[of _ "0"])
         (auto simp: v2 vwalk_bet_def dG_diamond_def)
  next
    case v3
    show ?thesis
      by (intro exI[of _ "[3,1,0]"] exI[of _ "0"])
         (auto simp: v3 vwalk_bet_def dG_diamond_def)
  qed
qed

lemma dG_diamond_layered: "layered_dgraph dG_diamond lev_id"
proof (rule layered_dgraphI)
  show "finite (dVs dG_diamond)" using dG_diamond_L2 by simp
next
  fix v v' assume "(v, v') \<in> dG_diamond"
  then show "lev_id v' < lev_id v" using dG_diamond_L1 by simp
next
  fix v assume "v \<in> dVs dG_diamond"
  then show "\<exists>p v'. dpath_bet dG_diamond p v v' \<and> lev_id v' = 0"
    using dG_diamond_L3 by fastforce
qed
subsection \<open>Chain graph\<close>

definition dG_chain :: "(nat \<times> nat) set" where
  "dG_chain = {(3,2),(2,1),(1,0)}"

lemma dG_chain_L1: "(v, v') \<in> dG_chain \<Longrightarrow> id v' < id v"
  by (auto simp: dG_chain_def)

lemma dG_chain_L2: "finite (dVs dG_chain)"
  by (rule finite_subset[of _ "{0,1,2,3}"]) (auto simp: dG_chain_def dVs_def)

lemma dG_chain_dVs: "dVs dG_chain = {0,1,2,3}"
  by (auto simp: dG_chain_def dVs_def)

lemma dG_chain_L3:
  "v \<in> dVs dG_chain \<Longrightarrow> \<exists>p v'. p \<noteq> [] \<and> dpath_bet dG_chain p v v' \<and> id v' = 0"
proof -
  assume vin: "v \<in> dVs dG_chain"
  have mem: "v \<in> {0,1,2,3}" using dG_chain_dVs vin by auto
  then consider (v0) "v = 0" | (v1) "v = 1" | (v2) "v = 2" | (v3) "v = 3" by blast
  then show ?thesis
  proof cases
    case v0
    show ?thesis
      by (intro exI[of _ "[0]"] exI[of _ "0"])
         (auto simp: v0 vwalk_bet_def dG_chain_def)
  next
    case v1
    show ?thesis
      by (intro exI[of _ "[1,0]"] exI[of _ "0"])
         (auto simp: v1 vwalk_bet_def dG_chain_def)
  next
    case v2
    show ?thesis
      by (intro exI[of _ "[2,1,0]"] exI[of _ "0"])
         (auto simp: v2 vwalk_bet_def dG_chain_def)
  next
    case v3
    show ?thesis
      by (intro exI[of _ "[3,2,1,0]"] exI[of _ "0"])
         (auto simp: v3 vwalk_bet_def dG_chain_def)
  qed
qed

lemma dG_chain_layered: "layered_dgraph dG_chain lev_id"
proof (rule layered_dgraphI)
  show "finite (dVs dG_chain)" using dG_chain_L2 by simp
next
  fix v v' assume "(v, v') \<in> dG_chain"
  then show "lev_id v' < lev_id v" using dG_chain_L1 by simp
next
  fix v assume "v \<in> dVs dG_chain"
  then show "\<exists>p v'. dpath_bet dG_chain p v v' \<and> lev_id v' = 0"
    using dG_chain_L3 by fastforce
qed
section \<open>RBT graph definitions\<close>

definition "G_diamond_rbt = a_graph [(3::nat,2::nat),(3,1),(2,0),(1,0)]"
definition "G_chain_rbt   = a_graph [(3::nat,2::nat),(2,1),(1,0)]"

section \<open>Bridge: RBT graphs realise the plain-set graphs\<close>

lemma G_diamond_rbt_lit: "G_diamond_rbt = B (B \<langle>\<rangle> (0, \<langle>\<rangle>) \<langle>\<rangle>) (1, B \<langle>\<rangle> 0 \<langle>\<rangle>) (B \<langle>\<rangle> (2, B \<langle>\<rangle> 0 \<langle>\<rangle>) (R \<langle>\<rangle> (3, B \<langle>\<rangle> 1 (R \<langle>\<rangle> 2 \<langle>\<rangle>)) \<langle>\<rangle>))"
  by eval

lemma G_chain_rbt_lit: "G_chain_rbt = B (B \<langle>\<rangle> (0, \<langle>\<rangle>) \<langle>\<rangle>) (1, B \<langle>\<rangle> 0 \<langle>\<rangle>) (B \<langle>\<rangle> (2, B \<langle>\<rangle> 1 \<langle>\<rangle>) (R \<langle>\<rangle> (3, B \<langle>\<rangle> 2 \<langle>\<rangle>) \<langle>\<rangle>))"
  by eval

lemma adj_inv_diamond: "adj_inv G_diamond_rbt"
  unfolding adj_inv_def G_diamond_rbt_def a_graph_def vertices_def nbs_def
  apply simp
  by (intro M.invar_update M.invar_empty)

lemma graph_inv_diamond: "G.graph_inv G_diamond_rbt"
proof (rule G.graph_invI)
  show "M.invar G_diamond_rbt"
    using adj_inv_diamond unfolding adj_inv_def .
next
  fix v vset assume "lookup G_diamond_rbt v = Some vset"
  then show "vset_inv vset"
    by (simp only: G_diamond_rbt_lit) (auto simp: vset_inv_def lookup.simps split: option.splits if_splits)
qed

lemma finite_graph_diamond: "G.finite_graph G_diamond_rbt"
proof -
  have "{v::nat. lookup G_diamond_rbt v \<noteq> None} \<subseteq> {0,1,2,3}"
    by (auto simp: G_diamond_rbt_lit lookup.simps split: if_splits)
  then show ?thesis
    unfolding G.finite_graph_def
    by (rule finite_subset) simp
qed

lemma finite_vsets_diamond: "G.finite_vsets G_diamond_rbt"
  unfolding G.finite_vsets_def
  by (auto simp: G_diamond_rbt_lit lookup.simps split: if_splits)

lemma dabs_diamond: "G.digraph_abs G_diamond_rbt = dG_diamond"
  unfolding G.digraph_abs_def dG_diamond_def G.neighbourhood_def
  by (auto simp: G_diamond_rbt_lit lookup.simps isin.simps split: option.splits if_splits)

lemma adj_inv_chain: "adj_inv G_chain_rbt"
  unfolding adj_inv_def G_chain_rbt_def a_graph_def vertices_def nbs_def
  apply simp
  by (intro M.invar_update M.invar_empty)

lemma graph_inv_chain: "G.graph_inv G_chain_rbt"
proof (rule G.graph_invI)
  show "M.invar G_chain_rbt"
    using adj_inv_chain unfolding adj_inv_def .
next
  fix v vset assume "lookup G_chain_rbt v = Some vset"
  then show "vset_inv vset"
    by (simp only: G_chain_rbt_lit) (auto simp: vset_inv_def lookup.simps split: option.splits if_splits)
qed

lemma finite_graph_chain: "G.finite_graph G_chain_rbt"
proof -
  have "{v::nat. lookup G_chain_rbt v \<noteq> None} \<subseteq> {0,1,2,3}"
    by (auto simp: G_chain_rbt_lit lookup.simps split: if_splits)
  then show ?thesis
    unfolding G.finite_graph_def
    by (rule finite_subset) simp
qed

lemma finite_vsets_chain: "G.finite_vsets G_chain_rbt"
  unfolding G.finite_vsets_def
  by (auto simp: G_chain_rbt_lit lookup.simps split: if_splits)

lemma dabs_chain: "G.digraph_abs G_chain_rbt = dG_chain"
  unfolding G.digraph_abs_def dG_chain_def G.neighbourhood_def
  by (auto simp: G_chain_rbt_lit lookup.simps isin.simps split: option.splits if_splits)

section \<open>DDFS_layered global interpretations\<close>

global_interpretation ddfs_diamond: DDFS_layered
  where insert = vset_insert and sel = sel and vset_empty = vset_empty
    and diff = vset_diff and lookup = lookup and empty = map_empty
    and delete = RBT_Map.delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv
    and vset_delete = vset_delete and vset_inv = vset_inv
    and union = vset_union and inter = vset_inter
    and G = G_diamond_rbt and lev = "id :: nat \<Rightarrow> nat"
  defines ddfs_diamond_run = ddfs_diamond.DDFS_impl
      and vol_diamond = ddfs_diamond.vset_of_list
      and idfs_diamond_run = ddfs_diamond.IDFS_impl
      and neighbourhood_diamond = ddfs_diamond.Graph.neighbourhood
      and add_edge_diamond    = ddfs_diamond.Graph.add_edge
      and delete_edge_diamond = ddfs_diamond.Graph.delete_edge
      and from_list_diamond   = ddfs_diamond.Graph.from_list
      and IDFS_stack0_diamond = ddfs_diamond.IDFS_stack0
  proof (intro IDFS.DDFS_layered.intro IDFS.IDFS_witness.intro
               IDFS.IDFS_witness_axioms.intro, goal_cases)
    case 1
    show ?case
      using G.Pair_Graph_Specs_axioms
      by (simp add: adj_inv_def map_empty_def RBT_Set.empty_def)
  next
    case 2
    show ?case
      using RBT.Set2_axioms
      by (simp add: vset_inv_def RBT_Set.empty_def)
  next
    case 3
    have PGS: "Pair_Graph_Specs map_empty RBT_Map.delete lookup vset_insert isin
                                 t_set sel update adj_inv vset_empty vset_delete vset_inv"
      using G.Pair_Graph_Specs_axioms
      by (simp add: adj_inv_def map_empty_def RBT_Set.empty_def)
    have eq: "Pair_Graph_Specs.digraph_abs lookup isin vset_empty G_diamond_rbt
              = dG_diamond"
      using dabs_diamond
      by (simp add: adj_inv_def map_empty_def RBT_Set.empty_def)
    have gi: "Pair_Graph_Specs.graph_inv lookup adj_inv vset_inv G_diamond_rbt"
      using graph_inv_diamond
      unfolding G.graph_inv_def Pair_Graph_Specs.graph_inv_def adj_inv_def by blast
    have fg: "G.finite_graph G_diamond_rbt"
      by (rule finite_graph_diamond)
    have fv: "G.finite_vsets G_diamond_rbt"
      by (rule finite_vsets_diamond)
    show ?case
      unfolding Pair_Graph_Specs.layered_graph_input_def[OF PGS] eq
      by (intro conjI gi fg fv dG_diamond_layered)
  qed

global_interpretation ddfs_chain: DDFS_layered
  where insert = vset_insert and sel = sel and vset_empty = vset_empty
    and diff = vset_diff and lookup = lookup and empty = map_empty
    and delete = RBT_Map.delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv
    and vset_delete = vset_delete and vset_inv = vset_inv
    and union = vset_union and inter = vset_inter
    and G = G_chain_rbt and lev = "id :: nat \<Rightarrow> nat"
  defines ddfs_chain_run = ddfs_chain.DDFS_impl
      and vol_chain = ddfs_chain.vset_of_list
      and idfs_chain_run  = ddfs_chain.IDFS_impl
  proof (intro IDFS.DDFS_layered.intro IDFS.IDFS_witness.intro
               IDFS.IDFS_witness_axioms.intro, goal_cases)
    case 1
    show ?case
      using G.Pair_Graph_Specs_axioms
      by (simp add: adj_inv_def map_empty_def RBT_Set.empty_def)
  next
    case 2
    show ?case
      using RBT.Set2_axioms
      by (simp add: vset_inv_def RBT_Set.empty_def)
  next
    case 3
    have PGS: "Pair_Graph_Specs map_empty RBT_Map.delete lookup vset_insert isin
                                 t_set sel update adj_inv vset_empty vset_delete vset_inv"
      using G.Pair_Graph_Specs_axioms
      by (simp add: adj_inv_def map_empty_def RBT_Set.empty_def)
    have eq: "Pair_Graph_Specs.digraph_abs lookup isin vset_empty G_chain_rbt
              = dG_chain"
      using dabs_chain
      by (simp add: adj_inv_def map_empty_def RBT_Set.empty_def)
    have gi: "Pair_Graph_Specs.graph_inv lookup adj_inv vset_inv G_chain_rbt"
      using graph_inv_chain
      unfolding G.graph_inv_def Pair_Graph_Specs.graph_inv_def adj_inv_def by blast
    have fg: "G.finite_graph G_chain_rbt"
      by (rule finite_graph_chain)
    have fv: "G.finite_vsets G_chain_rbt"
      by (rule finite_vsets_chain)
    show ?case
      unfolding Pair_Graph_Specs.layered_graph_input_def[OF PGS] eq
      by (intro conjI gi fg fv dG_chain_layered)
  qed

section \<open>Generic DFS\_avoid interpretation (axioms-free skeleton pattern)\<close>

global_interpretation idfs: DFS_avoid
  where insert = vset_insert and sel = sel and vset_empty = vset_empty
    and diff = vset_diff and lookup = lookup and empty = map_empty
    and delete = RBT_Map.delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv
    and vset_delete = vset_delete and vset_inv = vset_inv
    and union = vset_union and inter = vset_inter
    and G = G and stack0 = p0 and vis0 = V0 and avoid = A0
    and Pv = P and level = lev
  for G p0 V0 A0 P lev
  defines find_idfs = idfs.av.DFS_skel_impl
    and   av_found_rbt = idfs.av_found
    and   neighbourhood_idfs = idfs.Graph.neighbourhood
    and   avoid_impl_rbt = idfs.avoid_final_state_impl
    and   avoid_initial_rbt = idfs.avoid_initial_state
    and   vset_of_list_rbt = idfs.vset_of_list
  using G.Pair_Graph_Specs_axioms RBT.Set2_axioms
  by (auto intro!: DFS_avoid.intro
           simp: adj_inv_def map_empty_def vset_inv_def RBT_Set.empty_def)

lemmas find_idfs_code[code] =
  idfs.av.DFS_skel_impl.simps[folded find_idfs_def[folded av_found_rbt_def],
    unfolded idfs.av_on_found_def idfs.av_on_empty_def
             idfs.av_on_backtrack_def]
lemmas av_found_rbt_code[code] = idfs.av_found_def

text \<open>Code equations for the DDFS layer (diamond graph).\<close>

lemmas ddfs_diamond_code[code] =
  DDFS.DDFS_impl.simps[OF ddfs_diamond.DDFS_axioms,
    folded ddfs_diamond_run_def[folded idfs_diamond_run_def neighbourhood_diamond_def],
    folded vol_diamond_def]

lemmas idfs_diamond_code[code] =
  ddfs_diamond.IDFS_impl_def[folded idfs_diamond_run_def,
    folded avoid_impl_rbt_def]

lemmas vol_diamond_code[code] =
  ddfs_diamond.vset_of_list_def[folded vol_diamond_def]

text \<open>Code equations for the DDFS layer (chain graph).\<close>

lemmas ddfs_chain_code[code] =
  DDFS.DDFS_impl.simps[OF ddfs_chain.DDFS_axioms,
    folded ddfs_chain_run_def[folded idfs_chain_run_def],
    folded vol_chain_def,
    folded neighbourhood_idfs_def]

lemmas idfs_chain_code[code] =
  ddfs_chain.IDFS_impl_def[folded idfs_chain_run_def,
    folded avoid_impl_rbt_def,
    folded IDFS_stack0_diamond_def]

lemmas vol_chain_code[code] =
  ddfs_chain.vset_of_list_def[folded vol_chain_def]

text \<open>Routing lemmas for the IDFS/DFS\_avoid code-equation chain.

Note: The fold find\_idfs\_def[folded av\_found\_rbt\_def] transforms find\_idfs G A0 P into
idfs.av.DFS\_skel\_impl G A0 P (at the term level), allowing avoid\_impl\_rbt to be routed
through find\_idfs which already has code equations via find\_idfs\_code.\<close>

lemmas avoid_impl_rbt_code[code] =
  idfs.avoid_final_state_impl_def[folded find_idfs_def[folded av_found_rbt_def]]
lemmas avoid_initial_rbt_code[code] = idfs.avoid_initial_state_def
lemmas vset_of_list_rbt_code[code] = idfs.vset_of_list_def


text \<open>Sanity check: vol_diamond is computable.
  Result verified: vol_diamond [3::nat, 2, 1, 0] evaluates to a valid RBT tree.
  Result verified: ddfs_diamond_run (initial state with curr1=3, curr2=2) = ([0, 1, 3], [0, 2]).\<close>

section \<open>Executable demos\<close>

text \<open>
This section provides six executable value commands that exercise the RBT-backed
DDFS and IDFS pipelines on the diamond and chain graphs.  All results were
obtained by running Isabelle's code evaluator on the definitions exported in the
previous sections; none are sorry-guarded.

Demos 1--3 call the two-phase DDFS via ddfs_diamond_run and ddfs_chain_run.
Demos 4--6 call the inner IDFS (DFS_avoid) via avoid_impl_rbt, projecting the
ret slot of the returned DFS_avoid_state.
\<close>

subsection \<open>DDFS demos\<close>

text \<open>
Demo 1.  Diamond graph, curr1 = 3, curr2 = 2, both stacks and visited sets
empty.  The two phases explore alternating layers: phase-1 descends from 3
while phase-2 descends from 2, meeting at level 0.  Expected result (exact,
confirmed by interactive probe): ([0, 1, 3], [0, 2]).
\<close>

value "ddfs_diamond_run
  \<lparr>curr1 = 3::nat, stack1 = [], vis1 = vset_empty,
   curr2 = 2::nat, stack2 = [], done2 = [], vis2 = vset_empty\<rparr>"

text \<open>
Demo 2.  Diamond graph, curr1 = curr2 = 3, both stacks and visited sets empty.
Because curr1 = curr2 the IDFS branch fires immediately on the first step,
searching for a path from curr2's perspective before any layer descent has
occurred.  The two returned paths are both rooted at level 3 or below,
and are disjoint by the DDFS correctness theorem.
\<close>

value "ddfs_diamond_run
  \<lparr>curr1 = 3::nat, stack1 = [], vis1 = vset_empty,
   curr2 = 3::nat, stack2 = [], done2 = [], vis2 = vset_empty\<rparr>"

text \<open>
Demo 3.  Chain graph, curr1 = 3, curr2 = 2, both stacks and visited sets empty.
The chain has a unique path 3 -> 2 -> 1 -> 0, so the two phases share this
single branch; the returned paths are prefixes of [3, 2, 1, 0].
\<close>

value "ddfs_chain_run
  \<lparr>curr1 = 3::nat, stack1 = [], vis1 = vset_empty,
   curr2 = 2::nat, stack2 = [], done2 = [], vis2 = vset_empty\<rparr>"

subsection \<open>Inner IDFS demos\<close>

text \<open>
Demos 4--6 exercise the inner DFS_avoid engine directly via avoid_impl_rbt.
The predicate \<open>\<lambda>v. v = 0\<close> is used as the found condition (search for the
unique level-0 vertex).  The result slot ret of the returned DFS_avoid_state
holds Some path if the target was reached, or None otherwise.
\<close>

text \<open>
Demo 4.  Diamond graph, initial stack [3], avoid set empty, visited set empty.
The DFS descends from 3 along one of the two branches to vertex 0.  Since the
avoid set is empty both branches [3, 1, 0] and [3, 2, 0] are reachable; the
sel-determined branch is chosen.  Expected: Some path ending at 0.
\<close>

value "DFS_avoid_state.ret
  (avoid_impl_rbt G_diamond_rbt [3::nat] vset_empty vset_empty
     (\<lambda>v. v = (0::nat)))"

text \<open>
Demo 5.  Diamond graph, initial stack [3], avoid set {2}, visited set empty.
With vertex 2 in the avoid set the DFS must bypass it and can only reach 0 via
vertex 1.  The ret slot stores the stack in head-first order, so the result
is Some [0, 1, 3] (the unique remaining path, with 0 at the top).
\<close>

value "DFS_avoid_state.ret
  (avoid_impl_rbt G_diamond_rbt [3::nat] vset_empty
     (vset_insert (2::nat) vset_empty)
     (\<lambda>v. v = (0::nat)))"

text \<open>
Demo 6.  Chain graph, initial stack [3], avoid set empty, visited set empty.
The chain has a unique path 3 -> 2 -> 1 -> 0, so the DFS finds the single
route to 0.  The ret slot stores the stack in head-first order, so the result
is Some [0, 1, 2, 3].
\<close>

value "DFS_avoid_state.ret
  (avoid_impl_rbt G_chain_rbt [3::nat] vset_empty vset_empty
     (\<lambda>v. v = (0::nat)))"

section \<open>SML code export\<close>

text \<open>
The following command exports the three top-level executable constants to SML.
It exercises the full code-equation chain: ddfs_diamond_run and ddfs_chain_run
go through ddfs_diamond_code/ddfs_chain_code which route DDFS_impl through the
IDFS layer; find_idfs goes through find_idfs_code.  A_graph appears because
G_diamond_rbt and G_chain_rbt are defined in terms of it.
\<close>

export_code ddfs_diamond_run ddfs_chain_run find_idfs a_graph
  in SML module_name DDFS_RBT

end
