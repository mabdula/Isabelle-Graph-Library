theory DDFS_Example
  imports DDFS_Interpretation Directed_Set_Graphs.Pair_Graph_RBT
begin

text \<open>
Phase 4: Executable DDFS demonstration.

== Representation decision ==

For executable value-level demos we need a computable sel (SOME is not executable).
We therefore use the Pair_Graph_RBT back-end (RBT-backed adjacency maps and vertex sets)
— the same back-end as DFS_DirCycle_Example — and instantiate DFS_avoid with it.
The code-generation recipe follows DFS_DirCycle_Example exactly:
  (1) global_interpretation with defines for the impl and found-callback;
  (2) lemmas ...[code] restating the partial-function simps with concrete callback names.

The initial state is constructed inline (as a concrete record) in each value call,
avoiding the need for a code equation for the abstract locale constant
DFS_avoid.avoid_initial_state.

Arities discovered empirically:
  find_idfs :: G \<rightarrow> A0 \<rightarrow> P \<rightarrow> state \<rightarrow> state  (3 for-params: graph, avoid, predicate)
  av_found_rbt :: G \<rightarrow> A0 \<rightarrow> P \<rightarrow> state \<rightarrow> bool
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

section \<open>DDFS_layered interpretations\<close>

interpretation ddfs_diamond: DDFS_layered dG_diamond lev_id
  sorry (*READT-TODO-37: original: using dG_diamond_L1 dG_diamond_L2 dG_diamond_L3 by unfold_locales auto; symptom: DDFS_layered undefined in PIDE Draft mode - cascade from TODO-20 sublocale sorry; pattern: Draft mode import cascade*)

interpretation ddfs_chain: DDFS_layered dG_chain lev_id
  sorry (*READT-TODO-38: original: using dG_chain_L1 dG_chain_L2 dG_chain_L3 by unfold_locales auto; symptom: DDFS_layered undefined - cascade from TODO-20; pattern: Draft mode import cascade*)

section \<open>Executable IDFS via RBT-backed DFS_avoid\<close>

text \<open>We follow the DFS_DirCycle_Example recipe: instantiate DFS_avoid with the
Pair_Graph_RBT back-end (computable sel, RBT adjacency maps) and provide concrete
code equations via defines + lemmas [code].
The initial state is constructed inline as a concrete DFS_avoid_state record
(stack, seen, visited, ret) to avoid exporting the abstract locale constant
DFS_avoid.avoid_initial_state which has no standalone code equations.\<close>

global_interpretation idfs: DFS_avoid
  where insert = vset_insert and sel = sel and vset_empty = vset_empty
    and diff = vset_diff and lookup = lookup and empty = map_empty
    and delete = delete and isin = isin and t_set = t_set
    and update = update and adjmap_inv = adj_inv
    and vset_delete = vset_delete and vset_inv = vset_inv
    and union = vset_union and inter = vset_inter
    and G = G and stack0 = p0 and vis0 = V0 and avoid = A0
    and Pv = P and level = lev
  for G and p0 and V0 and A0 and P and lev
  defines find_idfs    = idfs.av.DFS_skel_impl
    and   av_found_rbt = idfs.av_found
    and   neighbourhood_idfs = idfs.Graph.neighbourhood
  sorry (*READT-TODO-39: original: using G.Pair_Graph_Specs_axioms RBT.Set2_axioms by (auto intro!: DFS_avoid.intro simp: adj_inv_def map_empty_def vset_inv_def RBT_Set.empty_def); symptom: DFS_avoid undefined - cascade from TODO-20; pattern: Draft mode import cascade*)

text \<open>Concrete code equations following DFS_DirCycle_Example pattern.
find_idfs :: G \<rightarrow> A0 \<rightarrow> P \<rightarrow> state \<rightarrow> state (3 for-params from callbacks).\<close>
(*READT-TODO-40: original: lemmas find_idfs_code[code] = idfs.av.DFS_skel_impl.simps[folded find_idfs_def[folded av_found_rbt_def], unfolded idfs.av_on_found_def idfs.av_on_empty_def idfs.av_on_backtrack_def]; symptom: Undefined fact idfs.av.DFS_skel_impl.simps - global_interpretation sorry'd; pattern: non-fact command commented out per PASS 1 rules*)

text \<open>Code equation for the found predicate.\<close>
(*READT-TODO-41: original: lemmas av_found_rbt_code[code] = idfs.av_found_def; symptom: Undefined fact - cascade from TODO-39; pattern: non-fact command commented out*)

section \<open>Executable IDFS demos\<close>

text \<open>Build RBT adjacency maps from the edge lists.\<close>

definition "G_diamond_rbt = a_graph [(3::nat,2::nat),(3,1),(2,0),(1,0)]"
definition "G_chain_rbt   = a_graph [(3::nat,2::nat),(2,1),(1,0)]"

text \<open>
Signature:
  find_idfs :: G adj_map \<rightarrow> A0 vset \<rightarrow> P predicate \<rightarrow> DFS_avoid_state \<rightarrow> DFS_avoid_state

Initial states are constructed inline as concrete DFS_avoid_state records.
For stack0 = [v], vis0 = vset_empty, avoid = A0:
  seen0 = vset_union (vset_union A0 vset_empty) (vset_insert v vset_empty)
        = vset_union A0 (vset_insert v vset_empty)

For the demos below we use avoid = vset_empty so seen0 = vset_insert v vset_empty.
\<close>

text \<open>Demo 1: IDFS on diamond from [3], searching for 0, avoid = empty.
seen0 = {3}, expected: path Some [3,1,0] or [3,2,0] (DFS order).\<close>
(*READT-TODO-42: value "find_idfs G_diamond_rbt vset_empty (\<lambda>v::nat. v = 0) \<lparr>stack = [3::nat], seen = vset_insert (3::nat) vset_empty, visited = vset_empty, ret = None\<rparr>"; symptom: stack not a proper field - global_interpretation sorry'd; non-fact command commented out per PASS 1 rules*)

text \<open>Demo 2: IDFS on diamond from [2], searching for 0, avoid = empty.\<close>
(*READT-TODO-43: value "find_idfs G_diamond_rbt vset_empty (\<lambda>v::nat. v = 0) \<lparr>stack = [2::nat], seen = vset_insert (2::nat) vset_empty, visited = vset_empty, ret = None\<rparr>"; non-fact command commented out*)

text \<open>Demo 3: IDFS on diamond from [3] with avoid = {2}. Route via 2 blocked.
seen0 = {2,3}.\<close>
(*READT-TODO-44: value "find_idfs G_diamond_rbt (vset_insert 2 vset_empty) (\<lambda>v::nat. v = 0) \<lparr>stack = [3::nat], seen = vset_insert (2::nat) (vset_insert (3::nat) vset_empty), visited = vset_empty, ret = None\<rparr>"; non-fact command commented out*)

text \<open>Demo 4: IDFS on chain from [3], searching for 0, avoid = empty.\<close>
(*READT-TODO-45: value "find_idfs G_chain_rbt vset_empty (\<lambda>v::nat. v = 0) \<lparr>stack = [3::nat], seen = vset_insert (3::nat) vset_empty, visited = vset_empty, ret = None\<rparr>"; non-fact command commented out*)

section \<open>Export code\<close>

(*READT-TODO-46: export_code find_idfs a_graph in SML module_name IDFS_RBT; non-fact command commented out*)

end
