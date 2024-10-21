theory DFS_RBT
  imports DFS
begin

definition "t_set \<equiv> Tree2.set_tree"
definition "neighb_inv \<equiv>  (\<lambda>t. (invc t \<and> invh t) \<and> Tree2.bst t)"
definition "neighb_empty = Leaf"

notation neighb_empty ("\<emptyset>\<^sub>N")

fun sel where
"sel Leaf = undefined" |
"sel (B l a r) = a"|
"sel (R l a r) = a"

lemma Set_satisified: "Set neighb_empty neighb_insert neighb_delete isin t_set neighb_inv"
  using  RBT.Set_axioms 
  by(auto simp add: neighb_empty_def neighb_delete_def neighb_insert_def t_set_def neighb_inv_def)

interpretation Set: Set where 
empty = neighb_empty and  insert = neighb_insert and
 delete = neighb_delete and isin = isin and  set = t_set and invar = neighb_inv
  using Set_satisified by simp

lemma Set_Choose_axioms: "Set_Choose_axioms neighb_empty isin sel"
  apply(rule Set_Choose_axioms.intro)
  unfolding neighb_empty_def  
  subgoal for s
    by(induction rule: sel.induct) auto
  done
 
lemma Set_Choose_satisfied:"Set_Choose neighb_empty neighb_insert neighb_delete isin neighb_inv t_set sel"
  using Set_satisified Set_Choose_axioms
  by(auto simp add: Set_Choose_def)

interpretation Set_Choose: Set_Choose where
empty = neighb_empty and insert = neighb_insert and  delete = neighb_delete and
isin = isin and invar = neighb_inv and t_set = t_set and sel = sel
  using Set_Choose_satisfied by simp

global_interpretation dfs: DFS where insert = neighb_insert and
 sel = sel and  neighb_empty = neighb_empty and  diff = neighb_diff and
 lookup = lookup and empty = empty and delete=delete and isin = isin and t_set=t_set
and update=update and adj_inv = adj_inv and neighb_delete= neighb_delete
and neighb_inv = neighb_inv and union=neighb_union and inter=neighb_inter and G = F and
t = "t::nat" and s = "s::nat"  for F t s
defines  dfs_initial_state = dfs.initial_state and
neighbourhood=dfs.Graph.neighbourhood and
dfs_impl = dfs.DFS_impl
  using Pair_Graph_Specs_satisfied Set2_satisfied 
  by(auto intro!: DFS.intro simp add: edge_map_update_def)

context
begin
definition "edges = [(0::nat, 1::nat), (0, 2), (2, 3), (2,4), (2,1), (1,5), (5,8), (8,7), (7,1),
                     (7,2), (7,4), (4,3), (3,4), (3,3), (9, 8), (8, 1), (4,5), (5,10)]"

definition "vertices = remdups (map prod.fst edges @ map prod.snd edges)"

definition "nbs v = foldr (\<lambda> x tree. insert x tree) (remdups (map prod.snd (filter (\<lambda> e. prod.fst e = v) edges))) neighb_empty"

definition "G = foldr (\<lambda> x tree. update x (nbs x) tree) vertices  empty"

value edges
value vertices
value G
value "dfs_initial_state 1"   
value "dfs_impl G 9 (dfs_initial_state 0)"
value "neighb_diff (nbs 1) (nbs 2)"
end