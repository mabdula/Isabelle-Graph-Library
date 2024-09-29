theory BFS
  imports Pair_Graph_Specs "HOL-Eisbach.Eisbach_Tools"
begin

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

fun fold_tree where
"fold_tree f Leaf a = a"
| "fold_tree f (Node l x r) a = fold_tree f r (fold_tree f l a)" 

definition "invar P I f \<equiv> (\<forall>s. (P s \<and> I s) \<longrightarrow> I (f s))"

lemma invarI: "(\<And>s. \<lbrakk>P s; I s\<rbrakk> \<Longrightarrow> I (f s)) \<Longrightarrow> invar P I f"
  by (auto simp: invar_def)

lemma invarE: "invar P I f \<Longrightarrow> ((\<And>s. \<lbrakk>P s; I s\<rbrakk> \<Longrightarrow> I (f s)) \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (auto simp: invar_def)

lemma invarD: "invar P I f \<Longrightarrow> (\<And>s. \<lbrakk>P s; I s\<rbrakk> \<Longrightarrow> I (f s))"
  by (auto simp: invar_def)


definition "valid_fold set_of fold_fun \<equiv> \<forall>dom f a0. (\<exists>xs. fold_fun f dom a0 = foldr f xs a0 \<and> set xs = set_of dom)"

lemma valid_foldE:
  "valid_fold set_of fold_fun \<Longrightarrow> 
    (\<And>xs. \<lbrakk>fold_fun f domain a0 = foldr f xs a0; set_of domain = set xs\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (fastforce simp: valid_fold_def)

lemma invar_fold_conjI:
  fixes f:: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>x. x \<in> set_of domain \<Longrightarrow> invar (\<lambda>_. True) (\<lambda>s. P s \<and> I s) (f x)"
  shows "invar P I (fold_fun f domain)"
proof-
  have "P (foldr f xs s) \<and> I (foldr f xs s)" if "(\<And>x. x \<in> set xs \<Longrightarrow> invar (\<lambda>_. True) (\<lambda>s. P s \<and> I s) (f x))" "P s" "I s" for xs s
    using that
  proof(induction xs)
    case (Cons x xs)
    hence "P (foldr f xs s)" "I (foldr f xs s)"
      by auto 
    thus ?case
      using Cons(2)[of x]
      by (auto elim!: invarE)
  qed auto
  hence "invar P I (foldr f xs)" if "(\<And>x. x \<in> set xs \<Longrightarrow> invar (\<lambda>_. True) (\<lambda>s. P s \<and> I s) (f x))" for xs
    using that
    by (auto intro!: invarI)
  thus ?thesis
    using assms
    by (smt (verit) invarE invarI valid_foldE)
qed

method elim_valid_fold for  f::"'a \<Rightarrow> 'b \<Rightarrow> 'b" = 
  ((match conclusion in "P (fold_fun f domain a0)" for a0::'b and fold_fun domain and P 
      \<Rightarrow> \<open>elim valid_foldE[where f = f and domain = domain and ?a0.0 = a0], match premises in a[thin]: 
           "fold_fun f domain a0 = foldr _ _ _"
              \<Rightarrow> \<open>subst  a\<close>\<close>))

lemma invar_foldI:
  fixes f:: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>x. x \<in> set_of domain \<Longrightarrow> invar (\<lambda>_. True) I (f x)"
  shows "invar (\<lambda>_. True) I (fold_fun f domain)"
  using assms(2)
  by(auto intro!: invar_fold_conjI[OF assms(1), where P = "\<lambda>_. True"])

lemma invar_foldI':
  fixes f:: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>x s. \<lbrakk>x \<in> set_of domain; I s\<rbrakk> \<Longrightarrow> I (f x s)"
    "I s"
  shows "I (fold_fun f domain s)"
  using invar_foldI[simplified invar_def, OF assms(1)] assms
  by metis

lemma invar_foldI'':
  fixes f:: "'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>s x. \<lbrakk>I s; x \<in> set_of (domain s)\<rbrakk> \<Longrightarrow> invar (\<lambda>_. True) I (f s x)"
  shows "invar (\<lambda>_. True) I (\<lambda>s. fold_fun (f s) (domain s) s)"
  using invar_foldI[OF assms(1)] assms(2-)
  by (metis (no_types, lifting) invar_def)

lemma invar_fold_conjI'':
  fixes f:: "'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b" and I::"'b \<Rightarrow> bool"
  assumes
    "valid_fold set_of fold_fun"
    "\<And>s x. \<lbrakk>I s; x \<in> set_of (domain s)\<rbrakk> \<Longrightarrow> invar (\<lambda>_. True) (\<lambda>s. P s \<and> I s) (f s x)"
  shows "invar P I (\<lambda>s. fold_fun (f s) (domain s) s)"
  using invar_fold_conjI[OF assms(1)] assms(2-)
  by (smt (verit, ccfv_SIG) invar_def)

lemma invar_conjI: "\<lbrakk>J; invar P (\<lambda>s. J \<and> I s) f\<rbrakk> \<Longrightarrow> invar P I f"
  by (auto simp: invar_def)

record ('parents, 'neighb) BFS_state = parents:: "'parents" current:: "'neighb" nexts:: "'neighb" visited:: "'neighb" 

locale BFS =
  (*set_ops: Set2 where empty = empty and insert = neighb_insert and isin = neighb_isin +*)
  Graph: Pair_Graph_Specs
    where lookup = lookup +
  set_ops: Set2 neighb_empty neighb_delete _ t_set neighb_inv neighb_insert
  
for lookup :: "'adj \<Rightarrow> 'ver \<Rightarrow> 'neighb option" +

fixes neighbourhood_fold ::
  "('ver \<Rightarrow> ('adj, 'neighb) BFS_state \<Rightarrow> ('adj, 'neighb) BFS_state) \<Rightarrow> 'neighb \<Rightarrow> 
   ('adj, 'neighb) BFS_state \<Rightarrow> ('adj, 'neighb) BFS_state" and
   G ::"'adj"
assumes
   neighbourhood_fold:
    "valid_fold t_set neighbourhood_fold" and
   graph_inv[simp]:
     "Graph.graph_inv G"

   \<comment> \<open>Every folding function that is needed for the domain of the map or the elements of the set
       can be added explicitly like this. There is no need to fix the function, but we need to fix
       its type.\<close>

begin

abbreviation "neighbourhood' \<equiv> Graph.neighbourhood G" 
notation "neighbourhood'" ("\<N>\<^sub>G _" 100)

notation "inter" (infixl "\<inter>\<^sub>G" 100)

notation "diff" (infixl "-\<^sub>G" 100)

notation "union" (infixl "\<union>\<^sub>G" 100)

declare set_ops.set_union[simp] set_ops.set_inter[simp] set_ops.set_diff[simp] set_ops.invar_union[simp]
        set_ops.invar_inter[simp] set_ops.invar_diff[simp]


definition "update_parent v u BFS_state \<equiv> (BFS_state \<lparr>parents := Graph.add_edge (parents BFS_state) v u\<rparr>)"

definition "update_parents v neighb BFS_state \<equiv> neighbourhood_fold (update_parent v) neighb BFS_state"

function (domintros) BFS::"('adj, 'neighb) BFS_state \<Rightarrow> ('adj, 'neighb) BFS_state" where
  "BFS BFS_state = 
     (if (current BFS_state) \<noteq> \<emptyset>\<^sub>N then
        let
          BFS_state = neighbourhood_fold (\<lambda>v. update_parents v (\<N>\<^sub>G v -\<^sub>G visited BFS_state)) (current BFS_state) BFS_state;
          BFS_state = neighbourhood_fold (\<lambda>v bfs_state. (bfs_state \<lparr>nexts := nexts bfs_state \<union>\<^sub>G (\<N>\<^sub>G v -\<^sub>G visited BFS_state)\<rparr>)) (current BFS_state) BFS_state
        in 
          BFS (BFS_state \<lparr>visited := visited BFS_state \<union>\<^sub>G current BFS_state, current := nexts BFS_state, nexts := \<emptyset>\<^sub>N \<rparr>)
       else
        BFS_state)"
  by pat_completeness auto

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros

definition "BFS_call_1_conds bfs_state \<equiv> (current bfs_state) \<noteq> \<emptyset>\<^sub>N"

lemma DFS_call_1_conds[call_cond_elims]: 
  "BFS_call_1_conds bfs_state \<Longrightarrow> 
   \<lbrakk>(current bfs_state) \<noteq> \<emptyset>\<^sub>N \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by(auto simp: BFS_call_1_conds_def split: list.splits option.splits if_splits)


definition "BFS_upd1_step_1 BFS_state \<equiv>
  neighbourhood_fold (\<lambda>v. update_parents v (\<N>\<^sub>G v -\<^sub>G visited BFS_state)) (current BFS_state) BFS_state" 

definition "BFS_upd1_step_2 BFS_state \<equiv> 
  neighbourhood_fold (\<lambda>v bfs_state. (bfs_state \<lparr>nexts := nexts bfs_state \<union>\<^sub>G (\<N>\<^sub>G v -\<^sub>G visited BFS_state)\<rparr>))
                     (current BFS_state)
                      BFS_state"

definition "BFS_upd1_step_3 BFS_state \<equiv> BFS_state \<lparr>visited := visited BFS_state \<union>\<^sub>G current BFS_state, current := nexts BFS_state, nexts := \<emptyset>\<^sub>N \<rparr>"

definition "BFS_upd1 BFS_state \<equiv>
(       let
          BFS_state = BFS_upd1_step_1 BFS_state;
          BFS_state = BFS_upd1_step_2 BFS_state;
          BFS_state = BFS_upd1_step_3 BFS_state
        in 
          BFS_state
)" 

lemma invar_BFS_upd1I[invar_holds_intros]:
   "\<lbrakk>invar (\<lambda>_.True) (\<lambda>s. P s \<and> Q s) BFS_upd1_step_1; invar (\<lambda>_.True) (\<lambda>s. P s \<and> Q s) BFS_upd1_step_2; invar P Q  BFS_upd1_step_3\<rbrakk> \<Longrightarrow> invar P Q BFS_upd1"
  by (fastforce elim!: invarE  intro!: invarI simp: BFS_upd1_def)

definition "BFS_ret_1_conds bfs_state \<equiv> (current bfs_state) = \<emptyset>\<^sub>N"

lemma BFS_ret_1_conds[call_cond_elims]:
  "BFS_ret_1_conds bfs_state \<Longrightarrow> 
   \<lbrakk>(current bfs_state) = \<emptyset>\<^sub>N \<Longrightarrow> P\<rbrakk>
   \<Longrightarrow> P"
  by(auto simp: BFS_ret_1_conds_def split: list.splits option.splits if_splits)

lemma BFS_ret_1_condsI[call_cond_intros]:
  "\<lbrakk>current bfs_state = \<emptyset>\<^sub>N\<rbrakk> \<Longrightarrow> BFS_ret_1_conds bfs_state"
  by(auto simp: BFS_ret_1_conds_def split: list.splits option.splits if_splits)

abbreviation "BFS_ret1 dfs_state \<equiv> dfs_state"

lemma BFS_cases:
  assumes "BFS_call_1_conds bfs_state \<Longrightarrow> P"
      "BFS_ret_1_conds bfs_state \<Longrightarrow> P"
  shows "P"
proof-
  have "BFS_call_1_conds bfs_state \<or>
        BFS_ret_1_conds bfs_state"
    by (auto simp add: BFS_call_1_conds_def
                        BFS_ret_1_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms
    by auto
qed

lemma BFS_simps:
  assumes "BFS_dom BFS_state" 
  shows"BFS_call_1_conds BFS_state \<Longrightarrow> BFS BFS_state = BFS (BFS_upd1 BFS_state)"
      "BFS_ret_1_conds BFS_state \<Longrightarrow> BFS BFS_state = BFS_ret1 BFS_state"
  by (auto simp add: BFS.psimps[OF assms]
                     BFS_call_1_conds_def BFS_upd1_def BFS_upd1_step_1_def BFS_upd1_step_2_def BFS_upd1_step_3_def
                     BFS_ret_1_conds_def Let_def
            split: list.splits option.splits if_splits)

lemma BFS_induct: 
  assumes "BFS_dom bfs_state"
  assumes "\<And>bfs_state. \<lbrakk>BFS_dom bfs_state;
                        BFS_call_1_conds bfs_state \<Longrightarrow> P (BFS_upd1 bfs_state)\<rbrakk>
              \<Longrightarrow> P bfs_state"
  shows "P bfs_state"
  apply(rule BFS.pinduct)
  subgoal using assms(1) .
  apply(rule assms(2))
  by (auto simp add: BFS_call_1_conds_def BFS_upd1_def BFS_upd1_step_1_def BFS_upd1_step_2_def BFS_upd1_step_3_def  Let_def
           split: list.splits option.splits if_splits)

definition "invar_1 bfs_state \<equiv> neighb_inv (visited bfs_state) \<and> neighb_inv (current bfs_state) \<and> neighb_inv (nexts bfs_state) \<and> Graph.graph_inv (parents bfs_state)"

lemma invar_1_props[elim]: 
  "invar_1 bfs_state \<Longrightarrow> 
  (\<lbrakk>neighb_inv (visited bfs_state) ; neighb_inv (current bfs_state) ; neighb_inv (nexts bfs_state) ;
    Graph.graph_inv (parents bfs_state)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]: "\<lbrakk>neighb_inv (visited bfs_state); neighb_inv (current bfs_state); neighb_inv (nexts bfs_state); Graph.graph_inv (parents bfs_state)\<rbrakk>  \<Longrightarrow> invar_1 bfs_state"
  by (auto simp: invar_1_def)

lemma invar_1_holds_upd1_step_1[invar_holds_intros]: 
  shows "invar (\<lambda>_. True) (\<lambda> bfs_state. BFS_call_1_conds bfs_state \<and> invar_1 bfs_state) BFS_upd1_step_1"
proof-
  have *: "invar (\<lambda>_. True) (\<lambda>s. BFS_call_1_conds s \<and> invar_1 s) (\<lambda>bfs_state. update_parents v neighb bfs_state)" for v neighb
  proof-
    have "x \<in> t_set neighb \<Longrightarrow> invar (\<lambda>_. True) (\<lambda>s. BFS_call_1_conds s \<and> invar_1 s) (update_parent v x)" for x neighb v
      by(force elim!: call_cond_elims simp: update_parent_def BFS_call_1_conds_def intro!: invar_props_intros invarI)
    thus ?thesis
      by(auto simp: update_parents_def
          intro!: neighbourhood_fold invar_foldI[where fold_fun = neighbourhood_fold])
  qed
  hence "invar (\<lambda>_. True) (\<lambda>s. BFS_call_1_conds s \<and> invar_1 s) (\<lambda>s. BFS_upd1_step_1 s)"
    using neighbourhood_fold
    by(auto simp: BFS_upd1_step_1_def intro!: invar_foldI''[where fold_fun = neighbourhood_fold])
  thus ?thesis
    by auto
qed

lemma invar_1_holds_upd1_step_2[invar_holds_intros]:
  shows "invar (\<lambda>_. True) (\<lambda> bfs_state. BFS_call_1_conds bfs_state \<and> invar_1 bfs_state) BFS_upd1_step_2"
proof-
  have *: "invar (\<lambda>_. True) (\<lambda>s. BFS_call_1_conds s \<and> invar_1 s) (\<lambda> bfs_state. (bfs_state \<lparr>nexts := nexts bfs_state \<union>\<^sub>G neighb\<rparr>))" if "neighb_inv neighb" for neighb
    using that
    by(auto elim!: call_cond_elims simp: BFS_call_1_conds_def intro!: invar_props_intros invarI)
  have "invar (\<lambda>_. True) (\<lambda>s. BFS_call_1_conds s \<and> invar_1 s) (\<lambda>s. BFS_upd1_step_2 s)"
    using neighbourhood_fold Graph.neighbourhood_invars'[OF graph_inv]
    by(auto simp: * BFS_upd1_step_2_def intro!: invar_foldI''[where fold_fun = neighbourhood_fold])
  thus ?thesis
    by auto
qed

lemma invar_1_holds_upd1_step_3[invar_holds_intros]:
  shows "invar (\<lambda>bfs_state. BFS_call_1_conds bfs_state) (\<lambda>bfs_state. invar_1 bfs_state) BFS_upd1_step_3"
  by(auto elim!: call_cond_elims simp: BFS_upd1_step_3_def BFS_call_1_conds_def intro!: invar_props_intros invarI)

lemma invar_1_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_1 bfs_state"
  shows "invar_1 (BFS_upd1 bfs_state)"
proof-
  have "invar (\<lambda>bfs_state. BFS_call_1_conds bfs_state) (\<lambda>bfs_state. invar_1 bfs_state) BFS_upd1"
    by(auto intro!: invar_BFS_upd1I invar_holds_intros)
  thus ?thesis
    using assms
    by(auto elim!: invarE)
qed

lemma invar_1_holds_4[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_1 bfs_state\<rbrakk> \<Longrightarrow> invar_1 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_1_holds: 
   assumes "BFS_dom bfs_state" "invar_1 bfs_state"
   shows "invar_1 (BFS bfs_state)"
  using assms(2)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

definition "invar_2 bfs_state \<equiv> Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs G"

lemma invar_2_props[elim]: 
  "invar_2 bfs_state \<Longrightarrow> 
  (\<lbrakk>Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs G\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]:
   "\<lbrakk>Graph.digraph_abs (parents bfs_state) \<subseteq> Graph.digraph_abs G\<rbrakk>  \<Longrightarrow> invar_2 bfs_state"
  by (auto simp: invar_2_def)

lemma invar_2_holds_upd1_step_1[invar_holds_intros]: 
  shows "invar (\<lambda>_. True) (\<lambda> bfs_state. BFS_call_1_conds bfs_state \<and> invar_1 bfs_state \<and> invar_2 bfs_state) BFS_upd1_step_1"
proof-
  have *: "invar (\<lambda>_. True) (\<lambda>s. BFS_call_1_conds s \<and> invar_1 s \<and> invar_2 s) (\<lambda>bfs_state. update_parents v neighb bfs_state)" 
    if "t_set neighb \<subseteq> t_set (\<N>\<^sub>G v)" for v neighb
  proof-
    have "x \<in> t_set neighb \<Longrightarrow> invar (\<lambda>_. True) (\<lambda>s. BFS_call_1_conds s \<and> invar_1 s \<and> invar_2 s) (update_parent v x)"
      if "t_set neighb \<subseteq> t_set (\<N>\<^sub>G v)" for x neighb v
      using that
      by(fastforce elim!: call_cond_elims simp: update_parent_def BFS_call_1_conds_def intro!: invar_props_intros invarI)
    thus ?thesis
      using that
      by(auto simp: update_parents_def
          intro!: neighbourhood_fold invar_foldI[where fold_fun = neighbourhood_fold])
  qed
  hence "invar (\<lambda>_. True) (\<lambda>s. BFS_call_1_conds s \<and> invar_1 s \<and> invar_2 s) (\<lambda>s. BFS_upd1_step_1 s)"
    using neighbourhood_fold
    by (auto simp: BFS_upd1_step_1_def intro!: invar_foldI''[where fold_fun = neighbourhood_fold])
  thus ?thesis
    by auto
qed

lemma invar_2_holds_upd1_step_2[invar_holds_intros]:
  shows "invar (\<lambda>_. True) (\<lambda> bfs_state. BFS_call_1_conds bfs_state \<and> invar_1 bfs_state \<and> invar_2 bfs_state) BFS_upd1_step_2"
proof-
  have *: "invar (\<lambda>_. True) (\<lambda>s. BFS_call_1_conds s \<and> invar_1 s \<and> invar_2 s) (\<lambda> bfs_state. (bfs_state \<lparr>nexts := nexts bfs_state \<union>\<^sub>G neighb\<rparr>))" if "neighb_inv neighb" for neighb
    using that
    by(fastforce elim!: call_cond_elims simp: BFS_call_1_conds_def intro!: invar_props_intros invarI)
  hence "invar (\<lambda>_. True) (\<lambda>s. BFS_call_1_conds s \<and> invar_1 s \<and> invar_2 s) (\<lambda>s. BFS_upd1_step_2 s)"
    using neighbourhood_fold Graph.neighbourhood_invars'[OF graph_inv]
    by (auto simp: BFS_upd1_step_2_def intro!: invar_foldI''[where fold_fun = neighbourhood_fold] *)
  thus ?thesis
    by auto
qed

lemma invar_2_holds_upd1_step_3[invar_holds_intros]:
  shows "invar (\<lambda>bfs_state. BFS_call_1_conds bfs_state) (\<lambda>bfs_state. invar_1 bfs_state \<and> invar_2 bfs_state) BFS_upd1_step_3"
  by(fastforce elim!: call_cond_elims simp: BFS_upd1_step_3_def BFS_call_1_conds_def intro!: invar_props_intros invarI)

lemma invar_2_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_1 bfs_state" "invar_2 bfs_state"
  shows "invar_2 (BFS_upd1 bfs_state)"
proof-
  have "invar (\<lambda>bfs_state. BFS_call_1_conds bfs_state) (\<lambda>bfs_state. invar_1 bfs_state \<and> invar_2 bfs_state) BFS_upd1"
    by(auto intro!: invar_BFS_upd1I invar_holds_intros)
  thus ?thesis
    using assms
    by(auto elim!: invarE)
qed

lemma invar_2_holds_4[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_1 bfs_state\<rbrakk> \<Longrightarrow> invar_1 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_2_holds: 
   assumes "BFS_dom bfs_state" "invar_1 bfs_state" "invar_2 bfs_state"
   shows "invar_2 (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed

definition "frontier bfs_state \<equiv> (\<Union> {t_set (\<N>\<^sub>G v) | v . v \<in> t_set (current bfs_state)}) \<union> t_set (current bfs_state) \<union> t_set (nexts bfs_state)"

definition "invar_3 bfs_state \<equiv> 
  (\<forall>v \<in> (dVs (Graph.digraph_abs (parents bfs_state))) - frontier bfs_state.
    \<forall>u. (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u) \<longrightarrow> 
      ((v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents bfs_state)\<^esub> u) 
       \<or> (\<exists>w\<in>t_set (current bfs_state) \<union> t_set (nexts bfs_state). (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents bfs_state)\<^esub> w) \<and> (w \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u))))"

lemma invar_3_props[elim]: 
  "invar_3 bfs_state \<Longrightarrow> 
  \<lbrakk>\<lbrakk>\<lbrakk>v \<in> (dVs (Graph.digraph_abs (parents bfs_state))) - frontier bfs_state; (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u)\<rbrakk> \<Longrightarrow>
          (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents bfs_state)\<^esub> u)\<rbrakk>
           \<Longrightarrow> P;
   \<lbrakk>\<lbrakk>v \<in> (dVs (Graph.digraph_abs (parents bfs_state))) - frontier bfs_state; (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u)\<rbrakk> \<Longrightarrow>
           (\<exists>w\<in>t_set (current bfs_state) \<union> t_set (nexts bfs_state). (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents bfs_state)\<^esub> w) \<and> (w \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u))\<rbrakk>
           \<Longrightarrow> P\<rbrakk>
     \<Longrightarrow> P"
  by (auto simp: invar_3_def)

lemma invar_3_intro[invar_props_intros]:
   "(\<And>v u. \<lbrakk>v \<in> (dVs (Graph.digraph_abs (parents bfs_state))) - frontier bfs_state; (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u)\<rbrakk> \<Longrightarrow>
       (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents bfs_state)\<^esub> u) \<or>
       (\<exists>w\<in>t_set (current bfs_state) \<union> t_set (nexts bfs_state). (v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents bfs_state)\<^esub> w) \<and> (w \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u)))
    \<Longrightarrow> invar_3 bfs_state"
  by (auto simp: invar_3_def)
                      

lemma invar_3_holds_upd1_step_1[invar_holds_intros]: 
  shows "invar (\<lambda>_. True) (\<lambda> bfs_state. BFS_call_1_conds bfs_state \<and> invar_1 bfs_state \<and> invar_3 bfs_state) BFS_upd1_step_1"
proof-
  have *: "invar (\<lambda>_. True ) (\<lambda>s. (v \<in> t_set (current s)) \<and> BFS_call_1_conds s \<and> invar_1 s \<and> invar_3 s) (\<lambda>bfs_state. update_parents v neighb bfs_state)" 
    if "t_set neighb \<subseteq> t_set (\<N>\<^sub>G v)" for v neighb
  proof-
    have "invar (\<lambda>_. True) (\<lambda>s. (v \<in> t_set (current s)) \<and> BFS_call_1_conds s \<and> invar_1 s \<and> invar_3 s) (update_parent v x)"
      if "x \<in> t_set neighb" "t_set neighb \<subseteq> t_set (\<N>\<^sub>G v)" for x
    proof(intro invarI conjI, goal_cases)
      case (1 s)
      then show ?case
      using that
      by (auto elim!: invar_1_props call_cond_elims simp: update_parent_def BFS_call_1_conds_def intro!: invar_props_intros invarI)
    next
      case (2 s)
      then show ?case 
      using that
      by (auto elim!: invar_1_props call_cond_elims simp: update_parent_def BFS_call_1_conds_def intro!: invar_props_intros invarI)
    next
      case (3 s)
      then show ?case 
      using that
      by (auto elim!: invar_1_props call_cond_elims simp: update_parent_def BFS_call_1_conds_def intro!: invar_props_intros invarI)
    next
      case (4 s)
      thus ?case
      proof(intro invar_props_intros, goal_cases)
        case (1 v' u)
        hence "invar_1 s" "v\<in>t_set (current s)"
          by auto
        have "v' \<noteq> x"
          using \<open>v\<in>t_set (current s)\<close> \<open>x \<in> t_set neighb\<close> \<open>t_set neighb \<subseteq> t_set (\<N>\<^sub>G v)\<close> "1"(3)
          by (auto simp: frontier_def update_parent_def)
        have "invar_3 s"
          using 1
          by auto
        with 1 show ?case
        proof(elim invar_3_props[where v = v' and u = u], goal_cases)
          case invar_3_case_1: 1
          have "v' \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents (update_parent v x s))\<^esub> u"
            if "v' \<in> dVs (Graph.digraph_abs (parents s))"
          proof- 
            from invar_3_case_1(3,4,5) have "v' \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents s)\<^esub> u"
              using that
              by (auto intro!: invar_3_case_1(5) elim!: invar_1_props simp: update_parent_def frontier_def)
            thus ?thesis
              using that \<open>invar_1 s\<close>
              by (force simp: update_parent_def intro: reachable_subset)
          qed
          moreover have "v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents (update_parent v x s))\<^esub> v"
            using \<open>invar_1 s\<close>
            by (fastforce simp: update_parent_def)
          ultimately show ?case
            using invar_3_case_1(1,2,3,4) \<open>invar_1 s\<close> \<open>v' \<noteq> x\<close>
            apply (clarsimp simp: update_parent_def elim!: invar_1_props)
            by blast
        next
          case invar_3_case_2: 2
          have "\<exists>w\<in>t_set (current s) \<union> t_set (nexts s). v' \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents (update_parent v x s))\<^esub> w \<and> w \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u"
            if "v' \<in> dVs (Graph.digraph_abs (parents s))"
          proof- 
            from invar_3_case_2(3,4,5)
            have "\<exists>w\<in>t_set (current s) \<union> t_set (nexts s). v' \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents s)\<^esub> w\<and>w \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u"
              using that
              by (auto intro!: invar_3_case_2(5) elim!: invar_1_props simp: update_parent_def frontier_def)
            then obtain w where "w\<in>t_set (current s) \<union> t_set (nexts s)" "v' \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents s)\<^esub> w" "w \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs G\<^esub> u"
              using that
              by (auto intro!: invar_3_case_2(5) elim!: invar_1_props simp: update_parent_def frontier_def)
            thus ?thesis
              using that \<open>invar_1 s\<close>
              by (force simp: update_parent_def intro: reachable_subset intro!: bexI[where x = w])
          qed
          moreover have "v \<rightarrow>\<^sup>*\<^bsub>Graph.digraph_abs (parents (update_parent v x s))\<^esub> v"
            using \<open>invar_1 s\<close>
            by (fastforce simp: update_parent_def)
          ultimately show ?case
            using invar_3_case_2(1,2,3,4) \<open>invar_1 s\<close> \<open>v' \<noteq> x\<close>
            apply (clarsimp simp: update_parent_def elim!: invar_1_props)
            by blast
        qed
      qed
    qed
    thus ?thesis
      using that
      by(auto simp: update_parents_def    
          intro!: neighbourhood_fold invar_foldI[where fold_fun = neighbourhood_fold])
  qed
  hence "invar (\<lambda>_. True) (\<lambda>s. BFS_call_1_conds s \<and> invar_1 s \<and> invar_3 s) (\<lambda>s. BFS_upd1_step_1 s)"
    using neighbourhood_fold 
    apply (auto simp: BFS_upd1_step_1_def invar_def intro!: invarI )
    apply(auto intro!: invar_foldI'[where fold_fun = neighbourhood_fold and I = BFS_call_1_conds])
    subgoal sorry
    subgoal sorry
    apply(rule ])
    apply simp
    apply (auto simp add: invar_def *[where ?v8 = v and ?neighb8 = "\<N>\<^sub>G v -\<^sub>G visited s" for v s, simplified invar_def subset_refl] intro!: )

    by auto
  thus ?thesis
    by auto
qed

lemma False
    apply (smt (verit, ccfv_threshold) BFS.update_parent_def BFS_axioms BFS_call_1_conds_def BFS_state.ext_inject BFS_state.surjective BFS_state.update_convs(1) invar_foldI' update_parents_def)


lemma invar_3_holds_upd1_step_2[invar_holds_intros]:
  shows "invar (\<lambda>_. True) (\<lambda> bfs_state. BFS_call_1_conds bfs_state \<and> invar_1 bfs_state \<and> invar_3 bfs_state) BFS_upd1_step_2"
proof-
  have *: "invar (\<lambda>_. True) (\<lambda>s. BFS_call_1_conds s \<and> invar_1 s \<and> invar_3 s) (\<lambda> bfs_state. (bfs_state \<lparr>nexts := nexts bfs_state \<union>\<^sub>G neighb\<rparr>))" 
    if "neighb_inv neighb" for neighb
    using that
    by (auto elim!: inv ar_1_props invar_2_props invar_3_props call_cond_elims simp: BFS_call_1_conds_def intro!: invar_props_intros invarI)

  hence "invar (\<lambda>_. True) (\<lambda>s. BFS_call_1_conds s \<and> invar_1 s \<and> invar_3 s) (\<lambda>s. BFS_upd1_step_2 s)"
    using neighbourhood_fold Graph.neighbourhood_invars'[OF graph_inv]
    by (auto simp: BFS_upd1_step_2_def intro!: invar_foldI''[where fold_fun = neighbourhood_fold] *)
  thus ?thesis
    by auto
qed

lemma invar_3_holds_upd1_step_3[invar_holds_intros]:
  shows "invar (\<lambda>bfs_state. BFS_call_1_conds bfs_state) (\<lambda>bfs_state. invar_1 bfs_state \<and> invar_2 bfs_state \<and> invar_3 bfs_state) BFS_upd1_step_3"
  by(auto elim!: inva r_1_props invar_2_props invar_3_props call_cond_elims simp: BFS_upd1_step_3_def BFS_call_1_conds_def intro!: invar_props_intros invarI)

lemma invar_2_holds_upd1[invar_holds_intros]:
  assumes "BFS_call_1_conds bfs_state" "invar_1 bfs_state" "invar_2 bfs_state"
  shows "invar_2 (BFS_upd1 bfs_state)"
proof-
  have "invar (\<lambda>bfs_state. BFS_call_1_conds bfs_state) (\<lambda>bfs_state. invar_1 bfs_state \<and> invar_2 bfs_state) BFS_upd1"
    by(auto intro!: invar_BFS_upd1I invar_holds_intros)
  thus ?thesis
    using assms
    by(auto elim!: invarE)
qed

lemma invar_2_holds_4[invar_holds_intros]:
  "\<lbrakk>BFS_ret_1_conds bfs_state; invar_1 bfs_state\<rbrakk> \<Longrightarrow> invar_1 (BFS_ret1 bfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_2_holds: 
   assumes "BFS_dom bfs_state" "invar_1 bfs_state" "invar_2 bfs_state"
   shows "invar_2 (BFS bfs_state)"
  using assms(2-)
proof(induction rule: BFS_induct[OF assms(1)])
  case IH: (1 bfs_state)
  show ?case
    apply(rule BFS_cases[where bfs_state = bfs_state])
    by (auto intro!: IH(2-) intro: invar_holds_intros  simp: BFS_simps[OF IH(1)])
qed



definition "invar_2 dfs_state = (Vwalk.vwalk Graph.digraph_abs (rev (stack dfs_state)))"

lemma invar_2_props[dest!]: "invar_2 dfs_state \<Longrightarrow> (Vwalk.vwalk Graph.digraph_abs (rev (stack dfs_state)))"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]: "Vwalk.vwalk Graph.digraph_abs (rev (stack dfs_state)) \<Longrightarrow> invar_2 dfs_state"
  by (auto simp: invar_2_def)

lemma invar_2_holds_1[invar_holds_intros]:
  assumes "DFS_call_1_conds dfs_state" "invar_1 dfs_state" "invar_2 dfs_state"
  shows "invar_2 (DFS_upd1 dfs_state)"
    using assms
    by (fastforce simp: DFS_upd1_def elim!: call_cond_elims
                intro!: invar_props_intros Vwalk.vwalk_append2)

lemma invar_2_holds_2[invar_holds_intros]: "\<lbrakk>DFS_call_2_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (DFS_upd2 dfs_state)"
  by (auto simp: DFS_upd2_def dest!: append_vwalk_pref intro!: invar_props_intros elim: call_cond_elims)

lemma invar_2_holds_4[invar_holds_intros]: "\<lbrakk>DFS_ret_1_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (DFS_ret1 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_2_holds_5[invar_holds_intros]: "\<lbrakk>DFS_ret_2_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (DFS_ret2 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_2_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state" "invar_2 dfs_state"
   shows "invar_2 (DFS dfs_state)"
  using assms(2-3)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_simps[OF IH(1)])
qed

\<comment> \<open>Example of funciton package bad ind ppcl?\<close>

definition "invar_3 dfs_state = (\<forall>v \<in> t_set (visited dfs_state). (\<nexists>p. Vwalk.vwalk_bet Graph.digraph_abs v p t) )"

lemma invar_3_props[elim!]: "invar_3 dfs_state \<Longrightarrow> (\<lbrakk>\<And>v p. v \<in> t_set (visited dfs_state) \<Longrightarrow> \<not> (Vwalk.vwalk_bet Graph.digraph_abs v p t)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P "
  by (auto simp: invar_3_def)

lemma invar_3_intro[invar_props_intros]: "\<lbrakk>\<And>v p. v \<in> t_set (visited dfs_state) \<Longrightarrow>  \<not> (Vwalk.vwalk_bet Graph.digraph_abs v p t)\<rbrakk> \<Longrightarrow> invar_3 dfs_state"
  by (auto simp: invar_3_def)

lemma invar_3_holds_1[invar_holds_intros]:
  "\<lbrakk>DFS_call_1_conds dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> invar_3 (DFS_upd1 dfs_state)"
  by (auto simp: DFS_upd1_def dest!: append_vwalk_pref intro!: invar_props_intros)

lemma invar_3_holds_2[invar_holds_intros]: "\<lbrakk>DFS_call_2_conds dfs_state; invar_1 dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> invar_3 (DFS_upd2 dfs_state)"
  by (force simp: DFS_upd2_def dest!: append_vwalk_pref intro!: invar_props_intros elim!: DFS_call_2_conds)

lemma invar_3_holds_4[invar_holds_intros]: "\<lbrakk>DFS_ret_1_conds dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> invar_3 (DFS_ret1 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_3_holds_5[invar_holds_intros]: "\<lbrakk>DFS_ret_2_conds dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> invar_3 (DFS_ret2 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_3_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state" "invar_3 dfs_state"
   shows "invar_3 (DFS dfs_state)" 
   using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_simps[OF IH(1)])
qed

abbreviation "seen_verts dfs_state \<equiv> (set (stack dfs_state) \<union> t_set (visited dfs_state))"

definition "state_rel_1 dfs_state_1 dfs_state_2 
              \<equiv> seen_verts dfs_state_1 \<subseteq> seen_verts dfs_state_2"

lemma state_rel_1_props[elim!]: "state_rel_1 dfs_state_1 dfs_state_2 \<Longrightarrow>
                                  (seen_verts dfs_state_1 \<subseteq> seen_verts dfs_state_2 \<Longrightarrow> P) \<Longrightarrow> P "
  by (auto simp: state_rel_1_def)

lemma state_rel_1_intro[state_rel_intros]: "\<lbrakk>seen_verts dfs_state_1 \<subseteq> seen_verts dfs_state_2\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state_1 dfs_state_2"
  by (auto simp: state_rel_1_def)

lemma state_rel_1_trans:
  "\<lbrakk>state_rel_1 dfs_state_1 dfs_state_2; state_rel_1 dfs_state_2 dfs_state_3\<rbrakk> \<Longrightarrow>
   state_rel_1 dfs_state_1 dfs_state_3"
  by (auto intro!: state_rel_intros)

lemma state_rel_1_holds_1[state_rel_holds_intros]:
  "\<lbrakk>DFS_call_1_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (DFS_upd1 dfs_state)"
  by (auto simp: DFS_upd1_def intro!: state_rel_intros)

lemma state_rel_1_holds_2[state_rel_holds_intros]:
  "\<lbrakk>DFS_call_2_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (DFS_upd2 dfs_state)"
  by (auto simp: DFS_upd2_def intro!: state_rel_intros elim: call_cond_elims)

lemma state_rel_1_holds_4[state_rel_holds_intros]:
  "\<lbrakk>DFS_ret_1_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (DFS_ret1 dfs_state)"
  by (auto simp: intro!: state_rel_intros)

lemma state_rel_1_holds_5[state_rel_holds_intros]:
  "\<lbrakk>DFS_ret_2_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (DFS_ret2 dfs_state)"
  by (auto simp: intro!: state_rel_intros)

lemma state_rel_1_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state"
   shows "state_rel_1 dfs_state (DFS dfs_state)" 
   using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro: state_rel_1_trans invar_holds_intros state_rel_holds_intros intro!: IH(2-) simp: DFS_simps[OF IH(1)])
qed

definition "state_rel_2 dfs_state_1 dfs_state_2 
              \<equiv> (\<forall>v \<in> set (stack dfs_state_1). ((\<exists>p. Vwalk.vwalk_bet Graph.digraph_abs v p t) \<or> v = t) \<longrightarrow> v \<in> set (stack dfs_state_2))"

lemma state_rel_2_props[elim!]: "state_rel_2 dfs_state_1 dfs_state_2 \<Longrightarrow>
                                  \<lbrakk>\<lbrakk>\<And>v.\<lbrakk>v \<in> set (stack dfs_state_1); (\<exists>p. Vwalk.vwalk_bet Graph.digraph_abs v p t) \<or> v = t\<rbrakk>
                                    \<Longrightarrow> v \<in> set (stack dfs_state_2)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P "
  by (auto simp: state_rel_2_def)

lemma state_rel_2_intro[state_rel_intros]: "\<lbrakk>\<And>v. \<lbrakk>v \<in> set (stack dfs_state_1); (\<exists>p. Vwalk.vwalk_bet Graph.digraph_abs v p t) \<or> v = t\<rbrakk>
                                    \<Longrightarrow> v \<in> set (stack dfs_state_2)\<rbrakk> \<Longrightarrow> state_rel_2 dfs_state_1 dfs_state_2"
  by (auto simp: state_rel_2_def)

lemma state_rel_2_trans:
  "\<lbrakk>state_rel_2 dfs_state_1 dfs_state_2; state_rel_2 dfs_state_2 dfs_state_3\<rbrakk> \<Longrightarrow>
   state_rel_2 dfs_state_1 dfs_state_3"
  by (auto intro!: state_rel_intros)

lemma state_rel_2_holds_1[state_rel_holds_intros]:
  "\<lbrakk>DFS_call_1_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_2 dfs_state (DFS_upd1 dfs_state)"
  by (auto simp: DFS_upd1_def intro!: state_rel_intros)

lemma state_rel_2_holds_2[state_rel_holds_intros]:
  "\<lbrakk>DFS_call_2_conds dfs_state; invar_1 dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> state_rel_2 dfs_state (DFS_upd2 dfs_state)"
  by (force simp: DFS_upd2_def intro!: state_rel_intros elim!: DFS_call_2_conds)

lemma state_rel_2_holds_4[state_rel_holds_intros]:
  "\<lbrakk>DFS_ret_1_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_2 dfs_state (DFS_ret1 dfs_state)"
  by (auto simp: intro!: state_rel_intros)

lemma state_rel_2_holds_5[state_rel_holds_intros]:
  "\<lbrakk>DFS_ret_2_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_2 dfs_state (DFS_ret2 dfs_state)"
  by (auto simp: intro!: state_rel_intros)

lemma state_rel_2_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state" "invar_3 dfs_state"
   shows "state_rel_2 dfs_state (DFS dfs_state)" 
   using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro: state_rel_2_trans invar_holds_intros state_rel_holds_intros intro!: IH(2-) simp: DFS_simps[OF IH(1)])
qed

lemma DFS_ret_1[ret_holds_intros]: "DFS_ret_1_conds (dfs_state) \<Longrightarrow> DFS_ret_1_conds (DFS_ret1 dfs_state)"
  by (auto simp: elim!: call_cond_elims intro!: call_cond_intros)

lemma ret1_holds:
   assumes "DFS_dom dfs_state" "return (DFS dfs_state) = NotReachable"
   shows "DFS_ret_1_conds (DFS dfs_state)" 
   using assms(2-)
proof(induction  rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    using IH(4)                                                                
    by (auto intro: ret_holds_intros intro!: IH(2-) simp: DFS_simps[OF IH(1)])
qed

lemma DFS_ret_2[ret_holds_intros]: "DFS_ret_2_conds (dfs_state) \<Longrightarrow> DFS_ret_2_conds (DFS_ret2 dfs_state)"
  by (auto simp: elim!: call_cond_elims intro!: call_cond_intros)

lemma ret2_holds:
   assumes "DFS_dom dfs_state" "return (DFS dfs_state) = Reachable"
   shows "DFS_ret_2_conds (DFS dfs_state)" 
   using assms(2-)
proof(induction  rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    using IH(4)                                                                
    by (auto intro: ret_holds_intros intro!: IH(2-) simp: DFS_simps[OF IH(1)])
qed

end
                                                               
end
