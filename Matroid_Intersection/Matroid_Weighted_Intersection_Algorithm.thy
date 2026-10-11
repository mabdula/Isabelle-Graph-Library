theory Matroid_Weighted_Intersection_Algorithm
  imports Matroid_Weighted_Intersection_Path_Loop Matroid_Intersection_Algorithm
begin

section \<open>Weighted Matroid Intersection Algorithm\<close>

text \<open>Frank's weighted matroid intersection algorithm (Korte--Vygen, Section 13.7) with the tight
auxiliary graph built explicitly. The loop itself is the one of
@{theory Matroid_Intersection.Matroid_Weighted_Intersection_Path_Loop}. Here it is instantiated
twice, as in @{theory Matroid_Intersection.Matroid_Intersection_Algorithm}:
\<^item> the \<open>plain\<close> version probes each single swap \<open>X - {x} + y\<close> via the independence oracle;
\<^item> the \<open>circuit\<close> version reads off the whole fundamental circuit at once.

Per iteration a context is built: the endpoint sets \<open>S\<close>/\<open>T\<close> from the unweighted auxiliary graph,
their maximum-weight elements \<open>Sbar\<close>/\<open>Tbar\<close>, the tight graph \<open>Gbar\<close> and the set reachable in it.
The tight path, the reachable set and \<open>\<epsilon>\<close> are read off this context. The split weights are values of
an abstract weight-map type \<open>'cmap\<close>, accessed through \<open>c_lookup\<close>, \<open>c_shift\<close>, \<open>c_zero\<close>,
\<open>weight_Max\<close> and \<open>restrict_to_max\<close>.\<close>

text \<open>The context of one iteration.\<close>

record ('mset, 'cmap, 'vset, 'adjmap) weighted_aux_ctx =
  actx_X  :: 'mset
  actx_c1 :: 'cmap
  actx_c2 :: 'cmap
  actx_SX :: 'vset
  actx_TX :: 'vset
  actx_Sb :: 'vset
  actx_Tb :: 'vset
  actx_G  :: 'adjmap
  actx_R  :: 'vset

subsection \<open>Executable specification locale (both variants)\<close>

text \<open>Extends the unweighted spec locale, thereby reusing every graph/set ADT operation and the
unweighted \<open>compute_graph\<close>/\<open>compute_graph_circuit\<close>/\<open>augment\<close> definitions, and adds the weight-map
ADT together with the weight-specific oracles.\<close>

locale weighted_intersection_spec =
  unweighted_intersection_spec where insert = "insert :: 'a \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and lookup = "lookup :: 'adjmap \<Rightarrow> 'a \<Rightarrow> 'vset option"
    and set_insert = "set_insert :: 'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and complement = "complement :: 'mset \<Rightarrow> 'mset_red"
  for insert lookup set_insert complement +
  fixes c_lookup :: "'cmap \<Rightarrow> 'a \<Rightarrow> real"
    and c_invar :: "'cmap \<Rightarrow> bool"
    and c_shift :: "'vset \<Rightarrow> real \<Rightarrow> 'cmap \<Rightarrow> 'cmap"
    and c_zero :: "'cmap"
    and weight_Max :: "'vset \<Rightarrow> 'cmap \<Rightarrow> real"
    and restrict_to_max :: "'vset \<Rightarrow> 'cmap \<Rightarrow> 'vset"
    and reach_set :: "'vset \<Rightarrow> 'adjmap \<Rightarrow> 'vset"
    \<comment> \<open>the two set-folds with a running-\<open>min\<close> accumulator, used to \<^emph>\<open>compute\<close> \<open>\<epsilon>\<close>; they are
      \<open>inner_fold\<close>/\<open>outer_fold\<close> at the accumulator type \<^typ>\<open>real option\<close> (\<^const>\<open>None\<close> = \<open>\<infinity>\<close>)\<close>
    and eps_fold :: "'mset \<Rightarrow> ('a \<Rightarrow> real option \<Rightarrow> real option) \<Rightarrow> real option \<Rightarrow> real option"
    and eps_fold_red :: "'mset_red \<Rightarrow> ('a \<Rightarrow> real option \<Rightarrow> real option) \<Rightarrow> real option \<Rightarrow> real option"
begin

subsubsection \<open>Tight auxiliary graph -- plain version\<close>

text \<open>Like the unweighted \<open>treat1\<close>/\<open>treat2\<close>, but an arc is kept only when its endpoints have equal
weight (looked up through \<open>c_lookup\<close>), so the resulting graph abstracts to the tight subgraph
\<open>Gbar\<close>.\<close>

definition "treat1_tight y X c init_map =
  inner_fold X (\<lambda> x current_map. if weak_orcl1 y (set_delete x X) \<and> c_lookup c x = c_lookup c y
                                 then graph.add_edge current_map x y
                                 else current_map) init_map"

definition "treat2_tight y X c init_map =
  inner_fold X (\<lambda> x current_map. if weak_orcl2 y (set_delete x X) \<and> c_lookup c y = c_lookup c x
                                 then graph.add_edge current_map y x
                                 else current_map) init_map"

definition "compute_tight_graph X c1 c2 E_without_X =
  snd (snd (outer_fold E_without_X (\<lambda> y (SX, TX, current_map).
     let (SX, TX, current_map) = (if weak_orcl1 y X then (SX, TX, current_map)
                                  else (SX, TX, treat1_tight y X c1 current_map));
         (SX, TX, current_map) = (if weak_orcl2 y X then (SX, TX, current_map)
                                  else (SX, TX, treat2_tight y X c2 current_map))
     in (SX, TX, current_map)) (vset_empty, vset_empty, empty)))"

subsubsection \<open>Tight auxiliary graph -- circuit version\<close>

definition "treat1_circuit_tight y C c init_map =
  inner_fold_circuit C (\<lambda> x current_map. if c_lookup c x = c_lookup c y
                                          then graph.add_edge current_map x y
                                          else current_map) init_map"

definition "treat2_circuit_tight y C c init_map =
  inner_fold_circuit C (\<lambda> x current_map. if c_lookup c y = c_lookup c x
                                          then graph.add_edge current_map y x
                                          else current_map) init_map"

definition "compute_tight_graph_circuit X c1 c2 E_without_X =
  snd (snd (outer_fold E_without_X (\<lambda> y (SX, TX, current_map).
     let (SX, TX, current_map) = (if weak_orcl1 y X then (SX, TX, current_map)
                                  else (SX, TX, treat1_circuit_tight y (circuit1 y X) c1 current_map));
         (SX, TX, current_map) = (if weak_orcl2 y X then (SX, TX, current_map)
                                  else (SX, TX, treat2_circuit_tight y (circuit2 y X) c2 current_map))
     in (SX, TX, current_map)) (vset_empty, vset_empty, empty)))"

subsubsection \<open>Computing \<open>\<epsilon>\<close> (naive, following Frank)\<close>

text \<open>\<open>\<epsilon> = min(\<epsilon>\<^sub>1,\<epsilon>\<^sub>2,\<epsilon>\<^sub>3,\<epsilon>\<^sub>4)\<close> as a \<^typ>\<open>real option\<close> (\<^const>\<open>None\<close> = \<open>\<infinity>\<close>), computed by folding the
complement \<open>carrier - X\<close>: each \<open>y\<close> contributes its \<open>S\<close>/\<open>T\<close> endpoint gap (\<open>\<epsilon>\<^sub>3\<close>/\<open>\<epsilon>\<^sub>4\<close>) and, when \<open>y\<close> is not
addable, the gaps of its arcs crossing the boundary of \<open>R\<close> (\<open>\<epsilon>\<^sub>1\<close>/\<open>\<epsilon>\<^sub>2\<close>).\<close>

text \<open>Circuit variant: the arcs of \<open>y\<close> are read off its fundamental circuits \<open>circuit1/2 y X\<close>.\<close>
definition "compute_eps_circuit X m1 m2 R c1 c2 =
  eps_fold_red (complement X) (\<lambda> y acc.
    let acc = (if weak_orcl1 y X
               then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
               else (if y \<in>\<^sub>G R then acc
                     else eps_fold_red (circuit1 y X)
                            (\<lambda> x acc. if x \<in>\<^sub>G R then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc));
        acc = (if weak_orcl2 y X
               then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
               else (if y \<in>\<^sub>G R
                     then eps_fold_red (circuit2 y X)
                            (\<lambda> x acc. if x \<notin>\<^sub>G R then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
                     else acc))
    in acc) None"

text \<open>Plain variant: the arcs of \<open>y\<close> are found by probing \<open>weak_orcl\<close> over each \<open>x \<in> X\<close>.\<close>
definition "compute_eps X m1 m2 R c1 c2 =
  eps_fold_red (complement X) (\<lambda> y acc.
    let acc = (if weak_orcl1 y X
               then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
               else (if y \<in>\<^sub>G R then acc
                     else eps_fold X
                            (\<lambda> x acc. if weak_orcl1 y (set_delete x X) \<and> x \<in>\<^sub>G R
                                      then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc));
        acc = (if weak_orcl2 y X
               then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
               else (if y \<in>\<^sub>G R
                     then eps_fold X
                            (\<lambda> x acc. if weak_orcl2 y (set_delete x X) \<and> x \<notin>\<^sub>G R
                                      then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
                     else acc))
    in acc) None"

subsubsection \<open>The context and the two loops\<close>

text \<open>The context stores the endpoint sets, their maximum-weight elements, the tight graph and the set
reachable in it. The two variants differ only in how the auxiliary graphs and \<open>\<epsilon>\<close> are computed.\<close>

definition "aux_tight_ctx X c1 c2 =
  (case compute_graph X (complement X) of (SX, TX, G) \<Rightarrow>
     let Sb = restrict_to_max SX c1; Tb = restrict_to_max TX c2;
         Gt = compute_tight_graph X c1 c2 (complement X)
     in \<lparr>actx_X = X, actx_c1 = c1, actx_c2 = c2, actx_SX = SX, actx_TX = TX,
         actx_Sb = Sb, actx_Tb = Tb, actx_G = Gt, actx_R = reach_set Sb Gt\<rparr>)"

definition "aux_tight_ctx_circuit X c1 c2 =
  (case compute_graph_circuit X (complement X) of (SX, TX, G) \<Rightarrow>
     let Sb = restrict_to_max SX c1; Tb = restrict_to_max TX c2;
         Gt = compute_tight_graph_circuit X c1 c2 (complement X)
     in \<lparr>actx_X = X, actx_c1 = c1, actx_c2 = c2, actx_SX = SX, actx_TX = TX,
         actx_Sb = Sb, actx_Tb = Tb, actx_G = Gt, actx_R = reach_set Sb Gt\<rparr>)"

definition "aux_tight_path K = find_path (actx_Sb K) (actx_Tb K) (actx_G K)"

definition "aux_reach K = actx_R K"

definition "aux_eps K =
  compute_eps (actx_X K) (weight_Max (actx_SX K) (actx_c1 K)) (weight_Max (actx_TX K) (actx_c2 K))
    (actx_R K) (actx_c1 K) (actx_c2 K)"

definition "aux_eps_circuit K =
  compute_eps_circuit (actx_X K) (weight_Max (actx_SX K) (actx_c1 K))
    (weight_Max (actx_TX K) (actx_c2 K)) (actx_R K) (actx_c1 K) (actx_c2 K)"

sublocale standard: weighted_intersection_path_loop_spec set_insert set_delete to_set set_invar
  set_empty c_shift c_zero c_lookup aux_tight_ctx aux_tight_path aux_reach aux_eps .

definition "weighted_matroid_intersection \<equiv> standard.weighted_matroid_intersection"

definition "weighted_matroid_intersection_impl \<equiv> standard.weighted_matroid_intersection_impl"

definition "weighted_initial_state \<equiv> standard.weighted_initial_state"

lemmas weighted_matroid_intersection_impl_simps =
  standard.weighted_matroid_intersection_impl.simps[folded weighted_matroid_intersection_impl_def]

sublocale circuit: weighted_intersection_path_loop_spec set_insert set_delete to_set set_invar
  set_empty c_shift c_zero c_lookup aux_tight_ctx_circuit aux_tight_path aux_reach aux_eps_circuit .

definition "weighted_matroid_intersection_circuit \<equiv> circuit.weighted_matroid_intersection"

definition "weighted_matroid_intersection_circuit_impl \<equiv> circuit.weighted_matroid_intersection_impl"

lemmas weighted_matroid_intersection_circuit_impl_simps =
  circuit.weighted_matroid_intersection_impl.simps[folded weighted_matroid_intersection_circuit_impl_def]

lemmas [code] = treat1_tight_def treat2_tight_def compute_tight_graph_def
  treat1_circuit_tight_def treat2_circuit_tight_def compute_tight_graph_circuit_def
  compute_eps_def compute_eps_circuit_def aux_tight_ctx_def aux_tight_ctx_circuit_def
  aux_tight_path_def aux_reach_def aux_eps_def aux_eps_circuit_def
  weighted_matroid_intersection_impl_simps weighted_matroid_intersection_circuit_impl_simps

end

subsection \<open>Proof locale (both variants)\<close>

text \<open>Merges the unweighted proof locale (which already provides the \<open>double_matroid\<close> structure and
all the graph/set ADT axioms) with the weighted executable spec, and adds the specifications of the
weight-map ADT and the weight oracles.  Every weight specification is phrased through the abstraction
\<open>c_lookup\<close>.  The weighted snapshot lemmas of \<open>Matroid_Weighted_Intersection\<close> (in particular
\<open>weighted_intersection_graph.augment_tight_path\<close>) become available by interpreting the locale
\<open>weighted_intersection_graph\<close> at the current split.\<close>

locale weighted_intersection =
  weighted_intersection_spec where insert = "insert :: 'a \<Rightarrow> 'vset \<Rightarrow> 'vset"
    and lookup = "lookup :: 'adjmap \<Rightarrow> 'a \<Rightarrow> 'vset option"
    and set_insert = "set_insert :: 'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and find_path = "find_path :: 'vset \<Rightarrow> 'vset \<Rightarrow> 'adjmap \<Rightarrow> 'a list option"
    and t_set = vset
    and complement = "complement :: 'mset \<Rightarrow> 'mset_red"
    + double_matroid where carrier = "carrier :: 'a set"
  for insert lookup set_insert find_path carrier vset complement +
  fixes to_set_red :: "'mset_red \<Rightarrow> 'a set"
    and set_invar_red :: "'mset_red \<Rightarrow> bool"
  assumes set_insert: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar (set_insert x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_insert x S) = Set.insert x (to_set S)"
  assumes set_delete: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar (set_delete x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_delete x S) = (to_set S) - {x}"
  assumes set_empty: "set_invar set_empty" "to_set set_empty = {}"
  assumes weak_orcl1:
    "\<And> X x. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; x \<in> carrier; x \<notin> to_set X; indep1 (to_set X)\<rbrakk>
       \<Longrightarrow> weak_orcl1 x X \<longleftrightarrow> indep1 (Set.insert x (to_set X))"
  assumes weak_orcl2:
    "\<And> X x. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; x \<in> carrier; x \<notin> to_set X; indep2 (to_set X)\<rbrakk>
       \<Longrightarrow> weak_orcl2 x X \<longleftrightarrow> indep2 (Set.insert x (to_set X))"
  assumes inner_fold:
     "\<And> X f G. set_invar X \<Longrightarrow> \<exists> xs. set xs = to_set X \<and> inner_fold X f G = foldr f xs G"
  assumes inner_fold_circuit:
     "\<And> X f G. set_invar_red X
      \<Longrightarrow> \<exists> xs. set xs = to_set_red X \<and> inner_fold_circuit X f G = foldr f xs G"
  assumes outer_fold:
     "\<And> X f trip. set_invar_red X \<Longrightarrow> \<exists> xs. set xs = to_set_red X
                                           \<and> outer_fold X f trip = foldr f xs trip"
  assumes find_path:
    "\<And> G S T. \<lbrakk>graph.graph_inv G; graph.finite_graph G; graph.finite_vsets G; vset_inv S;
               vset_inv T; vset S \<subseteq> carrier; vset T \<subseteq> carrier; dVs (graph.digraph_abs G) \<subseteq> carrier\<rbrakk>
      \<Longrightarrow> find_path S T G = None \<longleftrightarrow>
           (\<nexists> p u v. (vwalk_bet (graph.digraph_abs G) u p v \<or> (p = [u] \<and> u = v)) \<and>
                       u \<in> vset S \<and> v \<in> vset T)"
    "\<And> G S T p. \<lbrakk>graph.graph_inv G; graph.finite_graph G; graph.finite_vsets G; vset_inv S;
                 vset_inv T; vset S \<subseteq> carrier; vset T \<subseteq> carrier;
                 dVs (graph.digraph_abs G) \<subseteq> carrier; find_path S T G = Some p\<rbrakk>
      \<Longrightarrow> \<exists> u v. (vwalk_bet (graph.digraph_abs G) u p v \<or> (p = [u] \<and> u = v))
                         \<and> u \<in> vset S \<and> v \<in> vset T \<and>
             (\<nexists> p'. (vwalk_bet (graph.digraph_abs G) u p' v \<or> (p' = [u] \<and> u = v))
                         \<and> length p' < length p)"
  assumes complement: "\<And> S. \<lbrakk>set_invar S; to_set S  \<subseteq> carrier\<rbrakk> \<Longrightarrow> set_invar_red (complement S)"
    "\<And> S. \<lbrakk>set_invar S; to_set S  \<subseteq> carrier\<rbrakk> \<Longrightarrow> to_set_red (complement S) = carrier - to_set S"
  assumes circuit1:
    "\<And> X y. \<lbrakk>set_invar X; indep1 (to_set X); to_set X \<subseteq> carrier; y \<in> carrier;
             \<not> indep1 (Set.insert y (to_set X))\<rbrakk>
        \<Longrightarrow> to_set_red (circuit1 y X) = matroid1.the_circuit (Set.insert y (to_set X)) - {y}"
    "\<And> X y. \<lbrakk>set_invar X; indep1 (to_set X); to_set X \<subseteq> carrier; y \<in> carrier;
              \<not> indep1 (Set.insert y (to_set X))\<rbrakk>
        \<Longrightarrow> set_invar_red (circuit1 y X)"
  assumes circuit2:
    "\<And> X y. \<lbrakk>set_invar X; indep2 (to_set X); to_set X \<subseteq> carrier; y \<in> carrier;
              \<not> indep2 (Set.insert y (to_set X))\<rbrakk>
        \<Longrightarrow> to_set_red (circuit2 y X) = matroid2.the_circuit (Set.insert y (to_set X)) - {y}"
    "\<And> X y. \<lbrakk>set_invar X; indep2 (to_set X); to_set X \<subseteq> carrier; y \<in> carrier;
              \<not> indep2 (Set.insert y (to_set X))\<rbrakk>
        \<Longrightarrow> set_invar_red (circuit2 y X)"
  \<comment> \<open>the weight-map ADT: \<open>c_lookup\<close> is both the executable lookup and the abstraction to \<^typ>\<open>'a \<Rightarrow> real\<close>\<close>
  assumes c_zero: "c_invar c_zero" "c_lookup c_zero = (\<lambda> _. 0)"
  assumes c_shift:
    "\<And> R e c. \<lbrakk>c_invar c; vset_inv R\<rbrakk> \<Longrightarrow> c_invar (c_shift R e c)"
    "\<And> R e c. \<lbrakk>c_invar c; vset_inv R\<rbrakk>
       \<Longrightarrow> c_lookup (c_shift R e c) = (\<lambda> x. if x \<in> vset R then c_lookup c x + e else c_lookup c x)"
  assumes weight_Max:
    "\<And> V c. \<lbrakk>c_invar c; vset_inv V; vset V \<noteq> {}\<rbrakk> \<Longrightarrow> weight_Max V c = Max (c_lookup c ` vset V)"
  assumes restrict_to_max:
    "\<And> V c. \<lbrakk>c_invar c; vset_inv V\<rbrakk> \<Longrightarrow> vset_inv (restrict_to_max V c)"
    "\<And> V c. \<lbrakk>c_invar c; vset_inv V\<rbrakk>
       \<Longrightarrow> vset (restrict_to_max V c) = {y \<in> vset V. c_lookup c y = Max (c_lookup c ` vset V)}"
  assumes reach_set:
    "\<And> Src G. \<lbrakk>graph.graph_inv G; vset_inv Src\<rbrakk> \<Longrightarrow> vset_inv (reach_set Src G)"
    "\<And> Src G. \<lbrakk>graph.graph_inv G; vset_inv Src\<rbrakk> \<Longrightarrow>
       vset (reach_set Src G) =
         {v. \<exists> u \<in> vset Src. u = v \<or> (\<exists> p. vwalk_bet [G]\<^sub>g u p v)}"
  assumes eps_fold:
    "\<And> X f a. set_invar X \<Longrightarrow> \<exists> xs. set xs = to_set X \<and> eps_fold X f a = foldr f xs a"
  assumes eps_fold_red:
    "\<And> X f a. set_invar_red X \<Longrightarrow> \<exists> xs. set xs = to_set_red X \<and> eps_fold_red X f a = foldr f xs a"
begin


subsubsection \<open>Reusing the unweighted development\<close>

text \<open>Since the weighted proof locale carries exactly the assumptions of the unweighted one, it is an
instance of it; interpreting it makes every unweighted lemma (\<open>compute_graph_meaning\<close>,
\<open>effect_of_augmentation\<close>, \<open>if_no_augpath_then_maximum\<close>, ...) available under the \<open>U\<close> prefix.\<close>

sublocale U: unweighted_intersection
  by unfold_locales
    (fact set_insert set_delete set_empty weak_orcl1 weak_orcl2 inner_fold
       inner_fold_circuit outer_fold find_path complement circuit1 circuit2)+

subsubsection \<open>The tight auxiliary graph abstracts to \<open>Gbar\<close>\<close>

text \<open>Analogue of the unweighted @{thm [source] U.treat1_correct}: the tight treat step adds exactly
the tight \<open>A1\<close>-arcs.\<close>

lemma treat1_tight_correct:
  assumes "indep1 (to_set X)" "set_invar X" "y \<in> carrier - to_set X" "graph.graph_inv G"
  shows "graph.graph_inv (treat1_tight y X c G)"
    "graph.digraph_abs (treat1_tight y X c G) = graph.digraph_abs G \<union>
       {(x, y) | x. x \<in> to_set X \<and> indep1 (to_set X - {x} \<union> {y}) \<and> c_lookup c x = c_lookup c y}"
    "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat1_tight y X c G)"
    "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat1_tight y X c G)"
proof-
  define f where "f = (\<lambda> x current_map. if weak_orcl1 y (set_delete x X) \<and> c_lookup c x = c_lookup c y
                                         then graph.add_edge current_map x y
                                         else current_map)"
  obtain xs where xs_prop: "set xs = to_set X" True "inner_fold X f G = foldr f xs G"
    using inner_fold[OF assms(2), of f G] by auto
  have treat_is: "treat1_tight y X c G = foldr f xs G"
    by(unfold xs_prop(3)[symmetric])(simp add: treat1_tight_def f_def)
  have claim1:"graph.graph_inv (foldr f xs G)" for xs
    by(induction xs)(auto split: if_split simp add: f_def assms(4))
  thus "graph.graph_inv (treat1_tight y X c G)"
    by (simp add: treat_is)
  have X_in_Carrier: "to_set X \<subseteq> carrier "
    by (simp add: assms(1) matroid1.indep_subset_carrier)
  have independence_is:"a \<in> to_set X \<Longrightarrow>
          weak_orcl1 y (set_delete a X) = indep1 (Set.insert y (to_set X - {a}))" for a
    using X_in_Carrier  assms(1) matroid1.indep_in_subset set_delete(2)[OF  assms(2)]
      matroid1.indep_in_carrier assms(3)
    by (subst weak_orcl1)
      (fastforce simp add: weak_orcl1 assms(3) assms(2) set_delete(1) subset_eq)+
  have "set xs \<subseteq> to_set X  \<Longrightarrow>graph.digraph_abs (foldr f xs G) = graph.digraph_abs G \<union>
       {(x, y) | x. x \<in> set xs \<and> indep1 (to_set X - {x} \<union> {y}) \<and> c_lookup c x = c_lookup c y}"
    using xs_prop(2)
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is graph.digraph_abs_insert[OF claim1])
  thus "graph.digraph_abs (treat1_tight y X c G) = graph.digraph_abs G \<union>
       {(x, y) |x. x \<in> to_set X \<and> indep1 (to_set X - {x} \<union> {y}) \<and> c_lookup c x = c_lookup c y}"
    by(simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set X \<Longrightarrow> graph.finite_graph G \<Longrightarrow> graph.finite_graph (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is claim1 graph.finite_graph_add_edge)
  thus "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat1_tight y X c G)"
    by (simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set X \<Longrightarrow> graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is claim1 graph.finite_vsets_add_edge)
  thus "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat1_tight y X c G)"
    by (simp add: treat_is xs_prop(1))
qed

lemma treat2_tight_correct:
  assumes "indep2 (to_set X)" "set_invar X" "y \<in> carrier - to_set X" "graph.graph_inv G"
  shows "graph.graph_inv (treat2_tight y X c G)"
    "graph.digraph_abs (treat2_tight y X c G) = graph.digraph_abs G \<union>
       {(y, x) | x. x \<in> to_set X \<and> indep2 (to_set X - {x} \<union> {y}) \<and> c_lookup c y = c_lookup c x}"
    "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat2_tight y X c G)"
    "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat2_tight y X c G)"
proof-
  define f where "f = (\<lambda> x current_map. if weak_orcl2 y (set_delete x X) \<and> c_lookup c y = c_lookup c x
                                         then graph.add_edge current_map y x
                                         else current_map)"
  obtain xs where xs_prop: "set xs = to_set X" True "inner_fold X f G = foldr f xs G"
    using inner_fold[OF assms(2), of f G] by auto
  have treat_is: "treat2_tight y X c G = foldr f xs G"
    by(unfold xs_prop(3)[symmetric])(simp add: treat2_tight_def f_def)
  have claim1:"graph.graph_inv (foldr f xs G)" for xs
    by(induction xs)(auto split: if_split simp add: f_def assms(4))
  thus "graph.graph_inv (treat2_tight y X c G)"
    by (simp add: treat_is)
  have X_in_Carrier: "to_set X \<subseteq> carrier "
    by (simp add: assms(1) matroid2.indep_subset_carrier)
  have independence_is:"a \<in> to_set X \<Longrightarrow>
          weak_orcl2 y (set_delete a X) = indep2 (Set.insert y (to_set X - {a}))" for a
    using X_in_Carrier  assms(1) matroid2.indep_in_subset set_delete(2)[OF  assms(2)]
      matroid2.indep_in_carrier assms(3)
    by (subst weak_orcl2)
      (fastforce simp add: weak_orcl2 assms(3) assms(2) set_delete(1) subset_eq)+
  have "set xs \<subseteq> to_set X  \<Longrightarrow>graph.digraph_abs (foldr f xs G) = graph.digraph_abs G \<union>
       {(y, x) | x. x \<in> set xs \<and> indep2 (to_set X - {x} \<union> {y}) \<and> c_lookup c y = c_lookup c x}"
    using xs_prop(2)
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is graph.digraph_abs_insert[OF claim1])
  thus "graph.digraph_abs (treat2_tight y X c G) = graph.digraph_abs G \<union>
       {(y, x) |x. x \<in> to_set X \<and> indep2 (to_set X - {x} \<union> {y}) \<and> c_lookup c y = c_lookup c x}"
    by(simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set X \<Longrightarrow> graph.finite_graph G \<Longrightarrow> graph.finite_graph (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is claim1 graph.finite_graph_add_edge)
  thus "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat2_tight y X c G)"
    by (simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set X \<Longrightarrow> graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: independence_is claim1 graph.finite_vsets_add_edge)
  thus "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat2_tight y X c G)"
    by (simp add: treat_is xs_prop(1))
qed

text \<open>The circuit-oracle counterparts of @{thm [source] treat1_tight_correct}/@{thm [source]
treat2_tight_correct}: verbatim copies of the unweighted @{thm [source] U.treat1_circuit_correct}/
@{thm [source] U.treat2_circuit_correct} with the tightness guard \<open>c_lookup c x = c_lookup c y\<close>.\<close>

lemma treat1_circuit_tight_correct:
  assumes "set_invar_red C" "graph.graph_inv G"
  shows "graph.graph_inv (treat1_circuit_tight y C c G)"
    "graph.digraph_abs (treat1_circuit_tight y C c G) = graph.digraph_abs G \<union>
                       {(x, y) | x. x \<in> to_set_red C \<and> c_lookup c x = c_lookup c y}"
    "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat1_circuit_tight y C c G)"
    "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat1_circuit_tight y C c G)"
proof-
  define f where "f = (\<lambda> x current_map.  if c_lookup c x = c_lookup c y
                                          then graph.add_edge current_map x y else current_map)"
  obtain xs where xs_prop: "set xs = to_set_red C" True "inner_fold_circuit C f G = foldr f xs G"
    using inner_fold_circuit[OF assms(1), of f G] by auto
  have treat_is: "treat1_circuit_tight y C c G = foldr f xs G"
    by(unfold xs_prop(3)[symmetric])(simp add: treat1_circuit_tight_def f_def)
  have claim1:"graph.graph_inv (foldr f xs G)" for xs
    by(induction xs)(auto split: if_split simp add: f_def assms(2))
  thus "graph.graph_inv (treat1_circuit_tight y C c G)"
    by (simp add: treat_is)
  have "set xs \<subseteq> to_set_red C  \<Longrightarrow> graph.digraph_abs (foldr f xs G) = graph.digraph_abs G \<union>
                       {(x, y) | x. x \<in> set xs \<and> c_lookup c x = c_lookup c y}"
    using xs_prop(2)
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: graph.digraph_abs_insert[OF claim1])
  thus "[treat1_circuit_tight y C c G]\<^sub>g = [G]\<^sub>g \<union> {(x, y) |x. x \<in> to_set_red C \<and> c_lookup c x = c_lookup c y}"
    by(simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set_red C \<Longrightarrow> graph.finite_graph G \<Longrightarrow> graph.finite_graph (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: claim1 graph.finite_graph_add_edge)
  thus "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat1_circuit_tight y C c G)"
    by (simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set_red C \<Longrightarrow> graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: claim1 graph.finite_vsets_add_edge)
  thus "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat1_circuit_tight y C c G)"
    by (simp add: treat_is xs_prop(1))
qed

lemma treat2_circuit_tight_correct:
  assumes "set_invar_red C" "graph.graph_inv G"
  shows "graph.graph_inv (treat2_circuit_tight y C c G)"
    "graph.digraph_abs (treat2_circuit_tight y C c G) = graph.digraph_abs G \<union>
                       {(y, x) | x. x \<in> to_set_red C \<and> c_lookup c y = c_lookup c x}"
    "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat2_circuit_tight y C c G)"
    "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat2_circuit_tight y C c G)"
proof-
  define f where "f = (\<lambda> x current_map. if c_lookup c y = c_lookup c x
                                          then graph.add_edge current_map y x else current_map)"
  obtain xs where xs_prop: "set xs = to_set_red C" True "inner_fold_circuit C f G = foldr f xs G"
    using inner_fold_circuit[OF assms(1), of f G] by auto
  have treat_is: "treat2_circuit_tight y C c G = foldr f xs G"
    by(unfold xs_prop(3)[symmetric])(simp add: treat2_circuit_tight_def f_def)
  have claim1:"graph.graph_inv (foldr f xs G)" for xs
    by(induction xs)(auto split: if_split simp add: f_def assms(2))
  thus "graph.graph_inv (treat2_circuit_tight y C c G)"
    by (simp add: treat_is)
  have "set xs \<subseteq> to_set_red C  \<Longrightarrow> graph.digraph_abs (foldr f xs G) = graph.digraph_abs G \<union>
                       {(y, x) | x. x \<in> set xs \<and> c_lookup c y = c_lookup c x}"
    using xs_prop(2)
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: graph.digraph_abs_insert[OF claim1])
  thus "[treat2_circuit_tight y C c G]\<^sub>g = [G]\<^sub>g \<union> {(y, x) |x. x \<in> to_set_red C \<and> c_lookup c y = c_lookup c x}"
    by(simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set_red C \<Longrightarrow> graph.finite_graph G \<Longrightarrow> graph.finite_graph (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: claim1 graph.finite_graph_add_edge)
  thus "graph.finite_graph G \<Longrightarrow> graph.finite_graph (treat2_circuit_tight y C c G)"
    by (simp add: treat_is xs_prop(1))
  have "set xs \<subseteq> to_set_red C \<Longrightarrow> graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (foldr f xs G)"
    apply(induction xs, simp)
    apply(subst foldr_Cons, subst o_apply)
    apply(subst f_def)
    by(auto simp add: claim1 graph.finite_vsets_add_edge)
  thus "graph.finite_vsets G \<Longrightarrow> graph.finite_vsets (treat2_circuit_tight y C c G)"
    by (simp add: treat_is xs_prop(1))
qed

text \<open>Analogue of the unweighted @{thm [source] U.compute_graph_correct} for the tight builder (the
\<open>S\<close>/\<open>T\<close> components are irrelevant here, so only the graph is described): it abstracts to the tight
arcs of \<open>A1\<close>/\<open>A2\<close>.\<close>

lemma compute_tight_graph_correct:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X"
    "set_invar_red E_without_X" "to_set_red E_without_X \<subseteq> carrier - to_set X"
  shows "graph.graph_inv (compute_tight_graph X c1 c2 E_without_X)"
    and "graph.digraph_abs (compute_tight_graph X c1 c2 E_without_X) =
       {(x, y) |x y. y \<in> to_set_red E_without_X \<and> \<not> indep1 (Set.insert y (to_set X))
                     \<and> x \<in> to_set X \<and> indep1 (to_set X - {x} \<union> {y}) \<and> c_lookup c1 x = c_lookup c1 y}
       \<union> {(y, x) |x y. y \<in> to_set_red E_without_X \<and> \<not> indep2 (Set.insert y (to_set X))
                     \<and> x \<in> to_set X \<and> indep2 (to_set X - {x} \<union> {y}) \<and> c_lookup c2 y = c_lookup c2 x}"
    (is ?last_thesis)
    and "graph.finite_graph (compute_tight_graph X c1 c2 E_without_X)"
    and "graph.finite_vsets (compute_tight_graph X c1 c2 E_without_X)"
proof-
  define f where "f = (\<lambda> y (SX::'vset, TX::'vset, current_map).
            let (SX, TX, current_map) = (if weak_orcl1 y X then (SX, TX, current_map)
                                         else (SX, TX, treat1_tight y X c1 current_map));
                (SX, TX, current_map) = (if weak_orcl2 y X then (SX, TX, current_map)
                                         else (SX, TX, treat2_tight y X c2 current_map))
            in (SX, TX, current_map))"
  obtain xs where xs_prop: "set xs = to_set_red E_without_X" True
    "outer_fold E_without_X f (vset_empty, vset_empty, empty) = foldr f xs (vset_empty, vset_empty, empty)"
    using outer_fold[OF assms(4), of f "(vset_empty, vset_empty, empty)"] by auto
  have resulting_map_is: "compute_tight_graph X c1 c2 E_without_X =
                            snd (snd (foldr f xs (vset_empty, vset_empty, empty)))"
    using xs_prop(3)[symmetric] by(auto simp add: f_def compute_tight_graph_def)
  have graph_inv_resulting_map:
    "set xs \<subseteq> carrier - to_set X \<Longrightarrow>
       graph.graph_inv (snd (snd (foldr f xs (vset_empty, vset_empty, empty))))" for xs
    by(induction xs)
      (auto split: prod.split
        intro!: treat1_tight_correct(1)[OF assms(1,3)] treat2_tight_correct(1)[OF assms(2,3)]
        simp add: f_def graph.graph_inv_empty)
  thus "graph.graph_inv (compute_tight_graph X c1 c2 E_without_X)"
    by (simp add: assms(5) resulting_map_is xs_prop(1))
  have X_in_carrier:"to_set X \<subseteq> carrier"
    by (simp add: assms(1) matroid1.indep_subset_carrier)
  have "set xs \<subseteq> carrier - to_set X \<Longrightarrow>
     graph.digraph_abs (snd (snd (foldr f xs (vset_empty, vset_empty, empty)))) =
       {(x, y) |x y. y \<in> set xs \<and> \<not> indep1 (Set.insert y (to_set X)) \<and> x \<in> to_set X
                     \<and> indep1 (to_set X - {x} \<union> {y}) \<and> c_lookup c1 x = c_lookup c1 y}
     \<union> {(y, x) |x y. y \<in> set xs \<and> \<not> indep2 (Set.insert y (to_set X)) \<and> x \<in> to_set X
                     \<and> indep2 (to_set X - {x} \<union> {y}) \<and> c_lookup c2 y = c_lookup c2 x}"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _  _ assms(2)]
          by auto
      next
        case 2
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (clarsimp, subst treat2_tight_correct(2)[OF assms(2,3)])force+
      next
        case 3
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (clarsimp, subst treat1_tight_correct(2)[OF assms(1,3)])force+
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_tight_correct(2)[OF assms(2,3)], simp)
           apply(rule treat1_tight_correct(1)[OF assms(1,3)])
          using graph_inv_resulting_map[of xs]  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (subst treat1_tight_correct(2)[OF assms(1,3)]|force)+
      qed
    qed
  qed (auto simp add:  graph.digraph_abs_empty)
  thus ?last_thesis
    using assms(5) resulting_map_is xs_prop(1) by presburger
  have "set xs  \<subseteq> carrier -to_set X \<Longrightarrow>
       graph.finite_graph (snd (snd (foldr f xs (vset_empty, vset_empty, empty))))"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by auto
      next
        case 2
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (clarsimp, subst treat2_tight_correct(3)[OF assms(2,3)])force+
      next
        case 3
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (clarsimp, subst treat1_tight_correct(3)[OF assms(1,3)])force+
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_tight_correct(3)[OF assms(2,3)], simp)
            apply(rule treat1_tight_correct(1)[OF assms(1,3)])
          using graph_inv_resulting_map[of xs]  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (subst treat1_tight_correct(3)[OF assms(1,3)]|force)+
      qed
    qed
  qed (auto simp add: graph.adjmap.map_empty graph.finite_graph_def)
  thus "graph.finite_graph (compute_tight_graph X c1 c2 E_without_X)"
    using  resulting_map_is xs_prop(1)  assms(5) by auto
  have "set xs  \<subseteq> carrier -to_set X \<Longrightarrow>
       graph.finite_vsets (snd (snd (foldr f xs (vset_empty, vset_empty, empty))))"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by auto
      next
        case 2
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (clarsimp, subst treat2_tight_correct(4)[OF assms(2,3)])force+
      next
        case 3
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (clarsimp, subst treat1_tight_correct(4)[OF assms(1,3)])force+
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_tight_correct(4)[OF assms(2,3)], simp)
            apply(rule treat1_tight_correct(1)[OF assms(1,3)])
          using graph_inv_resulting_map[of xs]  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (subst treat1_tight_correct(4)[OF assms(1,3)]|force)+
      qed
    qed
  qed (auto simp add: graph.adjmap.map_empty graph.finite_graph_def)
  thus "graph.finite_vsets (compute_tight_graph X c1 c2 E_without_X)"
    using assms(5) resulting_map_is xs_prop(1) by force
qed

text \<open>The tight builder abstracts to Frank's tight subgraph \<open>Gbar\<close> (with the abstract split weights
\<open>c_lookup c1\<close>/\<open>c_lookup c2\<close>) --- the analogue of the unweighted @{thm [source] U.compute_graph_meaning}(3).\<close>

lemma compute_tight_graph_meaning:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X"
    "set_invar_red E_without_X" "to_set_red E_without_X = carrier - to_set X"
  shows "graph.digraph_abs (compute_tight_graph X c1 c2 E_without_X)
           = weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  show ?thesis
    using matroid2.indep_subset_carrier[OF assms(2)]
    by(subst compute_tight_graph_correct(2)[OF assms(1-4) _])
      (auto simp add: matroid1.circuit_extensional[OF assms(1)] insert_Diff_if
        matroid2.circuit_extensional[OF assms(2)] A1_def A2_def assms(5)
        W.Gbar_def W.Abar1_def W.Abar2_def)
qed

text \<open>Circuit-oracle twin of @{thm [source] compute_tight_graph_correct}: mirror of the unweighted
@{thm [source] U.compute_graph_circuit_correct} (again only the graph, no \<open>S\<close>/\<open>T\<close>), with the tightness
guard added to the two arc set-builders.\<close>

lemma compute_tight_graph_circuit_correct:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X"
    "set_invar_red E_without_X" "to_set_red E_without_X \<subseteq> carrier - to_set X"
  shows "graph.graph_inv (compute_tight_graph_circuit X c1 c2 E_without_X)"
    and "graph.digraph_abs (compute_tight_graph_circuit X c1 c2 E_without_X) =
                {(x, y) |x y. y \<in> to_set_red E_without_X
                       \<and> x \<in> matroid1.the_circuit (Set.insert y (to_set X)) - {y}
                       \<and> c_lookup c1 x = c_lookup c1 y}
                \<union> {(y, x) |x y. y \<in> to_set_red E_without_X
                       \<and> x \<in> matroid2.the_circuit (Set.insert y (to_set X)) - {y}
                       \<and> c_lookup c2 y = c_lookup c2 x}"
    (is ?last_thesis)
    and "graph.finite_graph (compute_tight_graph_circuit X c1 c2 E_without_X)"
    and "graph.finite_vsets (compute_tight_graph_circuit X c1 c2 E_without_X)"
proof-
  define f where "f = (\<lambda> y (SX::'vset, TX::'vset, current_map). (
            let (SX, TX, current_map) = (if weak_orcl1 y X then (SX, TX, current_map)
                                         else (SX, TX, treat1_circuit_tight y (circuit1 y X) c1 current_map));
                (SX, TX, current_map) = (if weak_orcl2 y X then (SX, TX, current_map)
                                         else (SX, TX, treat2_circuit_tight y (circuit2 y X) c2 current_map))
            in (SX, TX, current_map)))"
  obtain xs where xs_prop: "set xs = to_set_red E_without_X" True
    "outer_fold E_without_X f (vset_empty, vset_empty, empty) = foldr f xs (vset_empty, vset_empty, empty)"
    using outer_fold[OF assms(4), of f "(vset_empty, vset_empty, empty)"] by auto
  have resulting_map_is: "compute_tight_graph_circuit X c1 c2 E_without_X =
                            snd (snd (foldr f xs (vset_empty, vset_empty, empty)))"
    using xs_prop(3)[symmetric] by(auto simp add: f_def compute_tight_graph_circuit_def)
  have X_in_carrier:"to_set X \<subseteq> carrier"
    by (simp add: assms(1) matroid1.indep_subset_carrier)
  have graph_inv_resulting_map:
    "set xs \<subseteq> carrier - to_set X \<Longrightarrow>
       graph.graph_inv (snd (snd (foldr f xs (vset_empty, vset_empty, empty))))" for xs
    by(induction xs)
      (auto split: prod.split intro!: treat2_circuit_tight_correct(1) treat1_circuit_tight_correct(1)
        simp add: X_in_carrier assms(1) assms(2) assms(3) circuit2(2) weak_orcl2 circuit1(2) weak_orcl1
        f_def graph.graph_inv_empty)
  thus "graph.graph_inv (compute_tight_graph_circuit X c1 c2 E_without_X)"
    by (simp add: assms(5) resulting_map_is xs_prop(1))
  have "set xs \<subseteq> carrier -to_set X \<Longrightarrow>
     graph.digraph_abs (snd (snd (foldr f xs (vset_empty, vset_empty, empty)))) =
       {(x, y) |x y. y \<in> set xs \<and> x \<in> matroid1.the_circuit (Set.insert y (to_set X)) - {y}
                     \<and> c_lookup c1 x = c_lookup c1 y}
     \<union> {(y, x) |x y. y \<in> set xs \<and> x \<in> matroid2.the_circuit (Set.insert y (to_set X)) - {y}
                     \<and> c_lookup c2 y = c_lookup c2 x}"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            matroid1.independent_empty_circuit  matroid2.independent_empty_circuit
          by auto
      next
        case 2
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            matroid1.independent_empty_circuit  matroid2.independent_empty_circuit
            X_in_carrier assms(2) assms(3) circuit2(2) assms(1) circuit2(1)
          apply (clarsimp,  subst treat2_circuit_tight_correct(2))
            apply (force)
           apply (metis (no_types, lifting) snd_conv)
          by(auto split: prod.split )
      next
        case 3
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            matroid1.independent_empty_circuit  matroid2.independent_empty_circuit
            X_in_carrier assms(2) assms(3) circuit1(2) assms(1) circuit1(1)
          apply (clarsimp,  subst treat1_circuit_tight_correct(2))
            apply (force)
           apply (metis (no_types, lifting) snd_conv)
          by(auto split: prod.split )
      next
        case 4
        then show ?case
          using Cons.prems X_in_carrier assms(2) assms(3) circuit2(2) weak_orcl2
          apply(clarsimp, subst treat2_circuit_tight_correct(2), simp)
           apply(rule treat1_circuit_tight_correct(1))
          using assms(1) circuit1(2)  graph_inv_resulting_map[of xs]
            Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by (subst treat1_circuit_tight_correct(2)| force simp add: circuit1(1) circuit2(1) assms(1,2,3))+
      qed
    qed
  qed (auto simp add:  graph.digraph_abs_empty)
  thus ?last_thesis
    using assms(5) resulting_map_is xs_prop(1) by presburger
  have "set xs  \<subseteq> carrier -to_set X \<Longrightarrow>
       graph.finite_graph (snd (snd (foldr f xs (vset_empty, vset_empty, empty))))"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by auto
      next
        case 2
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            X_in_carrier assms(2) assms(3) circuit2(2)
          apply(clarsimp, subst treat2_circuit_tight_correct(3))
             apply (force)
            apply (metis (no_types, lifting) snd_conv)
          by(auto split: prod.split )
      next
        case 3
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            X_in_carrier assms(1) assms(3) circuit1(2)
          apply (clarsimp, subst treat1_circuit_tight_correct(3))
             apply (force)
            apply (metis (no_types, lifting) snd_conv)
          by(auto split: prod.split )
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_circuit_tight_correct(3))
          using   X_in_carrier assms(1) assms(3) circuit1(2)   weak_orcl1[OF  assms(3) X_in_carrier _ _ assms(1)]
            graph_inv_resulting_map Cons.IH
          by (fastforce intro!: treat1_circuit_tight_correct(1,3) circuit1(2)
              simp add: X_in_carrier assms(2) assms(3) circuit2(2) weak_orcl2)+
      qed
    qed
  qed (auto simp add: graph.adjmap.map_empty graph.finite_graph_def)
  thus "graph.finite_graph (compute_tight_graph_circuit X c1 c2 E_without_X)"
    using  resulting_map_is xs_prop(1)  assms(5) by auto
  have "set xs  \<subseteq> carrier -to_set X \<Longrightarrow>
       graph.finite_vsets (snd (snd (foldr f xs (vset_empty, vset_empty, empty))))"
  proof(induction xs)
    case (Cons a xs)
    show ?case
    proof(subst foldr_Cons, subst o_apply, subst f_def, unfold Let_def,
        (split prod.split, rule, rule, rule)+, goal_cases)
      case (1 x1 x2 x1a x2a x1b x2b x1c x2c x1d x2d x1e x2e)
      then show ?case
      proof(cases "weak_orcl1 a X", all \<open>cases "weak_orcl2 a X"\<close>, goal_cases)
        case 1
        then show ?case
          using Cons  weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
          by auto
      next
        case 2
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            X_in_carrier assms(2) assms(3) circuit2(2)
          apply(clarsimp, subst treat2_circuit_tight_correct(4))
             apply (force)
            apply (metis (no_types, lifting) snd_conv)
          by(auto split: prod.split )
      next
        case 3
        then show ?case
          using  graph_inv_resulting_map  Cons weak_orcl1[OF assms(3) X_in_carrier _ _ assms(1)]
            weak_orcl2[OF assms(3) X_in_carrier _ _ assms(2)]
            X_in_carrier assms(1) assms(3) circuit1(2)
          apply (clarsimp, subst treat1_circuit_tight_correct(4))
             apply (force)
            apply (metis (no_types, lifting) snd_conv)
          by(auto split: prod.split )
      next
        case 4
        then show ?case
          using Cons.prems
          apply(clarsimp, subst treat2_circuit_tight_correct(4))
          using   X_in_carrier assms(1) assms(3) circuit1(2)   weak_orcl1[OF  assms(3) X_in_carrier _ _ assms(1)]
            graph_inv_resulting_map Cons.IH
          by (fastforce intro!: treat1_circuit_tight_correct(1,4) circuit1(2)
              simp add: X_in_carrier assms(2) assms(3) circuit2(2) weak_orcl2)+
      qed
    qed
  qed (auto simp add: graph.adjmap.map_empty graph.finite_graph_def)
  thus "graph.finite_vsets (compute_tight_graph_circuit X c1 c2 E_without_X)"
    using  resulting_map_is xs_prop(1)  assms(5) by force
qed

lemma compute_tight_graph_circuit_meaning:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X"
    "set_invar_red E_without_X" "to_set_red E_without_X = carrier - to_set X"
  shows "graph.digraph_abs (compute_tight_graph_circuit X c1 c2 E_without_X)
           = weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  show ?thesis
    using matroid2.indep_subset_carrier[OF assms(2)]
    by(subst compute_tight_graph_circuit_correct(2)[OF assms(1-4) _])
      (auto simp add: matroid1.circuit_extensional[OF assms(1)] insert_Diff_if
        matroid2.circuit_extensional[OF assms(2)] A1_def A2_def assms(5)
        W.Gbar_def W.Abar1_def W.Abar2_def)
qed

text \<open>Restricting the (weight-agnostic) endpoint sets @{term "S (to_set X)"}/@{term "T (to_set X)"}
to their maximum-weight elements yields Frank's tight endpoints \<open>Sbar\<close>/\<open>Tbar\<close>.\<close>

lemma restrict_to_max_Sbar:
  assumes "c_invar c1" "vset_inv SX" "vset SX = S (to_set X)"
  shows "vset (restrict_to_max SX c1) =
           {y \<in> S (to_set X). c_lookup c1 y = Max (c_lookup c1 ` S (to_set X))}"
  by (simp add: restrict_to_max(2)[OF assms(1,2)] assms(3))

lemma restrict_to_max_Tbar:
  assumes "c_invar c2" "vset_inv TX" "vset TX = T (to_set X)"
  shows "vset (restrict_to_max TX c2) =
           {y \<in> T (to_set X). c_lookup c2 y = Max (c_lookup c2 ` T (to_set X))}"
  by (simp add: restrict_to_max(2)[OF assms(1,2)] assms(3))

text \<open>Bridging the abstract fold oracles to the \<open>eps_of\<close> characterisation: an inner \<open>eps_fold\<close> over a
conditional \<open>eps_min\<close> yields the minimum of its gap set, and an outer \<open>eps_fold_red\<close> whose body already
folds a per-element gap set yields the minimum over the union.\<close>

lemma eps_fold_is_eps_of:
  fixes g :: "'a \<Rightarrow> real"
  assumes "set_invar X"
  shows "eps_fold X (\<lambda>x acc. if P x then eps_min acc (g x) else acc) a
           = eps_of (g ` {x \<in> to_set X. P x}) a"
proof-
  obtain xs where "set xs = to_set X"
    "eps_fold X (\<lambda>x acc. if P x then eps_min acc (g x) else acc) a
       = foldr (\<lambda>x acc. if P x then eps_min acc (g x) else acc) xs a"
    using eps_fold[OF assms] by blast
  thus ?thesis by (simp add: foldr_eps_of)
qed

lemma eps_fold_red_is_eps_of_gen:
  fixes G :: "'a \<Rightarrow> real set"
  assumes "set_invar_red C" "\<And>y acc. body y acc = eps_of (G y) acc" "\<And>y. finite (G y)"
  shows "eps_fold_red C body a = eps_of (\<Union>y \<in> to_set_red C. G y) a"
proof-
  obtain ys where "set ys = to_set_red C" "eps_fold_red C body a = foldr body ys a"
    using eps_fold_red[OF assms(1)] by blast
  thus ?thesis by (simp add: foldr_eps_of_gen[OF assms(2,3)])
qed

subsubsection \<open>The computed \<open>\<epsilon>\<close> is the minimum boundary gap\<close>

text \<open>Each of the two blocks of the \<open>compute_eps\<close> body contributes exactly the set of weight gaps of
the arcs it ranges over (via @{thm [source] eps_fold_is_eps_of} for the inner probe folds).\<close>

lemma eps_block1:
  assumes "set_invar X"
  shows "(if weak_orcl1 y X then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
          else (if y \<in>\<^sub>G R then acc
                else eps_fold X (\<lambda> x acc. if weak_orcl1 y (set_delete x X) \<and> x \<in>\<^sub>G R
                                 then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc))
         = eps_of (if weak_orcl1 y X then (if y \<in>\<^sub>G R then {} else {m1 - c_lookup c1 y})
                   else (if y \<in>\<^sub>G R then {}
                         else (\<lambda>x. c_lookup c1 x - c_lookup c1 y) ` {x \<in> to_set X. weak_orcl1 y (set_delete x X) \<and> x \<in>\<^sub>G R})) acc"
  by (auto simp add: eps_of_single eps_fold_is_eps_of[OF assms])

lemma eps_block2:
  assumes "set_invar X"
  shows "(if weak_orcl2 y X then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
          else (if y \<in>\<^sub>G R
                then eps_fold X (\<lambda> x acc. if weak_orcl2 y (set_delete x X) \<and> x \<notin>\<^sub>G R
                                 then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
                else acc))
         = eps_of (if weak_orcl2 y X then (if y \<in>\<^sub>G R then {m2 - c_lookup c2 y} else {})
                   else (if y \<in>\<^sub>G R
                         then (\<lambda>x. c_lookup c2 x - c_lookup c2 y) ` {x \<in> to_set X. weak_orcl2 y (set_delete x X) \<and> x \<notin>\<^sub>G R}
                         else {})) acc"
  by (auto simp add: eps_of_single eps_fold_is_eps_of[OF assms])

text \<open>The gap set \<open>Dgap\<close> contributed by a single non-basis element \<open>y\<close>: the tight boundary arcs into
its two fundamental circuits, split as \<open>Dgap1\<close> (matroid 1, reachable side) and \<open>Dgap2\<close> (matroid 2).\<close>

definition "Dgap1 X R m1 c1 y =
  (if weak_orcl1 y X then (if y \<in>\<^sub>G R then {} else {m1 - c_lookup c1 y})
   else (if y \<in>\<^sub>G R then {}
         else (\<lambda>x. c_lookup c1 x - c_lookup c1 y) ` {x \<in> to_set X. weak_orcl1 y (set_delete x X) \<and> x \<in>\<^sub>G R}))"

definition "Dgap2 X R m2 c2 y =
  (if weak_orcl2 y X then (if y \<in>\<^sub>G R then {m2 - c_lookup c2 y} else {})
   else (if y \<in>\<^sub>G R
         then (\<lambda>x. c_lookup c2 x - c_lookup c2 y) ` {x \<in> to_set X. weak_orcl2 y (set_delete x X) \<and> x \<notin>\<^sub>G R}
         else {}))"

definition "Dgap X R m1 m2 c1 c2 y = Dgap1 X R m1 c1 y \<union> Dgap2 X R m2 c2 y"

lemma Dgap1_finite: "finite (to_set X) \<Longrightarrow> finite (Dgap1 X R m1 c1 y)"
  by (auto simp add: Dgap1_def)

lemma Dgap2_finite: "finite (to_set X) \<Longrightarrow> finite (Dgap2 X R m2 c2 y)"
  by (auto simp add: Dgap2_def)

lemma Dgap_finite: "finite (to_set X) \<Longrightarrow> finite (Dgap X R m1 m2 c1 c2 y)"
  by (auto simp add: Dgap_def Dgap1_finite Dgap2_finite)

lemma eps_block1':
  assumes "set_invar X"
  shows "(if weak_orcl1 y X then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
          else (if y \<in>\<^sub>G R then acc
                else eps_fold X (\<lambda> x acc. if weak_orcl1 y (set_delete x X) \<and> x \<in>\<^sub>G R
                                 then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc))
         = eps_of (Dgap1 X R m1 c1 y) acc"
  unfolding Dgap1_def by (rule eps_block1[OF assms])

lemma eps_block2':
  assumes "set_invar X"
  shows "(if weak_orcl2 y X then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
          else (if y \<in>\<^sub>G R
                then eps_fold X (\<lambda> x acc. if weak_orcl2 y (set_delete x X) \<and> x \<notin>\<^sub>G R
                                 then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
                else acc))
         = eps_of (Dgap2 X R m2 c2 y) acc"
  unfolding Dgap2_def by (rule eps_block2[OF assms])

text \<open>Hence \<open>compute_eps\<close> computes the minimum, over all non-basis elements, of all tight boundary gaps
(\<open>None\<close> meaning \<open>\<infinity>\<close> when no gap exists) --- the value Frank's algorithm reweights by.\<close>

lemma eps_meaning:
  assumes "set_invar X" "finite (to_set X)" "to_set X \<subseteq> carrier"
  shows "compute_eps X m1 m2 R c1 c2
           = eps_of (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y) None"
  unfolding compute_eps_def
  apply (rule eps_fold_red_is_eps_of_gen[OF complement(1)[OF assms(1,3)]])
   apply (simp only: Let_def eps_block1'[OF assms(1)] eps_block2'[OF assms(1)]
                     eps_of_Un[OF Dgap2_finite[OF assms(2)] Dgap1_finite[OF assms(2)]])
   apply (simp add: Dgap_def Un_commute)
  apply (rule Dgap_finite[OF assms(2)])
  done

text \<open>Consequences of @{thm [source] eps_meaning}: the index set is finite, so the gap set is finite,
\<open>\<epsilon>\<close> (when defined) is its minimum, and hence a lower bound on every individual boundary gap --- the
key inequality feeding the reweighting lemma \<open>reweight_preserves_local_opt\<close>.\<close>

lemma eps_index_finite:
  assumes "set_invar X" "to_set X \<subseteq> carrier"
  shows "finite (to_set_red (complement X))"
proof -
  obtain xs where "set xs = to_set_red (complement X)"
    using eps_fold_red[OF complement(1)[OF assms]] by blast
  thus ?thesis by (metis List.finite_set)
qed

lemma eps_D_finite:
  assumes "set_invar X" "finite (to_set X)" "to_set X \<subseteq> carrier"
  shows "finite (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y)"
  using eps_index_finite[OF assms(1,3)] Dgap_finite[OF assms(2)] by blast

text \<open>The \<open>weak_orcl\<close> arc conditions occurring in \<open>Dgap\<close> characterise the auxiliary-graph arcs
\<open>A1\<close>/\<open>A2\<close> (via @{thm [source] matroid.circuit_extensional}).\<close>

lemma arc1_from_orcl:
  assumes "indep1 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "x \<in> to_set X" "y \<in> carrier - to_set X"
    "weak_orcl1 y (set_delete x X)" "\<not> weak_orcl1 y X"
  shows "(x, y) \<in> A1 (to_set X)"
proof -
  have xy: "x \<noteq> y" using assms(4,5) by auto
  have ycarr: "y \<in> carrier" using assms(5) by auto
  have del: "to_set (set_delete x X) = to_set X - {x}"
    using set_delete(2)[OF assms(2)] assms(3,4) by auto
  have dinv: "set_invar (set_delete x X)" using set_delete(1)[OF assms(2)] assms(3,4) by auto
  have idel: "indep1 (to_set X - {x})" using assms(1) matroid1.indep_subset by auto
  have "weak_orcl1 y (set_delete x X) = indep1 (Set.insert y (to_set X - {x}))"
    using weak_orcl1[OF dinv _ ycarr _ idel[folded del]] del assms(3,5) by auto
  hence i1: "indep1 (Set.insert y (to_set X - {x}))" using assms(6) by simp
  have i2: "\<not> indep1 (Set.insert y (to_set X))"
    using assms(7) weak_orcl1[OF assms(2,3) ycarr _ assms(1)] assms(5) by auto
  have "Set.insert y (to_set X) - {x} = Set.insert y (to_set X - {x})" using xy by auto
  hence "x \<in> matroid1.the_circuit (Set.insert y (to_set X))"
    using matroid1.circuit_extensional[OF assms(1) ycarr] assms(4) i1 i2 by auto
  thus ?thesis using xy assms(5) by (auto simp add: A1_def)
qed

lemma arc2_from_orcl:
  assumes "indep2 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "x \<in> to_set X" "y \<in> carrier - to_set X"
    "weak_orcl2 y (set_delete x X)" "\<not> weak_orcl2 y X"
  shows "(y, x) \<in> A2 (to_set X)"
proof -
  have xy: "x \<noteq> y" using assms(4,5) by auto
  have ycarr: "y \<in> carrier" using assms(5) by auto
  have del: "to_set (set_delete x X) = to_set X - {x}"
    using set_delete(2)[OF assms(2)] assms(3,4) by auto
  have dinv: "set_invar (set_delete x X)" using set_delete(1)[OF assms(2)] assms(3,4) by auto
  have idel: "indep2 (to_set X - {x})" using assms(1) matroid2.indep_subset by auto
  have "weak_orcl2 y (set_delete x X) = indep2 (Set.insert y (to_set X - {x}))"
    using weak_orcl2[OF dinv _ ycarr _ idel[folded del]] del assms(3,5) by auto
  hence i1: "indep2 (Set.insert y (to_set X - {x}))" using assms(6) by simp
  have i2: "\<not> indep2 (Set.insert y (to_set X))"
    using assms(7) weak_orcl2[OF assms(2,3) ycarr _ assms(1)] assms(5) by auto
  have "Set.insert y (to_set X) - {x} = Set.insert y (to_set X - {x})" using xy by auto
  hence "x \<in> matroid2.the_circuit (Set.insert y (to_set X))"
    using matroid2.circuit_extensional[OF assms(1) ycarr] assms(4) i1 i2 by auto
  thus ?thesis using xy assms(5) by (auto simp add: A2_def)
qed

lemma arc1_to_orcl:
  assumes "indep1 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "(x, y) \<in> A1 (to_set X)"
  shows "x \<in> to_set X \<and> weak_orcl1 y (set_delete x X) \<and> \<not> weak_orcl1 y X \<and> y \<in> carrier - to_set X"
proof -
  have yc: "y \<in> carrier - to_set X" and xc: "x \<in> matroid1.the_circuit (Set.insert y (to_set X)) - {y}"
    using assms(4) by (auto simp add: A1_def)
  have ycarr: "y \<in> carrier" using yc by auto
  have subc: "Set.insert y (to_set X) \<subseteq> carrier" using assms(3) ycarr by auto
  have xins: "x \<in> Set.insert y (to_set X)"
    using xc matroid1.the_circuit_X_in_X[OF subset_refl subc] by auto
  have xy: "x \<noteq> y" using xc by auto
  have xX: "x \<in> to_set X" using xins xy by auto
  have dep: "\<not> indep1 (Set.insert y (to_set X))"
    using xc matroid1.the_circuit_non_empty_dependent by auto
  have "indep1 (Set.insert y (to_set X) - {x})"
    using xc matroid1.circuit_extensional[OF assms(1) ycarr] by auto
  hence idel: "indep1 (Set.insert y (to_set X - {x}))" using xy by (simp add: insert_Diff_if)
  have del: "to_set (set_delete x X) = to_set X - {x}" using set_delete(2)[OF assms(2)] assms(3) xX by auto
  have dinv: "set_invar (set_delete x X)" using set_delete(1)[OF assms(2)] assms(3) xX by auto
  have idelX: "indep1 (to_set X - {x})" using assms(1) matroid1.indep_subset by auto
  have "weak_orcl1 y (set_delete x X) = indep1 (Set.insert y (to_set X - {x}))"
    using weak_orcl1[OF dinv _ ycarr _ idelX[folded del]] del assms(3) yc by auto
  hence wo1: "weak_orcl1 y (set_delete x X)" using idel by simp
  have wo2: "\<not> weak_orcl1 y X"
    using weak_orcl1[OF assms(2,3) ycarr _ assms(1)] yc dep by auto
  show ?thesis using xX wo1 wo2 yc by simp
qed

lemma arc2_to_orcl:
  assumes "indep2 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "(y, x) \<in> A2 (to_set X)"
  shows "x \<in> to_set X \<and> weak_orcl2 y (set_delete x X) \<and> \<not> weak_orcl2 y X \<and> y \<in> carrier - to_set X"
proof -
  have yc: "y \<in> carrier - to_set X" and xc: "x \<in> matroid2.the_circuit (Set.insert y (to_set X)) - {y}"
    using assms(4) by (auto simp add: A2_def)
  have ycarr: "y \<in> carrier" using yc by auto
  have subc: "Set.insert y (to_set X) \<subseteq> carrier" using assms(3) ycarr by auto
  have xins: "x \<in> Set.insert y (to_set X)"
    using xc matroid2.the_circuit_X_in_X[OF subset_refl subc] by auto
  have xy: "x \<noteq> y" using xc by auto
  have xX: "x \<in> to_set X" using xins xy by auto
  have dep: "\<not> indep2 (Set.insert y (to_set X))"
    using xc matroid2.the_circuit_non_empty_dependent by auto
  have "indep2 (Set.insert y (to_set X) - {x})"
    using xc matroid2.circuit_extensional[OF assms(1) ycarr] by auto
  hence idel: "indep2 (Set.insert y (to_set X - {x}))" using xy by (simp add: insert_Diff_if)
  have del: "to_set (set_delete x X) = to_set X - {x}" using set_delete(2)[OF assms(2)] assms(3) xX by auto
  have dinv: "set_invar (set_delete x X)" using set_delete(1)[OF assms(2)] assms(3) xX by auto
  have idelX: "indep2 (to_set X - {x})" using assms(1) matroid2.indep_subset by auto
  have "weak_orcl2 y (set_delete x X) = indep2 (Set.insert y (to_set X - {x}))"
    using weak_orcl2[OF dinv _ ycarr _ idelX[folded del]] del assms(3) yc by auto
  hence wo1: "weak_orcl2 y (set_delete x X)" using idel by simp
  have wo2: "\<not> weak_orcl2 y X"
    using weak_orcl2[OF assms(2,3) ycarr _ assms(1)] yc dep by auto
  show ?thesis using xX wo1 wo2 yc by simp
qed

subsubsection \<open>The circuit oracle computes the same \<open>\<epsilon>\<close>\<close>

text \<open>The circuit variant differs only in how each element's boundary arcs are enumerated
(directly via \<open>circuit1\<close>/\<open>circuit2\<close> rather than by probing \<open>weak_orcl\<close>); both range over the same arcs,
so @{term compute_eps_circuit} equals @{term compute_eps}. This lets the whole plain-loop correctness be
reused for the circuit loop without redoing the \<open>\<epsilon>\<close> analysis.\<close>

lemma eps_fold_red_cond_is_eps_of:
  fixes g :: "'a \<Rightarrow> real"
  assumes "set_invar_red C"
  shows "eps_fold_red C (\<lambda>x acc. if P x then eps_min acc (g x) else acc) a
           = eps_of (g ` {x \<in> to_set_red C. P x}) a"
proof-
  obtain xs where "set xs = to_set_red C"
    "eps_fold_red C (\<lambda>x acc. if P x then eps_min acc (g x) else acc) a
       = foldr (\<lambda>x acc. if P x then eps_min acc (g x) else acc) xs a"
    using eps_fold_red[OF assms] by blast
  thus ?thesis by (simp add: foldr_eps_of)
qed

lemma foldr_eps_of_gen_restr:
  fixes G :: "'a \<Rightarrow> real set"
  assumes "\<And>y acc. y \<in> set ys \<Longrightarrow> body y acc = eps_of (G y) acc" "\<And>y. y \<in> set ys \<Longrightarrow> finite (G y)"
  shows "foldr body ys a = eps_of (\<Union>y \<in> set ys. G y) a"
  using assms
proof (induction ys)
  case (Cons y ys)
  have "foldr body (y # ys) a = eps_of (G y) (eps_of (\<Union>z \<in> set ys. G z) a)"
    using Cons by simp
  also have "... = eps_of (G y \<union> (\<Union>z \<in> set ys. G z)) a"
    using Cons.prems(2) by (subst eps_of_Un) auto
  finally show ?case by simp
qed simp

lemma eps_fold_red_is_eps_of_gen_restr:
  fixes G :: "'a \<Rightarrow> real set"
  assumes "set_invar_red C" "\<And>y acc. y \<in> to_set_red C \<Longrightarrow> body y acc = eps_of (G y) acc"
    "\<And>y. y \<in> to_set_red C \<Longrightarrow> finite (G y)"
  shows "eps_fold_red C body a = eps_of (\<Union>y \<in> to_set_red C. G y) a"
proof-
  obtain ys where yseq: "set ys = to_set_red C" and ef: "eps_fold_red C body a = foldr body ys a"
    using eps_fold_red[OF assms(1)] by blast
  have "foldr body ys a = eps_of (\<Union>y \<in> set ys. G y) a"
    using assms(2,3) yseq by (intro foldr_eps_of_gen_restr) auto
  thus ?thesis using ef yseq by simp
qed

lemma circuit1_arc_eq:
  assumes "indep1 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "y \<in> carrier - to_set X" "\<not> weak_orcl1 y X"
  shows "to_set_red (circuit1 y X) = {x \<in> to_set X. weak_orcl1 y (set_delete x X)}"
proof -
  have ny: "\<not> indep1 (Set.insert y (to_set X))"
    using assms(5) weak_orcl1[OF assms(2,3) _ _ assms(1)] assms(4) by auto
  have tc: "to_set_red (circuit1 y X) = matroid1.the_circuit (Set.insert y (to_set X)) - {y}"
    using circuit1(1)[OF assms(2,1,3) _ ny] assms(4) by auto
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> to_set_red (circuit1 y X)"
    hence "(x, y) \<in> A1 (to_set X)" using tc assms(4) by (auto simp add: A1_def)
    thus "x \<in> {x \<in> to_set X. weak_orcl1 y (set_delete x X)}" using arc1_to_orcl[OF assms(1,2,3)] by auto
  next
    fix x assume "x \<in> {x \<in> to_set X. weak_orcl1 y (set_delete x X)}"
    hence "(x, y) \<in> A1 (to_set X)" using arc1_from_orcl[OF assms(1,2,3) _ assms(4) _ assms(5)] by auto
    thus "x \<in> to_set_red (circuit1 y X)" using tc assms(4) by (auto simp add: A1_def)
  qed
qed

lemma circuit2_arc_eq:
  assumes "indep2 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "y \<in> carrier - to_set X" "\<not> weak_orcl2 y X"
  shows "to_set_red (circuit2 y X) = {x \<in> to_set X. weak_orcl2 y (set_delete x X)}"
proof -
  have ny: "\<not> indep2 (Set.insert y (to_set X))"
    using assms(5) weak_orcl2[OF assms(2,3) _ _ assms(1)] assms(4) by auto
  have tc: "to_set_red (circuit2 y X) = matroid2.the_circuit (Set.insert y (to_set X)) - {y}"
    using circuit2(1)[OF assms(2,1,3) _ ny] assms(4) by auto
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> to_set_red (circuit2 y X)"
    hence "(y, x) \<in> A2 (to_set X)" using tc assms(4) by (auto simp add: A2_def)
    thus "x \<in> {x \<in> to_set X. weak_orcl2 y (set_delete x X)}" using arc2_to_orcl[OF assms(1,2,3)] by auto
  next
    fix x assume "x \<in> {x \<in> to_set X. weak_orcl2 y (set_delete x X)}"
    hence "(y, x) \<in> A2 (to_set X)" using arc2_from_orcl[OF assms(1,2,3) _ assms(4) _ assms(5)] by auto
    thus "x \<in> to_set_red (circuit2 y X)" using tc assms(4) by (auto simp add: A2_def)
  qed
qed

lemma eps_block1_circ:
  assumes "indep1 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "y \<in> carrier - to_set X"
  shows "(if weak_orcl1 y X then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
          else (if y \<in>\<^sub>G R then acc
                else eps_fold_red (circuit1 y X)
                       (\<lambda>x acc. if x \<in>\<^sub>G R then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc))
         = eps_of (Dgap1 X R m1 c1 y) acc"
proof (cases "weak_orcl1 y X")
  case True
  thus ?thesis by (simp add: Dgap1_def eps_of_single)
next
  case False
  have yc: "y \<in> carrier" using assms(4) by auto
  show ?thesis
  proof (cases "y \<in>\<^sub>G R")
    case True thus ?thesis using False by (simp add: Dgap1_def)
  next
    case Rfalse: False
    have ny: "\<not> indep1 (Set.insert y (to_set X))"
      using False weak_orcl1[OF assms(2,3) yc _ assms(1)] assms(4) by auto
    have "eps_fold_red (circuit1 y X)
             (\<lambda>x acc. if x \<in>\<^sub>G R then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc
            = eps_of ((\<lambda>x. c_lookup c1 x - c_lookup c1 y) ` {x \<in> to_set_red (circuit1 y X). x \<in>\<^sub>G R}) acc"
      using eps_fold_red_cond_is_eps_of[OF circuit1(2)[OF assms(2,1,3) yc ny]] by simp
    also have "... = eps_of ((\<lambda>x. c_lookup c1 x - c_lookup c1 y)
                              ` {x \<in> to_set X. weak_orcl1 y (set_delete x X) \<and> x \<in>\<^sub>G R}) acc"
      by (simp add: circuit1_arc_eq[OF assms(1,2,3,4) False] conj_ac)
    finally show ?thesis using False Rfalse by (simp add: Dgap1_def)
  qed
qed

lemma eps_block2_circ:
  assumes "indep2 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "y \<in> carrier - to_set X"
  shows "(if weak_orcl2 y X then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
          else (if y \<in>\<^sub>G R
                then eps_fold_red (circuit2 y X)
                       (\<lambda>x acc. if x \<notin>\<^sub>G R then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
                else acc))
         = eps_of (Dgap2 X R m2 c2 y) acc"
proof (cases "weak_orcl2 y X")
  case True
  thus ?thesis by (simp add: Dgap2_def eps_of_single)
next
  case False
  have yc: "y \<in> carrier" using assms(4) by auto
  show ?thesis
  proof (cases "y \<in>\<^sub>G R")
    case False thus ?thesis using \<open>\<not> weak_orcl2 y X\<close> by (simp add: Dgap2_def)
  next
    case Rtrue: True
    have ny: "\<not> indep2 (Set.insert y (to_set X))"
      using False weak_orcl2[OF assms(2,3) yc _ assms(1)] assms(4) by auto
    have "eps_fold_red (circuit2 y X)
             (\<lambda>x acc. if x \<notin>\<^sub>G R then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
            = eps_of ((\<lambda>x. c_lookup c2 x - c_lookup c2 y) ` {x \<in> to_set_red (circuit2 y X). x \<notin>\<^sub>G R}) acc"
      using eps_fold_red_cond_is_eps_of[OF circuit2(2)[OF assms(2,1,3) yc ny]] by simp
    also have "... = eps_of ((\<lambda>x. c_lookup c2 x - c_lookup c2 y)
                              ` {x \<in> to_set X. weak_orcl2 y (set_delete x X) \<and> x \<notin>\<^sub>G R}) acc"
      by (simp add: circuit2_arc_eq[OF assms(1,2,3,4) False] conj_ac)
    finally show ?thesis using False Rtrue by (simp add: Dgap2_def)
  qed
qed

lemma eps_meaning_circuit:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X" "finite (to_set X)" "to_set X \<subseteq> carrier"
  shows "compute_eps_circuit X m1 m2 R c1 c2
           = eps_of (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y) None"
  unfolding compute_eps_circuit_def
proof (rule eps_fold_red_is_eps_of_gen_restr[OF complement(1)[OF assms(3,5)]])
  fix y acc assume "y \<in> to_set_red (complement X)"
  hence yc: "y \<in> carrier - to_set X" using complement(2)[OF assms(3,5)] by simp
  show "(let acc = (if weak_orcl1 y X then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
                    else (if y \<in>\<^sub>G R then acc
                          else eps_fold_red (circuit1 y X)
                                 (\<lambda>x acc. if x \<in>\<^sub>G R then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc));
             acc = (if weak_orcl2 y X then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
                    else (if y \<in>\<^sub>G R
                          then eps_fold_red (circuit2 y X)
                                 (\<lambda>x acc. if x \<notin>\<^sub>G R then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
                          else acc))
          in acc)
        = eps_of (Dgap X R m1 m2 c1 c2 y) acc"
    by (simp only: Let_def eps_block1_circ[OF assms(1,3,5) yc] eps_block2_circ[OF assms(2,3,5) yc]
                   eps_of_Un[OF Dgap2_finite[OF assms(4)] Dgap1_finite[OF assms(4)]])
       (simp add: Dgap_def Un_commute)
next
  fix y show "finite (Dgap X R m1 m2 c1 c2 y)" using Dgap_finite[OF assms(4)] .
qed

lemma compute_eps_circuit_eq:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X" "finite (to_set X)" "to_set X \<subseteq> carrier"
  shows "compute_eps_circuit X m1 m2 R c1 c2 = compute_eps X m1 m2 R c1 c2"
  using eps_meaning_circuit[OF assms] eps_meaning[OF assms(3,4,5)] by simp

subsubsection \<open>The computed \<open>\<epsilon>\<close> is the minimum gap\<close>

text \<open>The gaps collected by \<open>compute_eps\<close> are exactly the boundary gaps of
@{const weighted_intersection_graph.gaps}.\<close>

lemma Dgap_gaps:
  assumes "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
    "c_invar c1" "c_invar c2" "vset_inv SX" "vset SX = S (to_set X)"
    "vset_inv TX" "vset TX = T (to_set X)" "vset_inv R"
  shows "(\<Union> y \<in> to_set_red (complement X). Dgap X R (weight_Max SX c1) (weight_Max TX c2) c1 c2 y)
         = weighted_intersection_graph.gaps carrier indep1 indep2 (c_lookup c1) (c_lookup c2)
             (to_set X) (vset R)"
    (is "?D = ?G")
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF assms(1,2)] .
  have isinR: "\<And>z. (z \<in>\<^sub>G R) = (z \<in> vset R)" using graph.vset.set.set_isin[OF assms(11)] by simp
  have m1: "weight_Max SX c1 = Max (c_lookup c1 ` S (to_set X))" if "y \<in> S (to_set X)" for y
    using weight_Max[OF assms(5,7)] assms(8) that by auto
  have m2: "weight_Max TX c2 = Max (c_lookup c2 ` T (to_set X))" if "y \<in> T (to_set X)" for y
    using weight_Max[OF assms(6,9)] assms(10) that by auto
  have woS: "weak_orcl1 y X \<longleftrightarrow> y \<in> S (to_set X)" if "y \<in> carrier - to_set X" for y
    using weak_orcl1[OF assms(1,2) _ _ assms(3)] that by (auto simp add: S_def)
  have woT: "weak_orcl2 y X \<longleftrightarrow> y \<in> T (to_set X)" if "y \<in> carrier - to_set X" for y
    using weak_orcl2[OF assms(1,2) _ _ assms(4)] that by (auto simp add: T_def)
  have g1: "c_lookup c1 x - c_lookup c1 y \<in> ?G"
    if "(x, y) \<in> A1 (to_set X)" "x \<in> vset R" "y \<notin> vset R" for x y
    unfolding W.gaps_def by (rule UnI1, rule UnI1, rule UnI1) (use that in blast)
  have g2: "c_lookup c2 x - c_lookup c2 y \<in> ?G"
    if "(y, x) \<in> A2 (to_set X)" "y \<in> vset R" "x \<notin> vset R" for x y
    unfolding W.gaps_def by (rule UnI1, rule UnI1, rule UnI2) (use that in blast)
  have g3: "Max (c_lookup c1 ` S (to_set X)) - c_lookup c1 y \<in> ?G"
    if "y \<in> S (to_set X)" "y \<notin> vset R" for y
    unfolding W.gaps_def by (rule UnI1, rule UnI2) (use that in blast)
  have g4: "Max (c_lookup c2 ` T (to_set X)) - c_lookup c2 y \<in> ?G"
    if "y \<in> T (to_set X)" "y \<in> vset R" for y
    unfolding W.gaps_def by (rule UnI2) (use that in blast)
  have DG: "v \<in> ?G" if y: "y \<in> carrier - to_set X"
    and vy: "v \<in> Dgap X R (weight_Max SX c1) (weight_Max TX c2) c1 c2 y" for y v
  proof-
    from vy consider (D1) "v \<in> Dgap1 X R (weight_Max SX c1) c1 y"
      | (D2) "v \<in> Dgap2 X R (weight_Max TX c2) c2 y"
      by (auto simp add: Dgap_def)
    thus ?thesis
    proof cases
      case D1
      show ?thesis
      proof (cases "weak_orcl1 y X")
        case True
        hence yS: "y \<in> S (to_set X)" using woS[OF y] by simp
        have "y \<notin> vset R" "v = weight_Max SX c1 - c_lookup c1 y"
          using D1 True isinR by (auto simp add: Dgap1_def split: if_splits)
        thus ?thesis using g3[OF yS] m1[OF yS] by simp
      next
        case False
        then obtain x where x: "x \<in> to_set X" "weak_orcl1 y (set_delete x X)" "x \<in> vset R"
          and yR: "y \<notin> vset R" and v: "v = c_lookup c1 x - c_lookup c1 y"
          using D1 isinR by (auto simp add: Dgap1_def split: if_splits)
        have "(x, y) \<in> A1 (to_set X)"
          by (rule arc1_from_orcl[OF assms(3,1,2) x(1) y x(2) False])
        thus ?thesis using g1 x(3) yR v by simp
      qed
    next
      case D2
      show ?thesis
      proof (cases "weak_orcl2 y X")
        case True
        hence yT: "y \<in> T (to_set X)" using woT[OF y] by simp
        have "y \<in> vset R" "v = weight_Max TX c2 - c_lookup c2 y"
          using D2 True isinR by (auto simp add: Dgap2_def split: if_splits)
        thus ?thesis using g4[OF yT] m2[OF yT] by simp
      next
        case False
        then obtain x where x: "x \<in> to_set X" "weak_orcl2 y (set_delete x X)" "x \<notin> vset R"
          and yR: "y \<in> vset R" and v: "v = c_lookup c2 x - c_lookup c2 y"
          using D2 isinR by (auto simp add: Dgap2_def split: if_splits)
        have "(y, x) \<in> A2 (to_set X)"
          by (rule arc2_from_orcl[OF assms(4,1,2) x(1) y x(2) False])
        thus ?thesis using g2 x(3) yR v by simp
      qed
    qed
  qed
  have GD: "v \<in> ?D" if "v \<in> ?G" for v
  proof-
    from that consider
        (A1) x y where "(x, y) \<in> A1 (to_set X)" "x \<in> vset R" "y \<notin> vset R"
          "v = c_lookup c1 x - c_lookup c1 y"
      | (A2) x y where "(y, x) \<in> A2 (to_set X)" "y \<in> vset R" "x \<notin> vset R"
          "v = c_lookup c2 x - c_lookup c2 y"
      | (S) y where "y \<in> S (to_set X)" "y \<notin> vset R" "v = Max (c_lookup c1 ` S (to_set X)) - c_lookup c1 y"
      | (T) y where "y \<in> T (to_set X)" "y \<in> vset R" "v = Max (c_lookup c2 ` T (to_set X)) - c_lookup c2 y"
      unfolding W.gaps_def by blast
    thus ?thesis
    proof cases
      case (A1 x y)
      note o = arc1_to_orcl[OF assms(3,1,2) A1(1)]
      have "v \<in> Dgap X R (weight_Max SX c1) (weight_Max TX c2) c1 c2 y"
        using o A1(2-4) isinR by (auto simp add: Dgap_def Dgap1_def)
      thus ?thesis using o compIs by blast
    next
      case (A2 x y)
      note o = arc2_to_orcl[OF assms(4,1,2) A2(1)]
      have "v \<in> Dgap X R (weight_Max SX c1) (weight_Max TX c2) c1 c2 y"
        using o A2(2-4) isinR by (auto simp add: Dgap_def Dgap2_def)
      thus ?thesis using o compIs by blast
    next
      case (S y)
      have y: "y \<in> carrier - to_set X" using S(1) by (auto simp add: S_def)
      have "v \<in> Dgap X R (weight_Max SX c1) (weight_Max TX c2) c1 c2 y"
        using S woS[OF y] m1[OF S(1)] isinR by (auto simp add: Dgap_def Dgap1_def)
      thus ?thesis using y compIs by blast
    next
      case (T y)
      have y: "y \<in> carrier - to_set X" using T(1) by (auto simp add: T_def)
      have "v \<in> Dgap X R (weight_Max SX c1) (weight_Max TX c2) c1 c2 y"
        using T woT[OF y] m2[OF T(1)] isinR by (auto simp add: Dgap_def Dgap2_def)
      thus ?thesis using y compIs by blast
    qed
  qed
  show ?thesis
    using DG GD compIs by blast
qed

subsubsection \<open>The contexts satisfy the specification of the loop\<close>

text \<open>The invariant of a context: it was built for \<open>X\<close>, \<open>c1\<close> and \<open>c2\<close>, and its graph abstracts to
the tight graph. It is shared by both variants.\<close>

definition "aux_ctx_invar X c1 c2 K \<longleftrightarrow>
  actx_X K = X \<and> actx_c1 K = c1 \<and> actx_c2 K = c2 \<and>
  set_invar X \<and> to_set X \<subseteq> carrier \<and> indep1 (to_set X) \<and> indep2 (to_set X) \<and>
  c_invar c1 \<and> c_invar c2 \<and>
  vset_inv (actx_SX K) \<and> vset (actx_SX K) = S (to_set X) \<and>
  vset_inv (actx_TX K) \<and> vset (actx_TX K) = T (to_set X) \<and>
  actx_Sb K = restrict_to_max (actx_SX K) c1 \<and> actx_Tb K = restrict_to_max (actx_TX K) c2 \<and>
  graph.graph_inv (actx_G K) \<and> graph.finite_graph (actx_G K) \<and> graph.finite_vsets (actx_G K) \<and>
  graph.digraph_abs (actx_G K) =
    weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X) \<and>
  actx_R K = reach_set (actx_Sb K) (actx_G K)"

lemma aux_tight_ctx_invar:
  assumes "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
    "c_invar c1" "c_invar c2" "matroid1.local_opt (c_lookup c1) (to_set X)"
    "matroid2.local_opt (c_lookup c2) (to_set X)"
  shows "aux_ctx_invar X c1 c2 (aux_tight_ctx X c1 c2)"
    and "aux_ctx_invar X c1 c2 (aux_tight_ctx_circuit X c1 c2)"
proof-
  have cInvComp: "set_invar_red (complement X)" using complement(1)[OF assms(1,2)] .
  have compIs: "to_set_red (complement X) = carrier - to_set X" using complement(2)[OF assms(1,2)] .
  obtain SX TX G where fields: "compute_graph X (complement X) = (SX, TX, G)"
    by (rule prod_cases3)
  note props = U.compute_graph_aux_graph[OF assms(1-4) fields]
  note ctc = compute_tight_graph_correct[OF assms(3,4,1) cInvComp compIs[THEN equalityD1]]
  note ctm = compute_tight_graph_meaning[OF assms(3,4,1) cInvComp compIs]
  show "aux_ctx_invar X c1 c2 (aux_tight_ctx X c1 c2)"
    using props(4,5,9,10) ctc(1,3,4) ctm assms(1-6)
    by (simp add: aux_ctx_invar_def aux_tight_ctx_def fields Let_def)
  obtain SX' TX' G' where fields': "compute_graph_circuit X (complement X) = (SX', TX', G')"
    by (rule prod_cases3)
  note props' = U.compute_graph_circuit_aux_graph[OF assms(1-4) fields']
  note ctc' = compute_tight_graph_circuit_correct[OF assms(3,4,1) cInvComp compIs[THEN equalityD1]]
  note ctm' = compute_tight_graph_circuit_meaning[OF assms(3,4,1) cInvComp compIs]
  show "aux_ctx_invar X c1 c2 (aux_tight_ctx_circuit X c1 c2)"
    using props'(4,5,9,10) ctc'(1,3,4) ctm' assms(1-6)
    by (simp add: aux_ctx_invar_def aux_tight_ctx_circuit_def fields' Let_def)
qed

lemma aux_ctx_abs:
  assumes "aux_ctx_invar X c1 c2 K"
  shows "graph.digraph_abs (actx_G K) =
           weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
    and "vset (actx_Sb K) = weighted_intersection_graph.Sbar carrier indep1 (c_lookup c1) (to_set X)"
    and "vset (actx_Tb K) = weighted_intersection_graph.Tbar carrier indep2 (c_lookup c2) (to_set X)"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  show "graph.digraph_abs (actx_G K) = W.Gbar (to_set X)"
    using assms by (simp add: aux_ctx_invar_def)
  show "vset (actx_Sb K) = W.Sbar (to_set X)"
    using assms restrict_to_max_Sbar[of c1 "actx_SX K" X]
    by (simp add: aux_ctx_invar_def W.Sbar_def)
  show "vset (actx_Tb K) = W.Tbar (to_set X)"
    using assms restrict_to_max_Tbar[of c2 "actx_TX K" X]
    by (simp add: aux_ctx_invar_def W.Tbar_def)
qed

lemma aux_ctx_graph:
  assumes "aux_ctx_invar X c1 c2 K"
  shows "graph.graph_inv (actx_G K)" "graph.finite_graph (actx_G K)" "graph.finite_vsets (actx_G K)"
    "vset_inv (actx_Sb K)" "vset_inv (actx_Tb K)" "vset (actx_Sb K) \<subseteq> carrier"
    "vset (actx_Tb K) \<subseteq> carrier" "dVs (graph.digraph_abs (actx_G K)) \<subseteq> carrier"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  have inv: "indep1 (to_set X)" "indep2 (to_set X)" "c_invar c1" "c_invar c2"
    "vset_inv (actx_SX K)" "vset_inv (actx_TX K)"
    "actx_Sb K = restrict_to_max (actx_SX K) c1" "actx_Tb K = restrict_to_max (actx_TX K) c2"
    using assms by (simp_all add: aux_ctx_invar_def)
  note abs = aux_ctx_abs[OF assms]
  show "graph.graph_inv (actx_G K)" "graph.finite_graph (actx_G K)" "graph.finite_vsets (actx_G K)"
    using assms by (simp_all add: aux_ctx_invar_def)
  show "vset_inv (actx_Sb K)" "vset_inv (actx_Tb K)"
    using restrict_to_max(1)[OF inv(3,5)] restrict_to_max(1)[OF inv(4,6)] inv(7,8) by simp_all
  show "vset (actx_Sb K) \<subseteq> carrier" "vset (actx_Tb K) \<subseteq> carrier"
    using abs(2,3) W.Sbar_subset W.Tbar_subset S_in_carrier[OF inv(1,2)] T_in_carrier[OF inv(1,2)]
    by blast+
  show "dVs (graph.digraph_abs (actx_G K)) \<subseteq> carrier"
    using abs(1) dVs_subset[OF W.Gbar_subset] dVs_A1A2_carrier[OF inv(1,2)] by (metis subset_trans)
qed

lemma aux_tight_path_spec:
  "aux_ctx_invar X c1 c2 K \<Longrightarrow> aux_tight_path K = None \<longleftrightarrow>
     (\<nexists> p u v. (vwalk_bet (graph.digraph_abs (actx_G K)) u p v \<or> (p = [u] \<and> u = v))
               \<and> u \<in> vset (actx_Sb K) \<and> v \<in> vset (actx_Tb K))"
  "\<lbrakk>aux_ctx_invar X c1 c2 K; aux_tight_path K = Some p\<rbrakk> \<Longrightarrow>
     \<exists> u v. (vwalk_bet (graph.digraph_abs (actx_G K)) u p v \<or> (p = [u] \<and> u = v))
            \<and> u \<in> vset (actx_Sb K) \<and> v \<in> vset (actx_Tb K) \<and>
       (\<nexists> p'. (vwalk_bet (graph.digraph_abs (actx_G K)) u p' v \<or> (p' = [u] \<and> u = v))
                \<and> length p' < length p)"
  using find_path(1)[OF aux_ctx_graph] find_path(2)[OF aux_ctx_graph]
  by (simp_all add: aux_tight_path_def)

lemma aux_reach_spec:
  assumes "aux_ctx_invar X c1 c2 K" "aux_tight_path K = None"
  shows "vset_inv (aux_reach K)"
    and "vset (aux_reach K) =
       {v. \<exists> u \<in> vset (actx_Sb K). u = v \<or> (\<exists> p. vwalk_bet (graph.digraph_abs (actx_G K)) u p v)}"
proof-
  have R: "aux_reach K = reach_set (actx_Sb K) (actx_G K)"
    using assms(1) by (simp add: aux_ctx_invar_def aux_reach_def)
  show "vset_inv (aux_reach K)"
    unfolding R by (rule reach_set(1)[OF aux_ctx_graph(1,4)[OF assms(1)]])
  show "vset (aux_reach K) =
       {v. \<exists> u \<in> vset (actx_Sb K). u = v \<or> (\<exists> p. vwalk_bet (graph.digraph_abs (actx_G K)) u p v)}"
    unfolding R by (rule reach_set(2)[OF aux_ctx_graph(1,4)[OF assms(1)]])
qed

text \<open>Both \<open>\<epsilon>\<close> oracles compute the minimum gap across the boundary of the reachable set.\<close>

lemma aux_eps_spec:
  assumes "aux_ctx_invar X c1 c2 K" "aux_tight_path K = None"
  shows "aux_eps K = eps_of (weighted_intersection_graph.gaps carrier indep1 indep2 (c_lookup c1)
                 (c_lookup c2) (to_set X) (weighted_intersection_graph.Rbar carrier indep1 indep2
                 (c_lookup c1) (c_lookup c2) (to_set X))) None"
    and "aux_eps_circuit K = eps_of (weighted_intersection_graph.gaps carrier indep1 indep2
                 (c_lookup c1) (c_lookup c2) (to_set X) (weighted_intersection_graph.Rbar carrier
                 indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X))) None"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  have inv: "actx_X K = X" "actx_c1 K = c1" "actx_c2 K = c2" "set_invar X" "to_set X \<subseteq> carrier"
    "indep1 (to_set X)" "indep2 (to_set X)" "c_invar c1" "c_invar c2"
    "vset_inv (actx_SX K)" "vset (actx_SX K) = S (to_set X)"
    "vset_inv (actx_TX K)" "vset (actx_TX K) = T (to_set X)"
    using assms(1) by (simp_all add: aux_ctx_invar_def)
  have finX: "finite (to_set X)" using matroid1.indep_finite[OF inv(6)] .
  have Rinv: "vset_inv (actx_R K)" using aux_reach_spec(1)[OF assms] by (simp add: aux_reach_def)
  have Rset: "vset (actx_R K) = W.Rbar (to_set X)"
    using aux_reach_spec(2)[OF assms] aux_ctx_abs[OF assms(1)] by (simp add: aux_reach_def W.Rbar_def)
  have eq: "compute_eps X (weight_Max (actx_SX K) c1) (weight_Max (actx_TX K) c2) (actx_R K) c1 c2
              = eps_of (W.gaps (to_set X) (W.Rbar (to_set X))) None"
    unfolding eps_meaning[OF inv(4) finX inv(5)] Dgap_gaps[OF inv(4-13) Rinv] Rset ..
  show "aux_eps K = eps_of (W.gaps (to_set X) (W.Rbar (to_set X))) None"
    using eq by (simp add: aux_eps_def inv(1-3))
  show "aux_eps_circuit K = eps_of (W.gaps (to_set X) (W.Rbar (to_set X))) None"
    using eq compute_eps_circuit_eq[OF inv(6,7,4) finX inv(5)]
    by (simp add: aux_eps_circuit_def inv(1-3))
qed

sublocale standard: weighted_intersection_path_loop where set_insert = set_insert
  and set_delete = set_delete and to_set = to_set and set_invar = set_invar
  and set_empty = set_empty and c_shift = c_shift and c_zero = c_zero
  and tight_ctx = aux_tight_ctx and tight_path = aux_tight_path and reach = aux_reach
  and eps = aux_eps and carrier = carrier and indep1 = indep1 and indep2 = indep2
  and c_lookup = c_lookup and c_invar = c_invar and r_set = vset and r_invar = vset_inv
  and ctx_invar = aux_ctx_invar and ctx_edges = "\<lambda> K. graph.digraph_abs (actx_G K)"
  and ctx_S = "\<lambda> K. vset (actx_Sb K)" and ctx_T = "\<lambda> K. vset (actx_Tb K)"
  by unfold_locales
    (fact set_insert set_delete set_empty c_zero c_shift aux_tight_ctx_invar
       aux_ctx_abs aux_tight_path_spec aux_reach_spec aux_eps_spec)+

sublocale circuit: weighted_intersection_path_loop where set_insert = set_insert
  and set_delete = set_delete and to_set = to_set and set_invar = set_invar
  and set_empty = set_empty and c_shift = c_shift and c_zero = c_zero
  and tight_ctx = aux_tight_ctx_circuit and tight_path = aux_tight_path and reach = aux_reach
  and eps = aux_eps_circuit and carrier = carrier and indep1 = indep1 and indep2 = indep2
  and c_lookup = c_lookup and c_invar = c_invar and r_set = vset and r_invar = vset_inv
  and ctx_invar = aux_ctx_invar and ctx_edges = "\<lambda> K. graph.digraph_abs (actx_G K)"
  and ctx_S = "\<lambda> K. vset (actx_Sb K)" and ctx_T = "\<lambda> K. vset (actx_Tb K)"
  by unfold_locales
    (fact set_insert set_delete set_empty c_zero c_shift aux_tight_ctx_invar
       aux_ctx_abs aux_tight_path_spec aux_reach_spec aux_eps_spec)+

lemmas weighted_matroid_intersection_correct = standard.weighted_matroid_intersection_correct[
  folded weighted_matroid_intersection_def weighted_initial_state_def]

lemmas weighted_matroid_intersection_partial_correct =
  standard.weighted_matroid_intersection_partial_correct[
  folded weighted_matroid_intersection_def weighted_initial_state_def]

lemmas weighted_matroid_intersection_circuit_correct = circuit.weighted_matroid_intersection_correct[
  folded weighted_matroid_intersection_circuit_def weighted_initial_state_def]

lemmas weighted_matroid_intersection_circuit_partial_correct =
  circuit.weighted_matroid_intersection_partial_correct[
  folded weighted_matroid_intersection_circuit_def weighted_initial_state_def]

end

end
