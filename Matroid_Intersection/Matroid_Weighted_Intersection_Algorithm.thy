theory Matroid_Weighted_Intersection_Algorithm
  imports Matroid_Weighted_Intersection_Path_Loop Matroid_Intersection_Algorithm
begin

section \<open>Weighted Matroid Intersection Algorithm\<close>

text \<open>Frank's weighted matroid intersection algorithm (Korte--Vygen, Section 13.7) with the tight
auxiliary graph built explicitly. The loop itself is the one of
@{theory Matroid_Intersection.Matroid_Weighted_Intersection_Path_Loop}. Here it is instantiated
twice, as in @{theory Matroid_Intersection.Matroid_Intersection_Algorithm}:
\<^item> the \<open>plain\<close> version probes each single swap \<open>X - {x} + y\<close> via the independence
    oracle;
\<^item> the \<open>circuit\<close> version reads off the whole fundamental circuit at once.

Per iteration a context is built: the endpoint sets \<open>S\<close>/\<open>T\<close> from the unweighted auxiliary
    graph,
their maximum-weight elements \<open>Sbar\<close>/\<open>Tbar\<close>, the tight graph \<open>Gbar\<close> and the set
    reachable in it.
The tight path, the reachable set and \<open>\<epsilon>\<close> are read off this context. The split weights are
    values of
an abstract weight-map type \<open>'cmap\<close>, accessed through \<open>c_lookup\<close>, \<open>c_shift\<close>,
    \<open>c_zero\<close>,
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
unweighted \<open>compute_graph\<close>/\<open>compute_graph_circuit\<close>/\<open>augment\<close> definitions, and
    adds the weight-map
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
    \<comment> \<open>the two set-folds with a running-\<open>min\<close> accumulator, used to
      \<^emph>\<open>compute\<close> \<open>\<epsilon>\<close>; they are
      \<open>inner_fold\<close>/\<open>outer_fold\<close> at the accumulator type \<^typ>\<open>real option\<close>
        (\<^const>\<open>None\<close> = \<open>\<infinity>\<close>)\<close>
    and eps_fold :: "'mset \<Rightarrow> ('a \<Rightarrow> real option \<Rightarrow> real option) \<Rightarrow> real
      option \<Rightarrow> real option"
    and eps_fold_red :: "'mset_red \<Rightarrow> ('a \<Rightarrow> real option \<Rightarrow> real option)
      \<Rightarrow> real option \<Rightarrow> real option"
begin

subsubsection \<open>Tight auxiliary graph -- plain version\<close>

text \<open>Like the unweighted \<open>treat1\<close>/\<open>treat2\<close>, but an arc is kept only when its
    endpoints have equal
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

text \<open>\<open>\<epsilon> =
    min(\<epsilon>\<^sub>1,\<epsilon>\<^sub>2,\<epsilon>\<^sub>3,\<epsilon>\<^sub>4)\<close> as a \<^typ>\<open>real
    option\<close> (\<^const>\<open>None\<close> = \<open>\<infinity>\<close>), computed by folding the
complement \<open>carrier - X\<close>: each \<open>y\<close> contributes its \<open>S\<close>/\<open>T\<close>
    endpoint gap (\<open>\<epsilon>\<^sub>3\<close>/\<open>\<epsilon>\<^sub>4\<close>) and, when \<open>y\<close> is not
addable, the gaps of its arcs crossing the boundary of \<open>R\<close>
    (\<open>\<epsilon>\<^sub>1\<close>/\<open>\<epsilon>\<^sub>2\<close>).\<close>

text \<open>Circuit variant: the arcs of \<open>y\<close> are read off its fundamental circuits \<open>circuit1/2 y
    X\<close>.\<close>
definition "compute_eps_circuit X m1 m2 R c1 c2 =
  eps_fold_red (complement X) (\<lambda> y acc.
    let acc = (if weak_orcl1 y X
               then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
               else (if y \<in>\<^sub>G R then acc
                     else eps_fold_red (circuit1 y X)
                            (\<lambda> x acc. if x \<in>\<^sub>G R then eps_min acc (c_lookup c1 x - c_lookup c1 y)
                              else acc) acc));
        acc = (if weak_orcl2 y X
               then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
               else (if y \<in>\<^sub>G R
                     then eps_fold_red (circuit2 y X)
                            (\<lambda> x acc. if x \<notin>\<^sub>G R then eps_min acc (c_lookup c2 x - c_lookup c2 y)
                              else acc) acc
                     else acc))
    in acc) None"

text \<open>Plain variant: the arcs of \<open>y\<close> are found by probing \<open>weak_orcl\<close> over each
    \<open>x \<in> X\<close>.\<close>
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
reachable in it. The two variants differ only in how the auxiliary graphs and \<open>\<epsilon>\<close> are
    computed.\<close>

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
  assumes set_insert: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar
    (set_insert x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_insert x S) = Set.insert
      x (to_set S)"
  assumes set_delete: "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar
    (set_delete x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_delete x S) = (to_set S)
      - {x}"
  assumes set_empty: "set_invar set_empty" "to_set set_empty = {}"
  assumes weak_orcl1:
    "\<And> X x. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; x \<in> carrier; x \<notin> to_set X; indep1
      (to_set X)\<rbrakk>
       \<Longrightarrow> weak_orcl1 x X \<longleftrightarrow> indep1 (Set.insert x (to_set X))"
  assumes weak_orcl2:
    "\<And> X x. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; x \<in> carrier; x \<notin> to_set X; indep2
      (to_set X)\<rbrakk>
       \<Longrightarrow> weak_orcl2 x X \<longleftrightarrow> indep2 (Set.insert x (to_set X))"
  assumes inner_fold:
     "\<And> X f G. set_invar X \<Longrightarrow> \<exists> xs. set xs = to_set X \<and> inner_fold X f G = foldr f xs
       G"
  assumes inner_fold_circuit:
     "\<And> X f G. set_invar_red X
      \<Longrightarrow> \<exists> xs. set xs = to_set_red X \<and> inner_fold_circuit X f G = foldr f xs G"
  assumes outer_fold:
     "\<And> X f trip. set_invar_red X \<Longrightarrow> \<exists> xs. set xs = to_set_red X
                                           \<and> outer_fold X f trip = foldr f xs trip"
  assumes find_path:
    "\<And> G S T. \<lbrakk>graph.graph_inv G; graph.finite_graph G; graph.finite_vsets G; vset_inv S;
               vset_inv T; vset S \<subseteq> carrier; vset T \<subseteq> carrier; dVs (graph.digraph_abs G)
                 \<subseteq> carrier\<rbrakk>
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
  assumes complement: "\<And> S. \<lbrakk>set_invar S; to_set S  \<subseteq> carrier\<rbrakk> \<Longrightarrow>
    set_invar_red (complement S)"
    "\<And> S. \<lbrakk>set_invar S; to_set S  \<subseteq> carrier\<rbrakk> \<Longrightarrow> to_set_red (complement
      S) = carrier - to_set S"
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
  \<comment> \<open>the weight-map ADT: \<open>c_lookup\<close> is both the executable lookup and the abstraction to
    \<^typ>\<open>'a \<Rightarrow> real\<close>\<close>
  assumes c_zero: "c_invar c_zero" "c_lookup c_zero = (\<lambda> _. 0)"
  assumes c_shift:
    "\<And> R e c. \<lbrakk>c_invar c; vset_inv R\<rbrakk> \<Longrightarrow> c_invar (c_shift R e c)"
    "\<And> R e c. \<lbrakk>c_invar c; vset_inv R\<rbrakk>
       \<Longrightarrow> c_lookup (c_shift R e c) = (\<lambda> x. if x \<in> vset R then c_lookup c x + e else
         c_lookup c x)"
  assumes weight_Max:
    "\<And> V c. \<lbrakk>c_invar c; vset_inv V; vset V \<noteq> {}\<rbrakk> \<Longrightarrow> weight_Max V c = Max
      (c_lookup c ` vset V)"
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
    "\<And> X f a. set_invar_red X \<Longrightarrow> \<exists> xs. set xs = to_set_red X \<and> eps_fold_red X f a =
      foldr f xs a"
begin

subsubsection \<open>Reusing the unweighted development\<close>

text \<open>Since the weighted proof locale carries exactly the assumptions of the unweighted one, it is an
instance of it; interpreting it makes every unweighted lemma (\<open>compute_graph_meaning\<close>,
\<open>effect_of_augmentation\<close>, \<open>if_no_augpath_then_maximum\<close>, ...) available under the
    \<open>U\<close> prefix.\<close>

sublocale U: unweighted_intersection
  by unfold_locales
    (fact set_insert set_delete set_empty weak_orcl1 weak_orcl2 inner_fold
       inner_fold_circuit outer_fold find_path complement circuit1 circuit2)+

lemma weighted_graph_inst: "weighted_intersection_graph carrier indep1 indep2"
  by unfold_locales

subsubsection \<open>The tight auxiliary graph abstracts to \<open>Gbar\<close>\<close>

text \<open>A fold that adds one guarded arc per element keeps the graph invariants and adds exactly the
  guarded arcs.\<close>

lemma fold_add_edges:
  assumes "graph.graph_inv G" "\<exists> xs. set xs = A \<and> H = foldr (\<lambda> x G. if P x then graph.add_edge G
    (a x) (b x) else G) xs G"
  shows "graph.graph_inv H \<and> [H]\<^sub>g = [G]\<^sub>g \<union> {(a x, b x) | x. x \<in> A \<and> P x} \<and>
    (graph.finite_graph G \<longrightarrow> graph.finite_graph H) \<and> (graph.finite_vsets G \<longrightarrow>
      graph.finite_vsets H)"
proof-
  have "graph.graph_inv (foldr (\<lambda> x G. if P x then graph.add_edge G (a x) (b x) else G) xs G) \<and>
    [foldr (\<lambda> x G. if P x then graph.add_edge G (a x) (b x) else G) xs G]\<^sub>g =
      [G]\<^sub>g \<union> {(a x, b x) | x. x \<in> set xs \<and> P x} \<and>
    (graph.finite_graph G \<longrightarrow> graph.finite_graph (foldr (\<lambda> x G. if P x then graph.add_edge G (a
      x) (b x) else G) xs G)) \<and>
    (graph.finite_vsets G \<longrightarrow> graph.finite_vsets (foldr (\<lambda> x G. if P x then graph.add_edge G (a
      x) (b x) else G) xs G))"
    for xs
    using assms(1)
    by (induction xs) (auto simp add: graph.finite_graph_add_edge graph.finite_vsets_add_edge)
  thus ?thesis
    using assms(2)
    by blast
qed

text \<open>The oracle answers for an element \<open>y\<close> outside \<open>X\<close>: \<open>X + y\<close> is
    independent iff \<open>y\<close> is a
  source (and then its fundamental circuit is empty); \<open>X - x + y\<close> is probed via the oracle at
  \<open>X - x\<close>; and for a dependent \<open>X + y\<close> the accepted \<open>x\<close> form the fundamental
    circuit without \<open>y\<close>.\<close>

lemma weak_orcl1_iff:
  assumes "set_invar X" "indep1 (to_set X)" "y \<in> carrier - to_set X"
  shows "weak_orcl1 y X \<longleftrightarrow> y \<in> S (to_set X)"
    "weak_orcl1 y X \<Longrightarrow> matroid1.the_circuit (Set.insert y (to_set X)) = {}"
  using weak_orcl1 matroid1.indep_subset_carrier matroid1.independent_empty_circuit assms
  by (auto simp add: S_def)

lemma weak_orcl1_delete:
  assumes "set_invar X" "indep1 (to_set X)" "y \<in> carrier - to_set X" "x \<in> to_set X"
  shows "weak_orcl1 y (set_delete x X) \<longleftrightarrow> indep1 (Set.insert y (to_set X - {x}))"
proof-
  have "x \<in> carrier"
    using assms(2,4) matroid1.indep_subset_carrier
    by blast
  thus ?thesis
    using weak_orcl1[of "set_delete x X" y] set_delete[of X x] matroid1.indep_subset[of "to_set X" "to_set X - {x}"]
      matroid1.indep_subset_carrier assms
    by (simp add: Diff_subset[THEN order_trans])
qed

lemma weak_orcl1_circuit:
  assumes "set_invar X" "indep1 (to_set X)" "y \<in> carrier - to_set X" "\<not> weak_orcl1 y X"
  shows "matroid1.the_circuit (Set.insert y (to_set X)) - {y} = {x \<in> to_set X. weak_orcl1 y (set_delete x X)}"
  using weak_orcl1_iff(1) weak_orcl1_delete matroid1.circuit_extensional assms
  by (auto simp add: S_def insert_Diff_if)

lemma weak_orcl2_iff:
  assumes "set_invar X" "indep2 (to_set X)" "y \<in> carrier - to_set X"
  shows "weak_orcl2 y X \<longleftrightarrow> y \<in> T (to_set X)"
    "weak_orcl2 y X \<Longrightarrow> matroid2.the_circuit (Set.insert y (to_set X)) = {}"
  using weak_orcl2 matroid2.indep_subset_carrier matroid2.independent_empty_circuit assms
  by (auto simp add: T_def)

lemma weak_orcl2_delete:
  assumes "set_invar X" "indep2 (to_set X)" "y \<in> carrier - to_set X" "x \<in> to_set X"
  shows "weak_orcl2 y (set_delete x X) \<longleftrightarrow> indep2 (Set.insert y (to_set X - {x}))"
proof-
  have "x \<in> carrier"
    using assms(2,4) matroid2.indep_subset_carrier
    by blast
  thus ?thesis
    using weak_orcl2[of "set_delete x X" y] set_delete[of X x] matroid2.indep_subset[of "to_set X" "to_set X - {x}"]
      matroid2.indep_subset_carrier assms
    by (simp add: Diff_subset[THEN order_trans])
qed

lemma weak_orcl2_circuit:
  assumes "set_invar X" "indep2 (to_set X)" "y \<in> carrier - to_set X" "\<not> weak_orcl2 y X"
  shows "matroid2.the_circuit (Set.insert y (to_set X)) - {y} = {x \<in> to_set X. weak_orcl2 y (set_delete x X)}"
  using weak_orcl2_iff(1) weak_orcl2_delete matroid2.circuit_extensional assms
  by (auto simp add: T_def insert_Diff_if)

text \<open>The tight treat steps add the tight arcs found by the oracle or read off the circuit.\<close>

lemma treat1_tight_correct:
  assumes "set_invar X" "graph.graph_inv G"
  shows "graph.graph_inv (treat1_tight y X c G) \<and>
    [treat1_tight y X c G]\<^sub>g = [G]\<^sub>g \<union>
      {(x, y) | x. x \<in> to_set X \<and> weak_orcl1 y (set_delete x X) \<and> c_lookup c x = c_lookup c y} \<and>
    (graph.finite_graph G \<longrightarrow> graph.finite_graph (treat1_tight y X c G)) \<and>
    (graph.finite_vsets G \<longrightarrow> graph.finite_vsets (treat1_tight y X c G))"
  unfolding treat1_tight_def
  by (intro fold_add_edges inner_fold assms)

lemma treat2_tight_correct:
  assumes "set_invar X" "graph.graph_inv G"
  shows "graph.graph_inv (treat2_tight y X c G) \<and>
    [treat2_tight y X c G]\<^sub>g = [G]\<^sub>g \<union>
      {(y, x) | x. x \<in> to_set X \<and> weak_orcl2 y (set_delete x X) \<and> c_lookup c y = c_lookup c x} \<and>
    (graph.finite_graph G \<longrightarrow> graph.finite_graph (treat2_tight y X c G)) \<and>
    (graph.finite_vsets G \<longrightarrow> graph.finite_vsets (treat2_tight y X c G))"
  unfolding treat2_tight_def
  by (intro fold_add_edges inner_fold assms)

lemma treat1_circuit_tight_correct:
  assumes "set_invar_red C" "graph.graph_inv G"
  shows "graph.graph_inv (treat1_circuit_tight y C c G) \<and>
    [treat1_circuit_tight y C c G]\<^sub>g = [G]\<^sub>g \<union> {(x, y) | x. x \<in> to_set_red C \<and> c_lookup c
      x = c_lookup c y} \<and>
    (graph.finite_graph G \<longrightarrow> graph.finite_graph (treat1_circuit_tight y C c G)) \<and>
    (graph.finite_vsets G \<longrightarrow> graph.finite_vsets (treat1_circuit_tight y C c G))"
  unfolding treat1_circuit_tight_def
  by (intro fold_add_edges inner_fold_circuit assms)

lemma treat2_circuit_tight_correct:
  assumes "set_invar_red C" "graph.graph_inv G"
  shows "graph.graph_inv (treat2_circuit_tight y C c G) \<and>
    [treat2_circuit_tight y C c G]\<^sub>g = [G]\<^sub>g \<union> {(y, x) | x. x \<in> to_set_red C \<and> c_lookup c
      y = c_lookup c x} \<and>
    (graph.finite_graph G \<longrightarrow> graph.finite_graph (treat2_circuit_tight y C c G)) \<and>
    (graph.finite_vsets G \<longrightarrow> graph.finite_vsets (treat2_circuit_tight y C c G))"
  unfolding treat2_circuit_tight_def
  by (intro fold_add_edges inner_fold_circuit assms)

text \<open>The outer fold of both tight builders: if the two treat steps add the tight arcs of the two
  fundamental circuits, the fold over the complement builds a graph abstracting to \<open>Gbar\<close>.\<close>

lemma outer_fold_tight:
  fixes SX TX :: 'vset
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X" "set_invar_red E"
    "to_set_red E = carrier - to_set X"
    "\<And> y T. snd (snd (F y T)) =
       (if weak_orcl2 y X then id else tB y) ((if weak_orcl1 y X then id else tA y) (snd (snd T)))"
    "\<And> y G. \<lbrakk>y \<in> carrier - to_set X; \<not> weak_orcl1 y X; graph.graph_inv G\<rbrakk>
      \<Longrightarrow>
       graph.graph_inv (tA y G) \<and> (graph.finite_graph G \<longrightarrow> graph.finite_graph (tA y G)) \<and>
       (graph.finite_vsets G \<longrightarrow> graph.finite_vsets (tA y G)) \<and>
       [tA y G]\<^sub>g = [G]\<^sub>g \<union> {(x, y) | x. x \<in> matroid1.the_circuit (Set.insert y (to_set X)) - {y}
                                    \<and> c_lookup c1 x = c_lookup c1 y}"
    "\<And> y G. \<lbrakk>y \<in> carrier - to_set X; \<not> weak_orcl2 y X; graph.graph_inv G\<rbrakk>
      \<Longrightarrow>
       graph.graph_inv (tB y G) \<and> (graph.finite_graph G \<longrightarrow> graph.finite_graph (tB y G)) \<and>
       (graph.finite_vsets G \<longrightarrow> graph.finite_vsets (tB y G)) \<and>
       [tB y G]\<^sub>g = [G]\<^sub>g \<union> {(y, x) | x. x \<in> matroid2.the_circuit (Set.insert y (to_set X)) - {y}
                                    \<and> c_lookup c2 y = c_lookup c2 x}"
  defines "H \<equiv> snd (snd (outer_fold E F (SX, TX, empty)))"
  shows "graph.graph_inv H \<and> graph.finite_graph H \<and> graph.finite_vsets H \<and>
    [H]\<^sub>g = weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  define D where "D y = {(x, y) | x. x \<in> matroid1.the_circuit (Set.insert y (to_set X)) - {y}
                                     \<and> c_lookup c1 x = c_lookup c1 y}
                      \<union> {(y, x) | x. x \<in> matroid2.the_circuit (Set.insert y (to_set X)) - {y}
                                     \<and> c_lookup c2 y = c_lookup c2 x}" for y
  have "graph.graph_inv (snd (snd (foldr F ys (SX, TX, empty)))) \<and>
        graph.finite_graph (snd (snd (foldr F ys (SX, TX, empty)))) \<and>
        graph.finite_vsets (snd (snd (foldr F ys (SX, TX, empty)))) \<and>
        [snd (snd (foldr F ys (SX, TX, empty)))]\<^sub>g = (\<Union> y \<in> set ys. D y)"
    if "set ys \<subseteq> carrier - to_set X" for ys
    using that
  proof(induction ys)
    case Nil
    thus ?case
      by (simp add: graph.finite_graph_empty graph.finite_vsets_empty)
  next
    case (Cons y ys)
    thus ?case
      using assms(6) assms(7)[of y] assms(8)[of y] weak_orcl1_iff(2)[OF assms(3,1), of y]
        weak_orcl2_iff(2)[OF assms(3,2), of y]
      by (cases "weak_orcl1 y X"; cases "weak_orcl2 y X"; auto simp add: D_def)
  qed
  moreover obtain ys where "set ys = to_set_red E" "H = snd (snd (foldr F ys (SX, TX, empty)))"
    using outer_fold[of E F "(SX, TX, empty)"] assms(4)
    by (auto simp add: H_def)
  ultimately show ?thesis
    using assms(5)
    by (auto simp add: D_def W.Gbar_def W.Abar1_def W.Abar2_def A1_def A2_def)
qed

text \<open>Both tight builders abstract to Frank's tight subgraph \<open>Gbar\<close>.\<close>

lemma compute_tight_graph_correct:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X" "set_invar_red E"
    "to_set_red E = carrier - to_set X"
  shows "graph.graph_inv (compute_tight_graph X c1 c2 E) \<and> graph.finite_graph (compute_tight_graph X c1 c2 E)
    \<and> graph.finite_vsets (compute_tight_graph X c1 c2 E) \<and> [compute_tight_graph X c1 c2 E]\<^sub>g =
      weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
  unfolding compute_tight_graph_def
  by (rule outer_fold_tight[where tA = "\<lambda> y. treat1_tight y X c1" and tB = "\<lambda> y. treat2_tight y X c2",
        OF assms]; insert treat1_tight_correct treat2_tight_correct weak_orcl1_circuit weak_orcl2_circuit assms;
      auto simp add: Let_def split: prod.splits)

lemma compute_tight_graph_circuit_correct:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X" "set_invar_red E"
    "to_set_red E = carrier - to_set X"
  shows "graph.graph_inv (compute_tight_graph_circuit X c1 c2 E) \<and>
    graph.finite_graph (compute_tight_graph_circuit X c1 c2 E) \<and>
    graph.finite_vsets (compute_tight_graph_circuit X c1 c2 E) \<and> [compute_tight_graph_circuit X c1 c2 E]\<^sub>g =
      weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
  unfolding compute_tight_graph_circuit_def
  by (rule outer_fold_tight[where tA = "\<lambda> y. treat1_circuit_tight y (circuit1 y X) c1"
        and tB = "\<lambda> y. treat2_circuit_tight y (circuit2 y X) c2", OF assms];
      insert treat1_circuit_tight_correct treat2_circuit_tight_correct circuit1 circuit2 weak_orcl1 weak_orcl2
        matroid1.indep_subset_carrier assms; auto simp add: Let_def split: prod.splits)

text \<open>Restricting the (weight-agnostic) endpoint sets @{term "S (to_set X)"}/@{term "T (to_set X)"}
to their maximum-weight elements yields Frank's tight endpoints \<open>Sbar\<close>/\<open>Tbar\<close>.\<close>

lemma restrict_to_max_Sbar:
  assumes "c_invar c1" "vset_inv SX" "vset SX = S (to_set X)"
  shows "vset (restrict_to_max SX c1) =
           {y \<in> S (to_set X). c_lookup c1 y = Max (c_lookup c1 ` S (to_set X))}"
  using restrict_to_max(2) assms
  by simp

lemma restrict_to_max_Tbar:
  assumes "c_invar c2" "vset_inv TX" "vset TX = T (to_set X)"
  shows "vset (restrict_to_max TX c2) =
           {y \<in> T (to_set X). c_lookup c2 y = Max (c_lookup c2 ` T (to_set X))}"
  using restrict_to_max(2) assms
  by simp

text \<open>Bridging the abstract fold oracles to the \<open>eps_of\<close> characterisation: a fold over a
conditional \<open>eps_min\<close> yields the minimum of its gap set, and an outer fold whose body folds a
per-element gap set yields the minimum over the union.\<close>

lemma eps_fold_is_eps_of:
  fixes g :: "'a \<Rightarrow> real"
  assumes "set_invar X"
  shows "eps_fold X (\<lambda>x acc. if P x then eps_min acc (g x) else acc) a
           = eps_of (g ` {x \<in> to_set X. P x}) a"
  using eps_fold[of X "\<lambda>x acc. if P x then eps_min acc (g x) else acc" a] assms
  by (auto simp add: foldr_eps_of)

lemma eps_fold_red_cond_is_eps_of:
  fixes g :: "'a \<Rightarrow> real"
  assumes "set_invar_red C"
  shows "eps_fold_red C (\<lambda>x acc. if P x then eps_min acc (g x) else acc) a
           = eps_of (g ` {x \<in> to_set_red C. P x}) a"
  using eps_fold_red[of C "\<lambda>x acc. if P x then eps_min acc (g x) else acc" a] assms
  by (auto simp add: foldr_eps_of)

lemma foldr_eps_of_gen_restr:
  fixes G :: "'a \<Rightarrow> real set"
  assumes "\<And>y acc. y \<in> set ys \<Longrightarrow> body y acc = eps_of (G y) acc" "\<And>y. y \<in> set ys
    \<Longrightarrow> finite (G y)"
  shows "foldr body ys a = eps_of (\<Union>y \<in> set ys. G y) a"
  using assms
  by (induction ys) (simp_all add: eps_of_Un)

lemma eps_fold_red_is_eps_of_gen_restr:
  fixes G :: "'a \<Rightarrow> real set"
  assumes "set_invar_red C" "\<And>y acc. y \<in> to_set_red C \<Longrightarrow> body y acc = eps_of (G y) acc"
    "\<And>y. y \<in> to_set_red C \<Longrightarrow> finite (G y)"
  shows "eps_fold_red C body a = eps_of (\<Union>y \<in> to_set_red C. G y) a"
proof-
  obtain ys where "set ys = to_set_red C" "eps_fold_red C body a = foldr body ys a"
    using eps_fold_red[of C body a] assms(1)
    by blast
  thus ?thesis
    using foldr_eps_of_gen_restr[of ys body G a] assms(2,3)
    by auto
qed

subsubsection \<open>The computed \<open>\<epsilon>\<close> is the minimum boundary gap\<close>

text \<open>The gap set \<open>Dgap\<close> contributed by a single non-basis element \<open>y\<close>: the tight
    boundary arcs into
its two fundamental circuits, split as \<open>Dgap1\<close> (matroid 1, reachable side) and \<open>Dgap2\<close>
    (matroid 2).\<close>

definition "Dgap1 X R m1 c1 y =
  (if weak_orcl1 y X then (if y \<in>\<^sub>G R then {} else {m1 - c_lookup c1 y})
   else (if y \<in>\<^sub>G R then {}
         else (\<lambda>x. c_lookup c1 x - c_lookup c1 y) ` {x \<in> to_set X. weak_orcl1 y (set_delete x X) \<and> x
           \<in>\<^sub>G R}))"

definition "Dgap2 X R m2 c2 y =
  (if weak_orcl2 y X then (if y \<in>\<^sub>G R then {m2 - c_lookup c2 y} else {})
   else (if y \<in>\<^sub>G R
         then (\<lambda>x. c_lookup c2 x - c_lookup c2 y) ` {x \<in> to_set X. weak_orcl2 y (set_delete x X) \<and> x
           \<notin>\<^sub>G R}
         else {}))"

definition "Dgap X R m1 m2 c1 c2 y = Dgap1 X R m1 c1 y \<union> Dgap2 X R m2 c2 y"

lemma Dgap_finite:
  "finite (to_set X) \<Longrightarrow> finite (Dgap1 X R m1 c1 y)" "finite (to_set X) \<Longrightarrow> finite (Dgap2
    X R m2 c2 y)"
  "finite (to_set X) \<Longrightarrow> finite (Dgap X R m1 m2 c1 c2 y)"
  by (auto simp add: Dgap_def Dgap1_def Dgap2_def)

text \<open>Each of the two blocks of the \<open>compute_eps\<close> body contributes exactly its gap set.\<close>

lemma eps_block1:
  assumes "set_invar X"
  shows "(if weak_orcl1 y X then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
          else (if y \<in>\<^sub>G R then acc
                else eps_fold X (\<lambda> x acc. if weak_orcl1 y (set_delete x X) \<and> x \<in>\<^sub>G R
                                 then eps_min acc (c_lookup c1 x - c_lookup c1 y) else acc) acc))
         = eps_of (Dgap1 X R m1 c1 y) acc"
  using assms
  by (auto simp add: Dgap1_def eps_of_single eps_fold_is_eps_of)

lemma eps_block2:
  assumes "set_invar X"
  shows "(if weak_orcl2 y X then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
          else (if y \<in>\<^sub>G R
                then eps_fold X (\<lambda> x acc. if weak_orcl2 y (set_delete x X) \<and> x \<notin>\<^sub>G R
                                 then eps_min acc (c_lookup c2 x - c_lookup c2 y) else acc) acc
                else acc))
         = eps_of (Dgap2 X R m2 c2 y) acc"
  using assms
  by (auto simp add: Dgap2_def eps_of_single eps_fold_is_eps_of)

text \<open>Hence \<open>compute_eps\<close> computes the minimum, over all non-basis elements, of all tight boundary
    gaps
(\<open>None\<close> meaning \<open>\<infinity>\<close> when no gap exists) --- the value Frank's algorithm reweights
    by.\<close>

lemma eps_meaning:
  assumes "set_invar X" "finite (to_set X)" "to_set X \<subseteq> carrier"
  shows "compute_eps X m1 m2 R c1 c2
           = eps_of (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y) None"
  by (unfold compute_eps_def, rule eps_fold_red_is_eps_of_gen_restr)
    (simp_all add: complement assms Let_def eps_block1 eps_block2 eps_of_Un Dgap_finite Dgap_def Un_commute)

lemma eps_D_finite:
  assumes "set_invar X" "finite (to_set X)" "to_set X \<subseteq> carrier"
  shows "finite (\<Union> y \<in> to_set_red (complement X). Dgap X R m1 m2 c1 c2 y)"
  using complement(2) matroid1.carrier_finite Dgap_finite(3) assms
  by simp

subsubsection \<open>The circuit oracle computes the same \<open>\<epsilon>\<close>\<close>

text \<open>The circuit variant differs only in how each element's boundary arcs are enumerated
(directly via \<open>circuit1\<close>/\<open>circuit2\<close> rather than by probing \<open>weak_orcl\<close>); both
    range over the same arcs,
so @{term compute_eps_circuit} equals @{term compute_eps}.\<close>

lemma eps_block1_circ:
  assumes "indep1 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "y \<in> carrier - to_set X"
  shows "(if weak_orcl1 y X then (if y \<in>\<^sub>G R then acc else eps_min acc (m1 - c_lookup c1 y))
          else (if y \<in>\<^sub>G R then acc
                else eps_fold_red (circuit1 y X)
                       (\<lambda>x acc. if x \<in>\<^sub>G R then eps_min acc (c_lookup c1 x - c_lookup c1 y) else
                         acc) acc))
         = eps_of (Dgap1 X R m1 c1 y) acc"
proof(cases "weak_orcl1 y X")
  case False
  hence "set_invar_red (circuit1 y X)" "to_set_red (circuit1 y X) = {x \<in> to_set X. weak_orcl1 y (set_delete x X)}"
    using circuit1 weak_orcl1_iff(1) weak_orcl1_circuit assms False
    by (auto simp add: S_def)
  thus ?thesis
    using False
    by (simp add: Dgap1_def eps_fold_red_cond_is_eps_of conj_ac)
qed (simp add: Dgap1_def eps_of_single)

lemma eps_block2_circ:
  assumes "indep2 (to_set X)" "set_invar X" "to_set X \<subseteq> carrier" "y \<in> carrier - to_set X"
  shows "(if weak_orcl2 y X then (if y \<in>\<^sub>G R then eps_min acc (m2 - c_lookup c2 y) else acc)
          else (if y \<in>\<^sub>G R
                then eps_fold_red (circuit2 y X)
                       (\<lambda>x acc. if x \<notin>\<^sub>G R then eps_min acc (c_lookup c2 x - c_lookup c2 y) else
                         acc) acc
                else acc))
         = eps_of (Dgap2 X R m2 c2 y) acc"
proof(cases "weak_orcl2 y X")
  case False
  hence "set_invar_red (circuit2 y X)" "to_set_red (circuit2 y X) = {x \<in> to_set X. weak_orcl2 y (set_delete x X)}"
    using circuit2 weak_orcl2_iff(1) weak_orcl2_circuit assms False
    by (auto simp add: T_def)
  thus ?thesis
    using False
    by (simp add: Dgap2_def eps_fold_red_cond_is_eps_of conj_ac)
qed (simp add: Dgap2_def eps_of_single)

lemma compute_eps_circuit_eq:
  assumes "indep1 (to_set X)" "indep2 (to_set X)" "set_invar X" "finite (to_set X)" "to_set X \<subseteq> carrier"
  shows "compute_eps_circuit X m1 m2 R c1 c2 = compute_eps X m1 m2 R c1 c2"
  by (unfold eps_meaning[OF assms(3-5)] compute_eps_circuit_def, rule eps_fold_red_is_eps_of_gen_restr)
    (simp_all add: complement assms Let_def eps_block1_circ eps_block2_circ eps_of_Un Dgap_finite Dgap_def Un_commute)

subsubsection \<open>The computed \<open>\<epsilon>\<close> is the minimum gap\<close>

text \<open>Per element \<open>y\<close>, \<open>Dgap1\<close> and \<open>Dgap2\<close> are the gaps of @{const
    weighted_intersection_graph.gaps}
whose arc ends or starts in \<open>y\<close>, or whose endpoint is \<open>y\<close>.\<close>

lemma Dgap1_gaps:
  assumes "set_invar X" "indep1 (to_set X)" "c_invar c1" "vset_inv SX" "vset SX = S (to_set X)" "vset_inv R"
    "y \<in> carrier - to_set X"
  shows "Dgap1 X R (weight_Max SX c1) c1 y =
    {c_lookup c1 x - c_lookup c1 y | x. (x, y) \<in> A1 (to_set X) \<and> x \<in> vset R \<and> y \<notin> vset R}
      \<union>
    {Max (c_lookup c1 ` S (to_set X)) - c_lookup c1 y | z. z = y \<and> y \<in> S (to_set X) \<and> y \<notin> vset R}"
  using weak_orcl1_iff[of X y] weak_orcl1_circuit[of X y] weight_Max[of c1 SX] graph.vset.set.set_isin[of R] assms
  by (auto simp add: Dgap1_def A1_def)

lemma Dgap2_gaps:
  assumes "set_invar X" "indep2 (to_set X)" "c_invar c2" "vset_inv TX" "vset TX = T (to_set X)" "vset_inv R"
    "y \<in> carrier - to_set X"
  shows "Dgap2 X R (weight_Max TX c2) c2 y =
    {c_lookup c2 x - c_lookup c2 y | x. (y, x) \<in> A2 (to_set X) \<and> y \<in> vset R \<and> x \<notin> vset R}
      \<union>
    {Max (c_lookup c2 ` T (to_set X)) - c_lookup c2 y | z. z = y \<and> y \<in> T (to_set X) \<and> y \<in> vset R}"
  using weak_orcl2_iff[of X y] weak_orcl2_circuit[of X y] weight_Max[of c2 TX] graph.vset.set.set_isin[of R] assms
  by (auto simp add: Dgap2_def A2_def)

text \<open>The gaps collected by \<open>compute_eps\<close> are exactly the boundary gaps of
@{const weighted_intersection_graph.gaps}.\<close>

lemma Dgap_gaps:
  assumes "set_invar X" "to_set X \<subseteq> carrier" "indep1 (to_set X)" "indep2 (to_set X)"
    "c_invar c1" "c_invar c2" "vset_inv SX" "vset SX = S (to_set X)"
    "vset_inv TX" "vset TX = T (to_set X)" "vset_inv R"
  shows "(\<Union> y \<in> to_set_red (complement X). Dgap X R (weight_Max SX c1) (weight_Max TX c2) c1 c2 y)
         = weighted_intersection_graph.gaps carrier indep1 indep2 (c_lookup c1) (c_lookup c2)
             (to_set X) (vset R)"
  using complement(2) Dgap1_gaps Dgap2_gaps assms weighted_graph_inst
  by (auto simp add: Dgap_def weighted_intersection_graph.gaps_def A1_def A2_def S_def T_def)

subsubsection \<open>The contexts satisfy the specification of the loop\<close>

text \<open>The invariant of a context: it was built for \<open>X\<close>, \<open>c1\<close> and \<open>c2\<close>,
    and its graph abstracts to
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
  using U.compute_graph_aux_graph U.compute_graph_circuit_aux_graph compute_tight_graph_correct
    compute_tight_graph_circuit_correct complement[OF assms(1,2)] assms(1-6)
  by (simp_all add: aux_ctx_invar_def aux_tight_ctx_def aux_tight_ctx_circuit_def Let_def split: prod.splits)

lemma aux_ctx_abs:
  assumes "aux_ctx_invar X c1 c2 K"
  shows "graph.digraph_abs (actx_G K) =
           weighted_intersection_graph.Gbar carrier indep1 indep2 (c_lookup c1) (c_lookup c2) (to_set X)"
    and "vset (actx_Sb K) = weighted_intersection_graph.Sbar carrier indep1 (c_lookup c1) (to_set X)"
    and "vset (actx_Tb K) = weighted_intersection_graph.Tbar carrier indep2 (c_lookup c2) (to_set X)"
  using assms restrict_to_max_Sbar[of c1 "actx_SX K" X] restrict_to_max_Tbar[of c2 "actx_TX K" X] weighted_graph_inst
  by (simp_all add: aux_ctx_invar_def weighted_intersection_graph.Sbar_def weighted_intersection_graph.Tbar_def)

lemma aux_ctx_graph:
  assumes "aux_ctx_invar X c1 c2 K"
  shows "graph.graph_inv (actx_G K)" "graph.finite_graph (actx_G K)" "graph.finite_vsets (actx_G K)"
    "vset_inv (actx_Sb K)" "vset_inv (actx_Tb K)" "vset (actx_Sb K) \<subseteq> carrier"
    "vset (actx_Tb K) \<subseteq> carrier" "dVs (graph.digraph_abs (actx_G K)) \<subseteq> carrier"
proof-
  interpret W: weighted_intersection_graph carrier indep1 indep2 "c_lookup c1" "c_lookup c2"
    by unfold_locales
  have "indep1 (to_set X)" "indep2 (to_set X)"
    using assms
    by (simp_all add: aux_ctx_invar_def)
  hence "W.Sbar (to_set X) \<subseteq> carrier" "W.Tbar (to_set X) \<subseteq> carrier" "dVs (W.Gbar (to_set X))
    \<subseteq> carrier"
    using W.Sbar_subset W.Tbar_subset S_in_carrier T_in_carrier dVs_subset[OF W.Gbar_subset] dVs_A1A2_carrier
    by (blast+)
  thus "vset (actx_Sb K) \<subseteq> carrier" "vset (actx_Tb K) \<subseteq> carrier" "dVs (graph.digraph_abs (actx_G
    K)) \<subseteq> carrier"
    using aux_ctx_abs[OF assms]
    by simp_all
  show "graph.graph_inv (actx_G K)" "graph.finite_graph (actx_G K)" "graph.finite_vsets (actx_G K)"
    "vset_inv (actx_Sb K)" "vset_inv (actx_Tb K)"
    using assms restrict_to_max(1)
    by (simp_all add: aux_ctx_invar_def)
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
       {v. \<exists> u \<in> vset (actx_Sb K). u = v \<or> (\<exists> p. vwalk_bet (graph.digraph_abs (actx_G K)) u p
         v)}"
  using reach_set aux_ctx_graph(1,4)[OF assms(1)] assms(1)
  by (simp_all add: aux_ctx_invar_def aux_reach_def)

text \<open>Both \<open>\<epsilon>\<close> oracles compute the minimum gap across the boundary of the reachable
    set.\<close>

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
    using assms(1)
    by (simp_all add: aux_ctx_invar_def)
  have "vset (actx_R K) = W.Rbar (to_set X)"
    using aux_reach_spec(2)[OF assms] aux_ctx_abs[OF assms(1)]
    by (simp add: aux_reach_def W.Rbar_def)
  hence "compute_eps X (weight_Max (actx_SX K) c1) (weight_Max (actx_TX K) c2) (actx_R K) c1 c2
           = eps_of (W.gaps (to_set X) (W.Rbar (to_set X))) None"
    using inv aux_reach_spec(1)[OF assms] matroid1.indep_finite
    by (simp add: eps_meaning Dgap_gaps aux_reach_def)
  thus "aux_eps K = eps_of (W.gaps (to_set X) (W.Rbar (to_set X))) None"
    "aux_eps_circuit K = eps_of (W.gaps (to_set X) (W.Rbar (to_set X))) None"
    using inv matroid1.indep_finite
    by (simp_all add: aux_eps_def aux_eps_circuit_def compute_eps_circuit_eq)
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
