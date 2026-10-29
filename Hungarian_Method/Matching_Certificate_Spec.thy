theory Matching_Certificate_Spec
  imports Matching_LPs.Matching_LP Basic_Matching.Weighted_Matchings_Reductions
          Tutte_Theorem.Bipartite_Matchings_Existence 
          Data_Structures.Real_Embedding
begin

section \<open>Certificate Checkers for Extremal Bipartite Matchings: Specification\<close>

text \<open>A checker that is independent of any solver. It receives an instance, a candidate matching
      and a certificate, and decides whether the candidate is a minimum or maximum weight
      (perfect) matching, or whether a certificate shows that there is no perfect matching.

      The instance consists of a finite set @{term E} of edge names, enumerated by
      @{term elist}, with the left endpoint @{term efst}, the right endpoint @{term esnd} and the
      weight @{term ew} of every edge, and of the lists @{term ls} and @{term rs} of the left and
      the right vertices, all below @{term n}. The candidate matching is a list of edge names,
      the optimality certificate a list of potentials (one for every vertex), and the
      infeasibility certificate a list of left vertices violating Hall's condition.

      For @{term neg}, the problem is to minimise the weights negated if @{term neg} holds.
      The certificate is always a dual of the minimisation problem.\<close>

definition sgn_c :: "bool \<Rightarrow> 'a::uminus \<Rightarrow> 'a" where
  "sgn_c b x = (if b then - x else x)"

subsection \<open>The Checks\<close>

locale matching_cert_spec =
  fixes E :: "'e set"
    and elist :: "'e list"
    and efst :: "'e \<Rightarrow> nat"
    and esnd :: "'e \<Rightarrow> nat"
    and ew :: "'e \<Rightarrow> 'n::linordered_idom"
    and n :: nat
    and ls :: "nat list"
    and rs :: "nat list"
begin

abbreviation "L \<equiv> set ls"
abbreviation "R \<equiv> set rs"

text \<open>The checks are for the weights shifted by @{term "- t"}: the dual constraint of an edge
      @{term e} is @{term "ys ! efst e + ys ! esnd e + t \<le> sgn_c neg (ew e)"}. The shift is
      @{term 0} except for the maximum cardinality variants.\<close>

definition "feas_ok neg t ys e = (ys ! efst e + ys ! esnd e + t \<le> sgn_c neg (ew e))"

definition "tight_ok neg t ys e = (ys ! efst e + ys ! esnd e + t = sgn_c neg (ew e))"

text \<open>The matching: every name is an edge, no vertex is used twice, and every edge is tight.
      The set @{term U} collects the matched vertices.\<close>

fun match_list :: "bool \<Rightarrow> 'n \<Rightarrow> 'n list \<Rightarrow> nat set \<Rightarrow> 'e list \<Rightarrow> nat set \<times> bool" where
  "match_list neg t ys U [] = (U, True)"
| "match_list neg t ys U (e # es) =
     (if e \<in> E \<and> efst e \<notin> U \<and> esnd e \<notin> U \<and> tight_ok neg t ys e
      then match_list neg t ys (insert (esnd e) (insert (efst e) U)) es else (U, False))"

text \<open>Non-perfect variants: potentials are non-positive and vanish on unmatched vertices.\<close>

definition "vert_ok ys U x = (ys ! x \<le> 0 \<and> (ys ! x \<noteq> 0 \<longrightarrow> x \<in> U))"

definition certify_sh :: "bool \<Rightarrow> bool \<Rightarrow> 'n \<Rightarrow> 'e list \<Rightarrow> 'n list \<Rightarrow> bool" where
  "certify_sh neg perfect t ms ys =
     (n \<le> length ys \<and> list_all (feas_ok neg t ys) elist \<and>
      (case match_list neg t ys {} ms of (U, ok) \<Rightarrow> ok \<and>
         (if perfect then length ms = length ls \<and> length ls = length rs
          else list_all (vert_ok ys U) ls \<and> list_all (vert_ok ys U) rs)))"

definition certify :: "bool \<Rightarrow> bool \<Rightarrow> 'e list \<Rightarrow> 'n list \<Rightarrow> bool" where
  "certify neg perfect = certify_sh neg perfect 0"

text \<open>Hall violators: the distinct elements of @{term S} are counted, duplicates are skipped.\<close>

fun hall_S :: "nat set \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat set \<times> nat \<times> bool" where
  "hall_S Sm k [] = (Sm, k, True)"
| "hall_S Sm k (x # xs) =
     (if x \<in> L then if x \<in> Sm then hall_S Sm k xs else hall_S (insert x Sm) (Suc k) xs
      else (Sm, k, False))"

fun hall_N :: "nat set \<Rightarrow> nat set \<Rightarrow> nat \<Rightarrow> 'e list \<Rightarrow> nat set \<times> nat" where
  "hall_N Sm Nm k [] = (Nm, k)"
| "hall_N Sm Nm k (e # es) =
     (if efst e \<in> Sm \<and> esnd e \<notin> Nm then hall_N Sm (insert (esnd e) Nm) (Suc k) es
      else hall_N Sm Nm k es)"

definition hall_check :: "nat list \<Rightarrow> bool" where
  "hall_check S =
     (length ls \<noteq> length rs \<or>
      (case hall_S {} 0 S of (Sm, k, ok) \<Rightarrow>
         ok \<and> (case hall_N Sm {} 0 elist of (Nm, nb) \<Rightarrow> nb < k)))"

text \<open>Maximum cardinality: a set @{term S} of left vertices with
      @{text "|L| - |S| + |N(S)| \<le> |ms|"}, and a dual for the shifted weights.\<close>

definition defic_ok :: "'e list \<Rightarrow> nat list \<Rightarrow> bool" where
  "defic_ok ms S =
     (case hall_S {} 0 S of (Sm, k, ok) \<Rightarrow>
        ok \<and> (case hall_N Sm {} 0 elist of (Nm, nb) \<Rightarrow> length ls + nb \<le> length ms + k))"

definition certify_mc :: "bool \<Rightarrow> 'e list \<Rightarrow> 'n list \<Rightarrow> 'n \<Rightarrow> nat list \<Rightarrow> bool" where
  "certify_mc neg ms ys t S = (certify_sh neg False t ms ys \<and> defic_ok ms S)"

end

subsection \<open>Soundness\<close>

locale matching_cert = matching_cert_spec E elist efst esnd ew n ls rs + real_embedding h
  for E :: "'e set" and elist efst esnd and ew :: "'e \<Rightarrow> 'n::linordered_idom" and n ls rs
    and h :: "'n \<Rightarrow> real" +
  assumes elist_E: "set elist = E"
    and fst_L: "efst ` E = L"
    and snd_R: "esnd ` E = R"
    and ls_distinct: "distinct ls"
    and rs_distinct: "distinct rs"
    and sides_disjoint: "L \<inter> R = {}"
    and verts_below: "L \<union> R \<subseteq> {..<n}"
    and no_parallel: "inj_on (\<lambda>e. (efst e, esnd e)) E"
begin

definition "cedge e = {efst e, esnd e}"

definition "G = cedge ` E"

definition "wG d = h (ew (THE e. e \<in> E \<and> cedge e = d))"

definition "wt neg d = sgn_c neg (wG d)"

definition "wt_sh neg t = (\<lambda>d. wt neg d - h t)"

lemma wt_sh_0 [simp]: "wt_sh neg 0 = wt neg"
  by (simp add: wt_sh_def)

definition "pot ys v = h (ys ! v)"

definition "Mat ms = cedge ` set ms"

lemma fst_in: "e \<in> E \<Longrightarrow> efst e \<in> L" and snd_in: "e \<in> E \<Longrightarrow> esnd e \<in> R"
  using fst_L snd_R
  by blast+

lemma fst_snd_neq: "e \<in> E \<Longrightarrow> efst e \<noteq> esnd e"
  using fst_in[of e] snd_in[of e] sides_disjoint
  by auto

lemma finite_E: "finite E"
  using elist_E
  by blast

lemma cedge_eq: "\<lbrakk>e \<in> E; e' \<in> E; cedge e = cedge e'\<rbrakk> \<Longrightarrow> e = e'"
  using fst_in[of e] snd_in[of e] fst_in[of e'] snd_in[of e'] sides_disjoint inj_onD[OF no_parallel, of e e']
  by (auto simp: cedge_def doubleton_eq_iff)

lemma wG_edge: "e \<in> E \<Longrightarrow> wG (cedge e) = h (ew e)"
  using cedge_eq
  by (auto simp: wG_def intro!: arg_cong[where f = ew] the_equality)

lemma h_sgn: "h (sgn_c b x) = sgn_c b (h x)"
  by (simp add: sgn_c_def)

lemma Vs_cedge: "Vs (cedge ` S) = efst ` S \<union> esnd ` S"
  by (auto simp: Vs_def cedge_def)

lemma Vs_G: "Vs G = L \<union> R"
  using fst_L snd_R
  by (simp add: G_def Vs_cedge)

lemma G_edgeE:
  assumes "d \<in> G"
  obtains e where "e \<in> E" "d = cedge e"
  using assms
  by (auto simp: G_def)

lemma graph_invar_G: "graph_invar G"
  using fst_snd_neq Vs_G
  by (fastforce simp: dblton_graph_def G_def cedge_def)

lemma bipartite_G: "bipartite G L R"
  using sides_disjoint fst_in snd_in
  by (fastforce simp: bipartite_def G_def cedge_def)

subsubsection \<open>Feasibility and Tightness\<close>

lemma cedge_doubleton:
  assumes "e \<in> E" "cedge e = {u, v}"
  shows "pot ys u + pot ys v = h (ys ! efst e + ys ! esnd e)"
  using assms
  by (auto simp: cedge_def doubleton_eq_iff pot_def h_add)

lemma feasible:
  "list_all (feas_ok neg t ys) elist \<Longrightarrow> feasible_min_perfect_dual G (wt_sh neg t) (pot ys)"
proof(rule feasible_min_perfect_dualI, elim G_edgeE)
  fix d u v e
  assume "d = {u, v}" "e \<in> E" "d = cedge e" "list_all (feas_ok neg t ys) elist"
  moreover hence "h (ys ! efst e + ys ! esnd e + t) \<le> h (sgn_c neg (ew e))"
    using elist_E
    by (auto simp: list_all_iff feas_ok_def simp del: h_add)
  ultimately show "pot ys u + pot ys v \<le> wt_sh neg t d"
    using wG_edge[of e] cedge_doubleton[of e u v ys]
    by (auto simp: wt_sh_def wt_def h_sgn h_add)
qed

lemma tight:
  assumes "e \<in> E" "tight_ok neg t ys e"
  shows "cedge e \<in> tight_subgraph G (wt_sh neg t) (pot ys)"
proof-
  have "h (ys ! efst e) + h (ys ! esnd e) + h t = h (sgn_c neg (ew e))"
    using assms(2)
    by (simp add: tight_ok_def flip: h_add)
  thus ?thesis
    using assms(1) wG_edge[of e]
    by (auto intro!: in_tight_subgraphI[OF refl] simp: G_def cedge_def wt_sh_def wt_def pot_def h_sgn)
qed

subsubsection \<open>The Matching\<close>

lemma match_list_props:
  "match_list neg t ys U0 xs = (U, True) \<Longrightarrow>
   set xs \<subseteq> E \<and> list_all (tight_ok neg t ys) xs \<and> U = U0 \<union> efst ` set xs \<union> esnd ` set xs \<and>
   (efst ` set xs \<union> esnd ` set xs) \<inter> U0 = {} \<and> distinct (map efst xs) \<and> distinct (map esnd xs)"
  by (induction xs arbitrary: U0; fastforce split: if_splits)

lemma matching_Mat:
  assumes "set ms \<subseteq> E" "distinct (map efst ms)" "distinct (map esnd ms)"
  shows "matching (Mat ms)"
proof(rule matchingI)
  fix d1 d2
  assume "d1 \<in> Mat ms" "d2 \<in> Mat ms" "d1 \<noteq> d2"
  then obtain a b where "a \<in> set ms" "b \<in> set ms" "a \<noteq> b" "d1 = cedge a" "d2 = cedge b"
    by (auto simp: Mat_def)
  moreover hence "efst a \<noteq> efst b" "esnd a \<noteq> esnd b"
    using assms(2,3)
    by (auto simp: distinct_map inj_on_def)
  moreover have "efst a \<noteq> esnd b" "esnd a \<noteq> efst b"
    using fst_in[of a] fst_in[of b] snd_in[of a] snd_in[of b] sides_disjoint assms(1) \<open>a \<in> set ms\<close> \<open>b \<in> set ms\<close>
    by (auto simp: subset_iff)
  ultimately show "d1 \<inter> d2 = {}"
    by (auto simp: cedge_def)
qed

lemma Mat_props:
  assumes "match_list neg t ys {} ms = (U, True)"
  shows "graph_matching G (Mat ms)" "Vs (Mat ms) = U"
        "Mat ms \<subseteq> tight_subgraph G (wt_sh neg t) (pot ys)"
        "distinct (map efst ms)" "distinct (map esnd ms)" "set ms \<subseteq> E"
  using match_list_props[OF assms] matching_Mat tight
  by (auto simp: Mat_def G_def Vs_cedge list_all_iff)

subsubsection \<open>Perfect Variants\<close>

lemma covers:
  "\<lbrakk>set ms \<subseteq> E; distinct (map f ms); f ` E = X; distinct xs; set xs = X; length ms = length xs\<rbrakk>
     \<Longrightarrow> f ` set ms = X"
  using distinct_card[of "map f ms"] distinct_card[of xs] finite_E
  by (intro card_subset_eq; auto)

lemma certify_perfect_sound:
  assumes "certify_sh neg True t ms ys"
  shows "min_weight_perfect_matching G (wt_sh neg t) (Mat ms)"
proof(cases "match_list neg t ys {} ms")
  case (Pair U ok)
  hence "perfect_matching G (Mat ms)"
    using assms Mat_props[of neg t ys ms U] covers[of ms efst L ls] covers[of ms esnd R rs] fst_L snd_R
          ls_distinct rs_distinct Vs_G
    by (auto simp: certify_sh_def perfect_matching_def Mat_def Vs_cedge)
  thus ?thesis
    using assms Pair min_weight_perfect_if_tight(1)[OF feasible _ graph_invar_G, of neg t ys "Mat ms"]
          Mat_props(3)[of neg t ys ms U]
    by (auto simp: certify_sh_def)
qed

subsubsection \<open>Non-Perfect Variants\<close>

lemma tight_subgraph_uminus:
  "tight_subgraph X (- w) (- y) = tight_subgraph X w (y :: _ \<Rightarrow> 'b :: ab_group_add)"
  by (force simp: tight_subgraph_def minus_equation_iff add.commute)

lemma certify_matching_sound:
  assumes "certify_sh neg False t ms ys"
  shows "min_weight_matching G (wt_sh neg t) (Mat ms)"
proof(cases "match_list neg t ys {} ms")
  case (Pair U ok)
  hence "match_list neg t ys {} ms = (U, True)" "list_all (feas_ok neg t ys) elist"
        "\<forall>x \<in> L \<union> R. ys ! x \<le> 0 \<and> (ys ! x \<noteq> 0 \<longrightarrow> x \<in> U)"
    using assms
    by (auto simp: certify_sh_def list_all_iff vert_ok_def)
  hence "max_weight_matching G (- wt_sh neg t) (Mat ms)"
    using Mat_props[of neg t ys ms U] feasible_min_perfect_dualD[OF feasible[of neg t ys]] Vs_G
    by ((auto intro!: max_weight_if_tight_matching_covers_bads(1)[of "L \<union> R" G _ "- pot ys"]
           feasible_max_dualI graph_invar_G simp: tight_subgraph_uminus non_zero_vertices_def pot_def);
        fastforce)
  thus ?thesis
    using min_and_max_matching[of G "wt_sh neg t"]
    by simp
qed

subsubsection \<open>The Four Variants\<close>

lemma wt_False: "wt False = wG" and wt_True: "wt True = - wG" and neg_neg_wG: "- (- wG) = wG"
  by (auto simp: wt_def sgn_c_def)

lemma min_weight_perfect_certified:
  "certify False True ms ys \<Longrightarrow> min_weight_perfect_matching G wG (Mat ms)"
  using certify_perfect_sound[of False 0]
  by (simp add: certify_def wt_False)

lemma max_weight_perfect_certified:
  "certify True True ms ys \<Longrightarrow> max_weight_perfect_matching G wG (Mat ms)"
  using certify_perfect_sound[of True 0] min_perfect_and_max_perfect_matching[of G "- wG"]
  by (simp add: certify_def wt_True neg_neg_wG)

lemma min_weight_matching_certified:
  "certify False False ms ys \<Longrightarrow> min_weight_matching G wG (Mat ms)"
  using certify_matching_sound[of False 0]
  by (simp add: certify_def wt_False)

lemma max_weight_matching_certified:
  "certify True False ms ys \<Longrightarrow> max_weight_matching G wG (Mat ms)"
  using certify_matching_sound[of True 0] min_and_max_matching[of G "- wG"]
  by (simp add: certify_def wt_True neg_neg_wG)

subsubsection \<open>Hall Violators\<close>

lemma hall_S_props:
  "\<lbrakk>hall_S Sm0 k0 xs = (Sm, k, True); finite Sm0; k0 = card Sm0\<rbrakk>
   \<Longrightarrow> Sm = Sm0 \<union> set xs \<and> k = card Sm \<and> set xs \<subseteq> L"
proof(induction xs arbitrary: Sm0 k0)
  case (Cons x xs)
  hence "x \<in> L"
    by (simp split: if_splits)
  show ?case
  proof(cases "x \<in> Sm0")
    case True
    hence "hall_S Sm0 k0 xs = (Sm, k, True)"
      using Cons.prems(1) \<open>x \<in> L\<close>
      by simp
    thus ?thesis
      using Cons.IH[OF _ Cons.prems(2,3)] \<open>x \<in> L\<close> True
      by auto
  next
    case False
    hence "hall_S (insert x Sm0) (Suc k0) xs = (Sm, k, True)" "Suc k0 = card (insert x Sm0)"
      using Cons.prems \<open>x \<in> L\<close>
      by simp_all
    thus ?thesis
      using Cons.IH[of "insert x Sm0" "Suc k0"] Cons.prems(2) \<open>x \<in> L\<close>
      by auto
  qed
qed simp

lemma hall_N_props:
  "\<lbrakk>hall_N Sm Nm0 k0 xs = (Nm, k); finite Nm0; k0 = card Nm0\<rbrakk>
   \<Longrightarrow> Nm = Nm0 \<union> esnd ` {e \<in> set xs. efst e \<in> Sm} \<and> k = card Nm"
proof(induction xs arbitrary: Nm0 k0)
  case (Cons e xs)
  show ?case
  proof(cases "efst e \<in> Sm \<and> esnd e \<notin> Nm0")
    case True
    hence "hall_N Sm (insert (esnd e) Nm0) (Suc k0) xs = (Nm, k)" "Suc k0 = card (insert (esnd e) Nm0)"
      using Cons.prems
      by simp_all
    hence "Nm = insert (esnd e) Nm0 \<union> esnd ` {e \<in> set xs. efst e \<in> Sm}" "k = card Nm"
      using Cons.IH[of "insert (esnd e) Nm0" "Suc k0"] Cons.prems(2)
      by auto
    thus ?thesis
      using True
      by auto
  next
    case False
    hence "hall_N Sm Nm0 k0 xs = (Nm, k)"
      using Cons.prems(1)
      by (auto split: if_splits)
    hence "Nm = Nm0 \<union> esnd ` {e \<in> set xs. efst e \<in> Sm}" "k = card Nm"
      using Cons.IH[OF _ Cons.prems(2,3)]
      by auto
    thus ?thesis
      using False
      by auto
  qed
qed simp

lemma hall_counts:
  "\<lbrakk>hall_S {} 0 S = (Sm, k, True); hall_N Sm {} 0 elist = (Nm, nb)\<rbrakk>
     \<Longrightarrow> set S \<subseteq> L \<and> k = card (set S) \<and> nb = card (esnd ` {e \<in> E. efst e \<in> set S})"
  using hall_S_props[of "{}" 0 S Sm k] hall_N_props[of Sm "{}" 0 elist Nm nb] elist_E
  by auto

lemma neighbourhood_left:
  "X \<subseteq> L \<Longrightarrow> Neighbourhood G X = esnd ` {e \<in> E. efst e \<in> X}"
  using fst_in snd_in sides_disjoint
  by (fastforce simp: Neighbourhood_def G_def cedge_def doubleton_eq_iff)

lemma hall_sound:
  assumes "hall_check S"
  shows "\<nexists>M. perfect_matching G M"
proof(cases "length ls = length rs")
  case True
  then obtain Sm k Nm nb where "hall_S {} 0 S = (Sm, k, True)" "hall_N Sm {} 0 elist = (Nm, nb)" "nb < k"
    using assms
    by (auto simp: hall_check_def split: prod.splits)
  hence "set S \<subseteq> L" "card (Neighbourhood G (set S)) < card (set S)"
    using hall_counts neighbourhood_left
    by auto
  thus ?thesis
    using frobenius_standard_bipartite[OF bipartite_G graph_invar_G] Vs_G
    by (auto simp: not_le)
next
  case False
  thus ?thesis
    using frobenius_standard_bipartite[OF bipartite_G graph_invar_G] Vs_G distinct_card[OF ls_distinct]
          distinct_card[OF rs_distinct]
    by auto
qed

lemma hall_complete:
  "\<lbrakk>\<nexists>M. perfect_matching G M; length ls = length rs\<rbrakk> \<Longrightarrow> \<exists>X \<subseteq> L. card (Neighbourhood G X) < card X"
  using frobenius_standard_bipartite[OF bipartite_G graph_invar_G] Vs_G distinct_card[OF ls_distinct]
        distinct_card[OF rs_distinct]
  by (auto simp: not_le Int_absorb2)

subsubsection \<open>Extremal Weight Maximum Cardinality Matchings\<close>

lemma matching_inj_on_member:
  assumes "matching M" "\<And>d. d \<in> M \<Longrightarrow> f d \<in> d"
  shows "inj_on f M"
proof(rule inj_onI)
  fix d d'
  assume "d \<in> M" "d' \<in> M" "f d = f d'"
  thus "d = d'"
    using assms(1) assms(2)[of d] assms(2)[of d'] matching_unique_match[of M "f d" d d']
    by simp
qed

text \<open>Every matching has at most @{text "|L - S| + |N(S)|"} edges: map each edge to its right
      endpoint if its left endpoint is in @{term S}, and to its left endpoint otherwise.\<close>

lemma defic_bound:
  assumes "graph_matching G M'" "Sset \<subseteq> L"
  shows "card M' \<le> card (L - Sset) + card (esnd ` {e \<in> E. efst e \<in> Sset})"
proof-
  define f where "f d = (if d \<inter> Sset = {} then the_elem (d \<inter> L) else the_elem (d \<inter> R))" for d
  have "f d \<in> d \<and> f d \<in> (L - Sset) \<union> esnd ` {e \<in> E. efst e \<in> Sset}" if "d \<in> G" for d
    using that
  proof(rule G_edgeE)
    fix e
    assume "e \<in> E" "d = cedge e"
    thus ?thesis
      using fst_in[of e] snd_in[of e] sides_disjoint assms(2)
      by (auto simp: f_def cedge_def Int_insert_left)
  qed
  hence "inj_on f M'" "f ` M' \<subseteq> (L - Sset) \<union> esnd ` {e \<in> E. efst e \<in> Sset}"
    using assms(1) matching_inj_on_member[of M' f]
    by blast+
  hence "card M' \<le> card ((L - Sset) \<union> esnd ` {e \<in> E. efst e \<in> Sset})"
    by (rule card_inj_on_le; simp add: finite_E)
  thus ?thesis
    using card_Un_le[of "L - Sset" "esnd ` {e \<in> E. efst e \<in> Sset}"]
    by linarith
qed

lemma card_Mat: "\<lbrakk>set ms \<subseteq> E; distinct (map efst ms)\<rbrakk> \<Longrightarrow> card (Mat ms) = length ms"
  using cedge_eq
  by (auto simp: Mat_def card_image distinct_card distinct_map inj_on_def subset_iff)

lemma certify_mc_sound:
  assumes "certify_mc neg ms ys t S"
  shows "min_weight_max_card_matching G (wt neg) (Mat ms)"
proof-
  obtain U Sm k Nm nb where "match_list neg t ys {} ms = (U, True)" "hall_S {} 0 S = (Sm, k, True)"
      "hall_N Sm {} 0 elist = (Nm, nb)" "length ls + nb \<le> length ms + k"
    using assms
    by (auto simp: certify_mc_def certify_sh_def defic_ok_def split: prod.splits)
  hence "card M' \<le> card (Mat ms)" if "graph_matching G M'" for M'
    using that hall_counts[of S Sm k Nm nb] defic_bound[of M' "set S"] Mat_props[of neg t ys ms U]
          card_Mat[of ms] card_Diff_subset[of "set S" L] card_mono[of L "set S"] distinct_card[OF ls_distinct]
    by auto
  hence "max_card_matching G (Mat ms)"
    using Mat_props(1)[of neg t ys ms U] \<open>match_list neg t ys {} ms = (U, True)\<close>
    by (auto intro!: max_card_matchingI')
  thus ?thesis
    using assms certify_matching_sound[of neg t ms ys] shift_max_card[of G "wt neg" "h t" "Mat ms"]
    by (simp add: certify_mc_def wt_sh_def)
qed

lemma min_weight_max_card_certified:
  "certify_mc False ms ys t S \<Longrightarrow> min_weight_max_card_matching G wG (Mat ms)"
  using certify_mc_sound[of False]
  by (simp add: wt_False)

lemma max_weight_max_card_certified:
  "certify_mc True ms ys t S \<Longrightarrow> max_weight_max_card_matching G wG (Mat ms)"
  using certify_mc_sound[of True] min_max_card_and_max_max_card_matching[of G "- wG"]
  by (simp add: wt_True neg_neg_wG)

end

end
