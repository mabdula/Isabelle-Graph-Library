theory CSR_Neighbour_Lists
  imports Imperative.Array_Range_Iteration
begin

section \<open>Neighbour Lists of an Edge List\<close>

text \<open>The functional model of a graph given as a list of edges: the neighbour lists, their
      start offsets in a flat neighbour array, and the neighbour map \<open>build_nhlists\<close>.\<close>

subsection \<open>Abstract Construction\<close>

text \<open>Neighbours of vertex v in edge list es.\<close>
definition nbrs :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "nbrs es v = map snd (filter (\<lambda>e. fst e = v) es)"

text \<open>Start offset of vertex v in the flat neighbour array.\<close>
definition start_off :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat" where
  "start_off es v = sum_list (map (\<lambda>u. length (nbrs es u)) [0..<v])"

text \<open>Flat neighbour array (as an Isabelle list).\<close>
definition build_nha :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "build_nha es n = concat (map (nbrs es) [0..<n])"

text \<open>The neighbour map of the edge list.\<close>
definition build_nhlists :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list option" where
  "build_nhlists es v =
     (if nbrs es v = [] then None else Some (nbrs es v))"

subsection \<open>Basic Properties\<close>

lemma length_build_nha: "length (build_nha es n) = start_off es n"
  unfolding build_nha_def start_off_def
  by (simp add: length_concat comp_def)

lemma start_off_zero [simp]: "start_off es 0 = 0"
  unfolding start_off_def by simp

lemma start_off_Suc:
  "start_off es (Suc v) = start_off es v + length (nbrs es v)"
  unfolding start_off_def by simp

lemma build_nhlists_dom:
  "dom (build_nhlists es) = {v. nbrs es v \<noteq> []}"
  unfolding build_nhlists_def by (auto split: if_split)

lemma build_nhlists_edge:
  "(\<exists>vs. build_nhlists es u = Some vs \<and> v \<in> set vs) \<longleftrightarrow> (u, v) \<in> set es"
  by (auto simp add: build_nhlists_def nbrs_def filter_empty_conv)

lemma build_nhlists_set:
  "set (case build_nhlists es u of None \<Rightarrow> [] | Some vs \<Rightarrow> vs) = {v. (u, v) \<in> set es}"
  using build_nhlists_edge[of es u] by (cases "build_nhlists es u") auto

lemma finite_build_nhlists_dom: "finite (dom (build_nhlists es))"
proof-
  have "dom (build_nhlists es) \<subseteq> fst ` set es"
    unfolding build_nhlists_dom nbrs_def map_is_Nil_conv filter_empty_conv by blast
  then show ?thesis
    by (rule finite_subset) (rule finite_imageI[OF finite_set])
qed

subsection \<open>Monotonicity of start\_off\<close>

lemma start_off_mono:
  "v \<le> n \<Longrightarrow> start_off es v \<le> start_off es n"
  by (induction n) (auto simp: start_off_Suc le_Suc_eq)

subsection \<open>The Key Indexing Lemma\<close>

text \<open>
The strict-interval segment at vertex v in the flat array equals nbrs es v.
Proof: split the list at v using id\_take\_nth\_drop, then use
nths\_intervall\_strict\_as\_drop\_and\_take.
\<close>

lemma build_nha_nths_vertex:
  assumes "v < n"
  shows "nths (build_nha es n)
              {start_off es v ..< start_off es v + length (nbrs es v)}
         = nbrs es v"
proof -
  let ?A = "concat (map (nbrs es) [0..<v])"
  let ?xs = "nbrs es v"
  let ?B = "concat (map (nbrs es) [Suc v..<n])"
  have list_split: "[0..<n] = [0..<v] @ v # [Suc v..<n]"
    using assms id_take_nth_drop[of v "[0..<n]"] by simp
  have split: "build_nha es n = ?A @ ?xs @ ?B"
    unfolding build_nha_def by (simp add: list_split)
  have lenA: "length ?A = start_off es v"
    unfolding start_off_def by (simp add: length_concat comp_def)
  show ?thesis
    unfolding nths_intervall_strict_as_drop_and_take
    by (simp add: split lenA[symmetric])
  qed

lemma nbrs_append [simp]:
  "nbrs (xs @ ys) v = nbrs xs v @ nbrs ys v"
  unfolding nbrs_def by (simp add: filter_append)

end
