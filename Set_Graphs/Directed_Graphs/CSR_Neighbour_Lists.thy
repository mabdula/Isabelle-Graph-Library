theory CSR_Neighbour_Lists
  imports Imperative.Array_Range_Iteration
begin

section \<open>Neighbour Lists of an Edge List\<close>

text \<open>The functional model of a graph given as a list of edges: the neighbour lists, their
      start and end offsets in a flat neighbour array, and the neighbour map
      \<open>build_nhlists\<close>. The imperative construction of these arrays from an edge list is in
      \<open>CSR_Buildup_Simple\<close>.\<close>

subsection \<open>Abstract Construction\<close>

text \<open>Neighbours of vertex v in edge list es.\<close>
definition nbrs :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "nbrs es v = map snd (filter (\<lambda>e. fst e = v) es)"

text \<open>
Number of vertices: 0 for the empty edge list, otherwise one more than the
largest source vertex.
\<close>
definition nverts :: "(nat \<times> nat) list \<Rightarrow> nat" where
  "nverts es =
     (if es = [] then 0
      else Suc (foldl (\<lambda>m e. max m (fst e)) 0 es))"

text \<open>Start offset of vertex v in the flat neighbour array.\<close>
definition start_off :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat" where
  "start_off es v = sum_list (map (\<lambda>u. length (nbrs es u)) [0..<v])"

text \<open>Flat neighbour array (as an Isabelle list).\<close>
definition build_nha :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "build_nha es n = concat (map (nbrs es) [0..<n])"

text \<open>Start-index list for the CSR representation.\<close>
definition build_sindices :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "build_sindices es n =
     map (\<lambda>v. if nbrs es v = [] then 1 else start_off es v) [0..<n]"

text \<open>End-index list for the CSR representation.\<close>
definition build_eindices :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list" where
  "build_eindices es n =
     map (\<lambda>v. if nbrs es v = [] then 0
               else start_off es v + length (nbrs es v) - 1) [0..<n]"

text \<open>
Abstract neighbour-list map (the nhlists argument of CSR\_assn\_raw at line 546
of CSR\_Graph\_Simple.thy).
\<close>
definition build_nhlists :: "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat list option" where
  "build_nhlists es v =
     (if nbrs es v = [] then None else Some (nbrs es v))"

subsection \<open>Basic Properties\<close>

lemma length_build_sindices [simp]: "length (build_sindices es n) = n"
  unfolding build_sindices_def by simp

lemma length_build_eindices [simp]: "length (build_eindices es n) = n"
  unfolding build_eindices_def by simp

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

lemma build_nhlists_val:
  "v \<in> dom (build_nhlists es) \<Longrightarrow> the (build_nhlists es v) = nbrs es v"
  by(auto simp add: build_nhlists_def)

subsection \<open>Vertex Bounds\<close>

lemma foldl_max_ge_acc:
  "foldl (\<lambda>m (e :: nat \<times> nat). max m (fst e)) acc xs \<ge> acc"
  apply (induction xs arbitrary: acc)
   apply (auto simp: le_max_iff_disj )
  using max.bounded_iff by blast

lemma foldl_max_fst_ge:
  "(u, v::nat) \<in> set es \<Longrightarrow>
   foldl (\<lambda>(m::nat) e. max m (fst e)) acc es \<ge> u"
proof (induction es arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons e es')
  show ?case
  proof (cases "(u, v) = e")
    case True
    then have "fst e = u" by auto
    thus ?thesis
      using foldl_max_ge_acc[of "max acc (fst e)" es']
      by (auto simp: le_max_iff_disj intro: order_trans)
  next
    case False
    with Cons.prems have "(u, v) \<in> set es'" by simp
    with Cons.IH show ?thesis by simp
  qed
qed


lemma nverts_source_upper:
  "(u, v) \<in> set es \<Longrightarrow> u < nverts es"
  using foldl_max_fst_ge[of u v es 0]
  unfolding nverts_def by (auto simp: less_Suc_eq_le)

lemma build_nhlists_dom_subset:
  "dom (build_nhlists es) \<subseteq> {0..<nverts es}"
proof
  fix v assume hv: "v \<in> dom (build_nhlists es)"
  have hne: "nbrs es v \<noteq> []"
    using hv unfolding build_nhlists_dom by simp
  have "\<exists>e \<in> set es. fst e = v"
    using hne unfolding nbrs_def
    by (auto simp: filter_empty_conv)
  then obtain e where he: "e \<in> set es" "fst e = v" by blast
  obtain w where "e = (v, w)"
    using he(2) by (cases e) auto
  then have "(v, w) \<in> set es" using he(1) by simp
  thus "v \<in> {0..<nverts es}"
    using nverts_source_upper[of v w es] by simp
qed


subsection \<open>Monotonicity of start\_off\<close>

lemma start_off_mono:
  "v \<le> n \<Longrightarrow> start_off es v \<le> start_off es n"
  by (induction n) (auto simp: start_off_Suc le_Suc_eq)

lemma start_off_lt_total:
  assumes "v < n" "nbrs es v \<noteq> []"
  shows "start_off es v < start_off es n"
proof -
  have "start_off es (Suc v) = start_off es v + length (nbrs es v)"
    by (simp add: start_off_Suc)
  moreover have "start_off es (Suc v) \<le> start_off es n"
    using assms(1) by (intro start_off_mono) simp
  ultimately show ?thesis using assms(2)
    using nat_less_le by fastforce
qed


lemma start_off_end_lt_total:
  assumes "v < n" "nbrs es v \<noteq> []"
  shows "start_off es v + length (nbrs es v) - 1 < start_off es n"
  using start_off_lt_total[OF assms] assms(2) 
  by (metis One_nat_def Suc_le_eq add_gr_0 assms(1)
      length_greater_0_conv nz_le_conv_less start_off_Suc
      start_off_mono)

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

lemma build_nha_nths_vertex_incl:
  assumes "v < n" "nbrs es v \<noteq> []"
  shows "nths (build_nha es n)
              {start_off es v .. start_off es v + length (nbrs es v) - 1}
         = nbrs es v"
proof -
  let ?s = "start_off es v"
  let ?l = "length (nbrs es v)"
  have pos: "0 < ?l" using assms(2) by simp
  have set_eq: "{?s .. ?s + ?l - 1} = {?s ..< ?s + ?l}"
    using pos by (cases ?l) (simp_all add: atLeastLessThanSuc_atLeastAtMost)
  thus ?thesis using build_nha_nths_vertex[OF assms(1)] by simp
qed


subsection \<open>Correctness of the Abstract Construction\<close>

theorem build_CSR_inv:
  assumes n_def: "n = nverts es"
  shows
    "dom (build_nhlists es) \<subseteq> {0..<length (build_sindices es n)} \<and>
     dom (build_nhlists es) \<subseteq> {0..<length (build_eindices es n)} \<and>
     length (build_sindices es n) = length (build_eindices es n) \<and>
     (\<forall>v \<in> dom (build_nhlists es).
         build_sindices es n ! v < length (build_nha es n) \<and>
         build_eindices es n ! v < length (build_nha es n) \<and>
         the (build_nhlists es v) =
           nths (build_nha es n)
                {build_sindices es n ! v .. build_eindices es n ! v}) \<and>
     (\<forall>v. v \<notin> dom (build_nhlists es) \<and> v < n \<longrightarrow>
         build_eindices es n ! v < build_sindices es n ! v)"
proof (intro conjI)
  show "dom (build_nhlists es) \<subseteq> {0..<length (build_sindices es n)}"
       "dom (build_nhlists es) \<subseteq> {0..<length (build_eindices es n)}"
    using build_nhlists_dom_subset n_def by simp_all
  show "length (build_sindices es n) = length (build_eindices es n)"
    by simp
  show "\<forall>v \<in> dom (build_nhlists es).
           build_sindices es n ! v < length (build_nha es n) \<and>
           build_eindices es n ! v < length (build_nha es n) \<and>
           the (build_nhlists es v) =
             nths (build_nha es n)
                  {build_sindices es n ! v .. build_eindices es n ! v}"
  proof
    fix v assume hv: "v \<in> dom (build_nhlists es)"
    have hn: "nbrs es v \<noteq> []"
      using hv by (simp add: build_nhlists_dom)
    have hv_lt: "v < n"
      unfolding n_def
      using build_nhlists_dom_subset hv
      by force
    have si_val: "build_sindices es n ! v = start_off es v"
      unfolding build_sindices_def using hn hv_lt by simp
    have ei_val: "build_eindices es n ! v = start_off es v + length (nbrs es v) - 1"
      unfolding build_eindices_def using hn hv_lt by simp
    have si_lt: "build_sindices es n ! v < length (build_nha es n)"
      using start_off_lt_total[OF hv_lt hn]
      unfolding length_build_nha si_val by assumption
    have ei_lt: "build_eindices es n ! v < length (build_nha es n)"
      using start_off_end_lt_total[OF hv_lt hn]
      unfolding length_build_nha ei_val by assumption
    have nths_eq:
      "the (build_nhlists es v) =
       nths (build_nha es n)
            {build_sindices es n ! v .. build_eindices es n ! v}"
      unfolding si_val ei_val build_nhlists_def
      using hn apply (simp add: build_nha_nths_vertex_incl[OF hv_lt hn])
      using One_nat_def build_nha_nths_vertex_incl hv_lt
      by presburger
      
      from si_lt ei_lt nths_eq show
      "build_sindices es n ! v < length (build_nha es n) \<and>
       build_eindices es n ! v < length (build_nha es n) \<and>
       the (build_nhlists es v) =
         nths (build_nha es n)
              {build_sindices es n ! v .. build_eindices es n ! v}"
      by blast
  qed
  show "\<forall>v. v \<notin> dom (build_nhlists es) \<and> v < n \<longrightarrow>
            build_eindices es n ! v < build_sindices es n ! v"
  proof (intro allI impI, elim conjE)
    fix v assume hdom: "v \<notin> dom (build_nhlists es)" "v < n"
    then have hn: "nbrs es v = []"
      unfolding build_nhlists_dom by simp
    show "build_eindices es n ! v < build_sindices es n ! v"
      unfolding build_sindices_def build_eindices_def
      using hn hdom(2) by simp
  qed
qed

lemma nbrs_append [simp]:
  "nbrs (xs @ ys) v = nbrs xs v @ nbrs ys v"
  unfolding nbrs_def by (simp add: filter_append)

lemma nbrs_singleton:
  "nbrs [(u, w)] v = (if u = v then [w] else [])"
  unfolding nbrs_def by simp

end
