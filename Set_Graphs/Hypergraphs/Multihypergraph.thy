theory Multihypergraph
  imports "Directed_Set_Graphs.enat_misc"
 "HOL-Eisbach.Eisbach_Tools" "HOL-Library.FuncSet" 
    Graph_Theory.Rtrancl_On
begin
subsection \<open>Three Criteria to Classify Graphs\<close>

text \<open>The most general form of a graph is a \textit{multihypergraph}.
\textit{simple} instead of \textit{multi} means uniqueness of edges.
\textit{bigraph} means to have edges with at most two distinct endpoints.
An \textit{undirected} graph is a graph where edges are symmetric.\<close>

(*Multihypergraph --- unique edges ---> Simple Hypergraph
|                                          |
|                                          |
two vertices only                     two vertices only
|                                          |
v                                          v
Multibigraph---------- unique edges ----> Simple Bigraph

3rd dimension (un)directedness by (absence of) symmetry
  *)
subsection \<open>Basic Lists\<close>
lemma induct_pcpl:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y zs. P zs \<Longrightarrow> P (x # y # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

lemma induct_pcpl_2:
  "\<lbrakk>P []; \<And>x. P [x]; \<And>x y. P [x,y]; \<And>x y z. P [x,y,z]; \<And>w x y z zs. P zs \<Longrightarrow> P (w # x # y # z # zs)\<rbrakk> \<Longrightarrow> P xs"
  by induction_schema (pat_completeness, lexicographic_order)

subsection \<open>Definitions to Classify Hypergraphs\<close>

definition "consent conn e e' = (\<forall> u v. conn u e v \<longleftrightarrow> conn u e' v)"

lemma consentI:"(\<And> u v. conn u e v \<Longrightarrow> conn u e' v) \<Longrightarrow>
                (\<And> u v. conn u e' v \<Longrightarrow> conn u e v) \<Longrightarrow> consent conn e e'"
  by(auto simp add: consent_def)

lemma consentE:" consent conn e e' \<Longrightarrow>
               ((\<And> u v. conn u e v \<Longrightarrow> conn u e' v) \<Longrightarrow>
                (\<And> u v. conn u e' v \<Longrightarrow> conn u e v) \<Longrightarrow>P) \<Longrightarrow> P"
  by(auto simp add: consent_def)

lemma consentD[dest]: "consent conn e e' \<Longrightarrow> conn u e v \<Longrightarrow> conn u e' v"
  by(auto simp add: consent_def)

lemma consent_refl[intro]: "consent conn e e"
  by(auto simp add: consent_def)

lemma consent_sym[intro]: "consent conn e e' \<Longrightarrow> consent conn e' e"
  by(auto simp add: consent_def)

lemma consent_trans[intro]: "consent conn e e' \<Longrightarrow> consent conn e' e'' \<Longrightarrow> consent conn e e''"
  by(auto simp add: consent_def)

(*example*)
lemma "consent conn a b \<Longrightarrow> consent conn c b \<Longrightarrow> consent conn a c" 
  by auto

definition "is_simple conn = (\<forall> e e'.  consent conn e e' \<longrightarrow>  e = e')"

lemma is_simpleI: "(\<And> e e'. consent conn e e' \<Longrightarrow> e = e') \<Longrightarrow> is_simple conn"
  by(auto simp add: is_simple_def)

lemma is_simpleE: "is_simple conn \<Longrightarrow> ((\<And> e e'. consent conn e e' \<Longrightarrow> e = e') \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: is_simple_def)

definition "endpoints conn e = \<Union> {{u, v} | u v. conn u e v}"

lemma in_endpointsI: "conn u e v \<Longrightarrow> u \<in> endpoints conn e"
                     "conn u e v \<Longrightarrow> v \<in> endpoints conn e"
  by(auto simp add: endpoints_def)

lemma in_endpointsE: 
"u \<in> endpoints conn e \<Longrightarrow> 
(\<And> v. conn u e v \<Longrightarrow> P) \<Longrightarrow>
(\<And> v. conn v e u \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: endpoints_def)

definition "is_dbltn conn = (\<forall> e. \<exists> u v. endpoints conn e \<subseteq> {u, v})"

lemma is_dbltnI_meta: 
  assumes "(\<And> e P. (\<And> u v. endpoints conn e \<subseteq> {u, v} \<Longrightarrow> P) \<Longrightarrow> P )" 
  shows"is_dbltn conn"
  by(auto simp add: is_dbltn_def intro: assms)

lemma is_dbltnE_meta: 
  assumes "is_dbltn conn" "(\<And> e P. (\<And> u v. endpoints conn e \<subseteq> {u, v} \<Longrightarrow> P) \<Longrightarrow> P) \<Longrightarrow> P" 
  shows P
  using assms(1)
  by(auto simp add: is_dbltn_def intro: assms(2))

lemma is_dbltnI: 
  shows"(\<And> e. \<exists> u v. endpoints conn e \<subseteq> {u, v}) \<Longrightarrow> is_dbltn conn"
  by(auto simp add: is_dbltn_def)

lemma is_dbltnE: 
  assumes "is_dbltn conn" "(\<And> e. \<exists> u v. endpoints conn e \<subseteq> {u, v}) \<Longrightarrow> P" 
  shows P
  using assms(1)
  by(auto simp add: is_dbltn_def intro: assms(2))

definition "is_undirected conn = (\<forall> e u v. conn u e v \<longrightarrow> conn v e u)"

lemma is_undirectedI: "(\<And> e u v. conn u e v \<Longrightarrow> conn v e u) \<Longrightarrow> is_undirected conn"
  by(auto simp add: is_undirected_def)

lemma is_undirectedE: " is_undirected conn \<Longrightarrow> ((\<And> e u v. conn u e v \<Longrightarrow> conn v e u) \<Longrightarrow>P) \<Longrightarrow> P"
  by(auto simp add: is_undirected_def)

term "(+)" 
term sum

lemma is_undirectedD: "is_undirected conn \<Longrightarrow> conn u e v \<Longrightarrow> conn v e u"
  by(auto elim: is_undirectedE)


subsection \<open>General Operations on Hypergraphs\<close>

definition hempty ("\<emptyset>") where "hempty = (\<lambda> _ _ _. False)" 

lemma hempty_no_connection[intro]: "hempty u e v \<Longrightarrow> False"
  by(auto simp add: hempty_def)

definition HUNIV where "HUNIV = (\<lambda> _ _ _. True)"
(*Lattice Instantiation!?*)

definition hsubset ("_ \<sqsubseteq> _" [50, 50])
  where "hsubset conn conn' = (\<forall> e u v. conn u e v \<longrightarrow> conn' u e v)"

abbreviation strict_hsubset (" _ \<sqsubset> _" [50, 50])
  where "strict_hsubset X Y \<equiv> (X \<sqsubseteq> Y \<and> \<not> Y \<sqsubseteq> X)"

lemma hsubsetI[intro?]: "(\<And> e u v. conn  u e v \<Longrightarrow> conn' u e v) \<Longrightarrow> hsubset conn conn'"
  by(auto simp add: hsubset_def)

lemma hsubsetE[elim?]: "conn \<sqsubseteq> conn' \<Longrightarrow>
 ((\<And> e u v. conn  u e v \<Longrightarrow> conn' u e v) \<Longrightarrow> P)\<Longrightarrow>P"
  by(auto simp add: hsubset_def)

lemma hsubset_mp[intro]: "hsubset conn conn' \<Longrightarrow> conn u e v\<Longrightarrow>conn' u e v"
  by(auto simp add: hsubset_def)

lemma hsubset_refl[intro, simp]: "X \<sqsubseteq> X"
  by(auto intro!: hsubsetI)

lemma hsubset_antisym: "X \<sqsubseteq> Y \<Longrightarrow> Y \<sqsubseteq> X \<Longrightarrow> X = Y"
  by(rule ext)+(auto intro!: hsubsetI elim: hsubsetE)

lemma hsubset_trans[intro, dest]: "X \<sqsubseteq> Y \<Longrightarrow> Y \<sqsubseteq> Z \<Longrightarrow> X \<sqsubseteq> Z"
  by(auto intro!: hsubsetI elim!: hsubsetE)

lemma hsubset_hempty[simp, intro]: "\<emptyset> \<sqsubseteq> X"
  by(auto intro!: hsubsetI simp add: hempty_def)

lemma hsubset_huniv[simp, intro]: "X \<sqsubseteq> HUNIV"
  by(auto intro!: hsubsetI simp add: HUNIV_def)

lemma strict_hsubsetI: "X \<sqsubseteq> Y \<Longrightarrow> Y u e v \<Longrightarrow> \<not> X u e v \<Longrightarrow> X \<sqsubset> Y"
  by auto

lemma strict_hsubsetE:
 "X \<sqsubset> Y \<Longrightarrow> (\<And> u e v. X \<sqsubseteq> Y \<Longrightarrow> Y u e v \<Longrightarrow> \<not> X u e v \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: hsubset_def)

lemma hypergraph_eqI: "(\<And> u v e. conn u e v = conn' u e v) \<Longrightarrow> conn = conn'"
                       "(\<And> u v e. conn u e v \<Longrightarrow> conn' u e v) \<Longrightarrow>
                      (\<And> u v e. conn' u e v \<Longrightarrow> conn u e v) \<Longrightarrow> conn = conn'"
  by(auto intro!: ext)

definition hember ("_ \<euro> _" [50, 50]) where
  "e \<euro> conn \<longleftrightarrow> (\<exists> u v. conn u e v)"

lemma hemberI: "conn u e v \<Longrightarrow> e \<euro> conn"
  by(auto simp add: hember_def)

lemma hemberE: "e \<euro> conn \<Longrightarrow> (\<And> u v. conn u e v \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: hember_def)

lemma hember_hempty[simp, intro]: "x \<euro> \<emptyset> \<Longrightarrow> False"
  by(auto simp add: hempty_def hember_def)

lemma hember_huniv[simp]: "x \<euro> HUNIV"
  by(auto simp add: HUNIV_def hember_def)

lemma hypergraph_set_mp[intro]: 
"A \<sqsubseteq> B \<Longrightarrow> x \<euro> A \<Longrightarrow> x \<euro> B"
  by(auto intro!: hemberI elim!: hemberE hsubsetE)

(*example*)
lemma "x \<euro> A \<Longrightarrow>\<not> (x \<euro> B) \<Longrightarrow> \<not> A \<sqsubseteq> B"
  by auto

definition hminus (infixl \<open>\<setminus>\<close> 65) where
 "hminus conn conn' = (\<lambda> u e v. conn u e v \<and> \<not> conn' u e v)"

lemma in_hminusEspecial: "(hminus G G') u e v \<Longrightarrow>
 (G u e v \<Longrightarrow> \<not> G' u e v \<Longrightarrow> P) \<Longrightarrow> P "
  by(auto simp add: hminus_def)

lemma in_hminusI[intro]: "G u e v \<Longrightarrow> \<not> G' u e v \<Longrightarrow> (hminus G G') u e v"
  by(auto simp add: hminus_def)

lemma hminus_hsubset[intro]: "hsubset (hminus G G') G"
  by(auto simp add: hsubset_def hminus_def)

lemma hminus_self_empty: "hminus G G = hempty"
  by(auto simp add: hminus_def hempty_def)

lemma hminus_superset_empty: "G \<sqsubseteq> G' \<Longrightarrow> hminus G G' = hempty"
 by(auto intro!: hypergraph_eqI elim!: in_hminusEspecial)

definition hunion (infixl \<open>\<squnion>\<close> 65) where 
"hunion conn conn' = (\<lambda> u e v. conn u e v \<or> conn' u e v)"

lemma in_hunionI: 
                  "conn u e v \<Longrightarrow> (hunion conn conn') u e v"
                  "conn' u e v \<Longrightarrow> (hunion conn conn') u e v"
  by(auto simp add: hunion_def)

lemma in_hunionE[elim]: 
"(hunion conn conn') u e v \<Longrightarrow>
(conn u e v \<Longrightarrow> P) \<Longrightarrow>
(conn' u e v \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: hunion_def)

term union

lemma hunion_comm[intro?]: "G \<squnion> G' = G' \<squnion> G" 
  by(auto intro: hypergraph_eqI(2) in_hunionE[OF _ in_hunionI(2,1)])

lemma hunion_idem[simp]: "G \<squnion> G = G"
  by(fastforce intro: hypergraph_eqI(2) in_hunionI)

lemma hunion_empty[simp]: "G \<squnion> \<emptyset> = G" " \<emptyset> \<squnion> G= G"
  by(auto intro: hypergraph_eqI(2) in_hunionI  dest: hempty_no_connection)
(*example*)
lemma "(G \<squnion> G) \<squnion> \<emptyset> = G" 
  by simp

lemma hunion_assoc: "F \<squnion> (G \<squnion> H) = F \<squnion> G \<squnion> H" 
  by(auto simp add: hunion_def)

lemma hunion_subset[simp, intro]: "G \<sqsubseteq> G \<squnion> G'"  "G \<sqsubseteq> G' \<squnion> G"
  by(auto simp add: hsubset_def hunion_def)

definition Hunion ("\<Squnion>_" [66]) where "Hunion Conn = (\<lambda> u e v. \<exists> conn \<in> Conn. conn u e v)"

lemma in_HunionI[intro?]: "conn u e v \<Longrightarrow> conn \<in> Conn \<Longrightarrow> (Hunion Conn) u e v"
  by(auto simp add: Hunion_def)

lemma in_HunionE[elim?]: "(Hunion Conn) u e v \<Longrightarrow>
(\<And> conn. conn \<in> Conn \<Longrightarrow> conn u e v \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: Hunion_def)

lemma Hunion_empty: "Hunion {} = \<emptyset>"
  by(auto simp add: Hunion_def)

lemma hunion_Hunion[simp]:  "\<Squnion> {conn, conn'} = conn \<squnion> conn'" 
                            "\<Squnion> (insert conn Conn) = conn \<squnion> \<Squnion> Conn"
  by(simp add: Hunion_def hunion_def)+

definition "hinsert  conn u e v = (\<lambda> u' e' v'. if u = u' \<and> e = e' \<and> v = v' then True
                                    else conn u' e' v')"

lemma in_hinsertI[intro]: "conn u e v \<Longrightarrow> (hinsert conn uu ee vv) u e v"
                   "(hinsert conn u e v) u e v"
  by(auto simp add: hinsert_def)

lemma in_hinsertE[elim]: "(hinsert conn uu ee vv) u e v \<Longrightarrow>
(uu = u \<Longrightarrow> ee = e \<Longrightarrow> vv = v \<Longrightarrow> P) \<Longrightarrow>
(conn u e v \<Longrightarrow> P) \<Longrightarrow>P"
  by(cases "uu = u \<and> ee = e \<and> vv = v")(auto simp add: hinsert_def)

section \<open>Multihypergraphs\<close>

definition "hVs conn = \<Union> {{u, v} | u v. \<exists> e. conn u e v}"

lemma in_hVsI[intro]: "conn u e v \<Longrightarrow> u \<in> hVs conn"
               "conn u e v \<Longrightarrow> v \<in> hVs conn"
  by(auto simp add: hVs_def)

lemma in_hVsE[elim]: 
"x \<in> hVs conn \<Longrightarrow> (\<And> u e. conn x e u \<Longrightarrow> P) \<Longrightarrow>
(\<And> u e. conn u e x \<Longrightarrow> P) \<Longrightarrow> P"
  by(auto simp add: hVs_def)

lemma hvs_member[iff?]: "v \<in> hVs conn\<longleftrightarrow> (\<exists>e u. conn u e v \<or> conn v e u )"
  by(auto simp add: hVs_def)

lemma hVs_empty[simp]: "hVs \<emptyset> = {}" 
  by (auto dest: hempty_no_connection)

lemma hVs_empty_iff[simp]: "hVs E = {} \<longleftrightarrow> E = \<emptyset>"
  by(auto simp add: hVs_def hempty_def intro!: ext) 

definition "hEs conn = {e| e u v. conn u e v}"

lemma in_hEsI:"conn u e v \<Longrightarrow> e \<in> hEs conn"
  by(auto simp add: hEs_def)

lemma in_hEsE:"e \<in> hEs conn \<Longrightarrow> (\<And> u v. conn u e v ==> P) ==> P"
  by(auto simp add: hEs_def)

lemma vs_member_elim[elim?]:
  assumes "v \<in> hVs conn"
  obtains e u where "conn u e v \<or> conn v e u"
  using assms
  by(auto simp add: hVs_def)

lemmas vs_member_intro = in_hVsI

lemma edges_are_Vs:
  assumes "conn v e u"
  shows "v \<in> hVs conn"
  using assms by blast

lemma edges_are_Vs_2:
  assumes  "conn u e v"
  shows "v \<in> hVs conn"
  using assms by blast

lemma edges_are_Vs':
  assumes "\<exists> e. conn v e u"
  shows "v \<in> hVs conn"
  using assms by blast

lemma edges_are_Vs_2':
  assumes  "\<exists> e. conn u e v"
  shows "v \<in> hVs conn"
  using assms by blast

lemma hVs_union_distr[simp]: "hVs (G \<squnion> H) = hVs G \<union> hVs H"
 by(auto elim!: in_hVsE elim: in_hunionE[OF _ in_hVsI] in_hunionE[OF _ in_hVsI(2,1)] 
            intro: in_hVsI(1, 2)[of "_ \<squnion> _", OF in_hunionI(1)] 
                      in_hVsI(1,2)[of "_ \<squnion> _", OF in_hunionI(2)]
            simp add: edges_are_Vs_2)

lemma dVs_union_big_distr: "hVs (\<Squnion> G) = \<Union>(hVs ` G)"
  by(auto elim!: in_HunionE intro: in_hVsI[of "\<Squnion> _", OF in_HunionI(1)])

abbreviation reachable1 :: "('a \<Rightarrow>'e \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>+\<index> _" [100,100] 40) where
  "reachable1 E u v \<equiv> (u,v) \<in> {(u, v) | u e v. E u e v}\<^sup>+"

definition reachable :: "('a \<Rightarrow>'e \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" ("_ \<rightarrow>\<^sup>*\<index> _" [100,100] 40) where
  "reachable E u v = ( (u,v) \<in> rtrancl_on (hVs E) ({(u, v) | u e v. E u e v}))"

lemma reachableE(*[elim?]*):
  assumes "(u,v) \<in> {(u, v) | u e v. E u e v}"
  obtains e where "E u e v"
  using assms by auto

lemma reachable_refl(*[intro!, Pure.intro!, simp]*): "v \<in> hVs E \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  by(auto simp add: reachable_def)

lemma reachable_trans(*[trans,intro]*):
  assumes "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w" shows "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w"
  using assms unfolding reachable_def by (rule rtrancl_on_trans)

lemma reachable1_edge(*[dest,intro]*): "E u e v \<Longrightarrow> u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v"
  by(auto simp add: reachable_def)

lemma reachable_edge(*[dest,intro]*): "E u e v \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  unfolding reachable_def
  by (auto intro!: rtrancl_consistent_rtrancl_on)

lemma reachable_induct[consumes 1, case_names base step]:
  assumes major: "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
    and cases: "\<lbrakk>u \<in> hVs E\<rbrakk> \<Longrightarrow> P u"
      "\<And>x y . \<lbrakk>u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> x; \<exists> e. E x e y; P x\<rbrakk> \<Longrightarrow> P y"
    shows "P v"
  using assms unfolding reachable_def 
  by(rule rtrancl_on_induct) auto

lemma converse_reachable_induct[consumes 1, case_names base step, induct pred: reachable]:
  assumes major: "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
    and cases: "v \<in> hVs E \<Longrightarrow> P v"
      "\<And>x y. \<lbrakk>\<exists> e. E x e y; y \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v; P y\<rbrakk> \<Longrightarrow> P x"
    shows "P u"
  using assms unfolding reachable_def by (rule converse_rtrancl_on_induct) auto

lemma reachable_in_dVs:
  assumes "u \<rightarrow>\<^sup>*\<^bsub>E\<^esub> v"
  shows "u \<in> hVs E" "v \<in> hVs E"
  using assms by (induct) (auto simp add: in_hVsI)

lemma reachable1_in_dVs:
  assumes "u \<rightarrow>\<^sup>+\<^bsub>E\<^esub> v"
  shows "u \<in> hVs E" "v \<in> hVs E"
  using assms by (induct) (auto simp add: in_hVsI)


lemma reachable1_reachable[intro]:
  "v \<rightarrow>\<^sup>+\<^bsub>E\<^esub> w \<Longrightarrow> v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w"
  by(auto intro!: rtrancl_consistent_rtrancl_on intro: reachable1_in_dVs simp add: reachable_def)

lemmas reachable1_reachableE[elim] = reachable1_reachable[elim_format]

lemma reachable_neq_reachable1[intro]:
  assumes reach: "v \<rightarrow>\<^sup>*\<^bsub>E\<^esub> w"
    and neq: "v \<noteq> w"
  shows "v \<rightarrow>\<^sup>+\<^bsub>E\<^esub> w" 
  using assms
  unfolding reachable_def
  by (auto dest: rtrancl_on_rtranclI rtranclD)

lemmas reachable_neq_reachable1E[elim] = reachable_neq_reachable1[elim_format]

definition "neighbourhood G u = {v. \<exists> e. G u e v}"

lemma 
  neighbourhoodD[dest]: "v \<in> (neighbourhood G u) \<Longrightarrow> \<exists> e. G u e v" and
  neighbourhoodI[intro]: "G u e v \<Longrightarrow> v \<in> (neighbourhood G u)" and
  neighbourhoodE[elim]: "v \<in> (neighbourhood G u) \<Longrightarrow> (\<And> e. G u e v \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: neighbourhood_def)

definition "sources G = {u | u v . \<exists> e. G u e v}"

definition "sinks G = {v | u v . \<exists> e. G u e v}"

lemma dVs_subset: "G \<sqsubseteq> G' \<Longrightarrow> hVs G \<subseteq> hVs G'"
  by(auto elim!: in_hVsE intro: vs_member_intro[of G', OF hsubset_mp[of G G']])

lemma dVs_insert[elim]:
  "v\<in> hVs (hinsert G x e y) \<Longrightarrow> \<lbrakk>v = x \<Longrightarrow> P; v = y \<Longrightarrow> P; v \<in> hVs G \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by(auto elim!: in_hVsE)

lemma in_neighbourhood_dVs[simp, intro]:
  "v \<in> neighbourhood G u \<Longrightarrow> v \<in> hVs G"
  by(auto intro: edges_are_Vs_2') 

lemma subset_neighbourhood_dVs[simp, intro]:
  "neighbourhood G u \<subseteq> hVs G"
  by auto

lemma in_dVsE: "v \<in> hVs G \<Longrightarrow> \<lbrakk>(\<And>u e. G u e v \<Longrightarrow> P); (\<And>u e. G v e u \<Longrightarrow> P)\<rbrakk> \<Longrightarrow> P"
               "v \<notin> hVs G \<Longrightarrow> (\<lbrakk>(\<And>u e. \<not> G u e v); (\<And>u e. \<not> G v e u)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  subgoal
    by auto
  subgoal
   by(simp add: hVs_def) blast
  done

lemma neighoubrhood_union[simp]:
 "neighbourhood (G \<squnion> G') u = neighbourhood G u \<union> neighbourhood G' u"
  using neighbourhoodI[of "G \<squnion> G'", OF hsubset_mp[of G "G \<squnion> G'"]]
        neighbourhoodI[of "G \<squnion> G'", OF hsubset_mp[of G' "G \<squnion> G'"]]
  by(fastforce elim!: in_hunionE)

definition reverse ("_\<^sup>\<hookleftarrow>" [70]) where
"reverse conn = (\<lambda> u e v. conn v e u)"

lemma reverse_reverse[simp, intro]: "reverse (reverse G) = G"
  by(auto simp add: reverse_def)

lemma "G\<^sup>\<hookleftarrow>\<^sup>\<hookleftarrow>\<^sup>\<hookleftarrow>\<^sup>\<hookleftarrow>\<^sup>\<hookleftarrow>\<^sup>\<hookleftarrow>\<^sup>\<hookleftarrow>\<^sup>\<hookleftarrow> = G"
  by simp

lemma reverse_hempty[simp, intro]: "reverse \<emptyset> = \<emptyset>" 
  by(auto simp add: reverse_def hempty_def)

lemma reverse_HUNIV[simp, intro]: "reverse HUNIV = HUNIV" 
  by(auto simp add: reverse_def HUNIV_def)

lemma in_reverseI: "G u e v \<Longrightarrow> (reverse G) v e u"
  by(auto simp add: reverse_def)

lemma in_reverseE: "(reverse G) v e u \<Longrightarrow> (G u e v \<Longrightarrow> P ) \<Longrightarrow> P"
  by(auto simp add: reverse_def)

lemma in_reverseD: "(reverse G) v e u \<Longrightarrow> G u e v"
  by(auto simp add: reverse_def)

lemma hVs_reverse: "hVs (reverse G) = hVs G"
  by(auto simp add: hVs_def reverse_def)

lemma reverse_sources_sinks: "sources (reverse G) = sinks G"
                             "sinks (reverse G) = sources G"
  by(auto simp add: sources_def sinks_def reverse_def)

lemma reverse_hsubset: "G \<sqsubseteq> G' \<Longrightarrow> G\<^sup>\<hookleftarrow> \<sqsubseteq> G'\<^sup>\<hookleftarrow>"
  by(auto elim: in_reverseE intro: in_reverseI hsubsetI)

lemma reverse_hunion: "(G \<squnion> G')\<^sup>\<hookleftarrow> = G\<^sup>\<hookleftarrow> \<squnion> G'\<^sup>\<hookleftarrow>"
  by(auto elim!: in_reverseE in_hunionE
         intro!: hypergraph_eqI
          intro: in_reverseI in_hunionI in_reverseD[of G] in_reverseD[of G']) 



inductive hawalk where
"u \<in> hVs conn \<Longrightarrow>  hawalk conn u [] u" |
"conn x e y \<Longrightarrow> hawalk conn y p z \<Longrightarrow> hawalk conn  x (e#p) z"

inductive path where
"u \<in> hVs conn \<Longrightarrow> path conn [u]" |
"conn u e v \<Longrightarrow> path conn (v#p) \<Longrightarrow> path conn (u#v#p)"

lemma vwalk_in_hVs:
"path conn p \<Longrightarrow> set p \<subseteq> hVs conn"
  by(induction rule: path.induct) auto

inductive edges_fitting_to_path where
"edges_fitting_to_path conn [] [u]"|
"conn u e v \<Longrightarrow> edges_fitting_to_path conn es (v#p)
          \<Longrightarrow> edges_fitting_to_path conn (e#es) (u#v#p)"

lemma edges_fitting_first_stepE:
"edges_fitting_to_path conn (e#es) (u#p) \<Longrightarrow> edges_fitting_to_path conn es p"
"edges_fitting_to_path conn (e#es) (u#p) \<Longrightarrow> conn u e (hd p)"
"edges_fitting_to_path conn (e#es) (u#p) \<Longrightarrow> p \<noteq> Nil"
  by(auto elim: edges_fitting_to_path.cases)

lemma hawalk_obtain_fitting_path:
  assumes "hawalk conn x es z" 
  obtains p where "edges_fitting_to_path conn es p" "path conn p" 
                  "hd p = x" "last p = z"
  using assms
proof(induction arbitrary: thesis rule: hawalk.induct)
  case (1 u)
  show ?case 
    by(auto intro!: 1 edges_fitting_to_path.intros path.intros)
next
  case (2 conn x e y p z)
  obtain pa where pa: "edges_fitting_to_path conn p pa"
           "path conn pa"
           "(pa \<noteq> [] \<Longrightarrow> hd pa = y)" "(pa \<noteq> [] \<Longrightarrow> last pa = z)"
    using 2(3) by auto
  show ?case 
    using  pa "2.hyps"(1) 
    by (intro  2(4)[of "x#pa"], all \<open>cases pa\<close>)
       (auto intro:edges_fitting_to_path.intros path.intros 
              elim: edges_fitting_to_path.cases)
qed

lemma path_obtain_fitting_hawalk:
  assumes "path conn p" 
  obtains es where "edges_fitting_to_path conn es p" "hawalk conn (hd p) es (last p)"
  using assms
proof(induction arbitrary: thesis rule: path.induct)
  case (1 u)
  show ?case 
    by(auto intro!: 1 edges_fitting_to_path.intros hawalk.intros)
next
  case (2 conn x e y p)
  obtain es where es: "edges_fitting_to_path conn es (y#p)"
                      "hawalk conn (hd (y # p)) es (last (y # p))"
    using 2(3) by auto
  show ?case 
    using  es "2.hyps"(1) 
    using [[simp_trace]]
    by(auto intro!:2(4)[of "e#es"] 
             intro: edges_fitting_to_path.intros  hawalk.intros
              elim: edges_fitting_to_path.cases)
qed

lemma edges_fitting_to_path_index:
  "Suc i < length p \<Longrightarrow> edges_fitting_to_path conn es p 
              \<Longrightarrow> conn (p!i) (es ! i) (p!Suc i)"
proof(induction i arbitrary: p es)
  case 0
  then obtain u v ps where "p = u#v#ps" 
    by (auto simp: less_eq_Suc_le Suc_le_length_iff)
  thus ?case
    using "0.prems"(2) 
    by (fastforce elim: edges_fitting_to_path.cases)
next
  case (Suc i)
  then obtain u v ps where p_split:"p = u#v#ps"
    by (auto simp: less_eq_Suc_le Suc_le_length_iff)
  then obtain e ees where es_split: "es = e#ees"
    using Suc.prems(2) by(auto elim: edges_fitting_to_path.cases)
  hence "edges_fitting_to_path conn ees (v#ps)"
    using Suc(3) 
    by(auto elim!: edges_fitting_first_stepE simp add: p_split es_split)
  hence "conn ((v#ps) ! i) (ees ! i) ((v#ps) ! Suc i)"
    using Suc.prems(1) 
    by(force intro!:  Suc.IH simp add: p_split)
  thus ?case
    by (simp add: es_split p_split)
qed

lemma fitting_edges_length: "edges_fitting_to_path conn es p \<Longrightarrow> length es + 1 = length p"
  by (induction p rule: edges_fitting_to_path.induct, auto)

lemma hawalk_in_hEs: "hawalk conn x es z \<Longrightarrow> set es \<subseteq> hEs conn"
  by(induction rule: hawalk.induct)(simp add: in_hEsI)+

lemma hawalk_e_in_hEs: "hawalk conn x es z \<Longrightarrow> e \<in> set es ==> e \<in> hEs conn"
  using hawalk_in_hEs by fast

lemma path_ball_edges: "
edges_fitting_to_path conn es p \<Longrightarrow> b \<in> set es \<Longrightarrow> b \<in> hEs conn"
  by(induction rule: edges_fitting_to_path.induct) (auto intro: in_hEsI)

lemma edges_of_path_length: "edges_fitting_to_path conn es p \<Longrightarrow> length es +1 = length p"
  by(induction rule: edges_fitting_to_path.induct) auto

lemma edges_of_path_length': "edges_fitting_to_path conn  es p \<Longrightarrow> length es = length p -1"
  using edges_of_path_length by force

lemma hsubset_hVs: 
  assumes"hsubset conn conn'" 
  shows  "hVs conn \<subseteq> hVs conn'"
proof
  fix x
  assume asm: "x \<in> hVs conn"
  show "x \<in> hVs conn'"
    using in_hVsI[of conn', OF hsubset_mp[OF assms]]
    by (auto intro: in_hVsE[OF asm] hsubsetE[OF assms])
qed

lemma hsubset_awalk: 
  assumes"hsubset conn conn'" "hawalk conn u p v"
  shows  "hawalk conn' u p v"
  using assms(1)
proof(induction rule: hawalk.induct[OF assms(2)])
  case (1 u conn)
  then show ?case 
    by(auto intro!: hawalk.intros(1) set_mp[OF hsubset_hVs[of _ conn']])
next
  case (2 conn x e y p z)
  then show ?case 
    by(auto intro!: hawalk.intros elim!: hsubsetE[of _ conn'] 
               intro!: set_mp[OF hsubset_hVs[of _ conn']])
qed

lemma hVs_hempty: "hVs hempty = {}"
                  "hVs G = {} \<longleftrightarrow> G = hempty"
  using equals0D[of "hVs G"] in_hVsI(1)[of G] 
  by(fastforce simp add: hempty_def elim: in_hVsE)+

lemma hVs_subset:
  "hsubset G  G' \<Longrightarrow> hVs G \<subseteq> hVs G'"
  by(auto intro!: hsubset_hVs)

lemma vs_transport:
  "\<lbrakk>u \<in> hVs G; \<And>e v. G u e v \<Longrightarrow> \<exists>g. F u g v;
       \<And>e v. G v e u \<Longrightarrow> \<exists>g. F v g u\<rbrakk> \<Longrightarrow>u \<in> hVs F"
  using in_hVsI(1)[of F u] in_hVsI(2)[of F _ _ u]
 by(fastforce elim!: in_hVsE)

definition card' :: "'a set \<Rightarrow> enat" where
  "card' A = (if infinite A then \<infinity> else card A)"

lemma card'_finite: "finite A \<Longrightarrow> card' A = card A"
  unfolding card'_def by simp

lemma card'_mono: "A \<subseteq> B \<Longrightarrow> card' A \<le> card' B"
  using finite_subset
  by (auto simp add: card'_def dest: card_mono)

lemma card'_empty[iff]: "(card' A = 0) \<longleftrightarrow> A = {}"
  unfolding card'_def using enat_0_iff(2) by auto

lemma card'_finite_nat[iff]: "(card' A = numeral m) \<longleftrightarrow> (finite A \<and> card A = numeral m)"
  unfolding card'_def
  by (simp add: numeral_eq_enat)

lemma card'_finite_enat[iff]: "(card' A = enat m) \<longleftrightarrow> (finite A \<and> card A = m)"
  unfolding card'_def by simp

lemma card'_1_singletonE:
  assumes "card' A = 1"
  obtains x where "A = {x}"
  using assms
  unfolding card'_def
  by (fastforce elim!: card_1_singletonE dest: iffD1[OF enat_1_iff(1)] split: if_splits)

lemma card'_insert[simp]: "card' (insert a A) = (if a \<in> A then id else eSuc) (card' A)"
  using card_insert_if finite_insert
  by (simp add: card_insert_if card'_def)

lemma card'_empty_2[simp]: "card' {} = enat 0"
  by (simp add: card'_def)

definition "delta G u = {e | e v. G u e v} "

lemma in_deltaI: "G u e v \<Longrightarrow> e \<in> delta G u"
  by(auto simp add: delta_def)

lemma in_deltaE: " e \<in> delta G u \<Longrightarrow>(\<And> v. G u e v \<Longrightarrow> P)  \<Longrightarrow> P"
  by(auto simp add: delta_def)

definition degree where
  "degree G v = card' (delta G v)"

lemma degree_def2: "degree G u \<equiv> card' ({e | e v. G u e v})"
 by(simp add: degree_def delta_def)

lemma degree_not_Vs: "v \<notin> hVs G \<Longrightarrow> degree G v = 0"
  by(auto simp only: hVs_def degree_def delta_def)

lemma degree_hempty[simp]: "degree hempty a = 0"
  by (simp add: degree_def zero_enat_def delta_def hempty_def)

lemma subset_edges_less_degree:
  "hsubset G' G \<Longrightarrow> degree G' v \<le> degree G v"
  by (force intro!: card'_mono simp: degree_def delta_def elim!: hsubsetE)

lemma less_edges_less_degree:  "degree (hminus G  G') v \<le> degree G v"
  by (auto intro!: subset_edges_less_degree hminus_hsubset)
end