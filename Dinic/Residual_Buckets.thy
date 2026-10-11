theory Residual_Buckets
  imports
    Flow_Theory.Residual
    Directed_Set_Graphs.More_Lists
    "HOL-Data_Structures.Map_Specs"
begin

section \<open>Residual Edges Grouped by Pairs of Vertices\<close>

text \<open>A residual graph is a multigraph. A search on its projection to pairs of vertices needs, for
every pair, the residual edges realising it. We store these lists in a map from pairs of vertices
to lists of residual edges.\<close>

locale residual_buckets_spec =
  flow_network_spec where fst = fst  +
  Map_realising: Map realising_edges_empty
  "realising_edges_update::('v\<times> 'v) \<Rightarrow> ('e Redge) list \<Rightarrow> 'realising_type \<Rightarrow> 'realising_type"
   realising_edges_delete realising_edges_lookup realising_edges_invar
for fst::"'e \<Rightarrow> 'v" and realising_edges_empty realising_edges_update
  realising_edges_delete realising_edges_lookup realising_edges_invar
begin

definition "realising_edges_general list =
           (foldr (\<lambda> e found_edges. let ee = to_vertex_pair e in
                     (case realising_edges_lookup found_edges ee of 
                      None \<Rightarrow> realising_edges_update ee [e] found_edges
                     |Some ds \<Rightarrow> realising_edges_update ee (e#ds) found_edges))
            list realising_edges_empty)"

lemmas [code] = realising_edges_general_def

lemma realising_edges_invar_pres: "realising_edges_invar (realising_edges_general list)"
  unfolding realising_edges_general_def
  by(auto intro: foldr_invar 
      simp add: Map_realising.invar_empty Map_realising.invar_update realising_edges_general_def
        Let_def
      split: option.split)

lemma realising_edges_general_result_None_and_Some:
  assumes "(case realising_edges_lookup (realising_edges_general list) (u, v) 
            of Some ds \<Rightarrow> ds 
               | None \<Rightarrow> [])= ds"
  shows "set ds = {e | e. e \<in> set list \<and> to_vertex_pair e = (u, v)}"
  using assms
proof(induction list arbitrary: ds)
  case Nil
  then show ?case 
    by (auto simp add: realising_edges_general_def  Map_realising.map_empty 
        split: option.split)
next
  case (Cons a list ds)
  show ?case 
    using Map_realising.map_update[OF  realising_edges_invar_pres] Cons(1)[OF refl] 
    by (auto intro: realising_edges_invar_pres 
        simp add: Map_realising.map_update realising_edges_general_def Cons(2)[symmetric] Let_def
        split: option.split)
qed

lemma realising_edges_general_result_distinct:
  assumes "distinct list"
    "(case realising_edges_lookup (realising_edges_general list) (u, v) 
            of Some ds \<Rightarrow> ds 
               | None \<Rightarrow> [])= ds"
  shows "distinct ds"
  using assms
proof(induction list arbitrary: ds u v)
  case Nil
  then show ?case 
    by (auto simp add: realising_edges_general_def  Map_realising.map_empty 
        split: option.split)
next
  case (Cons e list ds u v)
  let ?M = "realising_edges_general list"
  have distlist: "distinct list" and e: "e \<notin> set list"
    using Cons.prems(1) by auto
  have gen: "realising_edges_general (e # list) =
      (case realising_edges_lookup ?M (to_vertex_pair e) of
         None \<Rightarrow> realising_edges_update (to_vertex_pair e) [e] ?M
       | Some ds' \<Rightarrow> realising_edges_update (to_vertex_pair e) (e # ds') ?M)"
    by (simp only: realising_edges_general_def foldr_Cons o_apply Let_def)
  have upd: "realising_edges_lookup (realising_edges_update k d ?M) =
      (realising_edges_lookup ?M)(k := Some d)" for k d
    by (rule Map_realising.map_update[OF realising_edges_invar_pres])
  have IH: "distinct (case realising_edges_lookup ?M (u, v) of Some ds \<Rightarrow> ds | None \<Rightarrow> [])"
    by (rule Cons.IH[OF distlist refl])
  have sub: "e \<notin> set ds'" if "realising_edges_lookup ?M (u, v) = Some ds'" for ds'
    using realising_edges_general_result_None_and_Some[OF refl, of list u v] e that by auto
  show ?case
  proof (cases "to_vertex_pair e = (u, v)")
    case True
    then show ?thesis
      unfolding Cons.prems(2)[symmetric] gen
      using IH sub by (auto simp: upd split: option.split)
  next
    case False
    then show ?thesis
      unfolding Cons.prems(2)[symmetric] gen
      using IH by (auto simp: upd split: option.split)
  qed
qed

lemma realising_edges_general_result:
  assumes "realising_edges_lookup (realising_edges_general list) (u, v) = Some ds"
  shows "set ds = {e | e. e \<in> set list \<and> to_vertex_pair e = (u, v)}"
  using realising_edges_general_result_None_and_Some[of list u v ds] assms
  by simp

text \<open>The residual edges realising a pair of vertices.\<close>

definition "bucket bkt d = (case realising_edges_lookup bkt d of None \<Rightarrow> [] | Some ds \<Rightarrow> ds)"

lemmas [code] = bucket_def

lemma bucket_update:
  "realising_edges_invar m \<Longrightarrow>
    bucket (realising_edges_update d L m) d' = (if d' = d then L else bucket m d')"
  by (simp add: bucket_def Map_realising.map_update)

lemma bucket_general:
  "set (bucket (realising_edges_general list) d) = {e. e \<in> set list \<and> to_vertex_pair e = d}"
  "distinct list \<Longrightarrow> distinct (bucket (realising_edges_general list) d)"
proof -
  obtain u v where d: "d = (u, v)"
    by (cases d)
  show "set (bucket (realising_edges_general list) d) = {e. e \<in> set list \<and> to_vertex_pair e = d}"
    using realising_edges_general_result_None_and_Some[OF refl, of list u v]
    unfolding bucket_def d by blast
  show "distinct (bucket (realising_edges_general list) d)" if "distinct list"
    using realising_edges_general_result_distinct[OF that refl, of u v]
    unfolding bucket_def d .
qed

end

end
