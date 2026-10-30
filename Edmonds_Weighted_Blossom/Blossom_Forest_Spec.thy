theory Blossom_Forest_Spec
  imports Laminar_Family.Laminar_Spec Undirected_Set_Graphs.Paths
begin

locale blossom_forest_spec =
 laminar_family_spec where collect_elems = collect_elems
 and laminar_invar = blossom_forest_invar
for collect_elems:: "'L \<Rightarrow> 'id \<Rightarrow> 'v set" and blossom_forest_invar+ 
fixes blossom_edges::"'L \<Rightarrow> 'id set set" 
assumes odd_sets: "\<And> L i. \<lbrakk>blossom_forest_invar L; i \<in> all_ids L\<rbrakk> \<Longrightarrow> odd (card (collect_elems L i))"
and blossom_edges: 
  "\<And> L . blossom_forest_invar L \<Longrightarrow> dblton_graph (blossom_edges L)"
  "\<And> L . blossom_forest_invar L \<Longrightarrow> Vs (blossom_edges L) \<subseteq> all_ids L"
  "\<And> L i j. \<lbrakk>blossom_forest_invar L; {i, j} \<in> blossom_edges L\<rbrakk>
       \<Longrightarrow> \<exists> m \<in> max_ids L. collect_elems L i \<union> collect_elems L j \<subseteq> collect_elems L m"
begin

definition "blossom_forest_merge_precond L ls new_id = 
 (laminar_merge_precond L ls new_id \<and> odd (length ls))"

lemma blossom_forest_merge_precondI:
  "\<lbrakk>blossom_forest_invar L; set ls \<subseteq> max_ids L; length ls \<ge> 2;
      distinct ls; new_id \<notin> all_ids L; odd (length ls)\<rbrakk> \<Longrightarrow> blossom_forest_merge_precond L ls new_id"
  unfolding laminar_merge_precond_def blossom_forest_merge_precond_def by simp

lemma blossom_forest_merge_precondE:
  "\<lbrakk>blossom_forest_merge_precond L ls new_id; 
       \<lbrakk>blossom_forest_invar L; set ls \<subseteq> max_ids L; length ls \<ge> 2; distinct ls; new_id \<notin> all_ids L; odd (length ls)\<rbrakk> \<Longrightarrow> P\<rbrakk>
     \<Longrightarrow> P"
  unfolding laminar_merge_precond_def blossom_forest_merge_precond_def by blast

lemma blossom_forest_merge_precondD:
  "blossom_forest_merge_precond L ls new_id \<Longrightarrow> blossom_forest_invar L"
  "blossom_forest_merge_precond L ls new_id \<Longrightarrow> set ls \<subseteq> max_ids L"
  "blossom_forest_merge_precond L ls new_id \<Longrightarrow> length ls \<ge> 3"
  "blossom_forest_merge_precond L ls new_id \<Longrightarrow> distinct ls"
  "blossom_forest_merge_precond L ls new_id \<Longrightarrow> new_id \<notin> all_ids L"
  "blossom_forest_merge_precond L ls new_id \<Longrightarrow> odd (length ls)"
  unfolding laminar_merge_precond_def blossom_forest_merge_precond_def by auto presburger

abbreviation "blossom_forest_unmerge_precond \<equiv> laminar_unmerge_precond"

lemmas blossom_forest_unmerge_precondI = laminar_unmerge_precondI
lemmas blossom_forest_unmerge_precondE = laminar_unmerge_precondE
lemmas blossom_forest_unmerge_precondD = laminar_unmerge_precondD

end

locale blossom_forest_merge_spec =
 blossom_forest_spec where collect_elems = collect_elems
for collect_elems:: "'L \<Rightarrow> 'id \<Rightarrow> 'v set" + 
fixes merge::"'L \<Rightarrow> 'id list \<Rightarrow> 'id \<Rightarrow> 'L"
assumes merge_spec: 
"\<And> L ls new_id. blossom_forest_merge_precond L ls new_id 
  \<Longrightarrow> blossom_forest_invar (merge L ls new_id)"
"\<And> L ls new_id. blossom_forest_merge_precond L ls new_id 
  \<Longrightarrow> all_ids (merge L ls new_id) = insert new_id (all_ids L)"
"\<And> L ls new_id. blossom_forest_merge_precond L ls new_id 
  \<Longrightarrow> universe (merge L ls new_id) = universe L"
"\<And> L ls new_id. blossom_forest_merge_precond L ls new_id 
  \<Longrightarrow> collect_elems (merge L ls new_id) = 
      (\<lambda> i. if i = new_id 
            then \<Union> ((collect_elems L) ` (set ls))
            else collect_elems L i)"
"\<And> L ls new_id. blossom_forest_merge_precond L ls new_id 
  \<Longrightarrow> max_ids (merge L ls new_id) = max_ids L - set ls \<union> {new_id}"
"\<And> L ls new_id. blossom_forest_merge_precond L ls new_id 
  \<Longrightarrow> laminar_abstract (merge L ls new_id) = 
     insert (\<Union> ((collect_elems L) ` (set ls))) (laminar_abstract L)"
"\<And> L ls new_id. blossom_forest_merge_precond L ls new_id \<Longrightarrow>
     blossom_edges (merge L ls new_id) = 
     set (edges_of_path (ls@[hd ls])) \<union> blossom_edges L"

locale blossom_forest_unmerge_spec =
 blossom_forest_spec where collect_elems = collect_elems
for collect_elems:: "'L \<Rightarrow> 'id \<Rightarrow> 'v set" + 
fixes unmerge::"'L \<Rightarrow> 'id \<Rightarrow> 'L \<times> 'id list"
assumes unmerge_spec: 
"\<And> L id L' ids. \<lbrakk>laminar_unmerge_precond L id; unmerge L id = (L', ids)\<rbrakk>
        \<Longrightarrow> blossom_forest_invar L'"
"\<And> L id L' ids. \<lbrakk>laminar_unmerge_precond L id; unmerge L id = (L', ids)\<rbrakk>
        \<Longrightarrow> all_ids L' = all_ids L - {id}"
"\<And> L id L' ids. \<lbrakk>laminar_unmerge_precond L id; unmerge L id = (L', ids)\<rbrakk>
        \<Longrightarrow> universe L' = universe L"
"\<And> L id L' ids id'. \<lbrakk>laminar_unmerge_precond L id; unmerge L id = (L', ids);
                 id' \<in> all_ids L - {id}\<rbrakk>
        \<Longrightarrow> collect_elems L' id' = collect_elems L id'"
"\<And> L id L' ids. \<lbrakk>laminar_unmerge_precond L id; unmerge L id = (L', ids)\<rbrakk>
        \<Longrightarrow> max_ids L' = max_ids L - {id} \<union> set ids"
"\<And> L id L' ids. \<lbrakk>laminar_unmerge_precond L id; unmerge L id = (L', ids)\<rbrakk>
        \<Longrightarrow> laminar_abstract L' = laminar_abstract L - {collect_elems L id}"
"\<And> L id L' ids. \<lbrakk>laminar_unmerge_precond L id; unmerge L id = (L', ids)\<rbrakk>
        \<Longrightarrow>  blossom_edges L' = blossom_edges L - set (edges_of_path (ids@[hd ids]))"
"\<And> L id L' ids. \<lbrakk>laminar_unmerge_precond L id; unmerge L id = (L', ids)\<rbrakk>
        \<Longrightarrow>  set (edges_of_path (ids@[hd ids])) \<subseteq> blossom_edges L"
"\<And> L id L' ids. \<lbrakk>laminar_unmerge_precond L id; unmerge L id = (L', ids)\<rbrakk>
        \<Longrightarrow>  distinct ids"
"\<And> L id L' ids. \<lbrakk>laminar_unmerge_precond L id; unmerge L id = (L', ids)\<rbrakk>
        \<Longrightarrow> length ids \<ge> 3"
"\<And> L id L' ids. \<lbrakk>laminar_unmerge_precond L id; unmerge L id = (L', ids)\<rbrakk>
        \<Longrightarrow> odd (length ids)"

locale blossom_forest_iteration_spec =
 blossom_forest_spec where collect_elems = collect_elems
for collect_elems:: "'L \<Rightarrow> 'id \<Rightarrow> 'v set" + 
fixes max_qualified_iteration :: 
    "('id \<Rightarrow> bool) \<Rightarrow>'L \<Rightarrow> ('acc1 \<Rightarrow> 'id \<Rightarrow> 'acc1) \<Rightarrow> 'acc1 \<Rightarrow> 'acc1"
and elems_iteration :: "'L \<Rightarrow> 'id \<Rightarrow> ('acc2 \<Rightarrow> 'v \<Rightarrow> 'acc2) \<Rightarrow> 'acc2 \<Rightarrow> 'acc2"
assumes max_qualified_iteration:
  "\<And> P L f acc. blossom_forest_invar L \<Longrightarrow>
       \<exists> ids. set ids = {id | id mid. mid \<in> max_ids L
          \<and> collect_elems L id \<subseteq> collect_elems L mid \<and> P mid 
          \<and> id \<in> all_ids L}
          \<and> distinct ids \<and> max_qualified_iteration P L f acc = foldl f acc ids"
and elems_iteration: 
  "\<And> L id f acc. blossom_forest_invar L \<Longrightarrow>
       \<exists> elems. set elems = collect_elems L id \<and> distinct elems
               \<and> elems_iteration L id f acc = foldl f acc elems"
end