theory Laminar_Spec
  imports Laminar_Family
begin

locale laminar_family_spec = 
  fixes all_ids:: "'L \<Rightarrow> 'id set"
   and  universe:: "'L \<Rightarrow> 'v set"
   and  collect_elems:: "'L \<Rightarrow> 'id \<Rightarrow> 'v set"
   and  max_ids:: "'L \<Rightarrow> 'id set"
   and laminar_invar:: "'L \<Rightarrow> bool"
   and laminar_abstract::"'L \<Rightarrow> 'v set set"
   and compound::"'L \<Rightarrow> 'id \<Rightarrow> bool"
 assumes 
  elems_in_universe:
   "\<And> L i. \<lbrakk>laminar_invar L; i \<in> all_ids L\<rbrakk> \<Longrightarrow> collect_elems L i \<subseteq> universe L"
  and max_ids:
    "\<And> L . laminar_invar L \<Longrightarrow> 
       max_ids L = {i | i. i \<in> all_ids L \<and> collect_elems L i \<in> maximal_sets (laminar_abstract L)}"
  and laminarity:
     "\<And> L. laminar_invar L \<Longrightarrow>  laminar (universe L) (collect_elems L ` (all_ids L))"
  and collect_elems_bijection:
     "\<And> L. laminar_invar L \<Longrightarrow> bij_betw (collect_elems L) (all_ids L) (laminar_abstract L)"  
  and "\<And> L id. \<lbrakk>laminar_invar L; compound L id\<rbrakk> \<Longrightarrow> card (collect_elems L id) > 1"
begin

definition "laminar_merge_precond L ls new_id = 
 (laminar_invar L \<and> set ls \<subseteq> max_ids L \<and> length ls \<ge> 2 \<and> distinct ls \<and> new_id \<notin> all_ids L)"

lemma laminar_merge_precondI:
  "\<lbrakk>laminar_invar L; set ls \<subseteq> max_ids L; length ls \<ge> 2; distinct ls; new_id \<notin> all_ids L\<rbrakk> \<Longrightarrow> laminar_merge_precond L ls new_id"
  unfolding laminar_merge_precond_def by simp

lemma laminar_merge_precondE:
  "\<lbrakk>laminar_merge_precond L ls new_id; 
       \<lbrakk>laminar_invar L; set ls \<subseteq> max_ids L; length ls \<ge> 2; distinct ls; new_id \<notin> all_ids L\<rbrakk> \<Longrightarrow> P\<rbrakk>
     \<Longrightarrow> P"
  unfolding laminar_merge_precond_def by blast

lemma laminar_merge_precondD:
  "laminar_merge_precond L ls new_id \<Longrightarrow> laminar_invar L"
  "laminar_merge_precond L ls new_id \<Longrightarrow> set ls \<subseteq> max_ids L"
  "laminar_merge_precond L ls new_id \<Longrightarrow> length ls \<ge> 2"
  "laminar_merge_precond L ls new_id \<Longrightarrow> distinct ls"
  "laminar_merge_precond L ls new_id \<Longrightarrow> new_id \<notin> all_ids L"
  unfolding laminar_merge_precond_def by simp_all

definition "laminar_unmerge_precond L id = 
 (laminar_invar L \<and> id \<in> max_ids L \<and> card (collect_elems L id) > 1)" for id

lemma laminar_unmerge_precondI:
  "\<lbrakk>laminar_invar L; id \<in> max_ids L; card (collect_elems L id) > 1\<rbrakk> 
   \<Longrightarrow> laminar_unmerge_precond L id" for id
  unfolding laminar_unmerge_precond_def by simp

lemma laminar_unmerge_precondE:
  "\<lbrakk>laminar_unmerge_precond L id; 
     \<lbrakk>laminar_invar L; id \<in> max_ids L; card (collect_elems L id) > 1\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" for id
  unfolding laminar_unmerge_precond_def by blast

lemma laminar_unmerge_precondD:
  "laminar_unmerge_precond L id \<Longrightarrow> laminar_invar L"
  "laminar_unmerge_precond L id \<Longrightarrow> id \<in> max_ids L"
  "laminar_unmerge_precond L id \<Longrightarrow> card (collect_elems L id) > 1"for id
  unfolding laminar_unmerge_precond_def by simp_all

end

locale laminar_merge_spec =
 laminar_family_spec where collect_elems = collect_elems
for collect_elems:: "'L \<Rightarrow> 'id \<Rightarrow> 'v set" + 
fixes merge::"'L \<Rightarrow> 'id list \<Rightarrow> 'id \<Rightarrow> 'L"
assumes merge_spec: 
"\<And> L ls new_id. laminar_merge_precond L ls new_id 
  \<Longrightarrow> laminar_invar (merge L ls new_id)"
"\<And> L ls new_id. laminar_merge_precond L ls new_id 
  \<Longrightarrow> all_ids (merge L ls new_id) = insert new_id (all_ids L)"
"\<And> L ls new_id. laminar_merge_precond L ls new_id 
  \<Longrightarrow> universe (merge L ls new_id) = universe L"
"\<And> L ls new_id. laminar_merge_precond L ls new_id 
  \<Longrightarrow> collect_elems (merge L ls new_id) = 
      (\<lambda> i. if i = new_id 
            then \<Union> ((collect_elems L) ` (set ls))
            else collect_elems L i)"
"\<And> L ls new_id. laminar_merge_precond L ls new_id 
  \<Longrightarrow> max_ids (merge L ls new_id) = max_ids L - set ls \<union> {new_id}"
"\<And> L ls new_id. laminar_merge_precond L ls new_id 
  \<Longrightarrow> laminar_abstract (merge L ls new_id) = 
     insert (\<Union> ((collect_elems L) ` (set ls))) (laminar_abstract L)"

locale laminar_unmerge_spec =
 laminar_family_spec where collect_elems = collect_elems
for collect_elems:: "'L \<Rightarrow> 'id \<Rightarrow> 'v set" + 
fixes unmerge::"'L \<Rightarrow> 'id \<Rightarrow> 'L \<times> 'id list"
assumes unmerge_spec: 
"\<And> L id L' ids. \<lbrakk>laminar_unmerge_precond L id; unmerge L id = (L', ids)\<rbrakk>
        \<Longrightarrow> laminar_invar L'"
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
        \<Longrightarrow> distinct ids"
"\<And> L id L' ids. \<lbrakk>laminar_unmerge_precond L id; unmerge L id = (L', ids)\<rbrakk>
        \<Longrightarrow> length ids \<ge> 2"

locale laminar_iteration_spec =
 laminar_family_spec where collect_elems = collect_elems
for collect_elems:: "'L \<Rightarrow> 'id \<Rightarrow> 'v set" + 
fixes max_qualified_iteration :: 
    "('id \<Rightarrow> bool) \<Rightarrow>'L \<Rightarrow> ('acc1 \<Rightarrow> 'id \<Rightarrow> 'acc1) \<Rightarrow> 'acc1 \<Rightarrow> 'acc1"
and elems_iteration :: "'L \<Rightarrow> 'id \<Rightarrow> ('acc2 \<Rightarrow> 'v \<Rightarrow> 'acc2) \<Rightarrow> 'acc2 \<Rightarrow> 'acc2"
assumes max_qualified_iteration:
  "\<And> P L f acc. laminar_invar L \<Longrightarrow>
       \<exists> ids. set ids = {id | id mid. mid \<in> max_ids L
          \<and> collect_elems L id \<subseteq> collect_elems L mid \<and> P mid 
          \<and> id \<in> all_ids L}
          \<and> distinct ids \<and> max_qualified_iteration P L f acc = foldl f acc ids"
and elems_iteration: 
  "\<And> L id f acc. laminar_invar L \<Longrightarrow>
       \<exists> elems. set elems = collect_elems L id \<and> distinct elems
               \<and> elems_iteration L id f acc = foldl f acc elems"
end