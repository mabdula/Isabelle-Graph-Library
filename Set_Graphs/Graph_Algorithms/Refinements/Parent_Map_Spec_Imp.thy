theory Parent_Map_Spec_Imp
  imports Separation_Logic_Imperative_HOL_Partial.Sep_Main Graph_Algorithms_Dev.Parent_Map_Spec
begin

section \<open>Imperative Parent Maps\<close>

text \<open>The imperative counterparts of the locales of @{theory Graph_Algorithms_Dev.Parent_Map_Spec}.
      The parent map is refined by the assertion @{term parent_assn}. Initialisation and extension
      work in place, so that the parent map can be allocated once by the caller. Each locale only
      adds one operation; clients combine those they need, sharing @{term parent_assn}.\<close>

text \<open>Path reconstruction: the path from @{term s} to its root is written into the array
      @{term Ra} given by the caller, from position @{term k} on. The result is the position after
      the last vertex written.\<close>

locale Parent_Map_Spec_static_imp =
  Parent_Map_Spec_static where U = U and to_dir_graph = to_dir_graph and get_path = get_path
    and invar = invar and roots = roots
  for U :: "'v::heap set"
    and to_dir_graph :: "'pmap \<Rightarrow> ('v \<times> 'v) set"
    and get_path :: "'pmap \<Rightarrow> 'v \<Rightarrow> 'v list"
    and invar :: "'pmap \<Rightarrow> bool"
    and roots :: "'pmap \<Rightarrow> 'v set" +
  fixes parent_assn :: "'pmap \<Rightarrow> 'pmapi \<Rightarrow> assn"
    and get_path_imp :: "'pmapi \<Rightarrow> 'v array \<Rightarrow> nat \<Rightarrow> 'v \<Rightarrow> nat Heap"
  assumes get_path_rule:
    "\<And> \<pi> \<pi>i Ra r k s.
       \<lbrakk>invar \<pi>; s \<in> dVs (to_dir_graph \<pi>) \<union> roots \<pi>; k + length (get_path \<pi> s) \<le> length r\<rbrakk> \<Longrightarrow>
       <parent_assn \<pi> \<pi>i * Ra \<mapsto>\<^sub>a r> get_path_imp \<pi>i Ra k s
       <\<lambda>k'. parent_assn \<pi> \<pi>i *
             Ra \<mapsto>\<^sub>a (take k r @ get_path \<pi> s @ drop (k + length (get_path \<pi> s)) r) *
             \<up>(k' = k + length (get_path \<pi> s))>"

text \<open>Initialisation in place: whatever the parent map held before, afterwards it has the given
      roots and no edges.\<close>

locale Parent_Map_Spec_init_imp =
  Parent_Map_Spec_init where U = U and to_dir_graph = to_dir_graph and invar = invar
    and roots = roots and vset_abstract = vset_abstract and init = init and vset_invar = vset_invar
  for U :: "'v set"
    and to_dir_graph :: "'pmap \<Rightarrow> ('v \<times> 'v) set"
    and invar :: "'pmap \<Rightarrow> bool"
    and roots :: "'pmap \<Rightarrow> 'v set"
    and vset_abstract :: "'vset \<Rightarrow> 'v set"
    and init :: "'vset \<Rightarrow> 'pmap"
    and vset_invar :: "'vset \<Rightarrow> bool" +
  fixes parent_assn :: "'pmap \<Rightarrow> 'pmapi \<Rightarrow> assn"
    and vset_assn :: "'vset \<Rightarrow> 'vseti \<Rightarrow> assn"
    and init_imp :: "'vseti \<Rightarrow> 'pmapi \<Rightarrow> unit Heap"
  assumes init_rule:
    "\<And> \<pi> \<pi>i R Ri. \<lbrakk>vset_invar R; vset_abstract R \<subseteq> U\<rbrakk> \<Longrightarrow>
       <parent_assn \<pi> \<pi>i * vset_assn R Ri> init_imp Ri \<pi>i
       <\<lambda>_. parent_assn (init R) \<pi>i * vset_assn R Ri>"

text \<open>Extension in place by the edge from @{term v} to its parent @{term u}.\<close>

locale Parent_Map_Spec_extend_imp =
  Parent_Map_Spec_extend where U = U and to_dir_graph = to_dir_graph and extend = extend
    and invar = invar and roots = roots
  for U :: "'v set"
    and to_dir_graph :: "'pmap \<Rightarrow> ('v \<times> 'v) set"
    and extend :: "'pmap \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'pmap"
    and invar :: "'pmap \<Rightarrow> bool"
    and roots :: "'pmap \<Rightarrow> 'v set" +
  fixes parent_assn :: "'pmap \<Rightarrow> 'pmapi \<Rightarrow> assn"
    and extend_imp :: "'pmapi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> unit Heap"
  assumes extend_rule:
    "\<And> \<pi> \<pi>i u v. \<lbrakk>invar \<pi>; v \<in> U - dVs (to_dir_graph \<pi>) - roots \<pi>;
                 u \<in> dVs (to_dir_graph \<pi>) \<union> roots \<pi>\<rbrakk> \<Longrightarrow>
       <parent_assn \<pi> \<pi>i> extend_imp \<pi>i u v <\<lambda>_. parent_assn (extend \<pi> u v) \<pi>i>"

end
