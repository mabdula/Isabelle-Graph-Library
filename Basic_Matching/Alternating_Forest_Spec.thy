theory Alternating_Forest_Spec
  imports Matching
begin

section \<open>Specification of Executable Alternating Forest\<close>

locale alternating_forest_spec = 
  fixes evens::"'forest \<Rightarrow> 'vset"
    and odds::"'forest \<Rightarrow> 'vset"
    and get_path::"'forest \<Rightarrow> 'v \<Rightarrow> 'v list"
    and abstract_forest::"'forest \<Rightarrow> 'v set set"
    and forest_invar::"'v set set \<Rightarrow> 'forest \<Rightarrow> bool"
    and roots::"'forest \<Rightarrow> 'vset"
    and vset_invar::"'vset \<Rightarrow> bool"
    and vset_to_set::"'vset \<Rightarrow> 'v set"
  assumes evens_and_odds:
 "\<And> F M. forest_invar M F\<Longrightarrow> vset_invar (evens F)"
 "\<And> F M. forest_invar M F\<Longrightarrow> vset_invar (odds F)"
 "\<And> F M. forest_invar M F
      \<Longrightarrow> vset_to_set (evens F) \<union> vset_to_set (odds F) = 
          vset_to_set (roots F) \<union> Vs (abstract_forest F)"
  "\<And> F M. forest_invar M F\<Longrightarrow> 
       (vset_to_set (evens F))\<inter>(vset_to_set (odds F)) = {}"
and finite_forest:
 "\<And> F M. forest_invar M F\<Longrightarrow> finite (vset_to_set (evens F))"
 "\<And> F M. forest_invar M F\<Longrightarrow> finite (vset_to_set (odds F))"
 "\<And> F M. forest_invar M F\<Longrightarrow> finite (abstract_forest F)"
and roots:
   "\<And> F M. forest_invar M F \<Longrightarrow> vset_invar (roots F)" 
   "\<And> F M. forest_invar M F \<Longrightarrow> vset_to_set (roots F) \<subseteq> vset_to_set (evens F)" 
   "\<And> F M. forest_invar M F \<Longrightarrow> vset_to_set (roots F) \<inter> Vs M = {}" 
and get_path:
    "\<And> F M v p. \<lbrakk>forest_invar M F; v \<in> vset_to_set (evens F); p = get_path F v\<rbrakk> \<Longrightarrow>
           rev_alt_path M p \<and> odd (length p) \<and>
           last p \<in> vset_to_set (roots F) \<and>
           (walk_betw (abstract_forest F) v p (last p) \<or> p = [v]) \<and>
           distinct p"
and higher_forest_properties:
    "\<And> F M. forest_invar M F\<Longrightarrow> 
       card (vset_to_set (evens F)) > card (vset_to_set (odds F))"
    "\<And> F M u v. \<lbrakk>forest_invar M F; {u, v} \<in> M\<rbrakk>\<Longrightarrow>
        {u, v} \<in> abstract_forest F \<or> 
          {u, v} \<inter> (Vs (abstract_forest F) \<union> vset_to_set (roots F)) = {}"
    "\<And> F M u v. \<lbrakk>forest_invar M F; {u, v} \<in> abstract_forest F\<rbrakk>\<Longrightarrow>
               u \<in> vset_to_set (evens F) \<longleftrightarrow> v \<in> vset_to_set (odds F)"
begin
definition "forest_extension_precond F M x y z =
      (forest_invar M F \<and> x \<in> vset_to_set (evens F) \<and>
        {y, z} \<inter> (vset_to_set (evens F) \<union> vset_to_set (odds F)) = {} \<and>
        {x, y} \<notin> M \<and> {y, z} \<in> M \<and>  matching M \<and> x \<noteq> y \<and>  y \<noteq> z \<and> x \<noteq> z)"

lemma forest_extension_precondI:
"\<lbrakk>forest_invar M F; x \<in> vset_to_set (evens F);
  {y, z} \<inter> (vset_to_set (evens F) \<union> vset_to_set (odds F)) = {};
  {x, y} \<notin> M; {y, z} \<in> M; matching M;
  x \<noteq> y; y \<noteq> z; x \<noteq> z\<rbrakk>
\<Longrightarrow>forest_extension_precond F M x y z "
  by(auto simp add: forest_extension_precond_def)
end

locale alternating_forest_ordinary_extension_spec = 
alternating_forest_spec evens odds get_path abstract_forest forest_invar roots
    for evens::"'forest \<Rightarrow> 'vset"
    and odds::"'forest \<Rightarrow> 'vset"
    and get_path::"'forest \<Rightarrow> 'v \<Rightarrow> 'v list"
    and abstract_forest::"'forest \<Rightarrow> 'v set set"
    and forest_invar::"'v set set \<Rightarrow> 'forest \<Rightarrow> bool"
    and roots::"'forest \<Rightarrow> 'vset"
    and vset_empty::'vset +
  fixes extend_forest_even_unclassified::
        "'forest \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'forest"
   and empty_forest::"'vset \<Rightarrow> 'forest"
  assumes forest_extend: "\<And> F M x y z. forest_extension_precond F M x y z
      \<Longrightarrow> forest_invar M (extend_forest_even_unclassified F x y z)"
   "\<And> F M x y z. forest_extension_precond F M x y z
      \<Longrightarrow> abstract_forest (extend_forest_even_unclassified F x y z) =
          abstract_forest F \<union> {{x, y}, {y, z}}"
   "\<And> F M x y z. forest_extension_precond F M x y z
      \<Longrightarrow> vset_to_set (evens (extend_forest_even_unclassified F x y z)) =
          insert z (vset_to_set (evens F))"
   "\<And> F M x y z. forest_extension_precond F M x y z
      \<Longrightarrow> vset_to_set (odds (extend_forest_even_unclassified F x y z)) =
          insert y (vset_to_set (odds F))"
   "\<And> F M x y z. forest_extension_precond F M x y z
      \<Longrightarrow> vset_to_set (roots (extend_forest_even_unclassified F x y z)) =
          vset_to_set (roots F)"
and empty_forest:
    "\<And> R. evens (empty_forest R) = R"
    "\<And> R. odds (empty_forest R) = vset_empty"
    "\<And> R. abstract_forest (empty_forest R) = {}"
    "\<And> R M. \<lbrakk>matching M; vset_invar R; vset_to_set R \<inter> Vs M = {}; 
           finite (vset_to_set R); vset_to_set R \<noteq> {}\<rbrakk>
          \<Longrightarrow> forest_invar M (empty_forest R)"

end