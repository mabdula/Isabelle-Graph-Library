theory Alternating_Forest_Executable
  imports  Graph_Algorithms_Dev.Parent_Map  Alternating_Forest_Spec
begin
hide_const verts
section \<open>Executable Alternating Forest\<close>

subsection \<open>Implementation in Locale\<close>
datatype ('roots, 'evens, 'odds, 'parents, 'origin) alt_forest =
  Forest (roots: 'roots) (evens: 'evens) (odds: 'odds) (parents: 'parents) (origins: 'origin)

locale forest_manipulation_spec = 
parent_map: Map parent_empty parent_upd parent_delete parent_lookup parent_invar +
origin_map: Map origin_empty origin_upd origin_delete origin_lookup origin_invar +
vset: Set vset_empty vset_insert vset_delete vset_isin vset_to_set vset_invar
for parent_empty and parent_upd::"'v\<Rightarrow>'v\<Rightarrow>'parent\<Rightarrow>'parent"
and  parent_delete parent_lookup parent_invar
and origin_empty and origin_upd::"'v\<Rightarrow>'v\<Rightarrow>'origin\<Rightarrow>'origin" 
and origin_delete origin_lookup origin_invar
and vset_empty and vset_insert::"'v \<Rightarrow> 'vset \<Rightarrow> 'vset"
and  vset_delete vset_isin vset_to_set vset_invar +
fixes  vset_iterate::"('origin \<Rightarrow> 'v \<Rightarrow> 'origin)
             \<Rightarrow> 'origin \<Rightarrow> 'vset \<Rightarrow> 'origin"
begin

definition 
  "empty_forest roots = (Forest roots roots vset_empty parent_empty 
     (vset_iterate (\<lambda> m r. origin_upd r r m) origin_empty roots))" for roots

definition "extend_forest_even_unclassified (F::('vset, 'vset, 'vset, 'parent, 'origin) alt_forest) x y z= 
(Forest (roots F)
        (vset_insert z (evens F))
        (vset_insert y (odds F))
        (parent_upd z y (parent_upd y x (parents F))))
        (let r = the (origin_lookup (origins F) x)
             in origin_upd z r (origin_upd y r (origins F)))"


definition  "get_path F = (\<lambda> x. follow_impl (parent_lookup (parents F)) x)"

definition "abstract_forest F = {{x, y} | x y . parent_lookup (parents F) x = Some y}"


lemmas [code] = empty_forest_def extend_forest_even_unclassified_def
  get_path_def

end

subsection \<open>Locale for Proofs\<close>

locale forest_manipulation =  
  forest_manipulation_spec +
  assumes vseta:
    "\<And> V f init. vset_invar V \<Longrightarrow> 
          \<exists> vs. vset_to_set V = set vs \<and> distinct vs \<and>
            vset_iterate f init V = foldl f init vs"
begin

lemmas vset =
 vset.invar_empty
 vset.set_empty
 vset.invar_insert
 vset.set_insert
 vset.set_isin
 vseta

lemmas parent =
 parent_map.invar_empty
 parent_map.map_empty
 parent_map.invar_update
 parent_map.map_update

lemmas origin = 
 origin_map.invar_empty
 origin_map.map_empty
 origin_map.invar_update
 origin_map.map_update

subsection \<open>The Invariants\<close>

abbreviation "verts F \<equiv> vset_to_set (roots F) \<union> Vs (abstract_forest F)"

definition "invar_basic \<M>= 
(\<lambda> F. vset_invar (roots F) \<and>
      vset_invar (evens F) \<and>
      vset_invar (odds F)\<and>
      parent_invar (parents F) \<and>
      origin_invar (origins F) \<and>
      vset_to_set (evens F) \<union> vset_to_set (odds F) =
           vset_to_set (roots F) \<union> Vs (abstract_forest F) \<and>
           vset_to_set (evens F) \<inter> vset_to_set (odds F) = {} \<and>
           finite (vset_to_set (evens F)) \<and>
           finite (vset_to_set (odds F)) \<and>
           vset_to_set (roots F) \<subseteq> vset_to_set (evens F) \<and>
           vset_to_set (roots F) \<inter> Vs \<M> = {} \<and>
         card (vset_to_set (odds F)) < card (vset_to_set (evens F)) \<and>
         dom (parent_lookup (parents F)) = dom (origin_lookup (origins F)) - vset_to_set (roots F) \<and>
         dom (parent_lookup (parents F)) \<subseteq> Vs (abstract_forest F) \<and>
         origin_lookup (origins F) ` ( vset_to_set (roots F) \<union> Vs (abstract_forest F)) =
         Some ` (vset_to_set (roots F)) \<and>
         Vs (abstract_forest F) - Vs \<M> \<subseteq> vset_to_set (roots F) \<and>
         finite (abstract_forest F))" 

lemma invar_basicE:
  "invar_basic \<M> F \<Longrightarrow>
 (\<lbrakk> vset_invar (roots F);  vset_invar (evens F); vset_invar (odds F);
    parent_invar (parents F); origin_invar (origins F);
       vset_to_set (evens F) \<union> vset_to_set (odds F) =
           vset_to_set (roots F) \<union> Vs (abstract_forest F);
           vset_to_set (evens F) \<inter> vset_to_set (odds F) = {};
           finite (vset_to_set (evens F)); finite (vset_to_set (odds F));
           vset_to_set (roots F) \<subseteq> vset_to_set (evens F);
           vset_to_set (roots F) \<inter> Vs \<M> = {};
         card (vset_to_set (odds F)) < card (vset_to_set (evens F));
         dom (parent_lookup (parents F)) = dom (origin_lookup (origins F)) - vset_to_set (roots F);
         dom (parent_lookup (parents F)) \<subseteq> Vs (abstract_forest F);
         origin_lookup (origins F) ` ( vset_to_set (roots F) \<union> Vs (abstract_forest F)) =
         Some ` (vset_to_set (roots F));
         Vs (abstract_forest F) - Vs \<M>  \<subseteq> vset_to_set (roots F);
         finite (abstract_forest F)\<rbrakk> 
     \<Longrightarrow> P)
\<Longrightarrow> P"
  and invar_basicI:
  "\<lbrakk> vset_invar (roots F);  vset_invar (evens F); vset_invar (odds F);
    parent_invar (parents F); origin_invar (origins F);
       vset_to_set (evens F) \<union> vset_to_set (odds F) =
           vset_to_set (roots F) \<union> Vs (abstract_forest F);
           vset_to_set (evens F) \<inter> vset_to_set (odds F) = {};
           finite (vset_to_set (evens F)); finite (vset_to_set (odds F));
           vset_to_set (roots F) \<subseteq> vset_to_set (evens F);
           vset_to_set (roots F) \<inter> Vs \<M> = {};
         card (vset_to_set (odds F)) < card (vset_to_set (evens F));
         dom (parent_lookup (parents F)) = dom (origin_lookup (origins F)) - vset_to_set (roots F);
         dom (parent_lookup (parents F)) \<subseteq> Vs (abstract_forest F);
         origin_lookup (origins F) ` ( vset_to_set (roots F) \<union> Vs (abstract_forest F)) =
         Some ` (vset_to_set (roots F));
         Vs (abstract_forest F) - Vs \<M>  \<subseteq> vset_to_set (roots F);
         finite (abstract_forest F)\<rbrakk> 
     \<Longrightarrow> invar_basic \<M> F"
  and invar_basicD:
  "invar_basic \<M> F \<Longrightarrow>  vset_invar (roots F)"
  "invar_basic \<M> F \<Longrightarrow>  vset_invar (evens F)"
  "invar_basic \<M> F \<Longrightarrow> vset_invar (odds F)"
  "invar_basic \<M> F \<Longrightarrow> parent_invar (parents F)" 
  "invar_basic \<M> F \<Longrightarrow>  origin_invar (origins F)"
  "invar_basic \<M> F \<Longrightarrow> vset_to_set (evens F) \<union> vset_to_set (odds F) =
           vset_to_set (roots F) \<union> Vs (abstract_forest F)"
  "invar_basic \<M> F \<Longrightarrow> vset_to_set (evens F) \<inter> vset_to_set (odds F) = {}"
  "invar_basic \<M> F \<Longrightarrow> finite (vset_to_set (evens F))"
  "invar_basic \<M> F \<Longrightarrow>  finite (vset_to_set (odds F))"
  "invar_basic \<M> F \<Longrightarrow>  vset_to_set (roots F) \<subseteq> vset_to_set (evens F)"
  "invar_basic \<M> F \<Longrightarrow>  vset_to_set (roots F) \<inter> Vs \<M> = {}"
  "invar_basic \<M> F \<Longrightarrow> card (vset_to_set (odds F)) < card (vset_to_set (evens F))"
  "invar_basic \<M> F \<Longrightarrow> 
  dom (parent_lookup (parents F)) = dom (origin_lookup (origins F)) - vset_to_set (roots F)"
  "invar_basic \<M> F \<Longrightarrow> dom (parent_lookup (parents F)) \<subseteq> Vs (abstract_forest F)"
  "invar_basic \<M> F \<Longrightarrow>origin_lookup (origins F) ` ( vset_to_set (roots F) \<union> Vs (abstract_forest F)) =
         Some ` (vset_to_set (roots F))"
  "invar_basic \<M> F \<Longrightarrow>Vs (abstract_forest F) - Vs \<M>  \<subseteq> vset_to_set (roots F)"
  "invar_basic \<M> F \<Longrightarrow>finite (abstract_forest F)"
  by(force simp add: invar_basic_def)+
(*similar to blossom*)
definition "invar_matching_both_or_none \<M> F =
           (\<forall>  u v . {u, v} \<in> \<M> \<longrightarrow>
              {u, v} \<in> abstract_forest F \<or>
            {u, v} \<inter> (Vs (abstract_forest F) \<union> vset_to_set (roots F)) = {})"

lemma invar_matching_both_or_noneE:
  "invar_matching_both_or_none \<M> F \<Longrightarrow>
  ((\<And> u v. {u, v} \<in> \<M> \<Longrightarrow>
              {u, v} \<in> abstract_forest F \<or>
              {u, v} \<inter> (Vs (abstract_forest F) \<union> vset_to_set (roots F)) = {}) \<Longrightarrow> P)
  \<Longrightarrow> P"
and invar_matching_both_or_noneI:
  "(\<And> u v. {u, v} \<in> \<M> \<Longrightarrow> {u, v} \<in> abstract_forest F \<or>
            {u, v} \<inter> (Vs (abstract_forest F) \<union> vset_to_set (roots F)) = {})
   \<Longrightarrow> invar_matching_both_or_none \<M> F"
and invar_matching_both_or_noneD:
  "\<lbrakk>invar_matching_both_or_none \<M> F ;  {u, v} \<in> \<M>\<rbrakk>
  \<Longrightarrow> {u, v} \<in> abstract_forest F \<or>
      {u, v} \<inter> (Vs (abstract_forest F) \<union> vset_to_set (roots F)) = {}"
  by(auto simp add: invar_matching_both_or_none_def)
(*similar to blossom*)
definition "invar_forest_even_and_odd F =
         (\<forall> u v. {u, v} \<in> abstract_forest  F \<longrightarrow>
            (u \<in> vset_to_set (evens F)) = (v \<in> vset_to_set (odds F)))"

lemma invar_forest_even_and_oddE:
  "invar_forest_even_and_odd F \<Longrightarrow>
  ((\<And> u v. {u, v} \<in> abstract_forest  F \<Longrightarrow>
            (u \<in> vset_to_set (evens F)) = (v \<in> vset_to_set (odds F))) \<Longrightarrow> P)
 \<Longrightarrow> P"
  and invar_forest_even_and_oddI:
  "(\<And> u v. {u, v} \<in> abstract_forest  F \<Longrightarrow>
            (u \<in> vset_to_set (evens F)) = (v \<in> vset_to_set (odds F))) 
 \<Longrightarrow> invar_forest_even_and_odd F"
  and invar_forest_even_and_oddD:
  "\<lbrakk>invar_forest_even_and_odd F;  {u, v} \<in> abstract_forest  F\<rbrakk>
  \<Longrightarrow>(u \<in> vset_to_set (evens F)) = (v \<in> vset_to_set (odds F))"
  by(auto simp add: invar_forest_even_and_odd_def)
(*similar to blossom*)
definition "invar_parent_wf F = parent_spec (parent_lookup (parents F))"

lemma invar_parent_wfE:
  "\<lbrakk>invar_parent_wf F; parent_spec (parent_lookup (parents F)) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
and invar_parent_wfI:
  "parent_spec (parent_lookup (parents F)) \<Longrightarrow> invar_parent_wf F"
and invar_parent_wfD:
  "invar_parent_wf F \<Longrightarrow> parent_spec (parent_lookup (parents F))"
  by(auto simp add: invar_parent_wf_def)

definition "invar_even_to_parent_matching \<M> F =
             (\<forall> u v.  u \<in> vset_to_set (evens F) \<and>parent_lookup (parents F) u = Some v 
                     \<longrightarrow> {u, v} \<in> \<M>)"

lemma invar_even_to_parent_matchingE:
  "invar_even_to_parent_matching \<M> F \<Longrightarrow>
  ((\<And> u v . \<lbrakk>u \<in> vset_to_set (evens F); parent_lookup (parents F) u = Some v \<rbrakk> \<Longrightarrow> {u, v} \<in> \<M>)
    \<Longrightarrow> P)
  \<Longrightarrow> P"
and invar_even_to_parent_matchingI:
  "(\<And> u v . \<lbrakk>u \<in> vset_to_set (evens F); parent_lookup (parents F) u = Some v \<rbrakk> \<Longrightarrow> {u, v} \<in> \<M>)
   \<Longrightarrow> invar_even_to_parent_matching \<M> F"
and invar_even_to_parent_matchingD:
  "\<lbrakk>invar_even_to_parent_matching \<M> F; u \<in> vset_to_set (evens F); 
    parent_lookup (parents F) u = Some v \<rbrakk>
   \<Longrightarrow> {u, v} \<in> \<M>"
  by(auto simp add: invar_even_to_parent_matching_def)

definition "invar_odd_to_parent_non_matching \<M> F =
             (\<forall>  u \<in> vset_to_set (odds F). (\<exists> v. parent_lookup (parents F) u = Some v 
                      \<and> {u, v} \<notin> \<M>))"

lemma invar_odd_to_parent_non_matchingE:
  "invar_odd_to_parent_non_matching \<M> F \<Longrightarrow>
  ((\<And> u . u \<in> vset_to_set (odds F) \<Longrightarrow> \<exists> v. parent_lookup (parents F) u = Some v \<and> {u, v} \<notin> \<M>)
     \<Longrightarrow> P)
   \<Longrightarrow> P"
and invar_odd_to_parent_non_matchingI:
  "(\<And> u . u \<in> vset_to_set (odds F) \<Longrightarrow> \<exists> v. parent_lookup (parents F) u = Some v \<and> {u, v}  \<notin> \<M>)
   \<Longrightarrow> invar_odd_to_parent_non_matching \<M> F"
and invar_odd_to_parent_non_matchingD:
  "\<lbrakk>invar_odd_to_parent_non_matching \<M> F; u \<in> vset_to_set (odds F); parent_lookup (parents F) u = Some v \<rbrakk>
  \<Longrightarrow> {u, v}  \<notin> \<M>"
  by(auto simp add: invar_odd_to_parent_non_matching_def)

definition "invar_roots F = 
   ((\<forall> r \<in> vset_to_set (roots F). origin_lookup (origins F) r = Some r) \<and>
    (\<forall> v \<in> verts F. origin_lookup (origins F) v = Some (last (follow (parent_lookup (parents F)) v))) \<and>
    (\<forall> v \<in> verts F. \<forall> u \<in> set (follow (parent_lookup (parents F)) v).
           origin_lookup (origins F) v = origin_lookup (origins F) u) \<and>
    (\<forall> v \<in> verts F. set (edges_of_path (follow (parent_lookup (parents F)) v)) \<subseteq> abstract_forest F))"

lemma invar_rootsE:
  "invar_roots F \<Longrightarrow> 
  (\<lbrakk>\<And> r. r \<in> vset_to_set (roots F) \<Longrightarrow> origin_lookup (origins F) r = Some r;
    \<And> v. v \<in> verts F \<Longrightarrow> origin_lookup (origins F) v = Some (last (follow (parent_lookup (parents F)) v));
    \<And> v u. \<lbrakk>v \<in> verts F; u \<in> set (follow (parent_lookup (parents F)) v)\<rbrakk> \<Longrightarrow>
           origin_lookup (origins F) v = origin_lookup (origins F) u;
    \<And> v. v \<in>  verts F \<Longrightarrow> set (edges_of_path (follow (parent_lookup (parents F)) v)) \<subseteq> abstract_forest F\<rbrakk>
      \<Longrightarrow> P)
   \<Longrightarrow> P"
and invar_rootsI:
  " \<lbrakk>\<And> r. r \<in> vset_to_set (roots F) \<Longrightarrow> origin_lookup (origins F) r = Some r;
     \<And> v. v \<in> verts F \<Longrightarrow> origin_lookup (origins F) v = Some (last (follow (parent_lookup (parents F)) v));
     \<And> v u. \<lbrakk>v \<in> verts F; u \<in> set (follow (parent_lookup (parents F)) v)\<rbrakk> \<Longrightarrow>
           origin_lookup (origins F) v = origin_lookup (origins F) u;
    \<And> v. v \<in> verts F \<Longrightarrow> set (edges_of_path (follow (parent_lookup (parents F)) v)) \<subseteq> abstract_forest F\<rbrakk>
   \<Longrightarrow> invar_roots F"
  and invar_rootsD:
  "\<lbrakk>invar_roots F ; r \<in> vset_to_set (roots F)\<rbrakk> \<Longrightarrow> origin_lookup (origins F) r = Some r"
  "\<lbrakk>invar_roots F; v \<in> verts F\<rbrakk>
   \<Longrightarrow> origin_lookup (origins F) v = Some (last (follow (parent_lookup (parents F)) v))"
  "\<lbrakk>invar_roots F; v \<in> verts F; u \<in> set (follow (parent_lookup (parents F)) v)\<rbrakk>
   \<Longrightarrow>origin_lookup (origins F) v = origin_lookup (origins F) u"
  "\<lbrakk>invar_roots F; v \<in> verts F\<rbrakk> 
   \<Longrightarrow> set (edges_of_path (follow (parent_lookup (parents F)) v)) \<subseteq> abstract_forest F"
  by(auto simp add: invar_roots_def)

lemma follow_dom_invar_parent_wf:
  assumes "invar_parent_wf F"
  shows "parent (parent_lookup (parents F))" 
        "parent_spec_i.follow_dom (parent_lookup (parents F)) v"
proof-
  show ths1: "parent (parent_lookup (parents F))"
    by (simp add: assms invar_parent_wfD parent.intro)
  show "parent_spec_i.follow_dom (parent_lookup (parents F)) v"
    apply(rule parent_spec.wf_follow_rel)
    using assms
    unfolding parent.parent_eq_follow_rel[OF ths1] invar_parent_wf_def  parent_spec_def
    by simp
qed

lemma path_follow_verts_in_verts_F:
  assumes "invar_basic M F" "invar_roots F" "invar_parent_wf F" "v \<in> verts F"
  shows "set (follow (parent_lookup (parents F)) v) \<subseteq> verts F" 
proof-
  obtain xs where xs: "follow (parent_lookup (parents F)) v = v#xs"
    unfolding follow_def
    apply(subst (asm)  parent_spec.follow.psimps[OF follow_dom_invar_parent_wf(2), OF assms(3)]) 
    by(cases "parent_lookup (parents F) v") auto
  show ?thesis
  proof(cases xs)
    case Nil
    then show ?thesis 
      using assms(4) xs by auto
  next
    case (Cons a list)
    show ?thesis 
    proof(rule, goal_cases)
      case (1 x)
      thus ?case
        using  Vs_subset[OF invar_rootsD(4)[OF assms(2) assms(4) ]]
          in_edges_of_path'[of x "v#xs", simplified Cons, simplified] 
        by(auto simp add: xs Cons )
    qed
  qed
qed


definition "forest_invar \<M> F = 
   (invar_basic \<M> F \<and> 
    invar_matching_both_or_none \<M> F \<and>
    invar_forest_even_and_odd F \<and> 
    invar_parent_wf F \<and>
    invar_even_to_parent_matching \<M> F \<and>
    invar_odd_to_parent_non_matching \<M> F \<and>
    invar_roots F)"

lemma forest_invarE:
  "forest_invar \<M> F \<Longrightarrow>
  (\<lbrakk>invar_basic \<M> F; invar_matching_both_or_none \<M> F; invar_forest_even_and_odd F;
    invar_parent_wf F; invar_even_to_parent_matching \<M> F; invar_roots F;
    invar_odd_to_parent_non_matching \<M> F\<rbrakk> \<Longrightarrow> P)
   \<Longrightarrow> P"
and forest_invarI:
  "\<lbrakk>invar_basic \<M> F; invar_matching_both_or_none \<M> F; invar_forest_even_and_odd F;
    invar_parent_wf F; invar_even_to_parent_matching \<M> F; invar_roots F;
    invar_odd_to_parent_non_matching \<M> F\<rbrakk> \<Longrightarrow> forest_invar \<M> F"
and forest_invarD:
  "forest_invar \<M> F \<Longrightarrow> invar_basic \<M> F"
  "forest_invar \<M> F \<Longrightarrow> invar_matching_both_or_none \<M> F"
  "forest_invar \<M> F \<Longrightarrow> invar_forest_even_and_odd F"
  "forest_invar \<M> F \<Longrightarrow> invar_parent_wf F"
  "forest_invar \<M> F \<Longrightarrow> invar_even_to_parent_matching \<M> F"
  "forest_invar \<M> F \<Longrightarrow> invar_roots F"
  "forest_invar \<M> F \<Longrightarrow> invar_odd_to_parent_non_matching \<M> F"
  by(auto simp add: forest_invar_def)

definition "forest_extension_precond F M x y z =
      (forest_invar M F \<and> x \<in> vset_to_set (evens F) \<and>
        {y, z} \<inter> (vset_to_set (evens F) \<union> vset_to_set (odds F)) = {} \<and>
        {x, y} \<notin> M \<and> {y, z} \<in> M \<and> matching M \<and> x \<noteq> y \<and>  y \<noteq> z \<and> x \<noteq> z)"

lemma forest_extension_precondE:
  "forest_extension_precond F M x y z \<Longrightarrow>
  (\<lbrakk>forest_invar M F; x \<in> vset_to_set (evens F); 
   {y, z} \<inter> (vset_to_set (evens F) \<union> vset_to_set (odds F)) = {};
   {x, y} \<notin> M; {y, z} \<in> M; matching M; x \<noteq> y; y \<noteq> z; x \<noteq> z\<rbrakk> \<Longrightarrow> P)
   \<Longrightarrow> P"
  and forest_extension_precondI:
  "\<lbrakk>forest_invar M F; x \<in> vset_to_set (evens F); 
   {y, z} \<inter> (vset_to_set (evens F) \<union> vset_to_set (odds F)) = {};
   {x, y} \<notin> M; {y, z} \<in> M; matching M; x \<noteq> y; y \<noteq> z; x \<noteq> z\<rbrakk> 
   \<Longrightarrow> forest_extension_precond F M x y z"
  and forest_extension_precondD:
  "forest_extension_precond F M x y z \<Longrightarrow> forest_invar M F"
  "forest_extension_precond F M x y z \<Longrightarrow>  x \<in> vset_to_set (evens F)"
  "forest_extension_precond F M x y z 
   \<Longrightarrow> {y, z} \<inter> (vset_to_set (evens F) \<union> vset_to_set (odds F)) = {}"
  "forest_extension_precond F M x y z \<Longrightarrow>{x, y} \<notin> M"
  "forest_extension_precond F M x y z \<Longrightarrow>{y, z} \<in> M"
  "forest_extension_precond F M x y z \<Longrightarrow> matching M"
  "forest_extension_precond F M x y z \<Longrightarrow> x \<noteq> y"
  "forest_extension_precond F M x y z \<Longrightarrow> y \<noteq> z"
  "forest_extension_precond F M x y z \<Longrightarrow> x \<noteq> z"
  by(auto simp add: forest_extension_precond_def)

subsection \<open>Invariant Preservation and Ordinary Forest Extension\<close>

lemma 
  assumes "forest_extension_precond F \<M> x y z"
  shows  extension_main_preservation: "forest_invar \<M> (extend_forest_even_unclassified F x y z)"
    and extension_abstract_is:  "abstract_forest (extend_forest_even_unclassified F x y z) = 
                      abstract_forest F \<union> {{x, y}, {y, z}}"
    and extension_evens: "vset_to_set (evens (extend_forest_even_unclassified F x y z)) =
                             insert z (vset_to_set (evens F))"
    and extension_odds: "vset_to_set (odds (extend_forest_even_unclassified F x y z)) =
                             insert y (vset_to_set (odds F))"
    and extension_roots: "roots (extend_forest_even_unclassified F x y z) = roots F"
    and parent_lookup_is: "parent_lookup (parents (extend_forest_even_unclassified F x y z))
                            = (parent_lookup (parents F))(y \<mapsto> x, z \<mapsto> y)"
    and origins_lookup_is: "origin_lookup (origins (extend_forest_even_unclassified F x y z))
                            = (origin_lookup (origins F))(y \<mapsto> the (origin_lookup (origins F) x),
                                                          z \<mapsto>  the (origin_lookup (origins F) x))"
proof-
  note extension_precond = forest_extension_precondD[OF assms]
  note assms = assms extension_precond(1)
  note invars_old = forest_invarD[OF assms(2)]
  note invar_basic_old = invar_basicD[OF invars_old(1)]
  note new_parent_lookup = parent(4)[OF parent(3), OF invar_basic_old(4),
      simplified parent(4)[OF invar_basic_old(4)], of z y y x]
  have neither_even_not_odd_no_parent:
    "x \<notin> vset_to_set (evens F) \<union> vset_to_set (odds F) \<Longrightarrow>
       \<nexists> y. parent_lookup (parents F) x = Some y \<or> parent_lookup (parents F) y = Some x" for x
  proof(rule ccontr, goal_cases)
    case 1
    then obtain y where "parent_lookup (parents F) x = Some y \<or> parent_lookup (parents F) y = Some x" by auto
    hence "{y, x} \<in> abstract_forest F" by(auto simp add: abstract_forest_def)
    hence "x \<in> Vs (abstract_forest F)" by auto
    hence "x \<in> vset_to_set (evens F) \<union> vset_to_set (odds F)"
      by (simp add: invar_basic_old(6))
    then show ?case 
      using 1 by simp
  qed
  have x_in_F: "x \<in> vset_to_set (roots F) \<union> Vs (abstract_forest F)"
    using extension_precond(2) invar_basic_old(6) by auto
  show new_abstract_is: 
    "abstract_forest (extend_forest_even_unclassified F x y z) = 
     abstract_forest F \<union> {{x, y}, {y, z}}"
    using extension_precond(3,8,9,7)  neither_even_not_odd_no_parent[of y] 
      neither_even_not_odd_no_parent[of z] 
    by (fastforce simp add: extend_forest_even_unclassified_def abstract_forest_def  
        new_parent_lookup  doubleton_eq_iff if_split[of "\<lambda> x. x = _"  " _ = y"] 
        if_split[of "\<lambda> x. x = Some _"  " _ = z"]) 
  show extension_evens: "vset_to_set (evens (extend_forest_even_unclassified F x y z)) =
                             insert z (vset_to_set (evens F))"
    by(simp add: extend_forest_even_unclassified_def invar_basic_old(2) vset(4))
  show extension_odds: "vset_to_set (odds (extend_forest_even_unclassified F x y z)) =
                             insert y (vset_to_set (odds F))"
    by (simp add: extend_forest_even_unclassified_def invar_basic_old(3) vset(4))
  show extension_roots: "roots (extend_forest_even_unclassified F x y z) = roots F"
    by(auto simp add: extend_forest_even_unclassified_def)
  show parent_lookup_is: "parent_lookup (parents (extend_forest_even_unclassified F x y z))
                            = (parent_lookup (parents F))(y \<mapsto> x, z \<mapsto> y)"
    by (simp add: extend_forest_even_unclassified_def new_parent_lookup)
  show origins_lookup_is: "origin_lookup (origins (extend_forest_even_unclassified F x y z))
                            = (origin_lookup (origins F))(y \<mapsto> the (origin_lookup (origins F) x),
                                                          z \<mapsto>  the (origin_lookup (origins F) x))"
    using invar_basic_old(5)
    by(auto simp add: extend_forest_even_unclassified_def origin(3,4) Let_def)
  have y_and_z_no_roots: "y \<notin> vset_to_set (roots F)" "z \<notin> vset_to_set (roots F)"
    using extension_precond(3,4) invar_basic_old(10) by auto
  have invar_basic_new: "invar_basic \<M> (extend_forest_even_unclassified F x y z)"
  proof(rule invar_basicI, goal_cases)
    case 1
    then show ?case
      by (simp add: invar_basic_old(1) extend_forest_even_unclassified_def)
  next
    case 2
    then show ?case 
      by (simp add: invar_basic_old(2) vset(3) extend_forest_even_unclassified_def)
  next
    case 3
    then show ?case 
      by (simp add: invar_basic_old(3) vset(3) extend_forest_even_unclassified_def)
  next
    case 4
    then show ?case 
      by(simp add: invar_basic_old(4) parent(3) extend_forest_even_unclassified_def)
  next
    case 5
    then show ?case 
      by(simp add: invar_basic_old(5) origin(3)  Let_def extend_forest_even_unclassified_def)
  next
    case 6
    then show ?case 
      unfolding  new_abstract_is
      using invar_basic_old(2,3,6) extension_precond(2)
      by(auto simp add: parent(3,4)  invar_basic_old(4) extend_forest_even_unclassified_def
          vset(4) vs_insert)
  next
    case 7
    then show ?case 
      using extension_evens extension_odds extension_precond(3,8) invar_basic_old(7) by auto
  next
    case 8
    then show ?case 
      using invar_basic_old(8)  extension_evens
      by(auto simp add: extend_forest_even_unclassified_def)
  next
    case 9
    then show ?case
      using invar_basic_old(9) extension_odds
      by(auto simp add: extend_forest_even_unclassified_def)
  next
    case 10
    then show ?case 
      using invar_basic_old(10) extension_evens
      by(auto simp add: extend_forest_even_unclassified_def)
  next
    case 11
    then show ?case 
      using invar_basic_old(2,3,11)
      by(auto simp add: extend_forest_even_unclassified_def  vset(4))
  next
    case 12
    then show ?case 
      using invar_basic_old(12,8,9) extension_precond(3) extension_evens extension_odds 
      by(auto simp add: extend_forest_even_unclassified_def)
  next
    case 13
    show ?case
      using y_and_z_no_roots invar_basic_old(13)
      by(auto simp add: origins_lookup_is parent_lookup_is extension_roots)
  next
    case 14
    show ?case
      using y_and_z_no_roots invar_basic_old(14)
      by(auto simp add: origins_lookup_is parent_lookup_is extension_roots new_abstract_is vs_insert)
  next
    case 15
    have rw1:"origin_lookup (origins (extend_forest_even_unclassified F x y z)) `
    (vset_to_set (roots (extend_forest_even_unclassified F x y z)) \<union>
     Vs (abstract_forest (extend_forest_even_unclassified F x y z))) = 
        origin_lookup (origins (extend_forest_even_unclassified F x y z)) ` 
         ((vset_to_set (roots F) \<union> Vs (abstract_forest F)) \<union> {y,z})"
    proof(rule image_cong[OF _ refl], unfold new_abstract_is extension_roots,
        cases "x \<in> Vs (abstract_forest F)", goal_cases)
      case 1
      then show ?case 
        by(auto simp add: vs_union vs_insert)
    next
      case 2
      hence "x \<in> vset_to_set (roots F)"
        using extension_precond(2) invar_basic_old(6) by auto
      then show ?case 
        by(auto simp add: vs_union vs_insert)
    qed
    have rw2:"origin_lookup (origins (extend_forest_even_unclassified F x y z)) ` 
         (vset_to_set (roots F) \<union> Vs (abstract_forest F)) = 
          origin_lookup (origins F) ` 
         (vset_to_set (roots F) \<union> Vs (abstract_forest F))"
      using y_and_z_no_roots extension_precond(3) invar_basic_old(6)
      by(auto intro!: image_cong[OF  refl] simp add: origins_lookup_is )
    have rw3:"origin_lookup (origins (extend_forest_even_unclassified F x y z)) `  {y,z} =
                  {Some (the (origin_lookup (origins F) x))}"
      by(auto simp add: origins_lookup_is)
    have rw4:"Some (the (origin_lookup (origins F) x)) \<in> Some ` vset_to_set (roots F)"
      using extension_precond(2) invar_basic_old(15)        
        None_notin_image_Some[of "vset_to_set (roots F)"]
      unfolding  invar_basic_old(6)[symmetric]
      by(cases "origin_lookup (origins F) x") force+  
    show ?case
      using rw4 rw3 rw2 rw1
      by (simp add: extension_roots insert_absorb invar_basic_old(15))  
  next
    case 16
    show ?case
      using edges_are_Vs[OF extension_precond(5)] edges_are_Vs_2[OF extension_precond(5)]
        extension_precond(2) invar_basic_old(16,6)
      by(auto simp add: new_abstract_is extension_roots vs_union vs_insert)
  next
    case 17
    show ?case 
      by (simp add: invar_basic_old(17) new_abstract_is)
  qed
  have invar_matching_both_or_none_new:
    "invar_matching_both_or_none \<M> (extend_forest_even_unclassified F x y z)"
  proof(rule invar_matching_both_or_noneI, rule ccontr, goal_cases)
    case (1 u v)
    note dests = doubleton_in_matching(1,2)[OF extension_precond(6,5), of u] 
      doubleton_in_matching(1)[OF extension_precond(6), of y u z,
        simplified  insert_commute[of y u "{}"]] 
      doubleton_in_matching(1)[OF extension_precond(6),
        of z y, simplified insert_commute[of z y "{}"], OF extension_precond(5)] 
      doubleton_in_matching(1)[OF extension_precond(6,5), of v]
    from 1 show ?case
      using extension_precond(2) invar_basic_old(6)  invar_matching_both_or_noneD[OF invars_old(2), OF 1(1)]
        (* don't worry, this simply takes some time*)
      by(auto simp add: new_abstract_is vs_union extension_roots doubleton_eq_iff extension_precond(5)
          elim!: in_Vs_insertE
          dest: dests)
  qed
  have invar_forest_even_and_odd_new: 
    "invar_forest_even_and_odd (extend_forest_even_unclassified F x y z)"
  proof(rule invar_forest_even_and_oddI, goal_cases)
    case (1 u v)
    show ?case
    proof(cases "{u, v} = {x, y}")
      case True
      then show ?thesis 
      using  extension_precond(2,3,8,9,7) invar_basic_old(7) 
      by (auto simp add: extension_evens extension_odds)
    next
      case False
      note false = this
      show ?thesis 
      proof(cases "{u, v} = {y, z}")
        case True
        then show ?thesis 
         using  extension_precond(3) 
         by (auto simp add: extension_evens extension_odds doubleton_eq_iff )
      next
        case False
        hence "{u, v} \<in> abstract_forest F"
          using false 1
          by(auto simp add: new_abstract_is)
        then show ?thesis 
          using  extension_precond(3) invar_basic_old(6) 
                 invar_forest_even_and_oddD[OF invars_old(3)]
          by (auto simp add: extension_evens extension_odds doubleton_eq_iff)
      qed
    qed
  qed
  have invar_parent_wf_new: "invar_parent_wf (extend_forest_even_unclassified F x y z)"
  proof(rule invar_parent_wfI, goal_cases)
    case 1
    then show ?case 
      using extension_precond(3) neither_even_not_odd_no_parent
      by(all \<open>cases "parent_lookup (parents F) y"\<close>, all \<open>cases "parent_lookup (parents F) z"\<close>)
        (auto intro!: wf_par'(1)[of "parent_lookup (parents F)", OF _ refl]
          simp add: parent_lookup_is invar_parent_wfD invars_old(4) extension_precond(7,8,9))
  qed
  have invar_even_to_parent_matching_new:
    "invar_even_to_parent_matching \<M> (extend_forest_even_unclassified F x y z)"
  proof(rule invar_even_to_parent_matchingI, goal_cases)
    case (1 u v)
    moreover hence "{u, v} \<in> abstract_forest (extend_forest_even_unclassified F x y z)" 
      by(auto simp add: extend_forest_even_unclassified_def Let_def abstract_forest_def)
    ultimately show ?case 
      using edge_commute[OF extension_precond(5)] invar_even_to_parent_matchingD[OF invars_old(5)]
        extension_precond(3)
      by(auto simp add:  new_abstract_is extension_evens parent_lookup_is 
          if_split[of "\<lambda> x. x = Some v"  "u = z" "Some y"] 
          if_split[of  "\<lambda> x. x = Some v" "u = y"])  
  qed
  interpret parents_old: parent "parent_lookup (parents F)"
    by (simp add: follow_dom_invar_parent_wf(1) invars_old(4))
  interpret parents_new: parent " ((parent_lookup (parents F))(y \<mapsto> x, z \<mapsto> y))"
    using  invar_parent_wf_new
    by(auto intro!: parent.intro 
        dest: invar_parent_wfD 
        simp add:  parent_lookup_is)
  have follow_dom: "parent_spec_i.follow_dom ((parent_lookup (parents F))(y \<mapsto> x, z \<mapsto> y)) v" for v
    apply(rule parent_spec.wf_follow_rel)
    using invar_parent_wf_new
    unfolding parents_new.parent_eq_follow_rel invar_parent_wf_def  parent_lookup_is parent_spec_def
    by simp
  note follow_simps = parents_new.follow_psimps[folded follow_def]
  note follow_hd_new = parents_new.follow_hd[folded follow_def]
  note follow_hd_old = parents_old.follow_hd[folded follow_def]
  note follow_nempty_old = parents_old.follow_nempty[folded follow_def]
  have same_parent:
    "v'\<in>set (parent_spec.follow ((parent_lookup (parents F))(y \<mapsto> x, z \<mapsto> y)) x) \<Longrightarrow>
       ((parent_lookup (parents F))(y \<mapsto> x, z \<mapsto> y)) v' = parent_lookup (parents F) v'" for v'
  proof(goal_cases)
    case 1
    have "v' \<noteq> z" 
      using 1 extension_precond(3,8,9)
        neither_even_not_odd_no_parent[of z] 
        parents_new.nin_ancestors[ of x z] 
      by auto
    moreover have "v' = y \<Longrightarrow> False"
    proof-
      assume "v' = y"
      moreover have "v2\<in>set (parent_spec.follow ((parent_lookup (parents F))(y \<mapsto> x, z \<mapsto> y)) x) \<Longrightarrow>
       ((parent_lookup (parents F))(y \<mapsto> x, z \<mapsto> y)) v2 \<noteq> Some y" for v2
        using extension_precond(3,7,8,9)
          neither_even_not_odd_no_parent[of z] 
          neither_even_not_odd_no_parent[of y] 
          parents_new.nin_ancestors[ of x z] 
        by auto
      ultimately have "y \<in> vset_to_set (evens F) \<union> vset_to_set (odds F)"
        using extension_precond(3,7,8,9)
          parents_new.nin_ancestors[of x y] 1 
        by simp
      thus False 
        using extension_precond(3) by auto
    qed
    ultimately show ?thesis 
      by auto
  qed
  have follow_from_z_is:"follow ((parent_lookup (parents F))(y \<mapsto> x, z \<mapsto> y)) z =
         [z, y]@ follow (parent_lookup (parents F)) x"
    apply(subst follow_simps)
    apply(subst follow_simps)
    using extension_precond(8)  same_parent
    by (auto intro!: follow_cong[OF parents_new.parent_axioms follow_dom]
        simp add: follow_dom_invar_parent_wf(1) invars_old(4)  follow_def)
  have follow_from_y_is:"follow ((parent_lookup (parents F))(y \<mapsto> x, z \<mapsto> y)) y =
         y#follow (parent_lookup (parents F)) x"
    apply(subst follow_simps)
    using extension_precond(8) same_parent
    by (auto intro!: follow_cong[OF parents_new.parent_axioms follow_dom]
        simp add: follow_dom_invar_parent_wf(1) invars_old(4)  follow_def)
  have other_follows: 
    "follow ((parent_lookup (parents F))(y \<mapsto> x, z \<mapsto> y)) v =
         follow (parent_lookup (parents F)) v"
    if "v \<noteq> y" "v \<noteq> z" for v
    using  same_parent that extension_precond(3,7,8,9)
      neither_even_not_odd_no_parent[of y] 
      neither_even_not_odd_no_parent[of z]
      parents_new.nin_ancestors[of v y] 
      parents_new.nin_ancestors[of v z] 
    by(auto intro!: follow_cong[OF parents_new.parent_axioms follow_dom]
        simp add: follow_dom_invar_parent_wf(1) invars_old(4)  follow_def
        if_split[of "\<lambda> x. x \<noteq> Some _"  "_ = _"])+
  have invar_roots_new: "invar_roots (extend_forest_even_unclassified F x y z)"
  proof(rule invar_rootsI, goal_cases)
    case (1 r)
    then show ?case
      using  invar_rootsD(1)[OF invars_old(6), of r]
      by(auto simp add: extension_roots origins_lookup_is y_and_z_no_roots)
  next
    case (2 v)
    then show ?case 
      unfolding extension_roots new_abstract_is vs_union vs_insert
        origins_lookup_is parent_lookup_is 
    proof(cases "v = z", goal_cases)
      case 1
      have "the (origin_lookup (origins F) x) = last (follow ((parent_lookup (parents F))(y \<mapsto> x, z \<mapsto> y)) z)"
        apply(unfold follow_from_z_is)
        apply(subst last_appendR[OF  follow_nempty_old])
        using extension_precond(2) invar_rootsD(2)[OF invars_old(6), of x]
        by(auto simp add: invar_basic_old(6)[symmetric])
      thus ?case
        using 1 by simp
    next
      case 2
      thus ?case
      proof(cases "v = y", goal_cases)
        case 1
        have " the (origin_lookup (origins F) x) =
               last (follow ((parent_lookup (parents F))(y \<mapsto> x, z \<mapsto> y)) y)"
          apply(unfold follow_from_y_is, unfold follow_def)
          apply(subst last_ConsR[OF parent.follow_nempty])
          using extension_precond(2)  invar_rootsD(2)[OF invars_old(6), of x]
          by(auto simp add: follow_def invar_basic_old(6)[symmetric]
              follow_dom_invar_parent_wf(1) invars_old(4))
        thus ?case
          using 1 by simp
      next
        case 2
        thus ?case
          using  invar_rootsD(2)[OF invars_old(6)]  extension_precond(2) invar_basic_old(6) 
          by(auto simp add: other_follows)
      qed
    qed
  next
    case (3 v u)
    note three = this
    show ?case 
    proof(cases "v = z")
      case True
      note true = this
      show ?thesis 
      proof(cases "u = z")
        case True
        then show ?thesis 
          using true by simp
      next
        case False
        note false = this
        show ?thesis 
        proof(cases "u = y")
          case True
          then show ?thesis 
            by (simp add: origins_lookup_is true)
        next
          case False
          then show ?thesis 
            using extension_precond(2) invar_basic_old(15) 
              invar_rootsD(3)[OF invars_old(6), of x u, symmetric] three(2) 
            by (auto  dest: set_mp[OF equalityD1]
                simp add: origins_lookup_is parent_lookup_is true  follow_from_z_is 
                invar_basic_old(6)[symmetric])
        qed
      qed
    next
      case False
      note FALSE = this
      show ?thesis
      proof(cases "v = y")
        case True
        then show ?thesis 
          using extension_precond(2)  False
            invar_basic_old(15) invar_rootsD(3)[OF invars_old(6), of x u] three(2) 
          by (auto simp add: follow_from_y_is origins_lookup_is parent_lookup_is 
              invar_basic_old(6)[symmetric] 
              dest!: set_mp[OF equalityD1] sym[of "Some _"])
      next
        case False
        have helper:"origin_lookup (origins F) v = origin_lookup (origins F) u"
          using three False FALSE extension_precond(2) invar_basic_old(6) invar_rootsD(3) invars_old(6)
          by (auto simp add: extension_roots new_abstract_is vs_union vs_insert
              parent_lookup_is other_follows[OF False FALSE])
        show ?thesis
          using FALSE False  extension_precond(3) helper  neither_even_not_odd_no_parent 
            no_children_not_in_follow[OF follow_dom_invar_parent_wf(1)[OF invars_old(4)] _ _ refl]
            other_follows[OF False FALSE] three(2)
          by(force simp add:  parent_lookup_is  follow_def  origins_lookup_is)
      qed
    qed
  next
    case (4 v)
    show ?case
    proof(cases "v = z")
      case True
      show ?thesis 
        apply(unfold parent_lookup_is True follow_from_z_is new_abstract_is)
        apply(subst edges_of_path_append_2)
        using invar_rootsD(4)[OF invars_old(6) x_in_F]
        by(auto simp add: follow_hd_old follow_nempty_old)
    next
      case False
      note false = this
      show ?thesis
      proof(cases "v = y")
        case True
        then show ?thesis 
          apply(unfold parent_lookup_is True follow_from_y_is new_abstract_is)
          apply(subst edges_of_path_append_2[of _ "[_]", simplified])
          using invar_rootsD(4)[OF invars_old(6) x_in_F]
          by(auto simp add: follow_hd_old follow_nempty_old)
      next
        case False
        hence "v \<in> vset_to_set (roots F) \<union> Vs (abstract_forest F)"
          using 4 False false x_in_F
          by(auto simp add: extension_roots new_abstract_is vs_insert vs_union)
        thus ?thesis 
          using invar_rootsD(4)[OF invars_old(6)] 4
          by(auto simp add: parent_lookup_is other_follows[OF False false] new_abstract_is)     
      qed
    qed
  qed
  have invar_odd_to_parent_non_matching_new:
    "invar_odd_to_parent_non_matching \<M> (extend_forest_even_unclassified F x y z)"
  proof(rule invar_odd_to_parent_non_matchingI, goal_cases)
    case (1 u)
    have u_not_z: "u \<noteq> z"
      using "1" extension_odds extension_precond(3,8) by auto
    show ?case
    proof(cases "u = y")
      case True
      then show ?thesis 
        by (simp add:  parent_lookup_is True extension_precond(4,8) insert_commute)
    next
      case False
      show ?thesis
        using False u_not_z 1 invars_old(7) 
        by(auto elim: invar_odd_to_parent_non_matchingE
            simp add: parent_lookup_is extension_odds)
    qed
  qed

  show "forest_invar \<M> (extend_forest_even_unclassified F x y z)"
    by(auto intro!: forest_invarI 
        invar_basic_new invar_matching_both_or_none_new invar_forest_even_and_odd_new 
        invar_parent_wf_new invar_even_to_parent_matching_new invar_roots_new
        invar_odd_to_parent_non_matching_new)
qed

subsection \<open>Properties of the Result\<close>

lemma follow_alternating_paths_induction:
  assumes "forest_invar \<M> F" "p = follow (parent_lookup (parents F)) v" "length p = l"
  shows "v \<in> vset_to_set (evens F) \<Longrightarrow> rev_alt_path \<M> p"
    "v \<in> vset_to_set (odds F) \<Longrightarrow> alt_path \<M> p"
    "v \<in> vset_to_set (evens F) \<Longrightarrow> alt_list (\<lambda> x. x \<in> vset_to_set (evens F))
                                                      (\<lambda> x. x \<in> vset_to_set (odds F)) p"
    "v \<in> vset_to_set (odds F) \<Longrightarrow> alt_list (\<lambda> x. x \<in> vset_to_set (odds F))
                                                      (\<lambda> x. x \<in> vset_to_set (evens F)) p"
proof-
  interpret parents_here: parent "(parent_lookup (parents F))"
    using assms(1) follow_dom_invar_parent_wf(1) forest_invarD(4) by auto
  note follow_nempty = parents_here.follow_nempty[folded follow_def]
  note follow_cons = parents_here.follow_cons[folded follow_def]
  note follow_simps = parents_here.follow_psimps[folded follow_def]
  have l_geq_1: "l \<ge> 1" 
    using assms(2,3)[symmetric] follow_nempty 
    by(cases p) auto
  have  "(v \<in> vset_to_set (evens F) \<longrightarrow> rev_alt_path \<M> p \<and>
                  alt_list (\<lambda> x. x \<in> vset_to_set (evens F))
                           (\<lambda> x. x \<in> vset_to_set (odds F)) p) \<and>
         (v \<in> vset_to_set (odds F) \<longrightarrow> alt_path \<M> p \<and>
                   alt_list (\<lambda> x. x \<in> vset_to_set (odds F))
                            (\<lambda> x. x \<in> vset_to_set (evens F)) p)"
    using assms(2,3)
  proof(induction arbitrary: p v rule: nat_induct_at_least[OF l_geq_1])
    case 1
    hence "p = [v]" 
      by(subst (asm) follow_simps)(auto  split: option.split)
    then show ?case 
      by(simp add: alt_list.intros(1,2))
  next
    case (2 n)
    note 2
    note IH = this(1) 
      conjunct1[OF mp[OF conjunct1[OF this(2)]]] 
      conjunct2[OF mp[OF conjunct1[OF this(2)]]] 
      conjunct1[OF mp[OF conjunct2[OF this(2)]]] 
      conjunct2[OF mp[OF conjunct2[OF this(2)]]] 
      this(3,4)
    obtain u where u:"Some u = parent_lookup (parents F) v" 
      using IH(6,7,1) 
      apply(subst (asm) follow_simps) 
      by(cases "parent_lookup (parents F) v") auto
    obtain p' where p':"follow (parent_lookup (parents F)) u = u#p'" 
      using  follow_nempty neq_Nil_conv
      by(cases "follow (parent_lookup (parents F)) u")
        (auto dest: follow_cons)
    have p_first_two_verts: "p = [v, u]@p'" 
      using IH(6)   p' u
      by(cases "parent_lookup (parents F) v")
        (auto simp add: follow_simps[of v])
    have vu_in_abs_forest:"{v, u} \<in> abstract_forest F"
      using abstract_forest_def u by fastforce
    have edge_split_off:"edges_of_path p = {v, u}#edges_of_path (u#p')"
      by (simp add: p_first_two_verts)
    show ?case 
    proof(rule, (all \<open>rule\<close>), goal_cases)
      case 1
      have u_odd: "u \<in> vset_to_set (odds F)" 
        using  "1" assms(1) forest_invarD(3) 
          invar_forest_even_and_oddD vu_in_abs_forest
        by force
      hence "alt_path \<M> (u # p')"
        using IH(7) p_first_two_verts
        by(auto intro!: IH(4)[of "u#p'" u] simp add: p')
      moreover have "{v, u} \<in> \<M>" 
        using  "1" assms(1)forest_invarD(5) invar_even_to_parent_matchingD u 
        by force
      ultimately have "rev_alt_path \<M> p"
        by (simp add: alt_list_step edge_split_off)
      moreover have "alt_list (\<lambda>x. x \<in> vset_to_set (odds F)) (\<lambda>x. x \<in> vset_to_set (evens F)) (u#p')"
        using IH(7)
        by(auto intro!: IH(5)[OF _ _ u_odd] simp add: p'  p_first_two_verts)
      ultimately show ?case 
        by (simp add: "1" alt_list.intros(2) p_first_two_verts)
    next
      case 2
      have u_even:"u \<in> vset_to_set (evens F)" 
        using  "2" assms(1) edge_commute forest_invarD(3)
          invar_forest_even_and_oddD vu_in_abs_forest
        by fastforce
      hence "rev_alt_path \<M> (u # p')"
        using IH(7) p_first_two_verts
        by(auto intro!: IH(2)[of "u#p'" u] simp add: p')
      moreover have "{v, u} \<notin> \<M>" 
        using  "2" assms(1) forest_invarD(7) invar_odd_to_parent_non_matchingD u 
        by force
      ultimately have "alt_path \<M> p"
        by (simp add: alt_list_step edge_split_off)
      moreover have "alt_list (\<lambda>x. x \<in> vset_to_set (evens F)) (\<lambda>x. x \<in> vset_to_set (odds F)) (u#p')"
        using IH(7)
        by(auto intro!: IH(3)[OF _ _ u_even] simp add: p'  p_first_two_verts)
      ultimately show ?case 
        by (simp add: 2 alt_list.intros(2) p_first_two_verts)
    qed
  qed
  thus "v \<in> vset_to_set (evens F) \<Longrightarrow> rev_alt_path \<M> p"
    "v \<in> vset_to_set (odds F) \<Longrightarrow> alt_path \<M> p"
    "v \<in> vset_to_set (evens F) \<Longrightarrow> alt_list (\<lambda> x. x \<in> vset_to_set (evens F))
                                                      (\<lambda> x. x \<in> vset_to_set (odds F)) p"
    "v \<in> vset_to_set (odds F) \<Longrightarrow> alt_list (\<lambda> x. x \<in> vset_to_set (odds F))
                                                      (\<lambda> x. x \<in> vset_to_set (evens F)) p"
    by auto
qed

lemmas follow_alternating_paths = follow_alternating_paths_induction[OF _ _ refl]

lemma simple_invariant_consequences:
  assumes "forest_invar M F"
  shows "vset_invar (evens F)"
    "vset_invar (odds F)"
    "vset_to_set (evens F) \<union> vset_to_set (odds F) =
           vset_to_set (roots F) \<union> Vs (abstract_forest  F)"
    "vset_to_set (evens F) \<inter> vset_to_set (odds F) = {}"
    "finite (vset_to_set (evens F))"
    "finite (vset_to_set (odds F))"
    "finite (abstract_forest  F)"
    "vset_invar (roots F)"
    "vset_to_set (roots F) \<subseteq> vset_to_set (evens F)"
    "vset_to_set (roots F) \<inter> Vs M = {}"
    "card (vset_to_set (odds F)) < card (vset_to_set (evens F))"
  using  invar_basicD[OF forest_invarD(1)[OF assms]]
  by simp_all

lemma complex_invariant_consequences:
  assumes "forest_invar M F"
  shows "{u, v} \<in> M 
         \<Longrightarrow> {u, v} \<in> abstract_forest  F \<or>
             {u, v} \<inter> (Vs (abstract_forest  F) \<union> vset_to_set (roots F)) = {}"
        "{u, v} \<in> abstract_forest F 
         \<Longrightarrow> (u \<in> vset_to_set (evens F)) = (v \<in> vset_to_set (odds F))"
  using  forest_invarD[OF assms] 
    invar_matching_both_or_noneD[of M F u v] invar_forest_even_and_oddD
  by auto

lemmas ordinary_extension_properties = 
  extension_main_preservation 
  extension_abstract_is
  extension_odds extension_evens 
  extension_roots

lemma empty_forest_correctess:
  "evens (empty_forest R) = R"
  "odds (empty_forest R) = vset_empty"
  "abstract_forest (empty_forest R) = {}"
  "\<lbrakk>matching M ; vset_invar R; vset_to_set R \<inter> Vs M = {}; 
    finite (vset_to_set R) ; vset_to_set R \<noteq> {}\<rbrakk>
   \<Longrightarrow> forest_invar M (empty_forest R)"
proof(goal_cases)
  case 1
  then show ?case 
    by(auto simp add: empty_forest_def)
next
  case 2
  then show ?case 
    by(auto simp add: empty_forest_def)
next
  case 3
  then show ?case 
    by(auto simp add: empty_forest_def abstract_forest_def parent(2))
next
  case 4
  note four = this
  have orig_inv_foldr: "origin_invar (foldr (\<lambda>x. origin_upd x x) ys origin_empty)"
    for ys
    by(induction ys) (auto simp add: origin(1,2,3))
  have orig_inv: "origin_invar (foldl (\<lambda>m r. origin_upd r r m) origin_empty xs)" for xs 
    using orig_inv_foldr by(simp add: foldl_conv_foldr)
  have orig_lookup: "origin_lookup (foldl (\<lambda>m r. origin_upd r r m) origin_empty xs)
                       = (\<lambda> x. if x \<in> set xs then Some x else None)" for xs 
  proof-
    define ys where "ys = rev xs"
    show ?thesis
      unfolding foldl_conv_foldr ys_def[symmetric] set_rev[of xs, simplified ys_def[symmetric], symmetric]
      by(induction ys) 
        (auto simp add: origin(1,2,3,4)  orig_inv_foldr intro!: ext)
  qed
  show ?case 
  proof(rule forest_invarI, goal_cases)
    case 1
    then show ?case 
      using four vset(6)[of R "\<lambda>m r. origin_upd r r m" origin_empty]
      by (auto intro!: invar_basicI 
          simp add: abstract_forest_def parent(1,2) vset(1,2) empty_forest_def
          card_gt_0_iff orig_inv orig_lookup )
  next
    case 2
    then show ?case 
      using four(3)
      by(auto intro!: invar_matching_both_or_noneI
          simp add: empty_forest_def abstract_forest_def parent(2)
          dest: edges_are_Vs edges_are_Vs_2)
  next
    case 3
    then show ?case 
      by(auto intro!: invar_forest_even_and_oddI
          simp add: empty_forest_def abstract_forest_def parent(2))
  next
    case 4
    then show ?case 
      by(auto intro!: invar_parent_wfI 
          simp add: empty_forest_def abstract_forest_def parent(2) parent_spec_def)
  next
    case 5
    then show ?case 
      by(auto intro!: invar_even_to_parent_matchingI
          simp add: empty_forest_def abstract_forest_def parent(2))
  next
    case 6
    interpret parent_empty: parent "(\<lambda>x. None)"
      by(auto simp add: parent_def parent_spec_def)
    note follow_psimps = parent_empty.follow_psimps[folded follow_def]
    show ?case 
      using four(2) vset(6)[of R "\<lambda>m r. origin_upd r r m" origin_empty]
      by(auto intro!: invar_rootsI
          simp add: empty_forest_def abstract_forest_def parent(2)
          orig_lookup follow_psimps)
  next
    case 7
    then show ?case 
      by(auto intro!: invar_odd_to_parent_non_matchingI
          simp add: parent(2) empty_forest_def vset(2))
  qed
qed

lemma get_path_correct:
  assumes"forest_invar M F" "v \<in> vset_to_set (evens F)" "p = get_path  F v"
  shows "rev_alt_path M p" "odd (length p)" "last p \<in> vset_to_set (roots F)" 
        "walk_betw (abstract_forest  F) v p (last p) \<or> p = [v]" "distinct p"
proof-
  interpret parents_here: parent "parent_lookup (parents F)"
    using assms(1) follow_dom_invar_parent_wf(1) forest_invarD(4) by auto
  note follow_impl_is_follow =
    parents_here.follow_impl_is_follow[folded follow_def follow_impl_def]
  have p_def: "p = follow (parent_lookup (parents F)) v"
    by(simp add: assms(3) get_path_def follow_impl_is_follow)
  note follow_alternating_paths_facts = follow_alternating_paths(1,3)[OF assms(1) p_def assms(2)]
  thus "rev_alt_path M p" 
    by simp
  show last_root: "last p \<in> vset_to_set (roots F)"
    using assms(2)  invar_rootsD(2)[OF forest_invarD(6)[OF assms(1)], of v]
      invar_basicD(15)[OF forest_invarD(1)[OF assms(1)]] 
      imageI[of v "vset_to_set (evens F) \<union> vset_to_set (odds F)"
        "origin_lookup (origins F)"]
    by (auto simp add: p_def invar_basicD(6)[OF forest_invarD(1)[OF assms(1)], symmetric] )
  hence "last p \<in> vset_to_set (evens F)"  "last p \<notin> vset_to_set (odds F)"
    using  simple_invariant_consequences(4,9)[OF assms(1)]
    by auto
  thus odd_length_p: "odd (length p)"
    using  simple_invariant_consequences(4)[OF assms(1)]
    by(intro last_odd_P1'[OF follow_alternating_paths_facts(2)])
      (force dest!: alt_list_or[OF follow_alternating_paths_facts(2)]
        simp add: follow_def p_def parents_here.follow_nempty)+
  show "walk_betw (abstract_forest F) v p (last p) \<or> p = [v]"
    using parents_here.follow_walk_betw[folded follow_def, of v] 
    by (fastforce intro: back_subst[of "\<lambda> G. walk_betw G x p y" for x p y] 
        simp add: doubleton_eq_iff parents_here.parent_eq_follow_rel 
        abstract_forest_def p_def)
  show "distinct p"
    by (simp add: p_def follow_def parents_here.follow_distinct)
qed

end
                              
context
  forest_manipulation
begin

interpretation  satisfied_simple:
  alternating_forest_spec evens odds local.get_path local.abstract_forest forest_invar roots 
                          vset_invar vset_to_set
  using complex_invariant_consequences(1,2) 
  by(intro alternating_forest_spec.intro simple_invariant_consequences)
    (auto simp add: get_path_correct(1,2,3,4,5))

lemma satisfied_simple_extension_precond_same:
  "satisfied_simple.forest_extension_precond F M x y z = forest_extension_precond F M x y z"
  by(auto simp add: forest_extension_precond_def satisfied_simple.forest_extension_precond_def)

interpretation satisfied: alternating_forest_ordinary_extension_spec
  vset_invar vset_to_set 
  evens odds "get_path "
  "abstract_forest" forest_invar  roots vset_empty
  "extend_forest_even_unclassified"
  "empty_forest"
  by(intro alternating_forest_ordinary_extension_spec.intro
      satisfied_simple.alternating_forest_spec_axioms
      alternating_forest_ordinary_extension_spec_axioms.intro)
    (simp_all add: satisfied_simple_extension_precond_same extension_main_preservation 
      extension_abstract_is extension_evens extension_odds extension_roots 
      empty_forest_correctess)

lemmas satisified = satisfied.alternating_forest_ordinary_extension_spec_axioms

end
end