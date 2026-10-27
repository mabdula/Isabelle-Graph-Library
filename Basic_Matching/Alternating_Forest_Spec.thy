(*
  Author: Thomas Ammer
*)

theory Alternating_Forest_Spec
  imports
    Matching
begin

provenance human

section \<open>Specification of Executable Alternating Forest\<close>

text \<open>The locales assume a minimal basis of properties. All further properties are derived
      inside the locales and keep the names they had when they were assumptions.\<close>

locale alternating_forest_spec =
  fixes evens::"'forest \<Rightarrow> 'vset"
    and odds::"'forest \<Rightarrow> 'vset"
    and get_path::"'forest \<Rightarrow> 'v \<Rightarrow> 'v list"
    and abstract_forest::"'forest \<Rightarrow> 'v set set"
    and forest_invar::"'v set set \<Rightarrow> 'forest \<Rightarrow> bool"
    and roots::"'forest \<Rightarrow> 'vset"
    and vset_invar::"'vset \<Rightarrow> bool"
    and vset_to_set::"'vset \<Rightarrow> 'v set"
  assumes evens_and_odds_basis:
 "\<And> F M. forest_invar M F\<Longrightarrow> vset_invar (evens F)"
 "\<And> F M. forest_invar M F\<Longrightarrow> vset_invar (odds F)"
 "\<And> F M. forest_invar M F
      \<Longrightarrow> Vs (abstract_forest F) \<subseteq> vset_to_set (evens F) \<union> vset_to_set (odds F)"
 "\<And> F M. forest_invar M F \<Longrightarrow> vset_to_set (odds F) \<subseteq> Vs (abstract_forest F)"
 "\<And> F M. forest_invar M F \<Longrightarrow> vset_to_set (roots F) \<inter> vset_to_set (odds F) = {}"
and finite_forest_basis:
 "\<And> F M. forest_invar M F\<Longrightarrow> finite (vset_to_set (odds F))"
and roots:
   "\<And> F M. forest_invar M F \<Longrightarrow> vset_invar (roots F)"
   "\<And> F M. forest_invar M F \<Longrightarrow> vset_to_set (roots F) \<subseteq> vset_to_set (evens F)"
   "\<And> F M. forest_invar M F \<Longrightarrow> vset_to_set (roots F) \<inter> Vs M = {}"
and get_path_basis:
    "\<And> F M v p. \<lbrakk>forest_invar M F; v \<in> vset_to_set (evens F); p = get_path F v\<rbrakk> \<Longrightarrow>
           rev_alt_path M p \<and>
           last p \<in> vset_to_set (roots F) \<and>
           (walk_betw (abstract_forest F) v p (last p) \<or> p = [v]) \<and>
           distinct p"
and higher_forest_properties_basis:
    "\<And> F M. forest_invar M F\<Longrightarrow>
       card (vset_to_set (evens F)) > card (vset_to_set (odds F))"
    "\<And> F M u v. \<lbrakk>forest_invar M F; {u, v} \<in> M\<rbrakk>\<Longrightarrow>
        {u, v} \<in> abstract_forest F \<or> {u, v} \<inter> Vs (abstract_forest F) = {}"
    "\<And> F M u v. \<lbrakk>forest_invar M F; {u, v} \<in> abstract_forest F\<rbrakk>\<Longrightarrow>
               u \<in> vset_to_set (evens F) \<longleftrightarrow> v \<in> vset_to_set (odds F)"
begin

subsection \<open>Derived Properties\<close>

text \<open>Along a path in the forest, even and odd vertices alternate.\<close>

lemma forest_path_parity:
  assumes "forest_invar M F" "path (abstract_forest F) p" "p \<noteq> []"
    "last p \<in> vset_to_set (evens F)" "last p \<notin> vset_to_set (odds F)"
  shows "(hd p \<in> vset_to_set (evens F) \<and> hd p \<notin> vset_to_set (odds F) \<and> odd (length p)) \<or>
         (hd p \<in> vset_to_set (odds F) \<and> hd p \<notin> vset_to_set (evens F) \<and> even (length p))"
  using assms(2-)
proof(induction p rule: path.induct)
  case (path2 v v' vs)
  have last_v': "last (v' # vs) \<in> vset_to_set (evens F)"
    "last (v' # vs) \<notin> vset_to_set (odds F)"
    using path2.prems(2,3) by simp_all
  have IH: "(v' \<in> vset_to_set (evens F) \<and> v' \<notin> vset_to_set (odds F) \<and> even (length vs)) \<or>
            (v' \<in> vset_to_set (odds F) \<and> v' \<notin> vset_to_set (evens F) \<and> odd (length vs))"
    using path2.IH[OF _ last_v'] by simp
  have "v \<in> vset_to_set (evens F) \<longleftrightarrow> v' \<in> vset_to_set (odds F)"
    by (rule higher_forest_properties_basis(3)[OF assms(1) path2.hyps(1)])
  moreover have "v' \<in> vset_to_set (evens F) \<longleftrightarrow> v \<in> vset_to_set (odds F)"
    by (rule higher_forest_properties_basis(3)[OF assms(1) edge_commute[OF path2.hyps(1)]])
  ultimately show ?case
    using IH by auto
qed simp_all

lemma get_path_parity:
  assumes "forest_invar M F" "v \<in> vset_to_set (evens F)"
  shows "v \<notin> vset_to_set (odds F)" "odd (length (get_path F v))"
proof-
  define p where "p = get_path F v"
  have p: "last p \<in> vset_to_set (roots F)"
    "walk_betw (abstract_forest F) v p (last p) \<or> p = [v]"
    using get_path_basis[OF assms p_def] by blast+
  have last_p: "last p \<in> vset_to_set (evens F)" "last p \<notin> vset_to_set (odds F)"
    using p(1) roots(2)[OF assms(1)] evens_and_odds_basis(5)[OF assms(1)] by blast+
  have "v \<notin> vset_to_set (odds F) \<and> odd (length p)"
  proof(cases "p = [v]")
    case True
    thus ?thesis
      using last_p by simp
  next
    case False
    hence walk: "walk_betw (abstract_forest F) v p (last p)"
      using p(2) by simp
    have "(hd p \<in> vset_to_set (evens F) \<and> hd p \<notin> vset_to_set (odds F) \<and> odd (length p)) \<or>
          (hd p \<in> vset_to_set (odds F) \<and> hd p \<notin> vset_to_set (evens F) \<and> even (length p))"
      by (rule forest_path_parity[OF assms(1) walk_between_nonempty_pathD(1,2)[OF walk] last_p])
    thus ?thesis
      using walk_between_nonempty_pathD(3)[OF walk] assms(2) by auto
  qed
  thus "v \<notin> vset_to_set (odds F)" "odd (length (get_path F v))"
    by (simp_all add: p_def)
qed

lemma evens_and_odds:
 "\<And> F M. forest_invar M F\<Longrightarrow> vset_invar (evens F)"
 "\<And> F M. forest_invar M F\<Longrightarrow> vset_invar (odds F)"
 "\<And> F M. forest_invar M F
      \<Longrightarrow> vset_to_set (evens F) \<union> vset_to_set (odds F) =
          vset_to_set (roots F) \<union> Vs (abstract_forest F)"
  "\<And> F M. forest_invar M F\<Longrightarrow>
       (vset_to_set (evens F))\<inter>(vset_to_set (odds F)) = {}"
proof-
  fix F M
  assume invar: "forest_invar M F"
  show "vset_invar (evens F)"
    by (rule evens_and_odds_basis(1)[OF invar])
  show "vset_invar (odds F)"
    by (rule evens_and_odds_basis(2)[OF invar])
  have "vset_to_set (evens F) \<subseteq> vset_to_set (roots F) \<union> Vs (abstract_forest F)"
  proof
    fix v
    assume v: "v \<in> vset_to_set (evens F)"
    have "last (get_path F v) \<in> vset_to_set (roots F)"
      "walk_betw (abstract_forest F) v (get_path F v) (last (get_path F v)) \<or> get_path F v = [v]"
      using get_path_basis[OF invar v refl] by blast+
    thus "v \<in> vset_to_set (roots F) \<union> Vs (abstract_forest F)"
      by (auto dest: walk_endpoints(1))
  qed
  thus "vset_to_set (evens F) \<union> vset_to_set (odds F) =
          vset_to_set (roots F) \<union> Vs (abstract_forest F)"
    using evens_and_odds_basis(3,4)[OF invar] roots(2)[OF invar] by blast
  show "vset_to_set (evens F) \<inter> vset_to_set (odds F) = {}"
    using get_path_parity(1)[OF invar] by blast
qed

lemma finite_forest:
 "\<And> F M. forest_invar M F\<Longrightarrow> finite (vset_to_set (evens F))"
 "\<And> F M. forest_invar M F\<Longrightarrow> finite (vset_to_set (odds F))"
 "\<And> F M. forest_invar M F\<Longrightarrow> finite (abstract_forest F)"
proof-
  fix F M
  assume invar: "forest_invar M F"
  show finite_evens: "finite (vset_to_set (evens F))"
  proof(rule ccontr)
    assume "infinite (vset_to_set (evens F))"
    hence "card (vset_to_set (evens F)) = 0"
      by (simp add: card_eq_0_iff)
    thus False
      using higher_forest_properties_basis(1)[OF invar] by simp
  qed
  show "finite (vset_to_set (odds F))"
    by (rule finite_forest_basis[OF invar])
  show "finite (abstract_forest F)"
    using finite_evens finite_forest_basis[OF invar]
    by (intro finite_Vs_then_finite finite_subset[OF evens_and_odds_basis(3)[OF invar]]) simp
qed

lemma get_path:
    "\<And> F M v p. \<lbrakk>forest_invar M F; v \<in> vset_to_set (evens F); p = get_path F v\<rbrakk> \<Longrightarrow>
           rev_alt_path M p \<and> odd (length p) \<and>
           last p \<in> vset_to_set (roots F) \<and>
           (walk_betw (abstract_forest F) v p (last p) \<or> p = [v]) \<and>
           distinct p"
<<<<<<< HEAD
  subgoal premises prems for F M v p
    using get_path_basis[OF prems] get_path_parity(2)[OF prems(1,2)]
    by (simp add: prems(3))
  done

lemma higher_forest_properties:
    "\<And> F M. forest_invar M F\<Longrightarrow>
       card (vset_to_set (evens F)) > card (vset_to_set (odds F))"
=======
and get_path_prefices:
    "\<And> F M v v' x p1 p2 p1' p2'. 
      \<lbrakk>forest_invar M F; p1@x#p2 = get_path F v;  p1'@[x]@p2' = get_path F v'\<rbrakk> \<Longrightarrow>
           p2 = p2'"
and higher_forest_properties:
    "\<And> F M. forest_invar M F\<Longrightarrow> 
       card (vset_to_set (evens F)) = card (vset_to_set (odds F)) +  card (vset_to_set (roots F))"
>>>>>>> weighted_blossom
    "\<And> F M u v. \<lbrakk>forest_invar M F; {u, v} \<in> M\<rbrakk>\<Longrightarrow>
        {u, v} \<in> abstract_forest F \<or>
          {u, v} \<inter> (Vs (abstract_forest F) \<union> vset_to_set (roots F)) = {}"
    "\<And> F M u v. \<lbrakk>forest_invar M F; {u, v} \<in> abstract_forest F\<rbrakk>\<Longrightarrow>
               u \<in> vset_to_set (evens F) \<longleftrightarrow> v \<in> vset_to_set (odds F)"
<<<<<<< HEAD
  subgoal
    by (rule higher_forest_properties_basis(1))
  subgoal premises prems for F M u v
    using higher_forest_properties_basis(2)[OF prems] roots(3)[OF prems(1)]
          edges_are_Vs[OF prems(2)] edges_are_Vs_2[OF prems(2)]
    by blast
  subgoal
    by (rule higher_forest_properties_basis(3))
  done

text \<open>The roots are exactly the even vertices that the matching does not cover.\<close>

lemma roots_are_unmatched_evens:
  assumes "forest_invar M F"
  shows "vset_to_set (roots F) = vset_to_set (evens F) - Vs M"
proof
  show "vset_to_set (roots F) \<subseteq> vset_to_set (evens F) - Vs M"
    using roots(2,3)[OF assms] by blast
next
  show "vset_to_set (evens F) - Vs M \<subseteq> vset_to_set (roots F)"
  proof
    fix v
    assume v: "v \<in> vset_to_set (evens F) - Vs M"
    define p where "p = get_path F v"
    have p: "rev_alt_path M p" "last p \<in> vset_to_set (roots F)"
      "walk_betw (abstract_forest F) v p (last p) \<or> p = [v]"
      using get_path_basis[OF assms _ p_def] v by blast+
    show "v \<in> vset_to_set (roots F)"
    proof(cases "p = [v]")
      case True
      thus ?thesis
        using p(2) by simp
    next
      case False
      hence walk: "walk_betw (abstract_forest F) v p (last p)"
        using p(3) by simp
      obtain q where q: "p = v # q"
        using walk_between_nonempty_pathD(2,3)[OF walk] by (cases p) auto
      then obtain w q' where "p = v # w # q'"
        using False by (cases q) auto
      hence "{v, w} \<in> M"
        using p(1) by (simp add: alt_list_step)
      hence "v \<in> Vs M"
        by (rule edges_are_Vs)
      thus ?thesis
        using v by simp
    qed
  qed
qed

subsection \<open>Precondition of the Ordinary Extension\<close>

=======
and dblton: "\<And> M F. forest_invar M F \<Longrightarrow> dblton_graph (abstract_forest F)"
begin
>>>>>>> weighted_blossom
definition "forest_extension_precond F M x y z =
      (forest_invar M F \<and> x \<in> vset_to_set (evens F) \<and>
        {y, z} \<inter> (vset_to_set (evens F) \<union> vset_to_set (odds F)) = {} \<and>
        {x, y} \<notin> M \<and> {y, z} \<in> M \<and>  matching M \<and> x \<noteq> y \<and>  y \<noteq> z \<and> x \<noteq> z)"

text \<open>The remaining conjuncts of @{term forest_extension_precond} follow from these.\<close>

lemma forest_extension_precondI:
<<<<<<< HEAD
  assumes invar: "forest_invar M F"
    and x_even: "x \<in> vset_to_set (evens F)"
    and y_new: "y \<notin> vset_to_set (evens F) \<union> vset_to_set (odds F)"
    and yz: "{y, z} \<in> M" and matching: "matching M" and y_not_z: "y \<noteq> z"
  shows "forest_extension_precond F M x y z"
proof-
  have y_not_forest: "y \<notin> Vs (abstract_forest F)"
    using y_new evens_and_odds_basis(3)[OF invar] by blast
  have z_new: "z \<notin> vset_to_set (evens F) \<union> vset_to_set (odds F)"
  proof
    assume "z \<in> vset_to_set (evens F) \<union> vset_to_set (odds F)"
    moreover have "z \<notin> vset_to_set (roots F)"
      using roots(3)[OF invar] edges_are_Vs_2[OF yz] by blast
    ultimately have "z \<in> Vs (abstract_forest F)"
      using evens_and_odds(3)[OF invar] by blast
    hence "{y, z} \<in> abstract_forest F"
      using higher_forest_properties_basis(2)[OF invar yz] by blast
    hence "y \<in> Vs (abstract_forest F)"
      by (rule edges_are_Vs)
    thus False
      using y_not_forest by blast
  qed
  have xy: "{x, y} \<notin> M"
  proof
    assume xy: "{x, y} \<in> M"
    hence "x \<notin> vset_to_set (roots F)"
      using roots(3)[OF invar] edges_are_Vs[OF xy] by blast
    hence "x \<in> Vs (abstract_forest F)"
      using x_even evens_and_odds(3)[OF invar] by blast
    hence "{x, y} \<in> abstract_forest F"
      using higher_forest_properties_basis(2)[OF invar xy] by blast
    hence "y \<in> Vs (abstract_forest F)"
      by (rule edges_are_Vs_2)
    thus False
      using y_not_forest by blast
  qed
  show ?thesis
    unfolding forest_extension_precond_def
    using invar x_even y_new z_new xy yz matching y_not_z by blast
qed
=======
"\<lbrakk>forest_invar M F; x \<in> vset_to_set (evens F);
  {y, z} \<inter> (vset_to_set (evens F) \<union> vset_to_set (odds F)) = {};
  {x, y} \<notin> M; {y, z} \<in> M; matching M;
  x \<noteq> y; y \<noteq> z; x \<noteq> z\<rbrakk>
\<Longrightarrow>forest_extension_precond F M x y z "
  by(auto simp add: forest_extension_precond_def)

definition 
   "contract_fork_precond \<M> F v v' B1 B2 u new_vert P contr = 
    (forest_invar \<M> F \<and>  matching \<M> \<and> dblton_graph \<M> \<and> 
     get_path F v = B1@[u]@P \<and> get_path F v' = B2@[u]@P \<and> set B1 \<inter> set B2 ={} \<and>
     v \<in> vset_to_set (evens F) \<and> v' \<in> vset_to_set (evens F) \<and> 
     new_vert \<notin> Vs \<M> \<union> vset_to_set (evens F) \<union> vset_to_set (odds F) - (set B1 \<union> set B2 \<union> {u}) \<and>
     contr = (\<lambda> v. if v \<in> {u} \<union> set B1 \<union> set B2 then new_vert else v))"

lemma contract_fork_precondI:
 "\<lbrakk>forest_invar \<M> F; matching \<M>; dblton_graph \<M>; get_path F v = B1@[u]@P;
   get_path F v' = B2@[u]@P; set B1 \<inter> set B2 = {}; v \<in> vset_to_set (evens F);
   v' \<in> vset_to_set (evens F); 
   new_vert \<notin> Vs \<M> \<union> vset_to_set (evens F) \<union> vset_to_set (odds F) - (set B1 \<union> set B2 \<union> {u});
   contr = (\<lambda> v. if v \<in> {u} \<union> set B1 \<union> set B2 then new_vert else v)\<rbrakk>
   \<Longrightarrow> contract_fork_precond \<M> F v v' B1 B2 u new_vert P contr"
and contract_fork_precondE:
 "contract_fork_precond \<M> F v v' B1 B2 u new_vert P contr \<Longrightarrow>
 (\<lbrakk>forest_invar \<M> F; matching \<M>; dblton_graph \<M>; get_path F v = B1@[u]@P;
   get_path F v' = B2@[u]@P; set B1 \<inter> set B2 = {}; v \<in> vset_to_set (evens F);
   v' \<in> vset_to_set (evens F); 
   new_vert \<notin> Vs \<M> \<union> vset_to_set (evens F) \<union> vset_to_set (odds F) - (set B1 \<union> set B2 \<union> {u});
   contr = (\<lambda> v. if v \<in> {u} \<union> set B1 \<union> set B2 then new_vert else v)\<rbrakk>
   \<Longrightarrow> Q)
  \<Longrightarrow> Q"
  by(auto simp add: contract_fork_precond_def)

definition 
 "odd_expansion_precond \<M> F u mu p = 
  (forest_invar \<M> F \<and> matching \<M> \<and> u \<in> vset_to_set (odds F) \<and> {u, mu} \<in> \<M> \<and>
  odd (length p) \<and> set p \<inter> (Vs (abstract_forest F) \<union> vset_to_set (roots F) \<union> Vs \<M>) \<subseteq> {u} \<and> 
  distinct p)"

lemma odd_expansion_precondE:
  "\<lbrakk>odd_expansion_precond \<M> F u mu p; 
    \<lbrakk>forest_invar \<M> F; matching \<M>; u \<in> vset_to_set (odds F); {u, mu} \<in> \<M>; odd (length p);
     set p \<inter> (Vs (abstract_forest F) \<union> vset_to_set (roots F) \<union> Vs \<M>) \<subseteq> {u};  distinct p\<rbrakk> \<Longrightarrow> P \<rbrakk>
   \<Longrightarrow> P"
and odd_expansion_precondI:
  "\<lbrakk>forest_invar \<M> F; matching \<M>; u \<in> vset_to_set (odds F); {u, mu} \<in> \<M>; odd (length p);
     set p \<inter> (Vs (abstract_forest F) \<union> vset_to_set (roots F) \<union> Vs \<M>) \<subseteq> {u};  distinct p\<rbrakk> 
   \<Longrightarrow> odd_expansion_precond \<M> F u mu p"
  by(auto simp add: odd_expansion_precond_def)

>>>>>>> weighted_blossom
end

locale alternating_forest_ordinary_extension_spec =
alternating_forest_spec evens odds get_path abstract_forest forest_invar roots
    for evens::"'forest \<Rightarrow> 'vset"
    and odds::"'forest \<Rightarrow> 'vset"
    and get_path::"'forest \<Rightarrow> 'v \<Rightarrow> 'v list"
    and abstract_forest::"'forest \<Rightarrow> 'v set set"
    and forest_invar::"'v set set \<Rightarrow> 'forest \<Rightarrow> bool"
    and roots::"'forest \<Rightarrow> 'vset" +
  fixes extend_forest_even_unclassified::
        "'forest \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'forest"
   and empty_forest::"'vset \<Rightarrow> 'forest"
   and forest_univ::"'v set"
  assumes forest_extend_basis: "\<And> F M x y z. forest_extension_precond F M x y z
      \<Longrightarrow> forest_invar M (extend_forest_even_unclassified F x y z)"
   "\<And> F M x y z. forest_extension_precond F M x y z
      \<Longrightarrow> abstract_forest (extend_forest_even_unclassified F x y z) =
          abstract_forest F \<union> {{x, y}, {y, z}}"
   "\<And> F M x y z. forest_extension_precond F M x y z
      \<Longrightarrow> vset_to_set (evens (extend_forest_even_unclassified F x y z)) =
          insert z (vset_to_set (evens F))"
and empty_forest_basis:
    "\<And> R. evens (empty_forest R) = R"
    "\<And> R. abstract_forest (empty_forest R) = {}"
    "\<And> R M. \<lbrakk>matching M; vset_invar R; vset_to_set R \<inter> Vs M = {};
           finite (vset_to_set R); vset_to_set R \<noteq> {}; Vs M \<subseteq> forest_univ\<rbrakk>
          \<Longrightarrow> forest_invar M (empty_forest R)"
begin

subsection \<open>Derived Properties of Extension and Empty Forest\<close>

lemma forest_extend:
  "\<And> F M x y z. forest_extension_precond F M x y z
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
<<<<<<< HEAD
proof-
  fix F M x y z
  assume precond: "forest_extension_precond F M x y z"
  define F' where "F' = extend_forest_even_unclassified F x y z"
  have invar: "forest_invar M F" and x_even: "x \<in> vset_to_set (evens F)"
    and yz_new: "{y, z} \<inter> (vset_to_set (evens F) \<union> vset_to_set (odds F)) = {}"
    and yz: "{y, z} \<in> M" and y_not_z: "y \<noteq> z"
    using precond by (auto simp: forest_extension_precond_def)
  have invar': "forest_invar M F'"
    and A': "abstract_forest F' = abstract_forest F \<union> {{x, y}, {y, z}}"
    and E': "vset_to_set (evens F') = insert z (vset_to_set (evens F))"
    using forest_extend_basis[OF precond] by (simp_all add: F'_def)
  show "forest_invar M (extend_forest_even_unclassified F x y z)"
    "abstract_forest (extend_forest_even_unclassified F x y z) =
          abstract_forest F \<union> {{x, y}, {y, z}}"
    "vset_to_set (evens (extend_forest_even_unclassified F x y z)) =
          insert z (vset_to_set (evens F))"
    by (rule forest_extend_basis[OF precond])+
  have Vs_A': "Vs (abstract_forest F') = Vs (abstract_forest F) \<union> {x, y, z}"
    by (auto simp: A' vs_union vs_insert)
  have "vset_to_set (odds F') = insert y (vset_to_set (odds F))"
  proof
    show "vset_to_set (odds F') \<subseteq> insert y (vset_to_set (odds F))"
    proof
      fix u
      assume u: "u \<in> vset_to_set (odds F')"
      hence "u \<in> Vs (abstract_forest F) \<union> {x, y, z}"
        using evens_and_odds_basis(4)[OF invar'] Vs_A' by blast
      hence "u \<in> vset_to_set (evens F) \<union> vset_to_set (odds F) \<union> {y, z}"
        using evens_and_odds_basis(3)[OF invar] x_even by blast
      moreover have "u \<notin> vset_to_set (evens F')"
        using u evens_and_odds(4)[OF invar'] by blast
      ultimately show "u \<in> insert y (vset_to_set (odds F))"
        using E' by blast
    qed
  next
    show "insert y (vset_to_set (odds F)) \<subseteq> vset_to_set (odds F')"
    proof
      fix u
      assume u: "u \<in> insert y (vset_to_set (odds F))"
      hence "u \<in> Vs (abstract_forest F')"
        using evens_and_odds_basis(4)[OF invar] Vs_A' by blast
      hence "u \<in> vset_to_set (evens F') \<union> vset_to_set (odds F')"
        using evens_and_odds_basis(3)[OF invar'] by blast
      moreover have "u \<notin> vset_to_set (evens F')"
        using u E' yz_new y_not_z evens_and_odds(4)[OF invar] by blast
      ultimately show "u \<in> vset_to_set (odds F')"
        by blast
    qed
  qed
  thus "vset_to_set (odds (extend_forest_even_unclassified F x y z)) =
          insert y (vset_to_set (odds F))"
    by (simp add: F'_def)
  have "z \<in> Vs M"
    using yz by (rule edges_are_Vs_2)
  thus "vset_to_set (roots (extend_forest_even_unclassified F x y z)) =
          vset_to_set (roots F)"
    using roots_are_unmatched_evens[OF invar'] roots_are_unmatched_evens[OF invar] E'
    by (auto simp: F'_def)
qed
=======
and empty_forest:
    "\<And> R. evens (empty_forest R) = R"
    "\<And> R. odds (empty_forest R) = vset_empty"
    "\<And> R. roots (empty_forest R) = R"
    "\<And> R. abstract_forest (empty_forest R) = {}"
    "\<And> R M. \<lbrakk>matching M; vset_invar R; vset_to_set R \<inter> Vs M = {}; 
           finite (vset_to_set R)\<rbrakk>
          \<Longrightarrow> forest_invar M (empty_forest R)"
>>>>>>> weighted_blossom

lemma empty_forest:
    "\<And> R. evens (empty_forest R) = R"
    "\<And> R M. forest_invar M (empty_forest R) \<Longrightarrow> vset_to_set (odds (empty_forest R)) = {}"
    "\<And> R. abstract_forest (empty_forest R) = {}"
    "\<And> R M. \<lbrakk>matching M; vset_invar R; vset_to_set R \<inter> Vs M = {};
           finite (vset_to_set R); vset_to_set R \<noteq> {}; Vs M \<subseteq> forest_univ\<rbrakk>
          \<Longrightarrow> forest_invar M (empty_forest R)"
  subgoal
    by (rule empty_forest_basis(1))
  subgoal premises prems for R M
    using evens_and_odds_basis(4)[OF prems] by (simp add: empty_forest_basis(2))
  subgoal
    by (rule empty_forest_basis(2))
  subgoal
    by (rule empty_forest_basis(3))
  done

end

end
