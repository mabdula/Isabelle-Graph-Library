theory Parent_Map_Spec
  imports Undirected_Set_Graphs.Paths Directed_Set_Graphs.Awalk
begin

locale Parent_Map_Spec =
  fixes U ::"'v set"
  and to_dir_graph::"'pmap \<Rightarrow> ('v \<times> 'v) set"
  and get_path::"'pmap \<Rightarrow> 'v \<Rightarrow> 'v list"
  and extend::"'pmap \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'pmap"
  and invar::"'pmap \<Rightarrow> bool"
  and roots::"'pmap \<Rightarrow> 'v set"
  and vset_abstract::"'vset \<Rightarrow> 'v set"
  and init::"'vset \<Rightarrow> 'pmap"
  and vset_invar::"'vset \<Rightarrow> bool"
assumes
  to_dir_graph_in_U: 
     "\<And> \<pi>. invar \<pi> \<Longrightarrow> dVs (to_dir_graph \<pi>) \<subseteq> U"
and get_path:
     "\<And> \<pi> s. invar \<pi> \<Longrightarrow> 
        \<exists> t. distinct_vwalk_bet (to_dir_graph \<pi>) s (get_path \<pi> s) t \<and>
             t \<in> roots \<pi>"
and extend: 
     "\<And> \<pi> u v. \<lbrakk>invar \<pi>; v \<in> U - dVs (to_dir_graph \<pi>);
                 u \<in> dVs (to_dir_graph \<pi>)\<rbrakk> \<Longrightarrow>
          invar (extend \<pi> u v)"
     "\<And> \<pi> u v. \<lbrakk>invar \<pi>; v \<in> U - dVs (to_dir_graph \<pi>);
                 u \<in> dVs (to_dir_graph \<pi>)\<rbrakk> \<Longrightarrow>
          to_dir_graph (extend \<pi> u v) = Set.insert (v, u) (to_dir_graph \<pi>)"
     "\<And> \<pi> u v. \<lbrakk>invar \<pi>; v \<in> U - dVs (to_dir_graph \<pi>);
                 u \<in> dVs (to_dir_graph \<pi>)\<rbrakk> \<Longrightarrow>
          roots (extend \<pi> u v) = roots \<pi>"
and init:
     "\<And> R. \<lbrakk>vset_invar R; vset_abstract R \<subseteq> U\<rbrakk> \<Longrightarrow>
              roots (init R) = vset_abstract R"
      "\<And> R. \<lbrakk>vset_invar R; vset_abstract R \<subseteq> U\<rbrakk> \<Longrightarrow>
           to_dir_graph (init R) = {}"
      "\<And> R. \<lbrakk>vset_invar R; vset_abstract R \<subseteq> U\<rbrakk> \<Longrightarrow>
            invar (init R)"


begin
end



end