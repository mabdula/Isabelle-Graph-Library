theory Blocking_Flow
  imports STFlow
begin

definition "unsaturated_path_simple G (u::_ \<Rightarrow> 'a::order) f s p t = (vwalk_bet G s p t
                                     \<and> (\<forall> e \<in> set (edges_of_vwalk p). f e < u e))"

lemma unsaturated_path_simple_mono: "unsaturated_path_simple G u f s p t  \<Longrightarrow>
     (\<And> e. e \<in> set (edges_of_vwalk p) \<Longrightarrow> f' e \<le> f e) \<Longrightarrow> unsaturated_path_simple G u f' s p t "
  by(auto intro: preorder_class.order.strict_trans1[of "f' _" "f _" "u _"] 
          simp add: unsaturated_path_simple_def)

context flow_network
begin

definition "is_blocking_flow s t f = (is_s_t_flow f s t \<and> 
                                     (\<nexists> p. multigraph_path p \<and> p \<noteq> [] \<and>
                                           fst (hd p) = s \<and> snd (last p) = t \<and> set p \<subseteq> \<E> \<and>
                                           (\<forall> e \<in> set p. f e < \<u> e)))"
end


end