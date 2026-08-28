theory Decomposition
  imports Augmentation
begin
context flow_network_spec
begin

text \<open>We define integrality for balance and flow functions.\<close>

definition "is_integral_flow (f::_\<Rightarrow> real) = (\<forall> e \<in> \<E>. \<exists> n::int. f e =  n)"

definition "is_integral_balance (b::'a \<Rightarrow> real) = (\<forall> v \<in> \<V>. \<exists> n::int. b v = n)"

section \<open>Decomposition of Flows\<close>

subsection \<open>Decomposition of Circulations\<close>

text \<open>In the subsequent part we argue that any non-trivial circulation can be decomposed 
into some distinct cycles..
\<close>

text \<open>For a vertex with some outgoing flow we try to find a list of successors.
The natural number indicates a maximum number of iterations.
\<close>

fun find_cycle::" ('edge \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
"find_cycle g 0 v= [v]"|
"find_cycle g (Suc n) v = v#(if (\<exists> e \<in> \<E>. g e > 0 \<and> fst e = v) then 
                                 (let e = (SOME e.  g e > 0  \<and> fst e = v \<and> e \<in>\<E>) 
                                   in find_cycle g n (snd e))
                             else [])"
end
context flow_network
begin
text \<open>For any non-trivial circulation we can find a list of vertices 
connected by edges carrying some flow. 
The length of this list is exactly the maximum iteration number,
i.e. there is no premature termination.
\<close>

lemma find_cycle_no_premature_termination:
 "\<lbrakk>is_circ g; flow_out g v > 0; g \<ge>\<^sub>F 0\<rbrakk> \<Longrightarrow> length (find_cycle g n v) = Suc n"
proof(induction g n v rule: find_cycle.induct)
  case (2 g n v)
  have all_e_pos:"\<And> e. e \<in> \<E> \<Longrightarrow> g e \<ge> 0"
    using "2.prems"(3) flow_non_neg_def by blast
  obtain e where a: "fst e = v \<and> g e > 0 \<and> e \<in> \<E>"  using 2(3) 
    unfolding flow_out_def delta_plus_def 
     proof-
    have "\<exists> e \<in> \<delta>\<^sup>+ v. 0 < g e"
    proof(rule ccontr)
      assume ass: "\<not> (\<exists> e \<in> \<delta>\<^sup>+ v. 0 < g e)"
      have "sum g (\<delta>\<^sup>+ v) \<le> 0"
      proof(rule sum_nonpos)
        fix e assume "e \<in> \<delta>\<^sup>+ v"
        thus "g e \<le> 0"
          using ass by auto
      qed
      moreover have "0 < sum g (\<delta>\<^sup>+ v)"
        using "2.prems"(2) by(simp add: flow_out_def)
      ultimately show False by simp
    qed
    then obtain d where d_prop: "d \<in> \<delta>\<^sup>+ v" "0 < g d" by auto
    show ?thesis
      using that[of d] d_prop by(auto simp add: delta_plus_def)
  qed
   hence b:"(\<exists>e\<in>\<E>. 0 < g e \<and> fst e = v) = True" by auto
   then obtain d where d_def: "d = (SOME e. 0 < g e \<and> fst e = v \<and> e \<in>\<E>)" by simp
   hence b1:"fst d = v" "g d > 0" "d \<in> \<E>" 
     proof -
  have ex_e: "\<exists>x. 0 < g x \<and> fst x = v \<and> x \<in> \<E>"
    using a by blast
  have some_prop: "0 < g d \<and> fst d = v \<and> d \<in> \<E>"
    unfolding d_def by (rule someI_ex[OF ex_e])
  show "fst d = v" using some_prop by simp
  show "g d > 0" using some_prop by simp
  show "d \<in> \<E>" using some_prop by simp
qed
   have c: "find_cycle g (Suc n) v = v#find_cycle g n (snd d)"
      using b d_def by auto
   have d: "(snd d) \<in> \<V>"
      using  b1 dVsI(1) dVsI(2)
      by(auto simp add: snd_E_V fst_E_V)
   hence e:"ex g (snd d) = 0" 
     using 2(2) unfolding is_circ_def by simp
   moreover have f:"flow_in g (snd d) > 0"
     unfolding flow_in_def
     using b1
     by (fastforce intro!: ordered_comm_monoid_add_class.sum_pos2[of _ "d", OF delta_minus_finite]
                 simp add: all_e_pos delta_minus_def delta_minus_finite)
   ultimately have f:"flow_out g (snd d) > 0"
     by (simp add: ex_def flow_in_def flow_out_def)
   show ?case 
     apply(subst c, simp)
     using b d_def  2(2) f 2(4)
     by(intro 2(1)[of d], auto intro: 2(1)[of d])
qed simp

text \<open>When searching for a cycle, no vertex outside $\mathcal{V}$ is collected.\<close>

lemma find_cycle_subset_V: 
  "v \<in> \<V> \<Longrightarrow> set (find_cycle g n v) \<subseteq> \<V>"
proof(induction g n v rule: find_cycle.induct)
  case (2 g n v)
  then show ?case 
  proof(cases "\<exists>e\<in>\<E>. 0 < g e \<and> fst e = v")
    case True
    then obtain e where e_Def:"e = (SOME e. 0 < g e \<and> fst e = v \<and> e \<in> \<E>)" by auto
    hence a:"0 < g e" "fst e = v" "e \<in> \<E>" 
      by (metis (mono_tags, lifting) True someI_ex)+
    hence b:"snd e \<in> \<V>" 
      using  a dVsI(1) dVsI(2) 
      by(auto simp add: snd_E_V fst_E_V )
    show ?thesis 
      using True e_Def b 2 
      by auto
  next
    case False
    then show ?thesis 
      using "2.prems" by auto
  qed
qed simp

text \<open>For non-trivial circulations,
       we find a vertex-based cycle connected by edges while carrying positive flow.\<close>

lemma pos_circ_cycle:
  assumes "g \<ge>\<^sub>F 0"  "Abs g > 0"  "is_circ g"
  shows   "(\<exists> v as bs cs x. (find_cycle g (card \<V>) v) = as@[x]@bs@[x]@cs
                             \<and> distinct bs \<and> v \<in>\<V> \<and> x \<notin> set bs \<and> flow_out g v > 0)"
proof-
  obtain v where v_def: " flow_out g v > 0 \<and> v \<in> \<V>" using assms
    using Abs_pos_some_node_pos isbflow_def by blast
  moreover have "is_circ g" using assms by simp
  ultimately have cc: "length (find_cycle g (card  \<V>) v) = Suc (card  \<V>)"
    using find_cycle_no_premature_termination[of g v  "card  \<V>"] assms by simp
  moreover have ff:"set (find_cycle g (card  \<V>) v) \<subseteq> \<V>"
    using  find_cycle_subset_V[of v g "card  \<V>"] v_def by simp
  moreover have "card \<V> < length (find_cycle g (card  \<V>) v)" using cc by simp
  moreover hence "\<not> distinct (find_cycle g (card  \<V>) v)" 
    using double_occur_non_dist[of "(find_cycle g (card  \<V>) v)" \<V>] ff 
    using \<V>_finite by fastforce
  ultimately show ?thesis 
    using list_triple_split_mid_distinct[of "(find_cycle g (card  \<V>) v)" "Suc (card  \<V>)"]
          v_def by blast
qed

text \<open>So far we have just obtained paths and cycles emerging from vertices.
For our reasoning, however, we need paths on arcs. The subsequent part will bridge that gap.\<close>

lemma find_cycle_gives_flowpath:
  assumes "v \<in> \<V>"
  shows "\<exists> es. length es = length (find_cycle g n v) -1 \<and> 
               (\<forall> i < length es. fst (es ! i) = ((find_cycle g n v) ! i) \<and>
               snd (es ! i) = ((find_cycle g n v) ! (i+1))) \<and>
               flowpath g es \<and> set es \<subseteq> \<E> \<and> set es \<subseteq> support g"
proof(induction g n v rule: find_cycle.induct)
  case (2 g n v)
  then show ?case
  proof(cases "(\<exists> e \<in>\<E>. g e > 0 \<and> fst e = v)")
    case True
    then obtain e where x_def: "e = (SOME e. 0 < g e \<and> fst e = v \<and> e \<in> \<E>)"
      by simp
    hence aaa:"0 < g e" "fst e = v" "e \<in> \<E>" 
      proof -
        have ex_e: "\<exists>e. 0 < g e \<and> fst e = v \<and> e \<in> \<E>"
          using True by blast
        have all_three: "0 < g e \<and> fst e = v \<and> e \<in> \<E>"
          unfolding x_def by (rule someI_ex[OF ex_e])
        show "0 < g e" using all_three by blast
        show "fst e = v" using all_three by blast
        show "e \<in> \<E>" using all_three by blast
      qed
    hence find_cycle_prop: "find_cycle g (Suc n) v = v#(find_cycle g n (snd e))" 
      using True x_def by simp
    obtain es where es_def: "length es = length (find_cycle g n (snd e)) - 1 \<and>
                  (\<forall>i<length es.
                    fst (es ! i) = find_cycle g n (snd e) ! i \<and>
                    snd (es ! i) = find_cycle g n (snd e) ! (i + 1)) \<and>
                    flowpath g es \<and> set es \<subseteq> \<E> \<and> set es \<subseteq> support g"
      using "2" True x_def by presburger
    have "length (e#es) = length (find_cycle g (Suc n) v) - 1" 
      using find_cycle_prop es_def 
      proof -
        have ne: "find_cycle g n (snd e) \<noteq> []"
          by (cases n) auto
        then obtain u us where cons: "find_cycle g n (snd e) = u # us"
          by (auto simp add: neq_Nil_conv)
        have es_len: "length es = length (find_cycle g n (snd e)) - 1"
          using es_def by simp
        have len_suc: "length (find_cycle g (Suc n) v) = Suc (length (find_cycle g n (snd e)))"
          by (simp only: find_cycle_prop length_Cons)
        have "length (e # es) = Suc (length es)" by simp
        also have "\<dots> = Suc (length us)"
          using es_len cons by simp
        also have "\<dots> = length (find_cycle g n (snd e))"
          using cons by simp
        also have "\<dots> = length (find_cycle g (Suc n) v) - 1"
          by (simp only: len_suc diff_Suc_1)
        finally show ?thesis .
      qed
    moreover have "i<length (e#es) \<Longrightarrow>
                    fst ((e#es) ! i) = find_cycle g (Suc n) v ! i \<and>
                    snd ((e#es) ! i) = find_cycle g (Suc n) v ! (i + 1)" for i
    proof -
      assume ilen: "i < length (e # es)"
      show "fst ((e # es) ! i) = find_cycle g (Suc n) v ! i \<and>
            snd ((e # es) ! i) = find_cycle g (Suc n) v ! (i + 1)"
      proof(cases i)
        case 0
        have hd_fc: "find_cycle g n (snd e) ! 0 = snd e"
          by (cases n) auto
        have fst0: "fst ((e # es) ! i) = find_cycle g (Suc n) v ! i"
          using 0 aaa unfolding find_cycle_prop by simp
        have snd0: "snd ((e # es) ! i) = find_cycle g (Suc n) v ! (i + 1)"
          using 0 hd_fc unfolding find_cycle_prop by simp
        show ?thesis
          using fst0 snd0 by blast
      next
        case (Suc j)
        have jlen: "j < length es"
          using ilen Suc by simp
        have esj: "fst (es ! j) = find_cycle g n (snd e) ! j \<and>
                   snd (es ! j) = find_cycle g n (snd e) ! (j + 1)"
          using es_def jlen by blast
        show ?thesis
          using esj Suc unfolding find_cycle_prop by simp
      qed
    qed
    moreover have " flowpath g (e#es)" 
        using  calculation(2)[of 1] calculation(2)[of 0] es_def find_cycle_prop aaa
        by (cases es) (auto intro: flowpath_intros)
    moreover have "set (e#es) \<subseteq> \<E>" 
          using aaa es_def by auto
   moreover have "set (e#es) \<subseteq> support g" 
          using es_def 
          by (simp add: aaa support_def)
   ultimately show ?thesis by blast
  next
    case False
    hence "find_cycle g (Suc n) v = [v]"
      using find_cycle.simps(2) by presburger
    hence "length [] = length  (find_cycle g  (Suc n) v) -1 "
          "flowpath g []" 
      using flowpath_intros by auto
      then show ?thesis by simp
  qed
qed (force simp add: flowpath_intros)
end
context flow_network_spec
begin
text \<open>Analogously to augmenting paths and cycles, we define the concept of a cycle.\<close>

definition "flowcycle g es = (flowpath g es \<and> es \<noteq> [] \<and> fst (hd es) = snd(last es))"
end

context 
  flow_network
begin

lemma flow_path_mono: 
  assumes "flowpath g' es " 
  shows   "(\<And> e. e \<in> (set es) \<Longrightarrow> g e \<ge> g' e)  \<Longrightarrow> flowpath g es"
  by(induction  rule: flowpath_induct[OF assms])
    (fastforce simp add: flowpath_intros)+

lemma flow_cyc_mono:  "flowcycle g' es \<Longrightarrow> (\<And> e. e \<in> (set es) \<Longrightarrow> g e \<ge> g' e)  \<Longrightarrow> flowcycle g es"
  unfolding flowcycle_def
  using flow_path_mono by blast

lemma flowpath_es_non_neg:
  assumes "flowpath g es"
  shows   "(\<forall> e \<in> set es. g e > 0)"
  by(induction g es rule: flowpath_induct, simp add: assms) simp+

text \<open>For any non-trivial circulation we obtain a cycle based on edges,
      where any vertex is visited at most once.\<close>

theorem find_flow_cycle_in_circ:
  assumes "g \<ge>\<^sub>F 0" "Abs g > 0"  "is_circ g"
  shows   "\<exists> es. flowcycle g es \<and> set es \<subseteq> support g \<and> distinct es \<and> 
               (\<forall> v \<in>\<V>. (\<exists> eov eiv. \<delta>\<^sup>+ v \<inter> set es = {eov} \<and>  \<delta>\<^sup>- v \<inter> set es = {eiv}) \<or>
                        (\<delta>\<^sup>+ v \<inter> set es = {} \<and>  \<delta>\<^sup>- v \<inter> set es = {}))"
proof-
  obtain  v as bs cs x where v_Def: "(find_cycle g (card \<V>) v) = as@[x]@bs@[x]@cs \<and> 
                                   distinct bs \<and> v \<in> \<V> \<and> x \<notin> set bs \<and> 0 < flow_out g v"
    using pos_circ_cycle assms by blast
  then obtain es where es_prop: " length es = length (find_cycle g (card \<V>) v) - 1"
                         "(\<forall>i<length es.
                               fst (es ! i) = find_cycle g (card \<V>) v ! i \<and>
                               snd (es ! i) = find_cycle g (card \<V>) v ! (i + 1))"
                         "flowpath g es" "set es \<subseteq> \<E>" " set es \<subseteq> support g "
    using find_cycle_gives_flowpath[of v g "card \<V>"] by auto
  hence "length es = card (\<V>)" 
    using v_Def find_cycle_no_premature_termination[of g  v "(card \<V>)"] assms(3) assms(1) by simp
  define a_len where "a_len = length as"  
  have "a_len < length es" using v_Def es_prop
    by (simp add: a_len_def)
  have "es = take (a_len) es @ (drop  a_len es)" by simp 
  define a_rst where "a_rst =  (drop  a_len es)"
  have "length a_rst = length es - a_len" 
    by (simp add: a_rst_def)
  have "a_rst \<noteq> []" 
    using \<open>a_len < length es\<close> a_rst_def by force
  hence a_rst_prop:"(\<forall>i<length a_rst. fst (a_rst ! i) = find_cycle g (card \<V>) v ! (a_len + i) \<and>
                               snd (a_rst ! i) = find_cycle g (card \<V>) v ! (a_len +i + 1))"
    using es_prop add.commute add_diff_cancel_right' less_diff_conv a_rst_def by auto
  define b_len where "b_len = length (bs@[x])"
  have "b_len \<le> length a_rst" 
    using a_rst_def v_Def a_rst_prop es_prop
     by (simp add: a_len_def b_len_def)
  have "a_rst = take b_len a_rst @ (drop b_len a_rst)" by simp 
  define ES where "ES = take b_len a_rst"
  have Es_len_b_len:"length ES = b_len"
    using ES_def \<open>b_len \<le> length a_rst\<close> by force
  have ES_prop:"(\<forall>i<length ES. fst (ES ! i) = find_cycle g (card \<V>) v ! (a_len + i) \<and>
                               snd (ES ! i) = find_cycle g (card \<V>) v ! (a_len + i + 1))"
    using ES_def a_rst_prop by force
  hence ES_prop': "i<length ES \<Longrightarrow>fst (ES ! i) = find_cycle g (card \<V>) v ! (a_len + i)"
                  "i<length ES \<Longrightarrow>snd (ES ! i) = find_cycle g (card \<V>) v ! (a_len + i + 1)" for i
    by auto
  have " flowpath g ES " 
    using ES_def a_rst_def append_take_drop_id[of a_len es] append_take_drop_id[of b_len a_rst]
          es_prop(3) flow_path_split_left[ of g "take b_len a_rst" "drop b_len a_rst"]
          flow_path_split_right[of g  "take a_len es" "drop a_len es"] 
    by simp
 moreover have " ES \<noteq> []" 
    using ES_def \<open>a_rst \<noteq> []\<close> b_len_def by force
  moreover hence "fst (ES ! 0) = x"
    using ES_prop v_Def es_prop a_len_def by simp
  moreover hence "fst (hd ES) = x" 
    by (simp add: \<open>ES \<noteq> []\<close> hd_conv_nth)
  moreover have "snd (ES ! (b_len-1)) = x" 
    using ES_prop v_Def es_prop a_len_def  \<open>ES \<noteq> []\<close> \<open>length ES = b_len\<close>  b_len_def 
           nth_append_length_plus[of "as" "[x]@bs @ [x] @ cs" "b_len"] nth_append_length 
    by simp
  moreover hence "snd (last ES) = x" 
    by (simp add: \<open>ES \<noteq> []\<close> \<open>length ES = b_len\<close> last_conv_nth)
  ultimately have  "flowcycle g ES" unfolding flowcycle_def by simp
  have "set ES \<subseteq> support g" unfolding ES_def a_rst_def using es_prop 
    by (meson in_set_dropD in_set_takeD subset_code(1))
  have xbs_distinct: "distinct ([x]@bs)" using v_Def by simp
  moreover have "distinct ES"
  proof(rule ccontr)
    assume "\<not> distinct ES "
    then obtain i j where ij_def: "i < length ES \<and> j < length ES \<and> j \<noteq> i \<and> ES ! i = ES ! j" 
      using distinct_conv_nth by blast
    hence "find_cycle g (card \<V>) v ! (a_len + i) =
             find_cycle g (card \<V>) v ! (a_len + j)"
      by (simp add: ij_def ES_prop[rule_format, THEN conjunct1, symmetric])
    hence "(as @ [x] @ bs @ [x] @ cs) ! (a_len + i) =
           (as @ [x] @ bs @ [x] @ cs)  ! (a_len + j) " using v_Def by simp
    hence "([x]@bs@[x]@cs) !  i =  ([x]@bs@[x]@cs) ! j" unfolding a_len_def by simp
    hence aaa:"([x]@bs) !  i =  ([x]@bs) ! j" 
      using  One_nat_def ij_def \<open>length ES = b_len\<close> b_len_def 
      using nth_append'[of "[x] @ bs" "[x] @ cs" i j] by simp
    from aaa ij_def have "\<not> distinct ([x]@bs)" 
      using \<open>length ES = b_len\<close> add.commute b_len_def 
             length_append nth_eq_iff_index_eq[of "[x]@bs"] by auto
    from this xbs_distinct show False by simp
  qed
  have ES_prop':" i<length ES \<Longrightarrow>  fst (ES ! i) = ([x]@bs) ! i \<and>
                               snd (ES ! i) =  ([x]@bs) ! ((i + 1) mod b_len)" for i
  proof-
    assume i_assm: "i < length ES"
    hence " fst (ES ! i) = find_cycle g (card \<V>) v ! (a_len + i)" 
      using ES_prop by simp
    also have "... =  ( as@[x]@bs@[x]@cs) ! (a_len + i)" 
      using v_Def by simp
    also have "... =  ([x]@bs@[x]@cs) ! i"
      by (simp add: a_len_def)
    finally have "fst (ES ! i) = ([x] @ bs) ! i" 
      using \<open>i < length ES\<close> \<open>length ES = b_len\<close>  b_len_def  nth_append[of "[x]@bs" "[x]@cs" i]
      by simp
    moreover have round_property: "snd (ES ! i) =  ([x]@bs) ! ((i + 1) mod b_len)"
    proof(cases "i+1 < b_len")
      case True
      hence " snd (ES ! i) = find_cycle g (card \<V>) v ! (a_len + i +1)" using ES_prop 
        using \<open>i < length ES\<close> by blast
    also have "... =  ( as@[x]@bs@[x]@cs) ! (a_len + i + 1)" using v_Def by simp
    also have "... =  ([x]@bs@[x]@cs) ! (i+1)" 
      using a_len_def  nth_append_length_plus[of as "[x] @ bs @ [x] @ cs" "i+1"] by simp  
    finally have "snd (ES ! i) = ([x] @ bs) ! (i+1)" 
      using True[simplified b_len_def]  nth_append[of "[x] @ bs" "[x] @ cs" "i+1"]
      by simp
    then show ?thesis 
        using True mod_less by presburger
    next
      case False
      hence "i = b_len - 1"  
        using i_assm Es_len_b_len by simp
      hence "(i + 1) mod b_len = 0" 
        using Es_len_b_len \<open>ES \<noteq> []\<close> by fastforce
      hence "([x] @ bs) ! ((i + 1) mod b_len) = x" by simp
      moreover have "snd (ES ! i) = x" 
        using \<open>i = b_len - 1\<close> \<open>snd (ES ! (b_len - 1)) = x\<close> by blast 
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by simp
  qed
  moreover have ES_in_E: "set ES \<subseteq> \<E>" 
    using ES_def a_rst_def es_prop  set_drop_subset set_take_subset by fastforce
  moreover have "u \<in> \<V> \<Longrightarrow> (\<exists>eov eiv. \<delta>\<^sup>+ u \<inter> set ES = {eov} \<and> \<delta>\<^sup>- u \<inter> set ES = {eiv})
                   \<or> (\<delta>\<^sup>+ u \<inter> set ES = {} \<and> \<delta>\<^sup>- u \<inter> set ES = {})"              for u
  proof-
    assume " u \<in> \<V> "
    show " (\<exists>eov eiv. \<delta>\<^sup>+ u \<inter> set ES = {eov} \<and> \<delta>\<^sup>- u \<inter> set ES = {eiv}) \<or>
             \<delta>\<^sup>+ u \<inter> set ES = {} \<and> \<delta>\<^sup>- u \<inter> set ES = {}"
    proof(cases "\<delta>\<^sup>+ u \<inter> set ES = {} \<and> \<delta>\<^sup>- u \<inter> set ES = {}")
      case False
      hence "\<delta>\<^sup>+ u \<inter> set ES \<noteq> {} \<or> \<delta>\<^sup>- u \<inter> set ES \<noteq> {}" by simp
      then show ?thesis 
      proof(cases "\<delta>\<^sup>+ u \<inter> set ES \<noteq> {}")
        case True
        then obtain eov where eov_def: "eov \<in> \<delta>\<^sup>+ u \<and> eov \<in>  set ES" by auto
        then obtain i where i_def: "i < length ES \<and> ES ! i = eov" 
          by (meson in_set_conv_nth)
        hence fst_i_prop: "fst (ES ! i) = ([x] @ bs) ! i" 
          using ES_prop'[of i] by simp
        hence ui_prop: "u = ([x] @ bs) ! i"
          using eov_def unfolding delta_plus_def
          using i_def by blast
        have "eov' \<in> \<delta>\<^sup>+ u \<and> eov' \<in>  set ES \<Longrightarrow> eov' \<noteq> eov \<Longrightarrow> False" for eov'
        proof-
          assume subassm: "eov' \<in> \<delta>\<^sup>+ u \<and> eov' \<in> set ES " "eov' \<noteq> eov"
          then obtain j where j_def: "j < length ES \<and> ES ! j = eov' \<and> j \<noteq> i" 
            proof -
              have "eov' \<in> set ES" using subassm(1) by simp
              then obtain j where j_lt: "j < length ES" and j_nth: "ES ! j = eov'"
                unfolding in_set_conv_nth by blast
              have "j \<noteq> i"
              proof
                assume "j = i"
                hence "eov' = eov" using i_def j_nth by simp
                thus False using subassm(2) by simp
              qed
              thus thesis using that j_lt j_nth by blast
            qed
          hence "fst (ES ! j) = ([x] @ bs) ! j" 
            using ES_prop' by blast 
          moreover have "fst eov' = fst eov" 
            using delta_plus_def eov_def subassm(1) by fastforce
          ultimately have  "\<not> distinct ([x] @ bs)"  
            using Es_len_b_len \<open>fst (ES ! i) = ([x] @ bs) ! i\<close> b_len_def i_def j_def 
                 length_append nth_eq_iff_index_eq[of "[x] @ bs" i j] by auto
          then show ?thesis
           using xbs_distinct by blast
       qed
      hence "\<delta>\<^sup>+ u \<inter> set ES = {eov}" using eov_def by auto
      have "b_len > 0" 
        using Es_len_b_len \<open>ES \<noteq> []\<close> by blast
      moreover hence " nat ((int i - 1) mod int b_len) < length ES" 
        using Es_len_b_len mod_less_divisor nat_int nat_less_iff by force
      hence 003:"snd (ES ! nat ((int i - 1) mod int b_len)) =
               ([x] @ bs) ! ((nat ((int i - 1) mod int b_len) + 1) mod b_len)"
        using  ES_prop'[of "nat ((int i-1) mod b_len)"]  by simp
      have 001:"(nat ((int i - 1) mod int b_len) + 1) mod b_len = 
            nat ((((int i - 1) mod int b_len) + 1) mod b_len)" 
        by (simp add: calculation nat_add_distrib nat_mod_distrib)
      also have 002:"nat ((((int i - 1) mod int b_len) + 1) mod b_len) = 
                nat ((((int i - 1) +1) mod int b_len) )" 
        by presburger
      also have fgh: "... = nat (((int i)  mod int b_len) )" by simp
      finally have nat_i_int:"(nat ((int i - 1) mod int b_len) + 1) mod b_len  = i" 
      proof -
        have i_less: "i < b_len"
          using i_def Es_len_b_len by simp
        hence "nat (int i mod int b_len) = i"
          by (simp flip: zmod_int)
        thus ?thesis
          using 001 002 fgh by simp
      qed
      hence "snd (ES ! (nat (((int i)-1) mod b_len))) =
                      (([x] @ bs) ! nat ((((int i)-1)+1) mod b_len) )" using
        ES_prop'[of "nat ((int i-1) mod b_len)"]  
        using 001 002 003 by presburger
      hence w_prop: "snd (ES ! nat ((int i - 1) mod int b_len)) 
                  = ([x] @ bs) ! i"
        using "003" nat_i_int by presburger
      then obtain w where w_def: "w = snd (ES ! nat ((int i - 1) mod int b_len))" by simp 
      hence w_prop':"w =  ([x] @ bs) ! i"using w_prop by simp
      hence w_u_eq: " u = w" 
        using ui_prop by blast
      obtain eiv where eiv_def: "eiv = ES ! nat ((int i - 1) mod int b_len)" by simp
      hence "eiv \<in> set ES " 
        using \<open>nat ((int i - 1) mod int b_len) < length ES\<close> nth_mem by blast
      have hij:"nat ((int i - 1) mod int b_len) < b_len"
        using Es_len_b_len \<open>nat ((int i - 1) mod int b_len) < length ES\<close> by blast
      moreover have "eiv \<in> \<delta>\<^sup>- u" unfolding delta_minus_def 
        apply(subst w_u_eq)
        unfolding eiv_def w_def 
        using ES_in_E \<open>eiv \<in> set ES\<close> eiv_def by auto 
      hence "eiv \<in> \<delta>\<^sup>- u \<inter> set ES " 
        unfolding delta_minus_def 
        using \<open>eiv \<in> set ES\<close> by blast
      have "eiv' \<in> \<delta>\<^sup>- u \<and> eiv' \<in>  set ES \<Longrightarrow> eiv' \<noteq> eiv \<Longrightarrow> False" for eiv'
      proof-
        assume subassm: "eiv' \<in> \<delta>\<^sup>- u \<and> eiv' \<in>  set ES" "eiv' \<noteq> eiv"
        then obtain j where j_def: "j < length ES" "ES ! j = eiv'" 
                                   "j \<noteq> nat ((int i - 1) mod int b_len)"
        proof -
          obtain k where k_less: "k < length ES" and k_nth: "ES ! k = eiv'"
            using subassm(1) by (auto simp add: in_set_conv_nth)
          have k_neq: "k \<noteq> nat ((int i - 1) mod int b_len)"
          proof(rule notI)
            assume "k = nat ((int i - 1) mod int b_len)"
            hence "eiv' = eiv"
              using k_nth eiv_def by simp
            thus False
              using subassm(2) by simp
          qed
          show thesis
            by(rule that[OF k_less k_nth k_neq])
        qed
        hence "snd (ES ! j) = ([x] @ bs) ! ((j+1) mod b_len)" 
          using ES_prop' by blast 
        moreover have "snd (ES ! i) =  ([x] @ bs) ! ((i+1)  mod b_len)"
        using ES_prop'  i_def by blast 
        moreover have " snd eiv' = snd eiv"
          using \<open>eiv \<in> \<delta>\<^sup>- u\<close> delta_minus_def subassm(1) by auto
        moreover have "(j+1) mod b_len \<noteq> i mod b_len"  
          using Es_len_b_len   hij mod_less[of "j+1" "length ES"] j_def i_def
                 nat_i_int  mod_less[of "j+1" "length ES", simplified Es_len_b_len]    
          by (cases "j +1 = length ES")  auto       
        ultimately have  "\<not> distinct ([x] @ bs)" 
          using hij j_def 
          proof -
          let ?k = "nat ((int i - 1) mod int b_len)"
          have blen_eq: "length ([x] @ bs) = b_len"
            using b_len_def by simp
          have i_less: "i < b_len"
            using i_def Es_len_b_len by simp
          have j_less: "j < b_len"
            using j_def(1) Es_len_b_len by simp
          have mod_suc: "(a + 1) mod b_len = (if a + 1 = b_len then 0 else a + 1)"
            if "a < b_len" for a
          proof(cases "a + 1 = b_len")
            case True
            thus ?thesis by simp
          next
            case False
            have "a + 1 \<le> b_len" using that by simp
            hence "a + 1 < b_len" using False by (simp add: less_le)
            thus ?thesis using False by simp
          qed
          have snd_j: "snd (ES ! j) = ([x] @ bs) ! ((j + 1) mod b_len)"
            using ES_prop'[OF j_def(1)] by blast
          have snd_eiv: "snd eiv = ([x] @ bs) ! i"
            using w_prop eiv_def by simp
          have snd_eq: "snd eiv' = snd eiv"
            using subassm(1) \<open>eiv \<in> \<delta>\<^sup>- u\<close> by (auto simp add: delta_minus_def)
          have nth_eq: "([x] @ bs) ! ((j + 1) mod b_len) = ([x] @ bs) ! i"
          proof-
            have "([x] @ bs) ! ((j + 1) mod b_len) = snd (ES ! j)" using snd_j by simp
            also have "... = snd eiv'" using j_def(2) by simp
            also have "... = snd eiv" using snd_eq by simp
            also have "... = ([x] @ bs) ! i" using snd_eiv by simp
            finally show ?thesis by simp
          qed
          show ?thesis
          proof
            assume dist: "distinct ([x] @ bs)"
            have idx1: "(j + 1) mod b_len < length ([x] @ bs)"
              using \<open>0 < b_len\<close> blen_eq by simp
            have idx2: "i < length ([x] @ bs)"
              using i_less blen_eq by simp
            have j1: "(j + 1) mod b_len = i"
              using nth_eq_iff_index_eq[OF dist idx1 idx2] nth_eq by simp
            have "j = ?k"
            proof(cases "j + 1 = b_len")
              case True
              hence i0: "i = 0" using j1 by simp
              have "?k + 1 = b_len"
              proof(rule ccontr)
                assume "?k + 1 \<noteq> b_len"
                hence "(?k + 1) mod b_len = ?k + 1" using mod_suc[OF hij] by simp
                hence "?k + 1 = i" using nat_i_int by simp
                thus False using i0 by simp
              qed
              hence "j + 1 = ?k + 1" using True by simp
              thus ?thesis by simp
            next
              case False
              have "i = (j + 1) mod b_len" using j1 by simp
              also have "... = j + 1" using mod_suc[OF j_less] False by simp
              finally have jv: "i = j + 1" by simp
              have k_ne: "?k + 1 \<noteq> b_len"
              proof
                assume "?k + 1 = b_len"
                hence "(?k + 1) mod b_len = 0" by simp
                hence "i = 0" using nat_i_int by simp
                thus False using jv by simp
              qed
              have "?k + 1 = (?k + 1) mod b_len" using mod_suc[OF hij] k_ne by simp
              also have "... = i" using nat_i_int by simp
              finally have "?k + 1 = j + 1" using jv by simp
              thus ?thesis by simp
            qed
            thus False using j_def(3) by simp
          qed
        qed        then show False 
            using xbs_distinct by blast
        qed
        hence "\<delta>\<^sup>- u \<inter> set ES = {eiv}" 
          using \<open>eiv \<in> \<delta>\<^sup>- u \<inter> set ES\<close> by blast
        then show ?thesis 
          by (simp add: \<open>\<delta>\<^sup>+ u \<inter> set ES = {eov}\<close>)
      next
        case False
        hence "\<delta>\<^sup>- u \<inter> set ES \<noteq> {}" 
          using \<open>\<delta>\<^sup>+ u \<inter> set ES \<noteq> {} \<or> \<delta>\<^sup>- u \<inter> set ES \<noteq> {}\<close> by auto
        then obtain ie where ie_def: "ie \<in> \<delta>\<^sup>- u \<and> ie \<in> set ES" by auto 
        then obtain i where "i < b_len \<and> ES ! i = ie" 
          using ie_def by (auto simp add: in_set_conv_nth Es_len_b_len)
        have "snd ie = u" using ie_def unfolding delta_minus_def by simp
        have "b_len > 0" 
          using Es_len_b_len \<open>ES \<noteq> []\<close> by blast
        have "u = ([x] @ bs) ! ((i + 1) mod b_len)"
        using ES_prop'[of i]  
        using Es_len_b_len \<open>i < b_len \<and> ES ! i = ie\<close> \<open>snd ie = u\<close> by fastforce
      obtain oe where "fst oe = u \<and> oe \<in> set ES"
        using ES_prop'[of "(i + 1) mod b_len"]  Es_len_b_len \<open>0 < b_len\<close>
               \<open>u = ([x] @ bs) ! ((i + 1) mod b_len)\<close> mod_less_divisor nth_mem by blast
       hence "oe \<in> \<delta>\<^sup>+ u \<inter> set ES" 
         using ES_in_E delta_plus_def by blast
       then show ?thesis using False by auto
      qed
    qed blast
  qed
  ultimately show ?thesis 
    using \<open>distinct ES\<close> \<open>flowcycle g ES\<close> \<open>set ES \<subseteq> support g\<close> by blast
qed

text \<open>Finally, assume a valid and non-trivial circulation.
We can find a list of flowcycles and corresponding weights, such that
the  flow through any edge equals the accumulated weights of all cycles where this arc is involved.

The claim is shown by induction on the cardinality of the support, 
i.e. the number of edges with non-negative flow assigned.

In the proof, we search for a cycle. This has to exist, since the circulation is non-trivial.
Then we subtract the minimum flow in the cycle from the remaining circulation and continue.
\<close>

theorem flowcycle_decomposition:
  assumes "g \<ge>\<^sub>F 0" "0 < Abs g" "is_circ g"
          "support g \<noteq> {}" "card (support g) = n"
  shows "\<exists> css ws.
   length css = length ws \<and>
   set css \<noteq> {} \<and> 
   (\<forall> w \<in> set ws. w > 0)\<and>
   (\<forall> cs \<in> set css. flowcycle g cs \<and> set cs \<subseteq> support g \<and> distinct cs) \<and>
   (\<forall> e \<in> \<E>. g e = (\<Sum> i < length css. ( if e \<in> set (css ! i) then ws ! i else 0))) \<and>
   (is_integral_flow g \<longrightarrow> (\<forall> w \<in> set ws. \<exists> n::nat. w = real n))"
  using assms 
proof(induction n arbitrary: g rule: less_induct)
  case (less n) 
  have"finite (support g)"
    unfolding support_def 
    using finite_E by auto
  hence "n > 0"
    using card_0_eq less.prems(4) less.prems(5) by blast
  obtain es where es_Def:  "flowcycle g es" 
                   "set es \<subseteq> support g"
                   "distinct es"
                   "\<And> v. v\<in>\<V> \<Longrightarrow> (\<exists>eov eiv. \<delta>\<^sup>+ v \<inter> set es = {eov} \<and> \<delta>\<^sup>- v \<inter> set es = {eiv}) \<or>
                   \<delta>\<^sup>+ v \<inter> set es = {} \<and> \<delta>\<^sup>- v \<inter> set es = {}" 
    using find_flow_cycle_in_circ less.prems(1) less.prems(2) less.prems(3) by force
  hence e_not_empty: "es \<noteq> []" unfolding flowcycle_def by simp
  define \<gamma> where "\<gamma> = foldr (\<lambda> e gam. min (g e) gam) es (g (last es))"

  hence gamma_less_Es: "\<And> e. e \<in> set es \<Longrightarrow> \<gamma> \<le> g e"
    unfolding \<gamma>_def
  proof(induction es)
    case (Cons b es)
    note cons = this
    then show ?case 
    proof(cases es)
      case (Cons a list)
      hence lasty: "last (b # es) = last es" by simp
      have "foldr (\<lambda>e. min (g e)) (b # es) (g (last (b # es))) = 
             min (g b) (foldr (\<lambda>e. min (g e)) (es) (g (last (es))))" 
        by(subst lasty) simp
      then show ?thesis 
        using Cons.IH cons(2) by fastforce
    qed simp      
  qed simp

  have e_gamma_eq: "\<exists> e \<in> set es. g e = \<gamma>"
    using e_not_empty unfolding \<gamma>_def
  proof(induction es)
    case (Cons a es)
    note cons = this
    then show ?case 
    proof(cases es)
      case (Cons a list)
      from this cons  show ?thesis 
      unfolding comp_def 
      by(cases "(g a) \<le>(foldr (\<lambda>e. min (g e)) es (g (last (a # es))))")
           (auto simp add: min_def_raw)
    qed simp
  qed simp

  have aaaa:"flowpath g es" using es_Def(1) unfolding flowcycle_def by simp
  hence gamma_greater_zero: "\<gamma> > 0"
    using e_not_empty unfolding \<gamma>_def
    by(induction rule: flowpath_induct[OF aaaa]) simp+

  have integral_gamma: "is_integral_flow g \<Longrightarrow>
          \<exists>n::nat. \<gamma> = n"
    using e_not_empty less(2) es_Def(2) zero_less_imp_eq_int
    unfolding \<gamma>_def is_integral_flow_def flow_non_neg_def support_def 
    by(induction es) (fastforce intro!: min_integral simp add:  \<gamma>_def is_integral_flow_def flow_non_neg_def support_def )+
      
  define g' where "g' = (\<lambda> e. (if e \<in> set es then  g e - \<gamma> else g e))"

  then obtain eee where "eee \<notin> support g'\<and> eee \<in> support g"
    using e_gamma_eq es_Def(2) support_def by fastforce 

  have integral_g: "is_integral_flow g \<Longrightarrow>is_integral_flow g'"
  proof -
    assume asm: "is_integral_flow g"
    then obtain m :: nat where m: "\<gamma> = real m"
      using integral_gamma by blast
    show "is_integral_flow g'"
      unfolding is_integral_flow_def
    proof
      fix e
      assume "e \<in> \<E>"
      then obtain k :: int where k: "g e = real_of_int k"
        using asm by (auto simp add: is_integral_flow_def)
      show "\<exists> n::int. g' e = n"
      proof(cases "e \<in> set es")
        case True
        have "g' e = real_of_int k - real m"
          using True k m by (simp add: g'_def)
        also have "\<dots> = real_of_int (k - int m)" by simp
        finally show ?thesis by blast
      next
        case False
        hence "g' e = real_of_int k"
          using k by (simp add: g'_def)
        thus ?thesis by blast
      qed
    qed
  qed

  have g_greater_g': "e \<in> set es \<Longrightarrow>g e\<ge> g' e " for e
    unfolding g'_def 
    using gamma_greater_zero by auto

  have g'_non_neg:"g' \<ge>\<^sub>F 0" unfolding flow_non_neg_def
  proof
    fix e
    assume " e \<in> \<E>"
    thus "0 \<le> g' e "
      using gamma_less_Es  g'_def less.prems(1) flow_non_neg_def 
      by (cases "e \<in> set es") auto
  qed
  
  have " Abs g' \<ge> 0" unfolding Abs_def 
  proof(rule sum_nonneg)
    fix e
    assume "e \<in> \<E>"
    thus "0 \<le> g' e"
      using gamma_less_Es g'_def less.prems(1) flow_non_neg_def
      by (cases "e \<in> set es") auto
  qed

  then show ?case 
  proof(cases "0 =  Abs g'")
    case True
    define css where "css = [es]"
    define ws where  "ws = [\<gamma>]"
    have " length css = length ws"
      unfolding css_def ws_def by simp
    moreover have "set css \<noteq> {}"
      unfolding css_def by simp
    moreover have "(\<forall> cs \<in> set css. flowcycle g cs \<and> set cs \<subseteq> support g \<and> distinct cs)"
      unfolding css_def 
      by (simp add: es_Def(1) es_Def(2) es_Def(3))
    
    moreover have "(\<forall> e \<in> \<E>. g e = 
                            (\<Sum> i < length css. ( if e \<in> set (css ! i) then ws ! i else 0)))"
       unfolding css_def ws_def 
     proof
       fix e
       assume e_Assm:"e \<in> \<E> "
       have 001: "e \<in> set es \<Longrightarrow> \<gamma> = g e"
         proof(rule ccontr)
           assume ee_assm: " e \<in> set es" "\<gamma>  \<noteq> g e "
           hence "\<gamma>  < g e" using gamma_less_Es[of e] by simp
           hence "g' e > 0" unfolding g'_def using ee_assm by simp
           hence " Abs g' > 0"
             unfolding Abs_def
             by (meson \<open>g' \<ge>\<^sub>F 0\<close> e_Assm finite_E flow_non_neg_def sum_pos2)
           then show False 
             by (simp add: True)
         qed
       have 002: "e \<notin> set es \<Longrightarrow> g e = 0"
         proof(rule ccontr)
           assume ee_assm: " e \<notin> set es" " g e  \<noteq> 0 "
           hence "g' e > 0" unfolding g'_def 
              using e_Assm less.prems(1) flow_non_neg_def by fastforce
           hence " Abs g' > 0"
             unfolding Abs_def
             by (meson \<open>g' \<ge>\<^sub>F 0\<close> e_Assm finite_E flow_non_neg_def sum_pos2)
           then show False 
             by (simp add: True)
         qed 
       have "(\<Sum>i<length [es]. if e \<in> set ([es] ! i) then [\<gamma>] ! i else 0) = 
             (\<Sum>i \<in> {0}. if e \<in> set ([es] ! i) then [\<gamma>] ! i else 0)" by auto
       also have "... = (if e \<in> set ([es] ! 0) then [\<gamma>] ! 0 else 0)" 
         by(rule sum_singleton)
       also have "... =  (if e \<in> set es then \<gamma> else 0)" by simp
       also have "... = g e"
         using 001 002 by (cases " e \<in> set es ") auto
       finally show "g e = (\<Sum>i<length [es]. if e \<in> set ([es] ! i) then [\<gamma>] ! i else 0)" 
         by simp
     qed       
    moreover have "\<forall> w \<in> set ws. w > 0" unfolding ws_def 
      by (simp add: gamma_greater_zero)
    moreover have "is_integral_flow g \<longrightarrow> (\<forall>w\<in>set ws. \<exists>n. w = real n)"
      using ws_def integral_g integral_gamma by simp
    ultimately show ?thesis by blast
  next
    case False
    hence res_abs_pos: "Abs g' > 0" 
      using \<open>0 \<le> Abs g'\<close> by auto
    moreover have res_circ_g': "is_circ g'"
      unfolding is_circ_def
    proof
      fix v
      assume v_Assm: "v \<in> \<V>"
      show "ex g' v = 0"
        unfolding ex_def
      proof(cases "\<delta>\<^sup>+ v \<inter> set es = {} \<and> \<delta>\<^sup>- v \<inter> set es = {}")
        case True
        have "sum g' (\<delta>\<^sup>- v) =  sum g (\<delta>\<^sup>- v)"
          using sum.cong[of "{e \<in> \<E>. snd e = v}" "{e \<in> \<E>. snd e = v}" g' g] True
          unfolding g'_def  
          by (auto simp add: delta_minus_def disjoint_iff)
        moreover have "sum g' (\<delta>\<^sup>+ v) =  sum g (\<delta>\<^sup>+ v)"
          using sum.cong[of "{e \<in> \<E>. snd e = v}" "{e \<in> \<E>. snd e = v}" g' g] True
          unfolding g'_def  
          by (auto simp add: delta_minus_def disjoint_iff)
        ultimately show "sum g' (\<delta>\<^sup>- v) - sum g' (\<delta>\<^sup>+ v) = 0" 
          using less.prems(3) v_Assm
          by (simp add: is_circ_def ex_def)
      next
        case False
        then obtain eov eiv where eov_def:"\<delta>\<^sup>+ v \<inter> set es = {eov}"  
                              and eiv_def: "\<delta>\<^sup>- v \<inter> set es = {eiv}"
          by (meson es_Def(4) v_Assm)
        have delt_min_split: "\<delta>\<^sup>- v = (\<delta>\<^sup>- v -{eiv}) \<union> {eiv}" 
          using eiv_def  by auto
        have delt_plus_split: "\<delta>\<^sup>+ v = (\<delta>\<^sup>+ v -{eov}) \<union> {eov}" 
          using eov_def  by auto     
        have "sum g' (\<delta>\<^sup>- v) = sum g' (\<delta>\<^sup>- v - {eiv}) + g' eiv"
          using delta_minus_finite
          by (subst delt_min_split, 
              subst sym[ OF sum_singleton[of g' eiv]],
              fastforce intro: sum.union_disjoint)
        also have "... = sum g (\<delta>\<^sup>- v - {eiv}) + (g eiv - \<gamma>) "
          unfolding g'_def
          using eiv_def 
          by (intro sum_eq_split, intro sum.cong, auto)
        finally have inflow: "sum g' (\<delta>\<^sup>- v) = sum g (\<delta>\<^sup>- v - {eiv}) + (g eiv - \<gamma>)"
          by simp
        have "sum g' (\<delta>\<^sup>+ v) = sum g' (\<delta>\<^sup>+ v - {eov}) + g' eov"
          using delta_plus_finite
          by (subst delt_plus_split, 
              subst sym[ OF sum_singleton[of g' eov]], 
              fastforce intro: sum.union_disjoint)
        also have "... = sum g (\<delta>\<^sup>+ v - {eov}) + (g eov - \<gamma>) "
            unfolding g'_def
            using eov_def 
            by (intro sum_eq_split, intro  sum.cong, auto)
        finally have 004:"sum g' (\<delta>\<^sup>+ v) = sum g (\<delta>\<^sup>+ v - {eov}) + (g eov - \<gamma>)" by simp
        hence 005: "sum g' (\<delta>\<^sup>+ v) = sum g (\<delta>\<^sup>+ v)  - \<gamma>" 
          using  delt_plus_split delta_plus_finite  
                 sum.insert_remove[of "(\<delta>\<^sup>+ v) - {eov}" g eov] 
          by simp
        have 006:"sum g (\<delta>\<^sup>- v) = sum g (\<delta>\<^sup>- v - {eiv}) + g eiv"
          using delta_minus_finite          
          by (subst delt_min_split, 
              subst sym[ OF sum_singleton[of g eiv]], 
              fastforce intro: sum.union_disjoint)
        also have "... = sum g' (\<delta>\<^sup>- v - {eiv}) + (g' eiv + \<gamma>) "
            unfolding g'_def
            using eiv_def 
            by (intro sum_eq_split, intro  sum.cong, auto)
        finally have "sum g (\<delta>\<^sup>- v) = sum g' (\<delta>\<^sup>- v - {eiv}) + (g' eiv + \<gamma>)"  by simp
        hence 007: "sum g (\<delta>\<^sup>- v) = sum g' (\<delta>\<^sup>- v) + \<gamma>" 
          using  delt_min_split delta_minus_finite
                 sum.insert_remove[of "(\<delta>\<^sup>- v) - {eiv}" g' eiv] 
          by simp
        hence "sum g' (\<delta>\<^sup>- v) - sum g' (\<delta>\<^sup>+ v) = sum g (\<delta>\<^sup>- v) - sum g (\<delta>\<^sup>+ v)" 
          using 005 by simp
        then show "sum g' (\<delta>\<^sup>- v) - sum g' (\<delta>\<^sup>+ v) = 0" 
        proof -
          have exg: "ex g v = 0"
            using less.prems(3) v_Assm by (auto simp add: is_circ_def)
          have g_bal: "sum g (\<delta>\<^sup>- v) - sum g (\<delta>\<^sup>+ v) = 0"
            using exg by (simp add: ex_def)
          have g'_in: "sum g' (\<delta>\<^sup>- v) = sum g (\<delta>\<^sup>- v) - \<gamma>"
            using 007 by simp
          have g'_out: "sum g' (\<delta>\<^sup>+ v) = sum g (\<delta>\<^sup>+ v) - \<gamma>"
            using 005 by simp
          show ?thesis
            using g_bal g'_in g'_out by linarith
        qed
      qed
    qed

    have support_incl:"support g' \<subset> support g" 
    proof
      show "support g' \<subseteq> support g"
      proof
        fix x
        assume asm: " x \<in> support g'"
        moreover have "g x \<ge> g' x" unfolding g'_def 
          using gamma_greater_zero by auto
        thus "x \<in> support g " using asm  unfolding support_def by simp
      qed
      show "support g' \<noteq> support g" 
        using  \<open>eee \<notin> support g' \<and> eee \<in> support g\<close>
        by auto
    qed 
 
    hence "card (support g') < n" 
      using \<open>finite (support g)\<close> less.prems(5) psubset_card_mono by auto

    have sup_g'_non_empt: "support g' \<noteq> {}"
      unfolding support_def
    proof(rule ccontr)
      assume set_assm: "\<not> {e |e. 0 < g' e \<and> e \<in> \<E>} \<noteq> {}"
      obtain e where "g' e > 0 \<and> e \<in> \<E>"  
        proof -
          have "\<exists> d \<in> \<E>. 0 < g' d"
          proof(rule ccontr)
            assume no_pos: "\<not> (\<exists> d \<in> \<E>. 0 < g' d)"
            have sum_le: "(\<Sum> d \<in> \<E>. g' d) \<le> 0"
            proof(rule sum_nonpos)
              fix d assume dE: "d \<in> \<E>"
              have "\<not> (0 < g' d)"
                using no_pos dE by blast
              thus "g' d \<le> 0" by linarith
            qed
            have "0 < (\<Sum> d \<in> \<E>. g' d)"
              using res_abs_pos by (simp add: Abs_def)
            thus False using sum_le by linarith
          qed
          then obtain d where d_prop: "d \<in> \<E>" "0 < g' d" by blast
          show thesis
            using that[of d] d_prop by blast
        qed
      then show False using set_assm by auto
    qed

    then obtain css ws  where  css_wss_def:
       "length css = length ws"
       "set css \<noteq> {}" "\<forall> w \<in> set ws. w > 0"
       "(\<forall>cs\<in>set css. flowcycle g' cs \<and> set cs \<subseteq> support g' \<and> distinct cs)"
       "(\<forall>e\<in>\<E>. g' e = (\<Sum>i<length css. if e \<in> set (css ! i) then ws ! i else 0))"
       "(is_integral_flow g' \<longrightarrow> (\<forall> w \<in> set ws. \<exists> n::nat. w = real n))"
      using  g'_non_neg  res_circ_g' res_abs_pos sup_g'_non_empt 
          less(1)[of "card (support g')" g']  \<open>card (support g') < n\<close> by blast
    have "length (es#css) = length (\<gamma>#ws)" using  css_wss_def by simp
    moreover have "set (es#css) \<noteq> {}" by simp
    moreover have "(\<forall>cs\<in>set (es#css). flowcycle g cs \<and> set cs \<subseteq> support g \<and> distinct cs)" 
    proof
      fix cs
      assume asm: "cs \<in> set (es # css)"
      have "flowcycle g cs" 
        using asm es_Def css_wss_def(4) g'_def g_greater_g' flow_cyc_mono
        by auto
      moreover have "set cs \<subseteq> support g"
        using asm css_wss_def(4) es_Def(2) support_incl 
        by auto
      moreover have "distinct cs" 
        using asm css_wss_def(4) es_Def(3) 
        by auto
      ultimately show  "flowcycle g cs \<and> set cs \<subseteq> support g \<and> distinct cs" by simp
    qed
    moreover have "(\<forall>e\<in>\<E>. g e = (\<Sum>i<length (es#css). if e \<in> set ((es#css) ! i) 
                                                        then (\<gamma>#ws) ! i else 0))"
    proof
      fix e
      assume "e \<in> \<E> "
      have aa:"g e  = g' e + (if e \<in> set es then \<gamma> else 0)" unfolding g'_def by simp
      also have "... =  (\<Sum>i<length css. if e \<in> set (css ! i) then ws ! i else 0) +
                         (if e \<in> set es then \<gamma> else 0)" 
        using \<open>e \<in> \<E>\<close> css_wss_def(5) by auto
      also have ac:"... =  (\<Sum>i\<in>{0..<length (css)}. if e \<in> set ((es # css) ! (i+1)) 
                                              then (\<gamma> # ws) ! (i+1) else 0) +
                        (if e \<in> set es then \<gamma> else 0)" 
        by(rule sum_eq_split,
           smt (verit, del_insts) add_diff_cancel_right' add_is_0 gr_zeroI lessThan_atLeast0 
               nth_Cons_pos sum.cong zero_neq_one) simp
      also have ae:"... =  (\<Sum>i\<in>{x + 1 |x. x \<in> {0..<length css}}. if e \<in> set ((es # css) ! (i)) 
                                              then (\<gamma> # ws) ! (i) else 0) +
                        (if e \<in> set es then \<gamma> else 0)" 
        by(rule sum_eq_split, rule sym[OF sum_index_shift[of "{0..<length css}" ]]) simp+
      also have "... =  (\<Sum>i\<in>{x |x. x > 0 \<and> x <length (es# css)}. if e \<in> set ((es # css) ! (i)) 
                                              then (\<gamma> # ws) ! (i) else 0) +
                        (if e \<in> set es then \<gamma> else 0)" 
        apply(rule sum_eq_split, rule sum.cong)
        defer
        by (simp, rule, rule, force, rule,
             smt (verit) Suc_eq_plus1 Suc_length_conv Suc_pred lessThan_atLeast0 lessThan_iff 
            less_Suc_eq less_imp_diff_less mem_Collect_eq)  
      also have "... = (\<Sum>i\<in>{i| i. i> 0 \<and> i <length (es#css)}. if e \<in> set ((es # css) ! (i))
                                              then (\<gamma> # ws) ! (i) else 0) +
                       (\<Sum>i\<in>{0}. if e \<in> set ((es # css) ! (i))
                                              then (\<gamma> # ws) ! (i) else 0)"  by simp
      also have "... = (\<Sum>i\<in> {0} \<union> {i| i. i> 0 \<and> i <length (es#css)}.
                                              if e \<in> set ((es # css) ! i)
                                              then (\<gamma> # ws) ! i else 0)"  
        using sym[OF sum.union_disjoint[of "{i |i. 0 < i \<and> i < length (es # css)}" "{0}"]]
        by simp 
      also have  "...= (\<Sum>i<length (es # css).
                                  if e \<in> set ((es # css) ! i) then (\<gamma> # ws) ! i else 0)"
        by(fastforce intro!: sum.cong)
      finally show "g e = (\<Sum>i<length (es # css). 
                          if e \<in> set ((es # css) ! i) then (\<gamma> # ws) ! i else 0)"
         by simp
     qed  
    moreover have "\<forall> w \<in> set (\<gamma>#ws). w > 0" 
      using css_wss_def(3) gamma_greater_zero by fastforce
    moreover have "(is_integral_flow g \<longrightarrow> (\<forall> w \<in> set (\<gamma> # ws). \<exists> n::nat. w = real n))"
      using css_wss_def(6) integral_g
      by (simp add: integral_gamma)
    ultimately show ?thesis by blast
  qed
qed

end
end