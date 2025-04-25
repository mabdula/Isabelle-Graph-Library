theory Greedoids_Example
  imports Greedoids 
begin

section \<open>Greedoid Example\<close>

locale greedoid_example  =
  fixes V :: "'a set"         (* Set of vertices *)
    and E :: "('a set) set"  (* Set of directed edges *) 
  assumes finite_assum_V: "finite V"

context greedoid_example
begin

definition undirected_graph::"'a set \<Rightarrow> ('a set) set \<Rightarrow> bool" where
 "undirected_graph F G \<longleftrightarrow> F \<subseteq> V \<and> (\<forall>e \<in> G. card e = 2 \<and> e \<subseteq> F)"

definition acyclic::"'a set \<Rightarrow> ('a set) set \<Rightarrow> bool" where
 "acyclic F G = ((G = {}) \<or> (\<forall>v \<in> F. \<not> (\<exists>p. p \<noteq> [] \<and> hd p = v \<and> last p = v
                                               \<and> (\<forall>i < length p - 1. {p ! i, p ! (i + 1)} \<in> G) 
                                                  \<and> length p \<ge> 4 \<and> distinct (butlast p))))"

definition connected::"'a set \<Rightarrow>  ('a set) set \<Rightarrow> bool" where 
"connected F G = ((G = {} \<and> card F = 1) \<or> (\<forall>u v. u \<in> F \<and> v \<in> F \<and> u \<noteq> v \<longrightarrow> (\<exists>p. p \<noteq> [] \<and> (hd p = v \<and>
                           last p = u) \<and> (\<forall>i < length p - 1. {p ! i, p ! (i + 1)} \<in> G) \<and> length p \<ge> 2)))"

definition tree::"'a set \<Rightarrow> ('a set) set \<Rightarrow> bool" where 
"tree F G \<longleftrightarrow> undirected_graph F G \<and> acyclic F G \<and> connected F G \<and> (card G = card F - 1) "

lemma empty_in: 
  assumes "undirected_graph V E" "r \<in> V"
  shows "{} \<in> {Y. \<exists> X. X \<subseteq> V \<and> Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}"
  proof -
    have factone: "{r} \<subseteq> V" using assms(2) by simp
    have "tree {r} {}" unfolding tree_def
    proof 
      show "undirected_graph {r} {}" unfolding undirected_graph_def using assms by auto
      have 1: "acyclic {r} {}" unfolding acyclic_def by simp
        have 2: "connected {r} {}" unfolding connected_def by simp
        have 3: "card {} = card {} - 1" by simp
        then show "local.acyclic {r} {} \<and> local.connected {r} {} \<and> card {} = card {r} - 1" using 1 2 by simp
      qed
      then have "{r} \<subseteq> V \<and> {} \<subseteq> E \<and> r \<in> {r} \<and> tree {r} {}" using factone by simp
      then show ?thesis by blast
 qed

lemma defines_set_system:
  assumes "undirected_graph V E" "r \<in> V" 
  shows "set_system E {Y. \<exists> X. X \<subseteq> V \<and> Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}" 
  unfolding set_system_def
    proof 
      show "finite E" 
      proof -
        have "\<forall>e \<in> E. e \<subseteq> V" using assms(1) unfolding undirected_graph_def by simp
        then show "finite E" using finite_assum_V 
          by (meson Sup_le_iff finite_UnionD rev_finite_subset)
      qed
      show "\<forall>Z\<in>{Y. \<exists> X. X \<subseteq> V \<and> Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}. Z \<subseteq> E" by auto
    qed


lemma extension_property: 
  assumes "undirected_graph V E" "r \<in> V" 
          "X \<in> {Y. \<exists> X. X \<subseteq> V \<and> Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}"
          "Y \<in> {Y. \<exists> X. X \<subseteq> V \<and> Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}" "card Y < card X"
    shows "\<exists>x\<in>X - Y. Y \<union> {x} \<in> {Y. \<exists> X. X \<subseteq> V \<and> Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}"
proof-
  let ?F = "{Y. \<exists> X. X \<subseteq> V \<and> Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}"
  have "X \<in> ?F \<and>
           Y \<in> ?F \<and> card Y < card X \<Longrightarrow>
           \<exists>x\<in>X - Y. Y \<union> {x} \<in> ?F"
    proof -
      fix X Y
      assume assum2: "X \<in> ?F \<and>
           Y \<in> ?F \<and> card Y < card X"
      then obtain V1 where V1_prop: "V1 \<subseteq> V \<and>  X \<subseteq> E \<and> r \<in> V1 \<and> tree V1 X" by auto
      then have "tree V1 X" by simp
      then have V1_card: "card V1 - 1 = card X" unfolding tree_def by auto
      have "V1 \<noteq> {}" using V1_prop by auto
      have "finite V1" using V1_prop finite_assum_V finite_subset by auto
      then have "card V1 > 0" using \<open>V1 \<noteq> {}\<close> by auto
      then have factone: "card V1 = card X + 1" using V1_card by auto 
      obtain V2 where V2_prop: "V2 \<subseteq> V \<and>  Y \<subseteq> E \<and> r \<in> V2 \<and> tree V2 Y" using assum2 by auto
      then have "tree V2 Y" by simp
      then have V2_card: "card V2 - 1 = card Y" unfolding tree_def by auto  
      have "V2 \<noteq> {}" using V2_prop by auto
      have "finite V2" using V2_prop finite_assum_V finite_subset by auto
      then have "card V2 > 0" using \<open>V2 \<noteq> {}\<close> by auto
      then have facttwo: "card V2 = (card Y) + 1" using V2_card by auto
      have "card Y < card X" using assum2 by simp
      then have "card Y + 1 < card X + 1" by simp
      then have "card V2 < card V1" using factone facttwo by simp
      have "X = (X - Y) \<union> (X \<inter> Y)" by auto
      show "\<exists>x\<in>X - Y. Y \<union> {x} \<in> ?F"
      proof -
        have "V1 \<noteq> {}" using V1_prop by auto
          then have "V1 \<noteq> V2" using \<open>card V2 < card V1\<close> by auto
          then have "V1 - V2 \<noteq> {}" 
            by (metis \<open>card V2 < card V1\<close> \<open>finite V1\<close> \<open>finite V2\<close> bot.extremum_strict bot_nat_def card.empty card_less_sym_Diff)
          then obtain x where "x \<in> V1 - V2" by auto
          then have "x \<notin> V2" by simp
          have "x \<in> V1" using \<open>x \<in> V1 - V2\<close> by simp
          have "r \<in> V2" using V2_prop by simp
          then have "x \<noteq> r" using \<open>x \<notin> V2\<close> by auto
          have "X \<noteq> {}" 
            using \<open>card Y < card X\<close> card.empty by auto
          have "r \<in> V1" using V1_prop by simp
          have "tree V1 X" using V1_prop by simp
          then have "connected V1 X" unfolding tree_def by simp
          then have "(X = {} \<and> card V1 = 1) \<or> (\<forall>u v. u \<in> V1 \<and> v \<in> V1 \<and> u \<noteq> v \<longrightarrow> (\<exists>p. p \<noteq> [] \<and> (hd p = u \<and> last p = v ) \<and> (\<forall>i < length p - 1. ({p ! i, p ! (i + 1)} \<in> X)) \<and> length p \<ge> 2))" unfolding
              connected_def by auto
          then have "(\<forall>u v. u \<in> V1 \<and> v \<in> V1 \<and> u \<noteq> v \<longrightarrow> (\<exists>p. p \<noteq> [] \<and> (hd p = u \<and> last p = v) \<and> (\<forall>i < length p - 1. ({p ! i, p ! (i + 1)} \<in> X)) \<and> length p \<ge> 2))" using \<open>X \<noteq> {}\<close> by simp
          then have "(\<exists>p. p \<noteq> [] \<and> (hd p = r \<and> last p = x) \<and> (\<forall>i < length p - 1. ({p ! i, p ! (i + 1)} \<in> X)) \<and> length p \<ge> 2)" using \<open>r \<in> V1\<close> \<open>x \<in> V1\<close> \<open>x \<noteq> r\<close> \<open>X \<noteq> {}\<close> by simp
          then obtain p where p_prop: "(p \<noteq> [] \<and> (hd p = r \<and> last p = x) \<and> (\<forall>i < length p - 1. ({p ! i, p ! (i + 1)} \<in> X)) \<and> length p \<ge> 2)" by auto
          have "\<exists>v' w. v' \<in> V1 \<inter> V2 \<and> w \<in> V1 - V2 \<and> {v', w} \<in> X" 
          proof -
           have "last p = x" using p_prop by auto
          have "hd p = r" using p_prop by simp
          have "length p \<ge> 2" using p_prop by simp
          have p_prop2: "(\<forall>i < length p - 1. ({p ! i, p ! (i + 1)} \<in> X))" using p_prop by simp
          have "undirected_graph V1 X" using \<open>tree V1 X\<close> unfolding tree_def by simp
          then have X_prop1: "V1 \<subseteq> V \<and> (\<forall>e \<in> X. e \<subseteq> V1 \<and> card e = 2)" unfolding undirected_graph_def by simp
          have p_prop3: "\<forall>i \<le> length p - 1. (nth p i) \<in> V1" 
          proof (rule allI)
            fix i
            show "i \<le> length p - 1 \<longrightarrow> p ! i \<in> V1"
            proof (cases "i = length p - 1")
              case True
              then have "i \<noteq> 0" using \<open>length p \<ge> 2\<close> by simp
              then have "i - 1 = length p - 1 - 1" using True by simp
              then have "i = (i - 1) + 1" using \<open>i \<noteq> 0\<close> by simp
              then have "i - 1 < length p - 1" using \<open>length p \<ge> 2\<close> \<open>i - 1 = length p - 1 - 1\<close> by simp
              then have "{nth p (i - 1), (nth p i)} \<in> X" using p_prop \<open>i = (i - 1) + 1\<close> by auto
              then have "{nth p (i - 1), (nth p i)} \<subseteq> V1" using X_prop1 by auto
              then show ?thesis using True by auto
            next
              case False
              show "i \<le> length p - 1 \<longrightarrow> (nth p i) \<in> V1"
              proof
                assume "i \<le> length p - 1"
                then have "i < length p - 1" using \<open>length p \<ge> 2\<close> False by simp
                then have "{nth p i, (nth p (i + 1))} \<in> X " using p_prop by simp
                then have "{nth p i, (nth p (i + 1))} \<subseteq> V1" using X_prop1 by auto
                then show "(nth p i) \<in> V1" by simp
            qed
          qed
        qed
          have "V1 = (V1 \<inter> V2) \<union> (V1 - V2)" by auto
          then have V1_el_prop: "\<forall>v. v \<in> V1 \<longrightarrow> v \<in> (V1 - V2) \<or> v \<in> (V1 \<inter> V2)" by auto
          have "\<exists>i. i \<le> (length p) - 1 \<and> (nth p (i )) \<in> V1 - V2 \<and> (nth p (i - 1)) \<in> V1 \<inter> V2"
          proof (cases "\<forall>i < (length p) - 1. (nth p i) \<in> V1 \<inter> V2")
            case True
            have "((length p) - 1) - 1 < (length p) - 1" using \<open>length p \<ge> 2\<close> by simp 
            then have prop1: "(nth p ((length p) - 1 - 1)) \<in> V1 \<inter> V2" using True by simp
            have "(nth p (length p - 1)) = x" using \<open>last p = x\<close> 
              by (metis last_conv_nth p_prop)
            then have "(nth p (length p - 1)) \<in> V1 - V2" using \<open>x \<in> V1 - V2\<close> by simp
            then show ?thesis using prop1  \<open>length p - 1 - 1 < length p - 1\<close>  by auto
          next
            case False
            then have "\<exists>i < (length p) - 1. (nth p i) \<notin> V1 \<inter> V2" by auto
            then obtain i where i_prop: "i < (length p) - 1 \<and> (nth p i) \<notin> V1 \<inter> V2" by auto
            then have i_prop2: "(nth p i) \<notin> V1 \<inter> V2" by simp
            then have "i < length p - 1" using i_prop by simp
            then have "(nth p i) \<in> V1 - V2" using V1_el_prop i_prop2 p_prop3 by simp
            let ?A = "{j. j < length p - 1 \<and> (nth p j) \<in> V1 - V2}" 
            have "finite ?A" by simp
            have "i \<in> ?A" using \<open>i < length p - 1\<close> \<open>(nth p i) \<in> V1 - V2\<close> by simp
            then have "?A \<noteq> {}" by auto
            then have "Min ?A \<in> ?A" using \<open>finite ?A\<close> Min_in by blast
            let ?k = "Min ?A"
            have min_prop: "\<forall>j. j\<in> ?A \<longrightarrow> ?k \<le> j" by simp
            have k_prop: "?k < length p - 1 \<and> (nth p ?k) \<in> V1 - V2" using \<open>?k \<in> ?A\<close> by simp
            have "(nth p 0) = r" using p_prop hd_conv_nth by metis
            then have "(nth p 0) \<in> V1 \<inter> V2" using V1_prop V2_prop by simp
            have "(nth p ?k) \<in> V1 - V2" using k_prop by simp
            then have "?k \<noteq> 0" using \<open>(nth p 0) \<in> V1 \<inter> V2\<close> 
              by (metis DiffD2 \<open>p ! 0 = r\<close> \<open>r \<in> V2\<close>)
            then have "?k - 1 < ?k" by simp
            have "?k - 1 < length p - 1" using k_prop by auto
            have k_prop4: "(nth p (?k - 1)) \<in> V1 \<inter> V2"
            proof (rule ccontr)
              assume "(nth p (?k - 1)) \<notin> V1 \<inter> V2"
              then have "(nth p (?k - 1)) \<in> V1 - V2" using p_prop3 V1_el_prop i_prop2 \<open>?k - 1 < length p -1 \<close> by simp
              then have "?k - 1 < length p - 1" using \<open>?k - 1 < ?k\<close> k_prop by simp
              then have "?k - 1 \<in> ?A" using \<open>(nth p (?k - 1)) \<in> V1 - V2\<close> by simp
              then show "False" using min_prop \<open>?k - 1 < ?k\<close> 
                using less_le_not_le by blast
            qed
            then have k_prop3: "?k \<le> length p - 1 \<and> (nth p ?k) \<in> V1 - V2" using k_prop by simp
            then show ?thesis using k_prop4 by auto
          qed
          then obtain i where i_prop: "i \<le> (length p) - 1 \<and> (nth p i) \<in> V1 - V2 \<and> (nth p (i - 1)) \<in> V1 \<inter> V2" by auto
          then have "i - 1 < length p - 1" using p_prop by auto
          have "nth p 0 = r" using hd_conv_nth p_prop by metis
          then have "nth p 0 \<in> V1 \<inter> V2" using V1_prop V2_prop by simp
          have "i \<noteq> 0" 
          proof
            assume "i = 0"
            then have "nth p 0 \<in> V1 - V2" using i_prop by simp
            then show "False" using \<open>nth p 0 \<in> V1 \<inter> V2\<close> by simp
          qed
          then have "i - 1 + 1 = i" by simp
          then have factone: "{nth p (i - 1), nth p i} \<in> X" using p_prop \<open>i - 1 < length p - 1\<close> by auto
          have "i - 1 < length p" using \<open>i - 1 < length p - 1\<close> by simp 
          then show ?thesis using i_prop factone by auto
        qed
          then obtain v' w where v'_w_prop: "v' \<in> V1 \<inter> V2 \<and> w \<in> V1 - V2 \<and> ({v', w} \<in> X)" by auto
          let ?v = "v'"
          let ?w = "w"
          have "?v \<in> V1 \<inter> V2" using v'_w_prop by simp
          have "?w \<in> V1 - V2" using v'_w_prop by simp
          show "\<exists>x\<in>X - Y. Y \<union> {x} \<in> {Y. \<exists>X\<subseteq>V. Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}"
          proof -
            have "{?v, ?w} \<in> X" using v'_w_prop by simp
          have "tree V2 Y" using V2_prop by simp
          then have "undirected_graph V2 Y" unfolding tree_def by simp
          then have Y_prop: "V2 \<subseteq> V \<and> (\<forall>e \<in> Y. e \<subseteq> V2 \<and> card e = 2)" unfolding undirected_graph_def by simp
          have "\<not> {?v, ?w} \<subseteq> V2" using \<open>?w \<in> V1 - V2\<close> by simp
          then have "{?v, ?w} \<notin> Y" using Y_prop by auto
          then have "{?v, ?w} \<in> X - Y" using \<open>{?v, ?w} \<in> X\<close> by simp
          have "connected V2 Y" using \<open>tree V2 Y\<close> unfolding tree_def by simp
          then have Y_connected: "(Y = {} \<and> card V2 = 1) \<or>(\<forall>u v. u \<in> V2 \<and> v \<in> V2 \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y) \<and>
           2 \<le> length p))" 
            unfolding connected_def by simp
          have "undirected_graph V1 X" using \<open>tree V1 X\<close> unfolding tree_def by simp
          then have X_prop1: "V1 \<subseteq> V \<and> (\<forall>e \<in> X. e \<subseteq> V1 \<and> card e = 2)" unfolding undirected_graph_def by simp
          have "acyclic V2 Y" using \<open>tree V2 Y\<close> unfolding tree_def by auto
          then have Y_acyclic: "(Y = {}) \<or> (\<forall>v. v \<in> V2 \<longrightarrow> \<not>(\<exists>p. p \<noteq> [] \<and> hd p = v \<and> last p = v \<and> (\<forall>i < length p - 1. {nth p i, nth p (i + 1)} \<in> Y) \<and> length p \<ge> 4 \<and> distinct (butlast p)))"  unfolding acyclic_def by auto
          have w_el_prop: "(\<nexists>x. x \<in> V2 \<union> {?w} \<and> {x, ?w} \<in> Y \<union> {{?v, ?w}} \<and> x \<noteq> ?v)"
          proof 
            assume "\<exists>x. x \<in> V2 \<union> {w} \<and> {x, w} \<in> Y \<union> {{v', w}} \<and> x \<noteq> v'"
            then obtain y where y_prop: "y \<in> V2 \<union> {w} \<and> {y, w} \<in> Y \<union> {{v', w}} \<and> y \<noteq> v'" by auto
            then have "{y, ?w} \<in> Y \<union> {{?v, ?w}}" by simp
            then have "{y, ?w} \<in> Y" using y_prop by fast
            then have "{y, ?w} \<subseteq> V2" using Y_prop by auto
            then have "?w \<in> V2" by simp
            then show False using \<open>?w \<in> V1 - V2\<close> by simp
          qed
          
          have "undirected_graph (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})"  unfolding undirected_graph_def
          proof
            show "V2 \<union> {?w} \<subseteq> V" using Y_prop \<open>?w \<in> V1 - V2\<close> X_prop1 by auto
            show "\<forall>e\<in>Y \<union> {{?v, ?w}}. card e = 2 \<and> e \<subseteq> V2 \<union> {?w}"
            proof 
              fix e
              show "e \<in> Y \<union> {{?v, ?w}} \<Longrightarrow> card e = 2 \<and> e \<subseteq> V2 \<union> {?w}"
              proof -
                assume "e \<in> Y \<union> {{?v, ?w}}"
                then show "card e = 2 \<and> e \<subseteq> V2 \<union> {?w}"
                proof (cases "e = {?v, ?w}")
                  case True
                  then have "{?v, ?w} \<subseteq> V2 \<union> {?w}" using \<open>?v \<in> V1 \<inter> V2\<close> by auto
                  then show ?thesis using True 
                    by (simp add: X_prop1 \<open>{v', w} \<in> X\<close>)
                next
                  case False
                  then have "e \<in> Y" using \<open>{?v, ?w} \<notin> Y\<close> \<open>e \<in> Y \<union> {{?v, ?w}}\<close> by simp
                  then show ?thesis using Y_prop by auto
                qed
              qed
            qed
          qed
          have "acyclic (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})" unfolding acyclic_def
          proof -
            have "Y \<union> {{?v, ?w}} \<noteq> {}" by simp
            have "(\<forall>v\<in>V2 \<union> {w}.
        \<nexists>p. p \<noteq> [] \<and>
            hd p = v \<and>
            last p = v \<and>
            (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
            4 \<le> length p \<and> distinct (butlast p))"
            proof 
              fix u
              show "u \<in> V2 \<union> {w} \<Longrightarrow>
         \<nexists>p. p \<noteq> [] \<and>
             hd p = u \<and>
             last p = u \<and>
             (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
             4 \<le> length p \<and> distinct (butlast p)"
              proof -
                assume "u \<in> V2 \<union> {?w}" 
                show "\<nexists>p. p \<noteq> [] \<and>
             hd p = u \<and>
             last p = u \<and>
             (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
             4 \<le> length p \<and> distinct (butlast p)"
                proof (cases "u = ?w")
                  case True
                  show ?thesis
                  proof 
                    assume "\<exists>p. p \<noteq> [] \<and>
        hd p = u \<and>
        last p = u \<and>
        (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
        4 \<le> length p \<and> distinct (butlast p)"
                    then obtain pa where pa_prop: "pa \<noteq> [] \<and>
        hd pa = u \<and>
        last pa = u \<and>
        (\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
        4 \<le> length pa \<and> distinct (butlast pa)" by auto
                    then have "{(nth pa 0), (nth pa 1)} \<in> Y \<union> {{?v, ?w}}" by simp
                    then have "{(nth pa 0), nth pa 1} \<subseteq> V2 \<union> {?w}" using \<open>undirected_graph (V2 \<union> {?w}) ( Y \<union> {{?v, ?w}})\<close>
                      unfolding undirected_graph_def by auto
                    have "(nth pa 0) = ?w" using True hd_conv_nth pa_prop by fastforce
                    have 1: "(nth pa 1) = ?v"
                    proof (rule ccontr)
                      assume "nth pa 1 \<noteq> ?v"
                      then have "nth pa 1 \<noteq> ?w" using \<open>nth pa 0 = ?w\<close> p_prop 
                        by (metis Int_iff UnE Y_prop \<open>\<not> {v', w} \<subseteq> V2\<close> \<open>v' \<in> V1 \<inter> V2\<close> \<open>{pa ! 0, pa ! 1} \<in> Y \<union> {{v', w}}\<close> insert_subset singleton_iff singleton_insert_inj_eq)
                      then have "{nth pa 0, nth pa 1} \<in> Y \<union> {{?v, ?w}}" using pa_prop by simp
                      then show False using \<open>nth pa 1 \<noteq> ?v\<close> \<open>nth pa 0 = ?w\<close> w_el_prop 
                        by (metis \<open>{pa ! 0, pa ! 1} \<subseteq> V2 \<union> {w}\<close> insert_commute insert_subset)
                    qed
                    have "(nth pa (length pa - 1)) = ?w" using last_conv_nth pa_prop True  by fastforce
                    moreover have "length pa - 1 - 1 < length pa - 1" using pa_prop by auto
                    moreover have "length pa - 1 - 1 + 1 = length pa - 1" using pa_prop by auto
                    ultimately have facttwo: "{nth pa (length pa - 1 - 1), nth pa (length pa - 1)} \<in> Y \<union> {{?v, ?w}}" using pa_prop by fastforce
                    then have "{nth pa (length pa - 1 - 1), ?w} \<in> Y \<union> {{?v, ?w}}" using \<open>nth pa (length pa - 1) = ?w\<close> by simp
                    then have "{nth pa (length pa - 1 - 1), ?w} \<subseteq> V2 \<union> {?w}" using \<open>undirected_graph (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})\<close> unfolding undirected_graph_def by auto
                    have 2: "nth pa (length pa - 1 - 1) = ?v"
                    proof (rule ccontr)
                      assume "nth pa (length pa - 1 - 1) \<noteq> ?v"
                      then have "nth pa (length pa - 1 - 1) \<noteq> ?w" using \<open>nth pa (length pa - 1) = ?w\<close> p_prop 
                        by (metis Int_iff UnE Y_prop \<open>\<not> {v', w} \<subseteq> V2\<close> \<open>v' \<in> V1 \<inter> V2\<close> \<open>{pa ! (length pa - 1 -1 ), pa ! (length pa - 1)} \<in> Y \<union> {{v', w}}\<close> insert_subset singleton_iff singleton_insert_inj_eq)
                      then show False using \<open>nth pa (length pa - 1 - 1) \<noteq> ?v\<close> \<open>nth pa (length pa - 1) = ?w\<close> w_el_prop 
                        using \<open>{pa ! (length pa - 1 - 1), w} \<in> Y \<union> {{v', w}}\<close> \<open>{pa ! (length pa - 1 - 1), w} \<subseteq> V2 \<union> {w}\<close> by blast
                    qed
                    have "distinct (butlast pa)" using pa_prop by simp
                    show False
                    proof -
                      have "1 < length (butlast pa)" using pa_prop by auto
                      moreover have "(length pa - 1 - 1) < length (butlast pa)" using pa_prop by auto
                      moreover have "1 \<noteq> length pa - 1 - 1" using pa_prop by auto
                      ultimately have "nth pa (length pa - 1 - 1) \<noteq> (nth pa 1)" using pa_prop  
                        by (metis \<open>distinct (butlast pa)\<close> nth_butlast nth_eq_iff_index_eq)
                      then show False using 1 2 by simp
                    qed
                  qed
                next
                  case False
                  then have "u \<in> V2" using \<open>u \<in> V2 \<union> {?w}\<close> \<open>?w \<in> V1 - V2\<close> by simp
                  show ?thesis
                  proof
                    assume " \<exists>p. p \<noteq> [] \<and>
        hd p = u \<and>
        last p = u \<and>
        (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
        4 \<le> length p \<and> distinct (butlast p)"
                    then obtain pa where pa_prop: " pa \<noteq> [] \<and>
        hd pa = u \<and>
        last pa = u \<and>
        (\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
        4 \<le> length pa \<and> distinct (butlast pa)" by auto
                    then show False
                    proof (cases "u = ?v")
                      case True
                      then show ?thesis 
                      proof (cases "List.member pa ?w")
                        case True
                        then have "?w \<in> set pa" using in_set_member pa_prop by force
                        then obtain ia where ia_prop: "nth pa ia = ?w" "ia \<ge> 0 \<and> ia < length pa" using in_set_conv_nth 
                          by (metis bot_nat_0.extremum)
                        have "ia \<noteq> 0"
                        proof
                          assume "ia = 0"
                          then have "nth pa 0 = ?w" using ia_prop by simp
                          then have "hd pa = ?w" using hd_conv_nth pa_prop by fast
                          then show False using pa_prop \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by simp
                        qed
                        have "ia \<noteq> length pa - 1"
                        proof
                          assume "ia = length pa - 1"
                          then have "nth pa (length pa - 1) = ?w" using ia_prop by simp
                          then have "last pa = ?w" using last_conv_nth pa_prop by fast
                          then show False using pa_prop \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by simp
                        qed
                        show ?thesis 
                        proof (cases "ia = length pa - 1 - 1")
                          case True
                          have "length pa - 1 - 1 - 1 + 1 = length pa - 1 - 1" using pa_prop by auto
                          moreover have "length pa - 1 - 1 - 1 < length pa - 1" using pa_prop by auto
                          ultimately  have fact1: "{nth pa (length pa - 1 - 1 - 1), nth pa (length pa - 1 - 1 - 1 + 1)} \<in> Y\<union> {{?v, ?w}}" using pa_prop 
                            by blast
                          then have "{nth pa (length pa - 1 - 1 - 1), nth pa (length pa - 1 - 1)} \<subseteq> V2 \<union> {?w}" using \<open>undirected_graph (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})\<close>
                            unfolding undirected_graph_def 
                            by (metis \<open>length pa - 1 - 1 - 1 + 1 = length pa - 1 - 1\<close>)
                          then have fact3: "{nth pa (length pa - 1 - 1 - 1), ?w} \<subseteq> V2 \<union> {?w}" using fact1 ia_prop True \<open>length pa - 1 -1 - 1 + 1 = length pa - 1 - 1\<close> by simp 
                          have fact2: "{nth pa (length pa - 1 - 1 - 1), ?w} \<in> Y \<union> {{?v, ?w}}" using fact1 True ia_prop \<open>length pa - 1 -1 - 1 + 1 = length pa - 1 - 1\<close> by simp 
                          have "nth pa (length pa - 1 - 1 - 1) = ?v"
                          proof (rule ccontr)
                            assume "nth pa (length pa - 1 - 1 - 1) \<noteq> ?v"
                            have "nth pa (length pa - 1 - 1 - 1) \<in> V2 \<union> {?w}" using fact3 by simp
                            have "nth pa (length pa - 1 - 1 - 1) \<noteq> ?w" 
                            proof
                              assume "nth pa (length pa - 1 - 1 - 1) = ?w"
                              have "length pa - 1 - 1 - 1 < length (butlast pa)" using pa_prop by auto
                              moreover have "length pa - 1 - 1 < length (butlast pa)" using pa_prop by auto
                              moreover have "nth pa (length pa - 1- 1 - 1) = nth pa (length pa - 1 - 1)" using ia_prop \<open>nth pa (length pa - 1 - 1 -1) = ?w\<close> True by simp
                              ultimately show False using pa_prop 
                                by (meson \<open>pa ! (length pa - 1 - 1 - 1) \<noteq> v'\<close> fact2 fact3 insert_subset w_el_prop) 
                            qed
                            then show False using fact2 w_el_prop \<open>nth pa (length pa - 1 - 1 -1) \<in> V2 \<union> {?w}\<close> \<open>nth pa (length pa - 1 - 1 - 1) \<noteq> ?v\<close> by auto
                          qed
                          moreover have "nth pa 0 = ?v" using \<open>u = ?v\<close> pa_prop hd_conv_nth by fastforce
                          moreover have "0 < length (butlast pa)" using pa_prop by simp
                          moreover have "(length pa - 1 - 1 - 1) < length (butlast pa)" using pa_prop by auto
                          ultimately show False using pa_prop  nth_butlast nth_eq_iff_index_eq 
                            by (smt (verit) add_diff_inverse_nat add_le_cancel_right add_le_same_cancel2 diff_diff_cancel diff_is_0_eq' le_numeral_extra(4) length_butlast less_iff_succ_less_eq linordered_nonzero_semiring_class.zero_le_one nat_1_add_1 nat_diff_split_asm not_one_le_zero numeral_Bit0 ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
                        next
                          case False
                          have "ia \<noteq> length pa - 1" 
                          proof 
                            assume "ia = length pa - 1"
                            then have "nth pa (length pa - 1) = ?w" using ia_prop by simp
                            then have "last pa = ?w" using last_conv_nth pa_prop by blast
                            then show False using pa_prop \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by simp
                          qed
                          then have "ia < length pa - 1 - 1" using False ia_prop by simp
                          moreover have "length pa - 1 - 1 < length pa - 1 " using pa_prop by auto
                          ultimately have "ia < length pa - 1" by simp
                          have "ia + 1 < length pa - 1 " using \<open>ia < length pa - 1 - 1\<close> by simp
                          have "{nth pa (ia), nth pa (ia + 1)} \<in> Y \<union> {{?v, ?w}}" using pa_prop \<open>ia < length pa - 1\<close> by simp
                          then have "{?w, nth pa (ia + 1)} \<in> Y \<union> {{?v, ?w}}" using ia_prop by simp
                          then have "{?w, nth pa (ia + 1)} \<subseteq> V2 \<union> {?w}" using \<open>undirected_graph (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})\<close> unfolding undirected_graph_def by auto
                          have "nth pa (ia + 1) = ?v"
                          proof (rule ccontr)
                            assume "nth pa (ia + 1) \<noteq> ?v"
                            have "nth pa (ia + 1) \<noteq> ?w" 
                            proof
                              assume "nth pa (ia + 1) = ?w"
                              then have "{?w, ?w} \<in> Y \<union> {{?v, ?w}}" using \<open>{?w, nth pa (ia + 1)} \<in> Y \<union> {{?v, ?w}}\<close> by simp
                              moreover have "?v \<noteq> ?w" using \<open>?v \<in> V1 \<inter> V2\<close> \<open>?w \<in> V1 - V2\<close> by auto
                              moreover have "?w \<in> V2 \<union> {?w}" by simp
                              ultimately show False using w_el_prop by auto
                            qed
                            have "nth pa (ia + 1) \<in> V2 \<union> {?w}" using \<open>{?w, nth pa (ia+ 1)} \<subseteq> V2 \<union> {?w}\<close> by simp
                            then show False using \<open>nth pa (ia + 1) \<noteq> ?v\<close> \<open>{?w, nth pa (ia+ 1)} \<in> Y \<union> {{?v, ?w}}\<close> w_el_prop 
                              by (metis insert_commute) 
                          qed
                          have "nth pa 0 = ?v" using \<open>u = ?v\<close> pa_prop hd_conv_nth by fastforce
                          have "(ia + 1) < length (butlast pa)" using \<open>ia + 1 < length pa - 1\<close> by simp
                          moreover have "0 < length (butlast pa)" using pa_prop by simp
                          moreover have "nth pa 0 = nth pa (ia + 1)" using \<open>nth pa 0 = ?v\<close> \<open>nth pa (ia + 1) = ?v\<close> by simp
                          ultimately show False using pa_prop nth_butlast  nth_eq_iff_index_eq 
                            by (smt (verit) add_diff_inverse_nat add_le_cancel_right add_le_same_cancel2 diff_diff_cancel diff_is_0_eq' le_numeral_extra(4) length_butlast less_iff_succ_less_eq linordered_nonzero_semiring_class.zero_le_one nat_1_add_1 nat_diff_split_asm not_one_le_zero numeral_Bit0 ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
                        qed
                      next
                        case False
                        have 1: "(\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y)"
                        proof (rule ccontr)
                          assume "\<not> (\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y)"
                          then have "(\<exists>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<notin> Y)" by simp
                          then obtain ia where ia_prop: "ia<length pa - 1 \<and> {pa ! ia, pa ! (ia + 1)} \<notin> Y" by auto
                          then have "{nth pa ia, nth pa (ia + 1)} \<in> {{?v, ?w}}" using pa_prop by auto
                          then have "{nth pa ia, nth pa (ia + 1)} = {?v, ?w}" by auto
                          then have "nth pa ia = ?w \<or> nth pa (ia + 1) = ?w" 
                            by (meson doubleton_eq_iff)
                          then have "List.member pa ?w" using ia_prop 
                            by (metis add_lessD1 in_set_member less_diff_conv nth_mem)
                          then show False using False by simp
                        qed
                        show ?thesis 
                        proof (cases "Y = {}")
                          case True
                          then show False using 1 pa_prop by force
                        next
                          case False
                          then show False using \<open>u \<in> V2\<close> \<open>acyclic V2 Y\<close> 1  unfolding acyclic_def 
                            using pa_prop by blast
                        qed
                      qed
                    next
                      case False
                      show ?thesis 
                      proof(cases "List.member pa ?w")
                        case True
                        then have "?w \<in> set pa" using in_set_member pa_prop by force
                        then obtain ia where ia_prop: "nth pa ia = ?w" "ia \<ge> 0 \<and> ia < length pa" using in_set_conv_nth 
                          by (metis bot_nat_0.extremum)
                        have "ia \<noteq> 0"
                        proof
                          assume "ia = 0"
                          then have "nth pa 0 = ?w" using ia_prop by simp
                          then have "hd pa = ?w" using hd_conv_nth pa_prop by fast
                          then show False using pa_prop \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by simp
                        qed
                        have "ia \<noteq> length pa - 1"
                        proof
                          assume "ia = length pa - 1"
                          then have "nth pa (length pa - 1) = ?w" using ia_prop by simp
                          then have "last pa = ?w" using last_conv_nth pa_prop by fast
                          then show False using pa_prop \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by simp
                        qed
                        have "ia \<noteq> 1"
                        proof
                          assume "ia = 1"
                          have "{nth pa 0, nth pa 1} \<in> Y \<union> {{?v, ?w}}" using pa_prop by simp
                          then have "{hd pa, ?w} \<in> Y \<union> {{?v, ?w}}" using ia_prop hd_conv_nth pa_prop \<open>ia = 1\<close> by fastforce
                          then have "{u, ?w} \<in> Y \<union> {{?v, ?w}}" using pa_prop by simp
                          moreover have "u \<in> V2 \<union> {?w}" using \<open>u \<in> V2\<close> by simp
                          ultimately show False using w_el_prop \<open>u \<noteq> ?v\<close> by auto
                        qed
                        have not_w1: "nth pa 1 \<noteq> ?w" 
                        proof
                          assume "nth pa 1 = ?w"
                          moreover have "1 < length (butlast pa)" using pa_prop by auto
                          moreover have "ia < length (butlast pa)"
                          proof (rule ccontr)
                            assume "\<not>ia < length (butlast pa)"
                            then have "ia = length pa - 1" using ia_prop by simp
                            then have "nth pa (length pa - 1) = ?w" using ia_prop by simp
                            then show False using pa_prop last_conv_nth \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by fastforce
                          qed
                          moreover have "nth pa ia = nth pa 1" using \<open>nth pa 1=  ?w\<close> ia_prop by simp
                          ultimately show False using nth_butlast pa_prop 
                            by (metis \<open>ia \<noteq> 1\<close> nth_eq_iff_index_eq)
                        qed
                        have "ia \<noteq> (length pa - 1 - 1)"
                        proof
                          assume "ia = length pa - 1 - 1"
                          have "length pa - 1 - 1 + 1 = length pa - 1" using pa_prop by auto
                          moreover have "length pa - 1 - 1 < length pa - 1" using pa_prop by auto
                          ultimately have "{nth pa (length pa - 1 - 1), nth pa (length pa - 1 -1 + 1)} \<in> Y \<union> {{?v, ?w}}" using pa_prop by blast
                          then have "{nth pa (length pa - 1 - 1), nth pa (length pa - 1)} \<in> Y \<union> {{?v, ?w}}" using \<open>length pa - 1 -1 + 1 = length pa - 1\<close> by simp
                          then have "{last pa, ?w} \<in> Y \<union> {{?v, ?w}}" using ia_prop last_conv_nth pa_prop \<open>ia = length pa - 1 - 1\<close> by (metis insert_commute)
                          then have "{u, ?w} \<in> Y \<union> {{?v, ?w}}" using pa_prop by simp
                          moreover have "u \<in> V2 \<union> {?w}" using \<open>u \<in> V2\<close> by simp
                          ultimately show False using w_el_prop \<open>u \<noteq> ?v\<close> by auto
                        qed
                        have len2_not_w: "nth pa (length pa - 1 - 1) \<noteq> ?w" 
                        proof
                          assume "nth pa (length pa - 1 - 1) = ?w"
                          moreover have "(length pa - 1 - 1) < length (butlast pa)" using pa_prop by auto
                          moreover have "ia < length (butlast pa)"
                          proof (rule ccontr)
                            assume "\<not>ia < length (butlast pa)"
                            then have "ia = length pa - 1" using ia_prop by simp
                            then have "nth pa (length pa - 1) = ?w" using ia_prop by simp
                            then show False using pa_prop last_conv_nth \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by fastforce
                          qed
                          moreover have "nth pa ia = nth pa (length pa - 1 - 1)" using \<open>nth pa (length pa - 1 - 1)=  ?w\<close> ia_prop by simp
                          ultimately show False using nth_butlast pa_prop 
                            by (metis \<open>ia \<noteq> (length pa - 1 - 1)\<close> nth_eq_iff_index_eq)
                        qed
                        show ?thesis
                        proof (cases "length pa = 4")
                          case True
                          have fact0: "nth pa 0 \<noteq> ?w" using pa_prop hd_conv_nth \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> by fastforce
                          have fact3: "nth pa 3 \<noteq> ?w" using pa_prop last_conv_nth \<open>u \<in> V2\<close> \<open>?w \<in> V1 - V2\<close> True by fastforce
                          have fact1: "nth pa 1 \<noteq> ?w" using not_w1 by simp
                          have fact2: "nth pa 2 \<noteq> ?w" using True len2_not_w by simp
                          have "?w \<notin> set pa"
                          proof 
                            assume "?w \<in> set  pa"
                            then obtain ia' where ia'_prop: "nth pa ia' = ?w \<and> ia' \<ge> 0 \<and> ia' < length pa" using in_set_conv_nth 
                              by (metis bot_nat_0.extremum)  
                            then have "ia' \<in> {0, 1 ,2 ,3}" using True by auto
                            then show False
                            proof (elim insertE)
                              show "ia' = 0 \<Longrightarrow> False" using fact0 ia'_prop by simp
                              show "ia' = 1 \<Longrightarrow> False" using fact1 ia'_prop by simp
                              show "ia' = 2 \<Longrightarrow> False" using fact2 ia'_prop by simp
                              show "ia' = 3 \<Longrightarrow> False" using fact3 ia'_prop by simp
                              show "ia' \<in> {} \<Longrightarrow> False" using  ia'_prop by simp
                            qed
                          qed
                          then have "\<not> List.member pa ?w" using in_set_member pa_prop by force
                          then show ?thesis using \<open>List.member pa ?w\<close> by simp
                        next
                          case False
                          then have "length pa > 4" using pa_prop by simp 
                          have "ia < length pa -1 - 1" using ia_prop \<open>ia \<noteq> length pa - 1\<close> \<open>ia \<noteq> length pa - 1 -1\<close> by simp
                          then have "ia + 1 < length (butlast pa)" by simp
                          have f1: "{nth pa ia , nth pa (ia + 1)} \<in> Y \<union> {{?v, ?w}}" using pa_prop \<open>ia < length pa - 1 - 1\<close> by simp
                          then have "{?w , nth pa (ia + 1)} \<in> Y \<union> {{?v, ?w}}" using ia_prop by simp
                          then have "{nth pa ia , nth pa (ia + 1)} \<subseteq> V2 \<union> {?w}" using f1 \<open>undirected_graph (V2 \<union>{?w}) (Y \<union> {{?v, ?w}})\<close> unfolding undirected_graph_def by auto
                          have "nth pa (ia + 1) = ?v"
                          proof (rule ccontr)
                            assume "nth pa (ia + 1) \<noteq> ?v"
                            have "nth pa (ia + 1) \<noteq> ?w" 
                            proof
                              assume "nth pa (ia + 1) = ?w"
                              then have "{?w, ?w} \<in> Y \<union> {{?v, ?w}}" using \<open>{?w, nth pa (ia + 1)} \<in> Y \<union> {{?v, ?w}}\<close> by simp
                              moreover have "?v \<noteq> ?w" using \<open>?v \<in> V1 \<inter> V2\<close> \<open>?w \<in> V1 - V2\<close> by auto
                              moreover have "?w \<in> V2 \<union> {?w}" by simp
                              ultimately show False using w_el_prop by auto
                            qed
                            have "nth pa (ia + 1) \<in> V2 \<union> {?w}" using \<open>{nth pa ia, nth pa (ia+ 1)} \<subseteq> V2 \<union> {?w}\<close> by simp
                            then show False using \<open>nth pa (ia + 1) \<noteq> ?v\<close> \<open>{?w, nth pa (ia+ 1)} \<in> Y \<union> {{?v, ?w}}\<close> w_el_prop 
                              by (metis insert_commute) 
                          qed
                          have "ia > 1" using ia_prop \<open>ia \<noteq> 1\<close>
                            by (simp add: \<open>ia \<noteq> 0\<close> nat_neq_iff)
                          have "ia - 1 \<ge> 0" by simp
                          moreover have "ia - 1 < length (butlast pa)" using pa_prop ia_prop by auto
                          moreover have "ia - 1 < length pa - 1" using pa_prop ia_prop by auto
                          moreover have "ia - 1 + 1 = ia" using \<open>ia > 1\<close> by simp
                          ultimately have "{nth pa (ia - 1), nth pa ia} \<in> Y \<union> {{?v, ?w}}" using pa_prop by metis
                          then have "{nth pa (ia - 1), ?w} \<in> Y \<union> {{?v, ?w}}" using ia_prop by simp
                          then have "{nth pa (ia - 1) , ?w} \<subseteq> V2 \<union> {?w}" using \<open>undirected_graph (V2 \<union>{?w}) (Y \<union> {{?v, ?w}})\<close> unfolding undirected_graph_def by auto
                          have "nth pa (ia - 1) = ?v"
                          proof (rule ccontr)
                            assume "nth pa (ia - 1) \<noteq> ?v"
                            have "nth pa (ia - 1) \<noteq> ?w" 
                            proof
                              assume "nth pa (ia - 1) = ?w"
                              then have "{?w, ?w} \<in> Y \<union> {{?v, ?w}}" using \<open>{nth pa (ia - 1), ?w} \<in> Y \<union> {{?v, ?w}}\<close> by simp
                              moreover have "?v \<noteq> ?w" using \<open>?v \<in> V1 \<inter> V2\<close> \<open>?w \<in> V1 - V2\<close> by auto
                              moreover have "?w \<in> V2 \<union> {?w}" by simp
                              ultimately show False using w_el_prop by auto
                            qed
                            have "nth pa (ia - 1) \<in> V2 \<union> {?w}" using \<open>{nth pa (ia - 1), ?w} \<subseteq> V2 \<union> {?w}\<close> by simp
                            then show False using \<open>nth pa (ia - 1) \<noteq> ?v\<close> \<open>{nth pa (ia - 1), ?w} \<in> Y \<union> {{?v, ?w}}\<close> w_el_prop 
                              by (metis insert_commute) 
                          qed
                          then show ?thesis using \<open>ia - 1 < length (butlast pa)\<close> \<open>ia + 1 < length (butlast pa)\<close> \<open>nth pa (ia + 1) = ?v\<close> nth_butlast pa_prop
                              nth_eq_iff_index_eq  by (smt (verit) add_diff_inverse_nat add_le_cancel_right add_le_same_cancel2 diff_diff_cancel diff_is_0_eq' le_numeral_extra(4) length_butlast less_iff_succ_less_eq linordered_nonzero_semiring_class.zero_le_one nat_1_add_1 nat_diff_split_asm not_one_le_zero numeral_Bit0 ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
                        qed
                      next
                        case False
                        have 1: "(\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y)"
                        proof (rule ccontr)
                          assume "\<not> (\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y)"
                          then have "(\<exists>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<notin> Y)" by simp
                          then obtain ia where ia_prop: "ia<length pa - 1 \<and> {pa ! ia, pa ! (ia + 1)} \<notin> Y" by auto
                          then have "{nth pa ia, nth pa (ia + 1)} \<in> {{?v, ?w}}" using pa_prop by auto
                          then have "{nth pa ia, nth pa (ia + 1)} = {?v, ?w}" by auto
                          then have "nth pa ia = ?w \<or> nth pa (ia + 1) = ?w" 
                            by (meson doubleton_eq_iff)
                          then have "List.member pa ?w" using ia_prop 
                            by (metis add_lessD1 in_set_member less_diff_conv nth_mem)
                          then show False using False by simp
                        qed
                        show ?thesis 
                        proof (cases "Y = {}")
                          case True
                          then show False using 1 pa_prop by force
                        next
                          case False
                          then show False using \<open>u \<in> V2\<close> \<open>acyclic V2 Y\<close> 1  unfolding acyclic_def 
                            using pa_prop by blast
                        qed
                        qed
                    qed
                  qed
                qed
              qed
            qed
            then show "Y \<union> {{v', w}} = {} \<or>
    (\<forall>v\<in>V2 \<union> {w}.
        \<nexists>p. p \<noteq> [] \<and>
            hd p = v \<and>
            last p = v \<and>
            (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
            4 \<le> length p \<and> distinct (butlast p))" by simp
          qed
          have "connected (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})" unfolding connected_def
          proof (cases "Y = {} \<and> card V2 = 1")
            case True
            then have "Y \<union> {{?v, ?w}} = {{?v, ?w}}" by simp
            have "V2 = {r}" using \<open>r \<in> V2\<close>  True card_1_singletonE by auto
            have "r \<in> V1 \<inter> V2" using \<open>r \<in> V1\<close> \<open>r \<in> V2\<close> by simp
            then have "?v = r" using \<open>r \<in> V1 \<inter> V2\<close> \<open>?v \<in> V1 \<inter> V2\<close> \<open>V2 = {r}\<close> by simp
            then have "V2 = {?v}" using \<open>V2 = {r}\<close> by simp
            then have "V2 \<union> {?w} = {?v, ?w}" by auto
            have "(\<forall>u v. u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
                2 \<le> length p))"
            proof (rule, rule)
              fix u v
              show " u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
                2 \<le> length p)"
              proof
                assume u_v_prop: "u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v"
                show "\<exists>p. p \<noteq> [] \<and>
        (hd p = v \<and> last p = u) \<and>
        (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and> 2 \<le> length p "
                proof (cases "u = ?v")
                  case True
                  then have "v = ?w" using u_v_prop \<open>V2 \<union> {?w} = {?v, ?w}\<close> by auto
                  let ?p = "[ ?w, ?v]"
                  have "?p \<noteq> []" by simp
                  moreover have "length ?p \<ge> 2" by simp
                  moreover have "hd ?p = ?w \<and> last ?p = ?v" using hd_conv_nth last_conv_nth by fastforce
                  moreover have "(\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" using \<open>Y \<union> {{v', w}} = {{v', w}}\<close>
                    by auto
                  ultimately have "?p \<noteq> [] \<and> length ?p \<ge> 2 \<and> hd ?p = ?w \<and> last ?p = ?v \<and> (\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" by simp
                  then show ?thesis using True \<open>v = ?w\<close> by blast
                next
                  case False
                  then have "u = ?w" using u_v_prop \<open>V2 \<union> {?w} = {?v, ?w}\<close> by auto
                  then have "v = ?v" using u_v_prop \<open>V2 \<union> {?w} = {?v, ?w}\<close> by auto
                  let ?p = "[?v, ?w]"
                  have "?p \<noteq> []" by simp
                  moreover have "length ?p \<ge> 2" by simp
                  moreover have "hd ?p = ?v \<and> last ?p = ?w" using hd_conv_nth last_conv_nth by fastforce
                  moreover have "(\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" using \<open>Y \<union> {{v', w}} = {{v', w}}\<close>
                    by auto
                  ultimately have "?p \<noteq> [] \<and> length ?p \<ge> 2 \<and> hd ?p = ?v \<and> last ?p = ?w \<and> (\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" by simp
                  then show ?thesis using \<open>u = ?w\<close> \<open>v = ?v\<close> by blast
                qed
              qed
            qed
            then show \<open>Y \<union> {{v', w}} = {} \<and> card (V2 \<union> {w}) = 1 \<or>
    (\<forall>u v. u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
                2 \<le> length p))\<close> by simp
          next
            case False
            then have Y_connected: "(\<forall>u v. u \<in> V2 \<and> v \<in> V2  \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y) \<and>
                2 \<le> length p))" using \<open>connected V2 Y\<close> unfolding connected_def by auto
            have "(\<forall>u v. u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
                2 \<le> length p))"
            proof (rule, rule)
              fix u v
              show " u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
                2 \<le> length p)"
              proof
                assume u_v_prop: " u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v"
                show "
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
                2 \<le> length p)"
                proof (cases "u \<in> V2 \<and> v \<in> V2")
                  case True
                  then have "u \<noteq> ?w \<and> v \<noteq> ?w" using \<open>?w \<in> V1 - V2\<close> by auto
                  then have "(\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y) \<and>
                2 \<le> length p)" using True Y_connected u_v_prop by simp
                  then show ?thesis by auto
                next
                  case False
                  then have "u \<notin> V2 \<or> v \<notin> V2" by simp
                  show ?thesis
                  proof (cases "u \<notin> V2")
                    case True
                    then have "u = ?w" using u_v_prop by simp
                    then have "v \<in> V2 " using u_v_prop by auto
                    show ?thesis
                    proof (cases "v = ?v")
                      case True
                      let ?p = "[?v, ?w]"
                      have "?p \<noteq> []" by simp
                      moreover have "length ?p \<ge> 2" by simp
                  moreover have "hd ?p = ?v \<and> last ?p = ?w" using hd_conv_nth last_conv_nth by fastforce
                  moreover have "(\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" 
                    by auto
                  ultimately have "?p \<noteq> [] \<and> length ?p \<ge> 2 \<and> hd ?p = ?v \<and> last ?p = ?w \<and> (\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" by simp
                  then show ?thesis using \<open>u = ?w\<close> \<open>v = ?v\<close> by blast
                    next
                      case False
                      then have "\<exists>p. p \<noteq> [] \<and>
        (hd p = v \<and> last p = ?v) \<and>
        (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y) \<and> 2 \<le> length p" using \<open>?v \<in> V1 \<inter> V2\<close>  \<open>v \<in> V2\<close> Y_connected by simp
                      then obtain pa where pa_prop: "pa \<noteq> [] \<and>
        (hd pa = v \<and> last pa = ?v) \<and>
        (\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y) \<and> 2 \<le> length pa" by auto
                      let ?p = "pa @ [?w]"
                      have "?p \<noteq> []" by simp
                      have "hd ?p = v \<and> last ?p = ?w" using hd_conv_nth last_conv_nth pa_prop by fastforce
                      have "length ?p \<ge> 2"  using pa_prop by simp
                      then have "length ?p - 1- 1 < length ?p - 1" by simp
                      have "length ?p  - 1 = length pa" by simp
                      moreover have "(\<forall> i < length pa. nth pa i = nth ?p i)" 
                        by (simp add: nth_append)
                      ultimately have factone: "(\<forall> i < length ?p - 1. nth pa i = nth ?p i)" by simp
                      then have "(\<forall>i<length pa - 1. {?p ! i, ?p ! (i + 1)} \<in> Y )" using pa_prop by auto
                      then have "(\<forall>i<length ?p - 1 - 1. {?p ! i, ?p ! (i + 1)} \<in> Y )" using \<open>length ?p - 1 = length pa\<close> by simp
                      then have facttwo: "(\<forall>i<length ?p - 1 - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{?v, ?w}})" by simp
                      have "(\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{?v, ?w}})"
                      proof - 
                        have "length ?p - 1 - 1 = length pa - 1" by simp
                        then have "nth ?p (length ?p - 1 - 1) = nth pa (length pa - 1)" using factone pa_prop by auto
                        also have "... = ?v" using pa_prop last_conv_nth by fastforce
                        finally have "nth ?p (length ?p - 1 - 1) = ?v" by simp
                        have "nth ?p (length ?p - 1) = ?w" by simp
                        have "length ?p - 1 - 1 + 1 = length ?p - 1" using \<open>length ?p \<ge> 2\<close> by simp
                        then have "{nth ?p (length ?p - 1 - 1), nth ?p (length ?p - 1 - 1 + 1)} = {?v, ?w}" using \<open>nth ?p (length ?p - 1) = ?w\<close> \<open>nth ?p (length ?p - 1 - 1) = ?v\<close> by simp
                        also have "... \<in> Y \<union> {{?v, ?w}}" by simp
                        finally have "{nth ?p (length ?p - 1 - 1), nth ?p (length ?p - 1 - 1 + 1)} \<in> Y \<union> {{?v, ?w}}" by simp
                        then show ?thesis using facttwo 
                          by (smt (verit, del_insts) \<open>length (pa @ [w]) - 1 - 1 + 1 = length (pa @ [w]) - 1\<close> add.commute diff_add_inverse2 less_iff_succ_less_eq nat_add_left_cancel_less nat_less_le)
                      qed
                      then show ?thesis using \<open>length ?p \<ge> 2\<close> \<open>?p \<noteq> []\<close> \<open>hd ?p = v \<and> last ?p = ?w\<close> \<open>u = ?w\<close> by blast
                    qed
                  next
                    case False
                    then have "v = ?w" using u_v_prop \<open>u \<notin> V2 \<or> v \<notin> V2\<close> by simp
                    then have "u \<in> V2 " using u_v_prop by auto
                    show ?thesis
                    proof (cases "u = ?v")
                      case True
                      let ?p = "[?w, ?v]"
                      have "?p \<noteq> []" by simp
                      moreover have "length ?p \<ge> 2" by simp
                  moreover have "hd ?p = ?w \<and> last ?p = ?v" using hd_conv_nth last_conv_nth by fastforce
                  moreover have "(\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" 
                    by auto
                  ultimately have "?p \<noteq> [] \<and> length ?p \<ge> 2 \<and> hd ?p = ?w \<and> last ?p = ?v \<and> (\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{v', w}})" by simp
                  then show ?thesis using \<open>u = ?v\<close> \<open>v = ?w\<close> by blast
                    next
                      case False
                      then have "\<exists>p. p \<noteq> [] \<and>
        (hd p = u \<and> last p = ?v) \<and>
        (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y) \<and> 2 \<le> length p" using \<open>?v \<in> V1 \<inter> V2\<close>  \<open>u \<in> V2\<close> Y_connected by simp
                      then obtain pa where pa_prop: "pa \<noteq> [] \<and>
        (hd pa = u \<and> last pa = ?v) \<and>
        (\<forall>i<length pa - 1. {pa ! i, pa ! (i + 1)} \<in> Y) \<and> 2 \<le> length pa" by auto
                      let ?p = "pa @ [?w]"
                      have "?p \<noteq> []" by simp
                      have "hd ?p = u \<and> last ?p = ?w" using hd_conv_nth last_conv_nth pa_prop by fastforce
                      have "length ?p \<ge> 2"  using pa_prop by simp
                      then have "length ?p - 1- 1 < length ?p - 1" by simp
                      have "length ?p  - 1 = length pa" by simp
                      moreover have "(\<forall> i < length pa. nth pa i = nth ?p i)" 
                        by (simp add: nth_append)
                      ultimately have factone: "(\<forall> i < length ?p - 1. nth pa i = nth ?p i)" by simp
                      then have "(\<forall>i<length pa - 1. {?p ! i, ?p ! (i + 1)} \<in> Y )" using pa_prop by auto
                      then have "(\<forall>i<length ?p - 1 - 1. {?p ! i, ?p ! (i + 1)} \<in> Y )" using \<open>length ?p - 1 = length pa\<close> by simp
                      then have facttwo: "(\<forall>i<length ?p - 1 - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{?v, ?w}})" by simp
                      have factthree:"(\<forall>i<length ?p - 1. {?p ! i, ?p ! (i + 1)} \<in> Y \<union> {{?v, ?w}})"
                      proof - 
                        have "length ?p - 1 - 1 = length pa - 1" by simp
                        then have "nth ?p (length ?p - 1 - 1) = nth pa (length pa - 1)" using factone pa_prop by auto
                        also have "... = ?v" using pa_prop last_conv_nth by fastforce
                        finally have "nth ?p (length ?p - 1 - 1) = ?v" by simp
                        have "nth ?p (length ?p - 1) = ?w" by simp
                        have "length ?p - 1 - 1 + 1 = length ?p - 1" using \<open>length ?p \<ge> 2\<close> by simp
                        then have "{nth ?p (length ?p - 1 - 1), nth ?p (length ?p - 1 - 1 + 1)} = {?v, ?w}" using \<open>nth ?p (length ?p - 1) = ?w\<close> \<open>nth ?p (length ?p - 1 - 1) = ?v\<close> by simp
                        also have "... \<in> Y \<union> {{?v, ?w}}" by simp
                        finally have "{nth ?p (length ?p - 1 - 1), nth ?p (length ?p - 1 - 1 + 1)} \<in> Y \<union> {{?v, ?w}}" by simp
                        then show ?thesis using facttwo 
                          by (smt (verit, del_insts) \<open>length (pa @ [w]) - 1 - 1 + 1 = length (pa @ [w]) - 1\<close> add.commute diff_add_inverse2 less_iff_succ_less_eq nat_add_left_cancel_less nat_less_le)
                      qed
                      let ?p' = "rev ?p"
                      have "?p' \<noteq> []" by simp
                      moreover have "length ?p' \<ge> 2" using \<open>length ?p \<ge> 2\<close> by simp
                      moreover have "hd ?p' = ?w \<and> last ?p' = u" using \<open>hd ?p = u \<and> last ?p = ?w\<close>  
                        by (metis hd_rev rev_rev_ident)
                      moreover have "(\<forall>i<length ?p' - 1. {?p' ! i, ?p' ! (i + 1)} \<in> Y \<union> {{?v, ?w}})" 
                      proof (rule allI impI)
                        fix i
                        show "i < length (rev (pa @ [w])) - 1 \<longrightarrow>
         {rev (pa @ [w]) ! i, rev (pa @ [w]) ! (i + 1)} \<in> Y \<union> {{v', w}} "
                        proof
                        assume "i < length (rev (pa @ [w])) - 1"
                        then have "length ?p' - 1 - 1 - i< length ?p' - 1" using \<open>i < length (?p') - 1\<close> by simp
                        then have "length ?p' - 1 - (i + 1) < length ?p' - 1" by simp
                        then have "length ?p' - 1 - (i + 1) + 1  = length ?p' - 1 - i" using \<open>length ?p' \<ge> 2\<close> 
                          using Suc_diff_Suc \<open>i < length (rev (pa @ [w])) - 1\<close> by presburger
                        then have "length ?p' - 1 - i < length ?p'" using \<open>length ?p' - 1 - (i + 1) < length ?p' - 1\<close> by auto 
                        have "length ?p' - 1 - (i + 1) < length ?p'" using \<open>length ?p' - 1 - (i + 1) < length ?p' - 1\<close> \<open>length ?p' \<ge> 2\<close> by simp
                        have f1: "length ?p' - 1 - (length ?p - 1 - (i + 1)) = i + 1" using \<open>length ?p' - 1 - (i + 1) < length ?p' - 1\<close> \<open>length ?p' \<ge> 2\<close>
                          using \<open>i < length (rev (pa @ [w])) - 1\<close> by fastforce
                        have f2: "length ?p' - 1 - (length ?p' - 1 - i) = i" using \<open>i < length ?p' - 1\<close> by fastforce
                        have "length ?p' - 1 - 1 - i< length ?p - 1" using \<open>length ?p' - 1 - 1 - i< length ?p' - 1\<close> by simp
                        then have f3: "{?p ! (length ?p' - 1 - (i + 1)), ?p ! (length ?p' - 1 - i)} \<in> Y \<union> {{?v, ?w}}" using \<open>length ?p' - 1 - (i + 1) + 1  = length ?p' - 1 - i\<close> factthree by fastforce
                        have "\<forall>i. i < length ?p \<longrightarrow> nth ?p i = nth ?p' (length ?p - 1 - i)" 
                          by (smt (verit, best) Nat.lessE Suc_diff_1 cancel_comm_monoid_add_class.diff_cancel diff_Suc_1' diff_Suc_Suc length_rev rev_nth rev_rev_ident zero_less_one)
                        then have "{?p ! (length ?p' - 1 - (i + 1)), ?p ! (length ?p' - 1 - i)} = {nth ?p' (i + 1), nth ?p' i}" using f1 f2 \<open>length ?p' - 1 - (i + 1) < length ?p' - 1\<close> 
                          \<open>length ?p' \<ge> 2\<close> 
                          by (metis \<open>length (rev (pa @ [w])) - 1 - (i + 1) < length (rev (pa @ [w]))\<close> \<open>length (rev (pa @ [w])) - 1 - i < length (rev (pa @ [w]))\<close> f1 f2 length_rev)
                        then show " {rev (pa @ [w]) ! i, rev (pa @ [w]) ! (i + 1)} \<in> Y \<union> {{v', w}}" using f3 insert_commute by metis
                      qed
                    qed
                      ultimately show ?thesis using \<open>v = ?w\<close> by blast
                    qed
                  qed
                qed
              qed
            qed
            then show "Y \<union> {{v', w}} = {} \<and> card (V2 \<union> {w}) = 1 \<or>
    (\<forall>u v. u \<in> V2 \<union> {w} \<and> v \<in> V2 \<union> {w} \<and> u \<noteq> v \<longrightarrow>
           (\<exists>p. p \<noteq> [] \<and>
                (hd p = v \<and> last p = u) \<and>
                (\<forall>i<length p - 1. {p ! i, p ! (i + 1)} \<in> Y \<union> {{v', w}}) \<and>
                2 \<le> length p))" by simp
          qed
          have "finite Y" using Y_prop \<open>finite V2\<close>  by (meson Sup_le_iff finite_UnionD rev_finite_subset)
          then have "finite (Y \<union> {{?v, ?w}})" by simp
          have "card (V2 \<union> {?w}) = card (V2) + 1" using  \<open>?w \<in> V1 - V2\<close> \<open>finite V2\<close> by simp
           have  "card V2 + 1 = card Y + 1 + 1" using \<open>card V2 = card Y + 1\<close> by simp
           then have "card Y + 1 = card (Y \<union> {{?v, ?w}})" using \<open>{?v, ?w} \<notin> Y\<close> \<open>finite Y\<close> by simp
           then have "card Y + 1 + 1 = card (Y \<union> {{?v, ?w}}) + 1"  by simp 
           then have "card V2 +1 =  card (Y \<union> {{?v, ?w}}) + 1" using \<open>card V2 + 1 = card Y + 1 + 1\<close> by simp
           then have "card (V2 \<union> {?w}) = card (Y \<union> {{?v, ?w}}) + 1" using \<open>card (V2 \<union> {?w}) = card V2 + 1\<close> by simp
           then have "tree (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})" using \<open>acyclic (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})\<close>
\<open>connected (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})\<close> \<open>undirected_graph (V2 \<union> {?w}) (Y \<union> {{?v, ?w}})\<close> unfolding tree_def by simp
           moreover have "V2 \<union> {?w} \<subseteq> V" using \<open>?w \<in> V1 - V2\<close> X_prop1 Y_prop by auto
           moreover have "{?v, ?w} \<in> X - Y" using \<open>{?v, ?w} \<in> X\<close> \<open>{?v, ?w} \<notin> Y\<close> by simp
           moreover have "r \<in> V2 \<union> {?w}" using \<open>r \<in> V2\<close> by simp
           moreover have "Y \<union> {{?v, ?w}} \<subseteq> E" using \<open>{?v, ?w} \<in> X\<close> V1_prop V2_prop by auto
           ultimately have "Y \<union> {{?v, ?w}} \<in> {Y. \<exists>X\<subseteq>V. Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}" by blast 
           then show ?thesis using \<open>{?v, ?w} \<in> X - Y\<close> by auto
         qed
       qed
     qed 
     thus ?thesis using assms 
       by simp
   qed

lemma greedoid_graph_example: 
  assumes "undirected_graph V E" "r \<in> V" 
  shows "greedoid E {Y. \<exists> X. X \<subseteq> V \<and> Y \<subseteq> E \<and> r \<in> X \<and> tree X Y}"
  using extension_property[OF assms] defines_set_system[OF assms] empty_in[OF assms]
  by(unfold_locales)

end
end
