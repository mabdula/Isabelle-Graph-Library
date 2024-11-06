theory Order_Relations_From_Priorities
  imports 
    Order_Relations
    Treaps.Random_List_Permutation
begin

subsection \<open>Unweighted Case\<close>
lemma preorder_on_linorder_from_keys[intro]: "preorder_on A (linorder_from_keys A f)"
  unfolding linorder_from_keys_def preorder_on_def
  by (auto simp: refl_on_def trans_def total_on_def) 

lemma linorder_from_keys_in_preorders_on[intro]: "linorder_from_keys A f \<in> preorders_on A"
  by auto

lemma linorder_from_keys_lessI:
  assumes "f i < f j"
  assumes "i \<in> A" "j \<in> A"
  shows "(i,j) \<in> linorder_from_keys A f \<and> (j,i) \<notin> linorder_from_keys A f"
  using assms
  unfolding linorder_from_keys_def
  by auto

lemma linorder_from_keys_Restr:
  shows "Restr (linorder_from_keys A f) (A - B) = linorder_from_keys (A - B) f"
  unfolding linorder_from_keys_def
  by blast

lemma linorder_from_keys_update_eq:
  shows "linorder_from_keys (A - {a}) (f(a:=x)) = linorder_from_keys (A - {a}) f"
  unfolding linorder_from_keys_def
  by auto

text \<open>Generalize @{thm measurable_linorder_from_keys_restrict} by Eberl from
 \<^term>\<open>count_space (Pow (A \<times> A))\<close> to \<^term>\<open>count_space (preorders_on A)\<close>. The original
  statement then also follows with @{thm measurable_count_space_extend}.\<close>
lemma measurable_linorder_from_keys_restrict_preorders[measurable]:
  assumes fin: "finite A"
  shows "linorder_from_keys A \<in> Pi\<^sub>M A (\<lambda>_. borel :: real measure) \<rightarrow>\<^sub>M count_space (preorders_on A)"
  (is "_ : ?M \<rightarrow>\<^sub>M _")
  apply (subst measurable_count_space_eq2)
   apply (auto simp: fin)
proof -
  note fin[simp]
  fix r assume "r \<in> preorders_on A"
  then have "linorder_from_keys A -` {r} \<inter> space ?M =
    {f \<in> space ?M. \<forall>x\<in>A. \<forall>y\<in>A. (x,y) \<in> r \<longleftrightarrow> f x \<le> f y}"
    by (auto simp: linorder_from_keys_def preorder_on_def set_eq_iff dest!: preorders_onD refl_on_domain)

  also have "\<dots> \<in> sets ?M"
    by measurable

  finally show "linorder_from_keys A -` {r} \<inter> space ?M \<in> sets ?M" .
qed

lemma linorder_on_linorder_from_keys_insert:
  assumes linorder: "linorder_on A (linorder_from_keys A f)"
  assumes "y \<notin> f ` A"
  assumes "a \<notin> A"
  shows "linorder_on (insert a A) (linorder_from_keys (insert a A) (f(a:=y)))"
proof -
  from \<open>a \<notin> A\<close> have linorder_from_insert: "linorder_from_keys (insert a A) (f(a:=y)) = linorder_from_keys A f \<union> {(a,a)} \<union> {(a,b) | b. b \<in> A \<and> y \<le> f b} \<union> {(b,a) | b. b \<in> A \<and> f b \<le> y}"
    unfolding linorder_from_keys_def
    by (auto split: if_splits)

  show "linorder_on (insert a A) (linorder_from_keys (insert a A) (f(a:=y)))"
    unfolding linorder_on_def
  proof (intro conjI, goal_cases)
    case 1
    with linorder show ?case
      by (subst linorder_from_insert)
         (auto simp: linorder_on_def refl_on_def)
  next
    case 2
    with linorder \<open>a \<notin> A\<close> \<open>y \<notin> f ` A\<close> show ?case
      by (subst linorder_from_insert)
         (auto simp: linorder_on_def antisym_def dest: refl_on_domain)
  next
    case 3
    with linorder \<open>a \<notin> A\<close> \<open>y \<notin> f ` A\<close> show ?case
      by (subst linorder_from_insert, unfold trans_def)
         (auto simp: linorder_from_keys_def linorder_on_def)
  next
    case 4
    with linorder show ?case
      by (subst linorder_from_insert, unfold linorder_on_def total_on_def)
         auto
  qed
qed

text \<open>Adapted from @{thm almost_everywhere_linorder}\<close>
lemma almost_everywhere_linorder_preorders: 
  fixes a b :: real
  assumes fin: "finite A" and ab: "a < b"
  defines "M \<equiv> distr (\<Pi>\<^sub>M i \<in> A. uniform_measure lborel {a..b}) (count_space (preorders_on A)) (linorder_from_keys A)"
  shows "AE R in M. linorder_on A R"
proof -
  define N where "N = PiM A (\<lambda>_. uniform_measure lborel {a..b})"
  have [simp]: "sets (Pi\<^sub>M A (\<lambda>_. uniform_measure lborel {a..b})) = sets (PiM A (\<lambda>_. lborel))"
    by (intro sets_PiM_cong) simp_all
  let ?M_A = "(Pi\<^sub>M A (\<lambda>_. lborel :: real measure))"
  have meas: "{h \<in> A \<rightarrow>\<^sub>E UNIV. h i = h j} \<in> sets ?M_A"
    if [simp]: "i \<in> A" "j \<in> A" for i j
  proof -
    have "{h \<in> A \<rightarrow>\<^sub>E UNIV. h i = h j} = {h \<in> space ?M_A. h i = h j}"
      by (auto simp: space_PiM)
    also have "... \<in> sets ?M_A"
      by measurable
    finally show ?thesis .
  qed
  define X :: "('a \<Rightarrow> real) set" where "X = (\<Union>x\<in>A. \<Union>y\<in>A-{x}. {h\<in>A \<rightarrow>\<^sub>E UNIV. h x = h y})"
  have "AE f in N. inj_on f A"
  proof (rule AE_I)
    show "{f \<in> space N. \<not> inj_on f A} \<subseteq> X"
      by (auto simp: inj_on_def X_def space_PiM N_def)
  next
    show "X \<in> sets N" unfolding X_def N_def
      using meas by (auto intro!: countable_finite fin sets.countable_UN')
  next
    have "emeasure N X \<le> (\<Sum>i\<in>A. emeasure N (\<Union>y\<in>A - {i}. {h \<in> A \<rightarrow>\<^sub>E UNIV. h i = h y}))"
      unfolding X_def N_def using fin meas
      by (intro emeasure_subadditive_finite) 
         (auto simp: disjoint_family_on_def intro!: sets.countable_UN' countable_finite)
    also have "\<dots> \<le> (\<Sum>i\<in>A. \<Sum>j\<in>A-{i}. emeasure N {h \<in> A \<rightarrow>\<^sub>E UNIV. h i = h j})"
      unfolding N_def using fin meas
      by (intro emeasure_subadditive_finite sum_mono) 
         (auto simp: disjoint_family_on_def intro!: sets.countable_UN' countable_finite)
    also have "\<dots> = (\<Sum>i\<in>A. \<Sum>j\<in>A-{i}. 0)" unfolding N_def using fin ab
      by (intro sum.cong refl emeasure_PiM_diagonal) auto
    also have "\<dots> = 0" by simp
    finally show "emeasure N X = 0" by simp
  qed
  hence "AE f in N. linorder_on A (linorder_from_keys A f)"
    by eventually_elim auto
  with fin show ?thesis unfolding M_def N_def
    by (subst AE_distr_iff) auto
qed

text \<open>Adapted from @{thm random_linorder_by_prios}\<close>
lemma random_linorder_by_prios_preorders:
  fixes a b :: real
  assumes fin: "finite A" and ab: "a < b"
  defines "M \<equiv> distr (\<Pi>\<^sub>M i \<in> A. uniform_measure lborel {a..b}) (count_space (preorders_on A)) (linorder_from_keys A)"
  shows
  "M = uniform_measure (count_space (preorders_on A)) (linorders_on A)"
proof -
  from linorders_finite_nonempty[OF fin] obtain R where R: "linorder_on A R"
    by (auto simp: linorders_on_def)
  
  have *: "emeasure M {R} \<le> emeasure M {R'}" if "linorder_on A R" "linorder_on A R'" for R R'
  proof -
    define N where "N = PiM A (\<lambda>_. uniform_measure lborel {a..b})"
    from linorder_permutation_exists[OF fin that]
    obtain \<pi> where \<pi>: "\<pi> permutes A" "R' = map_relation A \<pi> R"
      by blast
    have "(\<lambda>f. f \<circ> \<pi>) \<in> Pi\<^sub>M A (\<lambda>_. lborel :: real measure) \<rightarrow>\<^sub>M Pi\<^sub>M A (\<lambda>_. lborel :: real measure)"
      by (auto intro!: measurable_PiM_single' measurable_PiM_component_rev
          simp: comp_def permutes_in_image[OF \<pi>(1)] space_PiM PiE_def extensional_def)
    also have "\<dots> = N \<rightarrow>\<^sub>M Pi\<^sub>M A (\<lambda>_. lborel)"
      unfolding N_def by (intro measurable_cong_sets refl sets_PiM_cong) simp_all
    finally have [measurable]: "(\<lambda>f. f \<circ> \<pi>) \<in> \<dots>" .    
        
    have [simp]: "measurable N X = measurable (PiM A (\<lambda>_. lborel)) X" for X :: "('a \<times> 'a) set measure"
      unfolding N_def by (intro measurable_cong_sets refl sets_PiM_cong) simp_all
    have [simp]: "measurable M X = measurable (count_space (preorders_on A)) X" for X :: "('a \<times> 'a) set measure"
      unfolding M_def by simp
      
    have M_eq: "M = distr N (count_space (preorders_on A)) (linorder_from_keys A)"
      by (simp only: M_def N_def)
    also have "N = distr N (PiM A (\<lambda>_. lborel)) (\<lambda>f. f \<circ> \<pi>)"
      unfolding N_def by (rule PiM_uniform_measure_permute [symmetric]) fact+
    also have "distr \<dots> (count_space (preorders_on A)) (linorder_from_keys A) = 
                 distr N (count_space (preorders_on A)) (linorder_from_keys A \<circ> (\<lambda>f. f \<circ> \<pi>))"
      using fin
      by (intro distr_distr) measurable
    also have "\<dots> = distr N (count_space (preorders_on A)) (map_relation A \<pi> \<circ> linorder_from_keys A)"
      by (intro distr_cong refl) (auto simp: linorder_from_keys_permute[OF \<pi>(1)])
    also have "\<dots> = distr M (count_space (preorders_on A)) (map_relation A \<pi>)"
      unfolding M_eq
      using fin \<pi>
      by (intro distr_distr [symmetric])
         (auto simp: map_relation_def intro!: preorder_on_permutes preorders_onI dest!: preorders_onD)
    finally have M_eq': "distr M (count_space (preorders_on A)) (map_relation A \<pi>) = M" ..

    from that have preorder: "R \<in> preorders_on A" "R' \<in> preorders_on A"
      by (auto dest: linorder_on_imp_preorder_on)
    hence "emeasure M {R} \<le> emeasure M (map_relation A \<pi> -` {R'} \<inter> space M)"
      using preorder by (intro emeasure_mono) (auto simp: M_def \<pi> )
    also have "\<dots> = emeasure (distr M (count_space (preorders_on A)) (map_relation A \<pi>)) {R'} "
      by (rule emeasure_distr [symmetric])
         (use preorder \<pi> in \<open>auto simp: map_relation_def intro!: preorders_onI preorder_on_permutes dest: preorders_onD\<close>)
    also note M_eq'
    finally show ?thesis .
  qed
  have same_prob: "emeasure M {R'} = emeasure M {R}" if "linorder_on A R'" for R'
    using *[of R R'] and *[of R' R] and R and that by simp
  
  from ab fin have "prob_space M"
    unfolding M_def
    by (intro prob_space.prob_space_distr prob_space_PiM prob_space_uniform_measure) simp_all
  hence "1 = emeasure M (preorders_on A)" 
    using prob_space.emeasure_space_1[OF \<open>prob_space M\<close>] by (simp add: M_def)
  also have "preorders_on A  = linorders_on A \<union> ((preorders_on A)-linorders_on A)"
    by (auto simp: linorders_on_def linorder_on_def refl_on_def preorders_on_def preorder_on_def)
  also have "emeasure M \<dots> = emeasure M (linorders_on A) + emeasure M ((preorders_on A)-linorders_on A)"
    by (subst plus_emeasure) (auto simp: M_def linorders_on_def linorder_on_def refl_on_def preorders_on_def preorder_on_def)
  also have "emeasure M ((preorders_on A)-linorders_on A) = 0" using almost_everywhere_linorder_preorders[OF fin ab]
    by (subst (asm) AE_iff_measurable) (auto simp: linorders_on_def M_def)
  also from fin have "emeasure M (linorders_on A) = (\<Sum>R'\<in>linorders_on A. emeasure M {R'})"
    by (intro emeasure_eq_sum_singleton) 
       (auto simp: M_def  linorders_on_def linorder_on_def refl_on_def preorders_on_def preorder_on_def)
  also have "\<dots> = (\<Sum>R'\<in>linorders_on A. emeasure M {R})"
    by (rule sum.cong) (simp_all add: linorders_on_def same_prob)
  also from fin have "\<dots> = fact (card A) * emeasure M {R}"
    by (simp add: linorders_on_def card_finite_linorders)
  finally have [simp]: "emeasure M {R} = inverse (fact (card A))"
    by (simp add: inverse_ennreal_unique)
  
  show ?thesis
  proof (rule measure_eqI_countable_AE')
    show "sets M = Pow (preorders_on A)"
      by (simp add: M_def)
  next
    from \<open>finite A\<close> show "countable (linorders_on A)"
      by (blast intro: countable_finite)
  next
    show "AE R in uniform_measure (count_space (preorders_on A)) 
            (linorders_on A). R \<in> linorders_on A"
      by (rule AE_uniform_measureI)
         (auto simp: linorders_on_def preorders_on_def dest: linorder_on_imp_preorder_on)
  next
    fix R' assume R': "R' \<in> linorders_on A"
    have subset: "linorders_on A \<subseteq> preorders_on A"
      by (auto simp: linorders_on_def preorders_on_def dest: linorder_on_imp_preorder_on)
    have "emeasure (uniform_measure (count_space (preorders_on A)) 
           (linorders_on A)) {R'} = emeasure (count_space (preorders_on A)) (linorders_on A \<inter> {R'}) /
                                      emeasure (count_space (preorders_on A)) (linorders_on A)"
      using R' by (subst emeasure_uniform_measure) (auto simp: linorders_on_def preorders_on_def dest: linorder_on_imp_preorder_on)
    also have "\<dots> = 1 / emeasure (count_space (preorders_on A)) (linorders_on A)"
      using R' by (subst emeasure_count_space) (auto simp: linorders_on_def preorders_on_def dest: linorder_on_imp_preorder_on)
    also have "\<dots> = 1 / fact (card A)"
      using fin finite_linorders_on[of A]
      by (subst emeasure_count_space [OF subset])
         (auto simp: divide_ennreal [symmetric] linorders_on_def card_finite_linorders)
    also have "\<dots> = emeasure M {R}"
      by (simp add: field_simps divide_ennreal_def)
    also have "\<dots> = emeasure M {R'}"
      using R' by (intro same_prob [symmetric]) (auto simp: linorders_on_def)
    finally show "emeasure M {R'} = emeasure (uniform_measure (count_space (preorders_on A)) 
                    (linorders_on A)) {R'}" ..
  next
    show "linorders_on A \<subseteq> preorders_on A"
      by (auto simp: linorders_on_def preorders_on_def dest: linorder_on_imp_preorder_on)
  next
    show "AE r in M. r \<in> linorders_on A"
      unfolding M_def
      using almost_everywhere_linorder_preorders[OF fin ab]
      by (auto simp: linorders_on_def)
  qed simp
qed

subsection \<open>Weighted Case\<close>
definition weighted_linorder_from_keys :: "'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<times> 'a) set" where
  "weighted_linorder_from_keys A v g Y = {(x, y) \<in> A \<times> A. v x * (1 - g (Y x)) \<ge> v y * (1 - g (Y y))}"

lemma preorder_on_weighted_linorder_from_keys[intro]: "preorder_on A (weighted_linorder_from_keys A v g f)"
  unfolding weighted_linorder_from_keys_def preorder_on_def
  by (auto simp: refl_on_def trans_def total_on_def) 

lemma weighted_linorder_from_keys_in_preorders_on[intro]: "weighted_linorder_from_keys A v g f \<in> preorders_on A"
  by auto

lemma measurable_weighted_linorder_from_keys[measurable]:
  assumes fin: "finite A"
  assumes "g \<in> borel_measurable borel"
  shows "weighted_linorder_from_keys A v g \<in> PiM A (\<lambda>_. borel :: real measure) \<rightarrow>\<^sub>M count_space (preorders_on A)"
  (is "_ \<in> ?M \<rightarrow>\<^sub>M _")
  apply (subst measurable_count_space_eq2)
   apply (auto simp: fin)
proof -
  note fin[simp]
  fix r assume "r \<in> preorders_on A"
  then have "weighted_linorder_from_keys A v g -` {r} \<inter> space ?M =
    {f \<in> space ?M. \<forall>x\<in>A. \<forall>y\<in>A. (x,y) \<in> r \<longleftrightarrow> v x * (1 - g(f x)) \<ge> v y * (1 - g(f y))}"
    by (auto simp: weighted_linorder_from_keys_def preorder_on_def set_eq_iff dest!: preorders_onD refl_on_domain)

  also from assms have "\<dots> \<in> sets ?M"
    by measurable

  finally show "weighted_linorder_from_keys A v g -` {r} \<inter> space ?M \<in> sets ?M" .
qed

lemma weighted_linorder_from_keys_fun_upd_eq:
  assumes "a \<notin> A"
  shows "weighted_linorder_from_keys A v g (f(a:=x)) = weighted_linorder_from_keys A v g f"
  using assms
  unfolding weighted_linorder_from_keys_def
  by auto

lemma weighted_linorder_from_keys_Restr:
  shows "Restr (weighted_linorder_from_keys A v g f) (A - B) = weighted_linorder_from_keys (A - B) v g f"
  unfolding weighted_linorder_from_keys_def
  by blast

lemma weighted_linorder_from_keys_update_eq:
  shows "weighted_linorder_from_keys (A - {a}) v g (f(a:=x)) = weighted_linorder_from_keys (A - {a}) v g f"
  unfolding weighted_linorder_from_keys_def
  by auto

lemma weighted_linorder_from_keys_lessI:
  assumes "v i * (1 - g (f i)) > v j * (1 - g (f j))"
  assumes "i \<in> A" "j \<in> A"
  shows "(i,j) \<in> weighted_linorder_from_keys A v g f \<and> (j,i) \<notin> weighted_linorder_from_keys A v g f"
  using assms
  unfolding weighted_linorder_from_keys_def
  by auto

lemma linorder_on_weighted_linorder_from_keys[intro]:
  assumes "inj_on (\<lambda>a. v a * (1 - g (f a))) A"
  shows "linorder_on A (weighted_linorder_from_keys A v g f)"
  using assms
  by (auto simp: linorder_on_def refl_on_def antisym_def weighted_linorder_from_keys_def trans_def total_on_def
           dest: inj_onD)

lemma linorder_on_weighted_linorder_from_keys_insert:
  assumes linorder: "linorder_on A (weighted_linorder_from_keys A v g f)"
  assumes no_collision: "y \<notin> {y | y i. i \<in> A \<and> v a * (1 - g y) = v i * (1 - g (f i))}"
  assumes "a \<notin> A"
  shows "linorder_on (insert a A) (weighted_linorder_from_keys (insert a A) v g (f(a:=y)))"
proof -
  from \<open>a \<notin> A\<close> have linorder_from_insert: "weighted_linorder_from_keys (insert a A) v g (f(a:=y)) =
    weighted_linorder_from_keys A v g f \<union> {(a,a)} \<union> {(a,b) | b. b \<in> A \<and> v a * (1 - g y) \<ge> v b * (1 - g (f b))} \<union> {(b,a) | b. b \<in> A \<and> v b * (1 - g (f b)) \<ge> v a * (1 - g y)}"
    unfolding weighted_linorder_from_keys_def
    by (auto split: if_splits)

  show "linorder_on (insert a A) (weighted_linorder_from_keys (insert a A) v g (f(a:=y)))"
    unfolding linorder_on_def
  proof (intro conjI, goal_cases)
    case 1
    with linorder show ?case
      by (subst linorder_from_insert)
         (auto simp: linorder_on_def refl_on_def)
  next
    case 2
    with linorder no_collision \<open>a \<notin> A\<close> show ?case
      by (subst linorder_from_insert)
         (auto simp: linorder_on_def antisym_def dest: refl_on_domain)
  next
    case 3
    with linorder no_collision \<open>a \<notin> A\<close> show ?case
      by (subst linorder_from_insert, unfold trans_def)
         (auto simp: weighted_linorder_from_keys_def linorder_on_def)
  next
    case 4
    with linorder show ?case
      by (subst linorder_from_insert, unfold linorder_on_def total_on_def)
         auto
  qed
qed

end