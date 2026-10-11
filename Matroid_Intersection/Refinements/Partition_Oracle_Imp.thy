theory Partition_Oracle_Imp
  imports Partition_Oracle Exchange_Oracles_Imp Directed_Set_Graphs.CSR_Buildup
begin

section \<open>The Unit Partition Oracle in Imperative HOL\<close>

text \<open>Elements are the nats below \<open>n\<close>, blocks the nats below \<open>nb\<close>, and the block of each
  element is stored in an array (the static data of the oracle). The oracle data of a solution
  is an array counting, for every block, the elements of the solution in it. Insertion and
  deletion of an element update one counter; insertion queries read one counter, and exchange
  queries compare two blocks. All take constant time. They refine the functional oracle of
  \<open>Partition_Oracle\<close> with sets as solutions and as block sets.\<close>

subsection \<open>Code\<close>

definition part_cnt_ins :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "part_cnt_ins Bl C i = do { b \<leftarrow> Array.nth Bl i; c \<leftarrow> Array.nth C b; Array.upd b (Suc c) C; return () }"

definition part_cnt_del :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "part_cnt_del Bl C i = do { b \<leftarrow> Array.nth Bl i; c \<leftarrow> Array.nth C b; Array.upd b (c - 1) C; return () }"

definition part_ins_imp :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "part_ins_imp Bl C y = do { b \<leftarrow> Array.nth Bl y; c \<leftarrow> Array.nth C b; return (c = 0) }"

definition part_exch_imp :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "part_exch_imp Bl x y = do { a \<leftarrow> Array.nth Bl x; b \<leftarrow> Array.nth Bl y; return (a = b) }"

subsection \<open>Correctness\<close>

definition "blocks_assn n nb bl Bl = Bl \<mapsto>\<^sub>a bl * \<up>(length bl = n \<and> (\<forall> i < n. bl ! i < nb))"

definition "bcount bl X b = card {i \<in> X. bl ! i = b}"

definition "cnt_assn nb bl X C = C \<mapsto>\<^sub>a map (bcount bl X) [0..<nb] * \<up>(finite X)"

lemma bcount_insert:
  "\<lbrakk>finite X; i \<notin> X\<rbrakk> \<Longrightarrow> 
   bcount bl (insert i X) b = (if bl ! i = b then Suc (bcount bl X b) else bcount bl X b)"
proof-
  assume a: "finite X" "i \<notin> X"
  have f: "finite {j \<in> X. bl ! j = b}"
    using a(1) by simp
  show ?thesis
  proof(cases "bl ! i = b")
    case True
    have "{j \<in> insert i X. bl ! j = b} = insert i {j \<in> X. bl ! j = b}"
      using True by auto
    then show ?thesis
      unfolding bcount_def using True a(2) card_insert_disjoint[OF f] by simp
  next
    case False
    have "{j \<in> insert i X. bl ! j = b} = {j \<in> X. bl ! j = b}"
      using False by auto
    then show ?thesis
      unfolding bcount_def using False by simp
  qed
qed

lemma bcount_delete:
  "\<lbrakk>finite X; i \<in> X\<rbrakk> \<Longrightarrow> 
   bcount bl (X - {i}) b = (if bl ! i = b then bcount bl X b - 1 else bcount bl X b)"
proof-
  assume a: "finite X" "i \<in> X"
  have "bcount bl X b = bcount bl (insert i (X - {i})) b"
    using a(2) by (simp add: insert_absorb)
  then show ?thesis
    using bcount_insert[of "X - {i}" i bl b] a(1) by simp
qed

lemma bcount_zero: "finite X \<Longrightarrow> (bcount bl X b = 0) = (b \<notin> (\<lambda> i. bl ! i) ` X)"
  unfolding bcount_def by auto

lemma map_bcount_upd:
  assumes "k < nb" "\<And> b. b < nb \<Longrightarrow> g b = (if b = k then v else f b)"
  shows "(map f [0..<nb])[k := v] = map g [0..<nb]"
  by (rule nth_equalityI) (use assms in \<open>auto simp: nth_list_update\<close>)

lemma cnt_assn_new: "<emp> Array.new nb 0 <cnt_assn nb bl {}>"
  unfolding cnt_assn_def bcount_def by (sep_auto simp: map_replicate_const)

lemma part_cnt_ins_rule:
  "<cnt_assn nb bl X C * blocks_assn n nb bl Bl * \<up>(i < n \<and> i \<notin> X)> part_cnt_ins Bl C i
   <\<lambda> _. cnt_assn nb bl (insert i X) C * blocks_assn n nb bl Bl>"
proof-
  have upd: "(map (bcount bl X) [0..<nb])[bl ! i := Suc (bcount bl X (bl ! i))] = 
             map (bcount bl (insert i X)) [0..<nb]"
    if "finite X" "i \<notin> X" "bl ! i < nb" 
    by (rule map_bcount_upd) (simp_all add: that bcount_insert[OF that(1,2)])
  show ?thesis
    unfolding part_cnt_ins_def cnt_assn_def blocks_assn_def by (sep_auto simp: upd)
qed

lemma part_cnt_del_rule:
  "<cnt_assn nb bl X C * blocks_assn n nb bl Bl * \<up>(i < n \<and> i \<in> X)> part_cnt_del Bl C i
   <\<lambda> _. cnt_assn nb bl (X - {i}) C * blocks_assn n nb bl Bl>"
proof-
  have upd: "(map (bcount bl X) [0..<nb])[bl ! i := bcount bl X (bl ! i) - Suc 0] = 
             map (bcount bl (X - {i})) [0..<nb]"
    if "finite X" "i \<in> X" "bl ! i < nb" 
    by (rule map_bcount_upd) (simp_all add: that bcount_delete[OF that(1,2)])
  show ?thesis
    unfolding part_cnt_del_def cnt_assn_def blocks_assn_def by (sep_auto simp: upd)
qed

lemma part_ins_imp_rule:
  "<cnt_assn nb bl X C * blocks_assn n nb bl Bl * \<up>(y < n)> part_ins_imp Bl C y
   <\<lambda> r. cnt_assn nb bl X C * blocks_assn n nb bl Bl * 
         \<up>(finite X \<and> r = (bl ! y \<notin> (\<lambda> i. bl ! i) ` X))>"
  unfolding part_ins_imp_def cnt_assn_def blocks_assn_def by (sep_auto simp: bcount_zero)

lemma part_exch_imp_rule:
  "<blocks_assn n nb bl Bl * \<up>(x < n \<and> y < n)> part_exch_imp Bl x y
   <\<lambda> r. blocks_assn n nb bl Bl * \<up>(r = (bl ! x = bl ! y))>"
  unfolding part_exch_imp_def blocks_assn_def by sep_auto

subsection \<open>Exchange Partners\<close>

text \<open>The potential exchange partners of an element are the elements of its block, in
  ascending order. The handle consists of three arrays: the elements grouped by block, and for
  every element the first and the end position of its block in that array. It is built once
  from the array of blocks in time \<open>O(n + nb)\<close> by the counting sort of the locale
  @{locale csr_buildup}: count the elements per block, form the prefix sums,
  and place the elements; the array of block boundaries is then read for every element. Both
  queries read two cells; the array of blocks stays with its owner.\<close>

definition "bucket bl b = filter (\<lambda> i. bl ! i = b) [0..<length bl]"

definition "part_pts bl x = bucket bl (bl ! x)"

type_synonym part_hnd = "nat array \<times> nat array \<times> nat array"

definition "part_hnd_ok n bl os ss es = 
  (length ss = n \<and> length es = n \<and> 
   (\<forall> x < n. ss ! x \<le> es ! x \<and> es ! x \<le> length os \<and> 
             part_pts bl x = take (es ! x - ss ! x) (drop (ss ! x) os)))"

definition part_pst :: "nat \<Rightarrow> nat list \<Rightarrow> part_hnd \<Rightarrow> assn" where
  "part_pst n bl H = (case H of (Oa, Sa, Ea) \<Rightarrow> 
     \<exists>\<^sub>A os ss es. Oa \<mapsto>\<^sub>a os * Sa \<mapsto>\<^sub>a ss * Ea \<mapsto>\<^sub>a es * \<up>(part_hnd_ok n bl os ss es))"

definition part_npts_imp :: "part_hnd \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "part_npts_imp H x = (case H of (Oa, Sa, Ea) \<Rightarrow> do { 
     s \<leftarrow> Array.nth Sa x; e \<leftarrow> Array.nth Ea x; return (e - s) })"

definition part_pt_imp :: "part_hnd \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "part_pt_imp H x k = (case H of (Oa, Sa, Ea) \<Rightarrow> do { s \<leftarrow> Array.nth Sa x; Array.nth Oa (s + k) })"

definition "part_count_imp n nb Bl B = foldl_range_imp (\<lambda> i _. do { 
     k \<leftarrow> Array.nth Bl i;
     if k + 2 \<le> nb then do { c \<leftarrow> Array.nth B (k + 2); Array.upd (k + 2) (c + 1) B; return () }
     else return () }) 0 n ()"

definition "part_prefix_imp nb B = foldl_range_imp (\<lambda> j _. do { 
     c \<leftarrow> Array.nth B j; d \<leftarrow> Array.nth B (j - 1); Array.upd j (c + d) B; return () }) 1 (Suc nb) ()"

definition "part_fill_imp n Bl B Oa = foldl_range_imp (\<lambda> i _. do { 
     k \<leftarrow> Array.nth Bl i; p \<leftarrow> Array.nth B (k + 1); 
     Array.upd (k + 1) (Suc p) B; Array.upd p i Oa; return () }) 0 n ()"

definition "part_handle_imp n nb Bl = do { 
   B \<leftarrow> Array.new (Suc nb) 0;
   part_count_imp n nb Bl B;
   part_prefix_imp nb B;
   Oa \<leftarrow> Array.new n 0;
   part_fill_imp n Bl B Oa;
   Sa \<leftarrow> Array.new n 0;
   copy_range_imp (\<lambda> i. do { k \<leftarrow> Array.nth Bl i; Array.nth B k }) n Sa;
   Ea \<leftarrow> Array.new n 0;
   copy_range_imp (\<lambda> i. do { k \<leftarrow> Array.nth Bl i; Array.nth B (Suc k) }) n Ea;
   return (Oa, Sa, Ea) }"

text \<open>The construction is the counting sort of the elements below \<open>n\<close>, enumerated by a counter,
  with their blocks as keys.\<close>

locale part_blocks =
  fixes n nb :: nat and bl :: "nat list"
  assumes bl_len: "length bl = n"
    and bl_bound: "i < n \<Longrightarrow> bl ! i < nb"
begin

sublocale cs: csr_buildup "range_next n" "range_seq n" "\<lambda> _. True" "\<lambda> i. bl ! i" nb 0
  by (intro csr_buildup.intro range_it.iterator_axioms csr_buildup_axioms.intro)
     (simp_all add: range_seq_def bl_bound)

lemma es: "cs.es = [0..<n]"
  by (simp add: cs.es_def range_seq_def)

lemma blk_bucket: "cs.blk k = bucket bl k"
  by (simp add: cs.blk_def es bucket_def bl_len)

lemma init_E: "cs.init_E n = replicate n 0"
  by (simp add: cs.init_E_def range_next_def)

lemma fold_fill_spec:
  "fold cs.fill_step [0..<n] (cs.prefix_sums (cs.count_B [0..<n]), replicate n 0) = (cs.B_spec, cs.E_spec)"
  using cs.csr_build_correct 
  by (simp add: cs.csr_build_def cs.count_edges cs.it_fold_s0 es init_E)

lemma count_rule:
  "<B \<mapsto>\<^sub>a replicate (Suc nb) 0 * Bl \<mapsto>\<^sub>a bl> part_count_imp n nb Bl B 
   <\<lambda> _. B \<mapsto>\<^sub>a cs.count_B [0..<n] * Bl \<mapsto>\<^sub>a bl>"
proof-
  have run: "<B \<mapsto>\<^sub>a fst a0 * \<up>(length (fst a0) = Suc nb) * Bl \<mapsto>\<^sub>a bl> 
               part_count_imp n nb Bl B 
             <\<lambda> r. B \<mapsto>\<^sub>a fst (foldl (\<lambda> a j. cs.count_step j a) a0 [0..<n]) * 
                   \<up>(length (fst (foldl (\<lambda> a j. cs.count_step j a) a0 [0..<n])) = Suc nb) * 
                   Bl \<mapsto>\<^sub>a bl>" for a0
    unfolding part_count_imp_def
    apply (rule foldl_range_imp_rule[where A = "\<lambda> a (_ :: unit). B \<mapsto>\<^sub>a fst a * \<up>(length (fst a) = Suc nb)" 
          and F = "Bl \<mapsto>\<^sub>a bl" and g = cs.count_step])
    subgoal for j a ai
      by (cases a) (sep_auto simp: cs.count_step_def Let_def bl_len bl_bound)
    done
  have fin: "foldl (\<lambda> a j. cs.count_step j a) (replicate (Suc nb) 0, 0) [0..<n] = (cs.count_B [0..<n], n)"
    using cs.fold_count_step[of "[0..<n]"] by (simp add: foldl_conv_fold)
  show ?thesis
    by (rule ht_cons_post[OF ht_cons_pre[OF _ run[of "(replicate (Suc nb) 0, 0)"]]]) 
       (sep_auto simp: fin[unfolded replicate_Suc])+
qed

lemma prefix_rule:
  "<B \<mapsto>\<^sub>a Bs * \<up>(length Bs = Suc nb)> part_prefix_imp nb B <\<lambda> _. B \<mapsto>\<^sub>a cs.prefix_sums Bs>"
proof-
  have run: "<B \<mapsto>\<^sub>a Bs * \<up>(length Bs = Suc nb) * emp> part_prefix_imp nb B 
             <\<lambda> r. B \<mapsto>\<^sub>a foldl (\<lambda> a j. cs.prefix_step j a) Bs [1..<Suc nb] * 
                   \<up>(length (foldl (\<lambda> a j. cs.prefix_step j a) Bs [1..<Suc nb]) = Suc nb) * emp>"
    unfolding part_prefix_imp_def
    by (rule foldl_range_imp_rule[where A = "\<lambda> Bs (_ :: unit). B \<mapsto>\<^sub>a Bs * \<up>(length Bs = Suc nb)" 
          and F = emp and g = cs.prefix_step]) 
       (sep_auto simp: cs.prefix_step_def)
  show ?thesis
    by (rule ht_cons_post[OF ht_cons_pre[OF _ run]]) 
       (sep_auto simp: cs.prefix_sums_def foldl_conv_fold)+
qed

lemma fill_rule:
  "<B \<mapsto>\<^sub>a cs.prefix_sums (cs.count_B [0..<n]) * Oa \<mapsto>\<^sub>a replicate n 0 * Bl \<mapsto>\<^sub>a bl> 
     part_fill_imp n Bl B Oa 
   <\<lambda> _. B \<mapsto>\<^sub>a cs.B_spec * Oa \<mapsto>\<^sub>a cs.E_spec * Bl \<mapsto>\<^sub>a bl>"
proof-
  define A where "A = (\<lambda> j a (_ :: unit). B \<mapsto>\<^sub>a fst a * Oa \<mapsto>\<^sub>a snd a * \<up>(cs.fill_invar [0..<j] a))"
  have step: "<A j a ai * Bl \<mapsto>\<^sub>a bl> 
     do { k \<leftarrow> Array.nth Bl j; p \<leftarrow> Array.nth B (k + 1); 
          Array.upd (k + 1) (Suc p) B; Array.upd p j Oa; return () }
     <\<lambda> r. A (Suc j) (cs.fill_step j a) r * Bl \<mapsto>\<^sub>a bl>" if j: "j < n" for j a ai
  proof(cases a)
    case (Pair Bs Es)
    have "[0..<n] = [0..<j] @ [j..<n]"
      using upt_add_eq_append[of 0 j "n - j"] j by simp
    then have split: "[0..<j] @ j # [Suc j..<n] = cs.es"
      using j upt_conv_Cons[of j n] by (simp add: es)
    show ?thesis
    proof(cases "cs.fill_invar [0..<j] (Bs, Es)")
      case inv: True
      have bnd: "Suc (bl ! j) < length Bs" "Bs ! Suc (bl ! j) < length Es"
        using cs.fill_step_bounds[OF split inv] by simp_all
      have inv': "cs.fill_invar [0..<Suc j] (cs.fill_step j (Bs, Es))"
        using cs.fill_step_invar[OF split inv] by simp
      have fs: "cs.fill_step j (Bs, Es) = 
                (Bs[Suc (bl ! j) := Suc (Bs ! Suc (bl ! j))], Es[Bs ! Suc (bl ! j) := j])"
        by (simp add: cs.fill_step_def Let_def)
      show ?thesis
        using bnd inv' j unfolding Pair fs A_def by (sep_auto simp: bl_len)
    next
      case False
      then show ?thesis
        unfolding Pair A_def by sep_auto
    qed
  qed
  have run: "<A 0 (cs.prefix_sums (cs.count_B [0..<n]), replicate n 0) () * Bl \<mapsto>\<^sub>a bl> 
               part_fill_imp n Bl B Oa 
             <\<lambda> r. A n (foldl (\<lambda> a j. cs.fill_step j a) 
                            (cs.prefix_sums (cs.count_B [0..<n]), replicate n 0) [0..<n]) r * 
                   Bl \<mapsto>\<^sub>a bl>"
    unfolding part_fill_imp_def 
    by (rule foldl_range_imp_idx_rule[where A = A and F = "Bl \<mapsto>\<^sub>a bl" and g = cs.fill_step]) 
       (rule step, simp_all)
  have init: "cs.fill_invar [] (cs.prefix_sums (cs.count_B [0..<n]), replicate n 0)"
    using cs.fill_invar_init by (simp add: es init_E)
  show ?thesis
    by (rule ht_cons_post[OF ht_cons_pre[OF _ run]]) 
       (sep_auto simp: A_def init foldl_conv_fold fold_fill_spec)+
qed

lemma bounds_rule:
  "<B \<mapsto>\<^sub>a cs.B_spec * Bl \<mapsto>\<^sub>a bl * Sa \<mapsto>\<^sub>a replicate n 0> 
     copy_range_imp (\<lambda> i. do { k \<leftarrow> Array.nth Bl i; Array.nth B (f k) }) n Sa
   <\<lambda> _. Sa \<mapsto>\<^sub>a map (\<lambda> i. cs.B_spec ! f (bl ! i)) [0..<n] * (B \<mapsto>\<^sub>a cs.B_spec * Bl \<mapsto>\<^sub>a bl)>"
  if "\<And> k. k < nb \<Longrightarrow> f k \<le> nb"
proof-
  have r: "<B \<mapsto>\<^sub>a cs.B_spec * Bl \<mapsto>\<^sub>a bl> do { k \<leftarrow> Array.nth Bl i; Array.nth B (f k) }
           <\<lambda> r. (B \<mapsto>\<^sub>a cs.B_spec * Bl \<mapsto>\<^sub>a bl) * \<up>(r = cs.B_spec ! f (bl ! i))>" if "i < n" for i
    using that bl_bound[OF that] \<open>\<And> k. k < nb \<Longrightarrow> f k \<le> nb\<close>[OF bl_bound[OF that]]
    by (sep_auto simp: bl_len cs.length_B_spec)
  show ?thesis
    by (rule ht_cons_pre[OF _ copy_range_imp_rule[OF r]]) sep_auto
qed

lemma handle_ok:
  "part_hnd_ok n bl cs.E_spec (map (\<lambda> i. cs.B_spec ! (bl ! i)) [0..<n]) 
                              (map (\<lambda> i. cs.B_spec ! Suc (bl ! i)) [0..<n])"
  unfolding part_hnd_ok_def
proof(intro conjI allI impI)
  fix x
  assume x: "x < n"
  have k: "bl ! x < nb"
    by (rule bl_bound[OF x])
  show "map (\<lambda> i. cs.B_spec ! (bl ! i)) [0..<n] ! x \<le> map (\<lambda> i. cs.B_spec ! Suc (bl ! i)) [0..<n] ! x"
    using x k cs.start_mono[of "bl ! x" "Suc (bl ! x)"] by (simp add: cs.B_spec_nth)
  show "map (\<lambda> i. cs.B_spec ! Suc (bl ! i)) [0..<n] ! x \<le> length cs.E_spec"
    using x k cs.start_mono[of "Suc (bl ! x)" nb] by (simp add: cs.B_spec_nth cs.start_n cs.length_E_spec)
  show "part_pts bl x = take (map (\<lambda> i. cs.B_spec ! Suc (bl ! i)) [0..<n] ! x - 
                              map (\<lambda> i. cs.B_spec ! (bl ! i)) [0..<n] ! x)
                             (drop (map (\<lambda> i. cs.B_spec ! (bl ! i)) [0..<n] ! x) cs.E_spec)"
    using x cs.csr_block[OF k] by (simp add: part_pts_def blk_bucket)
qed simp_all

lemma handle_rule:
  "<Bl \<mapsto>\<^sub>a bl> part_handle_imp n nb Bl <\<lambda> H. Bl \<mapsto>\<^sub>a bl * part_pst n bl H * true>"
proof-
  note b1 = bounds_rule[where f = "\<lambda> k. k", OF less_imp_le]
  note b2 = bounds_rule[where f = Suc, OF Suc_leI]
  show ?thesis
    unfolding part_handle_imp_def
    by (sep_auto heap: count_rule prefix_rule fill_rule b1 b2 simp: part_pst_def handle_ok)
qed

end

lemma part_handle_rule:
  "<blocks_assn n nb bl Bl> part_handle_imp n nb Bl <\<lambda> H. blocks_assn n nb bl Bl * part_pst n bl H * true>"
proof-
  have "length bl = n \<and> (\<forall> i < n. bl ! i < nb) \<Longrightarrow> 
        <Bl \<mapsto>\<^sub>a bl> part_handle_imp n nb Bl <\<lambda> H. Bl \<mapsto>\<^sub>a bl * part_pst n bl H * true>"
    by (intro part_blocks.handle_rule part_blocks.intro) simp_all
  then show ?thesis
    unfolding blocks_assn_def by sep_auto
qed

lemma part_hnd_len: "\<lbrakk>part_hnd_ok n bl os ss es; x < n\<rbrakk> \<Longrightarrow> length (part_pts bl x) = es ! x - ss ! x"
  unfolding part_hnd_ok_def by auto

lemma part_hnd_nth: 
  "\<lbrakk>part_hnd_ok n bl os ss es; x < n; k < es ! x - ss ! x\<rbrakk> \<Longrightarrow> 
   part_pts bl x ! k = os ! (ss ! x + k) \<and> ss ! x + k < length os"
  unfolding part_hnd_ok_def by auto

lemma part_hnd_lens: "part_hnd_ok n bl os ss es \<Longrightarrow> length ss = n \<and> length es = n"
  unfolding part_hnd_ok_def by simp

lemma part_npts_rule:
  "<part_pst n bl H * \<up>(x < n)> part_npts_imp H x <\<lambda> r. part_pst n bl H * \<up>(r = length (part_pts bl x))>"
  by (cases H rule: prod_cases3) 
     (sep_auto simp: part_pst_def part_npts_imp_def part_hnd_len dest: part_hnd_lens)

lemma part_pt_rule:
  "<part_pst n bl H * \<up>(x < n \<and> k < length (part_pts bl x))> part_pt_imp H x k 
   <\<lambda> r. part_pst n bl H * \<up>(r = part_pts bl x ! k)>"
  by (cases H rule: prod_cases3) 
     (sep_auto simp: part_pst_def part_pt_imp_def part_hnd_len part_hnd_nth dest: part_hnd_lens)

lemma part_pts_sorted: "sorted_wrt (<) (part_pts bl x)"
  unfolding part_pts_def bucket_def by (simp add: sorted_wrt_filter)

lemma part_pts_bound: "y \<in> set (part_pts bl x) \<Longrightarrow> y < length bl"
  unfolding part_pts_def bucket_def by simp

lemma part_pts_cover: 
  "\<lbrakk>x < length bl; y < length bl; bl ! x = bl ! y\<rbrakk> \<Longrightarrow> y \<in> set (part_pts bl x) \<and> x \<in> set (part_pts bl y)"
  unfolding part_pts_def bucket_def by simp

subsection \<open>Solutions Counted in Two Partitions\<close>

text \<open>A solution for two partition oracles: the Boolean array of the solution, the two arrays
  of counters and the two arrays of blocks. Insertion and deletion keep both counters
  up to date.\<close>

type_synonym bm_sol = "bool array \<times> nat array \<times> nat array \<times> nat array \<times> nat array"

definition bm_memb :: "nat \<Rightarrow> bm_sol \<Rightarrow> bool Heap" where
  "bm_memb x Si = (case Si of (Xi, C1, C2, Bl, Br) \<Rightarrow> Array.nth Xi x)"

definition bm_ins :: "nat \<Rightarrow> bm_sol \<Rightarrow> unit Heap" where
  "bm_ins x Si = (case Si of (Xi, C1, C2, Bl, Br) \<Rightarrow> do {
     b \<leftarrow> Array.nth Xi x;
     if b then return ()
     else do { Array.upd x True Xi; part_cnt_ins Bl C1 x; part_cnt_ins Br C2 x } })"

definition bm_del :: "nat \<Rightarrow> bm_sol \<Rightarrow> unit Heap" where
  "bm_del x Si = (case Si of (Xi, C1, C2, Bl, Br) \<Rightarrow> do {
     b \<leftarrow> Array.nth Xi x;
     if b then do { Array.upd x False Xi; part_cnt_del Bl C1 x; part_cnt_del Br C2 x }
     else return () })"

fun bm_sol_assn :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat set \<Rightarrow> bm_sol \<Rightarrow> assn" where
  "bm_sol_assn m nb bl br X (Xi, C1, C2, Bl, Br) = 
     xset_assn m X Xi * cnt_assn nb bl X C1 * cnt_assn nb br X C2 * 
     blocks_assn m nb bl Bl * blocks_assn m nb br Br"

lemma bm_memb_rule:
  "<bm_sol_assn m nb bl br X Si * \<up>(x < m)> bm_memb x Si 
   <\<lambda> r. bm_sol_assn m nb bl br X Si * \<up>(r = (x \<in> X))>"
  by (cases Si rule: prod_cases5) (sep_auto simp: bm_memb_def heap: xset_memb_rule)

lemma bm_ins_rule:
  "<bm_sol_assn m nb bl br X Si * \<up>(x < m)> bm_ins x Si 
   <\<lambda> _. bm_sol_assn m nb bl br (Set.insert x X) Si>"
  by (cases Si rule: prod_cases5) 
     (sep_auto simp: bm_ins_def insert_absorb heap: xset_memb_rule xset_upd_rule part_cnt_ins_rule)

lemma bm_del_rule:
  "<bm_sol_assn m nb bl br X Si * \<up>(x < m)> bm_del x Si 
   <\<lambda> _. bm_sol_assn m nb bl br (X - {x}) Si>"
proof-
  have "x \<notin> X \<Longrightarrow> X - {x} = X"
    by blast
  then show ?thesis
    by (cases Si rule: prod_cases5) 
       (sep_auto simp: bm_del_def heap: xset_memb_rule xset_upd_rule part_cnt_del_rule)
qed

end
