theory Partition_Oracle_Imp
  imports Partition_Oracle Exchange_Oracles_Imp Directed_Set_Graphs.CSR_Buildup_Imperative
begin

provenance ai


section \<open>The Unit Partition Oracle in Imperative HOL\<close>

text \<open>Elements are the nats below \<open>n\<close>, blocks the nats below \<open>nb\<close>, and the block of each
  element is stored in an array (the static data of the oracle). The oracle data of a solution
  is an array counting, for every block, the elements of the solution in it. Insertion and
  deletion of an element update one counter; insertion queries read one counter, and exchange
  queries compare two blocks. All take constant time. They refine the functional oracle of
  \<open>Partition_Oracle\<close> with sets as solutions and as block sets.\<close>

subsection \<open>Code\<close>

definition \<^marker>\<open>provenance ai_human\<close> part_cnt_ins :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "part_cnt_ins Bl C i = do { b \<leftarrow> Array.nth Bl i; c \<leftarrow> Array.nth C b; Array.upd b (Suc c) C;
    return () }"

definition \<^marker>\<open>provenance ai_human\<close> part_cnt_del :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "part_cnt_del Bl C i = do { b \<leftarrow> Array.nth Bl i; c \<leftarrow> Array.nth C b; Array.upd b (c - 1) C;
    return () }"

definition \<^marker>\<open>provenance ai_human\<close> part_ins_imp :: "nat array \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "part_ins_imp Bl C y = do { b \<leftarrow> Array.nth Bl y; c \<leftarrow> Array.nth C b; return (c = 0) }"

definition \<^marker>\<open>provenance ai_human\<close> part_exch_imp :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where
  "part_exch_imp Bl x y = do { a \<leftarrow> Array.nth Bl x; b \<leftarrow> Array.nth Bl y; return (a = b) }"

subsection \<open>Correctness\<close>

definition "blocks_assn n nb bl Bl = Bl \<mapsto>\<^sub>a bl * \<up>(length bl = n \<and> (\<forall> i < n. bl ! i <
    nb))"

definition "bcount bl X b = card {i \<in> X. bl ! i = b}"

definition "cnt_assn nb bl X C = C \<mapsto>\<^sub>a map (bcount bl X) [0..<nb] * \<up>(finite X)"

lemma bcount_insert:
  "\<lbrakk>finite X; i \<notin> X\<rbrakk> \<Longrightarrow>
   bcount bl (insert i X) b = (if bl ! i = b then Suc (bcount bl X b) else bcount bl X b)"
  by (simp only: bcount_def Collect_conj_eq Collect_mem_eq) (simp add: Int_insert_left)

lemma bcount_delete:
  "\<lbrakk>finite X; i \<in> X\<rbrakk> \<Longrightarrow>
   bcount bl (X - {i}) b = (if bl ! i = b then bcount bl X b - 1 else bcount bl X b)"
  using bcount_insert[of "X - {i}" i bl b]
  by (auto simp: insert_absorb split: if_splits)

lemma bcount_zero: "finite X \<Longrightarrow> (bcount bl X b = 0) = (b \<notin> (\<lambda> i. bl ! i) ` X)"
  by (auto simp: bcount_def)

lemma \<^marker>\<open>provenance ai_human\<close> cnt_assn_new: "<emp> Array.new nb 0 <cnt_assn nb bl {}>"
  unfolding cnt_assn_def bcount_def
  by (sep_auto simp: map_replicate_const)

lemma \<^marker>\<open>provenance ai_human\<close> part_cnt_ins_rule:
  "<cnt_assn nb bl X C * blocks_assn n nb bl Bl * \<up>(i < n \<and> i \<notin> X)> part_cnt_ins Bl C i
   <\<lambda> _. cnt_assn nb bl (insert i X) C * blocks_assn n nb bl Bl>"
proof-
  have upd: "(map (bcount bl X) [0..<nb])[bl ! i := Suc (bcount bl X (bl ! i))] =
             map (bcount bl (insert i X)) [0..<nb]"
    if "finite X" "i \<notin> X" "bl ! i < nb"
    by (rule map_bcount_upd) (simp_all add: that bcount_insert[OF that(1,2)])
  show ?thesis
    unfolding part_cnt_ins_def cnt_assn_def blocks_assn_def
    by (sep_auto simp: upd)
qed

lemma \<^marker>\<open>provenance ai_human\<close> part_cnt_del_rule:
  "<cnt_assn nb bl X C * blocks_assn n nb bl Bl * \<up>(i < n \<and> i \<in> X)> part_cnt_del Bl C i
   <\<lambda> _. cnt_assn nb bl (X - {i}) C * blocks_assn n nb bl Bl>"
proof-
  have upd: "(map (bcount bl X) [0..<nb])[bl ! i := bcount bl X (bl ! i) - Suc 0] =
             map (bcount bl (X - {i})) [0..<nb]"
    if "finite X" "i \<in> X" "bl ! i < nb"
    by (rule map_bcount_upd) (simp_all add: that bcount_delete[OF that(1,2)])
  show ?thesis
    unfolding part_cnt_del_def cnt_assn_def blocks_assn_def
    by (sep_auto simp: upd)
qed

lemma \<^marker>\<open>provenance ai_human\<close> part_ins_imp_rule:
  "<cnt_assn nb bl X C * blocks_assn n nb bl Bl * \<up>(y < n)> part_ins_imp Bl C y
   <\<lambda> r. cnt_assn nb bl X C * blocks_assn n nb bl Bl *
         \<up>(finite X \<and> r = (bl ! y \<notin> (\<lambda> i. bl ! i) ` X))>"
  unfolding part_ins_imp_def cnt_assn_def blocks_assn_def
  by (sep_auto simp: bcount_zero)

lemma \<^marker>\<open>provenance ai_human\<close> part_exch_imp_rule:
  "<blocks_assn n nb bl Bl * \<up>(x < n \<and> y < n)> part_exch_imp Bl x y
   <\<lambda> r. blocks_assn n nb bl Bl * \<up>(r = (bl ! x = bl ! y))>"
  unfolding part_exch_imp_def blocks_assn_def
  by sep_auto

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
     \<exists>\<^sub>A os ss es. Oa \<mapsto>\<^sub>a os * Sa \<mapsto>\<^sub>a ss * Ea \<mapsto>\<^sub>a es *
       \<up>(part_hnd_ok n bl os ss es))"

definition \<^marker>\<open>provenance ai_human\<close> part_npts_imp :: "part_hnd \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "part_npts_imp H x = (case H of (Oa, Sa, Ea) \<Rightarrow> do {
     s \<leftarrow> Array.nth Sa x; e \<leftarrow> Array.nth Ea x; return (e - s) })"

definition \<^marker>\<open>provenance ai_human\<close> part_pt_imp :: "part_hnd \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "part_pt_imp H x k = (case H of (Oa, Sa, Ea) \<Rightarrow> do { s \<leftarrow> Array.nth Sa x; Array.nth Oa (s + k)
    })"

text \<open>The block boundaries and the element array are built by the CSR buildup of the library,
  with a counter over the elements below \<open>n\<close> as iterator, the block of an element as key and
  the element itself as value.\<close>

global_interpretation part_csr: imp_csr_buildup_code nb "\<lambda>_ i. return (i < n)" "\<lambda>_ i. return i"
    "\<lambda>_ i. return (Suc i)" Array.nth "\<lambda>_ i. return i"
  for n nb
  defines part_csr_build = part_csr.csr_build_imp
    and part_csr_count = part_csr.count_imp
    and part_csr_prefix_sums = part_csr.prefix_imp
    and part_csr_init = part_csr.init_E_imp
    and part_csr_fill = part_csr.fill_imp
  done

declare part_csr.count_imp.simps[code] part_csr.prefix_imp.simps[code] part_csr.fill_imp.simps[code]

definition "part_handle_imp n nb Bl = do {
   (B, Oa) \<leftarrow> part_csr_build n nb Bl 0;
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

sublocale cs: imp_csr_buildup "range_next n" "range_seq n" "\<lambda> _. True" "\<lambda> i. bl ! i" nb 0
    "\<lambda>_ i. return (i < n)" "\<lambda>_ i. return i" "\<lambda>_ i. return (Suc i)" Array.nth "\<lambda>_ i.
      return i" id
    "\<lambda>s si. si = s" "\<lambda>Bl. Bl \<mapsto>\<^sub>a bl"
  by (intro imp_csr_buildup.intro csr_buildup.intro range_it.iterator_axioms csr_buildup_axioms.intro
            imp_csr_buildup_axioms.intro)
     (sep_auto simp: range_seq_def range_next_def bl_bound bl_len split: if_splits)+

lemma es: "cs.es = [0..<n]"
  by (simp add: cs.es_def range_seq_def)

lemma blk_bucket: "cs.blk k = bucket bl k"
  by (simp add: cs.blk_def es bucket_def bl_len)

lemma \<^marker>\<open>provenance ai_human\<close> bounds_rule:
  "<B \<mapsto>\<^sub>a cs.B_spec * Bl \<mapsto>\<^sub>a bl * Sa \<mapsto>\<^sub>a replicate n 0>
     copy_range_imp (\<lambda> i. do { k \<leftarrow> Array.nth Bl i; Array.nth B (f k) }) n Sa
   <\<lambda> _. Sa \<mapsto>\<^sub>a map (\<lambda> i. cs.B_spec ! f (bl ! i)) [0..<n] * (B \<mapsto>\<^sub>a
     cs.B_spec * Bl \<mapsto>\<^sub>a bl)>"
  if "\<And> k. k < nb \<Longrightarrow> f k \<le> nb"
proof-
  note bounds = that
  have r: "<B \<mapsto>\<^sub>a cs.B_spec * Bl \<mapsto>\<^sub>a bl> do { k \<leftarrow> Array.nth Bl i; Array.nth B
    (f k) }
           <\<lambda> r. (B \<mapsto>\<^sub>a cs.B_spec * Bl \<mapsto>\<^sub>a bl) * \<up>(r = cs.B_spec ! f (bl !
             i))>" if "i < n" for i
    using that bl_bound[OF that] bounds[OF bl_bound[OF that]]
    by (sep_auto simp: bl_len cs.length_B_spec)
  show ?thesis
    by (rule ht_cons_pre[OF _ copy_range_imp_rule[OF r]]) sep_auto
qed

lemma block_ok:
  "k < nb \<Longrightarrow>
   cs.B_spec ! k \<le> cs.B_spec ! Suc k \<and> cs.B_spec ! Suc k \<le> length cs.E_spec \<and>
   take (cs.B_spec ! Suc k - cs.B_spec ! k) (drop (cs.B_spec ! k) cs.E_spec) = bucket bl k"
  using cs.start_mono[of k "Suc k"] cs.start_mono[of "Suc k" nb] cs.csr_block[of k]
  by (auto simp: cs.B_spec_nth cs.start_n cs.length_E_spec blk_bucket)

lemma handle_ok:
  "part_hnd_ok n bl cs.E_spec (map (\<lambda> i. cs.B_spec ! (bl ! i)) [0..<n])
                              (map (\<lambda> i. cs.B_spec ! Suc (bl ! i)) [0..<n])"
  by (auto simp: part_hnd_ok_def part_pts_def dest!: bl_bound block_ok)

lemma \<^marker>\<open>provenance ai_human\<close> handle_rule:
  "<Bl \<mapsto>\<^sub>a bl> part_handle_imp n nb Bl <\<lambda> H. Bl \<mapsto>\<^sub>a bl * part_pst n bl H * true>"
proof-
  note b1 = bounds_rule[where f = "\<lambda> k. k", OF less_imp_le]
  note b2 = bounds_rule[where f = Suc, OF Suc_leI]
  note build = cs.csr_build_imp_rule[of Bl 0, simplified]
  show ?thesis
    unfolding part_handle_imp_def part_csr_build_def
    by (sep_auto heap: build b1 b2 simp: part_pst_def handle_ok)
qed

end

lemma \<^marker>\<open>provenance ai_human\<close> part_handle_rule:
  "<blocks_assn n nb bl Bl> part_handle_imp n nb Bl <\<lambda> H. blocks_assn n nb bl Bl * part_pst n bl H * true>"
proof-
  have "length bl = n \<and> (\<forall> i < n. bl ! i < nb) \<Longrightarrow>
        <Bl \<mapsto>\<^sub>a bl> part_handle_imp n nb Bl <\<lambda> H. Bl \<mapsto>\<^sub>a bl * part_pst n bl H *
          true>"
    by (intro part_blocks.handle_rule part_blocks.intro) simp_all
  then show ?thesis
    unfolding blocks_assn_def
    by sep_auto
qed

lemma part_hnd_len: "\<lbrakk>part_hnd_ok n bl os ss es; x < n\<rbrakk> \<Longrightarrow> length (part_pts bl x) = es
    ! x - ss ! x"
  by (auto simp: part_hnd_ok_def)

lemma part_hnd_nth:
  "\<lbrakk>part_hnd_ok n bl os ss es; x < n; k < es ! x - ss ! x\<rbrakk> \<Longrightarrow>
   part_pts bl x ! k = os ! (ss ! x + k) \<and> ss ! x + k < length os"
  by (auto simp: part_hnd_ok_def)

lemma part_hnd_lens: "part_hnd_ok n bl os ss es \<Longrightarrow> length ss = n \<and> length es = n"
  by (simp add: part_hnd_ok_def)

lemma \<^marker>\<open>provenance ai_human\<close> part_npts_rule:
  "<part_pst n bl H * \<up>(x < n)> part_npts_imp H x <\<lambda> r. part_pst n bl H * \<up>(r = length (part_pts bl
    x))>"
  by (cases H rule: prod_cases3)
     (sep_auto simp: part_pst_def part_npts_imp_def part_hnd_len dest: part_hnd_lens)

lemma \<^marker>\<open>provenance ai_human\<close> part_pt_rule:
  "<part_pst n bl H * \<up>(x < n \<and> k < length (part_pts bl x))> part_pt_imp H x k
   <\<lambda> r. part_pst n bl H * \<up>(r = part_pts bl x ! k)>"
  by (cases H rule: prod_cases3)
     (sep_auto simp: part_pst_def part_pt_imp_def part_hnd_len part_hnd_nth dest: part_hnd_lens)

lemma part_pts_sorted: "sorted_wrt (<) (part_pts bl x)"
  by (simp add: part_pts_def bucket_def sorted_wrt_filter)

lemma part_pts_bound: "y \<in> set (part_pts bl x) \<Longrightarrow> y < length bl"
  by (simp add: part_pts_def bucket_def)

lemma part_pts_cover:
  "\<lbrakk>x < length bl; y < length bl; bl ! x = bl ! y\<rbrakk> \<Longrightarrow> y \<in> set (part_pts bl x)
    \<and> x \<in> set (part_pts bl y)"
  by (simp add: part_pts_def bucket_def)

subsection \<open>Solutions Counted in Two Partitions\<close>

text \<open>A solution for two partition oracles: the Boolean array of the solution, the two arrays
  of counters and the two arrays of blocks. Insertion and deletion keep both counters
  up to date.\<close>

type_synonym bm_sol = "bool array \<times> nat array \<times> nat array \<times> nat array \<times> nat array"

definition \<^marker>\<open>provenance ai_human\<close> bm_memb :: "nat \<Rightarrow> bm_sol \<Rightarrow> bool Heap" where
  "bm_memb x Si = (case Si of (Xi, C1, C2, Bl, Br) \<Rightarrow> Array.nth Xi x)"

definition \<^marker>\<open>provenance ai_human\<close> bm_ins :: "nat \<Rightarrow> bm_sol \<Rightarrow> unit Heap" where
  "bm_ins x Si = (case Si of (Xi, C1, C2, Bl, Br) \<Rightarrow> do {
     b \<leftarrow> Array.nth Xi x;
     if b then return ()
     else do { Array.upd x True Xi; part_cnt_ins Bl C1 x; part_cnt_ins Br C2 x } })"

definition \<^marker>\<open>provenance ai_human\<close> bm_del :: "nat \<Rightarrow> bm_sol \<Rightarrow> unit Heap" where
  "bm_del x Si = (case Si of (Xi, C1, C2, Bl, Br) \<Rightarrow> do {
     b \<leftarrow> Array.nth Xi x;
     if b then do { Array.upd x False Xi; part_cnt_del Bl C1 x; part_cnt_del Br C2 x }
     else return () })"

fun bm_sol_assn :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat set
    \<Rightarrow> bm_sol \<Rightarrow> assn" where
  "bm_sol_assn m nb bl br X (Xi, C1, C2, Bl, Br) =
     bool_array_set_assn m X Xi * cnt_assn nb bl X C1 * cnt_assn nb br X C2 *
     blocks_assn m nb bl Bl * blocks_assn m nb br Br"

lemma \<^marker>\<open>provenance ai_human\<close> bm_memb_rule:
  "<bm_sol_assn m nb bl br X Si * \<up>(x < m)> bm_memb x Si
   <\<lambda> r. bm_sol_assn m nb bl br X Si * \<up>(r = (x \<in> X))>"
  by (cases Si rule: prod_cases5) (sep_auto simp: bm_memb_def heap: bool_array_set_memb_rule)

lemma \<^marker>\<open>provenance ai_human\<close> bm_ins_rule:
  "<bm_sol_assn m nb bl br X Si * \<up>(x < m)> bm_ins x Si
   <\<lambda> _. bm_sol_assn m nb bl br (Set.insert x X) Si>"
  by (cases Si rule: prod_cases5)
     (sep_auto simp: bm_ins_def insert_absorb heap: bool_array_set_memb_rule bool_array_set_upd_rule part_cnt_ins_rule)

lemma \<^marker>\<open>provenance ai_human\<close> bm_del_rule:
  "<bm_sol_assn m nb bl br X Si * \<up>(x < m)> bm_del x Si
   <\<lambda> _. bm_sol_assn m nb bl br (X - {x}) Si>"
proof-
  have "x \<notin> X \<Longrightarrow> X - {x} = X"
    by blast
  then show ?thesis
    by (cases Si rule: prod_cases5)
       (sep_auto simp: bm_del_def heap: bool_array_set_memb_rule bool_array_set_upd_rule part_cnt_del_rule)
qed

end
