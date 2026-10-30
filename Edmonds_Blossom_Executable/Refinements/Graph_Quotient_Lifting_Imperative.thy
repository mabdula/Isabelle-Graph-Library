theory Graph_Quotient_Lifting_Imperative
  imports
    Find_Aug_Path_Subprocedures_Imperative
    Blossom_Executable.Graph_Quotient_Lifting
begin

provenance ai

section \<open>Imperative refinement of the lifting of a path through a contraction\<close>

text \<open>The imperative program mirrors @{const refine}. Paths and cycles are stored in arrays. The
  adjacency test of the graph and the lookup of the partner of a vertex are heap operations,
  passed as arguments; their Hoare triples, stated against the functional adjacency test and the
  functional partner lookup inside an arbitrary frame, are premises of the correctness lemmas.
  The lifted path is a new array.\<close>

subsection \<open>The first position of an element with a property\<close>

fun first_pos :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "first_pos P [] = 0"
| "first_pos P (x # xs) = (if P x then 0 else Suc (first_pos P xs))"

lemma first_pos_le: "first_pos P xs \<le> length xs"
  by (induction xs) auto

lemma first_pos_less_iff: "first_pos P xs < length xs \<longleftrightarrow> (\<exists>x \<in> set xs. P x)"
  by (induction xs) auto

lemma first_pos_nth: "first_pos P xs < length xs \<Longrightarrow> P (xs ! first_pos P xs)"
  by (induction xs) auto

lemma first_pos_before: "j < first_pos P xs \<Longrightarrow> \<not> P (xs ! j)"
  by (induction xs arbitrary: j) (auto simp: nth_Cons split: nat.splits if_splits)

lemma find_first_pos:
  "find P xs = (if first_pos P xs < length xs then Some (xs ! first_pos P xs) else None)"
  by (induction xs) auto

lemma find_pfx_first_pos: "find_pfx P xs = take (Suc (first_pos P xs)) xs"
  by (induction xs) auto

lemma pref_suf_first_pos:
  "pref_suf pref u xs =
     (pref @ take (first_pos (\<lambda>y. y = u) xs) xs, drop (Suc (first_pos (\<lambda>y. y = u) xs)) xs)"
  by (induction xs arbitrary: pref) auto

lemma first_pos_member: "first_pos (\<lambda>y. y = x) xs < length xs \<longleftrightarrow> x \<in> set xs"
  by (auto simp: first_pos_less_iff)

text \<open>The search for the first position, with a test that is a heap operation.\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) first_pos_imp ::
  "('a \<Rightarrow> bool Heap) \<Rightarrow> 'a::heap array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "first_pos_imp t A n i =
     (if i < n then do { x \<leftarrow> Array.nth A i;
                         b \<leftarrow> t x;
                         if b then return i else first_pos_imp t A n (Suc i) }
      else return i)"

lemma first_pos_imp_rule:
  assumes "i \<le> length xs"
    and test: "\<And>x. x \<in> set xs \<Longrightarrow> <R> t x <\<lambda>r. R * \<up>(r = P x)>"
  shows "<A \<mapsto>\<^sub>a xs * R> first_pos_imp t A (length xs) i
         <\<lambda>r. A \<mapsto>\<^sub>a xs * R * \<up>(r = i + first_pos P (drop i xs))>"
  using assms(1)
proof(induction "length xs - i" arbitrary: i rule: less_induct)
  case less
  show ?case
  proof(cases "i < length xs")
    case True
    have d: "drop i xs = xs ! i # drop (Suc i) xs"
      using True by (simp add: Cons_nth_drop_Suc)
    have IH: "<A \<mapsto>\<^sub>a xs * R> first_pos_imp t A (length xs) (Suc i)
              <\<lambda>r. A \<mapsto>\<^sub>a xs * R * \<up>(r = Suc i + first_pos P (drop (Suc i) xs))>"
      using True by (intro less.hyps) auto
    show ?thesis
      using True
      by (subst first_pos_imp.simps) (sep_auto heap: test IH simp: d)
  next
    case False
    thus ?thesis
      using less.prems by (subst first_pos_imp.simps) sep_auto
  qed
qed

lemma first_pos_imp_eq_rule:
  "<A \<mapsto>\<^sub>a xs> first_pos_imp (\<lambda>y. return (P y)) A (length xs) 0
   <\<lambda>r. A \<mapsto>\<^sub>a xs * \<up>(r = first_pos P xs)>"
proof-
  have T: "<emp> return (P x) <\<lambda>r. emp * \<up>(r = P x)>" for x
    by sep_auto
  show ?thesis
    using first_pos_imp_rule[of 0 xs emp "\<lambda>y. return (P y)" P A, OF _ T] by simp
qed

subsection \<open>Prefixes and reversals of arrays\<close>

definition \<^marker>\<open>provenance ai_human\<close> "prefix_imp A k =
  do { x \<leftarrow> Array.nth A 0;
       B \<leftarrow> Array.new k x;
       copy_fwd_imp A 0 k B 0;
       return B }"

lemma prefix_imp_rule:
  "\<lbrakk>xs \<noteq> []; k \<le> length xs\<rbrakk> \<Longrightarrow>
   <A \<mapsto>\<^sub>a xs> prefix_imp A k <\<lambda>B. A \<mapsto>\<^sub>a xs * B \<mapsto>\<^sub>a take k xs>"
  unfolding prefix_imp_def
  by (sep_auto heap: copy_fwd_imp_rule simp: put_list_full)

definition \<^marker>\<open>provenance ai_human\<close> "rev_copy_imp A =
  do { n \<leftarrow> Array.len A;
       x \<leftarrow> Array.nth A 0;
       B \<leftarrow> Array.new n x;
       copy_rev_imp A n n B 0;
       return B }"

lemma rev_copy_imp_rule:
  "xs \<noteq> [] \<Longrightarrow> <A \<mapsto>\<^sub>a xs> rev_copy_imp A <\<lambda>B. A \<mapsto>\<^sub>a xs * B \<mapsto>\<^sub>a rev xs>"
  unfolding rev_copy_imp_def
  by (sep_auto heap: copy_rev_imp_rule simp: put_list_full)

subsection \<open>The path from a vertex of the stem to the cycle\<close>

lemma choose_con_vert_first_pos:
  "C \<noteq> [] \<Longrightarrow> choose_con_vert adj C v =
     (if first_pos (adj v) C < length C then C ! first_pos (adj v) C else C ! 0)"
  by (simp add: choose_con_vert_def find_first_pos hd_conv_nth)

lemma choose_con_vert_in: "C \<noteq> [] \<Longrightarrow> choose_con_vert adj C v \<in> set C"
  by (simp add: choose_con_vert_first_pos)

lemma last_edge_matched_take:
  assumes "i < length C"
  shows "last_edge_matched mate (take (Suc i) C) =
    (if 0 < i then mate (C ! (i - 1)) = Some (C ! i) else True)"
proof(cases i)
  case 0
  then show ?thesis
    using assms by (cases C) (simp_all add: last_edge_matched_def)
next
  case (Suc j)
  have "rev (take (Suc i) C) = C ! i # C ! j # rev (take j C)"
    using assms Suc by (simp add: take_Suc_conv_app_nth)
  then show ?thesis
    using Suc by (simp add: last_edge_matched_def)
qed

lemma stem2vert_path_first_pos:
  "stem2vert_path adj mate C v =
    (let c = choose_con_vert adj C v; i = first_pos (\<lambda>y. c = y) C in
     if last_edge_matched mate (take (Suc i) C) then take (Suc i) C
     else take (Suc (first_pos (\<lambda>y. c = y) (rev C))) (rev C))"
  by (simp add: stem2vert_path_def find_pfx_first_pos Let_def)

text \<open>The premises on the heap operations. The adjacency test and the partner lookup are
  correct for vertices of a set @{term U} that contains the path and the cycle.\<close>

definition \<^marker>\<open>provenance ai_human\<close> "adj_ok R adj_t adj U \<longleftrightarrow>
  (\<forall>v w. v \<in> U \<longrightarrow> w \<in> U \<longrightarrow> <R> adj_t v w <\<lambda>r. R * \<up>(r = adj v w)>)"

definition \<^marker>\<open>provenance ai_human\<close> "mate_ok R mate_t mate U \<longleftrightarrow>
  (\<forall>x. x \<in> U \<longrightarrow> <R> mate_t x <\<lambda>r. R * \<up>(r = mate x)>)"

definition \<^marker>\<open>provenance ai_human\<close> "choose_con_vert_imp adj_t Ct v =
  do { n \<leftarrow> Array.len Ct;
       j \<leftarrow> first_pos_imp (adj_t v) Ct n 0;
       if j < n then Array.nth Ct j else Array.nth Ct 0 }"

lemma choose_con_vert_imp_rule:
  assumes "C \<noteq> []" "v \<in> U" "set C \<subseteq> U" "adj_ok R adj_t adj U"
  shows "<R * Ct \<mapsto>\<^sub>a C> choose_con_vert_imp adj_t Ct v
         <\<lambda>c. R * Ct \<mapsto>\<^sub>a C * \<up>(c = choose_con_vert adj C v)>"
proof-
  have T: "<R> adj_t v x <\<lambda>r. R * \<up>(r = adj v x)>" if "x \<in> set C" for x
    using assms(2-4) that by (auto simp: adj_ok_def)
  have ADJ: "<Ct \<mapsto>\<^sub>a C * R> first_pos_imp (adj_t v) Ct (length C) 0
             <\<lambda>r. Ct \<mapsto>\<^sub>a C * R * \<up>(r = first_pos (adj v) C)>"
    using first_pos_imp_rule[of 0 C R "adj_t v" "adj v" Ct, OF _ T] by simp
  show ?thesis
    using assms(1)
    by (sep_auto heap: ADJ simp: choose_con_vert_imp_def choose_con_vert_first_pos)
qed

definition \<^marker>\<open>provenance ai_human\<close> "last_edge_matched_imp mate_t Ct i =
  (if 0 < i then do { a \<leftarrow> Array.nth Ct (i - 1);
                      b \<leftarrow> Array.nth Ct i;
                      m \<leftarrow> mate_t a;
                      return (m = Some b) }
   else return True)"

lemma last_edge_matched_imp_rule:
  assumes "i < length C" "set C \<subseteq> U" "mate_ok R mate_t mate U"
  shows "<R * Ct \<mapsto>\<^sub>a C> last_edge_matched_imp mate_t Ct i
         <\<lambda>b. R * Ct \<mapsto>\<^sub>a C * \<up>(b = last_edge_matched mate (take (Suc i) C))>"
proof(cases "0 < i")
  case True
  have "C ! (i - Suc 0) \<in> U"
    using assms(1,2) by (auto intro: nth_mem)
  hence MT: "<R> mate_t (C ! (i - Suc 0)) <\<lambda>r. R * \<up>(r = mate (C ! (i - Suc 0)))>"
    using assms(3) by (simp add: mate_ok_def)
  show ?thesis
    using assms(1) True
    by (sep_auto heap: MT simp: last_edge_matched_imp_def last_edge_matched_take)
next
  case False
  thus ?thesis
    using assms(1)
    by (sep_auto simp: last_edge_matched_imp_def last_edge_matched_take)
qed

definition \<^marker>\<open>provenance ai_human\<close> "stem2vert_imp adj_t mate_t Ct v =
  do { c \<leftarrow> choose_con_vert_imp adj_t Ct v;
       n \<leftarrow> Array.len Ct;
       i \<leftarrow> first_pos_imp (\<lambda>y. return (c = y)) Ct n 0;
       b \<leftarrow> last_edge_matched_imp mate_t Ct i;
       if b then prefix_imp Ct (Suc i)
       else do { Rt \<leftarrow> rev_copy_imp Ct;
                 i' \<leftarrow> first_pos_imp (\<lambda>y. return (c = y)) Rt n 0;
                 prefix_imp Rt (Suc i') } }"

lemma stem2vert_imp_rule:
  assumes "C \<noteq> []" "v \<in> U" "set C \<subseteq> U" "adj_ok R adj_t adj U" "mate_ok R mate_t mate U"
  shows "<R * Ct \<mapsto>\<^sub>a C> stem2vert_imp adj_t mate_t Ct v
         <\<lambda>St. R * Ct \<mapsto>\<^sub>a C * St \<mapsto>\<^sub>a stem2vert_path adj mate C v * true>"
proof-
  define c where "c = choose_con_vert adj C v"
  have cC: "c \<in> set C"
    using choose_con_vert_in[OF assms(1)] by (simp add: c_def)
  have i: "first_pos (\<lambda>y. c = y) C < length C"
    using cC by (auto simp: first_pos_less_iff)
  have i': "first_pos (\<lambda>y. c = y) (rev C) < length C"
    using cC first_pos_less_iff[of "\<lambda>y. c = y" "rev C"] by auto
  note LE = last_edge_matched_imp_rule[OF i assms(3,5)]
  show ?thesis
    using assms(1) i i'
    by (sep_auto heap: choose_con_vert_imp_rule[OF assms(1-4)] first_pos_imp_eq_rule LE
        first_pos_imp_eq_rule[where xs = "rev C", simplified] prefix_imp_rule rev_copy_imp_rule
        simp: stem2vert_imp_def stem2vert_path_first_pos c_def[symmetric] Suc_le_eq)
qed
subsection \<open>Whether a vertex is matched to the cycle\<close>

definition \<^marker>\<open>provenance ai_human\<close> "matched_to_cycle_imp mate_t Ct x =
  do { n \<leftarrow> Array.len Ct;
       i \<leftarrow> first_pos_imp (\<lambda>y. return (y = x)) Ct n 0;
       if i < n then return False
       else do { m \<leftarrow> mate_t x;
                 case m of
                   None \<Rightarrow> return False
                 | Some c \<Rightarrow> do { j \<leftarrow> first_pos_imp (\<lambda>y. return (y = c)) Ct n 0;
                                 return (j < n) } } }"

lemma matched_to_cycle_imp_rule:
  assumes "x \<in> U" "mate_ok R mate_t mate U"
  shows "<R * Ct \<mapsto>\<^sub>a C> matched_to_cycle_imp mate_t Ct x
         <\<lambda>r. R * Ct \<mapsto>\<^sub>a C * \<up>(r = matched_to_cycle mate C x)>"
proof-
  have MT: "<R> mate_t x <\<lambda>r. R * \<up>(r = mate x)>"
    using assms by (auto simp: mate_ok_def)
  show ?thesis
    by (sep_auto heap: first_pos_imp_eq_rule MT
        simp: matched_to_cycle_imp_def matched_to_cycle_def first_pos_member
        split: option.splits)
qed

subsection \<open>Joining the pieces of the lifted path\<close>

text \<open>The four cases of @{const replace_cycle}: the vertex of the cycle starts the path, ends
  it, or lies inside it, where the path is reversed if the vertex after it is matched to the
  cycle. The path @{term p} is split at position @{term i}.\<close>

definition \<^marker>\<open>provenance ai_human\<close> "join_start_imp St Pt n =
  do { m \<leftarrow> Array.len St;
       x \<leftarrow> Array.nth St 0;
       Rt \<leftarrow> Array.new (m + (n - 1)) x;
       copy_fwd_imp St 0 m Rt 0;
       copy_fwd_imp Pt 1 (n - 1) Rt m;
       return Rt }"

definition \<^marker>\<open>provenance ai_human\<close> "join_end_imp St Pt i =
  do { m \<leftarrow> Array.len St;
       x \<leftarrow> Array.nth St 0;
       Rt \<leftarrow> Array.new (m + i) x;
       copy_fwd_imp St 0 m Rt 0;
       copy_rev_imp Pt i i Rt m;
       return Rt }"

definition \<^marker>\<open>provenance ai_human\<close> "join_mid_imp St Pt i n =
  do { m \<leftarrow> Array.len St;
       x \<leftarrow> Array.nth St 0;
       Rt \<leftarrow> Array.new (i + m + (n - Suc i)) x;
       copy_fwd_imp Pt 0 i Rt 0;
       copy_fwd_imp St 0 m Rt i;
       copy_fwd_imp Pt (Suc i) (n - Suc i) Rt (i + m);
       return Rt }"

definition \<^marker>\<open>provenance ai_human\<close> "join_mid_rev_imp St Pt i n =
  do { m \<leftarrow> Array.len St;
       x \<leftarrow> Array.nth St 0;
       Rt \<leftarrow> Array.new ((n - Suc i) + m + i) x;
       copy_rev_imp Pt n (n - Suc i) Rt 0;
       copy_fwd_imp St 0 m Rt (n - Suc i);
       copy_rev_imp Pt i i Rt ((n - Suc i) + m);
       return Rt }"

lemma join_start_imp_rule:
  "\<lbrakk>s \<noteq> []; p \<noteq> []\<rbrakk> \<Longrightarrow>
   <St \<mapsto>\<^sub>a s * Pt \<mapsto>\<^sub>a p> join_start_imp St Pt (length p)
   <\<lambda>Rt. St \<mapsto>\<^sub>a s * Pt \<mapsto>\<^sub>a p * Rt \<mapsto>\<^sub>a (s @ drop 1 p)>"
proof-
  assume "s \<noteq> []" "p \<noteq> []"
  then obtain k where k: "length p = Suc k"
    by (cases p) auto
  show ?thesis
    using \<open>s \<noteq> []\<close>
    unfolding join_start_imp_def
    by (sep_auto heap: copy_fwd_imp_rule simp: put_list_eq k)
qed

lemma join_end_imp_rule:
  "\<lbrakk>s \<noteq> []; i \<le> length p\<rbrakk> \<Longrightarrow>
   <St \<mapsto>\<^sub>a s * Pt \<mapsto>\<^sub>a p> join_end_imp St Pt i
   <\<lambda>Rt. St \<mapsto>\<^sub>a s * Pt \<mapsto>\<^sub>a p * Rt \<mapsto>\<^sub>a (s @ rev (take i p))>"
  unfolding join_end_imp_def
  by (sep_auto heap: copy_fwd_imp_rule copy_rev_imp_rule simp: put_list_eq)

lemma join_mid_imp_rule:
  "\<lbrakk>s \<noteq> []; i < length p\<rbrakk> \<Longrightarrow>
   <St \<mapsto>\<^sub>a s * Pt \<mapsto>\<^sub>a p> join_mid_imp St Pt i (length p)
   <\<lambda>Rt. St \<mapsto>\<^sub>a s * Pt \<mapsto>\<^sub>a p * Rt \<mapsto>\<^sub>a (take i p @ s @ drop (Suc i) p)>"
  unfolding join_mid_imp_def
  by (sep_auto heap: copy_fwd_imp_rule simp: put_list_eq)

lemma join_mid_rev_imp_rule:
  "\<lbrakk>s \<noteq> []; i < length p\<rbrakk> \<Longrightarrow>
   <St \<mapsto>\<^sub>a s * Pt \<mapsto>\<^sub>a p> join_mid_rev_imp St Pt i (length p)
   <\<lambda>Rt. St \<mapsto>\<^sub>a s * Pt \<mapsto>\<^sub>a p *
         Rt \<mapsto>\<^sub>a (rev (drop (Suc i) p) @ s @ rev (take i p))>"
  unfolding join_mid_rev_imp_def
  by (sep_auto heap: copy_fwd_imp_rule copy_rev_imp_rule simp: put_list_eq)

subsection \<open>Lifting a path through a contraction\<close>

text \<open>The path @{term p} is split at position @{term i}, the position of the contracted vertex.\<close>

definition \<^marker>\<open>provenance ai_human\<close> "replace_cycle_imp adj_t mate_t Ct Pt i n =
  (if i = 0 then
     do { h \<leftarrow> Array.nth Pt 1;
          St \<leftarrow> stem2vert_imp adj_t mate_t Ct h;
          join_start_imp St Pt n }
   else if Suc i = n then
     do { l \<leftarrow> Array.nth Pt (i - 1);
          St \<leftarrow> stem2vert_imp adj_t mate_t Ct l;
          join_end_imp St Pt i }
   else
     do { h \<leftarrow> Array.nth Pt (Suc i);
          mc \<leftarrow> matched_to_cycle_imp mate_t Ct h;
          if \<not> mc then
            do { St \<leftarrow> stem2vert_imp adj_t mate_t Ct h;
                 join_mid_imp St Pt i n }
          else
            do { l \<leftarrow> Array.nth Pt (i - 1);
                 St \<leftarrow> stem2vert_imp adj_t mate_t Ct l;
                 join_mid_rev_imp St Pt i n } })"

definition \<^marker>\<open>provenance ai_human\<close> "refine_imp adj_t mate_t u Ct Pt =
  do { n \<leftarrow> Array.len Pt;
       i \<leftarrow> first_pos_imp (\<lambda>y. return (y = u)) Pt n 0;
       if i < n then replace_cycle_imp adj_t mate_t Ct Pt i n else return Pt }"

lemma refine_first_pos:
  "refine adj mate u C p =
    (if first_pos (\<lambda>y. y = u) p < length p
     then replace_cycle adj mate C (take (first_pos (\<lambda>y. y = u) p) p)
            (drop (Suc (first_pos (\<lambda>y. y = u) p)) p)
     else p)"
  by (simp add: refine_def pref_suf_first_pos first_pos_member)

lemma stem2vert_path_nonempty: "C \<noteq> [] \<Longrightarrow> stem2vert_path adj mate C v \<noteq> []"
  by (simp add: stem2vert_path_first_pos Let_def)

lemma replace_cycle_imp_rule:
  assumes "C \<noteq> []" "i < length p" "2 \<le> length p" "set p \<subseteq> U" "set C \<subseteq> U"
    "adj_ok R adj_t adj U" "mate_ok R mate_t mate U"
  shows "<R * Ct \<mapsto>\<^sub>a C * Pt \<mapsto>\<^sub>a p> replace_cycle_imp adj_t mate_t Ct Pt i (length p)
         <\<lambda>Rt. R * Ct \<mapsto>\<^sub>a C * Rt \<mapsto>\<^sub>a replace_cycle adj mate C (take i p) (drop (Suc i) p) * true>"
proof-
  note S = stem2vert_imp_rule[OF assms(1) _ assms(5-7)]
  have ne: "stem2vert_path adj mate C v \<noteq> []" for v
    by (rule stem2vert_path_nonempty[OF assms(1)])
  have pU: "p ! j \<in> U" if "j < length p" for j
    using assms(4) that by (auto intro: nth_mem)
  show ?thesis
  proof(cases "i = 0")
    case True
    have rc: "replace_cycle adj mate C [] (drop (Suc 0) p) =
        stem2vert_path adj mate C (p ! Suc 0) @ drop 1 p"
      using assms(3) by (simp add: replace_cycle_def hd_drop_conv_nth)
    have one: "Suc 0 < length p" "p \<noteq> []"
      using assms(3) by auto
    show ?thesis
      using True one
      by (sep_auto heap: S[OF pU[OF one(1)]] join_start_imp_rule[OF ne]
          simp: replace_cycle_imp_def rc)
  next
    case False
    have lst: "last (take i p) = p ! (i - Suc 0)" "take i p \<noteq> []"
      using assms(2) False by (simp_all add: last_take_nth_conv)
    have prev: "i - Suc 0 < length p"
      using assms(2) by simp
    show ?thesis
    proof(cases "Suc i = length p")
      case last: True
      have rc: "replace_cycle adj mate C (take i p) [] =
          stem2vert_path adj mate C (p ! (i - Suc 0)) @ rev (take i p)"
        using lst by (simp add: replace_cycle_def)
      show ?thesis
        using False last assms(2)
        by (sep_auto heap: S[OF pU[OF prev]] join_end_imp_rule[OF ne]
            simp: replace_cycle_imp_def rc)
    next
      case mid: False
      have next_: "Suc i < length p"
        using assms(2) mid by simp
      have hd2: "hd (drop (Suc i) p) = p ! Suc i" "drop (Suc i) p \<noteq> []"
        using next_ by (simp_all add: hd_drop_conv_nth)
      note MC = matched_to_cycle_imp_rule[OF pU[OF next_] assms(7)]
      show ?thesis
      proof(cases "matched_to_cycle mate C (p ! Suc i)")
        case False
        have rc: "replace_cycle adj mate C (take i p) (drop (Suc i) p) =
            take i p @ stem2vert_path adj mate C (p ! Suc i) @ drop (Suc i) p"
          using hd2 lst False by (simp add: replace_cycle_def)
        show ?thesis
          using \<open>i \<noteq> 0\<close> mid False assms(2)
          by (sep_auto heap: MC S[OF pU[OF next_]] join_mid_imp_rule[OF ne]
              simp: replace_cycle_imp_def rc)
      next
        case matched: True
        have rc: "replace_cycle adj mate C (take i p) (drop (Suc i) p) =
            rev (drop (Suc i) p) @ stem2vert_path adj mate C (p ! (i - Suc 0)) @ rev (take i p)"
          using hd2 lst matched by (simp add: replace_cycle_def)
        show ?thesis
          using \<open>i \<noteq> 0\<close> mid matched assms(2)
          by (sep_auto heap: MC S[OF pU[OF prev]] join_mid_rev_imp_rule[OF ne]
              simp: replace_cycle_imp_def rc)
      qed
    qed
  qed
qed

text \<open>A path through the contracted vertex has at least two vertices, as an augmenting path
  has. The path is consumed: if it does not pass through the contracted vertex, it is returned
  unchanged.\<close>

lemma \<^marker>\<open>provenance ai_human\<close> refine_imp_rule:
  assumes "C \<noteq> []" "u \<in> set p \<Longrightarrow> 2 \<le> length p" "set p \<subseteq> U" "set C \<subseteq> U"
    "adj_ok R adj_t adj U" "mate_ok R mate_t mate U"
  shows "<R * Ct \<mapsto>\<^sub>a C * Pt \<mapsto>\<^sub>a p> refine_imp adj_t mate_t u Ct Pt
         <\<lambda>Rt. R * Ct \<mapsto>\<^sub>a C * Rt \<mapsto>\<^sub>a refine adj mate u C p * true>"
proof \<^marker>\<open>provenance ai\<close> (cases "first_pos (\<lambda>y. y = u) p < length p")
  case True
  have two: "2 \<le> length p"
    using True assms(2) by (simp add: first_pos_member)
  show ?thesis
    using True
    by (sep_auto heap: first_pos_imp_eq_rule
        replace_cycle_imp_rule[OF assms(1) True two assms(3-6)]
        simp: refine_imp_def refine_first_pos)
next
  case False
  thus ?thesis
    by (sep_auto heap: first_pos_imp_eq_rule simp: refine_imp_def refine_first_pos)
qed

end