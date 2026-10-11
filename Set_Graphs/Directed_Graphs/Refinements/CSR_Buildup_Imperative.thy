theory CSR_Buildup_Imperative
  imports "../CSR_Buildup" Separation_Logic_Imperative_HOL_Partial.Sep_Main
begin

section \<open>Imperative CSR Buildup\<close>

text \<open>
  The functional counting sort of @{locale csr_buildup} is refined to Imperative HOL,
  following the imperative DFS: one locale combines the functional locale with the imperative
  operations and their Hoare triples, the loops are heap @{command partial_function}s,
  and each loop is shown to compute the functional loop by fixpoint induction.

  For efficiency,
  \<^item> the boundaries \<open>B\<close> and edges \<open>E\<close> are arrays updated in place, and
    no memory beyond them is allocated (in particular, no cursor array),
  \<^item> the prefix sums carry the running sum in a register, so each entry of \<open>B\<close> is read once,
  \<^item> the iterator is split into \<open>has_next\<close>, \<open>cur\<close> and \<open>adv\<close>,
    so no option or pair is built per edge. The iterator state is a plain value
    (e.g.\ a counter), so restarting the iterator for the second pass is free.
    The iterator operations additionally take the handle \<open>c\<close> of the input container (e.g.\ the
    input arrays). No imperative value is fixed by a locale: the container is an argument of the
    programs, and the refinement assertion @{term input_assn} relates it to the input in the
    Hoare triples, which the operations preserve.
  \<^item> \<open>E\<close> does not store the elements themselves but their values under a function \<open>val\<close>, so an
    element can be a position in the input, from which the key and the stored value are read.
    The key and the value operations therefore also take the input container.
\<close>

text \<open>The code locale fixes only the size and the imperative iterator, key and value operations;
      it has no assumptions, so that the programs can be globally interpreted and exported.\<close>

locale imp_csr_buildup_code =
  fixes n :: nat
    and it_has_next_impl :: "'ci \<Rightarrow> 'si \<Rightarrow> bool Heap"
    and it_cur_impl :: "'ci \<Rightarrow> 'si \<Rightarrow> 'e Heap"
    and it_adv_impl :: "'ci \<Rightarrow> 'si \<Rightarrow> 'si Heap"
    and key_impl :: "'ci \<Rightarrow> 'e \<Rightarrow> nat Heap"
    and val_impl :: "'ci \<Rightarrow> 'e \<Rightarrow> 'x::heap Heap"
begin

subsection \<open>Programs\<close>

text \<open>Count pass, refining @{term "it_fold count_step"}.\<close>

partial_function (heap) count_imp :: "'ci \<Rightarrow> nat array \<Rightarrow> nat \<Rightarrow> 'si \<Rightarrow> nat Heap" where
  "count_imp c B m si = do {
     b \<leftarrow> it_has_next_impl c si;
     if b then do {
       e \<leftarrow> it_cur_impl c si;
       k \<leftarrow> key_impl c e;
       (if k + 2 \<le> n then do {
          d \<leftarrow> Array.nth B (k + 2);
          Array.upd (k + 2) (Suc d) B;
          return () }
        else return ());
       si' \<leftarrow> it_adv_impl c si;
       count_imp c B (Suc m) si' }
     else return m }"

text \<open>Prefix sums, refining @{term "fold prefix_step [j..<Suc n]"}; \<open>acc\<close> holds \<open>B!(j-1)\<close>.\<close>

partial_function (heap) prefix_imp :: "nat array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "prefix_imp B j acc =
     (if j \<le> n then do {
        c \<leftarrow> Array.nth B j;
        let acc' = c + acc;
        Array.upd j acc' B;
        prefix_imp B (Suc j) acc' }
      else return ())"

text \<open>Fill pass, refining @{term "it_fold fill_step"}; the value of the element is stored.\<close>

partial_function (heap) fill_imp :: "'ci \<Rightarrow> nat array \<Rightarrow> 'x array \<Rightarrow> 'si \<Rightarrow> unit Heap" where
  "fill_imp c B E si = do {
     b \<leftarrow> it_has_next_impl c si;
     if b then do {
       e \<leftarrow> it_cur_impl c si;
       k \<leftarrow> key_impl c e;
       x \<leftarrow> val_impl c e;
       p \<leftarrow> Array.nth B (k + 1);
       Array.upd (k + 1) (Suc p) B;
       Array.upd p x E;
       si' \<leftarrow> it_adv_impl c si;
       fill_imp c B E si' }
     else return () }"

text \<open>Allocation of the edge array, refining @{const csr_buildup.init_E}.\<close>

definition init_E_imp :: "'ci \<Rightarrow> 'si \<Rightarrow> nat \<Rightarrow> 'x array Heap" where
  "init_E_imp c si m = do {
     b \<leftarrow> it_has_next_impl c si;
     if b then do { e \<leftarrow> it_cur_impl c si; x \<leftarrow> val_impl c e; Array.new m x }
     else Array.of_list [] }"

definition csr_build_imp :: "'ci \<Rightarrow> 'si \<Rightarrow> (nat array \<times> 'x array) Heap" where
  "csr_build_imp c si = do {
     B \<leftarrow> Array.new (Suc n) 0;
     m \<leftarrow> count_imp c B 0 si;
     prefix_imp B 1 0;
     E \<leftarrow> init_E_imp c si m;
     fill_imp c B E si;
     return (B, E) }"

end

text \<open>The proof locale: the functional counting sort, the value function, the iterator relation
      and the context assertion, with one Hoare triple per imperative operation.\<close>

locale imp_csr_buildup = csr_buildup it_next it_seq it_invar key n s0 +
  imp_csr_buildup_code n it_has_next_impl it_cur_impl it_adv_impl key_impl val_impl
  for it_next :: "'s \<Rightarrow> ('e \<times> 's) option"
    and it_seq :: "'s \<Rightarrow> 'e list"
    and it_invar :: "'s \<Rightarrow> bool"
    and key :: "'e \<Rightarrow> nat"
    and n :: nat
    and s0 :: 's
    and it_has_next_impl :: "'ci \<Rightarrow> 'si \<Rightarrow> bool Heap"
    and it_cur_impl :: "'ci \<Rightarrow> 'si \<Rightarrow> 'e Heap"
    and it_adv_impl :: "'ci \<Rightarrow> 'si \<Rightarrow> 'si Heap"
    and key_impl :: "'ci \<Rightarrow> 'e \<Rightarrow> nat Heap"
    and val_impl :: "'ci \<Rightarrow> 'e \<Rightarrow> 'x::heap Heap" +
  fixes val :: "'e \<Rightarrow> 'x"
    and it_rel :: "'s \<Rightarrow> 'si \<Rightarrow> bool"
    and input_assn :: "'ci \<Rightarrow> assn"
  assumes has_next_rule:
    "\<lbrakk>it_invar s; it_rel s si\<rbrakk> \<Longrightarrow>
       <input_assn c> it_has_next_impl c si <\<lambda>b. input_assn c * \<up>(b \<longleftrightarrow> it_next s \<noteq> None)>"
    and cur_rule:
    "\<lbrakk>it_invar s; it_rel s si; it_next s = Some (e, s')\<rbrakk> \<Longrightarrow>
       <input_assn c> it_cur_impl c si <\<lambda>r. input_assn c * \<up>(r = e)>"
    and adv_rule:
    "\<lbrakk>it_invar s; it_rel s si; it_next s = Some (e, s')\<rbrakk> \<Longrightarrow>
       <input_assn c> it_adv_impl c si <\<lambda>si'. input_assn c * \<up>(it_rel s' si')>"
    and key_rule:
    "e \<in> set (it_seq s0) \<Longrightarrow> <input_assn c> key_impl c e <\<lambda>k. input_assn c * \<up>(k = key e)>"
    and val_rule:
    "e \<in> set (it_seq s0) \<Longrightarrow> <input_assn c> val_impl c e <\<lambda>x. input_assn c * \<up>(x = val e)>"
begin

subsection \<open>Correctness\<close>

lemma count_imp_rule:
  "<input_assn c * B \<mapsto>\<^sub>a Bs * \<up>(it_invar s \<and> it_rel s si \<and> set (it_seq s) \<subseteq> set es \<and> length Bs = Suc n)>
     count_imp c B m si
   <\<lambda>r. input_assn c * B \<mapsto>\<^sub>a fst (it_fold count_step s (Bs, m))
         * \<up>(r = snd (it_fold count_step s (Bs, m)))>"
proof (induction arbitrary: s si Bs m rule: count_imp.fixp_induct)
  case 1
  show ?case by simp
next
  case 2
  show ?case by simp
next
  case (3 f)
  note IH = "3"
  show ?case
  proof (cases "it_invar s \<and> it_rel s si \<and> set (it_seq s) \<subseteq> set es \<and> length Bs = Suc n")
    case False
    thus ?thesis by (intro ht_extract_pre_pure(1)) simp
  next
    case True
    hence inv: "it_invar s" and rel: "it_rel s si" and sub: "set (it_seq s) \<subseteq> set es"
      and len: "length Bs = Suc n"
      by auto
    show ?thesis
    proof (cases "it_next s")
      case None
      have fe: "it_fold count_step s (Bs, m) = (Bs, m)"
        by (subst it_fold.simps) (simp add: None)
      thus ?thesis
        using None by (sep_auto heap: has_next_rule[OF inv rel])
    next
      case (Some a)
      then obtain e s' where nx: "it_next s = Some (e, s')"
        by (cases a) auto
      have inv': "it_invar s'" and seq: "it_seq s = e # it_seq s'"
        using it_next_Some[OF inv nx] by auto
      have eE: "e \<in> set (it_seq s0)"
        using sub seq by (auto simp add: es_def)
      have sub': "set (it_seq s') \<subseteq> set es"
        using sub seq by auto
      have IH': "<input_assn c * B \<mapsto>\<^sub>a Bs' * \<up>(it_rel s' si' \<and> length Bs' = Suc n)> f c B m' si'
                 <\<lambda>r. input_assn c * B \<mapsto>\<^sub>a fst (it_fold count_step s' (Bs', m'))
                       * \<up>(r = snd (it_fold count_step s' (Bs', m')))>" for si' Bs' m'
        using IH[where s1=s' and si1=si' and Bs1=Bs' and m1=m'] inv' sub' by (simp only: simp_thms)
      have fe: "it_fold count_step s (Bs, m)
            = it_fold count_step s'
                (if key e + 2 \<le> n then Bs[key e + 2 := Bs ! (key e + 2) + 1] else Bs, Suc m)"
        by (subst it_fold.simps) (simp add: nx count_step_def Let_def)
      show ?thesis
        using len
        by (sep_auto heap: has_next_rule[OF inv rel] cur_rule[OF inv rel nx]
                           adv_rule[OF inv rel nx] key_rule[OF eE] IH'
                     simp: nx fe)
    qed
  qed
qed

lemma prefix_imp_rule:
  "<B \<mapsto>\<^sub>a Bs * \<up>(length Bs = Suc n \<and> 0 < j \<and> acc = Bs ! (j - 1))>
     prefix_imp B j acc
   <\<lambda>_. B \<mapsto>\<^sub>a fold prefix_step [j..<Suc n] Bs>"
proof (induction arbitrary: Bs j acc rule: prefix_imp.fixp_induct)
  case 1
  show ?case by simp
next
  case 2
  show ?case by simp
next
  case (3 f)
  note IH = "3"
  show ?case
  proof (cases "length Bs = Suc n \<and> 0 < j \<and> acc = Bs ! (j - 1)")
    case False
    thus ?thesis by (intro ht_extract_pre_pure(1)) simp
  next
    case True
    hence len: "length Bs = Suc n" and j: "0 < j" and acc: "acc = Bs ! (j - 1)"
      by auto
    show ?thesis
    proof (cases "j \<le> n")
      case False
      thus ?thesis by sep_auto
    next
      case True
      have IH': "<B \<mapsto>\<^sub>a Bs' * \<up>(length Bs' = Suc n \<and> acc' = Bs' ! j)> f B (Suc j) acc'
                 <\<lambda>_. B \<mapsto>\<^sub>a fold prefix_step [Suc j..<Suc n] Bs'>" for Bs' acc'
        using IH[where Bs1=Bs' and j1="Suc j" and acc1=acc']
        by (simp only: zero_less_Suc diff_Suc_1 simp_thms)
      have "fold prefix_step [j..<Suc n] Bs = fold prefix_step [Suc j..<Suc n] (Bs[j := Bs ! j + acc])"
        using True by (subst upt_conv_Cons[of j "Suc n"]) (simp_all add: prefix_step_def acc del: upt_Suc)
      thus ?thesis
        using True len by (sep_auto heap: IH')
    qed
  qed
qed

corollary prefix_sums_imp_rule:
  "<B \<mapsto>\<^sub>a Bs * \<up>(length Bs = Suc n \<and> Bs ! 0 = 0)> prefix_imp B 1 0 <\<lambda>_. B \<mapsto>\<^sub>a prefix_sums Bs>"
  using prefix_imp_rule[where j=1 and acc=0] by (simp add: prefix_sums_def)

lemma fill_imp_rule:
  "<input_assn c * B \<mapsto>\<^sub>a Bs * E \<mapsto>\<^sub>a map val Es
      * \<up>(it_invar s \<and> it_rel s si \<and> xs @ it_seq s = es \<and> fill_invar xs (Bs, Es))>
     fill_imp c B E si
   <\<lambda>_. input_assn c * B \<mapsto>\<^sub>a fst (it_fold fill_step s (Bs, Es))
         * E \<mapsto>\<^sub>a map val (snd (it_fold fill_step s (Bs, Es)))>"
proof (induction arbitrary: s si xs Bs Es rule: fill_imp.fixp_induct)
  case 1
  show ?case by simp
next
  case 2
  show ?case by simp
next
  case (3 f)
  note IH = "3"
  show ?case
  proof (cases "it_invar s \<and> it_rel s si \<and> xs @ it_seq s = es \<and> fill_invar xs (Bs, Es)")
    case False
    thus ?thesis by (intro ht_extract_pre_pure(1)) simp
  next
    case True
    hence inv: "it_invar s" and rel: "it_rel s si" and xs: "xs @ it_seq s = es"
      and finv: "fill_invar xs (Bs, Es)"
      by auto
    show ?thesis
    proof (cases "it_next s")
      case None
      have "it_fold fill_step s (Bs, Es) = (Bs, Es)"
        by (subst it_fold.simps) (simp add: None)
      thus ?thesis
        using None by (sep_auto heap: has_next_rule[OF inv rel])
    next
      case (Some a)
      then obtain e s' where nx: "it_next s = Some (e, s')"
        by (cases a) auto
      have inv': "it_invar s'" and seq: "it_seq s = e # it_seq s'"
        using it_next_Some[OF inv nx] by auto
      have es: "xs @ e # it_seq s' = es"
        using xs seq by simp
      have eE: "e \<in> set (it_seq s0)"
        unfolding es_def[symmetric] es[symmetric] by simp
      have bnd: "Suc (key e) < length Bs" "Bs ! Suc (key e) < length Es"
        using fill_step_bounds[OF es finv] by auto
      have finv': "fill_invar (xs @ [e]) (fill_step e (Bs, Es))"
        using fill_step_invar[OF es finv] .
      have fs: "fill_step e (Bs, Es)
                = (Bs[Suc (key e) := Suc (Bs ! Suc (key e))], Es[Bs ! Suc (key e) := e])"
        by (simp add: fill_step_def Let_def)
      have IH': "<input_assn c * B \<mapsto>\<^sub>a fst (fill_step e (Bs, Es))
                    * E \<mapsto>\<^sub>a map val (snd (fill_step e (Bs, Es))) * \<up>(it_rel s' si')> f c B E si'
                 <\<lambda>_. input_assn c * B \<mapsto>\<^sub>a fst (it_fold fill_step s' (fill_step e (Bs, Es)))
                       * E \<mapsto>\<^sub>a map val (snd (it_fold fill_step s' (fill_step e (Bs, Es))))>" for si'
        using IH[where s1=s' and si1=si' and xs1="xs @ [e]" and Bs1="fst (fill_step e (Bs, Es))"
                 and Es1="snd (fill_step e (Bs, Es))"]
              inv' es finv'
        by (simp only: prod.collapse append_assoc append.simps es simp_thms)
      have "it_fold fill_step s (Bs, Es)
            = it_fold fill_step s' (Bs[Suc (key e) := Suc (Bs ! Suc (key e))], Es[Bs ! Suc (key e) := e])"
        by (subst it_fold.simps) (simp add: nx fs)
      thus ?thesis
        using bnd
        by (sep_auto heap: has_next_rule[OF inv rel] cur_rule[OF inv rel nx]
                           adv_rule[OF inv rel nx] key_rule[OF eE] val_rule[OF eE]
                           IH'[unfolded fs fst_conv snd_conv map_update]
                     simp: nx)
    qed
  qed
qed

lemma init_E_imp_rule:
  "<input_assn c * \<up>(it_rel s0 si)> init_E_imp c si m <\<lambda>E. input_assn c * E \<mapsto>\<^sub>a map val (init_E m)>"
proof (cases "it_next s0")
  case None
  thus ?thesis
    unfolding init_E_imp_def init_E_def
    by (sep_auto heap: has_next_rule[OF s0_invar])
next
  case (Some a)
  then obtain e s' where nx: "it_next s0 = Some (e, s')"
    by (cases a) auto
  have eE: "e \<in> set (it_seq s0)"
    using it_next_Some[OF s0_invar nx] by simp
  show ?thesis
    using nx
    unfolding init_E_imp_def init_E_def
    by (sep_auto heap: has_next_rule[OF s0_invar] cur_rule[OF s0_invar _ nx] val_rule[OF eE])
qed

theorem csr_build_imp_rule:
  "<input_assn c * \<up>(it_rel s0 si)> csr_build_imp c si
   <\<lambda>(B, E). input_assn c * B \<mapsto>\<^sub>a B_spec * E \<mapsto>\<^sub>a map val E_spec>"
proof -
  have c: "it_fold count_step s0 (0 # replicate n 0, 0) = (count_B es, length es)"
    using count_edges by (simp add: count_edges_def)
  have fl: "it_fold fill_step s0 (prefix_sums (count_B es), init_E (length es)) = (B_spec, E_spec)"
    using csr_build_correct by (simp add: csr_build_def count_edges)
  have seq0: "it_seq s0 = es"
    by (simp add: es_def)
  have B0: "count_B es ! 0 = 0"
    by (simp add: count_B_nth)
  show ?thesis
    unfolding csr_build_imp_def
    by (sep_auto heap: count_imp_rule[where s=s0] prefix_sums_imp_rule init_E_imp_rule
                       fill_imp_rule[where s=s0 and xs="[]"]
                 simp: c B0 fl s0_invar seq0 fill_invar_init)
qed

end

end


