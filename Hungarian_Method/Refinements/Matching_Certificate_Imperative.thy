theory Matching_Certificate_Imperative
  imports
    Hungarian_Method.Matching_Certificate_Spec
    Separation_Logic_Imperative_HOL_Partial.Sep_Main
    Data_Structures.Fixed_Univ_Set_Iterate_Imp
    Data_Structures.Fixed_Univ_List_Specs_Imp
begin

provenance ai


section \<open>Certificate Checkers for Extremal Bipartite Matchings: Imperative Refinement\<close>

subsection \<open>The Interfaces\<close>

text \<open>Read-only lists with random access. They hold the candidate matching, the potentials, the
      Hall violator and the vertex lists.\<close>

text \<open>The edges: an iterable fixed-universe set of edge names
      (@{locale fixed_univ_set_iterate_imp}) with membership, and the left endpoint
      @{term efst}, the right endpoint @{term esnd} and the weight @{term ew} of every edge.\<close>

locale imp_edge_set =
  es: fixed_univ_set_iterate_imp U es_invar id es_assn lst it_assn it_init it_has_next it_next
  for U :: "'e set" and es_invar :: "'e set \<Rightarrow> bool" and es_assn :: "'e set \<Rightarrow> 'p \<Rightarrow> assn"
    and lst :: "'e set \<Rightarrow> 'e list" and it_assn :: "'e set \<Rightarrow> 'p \<Rightarrow> 'e list \<Rightarrow> 'it \<Rightarrow> assn"
    and it_init :: "'p \<Rightarrow> 'it Heap" and it_has_next :: "'it \<Rightarrow> bool Heap"
    and it_next :: "'it \<Rightarrow> ('e \<times> 'it) Heap" +
  fixes efst :: "'e \<Rightarrow> nat"
    and esnd :: "'e \<Rightarrow> nat"
    and ew :: "'e \<Rightarrow> 'n"
    and memb_imp :: "'p \<Rightarrow> 'e \<Rightarrow> bool Heap"
    and fst_imp :: "'p \<Rightarrow> 'e \<Rightarrow> nat Heap"
    and snd_imp :: "'p \<Rightarrow> 'e \<Rightarrow> nat Heap"
    and w_imp :: "'p \<Rightarrow> 'e \<Rightarrow> 'n Heap"
  assumes memb_rule: "<es_assn D p> memb_imp p e <\<lambda>r. es_assn D p * \<up>(r \<longleftrightarrow> e \<in> D)>"
    and fst_rule: "e \<in> D \<Longrightarrow> <es_assn D p> fst_imp p e <\<lambda>r. es_assn D p * \<up>(r = efst e)>"
    and snd_rule: "e \<in> D \<Longrightarrow> <es_assn D p> snd_imp p e <\<lambda>r. es_assn D p * \<up>(r = esnd e)>"
    and w_rule: "e \<in> D \<Longrightarrow> <es_assn D p> w_imp p e <\<lambda>r. es_assn D p * \<up>(r = ew e)>"
begin

lemmas it_init_rule = es.it_init_rule[unfolded id_apply]
  and it_has_next_rule = es.it_has_next_rule[unfolded id_apply]
  and it_next_rule = es.it_next_rule[unfolded id_apply]

end

text \<open>The mark sets are fixed-universe sets (@{locale fixed_univ_set_imp}), of which the programs
      use membership and insertion in place. The programs do not allocate: the empty mark sets
      are passed in.\<close>

subsection \<open>The Programs\<close>

locale matching_cert_imp_code =
  fixes memb_imp :: "'p \<Rightarrow> 'e \<Rightarrow> bool Heap"
    and fst_imp :: "'p \<Rightarrow> 'e \<Rightarrow> nat Heap"
    and snd_imp :: "'p \<Rightarrow> 'e \<Rightarrow> nat Heap"
    and w_imp :: "'p \<Rightarrow> 'e \<Rightarrow> 'n::linordered_idom Heap"
    and it_init :: "'p \<Rightarrow> 'it Heap"
    and it_has_next :: "'it \<Rightarrow> bool Heap"
    and it_next :: "'it \<Rightarrow> ('e \<times> 'it) Heap"
    and elen :: "'pe \<Rightarrow> nat Heap"
    and enth :: "'pe \<Rightarrow> nat \<Rightarrow> 'e Heap"
    and ylen :: "'py \<Rightarrow> nat Heap"
    and ynth :: "'py \<Rightarrow> nat \<Rightarrow> 'n Heap"
    and vlen :: "'pv \<Rightarrow> nat Heap"
    and vnth :: "'pv \<Rightarrow> nat \<Rightarrow> nat Heap"
    and smemb :: "'s \<Rightarrow> nat \<Rightarrow> bool Heap"
    and sins :: "nat \<Rightarrow> 's \<Rightarrow> unit Heap"
begin

text \<open>Feasibility, over all edges.\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) feas_loop :: "bool \<Rightarrow> 'n \<Rightarrow> 'p \<Rightarrow> 'py \<Rightarrow> 'it \<Rightarrow> bool Heap" where
  "feas_loop neg t p Ya it = do {
     b \<leftarrow> it_has_next it;
     (if b then do {
        (e, it') \<leftarrow> it_next it;
        u \<leftarrow> fst_imp p e;
        v \<leftarrow> snd_imp p e;
        c \<leftarrow> w_imp p e;
        yu \<leftarrow> ynth Ya u;
        yv \<leftarrow> ynth Ya v;
        (if yu + yv + t \<le> sgn_c neg c then feas_loop neg t p Ya it' else return False) }
      else return True) }"

text \<open>The candidate matching: membership of the names, disjointness and tightness.\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) match_loop ::
  "bool \<Rightarrow> 'n \<Rightarrow> 'p \<Rightarrow> 'py \<Rightarrow> 'pe \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> bool Heap" where
  "match_loop neg t p Ya Ma i k Ui =
     (if i < k then do {
        e \<leftarrow> enth Ma i;
        b \<leftarrow> memb_imp p e;
        (if b then do {
           u \<leftarrow> fst_imp p e;
           v \<leftarrow> snd_imp p e;
           c \<leftarrow> w_imp p e;
           bu \<leftarrow> smemb Ui u;
           bv \<leftarrow> smemb Ui v;
           yu \<leftarrow> ynth Ya u;
           yv \<leftarrow> ynth Ya v;
           (if \<not> bu \<and> \<not> bv \<and> yu + yv + t = sgn_c neg c
            then do { sins u Ui; sins v Ui; match_loop neg t p Ya Ma (Suc i) k Ui }
            else return False) }
         else return False) }
      else return True)"

text \<open>Sign and complementary slackness of the potential, over a list of vertices.\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) vert_loop :: "'py \<Rightarrow> 'pv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> bool Heap" where
  "vert_loop Ya Va i k Ui =
     (if i < k then do {
        x \<leftarrow> vnth Va i;
        y \<leftarrow> ynth Ya x;
        b \<leftarrow> smemb Ui x;
        (if y \<le> 0 \<and> (y \<noteq> 0 \<longrightarrow> b) then vert_loop Ya Va (Suc i) k Ui else return False) }
      else return True)"

definition \<^marker>\<open>provenance ai_human\<close> certify_sh_imp ::
  "bool \<Rightarrow> bool \<Rightarrow> 'n \<Rightarrow> nat \<Rightarrow> 'p \<Rightarrow> 'pv \<Rightarrow> 'pv \<Rightarrow> 'pe \<Rightarrow> 'py \<Rightarrow> 's \<Rightarrow> bool Heap" where
  "certify_sh_imp neg perfect t n p La Ra Ma Ya Ui = do {
     ly \<leftarrow> ylen Ya;
     (if n \<le> ly then do {
        it \<leftarrow> it_init p;
        f \<leftarrow> feas_loop neg t p Ya it;
        (if f then do {
           km \<leftarrow> elen Ma;
           ok \<leftarrow> match_loop neg t p Ya Ma 0 km Ui;
           kl \<leftarrow> vlen La;
           kr \<leftarrow> vlen Ra;
           (if ok then
              (if perfect then return (km = kl \<and> kl = kr)
               else do {
                 a \<leftarrow> vert_loop Ya La 0 kl Ui;
                 (if a then vert_loop Ya Ra 0 kr Ui else return False) })
            else return False) }
         else return False) }
      else return False) }"

definition \<^marker>\<open>provenance ai_human\<close> certify_imp ::
  "bool \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> 'p \<Rightarrow> 'pv \<Rightarrow> 'pv \<Rightarrow> 'pe \<Rightarrow> 'py \<Rightarrow> 's \<Rightarrow> bool Heap" where
  "certify_imp neg perfect = certify_sh_imp neg perfect 0"

text \<open>Hall violators. The entries of the violator are input: the ones not below @{term n} are
      rejected before the mark sets are read.\<close>

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) insert_loop :: "'pv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> unit Heap" where
  "insert_loop Va i k Ui =
     (if i < k then do { x \<leftarrow> vnth Va i; sins x Ui; insert_loop Va (Suc i) k Ui }
      else return ())"

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) hall_S_loop ::
  "nat \<Rightarrow> 's \<Rightarrow> 'pv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> (nat \<times> bool) Heap" where
  "hall_S_loop n Li Sa i k Si c =
     (if i < k then do {
        x \<leftarrow> vnth Sa i;
        bl \<leftarrow> (if x < n then smemb Li x else return False);
        (if bl then do {
           bs \<leftarrow> smemb Si x;
           (if bs then hall_S_loop n Li Sa (Suc i) k Si c
            else do { sins x Si; hall_S_loop n Li Sa (Suc i) k Si (Suc c) }) }
         else return (c, False)) }
      else return (c, True))"

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) hall_N_loop :: "'p \<Rightarrow> 's \<Rightarrow> 'it \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "hall_N_loop p Si it Ni c = do {
     b \<leftarrow> it_has_next it;
     (if b then do {
        (e, it') \<leftarrow> it_next it;
        u \<leftarrow> fst_imp p e;
        v \<leftarrow> snd_imp p e;
        bu \<leftarrow> smemb Si u;
        bv \<leftarrow> smemb Ni v;
        (if bu \<and> \<not> bv then do { sins v Ni; hall_N_loop p Si it' Ni (Suc c) }
         else hall_N_loop p Si it' Ni c) }
      else return c) }"

definition \<^marker>\<open>provenance ai_human\<close> hall_imp :: "nat \<Rightarrow> 'p \<Rightarrow> 'pv \<Rightarrow> 'pv \<Rightarrow> 'pv \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool Heap" where
  "hall_imp n p La Ra Sa Li Si Ni = do {
     kl \<leftarrow> vlen La;
     kr \<leftarrow> vlen Ra;
     (if kl \<noteq> kr then return True
      else do {
        insert_loop La 0 kl Li;
        ks \<leftarrow> vlen Sa;
        (c, ok) \<leftarrow> hall_S_loop n Li Sa 0 ks Si 0;
        (if ok then do {
           it \<leftarrow> it_init p;
           nb \<leftarrow> hall_N_loop p Si it Ni 0;
           return (nb < c) }
         else return False) }) }"

text \<open>Extremal weight maximum cardinality matchings: the shifted dual check, and the deficient
      set @{term S}.\<close>

definition \<^marker>\<open>provenance ai_human\<close> certify_mc_imp ::
  "bool \<Rightarrow> nat \<Rightarrow> 'p \<Rightarrow> 'pv \<Rightarrow> 'pv \<Rightarrow> 'pe \<Rightarrow> 'py \<Rightarrow> 'n \<Rightarrow> 'pv \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow>
   bool Heap" where
  "certify_mc_imp neg n p La Ra Ma Ya t Sa Ui Li Si Ni = do {
     a \<leftarrow> certify_sh_imp neg False t n p La Ra Ma Ya Ui;
     (if a then do {
        kl \<leftarrow> vlen La;
        insert_loop La 0 kl Li;
        ks \<leftarrow> vlen Sa;
        (c, ok) \<leftarrow> hall_S_loop n Li Sa 0 ks Si 0;
        (if ok then do {
           it \<leftarrow> it_init p;
           nb \<leftarrow> hall_N_loop p Si it Ni 0;
           km \<leftarrow> elen Ma;
           return (kl + nb \<le> km + c) }
         else return False) }
      else return False) }"

end

subsection \<open>Correctness\<close>

text \<open>The mark sets are over a universe @{term K} containing the vertices below @{term n}.\<close>

locale matching_cert_imp =
  matching_cert E elist efst esnd ew n ls rs h +
  es: imp_edge_set EU es_invar es_assn lst it_assn it_init it_has_next it_next efst esnd ew
        memb_imp fst_imp snd_imp w_imp +
  el: imp_rlist el_assn elen enth +
  yl: imp_rlist yl_assn ylen ynth +
  vl: imp_rlist vl_assn vlen vnth +
  mk: fixed_univ_set_imp K sinvar sabs sempty sinsert sdelete sisin set_assn sempty_imp sins sdel
        smemb
  for E :: "'e set" and elist efst esnd and ew :: "'e \<Rightarrow> 'n::linordered_idom" and n ls rs h
    and EU es_invar and es_assn :: "'e set \<Rightarrow> 'p \<Rightarrow> assn"
    and lst and it_assn :: "'e set \<Rightarrow> 'p \<Rightarrow> 'e list \<Rightarrow> 'it \<Rightarrow> assn"
    and it_init it_has_next it_next memb_imp fst_imp snd_imp w_imp
    and el_assn :: "'e list \<Rightarrow> 'pe \<Rightarrow> assn" and elen enth
    and yl_assn :: "'n list \<Rightarrow> 'py \<Rightarrow> assn" and ylen ynth
    and vl_assn :: "nat list \<Rightarrow> 'pv \<Rightarrow> assn" and vlen vnth
    and K :: "nat set" and sinvar :: "'set \<Rightarrow> bool" and sabs sempty sinsert sdelete sisin
    and set_assn :: "'set \<Rightarrow> 's \<Rightarrow> assn" and sempty_imp sins sdel smemb +
  assumes E_invar: "es_invar E"
    and elist_lst: "elist = lst E"
    and verts_K: "{..<n} \<subseteq> K"

sublocale matching_cert_imp \<subseteq> code: matching_cert_imp_code
  memb_imp fst_imp snd_imp w_imp it_init it_has_next it_next elen enth ylen ynth vlen vnth
  smemb sins .

context matching_cert_imp
begin

abbreviation "EA p \<equiv> es_assn E p"

abbreviation "EI p \<equiv> it_assn E p"

text \<open>A mark set, up to abstraction.\<close>

definition "mark_assn U Ui = (\<exists>\<^sub>AS. set_assn S Ui * \<up>(sinvar S \<and> sabs S = U))"

lemma \<^marker>\<open>provenance ai_human\<close> mark_empty_rule: "<emp> sempty_imp <mark_assn {}>"
  unfolding mark_assn_def
  by (sep_auto heap: mk.fixed_univ_set_empty_rule simp: mk.fixed_univ_set_empty)

lemma \<^marker>\<open>provenance ai_human\<close> mark_memb_rule:
  "x \<in> K \<Longrightarrow> <mark_assn U Ui> smemb Ui x <\<lambda>r. mark_assn U Ui * \<up>(r \<longleftrightarrow> x \<in> U)>"
  unfolding mark_assn_def
  by (sep_auto heap: mk.fixed_univ_set_isin_rule simp: mk.fixed_univ_set_isin)

lemma \<^marker>\<open>provenance ai_human\<close> mark_ins_rule:
  "x \<in> K \<Longrightarrow> <mark_assn U Ui> sins x Ui <\<lambda>_. mark_assn (insert x U) Ui>"
  unfolding mark_assn_def
  by (sep_auto heap: mk.fixed_univ_set_insert_rule simp: mk.fixed_univ_set_insert)

lemma edge_bounds:
  assumes "e \<in> E" "n \<le> length ys"
  shows "efst e < length ys" "esnd e < length ys"
  using assms fst_in snd_in verts_below
  by fastforce+

lemma vert_bound: "\<lbrakk>x \<in> L \<union> R; n \<le> length ys\<rbrakk> \<Longrightarrow> x < length ys"
  using verts_below
  by auto

lemma vert_K: "x \<in> L \<union> R \<Longrightarrow> x \<in> K"
  using verts_below verts_K
  by auto

lemma edge_K:
  assumes "e \<in> E"
  shows "efst e \<in> K" "esnd e \<in> K"
  using assms vert_K fst_in snd_in
  by auto

lemma below_n_props:
  "x < n \<Longrightarrow> x \<in> K" "\<not> x < n \<Longrightarrow> x \<notin> L"
  using verts_K verts_below
  by auto

lemma elist_sub: "set elist \<subseteq> E"
  by (simp add: elist_E)

lemma \<^marker>\<open>provenance ai_human\<close> feas_loop_rule:
  assumes "set xs \<subseteq> E" "n \<le> length ys"
  shows "<EA p * yl_assn ys Ya * EI p xs it> code.feas_loop neg t p Ya it
         <\<lambda>r. EA p * yl_assn ys Ya * true * \<up>(r = list_all (feas_ok neg t ys) xs)>"
  using assms(1)
proof(induction xs arbitrary: it)
  case Nil
  show ?case
    by (subst code.feas_loop.simps) (sep_auto heap: es.it_has_next_rule)
next
  case (Cons e xs)
  note e = Cons.prems[simplified]
  show ?case
    by (subst code.feas_loop.simps)
       (sep_auto heap: es.it_has_next_rule es.it_next_rule es.fst_rule[of e] es.snd_rule[of e]
                       es.w_rule[of e] yl.nth_rule Cons.IH simp: e assms(2) edge_bounds feas_ok_def)
qed

lemma \<^marker>\<open>provenance ai_human\<close> match_loop_rule:
  assumes "k = length ms" "n \<le> length ys" "i \<le> k"
  shows "<EA p * yl_assn ys Ya * el_assn ms Ma * mark_assn U Ui> code.match_loop neg t p Ya Ma i k Ui
         <\<lambda>r. EA p * yl_assn ys Ya * el_assn ms Ma *
              mark_assn (fst (match_list neg t ys U (drop i ms))) Ui *
              \<up>(r = snd (match_list neg t ys U (drop i ms)))>"
  using assms(3)
proof(induction arbitrary: U rule: inc_induct)
  case base
  show ?case
    by (subst code.match_loop.simps) (sep_auto simp: assms(1))
next
  case (step i)
  show ?case
  proof(cases "ms ! i \<in> E")
    case False
    show ?thesis
      by (subst code.match_loop.simps)
         (sep_auto heap: el.nth_rule es.memb_rule
                   simp: step.hyps assms(1)[symmetric] Cons_nth_drop_Suc[symmetric] False)
  next
    case True
    show ?thesis
      by (subst code.match_loop.simps)
         (sep_auto heap: el.nth_rule es.memb_rule es.fst_rule[OF True] es.snd_rule[OF True]
                         es.w_rule[OF True] mark_memb_rule mark_ins_rule yl.nth_rule step.IH
                   simp: step.hyps assms(1)[symmetric] assms(2) Cons_nth_drop_Suc[symmetric] True
                         edge_bounds edge_K tight_ok_def)
  qed
qed

lemma \<^marker>\<open>provenance ai_human\<close> vert_loop_rule:
  assumes "k = length xs" "set xs \<subseteq> L \<union> R" "n \<le> length ys" "i \<le> k"
  shows "<yl_assn ys Ya * vl_assn xs Va * mark_assn U Ui> code.vert_loop Ya Va i k Ui
         <\<lambda>r. yl_assn ys Ya * vl_assn xs Va * mark_assn U Ui *
              \<up>(r = list_all (vert_ok ys U) (drop i xs))>"
  using assms(4)
proof(induction rule: inc_induct)
  case base
  show ?case
    by (subst code.vert_loop.simps) (sep_auto simp: assms(1))
next
  case (step i)
  have "xs ! i \<in> L \<union> R"
    using step.hyps assms(1,2) nth_mem[of i xs]
    by blast
  thus ?case
    by (subst code.vert_loop.simps)
       (sep_auto heap: vl.nth_rule yl.nth_rule mark_memb_rule step.IH
                 simp: step.hyps assms(1)[symmetric] assms(3) Cons_nth_drop_Suc[symmetric] vert_bound
                       vert_K vert_ok_def)
qed

lemma certify_alt:
  "certify_sh neg perfect t ms ys =
   (n \<le> length ys \<and> list_all (feas_ok neg t ys) elist \<and> snd (match_list neg t ys {} ms) \<and>
    (if perfect then length ms = length ls \<and> length ls = length rs
     else list_all (vert_ok ys (fst (match_list neg t ys {} ms))) ls \<and>
          list_all (vert_ok ys (fst (match_list neg t ys {} ms))) rs))"
  by (simp add: certify_sh_def split: prod.split)

lemma \<^marker>\<open>provenance ai_human\<close> certify_sh_imp_rule:
  "<EA p * vl_assn ls La * vl_assn rs Ra * el_assn ms Ma * yl_assn ys Ya * mark_assn {} Ui>
   code.certify_sh_imp neg perfect t n p La Ra Ma Ya Ui
   <\<lambda>r. EA p * vl_assn ls La * vl_assn rs Ra * el_assn ms Ma * yl_assn ys Ya * true *
        \<up>(r = certify_sh neg perfect t ms ys)>"
proof(cases "n \<le> length ys")
  case False
  thus ?thesis
    unfolding code.certify_sh_imp_def
    by (sep_auto heap: yl.len_rule simp: certify_alt)
next
  case True
  note vls = vert_loop_rule[OF refl _ True le0, where xs = ls]
   and vrs = vert_loop_rule[OF refl _ True le0, where xs = rs]
  show ?thesis
    unfolding code.certify_sh_imp_def
    by (sep_auto heap: yl.len_rule es.it_init_rule[OF E_invar, folded elist_lst] feas_loop_rule[OF elist_sub True]
                       el.len_rule match_loop_rule[OF refl True le0] vl.len_rule vls vrs
                 simp: True certify_alt)
qed

lemma \<^marker>\<open>provenance ai_human\<close> certify_imp_rule:
  "<EA p * vl_assn ls La * vl_assn rs Ra * el_assn ms Ma * yl_assn ys Ya * mark_assn {} Ui>
   code.certify_imp neg perfect n p La Ra Ma Ya Ui
   <\<lambda>r. EA p * vl_assn ls La * vl_assn rs Ra * el_assn ms Ma * yl_assn ys Ya * true *
        \<up>(r = certify neg perfect ms ys)>"
  unfolding code.certify_imp_def certify_def
  by (rule certify_sh_imp_rule)

subsubsection \<open>Hall Violators\<close>

lemma \<^marker>\<open>provenance ai_human\<close> insert_loop_rule:
  assumes "k = length xs" "set xs \<subseteq> K" "i \<le> k"
  shows "<vl_assn xs Va * mark_assn U Ui> code.insert_loop Va i k Ui
         <\<lambda>_. vl_assn xs Va * mark_assn (U \<union> set (drop i xs)) Ui>"
  using assms(3)
proof(induction arbitrary: U rule: inc_induct)
  case base
  show ?case
    by (subst code.insert_loop.simps) (sep_auto simp: assms(1))
next
  case (step i)
  have "xs ! i \<in> K"
    using step.hyps assms(1,2)
    by auto
  thus ?case
    by (subst code.insert_loop.simps)
       (sep_auto heap: vl.nth_rule mark_ins_rule step.IH
                 simp: step.hyps assms(1)[symmetric] Cons_nth_drop_Suc[symmetric])
qed

lemma \<^marker>\<open>provenance ai_human\<close> hall_S_loop_rule:
  assumes "k = length S" "i \<le> k"
  shows "<vl_assn S Sa * mark_assn L Li * mark_assn Sm Si> code.hall_S_loop n Li Sa i k Si c
         <\<lambda>(c', ok). vl_assn S Sa * mark_assn L Li * mark_assn (fst (hall_S Sm c (drop i S))) Si *
                     \<up>(c' = fst (snd (hall_S Sm c (drop i S))) \<and>
                       ok = snd (snd (hall_S Sm c (drop i S))))>"
  using assms(2)
proof(induction arbitrary: Sm c rule: inc_induct)
  case base
  show ?case
    by (subst code.hall_S_loop.simps) (sep_auto simp: assms(1))
next
  case (step i)
  show ?case
  proof(cases "S ! i < n")
    case True
    show ?thesis
      by (subst code.hall_S_loop.simps)
         (sep_auto heap: vl.nth_rule mark_memb_rule mark_ins_rule step.IH
                   simp: step.hyps assms(1)[symmetric] Cons_nth_drop_Suc[symmetric] True below_n_props)
  next
    case False
    show ?thesis
      by (subst code.hall_S_loop.simps)
         (sep_auto heap: vl.nth_rule
                   simp: step.hyps assms(1)[symmetric] Cons_nth_drop_Suc[symmetric] False below_n_props)
  qed
qed

lemma \<^marker>\<open>provenance ai_human\<close> hall_N_loop_rule:
  assumes "set xs \<subseteq> E"
  shows "<EA p * mark_assn Sm Si * mark_assn Nm Ni * EI p xs it> code.hall_N_loop p Si it Ni c
         <\<lambda>c'. EA p * mark_assn Sm Si * mark_assn (fst (hall_N Sm Nm c xs)) Ni * true *
              \<up>(c' = snd (hall_N Sm Nm c xs))>"
  using assms
proof(induction xs arbitrary: it Nm c)
  case Nil
  show ?case
    by (subst code.hall_N_loop.simps) (sep_auto heap: es.it_has_next_rule)
next
  case (Cons e xs)
  note e = Cons.prems[simplified]
  show ?case
    by (subst code.hall_N_loop.simps)
       (sep_auto heap: es.it_has_next_rule es.it_next_rule es.fst_rule[of e] es.snd_rule[of e]
                       mark_memb_rule mark_ins_rule Cons.IH simp: e edge_K)
qed

lemma hall_check_alt:
  "hall_check S =
   (length ls \<noteq> length rs \<or>
    (snd (snd (hall_S {} 0 S)) \<and>
     snd (hall_N (fst (hall_S {} 0 S)) {} 0 elist) < fst (snd (hall_S {} 0 S))))"
  by (simp add: hall_check_def split: prod.split)

lemma ls_K: "set ls \<subseteq> K"
  using vert_K
  by blast

lemma \<^marker>\<open>provenance ai_human\<close> hall_imp_rule:
  "<EA p * vl_assn ls La * vl_assn rs Ra * vl_assn S Sa * mark_assn {} Li * mark_assn {} Si *
    mark_assn {} Ni>
   code.hall_imp n p La Ra Sa Li Si Ni
   <\<lambda>r. EA p * vl_assn ls La * vl_assn rs Ra * vl_assn S Sa * true * \<up>(r = hall_check S)>"
  unfolding code.hall_imp_def
  by (sep_auto heap: vl.len_rule insert_loop_rule[OF refl ls_K le0, where U = "{}"]
                     hall_S_loop_rule[OF refl le0, where Sm = "{}" and c = 0]
                     es.it_init_rule[OF E_invar, folded elist_lst]
                     hall_N_loop_rule[OF elist_sub, where Nm = "{}" and c = 0]
               simp: hall_check_alt)

subsubsection \<open>Extremal Weight Maximum Cardinality Matchings\<close>

lemma defic_ok_alt:
  "defic_ok ms S =
   (snd (snd (hall_S {} 0 S)) \<and>
    length ls + snd (hall_N (fst (hall_S {} 0 S)) {} 0 elist) \<le> length ms + fst (snd (hall_S {} 0 S)))"
  by (simp add: defic_ok_def split: prod.split)

lemma \<^marker>\<open>provenance ai_human\<close> certify_mc_imp_rule:
  "<EA p * vl_assn ls La * vl_assn rs Ra * el_assn ms Ma * yl_assn ys Ya * vl_assn S Sa *
    mark_assn {} Ui * mark_assn {} Li * mark_assn {} Si * mark_assn {} Ni>
   code.certify_mc_imp neg n p La Ra Ma Ya t Sa Ui Li Si Ni
   <\<lambda>r. EA p * vl_assn ls La * vl_assn rs Ra * el_assn ms Ma * yl_assn ys Ya * vl_assn S Sa *
        true * \<up>(r = certify_mc neg ms ys t S)>"
  unfolding code.certify_mc_imp_def
  by (sep_auto heap: certify_sh_imp_rule vl.len_rule insert_loop_rule[OF refl ls_K le0, where U = "{}"]
                     hall_S_loop_rule[OF refl le0, where Sm = "{}" and c = 0]
                     es.it_init_rule[OF E_invar, folded elist_lst]
                     hall_N_loop_rule[OF elist_sub, where Nm = "{}" and c = 0] el.len_rule
               simp: certify_mc_def defic_ok_alt)

end

end
