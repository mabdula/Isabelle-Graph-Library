theory Matching_Certificate_Imperative
  imports
    Hungarian_Method.Matching_Certificate_Spec
    Separation_Logic_Imperative_HOL_Partial.Sep_Main
    Data_Structures.Fixed_Univ_Set_Specs_Imp
begin

section \<open>Certificate Checkers for Extremal Bipartite Matchings: Imperative Refinement\<close>

subsection \<open>The Interfaces\<close>

text \<open>Read-only lists with random access. They hold the candidate matching, the potentials, the
      Hall violator and the vertex lists.\<close>

locale imp_rlist =
  fixes rl_assn :: "'a list \<Rightarrow> 'p \<Rightarrow> assn"
    and len_imp :: "'p \<Rightarrow> nat Heap"
    and nth_imp :: "'p \<Rightarrow> nat \<Rightarrow> 'a Heap"
  assumes len_rule: "<rl_assn xs p> len_imp p <\<lambda>r. rl_assn xs p * \<up>(r = length xs)>"
    and nth_rule: "i < length xs \<Longrightarrow> <rl_assn xs p> nth_imp p i <\<lambda>r. rl_assn xs p * \<up>(r = xs ! i)>"

text \<open>The edges: an iterable set of edge names with membership, and the left endpoint, the right
      endpoint and the weight of every edge. The iterator enumerates the set in the order
      @{term elst}.\<close>

locale imp_edge_set =
  fixes es_assn :: "'e set \<Rightarrow> ('e \<Rightarrow> nat) \<Rightarrow> ('e \<Rightarrow> nat) \<Rightarrow> ('e \<Rightarrow> 'n) \<Rightarrow> 'p \<Rightarrow> assn"
    and elst :: "'e set \<Rightarrow> 'e list"
    and it_assn :: "'e list \<Rightarrow> 'it \<Rightarrow> assn"
    and memb_imp :: "'p \<Rightarrow> 'e \<Rightarrow> bool Heap"
    and fst_imp :: "'p \<Rightarrow> 'e \<Rightarrow> nat Heap"
    and snd_imp :: "'p \<Rightarrow> 'e \<Rightarrow> nat Heap"
    and w_imp :: "'p \<Rightarrow> 'e \<Rightarrow> 'n Heap"
    and it_init :: "'p \<Rightarrow> 'it Heap"
    and it_has_next :: "'p \<Rightarrow> 'it \<Rightarrow> bool Heap"
    and it_next :: "'p \<Rightarrow> 'it \<Rightarrow> ('e \<times> 'it) Heap"
  assumes memb_rule:
      "<es_assn D F T W p> memb_imp p e <\<lambda>r. es_assn D F T W p * \<up>(r \<longleftrightarrow> e \<in> D)>"
    and fst_rule: "e \<in> D \<Longrightarrow> <es_assn D F T W p> fst_imp p e <\<lambda>r. es_assn D F T W p * \<up>(r = F e)>"
    and snd_rule: "e \<in> D \<Longrightarrow> <es_assn D F T W p> snd_imp p e <\<lambda>r. es_assn D F T W p * \<up>(r = T e)>"
    and w_rule: "e \<in> D \<Longrightarrow> <es_assn D F T W p> w_imp p e <\<lambda>r. es_assn D F T W p * \<up>(r = W e)>"
    and it_init_rule: "<es_assn D F T W p> it_init p <\<lambda>it. es_assn D F T W p * it_assn (elst D) it>"
    and it_has_next_rule:
      "<es_assn D F T W p * it_assn xs it> it_has_next p it
       <\<lambda>r. es_assn D F T W p * it_assn xs it * \<up>(r \<longleftrightarrow> xs \<noteq> [])>"
    and it_next_rule:
      "<es_assn D F T W p * it_assn (x # xs) it> it_next p it
       <\<lambda>(y, it'). es_assn D F T W p * it_assn xs it' * \<up>(y = x)>"

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
    and it_has_next :: "'p \<Rightarrow> 'it \<Rightarrow> bool Heap"
    and it_next :: "'p \<Rightarrow> 'it \<Rightarrow> ('e \<times> 'it) Heap"
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

partial_function (heap) feas_loop :: "bool \<Rightarrow> 'n \<Rightarrow> 'p \<Rightarrow> 'py \<Rightarrow> 'it \<Rightarrow> bool Heap" where
  "feas_loop neg t p Ya it = do {
     b \<leftarrow> it_has_next p it;
     (if b then do {
        (e, it') \<leftarrow> it_next p it;
        u \<leftarrow> fst_imp p e;
        v \<leftarrow> snd_imp p e;
        c \<leftarrow> w_imp p e;
        yu \<leftarrow> ynth Ya u;
        yv \<leftarrow> ynth Ya v;
        (if yu + yv + t \<le> sgn_c neg c then feas_loop neg t p Ya it' else return False) }
      else return True) }"

text \<open>The candidate matching: membership of the names, disjointness and tightness.\<close>

partial_function (heap) match_loop ::
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

partial_function (heap) vert_loop :: "'py \<Rightarrow> 'pv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> bool Heap" where
  "vert_loop Ya Va i k Ui =
     (if i < k then do {
        x \<leftarrow> vnth Va i;
        y \<leftarrow> ynth Ya x;
        b \<leftarrow> smemb Ui x;
        (if y \<le> 0 \<and> (y \<noteq> 0 \<longrightarrow> b) then vert_loop Ya Va (Suc i) k Ui else return False) }
      else return True)"

definition certify_sh_imp ::
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

definition certify_imp ::
  "bool \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> 'p \<Rightarrow> 'pv \<Rightarrow> 'pv \<Rightarrow> 'pe \<Rightarrow> 'py \<Rightarrow> 's \<Rightarrow> bool Heap" where
  "certify_imp neg perfect = certify_sh_imp neg perfect 0"

text \<open>Hall violators. The entries of the violator are input: the ones not below @{term n} are
      rejected before the mark sets are read.\<close>

partial_function (heap) insert_loop :: "'pv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> unit Heap" where
  "insert_loop Va i k Ui =
     (if i < k then do { x \<leftarrow> vnth Va i; sins x Ui; insert_loop Va (Suc i) k Ui }
      else return ())"

partial_function (heap) hall_S_loop ::
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

partial_function (heap) hall_N_loop :: "'p \<Rightarrow> 's \<Rightarrow> 'it \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "hall_N_loop p Si it Ni c = do {
     b \<leftarrow> it_has_next p it;
     (if b then do {
        (e, it') \<leftarrow> it_next p it;
        u \<leftarrow> fst_imp p e;
        v \<leftarrow> snd_imp p e;
        bu \<leftarrow> smemb Si u;
        bv \<leftarrow> smemb Ni v;
        (if bu \<and> \<not> bv then do { sins v Ni; hall_N_loop p Si it' Ni (Suc c) }
         else hall_N_loop p Si it' Ni c) }
      else return c) }"

definition hall_imp :: "nat \<Rightarrow> 'p \<Rightarrow> 'pv \<Rightarrow> 'pv \<Rightarrow> 'pv \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool Heap" where
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

definition certify_mc_imp ::
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
  es: imp_edge_set es_assn elst it_assn memb_imp fst_imp snd_imp w_imp it_init it_has_next it_next +
  el: imp_rlist el_assn elen enth +
  yl: imp_rlist yl_assn ylen ynth +
  vl: imp_rlist vl_assn vlen vnth +
  mk: fixed_univ_set_imp K sinvar sabs sempty sinsert sdelete sisin set_assn sempty_imp sins sdel
        smemb
  for E :: "'e set" and elist efst esnd and ew :: "'e \<Rightarrow> 'n::linordered_idom" and n ls rs h
    and es_assn :: "'e set \<Rightarrow> ('e \<Rightarrow> nat) \<Rightarrow> ('e \<Rightarrow> nat) \<Rightarrow> ('e \<Rightarrow> 'n) \<Rightarrow> 'p \<Rightarrow> assn"
    and elst and it_assn :: "'e list \<Rightarrow> 'it \<Rightarrow> assn"
    and memb_imp fst_imp snd_imp w_imp it_init it_has_next it_next
    and el_assn :: "'e list \<Rightarrow> 'pe \<Rightarrow> assn" and elen enth
    and yl_assn :: "'n list \<Rightarrow> 'py \<Rightarrow> assn" and ylen ynth
    and vl_assn :: "nat list \<Rightarrow> 'pv \<Rightarrow> assn" and vlen vnth
    and K :: "nat set" and sinvar :: "'set \<Rightarrow> bool" and sabs sempty sinsert sdelete sisin
    and set_assn :: "'set \<Rightarrow> 's \<Rightarrow> assn" and sempty_imp sins sdel smemb +
  assumes elist_elst: "elist = elst E"
    and verts_K: "{..<n} \<subseteq> K"

sublocale matching_cert_imp \<subseteq> code: matching_cert_imp_code
  memb_imp fst_imp snd_imp w_imp it_init it_has_next it_next elen enth ylen ynth vlen vnth
  smemb sins .

context matching_cert_imp
begin

abbreviation "EA p \<equiv> es_assn E efst esnd ew p"

text \<open>A mark set, up to abstraction.\<close>

definition "mark_assn U Ui = (\<exists>\<^sub>AS. set_assn S Ui * \<up>(sinvar S \<and> sabs S = U))"

lemma mark_empty_rule: "<emp> sempty_imp <mark_assn {}>"
  unfolding mark_assn_def
  by (sep_auto heap: mk.fixed_univ_set_empty_rule simp: mk.fixed_univ_set_empty)

lemma mark_memb_rule:
  "x \<in> K \<Longrightarrow> <mark_assn U Ui> smemb Ui x <\<lambda>r. mark_assn U Ui * \<up>(r \<longleftrightarrow> x \<in> U)>"
  unfolding mark_assn_def
  by (sep_auto heap: mk.fixed_univ_set_isin_rule simp: mk.fixed_univ_set_isin)

lemma mark_ins_rule:
  "x \<in> K \<Longrightarrow> <mark_assn U Ui> sins x Ui <\<lambda>_. mark_assn (insert x U) Ui>"
  unfolding mark_assn_def
  by (sep_auto heap: mk.fixed_univ_set_insert_rule simp: mk.fixed_univ_set_insert)

lemma edge_bounds:
  assumes "e \<in> E" "n \<le> length ys"
  shows "efst e < length ys" "esnd e < length ys"
proof -
  have "efst e \<in> L" "esnd e \<in> R" using fst_in[OF assms(1)] snd_in[OF assms(1)] .
  thus "efst e < length ys" "esnd e < length ys" using verts_below assms(2) by auto
qed

lemma vert_bound: "\<lbrakk>x \<in> L \<union> R; n \<le> length ys\<rbrakk> \<Longrightarrow> x < length ys"
  using verts_below by auto

lemma vert_K: "x \<in> L \<union> R \<Longrightarrow> x \<in> K"
  using verts_below verts_K by auto

lemma edge_K:
  assumes "e \<in> E"
  shows "efst e \<in> K" "esnd e \<in> K"
  using vert_K fst_in[OF assms] snd_in[OF assms] by auto

lemma feas_loop_rule:
  assumes "set xs \<subseteq> E" "n \<le> length ys"
  shows "<EA p * yl_assn ys Ya * it_assn xs it> code.feas_loop neg t p Ya it
         <\<lambda>r. EA p * yl_assn ys Ya * true * \<up>(r = list_all (feas_ok neg t ys) xs)>"
  using assms(1)
proof (induction xs arbitrary: it)
  case Nil
  show ?case by (subst code.feas_loop.simps) (sep_auto heap: es.it_has_next_rule)
next
  case (Cons e xs)
  have e: "e \<in> E" and xs: "set xs \<subseteq> E" using Cons.prems by simp_all
  note b = edge_bounds[OF e assms(2)]
  note ih = Cons.IH[OF xs]
  show ?case
    by (subst code.feas_loop.simps)
       (sep_auto heap: es.it_has_next_rule es.it_next_rule es.fst_rule[OF e] es.snd_rule[OF e]
                       es.w_rule[OF e] yl.nth_rule ih simp: b feas_ok_def)
qed

lemma match_loop_rule:
  assumes "k = length ms" "n \<le> length ys"
  shows "i \<le> k \<Longrightarrow>
         <EA p * yl_assn ys Ya * el_assn ms Ma * mark_assn U Ui> code.match_loop neg t p Ya Ma i k Ui
         <\<lambda>r. EA p * yl_assn ys Ya * el_assn ms Ma *
              mark_assn (fst (match_list neg t ys U (drop i ms))) Ui *
              \<up>(r = snd (match_list neg t ys U (drop i ms)))>"
proof (induction "k - i" arbitrary: i U)
  case 0
  hence ik: "i = k" by simp
  show ?case by (subst code.match_loop.simps) (sep_auto simp: ik assms(1))
next
  case (Suc d)
  hence i: "i < k" by simp
  have dr: "drop i ms = ms ! i # drop (Suc i) ms" using i assms(1) by (simp add: Cons_nth_drop_Suc)
  have ih: "<EA p * yl_assn ys Ya * el_assn ms Ma * mark_assn U' Ui>
            code.match_loop neg t p Ya Ma (Suc i) k Ui
            <\<lambda>r. EA p * yl_assn ys Ya * el_assn ms Ma *
                 mark_assn (fst (match_list neg t ys U' (drop (Suc i) ms))) Ui *
                 \<up>(r = snd (match_list neg t ys U' (drop (Suc i) ms)))>" for U'
    using Suc.hyps(1)[of "Suc i" U'] Suc.hyps(2) i by simp
  have il: "i < length ms" using i assms(1) by simp
  show ?case
  proof (cases "ms ! i \<in> E")
    case False
    show ?thesis
      by (subst code.match_loop.simps)
         (sep_auto heap: el.nth_rule es.memb_rule simp: i il dr False)
  next
    case True
    note b = edge_bounds[OF True assms(2)] and kk = edge_K[OF True]
    show ?thesis
      by (subst code.match_loop.simps)
         (sep_auto heap: el.nth_rule es.memb_rule es.fst_rule[OF True] es.snd_rule[OF True]
                         es.w_rule[OF True] mark_memb_rule mark_ins_rule yl.nth_rule ih
                   simp: i il dr True b kk tight_ok_def)
  qed
qed

lemma vert_loop_rule:
  assumes "k = length xs" "set xs \<subseteq> L \<union> R" "n \<le> length ys"
  shows "i \<le> k \<Longrightarrow>
         <yl_assn ys Ya * vl_assn xs Va * mark_assn U Ui> code.vert_loop Ya Va i k Ui
         <\<lambda>r. yl_assn ys Ya * vl_assn xs Va * mark_assn U Ui *
              \<up>(r = list_all (vert_ok ys U) (drop i xs))>"
proof (induction "k - i" arbitrary: i)
  case 0
  hence ik: "i = k" by simp
  show ?case by (subst code.vert_loop.simps) (sep_auto simp: ik assms(1))
next
  case (Suc d)
  hence i: "i < k" by simp
  have dr: "drop i xs = xs ! i # drop (Suc i) xs" using i assms(1) by (simp add: Cons_nth_drop_Suc)
  have ih: "<yl_assn ys Ya * vl_assn xs Va * mark_assn U Ui> code.vert_loop Ya Va (Suc i) k Ui
            <\<lambda>r. yl_assn ys Ya * vl_assn xs Va * mark_assn U Ui *
                 \<up>(r = list_all (vert_ok ys U) (drop (Suc i) xs))>"
    using Suc.hyps(1)[of "Suc i"] Suc.hyps(2) i by simp
  have il: "i < length xs" using i assms(1) by simp
  have xLR: "xs ! i \<in> L \<union> R" using assms(2) il nth_mem by blast
  note b = vert_bound[OF xLR assms(3)] and kx = vert_K[OF xLR]
  show ?case
    by (subst code.vert_loop.simps)
       (sep_auto heap: vl.nth_rule yl.nth_rule mark_memb_rule ih simp: i il dr b kx vert_ok_def)
qed

lemma certify_alt:
  "certify_sh neg perfect t ms ys =
   (n \<le> length ys \<and> list_all (feas_ok neg t ys) elist \<and> snd (match_list neg t ys {} ms) \<and>
    (if perfect then length ms = length ls \<and> length ls = length rs
     else list_all (vert_ok ys (fst (match_list neg t ys {} ms))) ls \<and>
          list_all (vert_ok ys (fst (match_list neg t ys {} ms))) rs))"
  by (simp add: certify_sh_def split: prod.split)

theorem certify_sh_imp_rule:
  "<EA p * vl_assn ls La * vl_assn rs Ra * el_assn ms Ma * yl_assn ys Ya * mark_assn {} Ui>
   code.certify_sh_imp neg perfect t n p La Ra Ma Ya Ui
   <\<lambda>r. EA p * vl_assn ls La * vl_assn rs Ra * el_assn ms Ma * yl_assn ys Ya * true *
        \<up>(r = certify_sh neg perfect t ms ys)>"
proof (cases "n \<le> length ys")
  case False
  show ?thesis unfolding code.certify_sh_imp_def by (sep_auto heap: yl.len_rule simp: False certify_alt)
next
  case True
  have el: "set elist \<subseteq> E" using elist_E by simp
  note init = es.it_init_rule[where D = E, folded elist_elst]
  note feas = feas_loop_rule[OF el True]
  note match = match_loop_rule[OF refl True, where i = 0]
  note vls = vert_loop_rule[OF refl _ True, where xs = ls and i = 0]
   and vrs = vert_loop_rule[OF refl _ True, where xs = rs and i = 0]
  show ?thesis unfolding code.certify_sh_imp_def
    by (sep_auto heap: yl.len_rule init feas el.len_rule match vl.len_rule vls vrs
                 simp: True certify_alt)
qed

theorem certify_imp_rule:
  "<EA p * vl_assn ls La * vl_assn rs Ra * el_assn ms Ma * yl_assn ys Ya * mark_assn {} Ui>
   code.certify_imp neg perfect n p La Ra Ma Ya Ui
   <\<lambda>r. EA p * vl_assn ls La * vl_assn rs Ra * el_assn ms Ma * yl_assn ys Ya * true *
        \<up>(r = certify neg perfect ms ys)>"
  unfolding code.certify_imp_def certify_def by (rule certify_sh_imp_rule)

subsubsection \<open>Hall Violators\<close>

lemma insert_loop_rule:
  assumes "k = length xs" "set xs \<subseteq> K"
  shows "i \<le> k \<Longrightarrow>
         <vl_assn xs Va * mark_assn U Ui> code.insert_loop Va i k Ui
         <\<lambda>_. vl_assn xs Va * mark_assn (U \<union> set (drop i xs)) Ui>"
proof (induction "k - i" arbitrary: i U)
  case 0
  hence ik: "i = k" by simp
  show ?case by (subst code.insert_loop.simps) (sep_auto simp: ik assms(1))
next
  case (Suc d)
  hence i: "i < k" by simp
  have dr: "drop i xs = xs ! i # drop (Suc i) xs" using i assms(1) by (simp add: Cons_nth_drop_Suc)
  have ih: "<vl_assn xs Va * mark_assn U' Ui> code.insert_loop Va (Suc i) k Ui
            <\<lambda>_. vl_assn xs Va * mark_assn (U' \<union> set (drop (Suc i) xs)) Ui>" for U'
    using Suc.hyps(1)[of "Suc i" U'] Suc.hyps(2) i by simp
  have il: "i < length xs" using i assms(1) by simp
  have kx: "xs ! i \<in> K" using assms(2) il nth_mem by blast
  show ?case
    by (subst code.insert_loop.simps)
       (sep_auto heap: vl.nth_rule mark_ins_rule ih simp: i il dr kx)
qed

lemma hall_S_loop_rule:
  assumes "k = length S"
  shows "i \<le> k \<Longrightarrow>
         <vl_assn S Sa * mark_assn L Li * mark_assn Sm Si> code.hall_S_loop n Li Sa i k Si c
         <\<lambda>(c', ok). vl_assn S Sa * mark_assn L Li * mark_assn (fst (hall_S Sm c (drop i S))) Si *
                     \<up>(c' = fst (snd (hall_S Sm c (drop i S))) \<and>
                       ok = snd (snd (hall_S Sm c (drop i S))))>"
proof (induction "k - i" arbitrary: i Sm c)
  case 0
  hence ik: "i = k" by simp
  show ?case by (subst code.hall_S_loop.simps) (sep_auto simp: ik assms(1))
next
  case (Suc d)
  hence i: "i < k" by simp
  have dr: "drop i S = S ! i # drop (Suc i) S" using i assms(1) by (simp add: Cons_nth_drop_Suc)
  have ih: "<vl_assn S Sa * mark_assn L Li * mark_assn Sm' Si> code.hall_S_loop n Li Sa (Suc i) k Si c'
            <\<lambda>(c'', ok). vl_assn S Sa * mark_assn L Li *
                         mark_assn (fst (hall_S Sm' c' (drop (Suc i) S))) Si *
                         \<up>(c'' = fst (snd (hall_S Sm' c' (drop (Suc i) S))) \<and>
                           ok = snd (snd (hall_S Sm' c' (drop (Suc i) S))))>" for Sm' c'
    using Suc.hyps(1)[of "Suc i" Sm' c'] Suc.hyps(2) i by simp
  have il: "i < length S" using i assms(1) by simp
  show ?case
  proof (cases "S ! i < n")
    case True
    have kx: "S ! i \<in> K" using True verts_K by auto
    show ?thesis
      by (subst code.hall_S_loop.simps)
         (sep_auto heap: vl.nth_rule mark_memb_rule mark_ins_rule ih simp: i il dr True kx)
  next
    case False
    have nL: "S ! i \<notin> L" using False verts_below by auto
    show ?thesis
      by (subst code.hall_S_loop.simps) (sep_auto heap: vl.nth_rule simp: i il dr False nL)
  qed
qed

lemma hall_N_loop_rule:
  assumes "set xs \<subseteq> E"
  shows "<EA p * mark_assn Sm Si * mark_assn Nm Ni * it_assn xs it> code.hall_N_loop p Si it Ni c
         <\<lambda>c'. EA p * mark_assn Sm Si * mark_assn (fst (hall_N Sm Nm c xs)) Ni * true *
              \<up>(c' = snd (hall_N Sm Nm c xs))>"
  using assms
proof (induction xs arbitrary: it Nm c)
  case Nil
  show ?case by (subst code.hall_N_loop.simps) (sep_auto heap: es.it_has_next_rule)
next
  case (Cons e xs)
  have e: "e \<in> E" and xs: "set xs \<subseteq> E" using Cons.prems by simp_all
  note ih = Cons.IH[OF xs] and kk = edge_K[OF e]
  show ?case
    by (subst code.hall_N_loop.simps)
       (sep_auto heap: es.it_has_next_rule es.it_next_rule es.fst_rule[OF e] es.snd_rule[OF e]
                       mark_memb_rule mark_ins_rule ih simp: kk)
qed

lemma hall_check_alt:
  "hall_check S =
   (length ls \<noteq> length rs \<or>
    (snd (snd (hall_S {} 0 S)) \<and>
     snd (hall_N (fst (hall_S {} 0 S)) {} 0 elist) < fst (snd (hall_S {} 0 S))))"
  by (simp add: hall_check_def split: prod.split)

lemma ls_K: "set ls \<subseteq> K"
  using vert_K by blast

theorem hall_imp_rule:
  "<EA p * vl_assn ls La * vl_assn rs Ra * vl_assn S Sa * mark_assn {} Li * mark_assn {} Si *
    mark_assn {} Ni>
   code.hall_imp n p La Ra Sa Li Si Ni
   <\<lambda>r. EA p * vl_assn ls La * vl_assn rs Ra * vl_assn S Sa * true * \<up>(r = hall_check S)>"
proof -
  have el: "set elist \<subseteq> E" using elist_E by simp
  note init = es.it_init_rule[where D = E, folded elist_elst]
  note ins = insert_loop_rule[OF refl ls_K, where i = 0 and U = "{}"]
  note hS = hall_S_loop_rule[OF refl, where i = 0 and Sm = "{}" and c = 0]
  note hN = hall_N_loop_rule[OF el, where Nm = "{}" and c = 0]
  show ?thesis unfolding code.hall_imp_def
    by (sep_auto heap: vl.len_rule ins hS init hN simp: hall_check_alt)
qed

subsubsection \<open>Extremal Weight Maximum Cardinality Matchings\<close>

lemma defic_ok_alt:
  "defic_ok ms S =
   (snd (snd (hall_S {} 0 S)) \<and>
    length ls + snd (hall_N (fst (hall_S {} 0 S)) {} 0 elist) \<le> length ms + fst (snd (hall_S {} 0 S)))"
  by (simp add: defic_ok_def split: prod.split)

theorem certify_mc_imp_rule:
  "<EA p * vl_assn ls La * vl_assn rs Ra * el_assn ms Ma * yl_assn ys Ya * vl_assn S Sa *
    mark_assn {} Ui * mark_assn {} Li * mark_assn {} Si * mark_assn {} Ni>
   code.certify_mc_imp neg n p La Ra Ma Ya t Sa Ui Li Si Ni
   <\<lambda>r. EA p * vl_assn ls La * vl_assn rs Ra * el_assn ms Ma * yl_assn ys Ya * vl_assn S Sa *
        true * \<up>(r = certify_mc neg ms ys t S)>"
proof -
  have el: "set elist \<subseteq> E" using elist_E by simp
  note init = es.it_init_rule[where D = E, folded elist_elst]
  note ins = insert_loop_rule[OF refl ls_K, where i = 0 and U = "{}"]
  note hS = hall_S_loop_rule[OF refl, where i = 0 and Sm = "{}" and c = 0]
  note hN = hall_N_loop_rule[OF el, where Nm = "{}" and c = 0]
  show ?thesis unfolding code.certify_mc_imp_def
    by (sep_auto heap: certify_sh_imp_rule vl.len_rule ins hS init hN el.len_rule
                 simp: certify_mc_def defic_ok_alt)
qed
end

end
