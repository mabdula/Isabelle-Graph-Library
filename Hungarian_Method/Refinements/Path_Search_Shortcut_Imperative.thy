theory Path_Search_Shortcut_Imperative
  imports
    Path_Search_Shortcut
    Neighbourhood_Best_Scan_Imperative
    Data_Structures.Fixed_Univ_Set_Iterate_Imp
    Data_Structures.Fixed_Univ_Map_Specs_Imp
begin

section \<open>The Imperative Shortcut\<close>

text \<open>The imperative counterpart of @{const path_search_shortcut_spec.sc_loop}. The free left
      vertices are taken from an iterator until a chain succeeds; the remaining iterator is
      returned. The cursors are not reset. The key of a neighbour @{term r} of @{term l} is its
      reduced cost, read at the cursor together with the information whether @{term r} is free.
      The potential and the matching are changed in place. A chain returns the end points of its
      path, which are written to the path array once, at the end. Nothing is allocated.\<close>

locale path_search_shortcut_imp_code =
  fixes nil :: "'v::heap"
    and cap :: nat
    and pot_get_imp :: "'pi \<Rightarrow> 'v \<Rightarrow> 'n::linordered_idom Heap"
    and pot_upd_imp :: "'pi \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> unit Heap"
    and buddy_imp :: "'bdi \<Rightarrow> 'v \<Rightarrow> 'v Heap"
    and rematch_imp :: "'bdi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and left_it_has_next :: "'lit \<Rightarrow> bool Heap"
    and left_it_next :: "'lit \<Rightarrow> ('v \<times> 'lit) Heap"
    and has_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> bool Heap"
    and current_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> 'v Heap"
    and current_cost_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> 'n Heap"
    and move_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
    and reset_imp :: "'ci \<Rightarrow> 'v \<Rightarrow> unit Heap"
begin

sublocale bs: nb_best_scan_imp_code has_imp move_imp reset_imp .

definition "cur_red_imp Pti Bdi Ci l = do {
   r \<leftarrow> current_imp Ci l;
   c \<leftarrow> current_cost_imp Ci l;
   p \<leftarrow> pot_get_imp Pti r;
   b \<leftarrow> buddy_imp Bdi r;
   return (c - p, r, b = nil) }"

definition "pot_shift_imp Pti l v r1 d = do {
   p1 \<leftarrow> pot_get_imp Pti r1;
   pot_upd_imp Pti l v;
   pot_upd_imp Pti r1 (p1 - d) }"

partial_function (heap) chain_imp :: "nat \<Rightarrow> 'ci \<Rightarrow> 'pi \<Rightarrow> 'bdi \<Rightarrow> 'v \<Rightarrow> ('v \<times> 'v) option Heap"
  where
  "chain_imp k Ci Pti Bdi l = do {
     bs \<leftarrow> bs.best_two_imp (cur_red_imp Pti Bdi) Ci l;
     (case bs of
        (None, _) \<Rightarrow> return None
      | (Some (u1, r1, f1), s) \<Rightarrow>
          if f1 then
            (case s of
               None \<Rightarrow> do { pot_upd_imp Pti l u1; return (Some (l, r1)) }
             | Some (u2, _) \<Rightarrow> do { pot_shift_imp Pti l u2 r1 (u2 - u1); return (Some (l, r1)) })
          else (case s of
                  None \<Rightarrow> return None
                | Some (u2, _) \<Rightarrow>
                    (case k of
                       0 \<Rightarrow> return None
                     | Suc k' \<Rightarrow> do {
                         lq \<leftarrow> buddy_imp Bdi r1;
                         pot_shift_imp Pti l u2 r1 (u2 - u1);
                         rematch_imp Bdi l r1;
                         chain_imp k' Ci Pti Bdi lq }))) }"

definition "sc_row_imp Ci Pti Bdi l = do {
   bl \<leftarrow> buddy_imp Bdi l;
   (if bl = nil then chain_imp cap Ci Pti Bdi l else return None) }"

partial_function (heap) sc_loop_imp ::
  "'ci \<Rightarrow> 'pi \<Rightarrow> 'bdi \<Rightarrow> 'lit \<Rightarrow> (('v \<times> 'v \<times> 'v) option \<times> 'lit) Heap" where
  "sc_loop_imp Ci Pti Bdi it = do {
     b \<leftarrow> left_it_has_next it;
     if b then do {
       (l, it') \<leftarrow> left_it_next it;
       r \<leftarrow> sc_row_imp Ci Pti Bdi l;
       (case r of
          None \<Rightarrow> sc_loop_imp Ci Pti Bdi it'
        | Some (a, b) \<Rightarrow> return (Some (l, a, b), it')) }
     else return (None, it) }"

definition "shortcut_imp Ci Pti Bdi Ra it = do {
   (r, it') \<leftarrow> sc_loop_imp Ci Pti Bdi it;
   (case r of
      None \<Rightarrow> return (False, it')
    | Some (_, a, b) \<Rightarrow> do {
        _ \<leftarrow> Array.upd 0 a Ra;
        _ \<leftarrow> Array.upd 1 b Ra;
        return (True, it') }) }"

end

text \<open>The universe @{term K} of the potential contains all vertices of the graph. The left
      vertices are an imperative fixed-universe set, iterated in the order @{term left_order}. The
      matching is an assertion @{term buddy_assn} with a lookup and a rematch.\<close>

locale path_search_shortcut_imp =
  path_search_shortcut where G = "G :: 'v set set"
    and potential_get = potential_get and potential_upd = potential_upd +
  bs: nb_best_scan_imp
    where rnb_current = rnb_current and rnb_has = rnb_has and rnb_move = rnb_move
      and rnb_reset = rnb_reset and rnb_invar = rnb_invar and rnb_abstract = rnb_abstract
      and rnb_iterated = rnb_iterated and rnb_remaining = rnb_remaining and K = K
      and h = h and cost = edge_costs_code and wval = h and nb_init = rnb_init
      and nb_assn = nb_assn and has_imp = has_imp and current_imp = current_imp
      and current_cost_imp = current_cost_imp and move_imp = move_imp and reset_imp = reset_imp
      and reset_all_imp = reset_all_imp +
  pot: fixed_univ_map_imp
    where K = K and fixed_univ_map_invar = potential_invar
      and fixed_univ_map_upd = potential_upd and fixed_univ_map_lookup = potential_get
      and fixed_univ_map_val = h and fixed_univ_map_assn = pot_assn
      and fixed_univ_map_upd_imp = pot_upd_imp and fixed_univ_map_lookup_imp = pot_get_imp +
  left: fixed_univ_set_iterate_imp
    where U = K and set_invar = vset_invar and set_abstract = vset_to_set
      and set_assn = vset_assn and lst = lst and is_it = left_is_it
      and it_init = left_it_init and it_has_next = left_it_has_next and it_next = left_it_next
  for G :: "'v::heap set set"
    and potential_get :: "'potential \<Rightarrow> 'v \<Rightarrow> real"
    and potential_upd :: "'potential \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'potential"
    and h :: "'n::{linordered_idom, heap} \<Rightarrow> real"
    and nb_assn has_imp current_imp current_cost_imp move_imp reset_imp reset_all_imp
    and pot_assn pot_upd_imp pot_get_imp
    and vset_invar vset_to_set vset_assn
    and lst :: "'v set \<Rightarrow> 'v list"
    and left_is_it left_it_init left_it_has_next left_it_next +
  fixes buddy_assn and buddy_imp and rematch_imp :: "'bdi \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> unit Heap" and left
  assumes buddy_rule[sep_heap_rules]:
      "v \<in> K \<Longrightarrow> <buddy_assn M Bdi> buddy_imp Bdi v <\<lambda>r. buddy_assn M Bdi * \<up>(r = buddy_get M v)>"
    and rematch_rule:
      "\<lbrakk>matching_invar M; {lq, r} \<in> matching_abstract M; l \<notin> Vs (matching_abstract M);
        {l, r} \<in> G\<rbrakk> \<Longrightarrow>
       <buddy_assn M Bdi> rematch_imp Bdi l r <\<lambda>_. buddy_assn (rematch M l r) Bdi>"
    and left: "vset_invar left" "vset_to_set left = L" "left_order = lst L"

sublocale path_search_shortcut_imp \<subseteq> code: path_search_shortcut_imp_code
  nil cap pot_get_imp pot_upd_imp buddy_imp rematch_imp left_it_has_next left_it_next has_imp
  current_imp current_cost_imp move_imp reset_imp .

context path_search_shortcut_imp
begin

text \<open>The end points of a path represent the path.\<close>

definition "path_rel = (\<lambda>(a, b) p. p = [a, b])"

lemma cur_red_imp_rule:
  assumes "rnb_invar C" "l \<in> K" "rnb_remaining C l \<noteq> {}" "rnb_current C l \<in> K"
      and "potential_invar \<pi>"
  shows "<nb_assn C Ci * (pot_assn \<pi> Pti * buddy_assn M Bdi)> code.cur_red_imp Pti Bdi Ci l
         <\<lambda>(k, r, f). nb_assn C Ci * (pot_assn \<pi> Pti * buddy_assn M Bdi) *
                     \<up>(h k = red \<pi> l r \<and> r = rnb_current C l \<and> f = free M r)>"
  unfolding code.cur_red_imp_def
  by (sep_auto heap: bs.nb.idx_current_rule bs.nb.current_cost_rule
               simp: assms red_def free_def)

lemma pot_shift_imp_rule:
  assumes "potential_invar \<pi>" "l \<in> K" "r1 \<in> K" "h v = a" "h d = b"
  shows "<pot_assn \<pi> Pti> code.pot_shift_imp Pti l v r1 d
         <\<lambda>_. pot_assn (pot_shift \<pi> l a r1 b) Pti>"
proof-
  have inv1: "potential_invar (potential_upd \<pi> l a)"
    by (rule potential_map.fixed_univ_map_upd_invar[OF assms(1,2)])
  have get: "<pot_assn \<pi> Pti> pot_get_imp Pti r1
             <\<lambda>x. pot_assn \<pi> Pti * \<up>(h x = potential_get \<pi> r1)>"
    by (rule pot.fixed_univ_map_lookup_rule[OF assms(1,3)])
  have upd1: "<pot_assn \<pi> Pti> pot_upd_imp Pti l v <\<lambda>_. pot_assn (potential_upd \<pi> l a) Pti>"
    using pot.fixed_univ_map_upd_rule[OF assms(1,2), of Pti v] assms(4) by simp
  have upd2: "h w = potential_get \<pi> r1 - b \<Longrightarrow>
    <pot_assn (potential_upd \<pi> l a) Pti> pot_upd_imp Pti r1 w
    <\<lambda>_. pot_assn (pot_shift \<pi> l a r1 b) Pti>" for w
    using pot.fixed_univ_map_upd_rule[OF inv1 assms(3), of Pti w] by (simp add: pot_shift_def)
  show ?thesis
    unfolding code.pot_shift_imp_def
    supply pot.fixed_univ_map_upd_rule[sep_heap_rules del]
           pot.fixed_univ_map_lookup_rule[sep_heap_rules del]
    by (sep_auto heap: get upd1 upd2 simp: assms(5))
qed

lemma chain_imp_rule:
  assumes "path_search_precond M \<pi>" "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
          "l \<in> L" "l \<notin> Vs (matching_abstract M)" "chain k M \<pi> C l = (C', M', \<pi>', res)"
  shows "<nb_assn C Ci * (pot_assn \<pi> Pti * buddy_assn M Bdi)> code.chain_imp k Ci Pti Bdi l
         <\<lambda>r. nb_assn C' Ci * (pot_assn \<pi>' Pti * buddy_assn M' Bdi) *
              \<up>(rel_option path_rel r res)>"
  using assms
proof(induction k arbitrary: M \<pi> C l C' M' \<pi>' res rule: less_induct)
  case (less k)
  note pre = less.prems(1) and l = less.prems(4,5)
  note P = path_search_precondD[OF pre]
  have lK: "l \<in> K" using l(1) G(3) by auto
  have N: "rnb_abstract C l = {r. {l, r} \<in> G}" using rnb_init(2)[OF l(1)] less.prems(3) by simp
  have fin: "finite (rnb_abstract C l)" using rnb_init(3)[OF l(1)] less.prems(3) by simp
  have sub: "rnb_abstract C l \<subseteq> K" using N G(4) by (auto intro: edges_are_Vs_2)
  obtain C1 b s where bt: "best_two (red \<pi>) (free M) l C = (C1, b, s)" by (metis prod_cases3)
  note B = best_two_props[OF less.prems(2) lK fin bt]
  have C1: "rnb_invar C1" "rnb_abstract C1 = rnb_abstract rnb_init"
    using B(1,2) less.prems(3) by simp_all
  note bo = bs.best_two_imp_rule[where cur = "code.cur_red_imp Pti Bdi"
              and Ctx = "pot_assn \<pi> Pti * buddy_assn M Bdi" and key = "red \<pi>"
              and pref = "free M" and u = l and A = K,
              OF cur_red_imp_rule[OF _ lK _ _ P(2)] less.prems(2) lK fin sub, unfolded bt]
  note ch = less.prems(6)[unfolded chain.simps[of k M \<pi> C l] bt]
  note simps = bs.best2_rel_def bs.best_rel_None bs.best_rel_Some prod.case_eq_if
  show ?case
  proof(cases b)
    case None
    have eq: "C' = C1" "M' = M" "\<pi>' = \<pi>" "res = None" using ch None by auto
    show ?thesis
      unfolding eq by (subst code.chain_imp.simps) (sep_auto heap: bo simp: None simps)
  next
    case (Some q)
    note bS = Some
    obtain u1 r1 where q: "q = (u1, r1)" by (cases q) auto
    have b1: "r1 \<in> rnb_abstract C l" "u1 = red \<pi> l r1" "\<forall>r\<in>rnb_abstract C l. u1 \<le> red \<pi> l r"
      using B(4)[OF bS[unfolded q]] by auto
    have r1G: "{l, r1} \<in> G" using b1(1) N by simp
    have r1K: "r1 \<in> K" using b1(1) sub by auto
    have u1min: "\<And>r. {l, r} \<in> G \<Longrightarrow> u1 \<le> red \<pi> l r" using b1(3) N by simp
    show ?thesis
    proof(cases s)
      case None
      note sN = None
      show ?thesis
      proof(cases "free M r1")
        case True
        have eq: "C' = C1" "M' = M" "\<pi>' = potential_upd \<pi> l u1" "res = Some [l, r1]"
          using ch True by (simp_all add: bS q sN)
        have upd: "h k1 = u1 \<Longrightarrow>
          <pot_assn \<pi> Pti> pot_upd_imp Pti l k1 <\<lambda>_. pot_assn (potential_upd \<pi> l u1) Pti>" for k1
          using pot.fixed_univ_map_upd_rule[OF P(2) lK, of Pti k1] by simp
        show ?thesis
          unfolding eq
          supply pot.fixed_univ_map_upd_rule[sep_heap_rules del]
          by (subst code.chain_imp.simps)
             (sep_auto heap: bo upd simp: bS q True sN simps path_rel_def)
      next
        case False
        have eq: "C' = C1" "M' = M" "\<pi>' = \<pi>" "res = None" using ch False by (auto simp: bS q sN)
        show ?thesis
          unfolding eq by (subst code.chain_imp.simps) (sep_auto heap: bo simp: bS q False sN simps)
      qed
    next
      case (Some q2)
      note sS = Some
      obtain u2 r2 where q2: "q2 = (u2, r2)" by (cases q2) auto
      define \<pi>2 where "\<pi>2 = pot_shift \<pi> l u2 r1 (u2 - u1)"
      have sh: "\<lbrakk>h v = u2; h d = u2 - u1\<rbrakk> \<Longrightarrow>
        <pot_assn \<pi> Pti> code.pot_shift_imp Pti l v r1 d <\<lambda>_. pot_assn \<pi>2 Pti>" for v d
        unfolding \<pi>2_def by (rule pot_shift_imp_rule[OF P(2) lK r1K])
      show ?thesis
      proof(cases "free M r1")
        case True
        have eq: "C' = C1" "M' = M" "\<pi>' = \<pi>2" "res = Some [l, r1]"
          using ch True by (simp_all add: bS q sS q2 \<pi>2_def)
        show ?thesis
          unfolding eq
          by (subst code.chain_imp.simps)
             (sep_auto heap: bo sh simp: bS q True sS q2 simps path_rel_def)
      next
        case False
        have lqe: "{buddy_get M r1, r1} \<in> matching_abstract M"
          using buddy(2)[OF P(1)] False by (simp add: free_def)
        have b2: "r2 \<in> rnb_abstract C l - {r1}" "u2 = red \<pi> l r2"
                 "\<forall>r\<in>rnb_abstract C l - {r1}. u2 \<le> red \<pi> l r"
          using B(6)[OF bS[unfolded q] sS[unfolded q2]] by auto
        have r2G: "{l, r2} \<in> G" "r2 \<noteq> r1" using b2(1) N by auto
        have u2min: "\<And>r. \<lbrakk>{l, r} \<in> G; r \<noteq> r1\<rbrakk> \<Longrightarrow> u2 \<le> red \<pi> l r" using b2(3) N by simp
        show ?thesis
        proof(cases k)
          case 0
          have eq: "C' = C1" "M' = M" "\<pi>' = \<pi>" "res = None"
            using ch False 0 by (auto simp: bS q sS q2)
          show ?thesis
            unfolding eq 0
            by (subst code.chain_imp.simps) (sep_auto heap: bo simp: bS q False sS q2 simps)
        next
          case (Suc k')
          note st = rematch_step[OF pre l r1G lqe r2G b1(2) u1min b2(2) u2min \<pi>2_def]
          have rec: "chain k' (rematch M l r1) \<pi>2 C1 (buddy_get M r1) = (C', M', \<pi>', res)"
            using ch False by (simp add: bS q sS q2 Suc \<pi>2_def)
          have IH: "<nb_assn C1 Ci * (pot_assn \<pi>2 Pti * buddy_assn (rematch M l r1) Bdi)>
                    code.chain_imp k' Ci Pti Bdi (buddy_get M r1)
                    <\<lambda>r. nb_assn C' Ci * (pot_assn \<pi>' Pti * buddy_assn M' Bdi) *
                         \<up>(rel_option path_rel r res)>"
            by (rule less.IH[OF _ st(1) C1 st(3,4) rec]) (simp add: Suc)
          have rm: "<buddy_assn M Bdi> rematch_imp Bdi l r1
                    <\<lambda>_. buddy_assn (rematch M l r1) Bdi>"
            by (rule rematch_rule[OF P(1) lqe l(2) r1G])
          have bud: "<buddy_assn M Bdi> buddy_imp Bdi r1
                     <\<lambda>x. buddy_assn M Bdi * \<up>(x = buddy_get M r1)>"
            by (rule buddy_rule[OF r1K])
          show ?thesis
            supply buddy_rule[sep_heap_rules del]
            by (subst code.chain_imp.simps)
               (sep_auto heap: bo bud sh rm IH simp: bS q False sS q2 Suc simps)
        qed
      qed
    qed
  qed
qed

text \<open>The state of the loop over the left vertices: cursors, matching and potential.\<close>

definition "sc_A Ci Pti Bdi s =
  (case s of (C, M, \<pi>) \<Rightarrow> nb_assn C Ci * (pot_assn \<pi> Pti * buddy_assn M Bdi))"

definition "sc_P s =
  (case s of (C, M, \<pi>) \<Rightarrow>
     path_search_precond M \<pi> \<and> rnb_invar C \<and> rnb_abstract C = rnb_abstract rnb_init)"

lemma sc_row_P:
  assumes "sc_P s" "l \<in> L"
  shows "sc_P (fst (sc_row s l))"
proof-
  obtain C M \<pi> where s: "s = (C, M, \<pi>)" by (metis prod_cases3)
  have I: "path_search_precond M \<pi>" "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
    using assms(1) by (simp_all add: sc_P_def s)
  show ?thesis
  proof(cases "free M l")
    case True
    have lf: "l \<notin> Vs (matching_abstract M)"
      using True buddy(1)[OF path_search_precondD(1)[OF I(1)]] by (simp add: free_def)
    obtain C1 M1 \<pi>1 r where ch: "chain cap M \<pi> C l = (C1, M1, \<pi>1, r)" by (metis prod_cases4)
    show ?thesis
      using chain_valid[OF I assms(2) lf ch] True by (simp add: sc_P_def sc_row_def s ch)
  next
    case False
    thus ?thesis using assms(1) by (simp add: sc_row_def s)
  qed
qed

lemma sc_row_imp_rule:
  assumes "sc_P s" "l \<in> L"
  shows "<sc_A Ci Pti Bdi s> code.sc_row_imp Ci Pti Bdi l
         <\<lambda>r. sc_A Ci Pti Bdi (fst (sc_row s l)) * \<up>(rel_option path_rel r (snd (sc_row s l)))>"
proof-
  obtain C M \<pi> where s: "s = (C, M, \<pi>)" by (metis prod_cases3)
  have I: "path_search_precond M \<pi>" "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
    using assms(1) by (simp_all add: sc_P_def s)
  have lK: "l \<in> K" using assms(2) G(3) by auto
  show ?thesis
  proof(cases "free M l")
    case True
    have lf: "l \<notin> Vs (matching_abstract M)"
      using True buddy(1)[OF path_search_precondD(1)[OF I(1)]] by (simp add: free_def)
    obtain C1 M1 \<pi>1 r where ch: "chain cap M \<pi> C l = (C1, M1, \<pi>1, r)" by (metis prod_cases4)
    have bud: "<buddy_assn M Bdi> buddy_imp Bdi l <\<lambda>x. buddy_assn M Bdi * \<up>(x = nil)>"
      using buddy_rule[OF lK, of M Bdi] True by (simp add: free_def)
    show ?thesis
      unfolding code.sc_row_imp_def sc_A_def s
      supply buddy_rule[sep_heap_rules del]
      by (sep_auto heap: bud chain_imp_rule[OF I assms(2) lf ch] simp: sc_row_def True ch)
  next
    case False
    have bud: "<buddy_assn M Bdi> buddy_imp Bdi l <\<lambda>x. buddy_assn M Bdi * \<up>(x \<noteq> nil)>"
      using buddy_rule[OF lK, of M Bdi] False unfolding free_def by (sep_auto simp: hoare_triple_def)
    show ?thesis
      unfolding code.sc_row_imp_def sc_A_def s
      supply buddy_rule[sep_heap_rules del]
      by (sep_auto heap: bud simp: sc_row_def False)
  qed
qed

lemma rel_option_path_rel_Some:
  "rel_option path_rel r (Some p) \<longleftrightarrow> (\<exists>a b. r = Some (a, b) \<and> p = [a, b])"
  by (cases r) (auto simp: path_rel_def)

text \<open>The loop takes the left vertices from the iterator and hands back the iterator over the
      remaining ones.\<close>

lemma sc_loop_imp_rule:
  assumes "set xs \<subseteq> L" "sc_P s"
  shows "<vset_assn left Li * left_is_it (vset_to_set left) Li xs it * sc_A Ci Pti Bdi s>
         code.sc_loop_imp Ci Pti Bdi it
         <\<lambda>(r, it'). vset_assn left Li *
                     left_is_it (vset_to_set left) Li (snd (snd (sc_loop s xs))) it' *
                     sc_A Ci Pti Bdi (fst (sc_loop s xs)) *
                     \<up>(rel_option (rel_prod (=) path_rel) r (fst (snd (sc_loop s xs))))>"
  using assms
proof(induction xs arbitrary: s it)
  case Nil
  show ?case
    by (subst code.sc_loop_imp.simps) (sep_auto heap: left.it_has_next_rule)
next
  case (Cons l xs)
  have l: "l \<in> L" and xsL: "set xs \<subseteq> L" using Cons.prems(1) by auto
  obtain s1 r1 where row: "sc_row s l = (s1, r1)" by fastforce
  have P1: "sc_P s1" using sc_row_P[OF Cons.prems(2) l] row by simp
  have rowr: "<sc_A Ci Pti Bdi s> code.sc_row_imp Ci Pti Bdi l
              <\<lambda>r. sc_A Ci Pti Bdi s1 * \<up>(rel_option path_rel r r1)>"
    using sc_row_imp_rule[OF Cons.prems(2) l] row by simp
  show ?case
  proof(cases r1)
    case None
    have lp: "sc_loop s (l # xs) = sc_loop s1 xs" by (simp add: row None)
    show ?thesis
      unfolding lp
      by (subst code.sc_loop_imp.simps)
         (sep_auto heap: left.it_has_next_rule left.it_next_rule rowr Cons.IH[OF xsL P1]
                   simp: None)
  next
    case (Some p)
    have lp: "sc_loop s (l # xs) = (s1, Some (l, p), xs)" by (simp add: row Some)
    show ?thesis
      unfolding lp
      by (subst code.sc_loop_imp.simps)
         (sep_auto heap: left.it_has_next_rule left.it_next_rule rowr
                   simp: Some rel_option_path_rel_Some path_rel_def)
  qed
qed

text \<open>The cursors may be anywhere, as long as they belong to the collection of the
      neighbourhoods. The path array keeps its length; on success, it starts with the path.\<close>

theorem shortcut_imp_rule:
  assumes "path_search_precond M \<pi>" "set xs \<subseteq> L"
      and "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
      and sc: "sc_loop (C, M, \<pi>) xs = ((C', M', \<pi>'), res, xs')"
      and len: "res \<noteq> None \<Longrightarrow> 2 \<le> length ys"
  shows "<vset_assn left Li * left_is_it (vset_to_set left) Li xs it * nb_assn C Ci *
          buddy_assn M Bdi * pot_assn \<pi> Pti * Ra \<mapsto>\<^sub>a ys>
         code.shortcut_imp Ci Pti Bdi Ra it
         <\<lambda>(b, it'). \<exists>\<^sub>Ays'. vset_assn left Li * left_is_it (vset_to_set left) Li xs' it' *
            nb_assn C' Ci * buddy_assn M' Bdi *
            pot_assn \<pi>' Pti * Ra \<mapsto>\<^sub>a ys' * \<up>(length ys' = length ys) *
            \<up>(case res of None \<Rightarrow> \<not> b | Some (l, p) \<Rightarrow> b \<and> take 2 ys' = p)>"
proof-
  have P0: "sc_P (C, M, \<pi>)" using assms(1,3,4) by (simp add: sc_P_def)
  have loop: "<vset_assn left Li * left_is_it (vset_to_set left) Li xs it *
                (nb_assn C Ci * (pot_assn \<pi> Pti * buddy_assn M Bdi))>
      code.sc_loop_imp Ci Pti Bdi it
      <\<lambda>(r, it'). vset_assn left Li * left_is_it (vset_to_set left) Li xs' it' *
                  (nb_assn C' Ci * (pot_assn \<pi>' Pti * buddy_assn M' Bdi)) *
                  \<up>(rel_option (rel_prod (=) path_rel) r res)>"
    using sc_loop_imp_rule[OF assms(2) P0, of Li it Ci Pti Bdi] by (simp add: sc sc_A_def)
  show ?thesis
  proof(cases res)
    case None
    have loopN: "<vset_assn left Li * left_is_it (vset_to_set left) Li xs it *
                  (nb_assn C Ci * (pot_assn \<pi> Pti * buddy_assn M Bdi))>
        code.sc_loop_imp Ci Pti Bdi it
        <\<lambda>x. vset_assn left Li * left_is_it (vset_to_set left) Li xs' (snd x) *
             (nb_assn C' Ci * (pot_assn \<pi>' Pti * buddy_assn M' Bdi)) * \<up>(fst x = None)>"
      using loop by (simp add: None case_prod_beta')
    show ?thesis
      unfolding code.shortcut_imp_def
      by (sep_auto heap: loopN simp: None)
  next
    case (Some a)
    then obtain l p where a: "res = Some (l, p)" by (cases a) auto
    have rs: "rel_option (rel_prod (=) path_rel) r (Some (l, p)) \<longleftrightarrow>
              (\<exists>u v. r = Some (l, u, v) \<and> p = [u, v])"
      for r by (cases r) (auto simp: path_rel_def split: prod.splits)
    have loopS: "<vset_assn left Li * left_is_it (vset_to_set left) Li xs it *
                  (nb_assn C Ci * (pot_assn \<pi> Pti * buddy_assn M Bdi))>
        code.sc_loop_imp Ci Pti Bdi it
        <\<lambda>x. vset_assn left Li * left_is_it (vset_to_set left) Li xs' (snd x) *
             (nb_assn C' Ci * (pot_assn \<pi>' Pti * buddy_assn M' Bdi)) *
             \<up>(\<exists>u v. fst x = Some (l, u, v) \<and> p = [u, v])>"
      using loop by (simp add: a rs case_prod_beta')
    have "Suc 0 < length ys" using len a by auto
    then obtain y0 y1 zs where ys: "ys = y0 # y1 # zs" by (cases ys; cases "tl ys") auto
    show ?thesis
      unfolding code.shortcut_imp_def
      by (sep_auto heap: loopS simp: a ys)
  qed
qed

end

end
