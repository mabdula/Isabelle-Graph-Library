theory Path_Search_Shortcut_Imperative
  imports
    Path_Search_Shortcut
    Neighbourhood_Best_Scan_Imperative
    Data_Structures.Fixed_Univ_Set_Iterate_Imp
    Data_Structures.Fixed_Univ_Map_Specs_Imp
begin

provenance ai


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
  by (sep_auto heap: bs.nb.idx_current_rule bs.nb.current_cost_rule simp: assms red_def free_def)

lemma pot_shift_imp_rule:
  assumes "potential_invar \<pi>" "l \<in> K" "r1 \<in> K" "h v = a" "h d = b"
  shows "<pot_assn \<pi> Pti> code.pot_shift_imp Pti l v r1 d
         <\<lambda>_. pot_assn (pot_shift \<pi> l a r1 b) Pti>"
  unfolding code.pot_shift_imp_def
  by (sep_auto simp: assms pot_shift_def potential_map.fixed_univ_map_upd_invar)

lemma chain_nb_props:
  assumes "path_search_precond M \<pi>" "rnb_abstract C = rnb_abstract rnb_init" "l \<in> L"
  shows "matching_invar M" "potential_invar \<pi>" "l \<in> K" "finite (rnb_abstract C l)"
        "rnb_abstract C l \<subseteq> K"
  using assms path_search_precondD(1,2) rnb_init(2,3) G(3,4)
  by (auto intro: edges_are_Vs_2)

lemma edge_right_K: "{l, r} \<in> G \<Longrightarrow> r \<in> K"
  using G(4)
  by (auto intro: edges_are_Vs_2)

lemma chain_rematch_props:
  assumes "path_search_precond M \<pi>" "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
          "l \<in> L" "l \<notin> Vs (matching_abstract M)" "\<not> free M r1"
          "best_two (red \<pi>) (free M) l C = (C1, Some (u1, r1), Some (u2, r2))"
  shows "path_search_precond (rematch M l r1) (pot_shift \<pi> l u2 r1 (u2 - u1))"
        "rnb_invar C1" "rnb_abstract C1 = rnb_abstract rnb_init" "buddy_get M r1 \<in> L"
        "buddy_get M r1 \<notin> Vs (matching_abstract (rematch M l r1))"
        "{buddy_get M r1, r1} \<in> matching_abstract M" "{l, r1} \<in> G" "r1 \<in> K"
  using best_two_chain_props(1,2)[OF assms(2-4,7)] best_two_chain_props(3)[OF assms(2-4,7) refl]
        best_two_chain_props(4)[OF assms(2-4,7) refl refl] chain_rematch[of M \<pi> l r1 u1 r2 u2]
        not_free_matched[of M \<pi> r1] assms(1,4-6) edge_right_K[of l r1]
  by auto

lemma chain_imp_rule:
  assumes "path_search_precond M \<pi>" "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
          "l \<in> L" "l \<notin> Vs (matching_abstract M)"
  shows "<nb_assn C Ci * (pot_assn \<pi> Pti * buddy_assn M Bdi)> code.chain_imp k Ci Pti Bdi l
         <\<lambda>r. case chain k M \<pi> C l of (C', M', \<pi>', res) \<Rightarrow>
                nb_assn C' Ci * (pot_assn \<pi>' Pti * buddy_assn M' Bdi) * \<up>(rel_option path_rel r res)>"
  using assms
proof(induction k arbitrary: M \<pi> C l rule: less_induct)
  case (less k)
  note N = chain_nb_props[OF less.prems(1,3,4)]
  obtain C1 b s where "best_two (red \<pi>) (free M) l C = (C1, b, s)"
    by (cases "best_two (red \<pi>) (free M) l C") auto
  note bt = this
  note B = best_two_chain_props[OF less.prems(2-4) bt]
  note bo = bs.best_two_imp_rule[where cur = "code.cur_red_imp Pti Bdi"
              and Ctx = "pot_assn \<pi> Pti * buddy_assn M Bdi" and key = "red \<pi>"
              and pref = "free M" and u = l and A = K,
              OF cur_red_imp_rule[OF _ N(3) _ _ N(2)] less.prems(2) N(3-5), unfolded bt]
  note simps = bs.best2_rel_def bs.best_rel_None bs.best_rel_Some prod.case_eq_if
               chain.simps[of k M \<pi> C l] bt
  show ?case
  proof(cases b)
    case None
    show ?thesis
      by (subst code.chain_imp.simps) (sep_auto heap: bo simp: None simps)
  next
    case (Some q)
    show ?thesis
    proof(cases q)
      case (Pair u1 r1)
      show ?thesis
      proof(cases s)
        case None
        show ?thesis
        proof(cases "free M r1")
          case True
          show ?thesis
            by (subst code.chain_imp.simps)
               (sep_auto heap: bo simp: Some Pair None True simps path_rel_def N(2,3))
        next
          case False
          show ?thesis
            by (subst code.chain_imp.simps) (sep_auto heap: bo simp: Some Pair None False simps)
        qed
      next
        case (Some q2)
        show ?thesis
        proof(cases q2)
          case (Pair u2 r2)
          show ?thesis
          proof(cases "free M r1")
            case True
            show ?thesis
              using B(3)[of u1 r1]
              by (subst code.chain_imp.simps)
                 (sep_auto heap: bo pot_shift_imp_rule[OF N(2,3), where a = u2 and b = "u2 - u1"]
                           simp: \<open>b = Some q\<close> \<open>q = (u1, r1)\<close> Some Pair True simps path_rel_def
                                 edge_right_K)
          next
            case False
            show ?thesis
            proof(cases k)
              case 0
              show ?thesis
                by (subst code.chain_imp.simps)
                   (sep_auto heap: bo simp: \<open>b = Some q\<close> \<open>q = (u1, r1)\<close> Some Pair False 0 simps[unfolded 0])
            next
              case (Suc k')
              note R = chain_rematch_props[OF less.prems False
                                           bt[unfolded \<open>b = Some q\<close> \<open>q = (u1, r1)\<close> Some Pair]]
              show ?thesis
                by (subst code.chain_imp.simps)
                   (sep_auto heap: bo pot_shift_imp_rule[OF N(2,3) R(8), where a = u2 and b = "u2 - u1"]
                                   rematch_rule[OF N(1) R(6) less.prems(5) R(7)] less.IH[OF _ R(1-5)]
                             simp: \<open>b = Some q\<close> \<open>q = (u1, r1)\<close> Some Pair False Suc
                                   simps[unfolded Suc] R(8))
            qed
          qed
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

lemma left_K: "l \<in> L \<Longrightarrow> l \<in> K"
  using G(3)
  by blast

lemma sc_P_props:
  assumes "sc_P (C, M, \<pi>)"
  shows "path_search_precond M \<pi>" "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
  using assms
  by (simp_all add: sc_P_def)

lemma sc_row_P:
  assumes "sc_P s" "l \<in> L"
  shows "sc_P (fst (sc_row s l))"
  using assms chain_valid[of "fst (snd s)" "snd (snd s)" "fst s" l cap]
        free_unmatched[of "fst (snd s)" "snd (snd s)" l]
  by (cases "chain cap (fst (snd s)) (snd (snd s)) (fst s) l")
     (auto simp: sc_P_def sc_row_def split: prod.splits)

lemma sc_row_imp_rule:
  assumes "sc_P s" "l \<in> L"
  shows "<sc_A Ci Pti Bdi s> code.sc_row_imp Ci Pti Bdi l
         <\<lambda>r. sc_A Ci Pti Bdi (fst (sc_row s l)) * \<up>(rel_option path_rel r (snd (sc_row s l)))>"
proof(cases s rule: prod_cases3)
  case (fields C M \<pi>)
  note I = sc_P_props[OF assms(1)[unfolded fields]]
  show ?thesis
  proof(cases "free M l")
    case True
    show ?thesis
      unfolding code.sc_row_imp_def sc_A_def fields
      by (sep_auto heap: chain_imp_rule[OF I assms(2) free_unmatched[OF I(1) True]]
                   simp: sc_row_def True True[unfolded free_def] assms(2) left_K prod.case_eq_if)
  next
    case False
    show ?thesis
      unfolding code.sc_row_imp_def sc_A_def fields
      by (sep_auto simp: sc_row_def False False[unfolded free_def] eq_commute[of nil] assms(2) left_K)
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
  have "l \<in> L" "set xs \<subseteq> L"
    using Cons.prems(1)
    by simp_all
  note row = sc_row_imp_rule[OF Cons.prems(2) this(1)]
   and IH = Cons.IH[OF this(2) sc_row_P[OF Cons.prems(2) this(1)]]
  show ?case
  proof(cases "snd (sc_row s l)")
    case None
    show ?thesis
      by (subst code.sc_loop_imp.simps)
         (sep_auto heap: left.it_has_next_rule left.it_next_rule row IH simp: None prod.case_eq_if)
  next
    case (Some p)
    show ?thesis
      by (subst code.sc_loop_imp.simps)
         (sep_auto heap: left.it_has_next_rule left.it_next_rule row
                   simp: Some prod.case_eq_if rel_option_path_rel_Some path_rel_def)
  qed
qed

lemma rel_option_path_rel_pair_Some:
  "rel_option (rel_prod (=) path_rel) r (Some (l, p)) \<longleftrightarrow> (\<exists>u v. r = Some (l, u, v) \<and> p = [u, v])"
  by (cases r) (auto simp: path_rel_def)

text \<open>The cursors may be anywhere, as long as they belong to the collection of the
      neighbourhoods. The path array keeps its length; on success, it starts with the path.\<close>

lemma shortcut_imp_rule:
  assumes "path_search_precond M \<pi>" "set xs \<subseteq> L"
      and "rnb_invar C" "rnb_abstract C = rnb_abstract rnb_init"
      and "sc_loop (C, M, \<pi>) xs = ((C', M', \<pi>'), res, xs')"
      and "res \<noteq> None \<Longrightarrow> 2 \<le> length ys"
  shows "<vset_assn left Li * left_is_it (vset_to_set left) Li xs it * nb_assn C Ci *
          buddy_assn M Bdi * pot_assn \<pi> Pti * Ra \<mapsto>\<^sub>a ys>
         code.shortcut_imp Ci Pti Bdi Ra it
         <\<lambda>(b, it'). \<exists>\<^sub>Ays'. vset_assn left Li * left_is_it (vset_to_set left) Li xs' it' *
            nb_assn C' Ci * buddy_assn M' Bdi *
            pot_assn \<pi>' Pti * Ra \<mapsto>\<^sub>a ys' * \<up>(length ys' = length ys) *
            \<up>(case res of None \<Rightarrow> \<not> b | Some (l, p) \<Rightarrow> b \<and> take 2 ys' = p)>"
proof-
  have "sc_P (C, M, \<pi>)"
    using assms(1,3,4)
    by (simp add: sc_P_def)
  note loop = sc_loop_imp_rule[OF assms(2) this, of Li it Ci Pti Bdi, unfolded assms(5) sc_A_def, simplified]
  show ?thesis
  proof(cases res)
    case None
    show ?thesis
      unfolding code.shortcut_imp_def
      by (sep_auto heap: loop simp: None)
  next
    case (Some a)
    then obtain l p where "res = Some (l, p)"
      by (cases a) auto
    thus ?thesis
      using assms(6)
      unfolding code.shortcut_imp_def
      by (cases ys rule: remdups_adj.cases)
         (sep_auto heap: loop simp: rel_option_path_rel_pair_Some)+
  qed
qed

end

end
