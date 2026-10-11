theory Hungarian_Method_Top_Loop_Imperative
  imports
    Hungarian_Method.Hungarian_Method_Top_Loop
    Hungarian_Method.Path_Search_Result
    Separation_Logic_Imperative_HOL_Partial.Sep_Main
begin

section \<open>Imperative Refinement of the Top Loop\<close>

text \<open>The top loop of the Hungarian method, @{locale hungarian_loop}, is parametric in the path
      search, the augmentation, the matching and the potential. Its imperative counterpart is
      parametric in exactly their imperative counterparts: an imperative path search and an
      imperative augmentation, specified by Hoare triples relative to the functional
      @{term path_search} and @{term augment}, and representation assertions for the matching and
      the potential. The data structures of the path search, including its context, are opaque
      here (@{term scratch_assn}); the path is exchanged through an array @{term Ra}, which
      belongs to the caller. The top loop does not allocate.\<close>

locale hungarian_top_loop_imp_code =
  fixes path_search_imp ::
          "'si \<Rightarrow> 'mi \<Rightarrow> 'pi \<Rightarrow> 'v::heap array \<Rightarrow> (imp_search_result \<times> 'mi \<times> 'pi \<times> 'si) Heap"
    and augment_imp :: "'mi \<Rightarrow> 'v array \<Rightarrow> nat \<Rightarrow> 'mi Heap"
begin

partial_function (heap) main_loop_imp ::
  "'si \<Rightarrow> 'mi \<Rightarrow> 'pi \<Rightarrow> 'v array \<Rightarrow> (result \<times> 'mi \<times> 'pi \<times> 'si) Heap" where
  "main_loop_imp Si Mi Pti Ra = do {
     (res, Mi', Pti', Si') \<leftarrow> path_search_imp Si Mi Pti Ra;
     (case res of
        Imp_Unbounded \<Rightarrow> return (result.failure, Mi', Pti', Si')
      | Imp_Matched \<Rightarrow> return (result.success, Mi', Pti', Si')
      | Imp_Path k \<Rightarrow> do { Mi'' \<leftarrow> augment_imp Mi' Ra k;
                          main_loop_imp Si' Mi'' Pti' Ra }) }"

definition "hungarian_imp cL cR Si Mi Pti Ra =
  (if cL \<noteq> cR then return (result.failure, Mi, Pti, Si) else main_loop_imp Si Mi Pti Ra)"

end

locale hungarian_top_loop_imp =
  hungarian_loop where path_search = path_search and augment = augment and ctx_invar = ctx_invar +
  hungarian_top_loop_imp_code path_search_imp augment_imp
    for path_search :: "'ctx \<Rightarrow> 'matching \<Rightarrow> 'potential \<Rightarrow>
                        ('v::heap) path_search_result \<times> 'matching \<times> 'potential \<times> 'ctx"
    and ctx_invar :: "'ctx \<Rightarrow> bool"
    and augment :: "'matching \<Rightarrow> 'v list \<Rightarrow> 'matching"
    and path_search_imp ::
          "'si \<Rightarrow> 'mi \<Rightarrow> 'pi \<Rightarrow> 'v array \<Rightarrow> (imp_search_result \<times> 'mi \<times> 'pi \<times> 'si) Heap"
    and augment_imp :: "'mi \<Rightarrow> 'v array \<Rightarrow> nat \<Rightarrow> 'mi Heap" +
  fixes scratch_assn :: "'ctx \<Rightarrow> 'si \<Rightarrow> assn"
    and matching_assn :: "'matching \<Rightarrow> 'mi \<Rightarrow> assn"
    and pot_assn :: "'potential \<Rightarrow> 'pi \<Rightarrow> assn"
    and len_bound :: nat
  assumes path_search_rule:
    "\<lbrakk>path_search_precond M \<pi>; ctx_invar c; path_search c M \<pi> = (r, M', \<pi>', c');
      len_bound \<le> length xs\<rbrakk> \<Longrightarrow>
     <scratch_assn c Si * matching_assn M Mi * pot_assn \<pi> Pti * Ra \<mapsto>\<^sub>a xs>
     path_search_imp Si Mi Pti Ra
     <\<lambda>(res, Mi', Pti', Si'). \<exists>\<^sub>Axs'. scratch_assn c' Si' * matching_assn M' Mi' *
        pot_assn \<pi>' Pti' * Ra \<mapsto>\<^sub>a xs' * \<up>(length xs' = length xs) *
        \<up>(imp_result_rel xs' res r)>"
    and augment_rule:
    "\<lbrakk>matching_invar M; graph_augmenting_path G (matching_abstract M) p;
      k \<le> length xs; take k xs = p\<rbrakk> \<Longrightarrow>
     <matching_assn M Mi * Ra \<mapsto>\<^sub>a xs> augment_imp Mi Ra k
     <\<lambda>Mi'. matching_assn (augment M p) Mi' * Ra \<mapsto>\<^sub>a xs>"
begin


definition "loop_post state r Mi' Pti' Si' =
  scratch_assn (search_ctx (hungarian_loop state)) Si' *
  matching_assn (buddies (hungarian_loop state)) Mi' *
  pot_assn (potential (hungarian_loop state)) Pti' *
  \<up>(r = result (hungarian_loop state))"

lemma main_loop_imp_rule:
  assumes "state_invar state" "len_bound \<le> length xs"
  shows "<scratch_assn (search_ctx state) Si * matching_assn (buddies state) Mi *
          pot_assn (potential state) Pti * Ra \<mapsto>\<^sub>a xs>
         main_loop_imp Si Mi Pti Ra
         <\<lambda>(r, Mi', Pti', Si'). \<exists>\<^sub>Axs'. Ra \<mapsto>\<^sub>a xs' * \<up>(length xs' = length xs) *
             loop_post state r Mi' Pti' Si'>"
proof-
  have "state_invar state \<longrightarrow> (\<forall>Si Mi Pti xs. len_bound \<le> length xs \<longrightarrow>
         <scratch_assn (search_ctx state) Si * matching_assn (buddies state) Mi *
          pot_assn (potential state) Pti * Ra \<mapsto>\<^sub>a xs>
         main_loop_imp Si Mi Pti Ra
         <\<lambda>(r, Mi', Pti', Si'). \<exists>\<^sub>Axs'. Ra \<mapsto>\<^sub>a xs' * \<up>(length xs' = length xs) *
             loop_post state r Mi' Pti' Si'>)"
  proof(induction rule: hungarian_loop_induct[OF hungarian_loop_termination[OF assms(1)]])
    case (1 state)
    show ?case
    proof(intro impI allI)
      fix Si Mi Pti and xs :: "'v list"
      assume inv: "state_invar state" and len: "len_bound \<le> length xs"
      obtain r M' \<pi>' c' where so: "search_of state = (r, M', \<pi>', c')"
        by (cases "search_of state") auto
      note ps = path_search_rule[OF state_invarD(1)[OF inv] state_invarD(2)[OF inv]
                                    so[unfolded search_of_def] len]
      note gs = search_of_props[OF inv so]
      show "<scratch_assn (search_ctx state) Si * matching_assn (buddies state) Mi *
             pot_assn (potential state) Pti * Ra \<mapsto>\<^sub>a xs>
            main_loop_imp Si Mi Pti Ra
            <\<lambda>(r, Mi', Pti', Si'). \<exists>\<^sub>Axs'. Ra \<mapsto>\<^sub>a xs' * \<up>(length xs' = length xs) *
               loop_post state r Mi' Pti' Si'>"
      proof(cases r)
        case Dual_Unbounded
        have hl: "hungarian_loop state =
                  state\<lparr>buddies := M', potential := \<pi>', search_ctx := c', result := result.failure\<rparr>"
          by (simp add: hungarian_loop_simps(1) hungarian_loop_fail_cond_def
                        hungarian_loop_fail_def so Dual_Unbounded)
        show ?thesis
          apply(subst main_loop_imp.simps)
          apply(sep_auto heap: ps simp: Dual_Unbounded)
          by (sep_auto simp: loop_post_def hl)
      next
        case Lefts_Matched
        have hl: "hungarian_loop state =
                  state\<lparr>buddies := M', potential := \<pi>', search_ctx := c', result := result.success\<rparr>"
          by (simp add: hungarian_loop_simps(2) hungarian_loop_succ_cond_def
                        hungarian_loop_succ_def so Lefts_Matched)
        show ?thesis
          apply(subst main_loop_imp.simps)
          apply(sep_auto heap: ps simp: Lefts_Matched)
          by (sep_auto simp: loop_post_def hl)
      next
        case (Next_Iteration p)
        have cc: "hungarian_loop_cont_cond state"
          by (simp add: hungarian_loop_cont_cond_def so Next_Iteration)
        have pre': "path_search_precond M' \<pi>'" using good_searchD(1)[OF gs(1)] .
        have aug: "graph_augmenting_path G (matching_abstract M') p"
          using good_search_resultD(5)[OF good_searchD(5)[OF gs(1) Next_Iteration]] .
        have upd: "hungarian_loop_upd state =
                   state\<lparr>buddies := augment M' p, potential := \<pi>', search_ctx := c'\<rparr>"
          by (simp add: hungarian_loop_upd_def so Next_Iteration)
        have lp: "loop_post state = loop_post (hungarian_loop_upd state)"
          by (intro ext) (simp add: loop_post_def hungarian_loop_simps(3)[OF cc 1(1)])
        have inv': "state_invar (hungarian_loop_upd state)"
          using state_invar_pres_one_step[OF cc inv] .
        note IH = 1(2)[OF cc, rule_format, OF inv', unfolded upd, simplified]
        note lp' = lp[unfolded upd]
        note au = augment_rule[OF path_search_precondD(1)[OF pre'] aug]
        show ?thesis
          apply(subst main_loop_imp.simps)
          apply(sep_auto heap: ps simp: Next_Iteration)
          apply(sep_auto heap: au)
          by (sep_auto heap: IH simp: lp' len split: prod.splits)
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

text \<open>The imperative Hungarian method returns the same result as the functional one,
      @{term hungarian}, for which @{thm hungarian_correctness} holds.\<close>

theorem hungarian_imp_rule:
  assumes "len_bound \<le> length xs"
  shows "<scratch_assn init_ctx Si * matching_assn empty_matching Mi *
          pot_assn init_potential Pti * Ra \<mapsto>\<^sub>a xs>
         hungarian_imp card_L card_R Si Mi Pti Ra
         <\<lambda>(r, Mi', Pti', Si'). \<exists>\<^sub>Axs' M \<pi> c. scratch_assn c Si' * Ra \<mapsto>\<^sub>a xs' *
             matching_assn M Mi' * pot_assn \<pi> Pti' * \<up>(length xs' = length xs) *
             \<up>((r = result.success \<and> hungarian = Some M) \<or> (r = result.failure \<and> hungarian = None))>"
proof(cases "card_L = card_R")
  case False
  thus ?thesis by (sep_auto simp: hungarian_imp_def hungarian_def)
next
  case True
  define fs where "fs = hungarian_loop initial_state"
  have res: "result fs \<noteq> notyetterm"
    using loop_on_initial_state_result(2) by (simp add: fs_def)
  have hung: "hungarian = (case result fs of result.failure \<Rightarrow> None
                           | result.success \<Rightarrow> Some (buddies fs))"
    by (simp add: hungarian_loop_spec.hungarian_def True initial_state_loops_same fs_def Let_def
                  split: result.splits)
  have fin: "(result fs = result.success \<and> hungarian = Some (buddies fs)) \<or>
             (result fs = result.failure \<and> hungarian = None)"
    using res by (cases "result fs") (simp_all add: hung)
  have bi: "buddies initial_state = empty_matching" "potential initial_state = init_potential"
           "search_ctx initial_state = init_ctx"
    by (simp_all add: initial_state_def)
  note ml = main_loop_imp_rule[OF initial_state_invar assms, of Si Mi Pti Ra,
                               unfolded loop_post_def, folded fs_def, unfolded bi]
  show ?thesis
    apply(simp add: hungarian_imp_def True)
    apply(rule ht_cons_post[OF ml])
    apply(clarsimp split: prod.splits)
    apply(rule ent_ex_preI)
    apply(rule ent_ex_postI, rule ent_ex_postI[where x = "buddies fs"],
          rule ent_ex_postI[where x = "potential fs"], rule ent_ex_postI[where x = "search_ctx fs"])
    using fin[unfolded True] by sep_auto
qed

end

end
