theory Disjoint_Paths_Search_Imperative
  imports Hopcroft_Karp.Disjoint_Paths_Search Data_Structures.Bounded_Stack_Specs_Imp
begin

provenance ai


section \<open>Imperative Refinement of the Disjoint-Paths Search\<close>

text \<open>The imperative program mirrors @{const Disjoint_Paths_Search.Disjoint_Paths_Search_impl}.
      The roots are kept in an imperative bounded stack (@{locale bounded_stack_imp}) whose top is
      the next root, and the found paths in an abstract imperative store. The search step and the
      commitment of a found path are parameters; their Hoare triples, stated against the functional
      operations, are the assumptions of the refinement locale. The search step does not return the
      path it found: it keeps it in its own resources, described by @{text "step_assn (Some p)"},
      and the commitment moves it into the store of paths and extends the avoided set by the
      vertices it blocks. The resources of the search step (e.g.\ the graph and auxiliary arrays)
      are described by @{text "step_assn None"} when no path is pending.\<close>

record ('irs, 'imp_av, 'imp_ex, 'ips) Disjoint_Paths_Search_state_imp =
  i_roots :: 'irs
  i_avoided :: 'imp_av
  i_explored :: 'imp_ex
  i_paths :: 'ips

locale Disjoint_Paths_Search_Imperative_spec =
  fixes search_step_imp :: "'imp_av \<Rightarrow> 'v::heap \<Rightarrow> 'imp_ex \<Rightarrow> (bool \<times> 'imp_ex) Heap"
    and commit_path_imp :: "'imp_av \<Rightarrow> 'ips \<Rightarrow> ('imp_av \<times> 'ips) Heap"
    and stack_is_empty_imp :: "'irs \<Rightarrow> bool Heap"
    and stack_top_imp :: "'irs \<Rightarrow> 'v Heap"
    and stack_pop_imp :: "'irs \<Rightarrow> unit Heap"
begin

partial_function \<^marker>\<open>provenance ai_human\<close> (heap) Disjoint_Paths_Search_imp ::
  "('irs, 'imp_av, 'imp_ex, 'ips) Disjoint_Paths_Search_state_imp \<Rightarrow>
   ('irs, 'imp_av, 'imp_ex, 'ips) Disjoint_Paths_Search_state_imp Heap"
  where
  "Disjoint_Paths_Search_imp s =
     do { e \<leftarrow> stack_is_empty_imp (i_roots s);
          if e then return s
          else do { r \<leftarrow> stack_top_imp (i_roots s);
                    stack_pop_imp (i_roots s);
                    (found, Ei') \<leftarrow> search_step_imp (i_avoided s) r (i_explored s);
                    if found
                    then do { (Ai', Psi') \<leftarrow> commit_path_imp (i_avoided s) (i_paths s);
                              Disjoint_Paths_Search_imp
                                (s\<lparr>i_avoided := Ai', i_explored := Ei', i_paths := Psi'\<rparr>) }
                    else Disjoint_Paths_Search_imp (s\<lparr>i_explored := Ei'\<rparr>) } }"

definition "initial_state_imp Ri Ai Ei Psi =
  \<lparr>i_roots = Ri, i_avoided = Ai, i_explored = Ei, i_paths = Psi\<rparr>"

definition "Disjoint_Paths_Search_run_imp Ri Ai Ei Psi =
  Disjoint_Paths_Search_imp (initial_state_imp Ri Ai Ei Psi)"

end

locale Disjoint_Paths_Search_Imperative =
  Disjoint_Paths_Search_thms where lookup = lookup +
  Disjoint_Paths_Search_Imperative_spec where search_step_imp = search_step_imp
    and commit_path_imp = commit_path_imp +
  rts: bounded_stack_imp where stack_abstract = stack_abstract
  for lookup :: "'adjmap \<Rightarrow> 'v::heap \<Rightarrow> 'vset option"
  and search_step_imp :: "'imp_av \<Rightarrow> 'v \<Rightarrow> 'imp_ex \<Rightarrow> (bool \<times> 'imp_ex) Heap"
  and commit_path_imp :: "'imp_av \<Rightarrow> 'ips \<Rightarrow> ('imp_av \<times> 'ips) Heap"
  and stack_abstract :: "'rs \<Rightarrow> 'v list" +
  fixes step_assn :: "'v list option \<Rightarrow> assn"
    and avoided_assn :: "'vset \<Rightarrow> 'imp_av \<Rightarrow> assn"
    and explored_assn :: "'vset \<Rightarrow> 'imp_ex \<Rightarrow> assn"
    and paths_assn :: "'v list list \<Rightarrow> 'ips \<Rightarrow> assn"
  assumes search_step_imp_rule:
      "\<And>A Ai r V Vi. \<lbrakk>vset_inv A; vset_inv V; t_set A \<subseteq> dVs (Graph.digraph_abs G);
          t_set V \<subseteq> dVs (Graph.digraph_abs G); r \<in> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow>
       <step_assn None * avoided_assn A Ai * explored_assn V Vi>
         search_step_imp Ai r Vi
       <\<lambda>(found, Vi'). step_assn (fst (search_step A r V)) * avoided_assn A Ai *
                       explored_assn (snd (search_step A r V)) Vi' *
                       \<up>(found \<longleftrightarrow> fst (search_step A r V) \<noteq> None)>"
    and commit_path_imp_rule:
      "\<And>A Ai p ps Psi. \<lbrakk>vset_inv A; t_set A \<subseteq> dVs (Graph.digraph_abs G)\<rbrakk> \<Longrightarrow>
       <step_assn (Some p) * avoided_assn A Ai * paths_assn ps Psi>
         commit_path_imp Ai Psi
       <\<lambda>(Ai', Psi'). step_assn None * avoided_assn (union A (blocked p)) Ai' * paths_assn (p # ps) Psi'>"
begin

subsection \<open>The roots\<close>

definition "roots_assn xs Ri = (\<exists>\<^sub>A R. stack_assn R Ri * \<up>(stack_invar R \<and> stack_abstract R = xs))"

lemma \<^marker>\<open>provenance ai_human\<close> roots_is_empty_rule:
  "<roots_assn xs Ri> stack_is_empty_imp Ri <\<lambda>r. roots_assn xs Ri * \<up>(r \<longleftrightarrow> xs = [])>"
  unfolding roots_assn_def
  by (sep_auto heap: rts.stack_is_empty_rule simp: rts.stack_is_empty)

lemma \<^marker>\<open>provenance ai_human\<close> roots_top_rule:
  "xs \<noteq> [] \<Longrightarrow> <roots_assn xs Ri> stack_top_imp Ri <\<lambda>r. roots_assn xs Ri * \<up>(r = hd xs)>"
  unfolding roots_assn_def
  by (sep_auto heap: rts.stack_top_rule simp: rts.stack_top)

lemma \<^marker>\<open>provenance ai_human\<close> roots_pop_rule:
  "xs \<noteq> [] \<Longrightarrow> <roots_assn xs Ri> stack_pop_imp Ri <\<lambda>_. roots_assn (tl xs) Ri>"
  unfolding roots_assn_def
  by (sep_auto heap: rts.stack_pop_rule simp: rts.stack_pop)

subsection \<open>The loop\<close>

definition "state_assn s si =
  roots_assn (roots s) (i_roots si) * avoided_assn (avoided s) (i_avoided si) *
  explored_assn (explored s) (i_explored si) * paths_assn (paths s) (i_paths si) *
  \<up>(invar_1 s \<and> invar_within_graph s)"

lemma \<^marker>\<open>provenance ai_human\<close> Disjoint_Paths_Search_imp_refine:
  "<step_assn None * state_assn s si> Disjoint_Paths_Search_imp si
   <\<lambda>si'. step_assn None * state_assn (Disjoint_Paths_Search_impl s) si'>"
proof(induction arbitrary: s si rule: Disjoint_Paths_Search_imp.fixp_induct)
  case 1
  then show ?case
    by auto
next
  case 2
  then show ?case
    by simp
next
  case (3 f s si)
  show ?case
    unfolding state_assn_def[of s si] mult.assoc[symmetric]
  proof(rule ht_extract_pre_pure(1), goal_cases)
    case 1
    hence I1: "invar_1 s" and I2: "invar_within_graph s"
      by simp_all
    show ?case
    proof(cases "roots s")
      case Nil
      thus ?thesis
        using I1 I2
        by (sep_auto heap: roots_is_empty_rule
                     simp: Disjoint_Paths_Search_impl.simps[of s] state_assn_def)
    next
      case (Cons r rs)
      have hd: "hd (roots s) = r" and ne: "roots s \<noteq> []" and tl: "tl (roots s) = rs"
        using Cons by simp_all
      obtain res V' where step: "search_step (avoided s) r (explored s) = (res, V')"
        by (cases "search_step (avoided s) r (explored s)") auto
      have pre: "vset_inv (avoided s)" "vset_inv (explored s)"
                "t_set (avoided s) \<subseteq> dVs (Graph.digraph_abs G)"
                "t_set (explored s) \<subseteq> dVs (Graph.digraph_abs G)" "r \<in> dVs (Graph.digraph_abs G)"
        using I1 I2 Cons by (auto simp: invar_1_def invar_within_graph_def)
      have SS: "<step_assn None * avoided_assn (avoided s) (i_avoided si) *
                 explored_assn (explored s) (i_explored si)>
                  search_step_imp (i_avoided si) r (i_explored si)
                <\<lambda>(found, Vi'). step_assn res * avoided_assn (avoided s) (i_avoided si) *
                                explored_assn V' Vi' * \<up>(found \<longleftrightarrow> res \<noteq> None)>"
        using search_step_imp_rule[OF pre, of "i_avoided si" "i_explored si"] step by simp
      show ?thesis
      proof(cases res)
        case None
        define s' where "s' = s\<lparr>roots := rs, explored := V'\<rparr>"
        have upd: "Disjoint_Paths_Search_upd2 s = s'"
          by (simp add: Disjoint_Paths_Search_upd2_def s'_def Cons step)
        have call: "Disjoint_Paths_Search_call_2_conds s"
          using Cons step None by (auto intro: Disjoint_Paths_Search_call_2_condsI)
        have I': "invar_1 s'" "invar_within_graph s'"
          using invar_1_holds_upd2[OF call I2 I1] invar_within_graph_holds_upd2[OF call I1 I2]
          by (simp_all add: upd)
        have F: "Disjoint_Paths_Search_impl s = Disjoint_Paths_Search_impl s'"
          by (subst Disjoint_Paths_Search_impl.simps) (simp add: Cons step None s'_def)
        have IH: "<step_assn None * roots_assn (tl (roots s)) (i_roots si) *
                   avoided_assn (avoided s) (i_avoided si) * explored_assn V' Ei' *
                   paths_assn (paths s) (i_paths si)>
                    f (si\<lparr>i_explored := Ei'\<rparr>)
                  <\<lambda>si'. step_assn None * state_assn (Disjoint_Paths_Search_impl s) si'>" for Ei'
          using 3[of s' "si\<lparr>i_explored := Ei'\<rparr>"] I' tl
          unfolding F by (simp add: state_assn_def s'_def mult.assoc)
        show ?thesis
          using hd ne None
          by (sep_auto heap: roots_is_empty_rule roots_top_rule roots_pop_rule SS IH)
      next
        case (Some p)
        define s' where
          "s' = s\<lparr>roots := rs, avoided := union (avoided s) (blocked p), explored := V',
                   paths := p # paths s\<rparr>"
        have upd: "Disjoint_Paths_Search_upd1 s = s'"
          by (simp add: Disjoint_Paths_Search_upd1_def s'_def Cons step Some)
        have call: "Disjoint_Paths_Search_call_1_conds s"
          using Cons step Some by (auto intro: Disjoint_Paths_Search_call_1_condsI)
        have I': "invar_1 s'" "invar_within_graph s'"
          using invar_1_holds_upd1[OF call I2 I1] invar_within_graph_holds_upd1[OF call I1 I2]
          by (simp_all add: upd)
        have F: "Disjoint_Paths_Search_impl s = Disjoint_Paths_Search_impl s'"
          by (subst Disjoint_Paths_Search_impl.simps) (simp add: Cons step Some s'_def)
        note CP = commit_path_imp_rule[OF pre(1,3), where Ai = "i_avoided si" and p = p and ps = "paths s"
                                                and Psi = "i_paths si"]
        have IH: "<step_assn None * roots_assn (tl (roots s)) (i_roots si) *
                   avoided_assn (union (avoided s) (blocked p)) Ai' * explored_assn V' Ei' *
                   paths_assn (p # paths s) Psi'>
                    f (si\<lparr>i_avoided := Ai', i_explored := Ei', i_paths := Psi'\<rparr>)
                  <\<lambda>si'. step_assn None * state_assn (Disjoint_Paths_Search_impl s) si'>"
          for Ai' Ei' Psi'
          using 3[of s' "si\<lparr>i_avoided := Ai', i_explored := Ei', i_paths := Psi'\<rparr>"] I' tl
          unfolding F by (simp add: state_assn_def s'_def mult.assoc)
        show ?thesis
          using hd ne Some
          by (sep_auto heap: roots_is_empty_rule roots_top_rule roots_pop_rule SS CP IH)
      qed
    qed
  qed
qed

subsection \<open>Correctness\<close>

theorem \<^marker>\<open>provenance ai_human\<close> Disjoint_Paths_Search_run_imp_rule:
  "<step_assn None * roots_assn initial_roots Ri * avoided_assn vset_empty Ai *
    explored_assn vset_empty Ei * paths_assn [] Psi>
     Disjoint_Paths_Search_run_imp Ri Ai Ei Psi
   <\<lambda>si. step_assn None * state_assn Disjoint_Paths_Search_run_impl si>"
proof-
  have "state_assn initial_state (initial_state_imp Ri Ai Ei Psi) =
        roots_assn initial_roots Ri * avoided_assn vset_empty Ai * explored_assn vset_empty Ei *
        paths_assn [] Psi"
    using initial_state_props(1,2)
    by (simp add: state_assn_def initial_state_def initial_state_imp_def)
  thus ?thesis
    using Disjoint_Paths_Search_imp_refine[of initial_state "initial_state_imp Ri Ai Ei Psi"]
    by (simp add: Disjoint_Paths_Search_run_imp_def Disjoint_Paths_Search_run_impl_def mult.assoc)
qed

text \<open>The paths found by the imperative search are those of the functional one, and hence satisfy
      @{thm [source] Disjoint_Paths_Search_correct_1}, @{thm [source] Disjoint_Paths_Search_correct_2}
      and @{thm [source] Disjoint_Paths_Search_correct_3}. All roots have been consumed.\<close>

theorem \<^marker>\<open>provenance ai_human\<close> Disjoint_Paths_Search_run_imp_correct:
  "<step_assn None * roots_assn initial_roots Ri * avoided_assn vset_empty Ai *
    explored_assn vset_empty Ei * paths_assn [] Psi>
     Disjoint_Paths_Search_run_imp Ri Ai Ei Psi
   <\<lambda>si. \<exists>\<^sub>A ps A E. step_assn None * roots_assn [] (i_roots si) * avoided_assn A (i_avoided si) *
         explored_assn E (i_explored si) * paths_assn ps (i_paths si) *
         \<up>(ps = paths Disjoint_Paths_Search_run_impl \<and>
           (\<forall>p \<in> set ps.
              Vwalk.vwalk (Graph.digraph_abs G) (rev p) \<and> p \<noteq> [] \<and> distinct p \<and> target (hd p) \<and>
              last p \<in> set initial_roots) \<and>
           sorted_wrt (\<lambda>q p. set q \<inter> t_set (blocked p) = {}) ps \<and>
           (\<forall>r q z. r \<in> set initial_roots \<longrightarrow> Vwalk.vwalk_bet (Graph.digraph_abs G) r q z \<longrightarrow>
                    target z \<longrightarrow> ps \<noteq> []))>"
proof-
  have eq: "Disjoint_Paths_Search_run_impl = Disjoint_Paths_Search initial_state"
    by (simp add: Disjoint_Paths_Search_run_impl_def Disjoint_Paths_Search_impl_to_Disjoint_Paths_Search)
  have "roots (Disjoint_Paths_Search initial_state) = []"
    using ret1_holds[OF initial_state_props(8)]
    by (auto elim: call_cond_elims)
  thus ?thesis
    using Disjoint_Paths_Search_correct_1 Disjoint_Paths_Search_correct_2
          Disjoint_Paths_Search_correct_3
    by (sep_auto heap: Disjoint_Paths_Search_run_imp_rule simp: state_assn_def eq)
qed

end

end
