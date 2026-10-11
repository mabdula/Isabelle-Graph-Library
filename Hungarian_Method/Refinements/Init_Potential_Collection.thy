theory Init_Potential_Collection
  imports
    Data_Structures.Iterable_Set_Specs
    Data_Structures.Fixed_Univ_Map_Specs
    Directed_Set_Graphs.More_Arith
begin

section \<open>The Initial Potential over a Collection of Neighbourhoods\<close>

text \<open>The initial potential of the Hungarian method assigns to every left vertex @{term u} the
      minimum weight of an edge at @{term u}, and 0 to the right vertices. Here, the
      neighbourhoods are given by a collection with cursors (@{locale indexed_iterable_set}), which
      is scanned vertex by vertex. This is the functional counterpart of the imperative
      computation over CSR neighbourhoods, which reads the weights at the cursor.\<close>

locale init_potential_coll_spec =
  fixes potential_upd :: "'potential \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> 'potential"
    and potential_get :: "'potential \<Rightarrow> 'v \<Rightarrow> real"
    and rnb_current :: "'g \<Rightarrow> 'v \<Rightarrow> 'v"
    and rnb_has :: "'g \<Rightarrow> 'v \<Rightarrow> bool"
    and rnb_move :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
    and rnb_reset :: "'g \<Rightarrow> 'v \<Rightarrow> 'g"
    and cost :: "'v \<Rightarrow> 'v \<Rightarrow> real"
    and vset_iterate :: "('g \<times> 'potential \<Rightarrow> 'v \<Rightarrow> 'g \<times> 'potential)
                          \<Rightarrow> 'g \<times> 'potential \<Rightarrow> 'vset \<Rightarrow> 'g \<times> 'potential"
begin

definition "upd_min u c \<pi> = (if potential_get \<pi> u \<le> c then \<pi> else potential_upd \<pi> u c)"

partial_function (tailrec) scan_min :: "'v \<Rightarrow> 'g \<Rightarrow> 'potential \<Rightarrow> 'g \<times> 'potential" where
  "scan_min u C \<pi> =
     (if rnb_has C u then scan_min u (rnb_move C u) (upd_min u (cost u (rnb_current C u)) \<pi>)
      else (C, \<pi>))"

text \<open>The first neighbour sets the value of @{term u}, the others can only decrease it.\<close>

definition "init_step Cp u =
  (let C = rnb_reset (fst Cp) u
   in if rnb_has C u
      then scan_min u (rnb_move C u) (potential_upd (snd Cp) u (cost u (rnb_current C u)))
      else (C, snd Cp))"

definition "init_potential_coll C0 pot0 left = vset_iterate init_step (C0, pot0) left"

lemmas [code] = upd_min_def scan_min.simps init_step_def init_potential_coll_def

end

locale init_potential_coll = init_potential_coll_spec +
  pot: fixed_univ_map K potential_invar potential_upd potential_get +
  rnb: indexed_iterable_set rnb_invar rnb_abstract rnb_current rnb_has rnb_iterated
      rnb_remaining rnb_move rnb_reset K
  for potential_invar and rnb_invar rnb_abstract rnb_iterated rnb_remaining K +
  fixes potential_empty and vset_to_set and vset_invar and lst
  assumes potential_empty: "potential_invar potential_empty"
      "potential_get potential_empty = (\<lambda> _. 0)"
    and vset_iterate_lst:
      "\<And>V f init. vset_invar V \<Longrightarrow> vset_iterate f init V = foldl f init (lst (vset_to_set V))"
    and lst_set: "\<And>S. finite S \<Longrightarrow> set (lst S) = S"
begin

abbreviation "fmin u \<equiv> (\<lambda>\<pi> v. upd_min u (cost u v) \<pi>)"

lemma scan_min_is_foldl:
  assumes "rnb_invar C" "u \<in> K" "finite (rnb_remaining C u)"
  shows "\<exists>rs. set rs = rnb_remaining C u \<and>
            snd (scan_min u C \<pi>) = foldl (fmin u) \<pi> rs \<and>
            rnb_invar (fst (scan_min u C \<pi>)) \<and>
            rnb_abstract (fst (scan_min u C \<pi>)) = rnb_abstract C"
  using assms
proof(induction "card (rnb_remaining C u)" arbitrary: C \<pi>)
  case 0
  hence empty: "rnb_remaining C u = {}" by simp
  hence not_has: "\<not> rnb_has C u" using rnb.idx_has[OF 0(2,3)] by simp
  show ?case
    using 0(2) by (auto intro!: exI[of _ "[]"] simp: scan_min.simps[of u C \<pi>] not_has empty)
next
  case (Suc n)
  hence ne: "rnb_remaining C u \<noteq> {}" by auto
  hence has: "rnb_has C u" using rnb.idx_has[OF Suc(3,4)] by simp
  define x where "x = rnb_current C u"
  define C' where "C' = rnb_move C u"
  have x_in: "x \<in> rnb_remaining C u" using rnb.idx_current[OF Suc(3,4) ne] by (simp add: x_def)
  have C': "rnb_invar C'" "rnb_remaining C' u = rnb_remaining C u - {x}"
           "rnb_abstract C' = rnb_abstract C"
    using rnb.idx_move_invar[OF Suc(3,4)] rnb.idx_move_remaining[OF Suc(3,4) ne]
          rnb.idx_move_abstract[OF Suc(3,4) ne]
    by (auto simp: C'_def x_def fun_eq_iff)
  have card: "n = card (rnb_remaining C' u)" using Suc(2,5) x_in by (simp add: C'(2))
  obtain rs where rs: "set rs = rnb_remaining C' u"
     "snd (scan_min u C' (fmin u \<pi> x)) = foldl (fmin u) (fmin u \<pi> x) rs"
     "rnb_invar (fst (scan_min u C' (fmin u \<pi> x)))"
     "rnb_abstract (fst (scan_min u C' (fmin u \<pi> x))) = rnb_abstract C'"
    using Suc(1)[OF card C'(1) Suc(4)] Suc(5) by (auto simp: C'(2))
  have eq: "scan_min u C \<pi> = scan_min u C' (fmin u \<pi> x)"
    by (simp add: scan_min.simps[of u C \<pi>] has C'_def x_def)
  show ?case
    using rs x_in by (intro exI[of _ "x # rs"]) (auto simp: eq C'(2,3))
qed

lemma foldl_fmin:
  "\<lbrakk>potential_invar \<pi>; u \<in> K\<rbrakk> \<Longrightarrow>
   potential_invar (foldl (fmin u) \<pi> rs) \<and>
   (\<forall>w. w \<noteq> u \<longrightarrow> potential_get (foldl (fmin u) \<pi> rs) w = potential_get \<pi> w) \<and>
   (\<forall>v\<in>set rs. potential_get (foldl (fmin u) \<pi> rs) u \<le> cost u v) \<and>
   potential_get (foldl (fmin u) \<pi> rs) u \<le> potential_get \<pi> u"
proof(induction rs arbitrary: \<pi>)
  case (Cons v rs)
  define \<pi>' where "\<pi>' = fmin u \<pi> v"
  have p': "potential_invar \<pi>'"
           "\<And>w. w \<noteq> u \<Longrightarrow> potential_get \<pi>' w = potential_get \<pi> w"
           "potential_get \<pi>' u \<le> cost u v" "potential_get \<pi>' u \<le> potential_get \<pi> u"
    using Cons.prems
    by (auto simp: \<pi>'_def upd_min_def pot.fixed_univ_map_upd pot.fixed_univ_map_upd_invar)
  have IH: "potential_invar (foldl (fmin u) \<pi>' rs)"
       "\<And>w. w \<noteq> u \<Longrightarrow> potential_get (foldl (fmin u) \<pi>' rs) w = potential_get \<pi>' w"
       "\<And>v. v\<in>set rs \<Longrightarrow> potential_get (foldl (fmin u) \<pi>' rs) u \<le> cost u v"
       "potential_get (foldl (fmin u) \<pi>' rs) u \<le> potential_get \<pi>' u"
    using Cons.IH[OF p'(1) Cons.prems(2)] by auto
  show ?case
    using IH p' by (fastforce simp: \<pi>'_def)
qed simp

text \<open>The invariant of the iteration over the left vertices.\<close>

definition "init_inv C0 pot0 S Cp =
  (rnb_invar (fst Cp) \<and> rnb_abstract (fst Cp) = rnb_abstract C0 \<and>
   potential_invar (snd Cp) \<and>
   (\<forall>u\<in>S. \<forall>v\<in>rnb_abstract C0 u. potential_get (snd Cp) u \<le> cost u v) \<and>
   (\<forall>w. w \<notin> S \<longrightarrow> potential_get (snd Cp) w = potential_get pot0 w))"

lemma init_step_inv:
  assumes "init_inv C0 pot0 S Cp" "u \<in> K" "finite (rnb_abstract C0 u)"
  shows "init_inv C0 pot0 (insert u S) (init_step Cp u)"
proof-
  obtain C \<pi> where Cp: "Cp = (C, \<pi>)" by (cases Cp) auto
  have I: "rnb_invar C" "rnb_abstract C = rnb_abstract C0" "potential_invar \<pi>"
          "\<forall>u\<in>S. \<forall>v\<in>rnb_abstract C0 u. potential_get \<pi> u \<le> cost u v"
          "\<forall>w. w \<notin> S \<longrightarrow> potential_get \<pi> w = potential_get pot0 w"
    using assms(1) by (auto simp: init_inv_def Cp)
  define C1 where "C1 = rnb_reset C u"
  have C1: "rnb_invar C1" "rnb_remaining C1 u = rnb_abstract C0 u"
           "rnb_abstract C1 = rnb_abstract C0"
    using rnb.idx_reset_invar[OF I(1) assms(2)] rnb.idx_reset_remaining[OF I(1) assms(2)]
          rnb.idx_reset_abstract[OF I(1) assms(2)] I(2)
    by (auto simp: C1_def fun_eq_iff)
  show ?thesis
  proof(cases "rnb_has C1 u")
    case False
    hence "rnb_abstract C0 u = {}" 
      using rnb.idx_has[OF C1(1) assms(2)] C1(2) by simp
    thus ?thesis 
      using I C1 False by (auto simp: init_inv_def init_step_def Cp C1_def)
  next
    case True
    define x where "x = rnb_current C1 u"
    define C2 where "C2 = rnb_move C1 u"
    have ne: "rnb_remaining C1 u \<noteq> {}" using rnb.idx_has[OF C1(1) assms(2)] True by simp
    have x_in: "x \<in> rnb_abstract C0 u" 
      using rnb.idx_current[OF C1(1) assms(2) ne] C1(2) by (simp add: x_def)
    have C2: "rnb_invar C2" "rnb_remaining C2 u = rnb_abstract C0 u - {x}"
             "rnb_abstract C2 = rnb_abstract C0"
      using rnb.idx_move_invar[OF C1(1) assms(2)] rnb.idx_move_remaining[OF C1(1) assms(2) ne]
            rnb.idx_move_abstract[OF C1(1) assms(2) ne] C1(2,3)
      by (auto simp: C2_def x_def fun_eq_iff)
    define \<pi>1 where "\<pi>1 = potential_upd \<pi> u (cost u x)"
    have p1: "potential_invar \<pi>1" "potential_get \<pi>1 = (potential_get \<pi>)(u := cost u x)"
      using pot.fixed_univ_map_upd_invar[OF I(3) assms(2)] pot.fixed_univ_map_upd[OF I(3) assms(2)]
      by (auto simp: \<pi>1_def)
    obtain rs where rs: "set rs = rnb_abstract C0 u - {x}"
        "snd (scan_min u C2 \<pi>1) = foldl (fmin u) \<pi>1 rs"
        "rnb_invar (fst (scan_min u C2 \<pi>1))"
        "rnb_abstract (fst (scan_min u C2 \<pi>1)) = rnb_abstract C2"
      using scan_min_is_foldl[OF C2(1) assms(2), of \<pi>1] assms(3) C2(2) by auto
    note F = foldl_fmin[OF p1(1) assms(2), of rs]
    have st: "init_step Cp u = scan_min u C2 \<pi>1"
      by (simp add: init_step_def Cp C1_def[symmetric] True C2_def x_def \<pi>1_def Let_def)
    show ?thesis
      unfolding init_inv_def st
    proof(intro conjI ballI allI impI)
      show "rnb_invar (fst (scan_min u C2 \<pi>1))" using rs(3) .
      show "rnb_abstract (fst (scan_min u C2 \<pi>1)) = rnb_abstract C0" using rs(4) C2(3) by simp
      show "potential_invar (snd (scan_min u C2 \<pi>1))" using F rs(2) by simp
    next
      fix u' v assume u': "u' \<in> insert u S" and v: "v \<in> rnb_abstract C0 u'"
      show "potential_get (snd (scan_min u C2 \<pi>1)) u' \<le> cost u' v"
      proof(cases "u' = u")
        case True
        thus ?thesis using F v rs(1,2) p1(2) by (cases "v = x") fastforce+
      next
        case False
        hence "u' \<in> S" using u' by simp
        thus ?thesis using F I(4) v False rs(2) p1(2) by auto
      qed
    next
      fix w assume "w \<notin> insert u S"
      thus "potential_get (snd (scan_min u C2 \<pi>1)) w = potential_get pot0 w"
        using F I(5) rs(2) p1(2) by auto
    qed
  qed
qed

lemma foldl_init_step_inv:
  "\<lbrakk>init_inv C0 pot0 S Cp; set xs \<subseteq> K; \<forall>u\<in>set xs. finite (rnb_abstract C0 u)\<rbrakk> \<Longrightarrow>
   init_inv C0 pot0 (S \<union> set xs) (foldl init_step Cp xs)"
proof(induction xs arbitrary: S Cp)
  case (Cons x xs)
  have "init_inv C0 pot0 (insert x S) (init_step Cp x)"
    using init_step_inv[OF Cons.prems(1)] Cons.prems(2,3) by simp
  from Cons.IH[OF this] Cons.prems(2,3) show ?case by simp
qed simp

theorem init_potential_coll_props:
  assumes "rnb_invar C0" "vset_invar left" "finite (vset_to_set left)"
          "vset_to_set left \<subseteq> K" "\<And>u. u \<in> vset_to_set left \<Longrightarrow> finite (rnb_abstract C0 u)"
  defines "res \<equiv> init_potential_coll C0 potential_empty left"
  shows "potential_invar (snd res)"
        "\<And>u v. \<lbrakk>u \<in> vset_to_set left; v \<in> rnb_abstract C0 u\<rbrakk> \<Longrightarrow>
               potential_get (snd res) u \<le> cost u v"
        "\<And>u. u \<notin> vset_to_set left \<Longrightarrow> potential_get (snd res) u = 0"
        "rnb_invar (fst res)" "rnb_abstract (fst res) = rnb_abstract C0"
proof-
  have i0: "init_inv C0 potential_empty {} (C0, potential_empty)"
    using assms(1) potential_empty by (auto simp: init_inv_def)
  have res: "res = foldl init_step (C0, potential_empty) (lst (vset_to_set left))"
    by (simp add: res_def init_potential_coll_def vset_iterate_lst[OF assms(2)])
  have I: "init_inv C0 potential_empty (vset_to_set left) res"
    using foldl_init_step_inv[OF i0, of "lst (vset_to_set left)"] assms(4,5)
          lst_set[OF assms(3)]
    by (simp add: res)
  show "potential_invar (snd res)" "rnb_invar (fst res)" "rnb_abstract (fst res) = rnb_abstract C0"
       "\<And>u v. \<lbrakk>u \<in> vset_to_set left; v \<in> rnb_abstract C0 u\<rbrakk> \<Longrightarrow>
               potential_get (snd res) u \<le> cost u v"
       "\<And>u. u \<notin> vset_to_set left \<Longrightarrow> potential_get (snd res) u = 0"
    using I potential_empty(2) by (auto simp: init_inv_def)
qed

end

end
