theory Init_Potential_Collection
  imports
    Data_Structures.Iterable_Set_Specs
    Data_Structures.Fixed_Univ_Map_Specs
    Data_Structures.More_Arith
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

lemma upd_min_props:
  "\<lbrakk>potential_invar \<pi>; u \<in> K\<rbrakk> \<Longrightarrow>
     potential_invar (upd_min u c \<pi>) \<and> potential_get (upd_min u c \<pi>) u \<le> c \<and>
     potential_get (upd_min u c \<pi>) u \<le> potential_get \<pi> u \<and>
     (\<forall>w. w \<noteq> u \<longrightarrow> potential_get (upd_min u c \<pi>) w = potential_get \<pi> w)"
  by (auto simp: upd_min_def pot.fixed_univ_map_upd pot.fixed_univ_map_upd_invar)

lemma scan_min_props:
  assumes "rnb_invar C" "u \<in> K" "finite (rnb_remaining C u)" "potential_invar \<pi>"
  shows "rnb_invar (fst (scan_min u C \<pi>)) \<and> rnb_abstract (fst (scan_min u C \<pi>)) = rnb_abstract C \<and>
         potential_invar (snd (scan_min u C \<pi>)) \<and>
         (\<forall>w. w \<noteq> u \<longrightarrow> potential_get (snd (scan_min u C \<pi>)) w = potential_get \<pi> w) \<and>
         (\<forall>v\<in>rnb_remaining C u. potential_get (snd (scan_min u C \<pi>)) u \<le> cost u v) \<and>
         potential_get (snd (scan_min u C \<pi>)) u \<le> potential_get \<pi> u"
  using assms
proof(induction "card (rnb_remaining C u)" arbitrary: C \<pi>)
  case 0
  thus ?case
    by (simp add: scan_min.simps[of u C \<pi>] rnb.idx_has)
next
  case (Suc n)
  hence "rnb_remaining C u \<noteq> {}"
    by auto
  with Suc have "rnb_has C u" "rnb_abstract (rnb_move C u) = rnb_abstract C"
      "n = card (rnb_remaining (rnb_move C u) u)" "finite (rnb_remaining (rnb_move C u) u)"
      "rnb_remaining C u = insert (rnb_current C u) (rnb_remaining (rnb_move C u) u)"
    using rnb.idx_current[of C u]
    by (auto simp: rnb.idx_has rnb.idx_move_abstract rnb.idx_move_remaining fun_eq_iff)
  thus ?case
    using Suc(1)[of "rnb_move C u" "fmin u \<pi> (rnb_current C u)"] Suc(2-)
          upd_min_props[of \<pi> u "cost u (rnb_current C u)"]
    by (fastforce simp: scan_min.simps[of u C \<pi>] rnb.idx_move_invar)
qed

text \<open>The invariant of the iteration over the left vertices.\<close>

definition "init_inv C0 pot0 S Cp =
  (rnb_invar (fst Cp) \<and> rnb_abstract (fst Cp) = rnb_abstract C0 \<and>
   potential_invar (snd Cp) \<and>
   (\<forall>u\<in>S. \<forall>v\<in>rnb_abstract C0 u. potential_get (snd Cp) u \<le> cost u v) \<and>
   (\<forall>w. w \<notin> S \<longrightarrow> potential_get (snd Cp) w = potential_get pot0 w))"

lemma init_step_props:
  assumes "rnb_invar C" "u \<in> K" "finite (rnb_abstract C u)" "potential_invar \<pi>"
          "init_step (C, \<pi>) u = (C', \<pi>')"
  shows "rnb_invar C' \<and> rnb_abstract C' = rnb_abstract C \<and> potential_invar \<pi>' \<and>
         (\<forall>v\<in>rnb_abstract C u. potential_get \<pi>' u \<le> cost u v) \<and>
         (\<forall>w. w \<noteq> u \<longrightarrow> potential_get \<pi>' w = potential_get \<pi> w)"
proof(cases "rnb_has (rnb_reset C u) u")
  case True
  let ?C = "rnb_move (rnb_reset C u) u" and ?x = "rnb_current (rnb_reset C u) u"
  have "rnb_invar ?C" "?x \<in> rnb_abstract C u" "rnb_remaining ?C u = rnb_abstract C u - {?x}"
       "rnb_abstract ?C = rnb_abstract C"
    using assms True rnb.idx_current[of "rnb_reset C u" u]
    by (auto simp: rnb.idx_has rnb.idx_reset_invar rnb.idx_reset_remaining rnb.idx_reset_abstract
                   rnb.idx_move_invar rnb.idx_move_remaining rnb.idx_move_abstract fun_eq_iff)
  moreover have "scan_min u ?C (potential_upd \<pi> u (cost u ?x)) = (C', \<pi>')"
    using True assms(5)
    by (simp add: init_step_def Let_def)
  ultimately show ?thesis
    using assms(2-4) scan_min_props[of ?C u "potential_upd \<pi> u (cost u ?x)"]
    by (auto simp: pot.fixed_univ_map_upd pot.fixed_univ_map_upd_invar)
qed (use assms in \<open>auto simp: init_step_def rnb.idx_has rnb.idx_reset_invar rnb.idx_reset_remaining
                               rnb.idx_reset_abstract fun_eq_iff\<close>)

lemma init_step_inv:
  "\<lbrakk>init_inv C0 pot0 S Cp; u \<in> K; finite (rnb_abstract C0 u)\<rbrakk>
     \<Longrightarrow> init_inv C0 pot0 (insert u S) (init_step Cp u)"
  using init_step_props[of "fst Cp" u "snd Cp" "fst (init_step Cp u)" "snd (init_step Cp u)"]
  by (auto simp: init_inv_def)

lemma foldl_init_step_inv:
  "\<lbrakk>init_inv C0 pot0 S Cp; set xs \<subseteq> K; \<forall>u\<in>set xs. finite (rnb_abstract C0 u)\<rbrakk> \<Longrightarrow>
   init_inv C0 pot0 (S \<union> set xs) (foldl init_step Cp xs)"
  by (induction xs arbitrary: S Cp) (simp_all add: init_step_inv flip: Un_insert_left)

lemma init_potential_coll_props:
  assumes "rnb_invar C0" "vset_invar left" "finite (vset_to_set left)"
          "vset_to_set left \<subseteq> K" "\<And>u. u \<in> vset_to_set left \<Longrightarrow> finite (rnb_abstract C0 u)"
  defines "res \<equiv> init_potential_coll C0 potential_empty left"
  shows "potential_invar (snd res)"
        "\<And>u v. \<lbrakk>u \<in> vset_to_set left; v \<in> rnb_abstract C0 u\<rbrakk> \<Longrightarrow>
               potential_get (snd res) u \<le> cost u v"
        "\<And>u. u \<notin> vset_to_set left \<Longrightarrow> potential_get (snd res) u = 0"
        "rnb_invar (fst res)" "rnb_abstract (fst res) = rnb_abstract C0"
  using foldl_init_step_inv[of C0 potential_empty "{}" "(C0, potential_empty)" "lst (vset_to_set left)"] assms
  by (auto simp: res_def init_potential_coll_def vset_iterate_lst[OF assms(2)] init_inv_def potential_empty lst_set)

end

end
