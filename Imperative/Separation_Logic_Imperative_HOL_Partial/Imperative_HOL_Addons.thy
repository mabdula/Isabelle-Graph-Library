theory Imperative_HOL_Addons
  imports Separation_Logic_Imperative_HOL_Partial.Sep_Main
begin

section \<open>Additions to Imperative HOL\<close>

subsection \<open>Precondition Rules\<close>

lemma ht_ex_pre: "(\<And> x. <P x> c <Q>) \<Longrightarrow> <\<exists>\<^sub>A x. P x> c <Q>"
  unfolding hoare_triple_wlp
  by (auto simp: mod_ex_dist)

lemma ex_mid:
  assumes "\<And> x. <P x * Fm> c <Q>"
  shows "<(\<exists>\<^sub>A x. P x) * Fm> c <Q>"
proof-
  have "<\<exists>\<^sub>A x. P x * Fm> c <Q>"
    by (rule ht_ex_pre) (rule assms)
  then show ?thesis
    by (rule ht_cons_pre[rotated]) sep_auto
qed

lemma ht_ex_pre_and_post_I:
  "(\<And> x. <P x> c <\<lambda> r. Q x r>) \<Longrightarrow> <\<exists>\<^sub>A x. P x> c <\<lambda> r. \<exists>\<^sub>A x. Q x r>"
 by sep_auto

lemma triple_res_ht_ex_pre_and_post_I:"(\<And> x. <P x> c <\<lambda> (r1,r2,r3). Q x r1 r2 r3>)
           \<Longrightarrow> <\<exists>\<^sub>A x. P x> c <\<lambda> (r1,r2,r3). \<exists>\<^sub>A x. Q x r1 r2 r3>"
  by sep_auto

lemma ht_pure_pre: "(b \<Longrightarrow> <P> c <Q>) \<Longrightarrow> <P * \<up>b> c <Q>"
  by (auto simp: hoare_triple_wlp mod_pure_star_dist)

lemma pure_mid:
  assumes "b \<Longrightarrow> <P * Fm> c <Q>"
  shows "<P * \<up>b * Fm> c <Q>"
  by (rule ht_cons_pre[OF _ ht_pure_pre[OF assms]]) (simp only: star_aci, rule ent_refl)


subsection \<open>Framing\<close>

text \<open>Framing a triple, with the pre- and postconditions rearranged by entailments.\<close>

lemma ht_frame_ac:
  assumes "<P> c <Q>" "P' \<Longrightarrow>\<^sub>A P * R" "\<And> x. Q x * R \<Longrightarrow>\<^sub>A Q' x"
  shows "<P'> c <Q'>"
  using ht_frame[OF assms(1)] assms(2) ent_true_drop(2)[OF assms(3)]
  by (rule ht_cons[rotated 2])

subsection \<open>Sequencing\<close>

text \<open>Binding a freshly allocated object to a continuation.\<close>

lemma alloc_bind:
  assumes "<emp> c <Q>" "\<And> x. <Fm * Q x> f x <Qp>"
  shows "<Fm> c \<bind> f <Qp>"
  by (sep_auto heap: assms)

subsection \<open>Conditionals\<close>

lemma heap_cond_return:
  "<A S> f <\<lambda>_. A S'> \<Longrightarrow>
   <A S> (if b then f else return ()) <\<lambda>_. A (if b then S' else S)>"
  by (cases b) sep_auto+

subsection \<open>Array Updates\<close>

lemma "<a \<mapsto>\<^sub>a xs * a' \<mapsto>\<^sub>a xs' * \<up> (i < length xs \<and> j < length xs')>
       do {Array.upd i x a; Array.upd j x' a'}
      <\<lambda> r. a \<mapsto>\<^sub>a xs[i:=x] * r \<mapsto>\<^sub>a xs'[j:=x'] * \<up> (i < length xs \<and> j < length xs')>"
  by sep_auto

end
