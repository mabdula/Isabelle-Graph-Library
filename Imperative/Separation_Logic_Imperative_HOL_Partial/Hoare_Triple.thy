section \<open>Hoare-Triples\<close>
theory Hoare_Triple
imports Run Assertions
begin

(* TODO: Move \<rightarrow> Assertions:thm merge_true_star *)  
lemma merge_true_star'[simp]:
  "true * (true * P) = true * P"
  "P * true * true = P * true"
  apply (metis assn_times_assoc merge_true_star)
  apply (metis assn_times_assoc merge_true_star)
  done


text \<open>In this theory, we define Hoare-Triples, which are our basic tool
  for specifying properties of Imperative HOL programs.\<close>

subsection \<open>Definition\<close>

text \<open>Analyze the heap before and after executing a command, to add
  the allocated addresses to the covered address range.\<close>
definition new_addrs :: "heap \<Rightarrow> addr set \<Rightarrow> heap \<Rightarrow> addr set" where
  "new_addrs h as h' = as \<union> {a. lim h \<le> a \<and> a < lim h'}"

lemma new_addr_refl[simp]: "new_addrs h as h = as"
  unfolding new_addrs_def by auto

text \<open>
  Apart from correctness of the program wrt. the pre- and post condition,
  a Hoare-triple also encodes some well-formedness conditions of the command:
  The command must not change addresses outside the address range of the 
  precondition, and it must not decrease the heap limit. 

  Note that we do not require that the command only reads from heap locations
  inside the precondition's address range, as this condition would be quite
  complicated to express with the heap model of Imperative/HOL, and is not 
  necessary in our formalization of partial heaps, that always contain the 
  information for all addresses.
  
  As Imperative HOL is a garbage collected language, we allow memory to be dropped
  by commands. This is built into our notion of Hoare-triple
\<close>
definition hoare_triple 
  :: "assn \<Rightarrow> 'a Heap \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> bool" ("<_>/ _/ <_>")
  where
  "<P> c <Q> \<equiv> \<forall>h as \<sigma> r. (h,as)\<Turnstile>P \<and> run c (Some h) \<sigma> r 
  \<longrightarrow> \<not>is_exn \<sigma> \<longrightarrow> (let h'=the_state \<sigma>; as'=new_addrs h as h' in  
     (h',as')\<Turnstile>Q r * true \<and> relH ({a . a<lim h \<and> a\<notin>as}) h h' 
    \<and> lim h \<le> lim h')"


text \<open>Weakest liberal precondition, and definition of Hoare triple based on wlp\<close>
definition "wlp c Q \<equiv> \<lambda>(h,as). \<forall>\<sigma> r. run c (Some h) \<sigma> r \<longrightarrow> \<not>is_exn \<sigma> \<longrightarrow> (let h'=the_state \<sigma>; as'=new_addrs h as h' in  
     Q r (h',as') \<and> relH ({a . a<lim h \<and> a\<notin>as}) h h' 
    \<and> lim h \<le> lim h')"
    
lemma hoare_triple_wlp: "hoare_triple P c Q \<longleftrightarrow> (\<forall>h. h \<Turnstile> P \<longrightarrow> wlp c (\<lambda>r h. h\<Turnstile>Q r * true) h)"
  unfolding hoare_triple_def wlp_def by blast
  
    
    
text \<open>Sanity checking theorems for Hoare-Triples\<close>  

text \<open>Connecting Hoare-triple with semantics of Imperative HOL\<close>
lemma hoare_triple_effect:
  assumes "<P> c <Q>"
  assumes "(h,as)\<Turnstile>P"
  shows "success c h \<Longrightarrow> \<exists>h' r. effect c h h' r \<and> (h',new_addrs h as h')\<Turnstile>Q r * true"
  using assms 
  unfolding hoare_triple_def success_def effect_def
  apply -
  apply (auto simp: Let_def run.simps)
  by (metis is_exn.simps(1) the_state.simps)

lemma wlp_effect: 
  assumes "wlp c Q (h,as)"
  shows "success c h \<Longrightarrow> \<exists>h' r. effect c h h' r \<and> Q r (h',new_addrs h as h')"
  using assms
  unfolding wlp_def success_def effect_def
  by (auto simp: Let_def run.simps)
  
lemma wlpI:
  assumes "let (h,as) = has in \<forall>\<sigma> r. run c (Some h) \<sigma> r \<longrightarrow> \<not>is_exn \<sigma> \<longrightarrow> (let h'=the_state \<sigma>; as'=new_addrs h as h' in  
     Q r (h',as') \<and> relH ({a . a<lim h \<and> a\<notin>as}) h h' 
    \<and> lim h \<le> lim h')"
  shows "wlp c Q has"
  using assms unfolding wlp_def by auto
    
    
lemma hoare_triple_wlpI:  
  assumes "\<And>h. h\<Turnstile>P \<Longrightarrow> wlp c (\<lambda>r h'. h' \<Turnstile> Q r * true) h"
  shows "<P> c <\<lambda>r. Q r>"
  using assms unfolding hoare_triple_wlp by auto
  
lemma hoare_tripleI:
  assumes "\<And>h as \<sigma> r. \<lbrakk> (h,as)\<Turnstile>P; run c (Some h) \<sigma> r; \<not>is_exn \<sigma> \<rbrakk> \<Longrightarrow> 
    let h'=the_state \<sigma>; as'=new_addrs h as h' in  
     (h',as')\<Turnstile>Q r * true \<and> relH ({a . a<lim h \<and> a\<notin>as}) h h' 
    \<and> lim h \<le> lim h'
  "
  shows "<P> c <Q>"
  unfolding hoare_triple_def using assms
  by blast

text \<open>Does not allow to drop memory. 
  Can make proofs easier if no memory is actually dropped. 
\<close>
lemma hoare_tripleI_prec:
  assumes "\<And>h as \<sigma> r. \<lbrakk> (h,as)\<Turnstile>P; run c (Some h) \<sigma> r; \<not>is_exn \<sigma> \<rbrakk> \<Longrightarrow> 
    let h'=the_state \<sigma>; as'=new_addrs h as h' in  
     (h',as')\<Turnstile>Q r \<and> relH ({a . a<lim h \<and> a\<notin>as}) h h' 
    \<and> lim h \<le> lim h'
  "
  shows "<P> c <Q>"
  unfolding hoare_triple_def using assms
  unfolding Let_def
  by (blast intro: mod_star_trueI)
    
  
lemma hoare_tripleD:
  fixes h h' as as' \<sigma> r
  assumes "<P> c <Q>"
  assumes "(h,as)\<Turnstile>P"
  assumes "run c (Some h) \<sigma> r"
  assumes "\<not>is_exn \<sigma>"
  defines "h'\<equiv>the_state \<sigma>" and "as'\<equiv>new_addrs h as h'"
  shows "(h',as')\<Turnstile>Q r * true"
  and "relH ({a . a<lim h \<and> a\<notin>as}) h h'"
  and "lim h \<le> lim h'"
  using assms 
  unfolding hoare_triple_def h'_def as'_def 
  by (auto simp: Let_def)
  
lemma hoare_triple_wlpD:
  assumes "<P> c <Q>"
  assumes "h\<Turnstile>P"
  shows "wlp c (\<lambda>r h'. h'\<Turnstile>Q r*true) h"
  using assms 
  unfolding hoare_triple_wlp
  by blast

lemma wlpD:
  fixes h h' as as' \<sigma> r
  assumes "wlp c Q (h,as)"
  assumes "run c (Some h) \<sigma> r"
  assumes "\<not>is_exn \<sigma>"
  defines "h'\<equiv>the_state \<sigma>" and "as'\<equiv>new_addrs h as h'"
  shows "Q r (h',as')"
  and "relH ({a . a<lim h \<and> a\<notin>as}) h h'"
  and "lim h \<le> lim h'"
  using assms 
  unfolding wlp_def h'_def as'_def 
  by (auto simp: Let_def)
  
subsection \<open>Rules\<close>
text \<open>
  In this section, we provide a set of rules to prove Hoare-Triples correct.
\<close>
subsubsection \<open>Basic Rules\<close>

lemma hoare_triple_preI: 
  assumes "\<And>h. h\<Turnstile>P \<Longrightarrow> <P> c <Q>"
  shows "<P> c <Q>"
  using assms
  unfolding hoare_triple_def
  by auto

  
lemma ht_frame: 
  assumes A: "<P> c <Q>"
  shows "<P*R> c <\<lambda>x. Q x * R>"
  unfolding hoare_triple_def Let_def
  apply (intro allI impI)
  apply (elim conjE)
  apply (intro conjI)
proof -
  fix h as
  assume "(h,as) \<Turnstile> P * R"
  then obtain as1 as2 where [simp]: "as=as1\<union>as2" and DJ: "as1\<inter>as2={}"
    and M1: "(h,as1)\<Turnstile>P" and M2: "(h,as2)\<Turnstile>R"
    unfolding times_assn_def
    by (auto simp: Abs_assn_inverse)

  fix \<sigma> r
  assume RUN: "run c (Some h) \<sigma> r"
  assume [simp]: "\<not> is_exn \<sigma>"
  from hoare_tripleD(3)[OF A M1 RUN] 
  show "lim h \<le> lim (the_state \<sigma>)" by simp

  from hoare_tripleD(2)[OF A M1 RUN] have 
    RH1: "relH {a. a < lim h \<and> a \<notin> as1} h (the_state \<sigma>)" by simp
  moreover have "{a. a < lim h \<and> a \<notin> as} \<subseteq> {a. a < lim h \<and> a \<notin> as1}"
    by auto
  ultimately show "relH {a. a < lim h \<and> a \<notin> as} h (the_state \<sigma>)" 
    by (blast intro: relH_subset)
    
  from hoare_tripleD(1)[OF A M1 RUN] have 
    "(the_state \<sigma>, new_addrs h as1 (the_state \<sigma>)) \<Turnstile> Q r * true" by simp
  moreover have DJN: "new_addrs h as1 (the_state \<sigma>) \<inter> as2 = {}"
    using DJ models_in_range[OF M2]
    by (auto simp: in_range.simps new_addrs_def)
  moreover have "as2 \<subseteq> {a. a < lim h \<and> a \<notin> as1}" 
    using DJ models_in_range[OF M2]
    by (auto simp: in_range.simps)
  hence "relH as2 h (the_state \<sigma>)" using RH1
    by (blast intro: relH_subset)
  with M2 have "(the_state \<sigma>, as2)\<Turnstile>R"
    by (metis mem_Collect_eq Rep_assn  
      proper_iff relH_in_rangeI(2))
  moreover have "new_addrs h as (the_state \<sigma>) 
    = new_addrs h as1 (the_state \<sigma>) \<union> as2"
    by (auto simp: new_addrs_def)
  ultimately show 
    "(the_state \<sigma>, new_addrs h as (the_state \<sigma>)) \<Turnstile> Q r * R * true"
    unfolding times_assn_def
    apply (simp add: Abs_assn_inverse)
    by (smt (verit) Un_Int_eq(4) Un_commute boolean_algebra.conj_disj_distrib2
        inf_commute sup_left_commute)
    
qed

lemma wlp_cons:
  assumes "wlp c (\<lambda>x. Q x) h"
  assumes "\<And>x h. Q x h \<Longrightarrow> Q' x h"
  shows "wlp c (\<lambda>x. Q' x) h"
  using assms unfolding wlp_def 
  by (auto simp: Let_def)

lemma ht_cons:
  assumes CPRE: "P \<Longrightarrow>\<^sub>A P'"
  assumes CPOST: "\<And>x. Q x \<Longrightarrow>\<^sub>A Q' x * true"
  assumes R: "<P'> c <Q>"
  shows "<P> c <Q'>"
  unfolding hoare_triple_def Let_def
  apply clarsimp
  subgoal for h as \<sigma> r
    apply (frule (2) hoare_tripleD(1)[OF R entailsD[OF CPRE]])
    apply (frule (2) hoare_tripleD(2)[OF R entailsD[OF CPRE]])
    apply (drule (2) hoare_tripleD(3)[OF R entailsD[OF CPRE]])
    apply clarsimp
    supply R = entailsD[OF ent_star_mono[OF CPOST ent_refl[of true]]]
    apply (drule R)
    by (simp)
    done

lemma ht_cons_prec:
  assumes CPRE: "P \<Longrightarrow>\<^sub>A P'"
  assumes CPOST: "\<And>x. Q x \<Longrightarrow>\<^sub>A Q' x"
  assumes R: "<P'> c <Q>"
  shows "<P> c <Q'>"
  by (metis CPOST CPRE R ht_cons ent_imp_entt enttD)
    
lemmas ht_cons_pre = ht_cons_prec[OF _ ent_refl]
lemmas ht_cons_post = ht_cons[OF ent_refl, rotated]
lemmas ht_cons_post_prec = ht_cons_prec[OF ent_refl, rotated]

lemma ht_cons_t: "\<lbrakk>P\<Longrightarrow>\<^sub>tP'; \<And>x. Q x \<Longrightarrow>\<^sub>t Q' x; <P'> c <Q> \<rbrakk> \<Longrightarrow> <P> c <Q'>"
  unfolding entailst_def
  by (metis (no_types, lifting) ht_cons ent_refl ht_frame)
  
lemmas ht_cons_pre_t = ht_cons_t[OF _ entt_refl]
lemmas ht_cons_post_t = ht_cons_t[OF entt_refl, rotated]


lemma ht_frame_drop: "<P> c <Q> \<Longrightarrow> <P*F> c <Q>"
  by (meson ht_cons_pre_t ent_refl ent_star_mono ent_true enttI)

(* Apply Hoare triple to wlp *)  
lemma wlp_apply_ht:
  assumes "h\<Turnstile>P'"
  assumes "P' \<Longrightarrow>\<^sub>A P*F"
  assumes "<P> c <\<lambda>r. Q r>"
  assumes "\<And>h r. h \<Turnstile> Q r * F * true \<Longrightarrow> Q' r h"
  shows "wlp c Q' h"
  using assms ht_cons_pre_t ent_imp_entt ht_frame hoare_triple_wlpD wlp_cons by blast

lemma ht_false[simp, intro!]: "<false> c <Q>"
  unfolding hoare_triple_def by simp

lemma ht_nterm[simp, intro!]: "<P> Heap.Heap (\<lambda>s. None) <Q>"
  unfolding hoare_triple_def Let_def
  apply (auto simp add: run.simps)
  done
  
lemma decon_nterm: "wlp (Heap.Heap (\<lambda>_. None)) (\<lambda>_ _. False) h" 
  unfolding wlp_def Let_def
  apply (auto simp add: run.simps)
  done

  
subsubsection \<open>Rules for Atomic Commands\<close>
lemma ref_rule:
  "<emp> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>"
  apply (rule hoare_tripleI_prec)
  unfolding one_assn_def sngr_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (elim conjE run_elims)
  apply simp
  apply (auto 
    simp: new_addrs_def Ref.alloc_def Let_def
    Ref.set_def Ref.get_def relH_def in_range.simps)
  done

lemma lookup_rule:
  "<p \<mapsto>\<^sub>r x> !p <\<lambda>r. p \<mapsto>\<^sub>r x * \<up>(r = x)>"
  apply (rule hoare_tripleI_prec)
  unfolding sngr_assn_def
  apply (simp add: Let_def Abs_assn_inverse mod_dist)
  apply (auto elim: run_elims simp add: relH_refl in_range.simps new_addrs_def)
  done

lemma update_rule:
  "<p \<mapsto>\<^sub>r y> p := x <\<lambda>r. p \<mapsto>\<^sub>r x>"
  apply (rule hoare_tripleI_prec)
  unfolding sngr_assn_def
  apply (auto elim!: run_update 
    simp: Let_def Abs_assn_inverse new_addrs_def in_range.simps 
    intro!: relH_set_ref)
  done

lemma update_wp_rule:
  "<r \<mapsto>\<^sub>r y * ((r \<mapsto>\<^sub>r x) -* (Q ()))> r := x <Q>"
  apply (rule ht_cons_post)
  apply (rule ht_frame[OF update_rule[where p=r and x=x], 
    where R="((r \<mapsto>\<^sub>r x) -* (Q ()))"])
  apply simp
  using ent_imp_entt ent_mp entailst_def by blast

lemma new_rule:
  "<emp> Array.new n x <\<lambda>r. r \<mapsto>\<^sub>a replicate n x>"
  apply (rule hoare_tripleI_prec)
  unfolding snga_assn_def one_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps
  )
  done

lemma make_rule: "<emp> Array.make n f <\<lambda>r. r \<mapsto>\<^sub>a (map f [0 ..< n])>"
  apply (rule hoare_tripleI_prec)
  unfolding snga_assn_def one_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps
  )
  done
    
lemma of_list_rule: "<emp> Array.of_list xs <\<lambda>r. r \<mapsto>\<^sub>a xs>"
  apply (rule hoare_tripleI_prec)
  unfolding snga_assn_def one_assn_def
  apply (simp add: Let_def Abs_assn_inverse)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps
  )
  done

lemma length_rule:
  "<a \<mapsto>\<^sub>a xs> Array.len a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = length xs)>"
  apply (rule hoare_tripleI_prec)
  unfolding snga_assn_def
  apply (simp add: Let_def Abs_assn_inverse mod_dist)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps Array.length_def
  )
  done

text \<open>Note that the Boolean expression is placed at meta level and not 
  inside the precondition. This makes frame inference simpler.\<close>
lemma nth_rule:
  "\<^cancel>\<open>\<lbrakk>i < length xs\<rbrakk> \<Longrightarrow>\<close> <a \<mapsto>\<^sub>a xs> Array.nth a i <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs ! i \<and> i<length xs)>"
  apply (rule hoare_tripleI_prec)
  unfolding snga_assn_def
  apply (simp add: Let_def Abs_assn_inverse mod_dist)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps Array.length_def
  )
  done

lemma upd_rule:
  "\<^cancel>\<open>\<lbrakk>i < length xs\<rbrakk> \<Longrightarrow> \<close>
  <a \<mapsto>\<^sub>a xs> 
  Array.upd i x a 
  <\<lambda>r. (a \<mapsto>\<^sub>a (list_update xs i x)) * \<up>(r = a \<and> i<length xs)>"
  apply (rule hoare_tripleI_prec)
  unfolding snga_assn_def
  apply (simp add: Let_def Abs_assn_inverse mod_dist)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps Array.length_def Array.update_def comp_def
  )
  done

lemma freeze_rule:
  "<a \<mapsto>\<^sub>a xs> Array.freeze a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs)>"
  apply (rule hoare_tripleI_prec)
  unfolding snga_assn_def
  apply (simp add: Let_def Abs_assn_inverse mod_dist)
  apply (auto 
    elim!: run_elims
    simp: Let_def new_addrs_def Array.get_def Array.set_def Array.alloc_def
      relH_def in_range.simps Array.length_def Array.update_def
  )
  done
  
lemma ht_return_wp:
  "<Q x> return x <Q>"
  apply (rule hoare_tripleI_prec)
  unfolding Let_def
  apply (auto elim!: run_elims)
  apply (rule relH_refl)
  apply (simp add: in_range.simps)
  done

lemma ht_return_sp:
  "<P> return x <\<lambda>r. P * \<up>(r = x)>"
  apply (rule hoare_tripleI_prec)
  unfolding Let_def
  apply (simp add: Abs_assn_inverse mod_dist)
  apply (auto elim!: run_elims intro!: relH_refl intro: models_in_range)
  apply (simp add: in_range.simps)
  done

lemma ht_raise[simp,intro!]: 
  "<P> raise s <Q>"
  apply (rule hoare_tripleI_prec)
  unfolding Let_def
  apply (auto simp add: run_raise_iff)
  done

lemma decon_raise:
  "wlp (raise s) Q h"
  unfolding wlp_def
  unfolding Let_def
  apply (auto simp add: run_raise_iff)
  done
  
lemma decon_return: "Q x h \<Longrightarrow> wlp (return x) Q h"
  unfolding Let_def wlp_def
  apply (auto elim!: run_elims)
  apply (rule relH_refl)
  apply (simp add: in_range.simps)
  done


subsubsection \<open>Rules for Composed Commands\<close>


lemma decon_bind:
  assumes A: "wlp m (\<lambda>x. wlp (f x) Q) hh"
  shows "wlp (bind m (\<lambda>x. f x)) Q hh"
  apply (rule wlpI)
  apply (cases hh; clarsimp elim!: run_elims simp: Let_def)
  apply (intro conjI)
proof -
  fix h as \<sigma>'' r'' \<sigma>' r'
  
  assume [simp]: "hh=(h,as)"
  
  assume  
        R1: "run m (Some h) \<sigma>' r'" 
    and R2: "run (f r') \<sigma>' \<sigma>'' r''"

  assume NO_E''[simp]: "\<not> is_exn \<sigma>''"  

  then have NO_E[simp]: "\<not> is_exn \<sigma>'"
    using R2 by (metis run_exn)

  from A have A: "wlp m (\<lambda>x. wlp (f x) Q) (h,as)" by simp
      
  from wlpD[OF A R1 NO_E] have
    M': "wlp (f r') Q (the_state \<sigma>', new_addrs h as (the_state \<sigma>'))"
    and RH': "relH {a. a < lim h \<and> a \<notin> as} h (the_state \<sigma>')"
    and LIM: "lim h \<le> lim (the_state \<sigma>')"
    by auto
    
  from NO_E have [simp]: "Some (the_state \<sigma>') = \<sigma>'" by (cases \<sigma>') auto

  from wlpD[OF M', simplified, OF R2 NO_E''] have
    M'': "Q r'' (the_state \<sigma>'', new_addrs (the_state \<sigma>') (new_addrs h as (the_state \<sigma>')) (the_state \<sigma>''))"
    and RH'': 
    "relH 
      {a. a < lim (the_state \<sigma>') 
        \<and> a \<notin> new_addrs h as (the_state \<sigma>')
      }
      (the_state \<sigma>') (the_state \<sigma>'')"
    and LIM': "lim (the_state \<sigma>') \<le> lim (the_state \<sigma>'')"
    by auto
    
  have  
    "new_addrs 
      (the_state \<sigma>') 
      (new_addrs h as (the_state \<sigma>')) 
      (the_state \<sigma>'') 
    = new_addrs h as (the_state \<sigma>'')" 
    using LIM LIM' 
    by (auto simp add: new_addrs_def)
  with M'' show "Q r'' (the_state \<sigma>'', new_addrs h as (the_state \<sigma>''))" by simp
    
  note RH'
  also have "relH {a. a < lim h \<and> a \<notin> as} (the_state \<sigma>') (the_state \<sigma>'')"
    apply (rule relH_subset[OF RH''])
    using LIM LIM'
    by (auto simp: new_addrs_def)
  finally show "relH {a. a < lim h \<and> a \<notin> as} h (the_state \<sigma>'')" .

  note LIM
  also note LIM'
  finally show "lim h \<le> lim (the_state \<sigma>'')" .
qed


lemma ht_bind: 
  assumes T1: "<P> f <R>"
  assumes T2: "\<And>x. <R x> g x <Q>"
  shows "<P> bind f g <Q>"
  unfolding hoare_triple_def Let_def
  apply (intro allI impI)
  apply (elim conjE run_elims)
  apply (intro conjI)
proof -
  fix h as \<sigma>'' r'' \<sigma>' r'
  assume M: "(h,as) \<Turnstile> P" 
    and R1: "run f (Some h) \<sigma>' r'" 
    and R2: "run (g r') \<sigma>' \<sigma>'' r''"

  assume NO_E''[simp]: "\<not> is_exn \<sigma>''"  
  then have NO_E[simp]: "\<not> is_exn \<sigma>'"
    using R2 by (metis run_exn)
    
  from hoare_tripleD[OF T1 M R1] have  
        M': "(the_state \<sigma>', new_addrs h as (the_state \<sigma>')) \<Turnstile> R r' * true"
    and RH': "relH {a. a < lim h \<and> a \<notin> as} h (the_state \<sigma>')"
    and LIM: "lim h \<le> lim (the_state \<sigma>')"
    by auto

  from NO_E have [simp]: "Some (the_state \<sigma>') = \<sigma>'" by (cases \<sigma>') auto

  from T2 have T2': "<R r' * true> g r' <Q>" by (rule ht_frame_drop)
  
  from hoare_tripleD[OF T2' M', simplified, OF R2] have 
    M'': "(the_state \<sigma>'',
      new_addrs (the_state \<sigma>') 
        (new_addrs h as (the_state \<sigma>')) (the_state \<sigma>'')) 
      \<Turnstile> Q r'' * true"
    and RH'': 
    "relH 
      {a. a < lim (the_state \<sigma>') 
        \<and> a \<notin> new_addrs h as (the_state \<sigma>')
      }
      (the_state \<sigma>') (the_state \<sigma>'')"
    and LIM': "lim (the_state \<sigma>') \<le> lim (the_state \<sigma>'')"
    by auto
  
  (*show "\<not> is_exn \<sigma>''" by fact*)

  have  
    "new_addrs 
      (the_state \<sigma>') 
      (new_addrs h as (the_state \<sigma>')) 
      (the_state \<sigma>'') 
    = new_addrs h as (the_state \<sigma>'')" 
    using LIM LIM' 
    by (auto simp add: new_addrs_def)
  with M'' show 
    "(the_state \<sigma>'', new_addrs h as (the_state \<sigma>'')) \<Turnstile> Q r'' * true"
    by simp

  note RH'
  also have "relH {a. a < lim h \<and> a \<notin> as} (the_state \<sigma>') (the_state \<sigma>'')"
    apply (rule relH_subset[OF RH''])
    using LIM LIM'
    by (auto simp: new_addrs_def)
  finally show "relH {a. a < lim h \<and> a \<notin> as} h (the_state \<sigma>'')" .

  note LIM
  also note LIM'
  finally show "lim h \<le> lim (the_state \<sigma>'')" .
qed

lemma decon_if:
  assumes  "b \<Longrightarrow> wlp f Q h"
  assumes  "\<not>b \<Longrightarrow> wlp g Q h"
  shows "wlp (if b then f else g) Q h"
  using assms by auto

lemma decon_case_prod: 
  "(\<And>a b. x = (a, b) \<Longrightarrow> wlp (f a b) Q h) \<Longrightarrow> wlp (case x of (a, b) \<Rightarrow> f a b) Q h"
  by (auto split: prod.split)

lemma decon_case_list:
  "\<lbrakk> l=[] \<Longrightarrow> wlp fn Q h; \<And>x xs. l=x#xs \<Longrightarrow> wlp (fc x xs) Q h \<rbrakk> \<Longrightarrow> 
  wlp (case l of [] \<Rightarrow> fn | x#xs \<Rightarrow> fc x xs) Q h"
  by (auto split: list.split)

lemma decon_case_option:
  "\<lbrakk> v=None \<Longrightarrow> wlp fn Q h; \<And>x. v=Some x \<Longrightarrow> wlp (fs x) Q h \<rbrakk> 
  \<Longrightarrow> wlp (case v of None \<Rightarrow> fn | Some x \<Rightarrow> fs x) Q h"
  by (auto split: option.split)

lemma decon_case_sum:
  "\<lbrakk> \<And>x. v=Inl x \<Longrightarrow> wlp (fl x) Q h; 
     \<And>y. v=Inr y \<Longrightarrow> wlp (fr y) Q h \<rbrakk> 
  \<Longrightarrow> wlp (case v of Inl x \<Rightarrow> fl x | Inr y \<Rightarrow> fr y) Q h"
  by (auto split: sum.split)

lemma decon_let: "(\<And>x. x = t \<Longrightarrow> wlp (f x) Q h) \<Longrightarrow> wlp (let x=t in f x) Q h"
  by (auto)

end
