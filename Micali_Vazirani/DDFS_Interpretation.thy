theory DDFS_Interpretation
  imports DDFS IDFS
begin

text \<open>
Phase 2: Interpretation theory connecting the DDFS locale and the concrete IDFS.

This theory defines locale DDFS_layered (fixing a layered digraph dG and its level
function lev, with the three digraph assumptions of the DDFS locale) and exports all
available IDFS correctness properties.

GAP NOTE (Phase-1 alignment issue):
  The full sublocale claim
    DDFS_layered \<subseteq> DDFS dG lev IDFS
  cannot currently be proved, because the DDFS locale states
    IDFS_vis_works(1,2,4), IDFS_complete, IDFS_sound(3-8)
  UNIVERSALLY (for all p, without dpath or distinct premises), while our
  concrete IDFS only satisfies these when dpath dG (rev p) and distinct p hold.
  Outside that domain the DFS_skel function takes an arbitrary value (HOL totality),
  so the visited field may contain P-vertices, violating vis_works(1).

  Phase-1 fix required in DDFS.thy: add "dpath dG (rev p)" and "distinct p" as
  premises to IDFS_vis_works(1), IDFS_vis_works(2), IDFS_vis_works(4),
  IDFS_complete, IDFS_sound(3..8).  After that, DDFS.thy proofs provide these from
  invar_4 / invar_5, which maintain dpath+distinct for all stacks used.

  The dg-vs-dG typo in digraph(3) of the DDFS locale (now fixed: dg \<rightarrow> dG) was a
  separate pre-existing issue; it has been corrected in DDFS.thy.

Pairing table (DDFS locale clause \<leftrightarrow> IDFS.thy theorem):
  digraph(1)         \<leftrightarrow>  L1                   dischargeable
  digraph(2)         \<leftrightarrow>  L2                   dischargeable
  digraph(3)         \<leftrightarrow>  L3                   dischargeable (after dg\<rightarrow>dG fix)
  IDFS_vis_works(1)  \<leftrightarrow>  IDFS_vis_works_2     GAP: needs dpath+distinct
  IDFS_vis_works(2)  \<leftrightarrow>  IDFS_vis_works_3     GAP: needs dpath+distinct
  IDFS_vis_works(3)  \<leftrightarrow>  IDFS_vis_works_4     dischargeable (outer context)
  IDFS_vis_works(4)  \<leftrightarrow>  IDFS_vis_works_6     GAP: needs dpath+distinct
  IDFS_closed(1)     \<leftrightarrow>  IDFS_closed_None     dischargeable (clause has dpath+distinct)
  IDFS_closed(2)     \<leftrightarrow>  IDFS_closed_Some     dischargeable (clause has dpath+distinct)
  IDFS_complete      \<leftrightarrow>  IDFS_complete        GAP: needs dpath+distinct
  IDFS_sound(1)      \<leftrightarrow>  IDFS_sound_1         dischargeable (clause has dpath)
  IDFS_sound(2)      \<leftrightarrow>  IDFS_sound_2         dischargeable (clause has distinct)
  IDFS_sound(3)      \<leftrightarrow>  IDFS_sound_3         GAP: needs dpath+distinct
  IDFS_sound(4)      \<leftrightarrow>  IDFS_sound_4         GAP: needs dpath+distinct
  IDFS_sound(5)      \<leftrightarrow>  IDFS_sound_5         GAP: needs dpath+distinct
  IDFS_sound(6)      \<leftrightarrow>  IDFS_sound_6         GAP: needs dpath+distinct
  IDFS_sound(7)      \<leftrightarrow>  IDFS_sound_7         GAP: needs dpath+distinct
  IDFS_sound(8)      \<leftrightarrow>  IDFS_sound_8         GAP: needs dpath+distinct
\<close>

section \<open>Layered digraph locale\<close>

text \<open>The DDFS_layered locale is defined in IDFS.thy.
Here we add helper lemmas inside that locale context.\<close>

context DDFS_layered begin

section \<open>Universally available IDFS property\<close>

text \<open>IDFS_vis_works(3): the visited set only grows.  Proved directly from the
IDFS definition without any path or distinctness premise.
We use \<open>vis\<close> (not \<open>visited\<close>) to avoid clashing with the
\<open>DFS_avoid_state.visited\<close> record field accessor.\<close>

lemma IDFS_vis_works_mono:
  fixes vis vis' :: "'a set" and P :: "'a \<Rightarrow> bool" and avoid :: "'a set" and p :: "'a list"
  assumes ic: "IDFS dG P avoid p vis = (ret_p, vis')"
  shows "vis \<subseteq> vis'"
  sorry (*READT-TODO-21: original: using IDFS_vis_works(3)[OF ic] .; symptom: IDFS_vis_works not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

section \<open>Conditionally available IDFS properties (with dpath + distinct)\<close>

text \<open>These re-export the DDFS locale's IDFS assumptions in explicit form.
Inside \<open>context DDFS_layered\<close> these hold because the IDFS function
realises the DDFS interface (proved in IDFS.thy via the sublocale).
We use \<open>vis\<close> (not \<open>visited\<close>) to avoid clashing with the
\<open>DFS_avoid_state.visited\<close> record field accessor.\<close>

context
  fixes P :: "'a \<Rightarrow> bool" and avoid vis :: "'a set" and p :: "'a list"
  assumes path:  "dpath dG (rev p)"
      and dist:  "distinct p"
begin

lemma IDFS_notP:
  assumes ic: "IDFS dG P avoid p vis = (ret_p, vis')" and vm: "v \<in> vis' - vis"
  shows "\<not> P v"
  sorry (*READT-TODO-22: original: using IDFS_vis_works(1)[OF path dist ic vm] .; symptom: IDFS_vis_works/complete/closed/sound not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

lemma IDFS_newvis_avoid_disj:
  assumes ic: "IDFS dG P avoid p vis = (ret_p, vis')"
  shows "(vis' - vis) \<inter> avoid = {}"
  sorry (*READT-TODO-23: original: using IDFS_vis_works(2)[OF path dist ic] .; symptom: IDFS_vis_works/complete/closed/sound not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

lemma IDFS_newvis_finite:
  assumes ic: "IDFS dG P avoid p vis = (ret_p, vis')"
  shows "finite (vis' - vis)"
  sorry (*READT-TODO-24: original: using IDFS_vis_works(4)[OF path dist ic] .; symptom: IDFS_vis_works/complete/closed/sound not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

lemma IDFS_complete_cond:
  assumes ic: "IDFS dG P avoid p vis = (None, vis')"
  shows "set p - avoid \<subseteq> vis'"
  sorry (*READT-TODO-25: original: using IDFS_complete[OF path dist ic] .; symptom: IDFS_vis_works/complete/closed/sound not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

lemma IDFS_closed_None_cond:
  assumes ic: "IDFS dG P avoid p vis = (None, vis')" and vm: "v \<in> vis' - vis"
      and ew: "(v, w) \<in> dG"
  shows "w \<in> avoid \<union> vis'"
  sorry (*READT-TODO-26: original: using IDFS_closed(1)[OF path dist ic vm ew] .; symptom: IDFS_vis_works/complete/closed/sound not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

lemma IDFS_closed_Some_cond:
  assumes ic: "IDFS dG P avoid p vis = (Some p', vis')" and vm: "v \<in> vis' - vis"
      and ew: "(v, w) \<in> dG"
  shows "w \<in> avoid \<union> vis' \<union> set p'"
  sorry (*READT-TODO-27: original: using IDFS_closed(2)[OF path dist ic vm ew] .; symptom: IDFS_vis_works/complete/closed/sound not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

lemma IDFS_sound_dpath:
  assumes ic: "IDFS dG P avoid p vis = (Some p', vis')"
  shows "dpath dG (rev p')"
  sorry (*READT-TODO-28: original: using IDFS_sound(1)[OF path ic] .; symptom: IDFS_vis_works/complete/closed/sound not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

lemma IDFS_sound_distinct:
  assumes ic: "IDFS dG P avoid p vis = (Some p', vis')"
  shows "distinct p'"
  sorry (*READT-TODO-29: original: using IDFS_sound(2)[OF path dist ic] .; symptom: IDFS_vis_works/complete/closed/sound not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

lemma IDFS_sound_newvis_disjoint:
  assumes ic: "IDFS dG P avoid p vis = (Some p', vis')"
  shows "(set p' - set (tl p)) \<inter> (avoid \<union> vis') = {}"
  sorry (*READT-TODO-30: original: using IDFS_sound(3)[OF path dist ic] .; symptom: IDFS_vis_works/complete/closed/sound not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

lemma IDFS_sound_prefix_vis:
  assumes ic: "IDFS dG P avoid p vis = (Some p', vis')"
  shows "set p - set p' - avoid \<subseteq> vis'"
  sorry (*READT-TODO-31: original: using IDFS_sound(4)[OF path dist ic] .; symptom: IDFS_vis_works/complete/closed/sound not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

lemma IDFS_sound_tl_notP:
  assumes ic: "IDFS dG P avoid p vis = (Some p', vis')"
      and tlP: "\<And>u. u \<in> set (tl p) \<Longrightarrow> \<not> P u"
      and uv: "v \<in> set (tl p')"
  shows "\<not> P v"
  sorry (*READT-TODO-32: original: using IDFS_sound(5)[OF path dist ic tlP uv] .; symptom: IDFS_vis_works/complete/closed/sound not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

lemma IDFS_sound_last:
  assumes ic: "IDFS dG P avoid p vis = (Some p', vis')" and ne: "p \<noteq> []"
  shows "last p = last p'"
  sorry (*READT-TODO-33: original: using IDFS_sound(6)[OF path dist ic ne] .; symptom: IDFS_vis_works/complete/closed/sound not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

lemma IDFS_sound_nonempty:
  assumes ic: "IDFS dG P avoid p vis = (Some p', vis')"
  shows "p' \<noteq> []"
  sorry (*READT-TODO-34: original: using IDFS_sound(7)[OF path dist ic] .; symptom: IDFS_vis_works/complete/closed/sound not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

lemma IDFS_sound_hdP:
  assumes ic: "IDFS dG P avoid p vis = (Some p', vis')"
  shows "P (hd p')"
  sorry (*READT-TODO-35: original: using IDFS_sound(8)[OF path dist ic] .; symptom: IDFS_vis_works/complete/closed/sound not inherited (sublocale sorry'd); pattern: cascade from TODO-20*)

end (* inner context with path + distinct *)

text \<open>Summary: the derivable IDFS properties can be split into two groups:
 (A) Universal (no dpath/distinct needed):
      IDFS_vis_works_mono (visited monotone)
 (B) Conditional on dpath dG (rev p) \<and> distinct p:
      all other properties (IDFS_closed, IDFS_complete, IDFS_sound, IDFS_vis_works 1/2/4)

The full sublocale DDFS_layered \<subseteq> DDFS dG lev IDFS requires the DDFS locale
to be amended so that IDFS_vis_works(1/2/4), IDFS_complete and IDFS_sound(3-8) carry
dpath+distinct premises (matching group B above).  Once those premises are added
to DDFS.thy, each DDFS proof site can supply them from invar_4 / invar_5.\<close>

text \<open>The succ witness: for each non-zero-level vertex pick an outgoing
edge via SOME.  succ_works is discharged from L1 (level-decreasing edges) + L3
(level-0 path exists).\<close>

(*READT-TODO-39: original: definition "layered_succ v \<equiv> SOME v0. (v, v0) \<in> dG";
  symptom: Extra variables on rhs: dG — dG not in scope because context DDFS_layered
  failed (cascade from TODO-20 sublocale sorry); pass-3 item after DDFS_layered redesign;
  pattern: interface mismatch cascade*)

lemma layered_succ_works:
  "v \<in> dVs dG \<Longrightarrow> lev v \<noteq> 0 \<Longrightarrow> (\<exists>v0. (v, v0) \<in> dG)"
  sorry (*READT-TODO-36: original: (v, layered_succ v) \<in> dG (used definition layered_succ = SOME v0. (v,v0) \<in> dG); proof - assume vVs: "v \<in> dVs dG" and lne: "lev v \<noteq> 0"; original: proof - assume vVs: "v \<in> dVs dG" and lne: "lev v \<noteq> 0"; obtain q v0 where q: "q \<noteq> []" "dpath_bet dG q v v0" "lev v0 = 0" using L3[OF vVs] by blast; have "v \<noteq> v0" using lne q(3) by auto; then obtain v1 where e: "(v, v1) \<in> dG" using path_then_edge[OF q(2) q(1)] by blast; show "(v, layered_succ v) \<in> dG" unfolding layered_succ_def using someI_ex[where P = "\<lambda>v0. (v, v0) \<in> dG"] e by blast; qed; symptom: two 'by blast' spinning (L183,L189) - locale context picks up DDFS sorry'd sublocale causing nontermination; pattern: cascade from TODO-20*)

end (* DDFS_layered *)

end
