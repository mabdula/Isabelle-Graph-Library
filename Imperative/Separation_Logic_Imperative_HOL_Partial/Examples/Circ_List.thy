section \<open>Circular Singly Linked Lists\<close>
theory Circ_List
imports List_Seg Imp_List_Spec
begin

text \<open>
  Example of circular lists, with efficient append, prepend, pop, and rotate
  operations.
\<close>

subsection \<open>Datatype Definition\<close>

type_synonym 'a cs_list = "'a node ref option"

text \<open>A circular list is described by a list segment, with special
  cases for the empty list:\<close>
fun cs_list :: "'a::heap list \<Rightarrow> 'a node ref option \<Rightarrow> assn" where
  "cs_list [] None = emp"
| "cs_list (x#l) (Some p) = lseg (x#l) (Some p) (Some p)"
| "cs_list _ _ = false"

lemma cs_list_add_simps1[simp]: "cs_list l None = \<up>(l=[])"
  by (cases l) auto

lemma cs_list_add_simps2[simp]: 
  "cs_list l (Some p) 
  = (\<exists>\<^sub>Ax ls. \<up>(l=x#ls) * lseg (x#ls) (Some p) (Some p))"
  apply (rule ent_iffI)
  apply (cases l) 
  apply simp
  apply sep_auto
  apply (cases l) 
  apply simp
  apply sep_auto
  done

subsection \<open>Precision\<close>
(*lemma cs_prec: 
  "precise cs_list"
  apply rule
  apply (case_tac p)
  apply clarsimp

  apply clarsimp
  apply (subgoal_tac "x=xa \<and> n=na", simp)

  apply (erule prec_frame_expl[OF lseg_prec1])
  apply frame_inference
  apply frame_inference

  apply (drule prec_frame[OF sngr_prec])
  apply frame_inference
  apply frame_inference
  apply simp
  done
  *)

(*lemma cs_imp_list_impl: "imp_list cs_list"
  apply unfold_locales
  apply (rule cs_prec)
  done
*)  
interpretation cs: imp_list cs_list .

subsection \<open>Operations\<close>
subsubsection \<open>Allocate Empty List\<close>
definition cs_empty :: "'a::heap cs_list Heap" where
  "cs_empty \<equiv> return None"

lemma cs_empty_rule: "<emp> cs_empty <cs_list []>"
  unfolding cs_empty_def
  by sep_auto

lemma cs_empty_impl: "imp_list_empty cs_list cs_empty" 
  by unfold_locales (sep_auto heap: cs_empty_rule)
interpretation cs: imp_list_empty cs_list cs_empty by (rule cs_empty_impl)

subsubsection \<open>Prepend Element\<close>
fun cs_prepend :: "'a \<Rightarrow> 'a::heap cs_list \<Rightarrow> 'a cs_list Heap" where
  "cs_prepend x None = do {
    p \<leftarrow> ref (Node x None); 
    p:=Node x (Some p); 
    return (Some p)
  }"
| "cs_prepend x (Some p) = do {
    n \<leftarrow> !p;
    q \<leftarrow> ref (Node (val n) (next n));
    p := Node x (Some q);
    return (Some p)
  }"

declare cs_prepend.simps [simp del]

(* TODO: Move *)
lemma hoare_triple_exEI[intro!]:
  assumes "\<And>x. <P x> c <Q>"
  shows "<\<exists>\<^sub>Ax. P x> c <Q>"
  by (meson assms hoare_triple_wlp mod_exE)


lemma cs_prepend_rule: 
  "<cs_list l p> cs_prepend x p <cs_list (x#l)>"
  apply (cases p)
  subgoal
    apply (simp_all add: cs_prepend.simps)
    apply (sep_vcg auto)
    apply clarsimp
    apply (rule mod_exI[where x=x])
    apply (rule mod_exI[where x="[]"])
    by sep_auto
    
  apply (clarsimp simp: cs_prepend.simps)
  subgoal for a xx ls pp n
    apply (sep_vcg auto)
    apply clarsimp
    apply (rule mod_exI[where x=x])
    apply (rule mod_exI[where x="xx#ls"])
    by sep_auto
  done  

lemma cs_prepend_impl: "imp_list_prepend cs_list cs_prepend"
  by unfold_locales (sep_auto heap: cs_prepend_rule)
interpretation cs: imp_list_prepend cs_list cs_prepend 
  by (rule cs_prepend_impl)

subsubsection \<open>Append Element\<close>
fun cs_append :: "'a \<Rightarrow> 'a::heap cs_list \<Rightarrow> 'a cs_list Heap" where
  "cs_append x None = do { 
    p \<leftarrow> ref (Node x None); 
    p:=Node x (Some p); 
    return (Some p) }"
| "cs_append x (Some p) = do {
    n \<leftarrow> !p;
    q \<leftarrow> ref (Node (val n) (next n));
    p := Node x (Some q);
    return (Some q)
  }"

declare cs_append.simps [simp del]

lemma cs_append_rule: 
  "<cs_list l p> cs_append x p <cs_list (l@[x])>"
  apply (cases p)
  subgoal
    supply [simp] = cs_append.simps
    apply (sep_auto' simp)
    apply (rule mod_exI[where x=x])
    apply (rule mod_exI[where x="[]"])
    by sep_auto
  subgoal for a
    supply [simp] = cs_append.simps
    apply (sep_auto' clarsimp)
    subgoal for xa ls n ra aa b
      apply (sep_frame_fwd rule: lseg_append)
      apply (rule mod_exI[where x=xa])
      apply (rule mod_exI[where x="ls@[x]"])
      by sep_auto
    done
  done

lemma cs_append_impl: "imp_list_append cs_list cs_append"
  by unfold_locales (sep_auto heap: cs_append_rule)
interpretation cs: imp_list_append cs_list cs_append
  by (rule cs_append_impl)

subsubsection \<open>Pop First Element\<close>
fun cs_pop :: "'a::heap cs_list \<Rightarrow> ('a\<times>'a cs_list) Heap" where
  "cs_pop None = raise STR ''Pop from empty list''"
| "cs_pop (Some p) = do {
    n1 \<leftarrow> !p;
    if next n1 = Some p then
      return (val n1,None) \<comment> \<open>Singleton list becomes empty list\<close>
    else do {
      let p2 = the (next n1);
      n2 \<leftarrow> !p2;
      p := Node (val n2) (next n2);
      return (val n1,Some p)
    }
  }"

declare cs_pop.simps[simp del]

lemma cs_pop_rule: 
  "<cs_list (x#l) p> cs_pop p <\<lambda>(y,p'). cs_list l p' * true * \<up>(y=x)>"
  apply (cases p; cases l)
  apply (sep_auto simp: cs_pop.simps)
  done

lemma cs_pop_impl: "imp_list_pop cs_list cs_pop"
  apply unfold_locales 
  apply (sep_auto heap: cs_pop_rule elim': neq_NilE)
  done
interpretation cs: imp_list_pop cs_list cs_pop by (rule cs_pop_impl)

subsubsection \<open>Rotate\<close>
fun cs_rotate :: "'a::heap cs_list \<Rightarrow> 'a cs_list Heap" where
  "cs_rotate None = return None"
| "cs_rotate (Some p) = do {
    n \<leftarrow> !p;
    return (next n)
  }"

declare cs_rotate.simps [simp del]

lemma cs_list_append_sng: "cs_list (xs@[x]) n = (\<exists>\<^sub>Ap. \<up>(n=Some p) * lseg (xs@[x]) (Some p) (Some p))"
  supply [simp del] = lseg.simps lseg_if_splitf2
  by (cases n; cases xs; sep_auto intro': ent_iffI)
  

lemma cs_rotate_rule: 
  "<cs_list l p> cs_rotate p <cs_list (rotate1 l)>"
  apply (cases p; clarsimp simp add: cs_rotate.simps)
  subgoal by (sep_auto)
  subgoal for a x ls pp n
    apply sep_auto
    apply (sep_frame_fwd rule: lseg_append)
    apply (simp add: cs_list_append_sng)
    apply (cases n; sep_auto)
    done
  done

lemma cs_rotate_impl: "imp_list_rotate cs_list cs_rotate"
  apply unfold_locales 
  apply (sep_auto heap: cs_rotate_rule)
  done
interpretation cs: imp_list_rotate cs_list cs_rotate by (rule cs_rotate_impl)

subsection \<open>Test\<close>
definition "test \<equiv> do {
  l \<leftarrow> cs_empty;
  l \<leftarrow> cs_append ''a'' l;
  l \<leftarrow> cs_append ''b'' l;
  l \<leftarrow> cs_append ''c'' l;
  l \<leftarrow> cs_prepend ''0'' l;
  l \<leftarrow> cs_rotate l;
  (v1,l)\<leftarrow>cs_pop l;
  (v2,l)\<leftarrow>cs_pop l;
  (v3,l)\<leftarrow>cs_pop l;
  (v4,l)\<leftarrow>cs_pop l;
  return [v1,v2,v3,v4]
}"

definition "test_result \<equiv> [''a'', ''b'', ''c'', ''0'']"

lemma "<emp> test <\<lambda>r. \<up>(r=test_result) * true>"
  unfolding test_def test_result_def
  apply (sep_auto)
  done
  
export_code test checking SML_imp

ML_val \<open>
  val res = @{code test} ();
  if res = @{code test_result} then () else raise Match;
\<close>

hide_const (open) test test_result

end
