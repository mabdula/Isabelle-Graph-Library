section \<open>Separation Logic Framework Entrypoint\<close>
theory Sep_Main
imports Automation "HOL-Library.Complete_Partial_Order2"
begin
  text \<open>Import this theory to make available Imperative/HOL with 
    separation logic.\<close>
    
  subsection \<open>Dynamically Checked Assertion\<close>
  text \<open>Due to partial correctness, we can check assertions dynamically, 
    and assume that they hold during the proof. If they don't when the program runs, it will
    gracefully terminate with an exception\<close>  
    
  fun dynamic_check where
    "dynamic_check msg True = return ()"
  | "dynamic_check msg False = raise msg"  
  
  lemma dynamic_check_rule[sep_heap_rules]: "<emp> dynamic_check msg P <\<lambda>_. \<up>P>"
    apply (cases P)
    by sep_auto
    
    
  (* Some ccpo auxiliary lemmas *)  
    
  lemma flat_ord_chain_cases: 
    assumes A: "Complete_Partial_Order.chain (flat_ord b) C"
    obtains "C={}" 
    | "C={b}" 
    | x where "x\<noteq>b" and "C={x}" 
    | x where "x\<noteq>b" and "C={b,x}"
  proof -
    have "\<exists>m1 m2. C \<subseteq> {m1,m2} \<and> (m1 = b \<or> m2 = b)"
      apply (rule ccontr)
    proof clarsimp
      assume "\<forall>m1 m2. C \<subseteq> {m1, m2} \<longrightarrow> m1\<noteq>b \<and> m2\<noteq>b"
      then obtain m1 m2 where "m1\<in>C" "m2\<in>C" 
        "m1\<noteq>m2" "m1\<noteq>b" "m2\<noteq>b"
        by blast
      with A show False
        unfolding Complete_Partial_Order.chain_def flat_ord_def
        by auto
    qed
    then obtain m where "C \<subseteq> {m,b}" by blast
    thus ?thesis 
      apply (cases "m=b") 
      using that
      apply blast+
      done
  qed

  lemma chain_img_ord_conv: "Complete_Partial_Order.chain (img_ord f ord) C 
    \<longleftrightarrow> Complete_Partial_Order.chain ord (f`C)"  
    by (simp add: chain_def img_ord_def)
    
    
  lemma heap_lub_SomeE:
    assumes "Complete_Partial_Order.chain heap.le_fun A" 
    assumes "heap.lub_fun A x = Heap.Heap f"
    assumes "f h = Some rh'"
    obtains F' f' where "F'\<in>A" "F' x = Heap.Heap f'" "f' h = Some rh'"
  proof -
  
    have [simp]: "{y. \<exists>f. (\<exists>fa\<in>A. f = fa x) \<and> y = execute f h} = (\<lambda>f. execute (f x) h) ` A" for x h by blast

    show ?thesis  
      using assms
      apply -
      apply (drule chain_fun[where a=x])
      apply (simp add: chain_img_ord_conv Heap_ord_def)
      apply (drule chain_fun[where a=h]; simp add: )
      apply (clarsimp simp: fun_lub_def Heap_lub_def img_lub_def)
      by (metis (mono_tags, lifting) Heap_execute flat_lub_in_chain image_iff option.distinct(1) that)
  qed    
    
  lemma run_heap_lub_SomeE:
    assumes "run (heap.lub_fun A x) (Some h) \<sigma> r"
    assumes "Complete_Partial_Order.chain heap.le_fun A"  
    assumes "\<not> is_exn \<sigma>"
    obtains f where "f\<in>A" "run (f x) (Some h) \<sigma> r"
    using assms apply -
    apply (erule run.cases; simp)
    subgoal for \<sigma>' c r' h'
      apply (cases c; simp)
      by (auto elim: heap_lub_SomeE simp: regular)
    done    
          
  lemma hoare_triple_admissible[simp]: "heap.admissible (\<lambda>D. <P> D x <Q>)"
    by (smt (verit, best) ccpo.admissibleI hoare_triple_def run_heap_lub_SomeE)
    

      
    
    
  partial_function (heap) while where
    "while b c s = do {
      ctd \<leftarrow> b s;
      if ctd then do {
        s \<leftarrow> c s;
        while b c s
      } else
        return s
    
    }"      

  lemmas while_unfold = while.simps

  definition whileI :: "('a \<Rightarrow> assn) \<Rightarrow> ('a \<Rightarrow> bool Heap) \<Rightarrow> ('a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where "whileI I \<equiv> while"
  
  lemmas annot_whileI = whileI_def[symmetric]
    
  (* Needs invariant to be instantiated manually *)
  lemma while_rule:
    assumes step1: "\<And>s. <I s> b s <C s>"
    assumes step2: "\<And>s. <C s True> c s <I>"
    shows "<I s> while b c s <\<lambda>s'. C s' False>"
    apply (induction arbitrary: s rule: while.fixp_induct)
    subgoal by simp
    subgoal by simp
    subgoal
      supply [sep_heap_rules] = step1 step2
      by sep_auto
    done
    
  (* Annotated invariant *)
  lemma whileI_rule[sep_heap_rules]:
    assumes step1: "\<And>s. <I s> b s <C s>"
    assumes step2: "\<And>s. <C s True> c s <I>"
    shows "<I s\<^sub>0> whileI I b c s\<^sub>0 <\<lambda>s. C s False>"
    unfolding whileI_def using while_rule[OF assms] .
    

    
    
    
    
  fun foldM where
    "foldM f [] s = return s"
  | "foldM f (x#xs) s = do {
      s \<leftarrow> f x s;
      foldM f xs s
    }"  

  (* Needs manual instantiation of coupling invariant I.
  
    Intuition: I already_iterated remaining s si
  *)  
  lemma foldM_refine:
    assumes "\<And>xs\<^sub>1 x xs\<^sub>2 s si. <I xs\<^sub>1 (x#xs\<^sub>2) s si * \<up>(xs = xs\<^sub>1@x#xs\<^sub>2)> fi x si <\<lambda>si. I (xs\<^sub>1@[x]) xs\<^sub>2 (f x s) si>"
    shows "<I [] xs s si> foldM fi xs si <\<lambda>si. I xs [] (fold f xs s) si>"
  proof -  
    have "<I xs\<^sub>1 xs\<^sub>2 s si * \<up>(xs=xs\<^sub>1@xs\<^sub>2)> foldM fi xs\<^sub>2 si <\<lambda>si. I (xs\<^sub>1@xs\<^sub>2) [] (fold f xs\<^sub>2 s) si>" for xs\<^sub>1 xs\<^sub>2
      apply (induction xs\<^sub>2 arbitrary: xs\<^sub>1 s si)
      by (sep_auto heap: assms)
    thus ?thesis by sep_auto
  qed

    
    
            
end
