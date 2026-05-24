theory Array_List
imports 
  Array_Blit
begin

  type_synonym 'a array_list = "'a Heap.array \<times> nat"

  definition "is_array_list l \<equiv> \<lambda>(a,n). \<exists>\<^sub>Al'. a \<mapsto>\<^sub>a l' * \<up>(n \<le> length l' \<and> l = take n l' \<and> length l'>0)"

  (*lemma is_array_list_prec: "precise is_array_list"
    unfolding is_array_list_def[abs_def]
    apply(rule preciseI)
    apply(simp split: prod.splits simp: models_simps split_mod) 
  	using preciseD snga_prec
  	 apply (auto simp: models_simps split_mod) find_theorems "_*_"
  	
  	 by (fastforce simp: models_simps split_mod)
  *)  	 

  definition "initial_capacity \<equiv> 16::nat"
  definition "minimum_capacity \<equiv> 16::nat"

  definition "arl_empty \<equiv> do {
    a \<leftarrow> Array.new initial_capacity default;
    return (a,0)
  }"

  definition "arl_empty_sz init_cap \<equiv> do {
    a \<leftarrow> Array.new (max init_cap minimum_capacity) default;
    return (a,0)
  }"

  definition "arl_append \<equiv> \<lambda>(a,n) x. do {
    len \<leftarrow> Array.len a;

    if n<len then do {
      a \<leftarrow> Array.upd n x a;
      return (a,n+1)
    } else do {
      let newcap = 2 * len;
      a \<leftarrow> array_grow a newcap default;
      a \<leftarrow> Array.upd n x a;
      return (a,n+1)
    }
  }"

  definition "arl_copy \<equiv> \<lambda>(a,n). do {
    a \<leftarrow> array_copy a;
    return (a,n)
  }"

  definition arl_length :: "'a::heap array_list \<Rightarrow> nat Heap" where
    "arl_length \<equiv> \<lambda>(a,n). return (n)"

  definition arl_is_empty :: "'a::heap array_list \<Rightarrow> bool Heap" where
    "arl_is_empty \<equiv> \<lambda>(a,n). return (n=0)"

  definition arl_last :: "'a::heap array_list \<Rightarrow> 'a Heap" where
    "arl_last \<equiv> \<lambda>(a,n). do {
      dynamic_check STR ''Empty (arl_last)'' (0<n);
      Array.nth a (n - 1)
    }"

  definition arl_butlast :: "'a::heap array_list \<Rightarrow> 'a array_list Heap" where
    "arl_butlast \<equiv> \<lambda>(a,n). do {
      if n=0 then return (a,n)
      else do {
        let n = n - 1;
        len \<leftarrow> Array.len a;
        if (n*4 < len \<and> n*2\<ge>minimum_capacity) then do {
          a \<leftarrow> array_shrink a (n*2);
          return (a,n)
        } else
          return (a,n)
      }
    }"

  definition arl_get :: "'a::heap array_list \<Rightarrow> nat \<Rightarrow> 'a Heap" where
    "arl_get \<equiv> \<lambda>(a,n) i. do {
      dynamic_check STR ''ArrayIndexOutOfBounds (arl_get)'' (i<n);
      Array.nth a i
    }"

  definition arl_set :: "'a::heap array_list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array_list Heap" where
    "arl_set \<equiv> \<lambda>(a,n) i x. do { 
      dynamic_check STR ''ArrayIndexOutOfBounds (arl_set)'' (i<n);
      a \<leftarrow> Array.upd i x a; 
      return (a,n)
    }"


  lemma arl_empty_rule[sep_heap_rules]: "< emp > arl_empty <is_array_list []>"
    supply [simp] = arl_empty_def is_array_list_def initial_capacity_def
    by (sep_auto)

  lemma arl_empty_sz_rule[sep_heap_rules]: "< emp > arl_empty_sz N <is_array_list []>"
    supply [simp] = arl_empty_sz_def is_array_list_def minimum_capacity_def
    by (sep_auto)

  lemma arl_copy_rule[sep_heap_rules]: "< is_array_list l a > arl_copy a <\<lambda>r. is_array_list l a * is_array_list l r>"  
    supply [simp] = arl_copy_def is_array_list_def
    by (sep_auto)

  lemma arl_append_rule[sep_heap_rules]: "
    < is_array_list l a > 
      arl_append a x 
    <\<lambda>a. is_array_list (l@[x]) a >"  
    supply [simp] = arl_append_def is_array_list_def take_update_last neq_Nil_conv
    supply [split] = prod.splits nat.split
    by sep_auto
    
  lemma arl_length_rule[sep_heap_rules]: "
    <is_array_list l a> 
      arl_length a
    <\<lambda>r. is_array_list l a * \<up>(r=length l)>"
    by (sep_auto simp: arl_length_def is_array_list_def)
    
  lemma arl_is_empty_rule[sep_heap_rules]: "
    <is_array_list l a> 
      arl_is_empty a
    <\<lambda>r. is_array_list l a * \<up>(r\<longleftrightarrow>(l=[]))>"
    by (sep_auto simp: arl_is_empty_def is_array_list_def)

  lemma arl_last_rule[sep_heap_rules]: "
    <is_array_list l a> 
      arl_last a
    <\<lambda>r. is_array_list l a * \<up>(r=last l \<and> l\<noteq>[])>"
    by (sep_auto simp: arl_last_def is_array_list_def last_take_nth_conv)
    
  lemma arl_butlast_rule[sep_heap_rules]: "
    <is_array_list l a> 
      arl_butlast a
    <is_array_list (butlast l)>"
  proof -
    (*assume [simp]: "l\<noteq>[]"*)
  
    have [simp]: "\<And>x. min (x-Suc 0) ((x-Suc 0)*2) = x-Suc 0" by auto

    show ?thesis
      by (sep_auto 
        split: prod.splits
        simp: arl_butlast_def is_array_list_def butlast_take minimum_capacity_def)
  qed  

  lemma arl_get_rule[sep_heap_rules]: "
    <is_array_list l a> 
      arl_get a i
    <\<lambda>r. is_array_list l a * \<up>(r=l!i)>"
    by (sep_auto simp: arl_get_def is_array_list_def split: prod.split)
    

  lemma arl_set_rule[sep_heap_rules]: "
    <is_array_list l a> 
      arl_set a i x
    <is_array_list (l[i:=x])>"
    by (sep_auto simp: arl_set_def is_array_list_def split: prod.split)

end
