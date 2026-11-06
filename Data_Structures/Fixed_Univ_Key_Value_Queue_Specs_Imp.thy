theory Fixed_Univ_Key_Value_Queue_Specs_Imp
  imports Separation_Logic_Imperative_HOL_Partial.Sep_Main 
          Fixed_Univ_Key_Value_Queue_Specs
begin
section \<open>Imperative Key-Value Queues\<close>

text \<open>The functional key-value queue of @{locale key_value_queue} is extended by a representation
      assertion @{term queue_assn}, a key abstraction @{term queue_key} from the executable keys to
      the functional ones, and one imperative operation per functional operation. Operations that
      change the queue are in place and of type @{typ \<open>unit Heap\<close>}.

      In addition to the operations of the functional queue, there are

        \<^item> @{term queue_clear_imp}, which empties the queue in place, whatever its contents, without
          allocation, and
        \<^item> @{term queue_key_of_imp}, which returns the key of an element, if it is in the queue.

      @{term queue_extract_min_imp} also returns the key of the extracted element. Users that need
      the key of an element thus need not recompute it. The only allocating operation is
      @{term queue_empty_imp}, which is used during initialisation only.\<close>

locale key_value_queue_imp =
  key_value_queue U queue_empty queue_extract_min queue_decrease_key queue_insert
      queue_invar queue_abstract
  for U :: "'v set"
    and queue_empty :: "'queue"
    and queue_extract_min :: "'queue \<Rightarrow> ('queue \<times> 'v option)"
    and queue_decrease_key :: "'queue \<Rightarrow> 'v \<Rightarrow> ('a::linorder) \<Rightarrow> 'queue"
    and queue_insert :: "'queue \<Rightarrow> 'v \<Rightarrow> 'a \<Rightarrow> 'queue"
    and queue_invar :: "'queue \<Rightarrow> bool"
    and queue_abstract :: "'queue \<Rightarrow> ('v \<times> 'a) set" +
  fixes queue_key :: "'ai \<Rightarrow> 'a"
    and queue_assn :: "'queue \<Rightarrow> 'queuei \<Rightarrow> assn"
    and queue_empty_imp :: "'queuei Heap"
    and queue_clear_imp :: "'queuei \<Rightarrow> unit Heap"
    and queue_extract_min_imp :: "'queuei \<Rightarrow> ('v \<times> 'ai) option Heap"
    and queue_key_of_imp :: "'queuei \<Rightarrow> 'v \<Rightarrow> 'ai option Heap"
    and queue_decrease_key_imp :: "'queuei \<Rightarrow> 'v \<Rightarrow> 'ai \<Rightarrow> unit Heap"
    and queue_insert_imp :: "'queuei \<Rightarrow> 'v \<Rightarrow> 'ai \<Rightarrow> unit Heap"
  assumes queue_empty_rule[sep_heap_rules]:
      "<emp> queue_empty_imp <\<lambda>Hi. queue_assn queue_empty Hi>"
    and queue_clear_rule[sep_heap_rules]:
      "<queue_assn H Hi> queue_clear_imp Hi <\<lambda>_. queue_assn queue_empty Hi>"
    and queue_extract_min_rule[sep_heap_rules]:
      "queue_invar H \<Longrightarrow>
       <queue_assn H Hi> queue_extract_min_imp Hi
       <\<lambda>r. queue_assn (fst (queue_extract_min H)) Hi *
             \<up>(map_option fst r = snd (queue_extract_min H) \<and>
               (\<forall>x k. r = Some (x, k) \<longrightarrow> (x, queue_key k) \<in> queue_abstract H))>"
    and queue_key_of_rule[sep_heap_rules]:
      "\<lbrakk>queue_invar H; x \<in> U\<rbrakk> \<Longrightarrow>
       <queue_assn H Hi> queue_key_of_imp Hi x
       <\<lambda>r. queue_assn H Hi *
             \<up>(case r of None \<Rightarrow> (\<nexists>k. (x, k) \<in> queue_abstract H)
                       | Some k \<Rightarrow> (x, queue_key k) \<in> queue_abstract H)>"
    and queue_insert_rule[sep_heap_rules]:
      "\<lbrakk>queue_invar H; x \<in> U; \<nexists>k. (x, k) \<in> queue_abstract H\<rbrakk> \<Longrightarrow>
       <queue_assn H Hi> queue_insert_imp Hi x k
       <\<lambda>_. queue_assn (queue_insert H x (queue_key k)) Hi>"
    and queue_decrease_key_rule[sep_heap_rules]:
      "\<lbrakk>queue_invar H; x \<in> U; (x, k') \<in> queue_abstract H; queue_key k < k'\<rbrakk> \<Longrightarrow>
       <queue_assn H Hi> queue_decrease_key_imp Hi x k
       <\<lambda>_. queue_assn (queue_decrease_key H x (queue_key k)) Hi>"

end