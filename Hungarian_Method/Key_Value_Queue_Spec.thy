theory Key_Value_Queue_Spec
  imports Main
begin

section \<open>Specification of Queue as used by Hungarian Method\<close>

locale key_value_queue =
  fixes queue_empty::'queue
   and queue_extract_min::"'queue \<Rightarrow> ('queue \<times> 'v option)"
   and queue_decrease_key::"'queue \<Rightarrow> 'v \<Rightarrow> ('a::linorder) \<Rightarrow> 'queue"
   and queue_insert::"'queue \<Rightarrow> 'v \<Rightarrow> ('a::linorder) \<Rightarrow> 'queue"
   and queue_invar::"'queue \<Rightarrow> bool"
   and queue_abstract::"'queue \<Rightarrow> ('v \<times> ('a::linorder)) set"
 assumes queue_empty: "queue_invar queue_empty"
                     "queue_abstract queue_empty = {}"
 and queue_extract_min: 
 "\<And> H. queue_invar H \<Longrightarrow> queue_invar (fst (queue_extract_min H))"
 "\<And> H x.  \<lbrakk>queue_invar H; Some x = snd (queue_extract_min H)\<rbrakk> \<Longrightarrow>
           \<exists> k. ((x, k) \<in> queue_abstract H \<and> 
                (\<forall> x' k'. (x', k') \<in> queue_abstract H \<longrightarrow> k \<le> k'))"
 "\<And> H.  \<lbrakk>queue_invar H; None = snd (queue_extract_min H)\<rbrakk> \<Longrightarrow>
            queue_abstract H = {}"
 "\<And> H x k. \<lbrakk>queue_invar H; Some x = snd (queue_extract_min H);
             (x, k) \<in> queue_abstract H\<rbrakk> \<Longrightarrow>
          queue_abstract (fst (queue_extract_min H)) =  queue_abstract H - {(x, k)}"
 and queue_insert:
 "\<And> H x k. \<lbrakk>queue_invar H; \<nexists> k. (x, k) \<in> (queue_abstract H)\<rbrakk> 
          \<Longrightarrow> queue_invar (queue_insert H x k)"
 "\<And> H x k.  \<lbrakk>queue_invar H; \<nexists> k. (x, k) \<in> queue_abstract H\<rbrakk> \<Longrightarrow>
           queue_abstract (queue_insert H x k) = queue_abstract H  \<union> {(x, k)}"
 and queue_decrease_key:
 "\<And> H x k k'. \<lbrakk>queue_invar H; (x, k') \<in>  (queue_abstract H); k < k'\<rbrakk> 
          \<Longrightarrow> queue_invar (queue_decrease_key H x k)"
 "\<And> H x k k'.  \<lbrakk>queue_invar H;  (x, k) \<in> queue_abstract H; k' < k\<rbrakk> \<Longrightarrow>
           queue_abstract (queue_decrease_key H x k') =
           queue_abstract H - {(x, k)} \<union> {(x, k')}"
 and key_for_element_unique:
 "\<And> H x k k'. \<lbrakk>queue_invar H; (x, k) \<in> queue_abstract H; (x, k') \<in> queue_abstract H\<rbrakk>
                  \<Longrightarrow> k = k'"

end