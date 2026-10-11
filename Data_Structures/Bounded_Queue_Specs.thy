theory Bounded_Queue_Specs
  imports
    Main
begin

section \<open>FIFO Queues of Bounded Length\<close>

text \<open>A FIFO queue abstracted to a list (front first). What matters for an implementation is not a
      universe of elements but the capacity @{term cap}: elements may only be pushed while the
      queue holds fewer than @{term cap} elements. An implementation may therefore be a circular
      array of length @{term cap}, allocated once.\<close>

locale bounded_queue =
  fixes cap :: nat
  and queue_invar :: "'q \<Rightarrow> bool"
  and queue_abstract :: "'q \<Rightarrow> 'a list"
  and queue_empty :: "'q"
  and queue_push :: "'q \<Rightarrow> 'a \<Rightarrow> 'q"
  and queue_pop :: "'q \<Rightarrow> 'a \<times> 'q"
  and queue_is_empty :: "'q \<Rightarrow> bool"
  assumes queue_capacity:
      "\<And> Q. queue_invar Q \<Longrightarrow> length (queue_abstract Q) \<le> cap"
  and queue_empty:
      "queue_invar queue_empty"
      "queue_abstract queue_empty = []"
  and queue_push:
      "\<And> Q x. \<lbrakk>queue_invar Q; length (queue_abstract Q) < cap\<rbrakk> \<Longrightarrow> queue_invar (queue_push Q x)"
      "\<And> Q x. \<lbrakk>queue_invar Q; length (queue_abstract Q) < cap\<rbrakk> \<Longrightarrow>
          queue_abstract (queue_push Q x) = queue_abstract Q @ [x]"
  and queue_pop:
      "\<And> Q. \<lbrakk>queue_invar Q; queue_abstract Q \<noteq> []\<rbrakk> \<Longrightarrow> queue_invar (snd (queue_pop Q))"
      "\<And> Q. \<lbrakk>queue_invar Q; queue_abstract Q \<noteq> []\<rbrakk> \<Longrightarrow> fst (queue_pop Q) = hd (queue_abstract Q)"
      "\<And> Q. \<lbrakk>queue_invar Q; queue_abstract Q \<noteq> []\<rbrakk> \<Longrightarrow>
          queue_abstract (snd (queue_pop Q)) = tl (queue_abstract Q)"
  and queue_is_empty:
      "\<And> Q. queue_invar Q \<Longrightarrow> queue_is_empty Q \<longleftrightarrow> queue_abstract Q = []"

end
