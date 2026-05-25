theory Double_Example
  imports Imperative.Imperative_DS
begin

locale double_naturals = 
imp_set_iterate where is_set = is_set and it_next = it_next +
imp_set_ins where ins = ins and is_set = is_set +
imp_set_empty where empty = empty and is_set = is_set
for is_set :: "nat set \<Rightarrow> 'simpl \<Rightarrow> assn" 
and ins :: "nat \<Rightarrow> 'simpl \<Rightarrow> 'simpl Heap"
and empty :: "'simpl Heap"
and it_next :: "'it \<Rightarrow> (nat \<times> 'it) Heap"
 +
fixes S::"nat set"
and  Simpl::'simpl
begin


partial_function (heap) double_all_elems_loop ::"'simpl \<Rightarrow> 'it \<Rightarrow> 'simpl Heap"
  where
"double_all_elems_loop simpl it = 
  (do {b <- it_has_next it;
       if \<not> b then  return simpl
       else  do {
         (x, it') <- it_next it;
          simpl' <- ins (2*x) simpl;
          double_all_elems_loop simpl' it'
       }})"



lemmas [code] = double_all_elems_loop.simps
end



(*interpretation hs: imp_set_iterate 
  is_hashset hs_is_it hs_it_init hs_it_has_next hs_it_next
  by (rule hs_iterate_impl)*)

definition "from_list_impl (xs:: nat list) \<equiv>
  do {S <- hs_new; foldM (\<lambda> x S. hs_ins  x S) xs S }"

  setup Locale_Code.open_block  
interpretation dbl_nats_hs: double_naturals
 hs_is_it hs_it_init hs_it_has_next is_hashset hs_ins hs_new hs_it_next
  by unfold_locales
setup Locale_Code.close_block

definition "double_all_elems_loop = dbl_nats_hs.double_all_elems_loop"

definition "sinit = from_list_impl [1,2,3,4]"
                           
definition "hs_it_init_nat = (hs_it_init::(nat, unit) hashtable
   \<Rightarrow> (nat \<times> (nat \<times> unit) list \<times> (nat, unit) hashtable) Heap)"(* do {s <- sinit; it <- hs_it_init s; return it}"*)

definition "hs_new_nat = (hs_new::(nat, unit) hashtable Heap)"

 find_theorems dbl_nats_hs.double_all_elems_loop
 export_code double_all_elems_loop  from_list_impl hs_it_init_nat hs_new_nat checking SML_imp

 ML_val \<open>
    val noi = @{code nat_of_integer}
    val from_list_impl  = @{code from_list_impl} o map  noi
    val double_all_elems_loop = @{code double_all_elems_loop}
    val hs_it_init = @{code hs_it_init_nat}
    val hs_new = @{code hs_new_nat}
   
    val sinit = from_list_impl [0,1,2,3,4,5] ()
    val doubled = double_all_elems_loop (hs_new ()) (hs_it_init sinit ()) ()
  
  \<close>


end