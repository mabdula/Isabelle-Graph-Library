theory IDFS_Lists
  imports IDFS Alt_BFS_Lists
begin

provenance human

section \<open>The Incremental DFS on Neighbour Lists\<close>

text \<open>The incremental DFS for vertices that are natural numbers: graphs map a vertex to the list
      of its neighbours, and vertex sets are lists. The choice operation takes the head of a list,
      so the search always proceeds to the first neighbour in the neighbour list that has not been
      seen yet. This is the functional model of the imperative implementation on arrays.\<close>

locale IDFS_lists =
  fixes G :: "nat \<Rightarrow> nat list option" and P :: "nat \<Rightarrow> bool"
begin

sublocale idfs_l: DFS_avoid
  where empty = "\<lambda>_. None" and delete = "\<lambda>x M. fun_upd M x None" and lookup = "\<lambda>M x. M x"
    and insert = Cons and isin = "\<lambda>xs x. x \<in> set xs" and t_set = set and sel = hd
    and update = "\<lambda>x z M. M(x \<mapsto> z)" and adjmap_inv = "\<lambda>_. True"
    and vset_empty = Nil and vset_delete = "\<lambda>x xs. filter (\<lambda>y. y \<noteq> x) xs" and vset_inv = "\<lambda>_. True"
    and union = append and inter = "\<lambda>xs ys. filter (\<lambda>y. y \<in> set ys) xs"
    and diff = "\<lambda>xs ys. filter (\<lambda>y. y \<notin> set ys) xs"
    and G = G and stack0 = p0 and vis0 = V0 and avoid = A0 and Pv = P and level = lev
  for p0 V0 A0 lev
  by unfold_locales auto

text \<open>The incremental DFS from @{theory Micali_Vazirani.IDFS}: the head of the given stack is
      dropped if it is avoided or visited, then the search runs.\<close>

definition "IDFS_stack0_l A V p = (if p \<noteq> [] \<and> (hd p \<in> set A \<or> hd p \<in> set V) then tl p else p)"

definition "IDFS_l A p V =
  (let st = idfs_l.avoid_final_state_impl (IDFS_stack0_l A V p) V A in (ret st, visited st))"

lemma IDFS_l_eq:
  assumes "IDFS_witness (\<lambda>_. None) (\<lambda>x M. fun_upd M x None) Cons (\<lambda>xs x. x \<in> set xs) set hd
             (\<lambda>x z M. M(x \<mapsto> z)) (\<lambda>_. True) [] (\<lambda>x xs. filter (\<lambda>y. y \<noteq> x) xs) (\<lambda>_. True) append
             (\<lambda>xs ys. filter (\<lambda>y. y \<in> set ys) xs) (\<lambda>xs ys. filter (\<lambda>y. y \<notin> set ys) xs) (\<lambda>M x. M x)
             G lev"
  shows "IDFS_witness.IDFS_impl Cons (\<lambda>xs x. x \<in> set xs) hd [] append
           (\<lambda>xs ys. filter (\<lambda>y. y \<notin> set ys) xs) (\<lambda>M x. M x) G P = IDFS_l"
  by (intro ext)
     (simp add: IDFS_witness.IDFS_impl_def[OF assms] IDFS_witness.IDFS_stack0_def[OF assms]
                IDFS_l_def IDFS_stack0_l_def)

subsection \<open>Unfolding the search\<close>

lemma neighbourhood_nbs: "idfs_l.neighbourhood' v = nbs G v"
  by (simp add: nbs_def idfs_l.Graph.neighbourhood_def)

lemma idfs_l_found_iff:
  "idfs_l.av_found A st = (case stack st of [] \<Rightarrow> False | v # _ \<Rightarrow> P v \<and> v \<notin> set A)"
  by (simp add: idfs_l.av_found_def)

lemma idfs_l_skel_simps:
  "stack st = [] \<Longrightarrow> idfs_l.DFS_avoid_impl A st = st\<lparr>ret := None\<rparr>"
  "\<lbrakk>stack st = v # stl; P v; v \<notin> set A\<rbrakk> \<Longrightarrow>
     idfs_l.DFS_avoid_impl A st = st\<lparr>ret := Some (stack st)\<rparr>"
  "\<lbrakk>stack st = v # stl; \<not> (P v \<and> v \<notin> set A); filter (\<lambda>y. y \<notin> set (seen st)) (nbs G v) = u # us\<rbrakk>
   \<Longrightarrow> idfs_l.DFS_avoid_impl A st = idfs_l.DFS_avoid_impl A (st\<lparr>stack := u # stack st, seen := u # seen st\<rparr>)"
  "\<lbrakk>stack st = v # stl; \<not> (P v \<and> v \<notin> set A); filter (\<lambda>y. y \<notin> set (seen st)) (nbs G v) = []\<rbrakk>
   \<Longrightarrow> idfs_l.DFS_avoid_impl A st =
         idfs_l.DFS_avoid_impl A (st\<lparr>stack := stl,
            visited := (if v \<in> set A then visited st else v # visited st)\<rparr>)"
  by (auto simp add: idfs_l.av.DFS_skel_impl.simps[of _ st] idfs_l.av_found_def
                    idfs_l.av_on_empty_def idfs_l.av_on_found_def idfs_l.av_on_backtrack_def
                    neighbourhood_nbs)

end

end
