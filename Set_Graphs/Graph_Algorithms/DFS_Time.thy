theory DFS_Time
  imports DFS "HOL-Library.Time_Functions"
begin

provenance human

locale DFS_time = DFS where lookup = lookup 
for lookup :: "'adjmap \<Rightarrow> 'v \<Rightarrow> 'vset option" +
fixes T_diff::"'vset \<Rightarrow> 'vset \<Rightarrow> nat"
and T_sel::"'vset \<Rightarrow> nat" and T_insert::"'v \<Rightarrow> 'vset \<Rightarrow> nat"
and T_lookup::"'adjmap \<Rightarrow> 'v \<Rightarrow> nat" and T_G::nat and T_vset_empty::nat
and t_ret1::"('v, 'vset) DFS_state \<Rightarrow> nat" and t_ret2::"('v, 'vset) DFS_state \<Rightarrow> nat"
and t_call1::"('v, 'vset) DFS_state \<Rightarrow> nat" and t_call2::"('v, 'vset) DFS_state \<Rightarrow> nat"
begin

time_fun stack
text \<^marker>\<open>provenance ai\<close> \<open>Neither \<^theory_text>\<open>time_fun\<close> nor \<^theory_text>\<open>fun\<close> accepts the selector
pattern of a record extension, so the cost of @{term return} --- constant, like the costs that
\<^theory_text>\<open>time_fun\<close> gives the other selectors --- is a plain definition.\<close>

definition \<^marker>\<open>provenance ai\<close> T_return :: "('ver, 'vset, 'z) DFS_state_scheme \<Rightarrow> nat" where
  "T_return st = 0"

time_fun seen

definition "T_neighbourhood = undefined"

provenance ai

text \<open>The cost functions follow the recursion of @{term DFS}, i.e. that of the skeleton with the
reachability callbacks: the found test @{term reach_found}, the push hook @{term no_push} and the
backtrack hook @{term reach_on_backtrack}.\<close>

function (domintros) T_DFS::"('v, 'vset) DFS_state \<Rightarrow> nat" where
  "T_DFS dfs_state = 1+ T_stack dfs_state +
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow> 1+
       (if reach_found dfs_state then 1
        else (T_neighbourhood  v + T_seen dfs_state +
              T_diff (\<N>\<^sub>G v) (seen dfs_state) +
              (if (\<N>\<^sub>G v -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                 (
                  let u = (sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)));
                      stack' = u# (stack dfs_state);
                      seen' = insert u (seen dfs_state)
                  in
                   T_neighbourhood  v + T_seen dfs_state +
                 T_diff (\<N>\<^sub>G v) (seen dfs_state) + T_sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)) +
                 1 + T_stack dfs_state +
                 T_insert u (seen dfs_state) + T_seen dfs_state +
                    2 + (T_DFS (no_push u (dfs_state \<lparr>stack := stack', seen := seen' \<rparr>))))
                else 1 + (1 + T_DFS (reach_on_backtrack v (dfs_state \<lparr>stack := stack_tl\<rparr>))))) )
     | _ \<Rightarrow> 1)"
  by pat_completeness auto

function (domintros) T_DFS_coarse::"('v, 'vset) DFS_state \<Rightarrow> nat" where
  "T_DFS_coarse dfs_state =
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if reach_found dfs_state then t_ret1 dfs_state
        else ((if (\<N>\<^sub>G v -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                 (let u = (sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)));
                      stack' = u# (stack dfs_state);
                      seen' = insert u (seen dfs_state)
                  in t_call1 dfs_state +
                  (T_DFS_coarse (no_push u (dfs_state \<lparr>stack := stack', seen := seen' \<rparr>))))
                else t_call2 dfs_state
                     + T_DFS_coarse (reach_on_backtrack v (dfs_state \<lparr>stack := stack_tl\<rparr>)))))
     | _ \<Rightarrow> t_ret2 dfs_state)"
  by pat_completeness auto

provenance human

end

end
