theory DFS_Time
  imports DFS "HOL-Data_Structures.Define_Time_Function"
begin
locale DFS_time = DFS where lookup = lookup 
for lookup :: "'adjmapmap\<Rightarrow> 'v \<Rightarrow> 'vset option" +
fixes T_diff::"'vset \<Rightarrow> 'vset \<Rightarrow> nat"
and T_sel::"'vset \<Rightarrow> nat" and T_insert::"'v \<Rightarrow> 'vset \<Rightarrow> nat"
and T_lookup::"'adjmapmap\<Rightarrow> 'v \<Rightarrow> nat" and T_G::nat and T_vset_empty::nat
and t_ret1::"('v, 'vset) DFS_state \<Rightarrow> nat" and t_ret2::"('v, 'vset) DFS_state \<Rightarrow> nat"
and t_call1::"('v, 'vset) DFS_state \<Rightarrow> nat" and t_call2::"('v, 'vset) DFS_state \<Rightarrow> nat"
begin

time_fun stack
time_fun return
time_fun seen

definition "T_neighbourhood = undefined"

function (domintros) T_DFS::"('v, 'vset) DFS_state \<Rightarrow> nat" where
  "T_DFS dfs_state = 1+ T_stack dfs_state +
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow> 1+
       (if v = t then 1
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
                    2 + (T_DFS (dfs_state \<lparr>stack := stack', seen := seen' \<rparr>)))
                else 1 + (
                  let stack' = stack_tl in
                     1 + T_DFS (dfs_state \<lparr>stack := stack'\<rparr>)))) )
     | _ \<Rightarrow> 1)"
  by pat_completeness auto

function (domintros) T_DFS_coarse::"('v, 'vset) DFS_state \<Rightarrow> nat" where
  "T_DFS_coarse dfs_state = 
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow> 
       (if v = t then t_ret1 dfs_state
        else ((if (\<N>\<^sub>G v -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                 (let u = (sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)));
                      stack' = u# (stack dfs_state);
                      seen' = insert u (seen dfs_state)                     
                  in t_call1 dfs_state + 
                  (T_DFS_coarse (dfs_state \<lparr>stack := stack', seen := seen' \<rparr>)))
                else (let stack' = stack_tl 
                      in t_call2 dfs_state +  T_DFS_coarse (dfs_state \<lparr>stack := stack'\<rparr>)))))
     | _ \<Rightarrow> t_ret2 dfs_state)"