theory Awalk_Defs
  imports 
    Pair_Graph
begin

type_synonym 'a awalk = "('a \<times> 'a) list"

fun awalk_verts :: "'a \<Rightarrow> 'a awalk \<Rightarrow> 'a list" where
    "awalk_verts u [] = [u]"
  | "awalk_verts u ((t, h) # es) = t # awalk_verts h es"

abbreviation awhd :: "'a \<Rightarrow> 'a awalk \<Rightarrow> 'a" where
  "awhd u p \<equiv> hd (awalk_verts u p)"

abbreviation awlast :: "'a \<Rightarrow> 'a awalk \<Rightarrow> 'a" where
  "awlast u p \<equiv> last (awalk_verts u p)"

fun cas :: "'a \<Rightarrow> 'a awalk \<Rightarrow> 'a \<Rightarrow> bool" where
    "cas u [] v = (u = v)"
  | "cas u ((t, h) # es) v = (u = t \<and> cas h es v)"


definition awalk :: "'a dgraph \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "awalk E u p v \<equiv> u \<in> dVs E \<and> set p \<subseteq> E \<and> cas u p v"

definition trail :: "'a dgraph \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "trail E u p v \<equiv> awalk E u p v \<and> distinct p"

definition apath :: "'a dgraph \<Rightarrow> 'a \<Rightarrow> 'a awalk \<Rightarrow> 'a \<Rightarrow> bool" where
  "apath E u p v \<equiv> awalk E u p v \<and> distinct (awalk_verts u p)"

definition closed_w :: "'a dgraph \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> bool" where
  "closed_w E p \<equiv> \<exists>u. awalk E u p u \<and> 0 < length p"

definition cycle :: "'a dgraph \<Rightarrow> 'a awalk \<Rightarrow> bool" where
  "cycle E p \<equiv> \<exists>u. awalk E u p u \<and> distinct (tl (awalk_verts u p)) \<and> p \<noteq> []"

fun is_awalk_cyc_decomp :: "'a dgraph \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> 
  (('a \<times> 'a) list \<times> ('a \<times> 'a) list \<times> ('a \<times> 'a) list) \<Rightarrow> bool" where
  "is_awalk_cyc_decomp E p (q, r, s) \<longleftrightarrow> p = q @ r @ s
    \<and> (\<exists>u v w. awalk E u q v \<and> awalk E v r v \<and> awalk E v s w)
    \<and> 0 < length r
    \<and> (\<exists>u. distinct (awalk_verts u q))"

definition awalk_cyc_decomp :: "'a dgraph \<Rightarrow> ('a \<times> 'a) list 
  \<Rightarrow> ('a \<times> 'a) list \<times> ('a \<times> 'a) list \<times> ('a \<times> 'a) list" where
  "awalk_cyc_decomp E p = (SOME qrs. is_awalk_cyc_decomp E p qrs)"

function awalk_to_apath :: "'a dgraph \<Rightarrow> ('a \<times> 'a) list \<Rightarrow> ('a \<times> 'a) list" where
  "awalk_to_apath E p = (if \<not>(\<exists>u. distinct (awalk_verts u p)) \<and> (\<exists>u v. awalk E u p v)
    then (let (q,r,s) = awalk_cyc_decomp E p in awalk_to_apath E (q @ s))
    else p)"
  by auto



end