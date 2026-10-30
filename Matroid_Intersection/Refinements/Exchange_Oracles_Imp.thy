theory Exchange_Oracles_Imp
  imports "Data_Structures.Imp_Bool_Set"
begin

provenance ai


section \<open>Imperative Exchange Oracles\<close>

text \<open>Imperative insertion and exchange queries on elements below \<open>n\<close> refine functional
  oracles on sets of nats. They operate directly on the solution handle, with assertion
  \<open>sol_assn\<close>. Set operations maintain its oracle data, so no preparation step is needed.
  The assertion \<open>ost\<close> holds preserved static data, such as an array of blocks.\<close>

locale exchange_oracle_imp =
  fixes n :: nat
    and orcl_prep :: "nat set \<Rightarrow> 'o"
    and ins_orcl :: "'o \<Rightarrow> nat \<Rightarrow> bool"
    and exch_orcl :: "'o \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
    and sol_assn :: "nat set \<Rightarrow> 'si \<Rightarrow> assn"
    and ins_imp :: "'si \<Rightarrow> nat \<Rightarrow> bool Heap"
    and exch_imp :: "'si \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap"
    and ost :: assn
  assumes ins_imp:
    "<sol_assn X Si * ost * \<up>(y < n)> ins_imp Si y
     <\<lambda> r. sol_assn X Si * ost * \<up>(r = ins_orcl (orcl_prep X) y)>"
    and exch_imp:
    "<sol_assn X Si * ost * \<up>(x < n \<and> y < n)> exch_imp Si x y
     <\<lambda> r. sol_assn X Si * ost * \<up>(r = exch_orcl (orcl_prep X) x y)>"

text \<open>The sorted list \<open>pts x\<close> contains all possible exchange partners of \<open>x\<close>.
  These lists form a fixed candidate graph. A static handle with assertion \<open>pst H\<close>
  provides length and indexed-entry queries. An oracle may list every element; a partition
  oracle lists only the block of \<open>x\<close>, yielding a sparse candidate graph.\<close>

locale exchange_partners_imp =
  fixes n :: nat
    and indep :: "nat set \<Rightarrow> bool"
    and orcl_prep :: "nat set \<Rightarrow> 'o"
    and ins_orcl :: "'o \<Rightarrow> nat \<Rightarrow> bool"
    and exch_orcl :: "'o \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
    and pts :: "nat \<Rightarrow> nat list"
    and pst :: "'h \<Rightarrow> assn"
    and npts_imp :: "'h \<Rightarrow> nat \<Rightarrow> nat Heap"
    and pt_imp :: "'h \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat Heap"
  assumes pts_sorted: "sorted_wrt (<) (pts x)"
    and pts_bound: "y \<in> set (pts x) \<Longrightarrow> y < n"
    and pts_cover: 
    "\<lbrakk>finite X; X \<subseteq> {0..<n}; indep X; x < n; y < n; x \<in> X; y \<notin> X;
      \<not> ins_orcl (orcl_prep X) y; exch_orcl (orcl_prep X) x y\<rbrakk> 
     \<Longrightarrow> y \<in> set (pts x) \<and> x \<in> set (pts y)"
    and npts_imp: "<pst H * \<up>(x < n)> npts_imp H x <\<lambda> r. pst H * \<up>(r = length (pts x))>"
    and pt_imp: 
    "<pst H * \<up>(x < n \<and> k < length (pts x))> pt_imp H x k <\<lambda> r. pst H * \<up>(r = pts x ! k)>"

text \<open>The trivial choice that works for every oracle.\<close>

lemma exchange_partners_all:
  "exchange_partners_imp n indep orcl_prep ins_orcl exch_orcl (\<lambda> _. [0..<n]) (\<lambda> _. emp) 
     (\<lambda> _ _. return n) (\<lambda> _ _ k. return k)"
  by unfold_locales sep_auto+

end
