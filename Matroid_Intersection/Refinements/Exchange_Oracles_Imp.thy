theory Exchange_Oracles_Imp
  imports "Data_Structures.Imp_Bool_Set"
begin

section \<open>Imperative Exchange Oracles\<close>

text \<open>The imperative counterpart of the oracles of \<open>Exchange_Oracles\<close> for elements below \<open>n\<close>.
  Insertion and exchange queries are answered directly on the handle of the solution, whose
  assertion \<open>sol_assn\<close> is that of the solution set; whatever the oracle needs is part of
  that handle and kept up to date by the operations of the set, so there is no preparation
  step. They refine a functional oracle on sets of nats. The assertion \<open>ost\<close> holds static data
  of the oracle (e.g. an array of blocks) and is preserved.\<close>

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

text \<open>Potential exchange partners. Independently of the solution, an oracle names for every
  element \<open>x\<close> a list \<open>pts x\<close> containing every element that can ever form an exchange pair with
  \<open>x\<close>, in ascending order. The candidate graph of the exchange graph search is built from these
  lists once. The lists are read through a static handle \<open>H\<close> of the oracle with assertion
  \<open>pst H\<close>, one entry at a time: one query returns the length of \<open>pts x\<close>, the other its entry at
  a position. Every oracle can name all elements; a specific oracle can name fewer, e.g. a partition
  oracle names the block of \<open>x\<close>, which makes the candidate graph sparse.\<close>

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
