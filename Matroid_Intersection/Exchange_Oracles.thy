theory Exchange_Oracles
  imports Matroid_Intersection 
begin

section \<open>Insertion and Exchange Oracles\<close>

text \<open>This theory turns the weak insertion oracles and the circuit oracles into
      exchange oracles.\<close>

text \<open>Characterisation of the exchange graph by independence tests only
  and an oracle interface for a single matroid that allows a per-iteration
  preparation of the current solution.
  Nothing here knows about path search or augmentation.\<close>

subsection \<open>The Exchange Graph via Independence Tests\<close>

context double_matroid
begin

lemma A1_exchange:
  "indep1 X \<Longrightarrow>
     (x, y) \<in> A1 X \<longleftrightarrow>
       x \<in> X \<and> y \<in> carrier - X \<and> \<not> indep1 (insert y X) \<and> indep1 (insert y (X - {x}))"
  using matroid1.circuit_exchange_gen[of X y x]
  by (auto simp: A1_def)

lemma A2_exchange:
  "indep2 X \<Longrightarrow>
     (y, x) \<in> A2 X \<longleftrightarrow>
       x \<in> X \<and> y \<in> carrier - X \<and> \<not> indep2 (insert y X) \<and> indep2 (insert y (X - {x}))"
  using matroid2.circuit_exchange_gen[of X y x]
  by (auto simp: A2_def)

lemma A1_exchange_char:
  "indep1 X \<Longrightarrow>
     A1 X = {(x, y) | x y. x \<in> X \<and> y \<in> carrier - X \<and>
                 \<not> indep1 (insert y X) \<and> indep1 (insert y (X - {x}))}"
  by (auto simp: A1_exchange)

lemma A2_exchange_char:
  "indep2 X \<Longrightarrow>
     A2 X = {(y, x) | x y. x \<in> X \<and> y \<in> carrier - X \<and>
                 \<not> indep2 (insert y X) \<and> indep2 (insert y (X - {x}))}"
  by (auto simp: A2_exchange)

end

subsection \<open>Oracle Interface\<close>

text \<open>\<open>orcl_prep\<close> is called once per iteration on the current solution.
  The resulting context answers insertion queries (is \<open>X + y\<close> independent?) and
  exchange queries (is \<open>X - x + y\<close> independent?). Exchange queries are only asked
  for dependent \<open>X + y\<close>.\<close>

locale indep_oracle_spec =
  fixes orcl_prep :: "'mset \<Rightarrow> 'octx"
    and ins_orcl  :: "'octx \<Rightarrow> 'a \<Rightarrow> bool"
    and exch_orcl :: "'octx \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"

locale indep_oracle =
  indep_oracle_spec orcl_prep ins_orcl exch_orcl +
  matroid carrier indep
  for orcl_prep :: "'mset \<Rightarrow> 'octx"
    and ins_orcl  :: "'octx \<Rightarrow> 'a \<Rightarrow> bool"
    and exch_orcl :: "'octx \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
    and carrier :: "'a set" and indep +
  fixes to_set :: "'mset \<Rightarrow> 'a set"
    and set_invar :: "'mset \<Rightarrow> bool"
  assumes ins_orcl:
    "\<And> X y. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; indep (to_set X); y \<in> carrier - to_set X\<rbrakk>
       \<Longrightarrow> ins_orcl (orcl_prep X) y \<longleftrightarrow> indep (insert y (to_set X))"
  and exch_orcl:
    "\<And> X x y. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; indep (to_set X); y \<in> carrier - to_set X;
               x \<in> to_set X; \<not> indep (insert y (to_set X))\<rbrakk>
       \<Longrightarrow> exch_orcl (orcl_prep X) x y \<longleftrightarrow> indep (insert y (to_set X - {x}))"
begin

lemma exch_orcl_circuit:
  "\<lbrakk>set_invar X; to_set X \<subseteq> carrier; indep (to_set X); y \<in> carrier - to_set X; x \<in> to_set X;
    \<not> indep (insert y (to_set X))\<rbrakk> \<Longrightarrow>
     exch_orcl (orcl_prep X) x y \<longleftrightarrow> x \<in> the_circuit (insert y (to_set X)) - {y}"
  using circuit_exchange[of "to_set X" x y]
  by (simp add: exch_orcl)

end

subsection \<open>Adapters\<close>

text \<open>A weak independence oracle yields an exchange oracle by deleting \<open>x\<close>.\<close>

locale weak_indep_oracle =
  matroid carrier indep for carrier indep +
  fixes to_set :: "'mset \<Rightarrow> 'a set"
    and set_invar :: "'mset \<Rightarrow> bool"
    and set_delete :: "'a \<Rightarrow> 'mset \<Rightarrow> 'mset"
    and weak_orcl :: "'a \<Rightarrow> 'mset \<Rightarrow> bool"
  assumes set_delete: 
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> set_invar (set_delete x S)"
    "\<And> S x. \<lbrakk>set_invar S; x \<in> carrier\<rbrakk> \<Longrightarrow> to_set (set_delete x S) = (to_set S) - {x}"
  assumes weak_orcl: 
    "\<And> X x. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; x \<in> carrier; x \<notin> to_set X; indep (to_set X)\<rbrakk>
       \<Longrightarrow> weak_orcl x X \<longleftrightarrow> indep (insert x (to_set X))"
begin

definition "weak_ins_orcl X y = weak_orcl y X"
definition "weak_exch_orcl X x y = weak_orcl y (set_delete x X)"

sublocale indep_oracle id weak_ins_orcl weak_exch_orcl carrier indep to_set set_invar
proof(unfold_locales, goal_cases)
  case (2 X x y)
  hence "x \<in> carrier"
    by blast
  thus ?case
    using 2 weak_orcl[of "set_delete x X" y] set_delete[of X x]
      indep_subset[of "to_set X" "to_set X - {x}"]
    by (auto simp: weak_exch_orcl_def)
qed (auto simp: weak_ins_orcl_def weak_orcl)

end

text \<open>A circuit oracle yields an exchange oracle by membership tests.\<close>

locale circuit_indep_oracle =
  matroid carrier indep for carrier indep +
  fixes to_set :: "'mset \<Rightarrow> 'a set"
    and set_invar :: "'mset \<Rightarrow> bool"
    and weak_orcl :: "'a \<Rightarrow> 'mset \<Rightarrow> bool"
    and circuit :: "'a \<Rightarrow> 'mset \<Rightarrow> 'mset_red"
    and to_set_red :: "'mset_red \<Rightarrow> 'a set"
    and set_memb_red :: "'a \<Rightarrow> 'mset_red \<Rightarrow> bool"
    and set_invar_red :: "'mset_red \<Rightarrow> bool"
  assumes set_memb_red: 
    "\<And> S x. set_invar_red S \<Longrightarrow> set_memb_red x S \<longleftrightarrow> x \<in> to_set_red S"
  assumes weak_orcl: 
    "\<And> X x. \<lbrakk>set_invar X; to_set X \<subseteq> carrier; x \<in> carrier; x \<notin> to_set X; indep (to_set X)\<rbrakk>
       \<Longrightarrow> weak_orcl x X \<longleftrightarrow> indep (insert x (to_set X))"
  assumes circuit: 
    "\<And> X y. \<lbrakk>set_invar X; indep (to_set X); to_set X \<subseteq> carrier; y \<in> carrier;
             \<not> indep (insert y (to_set X))\<rbrakk>
        \<Longrightarrow> to_set_red (circuit y X) = the_circuit (insert y (to_set X)) - {y}"
    "\<And> X y. \<lbrakk>set_invar X; indep (to_set X); to_set X \<subseteq> carrier; y \<in> carrier;
              \<not> indep (insert y (to_set X))\<rbrakk>
        \<Longrightarrow> set_invar_red (circuit y X)"
begin

definition "circ_ins_orcl X y = weak_orcl y X"
definition "circ_exch_orcl X x y = set_memb_red x (circuit y X)"

sublocale indep_oracle id circ_ins_orcl circ_exch_orcl carrier indep to_set set_invar
proof(unfold_locales, goal_cases)
  case (2 X x y)
  thus ?case
    using circuit_exchange[of "to_set X" x y]
    by (auto simp: circ_exch_orcl_def set_memb_red circuit)
qed (auto simp: circ_ins_orcl_def weak_orcl)

end

end
