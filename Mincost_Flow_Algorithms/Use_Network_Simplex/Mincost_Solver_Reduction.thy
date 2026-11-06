section \<open>The DIMACS Minimum Cost Flow Problem\<close>

text \<open>This theory is the place where the minimum cost flow problem as posed by the
      \emph{DIMACS Challenge: Network Flows 2.0} specification (see \<open>mincost_dimacs.pdf\<close>) is to be
      related to the min cost flow problem of the library.

      \paragraph{The instance.} An instance is a directed graph \<open>G = (V, A)\<close>, given in an ASCII
      file whose lines carry a single-character designator:
      \begin{itemize}
      \item \<open>c \<dots>\<close> --- a comment line, ignored;
      \item \<open>p min <n> <m>\<close> --- the problem line, fixing the number \<open>n\<close> of nodes and the number
            \<open>m\<close> of arcs; nodes are identified by the integers \<open>1 \<dots> n\<close>;
      \item \<open>n <v> <supply>\<close> --- a node line, present only for nodes of non-zero supply;
            the supply is the balance \<open>b v\<close> below, and a negative supply is called a demand;
      \item \<open>a <v> <w> <l> <u> <c>\<close> --- an arc line: an arc from \<open>v\<close> to \<open>w\<close> with lower bound
            \<open>l\<close>, upper bound \<open>u\<close> and per-unit cost \<open>c\<close>. Parallel arcs are allowed and may not be
            merged, since they can carry different costs.
      \end{itemize}
      All numbers occurring in an instance are integers.

      \paragraph{The problem.} Writing \<open>f\<close> for the flow, the specification asks to minimise
      \<open>\<Sum>\<^bsub>a \<in> A\<^esub> c(a) f(a)\<close> subject to
      \begin{align}        l(a) {\isasymle} f(a) &{\isasymle} u(a) & {\isasymforall} a &{\isasymin} A \\
        \textstyle{\isasymSum}_{x : (w,x) {\isasymin} A} f(w,x) - \textstyle{\isasymSum}_{v : (v,w) {\isasymin} A} f(v,w) &= b(w)
           & \forall w &{\isasymin} V
      \end{align}

      \paragraph{Output.} A solution consists of a solution line \<open>s <F>\<close> carrying the cost of the
      flow found, together with one flow line \<open>f <v> <w> <x>\<close> per arc. If there is no feasible
      solution, this is reported on a comment line instead and neither solution nor flow lines
      appear.\<close>

theory Mincost_Solver_Reduction
  imports Flow_Theory.Cost_Optimality Data_Structures.Real_Embedding
begin


subsection \<open>Validity and optimality\<close>

text \<open>An instance adds two data to a cost flow network: the lower bounds \<open>l\<close> of the arc
      lines and the supplies \<^term>\<open>b\<close> of the node lines. Both are fixed by the following locale,
      which is otherwise the assumption-free \<^locale>\<open>cost_flow_spec\<close>: no finiteness, no
      non-emptiness and in particular no sign condition is needed to say what a valid flow is.

      Two deliberate generalisations over the DIMACS document:

      \begin{itemize}
      \item \emph{No assumption on the ranges.} The lower bound \<^term>\<open>l\<close> has the same type
            \<^typ>\<open>'edge \<Rightarrow> ereal\<close> as the capacity \<^term>\<open>\<u>\<close>, so the admissible interval
            \<^term>\<open>{l e..\<u> e}\<close> of an edge may be any interval of reals, including ones that are
            unbounded on either side. We require neither \<^term>\<open>0 \<le> l e\<close> nor \<^term>\<open>0 \<le> \<u> e\<close> nor
            \<^term>\<open>l e \<le> \<u> e\<close>; in particular an edge may be forced to carry negative flow, and an
            edge with an empty interval simply makes the instance infeasible. Note that this
            departs from \<open>isuflow\<close>, which builds \<open>0 \<le> f e\<close> into validity.
      \item \emph{The node set is an argument.} \<^term>\<open>\<V>\<close> is \<^term>\<open>dVs (make_pair ` \<E>)\<close> and hence
            cannot contain a vertex without incident edges, whereas a DIMACS instance may well
            declare an isolated node, even one of non-zero supply. The balance constraints are
            therefore quantified over a node set \<^term>\<open>V\<close> given as an argument, intended to be the
            set \<open>{1..n}\<close> of the problem line, which may properly contain \<^term>\<open>\<V>\<close>.
      \end{itemize}\<close>

locale dimacs_spec = cost_flow_spec where \<E> = "\<E>::'edge set" for \<E> +
  fixes l::"'edge \<Rightarrow> ereal"
    and b::"'a \<Rightarrow> real"
begin

text \<open>Validity: constraint (1) on every edge and constraint (2) at every node of
      \<^term>\<open>V\<close>. The net outflow \<^term>\<open>- (ex\<^bsub>f\<^esub> v)\<close> must equal the
      supply exactly. This is the balance clause of the library's \<open>isbflow\<close>, so the two
      formulations differ only in the lower bound of (1), and removing it is the whole content
      of the reduction below.\<close>

definition is_dimacs_flow :: "'a set \<Rightarrow> ('edge \<Rightarrow> real) \<Rightarrow> bool" where
"is_dimacs_flow V f \<longleftrightarrow>
   ((\<forall> e \<in> \<E>. l e \<le> ereal (f e) \<and> ereal (f e) \<le> \<u> e) \<and>
    (\<forall> v \<in> V. b v = - (ex\<^bsub>f\<^esub> v)))"

lemma is_dimacs_flowI:
  "\<lbrakk>\<And> e. e \<in> \<E> \<Longrightarrow> l e \<le> ereal (f e); \<And> e. e \<in> \<E> \<Longrightarrow> ereal (f e) \<le> \<u> e;
    \<And> v. v \<in> V \<Longrightarrow> b v = - (ex\<^bsub>f\<^esub> v)\<rbrakk>
   \<Longrightarrow> is_dimacs_flow V f"
and is_dimacs_flowE:
  "is_dimacs_flow V f \<Longrightarrow>
     (\<lbrakk>\<And> e. e \<in> \<E> \<Longrightarrow> l e \<le> ereal (f e); \<And> e. e \<in> \<E> \<Longrightarrow> ereal (f e) \<le> \<u> e;
       \<And> v. v \<in> V \<Longrightarrow> b v = - (ex\<^bsub>f\<^esub> v)\<rbrakk> \<Longrightarrow> P)
     \<Longrightarrow> P"
  by (auto simp: is_dimacs_flow_def)

text \<open>Optimality: a valid flow of least cost; \<^term>\<open>\<C> f\<close> is literally the DIMACS
      objective.\<close>

definition is_dimacs_Opt :: "'a set \<Rightarrow> ('edge \<Rightarrow> real) \<Rightarrow> bool" where
"is_dimacs_Opt V f \<longleftrightarrow>
   (is_dimacs_flow V f \<and> (\<forall> f'. is_dimacs_flow V f' \<longrightarrow> \<C> f \<le> \<C> f'))"

lemma is_dimacs_OptI:
  "\<lbrakk>is_dimacs_flow V f; \<And> f'. is_dimacs_flow V f' \<Longrightarrow> \<C> f \<le> \<C> f'\<rbrakk> \<Longrightarrow> is_dimacs_Opt V f"
and is_dimacs_OptE:
  "is_dimacs_Opt V f \<Longrightarrow>
     (\<lbrakk>is_dimacs_flow V f; \<And> f'. is_dimacs_flow V f' \<Longrightarrow> \<C> f \<le> \<C> f'\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: is_dimacs_Opt_def)

subsection \<open>Isolated nodes are harmless\<close>

text \<open>A node outside of \<^term>\<open>\<V>\<close> has no incident edge, hence zero excess.\<close>

lemma delta_plus_outside_V: "v \<notin> \<V> \<Longrightarrow> \<delta>\<^sup>+ v = {}"
and delta_minus_outside_V: "v \<notin> \<V> \<Longrightarrow> \<delta>\<^sup>- v = {}"
  by (auto simp: delta_plus_def delta_minus_def make_pair_def dVs_def)

lemma ex_outside_V: "v \<notin> \<V> \<Longrightarrow> (ex\<^bsub>f\<^esub> v) = 0"
  by (simp add: ex_def delta_plus_outside_V delta_minus_outside_V)

text \<open>Consequently an isolated node constrains nothing \<^emph>\<open>provided its supply is
      zero\<close>. An isolated node of non-zero supply makes the instance infeasible, as its excess
      is \<open>0\<close> whatever the flow does. So the extra nodes of the DIMACS format may be discarded
      after that check, and validity and optimality then only depend on \<^term>\<open>V \<inter> \<V>\<close>.
      The reduction below performs the check: see \<open>bal_ok\<close>, where an isolated node has zero
      incident capacity and hence balance \<open>0\<close>.\<close>

lemma no_dimacs_flow_if_isolated_supply:
  "\<lbrakk>v \<in> V; v \<notin> \<V>; b v \<noteq> 0\<rbrakk> \<Longrightarrow> \<not> is_dimacs_flow V f"
  by (auto elim!: is_dimacs_flowE simp: ex_outside_V)

text \<open>The following two lemmas must not be used as rewrite rules or with \<open>intro\<close>: the right hand
      side is again an instance of the left hand side.\<close>

lemma is_dimacs_flow_restrict_V:
  "(\<And> v. \<lbrakk>v \<in> V; v \<notin> \<V>\<rbrakk> \<Longrightarrow> b v = 0) \<Longrightarrow> is_dimacs_flow V f = is_dimacs_flow (V \<inter> \<V>) f"
  using ex_outside_V
  by (fastforce simp: is_dimacs_flow_def)

lemma is_dimacs_Opt_restrict_V:
  "(\<And> v. \<lbrakk>v \<in> V; v \<notin> \<V>\<rbrakk> \<Longrightarrow> b v = 0) \<Longrightarrow> is_dimacs_Opt V f = is_dimacs_Opt (V \<inter> \<V>) f"
  using is_dimacs_flow_restrict_V
  by (simp add: is_dimacs_Opt_def)

end

subsection \<open>Instances with finite data\<close>

text \<open>The locale above is more permissive than a DIMACS instance in two respects. First,
      \<^term>\<open>\<E>\<close> may be infinite, and a \<^const>\<open>sum\<close> over an infinite set is
      \<open>0\<close>, so every valid flow would count as optimal. Second, infinite bounds allow valid
      flows of unbounded cost, so that neither of the two output cases of the format applies. A
      DIMACS instance has finitely many arcs and integer bounds, which restores the dichotomy
      between an optimal solution and infeasibility.\<close>

locale dimacs_network = dimacs_spec where \<E> = "\<E>::'edge set" for \<E> +
  assumes finite_E: "finite \<E>"
      and u_finite: "\<And> e. e \<in> \<E> \<Longrightarrow> \<bar>\<u> e\<bar> \<noteq> \<infinity>"
      and l_finite: "\<And> e. e \<in> \<E> \<Longrightarrow> \<bar>l e\<bar> \<noteq> \<infinity>"

subsection \<open>The instance as lists\<close>

text \<open>The parsed form of an instance, in the style of \<open>initial_basis_code_spec\<close> of
      \<open>Network_Simplex_Initial_Basis_Code\<close>: the arc lines become five parallel lists indexed by the
      arc number (\<^term>\<open>fst_list\<close>, \<^term>\<open>snd_list\<close>, \<^term>\<open>lower\<close>,
      \<^term>\<open>upper\<close>, \<^term>\<open>cost_list\<close>), and the node lines one list
      \<^term>\<open>balance_list\<close> indexed by the node number.

      The counts \<^term>\<open>m\<close> and \<^term>\<open>n\<close> of the problem line are fixed alongside the
      data. That they are the lengths of the lists is only assumed where needed, and everything
      below is driven by \<^term>\<open>m\<close> and \<^term>\<open>n\<close>, never by a list's length.

      The numeric type \<^typ>\<open>'n\<close> is a \<^class>\<open>linordered_idom\<close>, as in the executable
      network simplex, so that an instance can be read at \<^typ>\<open>int\<close> and mapped into the
      reals only where the proofs need it.

      Vertices are the positions \<open>{0..<n}\<close> of \<^term>\<open>balance_list\<close>. A DIMACS instance
      names its nodes \<open>1 \<dots> n\<close>, so it is read with a \<^term>\<open>balance_list\<close> of length
      \<open>n+1\<close> whose slot \<open>0\<close> is a dummy, exactly as \<open>b_arr\<close> of
      \<open>Network_Simplex_Initial_Basis_Code\<close> does.\<close>

locale dimacs_lists =
  fixes fst_list     :: "nat list"
    and snd_list     :: "nat list"
    and lower        :: "('n::linordered_idom) list"
    and upper        :: "'n list"
    and cost_list    :: "'n list"
    and balance_list :: "'n list"
    and m            :: nat
    and n            :: nat
begin

subsection \<open>Reduction to the standard format\<close>

text \<open>The target is the shape of the library's \<open>isbflow\<close> and \<open>is_Opt\<close>: capacities
      only, non-negative flow, the balance met exactly, and the vertex set \<open>dVs\<close> of the arcs.
      So only the lower bounds have to go, by the substitution \<open>g e = f e - l e\<close>
      (\<open>isbflow_lb_iff\<close> of \<open>Capacity_Balance_Reductions\<close>): capacities shrink to
      \<open>u e - l e\<close> and balances shift by the excess of \<open>l\<close>. The cost changes by the
      constant \<open>\<Sum> e < m. c e * l e\<close>, which \<^term>\<open>cost_shift\<close> records.

      A vertex without arcs stays isolated in the reduced network and is not in \<open>\<V>\<close>; it has
      no incident capacity, so \<open>bal_ok\<close> forces its balance to \<open>0\<close>, which is what
      \<open>is_dimacs_flow_restrict_V\<close> needs. Vertex \<open>0\<close> is not a DIMACS node, and slot
      \<open>0\<close> of \<open>balance_list\<close> is ignored.

      The reduced instance has exactly the original arcs, so one fused pass over \<open>[0..<m]\<close>
      builds the capacities and the balances: a step shrinks the range of its arc, scatters its
      lower bound onto its two endpoints (head first, so a self-loop cancels) and accumulates the
      cost shift. An arc with \<open>upper ! e < lower ! e\<close> has an empty range; it gets capacity
      \<open>0\<close> and clears the flag \<open>red_ok_arcs\<close>, and the original instance is then
      infeasible.\<close>

definition red_step ::
  "nat \<Rightarrow> 'n list \<times> 'n list \<times> 'n \<times> bool \<Rightarrow> 'n list \<times> 'n list \<times> 'n \<times> bool" where
  "red_step = (\<lambda> i (us, bal, sh, ok).
     let x = fst_list ! i; y = snd_list ! i;
         li = lower ! i; ui = upper ! i; ci = cost_list ! i;
         a = bal[y := bal ! y + li]
     in (us[i := (if li \<le> ui then ui - li else 0)], a[x := a ! x - li], sh + ci * li,
         ok \<and> li \<le> ui))"

text \<open>Every capacity the pass emits is finite and non-negative, so the solver's unboundedness
      verdict is unreachable, see \<open>reduced_no_neg_infty_cycle\<close>.\<close>

definition red_upper_at :: "nat \<Rightarrow> 'n" where
  "red_upper_at i = (if lower ! i \<le> upper ! i then upper ! i - lower ! i else 0)"

text \<open>The pass starts from the parsed balances with slot \<open>0\<close> forced to \<open>0\<close>.\<close>

definition red_bal_init :: "'n list" where
  "red_bal_init = balance_list[0 := 0]"

definition red_init :: "'n list \<times> 'n list \<times> 'n \<times> bool" where
  "red_init = (replicate m 0, red_bal_init, 0, True)"

definition red_pass :: "'n list \<times> 'n list \<times> 'n \<times> bool" where
  "red_pass = fold red_step [0..<m] red_init"

definition red_upper :: "'n list" where
  "red_upper = (let (us, _, _, _) = red_pass in us)"

definition red_balance_raw :: "'n list" where
  "red_balance_raw = (let (_, bal, _, _) = red_pass in bal)"

definition cost_shift :: "'n" where
  "cost_shift = (let (_, _, sh, _) = red_pass in sh)"

definition red_ok_arcs :: bool where
  "red_ok_arcs = (let (_, _, _, ok) = red_pass in ok)"

text \<open>Reading the answer back: the reduced flow \<^term>\<open>gs\<close> is indexed by the original arcs, so
      undoing the substitution adds the lower bound back at each position. The flow lines
      \<open>f <v> <w> <x>\<close> are \<^term>\<open>fst_list ! e\<close>, \<^term>\<open>snd_list ! e\<close> and
      \<^term>\<open>orig_flow gs ! e\<close>, and the solution value \<open>s <F>\<close> is
      \<^term>\<open>orig_cost\<close> of the recovered flow.\<close>

definition orig_flow :: "'n list \<Rightarrow> 'n list" where
  "orig_flow gs = map (\<lambda> e. gs ! e + lower ! e) [0..<m]"

definition orig_cost :: "'n list \<Rightarrow> 'n" where
  "orig_cost fs = fold (\<lambda> e s. s + cost_list ! e * fs ! e) [0..<m] 0"

text \<open>Projections onto the two arrays the pass writes keep the step lemmas first-order.\<close>

definition rp_us where "rp_us st = fst st"
definition rp_bal where "rp_bal st = fst (snd st)"

lemma rp_projs [simp]:
  "rp_us (us, bal, sh, ok) = us"
  "rp_bal (us, bal, sh, ok) = bal"
  by (simp_all add: rp_us_def rp_bal_def)

lemma red_pass_projs:
  "red_upper = rp_us red_pass" "red_balance_raw = rp_bal red_pass"
  "red_ok_arcs = snd (snd (snd red_pass))"
  by (simp_all add: red_upper_def red_balance_raw_def red_ok_arcs_def rp_us_def rp_bal_def split_beta)

lemma red_step_arc_length [simp]:
  "length (rp_us (red_step i st)) = length (rp_us st)"
  "length (rp_bal (red_step i st)) = length (rp_bal st)"
  by (simp_all add: red_step_def Let_def rp_us_def rp_bal_def split: prod.splits)

lemma red_fold_length [simp]:
  "length (rp_us (fold red_step es st)) = length (rp_us st)"
  "length (rp_bal (fold red_step es st)) = length (rp_bal st)"
  by (induction es arbitrary: st) simp_all

text \<open>A step writes the capacity array at its own index and leaves every other index alone.\<close>

lemma red_step_arc_upd: "rp_us (red_step i st) = (rp_us st)[i := red_upper_at i]"
  by (cases st) (simp add: red_step_def Let_def red_upper_at_def)

lemma red_fold_arc_notin: "j \<notin> set es \<Longrightarrow> rp_us (fold red_step es st) ! j = rp_us st ! j"
  by (induction es arbitrary: st) (auto simp: red_step_arc_upd)

lemma red_fold_arc_in:
  "\<lbrakk>distinct es; j \<in> set es; length (rp_us st) = m; j < m\<rbrakk>
   \<Longrightarrow> rp_us (fold red_step es st) ! j = red_upper_at j"
proof(induction es arbitrary: st)
  case (Cons a es)
  show ?case
    using Cons.prems Cons.IH[of "red_step a st"]
    by (auto simp: red_fold_arc_notin red_step_arc_upd)
qed simp

lemma red_upper_length: "length red_upper = m"
  by (simp add: red_pass_projs red_pass_def red_init_def)

text \<open>Every position of the capacity array reads back the shrunk range of its arc.\<close>

lemma red_arc_nth: "i < m \<Longrightarrow> red_upper ! i = red_upper_at i"
  by (simp add: red_pass_projs red_pass_def red_init_def red_fold_arc_in)

text \<open>The balance array is accumulated by every step: an arc adds its lower bound at its head and
      subtracts it at its tail.\<close>

definition bal_step_at :: "nat \<Rightarrow> nat \<Rightarrow> 'n" where
  "bal_step_at i v = (if snd_list ! i = v then lower ! i else 0)
                     - (if fst_list ! i = v then lower ! i else 0)"

lemma red_step_bal_nth:
  "\<lbrakk>v < length (rp_bal st); fst_list ! i < length (rp_bal st); snd_list ! i < length (rp_bal st)\<rbrakk>
   \<Longrightarrow> rp_bal (red_step i st) ! v = rp_bal st ! v + bal_step_at i v"
  by (cases st) (auto simp: red_step_def Let_def bal_step_at_def nth_list_update)

lemma red_fold_bal_nth:
  "\<lbrakk>v < length (rp_bal st);
    \<And> i. i \<in> set es \<Longrightarrow> fst_list ! i < length (rp_bal st);
    \<And> i. i \<in> set es \<Longrightarrow> snd_list ! i < length (rp_bal st)\<rbrakk>
   \<Longrightarrow> rp_bal (fold red_step es st) ! v
         = rp_bal st ! v + sum_list (map (\<lambda> i. bal_step_at i v) es)"
proof(induction es arbitrary: st)
  case (Cons a es)
  thus ?case
    using Cons.IH[of "red_step a st"]
    by (simp add: red_step_bal_nth)
qed simp

lemma red_bal_init_length: "length (rp_bal red_init) = length balance_list"
  by (simp add: red_init_def red_bal_init_def)

lemma red_balance_raw_length_raw: "length red_balance_raw = length balance_list"
  by (simp add: red_pass_projs red_pass_def red_bal_init_length)

lemma red_ok_fold:
  "snd (snd (snd (fold red_step es st))) = (snd (snd (snd st)) \<and> (\<forall> i \<in> set es. lower ! i \<le> upper ! i))"
  by (induction es arbitrary: st) (auto simp: red_step_def Let_def split: prod.splits)

lemma red_ok_arcs_iff: "red_ok_arcs = (\<forall> e < m. lower ! e \<le> upper ! e)"
  by (auto simp: red_pass_projs red_pass_def red_init_def red_ok_fold)

end

subsection \<open>The two networks\<close>

text \<open>The embedding \<^term>\<open>h\<close> of \<^locale>\<open>real_embedding\<close> reads the entries as
      reals. The assumptions are the shape of a parsed instance and nothing else: the lists have
      the announced lengths, every endpoint names a node, and \<^term>\<open>balance_list\<close> has its
      reserved slot \<open>0\<close>. No bound is restricted; \<^term>\<open>upper ! e < lower ! e\<close> is
      reported through \<^term>\<open>red_ok_arcs\<close>.

      \<^term>\<open>0 < m\<close> is needed because the reduced instance has the original arcs and must be a
      \<^locale>\<open>multigraph\<close>. An arc-less instance is settled by inspection before the reduction is
      reached; see \<open>DIMACS_Solver\<close>.\<close>

locale dimacs_lists_network =
  dimacs_lists where lower = "lower :: ('n::linordered_idom) list" +
  real_embedding where h = "h :: 'n \<Rightarrow> real"
  for lower h +
  assumes length_fst_list:     "length fst_list = m"
      and length_snd_list:     "length snd_list = m"
      and length_lower:        "length lower = m"
      and length_upper:        "length upper = m"
      and length_cost_list:    "length cost_list = m"
      and length_balance_list: "length balance_list = n"
      and arcs_nonempty:       "0 < m"
      and nodes_nonempty:      "0 < n"
      and fst_list_vertex:     "\<And> e. e < m \<Longrightarrow> fst_list ! e \<in> {1..<n}"
      and snd_list_vertex:     "\<And> e. e < m \<Longrightarrow> snd_list ! e \<in> {1..<n}"
begin

lemma h_neg_le_iff: "- h a \<le> h b \<longleftrightarrow> - a \<le> b"
  using h_le_iff[of "- a" b]
  by simp

text \<open>The capacity of a reduced arc. Edges outside \<open>{0..<m}\<close> get \<open>\<infinity>\<close>, since
      \<open>u_non_neg\<close> ranges over the whole edge type.\<close>

definition red_u :: "nat \<Rightarrow> ereal" where
  "red_u e = (if e < m \<and> 0 \<le> red_upper ! e then ereal (h (red_upper ! e)) else \<infinity>)"

lemma red_u_nonneg: "0 \<le> red_u e"
  by (auto simp: red_u_def zero_ereal_def)

lemma red_u_finite: "\<lbrakk>e < m; 0 \<le> red_upper ! e\<rbrakk> \<Longrightarrow> red_u e = ereal (h (red_upper ! e))"
and red_u_infty: "\<not> (e < m \<and> 0 \<le> red_upper ! e) \<Longrightarrow> red_u e = \<infinity>"
  by (auto simp: red_u_def)

text \<open>The endpoint assumptions place every scatter of the pass inside the balance array.\<close>

lemma red_balance_raw_length: "length red_balance_raw = n"
  using red_balance_raw_length_raw length_balance_list
  by simp

lemma red_bal_init_nth: "v \<in> {1..<n} \<Longrightarrow> red_bal_init ! v = balance_list ! v"
  and red_bal_init_sentinel: "red_bal_init ! 0 = 0"
  using nodes_nonempty length_balance_list
  by (auto simp: red_bal_init_def)

lemma arc_ends_less_n: "e < m \<Longrightarrow> fst_list ! e < n" "e < m \<Longrightarrow> snd_list ! e < n"
  using fst_list_vertex[of e] snd_list_vertex[of e]
  by auto

lemma red_balance_raw_nth:
  assumes "v < n"
  shows "red_balance_raw ! v = red_bal_init ! v + sum_list (map (\<lambda> i. bal_step_at i v) [0..<m])"
proof-
  have "rp_bal (fold red_step [0..<m] red_init) ! v
          = rp_bal red_init ! v + sum_list (map (\<lambda> i. bal_step_at i v) [0..<m])"
    by (intro red_fold_bal_nth) (auto simp: red_bal_init_length length_balance_list arc_ends_less_n assms)
  thus ?thesis
    by (simp add: red_pass_projs red_pass_def red_init_def)
qed

text \<open>No arc touches the sentinel slot \<open>0\<close>.\<close>

lemma bal_step_at_sentinel: "i < m \<Longrightarrow> bal_step_at i 0 = 0"
  using fst_list_vertex[of i] snd_list_vertex[of i]
  by (auto simp: bal_step_at_def)

lemma red_balance_raw_sentinel: "red_balance_raw ! 0 = 0"
  using red_balance_raw_nth[of 0] nodes_nonempty red_bal_init_sentinel
  by (simp add: interv_sum_list_conv_sum_set_nat bal_step_at_sentinel)

text \<open>The DIMACS instance only gets the \emph{spec} locale: its bounds carry no sign condition.\<close>

sublocale original_network: dimacs_spec
  where \<E>           = "{0..<m}"
    and fst          = "\<lambda> e. if e < m then fst_list ! e
                             else Product_Type.fst (prod_decode (e - m))"
    and snd          = "\<lambda> e. if e < m then snd_list ! e
                             else Product_Type.snd (prod_decode (e - m))"
    and create_edge  = "\<lambda> u v. m + prod_encode (u, v)"
    and \<u>           = "\<lambda> e. ereal (h (upper ! e))"
    and \<c>           = "\<lambda> e. h (cost_list ! e)"
    and l            = "\<lambda> e. ereal (h (lower ! e))"
    and b            = "\<lambda> v. h (balance_list ! v)"
  by unfold_locales

text \<open>The transformed instance gets all of \<^locale>\<open>cost_flow_network\<close>: its capacities are
      non-negative and its edge set is non-empty. Its arcs, endpoints and costs are the original
      ones; only the capacities differ.\<close>

sublocale reduced_network: cost_flow_network
  where \<E>           = "{0..<m}"
    and fst          = "\<lambda> e. if e < m then fst_list ! e
                             else Product_Type.fst (prod_decode (e - m))"
    and snd          = "\<lambda> e. if e < m then snd_list ! e
                             else Product_Type.snd (prod_decode (e - m))"
    and create_edge  = "\<lambda> u v. m + prod_encode (u, v)"
    and \<u>           = red_u
    and \<c>           = "\<lambda> e. h (cost_list ! e)"
  by (unfold_locales) (auto simp: arcs_nonempty red_u_nonneg)

text \<open>Both networks have the same arcs, so they share incidence, vertices and endpoints.\<close>

lemma orig_delta:
  "original_network.delta_plus v = {e. e < m \<and> fst_list ! e = v}"
  "original_network.delta_minus v = {e. e < m \<and> snd_list ! e = v}"
  by (auto simp: multigraph_spec.delta_plus_def multigraph_spec.delta_minus_def)

subsection \<open>Capacity incident at a vertex\<close>

text \<open>The reduced capacity leaving and entering a vertex, read off \<open>red_upper\<close>.\<close>

definition capout :: "nat \<Rightarrow> 'n" where
  "capout v = sum_list (map (\<lambda> e. if fst_list ! e = v then red_upper ! e else 0) [0..<m])"

definition capin :: "nat \<Rightarrow> 'n" where
  "capin v = sum_list (map (\<lambda> e. if snd_list ! e = v then red_upper ! e else 0) [0..<m])"

lemma red_upper_orig_nonneg: "e < m \<Longrightarrow> 0 \<le> red_upper ! e"
  by (simp add: red_arc_nth red_upper_at_def)

lemma sum_if_arc_end:
  "(\<Sum> e \<in> {0..<m}. if idx ! e = v then g e else 0) = (\<Sum> e \<in> {e. e < m \<and> idx ! e = v}. g e)"
  by (subst sum.inter_filter[symmetric]) (auto intro: sum.cong)

lemma capout_sum: "h (capout v) = (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. h (red_upper ! e))"
  and capin_sum: "h (capin v) = (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. h (red_upper ! e))"
  by (simp_all add: capout_def capin_def h_sum interv_sum_list_conv_sum_set_nat if_distrib[of h]
                    sum_if_arc_end)

subsection \<open>Capacity confines the net out-flow\<close>

definition net_out :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "net_out g v = (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. g e)
               - (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. g e)"

text \<open>This is the entire mathematical content of the range test \<open>bal_ok\<close> below: a net out-flow
      outside the incident capacity cannot be met.\<close>

lemma net_out_bounds:
  assumes "\<And> e. e < m \<Longrightarrow> 0 \<le> g e" "\<And> e. e < m \<Longrightarrow> g e \<le> h (red_upper ! e)"
  shows "net_out g v \<le> h (capout v)" "- h (capin v) \<le> net_out g v"
proof-
  have "(\<Sum> e \<in> {e. e < m \<and> idx ! e = v}. g e) \<le> (\<Sum> e \<in> {e. e < m \<and> idx ! e = v}. h (red_upper ! e))"
    "0 \<le> (\<Sum> e \<in> {e. e < m \<and> idx ! e = v}. g e)" for idx
    using assms
    by (auto intro!: sum_mono sum_nonneg)
  from this[of fst_list] this[of snd_list]
  show "net_out g v \<le> h (capout v)" "- h (capin v) \<le> net_out g v"
    by (auto simp: net_out_def capout_sum capin_sum)
qed

subsection \<open>Total capacity\<close>

text \<open>Every arc contributes its capacity to the out-capacity of its tail and the in-capacity of its
      head, so both sum to the total capacity of the instance.\<close>

definition total_cap :: "'n" where
  "total_cap = sum_list (map (\<lambda> e. red_upper ! e) [0..<m])"

lemma sum_cap_aux:
  "(\<And> e. e < m \<Longrightarrow> idx ! e \<in> {1..<n})
   \<Longrightarrow> (\<Sum> v \<in> {1..<n}. \<Sum> e \<in> {0..<m}. if idx ! e = v then red_upper ! e else 0) = total_cap"
  by (subst sum.swap) (auto simp: total_cap_def interv_sum_list_conv_sum_set_nat intro!: sum.cong)

lemma sum_capout: "(\<Sum> v \<in> {1..<n}. capout v) = total_cap"
  and sum_capin: "(\<Sum> v \<in> {1..<n}. capin v) = total_cap"
  using sum_cap_aux[of fst_list] sum_cap_aux[of snd_list] fst_list_vertex snd_list_vertex
  by (simp_all add: capout_def capin_def interv_sum_list_conv_sum_set_nat)

lemma capout_nonneg: "0 \<le> capout v" and capin_nonneg: "0 \<le> capin v"
  by (auto simp: capout_def capin_def red_upper_orig_nonneg intro!: sum_list_nonneg)

lemma capout_le_total_cap: "v \<in> {1..<n} \<Longrightarrow> capout v \<le> total_cap"
  and capin_le_total_cap: "v \<in> {1..<n} \<Longrightarrow> capin v \<le> total_cap"
  using member_le_sum[of v "{1..<n}" capout] member_le_sum[of v "{1..<n}" capin] sum_capout sum_capin
  by (simp_all add: capout_nonneg capin_nonneg)

subsection \<open>The balance array the reduction emits\<close>

text \<open>Slot \<open>0\<close> carries \<open>0\<close> and a real vertex its shifted balance. The flag adds two tests to the arc
      check: the range test at each vertex, and that the emitted balances total \<open>0\<close>.\<close>

definition red_balance_list :: "'n list" where
  "red_balance_list = red_balance_raw"

definition bal_ok :: bool where
  "bal_ok = (\<forall> v \<in> {1..<n}. - capin v \<le> red_balance_raw ! v \<and> red_balance_raw ! v \<le> capout v)"

definition sum_ok :: bool where
  "sum_ok = (sum_list red_balance_raw = 0)"

definition red_ok :: bool where
  "red_ok = (red_ok_arcs \<and> bal_ok \<and> sum_ok)"

lemma red_ok_arcsD: "red_ok \<Longrightarrow> red_ok_arcs"
  and bal_okD: "red_ok \<Longrightarrow> bal_ok"
  and sum_okD: "red_ok \<Longrightarrow> sum_ok"
  by (simp_all add: red_ok_def)

lemma red_balance_list_length: "length red_balance_list = n"
  by (simp add: red_balance_list_def red_balance_raw_length)

lemma red_balance_list_nth: "v < n \<Longrightarrow> red_balance_list ! v = red_balance_raw ! v"
  by (simp add: red_balance_list_def)

lemma total_cap_nonneg: "0 \<le> total_cap"
  by (auto simp: total_cap_def red_upper_orig_nonneg intro!: sum_list_nonneg)

text \<open>Every emitted balance lies within the total capacity, as the marshalling guard needs.\<close>

lemma red_balance_list_bounded:
  assumes "red_ok" "v < n"
  shows "- total_cap \<le> red_balance_list ! v \<and> red_balance_list ! v \<le> total_cap"
proof-
  have "v \<noteq> 0 \<Longrightarrow> - capin v \<le> red_balance_raw ! v \<and> red_balance_raw ! v \<le> capout v \<and> v \<in> {1..<n}"
    using assms
    by (auto simp: red_ok_def bal_ok_def)
  thus ?thesis
    using assms(2) total_cap_nonneg capout_le_total_cap[of v] capin_le_total_cap[of v]
    by (cases "v = 0") (auto simp: red_balance_list_nth red_balance_raw_sentinel)
qed

text \<open>A real node no arc touches has no incident capacity, so the range test forces its balance
      to \<open>0\<close>.\<close>

lemma red_balance_raw_isolated:
  assumes "bal_ok" "v \<in> {1..<n}" "original_network.delta_plus v = {}" "original_network.delta_minus v = {}"
  shows "red_balance_raw ! v = 0"
proof-
  have "capout v = 0" "capin v = 0"
    using assms(3,4)
    by (simp_all add: capout_def capin_def interv_sum_list_conv_sum_set_nat sum_if_arc_end
                      orig_delta[symmetric])
  thus ?thesis
    using assms(1,2)
    by (force simp: bal_ok_def)
qed

definition red_b :: "nat \<Rightarrow> real" where
  "red_b v = h (red_balance_list ! v)"

subsection \<open>The immediate infeasibility check\<close>

text \<open>(1) When the flag is down, some arc has an empty range.\<close>

lemma no_dimacs_flow_if_not_red_ok_arcs:
  assumes "\<not> red_ok_arcs"
  shows "\<not> original_network.is_dimacs_flow V f"
proof
  assume "original_network.is_dimacs_flow V f"
  hence "h (lower ! e) \<le> f e" "f e \<le> h (upper ! e)" if "e < m" for e
    using that
    by (auto elim!: original_network.is_dimacs_flowE)
  hence "h (lower ! e) \<le> h (upper ! e)" if "e < m" for e
    using that
    by (blast intro: order_trans)
  thus False
    using assms
    by (auto simp: red_ok_arcs_iff)
qed

lemma no_dimacs_Opt_if_not_red_ok_arcs:
  "\<not> red_ok_arcs \<Longrightarrow> \<not> original_network.is_dimacs_Opt V f"
  using no_dimacs_flow_if_not_red_ok_arcs
  by (auto elim!: original_network.is_dimacs_OptE)

subsection \<open>The emitted balance of a vertex\<close>

lemma bal_arc_part:
  "sum_list (map (\<lambda> i. bal_step_at i v) [0..<m])
     = (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. lower ! e)
       - (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. lower ! e)"
  by (simp add: interv_sum_list_conv_sum_set_nat bal_step_at_def sum_subtractf sum_if_arc_end)

lemma red_balance_raw_value:
  "v \<in> {1..<n} \<Longrightarrow> red_balance_raw ! v
     = balance_list ! v + (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. lower ! e)
       - (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. lower ! e)"
  by (simp add: red_balance_raw_nth bal_arc_part red_bal_init_nth)

subsection \<open>From a DIMACS flow to a reduced b-flow\<close>

text \<open>Every arc has both endpoints among the real nodes, so summing over the heads, or the tails,
      of all nodes counts each arc once.\<close>

lemma sum_over_arc_ends:
  assumes "\<And> e. e < m \<Longrightarrow> idx ! e \<in> {1..<n}"
  shows "(\<Sum> v \<in> {1..<n}. \<Sum> e \<in> {e. e < m \<and> idx ! e = v}. g e) = (\<Sum> e \<in> {0..<m}. g e)"
proof-
  have "(\<Union> v \<in> {1..<n}. {e. e < m \<and> idx ! e = v}) = {0..<m}"
    using assms
    by auto
  thus ?thesis
    by (subst sum.UNION_disjoint[symmetric]) auto
qed

text \<open>Hence the excesses sum to zero over the real nodes, and the emitted balances total the parsed
      ones.\<close>

lemma orig_ex_sum_zero: "(\<Sum> v \<in> {1..<n}. original_network.ex f v) = 0"
  using sum_over_arc_ends[OF fst_list_vertex, of f] sum_over_arc_ends[OF snd_list_vertex, of f]
  by (simp add: flow_network_spec.ex_def orig_delta sum_subtractf)

lemma red_balance_raw_sum_inner:
  "sum_list red_balance_raw = (\<Sum> v \<in> {1..<n}. red_balance_raw ! v)"
  using sum.atLeast_Suc_lessThan[of 0 n "(!) red_balance_raw"] red_balance_raw_sentinel nodes_nonempty
  by (simp add: sum_list_sum_nth red_balance_raw_length atLeast0LessThan)

lemma red_balance_raw_sum: "sum_list red_balance_raw = (\<Sum> v \<in> {1..<n}. balance_list ! v)"
  using sum_over_arc_ends[OF fst_list_vertex, of "\<lambda> e. lower ! e"]
        sum_over_arc_ends[OF snd_list_vertex, of "\<lambda> e. lower ! e"]
  by (simp add: red_balance_raw_sum_inner red_balance_raw_value sum.distrib sum_subtractf)

text \<open>\<^term>\<open>n = 0\<close> forces \<^term>\<open>m = 0\<close>, since an arc needs an endpoint in
      \<^term>\<open>{1..<n}\<close>.\<close>

lemma m_pos_n: "0 < m \<Longrightarrow> 1 < n"
  using fst_list_vertex[of 0]
  by auto

lemma red_V_subset: "original_network.\<V> \<subseteq> {1..<n}"
  using fst_list_vertex snd_list_vertex
  by (fastforce simp: dVs_def multigraph_spec.make_pair_def)

lemma red_b_raw:
  "v \<in> {1..<n} \<Longrightarrow> h (red_balance_raw ! v) = h (balance_list ! v)
     + (\<Sum> e \<in> {e. e < m \<and> snd_list ! e = v}. h (lower ! e))
     - (\<Sum> e \<in> {e. e < m \<and> fst_list ! e = v}. h (lower ! e))"
  by (simp add: red_balance_raw_value h_sum h_add)

lemma red_b_real: "v \<in> {1..<n} \<Longrightarrow> red_b v = h (red_balance_raw ! v)"
  by (simp add: red_b_def red_balance_list_nth)

text \<open>The forward map subtracts the lower bound on an arc.\<close>

definition red_of :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "red_of f e = (if e < m then f e - h (lower ! e) else 0)"

lemma red_of_orig: "e < m \<Longrightarrow> red_of f e = f e - h (lower ! e)"
  by (simp add: red_of_def)

lemma red_of_balance:
  "\<lbrakk>original_network.is_dimacs_flow {1..<n} f; v \<in> {1..<n}\<rbrakk>
   \<Longrightarrow> - reduced_network.ex (red_of f) v = red_b v"
  by (auto elim!: original_network.is_dimacs_flowE
           simp: red_b_real red_b_raw flow_network_spec.ex_def orig_delta red_of_orig sum_subtractf)

lemma red_upper_orig: "\<lbrakk>red_ok_arcs; e < m\<rbrakk> \<Longrightarrow> red_upper ! e = upper ! e - lower ! e"
  by (simp add: red_arc_nth red_ok_arcs_iff red_upper_at_def)

lemma red_u_orig: "\<lbrakk>red_ok_arcs; e < m\<rbrakk> \<Longrightarrow> red_u e = ereal (h (upper ! e) - h (lower ! e))"
  by (simp add: red_u_def red_upper_orig red_ok_arcs_iff)

text \<open>The constraints of a DIMACS flow, read on the list instance.\<close>

lemma dimacs_flow_bounds:
  assumes "original_network.is_dimacs_flow {1..<n} f"
  shows "e < m \<Longrightarrow> h (lower ! e) \<le> f e"
    and "e < m \<Longrightarrow> f e \<le> h (upper ! e)"
    and "v \<in> {1..<n} \<Longrightarrow> original_network.ex f v = - h (balance_list ! v)"
  using assms
  by (auto elim!: original_network.is_dimacs_flowE)

lemma red_of_nonneg: "\<lbrakk>original_network.is_dimacs_flow {1..<n} f; e < m\<rbrakk> \<Longrightarrow> 0 \<le> red_of f e"
  by (simp add: red_of_orig dimacs_flow_bounds(1))

lemma red_of_le_red_upper:
  "\<lbrakk>red_ok_arcs; original_network.is_dimacs_flow {1..<n} f; e < m\<rbrakk> \<Longrightarrow> red_of f e \<le> h (red_upper ! e)"
  by (simp add: red_of_orig red_upper_orig dimacs_flow_bounds(2))

lemma net_out_red_of:
  "v \<in> {1..<n} \<Longrightarrow> net_out (red_of f) v
     = h (red_balance_raw ! v) - (h (balance_list ! v) + original_network.ex f v)"
  by (simp add: net_out_def red_b_raw flow_network_spec.ex_def orig_delta red_of_orig sum_subtractf)

subsection \<open>The forward map is a reduced b-flow\<close>

lemma red_of_le_u:
  "\<lbrakk>red_ok_arcs; original_network.is_dimacs_flow {1..<n} f; e < m\<rbrakk> \<Longrightarrow> ereal (red_of f e) \<le> red_u e"
  by (simp add: red_u_orig red_of_orig dimacs_flow_bounds(2))

lemma red_of_isuflow:
  "\<lbrakk>red_ok_arcs; original_network.is_dimacs_flow {1..<n} f\<rbrakk> \<Longrightarrow> reduced_network.isuflow (red_of f)"
  by (auto simp: flow_network_spec.isuflow_def red_of_le_u red_of_nonneg)

lemma red_of_isbflow:
  "\<lbrakk>red_ok_arcs; original_network.is_dimacs_flow {1..<n} f\<rbrakk> \<Longrightarrow> reduced_network.isbflow (red_of f) red_b"
  using red_V_subset
  by (auto intro!: flow_network_spec.isbflowI red_of_isuflow red_of_balance)

subsection \<open>The inverse map is a DIMACS flow\<close>

text \<open>Undoing the substitution: \<open>orig_of g e = g e + l e\<close>.\<close>

definition orig_of :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real" where
  "orig_of g e = g e + h (lower ! e)"

lemma orig_of_ex:
  "\<lbrakk>v \<in> {1..<n}; - reduced_network.ex g v = red_b v\<rbrakk>
   \<Longrightarrow> - original_network.ex (orig_of g) v = h (balance_list ! v)"
  by (auto simp: red_b_real red_b_raw flow_network_spec.ex_def orig_delta orig_of_def sum.distrib)

text \<open>A real node outside \<^term>\<open>original_network.\<V>\<close> has balance \<open>0\<close> by the
      range test, so the b-flow condition holds at it for free.\<close>

lemma red_balance_outside:
  assumes "bal_ok" "v \<in> {1..<n}" "v \<notin> original_network.\<V>"
  shows "- reduced_network.ex g v = red_b v"
proof-
  have "original_network.delta_plus v = {}" "original_network.delta_minus v = {}"
    using assms(3) reduced_network.fst_E_V reduced_network.snd_E_V
    by (fastforce simp: multigraph_spec.delta_plus_def multigraph_spec.delta_minus_def)+
  thus ?thesis
    using assms red_balance_raw_isolated[of v]
    by (simp add: red_b_real flow_network_spec.ex_def)
qed

lemma bflow_facts:
  assumes "bal_ok" "reduced_network.isbflow g red_b"
  shows "e < m \<Longrightarrow> 0 \<le> g e"
    and "e < m \<Longrightarrow> ereal (g e) \<le> red_u e"
    and "v \<in> {1..<n} \<Longrightarrow> - reduced_network.ex g v = red_b v"
  using assms red_balance_outside[OF assms(1)]
  by (auto elim!: flow_network_spec.isbflowE simp: flow_network_spec.isuflow_def)

lemma orig_of_is_dimacs_flow:
  "\<lbrakk>red_ok; reduced_network.isbflow g red_b\<rbrakk> \<Longrightarrow> original_network.is_dimacs_flow {1..<n} (orig_of g)"
  using bflow_facts[of g] orig_of_ex[of _ g]
  by (auto intro!: original_network.is_dimacs_flowI simp: red_ok_def orig_of_def red_u_orig le_diff_eq)

subsection \<open>The objective moves by a constant\<close>

lemma C_orig: "original_network.\<C> f = (\<Sum> e \<in> {0..<m}. h (cost_list ! e) * f e)"
  by (simp add: cost_flow_spec.\<C>_def mult.commute)

lemma C_reduced_orig_arcs: "reduced_network.\<C> g = (\<Sum> e \<in> {0..<m}. h (cost_list ! e) * g e)"
  by (simp add: cost_flow_spec.\<C>_def mult.commute)

definition cost_K :: real where
  "cost_K = (\<Sum> e \<in> {0..<m}. h (cost_list ! e) * h (lower ! e))"

lemma C_red_of: "reduced_network.\<C> (red_of f) = original_network.\<C> f - cost_K"
  by (simp add: C_reduced_orig_arcs C_orig cost_K_def red_of_orig right_diff_distrib sum_subtractf)

lemma C_orig_of: "original_network.\<C> (orig_of g) = reduced_network.\<C> g + cost_K"
  by (simp add: C_reduced_orig_arcs C_orig cost_K_def orig_of_def distrib_left sum.distrib)

text \<open>On the original arcs, the recovered flow \<^term>\<open>\<lambda> e. h (orig_flow gs ! e)\<close> is
      \<^term>\<open>orig_of\<close> of the reduced flow, and validity and cost depend only on those arcs.\<close>

lemma orig_flow_nth: "e < m \<Longrightarrow> h (orig_flow gs ! e) = orig_of (\<lambda> e. h (gs ! e)) e"
  by (simp add: orig_flow_def orig_of_def h_add)

lemma orig_flow_as_orig_of:
  "original_network.is_dimacs_flow V (\<lambda> e. h (orig_flow gs ! e))
     = original_network.is_dimacs_flow V (orig_of (\<lambda> e. h (gs ! e)))"
  "original_network.\<C> (\<lambda> e. h (orig_flow gs ! e)) = original_network.\<C> (orig_of (\<lambda> e. h (gs ! e)))"
  by (simp_all add: original_network.is_dimacs_flow_def flow_network_spec.ex_def orig_delta orig_flow_nth
                    C_orig)

subsection \<open>The verdicts\<close>

text \<open>One statement per verdict the solver can return. The reduced flow arrives as a list
      \<^term>\<open>gs\<close> and is read as \<^term>\<open>\<lambda> e. h (gs ! e)\<close>; the recovered DIMACS
      flow is \<^term>\<open>\<lambda> e. h (orig_flow gs ! e)\<close>.

      (2) A solved reduced instance yields a DIMACS optimum, provided the immediate check passed.\<close>

lemma orig_flow_is_dimacs_Opt:
  assumes "red_ok" "reduced_network.is_Opt red_b (\<lambda> e. h (gs ! e))"
  shows "original_network.is_dimacs_Opt {1..<n} (\<lambda> e. h (orig_flow gs ! e))"
proof-
  have "reduced_network.\<C> (\<lambda> e. h (gs ! e)) + cost_K \<le> original_network.\<C> f"
    if "original_network.is_dimacs_flow {1..<n} f" for f
    using assms that red_of_isbflow[of f] C_red_of[of f]
    by (force elim!: cost_flow_spec.is_OptE simp: red_ok_def)
  thus ?thesis
    using assms orig_of_is_dimacs_flow[of "\<lambda> e. h (gs ! e)"]
    by (auto simp: original_network.is_dimacs_Opt_def orig_flow_as_orig_of C_orig_of
             elim!: cost_flow_spec.is_OptE)
qed

text \<open>No reduced arc is uncapacitated, so the solver's unboundedness verdict cannot fire.\<close>

lemma red_u_finite_in_range: "e < m \<Longrightarrow> red_u e \<noteq> \<infinity>"
  by (simp add: red_u_def red_upper_orig_nonneg)

lemma reduced_no_neg_infty_cycle:
  "\<not> has_neg_infty_cycle original_network.make_pair {0..<m} (\<lambda> e. h (cost_list ! e)) red_u"
  by (force simp: has_neg_infty_cycle_def closed_w_def red_u_finite_in_range neq_Nil_conv)

text \<open>(3) A reduced instance that the solver rejects, as unbounded or as infeasible, means the
      original was infeasible, provided the arc check passed: a DIMACS flow would map forward to a
      reduced b-flow.\<close>

lemma original_infeasible_if_reduced_fails:
  assumes "red_ok_arcs"
      and "has_neg_infty_cycle original_network.make_pair {0..<m} (\<lambda> e. h (cost_list ! e)) red_u
           \<or> (\<nexists> g. reduced_network.isbflow g red_b)"
  shows "\<not> original_network.is_dimacs_flow {1..<n} f"
  using assms red_of_isbflow[of f] reduced_no_neg_infty_cycle
  by blast

text \<open>(4) An out-of-range balance proves infeasibility, by \<open>net_out_bounds\<close>.\<close>

lemma no_dimacs_flow_if_not_bal_ok:
  assumes "red_ok_arcs" "\<not> bal_ok"
  shows "\<not> original_network.is_dimacs_flow {1..<n} f"
proof
  assume "original_network.is_dimacs_flow {1..<n} f"
  hence "- capin v \<le> red_balance_raw ! v \<and> red_balance_raw ! v \<le> capout v" if "v \<in> {1..<n}" for v
    using assms(1) that net_out_bounds[of "red_of f" v]
    by (simp add: red_of_nonneg red_of_le_red_upper net_out_red_of dimacs_flow_bounds(3) h_neg_le_iff)
  thus False
    using assms(2)
    by (simp add: bal_ok_def)
qed

text \<open>(5) Balances that do not total \<open>0\<close> prove infeasibility: what a flow leaves at one vertex it
      enters at another.\<close>

lemma no_dimacs_flow_if_not_sum_ok:
  assumes "\<not> sum_ok"
  shows "\<not> original_network.is_dimacs_flow {1..<n} f"
proof
  assume "original_network.is_dimacs_flow {1..<n} f"
  hence "h (\<Sum> v \<in> {1..<n}. balance_list ! v) = 0"
    using orig_ex_sum_zero[of f]
    by (simp add: h_sum dimacs_flow_bounds(3) sum_negf)
  thus False
    using assms
    by (simp add: sum_ok_def red_balance_raw_sum)
qed

text \<open>All three immediate checks together: failing \<^const>\<open>red_ok\<close> means there is no
      DIMACS flow.\<close>

lemma no_dimacs_flow_if_not_red_ok:
  "\<not> red_ok \<Longrightarrow> \<not> original_network.is_dimacs_flow {1..<n} f"
  using no_dimacs_flow_if_not_red_ok_arcs no_dimacs_flow_if_not_bal_ok no_dimacs_flow_if_not_sum_ok
  by (auto simp: red_ok_def)

lemma no_dimacs_Opt_if_not_red_ok:
  "\<not> red_ok \<Longrightarrow> \<not> original_network.is_dimacs_Opt {1..<n} f"
  using no_dimacs_flow_if_not_red_ok
  by (auto elim!: original_network.is_dimacs_OptE)

end

end

