
theory Network_Simplex_Initial_Basis_Selector
  imports Network_Simplex_Initial_Basis_Arb
begin

provenance ai


section \<open>A concrete entering-edge selector: candidate-list block search\<close>

text \<open>We implement the @{locale edge_selector} ADT concretely, following the improved block-search
      pseudocode.  The selector state is a record holding a wrap-around \<^emph>\<open>bookmark\<close> into the
      augmented arc set @{term \<open>{0..<m + Kart}\<close>} (an arc is its own index, so
      \<open>arc_array ! i = i\<close>) and a \<^emph>\<open>candidate list\<close> of shortlisted edge ids.  A
      single call to the selection function sees the potentials @{term \<pi>} and the edge-tag array @{term es} as
      constants; all persistence lives in the record, threaded as the ADT's selector value.

      The rule proceeds in two phases.  \<^bold>\<open>Minor iteration\<close> (@{text scan_best}) re-prices the
      cached candidate list against the current @{term \<pi>}/@{term es}, drops the edges that are no longer
      eligible, and returns the most-violating survivor --- so a returned edge is always eligible
      \<^emph>\<open>now\<close>, which is all the ADT demands.  \<^bold>\<open>Major iteration\<close>
      (@{text scan}) is reached only when the cache is exhausted; it sweeps the arc array in blocks from the
      bookmark, refilling the cache (up to @{term max_candidates}) and simultaneously tracking the best edge to
      return, with a ceiling bailout (list full) and a floor bailout (enough fuel, checked at block boundaries). If
      a full sweep of all @{term \<open>m + Kart\<close>} arcs inserts nothing, no eligible edge exists and the
      selector returns @{term None} --- discharging the ADT's @{term None} contract, from which the outer loop
      later derives optimality.\<close>

locale \<^marker>\<open>provenance ai_human\<close> initial_basis_selector =
  initial_basis_correct where capacity_list = capacity_list and h = h
  for capacity_list :: "('n :: linordered_idom) list" and h :: "'n \<Rightarrow> real" +
  assumes block_size_pos:     "0 < block_size"
      and min_candidates_pos: "0 < min_candidates"
      and min_le_max:         "min_candidates \<le> max_candidates"
begin

text \<open>The number of augmented arcs.\<close>


subsection \<open>Reduced cost and eligibility in the big-M descriptor world\<close>

text \<open>The cost of an edge as a big-M descriptor: an ordinary cost for a real edge, and the symbolic
      @{term bigM} (tag \<open>+1\<close>) for an artificial edge, so that
      @{term \<open>pval_abstract bigM (cost_pval e) = cost_all ! e\<close>}.\<close>


text \<open>The reduced cost @{term \<open>\<c> e + \<pi> (fst e) - \<pi> (snd e)\<close>} assembled in the
      descriptor type; the potentials are looked up in the list-backed potential array.  Its abstract value is
      faithful to the real reduced cost under the network-simplex guard, via @{thm pot_plus_faithful} /
      @{thm pot_minus_faithful}.\<close>


definition rc_val :: "(mtag \<times> 'n) list \<Rightarrow> nat \<Rightarrow> real" where
  "rc_val \<pi> e = pval_abstract bigM (red_cost \<pi> e)"

text \<open>\<^bold>\<open>Faithfulness of the M-free sign tests.\<close>  The executable eligibility test uses the
      M-free \<open>pval_neg\<close> / \<open>pval_pos\<close>; they agree with the true sign of the abstract
      reduced cost @{term \<open>pval_abstract bigM g\<close>} whenever @{term g} satisfies the reduced-cost
      invariant @{const rc_invar} --- its ordinary part is bounded by
      @{term \<open>3 * sum_list (map abs cost_list)\<close>}, comfortably below @{term bigM}, so the big-M
      coefficient alone fixes the sign.  This is where the value of @{term bigM} does its work: in the proof, not
      in the code.\<close>

lemma pval_neg_abstract: "rc_invar g \<Longrightarrow> pval_neg g \<longleftrightarrow> pval_abstract bigM g < 0"
  using sabs_nonneg by (drule_tac h_rc_bound)
    (cases "fst g"; simp_all add: pval_neg_def pval_abstract_def bigM_def abs_le_iff; linarith)

lemma pval_pos_abstract: "rc_invar g \<Longrightarrow> pval_pos g \<longleftrightarrow> 0 < pval_abstract bigM g"
  using sabs_nonneg by (drule_tac h_rc_bound)
    (cases "fst g"; simp_all add: pval_pos_def pval_abstract_def bigM_def abs_le_iff; linarith)

text \<open>An @{term InL} edge is eligible when its reduced cost is negative, an @{term InU} edge when it is
      positive; tree edges are never eligible.  Both tests are the \<^emph>\<open>M-free\<close>
      \<open>pval_neg\<close> / \<open>pval_pos\<close>.  The violation is the magnitude of the reduced cost, and
      larger violation makes a better pivot (compared M-free by \<open>viol_gt\<close>).\<close>



definition gviol :: "mtag \<times> 'n \<Rightarrow> real" where
  "gviol g = \<bar>pval_abstract bigM g\<bar>"

text \<open>\<^bold>\<open>Compute-once evaluation\<close> of an edge.  A single pass reads the tag once and builds
      the reduced cost @{term \<open>red_cost \<pi> e\<close>} once, returning what the two loops need: the
      eligibility flag (via the \<^emph>\<open>M-free\<close> \<open>pval_neg\<close> / \<open>pval_pos\<close>),
      the @{term in_U} flag, and the reduced-cost descriptor @{term g} itself.
      \<^emph>\<open>No abstract value and no @{term bigM} multiply is ever formed\<close> --- the violation
      ordering is likewise done M-free by \<open>viol_gt\<close> on the descriptors.  It is the executable
      counterpart of @{const eligible} / @{const ent_in_U} / @{const red_cost}, tied to them by
      @{text evaluate_eq}.\<close>


text \<open>@{const evaluate} short-circuits: for a self-loop it returns @{term False}
      \<^emph>\<open>without\<close> pricing the edge (no @{const red_cost}), so its three projections are: the
      eligibility flag and the @{const ent_in_U} flag always, but the reduced-cost descriptor only on the
      non-self-loop (equivalently, eligible) branch --- which is the only branch where the loop ever reads
      it.\<close>

lemma evaluate_elig: "fst (evaluate es \<pi> e) = eligible es \<pi> e"
  by (simp add: evaluate_def eligible_def red_cost_def Let_def split: edge_tag.split)

lemma evaluate_inU: "fst (snd (evaluate es \<pi> e)) = ent_in_U es e"
  by (simp add: evaluate_def ent_in_U_def Let_def)

lemma evaluate_red: "eligible es \<pi> e \<Longrightarrow> snd (snd (evaluate es \<pi> e)) = red_cost \<pi> e"
  by (simp add: eligible_def evaluate_def red_cost_def Let_def)

subsection \<open>Selecting the most-violating edge\<close>

text \<open>Offer a candidate to the flat running best: take it if nothing is held yet
      (@{term \<open>\<not> found\<close>}) or it is strictly more violating, otherwise keep the incumbent.
      Comparison is \<^emph>\<open>M-free\<close> via \<open>viol_gt\<close> on the reduced-cost descriptors
      (bigger big-M coefficient first, then bigger ordinary part); no reduced cost is abstracted through
      @{term bigM}, and \<^emph>\<open>no option is formed\<close>.\<close>


text \<open>Two array lemmas backing the \<^emph>\<open>swap-with-last\<close> deletion of the minor iteration: the
      live prefix can only shrink (subset), and a still-live element survives the deletion of a
      \<^emph>\<open>different\<close> one.  No distinctness is needed.\<close>

lemma set_take_img: "nn \<le> length xs \<Longrightarrow> set (take nn xs) = (\<lambda>k. xs ! k) ` {0..<nn}"
  by (simp add: nth_image)

lemma set_take_swapdel_subset:
  "\<lbrakk>i < len; len \<le> length a\<rbrakk>
     \<Longrightarrow> set (take (len-1) (a[i := a ! (len-1)])) \<subseteq> set (take len a)"
  by (auto simp: set_take_img nth_list_update)

lemma mem_survives_swapdel:
  assumes "i < len" "len \<le> length a" "e \<in> set (take len a)" "e \<noteq> a ! i"
  shows "e \<in> set (take (len-1) (a[i := a ! (len-1)]))"
proof-
  obtain j where "j < len" "e = a ! j" using assms(2,3) by (auto simp: set_take_img)
  then show ?thesis using assms(1,2,4) by (cases "j = len - 1"; cases "i = len - 1")
      (auto simp: set_take_img nth_list_update intro: rev_image_eqI[of i] rev_image_eqI[of j])
qed

text \<open>And the lemma backing the \<^emph>\<open>push-at-pointer\<close> insertion of the major iteration.\<close>

lemma take_push_eq: "len < length a \<Longrightarrow> take (Suc len) (a[len := c]) = take len a @ [c]"
  by (simp add: take_Suc_conv_app_nth)

lemma set_take_push:
  "len < length a \<Longrightarrow> set (take (Suc len) (a[len := c])) = insert c (set (take len a))"
  by (simp add: take_push_eq)

text \<open>The running-best invariant @{term bok}: while the \<^emph>\<open>found\<close> flag is set, the stored
      edge is eligible, its @{term in_U} flag and reduced-cost descriptor are the ones @{const evaluate} would
      compute, and the edge lies in the current live prefix.\<close>


lemma bok_no_best[simp]: "bok es pt no_best a len"
  by (simp add: bok_def no_best_def)

lemma bok_better_keep:
  "\<lbrakk>bok es pt best a len; eligible es pt e; e \<in> set (take len a)\<rbrakk> \<Longrightarrow>
    bok es pt (better best (e, ent_in_U es e, red_cost pt e)) a len"
  by (cases best) (auto simp: bok_def)

lemma bok_swapdel:
  "\<lbrakk>bok es pt best a len; i < len; len \<le> length a; \<not> eligible es pt (a ! i)\<rbrakk> \<Longrightarrow>
    bok es pt best (a[i := a ! (len - 1)]) (len - 1)"
  by (cases best) (auto simp: bok_def intro: mem_survives_swapdel[simplified])

lemma fst_better[simp]: "fst (better best c)"
  by (cases best; cases c) auto

text \<open>\<^bold>\<open>Minor iteration\<close>, in a single pass over the live prefix
      @{term \<open>take len a\<close>} of the backing array @{term a}.  We walk an index @{term i} (against the
      pointer @{term len}, never against @{term \<open>length a\<close>}); a still-eligible entry is kept, priced
      once, offered to the running best, and @{term i} advances; an ineligible (dud) entry is removed by
      \<^emph>\<open>swap-with-last\<close> --- write the last live entry @{term \<open>a ! (len - 1)\<close>} into
      slot @{term i} and drop the pointer, \<^emph>\<open>without\<close> advancing @{term i} --- i.e. the
      \<open>O(1)\<close> in-place deletion @{text \<open>a[i] := a[len - 1]; len := len - 1\<close>}.  The backing
      list keeps its length (the vacated slot @{term \<open>len - 1\<close>} is just left behind the pointer); the
      result is the same array with the pointer moved and the most-violating survivor.\<close>

lemma scan_cache_step: "\<not> len \<le> i \<Longrightarrow> scan_cache es pt i a len best =
    (if eligible es pt (a ! i) then scan_cache es pt (Suc i) a len
     (better best (a ! i, ent_in_U es (a ! i), red_cost pt (a ! i)))
     else scan_cache es pt i (a[i := a ! (len - 1)]) (len - 1) best)"
  by (subst scan_cache.simps)
    (simp add: Let_def split_beta evaluate_elig evaluate_inU evaluate_red del: scan_cache.simps cong: if_cong)

text \<open>\<^bold>\<open>Specification of the minor iteration.\<close>  From any live prefix, the single pass
      returns an array of unchanged capacity whose new live prefix is no longer than and contained in the old one,
      the running best stays @{const bok} (so a \<^emph>\<open>found\<close> result is a genuine eligible edge of
      the prefix), the \<^emph>\<open>found\<close> flag is monotone, and --- crucially for the @{term None}
      certificate --- if the pass finds nothing then it has emptied the prefix (@{term \<open>rl = i\<close>}, i.e.
      @{term \<open>rl = 0\<close>} from the start pointer @{term \<open>i = 0\<close>}).  Distinctness plays no
      role.\<close>

lemma scan_cache_spec:
  "\<lbrakk>i \<le> len; len \<le> length a; bok es pt best a len\<rbrakk> \<Longrightarrow>
   (case scan_cache es pt i a len best of (ra,rl,rb) \<Rightarrow>
      length ra = length a \<and> rl \<le> len \<and> set (take rl ra) \<subseteq> set (take len a)
      \<and> bok es pt rb ra rl \<and> (fst best \<longrightarrow> fst rb)
        \<and> (\<not> fst rb \<longrightarrow> rl = i))"
proof(induction "len - i" arbitrary: i a len best rule: less_induct)
  case less
  show ?case
  proof(cases "len \<le> i")
    case False
    show ?thesis
    proof(cases "eligible es pt (a ! i)")
      case True
      let ?b = "better best (a ! i, ent_in_U es (a ! i), red_cost pt (a ! i))"
      from less.prems False True have "bok es pt ?b a len"
        by (intro bok_better_keep) (auto simp: set_take_img)
      then show ?thesis using less.hyps[of len "Suc i" a ?b] less.prems False True
        by (auto simp: scan_cache_step diff_less_mono2 simp del: scan_cache.simps split: prod.splits)
    next
      case False
      have "i \<le> len - 1" "len - 1 \<le> length a" using \<open>\<not> len \<le> i\<close> less.prems(2) by simp_all
      with False less.prems \<open>\<not> len \<le> i\<close> show ?thesis
        using less.hyps[of "len - 1" i "a[i := a ! (len - 1)]" best] bok_swapdel[of es pt best a len i]
          set_take_swapdel_subset[of i len a]
        by (auto simp: scan_cache_step diff_less_mono2 simp del: scan_cache.simps split: prod.splits)
    qed
  qed (use less.prems in simp)
qed

subsection \<open>Major iteration: block search over the arc array\<close>

text \<open>One straight sweep with three counters: @{term fuel} arcs remain to be scanned overall, @{term bpos}
      arcs remain in the current block (\<open>0\<close> marks a block boundary), and @{term len} tracks
      @{term \<open>length cand\<close>} in \<open>O(1)\<close> so the ceiling/floor tests never re-measure the
      list. We refill up to @{term max_candidates} (ceiling) and stop pulling new blocks once the pointer reaches
      @{term min_candidates} (floor, checked only at boundaries).  An inserted edge is
      \<^emph>\<open>pushed at the pointer\<close> --- @{text \<open>a[len] := cur; len := len + 1\<close>}, the
      @{const list_update} @{term \<open>a[len := cur]\<close>} --- overwriting the stale slot rather than growing
      the list, so the backing array keeps its capacity and nothing is allocated.  The bookmark advances cyclically
      by a \<^emph>\<open>conditional reset\<close> @{term \<open>if cur + 1 = mc then 0 else cur + 1\<close>}
      rather than a modulo --- a compare instead of a division --- which coincides with
      @{term \<open>(cur + 1) mod mc\<close>} on every state reached from a legal bookmark
      @{term \<open>cur < mc\<close>}.  The arc count @{term mc} (always @{term marc}) is threaded as a
      \<^emph>\<open>fixed loop parameter\<close>, so the wrap bound is read from a register each iteration rather
      than re-deriving the locale constant @{term marc} (hence never re-running @{term build_tree}). The best edge
      seen is accumulated for immediate return; termination is by the strictly decreasing @{term fuel}.\<close>


text \<open>Cyclic-sweep arithmetic for the block bookmark: the conditional wrap coincides with
      @{term \<open>(cur + 1) mod mc\<close>} and stays in range, and a full sweep of @{term mc} consecutive
      residues from any start covers every arc.\<close>

lemma wrap_eq: "cur < (mc::nat) \<Longrightarrow> (if cur + 1 = mc then 0 else cur + 1) = (cur + 1) mod mc"
  by (cases "cur + 1 = mc") auto

lemma wrap_lt: "\<lbrakk>0 < (mc::nat); cur < mc\<rbrakk> \<Longrightarrow> (if cur + 1 = mc then 0 else cur + 1) < mc"
  by auto

lemma wrap_shift:
  "cur < (mc::nat) \<Longrightarrow> ((if cur + 1 = mc then 0 else cur + 1) + t) mod mc = (cur + Suc t) mod mc"
  by (subst wrap_eq) (simp_all add: mod_add_left_eq)

lemma cyc_cover:
  "\<lbrakk>0 < (mc::nat); cur < mc; e < mc\<rbrakk> \<Longrightarrow> \<exists>t<mc. (cur + t) mod mc = e"
  by (rule exI[of _ "(e + mc - cur) mod mc"]) (simp add: mod_add_right_eq)

text \<open>One step of the major iteration, with the evaluation of the bookmark arc resolved.  Below, the
      major iteration is only unfolded through this lemma.\<close>

lemma scan_unfold: "scan es pt mc fuel bpos cur a len best =
    (if fuel = 0 \<or> max_candidates \<le> len \<or> (bpos = 0 \<and> min_candidates \<le> len)
     then (cur, a, len, best)
     else if eligible es pt cur
       then scan es pt mc (fuel - 1) ((if bpos = 0 then block_size else bpos) - 1)
         (if cur + 1 = mc then 0 else cur + 1) (a[len := cur]) (Suc len)
           (better best (cur, ent_in_U es cur, red_cost pt cur))
       else scan es pt mc (fuel - 1) ((if bpos = 0 then block_size else bpos) - 1)
         (if cur + 1 = mc then 0 else cur + 1) a len best)"
  by (subst scan.simps)
    (simp add: Let_def split_beta evaluate_elig evaluate_inU evaluate_red del: scan.simps cong: if_cong)

declare scan.simps[simp del]

lemma scan_fuel0: "scan es pt mc 0 bpos cur a len best = (cur, a, len, best)"
  by (subst scan_unfold) simp

text \<open>The \<^emph>\<open>found\<close> flag of the major iteration is monotone.\<close>

lemma scan_found_mono:
  "\<lbrakk>scan es pt mc fuel bpos cur a len best = (cur2,a2,len2,best2); fst best\<rbrakk>
     \<Longrightarrow> fst best2"
proof(induction fuel arbitrary: bpos cur a len best)
  case (Suc fuel)
  then show ?case using Suc.prems(1)[unfolded scan_unfold[of es pt mc "Suc fuel"]]
    by (auto split: if_splits intro: Suc.IH)
qed (simp add: scan_fuel0)

text \<open>\<^bold>\<open>The @{term None} certificate of the major iteration.\<close>  If the sweep returns with
      nothing found, then it consumed its whole fuel with no eligible arc \<^emph>\<open>anywhere\<close> on the
      cyclic run --- the precondition @{term \<open>\<not> fst best \<longrightarrow> len = 0\<close>} (no insert
      without a find) rules out the ceiling/floor bail-outs.\<close>

lemma scan_none:
  "\<lbrakk>scan es pt mc fuel bpos cur a len best = (cur2,a2,len2,best2); \<not> fst best2;
            \<not> fst best \<longrightarrow> len = 0;
    0 < min_candidates; 0 < max_candidates; cur < mc; 0 < mc\<rbrakk> \<Longrightarrow>
    \<forall>t<fuel. \<not> eligible es pt ((cur + t) mod mc)"
proof(induction fuel arbitrary: bpos cur a len best)
  case (Suc fuel)
  then have "\<not> fst best" by (auto dest: scan_found_mono)
  with Suc.prems have step: "\<not> eligible es pt cur
                               \<and> scan es pt mc fuel ((if bpos = 0 then block_size else bpos) - 1)
      (if cur + 1 = mc then 0 else cur + 1) a len best = (cur2, a2, len2, best2)"
    using Suc.prems(1)[unfolded scan_unfold[of es pt mc "Suc fuel"]] by (auto split: if_splits dest: scan_found_mono)
  have "\<forall>t<fuel. \<not> eligible es pt (((if cur + 1 = mc then 0 else cur + 1) + t) mod mc)"
    by (rule Suc.IH) (use step Suc.prems wrap_lt[of mc cur] in auto)
  with step Suc.prems show ?case using wrap_shift[of cur mc] by (auto simp: less_Suc_eq_0_disj)
qed simp

text \<open>\<^bold>\<open>The insertion-side invariants of the major iteration.\<close>  The candidate array keeps
      its capacity, the pointer never exceeds it, the bookmark stays in range, every candidate is a real arc, and
      the running best stays @{const bok}.\<close>

lemma bok_push: "\<lbrakk>bok es pt best a len; len < length a; eligible es pt c\<rbrakk> \<Longrightarrow>
    bok es pt (better best (c, ent_in_U es c, red_cost pt c)) (a[len := c]) (Suc len)"
  by (cases best) (auto simp: bok_def set_take_push)

lemma scan_some_spec:
  "\<lbrakk>scan es pt mc fuel bpos cur a len best = (cur2,a2,len2,best2); 0 < mc; cur < mc; length a = max_candidates;
    len \<le> max_candidates; set (take len a) \<subseteq> {0..<mc}; bok es pt best a len;
      0 < max_candidates\<rbrakk> \<Longrightarrow>
    length a2 = max_candidates \<and> len2 \<le> max_candidates \<and> cur2 < mc
      \<and> set (take len2 a2) \<subseteq> {0..<mc}
    \<and> bok es pt best2 a2 len2"
proof(induction fuel arbitrary: bpos cur a len best)
  case (Suc fuel)
  let ?bp = "(if bpos = 0 then block_size else bpos) - 1" and ?c = "if cur + 1 = mc then 0 else cur + 1"
  show ?case
  proof(cases "max_candidates \<le> len \<or> (bpos = 0 \<and> min_candidates \<le> len)")
    case False
    note eq = Suc.prems(1)[unfolded scan_unfold[of es pt mc "Suc fuel"]]
    show ?thesis
    proof(cases "eligible es pt cur")
      case True
      with False eq Suc.prems show ?thesis
        using Suc.IH[of ?bp ?c "a[len := cur]" "Suc len" "better best (cur, ent_in_U es cur, red_cost pt cur)"]
          wrap_lt[of mc cur] bok_push[of es pt best a len cur]
        by (auto simp: set_take_push split: if_splits)
    qed (use False eq Suc.prems Suc.IH[of ?bp ?c a len best] wrap_lt[of mc cur] in
         \<open>auto split: if_splits\<close>)
  qed (use Suc.prems in \<open>simp add: scan_unfold[of es pt mc "Suc fuel"]\<close>)
qed (simp add: scan_fuel0)

text \<open>\<^bold>\<open>From the M-free eligibility test to the true reduced-cost sign.\<close>  Under the
      reduced-cost invariant these turn the executable @{const eligible} test into the sign of the abstract reduced
      cost @{term \<open>pval_abstract bigM (red_cost pt e)\<close>}.\<close>

lemma elig_L: "\<lbrakk>rc_invar (red_cost pt e); nth es e = InL\<rbrakk> \<Longrightarrow>
    eligible es pt e = (fst_all ! e \<noteq> snd_all ! e \<and> pval_abstract bigM (red_cost pt e) < 0)"
  by (simp add: eligible_def pval_neg_abstract)

lemma elig_U: "\<lbrakk>rc_invar (red_cost pt e); nth es e = InU\<rbrakk> \<Longrightarrow>
    eligible es pt e = (fst_all ! e \<noteq> snd_all ! e \<and> 0 < pval_abstract bigM (red_cost pt e))"
  by (simp add: eligible_def pval_pos_abstract)

text \<open>A found eligible edge is guaranteed a \<^emph>\<open>non-self-loop\<close> (the self-loop skip added to
      @{const eligible}) on top of the sign of its reduced cost.\<close>

lemma sign_helper:
  "\<lbrakk>rc_invar (red_cost pt e); eligible es pt e; in_U = ent_in_U es e\<rbrakk> \<Longrightarrow>
    fst_all ! e \<noteq> snd_all ! e \<and> (if in_U then nth es e = InU \<and> 0 < pval_abstract bigM (red_cost pt e)
      else nth es e = InL \<and> pval_abstract bigM (red_cost pt e) < 0)"
  by (cases "nth es e") (auto simp: eligible_def ent_in_U_def pval_neg_abstract pval_pos_abstract)

declare scan.simps[simp]


subsection \<open>The selection function and the selector invariant\<close>

text \<open>Try the cache first; on a hit keep the pruned survivors (bookmark unchanged).  Otherwise run a
      major iteration from the bookmark: return its best, or @{term None} if the whole arc set was
      swept without finding an eligible edge.\<close>


text \<open>The selector invariant records only structural facts about the state --- it cannot mention
      @{term \<pi>} (the ADT invariant sees the selector alone), which is exactly why the minor iteration
      re-validates every cached edge before returning it.  The range bound is stated about the
      \<^emph>\<open>live prefix\<close> @{term \<open>take (sel_len sel) (sel_arr sel)\<close>} (its members are
      genuine arcs, so a returned edge lies in @{term \<E>}); the stale tail beyond the pointer is unconstrained.
      The fixed capacity is pinned by @{term \<open>length (sel_arr sel) = max_candidates\<close>}, which keeps the
      pointer a legal index for insertion.  Candidate-list \<^emph>\<open>distinctness\<close> is deliberately
      \<^emph>\<open>not\<close> asserted: the ADT axioms never need it (the loop treats
      \<open>sel_invar_impl\<close> abstractly), so requiring it would be pure proof cost.\<close>



lemma sel_invar_init_sel: "sel_invar_impl init_sel"
  by (simp add: sel_invar_impl_def init_sel_def)


subsection \<open>Pricing bridge: reduced-cost faithfulness from the good-potential invariant\<close>

text \<open>The remaining ADT obligation.  The two selector theorems above are stated with the abstract reduced
      cost @{term \<open>pval_abstract bigM (red_cost \<pi> e)\<close>} and a hypothesis
      @{term \<open>rc_invar (red_cost \<pi> e)\<close>}.  Both are discharged from the good-potential invariant
      that the network-simplex loop maintains: every stored potential value is a signed cost sum over augmented
      edges touching the artificial root @{term vcount} at most once (the descriptor-level
      \<open>good_pot_val_c\<close>, the concrete instance of @{term good_pot_val}), and the root's own potential
      is zero.  Under it the coefficient of every potential lies in @{term \<open>{- 1, 0, 1}\<close>} and its
      ordinary part is bounded by @{term \<open>sum_list (map abs cost_list)\<close>}; the clamped tag arithmetic
      is then \<^emph>\<open>faithful\<close> because the reduced-cost coefficient never leaves
      @{term \<open>{- 2 .. 2}\<close>} (an artificial edge always has the coefficient-zero root as one endpoint,
      ruling out \<open>\<plusminus> 3\<close>).\<close>

lemma pval_plus_faithful_coeff:
  "\<lbrakk>- 2 \<le> of_mtag (fst p) + of_mtag (fst g);
            of_mtag (fst p) + of_mtag (fst g) \<le> 2\<rbrakk> \<Longrightarrow>
    pval_abstract bigM (pval_plus p g) = pval_abstract bigM p + pval_abstract bigM g"
  unfolding pval_abstract_def pval_plus_def tag_add_def by (simp add: of_mtag_mtag_of algebra_simps h_add)

lemma pval_minus_faithful_coeff:
  "\<lbrakk>- 2 \<le> of_mtag (fst p) - of_mtag (fst g);
            of_mtag (fst p) - of_mtag (fst g) \<le> 2\<rbrakk> \<Longrightarrow>
    pval_abstract bigM (pval_minus p g) = pval_abstract bigM p - pval_abstract bigM g"
  unfolding pval_abstract_def pval_minus_def tag_sub_def by (simp add: of_mtag_mtag_of algebra_simps)

lemma pval_plus_coeff:
  "\<lbrakk>- 2 \<le> of_mtag (fst p) + of_mtag (fst g);
            of_mtag (fst p) + of_mtag (fst g) \<le> 2\<rbrakk> \<Longrightarrow>
    of_mtag (fst (pval_plus p g)) = of_mtag (fst p) + of_mtag (fst g)"
  unfolding pval_plus_def tag_add_def by (simp add: of_mtag_mtag_of)

lemma pval_minus_coeff:
  "\<lbrakk>- 2 \<le> of_mtag (fst p) - of_mtag (fst g);
            of_mtag (fst p) - of_mtag (fst g) \<le> 2\<rbrakk> \<Longrightarrow>
    of_mtag (fst (pval_minus p g)) = of_mtag (fst p) - of_mtag (fst g)"
  unfolding pval_minus_def tag_sub_def by (simp add: of_mtag_mtag_of)

definition good_pot_val_c :: "mtag \<times> 'n \<Rightarrow> bool" where
  "good_pot_val_c p = (\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart}
     \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1
     \<and> pval_abstract bigM p = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e))"

lemma gpv_coeff:
  assumes "good_pot_val_c p" "pv_invar p"
  shows "of_mtag (fst p) \<in> {- 1, 0, 1} \<and> \<bar>snd p\<bar> \<le> sum_list (map abs cost_list)"
proof-
  obtain A D where AD: "A \<subseteq> {0..<m+Kart}" "D \<subseteq> {0..<m+Kart}"
      "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1"
      "pval_abstract bigM p = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)"
    using assms(1) by (auto simp: good_pot_val_c_def)
  then obtain e0 R where e0: "real_of_int (of_mtag (fst p)) * bigM + h (snd p) = real_of_int e0 * bigM + R"
      "e0 \<in> {- 1, 0, 1}" "\<bar>R\<bar> \<le> h (sum_list (map abs cost_list))"
    using cost_decompose[OF AD(1-3)] by (auto simp: pval_abstract_def)
  have "h (snd p) = R" using bigM_unique(2)[OF e0(1,2) _ e0(3)] h_pv_bound[OF assms(2)] sabs_nonneg by simp
  with e0 bigM_pos show ?thesis by (auto simp flip: h_abs)
qed

lemma costlist_bound: "e < m \<Longrightarrow> \<bar>cost_list ! e\<bar> \<le> sum_list (map abs cost_list)"
  using nth_mem[of e cost_list] length_cost_list_m by (auto intro!: member_le_sum_list)

text \<open>A good potential value whose \<^emph>\<open>abstract\<close> reading is @{term \<open>0::real\<close>}
      has M-coefficient exactly @{term \<open>0::int\<close>}: the ordinary part is bounded by
      @{term \<open>sum_list (map abs cost_list)\<close>} and the M-coefficient lives in
      @{term \<open>{- 1, 0, 1}\<close>}, while @{term bigM} exceeds that bound, so no nonzero coefficient can
      cancel to zero. This is what lets the abstract root-potential-zero precondition of the network-simplex ADT
      stand in for the concrete @{term pval_zero} the pricing used before.\<close>

lemma gpv_root_zero:
  assumes "good_pot_val_c p" "pv_invar p" "pval_abstract bigM p = 0"
  shows "of_mtag (fst p) = 0"
proof-
  have "of_mtag (fst p) \<in> {- 1, 0, 1}" "\<bar>h (snd p)\<bar> \<le> h (sum_list (map abs cost_list))"
    using gpv_coeff[OF assms(1,2)] by (auto simp flip: h_abs)
  then show ?thesis using assms(3) sabs_nonneg unfolding pval_abstract_def bigM_def abs_le_iff
    by (auto simp del: h_le_iff)
qed

text \<open>Every augmented edge (@{term \<open>e < marc\<close>}) has both endpoints in the arborescence carrier
      @{term Varb} --- real endpoints in @{term \<open>set vs_list\<close>} (@{thm fst_snd_vs}), artificial endpoints
      in @{term \<open>insert vcount (set vs_list)\<close>} (@{thm build_tree_tail_sub}). Hence the pricing only ever
      reads potentials at vertices where the good-potential invariant is known.\<close>

lemma endpt_in_Varb:
  assumes "e < marc" shows "fst_all ! e \<in> Varb \<and> snd_all ! e \<in> Varb"
proof(cases "e < m")
  case True
  then show ?thesis using edged_in_V[of "fst_list ! e"] edged_in_V[of "snd_list ! e"] V_sub_Vseen
      nth_mem[of e fst_list] nth_mem[of e snd_list]
    by (auto simp: Varb_def fst_all_real snd_all_real)
next
  case False
  then obtain k where "e = m + k" "k < Kart" using assms le_Suc_ex[of m e] by (auto simp: marc_def)
  with build_tree_tail_sub show ?thesis
    by (auto simp: tail_sub_def Kart_def seen_set_build_tree fst_all_art snd_all_art Varb_def)
qed

text \<open>The potential store is \<^emph>\<open>good\<close> when every arborescence vertex carries a good
      potential value (invariant @{const good_pot_val_c} and descriptor bound @{const pv_invar}) and the root
      @{const vcount} reads abstractly as @{term \<open>0::real\<close>}. This is exactly what the network-simplex
      selection precondition supplies once @{term pot_value_invar} is instantiated to the good-potential predicate
      and the abstract root-zero precondition is available; the quantifier ranges over @{term Varb} (= the graph
      vertex set) rather than @{term \<open>{0..<vcount}\<close>}, matching the vertex names the algorithm actually
      uses.\<close>

definition pot_ok :: "(mtag \<times> 'n) list \<Rightarrow> bool" where
  "pot_ok pt = ((\<forall>v\<in>Varb. good_pot_val_c (nth pt v) \<and> pv_invar (nth pt v))
                 \<and> pval_abstract bigM (nth pt vcount) = 0)"

lemma plook_bound: "\<lbrakk>pot_ok pt; x \<in> Varb\<rbrakk> \<Longrightarrow>
    of_mtag (fst (nth pt x)) \<in> {- 1, 0, 1} \<and> \<bar>snd (nth pt x)\<bar> \<le> sum_list (map abs cost_list)"
  by (intro gpv_coeff) (auto simp: pot_ok_def)

lemma endpt_le: "e < m + Kart \<Longrightarrow> fst_all ! e \<le> vcount \<and> snd_all ! e \<le> vcount"
  using endpt_in_Varb[of e] Varb_elem_props(1) by (auto simp: marc_def less_Suc_eq_le)

lemma red_cost_faithful:
  assumes "pot_ok pt" "e < marc"
  shows "rc_invar (red_cost pt e) \<and> pval_abstract bigM (red_cost pt e)
    = cost_all ! e + pval_abstract bigM (nth pt (fst_all ! e)) - pval_abstract bigM (nth pt (snd_all ! e))"
proof-
  let ?f = "nth pt (fst_all ! e)" and ?s = "nth pt (snd_all ! e)" and ?S = "sum_list (map abs cost_list)"
  have b: "of_mtag (fst ?f) \<in> {- 1, 0, 1}" "\<bar>snd ?f\<bar> \<le> ?S" "of_mtag (fst ?s) \<in> {- 1, 0, 1}"
    "\<bar>snd ?s\<bar> \<le> ?S"
    using plook_bound[OF assms(1)] endpt_in_Varb[OF assms(2)] by auto
  have c: "pval_abstract bigM (cost_pval e) = cost_all ! e" "\<bar>snd (cost_pval e)\<bar> \<le> ?S"
      "of_mtag (fst (cost_pval e)) = (if e < m then 0 else 1)"
    using assms(2) costlist_bound sabs_nonneg
    by (auto simp: cost_pval_def pval_M_def pval_abstract_def cost_all_real cost_all_art' marc_def)
  have "of_mtag (fst (nth pt vcount)) = 0" using assms(1) r_in_V by (auto simp: pot_ok_def intro!: gpv_root_zero)
  then have "e < m \<or> of_mtag (fst ?f) = 0 \<or> of_mtag (fst ?s) = 0"
    using touches_root_iff[of e] assms(2) by (auto simp: marc_def)
  then have "- 2 \<le> of_mtag (fst ?f) - of_mtag (fst ?s)" "of_mtag (fst ?f) - of_mtag (fst ?s) \<le> 2"
      "- 2 \<le> of_mtag (fst (cost_pval e)) + (of_mtag (fst ?f) - of_mtag (fst ?s))"
      "of_mtag (fst (cost_pval e)) + (of_mtag (fst ?f) - of_mtag (fst ?s)) \<le> 2"
    using b(1,3) c(3) by auto
  moreover have "\<bar>snd (cost_pval e) + (snd ?f - snd ?s)\<bar> \<le> 3 * ?S" using b(2,4) c(2) by arith
  ultimately show ?thesis using c(1)
    by (simp add: red_cost_def rc_invar_def pval_plus_faithful_coeff pval_minus_faithful_coeff pval_minus_coeff,
        simp add: pval_plus_def pval_minus_def)
qed


subsection \<open>Preservation of the potential invariant under the network-simplex conditions\<close>

text \<open>The strengthened potential invariant is \<open>pval_pot_invar\<close>: the descriptor bound
      @{const pv_invar} together with the good-potential certificate \<open>good_pot_val_c\<close>.  Under exactly
      the preconditions the network-simplex locale prescribes for its mixed potential arithmetic
      (@{thm[source] pot_plus_faithful} / @{thm[source] pot_minus_faithful}: the operand invariants and the
      \<open>\<le> 1\<close>-root-touch signed-cost-sum certificate for the \<^emph>\<open>result\<close>), a
      @{const pval_plus} / @{const pval_minus} step keeps the invariant.  The certificate needs no work of its own:
      once faithfulness rewrites @{term \<open>pval_abstract bigM (pval_plus p g)\<close>} to
      @{term \<open>pval_abstract bigM p + pval_abstract bigM g\<close>}, the very sets @{term A}, @{term D}
      witnessing the precondition witness \<open>good_pot_val_c\<close> of the result.  These two lemmas are the
      concrete @{text pot_value_plus_spec} / @{text pot_value_minus_spec} obligations of
      @{locale network_simplex_spec} with @{term pot_value_invar} instantiated to
      \<open>pval_pot_invar\<close>.\<close>

lemma good_pot_val_c_plus:
  "\<lbrakk>pv_invar p; rc_invar g; \<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart}
       \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1
       \<and> pval_abstract bigM p + pval_abstract bigM g
         = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)\<rbrakk>
   \<Longrightarrow> good_pot_val_c (pval_plus p g)"
  by (simp add: good_pot_val_c_def pot_plus_faithful)

lemma good_pot_val_c_minus:
  "\<lbrakk>pv_invar p; rc_invar g; \<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart}
       \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1
       \<and> pval_abstract bigM p - pval_abstract bigM g
         = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)\<rbrakk>
   \<Longrightarrow> good_pot_val_c (pval_minus p g)"
  by (simp add: good_pot_val_c_def pot_minus_faithful)

definition pval_pot_invar :: "mtag \<times> 'n \<Rightarrow> bool" where
  "pval_pot_invar p = (pv_invar p \<and> good_pot_val_c p)"

lemma pot_value_plus_spec_conc:
  "\<lbrakk>pval_pot_invar p; rc_invar g; \<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart}
       \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1
       \<and> pval_abstract bigM p + pval_abstract bigM g
         = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)\<rbrakk>
   \<Longrightarrow> pval_abstract bigM (pval_plus p g) = pval_abstract bigM p + pval_abstract bigM g
    \<and> pval_pot_invar (pval_plus p g)"
  by (simp add: pval_pot_invar_def pot_plus_faithful good_pot_val_c_plus)

lemma pot_value_minus_spec_conc:
  "\<lbrakk>pval_pot_invar p; rc_invar g; \<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart}
       \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1
       \<and> pval_abstract bigM p - pval_abstract bigM g
         = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)\<rbrakk>
   \<Longrightarrow> pval_abstract bigM (pval_minus p g) = pval_abstract bigM p - pval_abstract bigM g
    \<and> pval_pot_invar (pval_minus p g)"
  by (simp add: pval_pot_invar_def pot_minus_faithful good_pot_val_c_minus)

lemma maxpos: "0 < max_candidates"
  using min_candidates_pos min_le_max by simp

lemma not_eligible_sign: "\<lbrakk>\<not> eligible es pt e; rc_invar (red_cost pt e)\<rbrakk> \<Longrightarrow>
    (fst_all ! e \<noteq> snd_all ! e \<longrightarrow> nth es e = InL
     \<longrightarrow> 0 \<le> pval_abstract bigM (red_cost pt e))
    \<and> (fst_all ! e \<noteq> snd_all ! e \<longrightarrow> nth es e = InU
            \<longrightarrow> pval_abstract bigM (red_cost pt e) \<le> 0)"
  by (auto simp: eligible_def pval_neg_abstract pval_pos_abstract not_less)

text \<open>\<^bold>\<open>The @{term None} axiom \<open>sel_select_None\<close> for this selector.\<close> A
      @{term None} return certifies that every non-tree arc is priced with the optimal sign.  The final
      identification of @{term \<open>pval_abstract bigM (red_cost \<pi> e)\<close>} with the true reduced cost
      @{term \<open>\<c> e + \<pi>(fst e) - \<pi>(snd e)\<close>}, and the hypothesis
      @{term \<open>rc_invar (red_cost \<pi> e)\<close>}, both follow from the good-potential invariant
      (@{text good_pot_val}) via @{thm[source] pot_plus_faithful} / @{thm[source] pot_minus_faithful} at the
      @{text network_simplex_init} interpretation, where @{term pot_value_invar} is instantiated to it.\<close>

lemma sel_select_impl_None:
  assumes "sel_invar_impl sel" "\<And>e. e < marc \<Longrightarrow> rc_invar (red_cost pt e)"
    "sel_select_impl sel pt es = None"
  shows "(\<forall>e<marc. fst_all ! e \<noteq> snd_all ! e \<longrightarrow> nth es e = InL
          \<longrightarrow> 0 \<le> pval_abstract bigM (red_cost pt e))
    \<and> (\<forall>e<marc. fst_all ! e \<noteq> snd_all ! e \<longrightarrow> nth es e = InU
            \<longrightarrow> pval_abstract bigM (red_cost pt e) \<le> 0)"
proof-
  obtain a1 len1 b1 where sc: "scan_cache es pt 0 (sel_arr sel) (sel_len sel) no_best = (a1, len1, b1)"
    by (cases "scan_cache es pt 0 (sel_arr sel) (sel_len sel) no_best")
  obtain cur2 a2 len2 b2 where scn:
    "scan es pt marc marc block_size (sel_cur sel) a1 len1 no_best = (cur2, a2, len2, b2)"
    by (cases "scan es pt marc marc block_size (sel_cur sel) a1 len1 no_best")
  have "\<not> fst b1" "\<not> fst b2" using assms(3) sc scn
    by (auto simp: sel_select_impl_def split: prod.splits if_splits)
  moreover have "\<not> fst b1 \<longrightarrow> len1 = 0"
    using scan_cache_spec[of 0 "sel_len sel" "sel_arr sel" es pt no_best] sc assms(1)
      by (auto simp: sel_invar_impl_def)
  ultimately have "\<forall>t<marc. \<not> eligible es pt ((sel_cur sel + t) mod marc)" if "0 < marc"
    using scan_none[OF scn] that assms(1) min_candidates_pos maxpos by (simp add: sel_invar_impl_def no_best_def)
  then have "\<not> eligible es pt e" if "e < marc" for e
    using cyc_cover[of marc "sel_cur sel" e] that assms(1) by (auto simp: sel_invar_impl_def)
  then show ?thesis using not_eligible_sign assms(2) by blast
qed

text \<open>\<^bold>\<open>The @{term Some} axiom \<open>sel_select_Some\<close> for this selector.\<close>
      A returned edge is a genuine arc @{term \<open>e < marc\<close>}, eligible on its side, with descriptor
      @{term \<open>g = red_cost \<pi> e\<close>}; the selector invariant is preserved.  As for @{term None}, the
      identification of @{term \<open>pval_abstract bigM (red_cost \<pi> e)\<close>} with the true reduced cost and the
      @{term rc_invar} hypothesis are discharged from @{text good_pot_val} at interpretation.\<close>

lemma bok_found:
  "\<lbrakk>bok es pt (True, e, u, g) a len; set (take len a) \<subseteq> {0..<marc};
            \<And>e. e < marc \<Longrightarrow> rc_invar (red_cost pt e)\<rbrakk>
   \<Longrightarrow> rc_invar g \<and> g = red_cost pt e \<and> e < marc
     \<and> fst_all ! e \<noteq> snd_all ! e \<and> (if u
    then nth es e = InU \<and> 0 < pval_abstract bigM (red_cost pt e)
      else nth es e = InL \<and> pval_abstract bigM (red_cost pt e) < 0)"
  using sign_helper[of pt e es u] by (auto simp: bok_def)

lemma sel_select_impl_Some:
  assumes "sel_invar_impl sel" "\<And>e. e < marc \<Longrightarrow> rc_invar (red_cost pt e)"
    "sel_select_impl sel pt es = Some (e,in_U,g,s2)"
  shows "sel_invar_impl s2 \<and> rc_invar g \<and> g = red_cost pt e \<and> e < marc
           \<and> fst_all ! e \<noteq> snd_all ! e \<and> (if in_U
    then nth es e = InU \<and> 0 < pval_abstract bigM (red_cost pt e)
      else nth es e = InL \<and> pval_abstract bigM (red_cost pt e) < 0)"
proof-
  obtain a1 len1 f1 e1 u1 g1 where sc:
      "scan_cache es pt 0 (sel_arr sel) (sel_len sel) no_best = (a1, len1, f1, e1, u1, g1)"
    by (cases "scan_cache es pt 0 (sel_arr sel) (sel_len sel) no_best" rule: prod_cases6)
  obtain cur2 a2 len2 f2 e2 u2 g2 where scn:
      "scan es pt marc marc block_size (sel_cur sel) a1 len1 no_best = (cur2, a2, len2, f2, e2, u2, g2)"
    by (cases "scan es pt marc marc block_size (sel_cur sel) a1 len1 no_best" rule: prod_cases7)
  have c: "length a1 = max_candidates" "len1 \<le> max_candidates" "set (take len1 a1) \<subseteq> {0..<marc}"
      "bok es pt (f1, e1, u1, g1) a1 len1" "\<not> f1 \<longrightarrow> len1 = 0"
    using scan_cache_spec[of 0 "sel_len sel" "sel_arr sel" es pt no_best] sc assms(1)
    by (auto simp: sel_invar_impl_def)
  show ?thesis
  proof(cases f1)
    case True
    with assms(3) sc c show ?thesis using bok_found[of es pt e in_U g a1 len1] assms(1,2)
      by (auto simp: sel_select_impl_def sel_invar_impl_def simp del: scan_cache.simps)
  next
    case False
    have "f2" using assms(3) sc scn False
      by (simp add: sel_select_impl_def split: if_splits del: scan_cache.simps scan.simps)
    moreover have "0 < marc" using scn calculation
      by (cases "marc = 0") (simp_all add: scan_fuel0 no_best_def del: scan.simps)
    moreover have "e = e2" "in_U = u2" "g = g2" "s2 = \<lparr>sel_cur = cur2, sel_arr = a2, sel_len = len2\<rparr>"
      using assms(3) sc scn False calculation(1)
        by (simp_all add: sel_select_impl_def del: scan_cache.simps scan.simps)
    ultimately show ?thesis using scan_some_spec[OF scn] c assms(1,2) bok_found[of es pt e2 u2 g2 a2 len2] maxpos False
      by (simp add: sel_invar_impl_def)
  qed
qed

subsection \<open>The ADT axioms, unconditionally, from the good-potential invariant\<close>

text \<open>Folding @{thm red_cost_faithful} into the two theorems above yields exactly the shape of
      \<open>sel_select_Some\<close> / \<open>sel_select_None\<close>: the
      abstract reduced cost @{term \<open>rcabs \<pi> e\<close>} (the concrete @{term reduced_cost}) with no leftover
      @{const rc_invar} hypothesis.  These are what the @{text network_simplex_init} interpretation feeds
      to the ADT, instantiating @{term pot_value_invar} with the good-potential predicate so that
      @{term pot_valid} entails @{const pot_ok}.\<close>

definition rcabs :: "(mtag \<times> 'n) list \<Rightarrow> nat \<Rightarrow> real" where
  "rcabs pt e = cost_all ! e + pval_abstract bigM (nth pt (fst_all ! e)) - pval_abstract bigM (nth pt (snd_all ! e))"

lemma sel_select_impl_None_final:
  "\<lbrakk>sel_invar_impl sel; pot_ok pt; sel_select_impl sel pt es = None\<rbrakk> \<Longrightarrow>
    (\<forall>e<marc. fst_all ! e \<noteq> snd_all ! e \<longrightarrow> nth es e = InL
     \<longrightarrow> 0 \<le> rcabs pt e)
    \<and> (\<forall>e<marc. fst_all ! e \<noteq> snd_all ! e \<longrightarrow> nth es e = InU
            \<longrightarrow> rcabs pt e \<le> 0)"
  using sel_select_impl_None[of sel pt es] red_cost_faithful[of pt] by (simp add: rcabs_def)

lemma sel_select_impl_Some_final:
  "\<lbrakk>sel_invar_impl sel; pot_ok pt; sel_select_impl sel pt es = Some (e,in_U,g,s2)\<rbrakk> \<Longrightarrow>
    sel_invar_impl s2 \<and> rc_invar g \<and> pval_abstract bigM g = rcabs pt e \<and> e < marc
      \<and> fst_all ! e \<noteq> snd_all ! e
    \<and> (if in_U then nth es e = InU \<and> 0 < rcabs pt e else nth es e = InL \<and> rcabs pt e < 0)"
  using sel_select_impl_Some[of sel pt es e in_U g s2] red_cost_faithful[of pt] by (auto simp: rcabs_def)

text \<open>On augmented edges the generic endpoint selectors of the interpretation below are
      @{const fst_all} / @{const snd_all}, so its signed-cost-sum certificate is the one used above.\<close>

lemma cert_conv:
  "(\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> card {e \<in> A \<union> D.
      (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount
      \<or> (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} \<le> 1 \<and> P A D)
   = (\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart}
      \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1 \<and> P A D)"
proof-
  have "{e \<in> A \<union> D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount
      \<or> (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount}
    = {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount}"
    if "A \<subseteq> {0..<m+Kart}" "D \<subseteq> {0..<m+Kart}" for A D
    using that by auto
  then show ?thesis by (simp cong: conj_cong)
qed

section \<open>The @{locale network_simplex_spec} interpretation for the augmented network\<close>

text \<open>The augmented cost-flow network (@{const fst_all} / @{const snd_all} / @{const cap_all} /
      @{const cost_all} over @{term \<open>{0..<m+Kart}\<close>}), the threaded arborescence @{term Sarb} with root
      @{const vcount} and carrier @{term Varb} (= the graph vertex set, @{thm NSg_verts_Varb}), the
      list-backed potential/flow/parent/dir/edge-state arrays and the block-scan selector together form a
      concrete @{locale network_simplex_spec}. The graph and arborescence axioms come from @{term NSg} /
      the @{const arb_invar} facts (rewriting the graph vertex set to @{term Varb} through
      @{thm NSg_verts_Varb}); the abstract-array laws from @{thm list_fixed_univ_map}; the pricing axioms
      @{text sel_select_Some} / @{text sel_select_None} from @{thm sel_select_impl_Some_final} /
      @{thm sel_select_impl_None_final} (with @{term pot_value_invar} instantiated to the good-potential
      predicate so the selection precondition entails @{const pot_ok}); and the descriptor arithmetic
      @{text pot_value_plus_spec} / @{text pot_value_minus_spec} from @{thm pot_plus_faithful} /
      @{thm pot_minus_faithful} with @{thm good_pot_val_c_plus} / @{thm good_pot_val_c_minus}.\<close>

interpretation NS: network_simplex
  where fst = "\<lambda> e. if e < m+Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m+Kart)))"
    and snd = "\<lambda> e. if e < m+Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m+Kart)))"
    and create_edge = "\<lambda> u v. (m+Kart) + prod_encode (u, v)"
    and \<E> = "{0..<m+Kart}"
    and \<u> = "\<lambda> e. if e < m+Kart
                  then (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) else \<infinity>"
    and \<c> = "\<lambda> e. cost_all ! e"
    and r = vcount
    and shift_pot = shift_pot_impl
    and arborescense_invar = "arb_invar vcount Varb"
    and abstract_arborescense = abstract_arb
    and get_path_pair = get_path_pair_impl
    and swap_edge = swap_edge_impl
    and flow_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and flow_upd = list_update
      and flow_lookup = nth
    and pot_invar = "\<lambda>xs. \<forall>v\<in>Varb. v < length xs" and pot_upd = list_update and pot_lookup = nth
    and parent_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and parent_upd = list_update
      and parent_lookup = nth
    and dir_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and dir_upd = list_update
      and dir_lookup = nth
    and es_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs"
      and es_upd = list_update and es_lookup = nth
    and sel_invar = sel_invar_impl and sel_select = sel_select_impl
    and b = "\<lambda> v. h (b_lookup v)"
    and cap = "\<lambda> e. cap_all ! e"
    and pot_value_invar = "\<lambda> p. good_pot_val_c p \<and> pv_invar p"
    and pot_value_abstract = "pval_abstract bigM"
    and pot_value_plus = pval_plus
    and pot_value_minus = pval_minus
    and rcost_invar = rc_invar
    and rcost_abstract = "pval_abstract bigM"
    and fst_exec = "\<lambda> e. fst_all ! e"
    and snd_exec = "\<lambda> e. snd_all ! e"
  apply unfold_locales
  subgoal by simp
  subgoal by simp
  subgoal by simp
  subgoal using num_edges_gtr_0 by simp
  subgoal using cap_all_nonneg by (auto simp: zero_ereal_def)
  subgoal using r_in_V NSg_verts_Varb by simp
  subgoal by (rule graph_invar_abstract_arb)
  subgoal by (rule general_axiom3[where r = vcount and V = Varb]) (assumption | simp add: NSg_verts_Varb)+
  subgoal by (frule Vs_abstract_arb) (simp add: NSg_verts_Varb)
  subgoal by (rule get_path_pair_axiom1[where V = Varb]) (assumption | simp add: NSg_verts_Varb)+
  subgoal by (rule get_path_pair_axiom2[where r = vcount and V = Varb]) (assumption | simp add: NSg_verts_Varb)+
  subgoal by (rule swap_edge_axiom1[where V = Varb]) (assumption | simp add: NSg_verts_Varb)+
  subgoal by (rule swap_edge_axiom2[where r = vcount and V = Varb]) (assumption | simp add: NSg_verts_Varb)+
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) \<comment> \<open>flow upd\<close>
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) \<comment> \<open>flow upd\_invar\<close>
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) \<comment> \<open>pot upd\<close>
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) \<comment> \<open>pot upd\_invar\<close>
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) \<comment> \<open>parent upd\<close>
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) \<comment> \<open>parent upd\_invar\<close>
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) \<comment> \<open>dir upd\<close>
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) \<comment> \<open>dir upd\_invar\<close>
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) \<comment> \<open>es upd\<close>
  subgoal by (auto simp: NSg_verts_Varb nth_fun_list_update) \<comment> \<open>es upd\_invar\<close>
  subgoal by auto \<comment> \<open>fst\_exec\<close>
  subgoal by auto \<comment> \<open>snd\_exec\<close>
  subgoal by auto \<comment> \<open>cap sentinel: (cap = -1) {\isasymlongleftrightarrow}
                                    ({\isasymu} = {\isasyminfinity})\<close>
  subgoal by auto \<comment> \<open>cap value on the non-sentinel branch\<close>
  subgoal using cap_all_nonneg by auto \<comment> \<open>cap validity: 0 {\isasymle} cap {\isasymor} cap = -1\<close>
  subgoal premises p for sel \<pi> es e in_U \<gamma> sel'
  proof-
    have "pot_ok \<pi>" using p(3)[simplified NSg_verts_Varb] p(4) by (simp add: pot_ok_def)
    then show ?thesis using sel_select_impl_Some_final[OF p(1) _ p(6)] by (auto simp: rcabs_def marc_def)
  qed
  subgoal premises p for sel \<pi> es
  proof-
    have "pot_ok \<pi>" using p(3)[simplified NSg_verts_Varb] p(4) by (simp add: pot_ok_def)
    then show ?thesis using sel_select_impl_None_final[OF p(1) _ p(6)] by (auto simp: rcabs_def marc_def)
  qed
  subgoal premises p for p g
    using p(1) pot_plus_faithful[OF _ p(2) p(3)[unfolded cert_conv]]
      good_pot_val_c_plus[OF _ p(2) p(3)[unfolded cert_conv]] by simp
  subgoal premises p for p g
    using p(1) pot_minus_faithful[OF _ p(2) p(3)[unfolded cert_conv]]
      good_pot_val_c_minus[OF _ p(2) p(3)[unfolded cert_conv]] by simp
  subgoal by (rule shift_pot_impl_spec[where V = Varb]) (simp_all add: NSg_verts_Varb)
  done


subsection \<open>Assembling the @{locale network_simplex_init} correctness obligations\<close>

text \<open>The concrete starting basis discharges five of the ten @{locale network_simplex_init} obligations
      directly from the proved @{const build_tree} corollaries: the two trivial ones (store invariant and
      @{thm arb_invar_Sarb}), the selector seed @{const init_sel}, the flow/edge partition fit
      (@{thm build_tree_tail_content} together with the real-edge status lemmas), and the potential fit
      (@{thm build_tree_rc_zero} together with @{thm build_tree_root_pot}). The remaining five ---
      @{term \<open>NS.pot_valid\<close>}, the @{term \<open>NS.isbflow\<close>}, the spanning-tree partition,
      strong feasibility and the tree correspondence --- need additional carried invariants, established in the
      following subsections.\<close>

lemma NS_V_Varb: "NS.\<V> = Varb"
  using NSg_verts_Varb by simp

lemma NS_V_minus_root: "NS.\<V> - {vcount} = Vseen"
  using NS_V_Varb by (auto simp: Varb_def Vseen_def)

lemma NS_V_minus_root_sub: "NS.\<V> - {vcount} \<subseteq> set vs_list"
  using NS_V_minus_root Vseen_eq_V V_sub_vs_list by simp

lemma len_par_bt: "length (ds_par (build_tree acyc_flow)) = Suc vcount"
  using build_tree_inv by (simp add: dfs_inv_def dfs_sized_def)

lemma len_dir_bt: "length (ds_dir (build_tree acyc_flow)) = Suc vcount"
  using build_tree_inv by (simp add: dfs_inv_def dfs_sized_def)

text \<open>Every non-root tree vertex's parent edge index lies inside the augmented edge range: interior
      vertices point at a real free edge (below @{term m}), component roots at their artificial edge.\<close>

lemma par_lt_marc:
  assumes "w < vcount" "ds_seen (build_tree acyc_flow) ! w"
  shows "ds_par (build_tree acyc_flow) ! w < m + Kart"
proof(cases "ds_prnt (build_tree acyc_flow) ! w < vcount")
  case False
  then have "ds_prnt (build_tree acyc_flow) ! w = vcount"
    using build_tree_inv assms unfolding dfs_inv_def tree_seen_inv_def by blast
  with build_tree_comproot_inv assms show ?thesis by (auto simp: comproot_inv_def comproot_edge_ok_def Kart_def)
qed (use build_tree_par_edge[OF assms] in simp)

lemma pval_abstract_zero: "pval_abstract bigM pval_zero = 0"
  by (simp add: pval_abstract_def pval_zero_def)

text \<open>Obligation 8 (\<open>potential_fits_spanning_tree_partition\<close>): the root potential is zero
      (@{thm build_tree_root_pot}) and every tree edge has zero reduced cost (@{thm build_tree_rc_zero}).\<close>

lemma NSinit_pot_fits:
  "NS.potential_fits_spanning_tree_partition vcount
     (nth (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}))
     (NS.abstract_pot (ds_pot (build_tree acyc_flow)))"
proof(unfold NS.potential_fits_spanning_tree_partition_def, intro conjI ballI)
  fix e assume "e \<in> nth (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})"
  then obtain v where "v < vcount" "ds_seen (build_tree acyc_flow) ! v" "e = ds_par (build_tree acyc_flow) ! v"
    using NS_V_minus_root by (auto simp: Vseen_def)
  then show "cost_all ! e
      + NS.abstract_pot (ds_pot (build_tree acyc_flow))
        (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))))
      - NS.abstract_pot (ds_pot (build_tree acyc_flow))
        (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart))))
      = 0"
    by (simp only: if_P[OF par_lt_marc] build_tree_rc_zero)
qed (use build_tree_root_pot plook_pot[of vcount] pval_abstract_zero in simp)

text \<open>Obligation 3 (selector invariant): the empty seed trivially satisfies @{const sel_invar_impl}.\<close>

lemma NSinit_sel_invar: "sel_invar_impl init_sel"
  using num_edges_gtr_0 by (simp add: sel_invar_impl_def init_sel_def marc_def)

text \<open>Obligation 7 (\<open>flow_fits_spanning_tree_partition\<close>): an @{const InL} edge carries no flow
      and an @{const InU} edge is saturated at a finite capacity --- real edges by their status
      characterisation, artificial edges by @{thm build_tree_tail_content}.\<close>

lemma slook: "e < m + Kart \<Longrightarrow> nth state_all e = state_all ! e"
  by simp

lemma flook: "e < m + Kart \<Longrightarrow> nth flow_all e = flow_all ! e"
  by simp

lemma art_state_not_InL: "k < Kart \<Longrightarrow> ds_aest (build_tree acyc_flow) ! k \<noteq> InL"
  using tail_edge_ok_build_tree[of k] by (auto simp: tail_edge_ok_def)

lemma art_InU_flow_cap: "\<lbrakk>k < Kart; ds_aest (build_tree acyc_flow) ! k = InU\<rbrakk> \<Longrightarrow>
    ds_aflw (build_tree acyc_flow) ! k = ds_acap (build_tree acyc_flow) ! k
      \<and> 0 \<le> ds_acap (build_tree acyc_flow) ! k"
  using tail_edge_ok_build_tree[of k] by (auto simp: tail_edge_ok_def art_flow_def)

lemma NSinit_flow_fits:
  "NS.flow_fits_spanning_tree_partition
     (nth (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}))
     {e \<in> {0..<m + Kart}. nth state_all e = InL}
     {e \<in> {0..<m + Kart}. nth state_all e = InU}
     (\<lambda>e. h (nth flow_all e))"
proof(unfold NS.flow_fits_spanning_tree_partition_def, intro conjI ballI)
  fix e assume "e \<in> {e \<in> {0..<m + Kart}. nth state_all e = InL}"
  then show "h (nth flow_all e) = 0"
    using le_Suc_ex[of m e] edge_state_InL_iff[of e] art_state_not_InL
    by (cases "e < m") (auto simp: state_all_real flow_all_real state_all_art)
next
  fix e assume "e \<in> {e \<in> {0..<m + Kart}. nth state_all e = InU}"
  then show "ereal (h (nth flow_all e))
      = (if e < m + Kart then if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e)) else \<infinity>)"
    using le_Suc_ex[of m e] edge_state_InU_iff[of e] art_InU_flow_cap[of "e - m"]
    by (cases "e < m") (auto simp: state_all_real flow_all_real cap_all_real state_all_art flow_all_art cap_all_art)
qed


subsection \<open>A combined DFS invariant: component-root direction and artificial-edge fields\<close>

text \<open>Obligation 9 (strong feasibility) needs, at every component root @{term c}, the tree-edge direction
      @{term \<open>ds_dir (build_tree acyc_flow) ! c = art_dir c\<close>} and the artificial edge's tag/flow/cap.
      These four facts are carried through the builder as a single invariant \<open>cr_ext_inv\<close>, alongside
      @{const comproot_inv}.  The direction is frozen by @{const build_dfs} at already-seen vertices
      (\<open>build_dfs_frozen\<close>); the artificial-edge fields sit below the tail cursor and are frozen by
      @{thm build_dfs_art} and update-at-a-fresh-index reasoning.\<close>

lemma bd_upd1_frozen:
  assumes "dfs_inv fl s" "bd_call1_conds fl s" "ds_seen s ! x"
  shows "ds_prnt (bd_upd1 fl s) ! x = ds_prnt s ! x \<and> ds_par (bd_upd1 fl s) ! x = ds_par s ! x
         \<and> ds_dir (bd_upd1 fl s) ! x = ds_dir s ! x"
proof-
  have "dfs_wf fl s" using assms(1) by (simp add: dfs_inv_def)
  then obtain v and rest :: "nat list" and e w c' where
    "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr>
                     else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    using assms(2) by (rule bd_upd1_eq)
  with assms(3) show ?thesis
    by (cases "ds_seen s ! w"; cases "w = x") (auto simp: dfs_discover_def dfs_push_def Let_def)
qed

lemma bd_upd2_frozen:
  assumes "dfs_inv fl s" "bd_call2_conds fl s" "ds_seen s ! x"
  shows "ds_prnt (bd_upd2 fl s) ! x = ds_prnt s ! x \<and> ds_par (bd_upd2 fl s) ! x = ds_par s ! x
         \<and> ds_dir (bd_upd2 fl s) ! x = ds_dir s ! x"
proof-
  have "dfs_wf fl s" using assms(1) by (simp add: dfs_inv_def)
  then obtain v and rest :: "nat list" and e w c' where
    "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr>
                     else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    using assms(2) by (rule bd_upd2_eq)
  with assms(3) show ?thesis
    by (cases "ds_seen s ! w"; cases "w = x") (auto simp: dfs_discover_def dfs_push_def Let_def)
qed

lemma bd_upd3_frozen: "bd_call3_conds fl s \<Longrightarrow> ds_prnt (bd_upd3 s) ! x = ds_prnt s ! x
    \<and> ds_par (bd_upd3 s) ! x = ds_par s ! x \<and> ds_dir (bd_upd3 s) ! x = ds_dir s ! x"
  by (erule bd_upd3_eq) (simp add: dfs_finish_def Let_def)

text \<open>@{const build_dfs} freezes the tree fields of an already-seen vertex.\<close>

lemma build_dfs_frozen:
  assumes "build_dfs_dom (fl, s)" "dfs_inv fl s" "ds_seen s ! x"
  shows "ds_prnt (build_dfs fl s) ! x = ds_prnt s ! x \<and> ds_par (build_dfs fl s) ! x = ds_par s ! x
         \<and> ds_dir (build_dfs fl s) ! x = ds_dir s ! x"
proof-
  let ?Q = "\<lambda>t. ds_seen t ! x \<and> ds_prnt t ! x = ds_prnt s ! x \<and> ds_par t ! x = ds_par s ! x
    \<and> ds_dir t ! x = ds_dir s ! x"
  have "?Q (build_dfs fl s)"
    by (rule build_dfs_preserve[OF assms(1,2)])
      (use assms(3) in \<open>auto simp: bd_upd1_frozen bd_upd2_frozen bd_upd3_frozen
        bd_upd1_seen_mono bd_upd2_seen_mono bd_upd3_seen_mono\<close>)
  then show ?thesis by simp
qed

definition cr_ext_ok :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> bool" where
  "cr_ext_ok s c \<longleftrightarrow> ds_dir s ! c = art_dir c
     \<and> ds_aest s ! (ds_par s ! c - m) = InTree
     \<and> ds_aflw s ! (ds_par s ! c - m) = art_flow c
     \<and> ds_acap s ! (ds_par s ! c - m) = art_tree_cap c"

definition cr_ext_inv :: "'n dfs_state \<Rightarrow> bool" where
  "cr_ext_inv s \<longleftrightarrow>
     (\<forall>c<vcount. ds_seen s ! c \<longrightarrow> ds_prnt s ! c = vcount \<longrightarrow> cr_ext_ok s c)"

lemma emit_U_edge_crext:
  "\<lbrakk>comproot_inv s; cr_ext_inv s\<rbrakk> \<Longrightarrow> cr_ext_inv (emit_U_edge s v)"
  by (auto simp: cr_ext_inv_def cr_ext_ok_def comproot_inv_def comproot_edge_ok_def emit_U_edge_def Let_def)

lemma open_tree_component_crext:
  assumes "dfs_inv acyc_flow s" "c < vcount" "\<not> ds_seen s ! c" "c \<noteq> 0" "ds_stk s = []" "art_len s"
    "ds_nxt s < length vs_list" "comproot_inv s" "cr_ext_inv s"
  shows "cr_ext_inv (open_tree_component acyc_flow s c)"
proof-
  have W: "dfs_wf acyc_flow s" "dfs_sized s" using assms(1) by (simp_all add: dfs_inv_def)
  obtain sd where sd: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd" "build_dfs_dom (acyc_flow, sd)"
      "dfs_inv acyc_flow sd" "ds_seen sd = (ds_seen s)[c := True]" "ds_prnt sd = (ds_prnt s)[c := vcount]"
      "ds_par sd = (ds_par s)[c := m + ds_nxt s]" "ds_dir sd = (ds_dir s)[c := art_dir c]"
      "ds_acap sd = (ds_acap s)[ds_nxt s := art_tree_cap c]" "ds_aflw sd = (ds_aflw s)[ds_nxt s := art_flow c]"
      "ds_aest sd = (ds_aest s)[ds_nxt s := InTree]"
    by (rule open_tree_component_seed[OF W assms(2)]) (use assms(1,3-5) in blast)
  have L: "length (ds_par s) = Suc vcount" "length (ds_dir s) = Suc vcount" "length (ds_aest s) = length vs_list"
    "length (ds_aflw s) = length vs_list" "length (ds_acap s) = length vs_list"
    using W(2) assms(6) by (simp_all add: dfs_sized_def art_len_def)
  show ?thesis
    unfolding cr_ext_inv_def sd(1)
  proof(intro allI impI)
    fix w assume "w < vcount" "ds_seen (build_dfs acyc_flow sd) ! w" "ds_prnt (build_dfs acyc_flow sd) ! w = vcount"
    with build_dfs_cr[OF sd(2,3)] have "ds_seen sd ! w" "ds_prnt sd ! w = vcount"
      "ds_par (build_dfs acyc_flow sd) ! w = ds_par sd ! w"
      by auto
    with build_dfs_frozen[OF sd(2,3)] show "cr_ext_ok (build_dfs acyc_flow sd) w"
      using \<open>w < vcount\<close> assms(2,7,8,9) L build_dfs_art[OF sd(2)] sd(4-10)
      by (cases "w = c") (auto simp: cr_ext_inv_def cr_ext_ok_def comproot_inv_def
                          comproot_edge_ok_def nth_list_update)
  qed
qed

lemma phase1_step_crext:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; ds_stk s = []; art_len s; comproot_inv s; cr_ext_inv s;
    ds_nxt (phase1_step acyc_flow v s) \<le> length vs_list\<rbrakk>
      \<Longrightarrow> cr_ext_inv (phase1_step acyc_flow v s)"
  using vs_less_vcount[of v] no_zero_node open_tree_component_art(1)[of acyc_flow s v]
  by (cases "v = 0") (auto simp: phase1_step_def emit_U_edge_crext intro!: open_tree_component_crext)

lemma phase2_step_crext:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; ds_stk s = []; art_len s; comproot_inv s; cr_ext_inv s;
    ds_nxt (phase2_step acyc_flow v s) \<le> length vs_list\<rbrakk>
      \<Longrightarrow> cr_ext_inv (phase2_step acyc_flow v s)"
  using vs_less_vcount[of v] no_zero_node open_tree_component_art(1)[of acyc_flow s v]
  by (cases "v = 0") (auto simp: phase2_step_def intro!: open_tree_component_crext)

lemma build_tree_crext: "cr_ext_inv (build_tree acyc_flow)"
proof-
  let ?Q = "\<lambda>s. art_len s
              \<and> (ds_nxt s \<le> length vs_list \<longrightarrow> comproot_inv s \<and> cr_ext_inv s)"
  have "?Q (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
  proof(rule phases_preserve[where Q = ?Q])
    fix v s assume "v \<in> set vs_list" "dfs_inv acyc_flow s \<and> ds_stk s = []" "?Q s"
    then show "?Q (phase1_step acyc_flow v s)" "?Q (phase2_step acyc_flow v s)"
      using phase1_step_nxt[of s v] phase2_step_nxt2[of s v] vs_less_vcount[of v]
      by (auto simp: phase1_step_art_len phase2_step_art_len
          intro: phase1_step_cri phase2_step_cri phase1_step_crext phase2_step_crext)
  qed (use dfs_init_art_len in \<open>simp add: comproot_inv_def cr_ext_inv_def dfs_init_def del:
                                      replicate_Suc\<close>)
  then show ?thesis
    using build_tree_nxt_le by (simp add: build_tree_def Let_def cr_ext_inv_def cr_ext_ok_def)
qed

text \<open>Obligation 9 (\<open>init_strict\<close>, strong feasibility): each non-root tree vertex's parent edge
      is strictly interior in the required direction.  Interior edges are free (both residual bounds
      hold); component-root edges are artificial, and their direction together with the tree-capacity
      (@{const art_tree_cap}) makes exactly the required bound strict.\<close>

lemmas acyc_is_free_iff = is_free_iff[OF acyc_flow_nonneg acyc_flow_le_cap]
  and acyc_state_InTree_iff = edge_state_InTree_iff[OF acyc_flow_nonneg acyc_flow_le_cap]

lemma par_free:
  "\<lbrakk>v < vcount; ds_seen (build_tree acyc_flow) ! v;
            ds_prnt (build_tree acyc_flow) ! v < vcount\<rbrakk> \<Longrightarrow>
    ds_par (build_tree acyc_flow) ! v < m \<and> is_free acyc_flow (ds_par (build_tree acyc_flow) ! v)"
  using build_tree_par_edge by blast

lemma par_ends:
  "\<lbrakk>v < vcount; ds_seen (build_tree acyc_flow) ! v;
            ds_prnt (build_tree acyc_flow) ! v < vcount\<rbrakk> \<Longrightarrow>
    fst_list ! (ds_par (build_tree acyc_flow) ! v)
      = (if ds_dir (build_tree acyc_flow) ! v then v else ds_prnt (build_tree acyc_flow) ! v)
    \<and> snd_list ! (ds_par (build_tree acyc_flow) ! v)
      = (if ds_dir (build_tree acyc_flow) ! v then ds_prnt (build_tree acyc_flow) ! v else v)"
  using build_tree_par_edge by blast

lemma strict_interior:
  "\<lbrakk>v < vcount; ds_seen (build_tree acyc_flow) ! v;
            ds_prnt (build_tree acyc_flow) ! v < vcount\<rbrakk> \<Longrightarrow>
    if ds_dir (build_tree acyc_flow) ! v
         then ereal (h (flow_all ! (ds_par (build_tree acyc_flow) ! v)))
                < (if cap_all ! (ds_par (build_tree acyc_flow) ! v) = - 1 then \<infinity>
                   else ereal (h (cap_all ! (ds_par (build_tree acyc_flow) ! v))))
         else 0 < flow_all ! (ds_par (build_tree acyc_flow) ! v)"
  by (drule (2) par_free) (auto simp: flow_all_real cap_all_real acyc_is_free_iff)

lemma strict_comproot:
  assumes "v < vcount" "ds_seen (build_tree acyc_flow) ! v" "ds_prnt (build_tree acyc_flow) ! v = vcount"
  shows "if ds_dir (build_tree acyc_flow) ! v
         then ereal (h (flow_all ! (ds_par (build_tree acyc_flow) ! v)))
                < (if cap_all ! (ds_par (build_tree acyc_flow) ! v) = - 1 then \<infinity>
                   else ereal (h (cap_all ! (ds_par (build_tree acyc_flow) ! v))))
         else 0 < flow_all ! (ds_par (build_tree acyc_flow) ! v)"
proof-
  let ?e = "ds_par (build_tree acyc_flow) ! v"
  have "cr_ext_ok (build_tree acyc_flow) v" "comproot_edge_ok (build_tree acyc_flow) v"
    using build_tree_crext build_tree_comproot_inv assms by (simp_all add: cr_ext_inv_def comproot_inv_def)
  then have "ds_dir (build_tree acyc_flow) ! v = art_dir v" "flow_all ! ?e = art_flow v"
    "cap_all ! ?e = art_tree_cap v"
    using flow_all_art[of "?e - m"] cap_all_art[of "?e - m"]
    by (auto simp: cr_ext_ok_def comproot_edge_ok_def Kart_def)
  then show ?thesis by (auto simp: art_tree_cap_def art_flow_def art_dir_def)
qed

lemma strict_core:
  "v \<in> Vseen \<Longrightarrow> if ds_dir (build_tree acyc_flow) ! v
         then ereal (h (flow_all ! (ds_par (build_tree acyc_flow) ! v)))
                < (if cap_all ! (ds_par (build_tree acyc_flow) ! v) = - 1 then \<infinity>
                   else ereal (h (cap_all ! (ds_par (build_tree acyc_flow) ! v))))
         else 0 < flow_all ! (ds_par (build_tree acyc_flow) ! v)"
  unfolding Vseen_def using build_tree_parent_in_seen[of v acyc_flow] strict_interior[of v] strict_comproot[of v]
  by blast

lemma NSinit_strict:
  "\<forall>v\<in>NS.\<V> - {vcount}.
      if nth (ds_dir (build_tree acyc_flow)) v
      then ereal (h (nth flow_all (nth (ds_par (build_tree acyc_flow)) v)))
             < (if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                then if cap_all ! nth (ds_par (build_tree acyc_flow)) v = - 1 then \<infinity>
                     else ereal (h (cap_all ! nth (ds_par (build_tree acyc_flow)) v))
                else \<infinity>)
      else 0 < nth flow_all (nth (ds_par (build_tree acyc_flow)) v)"
proof
  fix v assume "v \<in> NS.\<V> - {vcount}"
  then have "v \<in> Vseen" using NS_V_minus_root by simp
  moreover from this have "ds_par (build_tree acyc_flow) ! v < m + Kart" by (intro par_lt_marc) (auto simp: Vseen_def)
  ultimately show "if nth (ds_dir (build_tree acyc_flow)) v
      then ereal (h (nth flow_all (nth (ds_par (build_tree acyc_flow)) v)))
             < (if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                then if cap_all ! nth (ds_par (build_tree acyc_flow)) v = - 1 then \<infinity>
                     else ereal (h (cap_all ! nth (ds_par (build_tree acyc_flow)) v))
                else \<infinity>)
      else 0 < nth flow_all (nth (ds_par (build_tree acyc_flow)) v)"
    using strict_core by simp
qed


subsection \<open>Obligation 10 (init\_tree\_corr): the parent edges realise the abstract arborescence\<close>

text \<open>Every non-root tree vertex's parent edge realises its tree edge (endpoints
      \<open>{v, ds_prnt bt ! v}\<close>, correctly oriented by the direction flag), the finished parent-edge set
      has exactly the abstract arborescence @{term \<open>abstract_arb Sarb\<close>} as its endpoint-set family,
      and the walk to the root is the @{const follow} chain (@{thm follow_walk_root}).\<close>

lemma Vseen_par_lt: "v \<in> Vseen \<Longrightarrow> ds_par (build_tree acyc_flow) ! v < m + Kart"
  by (rule par_lt_marc) (auto simp: Vseen_def)

lemma tc_endpoints_interior:
  "\<lbrakk>v < vcount; ds_seen (build_tree acyc_flow) ! v;
            ds_prnt (build_tree acyc_flow) ! v < vcount\<rbrakk> \<Longrightarrow>
    fst_all ! (ds_par (build_tree acyc_flow) ! v)
      = (if ds_dir (build_tree acyc_flow) ! v then v else ds_prnt (build_tree acyc_flow) ! v)
    \<and> snd_all ! (ds_par (build_tree acyc_flow) ! v)
      = (if ds_dir (build_tree acyc_flow) ! v then ds_prnt (build_tree acyc_flow) ! v else v)"
  using par_free[of v] par_ends[of v] fst_all_real snd_all_real by (simp del: NS.fst_exec_eq NS.snd_exec_eq)

lemma tc_endpoints_comproot:
  assumes "v < vcount" "ds_seen (build_tree acyc_flow) ! v" "ds_prnt (build_tree acyc_flow) ! v = vcount"
  shows "fst_all ! (ds_par (build_tree acyc_flow) ! v)
      = (if ds_dir (build_tree acyc_flow) ! v then v else ds_prnt (build_tree acyc_flow) ! v)
    \<and> snd_all ! (ds_par (build_tree acyc_flow) ! v)
      = (if ds_dir (build_tree acyc_flow) ! v then ds_prnt (build_tree acyc_flow) ! v else v)"
proof-
  let ?e = "ds_par (build_tree acyc_flow) ! v"
  have "cr_ext_ok (build_tree acyc_flow) v" "comproot_edge_ok (build_tree acyc_flow) v"
    using build_tree_crext build_tree_comproot_inv assms by (simp_all add: cr_ext_inv_def comproot_inv_def)
  then show ?thesis using fst_all_art[of "?e - m"] snd_all_art[of "?e - m"] assms(3)
    by (auto simp: cr_ext_ok_def comproot_edge_ok_def Kart_def)
qed

lemma tc_endpoints:
  "v \<in> Vseen \<Longrightarrow> fst_all ! (ds_par (build_tree acyc_flow) ! v)
      = (if ds_dir (build_tree acyc_flow) ! v then v else ds_prnt (build_tree acyc_flow) ! v)
    \<and> snd_all ! (ds_par (build_tree acyc_flow) ! v)
      = (if ds_dir (build_tree acyc_flow) ! v then ds_prnt (build_tree acyc_flow) ! v else v)"
  unfolding Vseen_def using build_tree_parent_in_seen[of v acyc_flow] tc_endpoints_interior[of v]
    tc_endpoints_comproot[of v]
  by blast

lemma abstract_arb_Sarb: "abstract_arb Sarb = {{x, y} |x y. Sprnt x = Some y}"
  by (simp add: abstract_arb_def Sarb_sel)

lemma arb_edge_set: "abstract_arb Sarb = (\<lambda>v. {v, ds_prnt (build_tree acyc_flow) ! v}) ` Vseen"
  by (auto simp: abstract_arb_Sarb Sprnt_def split: if_splits)

lemma tc_edge: "v \<in> Vseen \<Longrightarrow>
    {fst_all ! (ds_par (build_tree acyc_flow) ! v), snd_all ! (ds_par (build_tree acyc_flow) ! v)}
      = {v, ds_prnt (build_tree acyc_flow) ! v}"
  using tc_endpoints[of v] by (cases "ds_dir (build_tree acyc_flow) ! v") (auto simp: insert_commute)

lemma tc_image:
  "(\<lambda>e. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
           if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))})
     ` (nth (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})) = abstract_arb Sarb"
  unfolding NS_V_minus_root image_image arb_edge_set
  by (rule image_cong[OF refl]) (simp only: if_P[OF Vseen_par_lt] tc_edge)

lemmas Sprnt_follow_simps = follow_ps_simps[OF parent_spec_Sprnt]
  and Sprnt_follow_distinct = follow_distinct_ps[OF parent_spec_Sprnt]
  and Sarb_follow_walk = follow_walk_root[OF arb_invar_Sarb]
  and Sarb_graph_invar = graph_invar_abstract_arb[OF arb_invar_Sarb]
  and Sarb_Vs = Vs_abstract_arb[OF arb_invar_Sarb]

lemma tc_walk:
  assumes "v \<in> Vseen"
  shows "\<exists>q. distinct (v # ds_prnt (build_tree acyc_flow) ! v # q)
             \<and> walk_betw (abstract_arb Sarb) v (v # ds_prnt (build_tree acyc_flow) ! v # q) vcount"
proof-
  have "Sprnt v = Some (ds_prnt (build_tree acyc_flow) ! v)" using assms by (simp add: Sprnt_def)
  then have "follow Sprnt v = v # ds_prnt (build_tree acyc_flow) ! v # tl
               (follow Sprnt (ds_prnt (build_tree acyc_flow) ! v))"
    using Sprnt_follow_simps[of v] Sprnt_follow_simps[of "ds_prnt (build_tree acyc_flow) ! v"]
    by (auto split: option.splits)
  moreover have "walk_betw (abstract_arb Sarb) v (follow Sprnt v) vcount"
    using Sarb_follow_walk[of v] assms by (simp add: Sarb_sel Varb_def)
  ultimately show ?thesis using Sprnt_follow_distinct[of v] by auto
qed

lemma tc_ball: "v \<in> Vseen \<Longrightarrow> nth (ds_par (build_tree acyc_flow)) v \<in> {0..<m + Kart}
      \<and> (if nth (ds_dir (build_tree acyc_flow)) v
          then (if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                then fst_all ! nth (ds_par (build_tree acyc_flow)) v
                else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v
          else (if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                then snd_all ! nth (ds_par (build_tree acyc_flow)) v
                else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v)
      \<and> (\<exists>q. distinct (v # (if nth (ds_dir (build_tree acyc_flow)) v
                then if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                  then snd_all ! nth (ds_par (build_tree acyc_flow)) v
                  else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))
                else if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                  then fst_all ! nth (ds_par (build_tree acyc_flow)) v
                  else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q)
             \<and> walk_betw (abstract_arb Sarb) v (v # (if nth (ds_dir (build_tree acyc_flow)) v
                then if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                  then snd_all ! nth (ds_par (build_tree acyc_flow)) v
                  else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))
                else if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                  then fst_all ! nth (ds_par (build_tree acyc_flow)) v
                  else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q) vcount)"
  using tc_endpoints[of v] tc_walk[of v] Vseen_par_lt[of v]
  by (cases "ds_dir (build_tree acyc_flow) ! v")
    (simp_all only: if_True if_False if_P atLeastLessThan_iff le0 simp_thms)

lemma NSinit_tree_corr:
  "(\<forall>v\<in>NS.\<V> - {vcount}. nth (ds_par (build_tree acyc_flow)) v \<in> {0..<m + Kart}
      \<and> (if nth (ds_dir (build_tree acyc_flow)) v
          then (if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                then fst_all ! nth (ds_par (build_tree acyc_flow)) v
                else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v
          else (if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                then snd_all ! nth (ds_par (build_tree acyc_flow)) v
                else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v)
      \<and> (\<exists>q. distinct (v # (if nth (ds_dir (build_tree acyc_flow)) v
                then if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                  then snd_all ! nth (ds_par (build_tree acyc_flow)) v
                  else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))
                else if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                  then fst_all ! nth (ds_par (build_tree acyc_flow)) v
                  else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q)
             \<and> walk_betw (abstract_arb Sarb) v (v # (if nth (ds_dir (build_tree acyc_flow)) v
                then if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                  then snd_all ! nth (ds_par (build_tree acyc_flow)) v
                  else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))
                else if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                  then fst_all ! nth (ds_par (build_tree acyc_flow)) v
                  else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q) vcount))
   \<and> (\<lambda>e. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
           if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))})
       ` nth (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}) = abstract_arb Sarb"
  using tc_ball tc_image unfolding NS_V_minus_root by blast



section \<open>The @{locale network_simplex_init} interpretation for the constructed initial basis\<close>

text \<open>Extending @{term NS} with the concrete starting basis produced by @{const build_tree}: the flow
      @{const flow_all}, the potentials @{term \<open>ds_pot (build_tree acyc_flow)\<close>}, the arborescence
      @{term Sarb}, the parent/direction maps @{term \<open>ds_par (build_tree acyc_flow)\<close>} /
      @{term \<open>ds_dir (build_tree acyc_flow)\<close>}, the edge-state array @{const state_all} and the
      selector seed @{const init_sel}. Because @{term NS} already discharges every
      \<open>network_simplex_spec\<close> axiom, \<open>unfold_locales\<close> leaves only the 10
      @{locale network_simplex_init} obligations. They are discharged in this theory: the trivial store invariant,
      the tree invariant @{thm arb_invar_Sarb}, the selector seed (@{thm NSinit_sel_invar}), the
      flow/edge-partition fit (@{thm NSinit_flow_fits}), the potential fit (@{thm NSinit_pot_fits}), strong
      feasibility (@{thm NSinit_strict}) and the tree correspondence (@{thm NSinit_tree_corr}) below, and the store
      validity, the \<open>b\<close>-flow and the spanning-tree partition further down.\<close>

subsection \<open>Validity of the initial potentials (obligation 2 / init\_pot\_valid)\<close>

text \<open>The built potential is a valid network-simplex potential: it satisfies the store-length
      invariant and, at every vertex, the good-potential certificate good\_pot\_val\_c together with
      the descriptor bound pv\_invar. The certificate is obtained from a closed form of the
      potential as a signed sum of tree-path edge costs (pot\_repr), proved by well-founded
      induction along the parent relation; distinctness of the path edges (par\_inj) keeps the
      cost sums honest, and exactly one artificial (root-incident) edge sits at the top of each
      path, which is what bounds the root-incident count by one.\<close>

lemma par_inj:
  assumes "u \<in> Vseen" "u' \<in> Vseen" "ds_par (build_tree acyc_flow) ! u = ds_par (build_tree acyc_flow) ! u'"
  shows "u = u'"
proof(rule ccontr)
  assume "u \<noteq> u'"
  let ?p = "\<lambda>x. ds_prnt (build_tree acyc_flow) ! x"
  have "(u, ?p u) \<in> pstep (build_tree acyc_flow)" "(u', ?p u') \<in> pstep (build_tree acyc_flow)"
    using assms(1,2) by (auto simp: pstep_def Vseen_def)
  moreover have "{u, ?p u} = {u', ?p u'}" using tc_edge[of u] tc_edge[of u'] assms by simp
  ultimately have "(u, u') \<in> pstep (build_tree acyc_flow)" "(u', u) \<in> pstep (build_tree acyc_flow)"
    using \<open>u \<noteq> u'\<close> by (auto simp: doubleton_eq_iff)
  then have "(u, u) \<in> (pstep (build_tree acyc_flow))\<^sup>+" by auto
  with pstep_acyclic show False by (simp add: acyclic_def)
qed

lemma pstep_build_tree: "pstep (build_tree acyc_flow) = (\<lambda>x. (x, ds_prnt (build_tree acyc_flow) ! x)) ` Vseen"
  by (auto simp: pstep_def Vseen_def)

lemma PS_finite: "finite (pstep (build_tree acyc_flow))"
  using Vseen_finite by (simp add: pstep_build_tree)

lemma wf_PS_conv: "wf ((pstep (build_tree acyc_flow))\<inverse>)"
  using PS_finite pstep_acyclic by (simp add: finite_acyclic_wf)

lemma anc_step:
  assumes "w \<in> Vseen"
  shows "{u. (w,u) \<in> (pstep (build_tree acyc_flow))\<^sup>*}
    = insert w {u. (ds_prnt (build_tree acyc_flow) ! w, u) \<in> (pstep (build_tree acyc_flow))\<^sup>*}"
proof-
  have "(w, y) \<in> pstep (build_tree acyc_flow) \<longleftrightarrow> y = ds_prnt (build_tree acyc_flow) ! w" for y
    using assms by (auto simp: pstep_def Vseen_def)
  then show ?thesis by (auto elim: converse_rtranclE intro: converse_rtrancl_into_rtrancl)
qed

lemma w_notin_anc_parent:
  assumes "w \<in> Vseen"
  shows "w \<notin> {u. (ds_prnt (build_tree acyc_flow) ! w, u) \<in> (pstep (build_tree acyc_flow))\<^sup>*}"
proof
  assume "w \<in> {u. (ds_prnt (build_tree acyc_flow) ! w, u) \<in> (pstep (build_tree acyc_flow))\<^sup>*}"
  moreover have "(w, ds_prnt (build_tree acyc_flow) ! w) \<in> pstep (build_tree acyc_flow)"
    using assms by (auto simp: pstep_def Vseen_def)
  ultimately have "(w, w) \<in> (pstep (build_tree acyc_flow))\<^sup>+" by (simp add: rtrancl_into_trancl2)
  with pstep_acyclic show False by (simp add: acyclic_def)
qed

lemma anc_sub:
  "\<lbrakk>(w0, u) \<in> (pstep (build_tree acyc_flow))\<^sup>*; w0 \<in> insert vcount Vseen\<rbrakk>
     \<Longrightarrow> u \<in> insert vcount Vseen"
  by (induction rule: rtrancl_induct) (auto simp: pstep_def Vseen_def dest: build_tree_parent_in_seen)

lemma pot_repr:
  assumes "w \<in> insert vcount Vseen"
  shows "\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> A \<inter> D = {}
      \<and> A \<union> D \<subseteq> (!) (ds_par (build_tree acyc_flow)) `
        ({u. (w,u) \<in> (pstep (build_tree acyc_flow))\<^sup>*} - {vcount})
      \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1
      \<and> pval_abstract bigM (ds_pot (build_tree acyc_flow) ! w)
        = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)
      \<and> snd (ds_pot (build_tree acyc_flow) ! w)
        = (\<Sum>e\<in>A\<inter>{0..<m}. cost_list ! e) - (\<Sum>e\<in>D\<inter>{0..<m}. cost_list ! e)"
  using assms
proof(induction w rule: wf_induct_rule[OF wf_PS_conv])
  case (1 w)
  note [simp del] = NS.fst_exec_eq NS.snd_exec_eq
  let ?bt = "build_tree acyc_flow" and ?PS = "pstep (build_tree acyc_flow)"
  let ?anc = "\<lambda>x. {u. (x, u) \<in> ?PS\<^sup>*}"
  show ?case
  proof(cases "w = vcount")
    case True
    then have "?anc w = {vcount}" by (auto simp: pstep_def elim: converse_rtranclE)
    with True show ?thesis by (intro exI[of _ "{}"]) (simp add: build_tree_root_pot pval_abstract_def pval_zero_def)
  next
    case False
    with "1.prems" have "w \<in> Vseen" "w < vcount" "ds_seen ?bt ! w" by (auto simp: Vseen_def)
    let ?p = "ds_prnt ?bt ! w" and ?e = "ds_par ?bt ! w"
    have "?e \<in> (!) (ds_par ?bt) ` (?anc w - {vcount})" "{fst_all ! ?e, snd_all ! ?e} = {w, ?p}"
      using \<open>w < vcount\<close> tc_edge[of w] \<open>w \<in> Vseen\<close> by auto
    note E = this
    show ?thesis
    proof(cases "?p = vcount")
      case True
      then have "comproot_edge_ok ?bt w"
        using build_tree_comproot_inv \<open>w < vcount\<close> \<open>ds_seen ?bt ! w\<close>
          by (simp add: comproot_inv_def)
      then have "m \<le> ?e" "?e < m + Kart" "ds_pot ?bt ! w = (if art_dir w then pval_negM else pval_M)"
        by (auto simp: comproot_edge_ok_def Kart_def)
      moreover have "{ee \<in> {?e}. fst_all ! ee = vcount \<or> snd_all ! ee = vcount} = {?e}"
        using E True by (auto simp: doubleton_eq_iff)
      ultimately show ?thesis
        using E by (intro exI[of _ "if art_dir w then {} else {?e}"] exI[of _ "if art_dir w then {?e} else {}"])
          (cases "art_dir w"; simp add: cost_all_art' pval_abstract_def pval_negM_def pval_M_def Int_insert_left)
    next
      case False
      then have "?p \<in> insert vcount Vseen" "?p < vcount" "ds_seen ?bt ! ?p"
        using build_tree_parent_in_seen[of w acyc_flow] \<open>w < vcount\<close> \<open>ds_seen ?bt ! w\<close>
          by (auto simp: Vseen_def)
      note P = this \<open>w < vcount\<close> \<open>ds_seen ?bt ! w\<close>
      have "(?p, w) \<in> ?PS\<inverse>" using P by (auto simp: pstep_def)
      from "1.IH"[OF this P(1)] obtain A D where AD: "A \<subseteq> {0..<m+Kart}"
        "D \<subseteq> {0..<m+Kart}" "A \<inter> D = {}"
          "A \<union> D \<subseteq> (!) (ds_par ?bt) ` (?anc ?p - {vcount})"
          "card {ee \<in> A \<union> D. fst_all ! ee = vcount \<or> snd_all ! ee = vcount} \<le> 1"
          "pval_abstract bigM (ds_pot ?bt ! ?p) = (\<Sum>ee\<in>A. cost_all ! ee) - (\<Sum>ee\<in>D. cost_all ! ee)"
          "snd (ds_pot ?bt ! ?p) = (\<Sum>ee\<in>A\<inter>{0..<m}. cost_list ! ee)
             - (\<Sum>ee\<in>D\<inter>{0..<m}. cost_list ! ee)"
        by blast
      have "?e < m" using par_free[of w] P(2,4,5) by simp
      moreover have "ds_pot ?bt ! w
          = pval_plus (ds_pot ?bt ! ?p) (M_0, if ?p = fst_list ! ?e then cost_list ! ?e else - cost_list ! ?e)"
        using build_tree_pot[of w acyc_flow] P(2,4,5) by simp
      then have "pval_abstract bigM (ds_pot ?bt ! w)
          = pval_abstract bigM (ds_pot ?bt ! ?p) + h (if ?p = fst_list ! ?e then cost_list ! ?e else - cost_list ! ?e)"
        "snd (ds_pot ?bt ! w) = snd (ds_pot ?bt ! ?p)
           + (if ?p = fst_list ! ?e then cost_list ! ?e else - cost_list ! ?e)"
        by (simp_all only: pval_plus_M0) (simp add: pval_plus_def)
      moreover have "?e \<notin> A \<union> D"
      proof
        assume "?e \<in> A \<union> D"
        then obtain u where "u \<in> ?anc ?p - {vcount}" "?e = ds_par ?bt ! u" using AD(4) by auto
        moreover from this have "u \<in> Vseen" using anc_sub[of ?p u] P(1) by simp
        ultimately show False using par_inj[of w u] w_notin_anc_parent[of w] \<open>w \<in> Vseen\<close> by auto
      qed
      moreover have "{ee \<in> insert ?e (A \<union> D). fst_all ! ee = vcount \<or> snd_all ! ee = vcount}
          = {ee \<in> A \<union> D. fst_all ! ee = vcount \<or> snd_all ! ee = vcount}"
        using E P by auto
      moreover have "A \<union> D \<subseteq> (!) (ds_par ?bt) ` (?anc w - {vcount})"
        using anc_step[of w] \<open>w \<in> Vseen\<close> AD(4) by auto
      moreover have "finite A" "finite D" using AD(1,2) by (auto intro: rev_finite_subset[of "{0..<m+Kart}"])
      ultimately show ?thesis
        using AD E by (intro exI[of _ "if ?p = fst_list ! ?e then insert ?e A else A"]
            exI[of _ "if ?p = fst_list ! ?e then D else insert ?e D"])
          (cases "?p = fst_list ! ?e"; simp add: cost_all_real Int_insert_left)
    qed
  qed
qed

lemma pot_value_ok:
  assumes "w \<in> insert vcount Vseen"
  shows "good_pot_val_c (ds_pot (build_tree acyc_flow) ! w) \<and> pv_invar (ds_pot (build_tree acyc_flow) ! w)"
proof-
  obtain A D where AD: "A \<subseteq> {0..<m+Kart}" "D \<subseteq> {0..<m+Kart}"
      "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1"
      "pval_abstract bigM (ds_pot (build_tree acyc_flow) ! w)
         = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)"
      "snd (ds_pot (build_tree acyc_flow) ! w)
         = (\<Sum>e\<in>A\<inter>{0..<m}. cost_list ! e) - (\<Sum>e\<in>D\<inter>{0..<m}. cost_list ! e)"
    using pot_repr[OF assms] by blast
  have "\<bar>(\<Sum>e\<in>A\<inter>{0..<m}. cost_list ! e) - (\<Sum>e\<in>D\<inter>{0..<m}. cost_list ! e)\<bar>
      \<le> (\<Sum>e\<in>A\<inter>{0..<m}. \<bar>cost_list ! e\<bar>)
        + (\<Sum>e\<in>D\<inter>{0..<m}. \<bar>cost_list ! e\<bar>)"
    using sum_abs[of "(!) cost_list" "A \<inter> {0..<m}"] sum_abs[of "(!) cost_list" "D \<inter> {0..<m}"] by linarith
  also have "\<dots> \<le> (\<Sum>e\<in>{0..<m}. \<bar>cost_list ! e\<bar>)
               + (\<Sum>e\<in>{0..<m}. \<bar>cost_list ! e\<bar>)"
    by (intro add_mono sum_mono2) auto
  also have "\<dots> = 2 * sum_list (map abs cost_list)"
    by (simp add: sum_list_sum_nth atLeast0LessThan)
  finally show ?thesis using AD unfolding good_pot_val_c_def pv_invar_def by auto
qed

lemma NS_verts: "NS.\<V> = insert vcount Vseen"
  using NS_V_Varb by (simp add: Varb_def)

lemma pot_valid_build_tree: "NS.pot_valid (ds_pot (build_tree acyc_flow))"
  unfolding NS.pot_valid_def using len_pot_bt pot_value_ok by (auto simp: NS_verts Varb_def Vseen_def)

subsection \<open>Towards the spanning-tree partition (obligation 9 / init\_partition): the edge tags\<close>

text \<open>The parent edges are exactly the InTree-tagged edges. The easy inclusion (a parent edge is
      InTree) is here: an interior parent edge is a free real edge (build\_tree\_par\_edge), a component
      root's parent edge is an artificial tree edge tagged InTree (build\_tree\_crext). Every edge is
      tagged with one of the three tags (state\_total). The reverse inclusion (an InTree edge is a
      parent edge) is the free-edge coverage theorem proved further down.\<close>

lemma state_par_InTree:
  assumes "v \<in> Vseen"
  shows "state_all ! (ds_par (build_tree acyc_flow) ! v) = InTree"
proof-
  let ?e = "ds_par (build_tree acyc_flow) ! v"
  have "v < vcount" "ds_seen (build_tree acyc_flow) ! v" using assms by (auto simp: Vseen_def)
  then consider "ds_prnt (build_tree acyc_flow) ! v < vcount" | "ds_prnt (build_tree acyc_flow) ! v = vcount"
    using build_tree_parent_in_seen by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis using par_free[of v] \<open>v < vcount\<close> \<open>ds_seen (build_tree acyc_flow) ! v\<close>
      by (auto simp: state_all_real acyc_is_free_iff acyc_state_InTree_iff)
  next
    case 2
    then have "cr_ext_ok (build_tree acyc_flow) v" "comproot_edge_ok (build_tree acyc_flow) v"
      using build_tree_crext build_tree_comproot_inv \<open>v < vcount\<close>
        \<open>ds_seen (build_tree acyc_flow) ! v\<close>
      by (simp_all add: cr_ext_inv_def comproot_inv_def)
    then show ?thesis using state_all_art[of "?e - m"] by (auto simp: cr_ext_ok_def comproot_edge_ok_def Kart_def)
  qed
qed

lemma state_total:
  "e < m + Kart \<Longrightarrow> state_all ! e = InL \<or> state_all ! e = InU \<or> state_all ! e = InTree"
  by (cases "state_all ! e") auto

lemma T_sub_InTree:
  "(!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})
     \<subseteq> {e \<in> {0..<m + Kart}. state_all ! e = InTree}"
  using state_par_InTree Vseen_par_lt by (auto simp: NS_V_minus_root)

text \<open>Four of the seven still-open @{locale network_simplex_init} obligations are the store-length
      invariants; they are immediate from the array sizes (flow\_all / state\_all have length m + Kart;
      the vertex-indexed arrays have length Suc vcount, and every vertex name is below vcount).\<close>

lemma NSinit_flow_invar: "\<forall>k\<in>{0..<m + Kart}. k < length flow_all"
  by simp

lemma NSinit_es_invar_len: "\<forall>k\<in>{0..<m + Kart}. k < length state_all"
  by simp

lemma NSinit_par_invar: "\<forall>v\<in>Varb - {vcount}. v < length (ds_par (build_tree acyc_flow))"
  using build_tree_inv[of acyc_flow] by (auto simp: dfs_inv_def dfs_sized_def Varb_def Vseen_def)

lemma NSinit_dir_invar: "\<forall>v\<in>Varb - {vcount}. v < length (ds_dir (build_tree acyc_flow))"
  using build_tree_inv[of acyc_flow] by (auto simp: dfs_inv_def dfs_sized_def Varb_def Vseen_def)


section \<open>Total correctness of the solver\<close>

text \<open>The final statement about solve, phrased entirely in terms of the original network: the
      original\_network sublocales, whose edge set is 0 ..< m, whose capacities and costs are read off
      capacity\_list and cost\_list, and whose balance is b\_lookup. Neither the Kart artificial edges
      nor the big-M costs occur anywhere below; they are an internal device of the search, and the
      three verdicts speak only about the problem the caller posed.

      Optimum carries a flow on the m original edges that is a minimum-cost b\_lookup-flow
      (original\_network.is\_Opt): feasible, and no feasible flow is cheaper.

      Infeasible certifies that the original network admits no b\_lookup-flow at all, not merely that
      this run failed to find one.

      Neg\_inf\_cycle certifies neg\_infty\_cycle: a directed closed walk of original arcs, each of
      infinite capacity, whose total cost is negative, so the objective is unbounded below. This is
      the verdict of the acyclifier (acyc\_flow\_opt = None) and of an unbounded loop return alike;
      both are sound for the same reason.

      Note the asymmetry that makes the Infeasible case meaningful: it is a statement about every
      candidate flow, obtained because the artificial edges make the augmented network
      unconditionally feasible, so an augmented optimum that still loads an artificial edge is a
      proof of original infeasibility rather than a failure report.\<close>

abbreviation neg_infty_cycle :: bool where
  "neg_infty_cycle \<equiv>
  has_neg_infty_cycle original_network.make_pair
         {0..<m} (\<lambda> e. cost_list ! e)
          (\<lambda> e. if e < m then (if capacity_list ! e = - 1 then \<infinity>
            else ereal (h (capacity_list ! e))) else \<infinity>)"

subsection \<open>Bridging the executable orchestrator to the verified loop\<close>

text \<open>solve runs NS.ns\_loop\_impl from the state assembled out of the concrete reader
      tree\_st art\_tree, whereas NSinit reasons about NS.ns\_loop from the abstract Sarb. The two trees
      are the same record: Sarb is tree\_st of art\_tree once Vseen and Varb are unfolded. So the two
      starting states coincide, and the executable twin agrees with the specification loop on the
      domain, which NSinit.network\_simplex\_correct(1) supplies.\<close>

lemma Sarb_tree_st: "Sarb = tree_st art_tree"
  by (simp add: Sarb_def tree_st_def Sprnt_def sprnt_st_def Sthrd_def sthrd_st_def
                Srvth_def srvth_st_def Vseen_def vseen_st_def Varb_def varb_st_def fun_eq_iff)

text \<open>The loop always leaves notyetterm behind: it stops only at NS.ns\_optimal or
      NS.ns\_unbounded\_upd, which set the flag to success resp. unbounded. This is what upgrades
      "not unbounded" to success in the two feasible branches.\<close>

lemma ns_loop_terminates:
  assumes "NS.ns_loop_dom s"
  shows "return (NS.ns_loop s) = success \<or> return (NS.ns_loop s) = unbounded"
proof(induction rule: NS.ns_loop_induct[OF assms])
  case (1 s)
  show ?case
    by (cases s rule: NS.ns_loop_cases)
      (use 1 in \<open>auto simp: NS.ns_loop_simps[OF 1(1)] NS.ns_optimal_def NS.ns_unbounded_upd_def\<close>)
qed


subsection \<open>The acyclifier's None verdict is an original negative infinite-capacity cycle\<close>

text \<open>make\_acyclic\_none\_unbounded is reused verbatim. Its balance premise af\_feasible b f0 is
      schematic in b, since af\_feasible takes the balance as an argument rather than reading a locale
      parameter. So although flow\_list is only assumed capacity-feasible (flow\_nonneg, flow\_le\_cap)
      and is not a b\_lookup-flow, we may instantiate b with flow\_list's own balance and the premise
      becomes vacuous. No change to Acyclic\_Flow is needed.\<close>

lemma acyc_input:
  "lc_invar \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr>"
  "lc_abstract \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr> = original_network.\<V>"
  "lc_iterated \<lparr>lc_list = edged_vs_list, lc_pos = 0\<rparr> = {}" "length flow_list = m"
  "\<forall>u. out.graph.csr_iterated ((!) out.inp.B_spec) u = {}
     \<and> inc.graph.csr_iterated ((!) inc.inp.B_spec) u = {}"
  using distinct_vs_list length_flow length_edges out.graph.csr_init_iterated inc.graph.csr_init_iterated
  by (simp_all add: lc_invar_def edged_vs_list_def lc_abstract_def V_orig_eq_edged lc_iterated_def)

lemma af_feasible_flow_list: "af_feasible (\<lambda>v. - original_network.ex (h \<circ> (!) flow_list) v) flow_list"
  by (rule af_feasibleI[OF af_cap_feasible_flow_list]) simp

lemma h_foldr_cost_list:
  "foldr (\<lambda>e. (+) (h (cost_list ! e))) D 0 = h (foldr (\<lambda>e. (+) (cost_list ! e)) D 0)"
  by (induction D) (simp_all add: h_add)

lemma acyc_none_neg_cycle:
  assumes "acyc_flow_opt = None" shows neg_infty_cycle
proof-
  from make_acyclic_none_unbounded[OF multigraph_inv_csr acyc_input(4) af_feasible_flow_list acyc_input(1)
      equalityD1[OF acyc_input(2)]] assms
  obtain D where "closed_w (original_network.make_pair ` {0..<m}) (map original_network.make_pair D)"
      "foldr (\<lambda>e. (+) (h (cost_list ! e))) D 0 < 0" "set D \<subseteq> {0..<m}"
      "\<forall>e\<in>set D. (if e < m then if capacity_list ! e = - 1 then \<infinity>
                              else ereal (h (capacity_list ! e)) else \<infinity>)
         = PInfty"
    unfolding has_neg_infty_cycle_def acyc_flow_opt_def by blast
  thus neg_infty_cycle using h_foldr_cost_list[of D] unfolding has_neg_infty_cycle_def by (intro exI[of _ D]) auto
qed

subsection \<open>An augmented {\isasyminfinity}-cycle is already an original {\isasyminfinity}-cycle\<close>

text \<open>Every artificial edge carries a finite capacity: tail\_edge\_ok\_build\_tree pins it to
      art\_tree\_cap subj or art\_flow subj, both non-negative, hence never the -1 sentinel that decodes
      to an infinite capacity. So a cycle all of whose arcs have infinite capacity cannot touch the
      artificial part, and on the original part the endpoint, cost and capacity arrays agree by
      fst\_all\_real, snd\_all\_real, cap\_all\_real and cost\_all\_real. The artificial device therefore
      cannot manufacture an unboundedness verdict of its own.\<close>

lemma cap_all_art_fin:
  assumes "m \<le> e" "e < m + Kart" shows "cap_all ! e \<noteq> - 1"
proof-
  have k: "e - m < Kart" using assms by simp
  have "0 \<le> ds_acap (build_tree acyc_flow) ! (e - m)"
    using tail_edge_ok_build_tree[OF k] by (auto simp: tail_edge_ok_def art_tree_cap_def art_flow_def)
  with cap_all_art[OF k] assms show ?thesis by simp
qed

lemma closed_w_restrict:
  assumes "closed_w E p" "set p \<subseteq> E'"
  shows "closed_w E' p"
proof-
  obtain u where "awalk E u p u" "0 < length p" using assms(1) by (auto simp: closed_w_def)
  moreover from this obtain a b q where "p = (a, b) # q" by (cases p) auto
  ultimately show ?thesis using assms(2) by (auto simp: closed_w_def awalk_def dVs_def)
qed

text \<open>Note. The simplifier calls below are deliberately "simp only". Under the NS interpretation
      the endpoint bridge NS.fst\_exec\_eq instantiates to

        e : {0..<m+Kart} ==> fst\_all ! e = (if e < m + Kart then fst\_all ! e else ...)

      whose right-hand side contains its own left-hand side. As a [simp] rule it rewrites fst\_all ! e
      to itself forever, so any plain simp on a goal mentioning fst\_all ! e or snd\_all ! e with
      e < m + Kart dischargeable diverges. The same holds for NS.snd\_exec\_eq. Declaring the two
      [simp del] removes the loop, but the fallout on existing proofs has not been measured, so the
      workaround here is local: unfold with simp only and discharge the conditions by hand.\<close>

lemma make_pair_real: "e < m \<Longrightarrow> NS.make_pair e = original_network.make_pair e"
  using fst_all_real[of e] snd_all_real[of e]
  by (simp add: NS.make_pair_def original_network.make_pair_def del: NS.fst_exec_eq NS.snd_exec_eq)

lemma cost_fold_real:
  "set D \<subseteq> {0..<m} \<Longrightarrow> foldr (\<lambda>e. (+) (cost_all ! e)) D 0
     = h (foldr (\<lambda>e. (+) (cost_list ! e)) D 0)"
  by (induction D) (simp_all add: cost_all_real h_add)

lemma aug_neg_cycle_orig:
  assumes "has_neg_infty_cycle NS.make_pair {0..<m + Kart} ((!) cost_all)
             (\<lambda>e. if e < m + Kart then if cap_all ! e = - 1 then \<infinity>
              else ereal (h (cap_all ! e)) else \<infinity>)"
  shows neg_infty_cycle
proof-
  obtain D where cw: "closed_w (NS.make_pair ` {0..<m + Kart}) (map NS.make_pair D)"
    and cst: "foldr (\<lambda>e. (+) (cost_all ! e)) D 0 < 0"
    and sD: "set D \<subseteq> {0..<m + Kart}"
    and inf: "\<forall>e \<in> set D. (if e < m + Kart then if cap_all ! e = - 1 then \<infinity>
                            else ereal (h (cap_all ! e)) else \<infinity>) = PInfty"
    using assms unfolding has_neg_infty_cycle_def by blast
  have Dm: "e < m \<and> capacity_list ! e = - 1" if "e \<in> set D" for e
    using inf[rule_format, of e] sD that cap_all_art_fin[of e] cap_all_real[of e]
    by (cases "e < m") (auto split: if_splits)
  then have "set D \<subseteq> {0..<m}" "map NS.make_pair D = map original_network.make_pair D"
    by (auto simp: make_pair_real)
  moreover have "closed_w (original_network.make_pair ` {0..<m}) (map original_network.make_pair D)"
    by (rule closed_w_restrict[OF cw[unfolded calculation(2)]]) (use calculation(1) in auto)
  ultimately show neg_infty_cycle unfolding has_neg_infty_cycle_def using cst Dm cost_fold_real[of D] by auto
qed

subsection \<open>The big-M transfer\<close>

text \<open>The two feasible verdicts both rest on transferring the augmented optimum
      NSinit.network\_simplex\_correct(3) back to the original network (the classical big-M argument).

      aug\_opt\_zero\_art\_orig\_opt: if the augmented optimum loads no artificial edge it restricts to an
      original b\_lookup-flow, and it is optimal there because every original b\_lookup-flow extends to
      an augmented one of equal cost (put 0 on the artificial edges, which is feasible at the root
      because b\_lookup vcount = 0). This direction needs no bound on bigM.

      aug\_opt\_nonzero\_art\_infeasible: if the optimum g loads an artificial edge while an original
      b\_lookup-flow f exists, the difference of g and the zero-extension of f is a non-negative residual
      circulation whose support contains the reverse arc of the loaded artificial edge but no forward
      artificial arc. A cycle of its decomposition through that reverse arc is an augmenting cycle of g
      with negative cost, because bigM dominates twice the total absolute original cost
      (neg\_res\_cost) --- contradicting the optimality of g.\<close>

text \<open>The loop carries its invariant to the terminal state, so the returned flow array is still long
      enough to be truncated at m. Only the two recursive branches do any work: the terminal ones just
      set the return flag, and ns\_invar does not mention that field.

      The simp del below is not optional. Under the NS interpretation NS.fst\_exec\_eq and
      NS.snd\_exec\_eq are [simp] rules whose right-hand side contains their own left-hand side (see the
      note further down), and unfolding ns\_invar\_tree\_def exposes fst\_all ! ... , at which point a
      plain simp diverges.\<close>

lemma ns_invar_ret: "NS.ns_invar (s\<lparr>return := r\<rparr>) = NS.ns_invar s"
  by (simp del: NS.fst_exec_eq NS.snd_exec_eq
           add: NS.ns_invar_def NS.ns_invar_impl_def NS.ns_invar_bflow_def NS.ns_invar_partition_def
                NS.ns_invar_flow_fits_def NS.ns_invar_pot_fits_def NS.ns_invar_strict_def
                NS.ns_invar_tree_def NS.ns_invar_selfloop_def NS.ns_L_of_def NS.ns_U_of_def
                NS.par_edge_def NS.par_up_def NS.par_vx_def)

lemma ns_loop_invar:
  assumes "NS.ns_loop_dom s"
  shows "NS.ns_invar s \<Longrightarrow> NS.ns_invar (NS.ns_loop s)"
proof(induction rule: NS.ns_loop_induct[OF assms])
  case IH: (1 s)
  show ?case
    by (cases s rule: NS.ns_loop_cases)
       (use IH NS.ns_flip_preservation(1)[OF IH(4)] NS.ns_pivot_preservation(1)[OF IH(4)] in
        \<open>simp_all add: NS.ns_loop_simps[OF IH(1)] NS.ns_optimal_def NS.ns_unbounded_upd_def ns_invar_ret\<close>)
qed



text \<open>Supporting facts for the transfer between the augmented and original networks. They all rest on
      the same two observations: on the original edges 0 ..< m the augmented arrays coincide with the
      input lists (fst\_all\_real, snd\_all\_real, cap\_all\_real, cost\_all\_real), and a flow that is zero on
      the artificial edges m ..< m + Kart contributes nothing there. Several proofs carry
      "note [simp del] = NS.fst\_exec\_eq NS.snd\_exec\_eq" because those two rewrite fst\_all ! e /
      snd\_all ! e to themselves under the NS interpretation (see the note further down).\<close>

lemma delta_plus_orig: "original_network.delta_plus v = NS.delta_plus v \<inter> {0..<m}"
  and delta_minus_orig: "original_network.delta_minus v = NS.delta_minus v \<inter> {0..<m}"
  by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq
           simp add: original_network.delta_plus_def NS.delta_plus_def
                     original_network.delta_minus_def NS.delta_minus_def fst_all_real snd_all_real)

lemma delta_fin: "finite (NS.delta_plus v)" "finite (NS.delta_minus v)"
  by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: NS.delta_plus_def NS.delta_minus_def)

text \<open>For a flow that vanishes on the artificial edges the augmented and original excesses agree at
      every vertex, because the delta sets differ only by artificial edges, which carry no flow.\<close>

lemma sum_art_zero:
  assumes "X \<subseteq> {0..<m + Kart}" "finite X"
    "\<And>k. \<lbrakk>m \<le> k; k < m + Kart\<rbrakk> \<Longrightarrow> g k = 0"
  shows "(\<Sum>e\<in>X. g e) = (\<Sum>e\<in>X \<inter> {0..<m}. g e)"
  using assms(1) by (intro sum.mono_neutral_right assms(2)) (auto intro!: assms(3))

lemma NS_delta_sub: "NS.delta_plus v \<subseteq> {0..<m + Kart}" "NS.delta_minus v \<subseteq> {0..<m + Kart}"
  by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: NS.delta_plus_def NS.delta_minus_def)

lemma ex_agree:
  assumes "\<And>k. \<lbrakk>m \<le> k; k < m + Kart\<rbrakk> \<Longrightarrow> g k = 0"
  shows "NS.ex g v = original_network.ex g v"
  using NS_delta_sub[of v] sum_art_zero[of "NS.delta_plus v" g] sum_art_zero[of "NS.delta_minus v" g] delta_fin assms
  by (simp add: NS.ex_def original_network.ex_def delta_plus_orig delta_minus_orig)

text \<open>Likewise the augmented and original costs of such a flow agree.\<close>

lemma cost_agree:
  "(\<And>k. \<lbrakk>m \<le> k; k < m + Kart\<rbrakk> \<Longrightarrow> g k = 0)
     \<Longrightarrow> NS.\<C> g = original_network.\<C> g"
  using sum_art_zero[of "{0..<m + Kart}" "\<lambda>e. g e * cost_all ! e"]
  by (simp add: NS.\<C>_def original_network.\<C>_def cost_all_real)

text \<open>An augmented flow restricts to an original flow: dropping the (unused) artificial edges keeps
      capacity-compliance and, by ex\_agree at every original vertex, the balances.\<close>

lemma isuflow_restrict:
  assumes "NS.isuflow g" shows "original_network.isuflow g"
  unfolding original_network.isuflow_def
proof
  fix e assume "e \<in> {0..<m}"
  then show "ereal (g e) \<le> (if e < m then if capacity_list ! e = - 1 then \<infinity>
                                else ereal (h (capacity_list ! e))
      else \<infinity>) \<and> 0 \<le> g e"
    using bspec[OF assms[unfolded NS.isuflow_def], of e] by (simp add: cap_all_real split: if_splits)
qed

lemma bflow_restrict:
  "\<lbrakk>NS.isbflow g (\<lambda>v. h (b_lookup v));
            \<And>k. \<lbrakk>m \<le> k; k < m + Kart\<rbrakk> \<Longrightarrow> g k = 0\<rbrakk>
   \<Longrightarrow> original_network.isbflow g (\<lambda>v. h (b_lookup v))"
  using isuflow_restrict ex_agree[of g] NS_verts Vseen_eq_V
  by (intro original_network.isbflowI) (auto simp: NS.isbflow_def)

text \<open>Conversely an original flow extends to an augmented one by putting zero on the artificial edges.
      Capacity holds (artificial capacities are non-negative), the balances hold at every original
      vertex, and at the root because b\_lookup vcount = 0. The cost is unchanged.\<close>

lemma orig_ex_ext:
  "original_network.ex (\<lambda>e. if e < m then f e else 0) v = original_network.ex f v"
proof-
  have "\<And>e. e \<in> original_network.delta_plus v \<Longrightarrow> (if e < m then f e else 0) = f e"
    by (auto simp: original_network.delta_plus_def)
  moreover have "\<And>e. e \<in> original_network.delta_minus v \<Longrightarrow> (if e < m then f e else 0) = f e"
    by (auto simp: original_network.delta_minus_def)
  ultimately show ?thesis
    by (simp add: original_network.ex_def cong: sum.cong)
qed

lemma orig_ex_notin_V:
  assumes "v \<notin> set vs_list"
  shows "original_network.ex f v = 0"
proof-
  have "original_network.delta_plus v = {}" "original_network.delta_minus v = {}"
    using assms fst_list_nth_vertex snd_list_nth_vertex
    by (auto simp: original_network.delta_plus_def original_network.delta_minus_def original_network.make_pair_def)
  thus ?thesis by (simp add: original_network.ex_def)
qed

lemma isuflow_ext:
  assumes "original_network.isuflow f"
  shows "NS.isuflow (\<lambda>e. if e < m then f e else 0)"
  unfolding NS.isuflow_def
proof
  fix e assume "e \<in> {0..<m + Kart}"
  with bspec[OF assms[unfolded original_network.isuflow_def], of e] cap_all_nonneg[of e]
  show "ereal (if e < m then f e else 0)
      \<le> (if e < m + Kart then (if cap_all ! e = - 1 then \<infinity>
                                   else ereal (h (cap_all ! e))) else \<infinity>)
      \<and> 0 \<le> (if e < m then f e else 0)"
    by (cases "e < m") (auto simp: cap_all_real zero_ereal_def)
qed

lemma bflow_ext:
  assumes "original_network.isbflow f (\<lambda>v. h (b_lookup v))"
  shows "NS.isbflow (\<lambda>e. if e < m then f e else 0) (\<lambda>v. h (b_lookup v))"
proof(rule NS.isbflowI)
  show "NS.isuflow (\<lambda>e. if e < m then f e else 0)"
    using assms isuflow_ext by (auto simp: original_network.isbflow_def)
next
  fix v assume "v \<in> NS.\<V>"
  then have "v = vcount \<or> v \<in> original_network.\<V>" using NS_verts Vseen_eq_V by auto
  moreover have "vcount \<notin> set vs_list" using vs_less_vcount by blast
  ultimately show "- NS.ex (\<lambda>e. if e < m then f e else 0) v = h (b_lookup v)"
    using assms ex_agree[of "\<lambda>e. if e < m then f e else 0" v] orig_ex_ext[of f v] orig_ex_notin_V[of vcount f]
      b_lookup_root
    by (auto simp: original_network.isbflow_def)
qed

lemma cost_ext: "NS.\<C> (\<lambda>e. if e < m then f e else 0) = original_network.\<C> f"
  using cost_agree[of "\<lambda>e. if e < m then f e else 0"] by (simp add: original_network.\<C>_def)

lemma aug_opt_zero_art_orig_opt:
  assumes "NS.is_Opt (\<lambda>v. h (b_lookup v)) g"
    "\<And>k. \<lbrakk>m \<le> k; k < m + Kart\<rbrakk> \<Longrightarrow> g k = 0"
  shows "original_network.is_Opt (\<lambda>v. h (b_lookup v)) g"
proof(rule original_network.is_OptI)
  have "NS.isbflow g (\<lambda>v. h (b_lookup v))" using assms(1) by (simp add: NS.is_Opt_def)
  thus "original_network.isbflow g (\<lambda>v. h (b_lookup v))" using assms(2) by (rule bflow_restrict)
  fix f' assume "original_network.isbflow f' (\<lambda>v. h (b_lookup v))"
  hence "NS.\<C> g \<le> NS.\<C> (\<lambda>e. if e < m then f' e else 0)" using assms(1) bflow_ext
    by (simp add: NS.is_Opt_def)
  thus "original_network.\<C> f' \<ge> original_network.\<C> g" using cost_agree[of g] assms(2) cost_ext by simp
qed

text \<open>Note the shape of the second premise. Stating it with a free k, as in

    and nz: "m <= k" "k < m + Kart" "g k ~= 0"

  exports k as a schematic ?k, so the premise becomes ?g ?k ~= 0: a schematic function applied to a
  schematic argument. Resolving that against a concrete fact is a flex-flex higher-order unification
  problem, and instantiating the lemma with OF then diverges. Binding k with an existential keeps the
  occurrence as ?g applied to a bound variable, which is a Miller pattern and unifies in one step.
  The sibling lemma above is safe for the same reason: its k is bound by the meta-quantifier.\<close>

lemma redge_FB_props:
  "finite {F e |e. e < (m::nat)}" "finite {B e |e. e < (m::nat)}" "{F e |e. e < m} \<inter> {B e |e. e < m} = {}"
  "inj_on F X" "inj_on B X"
  by (auto simp: inj_on_def)

lemma abs_cost_orig_bound:
  "(\<Sum>c \<in> ({F e |e. e < m} \<union> {B e |e. e < m}). \<bar>NS.\<cc> c\<bar>)
     = 2 * h (sum_list (map abs cost_list))"
proof-
  have "(\<Sum>e \<in> {e. e < m}. \<bar>cost_all ! e\<bar>) = (\<Sum>e \<in> {0..<m}. h \<bar>cost_list ! e\<bar>)"
    by (auto simp: cost_all_real h_abs atLeast0LessThan lessThan_def intro: sum.cong)
  also have "\<dots> = h (sum_list (map abs cost_list))" by (simp add: h_sum sum_list_sum_nth atLeast0LessThan)
  moreover have "(\<Sum>c \<in> {F e |e. e < m}. \<bar>NS.\<cc> c\<bar>)
                   = (\<Sum>e \<in> {e. e < m}. \<bar>cost_all ! e\<bar>)"
    by (simp add: setcompr_eq_image sum.reindex[OF redge_FB_props(4)])
  moreover have "(\<Sum>c \<in> {B e |e. e < m}. \<bar>NS.\<cc> c\<bar>)
                   = (\<Sum>e \<in> {e. e < m}. \<bar>cost_all ! e\<bar>)"
    by (simp add: setcompr_eq_image sum.reindex[OF redge_FB_props(5)])
  ultimately show ?thesis
    by (subst sum.union_disjoint[OF redge_FB_props(1-3)]) simp
qed

text \<open>A distinct residual arc list living in the augmented residual graph, containing at least one
      reverse artificial arc and no forward artificial arc, has strictly negative residual cost: each
      reverse artificial arc contributes -bigM, while the original arcs together contribute at most
      2 * sum\_list (map abs cost\_list) in absolute value, and bigM dominates that.\<close>

lemma neg_res_cost:
  assumes "distinct cs" "set cs \<subseteq> NS.\<EE>"
    "\<And>k'. \<lbrakk>m \<le> k'; k' < m + Kart\<rbrakk> \<Longrightarrow> F k' \<notin> set cs"
    "B k \<in> set cs" "m \<le> k" "k < m + Kart"
  shows "NS.\<CC> cs < 0"
proof-
  let ?A = "{c \<in> set cs. \<exists>k'. m \<le> k' \<and> k' < m + Kart \<and> c = B k'}"
  have "set cs - ?A \<subseteq> {F e |e. e < m} \<union> {B e |e. e < m}"
  proof
    fix c assume c: "c \<in> set cs - ?A"
    then obtain d where "d < m + Kart" "c = F d \<or> c = B d" using assms(2) by (auto simp: NS.\<EE>_def)
    thus "c \<in> {F e |e. e < m} \<union> {B e |e. e < m}" using c assms(3)[of d] by (cases "d < m") auto
  qed
  hence "(\<Sum>c \<in> set cs - ?A. NS.\<cc> c) \<le> 2 * h (sum_list (map abs cost_list))"
    unfolding abs_cost_orig_bound[symmetric]
    by (intro order.trans[OF sum_mono sum_mono2]) auto
  moreover have "(\<Sum>c \<in> ?A. NS.\<cc> c) = (\<Sum>c \<in> ?A. - bigM)"
    by (rule sum.cong) (auto simp: cost_all_art')
  moreover have "bigM \<le> bigM * real (card ?A)"
  proof-
    have "B k \<in> ?A" "finite ?A" using assms(4-6) by auto
    hence "1 \<le> real (card ?A)" by (simp add: Suc_le_eq card_gt_0_iff, blast)
    thus ?thesis using bigM_pos by simp
  qed
  moreover have "NS.\<CC> cs = (\<Sum>c \<in> ?A. NS.\<cc> c) + (\<Sum>c \<in> set cs - ?A. NS.\<cc> c)"
    by (simp add: NS.\<CC>_def sum.subset_diff[of ?A "set cs"])
  moreover have "(\<Sum>c \<in> ?A. - bigM) = - bigM * real (card ?A)" by simp
  ultimately show ?thesis using bigM_gt h_nonneg[OF sabs_nonneg] by linarith
qed

lemma aug_opt_nonzero_art_infeasible:
  assumes "NS.is_Opt (\<lambda>v. h (b_lookup v)) g" "\<exists>k. m \<le> k \<and> k < m + Kart \<and> g k \<noteq> 0"
  shows "\<nexists> f. original_network.isbflow f (\<lambda>v. h (b_lookup v))"
proof
  assume "\<exists>f. original_network.isbflow f (\<lambda>v. h (b_lookup v))"
  then obtain f where f: "NS.isbflow (\<lambda>e. if e < m then f e else 0) (\<lambda>v. h (b_lookup v))"
    using bflow_ext by blast
  interpret rf: flow_network where fst = NS.fstv and snd = NS.sndv
      and create_edge = NS.create_edge_residual and \<E> = "NS.\<EE>" and \<u> = "\<lambda> _. PInfty"
    using NS.make_pair NS.create_edge NS.E_not_empty NS.oedge_on_\<EE>
    by (auto simp add: NS.finite_\<EE> NS.make_pair[OF refl refl] NS.create_edge
                       cost_flow_network_def flow_network_axioms_def flow_network_def multigraph_def)
  obtain k where k: "m \<le> k" "k < m + Kart" "g k \<noteq> 0" using assms(2) by blast
  let ?d = "NS.difference (\<lambda>e. if e < m then f e else 0) g"
  have g: "NS.isbflow g (\<lambda>v. h (b_lookup v))" using assms(1) by (simp add: NS.is_Opt_def)
  hence gnn: "0 \<le> g e" if "e < m + Kart" for e using that by (auto simp: NS.isbflow_def NS.isuflow_def)
  have "?d (B k) = g k" "0 < g k" "B k \<in> NS.\<EE>" using k gnn[OF k(2)] by (auto simp: NS.\<EE>_def)
  hence supp: "B k \<in> rf.support ?d" "0 < ?d (B k)" by (simp_all add: rf.support_def)
  have nn: "rf.flow_non_neg ?d" using NS.diff_non_neg by (simp add: rf.flow_non_neg_def)
  hence "rf.Abs ?d > 0" using supp
    by (auto simp: rf.Abs_def rf.flow_non_neg_def rf.support_def intro: sum_pos2[of NS.\<EE> "B k"] NS.finite_\<EE>)
  then obtain css ws where cw: "\<forall>cs\<in>set css. rf.flowcycle ?d cs
                                  \<and> set cs \<subseteq> rf.support ?d \<and> distinct cs"
      "\<forall>e\<in>NS.\<EE>. ?d e = (\<Sum>i<length css. if e \<in> set (css ! i) then ws ! i else 0)"
    using rf.flowcycle_decomposition[OF nn _ NS.diff_is_res_circ[OF g f] _ refl] supp(1) by blast
  have "\<exists>i<length css. B k \<in> set (css ! i)"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence "(\<Sum>i<length css. if B k \<in> set (css ! i) then ws ! i else 0) = 0" by (intro sum.neutral) auto
    thus False using cw(2) supp by (auto simp: rf.support_def)
  qed
  then obtain i where i: "i < length css" "B k \<in> set (css ! i)" by blast
  hence cs: "rf.flowcycle ?d (css ! i)" "set (css ! i) \<subseteq> rf.support ?d"
    "distinct (css ! i)" using cw(1) by auto
  hence E: "set (css ! i) \<subseteq> NS.\<EE>" by (auto simp: rf.support_def)
  have "NS.\<CC> (css ! i) < 0"
  proof(rule neg_res_cost[OF cs(3) E _ i(2) k(1,2)])
    fix k' assume "m \<le> k'" "k' < m + Kart"
    hence "?d (F k') = 0" using gnn by simp
    thus "F k' \<notin> set (css ! i)" using cs(2) by (auto simp: rf.support_def)
  qed
  moreover have "0 < NS.rcap g e" if "e \<in> set (css ! i)" for e
    using that cs(2) NS.pos_difference_pos_rcap[of g "\<lambda>e. if e < m then f e else 0" e] g f
    by (auto simp: rf.support_def NS.isbflow_def)
  hence "0 < NS.Rcap g (set (css ! i))" by (auto simp: NS.Rcap_def zero_less_iff_neq_zero)
  moreover have "NS.prepath (css ! i)" "NS.fstv (hd (css ! i)) = NS.sndv (last (css ! i))"
    using cs(1) by (auto simp: rf.flowcycle_def rf.flowpath_def NS.prepath_def rf.multigraph_path_def
        NS.to_vertex_pair_fst_snd)
  ultimately have "NS.augcycle g (css ! i)" using cs(3) E by (simp add: NS.augcycle_def NS.augpath_def)
  thus False using NS.min_cost_flow_no_augcycle[OF assms(1)] by blast
qed

text \<open>original\_network.is\_Opt only reads the edges 0 ..< m, so truncating the augmented flow with
      take m does not change it.\<close>

lemma is_Opt_take:
  assumes "m \<le> length f"
  shows "original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth (take m f))
           = original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth f)"
proof
  have agree: "(h \<circ> nth (take m f)) e = (h \<circ> nth f) e" if "e \<in> {0..<m}" for e using that assms
    by (simp add: comp_def)
  assume "original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth (take m f))"
  thus "original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth f)"
    by (rule original_network.is_Opt_cong[rotated 2]) (use agree in auto)
next
  have agree: "(h \<circ> nth f) e = (h \<circ> nth (take m f)) e" if "e \<in> {0..<m}" for e using that assms
    by (simp add: comp_def)
  assume "original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth f)"
  thus "original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth (take m f))"
    by (rule original_network.is_Opt_cong[rotated 2]) (use agree in auto)
qed

subsection \<open>Total correctness of solve\<close>

text \<open>Toward free-edge coverage (obligation 9, the reverse inclusion). Under acyclicity the acyclified
      flow has no closed pre-path of distinct free arcs (flow\_no\_free\_cycle). The engine below packages
      that as: any closed walk of distinct free real edges is impossible. Coverage will feed it the
      cycle formed by an uncovered free edge together with the interior tree path between its endpoints.\<close>

lemma is_free_af_arc_free: "\<lbrakk>e < m; is_free acyc_flow e\<rbrakk> \<Longrightarrow> af_arc_free acyc_flow e"
  using acyc_state_InTree_iff[of e]
  by (simp add: is_free_def af_arc_free_def Let_def)

lemma free_walk_no_cycle:
  assumes "original_network.acyclic_flow (h \<circ> nth acyc_flow)" "C \<noteq> []"
    "\<And>a. a \<in> set C \<Longrightarrow> original_network.oedge a < m
       \<and> is_free acyc_flow (original_network.oedge a)"
    "distinct (map original_network.oedge C)" "set C \<subseteq> original_network.\<EE>" "original_network.prepath C"
    "original_network.fstv (hd C) = original_network.sndv (last C)"
  shows False
proof-
  have "\<forall>a\<in>set C. af_arc_free acyc_flow (original_network.oedge a)"
    using assms(3) is_free_af_arc_free by blast
  thus False using flow_no_free_cycle[OF acyc_flow_nonneg acyc_flow_le_cap assms(1)] assms(4-) by blast
qed

subsection \<open>Free-edge coverage: the scan-completeness invariant of the DFS (obligation 9, core)\<close>

text \<open>scan\_complete tracks that every free edge already scanned from a seen vertex --- one that is no
      longer among the remaining edges of the vertex's iterator --- has its far endpoint seen, and that a
      finished (seen, off-stack) vertex has no remaining edges. It needs no acyclicity --- it is pure DFS
      scan structure --- and is preserved by each build\_dfs step. At the end (empty stack) it says every
      free neighbour of every seen vertex is seen, which is what lets an uncovered free edge be closed
      into a free cycle for the engine.\<close>

abbreviation "orem c x \<equiv> csr_blocks.csr_remaining ((!) (fst (free_out acyc_flow)))
                (snd (free_out acyc_flow)) c x"
abbreviation "irem c x \<equiv> csr_blocks.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) c x"

definition scan_complete :: "'n dfs_state \<Rightarrow> bool" where
  "scan_complete s \<longleftrightarrow> (\<forall>v<vcount. ds_seen s ! v \<longrightarrow>
     (\<forall>e<m. is_free acyc_flow e \<and> fst_list ! e = v \<and> e \<notin> orem (ds_oc s) v
      \<longrightarrow> ds_seen s ! (snd_list ! e))
   \<and> (\<forall>e<m. is_free acyc_flow e \<and> snd_list ! e = v \<and> e \<notin> irem (ds_ic s) v
           \<longrightarrow> ds_seen s ! (fst_list ! e))
   \<and> (v \<notin> set (ds_stk s) \<longrightarrow> orem (ds_oc s) v = {} \<and> irem (ds_ic s) v = {}))"

text \<open>The generic preservation step: seen vertices stay seen, a freshly seen vertex is pushed with a
      full iterator, an edge leaving a remaining set has its far endpoint seen, and a vertex that is
      finished afterwards was finished before (with no new remaining edges) or has an empty iterator.\<close>

lemma scan_complete_upd:
  assumes "scan_complete s" "\<And>x. ds_seen s ! x \<Longrightarrow> ds_seen t ! x"
    "\<And>x. \<lbrakk>x < vcount; ds_seen t ! x; \<not> ds_seen s ! x\<rbrakk>
       \<Longrightarrow> x \<in> set (ds_stk t)
       \<and> orem (ds_oc t) x = {e. e < m \<and> fst_list ! e = x \<and> is_free acyc_flow e}
       \<and> irem (ds_ic t) x = {e. e < m \<and> snd_list ! e = x \<and> is_free acyc_flow e}"
    "\<And>x e. \<lbrakk>x < vcount; ds_seen s ! x; e \<in> orem (ds_oc s) x; e \<notin> orem (ds_oc t) x\<rbrakk>
       \<Longrightarrow> ds_seen t ! (snd_list ! e)"
    "\<And>x e. \<lbrakk>x < vcount; ds_seen s ! x; e \<in> irem (ds_ic s) x; e \<notin> irem (ds_ic t) x\<rbrakk>
       \<Longrightarrow> ds_seen t ! (fst_list ! e)"
    "\<And>x. \<lbrakk>x < vcount; ds_seen s ! x; x \<notin> set (ds_stk t)\<rbrakk> \<Longrightarrow>
       (x \<notin> set (ds_stk s) \<and> orem (ds_oc t) x \<subseteq> orem (ds_oc s) x
        \<and> irem (ds_ic t) x \<subseteq> irem (ds_ic s) x)
       \<or> (orem (ds_oc t) x = {} \<and> irem (ds_ic t) x = {})"
  shows "scan_complete t"
  unfolding scan_complete_def
proof(intro allI impI conjI)
  fix x e assume "x < vcount" "ds_seen t ! x" "e < m"
    "is_free acyc_flow e \<and> fst_list ! e = x \<and> e \<notin> orem (ds_oc t) x"
  thus "ds_seen t ! (snd_list ! e)"
    using assms(1)[unfolded scan_complete_def, rule_format, of x] assms(2) assms(3)[of x] assms(4)[of x e]
    by (cases "ds_seen s ! x") blast+
next
  fix x e assume "x < vcount" "ds_seen t ! x" "e < m"
    "is_free acyc_flow e \<and> snd_list ! e = x \<and> e \<notin> irem (ds_ic t) x"
  thus "ds_seen t ! (fst_list ! e)"
    using assms(1)[unfolded scan_complete_def, rule_format, of x] assms(2) assms(3)[of x] assms(5)[of x e]
    by (cases "ds_seen s ! x") blast+
next
  fix x assume "x < vcount" "ds_seen t ! x" "x \<notin> set (ds_stk t)"
  thus "orem (ds_oc t) x = {}" "irem (ds_ic t) x = {}"
    using assms(1)[unfolded scan_complete_def, rule_format, of x] assms(3)[of x] assms(6)[of x] by blast+
qed

text \<open>The iterators restart at a pushed vertex: everything it owns is remaining.\<close>

lemma dfs_push_remaining:
  assumes "w < vcount"
  shows "orem (ds_oc (dfs_push s w)) w = {e. e < m \<and> fst_list ! e = w \<and> is_free acyc_flow e}"
    and "irem (ds_ic (dfs_push s w)) w = {e. e < m \<and> snd_list ! e = w \<and> is_free acyc_flow e}"
    and "j \<noteq> w \<Longrightarrow> orem (ds_oc (dfs_push s w)) j = orem (ds_oc s) j"
    and "j \<noteq> w \<Longrightarrow> irem (ds_ic (dfs_push s w)) j = irem (ds_ic s) j"
proof-
  interpret F: csr_ranges vcount "{..<vcount}" out.inp.B_spec "(!) (fst (free_out acyc_flow))"
    "snd (free_out acyc_flow)"
    by (rule free_out(1))
  interpret G: csr_ranges vcount "{..<vcount}" inc.inp.B_spec "(!) (fst (free_in acyc_flow))" "snd (free_in acyc_flow)"
    by (rule free_in(1))
  show "orem (ds_oc (dfs_push s w)) w = {e. e < m \<and> fst_list ! e = w \<and> is_free acyc_flow e}"
    "irem (ds_ic (dfs_push s w)) w = {e. e < m \<and> snd_list ! e = w \<and> is_free acyc_flow e}"
    "j \<noteq> w \<Longrightarrow> orem (ds_oc (dfs_push s w)) j = orem (ds_oc s) j"
    "j \<noteq> w \<Longrightarrow> irem (ds_ic (dfs_push s w)) j = irem (ds_ic s) j"
    using assms free_out(2) free_in(2)
    by (simp_all add: dfs_push_def F.csr_reset_remaining G.csr_reset_remaining
        F.csr_reset_remaining_other G.csr_reset_remaining_other)
qed

lemma discover_seen_eq: "ds_seen (dfs_discover s v w e) = (ds_seen s)[w := True]"
  by (simp add: dfs_discover_def dfs_push_def Let_def)

lemma bd_upd1_scan_complete:
  assumes "dfs_inv acyc_flow s" "scan_complete s" "bd_call1_conds acyc_flow s"
  shows "scan_complete (bd_upd1 acyc_flow s)"
proof-
  from assms(3) obtain v rest where stk: "ds_stk s = v # rest"
    and has: "csr_blocks.csr_has ((!) (fst (free_out acyc_flow))) (ds_oc s) v"
    by (auto simp: bd_call1_conds_def split: list.splits)
  have "dfs_wf acyc_flow s" "length (ds_seen s) = Suc vcount" using assms(1)
    by (simp_all add: dfs_inv_def dfs_sized_def)
  note S = bd_out_step[OF this(1) stk has] this
  define e where "e = csr_blocks.csr_current (snd (free_out acyc_flow)) (ds_oc s) v"
  define c' where "c' = csr_blocks.csr_move ((!) (fst (free_out acyc_flow))) (ds_oc s) v"
  define w where "w = snd_list ! e"
  have up: "bd_upd1 acyc_flow s =
              (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr>
               else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (simp add: bd_upd1_def stk Let_def e_def c'_def w_def)
  have "w < vcount" using S(4) by (simp add: w_def e_def)
  have rem: "orem c' x = (if x = v then orem (ds_oc s) v - {e} else orem (ds_oc s) x)" for x
    using S(7,8)[folded e_def c'_def] by simp
  show ?thesis
  proof(cases "ds_seen s ! w")
    case True
    show ?thesis unfolding up if_P[OF True]
      by (rule scan_complete_upd) (use assms(2) True stk in \<open>auto simp: rem w_def split: if_splits\<close>)
  next
    case False
    let ?t = "bd_upd1 acyc_flow s"
    have T: "ds_seen ?t = (ds_seen s)[w := True]" "ds_stk ?t = w # ds_stk s"
      using False by (simp_all add: up discover_seen_eq dfs_discover_def dfs_push_def Let_def)
    have "orem (ds_oc ?t) j = (if j = w
        then {e. e < m \<and> fst_list ! e = w \<and> is_free acyc_flow e} else orem c' j)"
      "irem (ds_ic ?t) j = (if j = w then {e. e < m \<and> snd_list ! e = w \<and> is_free acyc_flow e}
                            else irem (ds_ic s) j)"
      for j using False dfs_push_remaining[of w] \<open>w < vcount\<close>
      by (cases "j = w"; simp add: up dfs_discover_def Let_def)+
    note R = this
    show ?thesis
      by (rule scan_complete_upd)
         (use assms(2) False stk \<open>w < vcount\<close> S(11) in
          \<open>auto simp: T R rem w_def nth_list_update split: if_splits\<close>)
  qed
qed

lemma bd_upd2_scan_complete:
  assumes "dfs_inv acyc_flow s" "scan_complete s" "bd_call2_conds acyc_flow s"
  shows "scan_complete (bd_upd2 acyc_flow s)"
proof-
  from assms(3) obtain v rest where stk: "ds_stk s = v # rest"
    and nho: "\<not> csr_blocks.csr_has ((!) (fst (free_out acyc_flow))) (ds_oc s) v"
    and has: "csr_blocks.csr_has ((!) (fst (free_in acyc_flow))) (ds_ic s) v"
    by (auto simp: bd_call2_conds_def split: list.splits)
  have "dfs_wf acyc_flow s" "length (ds_seen s) = Suc vcount" using assms(1)
    by (simp_all add: dfs_inv_def dfs_sized_def)
  note S = bd_in_step[OF this(1) stk has] this
  define e where "e = csr_blocks.csr_current (snd (free_in acyc_flow)) (ds_ic s) v"
  define c' where "c' = csr_blocks.csr_move ((!) (fst (free_in acyc_flow))) (ds_ic s) v"
  define w where "w = fst_list ! e"
  have up: "bd_upd2 acyc_flow s =
              (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr>
               else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    using nho by (simp add: bd_upd2_def stk Let_def e_def c'_def w_def)
  have "w < vcount" using S(4) by (simp add: w_def e_def)
  have rem: "irem c' x = (if x = v then irem (ds_ic s) v - {e} else irem (ds_ic s) x)" for x
    using S(7,8)[folded e_def c'_def] by simp
  show ?thesis
  proof(cases "ds_seen s ! w")
    case True
    show ?thesis unfolding up if_P[OF True]
      by (rule scan_complete_upd) (use assms(2) True stk in \<open>auto simp: rem w_def split: if_splits\<close>)
  next
    case False
    let ?t = "bd_upd2 acyc_flow s"
    have T: "ds_seen ?t = (ds_seen s)[w := True]" "ds_stk ?t = w # ds_stk s"
      using False by (simp_all add: up discover_seen_eq dfs_discover_def dfs_push_def Let_def)
    have "orem (ds_oc ?t) j = (if j = w then {e. e < m \<and> fst_list ! e = w \<and> is_free acyc_flow e}
                               else orem (ds_oc s) j)"
      "irem (ds_ic ?t) j = (if j = w then
                            {e. e < m \<and> snd_list ! e = w \<and> is_free acyc_flow e} else irem c' j)"
      for j using False dfs_push_remaining[of w] \<open>w < vcount\<close>
      by (cases "j = w"; simp add: up dfs_discover_def Let_def)+
    note R = this
    show ?thesis
      by (rule scan_complete_upd)
         (use assms(2) False stk \<open>w < vcount\<close> S(11) in
          \<open>auto simp: T R rem w_def nth_list_update split: if_splits\<close>)
  qed
qed

lemma bd_upd3_scan_complete:
  assumes "dfs_inv acyc_flow s" "scan_complete s" "bd_call3_conds acyc_flow s"
  shows "scan_complete (bd_upd3 s)"
proof-
  have wf: "dfs_wf acyc_flow s" using assms(1) by (simp add: dfs_inv_def)
  from assms(3) obtain v rest where stk: "ds_stk s = v # rest"
    and o: "\<not> csr_blocks.csr_has ((!) (fst (free_out acyc_flow))) (ds_oc s) v"
    and i: "\<not> csr_blocks.csr_has ((!) (fst (free_in acyc_flow))) (ds_ic s) v"
    by (auto simp: bd_call3_conds_def split: list.splits)
  have "scan_complete (dfs_finish s v rest)"
    by (rule scan_complete_upd[OF assms(2)])
       (use stk bd_finish_empty[OF wf stk o i] in \<open>auto simp: dfs_finish_def Let_def\<close>)
  thus ?thesis by (simp add: bd_upd3_def stk)
qed

lemma emit_U_edge_scan_complete: "scan_complete (emit_U_edge s v) = scan_complete s"
  by (simp add: scan_complete_def emit_U_edge_def Let_def)

text \<open>A finished vertex has every free neighbour seen.\<close>

lemma scan_complete_finished:
  "\<lbrakk>scan_complete s; a < vcount; ds_seen s ! a; a \<notin> set (ds_stk s); e < m; is_free acyc_flow e;
    fst_list ! e = a\<rbrakk> \<Longrightarrow> ds_seen s ! (snd_list ! e)"
  "\<lbrakk>scan_complete s; a < vcount; ds_seen s ! a; a \<notin> set (ds_stk s); e < m; is_free acyc_flow e;
    snd_list ! e = a\<rbrakk> \<Longrightarrow> ds_seen s ! (fst_list ! e)"
  unfolding scan_complete_def by blast+

subsection \<open>Free-edge coverage: ancestor extraction and the walk-builder\<close>

text \<open>A vertex on the stack is a pstep-ancestor of the top (@{thm stk_top_reaches}) --- this is what the
      merged invariant's ancinv conjunct uses at dfs\_discover. Further, chain\_redge turns a tree edge into the
      residual arc oriented from child to parent, and chain\_redge\_props certifies it is a free real edge of the
      original residual graph with the right endpoints --- the atom the walk-builder assembles into a pstep-chain
      prepath for free\_walk\_no\_cycle.\<close>

lemma redge_in_E: "original_network.oedge a < m \<Longrightarrow> a \<in> original_network.\<EE>"
  by (cases a) (auto simp: original_network.\<EE>_def)

definition chain_redge :: "nat \<Rightarrow> nat Redge" where
  "chain_redge x = (if fst_list ! (ds_par (build_tree acyc_flow) ! x) = x
                    then F (ds_par (build_tree acyc_flow) ! x) else B (ds_par (build_tree acyc_flow) ! x))"

lemma chain_redge_props:
  assumes "x \<in> Vseen" "ds_prnt (build_tree acyc_flow) ! x < vcount"
  shows "original_network.oedge (chain_redge x) = ds_par (build_tree acyc_flow) ! x
       \<and> ds_par (build_tree acyc_flow) ! x < m
       \<and> is_free acyc_flow (ds_par (build_tree acyc_flow) ! x)
       \<and> original_network.fstv (chain_redge x) = x
       \<and> original_network.sndv (chain_redge x) = ds_prnt (build_tree acyc_flow) ! x
       \<and> chain_redge x \<in> original_network.\<EE>"
proof-
  have "x < vcount" "ds_seen (build_tree acyc_flow) ! x" using assms(1) by (simp_all add: Vseen_def)
  moreover have "ds_prnt (build_tree acyc_flow) ! x \<noteq> x"
    using calculation pstep_acyclic[unfolded acyclic_def] r_into_trancl[of x x "pstep (build_tree acyc_flow)"]
    by (auto simp: pstep_def)
  ultimately show ?thesis using par_free[of x] par_ends[of x] assms(2)
    by (cases "ds_dir (build_tree acyc_flow) ! x") (simp_all add: chain_redge_def redge_in_E)
qed

text \<open>prepath plumbing: original\_network is only a flow\_network\_spec, so the flow\_network-level
      prepath\_intros are unavailable; op\_prepath\_single/cons rebuild the single-arc and cons introduction rules
      from prepath\_def and awalk\_Cons\_iff over the UNIV pair-graph. The walk-builder then turns a pstep-chain u
      {\isasymleadsto}* w to a real ancestor w into an interior free-real prepath from u to w (chain\_redge per
      step, oriented child{\isasymrightarrow}parent), tracking that its residual arcs are exactly the parent edges
      of the chain vertices --- hence distinct (par\_inj) and never equal to an uncovered edge.\<close>

lemma op_tvp: "original_network.to_vertex_pair e = (original_network.fstv e, original_network.sndv e)"
  by (cases e) (auto simp add: original_network.make_pair_def)

lemma dVs_UNIV_all: "(x::nat) \<in> dVs UNIV"
  by (auto simp: dVs_def)

lemma op_prepath_single: "original_network.prepath [e]"
  by (simp add: original_network.prepath_def op_tvp awalk_Cons_iff awalk_Nil_iff dVs_UNIV_all)

lemma op_prepath_cons:
  "\<lbrakk>original_network.sndv e = original_network.fstv (hd p); original_network.prepath p\<rbrakk>
   \<Longrightarrow> original_network.prepath (e # p)"
  by (cases p) (auto simp: original_network.prepath_def op_tvp awalk_Cons_iff dVs_UNIV_all)

lemma pstep_chain_prepath:
  assumes "(u, w) \<in> (pstep (build_tree acyc_flow))\<^sup>*" "w < vcount"
  shows "u = w \<or> (\<exists>C. C \<noteq> [] \<and> original_network.prepath C
     \<and> original_network.fstv (hd C) = u \<and> original_network.sndv (last C) = w
     \<and> (\<forall>a\<in>set C. original_network.oedge a < m \<and> is_free acyc_flow (original_network.oedge a))
     \<and> distinct (map original_network.oedge C)
     \<and> (\<forall>e'\<in>original_network.oedge ` set C. \<exists>y\<in>Vseen. e'
             = ds_par (build_tree acyc_flow) ! y
             \<and> (u,y) \<in> (pstep (build_tree acyc_flow))\<^sup>*
               \<and> (y,w) \<in> (pstep (build_tree acyc_flow))\<^sup>+))"
  using assms(1)
proof(induct rule: converse_rtrancl_induct)
  case (step a b)
  let ?P = "pstep (build_tree acyc_flow)"
  have aV: "a \<in> Vseen" and bpar: "b = ds_prnt (build_tree acyc_flow) ! a"
    using step(1) by (auto simp: pstep_def Vseen_def)
  have "b < vcount"
    using step(2) assms(2) by (cases rule: converse_rtranclE) (auto simp: pstep_def)
  note crp = chain_redge_props[OF aV this[unfolded bpar]]
  have aw: "(a, w) \<in> ?P\<^sup>+" using step(1,2) by (rule rtrancl_into_trancl2)
  show ?case
  proof(cases "b = w")
    case True
    thus ?thesis using crp aV aw op_prepath_single[of "chain_redge a"] bpar
      by (intro disjI2 exI[of _ "[chain_redge a]"]) auto
  next
    case False
    with step(3) obtain C where C: "C \<noteq> []" "original_network.prepath C"
      "original_network.fstv (hd C) = b" "original_network.sndv (last C) = w"
      "\<forall>aa\<in>set C. original_network.oedge aa < m \<and> is_free acyc_flow (original_network.oedge aa)"
      "distinct (map original_network.oedge C)"
      "\<forall>e'\<in>original_network.oedge ` set C. \<exists>y\<in>Vseen. e' = ds_par (build_tree acyc_flow) ! y
         \<and> (b,y) \<in> ?P\<^sup>* \<and> (y,w) \<in> ?P\<^sup>+"
      by blast
    have "ds_par (build_tree acyc_flow) ! a \<notin> original_network.oedge ` set C"
    proof
      assume "ds_par (build_tree acyc_flow) ! a \<in> original_network.oedge ` set C"
      then obtain y where "y \<in> Vseen" "ds_par (build_tree acyc_flow) ! y = ds_par (build_tree acyc_flow) ! a"
        "(b, y) \<in> ?P\<^sup>*"
        using C(7) by force
      thus False
        using par_inj[of y a] aV rtrancl_into_trancl2[OF step(1)] pstep_acyclic by (auto simp: acyclic_def)
    qed
    moreover have "original_network.prepath (chain_redge a # C)"
      using crp bpar C(2,3) by (intro op_prepath_cons) simp_all
    moreover have "\<forall>e'\<in>original_network.oedge ` set C. \<exists>y\<in>Vseen. e'
                     = ds_par (build_tree acyc_flow) ! y
         \<and> (a,y) \<in> ?P\<^sup>* \<and> (y,w) \<in> ?P\<^sup>+"
      using C(7) step(1) by (blast intro: converse_rtrancl_into_rtrancl)
    ultimately show ?thesis using C(1,3-6) crp aV aw
      by (intro disjI2 exI[of _ "chain_redge a # C"]) auto
  qed
qed simp

subsection \<open>Comparability of free-edge endpoints (covinv) and its discover-step maintenance\<close>

text \<open>covinv: any free real edge whose both endpoints are seen has pstep-comparable endpoints (one is a
      tree-ancestor of the other). Its only non-trivial maintenance is at dfs\_discover: a newly seen w
      and an already-seen free-neighbour a of it must be comparable. free\_neighbor\_on\_stack shows a is on
      the stack (a finished a would, by scan\_complete, already have seen w); then stk\_top\_reaches makes
      a an ancestor of the stack top v, and w becomes v's child, so (w,a){\isasymin}pstep*.\<close>

definition covinv :: "'n dfs_state \<Rightarrow> bool" where
  "covinv s \<longleftrightarrow> (\<forall>e<m. is_free acyc_flow e \<longrightarrow>
      ds_seen s ! (fst_list ! e) \<longrightarrow> ds_seen s ! (snd_list ! e) \<longrightarrow>
      (fst_list ! e, snd_list ! e) \<in> (pstep s)\<^sup>* \<or> (snd_list ! e, fst_list ! e) \<in> (pstep s)\<^sup>*)"

lemma free_neighbor_on_stack:
  assumes "scan_complete s" "e < m" "is_free acyc_flow e" "\<not> ds_seen s ! w" "ds_seen s ! a"
    "(fst_list ! e = a \<and> snd_list ! e = w) \<or> (fst_list ! e = w \<and> snd_list ! e = a)"
  shows "a \<in> stkverts s"
  unfolding stkverts_def
proof(rule ccontr)
  assume "a \<notin> set (ds_stk s)"
  moreover have "a < vcount" using assms(6) fst_list_lt[OF assms(2)] snd_list_lt[OF assms(2)] by auto
  ultimately show False using assms(4,6) scan_complete_finished[OF assms(1) _ assms(5) _ assms(2,3)] by blast
qed

lemma covinv_cong:
  "\<lbrakk>ds_seen s = ds_seen t; ds_prnt s = ds_prnt t; covinv s\<rbrakk> \<Longrightarrow> covinv t"
  by (simp add: covinv_def pstep_def)

lemma discover_prnt_eq: "ds_prnt (dfs_discover s v w e) = (ds_prnt s)[w := v]"
  by (simp add: dfs_discover_def dfs_push_def Let_def)

text \<open>Seeing one more vertex w keeps covinv when the old tree steps survive and every seen free neighbour
      of w becomes reachable from w.\<close>

lemma covinv_seen_upd:
  assumes "covinv s" "ds_seen t = (ds_seen s)[w := True]" "pstep s \<subseteq> pstep t"
    "\<And>a d. \<lbrakk>ds_seen s ! a; d < m; is_free acyc_flow d;
            (fst_list ! d = a \<and> snd_list ! d = w) \<or> (fst_list ! d = w \<and> snd_list ! d = a)\<rbrakk>
       \<Longrightarrow> (w, a) \<in> (pstep t)\<^sup>*"
  shows "covinv t"
  unfolding covinv_def
proof(intro allI impI)
  fix d assume d: "d < m" "is_free acyc_flow d" "ds_seen t ! (fst_list ! d)" "ds_seen t ! (snd_list ! d)"
  show "(fst_list ! d, snd_list ! d) \<in> (pstep t)\<^sup>*
          \<or> (snd_list ! d, fst_list ! d) \<in> (pstep t)\<^sup>*"
    using d assms(4)[of "fst_list ! d" d] assms(4)[of "snd_list ! d" d]
      assms(1)[unfolded covinv_def, rule_format, of d] rtrancl_mono[of "pstep s" "pstep t"] assms(3)
    by (cases "fst_list ! d = w"; cases "snd_list ! d = w") (auto simp: assms(2))
qed

text \<open>One scan step from the stack top v along the free edge e to w: if w is new, it becomes v's
      child, and a seen free neighbour of w is on the stack (@{thm free_neighbor_on_stack}), hence an
      ancestor of v (@{thm stk_top_reaches}).\<close>

lemma covinv_step:
  assumes "dfs_wf acyc_flow s" "dfs_sized s" "scan_complete s" "covinv s" "stk_prnt_inv s" "ds_stk s = v # rest"
    "e < m" "is_free acyc_flow e" "(fst_list ! e = v \<and> snd_list ! e = w)
                                     \<or> (fst_list ! e = w \<and> snd_list ! e = v)"
    "w < vcount" "ds_seen s' = ds_seen s" "ds_prnt s' = ds_prnt s"
  shows "covinv (if ds_seen s ! w then s' else dfs_discover s' v w e)"
proof(cases "ds_seen s ! w")
  case False
  have P: "pstep (dfs_discover s' v w e) = insert (w, v) (pstep s)"
    using assms(2,10-12) False by (intro pstep_upd) (simp_all add: discover_seen_eq discover_prnt_eq dfs_sized_def)
  show ?thesis unfolding if_not_P[OF False]
  proof(rule covinv_seen_upd[where s = s])
    fix a d assume "ds_seen s ! a" "d < m" "is_free acyc_flow d"
      "(fst_list ! d = a \<and> snd_list ! d = w) \<or> (fst_list ! d = w \<and> snd_list ! d = a)"
    from stk_top_reaches[OF assms(5,1,6) free_neighbor_on_stack[OF assms(3) this(2,3) False this(1,4)]]
    show "(w, a) \<in> (pstep (dfs_discover s' v w e))\<^sup>*"
      using rtrancl_mono[of "pstep s" "insert (w, v) (pstep s)"] by (auto simp: P intro: converse_rtrancl_into_rtrancl)
  qed (use assms(4,11) in \<open>auto simp: P discover_seen_eq\<close>)
qed (use assms(4,11,12) covinv_cong[of s s'] in simp)

text \<open>covinv is threaded through the builder jointly with scan\_complete, which its scan step needs.\<close>

lemma build_dfs_sc_cv:
  assumes "dfs_inv acyc_flow s" "scan_complete s" "covinv s"
  shows "scan_complete (build_dfs acyc_flow s) \<and> covinv (build_dfs acyc_flow s)"
proof-
  have "fl = acyc_flow \<longrightarrow> dfs_inv fl s \<longrightarrow> scan_complete s \<and> covinv s
          \<longrightarrow> scan_complete (build_dfs fl s) \<and> covinv (build_dfs fl s)"
    if "build_dfs_dom (fl, s)" for fl s
    using that
  proof(induct rule: bd_induct[consumes 1])
    case IH: (1 fl s)
    show ?case
    proof(intro impI, elim conjE)
      assume A: "fl = acyc_flow" "dfs_inv fl s" "scan_complete s" "covinv s"
      have wf: "dfs_wf acyc_flow s" and S: "dfs_sized s" "stk_prnt_inv s" using A(1,2) by (simp_all add: dfs_inv_def)
      note step = covinv_step[OF wf S(1) A(3,4) S(2)]
      show "scan_complete (build_dfs fl s) \<and> covinv (build_dfs fl s)"
      proof(rule bd_cases[where s = s and fl = fl])
        assume c: "bd_call1_conds fl s"
        obtain v rest e w c' where O: "ds_stk s = v # rest" "e < m" "fst_list ! e = v" "snd_list ! e = w"
          "is_free acyc_flow e" "w < vcount"
          and up: "bd_upd1 acyc_flow s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr>
                                          else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
          using wf c A(1) by (auto elim: bd_upd1_eq)
        have "covinv (bd_upd1 acyc_flow s)" unfolding up by (rule step) (use O in simp_all)
        moreover have "scan_complete (bd_upd1 acyc_flow s)" using A c by (intro bd_upd1_scan_complete) simp_all
        ultimately show ?thesis using IH(2) c bd_upd1_inv A bd_simps(1)[OF IH(1) c] by simp
      next
        assume c: "bd_call2_conds fl s"
        obtain v rest e w c' where O: "ds_stk s = v # rest" "e < m" "snd_list ! e = v" "fst_list ! e = w"
          "is_free acyc_flow e" "w < vcount"
          and up: "bd_upd2 acyc_flow s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr>
                                          else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
          using wf c A(1) by (auto elim: bd_upd2_eq)
        have "covinv (bd_upd2 acyc_flow s)" unfolding up by (rule step) (use O in simp_all)
        moreover have "scan_complete (bd_upd2 acyc_flow s)" using A c by (intro bd_upd2_scan_complete) simp_all
        ultimately show ?thesis using IH(3) c bd_upd2_inv A bd_simps(2)[OF IH(1) c] by simp
      next
        assume c: "bd_call3_conds fl s"
        obtain v rest where "bd_upd3 s = dfs_finish s v rest" using c by (rule bd_upd3_eq)
        hence "covinv (bd_upd3 s)" using covinv_cong[of s] A(4) by (simp add: dfs_finish_def Let_def)
        moreover have "scan_complete (bd_upd3 s)" using A c by (intro bd_upd3_scan_complete) simp_all
        ultimately show ?thesis using IH(4) c bd_upd3_inv A bd_simps(3)[OF IH(1) c] by simp
      qed (use A bd_simps(4)[OF IH(1)] in simp)
    qed
  qed
  then show ?thesis using build_dfs_dom_wf[of acyc_flow s] assms by (simp add: dfs_inv_def)
qed

text \<open>The component-root seed adds no comparability obligation: a seen free neighbour of the fresh
      root would be on the empty stack.\<close>

lemma open_tree_component_sc_cv:
  assumes "dfs_inv acyc_flow s" "scan_complete s" "covinv s" "c < vcount" "\<not> ds_seen s ! c" "c \<noteq> 0"
    "ds_stk s = []"
  shows "scan_complete (open_tree_component acyc_flow s c) \<and> covinv (open_tree_component acyc_flow s c)"
proof-
  have wf: "dfs_wf acyc_flow s" and sz: "dfs_sized s"
    and L: "length (ds_seen s) = Suc vcount" "length (ds_prnt s) = Suc vcount"
    using assms(1) by (simp_all add: dfs_inv_def dfs_sized_def)
  obtain sd where sd: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd" "dfs_inv acyc_flow sd"
    "ds_stk sd = [c]" "ds_oc sd = ds_oc (dfs_push s c)" "ds_ic sd = ds_ic (dfs_push s c)"
    "ds_seen sd = (ds_seen s)[c := True]" "ds_prnt sd = (ds_prnt s)[c := vcount]"
    by (rule open_tree_component_seed[OF wf sz assms(4)]) (use assms(1,5-7) in blast)
  have R: "orem (ds_oc sd) j = (if j = c then {e. e < m \<and> fst_list ! e = c \<and> is_free acyc_flow e}
                                else orem (ds_oc s) j)"
    "irem (ds_ic sd) j = (if j = c then {e. e < m \<and> snd_list ! e = c \<and> is_free acyc_flow e}
                          else irem (ds_ic s) j)"
    for j using sd(4,5) dfs_push_remaining assms(4) by (cases "j = c"; simp)+
  have "scan_complete sd"
    by (rule scan_complete_upd)
       (use assms(2,4,5,7) L in \<open>auto simp: sd(3,6) R nth_list_update split: if_splits\<close>)
  moreover have "covinv sd"
  proof(rule covinv_seen_upd[where s = s])
    show "pstep s \<subseteq> pstep sd" using pstep_upd[OF sd(7,6) assms(4,5) L] by auto
    fix a d assume "ds_seen s ! a" "d < m" "is_free acyc_flow d"
      "(fst_list ! d = a \<and> snd_list ! d = c) \<or> (fst_list ! d = c \<and> snd_list ! d = a)"
    thus "(c, a) \<in> (pstep sd)\<^sup>*"
      using free_neighbor_on_stack[of s _ c] assms(2,5,7) by (auto simp: stkverts_def)
  qed (use assms(3) sd(6) in auto)
  ultimately show ?thesis using build_dfs_sc_cv sd(1,2) by simp
qed

lemma emit_U_edge_covinv: "covinv s \<Longrightarrow> covinv (emit_U_edge s v)"
  by (rule covinv_cong) (simp_all add: emit_U_edge_def Let_def)

lemma vs_nonzero: "v \<in> set vs_list \<Longrightarrow> v \<noteq> 0"
  using no_zero_node by (rule contrapos_nn) simp

lemma phase1_step_sc_cv:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; ds_stk s = []; scan_complete s; covinv s\<rbrakk>
   \<Longrightarrow> scan_complete (phase1_step acyc_flow v s) \<and> covinv (phase1_step acyc_flow v s)"
  using open_tree_component_sc_cv[of s v] vs_less_vcount[of v] vs_nonzero[of v] emit_U_edge_covinv[of s v]
  by (simp add: phase1_step_def emit_U_edge_scan_complete)

lemma phase2_step_sc_cv:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; ds_stk s = []; scan_complete s; covinv s\<rbrakk>
   \<Longrightarrow> scan_complete (phase2_step acyc_flow v s) \<and> covinv (phase2_step acyc_flow v s)"
  using open_tree_component_sc_cv[of s v] vs_less_vcount[of v] vs_nonzero[of v]
  by (simp add: phase2_step_def)

lemma covinv_dfs_init: "covinv dfs_init"
  by (auto simp: covinv_def dfs_init_def dest: fst_list_lt simp del: replicate_Suc)

lemma scan_complete_dfs_init: "scan_complete dfs_init"
  by (simp add: scan_complete_def dfs_init_def del: replicate_Suc)

lemma build_tree_covinv: "covinv (build_tree acyc_flow)"
proof-
  have "scan_complete (phase2 acyc_flow (phase1 acyc_flow dfs_init))
          \<and> covinv (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
    using scan_complete_dfs_init covinv_dfs_init
    by (intro phases_preserve[where Q = "\<lambda>s. scan_complete s \<and> covinv s"])
      (use phase1_step_sc_cv phase2_step_sc_cv in blast)+
  thus ?thesis by (simp add: build_tree_def Let_def covinv_def pstep_def)
qed

subsection \<open>Free-edge coverage: every free real edge is a tree (parent) edge\<close>

text \<open>The payoff of covinv + the walk-builder + the acyclicity engine: an uncovered free real edge e,
      with both endpoints seen (build\_tree\_spans) and pstep-comparable (build\_tree\_covinv), would close a
      free residual cycle (the tree chain between its endpoints plus e), contradicting acyclicity. Hence
      e is a parent edge. Needs acyclic\_flow (nth acyc\_flow), delivered on the Some branch by acyc\_of\_some.\<close>

lemma cycle_contra:
  assumes "original_network.acyclic_flow (h \<circ> nth acyc_flow)"
    "(a, b) \<in> (pstep (build_tree acyc_flow))\<^sup>*"
    "b < vcount" "original_network.fstv re = b" "original_network.sndv re = a" "original_network.oedge re = e"
    "e < m" "is_free acyc_flow e" "\<And>v. v \<in> Vseen
                                     \<Longrightarrow> ds_par (build_tree acyc_flow) ! v \<noteq> e"
  shows False
  using pstep_chain_prepath[OF assms(2,3)]
proof(elim disjE exE conjE)
  assume "a = b"
  show False
    by (rule free_walk_no_cycle[of "[re]"])
       (use \<open>a = b\<close> assms(1,4-8) redge_in_E[of re] in \<open>auto simp: op_prepath_single\<close>)
next
  fix C assume C: "C \<noteq> []" "original_network.prepath C" "original_network.fstv (hd C) = a"
    "original_network.sndv (last C) = b"
    "\<forall>x\<in>set C. original_network.oedge x < m \<and> is_free acyc_flow (original_network.oedge x)"
    "distinct (map original_network.oedge C)"
    "\<forall>e'\<in>original_network.oedge ` set C. \<exists>y\<in>Vseen. e' = ds_par (build_tree acyc_flow) ! y
       \<and> (a,y) \<in> (pstep (build_tree acyc_flow))\<^sup>*
         \<and> (y,b) \<in> (pstep (build_tree acyc_flow))\<^sup>+"
  have E: "e \<notin> original_network.oedge ` set C"
  proof
    assume "e \<in> original_network.oedge ` set C"
    with C(7) obtain y where "y \<in> Vseen" "e = ds_par (build_tree acyc_flow) ! y" by blast
    thus False using assms(9)[of y] by simp
  qed
  show False
    by (rule free_walk_no_cycle[OF assms(1), of "re # C"])
       (use E C(1-6) assms(4-8) redge_in_E op_prepath_cons[of re C] in auto)
qed

lemma free_edge_covered:
  assumes "original_network.acyclic_flow (h \<circ> nth acyc_flow)" "e < m" "is_free acyc_flow e"
  shows "\<exists>v \<in> Vseen. ds_par (build_tree acyc_flow) ! v = e"
proof(rule ccontr)
  assume "\<not> ?thesis"
  hence notcov: "\<And>v. v \<in> Vseen \<Longrightarrow> ds_par (build_tree acyc_flow) ! v \<noteq> e" by auto
  have "fst_list ! e \<in> Vseen" "snd_list ! e \<in> Vseen"
    using assms(2) nth_mem[of e fst_list] nth_mem[of e snd_list] Vseen_eq_V V_orig_eq by auto
  hence "(fst_list ! e, snd_list ! e) \<in> (pstep (build_tree acyc_flow))\<^sup>*
       \<or> (snd_list ! e, fst_list ! e) \<in> (pstep (build_tree acyc_flow))\<^sup>*"
    using build_tree_covinv assms(2,3) by (simp add: covinv_def Vseen_def)
  thus False
  proof
    assume "(fst_list ! e, snd_list ! e) \<in> (pstep (build_tree acyc_flow))\<^sup>*"
    thus False
      by (rule cycle_contra[OF assms(1) _ _ _ _ _ assms(2,3) notcov, where re = "B e"])
         (simp_all add: assms(2) snd_list_lt)
  next
    assume "(snd_list ! e, fst_list ! e) \<in> (pstep (build_tree acyc_flow))\<^sup>*"
    thus False
      by (rule cycle_contra[OF assms(1) _ _ _ _ _ assms(2,3) notcov, where re = "F e"])
         (simp_all add: assms(2) fst_list_lt)
  qed
qed

subsection \<open>Artificial-edge reverse coverage: every artificial InTree edge is a component-root's edge\<close>

text \<open>art\_owned: for every emitted artificial slot k with tag InTree there is a component root c
      (\<open>ds_prnt c = vcount\<close>) whose parent edge is exactly that slot (\<open>ds_par c = m + k\<close>).
      This is the reverse of cr\_ext\_inv and completes InTree {\isasymsubseteq} T for the artificial range.
      Threaded like the forward cr\_ext machinery: build\_dfs adds no InTree artificial edge and freezes seen roots
      (build\_dfs\_frozen), open\_tree\_component installs the new root's witness and emit\_U\_edge only adds an
      InU edge. Like @{const tail_content_upto}, only the slots below the tail length are tracked, so no bound on
      ds\_nxt is needed during the phases (@{thm build_tree_nxt_le} supplies it at the end).\<close>

definition art_owned :: "'n dfs_state \<Rightarrow> bool" where
  "art_owned s \<longleftrightarrow>
     (\<forall>k < min (ds_nxt s) (length vs_list). ds_aest s ! k = InTree \<longrightarrow>
      (\<exists>c<vcount. ds_seen s ! c \<and> ds_prnt s ! c = vcount \<and> ds_par s ! c = m + k))"

lemma build_dfs_art_owned:
  assumes "build_dfs_dom (fl, s)" "dfs_inv fl s" "art_owned s"
  shows "art_owned (build_dfs fl s)"
  unfolding art_owned_def
proof(intro allI impI)
  fix k assume "k < min (ds_nxt (build_dfs fl s)) (length vs_list)" "ds_aest (build_dfs fl s) ! k = InTree"
  then obtain c where "c < vcount" "ds_seen s ! c" "ds_prnt s ! c = vcount" "ds_par s ! c = m + k"
    using assms(3) build_dfs_art[OF assms(1)] by (auto simp: art_owned_def)
  thus "\<exists>c<vcount. ds_seen (build_dfs fl s) ! c \<and> ds_prnt (build_dfs fl s) ! c = vcount
          \<and> ds_par (build_dfs fl s) ! c = m + k"
    using build_dfs_seen_mono[OF assms(1), of c] build_dfs_frozen[OF assms(1,2), of c] by (intro exI[of _ c]) auto
qed

lemma emit_U_edge_art_owned: "\<lbrakk>art_owned s; art_len s\<rbrakk> \<Longrightarrow> art_owned (emit_U_edge s v)"
  by (auto simp: art_owned_def art_len_def emit_U_edge_def Let_def nth_list_update less_Suc_eq min_def
      split: if_splits)

lemma open_tree_component_art_owned:
  assumes "dfs_inv acyc_flow s" "art_owned s" "c < vcount" "\<not> ds_seen s ! c" "c \<noteq> 0" "ds_stk s = []"
    "art_len s"
  shows "art_owned (open_tree_component acyc_flow s c)"
proof-
  have wf: "dfs_wf acyc_flow s" and sz: "dfs_sized s" using assms(1) by (simp_all add: dfs_inv_def)
  obtain sd where sd: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd" "build_dfs_dom (acyc_flow, sd)"
    "dfs_inv acyc_flow sd" "ds_nxt sd = Suc (ds_nxt s)"
    "ds_seen sd = (ds_seen s)[c := True]" "ds_prnt sd = (ds_prnt s)[c := vcount]"
    "ds_par sd = (ds_par s)[c := m + ds_nxt s]" "ds_aest sd = (ds_aest s)[ds_nxt s := InTree]"
    by (rule open_tree_component_seed[OF wf sz assms(3)]) (use assms(1,4-6) in blast)
  have "art_owned sd"
    unfolding art_owned_def
  proof(intro allI impI)
    fix k assume k: "k < min (ds_nxt sd) (length vs_list)" "ds_aest sd ! k = InTree"
    show "\<exists>c<vcount. ds_seen sd ! c \<and> ds_prnt sd ! c = vcount \<and> ds_par sd ! c = m + k"
    proof(cases "k = ds_nxt s")
      case True
      thus ?thesis using assms(3) sz by (intro exI[of _ c]) (simp add: sd(5-7) dfs_sized_def)
    next
      case False
      then obtain c0 where "c0 < vcount" "ds_seen s ! c0" "ds_prnt s ! c0 = vcount" "ds_par s ! c0 = m + k"
        using assms(2) k by (auto simp: art_owned_def sd(4,8) less_Suc_eq)
      moreover have "c0 \<noteq> c" using calculation(2) assms(4) by auto
      ultimately show ?thesis by (intro exI[of _ c0]) (simp add: sd(5-7))
    qed
  qed
  thus ?thesis using sd(1-3) build_dfs_art_owned by simp
qed

lemma phase1_step_art_owned:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; ds_stk s = []; art_len s; art_owned s\<rbrakk>
   \<Longrightarrow> art_owned (phase1_step acyc_flow v s)"
  using open_tree_component_art_owned[of s v] vs_less_vcount[of v] vs_nonzero[of v] emit_U_edge_art_owned[of s v]
  by (simp add: phase1_step_def)

lemma phase2_step_art_owned:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; ds_stk s = []; art_len s; art_owned s\<rbrakk>
   \<Longrightarrow> art_owned (phase2_step acyc_flow v s)"
  using open_tree_component_art_owned[of s v] vs_less_vcount[of v] vs_nonzero[of v]
  by (simp add: phase2_step_def)

lemma art_owned_dfs_init: "art_owned dfs_init"
  by (simp add: art_owned_def dfs_init_def)

lemma build_tree_art_owned:
  assumes "k < ds_nxt (build_tree acyc_flow)" "ds_aest (build_tree acyc_flow) ! k = InTree"
  shows "\<exists>c<vcount. ds_seen (build_tree acyc_flow) ! c \<and> ds_prnt (build_tree acyc_flow) ! c = vcount
         \<and> ds_par (build_tree acyc_flow) ! c = m + k"
proof-
  have "art_len (phase2 acyc_flow (phase1 acyc_flow dfs_init))
          \<and> art_owned (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
    using art_owned_dfs_init dfs_init_art_len
    by (intro phases_preserve[where Q = "\<lambda>s. art_len s \<and> art_owned s"])
       (use phase1_step_art_len phase2_step_art_len phase1_step_art_owned phase2_step_art_owned in blast)+
  thus ?thesis using assms build_tree_nxt_le by (auto simp: build_tree_def Let_def art_owned_def)
qed

subsection \<open>The tree edges are exactly the InTree edges (real coverage + artificial coverage)\<close>

lemma InTree_subseteq_T:
  assumes "original_network.acyclic_flow (h \<circ> nth acyc_flow)"
  shows "{e \<in> {0..<m + Kart}. state_all ! e = InTree}
           \<subseteq> (!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})"
proof
  fix e assume "e \<in> {e \<in> {0..<m + Kart}. state_all ! e = InTree}"
  hence e: "e < m + Kart" "state_all ! e = InTree" by auto
  show "e \<in> (!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})"
  proof(cases "e < m")
    case True
    hence "is_free acyc_flow e" using e(2) state_all_real[OF True] by (simp add: is_free_def)
    then obtain v where "v \<in> Vseen" "ds_par (build_tree acyc_flow) ! v = e"
      using free_edge_covered[OF assms True] by blast
    thus ?thesis by (auto simp: NS_V_minus_root)
  next
    case False
    then obtain k where k: "e = m + k" using le_Suc_ex[of m e] by auto
    then obtain c where "c < vcount" "ds_seen (build_tree acyc_flow) ! c" "ds_par (build_tree acyc_flow) ! c = m + k"
      using build_tree_art_owned[of k] e state_all_art[of k] by (auto simp: Kart_def)
    thus ?thesis using k by (force simp: NS_V_minus_root Vseen_def)
  qed
qed

lemma T_eq_InTree:
  "original_network.acyclic_flow (h \<circ> nth acyc_flow) \<Longrightarrow>
   (!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}) = {e \<in> {0..<m + Kart}. state_all ! e = InTree}"
  using T_sub_InTree InTree_subseteq_T by (rule subset_antisym)

subsection \<open>The spanning-tree partition (Some branch)\<close>

text \<open>Besides the edge cover and tag disjointness (from @{thm T_eq_InTree}), the parent edges form a
      graph (endpoint-set injectivity), a @{const graph_abs}, a rooted @{const graph_abs.arborescence}
      (via the unique-distinct-walk bridge @{thm unique_walks_arborescence}, whose uniqueness premise is
      exactly the arborescence-ADT axiom @{thm NS.general}(3)), and span the vertex set. Together this
      assembles @{const NS.spanning_tree_partition} on the Some branch.\<close>

lemma tree_edge_endpoint_inj:
  assumes "u \<in> Vseen" "u' \<in> Vseen"
    "{fst_all ! (ds_par (build_tree acyc_flow) ! u), snd_all ! (ds_par (build_tree acyc_flow) ! u)}
     = {fst_all ! (ds_par (build_tree acyc_flow) ! u'), snd_all ! (ds_par (build_tree acyc_flow) ! u')}"
  shows "u = u'"
proof-
  have P: "(x, ds_prnt (build_tree acyc_flow) ! x) \<in> pstep (build_tree acyc_flow)" if "x \<in> Vseen" for x
    using that by (auto simp: pstep_def Vseen_def)
  have "{u, ds_prnt (build_tree acyc_flow) ! u} = {u', ds_prnt (build_tree acyc_flow) ! u'}"
    using assms tc_endpoints[of u] tc_endpoints[of u']
    by (cases "ds_dir (build_tree acyc_flow) ! u"; cases "ds_dir (build_tree acyc_flow) ! u'") auto
  hence "u = u' \<or> (ds_prnt (build_tree acyc_flow) ! u' = u \<and> ds_prnt (build_tree acyc_flow) ! u = u')"
    by (auto simp: doubleton_eq_iff)
  thus ?thesis
  proof(elim disjE conjE)
    assume "ds_prnt (build_tree acyc_flow) ! u' = u" "ds_prnt (build_tree acyc_flow) ! u = u'"
    hence "(u, u') \<in> pstep (build_tree acyc_flow)" "(u', u) \<in> pstep (build_tree acyc_flow)"
      using P[of u] P[of u'] assms(1,2) by simp_all
    hence "(u, u) \<in> (pstep (build_tree acyc_flow))\<^sup>+" by (rule trancl_into_trancl[OF r_into_trancl])
    thus ?thesis using pstep_acyclic by (simp add: acyclic_def)
  qed
qed

lemma dVs_make_pair_Vs_gen: "dVs ((\<lambda>e. (g e, k e)) ` X) = Vs ((\<lambda>e. {g e, k e}) ` X)"
  by (auto simp: dVs_def Vs_def)

lemma NS_make_pair_eq:
  "NS.make_pair = (\<lambda>e. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
                         if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))))"
  by (rule ext) (simp add: NS.make_pair_def)

lemma NSinit_partition:
  assumes "original_network.acyclic_flow (h \<circ> nth acyc_flow)"
  shows "NS.spanning_tree_partition vcount
           ((!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}))
           {e \<in> {0..<m + Kart}. state_all ! e = InL}
           {e \<in> {0..<m + Kart}. state_all ! e = InU}"
proof(rule NS.spanning_tree_partitionI)
  let ?T = "(!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})"
  let ?f = "\<lambda>e. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
                  if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))}"

  show "{0..<m + Kart} = ?T \<union> {e \<in> {0..<m + Kart}. state_all ! e = InU}
          \<union> {e \<in> {0..<m + Kart}. state_all ! e = InL}"
    "?T \<inter> {e \<in> {0..<m + Kart}. state_all ! e = InU} = {}"
      "?T \<inter> {e \<in> {0..<m + Kart}. state_all ! e = InL} = {}"
    "{e \<in> {0..<m + Kart}. state_all ! e = InL} \<inter> {e \<in> {0..<m + Kart}. state_all ! e = InU} = {}"
    unfolding T_eq_InTree[OF assms] by (auto dest: state_total)
  show "graph_abs (?f ` ?T)" unfolding tc_image using Sarb_graph_invar by (simp add: graph_abs_def)
  show "graph_abs.arborescence (?f ` ?T) vcount (?f ` ?T)"
    unfolding tc_image
  proof(rule unique_walks_arborescence[OF Sarb_graph_invar])
    show "vcount \<in> Vs (abstract_arb Sarb)" using Sarb_Vs r_in_V by simp
    fix x y assume "x \<in> Vs (abstract_arb Sarb)" "y \<in> Vs (abstract_arb Sarb)"
    thus "\<exists>!p. walk_betw (abstract_arb Sarb) x p y \<and> distinct p"
      using NS.general(3)[OF arb_invar_Sarb, of y x] Sarb_Vs NS_V_Varb by simp
  qed
  show "\<forall>e e'. {e, e'} \<subseteq> ?T \<and> ?f e = ?f e' \<longrightarrow> e = e'"
  proof(intro allI impI, elim conjE)
    fix e e' assume E: "{e, e'} \<subseteq> ?T" "?f e = ?f e'"
    then obtain u u' where U: "u \<in> Vseen" "u' \<in> Vseen" "e = ds_par (build_tree acyc_flow) ! u"
      "e' = ds_par (build_tree acyc_flow) ! u'" by (auto simp: NS_V_minus_root)
    have "ds_par (build_tree acyc_flow) ! u < m + Kart" "ds_par (build_tree acyc_flow) ! u' < m + Kart"
      using U(1,2) par_lt_marc by (simp_all add: Vseen_def)
    with E(2) have "u = u'" unfolding U(3,4) by (intro tree_edge_endpoint_inj[OF U(1,2)]) (simp only: if_True)
    thus "e = e'" using U(3,4) by simp
  qed
  have "dVs (NS.make_pair ` ?T) = Vs (?f ` ?T)" unfolding NS_make_pair_eq by (rule dVs_make_pair_Vs_gen)
  thus "dVs (NS.make_pair ` ?T) = NS.\<V>" using tc_image Sarb_Vs NS_V_Varb by simp
qed

subsection \<open>Towards @{text init_bflow}: excess decomposition of the assembled flow\<close>

text \<open>The augmented excess of @{const flow_all} splits into a real part and an artificial part. On the real
      edges @{term \<open>e < m\<close>} the assembled flow is @{const acyc_flow}, so --- since the augmented and
      original in/out-edge sets agree there (@{thm delta_minus_orig} / @{thm delta_plus_orig}) --- the real part is
      exactly \<open>original_network.ex (h \<circ> nth acyc_flow) v\<close>. The artificial part is the signed
      flow on the artificial in/out edges of @{term v}; identifying it with @{term \<open>imbalance ! v\<close>}
      (and, with @{thm make_acyclic_ex},
      \<open>original_network.ex (h \<circ> nth acyc_flow) v = h (excess ! v)\<close>) is the remaining step toward
      @{text init_bflow}.\<close>

lemma flow_all_ex_real:
  "(\<Sum>e\<in>NS.delta_minus v \<inter> {0..<m}. h (flow_all ! e))
     - (\<Sum>e\<in>NS.delta_plus v \<inter> {0..<m}. h (flow_all ! e))
     = original_network.ex (h \<circ> nth acyc_flow) v"
proof-
  have "NS.delta_minus v \<inter> {0..<m} = original_network.delta_minus v"
    "NS.delta_plus v \<inter> {0..<m} = original_network.delta_plus v"
    using delta_minus_orig delta_plus_orig by simp_all
  thus ?thesis
    by (auto intro!: arg_cong2[where f = minus] sum.cong simp: original_network.ex_def flow_all_real
        original_network.delta_minus_def original_network.delta_plus_def)
qed

lemma NS_delta_split:
  "NS.delta_minus v = (NS.delta_minus v \<inter> {0..<m}) \<union> (NS.delta_minus v \<inter> {m..<m+Kart})"
  "NS.delta_plus v = (NS.delta_plus v \<inter> {0..<m}) \<union> (NS.delta_plus v \<inter> {m..<m+Kart})"
  by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: NS.delta_minus_def NS.delta_plus_def)

lemma ex_flow_all_decomp:
  "NS.ex (h \<circ> nth flow_all) v = original_network.ex (h \<circ> nth acyc_flow) v
     + h ((\<Sum>e\<in>NS.delta_minus v \<inter> {m..<m+Kart}. flow_all ! e)
          - (\<Sum>e\<in>NS.delta_plus v \<inter> {m..<m+Kart}. flow_all ! e))"
proof-
  have "(\<Sum>e\<in>NS.delta_minus v. h (flow_all ! e))
          = (\<Sum>e\<in>NS.delta_minus v \<inter> {0..<m}. h (flow_all ! e))
            + (\<Sum>e\<in>NS.delta_minus v \<inter> {m..<m+Kart}. h (flow_all ! e))"
    by (subst NS_delta_split(1)) (rule sum.union_disjoint, auto)
  moreover have "(\<Sum>e\<in>NS.delta_plus v. h (flow_all ! e))
          = (\<Sum>e\<in>NS.delta_plus v \<inter> {0..<m}. h (flow_all ! e))
            + (\<Sum>e\<in>NS.delta_plus v \<inter> {m..<m+Kart}. h (flow_all ! e))"
    by (subst NS_delta_split(2)) (rule sum.union_disjoint, auto)
  ultimately show ?thesis using flow_all_ex_real[of v] by (simp add: NS.ex_def h_sum algebra_simps)
qed

text \<open>The artificial in/out edge-sums at @{term v} are sums over the artificial \<^emph>\<open>slots\<close>
      @{term \<open>k < Kart\<close>}: edge @{term \<open>m + k\<close>} is the \<open>k\<close>-th artificial
      edge, carrying @{term \<open>ds_aflw (build_tree acyc_flow) ! k\<close>} (@{thm flow_all_art}). The
      membership rewrites @{text dm_art_set}/@{text dp_art_set} strip the augmented endpoint functions down to the
      plain arrays (the \<open>fst_exec\<close>/\<open>snd_exec\<close> simp rules must be disabled throughout ---
      they are self-referential and loop on any \<open>fst_all ! e\<close> / \<open>snd_all ! e\<close>).\<close>

lemma dm_art_set: "NS.delta_minus v \<inter> {m..<m+Kart} = {e. m \<le> e \<and> e < m+Kart \<and> snd_all ! e = v}"
  by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: NS.delta_minus_def)

lemma dp_art_set: "NS.delta_plus v \<inter> {m..<m+Kart} = {e. m \<le> e \<and> e < m+Kart \<and> fst_all ! e = v}"
  by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: NS.delta_plus_def)

lemma art_index_set:
  "{e. m \<le> e \<and> e < m+Kart \<and> xs ! e = v} = (+) m ` {k \<in> {0..<Kart}. xs ! (m+k) = v}"
  by (auto simp: image_iff le_iff_add)

lemma art_part_sum:
  "(\<Sum>e\<in>{e. m \<le> e \<and> e < m+Kart \<and> xs ! e = v}. flow_all ! e)
   = (\<Sum>k = 0..<Kart. if xs ! (m+k) = v then ds_aflw (build_tree acyc_flow) ! k else 0)"
proof-
  have "(\<Sum>e\<in>{e. m \<le> e \<and> e < m+Kart \<and> xs ! e = v}. flow_all ! e)
         = (\<Sum>k\<in>{k \<in> {0..<Kart}. xs ! (m+k) = v}. flow_all ! (m+k))"
    by (simp add: art_index_set sum.reindex inj_on_def)
  also have "\<dots> = (\<Sum>k\<in>{k \<in> {0..<Kart}. xs ! (m+k) = v}. ds_aflw (build_tree acyc_flow) ! k)"
    by (rule sum.cong) (simp_all add: flow_all_art)
  finally show ?thesis
    using sum.inter_filter[of "{0..<Kart}" "\<lambda>k. ds_aflw (build_tree acyc_flow) ! k"
                           "\<lambda>k. xs ! (m+k) = v"] by simp
qed

subsection \<open>Towards @{text init_bflow}: the artificial excess accumulator\<close>

text \<open>@{term \<open>aex s v\<close>} is the artificial-edge contribution to @{term v}'s excess in state
      @{term s}: the signed per-slot flow over the slots already emitted (@{term \<open>k < ds_nxt s\<close>}).
      Each emission --- @{const emit_U_edge} or the seed of @{const open_tree_component} (the enclosed
      @{const build_dfs} freezes the artificial arrays, @{thm build_dfs_art}) --- changes
      @{term \<open>aex s v\<close>} by exactly @{term \<open>- imbalance ! v\<close>} at the processed vertex and
      @{term \<open>imbalance ! v\<close>} at the root, so over a whole phase-1 sweep the increments accumulate as
      one @{const sum_list}. The @{term E}-witness (@{term \<open>ds_nxt s = card E\<close>}) carries the
      @{term \<open>ds_nxt s < length vs_list\<close>} bound the emission step lemmas need, exactly as in
      @{thm fold_emit_bnd}.\<close>

definition aex :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> 'n" where
  "aex s v = (\<Sum>k = 0..<ds_nxt s. (if ds_asnd s ! k = v then ds_aflw s ! k else 0)
                                - (if ds_afst s ! k = v then ds_aflw s ! k else 0))"

lemma aex_Suc:
  "\<lbrakk>ds_nxt t = Suc (ds_nxt s);
    \<And>k. k < ds_nxt s \<Longrightarrow> ds_asnd t ! k = ds_asnd s ! k \<and> ds_afst t ! k = ds_afst s ! k
      \<and> ds_aflw t ! k = ds_aflw s ! k\<rbrakk>
   \<Longrightarrow> aex t w = aex s w + ((if ds_asnd t ! ds_nxt s = w then ds_aflw t ! ds_nxt s else 0)
                            - (if ds_afst t ! ds_nxt s = w then ds_aflw t ! ds_nxt s else 0))"
  by (auto simp: aex_def sum.atLeast0_lessThan_Suc intro!: sum.cong)

lemma emit_U_edge_aex:
  assumes "art_len s" "ds_nxt s < length vs_list" "v < vcount"
  shows "aex (emit_U_edge s v) w
           = aex s w + (if w = v then - imbalance ! v else if w = vcount then imbalance ! v else 0)"
proof-
  have "aex (emit_U_edge s v) w = aex s w
      + ((if ds_asnd (emit_U_edge s v) ! ds_nxt s = w then ds_aflw (emit_U_edge s v) ! ds_nxt s else 0)
       - (if ds_afst (emit_U_edge s v) ! ds_nxt s = w then ds_aflw (emit_U_edge s v) ! ds_nxt s else 0))"
    by (rule aex_Suc) (simp_all add: emit_U_edge_def Let_def)
  thus ?thesis using assms no_zero_node
    by (cases "0 \<le> imbalance ! v") (auto simp: emit_U_edge_def Let_def art_len_def art_flow_def imbalance_def)
qed

lemma open_tree_component_aex:
  assumes "dfs_inv acyc_flow s" "art_len s" "ds_nxt s < length vs_list" "v < vcount"
  shows "aex (open_tree_component acyc_flow s v) w
           = aex s w + (if w = v then - imbalance ! v else if w = vcount then imbalance ! v else 0)"
proof-
  have "aex (open_tree_component acyc_flow s v) w = aex s w
      + ((if ds_asnd (open_tree_component acyc_flow s v) ! ds_nxt s = w
          then ds_aflw (open_tree_component acyc_flow s v) ! ds_nxt s else 0)
       - (if ds_afst (open_tree_component acyc_flow s v) ! ds_nxt s = w
          then ds_aflw (open_tree_component acyc_flow s v) ! ds_nxt s else 0))"
    using assms(1,4) by (intro aex_Suc) (simp_all add: open_tree_component_art)
  thus ?thesis using assms no_zero_node
    by (cases "art_dir v") (auto simp: open_tree_component_asnd_at open_tree_component_afst_at
        open_tree_component_aflw_at art_flow_def art_dir_def)
qed

lemma phase1_step_aex:
  "\<lbrakk>v \<in> set vs_list; dfs_inv acyc_flow s; ds_stk s = []; art_len s; ds_nxt s < length vs_list\<rbrakk>
   \<Longrightarrow> aex (phase1_step acyc_flow v s) w
       = aex s w + (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0)"
  using vs_less_vcount[of v] by (simp add: phase1_step_def emit_U_edge_aex open_tree_component_aex)

lemma fold_phase1_aex:
  assumes "distinct xs" "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}"
        "E \<inter> set xs = {}" "ds_nxt s = card E"
  shows "aex (fold (phase1_step acyc_flow) xs s) w
           = aex s w + (\<Sum>v\<leftarrow>xs.
                        (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0))
         \<and> art_len (fold (phase1_step acyc_flow) xs s)
         \<and> dfs_inv acyc_flow (fold (phase1_step acyc_flow) xs s)
         \<and> ds_stk (fold (phase1_step acyc_flow) xs s) = []
         \<and> (\<exists>E'. finite E' \<and> E'
                 \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase1_step acyc_flow) xs s) ! v}
                 \<and> ds_nxt (fold (phase1_step acyc_flow) xs s) = card E')"
  using assms
proof(induct xs arbitrary: s E)
  case (Cons x rest)
  have x: "x \<in> set vs_list" "x < vcount" "x \<notin> E" using Cons.prems(2,8) vs_less_vcount by auto
  have I: "insert x E \<subseteq> set vs_list" using Cons.prems(7) x(1) by auto
  have "ds_nxt s < length vs_list" using card_sub_vs_le[OF I] Cons.prems(6,9) x(3) by simp
  note step = phase1_step_aex[OF x(1) Cons.prems(3-5) this, of w]
  have R: "dfs_inv acyc_flow (phase1_step acyc_flow x s)" "ds_stk (phase1_step acyc_flow x s) = []"
    "art_len (phase1_step acyc_flow x s)"
      "E \<subseteq> {v \<in> set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}"
    using phase1_step_inv[OF x(1)] phase1_step_art_len[OF x(1) Cons.prems(3,5)] Cons.prems(3,4,7)
      phase1_step_seen_mono[OF Cons.prems(3) x(2)] by auto
  from phase1_step_nxt[OF Cons.prems(3) x(2)] show ?case
  proof
    assume "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(1,2,6,8,9) step Cons.hyps[OF _ _ R(1-3) _ R(4)] by simp
  next
    assume "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) \<and> ds_seen (phase1_step acyc_flow x s) ! x"
    thus ?thesis using Cons.prems(1,2,6,8,9) x R step Cons.hyps[OF _ _ R(1-3), of "insert x E"] by simp
  qed
qed auto

text \<open>The accumulator reaches its target already after phase 1 (every imbalanced vertex is opened
      or gets its @{const emit_U_edge}, hence seen), and phase 2 only opens the remaining --- balanced,
      hence zero-flow --- vertices, so it leaves @{const aex} unchanged; the final @{const ds_lsuc}
      touch-up is irrelevant. Thus each real vertex's artificial excess is exactly
      @{term \<open>- imbalance ! w\<close>}.\<close>

lemma aex_dfs_init: "aex dfs_init v = 0"
  by (simp add: aex_def dfs_init_def)

lemma aex_lsuc: "aex (s\<lparr>ds_lsuc := x\<rparr>) v = aex s v"
  by (simp add: aex_def cong: if_cong)

lemma phase1_step_marks_imb:
  "\<lbrakk>imbalance!x \<noteq> 0; dfs_inv acyc_flow s; x < vcount\<rbrakk>
     \<Longrightarrow> ds_seen (phase1_step acyc_flow x s) ! x"
  using open_tree_component_marks[of acyc_flow s x] by (simp add: phase1_step_def emit_U_edge_def Let_def)

lemma fold_phase1_imb_seen:
  "\<lbrakk>set xs \<subseteq> set vs_list; dfs_inv acyc_flow s; ds_stk s = [];
            ds_seen s ! v \<or> (v \<in> set xs \<and> imbalance!v \<noteq> 0)\<rbrakk>
   \<Longrightarrow> ds_seen (fold (phase1_step acyc_flow) xs s) ! v"
proof(induct xs arbitrary: s)
  case (Cons x rest)
  have "x \<in> set vs_list" "x < vcount" using Cons.prems(1) vs_less_vcount by auto
  thus ?case unfolding fold_Cons comp_def
    using Cons.prems phase1_step_inv[of x acyc_flow s] phase1_step_seen_mono[OF Cons.prems(2), of x v]
      phase1_step_marks_imb[OF _ Cons.prems(2), of x]
    by (intro Cons.hyps) auto
qed simp

lemma phase2_step_aex:
  "\<lbrakk>dfs_inv acyc_flow s; art_len s; ds_nxt s < length vs_list; v \<in> set vs_list; imbalance!v = 0\<rbrakk>
   \<Longrightarrow> aex (phase2_step acyc_flow v s) w = aex s w"
  using open_tree_component_aex[of s v w] vs_less_vcount[of v] by (simp add: phase2_step_def)

lemma fold_phase2_aex:
  assumes "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []" "art_len s"
      "finite E" "E \<subseteq> {u \<in> set vs_list. ds_seen s ! u}" "ds_nxt s = card E"
      "\<forall>u \<in> set vs_list. \<not> ds_seen s ! u \<longrightarrow> imbalance!u = 0"
  shows "aex (fold (phase2_step acyc_flow) xs s) w = aex s w
         \<and> art_len (fold (phase2_step acyc_flow) xs s)
           \<and> dfs_inv acyc_flow (fold (phase2_step acyc_flow) xs s)
         \<and> ds_stk (fold (phase2_step acyc_flow) xs s) = []
         \<and> (\<forall>u \<in> set vs_list. \<not> ds_seen (fold (phase2_step acyc_flow) xs s) ! u
                 \<longrightarrow> imbalance!u = 0)"
  using assms
proof(induct xs arbitrary: s E)
  case (Cons x rest)
  have x: "x \<in> set vs_list" "x < vcount" using Cons.prems(1) vs_less_vcount by auto
  have R: "dfs_inv acyc_flow (phase2_step acyc_flow x s)" "ds_stk (phase2_step acyc_flow x s) = []"
    "art_len (phase2_step acyc_flow x s)"
      "E \<subseteq> {u \<in> set vs_list. ds_seen (phase2_step acyc_flow x s) ! u}"
    "\<forall>u \<in> set vs_list. \<not> ds_seen (phase2_step acyc_flow x s) ! u \<longrightarrow> imbalance!u = 0"
    using phase2_step_inv[OF x(1)] phase2_step_art_len[OF x(1) Cons.prems(2,4)] Cons.prems(2,3,6,8)
      phase2_step_seen_mono[OF Cons.prems(2) x(2)] by auto
  from phase2_step_nxt2[OF Cons.prems(2) x(2)] show ?case
  proof
    assume "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    hence "phase2_step acyc_flow x s = s"
      using open_tree_component_art(1)[OF Cons.prems(2) x(2)] by (auto simp: phase2_step_def split: if_splits)
    thus ?thesis using Cons.prems(1) Cons.hyps[OF _ Cons.prems(2-8)] by simp
  next
    assume B: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! x
      \<and> ds_seen (phase2_step acyc_flow x s) ! x"
    hence "x \<notin> E" "imbalance ! x = 0" using Cons.prems(6,8) x(1) by auto
    moreover have I: "insert x E \<subseteq> set vs_list" using Cons.prems(6) x(1) by auto
    moreover have "ds_nxt s < length vs_list" using card_sub_vs_le[OF I] Cons.prems(5,7) calculation(1) by simp
    ultimately show ?thesis
      using B R Cons.prems(1,5,7) phase2_step_aex[OF Cons.prems(2,4) _ x(1)]
        Cons.hyps[OF _ R(1-3), of "insert x E"] by simp
  qed
qed auto

lemma dfs_init_stk_nxt: "ds_stk dfs_init = []" "ds_nxt dfs_init = card {}"
  by (simp_all add: dfs_init_def)

lemma aex_build_tree_generic:
  "aex (build_tree acyc_flow) w =
     (\<Sum>v\<leftarrow>vs_list. (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0))"
proof-
  note P1 = fold_phase1_aex[OF distinct_vs_list order_refl dfs_init_inv dfs_init_stk_nxt(1) dfs_init_art_len
      finite.emptyI empty_subsetI Int_empty_left dfs_init_stk_nxt(2), of w, folded phase1_def]
  then obtain E1 where E1: "finite E1" "E1 \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}"
    "ds_nxt (phase1 acyc_flow dfs_init) = card E1" by blast
  have "\<forall>u \<in> set vs_list. \<not> ds_seen (phase1 acyc_flow dfs_init) ! u \<longrightarrow> imbalance!u = 0"
    using fold_phase1_imb_seen[OF order_refl dfs_init_inv dfs_init_stk_nxt(1), folded phase1_def] by blast
  hence "aex (phase2 acyc_flow (phase1 acyc_flow dfs_init)) w = aex (phase1 acyc_flow dfs_init) w"
    using fold_phase2_aex[OF order_refl _ _ _ E1, of w] P1 by (simp add: phase2_def)
  thus ?thesis using P1 aex_dfs_init by (simp add: build_tree_def Let_def aex_lsuc)
qed

lemma build_tree_aex:
  assumes "w \<in> set vs_list"
  shows "aex (build_tree acyc_flow) w = - imbalance ! w"
proof-
  have "(\<lambda>v. if w = v then - imbalance!v else if w = vcount then imbalance!v else 0)
      = (\<lambda>v. if w = v then - imbalance!v else 0)"
    by (intro ext) (use assms vs_less_vcount in fastforce)
  thus ?thesis using assms by (simp add: aex_build_tree_generic sum_list_distinct_conv_sum_set[OF distinct_vs_list])
qed

text \<open>Reindexing @{const aex} at @{const build_tree} to the augmented artificial edge-sums bridges
      the accumulator to @{thm ex_flow_all_decomp}: the artificial part of @{term v}'s augmented
      excess is @{term \<open>aex (build_tree acyc_flow) v\<close>}. Hence for every real vertex the augmented
      excess of @{const flow_all} is the acyclified-flow excess minus @{term \<open>imbalance ! v\<close>}.\<close>

lemma art_sum_endpoints:
  "(\<Sum>k = 0..<Kart. if snd_all ! (m+k) = v then ds_aflw (build_tree acyc_flow) ! k else 0)
      = (\<Sum>k = 0..<Kart. if ds_asnd (build_tree acyc_flow) ! k = v then ds_aflw (build_tree acyc_flow) ! k else 0)"
  "(\<Sum>k = 0..<Kart. if fst_all ! (m+k) = v then ds_aflw (build_tree acyc_flow) ! k else 0)
      = (\<Sum>k = 0..<Kart. if ds_afst (build_tree acyc_flow) ! k = v then ds_aflw (build_tree acyc_flow) ! k else 0)"
  by (auto intro!: sum.cong simp: snd_all_art fst_all_art simp del: NS.fst_exec_eq NS.snd_exec_eq)

lemma aex_eq_art_part:
  "aex (build_tree acyc_flow) v
     = (\<Sum>e\<in>NS.delta_minus v \<inter> {m..<m+Kart}. flow_all ! e)
       - (\<Sum>e\<in>NS.delta_plus v \<inter> {m..<m+Kart}. flow_all ! e)"
  using art_sum_endpoints[of v] unfolding dm_art_set dp_art_set art_part_sum
  by (simp add: aex_def Kart_def sum_subtractf del: NS.fst_exec_eq NS.snd_exec_eq)

lemma ex_flow_all_real_vertex:
  "v \<in> set vs_list \<Longrightarrow> NS.ex (h \<circ> nth flow_all) v
     = original_network.ex (h \<circ> nth acyc_flow) v - h (imbalance!v)"
  using ex_flow_all_decomp[of v] by (simp add: aex_eq_art_part[symmetric] build_tree_aex)

subsection \<open>@{text init_bflow}: the assembled flow is a @{term b_lookup}-flow (Some branch)\<close>

text \<open>The augmented @{const flow_all} is capacity-feasible on both branches
      and, on the @{term Some} branch, balances @{const b_lookup} at every augmented vertex: at a real
      vertex because @{const acyc_flow} preserves the frozen excess (@{thm make_acyclic_ex}) which the
      artificial edge corrects by @{term \<open>imbalance ! v\<close>}, and at the root because the imbalances sum to
      zero. Together these discharge @{text init_bflow}.\<close>

text \<open>\<^emph>\<open>Pass A's excess for an arbitrary flow.\<close>  @{const excess} is defined as the excess
      component of @{term \<open>passA flow_list\<close>} --- the \<^emph>\<open>frozen\<close> input flow --- but
      the executable pipeline runs Pass A on the \<^emph>\<open>acyclified\<close> flow instead.  The lemmas below
      compute Pass A's excess for any @{term fl} (the underlying fold lemma @{thm passA_fold_exc} is already
      flow-generic), and then close the loop: since the acyclifier preserves every vertex's excess
      (@{text orig_ex_acyc_eq_excess}) and @{term h} is injective (@{thm h_eq_iff}), running Pass A on
      @{const acyc_flow} yields \<^emph>\<open>literally\<close> @{const excess}. This is what lets the imperative
      refinement identify its in-place excess array --- computed from the acyclified flow --- with the functional
      @{const imbalance}, which is anchored to @{const excess}.\<close>

lemma passA_exc_len: "length (fst (snd (passA fl))) = Suc vcount"
  using sized_passA[of fl] by (cases "passA fl") (simp add: sized_def)

lemma sized_passA_init:
  "sized (replicate m InL, replicate (Suc vcount) (0::'n), (out_lo, out.inp.E_spec), (in_lo, inc.inp.E_spec))"
  by (simp add: sized_def length_out_lo length_in_lo length_out_E length_in_E)

lemma passA_exc_nth:
  "v < Suc vcount \<Longrightarrow> fst (snd (passA fl)) ! v =
           (\<Sum>e\<leftarrow>[0..<m]. (if snd_list ! e = v then fl ! e else 0))
         - (\<Sum>e\<leftarrow>[0..<m]. (if fst_list ! e = v then fl ! e else 0))"
  using passA_fold_exc[OF sized_passA_init, where xs = "[0..<m]" and fl = fl]
  by (simp add: passA_def del: replicate_Suc)

lemma orig_delta_sets:
  "original_network.delta_minus v = {e \<in> {0..<m}. snd_list ! e = v}"
  "original_network.delta_plus v = {e \<in> {0..<m}. fst_list ! e = v}"
  by (auto simp: original_network.delta_minus_def original_network.delta_plus_def snd_all_real fst_all_real)

lemma ex_is_passA_exc:
  assumes "v < Suc vcount"
  shows "original_network.ex (h \<circ> nth fl) v = h (fst (snd (passA fl)) ! v)"
proof-
  have key: "(\<Sum>e\<in>{e \<in> {0..<m}. P e}. h (fl ! e))
               = h (\<Sum>e\<in>{0..<m}. if P e then fl ! e else 0)" for P
  proof-
    have "h (\<Sum>e\<in>{0..<m}. if P e then fl ! e else 0) = (\<Sum>e\<in>{0..<m}. if P e then h (fl ! e) else 0)"
      unfolding h_sum by (rule sum.cong[OF refl]) simp
    also have "\<dots> = (\<Sum>e\<in>{e \<in> {0..<m}. P e}. h (fl ! e))" by (rule sum.mono_neutral_cong_right) auto
    finally show ?thesis ..
  qed
  have "original_network.ex (h \<circ> nth fl) v
      = h (\<Sum>e\<in>{0..<m}. if snd_list ! e = v then fl ! e else 0)
        - h (\<Sum>e\<in>{0..<m}. if fst_list ! e = v then fl ! e else 0)"
    by (simp only: original_network.ex_def comp_def key orig_delta_sets)
  thus ?thesis using passA_exc_nth[OF assms] by (simp add: interv_sum_list_conv_sum_set_nat)
qed

lemma excess_is_orig_ex:
  "v < Suc vcount \<Longrightarrow> original_network.ex (h \<circ> nth flow_list) v = h (excess ! v)"
  using ex_is_passA_exc[of v flow_list] by (cases "passA flow_list") (simp add: excess_def)

lemma orig_ex_acyc_eq_excess:
  "\<lbrakk>acyc_flow_opt = Some f'; v < Suc vcount\<rbrakk>
     \<Longrightarrow> original_network.ex (h \<circ> nth acyc_flow) v = h (excess ! v)"
  using make_acyclic_ex[OF multigraph_inv_csr acyc_input(4) af_cap_feasible_flow_list acyc_input(1)
      equalityD1[OF acyc_input(2)], of f' v] excess_is_orig_ex[of v]
  by (simp add: acyc_flow_opt_def acyc_flow_def)

lemma passA_exc_acyc: "acyc_flow_opt = Some f' \<Longrightarrow> fst (snd (passA acyc_flow)) = excess"
  using ex_is_passA_exc orig_ex_acyc_eq_excess[of f'] by (intro nth_equalityI) (simp_all add: passA_exc_len)

lemma bflow_flow_all_real:
  "\<lbrakk>acyc_flow_opt = Some f'; v \<in> set vs_list\<rbrakk>
     \<Longrightarrow> - NS.ex (h \<circ> nth flow_all) v = h (b_lookup v)"
  using ex_flow_all_real_vertex[of v] orig_ex_acyc_eq_excess[of f' v] imbalance_nth[of v] vs_less_vcount[of v]
  by (simp add: h_add)

lemma aex_build_tree_root: "aex (build_tree acyc_flow) vcount = (\<Sum>v\<leftarrow>vs_list. imbalance!v)"
  unfolding aex_build_tree_generic
  by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (auto dest: vs_less_vcount)

lemma b_lookup_nonvertex:
  assumes "w < Suc vcount" "w \<notin> set vs_list"
  shows "b_lookup w = 0"
proof-
  have "b_arr ! w = replicate (Suc vcount) (0::'n) ! w"
    unfolding b_arr_def by (rule foldl_scatter_miss) (use assms(2) in \<open>auto dest: set_zip_leftD\<close>)
  thus ?thesis using assms(1) by (simp add: b_lookup_def del: replicate_Suc)
qed

lemma imbalance_nonvertex:
  "\<lbrakk>w < Suc vcount; w \<notin> set vs_list\<rbrakk> \<Longrightarrow> imbalance ! w = 0"
  using excess_is_orig_ex[of w] orig_ex_notin_V[of w] imbalance_root imbalance_nth[of w] b_lookup_nonvertex[of w]
  by (cases "w = vcount") auto

lemma sum_imbalance_set: "(\<Sum>v\<in>set vs_list. imbalance!v) = (\<Sum>v\<in>{0..<Suc vcount}. imbalance!v)"
  using imbalance_nonvertex by (intro sum.mono_neutral_left) (auto dest: vs_less_vcount)

lemma sum_imbalance_vs_list_zero: "(\<Sum>v\<leftarrow>vs_list. imbalance!v) = 0"
  using sum_imbalance_set sum_imbalance_zero by (simp add: sum_list_distinct_conv_sum_set[OF distinct_vs_list])

lemma vcount_notin_vs: "vcount \<notin> set vs_list" using vs_less_vcount by fastforce

lemma bflow_flow_all_root: "- NS.ex (h \<circ> nth flow_all) vcount = h (b_lookup vcount)"
  using ex_flow_all_decomp[of vcount] orig_ex_notin_V[OF vcount_notin_vs] aex_build_tree_root
    sum_imbalance_vs_list_zero b_lookup_root
  by (simp add: aex_eq_art_part[symmetric])

lemma isuflow_flow_all: "NS.isuflow (h \<circ> nth flow_all)"
  unfolding NS.isuflow_def comp_def
proof
  fix e assume "e \<in> {0..<m + Kart}"
  hence e: "e < m + Kart" by simp
  show "ereal (h (flow_all ! e)) \<le>
          (if e < m + Kart then if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e)) else \<infinity>)
        \<and> 0 \<le> h (flow_all ! e)"
  proof(cases "e < m")
    case True
    thus ?thesis using e flow_all_real cap_all_real acyc_flow_nonneg acyc_flow_le_cap[OF True] by auto
  next
    case False
    then obtain k where k: "e = m + k" "k < Kart" using e le_Suc_ex[of m e] by auto
    then obtain subj where "ds_aflw (build_tree acyc_flow) ! k = art_flow subj"
      "(ds_aest (build_tree acyc_flow) ! k = InTree \<and> ds_acap (build_tree acyc_flow) ! k = art_tree_cap subj)
       \<or> (ds_aest (build_tree acyc_flow) ! k = InU \<and> ds_acap (build_tree acyc_flow) ! k = art_flow subj)"
      using tail_edge_ok_build_tree by (auto simp: tail_edge_ok_def)
    thus ?thesis using k flow_all_art cap_all_art by (auto simp: art_tree_cap_def art_flow_def)
  qed
qed

lemma NSinit_bflow:
  assumes "acyc_flow_opt = Some f'"
  shows "NS.isbflow (h \<circ> nth flow_all) (\<lambda>v. h (b_lookup v))"
proof(rule NS.isbflowI[OF isuflow_flow_all])
  fix v assume "v \<in> NS.\<V>"
  hence "v = vcount \<or> v \<in> set vs_list" using NS_V_minus_root V_sub_vs_list Vseen_eq_V by auto
  thus "- NS.ex (h \<circ> nth flow_all) v = h (b_lookup v)"
    using bflow_flow_all_root bflow_flow_all_real[OF assms] by auto
qed

subsection \<open>Acyclicity of the acyclified flow on the Some branch (architecture keystone)\<close>

text \<open>On the branch where the acyclifier returns a flow (acyc\_flow\_opt = Some), that flow is genuinely
      acyclic: make\_acyclic\_correct\_unconditional certifies it, the freshly-built counting-sort CSRs
      have nothing iterated yet (csr\_lo = csr\_cur), and the vertex list abstracts to exactly the vertex
      set. This is the hypothesis under which the initial-basis interpretation's acyclicity-dependent
      obligations (free-edge coverage / init\_partition) become provable; it is discharged at the use
      site, inside solve on the Some branch.\<close>


lemma acyc_of_some: "acyc_flow_opt = Some f' \<Longrightarrow> original_network.acyclic_flow (h \<circ> nth acyc_flow)"
  using make_acyclic_correct_unconditional[OF multigraph_inv_csr acyc_input(4) af_cap_feasible_flow_list
      acyc_input(1-3,5)]
  by (simp add: acyc_flow_opt_def acyc_flow_def)

lemma solve_none: "acyc_flow_opt = None \<Longrightarrow> solve = Neg_inf_cycle" by (simp add: solve_def)

lemma NSinit_bflow_ne:
  "acyc_flow_opt \<noteq> None \<Longrightarrow> NS.isbflow (h \<circ> nth flow_all) (\<lambda>v. h (b_lookup v))"
  by (cases acyc_flow_opt) (auto intro: NSinit_bflow)

lemma NSinit_partition_ne:
  "acyc_flow_opt \<noteq> None \<Longrightarrow> NS.spanning_tree_partition vcount
     ((!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}))
     {e \<in> {0..<m + Kart}. state_all ! e = InL} {e \<in> {0..<m + Kart}. state_all ! e = InU}"
  using NSinit_partition[OF acyc_of_some] by (cases acyc_flow_opt) blast+

text \<open>Relabelling a spanning-tree partition: the tree-structure conjuncts depend only on @{term T},
      so any @{term L'} / @{term U'} that cover the same edges and stay disjoint from @{term T} and
      each other yield another valid partition. This lets the augmented (cost-folded) self-loop
      partition reuse the plain tag partition's arborescence facts.\<close>

lemma spanning_tree_partition_relabel:
  assumes "NS.spanning_tree_partition r T L U" "T \<union> U' \<union> L' = T \<union> U \<union> L"
    "T \<inter> U' = {}" "T \<inter> L' = {}" "L' \<inter> U' = {}"
  shows "NS.spanning_tree_partition r T L' U'"
proof-
  have "{0..<m + Kart} = T \<union> U' \<union> L'" using assms(1,2) by (simp add: NS.spanning_tree_partition_def)
  thus ?thesis using assms(1,3-5) unfolding NS.spanning_tree_partition_def by blast
qed

text \<open>Artificial edges run between a component root and the artificial root @{const vcount}, which are
      distinct, so no artificial edge is a self-loop.\<close>

lemma art_not_selfloop:
  assumes "m \<le> e" "e < m + Kart"
  shows "fst_all ! e \<noteq> snd_all ! e"
proof-
  obtain k where "e = m + k" "k < Kart" using assms le_Suc_ex[of m e] by auto
  thus ?thesis using tail_edge_ok_build_tree[of k] fst_all_art[of k] snd_all_art[of k]
    by (auto simp: tail_edge_ok_def simp del: NS.fst_exec_eq NS.snd_exec_eq split: if_splits)
qed

text \<open>\<open>make_acyclic_selfloop\<close>, specialised to the acyclified flow @{const acyc_flow} of the Some
      branch: a real self-loop is emptied when its cost is non-negative and saturated when negative.\<close>

lemma acyc_flow_selfloop:
  assumes "acyc_flow_opt \<noteq> None" "e < m" "fst_list ! e = snd_list ! e"
  shows "(0 \<le> cost_list ! e \<longrightarrow> acyc_flow ! e = 0)
           \<and> (cost_list ! e < 0 \<longrightarrow> acyc_flow ! e = capacity_list ! e)"
proof-
  obtain f' where "make_acyclic flow_list = Some f'" "acyc_flow = f'"
    using assms(1) by (auto simp: acyc_flow_opt_def acyc_flow_def)
  thus ?thesis
    using make_acyclic_selfloop[OF multigraph_inv_csr acyc_input(4) af_cap_feasible_flow_list acyc_input(1-3) _
        acyc_input(5), of f' e] assms(2,3)
    by simp
qed

text \<open>Obligation (\<open>init_selfloop\<close>): a self-loop of the initial basis carries the cost-directed
      bound the acyclifier fixes --- zero flow when @{term \<open>0 \<le> \<c>\<close>}, saturation when
      @{term \<open>\<c> < 0\<close>}. Artificial edges are not self-loops, so only the real edges contribute,
      discharged by @{thm acyc_flow_selfloop}; feasibility rules out the infinite-capacity negative case.\<close>

lemma NSinit_selfloop:
  assumes "acyc_flow_opt \<noteq> None"
  shows "\<forall>e\<in>{0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))))
          = (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart))))
     \<longrightarrow> (0 \<le> cost_all ! e \<longrightarrow> flow_all ! e = 0)
       \<and> (cost_all ! e < 0 \<longrightarrow> ereal (h (flow_all ! e))
            = (if e < m + Kart then if cap_all ! e = - 1 then \<infinity>
               else ereal (h (cap_all ! e)) else \<infinity>))"
proof(intro ballI impI)
  fix e assume "e \<in> {0..<m + Kart}" "(if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))))
          = (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart))))"
  hence "e < m + Kart" "fst_all ! e = snd_all ! e" by (simp_all del: NS.fst_exec_eq NS.snd_exec_eq)
  hence e: "e < m" "fst_list ! e = snd_list ! e"
    using art_not_selfloop[of e] fst_all_real[of e] snd_all_real[of e]
      by (force simp del: NS.fst_exec_eq NS.snd_exec_eq)+
  thus "(0 \<le> cost_all ! e \<longrightarrow> flow_all ! e = 0)
        \<and> (cost_all ! e < 0 \<longrightarrow> ereal (h (flow_all ! e))
            = (if e < m + Kart then if cap_all ! e = - 1 then \<infinity>
               else ereal (h (cap_all ! e)) else \<infinity>))"
    using acyc_flow_selfloop[OF assms e] cost_all_real[OF e(1)] flow_all_real[OF e(1)] cap_all_real[OF e(1)]
      acyc_flow_nonneg[OF e(1)]
    by auto
qed

text \<open>Obligation (\<open>init_flow_fits\<close>) in its non-self-loop form: it follows by monotonicity from
      the full flow fit @{thm NSinit_flow_fits} (fewer edges are constrained).\<close>

lemma NSinit_flow_fits_ns:
  "NS.flow_fits_spanning_tree_partition ((!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}))
     {e \<in> {0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))))
        \<noteq> (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) \<and> state_all ! e = InL}
     {e \<in> {0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))))
        \<noteq> (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) \<and> state_all ! e = InU}
     (h \<circ> (!) flow_all)"
  using NSinit_flow_fits by (auto simp: NS.flow_fits_spanning_tree_partition_def comp_def)

text \<open>Obligation (\<open>init_partition\<close>): the augmented partition folds self-loops into @{term L} /
      @{term U} by cost. It reuses the plain tag partition's tree facts via
      @{thm spanning_tree_partition_relabel}; the cover matches because every self-loop is covered by
      the cost split, and the tree carries no self-loop (the graph invariant). @{method blast} keeps the
      endpoint \<open>if\<close>-lambdas opaque, so it never diverges on @{term prod_decode}.\<close>

lemma ns_selfloops_eq:
  "NS.ns_selfloops_L
     = {e \<in> {0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))))
          = (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) \<and> 0 \<le> cost_all ! e}"
  "NS.ns_selfloops_U
     = {e \<in> {0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))))
          = (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) \<and> cost_all ! e < 0}"
  by (simp_all add: NS.ns_selfloops_L_def NS.ns_selfloops_U_def)

lemma NSinit_partition_aug:
  assumes "acyc_flow_opt \<noteq> None"
  shows "NS.spanning_tree_partition vcount ((!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}))
    ({e \<in> {0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))))
        \<noteq> (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) \<and> state_all ! e = InL}
     \<union> NS.ns_selfloops_L)
    ({e \<in> {0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))))
        \<noteq> (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) \<and> state_all ! e = InU}
     \<union> NS.ns_selfloops_U)"
proof-
  let ?T = "(!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})"
  let ?L = "{e \<in> {0..<m + Kart}. state_all ! e = InL}"
  let ?U = "{e \<in> {0..<m + Kart}. state_all ! e = InU}"
  let ?F = "\<lambda>e. if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))"
  let ?S = "\<lambda>e. if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))"
  note plain = NSinit_partition_ne[OF assms]
  note P = NS.spanning_tree_partitionD(1-3)[OF plain]
  have T: "?F d \<noteq> ?S d" if "d \<in> ?T" for d
  proof
    assume "?F d = ?S d"
    moreover have "{?F d, ?S d} \<in> abstract_arb Sarb" using that tc_image by blast
    ultimately show False
      using Sarb_graph_invar unfolding dblton_graph_def by fastforce
  qed

  have C: "InL \<noteq> InU" "\<And>x. cost_all ! x < 0 \<or> 0 \<le> cost_all ! x"
    "\<And>x. \<lbrakk>0 \<le> cost_all ! x; cost_all ! x < 0\<rbrakk> \<Longrightarrow> False" by auto
  show ?thesis
  proof(rule spanning_tree_partition_relabel[OF plain])
    show "?T \<inter> ({e \<in> {0..<m + Kart}. ?F e \<noteq> ?S e \<and> state_all ! e = InU}
                       \<union> NS.ns_selfloops_U) = {}"
      using P(2) T unfolding ns_selfloops_eq(2) by blast
    show "?T \<inter> ({e \<in> {0..<m + Kart}. ?F e \<noteq> ?S e \<and> state_all ! e = InL}
                       \<union> NS.ns_selfloops_L) = {}"
      using P(3) T unfolding ns_selfloops_eq(1) by blast
    show "({e \<in> {0..<m + Kart}. ?F e \<noteq> ?S e \<and> state_all ! e = InL} \<union> NS.ns_selfloops_L)
        \<inter> ({e \<in> {0..<m + Kart}. ?F e \<noteq> ?S e \<and> state_all ! e = InU}
                  \<union> NS.ns_selfloops_U) = {}"
      using C(1,3) unfolding ns_selfloops_eq by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)
  qed (use P(1) C(2) in \<open>unfold ns_selfloops_eq, blast\<close>)
qed

context
  assumes some: "acyc_flow_opt \<noteq> None"
begin

interpretation NSinit: network_simplex_init
  where fst = "\<lambda> e. if e < m+Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m+Kart)))"
    and snd = "\<lambda> e. if e < m+Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m+Kart)))"
    and create_edge = "\<lambda> u v. (m+Kart) + prod_encode (u, v)"
    and \<E> = "{0..<m+Kart}"
    and \<u> = "\<lambda> e. if e < m+Kart
                  then (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) else \<infinity>"
    and \<c> = "\<lambda> e. cost_all ! e"
    and r = vcount
    and shift_pot = shift_pot_impl
    and arborescense_invar = "arb_invar vcount Varb"
    and abstract_arborescense = abstract_arb
    and get_path_pair = get_path_pair_impl
    and swap_edge = swap_edge_impl
    and flow_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and flow_upd = list_update
      and flow_lookup = nth
    and pot_invar = "\<lambda>xs. \<forall>v\<in>Varb. v < length xs" and pot_upd = list_update and pot_lookup = nth
    and parent_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and parent_upd = list_update
      and parent_lookup = nth
    and dir_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and dir_upd = list_update
      and dir_lookup = nth
    and es_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs"
      and es_upd = list_update and es_lookup = nth
    and sel_invar = sel_invar_impl and sel_select = sel_select_impl
    and b = "\<lambda> v. h (b_lookup v)"
    and cap = "\<lambda> e. cap_all ! e"
    and pot_value_invar = "\<lambda> p. good_pot_val_c p \<and> pv_invar p"
    and pot_value_abstract = "pval_abstract bigM"
    and pot_value_plus = pval_plus
    and pot_value_minus = pval_minus
    and rcost_invar = rc_invar
    and rcost_abstract = "pval_abstract bigM"
    and fst_exec = "\<lambda> e. fst_all ! e"
    and snd_exec = "\<lambda> e. snd_all ! e"
    and init_flow = flow_all
    and init_pot = "ds_pot (build_tree acyc_flow)"
    and init_tree = Sarb
    and init_parent = "ds_par (build_tree acyc_flow)"
    and init_dir = "ds_dir (build_tree acyc_flow)"
    and init_edge_state = state_all
    and init_sel = init_sel
  apply unfold_locales
  apply (all \<open>(rule NSinit_tree_corr NSinit_strict NSinit_pot_fits NSinit_flow_fits_ns
                     arb_invar_Sarb NSinit_sel_invar
                     NSinit_flow_invar NSinit_es_invar_len NSinit_par_invar NSinit_dir_invar
                     pot_valid_build_tree NSinit_bflow_ne[OF some] NSinit_partition_aug[OF some]
                     NSinit_selfloop[OF some])?\<close>)
  done

lemma init_state_eq:
  "network_simplex_init_spec.init_state flow_all (ds_pot art_tree) (tree_st art_tree)
      (ds_par art_tree) (ds_dir art_tree) state_all init_sel = NSinit.init_state"
  by (simp add: NSinit.init_state_def network_simplex_init_spec.init_state_def Sarb_tree_st)

lemma solve_eq:
  "solve = (case acyc_flow_opt of None \<Rightarrow> Neg_inf_cycle
            | Some _ \<Rightarrow> (let s = NS.ns_loop NSinit.init_state; f = current_flow s
                        in if return s = unbounded then Neg_inf_cycle
                           else if list_all (\<lambda>k. f ! k = 0) [m..<m + Kart]
                                then Optimum (take m f) else Infeasible))"
proof-
  have "NS.ns_loop_impl (network_simplex_init_spec.init_state flow_all (ds_pot art_tree) (tree_st art_tree)
      (ds_par art_tree) (ds_dir art_tree) state_all init_sel) = NS.ns_loop NSinit.init_state"
    by (simp only: init_state_eq) (rule NS.ns_loop_dom_impl_same[OF NSinit.network_simplex_correct(1)])
  thus ?thesis by (simp only: solve_def Let_def)
qed

lemma solve_success: "solve \<noteq> Neg_inf_cycle \<Longrightarrow> return (NS.ns_loop NSinit.init_state) = success"
  using some ns_loop_terminates[OF NSinit.network_simplex_correct(1)]
  by (auto simp: solve_eq Let_def split: option.splits if_splits)

lemma solve_not_negI:
  "\<lbrakk>acyc_flow_opt = Some f'; return (NS.ns_loop NSinit.init_state) \<noteq> unbounded\<rbrakk>
   \<Longrightarrow> solve = (if list_all (\<lambda>k. current_flow (NS.ns_loop NSinit.init_state) ! k = 0)
                          [m..<m + Kart]
                  then Optimum (take m (current_flow (NS.ns_loop NSinit.init_state))) else Infeasible)"
  by (simp add: solve_eq Let_def)

lemma flow_all_len: "m \<le> length (current_flow (NS.ns_loop NSinit.init_state))"
proof-
  have "\<forall>k\<in>{0..<m + Kart}. k < length (current_flow (NS.ns_loop NSinit.init_state))"
    using ns_loop_invar[OF NSinit.network_simplex_correct(1) NSinit.init_state_invar]
    by (simp add: NS.ns_invar_def NS.ns_invar_impl_def)
  thus ?thesis using Kart_pos bspec[of _ _ "m + Kart - 1"] by fastforce
qed

theorem solve_correct_some:
  "solve = Optimum fs \<Longrightarrow> length fs = m
     \<and> original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth fs)"
  "solve = Infeasible \<Longrightarrow> \<nexists> f. original_network.isbflow f (\<lambda>v. h (b_lookup v))"
  "solve = Neg_inf_cycle \<Longrightarrow> neg_infty_cycle"
proof-
  show "solve = Neg_inf_cycle \<Longrightarrow> neg_infty_cycle"
    using some aug_neg_cycle_orig[OF NSinit.network_simplex_correct(2)]
    by (auto simp: solve_eq Let_def split: option.splits if_splits)
next
  assume A: "solve = Optimum fs"
  obtain f' where S: "acyc_flow_opt = Some f'" using some by auto
  have N: "return (NS.ns_loop NSinit.init_state) = success" using A by (intro solve_success) simp
  hence L: "list_all (\<lambda>k. current_flow (NS.ns_loop NSinit.init_state) ! k = 0) [m..<m + Kart]"
    "fs = take m (current_flow (NS.ns_loop NSinit.init_state))"
    using A S solve_not_negI[of f'] by (simp_all split: if_splits)
  have "original_network.is_Opt (\<lambda>v. h (b_lookup v)) (NS.ns_flow_of (NS.ns_loop NSinit.init_state))"
    using L(1) by (intro aug_opt_zero_art_orig_opt[OF NSinit.network_simplex_correct(3)[OF N]])
      (simp add: list_all_iff)
  thus "length fs = m \<and> original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth fs)"
    using L(2) is_Opt_take flow_all_len by simp
next
  assume A: "solve = Infeasible"
  obtain f' where S: "acyc_flow_opt = Some f'" using some by auto
  have N: "return (NS.ns_loop NSinit.init_state) = success" using A by (intro solve_success) simp
  hence "\<exists>k. m \<le> k \<and> k < m + Kart \<and> NS.ns_flow_of (NS.ns_loop NSinit.init_state) k \<noteq> 0"
    using A S solve_not_negI[of f'] by (auto simp: list_all_iff split: if_splits)
  thus "\<nexists> f. original_network.isbflow f (\<lambda>v. h (b_lookup v))"
    by (rule aug_opt_nonzero_art_infeasible[OF NSinit.network_simplex_correct(3)[OF N]])
qed

end

theorem solve_correct:
  "solve = Optimum fs \<Longrightarrow> length fs = m
     \<and> original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth fs)"
  "solve = Infeasible \<Longrightarrow> \<nexists> f. original_network.isbflow f (\<lambda>v. h (b_lookup v))"
  "solve = Neg_inf_cycle \<Longrightarrow> neg_infty_cycle"
  using solve_correct_some solve_none acyc_none_neg_cycle by (cases acyc_flow_opt; force)+

end

end
