
theory Network_Simplex_Initial_Basis_Selector
  imports Network_Simplex_Initial_Basis_Arb
begin

section \<open>A concrete entering-edge selector: candidate-list block search\<close>

text \<open>We implement the @{locale edge_selector} ADT concretely, following the improved block-search
      pseudocode.  The selector state is a record holding a wrap-around \<^emph>\<open>bookmark\<close> into the
      augmented arc set @{term \<open>{0..<m + Kart}\<close>} (an arc is its own index, so \<open>arc_array ! i = i\<close>)
      and a \<^emph>\<open>candidate list\<close> of shortlisted edge ids.  A single call to the selection function
      sees the potentials @{term \<pi>} and the edge-tag array @{term es} as constants; all persistence
      lives in the record, threaded as the ADT's selector value.

      The rule proceeds in two phases.  \<^bold>\<open>Minor iteration\<close> (@{text scan_best}) re-prices the cached
      candidate list against the current @{term \<pi>}/@{term es}, drops the edges that are no longer
      eligible, and returns the most-violating survivor --- so a returned edge is always eligible
      \<^emph>\<open>now\<close>, which is all the ADT demands.  \<^bold>\<open>Major iteration\<close> (@{text scan}) is reached only when the
      cache is exhausted; it sweeps the arc array in blocks from the bookmark, refilling the cache
      (up to @{term max_candidates}) and simultaneously tracking the best edge to return, with a
      ceiling bailout (list full) and a floor bailout (enough fuel, checked at block boundaries).
      If a full sweep of all @{term \<open>m + Kart\<close>} arcs inserts nothing, no eligible edge exists and the
      selector returns @{term None} --- discharging the ADT's @{term None} contract, from which the
      outer loop later derives optimality.\<close>

locale initial_basis_selector =
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


text \<open>The reduced cost @{term \<open>\<c> e + \<pi> (fst e) - \<pi> (snd e)\<close>} assembled in the descriptor type; the
      potentials are looked up in the list-backed potential array.  Its abstract value is faithful to
      the real reduced cost under the network-simplex guard, via @{thm pot_plus_faithful}
      / @{thm pot_minus_faithful}.\<close>


definition rc_val :: "(mtag \<times> 'n) list \<Rightarrow> nat \<Rightarrow> real" where
  "rc_val \<pi> e = pval_abstract bigM (red_cost \<pi> e)"

text \<open>\<^bold>\<open>Faithfulness of the M-free sign tests.\<close>  The executable eligibility test uses the M-free
      \<open>pval_neg\<close> / \<open>pval_pos\<close>; they agree with the true sign of the abstract reduced
      cost @{term \<open>pval_abstract bigM g\<close>} whenever @{term g} satisfies the reduced-cost invariant
      @{const rc_invar} --- its ordinary part is bounded by @{term \<open>3 * sum_list (map abs cost_list)\<close>},
      comfortably below @{term bigM}, so the big-M coefficient alone fixes the sign.  This is where the
      value of @{term bigM} does its work: in the proof, not in the code.\<close>

lemma pval_neg_abstract:
  assumes "rc_invar g" shows "pval_neg g \<longleftrightarrow> pval_abstract bigM g < 0"
proof -
  have ob: "h (snd g) \<le> 3 * h (sum_list (map abs cost_list))"
           "- h (snd g) \<le> 3 * h (sum_list (map abs cost_list))"
    using h_rc_bound[OF assms] by (simp_all add: abs_le_iff)
  have bM: "bigM = 6 * h (sum_list (map abs cost_list)) + 1" by (simp add: bigM_def)
  have s0: "0 \<le> h (sum_list (map abs cost_list))" using sabs_nonneg by simp
  show ?thesis
    using ob bM s0
    by (cases "fst g"; simp_all add: pval_neg_def pval_abstract_def; linarith)
qed

lemma pval_pos_abstract:
  assumes "rc_invar g" shows "pval_pos g \<longleftrightarrow> 0 < pval_abstract bigM g"
proof -
  have ob: "h (snd g) \<le> 3 * h (sum_list (map abs cost_list))"
           "- h (snd g) \<le> 3 * h (sum_list (map abs cost_list))"
    using h_rc_bound[OF assms] by (simp_all add: abs_le_iff)
  have bM: "bigM = 6 * h (sum_list (map abs cost_list)) + 1" by (simp add: bigM_def)
  have s0: "0 \<le> h (sum_list (map abs cost_list))" using sabs_nonneg by simp
  show ?thesis
    using ob bM s0
    by (cases "fst g"; simp_all add: pval_pos_def pval_abstract_def; linarith)
qed

text \<open>An @{term InL} edge is eligible when its reduced cost is negative, an @{term InU} edge when it
      is positive; tree edges are never eligible.  Both tests are the \<^emph>\<open>M-free\<close> \<open>pval_neg\<close> /
      \<open>pval_pos\<close>.  The violation is the magnitude of the reduced cost, and larger violation
      makes a better pivot (compared M-free by \<open>viol_gt\<close>).\<close>



definition gviol :: "mtag \<times> 'n \<Rightarrow> real" where
  "gviol g = \<bar>pval_abstract bigM g\<bar>"

text \<open>\<^bold>\<open>Compute-once evaluation\<close> of an edge.  A single pass reads the tag once and builds the reduced
      cost @{term \<open>red_cost \<pi> e\<close>} once, returning what the two loops need: the eligibility flag (via
      the \<^emph>\<open>M-free\<close> \<open>pval_neg\<close> / \<open>pval_pos\<close>), the @{term in_U} flag, and the reduced-cost
      descriptor @{term g} itself.  \<^emph>\<open>No abstract value and no @{term bigM} multiply is ever formed\<close> ---
      the violation ordering is likewise done M-free by \<open>viol_gt\<close> on the descriptors.  It is the
      executable counterpart of @{const eligible} / @{const ent_in_U} / @{const red_cost}, tied to them
      by @{text evaluate_eq}.\<close>


text \<open>@{const evaluate} short-circuits: for a self-loop it returns @{term False} \<^emph>\<open>without\<close> pricing
      the edge (no @{const red_cost}), so its three projections are: the eligibility flag and the
      @{const ent_in_U} flag always, but the reduced-cost descriptor only on the non-self-loop
      (equivalently, eligible) branch --- which is the only branch where the loop ever reads it.\<close>

lemma evaluate_elig: "fst (evaluate es \<pi> e) = eligible es \<pi> e"
  by (simp add: evaluate_def eligible_def red_cost_def Let_def split: edge_tag.split)

lemma evaluate_inU: "fst (snd (evaluate es \<pi> e)) = ent_in_U es e"
  by (simp add: evaluate_def ent_in_U_def Let_def)

lemma evaluate_red:
  assumes "eligible es \<pi> e" shows "snd (snd (evaluate es \<pi> e)) = red_cost \<pi> e"
proof -
  have "fst_all ! e \<noteq> snd_all ! e" using assms by (simp add: eligible_def)
  thus ?thesis by (simp add: evaluate_def red_cost_def Let_def)
qed

subsection \<open>Selecting the most-violating edge\<close>

text \<open>Offer a candidate to the flat running best: take it if nothing is held yet (@{term \<open>\<not> found\<close>}) or
      it is strictly more violating, otherwise keep the incumbent.  Comparison is \<^emph>\<open>M-free\<close> via
      \<open>viol_gt\<close> on the reduced-cost descriptors (bigger big-M coefficient first, then bigger
      ordinary part); no reduced cost is abstracted through @{term bigM}, and \<^emph>\<open>no option is formed\<close>.\<close>


text \<open>Two array lemmas backing the \<^emph>\<open>swap-with-last\<close> deletion of the minor iteration: the live
      prefix can only shrink (subset), and a still-live element survives the deletion of a
      \<^emph>\<open>different\<close> one.  No distinctness is needed.\<close>

lemma set_take_img: "nn \<le> length xs \<Longrightarrow> set (take nn xs) = (\<lambda>k. xs ! k) ` {0..<nn}"
  by (auto simp: in_set_conv_nth) (metis atLeastLessThan_iff imageI nth_take zero_le)

lemma set_take_swapdel_subset:
  assumes "i < len" "len \<le> length a"
  shows "set (take (len-1) (a[i := a ! (len-1)])) \<subseteq> set (take len a)"
proof -
  have A: "set (take (len-1) (a[i := a!(len-1)])) = (\<lambda>k. (a[i := a!(len-1)]) ! k) ` {0..<len-1}"
    using assms by (intro set_take_img) simp
  have B: "set (take len a) = (\<lambda>k. a ! k) ` {0..<len}" using assms by (intro set_take_img) simp
  show ?thesis unfolding A B using assms by (auto simp: nth_list_update)
qed

lemma mem_survives_swapdel:
  assumes "i < len" "len \<le> length a" "e \<in> set (take len a)" "e \<noteq> a ! i"
  shows "e \<in> set (take (len-1) (a[i := a ! (len-1)]))"
proof -
  have A: "set (take (len-1) (a[i := a!(len-1)])) = (\<lambda>k. (a[i := a!(len-1)]) ! k) ` {0..<len-1}"
    using assms by (intro set_take_img) simp
  have B: "set (take len a) = (\<lambda>k. a ! k) ` {0..<len}" using assms by (intro set_take_img) simp
  from assms(3) B obtain j where j: "j < len" "e = a ! j" by auto
  have jni: "j \<noteq> i" using j assms(4) by auto
  show ?thesis unfolding A
  proof (cases "j = len-1")
    case True
    have iL: "i < len-1" using assms(1) jni True by linarith
    have "(a[i := a!(len-1)]) ! i = e" using j True assms iL by (simp add: nth_list_update)
    thus "e \<in> (\<lambda>k. (a[i := a!(len-1)]) ! k) ` {0..<len-1}" using iL by auto
  next
    case False
    hence jL: "j < len-1" using j by linarith
    have "(a[i := a!(len-1)]) ! j = e" using jni j by (simp add: nth_list_update)
    thus "e \<in> (\<lambda>k. (a[i := a!(len-1)]) ! k) ` {0..<len-1}" using jL by auto
  qed
qed

text \<open>And the lemma backing the \<^emph>\<open>push-at-pointer\<close> insertion of the major iteration.\<close>

lemma take_push_eq:
  assumes "len < length a"
  shows "take (Suc len) (a[len := c]) = take len a @ [c]"
proof -
  have "take (Suc len) (a[len := c]) = take len (a[len := c]) @ [(a[len := c]) ! len]"
    using assms by (simp add: take_Suc_conv_app_nth)
  also have "take len (a[len := c]) = take len a" by simp
  also have "(a[len := c]) ! len = c" using assms by simp
  finally show ?thesis .
qed

lemma set_take_push:
  assumes "len < length a"
  shows "set (take (Suc len) (a[len := c])) = insert c (set (take len a))"
  using take_push_eq[OF assms] by simp

text \<open>The running-best invariant @{term bok}: while the \<^emph>\<open>found\<close> flag is set, the stored edge is
      eligible, its @{term in_U} flag and reduced-cost descriptor are the ones @{const evaluate}
      would compute, and the edge lies in the current live prefix.\<close>


lemma bok_no_best[simp]: "bok es pt no_best a len"
  by (simp add: bok_def no_best_def)

lemma bok_better_keep:
  assumes "bok es pt best a len" "eligible es pt e" "e \<in> set (take len a)"
  shows "bok es pt (better best (e, ent_in_U es e, red_cost pt e)) a len"
  using assms by (cases best) (auto simp: bok_def)

text \<open>\<^bold>\<open>Minor iteration\<close>, in a single pass over the live prefix @{term \<open>take len a\<close>} of the backing
      array @{term a}.  We walk an index @{term i} (against the pointer @{term len}, never against
      @{term \<open>length a\<close>}); a still-eligible entry is kept, priced once, offered to the running best,
      and @{term i} advances; an ineligible (dud) entry is removed by \<^emph>\<open>swap-with-last\<close> --- write the
      last live entry @{term \<open>a ! (len - 1)\<close>} into slot @{term i} and drop the pointer, \<^emph>\<open>without\<close>
      advancing @{term i} --- i.e. the \<open>O(1)\<close> in-place deletion
      @{text \<open>a[i] := a[len - 1]; len := len - 1\<close>}.  The backing list keeps its length (the vacated
      slot @{term \<open>len - 1\<close>} is just left behind the pointer); the result is the same array with the
      pointer moved and the most-violating survivor.\<close>


text \<open>\<^bold>\<open>Specification of the minor iteration.\<close>  From any live prefix, the single pass returns an
      array of unchanged capacity whose new live prefix is no longer than and contained in the old
      one, the running best stays @{const bok} (so a \<^emph>\<open>found\<close> result is a genuine eligible edge of the
      prefix), the \<^emph>\<open>found\<close> flag is monotone, and --- crucially for the @{term None} certificate --- if the
      pass finds nothing then it has emptied the prefix (@{term \<open>rl = i\<close>}, i.e. @{term \<open>rl = 0\<close>} from
      the start pointer @{term \<open>i = 0\<close>}).  Distinctness plays no role.\<close>

lemma scan_cache_spec:
  "i \<le> len \<Longrightarrow> len \<le> length a \<Longrightarrow> bok es pt best a len \<Longrightarrow>
   (case scan_cache es pt i a len best of (ra,rl,rb) \<Rightarrow>
      length ra = length a \<and> rl \<le> len \<and> set (take rl ra) \<subseteq> set (take len a)
      \<and> bok es pt rb ra rl \<and> (fst best \<longrightarrow> fst rb) \<and> (\<not> fst rb \<longrightarrow> rl = i))"
proof (induction es pt i a len best rule: scan_cache.induct)
  case (1 es pt i a len best)
  show ?case
  proof (cases "len \<le> i")
    case True
    hence il: "i = len" using 1(3) by simp
    show ?thesis using True 1(3) 1(4) 1(5) by (simp add: scan_cache.simps[of es pt i] il)
  next
    case False
    note nli = False
    have il: "i < len" using nli by simp
    define e where "e = a ! i"
    obtain elig u g where ev: "evaluate es pt e = (elig, u, g)" by (metis prod_cases3)
    have evd1: "elig = eligible es pt e" using ev evaluate_elig[of es pt e] by simp
    have evd2: "u = ent_in_U es e" using ev evaluate_inU[of es pt e] by simp
    show ?thesis
    proof (cases "eligible es pt e")
      case True
      have eligv: "elig" using evd1 True by simp
      have evd3: "g = red_cost pt e" using ev evaluate_red[OF True] by simp
      have ei: "e \<in> set (take len a)" using set_take_img[OF 1(4)] il e_def by auto
      have step: "scan_cache es pt i a len best = scan_cache es pt (Suc i) a len (better best (e,u,g))" using nli ev eligv by (simp add: scan_cache.simps[of es pt i] e_def Let_def)
      have bok2: "bok es pt (better best (e,u,g)) a len" using bok_better_keep[OF 1(5) True ei] evd2 evd3 by simp
      have fnd: "fst (better best (e,u,g))" by (cases best) auto
      have ilsuc: "Suc i \<le> len" using il by simp
      have IH: "(case scan_cache es pt (Suc i) a len (better best (e,u,g)) of (ra,rl,rb) \<Rightarrow> length ra = length a \<and> rl \<le> len \<and> set (take rl ra) \<subseteq> set (take len a) \<and> bok es pt rb ra rl \<and> (fst (better best (e,u,g)) \<longrightarrow> fst rb) \<and> (\<not> fst rb \<longrightarrow> rl = Suc i))" using 1(1)[OF nli e_def ev[symmetric] refl refl eligv ilsuc 1(4) bok2] by simp
      obtain ra rl rb where r: "scan_cache es pt (Suc i) a len (better best (e,u,g)) = (ra,rl,rb)" by (metis prod_cases3)
      have fbest: "fst rb" using IH fnd r by simp
      show ?thesis unfolding step r using IH r fbest by simp
    next
      case False
      have neligv: "\<not> elig" using evd1 False by simp
      have step: "scan_cache es pt i a len best = scan_cache es pt i (a[i := a ! (len - 1)]) (len-1) best" using nli ev neligv by (simp add: scan_cache.simps[of es pt i] e_def Let_def)
      have lenlen: "len - 1 \<le> length (a[i := a ! (len - 1)])" using 1(4) by simp
      have ile: "i \<le> len - 1" using il by simp
      have sub2: "set (take (len-1) (a[i := a ! (len - 1)])) \<subseteq> set (take len a)" using set_take_swapdel_subset[OF il 1(4)] by simp
      have bok2: "bok es pt best (a[i := a ! (len - 1)]) (len-1)"
      proof (cases "fst best")
        case True
        then obtain e0 u0 g0 where b0: "best = (True,e0,u0,g0)" by (cases best) auto
        have elig0: "eligible es pt e0" and mem0: "e0 \<in> set (take len a)" using 1(5) b0 by (auto simp: bok_def)
        have "e0 \<noteq> e" using elig0 False by (cases "e0 = e") auto
        hence "e0 \<in> set (take (len-1) (a[i := a ! (len - 1)]))" using mem_survives_swapdel[OF il 1(4) mem0] e_def by simp
        thus ?thesis using 1(5) b0 by (auto simp: bok_def)
      next
        case False thus ?thesis by (cases best) (auto simp: bok_def)
      qed
      have IH: "(case scan_cache es pt i (a[i := a ! (len - 1)]) (len-1) best of (ra,rl,rb) \<Rightarrow> length ra = length (a[i := a ! (len-1)]) \<and> rl \<le> len-1 \<and> set (take rl ra) \<subseteq> set (take (len-1) (a[i := a ! (len-1)])) \<and> bok es pt rb ra rl \<and> (fst best \<longrightarrow> fst rb) \<and> (\<not> fst rb \<longrightarrow> rl = i))" using 1(2)[OF nli e_def ev[symmetric] refl refl neligv ile lenlen bok2] by simp
      obtain ra rl rb where r: "scan_cache es pt i (a[i := a ! (len - 1)]) (len-1) best = (ra,rl,rb)" by (metis prod_cases3)
      show ?thesis unfolding step r using IH r sub2 1(4) by auto
    qed
  qed
qed

subsection \<open>Major iteration: block search over the arc array\<close>

text \<open>One straight sweep with three counters: @{term fuel} arcs remain to be scanned overall,
      @{term bpos} arcs remain in the current block (\<open>0\<close> marks a block boundary), and @{term len}
      tracks @{term \<open>length cand\<close>} in \<open>O(1)\<close> so the ceiling/floor tests never re-measure the list.
      We refill up to @{term max_candidates} (ceiling) and stop pulling new blocks once the pointer
      reaches @{term min_candidates} (floor, checked only at boundaries).  An inserted edge is
      \<^emph>\<open>pushed at the pointer\<close> --- @{text \<open>a[len] := cur; len := len + 1\<close>}, the @{const list_update}
      @{term \<open>a[len := cur]\<close>} --- overwriting the stale slot rather than growing the list, so the
      backing array keeps its capacity and nothing is allocated.  The bookmark advances cyclically by a
      \<^emph>\<open>conditional reset\<close> @{term \<open>if cur + 1 = mc then 0 else cur + 1\<close>} rather than a modulo --- a
      compare instead of a division --- which coincides with @{term \<open>(cur + 1) mod mc\<close>} on every state
      reached from a legal bookmark @{term \<open>cur < mc\<close>}.  The arc count @{term mc} (always @{term marc})
      is threaded as a \<^emph>\<open>fixed loop parameter\<close>, so the wrap bound is read from a register each iteration
      rather than re-deriving the locale constant @{term marc} (hence never re-running @{term build_tree}).
      The best edge seen is accumulated for immediate return; termination is by the strictly decreasing
      @{term fuel}.\<close>


text \<open>Cyclic-sweep arithmetic for the block bookmark: the conditional wrap coincides with
      @{term \<open>(cur + 1) mod mc\<close>} and stays in range, and a full sweep of @{term mc} consecutive
      residues from any start covers every arc.\<close>

lemma wrap_eq: "cur < (mc::nat) \<Longrightarrow> (if cur + 1 = mc then 0 else cur + 1) = (cur + 1) mod mc"
  by (cases "cur + 1 = mc") (auto simp: mod_less)

lemma wrap_lt: "0 < (mc::nat) \<Longrightarrow> cur < mc \<Longrightarrow> (if cur + 1 = mc then 0 else cur + 1) < mc"
  by auto

lemma cyc_cover:
  assumes A: "0 < (mc::nat)" and B: "cur < mc" and C: "e < mc"
  shows "\<exists>t<mc. (cur + t) mod mc = e"
proof -
  let ?t = "(e + mc - cur) mod mc"
  have t1: "?t < mc" using A by simp
  have ar: "cur + (e + mc - cur) = e + mc" using B by simp
  have "(cur + ?t) mod mc = (cur + (e + mc - cur)) mod mc" by (metis mod_add_right_eq)
  also have "... = (e + mc) mod mc" using ar by simp
  also have "... = e" using C by simp
  finally have "(cur + ?t) mod mc = e" .
  thus ?thesis using t1 by blast
qed

text \<open>The \<^emph>\<open>found\<close> flag of the major iteration is monotone.\<close>

lemma scan_found_mono:
  "scan es pt mc fuel bpos cur a len best = (cur2,a2,len2,best2) \<Longrightarrow> fst best \<Longrightarrow> fst best2"
proof (induction es pt mc fuel bpos cur a len best arbitrary: cur2 a2 len2 best2 rule: scan.induct)
  case (1 es pt mc fuel bpos cur a len best)
  show ?case
  proof (cases "fuel = 0 \<or> max_candidates \<le> len \<or> (bpos = 0 \<and> min_candidates \<le> len)")
    case True
    hence "scan es pt mc fuel bpos cur a len best = (cur,a,len,best)" by (auto simp: scan.simps[of es pt mc fuel])
    thus ?thesis using 1(2) 1(3) by simp
  next
    case False
    from False have g1: "fuel \<noteq> 0" and g2: "\<not> max_candidates \<le> len" and g3: "\<not> (bpos = 0 \<and> min_candidates \<le> len)" by auto
    obtain elig u g where ev: "evaluate es pt cur = (elig,u,g)" by (metis prod_cases3)
    have step: "scan es pt mc fuel bpos cur a len best = scan es pt mc (fuel-1) ((if bpos=0 then block_size else bpos)-1) (if cur+1=mc then 0 else cur+1) (if elig then a[len:=cur] else a) (if elig then Suc len else len) (if elig then better best (cur,u,g) else best)" using g1 g2 g3 ev by (auto simp: scan.simps[of es pt mc fuel] Let_def)
    have fb1: "fst (if elig then better best (cur,u,g) else best)" using 1(3) by (cases best) auto
    have subeq: "scan es pt mc (fuel-1) ((if bpos=0 then block_size else bpos)-1) (if cur+1=mc then 0 else cur+1) (if elig then a[len:=cur] else a) (if elig then Suc len else len) (if elig then better best (cur,u,g) else best) = (cur2,a2,len2,best2)" using 1(2) step by simp
    show ?thesis using 1(1)[OF g1 g2 g3 refl ev[symmetric] refl refl refl refl refl refl subeq] fb1 by simp
  qed
qed

text \<open>\<^bold>\<open>The @{term None} certificate of the major iteration.\<close>  If the sweep returns with nothing
      found, then it consumed its whole fuel with no eligible arc \<^emph>\<open>anywhere\<close> on the cyclic run --- the
      precondition @{term \<open>\<not> fst best \<longrightarrow> len = 0\<close>} (no insert without a find) rules out the
      ceiling/floor bail-outs.\<close>

lemma scan_none:
  "scan es pt mc fuel bpos cur a len best = (cur2,a2,len2,best2) \<Longrightarrow> \<not> fst best2 \<Longrightarrow> (\<not> fst best \<longrightarrow> len = 0) \<Longrightarrow> 0 < min_candidates \<Longrightarrow> 0 < max_candidates \<Longrightarrow> cur < mc \<Longrightarrow> 0 < mc \<Longrightarrow> (\<forall>t<fuel. \<not> eligible es pt ((cur + t) mod mc))"
proof (induction es pt mc fuel bpos cur a len best arbitrary: cur2 a2 len2 best2 rule: scan.induct)
  case (1 es pt mc fuel bpos cur a len best)
  show ?case
  proof (cases "fuel = 0")
    case True thus ?thesis by simp
  next
    case False
    have nfb: "\<not> fst best" using scan_found_mono[OF 1(2)] 1(3) by blast
    have nlen: "len = 0" using nfb 1(4) by simp
    have g2: "\<not> max_candidates \<le> len" using nlen 1(6) by simp
    have g3: "\<not> (bpos = 0 \<and> min_candidates \<le> len)" using nlen 1(5) by simp
    obtain elig u g where ev: "evaluate es pt cur = (elig,u,g)" by (metis prod_cases3)
    have step: "scan es pt mc fuel bpos cur a len best = scan es pt mc (fuel-1) ((if bpos=0 then block_size else bpos)-1) (if cur+1=mc then 0 else cur+1) (if elig then a[len:=cur] else a) (if elig then Suc len else len) (if elig then better best (cur,u,g) else best)" using False g2 g3 ev by (auto simp: scan.simps[of es pt mc fuel] Let_def)
    have subeq: "scan es pt mc (fuel-1) ((if bpos=0 then block_size else bpos)-1) (if cur+1=mc then 0 else cur+1) (if elig then a[len:=cur] else a) (if elig then Suc len else len) (if elig then better best (cur,u,g) else best) = (cur2,a2,len2,best2)" using 1(2) step by simp
    have curnel: "\<not> eligible es pt cur"
    proof
      assume ec: "eligible es pt cur"
      hence "elig" using ev evaluate_elig[of es pt cur] by simp
      hence "fst (if elig then better best (cur,u,g) else best)" by (cases best) auto
      hence "fst best2" using scan_found_mono[OF subeq] by simp
      thus False using 1(3) by simp
    qed
    have cm: "cur mod mc = cur" using 1(7) by simp
    have t0: "\<not> eligible es pt ((cur + 0) mod mc)" using curnel cm by simp
    have cur1lt: "(if cur+1=mc then 0 else cur+1) < mc" using wrap_lt[OF 1(8) 1(7)] by simp
    have cur1eq: "(if cur+1=mc then 0 else cur+1) = (cur + 1) mod mc" using wrap_eq[OF 1(7)] by simp
    have subPlen: "\<not> fst (if elig then better best (cur,u,g) else best) \<longrightarrow> (if elig then Suc len else len) = 0" using 1(4) by (cases elig; cases best; auto)
    have IH: "\<forall>t<fuel-1. \<not> eligible es pt (((if cur+1=mc then 0 else cur+1) + t) mod mc)" using 1(1)[OF False g2 g3 refl ev[symmetric] refl refl refl refl refl refl subeq 1(3) subPlen 1(5) 1(6) cur1lt 1(8)] .
    show ?thesis
    proof (intro allI impI)
      fix t assume tf: "t < fuel"
      show "\<not> eligible es pt ((cur + t) mod mc)"
      proof (cases "t = 0")
        case True thus ?thesis using t0 by simp
      next
        case False
        hence tm: "t - 1 < fuel - 1" using tf by simp
        have ne: "\<not> eligible es pt (((if cur+1=mc then 0 else cur+1) + (t-1)) mod mc)" using IH tm by blast
        have "((if cur+1=mc then 0 else cur+1) + (t-1)) mod mc = ((cur + 1) mod mc + (t-1)) mod mc" using cur1eq by simp
        also have "... = ((cur + 1) + (t-1)) mod mc" by (rule mod_add_left_eq)
        also have "... = (cur + t) mod mc" using False by simp
        finally show ?thesis using ne by simp
      qed
    qed
  qed
qed

text \<open>\<^bold>\<open>The insertion-side invariants of the major iteration.\<close>  The candidate array keeps its capacity,
      the pointer never exceeds it, the bookmark stays in range, every candidate is a real arc, and the
      running best stays @{const bok}.\<close>

lemma scan_some_spec:
  "scan es pt mc fuel bpos cur a len best = (cur2,a2,len2,best2) \<Longrightarrow> 0 < mc \<Longrightarrow> cur < mc \<Longrightarrow> length a = max_candidates \<Longrightarrow> len \<le> max_candidates \<Longrightarrow> set (take len a) \<subseteq> {0..<mc} \<Longrightarrow> bok es pt best a len \<Longrightarrow> 0 < max_candidates \<Longrightarrow> length a2 = max_candidates \<and> len2 \<le> max_candidates \<and> cur2 < mc \<and> set (take len2 a2) \<subseteq> {0..<mc} \<and> bok es pt best2 a2 len2"
proof (induction es pt mc fuel bpos cur a len best arbitrary: cur2 a2 len2 best2 rule: scan.induct)
  case (1 es pt mc fuel bpos cur a len best)
  show ?case
  proof (cases "fuel = 0 \<or> max_candidates \<le> len \<or> (bpos = 0 \<and> min_candidates \<le> len)")
    case True
    hence "scan es pt mc fuel bpos cur a len best = (cur,a,len,best)" by (auto simp: scan.simps[of es pt mc fuel])
    hence "(cur2,a2,len2,best2) = (cur,a,len,best)" using 1(2) by simp
    thus "length a2 = max_candidates \<and> len2 \<le> max_candidates \<and> cur2 < mc \<and> set (take len2 a2) \<subseteq> {0..<mc} \<and> bok es pt best2 a2 len2" using 1(4) 1(5) 1(6) 1(7) 1(8) by simp
  next
    case False
    from False have g1: "fuel \<noteq> 0" and g2: "\<not> max_candidates \<le> len" and g3: "\<not> (bpos = 0 \<and> min_candidates \<le> len)" by auto
    have lla: "len < length a" using g2 1(5) by simp
    obtain elig u g where ev: "evaluate es pt cur = (elig,u,g)" by (metis prod_cases3)
    have evd1: "elig = eligible es pt cur" using ev evaluate_elig[of es pt cur] by simp
    have evd2: "u = ent_in_U es cur" using ev evaluate_inU[of es pt cur] by simp
    have step: "scan es pt mc fuel bpos cur a len best = scan es pt mc (fuel-1) ((if bpos=0 then block_size else bpos)-1) (if cur+1=mc then 0 else cur+1) (if elig then a[len:=cur] else a) (if elig then Suc len else len) (if elig then better best (cur,u,g) else best)" using g1 g2 g3 ev by (auto simp: scan.simps[of es pt mc fuel] Let_def)
    have subeq: "scan es pt mc (fuel-1) ((if bpos=0 then block_size else bpos)-1) (if cur+1=mc then 0 else cur+1) (if elig then a[len:=cur] else a) (if elig then Suc len else len) (if elig then better best (cur,u,g) else best) = (cur2,a2,len2,best2)" using 1(2) step by simp
    have s_cur: "(if cur+1=mc then 0 else cur+1) < mc" using wrap_lt[OF 1(3) 1(4)] by simp
    have s_len_a: "length (if elig then a[len:=cur] else a) = max_candidates" using 1(5) by (cases elig) simp_all
    have s_len: "(if elig then Suc len else len) \<le> max_candidates" using 1(6) g2 by (cases elig) auto
    have s_range: "set (take (if elig then Suc len else len) (if elig then a[len:=cur] else a)) \<subseteq> {0..<mc}"
    proof (cases elig)
      case True
      have "set (take (Suc len) (a[len:=cur])) = insert cur (set (take len a))" using set_take_push[OF lla] by simp
      thus ?thesis using True 1(4) 1(7) by auto
    next
      case False thus ?thesis using 1(7) by simp
    qed
    have s_bok: "bok es pt (if elig then better best (cur,u,g) else best) (if elig then a[len:=cur] else a) (if elig then Suc len else len)"
    proof (cases elig)
      case True
      have ec: "eligible es pt cur" using evd1 True by simp
      have evd3: "g = red_cost pt cur" using ev evaluate_red[OF ec] by simp
      have setpush: "set (take (Suc len) (a[len:=cur])) = insert cur (set (take len a))" using set_take_push[OF lla] by simp
      have "bok es pt (better best (cur,u,g)) (a[len:=cur]) (Suc len)" using ec evd2 evd3 setpush 1(8) by (cases best) (auto simp: bok_def)
      thus ?thesis using True by simp
    next
      case False thus ?thesis using 1(8) by simp
    qed
    have IH: "length a2 = max_candidates \<and> len2 \<le> max_candidates \<and> cur2 < mc \<and> set (take len2 a2) \<subseteq> {0..<mc} \<and> bok es pt best2 a2 len2" using 1(1)[OF g1 g2 g3 refl ev[symmetric] refl refl refl refl refl refl subeq 1(3) s_cur s_len_a s_len s_range s_bok 1(9)] by simp
    thus "length a2 = max_candidates \<and> len2 \<le> max_candidates \<and> cur2 < mc \<and> set (take len2 a2) \<subseteq> {0..<mc} \<and> bok es pt best2 a2 len2" .
  qed
qed

text \<open>\<^bold>\<open>From the M-free eligibility test to the true reduced-cost sign.\<close>  Under the reduced-cost
      invariant these turn the executable @{const eligible} test into the sign of the abstract reduced
      cost @{term \<open>pval_abstract bigM (red_cost pt e)\<close>}.\<close>

lemma elig_L: "rc_invar (red_cost pt e) \<Longrightarrow> nth es e = InL \<Longrightarrow> eligible es pt e = (fst_all ! e \<noteq> snd_all ! e \<and> pval_abstract bigM (red_cost pt e) < 0)"
  by (simp add: eligible_def pval_neg_abstract)

lemma elig_U: "rc_invar (red_cost pt e) \<Longrightarrow> nth es e = InU \<Longrightarrow> eligible es pt e = (fst_all ! e \<noteq> snd_all ! e \<and> 0 < pval_abstract bigM (red_cost pt e))"
  by (simp add: eligible_def pval_pos_abstract)

text \<open>A found eligible edge is guaranteed a \<^emph>\<open>non-self-loop\<close> (the self-loop skip added to
      @{const eligible}) on top of the sign of its reduced cost.\<close>

lemma sign_helper:
  assumes rc: "rc_invar (red_cost pt e)" and el: "eligible es pt e" and iu: "in_U = ent_in_U es e"
  shows "fst_all ! e \<noteq> snd_all ! e \<and> (if in_U then nth es e = InU \<and> 0 < pval_abstract bigM (red_cost pt e) else nth es e = InL \<and> pval_abstract bigM (red_cost pt e) < 0)"
proof (intro conjI)
  show "fst_all ! e \<noteq> snd_all ! e" using el by (simp add: eligible_def)
next
  show "(if in_U then nth es e = InU \<and> 0 < pval_abstract bigM (red_cost pt e) else nth es e = InL \<and> pval_abstract bigM (red_cost pt e) < 0)"
  proof (cases "nth es e")
    case InTree thus ?thesis using el by (simp add: eligible_def)
  next
    case InL
    hence "\<not> in_U" using iu by (simp add: ent_in_U_def)
    thus ?thesis using InL el elig_L[OF rc InL] by simp
  next
    case InU
    hence "in_U" using iu by (simp add: ent_in_U_def)
    thus ?thesis using InU el elig_U[OF rc InU] by simp
  qed
qed


subsection \<open>The selection function and the selector invariant\<close>

text \<open>Try the cache first; on a hit keep the pruned survivors (bookmark unchanged).  Otherwise run a
      major iteration from the bookmark: return its best, or @{term None} if the whole arc set was
      swept without finding an eligible edge.\<close>


text \<open>The selector invariant records only structural facts about the state --- it cannot mention
      @{term \<pi>} (the ADT invariant sees the selector alone), which is exactly why the minor iteration
      re-validates every cached edge before returning it.  The range bound is stated about the
      \<^emph>\<open>live prefix\<close> @{term \<open>take (sel_len sel) (sel_arr sel)\<close>} (its members are genuine arcs, so a
      returned edge lies in @{term \<E>}); the stale tail beyond the pointer is unconstrained.  The fixed
      capacity is pinned by @{term \<open>length (sel_arr sel) = max_candidates\<close>}, which keeps the pointer a
      legal index for insertion.  Candidate-list \<^emph>\<open>distinctness\<close> is deliberately \<^emph>\<open>not\<close> asserted: the
      ADT axioms never need it (the loop treats \<open>sel_invar_impl\<close> abstractly), so requiring it
      would be pure proof cost.\<close>



lemma sel_invar_init_sel: "sel_invar_impl init_sel"
  by (simp add: sel_invar_impl_def init_sel_def)


subsection \<open>Pricing bridge: reduced-cost faithfulness from the good-potential invariant\<close>

text \<open>The remaining ADT obligation.  The two selector theorems above are stated with the abstract
      reduced cost @{term \<open>pval_abstract bigM (red_cost \<pi> e)\<close>} and a hypothesis
      @{term \<open>rc_invar (red_cost \<pi> e)\<close>}.  Both are discharged from the good-potential invariant that the
      network-simplex loop maintains: every stored potential value is a signed cost sum over augmented
      edges touching the artificial root @{term vcount} at most once (the descriptor-level
      \<open>good_pot_val_c\<close>, the concrete instance of @{term good_pot_val}), and the root's own
      potential is zero.  Under it the coefficient of every potential lies in @{term \<open>{- 1, 0, 1}\<close>} and
      its ordinary part is bounded by @{term \<open>sum_list (map abs cost_list)\<close>}; the clamped tag arithmetic
      is then \<^emph>\<open>faithful\<close> because the reduced-cost coefficient never leaves @{term \<open>{- 2 .. 2}\<close>} (an
      artificial edge always has the coefficient-zero root as one endpoint, ruling out \<open>\<plusminus> 3\<close>).\<close>

lemma pval_plus_faithful_coeff: "- 2 \<le> of_mtag (fst p) + of_mtag (fst g) \<Longrightarrow> of_mtag (fst p) + of_mtag (fst g) \<le> 2 \<Longrightarrow> pval_abstract bigM (pval_plus p g) = pval_abstract bigM p + pval_abstract bigM g"
  unfolding pval_abstract_def pval_plus_def tag_add_def by (simp add: of_mtag_mtag_of algebra_simps h_add)

lemma pval_minus_faithful_coeff: "- 2 \<le> of_mtag (fst p) - of_mtag (fst g) \<Longrightarrow> of_mtag (fst p) - of_mtag (fst g) \<le> 2 \<Longrightarrow> pval_abstract bigM (pval_minus p g) = pval_abstract bigM p - pval_abstract bigM g"
  unfolding pval_abstract_def pval_minus_def tag_sub_def by (simp add: of_mtag_mtag_of algebra_simps)

lemma pval_plus_coeff: "- 2 \<le> of_mtag (fst p) + of_mtag (fst g) \<Longrightarrow> of_mtag (fst p) + of_mtag (fst g) \<le> 2 \<Longrightarrow> of_mtag (fst (pval_plus p g)) = of_mtag (fst p) + of_mtag (fst g)"
  unfolding pval_plus_def tag_add_def by (simp add: of_mtag_mtag_of)

lemma pval_minus_coeff: "- 2 \<le> of_mtag (fst p) - of_mtag (fst g) \<Longrightarrow> of_mtag (fst p) - of_mtag (fst g) \<le> 2 \<Longrightarrow> of_mtag (fst (pval_minus p g)) = of_mtag (fst p) - of_mtag (fst g)"
  unfolding pval_minus_def tag_sub_def by (simp add: of_mtag_mtag_of)

definition good_pot_val_c :: "mtag \<times> 'n \<Rightarrow> bool" where "good_pot_val_c p = (\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1 \<and> pval_abstract bigM p = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e))"

lemma gpv_coeff:
  assumes gp: "good_pot_val_c p" and pv: "pv_invar p"
  shows "of_mtag (fst p) \<in> {- 1, 0, 1} \<and> \<bar>snd p\<bar> \<le> sum_list (map abs cost_list)"
proof -
  define sabs where "sabs = h (sum_list (map abs cost_list))"
  have sabs0: "0 \<le> sabs" using sabs_nonneg by (simp add: sabs_def)
  have bM: "bigM = 6 * sabs + 1" by (simp add: bigM_def sabs_def)
  obtain A D where AD: "A \<subseteq> {0..<m+Kart}" "D \<subseteq> {0..<m+Kart}" "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1" "pval_abstract bigM p = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)" using gp by (auto simp: good_pot_val_c_def)
  obtain e0 R where dec: "e0 \<in> {- 1, 0, 1}" "\<bar>R\<bar> \<le> sabs" "(\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e) = real_of_int e0 * bigM + R" using cost_decompose[OF AD(1) AD(2) AD(3)] by (auto simp: sabs_def)
  define c where "c = of_mtag (fst p)"
  have absp: "pval_abstract bigM p = real_of_int c * bigM + h (snd p)" by (simp add: pval_abstract_def c_def)
  have pb: "\<bar>h (snd p)\<bar> \<le> 2 * sabs" using h_pv_bound[OF pv] by (simp add: sabs_def)
  have eqn: "real_of_int (c - e0) * bigM = R - h (snd p)" using absp AD(4) dec(3) by (simp add: algebra_simps)
  have bnd: "\<bar>R - h (snd p)\<bar> < bigM"
  proof -
    have "\<bar>R - h (snd p)\<bar> \<le> \<bar>R\<bar> + \<bar>h (snd p)\<bar>" by simp
    also have "... \<le> sabs + 2 * sabs" using dec(2) pb by linarith
    also have "... < bigM" using bM sabs0 by linarith
    finally show ?thesis .
  qed
  have "\<bar>real_of_int (c - e0)\<bar> * bigM < bigM" using eqn bnd by (simp add: abs_mult)
  hence lt1: "\<bar>real_of_int (c - e0)\<bar> < 1" using bigM_pos by simp
  have n0: "c - e0 = 0"
  proof -
    have "real_of_int \<bar>c - e0\<bar> < 1" using lt1 by (simp add: of_int_abs)
    hence "\<bar>c - e0\<bar> < 1" by (metis of_int_1 of_int_less_iff)
    thus ?thesis by linarith
  qed
  hence ceq: "c = e0" by simp
  have Req: "h (snd p) = R" using eqn n0 by simp
  have sndbnd: "\<bar>snd p\<bar> \<le> sum_list (map abs cost_list)"
  proof -
    have "\<bar>h (snd p)\<bar> \<le> h (sum_list (map abs cost_list))" using Req dec(2) by (simp add: sabs_def)
    thus ?thesis by (simp add: h_abs[symmetric])
  qed
  show ?thesis using ceq dec(1) sndbnd by (simp add: c_def)
qed

lemma costlist_bound: "e < m \<Longrightarrow> \<bar>cost_list ! e\<bar> \<le> sum_list (map abs cost_list)"
proof -
  { assume e: "e < m"
    have mem: "\<bar>cost_list ! e\<bar> \<in> set (map abs cost_list)" using e length_cost_list_m by (metis length_map nth_map nth_mem)
    have "\<bar>cost_list ! e\<bar> \<le> sum_list (map abs cost_list)" by (rule member_le_sum_list[OF mem]) auto }
  thus "e < m \<Longrightarrow> \<bar>cost_list ! e\<bar> \<le> sum_list (map abs cost_list)" by blast
qed

text \<open>A good potential value whose \<^emph>\<open>abstract\<close> reading is @{term \<open>0::real\<close>} has M-coefficient
      exactly @{term \<open>0::int\<close>}: the ordinary part is bounded by @{term \<open>sum_list (map abs cost_list)\<close>}
      and the M-coefficient lives in @{term \<open>{- 1, 0, 1}\<close>}, while @{term bigM} exceeds that bound, so no
      nonzero coefficient can cancel to zero. This is what lets the abstract root-potential-zero
      precondition of the network-simplex ADT stand in for the concrete @{term pval_zero} the pricing
      used before.\<close>

lemma gpv_root_zero:
  assumes g: "good_pot_val_c p" and pv: "pv_invar p" and z: "pval_abstract bigM p = 0"
  shows "of_mtag (fst p) = 0"
proof -
  define sabs where "sabs = h (sum_list (map abs cost_list))"
  have b1: "of_mtag (fst p) \<in> {- 1, 0, 1}" using gpv_coeff[OF g pv] by simp
  have b2: "\<bar>h (snd p)\<bar> \<le> sabs"
  proof -
    have "\<bar>snd p\<bar> \<le> sum_list (map abs cost_list)" using gpv_coeff[OF g pv] by simp
    hence "h \<bar>snd p\<bar> \<le> h (sum_list (map abs cost_list))" by (rule h_mono)
    thus ?thesis by (simp add: h_abs sabs_def)
  qed
  have bM: "bigM = 6 * sabs + 1" by (simp add: bigM_def sabs_def)
  have s0: "0 \<le> sabs" using sabs_nonneg by (simp add: sabs_def)
  have b2': "- sabs \<le> h (snd p)" "h (snd p) \<le> sabs" using b2 by auto
  have eq: "real_of_int (of_mtag (fst p)) * bigM + h (snd p) = 0" using z by (simp add: pval_abstract_def)
  from b1 consider "of_mtag (fst p) = -1" | "of_mtag (fst p) = 0" | "of_mtag (fst p) = 1" by auto
  thus ?thesis
  proof cases
    case 1
    have "real_of_int (-1) * bigM + h (snd p) = 0" using eq 1 by simp
    hence False using b2' bM s0 by simp
    thus ?thesis by simp
  next
    case 2 thus ?thesis .
  next
    case 3
    have "real_of_int 1 * bigM + h (snd p) = 0" using eq 3 by simp
    hence False using b2' bM s0 by simp
    thus ?thesis by simp
  qed
qed

text \<open>Every augmented edge (@{term \<open>e < marc\<close>}) has both endpoints in the arborescence carrier
      @{term Varb} --- real endpoints in @{term \<open>set vs_list\<close>} (@{thm fst_snd_vs}), artificial endpoints
      in @{term \<open>insert vcount (set vs_list)\<close>} (@{thm build_tree_tail_sub}). Hence the pricing only ever
      reads potentials at vertices where the good-potential invariant is known.\<close>

lemma endpt_in_Varb:
  assumes "e < marc" shows "fst_all ! e \<in> Varb \<and> snd_all ! e \<in> Varb"
proof (cases "e < m")
  case True
  have fe: "fst_all ! e = fst_list ! e" and se: "snd_all ! e = snd_list ! e"
    using True by (simp_all add: fst_all_real snd_all_real)
  have "fst_list ! e \<in> set fst_list \<union> set snd_list" using True by (metis UnI1 len_fst_list_m nth_mem)
  moreover have "snd_list ! e \<in> set fst_list \<union> set snd_list" using True by (metis UnI2 len_snd_list_m nth_mem)
  ultimately have "fst_list ! e \<in> Vseen" "snd_list ! e \<in> Vseen"
    using edged_in_V V_sub_Vseen by auto
  thus ?thesis using fe se by (simp add: Varb_def)
next
  case False
  have emK: "e < m + Kart" using assms by (simp add: marc_def)
  define k where "k = e - m"
  have kdef: "e = m + k" using False by (simp add: k_def)
  have kK: "k < Kart" using emK kdef by simp
  have "ds_afst (build_tree acyc_flow) ! k \<in> insert vcount Vseen \<and> ds_asnd (build_tree acyc_flow) ! k \<in> insert vcount Vseen"
    using build_tree_tail_sub kK by (simp add: tail_sub_def Kart_def seen_set_build_tree)
  moreover have "fst_all ! e = ds_afst (build_tree acyc_flow) ! k" "snd_all ! e = ds_asnd (build_tree acyc_flow) ! k"
    using kdef kK by (simp_all add: fst_all_art snd_all_art)
  ultimately show ?thesis by (simp add: Varb_def)
qed

text \<open>The potential store is \<^emph>\<open>good\<close> when every arborescence vertex carries a good potential value
      (invariant @{const good_pot_val_c} and descriptor bound @{const pv_invar}) and the root
      @{const vcount} reads abstractly as @{term \<open>0::real\<close>}. This is exactly what the network-simplex
      selection precondition supplies once @{term pot_value_invar} is instantiated to the good-potential
      predicate and the abstract root-zero precondition is available; the quantifier ranges over
      @{term Varb} (= the graph vertex set) rather than @{term \<open>{0..<vcount}\<close>}, matching the vertex names
      the algorithm actually uses.\<close>

definition pot_ok :: "(mtag \<times> 'n) list \<Rightarrow> bool" where
  "pot_ok pt = ((\<forall>v\<in>Varb. good_pot_val_c (nth pt v) \<and> pv_invar (nth pt v))
                 \<and> pval_abstract bigM (nth pt vcount) = 0)"

lemma plook_bound:
  assumes ok: "pot_ok pt" and x: "x \<in> Varb"
  shows "of_mtag (fst (nth pt x)) \<in> {- 1, 0, 1} \<and> \<bar>snd (nth pt x)\<bar> \<le> sum_list (map abs cost_list)"
proof -
  have "good_pot_val_c (nth pt x) \<and> pv_invar (nth pt x)"
    using ok x by (simp add: pot_ok_def)
  thus ?thesis using gpv_coeff by blast
qed

lemma endpt_le:
  assumes "e < m + Kart" shows "fst_all ! e \<le> vcount \<and> snd_all ! e \<le> vcount"
proof (cases "e < m")
  case True
  thus ?thesis using real_fst_lt_vcount[of e] real_snd_lt_vcount[of e] by simp
next
  case False
  then obtain k where k: "e = m + k" "k < Kart" using assms by (metis add.commute le_Suc_ex not_le nat_add_left_cancel_less add_diff_inverse_nat)
  have tok: "tail_edge_ok (build_tree acyc_flow) k" using k(2) tail_edge_ok_build_tree by simp
  then obtain subj where s: "subj < vcount"
    "ds_afst (build_tree acyc_flow) ! k = (if art_dir subj then subj else vcount)"
    "ds_asnd (build_tree acyc_flow) ! k = (if art_dir subj then vcount else subj)"
    unfolding tail_edge_ok_def by auto
  show ?thesis using k s by (cases "art_dir subj"; auto simp: fst_all_art snd_all_art)
qed

lemma red_cost_faithful:
  assumes ok: "pot_ok pt" and em: "e < marc"
  shows "rc_invar (red_cost pt e) \<and> pval_abstract bigM (red_cost pt e) = cost_all ! e + pval_abstract bigM (nth pt (fst_all ! e)) - pval_abstract bigM (nth pt (snd_all ! e))"
proof -
  define sabs where "sabs = sum_list (map abs cost_list)"
  have sabs0: "0 \<le> sabs" using sabs_nonneg by (simp add: sabs_def)
  have emK: "e < m + Kart" using em by (simp add: marc_def)
  have lef: "fst_all ! e \<in> Varb" and les: "snd_all ! e \<in> Varb" using endpt_in_Varb[OF em] by auto
  define pf where "pf = nth pt (fst_all ! e)"
  define ps where "ps = nth pt (snd_all ! e)"
  have bf: "of_mtag (fst pf) \<in> {- 1, 0, 1}" "\<bar>snd pf\<bar> \<le> sabs" using plook_bound[OF ok lef] by (auto simp: pf_def sabs_def)
  have bs: "of_mtag (fst ps) \<in> {- 1, 0, 1}" "\<bar>snd ps\<bar> \<le> sabs" using plook_bound[OF ok les] by (auto simp: ps_def sabs_def)
  define cf where "cf = of_mtag (fst pf)"
  define cs where "cs = of_mtag (fst ps)"
  have dmb: "- 2 \<le> cf - cs" "cf - cs \<le> 2" using bf(1) bs(1) by (auto simp: cf_def cs_def)
  have df_abs: "pval_abstract bigM (pval_minus pf ps) = pval_abstract bigM pf - pval_abstract bigM ps" using pval_minus_faithful_coeff dmb by (simp add: cf_def cs_def)
  have df_coeff: "of_mtag (fst (pval_minus pf ps)) = cf - cs" using pval_minus_coeff dmb by (simp add: cf_def cs_def)
  have df_snd: "snd (pval_minus pf ps) = snd pf - snd ps" by (simp add: pval_minus_def)
  have redeq: "red_cost pt e = pval_plus (cost_pval e) (pval_minus pf ps)" by (simp add: red_cost_def pf_def ps_def)
  have ce_abs: "pval_abstract bigM (cost_pval e) = cost_all ! e"
  proof (cases "e < m")
    case True thus ?thesis by (simp add: cost_pval_def pval_abstract_def cost_all_real)
  next
    case False
    hence "cost_pval e = pval_M" by (simp add: cost_pval_def)
    thus ?thesis using emK False by (simp add: pval_M_def pval_abstract_def cost_all_art')
  qed
  have ce_coeff: "of_mtag (fst (cost_pval e)) = (if e < m then 0 else 1)" by (simp add: cost_pval_def pval_M_def)
  have ce_snd: "\<bar>snd (cost_pval e)\<bar> \<le> sabs"
  proof (cases "e < m")
    case True thus ?thesis using costlist_bound by (simp add: cost_pval_def sabs_def)
  next
    case False thus ?thesis using sabs0 by (simp add: cost_pval_def pval_M_def)
  qed
  have outer: "- 2 \<le> of_mtag (fst (cost_pval e)) + (cf - cs) \<and> of_mtag (fst (cost_pval e)) + (cf - cs) \<le> 2"
  proof (cases "e < m")
    case True thus ?thesis using ce_coeff dmb by simp
  next
    case False
    have tr: "fst_all ! e = vcount \<or> snd_all ! e = vcount" using touches_root_iff[OF emK] False by simp
    have z: "cf = 0 \<or> cs = 0"
    proof (cases "fst_all ! e = vcount")
      case True
      have pfv: "pf = nth pt vcount" using True by (simp add: pf_def)
      have g: "good_pot_val_c pf" and pv: "pv_invar pf" using ok r_in_V pfv by (auto simp: pot_ok_def)
      have zz: "pval_abstract bigM pf = 0" using ok pfv by (simp add: pot_ok_def)
      have "of_mtag (fst pf) = 0" using gpv_root_zero[OF g pv zz] .
      thus ?thesis by (simp add: cf_def)
    next
      case False
      hence sv: "snd_all ! e = vcount" using tr by simp
      have psv: "ps = nth pt vcount" using sv by (simp add: ps_def)
      have g: "good_pot_val_c ps" and pv: "pv_invar ps" using ok r_in_V psv by (auto simp: pot_ok_def)
      have zz: "pval_abstract bigM ps = 0" using ok psv by (simp add: pot_ok_def)
      have "of_mtag (fst ps) = 0" using gpv_root_zero[OF g pv zz] .
      thus ?thesis by (simp add: cs_def)
    qed
    show ?thesis using ce_coeff False z bf(1) bs(1) by (auto simp: cf_def cs_def)
  qed
  have "pval_abstract bigM (red_cost pt e) = pval_abstract bigM (cost_pval e) + pval_abstract bigM (pval_minus pf ps)"
    unfolding redeq using pval_plus_faithful_coeff[of "cost_pval e" "pval_minus pf ps"] outer df_coeff by simp
  also have "... = cost_all ! e + pval_abstract bigM pf - pval_abstract bigM ps" using ce_abs df_abs by simp
  finally have faith: "pval_abstract bigM (red_cost pt e) = cost_all ! e + pval_abstract bigM pf - pval_abstract bigM ps" .
  have "snd (red_cost pt e) = snd (cost_pval e) + snd (pval_minus pf ps)" unfolding redeq by (simp add: pval_plus_def)
  hence "\<bar>snd (red_cost pt e)\<bar> \<le> \<bar>snd (cost_pval e)\<bar> + \<bar>snd pf\<bar> + \<bar>snd ps\<bar>" using df_snd by simp
  also have "... \<le> 3 * sabs" using ce_snd bf(2) bs(2) by simp
  finally have rci: "rc_invar (red_cost pt e)" by (simp add: rc_invar_def sabs_def)
  show ?thesis using rci faith by (simp add: pf_def ps_def)
qed


subsection \<open>Preservation of the potential invariant under the network-simplex conditions\<close>

text \<open>The strengthened potential invariant is \<open>pval_pot_invar\<close>: the descriptor bound
      @{const pv_invar} together with the good-potential certificate \<open>good_pot_val_c\<close>.  Under
      exactly the preconditions the network-simplex locale prescribes for its mixed potential
      arithmetic (@{thm[source] pot_plus_faithful} / @{thm[source] pot_minus_faithful}: the operand
      invariants and the \<open>\<le> 1\<close>-root-touch signed-cost-sum certificate for the \<^emph>\<open>result\<close>), a
      @{const pval_plus} / @{const pval_minus} step keeps the invariant.  The certificate needs no work
      of its own: once faithfulness rewrites @{term \<open>pval_abstract bigM (pval_plus p g)\<close>} to
      @{term \<open>pval_abstract bigM p + pval_abstract bigM g\<close>}, the very sets @{term A}, @{term D} witnessing
      the precondition witness \<open>good_pot_val_c\<close> of the result.  These two lemmas are the concrete
      @{text pot_value_plus_spec} / @{text pot_value_minus_spec} obligations of @{locale network_simplex_spec}
      with @{term pot_value_invar} instantiated to \<open>pval_pot_invar\<close>.\<close>

lemma good_pot_val_c_plus:
  assumes pv: "pv_invar p" and rc: "rc_invar g" and cert: "(\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1 \<and> pval_abstract bigM p + pval_abstract bigM g = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e))"
  shows "good_pot_val_c (pval_plus p g)"
proof -
  from cert obtain A D where AD: "A \<subseteq> {0..<m+Kart}" "D \<subseteq> {0..<m+Kart}" "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1" "pval_abstract bigM p + pval_abstract bigM g = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)" by blast
  have "pval_abstract bigM (pval_plus p g) = pval_abstract bigM p + pval_abstract bigM g" using pot_plus_faithful[OF pv rc] cert by blast
  hence "pval_abstract bigM (pval_plus p g) = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)" using AD(4) by simp
  thus ?thesis using AD(1,2,3) by (auto simp: good_pot_val_c_def)
qed

lemma good_pot_val_c_minus:
  assumes pv: "pv_invar p" and rc: "rc_invar g" and cert: "(\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1 \<and> pval_abstract bigM p - pval_abstract bigM g = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e))"
  shows "good_pot_val_c (pval_minus p g)"
proof -
  from cert obtain A D where AD: "A \<subseteq> {0..<m+Kart}" "D \<subseteq> {0..<m+Kart}" "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1" "pval_abstract bigM p - pval_abstract bigM g = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)" by blast
  have "pval_abstract bigM (pval_minus p g) = pval_abstract bigM p - pval_abstract bigM g" using pot_minus_faithful[OF pv rc] cert by blast
  hence "pval_abstract bigM (pval_minus p g) = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)" using AD(4) by simp
  thus ?thesis using AD(1,2,3) by (auto simp: good_pot_val_c_def)
qed

definition pval_pot_invar :: "mtag \<times> 'n \<Rightarrow> bool" where "pval_pot_invar p = (pv_invar p \<and> good_pot_val_c p)"

lemma pot_value_plus_spec_conc:
  assumes "pval_pot_invar p" and "rc_invar g" and cert: "(\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1 \<and> pval_abstract bigM p + pval_abstract bigM g = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e))"
  shows "pval_abstract bigM (pval_plus p g) = pval_abstract bigM p + pval_abstract bigM g \<and> pval_pot_invar (pval_plus p g)"
  using pot_plus_faithful[OF _ assms(2) cert] good_pot_val_c_plus[OF _ assms(2) cert] assms(1) by (simp add: pval_pot_invar_def)

lemma pot_value_minus_spec_conc:
  assumes "pval_pot_invar p" and "rc_invar g" and cert: "(\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1 \<and> pval_abstract bigM p - pval_abstract bigM g = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e))"
  shows "pval_abstract bigM (pval_minus p g) = pval_abstract bigM p - pval_abstract bigM g \<and> pval_pot_invar (pval_minus p g)"
  using pot_minus_faithful[OF _ assms(2) cert] good_pot_val_c_minus[OF _ assms(2) cert] assms(1) by (simp add: pval_pot_invar_def)

lemma maxpos: "0 < max_candidates" using min_candidates_pos min_le_max by simp

text \<open>\<^bold>\<open>The @{term None} axiom \<open>sel_select_None\<close> for this selector.\<close>
      A @{term None} return certifies that every non-tree arc is priced with the optimal sign.  The
      final identification of @{term \<open>pval_abstract bigM (red_cost \<pi> e)\<close>} with the true reduced cost
      @{term \<open>\<c> e + \<pi>(fst e) - \<pi>(snd e)\<close>}, and the hypothesis @{term \<open>rc_invar (red_cost \<pi> e)\<close>}, both
      follow from the good-potential invariant (@{text good_pot_val}) via
      @{thm[source] pot_plus_faithful} / @{thm[source] pot_minus_faithful} at the @{text network_simplex_init}
      interpretation, where @{term pot_value_invar} is instantiated to it.\<close>

lemma sel_select_impl_None:
  assumes inv: "sel_invar_impl sel" and rcinv: "\<And>e. e < marc \<Longrightarrow> rc_invar (red_cost pt e)" and none: "sel_select_impl sel pt es = None"
  shows "(\<forall>e<marc. fst_all ! e \<noteq> snd_all ! e \<longrightarrow> nth es e = InL \<longrightarrow> 0 \<le> pval_abstract bigM (red_cost pt e)) \<and> (\<forall>e<marc. fst_all ! e \<noteq> snd_all ! e \<longrightarrow> nth es e = InU \<longrightarrow> pval_abstract bigM (red_cost pt e) \<le> 0)"
proof -
  have larr: "length (sel_arr sel) = max_candidates" and lenmax: "sel_len sel \<le> max_candidates" and curlt: "0 < marc \<longrightarrow> sel_cur sel < marc" and rng: "set (take (sel_len sel) (sel_arr sel)) \<subseteq> {0..<marc}" using inv by (auto simp: sel_invar_impl_def)
  obtain a1 len1 b1 where sc: "scan_cache es pt 0 (sel_arr sel) (sel_len sel) no_best = (a1,len1,b1)" by (metis prod_cases3)
  have sc_spec: "length a1 = length (sel_arr sel) \<and> len1 \<le> sel_len sel \<and> set (take len1 a1) \<subseteq> set (take (sel_len sel) (sel_arr sel)) \<and> bok es pt b1 a1 len1 \<and> (fst no_best \<longrightarrow> fst b1) \<and> (\<not> fst b1 \<longrightarrow> len1 = 0)" using scan_cache_spec[of 0 "sel_len sel" "sel_arr sel" es pt no_best, unfolded sc] lenmax larr by (simp add: no_best_def bok_def)
  obtain f1 eb ub gb where b1e: "b1 = (f1,eb,ub,gb)" by (cases b1)
  obtain cur2 a2 len2 b2 where scn: "scan es pt marc marc block_size (sel_cur sel) a1 len1 no_best = (cur2,a2,len2,b2)"
    by (cases "scan es pt marc marc block_size (sel_cur sel) a1 len1 no_best" rule: prod_cases4)
  have nf1: "\<not> f1" using none sc b1e scn by (auto simp: sel_select_impl_def split: if_splits)
  have nf2: "\<not> fst b2"
  proof (rule notI)
    assume h: "fst b2"
    obtain e2 u2 g2 where b2e: "b2 = (True, e2, u2, g2)" using h by (cases b2) auto
    have "sel_select_impl sel pt es \<noteq> None"
      using sc b1e scn nf1 b2e by (simp add: sel_select_impl_def Let_def)
    thus False using none by simp
  qed
  have len1z: "len1 = 0" using sc_spec nf1 unfolding b1e by force
  have allne: "\<forall>e<marc. \<not> eligible es pt e"
  proof (cases "marc = 0")
    case True thus ?thesis by simp
  next
    case False
    hence mpos: "0 < marc" by simp
    have curm: "sel_cur sel < marc" using curlt mpos by simp
    have sweep: "\<forall>t<marc. \<not> eligible es pt ((sel_cur sel + t) mod marc)" using scan_none[of es pt marc marc block_size "sel_cur sel" a1 len1 no_best cur2 a2 len2 b2] scn nf2 len1z min_candidates_pos maxpos curm mpos by simp
    show ?thesis
    proof (intro allI impI)
      fix e assume "e < marc"
      then obtain t where "t < marc" "(sel_cur sel + t) mod marc = e" using cyc_cover[OF mpos curm] by blast
      thus "\<not> eligible es pt e" using sweep by auto
    qed
  qed
  show ?thesis
  proof (intro conjI allI impI)
    fix e assume e: "e < marc" and neq: "fst_all ! e \<noteq> snd_all ! e" and tg: "nth es e = InL"
    have ne: "\<not> eligible es pt e" using allne e by blast
    show "0 \<le> pval_abstract bigM (red_cost pt e)" using ne neq elig_L[OF rcinv[OF e] tg] by simp
  next
    fix e assume e: "e < marc" and neq: "fst_all ! e \<noteq> snd_all ! e" and tg: "nth es e = InU"
    have ne: "\<not> eligible es pt e" using allne e by blast
    show "pval_abstract bigM (red_cost pt e) \<le> 0" using ne neq elig_U[OF rcinv[OF e] tg] by simp
  qed
qed

text \<open>\<^bold>\<open>The @{term Some} axiom \<open>sel_select_Some\<close> for this selector.\<close>
      A returned edge is a genuine arc @{term \<open>e < marc\<close>}, eligible on its side, with descriptor
      @{term \<open>g = red_cost \<pi> e\<close>}; the selector invariant is preserved.  As for @{term None}, the
      identification of @{term \<open>pval_abstract bigM (red_cost \<pi> e)\<close>} with the true reduced cost and the
      @{term rc_invar} hypothesis are discharged from @{text good_pot_val} at interpretation.\<close>

lemma sel_select_impl_Some:
  assumes inv: "sel_invar_impl sel" and rcinv: "\<And>e. e < marc \<Longrightarrow> rc_invar (red_cost pt e)" and some: "sel_select_impl sel pt es = Some (e,in_U,g,s2)"
  shows "sel_invar_impl s2 \<and> rc_invar g \<and> g = red_cost pt e \<and> e < marc \<and> fst_all ! e \<noteq> snd_all ! e \<and> (if in_U then nth es e = InU \<and> 0 < pval_abstract bigM (red_cost pt e) else nth es e = InL \<and> pval_abstract bigM (red_cost pt e) < 0)"
proof -
  have larr: "length (sel_arr sel) = max_candidates" and lenmax: "sel_len sel \<le> max_candidates" and curlt: "0 < marc \<longrightarrow> sel_cur sel < marc" and rng: "set (take (sel_len sel) (sel_arr sel)) \<subseteq> {0..<marc}" using inv by (auto simp: sel_invar_impl_def)
  obtain a1 len1 b1 where sc: "scan_cache es pt 0 (sel_arr sel) (sel_len sel) no_best = (a1,len1,b1)" by (metis prod_cases3)
  have sc_spec: "length a1 = length (sel_arr sel) \<and> len1 \<le> sel_len sel \<and> set (take len1 a1) \<subseteq> set (take (sel_len sel) (sel_arr sel)) \<and> bok es pt b1 a1 len1 \<and> (fst no_best \<longrightarrow> fst b1) \<and> (\<not> fst b1 \<longrightarrow> len1 = 0)" using scan_cache_spec[of 0 "sel_len sel" "sel_arr sel" es pt no_best, unfolded sc] lenmax larr by (simp add: no_best_def bok_def)
  obtain f1 eb ub gb where b1e: "b1 = (f1,eb,ub,gb)" by (cases b1)
  show ?thesis
  proof (cases f1)
    case True
    have selSome: "sel_select_impl sel pt es = Some (eb, ub, gb, sel\<lparr>sel_arr := a1, sel_len := len1\<rparr>)" using sc b1e True by (simp add: sel_select_impl_def)
    have eq: "e = eb" "in_U = ub" "g = gb" "s2 = sel\<lparr>sel_arr := a1, sel_len := len1\<rparr>" using some selSome by auto
    have bokd: "eligible es pt eb \<and> ub = ent_in_U es eb \<and> gb = red_cost pt eb \<and> eb \<in> set (take len1 a1)" using sc_spec b1e True by (simp add: bok_def)
    have em: "e < marc" using bokd sc_spec eq rng by auto
    have ge: "g = red_cost pt e" using bokd eq by simp
    have rc: "rc_invar (red_cost pt e)" using rcinv[OF em] by simp
    have siv: "sel_invar_impl s2" using eq larr lenmax sc_spec rng curlt by (auto simp: sel_invar_impl_def)
    have el: "eligible es pt e" using bokd eq by simp
    have iu: "in_U = ent_in_U es e" using bokd eq by simp
    have sgn: "fst_all ! e \<noteq> snd_all ! e \<and> (if in_U then nth es e = InU \<and> 0 < pval_abstract bigM (red_cost pt e) else nth es e = InL \<and> pval_abstract bigM (red_cost pt e) < 0)" using sign_helper[OF rc el iu] .
    show ?thesis using siv rc ge em sgn by simp
  next
    case False
    hence len1z: "len1 = 0" using sc_spec b1e by force
    obtain cur2 a2 len2 b2 where scn:
"scan es pt marc marc block_size (sel_cur sel) a1 len1 no_best
 = (cur2,a2,len2,b2)" by (cases "scan es pt marc marc block_size (sel_cur sel) a1 len1 no_best" rule: prod_cases4)
    have sel2: "sel_select_impl sel pt es = (case b2 of (found2,e2,u2,g2) \<Rightarrow> if found2 then Some (e2, u2, g2, \<lparr>sel_cur = cur2, sel_arr = a2, sel_len = len2\<rparr>) else None)" using sc b1e False scn by (simp add: sel_select_impl_def)
    obtain f2 eb2 ub2 gb2 where b2e: "b2 = (f2,eb2,ub2,gb2)" by (cases b2)
    have f2t: "f2" using some sel2 b2e by (auto split: if_splits)
    have mpos: "0 < marc"
    proof (rule ccontr)
      assume "\<not> 0 < marc"
      hence m0: "marc = 0" by simp
      have "scan es pt 0 0 block_size (sel_cur sel) a1 len1 no_best = (sel_cur sel, a1, len1, no_best)" by (subst scan.simps) simp
      hence "b2 = no_best" using scn m0 by simp
      thus False using f2t b2e by (simp add: no_best_def)
    qed
    have curm: "sel_cur sel < marc" using curlt mpos by simp
    have la1: "length a1 = max_candidates" using sc_spec larr by force
    have some_spec: "length a2 = max_candidates \<and> len2 \<le> max_candidates \<and> cur2 < marc \<and> set (take len2 a2) \<subseteq> {0..<marc} \<and> bok es pt b2 a2 len2" using scan_some_spec[of es pt marc marc block_size "sel_cur sel" a1 len1 no_best cur2 a2 len2 b2] scn mpos curm la1 len1z maxpos by simp
    have selSome: "sel_select_impl sel pt es = Some (eb2, ub2, gb2, \<lparr>sel_cur = cur2, sel_arr = a2, sel_len = len2\<rparr>)" using sel2 f2t b2e by simp
    have eq: "e = eb2" "in_U = ub2" "g = gb2" "s2 = \<lparr>sel_cur = cur2, sel_arr = a2, sel_len = len2\<rparr>" using some selSome by auto
    have bokd: "eligible es pt eb2 \<and> ub2 = ent_in_U es eb2 \<and> gb2 = red_cost pt eb2 \<and> eb2 \<in> set (take len2 a2)" using some_spec b2e f2t by (simp add: bok_def)
    have em: "e < marc" using bokd some_spec eq by auto
    have ge: "g = red_cost pt e" using bokd eq by simp
    have rc: "rc_invar (red_cost pt e)" using rcinv[OF em] by simp
    have siv: "sel_invar_impl s2" using eq some_spec mpos by (auto simp: sel_invar_impl_def)
    have el: "eligible es pt e" using bokd eq by simp
    have iu: "in_U = ent_in_U es e" using bokd eq by simp
    have sgn: "fst_all ! e \<noteq> snd_all ! e \<and> (if in_U then nth es e = InU \<and> 0 < pval_abstract bigM (red_cost pt e) else nth es e = InL \<and> pval_abstract bigM (red_cost pt e) < 0)" using sign_helper[OF rc el iu] .
    show ?thesis using siv rc ge em sgn by simp
  qed
qed

subsection \<open>The ADT axioms, unconditionally, from the good-potential invariant\<close>

text \<open>Folding @{thm red_cost_faithful} into the two theorems above yields exactly the shape of
      \<open>sel_select_Some\<close> / \<open>sel_select_None\<close>: the
      abstract reduced cost @{term \<open>rcabs \<pi> e\<close>} (the concrete @{term reduced_cost}) with no leftover
      @{const rc_invar} hypothesis.  These are what the @{text network_simplex_init} interpretation feeds
      to the ADT, instantiating @{term pot_value_invar} with the good-potential predicate so that
      @{term pot_valid} entails @{const pot_ok}.\<close>

definition rcabs :: "(mtag \<times> 'n) list \<Rightarrow> nat \<Rightarrow> real" where "rcabs pt e = cost_all ! e + pval_abstract bigM (nth pt (fst_all ! e)) - pval_abstract bigM (nth pt (snd_all ! e))"

lemma sel_select_impl_None_final:
  assumes inv: "sel_invar_impl sel" and ok: "pot_ok pt" and none: "sel_select_impl sel pt es = None"
  shows "(\<forall>e<marc. fst_all ! e \<noteq> snd_all ! e \<longrightarrow> nth es e = InL \<longrightarrow> 0 \<le> rcabs pt e) \<and> (\<forall>e<marc. fst_all ! e \<noteq> snd_all ! e \<longrightarrow> nth es e = InU \<longrightarrow> rcabs pt e \<le> 0)"
proof -
  have rcinv: "\<And>e. e < marc \<Longrightarrow> rc_invar (red_cost pt e)" using red_cost_faithful[OF ok] by simp
  have base: "(\<forall>e<marc. fst_all ! e \<noteq> snd_all ! e \<longrightarrow> nth es e = InL \<longrightarrow> 0 \<le> pval_abstract bigM (red_cost pt e)) \<and> (\<forall>e<marc. fst_all ! e \<noteq> snd_all ! e \<longrightarrow> nth es e = InU \<longrightarrow> pval_abstract bigM (red_cost pt e) \<le> 0)" using sel_select_impl_None[OF inv rcinv none] .
  show ?thesis
  proof (intro conjI allI impI)
    fix e assume e: "e < marc" and neq: "fst_all ! e \<noteq> snd_all ! e" and t: "nth es e = InL"
    have "0 \<le> pval_abstract bigM (red_cost pt e)" using base e neq t by blast
    thus "0 \<le> rcabs pt e" using red_cost_faithful[OF ok e] by (simp add: rcabs_def)
  next
    fix e assume e: "e < marc" and neq: "fst_all ! e \<noteq> snd_all ! e" and t: "nth es e = InU"
    have "pval_abstract bigM (red_cost pt e) \<le> 0" using base e neq t by blast
    thus "rcabs pt e \<le> 0" using red_cost_faithful[OF ok e] by (simp add: rcabs_def)
  qed
qed

lemma sel_select_impl_Some_final:
  assumes inv: "sel_invar_impl sel" and ok: "pot_ok pt" and some: "sel_select_impl sel pt es = Some (e,in_U,g,s2)"
  shows "sel_invar_impl s2 \<and> rc_invar g \<and> pval_abstract bigM g = rcabs pt e \<and> e < marc \<and> fst_all ! e \<noteq> snd_all ! e \<and> (if in_U then nth es e = InU \<and> 0 < rcabs pt e else nth es e = InL \<and> rcabs pt e < 0)"
proof -
  have rcinv: "\<And>e. e < marc \<Longrightarrow> rc_invar (red_cost pt e)" using red_cost_faithful[OF ok] by simp
  have base: "sel_invar_impl s2 \<and> rc_invar g \<and> g = red_cost pt e \<and> e < marc \<and> fst_all ! e \<noteq> snd_all ! e \<and> (if in_U then nth es e = InU \<and> 0 < pval_abstract bigM (red_cost pt e) else nth es e = InL \<and> pval_abstract bigM (red_cost pt e) < 0)" using sel_select_impl_Some[OF inv rcinv some] .
  have em: "e < marc" and geq: "g = red_cost pt e" using base by auto
  have rcf: "pval_abstract bigM (red_cost pt e) = rcabs pt e" using red_cost_faithful[OF ok em] by (simp add: rcabs_def)
  show ?thesis using base geq rcf by (simp split: if_splits)
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
    and \<u> = "\<lambda> e. if e < m+Kart then (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) else \<infinity>"
    and \<c> = "\<lambda> e. cost_all ! e"
    and r = vcount
    and shift_pot = shift_pot_impl
    and arborescense_invar = "arb_invar vcount Varb"
    and abstract_arborescense = abstract_arb
    and get_path_pair = get_path_pair_impl
    and swap_edge = swap_edge_impl
    and flow_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and flow_upd = list_update and flow_lookup = nth
    and pot_invar = "\<lambda>xs. \<forall>v\<in>Varb. v < length xs" and pot_upd = list_update and pot_lookup = nth
    and parent_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and parent_upd = list_update and parent_lookup = nth
    and dir_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and dir_upd = list_update and dir_lookup = nth
    and es_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and es_upd = list_update and es_lookup = nth
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
  subgoal premises p using p NSg_verts_Varb by (metis general_axiom3)
  subgoal premises p using p NSg_verts_Varb by (metis Vs_abstract_arb)
  subgoal premises p by (rule get_path_pair_axiom1[OF p(1) p(2) p(3) p(4)[simplified NSg_verts_Varb] p(5)[simplified NSg_verts_Varb]])
  subgoal premises p by (rule get_path_pair_axiom2[OF p(1) p(2) p(3) p(4)[simplified NSg_verts_Varb] p(5)[simplified NSg_verts_Varb]])
  subgoal premises p by (rule swap_edge_axiom1[OF p(1) p(2) p(3) p(4) p(5) p(6) p(7)[simplified NSg_verts_Varb] p(8)[simplified NSg_verts_Varb]])
  subgoal premises p by (rule swap_edge_axiom2[OF p(1) p(2) p(3) p(4) p(5) p(6) p(7)[simplified NSg_verts_Varb] p(8)[simplified NSg_verts_Varb]])
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
  subgoal by auto \<comment> \<open>cap sentinel: (cap = -1) {\isasymlongleftrightarrow} ({\isasymu} = {\isasyminfinity})\<close>
  subgoal by auto \<comment> \<open>cap value on the non-sentinel branch\<close>
  subgoal using cap_all_nonneg by auto \<comment> \<open>cap validity: 0 {\isasymle} cap {\isasymor} cap = -1\<close>
  subgoal premises p for sel \<pi> es e in_U \<gamma> sel'
  proof -
    have ok: "pot_ok \<pi>" using p(3)[simplified NSg_verts_Varb] p(4) by (simp add: pot_ok_def)
    show ?thesis using sel_select_impl_Some_final[OF p(1) ok p(6)] by (auto simp: rcabs_def marc_def)
  qed
  subgoal premises p for sel \<pi> es
  proof -
    have ok: "pot_ok \<pi>" using p(3)[simplified NSg_verts_Varb] p(4) by (simp add: pot_ok_def)
    show ?thesis using sel_select_impl_None_final[OF p(1) ok p(6)] by (auto simp: rcabs_def marc_def)
  qed
  subgoal premises p for p g
  proof -
    have pv: "pv_invar p" and gc: "good_pot_val_c p" using p(1) by auto
    have rc: "rc_invar g" using p(2) .
    have cert: "\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1 \<and> pval_abstract bigM p + pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D"
    proof -
      from p(3) obtain A D where AD: "A \<subseteq> {0..<m+Kart}" "D \<subseteq> {0..<m+Kart}"
        "card {e \<in> A \<union> D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount \<or> (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} \<le> 1"
        "pval_abstract bigM p + pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D" by (elim exE conjE)
      have SE: "{e \<in> A \<union> D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount \<or> (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} = {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount}"
        using AD(1,2) by auto
      have "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1" using AD(3) SE by simp
      thus ?thesis using AD(1,2,4) by (intro exI[of _ A] exI[of _ D]) auto
    qed
    show ?thesis using pot_plus_faithful[OF pv rc cert] good_pot_val_c_plus[OF pv rc cert] by simp
  qed
  subgoal premises p for p g
  proof -
    have pv: "pv_invar p" and gc: "good_pot_val_c p" using p(1) by auto
    have rc: "rc_invar g" using p(2) .
    have cert: "\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1 \<and> pval_abstract bigM p - pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D"
    proof -
      from p(3) obtain A D where AD: "A \<subseteq> {0..<m+Kart}" "D \<subseteq> {0..<m+Kart}"
        "card {e \<in> A \<union> D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount \<or> (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} \<le> 1"
        "pval_abstract bigM p - pval_abstract bigM g = sum ((!) cost_all) A - sum ((!) cost_all) D" by (elim exE conjE)
      have SE: "{e \<in> A \<union> D. (if e < m+Kart then fst_all ! e else fst (prod_decode (e - (m+Kart)))) = vcount \<or> (if e < m+Kart then snd_all ! e else snd (prod_decode (e - (m+Kart)))) = vcount} = {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount}"
        using AD(1,2) by auto
      have "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1" using AD(3) SE by simp
      thus ?thesis using AD(1,2,4) by (intro exI[of _ A] exI[of _ D]) auto
    qed
    show ?thesis using pot_minus_faithful[OF pv rc cert] good_pot_val_c_minus[OF pv rc cert] by simp
  qed
  subgoal premises p by (rule shift_pot_impl_spec[OF p(1) p(2)[simplified NSg_verts_Varb]])
  done


subsection \<open>Assembling the @{locale network_simplex_init} correctness obligations\<close>

text \<open>The concrete starting basis discharges five of the ten @{locale network_simplex_init}
      obligations directly from the proved @{const build_tree} corollaries: the two trivial ones
      (store invariant and @{thm arb_invar_Sarb}), the selector seed @{const init_sel}, the flow/edge
      partition fit (@{thm build_tree_tail_content} together with the real-edge status lemmas), and the
      potential fit (@{thm build_tree_rc_zero} together with @{thm build_tree_root_pot}). The remaining
      five --- @{term \<open>NS.pot_valid\<close>}, the @{term \<open>NS.isbflow\<close>}, the spanning-tree partition, strong
      feasibility and the tree correspondence --- need additional carried invariants and are left as
      \<^emph>\<open>sorry\<close> for now.\<close>

lemma NS_V_Varb: "NS.\<V> = Varb" using NSg_verts_Varb by simp

lemma NS_V_minus_root: "NS.\<V> - {vcount} = Vseen"
  using NS_V_Varb by (auto simp: Varb_def Vseen_def)

lemma NS_V_minus_root_sub: "NS.\<V> - {vcount} \<subseteq> set vs_list"
  using NS_V_minus_root Vseen_eq_V V_sub_vs_list by simp

lemma len_par_bt: "length (ds_par (build_tree acyc_flow)) = Suc vcount"
  using build_tree_inv by (simp add: dfs_inv_def dfs_sized_def)

lemma len_dir_bt: "length (ds_dir (build_tree acyc_flow)) = Suc vcount"
  using build_tree_inv by (simp add: dfs_inv_def dfs_sized_def)

lemma plook_par: "v \<in> set vs_list \<Longrightarrow> nth (ds_par (build_tree acyc_flow)) v = ds_par (build_tree acyc_flow) ! v"
  by simp

lemma plook_dir: "v \<in> set vs_list \<Longrightarrow> nth (ds_dir (build_tree acyc_flow)) v = ds_dir (build_tree acyc_flow) ! v"
  by simp

text \<open>Every non-root tree vertex's parent edge index lies inside the augmented edge range: interior
      vertices point at a real free edge (below @{term m}), component roots at their artificial edge.\<close>

lemma par_lt_marc:
  assumes w: "w < vcount" "ds_seen (build_tree acyc_flow) ! w"
  shows "ds_par (build_tree acyc_flow) ! w < m + Kart"
proof (cases "ds_prnt (build_tree acyc_flow) ! w < vcount")
  case True
  have "ds_par (build_tree acyc_flow) ! w < m" using build_tree_par_edge[OF w True] by simp
  thus ?thesis by simp
next
  case False
  have tsi: "tree_seen_inv (build_tree acyc_flow)" using build_tree_inv by (simp add: dfs_inv_def)
  have "ds_prnt (build_tree acyc_flow) ! w = vcount" using tsi w False unfolding tree_seen_inv_def by blast
  hence cr: "comproot_edge_ok (build_tree acyc_flow) w" using build_tree_comproot_inv w by (simp add: comproot_inv_def)
  have "ds_par (build_tree acyc_flow) ! w - m < Kart" using cr by (simp add: comproot_edge_ok_def Kart_def)
  moreover have "m \<le> ds_par (build_tree acyc_flow) ! w" using cr by (simp add: comproot_edge_ok_def)
  ultimately show ?thesis by simp
qed

lemma pval_abstract_zero: "pval_abstract bigM pval_zero = 0"
  by (simp add: pval_abstract_def pval_zero_def)

text \<open>Obligation 8 (\<open>potential_fits_spanning_tree_partition\<close>): the root potential is zero
      (@{thm build_tree_root_pot}) and every tree edge has zero reduced cost (@{thm build_tree_rc_zero}).\<close>

lemma NSinit_pot_fits:
  "NS.potential_fits_spanning_tree_partition vcount
     (nth (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}))
     (NS.abstract_pot (ds_pot (build_tree acyc_flow)))"
proof (unfold NS.potential_fits_spanning_tree_partition_def, intro conjI ballI)
  show "NS.abstract_pot (ds_pot (build_tree acyc_flow)) vcount = 0"
    using build_tree_root_pot plook_pot[of vcount] pval_abstract_zero by simp
next
  fix e assume "e \<in> nth (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})"
  then obtain v where v: "v \<in> Vseen" and e: "e = ds_par (build_tree acyc_flow) ! v"
    using NS_V_minus_root by auto
  have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
  show "cost_all ! e
          + NS.abstract_pot (ds_pot (build_tree acyc_flow)) (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))))
          - NS.abstract_pot (ds_pot (build_tree acyc_flow)) (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) = 0"
    by (simp only: e if_P[OF par_lt_marc[OF vlt vseen]] build_tree_rc_zero[OF vlt vseen])
qed

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

lemma art_InU_flow_cap:
  assumes k: "k < Kart" and u: "ds_aest (build_tree acyc_flow) ! k = InU"
  shows "ds_aflw (build_tree acyc_flow) ! k = ds_acap (build_tree acyc_flow) ! k \<and> 0 \<le> ds_acap (build_tree acyc_flow) ! k"
  using tail_edge_ok_build_tree[OF k] u by (auto simp: tail_edge_ok_def art_flow_def)

lemma NSinit_flow_fits:
  "NS.flow_fits_spanning_tree_partition
     (nth (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}))
     {e \<in> {0..<m + Kart}. nth state_all e = InL}
     {e \<in> {0..<m + Kart}. nth state_all e = InU}
     (\<lambda>e. h (nth flow_all e))"
proof (unfold NS.flow_fits_spanning_tree_partition_def, intro conjI ballI)
  fix e assume "e \<in> {e \<in> {0..<m + Kart}. nth state_all e = InL}"
  hence e: "e < m + Kart" and sl: "nth state_all e = InL" by auto
  from sl slook[OF e] have st: "state_all ! e = InL" by simp
  show "h (nth flow_all e) = 0"
  proof (cases "e < m")
    case True
    have "(edge_state acyc_flow) ! e = InL" using st state_all_real[OF True] by simp
    hence "acyc_flow ! e = 0" using edge_state_InL_iff[OF True] by simp
    thus ?thesis using flook[OF e] flow_all_real[OF True] by simp
  next
    case False
    then obtain k where ek: "e = m + k" by (metis add.commute le_Suc_ex not_less)
    have kK: "k < Kart" using e ek by simp
    have "state_all ! e = ds_aest (build_tree acyc_flow) ! k" using ek kK state_all_art by simp
    thus ?thesis using st art_state_not_InL[OF kK] by simp
  qed
next
  fix e assume "e \<in> {e \<in> {0..<m + Kart}. nth state_all e = InU}"
  hence e: "e < m + Kart" and sl: "nth state_all e = InU" by auto
  from sl slook[OF e] have st: "state_all ! e = InU" by simp
  show "ereal (h (nth flow_all e))
        = (if e < m + Kart then if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e)) else \<infinity>)"
  proof (cases "e < m")
    case True
    have es: "(edge_state acyc_flow) ! e = InU" using st state_all_real[OF True] by simp
    have "acyc_flow ! e \<noteq> 0 \<and> capacity_list ! e \<noteq> - 1 \<and> acyc_flow ! e = capacity_list ! e"
      using edge_state_InU_iff[OF True] es by simp
    hence fc: "acyc_flow ! e = capacity_list ! e" and cne: "capacity_list ! e \<noteq> - 1" by auto
    have cc: "cap_all ! e = capacity_list ! e" using cap_all_real[OF True] .
    have "nth flow_all e = capacity_list ! e" using flook[OF e] flow_all_real[OF True] fc by simp
    thus ?thesis using cc cne e by simp
  next
    case False
    then obtain k where ek: "e = m + k" by (metis add.commute le_Suc_ex not_less)
    have kK: "k < Kart" using e ek by simp
    have su: "ds_aest (build_tree acyc_flow) ! k = InU" using st ek kK state_all_art by simp
    have fc: "ds_aflw (build_tree acyc_flow) ! k = ds_acap (build_tree acyc_flow) ! k" and cnn: "0 \<le> ds_acap (build_tree acyc_flow) ! k"
      using art_InU_flow_cap[OF kK su] by auto
    have fe: "nth flow_all e = ds_aflw (build_tree acyc_flow) ! k" using flook[OF e] ek kK flow_all_art by simp
    have ce: "cap_all ! e = ds_acap (build_tree acyc_flow) ! k" using ek kK cap_all_art by simp
    have "cap_all ! e \<noteq> - 1" using ce cnn by simp
    thus ?thesis using fe ce fc e by simp
  qed
qed


subsection \<open>A combined DFS invariant: component-root direction and artificial-edge fields\<close>

text \<open>Obligation 9 (strong feasibility) needs, at every component root @{term c}, the tree-edge
      direction @{term \<open>ds_dir (build_tree acyc_flow) ! c = art_dir c\<close>} and the artificial edge's tag/flow/cap.
      These four facts are carried through the builder as a single invariant \<open>cr_ext_inv\<close>,
      proved together with @{const comproot_inv} in one shared @{const build_dfs}/@{const open_tree_component}/
      @{const emit_U_edge}/fold induction.  The direction is frozen by @{const build_dfs} at already-seen
      vertices (\<open>build_dfs_frozen\<close>); the artificial-edge fields sit below the tail cursor and are
      frozen by @{thm build_dfs_art} and update-at-a-fresh-index reasoning.\<close>

lemma bd_upd1_frozen:
  assumes inv: "dfs_inv fl s" and c: "bd_call1_conds fl s" and sx: "ds_seen s ! x"
  shows "ds_prnt (bd_upd1 fl s) ! x = ds_prnt s ! x \<and> ds_par (bd_upd1 fl s) ! x = ds_par s ! x
         \<and> ds_dir (bd_upd1 fl s) ! x = ds_dir s ! x"
proof -
  have wf: "dfs_wf fl s" using inv by (simp add: dfs_inv_def)
  obtain v rest e w c' where
    up: "bd_upd1 fl s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr> else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (rule bd_upd1_eq[OF wf c])
  moreover have "\<not> ds_seen s ! w \<longrightarrow> x \<noteq> w" using sx by auto
  ultimately show ?thesis by (cases "ds_seen s ! w") (simp_all add: dfs_discover_def dfs_push_def Let_def)
qed

lemma bd_upd2_frozen:
  assumes inv: "dfs_inv fl s" and c: "bd_call2_conds fl s" and sx: "ds_seen s ! x"
  shows "ds_prnt (bd_upd2 fl s) ! x = ds_prnt s ! x \<and> ds_par (bd_upd2 fl s) ! x = ds_par s ! x
         \<and> ds_dir (bd_upd2 fl s) ! x = ds_dir s ! x"
proof -
  have wf: "dfs_wf fl s" using inv by (simp add: dfs_inv_def)
  obtain v rest e w c' where
    up: "bd_upd2 fl s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr> else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    by (rule bd_upd2_eq[OF wf c])
  moreover have "\<not> ds_seen s ! w \<longrightarrow> x \<noteq> w" using sx by auto
  ultimately show ?thesis by (cases "ds_seen s ! w") (simp_all add: dfs_discover_def dfs_push_def Let_def)
qed

lemma bd_upd3_frozen:
  assumes c: "bd_call3_conds fl s"
  shows "ds_prnt (bd_upd3 s) ! x = ds_prnt s ! x \<and> ds_par (bd_upd3 s) ! x = ds_par s ! x
         \<and> ds_dir (bd_upd3 s) ! x = ds_dir s ! x"
proof -
  obtain v rest where "bd_upd3 s = dfs_finish s v rest" by (rule bd_upd3_eq[OF c])
  thus ?thesis by (simp add: dfs_finish_def Let_def)
qed

text \<open>@{const build_dfs} freezes the tree fields of an already-seen vertex.\<close>

lemma build_dfs_frozen:
  assumes dom: "build_dfs_dom (fl, s)" and inv0: "dfs_inv fl s" and sx0: "ds_seen s ! x"
  shows "ds_prnt (build_dfs fl s) ! x = ds_prnt s ! x \<and> ds_par (build_dfs fl s) ! x = ds_par s ! x
         \<and> ds_dir (build_dfs fl s) ! x = ds_dir s ! x"
proof -
  have "dfs_inv fl s \<longrightarrow> ds_seen s ! x \<longrightarrow> ds_prnt (build_dfs fl s) ! x = ds_prnt s ! x
          \<and> ds_par (build_dfs fl s) ! x = ds_par s ! x \<and> ds_dir (build_dfs fl s) ! x = ds_dir s ! x"
  proof (induct rule: bd_induct[OF dom])
    case IH: (1 fl s)
    show ?case
    proof (intro impI)
      assume invs: "dfs_inv fl s" and sx: "ds_seen s ! x"
      show "ds_prnt (build_dfs fl s) ! x = ds_prnt s ! x
          \<and> ds_par (build_dfs fl s) ! x = ds_par s ! x \<and> ds_dir (build_dfs fl s) ! x = ds_dir s ! x"
      proof (rule bd_cases[where s=s and fl=fl])
        assume c: "bd_call1_conds fl s"
        have step: "build_dfs fl s = build_dfs fl (bd_upd1 fl s)" using bd_simps(1)[OF IH(1) c] .
        show ?thesis using IH(2)[OF c] bd_upd1_inv[OF invs c] bd_upd1_seen_mono[OF c sx]
            bd_upd1_frozen[OF invs c sx] step by simp
      next
        assume c: "bd_call2_conds fl s"
        have step: "build_dfs fl s = build_dfs fl (bd_upd2 fl s)" using bd_simps(2)[OF IH(1) c] .
        show ?thesis using IH(3)[OF c] bd_upd2_inv[OF invs c] bd_upd2_seen_mono[OF c sx]
            bd_upd2_frozen[OF invs c sx] step by simp
      next
        assume c: "bd_call3_conds fl s"
        have step: "build_dfs fl s = build_dfs fl (bd_upd3 s)" using bd_simps(3)[OF IH(1) c] .
        show ?thesis using IH(4)[OF c] bd_upd3_inv[OF invs c] bd_upd3_seen_mono[OF c sx]
            bd_upd3_frozen[OF c] step by simp
      next
        assume c: "bd_ret_conds s"
        have "build_dfs fl s = s" using bd_simps(4)[OF IH(1) c] .
        thus ?thesis by simp
      qed
    qed
  qed
  thus ?thesis using inv0 sx0 by blast
qed

definition cr_ext_ok :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> bool" where
  "cr_ext_ok s c \<longleftrightarrow> ds_dir s ! c = art_dir c
     \<and> ds_aest s ! (ds_par s ! c - m) = InTree
     \<and> ds_aflw s ! (ds_par s ! c - m) = art_flow c
     \<and> ds_acap s ! (ds_par s ! c - m) = art_tree_cap c"

definition cr_ext_inv :: "'n dfs_state \<Rightarrow> bool" where
  "cr_ext_inv s \<longleftrightarrow> (\<forall>c<vcount. ds_seen s ! c \<longrightarrow> ds_prnt s ! c = vcount \<longrightarrow> cr_ext_ok s c)"

lemma emit_U_edge_crext:
  assumes ci: "comproot_inv s" and ce: "cr_ext_inv s"
  shows "cr_ext_inv (emit_U_edge s v)"
  unfolding cr_ext_inv_def
proof (intro allI impI)
  fix c assume clt: "c < vcount" and sc: "ds_seen (emit_U_edge s v) ! c" and pc: "ds_prnt (emit_U_edge s v) ! c = vcount"
  have seq: "ds_seen (emit_U_edge s v) = ds_seen s" "ds_prnt (emit_U_edge s v) = ds_prnt s"
            "ds_par (emit_U_edge s v) = ds_par s" "ds_dir (emit_U_edge s v) = ds_dir s"
    by (simp_all add: emit_U_edge_def Let_def)
  have sc': "ds_seen s ! c" and pc': "ds_prnt s ! c = vcount" using sc pc seq by simp_all
  have ok: "comproot_edge_ok s c" using ci clt sc' pc' by (simp add: comproot_inv_def)
  have bnd: "ds_par s ! c - m < ds_nxt s" using ok by (simp add: comproot_edge_ok_def)
  have ext: "cr_ext_ok s c" using ce clt sc' pc' by (simp add: cr_ext_inv_def)
  have aest': "ds_aest (emit_U_edge s v) ! (ds_par s ! c - m) = ds_aest s ! (ds_par s ! c - m)"
    using bnd by (simp add: emit_U_edge_def Let_def nth_list_update_neq)
  have aflw': "ds_aflw (emit_U_edge s v) ! (ds_par s ! c - m) = ds_aflw s ! (ds_par s ! c - m)"
    using bnd by (simp add: emit_U_edge_def Let_def nth_list_update_neq)
  have acap': "ds_acap (emit_U_edge s v) ! (ds_par s ! c - m) = ds_acap s ! (ds_par s ! c - m)"
    using bnd by (simp add: emit_U_edge_def Let_def nth_list_update_neq)
  show "cr_ext_ok (emit_U_edge s v) c"
    unfolding cr_ext_ok_def using seq ext aest' aflw' acap' by (simp add: cr_ext_ok_def)
qed

lemma open_tree_component_crext:
  assumes inv: "dfs_inv acyc_flow s" and c: "c < vcount" and unseen: "\<not> ds_seen s ! c" and cnz: "c \<noteq> 0"
      and stke: "ds_stk s = []" and al: "art_len s" and inb: "ds_nxt s < length vs_list"
      and ci: "comproot_inv s" and ce: "cr_ext_inv s"
  shows "cr_ext_inv (open_tree_component acyc_flow s c)"
proof -
  have "dfs_wf acyc_flow s" "dfs_sized s" using inv by (simp_all add: dfs_inv_def)
  then obtain sd where opd: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd"
      and dom: "build_dfs_dom (acyc_flow, sd)"
      and I: "(dfs_inv acyc_flow s \<and> \<not> ds_seen s ! c \<and> c \<noteq> 0 \<and> ds_stk s = []) \<longrightarrow> dfs_inv acyc_flow sd"
      and seensd: "ds_seen sd = (ds_seen s)[c := True]"
      and prntsd: "ds_prnt sd = (ds_prnt s)[c := vcount]"
      and parsd: "ds_par sd = (ds_par s)[c := m + ds_nxt s]"
      and dirsd: "ds_dir sd = (ds_dir s)[c := art_dir c]"
      and acapsd: "ds_acap sd = (ds_acap s)[ds_nxt s := art_tree_cap c]"
      and aflwsd: "ds_aflw sd = (ds_aflw s)[ds_nxt s := art_flow c]"
      and aestsd: "ds_aest sd = (ds_aest s)[ds_nxt s := InTree]"
    using c by (rule open_tree_component_seed)
  have invsd: "dfs_inv acyc_flow sd" using I inv unseen cnz stke by blast
  from build_dfs_art[OF dom]
  have artAe: "ds_aest (build_dfs acyc_flow sd) = ds_aest sd" and artAf: "ds_aflw (build_dfs acyc_flow sd) = ds_aflw sd"
   and artAc: "ds_acap (build_dfs acyc_flow sd) = ds_acap sd" by simp_all
  have lens: "length (ds_par s) = Suc vcount" "length (ds_dir s) = Suc vcount"
    using inv by (simp_all add: dfs_inv_def dfs_sized_def)
  have laest: "length (ds_aest s) = length vs_list" and laflw: "length (ds_aflw s) = length vs_list"
   and lacap: "length (ds_acap s) = length vs_list" using al by (simp_all add: art_len_def)
  show ?thesis
    unfolding cr_ext_inv_def
  proof (intro allI impI)
    fix w assume wlt: "w < vcount" and sw: "ds_seen (open_tree_component acyc_flow s c) ! w"
        and pw: "ds_prnt (open_tree_component acyc_flow s c) ! w = vcount"
    have bw: "ds_seen (build_dfs acyc_flow sd) ! w" using sw opd by simp
    have bpw: "ds_prnt (build_dfs acyc_flow sd) ! w = vcount" using pw opd by simp
    have cr: "ds_seen sd ! w \<and> ds_prnt sd ! w = vcount
              \<and> ds_par (build_dfs acyc_flow sd) ! w = ds_par sd ! w \<and> ds_pot (build_dfs acyc_flow sd) ! w = ds_pot sd ! w"
      using build_dfs_cr[OF dom invsd wlt bw bpw] .
    have swsd: "ds_seen sd ! w" using cr by simp
    have parw: "ds_par (open_tree_component acyc_flow s c) ! w = ds_par sd ! w" using cr opd by simp
    have dirw: "ds_dir (open_tree_component acyc_flow s c) ! w = ds_dir sd ! w"
      using build_dfs_frozen[OF dom invsd swsd] opd by simp
    show "cr_ext_ok (open_tree_component acyc_flow s c) w"
    proof (cases "w = c")
      case True
      have parval: "ds_par (open_tree_component acyc_flow s c) ! w = m + ds_nxt s"
        using parw parsd True c lens by (simp add: nth_list_update_eq)
      have idx: "ds_par (open_tree_component acyc_flow s c) ! w - m = ds_nxt s" using parval by simp
      have dirval: "ds_dir (open_tree_component acyc_flow s c) ! w = art_dir c"
        using dirw dirsd True c lens by (simp add: nth_list_update_eq)
      have aestval: "ds_aest (open_tree_component acyc_flow s c) ! (ds_par (open_tree_component acyc_flow s c) ! w - m) = InTree"
        using opd artAe aestsd idx inb laest by (simp add: nth_list_update_eq)
      have aflwval: "ds_aflw (open_tree_component acyc_flow s c) ! (ds_par (open_tree_component acyc_flow s c) ! w - m) = art_flow c"
        using opd artAf aflwsd idx inb laflw by (simp add: nth_list_update_eq)
      have acapval: "ds_acap (open_tree_component acyc_flow s c) ! (ds_par (open_tree_component acyc_flow s c) ! w - m) = art_tree_cap c"
        using opd artAc acapsd idx inb lacap by (simp add: nth_list_update_eq)
      show ?thesis unfolding cr_ext_ok_def using dirval aestval aflwval acapval True by simp
    next
      case False
      have swseed: "ds_seen s ! w" using swsd seensd False by (simp add: nth_list_update_neq)
      have pwseed: "ds_prnt s ! w = vcount" using cr prntsd False by (simp add: nth_list_update_neq)
      have okw: "comproot_edge_ok s w" using ci wlt swseed pwseed by (simp add: comproot_inv_def)
      have bndw: "ds_par s ! w - m < ds_nxt s" using okw by (simp add: comproot_edge_ok_def)
      have extw: "cr_ext_ok s w" using ce wlt swseed pwseed by (simp add: cr_ext_inv_def)
      have parw2: "ds_par (open_tree_component acyc_flow s c) ! w = ds_par s ! w"
        using parw parsd False by (simp add: nth_list_update_neq)
      have dirw2: "ds_dir (open_tree_component acyc_flow s c) ! w = ds_dir s ! w"
        using dirw dirsd False by (simp add: nth_list_update_neq)
      have idxne: "ds_par s ! w - m \<noteq> ds_nxt s" using bndw by simp
      have aest': "ds_aest (open_tree_component acyc_flow s c) ! (ds_par s ! w - m) = ds_aest s ! (ds_par s ! w - m)"
        using opd artAe aestsd idxne by (simp add: nth_list_update_neq)
      have aflw': "ds_aflw (open_tree_component acyc_flow s c) ! (ds_par s ! w - m) = ds_aflw s ! (ds_par s ! w - m)"
        using opd artAf aflwsd idxne by (simp add: nth_list_update_neq)
      have acap': "ds_acap (open_tree_component acyc_flow s c) ! (ds_par s ! w - m) = ds_acap s ! (ds_par s ! w - m)"
        using opd artAc acapsd idxne by (simp add: nth_list_update_neq)
      show ?thesis unfolding cr_ext_ok_def using extw parw2 dirw2 aest' aflw' acap' by (simp add: cr_ext_ok_def)
    qed
  qed
qed

lemma phase1_step_crext:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" and al: "art_len s"
      and ci: "comproot_inv s" and ce: "cr_ext_inv s" and inb: "ds_nxt (phase1_step acyc_flow v s) \<le> length vs_list"
  shows "cr_ext_inv (phase1_step acyc_flow v s)"
proof (cases "imbalance ! v = 0")
  case True thus ?thesis using ce by (simp add: phase1_step_def)
next
  case nz: False
  have vlt: "v < vcount" using v vs_less_vcount by simp
  show ?thesis
  proof (cases "ds_seen s ! v")
    case seen: True
    have eq: "phase1_step acyc_flow v s = emit_U_edge s v" using nz seen by (simp add: phase1_step_def)
    thus ?thesis using emit_U_edge_crext[OF ci ce] by simp
  next
    case notseen: False
    have vnz: "v \<noteq> 0" using v no_zero_node by metis
    have eq: "phase1_step acyc_flow v s = open_tree_component acyc_flow s v" using nz notseen by (simp add: phase1_step_def)
    have nxt: "ds_nxt (open_tree_component acyc_flow s v) = Suc (ds_nxt s)" using open_tree_component_art(1)[OF inv vlt] .
    have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
    show ?thesis using eq open_tree_component_crext[OF inv vlt notseen vnz stke al inbs ci ce] by simp
  qed
qed

lemma phase2_step_crext:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" and al: "art_len s"
      and ci: "comproot_inv s" and ce: "cr_ext_inv s" and inb: "ds_nxt (phase2_step acyc_flow v s) \<le> length vs_list"
  shows "cr_ext_inv (phase2_step acyc_flow v s)"
proof (cases "ds_seen s ! v \<or> is_lonely v")
  case True thus ?thesis using ce by (simp add: phase2_step_def)
next
  case False
  hence notseen: "\<not> ds_seen s ! v" and nl: "\<not> is_lonely v" by auto
  have vlt: "v < vcount" using v vs_less_vcount by simp
  have vnz: "v \<noteq> 0" using v no_zero_node by metis
  have eq: "phase2_step acyc_flow v s = open_tree_component acyc_flow s v" using notseen nl by (simp add: phase2_step_def)
  have nxt: "ds_nxt (open_tree_component acyc_flow s v) = Suc (ds_nxt s)" using open_tree_component_art(1)[OF inv vlt] .
  have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
  show ?thesis using eq open_tree_component_crext[OF inv vlt notseen vnz stke al inbs ci ce] by simp
qed

lemma fold_emit_crc1:
  assumes "distinct xs" "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "comproot_inv s" "cr_ext_inv s"
      "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "E \<inter> set xs = {}" "ds_nxt s = card E"
  shows "art_len (fold (phase1_step acyc_flow) xs s) \<and> comproot_inv (fold (phase1_step acyc_flow) xs s)
         \<and> cr_ext_inv (fold (phase1_step acyc_flow) xs s)
         \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase1_step acyc_flow) xs s) ! v}
                 \<and> ds_nxt (fold (phase1_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(2) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv1: "dfs_inv acyc_flow (phase1_step acyc_flow x s)" "ds_stk (phase1_step acyc_flow x s) = []"
    using phase1_step_inv[OF xvs conjI[OF Cons.prems(3) Cons.prems(4)]] by auto
  have al1: "art_len (phase1_step acyc_flow x s)" using phase1_step_art_len[OF xvs Cons.prems(3) Cons.prems(5)] .
  have Emono: "E \<subseteq> {v \<in> set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}"
    using Cons.prems(9) phase1_step_seen_mono[OF Cons.prems(3) xlt] by auto
  have Edisj: "E \<inter> set rest = {}" using Cons.prems(10) by auto
  have distr: "distinct rest" using Cons.prems(1) by simp
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(2) by simp
  have Esub: "E \<subseteq> set vs_list" using Cons.prems(9) by auto
  have xnotE: "x \<notin> E" using Cons.prems(10) by auto
  have step_inb: "ds_nxt (phase1_step acyc_flow x s) \<le> length vs_list"
    using phase1_step_nxt[OF Cons.prems(3) xlt]
  proof
    assume "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(11) card_sub_vs_le[OF Esub] by simp
  next
    assume A: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) \<and> ds_seen (phase1_step acyc_flow x s) ! x"
    have "insert x E \<subseteq> set vs_list" using Esub xvs by auto
    hence "card (insert x E) \<le> length vs_list" by (rule card_sub_vs_le)
    thus ?thesis using A Cons.prems(11) xnotE Cons.prems(8) by (simp add: card_insert_disjoint)
  qed
  have ci1: "comproot_inv (phase1_step acyc_flow x s)"
    using phase1_step_cri[OF xvs Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) step_inb] .
  have ce1: "cr_ext_inv (phase1_step acyc_flow x s)"
    using phase1_step_crext[OF xvs Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) Cons.prems(7) step_inb] .
  from phase1_step_nxt[OF Cons.prems(3) xlt] show ?case
  proof
    assume A: "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase1_step acyc_flow x s) = card E" using A Cons.prems(11) by simp
    show ?thesis
      using Cons.hyps[OF distr subr inv1(1) inv1(2) al1 ci1 ce1 Cons.prems(8) Emono Edisj card1] by simp
  next
    assume B: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) \<and> ds_seen (phase1_step acyc_flow x s) ! x"
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(8) by (simp add: E2_def)
    have E2seen: "E2 \<subseteq> {v \<in> set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have E2disj: "E2 \<inter> set rest = {}" using Edisj Cons.prems(1) by (auto simp: E2_def)
    have card2: "ds_nxt (phase1_step acyc_flow x s) = card E2" using B Cons.prems(11) xnotE Cons.prems(8) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF distr subr inv1(1) inv1(2) al1 ci1 ce1 fin2 E2seen E2disj card2] by simp
  qed
qed

lemma fold_emit_crc2:
  assumes "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "comproot_inv s" "cr_ext_inv s"
      "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "ds_nxt s = card E"
  shows "art_len (fold (phase2_step acyc_flow) xs s) \<and> comproot_inv (fold (phase2_step acyc_flow) xs s)
         \<and> cr_ext_inv (fold (phase2_step acyc_flow) xs s)
         \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase2_step acyc_flow) xs s) ! v}
                 \<and> ds_nxt (fold (phase2_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(1) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv1: "dfs_inv acyc_flow (phase2_step acyc_flow x s)" "ds_stk (phase2_step acyc_flow x s) = []"
    using phase2_step_inv[OF xvs conjI[OF Cons.prems(2) Cons.prems(3)]] by auto
  have al1: "art_len (phase2_step acyc_flow x s)" using phase2_step_art_len[OF xvs Cons.prems(2) Cons.prems(4)] .
  have Emono: "E \<subseteq> {v \<in> set vs_list. ds_seen (phase2_step acyc_flow x s) ! v}"
    using Cons.prems(8) phase2_step_seen_mono[OF Cons.prems(2) xlt] by auto
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(1) by simp
  have Esub: "E \<subseteq> set vs_list" using Cons.prems(8) by auto
  have step_inb: "ds_nxt (phase2_step acyc_flow x s) \<le> length vs_list"
    using phase2_step_nxt2[OF Cons.prems(2) xlt]
  proof
    assume "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(9) card_sub_vs_le[OF Esub] by simp
  next
    assume A: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! x \<and> ds_seen (phase2_step acyc_flow x s) ! x"
    have xnotE: "x \<notin> E" using A Cons.prems(8) by auto
    have "insert x E \<subseteq> set vs_list" using Esub xvs by auto
    hence "card (insert x E) \<le> length vs_list" by (rule card_sub_vs_le)
    thus ?thesis using A Cons.prems(9) xnotE Cons.prems(7) by (simp add: card_insert_disjoint)
  qed
  have ci1: "comproot_inv (phase2_step acyc_flow x s)"
    using phase2_step_cri[OF xvs Cons.prems(2) Cons.prems(3) Cons.prems(4) Cons.prems(5) step_inb] .
  have ce1: "cr_ext_inv (phase2_step acyc_flow x s)"
    using phase2_step_crext[OF xvs Cons.prems(2) Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) step_inb] .
  from phase2_step_nxt2[OF Cons.prems(2) xlt] show ?case
  proof
    assume A: "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase2_step acyc_flow x s) = card E" using A Cons.prems(9) by simp
    show ?thesis
      using Cons.hyps[OF subr inv1(1) inv1(2) al1 ci1 ce1 Cons.prems(7) Emono card1] by simp
  next
    assume B: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! x \<and> ds_seen (phase2_step acyc_flow x s) ! x"
    have xnotE: "x \<notin> E" using B Cons.prems(8) by auto
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(7) by (simp add: E2_def)
    have E2seen: "E2 \<subseteq> {v \<in> set vs_list. ds_seen (phase2_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have card2: "ds_nxt (phase2_step acyc_flow x s) = card E2" using B Cons.prems(9) xnotE Cons.prems(7) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF subr inv1(1) inv1(2) al1 ci1 ce1 fin2 E2seen card2] by simp
  qed
qed

lemma build_tree_crext: "cr_ext_inv (build_tree acyc_flow)"
proof -
  have i0: "dfs_inv acyc_flow dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have al0: "art_len dfs_init" by (rule dfs_init_art_len)
  have ci0: "comproot_inv dfs_init" by (simp add: comproot_inv_def dfs_init_def del: replicate_Suc)
  have ce0: "cr_ext_inv dfs_init" by (simp add: cr_ext_inv_def dfs_init_def del: replicate_Suc)
  have C1: "art_len (fold (phase1_step acyc_flow) vs_list dfs_init) \<and> comproot_inv (fold (phase1_step acyc_flow) vs_list dfs_init)
        \<and> cr_ext_inv (fold (phase1_step acyc_flow) vs_list dfs_init)
        \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase1_step acyc_flow) vs_list dfs_init) ! v}
                \<and> ds_nxt (fold (phase1_step acyc_flow) vs_list dfs_init) = card E')"
    apply (rule fold_emit_crc1[where E="{}"])
    subgoal by (rule distinct_vs_list)
    subgoal by simp
    subgoal using i0 by simp
    subgoal using i0 by simp
    subgoal by (rule al0)
    subgoal by (rule ci0)
    subgoal by (rule ce0)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: dfs_init_def)
    done
  have P1: "art_len (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have CI1: "comproot_inv (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have CE1: "cr_ext_inv (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have E1ex: "\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}
                \<and> ds_nxt (phase1 acyc_flow dfs_init) = card E'" using C1 by (simp add: phase1_def)
  have p1inv: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init) \<and> ds_stk (phase1 acyc_flow dfs_init) = []" using phase1_inv[OF i0] .
  obtain E1 where E1f: "finite E1" and E1s: "E1 \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}"
    and E1n: "ds_nxt (phase1 acyc_flow dfs_init) = card E1" using E1ex by blast
  have C2: "art_len (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        \<and> comproot_inv (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        \<and> cr_ext_inv (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init)) ! v}
                \<and> ds_nxt (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init)) = card E')"
    apply (rule fold_emit_crc2[where E=E1 and s="phase1 acyc_flow dfs_init"])
    subgoal by simp
    subgoal using p1inv by simp
    subgoal using p1inv by simp
    subgoal by (rule P1)
    subgoal by (rule CI1)
    subgoal by (rule CE1)
    subgoal by (rule E1f)
    subgoal by (rule E1s)
    subgoal by (rule E1n)
    done
  have "cr_ext_inv (phase2 acyc_flow (phase1 acyc_flow dfs_init))" using C2 by (simp add: phase2_def)
  thus ?thesis by (simp add: build_tree_def Let_def cr_ext_inv_def cr_ext_ok_def)
qed

text \<open>Obligation 9 (\<open>init_strict\<close>, strong feasibility): each non-root tree vertex's parent edge
      is strictly interior in the required direction.  Interior edges are free (both residual bounds
      hold); component-root edges are artificial, and their direction together with the tree-capacity
      (@{const art_tree_cap}) makes exactly the required bound strict.\<close>

lemma strict_interior:
  assumes vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" and prnt: "ds_prnt (build_tree acyc_flow) ! v < vcount"
  shows "if ds_dir (build_tree acyc_flow) ! v
         then ereal (h (flow_all ! (ds_par (build_tree acyc_flow) ! v)))
                < (if cap_all ! (ds_par (build_tree acyc_flow) ! v) = - 1 then \<infinity> else ereal (h (cap_all ! (ds_par (build_tree acyc_flow) ! v))))
         else 0 < flow_all ! (ds_par (build_tree acyc_flow) ! v)"
proof -
  have pe: "ds_par (build_tree acyc_flow) ! v < m" and free: "is_free acyc_flow (ds_par (build_tree acyc_flow) ! v)"
    using build_tree_par_edge[OF vlt vseen prnt] by simp_all
  have pos: "0 < acyc_flow ! (ds_par (build_tree acyc_flow) ! v)"
   and disj: "capacity_list ! (ds_par (build_tree acyc_flow) ! v) = - 1 \<or> acyc_flow ! (ds_par (build_tree acyc_flow) ! v) < capacity_list ! (ds_par (build_tree acyc_flow) ! v)"
    using free is_free_iff[OF acyc_flow_nonneg acyc_flow_le_cap pe] by simp_all
  have fa: "flow_all ! (ds_par (build_tree acyc_flow) ! v) = acyc_flow ! (ds_par (build_tree acyc_flow) ! v)" using flow_all_real[OF pe] .
  have ca: "cap_all ! (ds_par (build_tree acyc_flow) ! v) = capacity_list ! (ds_par (build_tree acyc_flow) ! v)" using cap_all_real[OF pe] .
  show ?thesis
  proof (cases "ds_dir (build_tree acyc_flow) ! v")
    case dir: True
    show ?thesis
    proof (cases "capacity_list ! (ds_par (build_tree acyc_flow) ! v) = - 1")
      case True thus ?thesis using dir fa ca by simp
    next
      case False
      have lt: "acyc_flow ! (ds_par (build_tree acyc_flow) ! v) < capacity_list ! (ds_par (build_tree acyc_flow) ! v)" using disj False by simp
      show ?thesis using dir fa ca False lt by simp
    qed
  next
    case False
    show ?thesis using False fa pos by simp
  qed
qed

lemma strict_comproot:
  assumes vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" and prnt: "ds_prnt (build_tree acyc_flow) ! v = vcount"
  shows "if ds_dir (build_tree acyc_flow) ! v
         then ereal (h (flow_all ! (ds_par (build_tree acyc_flow) ! v)))
                < (if cap_all ! (ds_par (build_tree acyc_flow) ! v) = - 1 then \<infinity> else ereal (h (cap_all ! (ds_par (build_tree acyc_flow) ! v))))
         else 0 < flow_all ! (ds_par (build_tree acyc_flow) ! v)"
proof -
  have ext: "cr_ext_ok (build_tree acyc_flow) v" using build_tree_crext vlt vseen prnt by (simp add: cr_ext_inv_def)
  have cok: "comproot_edge_ok (build_tree acyc_flow) v" using build_tree_comproot_inv vlt vseen prnt by (simp add: comproot_inv_def)
  have pm: "m \<le> ds_par (build_tree acyc_flow) ! v" and knxt: "ds_par (build_tree acyc_flow) ! v - m < ds_nxt (build_tree acyc_flow)"
    using cok by (simp_all add: comproot_edge_ok_def)
  have kK: "ds_par (build_tree acyc_flow) ! v - m < Kart" using knxt by (simp add: Kart_def)
  have mm: "m + (ds_par (build_tree acyc_flow) ! v - m) = ds_par (build_tree acyc_flow) ! v" using pm by simp
  have dirv: "ds_dir (build_tree acyc_flow) ! v = art_dir v" using ext by (simp add: cr_ext_ok_def)
  have flw: "flow_all ! (ds_par (build_tree acyc_flow) ! v) = art_flow v"
  proof -
    have "flow_all ! (ds_par (build_tree acyc_flow) ! v) = ds_aflw (build_tree acyc_flow) ! (ds_par (build_tree acyc_flow) ! v - m)"
      using flow_all_art[OF kK] mm by simp
    thus ?thesis using ext by (simp add: cr_ext_ok_def)
  qed
  have cpv: "cap_all ! (ds_par (build_tree acyc_flow) ! v) = art_tree_cap v"
  proof -
    have "cap_all ! (ds_par (build_tree acyc_flow) ! v) = ds_acap (build_tree acyc_flow) ! (ds_par (build_tree acyc_flow) ! v - m)"
      using cap_all_art[OF kK] mm by simp
    thus ?thesis using ext by (simp add: cr_ext_ok_def)
  qed
  have nn: "0 \<le> art_flow v" by (simp add: art_flow_def)
  show ?thesis
  proof (cases "art_dir v")
    case up: True
    have cc: "cap_all ! (ds_par (build_tree acyc_flow) ! v) = art_flow v + 1" using cpv up by (simp add: art_tree_cap_def)
    have ne: "cap_all ! (ds_par (build_tree acyc_flow) ! v) \<noteq> - 1" using cc nn by simp
    have lt: "ereal (h (flow_all ! (ds_par (build_tree acyc_flow) ! v))) < ereal (h (cap_all ! (ds_par (build_tree acyc_flow) ! v)))"
      using flw cc by simp
    have dtrue: "ds_dir (build_tree acyc_flow) ! v" using dirv up by simp
    show ?thesis using dtrue ne lt by simp
  next
    case down: False
    have gt: "0 < art_flow v" using down by (simp add: art_flow_def art_dir_def)
    have dfalse: "\<not> ds_dir (build_tree acyc_flow) ! v" using dirv down by simp
    show ?thesis using dfalse flw gt by simp
  qed
qed

lemma strict_core:
  assumes v: "v \<in> Vseen"
  shows "if ds_dir (build_tree acyc_flow) ! v
         then ereal (h (flow_all ! (ds_par (build_tree acyc_flow) ! v)))
                < (if cap_all ! (ds_par (build_tree acyc_flow) ! v) = - 1 then \<infinity> else ereal (h (cap_all ! (ds_par (build_tree acyc_flow) ! v))))
         else 0 < flow_all ! (ds_par (build_tree acyc_flow) ! v)"
proof -
  have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
  show ?thesis
  proof (cases "ds_prnt (build_tree acyc_flow) ! v < vcount")
    case True thus ?thesis using strict_interior[OF vlt vseen] by simp
  next
    case False
    have tsi: "tree_seen_inv (build_tree acyc_flow)" using build_tree_inv by (simp add: dfs_inv_def)
    have "ds_prnt (build_tree acyc_flow) ! v = vcount" using tsi vlt vseen False unfolding tree_seen_inv_def by blast
    thus ?thesis using strict_comproot[OF vlt vseen] by simp
  qed
qed

lemma NSinit_strict:
  "\<forall>v\<in>NS.\<V> - {vcount}.
      if nth (ds_dir (build_tree acyc_flow)) v
      then ereal (h (nth flow_all (nth (ds_par (build_tree acyc_flow)) v)))
             < (if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                then if cap_all ! nth (ds_par (build_tree acyc_flow)) v = - 1 then \<infinity>
                     else ereal (h (cap_all ! nth (ds_par (build_tree acyc_flow)) v))
                else \<infinity>)
      else 0 < nth flow_all (nth (ds_par (build_tree acyc_flow)) v)"
proof (rule ballI)
  fix v assume "v \<in> NS.\<V> - {vcount}"
  hence v: "v \<in> Vseen" using NS_V_minus_root by simp
  have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
  have emarc: "ds_par (build_tree acyc_flow) ! v < m + Kart" using par_lt_marc[OF vlt vseen] .
  show "if nth (ds_dir (build_tree acyc_flow)) v
        then ereal (h (nth flow_all (nth (ds_par (build_tree acyc_flow)) v)))
               < (if nth (ds_par (build_tree acyc_flow)) v < m + Kart
                  then if cap_all ! nth (ds_par (build_tree acyc_flow)) v = - 1 then \<infinity>
                       else ereal (h (cap_all ! nth (ds_par (build_tree acyc_flow)) v))
                  else \<infinity>)
        else 0 < nth flow_all (nth (ds_par (build_tree acyc_flow)) v)"
    unfolding if_P[OF emarc] by (rule strict_core[OF v])
qed


subsection \<open>Obligation 10 (init\_tree\_corr): the parent edges realise the abstract arborescence\<close>

text \<open>Every non-root tree vertex's parent edge realises its tree edge (endpoints \<open>{v, ds_prnt bt ! v}\<close>,
      correctly oriented by the direction flag), the finished parent-edge set has exactly the abstract
      arborescence @{term \<open>abstract_arb Sarb\<close>} as its endpoint-set family, and the walk to the root is the
      @{const follow} chain (@{thm follow_walk_root}).\<close>

lemma tc_endpoints_interior:
  assumes vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" and prnt: "ds_prnt (build_tree acyc_flow) ! v < vcount"
  shows "fst_all ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then v else ds_prnt (build_tree acyc_flow) ! v)
       \<and> snd_all ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then ds_prnt (build_tree acyc_flow) ! v else v)"
proof -
  from build_tree_par_edge[OF vlt vseen prnt]
  have pe: "ds_par (build_tree acyc_flow) ! v < m"
   and fl: "fst_list ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then v else ds_prnt (build_tree acyc_flow) ! v)"
   and sl: "snd_list ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then ds_prnt (build_tree acyc_flow) ! v else v)"
    by blast+
  have fa: "fst_all ! (ds_par (build_tree acyc_flow) ! v) = fst_list ! (ds_par (build_tree acyc_flow) ! v)" using fst_all_real[OF pe] .
  have sa: "snd_all ! (ds_par (build_tree acyc_flow) ! v) = snd_list ! (ds_par (build_tree acyc_flow) ! v)" using snd_all_real[OF pe] .
  show ?thesis using fa sa fl sl by simp
qed

lemma tc_endpoints_comproot:
  assumes vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" and prnt: "ds_prnt (build_tree acyc_flow) ! v = vcount"
  shows "fst_all ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then v else ds_prnt (build_tree acyc_flow) ! v)
       \<and> snd_all ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then ds_prnt (build_tree acyc_flow) ! v else v)"
proof -
  have ext: "cr_ext_ok (build_tree acyc_flow) v" using build_tree_crext vlt vseen prnt by (simp add: cr_ext_inv_def)
  have cok: "comproot_edge_ok (build_tree acyc_flow) v" using build_tree_comproot_inv vlt vseen prnt by (simp add: comproot_inv_def)
  have pm: "m \<le> ds_par (build_tree acyc_flow) ! v" and knxt: "ds_par (build_tree acyc_flow) ! v - m < ds_nxt (build_tree acyc_flow)"
    and af: "ds_afst (build_tree acyc_flow) ! (ds_par (build_tree acyc_flow) ! v - m) = (if art_dir v then v else vcount)"
    and as: "ds_asnd (build_tree acyc_flow) ! (ds_par (build_tree acyc_flow) ! v - m) = (if art_dir v then vcount else v)"
    using cok by (simp_all add: comproot_edge_ok_def)
  have kK: "ds_par (build_tree acyc_flow) ! v - m < Kart" using knxt by (simp add: Kart_def)
  have mm: "m + (ds_par (build_tree acyc_flow) ! v - m) = ds_par (build_tree acyc_flow) ! v" using pm by simp
  have dirv: "ds_dir (build_tree acyc_flow) ! v = art_dir v" using ext by (simp add: cr_ext_ok_def)
  have fa: "fst_all ! (ds_par (build_tree acyc_flow) ! v) = ds_afst (build_tree acyc_flow) ! (ds_par (build_tree acyc_flow) ! v - m)"
    using fst_all_art[OF kK] mm by simp
  have sa: "snd_all ! (ds_par (build_tree acyc_flow) ! v) = ds_asnd (build_tree acyc_flow) ! (ds_par (build_tree acyc_flow) ! v - m)"
    using snd_all_art[OF kK] mm by simp
  show ?thesis using fa sa af as dirv prnt by simp
qed

lemma tc_endpoints:
  assumes v: "v \<in> Vseen"
  shows "fst_all ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then v else ds_prnt (build_tree acyc_flow) ! v)
       \<and> snd_all ! (ds_par (build_tree acyc_flow) ! v) = (if ds_dir (build_tree acyc_flow) ! v then ds_prnt (build_tree acyc_flow) ! v else v)"
proof -
  have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
  show ?thesis
  proof (cases "ds_prnt (build_tree acyc_flow) ! v < vcount")
    case True thus ?thesis using tc_endpoints_interior[OF vlt vseen] by simp
  next
    case False
    have tsi: "tree_seen_inv (build_tree acyc_flow)" using build_tree_inv by (simp add: dfs_inv_def)
    have "ds_prnt (build_tree acyc_flow) ! v = vcount" using tsi vlt vseen False unfolding tree_seen_inv_def by blast
    thus ?thesis using tc_endpoints_comproot[OF vlt vseen] by simp
  qed
qed

lemma tc_orient: "v \<in> Vseen \<Longrightarrow>
  (if ds_dir (build_tree acyc_flow) ! v then fst_all ! (ds_par (build_tree acyc_flow) ! v) else snd_all ! (ds_par (build_tree acyc_flow) ! v)) = v"
  using tc_endpoints[of v] by (cases "ds_dir (build_tree acyc_flow) ! v") simp_all

lemma tc_other: "v \<in> Vseen \<Longrightarrow>
  (if ds_dir (build_tree acyc_flow) ! v then snd_all ! (ds_par (build_tree acyc_flow) ! v) else fst_all ! (ds_par (build_tree acyc_flow) ! v)) = ds_prnt (build_tree acyc_flow) ! v"
  using tc_endpoints[of v] by (cases "ds_dir (build_tree acyc_flow) ! v") simp_all

lemma tc_edge: "v \<in> Vseen \<Longrightarrow>
  {fst_all ! (ds_par (build_tree acyc_flow) ! v), snd_all ! (ds_par (build_tree acyc_flow) ! v)} = {v, ds_prnt (build_tree acyc_flow) ! v}"
  using tc_endpoints[of v] by (cases "ds_dir (build_tree acyc_flow) ! v") (auto simp: insert_commute)

lemma arb_edge_set: "abstract_arb Sarb = (\<lambda>v. {v, ds_prnt (build_tree acyc_flow) ! v}) ` Vseen"
proof -
  have "abstract_arb Sarb = {{x, y} |x y. Sprnt x = Some y}" by (simp add: abstract_arb_def Sarb_sel)
  also have "\<dots> = (\<lambda>v. {v, ds_prnt (build_tree acyc_flow) ! v}) ` Vseen"
    by (auto simp: Sprnt_def split: if_splits)
  finally show ?thesis .
qed

lemma tc_elt:
  assumes v: "v \<in> Vseen"
  shows "(\<lambda>e. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
                if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))})
           (nth (ds_par (build_tree acyc_flow)) v) = {v, ds_prnt (build_tree acyc_flow) ! v}"
proof -
  have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
  have emarc: "ds_par (build_tree acyc_flow) ! v < m + Kart" using par_lt_marc[OF vlt vseen] .
  show ?thesis by (simp only: if_P[OF emarc] tc_edge[OF v])
qed

lemma tc_image:
  "(\<lambda>e. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
           if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))})
     ` (nth (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})) = abstract_arb Sarb"
proof -
  let ?f = "\<lambda>e. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
                  if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))}"
  have "?f ` (nth (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}))
      = (\<lambda>v. ?f (nth (ds_par (build_tree acyc_flow)) v)) ` Vseen"
    by (simp only: NS_V_minus_root image_image)
  also have "\<dots> = (\<lambda>v. {v, ds_prnt (build_tree acyc_flow) ! v}) ` Vseen"
    by (rule image_cong[OF refl tc_elt])
  also have "\<dots> = abstract_arb Sarb" by (rule arb_edge_set[symmetric])
  finally show ?thesis .
qed

lemma tc_walk:
  assumes vVs: "v \<in> Vseen"
  shows "\<exists>q. distinct (v # ds_prnt (build_tree acyc_flow) ! v # q)
             \<and> walk_betw (abstract_arb Sarb) v (v # ds_prnt (build_tree acyc_flow) ! v # q) vcount"
proof -
  have vVarb: "v \<in> Varb" using vVs by (simp add: Varb_def)
  have sprntv: "Sprnt v = Some (ds_prnt (build_tree acyc_flow) ! v)" using vVs by (simp add: Sprnt_def)
  have f1: "follow Sprnt v = v # follow Sprnt (ds_prnt (build_tree acyc_flow) ! v)"
    using follow_ps_simps[OF parent_spec_Sprnt] sprntv by simp
  have f2: "follow Sprnt (ds_prnt (build_tree acyc_flow) ! v) = ds_prnt (build_tree acyc_flow) ! v # tl (follow Sprnt (ds_prnt (build_tree acyc_flow) ! v))"
    using follow_ps_simps[OF parent_spec_Sprnt, of "ds_prnt (build_tree acyc_flow) ! v"] by (auto split: option.splits)
  define q where "q = tl (follow Sprnt (ds_prnt (build_tree acyc_flow) ! v))"
  have flist: "follow Sprnt v = v # ds_prnt (build_tree acyc_flow) ! v # q" using f1 f2 q_def by simp
  have dist: "distinct (follow Sprnt v)" by (rule follow_distinct_ps[OF parent_spec_Sprnt])
  have walk: "walk_betw (abstract_arb Sarb) v (follow Sprnt v) vcount"
    using follow_walk_root[OF arb_invar_Sarb vVarb] by (simp add: Sarb_sel)
  from dist walk have "distinct (v # ds_prnt (build_tree acyc_flow) ! v # q)
        \<and> walk_betw (abstract_arb Sarb) v (v # ds_prnt (build_tree acyc_flow) ! v # q) vcount"
    using flist by simp
  thus ?thesis by blast
qed

lemma tc_orient_listarr:
  assumes v: "v \<in> Vseen"
  shows "if nth (ds_dir (build_tree acyc_flow)) v
          then (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v
          else (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v"
proof -
  have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
  have emarc: "ds_par (build_tree acyc_flow) ! v < m + Kart" using par_lt_marc[OF vlt vseen] .
  have red: "(if nth (ds_dir (build_tree acyc_flow)) v
          then (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v
          else (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v)
       = (if ds_dir (build_tree acyc_flow) ! v then fst_all ! (ds_par (build_tree acyc_flow) ! v) = v else snd_all ! (ds_par (build_tree acyc_flow) ! v) = v)"
    by (simp only: if_P[OF emarc])
  show ?thesis unfolding red using tc_orient[OF v] by (cases "ds_dir (build_tree acyc_flow) ! v") simp_all
qed

lemma tc_walk_listarr:
  assumes v: "v \<in> Vseen"
  shows "\<exists>q. distinct (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q)
             \<and> walk_betw (abstract_arb Sarb) v (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q) vcount"
proof -
  have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
  have emarc: "ds_par (build_tree acyc_flow) ! v < m + Kart" using par_lt_marc[OF vlt vseen] .
  have Xval: "(if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = ds_prnt (build_tree acyc_flow) ! v"
    by (simp only: if_P[OF emarc]) (rule tc_other[OF v])
  show ?thesis unfolding Xval by (rule tc_walk[OF v])
qed

lemma NSinit_tree_corr:
  "(\<forall>v\<in>NS.\<V> - {vcount}. nth (ds_par (build_tree acyc_flow)) v \<in> {0..<m + Kart}
      \<and> (if nth (ds_dir (build_tree acyc_flow)) v
          then (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v
          else (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v)
      \<and> (\<exists>q. distinct (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q)
             \<and> walk_betw (abstract_arb Sarb) v (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q) vcount))
   \<and> (\<lambda>e. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))), if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))}) ` nth (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}) = abstract_arb Sarb"
proof (rule conjI)
  show "\<forall>v\<in>NS.\<V> - {vcount}. nth (ds_par (build_tree acyc_flow)) v \<in> {0..<m + Kart}
      \<and> (if nth (ds_dir (build_tree acyc_flow)) v
          then (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v
          else (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v)
      \<and> (\<exists>q. distinct (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q)
             \<and> walk_betw (abstract_arb Sarb) v (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q) vcount)"
  proof (rule ballI)
    fix v assume "v \<in> NS.\<V> - {vcount}"
    hence v: "v \<in> Vseen" using NS_V_minus_root by simp
    have vlt: "v < vcount" and vseen: "ds_seen (build_tree acyc_flow) ! v" using v by (auto simp: Vseen_def)
    have emarc: "ds_par (build_tree acyc_flow) ! v < m + Kart" using par_lt_marc[OF vlt vseen] .
    show "nth (ds_par (build_tree acyc_flow)) v \<in> {0..<m + Kart}
      \<and> (if nth (ds_dir (build_tree acyc_flow)) v
          then (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v
          else (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v)
      \<and> (\<exists>q. distinct (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q)
             \<and> walk_betw (abstract_arb Sarb) v (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q) vcount)"
    proof (intro conjI)
      show "nth (ds_par (build_tree acyc_flow)) v \<in> {0..<m + Kart}"
        using emarc by simp
    next
      show "if nth (ds_dir (build_tree acyc_flow)) v
          then (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v
          else (if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) = v"
        by (rule tc_orient_listarr[OF v])
    next
      show "\<exists>q. distinct (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q)
             \<and> walk_betw (abstract_arb Sarb) v (v # (if nth (ds_dir (build_tree acyc_flow)) v then if nth (ds_par (build_tree acyc_flow)) v < m + Kart then snd_all ! nth (ds_par (build_tree acyc_flow)) v else snd (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart))) else if nth (ds_par (build_tree acyc_flow)) v < m + Kart then fst_all ! nth (ds_par (build_tree acyc_flow)) v else fst (prod_decode (nth (ds_par (build_tree acyc_flow)) v - (m + Kart)))) # q) vcount"
        by (rule tc_walk_listarr[OF v])
    qed
  qed
next
  show "(\<lambda>e. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))), if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))}) ` nth (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}) = abstract_arb Sarb"
    by (rule tc_image)
qed


section \<open>The @{locale network_simplex_init} interpretation for the constructed initial basis\<close>

text \<open>Extending @{term NS} with the concrete starting basis produced by @{const build_tree}: the flow
      @{const flow_all}, the potentials @{term \<open>ds_pot (build_tree acyc_flow)\<close>}, the arborescence @{term Sarb}, the
      parent/direction maps @{term \<open>ds_par (build_tree acyc_flow)\<close>} / @{term \<open>ds_dir (build_tree acyc_flow)\<close>}, the edge-state
      array @{const state_all} and the selector seed @{const init_sel}. Because @{term NS} already
      discharges every \<open>network_simplex_spec\<close> axiom, \<open>unfold_locales\<close> leaves only the 10
      @{locale network_simplex_init} obligations. Seven are now proved --- the trivial store invariant,
      the tree invariant @{thm arb_invar_Sarb}, the selector seed (@{thm NSinit_sel_invar}), the
      flow/edge-partition fit (@{thm NSinit_flow_fits}), the potential fit (@{thm NSinit_pot_fits}),
      strong feasibility (@{thm NSinit_strict}) and the tree correspondence (@{thm NSinit_tree_corr}).
      The remaining three (the store validity @{term \<open>NS.pot_valid\<close>}, the \<open>b\<close>-flow and the
      spanning-tree partition) each need extra carried invariants and are left as \<^emph>\<open>sorry\<close> for now.\<close>

subsection \<open>Validity of the initial potentials (obligation 2 / init\_pot\_valid)\<close>

text \<open>The built potential is a valid network-simplex potential: it satisfies the store-length
      invariant and, at every vertex, the good-potential certificate good\_pot\_val\_c together with
      the descriptor bound pv\_invar. The certificate is obtained from a closed form of the
      potential as a signed sum of tree-path edge costs (pot\_repr), proved by well-founded
      induction along the parent relation; distinctness of the path edges (par\_inj) keeps the
      cost sums honest, and exactly one artificial (root-incident) edge sits at the top of each
      path, which is what bounds the root-incident count by one.\<close>

lemma par_inj:
  assumes u: "u \<in> Vseen" and u': "u' \<in> Vseen"
    and eq: "ds_par (build_tree acyc_flow) ! u = ds_par (build_tree acyc_flow) ! u'"
  shows "u = u'"
proof -
  let ?bt = "build_tree acyc_flow"
  let ?p = "\<lambda>x. ds_prnt ?bt ! x"
  have ult: "u < vcount" and useen: "ds_seen ?bt ! u" using u by (auto simp: Vseen_def)
  have u'lt: "u' < vcount" and u'seen: "ds_seen ?bt ! u'" using u' by (auto simp: Vseen_def)
  have stepu: "(u, ?p u) \<in> pstep ?bt" using ult useen by (auto simp: pstep_def)
  have stepu': "(u', ?p u') \<in> pstep ?bt" using u'lt u'seen by (auto simp: pstep_def)
  have unp: "u \<noteq> ?p u"
  proof
    assume "u = ?p u"
    hence "(u, u) \<in> (pstep ?bt)\<^sup>+" using stepu by (auto intro: r_into_trancl)
    thus False using pstep_acyclic by (simp add: acyclic_def)
  qed
  have u'np: "u' \<noteq> ?p u'"
  proof
    assume "u' = ?p u'"
    hence "(u', u') \<in> (pstep ?bt)\<^sup>+" using stepu' by (auto intro: r_into_trancl)
    thus False using pstep_acyclic by (simp add: acyclic_def)
  qed
  have setu: "{fst_all ! (ds_par ?bt ! u), snd_all ! (ds_par ?bt ! u)} = {u, ?p u}"
    using tc_endpoints[OF u] by (cases "ds_dir ?bt ! u") auto
  have setu': "{fst_all ! (ds_par ?bt ! u'), snd_all ! (ds_par ?bt ! u')} = {u', ?p u'}"
    using tc_endpoints[OF u'] by (cases "ds_dir ?bt ! u'") auto
  have "{u, ?p u} = {u', ?p u'}" using setu setu' eq by simp
  hence "(u = u' \<and> ?p u = ?p u') \<or> (u = ?p u' \<and> ?p u = u')"
    using unp u'np by (auto simp: doubleton_eq_iff)
  thus ?thesis
  proof
    assume "u = u' \<and> ?p u = ?p u'" thus ?thesis by simp
  next
    assume A: "u = ?p u' \<and> ?p u = u'"
    have "(u, u') \<in> pstep ?bt" using stepu A by argo
    moreover have "(u', u) \<in> pstep ?bt" using stepu' A by argo
    ultimately have "(u, u) \<in> (pstep ?bt)\<^sup>+" by (meson trancl.simps)
    thus ?thesis using pstep_acyclic by (simp add: acyclic_def)
  qed
qed

lemma PS_finite: "finite (pstep (build_tree acyc_flow))"
proof -
  have "pstep (build_tree acyc_flow) = (\<lambda>x. (x, ds_prnt (build_tree acyc_flow) ! x)) ` Vseen"
    by (auto simp: pstep_def Vseen_def)
  thus ?thesis using Vseen_finite by simp
qed

lemma wf_PS_conv: "wf ((pstep (build_tree acyc_flow))\<inverse>)"
  using PS_finite pstep_acyclic
  by (simp add: finite_acyclic_wf acyclic_converse finite_converse)

lemma anc_step:
  assumes w: "w \<in> Vseen"
  shows "{u. (w,u) \<in> (pstep (build_tree acyc_flow))\<^sup>*} = insert w {u. (ds_prnt (build_tree acyc_flow) ! w, u) \<in> (pstep (build_tree acyc_flow))\<^sup>*}"
    (is "?L = insert w ?R")
proof
  have wlt: "w < vcount" and wseen: "ds_seen (build_tree acyc_flow) ! w" using w by (auto simp: Vseen_def)
  have step: "(w, ds_prnt (build_tree acyc_flow) ! w) \<in> pstep (build_tree acyc_flow)"
    using wlt wseen by (auto simp: pstep_def)
  have sv: "\<And>y. (w, y) \<in> pstep (build_tree acyc_flow) \<Longrightarrow> y = ds_prnt (build_tree acyc_flow) ! w"
    using wlt wseen by (auto simp: pstep_def)
  show "?L \<subseteq> insert w ?R"
  proof
    fix u assume "u \<in> ?L"
    hence "(w,u) \<in> (pstep (build_tree acyc_flow))\<^sup>*" by simp
    thus "u \<in> insert w ?R"
      by (cases rule: converse_rtranclE) (auto dest: sv)
  qed
next
  have wlt: "w < vcount" and wseen: "ds_seen (build_tree acyc_flow) ! w" using w by (auto simp: Vseen_def)
  have step: "(w, ds_prnt (build_tree acyc_flow) ! w) \<in> pstep (build_tree acyc_flow)"
    using wlt wseen by (auto simp: pstep_def)
  show "insert w ?R \<subseteq> ?L"
    using step by (auto intro: converse_rtrancl_into_rtrancl)
qed

lemma w_notin_anc_parent:
  assumes w: "w \<in> Vseen"
  shows "w \<notin> {u. (ds_prnt (build_tree acyc_flow) ! w, u) \<in> (pstep (build_tree acyc_flow))\<^sup>*}"
proof
  assume "w \<in> {u. (ds_prnt (build_tree acyc_flow) ! w, u) \<in> (pstep (build_tree acyc_flow))\<^sup>*}"
  hence "(ds_prnt (build_tree acyc_flow) ! w, w) \<in> (pstep (build_tree acyc_flow))\<^sup>*" by simp
  moreover have "(w, ds_prnt (build_tree acyc_flow) ! w) \<in> pstep (build_tree acyc_flow)"
    using w by (auto simp: pstep_def Vseen_def)
  ultimately have "(w, w) \<in> (pstep (build_tree acyc_flow))\<^sup>+" by (meson rtrancl_into_trancl2)
  thus False using pstep_acyclic by (simp add: acyclic_def)
qed

lemma anc_sub:
  assumes "(w0, u) \<in> (pstep (build_tree acyc_flow))\<^sup>*" and "w0 \<in> insert vcount Vseen"
  shows "u \<in> insert vcount Vseen"
  using assms
proof (induction rule: rtrancl_induct)
  case base thus ?case by simp
next
  case (step y z)
  from step(2) have ylt: "y < vcount" and yseen: "ds_seen (build_tree acyc_flow) ! y"
    and zp: "z = ds_prnt (build_tree acyc_flow) ! y" by (auto simp: pstep_def)
  show ?case using build_tree_parent_in_seen[OF ylt yseen] zp by (auto simp: Vseen_def)
qed

lemma pot_repr:
  assumes "w \<in> insert vcount Vseen"
  shows "\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> A \<inter> D = {}
      \<and> A \<union> D \<subseteq> (!) (ds_par (build_tree acyc_flow)) ` ({u. (w,u) \<in> (pstep (build_tree acyc_flow))\<^sup>*} - {vcount})
      \<and> card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1
      \<and> pval_abstract bigM (ds_pot (build_tree acyc_flow) ! w) = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)
      \<and> snd (ds_pot (build_tree acyc_flow) ! w) = (\<Sum>e\<in>A\<inter>{0..<m}. cost_list ! e) - (\<Sum>e\<in>D\<inter>{0..<m}. cost_list ! e)"
  using assms
proof (induction w rule: wf_induct_rule[OF wf_PS_conv])
  case (1 w)
  note [simp del] = NS.fst_exec_eq NS.snd_exec_eq
  note IH = "1.IH" and prem = "1.prems"
  let ?bt = "build_tree acyc_flow"
  let ?PS = "pstep ?bt"
  let ?anc = "\<lambda>x. {u. (x,u) \<in> ?PS\<^sup>*}"
  show ?case
  proof (cases "w = vcount")
    case True
    have novc: "\<And>y. (vcount, y) \<notin> ?PS" by (auto simp: pstep_def)
    have "?anc vcount \<subseteq> {vcount}"
    proof
      fix u assume "u \<in> ?anc vcount"
      hence "(vcount, u) \<in> ?PS\<^sup>*" by simp
      thus "u \<in> {vcount}"
        by (cases rule: converse_rtranclE) (auto simp: novc)
    qed
    hence "?anc vcount = {vcount}" by auto
    hence ancv: "?anc w - {vcount} = {}" using True by simp
    have "ds_pot ?bt ! w = pval_zero" using True by (simp add: build_tree_root_pot)
    hence "pval_abstract bigM (ds_pot ?bt ! w) = 0" and "snd (ds_pot ?bt ! w) = 0"
      by (simp_all add: pval_abstract_def pval_zero_def)
    thus ?thesis using ancv by (intro exI[of _ "{}"] exI[of _ "{}"]) auto
  next
    case False
    hence wV: "w \<in> Vseen" using prem by simp
    have wlt: "w < vcount" and wseen: "ds_seen ?bt ! w" using wV by (auto simp: Vseen_def)
    define p where "p = ds_prnt ?bt ! w"
    define e where "e = ds_par ?bt ! w"
    have step: "(w, p) \<in> ?PS" using wlt wseen by (auto simp: pstep_def p_def)
    have stepc: "(p, w) \<in> ?PS\<inverse>" using step by simp
    have ancw: "?anc w - {vcount} = insert w (?anc p) - {vcount}"
      using anc_step[OF wV] by (simp add: p_def)
    have wneP: "w \<notin> ?anc p" using w_notin_anc_parent[OF wV] by (simp add: p_def)
    have eendpts: "{fst_all ! e, snd_all ! e} = {w, p}"
      using tc_endpoints[OF wV] by (cases "ds_dir ?bt ! w") (auto simp: e_def p_def)
    show ?thesis
    proof (cases "p = vcount")
      case True  \<comment> \<open>root child: artificial edge, seed potential\<close>
      have pV: "p \<in> insert vcount Vseen" using True by simp
      have ok: "comproot_edge_ok ?bt w"
        using build_tree_comproot_inv wlt wseen True by (simp add: comproot_inv_def p_def)
      have em: "m \<le> e" and pot_seed: "ds_pot ?bt ! w = (if art_dir w then pval_negM else pval_M)"
        using ok by (auto simp: comproot_edge_ok_def e_def)
      have knxt: "Kart = ds_nxt (build_tree acyc_flow)" by (simp add: Kart_def)
      have "e - m < ds_nxt (build_tree acyc_flow)" using ok by (simp add: comproot_edge_ok_def e_def)
      hence elt: "e < m + Kart" using em knxt by linarith
      have coste: "cost_all ! e = bigM" using em elt by (simp add: cost_all_art')
      have "vcount \<in> {fst_all ! e, snd_all ! e}" using eendpts True by simp
      hence rootinc: "fst_all ! e = vcount \<or> snd_all ! e = vcount" by auto
      have wanc: "w \<in> ?anc w - {vcount}"
      proof -
        have "(w, w) \<in> (pstep ?bt)\<^sup>*" by simp
        thus ?thesis using wlt by simp
      qed
      have esub: "{e} \<subseteq> (!) (ds_par ?bt) ` (?anc w - {vcount})"
      proof -
        have "e = (!) (ds_par ?bt) w" by (simp add: e_def)
        thus ?thesis using wanc by blast
      qed
      have ele: "e \<in> {0..<m+Kart}" using em elt by simp
      have enotorig: "e \<notin> {0..<m}" using em by simp
      show ?thesis
      proof (cases "art_dir w")
        case True
        have pa: "pval_abstract bigM (ds_pot ?bt ! w) = - bigM"
          using pot_seed True by (simp add: pval_abstract_def pval_negM_def)
        have sn: "snd (ds_pot ?bt ! w) = 0" using pot_seed True by (simp add: pval_negM_def)
        show ?thesis
        proof (rule exI[of _ "{}"], rule exI[of _ "{e}"], intro conjI)
          show "({}::nat set) \<subseteq> {0..<m+Kart}" by simp
          show "{e} \<subseteq> {0..<m+Kart}" using ele by simp
          show "({}::nat set) \<inter> {e} = {}" by simp
          show "{} \<union> {e} \<subseteq> (!) (ds_par ?bt) ` (?anc w - {vcount})" using esub by simp
          have "{ee \<in> {} \<union> {e}. fst_all ! ee = vcount \<or> snd_all ! ee = vcount} = {e}"
            using rootinc by auto
          thus "card {ee \<in> {} \<union> {e}. fst_all ! ee = vcount \<or> snd_all ! ee = vcount} \<le> 1" by simp
          show "pval_abstract bigM (ds_pot ?bt ! w) = (\<Sum>ee\<in>{}. cost_all ! ee) - (\<Sum>ee\<in>{e}. cost_all ! ee)"
            using pa coste by simp
          show "snd (ds_pot ?bt ! w) = (\<Sum>ee\<in>{}\<inter>{0..<m}. cost_list ! ee) - (\<Sum>ee\<in>{e}\<inter>{0..<m}. cost_list ! ee)"
            using sn enotorig by simp
        qed
      next
        case False
        have pa: "pval_abstract bigM (ds_pot ?bt ! w) = bigM"
          using pot_seed False by (simp add: pval_abstract_def pval_M_def)
        have sn: "snd (ds_pot ?bt ! w) = 0" using pot_seed False by (simp add: pval_M_def)
        show ?thesis
        proof (rule exI[of _ "{e}"], rule exI[of _ "{}"], intro conjI)
          show "{e} \<subseteq> {0..<m+Kart}" using ele by simp
          show "({}::nat set) \<subseteq> {0..<m+Kart}" by simp
          show "{e} \<inter> ({}::nat set) = {}" by simp
          show "{e} \<union> {} \<subseteq> (!) (ds_par ?bt) ` (?anc w - {vcount})" using esub by simp
          have "{ee \<in> {e} \<union> {}. fst_all ! ee = vcount \<or> snd_all ! ee = vcount} = {e}"
            using rootinc by auto
          thus "card {ee \<in> {e} \<union> {}. fst_all ! ee = vcount \<or> snd_all ! ee = vcount} \<le> 1" by simp
          show "pval_abstract bigM (ds_pot ?bt ! w) = (\<Sum>ee\<in>{e}. cost_all ! ee) - (\<Sum>ee\<in>{}. cost_all ! ee)"
            using pa coste by simp
          show "snd (ds_pot ?bt ! w) = (\<Sum>ee\<in>{e}\<inter>{0..<m}. cost_list ! ee) - (\<Sum>ee\<in>{}\<inter>{0..<m}. cost_list ! ee)"
            using sn enotorig by simp
        qed
      qed
    next
      case False  \<comment> \<open>interior: real parent edge, potential recursion\<close>
      have plt: "p < vcount" and pseen: "ds_seen ?bt ! p"
        using build_tree_parent_in_seen[OF wlt wseen] False by (auto simp: p_def)
      have pV: "p \<in> insert vcount Vseen" using plt pseen by (simp add: Vseen_def)
      have pd: "ds_prnt ?bt ! w < vcount" using plt by (simp add: p_def)
      have IH: "\<exists>A D. A \<subseteq> {0..<m+Kart} \<and> D \<subseteq> {0..<m+Kart} \<and> A \<inter> D = {}
          \<and> A \<union> D \<subseteq> (!) (ds_par ?bt) ` (?anc p - {vcount})
          \<and> card {ee \<in> A \<union> D. fst_all ! ee = vcount \<or> snd_all ! ee = vcount} \<le> 1
          \<and> pval_abstract bigM (ds_pot ?bt ! p) = (\<Sum>ee\<in>A. cost_all ! ee) - (\<Sum>ee\<in>D. cost_all ! ee)
          \<and> snd (ds_pot ?bt ! p) = (\<Sum>ee\<in>A\<inter>{0..<m}. cost_list ! ee) - (\<Sum>ee\<in>D\<inter>{0..<m}. cost_list ! ee)"
        using IH[OF stepc pV] .
      then obtain A D where AD: "A \<subseteq> {0..<m+Kart}" "D \<subseteq> {0..<m+Kart}" "A \<inter> D = {}"
          "A \<union> D \<subseteq> (!) (ds_par ?bt) ` (?anc p - {vcount})"
          "card {ee \<in> A \<union> D. fst_all ! ee = vcount \<or> snd_all ! ee = vcount} \<le> 1"
          "pval_abstract bigM (ds_pot ?bt ! p) = (\<Sum>ee\<in>A. cost_all ! ee) - (\<Sum>ee\<in>D. cost_all ! ee)"
          "snd (ds_pot ?bt ! p) = (\<Sum>ee\<in>A\<inter>{0..<m}. cost_list ! ee) - (\<Sum>ee\<in>D\<inter>{0..<m}. cost_list ! ee)" by (elim exE conjE) (rule that; assumption)
      have par_e: "e < m" using build_tree_par_edge[OF wlt wseen pd] by (simp add: e_def)
      have coste: "cost_all ! e = h (cost_list ! e)" using par_e by (simp add: cost_all_real)
      have pot_rec: "ds_pot ?bt ! w = pval_plus (ds_pot ?bt ! p) (M_0, if p = fst_list ! e then cost_list ! e else - cost_list ! e)"
        using build_tree_pot[OF wlt wseen pd] by (simp add: e_def p_def)
      define s where "s = (if p = fst_list ! e then cost_list ! e else - cost_list ! e)"
      have absw: "pval_abstract bigM (ds_pot ?bt ! w) = pval_abstract bigM (ds_pot ?bt ! p) + h s"
        unfolding s_def using pot_rec by (simp add: pval_plus_M0)
      have sndw: "snd (ds_pot ?bt ! w) = snd (ds_pot ?bt ! p) + s"
        unfolding s_def using pot_rec by (simp add: pval_plus_def)
      have efresh: "e \<notin> A \<union> D"
      proof
        assume "e \<in> A \<union> D"
        then obtain u where uanc: "u \<in> ?anc p - {vcount}" and eu: "e = ds_par ?bt ! u" using AD(4) by auto
        have "u \<in> insert vcount Vseen" using anc_sub[of p u] uanc pV by simp
        hence uV: "u \<in> Vseen" using uanc by simp
        have "w = u" using par_inj[OF wV uV] eu by (simp add: e_def)
        thus False using uanc wneP by simp
      qed
      have enotroot: "fst_all ! e \<noteq> vcount \<and> snd_all ! e \<noteq> vcount"
        using eendpts wlt plt by auto
      have ele: "e \<in> {0..<m}" using par_e by simp
      have wanc: "w \<in> ?anc w - {vcount}"
      proof -
        have "(w, w) \<in> (pstep ?bt)\<^sup>*" by simp
        thus ?thesis using wlt by simp
      qed
      have ancpw: "?anc p - {vcount} \<subseteq> ?anc w - {vcount}"
        unfolding ancw by (rule Diff_mono[OF subset_insertI order_refl])
      have esub: "insert e (A \<union> D) \<subseteq> (!) (ds_par ?bt) ` (?anc w - {vcount})"
      proof -
        have "e \<in> (!) (ds_par ?bt) ` (?anc w - {vcount})" using imageI[OF wanc] by (simp add: e_def)
        moreover have "A \<union> D \<subseteq> (!) (ds_par ?bt) ` (?anc w - {vcount})"
          using AD(4) ancpw by blast
        ultimately show ?thesis by simp
      qed
      show ?thesis
      proof (cases "s = cost_list ! e")
        case True  \<comment> \<open>edge oriented up: goes into A\<close>
        let ?A = "insert e A" let ?D = D
        have g6: "pval_abstract bigM (ds_pot ?bt ! w) = (\<Sum>ee\<in>?A. cost_all ! ee) - (\<Sum>ee\<in>?D. cost_all ! ee)"
          using absw AD(6) True coste efresh AD(1) by (simp add: sum.insert_if finite_subset)
        have g7: "snd (ds_pot ?bt ! w) = (\<Sum>ee\<in>?A\<inter>{0..<m}. cost_list ! ee) - (\<Sum>ee\<in>?D\<inter>{0..<m}. cost_list ! ee)"
          using sndw AD(7) True efresh ele by (simp add: sum.insert_if Int_insert_left)
        have g5: "card {ee \<in> ?A \<union> ?D. fst_all ! ee = vcount \<or> snd_all ! ee = vcount} \<le> 1"
        proof -
          have "{ee \<in> ?A \<union> ?D. fst_all ! ee = vcount \<or> snd_all ! ee = vcount}
                = {ee \<in> A \<union> D. fst_all ! ee = vcount \<or> snd_all ! ee = vcount}"
            using enotroot by auto
          thus ?thesis using AD(5) by simp
        qed
        show ?thesis
        proof (rule exI[of _ ?A], rule exI[of _ ?D], intro conjI)
          show "?A \<subseteq> {0..<m+Kart}" using AD(1) ele by auto
          show "?D \<subseteq> {0..<m+Kart}" using AD(2) by simp
          show "?A \<inter> ?D = {}" using AD(3) efresh by auto
          show "?A \<union> ?D \<subseteq> (!) (ds_par ?bt) ` (?anc w - {vcount})" using esub by simp
          show "card {ee \<in> ?A \<union> ?D. fst_all ! ee = vcount \<or> snd_all ! ee = vcount} \<le> 1" by (rule g5)
          show "pval_abstract bigM (ds_pot ?bt ! w) = (\<Sum>ee\<in>?A. cost_all ! ee) - (\<Sum>ee\<in>?D. cost_all ! ee)" by (rule g6)
          show "snd (ds_pot ?bt ! w) = (\<Sum>ee\<in>?A\<inter>{0..<m}. cost_list ! ee) - (\<Sum>ee\<in>?D\<inter>{0..<m}. cost_list ! ee)" by (rule g7)
        qed
      next
        case False
        have sD: "s = - cost_list ! e" using \<open>s \<noteq> cost_list ! e\<close> by (simp add: s_def split: if_splits)
        let ?A = A let ?D = "insert e D"
        have g6: "pval_abstract bigM (ds_pot ?bt ! w) = (\<Sum>ee\<in>?A. cost_all ! ee) - (\<Sum>ee\<in>?D. cost_all ! ee)"
          using absw AD(6) sD coste efresh AD(2) by (simp add: sum.insert_if finite_subset)
        have g7: "snd (ds_pot ?bt ! w) = (\<Sum>ee\<in>?A\<inter>{0..<m}. cost_list ! ee) - (\<Sum>ee\<in>?D\<inter>{0..<m}. cost_list ! ee)"
          using sndw AD(7) sD efresh ele by (simp add: sum.insert_if Int_insert_left)
        have g5: "card {ee \<in> ?A \<union> ?D. fst_all ! ee = vcount \<or> snd_all ! ee = vcount} \<le> 1"
        proof -
          have "{ee \<in> ?A \<union> ?D. fst_all ! ee = vcount \<or> snd_all ! ee = vcount}
                = {ee \<in> A \<union> D. fst_all ! ee = vcount \<or> snd_all ! ee = vcount}"
            using enotroot by auto
          thus ?thesis using AD(5) by simp
        qed
        show ?thesis
        proof (rule exI[of _ ?A], rule exI[of _ ?D], intro conjI)
          show "?A \<subseteq> {0..<m+Kart}" using AD(1) by simp
          show "?D \<subseteq> {0..<m+Kart}" using AD(2) ele by auto
          show "?A \<inter> ?D = {}" using AD(3) efresh by auto
          show "?A \<union> ?D \<subseteq> (!) (ds_par ?bt) ` (?anc w - {vcount})" using esub by simp
          show "card {ee \<in> ?A \<union> ?D. fst_all ! ee = vcount \<or> snd_all ! ee = vcount} \<le> 1" by (rule g5)
          show "pval_abstract bigM (ds_pot ?bt ! w) = (\<Sum>ee\<in>?A. cost_all ! ee) - (\<Sum>ee\<in>?D. cost_all ! ee)" by (rule g6)
          show "snd (ds_pot ?bt ! w) = (\<Sum>ee\<in>?A\<inter>{0..<m}. cost_list ! ee) - (\<Sum>ee\<in>?D\<inter>{0..<m}. cost_list ! ee)" by (rule g7)
        qed
      qed
    qed
  qed
qed

lemma pot_value_ok:
  assumes "w \<in> insert vcount Vseen"
  shows "good_pot_val_c (ds_pot (build_tree acyc_flow) ! w) \<and> pv_invar (ds_pot (build_tree acyc_flow) ! w)"
proof -
  obtain A D where AD: "A \<subseteq> {0..<m+Kart}" "D \<subseteq> {0..<m+Kart}" "A \<inter> D = {}"
      "A \<union> D \<subseteq> (!) (ds_par (build_tree acyc_flow)) ` ({u. (w,u) \<in> (pstep (build_tree acyc_flow))\<^sup>*} - {vcount})"
      "card {e \<in> A \<union> D. fst_all ! e = vcount \<or> snd_all ! e = vcount} \<le> 1"
      "pval_abstract bigM (ds_pot (build_tree acyc_flow) ! w) = (\<Sum>e\<in>A. cost_all ! e) - (\<Sum>e\<in>D. cost_all ! e)"
      "snd (ds_pot (build_tree acyc_flow) ! w) = (\<Sum>e\<in>A\<inter>{0..<m}. cost_list ! e) - (\<Sum>e\<in>D\<inter>{0..<m}. cost_list ! e)"
    using pot_repr[OF assms] by (elim exE conjE) (rule that; assumption)
  have gp: "good_pot_val_c (ds_pot (build_tree acyc_flow) ! w)"
    unfolding good_pot_val_c_def using AD(1,2,5,6) by (intro exI[of _ A] exI[of _ D] conjI)
  have "\<bar>(\<Sum>e\<in>A\<inter>{0..<m}. cost_list ! e) - (\<Sum>e\<in>D\<inter>{0..<m}. cost_list ! e)\<bar>
        \<le> \<bar>(\<Sum>e\<in>A\<inter>{0..<m}. cost_list ! e)\<bar> + \<bar>(\<Sum>e\<in>D\<inter>{0..<m}. cost_list ! e)\<bar>" by simp
  also have "\<dots> \<le> (\<Sum>e\<in>A\<inter>{0..<m}. \<bar>cost_list ! e\<bar>) + (\<Sum>e\<in>D\<inter>{0..<m}. \<bar>cost_list ! e\<bar>)"
    by (intro add_mono sum_abs)
  also have "\<dots> \<le> (\<Sum>e\<in>{0..<m}. \<bar>cost_list ! e\<bar>) + (\<Sum>e\<in>{0..<m}. \<bar>cost_list ! e\<bar>)"
    by (intro add_mono sum_mono2) auto
  also have "\<dots> = 2 * sum_list (map abs cost_list)"
    by (simp add: sum_list_sum_nth atLeast0LessThan length_cost_list_m)
  finally have "\<bar>snd (ds_pot (build_tree acyc_flow) ! w)\<bar> \<le> 2 * sum_list (map abs cost_list)"
    using AD(7) by simp
  hence "pv_invar (ds_pot (build_tree acyc_flow) ! w)" by (simp add: pv_invar_def)
  thus ?thesis using gp by simp
qed

lemma NS_verts: "NS.\<V> = insert vcount Vseen"
proof -
  note [simp del] = NS.fst_exec_eq NS.snd_exec_eq
  have dvs: "NS.\<V> = (\<Union>e\<in>{0..<m+Kart}. {fst_all!e, snd_all!e})"
    by (auto simp: dVs_def NS.make_pair_function)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> NS.\<V>"
    then obtain e where e: "e < m+Kart" and xe: "x = fst_all!e \<or> x = snd_all!e"
      using dvs by auto
    show "x \<in> insert vcount Vseen"
    proof (cases "e < m")
      case True
      have fe: "fst_all!e = fst_list!e" and se: "snd_all!e = snd_list!e"
        using True by (simp_all add: fst_all_real snd_all_real)
      have "fst_list!e \<in> set fst_list" using True by (metis length_fst_list_m nth_mem)
      moreover have "snd_list!e \<in> set snd_list" using True by (metis length_snd_list_m nth_mem)
      ultimately have "fst_list!e \<in> Vseen" "snd_list!e \<in> Vseen" using Vseen_eq_V V_orig_eq by auto
      thus ?thesis using xe fe se by auto
    next
      case False
      define k where "k = e - m"
      have kK: "k < Kart" using e False by (simp add: k_def)
      have em: "e = m + k" using False by (simp add: k_def)
      have "fst_all!e = ds_afst (build_tree acyc_flow)!k" using kK em by (simp add: fst_all_art)
      moreover have "snd_all!e = ds_asnd (build_tree acyc_flow)!k" using kK em by (simp add: snd_all_art)
      moreover have "ds_afst (build_tree acyc_flow)!k \<in> insert vcount Vseen
                     \<and> ds_asnd (build_tree acyc_flow)!k \<in> insert vcount Vseen"
        using build_tree_tail_sub kK by (simp add: tail_sub_def Kart_def seen_set_build_tree)
      ultimately show ?thesis using xe by auto
    qed
  next
    fix x assume "x \<in> insert vcount Vseen"
    hence "x = vcount \<or> x \<in> Vseen" by simp
    thus "x \<in> NS.\<V>"
    proof
      assume xv: "x = vcount"
      have k0: "0 < Kart" by (rule Kart_pos)
      have tok: "tail_edge_ok (build_tree acyc_flow) 0" using build_tree_tail_content k0 by (simp add: tail_content_def Kart_def)
      then obtain subj where subj: "subj < vcount"
        and af: "ds_afst (build_tree acyc_flow)!0 = (if art_dir subj then subj else vcount)"
        and as: "ds_asnd (build_tree acyc_flow)!0 = (if art_dir subj then vcount else subj)"
        by (auto simp: tail_edge_ok_def)
      have am: "fst_all!m = ds_afst (build_tree acyc_flow)!0" using k0 fst_all_art[of 0] by simp
      have sm: "snd_all!m = ds_asnd (build_tree acyc_flow)!0" using k0 snd_all_art[of 0] by simp
      have "vcount = fst_all!m \<or> vcount = snd_all!m"
        using af as am sm by (cases "art_dir subj") auto
      moreover have "m \<in> {0..<m+Kart}" using k0 by simp
      ultimately show ?thesis using dvs xv by auto
    next
      assume xvs: "x \<in> Vseen"
      have "\<exists>e<m. x = fst_all!e \<or> x = snd_all!e"
      proof -
        from xvs have "x \<in> set fst_list \<or> x \<in> set snd_list" using Vseen_eq_V V_orig_eq by blast
        thus ?thesis
        proof
          assume "x \<in> set fst_list"
          then obtain e where e: "e < m" and "fst_list!e = x" using length_fst_list_m by (metis in_set_conv_nth)
          hence "x = fst_all!e" using fst_all_real[OF e] by simp
          thus ?thesis using e by auto
        next
          assume "x \<in> set snd_list"
          then obtain e where e: "e < m" and "snd_list!e = x" using length_snd_list_m by (metis in_set_conv_nth)
          hence "x = snd_all!e" using snd_all_real[OF e] by simp
          thus ?thesis using e by auto
        qed
      qed
      then obtain e where elt: "e < m" and xe: "x = fst_all!e \<or> x = snd_all!e" by blast
      have "e \<in> {0..<m+Kart}" using elt by simp
      thus ?thesis using dvs xe by auto
    qed
  qed
qed

lemma pot_valid_build_tree: "NS.pot_valid (ds_pot (build_tree acyc_flow))"
proof -
  have "\<forall>v\<in>Varb. v < length (ds_pot (build_tree acyc_flow))"
    using len_pot_bt by (auto simp: Varb_def Vseen_def)
  moreover have "\<forall>v\<in>NS.\<V>. good_pot_val_c (ds_pot (build_tree acyc_flow) ! v)
                          \<and> pv_invar (ds_pot (build_tree acyc_flow) ! v)"
  proof
    fix v assume "v \<in> NS.\<V>"
    hence "v \<in> insert vcount Vseen" using NS_verts by simp
    thus "good_pot_val_c (ds_pot (build_tree acyc_flow) ! v) \<and> pv_invar (ds_pot (build_tree acyc_flow) ! v)"
      by (rule pot_value_ok)
  qed
  ultimately show ?thesis by (simp add: NS.pot_valid_def)
qed

subsection \<open>Towards the spanning-tree partition (obligation 9 / init\_partition): the edge tags\<close>

text \<open>The parent edges are exactly the InTree-tagged edges. The easy inclusion (a parent edge is
      InTree) is here: an interior parent edge is a free real edge (build\_tree\_par\_edge), a component
      root's parent edge is an artificial tree edge tagged InTree (build\_tree\_crext). Every edge is
      tagged with one of the three tags (state\_total). The reverse inclusion (an InTree edge is a
      parent edge) is the free-edge coverage theorem, still owed.\<close>

lemma state_par_InTree:
  assumes v: "v \<in> Vseen"
  shows "state_all ! (ds_par (build_tree acyc_flow) ! v) = InTree"
proof -
  let ?bt = "build_tree acyc_flow"
  have vlt: "v < vcount" and vseen: "ds_seen ?bt ! v" using v by (auto simp: Vseen_def)
  show ?thesis
  proof (cases "ds_prnt ?bt ! v = vcount")
    case False
    hence pd: "ds_prnt ?bt ! v < vcount"
      using build_tree_parent_in_seen[OF vlt vseen] by simp
    have pe: "ds_par ?bt ! v < m" and free: "is_free acyc_flow (ds_par ?bt ! v)"
      using build_tree_par_edge[OF vlt vseen pd] by simp_all
    have "edge_state acyc_flow ! (ds_par ?bt ! v) = InTree"
      using free is_free_iff[OF acyc_flow_nonneg acyc_flow_le_cap pe]
            edge_state_InTree_iff[OF acyc_flow_nonneg acyc_flow_le_cap pe] by simp
    thus ?thesis using pe by (simp add: state_all_real)
  next
    case True
    have ok: "cr_ext_ok ?bt v"
      using build_tree_crext vlt vseen True by (simp add: cr_ext_inv_def)
    have em: "m \<le> ds_par ?bt ! v"
      using build_tree_comproot_inv vlt vseen True by (simp add: comproot_inv_def comproot_edge_ok_def)
    obtain k where ek: "ds_par ?bt ! v = m + k" using em le_Suc_ex by (metis add.commute)
    have "ds_par ?bt ! v - m < ds_nxt ?bt"
      using build_tree_comproot_inv vlt vseen True by (simp add: comproot_inv_def comproot_edge_ok_def)
    hence kK: "k < Kart" using ek by (simp add: Kart_def)
    have "ds_aest ?bt ! k = InTree" using ok ek by (simp add: cr_ext_ok_def)
    thus ?thesis using ek kK by (simp add: state_all_art)
  qed
qed

lemma state_total:
  assumes e: "e < m + Kart"
  shows "state_all ! e = InL \<or> state_all ! e = InU \<or> state_all ! e = InTree"
proof (cases "e < m")
  case True
  have "state_all ! e = classify acyc_flow e" using True by (simp add: state_all_real edge_state_nth)
  thus ?thesis by (auto simp: classify_def)
next
  case False
  obtain k where ek: "e = m + k" using False le_Suc_ex by (metis add.commute not_less)
  have kK: "k < Kart" using e ek by simp
  have "ds_aest (build_tree acyc_flow) ! k = InTree \<or> ds_aest (build_tree acyc_flow) ! k = InU"
    using tail_edge_ok_build_tree[OF kK] by (auto simp: tail_edge_ok_def)
  thus ?thesis using ek kK by (auto simp: state_all_art)
qed

lemma T_sub_InTree:
  "(!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}) \<subseteq> {e \<in> {0..<m + Kart}. state_all ! e = InTree}"
proof
  fix x assume "x \<in> (!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})"
  then obtain v where vV: "v \<in> Vseen" and xv: "x = ds_par (build_tree acyc_flow) ! v"
    using NS_V_minus_root by auto
  have "state_all ! x = InTree" using xv state_par_InTree[OF vV] by simp
  moreover have "x \<in> {0..<m + Kart}"
    using xv NSinit_tree_corr vV NS_V_minus_root by auto
  ultimately show "x \<in> {e \<in> {0..<m + Kart}. state_all ! e = InTree}" by simp
qed

text \<open>Four of the seven still-open @{locale network_simplex_init} obligations are the store-length
      invariants; they are immediate from the array sizes (flow\_all / state\_all have length m + Kart;
      the vertex-indexed arrays have length Suc vcount, and every vertex name is below vcount).\<close>

lemma NSinit_flow_invar: "\<forall>k\<in>{0..<m + Kart}. k < length flow_all" by (simp add: length_flow_all)
lemma NSinit_es_invar_len: "\<forall>k\<in>{0..<m + Kart}. k < length state_all" by (simp add: length_state_all)
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
proof (induction rule: NS.ns_loop_induct[OF assms])
  case (1 s)
  note IH = this
  note dom = IH(1)
  show ?case
  proof (cases s rule: NS.ns_loop_cases)
    case 1 thus ?thesis by (simp add: NS.ns_loop_simps(1)[OF dom] NS.ns_optimal_def)
  next
    case 2 thus ?thesis by (simp add: NS.ns_loop_simps(2)[OF dom] NS.ns_unbounded_upd_def)
  next
    case 3 thus ?thesis using IH(2)[OF 3] by (simp add: NS.ns_loop_simps(3)[OF dom])
  next
    case 4 thus ?thesis using IH(3)[OF 4] by (simp add: NS.ns_loop_simps(4)[OF dom])
  qed
qed



subsection \<open>The acyclifier's None verdict is an original negative infinite-capacity cycle\<close>

text \<open>make\_acyclic\_none\_unbounded is reused verbatim. Its balance premise af\_feasible b f0 is
      schematic in b, since af\_feasible takes the balance as an argument rather than reading a locale
      parameter. So although flow\_list is only assumed capacity-feasible (flow\_nonneg, flow\_le\_cap)
      and is not a b\_lookup-flow, we may instantiate b with flow\_list's own balance and the premise
      becomes vacuous. No change to Acyclic\_Flow is needed.\<close>

lemma acyc_none_neg_cycle:
  assumes "acyc_flow_opt = None" shows neg_infty_cycle
proof -
  have vv: "vtx_invar \<lparr>vi_list = edged_vs_list, vi_pos = 0\<rparr>"
    using distinct_vs_list by (simp add: vtx_invar_def edged_vs_list_def distinct_filter)
  have vab: "vtx_abstract \<lparr>vi_list = edged_vs_list, vi_pos = 0\<rparr> \<subseteq> original_network.\<V>"
    by (simp add: vtx_abstract_def V_orig_eq_edged)
  have ff: "length flow_list = m" using length_flow length_edges by simp
  have res: "make_acyclic flow_list = None" using assms by (simp add: acyc_flow_opt_def)
  have feas: "af_feasible (\<lambda>v. - original_network.ex (h \<circ> (!) flow_list) v) flow_list"
    by (rule af_feasibleI[OF af_cap_feasible_flow_list]) simp
  have ninf: "neg_inf_cycle" by (rule make_acyclic_none_unbounded[OF multigraph_inv_csr ff feas vv vab res])
  from ninf obtain D
    where cw: "closed_w (original_network.make_pair ` {0..<m}) (map original_network.make_pair D)"
      and cst: "foldr (\<lambda>e. (+) (h (cost_list ! e))) D 0 < 0"
      and sD: "set D \<subseteq> {0..<m}"
      and inf: "\<forall>e\<in>set D. (if e < m then if capacity_list ! e = - 1 then \<infinity> else ereal (h (capacity_list ! e)) else \<infinity>) = PInfty"
    unfolding has_neg_infty_cycle_def by blast
  have foldeq: "foldr (\<lambda>e. (+) (h (cost_list ! e))) D 0 = h (foldr (\<lambda>e. (+) (cost_list ! e)) D 0)"
    by (induction D) (simp_all add: h_add)
  have c2: "foldr (\<lambda>e. (+) (cost_list ! e)) D 0 < 0" using cst foldeq by simp
  show neg_infty_cycle unfolding has_neg_infty_cycle_def using cw c2 sD inf by blast
qed

subsection \<open>An augmented {\isasyminfinity}-cycle is already an original {\isasyminfinity}-cycle\<close>

text \<open>Every artificial edge carries a finite capacity: tail\_edge\_ok\_build\_tree pins it to
      art\_tree\_cap subj or art\_flow subj, both non-negative, hence never the -1 sentinel that decodes
      to an infinite capacity. So a cycle all of whose arcs have infinite capacity cannot touch the
      artificial part, and on the original part the endpoint, cost and capacity arrays agree by
      fst\_all\_real, snd\_all\_real, cap\_all\_real and cost\_all\_real. The artificial device therefore
      cannot manufacture an unboundedness verdict of its own.\<close>

lemma cap_all_art_fin:
  assumes e1: "m \<le> e" and e2: "e < m + Kart" shows "cap_all ! e \<noteq> - 1"
proof -
  obtain k where ek: "e = m + k" using e1 by (metis le_Suc_ex)
  have kK: "k < Kart" using e2 ek by simp
  have "cap_all ! e = ds_acap (build_tree acyc_flow) ! k" using ek kK by (simp add: cap_all_art)
  moreover have "0 \<le> ds_acap (build_tree acyc_flow) ! k"
    using tail_edge_ok_build_tree[OF kK]
    by (auto simp: tail_edge_ok_def art_tree_cap_def art_flow_def)
  ultimately show ?thesis by simp
qed

lemma closed_w_restrict:
  assumes cw: "closed_w E p" and sub: "set p \<subseteq> E'"
  shows "closed_w E' p"
proof -
  from cw obtain u where u: "awalk E u p u" and len: "0 < length p" by (auto simp: closed_w_def)
  from u have cas: "cas u p u" by (simp add: awalk_def)
  obtain a b q where p: "p = (a, b) # q" using len by (cases p) auto
  have ua: "u = a" using cas p by simp
  have "(a, b) \<in> E'" using sub p by simp
  hence "u \<in> dVs E'" using ua by (auto simp: dVs_def)
  thus ?thesis using cas sub len by (auto simp: closed_w_def awalk_def)
qed

text \<open>Note. The simplifier calls below are deliberately "simp only". Under the NS interpretation
      the endpoint bridge NS.fst\_exec\_eq instantiates to

        e : {0..<m+Kart} ==> fst\_all ! e = (if e < m + Kart then fst\_all ! e else ...)

      whose right-hand side contains its own left-hand side. As a [simp] rule it rewrites fst\_all ! e
      to itself forever, so any plain simp on a goal mentioning fst\_all ! e or snd\_all ! e with
      e < m + Kart dischargeable diverges. The same holds for NS.snd\_exec\_eq. Declaring the two
      [simp del] removes the loop, but the fallout on existing proofs has not been measured, so the
      workaround here is local: unfold with simp only and discharge the conditions by hand.\<close>

lemma make_pair_real:
  assumes e: "e < m" shows "NS.make_pair e = original_network.make_pair e"
proof -
  have lt: "e < m + Kart" using e by simp
  show ?thesis
    by (simp only: NS.make_pair_def original_network.make_pair_def if_P[OF lt] if_P[OF e]
                   fst_all_real[OF e] snd_all_real[OF e])
qed

lemma cost_fold_real:
  "set D \<subseteq> {0..<m} \<Longrightarrow> foldr (\<lambda>e. (+) (cost_all ! e)) D 0 = h (foldr (\<lambda>e. (+) (cost_list ! e)) D 0)"
  by (induction D) (simp_all add: cost_all_real h_add)

lemma aug_neg_cycle_orig:
  assumes "has_neg_infty_cycle NS.make_pair {0..<m + Kart} ((!) cost_all)
             (\<lambda>e. if e < m + Kart then if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e)) else \<infinity>)"
  shows neg_infty_cycle
proof -
  obtain D where cw: "closed_w (NS.make_pair ` {0..<m + Kart}) (map NS.make_pair D)"
    and cst: "foldr (\<lambda>e. (+) (cost_all ! e)) D 0 < 0"
    and sD: "set D \<subseteq> {0..<m + Kart}"
    and inf: "\<forall>e \<in> set D. (if e < m + Kart then if cap_all ! e = - 1 then \<infinity>
                            else ereal (h (cap_all ! e)) else \<infinity>) = PInfty"
    using assms unfolding has_neg_infty_cycle_def by blast
  have Dm: "e < m" if eD: "e \<in> set D" for e
  proof (rule ccontr)
    assume ne: "\<not> e < m"
    have elt: "e < m + Kart" using sD eD by auto
    have "cap_all ! e = - 1" using bspec[OF inf eD] elt by (simp split: if_splits)
    thus False using cap_all_art_fin[OF _ elt] ne by simp
  qed
  hence sDm: "set D \<subseteq> {0..<m}" by auto
  have mapeq: "map NS.make_pair D = map original_network.make_pair D"
    using make_pair_real Dm by (simp add: map_eq_conv)
  have c1: "closed_w (original_network.make_pair ` {0..<m}) (map original_network.make_pair D)"
    by (rule closed_w_restrict[OF cw[unfolded mapeq]]) (use sDm in auto)
  have c2: "foldr (\<lambda>e. (+) (cost_list ! e)) D 0 < 0" using cst cost_fold_real[OF sDm] by simp
  have c3: "\<forall>e \<in> set D. (if e < m then if capacity_list ! e = - 1 then \<infinity>
                          else ereal (h (capacity_list ! e)) else \<infinity>) = PInfty"
  proof
    fix e assume eD: "e \<in> set D"
    have em: "e < m" by (rule Dm[OF eD])
    hence elt: "e < m + Kart" by simp
    have "cap_all ! e = - 1" using bspec[OF inf eD] elt by (simp split: if_splits)
    hence "capacity_list ! e = - 1" using em by (simp add: cap_all_real)
    thus "(if e < m then if capacity_list ! e = - 1 then \<infinity> else ereal (h (capacity_list ! e)) else \<infinity>) = PInfty"
      using em by simp
  qed
  show neg_infty_cycle using c1 c2 sDm c3 unfolding has_neg_infty_cycle_def by blast
qed

subsection \<open>The unbounded verdict\<close>



subsection \<open>The big-M transfer \<^emph>\<open>(still owed)\<close>\<close>

text \<open>The two feasible verdicts both rest on transferring the augmented optimum
      NSinit.network\_simplex\_correct(3) back to the original network. This is the classical big-M
      argument, and it is the only part of solve\_correct not yet discharged.

      aug\_opt\_zero\_art\_orig\_opt: if the augmented optimum loads no artificial edge it restricts to an
      original b\_lookup-flow, and it is optimal there because every original b\_lookup-flow extends to
      an augmented one of equal cost (put 0 on the artificial edges, which is feasible at the root
      because b\_lookup vcount = 0). This direction needs no bound on bigM.

      aug\_opt\_nonzero\_art\_infeasible: the converse, and the hard one. Suppose an original
      b\_lookup-flow f existed and extend it by 0 to an augmented f'. Then g optimal gives
      C\_aug g <= C\_aug f' = C\_orig f, and C\_aug g = C\_orig g + bigM * t where t is the total
      artificial flow. To contradict t > 0 one needs a lower bound on C\_orig g in terms of C\_orig f
      and t, i.e.

        C\_orig f - C\_orig g <= t * sum\_list (map abs cost\_list).

      Note what this is and is not. Restricted to the original edges g is a b'-flow for a balance b'
      that differs from b only at the artificial endpoints, with total deviation at most 2*t; the
      displayed bound is therefore a *sensitivity* (Lipschitz) statement about the minimum-cost
      function as the balance is perturbed, not a statement about any single path or cycle. It has to
      be proved by decomposing f - g (restricted to the original edges) into paths and cycles, the
      paths carrying at most t units in total; flowcycle\_decomposition in Flow\_Theory/Decomposition.thy
      is the intended starting point.

      Two traps to record, both of which cost a wrong sketch here already.

      First, the bound must be on the *rate*, not the total. Flows are real-valued, so t can be
      arbitrarily small and then bigM * t is small too; no bound of the form "bigM exceeds any
      achievable original cost" closes the argument.

      Second, a per-cycle argument does not work. Decomposing f' - g into residual cycles of g gives
      each cycle a non-negative cost, since g is optimal. But every artificial edge is incident to the
      root, so a *simple* residual cycle that touches the root uses exactly two artificial arcs; if one
      is traversed forwards and the other backwards their bigM contributions cancel, and the cycle's
      non-negative cost yields no contradiction however large bigM is. The cancellation is why the
      argument has to go through the aggregate sensitivity bound above.

      Both lemmas are stated on the abstract flow g of the augmented network; the theorem below feeds
      them NS.ns\_flow\_of (NS.ns\_loop NSinit.init\_state) and the artificial-edge test that solve
      performs.\<close>

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
  assumes dom: "NS.ns_loop_dom s"
  shows "NS.ns_invar s \<Longrightarrow> NS.ns_invar (NS.ns_loop s)"
proof (induction rule: NS.ns_loop_induct[OF dom])
  case (1 s)
  note IH = this
  show ?case
  proof (cases s rule: NS.ns_loop_cases)
    case 1
    show ?thesis using IH(4)
      by (simp add: NS.ns_loop_simps(1)[OF IH(1) 1] NS.ns_optimal_def ns_invar_ret)
  next
    case 2
    show ?thesis using IH(4)
      by (simp add: NS.ns_loop_simps(2)[OF IH(1) 2] NS.ns_unbounded_upd_def ns_invar_ret)
  next
    case 3
    show ?thesis using IH(2)[OF 3 NS.ns_flip_preservation(1)[OF IH(4) 3]]
      by (simp add: NS.ns_loop_simps(3)[OF IH(1) 3])
  next
    case 4
    show ?thesis using IH(3)[OF 4 NS.ns_pivot_preservation(1)[OF IH(4) 4]]
      by (simp add: NS.ns_loop_simps(4)[OF IH(1) 4])
  qed
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

lemma ex_agree:
  assumes z: "\<And>k. m \<le> k \<Longrightarrow> k < m + Kart \<Longrightarrow> g k = 0"
  shows "NS.ex g v = original_network.ex g v"
proof -
  have sub: "NS.delta_plus v \<subseteq> {0..<m + Kart}"
    by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: NS.delta_plus_def)
  have step: "(\<Sum>e \<in> NS.delta_plus v. g e) = (\<Sum>e \<in> NS.delta_plus v \<inter> {0..<m}. g e)"
  proof (rule sum.mono_neutral_right)
    show "finite (NS.delta_plus v)" by (rule delta_fin)
    show "NS.delta_plus v \<inter> {0..<m} \<subseteq> NS.delta_plus v" by auto
    show "\<forall>e \<in> NS.delta_plus v - NS.delta_plus v \<inter> {0..<m}. g e = 0"
    proof
      fix e assume e: "e \<in> NS.delta_plus v - NS.delta_plus v \<inter> {0..<m}"
      hence "m \<le> e" "e < m + Kart" using sub by auto
      thus "g e = 0" by (rule z)
    qed
  qed
  hence P: "(\<Sum>e \<in> NS.delta_plus v. g e) = (\<Sum>e \<in> original_network.delta_plus v. g e)"
    by (simp add: delta_plus_orig)
  have sub2: "NS.delta_minus v \<subseteq> {0..<m + Kart}"
    by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: NS.delta_minus_def)
  have "(\<Sum>e \<in> NS.delta_minus v. g e) = (\<Sum>e \<in> NS.delta_minus v \<inter> {0..<m}. g e)"
  proof (rule sum.mono_neutral_right)
    show "finite (NS.delta_minus v)" by (rule delta_fin)
    show "NS.delta_minus v \<inter> {0..<m} \<subseteq> NS.delta_minus v" by auto
    show "\<forall>e \<in> NS.delta_minus v - NS.delta_minus v \<inter> {0..<m}. g e = 0"
    proof
      fix e assume e: "e \<in> NS.delta_minus v - NS.delta_minus v \<inter> {0..<m}"
      hence "m \<le> e" "e < m + Kart" using sub2 by auto
      thus "g e = 0" by (rule z)
    qed
  qed
  hence M: "(\<Sum>e \<in> NS.delta_minus v. g e) = (\<Sum>e \<in> original_network.delta_minus v. g e)"
    by (simp add: delta_minus_orig)
  show ?thesis unfolding NS.ex_def original_network.ex_def using P M by simp
qed

text \<open>Likewise the augmented and original costs of such a flow agree.\<close>

lemma cost_agree:
  assumes z: "\<And>k. m \<le> k \<Longrightarrow> k < m + Kart \<Longrightarrow> g k = 0"
  shows "NS.\<C> g = original_network.\<C> g"
proof -
  have "NS.\<C> g = (\<Sum>e \<in> {0..<m + Kart}. g e * cost_all ! e)" by (simp add: NS.\<C>_def)
  also have "\<dots> = (\<Sum>e \<in> {0..<m}. g e * cost_all ! e)"
  proof (rule sum.mono_neutral_right)
    show "finite {0..<m + Kart}" by simp
    show "{0..<m} \<subseteq> {0..<m + Kart}" by auto
    show "\<forall>e \<in> {0..<m + Kart} - {0..<m}. g e * cost_all ! e = 0"
    proof
      fix e assume "e \<in> {0..<m + Kart} - {0..<m}"
      hence "m \<le> e" "e < m + Kart" by auto
      thus "g e * cost_all ! e = 0" using z by simp
    qed
  qed
  also have "\<dots> = (\<Sum>e \<in> {0..<m}. g e * h (cost_list ! e))" by (simp add: cost_all_real)
  also have "\<dots> = original_network.\<C> g" by (simp add: original_network.\<C>_def)
  finally show ?thesis .
qed

text \<open>An augmented flow restricts to an original flow: dropping the (unused) artificial edges keeps
      capacity-compliance and, by ex\_agree at every original vertex, the balances.\<close>

lemma isuflow_restrict:
  assumes "NS.isuflow g"
  shows "original_network.isuflow g"
proof (unfold original_network.isuflow_def, rule ballI)
  fix e assume e: "e \<in> {0..<m}"
  hence em: "e < m" by simp
  have cc: "cap_all ! e = capacity_list ! e" by (rule cap_all_real[OF em])
  from assms e have "ereal (g e) \<le> (if e < m + Kart then (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) else \<infinity>) \<and> 0 \<le> g e"
    unfolding NS.isuflow_def by auto
  hence "ereal (g e) \<le> (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) \<and> 0 \<le> g e"
    using em by simp
  hence "ereal (g e) \<le> (if capacity_list ! e = - 1 then \<infinity> else ereal (h (capacity_list ! e))) \<and> 0 \<le> g e"
    unfolding cc .
  thus "ereal (g e) \<le> (if e < m then if capacity_list ! e = - 1 then \<infinity> else ereal (h (capacity_list ! e)) else \<infinity>) \<and> 0 \<le> g e"
    using em by simp
qed

lemma bflow_restrict:
  assumes bf: "NS.isbflow g (\<lambda>v. h (b_lookup v))"
    and z: "\<And>k. m \<le> k \<Longrightarrow> k < m + Kart \<Longrightarrow> g k = 0"
  shows "original_network.isbflow g (\<lambda>v. h (b_lookup v))"
proof (rule original_network.isbflowI)
  show "original_network.isuflow g" using bf isuflow_restrict by (auto simp: NS.isbflow_def)
  fix v assume "v \<in> original_network.\<V>"
  hence vin: "v \<in> NS.\<V>" using NS_verts Vseen_eq_V by auto
  have "- NS.ex g v = h (b_lookup v)" using bf vin by (auto simp: NS.isbflow_def)
  thus "- original_network.ex g v = h (b_lookup v)" using ex_agree[OF z, where v=v] by simp
qed

text \<open>Conversely an original flow extends to an augmented one by putting zero on the artificial edges.
      Capacity holds (artificial capacities are non-negative), the balances hold at every original
      vertex, and at the root because b\_lookup vcount = 0. The cost is unchanged.\<close>

lemma orig_ex_ext:
  "original_network.ex (\<lambda>e. if e < m then f e else 0) v = original_network.ex f v"
proof -
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
proof -
  have dp: "original_network.delta_plus v = {}"
    using assms fst_list_nth_vertex by (auto simp: original_network.delta_plus_def original_network.make_pair_def)
  have dm: "original_network.delta_minus v = {}"
    using assms snd_list_nth_vertex by (auto simp: original_network.delta_minus_def original_network.make_pair_def)
  show ?thesis by (simp add: original_network.ex_def dp dm)
qed

lemma isuflow_ext:
  assumes "original_network.isuflow f"
  shows "NS.isuflow (\<lambda>e. if e < m then f e else 0)"
proof (unfold NS.isuflow_def, rule ballI)
  fix e assume e: "e \<in> {0..<m + Kart}"
  hence eK: "e < m + Kart" by simp
  show "ereal (if e < m then f e else 0) \<le> (if e < m + Kart then (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) else \<infinity>) \<and> 0 \<le> (if e < m then f e else 0)"
  proof (cases "e < m")
    case True
    have cc: "cap_all ! e = capacity_list ! e" by (rule cap_all_real[OF True])
    have "ereal (f e) \<le> (if e < m then if capacity_list ! e = - 1 then \<infinity> else ereal (h (capacity_list ! e)) else \<infinity>) \<and> 0 \<le> f e"
      using assms True unfolding original_network.isuflow_def by auto
    hence "ereal (f e) \<le> (if capacity_list ! e = - 1 then \<infinity> else ereal (h (capacity_list ! e))) \<and> 0 \<le> f e"
      using True by simp
    hence "ereal (f e) \<le> (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) \<and> 0 \<le> f e"
      unfolding cc .
    thus ?thesis using True eK by simp
  next
    case False
    have cap: "0 \<le> cap_all ! e \<or> cap_all ! e = - 1" using cap_all_nonneg[OF eK] .
    show ?thesis using False eK cap by (auto simp: zero_ereal_def)
  qed
qed

lemma bflow_ext:
  assumes bf: "original_network.isbflow f (\<lambda>v. h (b_lookup v))"
  shows "NS.isbflow (\<lambda>e. if e < m then f e else 0) (\<lambda>v. h (b_lookup v))"
proof (rule NS.isbflowI)
  show "NS.isuflow (\<lambda>e. if e < m then f e else 0)"
    using bf isuflow_ext by (auto simp: original_network.isbflow_def)
next
  fix v assume vV: "v \<in> NS.\<V>"
  have zz: "\<And>k. m \<le> k \<Longrightarrow> k < m + Kart \<Longrightarrow> (\<lambda>e. if e < m then f e else 0) k = 0" by simp
  have exeq: "NS.ex (\<lambda>e. if e < m then f e else 0) v = original_network.ex f v"
    using ex_agree[OF zz, where v=v] orig_ex_ext[where v=v] by simp
  from vV have "v = vcount \<or> v \<in> Vseen" using NS_verts by auto
  thus "- NS.ex (\<lambda>e. if e < m then f e else 0) v = h (b_lookup v)"
  proof
    assume "v = vcount"
    thus ?thesis using exeq orig_ex_notin_V[where v=vcount and f=f] vs_less_vcount b_lookup_root by auto
  next
    assume vvs: "v \<in> Vseen"
    hence "v \<in> original_network.\<V>" using Vseen_eq_V by simp
    hence "- original_network.ex f v = h (b_lookup v)" using bf by (auto simp: original_network.isbflow_def)
    thus ?thesis using exeq by simp
  qed
qed

lemma cost_ext: "NS.\<C> (\<lambda>e. if e < m then f e else 0) = original_network.\<C> f"
proof -
  have z: "\<And>k. m \<le> k \<Longrightarrow> k < m + Kart \<Longrightarrow> (\<lambda>e. if e < m then f e else 0) k = 0" by simp
  have "NS.\<C> (\<lambda>e. if e < m then f e else 0) = original_network.\<C> (\<lambda>e. if e < m then f e else 0)"
    by (rule cost_agree[OF z])
  also have "\<dots> = original_network.\<C> f"
    by (simp add: original_network.\<C>_def)
  finally show ?thesis .
qed

lemma aug_opt_zero_art_orig_opt:
  assumes opt: "NS.is_Opt (\<lambda>v. h (b_lookup v)) g"
    and zero: "\<And>k. m \<le> k \<Longrightarrow> k < m + Kart \<Longrightarrow> g k = 0"
  shows "original_network.is_Opt (\<lambda>v. h (b_lookup v)) g"
proof (rule original_network.is_OptI)
  have gbf: "NS.isbflow g (\<lambda>v. h (b_lookup v))" using opt by (simp add: NS.is_Opt_def)
  show orig_bf: "original_network.isbflow g (\<lambda>v. h (b_lookup v))" by (rule bflow_restrict[OF gbf zero])
  fix f' assume f'bf: "original_network.isbflow f' (\<lambda>v. h (b_lookup v))"
  let ?e = "\<lambda>e. if e < m then f' e else 0"
  have "NS.isbflow ?e (\<lambda>v. h (b_lookup v))" by (rule bflow_ext[OF f'bf])
  hence "NS.\<C> g \<le> NS.\<C> ?e" using opt by (simp add: NS.is_Opt_def)
  moreover have "NS.\<C> g = original_network.\<C> g" by (rule cost_agree[OF zero])
  moreover have "NS.\<C> ?e = original_network.\<C> f'" by (rule cost_ext)
  ultimately show "original_network.\<C> f' \<ge> original_network.\<C> g" by simp
qed

text \<open>Note the shape of the second premise. Stating it with a free k, as in

    and nz: "m <= k" "k < m + Kart" "g k ~= 0"

  exports k as a schematic ?k, so the premise becomes ?g ?k ~= 0: a schematic function applied to a
  schematic argument. Resolving that against a concrete fact is a flex-flex higher-order unification
  problem, and instantiating the lemma with OF then diverges. Binding k with an existential keeps the
  occurrence as ?g applied to a bound variable, which is a Miller pattern and unifies in one step.
  The sibling lemma above is safe for the same reason: its k is bound by the meta-quantifier.\<close>

lemma cost_res_F: "NS.\<cc> (F (e::nat)) = cost_all ! e"
  using NS.\<CC>_def[of "[F e]"] by simp
lemma cost_res_B: "NS.\<cc> (B (e::nat)) = - cost_all ! e"
  using NS.\<CC>_def[of "[B e]"] by simp


lemma abs_cost_orig_bound:
  "(\<Sum>c \<in> ({F e |e. e < m} \<union> {B e |e. e < m}). \<bar>NS.\<cc> c\<bar>) = 2 * h (sum_list (map abs cost_list))"
proof -
  have finF: "finite {F e |e. e < (m::nat)}" and finB: "finite {B e |e. e < (m::nat)}"
    by (auto simp: finite_image_set)
  have disj: "{F e |e. e < m} \<inter> {B e |e. e < m} = {}" by auto
  have injF: "inj_on F {e. e < m}" and injB: "inj_on B {e. e < m}" by (auto simp: inj_on_def)
  have "(\<Sum>e \<in> {e. e < m}. \<bar>cost_all ! e\<bar>) = h (sum_list (map abs cost_list))"
  proof -
    have "(\<Sum>e \<in> {e. e < m}. \<bar>cost_all ! e\<bar>) = (\<Sum>e \<in> {0..<m}. h \<bar>cost_list ! e\<bar>)"
      by (auto simp: cost_all_real h_abs atLeast0LessThan lessThan_def intro: sum.cong)
    also have "\<dots> = h (\<Sum>e \<in> {0..<m}. \<bar>cost_list ! e\<bar>)" by (simp add: h_sum)
    also have "\<dots> = h (sum_list (map abs cost_list))"
      by (simp add: sum_list_sum_nth atLeast0LessThan length_cost_list_m)
    finally show ?thesis .
  qed
  moreover have "(\<Sum>c \<in> {F e |e. e < m}. \<bar>NS.\<cc> c\<bar>) = (\<Sum>e \<in> {e. e < m}. \<bar>cost_all ! e\<bar>)"
    by (simp add: setcompr_eq_image sum.reindex[OF injF] cost_res_F)
  moreover have "(\<Sum>c \<in> {B e |e. e < m}. \<bar>NS.\<cc> c\<bar>) = (\<Sum>e \<in> {e. e < m}. \<bar>cost_all ! e\<bar>)"
    by (simp add: setcompr_eq_image sum.reindex[OF injB] cost_res_B)
  ultimately show ?thesis
    by (subst sum.union_disjoint[OF finF finB disj]) simp
qed

text \<open>A distinct residual arc list living in the augmented residual graph, containing at least one
      reverse artificial arc and no forward artificial arc, has strictly negative residual cost: each
      reverse artificial arc contributes -bigM, while the original arcs together contribute at most
      2 * sum\_list (map abs cost\_list) in absolute value, and bigM dominates that.\<close>

lemma neg_res_cost:
  assumes dist: "distinct cs"
    and sub: "set cs \<subseteq> NS.\<EE>"
    and noFart: "\<And>k'. m \<le> k' \<Longrightarrow> k' < m + Kart \<Longrightarrow> F k' \<notin> set cs"
    and Bk: "B k \<in> set cs" and k1: "m \<le> k" and k2: "k < m + Kart"
  shows "NS.\<CC> cs < 0"
proof -
  define S where "S = set cs"
  define A where "A = {c \<in> S. \<exists>k'. m \<le> k' \<and> k' < m + Kart \<and> c = B k'}"
  define Oo where "Oo = S - A"
  have finS: "finite S" by (simp add: S_def)
  have SE: "S \<subseteq> NS.\<EE>" using sub by (simp add: S_def)
  have Oo_orig: "Oo \<subseteq> {F e |e. e < m} \<union> {B e |e. e < m}"
  proof
    fix c assume c: "c \<in> Oo"
    hence cS: "c \<in> S" and cnA: "c \<notin> A" by (auto simp: Oo_def)
    from cS SE have "c \<in> NS.\<EE>" by auto
    then obtain d where d: "d < m + Kart" and cd: "c = F d \<or> c = B d" by (auto simp: NS.\<EE>_def)
    show "c \<in> {F e |e. e < m} \<union> {B e |e. e < m}"
    proof (cases "d < m")
      case True thus ?thesis using cd by auto
    next
      case False
      hence dm: "m \<le> d" by simp
      from cd show ?thesis
      proof
        assume "c = F d" thus ?thesis using noFart[OF dm d] cS by (simp add: S_def)
      next
        assume cB: "c = B d"
        hence "c \<in> A" using dm d cS by (auto simp: A_def)
        thus ?thesis using cnA by simp
      qed
    qed
  qed
  have finA: "finite A" and finO: "finite Oo" using finS by (auto simp: A_def Oo_def)
  have Ainter: "A \<inter> Oo = {}" by (auto simp: Oo_def)
  have SAO: "S = A \<union> Oo" by (auto simp: Oo_def A_def)
  have costA: "\<And>c. c \<in> A \<Longrightarrow> NS.\<cc> c = - bigM"
    by (auto simp: A_def cost_res_B cost_all_art')
  have "NS.\<CC> cs = (\<Sum>c \<in> S. NS.\<cc> c)" by (simp add: NS.\<CC>_def S_def)
  also have "\<dots> = (\<Sum>c \<in> A. NS.\<cc> c) + (\<Sum>c \<in> Oo. NS.\<cc> c)"
    using SAO Ainter finA finO by (simp add: sum.union_disjoint)
  finally have split: "NS.\<CC> cs = (\<Sum>c \<in> A. NS.\<cc> c) + (\<Sum>c \<in> Oo. NS.\<cc> c)" .
  have Aval: "(\<Sum>c \<in> A. NS.\<cc> c) = - bigM * real (card A)"
    using costA by simp
  have Anz: "B k \<in> A" using Bk k1 k2 by (auto simp: A_def S_def)
  have cA: "card A \<noteq> 0" using finA Anz by auto
  have Alb: "(\<Sum>c \<in> A. NS.\<cc> c) \<le> - bigM"
  proof -
    have "(1::real) \<le> real (card A)" using cA by (simp add: Suc_leI)
    hence "bigM \<le> bigM * real (card A)" using bigM_pos by simp
    thus ?thesis using Aval by simp
  qed
  have "(\<Sum>c \<in> Oo. NS.\<cc> c) \<le> (\<Sum>c \<in> Oo. \<bar>NS.\<cc> c\<bar>)" by (rule sum_mono) simp
  also have "\<dots> \<le> (\<Sum>c \<in> ({F e |e. e < m} \<union> {B e |e. e < m}). \<bar>NS.\<cc> c\<bar>)"
    by (rule sum_mono2) (auto simp: Oo_orig finite_image_set)
  also have "\<dots> = 2 * h (sum_list (map abs cost_list))" by (rule abs_cost_orig_bound)
  finally have Oub: "(\<Sum>c \<in> Oo. NS.\<cc> c) \<le> 2 * h (sum_list (map abs cost_list))" .
  have "NS.\<CC> cs \<le> - bigM + 2 * h (sum_list (map abs cost_list))"
    using split Alb Oub by simp
  also have "\<dots> < 0"
  proof -
    have "0 \<le> h (sum_list (map abs cost_list))" using sabs_nonneg by (rule h_nonneg)
    thus ?thesis using bigM_gt by linarith
  qed
  finally show ?thesis .
qed

lemma aug_opt_nonzero_art_infeasible:
  assumes opt: "NS.is_Opt (\<lambda>v. h (b_lookup v)) g"
    and nz: "\<exists>k. m \<le> k \<and> k < m + Kart \<and> g k \<noteq> 0"
  shows "\<nexists> f. original_network.isbflow f (\<lambda>v. h (b_lookup v))"
proof (rule notI)
  assume "\<exists>f. original_network.isbflow f (\<lambda>v. h (b_lookup v))"
  then obtain f where forig: "original_network.isbflow f (\<lambda>v. h (b_lookup v))" by blast
  interpret rf: flow_network where fst = NS.fstv and snd = NS.sndv
      and create_edge = NS.create_edge_residual and \<E> = "NS.\<EE>" and \<u> = "\<lambda> _. PInfty"
    using NS.make_pair NS.create_edge NS.E_not_empty NS.oedge_on_\<EE>
    by (auto simp add: NS.finite_\<EE> NS.make_pair[OF refl refl] NS.create_edge
                       cost_flow_network_def flow_network_axioms_def flow_network_def multigraph_def)
  obtain k where k1: "m \<le> k" and k2: "k < m + Kart" and gk: "g k \<noteq> 0" using nz by blast
  define ef where "ef = (\<lambda>e. if e < m then f e else 0)"
  define d where "d = NS.difference ef g"
  have gbf: "NS.isbflow g (\<lambda>v. h (b_lookup v))" using opt by (simp add: NS.is_Opt_def)
  have guf: "NS.isuflow g" using gbf by (simp add: NS.isbflow_def)
  have efbf: "NS.isbflow ef (\<lambda>v. h (b_lookup v))" using bflow_ext[OF forig] by (simp add: ef_def)
  have efuf: "NS.isuflow ef" using efbf by (simp add: NS.isbflow_def)
  have gnn: "\<And>e. e < m + Kart \<Longrightarrow> 0 \<le> g e"
    using guf by (auto simp: NS.isuflow_def)
  have gk0: "g k > 0" using gnn[OF k2] gk by simp
  \<comment> \<open>d is a non-negative residual circulation\<close>
  have circ: "rf.is_circ d" using NS.diff_is_res_circ[OF gbf efbf] by (simp add: d_def)
  have nn: "rf.flow_non_neg d" using NS.diff_non_neg by (simp add: d_def rf.flow_non_neg_def)
  \<comment> \<open>B k is in the support: it reduces the loaded artificial edge\<close>
  have efk: "ef k = 0" using k1 by (simp add: ef_def)
  have dBk: "d (B k) = g k" using efk gk0 by (simp add: d_def)
  have BkE: "B k \<in> NS.\<EE>" using k1 k2 by (auto simp: NS.\<EE>_def)
  have BkSupp: "B k \<in> rf.support d" using dBk gk0 BkE by (simp add: rf.support_def)
  have Abs_pos: "rf.Abs d > 0"
  proof -
    have "0 < d (B k)" using dBk gk0 by simp
    moreover have "rf.flow_non_neg d" by (rule nn)
    ultimately show ?thesis using BkE by (auto simp: rf.Abs_def rf.flow_non_neg_def
        intro: sum_pos2[of NS.\<EE> "B k" d] NS.finite_\<EE>)
  qed
  have supp_ne: "rf.support d \<noteq> {}" using BkSupp by auto
  \<comment> \<open>no forward artificial arc is in the support: g {\isasymge} 0 and ef is zero there\<close>
  have noFart: "\<And>k'. m \<le> k' \<Longrightarrow> k' < m + Kart \<Longrightarrow> F k' \<notin> rf.support d"
  proof -
    fix k' assume a1: "m \<le> k'" and a2: "k' < m + Kart"
    have "ef k' = 0" using a1 by (simp add: ef_def)
    moreover have "0 \<le> g k'" using gnn[OF a2] .
    ultimately have "d (F k') = 0" by (simp add: d_def)
    thus "F k' \<notin> rf.support d" by (simp add: rf.support_def)
  qed
  \<comment> \<open>decompose the circulation\<close>
  obtain css ws where cw:
      "length css = length ws" "set css \<noteq> {}" "\<forall>w\<in>set ws. 0 < w"
      "\<forall>cs\<in>set css. rf.flowcycle d cs \<and> set cs \<subseteq> rf.support d \<and> distinct cs"
      "\<forall>e\<in>NS.\<EE>. d e = (\<Sum>i<length css. if e \<in> set (css ! i) then ws ! i else 0)"
    using rf.flowcycle_decomposition[OF nn Abs_pos circ supp_ne refl] by blast
  have "d (B k) = (\<Sum>i<length css. if B k \<in> set (css ! i) then ws ! i else 0)"
    using cw(5) BkE by blast
  hence pos: "(\<Sum>i<length css. if B k \<in> set (css ! i) then ws ! i else 0) > 0" using dBk gk0 by simp
  have "\<exists>i<length css. B k \<in> set (css ! i)"
  proof (rule ccontr)
    assume "\<not> (\<exists>i<length css. B k \<in> set (css ! i))"
    hence "(\<Sum>i<length css. if B k \<in> set (css ! i) then ws ! i else 0) = 0"
      by (intro sum.neutral) auto
    thus False using pos by simp
  qed
  then obtain i where iL: "i < length css" and Bki: "B k \<in> set (css ! i)" by blast
  define cs where "cs = css ! i"
  have cyc: "rf.flowcycle d cs" and cssub: "set cs \<subseteq> rf.support d" and cdist: "distinct cs"
    using cw(4) iL by (auto simp: cs_def)
  \<comment> \<open>the selected cycle has negative residual cost (big-M dominates)\<close>
  have csE: "set cs \<subseteq> NS.\<EE>" using cssub by (auto simp: rf.support_def)
  have noF: "\<And>k'. m \<le> k' \<Longrightarrow> k' < m + Kart \<Longrightarrow> F k' \<notin> set cs"
    using noFart cssub by blast
  have Bk_cs: "B k \<in> set cs" using Bki by (simp add: cs_def)
  have neg: "NS.\<CC> cs < 0" by (rule neg_res_cost[OF cdist csE noF Bk_cs k1 k2])
  \<comment> \<open>the cycle is an augmenting cycle of g: positive residual capacity, closed, distinct\<close>
  have rcap_pos: "\<And>e. e \<in> set cs \<Longrightarrow> 0 < NS.rcap g e"
  proof -
    fix e assume "e \<in> set cs"
    hence "e \<in> rf.support d" using cssub by blast
    hence eE: "e \<in> NS.\<EE>" and de: "0 < d e" by (auto simp: rf.support_def)
    show "0 < NS.rcap g e"
      using NS.pos_difference_pos_rcap[OF guf efuf eE] de by (simp add: d_def)
  qed
  have flowpath: "rf.flowpath d cs" and cs_ne: "cs \<noteq> []"
      and closed: "NS.fstv (hd cs) = NS.sndv (last cs)"
    using cyc by (auto simp: rf.flowcycle_def)
  have mpath: "rf.multigraph_path cs" using flowpath by (simp add: rf.flowpath_def)
  have prepath: "NS.prepath cs"
    using mpath cs_ne by (simp add: NS.prepath_def rf.multigraph_path_def NS.to_vertex_pair_fst_snd)
  have rcap_min: "0 < NS.Rcap g (set cs)"
  proof -
    have fin: "finite {NS.rcap g e |e. e \<in> set cs}" by simp
    have "\<forall>x\<in>insert PInfty {NS.rcap g e |e. e \<in> set cs}. 0 < x"
      using rcap_pos by (auto simp: zero_less_iff_neq_zero)
    thus ?thesis by (simp add: NS.Rcap_def Min_gr_iff)
  qed
  have augpath: "NS.augpath g cs" using prepath rcap_min by (simp add: NS.augpath_def)
  have "NS.augcycle g cs"
    using neg augpath closed cdist csE by (simp add: NS.augcycle_def)
  thus False using NS.min_cost_flow_no_augcycle[OF opt] by blast
qed

text \<open>original\_network.is\_Opt only reads the edges 0 ..< m, so truncating the augmented flow with
      take m does not change it.\<close>

lemma is_Opt_take:
  assumes "m \<le> length f"
  shows "original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth (take m f)) = original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth f)"
proof
  have agree: "(h \<circ> nth (take m f)) e = (h \<circ> nth f) e" if "e \<in> {0..<m}" for e using that assms by (simp add: comp_def)
  assume "original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth (take m f))"
  thus "original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth f)"
    by (rule original_network.is_Opt_cong[rotated 2]) (use agree in auto)
next
  have agree: "(h \<circ> nth f) e = (h \<circ> nth (take m f)) e" if "e \<in> {0..<m}" for e using that assms by (simp add: comp_def)
  assume "original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth f)"
  thus "original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth (take m f))"
    by (rule original_network.is_Opt_cong[rotated 2]) (use agree in auto)
qed

subsection \<open>Total correctness of solve\<close>

text \<open>Toward free-edge coverage (obligation 9, the reverse inclusion). Under acyclicity the acyclified
      flow has no closed pre-path of distinct free arcs (flow\_no\_free\_cycle). The engine below packages
      that as: any closed walk of distinct free real edges is impossible. Coverage will feed it the
      cycle formed by an uncovered free edge together with the interior tree path between its endpoints.\<close>

lemma is_free_af_arc_free:
  assumes "e < m" and "is_free acyc_flow e"
  shows "af_arc_free acyc_flow e"
proof -
  have "edge_state acyc_flow ! e = InTree" using assms(2) by (simp add: is_free_def)
  hence "0 < acyc_flow ! e \<and> (capacity_list ! e = - 1 \<or> acyc_flow ! e < capacity_list ! e)"
    using edge_state_InTree_iff[OF acyc_flow_nonneg acyc_flow_le_cap assms(1)] by simp
  thus ?thesis by (simp add: af_arc_free_def Let_def)
qed

lemma free_walk_no_cycle:
  assumes acyc: "original_network.acyclic_flow (h \<circ> nth acyc_flow)"
    and ne: "C \<noteq> []"
    and free: "\<And>a. a \<in> set C \<Longrightarrow> original_network.oedge a < m \<and> is_free acyc_flow (original_network.oedge a)"
    and dist: "distinct (map original_network.oedge C)"
    and sub: "set C \<subseteq> original_network.\<EE>"
    and pp: "original_network.prepath C"
    and closed: "original_network.fstv (hd C) = original_network.sndv (last C)"
  shows False
proof -
  have "af_arc_free acyc_flow (original_network.oedge a)" if "a \<in> set C" for a
    using free[OF that] is_free_af_arc_free by blast
  hence "\<exists>C. original_network.prepath C \<and> (\<forall>e\<in>set C. af_arc_free acyc_flow (original_network.oedge e))
       \<and> distinct (map original_network.oedge C)
       \<and> original_network.fstv (hd C) = original_network.sndv (last C) \<and> set C \<subseteq> original_network.\<EE>"
    using pp dist closed sub by blast
  thus False using flow_no_free_cycle[OF acyc_flow_nonneg acyc_flow_le_cap acyc] by blast
qed

subsection \<open>Free-edge coverage: the scan-completeness invariant of the DFS (obligation 9, core)\<close>

text \<open>scan\_complete tracks that every free edge already scanned from a seen vertex --- one that is no
      longer among the remaining edges of the vertex's iterator --- has its far endpoint seen, and that a
      finished (seen, off-stack) vertex has no remaining edges. It needs no acyclicity --- it is pure DFS
      scan structure --- and is preserved by each build\_dfs step. At the end (empty stack) it says every
      free neighbour of every seen vertex is seen, which is what lets an uncovered free edge be closed
      into a free cycle for the engine.\<close>

definition scan_complete :: "'n dfs_state \<Rightarrow> bool" where
  "scan_complete s \<longleftrightarrow> (\<forall>v<vcount. ds_seen s ! v \<longrightarrow>
     (\<forall>e<m. is_free acyc_flow e \<and> fst_list ! e = v
        \<and> e \<notin> csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc s) v
        \<longrightarrow> ds_seen s ! (snd_list ! e))
   \<and> (\<forall>e<m. is_free acyc_flow e \<and> snd_list ! e = v
        \<and> e \<notin> csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic s) v
        \<longrightarrow> ds_seen s ! (fst_list ! e))
   \<and> (v \<notin> set (ds_stk s) \<longrightarrow>
        csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc s) v = {}
      \<and> csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic s) v = {}))"

text \<open>The generic preservation step: seen vertices stay seen, a freshly seen vertex is pushed with a
      full iterator, an edge leaving a remaining set has its far endpoint seen, and a vertex that is
      finished afterwards was finished before (with no new remaining edges) or has an empty iterator.\<close>

lemma scan_complete_upd:
  assumes sc: "scan_complete s"
    and seen: "\<And>x. ds_seen s ! x \<Longrightarrow> ds_seen t ! x"
    and fresh: "\<And>x. x < vcount \<Longrightarrow> ds_seen t ! x \<Longrightarrow> \<not> ds_seen s ! x \<Longrightarrow> x \<in> set (ds_stk t)
       \<and> csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc t) x
           = {e. e < m \<and> fst_list ! e = x \<and> is_free acyc_flow e}
       \<and> csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic t) x
           = {e. e < m \<and> snd_list ! e = x \<and> is_free acyc_flow e}"
    and out: "\<And>x e. x < vcount \<Longrightarrow> ds_seen s ! x
       \<Longrightarrow> e \<in> csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc s) x
       \<Longrightarrow> e \<notin> csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc t) x
       \<Longrightarrow> ds_seen t ! (snd_list ! e)"
    and inn: "\<And>x e. x < vcount \<Longrightarrow> ds_seen s ! x
       \<Longrightarrow> e \<in> csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic s) x
       \<Longrightarrow> e \<notin> csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic t) x
       \<Longrightarrow> ds_seen t ! (fst_list ! e)"
    and fin: "\<And>x. x < vcount \<Longrightarrow> ds_seen s ! x \<Longrightarrow> x \<notin> set (ds_stk t) \<Longrightarrow>
       (x \<notin> set (ds_stk s)
        \<and> csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc t) x
          \<subseteq> csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc s) x
        \<and> csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic t) x
          \<subseteq> csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic s) x)
       \<or> (csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc t) x = {}
          \<and> csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic t) x = {})"
  shows "scan_complete t"
  unfolding scan_complete_def
proof (intro allI impI conjI)
  fix x assume x: "x < vcount" and xt: "ds_seen t ! x"
  note S = sc[unfolded scan_complete_def, rule_format, OF x]
  fix e assume e: "e < m" and E: "is_free acyc_flow e \<and> fst_list ! e = x
      \<and> e \<notin> csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc t) x"
  show "ds_seen t ! (snd_list ! e)"
  proof (cases "ds_seen s ! x")
    case True
    thus ?thesis using S[OF True] out[OF x True _ conjunct2[OF conjunct2[OF E]]] seen e E by blast
  next
    case False
    thus ?thesis using fresh[OF x xt False] e E by blast
  qed
next
  fix x assume x: "x < vcount" and xt: "ds_seen t ! x"
  note S = sc[unfolded scan_complete_def, rule_format, OF x]
  fix e assume e: "e < m" and E: "is_free acyc_flow e \<and> snd_list ! e = x
      \<and> e \<notin> csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic t) x"
  show "ds_seen t ! (fst_list ! e)"
  proof (cases "ds_seen s ! x")
    case True
    thus ?thesis using S[OF True] inn[OF x True _ conjunct2[OF conjunct2[OF E]]] seen e E by blast
  next
    case False
    thus ?thesis using fresh[OF x xt False] e E by blast
  qed
next
  fix x assume x: "x < vcount" and xt: "ds_seen t ! x" and xs: "x \<notin> set (ds_stk t)"
  note S = sc[unfolded scan_complete_def, rule_format, OF x]
  have xss: "ds_seen s ! x" using fresh[OF x xt] xs by blast
  show "csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc t) x = {}"
    using fin[OF x xss xs] S[OF xss] by blast
  show "csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic t) x = {}"
    using fin[OF x xss xs] S[OF xss] by blast
qed

text \<open>The iterators restart at a pushed vertex: everything it owns is remaining.\<close>

lemma dfs_push_remaining:
  assumes w: "w < vcount"
  shows "csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc (dfs_push s w)) w
           = {e. e < m \<and> fst_list ! e = w \<and> is_free acyc_flow e}"
    and "csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic (dfs_push s w)) w
           = {e. e < m \<and> snd_list ! e = w \<and> is_free acyc_flow e}"
    and "\<And>j. j \<noteq> w \<Longrightarrow>
         csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc (dfs_push s w)) j
         = csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc s) j"
    and "\<And>j. j \<noteq> w \<Longrightarrow>
         csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic (dfs_push s w)) j
         = csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic s) j"
proof -
  interpret F: csr_ranges vcount "{..<vcount}" out.inp.B_spec "(!) (fst (free_out acyc_flow))" "snd (free_out acyc_flow)"
    by (rule free_out(1))
  interpret G: csr_ranges vcount "{..<vcount}" inc.inp.B_spec "(!) (fst (free_in acyc_flow))" "snd (free_in acyc_flow)"
    by (rule free_in(1))
  show "F.csr_remaining (ds_oc (dfs_push s w)) w = {e. e < m \<and> fst_list ! e = w \<and> is_free acyc_flow e}"
    using free_out(2)[OF w] by (simp add: dfs_push_def F.csr_reset_remaining)
  show "G.csr_remaining (ds_ic (dfs_push s w)) w = {e. e < m \<and> snd_list ! e = w \<and> is_free acyc_flow e}"
    using free_in(2)[OF w] by (simp add: dfs_push_def G.csr_reset_remaining)
  show "F.csr_remaining (ds_oc (dfs_push s w)) j = F.csr_remaining (ds_oc s) j" if "j \<noteq> w" for j
    using that by (simp add: dfs_push_def F.csr_reset_remaining_other)
  show "G.csr_remaining (ds_ic (dfs_push s w)) j = G.csr_remaining (ds_ic s) j" if "j \<noteq> w" for j
    using that by (simp add: dfs_push_def G.csr_reset_remaining_other)
qed

lemma discover_seen_eq: "ds_seen (dfs_discover s v w e) = (ds_seen s)[w := True]"
  by (simp add: dfs_discover_def dfs_push_def Let_def)

lemma bd_upd1_scan_complete:
  assumes inv: "dfs_inv acyc_flow s" and sc: "scan_complete s" and c: "bd_call1_conds acyc_flow s"
  shows "scan_complete (bd_upd1 acyc_flow s)"
proof -
  have wf: "dfs_wf acyc_flow s" and sz: "dfs_sized s" using inv by (simp_all add: dfs_inv_def)
  from c obtain v rest where stk: "ds_stk s = v # rest"
    and has: "csr_ranges.csr_has ((!) (fst (free_out acyc_flow))) (ds_oc s) v"
    by (auto simp: bd_call1_conds_def split: list.splits)
  note S = bd_out_step[OF wf stk has]
  define e where "e = csr_ranges.csr_current (snd (free_out acyc_flow)) (ds_oc s) v"
  define c' where "c' = csr_ranges.csr_move ((!) (fst (free_out acyc_flow))) (ds_oc s) v"
  define w where "w = snd_list ! e"
  have up: "bd_upd1 acyc_flow s
            = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr> else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
    by (simp add: bd_upd1_def stk Let_def e_def c'_def w_def)
  have wlt: "w < vcount" using S(4) by (simp add: w_def e_def)
  have lseen: "length (ds_seen s) = Suc vcount" using sz by (simp add: dfs_sized_def)
  have vin: "v \<in> set (ds_stk s)" using stk by simp
  have rem: "\<And>x. csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) c' x
      = (if x = v then csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc s) v - {e}
         else csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc s) x)"
    using S(7,8)[folded e_def c'_def] by simp
  show ?thesis
  proof (cases "ds_seen s ! w")
    case True
    show ?thesis unfolding up if_P[OF True]
      by (rule scan_complete_upd[OF sc]) (use True vin in \<open>auto simp: rem w_def split: if_splits\<close>)
  next
    case False
    let ?t = "bd_upd1 acyc_flow s"
    note P = dfs_push_remaining[OF wlt]
    have tseen: "ds_seen ?t = (ds_seen s)[w := True]" using False by (simp add: up discover_seen_eq)
    have tstk: "ds_stk ?t = w # ds_stk s" using False by (simp add: up dfs_discover_def dfs_push_def Let_def)
    have toc: "csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc ?t) j
        = (if j = w then {e. e < m \<and> fst_list ! e = w \<and> is_free acyc_flow e}
           else csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) c' j)" for j
      using False P(1,3) by (cases "j = w") (simp_all add: up dfs_discover_def Let_def)
    have tic: "csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic ?t) j
        = (if j = w then {e. e < m \<and> snd_list ! e = w \<and> is_free acyc_flow e}
           else csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic s) j)" for j
      using False P(2,4) by (cases "j = w") (simp_all add: up dfs_discover_def Let_def)
    show ?thesis
      by (rule scan_complete_upd[OF sc])
         (use False vin wlt lseen in \<open>auto simp: tseen tstk toc tic rem w_def nth_list_update split: if_splits\<close>)
  qed
qed

lemma bd_upd2_scan_complete:
  assumes inv: "dfs_inv acyc_flow s" and sc: "scan_complete s" and c: "bd_call2_conds acyc_flow s"
  shows "scan_complete (bd_upd2 acyc_flow s)"
proof -
  have wf: "dfs_wf acyc_flow s" and sz: "dfs_sized s" using inv by (simp_all add: dfs_inv_def)
  from c obtain v rest where stk: "ds_stk s = v # rest"
    and nho: "\<not> csr_ranges.csr_has ((!) (fst (free_out acyc_flow))) (ds_oc s) v"
    and has: "csr_ranges.csr_has ((!) (fst (free_in acyc_flow))) (ds_ic s) v"
    by (auto simp: bd_call2_conds_def split: list.splits)
  note S = bd_in_step[OF wf stk has]
  define e where "e = csr_ranges.csr_current (snd (free_in acyc_flow)) (ds_ic s) v"
  define c' where "c' = csr_ranges.csr_move ((!) (fst (free_in acyc_flow))) (ds_ic s) v"
  define w where "w = fst_list ! e"
  have up: "bd_upd2 acyc_flow s
            = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr> else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
    using nho by (simp add: bd_upd2_def stk Let_def e_def c'_def w_def)
  have wlt: "w < vcount" using S(4) by (simp add: w_def e_def)
  have lseen: "length (ds_seen s) = Suc vcount" using sz by (simp add: dfs_sized_def)
  have vin: "v \<in> set (ds_stk s)" using stk by simp
  have rem: "\<And>x. csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) c' x
      = (if x = v then csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic s) v - {e}
         else csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic s) x)"
    using S(7,8)[folded e_def c'_def] by simp
  show ?thesis
  proof (cases "ds_seen s ! w")
    case True
    show ?thesis unfolding up if_P[OF True]
      by (rule scan_complete_upd[OF sc]) (use True vin in \<open>auto simp: rem w_def split: if_splits\<close>)
  next
    case False
    let ?t = "bd_upd2 acyc_flow s"
    note P = dfs_push_remaining[OF wlt]
    have tseen: "ds_seen ?t = (ds_seen s)[w := True]" using False by (simp add: up discover_seen_eq)
    have tstk: "ds_stk ?t = w # ds_stk s" using False by (simp add: up dfs_discover_def dfs_push_def Let_def)
    have toc: "csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc ?t) j
        = (if j = w then {e. e < m \<and> fst_list ! e = w \<and> is_free acyc_flow e}
           else csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc s) j)" for j
      using False P(1,3) by (cases "j = w") (simp_all add: up dfs_discover_def Let_def)
    have tic: "csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic ?t) j
        = (if j = w then {e. e < m \<and> snd_list ! e = w \<and> is_free acyc_flow e}
           else csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) c' j)" for j
      using False P(2,4) by (cases "j = w") (simp_all add: up dfs_discover_def Let_def)
    show ?thesis
      by (rule scan_complete_upd[OF sc])
         (use False vin wlt lseen in \<open>auto simp: tseen tstk toc tic rem w_def nth_list_update split: if_splits\<close>)
  qed
qed

lemma bd_upd3_scan_complete:
  assumes inv: "dfs_inv acyc_flow s" and sc: "scan_complete s" and c: "bd_call3_conds acyc_flow s"
  shows "scan_complete (bd_upd3 s)"
proof -
  have wf: "dfs_wf acyc_flow s" using inv by (simp add: dfs_inv_def)
  from c obtain v rest where stk: "ds_stk s = v # rest"
    and o: "\<not> csr_ranges.csr_has ((!) (fst (free_out acyc_flow))) (ds_oc s) v"
    and i: "\<not> csr_ranges.csr_has ((!) (fst (free_in acyc_flow))) (ds_ic s) v"
    by (auto simp: bd_call3_conds_def split: list.splits)
  note E = bd_finish_empty[OF wf stk o i]
  have up: "bd_upd3 s = dfs_finish s v rest" by (simp add: bd_upd3_def stk)
  show ?thesis unfolding up
    by (rule scan_complete_upd[OF sc]) (use stk E in \<open>auto simp: dfs_finish_def Let_def\<close>)
qed

lemma emit_U_edge_scan_complete: "scan_complete (emit_U_edge s v) = scan_complete s"
  by (simp add: scan_complete_def emit_U_edge_def Let_def)

text \<open>A finished vertex has every free neighbour seen.\<close>

lemma scan_complete_finished:
  assumes sc: "scan_complete s" and a: "a < vcount" "ds_seen s ! a" "a \<notin> set (ds_stk s)"
    and e: "e < m" "is_free acyc_flow e"
  shows "fst_list ! e = a \<Longrightarrow> ds_seen s ! (snd_list ! e)"
    and "snd_list ! e = a \<Longrightarrow> ds_seen s ! (fst_list ! e)"
  using sc[unfolded scan_complete_def, rule_format, OF a(1,2)] a(3) e by auto

subsection \<open>Free-edge coverage: ancestor extraction and the walk-builder\<close>

text \<open>A vertex on the stack is a pstep-ancestor of the top (@{thm stk_top_reaches}) --- this is what
      the merged invariant's ancinv conjunct uses at dfs\_discover. Further, chain\_redge turns a tree edge into the residual arc
      oriented from child to parent, and chain\_redge\_props certifies it is a free real edge of the
      original residual graph with the right endpoints --- the atom the walk-builder assembles into a
      pstep-chain prepath for free\_walk\_no\_cycle.\<close>

lemma cr_fstv_F: "e < m \<Longrightarrow> original_network.fstv (F e) = fst_list ! e"
  by simp
lemma cr_sndv_F: "e < m \<Longrightarrow> original_network.sndv (F e) = snd_list ! e"
  by simp
lemma cr_inE_F: "e < m \<Longrightarrow> F e \<in> original_network.\<EE>"
  by (simp add: original_network.\<EE>_def)
lemma cr_inE_B: "e < m \<Longrightarrow> B e \<in> original_network.\<EE>"
  by (simp add: original_network.\<EE>_def)

lemma cr_fstv_B: "e < m \<Longrightarrow> original_network.fstv (B e) = snd_list ! e" by simp
lemma cr_sndv_B: "e < m \<Longrightarrow> original_network.sndv (B e) = fst_list ! e" by simp

definition chain_redge :: "nat \<Rightarrow> nat Redge" where
  "chain_redge x = (if fst_list ! (ds_par (build_tree acyc_flow) ! x) = x
                    then F (ds_par (build_tree acyc_flow) ! x) else B (ds_par (build_tree acyc_flow) ! x))"

lemma chain_redge_props:
  assumes x: "x \<in> Vseen" and pd: "ds_prnt (build_tree acyc_flow) ! x < vcount"
  shows "original_network.oedge (chain_redge x) = ds_par (build_tree acyc_flow) ! x
       \<and> ds_par (build_tree acyc_flow) ! x < m
       \<and> is_free acyc_flow (ds_par (build_tree acyc_flow) ! x)
       \<and> original_network.fstv (chain_redge x) = x
       \<and> original_network.sndv (chain_redge x) = ds_prnt (build_tree acyc_flow) ! x
       \<and> chain_redge x \<in> original_network.\<EE>"
proof -
  let ?bt = "build_tree acyc_flow"
  let ?e = "ds_par ?bt ! x"
  have xlt: "x < vcount" and xseen: "ds_seen ?bt ! x" using x by (auto simp: Vseen_def)
  note bp = build_tree_par_edge[OF xlt xseen pd]
  have pe: "?e < m" using bp[THEN conjunct1] .
  have free: "is_free acyc_flow ?e" using bp[THEN conjunct2, THEN conjunct1] .
  have orient: "fst_list ! ?e = (if ds_dir ?bt ! x then x else ds_prnt ?bt ! x)"
    using bp[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1] .
  have orient2: "snd_list ! ?e = (if ds_dir ?bt ! x then ds_prnt ?bt ! x else x)"
    using bp[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2] .
  have pnx: "ds_prnt ?bt ! x \<noteq> x"
  proof
    assume "ds_prnt ?bt ! x = x"
    hence "(x, x) \<in> pstep ?bt" using xlt xseen by (auto simp: pstep_def)
    thus False using pstep_acyclic by (metis acyclic_def r_into_trancl)
  qed
  show ?thesis
  proof (cases "ds_dir ?bt ! x")
    case True
    have cr: "chain_redge x = F ?e" using True orient by (simp add: chain_redge_def)
    have oe: "original_network.oedge (chain_redge x) = ?e" by (simp add: cr)
    have fv: "original_network.fstv (chain_redge x) = x"
      using cr cr_fstv_F[OF pe] orient True by simp
    have sv: "original_network.sndv (chain_redge x) = ds_prnt ?bt ! x"
      using cr cr_sndv_F[OF pe] orient2 True by simp
    have ie: "chain_redge x \<in> original_network.\<EE>" using cr cr_inE_F[OF pe] by simp
    show ?thesis using oe pe free fv sv ie by simp
  next
    case False
    have fne: "fst_list ! ?e \<noteq> x" using False orient pnx by simp
    have cr: "chain_redge x = B ?e" using fne by (simp add: chain_redge_def)
    have oe: "original_network.oedge (chain_redge x) = ?e" by (simp add: cr)
    have fv: "original_network.fstv (chain_redge x) = x"
      using cr cr_fstv_B[OF pe] orient2 False by simp
    have sv: "original_network.sndv (chain_redge x) = ds_prnt ?bt ! x"
      using cr cr_sndv_B[OF pe] orient False by simp
    have ie: "chain_redge x \<in> original_network.\<EE>" using cr cr_inE_B[OF pe] by simp
    show ?thesis using oe pe free fv sv ie by simp
  qed
qed

text \<open>prepath plumbing: original\_network is only a flow\_network\_spec, so the flow\_network-level
      prepath\_intros are unavailable; op\_prepath\_single/cons rebuild the single-arc and cons introduction
      rules from prepath\_def and awalk\_Cons\_iff over the UNIV pair-graph. The walk-builder then turns a
      pstep-chain u {\isasymleadsto}* w to a real ancestor w into an interior free-real prepath from u to w (chain\_redge
      per step, oriented child{\isasymrightarrow}parent), tracking that its residual arcs are exactly the parent edges of
      the chain vertices --- hence distinct (par\_inj) and never equal to an uncovered edge.\<close>

lemma op_tvp: "original_network.to_vertex_pair e = (original_network.fstv e, original_network.sndv e)"
  by (cases e) (auto simp add: original_network.make_pair_def)

lemma dVs_UNIV_all: "(x::nat) \<in> dVs UNIV"
  by (auto simp: dVs_def)

lemma op_prepath_single: "original_network.prepath [e]"
  by (simp add: original_network.prepath_def op_tvp awalk_Cons_iff awalk_Nil_iff dVs_UNIV_all)

lemma op_prepath_cons:
  assumes "original_network.sndv e = original_network.fstv (hd p)" and "original_network.prepath p"
  shows "original_network.prepath (e # p)"
proof -
  obtain d es where p: "p = d # es" using assms(2) by (cases p) (auto simp: original_network.prepath_def)
  show ?thesis
    using assms
    by (auto simp: original_network.prepath_def op_tvp awalk_Cons_iff dVs_UNIV_all p)
qed

lemma pstep_chain_prepath:
  assumes uw: "(u, w) \<in> (pstep (build_tree acyc_flow))\<^sup>*" and wv: "w < vcount"
  shows "u = w \<or> (\<exists>C. C \<noteq> [] \<and> original_network.prepath C
     \<and> original_network.fstv (hd C) = u \<and> original_network.sndv (last C) = w
     \<and> (\<forall>a\<in>set C. original_network.oedge a < m \<and> is_free acyc_flow (original_network.oedge a))
     \<and> distinct (map original_network.oedge C)
     \<and> (\<forall>e'\<in>original_network.oedge ` set C. \<exists>y\<in>Vseen. e' = ds_par (build_tree acyc_flow) ! y
             \<and> (u,y) \<in> (pstep (build_tree acyc_flow))\<^sup>* \<and> (y,w) \<in> (pstep (build_tree acyc_flow))\<^sup>+))"
  using uw
proof (induct rule: converse_rtrancl_induct)
  case base
  show ?case by simp
next
  case (step a b)
  let ?bt = "build_tree acyc_flow"
  let ?P = "pstep ?bt"
  have ab: "(a, b) \<in> ?P" and bwstar: "(b, w) \<in> ?P\<^sup>*" by (rule step(1), rule step(2))
  have alt: "a < vcount" and aseen: "ds_seen ?bt ! a" and bpar: "b = ds_prnt ?bt ! a"
    using ab by (auto simp: pstep_def)
  have aV: "a \<in> Vseen" using alt aseen by (simp add: Vseen_def)
  have bv: "b < vcount"
  proof (rule ccontr)
    assume nb: "\<not> b < vcount"
    have "b = w"
    proof (rule converse_rtranclE[OF bwstar])
      show "b = w \<Longrightarrow> b = w" .
    next
      fix c assume "(b, c) \<in> ?P"
      hence "b < vcount" by (simp add: pstep_def)
      thus "b = w" using nb by simp
    qed
    thus False using nb wv by simp
  qed
  have bpd: "ds_prnt ?bt ! a < vcount" using bpar bv by simp
  note crp = chain_redge_props[OF aV bpd]
  have cr_oe: "original_network.oedge (chain_redge a) = ds_par ?bt ! a"
    using crp[THEN conjunct1] .
  have cr_pe: "ds_par ?bt ! a < m" using crp[THEN conjunct2, THEN conjunct1] .
  have cr_free: "is_free acyc_flow (ds_par ?bt ! a)"
    using crp[THEN conjunct2, THEN conjunct2, THEN conjunct1] .
  have cr_fv: "original_network.fstv (chain_redge a) = a"
    using crp[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1] .
  have cr_sv: "original_network.sndv (chain_redge a) = b"
    using crp[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN conjunct1] bpar by simp
  \<comment> \<open>freshness: ds\_par a is not among edges of any chain from b\<close>
  have fresh_helper: "\<And>y. y \<in> Vseen \<Longrightarrow> (b,y) \<in> ?P\<^sup>* \<Longrightarrow> ds_par ?bt ! y \<noteq> ds_par ?bt ! a"
  proof -
    fix y assume yseen: "y \<in> Vseen" and by_: "(b,y) \<in> ?P\<^sup>*"
    show "ds_par ?bt ! y \<noteq> ds_par ?bt ! a"
    proof
      assume eq: "ds_par ?bt ! y = ds_par ?bt ! a"
      have "y = a" using par_inj[OF yseen aV] eq by simp
      hence "(a,a) \<in> ?P\<^sup>+" using rtrancl_into_trancl2[OF ab] by_ by simp
      thus False using pstep_acyclic by (simp add: acyclic_def)
    qed
  qed
  show ?case
  proof (cases "b = w")
    case True
    have aw: "(a, w) \<in> ?P\<^sup>+" using ab True by (simp add: r_into_trancl)
    have pp: "original_network.prepath [chain_redge a]" by (rule op_prepath_single)
    have "\<forall>e'\<in>original_network.oedge ` set [chain_redge a]. \<exists>y\<in>Vseen. e' = ds_par ?bt ! y
             \<and> (a,y) \<in> ?P\<^sup>* \<and> (y,w) \<in> ?P\<^sup>+"
      using cr_oe aV aw by auto
    hence "[chain_redge a] \<noteq> [] \<and> original_network.prepath [chain_redge a]
       \<and> original_network.fstv (hd [chain_redge a]) = a \<and> original_network.sndv (last [chain_redge a]) = w
       \<and> (\<forall>aa\<in>set [chain_redge a]. original_network.oedge aa < m \<and> is_free acyc_flow (original_network.oedge aa))
       \<and> distinct (map original_network.oedge [chain_redge a])
       \<and> (\<forall>e'\<in>original_network.oedge ` set [chain_redge a]. \<exists>y\<in>Vseen. e' = ds_par ?bt ! y
             \<and> (a,y) \<in> ?P\<^sup>* \<and> (y,w) \<in> ?P\<^sup>+)"
      using pp cr_oe cr_pe cr_free cr_fv cr_sv True by simp
    thus ?thesis by blast
  next
    case False
    with step(3) obtain C where C: "C \<noteq> []" "original_network.prepath C"
      "original_network.fstv (hd C) = b" "original_network.sndv (last C) = w"
      "\<forall>aa\<in>set C. original_network.oedge aa < m \<and> is_free acyc_flow (original_network.oedge aa)"
      "distinct (map original_network.oedge C)"
      "\<forall>e'\<in>original_network.oedge ` set C. \<exists>y\<in>Vseen. e' = ds_par ?bt ! y \<and> (b,y) \<in> ?P\<^sup>* \<and> (y,w) \<in> ?P\<^sup>+"
      by blast
    have sf: "original_network.sndv (chain_redge a) = original_network.fstv (hd C)"
      using cr_sv C(3) by simp
    have pp: "original_network.prepath (chain_redge a # C)"
      by (rule op_prepath_cons[OF sf C(2)])
    have fresh: "ds_par ?bt ! a \<notin> original_network.oedge ` set C"
    proof
      assume "ds_par ?bt ! a \<in> original_network.oedge ` set C"
      then obtain y where yy: "y \<in> Vseen" "ds_par ?bt ! a = ds_par ?bt ! y" "(b,y) \<in> ?P\<^sup>*"
        using C(7) by blast
      thus False using fresh_helper[OF yy(1) yy(3)] by simp
    qed
    have hC: "original_network.fstv (hd (chain_redge a # C)) = a" using cr_fv by simp
    have lC: "original_network.sndv (last (chain_redge a # C)) = w" using C(1) C(4) by simp
    have edgesC: "\<forall>aa\<in>set (chain_redge a # C). original_network.oedge aa < m \<and> is_free acyc_flow (original_network.oedge aa)"
      using cr_oe cr_pe cr_free C(5) by auto
    have distC: "distinct (map original_network.oedge (chain_redge a # C))"
      using C(6) fresh cr_oe by simp
    have coverC: "\<forall>e'\<in>original_network.oedge ` set (chain_redge a # C). \<exists>y\<in>Vseen. e' = ds_par ?bt ! y
             \<and> (a,y) \<in> ?P\<^sup>* \<and> (y,w) \<in> ?P\<^sup>+"
    proof
      fix e' assume "e' \<in> original_network.oedge ` set (chain_redge a # C)"
      hence "e' = ds_par ?bt ! a \<or> e' \<in> original_network.oedge ` set C" using cr_oe by auto
      thus "\<exists>y\<in>Vseen. e' = ds_par ?bt ! y \<and> (a,y) \<in> ?P\<^sup>* \<and> (y,w) \<in> ?P\<^sup>+"
      proof
        assume "e' = ds_par ?bt ! a"
        moreover have "(a, w) \<in> ?P\<^sup>+" using ab bwstar by (simp add: rtrancl_into_trancl2)
        ultimately show ?thesis using aV by auto
      next
        assume "e' \<in> original_network.oedge ` set C"
        then obtain y where "y\<in>Vseen" "e' = ds_par ?bt ! y" "(b,y) \<in> ?P\<^sup>*" "(y,w) \<in> ?P\<^sup>+"
          using C(7) by blast
        moreover have "(a,y) \<in> ?P\<^sup>*" using ab \<open>(b,y) \<in> ?P\<^sup>*\<close> by (simp add: converse_rtrancl_into_rtrancl)
        ultimately show ?thesis by blast
      qed
    qed
    have "chain_redge a # C \<noteq> [] \<and> original_network.prepath (chain_redge a # C)
       \<and> original_network.fstv (hd (chain_redge a # C)) = a \<and> original_network.sndv (last (chain_redge a # C)) = w
       \<and> (\<forall>aa\<in>set (chain_redge a # C). original_network.oedge aa < m \<and> is_free acyc_flow (original_network.oedge aa))
       \<and> distinct (map original_network.oedge (chain_redge a # C))
       \<and> (\<forall>e'\<in>original_network.oedge ` set (chain_redge a # C). \<exists>y\<in>Vseen. e' = ds_par ?bt ! y
             \<and> (a,y) \<in> ?P\<^sup>* \<and> (y,w) \<in> ?P\<^sup>+)"
      using pp hC lC edgesC distC coverC by simp
    thus ?thesis by blast
  qed
qed

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
  assumes sc: "scan_complete s"
    and em: "e < m" and free: "is_free acyc_flow e"
    and wns: "\<not> ds_seen s ! w"
    and aseen: "ds_seen s ! a"
    and inc: "(fst_list ! e = a \<and> snd_list ! e = w) \<or> (fst_list ! e = w \<and> snd_list ! e = a)"
  shows "a \<in> stkverts s"
  unfolding stkverts_def
proof (rule ccontr)
  assume ans: "a \<notin> set (ds_stk s)"
  have avc: "a < vcount" using inc fst_list_lt[OF em] snd_list_lt[OF em] by auto
  show False using inc scan_complete_finished[OF sc avc aseen ans em free] wns by auto
qed

lemma covinv_cong:
  assumes s: "ds_seen s = ds_seen t" and p: "ds_prnt s = ds_prnt t" and ci: "covinv s"
  shows "covinv t"
proof -
  have eq: "pstep t = pstep s" using pstep_cong[OF p s] by simp
  show ?thesis using ci unfolding covinv_def eq s .
qed

lemma discover_prnt_eq: "ds_prnt (dfs_discover s v w e) = (ds_prnt s)[w := v]"
  by (simp add: dfs_discover_def dfs_push_def Let_def)

text \<open>One scan step from the stack top v along the free edge e to w: if w is new, it becomes v's
      child, and a seen free neighbour of w is on the stack (@{thm free_neighbor_on_stack}), hence an
      ancestor of v (@{thm stk_top_reaches}).\<close>

lemma covinv_step:
  assumes wf: "dfs_wf acyc_flow s" and sz: "dfs_sized s" and sc: "scan_complete s" and ci: "covinv s"
    and spi: "stk_prnt_inv s" and stk: "ds_stk s = v # rest"
    and em: "e < m" and free: "is_free acyc_flow e"
    and econn: "(fst_list ! e = v \<and> snd_list ! e = w) \<or> (fst_list ! e = w \<and> snd_list ! e = v)"
    and wvc: "w < vcount"
    and s': "ds_seen s' = ds_seen s" "ds_prnt s' = ds_prnt s"
  shows "covinv (if ds_seen s ! w then s' else dfs_discover s' v w e)"
proof (cases "ds_seen s ! w")
  case True
  thus ?thesis using covinv_cong[OF s'(1)[symmetric] s'(2)[symmetric] ci] by simp
next
  case wns: False
  let ?t = "dfs_discover s' v w e"
  have seent: "ds_seen ?t = (ds_seen s)[w := True]" using s' by (simp add: discover_seen_eq)
  have prntt: "ds_prnt ?t = (ds_prnt s)[w := v]" using s' by (simp add: discover_prnt_eq)
  have lseen: "length (ds_seen s) = Suc vcount" and lprnt: "length (ds_prnt s) = Suc vcount"
    using sz by (auto simp: dfs_sized_def)
  have pstept: "pstep ?t = insert (w, v) (pstep s)"
    by (rule pstep_upd[OF prntt seent wvc wns lseen lprnt])
  have mono: "pstep s \<subseteq> pstep ?t" using pstept by auto
  have wvpair: "(w, v) \<in> pstep ?t" using pstept by simp
  have tne: "\<And>x. x \<noteq> w \<Longrightarrow> ds_seen ?t ! x = ds_seen s ! x" using seent by (simp add: nth_list_update_neq)
  have anc: "(w, a) \<in> (pstep ?t)\<^sup>*" if sa: "ds_seen s ! a" and dm: "d < m" and dfree: "is_free acyc_flow d"
    and inc: "(fst_list ! d = a \<and> snd_list ! d = w) \<or> (fst_list ! d = w \<and> snd_list ! d = a)" for a d
  proof -
    have "(v, a) \<in> (pstep s)\<^sup>*"
      by (rule stk_top_reaches[OF spi wf stk free_neighbor_on_stack[OF sc dm dfree wns sa inc]])
    hence "(v, a) \<in> (pstep ?t)\<^sup>*" using mono rtrancl_mono by blast
    thus ?thesis using wvpair by (simp add: converse_rtrancl_into_rtrancl)
  qed
  show ?thesis
    unfolding if_not_P[OF wns] covinv_def
  proof (intro allI impI)
    fix d assume dm: "d < m" and dfree: "is_free acyc_flow d"
      and sa: "ds_seen ?t ! (fst_list ! d)" and sb: "ds_seen ?t ! (snd_list ! d)"
    let ?a = "fst_list ! d" and ?b = "snd_list ! d"
    show "(?a, ?b) \<in> (pstep ?t)\<^sup>* \<or> (?b, ?a) \<in> (pstep ?t)\<^sup>*"
    proof (cases "?a = w")
      case aw: True
      show ?thesis
      proof (cases "?b = w")
        case True thus ?thesis using aw by simp
      next
        case False
        hence "ds_seen s ! ?b" using sb tne by simp
        thus ?thesis using anc[OF _ dm dfree] aw by simp
      qed
    next
      case anw: False
      hence sas: "ds_seen s ! ?a" using sa tne by simp
      show ?thesis
      proof (cases "?b = w")
        case True thus ?thesis using anc[OF sas dm dfree] by simp
      next
        case False
        hence "ds_seen s ! ?b" using sb tne by simp
        hence "(?a, ?b) \<in> (pstep s)\<^sup>* \<or> (?b, ?a) \<in> (pstep s)\<^sup>*"
          using ci dm dfree sas by (simp add: covinv_def)
        thus ?thesis using mono rtrancl_mono by blast
      qed
    qed
  qed
qed

text \<open>covinv is threaded through the builder jointly with scan\_complete, which its scan step needs.\<close>

lemma build_dfs_sc_cv:
  assumes inv: "dfs_inv acyc_flow s" and sc: "scan_complete s" and ci: "covinv s"
  shows "scan_complete (build_dfs acyc_flow s) \<and> covinv (build_dfs acyc_flow s)"
proof -
  have "fl = acyc_flow \<longrightarrow> dfs_inv fl s \<longrightarrow> scan_complete s \<and> covinv s
          \<longrightarrow> scan_complete (build_dfs fl s) \<and> covinv (build_dfs fl s)"
    if "build_dfs_dom (fl, s)" for fl s
  proof (induct rule: bd_induct[OF that])
    case IH: (1 fl s)
    show ?case
    proof (intro impI, elim conjE)
      assume fl: "fl = acyc_flow" and inv: "dfs_inv fl s" and sc: "scan_complete s" and ci: "covinv s"
      have wf: "dfs_wf acyc_flow s" and sz: "dfs_sized s" and spi: "stk_prnt_inv s"
        using inv fl by (simp_all add: dfs_inv_def)
      show "scan_complete (build_dfs fl s) \<and> covinv (build_dfs fl s)"
      proof (rule bd_cases[where s = s and fl = fl])
        assume c: "bd_call1_conds fl s"
        obtain v rest e w c' where stk: "ds_stk s = v # rest" and em: "e < m" and fe: "fst_list ! e = v"
          and se: "snd_list ! e = w" and free: "is_free acyc_flow e" and wvc: "w < vcount"
          and up: "bd_upd1 acyc_flow s = (if ds_seen s ! w then s\<lparr>ds_oc := c'\<rparr> else dfs_discover (s\<lparr>ds_oc := c'\<rparr>) v w e)"
          using wf c fl by (auto elim: bd_upd1_eq)
        have "covinv (bd_upd1 acyc_flow s)" unfolding up
          by (rule covinv_step[OF wf sz sc ci spi stk em free]) (use fe se wvc in simp_all)
        moreover have "scan_complete (bd_upd1 acyc_flow s)" using bd_upd1_scan_complete inv sc c fl by simp
        moreover have "build_dfs fl s = build_dfs fl (bd_upd1 fl s)" using IH(1) c by (rule bd_simps(1))
        ultimately show ?thesis using IH(2)[OF c] bd_upd1_inv[OF inv c] fl by simp
      next
        assume c: "bd_call2_conds fl s"
        obtain v rest e w c' where stk: "ds_stk s = v # rest" and em: "e < m" and se: "snd_list ! e = v"
          and fe: "fst_list ! e = w" and free: "is_free acyc_flow e" and wvc: "w < vcount"
          and up: "bd_upd2 acyc_flow s = (if ds_seen s ! w then s\<lparr>ds_ic := c'\<rparr> else dfs_discover (s\<lparr>ds_ic := c'\<rparr>) v w e)"
          using wf c fl by (auto elim: bd_upd2_eq)
        have "covinv (bd_upd2 acyc_flow s)" unfolding up
          by (rule covinv_step[OF wf sz sc ci spi stk em free]) (use fe se wvc in simp_all)
        moreover have "scan_complete (bd_upd2 acyc_flow s)" using bd_upd2_scan_complete inv sc c fl by simp
        moreover have "build_dfs fl s = build_dfs fl (bd_upd2 fl s)" using IH(1) c by (rule bd_simps(2))
        ultimately show ?thesis using IH(3)[OF c] bd_upd2_inv[OF inv c] fl by simp
      next
        assume c: "bd_call3_conds fl s"
        obtain v rest where up: "bd_upd3 s = dfs_finish s v rest" by (rule bd_upd3_eq[OF c])
        have "covinv (bd_upd3 s)" by (rule covinv_cong[OF _ _ ci]) (simp_all add: up dfs_finish_def Let_def)
        moreover have "scan_complete (bd_upd3 s)" using bd_upd3_scan_complete inv sc c fl by simp
        moreover have "build_dfs fl s = build_dfs fl (bd_upd3 s)" using IH(1) c by (rule bd_simps(3))
        ultimately show ?thesis using IH(4)[OF c] bd_upd3_inv[OF inv c] fl by simp
      next
        assume c: "bd_ret_conds s"
        have "build_dfs fl s = s" using IH(1) c by (rule bd_simps(4))
        thus ?thesis using sc ci by simp
      qed
    qed
  qed
  moreover have "build_dfs_dom (acyc_flow, s)" using inv by (simp add: dfs_inv_def build_dfs_dom_wf)
  ultimately show ?thesis using inv sc ci by blast
qed

text \<open>The component-root seed adds no comparability obligation: a seen free neighbour of the fresh
      root would be on the empty stack.\<close>

lemma open_tree_component_sc_cv:
  assumes inv: "dfs_inv acyc_flow s" and sc: "scan_complete s" and ci: "covinv s" and c: "c < vcount"
      and unseen: "\<not> ds_seen s ! c" and cnz: "c \<noteq> 0" and stke: "ds_stk s = []"
  shows "scan_complete (open_tree_component acyc_flow s c) \<and> covinv (open_tree_component acyc_flow s c)"
proof -
  have sz: "dfs_sized s" using inv by (simp add: dfs_inv_def)
  have "dfs_wf acyc_flow s" using inv by (simp add: dfs_inv_def)
  then obtain sd where opd: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd"
    and I: "(dfs_inv acyc_flow s \<and> \<not> ds_seen s ! c \<and> c \<noteq> 0 \<and> ds_stk s = []) \<longrightarrow> dfs_inv acyc_flow sd"
    and stk: "ds_stk sd = [c]" and oc: "ds_oc sd = ds_oc (dfs_push s c)" and ic: "ds_ic sd = ds_ic (dfs_push s c)"
    and seen: "ds_seen sd = (ds_seen s)[c := True]" and prnt: "ds_prnt sd = (ds_prnt s)[c := vcount]"
    using sz c by (rule open_tree_component_seed)
  have lseen: "length (ds_seen s) = Suc vcount" and lprnt: "length (ds_prnt s) = Suc vcount"
    using sz by (auto simp: dfs_sized_def)
  note P = dfs_push_remaining[OF c]
  have toc: "csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc sd) j
      = (if j = c then {e. e < m \<and> fst_list ! e = c \<and> is_free acyc_flow e}
         else csr_ranges.csr_remaining ((!) (fst (free_out acyc_flow))) (snd (free_out acyc_flow)) (ds_oc s) j)" for j
    using oc P(1,3) by (cases "j = c") simp_all
  have tic: "csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic sd) j
      = (if j = c then {e. e < m \<and> snd_list ! e = c \<and> is_free acyc_flow e}
         else csr_ranges.csr_remaining ((!) (fst (free_in acyc_flow))) (snd (free_in acyc_flow)) (ds_ic s) j)" for j
    using ic P(2,4) by (cases "j = c") simp_all
  have scd: "scan_complete sd"
    by (rule scan_complete_upd[OF sc])
       (use stke c unseen lseen in \<open>auto simp: stk toc tic seen nth_list_update split: if_splits\<close>)
  have mono: "pstep s \<subseteq> pstep sd" using pstep_upd[OF prnt seen c unseen lseen lprnt] by auto
  have sne: "\<And>x. x \<noteq> c \<Longrightarrow> ds_seen sd ! x = ds_seen s ! x" using seen by (simp add: nth_list_update_neq)
  have nb: "\<not> ds_seen s ! a"
    if "d < m" "is_free acyc_flow d" "(fst_list ! d = a \<and> snd_list ! d = c) \<or> (fst_list ! d = c \<and> snd_list ! d = a)"
    for a d
    using free_neighbor_on_stack[OF sc that(1,2) unseen _ that(3)] stke by (auto simp: stkverts_def)
  have cvd: "covinv sd"
    unfolding covinv_def
  proof (intro allI impI)
    fix d assume dm: "d < m" and dfree: "is_free acyc_flow d"
      and sa: "ds_seen sd ! (fst_list ! d)" and sb: "ds_seen sd ! (snd_list ! d)"
    show "(fst_list ! d, snd_list ! d) \<in> (pstep sd)\<^sup>* \<or> (snd_list ! d, fst_list ! d) \<in> (pstep sd)\<^sup>*"
    proof (cases "fst_list ! d = c \<or> snd_list ! d = c")
      case True
      thus ?thesis using nb[OF dm dfree, of "fst_list ! d"] nb[OF dm dfree, of "snd_list ! d"] sa sb sne
        by (cases "fst_list ! d = snd_list ! d") auto
    next
      case False
      hence "(fst_list ! d, snd_list ! d) \<in> (pstep s)\<^sup>* \<or> (snd_list ! d, fst_list ! d) \<in> (pstep s)\<^sup>*"
        using ci dm dfree sa sb sne by (simp add: covinv_def)
      thus ?thesis using mono rtrancl_mono by blast
    qed
  qed
  show ?thesis unfolding opd using build_dfs_sc_cv[OF _ scd cvd] I inv unseen cnz stke by blast
qed

lemma emit_U_edge_covinv:
  assumes "covinv s" shows "covinv (emit_U_edge s v)"
proof (rule covinv_cong[OF _ _ assms])
  show "ds_seen s = ds_seen (emit_U_edge s v)" by (simp add: emit_U_edge_def Let_def)
  show "ds_prnt s = ds_prnt (emit_U_edge s v)" by (simp add: emit_U_edge_def Let_def)
qed

lemma phase1_step_sc_cv:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []"
    and sc: "scan_complete s" and ci: "covinv s"
  shows "scan_complete (phase1_step acyc_flow v s) \<and> covinv (phase1_step acyc_flow v s)"
proof -
  have vlt: "v < vcount" using vs_less_vcount[OF v] .
  have vnz: "v \<noteq> 0" using v no_zero_node by metis
  show ?thesis
    using open_tree_component_sc_cv[OF inv sc ci vlt _ vnz stke] sc ci emit_U_edge_covinv[OF ci]
    by (simp add: phase1_step_def emit_U_edge_scan_complete)
qed

lemma phase2_step_sc_cv:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []"
    and sc: "scan_complete s" and ci: "covinv s"
  shows "scan_complete (phase2_step acyc_flow v s) \<and> covinv (phase2_step acyc_flow v s)"
proof -
  have vlt: "v < vcount" using vs_less_vcount[OF v] .
  have vnz: "v \<noteq> 0" using v no_zero_node by metis
  show ?thesis
    using open_tree_component_sc_cv[OF inv sc ci vlt _ vnz stke] sc ci by (simp add: phase2_step_def)
qed

lemma covinv_dfs_init: "covinv dfs_init"
  unfolding covinv_def
proof (intro allI impI)
  fix e assume em: "e < m" and "is_free acyc_flow e" and se: "ds_seen dfs_init ! (fst_list ! e)"
  have "fst_list ! e < vcount" using vs_less_vcount[OF fst_list_nth_vertex[OF em]] .
  hence "\<not> ds_seen dfs_init ! (fst_list ! e)" by (simp add: dfs_init_def del: replicate_Suc)
  thus "(fst_list ! e, snd_list ! e) \<in> (pstep dfs_init)\<^sup>* \<or> (snd_list ! e, fst_list ! e) \<in> (pstep dfs_init)\<^sup>*"
    using se by simp
qed

lemma build_tree_covinv: "covinv (build_tree acyc_flow)"
proof -
  let ?P = "\<lambda>s. (dfs_inv acyc_flow s \<and> ds_stk s = []) \<and> scan_complete s \<and> covinv s"
  have i0: "dfs_inv acyc_flow dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have s0: "scan_complete dfs_init" by (simp add: scan_complete_def dfs_init_def del: replicate_Suc)
  have p1: "?P (phase1 acyc_flow dfs_init)"
    unfolding phase1_def
    by (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = ?P])
       (use i0 s0 covinv_dfs_init phase1_step_inv phase1_step_sc_cv in auto)
  have "?P (phase2 acyc_flow (phase1 acyc_flow dfs_init))"
    unfolding phase2_def
    by (rule fold_invariant[where Q = "\<lambda>v. v \<in> set vs_list" and P = ?P])
       (use p1 phase2_step_inv phase2_step_sc_cv in auto)
  thus ?thesis by (simp add: build_tree_def Let_def covinv_def pstep_def)
qed

subsection \<open>Free-edge coverage: every free real edge is a tree (parent) edge\<close>

text \<open>The payoff of covinv + the walk-builder + the acyclicity engine: an uncovered free real edge e,
      with both endpoints seen (build\_tree\_spans) and pstep-comparable (build\_tree\_covinv), would close a
      free residual cycle (the tree chain between its endpoints plus e), contradicting acyclicity. Hence
      e is a parent edge. Needs acyclic\_flow (nth acyc\_flow), delivered on the Some branch by acyc\_of\_some.\<close>

lemma redge_in_E: "original_network.oedge a < m \<Longrightarrow> a \<in> original_network.\<EE>"
  by (cases a) (auto simp: original_network.\<EE>_def)

lemma cycle_contra:
  assumes acyc: "original_network.acyclic_flow (h \<circ> nth acyc_flow)"
    and ab: "(a, b) \<in> (pstep (build_tree acyc_flow))\<^sup>*" and bv: "b < vcount"
    and re_fv: "original_network.fstv re = b" and re_sv: "original_network.sndv re = a"
    and re_oe: "original_network.oedge re = e" and em: "e < m" and free: "is_free acyc_flow e"
    and notcov: "\<And>v. v \<in> Vseen \<Longrightarrow> ds_par (build_tree acyc_flow) ! v \<noteq> e"
  shows False
proof -
  have reE: "re \<in> original_network.\<EE>" using re_oe em by (simp add: redge_in_E)
  have refree: "original_network.oedge re < m \<and> is_free acyc_flow (original_network.oedge re)"
    using re_oe em free by simp
  from pstep_chain_prepath[OF ab bv] show False
  proof
    assume "a = b"
    have cl: "original_network.fstv (hd [re]) = original_network.sndv (last [re])"
      using re_fv re_sv \<open>a = b\<close> by simp
    show False
      by (rule free_walk_no_cycle[OF acyc _ _ _ _ op_prepath_single cl])
         (use reE refree in \<open>auto\<close>)
  next
    assume "\<exists>C. C \<noteq> [] \<and> original_network.prepath C
       \<and> original_network.fstv (hd C) = a \<and> original_network.sndv (last C) = b
       \<and> (\<forall>x\<in>set C. original_network.oedge x < m \<and> is_free acyc_flow (original_network.oedge x))
       \<and> distinct (map original_network.oedge C)
       \<and> (\<forall>e'\<in>original_network.oedge ` set C. \<exists>y\<in>Vseen. e' = ds_par (build_tree acyc_flow) ! y
             \<and> (a,y) \<in> (pstep (build_tree acyc_flow))\<^sup>* \<and> (y,b) \<in> (pstep (build_tree acyc_flow))\<^sup>+)"
    then obtain C where C: "C \<noteq> []" "original_network.prepath C"
      "original_network.fstv (hd C) = a" "original_network.sndv (last C) = b"
      "\<forall>x\<in>set C. original_network.oedge x < m \<and> is_free acyc_flow (original_network.oedge x)"
      "distinct (map original_network.oedge C)"
      "\<forall>e'\<in>original_network.oedge ` set C. \<exists>y\<in>Vseen. e' = ds_par (build_tree acyc_flow) ! y
             \<and> (a,y) \<in> (pstep (build_tree acyc_flow))\<^sup>* \<and> (y,b) \<in> (pstep (build_tree acyc_flow))\<^sup>+"
      by blast
    let ?C = "re # C"
    have pp: "original_network.prepath ?C"
      by (rule op_prepath_cons) (use re_sv C(2,3) in simp_all)
    have hd_last: "original_network.fstv (hd ?C) = original_network.sndv (last ?C)"
      using re_fv C(1,4) by simp
    have enotC: "e \<notin> original_network.oedge ` set C"
    proof
      assume "e \<in> original_network.oedge ` set C"
      then obtain y where "y \<in> Vseen" "e = ds_par (build_tree acyc_flow) ! y" using C(7) by blast
      thus False using notcov by auto
    qed
    have dist: "distinct (map original_network.oedge ?C)" using C(6) enotC re_oe by simp
    have edges: "\<And>x. x \<in> set ?C \<Longrightarrow> original_network.oedge x < m \<and> is_free acyc_flow (original_network.oedge x)"
      using C(5) refree by auto
    have sub: "set ?C \<subseteq> original_network.\<EE>" using reE C(5) redge_in_E by auto
    show False
      by (rule free_walk_no_cycle[OF acyc _ edges dist sub pp hd_last]) simp
  qed
qed

lemma free_edge_covered:
  assumes acyc: "original_network.acyclic_flow (h \<circ> nth acyc_flow)"
    and em: "e < m" and free: "is_free acyc_flow e"
  shows "\<exists>v \<in> Vseen. ds_par (build_tree acyc_flow) ! v = e"
proof (rule ccontr)
  assume nc: "\<not> (\<exists>v \<in> Vseen. ds_par (build_tree acyc_flow) ! v = e)"
  hence notcov: "\<And>v. v \<in> Vseen \<Longrightarrow> ds_par (build_tree acyc_flow) ! v \<noteq> e" by auto
  let ?u = "fst_list ! e" and ?w = "snd_list ! e"
  have ue: "?u \<in> set fst_list" using em by (metis length_fst_list_m nth_mem)
  have we: "?w \<in> set snd_list" using em by (metis length_snd_list_m nth_mem)
  have uV: "?u \<in> Vseen" and wV: "?w \<in> Vseen" using ue we Vseen_eq_V V_orig_eq by auto
  have uv: "?u < vcount" and wv: "?w < vcount" using uV wV by (auto simp: Vseen_def)
  have us: "ds_seen (build_tree acyc_flow) ! ?u" and ws: "ds_seen (build_tree acyc_flow) ! ?w"
    using uV wV by (auto simp: Vseen_def)
  have cmp: "(?u, ?w) \<in> (pstep (build_tree acyc_flow))\<^sup>* \<or> (?w, ?u) \<in> (pstep (build_tree acyc_flow))\<^sup>*"
    using build_tree_covinv em free us ws by (simp add: covinv_def)
  have fF: "original_network.fstv (F e) = ?u" and sF: "original_network.sndv (F e) = ?w"
    and fB: "original_network.fstv (B e) = ?w" and sB: "original_network.sndv (B e) = ?u"
    using em by (simp_all add: cr_fstv_F cr_sndv_F cr_fstv_B cr_sndv_B)
  from cmp show False
  proof
    assume "(?u, ?w) \<in> (pstep (build_tree acyc_flow))\<^sup>*"
    show False
      by (rule cycle_contra[OF acyc \<open>(?u,?w)\<in>_\<close> wv fB sB _ em free notcov]) simp
  next
    assume "(?w, ?u) \<in> (pstep (build_tree acyc_flow))\<^sup>*"
    show False
      by (rule cycle_contra[OF acyc \<open>(?w,?u)\<in>_\<close> uv fF sF _ em free notcov]) simp
  qed
qed

subsection \<open>Artificial-edge reverse coverage: every artificial InTree edge is a component-root's edge\<close>

text \<open>art\_owned: for every emitted artificial slot k with tag InTree there is a component root c
      (\<open>ds_prnt c = vcount\<close>) whose parent edge is exactly that slot (\<open>ds_par c = m + k\<close>). This is the
      reverse of cr\_ext\_inv and completes InTree {\isasymsubseteq} T for the artificial range. Threaded like the forward
      cr\_ext machinery: build\_dfs adds no InTree artificial edge and freezes seen roots
      (build\_dfs\_frozen), open\_tree\_component installs the new
      root's witness, emit\_U\_edge only adds an InU edge, and the two phase folds carry it with the same
      ds\_nxt {\isasymle} length vs\_list bound (card of a seen-vertex witness set).\<close>

definition art_owned :: "'n dfs_state \<Rightarrow> bool" where
  "art_owned s \<longleftrightarrow> (\<forall>k < ds_nxt s. ds_aest s ! k = InTree \<longrightarrow>
      (\<exists>c<vcount. ds_seen s ! c \<and> ds_prnt s ! c = vcount \<and> ds_par s ! c = m + k))"

lemma build_dfs_art_owned:
  assumes dom: "build_dfs_dom (fl, s)" and inv: "dfs_inv fl s" and ao: "art_owned s"
  shows "art_owned (build_dfs fl s)"
proof -
  have aest: "ds_aest (build_dfs fl s) = ds_aest s" and nxt: "ds_nxt (build_dfs fl s) = ds_nxt s"
    using build_dfs_art[of fl s] dom by simp_all
  show ?thesis
    unfolding art_owned_def
  proof (intro allI impI)
    fix k assume klt: "k < ds_nxt (build_dfs fl s)" and kIT: "ds_aest (build_dfs fl s) ! k = InTree"
    have ks: "k < ds_nxt s" using klt nxt by simp
    have kITs: "ds_aest s ! k = InTree" using kIT aest by simp
    obtain c where c: "c < vcount" "ds_seen s ! c" "ds_prnt s ! c = vcount" "ds_par s ! c = m + k"
      using ao ks kITs by (auto simp: art_owned_def)
    have scb: "ds_seen (build_dfs fl s) ! c" using build_dfs_seen_mono[OF dom c(2)] .
    have "ds_prnt (build_dfs fl s) ! c = ds_prnt s ! c \<and> ds_par (build_dfs fl s) ! c = ds_par s ! c"
      using build_dfs_frozen[OF dom inv c(2)] by simp
    hence "ds_prnt (build_dfs fl s) ! c = vcount" "ds_par (build_dfs fl s) ! c = m + k"
      using c(3,4) by simp_all
    thus "\<exists>c<vcount. ds_seen (build_dfs fl s) ! c \<and> ds_prnt (build_dfs fl s) ! c = vcount \<and> ds_par (build_dfs fl s) ! c = m + k"
      using c(1) scb by blast
  qed
qed

lemma emit_U_edge_art_owned:
  assumes ao: "art_owned s" and al: "art_len s" and inb: "ds_nxt s < length vs_list"
  shows "art_owned (emit_U_edge s v)"
proof -
  have laest: "length (ds_aest s) = length vs_list" using al by (simp add: art_len_def)
  have seq: "ds_seen (emit_U_edge s v) = ds_seen s" "ds_prnt (emit_U_edge s v) = ds_prnt s"
       "ds_par (emit_U_edge s v) = ds_par s"
    by (simp_all add: emit_U_edge_def Let_def)
  show ?thesis
    unfolding art_owned_def
  proof (intro allI impI)
    fix k assume klt: "k < ds_nxt (emit_U_edge s v)" and kIT: "ds_aest (emit_U_edge s v) ! k = InTree"
    have klt': "k < Suc (ds_nxt s)" using klt by (simp add: emit_U_edge_nxt)
    have "k < ds_nxt s"
    proof (rule ccontr)
      assume "\<not> k < ds_nxt s"
      hence keq: "k = ds_nxt s" using klt' by simp
      have "ds_aest (emit_U_edge s v) ! k = InU"
        using keq inb laest by (simp add: emit_U_edge_def Let_def nth_list_update_eq)
      thus False using kIT by simp
    qed
    hence ks: "k < ds_nxt s" .
    have kITs: "ds_aest s ! k = InTree"
      using kIT ks by (simp add: emit_U_edge_def Let_def nth_list_update_neq)
    obtain c where c: "c < vcount" "ds_seen s ! c" "ds_prnt s ! c = vcount" "ds_par s ! c = m + k"
      using ao ks kITs by (auto simp: art_owned_def)
    show "\<exists>c<vcount. ds_seen (emit_U_edge s v) ! c \<and> ds_prnt (emit_U_edge s v) ! c = vcount \<and> ds_par (emit_U_edge s v) ! c = m + k"
      using c seq by auto
  qed
qed

lemma open_tree_component_art_owned:
  assumes inv: "dfs_inv acyc_flow s" and ao: "art_owned s" and c: "c < vcount"
    and unseen: "\<not> ds_seen s ! c" and cnz: "c \<noteq> 0" and stke: "ds_stk s = []"
    and al: "art_len s" and inb: "ds_nxt s < length vs_list"
  shows "art_owned (open_tree_component acyc_flow s c)"
proof -
  have "dfs_wf acyc_flow s" "dfs_sized s" using inv by (simp_all add: dfs_inv_def)
  then obtain sd where opd: "open_tree_component acyc_flow s c = build_dfs acyc_flow sd"
      and dom: "build_dfs_dom (acyc_flow, sd)"
      and I: "(dfs_inv acyc_flow s \<and> \<not> ds_seen s ! c \<and> c \<noteq> 0 \<and> ds_stk s = []) \<longrightarrow> dfs_inv acyc_flow sd"
      and nxtsd: "ds_nxt sd = Suc (ds_nxt s)"
      and seensd: "ds_seen sd = (ds_seen s)[c := True]" and prntsd: "ds_prnt sd = (ds_prnt s)[c := vcount]"
      and parsd: "ds_par sd = (ds_par s)[c := m + ds_nxt s]" and aestsd: "ds_aest sd = (ds_aest s)[ds_nxt s := InTree]"
    using c by (rule open_tree_component_seed)
  have invsd: "dfs_inv acyc_flow sd" using I inv unseen cnz stke by blast
  have lseen: "length (ds_seen s) = Suc vcount" and lprnt: "length (ds_prnt s) = Suc vcount"
       and lpar: "length (ds_par s) = Suc vcount" using inv by (simp_all add: dfs_inv_def dfs_sized_def)
  have laest: "length (ds_aest s) = length vs_list" using al by (simp add: art_len_def)
  have aosd: "art_owned sd"
    unfolding art_owned_def
  proof (intro allI impI)
    fix k assume klt: "k < ds_nxt sd" and kIT: "ds_aest sd ! k = InTree"
    have klt': "k < Suc (ds_nxt s)" using klt nxtsd by simp
    show "\<exists>c'<vcount. ds_seen sd ! c' \<and> ds_prnt sd ! c' = vcount \<and> ds_par sd ! c' = m + k"
    proof (cases "k = ds_nxt s")
      case True
      have "ds_seen sd ! c \<and> ds_prnt sd ! c = vcount \<and> ds_par sd ! c = m + k"
        using seensd prntsd parsd True c lseen lprnt lpar by (simp add: nth_list_update_eq)
      thus ?thesis using c by blast
    next
      case False
      hence ks: "k < ds_nxt s" using klt' by simp
      have kITs: "ds_aest s ! k = InTree" using kIT aestsd False by (simp add: nth_list_update_neq)
      obtain c0 where c0: "c0 < vcount" "ds_seen s ! c0" "ds_prnt s ! c0 = vcount" "ds_par s ! c0 = m + k"
        using ao ks kITs by (auto simp: art_owned_def)
      have c0nc: "c0 \<noteq> c" using c0(2) unseen by auto
      have "ds_seen sd ! c0 \<and> ds_prnt sd ! c0 = vcount \<and> ds_par sd ! c0 = m + k"
        using seensd prntsd parsd c0 c0nc by (simp add: nth_list_update_neq)
      thus ?thesis using c0(1) by blast
    qed
  qed
  show ?thesis using opd build_dfs_art_owned[OF dom invsd aosd] by simp
qed

lemma phase1_step_art_owned:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" and al: "art_len s"
      and ao: "art_owned s" and inb: "ds_nxt (phase1_step acyc_flow v s) \<le> length vs_list"
  shows "art_owned (phase1_step acyc_flow v s)"
proof (cases "imbalance ! v = 0")
  case True thus ?thesis using ao by (simp add: phase1_step_def)
next
  case nz: False
  have vlt: "v < vcount" using v vs_less_vcount by simp
  show ?thesis
  proof (cases "ds_seen s ! v")
    case seen: True
    have eq: "phase1_step acyc_flow v s = emit_U_edge s v" using nz seen by (simp add: phase1_step_def)
    have inbs: "ds_nxt s < length vs_list" using inb eq by (simp add: emit_U_edge_nxt)
    thus ?thesis using eq emit_U_edge_art_owned[OF ao al inbs] by simp
  next
    case notseen: False
    have vnz: "v \<noteq> 0" using v no_zero_node by metis
    have eq: "phase1_step acyc_flow v s = open_tree_component acyc_flow s v" using nz notseen by (simp add: phase1_step_def)
    have nxt: "ds_nxt (open_tree_component acyc_flow s v) = Suc (ds_nxt s)" using open_tree_component_art(1)[OF inv vlt] .
    have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
    show ?thesis using eq open_tree_component_art_owned[OF inv ao vlt notseen vnz stke al inbs] by simp
  qed
qed

lemma phase2_step_art_owned:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []" and al: "art_len s"
      and ao: "art_owned s" and inb: "ds_nxt (phase2_step acyc_flow v s) \<le> length vs_list"
  shows "art_owned (phase2_step acyc_flow v s)"
proof (cases "ds_seen s ! v \<or> is_lonely v")
  case True thus ?thesis using ao by (simp add: phase2_step_def)
next
  case False
  hence notseen: "\<not> ds_seen s ! v" and nl: "\<not> is_lonely v" by auto
  have vlt: "v < vcount" using v vs_less_vcount by simp
  have vnz: "v \<noteq> 0" using v no_zero_node by metis
  have eq: "phase2_step acyc_flow v s = open_tree_component acyc_flow s v" using notseen nl by (simp add: phase2_step_def)
  have nxt: "ds_nxt (open_tree_component acyc_flow s v) = Suc (ds_nxt s)" using open_tree_component_art(1)[OF inv vlt] .
  have inbs: "ds_nxt s < length vs_list" using inb eq nxt by simp
  show ?thesis using eq open_tree_component_art_owned[OF inv ao vlt notseen vnz stke al inbs] by simp
qed

lemma fold_phase1_art_owned:
  assumes "distinct xs" "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "art_owned s"
      "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "E \<inter> set xs = {}" "ds_nxt s = card E"
  shows "art_len (fold (phase1_step acyc_flow) xs s) \<and> art_owned (fold (phase1_step acyc_flow) xs s)
         \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase1_step acyc_flow) xs s) ! v}
                 \<and> ds_nxt (fold (phase1_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(2) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv1: "dfs_inv acyc_flow (phase1_step acyc_flow x s)" "ds_stk (phase1_step acyc_flow x s) = []"
    using phase1_step_inv[OF xvs conjI[OF Cons.prems(3) Cons.prems(4)]] by auto
  have al1: "art_len (phase1_step acyc_flow x s)" using phase1_step_art_len[OF xvs Cons.prems(3) Cons.prems(5)] .
  have Emono: "E \<subseteq> {v \<in> set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}"
    using Cons.prems(8) phase1_step_seen_mono[OF Cons.prems(3) xlt] by auto
  have Edisj: "E \<inter> set rest = {}" using Cons.prems(9) by auto
  have distr: "distinct rest" using Cons.prems(1) by simp
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(2) by simp
  have Esub: "E \<subseteq> set vs_list" using Cons.prems(8) by auto
  have xnotE: "x \<notin> E" using Cons.prems(9) by auto
  have step_inb: "ds_nxt (phase1_step acyc_flow x s) \<le> length vs_list"
    using phase1_step_nxt[OF Cons.prems(3) xlt]
  proof
    assume "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(10) card_sub_vs_le[OF Esub] by simp
  next
    assume A: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) \<and> ds_seen (phase1_step acyc_flow x s) ! x"
    have "insert x E \<subseteq> set vs_list" using Esub xvs by auto
    hence "card (insert x E) \<le> length vs_list" by (rule card_sub_vs_le)
    thus ?thesis using A Cons.prems(10) xnotE Cons.prems(7) by (simp add: card_insert_disjoint)
  qed
  have ao1: "art_owned (phase1_step acyc_flow x s)"
    using phase1_step_art_owned[OF xvs Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) step_inb] .
  from phase1_step_nxt[OF Cons.prems(3) xlt] show ?case
  proof
    assume A: "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase1_step acyc_flow x s) = card E" using A Cons.prems(10) by simp
    show ?thesis
      using Cons.hyps[OF distr subr inv1(1) inv1(2) al1 ao1 Cons.prems(7) Emono Edisj card1] by simp
  next
    assume B: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) \<and> ds_seen (phase1_step acyc_flow x s) ! x"
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(7) by (simp add: E2_def)
    have E2seen: "E2 \<subseteq> {v \<in> set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have E2disj: "E2 \<inter> set rest = {}" using Edisj Cons.prems(1) by (auto simp: E2_def)
    have card2: "ds_nxt (phase1_step acyc_flow x s) = card E2" using B Cons.prems(10) xnotE Cons.prems(7) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF distr subr inv1(1) inv1(2) al1 ao1 fin2 E2seen E2disj card2] by simp
  qed
qed

lemma fold_phase2_art_owned:
  assumes "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "art_owned s"
      "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "ds_nxt s = card E"
  shows "art_len (fold (phase2_step acyc_flow) xs s) \<and> art_owned (fold (phase2_step acyc_flow) xs s)
         \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase2_step acyc_flow) xs s) ! v}
                 \<and> ds_nxt (fold (phase2_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(1) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv1: "dfs_inv acyc_flow (phase2_step acyc_flow x s)" "ds_stk (phase2_step acyc_flow x s) = []"
    using phase2_step_inv[OF xvs conjI[OF Cons.prems(2) Cons.prems(3)]] by auto
  have al1: "art_len (phase2_step acyc_flow x s)" using phase2_step_art_len[OF xvs Cons.prems(2) Cons.prems(4)] .
  have Emono: "E \<subseteq> {v \<in> set vs_list. ds_seen (phase2_step acyc_flow x s) ! v}"
    using Cons.prems(7) phase2_step_seen_mono[OF Cons.prems(2) xlt] by auto
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(1) by simp
  have Esub: "E \<subseteq> set vs_list" using Cons.prems(7) by auto
  have step_inb: "ds_nxt (phase2_step acyc_flow x s) \<le> length vs_list"
    using phase2_step_nxt2[OF Cons.prems(2) xlt]
  proof
    assume "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    thus ?thesis using Cons.prems(8) card_sub_vs_le[OF Esub] by simp
  next
    assume A: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! x \<and> ds_seen (phase2_step acyc_flow x s) ! x"
    have xnotE: "x \<notin> E" using A Cons.prems(7) by auto
    have "insert x E \<subseteq> set vs_list" using Esub xvs by auto
    hence "card (insert x E) \<le> length vs_list" by (rule card_sub_vs_le)
    thus ?thesis using A Cons.prems(8) xnotE Cons.prems(6) by (simp add: card_insert_disjoint)
  qed
  have ao1: "art_owned (phase2_step acyc_flow x s)"
    using phase2_step_art_owned[OF xvs Cons.prems(2) Cons.prems(3) Cons.prems(4) Cons.prems(5) step_inb] .
  from phase2_step_nxt2[OF Cons.prems(2) xlt] show ?case
  proof
    assume A: "ds_nxt (phase2_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase2_step acyc_flow x s) = card E" using A Cons.prems(8) by simp
    show ?thesis
      using Cons.hyps[OF subr inv1(1) inv1(2) al1 ao1 Cons.prems(6) Emono card1] by simp
  next
    assume B: "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s) \<and> \<not> ds_seen s ! x \<and> ds_seen (phase2_step acyc_flow x s) ! x"
    have xnotE: "x \<notin> E" using B Cons.prems(7) by auto
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(6) by (simp add: E2_def)
    have E2seen: "E2 \<subseteq> {v \<in> set vs_list. ds_seen (phase2_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have card2: "ds_nxt (phase2_step acyc_flow x s) = card E2" using B Cons.prems(8) xnotE Cons.prems(6) by (simp add: E2_def card_insert_disjoint)
    show ?thesis using Cons.hyps[OF subr inv1(1) inv1(2) al1 ao1 fin2 E2seen card2] by simp
  qed
qed

lemma art_owned_dfs_init: "art_owned dfs_init"
  by (simp add: art_owned_def dfs_init_def)

lemma build_tree_art_owned: "art_owned (build_tree acyc_flow)"
proof -
  have i0: "dfs_inv acyc_flow dfs_init \<and> ds_stk dfs_init = []" using dfs_init_inv by (simp add: dfs_init_def)
  have al0: "art_len dfs_init" by (rule dfs_init_art_len)
  have C1: "art_len (fold (phase1_step acyc_flow) vs_list dfs_init) \<and> art_owned (fold (phase1_step acyc_flow) vs_list dfs_init)
        \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase1_step acyc_flow) vs_list dfs_init) ! v}
                \<and> ds_nxt (fold (phase1_step acyc_flow) vs_list dfs_init) = card E')"
    apply (rule fold_phase1_art_owned[where E="{}"])
    subgoal by (rule distinct_vs_list)
    subgoal by simp
    subgoal using i0 by simp
    subgoal using i0 by simp
    subgoal by (rule al0)
    subgoal by (rule art_owned_dfs_init)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal by (simp add: dfs_init_def)
    done
  have P1: "art_len (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have AO1: "art_owned (phase1 acyc_flow dfs_init)" using C1 by (simp add: phase1_def)
  have E1ex: "\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}
                \<and> ds_nxt (phase1 acyc_flow dfs_init) = card E'" using C1 by (simp add: phase1_def)
  have p1inv: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init) \<and> ds_stk (phase1 acyc_flow dfs_init) = []" using phase1_inv[OF i0] .
  obtain E1 where E1f: "finite E1" and E1s: "E1 \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}"
    and E1n: "ds_nxt (phase1 acyc_flow dfs_init) = card E1" using E1ex by blast
  have C2: "art_len (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        \<and> art_owned (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init))
        \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init)) ! v}
                \<and> ds_nxt (fold (phase2_step acyc_flow) vs_list (phase1 acyc_flow dfs_init)) = card E')"
    apply (rule fold_phase2_art_owned[where E=E1 and s="phase1 acyc_flow dfs_init"])
    subgoal by simp
    subgoal using p1inv by simp
    subgoal using p1inv by simp
    subgoal by (rule P1)
    subgoal by (rule AO1)
    subgoal by (rule E1f)
    subgoal by (rule E1s)
    subgoal by (rule E1n)
    done
  have "art_owned (phase2 acyc_flow (phase1 acyc_flow dfs_init))" using C2 by (simp add: phase2_def)
  thus ?thesis by (simp add: build_tree_def Let_def art_owned_def)
qed

subsection \<open>The tree edges are exactly the InTree edges (real coverage + artificial coverage)\<close>

lemma InTree_subseteq_T:
  assumes acyc: "original_network.acyclic_flow (h \<circ> nth acyc_flow)"
  shows "{e \<in> {0..<m + Kart}. state_all ! e = InTree}
           \<subseteq> (!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})"
proof
  fix e assume "e \<in> {e \<in> {0..<m + Kart}. state_all ! e = InTree}"
  hence e: "e < m + Kart" and st: "state_all ! e = InTree" by auto
  show "e \<in> (!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})"
  proof (cases "e < m")
    case True
    have "edge_state acyc_flow ! e = InTree" using st state_all_real[OF True] by simp
    hence free: "is_free acyc_flow e" by (simp add: is_free_def)
    obtain v where v: "v \<in> Vseen" and pe: "ds_par (build_tree acyc_flow) ! v = e"
      using free_edge_covered[OF acyc True free] by blast
    have vS: "v \<in> NS.\<V> - {vcount}" using v NS_V_minus_root by simp
    have "ds_par (build_tree acyc_flow) ! v \<in> (!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})"
      using vS by (rule imageI)
    thus ?thesis using pe by simp
  next
    case False
    then obtain k where ek: "e = m + k" by (metis add.commute le_Suc_ex not_less)
    have kK: "k < Kart" using e ek by simp
    have kn: "k < ds_nxt (build_tree acyc_flow)" using kK by (simp add: Kart_def)
    have "ds_aest (build_tree acyc_flow) ! k = InTree" using st ek kK state_all_art by simp
    then obtain c where c: "c < vcount" "ds_seen (build_tree acyc_flow) ! c"
        "ds_par (build_tree acyc_flow) ! c = m + k"
      using build_tree_art_owned kn by (auto simp: art_owned_def)
    have cV: "c \<in> Vseen" using c(1,2) by (simp add: Vseen_def)
    have cS: "c \<in> NS.\<V> - {vcount}" using cV NS_V_minus_root by simp
    have "ds_par (build_tree acyc_flow) ! c \<in> (!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})"
      using cS by (rule imageI)
    thus ?thesis using c(3) ek by simp
  qed
qed

lemma T_eq_InTree:
  assumes acyc: "original_network.acyclic_flow (h \<circ> nth acyc_flow)"
  shows "(!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}) = {e \<in> {0..<m + Kart}. state_all ! e = InTree}"
  using T_sub_InTree InTree_subseteq_T[OF acyc] by blast

subsection \<open>The spanning-tree partition: edge cover and tag disjointness\<close>

lemma edge_partition:
  assumes acyc: "original_network.acyclic_flow (h \<circ> nth acyc_flow)"
  shows "{0..<m + Kart} =
           (!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})
           \<union> {e \<in> {0..<m + Kart}. state_all ! e = InU}
           \<union> {e \<in> {0..<m + Kart}. state_all ! e = InL}"
proof -
  have T: "(!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}) = {e \<in> {0..<m + Kart}. state_all ! e = InTree}"
    by (rule T_eq_InTree[OF acyc])
  show ?thesis unfolding T by (auto dest: state_total)
qed

lemma part_disj:
  assumes acyc: "original_network.acyclic_flow (h \<circ> nth acyc_flow)"
  shows "(!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}) \<inter> {e \<in> {0..<m + Kart}. state_all ! e = InU} = {}"
    and "(!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}) \<inter> {e \<in> {0..<m + Kart}. state_all ! e = InL} = {}"
    and "{e \<in> {0..<m + Kart}. state_all ! e = InL} \<inter> {e \<in> {0..<m + Kart}. state_all ! e = InU} = {}"
proof -
  have T: "(!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}) = {e \<in> {0..<m + Kart}. state_all ! e = InTree}"
    by (rule T_eq_InTree[OF acyc])
  show "(!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}) \<inter> {e \<in> {0..<m + Kart}. state_all ! e = InU} = {}"
    unfolding T by auto
  show "(!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}) \<inter> {e \<in> {0..<m + Kart}. state_all ! e = InL} = {}"
    unfolding T by auto
  show "{e \<in> {0..<m + Kart}. state_all ! e = InL} \<inter> {e \<in> {0..<m + Kart}. state_all ! e = InU} = {}"
    by auto
qed

subsection \<open>The spanning-tree partition: arborescence and spanning (Some branch)\<close>

text \<open>The remaining four conjuncts of @{const NS.spanning_tree_partition}: the parent edges form a
      graph (endpoint-set injectivity), a @{const graph_abs}, a rooted @{const graph_abs.arborescence}
      (via the unique-distinct-walk bridge @{thm unique_walks_arborescence}, whose uniqueness premise is
      exactly the arborescence-ADT axiom @{thm NS.general}(3)), and span the vertex set. Together with the
      edge cover / tag disjointness above this assembles @{const NS.spanning_tree_partition} on the Some
      branch (acyclicity is needed only through @{thm edge_partition} / @{thm part_disj}).\<close>

lemma dVs_make_pair_Vs_gen:
  "dVs ((\<lambda>e. (g e, k e)) ` X) = Vs ((\<lambda>e. {g e, k e}) ` X)"
  by (auto simp: dVs_def Vs_def)

lemma tree_edge_endpoint_inj:
  assumes u: "u \<in> Vseen" and u': "u' \<in> Vseen"
    and eq: "{fst_all ! (ds_par (build_tree acyc_flow) ! u), snd_all ! (ds_par (build_tree acyc_flow) ! u)}
           = {fst_all ! (ds_par (build_tree acyc_flow) ! u'), snd_all ! (ds_par (build_tree acyc_flow) ! u')}"
  shows "u = u'"
proof -
  let ?bt = "build_tree acyc_flow"
  let ?p = "\<lambda>x. ds_prnt ?bt ! x"
  have uvs: "u \<in> set vs_list" and u'vs: "u' \<in> set vs_list" using u u' V_sub_vs_list Vseen_eq_V by auto
  have ult: "u < vcount" and useen: "ds_seen ?bt ! u" using u by (auto simp: Vseen_def)
  have u'lt: "u' < vcount" and u'seen: "ds_seen ?bt ! u'" using u' by (auto simp: Vseen_def)
  have stepu: "(u, ?p u) \<in> pstep ?bt" using ult useen by (auto simp: pstep_def)
  have stepu': "(u', ?p u') \<in> pstep ?bt" using u'lt u'seen by (auto simp: pstep_def)
  have unp: "u \<noteq> ?p u" using stepu pstep_acyclic by (metis acyclic_def r_into_trancl)
  have u'np: "u' \<noteq> ?p u'" using stepu' pstep_acyclic by (metis acyclic_def r_into_trancl)
  have setu: "{fst_all ! (ds_par ?bt ! u), snd_all ! (ds_par ?bt ! u)} = {u, ?p u}"
    using tc_endpoints[OF u] by (cases "ds_dir ?bt ! u") auto
  have setu': "{fst_all ! (ds_par ?bt ! u'), snd_all ! (ds_par ?bt ! u')} = {u', ?p u'}"
    using tc_endpoints[OF u'] by (cases "ds_dir ?bt ! u'") auto
  have "{u, ?p u} = {u', ?p u'}" using setu setu' eq by simp
  hence "(u = u' \<and> ?p u = ?p u') \<or> (u = ?p u' \<and> ?p u = u')"
    using unp u'np by (auto simp: doubleton_eq_iff)
  thus ?thesis
  proof
    assume "u = u' \<and> ?p u = ?p u'" thus ?thesis by simp
  next
    assume A: "u = ?p u' \<and> ?p u = u'"
    have "(u, u') \<in> pstep ?bt" using stepu A by argo
    moreover have "(u', u) \<in> pstep ?bt" using stepu' A by argo
    ultimately have "(u, u) \<in> (pstep ?bt)\<^sup>+" by (meson trancl.simps)
    thus ?thesis using pstep_acyclic by (simp add: acyclic_def)
  qed
qed

lemma NSinit_partition:
  assumes acyc: "original_network.acyclic_flow (h \<circ> nth acyc_flow)"
  shows "NS.spanning_tree_partition vcount
           ((!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount}))
           {e \<in> {0..<m + Kart}. state_all ! e = InL}
           {e \<in> {0..<m + Kart}. state_all ! e = InU}"
proof (rule NS.spanning_tree_partitionI)
  let ?T = "(!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})"
  let ?U = "{e \<in> {0..<m + Kart}. state_all ! e = InU}"
  let ?L = "{e \<in> {0..<m + Kart}. state_all ! e = InL}"
  let ?f = "\<lambda>e. {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
                  if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))}"
  have tci: "?f ` ?T = abstract_arb Sarb" by (rule tc_image)
  have gi: "graph_invar (abstract_arb Sarb)" by (rule graph_invar_abstract_arb[OF arb_invar_Sarb])
  show "{0..<m + Kart} = ?T \<union> ?U \<union> ?L" using edge_partition[OF acyc] by simp
  show "?T \<inter> ?U = {}" by (rule part_disj(1)[OF acyc])
  show "?T \<inter> ?L = {}" by (rule part_disj(2)[OF acyc])
  show "?L \<inter> ?U = {}" by (rule part_disj(3)[OF acyc])
  show "graph_abs (?f ` ?T)"
    unfolding tci using gi by (simp add: graph_abs_def)
  show "graph_abs.arborescence (?f ` ?T) vcount (?f ` ?T)"
    unfolding tci
  proof (rule unique_walks_arborescence)
    show "graph_invar (abstract_arb Sarb)" by (rule gi)
    show "vcount \<in> Vs (abstract_arb Sarb)" using Vs_abstract_arb[OF arb_invar_Sarb] r_in_V by simp
  next
    fix x y assume "x \<in> Vs (abstract_arb Sarb)" and "y \<in> Vs (abstract_arb Sarb)"
    hence xV: "x \<in> NS.\<V>" and yV: "y \<in> NS.\<V>" using Vs_abstract_arb[OF arb_invar_Sarb] NS_V_Varb by auto
    show "\<exists>!p. walk_betw (abstract_arb Sarb) x p y \<and> distinct p"
      using NS.general(3)[OF arb_invar_Sarb yV xV] by simp
  qed
  show "\<forall>e e'. {e, e'} \<subseteq> ?T \<and> {if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
                              if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))}
                          = {if e' < m + Kart then fst_all ! e' else fst (prod_decode (e' - (m + Kart))),
                             if e' < m + Kart then snd_all ! e' else snd (prod_decode (e' - (m + Kart)))}
               \<longrightarrow> e = e'"
  proof (intro allI impI, elim conjE)
    fix e e' assume sub: "{e, e'} \<subseteq> ?T"
      and eeq: "{if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
                  if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))}
              = {if e' < m + Kart then fst_all ! e' else fst (prod_decode (e' - (m + Kart))),
                 if e' < m + Kart then snd_all ! e' else snd (prod_decode (e' - (m + Kart)))}"
    have eT: "e \<in> ?T" using sub by simp
    have e'T: "e' \<in> ?T" using sub by simp
    from eT obtain u where uV: "u \<in> NS.\<V> - {vcount}" and eu: "e = ds_par (build_tree acyc_flow) ! u"
      unfolding image_iff by blast
    from e'T obtain u' where u'V: "u' \<in> NS.\<V> - {vcount}" and eu': "e' = ds_par (build_tree acyc_flow) ! u'"
      unfolding image_iff by blast
    have uVs: "u \<in> Vseen" using uV NS_V_minus_root by simp
    have u'Vs: "u' \<in> Vseen" using u'V NS_V_minus_root by simp
    have ult: "u < vcount" and useen: "ds_seen (build_tree acyc_flow) ! u" using uVs by (auto simp: Vseen_def)
    have u'lt: "u' < vcount" and u'seen: "ds_seen (build_tree acyc_flow) ! u'" using u'Vs by (auto simp: Vseen_def)
    have emK': "ds_par (build_tree acyc_flow) ! u < m + Kart" using par_lt_marc[OF ult useen] .
    have e'mK': "ds_par (build_tree acyc_flow) ! u' < m + Kart" using par_lt_marc[OF u'lt u'seen] .
    have endeq: "{fst_all ! (ds_par (build_tree acyc_flow) ! u), snd_all ! (ds_par (build_tree acyc_flow) ! u)}
               = {fst_all ! (ds_par (build_tree acyc_flow) ! u'), snd_all ! (ds_par (build_tree acyc_flow) ! u')}"
      using eeq by (simp only: eu eu' if_P[OF emK'] if_P[OF e'mK'])
    have "u = u'" by (rule tree_edge_endpoint_inj[OF uVs u'Vs endeq])
    thus "e = e'" using eu eu' by simp
  qed
  show "dVs (NS.make_pair ` ?T) = NS.\<V>"
  proof -
    have mp: "NS.make_pair = (\<lambda>e. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart))),
                                    if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))))"
      by (rule ext) (simp add: NS.make_pair_def)
    have "dVs (NS.make_pair ` ?T) = Vs (?f ` ?T)"
      unfolding mp by (rule dVs_make_pair_Vs_gen)
    thus ?thesis using tci Vs_abstract_arb[OF arb_invar_Sarb] NS_V_Varb by simp
  qed
qed

subsection \<open>Towards @{text init_bflow}: excess decomposition of the assembled flow\<close>

text \<open>The augmented excess of @{const flow_all} splits into a real part and an artificial part. On the
      real edges @{term \<open>e < m\<close>} the assembled flow is @{const acyc_flow}, so --- since the augmented and
      original in/out-edge sets agree there (@{thm delta_minus_orig} / @{thm delta_plus_orig}) --- the real
      part is exactly \<open>original_network.ex (h \<circ> nth acyc_flow) v\<close>. The artificial part is the signed
      flow on the artificial in/out edges of @{term v}; identifying it with @{term \<open>imbalance ! v\<close>} (and,
      with @{thm make_acyclic_ex}, \<open>original_network.ex (h \<circ> nth acyc_flow) v = h (excess ! v)\<close>) is the
      remaining step toward @{text init_bflow}.\<close>

lemma flow_all_ex_real:
  "(\<Sum>e\<in>NS.delta_minus v \<inter> {0..<m}. h (flow_all ! e)) - (\<Sum>e\<in>NS.delta_plus v \<inter> {0..<m}. h (flow_all ! e))
     = original_network.ex (h \<circ> nth acyc_flow) v"
proof -
  have m1: "NS.delta_minus v \<inter> {0..<m} = original_network.delta_minus v" using delta_minus_orig by simp
  have p1: "NS.delta_plus v \<inter> {0..<m} = original_network.delta_plus v" using delta_plus_orig by simp
  have dmreal: "\<And>e. e \<in> original_network.delta_minus v \<Longrightarrow> flow_all ! e = acyc_flow ! e"
    using flow_all_real by (auto simp: original_network.delta_minus_def)
  have dpreal: "\<And>e. e \<in> original_network.delta_plus v \<Longrightarrow> flow_all ! e = acyc_flow ! e"
    using flow_all_real by (auto simp: original_network.delta_plus_def)
  have "(\<Sum>e\<in>NS.delta_minus v \<inter> {0..<m}. h (flow_all ! e)) = (\<Sum>e\<in>original_network.delta_minus v. h (acyc_flow ! e))"
    unfolding m1 by (rule sum.cong[OF refl]) (simp add: dmreal)
  moreover have "(\<Sum>e\<in>NS.delta_plus v \<inter> {0..<m}. h (flow_all ! e)) = (\<Sum>e\<in>original_network.delta_plus v. h (acyc_flow ! e))"
    unfolding p1 by (rule sum.cong[OF refl]) (simp add: dpreal)
  ultimately show ?thesis by (simp add: original_network.ex_def comp_def)
qed

lemma ex_flow_all_decomp:
  "NS.ex (h \<circ> nth flow_all) v = original_network.ex (h \<circ> nth acyc_flow) v
     + h ((\<Sum>e\<in>NS.delta_minus v \<inter> {m..<m+Kart}. flow_all ! e) - (\<Sum>e\<in>NS.delta_plus v \<inter> {m..<m+Kart}. flow_all ! e))"
proof -
  have dmsub: "NS.delta_minus v \<subseteq> {0..<m+Kart}"
    by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: NS.delta_minus_def)
  have dpsub: "NS.delta_plus v \<subseteq> {0..<m+Kart}"
    by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: NS.delta_plus_def)
  have split: "{0..<m+Kart} = {0..<m} \<union> {m..<m+Kart}" by auto
  have dmU: "NS.delta_minus v = (NS.delta_minus v \<inter> {0..<m}) \<union> (NS.delta_minus v \<inter> {m..<m+Kart})"
    using dmsub split by blast
  have dpU: "NS.delta_plus v = (NS.delta_plus v \<inter> {0..<m}) \<union> (NS.delta_plus v \<inter> {m..<m+Kart})"
    using dpsub split by blast
  have dmdisj: "(NS.delta_minus v \<inter> {0..<m}) \<inter> (NS.delta_minus v \<inter> {m..<m+Kart}) = {}" by auto
  have dpdisj: "(NS.delta_plus v \<inter> {0..<m}) \<inter> (NS.delta_plus v \<inter> {m..<m+Kart}) = {}" by auto
  have sm: "(\<Sum>e\<in>NS.delta_minus v. h (nth flow_all e))
          = (\<Sum>e\<in>NS.delta_minus v \<inter> {0..<m}. h (flow_all ! e)) + (\<Sum>e\<in>NS.delta_minus v \<inter> {m..<m+Kart}. h (flow_all ! e))"
    by (subst dmU) (rule sum.union_disjoint[OF _ _ dmdisj], auto simp: delta_fin[unfolded NS.delta_minus_def])
  have sp: "(\<Sum>e\<in>NS.delta_plus v. h (nth flow_all e))
          = (\<Sum>e\<in>NS.delta_plus v \<inter> {0..<m}. h (flow_all ! e)) + (\<Sum>e\<in>NS.delta_plus v \<inter> {m..<m+Kart}. h (flow_all ! e))"
    by (subst dpU) (rule sum.union_disjoint[OF _ _ dpdisj], auto simp: delta_fin[unfolded NS.delta_plus_def])
  have "NS.ex (h \<circ> nth flow_all) v = (\<Sum>e\<in>NS.delta_minus v. h (nth flow_all e)) - (\<Sum>e\<in>NS.delta_plus v. h (nth flow_all e))"
    by (simp add: NS.ex_def comp_def)
  also have "\<dots> = ((\<Sum>e\<in>NS.delta_minus v \<inter> {0..<m}. h (flow_all ! e)) - (\<Sum>e\<in>NS.delta_plus v \<inter> {0..<m}. h (flow_all ! e)))
               + ((\<Sum>e\<in>NS.delta_minus v \<inter> {m..<m+Kart}. h (flow_all ! e)) - (\<Sum>e\<in>NS.delta_plus v \<inter> {m..<m+Kart}. h (flow_all ! e)))"
    using sm sp by (simp add: algebra_simps)
  also have "\<dots> = original_network.ex (h \<circ> nth acyc_flow) v
               + ((\<Sum>e\<in>NS.delta_minus v \<inter> {m..<m+Kart}. h (flow_all ! e)) - (\<Sum>e\<in>NS.delta_plus v \<inter> {m..<m+Kart}. h (flow_all ! e)))"
    using flow_all_ex_real by simp
  also have "\<dots> = original_network.ex (h \<circ> nth acyc_flow) v
               + h ((\<Sum>e\<in>NS.delta_minus v \<inter> {m..<m+Kart}. flow_all ! e) - (\<Sum>e\<in>NS.delta_plus v \<inter> {m..<m+Kart}. flow_all ! e))"
    by (simp add: h_sum)
  finally show ?thesis .
qed

text \<open>The artificial in/out edge-sums at @{term v} reindex to sums over the artificial \<^emph>\<open>slots\<close>
      @{term \<open>k < Kart\<close>}: edge @{term \<open>m + k\<close>} is the \<open>k\<close>-th artificial edge, carrying
      @{term \<open>ds_aflw (build_tree acyc_flow) ! k\<close>} (@{thm flow_all_art}). The membership rewrites
      @{text dm_art_iff}/@{text dp_art_iff} strip the augmented endpoint functions down to the plain
      arrays (the \<open>fst_exec\<close>/\<open>snd_exec\<close> simp rules must be disabled throughout --- they are
      self-referential and loop on any \<open>fst_all ! e\<close> / \<open>snd_all ! e\<close>).\<close>

lemma dm_art_iff: "e \<in> NS.delta_minus v \<inter> {m..<m+Kart} \<longleftrightarrow> (m \<le> e \<and> e < m+Kart \<and> snd_all ! e = v)"
proof -
  have "e \<in> NS.delta_minus v \<longleftrightarrow> (e \<in> {0..<m+Kart} \<and> snd_all ! e = v)"
    by (simp del: NS.fst_exec_eq NS.snd_exec_eq add: NS.delta_minus_def)
  thus ?thesis by auto
qed

lemma dp_art_iff: "e \<in> NS.delta_plus v \<inter> {m..<m+Kart} \<longleftrightarrow> (m \<le> e \<and> e < m+Kart \<and> fst_all ! e = v)"
proof -
  have "e \<in> NS.delta_plus v \<longleftrightarrow> (e \<in> {0..<m+Kart} \<and> fst_all ! e = v)"
    by (simp del: NS.fst_exec_eq NS.snd_exec_eq add: NS.delta_plus_def)
  thus ?thesis by auto
qed

lemma dm_art_set: "NS.delta_minus v \<inter> {m..<m+Kart} = {e. m \<le> e \<and> e < m+Kart \<and> snd_all!e = v}"
  using dm_art_iff by blast

lemma dp_art_set: "NS.delta_plus v \<inter> {m..<m+Kart} = {e. m \<le> e \<and> e < m+Kart \<and> fst_all!e = v}"
  using dp_art_iff by blast

lemma art_reindex_minus:
  "(\<Sum>e\<in>NS.delta_minus v \<inter> {m..<m+Kart}. flow_all ! e)
     = (\<Sum>k\<in>{k. k < Kart \<and> snd_all ! (m+k) = v}. ds_aflw (build_tree acyc_flow) ! k)"
proof -
  let ?S = "{k. k < Kart \<and> snd_all ! (m+k) = v}"
  have inj: "inj_on (\<lambda>k. m+k) ?S" by (auto simp: inj_on_def)
  have setEq: "{e. m \<le> e \<and> e < m+Kart \<and> snd_all!e = v} = (\<lambda>k. m+k) ` ?S"
  proof (rule set_eqI, rule iffI)
    fix e assume "e \<in> {e. m \<le> e \<and> e < m+Kart \<and> snd_all!e = v}"
    hence e1: "m \<le> e" "e < m+Kart" and sv: "snd_all!e = v" by blast+
    have mke: "m + (e - m) = e" using e1 by simp
    have kk: "e - m < Kart" using e1 by simp
    have ss: "snd_all ! (m + (e - m)) = v" using sv mke by argo
    show "e \<in> (\<lambda>k. m+k) ` ?S"
      using kk ss mke by (intro image_eqI[of e _ "e - m"]) (simp_all del: NS.fst_exec_eq NS.snd_exec_eq)
  next
    fix e assume "e \<in> (\<lambda>k. m+k) ` ?S"
    then obtain k where k: "e = m+k" and kS: "k<Kart" "snd_all!(m+k)=v" by blast
    show "e \<in> {e. m \<le> e \<and> e < m+Kart \<and> snd_all!e = v}" using k kS by (simp del: NS.fst_exec_eq NS.snd_exec_eq)
  qed
  have "(\<Sum>e\<in>NS.delta_minus v \<inter> {m..<m+Kart}. flow_all ! e) = (\<Sum>e\<in>(\<lambda>k. m+k) ` ?S. flow_all ! e)"
    by (simp only: dm_art_set setEq)
  also have "\<dots> = (\<Sum>k\<in>?S. flow_all ! (m+k))" by (subst sum.reindex[OF inj]) simp
  also have "\<dots> = (\<Sum>k\<in>?S. ds_aflw (build_tree acyc_flow) ! k)"
    by (rule sum.cong[OF refl]) (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: flow_all_art)
  finally show ?thesis .
qed

lemma art_reindex_plus:
  "(\<Sum>e\<in>NS.delta_plus v \<inter> {m..<m+Kart}. flow_all ! e)
     = (\<Sum>k\<in>{k. k < Kart \<and> fst_all ! (m+k) = v}. ds_aflw (build_tree acyc_flow) ! k)"
proof -
  let ?S = "{k. k < Kart \<and> fst_all ! (m+k) = v}"
  have inj: "inj_on (\<lambda>k. m+k) ?S" by (auto simp: inj_on_def)
  have setEq: "{e. m \<le> e \<and> e < m+Kart \<and> fst_all!e = v} = (\<lambda>k. m+k) ` ?S"
  proof (rule set_eqI, rule iffI)
    fix e assume "e \<in> {e. m \<le> e \<and> e < m+Kart \<and> fst_all!e = v}"
    hence e1: "m \<le> e" "e < m+Kart" and sv: "fst_all!e = v" by blast+
    have mke: "m + (e - m) = e" using e1 by simp
    have kk: "e - m < Kart" using e1 by simp
    have ss: "fst_all ! (m + (e - m)) = v" using sv mke by argo
    show "e \<in> (\<lambda>k. m+k) ` ?S"
      using kk ss mke by (intro image_eqI[of e _ "e - m"]) (simp_all del: NS.fst_exec_eq NS.snd_exec_eq)
  next
    fix e assume "e \<in> (\<lambda>k. m+k) ` ?S"
    then obtain k where k: "e = m+k" and kS: "k<Kart" "fst_all!(m+k)=v" by blast
    show "e \<in> {e. m \<le> e \<and> e < m+Kart \<and> fst_all!e = v}" using k kS by (simp del: NS.fst_exec_eq NS.snd_exec_eq)
  qed
  have "(\<Sum>e\<in>NS.delta_plus v \<inter> {m..<m+Kart}. flow_all ! e) = (\<Sum>e\<in>(\<lambda>k. m+k) ` ?S. flow_all ! e)"
    by (simp only: dp_art_set setEq)
  also have "\<dots> = (\<Sum>k\<in>?S. flow_all ! (m+k))" by (subst sum.reindex[OF inj]) simp
  also have "\<dots> = (\<Sum>k\<in>?S. ds_aflw (build_tree acyc_flow) ! k)"
    by (rule sum.cong[OF refl]) (auto simp del: NS.fst_exec_eq NS.snd_exec_eq simp add: flow_all_art)
  finally show ?thesis .
qed

subsection \<open>Towards @{text init_bflow}: the artificial excess accumulator\<close>

text \<open>@{term \<open>aex s v\<close>} is the artificial-edge contribution to @{term v}'s excess in state @{term s}:
      the signed per-slot flow over the slots already emitted (@{term \<open>k < ds_nxt s\<close>}). Each emission
      --- @{const emit_U_edge} or the seed of @{const open_tree_component} (the enclosed @{const build_dfs}
      freezes the artificial arrays, @{thm build_dfs_art}) --- changes @{term \<open>aex s v\<close>} by exactly
      @{term \<open>- imbalance ! v\<close>} at the processed vertex and @{term \<open>imbalance ! v\<close>} at the root, so over
      a whole phase-1 sweep the increments accumulate as one @{const sum_list}. The @{term E}-witness
      (@{term \<open>ds_nxt s = card E\<close>}) carries the @{term \<open>ds_nxt s < length vs_list\<close>} bound the emission
      step lemmas need, exactly as in @{thm fold_phase1_art_owned}.\<close>

definition aex :: "'n dfs_state \<Rightarrow> nat \<Rightarrow> 'n" where
  "aex s v = (\<Sum>k = 0..<ds_nxt s. (if ds_asnd s ! k = v then ds_aflw s ! k else 0)
                                - (if ds_afst s ! k = v then ds_aflw s ! k else 0))"

lemma emit_U_edge_aex:
  assumes al: "art_len s" and inb: "ds_nxt s < length vs_list" and vlt: "v < vcount"
  shows "aex (emit_U_edge s v) w
           = aex s w + (if w = v then - imbalance ! v else if w = vcount then imbalance ! v else 0)"
proof -
  let ?n = "ds_nxt s"
  let ?up = "0 \<le> imbalance ! v"
  have lens: "length (ds_afst s) = length vs_list" "length (ds_asnd s) = length vs_list"
             "length (ds_aflw s) = length vs_list" using al by (auto simp: art_len_def)
  have nb: "?n < length (ds_afst s)" "?n < length (ds_asnd s)" "?n < length (ds_aflw s)"
    using inb lens by simp_all
  have nxt': "ds_nxt (emit_U_edge s v) = Suc ?n" by (simp add: emit_U_edge_def Let_def)
  have asnd_n: "ds_asnd (emit_U_edge s v) ! ?n = (if ?up then vcount else v)"
    using nb by (simp add: emit_U_edge_def Let_def art_dir_def)
  have afst_n: "ds_afst (emit_U_edge s v) ! ?n = (if ?up then v else vcount)"
    using nb by (simp add: emit_U_edge_def Let_def art_dir_def)
  have aflw_n: "ds_aflw (emit_U_edge s v) ! ?n = \<bar>imbalance ! v\<bar>"
    using nb by (simp add: emit_U_edge_def Let_def)
  have keep: "\<And>k. k < ?n \<Longrightarrow> ds_asnd (emit_U_edge s v) ! k = ds_asnd s ! k
                          \<and> ds_afst (emit_U_edge s v) ! k = ds_afst s ! k
                          \<and> ds_aflw (emit_U_edge s v) ! k = ds_aflw s ! k"
    by (auto simp: emit_U_edge_def Let_def nth_list_update_neq)
  have "aex (emit_U_edge s v) w
      = (\<Sum>k = 0..<Suc ?n. (if ds_asnd (emit_U_edge s v) ! k = w then ds_aflw (emit_U_edge s v) ! k else 0)
                        - (if ds_afst (emit_U_edge s v) ! k = w then ds_aflw (emit_U_edge s v) ! k else 0))"
    by (simp add: aex_def nxt')
  also have "\<dots> = (\<Sum>k = 0..<?n. (if ds_asnd (emit_U_edge s v) ! k = w then ds_aflw (emit_U_edge s v) ! k else 0)
                             - (if ds_afst (emit_U_edge s v) ! k = w then ds_aflw (emit_U_edge s v) ! k else 0))
               + ((if ds_asnd (emit_U_edge s v) ! ?n = w then ds_aflw (emit_U_edge s v) ! ?n else 0)
                - (if ds_afst (emit_U_edge s v) ! ?n = w then ds_aflw (emit_U_edge s v) ! ?n else 0))"
    by (simp add: sum.atLeast0_lessThan_Suc)
  also have "(\<Sum>k = 0..<?n. (if ds_asnd (emit_U_edge s v) ! k = w then ds_aflw (emit_U_edge s v) ! k else 0)
                        - (if ds_afst (emit_U_edge s v) ! k = w then ds_aflw (emit_U_edge s v) ! k else 0))
           = aex s w"
    by (simp add: aex_def) (rule sum.cong[OF refl], simp add: keep)
  finally show ?thesis
    using vlt no_zero_node
    by (cases ?up) (auto simp: asnd_n afst_n aflw_n art_flow_def imbalance_def)
qed

lemma open_tree_component_aex:
  assumes inv: "dfs_inv acyc_flow s" and al: "art_len s" and inb: "ds_nxt s < length vs_list" and vlt: "v < vcount"
  shows "aex (open_tree_component acyc_flow s v) w
           = aex s w + (if w = v then - imbalance ! v else if w = vcount then imbalance ! v else 0)"
proof -
  let ?n = "ds_nxt s"
  let ?t = "open_tree_component acyc_flow s v"
  have nxt': "ds_nxt ?t = Suc ?n" using open_tree_component_art(1)[OF inv vlt] .
  have asnd_n: "ds_asnd ?t ! ?n = (if art_dir v then vcount else v)" using open_tree_component_asnd_at[OF inv vlt inb al] .
  have afst_n: "ds_afst ?t ! ?n = (if art_dir v then v else vcount)" using open_tree_component_afst_at[OF inv vlt inb al] .
  have aflw_n: "ds_aflw ?t ! ?n = art_flow v" using open_tree_component_aflw_at[OF inv vlt inb al] .
  have keep: "\<And>k. k < ?n \<Longrightarrow> ds_asnd ?t ! k = ds_asnd s ! k \<and> ds_afst ?t ! k = ds_afst s ! k \<and> ds_aflw ?t ! k = ds_aflw s ! k"
    using open_tree_component_asnd_old[OF inv vlt] open_tree_component_afst_old[OF inv vlt] open_tree_component_aflw_old[OF inv vlt] by simp
  have "aex ?t w
      = (\<Sum>k = 0..<Suc ?n. (if ds_asnd ?t ! k = w then ds_aflw ?t ! k else 0) - (if ds_afst ?t ! k = w then ds_aflw ?t ! k else 0))"
    by (simp add: aex_def nxt')
  also have "\<dots> = (\<Sum>k = 0..<?n. (if ds_asnd ?t ! k = w then ds_aflw ?t ! k else 0) - (if ds_afst ?t ! k = w then ds_aflw ?t ! k else 0))
               + ((if ds_asnd ?t ! ?n = w then ds_aflw ?t ! ?n else 0) - (if ds_afst ?t ! ?n = w then ds_aflw ?t ! ?n else 0))"
    by (simp add: sum.atLeast0_lessThan_Suc)
  also have "(\<Sum>k = 0..<?n. (if ds_asnd ?t ! k = w then ds_aflw ?t ! k else 0) - (if ds_afst ?t ! k = w then ds_aflw ?t ! k else 0)) = aex s w"
    by (simp add: aex_def) (rule sum.cong[OF refl], simp add: keep)
  finally show ?thesis
    using vlt no_zero_node
    by (cases "art_dir v") (auto simp: asnd_n afst_n aflw_n art_flow_def art_dir_def)
qed

lemma phase1_step_aex:
  assumes v: "v \<in> set vs_list" and inv: "dfs_inv acyc_flow s" and stke: "ds_stk s = []"
      and al: "art_len s" and inb: "ds_nxt s < length vs_list"
  shows "aex (phase1_step acyc_flow v s) w = aex s w + (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0)"
proof (cases "imbalance ! v = 0")
  case True
  hence "phase1_step acyc_flow v s = s" by (simp add: phase1_step_def)
  thus ?thesis using True by simp
next
  case nz: False
  have vlt: "v < vcount" using v vs_less_vcount by simp
  show ?thesis
  proof (cases "ds_seen s ! v")
    case True
    have "phase1_step acyc_flow v s = emit_U_edge s v" using nz True by (simp add: phase1_step_def)
    thus ?thesis using emit_U_edge_aex[OF al inb vlt] by simp
  next
    case False
    have "phase1_step acyc_flow v s = open_tree_component acyc_flow s v" using nz False by (simp add: phase1_step_def)
    thus ?thesis using open_tree_component_aex[OF inv al inb vlt] by simp
  qed
qed

lemma fold_phase1_aex:
  assumes "distinct xs" "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "art_len s" "finite E" "E \<subseteq> {v \<in> set vs_list. ds_seen s ! v}" "E \<inter> set xs = {}" "ds_nxt s = card E"
  shows "aex (fold (phase1_step acyc_flow) xs s) w
           = aex s w + (\<Sum>v\<leftarrow>xs. (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0))
         \<and> art_len (fold (phase1_step acyc_flow) xs s)
         \<and> dfs_inv acyc_flow (fold (phase1_step acyc_flow) xs s)
         \<and> ds_stk (fold (phase1_step acyc_flow) xs s) = []
         \<and> (\<exists>E'. finite E' \<and> E' \<subseteq> {v \<in> set vs_list. ds_seen (fold (phase1_step acyc_flow) xs s) ! v}
                 \<and> ds_nxt (fold (phase1_step acyc_flow) xs s) = card E')"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(2) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have Esub: "E \<subseteq> set vs_list" using Cons.prems(7) by auto
  have xnotE: "x \<notin> E" using Cons.prems(8) by auto
  have insub: "insert x E \<subseteq> set vs_list" using Esub xvs by auto
  have cardins: "card (insert x E) \<le> length vs_list" using insub by (rule card_sub_vs_le)
  have inbs: "ds_nxt s < length vs_list"
    using cardins Cons.prems(6,9) xnotE by (simp add: card_insert_disjoint)
  have stepaex: "aex (phase1_step acyc_flow x s) w
                   = aex s w + (if w = x then - imbalance!x else if w = vcount then imbalance!x else 0)"
    using phase1_step_aex[OF xvs Cons.prems(3) Cons.prems(4) Cons.prems(5) inbs] .
  have inv1: "dfs_inv acyc_flow (phase1_step acyc_flow x s)" "ds_stk (phase1_step acyc_flow x s) = []"
    using phase1_step_inv[OF xvs conjI[OF Cons.prems(3) Cons.prems(4)]] by auto
  have al1: "art_len (phase1_step acyc_flow x s)" using phase1_step_art_len[OF xvs Cons.prems(3) Cons.prems(5)] .
  have Emono: "E \<subseteq> {v \<in> set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}"
    using Cons.prems(7) phase1_step_seen_mono[OF Cons.prems(3) xlt] by auto
  have distr: "distinct rest" using Cons.prems(1) by simp
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(2) by simp
  from phase1_step_nxt[OF Cons.prems(3) xlt] show ?case
  proof
    assume A: "ds_nxt (phase1_step acyc_flow x s) = ds_nxt s"
    have card1: "ds_nxt (phase1_step acyc_flow x s) = card E" using A Cons.prems(9) by simp
    have Edisj: "E \<inter> set rest = {}" using Cons.prems(8) by auto
    note IH = Cons.hyps[OF distr subr inv1(1) inv1(2) al1 Cons.prems(6) Emono Edisj card1]
    show ?thesis using IH stepaex by simp
  next
    assume B: "ds_nxt (phase1_step acyc_flow x s) = Suc (ds_nxt s) \<and> ds_seen (phase1_step acyc_flow x s) ! x"
    define E2 where "E2 = insert x E"
    have fin2: "finite E2" using Cons.prems(6) by (simp add: E2_def)
    have E2seen: "E2 \<subseteq> {v \<in> set vs_list. ds_seen (phase1_step acyc_flow x s) ! v}" using Emono B xvs by (auto simp: E2_def)
    have E2disj: "E2 \<inter> set rest = {}" using Cons.prems(8) Cons.prems(1) by (auto simp: E2_def)
    have card2: "ds_nxt (phase1_step acyc_flow x s) = card E2" using B Cons.prems(9) xnotE Cons.prems(6) by (simp add: E2_def card_insert_disjoint)
    note IH = Cons.hyps[OF distr subr inv1(1) inv1(2) al1 fin2 E2seen E2disj card2]
    show ?thesis using IH stepaex by simp
  qed
qed

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
  assumes nz: "imbalance!x \<noteq> 0" and inv: "dfs_inv acyc_flow s" and xlt: "x < vcount"
  shows "ds_seen (phase1_step acyc_flow x s) ! x"
proof (cases "ds_seen s ! x")
  case True thus ?thesis using nz by (simp add: phase1_step_def emit_U_edge_def Let_def)
next
  case False thus ?thesis using nz open_tree_component_marks[OF inv xlt] by (simp add: phase1_step_def)
qed

lemma fold_phase1_imb_seen:
  assumes "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []"
      "ds_seen s ! v \<or> (v \<in> set xs \<and> imbalance!v \<noteq> 0)"
  shows "ds_seen (fold (phase1_step acyc_flow) xs s) ! v"
  using assms
proof (induct xs arbitrary: s)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(1) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have inv': "dfs_inv acyc_flow (phase1_step acyc_flow x s)" "ds_stk (phase1_step acyc_flow x s) = []"
    using phase1_step_inv[OF xvs conjI[OF Cons.prems(2) Cons.prems(3)]] by auto
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(1) by simp
  have "ds_seen (phase1_step acyc_flow x s) ! v \<or> (v \<in> set rest \<and> imbalance!v \<noteq> 0)"
    using Cons.prems(4)
  proof
    assume "ds_seen s ! v"
    hence "ds_seen (phase1_step acyc_flow x s) ! v" using phase1_step_seen_mono[OF Cons.prems(2) xlt] by simp
    thus ?thesis by simp
  next
    assume A: "v \<in> set (x#rest) \<and> imbalance!v \<noteq> 0"
    show ?thesis
    proof (cases "v = x")
      case True
      hence "ds_seen (phase1_step acyc_flow x s) ! v"
        using A phase1_step_marks_imb[OF _ Cons.prems(2) xlt] by auto
      thus ?thesis by simp
    next
      case False
      thus ?thesis using A by simp
    qed
  qed
  thus ?case using Cons.hyps[OF subr inv'(1) inv'(2)] by simp
qed

lemma phase2_step_aex:
  assumes inv: "dfs_inv acyc_flow s" and al: "art_len s" and inb: "ds_nxt s < length vs_list"
      and v: "v \<in> set vs_list" and imb0: "imbalance!v = 0"
  shows "aex (phase2_step acyc_flow v s) w = aex s w"
proof (cases "ds_seen s ! v \<or> is_lonely v")
  case True thus ?thesis by (simp add: phase2_step_def)
next
  case False
  hence notseen: "\<not> ds_seen s ! v" and nl: "\<not> is_lonely v" by auto
  have vlt: "v < vcount" using v vs_less_vcount by simp
  have "phase2_step acyc_flow v s = open_tree_component acyc_flow s v" using notseen nl by (simp add: phase2_step_def)
  thus ?thesis using open_tree_component_aex[OF inv al inb vlt] imb0 by simp
qed

lemma fold_phase2_aex:
  assumes "set xs \<subseteq> set vs_list" "dfs_inv acyc_flow s" "ds_stk s = []" "art_len s"
      "finite E" "E \<subseteq> {u \<in> set vs_list. ds_seen s ! u}" "ds_nxt s = card E"
      "\<forall>u \<in> set vs_list. \<not> ds_seen s ! u \<longrightarrow> imbalance!u = 0"
  shows "aex (fold (phase2_step acyc_flow) xs s) w = aex s w
         \<and> art_len (fold (phase2_step acyc_flow) xs s) \<and> dfs_inv acyc_flow (fold (phase2_step acyc_flow) xs s)
         \<and> ds_stk (fold (phase2_step acyc_flow) xs s) = []
         \<and> (\<forall>u \<in> set vs_list. \<not> ds_seen (fold (phase2_step acyc_flow) xs s) ! u \<longrightarrow> imbalance!u = 0)"
  using assms
proof (induct xs arbitrary: s E)
  case Nil thus ?case by auto
next
  case (Cons x rest)
  have xvs: "x \<in> set vs_list" using Cons.prems(1) by simp
  have xlt: "x < vcount" using xvs vs_less_vcount by simp
  have subr: "set rest \<subseteq> set vs_list" using Cons.prems(1) by simp
  have inv1: "dfs_inv acyc_flow (phase2_step acyc_flow x s)" "ds_stk (phase2_step acyc_flow x s) = []"
    using phase2_step_inv[OF xvs conjI[OF Cons.prems(2) Cons.prems(3)]] by auto
  have al1: "art_len (phase2_step acyc_flow x s)" using phase2_step_art_len[OF xvs Cons.prems(2) Cons.prems(4)] .
  have bal1: "\<forall>u \<in> set vs_list. \<not> ds_seen (phase2_step acyc_flow x s) ! u \<longrightarrow> imbalance!u = 0"
  proof (intro ballI impI)
    fix u assume uvs: "u \<in> set vs_list" and uns: "\<not> ds_seen (phase2_step acyc_flow x s) ! u"
    have ults: "u < vcount" using uvs vs_less_vcount by simp
    have "\<not> ds_seen s ! u" using uns phase2_step_seen_mono[OF Cons.prems(2) xlt] by blast
    thus "imbalance!u = 0" using Cons.prems(8) uvs by simp
  qed
  show ?case
  proof (cases "ds_seen s ! x")
    case seen: True
    have eq: "phase2_step acyc_flow x s = s" by (simp add: phase2_step_def seen)
    have aexeq: "aex (phase2_step acyc_flow x s) w = aex s w" by (simp add: eq)
    have Eeq: "E \<subseteq> {u \<in> set vs_list. ds_seen (phase2_step acyc_flow x s) ! u}" using Cons.prems(6) eq by simp
    have cardeq: "ds_nxt (phase2_step acyc_flow x s) = card E" using Cons.prems(7) eq by simp
    note IH = Cons.hyps[OF subr inv1(1) inv1(2) al1 Cons.prems(5) Eeq cardeq bal1]
    show ?thesis using IH aexeq by simp
  next
    case notseen: False
    show ?thesis
    proof (cases "is_lonely x")
      case lonely: True
      have eq: "phase2_step acyc_flow x s = s" by (simp add: phase2_step_def notseen lonely)
      have aexeq: "aex (phase2_step acyc_flow x s) w = aex s w" by (simp add: eq)
      have Eeq: "E \<subseteq> {u \<in> set vs_list. ds_seen (phase2_step acyc_flow x s) ! u}" using Cons.prems(6) eq by simp
      have cardeq: "ds_nxt (phase2_step acyc_flow x s) = card E" using Cons.prems(7) eq by simp
      note IH = Cons.hyps[OF subr inv1(1) inv1(2) al1 Cons.prems(5) Eeq cardeq bal1]
      show ?thesis using IH aexeq by simp
    next
      case nl: False
      have imb0: "imbalance!x = 0" using Cons.prems(8) xvs notseen by simp
      have xnotE: "x \<notin> E" using Cons.prems(6) notseen by auto
      have insub: "insert x E \<subseteq> set vs_list" using Cons.prems(6) xvs by auto
      have inbs: "ds_nxt s < length vs_list"
        using card_sub_vs_le[OF insub] Cons.prems(5,7) xnotE by (simp add: card_insert_disjoint)
      have aexeq: "aex (phase2_step acyc_flow x s) w = aex s w"
        using phase2_step_aex[OF Cons.prems(2) Cons.prems(4) inbs xvs imb0] .
      have nxt': "ds_nxt (phase2_step acyc_flow x s) = Suc (ds_nxt s)"
        using notseen open_tree_component_art(1)[OF Cons.prems(2) xlt] nl by (simp add: phase2_step_def)
      define E2 where "E2 = insert x E"
      have fin2: "finite E2" using Cons.prems(5) by (simp add: E2_def)
      have xseen1: "ds_seen (phase2_step acyc_flow x s) ! x" using phase2_step_marks[OF Cons.prems(2) xlt nl] .
      have E2seen: "E2 \<subseteq> {u \<in> set vs_list. ds_seen (phase2_step acyc_flow x s) ! u}"
        using Cons.prems(6) phase2_step_seen_mono[OF Cons.prems(2) xlt] xvs xseen1 by (auto simp: E2_def)
      have card2: "ds_nxt (phase2_step acyc_flow x s) = card E2"
        using nxt' Cons.prems(5,7) xnotE by (simp add: E2_def card_insert_disjoint)
      note IH = Cons.hyps[OF subr inv1(1) inv1(2) al1 fin2 E2seen card2 bal1]
      show ?thesis using IH aexeq by simp
    qed
  qed
qed

lemma build_tree_aex:
  assumes w: "w \<in> set vs_list"
  shows "aex (build_tree acyc_flow) w = - imbalance ! w"
proof -
  have invi: "dfs_inv acyc_flow dfs_init" by (rule dfs_init_inv)
  have stki: "ds_stk dfs_init = []" by (simp add: dfs_init_def)
  have E0: "({}::nat set) \<subseteq> {v \<in> set vs_list. ds_seen dfs_init ! v}" by simp
  have E0d: "({}::nat set) \<inter> set vs_list = {}" by simp
  have nxt0: "ds_nxt dfs_init = card ({}::nat set)" by (simp add: dfs_init_def)
  note P1 = fold_phase1_aex[OF distinct_vs_list order_refl invi stki dfs_init_art_len finite.emptyI E0 E0d nxt0, of w]
  have aex_p1: "aex (phase1 acyc_flow dfs_init) w = (\<Sum>v\<leftarrow>vs_list. (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0))"
    using P1 aex_dfs_init unfolding phase1_def by simp
  have al_p1: "art_len (phase1 acyc_flow dfs_init)" using P1 unfolding phase1_def by simp
  have inv_p1: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init)" using P1 unfolding phase1_def by simp
  have stk_p1: "ds_stk (phase1 acyc_flow dfs_init) = []" using P1 unfolding phase1_def by simp
  obtain E1 where E1: "finite E1" "E1 \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}" "ds_nxt (phase1 acyc_flow dfs_init) = card E1"
    using P1 unfolding phase1_def by blast
  have bal: "\<forall>u \<in> set vs_list. \<not> ds_seen (phase1 acyc_flow dfs_init) ! u \<longrightarrow> imbalance!u = 0"
  proof (intro ballI impI)
    fix u assume uvs: "u \<in> set vs_list" and uns: "\<not> ds_seen (phase1 acyc_flow dfs_init) ! u"
    show "imbalance!u = 0"
    proof (rule ccontr)
      assume "imbalance!u \<noteq> 0"
      hence "ds_seen (phase1 acyc_flow dfs_init) ! u"
        using fold_phase1_imb_seen[OF order_refl invi stki] uvs unfolding phase1_def by simp
      thus False using uns by simp
    qed
  qed
  note P2 = fold_phase2_aex[OF order_refl inv_p1 stk_p1 al_p1 E1(1) E1(2) E1(3) bal, of w]
  have aex_p2: "aex (phase2 acyc_flow (phase1 acyc_flow dfs_init)) w = aex (phase1 acyc_flow dfs_init) w"
    using P2 unfolding phase2_def by simp
  have aex_bt: "aex (build_tree acyc_flow) w = aex (phase2 acyc_flow (phase1 acyc_flow dfs_init)) w"
    by (simp add: build_tree_def Let_def aex_lsuc)
  have wnv: "w \<noteq> vcount" using w vs_less_vcount by fastforce
  have "(\<Sum>v\<leftarrow>vs_list. (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0))
      = (\<Sum>v\<leftarrow>vs_list. (if v = w then - imbalance!w else 0))"
    by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (auto simp: wnv)
  also have "\<dots> = (\<Sum>v\<in>set vs_list. (if v = w then - imbalance!w else 0))"
    by (rule sum_list_distinct_conv_sum_set[OF distinct_vs_list])
  also have "\<dots> = - imbalance!w" using w by simp
  finally have sumcollapse: "(\<Sum>v\<leftarrow>vs_list. (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0)) = - imbalance!w" .
  show ?thesis using aex_bt aex_p2 aex_p1 sumcollapse by simp
qed

text \<open>Reindexing @{const aex} at @{const build_tree} to the augmented artificial edge-sums bridges
      the accumulator to @{thm ex_flow_all_decomp}: the artificial part of @{term v}'s augmented
      excess is @{term \<open>aex (build_tree acyc_flow) v\<close>}. Hence for every real vertex the augmented
      excess of @{const flow_all} is the acyclified-flow excess minus @{term \<open>imbalance ! v\<close>}.\<close>

lemma aex_eq_art_part:
  "aex (build_tree acyc_flow) v
     = (\<Sum>e\<in>NS.delta_minus v \<inter> {m..<m+Kart}. flow_all ! e) - (\<Sum>e\<in>NS.delta_plus v \<inter> {m..<m+Kart}. flow_all ! e)"
proof -
  let ?bt = "build_tree acyc_flow"
  have nxtK: "ds_nxt ?bt = Kart" by (simp add: Kart_def)
  have Mcong: "(\<Sum>k = 0..<Kart. if ds_asnd ?bt!k=v then ds_aflw ?bt!k else 0) = (\<Sum>k = 0..<Kart. if snd_all!(m+k)=v then ds_aflw ?bt!k else 0)"
    by (rule sum.cong[OF refl]) (simp add: snd_all_art del: NS.fst_exec_eq NS.snd_exec_eq)
  have Pcong: "(\<Sum>k = 0..<Kart. if ds_afst ?bt!k=v then ds_aflw ?bt!k else 0) = (\<Sum>k = 0..<Kart. if fst_all!(m+k)=v then ds_aflw ?bt!k else 0)"
    by (rule sum.cong[OF refl]) (simp add: fst_all_art del: NS.fst_exec_eq NS.snd_exec_eq)
  have Mrestr: "(\<Sum>k = 0..<Kart. if snd_all!(m+k)=v then ds_aflw ?bt!k else 0) = (\<Sum>k\<in>{k. k < Kart \<and> snd_all!(m+k)=v}. ds_aflw ?bt!k)"
  proof (rule sum.mono_neutral_cong_right)
    show "finite {0..<Kart}" by simp
    show "{k. k < Kart \<and> snd_all!(m+k)=v} \<subseteq> {0..<Kart}" by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)
    show "\<forall>i\<in>{0..<Kart} - {k. k < Kart \<and> snd_all!(m+k)=v}. (if snd_all!(m+i)=v then ds_aflw ?bt!i else 0) = 0"
    proof
      fix i assume "i \<in> {0..<Kart} - {k. k < Kart \<and> snd_all!(m+k)=v}"
      hence "\<not> snd_all!(m+i)=v" by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)
      thus "(if snd_all!(m+i)=v then ds_aflw ?bt!i else 0) = 0" by (rule if_not_P)
    qed
  next
    fix x assume "x \<in> {k. k < Kart \<and> snd_all!(m+k)=v}"
    hence "snd_all!(m+x)=v" by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)
    thus "(if snd_all!(m+x)=v then ds_aflw ?bt!x else 0) = ds_aflw ?bt!x" by (rule if_P)
  qed
  have Prestr: "(\<Sum>k = 0..<Kart. if fst_all!(m+k)=v then ds_aflw ?bt!k else 0) = (\<Sum>k\<in>{k. k < Kart \<and> fst_all!(m+k)=v}. ds_aflw ?bt!k)"
  proof (rule sum.mono_neutral_cong_right)
    show "finite {0..<Kart}" by simp
    show "{k. k < Kart \<and> fst_all!(m+k)=v} \<subseteq> {0..<Kart}" by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)
    show "\<forall>i\<in>{0..<Kart} - {k. k < Kart \<and> fst_all!(m+k)=v}. (if fst_all!(m+i)=v then ds_aflw ?bt!i else 0) = 0"
    proof
      fix i assume "i \<in> {0..<Kart} - {k. k < Kart \<and> fst_all!(m+k)=v}"
      hence "\<not> fst_all!(m+i)=v" by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)
      thus "(if fst_all!(m+i)=v then ds_aflw ?bt!i else 0) = 0" by (rule if_not_P)
    qed
  next
    fix x assume "x \<in> {k. k < Kart \<and> fst_all!(m+k)=v}"
    hence "fst_all!(m+x)=v" by (auto simp del: NS.fst_exec_eq NS.snd_exec_eq)
    thus "(if fst_all!(m+x)=v then ds_aflw ?bt!x else 0) = ds_aflw ?bt!x" by (rule if_P)
  qed
  have "aex ?bt v = (\<Sum>k = 0..<Kart. if ds_asnd ?bt!k=v then ds_aflw ?bt!k else 0) - (\<Sum>k = 0..<Kart. if ds_afst ?bt!k=v then ds_aflw ?bt!k else 0)"
    by (simp add: aex_def nxtK sum_subtractf)
  also have "\<dots> = (\<Sum>k\<in>{k. k<Kart \<and> snd_all!(m+k)=v}. ds_aflw ?bt!k) - (\<Sum>k\<in>{k. k<Kart \<and> fst_all!(m+k)=v}. ds_aflw ?bt!k)"
    by (simp only: Mcong Mrestr Pcong Prestr)
  also have "\<dots> = (\<Sum>e\<in>NS.delta_minus v \<inter> {m..<m+Kart}. flow_all ! e) - (\<Sum>e\<in>NS.delta_plus v \<inter> {m..<m+Kart}. flow_all ! e)"
    by (simp only: art_reindex_minus[symmetric] art_reindex_plus[symmetric])
  finally show ?thesis .
qed

lemma ex_flow_all_real_vertex:
  assumes v: "v \<in> set vs_list"
  shows "NS.ex (h \<circ> nth flow_all) v = original_network.ex (h \<circ> nth acyc_flow) v - h (imbalance!v)"
proof -
  have "h ((\<Sum>e\<in>NS.delta_minus v \<inter> {m..<m+Kart}. flow_all ! e) - (\<Sum>e\<in>NS.delta_plus v \<inter> {m..<m+Kart}. flow_all ! e)) = h (- imbalance!v)"
    using aex_eq_art_part[of v] build_tree_aex[OF v] by simp
  thus ?thesis using ex_flow_all_decomp[of v] by simp
qed

subsection \<open>@{text init_bflow}: the assembled flow is a @{term b_lookup}-flow (Some branch)\<close>

text \<open>The augmented @{const flow_all} is capacity-feasible on both branches
      and, on the @{term Some} branch, balances @{const b_lookup} at every augmented vertex: at a real
      vertex because @{const acyc_flow} preserves the frozen excess (@{thm make_acyclic_ex}) which the
      artificial edge corrects by @{term \<open>imbalance ! v\<close>}, and at the root because the imbalances sum to
      zero. Together these discharge @{text init_bflow}.\<close>

lemma excess_is_orig_ex:
  assumes v: "v < Suc vcount"
  shows "original_network.ex (h \<circ> nth flow_list) v = h (excess ! v)"
proof -
  have dm: "original_network.delta_minus v = {e \<in> {0..<m}. snd_list ! e = v}"
    by (auto simp: original_network.delta_minus_def snd_all_real)
  have dp: "original_network.delta_plus v = {e \<in> {0..<m}. fst_list ! e = v}"
    by (auto simp: original_network.delta_plus_def fst_all_real)
  have key: "\<And>P. (\<Sum>e\<in>{e \<in> {0..<m}. P e}. h (flow_list ! e)) = h (\<Sum>e\<in>{0..<m}. if P e then flow_list ! e else 0)"
  proof -
    fix P :: "nat \<Rightarrow> bool"
    have "h (\<Sum>e\<in>{0..<m}. if P e then flow_list ! e else 0) = (\<Sum>e\<in>{0..<m}. h (if P e then flow_list ! e else 0))"
      by (rule h_sum)
    also have "\<dots> = (\<Sum>e\<in>{0..<m}. if P e then h (flow_list ! e) else 0)"
      by (rule sum.cong[OF refl]) simp
    also have "\<dots> = (\<Sum>e\<in>{e \<in> {0..<m}. P e}. h (flow_list ! e))"
      by (rule sum.mono_neutral_cong_right) auto
    finally show "(\<Sum>e\<in>{e \<in> {0..<m}. P e}. h (flow_list ! e)) = h (\<Sum>e\<in>{0..<m}. if P e then flow_list ! e else 0)" ..
  qed
  have "original_network.ex (h \<circ> nth flow_list) v
      = (\<Sum>e\<in>{e \<in> {0..<m}. snd_list ! e = v}. h (flow_list ! e)) - (\<Sum>e\<in>{e \<in> {0..<m}. fst_list ! e = v}. h (flow_list ! e))"
    by (simp add: original_network.ex_def dm dp comp_def)
  also have "\<dots> = h (\<Sum>e\<in>{0..<m}. if snd_list ! e = v then flow_list ! e else 0) - h (\<Sum>e\<in>{0..<m}. if fst_list ! e = v then flow_list ! e else 0)"
    by (simp only: key)
  also have "\<dots> = h ((\<Sum>e\<in>{0..<m}. if snd_list ! e = v then flow_list ! e else 0) - (\<Sum>e\<in>{0..<m}. if fst_list ! e = v then flow_list ! e else 0))"
    by (simp add: h_diff)
  also have "\<dots> = h (excess ! v)" using excess_nth_sum[OF v] by simp
  finally show ?thesis .
qed

lemma orig_ex_acyc_eq_excess:
  assumes some: "acyc_flow_opt = Some f'" and v: "v < Suc vcount"
  shows "original_network.ex (h \<circ> nth acyc_flow) v = h (excess ! v)"
proof -
  have vv: "vtx_invar \<lparr>vi_list = edged_vs_list, vi_pos = 0\<rparr>"
    using distinct_vs_list by (simp add: vtx_invar_def edged_vs_list_def distinct_filter)
  have vab: "vtx_abstract \<lparr>vi_list = edged_vs_list, vi_pos = 0\<rparr> \<subseteq> original_network.\<V>"
    by (simp add: vtx_abstract_def V_orig_eq_edged)
  have ff: "length flow_list = m" using length_flow length_edges by simp
  have res: "make_acyclic flow_list = Some f'" using some by (simp add: acyc_flow_opt_def)
  have "original_network.ex (h \<circ> (!) f') v = original_network.ex (h \<circ> (!) flow_list) v"
    using make_acyclic_ex[OF multigraph_inv_csr ff af_cap_feasible_flow_list vv vab res] .
  moreover have "acyc_flow = f'" using some by (simp add: acyc_flow_def)
  ultimately show ?thesis using excess_is_orig_ex[OF v] by simp
qed

text \<open>\<^emph>\<open>Pass A's excess for an arbitrary flow.\<close>  @{const excess} is defined as the excess component of
      @{term \<open>passA flow_list\<close>} --- the \<^emph>\<open>frozen\<close> input flow --- but the executable pipeline runs Pass A on
      the \<^emph>\<open>acyclified\<close> flow instead.  The three lemmas below generalise @{thm excess_nth} /
      @{thm excess_is_orig_ex} from @{term flow_list} to any @{term fl} (the underlying fold lemma
      @{thm passA_fold_exc} is already flow-generic), and then close the loop: since the acyclifier
      preserves every vertex's excess (@{thm orig_ex_acyc_eq_excess}) and @{term h} is injective
      (@{thm h_eq_iff}), running Pass A on @{const acyc_flow} yields \<^emph>\<open>literally\<close> @{const excess}.
      This is what lets the imperative refinement identify its in-place excess array --- computed from
      the acyclified flow --- with the functional @{const imbalance}, which is anchored to
      @{const excess}.\<close>

lemma passA_exc_len: "length (fst (snd (passA fl))) = Suc vcount"
  using sized_passA[of fl] by (cases "passA fl") (simp add: sized_def)

lemma passA_exc_nth:
  assumes v: "v < Suc vcount"
  shows "fst (snd (passA fl)) ! v =
           (\<Sum>e\<leftarrow>[0..<m]. (if snd_list ! e = v then fl ! e else 0))
         - (\<Sum>e\<leftarrow>[0..<m]. (if fst_list ! e = v then fl ! e else 0))"
proof -
  have sz0: "sized (replicate m InL, replicate (Suc vcount) (0::'n), (out_lo, out.inp.E_spec),
                (in_lo, inc.inp.E_spec))"
    by (simp add: sized_def length_out_lo length_in_lo length_out_E length_in_E)
  show ?thesis
    using passA_fold_exc[OF sz0 v, where xs = "[0..<m]" and fl = fl] v
    by (simp add: passA_def del: replicate_Suc)
qed

lemma ex_is_passA_exc:
  assumes v: "v < Suc vcount"
  shows "original_network.ex (h \<circ> nth fl) v = h (fst (snd (passA fl)) ! v)"
proof -
  have dm: "original_network.delta_minus v = {e \<in> {0..<m}. snd_list ! e = v}"
    by (auto simp: original_network.delta_minus_def snd_all_real)
  have dp: "original_network.delta_plus v = {e \<in> {0..<m}. fst_list ! e = v}"
    by (auto simp: original_network.delta_plus_def fst_all_real)
  have key: "\<And>P. (\<Sum>e\<in>{e \<in> {0..<m}. P e}. h (fl ! e)) = h (\<Sum>e\<in>{0..<m}. if P e then fl ! e else 0)"
  proof -
    fix P :: "nat \<Rightarrow> bool"
    have "h (\<Sum>e\<in>{0..<m}. if P e then fl ! e else 0) = (\<Sum>e\<in>{0..<m}. h (if P e then fl ! e else 0))"
      by (rule h_sum)
    also have "\<dots> = (\<Sum>e\<in>{0..<m}. if P e then h (fl ! e) else 0)"
      by (rule sum.cong[OF refl]) simp
    also have "\<dots> = (\<Sum>e\<in>{e \<in> {0..<m}. P e}. h (fl ! e))"
      by (rule sum.mono_neutral_cong_right) auto
    finally show "(\<Sum>e\<in>{e \<in> {0..<m}. P e}. h (fl ! e)) = h (\<Sum>e\<in>{0..<m}. if P e then fl ! e else 0)" ..
  qed
  have "original_network.ex (h \<circ> nth fl) v
      = (\<Sum>e\<in>{e \<in> {0..<m}. snd_list ! e = v}. h (fl ! e)) - (\<Sum>e\<in>{e \<in> {0..<m}. fst_list ! e = v}. h (fl ! e))"
    by (simp add: original_network.ex_def dm dp comp_def)
  also have "\<dots> = h (\<Sum>e\<in>{0..<m}. if snd_list ! e = v then fl ! e else 0) - h (\<Sum>e\<in>{0..<m}. if fst_list ! e = v then fl ! e else 0)"
    by (simp only: key)
  also have "\<dots> = h ((\<Sum>e\<in>{0..<m}. if snd_list ! e = v then fl ! e else 0) - (\<Sum>e\<in>{0..<m}. if fst_list ! e = v then fl ! e else 0))"
    by (simp add: h_diff)
  also have "\<dots> = h (fst (snd (passA fl)) ! v)"
    using passA_exc_nth[OF v] by (simp add: interv_sum_list_conv_sum_set_nat)
  finally show ?thesis .
qed

lemma passA_exc_acyc:
  assumes some: "acyc_flow_opt = Some f'"
  shows "fst (snd (passA acyc_flow)) = excess"
proof (rule nth_equalityI)
  show "length (fst (snd (passA acyc_flow))) = length excess"
    by (simp add: passA_exc_len)
next
  fix i assume "i < length (fst (snd (passA acyc_flow)))"
  hence v: "i < Suc vcount" by (simp add: passA_exc_len)
  have "h (fst (snd (passA acyc_flow)) ! i) = original_network.ex (h \<circ> nth acyc_flow) i"
    by (rule ex_is_passA_exc[OF v, symmetric])
  also have "\<dots> = h (excess ! i)" by (rule orig_ex_acyc_eq_excess[OF some v])
  finally show "fst (snd (passA acyc_flow)) ! i = excess ! i" by simp
qed

lemma bflow_flow_all_real:
  assumes some: "acyc_flow_opt = Some f'" and v: "v \<in> set vs_list"
  shows "- NS.ex (h \<circ> nth flow_all) v = h (b_lookup v)"
proof -
  have vlt: "v < vcount" using v vs_less_vcount by simp
  have vlt': "v < Suc vcount" using vlt by simp
  have "NS.ex (h \<circ> nth flow_all) v = original_network.ex (h \<circ> nth acyc_flow) v - h (imbalance!v)" by (rule ex_flow_all_real_vertex[OF v])
  also have "\<dots> = h (excess!v) - h (imbalance!v)" using orig_ex_acyc_eq_excess[OF some vlt'] by simp
  also have "\<dots> = - h (b_lookup v)" using imbalance_nth[OF vlt] by (simp add: h_add)
  finally show ?thesis by simp
qed

lemma aex_build_tree_generic:
  "aex (build_tree acyc_flow) w = (\<Sum>v\<leftarrow>vs_list. (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0))"
proof -
  have invi: "dfs_inv acyc_flow dfs_init" by (rule dfs_init_inv)
  have stki: "ds_stk dfs_init = []" by (simp add: dfs_init_def)
  have E0: "({}::nat set) \<subseteq> {v \<in> set vs_list. ds_seen dfs_init ! v}" by simp
  have E0d: "({}::nat set) \<inter> set vs_list = {}" by simp
  have nxt0: "ds_nxt dfs_init = card ({}::nat set)" by (simp add: dfs_init_def)
  note P1 = fold_phase1_aex[OF distinct_vs_list order_refl invi stki dfs_init_art_len finite.emptyI E0 E0d nxt0, of w]
  have aex_p1: "aex (phase1 acyc_flow dfs_init) w = (\<Sum>v\<leftarrow>vs_list. (if w = v then - imbalance!v else if w = vcount then imbalance!v else 0))"
    using P1 aex_dfs_init unfolding phase1_def by simp
  have al_p1: "art_len (phase1 acyc_flow dfs_init)" using P1 unfolding phase1_def by simp
  have inv_p1: "dfs_inv acyc_flow (phase1 acyc_flow dfs_init)" using P1 unfolding phase1_def by simp
  have stk_p1: "ds_stk (phase1 acyc_flow dfs_init) = []" using P1 unfolding phase1_def by simp
  obtain E1 where E1: "finite E1" "E1 \<subseteq> {v \<in> set vs_list. ds_seen (phase1 acyc_flow dfs_init) ! v}" "ds_nxt (phase1 acyc_flow dfs_init) = card E1"
    using P1 unfolding phase1_def by blast
  have bal: "\<forall>u \<in> set vs_list. \<not> ds_seen (phase1 acyc_flow dfs_init) ! u \<longrightarrow> imbalance!u = 0"
  proof (intro ballI impI)
    fix u assume uvs: "u \<in> set vs_list" and uns: "\<not> ds_seen (phase1 acyc_flow dfs_init) ! u"
    show "imbalance!u = 0"
    proof (rule ccontr)
      assume "imbalance!u \<noteq> 0"
      hence "ds_seen (phase1 acyc_flow dfs_init) ! u"
        using fold_phase1_imb_seen[OF order_refl invi stki] uvs unfolding phase1_def by simp
      thus False using uns by simp
    qed
  qed
  note P2 = fold_phase2_aex[OF order_refl inv_p1 stk_p1 al_p1 E1(1) E1(2) E1(3) bal, of w]
  have aex_p2: "aex (phase2 acyc_flow (phase1 acyc_flow dfs_init)) w = aex (phase1 acyc_flow dfs_init) w"
    using P2 unfolding phase2_def by simp
  have aex_bt: "aex (build_tree acyc_flow) w = aex (phase2 acyc_flow (phase1 acyc_flow dfs_init)) w"
    by (simp add: build_tree_def Let_def aex_lsuc)
  show ?thesis using aex_bt aex_p2 aex_p1 by simp
qed

lemma aex_build_tree_root: "aex (build_tree acyc_flow) vcount = (\<Sum>v\<leftarrow>vs_list. imbalance!v)"
proof -
  have "aex (build_tree acyc_flow) vcount = (\<Sum>v\<leftarrow>vs_list. (if vcount = v then - imbalance!v else if vcount = vcount then imbalance!v else 0))"
    by (rule aex_build_tree_generic)
  also have "\<dots> = (\<Sum>v\<leftarrow>vs_list. imbalance!v)"
    by (rule arg_cong[where f=sum_list], rule map_cong[OF refl]) (auto dest: vs_less_vcount)
  finally show ?thesis .
qed

lemma b_lookup_nonvertex:
  assumes w: "w < Suc vcount" and wv: "w \<notin> set vs_list"
  shows "b_lookup w = 0"
proof -
  have "\<And>v x. (v, x) \<in> set (zip vs_list b_list) \<Longrightarrow> v \<noteq> w"
    using wv by (auto dest: set_zip_leftD)
  hence "b_arr ! w = replicate (Suc vcount) (0::'n) ! w"
    unfolding b_arr_def by (rule foldl_scatter_miss)
  moreover have "replicate (Suc vcount) (0::'n) ! w = 0" using w by (simp add: nth_replicate del: replicate_Suc)
  ultimately show ?thesis by (simp add: b_lookup_def)
qed

lemma imbalance_nonvertex:
  assumes w: "w < Suc vcount" and wv: "w \<notin> set vs_list"
  shows "imbalance ! w = 0"
proof -
  have ex0: "excess ! w = 0"
    using excess_is_orig_ex[OF w] orig_ex_notin_V[OF wv] by simp
  show ?thesis
  proof (cases "w = vcount")
    case True thus ?thesis using ex0 imbalance_root by simp
  next
    case False
    hence nlt: "w < vcount" using w by simp
    show ?thesis using imbalance_nth[OF nlt] ex0 b_lookup_nonvertex[OF w wv] by simp
  qed
qed

lemma sum_imbalance_vs_list_zero: "(\<Sum>v\<leftarrow>vs_list. imbalance!v) = 0"
proof -
  have "(\<Sum>v\<leftarrow>vs_list. imbalance!v) = (\<Sum>v\<in>set vs_list. imbalance!v)"
    by (rule sum_list_distinct_conv_sum_set[OF distinct_vs_list])
  also have "\<dots> = (\<Sum>v\<in>{0..<Suc vcount}. imbalance!v)"
  proof (rule sum.mono_neutral_left)
    show "finite {0..<Suc vcount}" by simp
    show "set vs_list \<subseteq> {0..<Suc vcount}" by (auto dest: vs_less_vcount)
    show "\<forall>v\<in>{0..<Suc vcount} - set vs_list. imbalance!v = 0"
    proof (intro ballI)
      fix v assume "v \<in> {0..<Suc vcount} - set vs_list"
      hence "v < Suc vcount" "v \<notin> set vs_list" by auto
      thus "imbalance!v = 0" by (rule imbalance_nonvertex)
    qed
  qed
  also have "\<dots> = 0" by (rule sum_imbalance_zero)
  finally show ?thesis .
qed

lemma vcount_notin_vs: "vcount \<notin> set vs_list" using vs_less_vcount by fastforce

lemma bflow_flow_all_root: "- NS.ex (h \<circ> nth flow_all) vcount = h (b_lookup vcount)"
proof -
  have "NS.ex (h \<circ> nth flow_all) vcount = original_network.ex (h \<circ> nth acyc_flow) vcount + h (aex (build_tree acyc_flow) vcount)"
    using ex_flow_all_decomp[of vcount] by (simp add: aex_eq_art_part[symmetric])
  also have "\<dots> = 0 + 0"
    using orig_ex_notin_V[OF vcount_notin_vs] aex_build_tree_root sum_imbalance_vs_list_zero by simp
  finally have "NS.ex (h \<circ> nth flow_all) vcount = 0" by simp
  thus ?thesis using b_lookup_root by simp
qed

lemma isuflow_flow_all: "NS.isuflow (h \<circ> nth flow_all)"
proof (unfold NS.isuflow_def comp_def, rule ballI)
  fix e assume e: "e \<in> {0..<m + Kart}"
  hence emK: "e < m + Kart" by simp
  show "ereal (h (nth flow_all e)) \<le> (if e < m + Kart then if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e)) else \<infinity>) \<and> 0 \<le> h (nth flow_all e)"
  proof (cases "e < m")
    case True
    have fe: "nth flow_all e = acyc_flow ! e" using flook[OF emK] flow_all_real[OF True] by simp
    have nn: "0 \<le> acyc_flow ! e" by (rule acyc_flow_nonneg[OF True])
    have cc: "cap_all ! e = capacity_list ! e" by (rule cap_all_real[OF True])
    show ?thesis
    proof (cases "capacity_list ! e = - 1")
      case True thus ?thesis using fe nn cc emK by simp
    next
      case False
      have "acyc_flow ! e \<le> capacity_list ! e" using acyc_flow_le_cap[OF \<open>e < m\<close> False] .
      thus ?thesis using fe nn cc False emK by simp
    qed
  next
    case False
    then obtain k where ek: "e = m + k" by (metis add.commute le_Suc_ex not_less)
    have kK: "k < Kart" using emK ek by simp
    obtain subj where subj: "subj < vcount"
      and aflw: "ds_aflw (build_tree acyc_flow) ! k = art_flow subj"
      and cap: "(ds_aest (build_tree acyc_flow) ! k = InTree \<and> ds_acap (build_tree acyc_flow) ! k = art_tree_cap subj)
              \<or> (ds_aest (build_tree acyc_flow) ! k = InU \<and> ds_acap (build_tree acyc_flow) ! k = art_flow subj)"
      using tail_edge_ok_build_tree[OF kK] by (auto simp: tail_edge_ok_def)
    have fe: "nth flow_all e = art_flow subj" using flook[OF emK] ek kK flow_all_art aflw by simp
    have ce: "cap_all ! e = ds_acap (build_tree acyc_flow) ! k" using ek kK cap_all_art by simp
    have nn: "0 \<le> art_flow subj" by (simp add: art_flow_def)
    have le: "art_flow subj \<le> ds_acap (build_tree acyc_flow) ! k"
      using cap by (auto simp: art_tree_cap_def art_flow_def)
    have cnn: "0 \<le> ds_acap (build_tree acyc_flow) ! k" using nn le by simp
    have "cap_all ! e \<noteq> - 1" using ce cnn by simp
    thus ?thesis using fe ce nn le emK by simp
  qed
qed

lemma NSinit_bflow:
  assumes some: "acyc_flow_opt = Some f'"
  shows "NS.isbflow (h \<circ> nth flow_all) (\<lambda>v. h (b_lookup v))"
proof (rule NS.isbflowI)
  show "NS.isuflow (h \<circ> nth flow_all)" by (rule isuflow_flow_all)
next
  fix v assume vV: "v \<in> NS.\<V>"
  have "v = vcount \<or> v \<in> set vs_list" using vV NS_V_minus_root V_sub_vs_list Vseen_eq_V by auto
  thus "- NS.ex (h \<circ> nth flow_all) v = h (b_lookup v)"
  proof
    assume "v = vcount" thus ?thesis using bflow_flow_all_root by simp
  next
    assume "v \<in> set vs_list" thus ?thesis using bflow_flow_all_real[OF some] by simp
  qed
qed








subsection \<open>Acyclicity of the acyclified flow on the Some branch (architecture keystone)\<close>

text \<open>On the branch where the acyclifier returns a flow (acyc\_flow\_opt = Some), that flow is genuinely
      acyclic: make\_acyclic\_correct\_unconditional certifies it, the freshly-built counting-sort CSRs
      have nothing iterated yet (csr\_lo = csr\_cur), and the vertex list abstracts to exactly the vertex
      set. This is the hypothesis under which the initial-basis interpretation's acyclicity-dependent
      obligations (free-edge coverage / init\_partition) become provable; it is discharged at the use
      site, inside solve on the Some branch.\<close>

lemma out_in_csr_fresh:
  "out.graph.csr_iterated ((!) out.inp.B_spec) u = {}" "inc.graph.csr_iterated ((!) inc.inp.B_spec) u = {}"
  by (simp_all add: out.graph.csr_iterated_def inc.graph.csr_iterated_def out.graph.seg_def
                    inc.graph.seg_def)

lemma acyc_of_some:
  assumes some: "acyc_flow_opt = Some f'"
  shows "original_network.acyclic_flow (h \<circ> nth acyc_flow)"
proof -
  have vv: "vtx_invar \<lparr>vi_list = edged_vs_list, vi_pos = 0\<rparr>"
    using distinct_vs_list by (simp add: vtx_invar_def edged_vs_list_def distinct_filter)
  have vabsV: "vtx_abstract \<lparr>vi_list = edged_vs_list, vi_pos = 0\<rparr> = original_network.\<V>"
    by (simp add: vtx_abstract_def V_orig_eq_edged)
  have vit0: "vtx_iterated \<lparr>vi_list = edged_vs_list, vi_pos = 0\<rparr> = {}" by (simp add: vtx_iterated_def)
  have ff: "length flow_list = m" using length_flow length_edges by simp
  have fresh: "\<forall>u. out.graph.csr_iterated ((!) out.inp.B_spec) u = {} \<and> inc.graph.csr_iterated ((!) inc.inp.B_spec) u = {}"
    using out_in_csr_fresh by simp
  have res: "make_acyclic flow_list = Some f'" using some by (simp add: acyc_flow_opt_def)
  have "original_network.acyclic_flow (h \<circ> (!) f')"
    using make_acyclic_correct_unconditional[OF multigraph_inv_csr ff af_cap_feasible_flow_list vv vabsV vit0 fresh res] by blast
  thus ?thesis using some by (simp add: acyc_flow_def)
qed





lemma solve_none: "acyc_flow_opt = None \<Longrightarrow> solve = Neg_inf_cycle" by (simp add: solve_def)

lemma NSinit_bflow_ne:
  assumes "acyc_flow_opt \<noteq> None" shows "NS.isbflow (h \<circ> nth flow_all) (\<lambda>v. h (b_lookup v))"
  using assms by (cases acyc_flow_opt) (auto intro: NSinit_bflow)

lemma NSinit_partition_ne:
  assumes ne: "acyc_flow_opt \<noteq> None"
  shows "NS.spanning_tree_partition vcount ((!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})) {e \<in> {0..<m + Kart}. state_all ! e = InL} {e \<in> {0..<m + Kart}. state_all ! e = InU}"
proof -
  obtain f' where sf: "acyc_flow_opt = Some f'" using ne by (cases acyc_flow_opt) auto
  show ?thesis by (rule NSinit_partition[OF acyc_of_some[OF sf]])
qed

text \<open>Relabelling a spanning-tree partition: the tree-structure conjuncts depend only on @{term T},
      so any @{term L'} / @{term U'} that cover the same edges and stay disjoint from @{term T} and
      each other yield another valid partition. This lets the augmented (cost-folded) self-loop
      partition reuse the plain tag partition's arborescence facts.\<close>

lemma spanning_tree_partition_relabel:
  assumes p: "NS.spanning_tree_partition r T L U"
    and cov: "T \<union> U' \<union> L' = T \<union> U \<union> L"
    and d1: "T \<inter> U' = {}" and d2: "T \<inter> L' = {}" and d3: "L' \<inter> U' = {}"
  shows "NS.spanning_tree_partition r T L' U'"
proof -
  note pd = p[unfolded NS.spanning_tree_partition_def]
  have cov': "{0..<m + Kart} = T \<union> U' \<union> L'"
  proof -
    have "{0..<m + Kart} = T \<union> U \<union> L" using pd by simp
    thus ?thesis using cov by simp
  qed
  show ?thesis
    unfolding NS.spanning_tree_partition_def
    using cov' d1 d2 d3 pd by blast
qed

text \<open>Artificial edges run between a component root and the artificial root @{const vcount}, which are
      distinct, so no artificial edge is a self-loop.\<close>

lemma art_not_selfloop:
  assumes k: "m \<le> e" and elt: "e < m + Kart"
  shows "fst_all ! e \<noteq> snd_all ! e"
proof -
  obtain k' where k': "e = m + k'" and kK: "k' < Kart"
    using k elt by (metis add.commute le_Suc_ex nat_add_left_cancel_less add_diff_inverse_nat not_le)
  have tok: "tail_edge_ok (build_tree acyc_flow) k'" using kK tail_edge_ok_build_tree by simp
  then obtain subj where s1: "subj < vcount"
      and s2: "ds_afst (build_tree acyc_flow) ! k' = (if art_dir subj then subj else vcount)"
      and s3: "ds_asnd (build_tree acyc_flow) ! k' = (if art_dir subj then vcount else subj)"
    unfolding tail_edge_ok_def by auto
  have fa: "fst_all ! e = ds_afst (build_tree acyc_flow) ! k'" unfolding k' by (rule fst_all_art[OF kK])
  have sa: "snd_all ! e = ds_asnd (build_tree acyc_flow) ! k'" unfolding k' by (rule snd_all_art[OF kK])
  have neq: "subj \<noteq> vcount" using less_imp_neq[OF s1] .
  show ?thesis using fa sa s2 s3 neq by (cases "art_dir subj") auto
qed

text \<open>\<open>make_acyclic_selfloop\<close>, specialised to the acyclified flow @{const acyc_flow} of the Some
      branch: a real self-loop is emptied when its cost is non-negative and saturated when negative.\<close>

lemma acyc_flow_selfloop:
  assumes ne: "acyc_flow_opt \<noteq> None" and em: "e < m" and esl: "fst_list ! e = snd_list ! e"
  shows "(0 \<le> cost_list ! e \<longrightarrow> acyc_flow ! e = 0) \<and> (cost_list ! e < 0 \<longrightarrow> acyc_flow ! e = capacity_list ! e)"
proof -
  obtain f' where sf: "acyc_flow_opt = Some f'" using ne by (cases acyc_flow_opt) auto
  have vv: "vtx_invar \<lparr>vi_list = edged_vs_list, vi_pos = 0\<rparr>"
    using distinct_vs_list by (simp add: vtx_invar_def edged_vs_list_def distinct_filter)
  have vabsV: "vtx_abstract \<lparr>vi_list = edged_vs_list, vi_pos = 0\<rparr> = original_network.\<V>"
    by (simp add: vtx_abstract_def V_orig_eq_edged)
  have vit0: "vtx_iterated \<lparr>vi_list = edged_vs_list, vi_pos = 0\<rparr> = {}" by (simp add: vtx_iterated_def)
  have ff: "length flow_list = m" using length_flow length_edges by simp
  have fresh: "\<forall>u. out.graph.csr_iterated ((!) out.inp.B_spec) u = {} \<and> inc.graph.csr_iterated ((!) inc.inp.B_spec) u = {}" using out_in_csr_fresh by simp
  have res: "make_acyclic flow_list = Some f'" using sf by (simp add: acyc_flow_opt_def)
  have af: "acyc_flow = f'" using sf by (simp add: acyc_flow_def)
  have eE: "e \<in> {0..<m}" using em by simp
  have main: "(0 \<le> cost_list ! e \<longrightarrow> f' ! e = 0) \<and> (cost_list ! e < 0 \<longrightarrow> f' ! e = capacity_list ! e)"
    using make_acyclic_selfloop[OF multigraph_inv_csr ff af_cap_feasible_flow_list vv vabsV vit0 res fresh eE] esl em by simp
  thus ?thesis using af by simp
qed

text \<open>Obligation (\<open>init_selfloop\<close>): a self-loop of the initial basis carries the cost-directed
      bound the acyclifier fixes --- zero flow when @{term \<open>0 \<le> \<c>\<close>}, saturation when @{term \<open>\<c> < 0\<close>}.
      Artificial edges are not self-loops, so only the real edges contribute, discharged by
      @{thm acyc_flow_selfloop}; feasibility rules out the infinite-capacity negative case.\<close>

lemma NSinit_selfloop:
  assumes ne: "acyc_flow_opt \<noteq> None"
  shows "\<forall>e\<in>{0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))) = (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) \<longrightarrow> (0 \<le> cost_all ! e \<longrightarrow> flow_all ! e = 0) \<and> (cost_all ! e < 0 \<longrightarrow> ereal (h (flow_all ! e)) = (if e < m + Kart then if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e)) else \<infinity>))"
proof (intro ballI impI)
  fix e assume e: "e \<in> {0..<m + Kart}"
    and sl: "(if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))) = (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart))))"
  have elt: "e < m + Kart" using e by simp
  have slr: "fst_all ! e = snd_all ! e" using sl elt by argo
  have em: "e < m" using slr elt art_not_selfloop by (metis not_le)
  have flr: "fst_list ! e = snd_list ! e" using slr fst_all_real[OF em] snd_all_real[OF em] by simp
  have core: "(0 \<le> cost_list ! e \<longrightarrow> acyc_flow ! e = 0) \<and> (cost_list ! e < 0 \<longrightarrow> acyc_flow ! e = capacity_list ! e)"
    using acyc_flow_selfloop[OF ne em flr] .
  have ce: "cost_all ! e = h (cost_list ! e)" using cost_all_real[OF em] .
  have fe: "flow_all ! e = acyc_flow ! e" using flow_all_real[OF em] .
  have cae: "cap_all ! e = capacity_list ! e" using cap_all_real[OF em] .
  show "(0 \<le> cost_all ! e \<longrightarrow> flow_all ! e = 0) \<and> (cost_all ! e < 0 \<longrightarrow> ereal (h (flow_all ! e)) = (if e < m + Kart then if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e)) else \<infinity>))"
  proof (intro conjI impI)
    assume "0 \<le> cost_all ! e"
    thus "flow_all ! e = 0" using core ce fe by simp
  next
    assume neg: "cost_all ! e < 0"
    hence fcap: "flow_all ! e = capacity_list ! e" using core ce fe by simp
    have "0 \<le> acyc_flow ! e" using acyc_flow_nonneg[OF em] .
    hence "cap_all ! e \<noteq> - 1" using fcap fe cae by simp
    thus "ereal (h (flow_all ! e)) = (if e < m + Kart then if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e)) else \<infinity>)"
      using fcap cae elt by simp
  qed
qed

text \<open>Obligation (\<open>init_flow_fits\<close>) in its non-self-loop form: it follows by monotonicity from
      the full flow fit @{thm NSinit_flow_fits} (fewer edges are constrained).\<close>

lemma NSinit_flow_fits_ns:
  "NS.flow_fits_spanning_tree_partition ((!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})) {e \<in> {0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))) \<noteq> (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) \<and> state_all ! e = InL} {e \<in> {0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))) \<noteq> (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) \<and> state_all ! e = InU} (h \<circ> (!) flow_all)"
  using NSinit_flow_fits by (auto simp: NS.flow_fits_spanning_tree_partition_def comp_def)

text \<open>Obligation (\<open>init_partition\<close>): the augmented partition folds self-loops into @{term L} /
      @{term U} by cost. It reuses the plain tag partition's tree facts via
      @{thm spanning_tree_partition_relabel}; the cover matches because every self-loop is covered by
      the cost split, and the tree carries no self-loop (@{thm art_not_selfloop} / the graph invariant).\<close>

lemma NSinit_partition_aug:
  assumes ne: "acyc_flow_opt \<noteq> None"
  shows "NS.spanning_tree_partition vcount ((!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})) ({e \<in> {0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))) \<noteq> (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) \<and> state_all ! e = InL} \<union> NS.ns_selfloops_L) ({e \<in> {0..<m + Kart}. (if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))) \<noteq> (if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))) \<and> state_all ! e = InU} \<union> NS.ns_selfloops_U)"
proof -
  obtain f' where sf: "acyc_flow_opt = Some f'" using ne by (cases acyc_flow_opt) auto
  have acyc: "original_network.acyclic_flow (h \<circ> nth acyc_flow)" using acyc_of_some[OF sf] .
  let ?T = "(!) (ds_par (build_tree acyc_flow)) ` (NS.\<V> - {vcount})"
  let ?L = "{e \<in> {0..<m + Kart}. state_all ! e = InL}"
  let ?U = "{e \<in> {0..<m + Kart}. state_all ! e = InU}"
  let ?F = "\<lambda>e. if e < m + Kart then fst_all ! e else fst (prod_decode (e - (m + Kart)))"
  let ?S = "\<lambda>e. if e < m + Kart then snd_all ! e else snd (prod_decode (e - (m + Kart)))"
  let ?aL = "{e \<in> {0..<m + Kart}. ?F e \<noteq> ?S e \<and> state_all ! e = InL} \<union> NS.ns_selfloops_L"
  let ?aU = "{e \<in> {0..<m + Kart}. ?F e \<noteq> ?S e \<and> state_all ! e = InU} \<union> NS.ns_selfloops_U"
  have plain: "NS.spanning_tree_partition vcount ?T ?L ?U" using NSinit_partition[OF acyc] .
  note pd = plain[unfolded NS.spanning_tree_partition_def]
  have coverP: "{0..<m + Kart} = ?T \<union> ?U \<union> ?L" using pd by argo
  have dTU: "?T \<inter> ?U = {}" using pd by blast
  have dTL: "?T \<inter> ?L = {}" using pd by blast
  have slL: "NS.ns_selfloops_L = {e \<in> {0..<m + Kart}. ?F e = ?S e \<and> 0 \<le> cost_all ! e}"
    by (simp add: NS.ns_selfloops_L_def)
  have slU: "NS.ns_selfloops_U = {e \<in> {0..<m + Kart}. ?F e = ?S e \<and> cost_all ! e < 0}"
    by (simp add: NS.ns_selfloops_U_def)
  have Tnsl: "\<And>d. d \<in> ?T \<Longrightarrow> ?F d \<noteq> ?S d"
  proof -
    fix d assume d: "d \<in> ?T"
    have mem: "{?F d, ?S d} \<in> abstract_arb Sarb" using d tc_image by blast
    have dbl: "dblton_graph (abstract_arb Sarb)" using graph_invar_abstract_arb[OF arb_invar_Sarb] by simp
    obtain u v where uv: "{?F d, ?S d} = {u, v}" and une: "u \<noteq> v" using dbl mem unfolding dblton_graph_def by blast
    show "?F d \<noteq> ?S d"
    proof
      assume "?F d = ?S d"
      hence "{u, v} = {?F d}" using uv by simp
      thus False using une by blast
    qed
  qed
  \<comment> \<open>Arithmetic facts fed to @{method blast} (which cannot do them itself); @{method blast} keeps the
      @{term ?F} / @{term ?S} \<open>if\<close>-lambdas opaque, so it never diverges on @{term prod_decode}.\<close>
  have cost_tri: "\<And>x. cost_all ! x < 0 \<or> 0 \<le> cost_all ! x" by auto
  have cost_contra: "\<And>x. 0 \<le> cost_all ! x \<Longrightarrow> cost_all ! x < 0 \<Longrightarrow> False" by simp
  show ?thesis
  proof (rule spanning_tree_partition_relabel[OF plain])
    show "?T \<union> ?aU \<union> ?aL = ?T \<union> ?U \<union> ?L" using coverP cost_tri unfolding slL slU by blast
    show "?T \<inter> ?aU = {}" using dTU Tnsl unfolding slU by blast
    show "?T \<inter> ?aL = {}" using dTL Tnsl unfolding slL by blast
    show "?aL \<inter> ?aU = {}"
    proof (rule equals0I)
      fix x assume xin: "x \<in> ?aL \<inter> ?aU"
      have xLd: "x \<in> {e \<in> {0..<m + Kart}. ?F e \<noteq> ?S e \<and> state_all ! e = InL} \<or> x \<in> NS.ns_selfloops_L"
        using xin by blast
      have xUd: "x \<in> {e \<in> {0..<m + Kart}. ?F e \<noteq> ?S e \<and> state_all ! e = InU} \<or> x \<in> NS.ns_selfloops_U"
        using xin by blast
      from xLd xUd show False
      proof (elim disjE)
        assume a: "x \<in> {e \<in> {0..<m + Kart}. ?F e \<noteq> ?S e \<and> state_all ! e = InL}"
          and b: "x \<in> {e \<in> {0..<m + Kart}. ?F e \<noteq> ?S e \<and> state_all ! e = InU}"
        have "state_all ! x = InL" using a by blast
        moreover have "state_all ! x = InU" using b by blast
        ultimately show False by simp
      next
        assume a: "x \<in> {e \<in> {0..<m + Kart}. ?F e \<noteq> ?S e \<and> state_all ! e = InL}"
          and b: "x \<in> NS.ns_selfloops_U"
        have "?F x \<noteq> ?S x" using a by blast
        moreover have "?F x = ?S x" using b unfolding slU by blast
        ultimately show False by simp
      next
        assume a: "x \<in> NS.ns_selfloops_L"
          and b: "x \<in> {e \<in> {0..<m + Kart}. ?F e \<noteq> ?S e \<and> state_all ! e = InU}"
        have "?F x = ?S x" using a unfolding slL by blast
        moreover have "?F x \<noteq> ?S x" using b by blast
        ultimately show False by simp
      next
        assume a: "x \<in> NS.ns_selfloops_L" and b: "x \<in> NS.ns_selfloops_U"
        have "0 \<le> cost_all ! x" using a unfolding slL by blast
        moreover have "cost_all ! x < 0" using b unfolding slU by blast
        ultimately show False by linarith
      qed
    qed
  qed
qed


context
  assumes some: "acyc_flow_opt \<noteq> None"
begin

interpretation NSinit: network_simplex_init
  where fst = "\<lambda> e. if e < m+Kart then fst_all ! e else Product_Type.fst (prod_decode (e - (m+Kart)))"
    and snd = "\<lambda> e. if e < m+Kart then snd_all ! e else Product_Type.snd (prod_decode (e - (m+Kart)))"
    and create_edge = "\<lambda> u v. (m+Kart) + prod_encode (u, v)"
    and \<E> = "{0..<m+Kart}"
    and \<u> = "\<lambda> e. if e < m+Kart then (if cap_all ! e = - 1 then \<infinity> else ereal (h (cap_all ! e))) else \<infinity>"
    and \<c> = "\<lambda> e. cost_all ! e"
    and r = vcount
    and shift_pot = shift_pot_impl
    and arborescense_invar = "arb_invar vcount Varb"
    and abstract_arborescense = abstract_arb
    and get_path_pair = get_path_pair_impl
    and swap_edge = swap_edge_impl
    and flow_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and flow_upd = list_update and flow_lookup = nth
    and pot_invar = "\<lambda>xs. \<forall>v\<in>Varb. v < length xs" and pot_upd = list_update and pot_lookup = nth
    and parent_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and parent_upd = list_update and parent_lookup = nth
    and dir_invar = "\<lambda>xs. \<forall>v\<in>Varb - {vcount}. v < length xs" and dir_upd = list_update and dir_lookup = nth
    and es_invar = "\<lambda>xs. \<forall>k\<in>{0..<m+Kart}. k < length xs" and es_upd = list_update and es_lookup = nth
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

lemma solve_init_state:
  "network_simplex_init_spec.init_state flow_all (ds_pot art_tree) (tree_st art_tree)
      (ds_par art_tree) (ds_dir art_tree) state_all init_sel = NSinit.init_state"
  by (simp add: NSinit.init_state_def network_simplex_init_spec.init_state_def Sarb_tree_st)

lemma solve_loop_eq:
  "NS.ns_loop_impl (network_simplex_init_spec.init_state flow_all (ds_pot art_tree) (tree_st art_tree)
      (ds_par art_tree) (ds_dir art_tree) state_all init_sel) = NS.ns_loop NSinit.init_state"
  unfolding solve_init_state
  by (rule NS.ns_loop_dom_impl_same[OF NSinit.network_simplex_correct(1)])

lemma solve_eq:
  "solve = (case acyc_flow_opt of None \<Rightarrow> Neg_inf_cycle
            | Some _ \<Rightarrow> (let s = NS.ns_loop NSinit.init_state; f = current_flow s
                        in if return s = unbounded then Neg_inf_cycle
                           else if list_all (\<lambda>k. f ! k = 0) [m..<m + Kart]
                                then Optimum (take m f) else Infeasible))"
  by (simp only: solve_def solve_loop_eq Let_def)

lemma ns_loop_success:
  assumes "return (NS.ns_loop NSinit.init_state) \<noteq> unbounded"
  shows "return (NS.ns_loop NSinit.init_state) = success"
  using ns_loop_terminates[OF NSinit.network_simplex_correct(1)] assms by blast

lemma solve_not_negI:
  assumes Some: "acyc_flow_opt = Some f'"
    and nu: "return (NS.ns_loop NSinit.init_state) \<noteq> unbounded"
  shows "solve = (if list_all (\<lambda>k. current_flow (NS.ns_loop NSinit.init_state) ! k = 0) [m..<m + Kart]
                  then Optimum (take m (current_flow (NS.ns_loop NSinit.init_state))) else Infeasible)"
  unfolding solve_eq Some option.simps Let_def using nu by (rule if_not_P)

lemma solve_ne_neg:
  assumes "acyc_flow_opt = Some f'" and "return (NS.ns_loop NSinit.init_state) \<noteq> unbounded"
  shows "solve \<noteq> Neg_inf_cycle"
  using solve_not_negI[OF assms] by simp

lemma solve_neg_inf:
  assumes nc: "solve = Neg_inf_cycle" shows neg_infty_cycle
proof (cases acyc_flow_opt)
  case None
  show ?thesis by (rule acyc_none_neg_cycle[OF None])
next
  case (Some f')
  show ?thesis
  proof (cases "return (NS.ns_loop NSinit.init_state) = unbounded")
    case True
    show ?thesis by (rule aug_neg_cycle_orig[OF NSinit.network_simplex_correct(2)[OF True]])
  next
    case False
    show ?thesis using solve_ne_neg[OF Some False] nc by simp
  qed
qed

lemma flow_all_len: "m \<le> length (current_flow (NS.ns_loop NSinit.init_state))"
proof -
  have "NS.ns_invar (NS.ns_loop NSinit.init_state)"
    by (rule ns_loop_invar[OF NSinit.network_simplex_correct(1) NSinit.init_state_invar])
  hence fi: "\<forall>k\<in>{0..<m + Kart}. k < length (current_flow (NS.ns_loop NSinit.init_state))"
    by (simp add: NS.ns_invar_def NS.ns_invar_impl_def)
  have "m + Kart - 1 < length (current_flow (NS.ns_loop NSinit.init_state))"
    using fi Kart_pos by simp
  thus ?thesis using Kart_pos by simp
qed

theorem solve_correct_some:
  "solve = Optimum fs \<Longrightarrow> length fs = m \<and> original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth fs)"
  "solve = Infeasible \<Longrightarrow> \<nexists> f. original_network.isbflow f (\<lambda>v. h (b_lookup v))"
  "solve = Neg_inf_cycle \<Longrightarrow> neg_infty_cycle"
proof -
  show "solve = Neg_inf_cycle \<Longrightarrow> neg_infty_cycle" by (rule solve_neg_inf)
next
  assume A: "solve = Optimum fs"
  obtain f' where Some: "acyc_flow_opt = Some f'"
    using A by (cases acyc_flow_opt) (simp_all add: solve_eq)
  have nu: "return (NS.ns_loop NSinit.init_state) \<noteq> unbounded"
    using A solve_eq Some by (simp add: Let_def split: if_splits)
  note eq = solve_not_negI[OF Some nu]
  have la: "list_all (\<lambda>k. current_flow (NS.ns_loop NSinit.init_state) ! k = 0) [m..<m + Kart]"
    using A eq by (simp split: if_splits)
  have fs: "fs = take m (current_flow (NS.ns_loop NSinit.init_state))"
    using A eq la by simp
  have len: "length fs = m" using fs flow_all_len by simp
  have zero: "NS.ns_flow_of (NS.ns_loop NSinit.init_state) k = 0" if "m \<le> k" "k < m + Kart" for k
    using la that by (simp add: list_all_iff)
  have "original_network.is_Opt (\<lambda>v. h (b_lookup v)) (NS.ns_flow_of (NS.ns_loop NSinit.init_state))"
    by (rule aug_opt_zero_art_orig_opt[OF NSinit.network_simplex_correct(3)[OF ns_loop_success[OF nu]] zero])
  hence "original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth fs)"
    using fs is_Opt_take[OF flow_all_len] by simp
  thus "length fs = m \<and> original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth fs)" using len by simp
next
  assume A: "solve = Infeasible"
  obtain f' where Some: "acyc_flow_opt = Some f'"
    using A by (cases acyc_flow_opt) (simp_all add: solve_eq)
  have nu: "return (NS.ns_loop NSinit.init_state) \<noteq> unbounded"
    using A solve_eq Some by (simp add: Let_def split: if_splits)
  note eq = solve_not_negI[OF Some nu]
  have "\<not> list_all (\<lambda>k. current_flow (NS.ns_loop NSinit.init_state) ! k = 0) [m..<m + Kart]"
    using A eq by (simp split: if_splits)
  hence nzex: "\<exists>k. m \<le> k \<and> k < m + Kart \<and> NS.ns_flow_of (NS.ns_loop NSinit.init_state) k \<noteq> 0"
    by (auto simp: list_all_iff)
  have succ: "return (NS.ns_loop NSinit.init_state) = success" by (rule ns_loop_success[OF nu])
  have opt3: "NS.is_Opt (\<lambda>v. h (b_lookup v)) (NS.ns_flow_of (NS.ns_loop NSinit.init_state))"
    by (rule NSinit.network_simplex_correct(3)[OF succ])
  note infd = aug_opt_nonzero_art_infeasible[OF opt3 nzex]
  show "\<nexists> f. original_network.isbflow f (\<lambda>v. h (b_lookup v))" by (fact infd)
qed

end

theorem solve_correct:
  "solve = Optimum fs \<Longrightarrow> length fs = m \<and> original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth fs)"
  "solve = Infeasible \<Longrightarrow> \<nexists> f. original_network.isbflow f (\<lambda>v. h (b_lookup v))"
  "solve = Neg_inf_cycle \<Longrightarrow> neg_infty_cycle"
proof -
  show "solve = Neg_inf_cycle \<Longrightarrow> neg_infty_cycle"
  proof -
    assume A: "solve = Neg_inf_cycle"
    show neg_infty_cycle
    proof (cases acyc_flow_opt)
      case None thus ?thesis by (rule acyc_none_neg_cycle)
    next
      case (Some f') hence "acyc_flow_opt \<noteq> None" by simp
      thus ?thesis using A solve_correct_some(3) by blast
    qed
  qed
next
  assume A: "solve = Optimum fs"
  have ne: "acyc_flow_opt \<noteq> None" using A solve_none by auto
  show "length fs = m \<and> original_network.is_Opt (\<lambda>v. h (b_lookup v)) (h \<circ> nth fs)" using solve_correct_some(1)[OF ne A] .
next
  assume A: "solve = Infeasible"
  have ne: "acyc_flow_opt \<noteq> None" using A solve_none by auto
  show "\<nexists> f. original_network.isbflow f (\<lambda>v. h (b_lookup v))" 
    using solve_correct_some(2)[OF ne A] .
qed


end
thm initial_basis_selector.solve_correct
thm initial_basis_selector_def
end