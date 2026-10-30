theory Matching_Augmentation_Imperative
  imports
    Data_Structures.Fixed_Univ_Map_Specs_Imp
    Basic_Matching.Matching_Augmentation_Executable
begin

provenance ai


section \<open>Imperative Augmentation of Matchings\<close>

text \<open>This is the imperative counterpart of @{locale Matching_Augmentation_Specs}. It is generic in
      the buddy map and uses the imperative fixed-universe map only through its interface. The
      buddy map is updated in place. The augmenting path is not a list but the prefix of length
      @{term k} of an array, which belongs to the caller. The program does not allocate.\<close>

locale matching_augmentation_imp =
  Matching_Augmentation_Specs K buddy_invar buddy_upd buddy_get buddy_empty nil +
  bm: fixed_univ_map_imp K buddy_invar buddy_upd buddy_get id buddy_assn buddy_upd_imp
    buddy_get_imp
  for K :: "'v::heap set" and buddy_invar and buddy_upd :: "'buddy \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'buddy"
    and buddy_get buddy_empty nil
    and buddy_assn :: "'buddy \<Rightarrow> 'bi \<Rightarrow> assn" and buddy_upd_imp buddy_get_imp
begin

lemma buddy_get_rule[sep_heap_rules]:
  "\<lbrakk>buddy_invar M; u \<in> K\<rbrakk> \<Longrightarrow>
   <buddy_assn M Bi> buddy_get_imp Bi u <\<lambda>r. buddy_assn M Bi * \<up>(r = buddy_get M u)>"
  using bm.fixed_univ_map_lookup_rule[of M u Bi]
  by simp

lemma buddy_upd_rule[sep_heap_rules]:
  "\<lbrakk>buddy_invar M; u \<in> K\<rbrakk> \<Longrightarrow>
   <buddy_assn M Bi> buddy_upd_imp Bi u v <\<lambda>_. buddy_assn (buddy_upd M u v) Bi>"
  using bm.fixed_univ_map_upd_rule[of M u Bi v]
  by simp

partial_function (heap) augment_loop :: "'bi \<Rightarrow> 'v array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "augment_loop Bi Ra i k =
     (if i + 1 < k
      then do { u \<leftarrow> Array.nth Ra i;
                v \<leftarrow> Array.nth Ra (i + 1);
                buddy_upd_imp Bi u v;
                buddy_upd_imp Bi v u;
                augment_loop Bi Ra (i + 2) k }
      else return ())"

definition "augment_imp Bi Ra k = augment_loop Bi Ra 0 k"

lemma augment_impl_short:
  "length p \<le> 1 \<Longrightarrow> augment_impl M p = M"
  by (cases "(M, p)" rule: augment_impl.cases) auto

lemma augment_loop_rule:
  "\<lbrakk>buddy_invar M; k \<le> length xs; set (drop i (take k xs)) \<subseteq> K\<rbrakk> \<Longrightarrow>
   <buddy_assn M Bi * Ra \<mapsto>\<^sub>a xs> augment_loop Bi Ra i k
   <\<lambda>_. buddy_assn (augment_impl M (drop i (take k xs))) Bi * Ra \<mapsto>\<^sub>a xs>"
proof(induction "k - i" arbitrary: i M rule: less_induct)
  case IH: less
  show ?case
  proof(cases "i + 1 < k")
    case True
    have path: "drop i (take k xs) = xs ! i # xs ! (i + 1) # drop (i + 2) (take k xs)"
      using True IH.prems
      by (simp add: drop_take_Cons_Cons)
    show ?thesis
      using True IH.prems
      by (subst augment_loop.simps)
         (sep_auto heap: IH.hyps buddy_upd_rule
                   simp: path buddy_map.fixed_univ_map_upd_invar)
  next
    case False
    thus ?thesis
      by (subst augment_loop.simps) (sep_auto simp: augment_impl_short)
  qed
qed

lemma augment_imp_rule:
  "\<lbrakk>buddy_invar M; k \<le> length xs; set (take k xs) \<subseteq> K\<rbrakk> \<Longrightarrow>
   <buddy_assn M Bi * Ra \<mapsto>\<^sub>a xs> augment_imp Bi Ra k
   <\<lambda>_. buddy_assn (augment_impl M (take k xs)) Bi * Ra \<mapsto>\<^sub>a xs>"
  unfolding augment_imp_def
  using augment_loop_rule[of M k xs 0]
  by simp

text \<open>Rematching in place: three writes into the buddy map.\<close>

definition "rematch_imp Bi l r = do {
   lq \<leftarrow> buddy_get_imp Bi r;
   buddy_upd_imp Bi lq nil;
   buddy_upd_imp Bi r l;
   buddy_upd_imp Bi l r }"

lemma rematch_imp_rule:
  "\<lbrakk>buddy_invar M; l \<in> K; r \<in> K; buddy_get M r \<in> K\<rbrakk> \<Longrightarrow>
   <buddy_assn M Bi> rematch_imp Bi l r <\<lambda>_. buddy_assn (rematch M l r) Bi>"
  unfolding rematch_imp_def rematch_def
  by (sep_auto heap: buddy_upd_rule simp: buddy_map.fixed_univ_map_upd_invar)

subsection \<open>Matchings with a Cached Cardinality\<close>

text \<open>A buddy map together with a reference to the cardinality of the matching. Augmentation
      increments the reference, hence the cardinality is read in constant time. Both are
      updated in place; the pair is returned to fit the interface of the top loop.\<close>

definition counted_assn :: "'buddy \<Rightarrow> 'bi \<times> nat ref \<Rightarrow> assn" where
  "counted_assn M = (\<lambda>(Bi, Ki). buddy_assn M Bi * Ki \<mapsto>\<^sub>r card (\<M> M))"

lemma counted_assn_pair: "counted_assn M (Bi, Ki) = buddy_assn M Bi * Ki \<mapsto>\<^sub>r card (\<M> M)"
  by (simp add: counted_assn_def)

definition "augment_counted_imp = (\<lambda>(Bi, Ki) Ra k. do {
   augment_imp Bi Ra k;
   c \<leftarrow> !Ki;
   Ki := Suc c;
   return (Bi, Ki) })"

definition "matching_card_imp = (\<lambda>(Bi, Ki). !Ki)"

lemma matching_card_imp_rule:
  "<counted_assn M Mi> matching_card_imp Mi <\<lambda>c. counted_assn M Mi * \<up>(c = card (\<M> M))>"
  by (cases Mi) (sep_auto simp: counted_assn_pair matching_card_imp_def)

lemma augment_counted_imp_rule:
  "\<lbrakk>buddy_invar M; k \<le> length xs; set (take k xs) \<subseteq> K;
    card (\<M> (augment_impl M (take k xs))) = Suc (card (\<M> M))\<rbrakk> \<Longrightarrow>
   <counted_assn M Mi * Ra \<mapsto>\<^sub>a xs> augment_counted_imp Mi Ra k
   <\<lambda>Mi'. counted_assn (augment_impl M (take k xs)) Mi' * Ra \<mapsto>\<^sub>a xs>"
  by (cases Mi) (sep_auto heap: augment_imp_rule simp: counted_assn_pair augment_counted_imp_def)

text \<open>Rematching does not change the cardinality, hence the reference is left as it is.\<close>

definition "rematch_counted_imp = (\<lambda>(Bi, Ki) l r. rematch_imp Bi l r)"

lemma rematch_counted_imp_rule:
  "\<lbrakk>buddy_invar M; l \<in> K; r \<in> K; buddy_get M r \<in> K;
    card (\<M> (rematch M l r)) = card (\<M> M)\<rbrakk> \<Longrightarrow>
   <counted_assn M Mi> rematch_counted_imp Mi l r <\<lambda>_. counted_assn (rematch M l r) Mi>"
  by (cases Mi) (sep_auto heap: rematch_imp_rule simp: counted_assn_pair rematch_counted_imp_def)

end

end