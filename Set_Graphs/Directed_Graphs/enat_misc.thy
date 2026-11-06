(*
  Author: Mohammad Abdulaziz, TUM
*)

theory enat_misc
  imports Main "HOL-Library.Extended_Nat" AI_Provenance.Provenance
begin

provenance human

declare one_enat_def

declare zero_enat_def

lemma eval_enat_numeral:
  "numeral Num.One = eSuc 0"
  "numeral (Num.Bit0 n) = eSuc (numeral (Num.BitM n))"
  "numeral (Num.Bit1 n) = eSuc (numeral (Num.Bit0 n))"
  by (simp_all add: BitM_plus_one eSuc_enat numeral_plus_one[symmetric] zero_enat_def one_enat_def)

declare eSuc_enat[symmetric, simp]

lemma eqI_strict_less_contradiction_cases:
  "\<lbrakk>((x::enat) < y \<Longrightarrow> False); (y < x \<Longrightarrow> False)\<rbrakk> \<Longrightarrow> x = y"
  using linorder_less_linear by blast

lemma enat_sum_distr:"finite X \<Longrightarrow> sum (\<lambda> x. enat (f x)) X = enat (sum f X)" 
  by(induction X rule: finite_induct) 
    (auto simp add: comm_monoid_add_class.sum.insert_remove enat_0)

lemma nat_cases_up_to_3:
  "\<lbrakk>n = 0 \<Longrightarrow> P; n = Suc 0 \<Longrightarrow> P; n = Suc (Suc 0) \<Longrightarrow> P; 
   \<And> nn. n = Suc (Suc (Suc nn)) \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
proof -
  assume h0: "n = 0 \<Longrightarrow> P"
  assume h1: "n = Suc 0 \<Longrightarrow> P"
  assume h2: "n = Suc (Suc 0) \<Longrightarrow> P"
  assume h3: "\<And>nn. n = Suc (Suc (Suc nn)) \<Longrightarrow> P"
  show P
  proof (cases n)
    case 0
    with h0 show ?thesis by blast
  next
    case (Suc n1)
    note n_eq1 = Suc
    show ?thesis
    proof (cases n1)
      case 0
      hence "n = Suc 0" using n_eq1 by simp
      with h1 show ?thesis by blast
    next
      case (Suc n2)
      note n1_eq2 = Suc
      show ?thesis
      proof (cases n2)
        case 0
        hence "n = Suc (Suc 0)" using n1_eq2 n_eq1 by simp
        with h2 show ?thesis by blast
      next
        case (Suc n3)
        hence "n = Suc (Suc (Suc n3))" using n1_eq2 n_eq1 by simp
        with h3[of n3] show ?thesis by blast
      qed
    qed
  qed
qed

end