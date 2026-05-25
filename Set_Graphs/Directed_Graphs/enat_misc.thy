(*
  Author: Mohammad Abdulaziz, TUM
*)

theory enat_misc
  imports Main "HOL-Library.Extended_Nat"
begin

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
  by (metis nat.exhaust_sel)

end