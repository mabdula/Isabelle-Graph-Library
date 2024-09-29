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

end