module

public import Ordinals

/-! Tests for the Jacobsthal operations on the quotient layer. -/

open Ordinals Ordinal

example (a b c : Ordinal) : a ×ⱼ (b +ₕ c) = a ×ⱼ b +ₕ a ×ⱼ c := jmul_nadd a b c

example (a b c : Ordinal) : a ×ⱼ b ×ⱼ c = a ×ⱼ (b ×ⱼ c) := jmul_assoc a b c

example (a b : Ordinal) : a * b ≤ a ×ⱼ b := mul_le_jmul a b

example (a : Ordinal) (h : 0 < a) (b c : Ordinal) : a ^ⱼ (b + c) = a ^ⱼ b ×ⱼ a ^ⱼ c :=
  jpow_add h b c

/-- info: 'Ordinals.Ordinal.jmul_nadd' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Ordinal.jmul_nadd
