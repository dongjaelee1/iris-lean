module

public import Ordinals

/-! Tests for the arithmetic of ordinals. The laws are equalities, so `rw` works. -/

open Ordinals Ordinal

example (a b c : Ordinal) : a + b + c + 0 = a + (b + c) := by
  rw [Ordinal.add_zero, Ordinal.add_assoc]

example (a b c : Ordinal) : a * (b + c) = a * b + a * c := Ordinal.mul_add a b c

example : (1 : Ordinal) + ω = ω := one_add_omega

example : (ω : Ordinal) < ω + 1 := omega_lt_omega_add_one

example (a b c : Ordinal) : a +ₕ b +ₕ c = c +ₕ (b +ₕ a) := by
  rw [nadd_comm c, nadd_comm b a, nadd_assoc]

example (a b c : Ordinal) (h : a +ₕ b = a +ₕ c) : b = c := nadd_left_cancel a h

example (a b : Ordinal) (h : a < b) (c : Ordinal) : c +ₕ a < c +ₕ b := nadd_lt_nadd_left h c

/-- info: 'Ordinals.Ordinal.mul_add' depends on axioms: [Quot.sound] -/
#guard_msgs in
#print axioms Ordinal.mul_add

/-- info: 'Ordinals.Ordinal.nadd_left_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ordinal.nadd_left_cancel
