module

public import Ordinals

/-! Tests for the quotient layer. -/

open Ordinals Ordinal

/-- `grind` uses the core order instances. -/
example (a b c : Ordinal) (h₁ : a ≤ b) (h₂ : b < c) : a < c := by grind

example (a b : Ordinal) (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by grind

example (a b : Ordinal) : a < b ∨ a = b ∨ b < a := by grind

example (a : Ordinal) : a < succ a := lt_succ a

example : (2 : Ordinal) < ω := ofNat_lt_omega 2

/-- info: 'Ordinals.Ordinal.le_antisymm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Ordinal.le_antisymm

/-- info: 'Ordinals.Ordinal.lt_wf' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Ordinal.lt_wf

/-- info: 'Ordinals.Ordinal.lt_trichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ordinal.lt_trichotomy
