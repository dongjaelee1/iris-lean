module

public import Ordinals

/-! Tests for ordinal arithmetic on trees: the main results use no axioms, and examples. -/

open Ordinals OTree

universe u

/-- info: 'Ordinals.OTree.trec_add' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.trec_add

/-- info: 'Ordinals.OTree.add_assoc' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.add_assoc

/-- info: 'Ordinals.OTree.add_lt_add_left' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.add_lt_add_left

/-- info: 'Ordinals.OTree.add_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.add_congr

/-- info: 'Ordinals.OTree.mul_add' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.mul_add

/-- info: 'Ordinals.OTree.mul_assoc' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.mul_assoc

/-- info: 'Ordinals.OTree.mul_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.mul_congr

/-- info: 'Ordinals.OTree.pow_add' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.pow_add

/-- info: 'Ordinals.OTree.pow_mul' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.pow_mul

/-- info: 'Ordinals.OTree.pow_lt_pow_right' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.pow_lt_pow_right

/-- info: 'Ordinals.OTree.pow_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.pow_congr

/-- info: 'Ordinals.OTree.ofNat_pow' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ofNat_pow

/-! ## Examples -/

example : add (ofNat.{u} 2) (ofNat 3) ≈ ofNat 5 :=
  (ofNat_add 2 3).symm

example : mul (ofNat.{u} 2) (ofNat 3) ≈ ofNat 6 :=
  (ofNat_mul 2 3).symm

example : pow (ofNat.{u} 2) (ofNat 3) ≈ ofNat 8 :=
  (ofNat_pow (Nat.zero_lt_succ 1) 3).symm

/-- `ω + 1` is above `ω`. -/
example : omega.{u} < add omega (succ zero) :=
  OTree.lt_add_of_pos_right omega (zero_lt_succ zero)

/-- `1 + ω` is `ω`. -/
example : add (succ zero) omega.{u} ≈ omega := by
  refine ⟨?_, OTree.le_add_left _ _⟩
  refine OTree.le_trans (add_sup_of_nonempty _ _).le (sup_le fun n => ?_)
  exact OTree.le_trans (ofNat_add 1 n.down).ge (OTree.le_of_lt (ofNat_lt_omega (1 + n.down)))

/-- `2 * ω` is `ω`. -/
example : mul (ofNat.{u} 2) omega ≈ omega := by
  refine ⟨?_, ?_⟩
  · refine OTree.le_trans (mul_sup _ _).le (sup_le fun n => ?_)
    exact OTree.le_trans (ofNat_mul 2 n.down).ge (OTree.le_of_lt (ofNat_lt_omega (2 * n.down)))
  · exact OTree.le_trans (OTree.one_mul omega).ge
      (OTree.mul_le_mul_right (succ_le_succ (zero_le _)) omega)
