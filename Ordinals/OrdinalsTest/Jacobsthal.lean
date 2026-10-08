module

public import Ordinals

/-! Tests for `Ordinals.Tree.Jacobsthal` and `Ordinals.Tree.HessenbergArith`. -/

open Ordinals OTree

universe u

/-- info: 'Ordinals.OTree.add_le_nadd' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.add_le_nadd

/-- info: 'Ordinals.OTree.nadd_ofNat_equiv_add' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.nadd_ofNat_equiv_add

/-- info: 'Ordinals.OTree.mul_le_jmul' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.mul_le_jmul

/-- info: 'Ordinals.OTree.jmul_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.jmul_congr

/-- info: 'Ordinals.OTree.jmul_lt_jmul_of_pos_left' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.jmul_lt_jmul_of_pos_left

/-- info: 'Ordinals.OTree.one_jmul' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.one_jmul

/-- info: 'Ordinals.OTree.ofNat_jmul' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ofNat_jmul

/-- info: 'Ordinals.OTree.jmul_nadd' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.jmul_nadd

/-- info: 'Ordinals.OTree.jmul_assoc' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.jmul_assoc

/-- info: 'Ordinals.OTree.pow_le_jpow' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.pow_le_jpow

/-- info: 'Ordinals.OTree.jpow_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.jpow_congr

/-- info: 'Ordinals.OTree.jpow_lt_jpow_right' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.jpow_lt_jpow_right

/-- info: 'Ordinals.OTree.ofNat_jpow' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ofNat_jpow

/-- info: 'Ordinals.OTree.jpow_add' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.jpow_add

/-- info: 'Ordinals.OTree.jpow_mul' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.jpow_mul

/-! ## Natural numbers -/

example : jmul (ofNat.{u} 2) (ofNat 3) ≈ ofNat 6 :=
  (ofNat_jmul 2 3).symm

example : jpow (ofNat.{u} 2) (ofNat 3) ≈ ofNat 8 :=
  (ofNat_jpow (Nat.zero_lt_succ 1) 3).symm

example : nadd omega.{u} (ofNat 3) ≈ add omega (ofNat 3) :=
  nadd_ofNat_equiv_add omega 3

/-! ## `ω` and `2` -/

theorem jmul_omega_two : jmul omega.{u} (ofNat 2) ≈ nadd omega omega :=
  Equiv.trans (jmul_succ omega _) (nadd_congr_left (jmul_one omega) omega)

theorem mul_omega_two : mul omega.{u} (ofNat 2) ≈ add omega omega :=
  Equiv.trans (mul_succ omega _) (add_congr_left (OTree.mul_one omega) omega)

theorem le_ofNat_of_lt_omega {s : OTree.{u}} (h : s < omega) : ∃ n : Nat, s ≤ ofNat n :=
  let ⟨n, hn⟩ := lt_sup_iff.mp h
  ⟨n.down, OTree.le_of_lt hn⟩

theorem nadd_omega_omega : nadd omega.{u} omega ≈ add omega omega := by
  refine ⟨nadd_le_of_forall_lt (fun s hs => ?_) (fun t ht => ?_), add_le_nadd _ _⟩
  · obtain ⟨n, hn⟩ := le_ofNat_of_lt_omega hs
    exact OTree.lt_of_le_of_lt
      (OTree.le_trans (nadd_le_nadd_right hn omega) (ofNat_nadd_equiv_add n omega).le)
      (OTree.add_lt_add_left (ofNat_lt_omega n) omega)
  · obtain ⟨n, hn⟩ := le_ofNat_of_lt_omega ht
    exact OTree.lt_of_le_of_lt
      (OTree.le_trans (nadd_le_nadd_left hn omega) (nadd_ofNat_equiv_add omega n).le)
      (OTree.add_lt_add_left (ofNat_lt_omega n) omega)

example : jmul omega.{u} (ofNat 2) ≈ mul omega (ofNat 2) :=
  Equiv.trans jmul_omega_two (Equiv.trans nadd_omega_omega mul_omega_two.symm)

theorem jmul_two_omega : jmul (ofNat.{u} 2) omega ≈ omega := by
  refine ⟨?_, le_jmul_of_pos_left omega (zero_lt_succ _)⟩
  refine OTree.le_trans (jmul_sup _ _).le (sup_le fun n => ?_)
  exact OTree.le_trans (ofNat_jmul 2 n.down).ge (OTree.le_of_lt (ofNat_lt_omega (2 * n.down)))

/-- The Jacobsthal product is not commutative. -/
example : jmul (ofNat.{u} 2) omega < jmul omega (ofNat 2) :=
  (lt_congr jmul_two_omega jmul_omega_two).mpr
    (lt_nadd_of_pos_right omega (ofNat_lt_omega 0))

/-! ## `ω + 1` and `2`

Here the Jacobsthal product (`ω · 2 + 2`) is above the standard product (`ω · 2 + 1`).
-/

theorem one_add_omega : add (succ zero) omega.{u} ≈ omega := by
  refine ⟨?_, OTree.le_add_left _ _⟩
  refine OTree.le_trans (add_sup_of_nonempty _ _).le (sup_le fun n => ?_)
  exact OTree.le_trans (ofNat_add 1 n.down).ge (OTree.le_of_lt (ofNat_lt_omega (1 + n.down)))

theorem add_omega_one : add omega.{u} (succ zero) ≈ succ omega :=
  Equiv.trans (add_succ omega zero) (succ_congr (OTree.add_zero omega))

theorem mul_succ_omega_two : mul (succ omega.{u}) (ofNat 2) ≈ succ (add omega omega) := by
  refine Equiv.trans (mul_succ _ _) (Equiv.trans (add_congr_left (OTree.mul_one _) _) ?_)
  refine Equiv.trans (add_succ _ _) (succ_congr ?_)
  -- `(ω + 1) + ω = ω + (1 + ω) = ω + ω`.
  exact Equiv.trans (add_congr_left add_omega_one.symm omega)
    (Equiv.trans (OTree.add_assoc _ _ _) (add_congr_right one_add_omega omega))

theorem jmul_succ_omega_two :
    jmul (succ omega.{u}) (ofNat 2) ≈ succ (succ (add omega omega)) := by
  refine Equiv.trans (jmul_succ _ _) (Equiv.trans (nadd_congr_left (jmul_one _) _) ?_)
  refine Equiv.trans (succ_nadd _ _) (succ_congr (Equiv.trans (nadd_succ _ _) (succ_congr ?_)))
  exact nadd_omega_omega

example : mul (succ omega.{u}) (ofNat 2) < jmul (succ omega) (ofNat 2) :=
  (lt_congr mul_succ_omega_two jmul_succ_omega_two).mpr (lt_succ _)

/-! ## Usage of the algebraic laws -/

example {s : OTree.{u}} (hs : zero < s) (t t' : OTree.{u}) :
    jpow s (add t t') ≈ jmul (jpow s t) (jpow s t') :=
  jpow_add hs t t'

example (r s t : OTree.{u}) :
    jmul (jmul r s) (nadd t t) ≈ nadd (jmul r (jmul s t)) (jmul r (jmul s t)) :=
  Equiv.trans (jmul_nadd _ t t) (nadd_congr (jmul_assoc r s t) (jmul_assoc r s t))

example : jpow omega.{u} (ofNat 2) ≈ jmul omega omega :=
  have hω : zero < omega.{u} := ofNat_lt_omega 0
  Equiv.trans (jpow_succ hω _) (jmul_congr_left (jpow_one hω) omega)
