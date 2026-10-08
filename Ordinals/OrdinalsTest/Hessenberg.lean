module

public import Ordinals

/-! Tests for the natural sum of trees (`Ordinals.Tree.Hessenberg`). -/

open Ordinals

universe u

/-! ## Usage -/

/-- The unfolding equation is definitional. -/
example (s t : OTree.{u}) :
    OTree.nadd (OTree.succ s) (OTree.succ t) =
      OTree.max (OTree.mk PUnit fun _ => OTree.nadd (OTree.succ s) t)
        (OTree.mk PUnit fun _ => OTree.nadd s (OTree.succ t)) :=
  rfl

example : OTree.nadd (OTree.ofNat.{u} 2) (OTree.ofNat 3) ≈ OTree.ofNat 5 :=
  OTree.nadd_ofNat 2 3

example {s s' t t' : OTree.{u}} (hs : s < s') (ht : t < t') :
    OTree.nadd s t < OTree.nadd s' t' :=
  OTree.lt_trans (OTree.nadd_lt_nadd_right hs t) (OTree.nadd_lt_nadd_left ht s')

/-- The natural sum `1 +ₕ ω` is `succ ω`, but the standard sum `1 + ω` is `ω`. -/
example : OTree.nadd (OTree.ofNat.{u} 1) OTree.omega ≈ OTree.succ OTree.omega :=
  (OTree.succ_nadd _ _).trans (OTree.succ_congr (OTree.zero_nadd _))

/-! ## Axioms -/

/-- info: 'Ordinals.OTree.induction₂' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.induction₂

/-- info: 'Ordinals.OTree.nadd_mk_mk' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.nadd_mk_mk

/-- info: 'Ordinals.OTree.nadd_le_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.nadd_le_iff

/-- info: 'Ordinals.OTree.lt_nadd_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.lt_nadd_iff

/-- info: 'Ordinals.OTree.nadd_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.nadd_congr

/-- info: 'Ordinals.OTree.nadd_lt_nadd_left' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.nadd_lt_nadd_left

/-- info: 'Ordinals.OTree.nadd_lt_nadd_right' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.nadd_lt_nadd_right

/-- info: 'Ordinals.OTree.nadd_comm' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.nadd_comm

/-- info: 'Ordinals.OTree.nadd_assoc' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.nadd_assoc

/-- info: 'Ordinals.OTree.nadd_zero' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.nadd_zero

/-- info: 'Ordinals.OTree.nadd_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.nadd_succ

/-- info: 'Ordinals.OTree.nadd_ofNat' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.nadd_ofNat

/-- info: 'Ordinals.OTree.lt_nadd_of_pos_right' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.lt_nadd_of_pos_right

/-- info: 'Ordinals.OTree.lift_nadd' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.lift_nadd
