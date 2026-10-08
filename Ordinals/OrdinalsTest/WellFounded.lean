module

public import Ordinals

/-! Tests for `Ordinals.Tree.WellFounded` and `Ordinals.Tree.WfRel`. -/

open Ordinals

universe u

/-! ## Usage -/

example {A : Type u} {R : A → A → Prop} (hwf : WellFounded R) (a : A) :
    OTree.ofWf hwf a = OTree.mk {b // R b a} fun b => OTree.ofWf hwf b.1 :=
  OTree.ofWf_eq hwf a

/-- The tree does not depend on the proof of well-foundedness. -/
example {A : Type u} {R : A → A → Prop} (hwf₀ hwf₁ : WellFounded R) :
    OTree.ofWfSet hwf₀ = OTree.ofWfSet hwf₁ :=
  rfl

example : OTree.ofNat.{0} 3 ≈ OTree.ofWf OTree.ulift_nat_lt_wf ⟨3⟩ :=
  OTree.ofNat_equiv_ofWf 3

example : OTree.lift.{0, 1} OTree.omega < OTree.large.{0} :=
  OTree.lift_lt_large OTree.omega

example : OTree.omega.{u} < OTree.hartogs (ULift.{u} Nat) :=
  OTree.lt_of_le_of_lt OTree.omega_equiv_ofWfSet.le (OTree.ofWfSet_lt_hartogs _)

/-! ## Axioms: `Ordinals.Tree.WellFounded` -/

/-- info: 'Ordinals.OTree.ofAcc_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ofAcc_eq

/-- info: 'Ordinals.OTree.ofWf_le_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ofWf_le_iff

/-- info: 'Ordinals.OTree.lt_ofWf_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.lt_ofWf_iff

/-- info: 'Ordinals.OTree.ofWf_lt_ofWf' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ofWf_lt_ofWf

/-- info: 'Ordinals.OTree.ofNat_equiv_ofWf' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ofNat_equiv_ofWf

/-- info: 'Ordinals.OTree.omega_equiv_ofWfSet' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.omega_equiv_ofWfSet

/-- info: 'Ordinals.OTree.ofWf_lt_hartogs' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ofWf_lt_hartogs

/-- info: 'Ordinals.OTree.hartogs_le_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.hartogs_le_iff

/-- info: 'Ordinals.OTree.lift_hartogs_le_large' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.lift_hartogs_le_large

/-- info: 'Ordinals.OTree.lift_ofWf_lt_large' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.lift_ofWf_lt_large

/-- info: 'Ordinals.OTree.large_le_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.large_le_iff

/-- info: 'Ordinals.OTree.equiv_ofWfSet_pos' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.equiv_ofWfSet_pos

/-- info: 'Ordinals.OTree.lift_lt_large' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.lift_lt_large

/-! ## Axioms: `Ordinals.Tree.WfRel` -/

/-- info: 'Ordinals.OTree.ofWfSet_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ofWfSet_mono

/-- info: 'Ordinals.OTree.ofWfSet_le_ofWfSet_of_map' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ofWfSet_le_ofWfSet_of_map

/-- info: 'Ordinals.OTree.ProjRel.wf' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ProjRel.wf

/-- info: 'Ordinals.OTree.ProjRel.wf_of_map' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ProjRel.wf_of_map

/-- info: 'Ordinals.OTree.ofWf_equiv_ofWf_projRel' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ofWf_equiv_ofWf_projRel

/-- info: 'Ordinals.OTree.ofWfSet_equiv_ofWfSet_rangeRel' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ofWfSet_equiv_ofWfSet_rangeRel

/-- info: 'Ordinals.OTree.CutRel.total' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.CutRel.total

/-- info: 'Ordinals.OTree.ofWf_equiv_ofWfSet_cutRel' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ofWf_equiv_ofWfSet_cutRel
