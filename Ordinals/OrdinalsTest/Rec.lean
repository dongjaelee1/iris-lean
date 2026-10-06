module

public import Ordinals

/-! Tests for transfinite recursion on trees: the main results use no axioms, and examples. -/

open Ordinals OTree

universe u

/-- info: 'Ordinals.OTree.trec_le_trec' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.trec_le_trec

/-- info: 'Ordinals.OTree.trec_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.trec_succ

/-- info: 'Ordinals.OTree.trec_sup_of_nonempty' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.trec_sup_of_nonempty

/-- info: 'Ordinals.OTree.trec_mk_of_open' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.trec_mk_of_open

/-- info: 'Ordinals.OTree.trec_max' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.trec_max

/-- info: 'Ordinals.OTree.trec_unique' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.trec_unique

/-- info: 'Ordinals.OTree.trec_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.trec_mono

/-- info: 'Ordinals.OTree.orec_sup' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.orec_sup

/-- info: 'Ordinals.OTree.orec_le' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.orec_le

/-- info: 'Ordinals.OTree.orec_unique' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.orec_unique

/-- info: 'Ordinals.OTree.orec_zero_succ' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.orec_zero_succ

/-! ## Recursion into `Prop`

The propositions form a join domain: `→` is the order and `∃` is the join. -/

theorem prop_joinLaws :
    JoinLaws.{u} (D := Prop) (· → ·) (fun _ => True) fun A ds => ∃ a : A, ds a :=
  ⟨fun _ h => h, fun _ _ _ h₁ h₂ h => h₂ (h₁ h), fun _ a h => ⟨a, h⟩,
    fun _ _ h ⟨a, ha⟩ => h a ha, fun _ => trivial⟩

/-- Recursion with `base := False` and `next := fun _ => True`: the result is `True` exactly
on the trees above `zero`. -/
example (t : OTree.{u}) : trec False (fun _ => True) (fun A ds => ∃ a : A, ds a) (succ t) :=
  (trec_succ prop_joinLaws ⟨trivial, fun _ => trivial⟩ (fun _ _ => trivial) t).2 trivial

example : ¬trec False (fun _ => True) (fun A ds => ∃ a : A, ds a) zero.{u} :=
  (trec_zero prop_joinLaws ⟨trivial, fun _ => trivial⟩).1

/-! ## Recursion into the trees -/

/-- `orec zero succ` keeps the height. -/
example : orec zero succ omega.{u} ≈ omega :=
  orec_zero_succ omega

/-- The defining equation of `orec` holds by `rfl`, with `dunion` in place of `max`. -/
example (base : OTree.{u}) (next : OTree.{u} → OTree.{u}) (ι : Type u) (f : ι → OTree.{u}) :
    orec base next (mk ι f) =
      dunion (fun _ => sup) base (sup fun i => next (orec base next (f i))) :=
  rfl
