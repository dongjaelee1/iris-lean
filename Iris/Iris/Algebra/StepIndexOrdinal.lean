/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals
public import Iris.Algebra.StepIndexTransfinite

/-!
# The ordinals as step indices

The step-index structures of `Ordinals.Ordinal.{u}` (the ordinals library of this repository), for
each universe `u`:

- `ordinalSIdx`: `SIdx`,
- `ordinalSIdxTransfinite`: `SIdxTransfinite`,
- `ordinalSIdxLarge`: the existential property for quantifiers over types in `Type u`.

They are `def`s and theorems, not instances. The ordinal choice file
(`Iris/StepIndexChoices/ordinal/StepIndexChoice.lean`) makes them the instances of `Iris.SI`.
Every build compiles this file, also when the build uses another index.
-/

@[expose] public section

noncomputable section

namespace Iris

open Ordinals

universe u

/-- The step-index structure of `Ordinal.{u}`. -/
@[reducible] def ordinalSIdx : SIdx Ordinal.{u} where
  succ := Ordinal.succ
  lt_trans := Ordinal.lt_trans
  lt_wf := Ordinal.lt_wf
  lt_trichotomyT n m :=
    if h : n < m then .inl h
    else if h' : n = m then .inr (.inl h')
    else .inr (.inr ((Ordinal.lt_trichotomy n m).resolve_left h |>.resolve_left h'))
  le_lteq := Ordinal.le_iff_lt_or_eq
  not_lt_zero := Ordinal.not_lt_zero
  lt_succ_self := Ordinal.lt_succ
  succ_le_of_lt := Ordinal.succ_le_of_lt
  weak_case n :=
    letI : Decidable (∃ m, n = Ordinal.succ m) := Classical.propDecidable _
    if h : ∃ m, n = Ordinal.succ m then .inl ⟨h.choose, h.choose_spec⟩
    else .inr fun m hm => Ordinal.lt_iff_le_and_ne.mpr
      ⟨Ordinal.succ_le_of_lt hm, fun e => h ⟨m, e.symm⟩⟩

/-- The upper limit of `m` is the strict supremum of the finite successors of `m`. -/
@[reducible] def ordinalSIdxTransfinite : @SIdxTransfinite Ordinal.{u} ordinalSIdx :=
  letI := ordinalSIdx
  { upperLimit m := Ordinal.ssup fun n : ULift.{u} Nat => Nat.repeat Ordinal.succ n.down m
    iter_succ_lt_upperLimit n m :=
      Ordinal.lt_ssup (fun n : ULift.{u} Nat => Nat.repeat Ordinal.succ n.down m) ⟨n⟩ }

/-- The existential property for quantifiers over types in `Type u`. -/
theorem ordinalSIdxLarge {X : Type u} : @SIdxLarge Ordinal.{u} ordinalSIdx X :=
  letI := ordinalSIdx
  { commute_exists P hmono hex := by
      refine Classical.byContradiction fun hne => ?_
      have h : ∀ x, ∃ a, ¬P x a := fun x => Classical.not_forall.mp fun h => hne ⟨x, h⟩
      let f : X → Ordinal.{u} := fun x => Classical.choose (h x)
      obtain ⟨x, hx⟩ := hex (Ordinal.ssup f)
      exact Classical.choose_spec (h x) (hmono x _ _ (Ordinal.lt_ssup f x) hx) }

end Iris
