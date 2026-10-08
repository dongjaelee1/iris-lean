/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals
public import Iris.Algebra.StepIndexTransfinite
public import Iris.Std.Classes
public meta import Iris.Std.RocqPorting

/-!
# The step-index type of this build: ordinals

This version of the choice file is for the ordinal build. It sets `SI := Ordinals.Ordinal.{3}`
(the ordinals library of this repository; no Mathlib), so `SI : Type 4`. It gives the instances
`SIdx SI`, `SIdxTransfinite SI` and `SIdxLarge.{v} SI` for `v ≤ 3`. There is no `SIdxFinite SI`
instance. `TypeSI u` expands to `Type (max u 4)`.

The universe level 3 gives three levels of ordinals below the step index: `Ordinal.{0}`,
`Ordinal.{1}` and `Ordinal.{2}`. For each level `k`, `Ordinal.lift.{k, 3}` maps `Ordinal.{k}` onto
an initial segment of `SI`, and the lift of `Ordinal.univ.{k}` is above this segment. The
existential property `SIdxLarge.{3} SI` applies to quantifiers over types in `Type 3`, which
include `Ordinal.{2}`. To change the level, change `Ordinal.{3}`, `ULift.{3}`, `SIdxLarge.{3}`,
`Type 4` and the two macros together.
-/

@[expose] public section

noncomputable section

namespace Iris

open Ordinals

/-- The step-index structure of `Ordinal.{3}`. It is a `def`, so that `SI` has the only `SIdx`
instance. -/
@[reducible] def ordinalSIdx : SIdx Ordinal.{3} where
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
@[reducible] def ordinalSIdxTransfinite : @SIdxTransfinite Ordinal.{3} ordinalSIdx :=
  letI := ordinalSIdx
  { upperLimit m := Ordinal.ssup fun n : ULift.{3} Nat => Nat.repeat Ordinal.succ n.down m
    iter_succ_lt_upperLimit n m :=
      Ordinal.lt_ssup (fun n : ULift.{3} Nat => Nat.repeat Ordinal.succ n.down m) ⟨n⟩ }

/-- The existential property for families indexed by types in `Type 3`. -/
theorem ordinalSIdxLarge : @SIdxLarge.{3} Ordinal.{3} ordinalSIdx :=
  letI := ordinalSIdx
  { commute_exists {X} P hmono hex := by
      refine Classical.byContradiction fun hne => ?_
      have h : ∀ x, ∃ a, ¬P x a := fun x => Classical.not_forall.mp fun h => hne ⟨x, h⟩
      let f : X → Ordinal.{3} := fun x => Classical.choose (h x)
      obtain ⟨x, hx⟩ := hex (Ordinal.ssup f)
      exact Classical.choose_spec (h x) (hmono x _ _ (Ordinal.lt_ssup f x) hx) }

/-- The step-index type of this build. -/
def SI : Type 4 := Ordinal.{3}

instance instSIdxSI : SIdx SI := ordinalSIdx
instance instSIdxTransfiniteSI : SIdxTransfinite SI := ordinalSIdxTransfinite
instance instSIdxLargeSI : SIdxLarge.{3} SI := ordinalSIdxLarge
instance instSIdxLargeSI2 : SIdxLarge.{2} SI := SIdxLarge.down.{2, 3} (h := instSIdxLargeSI)
instance instSIdxLargeSI1 : SIdxLarge.{1} SI := SIdxLarge.down.{1, 3} (h := instSIdxLargeSI)
instance instSIdxLargeSI0 : SIdxLarge.{0} SI := SIdxLarge.down.{0, 3} (h := instSIdxLargeSI)

/-- `SI : Type 4`, so `TypeSI u` is `Type (max u 4)`. See the `Nat` choice file. -/
macro "TypeSI " u:level : term => `(Type (max $u 4))

/-- `levelSI% u` is the level of `TypeSI u`: `max u 4`. See the `Nat` choice file. -/
macro "levelSI% " u:term:max : term => `(Lean.Level.max $u 4)

end Iris
