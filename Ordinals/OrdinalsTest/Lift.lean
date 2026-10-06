module

public import Ordinals

/-! Tests for ordinals in several universes. -/

open Ordinals Ordinal

/-- A data ordinal in `Ordinal.{0}` is below `univ.{0}`, which is in `Ordinal.{1}`. -/
example (a : Ordinal.{0}) : lift.{0, 1} a < univ.{0} := lift_lt_univ a

/-- Ordinals of `Ordinal.{1}` (for example a step index) are below `univ.{1}`. -/
example (a : Ordinal.{1}) : lift.{1, 2} a < univ.{1} := lift_lt_univ a

/-- `univ.{0}`, lifted, is below `univ.{1}`. -/
example : lift.{1, 2} univ.{0} < univ.{1} := lift_lt_univ _

/-- The lift keeps `ω` and the natural numbers. -/
example : lift.{0, 1} (ω : Ordinal.{0}) = ω := lift_omega

example (n : Nat) : lift.{0, 2} (ofNat n : Ordinal.{0}) = ofNat n := lift_ofNat n

/-- A supremum of a family indexed by a small type, in a larger universe. -/
example (f : Nat → Ordinal.{1}) (n : Nat) : f n ≤ sup (fun i : ULift.{1} Nat => f i.down) :=
  le_sup (fun i : ULift.{1} Nat => f i.down) ⟨n⟩

/-- info: 'Ordinals.Ordinal.lt_lift_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ordinal.lt_lift_iff

/-- snu-sf's `large` is `univ`. -/
example : large.{0} = univ.{0} := large_eq_univ

/-- Each ordinal is the type of a well-founded relation. -/
example (c : Ordinal.{0}) : ∃ (B : Type) (S : B → B → Prop) (hwf : WellFounded S), type hwf = c :=
  exists_type_eq c
