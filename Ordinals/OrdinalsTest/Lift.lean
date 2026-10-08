module

public import Ordinals

/-! Tests for ordinals in several universes. -/

open Ordinals Ordinal

example (a : Ordinal.{0}) : lift.{0, 1} a < univ.{0} := lift_lt_univ a

example (a : Ordinal.{1}) : lift.{1, 2} a < univ.{1} := lift_lt_univ a

example : lift.{1, 2} univ.{0} < univ.{1} := lift_lt_univ _

example : lift.{0, 1} (ω : Ordinal.{0}) = ω := lift_omega

example (n : Nat) : lift.{0, 2} (ofNat n : Ordinal.{0}) = ofNat n := lift_ofNat n

/-- A supremum in a larger universe needs a `ULift` of the index type. -/
example (f : Nat → Ordinal.{1}) (n : Nat) : f n ≤ sup (fun i : ULift.{1} Nat => f i.down) :=
  le_sup (fun i : ULift.{1} Nat => f i.down) ⟨n⟩

/-- info: 'Ordinals.Ordinal.lt_lift_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Ordinal.lt_lift_iff

example : large.{0} = univ.{0} := large_eq_univ

example (c : Ordinal.{0}) : ∃ (B : Type) (S : B → B → Prop) (hwf : WellFounded S), type hwf = c :=
  exists_type_eq c
