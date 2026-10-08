/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Instances.UPred.Transfinite
public import Iris.Algebra.IProp

/-! Tests of the ordinal choice, `SI := Ordinals.Ordinal.{3}`. -/

@[expose] public section

namespace IrisTest
open Iris Ordinals Ordinal UPred

example : SI = Ordinal.{3} := rfl

example (GF : BundledGFunctors.{0}) : Type 4 := IProp GF

/-! For each level `k < 3`, the lift of `univ.{k}` is above the lifted ordinals of
`Ordinal.{k}`. -/

example (a : Ordinal.{2}) : (lift.{2, 3} a : SI) < (univ.{2} : SI) :=
  lift_lt_univ a

example (a : Ordinal.{1}) : (lift.{1, 3} a : SI) < (lift.{2, 3} univ.{1} : SI) := by
  have h := (lift_lt_lift_iff.{_, 3}).mpr (lift_lt_univ a)
  rwa [lift_lift] at h

example (a : Ordinal.{0}) : (lift.{0, 3} a : SI) < (lift.{1, 3} univ.{0} : SI) := by
  have h := (lift_lt_lift_iff.{_, 3}).mpr (lift_lt_univ a)
  rwa [lift_lift] at h

/-! The existential property at each level, with no universe annotation. -/

section
variable {M : Type} [UCMRA M]

example {P : Ordinal.{2} → UPred M} (h : satisfiable iprop(∃ α, P α)) :
    ∃ α, satisfiable (P α) :=
  satisfiable_exists h

example {P : Ordinal.{1} → UPred M} (h : satisfiable iprop(∃ α, P α)) :
    ∃ α, satisfiable (P α) :=
  satisfiable_exists h

example {P : Ordinal.{0} → UPred M} (h : satisfiable iprop(∃ α, P α)) :
    ∃ α, satisfiable (P α) :=
  satisfiable_exists h

/-- Sets of ordinals of level 1 are in `Type 2`. -/
example {P : (Ordinal.{1} → Prop) → UPred M} (h : satisfiable iprop(∃ s, P s)) :
    ∃ s, satisfiable (P s) :=
  satisfiable_exists h

/-- A small type in a large universe, through `ULift`. -/
example {P : ULift.{7} Ordinal.{1} → UPred M} (h : satisfiable iprop(∃ α, P α)) :
    ∃ α, satisfiable (P α) :=
  satisfiable_exists h

-- The step index itself is too large: there is no instance.
/--
error: failed to synthesize instance of type class
  SIdxLarge SI SI

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {P : SI → UPred M} (h : satisfiable iprop(∃ α, P α)) : ∃ α, satisfiable (P α) :=
  satisfiable_exists h

end

end IrisTest
