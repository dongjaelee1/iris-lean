/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Instances.UPred.Transfinite

/-! Tests for the existential property `SIdxLarge SI X`. The instances are hypotheses, so the
tests hold for every step-index type. -/

@[expose] public section

namespace IrisTest
open Iris BI UPred

universe v w

section
variable {M : Type} [UCMRA M]

/-- An instance for the type of the quantifier. -/
example {X : Type v} [SIdxLarge SI X] {P : X → UPred M} (h : satisfiable iprop(∃ x, P x)) :
    ∃ x, satisfiable (P x) :=
  satisfiable_exists h

/-- `apply` and `obtain` also find the instance. -/
example {X : Type v} [SIdxLarge SI X] {P : X → UPred M} (h : satisfiable iprop(∃ x, P x)) :
    ∃ x, satisfiable (P x) := by
  apply satisfiable_exists h

example {X : Type v} [SIdxLarge SI X] {P : X → UPred M} (h : satisfiable iprop(∃ x, P x)) :
    True := by
  obtain ⟨_, _⟩ := satisfiable_exists h
  trivial

/-- The existential property for all types of a universe (Rocq's `LargeIndex`). -/
example [∀ X : Type v, SIdxLarge SI X] {X : Type v} {P : X → UPred M}
    (h : satisfiable iprop(∃ x, P x)) : ∃ x, satisfiable (P x) :=
  satisfiable_exists h

/-- Two universes in one proof. -/
example [∀ X : Type v, SIdxLarge SI X] [∀ Y : Type w, SIdxLarge SI Y] {X : Type v} {Y : Type w}
    {P : X → UPred M} {Q : Y → UPred M} (h : satisfiable iprop(∃ x, P x))
    (h' : satisfiable iprop(∃ y, Q y)) :
    (∃ x, satisfiable (P x)) ∧ (∃ y, satisfiable (Q y)) :=
  ⟨satisfiable_exists h, satisfiable_exists h'⟩

/-- A small type in a large universe, through `ULift`. -/
example {X : Type v} [SIdxLarge SI X] {P : ULift.{7} X → UPred M}
    (h : satisfiable iprop(∃ x, P x)) : ∃ x, satisfiable (P x) :=
  satisfiable_exists h

/-- The property for `ULift X` gives it for `X`. -/
example {X : Type v} [SIdxLarge SI (ULift.{w} X)] : SIdxLarge SI X :=
  SIdxLarge.of_ulift.{_, _, w}

/-- The rule of the `Satisfiable` class. (The class has the universe parameters `w` and `v` of its
quantifiers, so the statement gives them.) -/
example {X : Type v} [SIdxLarge SI X] {P : X → UPred M}
    (h : Satisfiable.satisfiable.{0, v} iprop(∃ x, P x)) :
    ∃ x, Satisfiable.satisfiable.{0, v} (P x) :=
  Satisfiable.exists_ h

end

end IrisTest
