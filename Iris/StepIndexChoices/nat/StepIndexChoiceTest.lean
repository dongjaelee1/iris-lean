/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.BI.DerivedLawsLater
public import Iris.Algebra.IProp

/-! Tests of the Nat build, `SI := Nat`. These tests hold only for this choice file
(`Iris/StepIndexChoices/nat/`). -/

@[expose] public section

namespace IrisTest
open Iris BI

example : SI = Nat := rfl

/-- The index is finite. -/
example : SIdxFinite SI := inferInstance

/-- `IProp` is in `Type` for ghost state in `Type`. -/
example (GF : BundledGFunctors.{0}) : Type := IProp GF

/-- The laws for finite indices apply with no hypothesis. -/
example {PROP : Type _} [BI PROP] {P Q : PROP} : ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q := later_sep_1

example {PROP : Type _} [BI PROP] {Φ : Nat → PROP} : (∃ n, ▷ Φ n) ⊣⊢ ▷ (∃ n, Φ n) :=
  later_exists

end IrisTest
