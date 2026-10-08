/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.BI.DerivedLawsLater
public import Iris.Algebra.IProp

/-! Tests of the Nat choice, `SI := Nat`. -/

@[expose] public section

namespace IrisTest
open Iris BI

example : SI = Nat := rfl

example : SIdxFinite SI := inferInstance

example (GF : BundledGFunctors.{0}) : Type := IProp GF

/-- The laws for finite indices apply with no hypothesis. -/
example {PROP : Type _} [BI PROP] {P Q : PROP} : ▷ (P ∗ Q) ⊢ ▷ P ∗ ▷ Q := later_sep_1

example {PROP : Type _} [BI PROP] {Φ : Nat → PROP} : (∃ n, ▷ Φ n) ⊣⊢ ▷ (∃ n, Φ n) :=
  later_exists

end IrisTest
