/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra.Numbers
public import Ordinals.Ordinal.Natural

/-!
# The ordinal camera

The ordinals with the natural (Hessenberg) sum are a discrete, unital, cancelable camera:
`Ordinals.NatOrdinal`, where `a + b` is the natural sum `a +ₕ b`, the unit is `0`, and every
element is valid. This is the camera of Transfinite Iris (`algebra/ordinals.v`, `ordR`), for
example for ghost state that counts down along the ordinals in termination proofs.

The natural sum, and not the standard sum, is necessary: the camera operation must be
commutative and cancelable.
-/

@[expose] public noncomputable section

namespace Iris

open _root_.Std (Associative Commutative LeftIdentity LawfulLeftIdentity)
open Iris OFE COFE CommMonoidLike Ordinals

universe u

instance : Associative (α := NatOrdinal.{u}) (· + ·) := ⟨NatOrdinal.add_assoc⟩
instance : Commutative (α := NatOrdinal.{u}) (· + ·) := ⟨NatOrdinal.add_comm⟩
instance : LeftIdentity (α := NatOrdinal.{u}) (· + ·) Zero.zero where
instance : LawfulLeftIdentity (α := NatOrdinal.{u}) (· + ·) Zero.zero := ⟨NatOrdinal.zero_add⟩
instance : LeftCancelAdd NatOrdinal.{u} := ⟨fun h => NatOrdinal.add_left_cancel _ h⟩

instance : COFE NatOrdinal.{u} := COFE.ofDiscrete _
instance : Discrete NatOrdinal.{u} := ⟨fun h => h⟩

/-- The ordinal camera (Transfinite Iris: `ordR`, `ordUR`). -/
instance : UCMRA NatOrdinal.{u} := CommMonoidLike.instUCMRA
instance : CMRA.Discrete NatOrdinal.{u} := CommMonoidLike.instDiscrete
instance {a : NatOrdinal.{u}} : CMRA.Cancelable a := CommMonoidLike.instCancelable

/-- The camera operation is the natural sum. -/
theorem NatOrdinal.op_eq (a b : NatOrdinal.{u}) : a • b = a + b :=
  rfl

/-- Each element is valid. -/
theorem NatOrdinal.valid (a : NatOrdinal.{u}) : ✓ a :=
  CMRA.valid_iff_validN.mpr fun _ => trivial

end Iris
