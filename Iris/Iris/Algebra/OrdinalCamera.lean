/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra.Numbers
public import Ordinals.Ordinal.Natural

/-!
# The ordinal camera

`Ordinals.NatOrdinal` with the natural (Hessenberg) sum is a discrete, unital, cancelable camera
in which all elements are valid (Transfinite Iris: `algebra/ordinals.v`). The camera operation
must be commutative and cancelable, so it is the natural sum and not the standard sum.
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

theorem NatOrdinal.valid (a : NatOrdinal.{u}) : ✓ a :=
  CMRA.valid_iff_validN.mpr fun _ => trivial

end Iris
