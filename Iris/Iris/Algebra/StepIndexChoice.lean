/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra.StepIndex
public import Iris.Std.Classes
public meta import Iris.Std.RocqPorting

/-!
# The step-index type of this build

Iris uses one step-index type, `Iris.SI`, in all classes and lemmas. This file is the only file
that sets it. To build Iris for a different step-index type, change `SI` and its two instances
below, and change nothing else.

The library uses only the `SIdx` interface of `SI` (and `SIdxFinite` where a finite index is
necessary). `SI` is a `def`, not an `abbrev`, so that the library does not see the facts of
`Nat` by accident. `SI` is the only type with an `SIdx` instance: `natSIdx` is a `def`, so that a
search for `SIdx ?I` (the index is an `outParam`) always finds `SI`.
-/

@[expose] public section

namespace Iris

@[reducible, rocq_alias natSI, rocq_alias nat_sidx_mixin]
def natSIdx : SIdx Nat where
  zero := 0
  succ := Nat.succ
  lt_trans := Nat.lt_trans
  lt_wf := Nat.lt_wfRel.wf
  lt_trichotomyT n m :=
    if h : n < m then .inl h
    else if he : n = m then .inr <| .inl he
    else .inr <| .inr (by omega)
  le_lteq {_ _} := Nat.le_iff_lt_or_eq
  not_lt_zero n := by simp
  lt_succ_self n := by simp
  succ_le_of_lt h := h
  weak_case
    | 0 => .inr (by omega)
    | m + 1 => .inl ⟨_, rfl⟩

@[rocq_alias nat_sidx_finite]
theorem natSIdxFinite : @SIdxFinite Nat natSIdx :=
  letI := natSIdx
  { finite_index := fun | 0 => .inl rfl | n + 1 => .inr ⟨n, rfl⟩ }

/-- The step-index type of this build. -/
def SI : Type := Nat

instance instSIdxSI : SIdx SI := natSIdx

instance instSIdxFiniteSI : SIdxFinite SI := natSIdxFinite

end Iris
