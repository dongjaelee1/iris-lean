/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Ordinal.Arith
public import Ordinals.Tree.Hessenberg

/-!
# The natural (Hessenberg) sum of ordinals

The natural sum `a +ₕ b` of `Ordinals.Tree.Hessenberg` under the quotient. Unlike `+`, it is
commutative. Transfinite Iris uses it as the operation of its ordinal camera.

`NatOrdinal` is a type synonym of `Ordinal` whose `+` is the natural sum.
-/

@[expose] public section

namespace Ordinals

universe u v

namespace Ordinal

/-- The natural (Hessenberg) sum (snu-sf: `Hessenberg.add`). -/
def nadd : Ordinal.{u} → Ordinal.{u} → Ordinal.{u} :=
  Quotient.lift₂ (fun s t => mk (OTree.nadd s t)) fun _ _ _ _ hs ht =>
    sound (OTree.nadd_congr hs ht)

@[inherit_doc] scoped infixl:65 " +ₕ " => Ordinal.nadd

@[simp] theorem mk_nadd_mk (s t : OTree.{u}) : mk s +ₕ mk t = mk (OTree.nadd s t) :=
  rfl

theorem nadd_comm (a b : Ordinal.{u}) : a +ₕ b = b +ₕ a :=
  Ordinal.inductionOn₂ a b fun s t => sound (OTree.nadd_comm s t)

theorem nadd_assoc (a b c : Ordinal.{u}) : a +ₕ b +ₕ c = a +ₕ (b +ₕ c) :=
  Ordinal.inductionOn₃ a b c fun r s t => sound (OTree.nadd_assoc r s t)

@[simp] theorem nadd_zero (a : Ordinal.{u}) : a +ₕ 0 = a :=
  Ordinal.inductionOn a fun s => sound (OTree.nadd_zero s)

@[simp] theorem zero_nadd (a : Ordinal.{u}) : 0 +ₕ a = a :=
  Ordinal.inductionOn a fun s => sound (OTree.zero_nadd s)

theorem nadd_succ (a b : Ordinal.{u}) : a +ₕ succ b = succ (a +ₕ b) :=
  Ordinal.inductionOn₂ a b fun s t => sound (OTree.nadd_succ s t)

theorem succ_nadd (a b : Ordinal.{u}) : succ a +ₕ b = succ (a +ₕ b) :=
  Ordinal.inductionOn₂ a b fun s t => sound (OTree.succ_nadd s t)

theorem le_self_nadd (a b : Ordinal.{u}) : a ≤ a +ₕ b :=
  Ordinal.inductionOn₂ a b OTree.le_self_nadd

theorem le_nadd_self (a b : Ordinal.{u}) : b ≤ a +ₕ b :=
  Ordinal.inductionOn₂ a b OTree.le_nadd_self

theorem nadd_le_nadd {a a' b b' : Ordinal.{u}} (ha : a ≤ a') (hb : b ≤ b') : a +ₕ b ≤ a' +ₕ b' := by
  induction a, a' using Ordinal.inductionOn₂ with
  | _ s s' => induction b, b' using Ordinal.inductionOn₂ with
    | _ t t' => exact OTree.nadd_mono ha hb

theorem nadd_lt_nadd_left {b c : Ordinal.{u}} (h : b < c) (a : Ordinal.{u}) : a +ₕ b < a +ₕ c := by
  induction a using Ordinal.ind with
  | _ s => induction b, c using Ordinal.inductionOn₂ with
    | _ t t' => exact OTree.nadd_lt_nadd_left h s

theorem nadd_lt_nadd_right {a b : Ordinal.{u}} (h : a < b) (c : Ordinal.{u}) : a +ₕ c < b +ₕ c := by
  induction c using Ordinal.ind with
  | _ t => induction a, b using Ordinal.inductionOn₂ with
    | _ s s' => exact OTree.nadd_lt_nadd_right h t

theorem nadd_lt_nadd_iff_left (a : Ordinal.{u}) {b c : Ordinal.{u}} : a +ₕ b < a +ₕ c ↔ b < c :=
  ⟨fun h => Ordinal.not_le.mp fun h' =>
      Ordinal.not_le_of_lt h (nadd_le_nadd Ordinal.le_rfl h'),
   fun h => nadd_lt_nadd_left h a⟩

theorem nadd_le_nadd_iff_left (a : Ordinal.{u}) {b c : Ordinal.{u}} : a +ₕ b ≤ a +ₕ c ↔ b ≤ c :=
  ⟨fun h => Ordinal.not_lt.mp fun h' => Ordinal.not_le_of_lt (nadd_lt_nadd_left h' a) h,
   fun h => nadd_le_nadd Ordinal.le_rfl h⟩

theorem nadd_left_cancel (a : Ordinal.{u}) {b c : Ordinal.{u}} (h : a +ₕ b = a +ₕ c) : b = c :=
  Ordinal.le_antisymm ((nadd_le_nadd_iff_left a).mp (Ordinal.le_of_eq h))
    ((nadd_le_nadd_iff_left a).mp (Ordinal.le_of_eq h.symm))

theorem nadd_right_cancel {a b : Ordinal.{u}} (c : Ordinal.{u}) (h : a +ₕ c = b +ₕ c) : a = b :=
  nadd_left_cancel c (by rw [nadd_comm c a, nadd_comm c b]; exact h)

theorem lt_nadd_of_pos_right (a : Ordinal.{u}) {b : Ordinal.{u}} (h : 0 < b) : a < a +ₕ b := by
  induction a using Ordinal.ind with
  | _ s => induction b using Ordinal.ind with
    | _ t => exact OTree.lt_nadd_of_pos_right s h

/-- `a +ₕ b` is the least ordinal above `a' +ₕ b` for `a' < a` and above `a +ₕ b'` for `b' < b`
(snu-sf: `Hessenberg.add_spec`). -/
theorem nadd_le_iff {a b c : Ordinal.{u}} :
    a +ₕ b ≤ c ↔ (∀ a', a' < a → a' +ₕ b < c) ∧ (∀ b', b' < b → a +ₕ b' < c) := by
  constructor
  · exact fun h => ⟨fun a' ha' => Ordinal.lt_of_lt_of_le (nadd_lt_nadd_right ha' b) h,
      fun b' hb' => Ordinal.lt_of_lt_of_le (nadd_lt_nadd_left hb' a) h⟩
  · intro ⟨ha, hb⟩
    induction a using Ordinal.ind with
    | _ s => induction b using Ordinal.ind with
      | _ t => induction c using Ordinal.ind with
        | _ r =>
          exact OTree.nadd_le_of_forall_lt (fun s' hs' => ha (mk s') hs')
            (fun t' ht' => hb (mk t') ht')

theorem nadd_ofNat (m n : Nat) : ofNat.{u} m +ₕ ofNat n = ofNat (m + n) :=
  sound (OTree.nadd_ofNat m n)

theorem lift_nadd (a b : Ordinal.{u}) : lift.{u, v} (a +ₕ b) = lift a +ₕ lift b :=
  Ordinal.inductionOn₂ a b fun s t => sound (OTree.lift_nadd s t)

end Ordinal

/-- The ordinals with the natural sum as `+`. -/
def NatOrdinal : Type (u + 1) :=
  Ordinal.{u}

namespace NatOrdinal

/-- The ordinal of a natural-sum ordinal. -/
def toOrdinal : NatOrdinal.{u} → Ordinal.{u} :=
  id

/-- The natural-sum ordinal of an ordinal. -/
def ofOrdinal : Ordinal.{u} → NatOrdinal.{u} :=
  id

instance : LE NatOrdinal.{u} := inferInstanceAs (LE Ordinal.{u})
instance : LT NatOrdinal.{u} := inferInstanceAs (LT Ordinal.{u})
instance : Zero NatOrdinal.{u} := inferInstanceAs (Zero Ordinal.{u})
instance : Inhabited NatOrdinal.{u} := ⟨0⟩
instance : Add NatOrdinal.{u} := ⟨Ordinal.nadd⟩

theorem add_def (a b : NatOrdinal.{u}) : a + b = ofOrdinal (Ordinal.nadd a.toOrdinal b.toOrdinal) :=
  rfl

protected theorem add_comm (a b : NatOrdinal.{u}) : a + b = b + a :=
  Ordinal.nadd_comm a b

protected theorem add_assoc (a b c : NatOrdinal.{u}) : a + b + c = a + (b + c) :=
  Ordinal.nadd_assoc a b c

@[simp] protected theorem zero_add (a : NatOrdinal.{u}) : 0 + a = a :=
  Ordinal.zero_nadd a

@[simp] protected theorem add_zero (a : NatOrdinal.{u}) : a + 0 = a :=
  Ordinal.nadd_zero a

protected theorem add_left_cancel (a : NatOrdinal.{u}) {b c : NatOrdinal.{u}} (h : a + b = a + c) :
    b = c :=
  Ordinal.nadd_left_cancel a h

end NatOrdinal

end Ordinals
