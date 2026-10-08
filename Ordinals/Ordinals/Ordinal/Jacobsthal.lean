/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Ordinal.Natural
public import Ordinals.Tree.HessenbergArith
public import Ordinals.Tree.Jacobsthal

/-!
# Jacobsthal product and power of ordinals

The Jacobsthal product `a ×ⱼ b` is the repeated natural sum: `a ×ⱼ succ b = a +ₕ (a ×ⱼ b)`. The
Jacobsthal power `a ^ⱼ b` is the repeated Jacobsthal product. They are the tree operations of
`Ordinals.Tree.Jacobsthal` under the quotient.
-/

@[expose] public section

namespace Ordinals

universe u

namespace Ordinal

/-- The Jacobsthal product (snu-sf: `Jacobsthal.mult`). -/
def jmul : Ordinal.{u} → Ordinal.{u} → Ordinal.{u} :=
  Quotient.lift₂ (fun s t => mk (OTree.jmul s t)) fun _ _ _ _ hs ht =>
    sound (OTree.jmul_congr hs ht)

/-- The Jacobsthal power (snu-sf: `Jacobsthal.expn`). -/
def jpow : Ordinal.{u} → Ordinal.{u} → Ordinal.{u} :=
  Quotient.lift₂ (fun s t => mk (OTree.jpow s t)) fun _ _ _ _ hs ht =>
    sound (OTree.jpow_congr hs ht)

@[inherit_doc] scoped infixl:70 " ×ⱼ " => Ordinal.jmul

@[inherit_doc] scoped infixr:75 " ^ⱼ " => Ordinal.jpow

@[simp] theorem mk_jmul_mk (s t : OTree.{u}) : mk s ×ⱼ mk t = mk (OTree.jmul s t) :=
  rfl

@[simp] theorem mk_jpow_mk (s t : OTree.{u}) : mk s ^ⱼ mk t = mk (OTree.jpow s t) :=
  rfl

/-! ## The standard and the natural operations -/

/-- snu-sf: `Hessenberg.arith_add_larger`. -/
theorem add_le_nadd (a b : Ordinal.{u}) : a + b ≤ a +ₕ b :=
  Ordinal.inductionOn₂ a b OTree.add_le_nadd

/-- snu-sf: `Hessenberg.arith_add_from_nat`. -/
theorem nadd_ofNat_eq_add (a : Ordinal.{u}) (n : Nat) : a +ₕ ofNat n = a + ofNat n :=
  Ordinal.inductionOn a fun s => sound (OTree.nadd_ofNat_equiv_add s n)

/-- snu-sf: `Jacobsthal.arith_mult_larger`. -/
theorem mul_le_jmul (a b : Ordinal.{u}) : a * b ≤ a ×ⱼ b :=
  Ordinal.inductionOn₂ a b OTree.mul_le_jmul

/-- snu-sf: `Jacobsthal.arith_expn_larger`. -/
theorem pow_le_jpow (a b : Ordinal.{u}) : a ^ b ≤ a ^ⱼ b :=
  Ordinal.inductionOn₂ a b OTree.pow_le_jpow

/-! ## Jacobsthal product -/

@[simp] theorem jmul_zero (a : Ordinal.{u}) : a ×ⱼ 0 = 0 :=
  Ordinal.inductionOn a fun s => sound (OTree.jmul_zero s)

@[simp] theorem zero_jmul (a : Ordinal.{u}) : 0 ×ⱼ a = 0 :=
  Ordinal.inductionOn a fun s => sound (OTree.zero_jmul s)

theorem jmul_succ (a b : Ordinal.{u}) : a ×ⱼ succ b = a +ₕ (a ×ⱼ b) :=
  Ordinal.inductionOn₂ a b fun s t => sound (OTree.jmul_succ s t)

@[simp] theorem jmul_one (a : Ordinal.{u}) : a ×ⱼ 1 = a :=
  Ordinal.inductionOn a fun s => sound (OTree.jmul_one s)

@[simp] theorem one_jmul (a : Ordinal.{u}) : 1 ×ⱼ a = a :=
  Ordinal.inductionOn a fun s => sound (OTree.one_jmul s)

/-- snu-sf: `ClassicJacobsthal.mult_dist`. -/
theorem jmul_nadd (a b c : Ordinal.{u}) : a ×ⱼ (b +ₕ c) = a ×ⱼ b +ₕ a ×ⱼ c :=
  Ordinal.inductionOn₃ a b c fun r s t => sound (OTree.jmul_nadd r s t)

/-- snu-sf: `ClassicJacobsthal.mult_assoc`. -/
theorem jmul_assoc (a b c : Ordinal.{u}) : a ×ⱼ b ×ⱼ c = a ×ⱼ (b ×ⱼ c) :=
  Ordinal.inductionOn₃ a b c fun r s t => sound (OTree.jmul_assoc r s t)

theorem jmul_le_jmul {a a' b b' : Ordinal.{u}} (ha : a ≤ a') (hb : b ≤ b') :
    a ×ⱼ b ≤ a' ×ⱼ b' := by
  induction a, a' using Ordinal.inductionOn₂ with
  | _ s s' => induction b, b' using Ordinal.inductionOn₂ with
    | _ t t' => exact OTree.jmul_le_jmul ha hb

theorem jmul_lt_jmul_of_pos_left {a b c : Ordinal.{u}} (h : b < c) (ha : 0 < a) :
    a ×ⱼ b < a ×ⱼ c := by
  induction a using Ordinal.ind with
  | _ r => induction b, c using Ordinal.inductionOn₂ with
    | _ s t => exact OTree.jmul_lt_jmul_of_pos_left h ha

theorem jmul_sup (a : Ordinal.{u}) {ι : Type u} (f : ι → Ordinal.{u}) :
    a ×ⱼ sup f = sup fun i => a ×ⱼ f i := by
  induction a using Ordinal.ind with
  | _ s =>
    obtain ⟨g, rfl⟩ := exists_eq_mk_comp f
    simp only [sup_mk, mk_jmul_mk]
    exact sound (OTree.jmul_sup s g)

theorem jmul_max (a b c : Ordinal.{u}) : a ×ⱼ max b c = max (a ×ⱼ b) (a ×ⱼ c) :=
  Ordinal.inductionOn₃ a b c fun r s t => sound (OTree.jmul_max r s t)

theorem ofNat_jmul (m n : Nat) : ofNat.{u} (m * n) = ofNat m ×ⱼ ofNat n :=
  sound (OTree.ofNat_jmul m n)

/-! ## Jacobsthal power -/

@[simp] theorem jpow_zero (a : Ordinal.{u}) : a ^ⱼ 0 = 1 :=
  Ordinal.inductionOn a fun s => sound (OTree.jpow_zero s)

theorem zero_jpow (b : Ordinal.{u}) : 0 ^ⱼ b = 1 :=
  Ordinal.inductionOn b fun t => sound (OTree.jpow_zero_left t)

theorem jpow_succ {a : Ordinal.{u}} (ha : 0 < a) (b : Ordinal.{u}) :
    a ^ⱼ succ b = a ^ⱼ b ×ⱼ a := by
  induction a using Ordinal.ind with
  | _ s => induction b using Ordinal.ind with
    | _ t => exact sound (OTree.jpow_succ ha t)

theorem jpow_one {a : Ordinal.{u}} (ha : 0 < a) : a ^ⱼ 1 = a := by
  induction a using Ordinal.ind with
  | _ s => exact sound (OTree.jpow_one ha)

@[simp] theorem one_jpow (b : Ordinal.{u}) : 1 ^ⱼ b = 1 :=
  Ordinal.inductionOn b fun t => sound (OTree.one_jpow t)

/-- snu-sf: `ClassicJacobsthal.expn_add`. -/
theorem jpow_add {a : Ordinal.{u}} (ha : 0 < a) (b c : Ordinal.{u}) :
    a ^ⱼ (b + c) = a ^ⱼ b ×ⱼ a ^ⱼ c := by
  induction a using Ordinal.ind with
  | _ s => induction b, c using Ordinal.inductionOn₂ with
    | _ t t' => exact sound (OTree.jpow_add ha t t')

/-- snu-sf: `ClassicJacobsthal.expn_mult`. -/
theorem jpow_mul {a : Ordinal.{u}} (ha : 0 < a) (b c : Ordinal.{u}) :
    a ^ⱼ (b * c) = (a ^ⱼ b) ^ⱼ c := by
  induction a using Ordinal.ind with
  | _ s => induction b, c using Ordinal.inductionOn₂ with
    | _ t t' => exact sound (OTree.jpow_mul ha t t')

theorem jpow_le_jpow {a a' b b' : Ordinal.{u}} (ha : a ≤ a') (hb : b ≤ b') :
    a ^ⱼ b ≤ a' ^ⱼ b' := by
  induction a, a' using Ordinal.inductionOn₂ with
  | _ s s' => induction b, b' using Ordinal.inductionOn₂ with
    | _ t t' => exact OTree.jpow_le_jpow ha hb

theorem jpow_lt_jpow_right {a : Ordinal.{u}} (ha : 1 < a) {b c : Ordinal.{u}} (h : b < c) :
    a ^ⱼ b < a ^ⱼ c := by
  induction a using Ordinal.ind with
  | _ s => induction b, c using Ordinal.inductionOn₂ with
    | _ t t' => exact OTree.jpow_lt_jpow_right ha h

theorem jpow_sup (a : Ordinal.{u}) {ι : Type u} (f : ι → Ordinal.{u}) :
    a ^ⱼ sup f = max 1 (sup fun i => a ^ⱼ f i) := by
  induction a using Ordinal.ind with
  | _ s =>
    obtain ⟨g, rfl⟩ := exists_eq_mk_comp f
    simp only [sup_mk, mk_jpow_mk]
    exact sound (OTree.jpow_sup s g)

theorem ofNat_jpow {m : Nat} (hm : 0 < m) (n : Nat) : ofNat.{u} (m ^ n) = ofNat m ^ⱼ ofNat n :=
  sound (OTree.ofNat_jpow hm n)

end Ordinal

end Ordinals
