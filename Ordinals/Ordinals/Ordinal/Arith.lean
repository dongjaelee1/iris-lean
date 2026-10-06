/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Ordinal.Lift
public import Ordinals.Tree.Arith

/-!
# Ordinal arithmetic

The standard ordinal sum `a + b`, product `a * b` and power `a ^ b`: the tree operations of
`Ordinals.Tree.Arith` (snu-sf `OrdArith`) under the quotient. The lemmas are equalities.

The power follows snu-sf: `a ^ b := orec 1 (· * a) b`. The base `1` is part of each join, so
`0 ^ b = 1` for every `b` (`zero_pow`), and the usual laws `pow_succ`, `pow_add`, `pow_mul` need
`0 < a`.
-/

@[expose] public section

namespace Ordinals

universe u v

namespace Ordinal

/-! ## Instances -/

instance : Add Ordinal.{u} :=
  ⟨Quotient.lift₂ (fun s t => mk (OTree.add s t)) fun _ _ _ _ hs ht =>
    sound (OTree.add_congr hs ht)⟩

instance : Mul Ordinal.{u} :=
  ⟨Quotient.lift₂ (fun s t => mk (OTree.mul s t)) fun _ _ _ _ hs ht =>
    sound (OTree.mul_congr hs ht)⟩

instance : Pow Ordinal.{u} Ordinal.{u} :=
  ⟨Quotient.lift₂ (fun s t => mk (OTree.pow s t)) fun _ _ _ _ hs ht =>
    sound (OTree.pow_congr hs ht)⟩

@[simp] theorem mk_add_mk (s t : OTree.{u}) : mk s + mk t = mk (OTree.add s t) :=
  rfl

@[simp] theorem mk_mul_mk (s t : OTree.{u}) : mk s * mk t = mk (OTree.mul s t) :=
  rfl

@[simp] theorem mk_pow_mk (s t : OTree.{u}) : mk s ^ mk t = mk (OTree.pow s t) :=
  rfl

/-! ## Sum -/

@[simp] protected theorem add_zero (a : Ordinal.{u}) : a + 0 = a :=
  Ordinal.inductionOn a fun s => sound (OTree.add_zero s)

@[simp] protected theorem zero_add (a : Ordinal.{u}) : 0 + a = a :=
  Ordinal.inductionOn a fun s => sound (OTree.zero_add s)

protected theorem add_succ (a b : Ordinal.{u}) : a + succ b = succ (a + b) :=
  Ordinal.inductionOn₂ a b fun s t => sound (OTree.add_succ s t)

theorem add_one_eq_succ (a : Ordinal.{u}) : a + 1 = succ a := by
  rw [one_eq_succ_zero, Ordinal.add_succ, Ordinal.add_zero]

protected theorem add_assoc (a b c : Ordinal.{u}) : a + b + c = a + (b + c) :=
  Ordinal.inductionOn₃ a b c fun r s t => sound (OTree.add_assoc r s t)

protected theorem le_add_right (a b : Ordinal.{u}) : a ≤ a + b :=
  Ordinal.inductionOn₂ a b OTree.le_add_right

protected theorem le_add_left (a b : Ordinal.{u}) : b ≤ a + b :=
  Ordinal.inductionOn₂ a b OTree.le_add_left

protected theorem add_le_add_left {b c : Ordinal.{u}} (h : b ≤ c) (a : Ordinal.{u}) :
    a + b ≤ a + c := by
  induction a using Ordinal.ind with
  | _ r => induction b, c using Ordinal.inductionOn₂ with
    | _ s t => exact OTree.add_le_add_left h r

protected theorem add_lt_add_left {b c : Ordinal.{u}} (h : b < c) (a : Ordinal.{u}) :
    a + b < a + c := by
  induction a using Ordinal.ind with
  | _ r => induction b, c using Ordinal.inductionOn₂ with
    | _ s t => exact OTree.add_lt_add_left h r

protected theorem add_le_add_right {a b : Ordinal.{u}} (h : a ≤ b) (c : Ordinal.{u}) :
    a + c ≤ b + c := by
  induction c using Ordinal.ind with
  | _ r => induction a, b using Ordinal.inductionOn₂ with
    | _ s t => exact OTree.add_le_add_right h r

protected theorem add_le_add {a a' b b' : Ordinal.{u}} (ha : a ≤ a') (hb : b ≤ b') :
    a + b ≤ a' + b' :=
  Ordinal.le_trans (Ordinal.add_le_add_right ha b) (Ordinal.add_le_add_left hb a')

protected theorem lt_add_of_pos_right (a : Ordinal.{u}) {b : Ordinal.{u}} (h : 0 < b) :
    a < a + b := by
  induction a using Ordinal.ind with
  | _ s => induction b using Ordinal.ind with
    | _ t => exact OTree.lt_add_of_pos_right s h

protected theorem add_lt_add_iff_left (a : Ordinal.{u}) {b c : Ordinal.{u}} :
    a + b < a + c ↔ b < c :=
  ⟨fun h => Ordinal.not_le.mp fun h' => Ordinal.not_le_of_lt h (Ordinal.add_le_add_left h' a),
   fun h => Ordinal.add_lt_add_left h a⟩

protected theorem add_le_add_iff_left (a : Ordinal.{u}) {b c : Ordinal.{u}} :
    a + b ≤ a + c ↔ b ≤ c :=
  ⟨fun h => Ordinal.not_lt.mp fun h' => Ordinal.not_le_of_lt (Ordinal.add_lt_add_left h' a) h,
   fun h => Ordinal.add_le_add_left h a⟩

protected theorem add_left_cancel (a : Ordinal.{u}) {b c : Ordinal.{u}} (h : a + b = a + c) :
    b = c :=
  Ordinal.le_antisymm ((Ordinal.add_le_add_iff_left a).mp (Ordinal.le_of_eq h))
    ((Ordinal.add_le_add_iff_left a).mp (Ordinal.le_of_eq h.symm))

theorem add_sup (a : Ordinal.{u}) {ι : Type u} (f : ι → Ordinal.{u}) :
    a + sup f = max a (sup fun i => a + f i) := by
  induction a using Ordinal.ind with
  | _ s =>
    obtain ⟨g, rfl⟩ := exists_eq_mk_comp f
    simp only [sup_mk, mk_add_mk, max_mk]
    exact sound (OTree.add_sup s g)

theorem add_sup_of_nonempty (a : Ordinal.{u}) {ι : Type u} [Nonempty ι] (f : ι → Ordinal.{u}) :
    a + sup f = sup fun i => a + f i := by
  induction a using Ordinal.ind with
  | _ s =>
    obtain ⟨g, rfl⟩ := exists_eq_mk_comp f
    simp only [sup_mk, mk_add_mk]
    exact sound (OTree.add_sup_of_nonempty s g)

theorem add_max (a b c : Ordinal.{u}) : a + max b c = max (a + b) (a + c) :=
  Ordinal.inductionOn₃ a b c fun r s t => sound (OTree.add_max r s t)

theorem ofNat_add (m n : Nat) : ofNat.{u} (m + n) = ofNat m + ofNat n :=
  sound (OTree.ofNat_add m n)

theorem natCast_add (m n : Nat) : ((m + n : Nat) : Ordinal.{u}) = (m : Ordinal.{u}) + n :=
  ofNat_add m n

theorem omega_eq_sup : (ω : Ordinal.{u}) = sup fun n : ULift.{u} Nat => ofNat n.down :=
  (sup_mk _).symm

/-- `1 + ω = ω`, but `ω < ω + 1`: the sum is not commutative. -/
theorem one_add_omega : (1 : Ordinal.{u}) + ω = ω := by
  rw [omega_eq_sup, add_sup]
  refine Ordinal.le_antisymm (Ordinal.max_le_iff.mpr ⟨?_, sup_le fun n => ?_⟩) (sup_le fun n => ?_)
  · exact le_sup (fun n : ULift.{u} Nat => ofNat n.down) ⟨1⟩
  · rw [show (1 : Ordinal.{u}) + ofNat n.down = ofNat (1 + n.down) from (ofNat_add 1 n.down).symm]
    exact le_sup (fun n : ULift.{u} Nat => ofNat n.down) ⟨1 + n.down⟩
  · exact Ordinal.le_trans (Ordinal.le_add_left 1 (ofNat n.down))
      (Ordinal.le_trans (le_sup (fun n : ULift.{u} Nat => 1 + ofNat n.down) n)
        (Ordinal.le_max_right _ _))

theorem omega_lt_omega_add_one : (ω : Ordinal.{u}) < ω + 1 := by
  rw [add_one_eq_succ]
  exact lt_succ ω

/-! ## Product -/

@[simp] protected theorem mul_zero (a : Ordinal.{u}) : a * 0 = 0 :=
  Ordinal.inductionOn a fun s => sound (OTree.mul_zero s)

@[simp] protected theorem zero_mul (a : Ordinal.{u}) : 0 * a = 0 :=
  Ordinal.inductionOn a fun s => sound (OTree.zero_mul s)

protected theorem mul_succ (a b : Ordinal.{u}) : a * succ b = a * b + a :=
  Ordinal.inductionOn₂ a b fun s t => sound (OTree.mul_succ s t)

@[simp] protected theorem mul_one (a : Ordinal.{u}) : a * 1 = a :=
  Ordinal.inductionOn a fun s => sound (OTree.mul_one s)

@[simp] protected theorem one_mul (a : Ordinal.{u}) : 1 * a = a :=
  Ordinal.inductionOn a fun s => sound (OTree.one_mul s)

protected theorem mul_add (a b c : Ordinal.{u}) : a * (b + c) = a * b + a * c :=
  Ordinal.inductionOn₃ a b c fun r s t => sound (OTree.mul_add r s t)

protected theorem mul_assoc (a b c : Ordinal.{u}) : a * b * c = a * (b * c) :=
  Ordinal.inductionOn₃ a b c fun r s t => sound (OTree.mul_assoc r s t)

protected theorem mul_le_mul_left {b c : Ordinal.{u}} (h : b ≤ c) (a : Ordinal.{u}) :
    a * b ≤ a * c := by
  induction a using Ordinal.ind with
  | _ r => induction b, c using Ordinal.inductionOn₂ with
    | _ s t => exact OTree.mul_le_mul_left h r

protected theorem mul_le_mul_right {a b : Ordinal.{u}} (h : a ≤ b) (c : Ordinal.{u}) :
    a * c ≤ b * c := by
  induction c using Ordinal.ind with
  | _ r => induction a, b using Ordinal.inductionOn₂ with
    | _ s t => exact OTree.mul_le_mul_right h r

protected theorem mul_le_mul {a a' b b' : Ordinal.{u}} (ha : a ≤ a') (hb : b ≤ b') :
    a * b ≤ a' * b' :=
  Ordinal.le_trans (Ordinal.mul_le_mul_right ha b) (Ordinal.mul_le_mul_left hb a')

protected theorem mul_lt_mul_of_pos_left {a b c : Ordinal.{u}} (h : b < c) (ha : 0 < a) :
    a * b < a * c := by
  induction a using Ordinal.ind with
  | _ r => induction b, c using Ordinal.inductionOn₂ with
    | _ s t => exact OTree.mul_lt_mul_of_pos_left h ha

theorem mul_sup (a : Ordinal.{u}) {ι : Type u} (f : ι → Ordinal.{u}) :
    a * sup f = sup fun i => a * f i := by
  induction a using Ordinal.ind with
  | _ s =>
    obtain ⟨g, rfl⟩ := exists_eq_mk_comp f
    simp only [sup_mk, mk_mul_mk]
    exact sound (OTree.mul_sup s g)

theorem mul_max (a b c : Ordinal.{u}) : a * max b c = max (a * b) (a * c) :=
  Ordinal.inductionOn₃ a b c fun r s t => sound (OTree.mul_max r s t)

theorem ofNat_mul (m n : Nat) : ofNat.{u} (m * n) = ofNat m * ofNat n :=
  sound (OTree.ofNat_mul m n)

/-! ## Power -/

@[simp] protected theorem pow_zero (a : Ordinal.{u}) : a ^ (0 : Ordinal.{u}) = 1 :=
  Ordinal.inductionOn a fun s => sound (OTree.pow_zero s)

/-- With snu-sf's definition, the base `0` gives `1` for each exponent. -/
theorem zero_pow (b : Ordinal.{u}) : (0 : Ordinal.{u}) ^ b = 1 :=
  Ordinal.inductionOn b fun t => sound (OTree.pow_zero_left t)

protected theorem pow_succ {a : Ordinal.{u}} (ha : 0 < a) (b : Ordinal.{u}) :
    a ^ succ b = a ^ b * a := by
  induction a using Ordinal.ind with
  | _ s => induction b using Ordinal.ind with
    | _ t => exact sound (OTree.pow_succ ha t)

protected theorem pow_one {a : Ordinal.{u}} (ha : 0 < a) : a ^ (1 : Ordinal.{u}) = a := by
  induction a using Ordinal.ind with
  | _ s => exact sound (OTree.pow_one ha)

@[simp] protected theorem one_pow (b : Ordinal.{u}) : (1 : Ordinal.{u}) ^ b = 1 :=
  Ordinal.inductionOn b fun t => sound (OTree.one_pow t)

protected theorem pow_add {a : Ordinal.{u}} (ha : 0 < a) (b c : Ordinal.{u}) :
    a ^ (b + c) = a ^ b * a ^ c := by
  induction a using Ordinal.ind with
  | _ s => induction b, c using Ordinal.inductionOn₂ with
    | _ t t' => exact sound (OTree.pow_add ha t t')

protected theorem pow_mul {a : Ordinal.{u}} (ha : 0 < a) (b c : Ordinal.{u}) :
    a ^ (b * c) = (a ^ b) ^ c := by
  induction a using Ordinal.ind with
  | _ s => induction b, c using Ordinal.inductionOn₂ with
    | _ t t' => exact sound (OTree.pow_mul ha t t')

protected theorem zero_lt_pow (a b : Ordinal.{u}) : 0 < a ^ b :=
  Ordinal.inductionOn₂ a b OTree.zero_lt_pow

protected theorem pow_le_pow_right (a : Ordinal.{u}) {b c : Ordinal.{u}} (h : b ≤ c) :
    a ^ b ≤ a ^ c := by
  induction a using Ordinal.ind with
  | _ s => induction b, c using Ordinal.inductionOn₂ with
    | _ t t' => exact OTree.pow_le_pow_right s h

protected theorem pow_le_pow_left {a a' : Ordinal.{u}} (h : a ≤ a') (b : Ordinal.{u}) :
    a ^ b ≤ a' ^ b := by
  induction b using Ordinal.ind with
  | _ t => induction a, a' using Ordinal.inductionOn₂ with
    | _ s s' => exact OTree.pow_le_pow_left h t

protected theorem pow_lt_pow_right {a : Ordinal.{u}} (ha : 1 < a) {b c : Ordinal.{u}}
    (h : b < c) : a ^ b < a ^ c := by
  induction a using Ordinal.ind with
  | _ s => induction b, c using Ordinal.inductionOn₂ with
    | _ t t' => exact OTree.pow_lt_pow_right ha h

theorem pow_sup (a : Ordinal.{u}) {ι : Type u} (f : ι → Ordinal.{u}) :
    a ^ sup f = max 1 (sup fun i => a ^ f i) := by
  induction a using Ordinal.ind with
  | _ s =>
    obtain ⟨g, rfl⟩ := exists_eq_mk_comp f
    simp only [sup_mk, mk_pow_mk]
    exact sound (OTree.pow_sup s g)

theorem pow_sup_of_nonempty (a : Ordinal.{u}) {ι : Type u} [Nonempty ι] (f : ι → Ordinal.{u}) :
    a ^ sup f = sup fun i => a ^ f i := by
  induction a using Ordinal.ind with
  | _ s =>
    obtain ⟨g, rfl⟩ := exists_eq_mk_comp f
    simp only [sup_mk, mk_pow_mk]
    exact sound (OTree.pow_sup_of_nonempty s g)

theorem ofNat_pow {m : Nat} (hm : 0 < m) (n : Nat) : ofNat.{u} (m ^ n) = ofNat m ^ ofNat n :=
  sound (OTree.ofNat_pow hm n)

end Ordinal

end Ordinals
