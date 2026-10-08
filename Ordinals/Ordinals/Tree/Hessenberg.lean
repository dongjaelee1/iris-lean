/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Tree.Constructions

/-!
# The natural (Hessenberg) sum of trees

`nadd s t` is the least tree above `nadd s' t` for all `s' < s` and above `nadd s t'` for all
`t' < t`. It is commutative, associative and strictly monotone in both arguments.

This file follows snu-sf/Ordinal (`src/Hessenberg.v`, module `Hessenberg`, section `ADD`).
-/

@[expose] public section

namespace Ordinals

universe u v

namespace OTree

/-! ## Induction on two trees -/

/-- Induction on two trees (snu-sf: `double_well_founded_induction`). -/
theorem induction₂ {P : OTree.{u} → OTree.{u} → Prop}
    (h : ∀ s t, (∀ s', s' < s → P s' t) → (∀ t', t' < t → P s t') → P s t)
    (s t : OTree.{u}) : P s t := by
  induction s using lt_wf.induction generalizing t with
  | _ s ihs =>
    induction t using lt_wf.induction with
    | _ t iht => exact h s t (fun s' hs' => ihs s' hs' t) iht

/-! ## Definition -/

/-- The inner recursion of `nadd` on the second tree. For `s = mk ι f`, the function
`naddAux f (fun i => nadd (f i))` is `nadd s`. -/
def naddAux {ι : Type u} (f : ι → OTree.{u}) (r : ι → OTree.{u} → OTree.{u}) :
    OTree.{u} → OTree.{u}
  | mk κ g => max (mk κ fun j => naddAux f r (g j)) (mk ι fun i => r i (mk κ g))

/-- The natural (Hessenberg) sum: its children are `nadd s (t.child j)` and `nadd (s.child i) t`.
It is a nested structural recursion, not `WellFounded.fix`, so that `nadd_mk_mk` is `rfl`
(snu-sf: `Hessenberg.add`). -/
def nadd : OTree.{u} → OTree.{u} → OTree.{u}
  | mk _ f => naddAux f fun i => nadd (f i)

/-- The unfolding equation of `nadd` (snu-sf: `Hessenberg.add_red`). -/
theorem nadd_mk_mk {ι κ : Type u} (f : ι → OTree.{u}) (g : κ → OTree.{u}) :
    nadd (mk ι f) (mk κ g) =
      max (mk κ fun j => nadd (mk ι f) (g j)) (mk ι fun i => nadd (f i) (mk κ g)) :=
  rfl

theorem nadd_eq (s t : OTree.{u}) :
    nadd s t =
      max (mk t.Index fun j => nadd s (t.child j)) (mk s.Index fun i => nadd (s.child i) t) := by
  cases s; cases t; rfl

/-! ## Basic order properties -/

theorem nadd_child_left_lt (s t : OTree.{u}) (i : s.Index) : nadd (s.child i) t < nadd s t := by
  rw [nadd_eq s t]
  exact lt_max_iff.mpr (.inr ⟨i, OTree.le_rfl⟩)

theorem nadd_child_right_lt (s t : OTree.{u}) (j : t.Index) : nadd s (t.child j) < nadd s t := by
  rw [nadd_eq s t]
  exact lt_max_iff.mpr (.inl ⟨j, OTree.le_rfl⟩)

theorem nadd_le_iff_child {s t r : OTree.{u}} :
    nadd s t ≤ r ↔ (∀ i, nadd (s.child i) t < r) ∧ (∀ j, nadd s (t.child j) < r) := by
  rw [nadd_eq s t]
  exact max_le_iff.trans
    ⟨fun h => ⟨mk_le.mp h.2, mk_le.mp h.1⟩, fun h => ⟨mk_le.mpr h.2, mk_le.mpr h.1⟩⟩

theorem lt_nadd_iff_child {r s t : OTree.{u}} :
    r < nadd s t ↔ (∃ i, r ≤ nadd (s.child i) t) ∨ (∃ j, r ≤ nadd s (t.child j)) := by
  rw [nadd_eq s t]
  exact lt_max_iff.trans Or.comm

/-! ## Monotonicity -/

/-- snu-sf: `Hessenberg.le_add_l`. -/
theorem nadd_le_nadd_right {s s' : OTree.{u}} (h : s ≤ s') (t : OTree.{u}) :
    nadd s t ≤ nadd s' t := by
  induction s, t using induction₂ generalizing s' with
  | _ s t ihs iht =>
    refine nadd_le_iff_child.mpr ⟨fun i => ?_, fun j => ?_⟩
    · obtain ⟨k, hk⟩ := OTree.lt_of_lt_of_le (child_lt s i) h
      exact OTree.lt_of_le_of_lt (ihs _ (child_lt s i) hk) (nadd_child_left_lt s' t k)
    · exact OTree.lt_of_le_of_lt (iht _ (child_lt t j) h) (nadd_child_right_lt s' t j)

/-- snu-sf: `Hessenberg.le_add_r`. -/
theorem nadd_le_nadd_left {t t' : OTree.{u}} (h : t ≤ t') (s : OTree.{u}) :
    nadd s t ≤ nadd s t' := by
  induction s, t using induction₂ generalizing t' with
  | _ s t ihs iht =>
    refine nadd_le_iff_child.mpr ⟨fun i => ?_, fun j => ?_⟩
    · exact OTree.lt_of_le_of_lt (ihs _ (child_lt s i) h) (nadd_child_left_lt s t' i)
    · obtain ⟨k, hk⟩ := OTree.lt_of_lt_of_le (child_lt t j) h
      exact OTree.lt_of_le_of_lt (iht _ (child_lt t j) hk) (nadd_child_right_lt s t' k)

/-- snu-sf: `Hessenberg.add_le_proper`. -/
theorem nadd_mono {s s' t t' : OTree.{u}} (hs : s ≤ s') (ht : t ≤ t') :
    nadd s t ≤ nadd s' t' :=
  OTree.le_trans (nadd_le_nadd_right hs t) (nadd_le_nadd_left ht s')

/-- `nadd` respects `≈` (snu-sf: `Hessenberg.add_eq_proper`). -/
theorem nadd_congr {s s' t t' : OTree.{u}} (hs : s ≈ s') (ht : t ≈ t') :
    nadd s t ≈ nadd s' t' :=
  ⟨nadd_mono hs.le ht.le, nadd_mono hs.ge ht.ge⟩

/-- snu-sf: `Hessenberg.eq_add_r`. -/
theorem nadd_congr_left {t t' : OTree.{u}} (h : t ≈ t') (s : OTree.{u}) :
    nadd s t ≈ nadd s t' :=
  nadd_congr (Equiv.refl s) h

/-- snu-sf: `Hessenberg.eq_add_l`. -/
theorem nadd_congr_right {s s' : OTree.{u}} (h : s ≈ s') (t : OTree.{u}) :
    nadd s t ≈ nadd s' t :=
  nadd_congr h (Equiv.refl t)

/-! ## Strict monotonicity -/

/-- snu-sf: `Hessenberg.lt_add_l`. -/
theorem nadd_lt_nadd_right {s s' : OTree.{u}} (h : s < s') (t : OTree.{u}) :
    nadd s t < nadd s' t :=
  let ⟨i, hi⟩ := h
  OTree.lt_of_le_of_lt (nadd_le_nadd_right hi t) (nadd_child_left_lt s' t i)

/-- snu-sf: `Hessenberg.lt_add_r`. -/
theorem nadd_lt_nadd_left {t t' : OTree.{u}} (h : t < t') (s : OTree.{u}) :
    nadd s t < nadd s t' :=
  let ⟨j, hj⟩ := h
  OTree.lt_of_le_of_lt (nadd_le_nadd_left hj s) (nadd_child_right_lt s t' j)

theorem nadd_lt_nadd_of_lt_of_le {s s' t t' : OTree.{u}} (hs : s < s') (ht : t ≤ t') :
    nadd s t < nadd s' t' :=
  OTree.lt_of_lt_of_le (nadd_lt_nadd_right hs t) (nadd_le_nadd_left ht s')

theorem nadd_lt_nadd_of_le_of_lt {s s' t t' : OTree.{u}} (hs : s ≤ s') (ht : t < t') :
    nadd s t < nadd s' t' :=
  OTree.lt_of_le_of_lt (nadd_le_nadd_right hs t) (nadd_lt_nadd_left ht s')

theorem nadd_lt_nadd {s s' t t' : OTree.{u}} (hs : s < s') (ht : t < t') :
    nadd s t < nadd s' t' :=
  nadd_lt_nadd_of_lt_of_le hs (OTree.le_of_lt ht)

/-! ## Characterization by the trees below -/

/-- snu-sf: `Hessenberg.add_spec`, `Hessenberg.add_supremum`. -/
theorem nadd_le_of_forall_lt {s t r : OTree.{u}} (hs : ∀ s', s' < s → nadd s' t < r)
    (ht : ∀ t', t' < t → nadd s t' < r) : nadd s t ≤ r :=
  nadd_le_iff_child.mpr ⟨fun i => hs _ (child_lt s i), fun j => ht _ (child_lt t j)⟩

theorem nadd_le_iff {s t r : OTree.{u}} :
    nadd s t ≤ r ↔ (∀ s', s' < s → nadd s' t < r) ∧ (∀ t', t' < t → nadd s t' < r) :=
  ⟨fun h => ⟨fun _ hs' => OTree.lt_of_lt_of_le (nadd_lt_nadd_right hs' t) h,
     fun _ ht' => OTree.lt_of_lt_of_le (nadd_lt_nadd_left ht' s) h⟩,
   fun h => nadd_le_of_forall_lt h.1 h.2⟩

theorem lt_nadd_iff {r s t : OTree.{u}} :
    r < nadd s t ↔ (∃ s', s' < s ∧ r ≤ nadd s' t) ∨ (∃ t', t' < t ∧ r ≤ nadd s t') :=
  ⟨fun h => match lt_nadd_iff_child.mp h with
    | .inl ⟨i, hi⟩ => .inl ⟨_, child_lt s i, hi⟩
    | .inr ⟨j, hj⟩ => .inr ⟨_, child_lt t j, hj⟩,
   fun h => match h with
    | .inl ⟨_, hs', hr⟩ => OTree.lt_of_le_of_lt hr (nadd_lt_nadd_right hs' t)
    | .inr ⟨_, ht', hr⟩ => OTree.lt_of_le_of_lt hr (nadd_lt_nadd_left ht' s)⟩

/-! ## Algebraic properties -/

theorem nadd_comm_le (s t : OTree.{u}) : nadd s t ≤ nadd t s := by
  induction s, t using induction₂ with
  | _ s t ihs iht =>
    exact nadd_le_iff_child.mpr
      ⟨fun i => OTree.lt_of_le_of_lt (ihs _ (child_lt s i)) (nadd_child_right_lt t s i),
       fun j => OTree.lt_of_le_of_lt (iht _ (child_lt t j)) (nadd_child_left_lt t s j)⟩

/-- snu-sf: `Hessenberg.add_comm`. -/
theorem nadd_comm (s t : OTree.{u}) : nadd s t ≈ nadd t s :=
  ⟨nadd_comm_le s t, nadd_comm_le t s⟩

/-- snu-sf: `Hessenberg.add_assoc`. -/
theorem nadd_assoc (r s t : OTree.{u}) : nadd (nadd r s) t ≈ nadd r (nadd s t) := by
  induction r using lt_wf.induction generalizing s t with
  | _ r ihr =>
    induction s using lt_wf.induction generalizing t with
    | _ s ihs =>
      induction t using lt_wf.induction with
      | _ t iht =>
        constructor
        · refine nadd_le_of_forall_lt (fun x hx => ?_) (fun t' ht' => ?_)
          · rcases lt_nadd_iff.mp hx with ⟨r', hr', hx'⟩ | ⟨s', hs', hx'⟩
            · exact OTree.lt_of_le_of_lt
                (OTree.le_trans (nadd_le_nadd_right hx' t) (ihr r' hr' s t).le)
                (nadd_lt_nadd_right hr' _)
            · exact OTree.lt_of_le_of_lt
                (OTree.le_trans (nadd_le_nadd_right hx' t) (ihs s' hs' t).le)
                (nadd_lt_nadd_left (nadd_lt_nadd_right hs' t) r)
          · exact OTree.lt_of_le_of_lt (iht t' ht').le
              (nadd_lt_nadd_left (nadd_lt_nadd_left ht' s) r)
        · refine nadd_le_of_forall_lt (fun r' hr' => ?_) (fun y hy => ?_)
          · exact OTree.lt_of_le_of_lt (ihr r' hr' s t).ge
              (nadd_lt_nadd_right (nadd_lt_nadd_right hr' s) t)
          · rcases lt_nadd_iff.mp hy with ⟨s', hs', hy'⟩ | ⟨t', ht', hy'⟩
            · exact OTree.lt_of_le_of_lt
                (OTree.le_trans (nadd_le_nadd_left hy' r) (ihs s' hs' t).ge)
                (nadd_lt_nadd_right (nadd_lt_nadd_left hs' r) t)
            · exact OTree.lt_of_le_of_lt
                (OTree.le_trans (nadd_le_nadd_left hy' r) (iht t' ht').ge)
                (nadd_lt_nadd_left ht' _)

theorem nadd_left_comm (r s t : OTree.{u}) : nadd r (nadd s t) ≈ nadd s (nadd r t) :=
  (nadd_assoc r s t).symm.trans ((nadd_congr_right (nadd_comm r s) t).trans (nadd_assoc s r t))

theorem nadd_right_comm (r s t : OTree.{u}) : nadd (nadd r s) t ≈ nadd (nadd r t) s :=
  (nadd_assoc r s t).trans ((nadd_congr_left (nadd_comm s t) r).trans (nadd_assoc r t s).symm)

/-- snu-sf: `Hessenberg.add_base_l`. -/
theorem le_self_nadd (s t : OTree.{u}) : s ≤ nadd s t := by
  induction s with
  | mk ι f ih =>
    exact mk_le.mpr fun i => OTree.lt_of_le_of_lt (ih i) (nadd_child_left_lt (mk ι f) t i)

/-- snu-sf: `Hessenberg.add_base_r`. -/
theorem le_nadd_self (s t : OTree.{u}) : t ≤ nadd s t :=
  OTree.le_trans (le_self_nadd t s) (nadd_comm t s).le

/-- snu-sf: `Hessenberg.add_lt_l`. -/
theorem lt_nadd_of_pos_right (s : OTree.{u}) {t : OTree.{u}} (h : zero < t) : s < nadd s t :=
  let ⟨j, _⟩ := h
  OTree.lt_of_le_of_lt (le_self_nadd s (t.child j)) (nadd_child_right_lt s t j)

/-- snu-sf: `Hessenberg.add_lt_r`. -/
theorem lt_nadd_of_pos_left {s : OTree.{u}} (t : OTree.{u}) (h : zero < s) : t < nadd s t :=
  let ⟨i, _⟩ := h
  OTree.lt_of_le_of_lt (le_nadd_self (s.child i) t) (nadd_child_left_lt s t i)

/-! ## Zero, successor, natural numbers -/

/-- snu-sf: `Hessenberg.add_O_r`. -/
theorem nadd_zero (s : OTree.{u}) : nadd s zero ≈ s := by
  induction s using lt_wf.induction with
  | _ s ih =>
    exact ⟨nadd_le_of_forall_lt (fun s' hs' => OTree.lt_of_le_of_lt (ih s' hs').le hs')
        (fun t' ht' => (not_lt_zero t' ht').elim),
      le_self_nadd s zero⟩

/-- snu-sf: `Hessenberg.add_O_l`. -/
theorem zero_nadd (s : OTree.{u}) : nadd zero s ≈ s :=
  (nadd_comm zero s).trans (nadd_zero s)

/-- snu-sf: `Hessenberg.add_S_r`. -/
theorem nadd_succ (s t : OTree.{u}) : nadd s (succ t) ≈ succ (nadd s t) := by
  induction s using lt_wf.induction generalizing t with
  | _ s ih =>
    refine ⟨nadd_le_of_forall_lt (fun s' hs' => ?_) (fun t' ht' => ?_),
      succ_le_of_lt (nadd_lt_nadd_left (lt_succ t) s)⟩
    · exact OTree.lt_of_le_of_lt (ih s' hs' t).le (succ_lt_succ_iff.mpr (nadd_lt_nadd_right hs' t))
    · exact lt_succ_iff.mpr (nadd_le_nadd_left (lt_succ_iff.mp ht') s)

/-- snu-sf: `Hessenberg.add_S_l`. -/
theorem succ_nadd (s t : OTree.{u}) : nadd (succ s) t ≈ succ (nadd s t) :=
  (nadd_comm (succ s) t).trans ((nadd_succ t s).trans (succ_congr (nadd_comm t s)))

/-- snu-sf: `Hessenberg.add_from_nat`. -/
theorem nadd_ofNat (m n : Nat) : nadd (ofNat.{u} m) (ofNat n) ≈ ofNat (m + n) := by
  induction n with
  | zero => exact nadd_zero _
  | succ n ih => exact (nadd_succ _ _).trans (succ_congr ih)

/-! ## Lift to a larger universe -/

theorem lt_lift_iff_exists_lt {s : OTree.{max u v}} {t : OTree.{u}} :
    s < lift.{u, v} t ↔ ∃ t', t' < t ∧ s ≤ lift.{u, v} t' := by
  cases t with
  | mk ι f =>
    exact ⟨fun ⟨j, hj⟩ => ⟨f j.down, child_lt (mk ι f) j.down, hj⟩,
      fun ⟨_, ht', hs⟩ => OTree.lt_of_le_of_lt hs (lift_lt_lift_iff.mpr ht')⟩

theorem lift_nadd (s t : OTree.{u}) :
    lift.{u, v} (nadd s t) ≈ nadd (lift.{u, v} s) (lift.{u, v} t) := by
  induction s, t using induction₂ with
  | _ s t ihs iht =>
    constructor
    · refine le_of_forall_lt fun x hx => ?_
      obtain ⟨y, hy, hxy⟩ := lt_lift_iff_exists_lt.mp hx
      rcases lt_nadd_iff.mp hy with ⟨s', hs', hy'⟩ | ⟨t', ht', hy'⟩
      · exact OTree.lt_of_le_of_lt
          (OTree.le_trans hxy (OTree.le_trans (lift_le_lift_iff.mpr hy') (ihs s' hs').le))
          (nadd_lt_nadd_right (lift_lt_lift_iff.mpr hs') _)
      · exact OTree.lt_of_le_of_lt
          (OTree.le_trans hxy (OTree.le_trans (lift_le_lift_iff.mpr hy') (iht t' ht').le))
          (nadd_lt_nadd_left (lift_lt_lift_iff.mpr ht') _)
    · refine nadd_le_of_forall_lt (fun x hx => ?_) (fun y hy => ?_)
      · obtain ⟨s', hs', hx'⟩ := lt_lift_iff_exists_lt.mp hx
        exact OTree.lt_of_le_of_lt (OTree.le_trans (nadd_le_nadd_right hx' _) (ihs s' hs').ge)
          (lift_lt_lift_iff.mpr (nadd_lt_nadd_right hs' t))
      · obtain ⟨t', ht', hy'⟩ := lt_lift_iff_exists_lt.mp hy
        exact OTree.lt_of_le_of_lt (OTree.le_trans (nadd_le_nadd_left hy' _) (iht t' ht').ge)
          (lift_lt_lift_iff.mpr (nadd_lt_nadd_left ht' s))

end OTree

end Ordinals
