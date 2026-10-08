/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Tree.Basic

/-!
# Basic constructions on trees

Zero, successor, joins, binary maximum, natural numbers, `ω`, and the lift to a larger
universe. This file follows snu-sf/Ordinal (`src/Ordinal.v`, section `OPERATOR`).
-/

@[expose] public section

namespace Ordinals

universe u v w

namespace OTree

/-! ## Zero -/

/-- The tree without children: the ordinal `0` (snu-sf: `Ord.O`). -/
def zero : OTree.{u} :=
  mk PEmpty fun e => e.elim

/-- snu-sf: `Ord.O_bot`. -/
theorem zero_le (t : OTree.{u}) : zero ≤ t :=
  mk_le.mpr fun e => e.elim

theorem not_lt_zero (t : OTree.{u}) : ¬t < zero :=
  fun ⟨e, _⟩ => e.elim

theorem le_zero_iff {t : OTree.{u}} : t ≤ zero ↔ t ≈ zero :=
  ⟨fun h => ⟨h, zero_le t⟩, fun h => h.le⟩

theorem equiv_zero_iff {t : OTree.{u}} : t ≈ zero ↔ ¬Nonempty t.Index := by
  constructor
  · intro h
    exact fun ⟨i⟩ => not_lt_zero _ (OTree.lt_of_lt_of_le (child_lt t i) h.le)
  · intro h
    exact ⟨le_iff_forall_child_lt.mpr fun i => (h ⟨i⟩).elim, zero_le t⟩

/-! ## Successor -/

/-- The successor: the tree with one child `t` (snu-sf: `Ord.S`). -/
def succ (t : OTree.{u}) : OTree.{u} :=
  mk PUnit fun _ => t

/-- snu-sf: `Ord.S_lt`. -/
theorem lt_succ (t : OTree.{u}) : t < succ t :=
  ⟨⟨⟩, OTree.le_rfl⟩

/-- snu-sf: `Ord.S_supremum`. -/
theorem succ_le_of_lt {s t : OTree.{u}} (h : s < t) : succ s ≤ t :=
  mk_le.mpr fun _ => h

theorem succ_le_iff {s t : OTree.{u}} : succ s ≤ t ↔ s < t :=
  ⟨fun h => OTree.lt_of_lt_of_le (lt_succ s) h, succ_le_of_lt⟩

theorem lt_succ_iff {s t : OTree.{u}} : s < succ t ↔ s ≤ t :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨⟨⟩, h⟩⟩

theorem le_succ (t : OTree.{u}) : t ≤ succ t :=
  OTree.le_of_lt (lt_succ t)

/-- snu-sf: `Ord.le_S`, `Ord.le_S_rev`. -/
theorem succ_le_succ_iff {s t : OTree.{u}} : succ s ≤ succ t ↔ s ≤ t :=
  succ_le_iff.trans lt_succ_iff

/-- snu-sf: `Ord.lt_S`, `Ord.lt_S_rev`. -/
theorem succ_lt_succ_iff {s t : OTree.{u}} : succ s < succ t ↔ s < t :=
  lt_succ_iff.trans succ_le_iff

theorem succ_le_succ {s t : OTree.{u}} (h : s ≤ t) : succ s ≤ succ t :=
  succ_le_succ_iff.mpr h

/-- snu-sf: `Ord.eq_S`. -/
theorem succ_congr {s t : OTree.{u}} (h : s ≈ t) : succ s ≈ succ t :=
  ⟨succ_le_succ h.le, succ_le_succ h.ge⟩

/-- snu-sf: `Ord.eq_S_rev`. -/
theorem equiv_of_succ_equiv_succ {s t : OTree.{u}} (h : succ s ≈ succ t) : s ≈ t :=
  ⟨succ_le_succ_iff.mp h.le, succ_le_succ_iff.mp h.ge⟩

/-- snu-sf: `Ord.S_pos`. -/
theorem zero_lt_succ (t : OTree.{u}) : zero < succ t :=
  lt_succ_iff.mpr (zero_le t)

/-! ## Joins -/

/-- The join (least upper bound) of a family of trees: its children are the children of all
members (snu-sf: `Ord.join`). -/
def sup {ι : Type u} (f : ι → OTree.{u}) : OTree.{u} :=
  mk (Σ i, (f i).Index) fun p => (f p.1).child p.2

/-- snu-sf: `Ord.join_upperbound`. -/
theorem le_sup {ι : Type u} (f : ι → OTree.{u}) (i : ι) : f i ≤ sup f :=
  le_iff_forall_child_lt.mpr fun k => ⟨⟨i, k⟩, OTree.le_rfl⟩

/-- snu-sf: `Ord.join_supremum`. -/
theorem sup_le {ι : Type u} {f : ι → OTree.{u}} {t : OTree.{u}} (h : ∀ i, f i ≤ t) :
    sup f ≤ t :=
  mk_le.mpr fun p => le_iff_forall_child_lt.mp (h p.1) p.2

theorem sup_le_iff {ι : Type u} {f : ι → OTree.{u}} {t : OTree.{u}} :
    sup f ≤ t ↔ ∀ i, f i ≤ t :=
  ⟨fun h i => OTree.le_trans (le_sup f i) h, sup_le⟩

theorem lt_sup_iff {ι : Type u} {f : ι → OTree.{u}} {t : OTree.{u}} :
    t < sup f ↔ ∃ i, t < f i :=
  ⟨fun ⟨⟨i, k⟩, h⟩ => ⟨i, ⟨k, h⟩⟩,
   fun ⟨i, h⟩ => OTree.lt_of_lt_of_le h (le_sup f i)⟩

/-- snu-sf: `Ord.le_join`. -/
theorem sup_mono {ι : Type u} {f g : ι → OTree.{u}} (h : ∀ i, f i ≤ g i) : sup f ≤ sup g :=
  sup_le fun i => OTree.le_trans (h i) (le_sup g i)

/-- snu-sf: `Ord.eq_join`. -/
theorem sup_congr {ι : Type u} {f g : ι → OTree.{u}} (h : ∀ i, f i ≈ g i) : sup f ≈ sup g :=
  ⟨sup_mono fun i => (h i).le, sup_mono fun i => (h i).ge⟩

/-- snu-sf: `Ord.build_join_S`. -/
theorem mk_equiv_sup_succ {ι : Type u} (f : ι → OTree.{u}) : mk ι f ≈ sup fun i => succ (f i) :=
  ⟨mk_le.mpr fun i => OTree.lt_of_lt_of_le (lt_succ (f i)) (le_sup (fun i => succ (f i)) i),
   sup_le fun i => succ_le_of_lt (child_lt (mk ι f) i)⟩

/-- snu-sf: `Ord.build_supremum`. -/
theorem mk_mono {ι : Type u} {f g : ι → OTree.{u}} (h : ∀ i, f i ≤ g i) : mk ι f ≤ mk ι g :=
  fun i => ⟨i, h i⟩

theorem mk_congr {ι : Type u} {f g : ι → OTree.{u}} (h : ∀ i, f i ≈ g i) : mk ι f ≈ mk ι g :=
  ⟨mk_mono fun i => (h i).le, mk_mono fun i => (h i).ge⟩

/-- A join is at most the strict join of the same family (snu-sf: `Ord.build_join`). -/
theorem sup_le_mk {ι : Type u} (f : ι → OTree.{u}) : sup f ≤ mk ι f :=
  sup_le fun i => OTree.le_of_lt (child_lt (mk ι f) i)

theorem sup_le_sup_of_forall_exists {ι κ : Type u} {f : ι → OTree.{u}} {g : κ → OTree.{u}}
    (h : ∀ i, ∃ j, f i ≤ g j) : sup f ≤ sup g :=
  sup_le fun i => let ⟨j, hj⟩ := h i; OTree.le_trans hj (le_sup g j)

theorem mk_le_mk_of_forall_exists {ι κ : Type u} {f : ι → OTree.{u}} {g : κ → OTree.{u}}
    (h : ∀ i, ∃ j, f i ≤ g j) : mk ι f ≤ mk κ g :=
  h

/-! ## Binary maximum -/

/-- The maximum of two trees: the children of both (snu-sf: `Ord.union`). -/
def max (s t : OTree.{u}) : OTree.{u} :=
  mk (s.Index ⊕ t.Index) (Sum.elim s.child t.child)

/-- snu-sf: `Ord.union_l`. -/
theorem le_max_left (s t : OTree.{u}) : s ≤ max s t :=
  le_iff_forall_child_lt.mpr fun i => ⟨.inl i, OTree.le_rfl⟩

/-- snu-sf: `Ord.union_r`. -/
theorem le_max_right (s t : OTree.{u}) : t ≤ max s t :=
  le_iff_forall_child_lt.mpr fun i => ⟨.inr i, OTree.le_rfl⟩

/-- snu-sf: `Ord.union_spec`. -/
theorem max_le {r s t : OTree.{u}} (hs : s ≤ r) (ht : t ≤ r) : max s t ≤ r :=
  mk_le.mpr fun
    | .inl i => le_iff_forall_child_lt.mp hs i
    | .inr i => le_iff_forall_child_lt.mp ht i

theorem max_le_iff {r s t : OTree.{u}} : max s t ≤ r ↔ s ≤ r ∧ t ≤ r :=
  ⟨fun h => ⟨OTree.le_trans (le_max_left s t) h, OTree.le_trans (le_max_right s t) h⟩,
   fun h => max_le h.1 h.2⟩

theorem lt_max_iff {r s t : OTree.{u}} : r < max s t ↔ r < s ∨ r < t :=
  ⟨fun
    | ⟨.inl i, h⟩ => .inl ⟨i, h⟩
    | ⟨.inr i, h⟩ => .inr ⟨i, h⟩,
   fun
    | .inl h => OTree.lt_of_lt_of_le h (le_max_left s t)
    | .inr h => OTree.lt_of_lt_of_le h (le_max_right s t)⟩

/-- snu-sf: `Ord.le_union`. -/
theorem max_mono {s s' t t' : OTree.{u}} (hs : s ≤ s') (ht : t ≤ t') : max s t ≤ max s' t' :=
  max_le (OTree.le_trans hs (le_max_left s' t')) (OTree.le_trans ht (le_max_right s' t'))

/-- snu-sf: `Ord.eq_union`. -/
theorem max_congr {s s' t t' : OTree.{u}} (hs : s ≈ s') (ht : t ≈ t') : max s t ≈ max s' t' :=
  ⟨max_mono hs.le ht.le, max_mono hs.ge ht.ge⟩

/-- snu-sf: `Ord.union_comm`. -/
theorem max_comm (s t : OTree.{u}) : max s t ≈ max t s :=
  ⟨max_le (le_max_right t s) (le_max_left t s), max_le (le_max_right s t) (le_max_left s t)⟩

/-- snu-sf: `Ord.union_assoc`. -/
theorem max_assoc (r s t : OTree.{u}) : max (max r s) t ≈ max r (max s t) :=
  ⟨max_le (max_le (le_max_left _ _) (OTree.le_trans (le_max_left s t) (le_max_right _ _)))
      (OTree.le_trans (le_max_right s t) (le_max_right _ _)),
   max_le (OTree.le_trans (le_max_left r s) (le_max_left _ _))
      (max_le (OTree.le_trans (le_max_right r s) (le_max_left _ _)) (le_max_right _ _))⟩

/-- snu-sf: `Ord.union_max`. -/
theorem max_equiv_of_le {s t : OTree.{u}} (h : s ≤ t) : max s t ≈ t :=
  ⟨max_le h OTree.le_rfl, le_max_right s t⟩

/-! ## Natural numbers and `ω` -/

/-- The natural number `n` as a tree (snu-sf: `Ord.from_nat`). -/
def ofNat : Nat → OTree.{u}
  | 0 => zero
  | n + 1 => succ (ofNat n)

@[simp] theorem ofNat_zero : ofNat.{u} 0 = zero := rfl

@[simp] theorem ofNat_succ (n : Nat) : ofNat.{u} (n + 1) = succ (ofNat n) := rfl

theorem ofNat_lt_ofNat_iff {m n : Nat} : ofNat.{u} m < ofNat n ↔ m < n := by
  induction n generalizing m with
  | zero => exact ⟨fun h => (not_lt_zero _ h).elim, fun h => (Nat.not_lt_zero _ h).elim⟩
  | succ n ih =>
    refine lt_succ_iff.trans ?_
    cases m with
    | zero => exact ⟨fun _ => Nat.succ_pos n, fun _ => zero_le _⟩
    | succ m => exact succ_le_iff.trans (ih.trans Nat.succ_lt_succ_iff.symm)

theorem ofNat_le_ofNat_iff {m n : Nat} : ofNat.{u} m ≤ ofNat n ↔ m ≤ n :=
  lt_succ_iff.symm.trans (ofNat_lt_ofNat_iff (n := n + 1) |>.trans Nat.lt_succ_iff)

/-- The first infinite ordinal: the join of the natural numbers (snu-sf: `Ord.omega`). -/
def omega : OTree.{u} :=
  sup fun n : ULift.{u} Nat => ofNat n.down

/-- snu-sf: `Ord.omega_upperbound`. -/
theorem ofNat_lt_omega (n : Nat) : ofNat.{u} n < omega :=
  OTree.lt_of_lt_of_le (lt_succ (ofNat n)) (le_sup (fun n : ULift.{u} Nat => ofNat n.down) ⟨n + 1⟩)

/-- snu-sf: `Ord.omega_supremum`. -/
theorem omega_le {t : OTree.{u}} (h : ∀ n, ofNat n ≤ t) : omega ≤ t :=
  sup_le fun n => h n.down

/-! ## Lift to a larger universe -/

/-- The same tree with the index types lifted to `Type (max u v)`. -/
def lift : OTree.{u} → OTree.{max u v}
  | mk ι f => mk (ULift.{v} ι) fun i => lift (f i.down)

@[simp] theorem lift_mk (ι : Type u) (f : ι → OTree.{u}) :
    lift.{u, v} (mk ι f) = mk (ULift.{v} ι) fun i => lift (f i.down) :=
  rfl

theorem lift_le_lift_iff : ∀ {s t : OTree.{u}}, lift.{u, v} s ≤ lift.{u, v} t ↔ s ≤ t
  | mk _ _, mk _ _ =>
    ⟨fun h i => let ⟨j, hj⟩ := h ⟨i⟩; ⟨j.down, lift_le_lift_iff.mp hj⟩,
     fun h i => let ⟨j, hj⟩ := h i.down; ⟨⟨j⟩, lift_le_lift_iff.mpr hj⟩⟩

theorem lift_lt_lift_iff {s t : OTree.{u}} : lift.{u, v} s < lift.{u, v} t ↔ s < t := by
  cases t with
  | mk κ g =>
    exact ⟨fun ⟨j, hj⟩ => ⟨j.down, lift_le_lift_iff.mp hj⟩,
      fun ⟨j, hj⟩ => ⟨⟨j⟩, lift_le_lift_iff.mpr hj⟩⟩

theorem lift_congr {s t : OTree.{u}} (h : s ≈ t) : lift.{u, v} s ≈ lift.{u, v} t :=
  ⟨lift_le_lift_iff.mpr h.le, lift_le_lift_iff.mpr h.ge⟩

theorem lift_equiv_lift_iff {s t : OTree.{u}} : lift.{u, v} s ≈ lift.{u, v} t ↔ s ≈ t :=
  ⟨fun h => ⟨lift_le_lift_iff.mp h.le, lift_le_lift_iff.mp h.ge⟩, lift_congr⟩

theorem lift_zero : lift.{u, v} zero ≈ zero :=
  ⟨mk_le.mpr fun e => e.down.elim, zero_le _⟩

theorem lift_succ (t : OTree.{u}) : lift.{u, v} (succ t) ≈ succ (lift.{u, v} t) :=
  ⟨mk_le.mpr fun _ => lt_succ _, succ_le_of_lt ⟨⟨⟨⟩⟩, OTree.le_rfl⟩⟩

theorem lift_sup {ι : Type u} (f : ι → OTree.{u}) :
    lift.{u, v} (sup f) ≈ sup fun i : ULift.{v} ι => lift.{u, v} (f i.down) := by
  constructor
  · refine le_of_forall_lt fun r ⟨⟨⟨i, k⟩⟩, hr⟩ => ?_
    exact OTree.lt_of_lt_of_le
      (OTree.lt_of_le_of_lt hr (lift_lt_lift_iff.mpr (child_lt (f i) k)))
      (le_sup (fun i : ULift.{v} ι => lift.{u, v} (f i.down)) ⟨i⟩)
  · exact sup_le fun i => lift_le_lift_iff.mpr (le_sup f i.down)

end OTree

end Ordinals
