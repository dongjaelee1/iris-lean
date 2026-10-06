/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

/-!
# Well-founded trees

An `OTree.{u}` is a tree whose nodes have children indexed by a type in `Type u`. Each tree
represents an ordinal: its height. The order `s ≤ t` compares heights: each child of `s` is
below `t`. Two trees are equivalent (`s ≈ t`) if `s ≤ t` and `t ≤ s`. The type
`Ordinals.Ordinal` is the quotient of `OTree` by this equivalence.

This file follows snu-sf/Ordinal (`src/Ordinal.v`, module `Ord`). The names of the Rocq lemmas
are in the docstrings. The results of this file use no axioms.

## Main definitions

- `OTree.mk ι f`: the tree with children `f i` for `i : ι` (snu-sf: `Ord.build`).
- `OTree.le`, `OTree.lt`: the order on heights.
- `OTree.setoid`: the equivalence `s ≈ t ↔ s ≤ t ∧ t ≤ s`.
- `OTree.lt_wf`: `<` is well-founded.
-/

@[expose] public section

namespace Ordinals

universe u v w

/-- A well-founded tree. The children of a node are indexed by a type in `Type u`
(snu-sf: `Ord.t`). -/
inductive OTree : Type (u + 1) where
  /-- The tree with the children `f i` for `i : ι` (snu-sf: `Ord.build`). -/
  | mk (ι : Type u) (f : ι → OTree)

namespace OTree

/-- The index type of the children of a tree (snu-sf: `Ord.proj1`). -/
def Index : OTree.{u} → Type u
  | mk ι _ => ι

/-- The children of a tree (snu-sf: `Ord.proj2`). -/
def child : (t : OTree.{u}) → t.Index → OTree.{u}
  | mk _ f => f

@[simp] theorem index_mk (ι : Type u) (f : ι → OTree.{u}) : (mk ι f).Index = ι := rfl

@[simp] theorem child_mk (ι : Type u) (f : ι → OTree.{u}) (i : ι) : (mk ι f).child i = f i :=
  rfl

theorem eta (t : OTree.{u}) : mk t.Index t.child = t := by
  cases t; rfl

/-! ## The order -/

/-- `le s t`: the height of `s` is at most the height of `t`. Each child of `s` is at most some
child of `t` (snu-sf: `Ord.le`). The definition is by structural recursion on `s`. -/
protected def le : OTree.{u} → OTree.{u} → Prop
  | mk _ f, mk _ g => ∀ i, ∃ j, OTree.le (f i) (g j)

/-- `lt s t`: the height of `s` is below the height of `t`. Some child of `t` has a height of at
least the height of `s` (snu-sf: `Ord.lt`). -/
protected def lt (s t : OTree.{u}) : Prop :=
  ∃ j, OTree.le s (t.child j)

instance : LE OTree.{u} := ⟨OTree.le⟩

instance : LT OTree.{u} := ⟨OTree.lt⟩

/-- snu-sf: `Ord.le_equivalent`. -/
theorem mk_le_mk {ι κ : Type u} {f : ι → OTree.{u}} {g : κ → OTree.{u}} :
    mk ι f ≤ mk κ g ↔ ∀ i, ∃ j, f i ≤ g j :=
  Iff.rfl

/-- snu-sf: `Ord.lt_equivalent`. -/
theorem lt_mk {s : OTree.{u}} {κ : Type u} {g : κ → OTree.{u}} :
    s < mk κ g ↔ ∃ j, s ≤ g j :=
  Iff.rfl

theorem lt_iff {s t : OTree.{u}} : s < t ↔ ∃ j, s ≤ t.child j :=
  Iff.rfl

/-- snu-sf: `Ord.le_proj`. -/
theorem le_iff {s t : OTree.{u}} : s ≤ t ↔ ∀ i, ∃ j, s.child i ≤ t.child j := by
  cases s; cases t; rfl

/-- snu-sf: `Ord.le_refl`. -/
@[refl] protected theorem le_refl : ∀ t : OTree.{u}, t ≤ t
  | mk _ f => fun i => ⟨i, OTree.le_refl (f i)⟩

protected theorem le_rfl {t : OTree.{u}} : t ≤ t :=
  OTree.le_refl t

/-- snu-sf: `Ord.le_trans`. -/
protected theorem le_trans : ∀ {r s t : OTree.{u}}, r ≤ s → s ≤ t → r ≤ t
  | mk _ _, mk _ _, mk _ _, h₁, h₂ => fun i =>
    let ⟨j, hj⟩ := h₁ i
    let ⟨k, hk⟩ := h₂ j
    ⟨k, OTree.le_trans hj hk⟩

/-- A child is below its tree (snu-sf: `Ord.build_upperbound`). -/
theorem child_lt (t : OTree.{u}) (i : t.Index) : t.child i < t :=
  ⟨i, OTree.le_rfl⟩

theorem lt_mk_of_le {s : OTree.{u}} {κ : Type u} {g : κ → OTree.{u}} (j : κ) (h : s ≤ g j) :
    s < mk κ g :=
  ⟨j, h⟩

/-- snu-sf: `Ord.le_lt_lt`. -/
protected theorem lt_of_le_of_lt {r s t : OTree.{u}} (h₁ : r ≤ s) (h₂ : s < t) : r < t :=
  let ⟨j, hj⟩ := h₂
  ⟨j, OTree.le_trans h₁ hj⟩

/-- A tree is at most another tree if and only if each of its children is below it
(snu-sf: `Ord.build_supremum`, `Ord.le_proj`). -/
theorem le_iff_forall_child_lt {s t : OTree.{u}} : s ≤ t ↔ ∀ i, s.child i < t := by
  cases s with
  | mk ι f =>
    cases t with
    | mk κ g => exact Iff.rfl

theorem mk_le {ι : Type u} {f : ι → OTree.{u}} {t : OTree.{u}} :
    mk ι f ≤ t ↔ ∀ i, f i < t :=
  le_iff_forall_child_lt

/-- snu-sf: `Ord.lt_le_lt`. -/
protected theorem lt_of_lt_of_le {r s t : OTree.{u}} (h₁ : r < s) (h₂ : s ≤ t) : r < t :=
  let ⟨k, hk⟩ := h₁
  let ⟨m, hm⟩ := le_iff.mp h₂ k
  ⟨m, OTree.le_trans hk hm⟩

/-- snu-sf: `Ord.lt_le`. -/
protected theorem le_of_lt : ∀ {s t : OTree.{u}}, s < t → s ≤ t
  | mk ι f, _, ⟨j, hj⟩ => mk_le.mpr fun i =>
    ⟨j, OTree.le_of_lt (s := f i) (OTree.lt_of_lt_of_le (child_lt (mk ι f) i) hj)⟩

/-- snu-sf: `Ord.lt_irreflexive`. -/
protected theorem lt_irrefl : ∀ t : OTree.{u}, ¬t < t
  | mk ι f, ⟨j, hj⟩ => OTree.lt_irrefl (f j) (OTree.lt_of_lt_of_le (child_lt (mk ι f) j) hj)

/-- snu-sf: `Ord.lt_trans`. -/
protected theorem lt_trans {r s t : OTree.{u}} (h₁ : r < s) (h₂ : s < t) : r < t :=
  OTree.lt_of_le_of_lt (OTree.le_of_lt h₁) h₂

/-- snu-sf: `Ord.lt_not_le`. -/
protected theorem not_lt_of_le {s t : OTree.{u}} (h : s ≤ t) : ¬t < s :=
  fun h' => OTree.lt_irrefl t (OTree.lt_of_lt_of_le h' h)

/-- snu-sf: `Ord.lt_not_le`. -/
protected theorem not_le_of_lt {s t : OTree.{u}} (h : s < t) : ¬t ≤ s :=
  fun h' => OTree.lt_irrefl s (OTree.lt_of_lt_of_le h h')

/-- `<` is well-founded (snu-sf: `Ord.lt_well_founded`). -/
theorem lt_wf : WellFounded (α := OTree.{u}) (· < ·) := by
  have key : ∀ t s : OTree.{u}, s ≤ t → Acc (· < ·) s := by
    intro t
    induction t with
    | mk κ g ih =>
      intro s hs
      refine ⟨_, fun r hr => ?_⟩
      obtain ⟨j, hj⟩ := hr
      obtain ⟨k, hk⟩ := le_iff.mp hs j
      exact ih k r (OTree.le_trans hj hk)
  exact ⟨fun t => key t t OTree.le_rfl⟩

instance : WellFoundedRelation OTree.{u} := ⟨(· < ·), lt_wf⟩

/-- Extensionality for `≤` (snu-sf: `Ord.le_ext`). -/
theorem le_of_forall_lt {s t : OTree.{u}} (h : ∀ r, r < s → r < t) : s ≤ t :=
  le_iff_forall_child_lt.mpr fun i => h _ (child_lt s i)

theorem le_iff_forall_lt {s t : OTree.{u}} : s ≤ t ↔ ∀ r, r < s → r < t :=
  ⟨fun h _ h' => OTree.lt_of_lt_of_le h' h, le_of_forall_lt⟩

/-! ## Equivalence -/

/-- Two trees are equivalent if they have the same height (snu-sf: `Ord.eq`). -/
protected def Equiv (s t : OTree.{u}) : Prop :=
  s ≤ t ∧ t ≤ s

instance setoid : Setoid OTree.{u} where
  r := OTree.Equiv
  iseqv :=
    ⟨fun _ => ⟨OTree.le_rfl, OTree.le_rfl⟩, fun h => ⟨h.2, h.1⟩,
      fun h₁ h₂ => ⟨OTree.le_trans h₁.1 h₂.1, OTree.le_trans h₂.2 h₁.2⟩⟩

theorem equiv_iff {s t : OTree.{u}} : s ≈ t ↔ s ≤ t ∧ t ≤ s :=
  Iff.rfl

theorem equiv_of_le_of_le {s t : OTree.{u}} (h₁ : s ≤ t) (h₂ : t ≤ s) : s ≈ t :=
  ⟨h₁, h₂⟩

@[refl] protected theorem Equiv.refl (t : OTree.{u}) : t ≈ t :=
  Setoid.refl t

protected theorem Equiv.symm {s t : OTree.{u}} (h : s ≈ t) : t ≈ s :=
  Setoid.symm h

protected theorem Equiv.trans {r s t : OTree.{u}} (h₁ : r ≈ s) (h₂ : s ≈ t) : r ≈ t :=
  Setoid.trans h₁ h₂

theorem Equiv.le {s t : OTree.{u}} (h : s ≈ t) : s ≤ t :=
  h.1

theorem Equiv.ge {s t : OTree.{u}} (h : s ≈ t) : t ≤ s :=
  h.2

/-- Extensionality for `≈` (snu-sf: `Ord.eq_ext`). -/
theorem equiv_of_forall_lt_iff {s t : OTree.{u}} (h : ∀ r, r < s ↔ r < t) : s ≈ t :=
  ⟨le_of_forall_lt fun r => (h r).mp, le_of_forall_lt fun r => (h r).mpr⟩

/-- `≤` respects `≈` (snu-sf: `Ord.le_eq_le`, `Ord.eq_le_le`). -/
theorem le_congr {s s' t t' : OTree.{u}} (hs : s ≈ s') (ht : t ≈ t') : s ≤ t ↔ s' ≤ t' :=
  ⟨fun h => OTree.le_trans hs.ge (OTree.le_trans h ht.le),
   fun h => OTree.le_trans hs.le (OTree.le_trans h ht.ge)⟩

/-- `<` respects `≈` (snu-sf: `Ord.lt_eq_lt`, `Ord.eq_lt_lt`). -/
theorem lt_congr {s s' t t' : OTree.{u}} (hs : s ≈ s') (ht : t ≈ t') : s < t ↔ s' < t' :=
  ⟨fun h => OTree.lt_of_le_of_lt hs.ge (OTree.lt_of_lt_of_le h ht.le),
   fun h => OTree.lt_of_le_of_lt hs.le (OTree.lt_of_lt_of_le h ht.ge)⟩

end OTree

end Ordinals
