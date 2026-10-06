/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Tree.Classical

/-!
# Ordinals

`Ordinal.{u}` is the quotient of `OTree.{u}` by `≈` (same height). Equality of ordinals is
Leibniz equality: `⟦s⟧ = ⟦t⟧ ↔ s ≈ t`. The quotient needs only `propext` and `Quot.sound`. The
linear order (totality, trichotomy, decidability, `min`) needs excluded middle.

## Main definitions

- `Ordinal.{u} : Type (u+1)`, with `≤`, `<`, and the instances `Std.IsLinearOrder`,
  `Std.LawfulOrderLT` (so `grind` can use the order) and `WellFoundedRelation`.
- `Ordinal.mk t` (notation `⟦t⟧`): the ordinal of a tree; `Ordinal.out a`: a representative.
- Classical facts: `le_total`, `lt_trichotomy`, `not_le`, `not_lt`.
-/

@[expose] public section

namespace Ordinals

universe u v w

/-- Ordinals: well-founded trees up to equal height. -/
def Ordinal : Type (u + 1) :=
  Quotient OTree.setoid.{u}

namespace Ordinal

/-- The ordinal of a tree: its height. -/
def mk (t : OTree.{u}) : Ordinal.{u} :=
  Quotient.mk _ t

theorem mk_eq_mk {s t : OTree.{u}} : mk s = mk t ↔ s ≈ t :=
  ⟨Quotient.exact, Quotient.sound⟩

theorem sound {s t : OTree.{u}} (h : s ≈ t) : mk s = mk t :=
  Quotient.sound h

theorem exact {s t : OTree.{u}} (h : mk s = mk t) : s ≈ t :=
  Quotient.exact h

@[elab_as_elim]
protected theorem ind {motive : Ordinal.{u} → Prop} (h : ∀ t, motive (mk t)) (a : Ordinal.{u}) :
    motive a :=
  Quotient.ind h a

@[elab_as_elim]
protected theorem inductionOn {motive : Ordinal.{u} → Prop} (a : Ordinal.{u})
    (h : ∀ t, motive (mk t)) : motive a :=
  Quotient.ind h a

@[elab_as_elim]
protected theorem inductionOn₂ {motive : Ordinal.{u} → Ordinal.{u} → Prop} (a b : Ordinal.{u})
    (h : ∀ s t, motive (mk s) (mk t)) : motive a b :=
  Quotient.inductionOn₂ a b h

@[elab_as_elim]
protected theorem inductionOn₃ {motive : Ordinal.{u} → Ordinal.{u} → Ordinal.{u} → Prop}
    (a b c : Ordinal.{u}) (h : ∀ r s t, motive (mk r) (mk s) (mk t)) : motive a b c :=
  Quotient.inductionOn₃ a b c h

theorem exists_mk (a : Ordinal.{u}) : ∃ t, mk t = a :=
  Quotient.exists_rep a

/-- A representative of an ordinal (chosen with `Classical.choose`). -/
noncomputable def out (a : Ordinal.{u}) : OTree.{u} :=
  Classical.choose (exists_mk a)

@[simp] theorem mk_out (a : Ordinal.{u}) : mk a.out = a :=
  Classical.choose_spec (exists_mk a)

theorem out_mk_equiv (t : OTree.{u}) : (mk t).out ≈ t :=
  exact (mk_out (mk t))

/-! ## The order -/

instance : LE Ordinal.{u} :=
  ⟨Quotient.lift₂ (· ≤ ·) fun _ _ _ _ hs ht => propext (OTree.le_congr hs ht)⟩

instance : LT Ordinal.{u} :=
  ⟨Quotient.lift₂ (· < ·) fun _ _ _ _ hs ht => propext (OTree.lt_congr hs ht)⟩

@[simp] theorem mk_le_mk {s t : OTree.{u}} : mk s ≤ mk t ↔ s ≤ t :=
  Iff.rfl

@[simp] theorem mk_lt_mk {s t : OTree.{u}} : mk s < mk t ↔ s < t :=
  Iff.rfl

@[refl] protected theorem le_refl (a : Ordinal.{u}) : a ≤ a :=
  Ordinal.inductionOn a OTree.le_refl

protected theorem le_rfl {a : Ordinal.{u}} : a ≤ a :=
  Ordinal.le_refl a

protected theorem le_trans {a b c : Ordinal.{u}} : a ≤ b → b ≤ c → a ≤ c :=
  Ordinal.inductionOn₃ a b c fun _ _ _ => OTree.le_trans

protected theorem le_antisymm {a b : Ordinal.{u}} : a ≤ b → b ≤ a → a = b :=
  Ordinal.inductionOn₂ a b fun _ _ h₁ h₂ => sound ⟨h₁, h₂⟩

protected theorem le_of_eq {a b : Ordinal.{u}} (h : a = b) : a ≤ b :=
  h ▸ Ordinal.le_rfl

protected theorem lt_irrefl (a : Ordinal.{u}) : ¬a < a :=
  Ordinal.inductionOn a OTree.lt_irrefl

protected theorem ne_of_lt {a b : Ordinal.{u}} (h : a < b) : a ≠ b :=
  fun e => Ordinal.lt_irrefl a (e ▸ h)

protected theorem le_of_lt {a b : Ordinal.{u}} : a < b → a ≤ b :=
  Ordinal.inductionOn₂ a b fun _ _ => OTree.le_of_lt

protected theorem lt_of_le_of_lt {a b c : Ordinal.{u}} : a ≤ b → b < c → a < c :=
  Ordinal.inductionOn₃ a b c fun _ _ _ => OTree.lt_of_le_of_lt

protected theorem lt_of_lt_of_le {a b c : Ordinal.{u}} : a < b → b ≤ c → a < c :=
  Ordinal.inductionOn₃ a b c fun _ _ _ => OTree.lt_of_lt_of_le

protected theorem lt_trans {a b c : Ordinal.{u}} (h₁ : a < b) (h₂ : b < c) : a < c :=
  Ordinal.lt_of_le_of_lt (Ordinal.le_of_lt h₁) h₂

protected theorem not_lt_of_le {a b : Ordinal.{u}} : a ≤ b → ¬b < a :=
  Ordinal.inductionOn₂ a b fun _ _ => OTree.not_lt_of_le

protected theorem not_le_of_lt {a b : Ordinal.{u}} : a < b → ¬b ≤ a :=
  Ordinal.inductionOn₂ a b fun _ _ => OTree.not_le_of_lt

/-- `<` is well-founded. -/
protected theorem lt_wf : WellFounded (α := Ordinal.{u}) (· < ·) := by
  refine ⟨fun a => Ordinal.inductionOn a fun t => ?_⟩
  induction t using OTree.lt_wf.induction with
  | _ t ih =>
    refine ⟨_, fun b hb => ?_⟩
    induction b using Ordinal.ind with
    | _ s => exact ih s hb

instance : WellFoundedRelation Ordinal.{u} :=
  ⟨(· < ·), Ordinal.lt_wf⟩

/-- Well-founded induction on ordinals. -/
@[elab_as_elim]
protected theorem induction {motive : Ordinal.{u} → Prop} (a : Ordinal.{u})
    (h : ∀ a, (∀ b, b < a → motive b) → motive a) : motive a :=
  Ordinal.lt_wf.induction a h

/-- Extensionality: ordinals with the same predecessors are equal. -/
theorem ext {a b : Ordinal.{u}} (h : ∀ c, c < a ↔ c < b) : a = b := by
  induction a using Ordinal.ind with
  | _ s =>
    induction b using Ordinal.ind with
    | _ t =>
      exact sound (OTree.equiv_of_forall_lt_iff fun r => h (mk r))

theorem le_of_forall_lt {a b : Ordinal.{u}} (h : ∀ c, c < a → c < b) : a ≤ b := by
  induction a using Ordinal.ind with
  | _ s =>
    induction b using Ordinal.ind with
    | _ t =>
      exact OTree.le_of_forall_lt fun r => h (mk r)

theorem le_iff_forall_lt {a b : Ordinal.{u}} : a ≤ b ↔ ∀ c, c < a → c < b :=
  ⟨fun h _ h' => Ordinal.lt_of_lt_of_le h' h, le_of_forall_lt⟩

/-! ## The linear order (classical) -/

protected theorem le_or_lt (a b : Ordinal.{u}) : a ≤ b ∨ b < a :=
  Ordinal.inductionOn₂ a b OTree.le_or_lt

protected theorem le_total (a b : Ordinal.{u}) : a ≤ b ∨ b ≤ a :=
  Ordinal.inductionOn₂ a b OTree.le_total

protected theorem lt_trichotomy (a b : Ordinal.{u}) : a < b ∨ a = b ∨ b < a :=
  Ordinal.inductionOn₂ a b fun s t =>
    (OTree.lt_trichotomy s t).imp id (Or.imp sound id)

protected theorem not_le {a b : Ordinal.{u}} : ¬a ≤ b ↔ b < a :=
  ⟨fun h => (Ordinal.le_or_lt a b).resolve_left h, Ordinal.not_le_of_lt⟩

protected theorem not_lt {a b : Ordinal.{u}} : ¬a < b ↔ b ≤ a :=
  ⟨fun h => (Ordinal.le_or_lt b a).resolve_right h, Ordinal.not_lt_of_le⟩

protected theorem lt_iff_le_and_ne {a b : Ordinal.{u}} : a < b ↔ a ≤ b ∧ a ≠ b :=
  ⟨fun h => ⟨Ordinal.le_of_lt h, Ordinal.ne_of_lt h⟩,
   fun ⟨h₁, h₂⟩ => Ordinal.not_le.mp fun h₃ => h₂ (Ordinal.le_antisymm h₁ h₃)⟩

protected theorem lt_or_eq_of_le {a b : Ordinal.{u}} (h : a ≤ b) : a < b ∨ a = b :=
  (Classical.em (a = b)).elim .inr fun h' => .inl (Ordinal.lt_iff_le_and_ne.mpr ⟨h, h'⟩)

protected theorem le_iff_lt_or_eq {a b : Ordinal.{u}} : a ≤ b ↔ a < b ∨ a = b :=
  ⟨Ordinal.lt_or_eq_of_le, fun h => h.elim Ordinal.le_of_lt Ordinal.le_of_eq⟩

instance : Std.IsLinearOrder Ordinal.{u} where
  le_refl := Ordinal.le_refl
  le_trans _ _ _ := Ordinal.le_trans
  le_antisymm _ _ := Ordinal.le_antisymm
  le_total := Ordinal.le_total

instance : Std.LawfulOrderLT Ordinal.{u} where
  lt_iff _ _ := ⟨fun h => ⟨Ordinal.le_of_lt h, Ordinal.not_le_of_lt h⟩,
    fun h => Ordinal.not_le.mp h.2⟩

/-- Decidability of the order, by excluded middle. -/
noncomputable instance (priority := low) decidableLE (a b : Ordinal.{u}) : Decidable (a ≤ b) :=
  Classical.propDecidable _

noncomputable instance (priority := low) decidableLT (a b : Ordinal.{u}) : Decidable (a < b) :=
  Classical.propDecidable _

noncomputable instance (priority := low) decidableEq : DecidableEq Ordinal.{u} :=
  fun _ _ => Classical.propDecidable _

end Ordinal

end Ordinals
