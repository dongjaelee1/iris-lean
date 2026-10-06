/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Tree.WellFounded

/-!
# Trees of related well-founded relations

This file compares the trees `ofWf` and `ofWfSet` of different well-founded relations:

- a larger relation gives larger trees (`ofWf_mono`, `ofWfSet_mono`);
- a map that keeps the relation gives larger trees (`ofWf_le_ofWf_of_map`);
- the image of a relation under an injective map gives equivalent trees
  (`ofWf_equiv_ofWf_projRel`, `ofWfSet_equiv_ofWfSet_rangeRel`);
- for a total relation, the tree of an element `a` is the tree of the relation on the elements
  below `a` (`ofWf_equiv_ofWfSet_cutRel`).

This file follows snu-sf/Ordinal (`src/WfRel.v`). The names of the Rocq lemmas are in the
docstrings. The results of this file use no axioms.

## Notes on the port

- All of `WfRel.v` is constructive. This file ports all of it, and leaves nothing for the
  classical layer.
- snu-sf `projected_rel_rev RB f` is the core relation `InvImage RB f`. Its well-foundedness
  (snu-sf: `projected_rel_rev_well_founded`) is the core lemma `InvImage.wf`, which does not
  need an injective map.
- snu-sf `projected_rel_sig` is `ProjRel RA (toRange f)` here (`RangeRel RA f`).
- snu-sf uses proof irrelevance in `cut_rel_total`. In Lean, proof irrelevance is a definitional
  equality.
-/

@[expose] public section

namespace Ordinals

universe u v

namespace OTree

/-! ## Monotonicity in the relation -/

section Mono

variable {A : Type u} {R₀ R₁ : A → A → Prop}

/-- A larger relation gives a larger tree (snu-sf: `from_acc_mon`). -/
theorem ofAcc_mono (H : Subrelation R₀ R₁) {a : A} (h₀ : Acc R₀ a) (h₁ : Acc R₁ a) :
    ofAcc h₀ ≤ ofAcc h₁ := by
  induction h₀ with
  | intro a _ ih =>
    exact (ofAcc_le_iff _).mpr fun b hb =>
      OTree.lt_of_le_of_lt (ih b hb (h₁.inv (H hb))) (ofAcc_lt_ofAcc (H hb) _ h₁)

/-- A larger relation gives a larger tree (snu-sf: `from_wf_mon`). -/
theorem ofWf_mono (H : Subrelation R₀ R₁) (hwf₀ : WellFounded R₀) (hwf₁ : WellFounded R₁)
    (a : A) : ofWf hwf₀ a ≤ ofWf hwf₁ a :=
  ofAcc_mono H _ _

/-- A larger relation gives a larger tree (snu-sf: `from_wf_set_le`). -/
theorem ofWfSet_mono (H : Subrelation R₀ R₁) (hwf₀ : WellFounded R₀) (hwf₁ : WellFounded R₁) :
    ofWfSet hwf₀ ≤ ofWfSet hwf₁ :=
  mk_mono fun a => ofWf_mono H hwf₀ hwf₁ a

end Mono

/-! ## Maps that keep the relation -/

section Map

variable {A B : Type u} {RA : A → A → Prop} {RB : B → B → Prop}

/-- A map that keeps the relation gives larger trees (snu-sf: `from_wf_inj`). -/
theorem ofWf_le_ofWf_of_map (hA : WellFounded RA) (hB : WellFounded RB) {f : A → B}
    (hf : ∀ {a b}, RA a b → RB (f a) (f b)) (a : A) : ofWf hA a ≤ ofWf hB (f a) := by
  induction a using hA.induction with
  | _ a ih =>
    exact (ofWf_le_iff hA).mpr fun b hb =>
      OTree.lt_of_le_of_lt (ih b hb) (ofWf_lt_ofWf hB (hf hb))

/-- A map that keeps the relation gives a larger tree (snu-sf: `from_wf_set_inj`). -/
theorem ofWfSet_le_ofWfSet_of_map (hA : WellFounded RA) (hB : WellFounded RB) {f : A → B}
    (hf : ∀ {a b}, RA a b → RB (f a) (f b)) : ofWfSet hA ≤ ofWfSet hB :=
  ofWfSet_le_of_forall_lt hA fun a =>
    OTree.lt_of_le_of_lt (ofWf_le_ofWf_of_map hA hB hf a) (ofWf_lt_ofWfSet hB (f a))

end Map

/-! ## The image of a relation -/

/-- The image of a relation `R` under a map `f` (snu-sf: `projected_rel`). -/
inductive ProjRel {A : Type u} {B : Type v} (R : A → A → Prop) (f : A → B) : B → B → Prop
  /-- If `R a b`, then `f a` and `f b` are related. -/
  | intro {a b : A} : R a b → ProjRel R f (f a) (f b)

namespace ProjRel

variable {A : Type u} {B : Type v} {RA : A → A → Prop} {RB : B → B → Prop} {f : A → B}

/-- snu-sf: `inj_projected_rel_incl`. -/
theorem subrelation (hf : ∀ {a b}, RA a b → RB (f a) (f b)) : Subrelation (ProjRel RA f) RB
  | _, _, intro h => hf h

/-- For an injective map, a predecessor of `f a` is the image of a predecessor of `a`. -/
theorem inv (hf : Function.Injective f) {y : B} {a : A} (h : ProjRel RA f y (f a)) :
    ∃ b, y = f b ∧ RA b a := by
  generalize hz : f a = z at h
  cases h with
  | intro hab => exact ⟨_, rfl, (hf hz) ▸ hab⟩

/-- The image of a well-founded relation under an injective map is well-founded
(snu-sf: `embed_projected_rel_well_founded`). -/
theorem wf (hA : WellFounded RA) (hf : Function.Injective f) : WellFounded (ProjRel RA f) := by
  have key : ∀ a, Acc (ProjRel RA f) (f a) := fun a => by
    induction a using hA.induction with
    | _ a ih =>
      exact ⟨_, fun y hy => let ⟨b, hb, hba⟩ := inv hf hy; hb ▸ ih b hba⟩
  exact ⟨fun y => ⟨_, fun x hx => by cases hx with | intro _ => exact key _⟩⟩

/-- If a map keeps the relation into a well-founded relation, then the image is well-founded
(snu-sf: `inj_projected_rel_well_founded`). -/
theorem wf_of_map (hB : WellFounded RB) (hf : ∀ {a b}, RA a b → RB (f a) (f b)) :
    WellFounded (ProjRel RA f) :=
  Subrelation.wf (subrelation (RA := RA) (f := f) hf) hB

end ProjRel

section Proj

variable {A B : Type u} {RA : A → A → Prop}

/-- The image under an injective map gives an equivalent tree
(snu-sf: `from_wf_projected_rel_eq`). -/
theorem ofWf_equiv_ofWf_projRel (hA : WellFounded RA) {f : A → B} (hf : Function.Injective f)
    (a : A) : ofWf hA a ≈ ofWf (ProjRel.wf hA hf) (f a) := by
  induction a using hA.induction with
  | _ a ih =>
    constructor
    · exact (ofWf_le_iff hA).mpr fun b hb =>
        OTree.lt_of_le_of_lt (ih b hb).le (ofWf_lt_ofWf _ (ProjRel.intro hb))
    · refine (ofWf_le_iff _).mpr fun y hy => ?_
      obtain ⟨b, rfl, hba⟩ := ProjRel.inv hf hy
      exact OTree.lt_of_le_of_lt (ih b hba).ge (ofWf_lt_ofWf hA hba)

/-- snu-sf: `from_wf_set_projected_rel_le`. -/
theorem ofWfSet_le_ofWfSet_projRel (hA : WellFounded RA) {f : A → B}
    (hf : Function.Injective f) : ofWfSet hA ≤ ofWfSet (ProjRel.wf hA hf) :=
  ofWfSet_le_of_forall_lt hA fun a =>
    OTree.lt_of_le_of_lt (ofWf_equiv_ofWf_projRel hA hf a).le (ofWf_lt_ofWfSet _ (f a))

end Proj

/-! ## The image of a relation on the range of a map -/

/-- The range of a map (snu-sf: `projected_rel_set`). -/
abbrev Range {A : Type u} {B : Type v} (f : A → B) : Type v :=
  {b // ∃ a, f a = b}

/-- The map into the range (snu-sf: `to_projected_sig`). -/
def toRange {A : Type u} {B : Type v} (f : A → B) (a : A) : Range f :=
  ⟨f a, a, rfl⟩

theorem toRange_injective {A : Type u} {B : Type v} {f : A → B} (hf : Function.Injective f) :
    Function.Injective (toRange f) :=
  fun _ _ h => hf (congrArg Subtype.val h)

/-- The image of a relation on the range of a map (snu-sf: `projected_rel_sig`). -/
abbrev RangeRel {A : Type u} {B : Type v} (R : A → A → Prop) (f : A → B) :
    Range f → Range f → Prop :=
  ProjRel R (toRange f)

section Range

variable {A B : Type u} {RA : A → A → Prop} {f : A → B}

/-- snu-sf: `projected_rel_sig_well_founded`. -/
theorem RangeRel.wf (hA : WellFounded RA) (hf : Function.Injective f) :
    WellFounded (RangeRel RA f) :=
  ProjRel.wf hA (toRange_injective hf)

/-- snu-sf: `from_wf_projected_rel_sig_eq`. -/
theorem ofWf_equiv_ofWf_rangeRel (hA : WellFounded RA) (hf : Function.Injective f) (a : A) :
    ofWf hA a ≈ ofWf (RangeRel.wf hA hf) (toRange f a) :=
  ofWf_equiv_ofWf_projRel hA (toRange_injective hf) a

/-- snu-sf: `from_wf_set_projected_rel_sig_le`. -/
theorem ofWfSet_le_ofWfSet_rangeRel (hA : WellFounded RA) (hf : Function.Injective f) :
    ofWfSet hA ≤ ofWfSet (RangeRel.wf hA hf) :=
  ofWfSet_le_ofWfSet_projRel hA (toRange_injective hf)

/-- The image on the range of an injective map gives an equivalent tree
(snu-sf: `from_wf_set_projected_rel_sig_eq`). -/
theorem ofWfSet_equiv_ofWfSet_rangeRel (hA : WellFounded RA) (hf : Function.Injective f) :
    ofWfSet hA ≈ ofWfSet (RangeRel.wf hA hf) :=
  ⟨ofWfSet_le_ofWfSet_rangeRel hA hf,
   ofWfSet_le_of_forall_lt _ fun ⟨_, a, h⟩ => by
    subst h
    exact OTree.lt_of_le_of_lt (ofWf_equiv_ofWf_rangeRel hA hf a).ge (ofWf_lt_ofWfSet hA a)⟩

end Range

/-! ## Cuts -/

section Cut

variable {A : Type u} {R : A → A → Prop}

/-- A well-founded relation has no cycle of length two. -/
theorem wf_not_rel_of_rel (hwf : WellFounded R) {a b : A} : R a b → ¬R b a := by
  induction a using hwf.induction generalizing b with
  | _ a ih => exact fun h₁ h₂ => ih b h₂ h₂ h₁

/-- A well-founded relation has no cycle of length three. -/
theorem wf_not_cycle₃ (hwf : WellFounded R) {a b c : A} : R a b → R b c → ¬R c a := by
  induction a using hwf.induction generalizing b c with
  | _ a ih => exact fun h₁ h₂ h₃ => ih c h₃ h₃ h₁ h₂

/-- A total well-founded relation is transitive. -/
theorem wf_trans_of_total (hwf : WellFounded R) (htot : ∀ a b, R a b ∨ a = b ∨ R b a)
    {a b c : A} (h₁ : R a b) (h₂ : R b c) : R a c :=
  match htot a c with
  | .inl h => h
  | .inr (.inl h) => (wf_not_rel_of_rel hwf (h ▸ h₁) h₂).elim
  | .inr (.inr h) => (wf_not_cycle₃ hwf h₁ h₂ h).elim

/-- The relation `R` on the elements below `a` (snu-sf: `cut_rel`). -/
def CutRel (R : A → A → Prop) (a : A) : {b // R b a} → {b // R b a} → Prop :=
  fun x y => R x.1 y.1

/-- snu-sf: `cut_rel_well_founded`. -/
theorem CutRel.wf (hwf : WellFounded R) (a : A) : WellFounded (CutRel R a) :=
  InvImage.wf Subtype.val hwf

/-- snu-sf: `cut_rel_total`. -/
theorem CutRel.total (htot : ∀ a b, R a b ∨ a = b ∨ R b a) (a : A) (x y : {b // R b a}) :
    CutRel R a x y ∨ x = y ∨ CutRel R a y x :=
  match htot x.1 y.1 with
  | .inl h => .inl h
  | .inr (.inl h) => .inr (.inl (Subtype.ext h))
  | .inr (.inr h) => .inr (.inr h)

/-- For a total relation, the tree of `b` is the same in the cut below `a`
(snu-sf: `from_wf_cut`). -/
theorem ofWf_equiv_ofWf_cutRel (hwf : WellFounded R) (htot : ∀ a b, R a b ∨ a = b ∨ R b a)
    (a : A) {b : A} (hb : R b a) : ofWf hwf b ≈ ofWf (CutRel.wf hwf a) ⟨b, hb⟩ := by
  induction b using hwf.induction with
  | _ b ih =>
    constructor
    · refine (ofWf_le_iff hwf).mpr fun c hc => ?_
      have hca : R c a := wf_trans_of_total hwf htot hc hb
      exact OTree.lt_of_le_of_lt (ih c hc hca).le
        (ofWf_lt_ofWf (CutRel.wf hwf a) (a := ⟨c, hca⟩) (b := ⟨b, hb⟩) hc)
    · refine (ofWf_le_iff _).mpr fun ⟨c, hca⟩ hc => ?_
      exact OTree.lt_of_le_of_lt (ih c hc hca).ge (ofWf_lt_ofWf hwf hc)

/-- For a total relation, the tree of `a` is the tree of the cut below `a`
(snu-sf: `from_wf_set_cut`). -/
theorem ofWf_equiv_ofWfSet_cutRel (hwf : WellFounded R)
    (htot : ∀ a b, R a b ∨ a = b ∨ R b a) (a : A) : ofWf hwf a ≈ ofWfSet (CutRel.wf hwf a) :=
  ⟨(ofWf_le_iff hwf).mpr fun b hb =>
      OTree.lt_of_le_of_lt (ofWf_equiv_ofWf_cutRel hwf htot a hb).le
        (ofWf_lt_ofWfSet (CutRel.wf hwf a) ⟨b, hb⟩),
   ofWfSet_le_of_forall_lt (CutRel.wf hwf a) fun ⟨_, hb⟩ =>
      OTree.lt_of_le_of_lt (ofWf_equiv_ofWf_cutRel hwf htot a hb).ge (ofWf_lt_ofWf hwf hb)⟩

end Cut

end OTree

end Ordinals
