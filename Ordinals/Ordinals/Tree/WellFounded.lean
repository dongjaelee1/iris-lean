/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Tree.Constructions

/-!
# The ordinal of a well-founded relation, Hartogs ordinals

Let `R` be a well-founded relation on a type `A`. Each element `a : A` has an ordinal: the tree
whose children are the trees of the elements `b` with `R b a`. The strict join of these trees
is the ordinal of the relation. This file defines these trees, the Hartogs ordinal `hartogs A` of a
type `A` (above the ordinals of all well-founded relations on `A`), and the tree `large`
(above the ordinals of all well-founded relations on all types in `Type u`).

This file follows snu-sf/Ordinal (`src/Ordinal.v`, section `FROMWF` and the end of the module
`Ord`). The names of the Rocq lemmas are in the docstrings. The results of this file use no
axioms.

## Main definitions

- `OTree.ofAcc h`: the tree of an accessible element (snu-sf: `Ord.from_acc`).
- `OTree.ofWf hwf a`: the tree of an element of a well-founded relation (snu-sf: `Ord.from_wf`).
- `OTree.ofWfSet hwf`: the tree of a well-founded relation (snu-sf: `Ord.from_wf_set`).
- `OTree.hartogs A`: the Hartogs ordinal of `A` (snu-sf: `Ord.hartogs`).
- `OTree.large`: a tree in `OTree.{u+1}` above the ordinals of all well-founded relations on
  types in `Type u` (snu-sf: `Ord.large`).

## Main results

- `OTree.ofWf_le_iff`, `OTree.lt_ofWf_iff`, `OTree.ofWf_lt_ofWf`: the order on `ofWf`.
- `OTree.omega_equiv_ofWfSet`: `ω` is the tree of `<` on the natural numbers.
- `OTree.equiv_ofWfSet_pos` (not in snu-sf): each tree is equivalent to the tree of a
  well-founded relation. Thus `lift t < large` for each tree `t` (`OTree.lift_lt_large`).

## Implementation notes

`ofAcc` is a recursion on the accessibility proof. Lean does not accept structural recursion on
`Acc` for a definition into `Type`, thus we use the recursor `Acc.rec` directly. The unfolding
lemma `ofAcc_eq` is a definitional equality after a case analysis on the proof.

`Acc R a` is a proposition, thus two proofs `h₀ h₁ : Acc R a` are equal by definition, and
`ofAcc h₀ = ofAcc h₁` holds by `rfl`. snu-sf proves this fact (`Ord.same_acc_le`,
`Ord.same_acc_eq`) by induction.
-/

@[expose] public section

namespace Ordinals

universe u

namespace OTree

/-! ## The tree of an accessible element -/

section Acc

variable {A : Type u} {R : A → A → Prop}

/-- The tree of an accessible element `a`. Its children are the trees of the elements `b` with
`R b a` (snu-sf: `Ord.from_acc`). -/
def ofAcc {a : A} (h : Acc R a) : OTree.{u} :=
  Acc.rec (motive := fun _ _ => OTree.{u}) (fun a _ ih => mk {b // R b a} fun b => ih b.1 b.2) h

/-- The unfolding lemma of `ofAcc`. -/
theorem ofAcc_eq {a : A} (h : Acc R a) :
    ofAcc h = mk {b // R b a} fun b => ofAcc (h.inv b.2) := by
  cases h; rfl

/-- The tree of an accessible element does not depend on the accessibility proof
(snu-sf: `Ord.same_acc_le`, `Ord.same_acc_eq`). -/
theorem ofAcc_proof_irrel {a : A} (h₀ h₁ : Acc R a) : ofAcc h₀ = ofAcc h₁ :=
  rfl

theorem lt_ofAcc_iff {a : A} (h : Acc R a) {t : OTree.{u}} :
    t < ofAcc h ↔ ∃ b, ∃ hb : R b a, t ≤ ofAcc (h.inv hb) := by
  rw [ofAcc_eq h]
  exact ⟨fun ⟨⟨b, hb⟩, h'⟩ => ⟨b, hb, h'⟩, fun ⟨b, hb, h'⟩ => ⟨⟨b, hb⟩, h'⟩⟩

/-- snu-sf: `Ord.lt_from_acc`. -/
theorem ofAcc_lt_ofAcc {a b : A} (hab : R a b) (ha : Acc R a) (hb : Acc R b) :
    ofAcc ha < ofAcc hb :=
  (lt_ofAcc_iff hb).mpr ⟨a, hab, OTree.le_rfl⟩

theorem ofAcc_le_iff {a : A} (h : Acc R a) {t : OTree.{u}} :
    ofAcc h ≤ t ↔ ∀ b (hb : R b a), ofAcc (h.inv hb) < t := by
  rw [ofAcc_eq h]
  exact ⟨fun h' b hb => mk_le.mp h' ⟨b, hb⟩, fun h' => mk_le.mpr fun b => h' b.1 b.2⟩

/-- snu-sf: `Ord.from_acc_supremum`. -/
theorem ofAcc_le_of_forall_lt {a : A} (h : Acc R a) {t : OTree.{u}}
    (H : ∀ b (hb : R b a), ofAcc (h.inv hb) < t) : ofAcc h ≤ t :=
  (ofAcc_le_iff h).mpr H

end Acc

/-! ## The tree of an element of a well-founded relation -/

section WellFounded

variable {A : Type u} {R : A → A → Prop}

/-- The tree of an element `a` of a well-founded relation. Its children are the trees of the
elements `b` with `R b a` (snu-sf: `Ord.from_wf`). -/
def ofWf (hwf : WellFounded R) (a : A) : OTree.{u} :=
  ofAcc (hwf.apply a)

/-- The unfolding lemma of `ofWf`. -/
theorem ofWf_eq (hwf : WellFounded R) (a : A) :
    ofWf hwf a = mk {b // R b a} fun b => ofWf hwf b.1 :=
  ofAcc_eq (hwf.apply a)

theorem ofWf_eq_ofAcc (hwf : WellFounded R) {a : A} (h : Acc R a) : ofWf hwf a = ofAcc h :=
  rfl

/-- The tree of an element does not depend on the proof of well-foundedness
(snu-sf: `Ord.same_wf_le`, `Ord.same_wf_eq`). -/
theorem ofWf_proof_irrel (hwf₀ hwf₁ : WellFounded R) (a : A) : ofWf hwf₀ a = ofWf hwf₁ a :=
  rfl

theorem lt_ofWf_iff (hwf : WellFounded R) {a : A} {t : OTree.{u}} :
    t < ofWf hwf a ↔ ∃ b, R b a ∧ t ≤ ofWf hwf b :=
  (lt_ofAcc_iff (hwf.apply a)).trans
    ⟨fun ⟨b, hb, h⟩ => ⟨b, hb, h⟩, fun ⟨b, hb, h⟩ => ⟨b, hb, h⟩⟩

/-- snu-sf: `Ord.lt_from_wf`. -/
theorem ofWf_lt_ofWf (hwf : WellFounded R) {a b : A} (h : R a b) : ofWf hwf a < ofWf hwf b :=
  ofAcc_lt_ofAcc h _ _

theorem ofWf_le_iff (hwf : WellFounded R) {a : A} {t : OTree.{u}} :
    ofWf hwf a ≤ t ↔ ∀ b, R b a → ofWf hwf b < t :=
  ofAcc_le_iff (hwf.apply a)

/-- snu-sf: `Ord.from_wf_supremum`. -/
theorem ofWf_le_of_forall_lt (hwf : WellFounded R) {a : A} {t : OTree.{u}}
    (H : ∀ b, R b a → ofWf hwf b < t) : ofWf hwf a ≤ t :=
  (ofWf_le_iff hwf).mpr H

/-- The tree of a well-founded relation: the strict join of the trees of its elements
(snu-sf: `Ord.from_wf_set`). -/
def ofWfSet (hwf : WellFounded R) : OTree.{u} :=
  mk A (ofWf hwf)

/-- The tree of a well-founded relation does not depend on the proof of well-foundedness
(snu-sf: `Ord.same_wf_set_le`, `Ord.same_wf_set_eq`). -/
theorem ofWfSet_proof_irrel (hwf₀ hwf₁ : WellFounded R) : ofWfSet hwf₀ = ofWfSet hwf₁ :=
  rfl

/-- snu-sf: `Ord.from_wf_set_upperbound`. -/
theorem ofWf_lt_ofWfSet (hwf : WellFounded R) (a : A) : ofWf hwf a < ofWfSet hwf :=
  child_lt (ofWfSet hwf) a

theorem lt_ofWfSet_iff (hwf : WellFounded R) {t : OTree.{u}} :
    t < ofWfSet hwf ↔ ∃ a, t ≤ ofWf hwf a :=
  Iff.rfl

theorem ofWfSet_le_iff (hwf : WellFounded R) {t : OTree.{u}} :
    ofWfSet hwf ≤ t ↔ ∀ a, ofWf hwf a < t :=
  mk_le

/-- snu-sf: `Ord.from_wf_set_supremum`. -/
theorem ofWfSet_le_of_forall_lt (hwf : WellFounded R) {t : OTree.{u}}
    (H : ∀ a, ofWf hwf a < t) : ofWfSet hwf ≤ t :=
  mk_le.mpr H

end WellFounded

/-! ## Natural numbers and `ω` -/

/-- The order `<` on `ULift Nat` is well-founded. -/
theorem ulift_nat_lt_wf : WellFounded (α := ULift.{u} Nat) (fun m n => m.down < n.down) :=
  InvImage.wf ULift.down Nat.lt_wfRel.wf

/-- The natural number `n` is the tree of `n` in the order `<` on the natural numbers
(snu-sf: `Ord.from_nat_from_peano_lt`). -/
theorem ofNat_equiv_ofWf (n : Nat) : ofNat.{u} n ≈ ofWf ulift_nat_lt_wf ⟨n⟩ := by
  induction n with
  | zero =>
    exact ⟨zero_le _, (ofWf_le_iff _).mpr fun b hb => (Nat.not_lt_zero _ hb).elim⟩
  | succ n ih =>
    refine Equiv.trans (succ_congr ih) ⟨succ_le_of_lt (ofWf_lt_ofWf _ (Nat.lt_succ_self n)), ?_⟩
    refine (ofWf_le_iff _).mpr fun ⟨m⟩ hm => lt_succ_iff.mpr ?_
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with
    | inl h => exact OTree.le_of_lt (ofWf_lt_ofWf _ h)
    | inr h => cases h; exact OTree.le_rfl

/-- `ω` is the tree of the order `<` on the natural numbers
(snu-sf: `Ord.omega_from_peano_lt_set`). -/
theorem omega_equiv_ofWfSet : omega.{u} ≈ ofWfSet ulift_nat_lt_wf.{u} :=
  ⟨sup_le fun n => OTree.le_of_lt <|
      OTree.lt_of_le_of_lt (ofNat_equiv_ofWf n.down).le (ofWf_lt_ofWfSet _ _),
   ofWfSet_le_of_forall_lt _ fun n =>
      OTree.lt_of_le_of_lt (ofNat_equiv_ofWf n.down).ge (ofNat_lt_omega n.down)⟩

/-! ## Hartogs ordinals -/

/-- The Hartogs ordinal of a type `A`: the strict join of the trees of all well-founded relations
on `A` (snu-sf: `Ord.hartogs`). -/
def hartogs (A : Type u) : OTree.{u} :=
  mk {R : A → A → Prop // WellFounded R} fun R => ofWfSet R.2

section Hartogs

variable {A : Type u} {R : A → A → Prop}

/-- snu-sf: `Ord.hartogs_lt_from_wf_set`. -/
theorem ofWfSet_lt_hartogs (hwf : WellFounded R) : ofWfSet hwf < hartogs A :=
  child_lt (hartogs A) ⟨R, hwf⟩

/-- snu-sf: `Ord.hartogs_lt_from_wf`. -/
theorem ofWf_lt_hartogs (hwf : WellFounded R) (a : A) : ofWf hwf a < hartogs A :=
  OTree.lt_trans (ofWf_lt_ofWfSet hwf a) (ofWfSet_lt_hartogs hwf)

theorem hartogs_le_iff {t : OTree.{u}} :
    hartogs A ≤ t ↔ ∀ (R : A → A → Prop) (hwf : WellFounded R), ofWfSet hwf < t :=
  mk_le.trans ⟨fun h R hwf => h ⟨R, hwf⟩, fun h R => h R.1 R.2⟩

/-- snu-sf: `Ord.hartogs_supremum`. -/
theorem hartogs_le_of_forall_lt {t : OTree.{u}}
    (H : ∀ (R : A → A → Prop) (hwf : WellFounded R), ofWfSet hwf < t) : hartogs A ≤ t :=
  hartogs_le_iff.mpr H

end Hartogs

/-! ## A tree above all well-founded relations of a universe -/

/-- A tree in `OTree.{u+1}` above the trees of all well-founded relations on types in `Type u`:
the strict join of their lifts (snu-sf: `Ord.large`). -/
def large : OTree.{u + 1} :=
  mk {p : (A : Type u) × (A → A → Prop) // WellFounded p.2} fun p => lift.{u, u + 1} (ofWfSet p.2)

section Large

variable {A : Type u} {R : A → A → Prop}

/-- snu-sf: `Ord.large_le_hartogs`. -/
theorem lift_hartogs_le_large (A : Type u) : lift.{u, u + 1} (hartogs A) ≤ large.{u} :=
  fun R => ⟨⟨⟨A, R.down.1⟩, R.down.2⟩, OTree.le_rfl⟩

/-- snu-sf: `Ord.large_lt_from_wf_set`. -/
theorem lift_ofWfSet_lt_large (hwf : WellFounded R) : lift.{u, u + 1} (ofWfSet hwf) < large.{u} :=
  child_lt large.{u} ⟨⟨A, R⟩, hwf⟩

/-- snu-sf: `Ord.large_lt_from_wf`. -/
theorem lift_ofWf_lt_large (hwf : WellFounded R) (a : A) :
    lift.{u, u + 1} (ofWf hwf a) < large.{u} :=
  OTree.lt_trans (lift_lt_lift_iff.mpr (ofWf_lt_ofWfSet hwf a)) (lift_ofWfSet_lt_large hwf)

theorem large_le_iff {t : OTree.{u + 1}} :
    large.{u} ≤ t ↔ ∀ (A : Type u) (R : A → A → Prop) (hwf : WellFounded R),
      lift.{u, u + 1} (ofWfSet hwf) < t :=
  mk_le.trans ⟨fun h A R hwf => h ⟨⟨A, R⟩, hwf⟩, fun h p => h p.1.1 p.1.2 p.2⟩

/-- snu-sf: `Ord.large_supremum`. -/
theorem large_le_of_forall_lt {t : OTree.{u + 1}}
    (H : ∀ (A : Type u) (R : A → A → Prop) (hwf : WellFounded R),
      lift.{u, u + 1} (ofWfSet hwf) < t) : large.{u} ≤ t :=
  large_le_iff.mpr H

end Large

/-! ## Each tree is the tree of a well-founded relation

This section is not in snu-sf. The proper subtrees of a tree `t` have positions `Pos t`. The
order `<` of the subtrees is a well-founded relation on `Pos t`, and its tree is equivalent to
`t`. Thus `lift t < large` for each tree `t`. -/

/-- The positions of the proper subtrees of a tree. The position `⟨i, none⟩` is the child `i`,
and the position `⟨i, some p⟩` is the position `p` in the child `i`. -/
def Pos : OTree.{u} → Type u
  | mk ι f => Σ i : ι, Option (Pos (f i))

/-- The subtree at a position. -/
def Pos.tree : {t : OTree.{u}} → Pos t → OTree.{u}
  | mk _ f, ⟨i, none⟩ => f i
  | mk _ f, ⟨i, some p⟩ => Pos.tree (t := f i) p

/-- A proper subtree is below the tree. -/
theorem Pos.tree_lt : ∀ {t : OTree.{u}} (p : Pos t), p.tree < t
  | mk ι f, ⟨i, none⟩ => child_lt (mk ι f) i
  | mk ι f, ⟨i, some p⟩ => OTree.lt_trans (Pos.tree_lt (t := f i) p) (child_lt (mk ι f) i)

/-- Each child of `t` has a position. -/
theorem Pos.exists_tree_eq_child : ∀ (t : OTree.{u}) (k : t.Index), ∃ q : Pos t, q.tree = t.child k
  | mk _ _, k => ⟨⟨k, none⟩, rfl⟩

/-- Each child of a proper subtree has a position. -/
theorem Pos.exists_tree_eq_tree_child :
    ∀ {t : OTree.{u}} (p : Pos t) (k : p.tree.Index), ∃ q : Pos t, q.tree = p.tree.child k
  | mk _ f, ⟨i, none⟩, k =>
    let ⟨q, hq⟩ := Pos.exists_tree_eq_child (f i) k
    ⟨⟨i, some q⟩, hq⟩
  | mk _ f, ⟨i, some p⟩, k =>
    let ⟨q, hq⟩ := Pos.exists_tree_eq_tree_child (t := f i) p k
    ⟨⟨i, some q⟩, hq⟩

/-- The order `<` of the proper subtrees of a tree. -/
def Pos.Rel (t : OTree.{u}) : Pos t → Pos t → Prop :=
  InvImage (· < ·) Pos.tree

theorem Pos.rel_wf (t : OTree.{u}) : WellFounded (Pos.Rel t) :=
  InvImage.wf Pos.tree lt_wf

/-- The tree of a position in the subtree order is equivalent to the subtree. -/
theorem ofWf_pos_equiv {t : OTree.{u}} (p : Pos t) : ofWf (Pos.rel_wf t) p ≈ p.tree := by
  induction p using (Pos.rel_wf t).induction with
  | _ p ih =>
    constructor
    · exact (ofWf_le_iff _).mpr fun q hq => OTree.lt_of_le_of_lt (ih q hq).le hq
    · refine le_iff_forall_child_lt.mpr fun k => ?_
      obtain ⟨q, hq⟩ := Pos.exists_tree_eq_tree_child p k
      have hqp : Pos.Rel t q p := show q.tree < p.tree from hq ▸ child_lt p.tree k
      exact hq ▸ OTree.lt_of_le_of_lt (ih q hqp).ge (ofWf_lt_ofWf _ hqp)

/-- Each tree is equivalent to the tree of a well-founded relation: the order of its proper
subtrees. -/
theorem equiv_ofWfSet_pos (t : OTree.{u}) : t ≈ ofWfSet (Pos.rel_wf t) := by
  constructor
  · refine le_iff_forall_child_lt.mpr fun k => ?_
    obtain ⟨q, hq⟩ := Pos.exists_tree_eq_child t k
    exact hq ▸ OTree.lt_of_le_of_lt (ofWf_pos_equiv q).ge (ofWf_lt_ofWfSet _ q)
  · exact ofWfSet_le_of_forall_lt _ fun p =>
      OTree.lt_of_le_of_lt (ofWf_pos_equiv p).le (Pos.tree_lt p)

/-- Each tree is below the Hartogs ordinal of the positions of its proper subtrees. -/
theorem lt_hartogs_pos (t : OTree.{u}) : t < hartogs (Pos t) :=
  OTree.lt_of_le_of_lt (equiv_ofWfSet_pos t).le (ofWfSet_lt_hartogs _)

/-- `large` is above the lift of each tree. -/
theorem lift_lt_large (t : OTree.{u}) : lift.{u, u + 1} t < large.{u} :=
  OTree.lt_of_le_of_lt (lift_le_lift_iff.mpr (equiv_ofWfSet_pos t).le)
    (lift_ofWfSet_lt_large _)

end OTree

end Ordinals
