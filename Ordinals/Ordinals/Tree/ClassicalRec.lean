/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Tree.Classical
public import Ordinals.Tree.Rec
public import Ordinals.Tree.WfRel

/-!
# Classical recursion on trees

With excluded middle, the order on trees is total. This file uses totality for these results:

- Each tree below the tree `ofWf hwf a` of a well-founded relation is equivalent to a tree
  `ofWf hwf b` (`exists_equiv_ofWf_of_lt`).
- Each inhabited set of trees has a least element (`exists_isMeet`).
- Each tree is a successor or the join of an open family (`succ_or_limit`). Thus we have an
  induction principle with the three cases zero, successor and limit (`limitInduction`).
- The recursion `trec` into a type `D` is monotone if `D` has joins of chains only
  (`ChainRecLaws`).
- Fixed-point theorem: if `next` is expansive, then `trec` at the Hartogs ordinal of `D` is a
  fixed point of `next` (`ChainRecLaws.next_trec_hartogs_le`).

This file follows snu-sf/Ordinal (`src/ClassicalOrdinal.v`, module `ClassicOrd`). The names of
the Rocq lemmas are in the docstrings. The results of this file use excluded middle
(`Classical.em`).

## Recursion with joins of chains

snu-sf `ClassicOrd.rec` is `Ord.rec` with other hypotheses on `D`. Here it is `trec` of
`Ordinals.Tree.Rec`. The lemmas are in the namespace `OTree.ChainRecLaws`. They take a proof
of `ChainRecLaws dle wf djoin base next`:

- `dle` is a preorder on the elements that satisfy `wf`.
- `djoin A ds` is a least upper bound of each chain `ds`. `JoinLaws` of `Ordinals.Tree.Rec`
  has least upper bounds of all families.
- `base` and `next` keep `wf`.
- `next` is expansive: `dle d (next d)`.
- `next` respects the equivalence `dle d₀ d₁ ∧ dle d₁ d₀`. It is possible that `next` is not
  monotone.

With these laws, `trec` is monotone (`ChainRecLaws.trec_le_trec`). Thus the families that `trec`
joins are chains. `ChainRecLaws.of_joinLaws` gives these laws from the laws of
`Ordinals.Tree.Rec`.

The first lemma `rec_all` of snu-sf shows four properties of `trec` together, by well-founded
induction. The proof here is shorter: a tree `s` below `mk ι f` is at most a child `f i`, thus
we do not need the case analysis of snu-sf on a tree between `s` and `mk ι f`.

## Main definitions

- `OTree.IsMeet P t`: `t` is a least element of `P` (snu-sf: `ClassicOrd.is_meet`).
- `OTree.IsChain dle ds`: each two members of `ds` are comparable.
- `OTree.ChainRecLaws`: the laws of the target type (snu-sf: the hypotheses of section
  `ClassicOrd.REC`).
- `OTree.StrictlyIncreasing`: the relation of the values of `trec` that increase strictly
  (snu-sf: `ClassicOrd.strictly_increasing`).
- `OTree.NotFixed`: `trec` increases strictly up to a tree (snu-sf: `ClassicOrd.not_fixed`).
-/

@[expose] public section

namespace Ordinals

universe u v

namespace OTree

/-! ## Trees of well-founded relations -/

section WellFounded

variable {A : Type u} {R : A → A → Prop}

/-- Each tree below the tree of an accessible element is equivalent to the tree of an
accessible element (snu-sf: `ClassicOrd.from_acc_complete`). -/
theorem exists_equiv_ofAcc_of_lt {a : A} (h : Acc R a) {t : OTree.{u}} (ht : t < ofAcc h) :
    ∃ b, ∃ hb : Acc R b, t ≈ ofAcc hb := by
  induction h generalizing t with
  | intro a h ih =>
    obtain ⟨b, hb, hle⟩ := (lt_ofAcc_iff _).mp ht
    rcases lt_or_equiv_of_le hle with hlt | he
    · exact ih b hb hlt
    · exact ⟨b, _, he⟩

/-- Each tree below `ofWf hwf a` is equivalent to a tree `ofWf hwf b`
(snu-sf: `ClassicOrd.from_wf_complete`). -/
theorem exists_equiv_ofWf_of_lt (hwf : WellFounded R) {a : A} {t : OTree.{u}}
    (ht : t < ofWf hwf a) : ∃ b, t ≈ ofWf hwf b :=
  let ⟨b, _, hb⟩ := exists_equiv_ofAcc_of_lt (hwf.apply a) ht
  ⟨b, hb⟩

/-- Each tree below `ofWfSet hwf` is equivalent to a tree `ofWf hwf a`
(snu-sf: `ClassicOrd.from_wf_set_complete`). -/
theorem exists_equiv_ofWf_of_lt_ofWfSet (hwf : WellFounded R) {t : OTree.{u}}
    (ht : t < ofWfSet hwf) : ∃ a, t ≈ ofWf hwf a := by
  obtain ⟨a, ha⟩ := (lt_ofWfSet_iff hwf).mp ht
  rcases lt_or_equiv_of_le ha with hlt | he
  · exact exists_equiv_ofWf_of_lt hwf hlt
  · exact ⟨a, he⟩

/-- Let `R₀` be a subrelation of `R₁`. If an element `a₂` has an `R₁`-predecessor, and each
element with an `R₀`-predecessor is an `R₁`-predecessor of `a₂`, then the tree of `R₀` is below
the tree of `R₁` (snu-sf: `ClassicOrd.from_wf_set_lt`). -/
theorem ofWfSet_lt_ofWfSet {R₀ R₁ : A → A → Prop} (H : Subrelation R₀ R₁)
    (hwf₀ : WellFounded R₀) (hwf₁ : WellFounded R₁)
    (htop : ∃ a₂ x, R₁ x a₂ ∧ ∀ a₀ a₁, R₀ a₀ a₁ → R₁ a₁ a₂) :
    ofWfSet hwf₀ < ofWfSet hwf₁ := by
  obtain ⟨a₂, x, hx, htop⟩ := htop
  refine (lt_ofWfSet_iff hwf₁).mpr ⟨a₂, (ofWfSet_le_iff hwf₀).mpr fun a₁ => ?_⟩
  refine (Classical.em (∃ a₀, R₀ a₀ a₁)).elim (fun ⟨a₀, h⟩ => ?_) (fun h => ?_)
  · exact OTree.lt_of_le_of_lt (ofWf_mono H hwf₀ hwf₁ a₁) (ofWf_lt_ofWf hwf₁ (htop a₀ a₁ h))
  · refine OTree.lt_of_le_of_lt ?_ (ofWf_lt_ofWf hwf₁ hx)
    exact (ofWf_le_iff hwf₀).mpr fun b hb => (h ⟨b, hb⟩).elim

end WellFounded

/-! ## Least elements -/

/-- `t` is a least element of `P` (snu-sf: `ClassicOrd.is_meet`). -/
def IsMeet (P : OTree.{u} → Prop) (t : OTree.{u}) : Prop :=
  P t ∧ ∀ s, P s → t ≤ s

/-- Each inhabited set of trees has a least element (snu-sf: `ClassicOrd.meet_exists`). -/
theorem exists_isMeet {P : OTree.{u} → Prop} (h : ∃ t, P t) : ∃ t, IsMeet P t := by
  refine Classical.byContradiction fun hn => ?_
  obtain ⟨t, ht⟩ := h
  refine lt_wf.induction (C := fun t => ¬P t) t (fun t ih hp => ?_) ht
  exact hn ⟨t, hp, fun s hs => not_lt.mp fun hlt => ih s hlt hs⟩

/-- Two least elements of a set are equivalent. -/
theorem IsMeet.equiv {P : OTree.{u} → Prop} {s t : OTree.{u}} (hs : IsMeet P s)
    (ht : IsMeet P t) : s ≈ t :=
  ⟨hs.2 t ht.1, ht.2 s hs.1⟩

/-! ## Successors and limits -/

/-- Each tree is a successor or the join of an open family (snu-sf: `ClassicOrd.limit_or_S`).
For a tree equivalent to `zero`, the family is empty. -/
theorem succ_or_limit (t : OTree.{u}) :
    (∃ s, t ≈ succ s) ∨
      ∃ (ι : Type u) (f : ι → OTree.{u}), t ≈ sup f ∧ ∀ i, ∃ j, f i < f j := by
  cases t with
  | mk ι f =>
    refine (Classical.em (∀ i, ∃ j, f i < f j)).elim
      (fun h => .inr ⟨ι, f, ⟨?_, sup_le_mk f⟩, h⟩) (fun h => .inl ?_)
    · exact mk_le.mpr fun i =>
        let ⟨j, hj⟩ := h i
        OTree.lt_of_lt_of_le hj (le_sup f j)
    · obtain ⟨i, hi⟩ := Classical.not_forall.mp h
      exact ⟨f i, mk_le.mpr fun j => lt_succ_iff.mpr (not_lt.mp fun hlt => hi ⟨j, hlt⟩),
        succ_le_of_lt (child_lt (mk ι f) i)⟩

/-- Induction with the three cases zero, successor and limit (snu-sf: `ClassicOrd.ind`). In each
case, the induction hypothesis also holds for all smaller trees. -/
@[elab_as_elim]
theorem limitInduction {motive : OTree.{u} → Prop} (t : OTree.{u})
    (zero : ∀ t, t ≈ OTree.zero → (∀ s, s < t → motive s) → motive t)
    (succ : ∀ s t, t ≈ OTree.succ s → motive s → (∀ r, r < t → motive r) → motive t)
    (limit : ∀ (ι : Type u) (f : ι → OTree.{u}) (t : OTree.{u}), t ≈ sup f → Nonempty ι →
      (∀ i, ∃ j, f i < f j) → (∀ i, motive (f i)) → (∀ s, s < t → motive s) → motive t) :
    motive t := by
  induction t using lt_wf.induction with
  | _ t ih =>
    rcases succ_or_limit t with ⟨s, hs⟩ | ⟨ι, f, hf, ho⟩
    · exact succ s t hs (ih s (OTree.lt_of_lt_of_le (lt_succ s) hs.ge)) ih
    · refine (Classical.em (Nonempty ι)).elim
        (fun hne => limit ι f t hf hne ho (fun i => ih _ ?_) ih) (fun hne => zero t ?_ ih)
      · obtain ⟨j, hj⟩ := ho i
        exact OTree.lt_of_lt_of_le hj (OTree.le_trans (le_sup f j) hf.ge)
      · exact ⟨OTree.le_trans hf.le (sup_le fun i => (hne ⟨i⟩).elim), zero_le _⟩

/-! ## Chains and their joins -/

/-- Each two members of the family `ds` are comparable. -/
def IsChain {D : Type v} (dle : D → D → Prop) {A : Type u} (ds : A → D) : Prop :=
  ∀ a₀ a₁, dle (ds a₀) (ds a₁) ∨ dle (ds a₁) (ds a₀)

/-- The laws of joins of chains: `dle` is a preorder on the elements that satisfy `wf`, and
`djoin A ds` is a least upper bound of each chain `ds` (snu-sf: the hypotheses `dle_reflexive`,
`dle_transitive`, `djoin_upperbound`, `djoin_supremum`, `djoin_wf` of section
`ClassicOrd.REC`). -/
structure ChainJoinLaws {D : Type v} (dle : D → D → Prop) (wf : D → Prop)
    (djoin : (A : Type u) → (A → D) → D) : Prop where
  /-- snu-sf: `dle_reflexive`. -/
  le_refl : ∀ {d}, wf d → dle d d
  /-- snu-sf: `dle_transitive`. -/
  le_trans : ∀ {d₀ d₁ d₂}, wf d₀ → wf d₁ → wf d₂ → dle d₀ d₁ → dle d₁ d₂ → dle d₀ d₂
  /-- snu-sf: `djoin_upperbound`. -/
  le_join : ∀ {A : Type u} {ds : A → D}, IsChain dle ds → (∀ a, wf (ds a)) →
    ∀ a, dle (ds a) (djoin A ds)
  /-- snu-sf: `djoin_supremum`. -/
  join_le : ∀ {A : Type u} {ds : A → D} {d : D}, IsChain dle ds → (∀ a, wf (ds a)) → wf d →
    (∀ a, dle (ds a) d) → dle (djoin A ds) d
  /-- snu-sf: `djoin_wf`. -/
  join_wf : ∀ {A : Type u} {ds : A → D}, IsChain dle ds → (∀ a, wf (ds a)) → wf (djoin A ds)

/-- The laws of the target type of the classical recursion (snu-sf: the hypotheses of section
`ClassicOrd.REC`): joins of chains, `base` and `next` keep `wf`, `next` is expansive, and `next`
respects the equivalence `dle d₀ d₁ ∧ dle d₁ d₀`. -/
structure ChainRecLaws {D : Type v} (dle : D → D → Prop) (wf : D → Prop)
    (djoin : (A : Type u) → (A → D) → D) (base : D) (next : D → D) : Prop
    extends ChainJoinLaws dle wf djoin, StepLaws wf base next where
  /-- snu-sf: `next_le`. -/
  next_le : ∀ {d}, wf d → dle d (next d)
  /-- snu-sf: `next_eq`. -/
  next_congr : ∀ {d₀ d₁}, wf d₀ → wf d₁ → dle d₀ d₁ → dle d₁ d₀ → dle (next d₀) (next d₁)

section Laws

variable {D : Type v} {dle : D → D → Prop} {wf : D → Prop} {djoin : (A : Type u) → (A → D) → D}
  {base : D} {next : D → D}

/-- The joins of all families are joins of chains. -/
theorem JoinLaws.toChainJoinLaws (hJ : JoinLaws dle wf djoin) : ChainJoinLaws dle wf djoin :=
  ⟨hJ.le_refl, hJ.le_trans, fun _ => hJ.le_join, fun _ => hJ.join_le, fun _ => hJ.join_wf⟩

/-- The laws of `Ordinals.Tree.Rec` with an expansive `next` give the laws of the classical
recursion. -/
theorem ChainRecLaws.of_joinLaws (hJ : JoinLaws dle wf djoin) (hS : StepLaws wf base next)
    (hl : ∀ {d}, wf d → dle d (next d)) (hm : NextMono dle wf next) :
    ChainRecLaws dle wf djoin base next :=
  { hJ.toChainJoinLaws, hS with
    next_le := hl
    next_congr := fun h₀ h₁ l _ => hm h₀ h₁ l }

namespace ChainJoinLaws

variable (hJ : ChainJoinLaws dle wf djoin)
include hJ

/-- The family of `dunion` is a chain if its two members are comparable. -/
theorem isChain_cond {d₀ d₁ : D} (h₀ : wf d₀) (h₁ : wf d₁) (h : dle d₀ d₁ ∨ dle d₁ d₀) :
    IsChain dle fun b : ULift.{u} Bool => cond b.down d₀ d₁
  | ⟨true⟩, ⟨true⟩ => .inl (hJ.le_refl h₀)
  | ⟨true⟩, ⟨false⟩ => h
  | ⟨false⟩, ⟨true⟩ => h.symm
  | ⟨false⟩, ⟨false⟩ => .inl (hJ.le_refl h₁)

/-- A lower bound of a member of a chain is a lower bound of the join. -/
theorem le_join_of_le {A : Type u} {ds : A → D} {d : D} (hc : IsChain dle ds)
    (hds : ∀ a, wf (ds a)) (hd : wf d) (a : A) (h : dle d (ds a)) : dle d (djoin A ds) :=
  hJ.le_trans hd (hds a) (hJ.join_wf hc hds) h (hJ.le_join hc hds a)

/-- snu-sf: the local `dunion_wf` of section `ClassicOrd.REC`. -/
theorem dunion_wf {d₀ d₁ : D} (h₀ : wf d₀) (h₁ : wf d₁) (h : dle d₀ d₁ ∨ dle d₁ d₀) :
    wf (dunion djoin d₀ d₁) :=
  hJ.join_wf (hJ.isChain_cond h₀ h₁ h) (cond_wf h₀ h₁)

/-- snu-sf: the local `dunion_l` of section `ClassicOrd.REC`. -/
theorem le_dunion_left {d₀ d₁ : D} (h₀ : wf d₀) (h₁ : wf d₁) (h : dle d₀ d₁ ∨ dle d₁ d₀) :
    dle d₀ (dunion djoin d₀ d₁) :=
  hJ.le_join (hJ.isChain_cond h₀ h₁ h) (cond_wf h₀ h₁) ⟨true⟩

/-- snu-sf: the local `dunion_r` of section `ClassicOrd.REC`. -/
theorem le_dunion_right {d₀ d₁ : D} (h₀ : wf d₀) (h₁ : wf d₁) (h : dle d₀ d₁ ∨ dle d₁ d₀) :
    dle d₁ (dunion djoin d₀ d₁) :=
  hJ.le_join (hJ.isChain_cond h₀ h₁ h) (cond_wf h₀ h₁) ⟨false⟩

/-- snu-sf: the local `dunion_supremum` of section `ClassicOrd.REC`. -/
theorem dunion_le {d₀ d₁ d : D} (h₀ : wf d₀) (h₁ : wf d₁) (hd : wf d)
    (h : dle d₀ d₁ ∨ dle d₁ d₀) (l₀ : dle d₀ d) (l₁ : dle d₁ d) : dle (dunion djoin d₀ d₁) d :=
  hJ.join_le (hJ.isChain_cond h₀ h₁ h) (cond_wf h₀ h₁) hd fun
    | ⟨true⟩ => l₀
    | ⟨false⟩ => l₁

/-- A family that is pointwise equivalent to a chain is a chain. -/
theorem isChain_of_equiv {A : Type u} {ds es : A → D} (hc : IsChain dle es)
    (hds : ∀ a, wf (ds a)) (hes : ∀ a, wf (es a))
    (h : ∀ a, dle (ds a) (es a) ∧ dle (es a) (ds a)) : IsChain dle ds := fun a₀ a₁ =>
  (hc a₀ a₁).imp
    (fun l => hJ.le_trans (hds a₀) (hes a₁) (hds a₁)
      (hJ.le_trans (hds a₀) (hes a₀) (hes a₁) (h a₀).1 l) (h a₁).2)
    (fun l => hJ.le_trans (hds a₁) (hes a₀) (hds a₀)
      (hJ.le_trans (hds a₁) (hes a₁) (hes a₀) (h a₁).1 l) (h a₀).2)

/-- The joins of pointwise equivalent chains are equivalent. -/
theorem join_congr {A : Type u} {ds es : A → D} (hc : IsChain dle es)
    (hds : ∀ a, wf (ds a)) (hes : ∀ a, wf (es a))
    (h : ∀ a, dle (ds a) (es a) ∧ dle (es a) (ds a)) :
    dle (djoin A ds) (djoin A es) ∧ dle (djoin A es) (djoin A ds) :=
  have hc' := hJ.isChain_of_equiv hc hds hes h
  ⟨hJ.join_le hc' hds (hJ.join_wf hc hes) fun a => hJ.le_join_of_le hc hes (hds a) a (h a).1,
    hJ.join_le hc hes (hJ.join_wf hc' hds) fun a => hJ.le_join_of_le hc' hds (hes a) a (h a).2⟩

/-- Transitivity of the equivalence `dle d₀ d₁ ∧ dle d₁ d₀` (snu-sf: the local
`deq_transitive` of section `ClassicOrd.REC`). -/
theorem equiv_trans {d₀ d₁ d₂ : D} (h₀ : wf d₀) (h₁ : wf d₁) (h₂ : wf d₂)
    (e₀ : dle d₀ d₁ ∧ dle d₁ d₀) (e₁ : dle d₁ d₂ ∧ dle d₂ d₁) : dle d₀ d₂ ∧ dle d₂ d₀ :=
  ⟨hJ.le_trans h₀ h₁ h₂ e₀.1 e₁.1, hJ.le_trans h₂ h₁ h₀ e₁.2 e₀.2⟩

end ChainJoinLaws

end Laws

/-! ## Recursion with joins of chains -/

namespace ChainRecLaws

section Rec

variable {D : Type v} {dle : D → D → Prop} {wf : D → Prop} {djoin : (A : Type u) → (A → D) → D}
  {base : D} {next : D → D} (h : ChainRecLaws dle wf djoin base next)
include h

/-- The four properties of `trec` that snu-sf `ClassicOrd.rec_all` shows together, by
well-founded induction. -/
private theorem trec_all (t : OTree.{u}) :
    (∀ s, s ≤ t → dle (trec base next djoin s) (trec base next djoin t)) ∧
      (∀ s, s < t → dle (next (trec base next djoin s)) (trec base next djoin t)) ∧
      wf (trec base next djoin t) ∧ dle base (trec base next djoin t) := by
  induction t using lt_wf.induction with
  | _ t ih =>
    obtain ⟨ι, f⟩ := t
    have hw : ∀ s, s < OTree.mk ι f → wf (trec base next djoin s) :=
      fun s hs => (ih s hs).2.2.1
    have hb : ∀ s, s < OTree.mk ι f → dle base (trec base next djoin s) :=
      fun s hs => (ih s hs).2.2.2
    -- Below `mk ι f`, `next ∘ trec` is monotone.
    have hnn : ∀ r s, r ≤ s → s < OTree.mk ι f →
        dle (next (trec base next djoin r)) (next (trec base next djoin s)) := by
      intro r s hrs hs
      have hr : r < OTree.mk ι f := OTree.lt_of_le_of_lt hrs hs
      rcases lt_or_equiv_of_le hrs with hlt | he
      · exact h.le_trans (h.next_wf (hw r hr)) (hw s hs) (h.next_wf (hw s hs))
          ((ih s hs).2.1 r hlt) (h.next_le (hw s hs))
      · exact h.next_congr (hw r hr) (hw s hs) ((ih s hs).1 r he.le) ((ih r hr).1 s he.ge)
    -- The families below `mk ι f` give chains.
    have hc : ∀ {κ : Type u} (g : κ → OTree.{u}), (∀ k, g k < OTree.mk ι f) →
        IsChain dle fun k => next (trec base next djoin (g k)) := by
      intro κ g hg k₀ k₁
      rcases le_total (g k₀) (g k₁) with hle | hle
      · exact .inl (hnn _ _ hle (hg k₁))
      · exact .inr (hnn _ _ hle (hg k₀))
    have hwn : ∀ {κ : Type u} (g : κ → OTree.{u}), (∀ k, g k < OTree.mk ι f) →
        ∀ k, wf (next (trec base next djoin (g k))) := fun g hg k => h.next_wf (hw _ (hg k))
    have hjw : ∀ {κ : Type u} (g : κ → OTree.{u}), (∀ k, g k < OTree.mk ι f) →
        wf (djoin κ fun k => next (trec base next djoin (g k))) :=
      fun g hg => h.join_wf (hc g hg) (hwn g hg)
    have hcb : ∀ {κ : Type u} (g : κ → OTree.{u}), (∀ k, g k < OTree.mk ι f) →
        dle base (djoin κ fun k => next (trec base next djoin (g k))) ∨
          dle (djoin κ fun k => next (trec base next djoin (g k))) base := by
      intro κ g hg
      refine (Classical.em (Nonempty κ)).elim (fun ⟨k⟩ => .inl ?_) (fun hne => .inr ?_)
      · have wk := hw _ (hg k)
        exact h.le_join_of_le (hc g hg) (hwn g hg) h.base_wf k
          (h.le_trans h.base_wf wk (h.next_wf wk) (hb _ (hg k)) (h.next_le wk))
      · exact h.join_le (hc g hg) (hwn g hg) h.base_wf fun k => (hne ⟨k⟩).elim
    -- The four properties at `mk ι f`.
    have hf : ∀ i, f i < OTree.mk ι f := child_lt (OTree.mk ι f)
    have wt : wf (trec base next djoin (OTree.mk ι f)) :=
      h.dunion_wf h.base_wf (hjw f hf) (hcb f hf)
    have hbt : dle base (trec base next djoin (OTree.mk ι f)) :=
      h.le_dunion_left h.base_wf (hjw f hf) (hcb f hf)
    have hlt : ∀ s, s < OTree.mk ι f →
        dle (next (trec base next djoin s)) (trec base next djoin (OTree.mk ι f)) := by
      intro s ⟨i, hi⟩
      have ws := h.next_wf (hw s ⟨i, hi⟩)
      exact h.le_trans ws (hjw f hf) wt
        (h.le_join_of_le (hc f hf) (hwn f hf) ws i (hnn s (f i) hi (hf i)))
        (h.le_dunion_right h.base_wf (hjw f hf) (hcb f hf))
    refine ⟨fun s hs => ?_, hlt, wt, hbt⟩
    obtain ⟨κ, g⟩ := s
    have hg : ∀ k, g k < OTree.mk ι f := mk_le.mp hs
    exact h.dunion_le h.base_wf (hjw g hg) wt (hcb g hg) hbt
      (h.join_le (hc g hg) (hwn g hg) wt fun k => hlt (g k) (hg k))

/-- `trec` is monotone (snu-sf: `ClassicOrd.le_rec`). -/
theorem trec_le_trec {s t : OTree.{u}} (hst : s ≤ t) :
    dle (trec base next djoin s) (trec base next djoin t) :=
  (trec_all h t).1 s hst

/-- `trec` respects `≈` (snu-sf: `ClassicOrd.eq_rec`). -/
theorem trec_congr {s t : OTree.{u}} (hst : s ≈ t) :
    dle (trec base next djoin s) (trec base next djoin t) ∧
      dle (trec base next djoin t) (trec base next djoin s) :=
  ⟨h.trec_le_trec hst.le, h.trec_le_trec hst.ge⟩

/-- snu-sf: `ClassicOrd.lt_rec`. -/
theorem next_trec_le_trec {s t : OTree.{u}} (hst : s < t) :
    dle (next (trec base next djoin s)) (trec base next djoin t) :=
  (trec_all h t).2.1 s hst

/-- snu-sf: `ClassicOrd.rec_le_base`. -/
theorem base_le_trec (t : OTree.{u}) : dle base (trec base next djoin t) :=
  (trec_all h t).2.2.2

/-- snu-sf: `ClassicOrd.rec_wf`. -/
theorem trec_wf (t : OTree.{u}) : wf (trec base next djoin t) :=
  (trec_all h t).2.2.1

theorem next_trec_wf (t : OTree.{u}) : wf (next (trec base next djoin t)) :=
  h.next_wf (h.trec_wf t)

/-- snu-sf: `ClassicOrd.rec_next_le`. -/
theorem next_trec_le_next_trec {s t : OTree.{u}} (hst : s ≤ t) :
    dle (next (trec base next djoin s)) (next (trec base next djoin t)) := by
  rcases lt_or_equiv_of_le hst with hlt | he
  · exact h.le_trans (h.next_trec_wf s) (h.trec_wf t) (h.next_trec_wf t)
      (h.next_trec_le_trec hlt) (h.next_le (h.trec_wf t))
  · exact h.next_congr (h.trec_wf s) (h.trec_wf t) (h.trec_congr he).1 (h.trec_congr he).2

/-- The values of `trec` on a family are a chain (snu-sf: the local `chain_helper` of section
`ClassicOrd.REC`). -/
theorem isChain_trec {ι : Type u} (f : ι → OTree.{u}) :
    IsChain dle fun i => trec base next djoin (f i) := fun i j =>
  (le_total (f i) (f j)).imp h.trec_le_trec h.trec_le_trec

/-- snu-sf: the local `chain_next_helper` of section `ClassicOrd.REC`. -/
theorem isChain_next_trec {ι : Type u} (f : ι → OTree.{u}) :
    IsChain dle fun i => next (trec base next djoin (f i)) := fun i j =>
  (le_total (f i) (f j)).imp h.next_trec_le_next_trec h.next_trec_le_next_trec

theorem join_trec_wf {ι : Type u} (f : ι → OTree.{u}) :
    wf (djoin ι fun i => trec base next djoin (f i)) :=
  h.join_wf (h.isChain_trec f) fun i => h.trec_wf (f i)

theorem join_next_trec_wf {ι : Type u} (f : ι → OTree.{u}) :
    wf (djoin ι fun i => next (trec base next djoin (f i))) :=
  h.join_wf (h.isChain_next_trec f) fun i => h.next_trec_wf (f i)

/-- snu-sf: the local `BASEJOIN` of section `ClassicOrd.REC`. -/
theorem base_le_join_trec_or {ι : Type u} (f : ι → OTree.{u}) :
    dle base (djoin ι fun i => trec base next djoin (f i)) ∨
      dle (djoin ι fun i => trec base next djoin (f i)) base := by
  refine (Classical.em (Nonempty ι)).elim (fun ⟨i⟩ => .inl ?_) (fun hne => .inr ?_)
  · exact h.le_join_of_le (h.isChain_trec f) (fun i => h.trec_wf (f i)) h.base_wf i
      (h.base_le_trec (f i))
  · exact h.join_le (h.isChain_trec f) (fun i => h.trec_wf (f i)) h.base_wf
      fun i => (hne ⟨i⟩).elim

/-- snu-sf: the local `BASENEXTJOIN` of section `ClassicOrd.REC`. -/
theorem base_le_join_next_trec_or {ι : Type u} (f : ι → OTree.{u}) :
    dle base (djoin ι fun i => next (trec base next djoin (f i))) ∨
      dle (djoin ι fun i => next (trec base next djoin (f i))) base := by
  refine (Classical.em (Nonempty ι)).elim (fun ⟨i⟩ => .inl ?_) (fun hne => .inr ?_)
  · exact h.le_join_of_le (h.isChain_next_trec f) (fun i => h.next_trec_wf (f i)) h.base_wf i
      (h.le_trans h.base_wf (h.trec_wf (f i)) (h.next_trec_wf (f i)) (h.base_le_trec (f i))
        (h.next_le (h.trec_wf (f i))))
  · exact h.join_le (h.isChain_next_trec f) (fun i => h.next_trec_wf (f i)) h.base_wf
      fun i => (hne ⟨i⟩).elim

/-- An upper bound of `trec` (as `OTree.orec_le`). -/
theorem trec_le {t : OTree.{u}} {d : D} (hd : wf d) (hb : dle base d)
    (hn : ∀ s, s < t → dle (next (trec base next djoin s)) d) :
    dle (trec base next djoin t) d := by
  cases t with
  | mk ι f =>
    exact h.dunion_le h.base_wf (h.join_next_trec_wf f) hd (h.base_le_join_next_trec_or f) hb
      (h.join_le (h.isChain_next_trec f) (fun i => h.next_trec_wf (f i)) hd
        fun i => hn (f i) (child_lt (OTree.mk ι f) i))

/-- snu-sf: `ClassicOrd.rec_O`. -/
theorem trec_zero :
    dle (trec base next djoin zero) base ∧ dle base (trec base next djoin zero) :=
  ⟨h.trec_le h.base_wf (h.le_refl h.base_wf) fun s hs => (not_lt_zero s hs).elim,
    h.base_le_trec zero⟩

/-- snu-sf: `ClassicOrd.rec_is_O`. -/
theorem trec_of_equiv_zero {t : OTree.{u}} (ht : t ≈ zero) :
    dle (trec base next djoin t) base ∧ dle base (trec base next djoin t) :=
  ⟨h.le_trans (h.trec_wf t) (h.trec_wf zero) h.base_wf (h.trec_le_trec ht.le) h.trec_zero.1,
    h.base_le_trec t⟩

/-- snu-sf: `ClassicOrd.rec_S`. -/
theorem trec_succ (t : OTree.{u}) :
    dle (trec base next djoin (succ t)) (next (trec base next djoin t)) ∧
      dle (next (trec base next djoin t)) (trec base next djoin (succ t)) :=
  ⟨h.trec_le (h.next_trec_wf t)
      (h.le_trans h.base_wf (h.trec_wf t) (h.next_trec_wf t) (h.base_le_trec t)
        (h.next_le (h.trec_wf t)))
      fun _ hs => h.next_trec_le_next_trec (lt_succ_iff.mp hs),
    h.next_trec_le_trec (lt_succ t)⟩

/-- snu-sf: `ClassicOrd.rec_is_S`. -/
theorem trec_of_equiv_succ {s t : OTree.{u}} (ht : t ≈ succ s) :
    dle (trec base next djoin t) (next (trec base next djoin s)) ∧
      dle (next (trec base next djoin s)) (trec base next djoin t) :=
  h.equiv_trans (h.trec_wf t) (h.trec_wf _) (h.next_trec_wf s) (h.trec_congr ht)
    (h.trec_succ s)

/-- `trec` on an open family with a member (snu-sf: `ClassicOrd.rec_build`). -/
theorem trec_mk_of_open {ι : Type u} [Nonempty ι] {f : ι → OTree.{u}}
    (hf : ∀ i, ∃ j, f i < f j) :
    dle (trec base next djoin (OTree.mk ι f)) (djoin ι fun i => trec base next djoin (f i)) ∧
      dle (djoin ι fun i => trec base next djoin (f i)) (trec base next djoin (OTree.mk ι f)) := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have wf' : ∀ i, wf (trec base next djoin (f i)) := fun i => h.trec_wf (f i)
  have hc := h.isChain_trec f
  have wj := h.join_trec_wf f
  refine ⟨h.trec_le wj (h.le_join_of_le hc wf' h.base_wf i₀ (h.base_le_trec _)) ?_, ?_⟩
  · intro s hs
    obtain ⟨i, hi⟩ := hs
    obtain ⟨j, hj⟩ := hf i
    exact h.le_join_of_le hc wf' (h.next_trec_wf s) j
      (h.next_trec_le_trec (OTree.lt_of_le_of_lt hi hj))
  · exact h.join_le hc wf' (h.trec_wf _) fun i =>
      h.trec_le_trec (OTree.le_of_lt (child_lt (OTree.mk ι f) i))

/-- snu-sf: `ClassicOrd.rec_join`. -/
theorem trec_sup {ι : Type u} (f : ι → OTree.{u}) :
    dle (trec base next djoin (sup f))
        (dunion djoin base (djoin ι fun i => trec base next djoin (f i))) ∧
      dle (dunion djoin base (djoin ι fun i => trec base next djoin (f i)))
        (trec base next djoin (sup f)) := by
  have wf' : ∀ i, wf (trec base next djoin (f i)) := fun i => h.trec_wf (f i)
  have hc := h.isChain_trec f
  have wj := h.join_trec_wf f
  have hcb := h.base_le_join_trec_or f
  have wu := h.dunion_wf h.base_wf wj hcb
  refine ⟨h.trec_le wu (h.le_dunion_left h.base_wf wj hcb) fun s hs => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := lt_sup_iff.mp hs
    exact h.le_trans (h.next_trec_wf s) wj wu
      (h.le_join_of_le hc wf' (h.next_trec_wf s) i (h.next_trec_le_trec hi))
      (h.le_dunion_right h.base_wf wj hcb)
  · exact h.dunion_le h.base_wf wj (h.trec_wf _) hcb (h.base_le_trec _)
      (h.join_le hc wf' (h.trec_wf _) fun i => h.trec_le_trec (le_sup f i))

/-- snu-sf: `ClassicOrd.rec_is_join`. -/
theorem trec_of_equiv_sup {ι : Type u} {f : ι → OTree.{u}} {t : OTree.{u}} (ht : t ≈ sup f) :
    dle (trec base next djoin t)
        (dunion djoin base (djoin ι fun i => trec base next djoin (f i))) ∧
      dle (dunion djoin base (djoin ι fun i => trec base next djoin (f i)))
        (trec base next djoin t) :=
  h.equiv_trans (h.trec_wf t) (h.trec_wf _)
    (h.dunion_wf h.base_wf (h.join_trec_wf f) (h.base_le_join_trec_or f)) (h.trec_congr ht)
    (h.trec_sup f)

/-- snu-sf: `ClassicOrd.rec_join_inhabited`. -/
theorem trec_sup_of_nonempty {ι : Type u} [Nonempty ι] (f : ι → OTree.{u}) :
    dle (trec base next djoin (sup f)) (djoin ι fun i => trec base next djoin (f i)) ∧
      dle (djoin ι fun i => trec base next djoin (f i)) (trec base next djoin (sup f)) := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have wf' : ∀ i, wf (trec base next djoin (f i)) := fun i => h.trec_wf (f i)
  have hc := h.isChain_trec f
  have wj := h.join_trec_wf f
  refine ⟨h.trec_le wj (h.le_join_of_le hc wf' h.base_wf i₀ (h.base_le_trec _))
    fun s hs => ?_, h.join_le hc wf' (h.trec_wf _) fun i => h.trec_le_trec (le_sup f i)⟩
  obtain ⟨i, hi⟩ := lt_sup_iff.mp hs
  exact h.le_join_of_le hc wf' (h.next_trec_wf s) i (h.next_trec_le_trec hi)

/-- snu-sf: `ClassicOrd.rec_is_join_inhabited`. -/
theorem trec_of_equiv_sup_of_nonempty {ι : Type u} [Nonempty ι] {f : ι → OTree.{u}}
    {t : OTree.{u}} (ht : t ≈ sup f) :
    dle (trec base next djoin t) (djoin ι fun i => trec base next djoin (f i)) ∧
      dle (djoin ι fun i => trec base next djoin (f i)) (trec base next djoin t) :=
  h.equiv_trans (h.trec_wf t) (h.trec_wf _) (h.join_trec_wf f) (h.trec_congr ht)
    (h.trec_sup_of_nonempty f)

/-- snu-sf: `ClassicOrd.rec_union`. -/
theorem trec_max (s t : OTree.{u}) :
    dle (trec base next djoin (max s t))
        (dunion djoin (trec base next djoin s) (trec base next djoin t)) ∧
      dle (dunion djoin (trec base next djoin s) (trec base next djoin t))
        (trec base next djoin (max s t)) := by
  have ws := h.trec_wf s
  have wt := h.trec_wf t
  have hst := (le_total s t).imp h.trec_le_trec h.trec_le_trec
  have wu := h.dunion_wf ws wt hst
  have ls := h.le_dunion_left ws wt hst
  have lt := h.le_dunion_right ws wt hst
  refine ⟨h.trec_le wu (h.le_trans h.base_wf ws wu (h.base_le_trec s) ls) fun r hr => ?_,
    h.dunion_le ws wt (h.trec_wf _) hst (h.trec_le_trec (le_max_left s t))
      (h.trec_le_trec (le_max_right s t))⟩
  rcases lt_max_iff.mp hr with hr | hr
  · exact h.le_trans (h.next_trec_wf r) ws wu (h.next_trec_le_trec hr) ls
  · exact h.le_trans (h.next_trec_wf r) wt wu (h.next_trec_le_trec hr) lt

/-- `trec` is the only function that satisfies its defining equation up to equivalence
(snu-sf: `ClassicOrd.rec_unique2`). -/
theorem trec_unique (F : OTree.{u} → D) (hw : ∀ t, wf (F t))
    (hF : ∀ (ι : Type u) (f : ι → OTree.{u}),
      dle (F (OTree.mk ι f)) (dunion djoin base (djoin ι fun i => next (F (f i)))) ∧
        dle (dunion djoin base (djoin ι fun i => next (F (f i)))) (F (OTree.mk ι f))) :
    ∀ t, dle (F t) (trec base next djoin t) ∧ dle (trec base next djoin t) (F t)
  | OTree.mk ι f => by
    have ih := fun i => trec_unique F hw hF (f i)
    have wF : ∀ i, wf (next (F (f i))) := fun i => h.next_wf (hw (f i))
    have wT : ∀ i, wf (next (trec base next djoin (f i))) := fun i => h.next_trec_wf (f i)
    have e : ∀ i, dle (next (F (f i))) (next (trec base next djoin (f i))) ∧
        dle (next (trec base next djoin (f i))) (next (F (f i))) := fun i =>
      ⟨h.next_congr (hw _) (h.trec_wf _) (ih i).1 (ih i).2,
        h.next_congr (h.trec_wf _) (hw _) (ih i).2 (ih i).1⟩
    have hc := h.isChain_next_trec f
    have hcF := h.isChain_of_equiv hc wF wT e
    have wjF := h.join_wf hcF wF
    have wjT := h.join_next_trec_wf f
    have hcb := h.base_le_join_next_trec_or f
    have ej := h.join_congr hc wF wT e
    -- The two `dunion` are equivalent.
    have hcbF : dle base (djoin ι fun i => next (F (f i))) ∨
        dle (djoin ι fun i => next (F (f i))) base :=
      hcb.imp (fun l => h.le_trans h.base_wf wjT wjF l ej.2)
        (fun l => h.le_trans wjF wjT h.base_wf ej.1 l)
    have wuF := h.dunion_wf h.base_wf wjF hcbF
    have wb := h.le_refl h.base_wf
    have eu : dle (dunion djoin base (djoin ι fun i => next (F (f i))))
          (trec base next djoin (OTree.mk ι f)) ∧
        dle (trec base next djoin (OTree.mk ι f))
          (dunion djoin base (djoin ι fun i => next (F (f i)))) :=
      ⟨h.dunion_le h.base_wf wjF (h.trec_wf _) hcbF (h.base_le_trec _)
          (h.le_trans wjF wjT (h.trec_wf _) ej.1 (h.le_dunion_right h.base_wf wjT hcb)),
        h.dunion_le h.base_wf wjT wuF hcb (h.le_dunion_left h.base_wf wjF hcbF)
          (h.le_trans wjT wjF wuF ej.2 (h.le_dunion_right h.base_wf wjF hcbF))⟩
    exact h.equiv_trans (hw _) wuF (h.trec_wf _) (hF ι f) eu

/-- `trec` is the only function that satisfies the equations of `trec_of_equiv_zero`,
`trec_of_equiv_succ` and `trec_of_equiv_sup_of_nonempty` up to equivalence
(snu-sf: `ClassicOrd.rec_unique`). -/
theorem trec_unique_of_zero_succ_limit (F : OTree.{u} → D) (hw : ∀ t, wf (F t))
    (hzero : ∀ t, t ≈ zero → dle (F t) base ∧ dle base (F t))
    (hsucc : ∀ s t, t ≈ succ s → dle (F t) (next (F s)) ∧ dle (next (F s)) (F t))
    (hlimit : ∀ (ι : Type u) (f : ι → OTree.{u}) (t : OTree.{u}), t ≈ sup f → Nonempty ι →
      (∀ i, ∃ j, f i < f j) →
      dle (F t) (djoin ι fun i => F (f i)) ∧ dle (djoin ι fun i => F (f i)) (F t))
    (t : OTree.{u}) : dle (F t) (trec base next djoin t) ∧ dle (trec base next djoin t) (F t) := by
  induction t using limitInduction with
  | zero t ht _ =>
    have e := h.trec_of_equiv_zero ht
    exact h.equiv_trans (hw t) h.base_wf (h.trec_wf t) (hzero t ht) ⟨e.2, e.1⟩
  | succ s t ht ih _ =>
    have e := h.trec_of_equiv_succ ht
    exact h.equiv_trans (hw t) (h.next_wf (hw s)) (h.trec_wf t) (hsucc s t ht)
      (h.equiv_trans (h.next_wf (hw s)) (h.next_trec_wf s) (h.trec_wf t)
        ⟨h.next_congr (hw s) (h.trec_wf s) ih.1 ih.2,
          h.next_congr (h.trec_wf s) (hw s) ih.2 ih.1⟩ ⟨e.2, e.1⟩)
  | limit ι f t ht hne ho ih _ =>
    have e := h.trec_of_equiv_sup_of_nonempty ht
    have wF : ∀ i, wf (F (f i)) := fun i => hw (f i)
    have wT : ∀ i, wf (trec base next djoin (f i)) := fun i => h.trec_wf (f i)
    have hcF := h.isChain_of_equiv (h.isChain_trec f) wF wT ih
    exact h.equiv_trans (hw t) (h.join_wf hcF wF) (h.trec_wf t) (hlimit ι f t ht hne ho)
      (h.equiv_trans (h.join_wf hcF wF) (h.join_trec_wf f) (h.trec_wf t)
        (h.join_congr (h.isChain_trec f) wF wT ih) ⟨e.2, e.1⟩)

/-- After a fixed point of `next`, `trec` stays at the fixed point
(snu-sf: `ClassicOrd.fixed_point_after`). The statement holds for all trees `t`, not only for
the trees `t` above `s`. -/
theorem trec_le_of_next_trec_le {s : OTree.{u}}
    (hs : dle (next (trec base next djoin s)) (trec base next djoin s)) (t : OTree.{u}) :
    dle (trec base next djoin t) (trec base next djoin s) := by
  induction t using lt_wf.induction with
  | _ t ih =>
    refine h.trec_le (h.trec_wf s) (h.base_le_trec s) fun r hr => ?_
    rcases le_or_lt s r with hsr | hrs
    · exact h.le_trans (h.next_trec_wf r) (h.next_trec_wf s) (h.trec_wf s)
        (h.next_congr (h.trec_wf r) (h.trec_wf s) (ih r hr) (h.trec_le_trec hsr)) hs
    · exact h.next_trec_le_trec hrs

end Rec

end ChainRecLaws

/-! ## The fixed-point theorem -/

section Fixed

variable {D : Type v} (dle : D → D → Prop) (djoin : (A : Type u) → (A → D) → D) (base : D)
  (next : D → D)

/-- The relation of the values of `trec` that increase strictly: `trec s` is related to `trec t`
if `s < t` and `trec t` is not below `trec s` (snu-sf: `ClassicOrd.strictly_increasing`). -/
def StrictlyIncreasing (d₀ d₁ : D) : Prop :=
  ∃ s t : OTree.{u}, s < t ∧ ¬dle (trec base next djoin t) (trec base next djoin s) ∧
    trec base next djoin s = d₀ ∧ trec base next djoin t = d₁

/-- `trec` increases strictly up to `t`: the value at `t` is not below the value at each tree
`s < t` (snu-sf: `ClassicOrd.not_fixed`). -/
def NotFixed (t : OTree.{u}) : Prop :=
  ∀ s, s < t → ¬dle (trec base next djoin t) (trec base next djoin s)

end Fixed

namespace ChainRecLaws

section Fixed

variable {D : Type v} {dle : D → D → Prop} {wf : D → Prop} {djoin : (A : Type u) → (A → D) → D}
  {base : D} {next : D → D} (h : ChainRecLaws dle wf djoin base next)
include h

/-- snu-sf: `ClassicOrd.strictly_increasing_well_founded`. -/
theorem strictlyIncreasing_wf : WellFounded (StrictlyIncreasing dle djoin base next) := by
  have key : ∀ t : OTree.{u}, Acc (StrictlyIncreasing dle djoin base next)
      (trec base next djoin t) := by
    intro t
    induction t using lt_wf.induction with
    | _ t ih =>
      refine ⟨_, fun d ⟨s, t', _, hn, hs, ht⟩ => hs ▸ ih s ?_⟩
      refine (le_or_lt t s).elim (fun hts => (hn ?_).elim) id
      rw [ht]
      exact h.trec_le_trec hts
  exact ⟨fun d => ⟨_, fun d' ⟨s, _, _, _, hs, _⟩ => hs ▸ key s⟩⟩

/-- If `trec` increases strictly up to `t`, then it increases strictly up to each `s ≤ t`
(snu-sf: the local `end_le_end` of section `ClassicOrd.REC`). -/
theorem notFixed_of_le {s t : OTree.{u}} (hst : s ≤ t) (ht : NotFixed dle djoin base next t) :
    NotFixed dle djoin base next s := fun r hr hle =>
  ht r (OTree.lt_of_lt_of_le hr hst) <| h.trec_le_of_next_trec_le
    (h.le_trans (h.next_trec_wf r) (h.trec_wf s) (h.trec_wf r) (h.next_trec_le_trec hr) hle) t

end Fixed

section Hartogs

variable {D : Type u} {dle : D → D → Prop} {wf : D → Prop} {djoin : (A : Type u) → (A → D) → D}
  {base : D} {next : D → D} (h : ChainRecLaws dle wf djoin base next)
include h

/-- If `trec` increases strictly up to `t`, then `t` is at most the tree of `trec t` in the
relation `StrictlyIncreasing` (snu-sf: the local `least_lt_incr_acc` of section
`ClassicOrd.REC`). -/
theorem le_ofWf_strictlyIncreasing :
    ∀ {t : OTree.{u}}, NotFixed dle djoin base next t →
      t ≤ ofWf h.strictlyIncreasing_wf (trec base next djoin t)
  | OTree.mk ι f, ht => mk_le.mpr fun i =>
    have hi : f i < OTree.mk ι f := child_lt (OTree.mk ι f) i
    OTree.lt_of_le_of_lt (le_ofWf_strictlyIncreasing (h.notFixed_of_le (OTree.le_of_lt hi) ht))
      (ofWf_lt_ofWf _ ⟨f i, OTree.mk ι f, hi, ht (f i) hi, rfl, rfl⟩)

/-- `trec` does not increase strictly up to the Hartogs ordinal of `D` (snu-sf: the local
`hartogs_fixed` of section `ClassicOrd.REC`). -/
theorem not_notFixed_hartogs : ¬NotFixed dle djoin base next (hartogs D) := fun ht =>
  OTree.lt_irrefl _ <| OTree.lt_of_le_of_lt (h.le_ofWf_strictlyIncreasing ht)
    (OTree.lt_trans (ofWf_lt_ofWfSet _ _) (ofWfSet_lt_hartogs h.strictlyIncreasing_wf))

/-- The fixed-point theorem: `trec` at the Hartogs ordinal of `D` is a fixed point of `next`
(snu-sf: `ClassicOrd._fixpoint_theorem`, `fixpoint_theorem_le`). With `next_le`, the two values
are equivalent (`Ordinals.Tree.Fixpoint`). -/
theorem next_trec_hartogs_le :
    dle (next (trec base next djoin (hartogs D))) (trec base next djoin (hartogs D)) := by
  refine Classical.byContradiction fun hn => h.not_notFixed_hartogs ?_
  refine h.notFixed_of_le (le_succ _) fun s hs hle => hn ?_
  have hs' := lt_succ_iff.mp hs
  exact h.le_trans (h.next_trec_wf _) (h.trec_wf _) (h.trec_wf _)
    (h.le_trans (h.next_trec_wf _) (h.trec_wf _) (h.trec_wf _) (h.trec_succ _).2 hle)
    (h.trec_le_trec hs')

end Hartogs

end ChainRecLaws

end OTree

end Ordinals
