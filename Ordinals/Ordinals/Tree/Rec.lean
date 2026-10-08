/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Tree.Constructions

/-!
# Transfinite recursion on trees

`trec base next djoin t` is the transfinite recursion along `t` into a type `D`:
`trec (mk ι f) = dunion base (djoin ι fun i => next (trec (f i)))`. `orec base next` is `trec`
into the trees, with `sup` as the join. The laws of `D` are hypotheses of the lemmas.

This file follows snu-sf/Ordinal (`src/Ordinal.v`, sections `REC`, `REC2`, `OREC`, `OREC2`).
snu-sf `Ord.rec` is `trec` here, because `OTree.rec` is the recursor of `OTree`.
-/

@[expose] public section

namespace Ordinals

universe u v

namespace OTree

/-! ## Laws of the target type -/

/-- The join laws of the target type of `trec`: `dle` is a preorder on the elements that
satisfy `wf`, and `djoin A ds` is a least upper bound of `ds` (snu-sf: hypotheses of `REC`). -/
structure JoinLaws {D : Type v} (dle : D → D → Prop) (wf : D → Prop)
    (djoin : (A : Type u) → (A → D) → D) : Prop where
  /-- snu-sf: `dle_reflexive`. -/
  le_refl : ∀ {d}, wf d → dle d d
  /-- snu-sf: `dle_transitive`. -/
  le_trans : ∀ {d₀ d₁ d₂}, wf d₀ → wf d₁ → wf d₂ → dle d₀ d₁ → dle d₁ d₂ → dle d₀ d₂
  /-- snu-sf: `djoin_upperbound`. -/
  le_join : ∀ {A : Type u} {ds : A → D}, (∀ a, wf (ds a)) → ∀ a, dle (ds a) (djoin A ds)
  /-- snu-sf: `djoin_supremum`. -/
  join_le : ∀ {A : Type u} {ds : A → D} {d : D}, (∀ a, wf (ds a)) → wf d →
    (∀ a, dle (ds a) d) → dle (djoin A ds) d
  /-- snu-sf: `djoin_wf`. -/
  join_wf : ∀ {A : Type u} {ds : A → D}, (∀ a, wf (ds a)) → wf (djoin A ds)

/-- `base` and `next` keep `wf` (snu-sf: hypotheses of `REC`). -/
structure StepLaws {D : Type v} (wf : D → Prop) (base : D) (next : D → D) : Prop where
  /-- snu-sf: `base_wf`. -/
  base_wf : wf base
  /-- snu-sf: `next_wf`. -/
  next_wf : ∀ {d}, wf d → wf (next d)

/-- `next` is monotone on the elements that satisfy `wf` (snu-sf: `next_mon`). -/
def NextMono {D : Type v} (dle : D → D → Prop) (wf : D → Prop) (next : D → D) : Prop :=
  ∀ {d₀ d₁}, wf d₀ → wf d₁ → dle d₀ d₁ → dle (next d₀) (next d₁)

/-- The binary join: the join of the family `true ↦ d₀`, `false ↦ d₁` (snu-sf: `dunion`). -/
def dunion {D : Type v} (djoin : (A : Type u) → (A → D) → D) (d₀ d₁ : D) : D :=
  djoin (ULift.{u} Bool) fun b => cond b.down d₀ d₁

/-- The two members of the family of `dunion` satisfy `wf`. -/
theorem cond_wf {D : Type v} {wf : D → Prop} {d₀ d₁ : D} (h₀ : wf d₀) (h₁ : wf d₁) :
    ∀ b : ULift.{u} Bool, wf (cond b.down d₀ d₁)
  | ⟨true⟩ => h₀
  | ⟨false⟩ => h₁

namespace JoinLaws

variable {D : Type v} {dle : D → D → Prop} {wf : D → Prop} {djoin : (A : Type u) → (A → D) → D}

theorem le_join_of_le (hJ : JoinLaws dle wf djoin) {A : Type u} {ds : A → D} {d : D}
    (hds : ∀ a, wf (ds a)) (hd : wf d) (a : A) (h : dle d (ds a)) : dle d (djoin A ds) :=
  hJ.le_trans hd (hds a) (hJ.join_wf hds) h (hJ.le_join hds a)

/-- snu-sf: `djoin_le` (`Arithmetic.v`). -/
theorem join_mono (hJ : JoinLaws dle wf djoin) {A : Type u} {f g : A → D}
    (hf : ∀ a, wf (f a)) (hg : ∀ a, wf (g a)) (h : ∀ a, dle (f a) (g a)) :
    dle (djoin A f) (djoin A g) :=
  hJ.join_le hf (hJ.join_wf hg) fun a => hJ.le_join_of_le hg (hf a) a (h a)

/-- snu-sf: `Ord.le_join` for `djoin`. -/
theorem join_le_join_of_forall_exists (hJ : JoinLaws dle wf djoin) {A B : Type u} {f : A → D}
    {g : B → D} (hf : ∀ a, wf (f a)) (hg : ∀ b, wf (g b)) (h : ∀ a, ∃ b, dle (f a) (g b)) :
    dle (djoin A f) (djoin B g) :=
  hJ.join_le hf (hJ.join_wf hg) fun a =>
    let ⟨b, hb⟩ := h a
    hJ.le_join_of_le hg (hf a) b hb

/-- snu-sf: `dunion_wf` (`Arithmetic.v`). -/
theorem dunion_wf (hJ : JoinLaws dle wf djoin) {d₀ d₁ : D} (h₀ : wf d₀) (h₁ : wf d₁) :
    wf (dunion djoin d₀ d₁) :=
  hJ.join_wf (cond_wf h₀ h₁)

/-- snu-sf: `dunion_l` (`Arithmetic.v`). -/
theorem le_dunion_left (hJ : JoinLaws dle wf djoin) {d₀ d₁ : D} (h₀ : wf d₀) (h₁ : wf d₁) :
    dle d₀ (dunion djoin d₀ d₁) :=
  hJ.le_join (cond_wf h₀ h₁) ⟨true⟩

/-- snu-sf: `dunion_r` (`Arithmetic.v`). -/
theorem le_dunion_right (hJ : JoinLaws dle wf djoin) {d₀ d₁ : D} (h₀ : wf d₀) (h₁ : wf d₁) :
    dle d₁ (dunion djoin d₀ d₁) :=
  hJ.le_join (cond_wf h₀ h₁) ⟨false⟩

/-- snu-sf: `dunion_supremum` (`Arithmetic.v`). -/
theorem dunion_le (hJ : JoinLaws dle wf djoin) {d₀ d₁ d : D} (h₀ : wf d₀) (h₁ : wf d₁)
    (hd : wf d) (l₀ : dle d₀ d) (l₁ : dle d₁ d) : dle (dunion djoin d₀ d₁) d :=
  hJ.join_le (cond_wf h₀ h₁) hd fun
    | ⟨true⟩ => l₀
    | ⟨false⟩ => l₁

/-- snu-sf: `dunion_le` (`Arithmetic.v`). -/
theorem dunion_mono (hJ : JoinLaws dle wf djoin) {d₀ d₁ e₀ e₁ : D} (h₀ : wf d₀) (h₁ : wf d₁)
    (k₀ : wf e₀) (k₁ : wf e₁) (l₀ : dle d₀ e₀) (l₁ : dle d₁ e₁) :
    dle (dunion djoin d₀ d₁) (dunion djoin e₀ e₁) :=
  hJ.join_mono (cond_wf h₀ h₁) (cond_wf k₀ k₁) fun
    | ⟨true⟩ => l₀
    | ⟨false⟩ => l₁

/-- snu-sf: `deq_transitive` (`Arithmetic.v`). -/
theorem equiv_trans (hJ : JoinLaws dle wf djoin) {d₀ d₁ d₂ : D} (h₀ : wf d₀) (h₁ : wf d₁)
    (h₂ : wf d₂) (e₀ : dle d₀ d₁ ∧ dle d₁ d₀) (e₁ : dle d₁ d₂ ∧ dle d₂ d₁) :
    dle d₀ d₂ ∧ dle d₂ d₀ :=
  ⟨hJ.le_trans h₀ h₁ h₂ e₀.1 e₁.1, hJ.le_trans h₂ h₁ h₀ e₁.2 e₀.2⟩

/-- snu-sf: `djoin_eq` (`Arithmetic.v`). -/
theorem join_congr (hJ : JoinLaws dle wf djoin) {A : Type u} {f g : A → D}
    (hf : ∀ a, wf (f a)) (hg : ∀ a, wf (g a)) (h : ∀ a, dle (f a) (g a) ∧ dle (g a) (f a)) :
    dle (djoin A f) (djoin A g) ∧ dle (djoin A g) (djoin A f) :=
  ⟨hJ.join_mono hf hg fun a => (h a).1, hJ.join_mono hg hf fun a => (h a).2⟩

/-- snu-sf: `dunion_eq` (`Arithmetic.v`). -/
theorem dunion_congr (hJ : JoinLaws dle wf djoin) {d₀ d₁ e₀ e₁ : D} (h₀ : wf d₀) (h₁ : wf d₁)
    (k₀ : wf e₀) (k₁ : wf e₁) (l₀ : dle d₀ e₀ ∧ dle e₀ d₀) (l₁ : dle d₁ e₁ ∧ dle e₁ d₁) :
    dle (dunion djoin d₀ d₁) (dunion djoin e₀ e₁) ∧
      dle (dunion djoin e₀ e₁) (dunion djoin d₀ d₁) :=
  ⟨hJ.dunion_mono h₀ h₁ k₀ k₁ l₀.1 l₁.1, hJ.dunion_mono k₀ k₁ h₀ h₁ l₀.2 l₁.2⟩

end JoinLaws

/-! ## Transfinite recursion -/

theorem max_equiv_sup_cond (s t : OTree.{u}) :
    max s t ≈ sup fun b : ULift.{u} Bool => cond b.down s t :=
  ⟨max_le (le_sup (fun b : ULift.{u} Bool => cond b.down s t) ⟨true⟩)
      (le_sup (fun b : ULift.{u} Bool => cond b.down s t) ⟨false⟩),
    sup_le fun
      | ⟨true⟩ => le_max_left s t
      | ⟨false⟩ => le_max_right s t⟩

/-- Transfinite recursion along a tree into `D`: start at `base`, apply `next` at each successor
step, and take joins at each node (snu-sf: `Ord.rec`). -/
def trec {D : Type v} (base : D) (next : D → D) (djoin : (A : Type u) → (A → D) → D) :
    OTree.{u} → D
  | mk ι f => dunion djoin base (djoin ι fun i => next (trec base next djoin (f i)))

section Trec

variable {D : Type v} {dle : D → D → Prop} {wf : D → Prop} {djoin : (A : Type u) → (A → D) → D}
  {base : D} {next : D → D}

/-- The defining equation of `trec` (snu-sf: `Ord.rec_red`). -/
theorem trec_mk (ι : Type u) (f : ι → OTree.{u}) :
    trec base next djoin (mk ι f) =
      dunion djoin base (djoin ι fun i => next (trec base next djoin (f i))) :=
  rfl

variable (hJ : JoinLaws dle wf djoin) (hS : StepLaws wf base next)

include hJ hS in
/-- snu-sf: `Ord.rec_wf`. -/
theorem trec_wf : ∀ t : OTree.{u}, wf (trec base next djoin t)
  | mk _ f => hJ.dunion_wf hS.base_wf (hJ.join_wf fun i => hS.next_wf (trec_wf (f i)))

include hJ hS in
theorem next_trec_wf (t : OTree.{u}) : wf (next (trec base next djoin t)) :=
  hS.next_wf (trec_wf hJ hS t)

include hJ hS in
theorem join_next_trec_wf {ι : Type u} (f : ι → OTree.{u}) :
    wf (djoin ι fun i => next (trec base next djoin (f i))) :=
  hJ.join_wf fun i => next_trec_wf hJ hS (f i)

include hJ hS in
/-- snu-sf: `Ord.rec_le_base`. -/
theorem base_le_trec (t : OTree.{u}) : dle base (trec base next djoin t) := by
  cases t with
  | mk ι f => exact hJ.le_dunion_left hS.base_wf (join_next_trec_wf hJ hS f)

include hJ hS in
/-- snu-sf: `Ord.rec_O`. -/
theorem trec_zero :
    dle (trec base next djoin zero) base ∧ dle base (trec base next djoin zero) :=
  ⟨hJ.dunion_le hS.base_wf (join_next_trec_wf hJ hS _) hS.base_wf (hJ.le_refl hS.base_wf)
      (hJ.join_le (fun e => e.elim) hS.base_wf fun e => e.elim),
    base_le_trec hJ hS zero⟩

variable (hm : NextMono dle wf next)

include hJ hS hm in
/-- `trec` is monotone (snu-sf: `Ord.le_rec`). -/
theorem trec_le_trec :
    ∀ {s t : OTree.{u}}, s ≤ t → dle (trec base next djoin s) (trec base next djoin t)
  | mk ι f, mk κ g, h => by
    have wt := trec_wf hJ hS (mk κ g)
    have wg := join_next_trec_wf hJ hS g
    refine hJ.dunion_le hS.base_wf (join_next_trec_wf hJ hS f) wt (base_le_trec hJ hS _) ?_
    refine hJ.join_le (fun i => next_trec_wf hJ hS (f i)) wt fun i => ?_
    obtain ⟨j, hj⟩ := h i
    refine hJ.le_trans (next_trec_wf hJ hS (f i)) wg wt ?_ (hJ.le_dunion_right hS.base_wf wg)
    exact hJ.le_join_of_le (fun j => next_trec_wf hJ hS (g j)) (next_trec_wf hJ hS (f i)) j
      (hm (trec_wf hJ hS _) (trec_wf hJ hS _) (trec_le_trec hj))

include hJ hS hm in
/-- `trec` respects `≈` (snu-sf: `Ord.eq_rec`). -/
theorem trec_congr {s t : OTree.{u}} (h : s ≈ t) :
    dle (trec base next djoin s) (trec base next djoin t) ∧
      dle (trec base next djoin t) (trec base next djoin s) :=
  ⟨trec_le_trec hJ hS hm h.le, trec_le_trec hJ hS hm h.ge⟩

include hJ hS hm in
/-- snu-sf: `Ord.lt_rec`. -/
theorem next_trec_le_trec {s t : OTree.{u}} (h : s < t) :
    dle (next (trec base next djoin s)) (trec base next djoin t) := by
  cases t with
  | mk κ g =>
    obtain ⟨j, hj⟩ := h
    have wg := join_next_trec_wf hJ hS g
    refine hJ.le_trans (next_trec_wf hJ hS s) wg (trec_wf hJ hS _) ?_
      (hJ.le_dunion_right hS.base_wf wg)
    exact hJ.le_join_of_le (fun j => next_trec_wf hJ hS (g j)) (next_trec_wf hJ hS s) j
      (hm (trec_wf hJ hS _) (trec_wf hJ hS _) (trec_le_trec hJ hS hm hj))

include hJ hS hm in
/-- snu-sf: `Ord.rec_next_le`. -/
theorem next_trec_le_next_trec {s t : OTree.{u}} (h : s ≤ t) :
    dle (next (trec base next djoin s)) (next (trec base next djoin t)) :=
  hm (trec_wf hJ hS s) (trec_wf hJ hS t) (trec_le_trec hJ hS hm h)

include hJ hS hm in
/-- snu-sf: `Ord.rec_is_O`. -/
theorem trec_of_equiv_zero {t : OTree.{u}} (h : t ≈ zero) :
    dle (trec base next djoin t) base ∧ dle base (trec base next djoin t) :=
  ⟨hJ.le_trans (trec_wf hJ hS t) (trec_wf hJ hS zero) hS.base_wf
      (trec_le_trec hJ hS hm h.le) (trec_zero hJ hS).1,
    base_le_trec hJ hS t⟩

include hJ hS in
/-- snu-sf: `Ord.rec_S`. -/
theorem trec_succ (hl : ∀ {d}, wf d → dle d (next d)) (t : OTree.{u}) :
    dle (trec base next djoin (succ t)) (next (trec base next djoin t)) ∧
      dle (next (trec base next djoin t)) (trec base next djoin (succ t)) := by
  have wt := trec_wf hJ hS t
  have wn := next_trec_wf hJ hS t
  have wj : wf (djoin PUnit fun _ => next (trec base next djoin t)) := hJ.join_wf fun _ => wn
  refine ⟨?_, ?_⟩
  · refine hJ.dunion_le hS.base_wf wj wn ?_ ?_
    · exact hJ.le_trans hS.base_wf wt wn (base_le_trec hJ hS t) (hl wt)
    · exact hJ.join_le (fun _ => wn) wn fun _ => hJ.le_refl wn
  · exact hJ.le_trans wn wj (trec_wf hJ hS _) (hJ.le_join (fun _ => wn) ⟨⟩)
      (hJ.le_dunion_right hS.base_wf wj)

include hJ hS hm in
/-- snu-sf: `Ord.rec_is_S`. -/
theorem trec_of_equiv_succ (hl : ∀ {d}, wf d → dle d (next d)) {s t : OTree.{u}}
    (h : t ≈ succ s) :
    dle (trec base next djoin t) (next (trec base next djoin s)) ∧
      dle (next (trec base next djoin s)) (trec base next djoin t) :=
  ⟨hJ.le_trans (trec_wf hJ hS t) (trec_wf hJ hS _) (next_trec_wf hJ hS s)
      (trec_le_trec hJ hS hm h.le) (trec_succ hJ hS hl s).1,
    hJ.le_trans (next_trec_wf hJ hS s) (trec_wf hJ hS _) (trec_wf hJ hS t)
      (trec_succ hJ hS hl s).2 (trec_le_trec hJ hS hm h.ge)⟩

include hJ hS hm in
/-- `trec` on a nonempty open family, where each member is below another member
(snu-sf: `Ord.rec_build`). -/
theorem trec_mk_of_open (hl : ∀ {d}, wf d → dle d (next d)) {ι : Type u} [Nonempty ι]
    {f : ι → OTree.{u}} (hf : ∀ i, ∃ j, f i < f j) :
    dle (trec base next djoin (mk ι f)) (djoin ι fun i => trec base next djoin (f i)) ∧
      dle (djoin ι fun i => trec base next djoin (f i)) (trec base next djoin (mk ι f)) := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have wf' : ∀ i, wf (trec base next djoin (f i)) := fun i => trec_wf hJ hS (f i)
  have wj := hJ.join_wf wf'
  have wn := join_next_trec_wf hJ hS f
  refine ⟨?_, ?_⟩
  · refine hJ.dunion_le hS.base_wf wn wj ?_ ?_
    · exact hJ.le_join_of_le wf' hS.base_wf i₀ (base_le_trec hJ hS _)
    · refine hJ.join_le (fun i => next_trec_wf hJ hS (f i)) wj fun i => ?_
      obtain ⟨j, hj⟩ := hf i
      exact hJ.le_join_of_le wf' (next_trec_wf hJ hS (f i)) j (next_trec_le_trec hJ hS hm hj)
  · refine hJ.join_le wf' (trec_wf hJ hS _) fun i => ?_
    refine hJ.le_trans (wf' i) wn (trec_wf hJ hS _) ?_ (hJ.le_dunion_right hS.base_wf wn)
    exact hJ.le_join_of_le (fun i => next_trec_wf hJ hS (f i)) (wf' i) i (hl (wf' i))

include hJ hS hm in
/-- snu-sf: `Ord.rec_join`. -/
theorem trec_sup {ι : Type u} (f : ι → OTree.{u}) :
    dle (trec base next djoin (sup f))
        (dunion djoin base (djoin ι fun i => trec base next djoin (f i))) ∧
      dle (dunion djoin base (djoin ι fun i => trec base next djoin (f i)))
        (trec base next djoin (sup f)) := by
  have wf' : ∀ i, wf (trec base next djoin (f i)) := fun i => trec_wf hJ hS (f i)
  have wj := hJ.join_wf wf'
  have wu := hJ.dunion_wf hS.base_wf wj
  refine ⟨?_, ?_⟩
  · refine hJ.dunion_le hS.base_wf (join_next_trec_wf hJ hS _) wu
      (hJ.le_dunion_left hS.base_wf wj) ?_
    refine hJ.join_le (fun p => next_trec_wf hJ hS _) wu fun ⟨i, k⟩ => ?_
    refine hJ.le_trans (next_trec_wf hJ hS _) wj wu ?_ (hJ.le_dunion_right hS.base_wf wj)
    exact hJ.le_join_of_le wf' (next_trec_wf hJ hS _) i
      (next_trec_le_trec hJ hS hm (child_lt (f i) k))
  · refine hJ.dunion_le hS.base_wf wj (trec_wf hJ hS _) (base_le_trec hJ hS _) ?_
    exact hJ.join_le wf' (trec_wf hJ hS _) fun i => trec_le_trec hJ hS hm (le_sup f i)

include hJ hS hm in
/-- snu-sf: `Ord.rec_join_inhabited`. -/
theorem trec_sup_of_nonempty {ι : Type u} [Nonempty ι] (f : ι → OTree.{u}) :
    dle (trec base next djoin (sup f)) (djoin ι fun i => trec base next djoin (f i)) ∧
      dle (djoin ι fun i => trec base next djoin (f i)) (trec base next djoin (sup f)) := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have wf' : ∀ i, wf (trec base next djoin (f i)) := fun i => trec_wf hJ hS (f i)
  have wj := hJ.join_wf wf'
  have wu := hJ.dunion_wf hS.base_wf wj
  have h := trec_sup hJ hS hm f
  refine ⟨hJ.le_trans (trec_wf hJ hS _) wu wj h.1 ?_,
    hJ.le_trans wj wu (trec_wf hJ hS _) (hJ.le_dunion_right hS.base_wf wj) h.2⟩
  exact hJ.dunion_le hS.base_wf wj wj
    (hJ.le_join_of_le wf' hS.base_wf i₀ (base_le_trec hJ hS _)) (hJ.le_refl wj)

include hJ hS hm in
/-- snu-sf: `Ord.rec_is_join`. -/
theorem trec_of_equiv_sup {ι : Type u} {f : ι → OTree.{u}} {t : OTree.{u}} (h : t ≈ sup f) :
    dle (trec base next djoin t)
        (dunion djoin base (djoin ι fun i => trec base next djoin (f i))) ∧
      dle (dunion djoin base (djoin ι fun i => trec base next djoin (f i)))
        (trec base next djoin t) := by
  have wu := hJ.dunion_wf hS.base_wf (hJ.join_wf fun i => trec_wf hJ hS (f i))
  have h' := trec_sup hJ hS hm f
  exact ⟨hJ.le_trans (trec_wf hJ hS _) (trec_wf hJ hS _) wu (trec_le_trec hJ hS hm h.le) h'.1,
    hJ.le_trans wu (trec_wf hJ hS _) (trec_wf hJ hS _) h'.2 (trec_le_trec hJ hS hm h.ge)⟩

include hJ hS hm in
/-- snu-sf: `Ord.rec_is_join_inhabited`. -/
theorem trec_of_equiv_sup_of_nonempty {ι : Type u} [Nonempty ι] {f : ι → OTree.{u}}
    {t : OTree.{u}} (h : t ≈ sup f) :
    dle (trec base next djoin t) (djoin ι fun i => trec base next djoin (f i)) ∧
      dle (djoin ι fun i => trec base next djoin (f i)) (trec base next djoin t) := by
  have wj := hJ.join_wf fun i => trec_wf hJ hS (f i)
  have h' := trec_sup_of_nonempty hJ hS hm f
  exact ⟨hJ.le_trans (trec_wf hJ hS _) (trec_wf hJ hS _) wj (trec_le_trec hJ hS hm h.le) h'.1,
    hJ.le_trans wj (trec_wf hJ hS _) (trec_wf hJ hS _) h'.2 (trec_le_trec hJ hS hm h.ge)⟩

include hJ hS hm in
/-- snu-sf: `Ord.rec_union`. -/
theorem trec_max (s t : OTree.{u}) :
    dle (trec base next djoin (max s t))
        (dunion djoin (trec base next djoin s) (trec base next djoin t)) ∧
      dle (dunion djoin (trec base next djoin s) (trec base next djoin t))
        (trec base next djoin (max s t)) := by
  have wc := cond_wf (trec_wf hJ hS s) (trec_wf hJ hS t)
  have wu := hJ.join_wf wc
  have wf' : ∀ b : ULift.{u} Bool, wf (trec base next djoin (cond b.down s t)) :=
    fun b => trec_wf hJ hS _
  have wj := hJ.join_wf wf'
  have h := trec_of_equiv_sup_of_nonempty hJ hS hm (max_equiv_sup_cond s t)
  have e : ∀ b : ULift.{u} Bool,
      dle (trec base next djoin (cond b.down s t))
        (cond b.down (trec base next djoin s) (trec base next djoin t)) ∧
      dle (cond b.down (trec base next djoin s) (trec base next djoin t))
        (trec base next djoin (cond b.down s t))
    | ⟨true⟩ => ⟨hJ.le_refl (trec_wf hJ hS s), hJ.le_refl (trec_wf hJ hS s)⟩
    | ⟨false⟩ => ⟨hJ.le_refl (trec_wf hJ hS t), hJ.le_refl (trec_wf hJ hS t)⟩
  exact ⟨hJ.le_trans (trec_wf hJ hS _) wj wu h.1 (hJ.join_mono wf' wc fun b => (e b).1),
    hJ.le_trans wu wj (trec_wf hJ hS _) (hJ.join_mono wc wf' fun b => (e b).2) h.2⟩

include hJ hS hm in
/-- `trec` is the only function that satisfies its defining equation up to equivalence
(snu-sf: `Ord.rec_unique`). -/
theorem trec_unique (F : OTree.{u} → D) (hw : ∀ t, wf (F t))
    (hF : ∀ (ι : Type u) (f : ι → OTree.{u}),
      dle (F (mk ι f)) (dunion djoin base (djoin ι fun i => next (F (f i)))) ∧
        dle (dunion djoin base (djoin ι fun i => next (F (f i)))) (F (mk ι f))) :
    ∀ t, dle (F t) (trec base next djoin t) ∧ dle (trec base next djoin t) (F t)
  | mk ι f => by
    have ih := fun i => trec_unique F hw hF (f i)
    have wF : ∀ i, wf (next (F (f i))) := fun i => hS.next_wf (hw (f i))
    have wT : ∀ i, wf (next (trec base next djoin (f i))) := fun i => next_trec_wf hJ hS (f i)
    have wu := hJ.dunion_wf hS.base_wf (hJ.join_wf wF)
    have wb := hJ.le_refl hS.base_wf
    exact ⟨hJ.le_trans (hw _) wu (trec_wf hJ hS _) (hF ι f).1
        (hJ.dunion_mono hS.base_wf (hJ.join_wf wF) hS.base_wf (hJ.join_wf wT) wb
          (hJ.join_mono wF wT fun i => hm (hw _) (trec_wf hJ hS _) (ih i).1)),
      hJ.le_trans (trec_wf hJ hS _) wu (hw _)
        (hJ.dunion_mono hS.base_wf (hJ.join_wf wT) hS.base_wf (hJ.join_wf wF) wb
          (hJ.join_mono wT wF fun i => hm (trec_wf hJ hS _) (hw _) (ih i).2))
        (hF ι f).2⟩

end Trec

/-- `trec` is monotone in `base` and `next` (snu-sf: `Ord.rec_mon`). -/
theorem trec_mono {D : Type v} {dle : D → D → Prop} {wf : D → Prop}
    {djoin : (A : Type u) → (A → D) → D} {base₀ base₁ : D} {next₀ next₁ : D → D}
    (hJ : JoinLaws dle wf djoin) (hS₀ : StepLaws wf base₀ next₀) (hS₁ : StepLaws wf base₁ next₁)
    (hb : dle base₀ base₁)
    (hn : ∀ {d₀ d₁}, wf d₀ → wf d₁ → dle d₀ d₁ → dle (next₀ d₀) (next₁ d₁)) :
    ∀ t : OTree.{u}, dle (trec base₀ next₀ djoin t) (trec base₁ next₁ djoin t)
  | mk _ f =>
    hJ.dunion_mono hS₀.base_wf (join_next_trec_wf hJ hS₀ f) hS₁.base_wf
      (join_next_trec_wf hJ hS₁ f) hb
      (hJ.join_mono (fun i => next_trec_wf hJ hS₀ (f i)) (fun i => next_trec_wf hJ hS₁ (f i))
        fun i => hn (trec_wf hJ hS₀ _) (trec_wf hJ hS₁ _) (trec_mono hJ hS₀ hS₁ hb hn (f i)))

/-! ## Recursion into the trees -/

/-- `sup` is a join on the trees, with `wf` always true. -/
theorem sup_joinLaws : JoinLaws (D := OTree.{u}) (· ≤ ·) (fun _ => True) fun _ => sup :=
  ⟨fun _ => OTree.le_rfl, fun _ _ _ => OTree.le_trans, fun _ a => le_sup _ a,
    fun _ _ h => sup_le h, fun _ => trivial⟩

theorem stepLaws_true (base : OTree.{u}) (next : OTree.{u} → OTree.{u}) :
    StepLaws (fun _ : OTree.{u} => True) base next :=
  ⟨trivial, fun _ => trivial⟩

theorem nextMono_of_mono {next : OTree.{u} → OTree.{u}}
    (hm : ∀ {s t : OTree.{u}}, s ≤ t → next s ≤ next t) :
    NextMono (· ≤ ·) (fun _ : OTree.{u} => True) next :=
  fun _ _ h => hm h

theorem dunion_sup_equiv_max (s t : OTree.{u}) : dunion (fun _ => sup) s t ≈ max s t :=
  (max_equiv_sup_cond s t).symm

/-- Transfinite recursion into the trees, with `sup` as the join (snu-sf: `Ord.orec`). -/
def orec (base : OTree.{u}) (next : OTree.{u} → OTree.{u}) : OTree.{u} → OTree.{u} :=
  trec base next fun _ => sup

section Orec

variable {base : OTree.{u}} {next : OTree.{u} → OTree.{u}}

/-- snu-sf: `Ord.orec_build`. -/
theorem orec_mk (ι : Type u) (f : ι → OTree.{u}) :
    orec base next (mk ι f) ≈ max base (sup fun i => next (orec base next (f i))) :=
  dunion_sup_equiv_max _ _

/-- snu-sf: `Ord.orec_le_base`. -/
theorem base_le_orec (t : OTree.{u}) : base ≤ orec base next t :=
  base_le_trec sup_joinLaws (stepLaws_true base next) t

/-- An upper bound of `orec` (snu-sf: `Ord.orec_build_supremum`). -/
theorem orec_le {t r : OTree.{u}} (hb : base ≤ r)
    (h : ∀ s, s < t → next (orec base next s) ≤ r) : orec base next t ≤ r := by
  cases t with
  | mk ι f =>
    exact OTree.le_trans (orec_mk ι f).le
      (max_le hb (sup_le fun i => h (f i) (child_lt (mk ι f) i)))

/-- snu-sf: `Ord.orec_O`. -/
theorem orec_zero : orec base next zero ≈ base :=
  trec_zero sup_joinLaws (stepLaws_true base next)

/-- snu-sf: `Ord.orec_S`. -/
theorem orec_succ (hl : ∀ s, s ≤ next s) (t : OTree.{u}) :
    orec base next (succ t) ≈ next (orec base next t) :=
  trec_succ sup_joinLaws (stepLaws_true base next) (fun _ => hl _) t

variable (hm : ∀ {s t : OTree.{u}}, s ≤ t → next s ≤ next t)

include hm in
/-- `orec` is monotone (snu-sf: `Ord.le_orec`). -/
theorem orec_le_orec {s t : OTree.{u}} (h : s ≤ t) : orec base next s ≤ orec base next t :=
  trec_le_trec sup_joinLaws (stepLaws_true base next) (nextMono_of_mono hm) h

include hm in
/-- `orec` respects `≈` (snu-sf: `Ord.eq_orec`). -/
theorem orec_congr {s t : OTree.{u}} (h : s ≈ t) : orec base next s ≈ orec base next t :=
  trec_congr sup_joinLaws (stepLaws_true base next) (nextMono_of_mono hm) h

include hm in
/-- snu-sf: `Ord.lt_rec` for `orec`. -/
theorem next_orec_le_orec {s t : OTree.{u}} (h : s < t) :
    next (orec base next s) ≤ orec base next t :=
  next_trec_le_trec sup_joinLaws (stepLaws_true base next) (nextMono_of_mono hm) h

include hm in
/-- snu-sf: `Ord.orec_is_O`. -/
theorem orec_of_equiv_zero {t : OTree.{u}} (h : t ≈ zero) : orec base next t ≈ base :=
  trec_of_equiv_zero sup_joinLaws (stepLaws_true base next) (nextMono_of_mono hm) h

include hm in
/-- snu-sf: `Ord.orec_is_S`. -/
theorem orec_of_equiv_succ (hl : ∀ s, s ≤ next s) {s t : OTree.{u}} (h : t ≈ succ s) :
    orec base next t ≈ next (orec base next s) :=
  trec_of_equiv_succ sup_joinLaws (stepLaws_true base next) (nextMono_of_mono hm)
    (fun _ => hl _) h

include hm in
/-- snu-sf: `Ord.orec_join`. -/
theorem orec_sup {ι : Type u} (f : ι → OTree.{u}) :
    orec base next (sup f) ≈ max base (sup fun i => orec base next (f i)) :=
  Equiv.trans (trec_sup sup_joinLaws (stepLaws_true base next) (nextMono_of_mono hm) f)
    (dunion_sup_equiv_max _ _)

include hm in
/-- snu-sf: `Ord.orec_join_inhabited`. -/
theorem orec_sup_of_nonempty {ι : Type u} [Nonempty ι] (f : ι → OTree.{u}) :
    orec base next (sup f) ≈ sup fun i => orec base next (f i) :=
  trec_sup_of_nonempty sup_joinLaws (stepLaws_true base next) (nextMono_of_mono hm) f

include hm in
/-- snu-sf: `Ord.orec_is_join`. -/
theorem orec_of_equiv_sup {ι : Type u} {f : ι → OTree.{u}} {t : OTree.{u}} (h : t ≈ sup f) :
    orec base next t ≈ max base (sup fun i => orec base next (f i)) :=
  Equiv.trans (orec_congr hm h) (orec_sup hm f)

include hm in
/-- snu-sf: `Ord.orec_is_join_inhabited`. -/
theorem orec_of_equiv_sup_of_nonempty {ι : Type u} [Nonempty ι] {f : ι → OTree.{u}}
    {t : OTree.{u}} (h : t ≈ sup f) : orec base next t ≈ sup fun i => orec base next (f i) :=
  Equiv.trans (orec_congr hm h) (orec_sup_of_nonempty hm f)

include hm in
/-- `orec` on a nonempty open family (snu-sf: `Ord.rec_build` for `orec`). -/
theorem orec_mk_of_open (hl : ∀ s, s ≤ next s) {ι : Type u} [Nonempty ι]
    {f : ι → OTree.{u}} (hf : ∀ i, ∃ j, f i < f j) :
    orec base next (mk ι f) ≈ sup fun i => orec base next (f i) :=
  trec_mk_of_open sup_joinLaws (stepLaws_true base next) (nextMono_of_mono hm)
    (fun _ => hl _) hf

include hm in
/-- snu-sf: `Ord.orec_union`. -/
theorem orec_max (s t : OTree.{u}) :
    orec base next (max s t) ≈ max (orec base next s) (orec base next t) :=
  Equiv.trans (trec_max sup_joinLaws (stepLaws_true base next) (nextMono_of_mono hm) s t)
    (dunion_sup_equiv_max _ _)

include hm in
/-- `orec` is the only function that satisfies its defining equation up to `≈`
(snu-sf: `Ord.orec_unique`). -/
theorem orec_unique (F : OTree.{u} → OTree.{u})
    (hF : ∀ (ι : Type u) (f : ι → OTree.{u}),
      F (mk ι f) ≈ max base (sup fun i => next (F (f i)))) :
    ∀ t, F t ≈ orec base next t :=
  trec_unique sup_joinLaws (stepLaws_true base next) (nextMono_of_mono hm) F (fun _ => trivial)
    fun ι f => Equiv.trans (hF ι f) (dunion_sup_equiv_max _ _).symm

end Orec

/-- `orec` is monotone in `base` and `next` (snu-sf: `Ord.orec_mon`). -/
theorem orec_mono {base₀ base₁ : OTree.{u}} {next₀ next₁ : OTree.{u} → OTree.{u}}
    (hb : base₀ ≤ base₁) (hn : ∀ {s t : OTree.{u}}, s ≤ t → next₀ s ≤ next₁ t) (t : OTree.{u}) :
    orec base₀ next₀ t ≤ orec base₁ next₁ t :=
  trec_mono sup_joinLaws (stepLaws_true base₀ next₀) (stepLaws_true base₁ next₁) hb
    (fun _ _ h => hn h) t

/-- `orec` respects `≈` in `base` and `next`. -/
theorem orec_congr_step {base₀ base₁ : OTree.{u}} {next₀ next₁ : OTree.{u} → OTree.{u}}
    (hb : base₀ ≈ base₁) (hn₀ : ∀ {s t : OTree.{u}}, s ≤ t → next₀ s ≤ next₁ t)
    (hn₁ : ∀ {s t : OTree.{u}}, s ≤ t → next₁ s ≤ next₀ t) (t : OTree.{u}) :
    orec base₀ next₀ t ≈ orec base₁ next₁ t :=
  ⟨orec_mono hb.le hn₀ t, orec_mono hb.ge hn₁ t⟩

/-- snu-sf: `Ord.orec_of_S`. -/
theorem orec_zero_succ (t : OTree.{u}) : orec zero succ t ≈ t :=
  (orec_unique succ_le_succ id
    (fun _ f => Equiv.trans (mk_equiv_sup_succ f) (max_equiv_of_le (zero_le _)).symm) t).symm

end OTree

end Ordinals
