/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Tree.Constructions

/-!
# Classical facts about trees

With excluded middle, the order on trees is total: `s ≤ t ∨ t < s`. Totality needs excluded
middle (snu-sf: `Totalness.v`). This file follows snu-sf/Ordinal (`src/ClassicalOrdinal.v`).
-/

@[expose] public section

namespace Ordinals

universe u

namespace OTree

/-- Both directions at once: the proof of each direction uses the other on smaller trees. -/
private theorem total_aux : ∀ (s t : OTree.{u}), (s ≤ t ∨ t < s) ∧ (t ≤ s ∨ s < t)
  | mk ι f, t => by
    induction t with
    | mk κ g ih =>
      constructor
      · refine (Classical.em (∃ i, mk κ g ≤ f i)).elim
          (fun ⟨i, hi⟩ => .inr ⟨i, hi⟩) (fun h => .inl fun i => ?_)
        rcases (total_aux (f i) (mk κ g)).2 with hle | hlt
        · exact (h ⟨i, hle⟩).elim
        · exact hlt
      · refine (Classical.em (∃ j, mk ι f ≤ g j)).elim
          (fun ⟨j, hj⟩ => .inr ⟨j, hj⟩) (fun h => .inl fun j => ?_)
        rcases (ih j).1 with hle | hlt
        · exact (h ⟨j, hle⟩).elim
        · exact hlt

/-- The order on trees is total (snu-sf: `ClassicOrd.total`). -/
theorem le_or_lt (s t : OTree.{u}) : s ≤ t ∨ t < s :=
  (total_aux s t).1

/-- snu-sf: `ClassicOrd.total_le`. -/
theorem le_total (s t : OTree.{u}) : s ≤ t ∨ t ≤ s :=
  (le_or_lt s t).imp id OTree.le_of_lt

/-- snu-sf: `ClassicOrd.trichotomy`. -/
theorem lt_trichotomy (s t : OTree.{u}) : s < t ∨ s ≈ t ∨ t < s := by
  rcases le_or_lt s t with h₁ | h₁
  · rcases le_or_lt t s with h₂ | h₂
    · exact .inr (.inl ⟨h₁, h₂⟩)
    · exact .inl h₂
  · exact .inr (.inr h₁)

theorem not_le {s t : OTree.{u}} : ¬s ≤ t ↔ t < s :=
  ⟨fun h => (le_or_lt s t).resolve_left h, OTree.not_le_of_lt⟩

theorem not_lt {s t : OTree.{u}} : ¬s < t ↔ t ≤ s :=
  ⟨fun h => (le_or_lt t s).resolve_right h, OTree.not_lt_of_le⟩

/-- snu-sf: `ClassicOrd.le_eq_or_lt`. -/
theorem lt_or_equiv_of_le {s t : OTree.{u}} (h : s ≤ t) : s < t ∨ s ≈ t :=
  (le_or_lt t s).elim (fun h' => .inr ⟨h, h'⟩) .inl

end OTree

end Ordinals
