module

public import Ordinals

/-! Tests for the classical recursion on trees (`Ordinals.Tree.ClassicalRec`): the axioms of the
main results, and examples. -/

open Ordinals OTree

universe u

/-! ## Axioms -/

/-- info: 'Ordinals.OTree.exists_equiv_ofWf_of_lt_ofWfSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OTree.exists_equiv_ofWf_of_lt_ofWfSet

/-- info: 'Ordinals.OTree.ofWfSet_lt_ofWfSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OTree.ofWfSet_lt_ofWfSet

/-- info: 'Ordinals.OTree.exists_isMeet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OTree.exists_isMeet

/-- info: 'Ordinals.OTree.limitInduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OTree.limitInduction

/-- info: 'Ordinals.OTree.ChainRecLaws.of_joinLaws' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ChainRecLaws.of_joinLaws

/-- info: 'Ordinals.OTree.ChainRecLaws.trec_le_trec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OTree.ChainRecLaws.trec_le_trec

/-- info: 'Ordinals.OTree.ChainRecLaws.trec_sup_of_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OTree.ChainRecLaws.trec_sup_of_nonempty

/-- info: 'Ordinals.OTree.ChainRecLaws.trec_unique_of_zero_succ_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OTree.ChainRecLaws.trec_unique_of_zero_succ_limit

/-- info: 'Ordinals.OTree.ChainRecLaws.strictlyIncreasing_wf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OTree.ChainRecLaws.strictlyIncreasing_wf

/-- info: 'Ordinals.OTree.ChainRecLaws.next_trec_hartogs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OTree.ChainRecLaws.next_trec_hartogs_le

/-! ## Least elements and limits -/

/-- The trees above `ω` have a least element. -/
example : ∃ t, IsMeet (fun t => omega.{u} < t) t :=
  exists_isMeet ⟨succ omega, lt_succ omega⟩

/-- `limitInduction` is an induction principle for `induction ... using`. -/
example (t : OTree.{u}) : zero ≤ t := by
  induction t using limitInduction with
  | zero t _ _ => exact zero_le t
  | succ s t _ _ _ => exact zero_le t
  | limit ι f t _ _ _ _ _ => exact zero_le t

/-! ## A `next` that is not monotone

`jump` maps `zero` to `5` and keeps the other trees. Thus it is expansive and respects `≈`, but
it is not monotone: `zero ≤ 1`, but `jump zero ≈ 5` is not below `jump 1 = 1`. The classical
recursion still gives a monotone `trec`. -/

namespace ClassicalRecTest

open Classical in
/-- `5` at `zero`, else the identity. -/
noncomputable def jump (t : OTree.{u}) : OTree.{u} :=
  if t ≈ zero then ofNat 5 else t

theorem jump_chainRecLaws :
    ChainRecLaws (D := OTree.{u}) (· ≤ ·) (fun _ => True) (fun _ => sup) zero jump where
  toChainJoinLaws := sup_joinLaws.toChainJoinLaws
  toStepLaws := stepLaws_true _ _
  next_le := by
    intro t _
    unfold jump
    split
    · next h => exact OTree.le_trans h.le (zero_le _)
    · exact OTree.le_rfl
  next_congr := by
    intro s t _ _ hst hts
    unfold jump
    by_cases hs : s ≈ zero
    · have ht : t ≈ zero := Equiv.trans ⟨hts, hst⟩ hs
      simp only [hs, ht, ite_true]
      exact OTree.le_rfl
    · have ht : ¬t ≈ zero := fun ht => hs (Equiv.trans ⟨hst, hts⟩ ht)
      simp only [hs, ht, ite_false]
      exact hst

theorem not_jump_mono : ¬∀ s t : OTree.{u}, s ≤ t → jump s ≤ jump t := by
  intro h
  have h₀ : jump zero.{u} = ofNat 5 := ite_eq_left (Equiv.refl _)
  have h₁ : jump (ofNat.{u} 1) = ofNat 1 :=
    ite_eq_right fun e => not_lt_zero _ (OTree.lt_of_lt_of_le (zero_lt_succ zero) e.le)
  have := h zero (ofNat 1) (zero_le _)
  rw [h₀, h₁] at this
  exact absurd (ofNat_le_ofNat_iff.mp this) (by decide)

/-- `trec` with `jump` is monotone. -/
example (s t : OTree.{u}) (h : s ≤ t) :
    trec zero jump (fun _ => sup) s ≤ trec zero jump (fun _ => sup) t :=
  jump_chainRecLaws.trec_le_trec h

end ClassicalRecTest
