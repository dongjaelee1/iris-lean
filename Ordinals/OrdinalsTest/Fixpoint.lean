module

public import Ordinals

/-! Tests for the fixed points (`Ordinals.Tree.Fixpoint`): the axioms of the main results, and
examples of `mu` and `nu`. -/

open Ordinals OTree

/-! ## Axioms -/

/-- info: 'Ordinals.OTree.ChainRecLaws.next_trec_hartogs_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OTree.ChainRecLaws.next_trec_hartogs_equiv

/-- info: 'Ordinals.OTree.map_mu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OTree.map_mu

/-- info: 'Ordinals.OTree.mu_le_map_mu' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.mu_le_map_mu

/-- info: 'Ordinals.OTree.mu_le' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.mu_le

/-- info: 'Ordinals.OTree.map_nu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OTree.map_nu

/-- info: 'Ordinals.OTree.le_nu' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.le_nu

namespace FixpointTest

/-! ## The even numbers as a least fixed point -/

/-- `0` is even, and `n + 2` is even if `n` is even. -/
def evenStep (P : Nat → Prop) (n : Nat) : Prop :=
  n = 0 ∨ ∃ m, P m ∧ n = m + 2

theorem evenStep_mono (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (n : Nat)
    (hn : evenStep P n) : evenStep Q n :=
  hn.imp id fun ⟨m, hm, e⟩ => ⟨m, h m hm, e⟩

example : mu evenStep 4 :=
  map_mu_le_mu evenStep_mono 4 <| .inr ⟨2, map_mu_le_mu evenStep_mono 2 <|
    .inr ⟨0, map_mu_le_mu evenStep_mono 0 (.inl rfl), rfl⟩, rfl⟩

/-- `mu evenStep` is below each predicate that `evenStep` keeps, for example `n % 2 = 0`. -/
example : ¬mu evenStep 3 := fun h => by
  have := mu_le evenStep_mono (P := fun n => n % 2 = 0)
    (fun n hn => by rcases hn with rfl | ⟨m, hm, rfl⟩ <;> omega) 3 h
  simp at this

example : mu evenStep = fun n => n % 2 = 0 := by
  funext n
  refine propext ⟨mu_le evenStep_mono (P := fun n => n % 2 = 0)
    (fun n hn => by rcases hn with rfl | ⟨m, hm, rfl⟩ <;> omega) n, fun hn => ?_⟩
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n, hn with
    | 0, _ => exact map_mu_le_mu evenStep_mono 0 (.inl rfl)
    | 1, h => simp at h
    | m + 2, h => exact map_mu_le_mu evenStep_mono _ (.inr ⟨m, ih m (by omega) (by omega), rfl⟩)

/-! ## The least and the greatest fixed points can differ

`shift P n := P (n + 1)`. Each constant predicate is a fixed point. The least fixed point is
empty, and the greatest fixed point is full. -/

/-- `P` at the next number. -/
def shift (P : Nat → Prop) (n : Nat) : Prop :=
  P (n + 1)

theorem shift_mono (P Q : Nat → Prop) (h : ∀ n, P n → Q n) (n : Nat) (hn : shift P n) :
    shift Q n :=
  h (n + 1) hn

example (n : Nat) : ¬mu shift n :=
  mu_le shift_mono (P := fun _ => False) (fun _ h => h) n

example (n : Nat) : nu shift n :=
  le_nu shift_mono (P := fun _ => True) (fun _ _ => trivial) n trivial

/-- `nu shift` is a fixed point of `shift`. -/
example : shift (nu shift) = nu shift :=
  map_nu shift_mono

end FixpointTest
