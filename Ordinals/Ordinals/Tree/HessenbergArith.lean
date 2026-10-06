/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Tree.Arith
public import Ordinals.Tree.Hessenberg

/-!
# The natural sum and the standard sum of trees

The natural sum `nadd s t` is at least the standard sum `add s t`. If `t` is a natural number,
the two sums are equivalent.

This file follows snu-sf/Ordinal (`src/Hessenberg.v`, module `Hessenberg`, section `ADD`). These
two lemmas use the standard sum, thus they are not in the file `Ordinals.Tree.Hessenberg`. The
results of this file use no axioms.
-/

@[expose] public section

namespace Ordinals

universe u

namespace OTree

/-- The standard sum is at most the natural sum (snu-sf: `Hessenberg.arith_add_larger`). -/
theorem add_le_nadd (s t : OTree.{u}) : add s t ≤ nadd s t := by
  induction t using lt_wf.induction with
  | _ t ih =>
    exact orec_le (le_self_nadd s t) fun t' ht' =>
      succ_le_of_lt (OTree.lt_of_le_of_lt (ih t' ht') (nadd_lt_nadd_left ht' s))

/-- The natural sum and the standard sum are equivalent if the second tree is a natural number
(snu-sf: `Hessenberg.arith_add_from_nat`). -/
theorem nadd_ofNat_equiv_add (s : OTree.{u}) :
    ∀ n : Nat, nadd s (ofNat n) ≈ add s (ofNat n)
  | 0 => (nadd_zero s).trans (OTree.add_zero s).symm
  | n + 1 =>
    (nadd_succ s _).trans ((succ_congr (nadd_ofNat_equiv_add s n)).trans (add_succ s _).symm)

/-- The natural sum `nadd (ofNat n) s` is the standard sum `add s (ofNat n)`, with the natural
number on the right. -/
theorem ofNat_nadd_equiv_add (n : Nat) (s : OTree.{u}) : nadd (ofNat n) s ≈ add s (ofNat n) :=
  (nadd_comm _ s).trans (nadd_ofNat_equiv_add s n)

end OTree

end Ordinals
