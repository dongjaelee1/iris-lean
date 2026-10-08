/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Tree.Arith
public import Ordinals.Tree.Hessenberg

/-!
# The natural sum and the standard sum of trees

`nadd s t` is at least `add s t`, and the two sums are equivalent if `t` is a natural number.
This file follows snu-sf/Ordinal (`src/Hessenberg.v`, module `Hessenberg`, section `ADD`).
-/

@[expose] public section

namespace Ordinals

universe u

namespace OTree

/-- snu-sf: `Hessenberg.arith_add_larger`. -/
theorem add_le_nadd (s t : OTree.{u}) : add s t ≤ nadd s t := by
  induction t using lt_wf.induction with
  | _ t ih =>
    exact orec_le (le_self_nadd s t) fun t' ht' =>
      succ_le_of_lt (OTree.lt_of_le_of_lt (ih t' ht') (nadd_lt_nadd_left ht' s))

/-- snu-sf: `Hessenberg.arith_add_from_nat`. -/
theorem nadd_ofNat_equiv_add (s : OTree.{u}) :
    ∀ n : Nat, nadd s (ofNat n) ≈ add s (ofNat n)
  | 0 => (nadd_zero s).trans (OTree.add_zero s).symm
  | n + 1 =>
    (nadd_succ s _).trans ((succ_congr (nadd_ofNat_equiv_add s n)).trans (add_succ s _).symm)

theorem ofNat_nadd_equiv_add (n : Nat) (s : OTree.{u}) : nadd (ofNat n) s ≈ add s (ofNat n) :=
  (nadd_comm _ s).trans (nadd_ofNat_equiv_add s n)

end OTree

end Ordinals
