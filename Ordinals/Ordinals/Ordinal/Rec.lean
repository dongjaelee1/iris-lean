/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Ordinal.Arith
public import Ordinals.Tree.Rec

/-!
# Transfinite recursion on ordinals

`Ordinal.orec base next` is the function `F` with `F a = max base (sup over b < a of
next (F b))` (snu-sf: `Ord.orec`). It is the tree recursion `OTree.orec` of
`Ordinals.Tree.Rec`, applied to representatives. The equations hold if `next` is monotone
(`hm : ∀ {a b}, a ≤ b → next a ≤ next b`); some need also that `next` is expansive
(`hl : ∀ a, a ≤ next a`).

The standard sum is `orec a succ` (`orec_succ_eq_add`).
-/

@[expose] public section

namespace Ordinals

universe u

namespace Ordinal

/-- The tree function of a function on ordinals: it maps a tree to a representative of the
image of its ordinal. -/
noncomputable def treeFun (F : Ordinal.{u} → Ordinal.{u}) (t : OTree.{u}) : OTree.{u} :=
  (F (mk t)).out

@[simp] theorem mk_treeFun (F : Ordinal.{u} → Ordinal.{u}) (t : OTree.{u}) :
    mk (treeFun F t) = F (mk t) :=
  mk_out _

theorem treeFun_mono {F : Ordinal.{u} → Ordinal.{u}} (hm : ∀ {a b}, a ≤ b → F a ≤ F b)
    {s t : OTree.{u}} (h : s ≤ t) : treeFun F s ≤ treeFun F t := by
  have h' := hm (show mk s ≤ mk t from h)
  rw [← mk_treeFun F s, ← mk_treeFun F t] at h'
  exact h'

theorem le_treeFun {F : Ordinal.{u} → Ordinal.{u}} (hl : ∀ a, a ≤ F a) (t : OTree.{u}) :
    t ≤ treeFun F t := by
  have h' := hl (mk t)
  rw [← mk_treeFun F t] at h'
  exact h'

theorem max_mk_right (a : Ordinal.{u}) (t : OTree.{u}) : max a (mk t) = mk (OTree.max a.out t) := by
  conv => lhs; rw [← mk_out a]
  rfl

/-- Transfinite recursion (snu-sf: `Ord.orec`). -/
noncomputable def orec (base : Ordinal.{u}) (next : Ordinal.{u} → Ordinal.{u})
    (a : Ordinal.{u}) : Ordinal.{u} :=
  mk (OTree.orec base.out (treeFun next) a.out)

section Orec

variable {base : Ordinal.{u}} {next : Ordinal.{u} → Ordinal.{u}}

theorem base_le_orec (a : Ordinal.{u}) : base ≤ orec base next a := by
  have h := OTree.base_le_orec (base := base.out) (next := treeFun next) a.out
  rw [← mk_le_mk, mk_out] at h
  exact h

variable (hm : ∀ {a b : Ordinal.{u}}, a ≤ b → next a ≤ next b)

include hm in
theorem orec_mk (t : OTree.{u}) : orec base next (mk t) = mk (OTree.orec base.out (treeFun next) t) :=
  sound (OTree.orec_congr (treeFun_mono hm) (out_mk_equiv t))

include hm in
/-- snu-sf: `Ord.le_orec`. -/
theorem orec_le_orec {a b : Ordinal.{u}} (h : a ≤ b) : orec base next a ≤ orec base next b := by
  induction a, b using Ordinal.inductionOn₂ with
  | _ s t =>
    rw [orec_mk hm, orec_mk hm]
    exact OTree.orec_le_orec (treeFun_mono hm) h

include hm in
/-- snu-sf: `Ord.lt_rec` for `orec`. -/
theorem next_orec_le_orec {a b : Ordinal.{u}} (h : a < b) :
    next (orec base next a) ≤ orec base next b := by
  induction a, b using Ordinal.inductionOn₂ with
  | _ s t =>
    rw [orec_mk hm, orec_mk hm, ← mk_treeFun next]
    exact OTree.next_orec_le_orec (treeFun_mono hm) h

include hm in
/-- snu-sf: `Ord.orec_O`. -/
theorem orec_zero : orec base next 0 = base := by
  rw [show (0 : Ordinal.{u}) = mk OTree.zero from rfl, orec_mk hm]
  conv => rhs; rw [← mk_out base]
  exact sound OTree.orec_zero

include hm in
/-- snu-sf: `Ord.orec_S`. -/
theorem orec_succ (hl : ∀ a, a ≤ next a) (a : Ordinal.{u}) :
    orec base next (succ a) = next (orec base next a) := by
  induction a using Ordinal.ind with
  | _ t =>
    rw [succ_mk, orec_mk hm, orec_mk hm, ← mk_treeFun next]
    exact sound (OTree.orec_succ (le_treeFun hl) t)

include hm in
/-- snu-sf: `Ord.orec_join`. -/
theorem orec_sup {ι : Type u} (f : ι → Ordinal.{u}) :
    orec base next (sup f) = max base (sup fun i => orec base next (f i)) := by
  obtain ⟨g, rfl⟩ := exists_eq_mk_comp f
  rw [sup_mk, orec_mk hm]
  simp only [orec_mk hm]
  rw [sup_mk, max_mk_right]
  exact sound (OTree.orec_sup (treeFun_mono hm) g)

include hm in
/-- snu-sf: `Ord.orec_join_inhabited`. -/
theorem orec_sup_of_nonempty {ι : Type u} [Nonempty ι] (f : ι → Ordinal.{u}) :
    orec base next (sup f) = sup fun i => orec base next (f i) := by
  obtain ⟨g, rfl⟩ := exists_eq_mk_comp f
  rw [sup_mk, orec_mk hm]
  simp only [orec_mk hm]
  rw [sup_mk]
  exact sound (OTree.orec_sup_of_nonempty (treeFun_mono hm) g)

include hm in
/-- `orec` on a strict supremum (snu-sf: `Ord.orec_build`). -/
theorem orec_ssup {ι : Type u} (f : ι → Ordinal.{u}) :
    orec base next (ssup f) = max base (sup fun i => next (orec base next (f i))) := by
  obtain ⟨g, rfl⟩ := exists_eq_mk_comp f
  have hn : ∀ t, next (mk t) = mk (treeFun next t) := fun t => (mk_treeFun next t).symm
  rw [ssup_mk, orec_mk hm]
  simp only [orec_mk hm, hn]
  rw [sup_mk, max_mk_right]
  exact sound (OTree.orec_mk ι g)

include hm in
/-- `orec` at a limit ordinal: the supremum of the earlier values. -/
theorem orec_limit {a : Ordinal.{u}} (ha : IsLimit a) :
    orec base next a = max base (sup fun i : a.out.Index => orec base next (mk (a.out.child i))) := by
  conv => lhs; rw [← ha.sup_eq]
  exact orec_sup hm _

include hm in
/-- An upper bound of `orec` (snu-sf: `Ord.orec_build_supremum`). -/
theorem orec_le {a c : Ordinal.{u}} (hb : base ≤ c) (h : ∀ b, b < a → next (orec base next b) ≤ c) :
    orec base next a ≤ c := by
  induction a using Ordinal.ind with
  | _ t =>
    induction c using Ordinal.ind with
    | _ r =>
      rw [orec_mk hm]
      refine OTree.orec_le (by rw [← mk_le_mk, mk_out]; exact hb) fun s hs => ?_
      have := h (mk s) hs
      rw [orec_mk hm, ← mk_treeFun next] at this
      exact this

include hm in
/-- `orec` with `succ` adds the base (snu-sf: `OrdArith.add` is `orec o succ`). -/
theorem orec_eq_iff_forall {F : Ordinal.{u} → Ordinal.{u}}
    (hF : ∀ (ι : Type u) (f : ι → Ordinal.{u}), F (ssup f) = max base (sup fun i => next (F (f i))))
    (a : Ordinal.{u}) : F a = orec base next a := by
  induction a using Ordinal.induction with
  | _ a ih =>
    conv => lhs; rw [← ssup_lt a]
    conv => rhs; rw [← ssup_lt a]
    rw [hF, orec_ssup hm]
    congr 2
    funext i
    have hi : mk (a.out.child i) < a := by
      have := OTree.child_lt a.out i
      rw [← mk_lt_mk, mk_out] at this
      exact this
    rw [ih _ hi]

end Orec

/-- Recursion with `0` and `succ` is the identity (snu-sf: `Ord.orec_of_S`). -/
theorem orec_zero_succ (a : Ordinal.{u}) : orec 0 succ a = a := by
  refine (orec_eq_iff_forall (fun h => succ_le_succ h) (F := id) (fun ι f => ?_) a).symm
  show ssup f = max 0 (sup fun i => succ (f i))
  rw [ssup_eq_sup_succ]
  exact (Ordinal.max_eq_right (Ordinal.zero_le _)).symm

/-- The standard sum is the recursion with `succ` from the first summand. -/
theorem orec_succ_eq_add (a b : Ordinal.{u}) : orec a succ b = a + b := by
  refine (orec_eq_iff_forall (fun h => succ_le_succ h) (F := (a + ·)) (fun ι f => ?_) b).symm
  show a + ssup f = max a (sup fun i => succ (a + f i))
  rw [ssup_eq_sup_succ, add_sup]
  simp only [Ordinal.add_succ]

end Ordinal

end Ordinals
