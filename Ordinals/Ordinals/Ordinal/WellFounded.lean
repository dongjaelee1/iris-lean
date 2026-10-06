/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Ordinal.Lift
public import Ordinals.Tree.WellFounded
public import Ordinals.Tree.WfRel

/-!
# Ordinals of well-founded relations

For a well-founded relation `R` on `A : Type u`:

- `Ordinal.ofWf hwf a`: the rank of `a` (snu-sf: `Ord.from_wf`);
- `Ordinal.type hwf`: the strict supremum of all ranks (snu-sf: `Ord.from_wf_set`);
- `Ordinal.hartogs A`: the strict supremum of the types of all well-founded relations on `A`
  (snu-sf: `Ord.hartogs`).

Each ordinal is the type of a well-founded relation (`exists_type_eq`), and snu-sf's `large` is
`univ` (`large_eq_univ`).
-/

@[expose] public section

namespace Ordinals

universe u v

namespace Ordinal

variable {A : Type u} {R : A → A → Prop}

/-- The rank of `a` for a well-founded relation (snu-sf: `Ord.from_wf`). -/
def ofWf (hwf : WellFounded R) (a : A) : Ordinal.{u} :=
  mk (OTree.ofWf hwf a)

/-- The order type of a well-founded relation: the strict supremum of the ranks
(snu-sf: `Ord.from_wf_set`). -/
def type (hwf : WellFounded R) : Ordinal.{u} :=
  mk (OTree.ofWfSet hwf)

theorem ofWf_lt_ofWf (hwf : WellFounded R) {a b : A} (h : R a b) : ofWf hwf a < ofWf hwf b :=
  OTree.ofWf_lt_ofWf hwf h

/-- The rank is the strict supremum of the ranks of the predecessors. -/
theorem ofWf_eq_ssup (hwf : WellFounded R) (a : A) :
    ofWf hwf a = ssup fun b : {b // R b a} => ofWf hwf b.1 := by
  show mk (OTree.ofWf hwf a) = ssup fun b : {b // R b a} => mk (OTree.ofWf hwf b.1)
  rw [ssup_mk, OTree.ofWf_eq]

theorem ofWf_le_iff (hwf : WellFounded R) {a : A} {c : Ordinal.{u}} :
    ofWf hwf a ≤ c ↔ ∀ b, R b a → ofWf hwf b < c := by
  rw [ofWf_eq_ssup, ssup_le_iff]
  exact ⟨fun h b hb => h ⟨b, hb⟩, fun h b => h b.1 b.2⟩

theorem lt_ofWf_iff (hwf : WellFounded R) {a : A} {c : Ordinal.{u}} :
    c < ofWf hwf a ↔ ∃ b, R b a ∧ c ≤ ofWf hwf b := by
  rw [ofWf_eq_ssup, lt_ssup_iff]
  exact ⟨fun ⟨b, hb⟩ => ⟨b.1, b.2, hb⟩, fun ⟨b, hb, h⟩ => ⟨⟨b, hb⟩, h⟩⟩

theorem type_eq_ssup (hwf : WellFounded R) : type hwf = ssup fun a => ofWf hwf a := by
  show mk (OTree.ofWfSet hwf) = ssup fun a => mk (OTree.ofWf hwf a)
  rw [ssup_mk]; rfl

theorem ofWf_lt_type (hwf : WellFounded R) (a : A) : ofWf hwf a < type hwf :=
  OTree.ofWf_lt_ofWfSet hwf a

theorem type_le_iff (hwf : WellFounded R) {c : Ordinal.{u}} :
    type hwf ≤ c ↔ ∀ a, ofWf hwf a < c := by
  rw [type_eq_ssup, ssup_le_iff]

theorem lt_type_iff (hwf : WellFounded R) {c : Ordinal.{u}} :
    c < type hwf ↔ ∃ a, c ≤ ofWf hwf a := by
  rw [type_eq_ssup, lt_ssup_iff]

/-- Each ordinal is the order type of a well-founded relation (the positions of a tree). -/
theorem exists_type_eq (c : Ordinal.{u}) :
    ∃ (B : Type u) (S : B → B → Prop) (hwf : WellFounded S), type hwf = c := by
  induction c using Ordinal.ind with
  | _ t => exact ⟨_, _, OTree.Pos.rel_wf t, (sound (OTree.equiv_ofWfSet_pos t)).symm⟩

/-- A relation that contains another has at least its type (snu-sf: `from_wf_set_le`). -/
theorem type_le_type_of_subrelation {R₀ R₁ : A → A → Prop} (h : Subrelation R₀ R₁)
    (hwf₀ : WellFounded R₀) (hwf₁ : WellFounded R₁) : type hwf₀ ≤ type hwf₁ :=
  OTree.ofWfSet_mono h hwf₀ hwf₁

/-! ## Natural numbers -/

theorem ofNat_eq_ofWf (n : Nat) : ofNat.{u} n = ofWf OTree.ulift_nat_lt_wf ⟨n⟩ :=
  sound (OTree.ofNat_equiv_ofWf n)

theorem omega_eq_type : (ω : Ordinal.{u}) = type OTree.ulift_nat_lt_wf.{u} :=
  sound OTree.omega_equiv_ofWfSet

/-! ## Hartogs ordinals -/

/-- The strict supremum of the types of the well-founded relations on `A`
(snu-sf: `Ord.hartogs`). -/
def hartogs (A : Type u) : Ordinal.{u} :=
  mk (OTree.hartogs A)

theorem type_lt_hartogs (hwf : WellFounded R) : type hwf < hartogs A :=
  OTree.ofWfSet_lt_hartogs hwf

theorem hartogs_le_iff {c : Ordinal.{u}} :
    hartogs A ≤ c ↔ ∀ (S : A → A → Prop) (hwf : WellFounded S), type hwf < c := by
  induction c using Ordinal.ind with
  | _ t => exact OTree.hartogs_le_iff

/-! ## `large` is `univ` -/

/-- snu-sf's `large`: above the types of all well-founded relations on types in `Type u`. It is
`univ` (`large_eq_univ`). -/
def large : Ordinal.{u + 1} :=
  mk OTree.large.{u}

theorem lift_type_lt_large (hwf : WellFounded R) : lift.{u, u + 1} (type hwf) < large.{u} :=
  OTree.lift_ofWfSet_lt_large hwf

theorem large_eq_univ : large.{u} = univ.{u} := by
  refine Ordinal.le_antisymm ?_ ?_
  · refine (show mk OTree.large.{u} ≤ univ.{u} from ?_)
    conv => rhs; rw [← mk_out univ.{u}]
    refine OTree.large_le_of_forall_lt fun B S hwf => ?_
    have h := lift_lt_univ.{u} (type hwf)
    rw [← mk_out univ.{u}] at h
    exact h
  · refine ssup_le fun c => ?_
    obtain ⟨B, S, hwf, rfl⟩ := exists_type_eq c
    exact lift_type_lt_large hwf

end Ordinal

end Ordinals
