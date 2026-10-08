/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Ordinals.Tree.ClassicalRec

/-!
# Fixed points

The fixed-point theorem of Bourbaki and Witt (`ChainRecLaws.next_trec_hartogs_equiv`), and the
least and greatest fixed points `mu f`, `nu f` of a monotone function `f` on the predicates
`A → Prop`. This file follows snu-sf/Ordinal (`src/Fixedpoint.v`).
-/

@[expose] public section

namespace Ordinals

universe u

namespace OTree

/-! ## The fixed-point theorem -/

/-- The fixed-point theorem of Bourbaki and Witt: `trec` at the Hartogs ordinal of `D` is a
fixed point of `next`, up to equivalence (snu-sf: `fixpoint_theorem`). -/
theorem ChainRecLaws.next_trec_hartogs_equiv {D : Type u} {dle : D → D → Prop}
    {wf : D → Prop} {djoin : (A : Type u) → (A → D) → D} {base : D} {next : D → D}
    (h : ChainRecLaws dle wf djoin base next) :
    dle (next (trec base next djoin (hartogs D))) (trec base next djoin (hartogs D)) ∧
      dle (trec base next djoin (hartogs D)) (next (trec base next djoin (hartogs D))) :=
  ⟨h.next_trec_hartogs_le, h.next_le (h.trec_wf _)⟩

/-- `trec` does not increase after the Hartogs ordinal of `D`. -/
theorem ChainRecLaws.trec_le_trec_hartogs {D : Type u} {dle : D → D → Prop}
    {wf : D → Prop} {djoin : (A : Type u) → (A → D) → D} {base : D} {next : D → D}
    (h : ChainRecLaws dle wf djoin base next) (t : OTree.{u}) :
    dle (trec base next djoin t) (trec base next djoin (hartogs D)) :=
  h.trec_le_of_next_trec_le h.next_trec_hartogs_le t

/-! ## Least and greatest fixed points of predicates -/

section Predicates

variable {A : Type u}

/-- Unions are joins for inclusion, on each set of predicates that is closed under unions. -/
theorem union_joinLaws {wf : (A → Prop) → Prop}
    (hwf : ∀ (X : Type u) (Ps : X → A → Prop), (∀ x, wf (Ps x)) → wf fun a => ∃ x, Ps x a) :
    JoinLaws (fun P Q : A → Prop => ∀ a, P a → Q a) wf
      fun (X : Type u) Ps a => ∃ x : X, Ps x a :=
  ⟨fun _ _ h => h, fun _ _ _ h₁ h₂ a h => h₂ a (h₁ a h), fun _ x _ h => ⟨x, h⟩,
    fun _ _ h a ⟨x, hx⟩ => h x a hx, fun hds => hwf _ _ hds⟩

/-- Intersections are joins for reverse inclusion, on each set of predicates that is closed
under intersections. -/
theorem inter_joinLaws {wf : (A → Prop) → Prop}
    (hwf : ∀ (X : Type u) (Ps : X → A → Prop), (∀ x, wf (Ps x)) → wf fun a => ∀ x, Ps x a) :
    JoinLaws (fun P Q : A → Prop => ∀ a, Q a → P a) wf
      fun (X : Type u) Ps a => ∀ x : X, Ps x a :=
  ⟨fun _ _ h => h, fun _ _ _ h₁ h₂ a h => h₁ a (h₂ a h), fun _ x _ h => h x,
    fun _ _ h a hd x => h x a hd, fun hds => hwf _ _ hds⟩

/-- The least fixed point of a monotone `f`: the recursion from the empty predicate, with `f`
and unions, up to the Hartogs ordinal of `A → Prop` (snu-sf: `mu`). -/
def mu (f : (A → Prop) → A → Prop) : A → Prop :=
  trec (fun _ => False) f (fun (X : Type u) Ps a => ∃ x : X, Ps x a) (hartogs (A → Prop))

/-- The greatest fixed point of a monotone `f`: the recursion from the full predicate, with `f`
and intersections, up to the Hartogs ordinal of `A → Prop` (snu-sf: `nu`). -/
def nu (f : (A → Prop) → A → Prop) : A → Prop :=
  trec (fun _ => True) f (fun (X : Type u) Ps a => ∀ x : X, Ps x a) (hartogs (A → Prop))

variable {f : (A → Prop) → A → Prop}
  (hf : ∀ P Q : A → Prop, (∀ a, P a → Q a) → ∀ a, f P a → f Q a)
include hf

/-- The join laws for `mu`: the elements are the predicates `P` with `P ⊆ f P`. -/
theorem mu_joinLaws :
    JoinLaws (fun P Q : A → Prop => ∀ a, P a → Q a) (fun P => ∀ a, P a → f P a)
      fun (X : Type u) Ps a => ∃ x : X, Ps x a :=
  union_joinLaws fun _ _ hPs a ⟨x, hx⟩ => hf _ _ (fun _ h => ⟨x, h⟩) a (hPs x a hx)

theorem mu_stepLaws : StepLaws (fun P : A → Prop => ∀ a, P a → f P a) (fun _ => False) f :=
  ⟨fun _ h => h.elim, fun hP => hf _ _ hP⟩

theorem mu_chainRecLaws :
    ChainRecLaws (fun P Q : A → Prop => ∀ a, P a → Q a) (fun P => ∀ a, P a → f P a)
      (fun (X : Type u) Ps a => ∃ x : X, Ps x a) (fun _ => False) f :=
  ChainRecLaws.of_joinLaws (mu_joinLaws hf) (mu_stepLaws hf) (fun h => h)
    (fun _ _ h => hf _ _ h)

/-- The join laws for `nu`: the order is the reverse inclusion, and the elements are the
predicates `P` with `f P ⊆ P`. -/
theorem nu_joinLaws :
    JoinLaws (fun P Q : A → Prop => ∀ a, Q a → P a) (fun P => ∀ a, f P a → P a)
      fun (X : Type u) Ps a => ∀ x : X, Ps x a :=
  inter_joinLaws fun _ _ hPs a h x => hPs x a (hf _ _ (fun _ h' => h' x) a h)

theorem nu_stepLaws : StepLaws (fun P : A → Prop => ∀ a, f P a → P a) (fun _ => True) f :=
  ⟨fun _ _ => trivial, fun hP => hf _ _ hP⟩

theorem nu_chainRecLaws :
    ChainRecLaws (fun P Q : A → Prop => ∀ a, Q a → P a) (fun P => ∀ a, f P a → P a)
      (fun (X : Type u) Ps a => ∀ x : X, Ps x a) (fun _ => True) f :=
  ChainRecLaws.of_joinLaws (nu_joinLaws hf) (nu_stepLaws hf) (fun h => h)
    (fun _ _ h => hf _ _ h)

/-- snu-sf: `mu_fixpoint`. -/
theorem mu_le_map_mu : ∀ a, mu f a → f (mu f) a :=
  trec_wf (mu_joinLaws hf) (mu_stepLaws hf) _

/-- snu-sf: `mu_fixpoint`. -/
theorem map_mu_le_mu : ∀ a, f (mu f) a → mu f a :=
  (mu_chainRecLaws hf).next_trec_hartogs_le

/-- `mu f` is a fixed point of `f` (snu-sf: `mu_fixpoint`). -/
theorem map_mu : f (mu f) = mu f :=
  funext fun a => propext ⟨map_mu_le_mu hf a, mu_le_map_mu hf a⟩

/-- `mu f` is below each predicate `P` with `f P ⊆ P` (snu-sf: `mu_least`). -/
theorem mu_le {P : A → Prop} (hP : ∀ a, f P a → P a) : ∀ a, mu f a → P a :=
  (trec_wf (wf := fun Q => (∀ a, Q a → f Q a) ∧ ∀ a, Q a → P a)
    (union_joinLaws fun _ _ hPs =>
      ⟨fun a ⟨x, hx⟩ => hf _ _ (fun _ h => ⟨x, h⟩) a ((hPs x).1 a hx),
        fun a ⟨x, hx⟩ => (hPs x).2 a hx⟩)
    ⟨⟨fun _ h => h.elim, fun _ h => h.elim⟩,
      fun hQ => ⟨hf _ _ hQ.1, fun a h => hP a (hf _ _ hQ.2 a h)⟩⟩
    (hartogs (A → Prop))).2

/-- snu-sf: `nu_fixpoint`. -/
theorem nu_le_map_nu : ∀ a, nu f a → f (nu f) a :=
  (nu_chainRecLaws hf).next_trec_hartogs_le

/-- snu-sf: `nu_fixpoint`. -/
theorem map_nu_le_nu : ∀ a, f (nu f) a → nu f a :=
  trec_wf (nu_joinLaws hf) (nu_stepLaws hf) _

/-- `nu f` is a fixed point of `f` (snu-sf: `nu_fixpoint`). -/
theorem map_nu : f (nu f) = nu f :=
  funext fun a => propext ⟨map_nu_le_nu hf a, nu_le_map_nu hf a⟩

/-- `nu f` is above each predicate `P` with `P ⊆ f P` (snu-sf: `nu_greatest`). -/
theorem le_nu {P : A → Prop} (hP : ∀ a, P a → f P a) : ∀ a, P a → nu f a :=
  (trec_wf (wf := fun Q => (∀ a, f Q a → Q a) ∧ ∀ a, P a → Q a)
    (inter_joinLaws fun _ _ hPs =>
      ⟨fun a h x => (hPs x).1 a (hf _ _ (fun _ h' => h' x) a h),
        fun a hp x => (hPs x).2 a hp⟩)
    ⟨⟨fun _ _ => trivial, fun _ _ => trivial⟩,
      fun hQ => ⟨hf _ _ hQ.1, fun a hp => hf _ _ hQ.2 a (hP a hp)⟩⟩
    (hartogs (A → Prop))).2

end Predicates

end OTree

end Ordinals
