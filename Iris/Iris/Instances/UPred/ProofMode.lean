/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Algebra.IsOp
public import Iris.Instances.UPred.Instance
public import Iris.Instances.UPred.Transfinite
public import Iris.ProofMode.Classes

@[expose] public section

open Iris BI CMRA ProofMode Std

namespace UPred

variable [UCMRA M]

@[rocq_alias from_sep_ownM]
instance fromSep_ownM {a b1 b2 : M} [h : IsOp .split a b1 b2] :
    FromSep (ownM a) (ownM b1) (ownM b2) where
  from_sep := by rw [h.is_op]; exact (ownM_op ..).mpr

@[rocq_alias combine_sep_as_ownM]
instance (priority := default - 15) combineSepAs_ownM {a b1 b2 : M} [h : IsOp .merge a b1 b2] :
    CombineSepAs (ownM b1) (ownM b2) (ownM a) where
  combine_sep_as := by rw [h.is_op]; exact (ownM_op ..).mpr

@[rocq_alias combine_sep_gives_ownM]
instance combineSepGives_ownM {b1 b2 : M} :
    CombineSepGives (ownM b1) (ownM b2) iprop(✓ b1 • b2) where
  combine_sep_gives := (ownM_op ..).mpr.trans (ownM_valid _)

@[rocq_alias from_sep_ownM_core_id]
instance fromAnd_ownM_coreId {a b1 b2 : M} [h : IsOp .split a b1 b2]
    [TCOr (CoreId b1) (CoreId b2)] : FromAnd (ownM a) (ownM b1) (ownM b2) where
  from_and := by
    rw [h.is_op]
    refine .trans ?_ (ownM_op ..).mpr
    cases (inferInstance : TCOr (CoreId b1) (CoreId b2)) <;> exact persistent_and_sep.mp

@[rocq_alias into_and_ownM]
instance intoAnd_ownM (p : Bool) {a b1 b2 : M} [h : IsOp .split a b1 b2] :
    IntoAnd p (ownM a) (ownM b1) (ownM b2) where
  into_and := intuitionisticallyIf_mono <| by rw [h.is_op]; exact (ownM_op ..).mp.trans sep_and

@[rocq_alias into_sep_ownM]
instance intoSep_ownM {a b1 b2 : M} [h : IsOp .split a b1 b2] :
    IntoSep (ownM a) (ownM b1) (ownM b2) where
  into_sep := by rw [h.is_op]; exact (ownM_op ..).mp

/-! ### `▷` over a timeless or persistent body, at every step index

The generic instances `intoSep_later` and `intoExists_later` need `[SIdxFinite SI]`: at a limit
index a later does not commute with `∗` or `∃` in general.  These fallbacks use the model-level laws
of `Iris.Instances.UPred.Transfinite`; their priorities put them after the generic instances and
`intoSepFractional` but before `intoSepFractionalHalf`, which matches any `IntoSep` goal and does
not backtrack (the IPM search moves on only from an instance marked `ipm_backtrack`, as these are;
Transfinite Iris's priority-100 instances); the cases are of `Iris.Instances.UPred.Transfinite`: both parts timeless, one part
persistent, or a timeless existential body. -/

@[ipm_backtrack] instance (priority := default - 20) intoSep_later_timeless (P Q1 Q2 : UPred M) [h : IntoSep P Q1 Q2]
    [Timeless Q1] [Timeless Q2] : IntoSep iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  into_sep := (later_mono h.1).trans (Iris.UPred.later_sep_timeless Q1 Q2).1

@[ipm_backtrack] instance (priority := default - 25) intoSep_later_persistent_l (P Q1 Q2 : UPred M) [h : IntoSep P Q1 Q2]
    [Persistent Q1] : IntoSep iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  into_sep := (later_mono h.1).trans (Iris.UPred.later_sep_persistent_l Q1 Q2)

@[ipm_backtrack] instance (priority := default - 25) intoSep_later_persistent_r (P Q1 Q2 : UPred M) [h : IntoSep P Q1 Q2]
    [Persistent Q2] : IntoSep iprop(▷ P) iprop(▷ Q1) iprop(▷ Q2) where
  into_sep := (later_mono h.1).trans (Iris.UPred.later_sep_persistent_r Q1 Q2)

@[ipm_backtrack] instance (priority := default - 20) intoExists_later_timeless [Inhabited α] (P : UPred M) (Φ : α → UPred M)
    [h : IntoExists P Φ] [∀ a, Timeless (Φ a)] :
    IntoExists iprop(▷ P) (fun a => iprop(▷ Φ a)) where
  into_exists := (later_mono h.1).trans (Iris.UPred.later_exists_timeless Φ)

end UPred

end
