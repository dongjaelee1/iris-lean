/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Iris.Instances.UPred.ProofMode
public import Iris.ProofMode

@[expose] public section

/-! Destructuring `▷` over timeless and persistent bodies, which the `[SIdxFinite]`-free fallback
instances of `Iris.Instances.UPred.ProofMode` provide at every step index. -/

namespace IrisTest
open Iris BI ProofMode UPred

variable {M : Type} [UCMRA M]

example (P Q : Nat → UPred M) [∀ n, Timeless (P n)] [∀ n, Timeless (Q n)] :
    iprop(▷ ∃ n, P n ∗ Q n) ⊢ iprop(∃ n, ▷ P n ∗ ▷ Q n) := by
  iintro ⟨%n, HP, HQ⟩
  iexists n
  iframe HP HQ

example (P Q : UPred M) [Persistent P] : iprop(▷ (P ∗ Q)) ⊢ iprop(▷ P ∗ ▷ Q) := by
  iintro ⟨HP, HQ⟩
  iframe HP HQ

example (P Q : UPred M) [Persistent Q] : iprop(▷ (P ∗ Q)) ⊢ iprop(▷ P ∗ ▷ Q) := by
  iintro ⟨HP, HQ⟩
  iframe HP HQ

/-- The timeless parts can then be stripped with `>` under an except-0 goal. -/
example (P Q : Nat → UPred M) [∀ n, Timeless (P n)] [∀ n, Timeless (Q n)] :
    iprop(▷ ∃ n, P n ∗ Q n) ⊢ iprop(◇ ∃ n, P n ∗ Q n) := by
  iintro ⟨%n, >HP, >HQ⟩
  imodintro
  iexists n
  iframe HP HQ

end IrisTest
