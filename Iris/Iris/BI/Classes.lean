/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro
-/
module

public import Iris.BI.BI

@[expose] public section

namespace Iris.BI

/-- Require that the proposition `P` is persistent. -/
@[rocq_alias Persistent]
class Persistent [BI PROP] (P : PROP) where
  persistent : P ⊢ <pers> P
export Persistent (persistent)

/-- Require that the proposition `P` is affine. -/
@[rocq_alias Affine]
class Affine [BI PROP] (P : PROP) where
  affine : P ⊢ emp
export Affine (affine)

/-- Require that the proposition `P` is absorbing. -/
@[rocq_alias Absorbing]
class Absorbing [BI PROP] (P : PROP) where
  absorbing : <absorb> P ⊢ P
export Absorbing (absorbing)

/-- Require that the proposition `P` is intuitionistic. -/
class Intuitionistic [BI PROP] (P : PROP) where
  intuitionistic : P ⊢ □ P
export Intuitionistic (intuitionistic)

/-- Require that the proposition `P` does not depend on the step index.

`P` is timeless when `P` holds at every step-index if it holds at step-index `0`. In the logic,
this is `<only0> P ⊢ P`. This version works for every type of step-indices (Transfinite Iris).
The other version, `▷ P ⊢ ◇ P` (`P` at `n` gives `P` at `n + 1`), follows from it
(`timeless_except0`). The two versions are equivalent with Löb induction (`timeless_alt`). -/
@[rocq_alias Timeless]
class Timeless [BI PROP] (P : PROP) where
  timeless : <only0> P ⊢ P

end Iris.BI
