/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lean.Linter.Init
public meta import Lean.Linter.Basic
public meta import Lean.Elab.Command
public meta import Iris.Std.Linter.DeclarationNames

meta section

namespace Iris.Std.Linter

/-!
### `multipleSIdx` linter

`Iris.SIdx` has an `outParam`, so instance search for `SIdx ?I` returns one instance (the last
local instance, else a global one) and never backtracks. With two visible `SIdx` instances, every
step-indexed notion (`OFE α`, `≡{n}≡`, …) uses the same one, and code for the other index type
fails to elaborate.

The linter warns
1. at a declaration with two or more binders of type `SIdx _` (explicit binders of class type
   are instances too), and
2. at a global `SIdx` instance declared while another `SIdx` instance is active.
-/

/-- Warn when more than one `SIdx` (step-index) instance is visible; see `Iris.SIdx`. -/
public register_option linter.iris.multipleSIdx : Bool := {
  defValue := true
  descr := "enable the multiple step-index-instances linter"
}

namespace MultipleSIdxLinter

open Lean Parser Elab Command Meta Lean.Linter

/-- Number of binders of type `Iris.SIdx _` in the leading `∀`s of `ty`. -/
def countSIdxBinders (ty : Expr) : MetaM Nat :=
  forallTelescopeReducing ty fun xs _ => do
    let mut k := 0
    for x in xs do
      if (← instantiateMVars (← inferType x)).isAppOf `Iris.SIdx then k := k + 1
    return k

/-- The active `SIdx` instances (global, opened `scoped` and `local` ones). -/
def activeSIdxInstances : MetaM (Array Name) := do
  let u ← mkFreshLevelMVar
  let I ← mkFreshExprMVar (mkSort (.succ u))
  let entries ← (← getGlobalInstancesIndex).getUnify (mkApp (.const `Iris.SIdx [u]) I)
  return entries.filterMap (·.globalName?)

/-- Is `stx` an `instance` command with a `scoped` or `local` attribute kind? -/
def isScopedOrLocalInstance (stx : Syntax) : Bool :=
  match stx.find? (·.isOfKind ``Lean.Parser.Term.attrKind) with
  | some k => !k[0].isNone
  | none => false

@[inherit_doc linter.iris.multipleSIdx]
def multipleSIdx : Linter where run := withSetOptionIn fun stx ↦ do
  unless getLinterValue linter.iris.multipleSIdx (← getLinterOptions) do return
  let env ← getEnv
  unless env.contains `Iris.SIdx do return
  for id in ← getNamesFrom (stx.getPos?.getD default) do
    let declName := id.getId
    if declName.hasMacroScopes then continue
    let some ci := env.find? declName | continue
    let k ← liftTermElabM <| countSIdxBinders ci.type
    if k ≥ 2 then
      Linter.logLint linter.iris.multipleSIdx id
        m!"`{.ofConstName declName}` has {k} step-index instances (`SIdx _` binders). `SIdx` \
        has an outParam, so instance search only ever uses the last one; pass the others \
        explicitly (e.g. as a non-class structure) or split the declaration."
    -- a new global `SIdx` instance next to an already active one
    let isSIdxInst ← liftTermElabM do
      if !(← isInstance declName) then return false
      forallTelescopeReducing ci.type fun _ b => return b.isAppOf `Iris.SIdx
    if isSIdxInst && !isScopedOrLocalInstance stx then
      let others := (← liftTermElabM activeSIdxInstances).filter (· != declName)
      unless others.isEmpty do
        Linter.logLint linter.iris.multipleSIdx id
          m!"global `SIdx` instance `{.ofConstName declName}` is declared while \
          {MessageData.andList (others.toList.map (m!"`{.ofConstName ·}`"))} is active. \
          `SIdx` has an outParam, so with two instances visible instance search picks one \
          of them; make one of them `scoped`."

initialize addLinter multipleSIdx

end MultipleSIdxLinter

end Iris.Std.Linter
