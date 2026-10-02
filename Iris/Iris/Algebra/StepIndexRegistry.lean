/-
Copyright (c) 2026 Markus de Medeiros. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Basic
public import Iris.Init

/-!
# Step Index Registry

An attribute holding a default type for step indices that can be registered per-section.
-/

open Lean Elab Command Tactic

/-- Extension used to track the current default type for step indices -/
public meta initialize siExt : SimpleScopedEnvExtension Name Name ←
  registerSimpleScopedEnvExtension {
    addEntry _ n := n
    initial := Name.anonymous
  }

/-- Query the type of step indices -/
@[expose] elab "#stepindex?" : command => do
  match siExt.getState (← getEnv) with
  | Name.anonymous =>  logInfo m!"No step index declared."
  | si =>  logInfo m!"{si}"


/--
`stepindex%` elaborates to the step index type in scope, resolved eagerly as a term.
Use this in macros so that the step index type is calculated based on the default at the use site.
Elaborates to a hole when no default step index is in scope, as to default to whichever `SIdx`
instance is in scope.
-/
@[expose] elab "stepindex%" : term <= expectedType? => do
  match siExt.getState (← getEnv) with
  | .anonymous =>
    -- `SIdx` has an outParam, so the step index type is whatever the `SIdx` instance in scope
    -- is about. A local instance (the usual `[SIdx SI]` binder) is read off directly: this is
    -- cheaper than instance search and creates no universe metavariables (instance-search results
    -- are cached across the elaborator's backtracking, e.g. in overloaded notation).
    for li in (← Meta.getLocalInstances).reverse do
      if li.className == `Iris.SIdx then
        let ty ← instantiateMVars (← Meta.inferType li.fvar)
        if ty.isAppOfArity `Iris.SIdx 1 then return ty.appArg!
    -- Otherwise ask instance search (a global instance) rather than leaving a hole.
    let u ← Meta.mkFreshLevelMVar
    let I ← Meta.mkFreshExprMVar (mkSort (.succ u))
    match ← Meta.trySynthInstance (mkApp (.const `Iris.SIdx [u]) I) with
    | .some _ => instantiateMVars I
    | _ => Term.elabTerm (← `(_)) expectedType?
  | n => Term.elabTerm (mkIdent n) expectedType?

@[expose] elab "infer_stepindex" : tactic => do
  if (← getGoals).isEmpty then return
  match siExt.getState (← getEnv) with
  | .anonymous =>
    throwError "infer_stepindex: no step index in scope; declare one with `local stepindex T`"
  | n => evalTactic (← `(tactic| exact $(mkIdent n)))
