/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Lean.Elab.DeclarationRange
public meta import Lean.Elab.Command

/-!
# Porting names of Transfinite Iris

`@[transfinite_alias]` and `#transfinite_ignore` are `@[rocq_alias]` and `#rocq_ignore` (see
`Iris.Std.RocqPorting`) for names that are not in Iris-Rocq: the names of
[Rocq Transfinite Iris](https://github.com/dongjaelee1/transfinite-iris) and of the Iris branch
that it builds on (MR !1256). The porting check against Iris-Rocq does not see these names, so
they are not reported as stale.

```
@[transfinite_alias LargeIndex]
class SIdxLarge ...

#transfinite_ignore uPred_primitive.later_false_sep "Inlined in `uPredI` construction"
```
-/

open Lean Elab Command

/-- Creates a `@[deprecated]` alias in the `RocqTransfinite` namespace with the given name of Rocq
Transfinite Iris. -/
syntax (name := transfinite_alias) "transfinite_alias " ident : attr

initialize registerBuiltinAttribute {
  name := `transfinite_alias
  descr := "Creates a @[deprecated] alias in the RocqTransfinite namespace for the name \
    correspondence with Rocq Transfinite Iris"
  applicationTime := .afterTypeChecking
  add := fun declName stx _kind => do
    let `(attr| transfinite_alias $rocqId) := stx
      | throwError "invalid @[transfinite_alias] syntax"
    let aliasName := `RocqTransfinite ++ rocqId.getId
    let env ← getEnv
    if env.find? aliasName |>.isSome then
      throwError s!"duplicate transfinite_alias: `{aliasName}` already exists"
    let some info := env.find? declName
      | throwError s!"unknown declaration '{declName}'"
    let value := mkConst declName (info.levelParams.map mkLevelParam)
    match info with
    | .thmInfo val =>
      addDecl (.thmDecl {
        name := aliasName
        levelParams := val.levelParams
        type := val.type
        value := value
      })
    | _ =>
      addDecl (.defnDecl {
        name := aliasName
        levelParams := info.levelParams
        type := info.type
        value := value
        hints := .abbrev
        safety := .safe
      })
    Elab.addDeclarationRangesFromSyntax aliasName stx rocqId
    let declIdent := mkIdent declName
    let depStx ← `(attr| deprecated $declIdent (since := "ported into iris-lean"))
    Attribute.add aliasName `deprecated depStx .global
}

/-- All `#transfinite_ignore` entries, as `(name, reason)` pairs. -/
public meta initialize transfiniteIgnoreExt :
    SimplePersistentEnvExtension (Name × String) (Array (Name × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun es => es.foldl (fun acc a => a.foldl Array.push acc) #[]
  }

/-- Ignore a name of Rocq Transfinite Iris, with a reason. -/
@[expose]
elab "#transfinite_ignore " id:ident ppSpace reason:str : command => do
  modifyEnv (transfiniteIgnoreExt.addEntry · (id.getId, reason.getString))
