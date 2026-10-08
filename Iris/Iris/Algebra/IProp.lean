/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus de Medeiros
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.OFE
public import Iris.Algebra.UPred
public import Iris.Algebra.GenMap
public import Iris.Algebra.COFESolverTransfinite
public import Iris.Algebra.ULift
public import Init.Data.Vector

@[expose] public section

universe u

namespace Iris

open COFE

abbrev GType := Nat

/-- A camera functor for ghost state. Its arguments and results are in `TypeSI u`, the universe
of `IProp`. -/
@[rocq_alias gFunctor]
abbrev GFunctor :=
  Σ F : (∀ (α β : TypeSI u) [COFE α] [COFE β], TypeSI u), RFunctorContractive F

@[rocq_alias gFunctors]
def BundledGFunctors := GType → GFunctor.{u}

def BundledGFunctors.default : BundledGFunctors := fun _ => ⟨constOFU Unit, by infer_instance⟩

def BundledGFunctors.set (GF : BundledGFunctors) (i : Nat) (FB : GFunctor) :
    BundledGFunctors :=
  fun j => if j = i then FB else GF j

#rocq_ignore gid "Use `GType` (= `Nat`) to index `BundledGFunctors` directly."
#rocq_ignore gFunctors.nil "`BundledGFunctors` is a function `GType → GFunctor`; no list combinators."
#rocq_ignore gFunctors.singleton "`BundledGFunctors` is a function `GType → GFunctor`; no list combinators."
#rocq_ignore gFunctors.app "`BundledGFunctors` is a function `GType → GFunctor`; no list combinators."

@[rocq_alias gname]
abbrev GName := Nat

#rocq_ignore gnameO "Use `LeibnizO GName`."

@[rocq_alias iResF]
abbrev IResF (GF : BundledGFunctors) : OFunctorPre :=
  DiscreteFunOF (fun i => GenMapOF (GF i).fst)

#rocq_ignore subG "Superseded by `ElemG`."
#rocq_ignore subG_inv "Lemma about `subG`; obsolete with `ElemG`."
#rocq_ignore subG_refl "Lemma about `subG`; obsolete with `ElemG`."
#rocq_ignore subG_app_l "Lemma about `subG`; obsolete with `ElemG`."
#rocq_ignore subG_app_r "Lemma about `subG`; obsolete with `ElemG`."

instance (GF : BundledGFunctors) (i : GName) : RFunctorContractive ((GF i).fst) := (GF i).snd

section IProp

variable (GF : BundledGFunctors.{u})

@[rocq_alias iProp_solution.iPrePropO, rocq_alias iProp_solution.iProp_result]
def IPre : TypeSI u := OFunctor.Transfinite.Fix (UPredOF (IResF GF))

@[rocq_alias iProp_solution.iPreProp_cofe]
noncomputable instance : COFE (IPre GF) := inferInstanceAs (COFE (OFunctor.Transfinite.Fix _))

@[rocq_alias iProp_solution.iResUR]
def IResUR : TypeSI u := (i : GType) → GenMap (GF i |>.fst (IPre GF) (IPre GF))

#rocq_ignore iResUR "Sealed copy of `iProp_solution.iResUR`; not needed since Lean does not seal it."

noncomputable instance : UCMRA (IResUR GF) :=
  ucmraDiscreteFunO (β := fun (i : GType) => GenMap (GF i |>.fst (IPre GF) (IPre GF)))

abbrev IProp : TypeSI u := UPred (IResUR GF)

@[rocq_alias iProp_solution.iProp_unfold]
noncomputable def IProp.unfold : IProp GF -n> IPre GF :=
  OFE.Iso.hom <| OFunctor.Transfinite.Fix.iso (F := (UPredOF (IResF GF)))

@[rocq_alias iProp_solution.iProp_fold]
noncomputable def IProp.fold : IPre GF -n> IProp GF :=
  OFE.Iso.inv <| OFunctor.Transfinite.Fix.iso (F := (UPredOF (IResF GF)))

@[rocq_alias iProp_solution.iProp_fold_unfold]
theorem IProp.fold_unfold (P : IProp GF) : IProp.fold GF (IProp.unfold GF P) = P :=
  OFunctor.Transfinite.Fix.iso (F := UPredOF (IResF GF)) |>.inv_hom

@[rocq_alias iProp_solution.iProp_unfold_fold]
theorem IProp.unfold_fold (P : IPre GF) : IProp.unfold GF (IProp.fold GF P) = P :=
  OFunctor.Transfinite.Fix.iso (F := UPredOF (IResF GF)) |>.hom_inv

end IProp

end Iris
