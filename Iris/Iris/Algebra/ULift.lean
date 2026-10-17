/-
Copyright (c) The Iris-Lean Contributors
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iris-Lean Contributors
-/
module

public import Iris.Algebra.CMRA
public import Iris.Algebra.Updates

/-! # Resource algebras on `ULift`

`ULift α` inherits the structure of `α`. This lifts ghost state in `Type` (for example masks) to
the universe of the resources of `IProp`, which is not `Type` for step-index types in higher
universes (for example ordinals).
-/

@[expose] public section

namespace Iris
open OFE ORA

namespace ULift

@[reducible] def raOp [OFE α] [Op α] : Op (ULift α) where
  op x y := ⟨x.down • y.down⟩
  op_ne {x} := ⟨fun _ _ _ h => (Op.op_ne (x := x.down)).ne h⟩
  assoc {x y z} := congrArg ULift.up (Op.assoc (x := x.down) (y := y.down) (z := z.down))
  comm {x y} := congrArg ULift.up (Op.comm (x := x.down) (y := y.down))

@[reducible] def raPCore [OFE α] [PCore α] : PCore (ULift α) where
  pcore x := (PCore.pcore x.down).map ULift.up
  pcore_ne {n x y cx} h e := by
    cases hx : PCore.pcore x.down with
    | none => simp [hx] at e
    | some cx' =>
      simp only [hx, Option.map_some, Option.some.injEq] at e
      subst e
      obtain ⟨cy, hy, hc⟩ := PCore.pcore_ne (x := x.down) h hx
      exact ⟨⟨cy⟩, by simp [hy], hc⟩
  pcore_idem {x cx} e := by
    cases hx : PCore.pcore x.down with
    | none => simp [hx] at e
    | some cx' =>
      simp only [hx, Option.map_some, Option.some.injEq] at e
      subst e
      change Option.map ULift.up (PCore.pcore cx') = _
      rw [PCore.pcore_idem hx]
      rfl

@[reducible] def raValid [OFE α] [Valid α] : Valid (ULift α) where
  ValidN n x := ✓{n} x.down
  Valid x := ✓ x.down
  validN_ne h hv := Valid.validN_ne (x := _) h hv
  valid_iff_validN := Valid.valid_iff_validN
  validN_le := Valid.validN_le

@[reducible] def raOrdered [OFE α] [Ordered α] : Ordered (ULift α) where
  OrderN n x y := x.down ≼ₒ{n} y.down
  Order x y := x.down ≼ₒ y.down
  ordN_ne ex ey h := Ordered.ordN_ne ex ey h
  ordN_le := Ordered.ordN_le
  ordN_trans := Ordered.ordN_trans
  ord_trans := Ordered.ord_trans
  ordN_of_ord n h := Ordered.ordN_of_ord n h

attribute [local instance] raOp raPCore raValid raOrdered

theorem pcore_eq [OFE α] [PCore α] (x : ULift α) :
    PCore.pcore x = (PCore.pcore x.down).map ULift.up := rfl

theorem increasing_up [OFE α] [Op α] [Ordered α] {x : α} (h : Increasing x) :
    Increasing (ULift.up x : ULift α) :=
  ⟨fun y => h.increasing y.down⟩

theorem increasing_down [OFE α] [Op α] [Ordered α] {x : ULift α} (h : Increasing x) :
    Increasing x.down :=
  ⟨fun y => h.increasing ⟨y⟩⟩

instance instORA [ORA α] : ORA (ULift α) where
  toOp := raOp
  toPCore := raPCore
  toValid := raValid
  toOrdered := raOrdered
  validN_op_left := validN_op_left (α := α)
  pcore_op_left {x cx} e := by
    cases hx : pcore x.down with
    | none => simp [pcore_eq, hx] at e
    | some cx' =>
      simp only [pcore_eq, hx, Option.map_some, Option.some.injEq] at e
      subst e
      exact congrArg ULift.up (pcore_op_left hx)
  extend {n x y₁ y₂} hv h :=
    let ⟨z₁, z₂, hx, h₁, h₂⟩ := extend (x := x.down) hv h
    ⟨⟨z₁⟩, ⟨z₂⟩, congrArg ULift.up hx, h₁, h₂⟩
  op_monoN_left_ord z h := op_monoN_left_ord (α := α) z.down h
  op_mono_left_ord z h := op_mono_left_ord (α := α) z.down h
  validN_of_ordN h v := validN_of_ordN (α := α) h v
  pcore_monoN_ord {n x y cx} h e := by
    cases hx : pcore x.down with
    | none => simp [pcore_eq, hx] at e
    | some cx' =>
      simp only [pcore_eq, hx, Option.map_some, Option.some.injEq] at e
      subst e
      obtain ⟨cy, hcy, hc⟩ := pcore_monoN_ord (α := α) h hx
      exact ⟨⟨cy⟩, by simp [pcore_eq, hcy], hc⟩
  pcore_mono_ord {x y cx} h e := by
    cases hx : pcore x.down with
    | none => simp [pcore_eq, hx] at e
    | some cx' =>
      simp only [pcore_eq, hx, Option.map_some, Option.some.injEq] at e
      subst e
      obtain ⟨cy, hcy, hc⟩ := pcore_mono_ord (α := α) h hx
      exact ⟨⟨cy⟩, by simp [pcore_eq, hcy], hc⟩
  pcore_order_op {x cx} e y := by
    cases hx : pcore x.down with
    | none => simp [pcore_eq, hx] at e
    | some cx' =>
      simp only [pcore_eq, hx, Option.map_some, Option.some.injEq] at e
      subst e
      obtain ⟨cxy, hcxy, hc⟩ := pcore_order_op hx y.down
      refine ⟨⟨cxy⟩, ?_, hc⟩
      change (pcore (x.down • y.down)).map ULift.up = _
      rw [hcxy]; rfl
  pcore_increasing {x cx} e := by
    cases hx : pcore x.down with
    | none => simp [pcore_eq, hx] at e
    | some cx' =>
      simp only [pcore_eq, hx, Option.map_some, Option.some.injEq] at e
      subst e
      exact increasing_up (pcore_increasing hx)
  increasing_closed h h' := increasing_up (increasing_closed (increasing_down h) h')
  ord_extend {n x y} v h :=
    let ⟨z, hz, ez⟩ := ord_extend (x := x.down) v h
    ⟨⟨z⟩, hz, ez⟩

instance instIncOrd [ORA α] [IncOrd α] : IncOrd (ULift α) where
  inc_ord {x _} := fun ⟨z, e⟩ => IncOrd.inc_ord (x := x.down) ⟨z.down, congrArg ULift.down e⟩

instance instOrdInc [ORA α] [OrdInc α] : OrdInc (ULift α) where
  ord_inc {x y} h := let ⟨z, e⟩ := OrdInc.ord_inc (x := x.down) (y := y.down) h
    ⟨⟨z⟩, congrArg ULift.up e⟩
  ordN_incN {_ x y} h := let ⟨z, e⟩ := OrdInc.ordN_incN (x := x.down) (y := y.down) h; ⟨⟨z⟩, e⟩

instance instCMRA [CMRA α] : CMRA (ULift α) := {}

instance instOrderRefl [ORA α] [OrderRefl α] : OrderRefl (ULift α) where
  ord_refl x := OrderRefl.ord_refl x.down

theorem up_op [ORA α] (a b : α) : (ULift.up (a • b) : ULift α) = ULift.up a • ULift.up b := rfl

theorem valid_up [ORA α] {a : α} : ✓ (ULift.up a : ULift α) ↔ ✓ a := Iff.rfl

theorem validN_up [ORA α] {n : SI} {a : α} : ✓{n} (ULift.up a : ULift α) ↔ ✓{n} a := Iff.rfl

theorem updateP [ORA α] {a : α} {P : α → Prop} (h : a ~~>: P) :
    (ULift.up a : ULift α) ~~>: fun y => P y.down := by
  intro n mz hv
  obtain ⟨y, hy, hvy⟩ := h n (mz.map ULift.down) (by cases mz <;> exact hv)
  exact ⟨⟨y⟩, hy, by cases mz <;> exact hvy⟩

theorem update [ORA α] {a b : α} (h : a ~~> b) : (ULift.up a : ULift α) ~~> ULift.up b := by
  intro n mz hv
  have := h n (mz.map ULift.down) (by cases mz <;> exact hv)
  cases mz <;> exact this

instance instUORA [UORA α] : UORA (ULift α) where
  unit := ⟨UORA.unit⟩
  unit_valid := UORA.unit_valid (α := α)
  unit_left_id {x} := congrArg ULift.up (UORA.unit_left_id (x := x.down))
  pcore_unit := by
    change Option.map ULift.up (pcore (UORA.unit : α)) = _
    rw [UORA.pcore_unit]
    rfl

instance instOFEDiscrete [OFE α] [OFE.Discrete α] : OFE.Discrete (ULift α) where
  discrete_0 h := congrArg ULift.up (OFE.Discrete.discrete_0 h)

instance instDiscrete [ORA α] [ORA.Discrete α] : ORA.Discrete (ULift α) where
  discrete_valid h := ORA.Discrete.discrete_valid (α := α) h
  discrete_ord h := ORA.Discrete.discrete_ord (α := α) h

instance instDiscreteE [OFE α] {a : α} [OFE.DiscreteE a] : OFE.DiscreteE (ULift.up a) where
  discrete h := congrArg ULift.up (OFE.DiscreteE.discrete h)

instance instCoreId [ORA α] {a : α} [h : ORA.CoreId a] : ORA.CoreId (ULift.up a) where
  core_id := by
    change Option.map ULift.up (pcore a) = _
    rw [h.core_id]
    rfl

end ULift

/-- The homomorphism lifting `f : α -C> β` to `ULift`. -/
def ORA.Hom.ulift [ORA α] [ORA β] (f : α -C> β) : ULift.{w} α -C> ULift.{w} β where
  f x := ⟨f x.down⟩
  ne := ⟨fun _ _ _ h => f.ne.ne h⟩
  validN h := f.validN h
  pcore x := by
    change Option.map _ (Option.map ULift.up (pcore x.down)) =
      Option.map ULift.up (pcore (f x.down))
    rw [← f.pcore]
    cases pcore x.down <;> rfl
  op x y := congrArg ULift.up (f.op x.down y.down)
  monoN_ord h := f.monoN_ord h
  mono_ord h := f.mono_ord h
  increasing h := ULift.increasing_up (f.increasing (ULift.increasing_down h))

/-- `ULift.up` as a homomorphism. -/
def ULift.upC [ORA α] : α -C> ULift.{w} α where
  toHom := OFE.uliftUpHom
  validN h := h
  pcore _ := rfl
  op _ _ := rfl
  monoN_ord h := h
  mono_ord h := h
  increasing h := ULift.increasing_up h

/-- `ULift.down` as a homomorphism. -/
def ULift.downC [ORA α] : ULift.{w} α -C> α where
  toHom := OFE.uliftDownHom
  validN h := h
  pcore x := by
    change Option.map _ (Option.map ULift.up (pcore x.down)) = pcore x.down
    cases pcore x.down <;> rfl
  op _ _ := rfl
  monoN_ord h := h
  mono_ord h := h
  increasing h := ULift.increasing_down h

open COFE in
instance COFE.OFunctor.constOFU_RFunctor [ORA B] : RFunctor (constOFU.{w} B) where
  cmra := inferInstance
  map _ _ := (ORA.Hom.id : ULift.{w} B -C> ULift.{w} B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

instance OFunctor.constOFU_RFunctorContractive [ORA B] :
    RFunctorContractive (constOFU.{w} B) where
  map_contractive.1 := fun _ => .rfl

instance OFunctor.constOFU_RFunctorAffine [ORA B] [IncOrd B] : RFunctorAffine (constOFU.{w} B) where
  affine := ULift.instIncOrd

open COFE in
instance COFE.OFunctor.constOFU_URFunctor [UORA B] : URFunctor (constOFU.{w} B) where
  cmra := inferInstance
  map _ _ := (ORA.Hom.id : ULift.{w} B -C> ULift.{w} B)
  map_ne.ne _ _ _ _ _ _ _ := .rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ := rfl

instance OFunctor.constOFU_URFunctorContractive [UORA B] :
    URFunctorContractive (constOFU.{w} B) where
  map_contractive.1 _ := .rfl

open COFE in
/-- A resource functor lifted to the universe `w`: ghost state in `Type` in the resources of
`IProp` over a step-index type in a higher universe. -/
abbrev ULiftOF.{w} (F : OFunctorPre) : OFunctorPre := fun α β _ _ => ULift.{w} (F α β)

open COFE in
instance ULiftOF.instRFunctor [RFunctor F] : RFunctor (ULiftOF.{w} F) where
  cmra := inferInstance
  map f g := (RFunctor.map (F := F) f g).ulift
  map_ne.ne _ _ _ h _ _ h' x := (RFunctor.map_ne (F := F)).ne h h' x.down
  map_id x := congrArg ULift.up (RFunctor.map_id (F := F) x.down)
  map_comp f g f' g' x := congrArg ULift.up (RFunctor.map_comp (F := F) f g f' g' x.down)

open COFE in
instance ULiftOF.instRFunctorContractive [RFunctorContractive F] :
    RFunctorContractive (ULiftOF.{w} F) where
  map_contractive.1 h x := (RFunctorContractive.map_contractive (F := F)).1 h x.down

instance ULiftOF.instRFunctorAffine [RFunctor F] [RFunctorAffine F] :
    RFunctorAffine (ULiftOF.{w} F) where
  affine := ULift.instIncOrd

end Iris
