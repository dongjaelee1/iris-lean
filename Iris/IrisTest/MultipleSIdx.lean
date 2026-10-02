module

public import Iris.Algebra.StepIndexFinite

/-! Tests for the `linter.iris.multipleSIdx` linter. -/

namespace Iris.Test.MultipleSIdx

/--
warning: `two` has 2 step-index instances (`SIdx _` binders). `SIdx` has an outParam, so instance search only ever uses the last one; pass the others explicitly (e.g. as a non-class structure) or split the declaration.

Note: This linter can be disabled with `set_option linter.iris.multipleSIdx false`
-/
#guard_msgs in
theorem two {A B : Type} [SIdx A] [SIdx B] : True := trivial

-- Explicit binders of class type are local instances too.
/--
warning: `twoExplicit` has 2 step-index instances (`SIdx _` binders). `SIdx` has an outParam, so instance search only ever uses the last one; pass the others explicitly (e.g. as a non-class structure) or split the declaration.

Note: This linter can be disabled with `set_option linter.iris.multipleSIdx false`
-/
#guard_msgs in
theorem twoExplicit {A B : Type} [SIdx A] (_ : SIdx B) : True := trivial

-- One local instance next to the global `SIdx Nat` is fine.
#guard_msgs in
theorem one {A : Type} [SIdx A] : True := trivial

def Nat' := Nat

/--
warning: global `SIdx` instance `natSIdx'` is declared while `natSIdx` is active. `SIdx` has an outParam, so with two instances visible instance search picks one of them; make one of them `scoped`.

Note: This linter can be disabled with `set_option linter.iris.multipleSIdx false`
-/
#guard_msgs in
instance natSIdx' : SIdx Nat' := natSIdx

-- A `scoped` instance is the recommended way to add a second index type.
namespace Scoped
#guard_msgs in
scoped instance natSIdx'' : SIdx Nat' := natSIdx
end Scoped

end Iris.Test.MultipleSIdx
