module

public import Ordinals

/-! Tests for the tree layer. -/

open Ordinals

/-- info: 'Ordinals.OTree.lt_wf' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.lt_wf

/-- info: 'Ordinals.OTree.lift_sup' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.lift_sup

/-- info: 'Ordinals.OTree.ofNat_le_ofNat_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms OTree.ofNat_le_ofNat_iff
