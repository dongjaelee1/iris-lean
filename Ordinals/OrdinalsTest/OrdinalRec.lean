module

public import Ordinals

/-! Tests for transfinite recursion on the quotient layer. -/

open Ordinals Ordinal

example (a b : Ordinal) : orec a succ b = a + b := orec_succ_eq_add a b

example (a : Ordinal) : orec 0 succ a = a := orec_zero_succ a

example (base a : Ordinal) :
    orec base (fun x => x + x) (succ a) = orec base (fun x => x + x) a + orec base (fun x => x + x) a :=
  orec_succ (fun h => Ordinal.add_le_add h h) (fun x => Ordinal.le_add_right x x) a
