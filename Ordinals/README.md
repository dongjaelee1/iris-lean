# Ordinals

A library of ordinals in Lean 4, without Mathlib (core Lean only). Iris uses it for the ordinal
step index (Transfinite Iris) and for the ordinal camera. Other projects can use it alone.

## Design

The library combines two Rocq libraries:

- [snu-sf/Ordinal](https://github.com/snu-sf/Ordinal): the representation as well-founded trees
  (`Ord.build`), transfinite recursion into other types (`Ord.rec`, `Ord.orec`), the standard
  arithmetic, the Hessenberg (natural) sum, the Jacobsthal product and power, Hartogs
  ordinals, classical recursion for chains and fixed points.
- [Transfinite Iris](https://github.com/dongjaelee1/transfinite-iris) (`stepindex/ordinals.v`):
  Leibniz equality of ordinals, universe polymorphism, the existential property and the
  ordinal camera.

There are two layers:

1. **Trees** (`Ordinals.OTree`, files `Ordinals/Tree/`): `inductive OTree | mk (ι : Type u) (f : ι → OTree)`.
   A tree represents its height. The order `≤`, `<` and the equivalence `≈` (same height) are
   defined by structural recursion. All operations are defined here, mostly by structural
   recursion, and each operation respects `≈`. Most results use no axioms.
2. **Ordinals** (`Ordinals.Ordinal`, files `Ordinals/Ordinal/`): `Ordinal.{u} := Quotient OTree.setoid`.
   Equality is Leibniz equality, so `rw` and `simp` work with the laws. The quotient needs only
   `propext` and `Quot.sound`. The linear order (totality, trichotomy, `min`, case analysis)
   uses excluded middle (`Classical.em`, a theorem of core Lean).

Lean has no cumulative universes. So `Ordinal.lift : Ordinal.{u} → Ordinal.{max u v}` maps
between universes. Its image is an initial segment (`lt_lift_iff`). `Ordinal.univ.{u} :
Ordinal.{u+1}` is above all lifted ordinals of `Ordinal.{u}` (`lift_lt_univ`).

## Contents

| File | Content |
|---|---|
| `Tree/Basic` | `OTree`, `≤`, `<`, `≈`, `lt_wf` |
| `Tree/Constructions` | `zero`, `succ`, `sup` (join), `mk` (strict join), `max`, `ofNat`, `omega`, `lift` |
| `Tree/Classical` | totality with excluded middle |
| `Tree/WellFounded`, `Tree/WfRel` | ordinals of well-founded relations, `hartogs`, `large`, projections and cuts |
| `Tree/Rec` | `trec` (snu-sf `Ord.rec`), `orec` |
| `Tree/ClassicalRec`, `Tree/Fixpoint` | classical recursion for chains, fixed-point theorem, `mu`, `nu` |
| `Tree/Arith` | `add`, `mul`, `pow` |
| `Tree/Hessenberg`, `Tree/HessenbergArith` | natural sum `nadd` |
| `Tree/Jacobsthal` | Jacobsthal product `jmul` and power `jpow` |
| `Ordinal/Basic` | `Ordinal`, the order, `Std.IsLinearOrder` (so `grind` works), well-founded induction |
| `Ordinal/Constructions` | `0`, `succ`, `sup`, `ssup`, `max`, `min`, natural numbers, `ω`, `IsLimit`, `limitInduction` |
| `Ordinal/Lift` | `lift`, `univ` |
| `Ordinal/Arith` | `a + b`, `a * b`, `a ^ b` |
| `Ordinal/Natural` | natural sum `a +ₕ b` (scoped), `NatOrdinal` (`+` is `+ₕ`) |
| `Ordinal/Jacobsthal` | `a ×ⱼ b`, `a ^ⱼ b` (scoped) |
| `Ordinal/Rec` | `orec` with equations |
| `Ordinal/WellFounded` | `ofWf`, `type`, `hartogs`, `large_eq_univ` |

The Iris module `Iris/Algebra/OrdinalCamera.lean` gives the camera on `NatOrdinal`.

## Notes

- The power follows snu-sf: `0 ^ b = 1` for each `b` (`zero_pow`); `pow_succ`, `pow_add`,
  `pow_mul` need `0 < a`. The same holds for `^ⱼ`.
- snu-sf proves the distributivity of `×ⱼ` over `+ₕ` classically; here the proof is constructive.
- The names of the Rocq lemmas are in the docstrings.

## Build

```
lake build --wfail
lake test
```
