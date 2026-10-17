# Transfinite Iris-Lean: one ordinal step index for the whole build

- **Fork:** [dongjaelee1/iris-lean](https://github.com/dongjaelee1/iris-lean), branch
  [`transfinite`](https://github.com/dongjaelee1/iris-lean/tree/transfinite)
- **Baseline:** upstream Iris-Lean `81bc350` (#688), the upstream commit that the branch contains
- **Measured:** 2026-10-17, branch at `a85e593`, Lean 4.34.1

## Summary

The `transfinite` branch ports [Transfinite Iris](https://github.com/dongjaelee1/transfinite-iris)
(Spies et al., PLDI 2021) to Iris-Lean, with ordinals as step indices. It takes the extreme design:
the whole build has **one** step-index type, `Iris.SI := Ordinals.Ordinal.{3}`, and no definition
or lemma has a step-index parameter.

This is not a proposal for upstream. Upstream wants several step-index instances in one build, and
this design gives that up. The branch is a reference point: it shows the cost of transfinite step
indices when the index is fixed.

Against upstream, which uses `Nat`:

| | Change |
|---|---:|
| Clean build of the Iris package, wall time | +4.3% |
| Clean build, CPU time (with the new `Ordinals` package) | +9.2% |
| Library modules that are in both trees | +3.6% |
| HeapLang library proofs (the files closest to client proofs) | +4.0% |
| Tests that are in both trees | +2.2% |
| Peak memory | no change |

Half of the extra library time is in new modules, mostly the transfinite COFE solver (10 s). The
other half is +3.6% over the existing modules, spread thinly (median +1.7% per module).

Upstream #688 (ordered resource algebras) makes both trees about 6% slower. It does not change the
difference: before #688, the modules in both trees also took +3.6%.

These numbers cover all changes of the branch: the step index, the transfinite model and the new
rules, not only the fixed index.

## Design

### One step-index type per build

One file, `Iris/Iris/Algebra/StepIndexChoice.lean`, sets the index of the whole build:

```lean
def SI : Type 4 := Ordinals.Ordinal.{3}

instance instSIdxSI : SIdx SI := ordinalSIdx
instance instSIdxTransfiniteSI : SIdxTransfinite SI := ordinalSIdxTransfinite
instance instSIdxLargeSI3 {X : Type 3} : SIdxLarge SI X := ordinalSIdxLarge
-- also SIdxLarge for Type 0 to Type 2, and the universe macros TypeSI and levelSI%
```

The library uses `SI` where upstream uses `Nat`:

```lean
class OFE (α : Type _) where
  Dist : SI → α → α → Prop        -- upstream: Dist : Nat → α → α → Prop
```

- `SI` is a `def`, not an `abbrev`. So the proofs see only the `SIdx` interface (the order, the
  successor, well-foundedness, and the case split into zero, successor and limit), never the
  ordinals themselves.
- A proof that needs a finite index takes `[SIdxFinite SI]`. The ordinal build has no such
  instance, so these rules exist but cannot be used.
- Client code does not change: there are no step-index binders, annotations or scoped commands.
- The same library also builds at `Nat`: `scripts/stepindex.sh nat` selects the stored Nat choice.

### Resource algebras

Upstream's ordered resource algebras (#688) state three axioms with the successor index `n + 1`.
A chain of successors never reaches a limit index, so here these axioms hold for each index:

```lean
validN_le : ✓{n} x → n' ≤ n → ✓{n'} x              -- upstream: ✓{n + 1} x → ✓{n} x
ordN_le   : x ≼ₒ{n} y → n' ≤ n → x ≼ₒ{n'} y        -- upstream: x ≼ₒ{n + 1} y → x ≼ₒ{n} y
ord_extend : ✓{n} y → x ≼ₒ{n} y → ∃ z, z ≼ₒ y ∧ z ≡{n}≡ x
  -- upstream: ordN_extend, with z ≼ₒ{n + 1} y
```

Upstream's forms are derived lemmas. `ownM_timeless` and `later_false_impl_sep` need the exact
`ord_extend`, because they lift an order from index 0 to each index. Each instance proves
`ord_extend` in the same way as upstream proves `ordN_extend`.

### Transfinite Iris on top

- **Model.** `IProp` uses the transfinite COFE solver, ported from upstream PR #709. The solver is
  noncomputable, so 78 library files are `noncomputable section` (upstream: 3).
- **Later laws.** They follow Rocq Iris MR
  [!1256](https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/1256). `later_sep_1` and
  `later_sExists_false` need a finite index. The new laws `later_false_impl_sExists` and
  `later_false_impl_sep` hold for every index. `Timeless P` means `<only0> P ⊢ P`.
- **Rules that need a finite index**, as in Rocq Transfinite Iris: `inv_alter`, `inv_combine`,
  `inv_split`; `inv_acc` of non-atomic invariants; the rules of boxes; `later_exists`,
  `later_sep` and the other laws that come from `later_sep_1` or `later_sExists_false`;
  `Laterable`; the finite COFE solver.
- **Cancelable invariants** are `inv N (P ∨ own γ 1)`, as in Transfinite Iris.
- **HeapLang.** The heap tactics split the context before they remove `▷`. New rules
  `wp_load_later`, `wp_store_later`, `wp_cmpXchg_later` and `wp_faa_later` keep the
  specifications of the HeapLang library the same.
- **Ordinals.** A new package `Ordinals/` (core Lean only, no Mathlib): ordinals as a quotient of
  well-founded trees, so equality is Leibniz equality; a linear order; the standard and the
  natural (Hessenberg) arithmetic; Jacobsthal operations; `lift` and `univ` between universes.
- **Three levels of ordinals.** With `Ordinal.{3}`, the ordinals of `Ordinal.{0}`, `Ordinal.{1}`
  and `Ordinal.{2}` lift into the index. The existential property of Transfinite Iris
  (`SIdxLarge SI X`) holds for quantifiers over each level.
- **Also new:** the ordinal resource algebra, satisfiability, the big later `⧍`.

Against upstream, 142 of 292 library files change (+6.6k / −1.7k lines), and there are 12 new
library modules. The `Ordinals` package adds 6.3k lines with its tests.

## Performance

### Method

- **Per file:** `lean --profile` on each library and test file, with the dependencies already
  built, one thread. CPU time is user + sys. *Own time* is the CPU time without the time to import
  the dependencies. Three alternating rounds per tree, and per file the minimum. The round totals
  vary by 0.1%. Per file the rounds vary by 0.7% (median) and by 1.5% for one file in ten, so
  read differences under about 2% for one file as noise.
- **Clean build:** `lake build` of the Iris package with `LEAN_NUM_THREADS=6`, two alternating runs
  per tree, the faster one.
- **Machine:** Linux x86-64, 36 cores, shared but lightly loaded. We measured CPU time, not
  instruction counts (this machine has no `perf`).

All tables are in [transfinite-bench/results-2026-10-17.md](transfinite-bench/results-2026-10-17.md).

### Whole build

| | Upstream | Transfinite | Change |
|---|---:|---:|---:|
| Clean build, wall time (s) | 121.0 | 126.2 | +4.3% |
| Clean build, CPU time (s) | 510.8 | 557.6 | +9.2% |
| Clean build, peak memory of one process (MB) | 1224 | 1223 | −0.1% |
| Library modules | 281 | 293 | +12 |
| Library, own time, one thread (s) | 331.0 | 356.1 | +7.6% |
| Tests in both trees, own time (s) | 18.6 | 19.0 | +2.2% |
| `.olean` size (MB) | 71.0 | 73.8 | +3.9% |

The clean build of the branch also builds the `Ordinals` package: 21 modules, 5.5 s own time,
1.2 MB of `.olean`.

### Where the extra library time is

The library's own time grows by 25.1 s:

- **New modules: 13.2 s.** The transfinite COFE solver takes 10.1 s. The other 11 new modules
  (index structures, truncation, `ULift`, transfinite facts about the BI and `UPred`, porting
  attributes, a linter) take 3.1 s together.
- **Modules in both trees: +11.9 s (+3.6%):**

| Layer | Modules | Upstream (s) | Transfinite (s) | Change |
|---|---:|---:|---:|---:|
| Std | 39 | 20.6 | 20.6 | +0.1% |
| Algebra | 46 | 69.6 | 73.2 | +5.2% |
| BI | 48 | 55.7 | 57.2 | +2.6% |
| ProofMode | 60 | 46.7 | 47.3 | +1.3% |
| Instances | 27 | 30.2 | 32.0 | +6.1% |
| ProgramLogic | 18 | 22.8 | 23.6 | +3.4% |
| HeapLang (without `Lib`) | 14 | 64.9 | 67.7 | +4.4% |
| HeapLang `Lib` | 19 | 17.7 | 18.5 | +4.0% |
| Examples and other | 10 | 2.8 | 2.8 | +2.0% |
| **All** | **281** | **331.0** | **342.9** | **+3.6%** |

In these modules, the extra time is in these profiler categories:

| Category | Change |
|---|---:|
| interpretation (tactics and other meta code that runs interpreted) | +4.5 s (+10.9%) |
| unaccounted ("blocked") | +3.4 s (+3.2%) |
| typeclass inference (+1.0 s of it in the proof mode) | +3.2 s (+5.5%) |
| elaboration | +1.3 s (+2.6%) |
| tactic execution | +1.0 s (+2.3%) |
| type checking (kernel) | +0.6 s (+3.5%) |
| simp | +0.4 s (+1.3%) |
| compilation | −0.1 s (−0.5%) |

Per module, the change is small for most files: median +1.7%, quartiles +0.6% and +3.7% (154
modules of more than 0.5 s). The largest changes have clear causes:

| Module | Upstream (s) | Transfinite (s) | Change | Cause |
|---|---:|---:|---:|---|
| `HeapLang.PrimitiveLaws` | 3.66 | 4.97 | +1.31 s | 4 new rules (`wp_load_later`, ...) and a helper |
| `HeapLang.ProofMode` | 6.48 | 7.48 | +1.01 s | the heap tactics split the context first |
| `Algebra.OFE` | 4.43 | 5.38 | +0.94 s | bounded limits for limit indices (26 declarations, from #709) |
| `Algebra.CMRA` | 9.60 | 10.32 | +0.71 s | `SIdx` lemmas in place of `Nat` arithmetic; the derived lemmas of #688's axioms |
| `Instances.Lib.NaInvariants` | 0.83 | 1.40 | +0.57 s | new rules (`inv_acc_open`, ...) |
| `Instances.IProp.Instance` | 4.40 | 4.86 | +0.46 s | `ElemG` as an isomorphism of resource algebras (from #709) |
| `Algebra.StepIndex` | 0.46 | 0.80 | +0.34 s | more step-index lemmas |
| `Instances.Lib.CInvariants` | 1.19 | 0.91 | −0.28 s | the smaller Transfinite Iris representation |

The `multipleSIdx` linter (from upstream PR #627, in this branch) costs about 3 s. With the linter
off, `interpretation` drops by 2.7 s, and the modules in both trees take +2.7% instead of +3.6%.

### HeapLang library proofs

These 19 files use the program logic as a client does. Together they take 17.7 s upstream and
18.5 s here (+4.0%). Per file the change is from −1.0% (`TicketLock`) to +9.5% (`Counter`). The
import time per file is 0.40 s upstream and 0.41 s here.

<details>
<summary>Per file</summary>

| File | Upstream (s) | Transfinite (s) | Change |
|---|---:|---:|---:|
| `Arith` | 0.34 | 0.35 | +2.7% |
| `Array` | 1.58 | 1.64 | +4.3% |
| `Assert` | 0.17 | 0.17 | +4.6% |
| `ClairvoyantCoin` | 0.56 | 0.59 | +4.6% |
| `Counter` | 1.63 | 1.79 | +9.5% |
| `Diverge` | 0.14 | 0.15 | +4.0% |
| `LandinsKnot` | 0.39 | 0.42 | +6.9% |
| `LazyCoin` | 0.55 | 0.57 | +4.1% |
| `Lock` | 0.36 | 0.38 | +6.4% |
| `NondetBool` | 0.29 | 0.30 | +4.3% |
| `Par` | 0.40 | 0.41 | +2.5% |
| `Quicksort` | 5.39 | 5.53 | +2.6% |
| `RwLock` | 0.44 | 0.47 | +6.6% |
| `RwSpinLock` | 2.28 | 2.41 | +5.7% |
| `Spawn` | 0.57 | 0.61 | +6.0% |
| `SpinLock` | 0.71 | 0.74 | +3.7% |
| `TicketLock` | 1.71 | 1.69 | −1.0% |
| `Unwrap` | 0.16 | 0.16 | +2.1% |
| `Lib` (imports only) | 0.10 | 0.10 | +3.4% |

</details>

### Tests, memory and size

- **Tests:** the 26 test files in both trees take 18.6 s upstream and 19.0 s here (+2.2%). The
  largest, `IrisTest.Tactics` (8 s), changes by +1.3%. (`IrisTest.Linter` is left out: it needs
  the options of the lakefile.)
- **Memory:** the peak memory per module is almost the same: median 758 MB upstream and 752 MB
  here, maximum 1.23 GB and 1.28 GB (`HeapLang.ProphErasure`).
- **Import time:** 0.31 s per module upstream, 0.32 s here.
- **Size:** `.lean` lines of the Iris package +5.1% (98.9k to 103.9k); `.olean` +3.9%.

## Limits

- One step index for each build: a project cannot use two indices, and a change of index means a
  new build of Iris.
- At the ordinal index, the rules that need a finite index (see above) cannot be used.
- `IProp` is noncomputable, so client definitions that compute with it must be `noncomputable`.
- Not ported: the refinement logic and the time credits of Transfinite Iris. Later credits `£ n`
  count with `Nat`.

## Reproduce

```sh
git clone -b transfinite https://github.com/dongjaelee1/iris-lean tf
git clone https://github.com/leanprover-community/iris-lean up && git -C up checkout 81bc350
for d in tf up; do (cd $d/Iris && lake build && lake build IrisTest); done
TF=$PWD/tf UP=$PWD/up tf/docs/transfinite-bench/measure.sh results   # about 50 minutes
python3 tf/docs/transfinite-bench/analyze.py results                   # writes results/summary-TF.md
```

`measure.sh` ends with clean builds, so it deletes and rebuilds `Iris/.lake/build` in both trees.
