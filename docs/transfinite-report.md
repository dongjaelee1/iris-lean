# Transfinite Iris-Lean: one ordinal step index for the whole build

- **Fork:** [dongjaelee1/iris-lean](https://github.com/dongjaelee1/iris-lean), branch
  [`transfinite`](https://github.com/dongjaelee1/iris-lean/tree/transfinite)
- **Baseline:** upstream Iris-Lean `0533d02` (#717), the upstream commit that the branch contains
- **Measured:** 2026-10-16, branch at `fdc7402`, Lean 4.34.1

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
| Clean build of the Iris package, wall time | +6.2% |
| Clean build, CPU time (with the new `Ordinals` package) | +9.6% |
| Library modules that are in both trees | +3.6% |
| HeapLang library proofs (the files closest to client proofs) | +3.5% |
| Tests that are in both trees | +2.5% |
| Peak memory | no change |

Half of the extra library time is in new modules, mostly the transfinite COFE solver (10 s). The
other half is +3.6% over the existing modules, spread thinly (median +1.5% per module).

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

### Transfinite Iris on top

- **Model.** `IProp` uses the transfinite COFE solver, ported from upstream PR #709. The solver is
  noncomputable, so 77 library files are `noncomputable section` (upstream: 3).
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
- **Also new:** the ordinal camera, satisfiability, the big later `⧍`.

Against upstream, 142 of 292 library files change (+6.4k / −1.7k lines), and there are 12 new
library modules. The `Ordinals` package adds 6.3k lines with its tests.

## Performance

### Method

- **Per file:** `lean --profile` on each library and test file, with the dependencies already
  built, one thread. CPU time is user + sys. *Own time* is the CPU time without the time to import
  the dependencies. Three alternating rounds per tree (upstream: four), and per file the minimum.
  The round totals vary by 1.8% (upstream) and 2.8% (transfinite), so read differences under
  about 2% as noise.
- **Clean build:** `lake build` of the Iris package with `LEAN_NUM_THREADS=6`, two alternating runs
  per tree, the faster one.
- **Machine:** Linux x86-64, 36 cores, shared but lightly loaded. We measured CPU time, not
  instruction counts (this machine has no `perf`).

All tables are in [transfinite-bench/results-2026-10-16.md](transfinite-bench/results-2026-10-16.md).

### Whole build

| | Upstream | Transfinite | Change |
|---|---:|---:|---:|
| Clean build, wall time (s) | 118.1 | 125.4 | +6.2% |
| Clean build, CPU time (s) | 489.1 | 536.1 | +9.6% |
| Clean build, peak memory of one process (MB) | 1200 | 1204 | +0.4% |
| Library modules | 281 | 293 | +12 |
| Library, own time, one thread (s) | 311.7 | 335.9 | +7.8% |
| Tests in both trees, own time (s) | 18.3 | 18.8 | +2.5% |
| `.olean` size (MB) | 68.3 | 71.0 | +3.9% |

The clean build of the branch also builds the `Ordinals` package: 21 modules, 5.5 s own time,
1.2 MB of `.olean`.

### Where the extra library time is

The library's own time grows by 24.2 s:

- **New modules: 12.8 s.** The transfinite COFE solver takes 10.1 s. The other 11 new modules
  (index structures, truncation, transfinite facts about the BI and `UPred`, porting attributes,
  a linter) take 2.7 s together.
- **Modules in both trees: +11.4 s (+3.6%):**

| Layer | Modules | Upstream (s) | Transfinite (s) | Change |
|---|---:|---:|---:|---:|
| Std | 39 | 20.6 | 20.6 | +0.2% |
| Algebra | 46 | 54.3 | 57.4 | +5.8% |
| BI | 48 | 54.6 | 56.1 | +2.7% |
| ProofMode | 60 | 46.7 | 47.4 | +1.3% |
| Instances | 27 | 28.5 | 30.4 | +6.6% |
| ProgramLogic | 18 | 22.4 | 23.3 | +3.9% |
| HeapLang (without `Lib`) | 14 | 64.7 | 67.3 | +4.1% |
| HeapLang `Lib` | 19 | 17.3 | 17.9 | +3.5% |
| Examples and other | 10 | 2.6 | 2.7 | +3.0% |
| **All** | **281** | **311.7** | **323.1** | **+3.6%** |

In these modules, the extra time is in these profiler categories:

| Category | Change |
|---|---:|
| interpretation (tactics and other meta code that runs interpreted) | +4.2 s (+10.7%) |
| typeclass inference (+0.9 s of it in the proof mode) | +2.9 s (+5.9%) |
| unaccounted ("blocked") | +2.1 s (+2.1%) |
| elaboration | +1.3 s (+3.0%) |
| tactic execution | +0.9 s (+2.2%) |
| type checking (kernel) | +0.6 s (+3.6%) |
| simp | +0.4 s (+1.2%) |
| compilation | −0.1 s (−0.5%) |

Per module, the change is small for most files: median +1.5%, quartiles +0.7% and +3.8% (153
modules of more than 0.5 s). The largest changes have clear causes:

| Module | Upstream (s) | Transfinite (s) | Change | Cause |
|---|---:|---:|---:|---|
| `HeapLang.PrimitiveLaws` | 3.33 | 4.60 | +1.26 s | 4 new rules (`wp_load_later`, ...) and a helper |
| `HeapLang.ProofMode` | 6.49 | 7.47 | +0.98 s | the heap tactics split the context first |
| `Algebra.OFE` | 4.45 | 5.42 | +0.96 s | bounded limits for limit indices (26 declarations, from #709) |
| `Instances.Lib.NaInvariants` | 0.78 | 1.33 | +0.54 s | new rules (`inv_acc_open`, ...) |
| `Instances.IProp.Instance` | 3.51 | 4.02 | +0.51 s | `ElemG` as a camera isomorphism (from #709) |
| `Algebra.StepIndex` | 0.46 | 0.80 | +0.34 s | more step-index lemmas |
| `Instances.Lib.CInvariants` | 1.12 | 0.87 | −0.24 s | the smaller Transfinite Iris representation |

The `multipleSIdx` linter (from upstream PR #627, in this branch) costs less than the noise:
with the linter off, `interpretation` drops by 1.7 s, and the totals do not change measurably.

### HeapLang library proofs

These 19 files use the program logic as a client does. Together they take 17.3 s upstream and
17.9 s here (+3.5%). Per file the change is from −2.2% (`TicketLock`) to +8.9% (`Counter`). The
import time per file is 0.40 s upstream and 0.41 s here.

<details>
<summary>Per file</summary>

| File | Upstream (s) | Transfinite (s) | Change |
|---|---:|---:|---:|
| `Arith` | 0.33 | 0.34 | +3.8% |
| `Array` | 1.57 | 1.61 | +2.9% |
| `Assert` | 0.17 | 0.17 | +2.0% |
| `ClairvoyantCoin` | 0.56 | 0.58 | +4.0% |
| `Counter` | 1.51 | 1.64 | +8.9% |
| `Diverge` | 0.14 | 0.15 | +2.9% |
| `LandinsKnot` | 0.39 | 0.42 | +7.7% |
| `LazyCoin` | 0.54 | 0.56 | +3.4% |
| `Lock` | 0.35 | 0.38 | +8.0% |
| `NondetBool` | 0.28 | 0.29 | +3.9% |
| `Par` | 0.39 | 0.40 | +2.5% |
| `Quicksort` | 5.40 | 5.52 | +2.3% |
| `RwLock` | 0.43 | 0.46 | +5.3% |
| `RwSpinLock` | 2.16 | 2.28 | +5.6% |
| `Spawn` | 0.56 | 0.59 | +5.8% |
| `SpinLock` | 0.69 | 0.71 | +2.9% |
| `TicketLock` | 1.60 | 1.56 | −2.2% |
| `Unwrap` | 0.16 | 0.17 | +3.0% |
| `Lib` (imports only) | 0.10 | 0.10 | +3.8% |

</details>

### Tests, memory and size

- **Tests:** the 26 test files in both trees take 18.3 s upstream and 18.8 s here (+2.5%). The
  largest, `IrisTest.Tactics` (8 s), changes by +1.8%. (`IrisTest.Linter` is left out: it needs
  the options of the lakefile.)
- **Memory:** the peak memory per module is the same: median 757 MB upstream and 746 MB here,
  maximum 1.26 GB in both (`HeapLang.ProphErasure`).
- **Import time:** 0.31 s per module upstream, 0.32 s here.
- **Size:** `.lean` lines of the Iris package +5.2% (96.3k to 101.3k); `.olean` +3.9%.

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
git clone https://github.com/leanprover-community/iris-lean up && git -C up checkout 0533d02
for d in tf up; do (cd $d/Iris && lake build && lake build IrisTest); done
TF=$PWD/tf UP=$PWD/up tf/docs/transfinite-bench/measure.sh results   # about 1.5 hours
python3 tf/docs/transfinite-bench/analyze.py results                   # writes results/summary-TF.md
```

`measure.sh` ends with clean builds, so it deletes and rebuilds `Iris/.lake/build` in both trees.
