Lean 4 port of *Iris*, a higher-order concurrent separation logic framework.

# About Iris

"Iris is a framework that can be used for reasoning about safety of concurrent programs, as the logic in logical relations, to reason about type-systems, data-abstraction etc."<br>
– https://iris-project.org/

Rocq formalization of Iris: https://gitlab.mpi-sws.org/iris/iris/

# Project

Currently, Iris-Lean has support for 
- *MoSeL*, the proof interface of Iris
- `IProp`, the standard model of Iris
- `HeapLang`, the Iris example language and logic
- A selection of the Iris resources, including invariants, later credits, and many more.

Users of Iris-Lean should be aware of the documentation:
- [tactics.md](docs/tactics.md): Instructions for using Iris tactics.
- [tracking site](https://leanprover-community.github.io/iris-lean/): Iris-Lean correspondence for definitions in Iris-Rocq.
- [compatibility.md](docs/compatibility.md): Important differences between Iris-Rocq and Iris-Lean.
- [proofmode.md](docs/proofmode.md): Details of *MoSeL*; support for separation logics other than Iris.

# Transfinite Step Indices (This Branch)

This branch adds transfinite step indices to Iris-Lean, as in
[Transfinite Iris](https://github.com/dongjaelee1/transfinite-iris) (Spies et al., PLDI 2021).

## Design: One Step Index for Each Build

Upstream Iris-Lean uses `Nat` as the step index. This branch uses one constant, `Iris.SI`, which
the file `Iris/Iris/Algebra/StepIndexChoice.lean` sets. No class or lemma takes the index as a
parameter, so client proofs look the same as with upstream Iris-Lean. The library proofs use only
the interface of `SI` (the class `SIdx`, and `SIdxFinite` where the index must be finite), so they
hold for each index.

The default index is `Ordinals.Ordinal.{3}`, from the package `Ordinals/` of this repository (core
Lean only, no Mathlib). The universe level 3 gives three levels of ordinals below the index:
`Ordinal.{0}`, `Ordinal.{1}` and `Ordinal.{2}`.

To build Iris with another index, select a stored choice from `Iris/StepIndexChoices/` and build
again. The script also selects the tests of that index.

```sh
scripts/stepindex.sh nat       # SI := Nat
scripts/stepindex.sh ordinal   # SI := Ordinals.Ordinal.{3} (default)
cd Iris && lake build
```

## Differences from Upstream Iris-Lean

- **Model.** `IProp` uses the transfinite COFE solver (from upstream PR
  [#709](https://github.com/leanprover-community/iris-lean/pull/709)) for each index. The solver
  is noncomputable, so many files are `noncomputable section`.
- **Later laws.** The BI laws follow Rocq Iris MR
  [!1256](https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/1256). `later_sep_1` and
  `later_sExists_false`, and the laws that come from them (for example `later_exists`), need
  `[SIdxFinite SI]`. The new laws `later_false_impl_sExists` and `later_false_impl_sep` hold for
  each index. `Timeless P` means `<only0> P ⊢ P`.
- **Invariants.** As in Rocq Transfinite Iris, some rules need `[SIdxFinite SI]`: `inv_alter`,
  `inv_combine`, `inv_split`, `inv_acc` of non-atomic invariants, and the rules of boxes.
  Cancelable invariants are `inv N (P ∨ own γ 1)`.
- **HeapLang.** The heap tactics split the context before they remove `▷`. There are new rules
  `wp_load_later`, `wp_store_later`, `wp_cmpXchg_later` and `wp_faa_later`. The specifications of
  the HeapLang libraries do not change.
- **Universes.** `GFunctor` and `BundledGFunctors` have one universe, and `IProp GF : TypeSI u`.
- **New.** The ordinal camera (`NatOrdinal` with the natural sum), the existential property
  `SIdxLarge SI X`, satisfiability, and the big later `⧍`.
- **Not ported.** The refinement logic and the time credits of Transfinite Iris. Later credits
  `£ n` count with `Nat`.

Client proofs take about 3–4% more time than with upstream Iris-Lean (17 HeapLang library proofs,
measured on 2026-10-06).

# Using Iris-Lean as a Dependency

- Iris-Lean is updated in sync with Lean. The [releases](https://github.com/leanprover-community/iris-lean/releases) page includes tags for recent versions.
- The `master` branch may contain features added since the last release:
```
[[require]]
name = "iris"
git.url = "https://github.com/leanprover-community/iris-lean.git" 
git.subDir = "Iris" 
rev = "master"
```
- To use Iris constructions based on mathlib, you can also import the math library
```
[[require]]
name = "iris"
git.url = "https://github.com/leanprover-community/iris-lean.git" 
git.subDir = "IrisMath" 
rev = "master"
```

# Development

Development for Iris-Lean coordinates in:
- The [iris-lean channel](https://leanprover.zulipchat.com/#narrow/channel/490604-iris-lean) on the Lean Zulip. 
- The [Iris Mattermost channel](https://mattermost.mpi-sws.org/iris/channels/iris-lean)

We always welcome new contributors! For questions, contribution guidance, and development information, feel free to introduce yourself on the Zulip. 

# Miscellaneous

## Unicode Input

Most of the unicode characters used in Iris can be written with the Lean extension replacement, e.g. `\ast` will automatically be replaced with `∗`. To add additional replacements, edit the Lean extension setting `lean4.input.customTranslations`. Suggested additional replacements are listed below.

```json
"sep": "∗",
"wand": "-∗",
"pure": "⌜⌝",
"bientails": "⊣⊢",
"emb": "⎡⎤",
"auth": "●", 
"frag": "◯",
"incl": "≼", 
"valid": "✓",
"later": "▷",
"except0": "◇",
"plainly": "■",
"intuit": "□",
"credit": "£",
```

## References

- [koenig22](https://pp.ipd.kit.edu/uploads/publikationen/koenig22masterarbeit.pdf), Master Thesis, *An Improved Interface for Interactive Proofs in Separation Logic*, 2022-10, Lars König, KIT.
- [demedeiros26](https://arxiv.org/abs/2609.24252), Draft paper. *Iris in Lean*, Markus de Medeiros, Sergei Stepanenko, Zongyuan Liu, Oliver Soeser, Fernando Leal, Alvin Tang, Max Vistrup, Ralf Jung, Mario Carneiro, Joseph Tassarotti, Michael Sammler, and Lars Birkedal.
