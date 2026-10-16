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

This branch (`transfinite` of [dongjaelee1/iris-lean](https://github.com/dongjaelee1/iris-lean))
adds transfinite step indices to Iris-Lean, as in
[Transfinite Iris](https://github.com/dongjaelee1/transfinite-iris) (Spies et al., PLDI 2021).
The whole build uses one step-index type, `Iris.SI`, which `Iris/Iris/Algebra/StepIndexChoice.lean`
sets. The default is `Ordinals.Ordinal.{3}`, from the package `Ordinals/` of this repository (core
Lean only, no Mathlib). For a build with natural-number step indices, select the stored Nat choice
and build again:

```sh
scripts/stepindex.sh nat       # SI := Nat
scripts/stepindex.sh ordinal   # SI := Ordinals.Ordinal.{3} (default)
cd Iris && lake build
```

The design, the differences from upstream Iris-Lean and the performance measurements are in
[docs/transfinite-report.md](docs/transfinite-report.md).

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
