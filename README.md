# FailureOfComposition

This is the maintained repository for the Lean formalization and LaTeX source
of Florian Lengyel's *Pointwise provable equality and the failure of composition*.

- [Lean development and verification guide](Lean/FailureOfComposition/README.md)
- [Manuscript source, version 36](manuscript/failure_of_composition_2026-09-21_v36.tex)
  and [manuscript provenance and build instructions](manuscript/README.md)
- [Manuscript-to-Lean coverage map](Lean/FailureOfComposition/MANUSCRIPT_COVERAGE.md)
- [Palomar preparation](Lean/FailureOfComposition/Palomar/README.md)
- [Codex setup in WSL2](docs/CODEX_WSL_SETUP.md) and
  [first toolchain-port task](docs/CODEX_PORT_TASK.md)

The development proves the failure of induced composition on pointwise
provability classes, the Pi-one completeness characterization, the classification
of the generated composition congruence, and the weak-totality and range
obstructions. The coverage map states the exact program-index scope.
The manuscript is the unchanged v36 source underlying that coverage review;
the author's planned v37 revision will be added separately.

## Repository layout and history

The mathematical development and its verifier are in `Lean/`. The two declared
libraries are `FailureOfComposition` and the 31 pinned `CategoricalRiceShapiro`
evaluator modules it uses. The default build target is `FailureOfComposition`.
The Lake package name remains `CategoricalRiceShapiro` to preserve the dependency
manifest; it does not identify the repository where development is maintained.

The formalization was developed in
[flengyel/Categorical_Rice_Shapiro](https://github.com/flengyel/Categorical_Rice_Shapiro)
before moving here. That repository is the historical origin of the exported
code and verification records. [ROOTPROVENANCE.json](ROOTPROVENANCE.json) records
the initial export, including its input/output hashes and packaging changes.
Its flags describe that export event. It is not a manifest of later commits:
this repository has since been initialized, published, and extended with the
manuscript and updated documentation.

## Verification

The Lean 4.35.0-rc2 port at `d2100df` passed the independent WSL rerun on
2026-09-25. With that toolchain and the pinned dependencies installed under
this checkout's `Lean/.lake/packages`, run from this directory:

```sh
bash scripts/verify-failure-composition.sh --check-environment
bash scripts/verify-failure-composition.sh
```

The environment check invokes no Lake command. Full verification builds the
library and runs the style, theorem, dependency, and kernel checks. The
[evaluator style cleanup](Lean/FailureOfComposition/Porting/STYLE_CLEANUP.md)
extends warnings-as-errors checks to all 31 evaluator sources; its changed
proofs require a subsequent WSL verification before acceptance.
`CRS_LAKE_PACKAGES` may supply an existing package mapping. The scripts validate
the dependency pins and do not fetch new checkouts.

For a source checkout on `/mnt/c`, use the persistent Linux mirror described in
[scripts/README.md](scripts/README.md). Choose a fresh mirror, such as
`~/src/FailureOfCompositionStandalone`: the existing `~/src/FailureOfComposition`
mirror belongs to the original repository's checkout. Mirror ownership is tied
to its source directory.

## Licensing and Palomar

The Lean formalization and supporting code use the existing
[Apache-2.0 license](LICENSE). The manuscript retains its existing licensing;
placing its source here does not assign it a new code license. See the
[manuscript notes](manuscript/README.md).

The [Palomar draft](Lean/FailureOfComposition/Palomar/README.md) contains nine
paired statements and proved counterparts. The toolchain port has passed its
project verification. Submission still requires a Challenge with permitted
imports and actual Comparator verification. The manuscript's licensing scope must also be accounted
for in any submitted snapshot. No Palomar submission or registration is claimed.
