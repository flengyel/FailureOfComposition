# FailureOfComposition

This is the maintained repository for the Lean formalization and LaTeX source
of Florian Lengyel's *Pointwise provable equality and the failure of composition*.

- [Lean development and verification guide](Lean/FailureOfComposition/README.md)
- [Manuscript source, version 36](manuscript/failure_of_composition_2026-09-21_v36.tex)
  and [manuscript provenance and build instructions](manuscript/README.md)
- [Mathematical statements and Lean signatures](Lean/FailureOfComposition/MANUSCRIPT_STATEMENTS.md)
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
extends warnings-as-errors checks to all 31 evaluator sources. The cleanup
passed its full WSL verification; see the
[validation record](Lean/FailureOfComposition/Porting/STYLE_CLEANUP_VALIDATION.json).
`CRS_LAKE_PACKAGES` may supply an existing package mapping. The scripts validate
the dependency pins and do not fetch new checkouts.

For a source checkout on `/mnt/c`, use the persistent Linux mirror described in
[scripts/README.md](scripts/README.md). Choose a fresh mirror, such as
`~/src/FailureOfCompositionStandalone`: the existing `~/src/FailureOfComposition`
mirror belongs to the original repository's checkout. Mirror ownership is tied
to its source directory.

## Licensing and Palomar

The Lean formalization and supporting code use the existing
[Apache-2.0 license](LICENSE). The author retains copyright in the manuscript,
which was submitted under arXiv's perpetual, non-exclusive distribution
license; that grant is not a general public reuse license. See the
[manuscript notes](manuscript/README.md).

The [Palomar preparation](Lean/FailureOfComposition/Palomar/README.md) contains
nine paired statements and proved counterparts. The toolchain port has passed
its project verification. On `codex/palomar-eligibility`, all nine selected
declarations passed a local con-ron, NanoDa, and Lean Comparator run at
`381de9db4d2214b8fd8d05bf74b56bc9597f01c5`. The pinned official verifier then
fetched public commit `48e6eeccc420e8068f1bc6d810ddbe10cfdf39eb` and
completed its protected build/export/comparison/kernel workflow under
`palomar-standard-v1`. The
[recorded Nine checkpoint](Lean/FailureOfComposition/Palomar/STATUS.md)
identifies the exact scope.
That pass predates the current module-header requirement. The focused candidate
now retains 124 Lean modules, no maintained Lean code under `Audit/`, and the
same nine mathematical contracts. Current verifier preparation and capacity
checks passed for public candidate
`6adc1084e57ca3e9011dbd3765e99b803842ee17`, but the one full execution was
terminated during Solution build by an external host-monitor `/proc` race
before any kernel ran. It is neither a rejection nor a current-verifier pass;
the exact result is recorded separately in the status file.
These declaration counts are distinct from
manuscript numbering. The submitted snapshot includes the distinct manuscript
and code licensing notices. No Palomar service submission, editorial
acceptance, or registration is claimed.
