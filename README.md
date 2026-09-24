# FailureOfComposition: standalone repository candidate

This source-only export prepares a separate repository for the Lean
formalization of *Pointwise provable equality and the failure of composition*.
It has not initialized Git, created a remote repository, or published anything.

The mathematical development and its verifier remain in `Lean/`. The only
libraries declared here are `FailureOfComposition` and its 31 pinned
`CategoricalRiceShapiro` evaluator modules. The default target is
`FailureOfComposition`. The historical Lake package name remains
`CategoricalRiceShapiro` so that the committed dependency manifest is unchanged;
it does not determine the eventual repository name.

The source repository is [flengyel/Categorical_Rice_Shapiro](https://github.com/flengyel/Categorical_Rice_Shapiro).
The supplied baseline reference is `202194e54e883648f0d9f22a65afee6987ef2134`; this is not a claim that every
exported byte belongs to that commit. `ROOTPROVENANCE.json` records the exact
source and exported file hashes and every packaging transformation. No theorem
source or dependency pin was changed by the export.

## Verification

With Lean 4.32.2 and the pinned dependencies already installed under
`${PCATS_DST:-$HOME/src/PCats}/.lake/packages`, run from this directory:

```sh
./scripts/verify-failure-composition.sh --check-environment
./scripts/verify-failure-composition.sh
```

The environment check invokes no Lake command. Full verification builds the
native library and runs the maintained style, theorem, dependency, and kernel
checks. `CRS_LAKE_PACKAGES` may provide the existing validated package mapping.
No dependency checkout is copied into this export or fetched by those scripts.

For a source checkout on `/mnt/c`, use `./scripts/syncfailcomp.sh` to maintain
a Linux verification mirror. Choose a new `FAILCOMP_DST` if an existing mirror
belongs to the original repository; mirror ownership is tied to its source.
See [scripts/README.md](scripts/README.md). The exporter has not run these checks
on this new tree; results must be obtained separately and recorded honestly.

## Palomar preparation and licensing

The nine paired statement drafts are in
[Lean/FailureOfComposition/Palomar](Lean/FailureOfComposition/Palomar/README.md).
The export supplies a repository-root `LICENSE`, copied unchanged from the
existing Lean code license. Manuscripts, PDFs, unrelated projects, build
artifacts, dependency checkouts, and prior audit reports were not copied.

This packaging does not fix Palomar's current minimum-toolchain or Challenge
import-policy blockers. No Comparator or Palomar check has been run by the
exporter. The copied draft metadata retains original-repository provenance and
baseline-specific licensing discussion. Before any submission, update its
repository identity and checked revision, distinguish this root-license
packaging from the original baseline, and complete the outstanding gates.
The draft Challenge's deliberate theorem holes remain outside the maintained
proof umbrella. Source license and third-party dependency licenses remain
distinct; no manuscript license is declared by this code-only export.
