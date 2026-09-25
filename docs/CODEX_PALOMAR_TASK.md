# Codex task: eligible Challenge and actual Comparator verification

Work in `/home/flengyel/src/FailureOfComposition-port`. Construct a Palomar
Challenge that states the existing mathematics using permitted imports, prove
its correspondence with the maintained formalization, and verify the resulting
Challenge/Solution pair with the actual Comparator. Complete the implementation
and checks, not just an assessment or plan. This is a new mathematical interface
task; the Lean version port and evaluator style cleanup are complete.

## Accepted starting point

The accepted mathematical checkpoint is
`073e95e54907eb26b6af9070302f5afdde04d963` on `main`. Its parent
`dea04886088894fa919b54249b4e97ad59d56d54` was checked in a fresh WSL acceptance
run on September 25, 2026; the child records the result without changing proofs.
All 103 maintained sources passed strict style checks, and the native build,
type/axiom/dependency audits, both kernel replays, and nine local paired draft
checks passed. These results are recorded in
`Lean/FailureOfComposition/Porting/STYLE_CLEANUP_VALIDATION.json`.

| Component | Accepted pin |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc2` |
| Mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Foundation | `e72cfe981aa65166f37fa4e2584f4806bc48d72f` |

Keep these pins. Read `AGENTS.md`, the root README, the manuscript coverage map,
`Lean/FailureOfComposition/Palomar/README.md`, Challenge, Solution,
`comparator.json`, `formalization.yaml`, and the existing verification scripts.
The older `docs/CODEX_PORT_TASK.md` describes completed work, not this task.

Inspect Git status, origin, HEAD, disk space, available memory, package mappings,
and running Lean processes. Confirm that the accepted checkpoint is an ancestor
of HEAD and preserve subsequent work. Start a local branch
`codex/palomar-eligibility` from the updated, clean `main`; if that branch already
exists, inspect and resume it instead of resetting or recreating it. Retain the
existing compatible dependency installations in this checkout.

Run the environment check once. A repeat of the full accepted baseline suite is
unnecessary before editing:

```bash
mkdir -p .codex-work/logs .codex-work/tmp .codex-work/palomar
export TMPDIR="$PWD/.codex-work/tmp"
export LEAN_NUM_THREADS=1 FAILCOMP_STYLE_JOBS=1
set -o pipefail
bash scripts/verify-failure-composition.sh --check-environment \
  2>&1 | tee .codex-work/logs/palomar-baseline-environment.log
```

Do not run synchronization over this Git checkout. Preserve the Windows source
checkout, the older FailureOfComposition mirror, PCats, Categorical_Rice_Shapiro,
and ParametricBoundedLob. Permanent Lean sources belong under `Lean/`, including
the interface and bridge proofs; logs and downloads belong under `.codex-work/`.
Do not copy dependency build trees into `/tmp` or start another toolchain port.

## 1. Fix the reference point and inspect the actual requirements

These public upstream revisions were inspected on September 25, 2026:

| Repository | Revision | Relevant files |
| --- | --- | --- |
| [PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy/tree/792c7c0b9e798bd02719e795ef11fa2b5929e067) | `792c7c0b9e798bd02719e795ef11fa2b5929e067` | `CONTRIBUTING.md`, protocol |
| [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission/tree/a59f25bd8a66bf6faf3a4f4260d412989c0185ea) | `a59f25bd8a66bf6faf3a4f4260d412989c0185ea` | `toolchains.json`, `scripts/verify_submission.py`, `docs/comparator-declaration-closure.md`, execution profiles |
| [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate/tree/cb5c79b69a740d2dc299071fc35994627050d77a) | `cb5c79b69a740d2dc299071fc35994627050d77a` | `scripts/verify-comparator.sh`, metadata validation |

Fetch reference sources under `.codex-work/palomar/upstream/`. Inspect current
upstream heads and record any changes before adopting a newer verifier. Keep an
exact revision for each actual check. Do not clone the template over this project
or replace its existing Lake layout. Some prose in the upstream policy/README
describes earlier tool installation and resource defaults; record discrepancies
against the pinned implementation instead of inventing compatible flags.

The present import rule excludes Foundation and project-local helper modules
from Challenge's transitive imports. Moving those imports into a local
`Statement.lean` does not solve it. Foundation remains usable by Solution.
Challenge has a 100 KiB/1,000-line hard limit, with warnings above 32 KiB/300 lines.
Definitions needed to understand the statement must remain explicit and readable.
The permitted axiom list is `propext`, `Quot.sound`, and `Classical.choice`.

Produce an import inventory that records actual resolved source paths and package
revisions. Use the official source-policy logic, not merely a grep for Foundation.
Document the present failing imports and the requirements for their replacements.

## 2. Construct and prove the arithmetic correspondence

Inventory every concept occurring in the nine selected theorem types. Determine
which definitions are supplied by the pinned Mathlib and which must be expressed
in Challenge itself. The present interface includes arithmetic syntax, theories,
derivability, PA, consistency, coding and recursive enumerability, arithmetic
hierarchy and truth, concrete program operations and graph formulas, pointwise
and uniform provability, generated congruences, quotients, and a monoid of actual
partial recursive functions. Mathlib must not be assumed to contain a direct
replacement for Foundation's arithmetic proof infrastructure.

Use explicit arithmetic definitions with their mathematical meaning documented.
An arbitrary `Provable : Theory → Sentence → Prop` equipped with convenient laws
is not an acceptable replacement for derivability. Do not replace syntax-based
provability by semantic consequence, supply realization/completeness as a new
hypothesis, or put the desired conclusion into a structure field.

Keep the same independent statement definitions in the Challenge and Solution
environments. Prove bridges to Foundation inside Solution-side modules. Comparator
follows ordinary definition bodies transitively: a propositional equivalence to
an FFL alias does not make differing definitions compare identically. Solution
must not import Challenge or acquire its `sorryAx`. If definitions are generated
or duplicated for the two environments, commit readable generated source and
check agreement; do not conceal an imported proof in generated statement code.

Prove the required correspondence, including:

- Translation of terms, formulas, substitution, numeral instances, sentences,
  theories, and actual derivations in both directions. Establish the PA-extension
  and consistency correspondences for every theory quantified over. Preserve
  the existing `[𝗣𝗔 ⪯ T]` notion of deductive extension; replacing it by literal
  inclusion of one PA axiom set requires a proof that the full theory scope is
  retained.
- Computability of the relevant code translations and preservation/reflection of
  r.e. axiom-code sets. A set-theoretic bijection alone does not preserve r.e.-ness.
- Correspondence of the actual evaluator graph and its PA-provability laws, the
  concrete composition/identity/empty indices, and external pointwise versus
  internally uniform equality.
- The arithmetic hierarchy, standard truth and Sigma-one soundness needed for
  the classification statements, followed by relation, quotient and monoid
  transport with their representative equations. Prove preservation/reflection
  or a provable-normal-form correspondence sufficient for completeness for
  every true Pi-one sentence and soundness for every Sigma-one sentence;
  agreement only on evaluator-graph formulas is insufficient.

The first implementation checkpoint is `obstruction_four_properties`. It tests
the essential consistent-r.e.-PA hypotheses and both kinds of provability while
postponing quotient and hierarchy transport. Compile its independent interface,
prove its correspondence, obtain its Solution proof from the maintained theorem,
and run a temporary one-statement Comparator configuration. This is an
intermediate checkpoint; retain all nine names in the final configuration.

Extend the same construction to all nine, preserving these distinctions:

| Selected result | Required scope |
| --- | --- |
| Four witnesses; both no-composition routes; weak totality; both range routes | Every consistent PA extension with r.e. axiom codes; no added soundness, presentation, or realization hypothesis |
| Pi-one characterization | Every consistent PA extension; no r.e. hypothesis |
| Generated-congruence classification | Every PA extension; no consistency or r.e. hypothesis |
| Partial-recursive quotient isomorphism | Every Sigma-one sound PA extension, with the explicit representative equation into actual unary partial recursive functions |

All input and program-index quantifiers retain their stated natural-number
scope. Preserve the explicit weak-totality guard family. Range assignment must
retain its PA-uniform graph specification, not just agree with the range in the
standard model. The maintained choice-independence theorem can support a
different realizing range index only after its PA-correctness is proved. Do not
claim that an arbitrary classical selector is computable.

Keep the established productive and Goedel-II dependency separation. Keep
existing maintained theorem signatures and hypotheses unchanged. New Palomar
representations require proved transport and an explicit correspondence table;
printer-normalized type comparison alone cannot establish semantic fidelity.

Leave `definition_names` empty or absent: do not make PA, provability, evaluation,
or other substantive semantics unspecified slots. Keep the nine deliberate
Challenge theorem holes separate from the proved library. Any proposed additional
compared supporting theorem must be explained and actually proved in Solution;
an unselected hole is not an acceptable helper. Update local checks deliberately
if the interface changes, retaining their axiom and dependency obligations.

## 3. Implement reproducible verification on this machine

Add a project-specific `scripts/verify-palomar.sh` with a read-only
`--check-environment` mode and documented local Comparator/full-verifier modes.
Use persistent, uniquely named run directories, record exact commands and exit
codes, and preserve logs on failure. Test meaningful failure handling, including
missing tools and a JSON failure report accompanying process exit zero.

For ordinary proof development, retain the existing bounded Lake launcher
(`Lean/FailureOfComposition/bounded_lake.sh`) and its one-worker, `-j 1`,
`-M 12288` compiler settings. Those are resource controls, not an assertion about
the independent checkers' memory use. One build/checker workload at a time;
inspect actual child processes and pressure before allowing a long run.

### Local Comparator

Adapt the pinned Template helper to this project's `Lean/` directory and
`FailureOfComposition/Palomar/comparator.json`. Check `bwrap` and the selected
toolchain's bundled `lake`, `leanexport`, `leanchecker`, `nanoda_bin`, and
`con-ron`. Generate a separate protected configuration registering both bundled
independent kernels. `external_kernels` belongs in that generated configuration,
not in the submitted JSON; `enable_nanoda` is not authoritative.

Run the actual `lake comparator --config <generated-config>` with the correct
working directory. Validate dependencies before any cache retrieval; reuse this
checkout's compatible dependencies and fetch only what is actually missing.
Verify real build concurrency and memory limits across Comparator's child
processes. Do not infer this from the parent shell's environment variables.
Use authentic selected-toolchain judge binaries. Do not replace them with mock
commands or silently disable a kernel, sandbox, axiom check, or definition check.

The resulting evidence must identify all nine compared declarations and successful
Lean-kernel, NanoDa, and con-ron replay. Keep `check_draft.py` as a separate project
check; its success is not a Comparator result. A Template-style Comparator pass
alone does not verify Palomar's protected Challenge source provenance.

### Complete mechanical eligibility

Use the pinned PalomarSubmission implementation to check the exact candidate
commit, including its protected Challenge compilation/import audit and exported
proof comparison. Its `prepare` phase fetches a public immutable Git commit, not
uncommitted local files. Commit and push the candidate branch when needed for this
local mechanical test; do not submit or register it with the Palomar service.

The selected paths are:

| Setting | Value |
| --- | --- |
| Repository | `flengyel/FailureOfComposition` |
| Selected project | `Lean` |
| Comparator configuration | `Lean/FailureOfComposition/Palomar/comparator.json` |
| Metadata | `Lean/FailureOfComposition/Palomar/formalization.yaml` |

Paths in the verifier request are repository-relative. Build a local event from
the pinned `submission_contract.py`, with the real candidate SHA, `mode: full`,
a 12-character lowercase alphanumeric request identifier, and JSON-encoded
options. Record the responsible-maintainer authorization from this task; do not
claim that a service submission, review, or upload occurred.

Inspect the pinned workflow and the actual CLI for `prepare`, `check-capacity`,
and `execute`. Provision their declared Python/Ruby/Licensee and bubblewrap
dependencies in an isolated local environment. Record real tool revisions and
the execution profile. For the full verifier, use its pinned bubblewrap 0.12.0
installer and source-tag verification, not an arbitrary distribution build.
Pass `--execution-budget-seconds 19800` explicitly: the CLI default is 12 hours,
longer than the inspected profile's 19,800-second budget. The inspected verifier defaults to
`palomar-namespace-16x32-v1` (at least 16 effective CPUs and 28 GiB effective RAM).
Its explicitly approved `palomar-standard-v1` profile requires at least 14 GiB
effective RAM without that CPU minimum. Both require at least 20 GiB free disk.
Selecting the latter must be explicit in the report; it does not demonstrate a
run under the registry's current default profile. Record the profile's memory
high/max thresholds (95%/98%) and actual limits applied.

WSL support for bubblewrap, nested user namespaces and cgroup-v2 delegation must
be tested before starting the complete verifier. `LEAN_NUM_THREADS` is not passed
through this verifier's sandbox, so the shell export does not guarantee one
compiler there. Establish and monitor resource bounds before running it on this
machine. Do not weaken the profile or disable protected checks to fit available
resources. If the required infrastructure or safe concurrency control is absent,
record that exact environment blocker and retain the completed mathematical
interface and local Comparator evidence; do not label the full verifier passed.

Some official verifier failure paths exit zero while writing a failure report.
After preparation require JSON `status: pending`, `stage: prepared`. Final success
requires `status: pass`, `stage: complete`, and matching source SHA, selected paths,
profile, and protected configuration. Check the protected configuration's recorded
bytes/hash and expected transformation: the verifier renames Challenge and adds
kernel commands, so it must not literally equal the submitted JSON.
Do not use the Actions-only report gate
outside its CI context or fabricate upload state to satisfy it.

## 4. Finish the existing checks and the handoff

After repairs settle, run the existing full project verifier once and the new
Palomar checks. Include strict style and axiom/dependency checks for added bridge
and interface sources; document any inventory changes instead of dropping new
files from checks. Inspect the final diff against the accepted mathematical
checkpoint and preserve the manuscript coverage map unless an explained,
reviewable correction is genuinely needed. Do not edit manuscript v36 or draft
the author's v37 as part of this task.

Update Palomar documentation and metadata with observed outcomes. Repository
licensing remains a separate snapshot question: the manuscript retains its
existing terms. Identify the concrete conflict and prepare a packaging proposal
if necessary; do not assign the manuscript a new license or remove it from main
without the author's decision. Complete the technical work before raising that
decision. A local mechanical pass is not editorial acceptance or registration.

Commit a concise `Lean/FailureOfComposition/Palomar/STATUS.md`, the independent
interface, all correspondence proofs, verification scripts, and a machine-readable
validation record. The record must identify the exact tested code commit,
upstream/toolchain/dependency revisions, all nine declarations, import provenance,
commands, exit codes and report verdicts, resource settings/observations, remaining
blockers, and hashes of retained logs. Keep large output in `.codex-work/` and
produce an evidence archive for independent review. If a later documentation-only
commit records a tested code commit, state that relationship explicitly.

Make focused commits on `codex/palomar-eligibility` and publish that branch for
independent review. Keep `main` at its accepted state during this mathematical
interface change. Do not submit, register, or contact Palomar. If a genuine
mathematical or external blocker remains, preserve the work, give the smallest
reproduction and precise unsolved obligation, and label that phase incomplete.
Do not replace the result by a weaker theorem or present a preliminary checkpoint
as completion.
