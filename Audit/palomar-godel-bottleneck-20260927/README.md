# Gödel-II con-ron bottleneck diagnosis

Date: 2026-09-27

Proof-bearing baseline: `b557d255f1d0b42920440cb2d4762b1ca54b2728`

Diagnostic source head before this report:
`11163733efd0283ac34e1c9ecc96ad7ce69ba481`

Toolchain: Lean 4.35.0-rc2,
`11acb17ec6b07a8f9e9173e6845197929540936b`; Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; Foundation
`e72cfe981aa65166f37fa4e2584f4806bc48d72f`.

## Result

The cumulative Three timeout is reproduced by a single generated theorem in
the pinned Foundation dependency:

```text
FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction._proof_4
```

Stock con-ron completes the preceding
`FFL.FirstOrder.Arithmetic.listMax.congr_simp`, then does not complete this
next declaration.  The smallest retained reproducer is a dependency-closed
44,002,216-byte export rooted at `_proof_4`.  Its bounded replay reached
8,710,561,792 bytes aggregate cgroup memory, 47,191 `memory.high` events, and
full-memory PSI `avg10=86.6`; it reached the 120-second diagnostic deadline
without a verdict.  There were no `memory.max`, OOM, OOM-kill, swap, or pids
events.  This is an inconclusive resource result, not a rejection.

The theorem itself is not a large expression.  Its type has 183
pointer-distinct and 183 structurally distinct nodes; its body has 583 of
each.  The body is an auto-generated proof from
`func_defined := .mk fun v => by simp [blueprint]` in Foundation's
`FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Basic.lean`.  It contains 33
observed equality applications.  The largest `Eq.trans`-headed subterm has
545 pointer-distinct nodes.  The replay behavior therefore points to
pathological conversion/reduction while checking this small equality proof,
not to a multi-million-node local Gödel proof term.

The exact dependency path from the independent r.e.-axiom correspondence is:

```text
reAxiomCodes_toFoundation_iff
  -> FailureOfComposition.AxiomCodes
  -> FFL.FirstOrder.Sentence.instGödelQuoteSemisentence
  -> FFL.FirstOrder.Semiformula.instGödelQuoteSemiproposition
  -> FFL.FirstOrder.Arithmetic.Bootstrapping.Semiformula.val
  -> FFL.FirstOrder.Arithmetic.Bootstrapping.Semiformula
  -> FFL.FirstOrder.Arithmetic.Bootstrapping.Semiformula.mk
  -> FFL.FirstOrder.Arithmetic.Bootstrapping.IsSemiformula
  -> FFL.FirstOrder.Arithmetic.Bootstrapping.IsSemiformula.mk
  -> FFL.FirstOrder.Arithmetic.Bootstrapping.bv
  -> FFL.FirstOrder.Arithmetic.Bootstrapping.BV.construction
  -> FFL.FirstOrder.Arithmetic.Bootstrapping.termBVVec
  -> FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction
  -> ...construction._proof_9
  -> ...construction._proof_4
```

This path is already forced by the maintained `AxiomCodes` predicate used in
the type of the maintained r.e.-axiom Gödel theorem.  Replacing only the local
bridge proof, naming another wrapper, or factoring the selected theorem cannot
remove it.  Avoiding the declaration would require changing the pinned
Foundation source or rebuilding the maintained axiom-code/quotation route,
neither of which is a narrow candidate-side proof repair.  No mathematical
proof source or pinned dependency was changed.

Consequently the evidence gate for another cumulative Three Comparator run
was not met.  No full Comparator run was attempted in this checkpoint.

## Static profiles

The profile visits each physical expression node at most once.  “Physical”
means runtime `Expr` pointer identity.  “Structural” means `Expr.eqv`
alpha-equivalence with Lean's cached structural hash.  The global columns
deduplicate across declarations in a closure; the per-declaration columns sum
independently deduplicated declaration DAGs.  Types and bodies are counted
separately.  There is no normalization, reduction, or naive raw-tree walk.

| selection | declarations | global physical type | global structural type | global physical body | global structural body |
| --- | ---: | ---: | ---: | ---: | ---: |
| first two | 17,107 | 374,819 | 256,875 | 2,329,925 | 1,852,655 |
| Gödel only | 20,328 | 462,013 | 314,357 | 3,068,852 | 2,432,374 |
| all three | 21,253 | 482,505 | 326,710 | 3,268,655 | 2,595,423 |
| Three minus Two | 4,146 | 118,685 | 84,113 | 969,033 | 806,603 |

The marginal is distributed across Foundation quotation and bootstrapping
declarations.  The largest marginal bodies are approximately 13,000–26,000
pointer-distinct nodes, rather than one giant selected proof body.

Boundary closure counts are 13,657 for
`reAxiomCodes_toFoundation_iff`, 17,463 for
`CraigPresentation.exists_craig_presentation`, 18,318 for the direct
Delta-one `index_noncongruence_via_godel`, and 15,629 for
`graph_noncongruence_via_godel`.  Their additions over the Two closure are
1,195, 3,213, 3,208, and 3,052 respectively.  The r.e.-axiom and Craig
closures overlap in 13,560 declarations; Craig and the direct index route
overlap in 16,097.  Across the r.e.-axiom, Craig, and direct-index boundaries,
the portions unique against the other two are 93, 1,349, and 2,217
declarations.  This is why adding closure sizes would badly overcount the
actual contribution.

The graph and concrete-arithmetization closures contain 15,629 and 14,989
declarations and overlap in 12,334.  The realization closure is 14,703 and is
wholly contained in the concrete-arithmetization closure.  Static size alone
did not identify the checker behavior; the bounded replay did.

## Export measurements

Every generated export used `leanexport` from the pinned toolchain, module
`FailureOfComposition.Palomar.SolutionThree`, the named roots, and the same
Comparator primitive declarations.  The retained Three export is tied to the
prior Comparator process log and has pinned exporter metadata.

| selection | bytes | expression records | declaration records | SHA-256 |
| --- | ---: | ---: | ---: | --- |
| first two | 111,380,396 | 1,980,154 | 16,222 | `4da8d947e122b40ec29308749956743ddaa4384bc9902fe910a0c6ca4b22c3fd` |
| Gödel only | 145,578,019 | 2,589,941 | 19,359 | `fce2b7622a3b40ecad6be2d83c1c89ca3bdd28857b05ca15d67f56b736501c5c` |
| cumulative Three, retained | 154,887,560 | 2,757,272 | 20,283 | `4ff948819e5dd4d8d10be77ee1189f6e2fb9d8d498544a2607b84dba33b64553` |
| axiom-code bridge | 81,553,307 | 1,437,285 | 12,863 | `78ff3f6f50a21469bf6e3f414b7d168865200cde6085149563b5980bca2f1912` |
| Craig presentation | 111,511,969 | 1,964,877 | 16,576 | `1a10fe79f16e6031090c5770f01620ff41bf6404b816f13ce448dc16c763a363` |
| direct Delta-one index route | 130,976,419 | 2,334,287 | 17,471 | `22254e51de9bf827ec50f2a51f9afdc24e127b4df1a9783a897ff3ea130f00d3` |
| graph Gödel route | 101,290,407 | 1,793,485 | 14,832 | `daea963e408f3f8710293acde0349ce959fc70c736a1895dc855fcb3359db613` |
| `_proof_4` reproducer | 44,002,216 | 778,146 | 8,077 | `71a0c52bab8b42b11379cc2fcfafcc01a277a56f04e2dd7e1223e2c09a1ec47a` |

Expression records are exporter DAG records.  They are not physical pointer
counts and are not a direct measure of kernel work.

## Probe budget and telemetry

All probes used stock con-ron in verified mode with `--jobs=1`, a bubblewrap
sandbox, one assigned CPU, `memory.high=8G`, `memory.max=10G`, zero swap, and
the established 2 GiB physical and 4 GiB available-memory reserve checks.  An
early guard terminates the owned cgroup if full-memory PSI `avg10` remains at
least 80% for 60 consecutive seconds.  A synthetic fixture validated the
threshold state machine and owned-cgroup termination.  Telemetry was sampled
about every five seconds.

Four probe slots were used, totaling 390.927 seconds of active checker wall
time, below the 600-second budget:

1. The first sandbox invocation failed before con-ron because its working
   directory was masked.  It consumed one slot but zero active checker time;
   the preserved log records the failure.
2. The 81.6 MB axiom-code bridge export reached 8,689,934,336 bytes, 71,846
   high events, and the 180.219-second deadline.  With stride 100, its last
   completed heartbeat was check 8500/12360.
3. The same export with stride 1 reached 8,708,657,152 bytes and the
   90.349-second deadline.  Its last completed check was 8584/12360,
   `listMax.congr_simp`; export order shows `_proof_4` next.
4. The 44.0 MB helper-only export reached 8,710,561,792 bytes, 47,191 high
   events, PSI `avg10=86.6`, and the 120.359-second deadline.  Its last
   completed check was 7685/7691, again `listMax.congr_simp`, with `_proof_4`
   next.

The three real probes completed parsing and installation.  None completed the
check phase or returned a verdict.  Across them, all max/OOM/OOM-kill counts
were zero.  Silent time after the last heartbeat is reported as unknown work,
not progress.

## Reproduction tools

`tools/SolutionThreeProfile.lean` records the closure DAG profiles and largest
marginal declarations.  `tools/BoundaryOverlap.lean` records overlap and
marginal counts.  `tools/HotspotProfile.lean` reports the exact helper shape,
direct dependencies, equality subterms, printed proof, and dependency path.
`tools/export_stats.py` streams NDJSON statistics without loading the export
in memory.  `tools/export_decl_window.py` resolves export-order names.
The evidence archive retains the pinned Palomar supervisor with the recorded
early-pressure guard; the tracked fixture and validator document its focused
regression check.

Full export dumps and machine-specific run directories are intentionally not
tracked.  They remain local under `.codex-work/` and compact statistics,
commands, telemetry, identities, and hashes are included in the checkpoint
evidence archive.
