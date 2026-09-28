# Exact Foundation helper replacement diagnostic

Date: 2026-09-27 (America/New_York; evidence directory dated in UTC)

Candidate proof/configuration baseline:
`b557d255f1d0b42920440cb2d4762b1ca54b2728`.
Tested diagnostic source commit:
`996f70e1630602a7543a43c7ed87adec02ac841a`.

This checkpoint did not change the Palomar Challenge, Solution, comparator
configuration, dependency pins, or the pinned Foundation checkout.  It did not
run the cumulative Three Comparator.

## Result

The unchanged dependency-closed export rooted at

```text
FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction._proof_4
```

was replayed through Lean's bundled export checker and NanoDa on the exact
retained bytes.  Neither checker produced an acceptance or rejection before
its 120-second deadline.  Lean reached 8,895,926,272 bytes aggregate peak
memory, 3,766 `memory.high` events, and full-memory PSI `avg10=93.66`;
NanoDa reached 5,317,881,856 bytes without pressure or `memory.high` events.
Both results are timeouts, not rejections.  They do not establish that the
unchanged input is uniquely problematic for con-ron.  Neither checker emitted
a progress marker, so the retained runs do not establish that either checker
reached the suspect helper.  Their memory profiles also differ and do not
establish a shared mechanism.

A project-local theorem was then proved with exactly the original generated
helper's elaborated type, modulo deterministic universe-parameter renaming.
Instead of asking simplification or definitional equality to expand
`blueprint.func.val`, its proof:

1. reduces only the `Blueprint.func` record projection;
2. rewrites with `HierarchySymbol.Semiformula.val_mkSigma`;
3. uses a named `eval_substs` identity for the two substituted terms; and
4. finishes with `Arithmetic.listMax_defined.iff` and a small coordinate
   identity.

The replacement compile completed in 4.644 seconds with 196,042,752 bytes peak
aggregate memory.  That command omitted `-DwarningAsError=true`; its output
contained no warnings.  The exact type/dependency/axiom audit completed in
7.449 seconds with 249,417,728 bytes peak memory.  It established:

- exact universe-renamed `Expr.eqv` type equality with the original helper;
- a replacement closure of 8,661 constants which does not reach the original
  generated helper;
- recursive axioms exactly `propext`, `Classical.choice`, and `Quot.sound`;
- the same 183-node type, and a 134-node replacement body versus the original
  583-node body (physical and structural counts coincide for both bodies).

The dependency-closed replacement export was checked by the unchanged bundled
stock con-ron, SHA-256
`4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`,
using `--verified --jobs=1 --progress=1`.  Its explicit verdict was:

```text
con-ron: accepted 8080 declarations (--verified)
```

Con-ron completed all 7,698 pending checks in 65.935 seconds total (42.836
seconds installation and 22.138 seconds checking).  Aggregate CPU was 65.429
seconds and peak memory was 239,558,656 bytes.  There were no `memory.high`,
hard-limit, OOM, OOM-kill, deadline, swap, pids-limit, or pressure-stop events.

This is a checked local replacement candidate for the precise Foundation
proof.  It is not an integrated Foundation revision, a repaired maintained
Gödel proof, a cumulative Three pass, or official Palomar verification.

## Attribution

The 120.349-second attribution command named `PieceBlueprint.lean`.  That
source was not retained, so its contents cannot be audited or reconstructed as
historical evidence.  `BlueprintConversionControl.lean` is a later, untested
proposed reproducer; no timing or resource measurement from the missing source
is attributed to it.

The successful factored proof avoids the original broad unfolding and is
accepted cheaply by stock con-ron.  This does not identify the active operation
inside con-ron, Lean's export checker, or NanoDa.  The mechanism of the original
stall therefore remains unresolved; in particular, the evidence does not
localize it to a kernel cache, annotation step, conversion subroutine, or
cleanup path.

The earlier profiler's “33 equality applications” count is a count of curried
application prefixes.  The printed generated proof has six visible
`Eq.trans` uses.

No predecessor or instrumented-checker probe was needed.  No checker binary
or verification behavior was modified.

## Exports and replay budget

Both exports were produced by pinned `leanexport` 3.1.0 from Lean
4.35.0-rc2 commit `11acb17ec6b07a8f9e9173e6845197929540936b`
with the Comparator primitive roots.

| root | bytes | expression records | declaration records | SHA-256 |
| --- | ---: | ---: | ---: | --- |
| original generated helper | 44,002,216 | 778,146 | 8,077 | `71a0c52bab8b42b11379cc2fcfafcc01a277a56f04e2dd7e1223e2c09a1ec47a` |
| exact local replacement | 44,022,108 | 778,463 | 8,084 | `80a2623ebed8a530d026cafc00e727df0287d9ad18bda80150b78f5a7a9fe9bf` |

The replacement export is slightly larger, so its acceptance is not explained
by a smaller file or declaration closure.  The changed local proof shape is
the relevant difference.

Exactly three proof-replay launches consumed 307.271 of the permitted 600
checker-wall seconds:

| attempt | input/kernel | result | elapsed | peak memory |
| --- | --- | --- | ---: | ---: |
| 1 | unchanged helper / Lean export checker | timeout, no verdict | 120.379 s | 8,895,926,272 B |
| 2 | unchanged helper / NanoDa | timeout, no verdict | 120.957 s | 5,317,881,856 B |
| 3 | replacement / stock con-ron verified mode | accepted | 65.935 s | 239,558,656 B |

No launch was retried.  The optional predecessor and instrumented-con-ron
slots were skipped.  An optional compilation of a copied full Foundation
source file was not launched because the containment launcher reported its
user-systemd manager unavailable; it is not used as evidence and did not
consume replay budget.  The project-local exact theorem, its export, and its
stock con-ron replay are the tested evidence.

The direct Lean-checker command used `--from-export` without Comparator's
`--silent` option; it nevertheless emitted no progress or verdict.  A separate
attempt to capture `leanchecker` help failed with an incompatible cached
Lean-4.34.1 `Leanc.olean` and therefore supplies no interface evidence.  The
diagnostic NanoDa JSON explicitly set `num_threads` to 1.  Supervisor elapsed
time exceeded the 120-second deadlines by 0.379 seconds for Lean and 0.957
seconds for NanoDa; these are measured end-to-end deadline overruns, not
evidence about where either checker was executing.

## Proposed integration

At this checkpoint, `proposed-foundation-change.patch` passed
`git apply --unidiff-zero --check`
against pinned Foundation commit
`e72cfe981aa65166f37fa4e2584f4806bc48d72f`.  It adds the same named
substitution/result lemmas and changes only the source field

```text
Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Basic.lean
IsUTerm.BV.construction.func_defined
```

from the broad `simp [blueprint]` proof to the checked factored proof.  It had
not been compiled in the actual Foundation source context at this checkpoint;
the pinned package was not edited and the patch was not published as a fork.
The later integration checkpoint in
`Audit/palomar-foundation-integration-20260928/` records the first actual
source-context build and its separate bounded publication gate.

## Remaining obligations

The third result still lacks cumulative external verification.  Six selected
declarations remain to migrate, and complete official Palomar verification
remains outstanding.  No verifier process was left running.
