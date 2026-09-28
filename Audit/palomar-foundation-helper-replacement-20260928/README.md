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
unchanged input is uniquely problematic for con-ron.

A project-local theorem was then proved with exactly the original generated
helper's elaborated type, modulo deterministic universe-parameter renaming.
Instead of asking simplification or definitional equality to expand
`blueprint.func.val`, its proof:

1. reduces only the `Blueprint.func` record projection;
2. rewrites with `HierarchySymbol.Semiformula.val_mkSigma`;
3. uses a named `eval_substs` identity for the two substituted terms; and
4. finishes with `Arithmetic.listMax_defined.iff` and a small coordinate
   identity.

The strict compile completed in 4.644 seconds with 196,042,752 bytes peak
aggregate memory.  The exact type/dependency/axiom audit completed in 7.449
seconds with 249,417,728 bytes peak memory.  It established:

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

The narrowest source-level control states only the definitional equality
between `blueprint.func.val` and the substituted `listMax` formula and proves
it by `rfl`.  Its bounded Lean elaboration did not finish: 120.349 seconds,
8,592,031,744 bytes peak, 32,881 `memory.high` events, and no OOM.  In contrast,
the targeted record-projection reduction and named rewrite compile cheaply.
Together with the stock replacement acceptance, this demonstrates that broad
definitional reduction of this blueprint projection is the active expensive
operation and that the narrow proof avoids it.  It still does not identify a
particular kernel cache, annotation step, conversion subroutine, or cleanup
mechanism as the low-level cause.

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

## Proposed integration

`proposed-foundation-change.patch` passes `git apply --unidiff-zero --check`
against pinned Foundation commit
`e72cfe981aa65166f37fa4e2584f4806bc48d72f`.  It adds the same named
substitution/result lemmas and changes only the source field

```text
Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Basic.lean
IsUTerm.BV.construction.func_defined
```

from the broad `simp [blueprint]` proof to the checked factored proof.  The
pinned package was not edited and the patch has not been published as a fork.
A future checkpoint must create and record a public Foundation revision,
update provenance/pins deliberately, rebuild the maintained declarations,
rerun exact interfaces/routes/axioms/source policy, and only then decide
whether a cumulative Three Comparator attempt is warranted.

## Remaining obligations

The third result still lacks cumulative external verification.  Six selected
declarations remain to migrate, and complete official Palomar verification
remains outstanding.  No verifier process was left running.
