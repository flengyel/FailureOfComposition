# Cumulative Three con-ron localization

Date: 2026-09-28 (UTC evidence directory `20260928T230001Z`)

The mathematical candidate, Challenge/Solution sources, portable Comparator
configuration, and dependency pins were not changed.  The tested candidate and
configuration remain commit
`8094240bb8bfedc34fb875140111f95aabdf79b8`; the starting documentation head was
`d6f5b162ccf7832e92efa8035511c1c3bef9da08`.

## Result

The current cumulative Three bottleneck is localized to the stock con-ron check
boundary for

```text
FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_2
```

This generated theorem is an evaluation identity used only by
`TermSubst.construction._proof_8`, the proof of the `bvar_defined` field at
`Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Functions.lean:25`:

```lean
bvar_defined := .mk fun v ↦ by simp [blueprint]
```

The evidence localizes a performance boundary.  Neither replay returned an
acceptance or rejection, and the evidence does not identify con-ron's internal
conversion, inference, cache, annotation, or allocation operation.

## Input and provenance

The Solution export named by the earlier Comparator process log survived at
`.codex-work/tmp/tmp.XX2uxj18`.  It was copied before any replay to the stable
local path
`.codex-work/palomar/three-conron-localization/20260928T230001Z/exports/solution-three-full.ndjson`.
Its newly measured identity is:

| property | value |
| --- | ---: |
| bytes | 154,905,023 |
| SHA-256 | `64877ccc19f40fc23b59545e0f7afd26f0a6e9dd7ff00c2921620476be5dfe62` |
| export format | lean4export 3.1.0 |
| expression records | 2,757,532 |
| declaration records | 20,286 |
| con-ron checks after installation | 19,728 |

The previous archive did not record this cumulative export's hash.  The hash
therefore authenticates this diagnostic input but cannot retrospectively prove
byte identity with the earlier Comparator input.  Provenance is additionally
supported by the retained process command, exact selected roots, source hashes,
active public Foundation pin, compiled `SolutionThree.olean` hash, permitted
axioms, and the previously passing focused gates.  The export contains exactly
the axiom records `propext`, `Quot.sound`, and `Classical.choice`.

The relevant identities were unchanged:

| item | identity |
| --- | --- |
| Lean | 4.35.0-rc2, `11acb17ec6b07a8f9e9173e6845197929540936b` |
| Mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Foundation | `46715b758b3069351825f276f1d98de1e60f1e4f` |
| PalomarSubmission | `a59f25bd8a66bf6faf3a4f4260d412989c0185ea` |
| stock con-ron SHA-256 | `4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef` |
| leanexport SHA-256 | `c5bc1a10a21e22cbb3671d65987cdef2076833b14182d823ccb2153adf2fa954` |
| `ChallengeThree.lean` SHA-256 | `3278113aa6033b45b8b42ef3d4f8e7183c58bf8883e89af541f3ea62bb5cdf74` |
| `SolutionThree.lean` SHA-256 | `1bb5a940a507b31e9fe5459b6d3941a894a420585dce73516422f54f8776b777` |
| portable configuration SHA-256 | `72d9a84010d5ac2e8fb2e0144a58adf06b623e7d266a816b468b3e2cd6da5265` |
| `SolutionThree.olean` SHA-256 | `e11993154cacdd33e68ca0deb103d7b3d65ad2dbc97fadc7fa36152bed1829e2` |

## Progress semantics

The authenticated installed help says that `--jobs=1` uses the plain sequential
check loop, results are walked in record order, installation heartbeats are
printed before installation, and check heartbeats are printed only after a
check completes.  Both runs used the unchanged stock executable with
`--verified --jobs=1 --progress=1`.

A last completed heartbeat alone does not name the active declaration.  The
two-run comparison removes that ambiguity:

1. In the full export, con-ron completed check 16,967/19,728,
   `TermSubst.construction._proof_7`, at 61.079 seconds.  The next installed and
   exported theorem was `_proof_2`; no later completion appeared.
2. `_proof_7` is a trivial `NeZero (1 + 1)` proof with an 84-constant closure.
   It is absent from the `_proof_2` closure, which contains 8,516 constants.
3. In the dependency-closed `_proof_2` replay, con-ron completed check
   7,562/7,568, `nth.congr_simp`, at 23.817 seconds.  The next installed and
   exported theorem was again `_proof_2`; no later completion appeared.
4. The full replay had already completed `nth.congr_simp` and continued far
   beyond it, while the isolated replay does not contain `_proof_7`.  The
   shared pending boundary is therefore `_proof_2`, not cleanup of either last
   completed predecessor.

The dependency-closed export was produced by the pinned exporter from the
existing authenticated build, with `_proof_2` plus Comparator's primitive and
support roots:

| property | value |
| --- | ---: |
| bytes | 43,376,011 |
| SHA-256 | `58120b32d32e3bab1b355e1fc77e52c2707b6e28e2bdd9641a7afbe29f79de7b` |
| expression records | 767,800 |
| declaration records | 7,949 |
| con-ron checks after installation | 7,568 |

Export-local indices and hygienic binder names differ between the two streams.
After replacing local indices by content digests and omitting binder names for
alpha-equivalence, the target type hash is
`eb8ebe9d06a2a8603540fb78bdd6b60fa1a7f5ff1bf18e8f4d7abd74ed78bb24`
and the target body hash is
`15444cbdbe6934c770744e1c455684bbef08651c2f63de01da96ae7d2da20ffa`
in both exports.

## Bounded replays

Both payloads used one CPU/job, `LEAN_NUM_THREADS=1`, `memory.high=8G`,
`memory.max=10G`, zero swap, `memory.oom.group=1`, the established admission
reserves, and the 60-second sustained-full-PSI guard.  Host memory remained
available; pressure was local to the owned cgroup.

| replay | result | elapsed | CPU | peak memory | high/max/OOM events | peak full PSI avg10 | last completed check |
| --- | --- | ---: | ---: | ---: | --- | ---: | --- |
| cumulative Three export | pressure-aborted, no verdict | 215.675 s | 139.527 s | 8,955,527,168 B | 8,207 / 0 / 0 | 98.32 | `_proof_7` (16,967/19,728) |
| `_proof_2` closure | pressure-aborted, no verdict | 170.616 s | 90.799 s | 8,973,803,520 B | 6,484 / 0 / 0 | 98.36 | `nth.congr_simp` (7,562/7,568) |

The minimum sampled host `MemAvailable` values were 6,773,899,264 and
6,746,603,520 bytes.  Both cgroups were empty after immediate cleanup.  Total
supervised checker time was 386.291 seconds, within the 540-second budget.
There were exactly two checker parent invocations and two actual payloads; no
setup retry occurred.

## Static proof boundary

The generated `_proof_2` theorem states evaluation of
`TermSubst.blueprint.bvar` as the expected `nth` equation.  Its recursive
closure has only the permitted axioms.  `TermSubst.construction._proof_8`
reaches `_proof_2`; the corresponding `_proof_9` and `_proof_12` field proofs
do not.  The full `TermSubst.construction` closure has 8,545 constants.

The smallest justified next source experiment is therefore a one-field
Foundation change at `Term/Functions.lean:25`: replace broad
`simp [blueprint]` elaboration with a named, exact-type proof that reduces only
the `Blueprint.bvar` projection, proves the explicit evaluation/substitution
identity, and concludes through the existing `nth_defined.iff`.  Such a proof
must retain the same record field type, universes, instances, axioms, and
downstream route, and must be tested with unchanged stock con-ron before any
cumulative retry.  No such rewrite was made in this checkpoint.

## Disposition

This is a reproduced declaration boundary, not a kernel verdict or proof
defect.  Cumulative Three still lacks con-ron, NanoDa, and Lean acceptance on
the repaired pin.  The first two declarations retain their historical complete
local Three-kernel pass for their recorded Two checkpoint.  Six declarations
remain to migrate, and complete official verification remains outstanding.  No
checker or verifier was left running.

