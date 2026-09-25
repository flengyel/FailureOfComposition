# Lean 4.35 port status

Checkpoint: 2026-09-24. **Incomplete: the focused Foundation blocker is cleared,
but no full target build has been started.**

## Revisions and working state

- Accepted source checkpoint: `93fc6536f17f84933edf6d223eb41c8e3a9f866c`.
- Setup/current branch base: `be387e664cae010432f13786ea48b55efdaa0e26` on
  `codex/lean-4.35.0-rc2`.
- Target Lean: `leanprover/lean4:v4.35.0-rc2`.
- Target Mathlib: `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
- Target Foundation: `e72cfe981aa65166f37fa4e2584f4806bc48d72f`.
- The source repairs, manifest, toolchain, Lake configuration, and package-preparation
  changes are preserved in a local incomplete checkpoint on the migration branch.
  No full build or final audit has passed yet.

## Focused Foundation diagnostic

The unchanged target Foundation module
`Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Basic.lean`
compiles successfully with the final `-M 12288` ceiling. Lower Lean memory
ceilings, including `-M 7200` and `-M 10240`, stopped at `Basic.lean:628:30`
with `(kernel) excessive memory consumption detected`.

Lean 4.35.0-rc2 implements `-M` by multiplying the option by `1024 * 1024`, so
`-M 12288` is a 12 GiB Lean memory ceiling.

### Final 12 GiB ceiling: success

Starting from repository checkpoint `1fd80f521d17432a8574626e391182481577d9be`,
the checkout was clean and Foundation/Mathlib still matched the target hashes.
Linux reported `16,379,120 KiB` RAM and the existing `8,388,604 KiB` manual swap
file was active and unused. No Lean/Lake compiler was already running.

The 10 GiB diagnostic harness was copied and changed only to use a separate
`12288` filename/log/PID namespace and `-M 12288`. The unchanged module was run
exactly once:

```text
cd /home/flengyel/src/FailureOfComposition-port/Lean
LEAN_NUM_THREADS=1 FAILCOMP_STYLE_JOBS=1 bash ../.codex-work/tmp/run-term-basic-diagnostic-12288.sh
```

It used one Lean compiler process (PID 28), `LEAN_NUM_THREADS=1`, `-j 1`, the
target package map, and a 20-minute TERM/KILL watchdog. Result:

- Classification: **successful unchanged-module compilation**.
- Exit status: `0`; watchdog status: `0`; no timeout, signal, or forced kill.
- GNU Time compiler elapsed time: `3:19.09`; complete harness elapsed time:
  `202` seconds.
- Compiler output: empty.
- Actual Lean maximum RSS/high-water mark: `12,557,152 KiB`
  (`11.9754 GiB`). GNU Time and the direct `/proc/28` samples agree.
- Maximum Lean `VmSwap`: `0 KiB`; maximum system swap use: `0 KiB`.
- Maximum swap-in and swap-out rates: both `0 KiB/s` for all 40 samples.
- The first measured loading interval had the maximum major-fault rates:
  `535/s` system-wide and `1,305/s` for Lean; the swap counters remained zero.
- Minimum system `MemAvailable`: `3,790,040 KiB` (`3.614 GiB`).
- No new OOM, `oom-kill`, or killed-process message appeared in either the
  before/after capture or the current kernel log.

The candidate source was not modified. Its Git blob is
`2460a4f2f0e29c135afd3d52b2a6d4cb4c514d61`, matching the working file, whose
SHA-256 is `85ec21dc81777ba6b4a21a78350ec5321ef36464bb37b3a54d95df2a4330322f`.
Because the unchanged complete module passed, no standalone proof-repair probe
or dependency patch was made.

### 10 GiB ceiling: Lean memory-limit failure

After WSL was configured for 16 GiB, Linux reported `16,379,120 KiB` of RAM
(`15.620 GiB` usable) and the existing `8,388,604 KiB` manual swap file was
active and unused. No Lean/Lake compiler was already running. Foundation and
Mathlib remained at the target hashes above.

The prepared diagnostic was run exactly once:

```text
cd /home/flengyel/src/FailureOfComposition-port/Lean
LEAN_NUM_THREADS=1 FAILCOMP_STYLE_JOBS=1 bash ../.codex-work/tmp/run-term-basic-diagnostic-10240.sh
```

It used one Lean compiler process (PID 28), `LEAN_NUM_THREADS=1`, `-j 1`,
`-M 10240`, the target package map, and a 20-minute TERM/KILL watchdog. Result:

- Classification: **Lean memory-limit failure**, not timeout or OS termination.
- Exit status: `1`; watchdog status: `0`; no signal or forced kill.
- GNU Time compiler elapsed time: `2:33.65`; complete harness elapsed time:
  `156` seconds.
- Compiler output:
  `Basic.lean:628:30: error: (kernel) excessive memory consumption detected`.
- Actual Lean maximum RSS/high-water mark: `10,487,504 KiB`
  (`10.0017 GiB`). GNU Time and the direct `/proc/28` samples agree.
- Maximum Lean `VmSwap`: `0 KiB`; maximum system swap use: `0 KiB`.
- Maximum swap-in and swap-out rates: both `0 KiB/s` for all 31 samples.
- The first measured interval had the maximum major-fault rates: `959/s`
  system-wide and `1,653/s` for Lean; the swap counters remained zero. Near the
  memory-limit event, the respective sampled rates were `1/s` and `2/s`.
- Minimum system `MemAvailable`: `5,850,044 KiB` (`5.579 GiB`).
- No new OOM, `oom-kill`, or killed-process message appeared in either the
  before/after capture or the current kernel log.

This run established that, once the previous swapping pressure was removed,
the compiler reached Lean's configured 10 GiB limit at the same declaration
well before 20 minutes. The later 12 GiB run established successful checking
under that final ceiling; it does not establish a smaller exact minimum.

### Previous 8 GiB WSL diagnostic

The earlier corrected `-M 10240` command was:

Command (exit 124):

```text
cd /home/flengyel/src/FailureOfComposition-port/Lean && LEAN_NUM_THREADS=1 /home/flengyel/src/FailureOfComposition-port/Lean/../.codex-work/tmp/gnu-time/usr/bin/time -v timeout --signal=TERM --kill-after=30s 20m lake --packages=/home/flengyel/src/FailureOfComposition-port/Lean/../.codex-work/tmp/target-packages.json env lean -M 10240 -j 1 -R /home/flengyel/src/FailureOfComposition-port/Lean/.lake/packages/Foundation /home/flengyel/src/FailureOfComposition-port/Lean/.lake/packages/Foundation/Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Basic.lean
```

Its observed result was a **20-minute timeout**, elapsed `20:00.06`, with an
empty compiler log. No Lean memory-limit diagnostic, OS OOM message, or
killed-process message was observed in that run.

The 241 five-second system samples recorded a maximum system-wide
`MemTotal - MemAvailable` of `8,071,916 KiB` and a maximum system-wide swap use
of `6,060,376 KiB`; these maxima occurred at different times. They are system
pressure observations, not the compiler's memory requirement, and must not be
added to infer one.

GNU Time reported `808,108 KiB` maximum RSS, `0.43 s` user CPU, and `1.23 s`
system CPU for the logged command whose direct operand was
`timeout ... lake ...`. No Lean PID was captured in that run, so this field does
not establish the compiler's maximum RSS. The new direct-PID measurement does
not retroactively turn the earlier system-wide measurements into compiler RSS.

The contrast is consistent with severe paging causing the earlier timeout:
the old run used up to `6,060,376 KiB` system swap, while the 10 GiB direct-PID
run used none and reached the Lean limit in about 2.5 minutes. That causal
explanation is an inference; the recorded outcomes themselves are timeout
versus explicit Lean memory-limit failure.

Preserved evidence:

- `.codex-work/logs/diagnostic-term-basic-v435-memory-10240.command.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-10240.compiler.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-10240.time.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-10240.usage.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-10240.status.log`
- `.codex-work/logs/diagnostic-term-basic-memory-7200.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-10240-pid.command.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-10240-pid.preflight.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-10240-pid.compiler.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-10240-pid.time.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-10240-pid.usage.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-10240-pid.status.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-10240-pid.oom-before.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-10240-pid.oom-after.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-10240-pid.oom-diff.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-12288-pid.command.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-12288-pid.preflight.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-12288-pid.compiler.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-12288-pid.time.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-12288-pid.usage.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-12288-pid.status.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-12288-pid.oom-before.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-12288-pid.oom-after.log`
- `.codex-work/logs/diagnostic-term-basic-v435-memory-12288-pid.oom-diff.log`

## Declaration inspection

The reported location is the `func_defined` field of
`FFL.FirstOrder.Arithmetic.Bootstrapping.IsUTerm.BV.construction`:

```lean
noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar (_ z) := z + 1
  fvar (_ _) := 0
  func (_ _ _ _ v') := listMax v'
  bvar_defined := .mk fun v ↦ by simp [blueprint]
  fvar_defined := .mk fun v ↦ by simp [blueprint]
  func_defined := .mk fun v ↦ by simp [blueprint]
```

Its blueprint's function graph is
`.mkSigma “y k f v v'. !listMaxDef y v'”`. The previously failing proof is
generated by `simp [blueprint]` and discharges the `𝚺₁.DefinedFunction`
obligation for the four-argument function that ignores the first three inputs
and returns `listMax` of the fourth. It depends immediately on `listMaxDef` and
`listMax_defined` from `Arithmetic/HFS/Vec.lean`, where `listMaxDef` is the
result graph of the vector recursion using zero for nil and `max` for adjoin.

The accepted Foundation checkout at
`a3dd617f88bda178eb6c206dd5db91f88b6a2a42` is locally available. The complete
construction block is source-identical there. Its immediate `listMax` block is
also source-identical apart from the root namespace rename `LO` to `FFL`; the
term file additionally moved under `FirstOrder/Arithmetic/Bootstrapping` and
its import was adjusted accordingly. Thus there is no observed mathematical or
proof-script change at the expensive declaration. The concrete environmental
change is Lean 4.32.2 to 4.35.0-rc2, together with Foundation's namespace/file
reorganization. A target-toolchain kernel or simplifier performance regression,
or a changed generated proof term, is plausible but remains a hypothesis.

## Disposition

The final authorized memory increase succeeded and its separate logs are
preserved. No Lean/Lake compiler remains. Do not raise the 12 GiB ceiling or
begin a full build automatically. `Term/Basic.lean` is no longer the focused
blocker, and no dependency modification is proposed. The next obligation is the
first full target build followed by the required style, theorem/type, axiom,
dependency, kernel-replay, and paired-draft checks, in a separately authorized
continuation.

Those full-build and audit checks remain pending; this focused success is not a
verified port.
