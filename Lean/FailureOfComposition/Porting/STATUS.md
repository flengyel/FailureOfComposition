# Lean 4.35 port status

Checkpoint: 2026-09-24. **Incomplete: blocked before the first full target build.**

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

## Current blocker

The focused target-toolchain compilation of
`Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Basic.lean` is not
complete. Lower Lean memory ceilings, including `-M 7200`, stopped at
`Basic.lean:628:30` with `(kernel) excessive memory consumption detected`.

Lean 4.35.0-rc2 implements `-M` by multiplying the option by `1024 * 1024`, so
`-M 10240` is a 10 GiB Lean memory ceiling.

### Post-restart 16 GiB WSL diagnostic

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

This run establishes that, once the previous swapping pressure was removed,
the compiler reached Lean's configured 10 GiB limit at the same declaration
well before 20 minutes. It does not establish how much memory successful
checking would require and does not justify increasing the limit automatically.

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
the old run used up to `6,060,376 KiB` system swap, while the new run used none
and reached the Lean limit in about 2.5 minutes. That causal explanation is an
inference; the recorded outcomes themselves are timeout versus explicit Lean
memory-limit failure.

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
`.mkSigma “y k f v v'. !listMaxDef y v'”`. The failed proof is generated by
`simp [blueprint]` and discharges the `𝚺₁.DefinedFunction` obligation for the
four-argument function that ignores the first three inputs and returns
`listMax` of the fourth. It depends immediately on `listMaxDef` and
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

The prepared diagnostic has been consumed and its separate logs are preserved.
No Lean/Lake compiler remains. Do not rerun it, raise `-M 10240`, or begin a full
build automatically. The unresolved blocker is now the target-toolchain kernel
memory failure while checking the source-identical `func_defined` proof at line
628; the next work should diagnose or locally repair that proof without changing
the pinned revisions or theorem content.

The full native build and all required style, theorem/type, axiom, dependency,
kernel-replay, and paired-draft checks remain pending behind this blocker.
