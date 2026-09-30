# Generated quotient and cumulative Nine

The ninth eligible selection is the unnumbered consequence after manuscript
Theorem 4: for every Sigma-one-sound deductive PA extension, the quotient by
the generated composition congruence is multiplicatively equivalent to the
actual unary partial recursive functions, and the equivalence maps every index
class to that index's actual evaluation.

## Checked implementation

The proof/interface sources were committed at
`6bcb9f691053bfa9ea16939be1950fa25e4e8753`; the exact tested
code/configuration/harness commit, including the corrected evidence-path guard,
is `381de9db4d2214b8fd8d05bf74b56bc9597f01c5`.

`GeneratedQuotientInterface.lean` defines the independent quotient,
representatives, multiplication, unit, actual unary partial recursive target,
and `ofIndex`. `GeneratedQuotientBridge.lean` descends actual evaluation using
the migrated generated-congruence classification, proves bijectivity using the
pinned Mathlib code-existence theorem, and proves multiplication using the
evaluator composition law. It also checks representative, multiplication,
unit, and maintained-equivalence correspondence. The unit argument proves
equality of quotient classes; it does not assert literal equality of the fixed
identity index and the maintained chosen realization.

The exact separate-environment checker compared 5,149 recursively reachable
statement declarations. `ChallengeNine` has exactly nine selected theorem
holes, no definition holes, and no untrusted import. It is 44,209 bytes and
998 lines, within the 100 KiB/1,000-line hard limits and above the preferred
32 KiB/300-line review surface. All selected Solution closures use only
`propext`, `Classical.choice`, and `Quot.sound`. The ninth root contains 16,160
constants; the cumulative union contains 21,850, 39 more than Eight.

## Local Comparator result

The first stable-export parent invocation failed before any payload because
the new launcher's path guard retained a stale directory name. The failure was
preserved; the one-line harness repair was committed before the successful
export and Comparator input identity was recorded.

One cumulative Nine Comparator payload ran with one CPU,
`LEAN_NUM_THREADS=1`, 8 GiB `memory.high`, 10 GiB `memory.max`, zero workload
swap, the retained PID limit, a 1,200-second deadline, and the full-PSI guard.
Comparator accepted the exact pair through stock con-ron, NanoDa, and Lean's
default kernel and printed `Your solution is okay!`. Con-ron accepted 20,847
declarations.

Contained elapsed time was 181.897 seconds (178.69 seconds for Comparator),
aggregate CPU time was 180.918623 seconds, and peak aggregate memory was
989,483,008 bytes. There were no pressure, memory-high/max, deadline, swap, or
OOM events. Cleanup left the owned cgroup empty. Timestamped before/after
records show identical hashes for both exports and both configurations.

The Challenge export is 18,976,072 bytes with SHA-256
`cbc5f32f3da1b7c40612c3bf07f5d1da9f663ed0100225c1f2701d726c8fff03`.
The Solution export is 158,336,512 bytes with SHA-256
`5ddfa3701144f56f12ac354f3eabc5e0a8414c4cac923630cc06769a33f5259e`.
Their full bytes remain under the retained `.codex-work` evidence tree and are
omitted from the compact delivery archive.

## Remaining work

All nine selected declarations are migrated and locally kernel verified at the
recorded candidate. Complete official Palomar verification, final submission
snapshot/licensing review, submission, and registration were not attempted.
