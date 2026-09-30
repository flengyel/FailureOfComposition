# Gödel-II range migration and cumulative Seven result

## Outcome

The exact independent Gödel-II range counterexample is implemented and the
cumulative `ChallengeSeven`/`SolutionSeven` pair passed local Comparator at
project commit `16e73188e12244f651c7ce57207095bd0d223a44`. Stock con-ron,
NanoDa, and Lean's default kernel explicitly accepted the solution. This is a
local seven-result checkpoint, not official Palomar verification.

## Mathematical bridge

`RangeInterface.lean` defines the independent range graph
`r = w ∧ ∃ x, G_e(x,r)`, the PA-uniform realization predicate, and a
fixed epsilon-selected range index. `RangeBridge.lean` proves formula and
uniform-realization translation, existence and correctness of the selector,
and choice independence against the maintained `rangeIndex`. The two-operand
pointwise equivalence is proved separately and transports negation. The final
theorem preserves the maintained witness and the exact consistent/r.e.-axiom
PA-extension hypotheses. Its closure reaches the maintained Gödel-II/Craig
root and excludes the productive range route. See `CORRESPONDENCE.md` for the
exact declarations.

## Focused validation

- The separate-environment checker compared 4,481 statement-side constants,
  required ownership of all seven results, found exactly seven Challenge
  theorem holes and no definition holes, and limited Solution axioms to
  `propext`, `Classical.choice`, and `Quot.sound`.
- ChallengeSeven is 42,249 bytes and 966 lines. It passes the 100 KiB/1,000-line
  hard gate with the expected preferred-surface warning.
- The seven-root proof union is 21,798 constants, 82 above Six. The seventh
  root alone reaches 20,257 constants.
- Strict builds, configuration validation, source policy, route/axiom audits,
  launcher path-propagation smoke, and intended negative regressions passed.

## Comparator evidence

The Challenge export is 15,691,644 bytes with SHA-256
`20e1cac661f1947ed9fd0bc7b5d39d7ac9a2f27a12705ecd5b0f95c44c5db5db`.
The Solution export is 158,127,081 bytes with SHA-256
`784ca63776a83356b0d63ed4ad9b6a3c1bd14e7ac936f9ed5b19850a3e4463f4`.
Full exports remain under `.codex-work` and are omitted from the compact
archive. Timestamped before/after records and an exit-zero comparison confirm
that both exports and both configurations were unchanged.

One parent invocation launched the checkpoint's sole Comparator payload from
2026-09-30 01:27:53Z through 01:31:13Z. Contained elapsed time was 199.537
seconds; GNU time measured 197.88 seconds for Comparator. Aggregate CPU was
198.623975 seconds and aggregate peak memory was 787,070,976 bytes. The cgroup
recorded zero `memory.high`, `memory.max`, OOM, deadline, pressure-stop, and
swap events, and final cleanup left the owned cgroup empty. Con-ron accepted
20,797 declarations in verified mode; NanoDa and Lean also accepted, and
Comparator printed `Your solution is okay!`.

## Remaining work

Declarations 8–9 still require migration and local cumulative validation.
Complete official Palomar verification, submission, and registration also
remain; none was attempted here.
