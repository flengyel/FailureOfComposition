# Cumulative Six audit

This directory contains the reproducible exact-interface, dependency/axiom,
negative-regression, source-policy, stable-export, protected-configuration, and
contained Comparator harness for `ChallengeSix`/`SolutionSix`.

The decisive selection is the first five accepted declarations followed by
`FailureOfComposition.Palomar.weak_totality_counterexample`. The portable JSON
has no machine-local kernel paths. `prepare_comparator.py` creates a protected
copy by adding only the authenticated con-ron and NanoDa commands.

`record_input_hashes.py` records both exports and both configurations before
and after the payload; `compare_input_hashes.py` requires exact identity. Full
NDJSON exports remain under `.codex-work` and are intentionally excluded from
the compact evidence archive.

The tested candidate is
`b923699c670857f174ab445483d1508a453eaab0`.  The sole Comparator payload
passed con-ron, NanoDa, and Lean's default kernel in 199.351 seconds under
aggregate containment, peaking at 803,315,712 bytes without pressure or limit
events.  `RESULT.json` is the machine-readable result and `REPORT.md` explains
the proof bridge, focused gates, attempt accounting, and remaining work.
