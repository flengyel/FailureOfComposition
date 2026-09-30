# Cumulative Seven checkpoint

This audit directory contains the focused checker, route/dependency audit,
negative regressions, source-policy adapter, stable-export commands, protected
configuration preparation, and bounded Comparator launcher for
`range_counterexample_godel` and the cumulative seven-result pair.

The launcher takes an explicit absolute run directory as its first argument.
Its smoke test and decisive attempt therefore place command records, payload
logs, hash records, and cgroup telemetry under the same run directory.

The portable configuration remains under `Lean/` and contains no machine-local
kernel commands.  `prepare_comparator.py` makes a protected local copy by adding
only the authenticated con-ron and NanoDa commands.

The completed checkpoint is summarized in `REPORT.md` and `RESULT.json`.
The tested code/configuration commit is
`16e73188e12244f651c7ce57207095bd0d223a44`; its sole cumulative payload was
accepted by con-ron, NanoDa, and Lean's default kernel. Full exports remain in
the retained `.codex-work` run tree and are identified by hashes in the report.
