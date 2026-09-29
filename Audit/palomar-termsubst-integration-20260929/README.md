# TermSubst integration and cumulative Three validation

This checkpoint factors the Foundation `TermSubst.construction.bvar_defined`
proof, validates it in the actual module context, publishes the exact repair,
pins it in FailureOfComposition, and checks the cumulative eligible Three pair.

## Exact repairs and revisions

- Foundation parent: `46715b758b3069351825f276f1d98de1e60f1e4f`.
- Tested/public Foundation repair:
  `01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d`, tree
  `4f6d06e90aacdc5688064d089fa7160e109ce2dc`.
- Public branch: `flengyel/foundation`,
  `palomar-termsubst-bvar-repair-20260929`.
- Tested project source/pin/configuration:
  `9dc0a581dcc023fa0918cdf05e38c7c5288907de`.
- Lean remains `4.35.0-rc2`; Mathlib remains
  `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The Foundation patch changes only
`Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Functions.lean`.
It preserves the `TermSubst.blueprint`, the three computational record fields,
and the existing fvar/func proof fields.  It replaces only the bound-variable
proof with named, narrowly typed evaluation and substitution lemmas.  The
ordinary full-index patch in this directory applies to the exact parent with
plain `git apply --check`.

## Contract audit

The real patched module compiled with `-DwarningAsError=true`.  Separate
baseline and patched snapshots establish identical blueprint type/body,
identical construction public type, and identical normalized types and bodies
for all three computational assignments.  Only the intended `bvar_defined`
record argument changes.

`constructionBvarDefinedExact` is inferred from the new field theorem's
`.defined` projection.  Its raw expression is not identical to the fully
unfolded field obligation; `PatchedConstructionAudit.lean` records
`RAW_TYPE_EQUAL false`.  An ordinary Lean-checked assignment theorem proves
kernel convertibility to the unchanged obligation.  The field and projected
proof closures exclude the old construction proof, and the integrated closure
uses exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Integrated and cumulative checks

The integrated construction export is 43,708,676 bytes, contains 774,125
expression and 7,984 declaration records, and has SHA-256
`e1e79e14a42c5cf31b3c12c0ecc0a146399a8f62ed9550df7d3c843e56e5ba6d`.
Stock con-ron accepted 7,980 declarations and completed 7,602 checks in 24.250
seconds; contained elapsed time was 24.481 seconds and peak memory was
253,480,960 bytes, with no resource event.

After pinning, the active Functions target and `SolutionThree` rebuilt.  The
strict source checks, exact separate-environment interface/ownership/body
comparison, Challenge source policy, recursive axiom/dependency audit,
productive-versus-Gödel route audit, configuration check, and negative
regressions all passed.  The selected closure is 21,260 constants.

Stable Comparator exports were produced with the pinned exporter and the exact
Comparator root order:

- Challenge: 14,380,640 bytes,
  `d4082d08628fff75f298333d2aa71944a22a73ab25d163439679f9908fc513ae`.
- Solution: 154,914,915 bytes,
  `f67bbf4bb981e813f60061cc54b5bd6d097ceb8ca92104ef838e71aee507d7e6`.

The exact cumulative Three Comparator run accepted the pair through con-ron,
NanoDa, and Lean's default kernel and printed `Your solution is okay!`.
Contained elapsed time was 161.947 seconds; peak aggregate memory was
779,714,560 bytes.  No pressure, memory-high/max, deadline, swap, OOM, or pids
event occurred.

This is a local Comparator pass for exactly three declarations.  It is not
official Palomar verification, does not verify the other six declarations, and
does not submit or register the project.
