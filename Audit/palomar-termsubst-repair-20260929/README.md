# TermSubst bound-variable proof experiment

This checkpoint investigates
`FFL.FirstOrder.Arithmetic.Bootstrapping.TermSubst.construction._proof_2`
without changing the active FailureOfComposition dependency pin or any
mathematical statement.  The exact tested project candidate remains
`8094240bb8bfedc34fb875140111f95aabdf79b8`, and the active public Foundation
revision remains `46715b758b3069351825f276f1d98de1e60f1e4f`.

## Result

The project-local standalone proof in [`StandaloneReplacement.lean`](StandaloneReplacement.lean)
passes strict compilation with `-DwarningAsError=true`.  Before this namespaced
export candidate was made, the same proof strategy was checked in the original
`TermSubst` namespace against the original compiled Foundation environment:

- its universe-renamed, alpha-normalized elaborated type was exactly
  `TermSubst.construction._proof_2`'s type under `Lean.Expr.eqv`;
- its recursive closure had 1,719 declarations and excluded the original
  generated helper;
- its recursive axioms were exactly `Classical.choice`, `Quot.sound`, and
  `propext`.

The standalone checker candidate repeats the 1,719-declaration closure with a
fresh namespace and additionally excludes the patched/integrated construction
declarations.  Its dependency-closed export includes both the inferred
exact-type theorem and its named `bvar_defined` field proof.  The export is
43,394,988 bytes, has SHA-256
`1234ba6a1a2533a797a0c3a8f1482b849e3b2d24cc3acae85deab90aaf0351ce`,
and contains 768,087 expression records and 7,957 declaration records.

Unmodified stock con-ron, SHA-256
`4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`,
accepted that standalone export in verified mode.  It accepted 7,953
declarations and completed all 7,576 checks.  Checker time was 29.239 seconds;
the containing workload elapsed 29.495 seconds and peaked at 247,910,400
bytes.  There were no `memory.high`, `memory.max`, swap, OOM, pressure-stop, or
deadline events.

This is a standalone acceptance only.  It is not an integrated Foundation
repair, a cumulative Three pass, a NanoDa or Lean-export replay, or official
Palomar verification.

## Contextual one-field experiment

The ordinary full-index patch
[`termsubst-bvar-repair.patch`](termsubst-bvar-repair.patch) applies cleanly to
Foundation `46715b758b3069351825f276f1d98de1e60f1e4f`.  It changes only
`Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Functions.lean`,
adds the factored substitution/evaluation helpers, and replaces only

```lean
bvar_defined := .mk fun v ↦ by simp [blueprint]
```

with the named field proof.  `TermSubst.blueprint`, all three computational
fields, and the source proofs of `fvar_defined` and `func_defined` are
unchanged.  The real modified `Functions.lean` compiled strictly in 34.751
seconds at 383,803,392 bytes peak.  A body-sensitive baseline/patched record
snapshot confirms the unchanged blueprint type/body and construction type;
all computational arguments and the fvar/func proof arguments agree after
only the documented generated-name renumbering.  The construction directly
reaches the named new field proof, and its 8,551-declaration recursive closure
uses only the three permitted axioms.

The final exact-contract audit did not pass.  The contextual source stated
`constructionBvarDefinedExact` explicitly, and that proposition is
definitionally equivalent to the record obligation but not the same raw Lean
expression.  After universe/binder normalization and metadata removal, the
first difference has `OfNat.ofNat` in the explicit type where the inferred
field obligation has `HAdd.hAdd`.  The standalone theorem avoids this mismatch
by letting Lean infer the type of the named field's `.defined` projection.

Both authorized actual patched-Functions compile payloads had already been
used (the first exposed and the second corrected an unused-instance warning),
so the source was not revised and compiled a third time.  Consequently no
integrated export was replayed, and no local Foundation repair commit was
created.  The smallest follow-up is to define the field from the already
checked evaluation lemma, then define the exact theorem by inferred projection
type, compile that one-field source, repeat the exact contract/closure audits,
and only then replay the integrated construction.

## Artifact-overlay remediation

During audit setup, copying patched companion files onto symlink destinations
followed four links and overwrote the active package's compiled
`.olean.private`, `.olean.server`, `.ir`, and `.ir.sig` files.  No source,
manifest, Git pin, public `.olean`, or `.ilean` changed.  The mistake was
detected before the next audit workload.  A first remediation compile without
Lake's setup metadata did not match the retained public `.olean` and was not
copied back.  A second remediation used the exact retained Lake setup JSON;
its public `.olean` and `.ilean` matched the retained originals byte for byte,
so its matching companions were restored.

The restored active artifact hashes are:

| Artifact | SHA-256 |
| --- | --- |
| `Functions.olean` | `9495d5ffc2c21904f8cc6e0a3892cc90c94e3b63593944096b1d59206606adc7` |
| `Functions.ilean` | `8e503c9c11a00fb18fb7b92e9da82e0a40323094cd9721c02675b50aa82b352c` |
| `Functions.olean.private` | `d1de90cbd93785e7d5610167b006a5e5090d6bc12c1977b19af453521407106f` |
| `Functions.olean.server` | `5e39c93b0325c9cc1c62b88c1af480f22b1b2c4c8f7df0e418d2fed9af66993f` |
| `Functions.ir` | `426360adef640cfeb3ae587b25ad7af586bd641db1b73317eaff196c4540c09f` |
| `Functions.ir.sig` | `ce3b734d463c13a9d4acffc42cd5558777271fb404426b8fa252b92a0639bb53` |

The active Foundation checkout is clean at the unchanged pin.  The two
remediation compiles are infrastructure recovery evidence, not additional
proof-validation or checker payloads.

## Remaining work

Publication/pinning of a TermSubst repair, downstream SolutionThree rebuild,
focused Three gates, cumulative con-ron/NanoDa/Lean verification, the other six
declaration migrations, and complete official verification remain.  No
cumulative Comparator or official verifier ran in this checkpoint.
