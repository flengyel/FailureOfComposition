# Local Foundation integration checkpoint

Date: 2026-09-28 (America/New_York; run directory dated in UTC)

This checkpoint integrates the checked factored `func_defined` proof into an
isolated real Foundation checkout, rebuilds and audits it, and records a bounded
standalone-kernel setup failure.  It does **not** publish or pin a Foundation
fork and does not run cumulative Three Comparator.

## Source repair

The isolated checkout starts at Foundation
`e72cfe981aa65166f37fa4e2584f4806bc48d72f`.  Its local repair commit is
`46715b758b3069351825f276f1d98de1e60f1e4f`, with that exact parent and one
changed file:

```text
Foundation/FirstOrder/Arithmetic/Bootstrapping/Syntax/Term/Basic.lean
```

The repair adds explicit assignment, substitution-evaluation, and result
lemmas beside `IsUTerm.BV.blueprint`, packages them as
`constructionFuncDefined`, and changes only the `construction.func_defined`
field to use that theorem.  The first three helpers explicitly omit the
ambient `IΣ₁` model instance; their elaborated types confirm that only
`constructionFuncResult` and `constructionFuncDefined` require it.  The
blueprint, `bvar`, `fvar`, `func`, and the other two definedness fields are
unchanged.

The ordinary contextual patch has SHA-256
`d129d02bd32f143df31cbd444a4df0e0ad77e6fee8a67ad2efa5c4b663c9ed6a`
and passes plain `git apply --check` in a separate worktree at the parent
revision.  The modified source blob has SHA-256
`6a95b78fe707869e908b1b4a06f33826c4a670ddb2e9b8f7892764d3589b05dc`;
the parent source blob has SHA-256
`85ec21dc81777ba6b4a21a78350ec5321ef36464bb37b3a54d95df2a4330322f`.

## Actual-context build and audits

Foundation's target
`Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Term.Basic` and its full
1,071-job dependency graph were built in the isolated checkout.  The contained
build passed in 1,079.365 seconds, with 5,301,583,872 bytes aggregate peak
memory and no pressure, high/max, deadline, swap, OOM, or OOM-kill events.  A
second direct compilation of the real modified source with
`-DwarningAsError=true` passed in 52.086 seconds at 540,504,064 bytes peak and
printed no warnings.

Baseline and repaired modules were then loaded in separate environments.
After universe renaming and binder-name erasure—the existing exact comparison
convention—the following expressions match exactly:

- public `blueprint` type and body;
- public `construction` type;
- the elaborated `func_defined` proof obligation.

The repaired construction body directly depends on
`constructionFuncDefined`.  Its recursive axiom closure is exactly `propext`,
`Classical.choice`, and `Quot.sound`.  The named factored proof closure contains
8,660 constants and excludes the former expensive generated proof.  Lean still
uses the name `construction._proof_4`, now for the unrelated `bvar_defined`
field; its inspected type and dependencies establish that this is not a stale
copy of the old proof.

## Export and bounded gate

Pinned `leanexport` 3.1.0 exported the actual rebuilt `construction` and
`constructionFuncDefined` roots together with the normal Comparator primitive
roots:

| bytes | expression records | declaration records | SHA-256 |
| ---: | ---: | ---: | --- |
| 44,064,407 | 779,210 | 8,094 | `8d1ae06a757442846b5f3ad7190433adb7b462d97147f9132e2ed7011038ac63` |

The export remains local and is not included in the delivery archive; its
hash, statistics, roots, command, and tool identities are retained.

The sole authorized standalone integrated-construction con-ron parent
invocation failed at the containment runner's ordinary-user systemd-manager
preflight.  It created no run directory and no con-ron process.  Because the
task explicitly counts setup failures, the attempt allowance was treated as
spent and no retry was made.  The integrated export therefore has no stock
con-ron verdict.  Publication and project pinning were gated on such an
acceptance, so the local Foundation commit was not pushed to a public fork and
the project remains pinned to `e72cfe981aa65166f37fa4e2584f4806bc48d72f`.
The cumulative Three Comparator gate was not reached or attempted.

## Corrected historical account

The earlier timed attribution command named an unretained
`PieceBlueprint.lean`.  `BlueprintConversionControl.lean` is an untested later
proposal and is not assigned that timing.  The successful factored proof avoids
broad unfolding, but this does not locate an operation inside any external
kernel; the original mechanism remains unresolved.

The original-helper Lean-export-checker and NanoDa runs timed out silently.
Neither established that its checker reached the helper, and their resource
profiles differ.  The direct Lean run omitted Comparator's `--silent` option;
a separate help capture failed on an incompatible cached Lean-4.34.1
`Leanc.olean`.  The diagnostic NanoDa configuration set `num_threads` to 1.
Supervisor elapsed time exceeded their 120-second deadlines by 0.379 and 0.957
seconds respectively.  The earlier replacement compile omitted
`-DwarningAsError=true`, although it emitted no warning; the current real-module
compile supplies that missing strict check.

## Remaining obligations

The next authorized checkpoint must obtain a stock con-ron acceptance for the
actual integrated export before publishing and pinning the Foundation repair.
Only then may the project rebuild and the one cumulative Three Comparator run
be considered.  The third result remains externally unverified, six eligible
declarations remain to migrate, and complete official Palomar verification
remains outstanding.
