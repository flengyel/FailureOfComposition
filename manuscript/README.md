# Manuscript

This directory contains Florian Lengyel's *Pointwise provable equality and
the failure of composition*.

[Version 38](failure_of_composition_2026-11-14_v38.tex), dated November 14, 2026,
is the current repository manuscript; its [PDF](failure_of_composition_2026-11-14_v38.pdf)
has 11 pages. It removes the repeated comparison in Section 1.1 and adds the
domain-invariance deduction in Section 6.1. All numbered statements, existing
proofs, labels, and bibliography are preserved from
[version 37](failure_of_composition_2026-09-30_v37.tex).

The current arXiv release remains [2609.25556v2](https://arxiv.org/abs/2609.25556v2).
Palomar version 1 retains the immutable source
`fb32a19c4883baad83b286d4594cfbc6b1d2ad5c`. This repository revision does not
submit an arXiv replacement or a Palomar update. The Lean sources, selected
statements, Comparator configuration, and dependency pins are unchanged.

The [coverage map](../Lean/FailureOfComposition/MANUSCRIPT_COVERAGE.md) and
[statement correspondence](../Lean/FailureOfComposition/MANUSCRIPT_STATEMENTS.md)
identify the current manuscript. The
[revision report](../docs/MANUSCRIPT_V38_REPORT.txt) and
[focused review](../docs/reviews/MANUSCRIPT_V38_FOCUSED_REVIEW_2026-11-14.txt)
record the edits and checks.

## Current artifact hashes

- v38 source SHA-256: `94e80f24abd3a9c17fffa9075a017fdb1f04ea48995ad35b263386a4ddf6613b`
- v38 PDF SHA-256: `e57a045547808fff9f3f4e9ff8c5a239e1b1935dc61bd3b1971fa332719a99ce`

## Preserved v37 provenance

The v37 source and PDF remain at their existing paths. Their prior provenance
and build instructions are retained in the
[preceding manuscript notes](https://github.com/flengyel/FailureOfComposition/blob/506d1f1494d6c05b0ba304edf5fe0bfa6c32864b/manuscript/README.md).
V37 preserves the mathematical statements, proofs, and numbering from
[v36](https://github.com/flengyel/FailureOfComposition/blob/6adc1084e57ca3e9011dbd3765e99b803842ee17/manuscript/failure_of_composition_2026-09-21_v36.tex).
The recorded complete official local verification remains attached to its
own source commit `6adc1084e57ca3e9011dbd3765e99b803842ee17`; no new Lean build
or kernel replay is claimed for the manuscript edits.

## Licensing

The manuscript was submitted under arXiv's
[perpetual, non-exclusive distribution license](https://arxiv.org/licenses/nonexclusive-distrib/1.0/license.html).
The author retains copyright. The repository's Apache-2.0 license applies to
the Lean formalization and supporting code; it does not make a new grant for
the manuscript or its cited works.

## Build

The source includes its bibliography and has no external input or figure files.
From this directory:

```sh
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build failure_of_composition_2026-11-14_v38.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build failure_of_composition_2026-11-14_v38.tex
```

Both passes completed with exit code 0. References and citations are resolved;
there are no overfull boxes. One underfull box in the disclosure footnote also
occurs when rebuilding v37 with the same TeX installation.
