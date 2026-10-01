# Manuscript

This directory contains the LaTeX source of Florian Lengyel's
*Pointwise provable equality and the failure of composition*.

[Version 37](failure_of_composition_2026-09-30_v37.tex), dated September 30, 2026,
is the current manuscript; its [compiled PDF](failure_of_composition_2026-09-30_v37.pdf)
has 11 pages. It revises the exposition and related work while preserving the
mathematical statements, proofs, and numbering from
[version 36](failure_of_composition_2026-09-21_v36.tex).
The [Lean coverage map](../Lean/FailureOfComposition/MANUSCRIPT_COVERAGE.md)
and submission metadata now identify v37.
The [statement correspondence](../Lean/FailureOfComposition/MANUSCRIPT_STATEMENTS.md)
gives each numbered result in mathematical notation and its Lean signature,
including the hypotheses and the distinction between manuscript numbering
and selected-declaration order.
The submission target contains this manuscript and its corresponding Lean
development in one repository revision. Its 124 Lean sources, Comparator
configuration, and dependency pins match the complete official local run at
`6adc1084e57ca3e9011dbd3765e99b803842ee17`. That earlier SHA records the run;
the new revision supplies the v37 paper-and-Lean package. No new complete
verifier run or service submission is claimed by the manuscript update.

## Provenance

Version 37 was reviewed against the v36 source in the accepted Lean snapshot.
All 11 theorem, corollary, proposition, and proof environments are byte-identical.
The definitions and unlabelled arguments retain their mathematical content;
two short composition identities were moved inline. The source and PDF committed
here are the reviewed artifacts:

- v37 source SHA-256: `821a5a23632c8100c543430c973b8bd3546e1f9af298d1e52ec7953f3f15697c`
- v37 PDF SHA-256: `651415ef5605eb636e0790e93179c16f41b8719b41ad9c6c79aa85b238ddc168`

The v36 file was copied byte for byte from
[`flengyel/Categorical_Rice_Shapiro` at `6c3fe13979f31fed5c6da73098cbc323c2647f15`](https://github.com/flengyel/Categorical_Rice_Shapiro/blob/6c3fe13979f31fed5c6da73098cbc323c2647f15/research/notes/failure_of_composition_2026-09-21_v36.tex).
The manuscript is now maintained in this repository alongside its formalization.

- Git blob: `e0a2bd4b3570235fa4ea89ffe8dcf9d5445499f9`
- SHA-256: `65a7b8e1485452f5db9c2f3f1e0c172d6c40a8acc1c5d3a37e06fc80424bed2c`

The manuscript was submitted under arXiv's
[perpetual, non-exclusive distribution license](https://arxiv.org/licenses/nonexclusive-distrib/1.0/license.html).
The author retains copyright. That grant authorizes arXiv to distribute the
submission; it is not a general public reuse license. The repository's
Apache-2.0 license applies to the Lean formalization and supporting code, not to
the manuscript or its cited works. This notice records the existing license and
does not make a new grant or claim that an arXiv-deposited version is
byte-identical to repository v36.

## Build

The source includes its bibliography and has no external input or figure files.
It uses standard LaTeX packages. From this directory:

```sh
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build failure_of_composition_2026-09-30_v37.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build failure_of_composition_2026-09-30_v37.tex
```

Repeat the last command if LaTeX requests another pass to settle cross-references.
Intermediate build files stay in the ignored `build/` directory. The reviewed
v37 PDF is also committed alongside its source.

