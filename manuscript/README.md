# Manuscript

This directory contains the LaTeX source of Florian Lengyel's
*Pointwise provable equality and the failure of composition*.

[Version 36](failure_of_composition_2026-09-21_v36.tex), dated September 21, 2026,
is the unchanged manuscript used by the
[Lean coverage map](../Lean/FailureOfComposition/MANUSCRIPT_COVERAGE.md).
The author plans a separate version 37 discussing the formalization and its
consequences for the earlier constructions. This move does not create or edit
that revision.

## Provenance

The v36 file was copied byte for byte from
[`flengyel/Categorical_Rice_Shapiro` at `6c3fe13979f31fed5c6da73098cbc323c2647f15`](https://github.com/flengyel/Categorical_Rice_Shapiro/blob/6c3fe13979f31fed5c6da73098cbc323c2647f15/research/notes/failure_of_composition_2026-09-21_v36.tex).
The manuscript is now maintained in this repository alongside its formalization.

- Git blob: `e0a2bd4b3570235fa4ea89ffe8dcf9d5445499f9`
- SHA-256: `65a7b8e1485452f5db9c2f3f1e0c172d6c40a8acc1c5d3a37e06fc80424bed2c`

The manuscript retains its existing licensing. The repository's Apache-2.0
code license covers the Lean formalization and supporting code; this source
move does not grant an additional license for the paper or its cited works.

## Build

The source includes its bibliography and has no external input or figure files.
It uses standard LaTeX packages. From this directory:

```sh
mkdir -p build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build failure_of_composition_2026-09-21_v36.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build failure_of_composition_2026-09-21_v36.tex
```

Repeat the last command if LaTeX requests another pass to settle cross-references.
Generated files stay in the ignored `build/` directory.
