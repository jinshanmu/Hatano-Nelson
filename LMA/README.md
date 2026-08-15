# Linear and Multilinear Algebra submission workspace

This directory is an independent submission package for *Linear and
Multilinear Algebra* (LMA).  The earlier `ELA/` version is retained unchanged
as a historical submission snapshot.

The journal and publisher guidance cited below was checked on 2026-08-13.

## Main files

- `lma_pseudospectral_connectedness.tex`: LMA-targeted manuscript source.
- `lma_pseudospectral_connectedness.bib`: bibliography, expanded from 15 to
  22 entries and checked for citation completeness.
- `plainurl.bst`: portable numerical bibliography style with DOI support.
- `DECLARATIONS.tex`: funding, conflict-of-interest, availability, and
  AI-assisted-preparation statements included in the manuscript.
- `fig1_connectedness_transition.*` and `fig2_gap_barrier_bounds.*`: vector
  PDF and 300 dpi PNG versions of the two figures.
- `make_lma_figures.py` and `requirements-figures.txt`: deterministic figure
  reproduction material.
- `COVER_LETTER_LMA.md`: cover-letter draft.
- `SUBMISSION_METADATA.md`: copy-and-paste metadata worksheet.
- `LITERATURE_AUDIT.md`: rationale and metadata record for the seven added
  references.
- `REFERENCE_CLAIM_AUDIT.md`: claim-by-claim mapping from every manuscript
  citation to original-source pages, theorems, equations, or figures.
- `SUBMISSION_CHECKLIST.md`: final author actions and portal checks.
- `FINAL_SUBMISSION_AUDIT.md`: compilation, citation, archive, and visual-QA
  record.
- `lma_pseudospectral_connectedness.pdf`: final, visually checked manuscript
  PDF, stored beside the corresponding `.tex` source.
- `LMA_submission_source.zip`: self-contained seven-file LaTeX source archive
  tested in a fresh temporary directory.

## Editorial positioning implemented

The first two manuscript pages now present the same three claims in the same
order:

1. a general affine-spectral-line contraction theorem;
2. an exact connectedness criterion for the full complex tridiagonal
   Toeplitz family;
3. strict threshold monotonicity at every adjacent matrix order.

The introduction then distinguishes three neighboring literatures: classical
and recent Toeplitz spectral/pseudospectral theory, pseudospectral component
coalescence and distance to defectivity, and non-self-adjoint spectral
instability/localization.  It positions the contribution as an exact
finite-order criterion for the full complex family paired with an all-order
adjacent comparison.

## Layout choice

Taylor & Francis supplies an `interact`-class LaTeX template with numerical
reference style P.  This package currently uses a conservative
`article`-class layout with A4 paper, one-inch margins, Times-compatible
fonts, numbered citations, and DOI links.
It contains all elements requested by the Taylor & Francis submission portal:
author details, abstract, keywords, main text, references, and figures.

If the live LMA portal explicitly requires the `interact` source rather than
a manuscript PDF plus source files, migrate the preamble to the current
official template at that time; no mathematical-body conversion should be
needed.  The live portal always takes precedence over this worksheet.

LMA states that its research papers are initially appraised by an editor and,
if suitable, reviewed under a single-anonymized policy.  The current
manuscript therefore includes the author's identity; an anonymous duplicate
is not prepared unless the live portal requests one.

## Build

Run from this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  lma_pseudospectral_connectedness.tex
```

For a clean rebuild:

```sh
latexmk -C lma_pseudospectral_connectedness.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  lma_pseudospectral_connectedness.tex
```

## Rebuild the figures

The script is deterministic and uses no random samples.  From this directory:

```sh
uv run --no-project --python 3.11.14 \
  --with-requirements requirements-figures.txt \
  python make_lma_figures.py
```

## Official sources

- [LMA aims, scope, peer review, and submission link](https://www.tandfonline.com/journals/glma20/about-this-journal)
- [Taylor & Francis submission-portal file guidance](https://authorservices.taylorandfrancis.com/publishing-your-research/making-your-submission/using-taylor-francis-submission-portal/)
- [Taylor & Francis manuscript-preparation guidance](https://authorservices.taylorandfrancis.com/publishing-your-research/writing-your-paper/)
- [Taylor & Francis AI-use and authorship disclosure policy](https://authorservices.taylorandfrancis.com/editorial-policies/defining-authorship-research-paper/)
- [Taylor & Francis LaTeX `interact` template, P reference style](https://www.overleaf.com/latex/templates/taylor-and-francis-latex-template-for-authors-interact-layout-plus-p-reference-style/jcttgbjrwpvq)
