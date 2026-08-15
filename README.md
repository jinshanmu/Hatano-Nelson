# Exact Connectedness Thresholds and Strict Order Monotonicity for Complex Tridiagonal Toeplitz Pseudospectra

**Author:** Shanmu Jin

**Public repository:** https://github.com/jinshanmu/Hatano-Nelson

This repository accompanies the manuscript *Exact connectedness thresholds
and strict order monotonicity for complex tridiagonal Toeplitz
pseudospectra*, prepared for submission to *Linear and Multilinear Algebra*.
It contains the current manuscript, reproducibility code for the numerical
illustrations, and the corresponding Lean 4 formalization and audit materials.

## Current artifacts

- [`LMA/`](LMA/) contains the current manuscript source and PDF,
  bibliography, figures, figure generator, literature audit, and submission
  notes.
- [`lean/`](lean/) contains the pinned formalization, the result-by-result
  manuscript map, and executable build and axiom-audit records.
- [`ELA/`](ELA/) preserves the earlier ELA-formatted version and its official
  template as a historical submission snapshot.
- [`LAA/`](LAA/) preserves the earlier LAA-formatted version as a historical
  snapshot.
- [`JPA/JPA_submission_bundle/`](JPA/JPA_submission_bundle/) preserves the
  earlier J. Phys. A-formatted version as a historical snapshot.
- [`SIMAX_submission_bundle/`](SIMAX_submission_bundle/) preserves the earlier
  SIAM-formatted version.

The Lean development covers every theorem-bearing statement and independently
used proof-stage identity in the mathematical body, including the pointwise
backward-error identity, the abstract vertical-scaling topology, and the
complex Toeplitz reductions.  Its detailed label map remains anchored to the
mathematically identical ELA snapshot so that the completed audit is
reproducible.  See
[`lean/FORMALIZATION_MAP.md`](lean/FORMALIZATION_MAP.md) for the exact
correspondence and [`lean/STATUS.md`](lean/STATUS.md) for the latest build,
linter, and kernel-axiom evidence.

## Reproduce the artifacts

The audited figure environment is pinned in
`LMA/requirements-figures.txt`.  From the repository root, regenerate both
figures with:

```sh
cd LMA
uv run --no-project --python 3.11.14 \
  --with-requirements requirements-figures.txt \
  python make_lma_figures.py
```

The current manuscript uses a portable `article`-class initial-submission
layout and a bundled numerical bibliography style with DOI support.  Build
with:

```sh
cd LMA
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  lma_pseudospectral_connectedness.tex
```

The formalization is pinned to Lean 4.28.0 and Mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`.  Its acceptance commands use
default Lean options:

```sh
cd lean
lake build
lake env lean AxiomAudit.lean
```

## Repository layout

- `LMA/`: current LMA manuscript, bibliography, figures, reproducibility code,
  literature audit, and submission material.
- `lean/`: canonical Lean sources, pinned build configuration, formalization
  map, manuscript audit, axiom audit, and current validation status.
- `ELA/`: historical ELA manuscript, official template provenance, and
  submission material.
- `LAA/`: historical LAA manuscript and submission material.
- `JPA/JPA_submission_bundle/`: historical J. Phys. A-formatted manuscript.
- `SIMAX_submission_bundle/`: historical SIAM-formatted manuscript and
  companion artifacts.
- The local working copy may contain ignored journal templates, submission
  correspondence, local reference PDFs, and legacy research notes.  They are
  not part of the public reproducibility record.

## Third-party files and licensing

The LMA bibliography style and the historical ELA/SIAM class and style remain
third-party material and are not covered by the repository's MIT grant.  Their
redistribution terms, inventory, and provenance are recorded in
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).

The root [`LICENSE`](LICENSE) states the separate treatment of original source
code, manuscript material, and third-party files.  Citation metadata are in
[`CITATION.cff`](CITATION.cff).

## Citation

Until an article DOI is available, use the metadata in
[`CITATION.cff`](CITATION.cff), which identifies the preferred article title
and author without inventing publication metadata.
