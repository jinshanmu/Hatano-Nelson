# Pseudospectral Connectedness Thresholds for Tridiagonal Toeplitz Matrices

**Author:** Shanmu Jin

**Public repository:** https://github.com/jinshanmu/Hatano-Nelson

This repository accompanies the manuscript *Pseudospectral connectedness
thresholds and strict dimension monotonicity for asymmetric tridiagonal
Toeplitz matrices*, prepared for submission to *Linear Algebra and its
Applications*.  It contains the current manuscript, reproducibility code for
the numerical illustrations, and the corresponding Lean 4 formalization and
audit materials.

## Current artifacts

- [`LAA/`](LAA/) contains the current manuscript source and PDF,
  bibliography, figures, figure generator, and public reproduction notes.
- [`lean/`](lean/) contains the pinned formalization, the result-by-result
  manuscript map, and executable build and axiom-audit records.
- [`JPA/JPA_submission_bundle/`](JPA/JPA_submission_bundle/) preserves the
  earlier J. Phys. A-formatted version as a historical snapshot.
- [`SIMAX_submission_bundle/`](SIMAX_submission_bundle/) preserves the earlier
  SIAM-formatted version.

The Lean development covers every numbered theorem-like result in the LAA
manuscript and the independently used pointwise backward-error identity at the
result/proof-stage level.  See [`lean/FORMALIZATION_MAP.md`](lean/FORMALIZATION_MAP.md)
for the exact correspondence and [`lean/STATUS.md`](lean/STATUS.md) for the
latest build, linter, and kernel-axiom evidence.

## Reproduce the artifacts

The figure script uses Python 3.9 or later with NumPy 1.23 or later, SciPy 1.9
or later, and Matplotlib 3.6 or later.  From the repository root, the configured
Conda environment can regenerate both figures with:

```sh
conda run -n wirtinger_calculus python LAA/make_laa_figures.py
```

The manuscript uses Elsevier's `elsarticle` 3.4 class.  Third-party template
files are intentionally absent from the public repository.  After obtaining
the class and `elsarticle-harv.bst` from Elsevier, make them visible on
`TEXINPUTS` and `BSTINPUTS`, then run:

```sh
cd LAA
TEXINPUTS=/path/to/elsarticle: BSTINPUTS=/path/to/elsarticle: \
  latexmk -pdf -interaction=nonstopmode -halt-on-error \
  laa_connected_pseudospectra.tex
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

- `LAA/`: current LAA manuscript, bibliography, figures, and reproducibility
  code.
- `lean/`: canonical Lean sources, pinned build configuration, formalization
  map, manuscript audit, axiom audit, and current validation status.
- `JPA/JPA_submission_bundle/`: historical J. Phys. A-formatted manuscript.
- `SIMAX_submission_bundle/`: historical SIAM-formatted manuscript and
  companion artifacts.
- `SIAM_template/siamart_251216/`: retained unmodified reference copy of the
  SIAM standard macro distribution dated 2025-12-16.
- The local working copy may contain ignored journal templates, submission
  correspondence, local reference PDFs, and legacy research notes.  They are
  not part of the public reproducibility record.

## Third-party files and licensing

The current Elsevier class and bibliography style are not redistributed in
this repository.  The retained SIAM class remains third-party material and is
not covered by the repository's MIT grant.  Its redistribution terms,
inventory, and provenance are recorded in
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).

The root [`LICENSE`](LICENSE) states the separate treatment of original source
code, manuscript material, and third-party files.  Citation metadata are in
[`CITATION.cff`](CITATION.cff).

## Citation

Until an article DOI is available, use the metadata in
[`CITATION.cff`](CITATION.cff), which identifies the preferred article title
and author without inventing publication metadata.
