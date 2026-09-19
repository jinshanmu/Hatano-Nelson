# Connectedness thresholds for pseudospectra of tridiagonal Toeplitz matrices

**Author:** Shanmu Jin

**Public repository:** https://github.com/jinshanmu/Hatano-Nelson

This repository accompanies the preprint *Connectedness thresholds for
pseudospectra of tridiagonal Toeplitz matrices*. The manuscript studies
`A_n(a) = tridiag(a,0,1)` for `0 < a < 1` and the boundary cases `a = 0,1`.
It uses the Preprints.org template and includes all proofs in the main text.
The repository contains the manuscript, code for its numerical illustrations,
earlier journal versions, and the Lean 4 formalization and audit materials
associated with the ELA version.

## Current artifacts

- [`preprint/`](preprint/) contains the current preprint source and PDF,
  bibliography, figures, figure generator, source archive, and template
  provenance.
- [`LMA/`](LMA/) preserves the earlier LMA manuscript source and PDF,
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

The Lean development formalizes the canonical nonnormal theorem and the
complex-Toeplitz extension in the ELA manuscript, including the pointwise
backward-error identity and the abstract vertical-scaling topology. Its
statement-level map and completed audit remain anchored to that ELA snapshot.
See [`lean/FORMALIZATION_MAP.md`](lean/FORMALIZATION_MAP.md) for the exact
correspondence and [`lean/STATUS.md`](lean/STATUS.md) for the latest build,
linter, and kernel-axiom evidence.

## Reproduce the artifacts

The preprint figure environment is pinned in
`preprint/requirements-figures.txt`. From the repository root, regenerate both
figures with:

```sh
cd preprint
uv run --no-project --python 3.11.14 \
  --with-requirements requirements-figures.txt \
  python make_figures.py
```

The current manuscript uses the bundled, unmodified Preprints.org template
dependencies and a numerical bibliography with DOI links. Build with a full
TeX Live installation:

```sh
cd preprint
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  connectedness_thresholds.tex
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

- `preprint/`: current preprint, bibliography, figures, reproducibility code,
  source archive, and template provenance.
- `LMA/`: historical LMA manuscript, bibliography, figures, reproducibility code,
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

The Preprints.org template dependencies, LMA bibliography style, and historical
ELA/SIAM class and style remain third-party material and are not covered by
the repository's MIT grant. Their redistribution terms, inventory, and
provenance are recorded in
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).

The root [`LICENSE`](LICENSE) states the separate treatment of original source
code, manuscript material, and third-party files.  Citation metadata are in
[`CITATION.cff`](CITATION.cff).

## Citation

Until an article DOI is available, use the metadata in
[`CITATION.cff`](CITATION.cff), which identifies the preferred article title
and author without inventing publication metadata.
