# Connectedness Thresholds for Complex Tridiagonal Toeplitz Pseudospectra

**Author:** Shanmu Jin

**Public repository:** https://github.com/jinshanmu/Hatano-Nelson

This repository accompanies the manuscript *Connectedness thresholds for
complex tridiagonal Toeplitz pseudospectra: monotonicity with matrix order*,
prepared for submission to the *Electronic Journal of Linear Algebra*.  It
contains the current manuscript, reproducibility code for the numerical
illustrations, and the corresponding Lean 4 formalization and audit materials.

## Current artifacts

- [`ELA/`](ELA/) contains the current manuscript source and PDF,
  bibliography, figures, figure generator, official-template provenance, and
  submission notes.
- [`lean/`](lean/) contains the pinned formalization, the result-by-result
  manuscript map, and executable build and axiom-audit records.
- [`LAA/`](LAA/) preserves the earlier LAA-formatted version as a historical
  snapshot.
- [`JPA/JPA_submission_bundle/`](JPA/JPA_submission_bundle/) preserves the
  earlier J. Phys. A-formatted version as a historical snapshot.
- [`SIMAX_submission_bundle/`](SIMAX_submission_bundle/) preserves the earlier
  SIAM-formatted version.

The Lean development covers every theorem-bearing statement and independently
used proof-stage identity listed for the ELA manuscript, including the
pointwise backward-error identity, the abstract vertical-scaling topology,
and the complex Toeplitz reductions.  See
[`lean/FORMALIZATION_MAP.md`](lean/FORMALIZATION_MAP.md) for the exact
correspondence and [`lean/STATUS.md`](lean/STATUS.md) for the latest build,
linter, and kernel-axiom evidence.

## Reproduce the artifacts

The audited figure environment is pinned in
`ELA/requirements-figures.txt`.  From the repository root, regenerate both
figures with:

```sh
cd ELA
uv run --no-project --python 3.11.14 \
  --with-requirements requirements-figures.txt \
  python make_ela_figures.py
```

The manuscript uses ELA's official `siamart1116` class.  The unmodified class,
its complete upstream macro archive, provenance record, bibliography style,
and a compatibility shim for current LaTeX kernels are retained in `ELA/`.
Build with:

```sh
cd ELA
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  ela_pseudospectral_topology.tex
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

- `ELA/`: current ELA manuscript, bibliography, figures, reproducibility code,
  official template provenance, and submission material.
- `lean/`: canonical Lean sources, pinned build configuration, formalization
  map, manuscript audit, axiom audit, and current validation status.
- `LAA/`: historical LAA manuscript and submission material.
- `JPA/JPA_submission_bundle/`: historical J. Phys. A-formatted manuscript.
- `SIMAX_submission_bundle/`: historical SIAM-formatted manuscript and
  companion artifacts.
- The local working copy may contain ignored journal templates, submission
  correspondence, local reference PDFs, and legacy research notes.  They are
  not part of the public reproducibility record.

## Third-party files and licensing

The ELA/SIAM class and bibliography style remain third-party material and are
not covered by the repository's MIT grant.  Their redistribution terms,
inventory, and provenance are recorded in
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).

The root [`LICENSE`](LICENSE) states the separate treatment of original source
code, manuscript material, and third-party files.  Citation metadata are in
[`CITATION.cff`](CITATION.cff).

## Citation

Until an article DOI is available, use the metadata in
[`CITATION.cff`](CITATION.cff), which identifies the preferred article title
and author without inventing publication metadata.
