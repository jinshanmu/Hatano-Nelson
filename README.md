# Connected Pseudospectra of the Open Hatano–Nelson Chain

This repository accompanies the manuscript *Connected Pseudospectra of a
Nonnormal Toeplitz Path: The Open Hatano–Nelson Chain*. It contains the current
SIAM submission source, its reproducible figures, and a Lean 4 formalization of
the complete labelled mathematical argument.

## Current artifacts

- [`final_connected_pseudospectrum_proof_2026-07-16.tex`](SIMAX_submission_bundle/final_connected_pseudospectrum_proof_2026-07-16.tex)
  and its compiled PDF are the current audited manuscript.
- The corresponding 2026-07-13 TeX source and PDF are preserved unchanged as a
  historical snapshot.
- [`lean/`](lean/) contains the pinned formalization and the current
  statement-by-statement audit documentation.
- [`make_hatano_nelson_figures.py`](SIMAX_submission_bundle/make_hatano_nelson_figures.py)
  regenerates the manuscript figures.

The Lean audit covers all 90 labelled mathematical items literally, including
the complete connectedness-threshold proof and the lower real Lambert-\(W\)
branch used in the exact threshold formula. Physics-facing formulas are
deliberately unnumbered and remain outside the Lean kernel; they are checked as
physical exposition and are not used as unformalized premises of the main
mathematical theorem. See [`lean/README.md`](lean/README.md),
[`lean/FORMALIZATION_MAP.md`](lean/FORMALIZATION_MAP.md), and
[`lean/STATUS.md`](lean/STATUS.md) for the exact scope and latest evidence.

## Reproduce the artifacts

The figure script uses Python 3.9 or later with NumPy 1.23 or later, SciPy 1.9
or later, and Matplotlib 3.6 or later. The configured Conda environment can be
used from the repository root:

```sh
conda run -n wirtinger_calculus python SIMAX_submission_bundle/make_hatano_nelson_figures.py
```

Compile the current manuscript from its self-contained submission directory:

```sh
cd SIMAX_submission_bundle
latexmk -pdf -interaction=nonstopmode final_connected_pseudospectrum_proof_2026-07-16.tex
```

The formalization is pinned to Lean 4.28.0 and Mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. Its acceptance commands use all
default Lean options:

```sh
cd lean
lake build
lake env lean AxiomAudit.lean
```

## Repository layout

- `SIMAX_submission_bundle/`: manuscript, bibliography, figures, generator,
  and a complete SIAM standard macro distribution needed to compile it.
- `SIAM_template/siamart_251216/`: a second complete, unmodified reference copy
  of the SIAM standard macro distribution dated 2025-12-16.
- `lean/`: canonical Lean sources, pinned build configuration, formalization
  map, manuscript audit, axiom audit, and current validation status.
- The local working copy may contain an ignored `legacy/` directory of earlier
  research notes. It is not part of the GitHub repository and is not a current
  manuscript or formalization source.

## SIAM files and licensing

The SIAM class is third-party material and is **not** covered by this
repository's MIT grant. Its embedded redistribution notice requires the class
to be distributed with the complete macro set. Both retained copies now
include that set, including `docsiamart.tex` and `docsiamart.pdf`. The source,
inventory, verification record, and controlling terms are documented in
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md). The current upstream file
list is published on the [SIAM Journal Authors page](https://epubs.siam.org/journal-authors#siam-macros).

The root [`LICENSE`](LICENSE) states the separate treatment of original source
code, manuscript material, and third-party files. Citation metadata are in
[`CITATION.cff`](CITATION.cff).

## Citation

Until an article DOI is available, please use the metadata in
[`CITATION.cff`](CITATION.cff), which cites this repository and identifies the
preferred article title and author without inventing publication metadata.
