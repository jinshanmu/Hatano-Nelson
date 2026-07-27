# Exact Connectedness Threshold for Pseudospectra of the Open Hatano–Nelson Chain

**Author:** Shanmu Jin

**Public repository:** https://github.com/jinshanmu/Hatano-Nelson

This repository accompanies the manuscript *Exact Connectedness Threshold for
Pseudospectra of the Open Hatano–Nelson Chain*. It contains the current
Journal of Physics A submission bundle, reproducibility code for the numerical
illustrations, and the scoped Lean 4 formalization and audit materials described
below. The earlier SIAM-formatted manuscript remains available as a historical
snapshot.

## Current artifacts

- [`JPA/JPA_submission_bundle/`](JPA/JPA_submission_bundle/) contains the
  current audited J. Phys. A source, author-identified PDF,
  double-anonymous reviewer PDF, bibliography, figures, figure generator,
  change log, and submission audit.
- [`final_connected_pseudospectrum_proof_2026-07-16.tex`](SIMAX_submission_bundle/final_connected_pseudospectrum_proof_2026-07-16.tex)
  and its compiled PDF are preserved unchanged as the preceding
  SIAM-formatted snapshot. The corresponding 2026-07-13 source/PDF is also
  retained.
- [`lean/`](lean/) contains the pinned formalization and the current
  statement-by-statement audit documentation.
- [`make_hatano_nelson_figures.py`](JPA/JPA_submission_bundle/make_hatano_nelson_figures.py)
  regenerates the current manuscript figures.

The Lean materials are pinned to the earlier audited source and document their
coverage statement by statement. They formalize the mathematical items listed
in the map and audit files; the J. Phys. A physical exposition, the
floating-point illustrations, and the new editorial wrapper statements are
outside that claim. See [`lean/README.md`](lean/README.md),
[`lean/FORMALIZATION_MAP.md`](lean/FORMALIZATION_MAP.md), and
[`lean/STATUS.md`](lean/STATUS.md) for the exact scope and latest evidence.

## Reproduce the artifacts

The figure script uses Python 3.9 or later with NumPy 1.23 or later, SciPy 1.9
or later, and Matplotlib 3.6 or later. The configured Conda environment can be
used from the repository root:

```sh
conda run -n wirtinger_calculus python JPA/JPA_submission_bundle/make_hatano_nelson_figures.py
```

The journal-owned `iopjournal.cls` and ORCID graphic are intentionally absent
from the repository. Download the current IOP template, place it on
`TEXINPUTS`, and compile the double-anonymous reviewer manuscript from the
submission directory:

```sh
cd JPA/JPA_submission_bundle
TEXINPUTS=/path/to/iop-template: latexmk -pdf -interaction=nonstopmode \
  -halt-on-error exact_connectedness_threshold_hatano_nelson_anonymous.tex
```

The author-identifying front matter and declarations are isolated in
`jpa_identified_metadata.tex`. Exclude that file, the identified PDF, and the
identified `.bbl` from any reviewer source upload; the exact deidentified
source list is recorded in the bundle README.

The formalization is pinned to Lean 4.28.0 and Mathlib commit
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. Its acceptance commands use all
default Lean options:

```sh
cd lean
lake build
lake env lean AxiomAudit.lean
```

## Repository layout

- `JPA/JPA_submission_bundle/`: current J. Phys. A manuscript sources,
  author-identified and double-anonymous PDFs, bibliography, figures,
  generator, and audit documents. Journal-owned IOP template files are
  excluded.
- `SIMAX_submission_bundle/`: preserved earlier manuscript, bibliography,
  figures, generator, and SIAM macro distribution.
- `SIAM_template/siamart_251216/`: a second complete, unmodified reference copy
  of the SIAM standard macro distribution dated 2025-12-16.
- `lean/`: canonical Lean sources, pinned build configuration, formalization
  map, manuscript audit, axiom audit, and current validation status.
- The local working copy may contain an ignored `legacy/` directory of earlier
  research notes. It is not part of the GitHub repository and is not a current
  manuscript or formalization source.

## Third-party files and licensing

The retained SIAM class is third-party material and is **not** covered by this
repository's MIT grant. Its embedded redistribution notice requires the class
to be distributed with the complete macro set. Both retained copies now
include that set, including `docsiamart.tex` and `docsiamart.pdf`. The source,
inventory, verification record, and controlling terms are documented in
[`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md). The current upstream file
list is published on the [SIAM Journal Authors page](https://epubs.siam.org/journal-authors#siam-macros).
The IOP class and ORCID graphic used to build the J. Phys. A PDFs are
journal-owned and are deliberately not redistributed here.

The root [`LICENSE`](LICENSE) states the separate treatment of original source
code, manuscript material, and third-party files. Citation metadata are in
[`CITATION.cff`](CITATION.cff).

## Citation

Until an article DOI is available, please use the metadata in
[`CITATION.cff`](CITATION.cff), which cites this repository and identifies the
preferred article title and author without inventing publication metadata.
