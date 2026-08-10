# Historical LAA manuscript

This directory preserves the superseded LAA-formatted research artifacts for
*Pseudospectral connectedness thresholds and strict dimension monotonicity
for asymmetric tridiagonal Toeplitz matrices*.

## Tracked artifacts

- `laa_connected_pseudospectra.tex`: manuscript source.
- `laa_connected_pseudospectra.pdf`: validated 44-page A4 manuscript.
- `laa_connected_pseudospectra.bib`: bibliography with DOI metadata.
- `fig1_connectedness_transition.{pdf,png}` and
  `fig2_gap_barrier_bounds.{pdf,png}`: vector and preview figures.
- `make_laa_figures.py`: deterministic figure-generation script.

The local submission workspace also contains cover letters, highlights,
Elsevier template files, build intermediates, and a platform-upload ZIP.
Those journal-specific or temporary files are intentionally not part of the
public reproducibility record.

## Rebuild

Obtain Elsevier's `elsarticle` 3.4 class and `elsarticle-harv.bst`, make them
visible on the TeX search paths, and run from this directory:

```sh
TEXINPUTS=/path/to/elsarticle: BSTINPUTS=/path/to/elsarticle: \
  latexmk -pdf -interaction=nonstopmode -halt-on-error \
  laa_connected_pseudospectra.tex
```

Regenerate both figures from the repository root with:

```sh
conda run -n wirtinger_calculus python LAA/make_laa_figures.py
```

The result-by-result formalization map is
[`../lean/FORMALIZATION_MAP.md`](../lean/FORMALIZATION_MAP.md), and the latest
full validation record is [`../lean/STATUS.md`](../lean/STATUS.md).
