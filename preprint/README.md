# Preprint manuscript

**Title:** Connectedness thresholds for pseudospectra of tridiagonal Toeplitz matrices

**Author:** Shanmu Jin

The manuscript treats `A_n(a) = tridiag(a,0,1)` for `0 < a < 1`, with a
short treatment of the boundary cases `a = 0,1`. All proofs are in the main
text. The bibliography contains nine journal articles, each with a DOI.

The manuscript source, numerical illustration code, and generated figures
are available in the [Hatano-Nelson GitHub repository](https://github.com/jinshanmu/Hatano-Nelson).
The manuscript's Data Availability Statement points to this repository.

## Files

- `connectedness_thresholds.tex`: complete manuscript source.
- `connectedness_thresholds.pdf`: compiled manuscript.
- `references.bib`: article-only bibliography.
- `connectedness_thresholds.bbl`: generated bibliography for portable builds.
- `Definitions/`: unmodified Preprints.org template dependencies.
- `fig1_connectedness_transition.pdf` and `fig2_gap_barrier_bounds.pdf`: figures.
- `figures_pdf.zip`: both figure PDFs in a single archive.
- `make_figures.py` and `requirements-figures.txt`: figure reproduction files.
- `preprint_source.zip`: source archive with everything needed to rebuild the PDF.
- `TEMPLATE_SOURCE.md`: template provenance and checksums.
- `MATHEMATICAL_AUDIT.md` and `reference_audit.md`: separate working audit notes,
  excluded from the submission source archive.

The original journal versions elsewhere in the repository are unchanged.

## Compile

Run from this directory with a full TeX Live installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error connectedness_thresholds.tex
```

The official template uses the `preprints` option. Its `accept` option
suppresses draft line numbers, as documented in the template, and does not
indicate journal acceptance. No article DOI or publication date is assigned.

## Reproduce the figures

```sh
uv run --no-project --python 3.11.14 \
  --with-requirements requirements-figures.txt python make_figures.py
```

The script computes least singular values directly and writes both vector
PDF and PNG figures. At `a = 1/4` and `epsilon = 0.01`, the numerical
connectedness transition is between orders 6 and 7. The explicit analytic
bounds in the paper give `6 <= N_c <= 9`.
