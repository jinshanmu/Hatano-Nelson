# ELA submission workspace

This directory contains the manuscript and submission material for the
*Electronic Journal of Linear Algebra* (ELA).  The requirements below were
checked against the journal website on 2026-08-12.

## Files

- `ela_pseudospectral_topology.tex` and `.bib`: manuscript source and
  bibliography.
- `siamart1116.cls`: convenience copy of ELA's official class, placed beside
  the manuscript so that `pdflatex` finds it without a system installation.
- `siamplain.bst`: official SIAM bibliography style from the same archive; it
  prints DOI and URL fields and is preferable here to generic `plain` because
  this project requires verified DOIs to appear in the references.
- `siamart1116-compat.tex`: a small pre-class compatibility shim for the
  official 2016 class on LaTeX kernels dated 2024-11 or later.
- `official-template/`: an untouched copy of the official ELA sample, class,
  and SIAM macro archive; provenance and checksums are recorded in
  `official-template/SOURCE.md`.
- `COVER_LETTER_ELA.md` (local, ignored by Git): cover-letter draft.  Recheck
  its theorem summary against the final manuscript before submission.
- `DECLARATIONS.tex`: project-specific funding, conflict-of-interest,
  data/code-availability, and AI-use wording for inclusion near the end of
  the manuscript.
- `SUBMISSION_CHECKLIST.md`: final pre-submission and OJS-entry checklist.
- `SUBMISSION_METADATA.md`: author, title, keyword, AMS, and declaration
  worksheet for consistent entry in OJS.
- `REFERENCE_AUDIT.md`: bibliography-key to local-PDF map and claim-support
  audit for every retained citation.
- `FINAL_SUBMISSION_AUDIT.md`: closing validation record and the remaining
  author-only actions.
- `make_ela_figures.py`, `requirements-figures.txt`, and the figure files:
  reproducibility material for the illustrations.  The requirements file
  pins the direct dependencies of the audited figure-generation environment.
- `ELA_submission_source.zip` (local, ignored by Git): the validated nine-file
  OJS source archive; upload the manuscript PDF separately.

## Current official requirements

ELA requires manuscripts to use the LaTeX2e Standard Macros package for SIAM
journals.  Its own downloadable sample uses `siamart1116`; submissions are
compiled with `pdflatex`, and authors are responsible for successful
compilation.  The principal formatting requirements are:

- fluent English;
- an informative, third-person abstract of at most 250 words;
- 4--6 pertinent keywords;
- primary and secondary AMS classifications;
- theorem-like statements numbered consecutively within each section;
- displayed formulas: the website asks for right-side numbering, whereas the
  distributed official class loads `amsmath` with `leqno` and therefore puts
  numbers on the left; this manuscript keeps the official class unmodified;
- figures that remain intelligible in black and white even when color is used;
- title, authors, affiliations, addresses, and funding formatted as in the
  ELA sample.

The ELA sample adds two useful bibliography rules: every listed item
must be cited, and journal names must be consistently either written in full
or abbreviated according to *Mathematical Reviews*.  It also recommends
numbering only formulas that are referenced in the text.  The sample does not
state that DOI fields are compulsory.  The nested official SIAM archive,
however, supplies `siamplain.bst`, which supports DOI fields.  This project
uses that style and retains a verified DOI whenever one exists.

ELA states that articles have **no length restriction** and that publication
is free to authors and readers.  The public submission instructions do not
request highlights or a graphical abstract.  They also do not list a cover
letter, a separate data statement, or separate declaration files as mandatory
uploads.  The included cover letter is therefore a concise optional aid, and
the declarations are kept in the manuscript, consistent with recent ELA
articles.  The live OJS upload screen takes precedence if it requests an
additional item.

ELA's AI policy, last updated 2026-06-06, permits LLM use during manuscript
preparation, recommends disclosure in the acknowledgments, requires the
human authors to verify all input, and places responsibility for accuracy,
originality, citations, and copyright on the authors.  `DECLARATIONS.tex`
uses the author's requested description: OpenAI ChatGPT Work was used for
"checking algebraic consistency and presentation."  No other AI tool is
named.

## Build

The official `siamart1116` sample fails on the local TeX Live 2025 kernel at
the first theorem-like environment because that old class overwrites kernel
cross-reference commands subsequently used by `hyperref` and `cleveref`.
The official class itself is kept byte-for-byte unchanged.  For a source that
also compiles on a current LaTeX installation, put

```tex
\input{siamart1116-compat}
\documentclass[10pt,twoside]{siamart1116}
```

at the top of the manuscript, in that order.  The shim is conditional and
does nothing on older kernels that lack the hook mechanism.  The final source
compiled without warnings with `pdflatex` on 2026-08-12.  A separate BibTeX
check with `siamplain.bst` printed every cited DOI as a resolvable URL.

From this directory, run

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  ela_pseudospectral_topology.tex
```

## Rebuild the figures

The committed figures were reproduced and audited with CPython 3.11.14,
NumPy 2.3.5, SciPy 1.16.3, and Matplotlib 3.10.7.  The script is
deterministic and uses no random samples.  To recreate that environment with
`uv`, run from this directory:

```sh
uv run --no-project --python 3.11.14 \
  --with-requirements requirements-figures.txt \
  python make_ela_figures.py
```

The final command overwrites both `fig1_connectedness_transition` and
`fig2_gap_barrier_bounds` in PDF and PNG format.  It reports the numerical
barrier estimates and the independent 1-Lipschitz grid brackets used to
check the topology labels.  Those brackets are conditional on the float64
singular-value samples; they are not interval-arithmetic certificates and
are not used in the proofs.

The upload archive should contain the main `.tex`, bibliography source and
generated `.bbl` if used, `siamart1116.cls`, `siamplain.bst`,
`siamart1116-compat.tex`, `DECLARATIONS.tex`, and every figure or other file
actually read by the source.  Do not upload the large official template
archive unless the OJS form explicitly asks for it.

## Official sources

- [ELA submissions and author guidelines](https://journals.uwyo.edu/index.php/ela/about/submissions)
- [ELA aims, scope, length, and fee information](https://journals.uwyo.edu/index.php/ela/about)
- [ELA policy on AI-assisted tools](https://journals.uwyo.edu/index.php/ela/announcement/view/45)
- [ELA editorial team](https://journals.uwyo.edu/index.php/ela/about/editorialTeam)
- [Official ELA template folder](https://www.dropbox.com/scl/fo/qnl3vvhld72rmf4obzc83/AGKpoUNtQhvUE1owl3VFcKA?rlkey=nv17qs8qzd7k8s2c35jojzefo&dl=0)
