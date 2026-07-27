# J. Phys. A submission bundle

This directory contains the revised submission materials for
*Journal of Physics A: Mathematical and Theoretical*.  The original files in
`SIMAX_submission_bundle` were not modified.

## Files for the manuscript submission

- `exact_connectedness_threshold_hatano_nelson_anonymous.pdf` —
  double-anonymous reviewer manuscript; use this PDF for the selected review
  route.
- `exact_connectedness_threshold_hatano_nelson_anonymous.tex` — small wrapper
  that activates anonymous mode without duplicating the article body.
- `exact_connectedness_threshold_hatano_nelson.pdf` — author-identified
  manuscript for editorial records and later production.
- `exact_connectedness_threshold_hatano_nelson.tex` — shared manuscript body;
  its raw text contains no author name, email, ORCID, affiliation, repository
  URL, or other identifying declaration.  It contains the generic AI-use
  acknowledgment so that disclosure remains visible in both PDFs.
- `jpa_identified_metadata.tex` — author information and identified
  declarations used only by the non-anonymous build.
- `exact_connectedness_threshold_hatano_nelson.bbl` — generated numerical
  bibliography retained for robust source ingest.
- `exact_connectedness_threshold_hatano_nelson_anonymous.bbl` — generated
  numerical bibliography for the anonymous wrapper.
- `hatano_nelson_jpa.bib` — bibliography database.
- `fig1_connectedness_transition.pdf`
- `fig2_gap_barrier_bounds.pdf`
- `fig3_hatano_nelson_physics.pdf`

The three PNG figure copies are retained for convenient visual inspection.
`make_hatano_nelson_figures.py` regenerates both the PDF and PNG versions of
all figures.

## Compilation

The current official IOP class is intentionally not duplicated in this
bundle.  A local copy of the downloaded template is in the sibling directory
`../ioplatextemplate`.  From this directory, compile the selected
double-anonymous reviewer version with

```sh
TEXINPUTS=../ioplatextemplate: latexmk -pdf -interaction=nonstopmode \
  -halt-on-error exact_connectedness_threshold_hatano_nelson_anonymous.tex
```

Compile the author-identified version with

```sh
TEXINPUTS=../ioplatextemplate: latexmk -pdf -interaction=nonstopmode \
  -halt-on-error exact_connectedness_threshold_hatano_nelson.tex
```

The manuscript uses the official `iopjournal` class dated 2024-01-31 and
standard TeX Live packages.  Its article title, body text, abstract,
captions, declarations, and bibliography are fully justified; journal-header
and author/address metadata and section headings retain the class defaults.
The compiled manuscript has 41 pages: the main text occupies pages 1--27,
and the six self-contained technical appendices occupy pages 28--39, with
the acknowledgments beginning on the latter page.
The anonymous reviewer PDF also has 41 pages.  The class removes the author
front matter, the shared AI-use acknowledgment remains visible, and the
source replaces identifying declarations with an anonymity notice.  Its PDF
Author metadata is empty, and visible-text searches find no author name,
email, ORCID, affiliation, or repository URL.
At initial submission, IOP's current guidance requests a single, legible
manuscript PDF; source files can be supplied together in one directory when
requested.

The author-identified manuscript locally replaces the generic “Journal Name”
and “Author et al” placeholders with the target journal name and “Shanmu
Jin.”  The anonymous wrapper instead uses “Anonymous manuscript” and the
official anonymous-author notice.  The journal-owned class remains
untouched.  A manuscript-local patch removes the generic Crossmark and
received/revised date placeholders from both submission PDFs.

For a double-anonymous source upload, include the anonymous wrapper, shared
main source, anonymous `.bbl`, bibliography, and three PDF figures.  Exclude
`jpa_identified_metadata.tex`, the author-identified PDF and `.bbl`, and the
handoff documents.  The anonymous build has been tested in a separate
directory containing only that deidentified source set and the external
journal class.

## Figure regeneration

The figure script requires Python with NumPy, SciPy, and Matplotlib:

```sh
python3 make_hatano_nelson_figures.py
```

Its numerical topology labels use ordinary float64 singular-value
calculations supplemented by a Lipschitz grid check.  They are reproducible
illustrations, not interval-certified computations and not inputs to any
proof.

## Editorial handoff files

- `CHANGE_LOG_JPA.md` — detailed revision record.
- `SUBMISSION_AUDIT.md` — build, mathematical-preservation, and layout audit.
- `UNRESOLVED_AUTHOR_ISSUES.md` — record of the author’s now-resolved review
  and repository choices, plus the practical anonymity note.
- `COVER_LETTER_JPA.md` — local-only draft cover letter, intentionally
  excluded from the public repository as submission correspondence.

These four Markdown files are handoff documents and are not intended for
upload as manuscript source files.

## Official guidance checked

The conversion was checked on 27 July 2026 against the current official
[J. Phys. A scope and article-type page](https://publishingsupport.iopscience.iop.org/journals/journal-of-physics-a-mathematical-and-theoretical/about-journal-physics-mathematical-theoretical/),
[IOP manuscript guidance](https://publishingsupport.iopscience.iop.org/publishing-support/authors/authoring-for-journals/writing-journal-article/),
[IOP LaTeX-template page](https://publishingsupport.iopscience.iop.org/questions/latex-template/),
and [IOP generative-AI policy](https://publishingsupport.iopscience.iop.org/questions/generative-ai-tools/).
