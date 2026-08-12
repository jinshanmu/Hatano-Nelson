# ELA submission checklist

Checked against ELA's public instructions on 2026-08-12.  Recheck the live
OJS form immediately before uploading because portal fields may change
without appearing in the public author guidelines.

## Scientific and editorial readiness

- [x] The final title and abstract present
  `tridiag(alpha,d,beta)` as the main object, not merely as a late corollary.
- [x] The cases `alpha*beta = 0`, `|alpha| = |beta|`, and
  `alpha*beta != 0`, `|alpha| != |beta|` are all stated without overlap or
  omission.
- [x] Every result asserted in `COVER_LETTER_ELA.md` appears in the final
  manuscript with exactly the same scope and hypotheses.
- [x] Neither the title nor the abstract suggests strict threshold decrease
  when `alpha*beta = 0`; the threshold is identically zero in that regime.
- [x] The abstract is written in the third person and contains no more than
  250 words.
- [x] There are 4--6 keywords and both primary and secondary AMS 2020
  classifications.
- [x] The manuscript explains why nonunitary similarity, ordinary
  interlacing, and asymptotic Toeplitz theory do not imply the strict
  finite-order result.
- [x] Physics is retained only if it sharpens the mathematical significance;
  it is confined to a short discussion paragraph and is not needed for any
  theorem or proof.

## ELA style and source integrity

- [x] The source uses ELA's `siamart1116` class and follows
  `official-template/ELA-sample.tex` for title and author information.
- [x] `\input{siamart1116-compat}` appears immediately before
  `\documentclass` when compiling on the current local TeX Live; the official
  class file itself remains unmodified.
- [x] Receipt date, acceptance date, page range, and handling-editor fields
  have not been invented; these are completed by ELA after acceptance.
- [x] Theorems, lemmas, propositions, corollaries, definitions, remarks, and
  examples are numbered consecutively within each section.
- [x] Only equations cited in the text are numbered.  The website requests
  right-side numbers but the distributed official class enforces left-side
  numbers; the manuscript follows the unmodified class, and this discrepancy
  has been noted rather than silently changing the journal template.
- [x] Every color figure remains readable in grayscale; labels and symbols
  agree with the manuscript.
- [x] `pdflatex`/`latexmk` completes without errors, undefined references,
  missing citations, or missing files.
- [x] The final PDF has been visually inspected page by page for clipped
  equations, overfull lines, misplaced floats, and illegible labels.

## References and reproducibility

- [x] Every bibliography entry is cited, and every citation supports the
  statement attached to it.
- [x] Journal titles are consistently abbreviated according to
  *Mathematical Reviews* (or consistently written in full).
- [x] The bibliography uses the supplied `siamplain.bst` (rather than generic
  `plain`) so verified DOI fields are printed in the PDF.
- [x] Authors, title, journal or publisher, volume, year, pages/article
  number, and DOI have been checked against the corresponding local PDF and
  an authoritative bibliographic record.
- [x] A DOI is included whenever one exists; DOI links resolve.
- [ ] The repository URL in `DECLARATIONS.tex` is public and contains the
  figure script and the Lean files cited in the manuscript.
- [x] The submitted Lean revision and theorem crosswalk correspond to the
  final mathematical statements, including boundary cases.

## Declarations and authorship

- [ ] No part of the manuscript is under consideration elsewhere.  The prior
  LAA submission is closed.
- [ ] The work has not been previously published, except for any permitted
  abstract or dissertation material disclosed to the editor.
- [ ] Every listed author is human, consents to submission, and accepts
  responsibility for the work.
- [ ] Funding, conflict-of-interest, and data/code-availability statements
  in `DECLARATIONS.tex` remain factually accurate.
- [x] The AI acknowledgment says “OpenAI ChatGPT Work” and “checking
  algebraic consistency and presentation”; no other AI tool is named.
- [ ] The author has independently verified all AI-assisted suggestions,
  citations, formulas, and proofs.
- [ ] The corresponding author is prepared to grant ELA the nonexclusive
  publication license while retaining copyright, as stated in ELA's
  submission checklist.

## OJS upload

- [ ] Register or log in at the ELA site and complete its five-step
  submission process.
- [ ] Enter title, abstract, keywords, AMS classifications (where requested),
  author name, affiliation, email, country, and ORCID consistently with the
  PDF.
- [ ] Upload the manuscript PDF and every source dependency requested by the
  live form: main `.tex`, `.bib`, generated `.bbl` if used,
  `siamart1116.cls`, `siamplain.bst`, `siamart1116-compat.tex`,
  `DECLARATIONS.tex`, and figure files.
- [ ] Paste or upload `COVER_LETTER_ELA.md` only if the live form offers a
  cover-letter/comments field; recheck the letter against the final paper
  first.
- [ ] Do not prepare highlights or a graphical abstract unless the live OJS
  form newly requests them; neither appears in the current public ELA
  instructions.
- [ ] Preview the generated submission PDF and confirm the file order before
  clicking the final submission button.
