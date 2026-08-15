# Final LMA package audit

Audit completed on 2026-08-13.

## Editorial changes

- The title and abstract now foreground the exact threshold and strict
  all-order monotonicity.
- The abstract states the three contributions in the requested order.
- The numbered three-part contribution statement begins on page 1 and is
  completed at the top of page 2.
- The requested phrase `finite-dimensional topological problem` is absent.
- The literature discussion is divided into Toeplitz theory,
  coalescence/defectivity, and non-self-adjoint instability/localization.
- Repeated result summaries and defensive gap statements in the introduction
  and discussion were consolidated into positive, source-specific positioning.
- The AI-tool acknowledgment names `OpenAI ChatGPT Work 5.6 Sol`; the
  ambiguous word `suggestions` was replaced by a precise statement that the
  author reviewed revisions and independently verified cited references.
- Seven references were added, increasing the bibliography from 15 to 22.

## Mathematical and formalization checks

- The full theorem/proof chain and all six appendices were reread.  No
  mathematical correction was required.
- Symbols are introduced before substantive use.  The final pass explicitly
  defined `nu_+` and the ordered singular values `s_j(P_m)`, expanded the
  Euclidean condition-number notation, and moved the definition of `P_m(x)`
  before its first display.
- The local signature matrix was renamed from `Gamma` to `S` to avoid
  conflict with the abstract barrier `Gamma(B)`; the lone `spec` notation was
  unified with `sigma`.
- The theorem-bearing body and appendices remain the same proof development
  mapped in `../lean/FORMALIZATION_MAP.md`; the changes above are notation and
  exposition only.
- `lake build` completed successfully for all 114 imported project modules
  (8141 build jobs).  `AxiomAudit.lean` contains 246 kernel-axiom queries,
  including the abstract topology, strict barrier comparison, canonical main
  theorem, and full complex-family main theorem.  A static trust scan found
  no `sorry`, `admit`, `native_decide`, project `axiom`, `opaque`, or `unsafe`
  declarations.

## Mechanical checks

- Final PDF: 35 A4 pages.
- LaTeX/BibTeX build: successful with TeX Live 2025.
- Final log: no warnings, undefined references, undefined citations,
  overfull boxes, or underfull boxes.
- Bibliography: 22 database entries, 22 generated items, 22 printed DOI links,
  22 distinct citation keys used in the manuscript, and no uncited database
  entries.
- Local reference coverage: 22/22 bibliography entries are represented by 21
  distinct full-text PDFs; the 2025 Ammari et al. article and its 2026
  corrigendum are stored in one combined file.
- PDF metadata: title, author, subject, and keywords synchronized.
- Branding scan: no ELA class, style, filename, or journal-name residue in the
  manuscript or the seven-file upload archive.

## Claim-to-source checks

- Every cited manuscript statement was compared with a specific passage,
  theorem, equation, or figure in the corresponding original full text.  The
  exact local-PDF pages and source boundaries are recorded in
  `REFERENCE_CLAIM_AUDIT.md`.
- Three broad group-citation sentences were split into source-specific claims.
  In particular, the 1994 Boettcher result is confined to truncated
  Wiener--Hopf operators; the order-driven cloud-merger statement is assigned
  only to Kiorpelidis--Makris; and Ammari et al.'s localization statement is
  limited to the nontrivial eigenvectors covered by their theorem.
- The corrected 2026 finite-matrix pseudospectral limit is distinguished from
  the superseded 2025 theorem.  No manuscript claim relies on the erroneous
  original Theorem 3.3 or the affected versions of Theorems 3.5 and 3.7.
- The two cited facts used in the mathematical development are tied to exact
  theorem/definition locators and, for the component lemma, also proved in the
  manuscript.  The remaining citations are used only for positioning or
  interpretation.
- The final pass directly re-extracted the listed evidence pages from 20
  text-bearing local PDFs.  The scanned Schmidt--Spitzer article was checked
  visually on local PDF pages 1, 5, and 6: its finite Toeplitz spectra,
  limit set, and Theorem 1 match the manuscript's characterization claim.

## Archive test

`LMA_submission_source.zip` contains exactly the manuscript `.tex`,
`.bib`, generated `.bbl`, `plainurl.bst`, declarations, and the two vector-PDF
figures.  The archive passed `unzip -t` and compiled successfully in a fresh
temporary directory without repository-local dependencies.  The resulting
PDF again had 35 pages and a warning-free final log.

## Visual QA

The current 35-page PDF was rasterized and reviewed as four contact sheets
after the final notation pass.  Pages 1, 9, 10, 34, and 35 were also
inspected at full resolution.  No clipping, overlap, blank page, broken
glyph, malformed author name, or unreadable figure was found.

## Checksums

```text
34ffd790049a1f1b236d168dcdaa0998e64aec4178960763e990e64d2d66d133  lma_pseudospectral_connectedness.pdf
ecd66cec1ccb28f1f599f68818895d9928becc92f40c9c4b774b05c48512fd42  LMA_submission_source.zip
```

## Remaining author-only confirmations

1. Confirm that the GitHub repository is public and synchronized at the moment
   of submission.
2. Follow any stricter file or `interact`-template requirement displayed by
   the live LMA submission portal.
