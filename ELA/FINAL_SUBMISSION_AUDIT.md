# Final pre-submission audit

Audit date: 2026-08-12 (Asia/Shanghai)

## Verdict

The ELA manuscript and source package are technically ready for submission.
The remaining items are the author's declarations and the checks performed in
the live OJS portal immediately before submission.

## Mathematical and editorial review

- The complete complex tridiagonal Toeplitz family is treated in three
  disjoint regimes: zero product, unequal nonzero moduli, and equal nonzero
  moduli.  The piecewise threshold, strict inequalities, endpoint cases, and
  critical-order asymptotics use consistent hypotheses and notation.
- The proof chain was checked from vertical contraction through the real-axis
  connectedness criterion, signed-pencil branch selection, noncentral and
  central gap comparison, global strict decrease, two-sided bounds, and
  critical-order inversion.  No unresolved algebraic or logical conflict was
  found.
- All 95 numbered equations are referenced.  The source has 133 unique
  labels, with no duplicate or undefined label, and the prose uses the same
  meanings for (c,a,r,N,n,L,M,gamma_n,eta_n,Theta_n,N_c), and (N_T)
  throughout their stated scopes.
- The OJS metadata abstract, title, keywords, classifications, and PDF
  metadata match the manuscript.

## References and figures

- All 15 bibliography keys are cited, and no uncited entry remains.  Author,
  title, venue or publisher, year, volume, page or article number, and DOI
  were rechecked against the local papers and authoritative DOI metadata.
  Citation contexts were compared with the cited sources; no mismatch was
  found.
- Figure generation was rerun under CPython 3.11.14, NumPy 2.3.5, SciPy
  1.16.3, and Matplotlib 3.10.7.  It recovered
  (widehat N_c=7), the theorem's bracket (6leq N_cleq9), and the
  reported barrier values.  Both figures remain legible in grayscale.
- Figures 1 and 2 appear on pages 23 and 24.  Removing the post-figure float
  barrier lets the Discussion flow naturally and eliminates the previously
  underfull page without separating either figure from its numerical-methods
  description.

## Verification record

- Manuscript build: `latexmk` exit 0; 37 pages; no warnings, undefined
  references, missing citations, overfull boxes, or underfull boxes.  A
  narrow pre-class compatibility hook bridges the current LaTeX kernel's
  `\eqnarray` signature; the official `siamart1116.cls` and
  `siamplain.bst` remain byte-identical to the archived ELA copies.
- PDF audit: all 37 pages were rendered and inspected; no clipping, overlap,
  blank page, misplaced float, or illegible label was found.  All fonts are
  embedded and the References bookmark targets page 37.
- Lean validation: the complete umbrella build finished successfully with
  8,141 jobs.  The unused-argument lint passed, and 290 selected
  `#print axioms` checks reported only `propext`, `Classical.choice`, and
  `Quot.sound`.  The exact environment and source-closure record is in
  `../lean/STATUS.md` and `../lean/AXIOM_AUDIT.md`.
- Source archive: nine root-level files, no encryption, hidden entries, or
  path traversal.  It compiled independently in a fresh directory to the
  same 37-page PDF.
- SHA-256: final PDF
  `6f21d878513bf559b0fca0a08cac9e16400856377fd592cff2a8df332f9177cf`;
  source archive
  `0e71e228c0ce08dcc6e945663b4527ffe170dd817689f8d9bc0a81adc66ff655`.

## Author-only actions

Before clicking the final submission button, the author must:

1. confirm originality and exclusivity, authorship, funding, conflicts,
   data/code availability, the AI-assisted-tool wording, and independent
   verification of the manuscript;
2. recheck the live OJS metadata, upload the final PDF and source archive,
   and inspect the portal-generated preview; and
3. confirm that the public repository and the data/code-availability link are
   accessible after the synchronized GitHub revision is published.

The operational checklist is `SUBMISSION_CHECKLIST.md`.
