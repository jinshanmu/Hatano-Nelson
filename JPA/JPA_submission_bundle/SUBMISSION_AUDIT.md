# Submission audit

Audit date: 27 July 2026

## Original-file integrity

The source manuscript, bibliography, figure generator, and three source
figure PDFs in `SIMAX_submission_bundle` were hashed before revision and
checked again after the J. Phys. A bundle was completed.  All six SHA-256
checks matched.  No original submission-bundle file was altered.

## Mathematical preservation and consistency

- All 100 original LaTeX labels remain in the revised source.  Ten new
  labels name the six appendix sections, two concise appendix certificate
  statements, the pointwise backward-error identity, and the dimensional
  merger barrier.  All 110 labels are unique.
- A label-keyed comparison found all 84 original labelled equations,
  contained in 83 display environments, unchanged after whitespace,
  comments, and label placement were normalized.
- The mathematical content of all six original theorem, lemma, and
  proposition statements is unchanged.  One punctuation mark in the
  displayed parity definition in lemma 4.2 was moved from inside the final
  `cases` row to the end of the display; no formula, hypothesis, strict
  inequality, endpoint, asymptotic, parity case, or normalization convention
  was altered.  Two new appendix statements package calculations already
  present in the original proof.
- The final convention audit verified:
  - matrix size \(n\geq2\), with \(N=n+1\) used locally for the spectral mesh;
  - \(K-1\) as the matrix size in the chord construction;
  - \(n=2m\) and \(n=2m+1\) middle-branch indices and signs;
  - the central comparison \(c_m>d_m>c_{m+1}\);
  - the strict open convention
    \(\sigma_\varepsilon=\{s_{\min}<\varepsilon\}\) and
    connectedness if and only if \(\varepsilon>\gamma_n\);
  - \(N_f=N_e=N_c\), \(\gamma_2=a\), and
    \(N_c(a,a)=3\);
  - the hopping convention, \(H_n=t_LA_n(a)\), the conventional
    negative-sign Hamiltonian, the nonunitary similarity gauge, and the
    amplitude-versus-intensity skin depths;
  - the distinction among \(N_c\), \((N_c-1)d\), and skin depth in
    lattice-spacing units.
- Appendix moves preserve use order: the main text states the exact
  determinant implication before using vertical monotonicity, states the
  folded formulas and collision convention before the half-angle argument,
  records the two-way chord-sheet exhaustion before the gap comparisons, and
  states the central scalar and signed-root conclusions before the global
  Weyl/interlacing assembly.
- A label-keyed comparison after the final language pass confirmed that
  every original labelled equation and every original
  theorem/lemma/proposition statement remains unchanged.  Two new labelled
  displays make the already-used backward-error identity and dimensional
  merger barrier explicit near the main theorem; redundant unlabelled
  restatements later in the physical section were consolidated into
  cross-references.
- A final scope audit clarified that onsite and hopping perturbations belong
  to the unstructured norm ball, while realization of the extremal dimer
  perturbation by generic disorder is a separate question.  It also made the
  temporary assumption in the central derivative comparison explicit and
  restricted the polynomial-identity continuation to \(x,s\) for each fixed
  \(0<a<1\).
- A second independent review round rechecked every parity convention,
  signed-pencil branch, collision case, central-gap comparison, strict
  threshold equality, Lipschitz sampling implication, and physical
  normalization.  A final adversarial mathematical pass also checked the
  new backward-error, dimensional-barrier, infimum-threshold, resolvent, and
  skin-depth formulas.  It reported no P0, P1, P2, or mathematical P3 issue
  and judged the frozen candidate mathematically ready for submission.

No theorem-level mathematical error was found.

## Numerical certification issue identified and repaired

One genuine support-script overstatement was found in the original files:

- Original manuscript
  `final_connected_pseudospectrum_proof_2026-07-16.tex`, lines 2489–2493,
  inferred that the \(n=5,6\) cases were “mode-resolved” from a check that
  only the global barrier \(\gamma_n\) exceeded \(\varepsilon\).
- Original `make_hatano_nelson_figures.py`, lines 137–147, aggregated the
  largest sampled maximum over all gaps, while lines 207–218 used that one
  global result to label the disconnected panels as having \(n\) components.

The reason for concern is exact: \(\gamma_n\geq\varepsilon\) proves that at
least one real gap remains closed to the strict pseudospectrum, hence that
the pseudospectrum is disconnected, but it does not prove that every
adjacent gap remains closed.  It therefore cannot by itself certify one
component per eigenvalue.

The revised script repairs the inference by retaining a separate
sample/Lipschitz bracket for every real spectral gap.  It displays the
\(n\)-component labels only when every gap has a sampled lower check above
\(\varepsilon\).  For \(a=1/4\), \(\varepsilon=10^{-2}\), that condition is
met for \(n=5,6\); global upper checks put the \(n=7,8,9\) barriers below
\(\varepsilon\).  These implications are rigorous for exact samples, but
the NumPy/SciPy float64 SVD and eigenvalue computations are not interval
enclosures, as the manuscript and captions now state.  This repair changes
no theorem, proof, or analytic bound.

## Citation and repository audit

- All 29 bibliography entries are cited; there are no missing keys or
  uncited entries.
- Twenty-eight reference PDF files were available locally and checked.  They
  cover all 29 cited works because the two-page 2026 J. Phys. A corrigendum
  is appended as pages 30--31 of the same local PDF as the 2025 article.
  Direct inspection confirmed that the corrigendum identifies an error in
  theorem 3.3, replaces the relevant Toeplitz convergence statement, and
  weakens the spectral conclusions associated with theorems 3.5 and 3.7,
  while stating that the main spectrum and exponential eigenvector-decay
  results still hold.  The manuscript accordingly uses the neutral
  description that the finite-section pseudospectral convergence statement
  and its resulting limiting-spectrum theorems were corrected, and does not
  frame the present paper as a correction.
- No bibliography metadata error was found.  Particular checks covered the
  2024 mathematical-foundations and stability papers, the 2025
  \(k\)-Toeplitz article, its 2026 corrigendum, the 2025 pseudospectral
  scaling paper, and arXiv:2603.22643v3.
- Sentence-level attribution was narrowed where the full texts supported a
  more specific scope: the historical Hatano--Nelson sources, classical
  Toeplitz limit-set theory, general-matrix defectivity and variational
  optimization, banded-Toeplitz pseudospectra, and Toeplitz-structured
  perturbations are now cited separately.
- The Sirker comparison accurately records both the open-chain
  pseudospectral contours and the fixed-energy exponentially small
  singular-value branch tied to the Toeplitz index, without implying
  identical scope.
- The public repository was accessible at audit time.  It contained the
  16 July 2026 source/PDF, the figure generator and figures, a Lean 4.28.0
  project with pinned Mathlib revision, the manuscript-to-formalization map,
  and audit/status documents.  The revised data statement is intentionally
  concise and claims only that the Python code for the numerical
  illustrations and the Lean~4 code used for the accompanying mathematical
  formalization are available at the verified repository.  It does not
  extend kernel verification to the physical exposition or floating-point
  illustrations.
- Repository accessibility and contents were verified; the repository's
  reported full Lean build was not rerun as part of this editorial revision.
- A fresh sentence-level citation review after the final prose changes found
  no unsupported attribution, prestige-only citation, or missing reference.
  Every multi-reference group is in increasing numerical order; the former
  `[4,3]` ordering is absent.  No additional 2024--2026 reference was needed,
  so no further local download is required.

## Journal-format and build audit

- Checked the current official J. Phys. A scope/article-type page, IOP author
  instructions, current LaTeX-template page, research-data policy, and
  generative-AI policy.
- Used the downloaded current `iopjournal` class in 12-point mode and the
  regular research article type `Paper`.  No SIAM-only command or
  environment remains.
- Implemented the author’s double-anonymous choice through a small wrapper
  around the same main source.  It invokes the official `anonymous` class
  option, substitutes an anonymous running header, and clears PDF Author
  metadata without duplicating the mathematical body.  All identifying
  front matter and declarations are isolated in
  `jpa_identified_metadata.tex`; the shared source and wrapper contain no
  author name, email, ORCID, affiliation, or repository URL.  The generic
  AI-use declaration remains visible in both versions.
- The abstract contains approximately 150 prose words, below IOP's
  300-word guidance.
- The journal-owned class and ORCID graphic are not duplicated in the
  redistributable bundle.
- Clean `latexmk` builds with BibTeX completed successfully for both the
  author-identified and double-anonymous versions.  Both final logs have no
  fatal errors, missing figures, unresolved citations or references,
  multiply defined labels, overfull or underfull boxes, or font, package, or
  class warnings.
- The figure generator ran successfully.  Each PDF figure exists, is
  embedded in citation order, and has legible labels at its compiled width.
- All 41 author-version pages were rendered and inspected.  The title-page
  margin metadata, equations, figures, appendices, declarations, hyperlinks,
  and references were checked at full-page and enlarged figure-page scale.
  No clipping, collision, or unreadable label remains.
- All 41 pages of the anonymous reviewer PDF were rendered, with its title
  page, running header, AI disclosure, appendix boundary, and references
  also inspected at enlarged scale.  These elements are clean.
  PDF text, raw-string, and metadata searches found no author name, email,
  ORCID, affiliation, or repository URL.
- The anonymous source was also built from an isolated temporary directory
  containing only the wrapper, deidentified shared source, anonymous
  bibliography inputs, and figures.  The identified metadata file was
  absent, confirming that it is not a hidden compile-time dependency of the
  reviewer source set.
- The article title, manuscript body, abstract, figure captions,
  declarations, and bibliography are fully justified.  The journal header,
  author/address metadata, and section headings retain the current IOP
  class's ragged setting.  A second visual check found no objectionable word
  spacing, loose lines, or caption indentation after this adjustment.
- Figure typography was inspected at the actual compiled widths.  The three
  figures remain legible and have distinct functions: the component merger,
  the analytic barrier enclosure and unique crossing, and the relation
  between the real-axis barrier and the skin-mode envelope.  Float barriers
  keep them within section 6.
- The author-version acknowledgment names “OpenAI ChatGPT Work 5.6 Sol
  Ultra,” states its use for assistance with formula derivations, figure
  preparation, language polishing, and LaTeX typesetting, and assigns final
  review, verification, and responsibility to the human author.  The same
  generic acknowledgment appears in the anonymous reviewer PDF; only the
  identifying declarations are withheld.
- The generic Crossmark and received/revised date placeholders supplied by
  the template are absent from both final PDFs.  This was achieved through
  a manuscript-local patch, leaving the journal class unchanged.

## Counts and page allocation

Counts use TeXcount with merged input and exclude the bibliography.  The
first word-count row is the sum of text, headings, and captions; the second
also assigns one token to each inline or displayed formula:

| Measure | Original | Revised |
|---|---:|---:|
| Text, headings, and captions | 7,378 words | 8,679 words |
| TeXcount sum, including one token per inline/displayed formula | 8,511 | 9,875 |
| Author-identified compiled pages | 37 | 41 |
| Double-anonymous compiled pages | — | 41 |

The revised main text occupies pages 1--27.  The six appendices begin on
page 28 and end on page 39; page 39 is shared with the acknowledgments,
declarations, and the beginning of the references.  References continue
through page 41.  Thus the allocation is 27 main-text pages, approximately
12 appendix pages, and approximately three pages containing declarations
and references, with the noted shared boundary page.  The anonymous reviewer
version has the same main-text and appendix page ranges; its acknowledgment,
anonymous declarations notice, and references also occupy pages 39--41.
The original manuscript had no appendices: its proof and physical discussion
ran through approximately page 36, where the declarations also began, and
the reference list continued through page 37.

## Non-expository changes

No theorem statement or mathematical formula was changed for a
non-expository reason.  The substantive non-expository revisions were:

1. the per-gap numerical-certification repair documented above;
2. use of \(\widehat N_c\), rather than \(N_c\), for the non-interval
   numerical threshold shown in the figures;
3. narrowing of the Sirker comparison and repository/formalization claims
   to their verified scope;
4. conversion of article-number bibliography fields so that the standard
   numerical style prints them; and
5. revision of the generative-AI and data-availability declarations to match
   current IOP policy, the author-supplied model/version string, and the
   materials actually verified.

For exposition, two labelled identity displays were added near the main
theorem: the pointwise spectral backward-error formula and the dimensional
barrier \(\varepsilon_*(n)=t_L\gamma_n\), including its infimum
characterization.  They restate consequences already used later and alter no
result.

No other suspected mathematical error was identified.

## Frozen deliverable identifiers

At the final review freeze, the principal files had the following SHA-256
identifiers:

- TeX source:
  `6784cf68538c2bfe14ce5aa8bb38b1556160d1c8e16b522d288b9a53c52937e5`
- identified metadata:
  `a074ba30e9b11580dd8a3dd00560bd0f8eb0995a4fb70598cb25adfd71c99472`
- author-identified PDF:
  `e4f9ea430868efef867a38eabc19e2e9f4d11124cab3321d0510eb67b8995824`
- anonymous wrapper:
  `8fe6a0badd228da4102f41b9918f70b2ca508f65773f78fa3f972e7f649b71ed`
- double-anonymous PDF:
  `f5ec5366b4090b65f38dbec59b01c81afb5872e6a26da1503a2a40768a91a1e9`
- bibliography:
  `5fc466615b93bc293a71287c7501b565349d141cc103ae111724001499e3982f`
- figure generator:
  `411d94c2597de7efd216bec14cba49a3f2fb02ed24d3e59413159c9e14aadd7d`
