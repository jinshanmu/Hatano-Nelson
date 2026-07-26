# Change log for the J. Phys. A revision

## Front matter

- Replaced the generic class placeholders with the full journal name
  “Journal of Physics A: Mathematical and Theoretical” and the running
  author “Shanmu Jin,” using manuscript-local overrides that leave the
  journal-owned class untouched.
- Added the author’s ORCID, 0009-0009-5346-753X, through the class-native
  linked ORCID icon.
- Added a double-anonymous wrapper driven by the same main source.  Its PDF
  uses the official class option, replaces the running author with
  “Anonymous manuscript,” removes author/address/ORCID content and
  declarations from the reviewer view, and leaves the PDF Author metadata
  empty.  The author-identified version remains available for editorial
  records and later production.
- Moved the author name, ORCID, affiliation, email, repository-bearing data
  statement, and AI-use declaration into `jpa_identified_metadata.tex`.
  The shared manuscript source and anonymous wrapper are therefore
  textually deidentified when that identified-only file is omitted from a
  reviewer source upload.

## Title and abstract

- Replaced the matrix-analysis title with “Exact Connectedness Threshold for
  Pseudospectra of the Open Hatano–Nelson Chain.”
- Rewrote the abstract to begin with the finite-size physical and
  mathematical merger problem, introducing \(A_n(a)\) only after that
  motivation.
- Stated, without proof machinery, vertical monotonicity, component
  contractibility, the exact strict connectedness criterion, strict
  finite-size monotonicity, sharp-order bounds, equality of the first and
  eventual thresholds, and the logarithmic-plus-log-log site-count law.
- Identified \(2/\log(1/a)\) explicitly as the amplitude skin depth rather
  than the intensity decay length.
- Added the direct physical interpretation that the same imaginary gauge
  controlling skin localization fixes the finite-size loss of worst-case
  spectral resolution.

## Introduction and positioning

- Reorganized the opening around the open Hatano–Nelson chain, the merger of
  eigenvalue-centred Euclidean pseudospectral components, and connectedness
  as a worst-case spectral-resolution transition.
- Introduced the physical hopping convention, the positive-sign
  representative, the dimensionless matrix, and the strict open
  pseudospectrum in that order.
- Added an early main-results discussion in which \(\gamma_n\) is the largest
  real-axis backward-error barrier separating adjacent open-boundary
  spectral labels.
- Explained that strict decrease gives one system-size crossing at fixed
  uncertainty and excludes re-entrant disconnection.
- Stated explicitly that the result concerns unstructured spectral-norm
  uncertainty and is not the onset of the skin effect, the spectrum of one
  noisy realization, a structured-disorder threshold, or the termination of
  dynamical amplification.
- Recast the literature discussion to distinguish complete
  finite-dimensional pseudospectral topology and exact global-barrier
  comparison from prior Toeplitz-pseudospectrum, boundary-sensitivity, and
  numerical cloud-merger work.  Nearby papers and the published corrigendum
  are described neutrally; the manuscript is not framed as a correction.

## Whole-manuscript language polish

- Polished the abstract, main text, proofs, appendices, captions, and
  declarations for a direct mathematical-physics register consistent with
  J. Phys. A.
- Replaced repetitive defensive and negative constructions with active
  statements of scope, mechanism, and consequence.  The final article has
  no literal use of “not”; the four remaining uses of “no” occur only in
  the postal address and standard funding, conflict, and data declarations.
- Streamlined procedural proof narration, strengthened transitions between
  technical blocks, and replaced ambiguous uses of “topological” with
  “connectedness” or “pseudospectral component merger” where band topology
  could otherwise be inferred.
- Preserved the strict-pseudospectrum convention, every perturbation-scope
  caveat, the floating-point certification boundary, and the distinction between
  a connected union of attainable spectra and any single perturbation
  realization.
- Completed a second multi-agent editorial pass after the structural
  revision.  Independent reviewers rechecked mathematical consistency,
  physical positioning, citation support, declarations, figure legibility,
  and J. Phys. A presentation; no blocking or theorem-level issue remained.

## Proof restructuring

- Kept the model, definitions, main theorem, proof strategy, vertical
  monotonicity, signed-pencil mechanism, folded Chebyshev variables, chord
  parametrization, central/noncentral gap comparison, topology argument,
  sharp-order bounds, numerics, and physical interpretation in the main
  text.
- Replaced the procedural five-stage announcement at the start of the strict
  comparison with a conceptual roadmap: persymmetry produces signed
  eigenvalue branches, folded variables parametrize the relevant branch,
  scale inequalities handle noncentral gaps, and interlacing resolves the
  central obstruction.
- Added transitions explaining why each construction is needed and
  conclusion sentences recording exactly how each block advances
  \(\gamma_{n+1}<\gamma_n\).
- Reduced interruption of the main argument while retaining the formulas and
  certification statements needed to make the proof independently
  understandable.

## Appendices

- Added Appendix A, “Pentadiagonal continuant certificate for vertical
  monotonicity,” for the complete determinant-derivative certificate behind
  the short main-text monotonicity proof.
- Added Appendix B, “Folded-continuant transfer and boundary residuals,” for
  the five-minor transfer, characteristic-polynomial calculation, and
  boundary-residual checks.
- Added Appendix C, “Divided differences for the folded Chebyshev formulas,”
  for the lengthy rational-to-polynomial extraction.
- Added Appendix D, “Exhaustion of the endpoint-side chord sheet,” for the
  open--closed continuation, collision, endpoint, and converse cases used
  by the main-text chord parametrization.
- Added Appendix E, “Scalar estimate for the lower central-gap comparison,”
  for the detailed casewise scalar bounds.
- Added Appendix F, “Signed-root certification in the lower central gap,”
  for the final sign and root-separation verification.
- Preserved parity cases, collision conventions, endpoints, sign
  conventions, and every main-text dependency on these calculations.

## Physical interpretation

- Integrated the imaginary-gauge and skin-depth interpretation into the
  introduction, main-results discussion, numerical discussion, and final
  physical section.
- Kept the site convention for \(t_L,t_R\), the distinction between the
  positive-sign representative and the conventional negative-sign
  Hamiltonian, and the fact that the similarity gauge is nonunitary.
- Preserved the distinctions among the site count \(N_c\), physical
  end-to-end length \((N_c-1)d\), and the amplitude skin depth in
  lattice-spacing units.
- Retained \(\gamma_2=a\) and its rank-one perturbation interpretation as an
  exact endpoint illustration rather than the main conclusion.
- Clarified that connectedness concerns the union over a perturbation ball:
  it does not mean one perturbation fills the cloud, generic disorder
  realizes extremal perturbations, or a known perturbation path cannot be
  used to track eigenvalues.

## Figures

- Retained all three figures because they have distinct roles: the topology
  change, the rigorous barrier scale, and the skin-depth mechanism.
- Renamed section 6 simply “Numerical illustrations” and opened it by
  explaining those three roles directly.
- Removed software-package and implementation discussion from the article;
  reproducibility code is now identified only in the data-availability
  statement.
- Regenerated the figures with notation consistent with the revision.  The
  floating-point threshold is now denoted \(\widehat N_c\), avoiding confusion with
  the exact \(N_c\).
- Rewrote every caption to distinguish theorem-level conclusions from
  floating-point illustrations and to state that numerical calculations
  are independent of the proofs.
- Preserved the rigorous Lipschitz sampling implication and the warning that
  ordinary SVD computations are not interval-certified.
- Corrected an overstrong inference in the original numerical certification:
  a lower check for the global barrier proves disconnection but does not by
  itself prove one component per eigenvalue.  The revised script performs a
  separate lower check in every gap before displaying the \(n\)-component
  labels for \(n=5,6\).
- Flattened figure output into the source directory, as requested by the IOP
  upload guidance, and checked all labels at compiled journal width.
- Increased panel, axis, tick, and legend typography and enlarged the
  barrier plot to improve legibility at the compiled width.  Float barriers
  keep all three illustrations inside section 6.

## References

- Audited the sentence-level purpose of every citation and retained only
  references that support the associated statement.
- Described the 2025 paper and its 2026 published corrigendum separately and
  neutrally.
- Inspected the corrigendum directly on pages 30--31 of the combined local
  article PDF and described the amended finite-section spectral and
  pseudospectral statements without suggesting that the present manuscript
  is a correction.
- Kept the public repository citation only for the materials that were
  verified there: figure-generation code, pinned Lean 4 project,
  manuscript-to-formalization map, and audit documentation.
- Converted article-number metadata to a form printed correctly by the
  standard `unsrt` bibliography style.  All 29 bibliography entries are
  cited and compile.
- Corrected the descending citation group `[4,3]` to `[3,4]` and checked
  every multi-reference group against the `unsrt` first-appearance
  numbering.
- Separated historical model attribution from modern open-boundary
  localization statements, classical Toeplitz limit-set theory from later
  finite-section pseudospectral theory, matrix-defectivity results from
  broader variational optimization, and banded-Toeplitz pseudospectra from
  Toeplitz-structured perturbations.  These narrower formulations match the
  verified scope of the cited full texts.

## Declarations

- Revised the acknowledgment to identify “OpenAI ChatGPT Work 5.6 Sol
  Ultra,” state its use for assistance with formula derivations, figure
  preparation, language polishing, and LaTeX typesetting, and record final
  human review, verification, and responsibility.
- Adapted funding, conflict-of-interest, and data-availability statements to
  the current IOP commands and wording without adding funding, roles, or
  acknowledgments absent from the local record.
- Shortened data availability to the absence of experimental/external data,
  the location of the Python code, and the explicit statement that the
  accompanying Lean~4 code is used for mathematical formalization.

## LaTeX compatibility

- Replaced the SIAM class and SIAM-specific front matter and theorem
  machinery with the current 12-point `iopjournal` class and compatible
  standard packages.
- Preserved section-based equation and theorem numbering, semantic
  cross-references, and all 100 original labels.  The eight new labels name
  the six appendix sections and the two concise appendix certificate
  statements.
- Used the official IOP front-matter, acknowledgment, funding, and
  data-availability commands and the standard `unsrt` bibliography style.
- Overrode the class-wide ragged setting so that the article title,
  manuscript body, abstract, figure captions, declarations, and
  bibliography are fully justified, while preserving the IOP treatment of
  journal-header and author/address metadata and section headings.
- Kept the journal-owned class outside the redistributable bundle and placed
  every uploadable source and figure file in one directory.
- Rebuilt until there were no fatal errors, missing files, unresolved
  citations/references, multiply defined labels, overfull/underfull boxes, or
  font/package warnings.
- Built and visually inspected both deliverables: the 42-page
  author-identified PDF and the 40-page double-anonymous reviewer PDF.
