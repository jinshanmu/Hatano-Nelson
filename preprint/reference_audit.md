# Reference audit for the preprint

Checked on 19 September 2026 against the original articles in `../references/`, publisher records, and Crossref DOI registrations. The accompanying `references.bib` contains nine cited articles. Every entry is a journal article and has a DOI; no books or physics papers are included. Bibliography order should follow first citation in the manuscript.

The locators below document the audit only. They should not appear in the manuscript's citations. In the manuscript use ordinary numeric citations, with neither author-year citation commands nor page/theorem/section locators.

## Core articles

### `Trefethen1997`

L. N. Trefethen, *Pseudospectra of Linear Operators*, SIAM Review **39**(3) (1997), 383–406. DOI: [10.1137/S0036144595295284](https://doi.org/10.1137/S0036144595295284).

- Original inspected: `../references/Pseudospectra of Linear Operators.pdf`, PDF page 3 (journal page 385). The three displayed definitions identify pseudospectra through the resolvent norm, spectra of norm-bounded perturbations, and the smallest singular value. The text between the second and third displays explicitly treats strict perturbations and the interior.
- The article generally uses closed pseudospectra. The preprint may introduce its own open convention and cite this paper for the equivalences; the strict form is also explicit in `BurkeLewisOverton2003`.
- Suggested use: “The pseudospectrum can be described equivalently through the resolvent norm, the least singular value, or spectra of nearby matrices \cite{Trefethen1997}.”
- Metadata verified against [SIAM's article record](https://epubs.siam.org/doi/abs/10.1137/S0036144595295284), the original title page, and the DOI registration.

### `ReichelTrefethen1992`

L. Reichel and L. N. Trefethen, *Eigenvalues and pseudo-eigenvalues of Toeplitz matrices*, Linear Algebra and its Applications **162–164** (1992), 153–185. DOI: [10.1016/0024-3795(92)90374-J](https://doi.org/10.1016/0024-3795(92)90374-J).

- Original inspected: `../references/Eigenvalues and pseudo-eigenvalues of Toeplitz matrices.pdf`. PDF page 2 gives the equivalent pseudospectral definitions. PDF pages 21–23 (journal pages 173–175) derive symbol-based inclusions for banded Toeplitz matrices with exponentially small error, by constructing geometric pseudoeigenvectors. PDF pages 16–17 also discuss an explicit tridiagonal example.
- Suggested use: “For banded Toeplitz matrices, symbol-based constructions yield pseudoeigenvectors with residuals that decrease exponentially with the matrix order \cite{ReichelTrefethen1992}.”
- Do not claim exponential growth at every point outside every Toeplitz spectrum; the theorem has specific symbol-region hypotheses. The suggested sentence describes the existence and method, without dropping those restrictions into an overbroad universal claim.
- Metadata verified against [Elsevier's article record](https://www.sciencedirect.com/science/article/pii/002437959290374J), the original title page, and the DOI registration.

### `Bottcher1994`

A. Böttcher, *Pseudospectra and singular values of large convolution operators*, Journal of Integral Equations and Applications **6**(3) (1994), 267–301. DOI: [10.1216/jiea/1181075815](https://doi.org/10.1216/jiea/1181075815).

- Original inspected: `../references/Pseudospectra and singular values of large convolution operators.pdf`, PDF pages 1–5 and 19–20. Theorems 6.3 and 6.4, for the stated continuous-symbol class, establish convergence of inverse norms and pseudospectra of truncated Wiener–Hopf operators to the corresponding half-line operator quantities.
- Suggested use: “Related limiting results for inverse norms and pseudospectra of truncated Wiener–Hopf operators are established in \cite{Bottcher1994}.”
- Keep the operator class explicit. This paper is not a finite-order connectedness or adjacent-order monotonicity theorem for the matrices in the preprint.
- Title, author, year, volume, issue and DOI verified through [Crossref's registration](https://api.crossref.org/works/10.1216/jiea/1181075815); pages 267–301 verified directly from the original article. The publisher landing page was inaccessible to the browser, so it was not treated as inspected content.

### `NoschesePasquiniReichel2013`

S. Noschese, L. Pasquini and L. Reichel, *Tridiagonal Toeplitz matrices: properties and novel applications*, Numerical Linear Algebra with Applications **20**(2) (2013), 302–326. DOI: [10.1002/nla.1811](https://doi.org/10.1002/nla.1811).

- Original inspected: `../references/Tridiagonal Toeplitz matrices.pdf`, PDF page 3, formulas (4)–(8), for explicit eigenvalues and left/right eigenvectors; the individual and global condition-number discussion; and the pseudospectral discussion following formula (24).
- Suggested use: “Explicit eigenvectors allow a detailed analysis of the spectral sensitivity of tridiagonal Toeplitz matrices \cite{NoschesePasquiniReichel2013}.” The eigenvalue/eigenvector formulas in the mathematical preliminaries may also cite this source, although the preprint can prove them directly.
- The local PDF is the online-first version dated 2012. The final issue is March 2013; **2013** is the correct bibliography year for volume 20, pages 302–326.
- Metadata and final year verified against [Wiley's article record](https://onlinelibrary.wiley.com/doi/10.1002/nla.1811), including its formal citation text.

### `BurkeLewisOverton2003`

J. V. Burke, A. S. Lewis and M. L. Overton, *Optimization and pseudospectra, with applications to robust stability*, SIAM Journal on Matrix Analysis and Applications **25**(1) (2003), 80–104. DOI: [10.1137/S0895479802402818](https://doi.org/10.1137/S0895479802402818).

- Original inspected: `../references/Optimization and Pseudospectra, with Applications to Robust Stability.pdf`, PDF pages 3–4 for strict pseudospectra and the least-singular-value characterization; PDF page 10 (journal page 89), Theorem 5.1 and its proof, for the component lemma.
- Exact supported mathematical use: “Every connected component of an open pseudospectrum contains an eigenvalue \cite{BurkeLewisOverton2003}.”
- The paper also studies the pseudospectral abscissa and its variational properties. A broad sentence on pseudospectral optimization is valid, but this reference is most useful for the component fact actually used by the proof.
- Metadata verified against [SIAM's article record](https://epubs.siam.org/doi/10.1137/S0895479802402818) and the original title page.

### `BurkeLewisOverton2007`

J. V. Burke, A. S. Lewis and M. L. Overton, *Spectral conditioning and pseudospectral growth*, Numerische Mathematik **107**(1) (2007), 27–37. DOI: [10.1007/s00211-007-0080-3](https://doi.org/10.1007/s00211-007-0080-3).

- Original inspected: `../references/Spectral conditioning and pseudospectral growth.pdf`, PDF pages 1–2, and PDF page 8 (journal page 34), Theorem 3.1 with the following argument. The first-merger level is characterized as the distance to matrices with multiple eigenvalues; the paper uses closed pseudospectra for the minimum formulation and examines the strict pseudospectrum at the critical level separately.
- Suggested use: “For a matrix with distinct eigenvalues, the first coalescence level is the distance to matrices with multiple eigenvalues \cite{BurkeLewisOverton2007}.”
- Avoid identifying that first-merger level with the complete-connectedness threshold studied here when there are more than two components.
- Metadata verified against [Springer's article record](https://link.springer.com/article/10.1007/s00211-007-0080-3), the original title page and the DOI registration.

### `AlamEtAl2011`

R. Alam, S. Bora, R. Byers and M. L. Overton, *Characterization and construction of the nearest defective matrix via coalescence of pseudospectral components*, Linear Algebra and its Applications **435**(3) (2011), 494–513. DOI: [10.1016/j.laa.2010.09.022](https://doi.org/10.1016/j.laa.2010.09.022).

- Original inspected: `../references/Characterization and construction of the nearest defective matrix via coalescence of pseudospectral components.pdf`, PDF pages 3–4 and 6–7. The article assumes distinct eigenvalues, defines open pseudospectra, identifies the first-coalescence level with the distance to defectivity, and proves that first-coalescence points are lowest generalized saddle points of the least-singular-value function.
- Suggested use: “The points of first coalescence are lowest generalized saddle points of the least-singular-value function, and their common level equals the distance to defectivity \cite{AlamEtAl2011}.” Precede this with the distinct-eigenvalue hypothesis and the Euclidean operator norm convention.
- Metadata and content verified against the [author-hosted published original](https://cs.nyu.edu/overton/papers/pdffiles/neardefmat.pdf) and the DOI registration.

## Optional related work

### `ButtaGuglielmiNoschese2012`

P. Buttà, N. Guglielmi and S. Noschese, *Computing the structured pseudospectrum of a Toeplitz matrix and its extreme points*, SIAM Journal on Matrix Analysis and Applications **33**(4) (2012), 1300–1319. DOI: [10.1137/120864349](https://doi.org/10.1137/120864349).

- Original inspected: `../references/Computing the Structured Pseudospectrum of a Toeplitz Matrix and Its Extreme Points.pdf`, PDF pages 1–3. The perturbations preserve the nonzero Toeplitz diagonals; the norm is Frobenius. Algorithm 1 computes locally rightmost points, with related constructions for the radius and nearby boundary.
- Suggested use: “Algorithms for the extreme points of Toeplitz-structured pseudospectra in the Frobenius norm are developed in \cite{ButtaGuglielmiNoschese2012}.”
- Include only if the introduction discusses structured perturbations. No defensive paragraph contrasting this with the present problem is needed.
- Metadata verified against the original title page and [SIAM's article record](https://epubs.siam.org/doi/10.1137/120864349).

### `ChandlerWildeEtAl2024`

S. Chandler-Wilde, R. Chonchaiya and M. Lindner, *On spectral inclusion sets and computing the spectra and pseudospectra of bounded linear operators*, Journal of Spectral Theory **14**(2) (2024), 719–804. DOI: [10.4171/JST/514](https://doi.org/10.4171/JST/514).

- Original inspected: `../references/On spectral inclusion sets and computing the spectra and pseudospectra of bounded linear operators.pdf`, PDF pages 2–6, 20, and 52–53. Theorem 1.9 provides finite-section-based pseudospectral inclusions and Hausdorff convergence in the tridiagonal setting; Theorem 6.1 extends the construction to band-dominated operators under its stated hypotheses.
- Suggested use: “Finite-section methods also provide convergent spectral and pseudospectral inclusion sets for banded and band-dominated operators \cite{ChandlerWildeEtAl2024}.”
- This is useful recent mathematical context if discussing finite-section limits, rather than evidence for the present matrix-order theorem.
- Metadata verified against the original title page, [EMS Press's article record](https://ems.press/journals/jst/articles/14297880), and the DOI registration.

## Suggested compact related-work text

The following wording uses the seven core references without attributing any of the new results to prior literature. It is a source-checked draft, not mandatory manuscript wording:

> Pseudospectra admit equivalent descriptions through resolvent norms, least singular values, and spectra of nearby matrices \cite{Trefethen1997}. For banded Toeplitz matrices, symbol-based constructions yield pseudoeigenvectors with residuals that decrease exponentially with the matrix order \cite{ReichelTrefethen1992}. Related limiting results for inverse norms and pseudospectra of truncated Wiener–Hopf operators are established in \cite{Bottcher1994}. Explicit eigenvectors also permit a detailed analysis of the spectral sensitivity of tridiagonal Toeplitz matrices \cite{NoschesePasquiniReichel2013}.
>
> Every connected component of an open pseudospectrum contains an eigenvalue \cite{BurkeLewisOverton2003}. For a matrix with distinct eigenvalues, the first coalescence level equals its distance, in the Euclidean operator norm, to matrices with multiple eigenvalues \cite{BurkeLewisOverton2007}. The points of first coalescence are lowest generalized saddle points of the least-singular-value function, and their common level is also the distance to defectivity \cite{AlamEtAl2011}.

The preprint should then state its own exact criterion for complete connectedness and its adjacent-order comparison directly. It need not assert that no previous work addresses connectedness or add unsupported claims of priority.
