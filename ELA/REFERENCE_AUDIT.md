# Local-reference audit

Audited against the manuscript and the local PDF library on 2026-08-12.
Every one of the 15 bibliography keys is cited, has a corresponding local
PDF, and supports the statement to which it is attached.  Bibliographic
metadata and DOI values were checked against the PDFs and authoritative
records; all retained entries have a DOI, including the registered arXiv DOI
for the Sirker preprint.  The 2025 k-Toeplitz paper and its 2026 corrigendum
occupy pages 1--29 and 30--31, respectively, of one combined local PDF.

| Bib key | Local PDF | DOI | Claim checked |
|---|---|---|---|
| `AlamEtAl2011` | `../references/Characterization and construction of the nearest defective matrix via coalescence of pseudospectral components.pdf` | `10.1016/j.laa.2010.09.022` | Pseudospectral coalescence and distance to defectivity for matrices with distinct eigenvalues. |
| `AmmariEtAl2024` | `../references/Mathematical Foundations of the Non-Hermitian Skin Effect.pdf` | `10.1007/s00205-024-01976-y` | Exponential eigenmode envelope in a finite nonreciprocal resonator-chain Toeplitz model. |
| `AmmariEtAl2025` | `../references/Spectra and pseudo-spectra of tridiagonal k-Toeplitz matrices and the topological origin of the non-Hermitian skin effect.pdf` | `10.1088/1751-8121/add5ab` | Spectra and pseudospectra of periodic tridiagonal k-Toeplitz matrices. |
| `AmmariCorrigendum2026` | same combined PDF as `AmmariEtAl2025`, pages 30--31 | `10.1088/1751-8121/ae442e` | Corrections to the 2025 k-Toeplitz paper; cited together with the original. |
| `BottcherGrudsky2005` | `../references/Spectral Properties of Banded Toeplitz Matrices.pdf` | `10.1137/1.9780898717853` | Banded Toeplitz spectra, inverse norms, and asymptotic background. |
| `BurkeLewisOverton2003` | `../references/Optimization and Pseudospectra, with Applications to Robust Stability.pdf` | `10.1137/S0895479802402818` | Pseudospectral optimization and the eigenvalue-in-every-component theorem. |
| `ButtaGuglielmiNoschese2012` | `../references/Computing the Structured Pseudospectrum of a Toeplitz Matrix and Its Extreme Points.pdf` | `10.1137/120864349` | Toeplitz-structured pseudospectra. |
| `HatanoNelson1996` | `../references/Localization Transitions in Non-Hermitian Quantum Mechanics.pdf` | `10.1103/PhysRevLett.77.570` | Nonreciprocal nearest-neighbor hopping law. |
| `HatanoNelson1997` | `../references/Vortex pinning and non-Hermitian quantum mechanics.pdf` | `10.1103/PhysRevB.56.8651` | Lattice realization of the non-Hermitian hopping model. |
| `KiorpelidisMakris2025` | `../references/Scaling of pseudospectra in exponentially sensitive lattices.pdf` | `10.1103/PhysRevResearch.7.L032043` | Numerical and physical scaling study of pseudospectral-cloud merger in finite Hatano--Nelson lattices, including a numerically identified critical order. |
| `NoschesePasquiniReichel2013` | `../references/Tridiagonal Toeplitz matrices.pdf` | `10.1002/nla.1811` | Complex tridiagonal Toeplitz structure, spectral sensitivity, and pseudospectra. |
| `ReichelTrefethen1992` | `../references/Eigenvalues and pseudo-eigenvalues of Toeplitz matrices.pdf` | `10.1016/0024-3795(92)90374-J` | Finite Toeplitz resolvents and pseudospectra. |
| `SchmidtSpitzer1960` | `../references/The Toeplitz Matrices of an Arbitrary Laurent Polynomial.pdf` | `10.7146/math.scand.a-10588` | Spectral limit sets of finite Toeplitz sections. |
| `Sirker2026` | `../references/Pseudospectral phenomena and the origin of the non-Hermitian skin effect.pdf` | `10.48550/arXiv.2603.22643` | Hatano--Nelson pseudospectra, exponentially small singular values, and the nonunitary-similarity scale; it does not state a finite-order connectedness theorem. |
| `TrefethenEmbree2005` | `../references/Spectra and Pseudospectra.pdf` | `10.1515/9780691213101` | Equivalent perturbation definition and the eigenvalue-in-every-component theorem. |

The manuscript bibliography uses `siamplain.bst`, prints the 15 verified DOI
links, and treats `33`, `205201`, `079501`, and `L032043` as electronic
article numbers (`eid`) rather than page numbers.

## Closest-work boundary checked

The 2025 \(k\)-Toeplitz article and its corrigendum study periodic
tridiagonal Toeplitz spectra and pseudospectra in a broader coefficient
setting, but do not supply the present paper's exact finite-order
connectedness criterion, strict comparison at every adjacent matrix order,
contractibility of every component, or first-connected-order asymptotic.
Kiorpelidis--Makris numerically display and scale the merger of separate
Hatano--Nelson pseudospectral clouds; the present paper turns that observed
transition into an exact all-order theorem and extends it to the full complex
three-parameter family.  Sirker supplies complementary physical and
operator-theoretic context for pseudospectral instability and its exponential
scale, not a competing connectedness classification.
