# Literature-positioning audit

Checked on 2026-08-13 against the downloaded full texts and publication
metadata.  Seven entries were added, increasing the bibliography from 15 to
22 items.  All 22 bibliography entries now have local full-text coverage (21
distinct PDF files because the 2025 Ammari et al. article and its 2026
corrigendum are stored together).  The claim-level evidence for every cited
entry, including exact local-PDF pages and theorem/equation locators, is
recorded in `REFERENCE_CLAIM_AUDIT.md`.

| BibTeX key | Local PDF in `../references/` | Role in the revised introduction | DOI |
|---|---|---|---|
| `Bottcher1994` | `Pseudospectra and singular values of large convolution operators.pdf` | Classic direct treatment of pseudospectra and singular values for large convolution/Toeplitz-type operators | [10.1216/jiea/1181075815](https://doi.org/10.1216/jiea/1181075815) |
| `Bottcher2024` | `Spectral instabilities.pdf` | Recent overview and examples of non-self-adjoint spectral instability, including Toeplitz-like settings | [10.4171/JST/483](https://doi.org/10.4171/JST/483) |
| `BogoyaGascaGrudsky2025` | `Eigenvalues for a class of non-Hermitian tetradiagonal Toeplitz matrices.pdf` | Recent finite-order eigenvalue asymptotics for a non-Hermitian Toeplitz class | [10.4171/JST/538](https://doi.org/10.4171/JST/538) |
| `ChandlerWildeEtAl2024` | `On spectral inclusion sets and computing the spectra and pseudospectra of bounded linear operators.pdf` | Recent convergent spectral/pseudospectral inclusion framework for banded and band-dominated operators | [10.4171/JST/514](https://doi.org/10.4171/JST/514) |
| `BurkeLewisOverton2007` | `Spectral conditioning and pseudospectral growth.pdf` | Pseudospectral growth, spectral conditioning, and component coalescence | [10.1007/s00211-007-0080-3](https://doi.org/10.1007/s00211-007-0080-3) |
| `TrefethenContediniEmbree2001` | `Spectra, pseudospectra, and localization for random bidiagonal matrices.pdf` | Pseudospectra and localization in random bidiagonal nonnormal matrices | [10.1002/cpa.4](https://doi.org/10.1002/cpa.4) |
| `Davies2001` | `Spectral properties of random non-self-adjoint matrices and operators.pdf` | Foundational random non-self-adjoint spectral-instability context | [10.1098/rspa.2000.0662](https://doi.org/10.1098/rspa.2000.0662) |

## Claim boundary

The revised introduction does **not** claim that none of the cited papers
studies connectedness.  It makes the narrower, supportable statement that the
cited bodies of work do not *by themselves* supply both:

1. the exact finite-order Euclidean-norm connectedness criterion for the full
   complex tridiagonal Toeplitz family; and
2. a strict threshold comparison for every adjacent pair of matrix orders.

The six newly downloaded files were checked for title, authors, journal,
volume/pages, and DOI, and their relevant full-text passages were compared
with the revised manuscript wording.  The same passage-level check was then
applied to the other 16 bibliography entries.  This audit caused three broad
group-citation sentences to be split and narrowed.  In particular, the 1994
Boettcher result is now described in its actual truncated Wiener--Hopf scope,
and the corrected finite-matrix statement from the 2026 `k`-Toeplitz
corrigendum is distinguished from the superseded 2025 theorem.  Local
full-text coverage and claim-level support are now 22/22.

The final submission pass re-extracted the cited evidence pages from the 20
text-bearing local files.  The remaining Schmidt--Spitzer PDF is an image
scan; local PDF pages 1, 5, and 6 were therefore inspected visually and
confirm the finite Toeplitz spectra, the limit set, and its characterization
in Theorem 1.  No citation wording required further revision.
