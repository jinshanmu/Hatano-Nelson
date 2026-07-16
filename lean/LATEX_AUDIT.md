# LaTeX audit

Audited source:
`SIMAX_submission_bundle/final_connected_pseudospectrum_proof_2026-07-16.tex`

SHA-256:
`84e0021272c9a9eb5cbfba3f6c82c4219bc2d64382232ebe68084bc9febe29b6`

Source size: 2,477 lines; 89,709 bytes.

Last full source review: 2026-07-16.

This file records formalization-relevant omissions or ambiguities.  The
statement-level repairs incorporated in the dated source do not change its
main mathematical results.

Scope disposition: no unresolved defect is known in `thm:main` or its complete
kernel dependency graph.  The source has 102 labels: 92 mathematical, seven
section, and three figure labels.  `FORMALIZATION_MAP.md` classifies all 92
mathematical labels as literal kernel counterparts: zero are proof-sufficient
and zero are audited-only.  It separately inventories important unnumbered
physical, numerical, and expository claims outside the kernel scope.  The
latest default build and source-safety evidence is recorded in `STATUS.md`.

## Current manuscript-to-Lean alignment

The 2026-07-16 manuscript incorporates the formalization audit's statement-level
repairs:

- `eq:physical-scaling` and `eq:imaginary-gauge` now contain only the
  dimensionless logarithmic and gauge identities proved in Lean.  The
  dimensional OBC identification, PBC ellipse, full physical mode display, and
  skin-depth display are intentionally unnumbered physical exposition.
- `eq:odd-dilation` is literal: Lean proves the leading block, coupling column,
  transposed coupling row, and bottom-right entry of the bordered matrix.
- The folded section states the global recurrence via `Pi`, uses generic real
  variables satisfying the symmetric sum/product relations, and introduces
  the canonical `xi_±` only under `Delta_fold ≥ 0`.  The generating functions
  use `Pi^{-1}`, and the real-pair divided differences include their checked
  derivative value at collision.  These are exactly the domains and formulas
  proved in Lean.
- `eq:Delta-upsilon-bounds` now prints the correct weak endpoint inequality,
  records equality at `L=2`, and derives the strict downstream estimate from
  the preceding strict bound.
- `eq:chi` has a direct all-angle Lean theorem, including the root-power and
  homogeneous-sum modulus identities.
- `eq:tail-threshold-Lambert` is literal.  `LambertWThreshold` constructs the
  lower real branch, proves the sharp argument-domain bound, identifies the
  strict permanent tail crossing with the displayed floor, and proves the
  stated lower-branch logarithmic–logarithmic bounded-error expansion.  The
  Lean function is totalized to zero off `[-exp(-1),0)`, but every theorem that
  uses it as `W_{-1}` either carries the natural-domain hypothesis explicitly
  or derives it from its small-parameter hypotheses.

## Numerical certification wording

The displayed numerical values and topology margins reproduce with the
supplied NumPy/SciPy float64 script.  The grid `h/2` Lipschitz enclosure is
mathematically valid for exact sampled singular values, but the implementation
does not enclose floating-point SVD or eigenvalue error.  Consequently the
manuscript's “certify” language describes a reproducible floating-point check
conditional on computed samples, not a validated numerical, interval, or
kernel certificate.  None of these numerics is used in `thm:main`.

## Dimension-one endpoint correction in `lem:vertical` (resolved in 2026-07-16)

- Source lines: 308–323, especially the diagonal display at 313–316.
- Classification: resolved boundary ambiguity; the proof always used the
  correct formula.
- The 2026-07-16 source now states that the displayed diagonal
  `d - 1, d, …, d, d - a²` applies for `n ≥ 2`.  It separately records that,
  for `n = 1`, the first and last coordinates coincide, so both endpoint
  corrections apply to the same entry:

  ```text
  P₁(Y,t) = [d - 1 - a²] = [x² + Y - t²].
  ```

- Why the argument remains valid: the sequential boundary correction at
  lines 358–366 gives `F₁ = D₁ - a² D₀`, which applies both corrections and
  is correct.  The derivative is separately handled at lines 470–472.
- Implemented Lean treatment: `VerticalContinuant` and `VerticalToeplitz`
  encode both endpoint corrections and split the determinant base cases at
  `n = 0`, `n = 1`, and `n ≥ 2`; in dimension one the coincident corrections
  are both applied.  No theorem statement or downstream formula is changed.
- Checks performed: exact symbolic determinant calculations in dimensions
  1, 2, and 3 agree with `F_n = D_n - a² D_{n-1}`; the Toeplitz recurrence,
  including its `k = 2` inhomogeneous term, agrees through `k = 8`.

No theorem-level defect was established in the completed audit.

## Implemented repairs for valid implicit steps in `lem:mesh`

An independent exact-algebra and small-dimension audit found no false identity,
and the following prose steps have been made explicit in checked Lean lemmas.
The final `lem:mesh` and `thm:main` assemblies have also been kernel checked.

- Lines 632–633: the formalization proves that the spectrum of `A_m` is
  precisely the set of the even-indexed eigenvalues of `A_(2m+1)` before
  deriving nonsingularity of `xI_m - A_m` in the larger path's open gap.
- Lines 777–810: the Schur-complement computation is first made on a dense
  nonsingular set and then extended polynomially.  `FoldedMinorBridge` and
  `FoldedTransfer` instead prove the five-minor update by direct determinant
  identities, with no nonsingularity assumption or dense-set passage.
- Lines 1200–1248: the formalization supplies a closed invariant for the
  maximal continuation interval.  Its possible interior boundary failures—
  folded-variable collision, `y = 0`, `z = cosh h`, an inner nodal endpoint,
  or `z = u_K^max`—are excluded by separate lemmas.
  Formalization also exposes two logically distinct exhaustion directions:
  every actual gap point must lie on the selected chord sheet, and every
  interior chord parameter must produce an actual point of that gap with the
  selected signed middle root.  The first direction follows from a relatively
  clopen subset of the gap; it does not imply the second unless horizontal
  monotonicity is assumed.  Since the source explicitly avoids that
  monotonicity assumption, the second direction is proved by its own
  open--closed continuation lemma on the angle interval, using the endpoint
  germ, determinant-root continuation, root nonvanishing, and exclusion of
  nodal endpoints.  This is a valid omitted intermediate argument, not a
  change to the stated comparison.
- Lines 1958–1964: the formalization proves that the chosen gap maximum lies
  in the open gap: both endpoints have height zero, while every interior point
  is nonsingular and has strictly positive least singular value.
- Lines 1562–1564: the displayed logarithmic-derivative quotient has
  denominator `rho^2-1`, so its literal use requires `rho != 1`.  In the only
  branch where it is invoked the proof assumes `rho <= a < 1`, which supplies
  this side condition; the source then treats `rho=1` separately as
  immediate.  The Lean quotient lemma carries the explicit `rho != 1` guard,
  and the calling proofs perform the required case split.
- Lines 1641–1697: the sentence “the case `rho = 1` follows by continuity” can
  be replaced by a direct endpoint calculation, as it is in Lean.  At `rho = 1`,
  `b = (L+1)/L = 1+1/L`, and the required quantity is the already positive
  `Upsilon(1+omega_L)`.
- Lines 1877–1893: the displayed estimate uses the unstated weakening
  `c < 2 a sin(theta_L-Delta_L) < 2 sqrt(a) sin(theta_L-Delta_L)`, valid
  because `0 < a < 1`; the formal proof supplies this weakening explicitly.
- Lines 1823–1828: positivity of the displayed ratio follows from
  `D_L > 1`, `rho > rho_ref > omega_L`, and
  `rho + omega_L > 1 - omega_L`; these inequalities are explicit inputs to
  the Lean positivity proof.
- Line 1786 defines only `x_*^2`, but the later membership statement at line
  1949 needs `x_* > 0`.  `OddCentralLowerFolded` defines `x_*` as the positive
  square root and proves both its positivity and its square identity.  The
  radicand is positive from `0 < a`, `0 < 1-omega_L`, and
  `0 < (rho+omega_L)/(zeta+omega_L)`.  This makes the intended branch choice
  explicit without changing any displayed identity.

These are implemented, checked proof-expansion repairs, not changes to
`lem:mesh` or `thm:main`.  Final validation of both assembled results is
recorded in `STATUS.md`.
