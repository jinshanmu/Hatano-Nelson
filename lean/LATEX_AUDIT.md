# LaTeX audit

Immutable source:
`/Users/shanmujin/Documents/Hatano-Nelson/SIMAX_submission_bundle/final_connected_pseudospectrum_proof_2026-07-13.tex`

SHA-256:
`b4828ea18c0386e0a694c91af065c523c948ef4cf003a7ee1d823d19a8c72223`

Last full source review: 2026-07-15.

The pre-rename checksum was
`7cf4fc9fa4b019f6185560f38b20d8f1901d793b36e068d002c272bdeeed7a6f`.
The only content change is the filename in the line-2 compilation-command
comment; the audited mathematical text and all line numbers are unchanged.

This file records formalization-relevant omissions or ambiguities.  The source
mathematics is not modified by the audit.

Scope disposition: no unresolved defect is known in `thm:main` or its complete
kernel dependency graph.  The proof omissions, ambiguity, and strictness error
listed below are repaired explicitly in Lean without changing the theorem's
statement.  `FORMALIZATION_MAP.md` separately classifies all 95 mathematical
labels as 80 literal kernel counterparts, 12 proof-sufficient nonliteral
counterparts, and three audited-only items; it also inventories important
unlabeled physical and numerical claims outside the kernel scope.  The latest
default build and source-safety evidence is recorded in `STATUS.md`.

## Scope limitations that are not theorem defects

- The manuscript's folded-root formulas allow possibly complex roots when the
  discriminant is negative.  Lean proves the global determinant/transfer
  identities, explicit actual-root formulas on the positive-discriminant real
  sheets, and the derivative formula at collision.  The negative-discriminant
  complex-root presentation is not formalized because it is not used by the
  real-sheet proof.
- The exact Lambert-`W_{-1}` floor identity is not a Lean theorem.  The project
  instead proves elementary logarithmic and floor/ceiling bounds that give the
  bounded-error inversion actually used for the main asymptotic.
- The physical rescalings, PBC ellipse, full left/right mode display, and skin
  interpretation are audited exposition rather than kernel dependencies.

## Numerical certification wording

The displayed numerical values and topology margins reproduce with the
supplied NumPy/SciPy float64 script.  The grid `h/2` Lipschitz enclosure is
mathematically valid for exact sampled singular values, but the implementation
does not enclose floating-point SVD or eigenvalue error.  Consequently the
manuscript's “certify” language describes a reproducible floating-point check
conditional on computed samples, not a validated numerical, interval, or
kernel certificate.  None of these numerics is used in `thm:main`.

## Dimension-one endpoint correction in `lem:vertical`

- Source lines: 303–318, especially the diagonal display at 308–311.
- Classification: boundary ambiguity; the subsequent proof uses the correct
  formula.
- Written display: the diagonal of `P_n` is described as
  `d - 1, d, …, d, d - a²`.
- Issue: this display is literal only when `n ≥ 2`.  For `n = 1`, the first
  and last coordinates coincide, so both endpoint corrections apply to the
  same entry:

  ```text
  P₁(Y,t) = [d - 1 - a²] = [x² + Y - t²].
  ```

- Why the argument remains valid: the sequential boundary correction at
  lines 353–361 gives `F₁ = D₁ - a² D₀`, which applies both corrections and
  is correct.  The derivative is separately handled at lines 465–467.
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

- Lines 627–628: the formalization proves that the spectrum of `A_m` is
  precisely the set of the even-indexed eigenvalues of `A_(2m+1)` before
  deriving nonsingularity of `xI_m - A_m` in the larger path's open gap.
- Lines 757–790: the Schur-complement computation is first made on a dense
  nonsingular set and then extended polynomially.  `FoldedMinorBridge` and
  `FoldedTransfer` instead prove the five-minor update by direct determinant
  identities, with no nonsingularity assumption or dense-set passage.
- Lines 1174–1225: the formalization supplies a closed invariant for the
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
- Lines 1930–1936: the formalization proves that the chosen gap maximum lies
  in the open gap: both endpoints have height zero, while every interior point
  is nonsingular and has strictly positive least singular value.
- Lines 1539–1541: the displayed logarithmic-derivative quotient has
  denominator `rho^2-1`, so its literal use requires `rho != 1`.  In the only
  branch where it is invoked the proof assumes `rho <= a < 1`, which supplies
  this side condition; the source then treats `rho=1` separately as
  immediate.  The Lean quotient lemma carries the explicit `rho != 1` guard,
  and the calling proofs perform the required case split.
- Lines 1618–1674: the sentence “the case `rho = 1` follows by continuity” can
  be replaced by a direct endpoint calculation, as it is in Lean.  At `rho = 1`,
  `b = (L+1)/L = 1+1/L`, and the required quantity is the already positive
  `Upsilon(1+omega_L)`.
- Lines 1849–1865: the displayed estimate uses the unstated weakening
  `c < 2 a sin(theta_L-Delta_L) < 2 sqrt(a) sin(theta_L-Delta_L)`, valid
  because `0 < a < 1`; the formal proof supplies this weakening explicitly.
- Lines 1795–1800: positivity of the displayed ratio follows from
  `D_L > 1`, `rho > rho_ref > omega_L`, and
  `rho + omega_L > 1 - omega_L`; these inequalities are explicit inputs to
  the Lean positivity proof.
- Line 1761 defines only `x_*^2`, but the later membership statement at line
  1921 needs `x_* > 0`.  `OddCentralLowerFolded` defines `x_*` as the positive
  square root and proves both its positivity and its square identity.  The
  radicand is positive from `0 < a`, `0 < 1-omega_L`, and
  `0 < (rho+omega_L)/(zeta+omega_L)`.  This makes the intended branch choice
  explicit without changing any displayed identity.

## Harmless strictness error in the odd central-gap scalar estimate

- Source line: 1721, in the proof of the lower central comparison
  `d_m > c_(m+1)`.
- Classification: incorrect displayed strict inequality; the corrected weak
  inequality proves the same downstream strict conclusion.
- Written claim: for `L ≥ 2`,
  `5 / (2L + 1)^2 < 1 / 5`.
- Issue: at `L = 2` both sides are exactly `1 / 5`.
- Correct statement: `5 / (2L + 1)^2 ≤ 1 / 5` for `L ≥ 2`.
- Why the argument remains valid: the immediately preceding estimate is
  strict, `upsilon < 5 / (2L + 1)^2`; composing it with the corrected weak
  bound still gives the required `upsilon < 1 / 5`.
- Implemented Lean treatment: `five_div_reference_den_sq_le_one_fifth` proves
  the weak rational inequality by exact arithmetic, and the strict conclusion
  is retained by transitivity.  No theorem statement or downstream comparison
  changes.

These are implemented, checked proof-expansion repairs, not changes to
`lem:mesh` or `thm:main`.  Final validation of both assembled results is
recorded in `STATUS.md`.
