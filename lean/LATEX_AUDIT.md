# LaTeX audit

Audited source:
`SIMAX_submission_bundle/final_connected_pseudospectrum_proof_2026-07-16.tex`

SHA-256:
`280945bf9f0e0952bfb0eca719754ab6493490d4cbfe6c18bb9a61bdf3744b75`

Source size: 2,571 lines; 93,912 bytes.

Last full source review: 2026-07-16.

This file records the formalization-relevant omissions or ambiguities found
during the audit and how they were resolved.  The statement-level and
proof-expansion repairs incorporated in the dated source do not change its
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

The source now makes the numerical status explicit at lines 2377–2442.  For a
uniform grid of maximum spacing `h`, the 1-Lipschitz property gives
`M_h ≤ gamma_n ≤ M_h + h/2` when `M_h` is formed from exact sampled least
singular values.  The manuscript separately states that the supplied
NumPy/SciPy implementation uses float64 SVD and eigenvalue values without an
enclosure of their roundoff.  It therefore calls the reported margins and
threshold reproducible floating-point checks conditional on those samples,
not validated interval certificates.  The figures distinguish those computed
estimates from the exact analytic bounds, and none of the numerics is used in
`thm:main`.

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

## Absorbed proof-expansion repairs in `lem:mesh`

An independent exact-algebra and small-dimension audit found no false identity.
The manuscript now contains every corresponding intermediate argument, the
same obligations are explicit in checked Lean lemmas, and the final `lem:mesh`
and `thm:main` assemblies have been kernel checked.

- Lines 635–643 identify `spec(A_m)` exactly with the even-indexed eigenvalues
  of `A_(2m+1)` before concluding that `xI_m-A_m` is nonsingular in an open gap
  of the larger path.  The same spectral identification and nonsingularity
  implication are explicit in Lean.
- Lines 787–822 perform the Schur-complement calculation on the stated dense
  nonsingular set and then invoke polynomial identity to cover singular cases.
  `FoldedMinorBridge` and `FoldedTransfer` give the complementary Lean proof of
  the five-minor update by direct determinant identities, without an inverse or
  dense-set assumption.
- Lines 1196–1290 spell out both chord-exhaustion directions.  For actual gap
  points, lines 1222–1269 define the selected sheet as a relatively open and
  relatively closed subset of the gap and exclude folded-variable collision,
  `y = 0`, `z = cosh h`, inner nodal endpoints, and `z = u_K^max`.  For the
  converse, lines 1271–1289 use the continuous reconstructed angle, its exact
  values at the two spectral endpoints, the intermediate value theorem, and
  uniqueness of the endpoint-side outer solution to realize every interior
  chord parameter.  Thus this second exhaustion is not attributed to the
  relative clopen argument and does not assume monotonicity of `theta -> x`.
  Lean records the continuation invariants, boundary exclusions, endpoint
  data, classification, and exhaustion consequences used by this argument.
- Lines 492–506 prove that every maximum defining a gap height is attained in
  the open gap: spectral endpoints have height zero, whereas every interior
  point is nonsingular and has strictly positive least singular value.  Lines
  2032–2045 invoke this observation when choosing the comparison maximizer.
  The corresponding interiority fact is explicit in Lean.
- Lines 1596–1619 use the logarithmic-derivative quotient only under
  `rho ≤ a < 1`, which implies `rho < 1` and hence `rho² - 1 ≠ 0`; when
  `rho = 1`, the desired conclusion `rho > a` follows directly from `a < 1`
  and no quotient is invoked.  The Lean quotient lemma and its callers carry
  the same guard.
- Lines 1682–1755 state the direct endpoint calculation.  At `rho = 1`,
  `b = (L+1)/L`, `Q_b = L⁻²`, and
  `N = Upsilon(1+omega_L) + 2(1+omega_L)Delta_omega/L² ×
  (2L²+1)/6`; the first term and the displayed correction are both positive.
  This is also the endpoint case used in Lean, with no continuity shortcut.
- Lines 1937–1973 derive explicitly
  `c < 2a sin(theta_L-Delta_L) < 2 sqrt(a) sin(theta_L-Delta_L)`, including
  the use of `0 < a < 1` in the second inequality.  The same weakening is
  present in the formal proof.
- Lines 1881–1892 derive positivity of the ratio from `D_L > 1`,
  `rho > rho_ref > omega_L`, `omega_L > 1/2`, and hence
  `rho+omega_L > 2omega_L > 1 > 1-omega_L > 0`.  These are also explicit
  inputs to the Lean positivity proof.
- Lines 1841–1848 establish positivity of the radicand from `a > 0`,
  `Delta_omega > 0`, `rho+omega_L > 0`, and `zeta+omega_L > 0`, and define
  `x_* > 0` as its positive square root before displaying its square identity.
  `OddCentralLowerFolded` makes the same branch choice and proves both
  positivity and the square identity.

These are absorbed, checked proof-expansion repairs, not changes to
`lem:mesh` or `thm:main`.  Final validation of both assembled results is
recorded in `STATUS.md`.
