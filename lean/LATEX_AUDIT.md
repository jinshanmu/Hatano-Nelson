# LaTeX audit

Audited source:
`SIMAX_submission_bundle/final_connected_pseudospectrum_proof_2026-07-16.tex`

SHA-256:
`6b98b0feacea447775145c06706294be785a1c4b2901788396c0edf1a3e5de5f`

Source size: 2,731 lines; 101,861 bytes.

Last full source review: 2026-07-16.

This file records the formalization-relevant omissions or ambiguities found
during the audit and how they were resolved.  The statement-level and
proof-expansion repairs incorporated in the dated source do not change its
main mathematical results.

Scope disposition: no unresolved defect is known in `thm:main` or its complete
kernel dependency graph.  The source has 100 labels: 90 mathematical (84
equations, four lemmas, one theorem, and one proposition), seven section, and
three figure labels.  `FORMALIZATION_MAP.md` classifies all 90
mathematical labels as literal kernel counterparts: zero are proof-sufficient
and zero are audited-only.  It separately inventories important unnumbered
physical, numerical, and expository claims outside the kernel scope.  The
latest default build and source-safety evidence is recorded in `STATUS.md`.

## Current manuscript-to-Lean alignment

The 2026-07-16 manuscript incorporates the formalization audit's statement-level
repairs:

- The dimensionless logarithmic parametrization and gauge similarity in the
  introduction are intentionally unnumbered.  Their exact identities are
  nevertheless checked by `HyperbolicParameter` and `PathSpectrum`.  The
  dimensional OBC identification, PBC ellipse, full physical mode display, and
  skin-depth display are also intentionally unnumbered, but remain physical
  exposition outside the Lean scope.
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
- `eq:rectangular-min` states the two exact norm inequalities separately: the
  common sharp factor multiplies `‖u‖` and bounds both `‖C_theta u‖` and
  `‖D_theta u‖` from below.  `rectangularC_norm_lower_bound` and
  `rectangularD_norm_lower_bound` prove those literal inequalities with the
  manuscript's hypotheses.
- `eq:ratio-cross` now has the exported exact Lean counterpart
  `vertical_ratio_cross`; its positive denominator conditions are derived from
  positive definiteness rather than left implicit.
- `eq:tail-threshold-Lambert` is literal.  `LambertWThreshold` constructs the
  lower real branch, proves the sharp argument-domain bound, identifies the
  strict permanent tail crossing with the displayed floor, and proves the
  stated lower-branch logarithmic–logarithmic bounded-error expansion.  The
  Lean function is totalized to zero off `[-exp(-1),0)`, but every theorem that
  uses it as `W_{-1}` either carries the natural-domain hypothesis explicitly
  or derives it from its small-parameter hypotheses.

## Physics formula audit

All physics-facing displays in the introduction and conclusion are unnumbered.
Their signs and scalings have been checked against
`A_n(a)=tridiag(a,0,1)` and the stated hopping convention:

- `H_n^OBC=t_L A_n(t_R/t_L)` has superdiagonal `t_L` and subdiagonal `t_R`;
- the periodic symbol is
  `t_L exp(ik)+t_R exp(-ik)=(t_L+t_R)cos k+i(t_L-t_R)sin k`;
- the alternating-sign unitary conjugates `A_n` to `-A_n`, and the displayed
  positive-sign energies and left/right modes follow from the diagonal gauge;
- the amplitude skin depth is `h^(-1)=2/log(1/a)`, while the gauge condition
  number and reciprocal barrier have the stated common exponential rate; and
- the least-singular-value backward-error identity gives the exact cost of
  placing an eigenvalue at `z`, homogeneity gives the last-bridge budget
  `epsilon_*(n)=t_L gamma_n`, and the physical connectedness criterion follows
  with the same strict inequality;
- the bridge scale
  `epsilon_*(n) asymp_a t_L (n+1) exp(-hn)` agrees exactly with its `t_0` and
  skin-depth rewritings, and its inversion states the required limit
  `delta -> 0` explicitly; and
- at `n=2`, `gamma_2=a` gives `epsilon_*(2)=t_R`; cancelling the weaker hopping
  by the displayed rank-one perturbation has norm `t_R`, produces the stated
  defective dimer, and preserves the strict equality-case distinction.

The two unnumbered dimensionless parameter/gauge identities are still checked
in Lean because they support the mathematical proof.  The dimensional,
second-quantized, PBC, mode, skin-depth, and interpretive formulas remain
deliberately outside the kernel scope.  The component-based resolution-class
discussion and comparison with the published crossover notation are also
audited interpretation rather than new Lean claims.

## Connectedness-threshold proof closure

The complete chain has been checked from the actual matrix definitions:
vertical least-singular-value monotonicity gives vertical scaling and the
strict-open connectedness criterion; the noncentral, reflected, and two
central comparisons give the strict successor barrier inequality; the exact
rectangular estimates force barrier convergence and two-sided threshold
bounds; strict decrease identifies first-hit and eventual thresholds; and the
constructed lower Lambert branch proves the exact floor inversion and the
fixed-parameter bounded-error asymptotic.  The dimension-two endpoint is the
actual equality `gamma_2=a`.  `ConnectedPseudospectrum.main_theorem` assembles
these results with only `0<a<1` and `epsilon>0`.

## Numerical certification wording

The numerical discussion in `sec:numerics`, including the qualifications
attached to `fig:transition` and `fig:barriers`, now makes the status explicit.
For a uniform grid of maximum spacing `h`, the 1-Lipschitz property gives
`M_h ≤ gamma_n ≤ M_h + h/2` when `M_h` is formed from exact sampled least
singular values.  The manuscript separately states that the supplied
NumPy/SciPy implementation uses float64 SVD and eigenvalue values without an
enclosure of their roundoff.  It therefore calls the reported margins and
threshold reproducible floating-point checks conditional on those samples,
not validated interval certificates.  The figures distinguish those computed
estimates from the exact analytic bounds, and none of the numerics is used in
`thm:main`.  The current six figure assets were regenerated successfully with
the supplied script in the `wirtinger_calculus` Conda environment; it again
reported `N_c=7`, the exact-bound bracket `6 <= N_c <= 9`, and conclusive
sample/Lipschitz classifications for the displayed sizes.

## Dimension-one endpoint correction in `lem:vertical` (resolved in 2026-07-16)

- Source anchor: the pentadiagonal display following
  `eq:det-derivative-positive` and preceding `eq:D-R-def`.
- Classification: resolved boundary ambiguity; the proof always used the
  correct formula.
- The 2026-07-16 source now states that the displayed diagonal
  `d - 1, d, …, d, d - a²` applies for `n ≥ 2`.  It separately records that,
  for `n = 1`, the first and last coordinates coincide, so both endpoint
  corrections apply to the same entry:

  ```text
  P₁(Y,t) = [d - 1 - a²] = [x² + Y - t²].
  ```

- Why the argument remains valid: the sequential boundary correction in the
  derivation of `eq:D-F-generating` gives `F₁ = D₁ - a² D₀`, which applies both
  corrections and is correct.  The concluding base-case paragraph in
  `lem:vertical` separately handles the derivative.
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

- In the proof of `lem:middle-branch`, immediately after `eq:odd-dilation`, the
  manuscript identifies `spec(A_m)` exactly with the even-indexed eigenvalues
  of `A_(2m+1)` before concluding that `xI_m-A_m` is nonsingular in an open gap
  of the larger path.  The same spectral identification and nonsingularity
  implication are explicit in Lean.
- In the folded-minor derivation culminating in `eq:five-minor-update`, the
  manuscript performs the Schur-complement calculation on the stated dense
  nonsingular set and then invokes polynomial identity to cover singular
  cases.  `FoldedMinorBridge` and `FoldedTransfer` give the complementary Lean
  proof by direct determinant identities, without an inverse or dense-set
  assumption.
- The continuation argument between `eq:outer-level-dominates` and
  `eq:noncentral-domain` spells out both chord-exhaustion directions.  For
  actual gap points, it defines the selected sheet as a relatively open and
  relatively closed subset of the gap and excludes folded-variable collision,
  `y = 0`, `z = cosh h`, inner nodal endpoints, and `z = u_K^max`.  Conversely,
  it uses the continuous reconstructed angle, its exact values at the two
  spectral endpoints, the intermediate value theorem, and uniqueness of the
  endpoint-side outer solution to realize every interior chord parameter.
  Thus this second exhaustion is not attributed to the relative clopen
  argument and does not assume monotonicity of `theta -> x`.  Lean records the
  continuation invariants, boundary exclusions, endpoint data, classification,
  and exhaustion consequences used by this argument.
- The compact-gap discussion immediately before `eq:gamma-def` proves that
  every maximum defining a gap height is attained in the open gap: spectral
  endpoints have height zero, whereas every interior point is nonsingular and
  has strictly positive least singular value.  The closing comparison step of
  `lem:mesh` invokes this observation when choosing the maximizer.  The
  corresponding interiority fact is explicit in Lean.
- In the odd-central argument following `eq:central-chord`, the
  logarithmic-derivative quotient is used only under `rho ≤ a < 1`, which
  implies `rho < 1` and hence `rho² - 1 ≠ 0`; when `rho = 1`, the desired
  conclusion `rho > a` follows directly from `a < 1` and no quotient is
  invoked.  The Lean quotient lemma and its callers carry the same guard.
- In the direct `rho = 1` case of the proof of `eq:N-positive-target`, the
  manuscript calculates that `b = (L+1)/L`, `Q_b = L⁻²`, and
  `N = Upsilon(1+omega_L) + 2(1+omega_L)Delta_omega/L² ×
  (2L²+1)/6`; the first term and the displayed correction are both positive.
  This is also the endpoint case used in Lean, with no continuity shortcut.
- The test-point estimate from `eq:x-c-second-singular` through
  `eq:angle-inequality` derives explicitly
  `c < 2a sin(theta_L-Delta_L) < 2 sqrt(a) sin(theta_L-Delta_L)`, including
  the use of `0 < a < 1` in the second inequality.  The same weakening is
  present in the formal proof.
- In the determinant-product argument between `eq:x-star-central` and
  `eq:q-product-central`, positivity of the ratio is derived from `D_L > 1`,
  `rho > rho_ref > omega_L`, `omega_L > 1/2`, and hence
  `rho+omega_L > 2omega_L > 1 > 1-omega_L > 0`.  These are also explicit
  inputs to the Lean positivity proof.
- At `eq:x-star-central`, the manuscript establishes positivity of the
  radicand from `a > 0`,
  `Delta_omega > 0`, `rho+omega_L > 0`, and `zeta+omega_L > 0`, and defines
  `x_* > 0` as its positive square root before displaying its square identity.
  `OddCentralLowerFolded` makes the same branch choice and proves both
  positivity and the square identity.

These are absorbed, checked proof-expansion repairs, not changes to
`lem:mesh` or `thm:main`.  Final validation of both assembled results is
recorded in `STATUS.md`.
