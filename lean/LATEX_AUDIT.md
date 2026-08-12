# ELA statement and proof alignment

Audited source: `../ELA/ela_pseudospectral_topology.tex`

## Main dependency chain

The canonical nonnormal part of the ELA proof and the Lean assembly use the
same sequence:

1. vertical least-singular-value monotonicity;
2. deformation to the real axis and the exact connectedness criterion;
3. signed-pencil selection of the least-modulus middle branch;
4. folded Chebyshev and endpoint-side chord classification;
5. noncentral and central gap comparisons;
6. strict adjacent-size decrease of the global barrier;
7. rectangular two-sided barrier estimates;
8. elementary logarithmic inversion of the tail model; and
9. the exact order-two endpoint.

No assumption in `ConnectedPseudospectrum.main_theorem` exceeds the canonical
hypotheses `0<a<1` and `epsilon>0`.

## ELA abstraction and complex family

`VerticalTopology.lean` separates the set-theoretic input
`VerticalScalingClosed` from the spectral input.  The public theorem
`isConnected_iff_realInterval_mapsTo_of_verticalScaling` proves the real-axis
interval criterion from explicit endpoints and a real component anchor, while
`contractibleSpace_connectedComponentIn_of_verticalScaling` packages the
component contraction.  `PseudospectralComponents.lean` supplies the required
spectral anchor for arbitrary finite matrices.

`ComplexToeplitz.lean` defines `tridiag(alpha,d,beta)` over `Complex`, proves
the diagonal-unitary phase gauge entry by entry, and transports the complete
strict pseudospectrum through unitary similarity, translation, rotation, and
positive scaling.  The exact reduction includes the one-sided `a=0` endpoint.
For two nonzero unequal-modulus off-diagonals it transfers
component contractibility, the exact connectedness threshold, and strict
adjacent-size barrier decrease from `main_theorem`.  Equal nonzero moduli are
reduced exactly to the Hermitian endpoint `a=1`.  On the zero-product boundary,
triangular determinant formulas prove the singleton spectrum and connectedness
at every positive level; the double-zero case is identified exactly with an
open disk.  `RadialTopology.lean` classifies every bounded open connected
rotation-invariant planar set as an open ball and proves its contractibility;
`JordanBoundary.lean` supplies the matrix-specific rotations and packages the
exact one-sided disks.  `NormalBoundary.lean`, `NormalGapGeometry.lean`, and
`NormalToeplitzBoundary.lean` give the exact union-of-disks formula, identify
the largest half-gap with the parity formula `eta_n`, prove the strict normal
connectedness threshold, and transfer component contractibility to equal
complex moduli.  `NormalCriticalThreshold.lean` proves the displayed cubic
error and the stronger uniform estimate `|N-pi*c/epsilon|<2`, which implies
the manuscript's normal `O(1)` critical-order statement.

`FullFamilyMain.lean` defines the literal piecewise `Theta_n` and `N_T`
wrappers and packages all three regimes in `complexToeplitz_main_theorem`.
It proves the exact connected-order tail and `IsLeast` specification, rather
than leaving the complex critical-size conclusions as an informal composition
of branch-specific endpoints.

## Simplifications retained from the canonical version

- The paper defines only the first connected size `N_c`.  Strict barrier
  decrease proves directly that the connected sizes form the tail
  `{n : n >= N_c}`.  This exact set identity is formalized as
  `connectedDimensions_eq_criticalThreshold_tail` and included in
  `main_theorem`; first-hit and eventual sets remain internal order-theoretic
  proof devices.
- The threshold asymptotic is derived directly from
  `beta x - log(x+1) = log(1/t)`.  The unused exact Lambert-`W` floor formula,
  its auxiliary domain condition, and the corresponding Lean module were
  removed.
- Repeated folded formulas and terminal-vector multiplications were kept only
  at the point where they are proved or used.
- The endpoint-side chord-exhaustion lemma now states all outputs consumed by
  the main comparison: bidirectional exhaustion, signed-root magnitude,
  distinct folded variables, and the odd central-half case.
- The diagonal shift in the affine Toeplitz corollary is allowed to be complex;
  the reduction uses translation, positive scaling, and unitary conjugation by
  the reversal permutation, none of which requires a real diagonal shift.

## Standalone corollary and backward-error endpoints

The pointwise norm-minimizing perturbation formula is formalized both in
general form as
`generalPseudospectralHeight_isLeast_spectralBackwardErrors` and in the
paper's path-matrix notation as
`realGapValue_isLeast_spectralBackwardErrors`.  The legacy positive-real
Toeplitz set identity and all of its quantitative consequences remain in
`GeneralToeplitz.lean`.  The ELA-level complex extension is the exact set
identity `complexToeplitzPseudospectrum_eq_affine_image`; its unequal-modulus
topological and strict-comparison consequences are assembled in
`complexToeplitz_corollary` and
`complexToeplitz_scaled_barrier_succ_lt`.  These endpoints use only the
necessary nonzero, unequal-modulus, positive-dimension, and positive-level
hypotheses appearing in the corresponding manuscript clauses.

The figures, references, and physical Discussion are non-theorem material
outside the kernel scope.  They are not used to prove `main_theorem`.

`FORMALIZATION_MAP.md` lists the corresponding Lean endpoints, and
`STATUS.md` records the latest executable validation.
