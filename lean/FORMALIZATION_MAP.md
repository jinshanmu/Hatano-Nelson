# ELA proof-to-Lean map

Current source: `../ELA/ela_pseudospectral_topology.tex`

The canonical nonnormal proof is inherited from the earlier LAA draft.  The
first table records the new ELA abstraction and complex-Toeplitz extension;
the second retains the detailed canonical proof map.  Intermediate algebraic
displays are discharged inside the listed kernel-checked endpoints.

## ELA abstraction and complex-Toeplitz extension

| ELA result or label | Principal Lean endpoint(s) | Module(s) | Coverage |
|---|---|---|---|
| Matrix family, Eq. `eq:A-matrix` | `complexToeplitzMatrix`, `complexToeplitzMatrix_apply` | `ComplexToeplitz` | Exact definition and entry formula |
| Vertical contraction, Eq. `eq:abstract-vertical-property` | `VerticalScalingClosed`, `verticalScale_mem_connectedComponentIn` | `VerticalTopology` | Exact strict-sublevel-set formulation |
| Backward-error identity, Eq. `eq:backward-error-abstract` | `generalPseudospectralHeight_isLeast_spectralBackwardErrors` | `BackwardError` | Exact attained minimum for arbitrary finite complex matrices |
| Component lemma, Lem. `lem:component` | `exists_mem_spectrum_mem_pseudospectral_component` | `PseudospectralComponents` | Exact arbitrary finite-matrix statement |
| Abstract barrier, Eq. `eq:abstract-barrier` | `generalRealIntervalBarrier`, `exists_generalPseudospectralHeight_eq_generalRealIntervalBarrier`, `realInterval_mapsTo_generalPseudospectrum_iff_barrier_lt` | `AbstractPseudospectralTopology` | Exact attained compact-interval maximum and strict-sublevel equivalence |
| Vertical topology theorem, Thm. `thm:vertical-topology`, Eq. `eq:abstract-connectedness` | `generalPseudospectrum_vertical_topology_with_barrier`, assembled from `generalPseudospectrum_vertical_topology`, `isConnected_iff_realInterval_mapsTo_of_verticalScaling`, `contractibleSpace_connectedComponentIn_of_verticalScaling`, and `exists_mem_spectrum_mem_pseudospectral_component` | `AbstractPseudospectralTopology`, `VerticalTopology`, `PseudospectralComponents` | Exact component-contractibility and both connectedness equivalences with explicit real spectral endpoints; the endpoint parameters replace a particular min/max representation of Mathlib's abstract algebra spectrum |
| Complex affine invariance used in Prop. `prop:complex-reduction` | `generalPseudospectrum_complexAffine`, `generalPseudospectrum_unitary_conjugate` | `ComplexToeplitz` | Exact for every nonzero complex affine scale and every unitary similarity |
| Phase removal, Eq. `eq:complex-unitary-reduction` | `complexToeplitzMatrix_phase_reduction`, `complexToeplitzMatrix_phase_reduction_eq_canonical_or_reversal` | `ComplexToeplitz` | Exact whenever `alpha != 0 or beta != 0`, including the one-sided endpoint `a=0`, with reversal in the opposite orientation |
| Pseudospectral reduction, Eq. `eq:complex-pseudospectrum-reduction` | `complexToeplitzPseudospectrum_eq_affine_image` | `ComplexToeplitz` | Exact whenever the overall scale is nonzero, including `a=0` and `a=1` |
| Scalar part of Prop. `prop:boundary-cases` | `generalPseudospectralHeight_complexToeplitzMatrix_zero_zero`, `generalPseudospectrum_complexToeplitzMatrix_zero_zero` | `ComplexToeplitz` | Exact open disk |
| One-sided part of Prop. `prop:boundary-cases` | `generalPseudospectralHeight_left_zero_rotation`, `generalPseudospectralHeight_right_zero_rotation`, `exists_eq_ball_complexToeplitzPseudospectrum_of_left_zero`, `exists_eq_ball_complexToeplitzPseudospectrum_of_right_zero`, `contractibleSpace_complexToeplitzPseudospectrum_of_mul_eq_zero` | `ComplexToeplitz`, `RadialTopology`, `JordanBoundary` | Exact rotation invariance, open-disk identification, connectedness, and contractibility in both one-sided orientations, including the scalar overlap |
| Normal scalar, Eqs. `eq:normal-threshold`, `eq:normal-error-bound`, `eq:normal-asymptotic` | `normalThreshold`, `normalThreshold_even`, `normalThreshold_odd`, `normalThreshold_succ_lt`, `normalThreshold_error_bound`, `normalThreshold_cubic_remainder` | `BoundaryCases`, `NormalCriticalThreshold` | Exact parity formula, strict adjacent-dimension decrease, the displayed two-sided cubic error bound, and its absolute-remainder form |
| Normal half-gap and Eq. `eq:normal-connectedness` for `A_n(1)` | `normalAdjacentHalfGap_le_normalThreshold`, `exists_normalAdjacentHalfGap_eq_normalThreshold`, `pseudospectrum_one_eq_iUnion_balls`, `isConnected_pseudospectrum_one_iff_normalThreshold_lt`, `contractibleSpace_pseudospectrum_one_component` | `NormalGapGeometry`, `NormalBoundary`, `NormalToeplitzBoundary` | Exact largest adjacent half-gap, union-of-open-disks formula, strict connectedness threshold (including equality failure), and contractibility of every component |
| Equal-modulus normal reduction and Eqs. `eq:normal-connectedness`, `eq:full-connectedness` | `complexToeplitzPseudospectrum_eq_normal_affine_image`, `complexToeplitz_normal_corollary` | `ComplexToeplitz`, `NormalToeplitzBoundary` | Exact affine transfer to every complex equal-nonzero-modulus Toeplitz matrix, including component contractibility and threshold `epsilon > norm alpha * normalThreshold n` |
| Normal critical dimension, Eq. `eq:general-normal-critical` | `normalCriticalThreshold`, `normalCriticalThreshold_isLeast`, `normalCriticalThreshold_predecessor_ge`, `normalCriticalThreshold_scale_bounds`, `normalCriticalThreshold_error_lt_two`, `normalCriticalThreshold_boundedErrorAtZero`, `complexToeplitz_normal_connectedDimensions_eq_normalCriticalSet`, `complexToeplitz_normal_firstConnectedDimension_isLeast` | `NormalCriticalThreshold`, `NormalToeplitzBoundary` | Exact equality between matrix-connected dimensions and the scalar critical set, the literal first-connected-dimension specification, and the stronger estimate `|N-pi*c/epsilon|<2` for `0<epsilon<=c`, hence `pi*c/epsilon+O(1)` |
| Full threshold and critical size, Eq. `eq:full-threshold` and the definition of `N_T` | `complexToeplitzThreshold`, `complexToeplitzCriticalSize`, `complexToeplitz_firstConnectedDimension_isLeast` | `FullFamilyMain` | Exact piecewise definitions and literal first-connected-dimension specification in all three regimes |
| Full complex classification, Thm. `thm:main`, Eqs. `eq:full-connectedness`, `eq:general-nonnormal-critical`, `eq:general-normal-critical` | `complexToeplitz_main_theorem`, with `complexToeplitz_classification_at_size`, `complexToeplitzThreshold_succ_lt_of_mul_ne_zero`, `tendsto_complexToeplitzThreshold_atTop_zero`, `complexToeplitz_connectedDimensions_eq_criticalSize_tail`, `criticalThreshold_div_boundedErrorAtZero_scaled`, and the two `complexToeplitzCriticalSize_boundedErrorAtZero_of_norm_*` endpoints | `FullFamilyMain`, `ComplexToeplitz`, `NormalToeplitzBoundary` | Exact three-branch assembly: component contractibility, strict threshold criterion, irreducible strict decrease, decay, persistence, literal first order, exact scaled nonnormal bounded error, normal bounded error, and zero-product critical order two |

## Canonical nonnormal proof

| Canonical ELA result or proof stage | Principal Lean endpoint(s) | Module(s) |
|---|---|---|
| Matrix, gauge similarity, and real spectrum | `pathMatrix_eq_gauge_symmetricPath_mul_inv`, `spectrum_pathMatrix`, `charpoly_pathMatrix_separable` | `PathSpectrum`, `Spectrum` |
| Least singular value and gap barrier | `leastSingularValue_eq_zero_iff_det_eq_zero`, `exists_realGapValue_eq_gapBarrier` | `LeastSingular`, `Definitions` |
| Pointwise backward-error identity, Eq. `eq:backward-error-abstract`, specialized to the canonical path | `generalPseudospectralHeight_isLeast_spectralBackwardErrors`, `realGapValue_isLeast_spectralBackwardErrors` | `BackwardError` |
| Vertical determinant certificate, Prop. `prop:vertical-determinant-certificate` | `hasDerivWithinAt_verticalPencilDet_pos` | `VerticalGenerating`, `VerticalRatio` |
| Vertical monotonicity, Lem. `lem:vertical` | `verticalHeightMonotone` | `VerticalContinuation` |
| Component lemma, Lem. `lem:component`, and its topological consequences | `exists_mem_spectrum_mem_pseudospectral_component`, `contractibleSpace_pathPseudospectral_component`, `isConnected_pathPseudospectrum_iff_gapBarrier_lt` | `PseudospectralComponents`, `ComponentTopology`, `ConnectednessCriterion`, `PathTopologyFinal` |
| Middle signed branch, Lem. `lem:middle-branch` | `exists_signedPencil_root_abs_eq_pseudospectralHeight`, `selectedMiddleRoot_eq_negOnePow_mul_height` | `SignedPencil`, `MiddleBranchSelection`, `MiddleBranchBridge` |
| Folded continuants and collision convention | `signedPencilDet_even_eq_foldEvenSequence`, `signedPencilDet_odd_eq_foldOddSequence`, `foldEvenSequence_eq_deriv_at_foldXi_collision`, `foldOddSequence_eq_deriv_at_foldXi_collision` | `FoldedTransfer`, `FoldedGenerating`, `FoldedChebyshev`, `FoldedExactCollision` |
| Chord-sheet exhaustion, Lem. `lem:chord-sheet-exhaustion` | `middleBranchClassifiedInGap_eq_univ`, `EvenCentralHalfGapData.classifiedInGap_eq_univ`, `exists_outerChordFamily_representation_of_classified`, `realGapValue_outerChordFamilyX_eq_outerChordFamilyS` | `ChordFamilyExhaustion`, `EvenCentralContinuation`, `OuterSolutionContinuity` |
| Noncentral gap comparison, Lem. `lem:noncentral-gap-comparison` | `exists_predecessorGapPoint_strict_of_mem_successorGap`, `exists_predecessorReflectedGapPoint_strict_of_mem_successorGap` | `NoncentralGapComparison`, `NoncentralReflectedComparison` |
| Central-gap comparison, Lem. `lem:central-gap-comparison` | `oddCentralHeight_lt_centralBidiagonalHeight`, `centralBidiagonalHeight_succ_lt_oddCentralHeight` | `OddCentralUpperComparison`, `OddCentralLowerComparison`, `OddCentralLowerScalar` |
| Strict barrier comparison, Lem. `lem:mesh` | `meshGapHeight_succ_lt_gapBarrier`, `gapBarrier_succ_lt` | `MeshStrictComparison` |
| Sharp-order gap bounds, Prop. `prop:gap-bounds` | `lowerBarrier_le_gapBarrier`, `gapBarrier_le_upperBarrier`, `lowerBarrierOrderConstant_mul_tailModel_le_lowerBarrier` | `RectangularPrincipalAngle`, `GapUpperBound`, `LowerBarrierOrder` |
| Elementary threshold inversion | `tailThreshold_logarithmic_bounds`, `tailThreshold_boundedErrorAtZero`, `tailThreshold_mul_boundedErrorAtZero` | `TailThresholdAsymptotic` |
| Canonical theorem, Thm. `thm:canonical-main` | `main_theorem`, with `connectedDimensions_eq_criticalThreshold_tail`, `criticalThreshold_hasCriticalSizeAsymptotic`, and `criticalThreshold_eq_two_iff` as named endpoints | `MainTheorem`, `CriticalThreshold`, `DimensionTwo` |
| Historical positive-real specialization retained internally | `positiveToeplitzPseudospectrum_eq_affine_image`, `positiveToeplitz_corollary`, `positiveToeplitz_scaled_barrier_succ_lt`, `positiveToeplitz_scaled_barrier_bounds`, `positiveToeplitz_connectedDimensions_eq_criticalThreshold_tail`, `positiveToeplitz_firstConnectedDimension_isLeast`, `positiveToeplitz_threshold_bounds_and_asymptotic` | `GeneralToeplitz` |

## Internal threshold representation

The paper now introduces only `N_c`.  Lean represents it by
`criticalThreshold = firstHitThreshold`; the internal `eventualThreshold`
definition is retained solely to state and prove persistence as an equality
of candidate sets.  The paper's explicit identity
`{n : ℕ | 2 ≤ n ∧ IsConnected (pseudospectrum n a ε)} =
{n : ℕ | criticalThreshold a ε ≤ n}` is the theorem
`connectedDimensions_eq_criticalThreshold_tail` and is also a conjunct of
`main_theorem`.

## Scope boundary

The backward-error perturbation minimum, abstract vertical-topology theorem,
and complex affine Toeplitz reduction have standalone kernel theorems.  They
are logically independent of the canonical `main_theorem`.  The full-family
assembly is `complexToeplitz_main_theorem`; its exact affine-image input
transfers the canonical conclusions by the substitution
`epsilon -> epsilon / c` in the nonnormal regime.

All theorem-bearing boundary assertions in `prop:boundary-cases` and the
normal clause of `eq:general-normal-critical` now have named kernel endpoints:
the Jordan disk and contractibility, the actual normal connectedness
threshold, the explicit cubic remainder, and the bounded-error inversion.
The scalar critical-threshold definition is exactly the least `n >= 2` with
`c * normalThreshold n < epsilon`; `complexToeplitz_normal_corollary`
identifies that predicate with connectedness for the matrix family.

Numerical figures, bibliographic claims, and the physical Discussion contain
no proof obligations and remain outside the kernel scope.
