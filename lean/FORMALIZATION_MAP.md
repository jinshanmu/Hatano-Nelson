# LAA proof-to-Lean map

Source: `../LAA/laa_connected_pseudospectra.tex`

This map gives a result-by-result correspondence for every numbered
theorem-like statement in the LAA manuscript and for independently used
displayed claims.  Intermediate algebraic
displays are discharged inside the listed kernel-checked endpoints.

| LAA result or proof stage | Principal Lean endpoint(s) | Module(s) |
|---|---|---|
| Matrix, gauge similarity, and real spectrum | `pathMatrix_eq_gauge_symmetricPath_mul_inv`, `spectrum_pathMatrix`, `charpoly_pathMatrix_separable` | `PathSpectrum`, `Spectrum` |
| Least singular value and gap barrier | `leastSingularValue_eq_zero_iff_det_eq_zero`, `exists_realGapValue_eq_gapBarrier` | `LeastSingular`, `Definitions` |
| Pointwise backward-error identity, Eq. `eq:backward-error-main` | `generalPseudospectralHeight_isLeast_spectralBackwardErrors`, `realGapValue_isLeast_spectralBackwardErrors` | `BackwardError` |
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
| Main theorem, Thm. `thm:main` | `main_theorem`, with `connectedDimensions_eq_criticalThreshold_tail`, `criticalThreshold_hasCriticalSizeAsymptotic`, and `criticalThreshold_eq_two_iff` as named endpoints | `MainTheorem`, `CriticalThreshold`, `DimensionTwo` |
| Positive-off-diagonal Toeplitz corollary, Cor. `cor:general-toeplitz` | `positiveToeplitzPseudospectrum_eq_affine_image`, `positiveToeplitz_corollary`, `positiveToeplitz_scaled_barrier_succ_lt`, `positiveToeplitz_scaled_barrier_bounds`, `positiveToeplitz_connectedDimensions_eq_criticalThreshold_tail`, `positiveToeplitz_firstConnectedDimension_isLeast`, `positiveToeplitz_threshold_bounds_and_asymptotic` | `GeneralToeplitz` |

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

The backward-error perturbation minimum and affine general-Toeplitz corollary
now have standalone kernel theorems.  They are logically independent of
`main_theorem`, while the exact affine-image formula transfers the main
theorem's normalized bounds and asymptotic conclusions by the substitution
`epsilon -> epsilon / c`.  Numerical figures, bibliographic claims, and the
physical Discussion contain no proof obligations and remain outside the
kernel scope.
