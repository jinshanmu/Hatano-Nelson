import ConnectedPseudospectrum.CriticalThreshold
import ConnectedPseudospectrum.MeshStrictComparison
import ConnectedPseudospectrum.PathTopologyFinal
import ConnectedPseudospectrum.RectangularPrincipalAngle

/-!
# Main theorem

This module assembles the four clauses of `thm:main` from the proved
topological, mesh-comparison, barrier, threshold, and asymptotic results.
The threshold clause explicitly records nonemptiness of every set whose
minimum is used and the paper's empty-maximum convention.
-/

namespace ConnectedPseudospectrum

open Filter Set

noncomputable section

/-- The complete formal counterpart of `thm:main`.

The connected components are represented pointwise by
`connectedComponentIn`.  The common critical size is
`criticalThreshold = firstHitThreshold`, and the theorem proves that it is
also `eventualThreshold`.  `HasCriticalSizeAsymptotic` is the bounded-error
interpretation of the paper's fixed-parameter `O_a(1)` statement.
-/
theorem main_theorem {a ε : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε) :
    (∀ (n : ℕ), 2 ≤ n → ∀ {z : ℂ},
      z ∈ pseudospectrum n a ε →
        ContractibleSpace (connectedComponentIn (pseudospectrum n a ε) z)) ∧
    ((∀ (n : ℕ), 2 ≤ n →
        gapBarrier (n + 1) a < gapBarrier n a) ∧
      Tendsto (fun n : ℕ => gapBarrier n a) atTop (nhds 0) ∧
      (∀ (n : ℕ), 2 ≤ n →
        (IsConnected (pseudospectrum n a ε) ↔ ε > gapBarrier n a))) ∧
    ((firstHitSet a ε).Nonempty ∧
      (eventualSet a ε).Nonempty ∧
      (upperBarrierCrossingSet a ε).Nonempty ∧
      criticalThreshold a ε = firstHitThreshold a ε ∧
      criticalThreshold a ε = eventualThreshold a ε ∧
      1 + lowerObstructionMaximum a ε ≤ criticalThreshold a ε ∧
      criticalThreshold a ε ≤ upperBarrierThreshold a ε ∧
      (lowerObstructionSet a ε = ∅ →
        lowerObstructionMaximum a ε = 1)) ∧
    (HasCriticalSizeAsymptotic (criticalThreshold a) a ∧
      (criticalThreshold a ε = 2 ↔ ε > a)) := by
  have hcriterionAll :
      ∀ {δ : ℝ}, 0 < δ → ∀ {n : ℕ}, 2 ≤ n →
        (ConnectedAtSize n a δ ↔ gapBarrier n a < δ) := by
    intro δ hδ n hn
    unfold ConnectedAtSize
    exact isConnected_pathPseudospectrum_iff_gapBarrier_lt
      n hn ha0 ha1 hδ
  have hcriterion :
      ∀ {n : ℕ}, 2 ≤ n →
        (ConnectedAtSize n a ε ↔ gapBarrier n a < ε) :=
    hcriterionAll hε
  have hstrict :
      ∀ {n : ℕ}, 2 ≤ n →
        gapBarrier (n + 1) a < gapBarrier n a := by
    intro n hn
    exact gapBarrier_succ_lt n hn ha0 ha1
  have hlower :
      ∀ {n : ℕ}, 2 ≤ n →
        lowerBarrier n a ≤ gapBarrier n a := by
    intro n hn
    exact lowerBarrier_le_gapBarrier n hn ha0 ha1
  have hupper :
      ∀ {n : ℕ}, 2 ≤ n →
        gapBarrier n a ≤ upperBarrier n a := by
    intro n hn
    exact gapBarrier_le_upperBarrier hn a ha0
  obtain ⟨hfirst, hevent, heq, hLowerThreshold, hUpperThreshold⟩ :=
    threshold_equality_and_two_sided_bounds
      ha0 ha1 hε hcriterion hstrict hlower hupper
  have hUpperSet : (upperBarrierCrossingSet a ε).Nonempty :=
    upperBarrierCrossingSet_nonempty ha0 ha1 hε
  constructor
  · intro n hn z hz
    exact contractibleSpace_pathPseudospectral_component
      n hn ha0 ha1 hε hz
  constructor
  · constructor
    · intro n hn
      exact hstrict hn
    constructor
    · exact tendsto_gapBarrier_atTop_zero a ha0 ha1
    · intro n hn
      exact isConnected_pathPseudospectrum_iff_gapBarrier_lt
        n hn ha0 ha1 hε
  constructor
  · constructor
    · exact hfirst
    constructor
    · exact hevent
    constructor
    · exact hUpperSet
    constructor
    · rfl
    constructor
    · simpa only [criticalThreshold] using heq
    constructor
    · simpa only [criticalThreshold] using hLowerThreshold
    constructor
    · simpa only [criticalThreshold] using hUpperThreshold
    · exact lowerObstructionMaximum_eq_one_of_empty
  · constructor
    · exact criticalThreshold_hasCriticalSizeAsymptotic
        ha0 ha1 hcriterionAll hstrict hlower
    · exact criticalThreshold_eq_two_iff ha0 ha1 hε hcriterion

end

end ConnectedPseudospectrum
