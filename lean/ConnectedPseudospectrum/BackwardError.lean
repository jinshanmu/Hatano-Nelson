import ConnectedPseudospectrum.GeneralPseudospectrum
import ConnectedPseudospectrum.Definitions

/-!
# Spectral backward error

This module proves the pointwise spectral backward-error identity used in the
ELA manuscript.  For a positive-dimensional complex square matrix, the least
singular value of `zI - M` is the minimum Euclidean operator norm of a
perturbation that makes `z` an eigenvalue.
-/

namespace ConnectedPseudospectrum

open Matrix Set
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The set of norms of perturbations that place `z` in the spectrum of
`M + Δ`. -/
def spectralBackwardErrors {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : Set ℝ :=
  (fun Δ : Matrix (Fin n) (Fin n) ℂ ↦ ‖Δ‖) ''
    {Δ | z ∈ spectrum ℂ (M + Δ)}

/-- The rank-one perturbation determined by a matrix and its selected least
singular vector. -/
def optimalSingularPerturbation {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.toEuclideanLin (n := Fin n) (m := Fin n) (𝕜 := ℂ)).symm
    (InnerProductSpace.rankOne ℂ
      (matrixOperator B (leastSingularVector B))
      (leastSingularVector B)).toLinearMap

theorem matrixOperator_optimalSingularPerturbation {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) :
    matrixOperator (optimalSingularPerturbation B) =
      InnerProductSpace.rankOne ℂ
        (matrixOperator B (leastSingularVector B))
        (leastSingularVector B) := by
  apply ContinuousLinearMap.ext
  intro v
  change Matrix.toEuclideanLin (optimalSingularPerturbation B) v =
    (InnerProductSpace.rankOne ℂ
      (matrixOperator B (leastSingularVector B))
      (leastSingularVector B)).toLinearMap v
  simp [optimalSingularPerturbation]

/-- The optimal rank-one perturbation has norm equal to the least singular
value. -/
theorem norm_optimalSingularPerturbation {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    ‖optimalSingularPerturbation B‖ = leastSingularValue B := by
  rw [← norm_matrixOperator, matrixOperator_optimalSingularPerturbation,
    InnerProductSpace.norm_rankOne, norm_leastSingularVector B hn, mul_one]
  rfl

/-- The selected rank-one perturbation makes the shifted matrix singular. -/
theorem det_sub_optimalSingularPerturbation_eq_zero {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    (B - optimalSingularPerturbation B).det = 0 := by
  apply (exists_unit_kernel_iff_det_eq_zero
    (B - optimalSingularPerturbation B)).1
  let v := leastSingularVector B
  have hv : ‖v‖ = 1 := norm_leastSingularVector B hn
  refine ⟨v, hv, ?_⟩
  rw [matrixOperator_sub, ContinuousLinearMap.sub_apply,
    matrixOperator_optimalSingularPerturbation]
  simp [InnerProductSpace.rankOne_apply, v, hv]

/-- The least singular value is a lower bound for every spectral backward
error. -/
theorem generalPseudospectralHeight_le_of_mem_spectralBackwardErrors
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) (z : ℂ)
    {η : ℝ} (ηη : η ∈ spectralBackwardErrors M z) :
    generalPseudospectralHeight M z ≤ η := by
  rcases ηη with ⟨Δ, hΔ, rfl⟩
  have hdet : (generalShift (M + Δ) z).det = 0 :=
    (mem_spectrum_iff_det_generalShift_eq_zero (M + Δ) z).1 hΔ
  obtain ⟨v, hv, hker⟩ :=
    (exists_unit_kernel_iff_det_eq_zero (generalShift (M + Δ) z)).2 hdet
  have hshift : generalShift (M + Δ) z = generalShift M z - Δ := by
    simp [generalShift, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have haction : matrixOperator (generalShift M z) v = matrixOperator Δ v := by
    rw [hshift, matrixOperator_sub, ContinuousLinearMap.sub_apply] at hker
    exact sub_eq_zero.mp hker
  calc
    generalPseudospectralHeight M z = leastSingularValue (generalShift M z) := rfl
    _ ≤ ‖matrixOperator (generalShift M z) v‖ :=
      leastSingularValue_le (generalShift M z) hn v hv
    _ = ‖matrixOperator Δ v‖ := by rw [haction]
    _ ≤ ‖matrixOperator Δ‖ * ‖v‖ := (matrixOperator Δ).le_opNorm v
    _ = ‖Δ‖ := by rw [norm_matrixOperator, hv, mul_one]

/-- Pointwise spectral backward-error identity: the least singular value of
`zI - M` is the attained minimum norm of a perturbation making `z` an
eigenvalue of `M + Δ`. -/
theorem generalPseudospectralHeight_isLeast_spectralBackwardErrors
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) (z : ℂ) :
    IsLeast (spectralBackwardErrors M z)
      (generalPseudospectralHeight M z) := by
  let B := generalShift M z
  let Δ := optimalSingularPerturbation B
  have hshift : generalShift (M + Δ) z = B - Δ := by
    simp [B, generalShift, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hdet : (generalShift (M + Δ) z).det = 0 := by
    rw [hshift]
    exact det_sub_optimalSingularPerturbation_eq_zero B hn
  have hspectrum : z ∈ spectrum ℂ (M + Δ) :=
    (mem_spectrum_iff_det_generalShift_eq_zero (M + Δ) z).2 hdet
  constructor
  · refine ⟨Δ, hspectrum, ?_⟩
    change ‖Δ‖ = leastSingularValue B
    exact norm_optimalSingularPerturbation B hn
  · intro η hη
    exact generalPseudospectralHeight_le_of_mem_spectralBackwardErrors M hn z hη

/-- Path-specific form of the pointwise identity specialized in the ELA
manuscript: `gₙ(x)` is the minimum perturbation norm that makes `x` an
eigenvalue of `Aₙ(a) + Δ`. -/
theorem realGapValue_isLeast_spectralBackwardErrors
    (n : ℕ) (hn : 0 < n) (a x : ℝ) :
    IsLeast (spectralBackwardErrors (complexPathMatrix n a) (x : ℂ))
      (realGapValue n a x) := by
  exact generalPseudospectralHeight_isLeast_spectralBackwardErrors
    (complexPathMatrix n a) hn (x : ℂ)

end

end ConnectedPseudospectrum
