import ConnectedPseudospectrum.GeneralPseudospectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Least singular values and inverse operator norms

For an invertible finite complex matrix, this module proves directly from the
attained Euclidean minimum that the operator norm of the inverse is the
reciprocal of the least singular value.  This is the exact bridge from the
strict singular-value definition of pseudospectrum to the resolvent norm in
`lem:component`.
-/

namespace ConnectedPseudospectrum

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- In positive dimension, nonsingularity makes the actual least singular
value strictly positive. -/
theorem leastSingularValue_pos_of_det_ne_zero {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) (hdet : M.det ≠ 0) :
    0 < leastSingularValue M := by
  have hne : leastSingularValue M ≠ 0 := fun h =>
    hdet ((leastSingularValue_eq_zero_iff_det_eq_zero M hn).1 h)
  exact lt_of_le_of_ne (leastSingularValue_nonneg M) (Ne.symm hne)

/-- For an invertible matrix, its Euclidean inverse operator norm is exactly
the reciprocal of its attained least singular value. -/
theorem norm_nonsing_inv_eq_inv_leastSingularValue {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) (hdet : M.det ≠ 0) :
    ‖M⁻¹‖ = (leastSingularValue M)⁻¹ := by
  let s : ℝ := leastSingularValue M
  have hs : 0 < s := leastSingularValue_pos_of_det_ne_zero M hn hdet
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  apply le_antisymm
  · rw [← norm_matrixOperator]
    apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hs.le)
    intro v
    have hlower := leastSingularValue_mul_norm_le_norm_apply M hn
      (matrixOperator M⁻¹ v)
    have hcancel : matrixOperator M (matrixOperator M⁻¹ v) = v := by
      calc
        matrixOperator M (matrixOperator M⁻¹ v) =
            matrixOperator (M * M⁻¹) v := by simp [matrixOperator]
        _ = v := by rw [M.mul_nonsing_inv hunit]; simp [matrixOperator]
    rw [hcancel] at hlower
    change ‖matrixOperator M⁻¹ v‖ ≤ s⁻¹ * ‖v‖
    rw [inv_mul_eq_div]
    apply (le_div_iff₀ hs).2
    simpa only [mul_comm] using hlower
  · let u := leastSingularVector M
    let w : ComplexEuclidean n := ((s⁻¹ : ℝ) : ℂ) • matrixOperator M u
    have hu : ‖u‖ = 1 := norm_leastSingularVector M hn
    have hMu : ‖matrixOperator M u‖ = s := by
      rfl
    have hw : ‖w‖ = 1 := by
      change ‖((s⁻¹ : ℝ) : ℂ) • matrixOperator M u‖ = 1
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hs), hMu]
      exact inv_mul_cancel₀ hs.ne'
    have hcancel : matrixOperator M⁻¹ (matrixOperator M u) = u := by
      calc
        matrixOperator M⁻¹ (matrixOperator M u) =
            matrixOperator (M⁻¹ * M) u := by simp [matrixOperator]
        _ = u := by rw [M.nonsing_inv_mul hunit]; simp [matrixOperator]
    have hinvw : matrixOperator M⁻¹ w = ((s⁻¹ : ℝ) : ℂ) • u := by
      change matrixOperator M⁻¹
          (((s⁻¹ : ℝ) : ℂ) • matrixOperator M u) =
        ((s⁻¹ : ℝ) : ℂ) • u
      rw [map_smul, hcancel]
    have hinvnorm : ‖matrixOperator M⁻¹ w‖ = s⁻¹ := by
      rw [hinvw, norm_smul, hu, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
    have hop := (matrixOperator M⁻¹).le_opNorm w
    rw [hw, mul_one, hinvnorm, norm_matrixOperator] at hop
    exact hop

/-- Resolvent norm form of the least-singular-value identity. -/
theorem norm_generalShift_inv_eq_inv_height {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) (z : ℂ)
    (hdet : (generalShift M z).det ≠ 0) :
    ‖(generalShift M z)⁻¹‖ = (generalPseudospectralHeight M z)⁻¹ := by
  exact norm_nonsing_inv_eq_inv_leastSingularValue (generalShift M z) hn hdet

/-- Membership form of the standard spectrum--resolvent--least-singular-value
description of a positive strict pseudospectrum. -/
theorem mem_generalPseudospectrum_iff_mem_spectrum_or_norm_inv_gt
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (z : ℂ) :
    z ∈ generalPseudospectrum M epsilon ↔
      z ∈ spectrum ℂ M ∨ ‖(generalShift M z)⁻¹‖ > epsilon⁻¹ := by
  by_cases hspectrum : z ∈ spectrum ℂ M
  · constructor
    · intro _
      exact Or.inl hspectrum
    · intro _
      exact mem_generalPseudospectrum_of_mem_spectrum M hn hepsilon hspectrum
  · have hdet : (generalShift M z).det ≠ 0 := by
      intro hzero
      exact hspectrum ((mem_spectrum_iff_det_generalShift_eq_zero M z).2 hzero)
    have hheight : 0 < generalPseudospectralHeight M z :=
      leastSingularValue_pos_of_det_ne_zero (generalShift M z) hn hdet
    constructor
    · intro hz
      right
      rw [norm_generalShift_inv_eq_inv_height M hn z hdet]
      exact (inv_lt_inv₀ hepsilon hheight).2 hz
    · rintro (hz | hz)
      · exact (hspectrum hz).elim
      · rw [norm_generalShift_inv_eq_inv_height M hn z hdet] at hz
        exact (inv_lt_inv₀ hepsilon hheight).1 hz

/-- Set form of `eq:intro-pseudospectrum` for every positive-dimensional
finite complex matrix and every positive strict tolerance. -/
theorem generalPseudospectrum_eq_spectrum_union_resolvent
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    generalPseudospectrum M epsilon =
      spectrum ℂ M ∪ {z | ‖(generalShift M z)⁻¹‖ > epsilon⁻¹} := by
  ext z
  exact mem_generalPseudospectrum_iff_mem_spectrum_or_norm_inv_gt
    M hn hepsilon z

end

end ConnectedPseudospectrum
