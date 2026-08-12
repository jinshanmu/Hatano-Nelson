import ConnectedPseudospectrum.Definitions

/-!
# The exact two-dimensional barrier

This module formalizes the final explicit calculation in the proof of
`thm:canonical-main`: for `0 < a < 1`, the real gap barrier of the two-site path is
exactly `a`.
-/

namespace ConnectedPseudospectrum

open Matrix Set
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- In dimension two the spectral radius is `√a`. -/
@[simp] theorem spectralRadius_two (a : ℝ) :
    spectralRadius 2 a = Real.sqrt a := by
  norm_num [spectralRadius, pathRate, Real.cos_pi_div_three]
  ring

/-- The unnormalized two-dimensional pseudoeigenvector used for the upper
bound. -/
def dimensionTwoTestVector (x : ℝ) : ComplexEuclidean 2 :=
  !₂[(1 : ℂ), (x : ℂ)]

@[simp] theorem dimensionTwoTestVector_ne_zero (x : ℝ) :
    dimensionTwoTestVector x ≠ 0 := by
  intro h
  have h0 := congr_arg (fun v : ComplexEuclidean 2 => v (0 : Fin 2)) h
  simp [dimensionTwoTestVector] at h0

/-- The normalized two-dimensional pseudoeigenvector. -/
def dimensionTwoUnitVector (x : ℝ) : ComplexEuclidean 2 :=
  (‖dimensionTwoTestVector x‖⁻¹ : ℂ) • dimensionTwoTestVector x

@[simp] theorem norm_dimensionTwoUnitVector (x : ℝ) :
    ‖dimensionTwoUnitVector x‖ = 1 := by
  exact norm_smul_inv_norm (dimensionTwoTestVector_ne_zero x)

/-- Direct multiplication by the shifted two-site path matrix on the test
vector. -/
theorem shiftedPathMatrix_two_testVector (a x : ℝ) :
    matrixOperator (shiftedPathMatrix 2 a x) (dimensionTwoTestVector x) =
      !₂[(0 : ℂ), ((x ^ 2 - a : ℝ) : ℂ)] := by
  change matrixOperator (shiftedPathMatrix 2 a x)
      (WithLp.toLp 2 ![(1 : ℂ), (x : ℂ)]) =
    WithLp.toLp 2 ![(0 : ℂ), ((x ^ 2 - a : ℝ) : ℂ)]
  rw [matrixOperator_toLp]
  congr 1
  funext i
  fin_cases i
  · simp [shiftedPathMatrix, complexPathMatrix, pathMatrix_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [shiftedPathMatrix, complexPathMatrix, pathMatrix_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- The squared norm of the two-site pseudoeigenvector. -/
theorem norm_dimensionTwoTestVector_sq (x : ℝ) :
    ‖dimensionTwoTestVector x‖ ^ 2 = 1 + x ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp [dimensionTwoTestVector, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The first coordinate forces the pseudoeigenvector to have norm at least
one. -/
theorem one_le_norm_dimensionTwoTestVector (x : ℝ) :
    1 ≤ ‖dimensionTwoTestVector x‖ := by
  rw [← sq_le_sq₀ zero_le_one (norm_nonneg _)]
  rw [norm_dimensionTwoTestVector_sq]
  nlinarith [sq_nonneg x]

/-- Membership in the two-site spectral interval is equivalent to the
elementary estimate needed by the pseudoeigenvector calculation. -/
theorem sq_le_a_of_mem_spectralInterval_two {a x : ℝ} (ha : 0 ≤ a)
    (hx : x ∈ spectralInterval 2 a) :
    x ^ 2 ≤ a := by
  rw [spectralInterval, spectralRadius_two, mem_Icc] at hx
  have habs : |x| ≤ Real.sqrt a := abs_le.mpr hx
  have hsquare : |x| ^ 2 ≤ (Real.sqrt a) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg x) (Real.sqrt_nonneg a)).2 habs
  simpa only [sq_abs, Real.sq_sqrt ha] using hsquare

/-- The residual of the test vector has norm `a - x²` on the spectral
interval. -/
theorem norm_shiftedPathMatrix_two_testVector {a x : ℝ}
    (hx : x ^ 2 ≤ a) :
    ‖matrixOperator (shiftedPathMatrix 2 a x) (dimensionTwoTestVector x)‖ =
      a - x ^ 2 := by
  rw [shiftedPathMatrix_two_testVector]
  apply (sq_eq_sq₀ (norm_nonneg _) (sub_nonneg.mpr hx)).mp
  calc
    ‖(!₂[(0 : ℂ), ((x ^ 2 - a : ℝ) : ℂ)] : ComplexEuclidean 2)‖ ^ 2 =
        ‖((x ^ 2 - a : ℝ) : ℂ)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp
    _ = (x ^ 2 - a) ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = (a - x ^ 2) ^ 2 := by ring

/-- The explicit pseudoeigenvector bounds every two-site real gap value by
`a`. -/
theorem realGapValue_two_le_a {a x : ℝ} (ha : 0 ≤ a)
    (hx : x ∈ spectralInterval 2 a) :
    realGapValue 2 a x ≤ a := by
  have hx_sq : x ^ 2 ≤ a := sq_le_a_of_mem_spectralInterval_two ha hx
  unfold realGapValue pseudospectralHeight
  calc
    leastSingularValue (shiftedPathMatrix 2 a x) ≤
        leastSingularValue (shiftedPathMatrix 2 a x) *
          ‖dimensionTwoTestVector x‖ :=
      le_mul_of_one_le_right
        (leastSingularValue_nonneg (shiftedPathMatrix 2 a x))
        (one_le_norm_dimensionTwoTestVector x)
    _ ≤ ‖matrixOperator (shiftedPathMatrix 2 a x)
          (dimensionTwoTestVector x)‖ :=
      leastSingularValue_mul_norm_le_norm_apply
        (shiftedPathMatrix 2 a x) (by norm_num) (dimensionTwoTestVector x)
    _ = a - x ^ 2 := norm_shiftedPathMatrix_two_testVector hx_sq
    _ ≤ a := sub_le_self a (sq_nonneg x)

/-- First coordinate of the shifted two-site matrix at the central point. -/
theorem shiftedPathMatrix_two_zero_coord_zero (a : ℝ)
    (v : ComplexEuclidean 2) :
    matrixOperator (shiftedPathMatrix 2 a 0) v (0 : Fin 2) = -v (1 : Fin 2) := by
  change ((shiftedPathMatrix 2 a 0).mulVec (WithLp.ofLp v)) (0 : Fin 2) =
    -v (1 : Fin 2)
  simp [shiftedPathMatrix, complexPathMatrix, pathMatrix_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Second coordinate of the shifted two-site matrix at the central point. -/
theorem shiftedPathMatrix_two_zero_coord_one (a : ℝ)
    (v : ComplexEuclidean 2) :
    matrixOperator (shiftedPathMatrix 2 a 0) v (1 : Fin 2) =
      -(a : ℂ) * v (0 : Fin 2) := by
  change ((shiftedPathMatrix 2 a 0).mulVec (WithLp.ofLp v)) (1 : Fin 2) =
    -(a : ℂ) * v (0 : Fin 2)
  simp [shiftedPathMatrix, complexPathMatrix, pathMatrix_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- At the central point the shifted two-site matrix expands every vector by
at least the factor `a`, provided `0 ≤ a ≤ 1`. -/
theorem a_mul_norm_le_norm_shiftedPathMatrix_two_zero {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (v : ComplexEuclidean 2) :
    a * ‖v‖ ≤ ‖matrixOperator (shiftedPathMatrix 2 a 0) v‖ := by
  have ha_sq : a ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (by linarith : 0 ≤ 1 + a)]
  have hnorm_sq :
      ‖matrixOperator (shiftedPathMatrix 2 a 0) v‖ ^ 2 =
        ‖v (1 : Fin 2)‖ ^ 2 + a ^ 2 * ‖v (0 : Fin 2)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
      shiftedPathMatrix_two_zero_coord_zero,
      shiftedPathMatrix_two_zero_coord_one]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0]
    ring
  apply (sq_le_sq₀ (mul_nonneg ha0 (norm_nonneg v)) (norm_nonneg _)).mp
  calc
    (a * ‖v‖) ^ 2 =
        a ^ 2 * (‖v (0 : Fin 2)‖ ^ 2 + ‖v (1 : Fin 2)‖ ^ 2) := by
      rw [mul_pow, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    _ ≤ ‖v (1 : Fin 2)‖ ^ 2 + a ^ 2 * ‖v (0 : Fin 2)‖ ^ 2 := by
      nlinarith [sq_nonneg ‖v (0 : Fin 2)‖, sq_nonneg ‖v (1 : Fin 2)‖]
    _ = ‖matrixOperator (shiftedPathMatrix 2 a 0) v‖ ^ 2 := hnorm_sq.symm

/-- The least singular value at the central point is bounded below by `a`. -/
theorem a_le_realGapValue_two_zero {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    a ≤ realGapValue 2 a 0 := by
  unfold realGapValue pseudospectralHeight
  rw [leastSingularValue_eq_norm_apply]
  simpa [norm_leastSingularVector (shiftedPathMatrix 2 a 0) (by norm_num)] using
    a_mul_norm_le_norm_shiftedPathMatrix_two_zero ha0 ha1
      (leastSingularVector (shiftedPathMatrix 2 a 0))

/-- Exact central two-site least singular value. -/
theorem realGapValue_two_zero {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    realGapValue 2 a 0 = a := by
  apply le_antisymm
  · exact realGapValue_two_le_a ha0 (zero_mem_spectralInterval 2 a (by norm_num))
  · exact a_le_realGapValue_two_zero ha0 ha1

/-- The exact two-dimensional barrier `γ₂(a) = a`. -/
theorem gapBarrier_two {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    gapBarrier 2 a = a := by
  apply le_antisymm
  · obtain ⟨x, hx, hmax⟩ :=
      exists_realGapValue_eq_gapBarrier 2 a (by norm_num)
    rw [← hmax]
    exact realGapValue_two_le_a ha0 hx
  · calc
      a = realGapValue 2 a 0 := (realGapValue_two_zero ha0 ha1).symm
      _ ≤ gapBarrier 2 a := realGapValue_le_gapBarrier 2 a 0
        (zero_mem_spectralInterval 2 a (by norm_num))

end

end ConnectedPseudospectrum
