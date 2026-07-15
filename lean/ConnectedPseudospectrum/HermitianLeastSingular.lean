import ConnectedPseudospectrum.LeastSingular

/-!
# A Hermitian criterion for the least singular value

The Gram shift `Mᴴ M - t² I` is positive definite exactly below the actual
Euclidean least singular value.  The proof here is through the quadratic form
and the attained minimizing vector, rather than through an assumed singular-
value or Hermitian-eigenvalue API.
-/

namespace ConnectedPseudospectrum

open Matrix
open scoped ComplexOrder

noncomputable section

/-- The Hermitian Gram shift `Mᴴ M - t² I`. -/
def gramShift {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Mᴴ * M - ((t ^ 2 : ℝ) : ℂ) • 1

/-- The standard Hermitian square norm of a coordinate vector agrees with
the Euclidean norm after equipping the vector with its `ℓ²` norm. -/
theorem star_dotProduct_self_eq_norm_toLp_sq {n : ℕ} (x : Fin n → ℂ) :
    star x ⬝ᵥ x = ((‖WithLp.toLp 2 x‖ ^ 2 : ℝ) : ℂ) := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp]
  simp

/-- The Gram shift is Hermitian. -/
theorem gramShift_isHermitian {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    (gramShift M t).IsHermitian := by
  apply (isHermitian_conjTranspose_mul_self M).sub
  rw [Matrix.IsHermitian]
  simp

/-- Exact quadratic-form identity for the Gram shift.  Both sides live in
`ℂ`; the right side displays explicitly that the value is the coercion of a
real number. -/
theorem star_dotProduct_gramShift_mulVec {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (x : Fin n → ℂ) :
    star x ⬝ᵥ (gramShift M t *ᵥ x) =
      ((‖matrixOperator M (WithLp.toLp 2 x)‖ ^ 2 -
          t ^ 2 * ‖WithLp.toLp 2 x‖ ^ 2 : ℝ) : ℂ) := by
  have hMx := star_dotProduct_self_eq_norm_toLp_sq (M *ᵥ x)
  have hx := star_dotProduct_self_eq_norm_toLp_sq x
  rw [gramShift, sub_mulVec, dotProduct_sub, ← mulVec_mulVec,
    dotProduct_mulVec, vecMul_conjTranspose, star_star, smul_mulVec,
    one_mulVec, dotProduct_smul, hMx, hx]
  simp

/-- For nonnegative `t`, the Gram shift is positive definite exactly when
`t` lies strictly below the attained Euclidean least singular value. -/
theorem gramShift_posDef_iff_lt_leastSingularValue {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) (t : ℝ) (ht : 0 ≤ t) :
    (gramShift M t).PosDef ↔ t < leastSingularValue M := by
  constructor
  · intro hpos
    let v := leastSingularVector M
    have hvnorm : ‖v‖ = 1 := norm_leastSingularVector M hn
    have hvne : WithLp.ofLp v ≠ 0 := by
      intro hvzero
      have : v = 0 := by
        simpa only [WithLp.ofLp_eq_zero] using hvzero
      rw [this, norm_zero] at hvnorm
      norm_num at hvnorm
    have hquad := (Matrix.posDef_iff_dotProduct_mulVec.mp hpos).2 hvne
    rw [star_dotProduct_gramShift_mulVec] at hquad
    have hreal :
        0 < ‖matrixOperator M v‖ ^ 2 - t ^ 2 * ‖v‖ ^ 2 := by
      exact_mod_cast hquad
    have hsnonneg : 0 ≤ leastSingularValue M := leastSingularValue_nonneg M
    have hreal' : 0 < leastSingularValue M ^ 2 - t ^ 2 := by
      simpa [leastSingularValue, v, hvnorm] using hreal
    nlinarith
  · intro hlt
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    refine ⟨gramShift_isHermitian M t, ?_⟩
    intro x hx
    let v : ComplexEuclidean n := WithLp.toLp 2 x
    have hvne : v ≠ 0 := by
      simpa [v] using hx
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    have hscaled :
        t * ‖v‖ < leastSingularValue M * ‖v‖ :=
      mul_lt_mul_of_pos_right hlt hvnorm
    have hlower :
        leastSingularValue M * ‖v‖ ≤ ‖matrixOperator M v‖ :=
      leastSingularValue_mul_norm_le_norm_apply M hn v
    have hstrict : t * ‖v‖ < ‖matrixOperator M v‖ :=
      hscaled.trans_le hlower
    have htproduct : 0 ≤ t * ‖v‖ := mul_nonneg ht hvnorm.le
    have hnormimage : 0 ≤ ‖matrixOperator M v‖ := norm_nonneg _
    have hreal :
        0 < ‖matrixOperator M v‖ ^ 2 - t ^ 2 * ‖v‖ ^ 2 := by
      nlinarith
    rw [star_dotProduct_gramShift_mulVec]
    exact_mod_cast hreal

/-- At the least singular value itself, the Gram shift is positive
semidefinite.  Its quadratic form vanishes on an attained minimizing unit
vector. -/
theorem gramShift_leastSingularValue_posSemidef {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    (gramShift M (leastSingularValue M)).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨gramShift_isHermitian M (leastSingularValue M), ?_⟩
  intro x
  let v : ComplexEuclidean n := WithLp.toLp 2 x
  have hlower :
      leastSingularValue M * ‖v‖ ≤ ‖matrixOperator M v‖ :=
    leastSingularValue_mul_norm_le_norm_apply M hn v
  have hsproduct : 0 ≤ leastSingularValue M * ‖v‖ :=
    mul_nonneg (leastSingularValue_nonneg M) (norm_nonneg v)
  have hnormimage : 0 ≤ ‖matrixOperator M v‖ := norm_nonneg _
  have hreal :
      0 ≤ ‖matrixOperator M v‖ ^ 2 -
        leastSingularValue M ^ 2 * ‖v‖ ^ 2 := by
    nlinarith
  rw [star_dotProduct_gramShift_mulVec]
  exact_mod_cast hreal

end

end ConnectedPseudospectrum
