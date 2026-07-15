import ConnectedPseudospectrum.ResolventNorm

/-!
# Attainment of the Euclidean matrix operator norm

The component argument needs an actual unit vector maximizing a resolvent
operator norm.  In finite complex Euclidean dimension the unit sphere is
compact, so the maximum is attained.  This module records the choice and its
exact norm identity.
-/

namespace ConnectedPseudospectrum

open Metric Set
open scoped Matrix.Norms.L2Operator

noncomputable section

private theorem exists_unit_maximizer {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    ∃ v : ComplexEuclidean n,
      ‖v‖ = 1 ∧
        ∀ w : ComplexEuclidean n, ‖w‖ = 1 →
          ‖matrixOperator M w‖ ≤ ‖matrixOperator M v‖ := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : ProperSpace (ComplexEuclidean n) :=
    FiniteDimensional.proper_rclike ℂ (ComplexEuclidean n)
  have hsphere : (sphere (0 : ComplexEuclidean n) 1).Nonempty := by
    let i : Fin n := Classical.choice inferInstance
    refine ⟨EuclideanSpace.single i 1, ?_⟩
    exact mem_sphere_zero_iff_norm.mpr (by simp)
  obtain ⟨v, hv, hmax⟩ :=
    (isCompact_sphere (0 : ComplexEuclidean n) 1).exists_isMaxOn hsphere
      (matrixOperator M).continuous.norm.continuousOn
  refine ⟨v, mem_sphere_zero_iff_norm.mp hv, ?_⟩
  intro w hw
  exact hmax (mem_sphere_zero_iff_norm.mpr hw)

/-- A selected unit vector attaining the Euclidean operator norm.  In
dimension zero it is the unique zero vector. -/
def operatorNormVector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ComplexEuclidean n :=
  if hn : 0 < n then Classical.choose (exists_unit_maximizer M hn) else 0

/-- The selected maximizing vector is a unit vector in positive dimension. -/
theorem norm_operatorNormVector {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    ‖operatorNormVector M‖ = 1 := by
  simp only [operatorNormVector, dif_pos hn]
  exact (Classical.choose_spec (exists_unit_maximizer M hn)).1

/-- The selected vector dominates the image norm of every unit vector. -/
theorem operatorNormVector_maximal {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (w : ComplexEuclidean n) (hw : ‖w‖ = 1) :
    ‖matrixOperator M w‖ ≤ ‖matrixOperator M (operatorNormVector M)‖ := by
  simpa only [operatorNormVector, dif_pos hn] using
    (Classical.choose_spec (exists_unit_maximizer M hn)).2 w hw

/-- Exact attainment of the matrix's Euclidean (`ℓ²`) operator norm. -/
theorem norm_matrixOperator_operatorNormVector {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    ‖matrixOperator M (operatorNormVector M)‖ = ‖M‖ := by
  let v := operatorNormVector M
  have hv : ‖v‖ = 1 := norm_operatorNormVector M hn
  apply le_antisymm
  · calc
      ‖matrixOperator M v‖ ≤ ‖matrixOperator M‖ * ‖v‖ :=
        (matrixOperator M).le_opNorm v
      _ = ‖M‖ := by rw [norm_matrixOperator, hv, mul_one]
  · rw [← norm_matrixOperator]
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro w
    by_cases hwzero : w = 0
    · simp [hwzero]
    · let u : ComplexEuclidean n := (‖w‖⁻¹ : ℂ) • w
      have hu : ‖u‖ = 1 := norm_smul_inv_norm hwzero
      have hmax : ‖matrixOperator M u‖ ≤ ‖matrixOperator M v‖ :=
        operatorNormVector_maximal M hn u hu
      have hwu : (‖w‖ : ℂ) • u = w := by
        simp [u, smul_smul, hwzero]
      calc
        ‖matrixOperator M w‖ =
            ‖matrixOperator M ((‖w‖ : ℂ) • u)‖ := by rw [hwu]
        _ = ‖(‖w‖ : ℂ) • matrixOperator M u‖ := by rw [map_smul]
        _ = ‖w‖ * ‖matrixOperator M u‖ := by
          rw [norm_smul, Complex.norm_real,
            Real.norm_of_nonneg (norm_nonneg w)]
        _ ≤ ‖w‖ * ‖matrixOperator M v‖ :=
          mul_le_mul_of_nonneg_left hmax (norm_nonneg w)
        _ = ‖matrixOperator M v‖ * ‖w‖ := mul_comm _ _

end

end ConnectedPseudospectrum
