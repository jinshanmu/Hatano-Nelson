import Mathlib

/-!
# Least singular values of finite complex matrices

This module defines the Euclidean least singular value of a square complex
matrix as the attained minimum of the norm of its action on the unit sphere.
The zero-dimensional value is defined to be zero; all attainment statements
are made under the mathematically necessary positive-dimension hypothesis.
-/

namespace ConnectedPseudospectrum

open Metric Set
open scoped Matrix.Norms.L2Operator NNReal

noncomputable section

/-- A complex coordinate vector equipped with its Euclidean (`ℓ²`) norm. -/
abbrev ComplexEuclidean (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- The continuous linear operator on complex Euclidean space represented by a
square matrix. -/
def matrixOperator {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ComplexEuclidean n →L[ℂ] ComplexEuclidean n :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) M

@[simp] theorem matrixOperator_toLp {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (v : Fin n → ℂ) :
    matrixOperator M (WithLp.toLp 2 v) = WithLp.toLp 2 (M.mulVec v) :=
  rfl

@[simp] theorem matrixOperator_zero {n : ℕ} :
    matrixOperator (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  simp [matrixOperator]

@[simp] theorem matrixOperator_add {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) :
    matrixOperator (M + N) = matrixOperator M + matrixOperator N := by
  simp [matrixOperator]

@[simp] theorem matrixOperator_sub {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) :
    matrixOperator (M - N) = matrixOperator M - matrixOperator N := by
  simp [matrixOperator]

@[simp] theorem norm_matrixOperator {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ‖matrixOperator M‖ = ‖M‖ :=
  rfl

private theorem exists_unit_minimizer {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0 < n) :
    ∃ v : ComplexEuclidean n,
      ‖v‖ = 1 ∧
        ∀ w : ComplexEuclidean n, ‖w‖ = 1 →
          ‖matrixOperator M v‖ ≤ ‖matrixOperator M w‖ := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : ProperSpace (ComplexEuclidean n) :=
    FiniteDimensional.proper_rclike ℂ (ComplexEuclidean n)
  have hsphere : (sphere (0 : ComplexEuclidean n) 1).Nonempty := by
    let i : Fin n := Classical.choice inferInstance
    refine ⟨EuclideanSpace.single i 1, ?_⟩
    exact mem_sphere_zero_iff_norm.mpr (by simp)
  obtain ⟨v, hv, hmin⟩ :=
    (isCompact_sphere (0 : ComplexEuclidean n) 1).exists_isMinOn hsphere
      (matrixOperator M).continuous.norm.continuousOn
  refine ⟨v, mem_sphere_zero_iff_norm.mp hv, ?_⟩
  intro w hw
  exact hmin (mem_sphere_zero_iff_norm.mpr hw)

/-- A unit vector at which the Euclidean least singular value is attained.
In dimension zero it is the unique zero vector. -/
def leastSingularVector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ComplexEuclidean n :=
  if hn : 0 < n then Classical.choose (exists_unit_minimizer M hn) else 0

/-- The actual finite-dimensional complex Euclidean least singular value.

For positive dimension this is the attained minimum of `‖M v‖` over
`‖v‖ = 1`. The zero-dimensional value is explicitly set to zero. -/
def leastSingularValue {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ‖matrixOperator M (leastSingularVector M)‖

/-- The selected least singular vector has unit norm in positive dimension. -/
theorem norm_leastSingularVector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0 < n) :
    ‖leastSingularVector M‖ = 1 := by
  simp only [leastSingularVector, dif_pos hn]
  exact (Classical.choose_spec (exists_unit_minimizer M hn)).1

/-- The selected vector minimizes the image norm on the Euclidean unit sphere. -/
theorem leastSingularVector_minimal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0 < n) (v : ComplexEuclidean n) (hv : ‖v‖ = 1) :
    ‖matrixOperator M (leastSingularVector M)‖ ≤ ‖matrixOperator M v‖ := by
  simpa only [leastSingularVector, dif_pos hn] using
    (Classical.choose_spec (exists_unit_minimizer M hn)).2 v hv

/-- Evaluation of the least singular value at its selected minimizing vector. -/
theorem leastSingularValue_eq_norm_apply {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) :
    leastSingularValue M = ‖matrixOperator M (leastSingularVector M)‖ :=
  rfl

/-- Every unit vector gives an upper bound for the least singular value. -/
theorem leastSingularValue_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0 < n) (v : ComplexEuclidean n) (hv : ‖v‖ = 1) :
    leastSingularValue M ≤ ‖matrixOperator M v‖ := by
  exact leastSingularVector_minimal M hn v hv

/-- The least singular value is attained on the Euclidean unit sphere. -/
theorem exists_leastSingularVector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0 < n) :
    ∃ v : ComplexEuclidean n,
      ‖v‖ = 1 ∧
        leastSingularValue M = ‖matrixOperator M v‖ ∧
          ∀ w : ComplexEuclidean n, ‖w‖ = 1 →
            leastSingularValue M ≤ ‖matrixOperator M w‖ := by
  refine ⟨leastSingularVector M, norm_leastSingularVector M hn, rfl, ?_⟩
  intro w hw
  exact leastSingularValue_le M hn w hw

/-- Least singular values are nonnegative. -/
theorem leastSingularValue_nonneg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    0 ≤ leastSingularValue M :=
  norm_nonneg _

/-- The zero-dimensional least singular value is zero. -/
@[simp] theorem leastSingularValue_fin_zero
    (M : Matrix (Fin 0) (Fin 0) ℂ) :
    leastSingularValue M = 0 := by
  simp [leastSingularValue, leastSingularVector]

/-- The zero matrix has least singular value zero in every dimension. -/
@[simp] theorem leastSingularValue_zero {n : ℕ} :
    leastSingularValue (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  simp [leastSingularValue]

/-- In positive dimension, the identity matrix has least singular value one. -/
@[simp] theorem leastSingularValue_one {n : ℕ} (hn : 0 < n) :
    leastSingularValue (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simp [leastSingularValue, matrixOperator, norm_leastSingularVector _ hn]

/-- Vanishing is equivalent to the existence of a unit kernel vector. -/
theorem leastSingularValue_eq_zero_iff_exists_unit_kernel {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    leastSingularValue M = 0 ↔
      ∃ v : ComplexEuclidean n, ‖v‖ = 1 ∧ matrixOperator M v = 0 := by
  constructor
  · intro hzero
    refine ⟨leastSingularVector M, norm_leastSingularVector M hn, ?_⟩
    apply norm_eq_zero.mp
    simpa only [leastSingularValue_eq_norm_apply] using hzero
  · rintro ⟨v, hv, hMv⟩
    apply le_antisymm
    · simpa only [hMv, norm_zero] using leastSingularValue_le M hn v hv
    · exact leastSingularValue_nonneg M

/-- A unit Euclidean kernel vector exists exactly when the determinant
vanishes. -/
theorem exists_unit_kernel_iff_det_eq_zero {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (∃ v : ComplexEuclidean n, ‖v‖ = 1 ∧ matrixOperator M v = 0) ↔
      M.det = 0 := by
  constructor
  · rintro ⟨v, hv, hMv⟩
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨WithLp.ofLp v, ?_, ?_⟩
    · intro hofLp
      have hvzero : v = 0 := by
        simpa only [WithLp.ofLp_eq_zero] using hofLp
      subst v
      simp at hv
    · rw [← Matrix.ofLp_toEuclideanCLM M v, ← matrixOperator]
      simp [hMv]
  · intro hdet
    obtain ⟨u, hu, hMu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    let v₀ : ComplexEuclidean n := WithLp.toLp 2 u
    have hv₀ : v₀ ≠ 0 := by
      simpa [v₀] using hu
    let v : ComplexEuclidean n := (‖v₀‖⁻¹ : ℂ) • v₀
    refine ⟨v, ?_, ?_⟩
    · exact norm_smul_inv_norm hv₀
    · simp [v, v₀, matrixOperator, hMu]

/-- The Euclidean least singular value vanishes exactly for a singular
matrix. -/
theorem leastSingularValue_eq_zero_iff_det_eq_zero {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    leastSingularValue M = 0 ↔ M.det = 0 := by
  rw [leastSingularValue_eq_zero_iff_exists_unit_kernel M hn,
    exists_unit_kernel_iff_det_eq_zero M]

/-- The least singular value gives the optimal homogeneous lower bound on
the norm of the matrix action. -/
theorem leastSingularValue_mul_norm_le_norm_apply {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (v : ComplexEuclidean n) :
    leastSingularValue M * ‖v‖ ≤ ‖matrixOperator M v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  · let u : ComplexEuclidean n := (‖v‖⁻¹ : ℂ) • v
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hv
    have hmin := leastSingularValue_le M hn u hu
    have hmul := mul_le_mul_of_nonneg_right hmin (norm_nonneg v)
    have huv : (‖v‖ : ℂ) • u = v := by
      simp [u, smul_smul, hv]
    calc
      leastSingularValue M * ‖v‖ ≤ ‖matrixOperator M u‖ * ‖v‖ := hmul
      _ = ‖(‖v‖ : ℂ) • matrixOperator M u‖ := by
        simp only [norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (norm_nonneg v)]
        exact mul_comm (‖matrixOperator M u‖) ‖v‖
      _ = ‖matrixOperator M v‖ := by rw [← map_smul, huv]

/-- Least singular values satisfy the standard product lower bound. -/
theorem leastSingularValue_mul_le {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    leastSingularValue M * leastSingularValue N ≤
      leastSingularValue (M * N) := by
  let v := leastSingularVector (M * N)
  have hv : ‖v‖ = 1 := norm_leastSingularVector (M * N) hn
  calc
    leastSingularValue M * leastSingularValue N ≤
        leastSingularValue M * ‖matrixOperator N v‖ :=
      mul_le_mul_of_nonneg_left (leastSingularValue_le N hn v hv)
        (leastSingularValue_nonneg M)
    _ ≤ ‖matrixOperator M (matrixOperator N v)‖ :=
      leastSingularValue_mul_norm_le_norm_apply M hn (matrixOperator N v)
    _ = ‖matrixOperator (M * N) v‖ := by simp [matrixOperator]
    _ = leastSingularValue (M * N) := by
      simp [leastSingularValue, v]

/-- Scaling a matrix scales its least singular value by the norm of the
scalar. -/
@[simp] theorem leastSingularValue_smul {n : ℕ} (c : ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    leastSingularValue (c • M) = ‖c‖ * leastSingularValue M := by
  by_cases hn : 0 < n
  · apply le_antisymm
    · let v := leastSingularVector M
      calc
        leastSingularValue (c • M) ≤ ‖matrixOperator (c • M) v‖ :=
          leastSingularValue_le (c • M) hn v (norm_leastSingularVector M hn)
        _ = ‖c‖ * leastSingularValue M := by
          simp [matrixOperator, leastSingularValue, v, norm_smul]
    · let v := leastSingularVector (c • M)
      have hmin := leastSingularValue_le M hn v
        (norm_leastSingularVector (c • M) hn)
      have hmul := mul_le_mul_of_nonneg_left hmin (norm_nonneg c)
      simpa [matrixOperator, leastSingularValue, v, norm_smul] using hmul
  · have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp

/-- A unitary matrix acts isometrically on complex Euclidean vectors. -/
theorem norm_matrixOperator_of_mem_unitary {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (v : ComplexEuclidean n) :
    ‖matrixOperator U v‖ = ‖v‖ := by
  apply ContinuousLinearMap.norm_map_of_mem_unitary
  exact Unitary.map_mem (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) hU

/-- Left multiplication by a unitary matrix preserves the least singular
value. -/
theorem leastSingularValue_unitary_mul {n : ℕ}
    (U M : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    leastSingularValue (U * M) = leastSingularValue M := by
  by_cases hn : 0 < n
  · let vM := leastSingularVector M
    let vUM := leastSingularVector (U * M)
    apply le_antisymm
    · calc
        leastSingularValue (U * M) ≤ ‖matrixOperator (U * M) vM‖ :=
          leastSingularValue_le (U * M) hn vM (norm_leastSingularVector M hn)
        _ = ‖matrixOperator U (matrixOperator M vM)‖ := by simp [matrixOperator]
        _ = ‖matrixOperator M vM‖ :=
          norm_matrixOperator_of_mem_unitary U hU (matrixOperator M vM)
        _ = leastSingularValue M := by simp [leastSingularValue, vM]
    · calc
        leastSingularValue M ≤ ‖matrixOperator M vUM‖ :=
          leastSingularValue_le M hn vUM (norm_leastSingularVector (U * M) hn)
        _ = ‖matrixOperator U (matrixOperator M vUM)‖ :=
          (norm_matrixOperator_of_mem_unitary U hU (matrixOperator M vUM)).symm
        _ = ‖matrixOperator (U * M) vUM‖ := by simp [matrixOperator]
        _ = leastSingularValue (U * M) := by
          simp [leastSingularValue, vUM]
  · have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp

/-- Right multiplication by a unitary matrix preserves the least singular
value. -/
theorem leastSingularValue_mul_unitary {n : ℕ}
    (M U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    leastSingularValue (M * U) = leastSingularValue M := by
  by_cases hn : 0 < n
  · let vM := leastSingularVector M
    let vMU := leastSingularVector (M * U)
    let w : ComplexEuclidean n := matrixOperator (star U) vM
    have hstar : star U ∈ Matrix.unitaryGroup (Fin n) ℂ := Unitary.star_mem hU
    have hw : ‖w‖ = 1 := by
      dsimp only [w]
      rw [norm_matrixOperator_of_mem_unitary (star U) hstar,
        norm_leastSingularVector M hn]
    have hUstar : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
    have hUw : matrixOperator U w = vM := by
      dsimp only [w]
      calc
        matrixOperator U (matrixOperator (star U) vM) =
            matrixOperator (U * star U) vM := by simp [matrixOperator]
        _ = vM := by rw [hUstar]; simp [matrixOperator]
    have hMUw : matrixOperator (M * U) w = matrixOperator M vM := by
      calc
        matrixOperator (M * U) w = matrixOperator M (matrixOperator U w) := by
          simp [matrixOperator]
        _ = matrixOperator M vM := by rw [hUw]
    apply le_antisymm
    · calc
        leastSingularValue (M * U) ≤ ‖matrixOperator (M * U) w‖ :=
          leastSingularValue_le (M * U) hn w hw
        _ = ‖matrixOperator M vM‖ := by rw [hMUw]
        _ = leastSingularValue M := by simp [leastSingularValue, vM]
    · have hvMU : ‖matrixOperator U vMU‖ = 1 := by
        rw [norm_matrixOperator_of_mem_unitary U hU,
          norm_leastSingularVector (M * U) hn]
      calc
        leastSingularValue M ≤ ‖matrixOperator M (matrixOperator U vMU)‖ :=
          leastSingularValue_le M hn (matrixOperator U vMU) hvMU
        _ = ‖matrixOperator (M * U) vMU‖ := by simp [matrixOperator]
        _ = leastSingularValue (M * U) := by
          simp [leastSingularValue, vMU]
  · have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp

/-- A unitary matrix has least singular value one in positive dimension. -/
theorem leastSingularValue_of_mem_unitary {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    leastSingularValue U = 1 := by
  calc
    leastSingularValue U = leastSingularValue (U * 1) := by rw [mul_one]
    _ = leastSingularValue (1 : Matrix (Fin n) (Fin n) ℂ) :=
      leastSingularValue_unitary_mul U 1 hU
    _ = 1 := leastSingularValue_one hn

/-- A one-sided perturbation estimate for the least singular value. -/
theorem leastSingularValue_le_add_norm_sub {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℂ) :
    leastSingularValue M ≤ leastSingularValue N + ‖M - N‖ := by
  by_cases hn : 0 < n
  · let v := leastSingularVector N
    have hv : ‖v‖ = 1 := norm_leastSingularVector N hn
    have hmin : leastSingularValue M ≤ ‖matrixOperator M v‖ :=
      leastSingularValue_le M hn v hv
    have hdiff : ‖matrixOperator M v - matrixOperator N v‖ ≤ ‖M - N‖ := by
      calc
        ‖matrixOperator M v - matrixOperator N v‖ = ‖matrixOperator (M - N) v‖ := by
          rw [matrixOperator_sub, ContinuousLinearMap.sub_apply]
        _ ≤ ‖matrixOperator (M - N)‖ * ‖v‖ :=
          (matrixOperator (M - N)).le_opNorm v
        _ = ‖M - N‖ := by rw [norm_matrixOperator, hv, mul_one]
    have hnorm : ‖matrixOperator M v‖ ≤
        ‖matrixOperator N v‖ + ‖M - N‖ := by
      linarith [norm_sub_norm_le (matrixOperator M v) (matrixOperator N v)]
    exact hmin.trans (by simpa [leastSingularValue, v] using hnorm)
  · have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp

/-- The least singular value is `1`-Lipschitz in the Euclidean operator norm. -/
theorem abs_leastSingularValue_sub_le {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) ℂ) :
    |leastSingularValue M - leastSingularValue N| ≤ ‖M - N‖ := by
  have hMN := leastSingularValue_le_add_norm_sub M N
  have hNM := leastSingularValue_le_add_norm_sub N M
  rw [abs_le]
  constructor
  · rw [neg_le_sub_iff_le_add]
    simpa [norm_sub_rev] using hNM
  · simpa [add_comm] using sub_le_iff_le_add.mpr hMN

/-- Least singular value is a Lipschitz function of the matrix. -/
theorem leastSingularValue_lipschitzWith (n : ℕ) :
    LipschitzWith 1
      (leastSingularValue : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro M N
  simpa [Real.dist_eq, dist_eq_norm] using abs_leastSingularValue_sub_le M N

/-- Least singular value depends continuously on the matrix. -/
theorem continuous_leastSingularValue (n : ℕ) :
    Continuous (leastSingularValue : Matrix (Fin n) (Fin n) ℂ → ℝ) :=
  (leastSingularValue_lipschitzWith n).continuous

end

end ConnectedPseudospectrum
