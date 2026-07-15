import ConnectedPseudospectrum.Definitions
import ConnectedPseudospectrum.PathSpectrum

/-!
# Truncated sine pseudoeigenvectors and the upper gap barrier

This module formalizes the upper-bound half of `prop:gap-bounds`, following
the truncated sine vector calculation in lines 2062--2077 of the source.
-/

namespace ConnectedPseudospectrum

open Matrix Set

noncomputable section

/-- The real coordinates `r^i sin((i+1)θ)` of the paper's truncated sine vector. -/
def truncatedSineReal (n : ℕ) (r θ : ℝ) : Fin n → ℝ :=
  fun i => r ^ i.1 * Real.sin (((i.1 + 1 : ℕ) : ℝ) * θ)

/-- The truncated sine vector in the complex Euclidean space used to define singular values. -/
def truncatedSineVector (n : ℕ) (r θ : ℝ) : ComplexEuclidean n :=
  WithLp.toLp 2 fun i => (truncatedSineReal n r θ i : ℂ)

@[simp] theorem truncatedSineVector_apply (n : ℕ) (r θ : ℝ) (i : Fin n) :
    truncatedSineVector n r θ i = (truncatedSineReal n r θ i : ℂ) :=
  rfl

/-- Exact Euclidean norm of the truncated sine vector. -/
theorem norm_truncatedSineVector (n : ℕ) (r θ : ℝ) :
    ‖truncatedSineVector n r θ‖ =
      Real.sqrt (∑ i : Fin n,
        (r ^ i.1 * Real.sin (((i.1 + 1 : ℕ) : ℝ) * θ)) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro i hi
  change ‖((r ^ i.1 * Real.sin (((i.1 + 1 : ℕ) : ℝ) * θ) : ℝ) : ℂ)‖ ^ 2 = _
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The first coordinate gives the norm lower bound needed in the paper. -/
theorem sin_le_norm_truncatedSineVector {n : ℕ} (hn : 0 < n) (r θ : ℝ)
    (hθ : 0 ≤ Real.sin θ) :
    Real.sin θ ≤ ‖truncatedSineVector n r θ‖ := by
  let first : Fin n := ⟨0, hn⟩
  have hcoord := PiLp.norm_apply_le (truncatedSineVector n r θ) first
  have hcoord_eq : ‖truncatedSineVector n r θ first‖ = Real.sin θ := by
    rw [truncatedSineVector_apply]
    have hfirst : truncatedSineReal n r θ first = Real.sin θ := by
      simp [truncatedSineReal, first]
    rw [hfirst]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ]
  rw [hcoord_eq] at hcoord
  exact hcoord

/-- The real shifted path matrix used before casting the residual calculation to `ℂ`. -/
def upperBoundRealShiftedPathMatrix (n : ℕ) (a x : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  x • 1 - pathMatrix n a

/-- Casting a real shifted matrix and vector to `ℂ` commutes with matrix-vector multiplication. -/
theorem shiftedPathMatrix_mulVec_ofReal (n : ℕ) (a x : ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (shiftedPathMatrix n a (x : ℂ) *ᵥ fun j => (v j : ℂ)) i =
      ((upperBoundRealShiftedPathMatrix n a x *ᵥ v) i : ℂ) := by
  simp only [shiftedPathMatrix, upperBoundRealShiftedPathMatrix,
    Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [complexPathMatrix_apply]
  push_cast
  rfl

private theorem sine_three_term (θ : ℝ) (m : ℕ) :
    Real.sin ((m : ℝ) * θ) + Real.sin (((m + 2 : ℕ) : ℝ) * θ) =
      2 * Real.cos θ * Real.sin (((m + 1 : ℕ) : ℝ) * θ) := by
  have hsub :
      (m : ℝ) * θ = (((m + 1 : ℕ) : ℝ) * θ - θ) := by
    push_cast
    ring
  have hadd :
      ((m + 2 : ℕ) : ℝ) * θ = (((m + 1 : ℕ) : ℝ) * θ + θ) := by
    push_cast
    ring
  rw [hsub, hadd, ← Real.two_mul_sin_mul_cos]
  ring

/-- Pointwise residual identity for a positive-length truncated sine vector.
Only the last coordinate can be nonzero. -/
theorem realShiftedPathMatrix_mulVec_truncatedSineReal (m : ℕ) (hm : 0 < m)
    (r θ : ℝ) (i : Fin (m + 1)) :
    (upperBoundRealShiftedPathMatrix (m + 1) (r ^ 2)
      (2 * r * Real.cos θ) *ᵥ
        truncatedSineReal (m + 1) r θ) i =
      if i = Fin.last m then
        r ^ (m + 1) * Real.sin (((m + 2 : ℕ) : ℝ) * θ)
      else 0 := by
  simp only [upperBoundRealShiftedPathMatrix, Matrix.sub_mulVec,
    Matrix.smul_mulVec,
    Matrix.one_mulVec, pathMatrix_eq_upper_add_lower, Matrix.add_mulVec,
    Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  by_cases hiLast : i = Fin.last m
  · subst i
    rw [if_pos rfl]
    rw [upperShift_mulVec_apply_of_not_lt]
    · rw [lowerShift_mulVec_apply_of_pos]
      · simp only [truncatedSineReal, Fin.val_last]
        have hpow : r ^ 2 * r ^ (m - 1) = r ^ (m + 1) := by
          rw [← pow_add]
          congr 1
          omega
        have hmIndex : m - 1 + 1 = m := by omega
        have hrec := sine_three_term θ m
        rw [pow_succ r m] at hpow
        rw [hmIndex, pow_succ r m]
        linear_combination (norm := ring_nf)
          -(r ^ m * r) * hrec - Real.sin ((m : ℝ) * θ) * hpow
      · simpa using hm
    · simp
  · rw [if_neg hiLast]
    have hiUpper : i.1 + 1 < m + 1 := by
      have hle : i.1 ≤ m := Nat.le_of_lt_succ i.isLt
      have hne : i.1 ≠ m := by
        intro h
        apply hiLast
        apply Fin.ext
        simpa using h
      omega
    rw [upperShift_mulVec_apply_of_lt _ _ _ hiUpper]
    by_cases hiZero : i.1 = 0
    · rw [lowerShift_mulVec_apply_of_eq_zero _ _ _ hiZero]
      simp only [truncatedSineReal]
      have hrec := sine_three_term θ 0
      simp only [hiZero, Nat.cast_zero, zero_mul, Real.sin_zero, zero_add,
        Nat.cast_ofNat, pow_zero, one_mul, pow_one] at hrec ⊢
      have hrec' : Real.sin (θ * 2) = 2 * Real.cos θ * Real.sin θ := by
        simpa [mul_comm] using hrec
      linear_combination (norm := ring_nf) -r * hrec'
    · have hiPos : 0 < i.1 := Nat.pos_of_ne_zero hiZero
      rw [lowerShift_mulVec_apply_of_pos _ _ _ hiPos]
      simp only [truncatedSineReal]
      have hpow : r ^ 2 * r ^ (i.1 - 1) = r ^ (i.1 + 1) := by
        rw [← pow_add]
        congr 1
        omega
      have hiPred : i.1 - 1 + 1 = i.1 := by omega
      have hiSucc : i.1 + 1 + 1 = i.1 + 2 := by omega
      have hrec := sine_three_term θ i.1
      rw [pow_succ r i.1] at hpow
      rw [hiPred, hiSucc, pow_succ r i.1]
      linear_combination (norm := ring_nf)
        -(r ^ i.1 * r) * hrec - Real.sin ((i.1 : ℝ) * θ) * hpow

/-- The residual has exactly the norm of its last coordinate. -/
theorem norm_matrixOperator_truncatedSineVector (m : ℕ) (hm : 0 < m)
    (r θ : ℝ) :
    ‖matrixOperator
        (shiftedPathMatrix (m + 1) (r ^ 2)
          ((2 * r * Real.cos θ : ℝ) : ℂ))
        (truncatedSineVector (m + 1) r θ)‖ =
      |r ^ (m + 1) * Real.sin (((m + 2 : ℕ) : ℝ) * θ)| := by
  let last : Fin (m + 1) := Fin.last m
  let c : ℝ := r ^ (m + 1) * Real.sin (((m + 2 : ℕ) : ℝ) * θ)
  have hres :
      (shiftedPathMatrix (m + 1) (r ^ 2)
          ((2 * r * Real.cos θ : ℝ) : ℂ) *ᵥ
          fun j => (truncatedSineReal (m + 1) r θ j : ℂ)) =
        Pi.single last (c : ℂ) := by
    funext i
    rw [shiftedPathMatrix_mulVec_ofReal,
      realShiftedPathMatrix_mulVec_truncatedSineReal m hm]
    by_cases hi : i = last
    · subst i
      simp [last, c]
    · simp [last, c, hi]
  change
    ‖matrixOperator
        (shiftedPathMatrix (m + 1) (r ^ 2)
          ((2 * r * Real.cos θ : ℝ) : ℂ))
        (WithLp.toLp 2 fun j => (truncatedSineReal (m + 1) r θ j : ℂ))‖ = _
  rw [matrixOperator_toLp, hres, PiLp.norm_toLp_single]
  exact Complex.norm_real c

/-- The normalized truncated sine residual gives the paper's pointwise
least-singular-value upper estimate. -/
theorem pseudospectralHeight_at_cos_le_truncatedSine (m : ℕ) (hm : 0 < m)
    (r θ : ℝ) (hr : 0 ≤ r) (hθ : 0 < Real.sin θ) :
    pseudospectralHeight (m + 1) (r ^ 2)
        ((2 * r * Real.cos θ : ℝ) : ℂ) ≤
      r ^ (m + 1) *
          |Real.sin (((m + 2 : ℕ) : ℝ) * θ)| / Real.sin θ := by
  let M := shiftedPathMatrix (m + 1) (r ^ 2)
    ((2 * r * Real.cos θ : ℝ) : ℂ)
  let v := truncatedSineVector (m + 1) r θ
  have hleast := leastSingularValue_mul_norm_le_norm_apply M (Nat.succ_pos m) v
  have hnorm : Real.sin θ ≤ ‖v‖ := by
    exact sin_le_norm_truncatedSineVector (Nat.succ_pos m) r θ hθ.le
  have hmul : leastSingularValue M * Real.sin θ ≤
      leastSingularValue M * ‖v‖ :=
    mul_le_mul_of_nonneg_left hnorm (leastSingularValue_nonneg M)
  have hchain := hmul.trans hleast
  have hresnorm : ‖matrixOperator M v‖ =
      |r ^ (m + 1) * Real.sin (((m + 2 : ℕ) : ℝ) * θ)| := by
    exact norm_matrixOperator_truncatedSineVector m hm r θ
  rw [hresnorm, abs_mul, abs_pow, abs_of_nonneg hr] at hchain
  rw [le_div_iff₀ hθ]
  simpa [pseudospectralHeight, M] using hchain

private theorem sin_fundamental_interval_lower_bound (m : ℕ)
    (θ : ℝ)
    (hθLower : Real.pi / ((m + 2 : ℕ) : ℝ) ≤ θ)
    (hθUpper : θ ≤ Real.pi - Real.pi / ((m + 2 : ℕ) : ℝ)) :
    Real.sin (Real.pi / ((m + 2 : ℕ) : ℝ)) ≤ Real.sin θ := by
  let α := Real.pi / ((m + 2 : ℕ) : ℝ)
  have hden : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hαpos : 0 < α := div_pos Real.pi_pos hden
  change Real.sin α ≤ Real.sin θ
  change α ≤ θ at hθLower
  change θ ≤ Real.pi - α at hθUpper
  by_cases hθHalf : θ ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hθHalf hθLower
  · have hreflectedHalf : Real.pi - θ ≤ Real.pi / 2 := by linarith
    have hαReflected : α ≤ Real.pi - θ := by linarith
    calc
      Real.sin α ≤ Real.sin (Real.pi - θ) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith)
          hreflectedHalf hαReflected
      _ = Real.sin θ := Real.sin_pi_sub θ

/-- On the whole angular range corresponding to the real spectral interval,
the truncated sine estimate is bounded by the explicit upper barrier. -/
theorem pseudospectralHeight_at_cos_le_upperBarrier (m : ℕ) (hm : 0 < m)
    (r θ : ℝ) (hr : 0 ≤ r)
    (hθLower : Real.pi / ((m + 2 : ℕ) : ℝ) ≤ θ)
    (hθUpper : θ ≤ Real.pi - Real.pi / ((m + 2 : ℕ) : ℝ)) :
    pseudospectralHeight (m + 1) (r ^ 2)
        ((2 * r * Real.cos θ : ℝ) : ℂ) ≤
      r ^ (m + 1) *
        (Real.sin (Real.pi / ((m + 2 : ℕ) : ℝ)))⁻¹ := by
  let α := Real.pi / ((m + 2 : ℕ) : ℝ)
  have hden : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hαpos : 0 < α := div_pos Real.pi_pos hden
  have hθpos : 0 < θ := by
    change α ≤ θ at hθLower
    exact hαpos.trans_le hθLower
  have hθlt : θ < Real.pi := by
    change θ ≤ Real.pi - α at hθUpper
    exact hθUpper.trans_lt (sub_lt_self Real.pi hαpos)
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
  have hsinα : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hαpos (hθLower.trans_lt hθlt)
  have hsinLower : Real.sin α ≤ Real.sin θ := by
    exact sin_fundamental_interval_lower_bound m θ hθLower hθUpper
  have habs : |Real.sin (((m + 2 : ℕ) : ℝ) * θ)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  have hratio :
      |Real.sin (((m + 2 : ℕ) : ℝ) * θ)| / Real.sin θ ≤
        (Real.sin α)⁻¹ := by
    calc
      |Real.sin (((m + 2 : ℕ) : ℝ) * θ)| / Real.sin θ ≤
          1 / Real.sin θ :=
        (div_le_div_iff_of_pos_right hsinθ).2 habs
      _ ≤ 1 / Real.sin α := one_div_le_one_div_of_le hsinα hsinLower
      _ = (Real.sin α)⁻¹ := one_div _
  calc
    pseudospectralHeight (m + 1) (r ^ 2)
        ((2 * r * Real.cos θ : ℝ) : ℂ) ≤
        r ^ (m + 1) * |Real.sin (((m + 2 : ℕ) : ℝ) * θ)| /
          Real.sin θ :=
      pseudospectralHeight_at_cos_le_truncatedSine m hm r θ hr hsinθ
    _ = r ^ (m + 1) *
        (|Real.sin (((m + 2 : ℕ) : ℝ) * θ)| / Real.sin θ) := by ring
    _ ≤ r ^ (m + 1) * (Real.sin α)⁻¹ :=
      mul_le_mul_of_nonneg_left hratio (pow_nonneg hr _)
    _ = r ^ (m + 1) *
        (Real.sin (Real.pi / ((m + 2 : ℕ) : ℝ)))⁻¹ := rfl

/-- Every point of the real spectral interval for `A_{m+1}(r²)` has the
paper's cosine parametrization with angle in the full nodal range. -/
theorem exists_angle_of_mem_spectralInterval_sq (m : ℕ)
    (r x : ℝ) (hr : 0 < r) (hx : x ∈ spectralInterval (m + 1) (r ^ 2)) :
    ∃ θ : ℝ,
      Real.pi / ((m + 2 : ℕ) : ℝ) ≤ θ ∧
      θ ≤ Real.pi - Real.pi / ((m + 2 : ℕ) : ℝ) ∧
      x = 2 * r * Real.cos θ := by
  let α := Real.pi / ((m + 2 : ℕ) : ℝ)
  let q := x / (2 * r)
  have hden : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
  have hαpos : 0 < α := div_pos Real.pi_pos hden
  have hdenTwo : (2 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 ≤ m + 2 by omega)
  have hαHalf : α ≤ Real.pi / 2 := by
    exact (div_le_div_iff_of_pos_left Real.pi_pos hden (by norm_num)).2 hdenTwo
  have hαPi : α ≤ Real.pi := hαHalf.trans (by linarith [Real.pi_pos])
  have hsqrt : pathRate (r ^ 2) = r := by
    simpa [pathRate] using Real.sqrt_sq hr.le
  have hdim : ((m + 1 : ℕ) : ℝ) + 1 = ((m + 2 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [spectralInterval, mem_Icc, spectralRadius, hsqrt, hdim] at hx
  have htwoR : 0 < 2 * r := mul_pos (by norm_num) hr
  have hqLower : -Real.cos α ≤ q := by
    apply (le_div_iff₀ htwoR).2
    change -Real.cos α * (2 * r) ≤ x
    have hxLower := hx.1
    change -(2 * r * Real.cos α) ≤ x at hxLower
    nlinarith
  have hqUpper : q ≤ Real.cos α := by
    apply (div_le_iff₀ htwoR).2
    change x ≤ Real.cos α * (2 * r)
    have hxUpper := hx.2
    change x ≤ 2 * r * Real.cos α at hxUpper
    nlinarith
  have hqNegOne : (-1 : ℝ) ≤ q := by
    exact (neg_le_neg (Real.cos_le_one α)).trans hqLower
  have hqOne : q ≤ (1 : ℝ) := hqUpper.trans (Real.cos_le_one α)
  refine ⟨Real.arccos q, ?_, ?_, ?_⟩
  · change α ≤ Real.arccos q
    have harccos := Real.arccos_le_arccos hqUpper
    rwa [Real.arccos_cos hαpos.le hαPi] at harccos
  · change Real.arccos q ≤ Real.pi - α
    have harccos := Real.arccos_le_arccos hqLower
    rw [Real.arccos_neg, Real.arccos_cos hαpos.le hαPi] at harccos
    exact harccos
  · rw [Real.cos_arccos hqNegOne hqOne]
    change x = 2 * r * (x / (2 * r))
    field_simp

/-- The attained real gap maximum is bounded by the explicit truncated-sine
barrier when the asymmetry is written as `a=r²`. -/
theorem gapBarrier_sq_le_truncatedSineBarrier (m : ℕ) (hm : 0 < m)
    (r : ℝ) (hr : 0 < r) :
    gapBarrier (m + 1) (r ^ 2) ≤
      r ^ (m + 1) *
        (Real.sin (Real.pi / ((m + 2 : ℕ) : ℝ)))⁻¹ := by
  obtain ⟨x, hx, hxMax⟩ :=
    exists_realGapValue_eq_gapBarrier (m + 1) (r ^ 2) (by omega)
  obtain ⟨θ, hθLower, hθUpper, hxθ⟩ :=
    exists_angle_of_mem_spectralInterval_sq m r x hr hx
  rw [← hxMax]
  rw [hxθ]
  simpa [realGapValue] using
    pseudospectralHeight_at_cos_le_upperBarrier m hm r θ hr.le hθLower hθUpper

/-- Upper-bound half of `prop:gap-bounds`, with `n=m+1` (hence `n≥2`). -/
theorem gapBarrier_le_upperBarrier_succ (m : ℕ) (hm : 0 < m)
    (a : ℝ) (ha : 0 < a) :
    gapBarrier (m + 1) a ≤ upperBarrier (m + 1) a := by
  let r := pathRate a
  have hr : 0 < r := Real.sqrt_pos.2 ha
  have hra : r ^ 2 = a := Real.sq_sqrt ha.le
  have hbound := gapBarrier_sq_le_truncatedSineBarrier m hm r hr
  rw [hra] at hbound
  have hdim : ((m + 1 : ℕ) : ℝ) + 1 = ((m + 2 : ℕ) : ℝ) := by
    push_cast
    ring
  unfold upperBarrier
  rw [hdim]
  simpa only [r] using hbound

/-- Upper-bound half of `prop:gap-bounds` in the paper's original indexing. -/
theorem gapBarrier_le_upperBarrier {n : ℕ} (hn : 2 ≤ n)
    (a : ℝ) (ha : 0 < a) :
    gapBarrier n a ≤ upperBarrier n a := by
  have hm : 0 < n - 1 := by omega
  have hnEq : n - 1 + 1 = n := by omega
  rw [← hnEq]
  exact gapBarrier_le_upperBarrier_succ (n - 1) hm a ha

end

end ConnectedPseudospectrum
