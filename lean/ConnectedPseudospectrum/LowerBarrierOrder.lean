import ConnectedPseudospectrum.TailThresholdAsymptotic

/-!
# Fixed-parameter order of the explicit lower barrier

This module gives the elementary lower comparison between the paper's
explicit lower barrier `𝓛ₙ(a)` and the scalar tail model `(n+1)rⁿ`, where
`r = √a`.  The constant is explicit and depends only on `a`.
-/

namespace ConnectedPseudospectrum

noncomputable section

/-- An explicit positive fixed-`a` constant in the lower-barrier estimate. -/
def lowerBarrierOrderConstant (a : ℝ) : ℝ :=
  2 * (1 - pathRate a) ^ 2 * (1 - pathRate a ^ 2) / (3 * Real.pi)

/-- The lower-barrier order constant is positive for the paper's parameter
range `0 < a < 1`. -/
theorem lowerBarrierOrderConstant_pos {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    0 < lowerBarrierOrderConstant a := by
  have hr : 0 < pathRate a := by
    exact Real.sqrt_pos.2 ha
  have hr1 : pathRate a < 1 := by
    unfold pathRate
    simpa using (Real.sqrt_lt_sqrt_iff ha.le).2 ha1
  have hsub : 0 < 1 - pathRate a := sub_pos.2 hr1
  have hsquare : 0 < (1 - pathRate a) ^ 2 := sq_pos_of_pos hsub
  have hquadratic : 0 < 1 - pathRate a ^ 2 := by
    nlinarith
  unfold lowerBarrierOrderConstant
  positivity

/-- For every dimension at least two, the explicit lower barrier dominates
an explicit positive fixed-parameter multiple of `(n+1)rⁿ`. -/
theorem lowerBarrierOrderConstant_mul_tailModel_le_lowerBarrier
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {n : ℕ} (hn : 2 ≤ n) :
    lowerBarrierOrderConstant a * tailModel (pathRate a) n ≤
      lowerBarrier n a := by
  let r : ℝ := pathRate a
  let N : ℝ := (n : ℝ) + 1
  let beta : ℝ := 3 * Real.pi / (2 * N)
  have hr : 0 < r := by
    dsimp [r, pathRate]
    exact Real.sqrt_pos.2 ha
  have hr1 : r < 1 := by
    dsimp [r, pathRate]
    simpa using (Real.sqrt_lt_sqrt_iff ha.le).2 ha1
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hN_ge_three : 3 ≤ N := by
    dsimp [N]
    have hn_real : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hbeta : 0 < beta := by
    dsimp [beta]
    positivity
  have hbeta_lt_pi : beta < Real.pi := by
    dsimp [beta]
    rw [div_lt_iff₀ (by positivity : 0 < 2 * N)]
    nlinarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin beta :=
    Real.sin_pos_of_pos_of_lt_pi hbeta hbeta_lt_pi
  have hsin_le : Real.sin beta ≤ beta :=
    Real.sin_le hbeta.le
  have hpow_nonneg : 0 ≤ r ^ (2 * (n + 1)) := pow_nonneg hr.le _
  have hpow_lt_one : r ^ (2 * (n + 1)) < 1 := by
    apply pow_lt_one₀ hr.le hr1
    omega
  have hone_sub_pow_pos : 0 < 1 - r ^ (2 * (n + 1)) := sub_pos.2 hpow_lt_one
  have hone_sub_pow_le_one : 1 - r ^ (2 * (n + 1)) ≤ 1 := by
    linarith
  have hden_pos :
      0 < (1 - r ^ (2 * (n + 1))) * Real.sin beta :=
    mul_pos hone_sub_pow_pos hsin_pos
  have hden_le_beta :
      (1 - r ^ (2 * (n + 1))) * Real.sin beta ≤ beta := by
    calc
      (1 - r ^ (2 * (n + 1))) * Real.sin beta
          ≤ 1 * Real.sin beta :=
        mul_le_mul_of_nonneg_right hone_sub_pow_le_one hsin_pos.le
      _ ≤ beta := by simpa using hsin_le
  have hdelta :
      (1 - r) ^ 2 ≤
        1 + r ^ 2 - 2 * r * Real.cos (Real.pi / N) := by
    have hcos : Real.cos (Real.pi / N) ≤ 1 := Real.cos_le_one _
    nlinarith
  have hquadratic : 0 ≤ 1 - r ^ 2 := by
    nlinarith
  have hrpow : 0 ≤ r ^ n := pow_nonneg hr.le n
  have htailfactor : 0 ≤ r ^ n * (1 - r ^ 2) :=
    mul_nonneg hrpow hquadratic
  have hnum_lower :
      (1 - r) ^ 2 * (r ^ n * (1 - r ^ 2)) ≤
        (1 + r ^ 2 - 2 * r * Real.cos (Real.pi / N)) *
          (r ^ n * (1 - r ^ 2)) :=
    mul_le_mul_of_nonneg_right hdelta htailfactor
  have hbase_nonneg :
      0 ≤ (1 - r) ^ 2 * (r ^ n * (1 - r ^ 2)) :=
    mul_nonneg (sq_nonneg _) htailfactor
  have hconstant_identity :
      lowerBarrierOrderConstant a * tailModel r n =
        ((1 - r) ^ 2 * (r ^ n * (1 - r ^ 2))) / beta := by
    dsimp [lowerBarrierOrderConstant, tailModel, r, beta, N]
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hconstant_identity]
  unfold lowerBarrier
  dsimp only
  change
    ((1 - r) ^ 2 * (r ^ n * (1 - r ^ 2))) / beta ≤
      (1 + r ^ 2 - 2 * r * Real.cos (Real.pi / N)) *
          (r ^ n * (1 - r ^ 2)) /
        ((1 - r ^ (2 * (n + 1))) * Real.sin beta)
  apply (le_div_iff₀ hden_pos).2
  calc
    (((1 - r) ^ 2 * (r ^ n * (1 - r ^ 2))) / beta) *
          ((1 - r ^ (2 * (n + 1))) * Real.sin beta)
        ≤ (((1 - r) ^ 2 * (r ^ n * (1 - r ^ 2))) / beta) * beta :=
      mul_le_mul_of_nonneg_left hden_le_beta (div_nonneg hbase_nonneg hbeta.le)
    _ = (1 - r) ^ 2 * (r ^ n * (1 - r ^ 2)) := by
      exact div_mul_cancel₀ _ hbeta.ne'
    _ ≤ (1 + r ^ 2 - 2 * r * Real.cos (Real.pi / N)) *
          (r ^ n * (1 - r ^ 2)) := hnum_lower

end

end ConnectedPseudospectrum
