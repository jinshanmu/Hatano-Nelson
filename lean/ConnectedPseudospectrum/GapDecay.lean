import ConnectedPseudospectrum.GapUpperBound

/-!
# Decay of the real gap barrier

This module proves the fixed-parameter decay consequence of the upper half of
`prop:gap-bounds`.  The key elementary estimate is the paper's
`Uₙ(a) ≤ (n+1) rⁿ / 2`, where `r = √a`.
-/

namespace ConnectedPseudospectrum

open Filter

noncomputable section

/-- The explicit upper barrier is nonnegative in every positive dimension. -/
theorem upperBarrier_nonneg_of_one_le {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    0 ≤ upperBarrier n a := by
  have hden : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have hdenOne : (1 : ℝ) < (n + 1 : ℝ) := by
    exact_mod_cast (show 1 < n + 1 by omega)
  have hanglePos : 0 < Real.pi / (n + 1 : ℝ) :=
    div_pos Real.pi_pos hden
  have hangleLt : Real.pi / (n + 1 : ℝ) < Real.pi :=
    div_lt_self Real.pi_pos hdenOne
  have hsin : 0 < Real.sin (Real.pi / (n + 1 : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hanglePos hangleLt
  unfold upperBarrier
  exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg a) n) (inv_nonneg.mpr hsin.le)

/-- The elementary estimate used to turn the explicit upper barrier into a
geometrically decaying sequence. -/
theorem upperBarrier_le_linear_mul_pow {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    upperBarrier n a ≤
      ((n + 1 : ℕ) : ℝ) * pathRate a ^ n / 2 := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let α : ℝ := Real.pi / N
  have hNpos : 0 < N := by
    dsimp only [N]
    positivity
  have hNtwo : (2 : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast (show 2 ≤ n + 1 by omega)
  have hαnonneg : 0 ≤ α := div_nonneg Real.pi_pos.le hNpos.le
  have hαhalf : α ≤ Real.pi / 2 := by
    exact (div_le_div_iff_of_pos_left Real.pi_pos hNpos (by norm_num)).2 hNtwo
  have hsinLower : 2 / N ≤ Real.sin α := by
    calc
      2 / N = 2 / Real.pi * α := by
        dsimp only [α]
        field_simp [Real.pi_ne_zero, hNpos.ne']
      _ ≤ Real.sin α := Real.mul_le_sin hαnonneg hαhalf
  have htwoDivPos : 0 < 2 / N := div_pos (by norm_num) hNpos
  have hinv : (Real.sin α)⁻¹ ≤ N / 2 := by
    calc
      (Real.sin α)⁻¹ = 1 / Real.sin α := (one_div _).symm
      _ ≤ 1 / (2 / N) := one_div_le_one_div_of_le htwoDivPos hsinLower
      _ = N / 2 := by field_simp [hNpos.ne']
  have hinv' :
      (Real.sin (Real.pi / (n + 1 : ℝ)))⁻¹ ≤
        ((n + 1 : ℕ) : ℝ) / 2 := by
    simpa [α, N] using hinv
  unfold upperBarrier
  calc
    pathRate a ^ n * (Real.sin (Real.pi / (n + 1 : ℝ)))⁻¹ ≤
        pathRate a ^ n * (((n + 1 : ℕ) : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hinv' (pow_nonneg (Real.sqrt_nonneg a) n)
    _ = ((n + 1 : ℕ) : ℝ) * pathRate a ^ n / 2 := by ring

/-- The complementary elementary estimate for the explicit upper barrier.
Together with `upperBarrier_le_linear_mul_pow`, it proves directly that
`ᵊₙ(a)` has fixed-`a` order `(n+1) a^(n/2)`. -/
theorem linear_mul_pow_le_upperBarrier {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    ((n + 1 : ℕ) : ℝ) * pathRate a ^ n / Real.pi ≤
      upperBarrier n a := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let α : ℝ := Real.pi / N
  have hNpos : 0 < N := by
    dsimp only [N]
    positivity
  have hNone : (1 : ℝ) < N := by
    dsimp only [N]
    exact_mod_cast (show 1 < n + 1 by omega)
  have hαpos : 0 < α := div_pos Real.pi_pos hNpos
  have hαlt : α < Real.pi := div_lt_self Real.pi_pos hNone
  have hsinPos : 0 < Real.sin α :=
    Real.sin_pos_of_pos_of_lt_pi hαpos hαlt
  have hsinLe : Real.sin α ≤ α := Real.sin_le hαpos.le
  have hrecip : N / Real.pi ≤ (Real.sin α)⁻¹ := by
    calc
      N / Real.pi = 1 / α := by
        dsimp only [α]
        field_simp [Real.pi_ne_zero, hNpos.ne']
      _ ≤ 1 / Real.sin α := one_div_le_one_div_of_le hsinPos hsinLe
      _ = (Real.sin α)⁻¹ := one_div _
  have hrecip' :
      ((n + 1 : ℕ) : ℝ) / Real.pi ≤
        (Real.sin (Real.pi / (n + 1 : ℝ)))⁻¹ := by
    simpa [N, α] using hrecip
  unfold upperBarrier
  calc
    ((n + 1 : ℕ) : ℝ) * pathRate a ^ n / Real.pi =
        pathRate a ^ n * (((n + 1 : ℕ) : ℝ) / Real.pi) := by ring
    _ ≤ pathRate a ^ n * (Real.sin (Real.pi / (n + 1 : ℝ)))⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip' (pow_nonneg (Real.sqrt_nonneg a) n)

private theorem tendsto_linear_mul_pow_zero {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * r ^ n / 2)
      atTop (nhds 0) := by
  have hself : Tendsto (fun n : ℕ => (n : ℝ) * r ^ n) atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have hpow : Tendsto (fun n : ℕ => r ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hsum :
      Tendsto (fun n : ℕ => ((n : ℝ) * r ^ n + r ^ n) / 2)
        atTop (nhds 0) := by
    simpa using (hself.add hpow).div_const 2
  apply hsum.congr'
  filter_upwards [] with n
  push_cast
  ring

/-- For each fixed `0<a<1`, the explicit upper barrier tends to zero. -/
theorem tendsto_upperBarrier_atTop_zero (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => upperBarrier n a) atTop (nhds 0) := by
  let r := pathRate a
  have hr0 : 0 ≤ r := Real.sqrt_nonneg a
  have hr1 : r < 1 := by
    dsimp only [r, pathRate]
    have hsqrt : Real.sqrt a < Real.sqrt 1 :=
      (Real.sqrt_lt_sqrt_iff ha0.le).2 ha1
    simpa using hsqrt
  have hcomparison := tendsto_linear_mul_pow_zero hr0 hr1
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact upperBarrier_nonneg_of_one_le hn a
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact upperBarrier_le_linear_mul_pow hn a
  · simpa only [r] using hcomparison

/-- For each fixed `0<a<1`, the actual attained real gap barrier tends to
zero.  The comparison is used only on the eventual tail `n≥2`. -/
theorem tendsto_gapBarrier_atTop_zero (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun n : ℕ => gapBarrier n a) atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact gapBarrier_nonneg n a (by omega)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact gapBarrier_le_upperBarrier hn a ha0
  · exact tendsto_upperBarrier_atTop_zero a ha0 ha1

end

end ConnectedPseudospectrum
