import ConnectedPseudospectrum.ChordLobes

/-!
# Outer-level domination and collision exclusion

This module proves `eq:outer-level-dominates` from the source.  It also
records the endpoint-side ordering that rules out a folded-variable collision
on every positive noncentral chord, without assuming monotonicity of the
abscissa parametrization.
-/

namespace ConnectedPseudospectrum

noncomputable section

/-- The angular radical-to-sine ratio used to compare inner and outer chord
levels. -/
def chordAngleFactor (a t : ℝ) : ℝ :=
  halfTrigRadical a t / Real.sin t

theorem chordAngleFactor_strictAntiOn
    {a t₁ t₂ : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (ht₁0 : 0 < t₁) (ht12 : t₁ < t₂)
    (ht₂ : t₂ ≤ Real.pi / 2) :
    chordAngleFactor a t₂ < chordAngleFactor a t₁ := by
  let h := pathLogParameter a
  let c := Real.cosh h
  let p₁ := halfTrigRadical a t₁
  let p₂ := halfTrigRadical a t₂
  let s₁ := Real.sin t₁
  let s₂ := Real.sin t₂
  have hh : 0 < h := pathLogParameter_pos ha0 ha1
  have hc : 1 < c := by
    dsimp [c]
    exact Real.one_lt_cosh.mpr hh.ne'
  have ht₂0 : 0 < t₂ := ht₁0.trans ht12
  have ht₂pi : t₂ < Real.pi := by
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith
  have ht₁pi : t₁ < Real.pi := ht12.trans ht₂pi
  have hs₁ : 0 < s₁ := by
    dsimp [s₁]
    exact Real.sin_pos_of_pos_of_lt_pi ht₁0 ht₁pi
  have hs₂ : 0 < s₂ := by
    dsimp [s₂]
    exact Real.sin_pos_of_pos_of_lt_pi ht₂0 ht₂pi
  have hslt : s₁ < s₂ := by
    dsimp [s₁, s₂]
    apply Real.strictMonoOn_sin
    · constructor <;> linarith [Real.pi_pos]
    · constructor <;> linarith [Real.pi_pos]
    · exact ht12
  have hp₁sq : p₁ ^ 2 = c ^ 2 - Real.cos t₁ ^ 2 := by
    exact halfTrigRadical_sq a t₁
  have hp₂sq : p₂ ^ 2 = c ^ 2 - Real.cos t₂ ^ 2 := by
    exact halfTrigRadical_sq a t₂
  have htrig₁ := Real.sin_sq_add_cos_sq t₁
  have htrig₂ := Real.sin_sq_add_cos_sq t₂
  have hp₁sq' : p₁ ^ 2 = (c ^ 2 - 1) + s₁ ^ 2 := by
    rw [hp₁sq]
    dsimp [s₁]
    nlinarith
  have hp₂sq' : p₂ ^ 2 = (c ^ 2 - 1) + s₂ ^ 2 := by
    rw [hp₂sq]
    dsimp [s₂]
    nlinarith
  have hrad₁ : 0 < c ^ 2 - Real.cos t₁ ^ 2 := by
    nlinarith [Real.neg_one_le_cos t₁, Real.cos_le_one t₁]
  have hrad₂ : 0 < c ^ 2 - Real.cos t₂ ^ 2 := by
    nlinarith [Real.neg_one_le_cos t₂, Real.cos_le_one t₂]
  have hp₁ : 0 < p₁ := by
    dsimp [p₁, halfTrigRadical]
    exact Real.sqrt_pos.2 hrad₁
  have hp₂ : 0 < p₂ := by
    dsimp [p₂, halfTrigRadical]
    exact Real.sqrt_pos.2 hrad₂
  have hcSq : 0 < c ^ 2 - 1 := by nlinarith
  have hsSq : s₁ ^ 2 < s₂ ^ 2 := by nlinarith
  have hsquares : (p₂ * s₁) ^ 2 < (p₁ * s₂) ^ 2 := by
    rw [mul_pow, mul_pow, hp₁sq', hp₂sq']
    calc
      ((c ^ 2 - 1) + s₂ ^ 2) * s₁ ^ 2 =
          (c ^ 2 - 1) * s₁ ^ 2 + s₁ ^ 2 * s₂ ^ 2 := by ring
      _ = s₁ ^ 2 * s₂ ^ 2 + (c ^ 2 - 1) * s₁ ^ 2 := by ring
      _ < s₁ ^ 2 * s₂ ^ 2 + (c ^ 2 - 1) * s₂ ^ 2 :=
        add_lt_add_right (mul_lt_mul_of_pos_left hsSq hcSq)
          (s₁ ^ 2 * s₂ ^ 2)
      _ = (c ^ 2 - 1) * s₂ ^ 2 + s₁ ^ 2 * s₂ ^ 2 := by ring
      _ = ((c ^ 2 - 1) + s₁ ^ 2) * s₂ ^ 2 := by ring
  have hcross : p₂ * s₁ < p₁ * s₂ := by
    exact (sq_lt_sq₀ (mul_pos hp₂ hs₁).le
      (mul_pos hp₁ hs₂).le).mp hsquares
  change p₂ / s₂ < p₁ / s₁
  exact (div_lt_div_iff₀ hs₂ hs₁).2 (by simpa [mul_comm] using hcross)

theorem chordPhi_eq_chordAngleFactor_mul_abs
    {K : ℕ} (hK : 2 ≤ K) (a t : ℝ)
    (ht0 : 0 ≤ t) (htpi : t ≤ Real.pi) (hsin : Real.sin t ≠ 0) :
    chordPhi K a t =
      chordAngleFactor a t * |Real.sin (K * t)| := by
  rw [chordPhi_eq_sine_quotient a t hK ht0 htpi hsin]
  unfold chordAngleFactor
  field_simp [hsin]

theorem chordPhi_inner_lt_remainder
    {K j : ℕ} (hK : 2 ≤ K) (hj : 0 < j)
    {a θ : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hθLower : (j : ℝ) * Real.pi / K < θ)
    (hθUpper : θ < (j + 1 : ℕ) * Real.pi / K)
    (hθhalf : θ ≤ Real.pi / 2) :
    chordPhi K a θ <
      chordPhi K a (θ - (j : ℝ) * Real.pi / K) := by
  let t := θ - (j : ℝ) * Real.pi / K
  have hKpos : (0 : ℝ) < K := by positivity
  have hKne : (K : ℝ) ≠ 0 := hKpos.ne'
  have hjpos : 0 < (j : ℝ) * Real.pi / K := by positivity
  have ht0 : 0 < t := by
    dsimp [t]
    linarith
  have htθ : t < θ := by
    dsimp [t]
    linarith
  have htUpper : t < Real.pi / K := by
    dsimp [t]
    push_cast at hθUpper
    have hsplit :
        ((j : ℝ) + 1) * Real.pi / K =
          (j : ℝ) * Real.pi / K + Real.pi / K := by ring
    rw [hsplit] at hθUpper
    linarith
  have hθ0 : 0 < θ := ht0.trans htθ
  have hθpi : θ < Real.pi := by
    linarith [Real.pi_pos]
  have htpi : t < Real.pi := htθ.trans hθpi
  have hfactor : chordAngleFactor a θ < chordAngleFactor a t :=
    chordAngleFactor_strictAntiOn ha0 ha1 ht0 htθ hθhalf
  have harg : (K : ℝ) * t = K * θ - j * Real.pi := by
    dsimp [t]
    field_simp [hKne]
  have habs : |Real.sin (K * t)| = |Real.sin (K * θ)| := by
    rw [harg, Real.sin_sub_nat_mul_pi, abs_mul, abs_pow]
    norm_num
  have hsinK : Real.sin (K * θ) ≠ 0 := by
    intro hzero
    obtain ⟨q, hq⟩ := Real.sin_eq_zero_iff.mp hzero
    have hLowerMul : (j : ℝ) * Real.pi < θ * K := by
      exact (div_lt_iff₀ hKpos).mp hθLower
    have hUpperMul : θ * K < ((j + 1 : ℕ) : ℝ) * Real.pi := by
      exact (lt_div_iff₀ hKpos).mp hθUpper
    have hqeq : (q : ℝ) * Real.pi = θ * K := by
      simpa only [mul_comm] using hq
    have hjqReal : (j : ℝ) < q := by
      exact lt_of_mul_lt_mul_right (by
        calc
          (j : ℝ) * Real.pi < θ * K := hLowerMul
          _ = (q : ℝ) * Real.pi := hqeq.symm) Real.pi_pos.le
    have hqjReal : (q : ℝ) < (j + 1 : ℕ) := by
      exact lt_of_mul_lt_mul_right (by
        calc
          (q : ℝ) * Real.pi = θ * K := hqeq
          _ < ((j + 1 : ℕ) : ℝ) * Real.pi := hUpperMul) Real.pi_pos.le
    have hjq : (j : ℤ) < q := by exact_mod_cast hjqReal
    have hqj : q < (j : ℤ) + 1 := by exact_mod_cast hqjReal
    omega
  have hsint : Real.sin t ≠ 0 := by
    exact (Real.sin_pos_of_pos_of_lt_pi ht0 htpi).ne'
  rw [chordPhi_eq_chordAngleFactor_mul_abs hK a θ hθ0.le hθpi.le
      (Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi).ne',
    chordPhi_eq_chordAngleFactor_mul_abs hK a t ht0.le htpi.le hsint,
    habs]
  exact mul_lt_mul_of_pos_right hfactor (abs_pos.mpr hsinK)

theorem chordPhi_inner_lt_outerLobeMaximum
    {K j : ℕ} (hK : 2 ≤ K) (hj : 0 < j)
    {a θ p : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hθLower : (j : ℝ) * Real.pi / K < θ)
    (hθUpper : θ < (j + 1 : ℕ) * Real.pi / K)
    (hθhalf : θ ≤ Real.pi / 2)
    (hpMax : IsMaxOn (chordLobeWeight K a)
      (Set.Icc (Real.cos (Real.pi / K))
        (Real.cosh (pathLogParameter a))) p) :
    chordPhi K a θ < chordLobeWeight K a p := by
  let t := θ - (j : ℝ) * Real.pi / K
  have hKpos : (0 : ℝ) < K := by positivity
  have ht0 : 0 < t := by
    dsimp [t]
    linarith
  have htUpper : t < Real.pi / K := by
    dsimp [t]
    push_cast at hθUpper
    have hsplit :
        ((j : ℝ) + 1) * Real.pi / K =
          (j : ℝ) * Real.pi / K + Real.pi / K := by ring
    rw [hsplit] at hθUpper
    linarith
  have hpiKle : Real.pi / (K : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hKpos]
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
    nlinarith [Real.pi_pos]
  have hcosLower : Real.cos (Real.pi / K) < Real.cos t := by
    exact Real.cos_lt_cos_of_nonneg_of_le_pi ht0.le hpiKle htUpper
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha0 ha1
  have hcOne : 1 < Real.cosh (pathLogParameter a) :=
    Real.one_lt_cosh.mpr hh.ne'
  have hcosMem : Real.cos t ∈
      Set.Icc (Real.cos (Real.pi / K))
        (Real.cosh (pathLogParameter a)) :=
    ⟨hcosLower.le, (Real.cos_le_one t).trans hcOne.le⟩
  have hmax := hpMax hcosMem
  have hinner := chordPhi_inner_lt_remainder hK hj ha0 ha1
    hθLower hθUpper hθhalf
  exact hinner.trans_le (by
    rw [← chordLobeWeight_cos K a t]
    exact hmax)

theorem outerEndpointSide_gt_innerCos
    {K j : ℕ} (hK : 2 ≤ K) (hj : 0 < j)
    {a θ p z : ℝ}
    (hθLower : (j : ℝ) * Real.pi / K < θ)
    (hθhalf : θ ≤ Real.pi / 2)
    (hp : p ∈ Set.Ioo (Real.cos (Real.pi / K))
      (Real.cosh (pathLogParameter a)))
    (hz : p < z) :
    Real.cos θ < z := by
  have hKpos : (0 : ℝ) < K := by positivity
  have hjcast : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hbase : Real.pi / (K : ℝ) ≤ (j : ℝ) * Real.pi / K := by
    rw [div_le_div_iff_of_pos_right hKpos]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hjcast Real.pi_pos.le
  have hpiTheta : Real.pi / (K : ℝ) < θ := hbase.trans_lt hθLower
  have hpiKnonneg : 0 ≤ Real.pi / (K : ℝ) := by positivity
  have hθpi : θ ≤ Real.pi := by linarith [Real.pi_pos]
  have hcos : Real.cos θ < Real.cos (Real.pi / K) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hpiKnonneg hθpi hpiTheta
  exact (hcos.trans hp.1).trans hz

theorem outerEndpointSide_foldedVariables_ne
    {K j : ℕ} (hK : 2 ≤ K) (hj : 0 < j)
    {a θ p z : ℝ}
    (hθLower : (j : ℝ) * Real.pi / K < θ)
    (hθhalf : θ ≤ Real.pi / 2)
    (hp : p ∈ Set.Ioo (Real.cos (Real.pi / K))
      (Real.cosh (pathLogParameter a)))
    (hz : p < z) :
    z ^ 2 ≠ Real.cos θ ^ 2 := by
  have hgt := outerEndpointSide_gt_innerCos hK hj hθLower hθhalf hp hz
  have hθ0 : 0 < θ := by
    have hleft : 0 ≤ (j : ℝ) * Real.pi / K := by positivity
    exact hleft.trans_lt hθLower
  have hcosNonneg : 0 ≤ Real.cos θ := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · linarith [Real.pi_pos, hθ0]
    · exact hθhalf
  intro heq
  nlinarith

end

end ConnectedPseudospectrum
