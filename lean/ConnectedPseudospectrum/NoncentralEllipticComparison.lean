import ConnectedPseudospectrum.NoncentralHyperbolicComparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The analytic core of the noncentral elliptic comparison

This module supplies the elliptic case culminating in
`eq:elliptic-height-increase`.  It isolates the strict rescaled chord-factor
monotonicity and gives
the level-generic rightmost-inner-solution theorem needed by both outer
coordinate charts.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- The rightmost-return theorem with an arbitrary positive level.  This is
the level-generic form of the compactness/IVT argument used in the hyperbolic
case. -/
theorem existsUnique_rightmostInnerSolutionAtLevel
    (d : PositiveHalfGap) (θ0 : d.Angle) (level : ℝ)
    (hlevelPos : 0 < level)
    (hlevel : level < chordPhi d.K d.a θ0) :
    ∃! θhat : d.Angle,
      IsRightmostInnerSolution d θ0 level θhat := by
  let S : Set ℝ :=
    Icc (θ0 : ℝ) d.angleUpper ∩
      {t : ℝ | chordPhi d.K d.a t = level}
  have hrightZero : chordPhi d.K d.a d.angleUpper = 0 := by
    simpa only [PositiveHalfGap.angleUpper] using
      chordPhi_nodal (K := d.K) (k := d.j + 1) d.hK
        (Nat.succ_pos d.j) d.hjUpper d.a
  have hlevelRange : level ∈
      Icc (chordPhi d.K d.a d.angleUpper)
        (chordPhi d.K d.a (θ0 : ℝ)) := by
    rw [hrightZero]
    exact ⟨hlevelPos.le, hlevel.le⟩
  have hcontinuous : ContinuousOn (chordPhi d.K d.a)
      (Icc (θ0 : ℝ) d.angleUpper) :=
    (continuous_chordPhi d.K d.a).continuousOn
  obtain ⟨t, ht, htLevel⟩ :=
    intermediate_value_Icc' θ0.2.2 hcontinuous hlevelRange
  have hSne : S.Nonempty := by
    exact ⟨t, ht, htLevel⟩
  have hclosedLevel : IsClosed {t : ℝ | chordPhi d.K d.a t = level} :=
    isClosed_eq (continuous_chordPhi d.K d.a) continuous_const
  have hScompact : IsCompact S :=
    isCompact_Icc.inter_right hclosedLevel
  obtain ⟨tmax, htmaxS, htmax⟩ :=
    hScompact.exists_isMaxOn hSne continuous_id.continuousOn
  have htmaxBounds : tmax ∈ Icc (θ0 : ℝ) d.angleUpper := htmaxS.1
  let θhat : d.Angle :=
    ⟨tmax, θ0.2.1.trans htmaxBounds.1, htmaxBounds.2⟩
  have hθhatLevel : chordPhi d.K d.a θhat = level := htmaxS.2
  have hθ0lt : (θ0 : ℝ) < θhat := by
    refine lt_of_le_of_ne htmaxBounds.1 ?_
    intro heq
    have hEq : chordPhi d.K d.a θ0 = level := by
      simpa only [θhat, heq] using hθhatLevel
    exact (ne_of_lt hlevel) hEq.symm
  have hθhatUpper : (θhat : ℝ) < d.angleUpper := by
    refine lt_of_le_of_ne htmaxBounds.2 ?_
    intro heq
    have hzero : level = 0 := by
      calc
        level = chordPhi d.K d.a θhat := hθhatLevel.symm
        _ = chordPhi d.K d.a d.angleUpper := by rw [heq]
        _ = 0 := hrightZero
    exact (ne_of_gt hlevelPos) hzero
  have hgreatest : ∀ φ : d.Angle,
      (θ0 : ℝ) ≤ φ →
      chordPhi d.K d.a φ = level →
      (φ : ℝ) ≤ θhat := by
    intro φ hθ0φ hφLevel
    have hφS : (φ : ℝ) ∈ S :=
      ⟨⟨hθ0φ, φ.2.2⟩, hφLevel⟩
    simpa only [id_eq] using htmax hφS
  refine ⟨θhat, ⟨hθ0lt, hθhatUpper, hθhatLevel, hgreatest⟩, ?_⟩
  intro φ hφ
  apply Subtype.ext
  apply le_antisymm
  · exact hgreatest φ hφ.1.le hφ.2.2.1
  · exact hφ.2.2.2 θhat hθ0lt.le hθhatLevel

/-- The first positive factor in the source's expression for
`t * d_h(t)`. -/
def chordAngleCotFactor (t : ℝ) : ℝ :=
  t * Real.cos t / Real.sin t

/-- The second positive factor in the source's expression for
`t * d_h(t)`. -/
def chordAngleSineFactor (a t : ℝ) : ℝ :=
  Real.sinh (pathLogParameter a) ^ 2 /
    (Real.sinh (pathLogParameter a) ^ 2 + Real.sin t ^ 2)

/-- The source's angular decay
`d_h(t)=sinh(h)^2 cot(t)/(sinh(h)^2+sin(t)^2)`. -/
def chordAngleDecay (a t : ℝ) : ℝ :=
  Real.sinh (pathLogParameter a) ^ 2 * Real.cos t /
    (Real.sin t *
      (Real.sinh (pathLogParameter a) ^ 2 + Real.sin t ^ 2))

/-- The product whose strict decrease drives the rescaled ratio. -/
def chordAngleScaledDecay (a t : ℝ) : ℝ :=
  t * chordAngleDecay a t

theorem chordAngleScaledDecay_eq_factors
    {a t : ℝ} (hsin : Real.sin t ≠ 0)
    (hden : Real.sinh (pathLogParameter a) ^ 2 + Real.sin t ^ 2 ≠ 0) :
    chordAngleScaledDecay a t =
      chordAngleCotFactor t * chordAngleSineFactor a t := by
  unfold chordAngleScaledDecay chordAngleDecay chordAngleCotFactor
    chordAngleSineFactor
  field_simp [hsin, hden]

theorem chordAngleCotFactor_pos
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < chordAngleCotFactor t := by
  unfold chordAngleCotFactor
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht.1
      (ht.2.trans (half_lt_self Real.pi_pos))
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, ht.1], ht.2⟩
  exact div_pos (mul_pos ht.1 hcos) hsin

theorem chordAngleSineFactor_pos
    {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < chordAngleSineFactor a t := by
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha0 ha1
  have hH : 0 < Real.sinh (pathLogParameter a) ^ 2 :=
    sq_pos_of_pos (Real.sinh_pos_iff.mpr hh)
  unfold chordAngleSineFactor
  exact div_pos hH (add_pos_of_pos_of_nonneg hH (sq_nonneg _))

theorem chordAngleFactor_pos_of_pos_of_le_half
    {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (ht0 : 0 < t) (hthalf : t ≤ Real.pi / 2) :
    0 < chordAngleFactor a t := by
  unfold chordAngleFactor
  exact div_pos (halfTrigRadical_pos_of_parameter ha0 ha1 t)
    (Real.sin_pos_of_pos_of_lt_pi ht0
      (hthalf.trans_lt (half_lt_self Real.pi_pos)))

theorem hasDerivAt_chordAngleCotFactor
    {t : ℝ} (hsin : Real.sin t ≠ 0) :
    HasDerivAt chordAngleCotFactor
      (((Real.cos t - t * Real.sin t) * Real.sin t -
          (t * Real.cos t) * Real.cos t) / Real.sin t ^ 2) t := by
  unfold chordAngleCotFactor
  convert ((hasDerivAt_id t).mul (Real.hasDerivAt_cos t)).div
    (Real.hasDerivAt_sin t) hsin using 1
  simp only [Pi.mul_apply, id_eq]
  ring_nf

theorem chordAngleCotFactor_strictAntiOn :
    StrictAntiOn chordAngleCotFactor (Ioo (0 : ℝ) (Real.pi / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) (Real.pi / 2))
  · intro t ht
    have htIoo : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := ht
    have hsin : Real.sin t ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi htIoo.1
        (htIoo.2.trans (half_lt_self Real.pi_pos))).ne'
    exact (hasDerivAt_chordAngleCotFactor hsin).continuousAt.continuousWithinAt
  · intro t ht
    have htIoo : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
      simpa only [interior_Ioo] using ht
    have hsinPos : 0 < Real.sin t :=
      Real.sin_pos_of_pos_of_lt_pi htIoo.1
        (htIoo.2.trans (half_lt_self Real.pi_pos))
    have hsinCos : Real.sin t * Real.cos t < t := by
      have htwo : 0 < 2 * t := mul_pos (by norm_num) htIoo.1
      have hs := Real.sin_lt htwo
      rw [Real.sin_two_mul] at hs
      linarith
    have hnum :
        (Real.cos t - t * Real.sin t) * Real.sin t -
            (t * Real.cos t) * Real.cos t < 0 := by
      calc
        (Real.cos t - t * Real.sin t) * Real.sin t -
              (t * Real.cos t) * Real.cos t =
            Real.sin t * Real.cos t -
              t * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
        _ = Real.sin t * Real.cos t - t := by
          rw [Real.sin_sq_add_cos_sq]
          ring
        _ < 0 := sub_neg.mpr hsinCos
    have hderiv := hasDerivAt_chordAngleCotFactor hsinPos.ne'
    rw [hderiv.deriv]
    exact div_neg_of_neg_of_pos hnum (sq_pos_of_pos hsinPos)

theorem hasDerivAt_chordAngleSineFactor
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    HasDerivAt (chordAngleSineFactor a)
      ((-(Real.sinh (pathLogParameter a) ^ 2 *
          (2 * Real.sin t * Real.cos t))) /
        (Real.sinh (pathLogParameter a) ^ 2 + Real.sin t ^ 2) ^ 2) t := by
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha0 ha1
  have hH : 0 < Real.sinh (pathLogParameter a) ^ 2 :=
    sq_pos_of_pos (Real.sinh_pos_iff.mpr hh)
  have hden :
      Real.sinh (pathLogParameter a) ^ 2 + Real.sin t ^ 2 ≠ 0 := by
    exact (add_pos_of_pos_of_nonneg hH (sq_nonneg _)).ne'
  have hdenDeriv :
      HasDerivAt
        (fun x : ℝ => Real.sinh (pathLogParameter a) ^ 2 + Real.sin x ^ 2)
        (2 * Real.sin t * Real.cos t) t := by
    convert ((Real.hasDerivAt_sin t).pow 2).const_add
      (Real.sinh (pathLogParameter a) ^ 2) using 1
    ring
  convert (hasDerivAt_const t (Real.sinh (pathLogParameter a) ^ 2)).div
    hdenDeriv hden using 1
  ring

theorem chordAngleSineFactor_strictAntiOn
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    StrictAntiOn (chordAngleSineFactor a)
      (Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha0 ha1
  have hH : 0 < Real.sinh (pathLogParameter a) ^ 2 :=
    sq_pos_of_pos (Real.sinh_pos_iff.mpr hh)
  apply strictAntiOn_of_deriv_neg (convex_Ioo (0 : ℝ) (Real.pi / 2))
  · intro t _
    exact (hasDerivAt_chordAngleSineFactor ha0 ha1 t).continuousAt.continuousWithinAt
  · intro t ht
    have htIoo : t ∈ Ioo (0 : ℝ) (Real.pi / 2) := by
      simpa only [interior_Ioo] using ht
    have hsin : 0 < Real.sin t :=
      Real.sin_pos_of_pos_of_lt_pi htIoo.1
        (htIoo.2.trans (half_lt_self Real.pi_pos))
    have hcos : 0 < Real.cos t :=
      Real.cos_pos_of_mem_Ioo
        ⟨by nlinarith [Real.pi_pos, htIoo.1], htIoo.2⟩
    have hden :
        0 < (Real.sinh (pathLogParameter a) ^ 2 + Real.sin t ^ 2) ^ 2 := by
      positivity
    have hderiv := hasDerivAt_chordAngleSineFactor ha0 ha1 t
    rw [hderiv.deriv]
    have hnumPos :
        0 < Real.sinh (pathLogParameter a) ^ 2 *
          (2 * Real.sin t * Real.cos t) := by
      exact mul_pos hH (mul_pos (mul_pos (by norm_num) hsin) hcos)
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hnumPos) hden

theorem chordAngleScaledDecay_strictAntiOn
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    StrictAntiOn (chordAngleScaledDecay a)
      (Ioo (0 : ℝ) (Real.pi / 2)) := by
  intro s hs t ht hst
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha0 ha1
  have hsSin : Real.sin s ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hs.1
      (hs.2.trans (half_lt_self Real.pi_pos))).ne'
  have htSin : Real.sin t ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi ht.1
      (ht.2.trans (half_lt_self Real.pi_pos))).ne'
  have hsDen :
      Real.sinh (pathLogParameter a) ^ 2 + Real.sin s ^ 2 ≠ 0 := by
    positivity
  have htDen :
      Real.sinh (pathLogParameter a) ^ 2 + Real.sin t ^ 2 ≠ 0 := by
    positivity
  rw [chordAngleScaledDecay_eq_factors htSin htDen,
    chordAngleScaledDecay_eq_factors hsSin hsDen]
  have hcot := chordAngleCotFactor_strictAntiOn hs ht hst
  have hsine := chordAngleSineFactor_strictAntiOn ha0 ha1 hs ht hst
  exact (mul_lt_mul_of_pos_right hcot
      (chordAngleSineFactor_pos ha0 ha1)).trans
    (mul_lt_mul_of_pos_left hsine (chordAngleCotFactor_pos hs))

/-- A logarithmic representative of `chordAngleFactor`; it avoids taking a
derivative through a square root. -/
def chordAngleLogFactor (a t : ℝ) : ℝ :=
  Real.log
      (Real.sinh (pathLogParameter a) ^ 2 + Real.sin t ^ 2) / 2 -
    Real.log (Real.sin t)

theorem hasDerivAt_chordAngleLogFactor
    {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (ht0 : 0 < t) (hthalf : t ≤ Real.pi / 2) :
    HasDerivAt (chordAngleLogFactor a) (-chordAngleDecay a t) t := by
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha0 ha1
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht0
      (hthalf.trans_lt (half_lt_self Real.pi_pos))
  have hinner :
      0 < Real.sinh (pathLogParameter a) ^ 2 + Real.sin t ^ 2 := by
    positivity
  have hinnerDeriv :
      HasDerivAt
        (fun x : ℝ => Real.sinh (pathLogParameter a) ^ 2 + Real.sin x ^ 2)
        (2 * Real.sin t * Real.cos t) t := by
    convert ((Real.hasDerivAt_sin t).pow 2).const_add
      (Real.sinh (pathLogParameter a) ^ 2) using 1
    ring
  unfold chordAngleLogFactor
  convert ((hinnerDeriv.log hinner.ne').div_const 2).sub
      ((Real.hasDerivAt_sin t).log hsin.ne') using 1
  unfold chordAngleDecay
  field_simp
  ring

theorem log_chordAngleFactor_eq
    {a t : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (ht0 : 0 < t) (hthalf : t ≤ Real.pi / 2) :
    Real.log (chordAngleFactor a t) = chordAngleLogFactor a t := by
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht0
      (hthalf.trans_lt (half_lt_self Real.pi_pos))
  have hrad : 0 < halfTrigRadical a t :=
    halfTrigRadical_pos_of_parameter ha0 ha1 t
  rw [chordAngleFactor, Real.log_div hrad.ne' hsin.ne']
  unfold halfTrigRadical chordAngleLogFactor
  rw [Real.log_sqrt (halfTrigRadicand_nonneg a t),
    chordRadicand_cos_eq_sinh_sq_add_sin_sq]

/-- The logarithm of the rescaled chord-factor ratio. -/
def chordAngleRescaledLogRatio (κ a t : ℝ) : ℝ :=
  chordAngleLogFactor a (t / κ) - chordAngleLogFactor a t

theorem hasDerivAt_chordAngleRescaledLogRatio
    {κ a t : ℝ} (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1)
    (ha0 : 0 < a) (ha1 : a < 1)
    (ht0 : 0 < t) (htUpper : t / κ ≤ Real.pi / 2) :
    HasDerivAt (chordAngleRescaledLogRatio κ a)
      (chordAngleDecay a t - κ⁻¹ * chordAngleDecay a (t / κ)) t := by
  have hscaled0 : 0 < t / κ := div_pos ht0 hκ0
  have hinner := hasDerivAt_chordAngleLogFactor ha0 ha1 hscaled0 htUpper
  have htEq : t = κ * (t / κ) := by
    field_simp [hκ0.ne']
  have htHalf : t ≤ Real.pi / 2 := by
    rw [htEq]
    have hprod := mul_le_mul hκ1 htUpper hscaled0.le
      (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hprod
  have houter := hasDerivAt_chordAngleLogFactor ha0 ha1 ht0 htHalf
  have hlinear : HasDerivAt (fun x : ℝ => x / κ) (1 / κ) t := by
    simpa only [one_div] using (hasDerivAt_id t).div_const κ
  unfold chordAngleRescaledLogRatio
  convert (hinner.comp t hlinear).sub houter using 1
  field_simp
  ring

theorem chordAngleRescaledLogRatio_deriv_pos
    {κ a t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (ha0 : 0 < a) (ha1 : a < 1)
    (ht0 : 0 < t) (htUpper : t / κ < Real.pi / 2) :
    0 < chordAngleDecay a t - κ⁻¹ * chordAngleDecay a (t / κ) := by
  have hscaled0 : 0 < t / κ := div_pos ht0 hκ0
  have htScaled : t < t / κ := by
    apply (lt_div_iff₀ hκ0).2
    nlinarith
  have hanti := chordAngleScaledDecay_strictAntiOn ha0 ha1
    ⟨ht0, htScaled.trans htUpper⟩ ⟨hscaled0, htUpper⟩ htScaled
  have hrewrite :
      (t / κ) * chordAngleDecay a (t / κ) =
        t * (κ⁻¹ * chordAngleDecay a (t / κ)) := by
    field_simp [hκ0.ne']
  unfold chordAngleScaledDecay at hanti
  rw [hrewrite] at hanti
  exact sub_pos.mpr (lt_of_mul_lt_mul_left hanti ht0.le)

theorem chordAngleRescaledLogRatio_strictMonoOn
    {κ a : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (ha0 : 0 < a) (ha1 : a < 1) :
    StrictMonoOn (chordAngleRescaledLogRatio κ a)
      (Ioc (0 : ℝ) (κ * (Real.pi / 2))) := by
  apply strictMonoOn_of_deriv_pos
    (convex_Ioc (0 : ℝ) (κ * (Real.pi / 2)))
  · intro t ht
    have htUpper : t / κ ≤ Real.pi / 2 := by
      apply (div_le_iff₀ hκ0).2
      simpa only [mul_comm] using ht.2
    exact (hasDerivAt_chordAngleRescaledLogRatio hκ0 hκ1.le ha0 ha1 ht.1
      htUpper).continuousAt.continuousWithinAt
  · intro t ht
    have htIoo : t ∈ Ioo (0 : ℝ) (κ * (Real.pi / 2)) := by
      simpa only [interior_Ioc] using ht
    have htUpper : t / κ < Real.pi / 2 := by
      apply (div_lt_iff₀ hκ0).2
      simpa only [mul_comm] using htIoo.2
    have hderiv := hasDerivAt_chordAngleRescaledLogRatio hκ0 hκ1.le ha0 ha1
      htIoo.1 htUpper.le
    rw [hderiv.deriv]
    exact chordAngleRescaledLogRatio_deriv_pos hκ0 hκ1 ha0 ha1
      htIoo.1 htUpper

/-- The actual rescaled chord-factor ratio in equation (1319). -/
def chordAngleRescaledRatio (κ a t : ℝ) : ℝ :=
  chordAngleFactor a (t / κ) / chordAngleFactor a t

theorem log_chordAngleRescaledRatio_eq
    {κ a t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (ha0 : 0 < a) (ha1 : a < 1)
    (ht0 : 0 < t) (htUpper : t / κ ≤ Real.pi / 2) :
    Real.log (chordAngleRescaledRatio κ a t) =
      chordAngleRescaledLogRatio κ a t := by
  have hscaled0 : 0 < t / κ := div_pos ht0 hκ0
  have htHalf : t ≤ Real.pi / 2 := by
    have htEq : t = κ * (t / κ) := by field_simp [hκ0.ne']
    rw [htEq]
    have hprod := mul_le_mul hκ1 htUpper hscaled0.le
      (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hprod
  have hnum : 0 < chordAngleFactor a (t / κ) :=
    chordAngleFactor_pos_of_pos_of_le_half ha0 ha1 hscaled0 htUpper
  have hden : 0 < chordAngleFactor a t :=
    chordAngleFactor_pos_of_pos_of_le_half ha0 ha1 ht0 htHalf
  unfold chordAngleRescaledRatio chordAngleRescaledLogRatio
  rw [Real.log_div hnum.ne' hden.ne',
    log_chordAngleFactor_eq ha0 ha1 hscaled0 htUpper,
    log_chordAngleFactor_eq ha0 ha1 ht0 htHalf]

/-- Strict monotonicity of the source's rescaled factor ratio
`F_h(t/kappa)/F_h(t)` on its full positive half-angle domain. -/
theorem chordAngleRescaledRatio_strictMonoOn
    {κ a : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (ha0 : 0 < a) (ha1 : a < 1) :
    StrictMonoOn (chordAngleRescaledRatio κ a)
      (Ioc (0 : ℝ) (κ * (Real.pi / 2))) := by
  intro s hs t ht hst
  have hsUpper : s / κ ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hκ0).2
    simpa only [mul_comm] using hs.2
  have htUpper : t / κ ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hκ0).2
    simpa only [mul_comm] using ht.2
  have hlog := chordAngleRescaledLogRatio_strictMonoOn
    hκ0 hκ1 ha0 ha1 hs ht hst
  rw [← log_chordAngleRescaledRatio_eq hκ0 hκ1.le ha0 ha1 hs.1 hsUpper,
    ← log_chordAngleRescaledRatio_eq hκ0 hκ1.le ha0 ha1 ht.1 htUpper] at hlog
  have htPos : 0 < chordAngleRescaledRatio κ a t := by
    unfold chordAngleRescaledRatio
    exact div_pos
      (chordAngleFactor_pos_of_pos_of_le_half ha0 ha1
        (div_pos ht.1 hκ0) htUpper)
      (chordAngleFactor_pos_of_pos_of_le_half ha0 ha1 ht.1
        (by
          have htEq : t = κ * (t / κ) := by field_simp [hκ0.ne']
          rw [htEq]
          have hprod := mul_le_mul hκ1.le htUpper
            (div_pos ht.1 hκ0).le (by norm_num : (0 : ℝ) ≤ 1)
          simpa only [one_mul] using hprod))
  by_contra hnot
  have hle : chordAngleRescaledRatio κ a t ≤
      chordAngleRescaledRatio κ a s := le_of_not_gt hnot
  have hlogLe := Real.log_le_log htPos hle
  exact (not_lt_of_ge hlogLe) hlog

/-- Exact cancellation of the common Chebyshev sine factor under
`N * (t/kappa) = (N+1) * t`. -/
theorem chordPhi_rescaled_successor_ratio_eq
    {N : ℕ} (hN : 2 ≤ N) {a t : ℝ}
    (ht0 : 0 < t)
    (htUpper : t / noncentralScale N ≤ Real.pi / 2)
    (hphase : Real.sin (((N + 1 : ℕ) : ℝ) * t) ≠ 0) :
    chordPhi N a (t / noncentralScale N) /
        chordPhi (N + 1) a t =
      chordAngleRescaledRatio (noncentralScale N) a t := by
  have hκ0 : 0 < noncentralScale N :=
    noncentralScale_pos ((by norm_num : 1 ≤ 2).trans hN)
  have hscaled0 : 0 < t / noncentralScale N := div_pos ht0 hκ0
  have htHalf : t ≤ Real.pi / 2 := by
    have htEq : t = noncentralScale N * (t / noncentralScale N) := by
      field_simp [hκ0.ne']
    rw [htEq]
    have hprod := mul_le_mul (noncentralScale_lt_one N).le htUpper
      hscaled0.le (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hprod
  have hmultiple :
      (N : ℝ) * (t / noncentralScale N) =
        ((N + 1 : ℕ) : ℝ) * t := by
    unfold noncentralScale
    field_simp
  have hsinT : Real.sin t ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi ht0
      (htHalf.trans_lt (half_lt_self Real.pi_pos))).ne'
  have hsinScaledBase : Real.sin (t / noncentralScale N) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hscaled0
      (htUpper.trans_lt (half_lt_self Real.pi_pos))).ne'
  rw [chordPhi_eq_sine_quotient a (t / noncentralScale N) hN
      hscaled0.le (htUpper.trans (half_le_self Real.pi_pos.le))
      hsinScaledBase,
    chordPhi_eq_sine_quotient a t (hN.trans (Nat.le_succ N))
      ht0.le (htHalf.trans (half_le_self Real.pi_pos.le)) hsinT,
    hmultiple]
  have hphaseComm :
      Real.sin (t * ((N + 1 : ℕ) : ℝ)) ≠ 0 := by
    simpa only [mul_comm] using hphase
  unfold chordAngleRescaledRatio chordAngleFactor
  field_simp [hsinT, hsinScaledBase, abs_ne_zero.mpr hphaseComm]

/-- The explicit angular logarithmic derivative `Lambda_K`. -/
def chordPhiLogSlope (K : ℕ) (a t : ℝ) : ℝ :=
  -chordAngleDecay a t +
    (K : ℝ) * Real.cos ((K : ℝ) * t) /
      Real.sin ((K : ℝ) * t)

theorem log_chordPhi_eq_logFactor_add_logSin
    {K : ℕ} (hK : 2 ≤ K) {a t : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (ht0 : 0 < t) (hthalf : t ≤ Real.pi / 2)
    (hphase : Real.sin ((K : ℝ) * t) ≠ 0) :
    Real.log (chordPhi K a t) =
      chordAngleLogFactor a t + Real.log (Real.sin ((K : ℝ) * t)) := by
  have hsin : Real.sin t ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi ht0
      (hthalf.trans_lt (half_lt_self Real.pi_pos))).ne'
  have hfactor : 0 < chordAngleFactor a t :=
    chordAngleFactor_pos_of_pos_of_le_half ha0 ha1 ht0 hthalf
  rw [chordPhi_eq_chordAngleFactor_mul_abs hK a t ht0.le
      (hthalf.trans (half_le_self Real.pi_pos.le)) hsin,
    Real.log_mul hfactor.ne' (abs_ne_zero.mpr hphase), Real.log_abs,
    log_chordAngleFactor_eq ha0 ha1 ht0 hthalf]

theorem cos_ne_chordNodes_of_sin_size_ne_zero
    {K : ℕ} (hK : 2 ≤ K) {a t : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (ht0 : 0 < t) (hthalf : t ≤ Real.pi / 2)
    (hphase : Real.sin ((K : ℝ) * t) ≠ 0) :
    ∀ q ∈ chordNodes K, Real.cos t ≠ q := by
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht0
      (hthalf.trans_lt (half_lt_self Real.pi_pos))
  have hPhi : 0 < chordPhi K a t := by
    rw [chordPhi_eq_sine_quotient a t hK ht0.le
      (hthalf.trans (half_le_self Real.pi_pos.le)) hsin.ne']
    exact div_pos
      (mul_pos (halfTrigRadical_pos_of_parameter ha0 ha1 t)
        (abs_pos.mpr hphase)) hsin
  intro q hq heq
  have hzero := chordLobeWeight_eq_zero_of_mem_chordNodes K hK a hq
  rw [← heq, chordLobeWeight_cos] at hzero
  exact (ne_of_gt hPhi) hzero

theorem hasDerivAt_log_chordPhi
    {K : ℕ} (hK : 2 ≤ K) {a t : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hphase : Real.sin ((K : ℝ) * t) ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log (chordPhi K a x))
      (chordPhiLogSlope K a t) t := by
  have hlinear :
      HasDerivAt (fun x : ℝ => (K : ℝ) * x) (K : ℝ) t := by
    simpa only [mul_one] using (hasDerivAt_id t).const_mul (K : ℝ)
  have hlogPhase := hlinear.sin.log hphase
  have hexplicit :
      HasDerivAt
        (fun x : ℝ => chordAngleLogFactor a x +
          Real.log (Real.sin ((K : ℝ) * x)))
        (chordPhiLogSlope K a t) t := by
    unfold chordPhiLogSlope
    convert (hasDerivAt_chordAngleLogFactor ha0 ha1 ht.1 ht.2.le).add
      hlogPhase using 1
    field_simp
  have hIoo : ∀ᶠ x in nhds t, x ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    isOpen_Ioo.mem_nhds ht
  have hphaseEventually :
      ∀ᶠ x in nhds t, Real.sin ((K : ℝ) * x) ≠ 0 := by
    exact (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).continuousAt.eventually_ne hphase
  apply hexplicit.congr_of_eventuallyEq
  filter_upwards [hIoo, hphaseEventually] with x hx hxPhase
  exact (log_chordPhi_eq_logFactor_add_logSin hK ha0 ha1
    hx.1 hx.2.le hxPhase)

theorem chordPhiLogSlope_eq_coordinateSlope
    {K : ℕ} (hK : 2 ≤ K) {a t : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (ht : t ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hphase : Real.sin ((K : ℝ) * t) ≠ 0) :
    chordPhiLogSlope K a t =
      -Real.sin t * chordLogSlope K a (Real.cos t) := by
  have hnodes := cos_ne_chordNodes_of_sin_size_ne_zero hK ha0 ha1
    ht.1 ht.2.le hphase
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha0 ha1
  have hu : |Real.cos t| < Real.cosh (pathLogParameter a) :=
    (Real.abs_cos_le_one t).trans_lt (Real.one_lt_cosh.mpr hh.ne')
  have hprofile := (hasDerivAt_chordLogProfile K a (Real.cos t) hnodes hu).comp
    t (Real.hasDerivAt_cos t)
  have hcoordinate :
      HasDerivAt
        (fun x : ℝ =>
          Real.log (2 ^ (K - 1) : ℝ) + chordLogProfile K a (Real.cos x))
        (-Real.sin t * chordLogSlope K a (Real.cos t)) t := by
    convert (hasDerivAt_const t (Real.log (2 ^ (K - 1) : ℝ))).add
      hprofile using 1
    ring
  have hIoo : ∀ᶠ x in nhds t, x ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    isOpen_Ioo.mem_nhds ht
  have hphaseEventually :
      ∀ᶠ x in nhds t, Real.sin ((K : ℝ) * x) ≠ 0 := by
    exact (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).continuousAt.eventually_ne hphase
  have hcoordinatePhi :
      HasDerivAt (fun x : ℝ => Real.log (chordPhi K a x))
        (-Real.sin t * chordLogSlope K a (Real.cos t)) t := by
    apply hcoordinate.congr_of_eventuallyEq
    filter_upwards [hIoo, hphaseEventually] with x hx hxPhase
    have hxnodes := cos_ne_chordNodes_of_sin_size_ne_zero hK ha0 ha1
      hx.1 hx.2.le hxPhase
    have hxu : |Real.cos x| < Real.cosh (pathLogParameter a) :=
      (Real.abs_cos_le_one x).trans_lt (Real.one_lt_cosh.mpr hh.ne')
    symm
    calc
      Real.log (2 ^ (K - 1) : ℝ) + chordLogProfile K a (Real.cos x) =
          Real.log (chordLobeWeight K a (Real.cos x)) :=
        (log_chordLobeWeight_eq K hK a (Real.cos x) hxnodes hxu).symm
      _ = Real.log (chordPhi K a x) := by rw [chordLobeWeight_cos]
  exact (hasDerivAt_log_chordPhi hK ha0 ha1 ht hphase).unique hcoordinatePhi

theorem chordPhiLogSlope_rescale_identity
    {N : ℕ} (hN : 1 ≤ N) (a t : ℝ) :
    (noncentralScale N)⁻¹ *
        chordPhiLogSlope N a (t / noncentralScale N) =
      chordPhiLogSlope (N + 1) a t +
        (chordAngleDecay a t -
          (noncentralScale N)⁻¹ *
            chordAngleDecay a (t / noncentralScale N)) := by
  have hmultiple :
      (N : ℝ) * (t / noncentralScale N) =
        ((N + 1 : ℕ) : ℝ) * t := by
    unfold noncentralScale
    field_simp
  have hcoefficient :
      (noncentralScale N)⁻¹ * (N : ℝ) = ((N + 1 : ℕ) : ℝ) := by
    unfold noncentralScale
    field_simp
  unfold chordPhiLogSlope
  rw [hmultiple]
  calc
    (noncentralScale N)⁻¹ *
          (-chordAngleDecay a (t / noncentralScale N) +
            (N : ℝ) * Real.cos (((N + 1 : ℕ) : ℝ) * t) /
              Real.sin (((N + 1 : ℕ) : ℝ) * t)) =
        -(noncentralScale N)⁻¹ *
            chordAngleDecay a (t / noncentralScale N) +
          ((noncentralScale N)⁻¹ * (N : ℝ)) *
            Real.cos (((N + 1 : ℕ) : ℝ) * t) /
              Real.sin (((N + 1 : ℕ) : ℝ) * t) := by ring
    _ = -chordAngleDecay a t +
          ((N + 1 : ℕ) : ℝ) *
            Real.cos (((N + 1 : ℕ) : ℝ) * t) /
              Real.sin (((N + 1 : ℕ) : ℝ) * t) +
          (chordAngleDecay a t -
            (noncentralScale N)⁻¹ *
              chordAngleDecay a (t / noncentralScale N)) := by
      rw [hcoefficient]
      ring

/-- Positivity, radical-domain containment, and node exclusion on the first
outer lobe, exposed together for logarithmic-slope arguments. -/
theorem outerLobeAnalyticData
    (K : ℕ) (hK : 2 ≤ K) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    (∀ u ∈ Ioo (Real.cos (Real.pi / K))
        (Real.cosh (pathLogParameter a)), 0 < chordLobeWeight K a u) ∧
    (Ioo (Real.cos (Real.pi / K))
        (Real.cosh (pathLogParameter a)) ⊆
      Ioo (-Real.cosh (pathLogParameter a))
        (Real.cosh (pathLogParameter a))) ∧
    (∀ u ∈ Ioo (Real.cos (Real.pi / K))
        (Real.cosh (pathLogParameter a)),
      ∀ q ∈ chordNodes K, u ≠ q) := by
  let l := Real.cos (Real.pi / K)
  let c := Real.cosh (pathLogParameter a)
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha0 ha1
  have hcOne : 1 < c := by
    dsimp only [c]
    exact Real.one_lt_cosh.mpr hh.ne'
  have hlNonneg : 0 ≤ l := by
    dsimp only [l]
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · have hdiv : 0 ≤ Real.pi / (K : ℝ) := by positivity
      linarith [Real.pi_pos]
    · have hKpos : (0 : ℝ) < K := by positivity
      rw [div_le_iff₀ hKpos]
      have hKcast : (2 : ℝ) ≤ K := by exact_mod_cast hK
      nlinarith [Real.pi_pos]
  have hnodeUpper : ∀ q ∈ chordNodes K, q ≤ l := by
    intro q hq
    exact chordNode_le_first K hK hq
  have hdom : Ioo l c ⊆ Ioo (-c) c := by
    intro u hu
    have hcu : -c < u :=
      (neg_neg_of_pos (zero_lt_one.trans hcOne)).trans
        (hlNonneg.trans_lt hu.1)
    exact ⟨hcu, hu.2⟩
  have hnodes : ∀ u ∈ Ioo l c, ∀ q ∈ chordNodes K, u ≠ q := by
    intro u hu q hq huq
    subst u
    exact (not_lt_of_ge (hnodeUpper q hq)) hu.1
  have hpos : ∀ u ∈ Ioo l c, 0 < chordLobeWeight K a u := by
    intro u hu
    have hubounds : -c < u ∧ u < c := hdom hu
    have hradpos : 0 < c ^ 2 - u ^ 2 := by
      have hprod : 0 < (c - u) * (c + u) :=
        mul_pos (sub_pos.mpr hubounds.2) (by linarith)
      nlinarith
    have hnodeProd : chordNodeProduct K u ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro q hq
      exact sub_ne_zero.mpr (hnodes u hu q hq)
    rw [chordLobeWeight, chebyshevU_eq_chordNodeProduct K hK]
    exact mul_pos (Real.sqrt_pos.2 hradpos)
      (abs_pos.mpr (mul_ne_zero (by positivity) hnodeProd))
  simpa only [l, c] using ⟨hpos, hdom, hnodes⟩

theorem outerChordLogSlope_strictAntiOn
    (K : ℕ) (hK : 2 ≤ K) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    StrictAntiOn (chordLogSlope K a)
      (Ioo (Real.cos (Real.pi / K))
        (Real.cosh (pathLogParameter a))) := by
  obtain ⟨-, hdom, hnodes⟩ := outerLobeAnalyticData K hK a ha0 ha1
  exact chordLogSlope_strictAntiOn_Ioo K a
    (Real.cos (Real.pi / K)) (Real.cosh (pathLogParameter a))
    hdom hnodes

theorem outerLobeMaximizer_logSlope_eq_zero
    (d : PositiveHalfGap) :
    chordLogSlope d.K d.a (outerLobeMaximizer d) = 0 := by
  obtain ⟨hpos, hdom, hnodes⟩ :=
    outerLobeAnalyticData d.K d.hK d.a d.ha0 d.ha1
  exact chordLogSlope_eq_zero_of_isMaxOn d.K d.hK d.a
    (Real.cos (Real.pi / d.K)) (Real.cosh (pathLogParameter d.a))
    hpos hdom hnodes (outerLobeMaximizer_spec d).1
    (outerLobeMaximizer_spec d).2

theorem pi_div_size_le_half (K : ℕ) (hK : 2 ≤ K) :
    Real.pi / (K : ℝ) ≤ Real.pi / 2 := by
  have hKpos : (0 : ℝ) < K := by positivity
  rw [div_le_div_iff₀ hKpos (by norm_num : (0 : ℝ) < 2)]
  have hKcast : (2 : ℝ) ≤ K := by exact_mod_cast hK
  nlinarith [Real.pi_pos]

theorem firstOuterAngle_cos_mem
    {K : ℕ} (hK : 2 ≤ K) {a φ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hφ : φ ∈ Ioo (0 : ℝ) (Real.pi / K)) :
    Real.cos φ ∈ Ioo (Real.cos (Real.pi / K))
      (Real.cosh (pathLogParameter a)) := by
  have hanglePi : Real.pi / (K : ℝ) ≤ Real.pi :=
    (pi_div_size_le_half K hK).trans (half_le_self Real.pi_pos.le)
  have hlower : Real.cos (Real.pi / K) < Real.cos φ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hφ.1.le hanglePi hφ.2
  have hupper : Real.cos φ < Real.cosh (pathLogParameter a) :=
    (Real.cos_le_one φ).trans_lt
      (Real.one_lt_cosh.mpr (pathLogParameter_pos ha0 ha1).ne')
  exact ⟨hlower, hupper⟩

theorem chordPhiLogSlope_nonneg_of_selectedElliptic
    (d : PositiveHalfGap) (θ : d.Angle) {φ : ℝ}
    (hφ : φ ∈ Ioo (0 : ℝ) (Real.pi / d.K))
    (hselected : outerChordFamilyZ d θ = Real.cos φ) :
    0 ≤ chordPhiLogSlope d.K d.a φ := by
  have hφhalf : φ ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hφ.1, hφ.2.trans_le (pi_div_size_le_half d.K d.hK)⟩
  have hphase : Real.sin ((d.K : ℝ) * φ) ≠ 0 := by
    have hKpos : (0 : ℝ) < (d.K : ℝ) := by
      exact_mod_cast Nat.zero_lt_two.trans_le d.hK
    have hmulPos : 0 < (d.K : ℝ) * φ := mul_pos hKpos hφ.1
    have hmulPi : (d.K : ℝ) * φ < Real.pi := by
      simpa only [mul_comm] using (lt_div_iff₀ hKpos).mp hφ.2
    exact (Real.sin_pos_of_pos_of_lt_pi hmulPos hmulPi).ne'
  rw [chordPhiLogSlope_eq_coordinateSlope d.hK d.ha0 d.ha1
    hφhalf hphase]
  have hpLe : outerLobeMaximizer d ≤ Real.cos φ := by
    rw [← hselected]
    exact (outerChordFamilyZ_mem d θ).1
  have hu := firstOuterAngle_cos_mem d.hK d.ha0 d.ha1 hφ
  have hp := (outerLobeMaximizer_spec d).1
  have hslopeLe : chordLogSlope d.K d.a (Real.cos φ) ≤ 0 := by
    rcases hpLe.eq_or_lt with heq | hlt
    · rw [← heq, outerLobeMaximizer_logSlope_eq_zero]
    · have hanti := outerChordLogSlope_strictAntiOn
        d.K d.hK d.a d.ha0 d.ha1 hp hu hlt
      rw [outerLobeMaximizer_logSlope_eq_zero] at hanti
      exact hanti.le
  have hsin : 0 < Real.sin φ :=
    Real.sin_pos_of_pos_of_lt_pi hφ.1
      (hφhalf.2.trans (half_lt_self Real.pi_pos))
  exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hsin.le) hslopeLe

theorem outerLobeMaximizer_lt_cos_of_chordPhiLogSlope_pos
    (d : PositiveHalfGap) {φ : ℝ}
    (hφ : φ ∈ Ioo (0 : ℝ) (Real.pi / d.K))
    (hpositive : 0 < chordPhiLogSlope d.K d.a φ) :
    outerLobeMaximizer d < Real.cos φ := by
  have hφhalf : φ ∈ Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨hφ.1, hφ.2.trans_le (pi_div_size_le_half d.K d.hK)⟩
  have hphase : Real.sin ((d.K : ℝ) * φ) ≠ 0 := by
    have hKpos : (0 : ℝ) < (d.K : ℝ) := by
      exact_mod_cast Nat.zero_lt_two.trans_le d.hK
    have hmulPos : 0 < (d.K : ℝ) * φ := mul_pos hKpos hφ.1
    have hmulPi : (d.K : ℝ) * φ < Real.pi := by
      simpa only [mul_comm] using (lt_div_iff₀ hKpos).mp hφ.2
    exact (Real.sin_pos_of_pos_of_lt_pi hmulPos hmulPi).ne'
  rw [chordPhiLogSlope_eq_coordinateSlope d.hK d.ha0 d.ha1
    hφhalf hphase] at hpositive
  have hu := firstOuterAngle_cos_mem d.hK d.ha0 d.ha1 hφ
  have hp := (outerLobeMaximizer_spec d).1
  by_contra hnot
  have huLe : Real.cos φ ≤ outerLobeMaximizer d := le_of_not_gt hnot
  have hslopeNonneg : 0 ≤ chordLogSlope d.K d.a (Real.cos φ) := by
    rcases huLe.eq_or_lt with heq | hlt
    · rw [heq, outerLobeMaximizer_logSlope_eq_zero]
    · have hanti := outerChordLogSlope_strictAntiOn
        d.K d.hK d.a d.ha0 d.ha1 hu hp hlt
      rw [outerLobeMaximizer_logSlope_eq_zero] at hanti
      exact hanti.le
  have hsin : 0 < Real.sin φ :=
    Real.sin_pos_of_pos_of_lt_pi hφ.1
      (hφhalf.2.trans (half_lt_self Real.pi_pos))
  have : -Real.sin φ * chordLogSlope d.K d.a (Real.cos φ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsin.le) hslopeNonneg
  exact (not_lt_of_ge this) hpositive

/-- The source's predecessor elliptic angle `phi₀=phi/kappa`. -/
def ellipticRescaledAngle (N : ℕ) (φ : ℝ) : ℝ :=
  φ / noncentralScale N

theorem ellipticRescaledAngle_bounds
    {N : ℕ} (hN : 2 ≤ N) {φ : ℝ}
    (hφ : φ ∈ Ioo (0 : ℝ) (Real.pi / (N + 1 : ℕ))) :
    ellipticRescaledAngle N φ ∈
      Ioo (0 : ℝ) (Real.pi / N) := by
  have hN1 : 1 ≤ N := (by norm_num : 1 ≤ 2).trans hN
  have hκ0 : 0 < noncentralScale N := noncentralScale_pos hN1
  have hupperIdentity :
      noncentralScale N * (Real.pi / (N : ℝ)) =
        Real.pi / ((N + 1 : ℕ) : ℝ) := by
    unfold noncentralScale
    field_simp
  constructor
  · exact div_pos hφ.1 hκ0
  · apply (div_lt_iff₀ hκ0).2
    calc
      φ < Real.pi / ((N + 1 : ℕ) : ℝ) := hφ.2
      _ = Real.pi / (N : ℝ) * noncentralScale N := by
        simpa only [mul_comm] using hupperIdentity.symm

theorem ellipticRescaledAngle_gt
    {N : ℕ} (hN : 1 ≤ N) {φ : ℝ} (hφ : 0 < φ) :
    φ < ellipticRescaledAngle N φ := by
  have hκ0 : 0 < noncentralScale N := noncentralScale_pos hN
  unfold ellipticRescaledAngle
  apply (lt_div_iff₀ hκ0).2
  nlinarith [noncentralScale_lt_one N]

theorem ellipticOuterCoordinate_preserved
    (d : PositiveHalfGap)
    (θM : d.successor.Angle) (θN : d.Angle) {φ : ℝ}
    (hφ : φ ∈ Ioo (0 : ℝ) (Real.pi / d.successor.K))
    (hM : outerChordFamilyZ d.successor θM = Real.cos φ)
    (hNlevel : chordPhi d.K d.a θN =
      chordPhi d.K d.a (ellipticRescaledAngle d.K φ)) :
    outerChordFamilyZ d θN =
      Real.cos (ellipticRescaledAngle d.K φ) := by
  have hK2 : 2 ≤ d.K := d.hK
  have hK1 : 1 ≤ d.K := (by norm_num : 1 ≤ 2).trans hK2
  have hκ0 : 0 < noncentralScale d.K := noncentralScale_pos hK1
  have hκ1 : noncentralScale d.K < 1 := noncentralScale_lt_one d.K
  have hφBase : φ ∈ Ioo (0 : ℝ) (Real.pi / (d.K + 1 : ℕ)) := by
    simpa only [PositiveHalfGap.successor_K] using hφ
  have hφ0 := ellipticRescaledAngle_bounds hK2 hφBase
  have hφ0Half : ellipticRescaledAngle d.K φ < Real.pi / 2 :=
    hφ0.2.trans_le (pi_div_size_le_half d.K d.hK)
  have hLambdaM : 0 ≤ chordPhiLogSlope (d.K + 1) d.a φ := by
    simpa only [PositiveHalfGap.successor_K, PositiveHalfGap.successor_a] using
      chordPhiLogSlope_nonneg_of_selectedElliptic d.successor θM hφ hM
  have hdelta :
      0 < chordAngleDecay d.a φ -
        (noncentralScale d.K)⁻¹ *
          chordAngleDecay d.a (ellipticRescaledAngle d.K φ) := by
    exact chordAngleRescaledLogRatio_deriv_pos hκ0 hκ1 d.ha0 d.ha1
      hφ.1 hφ0Half
  have hidentity := chordPhiLogSlope_rescale_identity hK1 d.a φ
  have hscaledPositive :
      0 < (noncentralScale d.K)⁻¹ *
        chordPhiLogSlope d.K d.a (ellipticRescaledAngle d.K φ) := by
    unfold ellipticRescaledAngle
    rw [hidentity]
    exact add_pos_of_nonneg_of_pos hLambdaM hdelta
  have hLambdaN :
      0 < chordPhiLogSlope d.K d.a (ellipticRescaledAngle d.K φ) := by
    exact pos_of_mul_pos_right hscaledPositive (inv_nonneg.mpr hκ0.le)
  have hpNlt : outerLobeMaximizer d <
      Real.cos (ellipticRescaledAngle d.K φ) :=
    outerLobeMaximizer_lt_cos_of_chordPhiLogSlope_pos d hφ0 hLambdaN
  have hcosUpper :
      Real.cos (ellipticRescaledAngle d.K φ) <
        Real.cosh (pathLogParameter d.a) :=
    (Real.cos_le_one _).trans_lt
      (Real.one_lt_cosh.mpr (pathLogParameter_pos d.ha0 d.ha1).ne')
  have hanti := outerChordLobeWeight_strictAntiOn_closedEndpointSide
    d.K d.hK d.a d.ha0 d.ha1
    (outerLobeMaximizer_spec d).1 (outerLobeMaximizer_spec d).2
  apply hanti.injOn (outerChordFamilyZ_mem d θN)
    ⟨hpNlt.le, hcosUpper.le⟩
  rw [chordLobeWeight_outerChordFamilyZ d θN, hNlevel,
    chordLobeWeight_cos]

theorem predecessorEllipticLevel_strict
    (d : PositiveHalfGap) (θ0 : d.Angle)
    (hleft : d.angleLower < θ0) (hright : θ0 < d.angleUpper)
    {φ : ℝ}
    (hφ : φ ∈ Ioo (0 : ℝ) (Real.pi / d.successor.K))
    (hM : outerChordFamilyZ d.successor (d.scaleToSuccessor θ0) =
      Real.cos φ) :
    chordPhi d.K d.a (ellipticRescaledAngle d.K φ) <
      chordPhi d.K d.a θ0 := by
  have hK1 : 1 ≤ d.K := (by norm_num : 1 ≤ 2).trans d.hK
  have hκ0 : 0 < noncentralScale d.K := noncentralScale_pos hK1
  have hκ1 : noncentralScale d.K < 1 := noncentralScale_lt_one d.K
  have hφBase : φ ∈ Ioo (0 : ℝ) (Real.pi / (d.K + 1 : ℕ)) := by
    simpa only [PositiveHalfGap.successor_K] using hφ
  have hφ0 := ellipticRescaledAngle_bounds d.hK hφBase
  have hφHalf : φ ≤ Real.pi / 2 :=
    hφBase.2.le.trans
      (pi_div_size_le_half (d.K + 1) (d.hK.trans (Nat.le_succ d.K)))
  have hθMInterior := d.scaleToSuccessor_interior hleft hright
  have hθMPos : 0 < (d.scaleToSuccessor θ0 : ℝ) :=
    d.successor.angleLower_pos.trans hθMInterior.1
  have hθMUpper :
      (d.scaleToSuccessor θ0 : ℝ) /
          noncentralScale d.K ≤ Real.pi / 2 := by
    rw [PositiveHalfGap.coe_scaleToSuccessor]
    field_simp [hκ0.ne']
    nlinarith [θ0.2.2.trans d.angleUpper_le_half]
  have hφUpper : φ / noncentralScale d.K ≤ Real.pi / 2 :=
    hφ0.2.le.trans (pi_div_size_le_half d.K d.hK)
  have hφltθM : φ < (d.scaleToSuccessor θ0 : ℝ) := by
    have hfirst : Real.pi / ((d.K + 1 : ℕ) : ℝ) ≤
        d.successor.angleLower := by
      simp only [PositiveHalfGap.angleLower, PositiveHalfGap.successor_K,
        PositiveHalfGap.successor_j]
      have hjOne : (1 : ℝ) ≤ d.j := by exact_mod_cast d.hj
      have hden : (0 : ℝ) ≤ ((d.K + 1 : ℕ) : ℝ) := by positivity
      exact div_le_div_of_nonneg_right
        (by
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hjOne Real.pi_pos.le)) hden
    exact hφBase.2.trans (hfirst.trans_lt hθMInterior.1)
  have hratio := chordAngleRescaledRatio_strictMonoOn
    hκ0 hκ1 d.ha0 d.ha1
    ⟨hφ.1, (by
      have hmul := (div_le_iff₀ hκ0).mp hφUpper
      simpa only [mul_comm] using hmul)⟩
    ⟨hθMPos, (by
      have hmul := (div_le_iff₀ hκ0).mp hθMUpper
      simpa only [mul_comm] using hmul)⟩ hφltθM
  have hphaseφ :
      Real.sin (((d.K + 1 : ℕ) : ℝ) * φ) ≠ 0 := by
    have hden : (0 : ℝ) < ((d.K + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_pos d.K
    have hpos : 0 < ((d.K + 1 : ℕ) : ℝ) * φ := mul_pos hden hφ.1
    have hlt : ((d.K + 1 : ℕ) : ℝ) * φ < Real.pi := by
      simpa only [mul_comm] using (lt_div_iff₀ hden).mp hφBase.2
    exact (Real.sin_pos_of_pos_of_lt_pi hpos hlt).ne'
  have hphaseθ :
      Real.sin (((d.K + 1 : ℕ) : ℝ) *
        (d.scaleToSuccessor θ0 : ℝ)) ≠ 0 := by
    have hmultiple :
        ((d.K + 1 : ℕ) : ℝ) * (d.scaleToSuccessor θ0 : ℝ) =
          (d.K : ℝ) * (θ0 : ℝ) := by
      rw [PositiveHalfGap.coe_scaleToSuccessor]
      unfold noncentralScale
      field_simp
    rw [hmultiple]
    exact sin_size_mul_ne_zero_of_gapInterior d hleft hright
  have hratioφ := chordPhi_rescaled_successor_ratio_eq
    (a := d.a) (t := φ) d.hK hφ.1 hφUpper hphaseφ
  have hratioθ := chordPhi_rescaled_successor_ratio_eq
    (a := d.a) (t := (d.scaleToSuccessor θ0 : ℝ)) d.hK hθMPos
      hθMUpper hphaseθ
  have hchannel :
      chordPhi (d.K + 1) d.a (d.scaleToSuccessor θ0) =
        chordPhi (d.K + 1) d.a φ := by
    calc
      chordPhi (d.K + 1) d.a (d.scaleToSuccessor θ0) =
          chordLobeWeight d.successor.K d.a
            (outerChordFamilyZ d.successor (d.scaleToSuccessor θ0)) := by
        simpa only [PositiveHalfGap.successor_K,
          PositiveHalfGap.successor_a] using
          (chordLobeWeight_outerChordFamilyZ d.successor
            (d.scaleToSuccessor θ0)).symm
      _ = chordLobeWeight d.successor.K d.a (Real.cos φ) := by rw [hM]
      _ = chordPhi (d.K + 1) d.a φ := by
        rw [chordLobeWeight_cos]
        rfl
  have hMpos : 0 < chordPhi (d.K + 1) d.a φ := by
    rw [chordPhi_eq_sine_quotient d.a φ (d.hK.trans (Nat.le_succ d.K))
      hφ.1.le (hφHalf.trans (half_le_self Real.pi_pos.le))
      (Real.sin_pos_of_pos_of_lt_pi hφ.1
        (hφHalf.trans_lt (half_lt_self Real.pi_pos))).ne']
    exact div_pos
      (mul_pos (halfTrigRadical_pos_of_parameter d.ha0 d.ha1 φ)
        (abs_pos.mpr hphaseφ))
      (Real.sin_pos_of_pos_of_lt_pi hφ.1
        (hφHalf.trans_lt (half_lt_self Real.pi_pos)))
  have hEqφ :
      chordPhi d.K d.a (ellipticRescaledAngle d.K φ) =
        chordAngleRescaledRatio (noncentralScale d.K) d.a φ *
          chordPhi (d.K + 1) d.a φ := by
    exact (div_eq_iff (ne_of_gt hMpos)).mp hratioφ
  have hMθpos : 0 < chordPhi (d.K + 1) d.a (d.scaleToSuccessor θ0) := by
    rw [hchannel]
    exact hMpos
  have hEqθ :
      chordPhi d.K d.a θ0 =
        chordAngleRescaledRatio (noncentralScale d.K) d.a
            (d.scaleToSuccessor θ0) *
          chordPhi (d.K + 1) d.a (d.scaleToSuccessor θ0) := by
    have := (div_eq_iff (ne_of_gt hMθpos)).mp hratioθ
    have hrescale :
        (d.scaleToSuccessor θ0 : ℝ) / noncentralScale d.K = (θ0 : ℝ) := by
      rw [PositiveHalfGap.coe_scaleToSuccessor]
      field_simp [hκ0.ne']
    simpa only [hrescale] using this
  calc
    chordPhi d.K d.a (ellipticRescaledAngle d.K φ) =
        chordAngleRescaledRatio (noncentralScale d.K) d.a φ *
          chordPhi (d.K + 1) d.a φ := hEqφ
    _ < chordAngleRescaledRatio (noncentralScale d.K) d.a
          (d.scaleToSuccessor θ0) * chordPhi (d.K + 1) d.a φ :=
      mul_lt_mul_of_pos_right hratio hMpos
    _ = chordPhi d.K d.a θ0 := by rw [← hchannel, ← hEqθ]

theorem ellipticChordS_eq_factorized (a θ φ : ℝ) :
    ellipticChordS a θ φ =
      halfChordScale a * halfTrigRadical a θ * halfTrigRadical a φ := by
  rw [← outerChordS_cos]
  unfold outerChordS halfTrigRadical
  rw [Real.sqrt_mul' _ (halfTrigRadicand_nonneg a φ)]
  ring

theorem ellipticChordS_strictMono_bothAngles
    {a θ₁ θ₂ φ₁ φ₂ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hθ₁0 : 0 ≤ θ₁) (hθ₂half : θ₂ ≤ Real.pi / 2)
    (hθ : θ₁ < θ₂)
    (hφ₁0 : 0 ≤ φ₁) (hφ₂half : φ₂ ≤ Real.pi / 2)
    (hφ : φ₁ < φ₂) :
    ellipticChordS a θ₁ φ₁ < ellipticChordS a θ₂ φ₂ := by
  rw [ellipticChordS_eq_factorized, ellipticChordS_eq_factorized]
  have htrigθ := halfTrigRadical_strictMonoOn_positiveHalf ha0 ha1
    hθ₁0 hθ₂half hθ
  have htrigφ := halfTrigRadical_strictMonoOn_positiveHalf ha0 ha1
    hφ₁0 hφ₂half hφ
  have hfirst := mul_lt_mul_of_pos_left htrigθ (halfChordScale_pos ha0)
  exact (mul_lt_mul_of_pos_right hfirst
      (halfTrigRadical_pos_of_parameter ha0 ha1 φ₁)).trans
    (mul_lt_mul_of_pos_left htrigφ
      (mul_pos (halfChordScale_pos ha0)
        (halfTrigRadical_pos_of_parameter ha0 ha1 θ₂)))

/-- Full elliptic counterpart of `eq:hyper-height-increase`, stated for the
actual endpoint-side continuous chord families. -/
theorem existsUnique_noncentralEllipticComparison
    (d : PositiveHalfGap) (θ0 : d.Angle)
    (hleft : d.angleLower < θ0) (hright : θ0 < d.angleUpper)
    {φ : ℝ} (hφ : φ ∈ Ioo (0 : ℝ) (Real.pi / d.successor.K))
    (hM : outerChordFamilyZ d.successor (d.scaleToSuccessor θ0) =
      Real.cos φ) :
    ∃! θhat : d.Angle,
      IsRightmostInnerSolution d θ0
          (chordPhi d.K d.a (ellipticRescaledAngle d.K φ)) θhat ∧
      outerChordFamilyZ d θhat =
        Real.cos (ellipticRescaledAngle d.K φ) ∧
      outerChordFamilyS d.successor (d.scaleToSuccessor θ0) <
        outerChordFamilyS d θhat := by
  have hφBase : φ ∈ Ioo (0 : ℝ) (Real.pi / (d.K + 1 : ℕ)) := by
    simpa only [PositiveHalfGap.successor_K] using hφ
  have hφ0 := ellipticRescaledAngle_bounds d.hK hφBase
  have hlevelPos :
      0 < chordPhi d.K d.a (ellipticRescaledAngle d.K φ) :=
    chordPhi_pos_on_nodalInterval d.K 0 d.hK
      (Nat.zero_lt_two.trans_le d.hK) d.a
      (by simpa using hφ0)
      (halfTrigRadical_pos_of_parameter d.ha0 d.ha1 _)
  have hlevel := predecessorEllipticLevel_strict d θ0 hleft hright hφ hM
  obtain ⟨θhat, hθhat, hunique⟩ :=
    existsUnique_rightmostInnerSolutionAtLevel d θ0 _ hlevelPos hlevel
  have hN : outerChordFamilyZ d θhat =
      Real.cos (ellipticRescaledAngle d.K φ) :=
    ellipticOuterCoordinate_preserved d
      (d.scaleToSuccessor θ0) θhat hφ hM hθhat.2.2.1
  have hθMlt : (d.scaleToSuccessor θ0 : ℝ) < (θhat : ℝ) :=
    (d.scaleToSuccessor_lt hleft).trans hθhat.1
  have hφlt : φ < ellipticRescaledAngle d.K φ :=
    ellipticRescaledAngle_gt ((by norm_num : 1 ≤ 2).trans d.hK) hφ.1
  have hheight :
      outerChordFamilyS d.successor (d.scaleToSuccessor θ0) <
        outerChordFamilyS d θhat := by
    unfold outerChordFamilyS
    rw [hM, hN, outerChordS_cos, outerChordS_cos]
    exact ellipticChordS_strictMono_bothAngles d.ha0 d.ha1
      ((d.successor.angleLower_pos).le.trans
        (d.scaleToSuccessor θ0).2.1)
      (θhat.2.2.trans d.angleUpper_le_half) hθMlt
      hφ.1.le (hφ0.2.le.trans (pi_div_size_le_half d.K d.hK)) hφlt
  refine ⟨θhat, ⟨hθhat, hN, hheight⟩, ?_⟩
  intro ψ hψ
  exact hunique ψ hψ.1

end

end ConnectedPseudospectrum
