import ConnectedPseudospectrum.ChordLobes
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# Hyperbolic-channel half of the noncentral comparison

For `M=N+1`, this module formalizes `eq:Phi-scale` and `eq:Psi-scale`,
including the continuous hyperbolic value at `eta=0`, and combines them at
a common `M`-channel value.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- The source's scale `kappa=N/(N+1)`. -/
def noncentralScale (N : ℕ) : ℝ :=
  (N : ℝ) / (N + 1 : ℕ)

theorem noncentralScale_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < noncentralScale N := by
  unfold noncentralScale
  positivity

theorem noncentralScale_lt_one (N : ℕ) :
    noncentralScale N < 1 := by
  unfold noncentralScale
  rw [div_lt_one (by positivity : (0 : ℝ) < (N + 1 : ℕ))]
  norm_num

/-- Strict sine concavity in exactly the scaled form used by
`eq:Phi-scale`. -/
theorem noncentralScale_mul_sin_lt_sin
    {N : ℕ} (hN : 1 ≤ N) {θ0 : ℝ}
    (hθ0 : θ0 ∈ Ioc (0 : ℝ) (Real.pi / 2)) :
    noncentralScale N * Real.sin θ0 <
      Real.sin (noncentralScale N * θ0) := by
  have hκ0 := noncentralScale_pos hN
  have hκ1 := noncentralScale_lt_one N
  have hθ0Pi : θ0 ∈ Icc (0 : ℝ) Real.pi :=
    ⟨hθ0.1.le, hθ0.2.trans (half_le_self Real.pi_pos.le)⟩
  have hstrict := strictConcaveOn_sin_Icc.2
    ⟨le_rfl, Real.pi_pos.le⟩ hθ0Pi (ne_of_lt hθ0.1)
      (sub_pos.mpr hκ1) hκ0 (by ring)
  simpa only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add,
    sub_mul, one_mul] using hstrict

/-- `sinh` is strictly convex on the nonnegative half-axis. -/
theorem strictConvexOn_sinh_Ici :
    StrictConvexOn ℝ (Ici (0 : ℝ)) Real.sinh := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0)
    Real.continuous_sinh.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  simp only [Nat.iterate, Real.deriv_sinh, Real.deriv_cosh]
  exact Real.sinh_pos_iff.mpr hx

/-- Strict convexity gives the raw hyperbolic scaling inequality for
positive `eta`. -/
theorem sinh_ratio_lt_noncentralScale
    {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η) :
    Real.sinh (N * η) / Real.sinh ((N + 1 : ℕ) * η) <
      noncentralScale N := by
  have hκ0 := noncentralScale_pos hN
  have hκ1 := noncentralScale_lt_one N
  have hMη : 0 < ((N + 1 : ℕ) : ℝ) * η := by positivity
  have hsinhStrict
      (x : ℝ) (hx : x ∈ Ici (0 : ℝ))
      (y : ℝ) (hy : y ∈ Ici (0 : ℝ)) (hxy : x ≠ y)
      (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β = 1) :
      Real.sinh (α • x + β • y) <
        α • Real.sinh x + β • Real.sinh y := by
    exact strictConvexOn_sinh_Ici.2 hx hy hxy hα hβ hαβ
  have hstrict := hsinhStrict
    (0 : ℝ) (le_refl (0 : ℝ))
    (((N + 1 : ℕ) : ℝ) * η) hMη.le
    (ne_of_lt hMη) (1 - noncentralScale N) (noncentralScale N)
    (sub_pos.mpr hκ1) hκ0 (by ring)
  have hargument :
      noncentralScale N * (((N + 1 : ℕ) : ℝ) * η) = (N : ℝ) * η := by
    unfold noncentralScale
    field_simp
  have hsinhScaled :
      Real.sinh ((N : ℝ) * η) <
        noncentralScale N * Real.sinh (((N + 1 : ℕ) : ℝ) * η) := by
    simpa only [smul_eq_mul, Real.sinh_zero, mul_zero, zero_add,
      sub_mul, one_mul, hargument] using hstrict
  apply (div_lt_iff₀ (Real.sinh_pos_iff.mpr hMη)).2
  exact hsinhScaled

/-- For a fixed admissible hopping parameter, the trigonometric half-chord
radical is everywhere strictly positive. -/
theorem halfTrigRadical_pos_of_parameter
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    0 < halfTrigRadical a t := by
  rw [halfTrigRadical, Real.sqrt_pos]
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha0 ha1
  nlinarith [Real.cosh_sq_sub_sinh_sq (pathLogParameter a),
    Real.sin_sq_add_cos_sq t,
    sq_pos_of_pos (Real.sinh_pos_iff.mpr hh)]

/-- Before the terminal hyperbolic point, the hyperbolic half-chord radical
is strictly positive. -/
theorem halfHypRadical_pos_of_lt_pathLogParameter
    {a η : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hη0 : 0 ≤ η) (hηh : η < pathLogParameter a) :
    0 < halfHypRadical a η := by
  rw [halfHypRadical, Real.sqrt_pos]
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha0 ha1
  have hcosh : Real.cosh η < Real.cosh (pathLogParameter a) :=
    Real.cosh_strictMonoOn hη0 hh.le hηh
  nlinarith [Real.cosh_pos η, Real.cosh_pos (pathLogParameter a)]

/-- The source's auxiliary function
`F_h(t)=sqrt(sinh(h)^2+sin(t)^2)/sin(t)`, expressed with the chord radical. -/
def noncentralTrigProfile (a t : ℝ) : ℝ :=
  halfTrigRadical a t / Real.sin t

/-- The strict profile scaling behind `eq:Phi-scale`:
`F_h(theta₀)/F_h(kappa theta₀)>kappa`. -/
theorem noncentralTrigProfile_ratio_gt_scale
    {N : ℕ} (hN : 1 ≤ N) {a θ0 : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hθ0 : θ0 ∈ Ioc (0 : ℝ) (Real.pi / 2)) :
    noncentralScale N <
      noncentralTrigProfile a θ0 /
        noncentralTrigProfile a (noncentralScale N * θ0) := by
  have hκ0 : 0 < noncentralScale N := noncentralScale_pos hN
  have hκ1 : noncentralScale N < 1 := noncentralScale_lt_one N
  have hθ0pi : θ0 < Real.pi := by
    nlinarith [hθ0.2, Real.pi_pos]
  have hsin0 : 0 < Real.sin θ0 :=
    Real.sin_pos_of_pos_of_lt_pi hθ0.1 hθ0pi
  have hθpos : 0 < noncentralScale N * θ0 := mul_pos hκ0 hθ0.1
  have hθle : noncentralScale N * θ0 ≤ Real.pi / 2 :=
    (mul_le_of_le_one_left hθ0.1.le hκ1.le).trans hθ0.2
  have hθpi : noncentralScale N * θ0 < Real.pi := by
    nlinarith [hθle, Real.pi_pos]
  have hsin : 0 < Real.sin (noncentralScale N * θ0) :=
    Real.sin_pos_of_pos_of_lt_pi hθpos hθpi
  have hsine :
      noncentralScale N * Real.sin θ0 <
        Real.sin (noncentralScale N * θ0) :=
    noncentralScale_mul_sin_lt_sin hN hθ0
  have hsqSine :
      (noncentralScale N * Real.sin θ0) ^ 2 <
        Real.sin (noncentralScale N * θ0) ^ 2 :=
    (sq_lt_sq₀ (mul_nonneg hκ0.le hsin0.le) hsin.le).2 hsine
  have hκSq : noncentralScale N ^ 2 < 1 := by
    nlinarith [sq_nonneg (noncentralScale N - 1)]
  have hradical0 :
      halfTrigRadical a θ0 ^ 2 =
        Real.sinh (pathLogParameter a) ^ 2 + Real.sin θ0 ^ 2 := by
    rw [halfTrigRadical_sq]
    nlinarith [Real.cosh_sq_sub_sinh_sq (pathLogParameter a),
      Real.sin_sq_add_cos_sq θ0]
  have hradical :
      halfTrigRadical a (noncentralScale N * θ0) ^ 2 =
        Real.sinh (pathLogParameter a) ^ 2 +
          Real.sin (noncentralScale N * θ0) ^ 2 := by
    rw [halfTrigRadical_sq]
    nlinarith [Real.cosh_sq_sub_sinh_sq (pathLogParameter a),
      Real.sin_sq_add_cos_sq (noncentralScale N * θ0)]
  have hfirst :
      0 ≤ Real.sinh (pathLogParameter a) ^ 2 *
        (Real.sin (noncentralScale N * θ0) ^ 2 -
          noncentralScale N ^ 2 * Real.sin θ0 ^ 2) := by
    apply mul_nonneg (sq_nonneg _)
    nlinarith [hsqSine]
  have hsecond :
      0 < (1 - noncentralScale N ^ 2) *
        (Real.sin θ0 ^ 2 *
          Real.sin (noncentralScale N * θ0) ^ 2) := by
    exact mul_pos (sub_pos.mpr hκSq)
      (mul_pos (sq_pos_of_pos hsin0) (sq_pos_of_pos hsin))
  have hpositive :
      0 < Real.sinh (pathLogParameter a) ^ 2 *
          (Real.sin (noncentralScale N * θ0) ^ 2 -
            noncentralScale N ^ 2 * Real.sin θ0 ^ 2) +
        (1 - noncentralScale N ^ 2) *
          (Real.sin θ0 ^ 2 *
            Real.sin (noncentralScale N * θ0) ^ 2) :=
    add_pos_of_nonneg_of_pos hfirst hsecond
  have hcrossSq :
      (noncentralScale N * halfTrigRadical a
          (noncentralScale N * θ0) * Real.sin θ0) ^ 2 <
        (halfTrigRadical a θ0 *
          Real.sin (noncentralScale N * θ0)) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, hradical, hradical0]
    nlinarith [hpositive]
  have hcross :
      noncentralScale N * halfTrigRadical a
          (noncentralScale N * θ0) * Real.sin θ0 <
        halfTrigRadical a θ0 *
          Real.sin (noncentralScale N * θ0) := by
    apply (sq_lt_sq₀ ?_ ?_).1 hcrossSq
    · exact (mul_pos
        (mul_pos hκ0 (halfTrigRadical_pos_of_parameter ha0 ha1 _)) hsin0).le
    · exact (mul_pos (halfTrigRadical_pos_of_parameter ha0 ha1 _) hsin).le
  have hprofile :
      noncentralScale N *
          noncentralTrigProfile a (noncentralScale N * θ0) <
        noncentralTrigProfile a θ0 := by
    unfold noncentralTrigProfile
    calc
      noncentralScale N *
          (halfTrigRadical a (noncentralScale N * θ0) /
            Real.sin (noncentralScale N * θ0)) =
          (noncentralScale N *
            halfTrigRadical a (noncentralScale N * θ0)) /
              Real.sin (noncentralScale N * θ0) := by ring
      _ < halfTrigRadical a θ0 / Real.sin θ0 :=
        (div_lt_div_iff₀ hsin hsin0).2 hcross
  apply (lt_div_iff₀ ?_).2 hprofile
  exact div_pos (halfTrigRadical_pos_of_parameter ha0 ha1 _) hsin

/-- Exact `eq:Phi-scale`.  The nonzero hypothesis is the source's interior
of a trigonometric lobe: after the rescaling, the two Chebyshev sine factors
are literally the same nonzero factor. -/
theorem chordPhi_ratio_gt_noncentralScale
    {N : ℕ} (hN : 3 ≤ N) {a θ0 : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hθ0 : θ0 ∈ Ioc (0 : ℝ) (Real.pi / 2))
    (hnodal : Real.sin ((N : ℝ) * θ0) ≠ 0) :
    noncentralScale N <
      chordPhi N a θ0 /
        chordPhi (N + 1) a (noncentralScale N * θ0) := by
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hM2 : 2 ≤ N + 1 := by omega
  have hκ0 : 0 < noncentralScale N := noncentralScale_pos hN1
  have hκ1 : noncentralScale N < 1 := noncentralScale_lt_one N
  have hθ0ltpi : θ0 < Real.pi := by
    nlinarith [hθ0.2, Real.pi_pos]
  have hθ0pi : θ0 ≤ Real.pi := hθ0ltpi.le
  have hθpos : 0 < noncentralScale N * θ0 := mul_pos hκ0 hθ0.1
  have hθle : noncentralScale N * θ0 ≤ Real.pi / 2 :=
    (mul_le_of_le_one_left hθ0.1.le hκ1.le).trans hθ0.2
  have hθltpi : noncentralScale N * θ0 < Real.pi := by
    nlinarith [hθle, Real.pi_pos]
  have hθpi : noncentralScale N * θ0 ≤ Real.pi := hθltpi.le
  have hsin0 : Real.sin θ0 ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ0.1 hθ0ltpi)
  have hsin : Real.sin (noncentralScale N * θ0) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθpos hθltpi)
  have hmultiple :
      (((N + 1 : ℕ) : ℝ) * (noncentralScale N * θ0)) =
        (N : ℝ) * θ0 := by
    unfold noncentralScale
    field_simp
  rw [chordPhi_eq_sine_quotient a θ0 hN2 hθ0.1.le hθ0pi hsin0,
    chordPhi_eq_sine_quotient a (noncentralScale N * θ0) hM2
      hθpos.le hθpi hsin,
    hmultiple]
  have hratio :
      (halfTrigRadical a θ0 * |Real.sin ((N : ℝ) * θ0)| /
          Real.sin θ0) /
          (halfTrigRadical a (noncentralScale N * θ0) *
            |Real.sin ((N : ℝ) * θ0)| /
              Real.sin (noncentralScale N * θ0)) =
        noncentralTrigProfile a θ0 /
          noncentralTrigProfile a (noncentralScale N * θ0) := by
    unfold noncentralTrigProfile
    field_simp [hsin0, hsin, abs_ne_zero.mpr hnodal]
  rw [hratio]
  exact noncentralTrigProfile_ratio_gt_scale hN1 ha0 ha1 hθ0

/-- The continuous value of the hyperbolic channel at `eta=0`. -/
theorem chordPsi_zero (K : ℕ) (hK : 2 ≤ K) (a : ℝ) :
    chordPsi K a 0 = halfHypRadical a 0 * K := by
  have hcast : ((K - 1 : ℕ) : ℝ) + 1 = K := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ K)
  unfold chordPsi
  simp [chebyshevU, hcast]

/-- The continuous `eta=0` case of `eq:Psi-scale`; here equality holds. -/
theorem chordPsi_ratio_zero_eq_noncentralScale
    {N : ℕ} (hN : 3 ≤ N) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    chordPsi N a 0 / chordPsi (N + 1) a 0 =
      noncentralScale N := by
  have hN2 : 2 ≤ N := by omega
  have hM2 : 2 ≤ N + 1 := by omega
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha0 ha1
  have hradical : 0 < halfHypRadical a 0 :=
    halfHypRadical_pos_of_lt_pathLogParameter ha0 ha1 le_rfl hh
  rw [chordPsi_zero N hN2 a, chordPsi_zero (N + 1) hM2 a]
  unfold noncentralScale
  field_simp [ne_of_gt hradical]

/-- Strict positive-coordinate form of `eq:Psi-scale`. -/
theorem chordPsi_ratio_lt_noncentralScale
    {N : ℕ} (hN : 3 ≤ N) {a η : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hη0 : 0 < η) (hηh : η < pathLogParameter a) :
    chordPsi N a η / chordPsi (N + 1) a η <
      noncentralScale N := by
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hM2 : 2 ≤ N + 1 := by omega
  have hradical : 0 < halfHypRadical a η :=
    halfHypRadical_pos_of_lt_pathLogParameter ha0 ha1 hη0.le hηh
  have hsinh : Real.sinh η ≠ 0 := Real.sinh_ne_zero.mpr (ne_of_gt hη0)
  rw [chordPsi_eq_sinh_quotient a η hN2 (ne_of_gt hη0),
    chordPsi_eq_sinh_quotient a η hM2 (ne_of_gt hη0)]
  have hratio :
      (halfHypRadical a η * Real.sinh ((N : ℝ) * η) /
          Real.sinh η) /
          (halfHypRadical a η * Real.sinh (((N + 1 : ℕ) : ℝ) * η) /
            Real.sinh η) =
        Real.sinh ((N : ℝ) * η) /
          Real.sinh (((N + 1 : ℕ) : ℝ) * η) := by
    field_simp [ne_of_gt hradical, hsinh]
  rw [hratio]
  exact sinh_ratio_lt_noncentralScale hN1 hη0

/-- Full continuous `eq:Psi-scale`: equality at `eta=0`, strict inequality
at every positive coordinate before the terminal half-chord point. -/
theorem chordPsi_ratio_le_noncentralScale
    {N : ℕ} (hN : 3 ≤ N) {a η : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hη : η ∈ Ico (0 : ℝ) (pathLogParameter a)) :
    chordPsi N a η / chordPsi (N + 1) a η ≤
      noncentralScale N := by
  by_cases hη0 : η = 0
  · subst η
    exact (chordPsi_ratio_zero_eq_noncentralScale hN ha0 ha1).le
  · exact (chordPsi_ratio_lt_noncentralScale hN ha0 ha1
      (lt_of_le_of_ne hη.1 (Ne.symm hη0)) hη.2).le

/-- The source's noncentral trigonometric-versus-hyperbolic comparison.
At a common `(N+1)`-channel value, strict `Phi` scaling and weak `Psi`
scaling force the strict `N`-channel ordering. -/
theorem chordPhi_gt_chordPsi_of_next_eq
    {N : ℕ} (hN : 3 ≤ N) {a θ0 η : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hθ0 : θ0 ∈ Ioc (0 : ℝ) (Real.pi / 2))
    (hnodal : Real.sin ((N : ℝ) * θ0) ≠ 0)
    (hη : η ∈ Ico (0 : ℝ) (pathLogParameter a))
    (hchannel :
      chordPhi (N + 1) a (noncentralScale N * θ0) =
        chordPsi (N + 1) a η) :
    chordPsi N a η < chordPhi N a θ0 := by
  have hN1 : 1 ≤ N := by omega
  have hM2 : 2 ≤ N + 1 := by omega
  have hκ0 : 0 < noncentralScale N := noncentralScale_pos hN1
  have hκ1 : noncentralScale N < 1 := noncentralScale_lt_one N
  have hθpos : 0 < noncentralScale N * θ0 := mul_pos hκ0 hθ0.1
  have hθle : noncentralScale N * θ0 ≤ Real.pi / 2 :=
    (mul_le_of_le_one_left hθ0.1.le hκ1.le).trans hθ0.2
  have hθltpi : noncentralScale N * θ0 < Real.pi := by
    nlinarith [hθle, Real.pi_pos]
  have hθpi : noncentralScale N * θ0 ≤ Real.pi := hθltpi.le
  have hsin : 0 < Real.sin (noncentralScale N * θ0) :=
    Real.sin_pos_of_pos_of_lt_pi hθpos hθltpi
  have hmultiple :
      (((N + 1 : ℕ) : ℝ) * (noncentralScale N * θ0)) =
        (N : ℝ) * θ0 := by
    unfold noncentralScale
    field_simp
  have hPhiM :
      0 < chordPhi (N + 1) a (noncentralScale N * θ0) := by
    rw [chordPhi_eq_sine_quotient a (noncentralScale N * θ0) hM2
      hθpos.le hθpi (ne_of_gt hsin), hmultiple]
    exact div_pos
      (mul_pos (halfTrigRadical_pos_of_parameter ha0 ha1 _)
        (abs_pos.mpr hnodal)) hsin
  have hPsiM : 0 < chordPsi (N + 1) a η := by
    rw [← hchannel]
    exact hPhiM
  have hPhiRatio :=
    chordPhi_ratio_gt_noncentralScale hN ha0 ha1 hθ0 hnodal
  have hPsiRatio :=
    chordPsi_ratio_le_noncentralScale hN ha0 ha1 hη
  have hPhiScaled :
      noncentralScale N *
          chordPhi (N + 1) a (noncentralScale N * θ0) <
        chordPhi N a θ0 :=
    (lt_div_iff₀ hPhiM).1 hPhiRatio
  have hPsiScaled :
      chordPsi N a η ≤ noncentralScale N * chordPsi (N + 1) a η :=
    (div_le_iff₀ hPsiM).1 hPsiRatio
  rw [hchannel] at hPhiScaled
  exact hPsiScaled.trans_lt hPhiScaled

end

end ConnectedPseudospectrum
