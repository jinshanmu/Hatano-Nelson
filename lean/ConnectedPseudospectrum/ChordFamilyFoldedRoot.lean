import ConnectedPseudospectrum.ChordFamily
import ConnectedPseudospectrum.OuterChordGeneric
import ConnectedPseudospectrum.ChordSignClassification
import ConnectedPseudospectrum.PathSpectrum

/-!
# The endpoint-side chord family solves the folded determinant equation

The channel-level identity defining the endpoint-side outer solution is
converted here into the signed Chebyshev equation.  The coordinate-free
folded reductions then prove that every interior member of the continuous
chord family is an exact root of the appropriate even or odd folded sequence,
including after the outer coordinate crosses through `z = 1`.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- Above the first Chebyshev node, the outer Chebyshev factor has positive
sign. -/
theorem chebyshevU_pos_of_firstNode_lt
    {K : ℕ} (hK : 2 ≤ K) {z : ℝ}
    (hz : Real.cos (Real.pi / K) < z) :
    0 < chebyshevU (K - 1 : ℕ) z := by
  rw [chebyshevU_eq_chordNodeProduct K hK]
  apply mul_pos
  · positivity
  · unfold chordNodeProduct
    apply Finset.prod_pos
    intro q hq
    exact sub_pos.mpr ((chordNode_le_first K hK hq).trans_lt hz)

/-- For `K≥2`, the first Chebyshev node lies in the nonnegative half-line. -/
theorem cos_pi_div_nat_nonneg {K : ℕ} (hK : 2 ≤ K) :
    0 ≤ Real.cos (Real.pi / K) := by
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
  · have hdiv : 0 ≤ Real.pi / (K : ℝ) := by positivity
    linarith [Real.pi_pos]
  · have hKpos : (0 : ℝ) < K := by exact_mod_cast (Nat.zero_lt_two.trans_le hK)
    rw [div_le_iff₀ hKpos]
    have hKcast : (2 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith [Real.pi_pos]

theorem outerChordFamilyZ_nonneg
    (d : PositiveHalfGap) (θ : d.Angle) :
    0 ≤ outerChordFamilyZ d θ := by
  have hp0 : 0 ≤ outerLobeMaximizer d :=
    (cos_pi_div_nat_nonneg d.hK).trans
      (outerLobeMaximizer_spec d).1.1.le
  exact hp0.trans (outerChordFamilyZ_mem d θ).1

theorem outerChordFamilyZ_abs_le_cosh
    (d : PositiveHalfGap) (θ : d.Angle) :
    |outerChordFamilyZ d θ| ≤ Real.cosh (pathLogParameter d.a) := by
  rw [abs_of_nonneg (outerChordFamilyZ_nonneg d θ)]
  exact (outerChordFamilyZ_mem d θ).2

/-- Strict sheet ordering for every interior family member. -/
theorem outerChordFamily_cos_sq_lt_z_sq
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper) :
    Real.cos θ ^ 2 < outerChordFamilyZ d θ ^ 2 := by
  have hcosNonneg : 0 ≤ Real.cos θ := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · linarith [Real.pi_pos, d.angleLower_pos, hleft]
    · exact θ.2.2.trans d.hhalf
  have hzNonneg := outerChordFamilyZ_nonneg d θ
  have hgt := outerEndpointSide_gt_innerCos d.hK d.hj hleft
    (θ.2.2.trans d.hhalf) (outerLobeMaximizer_spec d).1
    (outerLobeMaximizer_lt_outerChordFamilyZ d θ hleft hright)
  nlinarith

/-- For `0<a<1`, the trigonometric chord radical is strictly positive at
every real angle. -/
theorem halfTrigRadical_pos_of_pathParameter
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    0 < halfTrigRadical a θ := by
  unfold halfTrigRadical
  apply Real.sqrt_pos.2
  rw [chordRadicand_cos_eq_sinh_sq_add_sin_sq]
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha0 ha1
  have hsinh : 0 < Real.sinh (pathLogParameter a) :=
    Real.sinh_pos_iff.mpr hh
  nlinarith [sq_pos_of_pos hsinh, sq_nonneg (Real.sin θ)]

/-- The selected outer variable cannot reach the radical endpoint at an
interior inner parameter. -/
theorem outerChordFamilyZ_lt_cosh
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper) :
    outerChordFamilyZ d θ < Real.cosh (pathLogParameter d.a) := by
  have hPhi : 0 < chordPhi d.K d.a θ :=
    chordPhi_pos_on_nodalInterval d.K d.j d.hK
      ((Nat.lt_succ_self d.j).trans d.hjUpper) d.a ⟨hleft, hright⟩
      (halfTrigRadical_pos_of_pathParameter d.ha0 d.ha1 θ)
  have hle := (outerChordFamilyZ_mem d θ).2
  exact lt_of_le_of_ne hle fun heq => by
    have hweight := chordLobeWeight_outerChordFamilyZ d θ
    rw [heq, chordLobeWeight_cosh_endpoint] at hweight
    linarith

/-- The coordinate-free height is strictly positive in the open angle
interval. -/
theorem outerChordFamilyS_pos
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper) :
    0 < outerChordFamilyS d θ := by
  unfold outerChordFamilyS
  exact outerChordS_pos_of_nonneg_of_lt_cosh d.ha0 d.ha1 θ
    (outerChordFamilyZ_nonneg d θ)
    (outerChordFamilyZ_lt_cosh d θ hleft hright)

theorem outerChordFamilySignedRoot_ne_zero
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper) :
    outerChordFamilySignedRoot d θ ≠ 0 := by
  unfold outerChordFamilySignedRoot
  exact mul_ne_zero (pow_ne_zero d.j (by norm_num))
    (outerChordFamilyS_pos d θ hleft hright).ne'

/-- The defining equality of levels is exactly the source's signed
coordinate-free Chebyshev chord equation. -/
theorem outerChordFamily_signed_chord_equation
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper) :
    halfTrigRadical d.a θ *
        chebyshevU (d.K - 1 : ℕ) (Real.cos θ) =
      (-1 : ℝ) ^ d.j *
        outerChordRadical d.a (outerChordFamilyZ d θ) *
          chebyshevU (d.K - 1 : ℕ) (outerChordFamilyZ d θ) := by
  have hinner :=
    halfTrigRadical_mul_chebyshevU_eq_negOnePow_mul_chordPhi
      d.K d.j d.hK ((Nat.lt_succ_self d.j).trans d.hjUpper) d.a
      ⟨hleft, hright⟩
  have hzFirst : Real.cos (Real.pi / d.K) < outerChordFamilyZ d θ :=
    (outerLobeMaximizer_spec d).1.1.trans
      (outerLobeMaximizer_lt_outerChordFamilyZ d θ hleft hright)
  have houterPos := chebyshevU_pos_of_firstNode_lt d.hK hzFirst
  have houter := chordLobeWeight_outerChordFamilyZ d θ
  unfold chordLobeWeight at houter
  rw [abs_of_pos houterPos] at houter
  change outerChordRadical d.a (outerChordFamilyZ d θ) *
      chebyshevU (d.K - 1 : ℕ) (outerChordFamilyZ d θ) =
        chordPhi d.K d.a θ at houter
  calc
    halfTrigRadical d.a θ *
          chebyshevU (d.K - 1 : ℕ) (Real.cos θ) =
        (-1 : ℝ) ^ d.j * chordPhi d.K d.a θ := hinner
    _ = (-1 : ℝ) ^ d.j *
        outerChordRadical d.a (outerChordFamilyZ d θ) *
          chebyshevU (d.K - 1 : ℕ) (outerChordFamilyZ d θ) := by
      calc
        (-1 : ℝ) ^ d.j * chordPhi d.K d.a θ =
            (-1 : ℝ) ^ d.j *
              (outerChordRadical d.a (outerChordFamilyZ d θ) *
                chebyshevU (d.K - 1 : ℕ) (outerChordFamilyZ d θ)) := by
          rw [houter]
        _ = _ := by ring

theorem negOnePow_sq (j : ℕ) : ((-1 : ℝ) ^ j) ^ 2 = 1 := by
  rcases neg_one_pow_eq_or ℝ j with hj | hj <;> rw [hj] <;> norm_num

/-- For odd `K=2m+1`, every interior chord is an exact root of the even
folded sequence. -/
theorem foldEvenSequence_outerChordFamily_eq_zero
    (d : PositiveHalfGap) (m : ℕ) (hK : d.K = 2 * m + 1)
    (θ : d.Angle) (hleft : d.angleLower < θ)
    (hright : θ < d.angleUpper) :
    foldEvenSequence d.a (outerChordFamilyX d θ)
        (outerChordFamilySignedRoot d θ) m = 0 := by
  have hiff := foldEvenSequence_signed_outerChord_eq_zero_iff m d.ha0
    d.ha1.ne (outerChordFamilyZ_abs_le_cosh d θ)
    (outerChordFamily_cos_sq_lt_z_sq d θ hleft hright)
    (negOnePow_sq d.j)
  change foldEvenSequence d.a
    (outerChordX d.a θ (outerChordFamilyZ d θ))
    ((-1 : ℝ) ^ d.j * outerChordS d.a θ (outerChordFamilyZ d θ)) m = 0
  apply hiff.2
  have hchord := outerChordFamily_signed_chord_equation d θ hleft hright
  have hindex : d.K - 1 = 2 * m := by omega
  simpa only [hindex] using hchord

/-- On a noncentral positive-half interval, the inner cosine is strictly
positive. -/
theorem cos_pos_on_positiveHalfGap
    (d : PositiveHalfGap) (θ : d.Angle)
    (hright : θ < d.angleUpper) :
    0 < Real.cos θ := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · linarith [Real.pi_pos, d.angleLower_pos, θ.2.1]
  · exact hright.trans_le d.hhalf

/-- For even `K=2m+2`, every interior chord is an exact root of the odd
folded sequence. -/
theorem foldOddSequence_outerChordFamily_eq_zero
    (d : PositiveHalfGap) (m : ℕ) (hK : d.K = 2 * m + 2)
    (θ : d.Angle) (hleft : d.angleLower < θ)
    (hright : θ < d.angleUpper) :
    foldOddSequence d.a (outerChordFamilyX d θ)
        (outerChordFamilySignedRoot d θ) m = 0 := by
  have hiff := foldOddSequence_signed_outerChord_eq_zero_iff m d.ha0
    d.ha1.ne (outerChordFamilyZ_abs_le_cosh d θ)
    (outerChordFamily_cos_sq_lt_z_sq d θ hleft hright)
    (negOnePow_sq d.j) (cos_pos_on_positiveHalfGap d θ hright).ne'
  change foldOddSequence d.a
    (outerChordX d.a θ (outerChordFamilyZ d θ))
    ((-1 : ℝ) ^ d.j * outerChordS d.a θ (outerChordFamilyZ d θ)) m = 0
  apply hiff.2
  have hchord := outerChordFamily_signed_chord_equation d θ hleft hright
  have hindex : d.K - 1 = 2 * m + 1 := by omega
  simpa only [hindex] using hchord

/-- The upper endpoint has the exact displayed path eigenvalue index `j-1`. -/
theorem outerChordFamilyX_leftAngle_eq_symmetricPathEigenvalue
    (d : PositiveHalfGap) :
    outerChordFamilyX d d.leftAngle =
      symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
        ⟨d.j - 1, by
          have hjUpper := d.hjUpper
          have hj := d.hj
          omega⟩ := by
  rw [outerChordFamilyX_leftAngle]
  unfold symmetricPathEigenvalue pathEigenangle PositiveHalfGap.angleLower
  have hKone : 1 ≤ d.K := le_trans (by norm_num) d.hK
  have hden : d.K - 1 + 1 = d.K := Nat.sub_add_cancel hKone
  have hjone : 1 ≤ d.j := d.hj
  have hnum : d.j - 1 + 1 = d.j := Nat.sub_add_cancel hjone
  simp only [hden, hnum]

/-- The lower endpoint has the exact displayed path eigenvalue index `j`. -/
theorem outerChordFamilyX_rightAngle_eq_symmetricPathEigenvalue
    (d : PositiveHalfGap) :
    outerChordFamilyX d d.rightAngle =
      symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
        ⟨d.j, by
          have hjUpper := d.hjUpper
          omega⟩ := by
  rw [outerChordFamilyX_rightAngle]
  unfold symmetricPathEigenvalue pathEigenangle PositiveHalfGap.angleUpper
  have hKone : 1 ≤ d.K := le_trans (by norm_num) d.hK
  have hden : d.K - 1 + 1 = d.K := Nat.sub_add_cancel hKone
  simp only [hden]

end

end ConnectedPseudospectrum
