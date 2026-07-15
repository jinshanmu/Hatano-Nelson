import ConnectedPseudospectrum.MiddleBranchContinuation

/-!
# Exhaustion of the selected middle branch by the chord family

The global continuation theorem classifies every point of a positive-half
spectral gap.  Here the reconstructed inner angle is extended continuously to
the two spectral endpoints and its exact endpoint values are computed.  The
intermediate value theorem then shows that every interior chord parameter is
attained by the selected branch.  Reverse classification and uniqueness of
the endpoint-side outer solution identify that attained point with the
canonical chord.  No monotonicity of the chord abscissa is used.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- The angle reconstructed from the selected folded coordinates is
continuous on the real axis, including at the spectral endpoints. -/
theorem continuous_selectedMiddleAngle (d : PositiveHalfGap) :
    Continuous (selectedMiddleAngle d) := by
  unfold selectedMiddleAngle
  exact Real.continuous_arccos.comp (continuous_selectedMiddleY d)

/-- The selected signed branch vanishes at the lower endpoint of its exact
spectral gap. -/
theorem selectedMiddleRoot_positiveHalfGapLower_eq_zero
    (d : PositiveHalfGap) :
    selectedMiddleRoot d (positiveHalfGapLower d) = 0 := by
  have hn : 0 < d.K - 1 := by
    have hK := d.hK
    omega
  have hr : 0 < pathRate d.a := Real.sqrt_pos.2 d.ha0
  have hrsq : pathRate d.a ^ 2 = d.a := Real.sq_sqrt d.ha0.le
  have hzero := middleBranchExtension_symmetricPathEigenvalue_sq_eq_zero
    (d.K - 1) hn d.j hr
      ⟨d.j, by
        have hjUpper := d.hjUpper
        omega⟩
  rw [hrsq] at hzero
  simpa only [selectedMiddleRoot, positiveHalfGapLower] using hzero

/-- The selected signed branch vanishes at the upper endpoint of its exact
spectral gap. -/
theorem selectedMiddleRoot_positiveHalfGapUpper_eq_zero
    (d : PositiveHalfGap) :
    selectedMiddleRoot d (positiveHalfGapUpper d) = 0 := by
  have hn : 0 < d.K - 1 := by
    have hK := d.hK
    omega
  have hr : 0 < pathRate d.a := Real.sqrt_pos.2 d.ha0
  have hrsq : pathRate d.a ^ 2 = d.a := Real.sq_sqrt d.ha0.le
  have hzero := middleBranchExtension_symmetricPathEigenvalue_sq_eq_zero
    (d.K - 1) hn d.j hr
      ⟨d.j - 1, by
        have hjUpper := d.hjUpper
        omega⟩
  rw [hrsq] at hzero
  simpa only [selectedMiddleRoot, positiveHalfGapUpper] using hzero

private theorem cos_nonneg_on_positiveHalfGapAngle
    (d : PositiveHalfGap) (θ : d.Angle) :
    0 ≤ Real.cos θ := by
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
  · linarith [Real.pi_pos, d.angleLower_pos, θ.2.1]
  · exact θ.2.2.trans d.angleUpper_le_half

private theorem cos_sq_lt_cosh_pathLogParameter_sq
    (d : PositiveHalfGap) (θ : ℝ) :
    Real.cos θ ^ 2 < Real.cosh (pathLogParameter d.a) ^ 2 := by
  rw [sq_lt_sq]
  rw [abs_of_pos (Real.cosh_pos (pathLogParameter d.a))]
  exact (Real.abs_cos_le_one θ).trans_lt
    (Real.one_lt_cosh.mpr
      (pathLogParameter_pos d.ha0 d.ha1).ne')

private theorem selectedMiddleCoordinates_eq_outerChordFamily_of_ordered_agreement
    (d : PositiveHalfGap) (θ : d.Angle)
    (horder : Real.cos θ ^ 2 < outerChordFamilyZ d θ ^ 2)
    (hagree : outerChordFamilySignedRoot d θ =
      selectedMiddleRoot d (outerChordFamilyX d θ)) :
    selectedMiddleY d (outerChordFamilyX d θ) = Real.cos θ ∧
      selectedMiddleZ d (outerChordFamilyX d θ) =
        outerChordFamilyZ d θ := by
  have hz := outerChordFamilyZ_abs_le_cosh d θ
  have hsign := negOnePow_sq d.j
  have hminus :
      foldXiMinus d.a (outerChordFamilyX d θ)
          (selectedMiddleRoot d (outerChordFamilyX d θ)) =
        halfFoldArgument (Real.cos θ) := by
    rw [← hagree]
    unfold outerChordFamilyX outerChordFamilySignedRoot outerChordFamilyS
    rw [foldXiMinus_signed_outerChord d.ha0 hz horder hsign]
    unfold halfFoldArgument
    rfl
  have hplus :
      foldXiPlus d.a (outerChordFamilyX d θ)
          (selectedMiddleRoot d (outerChordFamilyX d θ)) =
        halfFoldArgument (outerChordFamilyZ d θ) := by
    rw [← hagree]
    unfold outerChordFamilyX outerChordFamilySignedRoot outerChordFamilyS
    rw [foldXiPlus_signed_outerChord d.ha0 hz horder hsign]
    unfold halfFoldArgument
    rfl
  exact foldedHalfVariables_eq_of_generic
    (cos_nonneg_on_positiveHalfGapAngle d θ)
    (outerChordFamilyZ_nonneg d θ) hminus hplus

/-- At the lower spectral endpoint the reconstructed inner half variable is
the cosine of the right nodal endpoint. -/
theorem selectedMiddleY_positiveHalfGapLower
    (d : PositiveHalfGap) :
    selectedMiddleY d (positiveHalfGapLower d) =
      Real.cos d.angleUpper := by
  have hx : positiveHalfGapLower d = outerChordFamilyX d d.rightAngle := by
    simpa only [positiveHalfGapLower] using
      (outerChordFamilyX_rightAngle_eq_symmetricPathEigenvalue d).symm
  have hagree :
      outerChordFamilySignedRoot d d.rightAngle =
        selectedMiddleRoot d (outerChordFamilyX d d.rightAngle) := by
    rw [outerChordFamilySignedRoot_rightAngle, ← hx,
      selectedMiddleRoot_positiveHalfGapLower_eq_zero]
  have horder :
      Real.cos (d.rightAngle : ℝ) ^ 2 <
        outerChordFamilyZ d d.rightAngle ^ 2 := by
    rw [outerChordFamilyZ_rightAngle]
    exact cos_sq_lt_cosh_pathLogParameter_sq d d.rightAngle
  have hcoordinates :=
    selectedMiddleCoordinates_eq_outerChordFamily_of_ordered_agreement
      d d.rightAngle horder hagree
  calc
    selectedMiddleY d (positiveHalfGapLower d) =
        selectedMiddleY d (outerChordFamilyX d d.rightAngle) :=
      congrArg (selectedMiddleY d) hx
    _ = Real.cos d.rightAngle := hcoordinates.1
    _ = Real.cos d.angleUpper := rfl

/-- At the upper spectral endpoint the reconstructed inner half variable is
the cosine of the left nodal endpoint. -/
theorem selectedMiddleY_positiveHalfGapUpper
    (d : PositiveHalfGap) :
    selectedMiddleY d (positiveHalfGapUpper d) =
      Real.cos d.angleLower := by
  have hx : positiveHalfGapUpper d = outerChordFamilyX d d.leftAngle := by
    simpa only [positiveHalfGapUpper] using
      (outerChordFamilyX_leftAngle_eq_symmetricPathEigenvalue d).symm
  have hagree :
      outerChordFamilySignedRoot d d.leftAngle =
        selectedMiddleRoot d (outerChordFamilyX d d.leftAngle) := by
    rw [outerChordFamilySignedRoot_leftAngle, ← hx,
      selectedMiddleRoot_positiveHalfGapUpper_eq_zero]
  have horder :
      Real.cos (d.leftAngle : ℝ) ^ 2 <
        outerChordFamilyZ d d.leftAngle ^ 2 := by
    rw [outerChordFamilyZ_leftAngle]
    exact cos_sq_lt_cosh_pathLogParameter_sq d d.leftAngle
  have hcoordinates :=
    selectedMiddleCoordinates_eq_outerChordFamily_of_ordered_agreement
      d d.leftAngle horder hagree
  calc
    selectedMiddleY d (positiveHalfGapUpper d) =
        selectedMiddleY d (outerChordFamilyX d d.leftAngle) :=
      congrArg (selectedMiddleY d) hx
    _ = Real.cos d.leftAngle := hcoordinates.1
    _ = Real.cos d.angleLower := rfl

/-- The reconstructed angle takes the right nodal value at the lower
spectral endpoint. -/
@[simp] theorem selectedMiddleAngle_positiveHalfGapLower
    (d : PositiveHalfGap) :
    selectedMiddleAngle d (positiveHalfGapLower d) = d.angleUpper := by
  unfold selectedMiddleAngle
  rw [selectedMiddleY_positiveHalfGapLower]
  have hupperPos : 0 ≤ d.angleUpper :=
    (d.angleLower_pos.trans d.angleLower_lt_angleUpper).le
  have hupperPi : d.angleUpper ≤ Real.pi :=
    d.angleUpper_le_half.trans (by linarith [Real.pi_pos])
  exact Real.arccos_cos hupperPos hupperPi

/-- The reconstructed angle takes the left nodal value at the upper spectral
endpoint. -/
@[simp] theorem selectedMiddleAngle_positiveHalfGapUpper
    (d : PositiveHalfGap) :
    selectedMiddleAngle d (positiveHalfGapUpper d) = d.angleLower := by
  unfold selectedMiddleAngle
  rw [selectedMiddleY_positiveHalfGapUpper]
  have hlowerPi : d.angleLower ≤ Real.pi :=
    d.angleLower_lt_angleUpper.le.trans
      (d.angleUpper_le_half.trans (by linarith [Real.pi_pos]))
  exact Real.arccos_cos d.angleLower_pos.le hlowerPi

/-- The displayed endpoints defining a positive-half spectral gap are
strictly ordered. -/
theorem positiveHalfGapLower_lt_positiveHalfGapUpper
    (d : PositiveHalfGap) :
    positiveHalfGapLower d < positiveHalfGapUpper d := by
  have hr : 0 < pathRate d.a := Real.sqrt_pos.2 d.ha0
  have hindex :
      (⟨d.j - 1, by
        have hjUpper := d.hjUpper
        omega⟩ : Fin (d.K - 1)) <
      ⟨d.j, by
        have hjUpper := d.hjUpper
        omega⟩ := by
    exact Fin.mk_lt_mk.mpr (Nat.sub_lt d.hj Nat.one_pos)
  unfold positiveHalfGapLower positiveHalfGapUpper
  exact symmetricPathEigenvalue_strictAnti (d.K - 1) hr hindex

/-- Every interior nodal parameter occurs as the reconstructed angle of a
selected middle-branch point in the exact open spectral gap. -/
theorem exists_gapPoint_selectedMiddleAngle_eq
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper) :
    ∃ x : ℝ, x ∈ positiveHalfSpectralGap d ∧
      selectedMiddleAngle d x = θ := by
  have hgap := positiveHalfGapLower_lt_positiveHalfGapUpper d
  have hθ : (θ : ℝ) ∈
      Ioo
        (selectedMiddleAngle d (positiveHalfGapUpper d))
        (selectedMiddleAngle d (positiveHalfGapLower d)) := by
    simpa only [selectedMiddleAngle_positiveHalfGapUpper,
      selectedMiddleAngle_positiveHalfGapLower] using ⟨hleft, hright⟩
  obtain ⟨x, hx, hangle⟩ :=
    intermediate_value_Ioo' hgap.le
      (continuous_selectedMiddleAngle d).continuousOn hθ
  exact ⟨x, hx, hangle⟩

/-- A prescribed interior chord is exactly the selected signed middle branch
at its own abscissa.  This packages both gap membership and root agreement. -/
theorem outerChordFamily_selectedMiddle_agreement
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper) :
    outerChordFamilyX d θ ∈ positiveHalfSpectralGap d ∧
      outerChordFamilySignedRoot d θ =
        selectedMiddleRoot d (outerChordFamilyX d θ) := by
  obtain ⟨x, hxGap, hangle⟩ :=
    exists_gapPoint_selectedMiddleAngle_eq d θ hleft hright
  have hclass : x ∈ middleBranchRawClassifiedSet d :=
    positiveHalfSpectralGap_subset_middleBranchRawClassifiedSet d hxGap
  obtain ⟨φ, hφLeft, hφRight, hY, _hZ, hX, hroot⟩ :=
    exists_outerChordFamily_representation_of_classified d
      ⟨hxGap, hclass⟩
  have hφNonneg : 0 ≤ (φ : ℝ) :=
    d.angleLower_pos.le.trans hφLeft.le
  have hφPi : (φ : ℝ) ≤ Real.pi :=
    hφRight.le.trans
      (d.angleUpper_le_half.trans (by linarith [Real.pi_pos]))
  have hselectedAngleEqφ : selectedMiddleAngle d x = (φ : ℝ) := by
    unfold selectedMiddleAngle
    rw [hY, Real.arccos_cos hφNonneg hφPi]
  have hφθ : φ = θ := by
    apply Subtype.ext
    exact hselectedAngleEqφ.symm.trans hangle
  subst φ
  constructor
  · rw [← hX]
    exact hxGap
  · rw [← hX]
    exact hroot.symm

/-- Every interior chord abscissa belongs to the exact positive-half
spectral gap. -/
theorem outerChordFamilyX_mem_positiveHalfSpectralGap
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper) :
    outerChordFamilyX d θ ∈ positiveHalfSpectralGap d :=
  (outerChordFamily_selectedMiddle_agreement d θ hleft hright).1

/-- Every interior signed chord root is the selected middle signed root at
the chord abscissa. -/
theorem outerChordFamilySignedRoot_eq_selectedMiddleRoot
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper) :
    outerChordFamilySignedRoot d θ =
      selectedMiddleRoot d (outerChordFamilyX d θ) :=
  (outerChordFamily_selectedMiddle_agreement d θ hleft hright).2

/-- The positive chord magnitude is the actual finite-dimensional Euclidean
least singular value at the chord abscissa. -/
theorem realGapValue_outerChordFamilyX_eq_outerChordFamilyS
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper) :
    realGapValue (d.K - 1) d.a (outerChordFamilyX d θ) =
      outerChordFamilyS d θ := by
  have hagree := outerChordFamilySignedRoot_eq_selectedMiddleRoot
    d θ hleft hright
  have hsign := negOnePow_sq d.j
  change selectedMiddleHeight d (outerChordFamilyX d θ) =
    outerChordFamilyS d θ
  calc
    selectedMiddleHeight d (outerChordFamilyX d θ) =
        1 * selectedMiddleHeight d (outerChordFamilyX d θ) := by ring
    _ = ((-1 : ℝ) ^ d.j) ^ 2 *
        selectedMiddleHeight d (outerChordFamilyX d θ) := by rw [hsign]
    _ = (-1 : ℝ) ^ d.j *
        selectedMiddleRoot d (outerChordFamilyX d θ) := by
      rw [selectedMiddleRoot_eq_negOnePow_mul_height]
      ring
    _ = (-1 : ℝ) ^ d.j * outerChordFamilySignedRoot d θ := by
      rw [← hagree]
    _ = ((-1 : ℝ) ^ d.j) ^ 2 * outerChordFamilyS d θ := by
      unfold outerChordFamilySignedRoot
      ring
    _ = outerChordFamilyS d θ := by rw [hsign, one_mul]

end

end ConnectedPseudospectrum
