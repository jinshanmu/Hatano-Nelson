import ConnectedPseudospectrum.MiddleBranchCoordinates

/-!
# Reverse classification of the selected middle branch

This module proves the converse direction in the source's chord
classification.  A selected middle root on the strict classified sheet is
first reconstructed as a coordinate-free signed outer chord.  The literal
signed-pencil determinant is then split by dimension parity, and the exact
even or odd folded zero characterization forces equality of the inner and
outer lobe levels.  Strict endpoint-side injectivity consequently identifies
the reconstructed outer coordinate with the canonical chord family.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- The inner angle reconstructed from the nonnegative folded half
variable. -/
def selectedMiddleAngle (d : PositiveHalfGap) (x : ℝ) : ℝ :=
  Real.arccos (selectedMiddleY d x)

theorem selectedMiddleY_mem_Icc_of_classified
    (d : PositiveHalfGap) {x : ℝ}
    (hclass : x ∈ middleBranchRawClassifiedSet d) :
    selectedMiddleY d x ∈ Icc (-1 : ℝ) 1 := by
  change
    0 < selectedMiddleDiscriminant d x ∧
      Real.cos d.angleUpper < selectedMiddleY d x ∧
      selectedMiddleY d x < Real.cos d.angleLower ∧
      outerLobeMaximizer d < selectedMiddleZ d x ∧
      selectedMiddleZ d x < Real.cosh (pathLogParameter d.a) at hclass
  exact ⟨
    (Real.neg_one_le_cos d.angleUpper).trans hclass.2.1.le,
    hclass.2.2.1.le.trans (Real.cos_le_one d.angleLower)⟩

theorem selectedMiddleAngle_cos_of_classified
    (d : PositiveHalfGap) {x : ℝ}
    (hclass : x ∈ middleBranchRawClassifiedSet d) :
    Real.cos (selectedMiddleAngle d x) = selectedMiddleY d x := by
  unfold selectedMiddleAngle
  have hy := selectedMiddleY_mem_Icc_of_classified d hclass
  exact Real.cos_arccos hy.1 hy.2

/-- The reconstructed angle lies strictly in the target nodal interval. -/
theorem selectedMiddleAngle_mem_openGap_of_classified
    (d : PositiveHalfGap) {x : ℝ}
    (hclass : x ∈ middleBranchRawClassifiedSet d) :
    d.angleLower < selectedMiddleAngle d x ∧
      selectedMiddleAngle d x < d.angleUpper := by
  have hc := hclass
  change
    0 < selectedMiddleDiscriminant d x ∧
      Real.cos d.angleUpper < selectedMiddleY d x ∧
      selectedMiddleY d x < Real.cos d.angleLower ∧
      outerLobeMaximizer d < selectedMiddleZ d x ∧
      selectedMiddleZ d x < Real.cosh (pathLogParameter d.a) at hc
  have hy := selectedMiddleY_mem_Icc_of_classified d hclass
  have hupperPos : 0 < d.angleUpper :=
    d.angleLower_pos.trans d.angleLower_lt_angleUpper
  have hhalfPi : Real.pi / 2 ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hlowerPi : d.angleLower ≤ Real.pi :=
    d.angleLower_lt_angleUpper.le.trans
      (d.angleUpper_le_half.trans hhalfPi)
  have hupperPi : d.angleUpper ≤ Real.pi :=
    d.angleUpper_le_half.trans hhalfPi
  constructor
  · have h := Real.arccos_lt_arccos hy.1 hc.2.2.1
      (Real.cos_le_one d.angleLower)
    rw [Real.arccos_cos d.angleLower_pos.le hlowerPi] at h
    exact h
  · have h := Real.arccos_lt_arccos
      (Real.neg_one_le_cos d.angleUpper) hc.2.1 hy.2
    rw [Real.arccos_cos hupperPos.le hupperPi] at h
    exact h

theorem selectedMiddleY_pos_of_classified
    (d : PositiveHalfGap) {x : ℝ}
    (hclass : x ∈ middleBranchRawClassifiedSet d) :
    0 < selectedMiddleY d x := by
  change
    0 < selectedMiddleDiscriminant d x ∧
      Real.cos d.angleUpper < selectedMiddleY d x ∧
      selectedMiddleY d x < Real.cos d.angleLower ∧
      outerLobeMaximizer d < selectedMiddleZ d x ∧
      selectedMiddleZ d x < Real.cosh (pathLogParameter d.a) at hclass
  have hcos : 0 ≤ Real.cos d.angleUpper := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · have hupperPos : 0 < d.angleUpper :=
        d.angleLower_pos.trans d.angleLower_lt_angleUpper
      linarith [Real.pi_pos]
    · exact d.angleUpper_le_half
  exact hcos.trans_lt hclass.2.1

theorem selectedMiddleZ_pos_of_classified
    (d : PositiveHalfGap) {x : ℝ}
    (hclass : x ∈ middleBranchRawClassifiedSet d) :
    0 < selectedMiddleZ d x := by
  change
    0 < selectedMiddleDiscriminant d x ∧
      Real.cos d.angleUpper < selectedMiddleY d x ∧
      selectedMiddleY d x < Real.cos d.angleLower ∧
      outerLobeMaximizer d < selectedMiddleZ d x ∧
      selectedMiddleZ d x < Real.cosh (pathLogParameter d.a) at hclass
  have hmaxNonneg : 0 ≤ outerLobeMaximizer d :=
    (cos_pi_div_nat_nonneg d.hK).trans
      (outerLobeMaximizer_spec d).1.1.le
  exact hmaxNonneg.trans_lt hclass.2.2.2.1

theorem foldXiMinus_ge_negOne_selectedMiddle_of_classified
    (d : PositiveHalfGap) {x : ℝ}
    (hclass : x ∈ middleBranchRawClassifiedSet d) :
    -1 ≤ foldXiMinus d.a x (selectedMiddleRoot d x) := by
  have hyPos := selectedMiddleY_pos_of_classified d hclass
  have hsqrt :
      0 < Real.sqrt
        ((foldXiMinus d.a x (selectedMiddleRoot d x) + 1) / 2) := by
    simpa only [selectedMiddleY, foldedHalfY] using hyPos
  have harg := Real.sqrt_pos.1 hsqrt
  linarith

theorem foldXiPlus_ge_negOne_selectedMiddle_of_classified
    (d : PositiveHalfGap) {x : ℝ}
    (hclass : x ∈ middleBranchRawClassifiedSet d) :
    -1 ≤ foldXiPlus d.a x (selectedMiddleRoot d x) := by
  have hzPos := selectedMiddleZ_pos_of_classified d hclass
  have hsqrt :
      0 < Real.sqrt
        ((foldXiPlus d.a x (selectedMiddleRoot d x) + 1) / 2) := by
    simpa only [selectedMiddleZ, foldedHalfZ] using hzPos
  have harg := Real.sqrt_pos.1 hsqrt
  linarith

theorem foldXiMinus_selectedMiddle_eq_halfFoldArgument
    (d : PositiveHalfGap) {x : ℝ}
    (hclass : x ∈ middleBranchRawClassifiedSet d) :
    foldXiMinus d.a x (selectedMiddleRoot d x) =
      halfFoldArgument (selectedMiddleY d x) := by
  simpa only [selectedMiddleY] using
    foldXiMinus_eq_halfFoldArgument_foldedHalfY
      (foldXiMinus_ge_negOne_selectedMiddle_of_classified d hclass)

theorem foldXiPlus_selectedMiddle_eq_halfFoldArgument
    (d : PositiveHalfGap) {x : ℝ}
    (hclass : x ∈ middleBranchRawClassifiedSet d) :
    foldXiPlus d.a x (selectedMiddleRoot d x) =
      halfFoldArgument (selectedMiddleZ d x) := by
  simpa only [selectedMiddleZ] using
    foldXiPlus_eq_halfFoldArgument_foldedHalfZ
      (foldXiPlus_ge_negOne_selectedMiddle_of_classified d hclass)

/-- Horizontal folded reconstruction identifies the actual abscissa with
the coordinate-free chord expression built from the selected half
variables. -/
theorem selectedMiddleX_eq_outerChordX_reconstruction
    (d : PositiveHalfGap) {x : ℝ}
    (hxGap : x ∈ positiveHalfSpectralGap d)
    (hclass : x ∈ middleBranchRawClassifiedSet d) :
    x = outerChordX d.a (selectedMiddleAngle d x)
      (selectedMiddleZ d x) := by
  have hc := hclass
  change
    0 < selectedMiddleDiscriminant d x ∧
      Real.cos d.angleUpper < selectedMiddleY d x ∧
      selectedMiddleY d x < Real.cos d.angleLower ∧
      outerLobeMaximizer d < selectedMiddleZ d x ∧
      selectedMiddleZ d x < Real.cosh (pathLogParameter d.a) at hc
  have hrec := x_eq_halfChordScale_mul_foldedHalf d.ha0 hc.1
    (foldXiMinus_ge_negOne_selectedMiddle_of_classified d hclass)
    (foldXiPlus_ge_negOne_selectedMiddle_of_classified d hclass)
    (positiveHalfSpectralGap_pos d hxGap)
  calc
    x = halfChordScale d.a * selectedMiddleY d x *
        selectedMiddleZ d x := by
      simpa only [selectedMiddleY, selectedMiddleZ] using hrec
    _ = outerChordX d.a (selectedMiddleAngle d x)
        (selectedMiddleZ d x) := by
      unfold outerChordX
      rw [selectedMiddleAngle_cos_of_classified d hclass]

/-- The actual selected signed root is the prescribed sign times the
coordinate-free chord magnitude reconstructed from its half variables. -/
theorem selectedMiddleRoot_eq_signed_outerChordS_reconstruction
    (d : PositiveHalfGap) {x : ℝ}
    (hxGap : x ∈ positiveHalfSpectralGap d)
    (hclass : x ∈ middleBranchRawClassifiedSet d) :
    selectedMiddleRoot d x =
      (-1 : ℝ) ^ d.j *
        outerChordS d.a (selectedMiddleAngle d x)
          (selectedMiddleZ d x) := by
  have hc := hclass
  change
    0 < selectedMiddleDiscriminant d x ∧
      Real.cos d.angleUpper < selectedMiddleY d x ∧
      selectedMiddleY d x < Real.cos d.angleLower ∧
      outerLobeMaximizer d < selectedMiddleZ d x ∧
      selectedMiddleZ d x < Real.cosh (pathLogParameter d.a) at hc
  have habsRec :=
    abs_s_eq_halfChordScale_mul_sqrt_foldedHalf_complements
      d.ha0 hc.1
      (foldXiMinus_ge_negOne_selectedMiddle_of_classified d hclass)
      (foldXiPlus_ge_negOne_selectedMiddle_of_classified d hclass)
  have habs :
      |selectedMiddleRoot d x| =
        outerChordS d.a (selectedMiddleAngle d x)
          (selectedMiddleZ d x) := by
    simpa only [outerChordS, selectedMiddleY, selectedMiddleZ,
      selectedMiddleAngle_cos_of_classified d hclass] using habsRec
  have hsignedPos :=
    negOnePow_mul_selectedMiddleRoot_pos_of_mem_gap d hxGap
  have hsignedAbs :
      (-1 : ℝ) ^ d.j * selectedMiddleRoot d x =
        |selectedMiddleRoot d x| := by
    calc
      (-1 : ℝ) ^ d.j * selectedMiddleRoot d x =
          |(-1 : ℝ) ^ d.j * selectedMiddleRoot d x| :=
        (abs_of_pos hsignedPos).symm
      _ = |selectedMiddleRoot d x| := by
        rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hsign := negOnePow_sq d.j
  calc
    selectedMiddleRoot d x =
        ((-1 : ℝ) ^ d.j) ^ 2 * selectedMiddleRoot d x := by
      rw [hsign, one_mul]
    _ = (-1 : ℝ) ^ d.j *
        ((-1 : ℝ) ^ d.j * selectedMiddleRoot d x) := by ring
    _ = (-1 : ℝ) ^ d.j * |selectedMiddleRoot d x| := by
      rw [hsignedAbs]
    _ = (-1 : ℝ) ^ d.j *
        outerChordS d.a (selectedMiddleAngle d x)
          (selectedMiddleZ d x) := by rw [habs]

private theorem abs_signedChordEquation
    {a θ z : ℝ} {n : ℤ} {j : ℕ}
    (heq :
      halfTrigRadical a θ * chebyshevU n (Real.cos θ) =
        (-1 : ℝ) ^ j * outerChordRadical a z * chebyshevU n z) :
    outerChordRadical a z * |chebyshevU n z| =
      halfTrigRadical a θ * |chebyshevU n (Real.cos θ)| := by
  have hinner : 0 ≤ halfTrigRadical a θ := by
    unfold halfTrigRadical
    positivity
  have houter : 0 ≤ outerChordRadical a z := by
    unfold outerChordRadical
    positivity
  have habs := congrArg abs heq
  calc
    outerChordRadical a z * |chebyshevU n z| =
        |(-1 : ℝ) ^ j * outerChordRadical a z *
          chebyshevU n z| := by
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_nonneg houter, one_mul]
    _ = |halfTrigRadical a θ * chebyshevU n (Real.cos θ)| :=
      habs.symm
    _ = halfTrigRadical a θ *
        |chebyshevU n (Real.cos θ)| := by
      rw [abs_mul, abs_of_nonneg hinner]

/-- Exact converse bridge: every selected middle root on the classified
sheet has equal endpoint-side outer and inner lobe levels. -/
theorem chordLobeWeight_selectedMiddleZ_eq_selectedMiddleY
    (d : PositiveHalfGap) {x : ℝ}
    (hx : x ∈ positiveHalfSpectralGap d ∩
      middleBranchRawClassifiedSet d) :
    chordLobeWeight d.K d.a (selectedMiddleZ d x) =
      chordLobeWeight d.K d.a (selectedMiddleY d x) := by
  have hclass := hx.2
  have hc := hclass
  change
    0 < selectedMiddleDiscriminant d x ∧
      Real.cos d.angleUpper < selectedMiddleY d x ∧
      selectedMiddleY d x < Real.cos d.angleLower ∧
      outerLobeMaximizer d < selectedMiddleZ d x ∧
      selectedMiddleZ d x < Real.cosh (pathLogParameter d.a) at hc
  have htheta := selectedMiddleAngle_mem_openGap_of_classified d hclass
  have hcos := selectedMiddleAngle_cos_of_classified d hclass
  have hyPos := selectedMiddleY_pos_of_classified d hclass
  have hzPos := selectedMiddleZ_pos_of_classified d hclass
  have hzAbs :
      |selectedMiddleZ d x| ≤ Real.cosh (pathLogParameter d.a) := by
    rw [abs_of_pos hzPos]
    exact hc.2.2.2.2.le
  have hinnerOuter :
      Real.cos (selectedMiddleAngle d x) < selectedMiddleZ d x :=
    outerEndpointSide_gt_innerCos d.hK d.hj htheta.1
      (htheta.2.le.trans d.angleUpper_le_half)
      (outerLobeMaximizer_spec d).1 hc.2.2.2.1
  have horder :
      Real.cos (selectedMiddleAngle d x) ^ 2 <
        selectedMiddleZ d x ^ 2 := by
    apply (sq_lt_sq₀ ?_ hzPos.le).2 hinnerOuter
    rw [hcos]
    exact hyPos.le
  have hxRec := selectedMiddleX_eq_outerChordX_reconstruction
    d hx.1 hclass
  have hsRec := selectedMiddleRoot_eq_signed_outerChordS_reconstruction
    d hx.1 hclass
  have hsign := negOnePow_sq d.j
  have hdet :=
    signedPencilDet_selectedMiddleRoot_eq_zero_of_mem_gap d hx.1
  rcases Nat.even_or_odd (d.K - 1) with hnEven | hnOdd
  · rcases hnEven with ⟨m, hm⟩
    have hDim : d.K - 1 = 2 * m := by omega
    have hfold :
        foldEvenSequence d.a x (selectedMiddleRoot d x) m = 0 := by
      rw [← signedPencilDet_even_eq_foldEvenSequence d.ha1.ne m]
      simpa only [hDim] using hdet
    have hfoldRec :
        foldEvenSequence d.a
          (outerChordX d.a (selectedMiddleAngle d x)
            (selectedMiddleZ d x))
          ((-1 : ℝ) ^ d.j *
            outerChordS d.a (selectedMiddleAngle d x)
              (selectedMiddleZ d x)) m = 0 := by
      rw [← hxRec, ← hsRec]
      exact hfold
    have hchord :=
      (foldEvenSequence_signed_outerChord_eq_zero_iff m d.ha0
        d.ha1.ne hzAbs horder hsign).1 hfoldRec
    have habs := abs_signedChordEquation hchord
    simpa [chordLobeWeight, outerChordRadical, halfTrigRadical,
      hDim, hcos] using habs
  · rcases hnOdd with ⟨m, hm⟩
    have hDim : d.K - 1 = 2 * m + 1 := by omega
    have hfold :
        foldOddSequence d.a x (selectedMiddleRoot d x) m = 0 := by
      rw [← signedPencilDet_odd_eq_foldOddSequence d.ha1.ne m]
      simpa only [hDim] using hdet
    have hfoldRec :
        foldOddSequence d.a
          (outerChordX d.a (selectedMiddleAngle d x)
            (selectedMiddleZ d x))
          ((-1 : ℝ) ^ d.j *
            outerChordS d.a (selectedMiddleAngle d x)
              (selectedMiddleZ d x)) m = 0 := by
      rw [← hxRec, ← hsRec]
      exact hfold
    have hcosNe : Real.cos (selectedMiddleAngle d x) ≠ 0 := by
      rw [hcos]
      exact hyPos.ne'
    have hchord :=
      (foldOddSequence_signed_outerChord_eq_zero_iff m d.ha0
        d.ha1.ne hzAbs horder hsign hcosNe).1 hfoldRec
    have habs := abs_signedChordEquation hchord
    simpa [chordLobeWeight, outerChordRadical, halfTrigRadical,
      hDim, hcos] using habs

/-- Reverse classification: a classified selected middle root is exactly
one interior member of the canonical endpoint-side chord family. -/
theorem exists_outerChordFamily_representation_of_classified
    (d : PositiveHalfGap) {x : ℝ}
    (hx : x ∈ positiveHalfSpectralGap d ∩
      middleBranchRawClassifiedSet d) :
    ∃ θ : d.Angle,
      d.angleLower < θ ∧ θ < d.angleUpper ∧
      selectedMiddleY d x = Real.cos θ ∧
      selectedMiddleZ d x = outerChordFamilyZ d θ ∧
      x = outerChordFamilyX d θ ∧
      selectedMiddleRoot d x = outerChordFamilySignedRoot d θ := by
  have htheta := selectedMiddleAngle_mem_openGap_of_classified d hx.2
  let θ : d.Angle :=
    ⟨selectedMiddleAngle d x, htheta.1.le, htheta.2.le⟩
  have hcos : Real.cos (θ : ℝ) = selectedMiddleY d x := by
    exact selectedMiddleAngle_cos_of_classified d hx.2
  have hc := hx.2
  change
    0 < selectedMiddleDiscriminant d x ∧
      Real.cos d.angleUpper < selectedMiddleY d x ∧
      selectedMiddleY d x < Real.cos d.angleLower ∧
      outerLobeMaximizer d < selectedMiddleZ d x ∧
      selectedMiddleZ d x < Real.cosh (pathLogParameter d.a) at hc
  have hselectedMem : selectedMiddleZ d x ∈
      Icc (outerLobeMaximizer d)
        (Real.cosh (pathLogParameter d.a)) :=
    ⟨hc.2.2.2.1.le, hc.2.2.2.2.le⟩
  have hlevel :=
    chordLobeWeight_selectedMiddleZ_eq_selectedMiddleY d hx
  have hfamilyLevel :
      chordLobeWeight d.K d.a (outerChordFamilyZ d θ) =
        chordLobeWeight d.K d.a (selectedMiddleY d x) := by
    calc
      chordLobeWeight d.K d.a (outerChordFamilyZ d θ) =
          chordPhi d.K d.a θ :=
        chordLobeWeight_outerChordFamilyZ d θ
      _ = chordLobeWeight d.K d.a (Real.cos θ) :=
        (chordLobeWeight_cos d.K d.a θ).symm
      _ = chordLobeWeight d.K d.a (selectedMiddleY d x) := by
        rw [hcos]
  have hanti := outerChordLobeWeight_strictAntiOn_closedEndpointSide
    d.K d.hK d.a d.ha0 d.ha1 (outerLobeMaximizer_spec d).1
      (outerLobeMaximizer_spec d).2
  have hzEq : selectedMiddleZ d x = outerChordFamilyZ d θ := by
    apply hanti.injOn hselectedMem (outerChordFamilyZ_mem d θ)
    exact hlevel.trans hfamilyLevel.symm
  have hxRec := selectedMiddleX_eq_outerChordX_reconstruction
    d hx.1 hx.2
  have hsRec := selectedMiddleRoot_eq_signed_outerChordS_reconstruction
    d hx.1 hx.2
  have hxFamily : x = outerChordFamilyX d θ := by
    unfold outerChordFamilyX
    change x = outerChordX d.a (selectedMiddleAngle d x)
      (outerChordFamilyZ d θ)
    rw [← hzEq]
    exact hxRec
  have hsFamily :
      selectedMiddleRoot d x = outerChordFamilySignedRoot d θ := by
    unfold outerChordFamilySignedRoot outerChordFamilyS
    change selectedMiddleRoot d x =
      (-1 : ℝ) ^ d.j * outerChordS d.a (selectedMiddleAngle d x)
        (outerChordFamilyZ d θ)
    rw [← hzEq]
    exact hsRec
  exact ⟨θ, htheta.1, htheta.2, hcos.symm, hzEq, hxFamily, hsFamily⟩

end

end ConnectedPseudospectrum
