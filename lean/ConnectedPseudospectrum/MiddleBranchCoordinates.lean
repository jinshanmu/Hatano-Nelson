import ConnectedPseudospectrum.ChordEndpointAgreement
import ConnectedPseudospectrum.FoldedReconstruction
import ConnectedPseudospectrum.OuterChordGeneric

/-!
# Folded coordinates along the selected middle branch

This module attaches the literal folded discriminant and its reconstructed
half variables to the selected signed middle branch.  It isolates the open
coordinate sheet used by the source's continuation argument and proves that
the sheet has a genuine starting point inside every positive-half gap.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- Lower spectral endpoint of the positive-half gap. -/
def positiveHalfGapLower (d : PositiveHalfGap) : ℝ :=
  symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
    ⟨d.j, by
      have hjUpper := d.hjUpper
      omega⟩

/-- Upper spectral endpoint of the positive-half gap. -/
def positiveHalfGapUpper (d : PositiveHalfGap) : ℝ :=
  symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
    ⟨d.j - 1, by
      have hjUpper := d.hjUpper
      omega⟩

/-- The exact open real spectral gap corresponding to `d`. -/
def positiveHalfSpectralGap (d : PositiveHalfGap) : Set ℝ :=
  Ioo (positiveHalfGapLower d) (positiveHalfGapUpper d)

/-- The selected signed middle root over the real axis. -/
def selectedMiddleRoot (d : PositiveHalfGap) (x : ℝ) : ℝ :=
  middleBranchExtension (d.K - 1) d.a d.j x

/-- The actual least-singular-value height underlying the signed root. -/
def selectedMiddleHeight (d : PositiveHalfGap) (x : ℝ) : ℝ :=
  realGapValue (d.K - 1) d.a x

/-- The literal folded discriminant evaluated on the selected middle root. -/
def selectedMiddleDiscriminant (d : PositiveHalfGap) (x : ℝ) : ℝ :=
  foldDiscriminant d.a x (selectedMiddleRoot d x)

/-- The reconstructed nonnegative inner half variable. -/
def selectedMiddleY (d : PositiveHalfGap) (x : ℝ) : ℝ :=
  foldedHalfY d.a x (selectedMiddleRoot d x)

/-- The reconstructed nonnegative outer half variable. -/
def selectedMiddleZ (d : PositiveHalfGap) (x : ℝ) : ℝ :=
  foldedHalfZ d.a x (selectedMiddleRoot d x)

theorem continuous_selectedMiddleRoot (d : PositiveHalfGap) :
    Continuous (selectedMiddleRoot d) := by
  exact continuous_middleBranchExtension (d.K - 1) d.a d.j

theorem continuous_selectedMiddleHeight (d : PositiveHalfGap) :
    Continuous (selectedMiddleHeight d) := by
  exact continuous_realGapValue (d.K - 1) d.a

theorem continuous_selectedMiddleDiscriminant (d : PositiveHalfGap) :
    Continuous (selectedMiddleDiscriminant d) := by
  unfold selectedMiddleDiscriminant foldDiscriminant
  have hroot : Continuous (selectedMiddleRoot d) :=
    continuous_selectedMiddleRoot d
  have hminus : Continuous (fun x : ℝ => 1 + d.a - x) := by
    fun_prop
  have hplus : Continuous (fun x : ℝ => 1 + d.a + x) := by
    fun_prop
  exact ((hminus.pow 2).sub (hroot.pow 2)).mul
    ((hplus.pow 2).sub (hroot.pow 2))

theorem continuous_selectedMiddleY (d : PositiveHalfGap) :
    Continuous (selectedMiddleY d) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hparameter : ContinuousAt
      (fun y : ℝ =>
        ((d.a, (y, selectedMiddleRoot d y)) : FoldedParameterTriple)) x :=
    continuousAt_const.prodMk
      (continuousAt_id.prodMk
        (continuous_selectedMiddleRoot d).continuousAt)
  change ContinuousAt
    (fun y : ℝ => foldedHalfY d.a y (selectedMiddleRoot d y)) x
  exact
    (continuousAt_foldedHalfY_parameter
      (p := (d.a, (x, selectedMiddleRoot d x))) d.ha0.ne').comp'
        (f := fun y : ℝ =>
          ((d.a, (y, selectedMiddleRoot d y)) : FoldedParameterTriple))
        hparameter

theorem continuous_selectedMiddleZ (d : PositiveHalfGap) :
    Continuous (selectedMiddleZ d) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hparameter : ContinuousAt
      (fun y : ℝ =>
        ((d.a, (y, selectedMiddleRoot d y)) : FoldedParameterTriple)) x :=
    continuousAt_const.prodMk
      (continuousAt_id.prodMk
        (continuous_selectedMiddleRoot d).continuousAt)
  change ContinuousAt
    (fun y : ℝ => foldedHalfZ d.a y (selectedMiddleRoot d y)) x
  exact
    (continuousAt_foldedHalfZ_parameter
      (p := (d.a, (x, selectedMiddleRoot d x))) d.ha0.ne').comp'
        (f := fun y : ℝ =>
          ((d.a, (y, selectedMiddleRoot d y)) : FoldedParameterTriple))
        hparameter

/-- The sign convention for the middle branch is exactly `(-1)^j`. -/
theorem middleBranchSign_eq_negOnePow (j : ℕ) :
    middleBranchSign j = (-1 : ℝ) ^ j := by
  rcases Nat.even_or_odd j with hjEven | hjOdd
  · rw [middleBranchSign_of_even hjEven, hjEven.neg_one_pow]
  · rw [middleBranchSign_of_odd hjOdd, hjOdd.neg_one_pow]

theorem selectedMiddleRoot_eq_negOnePow_mul_height
    (d : PositiveHalfGap) (x : ℝ) :
    selectedMiddleRoot d x =
      (-1 : ℝ) ^ d.j * selectedMiddleHeight d x := by
  unfold selectedMiddleRoot selectedMiddleHeight middleBranchExtension
  rw [middleBranchSign_eq_negOnePow]

/-- Every point of a positive-half spectral gap has positive real
abscissa. -/
theorem positiveHalfSpectralGap_pos
    (d : PositiveHalfGap) {x : ℝ}
    (hx : x ∈ positiveHalfSpectralGap d) :
    0 < x := by
  have hcos : 0 ≤ Real.cos d.angleUpper := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · have hupperPos : 0 < d.angleUpper :=
        d.angleLower_pos.trans d.angleLower_lt_angleUpper
      linarith [Real.pi_pos]
    · exact d.angleUpper_le_half
  have hlowerNonneg : 0 ≤ positiveHalfGapLower d := by
    unfold positiveHalfGapLower
    rw [← outerChordFamilyX_rightAngle_eq_symmetricPathEigenvalue d,
      outerChordFamilyX_rightAngle]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg d.a)) hcos
  exact hlowerNonneg.trans_lt hx.1

/-- No displayed path eigenvalue lies in the open gap. -/
theorem ne_pathEigenvalue_of_mem_positiveHalfSpectralGap
    (d : PositiveHalfGap) {x : ℝ}
    (hx : x ∈ positiveHalfSpectralGap d)
    (k : Fin (d.K - 1)) :
    x ≠ pathEigenvalue (d.K - 1) d.a k := by
  have hr : 0 < pathRate d.a := Real.sqrt_pos.2 d.ha0
  rw [pathEigenvalue_eq_symmetricPathEigenvalue]
  by_cases hkj : k.1 < d.j
  · have hkUpper :
        k ≤ (⟨d.j - 1, by
          have hjUpper := d.hjUpper
          omega⟩ : Fin (d.K - 1)) := by
      exact Fin.mk_le_mk.mpr (by omega)
    have hxEigen :
        x < symmetricPathEigenvalue (d.K - 1) (pathRate d.a) k :=
      hx.2.trans_le
        ((symmetricPathEigenvalue_strictAnti (d.K - 1) hr).antitone
          hkUpper)
    exact ne_of_lt hxEigen
  · have hjk :
        (⟨d.j, by
          have hjUpper := d.hjUpper
          omega⟩ : Fin (d.K - 1)) ≤ k := by
      exact Fin.mk_le_mk.mpr (by omega)
    have hEigenX :
        symmetricPathEigenvalue (d.K - 1) (pathRate d.a) k < x :=
      lt_of_le_of_lt
        ((symmetricPathEigenvalue_strictAnti (d.K - 1) hr).antitone hjk)
        hx.1
    exact ne_of_gt hEigenX

/-- The underlying actual Euclidean least singular value is strictly
positive throughout the open gap. -/
theorem selectedMiddleHeight_pos_of_mem_gap
    (d : PositiveHalfGap) {x : ℝ}
    (hx : x ∈ positiveHalfSpectralGap d) :
    0 < selectedMiddleHeight d x := by
  have hn : 0 < d.K - 1 := by
    have hK := d.hK
    omega
  have hnonneg : 0 ≤ selectedMiddleHeight d x := by
    unfold selectedMiddleHeight realGapValue pseudospectralHeight
    exact leastSingularValue_nonneg _
  have hne : selectedMiddleHeight d x ≠ 0 := by
    intro hzero
    obtain ⟨k, hk⟩ :=
      (pseudospectralHeight_eq_zero_iff
        (d.K - 1) d.ha0 hn (x : ℂ)).1 hzero
    have hkReal : x = pathEigenvalue (d.K - 1) d.a k :=
      Complex.ofReal_injective hk
    exact (ne_pathEigenvalue_of_mem_positiveHalfSpectralGap d hx k) hkReal
  exact lt_of_le_of_ne hnonneg hne.symm

/-- The selected signed root has the fixed paper sign on the whole gap. -/
theorem negOnePow_mul_selectedMiddleRoot_pos_of_mem_gap
    (d : PositiveHalfGap) {x : ℝ}
    (hx : x ∈ positiveHalfSpectralGap d) :
    0 < (-1 : ℝ) ^ d.j * selectedMiddleRoot d x := by
  calc
    0 < selectedMiddleHeight d x :=
      selectedMiddleHeight_pos_of_mem_gap d hx
    _ = (-1 : ℝ) ^ d.j * selectedMiddleRoot d x := by
      rw [selectedMiddleRoot_eq_negOnePow_mul_height]
      have hsign := negOnePow_sq d.j
      calc
        selectedMiddleHeight d x =
            1 * selectedMiddleHeight d x := by ring
        _ = ((-1 : ℝ) ^ d.j) ^ 2 * selectedMiddleHeight d x := by
          rw [hsign]
        _ = (-1 : ℝ) ^ d.j *
            ((-1 : ℝ) ^ d.j * selectedMiddleHeight d x) := by
          ring

theorem selectedMiddleRoot_ne_zero_of_mem_gap
    (d : PositiveHalfGap) {x : ℝ}
    (hx : x ∈ positiveHalfSpectralGap d) :
    selectedMiddleRoot d x ≠ 0 := by
  intro hzero
  have hpos := negOnePow_mul_selectedMiddleRoot_pos_of_mem_gap d hx
  rw [hzero, mul_zero] at hpos
  exact (lt_irrefl 0) hpos

/-- The selected root solves the literal signed-pencil determinant at every
point of the exact open gap. -/
theorem signedPencilDet_selectedMiddleRoot_eq_zero_of_mem_gap
    (d : PositiveHalfGap) {x : ℝ}
    (hx : x ∈ positiveHalfSpectralGap d) :
    signedPencilDet (d.K - 1) d.a x (selectedMiddleRoot d x) = 0 := by
  exact signedPencilDet_middleBranchExtension_eq_zero_on_positiveHalfGap
    d hx.1 hx.2

/-- Raw coordinate classification: positive folded discriminant, the inner
half variable between the two nodal cosines, and the outer half variable on
the strict endpoint side of the unique outer maximum. -/
def middleBranchRawClassifiedSet (d : PositiveHalfGap) : Set ℝ :=
  {x |
    0 < selectedMiddleDiscriminant d x ∧
    Real.cos d.angleUpper < selectedMiddleY d x ∧
    selectedMiddleY d x < Real.cos d.angleLower ∧
    outerLobeMaximizer d < selectedMiddleZ d x ∧
    selectedMiddleZ d x < Real.cosh (pathLogParameter d.a)}

/-- The classified portion of the selected middle branch inside the target
spectral gap. -/
def middleBranchClassifiedSet (d : PositiveHalfGap) : Set ℝ :=
  positiveHalfSpectralGap d ∩ middleBranchRawClassifiedSet d

theorem isOpen_middleBranchRawClassifiedSet (d : PositiveHalfGap) :
    IsOpen (middleBranchRawClassifiedSet d) := by
  unfold middleBranchRawClassifiedSet
  exact (isOpen_lt continuous_const
    (continuous_selectedMiddleDiscriminant d)).inter
      ((isOpen_lt continuous_const (continuous_selectedMiddleY d)).inter
        ((isOpen_lt (continuous_selectedMiddleY d) continuous_const).inter
          ((isOpen_lt continuous_const (continuous_selectedMiddleZ d)).inter
            (isOpen_lt (continuous_selectedMiddleZ d) continuous_const))))

theorem isOpen_middleBranchClassifiedSet (d : PositiveHalfGap) :
    IsOpen (middleBranchClassifiedSet d) := by
  unfold middleBranchClassifiedSet positiveHalfSpectralGap
  exact isOpen_Ioo.inter (isOpen_middleBranchRawClassifiedSet d)

/-- At any interior chord point already identified with the selected middle
root, the reconstructed folded variables are exactly the chord's inner and
outer half variables. -/
theorem selectedMiddleCoordinates_eq_outerChordFamily_of_agreement
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper)
    (hagree : outerChordFamilySignedRoot d θ =
      selectedMiddleRoot d (outerChordFamilyX d θ)) :
    selectedMiddleY d (outerChordFamilyX d θ) = Real.cos θ ∧
      selectedMiddleZ d (outerChordFamilyX d θ) =
        outerChordFamilyZ d θ := by
  have horder := outerChordFamily_cos_sq_lt_z_sq d θ hleft hright
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
  have hvars := foldedHalfVariables_eq_of_generic
    (cos_pos_on_positiveHalfGap d θ hright).le
    (outerChordFamilyZ_nonneg d θ) hminus hplus
  exact hvars

/-- The same identified chord point lies on the strict positive-
discriminant sheet. -/
theorem selectedMiddleDiscriminant_pos_of_outerChordFamily_agreement
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper)
    (hagree : outerChordFamilySignedRoot d θ =
      selectedMiddleRoot d (outerChordFamilyX d θ)) :
    0 < selectedMiddleDiscriminant d (outerChordFamilyX d θ) := by
  have horder := outerChordFamily_cos_sq_lt_z_sq d θ hleft hright
  have hz := outerChordFamilyZ_abs_le_cosh d θ
  have hsign := negOnePow_sq d.j
  unfold selectedMiddleDiscriminant
  rw [← hagree]
  unfold outerChordFamilyX outerChordFamilySignedRoot outerChordFamilyS
  rw [foldDiscriminant_signed_outerChord_eq d.a θ
      (outerChordFamilyZ d θ) ((-1 : ℝ) ^ d.j) hsign,
    foldDiscriminant_outerChord d.ha0 hz]
  exact mul_pos
    (mul_pos (by norm_num) (sq_pos_of_pos d.ha0))
    (sq_pos_of_pos (sub_pos.mpr horder))

/-- The coordinate sheet starts nontrivially inside every positive-half
spectral gap.  This is the base point for the source's global continuation
and exhaustion argument. -/
theorem middleBranchClassifiedSet_nonempty (d : PositiveHalfGap) :
    (middleBranchClassifiedSet d).Nonempty := by
  obtain ⟨θ, hleft, hright, hxLower, hxUpper, hagree⟩ :=
    exists_outerChordFamily_left_endpoint_agreement d
  let x := outerChordFamilyX d θ
  have hcoords :=
    selectedMiddleCoordinates_eq_outerChordFamily_of_agreement
      d θ hleft hright hagree
  have hdisc :=
    selectedMiddleDiscriminant_pos_of_outerChordFamily_agreement
      d θ hleft hright hagree
  have hthetaPi : (θ : ℝ) ≤ Real.pi := by
    have hhalfPi : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
    exact (θ.2.2.trans d.angleUpper_le_half).trans hhalfPi.le
  have hupperPi : d.angleUpper ≤ Real.pi :=
    d.angleUpper_le_half.trans (by linarith [Real.pi_pos])
  have hcosLower : Real.cos θ < Real.cos d.angleLower :=
    Real.cos_lt_cos_of_nonneg_of_le_pi
      d.angleLower_pos.le hthetaPi hleft
  have hcosUpper : Real.cos d.angleUpper < Real.cos θ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi
      (le_trans d.angleLower_pos.le θ.2.1) hupperPi hright
  refine ⟨x, ?_⟩
  constructor
  · exact ⟨hxLower, hxUpper⟩
  · refine ⟨hdisc, ?_, ?_, ?_, ?_⟩
    · rw [hcoords.1]
      exact hcosUpper
    · rw [hcoords.1]
      exact hcosLower
    · rw [hcoords.2]
      exact outerLobeMaximizer_lt_outerChordFamilyZ
        d θ hleft hright
    · rw [hcoords.2]
      exact outerChordFamilyZ_lt_cosh d θ hleft hright

end

end ConnectedPseudospectrum
