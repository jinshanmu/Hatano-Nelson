import ConnectedPseudospectrum.HermitianLeastSingular
import ConnectedPseudospectrum.VerticalRatio
import ConnectedPseudospectrum.VerticalScalingBridge
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact

/-!
# Continuation of positive definiteness along vertical fibres

This module completes the analytic continuation step in `lem:vertical`.
The determinant derivative proved in `VerticalRatio` is used only while the
Gram shift is positive definite.  A first-contact argument shows that a
strict decrease of the least singular value would force that determinant to
increase from a positive value to zero, which is impossible.
-/

namespace ConnectedPseudospectrum

open Matrix PowerSeries Set
open scoped ComplexOrder

noncomputable section

/-- The least singular value along the paper's squared-height parameter
`Y = y²`. -/
def verticalLeastSingular (n : ℕ) (a x Y : ℝ) : ℝ :=
  leastSingularValue (verticalShiftedMatrix n a x Y)

/-- The vertically shifted path matrix varies continuously with `Y`.
This is global because `Real.sqrt` is defined continuously on all of `ℝ`. -/
theorem continuous_verticalShiftedMatrix (n : ℕ) (a x : ℝ) :
    Continuous (fun Y : ℝ => verticalShiftedMatrix n a x Y) := by
  simp only [verticalShiftedMatrix]
  exact (continuous_shiftedPathMatrix n a).comp
    (continuous_const.add
      (continuous_const.mul
        (Complex.continuous_ofReal.comp Real.continuous_sqrt)))

/-- Continuity of the actual Euclidean least singular value along the
squared-height parameter. -/
theorem continuous_verticalLeastSingular (n : ℕ) (a x : ℝ) :
    Continuous (verticalLeastSingular n a x) :=
  (continuous_leastSingularValue n).comp
    (continuous_verticalShiftedMatrix n a x)

/-- The Hermitian pencil and its determinant vary continuously in `Y`. -/
theorem continuous_verticalPencil (n : ℕ) (a x t : ℝ) :
    Continuous (fun Y : ℝ => verticalPencil n a x Y t) := by
  simp only [verticalPencil]
  have hM := continuous_verticalShiftedMatrix n a x
  exact (hM.matrix_conjTranspose.matrix_mul hM).sub continuous_const

theorem continuous_verticalPencilDet (n : ℕ) (a x t : ℝ) :
    Continuous (fun Y : ℝ => verticalPencilDet n a x Y t) := by
  simpa only [verticalPencilDet] using
    (continuous_verticalPencil n a x t).matrix_det

/-- At the attained least singular value the Gram shift is singular.  This
is the determinant-zero endpoint used in the first-contact argument. -/
theorem gramShift_det_eq_zero_at_leastSingularValue {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) :
    (gramShift M (leastSingularValue M)).det = 0 := by
  have hsemidef := gramShift_leastSingularValue_posSemidef M hn
  have hnotPosDef : ¬(gramShift M (leastSingularValue M)).PosDef := by
    rw [gramShift_posDef_iff_lt_leastSingularValue M hn
      (leastSingularValue M) (leastSingularValue_nonneg M)]
    exact lt_irrefl _
  have hnotUnit : ¬IsUnit (gramShift M (leastSingularValue M)) := by
    intro hunit
    exact hnotPosDef (hsemidef.posDef_iff_isUnit.mpr hunit)
  by_contra hdet
  apply hnotUnit
  exact (Matrix.isUnit_iff_isUnit_det
    (gramShift M (leastSingularValue M))).mpr
      (isUnit_iff_ne_zero.mpr hdet)

/-- Real-part form of the determinant derivative theorem.  The derivative
coefficient is real and strictly positive whenever the pencil is positive
definite. -/
theorem hasDerivWithinAt_verticalPencilDet_re_pos (n : ℕ) (hn : 0 < n)
    (a x Y t : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hY : 0 ≤ Y)
    (hpos : (verticalPencil n a x Y t).PosDef) :
    HasDerivWithinAt
        (fun Y' : ℝ => (verticalPencilDet n a x Y' t).re)
        (coeff n (verticalPencilYDerivativeSeries a x Y t)).re
        (Ici 0) Y ∧
      0 < (coeff n (verticalPencilYDerivativeSeries a x Y t)).re := by
  obtain ⟨hderiv, hcoeff⟩ := hasDerivWithinAt_verticalPencilDet_pos
    n hn a x Y t ha₀ ha₁ hY hpos
  constructor
  · convert (Complex.reCLM.hasFDerivAt.comp_hasFDerivWithinAt Y
      hderiv.hasFDerivWithinAt).hasDerivWithinAt using 1
    all_goals simp
  · exact (Complex.pos_iff.mp hcoeff).1

/-- Continuation in the squared-height parameter.  This is the formal
first-contact version of the maximal-interval argument in `lem:vertical`:
a hypothetical drop provides an intermediate threshold `t`; at its first
contact the Gram shift is singular, whereas its determinant has been
strictly increasing on the preceding positive-definite interval. -/
theorem verticalLeastSingular_mono_Y (n : ℕ) (hn : 2 ≤ n)
    (a x : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    {Y₀ Y₁ : ℝ} (hY₀ : 0 ≤ Y₀) (hY₀₁ : Y₀ ≤ Y₁) :
    verticalLeastSingular n a x Y₀ ≤
      verticalLeastSingular n a x Y₁ := by
  let s : ℝ → ℝ := verticalLeastSingular n a x
  have hscont : Continuous s := continuous_verticalLeastSingular n a x
  have hnpos : 0 < n := by omega
  by_contra hmono
  have hdrop : s Y₁ < s Y₀ := lt_of_not_ge hmono
  let t : ℝ := (s Y₀ + s Y₁) / 2
  have hs₀nonneg : 0 ≤ s Y₀ :=
    leastSingularValue_nonneg (verticalShiftedMatrix n a x Y₀)
  have hs₁nonneg : 0 ≤ s Y₁ :=
    leastSingularValue_nonneg (verticalShiftedMatrix n a x Y₁)
  have htnonneg : 0 ≤ t := by
    dsimp [t]
    linarith
  have htlt₀ : t < s Y₀ := by
    dsimp [t]
    linarith
  have h₁ltt : s Y₁ < t := by
    dsimp [t]
    linarith
  let contact : Set ℝ := Icc Y₀ Y₁ ∩ {Y | s Y = t}
  have hcontactCompact : IsCompact contact := by
    dsimp [contact]
    exact isCompact_Icc.inter_right
      (isClosed_eq hscont continuous_const)
  have hcontactNonempty : contact.Nonempty := by
    have htmem : t ∈ Icc (s Y₁) (s Y₀) := ⟨h₁ltt.le, htlt₀.le⟩
    obtain ⟨c, hcIcc, hceq⟩ :=
      (intermediate_value_Icc' hY₀₁ hscont.continuousOn) htmem
    exact ⟨c, hcIcc, hceq⟩
  obtain ⟨c, hcContact, hcLeast⟩ :=
    hcontactCompact.exists_isLeast hcontactNonempty
  have hcIcc : c ∈ Icc Y₀ Y₁ := hcContact.1
  have hsc : s c = t := hcContact.2
  have hY₀c : Y₀ < c := by
    refine lt_of_le_of_ne hcIcc.1 ?_
    intro hY₀eqc
    have : s Y₀ = t := by simpa [hY₀eqc] using hsc
    exact (ne_of_gt htlt₀) this
  have hs_above : ∀ Y ∈ Ioo Y₀ c, t < s Y := by
    intro Y hY
    by_contra hnot
    have hsYle : s Y ≤ t := le_of_not_gt hnot
    have htmem : t ∈ Icc (s Y) (s Y₀) := ⟨hsYle, htlt₀.le⟩
    obtain ⟨d, hdIcc, hdeq⟩ :=
      (intermediate_value_Icc' hY.1.le hscont.continuousOn) htmem
    have hdContact : d ∈ contact := by
      refine ⟨⟨hdIcc.1, ?_⟩, hdeq⟩
      exact hdIcc.2.trans (hY.2.le.trans hcIcc.2)
    have hcd : c ≤ d := hcLeast hdContact
    exact (not_lt_of_ge hcd) (hdIcc.2.trans_lt hY.2)
  let f : ℝ → ℝ := fun Y => (verticalPencilDet n a x Y t).re
  have hfcont : Continuous f :=
    Complex.continuous_re.comp (continuous_verticalPencilDet n a x t)
  have hstrict : StrictMonoOn f (Icc Y₀ c) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc Y₀ c)
      hfcont.continuousOn
    · intro Y hY
      have hYoo : Y ∈ Ioo Y₀ c := by simpa only [interior_Icc] using hY
      have hYnonneg : 0 ≤ Y := hY₀.trans hYoo.1.le
      have hpos : (verticalPencil n a x Y t).PosDef := by
        change (gramShift (verticalShiftedMatrix n a x Y) t).PosDef
        rw [gramShift_posDef_iff_lt_leastSingularValue
          (verticalShiftedMatrix n a x Y) hnpos t htnonneg]
        exact hs_above Y hYoo
      exact (hasDerivWithinAt_verticalPencilDet_re_pos
        n hnpos a x Y t ha₀ ha₁ hYnonneg hpos).1.mono fun Z hZ => by
          have hZoo : Z ∈ Ioo Y₀ c := by
            simpa only [interior_Icc] using hZ
          exact hY₀.trans hZoo.1.le
    · intro Y hY
      have hYoo : Y ∈ Ioo Y₀ c := by simpa only [interior_Icc] using hY
      have hYnonneg : 0 ≤ Y := hY₀.trans hYoo.1.le
      have hpos : (verticalPencil n a x Y t).PosDef := by
        change (gramShift (verticalShiftedMatrix n a x Y) t).PosDef
        rw [gramShift_posDef_iff_lt_leastSingularValue
          (verticalShiftedMatrix n a x Y) hnpos t htnonneg]
        exact hs_above Y hYoo
      exact (hasDerivWithinAt_verticalPencilDet_re_pos
        n hnpos a x Y t ha₀ ha₁ hYnonneg hpos).2
  have hpos₀ : (verticalPencil n a x Y₀ t).PosDef := by
    change (gramShift (verticalShiftedMatrix n a x Y₀) t).PosDef
    rw [gramShift_posDef_iff_lt_leastSingularValue
      (verticalShiftedMatrix n a x Y₀) hnpos t htnonneg]
    exact htlt₀
  have hdet₀ : 0 < f Y₀ := by
    exact (Complex.pos_iff.mp hpos₀.det_pos).1
  have hdetc : verticalPencilDet n a x c t = 0 := by
    change (gramShift (verticalShiftedMatrix n a x c) t).det = 0
    rw [← hsc]
    exact gramShift_det_eq_zero_at_leastSingularValue
      (verticalShiftedMatrix n a x c) hnpos
  have hdetlt := hstrict (left_mem_Icc.mpr hY₀c.le)
    (right_mem_Icc.mpr hY₀c.le) hY₀c
  have : f c = 0 := by simp [f, hdetc]
  rw [this] at hdetlt
  exact (not_lt_of_ge hdet₀.le) hdetlt

/-- `lem:vertical` in the form consumed by `VerticalScalingBridge`: on each
upper-half-plane vertical fibre, the actual Euclidean least singular value
is nondecreasing in the imaginary coordinate. -/
theorem verticalHeightMonotone (n : ℕ) (hn : 2 ≤ n)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    UpperVerticalHeightMonotone n a := by
  intro x y₀ y₁ hy₀ hy₀₁
  have hy₁ : 0 ≤ y₁ := hy₀.trans hy₀₁
  have hsq : y₀ ^ 2 ≤ y₁ ^ 2 := by nlinarith
  have hmono := verticalLeastSingular_mono_Y n hn a x ha₀ ha₁
    (sq_nonneg y₀) hsq
  simpa [verticalLeastSingular, verticalShiftedMatrix,
    pseudospectralHeight, verticalPoint, Real.sqrt_sq hy₀,
    Real.sqrt_sq hy₁, mul_comm] using hmono

end

end ConnectedPseudospectrum
