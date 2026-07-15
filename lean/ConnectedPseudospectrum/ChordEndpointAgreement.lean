import ConnectedPseudospectrum.ChordFamilySignedPencil
import ConnectedPseudospectrum.SignedPencilImplicit

/-!
# Agreement of the chord and middle branches at a spectral endpoint

This module starts the global continuation argument at the left angular
endpoint of every positive-half gap.  The chord abscissa enters the correct
open spectral gap, and local uniqueness at the simple endpoint identifies
the chord's signed determinant root with the selected middle branch.
-/

namespace ConnectedPseudospectrum

open Filter Set

open scoped Topology

noncomputable section

/-- The selected middle branch is an actual signed-pencil root throughout
the open spectral gap associated with a `PositiveHalfGap`.  This packages
the five parity cases of `lem:middle-branch` behind the source's uniform
`K-1` notation. -/
theorem signedPencilDet_middleBranchExtension_eq_zero_on_positiveHalfGap
    (d : PositiveHalfGap) {x : ℝ}
    (hxLower :
      symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
          ⟨d.j, by
            have hjUpper := d.hjUpper
            omega⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
          ⟨d.j - 1, by
            have hjUpper := d.hjUpper
            omega⟩) :
    signedPencilDet (d.K - 1) d.a x
        (middleBranchExtension (d.K - 1) d.a d.j x) = 0 := by
  have hr : 0 < pathRate d.a := Real.sqrt_pos.2 d.ha0
  have hrsq : pathRate d.a ^ 2 = d.a := Real.sq_sqrt d.ha0.le
  have hnLower : 2 ≤ d.K - 1 := by
    have hj := d.hj
    have hjUpper := d.hjUpper
    omega
  rcases Nat.even_or_odd (d.K - 1) with hnEven | hnOdd
  · rcases hnEven with ⟨m, hm⟩
    have hK : d.K = 2 * m + 1 := by omega
    have hDim : d.K - 1 = 2 * m := by omega
    have hmPos : 0 < m := by omega
    have hjn : d.j < 2 * m := by
      have hjUpper := d.hjUpper
      omega
    have hxLower' :
        symmetricPathEigenvalue (2 * m) (pathRate d.a)
            ⟨d.j, hjn⟩ < x := by
      simpa only [symmetricPathEigenvalue, pathEigenangle, Fin.val_mk,
        hDim] using hxLower
    have hxUpper' :
        x < symmetricPathEigenvalue (2 * m) (pathRate d.a)
            ⟨d.j - 1, by omega⟩ := by
      simpa only [symmetricPathEigenvalue, pathEigenangle, Fin.val_mk,
        hDim] using hxUpper
    rcases Nat.even_or_odd d.j with hjEven | hjOdd
    · have hbridge := evenMiddleBranch_bridge_even_gap
        m d.j hmPos d.hj hjn hjEven hr hxLower' hxUpper'
      have hdet :
          signedPencilDet (2 * m) (pathRate d.a ^ 2) x
              (middleBranchExtension (2 * m) (pathRate d.a ^ 2) d.j x) = 0 := by
        rw [hbridge.2.2.1]
        exact hbridge.2.2.2
      simpa only [hDim, hrsq] using hdet
    · by_cases hmOne : m = 1
      · subst m
        have hbridge := twoMiddleBranch_bridge_odd_gap
          d.j d.hj (by omega) hjOdd hr hxLower' hxUpper'
        have hdet :
            signedPencilDet 2 (pathRate d.a ^ 2) x
                (middleBranchExtension 2 (pathRate d.a ^ 2) d.j x) = 0 := by
          rw [hbridge.2.2.1]
          exact hbridge.2.2.2
        simpa only [hDim, hrsq] using hdet
      · have hmTwo : 2 ≤ m := by omega
        have hbridge := evenMiddleBranch_bridge_odd_gap
          m d.j hmTwo d.hj hjn hjOdd hr hxLower' hxUpper'
        have hdet :
            signedPencilDet (2 * m) (pathRate d.a ^ 2) x
                (middleBranchExtension (2 * m) (pathRate d.a ^ 2) d.j x) = 0 := by
          rw [hbridge.2.2.1]
          exact hbridge.2.2.2
        simpa only [hDim, hrsq] using hdet
  · rcases hnOdd with ⟨m, hm⟩
    have hK : d.K = 2 * m + 2 := by omega
    have hDim : d.K - 1 = 2 * m + 1 := by omega
    have hmPos : 0 < m := by omega
    have hjn : d.j < 2 * m + 1 := by
      have hjUpper := d.hjUpper
      omega
    have hxLower' :
        symmetricPathEigenvalue (2 * m + 1) (pathRate d.a)
            ⟨d.j, hjn⟩ < x := by
      simpa only [symmetricPathEigenvalue, pathEigenangle, Fin.val_mk,
        hDim] using hxLower
    have hxUpper' :
        x < symmetricPathEigenvalue (2 * m + 1) (pathRate d.a)
            ⟨d.j - 1, by omega⟩ := by
      simpa only [symmetricPathEigenvalue, pathEigenangle, Fin.val_mk,
        hDim] using hxUpper
    rcases Nat.even_or_odd d.j with hjEven | hjOdd
    · have hbridge := oddMiddleBranch_bridge_even_gap
        m d.j hmPos d.hj hjn hjEven hr hxLower' hxUpper'
      have hdet :
          signedPencilDet (2 * m + 1) (pathRate d.a ^ 2) x
              (middleBranchExtension (2 * m + 1) (pathRate d.a ^ 2) d.j x) = 0 := by
        rw [hbridge.2.2.1]
        exact hbridge.2.2.2
      simpa only [hDim, hrsq] using hdet
    · have hbridge := oddMiddleBranch_bridge_odd_gap
        m d.j hmPos d.hj hjn hjOdd hr hxLower' hxUpper'
      have hdet :
          signedPencilDet (2 * m + 1) (pathRate d.a ^ 2) x
              (middleBranchExtension (2 * m + 1) (pathRate d.a ^ 2) d.j x) = 0 := by
        rw [hbridge.2.2.1]
        exact hbridge.2.2.2
      simpa only [hDim, hrsq] using hdet

/-- Independently of the parity of `K`, every interior member of the chord
family is a root of the literal signed-pencil determinant. -/
theorem signedPencilDet_outerChordFamily_eq_zero
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper) :
    signedPencilDet (d.K - 1) d.a (outerChordFamilyX d θ)
        (outerChordFamilySignedRoot d θ) = 0 := by
  have hKLower := d.hK
  rcases Nat.even_or_odd (d.K - 1) with hnEven | hnOdd
  · rcases hnEven with ⟨m, hm⟩
    have hK : d.K = 2 * m + 1 := by omega
    exact signedPencilDet_outerChordFamily_even_eq_zero
      d m hK θ hleft hright
  · rcases hnOdd with ⟨m, hm⟩
    have hK : d.K = 2 * m + 2 := by omega
    exact signedPencilDet_outerChordFamily_odd_eq_zero
      d m hK θ hleft hright

/-- As soon as the inner angle leaves the left endpoint, the chord abscissa
lies strictly below that endpoint's path eigenvalue.  The proof uses only
`z ≤ cosh h` and strict decrease of cosine, so it does not assume that the
full chord abscissa is monotone. -/
theorem outerChordFamilyX_lt_leftSpectralEndpoint
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) :
    outerChordFamilyX d θ <
      symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
        ⟨d.j - 1, by
          have hjUpper := d.hjUpper
          omega⟩ := by
  have hcosNonneg : 0 ≤ Real.cos θ := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · linarith [Real.pi_pos, d.angleLower_pos, θ.2.1]
    · exact θ.2.2.trans d.angleUpper_le_half
  have hthetaPi : (θ : ℝ) ≤ Real.pi := by
    have hhalfPi : Real.pi / 2 < Real.pi := by linarith [Real.pi_pos]
    exact (θ.2.2.trans d.angleUpper_le_half).trans hhalfPi.le
  have hcosStrict : Real.cos θ < Real.cos d.angleLower :=
    Real.cos_lt_cos_of_nonneg_of_le_pi
      d.angleLower_pos.le hthetaPi hleft
  have hscaleCos :
      0 ≤ halfChordScale d.a * Real.cos θ :=
    mul_nonneg (halfChordScale_pos d.ha0).le hcosNonneg
  calc
    outerChordFamilyX d θ =
        halfChordScale d.a * Real.cos θ * outerChordFamilyZ d θ := rfl
    _ ≤ halfChordScale d.a * Real.cos θ *
          Real.cosh (pathLogParameter d.a) :=
      mul_le_mul_of_nonneg_left (outerChordFamilyZ_mem d θ).2 hscaleCos
    _ = 2 * pathRate d.a * Real.cos θ := by
      calc
        halfChordScale d.a * Real.cos θ *
              Real.cosh (pathLogParameter d.a) =
            (halfChordScale d.a * Real.cosh (pathLogParameter d.a)) *
              Real.cos θ := by ring
        _ = 2 * pathRate d.a * Real.cos θ := by
          rw [halfChordScale_mul_cosh_pathLogParameter]
    _ < 2 * pathRate d.a * Real.cos d.angleLower :=
      mul_lt_mul_of_pos_left hcosStrict
        (mul_pos (by norm_num) (Real.sqrt_pos.2 d.ha0))
    _ = outerChordFamilyX d d.leftAngle :=
      (outerChordFamilyX_leftAngle d).symm
    _ = symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
          ⟨d.j - 1, by
            have hjUpper := d.hjUpper
            omega⟩ :=
      outerChordFamilyX_leftAngle_eq_symmetricPathEigenvalue d

/-- In a sufficiently small right neighborhood of the left angular
endpoint, the chord abscissa lies in the corresponding open path-spectral
gap. -/
theorem eventually_outerChordFamilyX_mem_spectralGap_left
    (d : PositiveHalfGap) :
    ∀ᶠ θ in 𝓝[Ioi d.leftAngle] d.leftAngle,
      d.leftAngle < θ ∧ θ < d.rightAngle ∧
        symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
            ⟨d.j, by
              have hjUpper := d.hjUpper
              omega⟩ < outerChordFamilyX d θ ∧
        outerChordFamilyX d θ <
          symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
            ⟨d.j - 1, by
              have hjUpper := d.hjUpper
              omega⟩ := by
  have hr : 0 < pathRate d.a := Real.sqrt_pos.2 d.ha0
  have hj := d.hj
  have hjUpper := d.hjUpper
  have hindex :
      (⟨d.j - 1, by omega⟩ : Fin (d.K - 1)) <
        ⟨d.j, by omega⟩ := by
    simp only [Fin.mk_lt_mk]
    omega
  have hendpointGap :
      symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
          ⟨d.j, by
            have hjUpper := d.hjUpper
            omega⟩ < outerChordFamilyX d d.leftAngle := by
    rw [outerChordFamilyX_leftAngle_eq_symmetricPathEigenvalue]
    exact symmetricPathEigenvalue_strictAnti (d.K - 1) hr hindex
  have hlower :=
    (continuous_outerChordFamilyX d).continuousAt.eventually_const_lt
      hendpointGap
  have hrightEndpoint : d.leftAngle < d.rightAngle := by
    exact d.angleLower_lt_angleUpper
  have hright : ∀ᶠ θ in 𝓝 d.leftAngle, θ < d.rightAngle :=
    eventually_lt_nhds hrightEndpoint
  filter_upwards [self_mem_nhdsWithin,
    hlower.filter_mono nhdsWithin_le_nhds,
    hright.filter_mono nhdsWithin_le_nhds] with θ hleft hLower hRight
  exact ⟨hleft, hRight, hLower,
    outerChordFamilyX_lt_leftSpectralEndpoint d θ hleft⟩

/-- Local uniqueness at the simple left spectral endpoint identifies the
continuous chord root with the selected middle branch throughout a
sufficiently small interior angular germ. -/
theorem eventually_outerChordFamilySignedRoot_eq_middleBranchExtension_left
    (d : PositiveHalfGap) :
    ∀ᶠ θ in 𝓝[Ioi d.leftAngle] d.leftAngle,
      outerChordFamilySignedRoot d θ =
        middleBranchExtension (d.K - 1) d.a d.j
          (outerChordFamilyX d θ) := by
  have hn : 0 < d.K - 1 := by
    have hK := d.hK
    omega
  have hr : 0 < pathRate d.a := Real.sqrt_pos.2 d.ha0
  have hrsq : pathRate d.a ^ 2 = d.a := Real.sq_sqrt d.ha0.le
  let k : Fin (d.K - 1) := ⟨d.j - 1, by
    have hjUpper := d.hjUpper
    omega⟩
  let x₀ : ℝ := symmetricPathEigenvalue (d.K - 1) (pathRate d.a) k
  have hChordPair :
      Tendsto
        (fun θ : d.Angle =>
          (outerChordFamilyX d θ, outerChordFamilySignedRoot d θ))
        (𝓝 d.leftAngle) (𝓝 (x₀, 0)) := by
    have hcontinuous : ContinuousAt
        (fun θ : d.Angle =>
          (outerChordFamilyX d θ, outerChordFamilySignedRoot d θ))
        d.leftAngle :=
      ((continuous_outerChordFamilyX d).prodMk
        (continuous_outerChordFamilySignedRoot d)).continuousAt
    have hEndpointPair :
        (outerChordFamilyX d d.leftAngle,
            outerChordFamilySignedRoot d d.leftAngle) = (x₀, 0) := by
      apply Prod.ext
      · simpa only [x₀, k] using
          outerChordFamilyX_leftAngle_eq_symmetricPathEigenvalue d
      · exact outerChordFamilySignedRoot_leftAngle d
    change Tendsto
      (fun θ : d.Angle =>
        (outerChordFamilyX d θ, outerChordFamilySignedRoot d θ))
      (𝓝 d.leftAngle)
      (𝓝 (outerChordFamilyX d d.leftAngle,
        outerChordFamilySignedRoot d d.leftAngle)) at hcontinuous
    rw [hEndpointPair] at hcontinuous
    exact hcontinuous
  have hMiddleEndpoint :
      middleBranchExtension (d.K - 1) d.a d.j x₀ = 0 := by
    rw [← hrsq]
    exact middleBranchExtension_symmetricPathEigenvalue_sq_eq_zero
      (d.K - 1) hn d.j hr k
  have hMiddlePair :
      Tendsto
        (fun θ : d.Angle =>
          (outerChordFamilyX d θ,
            middleBranchExtension (d.K - 1) d.a d.j
              (outerChordFamilyX d θ)))
        (𝓝 d.leftAngle) (𝓝 (x₀, 0)) := by
    have hcontinuous : Continuous fun θ : d.Angle =>
        (outerChordFamilyX d θ,
          middleBranchExtension (d.K - 1) d.a d.j
            (outerChordFamilyX d θ)) :=
      (continuous_outerChordFamilyX d).prodMk
        ((continuous_middleBranchExtension (d.K - 1) d.a d.j).comp
          (continuous_outerChordFamilyX d))
    have hat : ContinuousAt
        (fun θ : d.Angle =>
          (outerChordFamilyX d θ,
            middleBranchExtension (d.K - 1) d.a d.j
              (outerChordFamilyX d θ))) d.leftAngle :=
      hcontinuous.continuousAt
    have hxEndpoint : outerChordFamilyX d d.leftAngle = x₀ := by
      simpa only [x₀, k] using
        outerChordFamilyX_leftAngle_eq_symmetricPathEigenvalue d
    have hEndpointPair :
        (outerChordFamilyX d d.leftAngle,
            middleBranchExtension (d.K - 1) d.a d.j
              (outerChordFamilyX d d.leftAngle)) = (x₀, 0) := by
      apply Prod.ext
      · exact hxEndpoint
      · simpa only [hxEndpoint] using hMiddleEndpoint
    change Tendsto
      (fun θ : d.Angle =>
        (outerChordFamilyX d θ,
          middleBranchExtension (d.K - 1) d.a d.j
            (outerChordFamilyX d θ)))
      (𝓝 d.leftAngle)
      (𝓝 (outerChordFamilyX d d.leftAngle,
        middleBranchExtension (d.K - 1) d.a d.j
          (outerChordFamilyX d d.leftAngle))) at hat
    rw [hEndpointPair] at hat
    exact hat
  have hunique :=
    eventually_signedPencilLocalRoot_eq_of_det_zero
      (d.K - 1) hn (r := pathRate d.a) hr k
  have hChordUnique := hChordPair.eventually hunique
  have hMiddleUnique := hMiddlePair.eventually hunique
  filter_upwards [eventually_outerChordFamilyX_mem_spectralGap_left d,
    hChordUnique.filter_mono nhdsWithin_le_nhds,
    hMiddleUnique.filter_mono nhdsWithin_le_nhds] with
      θ hgap hChord hMiddle
  have hdetChord :
      signedPencilDet (d.K - 1) (pathRate d.a ^ 2)
          (outerChordFamilyX d θ) (outerChordFamilySignedRoot d θ) = 0 := by
    rw [hrsq]
    exact signedPencilDet_outerChordFamily_eq_zero d θ hgap.1 hgap.2.1
  have hdetMiddle :
      signedPencilDet (d.K - 1) (pathRate d.a ^ 2)
          (outerChordFamilyX d θ)
          (middleBranchExtension (d.K - 1) d.a d.j
            (outerChordFamilyX d θ)) = 0 := by
    rw [hrsq]
    exact
      signedPencilDet_middleBranchExtension_eq_zero_on_positiveHalfGap
        d hgap.2.2.1 hgap.2.2.2
  exact (hChord hdetChord).symm.trans (hMiddle hdetMiddle)

/-- The complete left-endpoint germ: angles are interior, their abscissae
are in the exact open spectral gap, and the chord and middle signed roots
agree. -/
theorem outerChordFamily_left_endpoint_germ
    (d : PositiveHalfGap) :
    ∀ᶠ θ in 𝓝[Ioi d.leftAngle] d.leftAngle,
      d.leftAngle < θ ∧ θ < d.rightAngle ∧
        symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
            ⟨d.j, by
              have hjUpper := d.hjUpper
              omega⟩ < outerChordFamilyX d θ ∧
        outerChordFamilyX d θ <
          symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
            ⟨d.j - 1, by
              have hjUpper := d.hjUpper
              omega⟩ ∧
        outerChordFamilySignedRoot d θ =
          middleBranchExtension (d.K - 1) d.a d.j
            (outerChordFamilyX d θ) := by
  filter_upwards [eventually_outerChordFamilyX_mem_spectralGap_left d,
    eventually_outerChordFamilySignedRoot_eq_middleBranchExtension_left d]
    with θ hgap hagree
  exact ⟨hgap.1, hgap.2.1, hgap.2.2.1, hgap.2.2.2, hagree⟩

/-- In particular, the endpoint germ is inhabited by an actual interior
angle; the neighborhood statement above gives the stronger
"sufficiently close" form. -/
theorem exists_outerChordFamily_left_endpoint_agreement
    (d : PositiveHalfGap) :
    ∃ θ : d.Angle,
      d.leftAngle < θ ∧ θ < d.rightAngle ∧
        symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
            ⟨d.j, by
              have hjUpper := d.hjUpper
              omega⟩ < outerChordFamilyX d θ ∧
        outerChordFamilyX d θ <
          symmetricPathEigenvalue (d.K - 1) (pathRate d.a)
            ⟨d.j - 1, by
              have hjUpper := d.hjUpper
              omega⟩ ∧
        outerChordFamilySignedRoot d θ =
          middleBranchExtension (d.K - 1) d.a d.j
            (outerChordFamilyX d θ) := by
  letI : NeBot (𝓝[Ioi d.leftAngle] d.leftAngle) :=
    nhdsGT_neBot_of_exists_gt ⟨d.rightAngle, d.angleLower_lt_angleUpper⟩
  exact (outerChordFamily_left_endpoint_germ d).exists

end

end ConnectedPseudospectrum
