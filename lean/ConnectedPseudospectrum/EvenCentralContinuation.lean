import ConnectedPseudospectrum.EvenCentralChordAlgebra
import ConnectedPseudospectrum.MiddleBranchContinuation
import ConnectedPseudospectrum.ChordFamilySignedPencil
import ConnectedPseudospectrum.RealGapReflection

/-!
# Continuation and exact height of the even central gap

This module formalizes the even central-gap continuation used in
`eq:central-interlace`.  The
positive half of the central gap of the order-`2m` path is not a
`PositiveHalfGap`: its full nodal interval crosses `pi/2`.  We therefore
carry out the same continuation on the literal half-gap

`0 < x < 2*sqrt(a)*cos(m*pi/(2m+1))`.

The selected branch is always the actual signed middle branch
`middleBranchExtension (2m) a m`; its magnitude is the actual complex
Euclidean least singular value `realGapValue (2m) a x`.  In particular,
the endpoint-side status of `centralOuterZ0` is a conclusion of the
continuation-and-closure argument below, not an assumption built into any
definition.
-/

namespace ConnectedPseudospectrum

open Filter Set
open scoped Topology

noncomputable section

namespace EvenCentralHalfGapData

/-! ## The exact positive central half-gap -/

/-- The positive central nodal angle `m*pi/(2m+1)`. -/
def angleLower (d : EvenCentralHalfGapData) : ℝ :=
  (d.m : ℝ) * Real.pi / d.K

/-- The closed angular half-lobe from the positive central eigenvalue to
the centre of the gap. -/
abbrev Angle (d : EvenCentralHalfGapData) :=
  Icc d.angleLower (Real.pi / 2)

theorem angleLower_pos (d : EvenCentralHalfGapData) :
    0 < d.angleLower := by
  unfold angleLower
  have hm : (0 : ℝ) < d.m := by exact_mod_cast d.hm
  have hK : (0 : ℝ) < d.K := by exact_mod_cast d.K_pos
  exact div_pos (mul_pos hm Real.pi_pos) hK

theorem angleLower_lt_pi_div_two (d : EvenCentralHalfGapData) :
    d.angleLower < Real.pi / 2 := by
  have hKpos : (0 : ℝ) < d.K := by exact_mod_cast d.K_pos
  unfold angleLower
  rw [div_lt_iff₀ hKpos]
  rw [d.K_eq]
  push_cast
  nlinarith [Real.pi_pos]

/-- The centre `pi/2` still lies strictly before the next central node.
This is the point at which the full nodal interval crosses `pi/2`. -/
theorem pi_div_two_lt_nextNodeAngle (d : EvenCentralHalfGapData) :
    Real.pi / 2 <
      (((d.m + 1 : ℕ) : ℝ) * Real.pi / d.K) := by
  have hKpos : (0 : ℝ) < d.K := by exact_mod_cast d.K_pos
  rw [lt_div_iff₀ hKpos]
  rw [d.K_eq]
  push_cast
  nlinarith [Real.pi_pos]

/-- The nodal endpoint as a member of the closed central half-lobe. -/
def leftAngle (d : EvenCentralHalfGapData) : d.Angle :=
  ⟨d.angleLower, le_rfl, d.angleLower_lt_pi_div_two.le⟩

/-- The central angle `π/2` as a member of the closed central half-lobe. -/
def rightAngle (d : EvenCentralHalfGapData) : d.Angle :=
  ⟨Real.pi / 2, d.angleLower_lt_pi_div_two.le, le_rfl⟩

/-- The first positive eigenvalue bordering the central gap. -/
def positiveEndpoint (d : EvenCentralHalfGapData) : ℝ :=
  2 * pathRate d.a * d.innerEndpoint

theorem positiveEndpoint_pos (d : EvenCentralHalfGapData) :
    0 < d.positiveEndpoint := by
  unfold positiveEndpoint
  exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 d.ha0))
    d.innerEndpoint_pos

/-- The exact open positive half of the central spectral gap. -/
def positiveSpectralHalfGap (d : EvenCentralHalfGapData) : Set ℝ :=
  Ioo 0 d.positiveEndpoint

@[simp] theorem innerEndpoint_eq_cos_angleLower
    (d : EvenCentralHalfGapData) :
    d.innerEndpoint = Real.cos d.angleLower := by
  rfl

theorem innerEndpoint_le_cos_pi_div
    (d : EvenCentralHalfGapData) :
    d.innerEndpoint ≤ Real.cos (Real.pi / d.K) := by
  have hKpos : (0 : ℝ) < d.K := by exact_mod_cast d.K_pos
  have hangle : Real.pi / (d.K : ℝ) ≤ d.angleLower := by
    unfold angleLower
    rw [div_le_div_iff_of_pos_right hKpos]
    have hmcast : (1 : ℝ) ≤ d.m := by exact_mod_cast d.hm
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hmcast Real.pi_pos.le
  rw [d.innerEndpoint_eq_cos_angleLower]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
    (d.angleLower_lt_pi_div_two.le.trans (by linarith [Real.pi_pos]))
    hangle

/-- The positive central endpoint is the displayed path eigenvalue of
index `m-1`. -/
theorem positiveEndpoint_eq_symmetricPathEigenvalue
    (d : EvenCentralHalfGapData) :
    d.positiveEndpoint =
      symmetricPathEigenvalue (2 * d.m) (pathRate d.a)
        ⟨d.m - 1, by
          have hm := d.hm
          omega⟩ := by
  unfold positiveEndpoint innerEndpoint
  unfold symmetricPathEigenvalue pathEigenangle
  rw [Nat.sub_add_cancel d.hm]
  congr 2

/-- The other endpoint of the full central gap is the negative of the
positive endpoint. -/
theorem negativeEndpoint_eq_symmetricPathEigenvalue
    (d : EvenCentralHalfGapData) :
    -d.positiveEndpoint =
      symmetricPathEigenvalue (2 * d.m) (pathRate d.a)
        ⟨d.m, by
          have hm := d.hm
          omega⟩ := by
  unfold positiveEndpoint
  unfold symmetricPathEigenvalue pathEigenangle
  rw [show 2 * d.m + 1 = d.K by exact d.K_eq.symm,
    d.cos_succ_angle_eq_neg_innerEndpoint]
  ring

/-! ## The actual selected middle branch -/

/-- The continued signed middle-branch root on the even central gap. -/
def selectedRoot (d : EvenCentralHalfGapData) (x : ℝ) : ℝ :=
  middleBranchExtension (2 * d.m) d.a d.m x

/-- The actual least-singular-value height on the even central gap. -/
def selectedHeight (d : EvenCentralHalfGapData) (x : ℝ) : ℝ :=
  realGapValue (2 * d.m) d.a x

/-- The folded discriminant evaluated along the selected middle branch. -/
def selectedDiscriminant (d : EvenCentralHalfGapData) (x : ℝ) : ℝ :=
  foldDiscriminant d.a x (d.selectedRoot x)

/-- The smaller folded half-variable along the selected middle branch. -/
def selectedY (d : EvenCentralHalfGapData) (x : ℝ) : ℝ :=
  foldedHalfY d.a x (d.selectedRoot x)

/-- The larger folded half-variable along the selected middle branch. -/
def selectedZ (d : EvenCentralHalfGapData) (x : ℝ) : ℝ :=
  foldedHalfZ d.a x (d.selectedRoot x)

theorem continuous_selectedRoot (d : EvenCentralHalfGapData) :
    Continuous d.selectedRoot := by
  exact continuous_middleBranchExtension (2 * d.m) d.a d.m

theorem continuous_selectedHeight (d : EvenCentralHalfGapData) :
    Continuous d.selectedHeight := by
  exact continuous_realGapValue (2 * d.m) d.a

theorem continuous_selectedDiscriminant (d : EvenCentralHalfGapData) :
    Continuous d.selectedDiscriminant := by
  unfold selectedDiscriminant foldDiscriminant
  have hminus : Continuous (fun x : ℝ ↦ 1 + d.a - x) := by fun_prop
  have hplus : Continuous (fun x : ℝ ↦ 1 + d.a + x) := by fun_prop
  exact ((hminus.pow 2).sub (d.continuous_selectedRoot.pow 2)).mul
    ((hplus.pow 2).sub (d.continuous_selectedRoot.pow 2))

theorem continuous_selectedY (d : EvenCentralHalfGapData) :
    Continuous d.selectedY := by
  change Continuous (fun x : ℝ ↦
    foldedHalfY d.a x (d.selectedRoot x))
  rw [continuous_iff_continuousAt]
  intro x
  have hp : ContinuousAt
      (fun y : ℝ ↦ ((d.a, (y, d.selectedRoot y)) : FoldedParameterTriple)) x :=
    continuousAt_const.prodMk
      (continuousAt_id.prodMk d.continuous_selectedRoot.continuousAt)
  change ContinuousAt (fun y : ℝ ↦
    foldedHalfY d.a y (d.selectedRoot y)) x
  exact (continuousAt_foldedHalfY_parameter d.ha0.ne').comp'
    (f := fun y : ℝ ↦
      ((d.a, (y, d.selectedRoot y)) : FoldedParameterTriple)) hp

theorem continuous_selectedZ (d : EvenCentralHalfGapData) :
    Continuous d.selectedZ := by
  change Continuous (fun x : ℝ ↦
    foldedHalfZ d.a x (d.selectedRoot x))
  rw [continuous_iff_continuousAt]
  intro x
  have hp : ContinuousAt
      (fun y : ℝ ↦ ((d.a, (y, d.selectedRoot y)) : FoldedParameterTriple)) x :=
    continuousAt_const.prodMk
      (continuousAt_id.prodMk d.continuous_selectedRoot.continuousAt)
  change ContinuousAt (fun y : ℝ ↦
    foldedHalfZ d.a y (d.selectedRoot y)) x
  exact (continuousAt_foldedHalfZ_parameter d.ha0.ne').comp'
    (f := fun y : ℝ ↦
      ((d.a, (y, d.selectedRoot y)) : FoldedParameterTriple)) hp

theorem selectedRoot_eq_negOnePow_mul_height
    (d : EvenCentralHalfGapData) (x : ℝ) :
    d.selectedRoot x = (-1 : ℝ) ^ d.m * d.selectedHeight x := by
  unfold selectedRoot selectedHeight middleBranchExtension
  rw [middleBranchSign_eq_negOnePow]

theorem ne_pathEigenvalue_of_mem_positiveSpectralHalfGap
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hx : x ∈ d.positiveSpectralHalfGap)
    (k : Fin (2 * d.m)) :
    x ≠ pathEigenvalue (2 * d.m) d.a k := by
  have hm := d.hm
  have hr : 0 < pathRate d.a := Real.sqrt_pos.2 d.ha0
  rw [pathEigenvalue_eq_symmetricPathEigenvalue]
  by_cases hk : k.1 < d.m
  · have hkUpper :
        k ≤ (⟨d.m - 1, by omega⟩ : Fin (2 * d.m)) := by
      exact Fin.mk_le_mk.mpr (by omega)
    have hxEigen :
        x < symmetricPathEigenvalue (2 * d.m) (pathRate d.a) k :=
      hx.2.trans_le <| by
        rw [d.positiveEndpoint_eq_symmetricPathEigenvalue]
        exact (symmetricPathEigenvalue_strictAnti (2 * d.m) hr).antitone
          hkUpper
    exact ne_of_lt hxEigen
  · have hLower :
        (⟨d.m, by omega⟩ : Fin (2 * d.m)) ≤ k := by
      exact Fin.mk_le_mk.mpr (by omega)
    have hEigenNonpos :
        symmetricPathEigenvalue (2 * d.m) (pathRate d.a) k < 0 := by
      calc
        symmetricPathEigenvalue (2 * d.m) (pathRate d.a) k ≤
            symmetricPathEigenvalue (2 * d.m) (pathRate d.a)
              ⟨d.m, by omega⟩ :=
          (symmetricPathEigenvalue_strictAnti (2 * d.m) hr).antitone hLower
        _ = -d.positiveEndpoint := d.negativeEndpoint_eq_symmetricPathEigenvalue.symm
        _ < 0 := neg_neg_of_pos d.positiveEndpoint_pos
    exact ne_of_gt (hEigenNonpos.trans hx.1)

theorem selectedHeight_pos_of_mem_gap
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hx : x ∈ d.positiveSpectralHalfGap) :
    0 < d.selectedHeight x := by
  have hn : 0 < 2 * d.m := by
    have hm := d.hm
    omega
  have hnonneg : 0 ≤ d.selectedHeight x := by
    unfold selectedHeight realGapValue pseudospectralHeight
    exact leastSingularValue_nonneg _
  have hne : d.selectedHeight x ≠ 0 := by
    intro hzero
    obtain ⟨k, hk⟩ :=
      (pseudospectralHeight_eq_zero_iff
        (2 * d.m) d.ha0 hn (x : ℂ)).1 hzero
    have hkReal : x = pathEigenvalue (2 * d.m) d.a k :=
      Complex.ofReal_injective hk
    exact d.ne_pathEigenvalue_of_mem_positiveSpectralHalfGap hx k hkReal
  exact lt_of_le_of_ne hnonneg hne.symm

theorem selectedRoot_ne_zero_of_mem_gap
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hx : x ∈ d.positiveSpectralHalfGap) :
    d.selectedRoot x ≠ 0 := by
  rw [d.selectedRoot_eq_negOnePow_mul_height]
  exact mul_ne_zero (pow_ne_zero d.m (by norm_num))
    (d.selectedHeight_pos_of_mem_gap hx).ne'

/-- The selected branch solves the literal signed pencil throughout the
positive central half-gap. -/
theorem signedPencilDet_selectedRoot_eq_zero_of_mem_gap
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hx : x ∈ d.positiveSpectralHalfGap) :
    signedPencilDet (2 * d.m) d.a x (d.selectedRoot x) = 0 := by
  have hm := d.hm
  have hr : 0 < pathRate d.a := Real.sqrt_pos.2 d.ha0
  have hrsq : pathRate d.a ^ 2 = d.a := Real.sq_sqrt d.ha0.le
  have hxLower :
      symmetricPathEigenvalue (2 * d.m) (pathRate d.a)
          ⟨d.m, by omega⟩ < x := by
    rw [← d.negativeEndpoint_eq_symmetricPathEigenvalue]
    exact (neg_neg_of_pos d.positiveEndpoint_pos).trans hx.1
  have hxUpper :
      x < symmetricPathEigenvalue (2 * d.m) (pathRate d.a)
          ⟨d.m - 1, by omega⟩ := by
    rw [← d.positiveEndpoint_eq_symmetricPathEigenvalue]
    exact hx.2
  rcases Nat.even_or_odd d.m with hmEven | hmOdd
  · have hbridge := evenMiddleBranch_bridge_even_gap
      d.m d.m (by omega) d.hm (by omega) hmEven hr hxLower hxUpper
    have hdet :
        signedPencilDet (2 * d.m) (pathRate d.a ^ 2) x
          (middleBranchExtension (2 * d.m) (pathRate d.a ^ 2) d.m x) = 0 := by
      rw [hbridge.2.2.1]
      exact hbridge.2.2.2
    simpa only [selectedRoot, hrsq] using hdet
  · by_cases hmOne : d.m = 1
    · have hxLower' :
          symmetricPathEigenvalue 2 (pathRate d.a) ⟨1, by omega⟩ < x := by
        calc
          symmetricPathEigenvalue 2 (pathRate d.a) ⟨1, by omega⟩ =
              symmetricPathEigenvalue (2 * d.m) (pathRate d.a)
                ⟨d.m, by omega⟩ := by
            simp [symmetricPathEigenvalue, pathEigenangle, hmOne]
          _ < x := hxLower
      have hxUpper' :
          x < symmetricPathEigenvalue 2 (pathRate d.a) ⟨0, by omega⟩ := by
        calc
          x < symmetricPathEigenvalue (2 * d.m) (pathRate d.a)
              ⟨d.m - 1, by omega⟩ := hxUpper
          _ = symmetricPathEigenvalue 2 (pathRate d.a) ⟨0, by omega⟩ := by
            simp [symmetricPathEigenvalue, pathEigenangle, hmOne]
      have hbridge := twoMiddleBranch_bridge_odd_gap
        1 (by omega) (by omega) (by norm_num) hr hxLower' hxUpper'
      have hdet :
          signedPencilDet 2 (pathRate d.a ^ 2) x
            (middleBranchExtension 2 (pathRate d.a ^ 2) 1 x) = 0 := by
        rw [hbridge.2.2.1]
        exact hbridge.2.2.2
      simpa [selectedRoot, hrsq, hmOne] using hdet
    · have hmTwo : 2 ≤ d.m := by omega
      have hbridge := evenMiddleBranch_bridge_odd_gap
        d.m d.m hmTwo d.hm (by omega) hmOdd hr hxLower hxUpper
      have hdet :
          signedPencilDet (2 * d.m) (pathRate d.a ^ 2) x
            (middleBranchExtension (2 * d.m) (pathRate d.a ^ 2) d.m x) = 0 := by
        rw [hbridge.2.2.1]
        exact hbridge.2.2.2
      simpa only [selectedRoot, hrsq] using hdet

/-! ## A central endpoint-side chord family used to seed continuation -/

/-- The unique maximizer of the endpoint-side outer chord lobe. -/
noncomputable def outerLobeMaximizer
    (d : EvenCentralHalfGapData) : ℝ :=
  Classical.choose
    (existsUnique_outerChordLobeMaximum d.K d.two_le_K d.a d.ha0 d.ha1)

theorem outerLobeMaximizer_spec (d : EvenCentralHalfGapData) :
    d.outerLobeMaximizer ∈
        Ioo (Real.cos (Real.pi / d.K))
          (Real.cosh (pathLogParameter d.a)) ∧
      IsMaxOn (chordLobeWeight d.K d.a)
        (Icc (Real.cos (Real.pi / d.K))
          (Real.cosh (pathLogParameter d.a)))
        d.outerLobeMaximizer := by
  exact (Classical.choose_spec
    (existsUnique_outerChordLobeMaximum d.K d.two_le_K d.a d.ha0 d.ha1)).1

theorem chordPhi_le_outerLobeMaximum
    (d : EvenCentralHalfGapData) (theta : d.Angle) :
    chordPhi d.K d.a theta ≤
      chordLobeWeight d.K d.a d.outerLobeMaximizer := by
  rcases eq_or_lt_of_le theta.2.1 with hleft | hleft
  · have hnode := chordPhi_nodal (K := d.K) (k := d.m)
      d.two_le_K d.hm (by
        have hm := d.hm
        unfold K
        omega) d.a
    have hzero : chordPhi d.K d.a theta = 0 := by
      rw [← hleft]
      simpa only [angleLower] using hnode
    rw [hzero]
    exact chordLobeWeight_nonneg _ _ _
  · exact (chordPhi_inner_lt_outerLobeMaximum
      d.two_le_K d.hm d.ha0 d.ha1 hleft
      (theta.2.2.trans_lt d.pi_div_two_lt_nextNodeAngle)
      theta.2.2 d.outerLobeMaximizer_spec.2).le

/-- The central inner-lobe level, bundled with its admissible outer-lobe
bounds. -/
noncomputable def innerLevel
    (d : EvenCentralHalfGapData) (theta : d.Angle) :
    Icc (0 : ℝ) (chordLobeWeight d.K d.a d.outerLobeMaximizer) :=
  ⟨chordPhi d.K d.a theta, chordPhi_nonneg d.K d.a theta,
    d.chordPhi_le_outerLobeMaximum theta⟩

theorem continuous_innerLevel (d : EvenCentralHalfGapData) :
    Continuous d.innerLevel := by
  apply Continuous.subtype_mk
  exact (continuous_chordPhi d.K d.a).comp continuous_subtype_val

/-- The endpoint-side outer coordinate whose lobe level matches the inner
central angle. -/
noncomputable def chordZ
    (d : EvenCentralHalfGapData) (theta : d.Angle) : ℝ :=
  outerLobeEndpointSolution d.K d.two_le_K d.a d.ha0 d.ha1
    d.outerLobeMaximizer d.outerLobeMaximizer_spec.1
    d.outerLobeMaximizer_spec.2 (d.innerLevel theta)

theorem chordZ_mem (d : EvenCentralHalfGapData) (theta : d.Angle) :
    d.chordZ theta ∈
      Icc d.outerLobeMaximizer (Real.cosh (pathLogParameter d.a)) := by
  exact outerLobeEndpointSolution_mem d.K d.two_le_K d.a d.ha0 d.ha1
    d.outerLobeMaximizer d.outerLobeMaximizer_spec.1
    d.outerLobeMaximizer_spec.2 (d.innerLevel theta)

theorem chordLobeWeight_chordZ
    (d : EvenCentralHalfGapData) (theta : d.Angle) :
    chordLobeWeight d.K d.a (d.chordZ theta) =
      chordPhi d.K d.a theta := by
  exact chordLobeWeight_outerLobeEndpointSolution
    d.K d.two_le_K d.a d.ha0 d.ha1 d.outerLobeMaximizer
    d.outerLobeMaximizer_spec.1 d.outerLobeMaximizer_spec.2
    (d.innerLevel theta)

theorem continuous_chordZ (d : EvenCentralHalfGapData) :
    Continuous d.chordZ := by
  exact (continuous_outerLobeEndpointSolution
    d.K d.two_le_K d.a d.ha0 d.ha1 d.outerLobeMaximizer
    d.outerLobeMaximizer_spec.1 d.outerLobeMaximizer_spec.2).comp
      d.continuous_innerLevel

theorem outerLobeMaximizer_lt_chordZ
    (d : EvenCentralHalfGapData) (theta : d.Angle)
    (hleft : d.angleLower < theta) :
    d.outerLobeMaximizer < d.chordZ theta := by
  have hlevel : chordPhi d.K d.a theta <
      chordLobeWeight d.K d.a d.outerLobeMaximizer :=
    chordPhi_inner_lt_outerLobeMaximum d.two_le_K d.hm d.ha0 d.ha1
      hleft (theta.2.2.trans_lt d.pi_div_two_lt_nextNodeAngle)
      theta.2.2 d.outerLobeMaximizer_spec.2
  have hne : d.chordZ theta ≠ d.outerLobeMaximizer := by
    intro hz
    have hweight := d.chordLobeWeight_chordZ theta
    rw [hz] at hweight
    exact (ne_of_lt hlevel) hweight.symm
  exact lt_of_le_of_ne (d.chordZ_mem theta).1 hne.symm

theorem chordZ_nonneg
    (d : EvenCentralHalfGapData) (theta : d.Angle) :
    0 ≤ d.chordZ theta := by
  have hfirst : 0 ≤ Real.cos (Real.pi / d.K) :=
    cos_pi_div_nat_nonneg d.two_le_K
  exact hfirst.trans
    (d.outerLobeMaximizer_spec.1.1.le.trans (d.chordZ_mem theta).1)

theorem chordZ_abs_le_cosh
    (d : EvenCentralHalfGapData) (theta : d.Angle) :
    |d.chordZ theta| ≤ Real.cosh (pathLogParameter d.a) := by
  rw [abs_of_nonneg (d.chordZ_nonneg theta)]
  exact (d.chordZ_mem theta).2

theorem chordZ_lt_cosh
    (d : EvenCentralHalfGapData) (theta : d.Angle)
    (hleft : d.angleLower < theta) :
    d.chordZ theta < Real.cosh (pathLogParameter d.a) := by
  have hPhi : 0 < chordPhi d.K d.a theta :=
    chordPhi_pos_on_nodalInterval d.K d.m d.two_le_K (by
      have hm := d.hm
      unfold K
      omega)
      d.a ⟨hleft, theta.2.2.trans_lt d.pi_div_two_lt_nextNodeAngle⟩
      (halfTrigRadical_pos_of_pathParameter d.ha0 d.ha1 theta)
  exact lt_of_le_of_ne (d.chordZ_mem theta).2 fun heq => by
    have hweight := d.chordLobeWeight_chordZ theta
    rw [heq, chordLobeWeight_cosh_endpoint] at hweight
    linarith

theorem cos_sq_lt_chordZ_sq
    (d : EvenCentralHalfGapData) (theta : d.Angle)
    (hleft : d.angleLower < theta) :
    Real.cos theta ^ 2 < d.chordZ theta ^ 2 := by
  have hcosNonneg : 0 ≤ Real.cos theta := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · linarith [Real.pi_pos, d.angleLower_pos, theta.2.1]
    · exact theta.2.2
  have hgt := outerEndpointSide_gt_innerCos d.two_le_K d.hm hleft
    theta.2.2 d.outerLobeMaximizer_spec.1
    (d.outerLobeMaximizer_lt_chordZ theta hleft)
  nlinarith [d.chordZ_nonneg theta]

/-- The abscissa of the central endpoint-side chord family. -/
noncomputable def chordX
    (d : EvenCentralHalfGapData) (theta : d.Angle) : ℝ :=
  outerChordX d.a theta (d.chordZ theta)

/-- The nonnegative height of the central endpoint-side chord family. -/
noncomputable def chordS
    (d : EvenCentralHalfGapData) (theta : d.Angle) : ℝ :=
  outerChordS d.a theta (d.chordZ theta)

/-- The chord height with the parity sign of the selected middle branch. -/
noncomputable def signedChordRoot
    (d : EvenCentralHalfGapData) (theta : d.Angle) : ℝ :=
  (-1 : ℝ) ^ d.m * d.chordS theta

theorem continuous_chordX (d : EvenCentralHalfGapData) :
    Continuous d.chordX := by
  unfold chordX outerChordX
  exact ((continuous_const.mul
    (Real.continuous_cos.comp continuous_subtype_val)).mul
      d.continuous_chordZ)

theorem continuous_chordS (d : EvenCentralHalfGapData) :
    Continuous d.chordS := by
  unfold chordS outerChordS
  have hcos : Continuous fun theta : d.Angle ↦ Real.cos (theta : ℝ) :=
    Real.continuous_cos.comp continuous_subtype_val
  exact continuous_const.mul
    ((continuous_const.sub (hcos.pow 2)).mul
      (continuous_const.sub (d.continuous_chordZ.pow 2))).sqrt

theorem continuous_signedChordRoot (d : EvenCentralHalfGapData) :
    Continuous d.signedChordRoot := by
  unfold signedChordRoot
  exact continuous_const.mul d.continuous_chordS

@[simp] theorem chordZ_leftAngle (d : EvenCentralHalfGapData) :
    d.chordZ d.leftAngle = Real.cosh (pathLogParameter d.a) := by
  have hzero : chordPhi d.K d.a d.leftAngle = 0 := by
    simpa only [leftAngle, angleLower] using
      chordPhi_nodal (K := d.K) (k := d.m) d.two_le_K d.hm
        (by
          have hm := d.hm
          unfold K
          omega) d.a
  have hanti := outerChordLobeWeight_strictAntiOn_closedEndpointSide
    d.K d.two_le_K d.a d.ha0 d.ha1 d.outerLobeMaximizer_spec.1
      d.outerLobeMaximizer_spec.2
  apply hanti.injOn (d.chordZ_mem d.leftAngle)
    ⟨d.outerLobeMaximizer_spec.1.2.le, le_rfl⟩
  rw [d.chordLobeWeight_chordZ, hzero, chordLobeWeight_cosh_endpoint]

@[simp] theorem chordX_leftAngle (d : EvenCentralHalfGapData) :
    d.chordX d.leftAngle = d.positiveEndpoint := by
  unfold chordX outerChordX positiveEndpoint
  rw [d.chordZ_leftAngle]
  change halfChordScale d.a * d.innerEndpoint *
      Real.cosh (pathLogParameter d.a) = _
  calc
    halfChordScale d.a * d.innerEndpoint *
          Real.cosh (pathLogParameter d.a) =
        (halfChordScale d.a * Real.cosh (pathLogParameter d.a)) *
          d.innerEndpoint := by ring
    _ = 2 * pathRate d.a * d.innerEndpoint := by
      rw [halfChordScale_mul_cosh_pathLogParameter]

@[simp] theorem chordS_leftAngle (d : EvenCentralHalfGapData) :
    d.chordS d.leftAngle = 0 := by
  unfold chordS outerChordS
  rw [d.chordZ_leftAngle]
  ring_nf
  simp

@[simp] theorem signedChordRoot_leftAngle (d : EvenCentralHalfGapData) :
    d.signedChordRoot d.leftAngle = 0 := by
  simp [signedChordRoot]

@[simp] theorem chordX_rightAngle (d : EvenCentralHalfGapData) :
    d.chordX d.rightAngle = 0 := by
  unfold chordX outerChordX rightAngle
  rw [Real.cos_pi_div_two, mul_zero, zero_mul]

theorem chordS_pos
    (d : EvenCentralHalfGapData) (theta : d.Angle)
    (hleft : d.angleLower < theta) :
    0 < d.chordS theta := by
  unfold chordS
  exact outerChordS_pos_of_nonneg_of_lt_cosh d.ha0 d.ha1 theta
    (d.chordZ_nonneg theta) (d.chordZ_lt_cosh theta hleft)

theorem signedChordRoot_ne_zero
    (d : EvenCentralHalfGapData) (theta : d.Angle)
    (hleft : d.angleLower < theta) :
    d.signedChordRoot theta ≠ 0 := by
  unfold signedChordRoot
  exact mul_ne_zero (pow_ne_zero d.m (by norm_num))
    (d.chordS_pos theta hleft).ne'

theorem chordX_mem_positiveSpectralHalfGap
    (d : EvenCentralHalfGapData) (theta : d.Angle)
    (hleft : d.angleLower < theta) (hright : theta < Real.pi / 2) :
    d.chordX theta ∈ d.positiveSpectralHalfGap := by
  have hcosPos : 0 < Real.cos theta := by
    exact Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, d.angleLower_pos, theta.2.1], hright⟩
  have hxPos : 0 < d.chordX theta := by
    unfold chordX outerChordX
    exact mul_pos (mul_pos (halfChordScale_pos d.ha0) hcosPos)
      (lt_of_lt_of_le (by
        exact (cos_pi_div_nat_nonneg d.two_le_K).trans_lt
          d.outerLobeMaximizer_spec.1.1) (d.chordZ_mem theta).1)
  have hcosStrict : Real.cos theta < d.innerEndpoint := by
    rw [d.innerEndpoint_eq_cos_angleLower]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi d.angleLower_pos.le
      (theta.2.2.trans (by linarith [Real.pi_pos])) hleft
  have hscaleCos : 0 ≤ halfChordScale d.a * Real.cos theta :=
    mul_nonneg (halfChordScale_pos d.ha0).le hcosPos.le
  have hxUpper : d.chordX theta < d.positiveEndpoint := by
    calc
      d.chordX theta =
          halfChordScale d.a * Real.cos theta * d.chordZ theta := rfl
      _ ≤ halfChordScale d.a * Real.cos theta *
          Real.cosh (pathLogParameter d.a) :=
        mul_le_mul_of_nonneg_left (d.chordZ_mem theta).2 hscaleCos
      _ = 2 * pathRate d.a * Real.cos theta := by
        calc
          halfChordScale d.a * Real.cos theta *
                Real.cosh (pathLogParameter d.a) =
              (halfChordScale d.a * Real.cosh (pathLogParameter d.a)) *
                Real.cos theta := by ring
          _ = 2 * pathRate d.a * Real.cos theta := by
            rw [halfChordScale_mul_cosh_pathLogParameter]
      _ < 2 * pathRate d.a * d.innerEndpoint :=
        mul_lt_mul_of_pos_left hcosStrict
          (mul_pos (by norm_num) (Real.sqrt_pos.2 d.ha0))
      _ = d.positiveEndpoint := rfl
  exact ⟨hxPos, hxUpper⟩

theorem signed_chord_equation
    (d : EvenCentralHalfGapData) (theta : d.Angle)
    (hleft : d.angleLower < theta) :
    halfTrigRadical d.a theta *
        chebyshevU (2 * d.m) (Real.cos theta) =
      (-1 : ℝ) ^ d.m * outerChordRadical d.a (d.chordZ theta) *
        chebyshevU (2 * d.m) (d.chordZ theta) := by
  have hinner :=
    halfTrigRadical_mul_chebyshevU_eq_negOnePow_mul_chordPhi
      d.K d.m d.two_le_K (by
        have hm := d.hm
        unfold K
        omega) d.a
      ⟨hleft, theta.2.2.trans_lt d.pi_div_two_lt_nextNodeAngle⟩
  have hzFirst : Real.cos (Real.pi / d.K) < d.chordZ theta :=
    d.outerLobeMaximizer_spec.1.1.trans
      (d.outerLobeMaximizer_lt_chordZ theta hleft)
  have houterPos := chebyshevU_pos_of_firstNode_lt d.two_le_K hzFirst
  have houter := d.chordLobeWeight_chordZ theta
  unfold chordLobeWeight at houter
  rw [abs_of_pos houterPos] at houter
  have hindex : ((d.K - 1 : ℕ) : ℤ) = 2 * (d.m : ℤ) := by
    exact_mod_cast d.K_sub_one
  have houter' : outerChordRadical d.a (d.chordZ theta) *
      chebyshevU (d.K - 1 : ℕ) (d.chordZ theta) =
        chordPhi d.K d.a theta := by
    simpa only [outerChordRadical] using houter
  simpa only [hindex, outerChordRadical] using hinner.trans <| by
    calc
      (-1 : ℝ) ^ d.m * chordPhi d.K d.a theta =
          (-1 : ℝ) ^ d.m *
            (outerChordRadical d.a (d.chordZ theta) *
              chebyshevU (d.K - 1 : ℕ) (d.chordZ theta)) := by
        exact congrArg (fun t : ℝ ↦ (-1 : ℝ) ^ d.m * t) houter'.symm
      _ = _ := by
        rw [hindex]
        unfold outerChordRadical
        ring

theorem signedPencilDet_signedChordRoot_eq_zero
    (d : EvenCentralHalfGapData) (theta : d.Angle)
    (hleft : d.angleLower < theta) :
    signedPencilDet (2 * d.m) d.a (d.chordX theta)
      (d.signedChordRoot theta) = 0 := by
  rw [signedPencilDet_even_eq_foldEvenSequence]
  have hiff := foldEvenSequence_signed_outerChord_eq_zero_iff
    d.m d.ha0 (d.chordZ_abs_le_cosh theta)
    (d.cos_sq_lt_chordZ_sq theta hleft) (negOnePow_sq d.m)
  change foldEvenSequence d.a
    (outerChordX d.a theta (d.chordZ theta))
    ((-1 : ℝ) ^ d.m * outerChordS d.a theta (d.chordZ theta)) d.m = 0
  exact hiff.2 (d.signed_chord_equation theta hleft)

/-! ## Endpoint germ and the initial classified point -/

theorem eventually_chordX_mem_positiveSpectralHalfGap_left
    (d : EvenCentralHalfGapData) :
    ∀ᶠ theta in 𝓝[Ioi d.leftAngle] d.leftAngle,
      d.leftAngle < theta ∧ theta < d.rightAngle ∧
        d.chordX theta ∈ d.positiveSpectralHalfGap := by
  have hAngles : d.leftAngle < d.rightAngle :=
    d.angleLower_lt_pi_div_two
  have hright : ∀ᶠ theta : d.Angle in 𝓝 d.leftAngle,
      theta < d.rightAngle :=
    eventually_lt_nhds hAngles
  filter_upwards [self_mem_nhdsWithin,
    hright.filter_mono nhdsWithin_le_nhds] with theta hleft hright
  exact ⟨hleft, hright,
    d.chordX_mem_positiveSpectralHalfGap theta hleft hright⟩

/-- Local uniqueness at the simple positive central eigenvalue identifies
the central chord root with the actual selected middle branch. -/
theorem eventually_signedChordRoot_eq_selectedRoot_left
    (d : EvenCentralHalfGapData) :
    ∀ᶠ theta in 𝓝[Ioi d.leftAngle] d.leftAngle,
      d.signedChordRoot theta = d.selectedRoot (d.chordX theta) := by
  have hn : 0 < 2 * d.m := by
    have hm := d.hm
    omega
  have hr : 0 < pathRate d.a := Real.sqrt_pos.2 d.ha0
  have hrsq : pathRate d.a ^ 2 = d.a := Real.sq_sqrt d.ha0.le
  let k : Fin (2 * d.m) := ⟨d.m - 1, by
    have hm := d.hm
    omega⟩
  let x0 : ℝ := symmetricPathEigenvalue (2 * d.m) (pathRate d.a) k
  have hx0 : x0 = d.positiveEndpoint := by
    simpa only [x0, k] using d.positiveEndpoint_eq_symmetricPathEigenvalue.symm
  have hChordPair :
      Tendsto (fun theta : d.Angle ↦
        (d.chordX theta, d.signedChordRoot theta))
        (𝓝 d.leftAngle) (𝓝 (x0, 0)) := by
    have hcontinuous : ContinuousAt (fun theta : d.Angle ↦
        (d.chordX theta, d.signedChordRoot theta)) d.leftAngle :=
      (d.continuous_chordX.prodMk d.continuous_signedChordRoot).continuousAt
    have hend :
        (d.chordX d.leftAngle, d.signedChordRoot d.leftAngle) = (x0, 0) := by
      rw [d.chordX_leftAngle, d.signedChordRoot_leftAngle, ← hx0]
    rw [← hend]
    exact hcontinuous
  have hMiddleEndpoint : d.selectedRoot x0 = 0 := by
    unfold selectedRoot
    rw [← hrsq]
    exact middleBranchExtension_symmetricPathEigenvalue_sq_eq_zero
      (2 * d.m) hn d.m hr k
  have hMiddlePair :
      Tendsto (fun theta : d.Angle ↦
        (d.chordX theta, d.selectedRoot (d.chordX theta)))
        (𝓝 d.leftAngle) (𝓝 (x0, 0)) := by
    have hcontinuous : Continuous (fun theta : d.Angle ↦
        (d.chordX theta, d.selectedRoot (d.chordX theta))) :=
      d.continuous_chordX.prodMk
        (d.continuous_selectedRoot.comp d.continuous_chordX)
    have hend :
        (d.chordX d.leftAngle,
          d.selectedRoot (d.chordX d.leftAngle)) = (x0, 0) := by
      rw [d.chordX_leftAngle, ← hx0, hMiddleEndpoint]
    rw [← hend]
    exact hcontinuous.continuousAt
  have hunique := eventually_signedPencilLocalRoot_eq_of_det_zero
    (2 * d.m) hn hr k
  have hChordUnique := hChordPair.eventually hunique
  have hMiddleUnique := hMiddlePair.eventually hunique
  filter_upwards [d.eventually_chordX_mem_positiveSpectralHalfGap_left,
    hChordUnique.filter_mono nhdsWithin_le_nhds,
    hMiddleUnique.filter_mono nhdsWithin_le_nhds] with
      theta hgap hChord hMiddle
  have hdetChord :
      signedPencilDet (2 * d.m) (pathRate d.a ^ 2)
        (d.chordX theta) (d.signedChordRoot theta) = 0 := by
    rw [hrsq]
    exact d.signedPencilDet_signedChordRoot_eq_zero theta hgap.1
  have hdetMiddle :
      signedPencilDet (2 * d.m) (pathRate d.a ^ 2)
        (d.chordX theta) (d.selectedRoot (d.chordX theta)) = 0 := by
    rw [hrsq]
    exact d.signedPencilDet_selectedRoot_eq_zero_of_mem_gap hgap.2.2
  exact (hChord hdetChord).symm.trans (hMiddle hdetMiddle)

theorem exists_signedChordRoot_eq_selectedRoot_left
    (d : EvenCentralHalfGapData) :
    ∃ theta : d.Angle,
      d.angleLower < theta ∧ theta < Real.pi / 2 ∧
        d.chordX theta ∈ d.positiveSpectralHalfGap ∧
        d.signedChordRoot theta = d.selectedRoot (d.chordX theta) := by
  have hAngles : d.leftAngle < d.rightAngle :=
    d.angleLower_lt_pi_div_two
  letI : NeBot (𝓝[Ioi d.leftAngle] d.leftAngle) :=
    nhdsGT_neBot_of_exists_gt ⟨d.rightAngle, hAngles⟩
  obtain ⟨theta, htheta⟩ :=
    (d.eventually_chordX_mem_positiveSpectralHalfGap_left.and
      d.eventually_signedChordRoot_eq_selectedRoot_left).exists
  exact ⟨theta, htheta.1.1, htheta.1.2.1,
    htheta.1.2.2, htheta.2⟩

theorem selectedCoordinates_eq_chord_of_agreement
    (d : EvenCentralHalfGapData) (theta : d.Angle)
    (hleft : d.angleLower < theta)
    (hagree : d.signedChordRoot theta = d.selectedRoot (d.chordX theta)) :
    d.selectedY (d.chordX theta) = Real.cos theta ∧
      d.selectedZ (d.chordX theta) = d.chordZ theta := by
  have horder := d.cos_sq_lt_chordZ_sq theta hleft
  have hz := d.chordZ_abs_le_cosh theta
  have hsign := negOnePow_sq d.m
  have hminus :
      foldXiMinus d.a (d.chordX theta)
          (d.selectedRoot (d.chordX theta)) =
        halfFoldArgument (Real.cos theta) := by
    rw [← hagree]
    unfold chordX signedChordRoot chordS
    rw [foldXiMinus_signed_outerChord d.ha0 hz horder hsign]
    rfl
  have hplus :
      foldXiPlus d.a (d.chordX theta)
          (d.selectedRoot (d.chordX theta)) =
        halfFoldArgument (d.chordZ theta) := by
    rw [← hagree]
    unfold chordX signedChordRoot chordS
    rw [foldXiPlus_signed_outerChord d.ha0 hz horder hsign]
    rfl
  have hcos : 0 ≤ Real.cos theta := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · linarith [Real.pi_pos, d.angleLower_pos, theta.2.1]
    · exact theta.2.2
  simpa only [selectedY, selectedZ] using
    foldedHalfVariables_eq_of_generic hcos (d.chordZ_nonneg theta)
      hminus hplus

theorem selectedDiscriminant_pos_of_chord_agreement
    (d : EvenCentralHalfGapData) (theta : d.Angle)
    (hleft : d.angleLower < theta)
    (hagree : d.signedChordRoot theta = d.selectedRoot (d.chordX theta)) :
    0 < d.selectedDiscriminant (d.chordX theta) := by
  have horder := d.cos_sq_lt_chordZ_sq theta hleft
  have hz := d.chordZ_abs_le_cosh theta
  have hsign := negOnePow_sq d.m
  unfold selectedDiscriminant
  rw [← hagree]
  unfold chordX signedChordRoot chordS
  rw [foldDiscriminant_signed_outerChord_eq d.a theta
      (d.chordZ theta) ((-1 : ℝ) ^ d.m) hsign,
    foldDiscriminant_outerChord d.ha0 hz]
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos d.ha0))
    (sq_pos_of_pos (sub_pos.mpr horder))

/-! ## The central classified sheet -/

/-- Abscissae where the selected folded variables lie on the desired central
inner and endpoint-side outer lobes. -/
def rawClassifiedSet (d : EvenCentralHalfGapData) : Set ℝ :=
  {x |
    0 < d.selectedDiscriminant x ∧
    0 < d.selectedY x ∧
    d.selectedY x < d.innerEndpoint ∧
    d.outerLobeMaximizer < d.selectedZ x ∧
    d.selectedZ x < Real.cosh (pathLogParameter d.a)}

/-- The classified sheet restricted to the positive central spectral
half-gap. -/
def classifiedSet (d : EvenCentralHalfGapData) : Set ℝ :=
  d.positiveSpectralHalfGap ∩ d.rawClassifiedSet

theorem isOpen_rawClassifiedSet (d : EvenCentralHalfGapData) :
    IsOpen d.rawClassifiedSet := by
  unfold rawClassifiedSet
  exact (isOpen_lt continuous_const d.continuous_selectedDiscriminant).inter
    ((isOpen_lt continuous_const d.continuous_selectedY).inter
      ((isOpen_lt d.continuous_selectedY continuous_const).inter
        ((isOpen_lt continuous_const d.continuous_selectedZ).inter
          (isOpen_lt d.continuous_selectedZ continuous_const))))

theorem classifiedSet_nonempty (d : EvenCentralHalfGapData) :
    d.classifiedSet.Nonempty := by
  obtain ⟨theta, hleft, hright, hxGap, hagree⟩ :=
    d.exists_signedChordRoot_eq_selectedRoot_left
  have hcoords := d.selectedCoordinates_eq_chord_of_agreement
    theta hleft hagree
  have hdisc := d.selectedDiscriminant_pos_of_chord_agreement
    theta hleft hagree
  have hcosPos : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, d.angleLower_pos, theta.2.1], hright⟩
  have hcosUpper : Real.cos theta < d.innerEndpoint := by
    rw [d.innerEndpoint_eq_cos_angleLower]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi d.angleLower_pos.le
      (theta.2.2.trans (by linarith [Real.pi_pos])) hleft
  refine ⟨d.chordX theta, hxGap, hdisc, ?_, ?_, ?_, ?_⟩
  · rw [hcoords.1]
    exact hcosPos
  · rw [hcoords.1]
    exact hcosUpper
  · rw [hcoords.2]
    exact d.outerLobeMaximizer_lt_chordZ theta hleft
  · rw [hcoords.2]
    exact d.chordZ_lt_cosh theta hleft

/-- A point of the open positive half of the central spectral gap. -/
abbrev GapPoint (d : EvenCentralHalfGapData) :=
  {x : ℝ // x ∈ d.positiveSpectralHalfGap}

/-- Classified points represented in the positive-half-gap subtype. -/
def classifiedInGap (d : EvenCentralHalfGapData) : Set d.GapPoint :=
  {p | (p : ℝ) ∈ d.rawClassifiedSet}

/-- The real-coordinate image of the classified half-gap points. -/
def classifiedGapImage (d : EvenCentralHalfGapData) : Set ℝ :=
  ((↑) : d.GapPoint → ℝ) '' d.classifiedInGap

/-- The smaller squared folded variable along the selected middle branch. -/
def selectedXiMinus (d : EvenCentralHalfGapData) (x : ℝ) : ℝ :=
  foldXiMinus d.a x (d.selectedRoot x)

/-- The larger squared folded variable along the selected middle branch. -/
def selectedXiPlus (d : EvenCentralHalfGapData) (x : ℝ) : ℝ :=
  foldXiPlus d.a x (d.selectedRoot x)

theorem continuous_selectedXiMinus (d : EvenCentralHalfGapData) :
    Continuous d.selectedXiMinus := by
  have hroot := d.continuous_selectedRoot
  have hc0 : Continuous
      (fun x : ℝ ↦ foldC0 d.a x (d.selectedRoot x)) := by
    unfold foldC0
    exact ((continuous_id.pow 2).add continuous_const).sub (hroot.pow 2)
  unfold selectedXiMinus foldXiMinus
  exact (hc0.sub d.continuous_selectedDiscriminant.sqrt).div_const
    (4 * d.a)

theorem continuous_selectedXiPlus (d : EvenCentralHalfGapData) :
    Continuous d.selectedXiPlus := by
  have hroot := d.continuous_selectedRoot
  have hc0 : Continuous
      (fun x : ℝ ↦ foldC0 d.a x (d.selectedRoot x)) := by
    unfold foldC0
    exact ((continuous_id.pow 2).add continuous_const).sub (hroot.pow 2)
  unfold selectedXiPlus foldXiPlus
  exact (hc0.add d.continuous_selectedDiscriminant.sqrt).div_const
    (4 * d.a)

theorem selectedY_mem_Icc_of_classified
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hx : x ∈ d.rawClassifiedSet) :
    d.selectedY x ∈ Icc (-1 : ℝ) 1 := by
  exact ⟨by linarith [hx.2.1],
    hx.2.2.1.le.trans (Real.cos_le_one d.angleLower)⟩

/-- The principal angle recovered from the selected inner folded variable. -/
def selectedAngle (d : EvenCentralHalfGapData) (x : ℝ) : ℝ :=
  Real.arccos (d.selectedY x)

theorem continuous_selectedAngle (d : EvenCentralHalfGapData) :
    Continuous d.selectedAngle := by
  exact Real.continuous_arccos.comp d.continuous_selectedY

theorem cos_selectedAngle_of_classified
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hx : x ∈ d.rawClassifiedSet) :
    Real.cos (d.selectedAngle x) = d.selectedY x := by
  exact Real.cos_arccos
    (d.selectedY_mem_Icc_of_classified hx).1
    (d.selectedY_mem_Icc_of_classified hx).2

theorem selectedAngle_mem_openHalfLobe_of_classified
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hx : x ∈ d.rawClassifiedSet) :
    d.angleLower < d.selectedAngle x ∧
      d.selectedAngle x < Real.pi / 2 := by
  have hy := d.selectedY_mem_Icc_of_classified hx
  constructor
  · have h := Real.arccos_lt_arccos hy.1 hx.2.2.1
      (Real.cos_le_one d.angleLower)
    rw [d.innerEndpoint_eq_cos_angleLower] at h
    rw [Real.arccos_cos d.angleLower_pos.le
      (d.angleLower_lt_pi_div_two.le.trans
        (by linarith [Real.pi_pos]))] at h
    exact h
  · have h := Real.arccos_lt_arccos
      (by norm_num : (-1 : ℝ) ≤ 0) hx.2.1 hy.2
    simpa only [Real.arccos_zero] using h

theorem selectedXiMinus_ge_negOne_of_classified
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hx : x ∈ d.rawClassifiedSet) :
    -1 ≤ d.selectedXiMinus x := by
  have hsqrt : 0 < Real.sqrt ((d.selectedXiMinus x + 1) / 2) := by
    simpa only [selectedY, foldedHalfY, selectedXiMinus] using hx.2.1
  linarith [Real.sqrt_pos.1 hsqrt]

theorem selectedXiPlus_ge_negOne_of_classified
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hx : x ∈ d.rawClassifiedSet) :
    -1 ≤ d.selectedXiPlus x := by
  have hzPos : 0 < d.selectedZ x :=
    ((cos_pi_div_nat_nonneg d.two_le_K).trans_lt
      d.outerLobeMaximizer_spec.1.1).trans hx.2.2.2.1
  have hsqrt : 0 < Real.sqrt ((d.selectedXiPlus x + 1) / 2) := by
    simpa only [selectedZ, foldedHalfZ, selectedXiPlus] using hzPos
  linarith [Real.sqrt_pos.1 hsqrt]

theorem selectedX_eq_reconstructedChord
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hxGap : x ∈ d.positiveSpectralHalfGap)
    (hx : x ∈ d.rawClassifiedSet) :
    x = outerChordX d.a (d.selectedAngle x) (d.selectedZ x) := by
  have hrec := x_eq_halfChordScale_mul_foldedHalf d.ha0 hx.1
    (d.selectedXiMinus_ge_negOne_of_classified hx)
    (d.selectedXiPlus_ge_negOne_of_classified hx) hxGap.1
  calc
    x = halfChordScale d.a * d.selectedY x * d.selectedZ x := by
      simpa only [selectedY, selectedZ, selectedXiMinus,
        selectedXiPlus] using hrec
    _ = outerChordX d.a (d.selectedAngle x) (d.selectedZ x) := by
      unfold outerChordX
      rw [d.cos_selectedAngle_of_classified hx]

theorem abs_selectedRoot_eq_reconstructedChordS
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hx : x ∈ d.rawClassifiedSet) :
    |d.selectedRoot x| =
      outerChordS d.a (d.selectedAngle x) (d.selectedZ x) := by
  have hrec := abs_s_eq_halfChordScale_mul_sqrt_foldedHalf_complements
    d.ha0 hx.1 (d.selectedXiMinus_ge_negOne_of_classified hx)
      (d.selectedXiPlus_ge_negOne_of_classified hx)
  simpa only [outerChordS, selectedY, selectedZ, selectedXiMinus,
    selectedXiPlus, d.cos_selectedAngle_of_classified hx] using hrec

theorem selectedRoot_eq_signed_reconstructedChordS
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hxGap : x ∈ d.positiveSpectralHalfGap)
    (hx : x ∈ d.rawClassifiedSet) :
    d.selectedRoot x = (-1 : ℝ) ^ d.m *
      outerChordS d.a (d.selectedAngle x) (d.selectedZ x) := by
  rw [d.selectedRoot_eq_negOnePow_mul_height]
  have habs : |d.selectedRoot x| = d.selectedHeight x := by
    rw [d.selectedRoot_eq_negOnePow_mul_height, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (d.selectedHeight_pos_of_mem_gap hxGap)]
  rw [← habs, d.abs_selectedRoot_eq_reconstructedChordS hx]

private theorem abs_signedChordEquation
    {a theta z : ℝ} {n : ℤ} {j : ℕ}
    (heq : halfTrigRadical a theta * chebyshevU n (Real.cos theta) =
      (-1 : ℝ) ^ j * outerChordRadical a z * chebyshevU n z) :
    outerChordRadical a z * |chebyshevU n z| =
      halfTrigRadical a theta * |chebyshevU n (Real.cos theta)| := by
  have hinner : 0 ≤ halfTrigRadical a theta := by
    unfold halfTrigRadical
    positivity
  have houter : 0 ≤ outerChordRadical a z := by
    unfold outerChordRadical
    positivity
  have habs := congrArg abs heq
  calc
    outerChordRadical a z * |chebyshevU n z| =
        |(-1 : ℝ) ^ j * outerChordRadical a z * chebyshevU n z| := by
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_nonneg houter, one_mul]
    _ = |halfTrigRadical a theta * chebyshevU n (Real.cos theta)| :=
      habs.symm
    _ = halfTrigRadical a theta *
        |chebyshevU n (Real.cos theta)| := by
      rw [abs_mul, abs_of_nonneg hinner]

/-- Reverse folded classification for the central half-gap: the actual
selected root has equal inner and endpoint-side outer lobe levels. -/
theorem chordLobeWeight_selectedZ_eq_selectedY
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hxGap : x ∈ d.positiveSpectralHalfGap)
    (hx : x ∈ d.rawClassifiedSet) :
    chordLobeWeight d.K d.a (d.selectedZ x) =
      chordLobeWeight d.K d.a (d.selectedY x) := by
  have htheta := d.selectedAngle_mem_openHalfLobe_of_classified hx
  have hcos := d.cos_selectedAngle_of_classified hx
  have hzAbs : |d.selectedZ x| ≤ Real.cosh (pathLogParameter d.a) := by
    rw [abs_of_pos (by
      exact (cos_pi_div_nat_nonneg d.two_le_K).trans_lt
        (d.outerLobeMaximizer_spec.1.1.trans hx.2.2.2.1))]
    exact hx.2.2.2.2.le
  have horder : Real.cos (d.selectedAngle x) ^ 2 < d.selectedZ x ^ 2 := by
    rw [hcos]
    have hyz : d.selectedY x < d.selectedZ x :=
      hx.2.2.1.trans_le d.innerEndpoint_le_cos_pi_div |>.trans <|
        d.outerLobeMaximizer_spec.1.1.trans hx.2.2.2.1
    have hz0 : 0 ≤ d.selectedZ x :=
      (cos_pi_div_nat_nonneg d.two_le_K).trans
        (d.outerLobeMaximizer_spec.1.1.le.trans hx.2.2.2.1.le)
    nlinarith [hx.2.1.le]
  have hxRec := d.selectedX_eq_reconstructedChord hxGap hx
  have hsRec := d.selectedRoot_eq_signed_reconstructedChordS hxGap hx
  have hfold : foldEvenSequence d.a x (d.selectedRoot x) d.m = 0 := by
    rw [← signedPencilDet_even_eq_foldEvenSequence]
    exact d.signedPencilDet_selectedRoot_eq_zero_of_mem_gap hxGap
  have hfoldRec :
      foldEvenSequence d.a
        (outerChordX d.a (d.selectedAngle x) (d.selectedZ x))
        ((-1 : ℝ) ^ d.m *
          outerChordS d.a (d.selectedAngle x) (d.selectedZ x)) d.m = 0 := by
    rw [← hxRec, ← hsRec]
    exact hfold
  have hchord :=
    (foldEvenSequence_signed_outerChord_eq_zero_iff d.m d.ha0
      hzAbs horder (negOnePow_sq d.m)).1 hfoldRec
  have habs := abs_signedChordEquation hchord
  have hindex : ((d.K - 1 : ℕ) : ℤ) = 2 * (d.m : ℤ) := by
    exact_mod_cast d.K_sub_one
  simpa only [chordLobeWeight, outerChordRadical, halfTrigRadical,
    hindex, hcos] using habs

/-! ## Clopen continuation on the exact positive half-gap -/

theorem isOpen_classifiedInGap (d : EvenCentralHalfGapData) :
    IsOpen d.classifiedInGap := by
  exact d.isOpen_rawClassifiedSet.preimage continuous_subtype_val

theorem classifiedInGap_nonempty (d : EvenCentralHalfGapData) :
    d.classifiedInGap.Nonempty := by
  obtain ⟨x, hxGap, hxClass⟩ := d.classifiedSet_nonempty
  exact ⟨⟨x, hxGap⟩, hxClass⟩

private theorem mem_of_mem_closure_classifiedGapImage
    (d : EvenCentralHalfGapData) {T : Set ℝ} (hT : IsClosed T)
    (hsub : d.classifiedGapImage ⊆ T)
    {p : d.GapPoint} (hp : (p : ℝ) ∈ closure d.classifiedGapImage) :
    (p : ℝ) ∈ T :=
  closure_minimal hsub hT hp

theorem selectedDiscriminant_nonneg_of_mem_closure
    (d : EvenCentralHalfGapData) {p : d.GapPoint}
    (hp : (p : ℝ) ∈ closure d.classifiedGapImage) :
    0 ≤ d.selectedDiscriminant p := by
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_le continuous_const d.continuous_selectedDiscriminant) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  exact hq.1.le

theorem selectedY_nonneg_of_mem_closure
    (d : EvenCentralHalfGapData) {p : d.GapPoint}
    (hp : (p : ℝ) ∈ closure d.classifiedGapImage) :
    0 ≤ d.selectedY p := by
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_le continuous_const d.continuous_selectedY) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  exact hq.2.1.le

theorem selectedY_le_innerEndpoint_of_mem_closure
    (d : EvenCentralHalfGapData) {p : d.GapPoint}
    (hp : (p : ℝ) ∈ closure d.classifiedGapImage) :
    d.selectedY p ≤ d.innerEndpoint := by
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_le d.continuous_selectedY continuous_const) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  exact hq.2.2.1.le

theorem outerLobeMaximizer_le_selectedZ_of_mem_closure
    (d : EvenCentralHalfGapData) {p : d.GapPoint}
    (hp : (p : ℝ) ∈ closure d.classifiedGapImage) :
    d.outerLobeMaximizer ≤ d.selectedZ p := by
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_le continuous_const d.continuous_selectedZ) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  exact hq.2.2.2.1.le

theorem selectedZ_le_cosh_of_mem_closure
    (d : EvenCentralHalfGapData) {p : d.GapPoint}
    (hp : (p : ℝ) ∈ closure d.classifiedGapImage) :
    d.selectedZ p ≤ Real.cosh (pathLogParameter d.a) := by
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_le d.continuous_selectedZ continuous_const) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  exact hq.2.2.2.2.le

theorem selectedXiMinus_ge_negOne_of_mem_closure
    (d : EvenCentralHalfGapData) {p : d.GapPoint}
    (hp : (p : ℝ) ∈ closure d.classifiedGapImage) :
    -1 ≤ d.selectedXiMinus p := by
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_le continuous_const d.continuous_selectedXiMinus) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  exact d.selectedXiMinus_ge_negOne_of_classified hq

theorem selectedXiPlus_ge_negOne_of_mem_closure
    (d : EvenCentralHalfGapData) {p : d.GapPoint}
    (hp : (p : ℝ) ∈ closure d.classifiedGapImage) :
    -1 ≤ d.selectedXiPlus p := by
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_le continuous_const d.continuous_selectedXiPlus) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  exact d.selectedXiPlus_ge_negOne_of_classified hq

theorem selected_lobeLevel_eq_of_mem_closure
    (d : EvenCentralHalfGapData) {p : d.GapPoint}
    (hp : (p : ℝ) ∈ closure d.classifiedGapImage) :
    chordLobeWeight d.K d.a (d.selectedZ p) =
      chordLobeWeight d.K d.a (d.selectedY p) := by
  have hz : Continuous (fun x : ℝ ↦
      chordLobeWeight d.K d.a (d.selectedZ x)) :=
    (continuous_chordLobeWeight d.K d.a).comp' d.continuous_selectedZ
  have hy : Continuous (fun x : ℝ ↦
      chordLobeWeight d.K d.a (d.selectedY x)) :=
    (continuous_chordLobeWeight d.K d.a).comp' d.continuous_selectedY
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_eq hz hy) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  exact d.chordLobeWeight_selectedZ_eq_selectedY q.property hq

private theorem selectedY_lt_selectedZ_of_weak_bounds
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hy : d.selectedY x ≤ d.innerEndpoint)
    (hz : d.outerLobeMaximizer ≤ d.selectedZ x) :
    d.selectedY x < d.selectedZ x := by
  exact lt_of_le_of_lt
    (le_trans hy d.innerEndpoint_le_cos_pi_div)
    (d.outerLobeMaximizer_spec.1.1.trans_le hz)

theorem selectedDiscriminant_pos_of_mem_closure
    (d : EvenCentralHalfGapData) {p : d.GapPoint}
    (hp : (p : ℝ) ∈ closure d.classifiedGapImage) :
    0 < d.selectedDiscriminant p := by
  have hnonneg := d.selectedDiscriminant_nonneg_of_mem_closure hp
  by_contra hnot
  have hzero : foldDiscriminant d.a p (d.selectedRoot p) = 0 := by
    simpa only [selectedDiscriminant] using
      le_antisymm (le_of_not_gt hnot) hnonneg
  have hxi := foldXiPlus_eq_foldXiMinus_of_discriminant_eq_zero hzero
  have hyz : d.selectedY p = d.selectedZ p := by
    unfold selectedY selectedZ foldedHalfY foldedHalfZ
    rw [hxi]
  exact (ne_of_lt <| d.selectedY_lt_selectedZ_of_weak_bounds
    (d.selectedY_le_innerEndpoint_of_mem_closure hp)
    (d.outerLobeMaximizer_le_selectedZ_of_mem_closure hp)) hyz

theorem selectedZ_ne_cosh_of_mem_closure
    (d : EvenCentralHalfGapData) {p : d.GapPoint}
    (hp : (p : ℝ) ∈ closure d.classifiedGapImage) :
    d.selectedZ p ≠ Real.cosh (pathLogParameter d.a) := by
  intro hzCosh
  have hrec := abs_s_eq_halfChordScale_mul_sqrt_foldedHalf_complements
    d.ha0 (d.selectedDiscriminant_pos_of_mem_closure hp)
    (d.selectedXiMinus_ge_negOne_of_mem_closure hp)
    (d.selectedXiPlus_ge_negOne_of_mem_closure hp)
  have habs : |d.selectedRoot p| = halfChordScale d.a * Real.sqrt
      ((Real.cosh (pathLogParameter d.a) ^ 2 - d.selectedY p ^ 2) *
        (Real.cosh (pathLogParameter d.a) ^ 2 - d.selectedZ p ^ 2)) := by
    simpa only [selectedY, selectedZ, selectedXiMinus,
      selectedXiPlus] using hrec
  rw [hzCosh, sub_self, mul_zero, Real.sqrt_zero, mul_zero] at habs
  exact d.selectedRoot_ne_zero_of_mem_gap p.property (abs_eq_zero.mp habs)

theorem selectedY_ne_innerEndpoint_of_mem_closure
    (d : EvenCentralHalfGapData) {p : d.GapPoint}
    (hp : (p : ℝ) ∈ closure d.classifiedGapImage) :
    d.selectedY p ≠ d.innerEndpoint := by
  intro hyNode
  have hnode : chordLobeWeight d.K d.a d.innerEndpoint = 0 := by
    rw [d.innerEndpoint_eq_cos_angleLower, chordLobeWeight_cos]
    simpa only [angleLower] using chordPhi_nodal (K := d.K) (k := d.m)
      d.two_le_K d.hm (by
        have hm := d.hm
        unfold K
        omega) d.a
  have hanti := outerChordLobeWeight_strictAntiOn_closedEndpointSide
    d.K d.two_le_K d.a d.ha0 d.ha1 d.outerLobeMaximizer_spec.1
      d.outerLobeMaximizer_spec.2
  have hzEq : d.selectedZ p = Real.cosh (pathLogParameter d.a) := by
    apply hanti.injOn
      ⟨d.outerLobeMaximizer_le_selectedZ_of_mem_closure hp,
        d.selectedZ_le_cosh_of_mem_closure hp⟩
      ⟨d.outerLobeMaximizer_spec.1.2.le, le_rfl⟩
    calc
      chordLobeWeight d.K d.a (d.selectedZ p) =
          chordLobeWeight d.K d.a (d.selectedY p) :=
        d.selected_lobeLevel_eq_of_mem_closure hp
      _ = 0 := by rw [hyNode, hnode]
      _ = chordLobeWeight d.K d.a
          (Real.cosh (pathLogParameter d.a)) := by
        rw [chordLobeWeight_cosh_endpoint]
  exact d.selectedZ_ne_cosh_of_mem_closure hp hzEq

theorem selectedY_ne_zero_of_mem_closure
    (d : EvenCentralHalfGapData) {p : d.GapPoint}
    (hp : (p : ℝ) ∈ closure d.classifiedGapImage) :
    d.selectedY p ≠ 0 := by
  intro hyZero
  have hxRec := x_eq_halfChordScale_mul_foldedHalf d.ha0
    (d.selectedDiscriminant_pos_of_mem_closure hp)
    (d.selectedXiMinus_ge_negOne_of_mem_closure hp)
    (d.selectedXiPlus_ge_negOne_of_mem_closure hp) p.property.1
  have hxRec' : (p : ℝ) =
      halfChordScale d.a * d.selectedY p * d.selectedZ p := by
    simpa only [selectedY, selectedZ, selectedXiMinus,
      selectedXiPlus] using hxRec
  rw [hyZero, mul_zero, zero_mul] at hxRec'
  exact p.property.1.ne' hxRec'

theorem selectedZ_ne_outerLobeMaximizer_of_mem_closure
    (d : EvenCentralHalfGapData) {p : d.GapPoint}
    (hp : (p : ℝ) ∈ closure d.classifiedGapImage) :
    d.selectedZ p ≠ d.outerLobeMaximizer := by
  intro hzMax
  have hy0 : 0 < d.selectedY p :=
    lt_of_le_of_ne (d.selectedY_nonneg_of_mem_closure hp)
      (d.selectedY_ne_zero_of_mem_closure hp).symm
  have hyUpper : d.selectedY p < d.innerEndpoint :=
    lt_of_le_of_ne (d.selectedY_le_innerEndpoint_of_mem_closure hp)
      (d.selectedY_ne_innerEndpoint_of_mem_closure hp)
  have hyMem : d.selectedY p ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith, hyUpper.le.trans (Real.cos_le_one d.angleLower)⟩
  let theta := Real.arccos (d.selectedY p)
  have hcos : Real.cos theta = d.selectedY p :=
    Real.cos_arccos hyMem.1 hyMem.2
  have hthetaLower : d.angleLower < theta := by
    have h := Real.arccos_lt_arccos hyMem.1 hyUpper
      (Real.cos_le_one d.angleLower)
    rw [d.innerEndpoint_eq_cos_angleLower] at h
    rw [Real.arccos_cos d.angleLower_pos.le
      (d.angleLower_lt_pi_div_two.le.trans
        (by linarith [Real.pi_pos]))] at h
    exact h
  have hthetaHalf : theta < Real.pi / 2 := by
    have h := Real.arccos_lt_arccos (by norm_num : (-1 : ℝ) ≤ 0)
      hy0 hyMem.2
    simpa only [Real.arccos_zero] using h
  have hstrict : chordPhi d.K d.a theta <
      chordLobeWeight d.K d.a d.outerLobeMaximizer :=
    chordPhi_inner_lt_outerLobeMaximum d.two_le_K d.hm d.ha0 d.ha1
      hthetaLower (hthetaHalf.trans d.pi_div_two_lt_nextNodeAngle)
      hthetaHalf.le d.outerLobeMaximizer_spec.2
  have hlevel : chordLobeWeight d.K d.a (d.selectedY p) =
      chordPhi d.K d.a theta := by
    rw [← hcos, chordLobeWeight_cos]
  have heq : chordLobeWeight d.K d.a d.outerLobeMaximizer =
      chordPhi d.K d.a theta := by
    calc
      chordLobeWeight d.K d.a d.outerLobeMaximizer =
          chordLobeWeight d.K d.a (d.selectedZ p) := by rw [hzMax]
      _ = chordLobeWeight d.K d.a (d.selectedY p) :=
        d.selected_lobeLevel_eq_of_mem_closure hp
      _ = chordPhi d.K d.a theta := hlevel
  exact (ne_of_lt hstrict) heq.symm

theorem isClosed_classifiedInGap (d : EvenCentralHalfGapData) :
    IsClosed d.classifiedInGap := by
  rw [Topology.IsInducing.subtypeVal.isClosed_iff']
  intro p hp
  exact ⟨d.selectedDiscriminant_pos_of_mem_closure hp,
    lt_of_le_of_ne (d.selectedY_nonneg_of_mem_closure hp)
      (d.selectedY_ne_zero_of_mem_closure hp).symm,
    lt_of_le_of_ne (d.selectedY_le_innerEndpoint_of_mem_closure hp)
      (d.selectedY_ne_innerEndpoint_of_mem_closure hp),
    lt_of_le_of_ne (d.outerLobeMaximizer_le_selectedZ_of_mem_closure hp)
      (d.selectedZ_ne_outerLobeMaximizer_of_mem_closure hp).symm,
    lt_of_le_of_ne (d.selectedZ_le_cosh_of_mem_closure hp)
      (d.selectedZ_ne_cosh_of_mem_closure hp)⟩

theorem isClopen_classifiedInGap (d : EvenCentralHalfGapData) :
    IsClopen d.classifiedInGap :=
  ⟨d.isClosed_classifiedInGap, d.isOpen_classifiedInGap⟩

/-- Every point of the positive central half-gap remains on the selected
endpoint-side folded sheet. -/
theorem classifiedInGap_eq_univ (d : EvenCentralHalfGapData) :
    d.classifiedInGap = univ := by
  letI : PreconnectedSpace d.GapPoint :=
    Subtype.preconnectedSpace (by
      unfold positiveSpectralHalfGap
      exact isPreconnected_Ioo)
  have hsub : (univ : Set d.GapPoint) ⊆ d.classifiedInGap :=
    isPreconnected_univ.subset_isClopen d.isClopen_classifiedInGap (by
      obtain ⟨p, hp⟩ := d.classifiedInGap_nonempty
      exact ⟨p, trivial, hp⟩)
  exact eq_univ_of_univ_subset hsub

theorem positiveSpectralHalfGap_subset_rawClassifiedSet
    (d : EvenCentralHalfGapData) :
    d.positiveSpectralHalfGap ⊆ d.rawClassifiedSet := by
  intro x hx
  have hp : (⟨x, hx⟩ : d.GapPoint) ∈ d.classifiedInGap := by
    rw [d.classifiedInGap_eq_univ]
    trivial
  exact hp

/-! ## Closure at the centre and endpoint-side identification of `z₀` -/

theorem selectedRoot_zero_sq_eq_centralHeight_sq
    (d : EvenCentralHalfGapData) :
    d.selectedRoot 0 ^ 2 = centralBidiagonalHeight d.m d.a ^ 2 := by
  rw [d.selectedRoot_eq_negOnePow_mul_height, mul_pow,
    negOnePow_sq, one_mul]
  unfold selectedHeight
  rw [realGapValue_even_zero_eq_centralBidiagonalHeight
    d.m (by
      have hm := d.hm
      omega) d.a d.ha0 d.ha1]

theorem centralHeight_sq_eq_rho
    (d : EvenCentralHalfGapData) :
    centralBidiagonalHeight d.m d.a ^ 2 =
      1 + d.a ^ 2 - 2 * d.a * centralRho d.m d.a := by
  simpa only [centralRhoLambda] using
    centralBidiagonalHeight_sq_eq_rhoLambda
      d.m d.hm d.a d.ha0 d.ha1

theorem foldC0_selectedRoot_zero
    (d : EvenCentralHalfGapData) :
    foldC0 d.a 0 (d.selectedRoot 0) =
      2 * d.a * (centralRho d.m d.a - 1) := by
  unfold foldC0
  rw [d.selectedRoot_zero_sq_eq_centralHeight_sq,
    d.centralHeight_sq_eq_rho]
  ring

theorem centralEndpointFactor_selectedRoot_zero
    (d : EvenCentralHalfGapData) :
    (1 + d.a) ^ 2 - d.selectedRoot 0 ^ 2 =
      2 * d.a * (1 + centralRho d.m d.a) := by
  rw [d.selectedRoot_zero_sq_eq_centralHeight_sq,
    d.centralHeight_sq_eq_rho]
  ring

theorem centralEndpointFactor_selectedRoot_zero_pos
    (d : EvenCentralHalfGapData) :
    0 < (1 + d.a) ^ 2 - d.selectedRoot 0 ^ 2 := by
  rw [d.centralEndpointFactor_selectedRoot_zero]
  exact mul_pos (mul_pos (by norm_num) d.ha0) (by
    have hρ := centralRho_pos d.m d.hm d.a d.ha0 d.ha1
    linarith)

theorem foldDiscriminant_selectedRoot_zero
    (d : EvenCentralHalfGapData) :
    foldDiscriminant d.a 0 (d.selectedRoot 0) =
      (2 * d.a * (1 + centralRho d.m d.a)) ^ 2 := by
  unfold foldDiscriminant
  norm_num
  rw [d.centralEndpointFactor_selectedRoot_zero]
  ring

theorem sqrt_foldDiscriminant_selectedRoot_zero
    (d : EvenCentralHalfGapData) :
    Real.sqrt (foldDiscriminant d.a 0 (d.selectedRoot 0)) =
      2 * d.a * (1 + centralRho d.m d.a) := by
  rw [d.foldDiscriminant_selectedRoot_zero]
  exact Real.sqrt_sq (by
    have hρ := centralRho_pos d.m d.hm d.a d.ha0 d.ha1
    have hsum : 0 ≤ 1 + centralRho d.m d.a := by linarith
    exact mul_nonneg (mul_nonneg (by norm_num) d.ha0.le) hsum)

@[simp] theorem selectedXiMinus_zero (d : EvenCentralHalfGapData) :
    d.selectedXiMinus 0 = -1 := by
  unfold selectedXiMinus foldXiMinus
  rw [d.foldC0_selectedRoot_zero,
    d.sqrt_foldDiscriminant_selectedRoot_zero]
  field_simp [d.ha0.ne']
  ring

@[simp] theorem selectedXiPlus_zero (d : EvenCentralHalfGapData) :
    d.selectedXiPlus 0 = centralRho d.m d.a := by
  unfold selectedXiPlus foldXiPlus
  rw [d.foldC0_selectedRoot_zero,
    d.sqrt_foldDiscriminant_selectedRoot_zero]
  field_simp [d.ha0.ne']
  ring

@[simp] theorem selectedY_zero (d : EvenCentralHalfGapData) :
    d.selectedY 0 = 0 := by
  unfold selectedY foldedHalfY
  change Real.sqrt ((d.selectedXiMinus 0 + 1) / 2) = 0
  rw [d.selectedXiMinus_zero]
  norm_num

@[simp] theorem selectedZ_zero (d : EvenCentralHalfGapData) :
    d.selectedZ 0 = centralOuterZ0 d.m d.a := by
  unfold selectedZ foldedHalfZ centralOuterZ0
  change Real.sqrt ((d.selectedXiPlus 0 + 1) / 2) = _
  rw [d.selectedXiPlus_zero]
  ring_nf

/-- Continuity from positive `x` proves the missing endpoint-side inequality
at `x=0`.  No endpoint-side premise about `z₀` is used. -/
theorem outerLobeMaximizer_le_centralOuterZ0
    (d : EvenCentralHalfGapData) :
    d.outerLobeMaximizer ≤ centralOuterZ0 d.m d.a := by
  let T : Set ℝ := {x | d.outerLobeMaximizer ≤ d.selectedZ x}
  have hT : IsClosed T :=
    isClosed_le continuous_const d.continuous_selectedZ
  have hsub : d.positiveSpectralHalfGap ⊆ T := by
    intro x hx
    exact (d.positiveSpectralHalfGap_subset_rawClassifiedSet hx).2.2.2.1.le
  have hzero : (0 : ℝ) ∈ closure d.positiveSpectralHalfGap := by
    unfold positiveSpectralHalfGap
    rw [closure_Ioo d.positiveEndpoint_pos.ne]
    exact ⟨le_rfl, d.positiveEndpoint_pos.le⟩
  have : (0 : ℝ) ∈ T := closure_minimal hsub hT hzero
  simpa only [T, Set.mem_setOf_eq, d.selectedZ_zero] using this

theorem centralOuterZ0_mem_endpointSide
    (d : EvenCentralHalfGapData) :
    centralOuterZ0 d.m d.a ∈
      Icc d.outerLobeMaximizer (Real.cosh (pathLogParameter d.a)) := by
  exact ⟨d.outerLobeMaximizer_le_centralOuterZ0,
    (centralOuterZ0_lt_cosh d.m d.hm d.a d.ha0 d.ha1).le⟩

/-- This is the precise endpoint-side conclusion asserted at lines
1472--1474: the canonical endpoint-side outer solution at the central
level is `z₀`. -/
theorem chordZ_rightAngle_eq_centralOuterZ0
    (d : EvenCentralHalfGapData) :
    d.chordZ d.rightAngle = centralOuterZ0 d.m d.a := by
  have hanti := outerChordLobeWeight_strictAntiOn_closedEndpointSide
    d.K d.two_le_K d.a d.ha0 d.ha1 d.outerLobeMaximizer_spec.1
      d.outerLobeMaximizer_spec.2
  apply hanti.injOn (d.chordZ_mem d.rightAngle)
    d.centralOuterZ0_mem_endpointSide
  calc
    chordLobeWeight d.K d.a (d.chordZ d.rightAngle) =
        chordPhi d.K d.a d.rightAngle :=
      d.chordLobeWeight_chordZ d.rightAngle
    _ = chordLobeWeight d.K d.a 0 := by
      rw [← chordLobeWeight_cos]
      simp only [rightAngle, Real.cos_pi_div_two]
    _ = chordLobeWeight d.K d.a (centralOuterZ0 d.m d.a) := by
      rw [chordLobeWeight_evenCentral_zero d]
      simpa only [d.K_eq] using
        (chordLobeWeight_centralOuterZ0
          d.m d.hm d.a d.ha0 d.ha1).symm

/-- Away from the centre, strict central-lobe concavity and endpoint-side
strict antitonicity force the selected outer coordinate beyond `z₀`. -/
theorem centralOuterZ0_lt_selectedZ_of_mem_gap
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hx : x ∈ d.positiveSpectralHalfGap) :
    centralOuterZ0 d.m d.a < d.selectedZ x := by
  have hclass := d.positiveSpectralHalfGap_subset_rawClassifiedSet hx
  have hlevel := d.chordLobeWeight_selectedZ_eq_selectedY hx hclass
  have hinner := evenCentralInnerLobe_lt_center d
    hclass.2.1 hclass.2.2.1
  have hweight : chordLobeWeight d.K d.a (d.selectedZ x) <
      chordLobeWeight d.K d.a (centralOuterZ0 d.m d.a) := by
    calc
      chordLobeWeight d.K d.a (d.selectedZ x) =
          chordLobeWeight d.K d.a (d.selectedY x) := hlevel
      _ < chordLobeWeight d.K d.a 0 := hinner
      _ = chordLobeWeight d.K d.a (centralOuterZ0 d.m d.a) := by
        rw [chordLobeWeight_evenCentral_zero d]
        simpa only [d.K_eq] using
          (chordLobeWeight_centralOuterZ0
            d.m d.hm d.a d.ha0 d.ha1).symm
  have hanti := outerChordLobeWeight_strictAntiOn_closedEndpointSide
    d.K d.two_le_K d.a d.ha0 d.ha1 d.outerLobeMaximizer_spec.1
      d.outerLobeMaximizer_spec.2
  have hzMem : d.selectedZ x ∈
      Icc d.outerLobeMaximizer (Real.cosh (pathLogParameter d.a)) :=
    ⟨hclass.2.2.2.1.le, hclass.2.2.2.2.le⟩
  by_contra hnot
  have hle : d.selectedZ x ≤ centralOuterZ0 d.m d.a := le_of_not_gt hnot
  rcases hle.eq_or_lt with heq | hlt
  · rw [heq] at hweight
    exact (lt_irrefl _) hweight
  · have hreverse := hanti hzMem d.centralOuterZ0_mem_endpointSide hlt
    exact (not_lt_of_ge hweight.le) hreverse

/-! ## The strict actual-height comparison -/

theorem selectedHeight_sq_eq_evenCentralHalfChordHeightSq
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hx : x ∈ d.positiveSpectralHalfGap) :
    d.selectedHeight x ^ 2 = evenCentralHalfChordHeightSq d.a
      (d.selectedY x) (d.selectedZ x) := by
  have hclass := d.positiveSpectralHalfGap_subset_rawClassifiedSet hx
  have hrec := s_sq_eq_halfChordScale_sq_mul_foldedHalf_complements
    d.ha0 hclass.1
    (d.selectedXiMinus_ge_negOne_of_classified hclass)
    (d.selectedXiPlus_ge_negOne_of_classified hclass)
  have hrootSq : d.selectedRoot x ^ 2 = d.selectedHeight x ^ 2 := by
    rw [d.selectedRoot_eq_negOnePow_mul_height, mul_pow,
      negOnePow_sq, one_mul]
  rw [hrootSq] at hrec
  rw [evenCentralHalfChordHeightSq_eq_scale d.ha0]
  simpa only [selectedY, selectedZ, selectedXiMinus,
    selectedXiPlus] using hrec

/-- On the positive half of the central gap, every noncentral point has
actual least singular value strictly below `c_m`. -/
theorem selectedHeight_lt_centralBidiagonalHeight_of_mem_gap
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hx : x ∈ d.positiveSpectralHalfGap) :
    d.selectedHeight x < centralBidiagonalHeight d.m d.a := by
  let c := Real.cosh (pathLogParameter d.a)
  let y := d.selectedY x
  let z := d.selectedZ x
  let z0 := centralOuterZ0 d.m d.a
  have hclass := d.positiveSpectralHalfGap_subset_rawClassifiedSet hx
  have hcOne : 1 < c := by
    exact Real.one_lt_cosh.mpr (pathLogParameter_pos d.ha0 d.ha1).ne'
  have hyc : y < c :=
    hclass.2.2.1.trans_le (Real.cos_le_one d.angleLower) |>.trans hcOne
  have hy0 : 0 < y := hclass.2.1
  have hzc : z < c := hclass.2.2.2.2
  have hz0 : 0 ≤ z :=
    (cos_pi_div_nat_nonneg d.two_le_K).trans
      (d.outerLobeMaximizer_spec.1.1.le.trans hclass.2.2.2.1.le)
  have hz00 : 0 < z0 :=
    centralOuterZ0_pos d.m d.hm d.a d.ha0 d.ha1
  have hz0c : z0 < c :=
    centralOuterZ0_lt_cosh d.m d.hm d.a d.ha0 d.ha1
  have hz0z : z0 < z := d.centralOuterZ0_lt_selectedZ_of_mem_gap hx
  have hApos : 0 < c ^ 2 - y ^ 2 := by nlinarith
  have hAlt : c ^ 2 - y ^ 2 < c ^ 2 := by nlinarith
  have hBpos : 0 < c ^ 2 - z ^ 2 := by nlinarith
  have hBlt : c ^ 2 - z ^ 2 < c ^ 2 - z0 ^ 2 := by nlinarith
  have hprod :
      (c ^ 2 - y ^ 2) * (c ^ 2 - z ^ 2) <
        c ^ 2 * (c ^ 2 - z0 ^ 2) := by
    calc
      (c ^ 2 - y ^ 2) * (c ^ 2 - z ^ 2) <
          c ^ 2 * (c ^ 2 - z ^ 2) :=
        mul_lt_mul_of_pos_right hAlt hBpos
      _ < c ^ 2 * (c ^ 2 - z0 ^ 2) :=
        mul_lt_mul_of_pos_left hBlt (sq_pos_of_pos (by
          dsimp [c]
          exact Real.cosh_pos _))
  have hcpos : 0 < c := by
    dsimp [c]
    exact Real.cosh_pos _
  have hcoef : 0 < 4 * d.a / c ^ 2 :=
    div_pos (mul_pos (by norm_num) d.ha0) (sq_pos_of_pos hcpos)
  have hsquare : d.selectedHeight x ^ 2 <
      centralBidiagonalHeight d.m d.a ^ 2 := by
    calc
      d.selectedHeight x ^ 2 =
          (4 * d.a / c ^ 2) * (c ^ 2 - y ^ 2) *
            (c ^ 2 - z ^ 2) := by
        rw [d.selectedHeight_sq_eq_evenCentralHalfChordHeightSq hx]
        rfl
      _ = (4 * d.a / c ^ 2) *
          ((c ^ 2 - y ^ 2) * (c ^ 2 - z ^ 2)) := by ring
      _ < (4 * d.a / c ^ 2) *
          (c ^ 2 * (c ^ 2 - z0 ^ 2)) :=
        mul_lt_mul_of_pos_left hprod hcoef
      _ = 4 * d.a * (c ^ 2 - z0 ^ 2) := by
        field_simp [(Real.cosh_pos (pathLogParameter d.a)).ne']
      _ = centralBidiagonalHeight d.m d.a ^ 2 := by
        exact centralOuterZ0_radical_eq_height_sq
          d.m d.hm d.a d.ha0 d.ha1
  have hheightNonneg : 0 ≤ d.selectedHeight x := by
    unfold selectedHeight realGapValue pseudospectralHeight
    exact leastSingularValue_nonneg _
  exact (sq_lt_sq₀
    hheightNonneg
    (centralBidiagonalHeight_pos d.m d.hm d.a d.ha0).le).mp hsquare

/-- The source's strict positive-half comparison, stated directly for the
actual complex Euclidean least singular value. -/
theorem realGapValue_lt_centralBidiagonalHeight_of_mem_positiveHalfGap
    (d : EvenCentralHalfGapData) {x : ℝ}
    (hx : x ∈ d.positiveSpectralHalfGap) :
    realGapValue (2 * d.m) d.a x < centralBidiagonalHeight d.m d.a := by
  exact d.selectedHeight_lt_centralBidiagonalHeight_of_mem_gap hx

/-- The full open central spectral gap. -/
def centralSpectralGap (d : EvenCentralHalfGapData) : Set ℝ :=
  Ioo (-d.positiveEndpoint) d.positiveEndpoint

/-- Reflection supplies the negative half.  Thus the actual central-gap
height is exactly `c_m`, and it is attained only at `x=0`. -/
theorem centralGap_height_eq_and_unique
    (d : EvenCentralHalfGapData) :
    realGapValue (2 * d.m) d.a 0 = centralBidiagonalHeight d.m d.a ∧
      ∀ x ∈ d.centralSpectralGap,
        realGapValue (2 * d.m) d.a x ≤ centralBidiagonalHeight d.m d.a ∧
        (realGapValue (2 * d.m) d.a x =
          centralBidiagonalHeight d.m d.a ↔ x = 0) := by
  have hzero := realGapValue_even_zero_eq_centralBidiagonalHeight
    d.m (by
      have hm := d.hm
      omega) d.a d.ha0 d.ha1
  refine ⟨hzero, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    exact ⟨hzero.le, iff_of_true hzero rfl⟩
  · by_cases hxpos : 0 < x
    · have hxHalf : x ∈ d.positiveSpectralHalfGap := ⟨hxpos, hx.2⟩
      have hlt :=
        d.realGapValue_lt_centralBidiagonalHeight_of_mem_positiveHalfGap
          hxHalf
      exact ⟨hlt.le, ⟨fun heq ↦ (ne_of_lt hlt heq).elim,
        fun h ↦ (hx0 h).elim⟩⟩
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx0
      have hnegHalf : -x ∈ d.positiveSpectralHalfGap := by
        exact ⟨neg_pos.mpr hxneg, by linarith [hx.1]⟩
      have hltNeg :=
        d.realGapValue_lt_centralBidiagonalHeight_of_mem_positiveHalfGap
          hnegHalf
      have hlt : realGapValue (2 * d.m) d.a x <
          centralBidiagonalHeight d.m d.a := by
        simpa only [realGapValue_neg, neg_neg] using hltNeg
      exact ⟨hlt.le, ⟨fun heq ↦ (ne_of_lt hlt heq).elim,
        fun h ↦ (hx0 h).elim⟩⟩

end EvenCentralHalfGapData

end

end ConnectedPseudospectrum
