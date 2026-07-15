import ConnectedPseudospectrum.MiddleBranchReverseClassification
import Mathlib.Topology.Connected.Clopen

/-!
# Global continuation of the noncentral middle branch

The selected middle branch is already classified on a nonempty open part of
each positive-half spectral gap.  This module proves that this classified
part is also relatively closed.  At a relative closure point, continuity
first gives weak coordinate inequalities and the exact lobe-level identity.
The four possible boundary losses are then excluded: folded collision, either
inner nodal endpoint, the outer-lobe maximizer, and the radical endpoint.
Preconnectedness of the open interval propagates classification to the whole
gap.  No monotonicity of the chord abscissa is used.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- Points of the exact positive-half spectral gap, with the relative
topology inherited from the real axis. -/
abbrev PositiveHalfGapPoint (d : PositiveHalfGap) :=
  {x : ℝ // x ∈ positiveHalfSpectralGap d}

/-- The classified subset of the exact gap, regarded in the relative
topology. -/
def middleBranchClassifiedInGap
    (d : PositiveHalfGap) : Set (PositiveHalfGapPoint d) :=
  {p | (p : ℝ) ∈ middleBranchRawClassifiedSet d}

/-- Ambient real image of the relatively classified subset. -/
def middleBranchClassifiedGapImage
    (d : PositiveHalfGap) : Set ℝ :=
  ((↑) : PositiveHalfGapPoint d → ℝ) ''
    middleBranchClassifiedInGap d

/-- The smaller actual folded root evaluated along the selected middle
branch. -/
def selectedMiddleXiMinus (d : PositiveHalfGap) (x : ℝ) : ℝ :=
  foldXiMinus d.a x (selectedMiddleRoot d x)

/-- The larger actual folded root evaluated along the selected middle
branch. -/
def selectedMiddleXiPlus (d : PositiveHalfGap) (x : ℝ) : ℝ :=
  foldXiPlus d.a x (selectedMiddleRoot d x)

theorem continuous_selectedMiddleXiMinus (d : PositiveHalfGap) :
    Continuous (selectedMiddleXiMinus d) := by
  have hroot := continuous_selectedMiddleRoot d
  have hconstant : Continuous (fun _ : ℝ => (1 - d.a) ^ 2) :=
    continuous_const
  have hc0 : Continuous
      (fun x : ℝ => foldC0 d.a x (selectedMiddleRoot d x)) := by
    unfold foldC0
    exact ((continuous_id.pow 2).add hconstant).sub (hroot.pow 2)
  unfold selectedMiddleXiMinus foldXiMinus
  exact (hc0.sub (continuous_selectedMiddleDiscriminant d).sqrt).div_const
    (4 * d.a)

theorem continuous_selectedMiddleXiPlus (d : PositiveHalfGap) :
    Continuous (selectedMiddleXiPlus d) := by
  have hroot := continuous_selectedMiddleRoot d
  have hconstant : Continuous (fun _ : ℝ => (1 - d.a) ^ 2) :=
    continuous_const
  have hc0 : Continuous
      (fun x : ℝ => foldC0 d.a x (selectedMiddleRoot d x)) := by
    unfold foldC0
    exact ((continuous_id.pow 2).add hconstant).sub (hroot.pow 2)
  unfold selectedMiddleXiPlus foldXiPlus
  exact (hc0.add (continuous_selectedMiddleDiscriminant d).sqrt).div_const
    (4 * d.a)

theorem isOpen_middleBranchClassifiedInGap (d : PositiveHalfGap) :
    IsOpen (middleBranchClassifiedInGap d) := by
  exact (isOpen_middleBranchRawClassifiedSet d).preimage
    continuous_subtype_val

theorem middleBranchClassifiedInGap_nonempty (d : PositiveHalfGap) :
    (middleBranchClassifiedInGap d).Nonempty := by
  obtain ⟨x, hxGap, hclass⟩ := middleBranchClassifiedSet_nonempty d
  exact ⟨⟨x, hxGap⟩, hclass⟩

private theorem mem_of_mem_closure_classifiedGapImage
    (d : PositiveHalfGap) {T : Set ℝ} (hT : IsClosed T)
    (hsub : middleBranchClassifiedGapImage d ⊆ T)
    {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d)) :
    (p : ℝ) ∈ T :=
  closure_minimal hsub hT hp

theorem selectedMiddleDiscriminant_nonneg_of_mem_closure
    (d : PositiveHalfGap) {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d)) :
    0 ≤ selectedMiddleDiscriminant d p := by
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_le continuous_const (continuous_selectedMiddleDiscriminant d))
    ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  change
    0 < selectedMiddleDiscriminant d q ∧
      Real.cos d.angleUpper < selectedMiddleY d q ∧
      selectedMiddleY d q < Real.cos d.angleLower ∧
      outerLobeMaximizer d < selectedMiddleZ d q ∧
      selectedMiddleZ d q < Real.cosh (pathLogParameter d.a) at hq
  exact hq.1.le

theorem cos_angleUpper_le_selectedMiddleY_of_mem_closure
    (d : PositiveHalfGap) {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d)) :
    Real.cos d.angleUpper ≤ selectedMiddleY d p := by
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_le continuous_const (continuous_selectedMiddleY d)) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  change
    0 < selectedMiddleDiscriminant d q ∧
      Real.cos d.angleUpper < selectedMiddleY d q ∧
      selectedMiddleY d q < Real.cos d.angleLower ∧
      outerLobeMaximizer d < selectedMiddleZ d q ∧
      selectedMiddleZ d q < Real.cosh (pathLogParameter d.a) at hq
  exact hq.2.1.le

theorem selectedMiddleY_le_cos_angleLower_of_mem_closure
    (d : PositiveHalfGap) {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d)) :
    selectedMiddleY d p ≤ Real.cos d.angleLower := by
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_le (continuous_selectedMiddleY d) continuous_const) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  change
    0 < selectedMiddleDiscriminant d q ∧
      Real.cos d.angleUpper < selectedMiddleY d q ∧
      selectedMiddleY d q < Real.cos d.angleLower ∧
      outerLobeMaximizer d < selectedMiddleZ d q ∧
      selectedMiddleZ d q < Real.cosh (pathLogParameter d.a) at hq
  exact hq.2.2.1.le

theorem outerLobeMaximizer_le_selectedMiddleZ_of_mem_closure
    (d : PositiveHalfGap) {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d)) :
    outerLobeMaximizer d ≤ selectedMiddleZ d p := by
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_le continuous_const (continuous_selectedMiddleZ d)) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  change
    0 < selectedMiddleDiscriminant d q ∧
      Real.cos d.angleUpper < selectedMiddleY d q ∧
      selectedMiddleY d q < Real.cos d.angleLower ∧
      outerLobeMaximizer d < selectedMiddleZ d q ∧
      selectedMiddleZ d q < Real.cosh (pathLogParameter d.a) at hq
  exact hq.2.2.2.1.le

theorem selectedMiddleZ_le_cosh_of_mem_closure
    (d : PositiveHalfGap) {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d)) :
    selectedMiddleZ d p ≤ Real.cosh (pathLogParameter d.a) := by
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_le (continuous_selectedMiddleZ d) continuous_const) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  change
    0 < selectedMiddleDiscriminant d q ∧
      Real.cos d.angleUpper < selectedMiddleY d q ∧
      selectedMiddleY d q < Real.cos d.angleLower ∧
      outerLobeMaximizer d < selectedMiddleZ d q ∧
      selectedMiddleZ d q < Real.cosh (pathLogParameter d.a) at hq
  exact hq.2.2.2.2.le

theorem selectedMiddleXiMinus_ge_negOne_of_mem_closure
    (d : PositiveHalfGap) {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d)) :
    -1 ≤ selectedMiddleXiMinus d p := by
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_le continuous_const (continuous_selectedMiddleXiMinus d)) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  simpa only [selectedMiddleXiMinus] using
    foldXiMinus_ge_negOne_selectedMiddle_of_classified d hq

theorem selectedMiddleXiPlus_ge_negOne_of_mem_closure
    (d : PositiveHalfGap) {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d)) :
    -1 ≤ selectedMiddleXiPlus d p := by
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_le continuous_const (continuous_selectedMiddleXiPlus d)) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  simpa only [selectedMiddleXiPlus] using
    foldXiPlus_ge_negOne_selectedMiddle_of_classified d hq

theorem selectedMiddle_lobeLevel_eq_of_mem_closure
    (d : PositiveHalfGap) {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d)) :
    chordLobeWeight d.K d.a (selectedMiddleZ d p) =
      chordLobeWeight d.K d.a (selectedMiddleY d p) := by
  have hzContinuous : Continuous
      (fun x : ℝ => chordLobeWeight d.K d.a (selectedMiddleZ d x)) :=
    (continuous_chordLobeWeight d.K d.a).comp'
      (continuous_selectedMiddleZ d)
  have hyContinuous : Continuous
      (fun x : ℝ => chordLobeWeight d.K d.a (selectedMiddleY d x)) :=
    (continuous_chordLobeWeight d.K d.a).comp'
      (continuous_selectedMiddleY d)
  apply mem_of_mem_closure_classifiedGapImage d
    (isClosed_eq hzContinuous hyContinuous) ?_ hp
  rintro _ ⟨q, hq, rfl⟩
  exact chordLobeWeight_selectedMiddleZ_eq_selectedMiddleY d
    ⟨q.property, hq⟩

/-- The first outer node dominates the lower endpoint cosine of every
positive-half nodal interval. -/
theorem cos_angleLower_le_cos_pi_div (d : PositiveHalfGap) :
    Real.cos d.angleLower ≤ Real.cos (Real.pi / d.K) := by
  have hKNat : 0 < d.K := Nat.zero_lt_two.trans_le d.hK
  have hKpos : (0 : ℝ) < d.K := by exact_mod_cast hKNat
  have hbase : Real.pi / (d.K : ℝ) ≤ d.angleLower := by
    unfold PositiveHalfGap.angleLower
    rw [div_le_div_iff_of_pos_right hKpos]
    have hjcast : (1 : ℝ) ≤ d.j := by exact_mod_cast d.hj
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hjcast Real.pi_pos.le
  have hhalfPi : Real.pi / 2 ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hlowerPi : d.angleLower ≤ Real.pi :=
    d.angleLower_lt_angleUpper.le.trans
      (d.angleUpper_le_half.trans hhalfPi)
  exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hlowerPi hbase

private theorem selectedMiddleY_lt_selectedMiddleZ_of_weak_bounds
    (d : PositiveHalfGap) {x : ℝ}
    (hy : selectedMiddleY d x ≤ Real.cos d.angleLower)
    (hz : outerLobeMaximizer d ≤ selectedMiddleZ d x) :
    selectedMiddleY d x < selectedMiddleZ d x := by
  exact hy.trans_lt
    (((cos_angleLower_le_cos_pi_div d).trans_lt
      (outerLobeMaximizer_spec d).1.1).trans_le hz)

/-- A relative closure point cannot be a folded-variable collision. -/
theorem selectedMiddleDiscriminant_pos_of_mem_closure
    (d : PositiveHalfGap) {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d)) :
    0 < selectedMiddleDiscriminant d p := by
  have hdiscNonneg :=
    selectedMiddleDiscriminant_nonneg_of_mem_closure d hp
  by_contra hdiscNotPos
  have hdiscZero : selectedMiddleDiscriminant d p = 0 :=
    le_antisymm (le_of_not_gt hdiscNotPos) hdiscNonneg
  have hdiscZero' :
      foldDiscriminant d.a p (selectedMiddleRoot d p) = 0 := by
    simpa only [selectedMiddleDiscriminant] using hdiscZero
  have hxi :=
    foldXiPlus_eq_foldXiMinus_of_discriminant_eq_zero hdiscZero'
  have hyz : selectedMiddleY d p = selectedMiddleZ d p := by
    unfold selectedMiddleY selectedMiddleZ foldedHalfY foldedHalfZ
    rw [hxi]
  have hyzLt := selectedMiddleY_lt_selectedMiddleZ_of_weak_bounds d
    (selectedMiddleY_le_cos_angleLower_of_mem_closure d hp)
    (outerLobeMaximizer_le_selectedMiddleZ_of_mem_closure d hp)
  exact (ne_of_lt hyzLt) hyz

/-- The selected root cannot reach the radical endpoint `z=cosh h` at an
interior spectral-gap point. -/
theorem selectedMiddleZ_ne_cosh_of_mem_closure
    (d : PositiveHalfGap) {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d)) :
    selectedMiddleZ d p ≠ Real.cosh (pathLogParameter d.a) := by
  intro hzCosh
  have hdisc := selectedMiddleDiscriminant_pos_of_mem_closure d hp
  have hminus := selectedMiddleXiMinus_ge_negOne_of_mem_closure d hp
  have hplus := selectedMiddleXiPlus_ge_negOne_of_mem_closure d hp
  have hdisc' :
      0 < foldDiscriminant d.a p (selectedMiddleRoot d p) := by
    simpa only [selectedMiddleDiscriminant] using hdisc
  have hminus' :
      -1 ≤ foldXiMinus d.a p (selectedMiddleRoot d p) := by
    simpa only [selectedMiddleXiMinus] using hminus
  have hplus' :
      -1 ≤ foldXiPlus d.a p (selectedMiddleRoot d p) := by
    simpa only [selectedMiddleXiPlus] using hplus
  have habsRec :=
    abs_s_eq_halfChordScale_mul_sqrt_foldedHalf_complements
      (a := d.a) (x := (p : ℝ)) (s := selectedMiddleRoot d p)
      d.ha0 hdisc' hminus' hplus'
  have habs :
      |selectedMiddleRoot d p| = halfChordScale d.a * Real.sqrt
        ((Real.cosh (pathLogParameter d.a) ^ 2 - selectedMiddleY d p ^ 2) *
          (Real.cosh (pathLogParameter d.a) ^ 2 -
            selectedMiddleZ d p ^ 2)) := by
    simpa only [selectedMiddleY, selectedMiddleZ] using habsRec
  have hrootAbsZero : |selectedMiddleRoot d p| = 0 := by
    calc
      |selectedMiddleRoot d p| = halfChordScale d.a * Real.sqrt
          ((Real.cosh (pathLogParameter d.a) ^ 2 -
              selectedMiddleY d p ^ 2) *
            (Real.cosh (pathLogParameter d.a) ^ 2 -
              selectedMiddleZ d p ^ 2)) := habs
      _ = 0 := by rw [hzCosh]; simp
  exact (selectedMiddleRoot_ne_zero_of_mem_gap d p.property)
    (abs_eq_zero.mp hrootAbsZero)

@[simp] theorem chordLobeWeight_cos_angleLower (d : PositiveHalfGap) :
    chordLobeWeight d.K d.a (Real.cos d.angleLower) = 0 := by
  rw [chordLobeWeight_cos]
  simpa only [PositiveHalfGap.angleLower] using
    chordPhi_nodal (K := d.K) (k := d.j) d.hK d.hj
      ((Nat.lt_succ_self d.j).trans d.hjUpper) d.a

@[simp] theorem chordLobeWeight_cos_angleUpper (d : PositiveHalfGap) :
    chordLobeWeight d.K d.a (Real.cos d.angleUpper) = 0 := by
  rw [chordLobeWeight_cos]
  simpa only [PositiveHalfGap.angleUpper] using
    chordPhi_nodal (K := d.K) (k := d.j + 1) d.hK (by omega)
      d.hjUpper d.a

private theorem selectedMiddleZ_eq_cosh_of_Y_eq_nodal
    (d : PositiveHalfGap) {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d))
    {u : ℝ} (hy : selectedMiddleY d p = u)
    (hu : chordLobeWeight d.K d.a u = 0) :
    selectedMiddleZ d p = Real.cosh (pathLogParameter d.a) := by
  have hanti := outerChordLobeWeight_strictAntiOn_closedEndpointSide
    d.K d.hK d.a d.ha0 d.ha1 (outerLobeMaximizer_spec d).1
      (outerLobeMaximizer_spec d).2
  apply hanti.injOn
    ⟨outerLobeMaximizer_le_selectedMiddleZ_of_mem_closure d hp,
      selectedMiddleZ_le_cosh_of_mem_closure d hp⟩
    ⟨(outerLobeMaximizer_spec d).1.2.le, le_rfl⟩
  calc
    chordLobeWeight d.K d.a (selectedMiddleZ d p) =
        chordLobeWeight d.K d.a (selectedMiddleY d p) :=
      selectedMiddle_lobeLevel_eq_of_mem_closure d hp
    _ = chordLobeWeight d.K d.a u := by rw [hy]
    _ = 0 := hu
    _ = chordLobeWeight d.K d.a
        (Real.cosh (pathLogParameter d.a)) := by
      rw [chordLobeWeight_cosh_endpoint]

/-- A relative closure point cannot reach the lower nodal endpoint of the
inner variable. -/
theorem selectedMiddleY_ne_cos_angleLower_of_mem_closure
    (d : PositiveHalfGap) {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d)) :
    selectedMiddleY d p ≠ Real.cos d.angleLower := by
  intro hy
  have hz := selectedMiddleZ_eq_cosh_of_Y_eq_nodal d hp hy
    (chordLobeWeight_cos_angleLower d)
  exact (selectedMiddleZ_ne_cosh_of_mem_closure d hp) hz

/-- A relative closure point cannot reach the upper nodal endpoint of the
inner variable. -/
theorem selectedMiddleY_ne_cos_angleUpper_of_mem_closure
    (d : PositiveHalfGap) {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d)) :
    selectedMiddleY d p ≠ Real.cos d.angleUpper := by
  intro hy
  have hz := selectedMiddleZ_eq_cosh_of_Y_eq_nodal d hp hy
    (chordLobeWeight_cos_angleUpper d)
  exact (selectedMiddleZ_ne_cosh_of_mem_closure d hp) hz

private theorem selectedMiddleAngle_mem_openGap_of_strictYBounds
    (d : PositiveHalfGap) {x : ℝ}
    (hyLower : Real.cos d.angleUpper < selectedMiddleY d x)
    (hyUpper : selectedMiddleY d x < Real.cos d.angleLower) :
    d.angleLower < selectedMiddleAngle d x ∧
      selectedMiddleAngle d x < d.angleUpper := by
  have hyMem : selectedMiddleY d x ∈ Icc (-1 : ℝ) 1 :=
    ⟨(Real.neg_one_le_cos d.angleUpper).trans hyLower.le,
      hyUpper.le.trans (Real.cos_le_one d.angleLower)⟩
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
  · have h := Real.arccos_lt_arccos hyMem.1 hyUpper
      (Real.cos_le_one d.angleLower)
    rw [Real.arccos_cos d.angleLower_pos.le hlowerPi] at h
    exact h
  · have h := Real.arccos_lt_arccos
      (Real.neg_one_le_cos d.angleUpper) hyLower hyMem.2
    rw [Real.arccos_cos hupperPos.le hupperPi] at h
    exact h

/-- A relative closure point cannot cross the unique outer-lobe maximum. -/
theorem selectedMiddleZ_ne_outerLobeMaximizer_of_mem_closure
    (d : PositiveHalfGap) {p : PositiveHalfGapPoint d}
    (hp : (p : ℝ) ∈ closure (middleBranchClassifiedGapImage d)) :
    selectedMiddleZ d p ≠ outerLobeMaximizer d := by
  intro hzMax
  have hyLower : Real.cos d.angleUpper < selectedMiddleY d p :=
    lt_of_le_of_ne
      (cos_angleUpper_le_selectedMiddleY_of_mem_closure d hp)
      (selectedMiddleY_ne_cos_angleUpper_of_mem_closure d hp).symm
  have hyUpper : selectedMiddleY d p < Real.cos d.angleLower :=
    lt_of_le_of_ne
      (selectedMiddleY_le_cos_angleLower_of_mem_closure d hp)
      (selectedMiddleY_ne_cos_angleLower_of_mem_closure d hp)
  have htheta := selectedMiddleAngle_mem_openGap_of_strictYBounds
    d hyLower hyUpper
  have hcos :
      Real.cos (selectedMiddleAngle d p) = selectedMiddleY d p := by
    have hYlower : -1 ≤ selectedMiddleY d p :=
      (Real.neg_one_le_cos d.angleUpper).trans hyLower.le
    have hYupper : selectedMiddleY d p ≤ 1 :=
      hyUpper.le.trans (Real.cos_le_one d.angleLower)
    unfold selectedMiddleAngle
    exact Real.cos_arccos hYlower hYupper
  have hphi :
      chordPhi d.K d.a (selectedMiddleAngle d p) <
        chordLobeWeight d.K d.a (outerLobeMaximizer d) :=
    chordPhi_inner_lt_outerLobeMaximum d.hK d.hj d.ha0 d.ha1
      htheta.1 htheta.2
      (htheta.2.le.trans d.angleUpper_le_half)
      (outerLobeMaximizer_spec d).2
  have hYlevel :
      chordLobeWeight d.K d.a (selectedMiddleY d p) =
        chordPhi d.K d.a (selectedMiddleAngle d p) := by
    calc
      chordLobeWeight d.K d.a (selectedMiddleY d p) =
          chordLobeWeight d.K d.a
            (Real.cos (selectedMiddleAngle d p)) := by rw [hcos]
      _ = chordPhi d.K d.a (selectedMiddleAngle d p) :=
        chordLobeWeight_cos d.K d.a (selectedMiddleAngle d p)
  have hmaxEq :
      chordLobeWeight d.K d.a (outerLobeMaximizer d) =
        chordPhi d.K d.a (selectedMiddleAngle d p) := by
    calc
      chordLobeWeight d.K d.a (outerLobeMaximizer d) =
          chordLobeWeight d.K d.a (selectedMiddleZ d p) := by rw [hzMax]
      _ = chordLobeWeight d.K d.a (selectedMiddleY d p) :=
        selectedMiddle_lobeLevel_eq_of_mem_closure d hp
      _ = chordPhi d.K d.a (selectedMiddleAngle d p) := hYlevel
  exact (ne_of_lt hphi) hmaxEq.symm

/-- The classified subset is relatively closed in the exact open spectral
gap. -/
theorem isClosed_middleBranchClassifiedInGap (d : PositiveHalfGap) :
    IsClosed (middleBranchClassifiedInGap d) := by
  rw [Topology.IsInducing.subtypeVal.isClosed_iff']
  intro p hp
  have hdisc := selectedMiddleDiscriminant_pos_of_mem_closure d hp
  have hyLowerWeak :=
    cos_angleUpper_le_selectedMiddleY_of_mem_closure d hp
  have hyUpperWeak :=
    selectedMiddleY_le_cos_angleLower_of_mem_closure d hp
  have hzLowerWeak :=
    outerLobeMaximizer_le_selectedMiddleZ_of_mem_closure d hp
  have hzUpperWeak := selectedMiddleZ_le_cosh_of_mem_closure d hp
  have hyLower : Real.cos d.angleUpper < selectedMiddleY d p :=
    lt_of_le_of_ne hyLowerWeak
      (selectedMiddleY_ne_cos_angleUpper_of_mem_closure d hp).symm
  have hyUpper : selectedMiddleY d p < Real.cos d.angleLower :=
    lt_of_le_of_ne hyUpperWeak
      (selectedMiddleY_ne_cos_angleLower_of_mem_closure d hp)
  have hzLower : outerLobeMaximizer d < selectedMiddleZ d p :=
    lt_of_le_of_ne hzLowerWeak
      (selectedMiddleZ_ne_outerLobeMaximizer_of_mem_closure d hp).symm
  have hzUpper :
      selectedMiddleZ d p < Real.cosh (pathLogParameter d.a) :=
    lt_of_le_of_ne hzUpperWeak
      (selectedMiddleZ_ne_cosh_of_mem_closure d hp)
  exact ⟨hdisc, hyLower, hyUpper, hzLower, hzUpper⟩

/-- The classified subset is both open and closed in the relative gap. -/
theorem isClopen_middleBranchClassifiedInGap (d : PositiveHalfGap) :
    IsClopen (middleBranchClassifiedInGap d) :=
  ⟨isClosed_middleBranchClassifiedInGap d,
    isOpen_middleBranchClassifiedInGap d⟩

/-- Global continuation: every point of the exact positive-half spectral
gap belongs to the classified coordinate sheet. -/
theorem middleBranchClassifiedInGap_eq_univ (d : PositiveHalfGap) :
    middleBranchClassifiedInGap d = univ := by
  letI : PreconnectedSpace (PositiveHalfGapPoint d) :=
    Subtype.preconnectedSpace (by
      unfold positiveHalfSpectralGap
      exact isPreconnected_Ioo)
  have hsub : (univ : Set (PositiveHalfGapPoint d)) ⊆
      middleBranchClassifiedInGap d :=
    isPreconnected_univ.subset_isClopen
      (isClopen_middleBranchClassifiedInGap d) (by
        obtain ⟨p, hp⟩ := middleBranchClassifiedInGap_nonempty d
        exact ⟨p, trivial, hp⟩)
  exact eq_univ_of_univ_subset hsub

theorem positiveHalfSpectralGap_subset_middleBranchRawClassifiedSet
    (d : PositiveHalfGap) :
    positiveHalfSpectralGap d ⊆ middleBranchRawClassifiedSet d := by
  intro x hx
  have hp : (⟨x, hx⟩ : PositiveHalfGapPoint d) ∈
      middleBranchClassifiedInGap d := by
    rw [middleBranchClassifiedInGap_eq_univ d]
    trivial
  exact hp

end

end ConnectedPseudospectrum
