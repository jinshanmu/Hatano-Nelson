import ConnectedPseudospectrum.OuterLevelDominance
import Mathlib.Topology.Separation.Hausdorff

/-!
# Continuity of the endpoint-side outer solution

This module upgrades the unique endpoint-side solution from `ChordLobes` to a
homeomorphic level parametrization.  It is the continuation input used when
the folded middle branch is followed across the hyperbolic/elliptic outer
coordinate transition.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

theorem chordLobeWeight_strictAntiOn_closedEndpointSide
    (K : ℕ) (hK : 2 ≤ K) (a l r : ℝ)
    (hright : chordLobeWeight K a r = 0)
    (hpos : ∀ u ∈ Ioo l r, 0 < chordLobeWeight K a u)
    (hdom : Ioo l r ⊆
      Ioo (-Real.cosh (pathLogParameter a))
        (Real.cosh (pathLogParameter a)))
    (hnodes : ∀ u ∈ Ioo l r, ∀ q ∈ chordNodes K, u ≠ q)
    {p : ℝ} (hp : p ∈ Ioo l r)
    (hpMax : IsMaxOn (chordLobeWeight K a) (Icc l r) p) :
    StrictAntiOn (chordLobeWeight K a) (Icc p r) := by
  have hpSlope : chordLogSlope K a p = 0 :=
    chordLogSlope_eq_zero_of_isMaxOn K hK a l r hpos hdom hnodes hp hpMax
  have hslopeAnti := chordLogSlope_strictAntiOn_Ioo K a l r hdom hnodes
  intro x hx y hy hxy
  by_cases hyr : y = r
  · subst y
    rw [hright]
    exact hpos x ⟨hp.1.trans_le hx.1, hxy⟩
  · have hylt : y < r := lt_of_le_of_ne hy.2 hyr
    have hxIoo : x ∈ Ioo l r :=
      ⟨hp.1.trans_le hx.1, hxy.trans hylt⟩
    have hyIoo : y ∈ Ioo l r :=
      ⟨hp.1.trans (hx.1.trans_lt hxy), hylt⟩
    have hprofileAnti :
        StrictAntiOn (chordLogProfile K a) (Icc x y) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc x y)
      · intro z hz
        have hzIoo : z ∈ Ioo l r :=
          ⟨hp.1.trans_le (hx.1.trans hz.1), hz.2.trans_lt hylt⟩
        exact (hasDerivAt_chordLogProfile K a z (hnodes z hzIoo)
          (by simpa only [abs_lt] using hdom hzIoo)).continuousAt.continuousWithinAt
      · intro z hz
        have hzIooXY : z ∈ Ioo x y := by
          simpa only [interior_Icc] using hz
        have hzIoo : z ∈ Ioo l r :=
          ⟨hp.1.trans (hx.1.trans_lt hzIooXY.1), hzIooXY.2.trans hylt⟩
        have hzDeriv := hasDerivAt_chordLogProfile K a z
          (hnodes z hzIoo) (by simpa only [abs_lt] using hdom hzIoo)
        rw [hzDeriv.deriv]
        have hzSlope : chordLogSlope K a z < chordLogSlope K a p :=
          hslopeAnti hp hzIoo (hx.1.trans_lt hzIooXY.1)
        simpa only [hpSlope] using hzSlope
    have hprofilelt :
        chordLogProfile K a y < chordLogProfile K a x :=
      hprofileAnti ⟨le_rfl, hxy.le⟩ ⟨hxy.le, le_rfl⟩ hxy
    have hloglt :
        Real.log (chordLobeWeight K a y) <
          Real.log (chordLobeWeight K a x) := by
      rw [log_chordLobeWeight_eq K hK a y (hnodes y hyIoo)
          (by simpa only [abs_lt] using hdom hyIoo),
        log_chordLobeWeight_eq K hK a x (hnodes x hxIoo)
          (by simpa only [abs_lt] using hdom hxIoo)]
      linarith
    by_contra hweight
    have hle : chordLobeWeight K a x ≤ chordLobeWeight K a y :=
      le_of_not_gt hweight
    have hlogle := Real.log_le_log (hpos x hxIoo) hle
    exact (not_lt_of_ge hlogle) hloglt

/-- The endpoint-side coordinate interval, parametrized homeomorphically by
the decreasing nonnegative level of `f`. -/
noncomputable def endpointLevelHomeomorph
    (f : ℝ → ℝ) {p r : ℝ} (hpr : p ≤ r)
    (hcontinuous : ContinuousOn f (Icc p r))
    (hright : f r = 0)
    (hnonneg : ∀ x ∈ Icc p r, 0 ≤ f x)
    (hanti : StrictAntiOn f (Icc p r)) :
    Icc p r ≃ₜ Icc (0 : ℝ) (f p) := by
  let g : Icc p r → Icc (0 : ℝ) (f p) := fun x =>
    ⟨f x, hnonneg x x.2,
      hanti.antitoneOn ⟨le_rfl, hpr⟩ x.2 x.2.1⟩
  have hgContinuous : Continuous g := by
    exact (hcontinuous.restrict).subtype_mk _
  have hgInjective : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hanti.injOn x.2 y.2
    exact congrArg Subtype.val hxy
  have hgSurjective : Function.Surjective g := by
    intro level
    have hlevel : (level : ℝ) ∈ Icc (f r) (f p) := by
      rw [hright]
      exact level.2
    obtain ⟨x, hx, hfx⟩ :=
      intermediate_value_Icc' hpr hcontinuous hlevel
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hfx
  exact (hgContinuous.isClosedEmbedding hgInjective).toHomeomorphOfSurjective
    hgSurjective

@[simp] theorem endpointLevelHomeomorph_apply
    (f : ℝ → ℝ) {p r : ℝ} (hpr : p ≤ r)
    (hcontinuous : ContinuousOn f (Icc p r))
    (hright : f r = 0)
    (hnonneg : ∀ x ∈ Icc p r, 0 ≤ f x)
    (hanti : StrictAntiOn f (Icc p r)) (x : Icc p r) :
    endpointLevelHomeomorph f hpr hcontinuous hright hnonneg hanti x =
      ⟨f x, hnonneg x x.2,
        hanti.antitoneOn ⟨le_rfl, hpr⟩ x.2 x.2.1⟩ := by
  rfl

theorem continuous_endpointLevelSolution
    (f : ℝ → ℝ) {p r : ℝ} (hpr : p ≤ r)
    (hcontinuous : ContinuousOn f (Icc p r))
    (hright : f r = 0)
    (hnonneg : ∀ x ∈ Icc p r, 0 ≤ f x)
    (hanti : StrictAntiOn f (Icc p r)) :
    Continuous fun level : Icc (0 : ℝ) (f p) =>
      ((endpointLevelHomeomorph f hpr hcontinuous hright hnonneg hanti).symm
        level : ℝ) := by
  exact continuous_subtype_val.comp
    (endpointLevelHomeomorph f hpr hcontinuous hright hnonneg hanti).continuous_invFun

theorem outerChordLobeWeight_strictAntiOn_closedEndpointSide
    (K : ℕ) (hK : 2 ≤ K) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    {p : ℝ}
    (hp : p ∈ Ioo (Real.cos (Real.pi / K))
      (Real.cosh (pathLogParameter a)))
    (hpMax : IsMaxOn (chordLobeWeight K a)
      (Icc (Real.cos (Real.pi / K))
        (Real.cosh (pathLogParameter a))) p) :
    StrictAntiOn (chordLobeWeight K a)
      (Icc p (Real.cosh (pathLogParameter a))) := by
  let l := Real.cos (Real.pi / K)
  let c := Real.cosh (pathLogParameter a)
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha0 ha1
  have hcOne : 1 < c := by
    dsimp [c]
    exact Real.one_lt_cosh.mpr hh.ne'
  have hlNonneg : 0 ≤ l := by
    dsimp [l]
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
  have hright : chordLobeWeight K a c = 0 :=
    chordLobeWeight_cosh_endpoint K a
  exact chordLobeWeight_strictAntiOn_closedEndpointSide K hK a l c
    hright hpos hdom hnodes hp hpMax

/-- The endpoint side of the outer chord lobe, parametrized by its level. -/
noncomputable def outerLobeLevelHomeomorph
    (K : ℕ) (hK : 2 ≤ K) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (p : ℝ)
    (hp : p ∈ Ioo (Real.cos (Real.pi / K))
      (Real.cosh (pathLogParameter a)))
    (hpMax : IsMaxOn (chordLobeWeight K a)
      (Icc (Real.cos (Real.pi / K))
        (Real.cosh (pathLogParameter a))) p) :
    Icc p (Real.cosh (pathLogParameter a)) ≃ₜ
      Icc (0 : ℝ) (chordLobeWeight K a p) :=
  endpointLevelHomeomorph (chordLobeWeight K a) hp.2.le
    (continuous_chordLobeWeight K a).continuousOn
    (chordLobeWeight_cosh_endpoint K a)
    (fun x _ => by
      unfold chordLobeWeight
      positivity)
    (outerChordLobeWeight_strictAntiOn_closedEndpointSide
      K hK a ha0 ha1 hp hpMax)

/-- The unique endpoint-side outer coordinate attaining the prescribed chord
lobe level. -/
noncomputable def outerLobeEndpointSolution
    (K : ℕ) (hK : 2 ≤ K) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (p : ℝ)
    (hp : p ∈ Ioo (Real.cos (Real.pi / K))
      (Real.cosh (pathLogParameter a)))
    (hpMax : IsMaxOn (chordLobeWeight K a)
      (Icc (Real.cos (Real.pi / K))
        (Real.cosh (pathLogParameter a))) p)
    (level : Icc (0 : ℝ) (chordLobeWeight K a p)) : ℝ :=
  (outerLobeLevelHomeomorph K hK a ha0 ha1 p hp hpMax).symm level

theorem outerLobeEndpointSolution_mem
    (K : ℕ) (hK : 2 ≤ K) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (p : ℝ)
    (hp : p ∈ Ioo (Real.cos (Real.pi / K))
      (Real.cosh (pathLogParameter a)))
    (hpMax : IsMaxOn (chordLobeWeight K a)
      (Icc (Real.cos (Real.pi / K))
        (Real.cosh (pathLogParameter a))) p)
    (level : Icc (0 : ℝ) (chordLobeWeight K a p)) :
    outerLobeEndpointSolution K hK a ha0 ha1 p hp hpMax level ∈
      Icc p (Real.cosh (pathLogParameter a)) :=
  (outerLobeLevelHomeomorph K hK a ha0 ha1 p hp hpMax).symm level |>.2

theorem chordLobeWeight_outerLobeEndpointSolution
    (K : ℕ) (hK : 2 ≤ K) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (p : ℝ)
    (hp : p ∈ Ioo (Real.cos (Real.pi / K))
      (Real.cosh (pathLogParameter a)))
    (hpMax : IsMaxOn (chordLobeWeight K a)
      (Icc (Real.cos (Real.pi / K))
        (Real.cosh (pathLogParameter a))) p)
    (level : Icc (0 : ℝ) (chordLobeWeight K a p)) :
    chordLobeWeight K a
        (outerLobeEndpointSolution K hK a ha0 ha1 p hp hpMax level) = level := by
  have h := (outerLobeLevelHomeomorph K hK a ha0 ha1 p hp hpMax).apply_symm_apply
    level
  exact congrArg Subtype.val h

theorem continuous_outerLobeEndpointSolution
    (K : ℕ) (hK : 2 ≤ K) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (p : ℝ)
    (hp : p ∈ Ioo (Real.cos (Real.pi / K))
      (Real.cosh (pathLogParameter a)))
    (hpMax : IsMaxOn (chordLobeWeight K a)
      (Icc (Real.cos (Real.pi / K))
        (Real.cosh (pathLogParameter a))) p) :
    Continuous (outerLobeEndpointSolution K hK a ha0 ha1 p hp hpMax) := by
  exact continuous_subtype_val.comp
    (outerLobeLevelHomeomorph K hK a ha0 ha1 p hp hpMax).continuous_invFun

end

end ConnectedPseudospectrum
