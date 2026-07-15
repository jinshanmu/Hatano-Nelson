import ConnectedPseudospectrum.OuterSolutionContinuity
import ConnectedPseudospectrum.OuterChordCoordinates

/-!
# The continuous endpoint-side chord family

This module packages a positive-half nodal gap and constructs the source's
coordinate-free endpoint-side outer solution as an honest continuous function
of the inner angle.  The construction includes both nodal endpoints, where the
outer variable is `cosh h` and the signed root has height zero.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- Data specifying one noncentral nodal interval in the positive half of the
angle range. -/
structure PositiveHalfGap where
  /-- The half-chord size governing the Chebyshev nodal mesh. -/
  K : ℕ
  /-- The index of the left endpoint of the selected nodal interval. -/
  j : ℕ
  /-- The asymmetric path parameter, constrained to lie in `(0,1)`. -/
  a : ℝ
  hK : 2 ≤ K
  hj : 0 < j
  hjUpper : j + 1 < K
  ha0 : 0 < a
  ha1 : a < 1
  hhalf : ((j + 1 : ℕ) : ℝ) * Real.pi / K ≤ Real.pi / 2

namespace PositiveHalfGap

/-- Left endpoint of the inner angular interval. -/
def angleLower (d : PositiveHalfGap) : ℝ :=
  (d.j : ℝ) * Real.pi / d.K

/-- Right endpoint of the inner angular interval. -/
def angleUpper (d : PositiveHalfGap) : ℝ :=
  ((d.j + 1 : ℕ) : ℝ) * Real.pi / d.K

/-- The closed angular interval used for continuation up to both spectral
endpoints. -/
abbrev Angle (d : PositiveHalfGap) := Icc d.angleLower d.angleUpper

theorem angleLower_lt_angleUpper (d : PositiveHalfGap) :
    d.angleLower < d.angleUpper := by
  unfold angleLower angleUpper
  have hKNat : 0 < d.K := Nat.zero_lt_two.trans_le d.hK
  have hKpos : (0 : ℝ) < d.K := by exact_mod_cast hKNat
  rw [div_lt_div_iff_of_pos_right hKpos]
  push_cast
  nlinarith [Real.pi_pos]

/-- The left endpoint as a member of the closed angle interval. -/
def leftAngle (d : PositiveHalfGap) : d.Angle :=
  ⟨d.angleLower, le_rfl, (angleLower_lt_angleUpper d).le⟩

/-- The right endpoint as a member of the closed angle interval. -/
def rightAngle (d : PositiveHalfGap) : d.Angle :=
  ⟨d.angleUpper, (angleLower_lt_angleUpper d).le, le_rfl⟩

theorem angleLower_pos (d : PositiveHalfGap) : 0 < d.angleLower := by
  unfold angleLower
  have hjpos : (0 : ℝ) < d.j := by exact_mod_cast d.hj
  have hKpos : (0 : ℝ) < d.K := by
    exact_mod_cast (Nat.zero_lt_two.trans_le d.hK)
  exact div_pos (mul_pos hjpos Real.pi_pos) hKpos

theorem angleUpper_le_half (d : PositiveHalfGap) :
    d.angleUpper ≤ Real.pi / 2 := by
  exact d.hhalf

end PositiveHalfGap

/-- Every trigonometric channel is nonnegative. -/
theorem chordPhi_nonneg (K : ℕ) (a θ : ℝ) :
    0 ≤ chordPhi K a θ := by
  unfold chordPhi halfTrigRadical
  positivity

/-- The continuous channel vanishes at each of its finite nodal endpoints. -/
@[simp] theorem chordPhi_nodal
    {K k : ℕ} (hK : 2 ≤ K) (hk0 : 0 < k) (hkK : k < K) (a : ℝ) :
    chordPhi K a ((k : ℝ) * Real.pi / K) = 0 := by
  have hkLe : k ≤ K - 1 := by omega
  have hzero := chebyshevU_nodal_zero (n := K - 1) (k := k) hk0 hkLe
  have hKone : 1 ≤ K := by omega
  have hden : K - 1 + 1 = K := Nat.sub_add_cancel hKone
  have hdenReal : ((K - 1 : ℕ) : ℝ) + 1 = K := by
    exact_mod_cast hden
  rw [hdenReal] at hzero
  unfold chordPhi
  rw [hzero, abs_zero, mul_zero]

/-- The coordinate-free lobe weight is nonnegative everywhere. -/
theorem chordLobeWeight_nonneg (K : ℕ) (a u : ℝ) :
    0 ≤ chordLobeWeight K a u := by
  unfold chordLobeWeight
  positivity

/-- The unique maximizer on the outer lobe. -/
noncomputable def outerLobeMaximizer (d : PositiveHalfGap) : ℝ :=
  Classical.choose
    (existsUnique_outerChordLobeMaximum d.K d.hK d.a d.ha0 d.ha1)

theorem outerLobeMaximizer_spec (d : PositiveHalfGap) :
    outerLobeMaximizer d ∈
        Ioo (Real.cos (Real.pi / d.K))
          (Real.cosh (pathLogParameter d.a)) ∧
      IsMaxOn (chordLobeWeight d.K d.a)
        (Icc (Real.cos (Real.pi / d.K))
          (Real.cosh (pathLogParameter d.a)))
        (outerLobeMaximizer d) := by
  exact (Classical.choose_spec
    (existsUnique_outerChordLobeMaximum d.K d.hK d.a d.ha0 d.ha1)).1

/-- The inner level never exceeds the outer-lobe maximum, including at the
two zero-level endpoints. -/
theorem chordPhi_le_outerLobeMaximum
    (d : PositiveHalfGap) (θ : d.Angle) :
    chordPhi d.K d.a θ ≤
      chordLobeWeight d.K d.a (outerLobeMaximizer d) := by
  rcases eq_or_lt_of_le θ.2.1 with hleft | hleft
  · have hnode :
        chordPhi d.K d.a
          ((d.j : ℝ) * Real.pi / d.K) = 0 :=
      chordPhi_nodal (K := d.K) (k := d.j) d.hK d.hj
        ((Nat.lt_succ_self d.j).trans d.hjUpper) d.a
    have hzero : chordPhi d.K d.a θ = 0 := by
      rw [← hleft]
      simpa only [PositiveHalfGap.angleLower] using hnode
    rw [hzero]
    exact chordLobeWeight_nonneg _ _ _
  rcases eq_or_lt_of_le θ.2.2 with hright | hright
  · have hnode :
        chordPhi d.K d.a
          (((d.j + 1 : ℕ) : ℝ) * Real.pi / d.K) = 0 :=
      chordPhi_nodal (K := d.K) (k := d.j + 1) d.hK (by omega)
        d.hjUpper d.a
    have hzero : chordPhi d.K d.a θ = 0 := by
      rw [hright]
      simpa only [PositiveHalfGap.angleUpper] using hnode
    rw [hzero]
    exact chordLobeWeight_nonneg _ _ _
  · exact (chordPhi_inner_lt_outerLobeMaximum d.hK d.hj d.ha0 d.ha1
      hleft hright (θ.2.2.trans d.hhalf)
      (outerLobeMaximizer_spec d).2).le

/-- The level supplied to the endpoint-side inverse homeomorphism. -/
noncomputable def innerChordLevel (d : PositiveHalfGap) (θ : d.Angle) :
    Icc (0 : ℝ) (chordLobeWeight d.K d.a (outerLobeMaximizer d)) :=
  ⟨chordPhi d.K d.a θ, chordPhi_nonneg d.K d.a θ,
    chordPhi_le_outerLobeMaximum d θ⟩

theorem continuous_innerChordLevel (d : PositiveHalfGap) :
    Continuous (innerChordLevel d) := by
  apply Continuous.subtype_mk
  exact (continuous_chordPhi d.K d.a).comp continuous_subtype_val

/-- The endpoint-side outer coordinate `z_K(W_K(cos theta))`. -/
noncomputable def outerChordFamilyZ (d : PositiveHalfGap) (θ : d.Angle) : ℝ :=
  outerLobeEndpointSolution d.K d.hK d.a d.ha0 d.ha1
    (outerLobeMaximizer d) (outerLobeMaximizer_spec d).1
    (outerLobeMaximizer_spec d).2 (innerChordLevel d θ)

theorem outerChordFamilyZ_mem (d : PositiveHalfGap) (θ : d.Angle) :
    outerChordFamilyZ d θ ∈
      Icc (outerLobeMaximizer d)
        (Real.cosh (pathLogParameter d.a)) := by
  exact outerLobeEndpointSolution_mem d.K d.hK d.a d.ha0 d.ha1
    (outerLobeMaximizer d) (outerLobeMaximizer_spec d).1
    (outerLobeMaximizer_spec d).2 (innerChordLevel d θ)

theorem chordLobeWeight_outerChordFamilyZ
    (d : PositiveHalfGap) (θ : d.Angle) :
    chordLobeWeight d.K d.a (outerChordFamilyZ d θ) =
      chordPhi d.K d.a θ := by
  exact chordLobeWeight_outerLobeEndpointSolution d.K d.hK d.a d.ha0 d.ha1
    (outerLobeMaximizer d) (outerLobeMaximizer_spec d).1
    (outerLobeMaximizer_spec d).2 (innerChordLevel d θ)

theorem continuous_outerChordFamilyZ (d : PositiveHalfGap) :
    Continuous (outerChordFamilyZ d) := by
  exact (continuous_outerLobeEndpointSolution d.K d.hK d.a d.ha0 d.ha1
    (outerLobeMaximizer d) (outerLobeMaximizer_spec d).1
    (outerLobeMaximizer_spec d).2).comp
      (continuous_innerChordLevel d)

/-- At every interior inner parameter, the selected outer variable is strictly
on the endpoint side of the unique outer maximum. -/
theorem outerLobeMaximizer_lt_outerChordFamilyZ
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper) :
    outerLobeMaximizer d < outerChordFamilyZ d θ := by
  have hlevel : chordPhi d.K d.a θ <
      chordLobeWeight d.K d.a (outerLobeMaximizer d) :=
    chordPhi_inner_lt_outerLobeMaximum d.hK d.hj d.ha0 d.ha1
      hleft hright (θ.2.2.trans d.hhalf)
      (outerLobeMaximizer_spec d).2
  have hne : outerChordFamilyZ d θ ≠ outerLobeMaximizer d := by
    intro hz
    have hweight := chordLobeWeight_outerChordFamilyZ d θ
    rw [hz] at hweight
    exact (ne_of_lt hlevel) hweight.symm
  exact lt_of_le_of_ne (outerChordFamilyZ_mem d θ).1 (Ne.symm hne)

/-- The actual inner and outer folded half variables cannot collide anywhere
inside the positive-half nodal interval. -/
theorem outerChordFamily_foldedVariables_ne
    (d : PositiveHalfGap) (θ : d.Angle)
    (hleft : d.angleLower < θ) (hright : θ < d.angleUpper) :
    outerChordFamilyZ d θ ^ 2 ≠ Real.cos θ ^ 2 := by
  exact outerEndpointSide_foldedVariables_ne d.hK d.hj hleft
    (θ.2.2.trans d.hhalf) (outerLobeMaximizer_spec d).1
    (outerLobeMaximizer_lt_outerChordFamilyZ d θ hleft hright)

/-- A zero inner level selects the outer radical endpoint `cosh h`. -/
theorem outerChordFamilyZ_eq_cosh_of_chordPhi_eq_zero
    (d : PositiveHalfGap) (θ : d.Angle)
    (hzero : chordPhi d.K d.a θ = 0) :
    outerChordFamilyZ d θ = Real.cosh (pathLogParameter d.a) := by
  have hanti := outerChordLobeWeight_strictAntiOn_closedEndpointSide
    d.K d.hK d.a d.ha0 d.ha1 (outerLobeMaximizer_spec d).1
    (outerLobeMaximizer_spec d).2
  apply hanti.injOn (outerChordFamilyZ_mem d θ)
    ⟨(outerLobeMaximizer_spec d).1.2.le, le_rfl⟩
  rw [chordLobeWeight_outerChordFamilyZ d θ, hzero,
    chordLobeWeight_cosh_endpoint]

@[simp] theorem outerChordFamilyZ_leftAngle (d : PositiveHalfGap) :
    outerChordFamilyZ d d.leftAngle =
      Real.cosh (pathLogParameter d.a) := by
  apply outerChordFamilyZ_eq_cosh_of_chordPhi_eq_zero
  simpa only [PositiveHalfGap.leftAngle, PositiveHalfGap.angleLower]
    using chordPhi_nodal (K := d.K) (k := d.j) d.hK d.hj
      ((Nat.lt_succ_self d.j).trans d.hjUpper) d.a

@[simp] theorem outerChordFamilyZ_rightAngle (d : PositiveHalfGap) :
    outerChordFamilyZ d d.rightAngle =
      Real.cosh (pathLogParameter d.a) := by
  apply outerChordFamilyZ_eq_cosh_of_chordPhi_eq_zero
  simpa only [PositiveHalfGap.rightAngle, PositiveHalfGap.angleUpper]
    using chordPhi_nodal (K := d.K) (k := d.j + 1) d.hK (by omega)
      d.hjUpper d.a

/-- The scale normalization at the radical endpoint. -/
theorem halfChordScale_mul_cosh_pathLogParameter
    (a : ℝ) :
    halfChordScale a * Real.cosh (pathLogParameter a) =
      2 * pathRate a := by
  unfold halfChordScale
  field_simp [(Real.cosh_pos (pathLogParameter a)).ne']

/-- The coordinate-free horizontal coordinate of the chord family. -/
noncomputable def outerChordFamilyX
    (d : PositiveHalfGap) (θ : d.Angle) : ℝ :=
  outerChordX d.a θ (outerChordFamilyZ d θ)

/-- The nonnegative coordinate-free magnitude of the chord family. -/
noncomputable def outerChordFamilyS
    (d : PositiveHalfGap) (θ : d.Angle) : ℝ :=
  outerChordS d.a θ (outerChordFamilyZ d θ)

theorem continuous_outerChordFamilyX (d : PositiveHalfGap) :
    Continuous (outerChordFamilyX d) := by
  unfold outerChordFamilyX outerChordX
  exact ((continuous_const.mul
    (Real.continuous_cos.comp continuous_subtype_val)).mul
      (continuous_outerChordFamilyZ d))

theorem continuous_outerChordFamilyS (d : PositiveHalfGap) :
    Continuous (outerChordFamilyS d) := by
  unfold outerChordFamilyS outerChordS
  have hcos : Continuous fun θ : d.Angle => Real.cos (θ : ℝ) :=
    Real.continuous_cos.comp continuous_subtype_val
  have hz : Continuous fun θ : d.Angle => outerChordFamilyZ d θ :=
    continuous_outerChordFamilyZ d
  exact continuous_const.mul
    ((continuous_const.sub (hcos.pow 2)).mul
      (continuous_const.sub (hz.pow 2))).sqrt

@[simp] theorem outerChordFamilyX_leftAngle (d : PositiveHalfGap) :
    outerChordFamilyX d d.leftAngle =
      2 * pathRate d.a * Real.cos d.angleLower := by
  unfold outerChordFamilyX outerChordX
  rw [outerChordFamilyZ_leftAngle,
    show (d.leftAngle : ℝ) = d.angleLower by rfl]
  calc
    halfChordScale d.a * Real.cos d.angleLower *
          Real.cosh (pathLogParameter d.a) =
        (halfChordScale d.a * Real.cosh (pathLogParameter d.a)) *
          Real.cos d.angleLower := by ring
    _ = 2 * pathRate d.a * Real.cos d.angleLower := by
      rw [halfChordScale_mul_cosh_pathLogParameter]

@[simp] theorem outerChordFamilyX_rightAngle (d : PositiveHalfGap) :
    outerChordFamilyX d d.rightAngle =
      2 * pathRate d.a * Real.cos d.angleUpper := by
  unfold outerChordFamilyX outerChordX
  rw [outerChordFamilyZ_rightAngle,
    show (d.rightAngle : ℝ) = d.angleUpper by rfl]
  calc
    halfChordScale d.a * Real.cos d.angleUpper *
          Real.cosh (pathLogParameter d.a) =
        (halfChordScale d.a * Real.cosh (pathLogParameter d.a)) *
          Real.cos d.angleUpper := by ring
    _ = 2 * pathRate d.a * Real.cos d.angleUpper := by
      rw [halfChordScale_mul_cosh_pathLogParameter]

@[simp] theorem outerChordFamilyS_leftAngle (d : PositiveHalfGap) :
    outerChordFamilyS d d.leftAngle = 0 := by
  unfold outerChordFamilyS outerChordS
  rw [outerChordFamilyZ_leftAngle]
  ring_nf
  simp

@[simp] theorem outerChordFamilyS_rightAngle (d : PositiveHalfGap) :
    outerChordFamilyS d d.rightAngle = 0 := by
  unfold outerChordFamilyS outerChordS
  rw [outerChordFamilyZ_rightAngle]
  ring_nf
  simp

/-- The prescribed signed chord root, with sign `(-1)^j`. -/
noncomputable def outerChordFamilySignedRoot
    (d : PositiveHalfGap) (θ : d.Angle) : ℝ :=
  (-1 : ℝ) ^ d.j * outerChordFamilyS d θ

theorem continuous_outerChordFamilySignedRoot (d : PositiveHalfGap) :
    Continuous (outerChordFamilySignedRoot d) := by
  unfold outerChordFamilySignedRoot
  exact continuous_const.mul (continuous_outerChordFamilyS d)

@[simp] theorem outerChordFamilySignedRoot_leftAngle
    (d : PositiveHalfGap) :
    outerChordFamilySignedRoot d d.leftAngle = 0 := by
  simp [outerChordFamilySignedRoot]

@[simp] theorem outerChordFamilySignedRoot_rightAngle
    (d : PositiveHalfGap) :
    outerChordFamilySignedRoot d d.rightAngle = 0 := by
  simp [outerChordFamilySignedRoot]

end

end ConnectedPseudospectrum
