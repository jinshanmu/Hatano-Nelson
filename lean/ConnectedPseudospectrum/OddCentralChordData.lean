import ConnectedPseudospectrum.ChordFamilyExhaustion

/-!
# Chord data for the positive central gap of an odd path

For a path of odd order `2m+1`, the positive zero-adjacent spectral gap is
the `PositiveHalfGap` with chord size `K=2m+2` and gap index `j=m`.  This
module records that specialization exactly.  In particular, its angular
interval is

`[m*pi/(2m+2), pi/2]`

and its real spectral gap is

`(0, 2*sqrt(a)*sin(pi/(2m+2)))`.

The final declarations are specialization wrappers around the already proved
global chord-exhaustion and actual least-singular-value theorems.  No central
height comparison is used here.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- Parameters for the positive central gap of an odd path of actual order
`2m+1`. -/
structure OddCentralChordData where
  /-- The half-order parameter, so the represented matrix has order `2m+1`. -/
  m : Nat
  /-- The asymmetric path parameter. -/
  a : Real
  hm : 1 ≤ m
  ha0 : 0 < a
  ha1 : a < 1

namespace OddCentralChordData

private theorem centralAngle_eq_pi_div_two (m : Nat) :
    (((m + 1 : Nat) : Real) * Real.pi) /
        (((2 * m + 2 : Nat) : Real)) =
      Real.pi / 2 := by
  have hden : (2 * (m : Real) + 2) ≠ 0 := by positivity
  push_cast
  field_simp [hden]

private theorem centralLowerAngle_eq_pi_div_two_sub (m : Nat) :
    (m : Real) * Real.pi / (((2 * m + 2 : Nat) : Real)) =
      Real.pi / 2 - Real.pi / (((2 * m + 2 : Nat) : Real)) := by
  have hden : (2 * (m : Real) + 2) ≠ 0 := by positivity
  push_cast
  field_simp [hden]
  ring

/-- The central odd-order gap as the exact `PositiveHalfGap` consumed by the
chord-family development.  Its underlying matrix order is `K-1=2m+1`. -/
def positiveGap (d : OddCentralChordData) : PositiveHalfGap where
  K := 2 * d.m + 2
  j := d.m
  a := d.a
  hK := by omega
  hj := d.hm
  hjUpper := by
    have hm := d.hm
    omega
  ha0 := d.ha0
  ha1 := d.ha1
  hhalf := (centralAngle_eq_pi_div_two d.m).le

@[simp] theorem positiveGap_K (d : OddCentralChordData) :
    d.positiveGap.K = 2 * d.m + 2 := by
  rfl

@[simp] theorem positiveGap_j (d : OddCentralChordData) :
    d.positiveGap.j = d.m := by
  rfl

@[simp] theorem positiveGap_a (d : OddCentralChordData) :
    d.positiveGap.a = d.a := by
  rfl

/-- The matrix represented by the specialized chord data has the requested
actual order `2m+1`. -/
theorem positiveGap_matrixOrder (d : OddCentralChordData) :
    d.positiveGap.K - 1 = 2 * d.m + 1 := by
  simp only [positiveGap_K]
  omega

/-- The left endpoint of the central inner angular interval. -/
@[simp] theorem positiveGap_angleLower (d : OddCentralChordData) :
    d.positiveGap.angleLower =
      (d.m : Real) * Real.pi /
        (((2 * d.m + 2 : Nat) : Real)) := by
  rfl

/-- The zero-adjacent endpoint of the central inner angular interval is
exactly `pi/2`. -/
@[simp] theorem positiveGap_angleUpper (d : OddCentralChordData) :
    d.positiveGap.angleUpper = Real.pi / 2 := by
  exact centralAngle_eq_pi_div_two d.m

/-- Exact closed angular interval used by the central chord family. -/
theorem positiveGap_angleInterval (d : OddCentralChordData) :
    d.positiveGap.Angle =
      Icc
        ((d.m : Real) * Real.pi /
          (((2 * d.m + 2 : Nat) : Real)))
        (Real.pi / 2) := by
  change Icc d.positiveGap.angleLower d.positiveGap.angleUpper = _
  rw [positiveGap_angleLower, positiveGap_angleUpper]

private theorem positiveHalfGapLower_eq_rate_cos_angleUpper
    (e : PositiveHalfGap) :
    positiveHalfGapLower e =
      2 * pathRate e.a * Real.cos e.angleUpper := by
  have hKone : 1 ≤ e.K :=
    Nat.le_trans (by norm_num) e.hK
  unfold positiveHalfGapLower symmetricPathEigenvalue pathEigenangle
    PositiveHalfGap.angleUpper
  rw [Nat.sub_add_cancel hKone]

private theorem positiveHalfGapUpper_eq_rate_cos_angleLower
    (e : PositiveHalfGap) :
    positiveHalfGapUpper e =
      2 * pathRate e.a * Real.cos e.angleLower := by
  have hKone : 1 ≤ e.K :=
    Nat.le_trans (by norm_num) e.hK
  unfold positiveHalfGapUpper symmetricPathEigenvalue pathEigenangle
    PositiveHalfGap.angleLower
  rw [Nat.sub_add_cancel hKone,
    Nat.sub_add_cancel e.hj]

/-- The lower spectral endpoint is the central eigenvalue zero. -/
@[simp] theorem positiveGap_lowerEndpoint (d : OddCentralChordData) :
    positiveHalfGapLower d.positiveGap = 0 := by
  rw [positiveHalfGapLower_eq_rate_cos_angleUpper,
    positiveGap_angleUpper, Real.cos_pi_div_two, mul_zero]

/-- The upper spectral endpoint is the first positive eigenvalue of the
odd-order path. -/
@[simp] theorem positiveGap_upperEndpoint (d : OddCentralChordData) :
    positiveHalfGapUpper d.positiveGap =
      2 * Real.sqrt d.a *
        Real.sin (Real.pi / (((2 * d.m + 2 : Nat) : Real))) := by
  rw [positiveHalfGapUpper_eq_rate_cos_angleLower,
    positiveGap_a, positiveGap_angleLower,
    centralLowerAngle_eq_pi_div_two_sub,
    Real.cos_pi_div_two_sub]
  rfl

/-- The specialized exact real gap is `(0, 2 sqrt(a) sin(pi/(2m+2)))`. -/
theorem positiveHalfSpectralGap_positiveGap (d : OddCentralChordData) :
    positiveHalfSpectralGap d.positiveGap =
      Ioo 0
        (2 * Real.sqrt d.a *
          Real.sin (Real.pi / (((2 * d.m + 2 : Nat) : Real)))) := by
  unfold positiveHalfSpectralGap
  rw [positiveGap_lowerEndpoint, positiveGap_upperEndpoint]

/-- Every interior central chord parameter is attained by a selected
middle-branch point in the explicit positive real central gap. -/
theorem exists_positiveCentralGapPoint_selectedMiddleAngle_eq
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper) :
    ∃ x : Real,
      x ∈ Ioo 0
        (2 * Real.sqrt d.a *
          Real.sin (Real.pi / (((2 * d.m + 2 : Nat) : Real)))) ∧
      selectedMiddleAngle d.positiveGap x = θ := by
  obtain ⟨x, hx, hθ⟩ :=
    exists_gapPoint_selectedMiddleAngle_eq d.positiveGap θ hleft hright
  refine ⟨x, ?_, hθ⟩
  rw [← positiveHalfSpectralGap_positiveGap]
  exact hx

/-- An interior central chord abscissa lies in the explicit positive central
real gap. -/
theorem outerChordFamilyX_mem_positiveCentralGap
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper) :
    outerChordFamilyX d.positiveGap θ ∈
      Ioo 0
        (2 * Real.sqrt d.a *
          Real.sin (Real.pi / (((2 * d.m + 2 : Nat) : Real)))) := by
  rw [← positiveHalfSpectralGap_positiveGap]
  exact outerChordFamilyX_mem_positiveHalfSpectralGap
    d.positiveGap θ hleft hright

/-- The specialized signed chord is the selected middle root at its own
abscissa. -/
theorem outerChordFamilySignedRoot_eq_positiveCentralSelectedMiddleRoot
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper) :
    outerChordFamilySignedRoot d.positiveGap θ =
      selectedMiddleRoot d.positiveGap
        (outerChordFamilyX d.positiveGap θ) := by
  exact outerChordFamilySignedRoot_eq_selectedMiddleRoot
    d.positiveGap θ hleft hright

/-- On every interior central chord, the chord magnitude is the actual
finite-dimensional complex Euclidean least singular value for order
`2m+1`. -/
theorem realGapValue_outerChordFamilyX_positiveCentral
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper) :
    realGapValue (2 * d.m + 1) d.a
        (outerChordFamilyX d.positiveGap θ) =
      outerChordFamilyS d.positiveGap θ := by
  simpa only [positiveGap_matrixOrder, positiveGap_a] using
    (realGapValue_outerChordFamilyX_eq_outerChordFamilyS
      d.positiveGap θ hleft hright)

end OddCentralChordData

end

end ConnectedPseudospectrum
