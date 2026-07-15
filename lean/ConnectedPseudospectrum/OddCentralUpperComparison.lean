import ConnectedPseudospectrum.OddCentralChordData
import ConnectedPseudospectrum.EvenCentralChordAlgebra
import ConnectedPseudospectrum.NoncentralEllipticComparison
import Mathlib.Analysis.Convex.Deriv

/-!
# Transformed chord coordinates for the odd central upper comparison

This module specializes lines 1484--1571 of the immutable source.  For the
positive central chord of an odd path of order `2m+1`, it introduces

* `t_in = 2 cos(theta)^2 - 1`,
* `t_out = 2 z^2 - 1`,
* `zeta = (a+a⁻¹)/2`, and
* `V_m(t) = sqrt ((zeta-t)(1+t)) U_m(t)`.

The first part is the exact algebraic reduction of the chord equations.  The
second part isolates the strictly log-concave transformed outer lobe and the
descending-root comparison with `centralRho`.  No comparison with the lower
central height `c_(m+1)` is used.
-/

namespace ConnectedPseudospectrum

open Set
open scoped BigOperators

noncomputable section

namespace OddCentralChordData

/-- The source's central parameter `zeta=(a+a⁻¹)/2`. -/
def transformedZeta (d : OddCentralChordData) : Real :=
  (d.a + d.a⁻¹) / 2

/-- The largest zero `omega_m^e=cos(pi/(m+1))` of `U_m`. -/
def transformedFirstNode (d : OddCentralChordData) : Real :=
  centralChebyshevFirstNode d.m

/-- The quadratic half-angle coordinate `u |-> 2u²-1`. -/
def transformedCoordinate (u : Real) : Real :=
  2 * u ^ 2 - 1

/-- The transformed inner coordinate along the positive central chord. -/
def transformedInner (d : OddCentralChordData)
    (θ : d.positiveGap.Angle) : Real :=
  transformedCoordinate (Real.cos θ)

/-- The transformed endpoint-side outer coordinate. -/
def transformedOuter (d : OddCentralChordData)
    (θ : d.positiveGap.Angle) : Real :=
  transformedCoordinate (outerChordFamilyZ d.positiveGap θ)

/-- The source's transformed lobe function
`V_m(t)=sqrt((zeta-t)(1+t))*U_m(t)`. -/
def transformedCentralWeight (d : OddCentralChordData) (t : Real) : Real :=
  Real.sqrt ((d.transformedZeta - t) * (1 + t)) *
    chebyshevU d.m t

/-- The selected root `rho_m(a)` from the central continuant. -/
def transformedRho (d : OddCentralChordData) : Real :=
  centralRho d.m d.a

@[simp] theorem transformedCoordinate_cos (u : Real) :
    transformedCoordinate (Real.cos u) = Real.cos (2 * u) := by
  unfold transformedCoordinate
  rw [Real.cos_two_mul]

/-- The affine radical endpoint is the doubled hyperbolic half-angle. -/
theorem transformedZeta_eq_two_cosh_sq_sub_one
    (d : OddCentralChordData) :
    d.transformedZeta =
      2 * Real.cosh (pathLogParameter d.a) ^ 2 - 1 := by
  have hcosh := four_mul_mul_cosh_sq_pathLogParameter d.ha0
  unfold transformedZeta
  field_simp [d.ha0.ne'] at hcosh ⊢
  nlinarith

theorem one_lt_transformedZeta (d : OddCentralChordData) :
    1 < d.transformedZeta := by
  rw [transformedZeta_eq_two_cosh_sq_sub_one]
  have hc : 1 < Real.cosh (pathLogParameter d.a) :=
    Real.one_lt_cosh.mpr
      (pathLogParameter_pos d.ha0 d.ha1).ne'
  nlinarith

theorem transformedFirstNode_nonneg (d : OddCentralChordData) :
    0 ≤ d.transformedFirstNode := by
  unfold transformedFirstNode centralChebyshevFirstNode
  have hangle :
      Real.pi / (((d.m + 1 : Nat) : Real)) ≤ Real.pi / 2 := by
    rw [div_le_div_iff_of_pos_left Real.pi_pos (by positivity)
      (by norm_num : (0 : Real) < 2)]
    exact_mod_cast Nat.succ_le_succ d.hm
  have hangleNonneg :
      0 ≤ Real.pi / (((d.m + 1 : Nat) : Real)) := by
    positivity
  exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [Real.pi_pos, hangleNonneg]) hangle

theorem transformedFirstNode_lt_one (d : OddCentralChordData) :
    d.transformedFirstNode < 1 := by
  exact centralChebyshevFirstNode_lt_one d.m

/-- The left nodal angle transforms to the negative largest zero of `U_m`.
-/
theorem transformedCoordinate_cos_angleLower
    (d : OddCentralChordData) :
    transformedCoordinate (Real.cos d.positiveGap.angleLower) =
      -d.transformedFirstNode := by
  rw [transformedCoordinate_cos]
  have hangle :
      2 * d.positiveGap.angleLower =
        Real.pi - Real.pi / (((d.m + 1 : Nat) : Real)) := by
    rw [positiveGap_angleLower]
    have hden : (0 : Real) < (d.m + 1 : Nat) := by positivity
    push_cast
    field_simp [hden.ne']
    ring
  rw [hangle, Real.cos_pi_sub]
  rfl

/-- The first outer nodal coordinate transforms to the largest zero of
`U_m`. -/
theorem transformedCoordinate_firstOuterNode
    (d : OddCentralChordData) :
    transformedCoordinate
        (Real.cos (Real.pi / ((2 * d.m + 2 : Nat) : Real))) =
      d.transformedFirstNode := by
  rw [transformedCoordinate_cos]
  have hangle :
      2 * (Real.pi / ((2 * d.m + 2 : Nat) : Real)) =
        Real.pi / (((d.m + 1 : Nat) : Real)) := by
    have hden : (0 : Real) < (d.m + 1 : Nat) := by positivity
    push_cast
    field_simp [hden.ne']
  rw [hangle]
  rfl

/-- Exact source bounds `-1<t_in<-omega_m^e`. -/
theorem transformedInner_mem
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper) :
    d.transformedInner θ ∈
      Ioo (-1) (-d.transformedFirstNode) := by
  have hyPos : 0 < Real.cos θ :=
    cos_pos_on_positiveHalfGap d.positiveGap θ hright
  have hangleLowerNonneg : 0 ≤ d.positiveGap.angleLower :=
    d.positiveGap.angleLower_pos.le
  have hangleThetaPi : (θ : Real) ≤ Real.pi :=
    (θ.2.2.trans d.positiveGap.angleUpper_le_half).trans
      (by linarith [Real.pi_pos])
  have hyLt : Real.cos θ < Real.cos d.positiveGap.angleLower :=
    Real.cos_lt_cos_of_nonneg_of_le_pi
      hangleLowerNonneg hangleThetaPi hleft
  have hyLowerNonneg : 0 ≤ Real.cos d.positiveGap.angleLower := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · linarith [Real.pi_pos, d.positiveGap.angleLower_pos]
    · exact d.positiveGap.angleLower_lt_angleUpper.le.trans
        d.positiveGap.hhalf
  have htransformLt :
      transformedCoordinate (Real.cos θ) <
        transformedCoordinate (Real.cos d.positiveGap.angleLower) := by
    unfold transformedCoordinate
    nlinarith
  constructor
  · unfold transformedInner transformedCoordinate
    nlinarith
  · rw [← transformedCoordinate_cos_angleLower]
    exact htransformLt

/-- Exact source bounds `omega_m^e<t_out<zeta`. -/
theorem transformedOuter_mem
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper) :
    d.transformedOuter θ ∈
      Ioo d.transformedFirstNode d.transformedZeta := by
  let z := outerChordFamilyZ d.positiveGap θ
  let q := Real.cos (Real.pi / ((2 * d.m + 2 : Nat) : Real))
  have hqNonneg : 0 ≤ q := by
    dsimp only [q]
    exact cos_pi_div_nat_nonneg d.positiveGap.hK
  have hzNonneg : 0 ≤ z := by
    exact outerChordFamilyZ_nonneg d.positiveGap θ
  have hqz : q < z := by
    exact (outerLobeMaximizer_spec d.positiveGap).1.1.trans
      (outerLobeMaximizer_lt_outerChordFamilyZ
        d.positiveGap θ hleft hright)
  have hzc : z < Real.cosh (pathLogParameter d.a) := by
    exact outerChordFamilyZ_lt_cosh d.positiveGap θ hleft hright
  have hlower : transformedCoordinate q < transformedCoordinate z := by
    unfold transformedCoordinate
    nlinarith
  have hupper :
      transformedCoordinate z <
        transformedCoordinate (Real.cosh (pathLogParameter d.a)) := by
    unfold transformedCoordinate
    nlinarith [Real.cosh_pos (pathLogParameter d.a)]
  constructor
  · rw [← transformedCoordinate_firstOuterNode]
    exact hlower
  · rw [transformedZeta_eq_two_cosh_sq_sub_one]
    exact hupper

/-- Exact squared half-angle reduction of the full chord-lobe profile. -/
theorem chordLobeWeight_sq_eq_transformed
    (d : OddCentralChordData) {u : Real}
    (hu : |u| ≤ Real.cosh (pathLogParameter d.a)) :
    chordLobeWeight (2 * d.m + 2) d.a u ^ 2 =
      (d.transformedZeta - transformedCoordinate u) *
        (1 + transformedCoordinate u) *
          chebyshevU d.m (transformedCoordinate u) ^ 2 := by
  let c := Real.cosh (pathLogParameter d.a)
  have huSq : u ^ 2 ≤ c ^ 2 := by
    apply sq_le_sq.mpr
    dsimp only [c]
    simpa only [abs_of_pos (Real.cosh_pos _)] using hu
  have hrad : 0 ≤ c ^ 2 - u ^ 2 := sub_nonneg.mpr huSq
  have hhalf := chebyshevU_half_angle_odd_index_mul d.m u
  have hindex : 2 * d.m + 2 - 1 = 2 * d.m + 1 := by omega
  have hindexInt :
      ((2 * d.m + 1 : Nat) : Int) = 2 * (d.m : Int) + 1 := by
    push_cast
    ring
  rw [transformedZeta_eq_two_cosh_sq_sub_one]
  unfold chordLobeWeight transformedCoordinate
  rw [hindex, hindexInt, mul_pow, Real.sq_sqrt hrad, sq_abs,
    ← hhalf]
  ring

/-- The squared source formula for the inner lobe. -/
theorem chordLobeWeight_cos_sq_eq_transformedInner
    (d : OddCentralChordData) (θ : d.positiveGap.Angle) :
    chordLobeWeight (2 * d.m + 2) d.a (Real.cos θ) ^ 2 =
      (d.transformedZeta - d.transformedInner θ) *
        (1 + d.transformedInner θ) *
          chebyshevU d.m (d.transformedInner θ) ^ 2 := by
  apply chordLobeWeight_sq_eq_transformed
  have hc : 1 ≤ Real.cosh (pathLogParameter d.a) :=
    Real.one_le_cosh _
  exact (Real.abs_cos_le_one θ).trans hc

/-- The squared source formula for the endpoint-side outer lobe. -/
theorem chordLobeWeight_outer_sq_eq_transformedOuter
    (d : OddCentralChordData) (θ : d.positiveGap.Angle) :
    chordLobeWeight (2 * d.m + 2) d.a
          (outerChordFamilyZ d.positiveGap θ) ^ 2 =
      (d.transformedZeta - d.transformedOuter θ) *
        (1 + d.transformedOuter θ) *
          chebyshevU d.m (d.transformedOuter θ) ^ 2 := by
  apply chordLobeWeight_sq_eq_transformed
  exact outerChordFamilyZ_abs_le_cosh d.positiveGap θ

/-- On either transformed central interval, `V_m(t)^2` is its displayed
radical-polynomial expression. -/
theorem transformedCentralWeight_sq
    (d : OddCentralChordData) {t : Real}
    (ht : -1 ≤ t) (htzeta : t ≤ d.transformedZeta) :
    d.transformedCentralWeight t ^ 2 =
      (d.transformedZeta - t) * (1 + t) *
        chebyshevU d.m t ^ 2 := by
  have hrad : 0 ≤ (d.transformedZeta - t) * (1 + t) :=
    mul_nonneg (sub_nonneg.mpr htzeta) (by linarith)
  unfold transformedCentralWeight
  rw [mul_pow, Real.sq_sqrt hrad]

/-- Equality of inner and outer chord levels in the exact transformed
variables. -/
theorem transformedCentralWeight_outer_eq_abs_inner
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper) :
    d.transformedCentralWeight (d.transformedOuter θ) =
      |d.transformedCentralWeight (d.transformedInner θ)| := by
  have hin := transformedInner_mem d θ hleft hright
  have hout := transformedOuter_mem d θ hleft hright
  have hinZeta : d.transformedInner θ ≤ d.transformedZeta := by
    nlinarith [hin.2, transformedFirstNode_nonneg d,
      one_lt_transformedZeta d]
  have houtLower : -1 ≤ d.transformedOuter θ := by
    nlinarith [hout.1, transformedFirstNode_nonneg d]
  have hsqIn := transformedCentralWeight_sq d hin.1.le hinZeta
  have hsqOut := transformedCentralWeight_sq d houtLower hout.2.le
  have hlevels := congrArg (fun q : Real => q ^ 2)
    (chordLobeWeight_outerChordFamilyZ d.positiveGap θ)
  rw [← chordLobeWeight_cos] at hlevels
  have hinnerW := chordLobeWeight_cos_sq_eq_transformedInner d θ
  have houterW := chordLobeWeight_outer_sq_eq_transformedOuter d θ
  have hsquares :
      d.transformedCentralWeight (d.transformedOuter θ) ^ 2 =
        d.transformedCentralWeight (d.transformedInner θ) ^ 2 := by
    rw [hsqOut, hsqIn, ← houterW, ← hinnerW]
    exact hlevels
  have houterU :
      0 < chebyshevU d.m (d.transformedOuter θ) :=
    chebyshevU_pos_above_centralFirstNode d.m d.hm hout.1
  have houterRad :
      0 < (d.transformedZeta - d.transformedOuter θ) *
        (1 + d.transformedOuter θ) :=
    mul_pos (sub_pos.mpr hout.2)
      (add_pos_of_pos_of_nonneg zero_lt_one
        ((transformedFirstNode_nonneg d).trans hout.1.le))
  have houterPos :
      0 < d.transformedCentralWeight (d.transformedOuter θ) := by
    unfold transformedCentralWeight
    exact mul_pos (Real.sqrt_pos.2 houterRad) houterU
  apply (sq_eq_sq₀ houterPos.le
    (abs_nonneg (d.transformedCentralWeight (d.transformedInner θ)))).mp
  rw [sq_abs]
  exact hsquares

/-- The exact transformed formula for the squared chord abscissa. -/
theorem outerChordFamilyX_sq_eq_transformed
    (d : OddCentralChordData) (θ : d.positiveGap.Angle) :
    outerChordFamilyX d.positiveGap θ ^ 2 =
      2 * d.a *
          (1 + d.transformedOuter θ) *
          (1 + d.transformedInner θ) /
        (d.transformedZeta + 1) := by
  have hscale := halfChordScale_sq_eq_four_mul_div_cosh_sq d.ha0
  have hzeta := transformedZeta_eq_two_cosh_sq_sub_one d
  unfold outerChordFamilyX outerChordX transformedOuter transformedInner
    transformedCoordinate
  rw [positiveGap_a, mul_pow, mul_pow, hscale, hzeta]
  field_simp [(Real.cosh_pos (pathLogParameter d.a)).ne']
  ring

/-- The exact transformed formula for the squared actual chord height. -/
theorem outerChordFamilyS_sq_eq_transformed
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper) :
    outerChordFamilyS d.positiveGap θ ^ 2 =
      2 * d.a *
          (d.transformedZeta - d.transformedOuter θ) *
          (d.transformedZeta - d.transformedInner θ) /
        (d.transformedZeta + 1) := by
  let c := Real.cosh (pathLogParameter d.a)
  let y := Real.cos θ
  let z := outerChordFamilyZ d.positiveGap θ
  have hyRad : 0 < c ^ 2 - y ^ 2 := by
    have hh := pathLogParameter_pos d.ha0 d.ha1
    have hsinh : 0 < Real.sinh (pathLogParameter d.a) :=
      Real.sinh_pos_iff.mpr hh
    have hid := chordRadicand_cos_eq_sinh_sq_add_sin_sq d.a θ
    dsimp only [c, y]
    rw [hid]
    nlinarith [sq_pos_of_pos hsinh, sq_nonneg (Real.sin θ)]
  have hzRad : 0 < c ^ 2 - z ^ 2 := by
    have hz0 : 0 ≤ z := outerChordFamilyZ_nonneg d.positiveGap θ
    have hzc : z < Real.cosh (pathLogParameter d.a) := by
      dsimp only [z]
      simpa only [positiveGap_a] using
        outerChordFamilyZ_lt_cosh d.positiveGap θ hleft hright
    exact sub_pos.mpr
      ((sq_lt_sq₀ hz0 (Real.cosh_pos (pathLogParameter d.a)).le).2
        hzc)
  have hrad : 0 ≤ (c ^ 2 - y ^ 2) * (c ^ 2 - z ^ 2) :=
    (mul_pos hyRad hzRad).le
  have hscale := halfChordScale_sq_eq_four_mul_div_cosh_sq d.ha0
  have hzeta := transformedZeta_eq_two_cosh_sq_sub_one d
  unfold outerChordFamilyS outerChordS transformedOuter transformedInner
    transformedCoordinate
  change
    (halfChordScale d.a *
      Real.sqrt ((c ^ 2 - y ^ 2) * (c ^ 2 - z ^ 2))) ^ 2 = _
  rw [mul_pow, Real.sq_sqrt hrad, hscale, hzeta]
  field_simp [(Real.cosh_pos (pathLogParameter d.a)).ne']
  ring

/-! ## The transformed logarithmic lobe -/

/-- The selected central continuant root lies in the transformed outer
interval. -/
theorem transformedRho_mem (d : OddCentralChordData) :
    d.transformedRho ∈
      Ioo d.transformedFirstNode d.transformedZeta := by
  constructor
  · exact (centralRho_spec d.m d.hm d.a d.ha0 d.ha1).1
  · exact sub_pos.mp
      (centralZeta_sub_rho_pos d.m d.hm d.a d.ha0 d.ha1)

/-- `V_m` is positive on the transformed outer lobe. -/
theorem transformedCentralWeight_pos
    (d : OddCentralChordData) {t : Real}
    (ht : t ∈ Ioo d.transformedFirstNode d.transformedZeta) :
    0 < d.transformedCentralWeight t := by
  have hrad : 0 < (d.transformedZeta - t) * (1 + t) := by
    apply mul_pos (sub_pos.mpr ht.2)
    exact add_pos_of_pos_of_nonneg zero_lt_one
      ((transformedFirstNode_nonneg d).trans ht.1.le)
  have hU : 0 < chebyshevU d.m t :=
    chebyshevU_pos_above_centralFirstNode d.m d.hm ht.1
  unfold transformedCentralWeight
  exact mul_pos (Real.sqrt_pos.2 hrad) hU

/-- An explicit logarithm of `V_m`, written through the simple Chebyshev
roots so that its curvature is termwise negative. -/
def transformedCentralLogProfile
    (d : OddCentralChordData) (t : Real) : Real :=
  Real.log (2 ^ d.m : Real) +
    Real.log (d.transformedZeta - t) / 2 +
    Real.log (1 + t) / 2 +
    ∑ q ∈ chordNodes (d.m + 1), Real.log |t - q|

/-- The exact logarithmic derivative of the transformed central lobe. -/
def transformedCentralLogSlope
    (d : OddCentralChordData) (t : Real) : Real :=
  (∑ q ∈ chordNodes (d.m + 1), (t - q)⁻¹) +
    1 / (2 * (1 + t)) -
    1 / (2 * (d.transformedZeta - t))

/-- The exact second logarithmic derivative. -/
def transformedCentralLogCurvature
    (d : OddCentralChordData) (t : Real) : Real :=
  -(∑ q ∈ chordNodes (d.m + 1), 1 / (t - q) ^ 2) -
    1 / (2 * (1 + t) ^ 2) -
    1 / (2 * (d.transformedZeta - t) ^ 2)

private theorem transformedCentral_ne_chordNode
    (d : OddCentralChordData) {t : Real}
    (ht : d.transformedFirstNode < t) :
    ∀ q ∈ chordNodes (d.m + 1), t ≠ q := by
  intro q hq htq
  subst t
  exact (not_lt_of_ge
    (chordNode_le_first (d.m + 1) (Nat.succ_le_succ d.hm) hq)) ht

/-- On the transformed outer interval, the explicit logarithmic profile is
literally `log V_m`. -/
theorem log_transformedCentralWeight_eq_profile
    (d : OddCentralChordData) {t : Real}
    (ht : t ∈ Ioo d.transformedFirstNode d.transformedZeta) :
    Real.log (d.transformedCentralWeight t) =
      d.transformedCentralLogProfile t := by
  have hrad : 0 < (d.transformedZeta - t) * (1 + t) := by
    exact mul_pos (sub_pos.mpr ht.2)
      (add_pos_of_pos_of_nonneg zero_lt_one
        ((transformedFirstNode_nonneg d).trans ht.1.le))
  have hnodes := transformedCentral_ne_chordNode d ht.1
  have hprod : chordNodeProduct (d.m + 1) t ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    exact sub_ne_zero.mpr (hnodes q hq)
  have hpow : (2 ^ d.m : Real) ≠ 0 := by positivity
  have hU : chebyshevU d.m t =
      2 ^ d.m * chordNodeProduct (d.m + 1) t := by
    have h := chebyshevU_eq_chordNodeProduct (d.m + 1)
      (Nat.succ_le_succ d.hm) t
    simpa only [Nat.add_sub_cancel] using h
  have hlogProd :
      Real.log |chordNodeProduct (d.m + 1) t| =
        ∑ q ∈ chordNodes (d.m + 1), Real.log |t - q| := by
    rw [chordNodeProduct, Finset.abs_prod, Real.log_prod]
    intro q hq
    exact abs_ne_zero.mpr (sub_ne_zero.mpr (hnodes q hq))
  have hUpos : 0 < chebyshevU d.m t :=
    chebyshevU_pos_above_centralFirstNode d.m d.hm ht.1
  have hprodPos : 0 < chordNodeProduct (d.m + 1) t := by
    rw [hU] at hUpos
    exact pos_of_mul_pos_right hUpos
      (by positivity : (0 : Real) ≤ 2 ^ d.m)
  have hleftFactor : 0 < 1 + t :=
    add_pos_of_pos_of_nonneg zero_lt_one
      ((transformedFirstNode_nonneg d).trans ht.1.le)
  have hrightFactor : 0 < d.transformedZeta - t := sub_pos.mpr ht.2
  unfold transformedCentralWeight transformedCentralLogProfile
  rw [Real.log_mul (Real.sqrt_pos.2 hrad).ne' hUpos.ne',
    Real.log_sqrt hrad.le,
    Real.log_mul hrightFactor.ne' hleftFactor.ne', hU,
    Real.log_mul hpow hprod,
    ← abs_of_pos hprodPos, hlogProd]
  ring

/-- The derivative of the explicit transformed logarithmic profile. -/
theorem hasDerivAt_transformedCentralLogProfile
    (d : OddCentralChordData) {t : Real}
    (ht : t ∈ Ioo d.transformedFirstNode d.transformedZeta) :
    HasDerivAt d.transformedCentralLogProfile
      (d.transformedCentralLogSlope t) t := by
  have hleft : 0 < 1 + t := by
    linarith [transformedFirstNode_nonneg d, ht.1]
  have hright : 0 < d.transformedZeta - t := sub_pos.mpr ht.2
  have hnodes := transformedCentral_ne_chordNode d ht.1
  have hZeta :
      HasDerivAt (fun u : Real =>
        Real.log (d.transformedZeta - u) / 2)
        (-1 / (2 * (d.transformedZeta - t))) t := by
    have hbase :=
      ((hasDerivAt_const t d.transformedZeta).sub (hasDerivAt_id t)).log
        hright.ne'
    convert hbase.div_const 2 using 1
    simp only [Pi.sub_apply, id_eq]
    field_simp [hright.ne']
    ring
  have hOne :
      HasDerivAt (fun u : Real => Real.log (1 + u) / 2)
        (1 / (2 * (1 + t))) t := by
    have hbase :=
      ((hasDerivAt_const t 1).add (hasDerivAt_id t)).log hleft.ne'
    convert hbase.div_const 2 using 1
    simp only [Pi.add_apply, id_eq]
    field_simp [hleft.ne']
    ring
  have hsum :
      HasDerivAt
        (fun u : Real =>
          ∑ q ∈ chordNodes (d.m + 1), Real.log |u - q|)
        (∑ q ∈ chordNodes (d.m + 1), (t - q)⁻¹) t := by
    apply HasDerivAt.fun_sum
    intro q hq
    have h := ((hasDerivAt_id t).sub_const q).log
      (sub_ne_zero.mpr (hnodes q hq))
    simpa only [Real.log_abs, one_div] using h
  have hconst :
      HasDerivAt (fun _ : Real => Real.log (2 ^ d.m : Real)) 0 t :=
    hasDerivAt_const t _
  convert ((hconst.add hZeta).add hOne).add hsum using 1
  simp only [transformedCentralLogSlope, sub_eq_add_neg]
  ring

/-- The derivative of the transformed logarithmic slope. -/
theorem hasDerivAt_transformedCentralLogSlope
    (d : OddCentralChordData) {t : Real}
    (ht : t ∈ Ioo d.transformedFirstNode d.transformedZeta) :
    HasDerivAt d.transformedCentralLogSlope
      (d.transformedCentralLogCurvature t) t := by
  have hleft : 0 < 1 + t := by
    linarith [transformedFirstNode_nonneg d, ht.1]
  have hright : 0 < d.transformedZeta - t := sub_pos.mpr ht.2
  have hnodes := transformedCentral_ne_chordNode d ht.1
  have hsum :
      HasDerivAt
        (fun u : Real =>
          ∑ q ∈ chordNodes (d.m + 1), (u - q)⁻¹)
        (-∑ q ∈ chordNodes (d.m + 1), 1 / (t - q) ^ 2) t := by
    have hraw :
        HasDerivAt
          (fun u : Real =>
            ∑ q ∈ chordNodes (d.m + 1), (u - q)⁻¹)
          (∑ q ∈ chordNodes (d.m + 1),
            -(1 / (t - q) ^ 2)) t := by
      apply HasDerivAt.fun_sum
      intro q hq
      convert ((hasDerivAt_id t).sub_const q).inv
        (sub_ne_zero.mpr (hnodes q hq)) using 1
      simp only [id_eq]
      ring
    simpa only [Finset.sum_neg_distrib] using hraw
  have hOne :
      HasDerivAt (fun u : Real => 1 / (2 * (1 + u)))
        (-1 / (2 * (1 + t) ^ 2)) t := by
    have hden : HasDerivAt (fun u : Real => 2 * (1 + u)) 2 t := by
      convert (hasDerivAt_const t 2).mul
        ((hasDerivAt_const t 1).add (hasDerivAt_id t)) using 1
      ring
    convert (hasDerivAt_const t 1).div hden
      (mul_ne_zero (by norm_num) hleft.ne') using 1
    field_simp [hleft.ne']
    ring
  have hZeta :
      HasDerivAt
        (fun u : Real => -(1 / (2 * (d.transformedZeta - u))))
        (-1 / (2 * (d.transformedZeta - t) ^ 2)) t := by
    have hden :
        HasDerivAt (fun u : Real =>
          2 * (d.transformedZeta - u)) (-2) t := by
      convert (hasDerivAt_const t 2).mul
        ((hasDerivAt_const t d.transformedZeta).sub
          (hasDerivAt_id t)) using 1
      ring
    convert ((hasDerivAt_const t 1).div hden
      (mul_ne_zero (by norm_num) hright.ne')).neg using 1
    field_simp [hright.ne']
    ring
  convert (hsum.add hOne).add hZeta using 1
  simp only [transformedCentralLogCurvature, sub_eq_add_neg]
  ring

/-- Every term in the transformed logarithmic curvature is negative in
the outer interval. -/
theorem transformedCentralLogCurvature_neg
    (d : OddCentralChordData) {t : Real}
    (ht : t ∈ Ioo d.transformedFirstNode d.transformedZeta) :
    d.transformedCentralLogCurvature t < 0 := by
  have hleft : 0 < 1 + t := by
    linarith [transformedFirstNode_nonneg d, ht.1]
  have hright : 0 < d.transformedZeta - t := sub_pos.mpr ht.2
  have hsum :
      0 ≤ ∑ q ∈ chordNodes (d.m + 1), 1 / (t - q) ^ 2 := by
    positivity
  unfold transformedCentralLogCurvature
  have hone : 0 < 1 / (2 * (1 + t) ^ 2) := by positivity
  have hzeta : 0 < 1 / (2 * (d.transformedZeta - t) ^ 2) := by positivity
  linarith

/-- The logarithmic derivative is strictly decreasing throughout the
transformed outer lobe. -/
theorem transformedCentralLogSlope_strictAntiOn
    (d : OddCentralChordData) :
    StrictAntiOn d.transformedCentralLogSlope
      (Ioo d.transformedFirstNode d.transformedZeta) := by
  apply strictAntiOn_of_deriv_neg
    (convex_Ioo d.transformedFirstNode d.transformedZeta)
  · intro t ht
    exact (hasDerivAt_transformedCentralLogSlope d ht).continuousAt.continuousWithinAt
  · intro t ht
    have htOuter : t ∈ Ioo d.transformedFirstNode d.transformedZeta := by
      simpa only [interior_Ioo] using ht
    rw [(hasDerivAt_transformedCentralLogSlope d htOuter).deriv]
    exact transformedCentralLogCurvature_neg d htOuter

/-- Literal strict log-concavity of `V_m` on its positive outer interval. -/
theorem strictConcaveOn_log_transformedCentralWeight
    (d : OddCentralChordData) :
    StrictConcaveOn Real
      (Ioo d.transformedFirstNode d.transformedZeta)
      (fun t => Real.log (d.transformedCentralWeight t)) := by
  have hprofile :
      StrictConcaveOn Real
        (Ioo d.transformedFirstNode d.transformedZeta)
        d.transformedCentralLogProfile := by
    have hderivAnti :
        StrictAntiOn (deriv d.transformedCentralLogProfile)
          (Ioo d.transformedFirstNode d.transformedZeta) := by
      intro x hx y hy hxy
      rw [(hasDerivAt_transformedCentralLogProfile d hx).deriv,
        (hasDerivAt_transformedCentralLogProfile d hy).deriv]
      exact transformedCentralLogSlope_strictAntiOn d hx hy hxy
    have hderivAntiInterior :
        StrictAntiOn (deriv d.transformedCentralLogProfile)
          (interior
            (Ioo d.transformedFirstNode d.transformedZeta)) := by
      simpa only [interior_Ioo] using hderivAnti
    apply hderivAntiInterior.strictConcaveOn_of_deriv
      (convex_Ioo d.transformedFirstNode d.transformedZeta)
    intro t ht
    exact (hasDerivAt_transformedCentralLogProfile d ht).continuousAt.continuousWithinAt
  exact hprofile.congr fun t ht =>
    (log_transformedCentralWeight_eq_profile d ht).symm

/-! ## The descending side in transformed coordinates -/

/-- The transform sends the complete open outer lobe to
`(omega_m^e,zeta)`. -/
theorem transformedCoordinate_mem_of_mem_outerLobe
    (d : OddCentralChordData) {u : Real}
    (hu : u ∈ Ioo
      (Real.cos (Real.pi / ((2 * d.m + 2 : Nat) : Real)))
      (Real.cosh (pathLogParameter d.a))) :
    transformedCoordinate u ∈
      Ioo d.transformedFirstNode d.transformedZeta := by
  have hq0 :
      0 ≤ Real.cos (Real.pi / ((2 * d.m + 2 : Nat) : Real)) :=
    cos_pi_div_nat_nonneg d.positiveGap.hK
  have hu0 : 0 ≤ u := hq0.trans (le_of_lt hu.1)
  constructor
  · rw [← transformedCoordinate_firstOuterNode]
    unfold transformedCoordinate
    have hsq := (sq_lt_sq₀ hq0 hu0).2 hu.1
    nlinarith
  · rw [transformedZeta_eq_two_cosh_sq_sub_one]
    unfold transformedCoordinate
    have hsq := (sq_lt_sq₀ hu0
      (Real.cosh_pos (pathLogParameter d.a)).le).2 hu.2
    nlinarith

/-- On the outer lobe the original and transformed positive profiles agree,
not merely their squares. -/
theorem chordLobeWeight_eq_transformedCentralWeight
    (d : OddCentralChordData) {u : Real}
    (hu : u ∈ Ioo
      (Real.cos (Real.pi / ((2 * d.m + 2 : Nat) : Real)))
      (Real.cosh (pathLogParameter d.a))) :
    chordLobeWeight (2 * d.m + 2) d.a u =
      d.transformedCentralWeight (transformedCoordinate u) := by
  have ht := transformedCoordinate_mem_of_mem_outerLobe d hu
  have hu0 : 0 ≤ u :=
    (cos_pi_div_nat_nonneg d.positiveGap.hK).trans hu.1.le
  have huAbs : |u| ≤ Real.cosh (pathLogParameter d.a) := by
    rw [abs_of_nonneg hu0]
    exact hu.2.le
  have hWsq := chordLobeWeight_sq_eq_transformed d huAbs
  have htLower : -1 ≤ transformedCoordinate u := by
    nlinarith [ht.1, transformedFirstNode_nonneg d]
  have hVsq := transformedCentralWeight_sq d htLower ht.2.le
  apply (sq_eq_sq₀ (chordLobeWeight_nonneg _ _ _)
    (transformedCentralWeight_pos d ht).le).mp
  rw [hVsq]
  exact hWsq

private theorem hasDerivAt_log_chordLobeWeight_outer
    (d : OddCentralChordData) {u : Real}
    (hu : u ∈ Ioo
      (Real.cos (Real.pi / ((2 * d.m + 2 : Nat) : Real)))
      (Real.cosh (pathLogParameter d.a))) :
    HasDerivAt
      (fun v : Real =>
        Real.log (chordLobeWeight (2 * d.m + 2) d.a v))
      (chordLogSlope (2 * d.m + 2) d.a u) u := by
  obtain ⟨_, hdom, hnodes⟩ :=
    outerLobeAnalyticData (2 * d.m + 2) d.positiveGap.hK
      d.a d.ha0 d.ha1
  have hprofile := hasDerivAt_chordLogProfile
    (2 * d.m + 2) d.a u (hnodes u hu)
      (by simpa only [abs_lt] using hdom hu)
  have hsum :
      HasDerivAt
        (fun v : Real =>
          Real.log (2 ^ ((2 * d.m + 2) - 1) : Real) +
            chordLogProfile (2 * d.m + 2) d.a v)
        (chordLogSlope (2 * d.m + 2) d.a u) u := by
    simpa only [zero_add] using
      (hasDerivAt_const u
        (Real.log (2 ^ ((2 * d.m + 2) - 1) : Real))).add hprofile
  apply hsum.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact log_chordLobeWeight_eq
    (2 * d.m + 2) d.positiveGap.hK d.a v
      (hnodes v hv) (by simpa only [abs_lt] using hdom hv)

/-- The original outer logarithmic slope is the transformed logarithmic
slope times the Jacobian `4u`. -/
theorem chordLogSlope_eq_four_mul_transformedCentralLogSlope
    (d : OddCentralChordData) {u : Real}
    (hu : u ∈ Ioo
      (Real.cos (Real.pi / ((2 * d.m + 2 : Nat) : Real)))
      (Real.cosh (pathLogParameter d.a))) :
    chordLogSlope (2 * d.m + 2) d.a u =
      4 * u *
        d.transformedCentralLogSlope (transformedCoordinate u) := by
  have ht := transformedCoordinate_mem_of_mem_outerLobe d hu
  have htransform :
      HasDerivAt transformedCoordinate (4 * u) u := by
    unfold transformedCoordinate
    convert ((hasDerivAt_const u 2).mul
      (hasDerivAt_pow 2 u)).sub_const 1 using 1
    ring
  have hprofile :=
    (hasDerivAt_transformedCentralLogProfile d ht).comp u htransform
  have hlogV :
      HasDerivAt
        (fun v : Real =>
          Real.log
            (d.transformedCentralWeight (transformedCoordinate v)))
        (4 * u *
          d.transformedCentralLogSlope (transformedCoordinate u)) u := by
    have heventually :
        (fun v : Real =>
          Real.log
            (d.transformedCentralWeight (transformedCoordinate v))) =ᶠ[nhds u]
          (d.transformedCentralLogProfile ∘ transformedCoordinate) := by
      filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
      exact log_transformedCentralWeight_eq_profile d
        (transformedCoordinate_mem_of_mem_outerLobe d hv)
    convert hprofile.congr_of_eventuallyEq heventually using 1
    ring
  have hlogW :
      HasDerivAt
        (fun v : Real =>
          Real.log (chordLobeWeight (2 * d.m + 2) d.a v))
        (4 * u *
          d.transformedCentralLogSlope (transformedCoordinate u)) u := by
    apply hlogV.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
    rw [chordLobeWeight_eq_transformedCentralWeight d hv]
  exact (hasDerivAt_log_chordLobeWeight_outer d hu).unique hlogW

/-- The transformed coordinate of the outer-lobe maximizer. -/
def transformedOuterLobeMaximizer
    (d : OddCentralChordData) : Real :=
  transformedCoordinate (outerLobeMaximizer d.positiveGap)

theorem transformedOuterLobeMaximizer_mem
    (d : OddCentralChordData) :
    d.transformedOuterLobeMaximizer ∈
      Ioo d.transformedFirstNode d.transformedZeta := by
  exact transformedCoordinate_mem_of_mem_outerLobe d
    (outerLobeMaximizer_spec d.positiveGap).1

/-- The transformed logarithmic slope vanishes at the unique outer-lobe
maximum. -/
theorem transformedCentralLogSlope_outerLobeMaximizer_eq_zero
    (d : OddCentralChordData) :
    d.transformedCentralLogSlope d.transformedOuterLobeMaximizer = 0 := by
  let p := outerLobeMaximizer d.positiveGap
  have hp := (outerLobeMaximizer_spec d.positiveGap).1
  have hp0 : 0 < p :=
    (cos_pi_div_nat_nonneg d.positiveGap.hK).trans_lt hp.1
  have hcoordinate :=
    chordLogSlope_eq_four_mul_transformedCentralLogSlope d hp
  have hslope := outerLobeMaximizer_logSlope_eq_zero d.positiveGap
  simp only [positiveGap_K, positiveGap_a] at hslope
  rw [hslope] at hcoordinate
  dsimp only [transformedOuterLobeMaximizer, p]
  nlinarith

/-- Every selected endpoint-side outer coordinate lies strictly after the
transformed lobe maximum. -/
theorem transformedOuterLobeMaximizer_lt_transformedOuter
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper) :
    d.transformedOuterLobeMaximizer < d.transformedOuter θ := by
  have hpz := outerLobeMaximizer_lt_outerChordFamilyZ
    d.positiveGap θ hleft hright
  have hp0 : 0 ≤ outerLobeMaximizer d.positiveGap :=
    (cos_pi_div_nat_nonneg d.positiveGap.hK).trans
      (outerLobeMaximizer_spec d.positiveGap).1.1.le
  have hz0 := outerChordFamilyZ_nonneg d.positiveGap θ
  unfold transformedOuterLobeMaximizer transformedOuter
    transformedCoordinate
  nlinarith

/-! ## The reference root `rho_m` -/

/-- The logarithmic derivative `U_m'(t)/U_m(t)`. -/
def transformedChebyshevLogDerivative
    (d : OddCentralChordData) (t : Real) : Real :=
  deriv (chebyshevU d.m) t / chebyshevU d.m t

private theorem transformedNodeSum_eq_chebyshevLogDerivative
    (d : OddCentralChordData) {t : Real}
    (ht : t ∈ Ioo d.transformedFirstNode d.transformedZeta) :
    (∑ q ∈ chordNodes (d.m + 1), (t - q)⁻¹) =
      d.transformedChebyshevLogDerivative t := by
  have hnodes := transformedCentral_ne_chordNode d ht.1
  have hUpos : 0 < chebyshevU d.m t :=
    chebyshevU_pos_above_centralFirstNode d.m d.hm ht.1
  have hpoly :
      HasDerivAt (chebyshevU d.m)
        ((Polynomial.Chebyshev.U Real d.m).derivative.eval t) t := by
    exact (Polynomial.Chebyshev.U Real d.m).hasDerivAt t
  have hlogU :
      HasDerivAt (fun u : Real => Real.log (chebyshevU d.m u))
        (((Polynomial.Chebyshev.U Real d.m).derivative.eval t) /
          chebyshevU d.m t) t := by
    exact hpoly.log hUpos.ne'
  have hsum :
      HasDerivAt
        (fun u : Real => Real.log (2 ^ d.m : Real) +
          ∑ q ∈ chordNodes (d.m + 1), Real.log |u - q|)
        (∑ q ∈ chordNodes (d.m + 1), (t - q)⁻¹) t := by
    have hterms :
        HasDerivAt
          (fun u : Real =>
            ∑ q ∈ chordNodes (d.m + 1), Real.log |u - q|)
          (∑ q ∈ chordNodes (d.m + 1), (t - q)⁻¹) t := by
      apply HasDerivAt.fun_sum
      intro q hq
      have h := ((hasDerivAt_id t).sub_const q).log
        (sub_ne_zero.mpr (hnodes q hq))
      simpa only [Real.log_abs, one_div] using h
    simpa only [zero_add] using
      (hasDerivAt_const t (Real.log (2 ^ d.m : Real))).add hterms
  have hlogU' :
      HasDerivAt (fun u : Real => Real.log (chebyshevU d.m u))
        (∑ q ∈ chordNodes (d.m + 1), (t - q)⁻¹) t := by
    apply hsum.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    have hunodes := transformedCentral_ne_chordNode d hu.1
    have hprod : chordNodeProduct (d.m + 1) u ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro q hq
      exact sub_ne_zero.mpr (hunodes q hq)
    have hU := chebyshevU_eq_chordNodeProduct
      (d.m + 1) (Nat.succ_le_succ d.hm) u
    have hUindex : chebyshevU d.m u =
        2 ^ d.m * chordNodeProduct (d.m + 1) u := by
      simpa only [Nat.add_sub_cancel] using hU
    have hlogProd :
        Real.log |chordNodeProduct (d.m + 1) u| =
          ∑ q ∈ chordNodes (d.m + 1), Real.log |u - q| := by
      rw [chordNodeProduct, Finset.abs_prod, Real.log_prod]
      intro q hq
      exact abs_ne_zero.mpr (sub_ne_zero.mpr (hunodes q hq))
    have hpow : (2 ^ d.m : Real) ≠ 0 := by positivity
    have hprodPos : 0 < chordNodeProduct (d.m + 1) u := by
      have huUpos : 0 < chebyshevU d.m u :=
        chebyshevU_pos_above_centralFirstNode d.m d.hm hu.1
      rw [hUindex] at huUpos
      exact pos_of_mul_pos_right huUpos
        (by positivity : (0 : Real) ≤ 2 ^ d.m)
    rw [hUindex, Real.log_mul hpow hprod,
      ← abs_of_pos hprodPos, hlogProd]
  have hderiv :
      deriv (chebyshevU d.m) t =
        (Polynomial.Chebyshev.U Real d.m).derivative.eval t := by
    exact (Polynomial.Chebyshev.U Real d.m).deriv
  unfold transformedChebyshevLogDerivative
  rw [hderiv]
  exact (hlogU.unique hlogU').symm

/-- The transformed slope is the Chebyshev logarithmic derivative plus the
two radical terms. -/
theorem transformedCentralLogSlope_eq_chebyshevLogDerivative
    (d : OddCentralChordData) {t : Real}
    (ht : t ∈ Ioo d.transformedFirstNode d.transformedZeta) :
    d.transformedCentralLogSlope t =
      d.transformedChebyshevLogDerivative t +
        1 / (2 * (1 + t)) -
        1 / (2 * (d.transformedZeta - t)) := by
  unfold transformedCentralLogSlope
  rw [transformedNodeSum_eq_chebyshevLogDerivative d ht]

/-- The source's quotient formula for `U_m'(rho)/U_m(rho)`.

The guard `rho ≠ 1` is essential.  It is implicit in LaTeX lines
1539--1541: at `rho=1` both numerator and denominator printed there vanish.
The paper only uses this formula under `rho ≤ a < 1`, and handles
`rho=1` separately, so the guarded statement is the exact valid dependency.
-/
theorem transformedChebyshevLogDerivative_rho
    (d : OddCentralChordData)
    (hrhoOne : d.transformedRho ≠ 1) :
    d.transformedChebyshevLogDerivative d.transformedRho =
      (((d.m : Nat) : Real) * d.transformedRho -
          (((d.m + 1 : Nat) : Real) * d.a)) /
        (d.transformedRho ^ 2 - 1) := by
  let rho := d.transformedRho
  let U : Real := chebyshevU d.m rho
  let U' : Real := deriv (chebyshevU d.m) rho
  have hrho := transformedRho_mem d
  have hUpos : 0 < U := by
    exact chebyshevU_pos_above_centralFirstNode d.m d.hm hrho.1
  have hEq : d.a * U = chebyshevU ((d.m : Int) - 1) rho := by
    exact (centralRho_spec d.m d.hm d.a d.ha0 d.ha1).2
  have hpolyDeriv := congrArg
    (fun p : Polynomial Real => p.eval rho)
    (Polynomial.Chebyshev.add_one_mul_T_eq_poly_in_U
      (R := Real) (d.m : Int))
  have hpolyT := congrArg
    (fun p : Polynomial Real => p.eval rho)
    (Polynomial.Chebyshev.T_eq_X_mul_U_sub_U
      (R := Real) ((d.m : Int) - 1))
  have hDerivEval :
      (Polynomial.Chebyshev.U Real d.m).derivative.eval rho = U' := by
    dsimp only [U']
    symm
    exact (Polynomial.Chebyshev.U Real d.m).deriv
  have hTindex :
      (d.m : Int) - 1 + 2 = (d.m : Int) + 1 := by ring
  have hUindex :
      (d.m : Int) - 1 + 1 = (d.m : Int) := by ring
  have hT :
      (Polynomial.Chebyshev.T Real ((d.m : Int) + 1)).eval rho =
        rho * U - chebyshevU ((d.m : Int) - 1) rho := by
    simpa only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_X, chebyshevU, hTindex, hUindex] using hpolyT
  have hmain :
      (((d.m + 1 : Nat) : Real)) *
          (rho * U - chebyshevU ((d.m : Int) - 1) rho) =
        rho * U - (1 - rho ^ 2) * U' := by
    simpa only [Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
      Polynomial.eval_pow, Polynomial.eval_natCast,
      Polynomial.eval_intCast, chebyshevU, hDerivEval, hT,
      Int.cast_natCast, Int.cast_add, Int.cast_one,
      Nat.cast_add, Nat.cast_one] using hpolyDeriv
  have hrhoNonneg : 0 ≤ rho :=
    (transformedFirstNode_nonneg d).trans hrho.1.le
  have hrhoNegOne : rho ≠ -1 := by linarith
  have hden : rho ^ 2 - 1 ≠ 0 := by
    rw [show rho ^ 2 - 1 = (rho - 1) * (rho + 1) by ring]
    exact mul_ne_zero (sub_ne_zero.mpr hrhoOne)
      (by linarith)
  unfold transformedChebyshevLogDerivative
  dsimp only [rho, U, U'] at hEq hmain hUpos hden ⊢
  rw [← hEq] at hmain
  field_simp [hUpos.ne', hden]
  push_cast at hmain ⊢
  linear_combination (norm := ring_nf) -hmain

/-- If `rho ≤ a`, the transformed logarithmic slope at `rho` is
nonnegative. -/
theorem transformedCentralLogSlope_rho_nonneg_of_le_a
    (d : OddCentralChordData)
    (hrhoLe : d.transformedRho ≤ d.a) :
    0 ≤ d.transformedCentralLogSlope d.transformedRho := by
  have hrho := transformedRho_mem d
  have hrhoOne : d.transformedRho ≠ 1 := by
    exact ne_of_lt (hrhoLe.trans_lt d.ha1)
  have hrhoLtOne : d.transformedRho < 1 := hrhoLe.trans_lt d.ha1
  have hzetaOne : 1 ≤ d.transformedZeta :=
    (one_lt_transformedZeta d).le
  rw [transformedCentralLogSlope_eq_chebyshevLogDerivative d hrho,
    transformedChebyshevLogDerivative_rho d hrhoOne]
  have hrhoNonneg : 0 ≤ d.transformedRho :=
    (transformedFirstNode_nonneg d).trans hrho.1.le
  have hdenOne : 0 < 1 - d.transformedRho ^ 2 := by
    nlinarith
  have hnum :
      d.transformedRho ≤
        (((d.m + 1 : Nat) : Real) * d.a -
          (d.m : Real) * d.transformedRho) := by
    have hscaled :
        0 ≤ (((d.m + 1 : Nat) : Real)) *
          (d.a - d.transformedRho) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hrhoLe)
    push_cast at hscaled ⊢
    nlinarith
  have hquot :
      d.transformedRho / (1 - d.transformedRho ^ 2) ≤
        ((((d.m + 1 : Nat) : Real) * d.a -
            (d.m : Real) * d.transformedRho) /
          (1 - d.transformedRho ^ 2)) :=
    (div_le_div_iff_of_pos_right hdenOne).2 hnum
  have hradicalIdentity :
      1 / (2 * (1 - d.transformedRho)) =
        d.transformedRho / (1 - d.transformedRho ^ 2) +
          1 / (2 * (1 + d.transformedRho)) := by
    field_simp [hdenOne.ne',
      (by nlinarith : 1 - d.transformedRho ≠ 0),
      (by nlinarith : 1 + d.transformedRho ≠ 0)]
    ring
  have hfirst :
      1 / (2 * (1 - d.transformedRho)) ≤
        ((((d.m + 1 : Nat) : Real) * d.a -
            (d.m : Real) * d.transformedRho) /
          (1 - d.transformedRho ^ 2) +
            1 / (2 * (1 + d.transformedRho))) := by
    rw [hradicalIdentity]
    simpa only [add_comm] using
      add_le_add_right hquot (1 / (2 * (1 + d.transformedRho)))
  have hsecond :
      1 / (2 * (d.transformedZeta - d.transformedRho)) ≤
        1 / (2 * (1 - d.transformedRho)) := by
    apply one_div_le_one_div_of_le (by nlinarith)
    nlinarith
  rw [show d.transformedRho ^ 2 - 1 =
    -(1 - d.transformedRho ^ 2) by ring]
  have hquotSign :
      (((d.m : Nat) : Real) * d.transformedRho -
          (((d.m + 1 : Nat) : Real) * d.a)) /
          (-(1 - d.transformedRho ^ 2)) =
        ((((d.m + 1 : Nat) : Real) * d.a -
            (d.m : Real) * d.transformedRho) /
          (1 - d.transformedRho ^ 2)) := by
    field_simp [hdenOne.ne']
    ring
  rw [hquotSign]
  linarith

/-- Negative logarithmic slope forces the strict scalar relation `a<rho`.
This includes the source's separate `rho=1` observation and only invokes
the guarded quotient formula when `rho<1`. -/
theorem a_lt_transformedRho_of_logSlope_neg
    (d : OddCentralChordData)
    (hslope : d.transformedCentralLogSlope d.transformedRho < 0) :
    d.a < d.transformedRho := by
  by_contra hnot
  have hrhoLe : d.transformedRho ≤ d.a := le_of_not_gt hnot
  exact (not_lt_of_ge
    (transformedCentralLogSlope_rho_nonneg_of_le_a d hrhoLe)) hslope

/-- Exact reference value `V_m(rho)^2=(1+rho)/(2a)`. -/
theorem transformedCentralWeight_rho_sq
    (d : OddCentralChordData) :
    d.transformedCentralWeight d.transformedRho ^ 2 =
      (1 + d.transformedRho) / (2 * d.a) := by
  have hrho := transformedRho_mem d
  have hUpos : 0 < chebyshevU d.m d.transformedRho :=
    chebyshevU_pos_above_centralFirstNode d.m d.hm hrho.1
  have hEq :
      d.a * chebyshevU d.m d.transformedRho =
        chebyshevU ((d.m : Int) - 1) d.transformedRho :=
    (centralRho_spec d.m d.hm d.a d.ha0 d.ha1).2
  have hrhoLower : -1 ≤ d.transformedRho := by
    nlinarith [hrho.1, transformedFirstNode_nonneg d]
  rw [transformedCentralWeight_sq d
    hrhoLower hrho.2.le]
  simp only [transformedZeta, transformedRho] at hEq hUpos ⊢
  rw [centralZeta_sub_rho_eq d.m d.hm d.a d.ha0 d.ha1,
    ← hEq]
  field_simp [d.ha0.ne', hUpos.ne']

/-- Complementary angle `phi_c=pi-2theta` used for the negative transformed
inner coordinate. -/
def centralComplementAngle
    (d : OddCentralChordData) (θ : d.positiveGap.Angle) : Real :=
  Real.pi - 2 * θ

theorem centralComplementAngle_mem
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper) :
    d.centralComplementAngle θ ∈
      Ioo 0 (Real.pi / (((d.m + 1 : Nat) : Real))) := by
  have hupper : d.positiveGap.angleUpper = Real.pi / 2 :=
    positiveGap_angleUpper d
  have hlowerTwice :
      2 * d.positiveGap.angleLower =
        Real.pi - Real.pi / (((d.m + 1 : Nat) : Real)) := by
    rw [positiveGap_angleLower]
    have hden : (0 : Real) < (d.m + 1 : Nat) := by positivity
    push_cast
    field_simp [hden.ne']
    ring
  unfold centralComplementAngle
  constructor
  · rw [hupper] at hright
    linarith
  · linarith

theorem transformedInner_eq_neg_cos_complement
    (d : OddCentralChordData) (θ : d.positiveGap.Angle) :
    d.transformedInner θ = -Real.cos (d.centralComplementAngle θ) := by
  unfold transformedInner centralComplementAngle
  rw [transformedCoordinate_cos, Real.cos_pi_sub]
  ring

private theorem chebyshevU_neg_sq
    (m : Nat) (u : Real) :
    chebyshevU m (-u) ^ 2 = chebyshevU m u ^ 2 := by
  have hneg := Polynomial.Chebyshev.U_eval_neg
    (R := Real) m u
  have hcast :
      chebyshevU m (-u) = (-1 : Real) ^ m * chebyshevU m u := by
    unfold chebyshevU
    simpa only [Int.cast_natCast, Int.cast_negOnePow_natCast] using hneg
  rw [hcast, mul_pow, negOnePow_sq]
  simp

/-- Exact displayed inner formula in the complementary angle. -/
theorem transformedCentralWeight_inner_sq_complement
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper) :
    d.transformedCentralWeight (d.transformedInner θ) ^ 2 =
      (d.transformedZeta + Real.cos (d.centralComplementAngle θ)) *
          Real.sin (((d.m + 1 : Nat) : Real) *
            d.centralComplementAngle θ) ^ 2 /
        (1 + Real.cos (d.centralComplementAngle θ)) := by
  let phi := d.centralComplementAngle θ
  have hphi := centralComplementAngle_mem d θ hleft hright
  have hphiHalf : phi < Real.pi / 2 := by
    exact hphi.2.trans_le (by
      rw [div_le_div_iff_of_pos_left Real.pi_pos (by positivity)
        (by norm_num : (0 : Real) < 2)]
      exact_mod_cast Nat.succ_le_succ d.hm)
  have hphiPos : 0 < phi := hphi.1
  have hcosPos : 0 < Real.cos phi :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hphiPos], hphiHalf⟩
  have hsinPos : 0 < Real.sin phi :=
    Real.sin_pos_of_pos_of_lt_pi hphi.1
      (hphi.2.trans_le (by
        rw [div_le_iff₀ (by positivity : (0 : Real) < (d.m + 1 : Nat))]
        have hmcast : (1 : Real) ≤ (d.m + 1 : Nat) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le d.m)
        nlinarith [Real.pi_pos]))
  have htrig := chebyshevU_cos_mul_sin d.m phi
  have htrigSq := congrArg (fun q : Real => q ^ 2) htrig
  have hsinSq := Real.sin_sq_add_cos_sq phi
  have hin := transformedInner_mem d θ hleft hright
  have hinZeta : d.transformedInner θ ≤ d.transformedZeta := by
    nlinarith [hin.2, transformedFirstNode_nonneg d,
      one_lt_transformedZeta d]
  have hweight := transformedCentralWeight_sq d hin.1.le hinZeta
  rw [transformedInner_eq_neg_cos_complement] at hweight
  rw [transformedInner_eq_neg_cos_complement, hweight,
    chebyshevU_neg_sq]
  dsimp only [phi] at htrigSq hsinSq hcosPos hsinPos ⊢
  have hden : 1 + Real.cos (d.centralComplementAngle θ) ≠ 0 := by
    linarith
  have hsinFactor :
      (1 - Real.cos (d.centralComplementAngle θ)) *
          (1 + Real.cos (d.centralComplementAngle θ)) =
        Real.sin (d.centralComplementAngle θ) ^ 2 := by
    nlinarith [hsinSq]
  have htrigProduct :
      chebyshevU d.m (Real.cos (d.centralComplementAngle θ)) ^ 2 *
          Real.sin (d.centralComplementAngle θ) ^ 2 =
        Real.sin (((d.m + 1 : Nat) : Real) *
          d.centralComplementAngle θ) ^ 2 := by
    rw [show (((d.m + 1 : Nat) : Real)) = (d.m : Real) + 1 by
      push_cast
      ring]
    calc
      chebyshevU d.m (Real.cos (d.centralComplementAngle θ)) ^ 2 *
          Real.sin (d.centralComplementAngle θ) ^ 2 =
          (chebyshevU d.m (Real.cos (d.centralComplementAngle θ)) *
            Real.sin (d.centralComplementAngle θ)) ^ 2 := by ring
      _ = Real.sin (((d.m : Real) + 1) *
          d.centralComplementAngle θ) ^ 2 := htrigSq
  rw [eq_div_iff hden]
  calc
    (d.transformedZeta - -Real.cos (d.centralComplementAngle θ)) *
        (1 + -Real.cos (d.centralComplementAngle θ)) *
          chebyshevU d.m (Real.cos (d.centralComplementAngle θ)) ^ 2 *
            (1 + Real.cos (d.centralComplementAngle θ)) =
        (d.transformedZeta + Real.cos (d.centralComplementAngle θ)) *
          (chebyshevU d.m
              (Real.cos (d.centralComplementAngle θ)) ^ 2 *
            ((1 - Real.cos (d.centralComplementAngle θ)) *
              (1 + Real.cos (d.centralComplementAngle θ)))) := by ring
    _ = (d.transformedZeta + Real.cos (d.centralComplementAngle θ)) *
          (chebyshevU d.m
              (Real.cos (d.centralComplementAngle θ)) ^ 2 *
            Real.sin (d.centralComplementAngle θ) ^ 2) := by
      rw [hsinFactor]
    _ = (d.transformedZeta + Real.cos (d.centralComplementAngle θ)) *
        Real.sin (((d.m + 1 : Nat) : Real) *
          d.centralComplementAngle θ) ^ 2 := by
      rw [htrigProduct]

/-- In the negative-slope case, the inner transformed level is strictly
below the level at `rho`. -/
theorem abs_transformedCentralWeight_inner_lt_rho_of_a_lt_rho
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper)
    (haRho : d.a < d.transformedRho) :
    |d.transformedCentralWeight (d.transformedInner θ)| <
      d.transformedCentralWeight d.transformedRho := by
  let phi := d.centralComplementAngle θ
  let cphi := Real.cos phi
  let omega := d.transformedFirstNode
  let zeta := d.transformedZeta
  have hphi := centralComplementAngle_mem d θ hleft hright
  have hupperPi : Real.pi / (((d.m + 1 : Nat) : Real)) ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity : (0 : Real) < (d.m + 1 : Nat))]
    have hmcast : (1 : Real) ≤ (d.m + 1 : Nat) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le d.m)
    nlinarith [Real.pi_pos]
  have homegaLt : omega < cphi := by
    unfold omega transformedFirstNode centralChebyshevFirstNode cphi
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hphi.1.le hupperPi hphi.2
  have homega0 : 0 ≤ omega := transformedFirstNode_nonneg d
  have homegaLtOne : omega < 1 := transformedFirstNode_lt_one d
  have hcphi0 : 0 < cphi := homega0.trans_lt homegaLt
  have hzetaOne : 1 < zeta := one_lt_transformedZeta d
  have hweightFormula :=
    transformedCentralWeight_inner_sq_complement d θ hleft hright
  have hsinSq :
      Real.sin (((d.m + 1 : Nat) : Real) * phi) ^ 2 ≤ 1 :=
    Real.sin_sq_le_one _
  have hfirst :
      d.transformedCentralWeight (d.transformedInner θ) ^ 2 <
        (zeta + omega) / (1 + omega) := by
    have hlevelLe :
        d.transformedCentralWeight (d.transformedInner θ) ^ 2 ≤
          (zeta + cphi) / (1 + cphi) := by
      rw [hweightFormula]
      apply div_le_div_of_nonneg_right
      · exact mul_le_of_le_one_right
          (by linarith [hzetaOne]) hsinSq
      · linarith
    have hratio :
        (zeta + cphi) / (1 + cphi) <
          (zeta + omega) / (1 + omega) := by
      rw [div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    exact hlevelLe.trans_lt hratio
  have hsecond :
      (zeta + omega) / (1 + omega) < (1 + d.a) / (2 * d.a) := by
    have homegaPlus : 0 < 1 + omega := by linarith
    have haTwo : 0 < 2 * d.a := mul_pos (by norm_num) d.ha0
    have hstrictProduct :
        0 < (1 - d.a) * (d.a + omega) :=
      mul_pos (sub_pos.mpr d.ha1) (by linarith)
    unfold zeta transformedZeta
    rw [div_lt_div_iff₀ homegaPlus haTwo]
    field_simp [d.ha0.ne']
    nlinarith
  have hthird :
      (1 + d.a) / (2 * d.a) <
      (1 + d.transformedRho) / (2 * d.a) := by
    exact div_lt_div_of_pos_right (by linarith)
      (mul_pos (by norm_num) d.ha0)
  have hsquares :
      d.transformedCentralWeight (d.transformedInner θ) ^ 2 <
        d.transformedCentralWeight d.transformedRho ^ 2 := by
    rw [transformedCentralWeight_rho_sq]
    exact (hfirst.trans hsecond).trans hthird
  exact (sq_lt_sq₀
    (abs_nonneg (d.transformedCentralWeight (d.transformedInner θ)))
    (transformedCentralWeight_pos d (transformedRho_mem d)).le).mp
      (by simpa only [sq_abs] using hsquares)

/-- Direct derivative form for the literal logarithm of `V_m`. -/
theorem hasDerivAt_log_transformedCentralWeight
    (d : OddCentralChordData) {t : Real}
    (ht : t ∈ Ioo d.transformedFirstNode d.transformedZeta) :
    HasDerivAt (fun u : Real =>
      Real.log (d.transformedCentralWeight u))
      (d.transformedCentralLogSlope t) t := by
  apply (hasDerivAt_transformedCentralLogProfile d ht).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
  exact log_transformedCentralWeight_eq_profile d hu

/-- From the unique transformed lobe maximum to the radical endpoint,
`log V_m` is strictly decreasing. -/
theorem log_transformedCentralWeight_strictAntiOn_endpointSide
    (d : OddCentralChordData) :
    StrictAntiOn
      (fun t : Real => Real.log (d.transformedCentralWeight t))
      (Ioo d.transformedOuterLobeMaximizer d.transformedZeta) := by
  have hp := transformedOuterLobeMaximizer_mem d
  have hpSlope :=
    transformedCentralLogSlope_outerLobeMaximizer_eq_zero d
  apply strictAntiOn_of_deriv_neg
    (convex_Ioo d.transformedOuterLobeMaximizer d.transformedZeta)
  · intro t ht
    have htOuter : t ∈ Ioo d.transformedFirstNode d.transformedZeta :=
      ⟨hp.1.trans ht.1, ht.2⟩
    exact (hasDerivAt_log_transformedCentralWeight d htOuter).continuousAt.continuousWithinAt
  · intro t ht
    have htSide : t ∈ Ioo d.transformedOuterLobeMaximizer
        d.transformedZeta := by
      simpa only [interior_Ioo] using ht
    have htOuter : t ∈ Ioo d.transformedFirstNode d.transformedZeta :=
      ⟨hp.1.trans htSide.1, htSide.2⟩
    rw [(hasDerivAt_log_transformedCentralWeight d htOuter).deriv]
    have hlt := transformedCentralLogSlope_strictAntiOn d
      hp htOuter htSide.1
    simpa only [hpSlope] using hlt

/-- The selected endpoint-side outer root always lies at or beyond the
reference root `rho_m`.  This is the descending-root comparison in lines
1531--1566. -/
theorem transformedRho_le_transformedOuter
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper) :
    d.transformedRho ≤ d.transformedOuter θ := by
  let p := d.transformedOuterLobeMaximizer
  let rho := d.transformedRho
  let tout := d.transformedOuter θ
  have hp := transformedOuterLobeMaximizer_mem d
  have hrho := transformedRho_mem d
  have htout := transformedOuter_mem d θ hleft hright
  have hpTout : p < tout :=
    transformedOuterLobeMaximizer_lt_transformedOuter d θ hleft hright
  have hpSlope : d.transformedCentralLogSlope p = 0 :=
    transformedCentralLogSlope_outerLobeMaximizer_eq_zero d
  by_cases hslope : 0 ≤ d.transformedCentralLogSlope rho
  · have hrhoP : rho ≤ p := by
      by_contra hnot
      have hpRho : p < rho := lt_of_not_ge hnot
      have hanti := transformedCentralLogSlope_strictAntiOn d
        hp hrho hpRho
      rw [hpSlope] at hanti
      exact (not_lt_of_ge hslope) hanti
    exact hrhoP.trans hpTout.le
  · have hslopeNeg : d.transformedCentralLogSlope rho < 0 :=
      lt_of_not_ge hslope
    have haRho : d.a < rho :=
      a_lt_transformedRho_of_logSlope_neg d hslopeNeg
    have hpRho : p < rho := by
      by_contra hnot
      have hrhoP : rho ≤ p := le_of_not_gt hnot
      rcases hrhoP.eq_or_lt with hEq | hlt
      · rw [hEq, hpSlope] at hslopeNeg
        exact (lt_irrefl 0 hslopeNeg)
      · have hanti := transformedCentralLogSlope_strictAntiOn d
          hrho hp hlt
        rw [hpSlope] at hanti
        exact (not_lt_of_ge hslopeNeg.le) hanti
    have hlevel :=
      transformedCentralWeight_outer_eq_abs_inner d θ hleft hright
    have hinner :=
      abs_transformedCentralWeight_inner_lt_rho_of_a_lt_rho
        d θ hleft hright haRho
    have houtLt :
        d.transformedCentralWeight tout <
          d.transformedCentralWeight rho := by
      rw [hlevel]
      exact hinner
    by_contra hnot
    have htoutRho : tout < rho := lt_of_not_ge hnot
    have hlogAnti :=
      log_transformedCentralWeight_strictAntiOn_endpointSide d
        ⟨hpTout, htout.2⟩ ⟨hpRho, hrho.2⟩ htoutRho
    have hVrho : 0 < d.transformedCentralWeight rho :=
      transformedCentralWeight_pos d hrho
    have hVout : 0 < d.transformedCentralWeight tout :=
      transformedCentralWeight_pos d htout
    have hreverse :
        d.transformedCentralWeight rho <
          d.transformedCentralWeight tout :=
      (Real.log_lt_log_iff hVrho hVout).mp hlogAnti
    exact (not_lt_of_ge houtLt.le) hreverse

/-! ## Strict actual-height comparison -/

/-- Every interior positive-central chord has height strictly below the
actual bidiagonal height `c_m`. -/
theorem outerChordFamilyS_lt_centralBidiagonalHeight
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper) :
    outerChordFamilyS d.positiveGap θ <
      centralBidiagonalHeight d.m d.a := by
  let tin := d.transformedInner θ
  let tout := d.transformedOuter θ
  let rho := d.transformedRho
  let zeta := d.transformedZeta
  have hin := transformedInner_mem d θ hleft hright
  have hout := transformedOuter_mem d θ hleft hright
  have hrho := transformedRho_mem d
  have hrhoOut : rho ≤ tout :=
    transformedRho_le_transformedOuter d θ hleft hright
  have hzetaPlus : 0 < zeta + 1 := by
    dsimp only [zeta]
    linarith [one_lt_transformedZeta d]
  have haPos : 0 < 2 * d.a := mul_pos (by norm_num) d.ha0
  have houterFactor : 0 < zeta - tout := sub_pos.mpr hout.2
  have hrhoFactor : 0 < zeta - rho := sub_pos.mpr hrho.2
  have hinnerFactor : zeta - tin < zeta + 1 := by
    linarith [hin.1]
  have hproduct :
      (zeta - tout) * (zeta - tin) <
        (zeta - rho) * (zeta + 1) := by
    have hfirst : zeta - tout ≤ zeta - rho := by linarith
    have hinnerPos : 0 < zeta - tin := by
      linarith [hin.2, transformedFirstNode_nonneg d,
        one_lt_transformedZeta d]
    calc
      (zeta - tout) * (zeta - tin) ≤
          (zeta - rho) * (zeta - tin) :=
        mul_le_mul_of_nonneg_right hfirst hinnerPos.le
      _ < (zeta - rho) * (zeta + 1) :=
        mul_lt_mul_of_pos_left hinnerFactor hrhoFactor
  have hsSq :
      outerChordFamilyS d.positiveGap θ ^ 2 <
        2 * d.a * (zeta - rho) := by
    rw [outerChordFamilyS_sq_eq_transformed d θ hleft hright]
    dsimp only [tin, tout, rho, zeta]
    rw [div_lt_iff₀ hzetaPlus]
    nlinarith
  have hcSq :
      2 * d.a * (zeta - rho) =
        centralBidiagonalHeight d.m d.a ^ 2 := by
    dsimp only [zeta, rho, transformedZeta, transformedRho]
    exact two_mul_a_mul_centralZeta_sub_rho_eq_height_sq
      d.m d.hm d.a d.ha0 d.ha1
  have hheightPos := centralBidiagonalHeight_pos d.m d.hm d.a d.ha0
  apply (sq_lt_sq₀
    (outerChordS_nonneg d.ha0 θ
      (outerChordFamilyZ d.positiveGap θ))
    hheightPos.le).mp
  rw [← hcSq]
  exact hsSq

/-- Actual finite-dimensional Euclidean least-singular-value form of the
strict upper comparison at every canonical central chord. -/
theorem realGapValue_outerChordFamilyX_lt_centralBidiagonalHeight
    (d : OddCentralChordData) (θ : d.positiveGap.Angle)
    (hleft : d.positiveGap.angleLower < θ)
    (hright : θ < d.positiveGap.angleUpper) :
    realGapValue (2 * d.m + 1) d.a
        (outerChordFamilyX d.positiveGap θ) <
      centralBidiagonalHeight d.m d.a := by
  rw [realGapValue_outerChordFamilyX_positiveCentral
    d θ hleft hright]
  exact outerChordFamilyS_lt_centralBidiagonalHeight
    d θ hleft hright

/-- Every point of the actual positive zero-adjacent gap of `A_(2m+1)` has
least singular value strictly below `c_m`. -/
theorem realGapValue_lt_centralBidiagonalHeight_of_mem_positiveCentralGap
    (d : OddCentralChordData) {x : Real}
    (hx : x ∈ positiveHalfSpectralGap d.positiveGap) :
    realGapValue (2 * d.m + 1) d.a x <
      centralBidiagonalHeight d.m d.a := by
  have hclass :=
    positiveHalfSpectralGap_subset_middleBranchRawClassifiedSet
      d.positiveGap hx
  obtain ⟨θ, hleft, hright, _hY, _hZ, hX, _hroot⟩ :=
    exists_outerChordFamily_representation_of_classified d.positiveGap
      ⟨hx, hclass⟩
  rw [hX]
  exact realGapValue_outerChordFamilyX_lt_centralBidiagonalHeight
    d θ hleft hright

end OddCentralChordData

end

end ConnectedPseudospectrum
