import ConnectedPseudospectrum.OddCentralLowerFolded
import ConnectedPseudospectrum.OddCentralZeroSpectrum
import ConnectedPseudospectrum.OddCentralHeight
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The angle estimate in the odd central lower comparison

This module formalizes LaTeX lines 1839--1887.  It compares the central
Chebyshev root with the reference point `cos (pi/(2L+1))`, converts the two
resulting square estimates into strict sine bounds, proves the source's
elementary angle inequality, and places the test abscissa strictly inside
the actual positive central spectral gap.

The printed estimate for `c` tacitly passes from `a` to `sqrt a`.  The
corresponding strict inequality `a < sqrt a`, valid exactly under
`0 < a < 1`, is stated explicitly below and is used only in that estimate.
-/

namespace ConnectedPseudospectrum

open Set
open scoped BigOperators Interval

noncomputable section

namespace OddCentralChordData

/-! ## The reference Chebyshev value -/

/-- The source's reference value
`u_ref=U_{L-1}(cos (pi/(2L+1)))`. -/
def lowerCentralReferenceUMinus (d : OddCentralChordData) : Real :=
  chebyshevU d.m d.lowerCentralReferenceRho

/-- The reference Chebyshev value is positive. -/
theorem lowerCentralReferenceUMinus_pos (d : OddCentralChordData) :
    0 < d.lowerCentralReferenceUMinus := by
  unfold lowerCentralReferenceUMinus
  exact chebyshevU_pos_above_centralFirstNode d.m d.hm
    ((centralChebyshevFirstNode_lt_succ d.m).trans
      (lowerCentralReferenceRho_above_succNode d))

/-- At the reference point the adjacent Chebyshev values agree. -/
theorem lowerCentralReferenceUPlus_eq_UMinus
    (d : OddCentralChordData) :
    chebyshevU (d.m + 1) d.lowerCentralReferenceRho =
      d.lowerCentralReferenceUMinus := by
  have hratio := lowerCentralRatio_reference_eq_one d
  unfold centralChebyshevRatio at hratio
  rw [show (((d.m + 1 : Nat) : Int) - 1) = (d.m : Int) by omega]
    at hratio
  have hplus :
      0 < chebyshevU (d.m + 1) d.lowerCentralReferenceRho :=
    chebyshevU_pos_above_centralFirstNode (d.m + 1) (by omega)
      (lowerCentralReferenceRho_above_succNode d)
  unfold lowerCentralReferenceUMinus
  exact ((div_eq_one_iff_eq hplus.ne').mp hratio).symm

/-- The quadratic Chebyshev invariant gives the source identity
`u_ref^{-2}=2(1-rho_ref)`. -/
theorem lowerCentralReferenceUMinus_inv_sq
    (d : OddCentralChordData) :
    1 / d.lowerCentralReferenceUMinus ^ 2 =
      2 * (1 - d.lowerCentralReferenceRho) := by
  have hU := lowerCentralReferenceUPlus_eq_UMinus d
  have hEq :
      (1 : Real) *
          chebyshevU (d.m + 1) d.lowerCentralReferenceRho =
        chebyshevU (((d.m + 1 : Nat) : Int) - 1)
          d.lowerCentralReferenceRho := by
    rw [one_mul, show (((d.m + 1 : Nat) : Int) - 1) = (d.m : Int) by omega]
    exact hU
  have hinv := centralRhoLambda_eq_inv_sq
    (d.m + 1) 1 d.lowerCentralReferenceRho hEq
  have hindex : (((d.m + 1 : Nat) : Int)) = (d.m : Int) + 1 := by
    omega
  rw [hindex, hU] at hinv
  unfold centralRhoLambda at hinv
  nlinarith

/-- Every factor in the nodal product is strictly larger at `rho` than at
`rho_ref`; hence `u_->u_ref`. -/
theorem lowerCentralReferenceUMinus_lt_UMinus
    (d : OddCentralChordData) :
    d.lowerCentralReferenceUMinus < d.lowerCentralUMinus := by
  have hK : 2 ≤ d.m + 1 := Nat.succ_le_succ d.hm
  have hrefFirst :
      Real.cos (Real.pi / ((d.m + 1 : Nat) : Real)) <
        d.lowerCentralReferenceRho := by
    exact (centralChebyshevFirstNode_lt_succ d.m).trans
      (lowerCentralReferenceRho_above_succNode d)
  have hprod :
      chordNodeProduct (d.m + 1) d.lowerCentralReferenceRho <
        chordNodeProduct (d.m + 1) d.lowerCentralRho := by
    unfold chordNodeProduct
    apply Finset.prod_lt_prod_of_nonempty
    · intro q hq
      exact sub_pos.mpr
        ((chordNode_le_first (d.m + 1) hK hq).trans_lt hrefFirst)
    · intro q hq
      linarith [lowerCentralReferenceRho_lt_Rho d]
    · exact ⟨Real.cos (Real.pi / ((d.m + 1 : Nat) : Real)),
        first_mem_chordNodes (d.m + 1) hK⟩
  have href := chebyshevU_eq_chordNodeProduct
    (d.m + 1) hK d.lowerCentralReferenceRho
  have hrho := chebyshevU_eq_chordNodeProduct
    (d.m + 1) hK d.lowerCentralRho
  simp only [Nat.add_sub_cancel] at href hrho
  unfold lowerCentralReferenceUMinus lowerCentralUMinus
  rw [href, hrho]
  exact mul_lt_mul_of_pos_left hprod (by positivity)

/-! ## The source's `c` and `zeta-rho` comparisons -/

/-- The lower bidiagonal height is the positive quotient `a/u_-`. -/
theorem lowerCentralC_eq_a_div_UMinus (d : OddCentralChordData) :
    d.lowerCentralC = d.a / d.lowerCentralUMinus := by
  have hcentral := (lowerCentralRho_spec d).2
  have hminus := lowerCentralUMinus_pos d
  have hplus := lowerCentralUPlus_pos d
  have hquotient :
      1 / d.lowerCentralUPlus = d.a / d.lowerCentralUMinus := by
    apply (div_eq_div_iff hplus.ne' hminus.ne').2
    simpa only [one_mul] using hcentral.symm
  apply (sq_eq_sq₀ (lowerCentralC_pos d).le
    (div_pos d.ha0 hminus).le).mp
  calc
    d.lowerCentralC ^ 2 = 1 / d.lowerCentralUPlus ^ 2 :=
      lowerCentralC_sq_eq_inv_UPlus_sq d
    _ = (1 / d.lowerCentralUPlus) ^ 2 := by
      simp only [one_div, inv_pow]
    _ = (d.a / d.lowerCentralUMinus) ^ 2 := by rw [hquotient]

/-- The displayed identity `c^2=2a(zeta-rho)`. -/
theorem lowerCentralC_sq_eq_two_a_mul_zeta_sub_rho
    (d : OddCentralChordData) :
    d.lowerCentralC ^ 2 =
      2 * d.a * (d.transformedZeta - d.lowerCentralRho) := by
  rw [lowerCentralC_sq_eq_rhoLambda]
  nlinarith [two_mul_a_mul_lowerCentralZeta d]

/-- The strict comparison printed after `u_->u_ref`:
`zeta-rho<a(1-rho_ref)`. -/
theorem lowerCentralZeta_sub_Rho_lt_a_mul_referenceGap
    (d : OddCentralChordData) :
    d.transformedZeta - d.lowerCentralRho <
      d.a * (1 - d.lowerCentralReferenceRho) := by
  have hrefPos := lowerCentralReferenceUMinus_pos d
  have hminusPos := lowerCentralUMinus_pos d
  have hU := lowerCentralReferenceUMinus_lt_UMinus d
  have hsqU :
      d.lowerCentralReferenceUMinus ^ 2 <
        d.lowerCentralUMinus ^ 2 :=
    (sq_lt_sq₀ hrefPos.le hminusPos.le).2 hU
  have hinv :
      1 / d.lowerCentralUMinus ^ 2 <
        1 / d.lowerCentralReferenceUMinus ^ 2 :=
    one_div_lt_one_div_of_lt (sq_pos_of_pos hrefPos) hsqU
  have hscaled := mul_lt_mul_of_pos_left hinv (sq_pos_of_pos d.ha0)
  have hc := lowerCentralC_sq_eq_two_a_mul_zeta_sub_rho d
  have hcquotient :
      d.lowerCentralC ^ 2 =
        d.a ^ 2 / d.lowerCentralUMinus ^ 2 := by
    rw [lowerCentralC_eq_a_div_UMinus, div_pow]
  have href := lowerCentralReferenceUMinus_inv_sq d
  have hscaled' :
      d.a ^ 2 / d.lowerCentralUMinus ^ 2 <
        d.a ^ 2 / d.lowerCentralReferenceUMinus ^ 2 := by
    calc
      d.a ^ 2 / d.lowerCentralUMinus ^ 2 =
          d.a ^ 2 * (1 / d.lowerCentralUMinus ^ 2) := by ring
      _ < d.a ^ 2 *
          (1 / d.lowerCentralReferenceUMinus ^ 2) := hscaled
      _ = d.a ^ 2 / d.lowerCentralReferenceUMinus ^ 2 := by ring
  have hreferenceScaled :
      d.a ^ 2 / d.lowerCentralReferenceUMinus ^ 2 =
        2 * d.a ^ 2 * (1 - d.lowerCentralReferenceRho) := by
    calc
      d.a ^ 2 / d.lowerCentralReferenceUMinus ^ 2 =
          d.a ^ 2 *
            (1 / d.lowerCentralReferenceUMinus ^ 2) := by ring
      _ = d.a ^ 2 *
          (2 * (1 - d.lowerCentralReferenceRho)) := by rw [href]
      _ = 2 * d.a ^ 2 *
          (1 - d.lowerCentralReferenceRho) := by ring
  have hraw :
      (2 * d.a) * (d.transformedZeta - d.lowerCentralRho) <
        (2 * d.a) *
          (d.a * (1 - d.lowerCentralReferenceRho)) := by
    calc
      (2 * d.a) * (d.transformedZeta - d.lowerCentralRho) =
          d.lowerCentralC ^ 2 := by rw [hc]
      _ = d.a ^ 2 / d.lowerCentralUMinus ^ 2 := hcquotient
      _ < d.a ^ 2 / d.lowerCentralReferenceUMinus ^ 2 := hscaled'
      _ = (2 * d.a) *
          (d.a * (1 - d.lowerCentralReferenceRho)) := by
        rw [hreferenceScaled]
        ring
  have htwo : (0 : Real) < 2 := by norm_num
  exact (mul_lt_mul_iff_right₀ (mul_pos htwo d.ha0)).mp hraw

/-- Since `a<1`, the preceding strict comparison also gives
`zeta-rho<1-rho_ref`. -/
theorem lowerCentralZeta_sub_Rho_lt_referenceGap
    (d : OddCentralChordData) :
    d.transformedZeta - d.lowerCentralRho <
      1 - d.lowerCentralReferenceRho := by
  have hgap : 0 < 1 - d.lowerCentralReferenceRho :=
    sub_pos.mpr (lowerCentralReferenceRho_lt_one d)
  exact (lowerCentralZeta_sub_Rho_lt_a_mul_referenceGap d).trans
    (by
      simpa only [one_mul] using
        mul_lt_mul_of_pos_right d.ha1 hgap)

/-! ## Angles and exact trigonometric identities -/

/-- The source angle `theta=pi/(4L)`. -/
def lowerCentralTheta (d : OddCentralChordData) : Real :=
  Real.pi / (4 * d.lowerCentralLength)

/-- The source decrement `Delta=theta/(2L+1)`. -/
def lowerCentralAngleDelta (d : OddCentralChordData) : Real :=
  d.lowerCentralTheta / (2 * d.lowerCentralLength + 1)

/-- The comparison mesh `2 sqrt(a) sin(pi/(2L))`. -/
def lowerCentralSecondSingularMesh (d : OddCentralChordData) : Real :=
  2 * Real.sqrt d.a *
    Real.sin (Real.pi / (2 * d.lowerCentralLength))

/-- The source angle is positive. -/
theorem lowerCentralTheta_pos (d : OddCentralChordData) :
    0 < d.lowerCentralTheta := by
  unfold lowerCentralTheta
  exact div_pos Real.pi_pos
    (mul_pos (by norm_num) (lowerCentralLength_pos d))

/-- Since `L≥2`, the source angle lies below `pi/8`. -/
theorem lowerCentralTheta_le_pi_div_eight
    (d : OddCentralChordData) :
    d.lowerCentralTheta ≤ Real.pi / 8 := by
  unfold lowerCentralTheta
  rw [div_le_div_iff_of_pos_left Real.pi_pos
    (mul_pos (by norm_num) (lowerCentralLength_pos d))
    (by norm_num : (0 : Real) < 8)]
  nlinarith [lowerCentralLength_ge_two d]

/-- In particular, the source angle is below `pi`. -/
theorem lowerCentralTheta_lt_pi (d : OddCentralChordData) :
    d.lowerCentralTheta < Real.pi := by
  linarith [lowerCentralTheta_le_pi_div_eight d, Real.pi_pos]

/-- The source angle decrement is positive. -/
theorem lowerCentralAngleDelta_pos (d : OddCentralChordData) :
    0 < d.lowerCentralAngleDelta := by
  unfold lowerCentralAngleDelta
  exact div_pos (lowerCentralTheta_pos d)
    (by nlinarith [lowerCentralLength_pos d])

/-- The source angle decrement is strictly smaller than `theta`. -/
theorem lowerCentralAngleDelta_lt_Theta
    (d : OddCentralChordData) :
    d.lowerCentralAngleDelta < d.lowerCentralTheta := by
  unfold lowerCentralAngleDelta
  exact div_lt_self (lowerCentralTheta_pos d)
    (by nlinarith [lowerCentralLength_pos d])

/-- Thus the shifted angle `theta-Delta` is positive. -/
theorem lowerCentralTheta_sub_Delta_pos
    (d : OddCentralChordData) :
    0 < d.lowerCentralTheta - d.lowerCentralAngleDelta :=
  sub_pos.mpr (lowerCentralAngleDelta_lt_Theta d)

/-- Doubling `theta` gives the comparison-mesh angle. -/
theorem two_mul_lowerCentralTheta (d : OddCentralChordData) :
    2 * d.lowerCentralTheta =
      Real.pi / (2 * d.lowerCentralLength) := by
  unfold lowerCentralTheta
  field_simp [(lowerCentralLength_pos d).ne']
  ring

/-- The reference angle is twice `theta-Delta`. -/
theorem two_mul_lowerCentralTheta_sub_Delta
    (d : OddCentralChordData) :
    2 * (d.lowerCentralTheta - d.lowerCentralAngleDelta) =
      Real.pi / (2 * d.lowerCentralLength + 1) := by
  unfold lowerCentralAngleDelta lowerCentralTheta
  have hL := (lowerCentralLength_pos d).ne'
  have hden : 2 * d.lowerCentralLength + 1 ≠ 0 := by
    nlinarith [lowerCentralLength_pos d]
  field_simp [hL, hden]
  ring

/-- `Delta_omega=2 sin^2(theta)`. -/
theorem lowerCentralOmegaDelta_eq_two_mul_sin_sq_Theta
    (d : OddCentralChordData) :
    d.lowerCentralOmegaDelta =
      2 * Real.sin d.lowerCentralTheta ^ 2 := by
  unfold lowerCentralOmegaDelta lowerCentralOmega
  rw [← two_mul_lowerCentralTheta d, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq d.lowerCentralTheta]

/-- `1-rho_ref=2 sin^2(theta-Delta)`. -/
theorem one_sub_lowerCentralReferenceRho_eq_two_mul_sin_sq
    (d : OddCentralChordData) :
    1 - d.lowerCentralReferenceRho =
      2 * Real.sin
        (d.lowerCentralTheta - d.lowerCentralAngleDelta) ^ 2 := by
  unfold lowerCentralReferenceRho
  rw [← two_mul_lowerCentralTheta_sub_Delta d, Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq
    (d.lowerCentralTheta - d.lowerCentralAngleDelta)]

/-- The sine of the source angle is positive. -/
theorem lowerCentralSinTheta_pos (d : OddCentralChordData) :
    0 < Real.sin d.lowerCentralTheta :=
  Real.sin_pos_of_pos_of_lt_pi (lowerCentralTheta_pos d)
    (lowerCentralTheta_lt_pi d)

/-- The sine of the shifted source angle is positive. -/
theorem lowerCentralSinThetaSubDelta_pos
    (d : OddCentralChordData) :
    0 < Real.sin
      (d.lowerCentralTheta - d.lowerCentralAngleDelta) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact lowerCentralTheta_sub_Delta_pos d
  · linarith [lowerCentralAngleDelta_pos d,
      lowerCentralTheta_lt_pi d]

/-- Positive square roots in the reference identity give
`u_ref^{-1}=2 sin(theta-Delta)`. -/
theorem one_div_lowerCentralReferenceUMinus_eq_two_mul_sin
    (d : OddCentralChordData) :
    1 / d.lowerCentralReferenceUMinus =
      2 * Real.sin
        (d.lowerCentralTheta - d.lowerCentralAngleDelta) := by
  apply (sq_eq_sq₀
    (one_div_pos.mpr (lowerCentralReferenceUMinus_pos d)).le
    (mul_nonneg (by norm_num)
      (lowerCentralSinThetaSubDelta_pos d).le)).mp
  calc
    (1 / d.lowerCentralReferenceUMinus) ^ 2 =
        1 / d.lowerCentralReferenceUMinus ^ 2 := by
      simp only [one_div, inv_pow]
    _ = 2 * (1 - d.lowerCentralReferenceRho) :=
      lowerCentralReferenceUMinus_inv_sq d
    _ = (2 * Real.sin
        (d.lowerCentralTheta - d.lowerCentralAngleDelta)) ^ 2 := by
      rw [one_sub_lowerCentralReferenceRho_eq_two_mul_sin_sq]
      ring

/-! ## Strict sine bounds for `c` and `x_*` -/

/-- The source's implicit weakening `a<sqrt(a)`, isolated with its exact
hypotheses. -/
theorem lowerCentral_a_lt_sqrt (d : OddCentralChordData) :
    d.a < Real.sqrt d.a := by
  apply (sq_lt_sq₀ d.ha0.le (Real.sqrt_nonneg d.a)).mp
  rw [Real.sq_sqrt d.ha0.le]
  nlinarith [mul_pos d.ha0 (sub_pos.mpr d.ha1)]

/-- The printed strict bound
`c<2a sin(theta-Delta)` before the source weakens `a` to `sqrt(a)`. -/
theorem lowerCentralC_lt_two_a_mul_sin_Theta_sub_Delta
    (d : OddCentralChordData) :
    d.lowerCentralC <
      2 * d.a *
        Real.sin (d.lowerCentralTheta - d.lowerCentralAngleDelta) := by
  have hrefPos := lowerCentralReferenceUMinus_pos d
  have hinv :
      1 / d.lowerCentralUMinus <
        1 / d.lowerCentralReferenceUMinus :=
    one_div_lt_one_div_of_lt hrefPos
      (lowerCentralReferenceUMinus_lt_UMinus d)
  have hfirst :
      d.a / d.lowerCentralUMinus <
        d.a / d.lowerCentralReferenceUMinus := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_lt_mul_of_pos_left hinv d.ha0
  rw [lowerCentralC_eq_a_div_UMinus]
  calc
    d.a / d.lowerCentralUMinus <
        d.a / d.lowerCentralReferenceUMinus := hfirst
    _ = 2 * d.a *
        Real.sin (d.lowerCentralTheta - d.lowerCentralAngleDelta) := by
      rw [div_eq_mul_inv, ← one_div,
        one_div_lowerCentralReferenceUMinus_eq_two_mul_sin]
      ring

/-- The printed bound `c<2 sqrt(a) sin(theta-Delta)`.  This is the sole
place where the proof uses the implicit weakening `a<sqrt(a)`. -/
theorem lowerCentralC_lt_two_sqrt_mul_sin_Theta_sub_Delta
    (d : OddCentralChordData) :
    d.lowerCentralC <
      2 * Real.sqrt d.a *
        Real.sin (d.lowerCentralTheta - d.lowerCentralAngleDelta) := by
  calc
    d.lowerCentralC <
        2 * d.a *
          Real.sin (d.lowerCentralTheta - d.lowerCentralAngleDelta) :=
      lowerCentralC_lt_two_a_mul_sin_Theta_sub_Delta d
    _ = d.a *
        (2 * Real.sin
          (d.lowerCentralTheta - d.lowerCentralAngleDelta)) := by ring
    _ < Real.sqrt d.a *
        (2 * Real.sin
          (d.lowerCentralTheta - d.lowerCentralAngleDelta)) :=
      mul_lt_mul_of_pos_right (lowerCentral_a_lt_sqrt d)
        (mul_pos (by norm_num) (lowerCentralSinThetaSubDelta_pos d))
    _ = 2 * Real.sqrt d.a *
        Real.sin (d.lowerCentralTheta - d.lowerCentralAngleDelta) := by ring

/-- The definition of `x_*` gives the source's displayed quotient identity. -/
theorem lowerCentralXStar_sq_div_two_a
    (d : OddCentralChordData) :
    d.lowerCentralXStar ^ 2 / (2 * d.a) =
      d.lowerCentralOmegaDelta *
        ((d.lowerCentralRho + d.lowerCentralOmega) /
          (d.transformedZeta + d.lowerCentralOmega)) := by
  rw [lowerCentralXStar_sq]
  unfold lowerCentralXStarSq
  field_simp [d.ha0.ne', (lowerCentralZeta_add_Omega_pos d).ne']

/-- The folded radicand ratio is strictly below one. -/
theorem lowerCentralXStar_ratio_lt_one (d : OddCentralChordData) :
    (d.lowerCentralRho + d.lowerCentralOmega) /
        (d.transformedZeta + d.lowerCentralOmega) < 1 := by
  apply (div_lt_one (lowerCentralZeta_add_Omega_pos d)).2
  linarith [lowerCentralZeta_sub_Rho_pos d]

/-- The second printed strict bound `x_*<2 sqrt(a) sin(theta)`. -/
theorem lowerCentralXStar_lt_two_sqrt_mul_sin_Theta
    (d : OddCentralChordData) :
    d.lowerCentralXStar <
      2 * Real.sqrt d.a * Real.sin d.lowerCentralTheta := by
  have hbase : 0 < 2 * d.a * d.lowerCentralOmegaDelta := by
    exact mul_pos (mul_pos (by norm_num) d.ha0)
      (lowerCentralOmegaDelta_pos d)
  have hscaled := mul_lt_mul_of_pos_left
    (lowerCentralXStar_ratio_lt_one d) hbase
  have hsqrt : Real.sqrt d.a ^ 2 = d.a :=
    Real.sq_sqrt d.ha0.le
  have hsquare :
      d.lowerCentralXStar ^ 2 <
        (2 * Real.sqrt d.a * Real.sin d.lowerCentralTheta) ^ 2 := by
    calc
      d.lowerCentralXStar ^ 2 = d.lowerCentralXStarSq :=
        lowerCentralXStar_sq d
      _ = (2 * d.a * d.lowerCentralOmegaDelta) *
          ((d.lowerCentralRho + d.lowerCentralOmega) /
            (d.transformedZeta + d.lowerCentralOmega)) := by
        unfold lowerCentralXStarSq
        ring
      _ < (2 * d.a * d.lowerCentralOmegaDelta) * 1 := hscaled
      _ = (2 * Real.sqrt d.a *
          Real.sin d.lowerCentralTheta) ^ 2 := by
        rw [lowerCentralOmegaDelta_eq_two_mul_sin_sq_Theta]
        nlinarith
  exact (sq_lt_sq₀ (lowerCentralXStar_pos d).le
    (mul_pos
      (mul_pos (by norm_num) (Real.sqrt_pos.2 d.ha0))
      (lowerCentralSinTheta_pos d)).le).mp hsquare

/-! ## The exact elementary angle inequality -/

/-- The first source deficit estimate
`2 sin(theta)-sin(2 theta)<theta^3`. -/
theorem two_sin_Theta_sub_sin_two_Theta_lt_cube
    (d : OddCentralChordData) :
    2 * Real.sin d.lowerCentralTheta -
        Real.sin (2 * d.lowerCentralTheta) <
      d.lowerCentralTheta ^ 3 := by
  have htheta := lowerCentralTheta_pos d
  have hsin := Real.sin_lt htheta
  have hcosLower :=
    Real.one_sub_sq_div_two_lt_cos htheta.ne'
  have hcosLtOne : Real.cos d.lowerCentralTheta < 1 := by
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
      (le_refl (0 : Real)) (lowerCentralTheta_lt_pi d).le htheta
    simpa only [Real.cos_zero] using hcos
  have hgapPos : 0 < 1 - Real.cos d.lowerCentralTheta :=
    sub_pos.mpr hcosLtOne
  have hgapLt :
      1 - Real.cos d.lowerCentralTheta <
        d.lowerCentralTheta ^ 2 / 2 := by
    linarith
  have hfirst := mul_lt_mul_of_pos_right hsin hgapPos
  have hsecond := mul_lt_mul_of_pos_left hgapLt htheta
  have hproduct :
      Real.sin d.lowerCentralTheta *
          (1 - Real.cos d.lowerCentralTheta) <
        d.lowerCentralTheta * (d.lowerCentralTheta ^ 2 / 2) :=
    hfirst.trans hsecond
  rw [Real.sin_two_mul]
  nlinarith

/-- On `[theta-Delta,theta]`, integrating the strict cosine comparison gives
`Delta cos(theta)<sin(theta)-sin(theta-Delta)`. -/
theorem Delta_mul_cos_Theta_lt_sin_difference
    (d : OddCentralChordData) :
    d.lowerCentralAngleDelta * Real.cos d.lowerCentralTheta <
      Real.sin d.lowerCentralTheta -
        Real.sin (d.lowerCentralTheta - d.lowerCentralAngleDelta) := by
  have hleft := lowerCentralTheta_sub_Delta_pos d
  have hlt := lowerCentralAngleDelta_pos d
  have hab :
      d.lowerCentralTheta - d.lowerCentralAngleDelta <
        d.lowerCentralTheta := by
    linarith
  have hthetaPi := (lowerCentralTheta_lt_pi d).le
  have hintegral :
      (∫ _ in
          (d.lowerCentralTheta - d.lowerCentralAngleDelta)..
            d.lowerCentralTheta,
        Real.cos d.lowerCentralTheta) <
      ∫ u in
          (d.lowerCentralTheta - d.lowerCentralAngleDelta)..
            d.lowerCentralTheta,
        Real.cos u := by
    refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hab ?_ ?_ ?_ ?_
    · exact continuousOn_const
    · exact Real.continuous_cos.continuousOn
    · intro u hu
      exact Real.cos_le_cos_of_nonneg_of_le_pi
        (hleft.le.trans hu.1.le) hthetaPi hu.2
    · refine ⟨d.lowerCentralTheta - d.lowerCentralAngleDelta,
        ⟨le_rfl, hab.le⟩, ?_⟩
      exact Real.cos_lt_cos_of_nonneg_of_le_pi hleft.le hthetaPi
        hab
  simp only [intervalIntegral.integral_const, smul_eq_mul,
    integral_cos] at hintegral
  nlinarith

/-- The source's numerical chain proves
`theta(pi+2theta)<2 cos(theta)`. -/
theorem Theta_mul_pi_add_two_Theta_lt_two_cos
    (d : OddCentralChordData) :
    d.lowerCentralTheta *
        (Real.pi + 2 * d.lowerCentralTheta) <
      2 * Real.cos d.lowerCentralTheta := by
  have hthetaPos := lowerCentralTheta_pos d
  have hthetaLe := lowerCentralTheta_le_pi_div_eight d
  have hthetaSq :
      d.lowerCentralTheta ^ 2 ≤ (Real.pi / 8) ^ 2 :=
    (sq_le_sq₀ hthetaPos.le (by positivity)).2 hthetaLe
  have htwoSub :
      (59 : Real) / 32 < 2 - d.lowerCentralTheta ^ 2 := by
    nlinarith [pi_sq_lt_ten]
  have hcosTaylor :=
    Real.one_sub_sq_div_two_lt_cos hthetaPos.ne'
  have hcos :
      2 - d.lowerCentralTheta ^ 2 <
        2 * Real.cos d.lowerCentralTheta := by
    nlinarith
  have hsum :
      Real.pi + 2 * d.lowerCentralTheta ≤ 5 * Real.pi / 4 := by
    nlinarith
  have hmul :
      d.lowerCentralTheta *
          (Real.pi + 2 * d.lowerCentralTheta) ≤
        (Real.pi / 8) * (5 * Real.pi / 4) := by
    exact mul_le_mul hthetaLe hsum
      (by positivity : 0 ≤ Real.pi + 2 * d.lowerCentralTheta)
      (by positivity : 0 ≤ Real.pi / 8)
  have hupper :
      d.lowerCentralTheta *
          (Real.pi + 2 * d.lowerCentralTheta) <
        (25 : Real) / 16 := by
    calc
      d.lowerCentralTheta *
          (Real.pi + 2 * d.lowerCentralTheta) ≤
          (Real.pi / 8) * (5 * Real.pi / 4) := hmul
      _ < (25 : Real) / 16 := by
        nlinarith [pi_sq_lt_ten]
  have hconstants : (25 : Real) / 16 < 59 / 32 := by norm_num
  exact hupper.trans (hconstants.trans (htwoSub.trans hcos))

/-- The definitions satisfy
`Delta(pi+2theta)=2theta^2`. -/
theorem lowerCentralAngleDelta_mul_pi_add_two_Theta
    (d : OddCentralChordData) :
    d.lowerCentralAngleDelta *
        (Real.pi + 2 * d.lowerCentralTheta) =
      2 * d.lowerCentralTheta ^ 2 := by
  unfold lowerCentralAngleDelta lowerCentralTheta
  have hL := (lowerCentralLength_pos d).ne'
  have hden : 2 * d.lowerCentralLength + 1 ≠ 0 := by
    nlinarith [lowerCentralLength_pos d]
  have hdenComm : 1 + d.lowerCentralLength * 2 ≠ 0 := by
    nlinarith [lowerCentralLength_pos d]
  have hdenFinal : d.lowerCentralLength * 2 + 1 ≠ 0 := by
    nlinarith [lowerCentralLength_pos d]
  field_simp [hL, hden, hdenComm]
  ring

/-- The source's sufficient inequality
`theta^3<Delta cos(theta)`. -/
theorem lowerCentralTheta_cube_lt_Delta_mul_cos
    (d : OddCentralChordData) :
    d.lowerCentralTheta ^ 3 <
      d.lowerCentralAngleDelta * Real.cos d.lowerCentralTheta := by
  have hscaled := mul_lt_mul_of_pos_left
    (Theta_mul_pi_add_two_Theta_lt_two_cos d)
    (lowerCentralAngleDelta_pos d)
  have hidentity := lowerCentralAngleDelta_mul_pi_add_two_Theta d
  have hidentityScaled := congrArg
    (fun t : Real => d.lowerCentralTheta * t) hidentity
  nlinarith

/-- The exact angle inequality used in the strict comparison:
`sin(theta)+sin(theta-Delta)<sin(2theta)`. -/
theorem lowerCentral_exact_angle_inequality
    (d : OddCentralChordData) :
    Real.sin d.lowerCentralTheta +
        Real.sin (d.lowerCentralTheta - d.lowerCentralAngleDelta) <
      Real.sin (2 * d.lowerCentralTheta) := by
  have hfirst := two_sin_Theta_sub_sin_two_Theta_lt_cube d
  have hmiddle := lowerCentralTheta_cube_lt_Delta_mul_cos d
  have hlast := Delta_mul_cos_Theta_lt_sin_difference d
  linarith

/-! ## Comparison with the second singular value and gap membership -/

/-- The comparison mesh is positive. -/
theorem lowerCentralSecondSingularMesh_pos
    (d : OddCentralChordData) :
    0 < d.lowerCentralSecondSingularMesh := by
  unfold lowerCentralSecondSingularMesh
  rw [← two_mul_lowerCentralTheta d]
  have htwoThetaPos : 0 < 2 * d.lowerCentralTheta :=
    mul_pos (by norm_num) (lowerCentralTheta_pos d)
  have htwoThetaLtPi : 2 * d.lowerCentralTheta < Real.pi := by
    nlinarith [lowerCentralTheta_le_pi_div_eight d, Real.pi_pos]
  exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 d.ha0))
    (Real.sin_pos_of_pos_of_lt_pi htwoThetaPos htwoThetaLtPi)

/-- Adding the two strict sine bounds and applying the exact angle
inequality gives the first half of the source claim. -/
theorem lowerCentralXStar_add_C_lt_secondSingularMesh
    (d : OddCentralChordData) :
    d.lowerCentralXStar + d.lowerCentralC <
      d.lowerCentralSecondSingularMesh := by
  have hsum := add_lt_add
    (lowerCentralXStar_lt_two_sqrt_mul_sin_Theta d)
    (lowerCentralC_lt_two_sqrt_mul_sin_Theta_sub_Delta d)
  have hscale : 0 < 2 * Real.sqrt d.a :=
    mul_pos (by norm_num) (Real.sqrt_pos.2 d.ha0)
  have hangle := mul_lt_mul_of_pos_left
    (lowerCentral_exact_angle_inequality d) hscale
  unfold lowerCentralSecondSingularMesh
  rw [← two_mul_lowerCentralTheta d]
  calc
    d.lowerCentralXStar + d.lowerCentralC <
        2 * Real.sqrt d.a * Real.sin d.lowerCentralTheta +
          2 * Real.sqrt d.a *
            Real.sin (d.lowerCentralTheta - d.lowerCentralAngleDelta) :=
      hsum
    _ = 2 * Real.sqrt d.a *
        (Real.sin d.lowerCentralTheta +
          Real.sin (d.lowerCentralTheta - d.lowerCentralAngleDelta)) := by
      ring
    _ < 2 * Real.sqrt d.a *
        Real.sin (2 * d.lowerCentralTheta) := hangle

/-- The exact square difference in the source is `(1-a)^2`. -/
theorem oddCentralSecondSingularSquare_sub_mesh_sq
    (d : OddCentralChordData) :
    oddCentralSecondSingularSquare d.m d.a -
        d.lowerCentralSecondSingularMesh ^ 2 =
      (1 - d.a) ^ 2 := by
  have hangle :
      Real.pi / (((d.m + 1 : Nat) : Real)) =
        2 * (Real.pi / (2 * d.lowerCentralLength)) := by
    rw [lowerCentralLength]
    push_cast
    field_simp [show (d.m : Real) + 1 ≠ 0 by positivity]
  have hsqrt := Real.sq_sqrt d.ha0.le
  have htrig := Real.sin_sq_add_cos_sq
    (Real.pi / (2 * d.lowerCentralLength))
  unfold oddCentralSecondSingularSquare lowerCentralSecondSingularMesh
  rw [hangle, Real.cos_two_mul]
  nlinarith

/-- The mesh is at most the odd matrix's second-smallest singular value. -/
theorem lowerCentralSecondSingularMesh_le_secondSingularValue
    (d : OddCentralChordData) :
    d.lowerCentralSecondSingularMesh ≤
      oddCentralSecondSingularValue d.m d.a := by
  have hrad := oddCentralSecondSingularSquare_pos
    d.m d.ha0 d.ha1
  unfold oddCentralSecondSingularValue
  apply (sq_le_sq₀ (lowerCentralSecondSingularMesh_pos d).le
    (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hrad.le]
  nlinarith [oddCentralSecondSingularSquare_sub_mesh_sq d,
    sq_nonneg (1 - d.a)]

/-- Lines 1839--1887, in the exact two-sided form used downstream. -/
theorem lowerCentralXStar_add_C_lt_mesh_le_secondSingularValue
    (d : OddCentralChordData) :
    d.lowerCentralXStar + d.lowerCentralC <
        d.lowerCentralSecondSingularMesh ∧
      d.lowerCentralSecondSingularMesh ≤
        oddCentralSecondSingularValue d.m d.a :=
  ⟨lowerCentralXStar_add_C_lt_secondSingularMesh d,
    lowerCentralSecondSingularMesh_le_secondSingularValue d⟩

/-- The mesh is exactly the first positive odd spectral endpoint. -/
theorem lowerCentralSecondSingularMesh_eq_oddCentralEndpoint
    (d : OddCentralChordData) :
    d.lowerCentralSecondSingularMesh = oddCentralEndpoint d.m d.a := by
  have hden :
      (((2 * d.m + 2 : Nat) : Real)) =
        2 * d.lowerCentralLength := by
    rw [lowerCentralLength]
    push_cast
    ring
  unfold lowerCentralSecondSingularMesh oddCentralEndpoint
  rw [hden]

/-- The test abscissa is an actual point of the positive central spectral
gap, not merely a positive algebraic square root. -/
theorem lowerCentralXStar_mem_oddCentralPositiveGap
    (d : OddCentralChordData) :
    d.lowerCentralXStar ∈ Ioo 0 (oddCentralEndpoint d.m d.a) := by
  refine ⟨lowerCentralXStar_pos d, ?_⟩
  rw [← lowerCentralSecondSingularMesh_eq_oddCentralEndpoint d]
  have hsum := lowerCentralXStar_add_C_lt_secondSingularMesh d
  linarith [lowerCentralC_pos d]

/-- The same membership expressed using the project's actual positive-half
spectral-gap set. -/
theorem lowerCentralXStar_mem_positiveHalfSpectralGap
    (d : OddCentralChordData) :
    d.lowerCentralXStar ∈ positiveHalfSpectralGap d.positiveGap := by
  rw [positiveHalfSpectralGap_positiveGap]
  simpa only [oddCentralEndpoint] using
    lowerCentralXStar_mem_oddCentralPositiveGap d

end OddCentralChordData

end

end ConnectedPseudospectrum
