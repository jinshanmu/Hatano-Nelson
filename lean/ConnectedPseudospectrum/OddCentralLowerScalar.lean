import ConnectedPseudospectrum.OddCentralUpperComparison
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Scalar inequality for the odd central lower comparison

This module formalizes the scalar argument from `eq:central-D-xi` through
`eq:Delta-upsilon-bounds`.  For the
odd path of order `2m+1` it sets `L=m+1`, introduces the source's quantities
`rho`, `u_-`, `u_+`, `omega_L`, `Delta_omega`, `D_L`, and `xi`, and proves

`(1+omega_L)(1+xi)^2 U_{L-1}(xi)^2
  < (rho+omega_L) D_L`.

The logarithmic-derivative identity is denominator-free, including at
`rho=1`. Positivity uses two cases, `rho>=1` and `rho<1`; the latter follows
from one common positive bracket, without a quadratic endpoint argument.
-/

namespace ConnectedPseudospectrum

open Set Polynomial
open scoped BigOperators

noncomputable section

namespace OddCentralChordData

/-! ## Source parameters -/

/-- The source's lower-comparison index `L=m+1`, cast to `Real`. -/
def lowerCentralLength (d : OddCentralChordData) : Real :=
  ((d.m + 1 : Nat) : Real)

/-- The central continuant root `rho_L`. -/
def lowerCentralRho (d : OddCentralChordData) : Real :=
  centralRho (d.m + 1) d.a

/-- `u_-=U_{L-1}(rho)=U_m(rho)`. -/
def lowerCentralUMinus (d : OddCentralChordData) : Real :=
  chebyshevU d.m d.lowerCentralRho

/-- `u_+=U_L(rho)=U_{m+1}(rho)`. -/
def lowerCentralUPlus (d : OddCentralChordData) : Real :=
  chebyshevU (d.m + 1) d.lowerCentralRho

/-- `omega_L=cos(pi/(2L))`. -/
def lowerCentralOmega (d : OddCentralChordData) : Real :=
  Real.cos (Real.pi / (2 * d.lowerCentralLength))

/-- `Delta_omega=1-omega_L`. -/
def lowerCentralOmegaDelta (d : OddCentralChordData) : Real :=
  1 - d.lowerCentralOmega

/-- `D_L=1+2(rho+omega_L)u_-u_+`. -/
def lowerCentralD (d : OddCentralChordData) : Real :=
  1 + 2 * (d.lowerCentralRho + d.lowerCentralOmega) *
    d.lowerCentralUMinus * d.lowerCentralUPlus

/-- The shifted scalar `xi=rho-Delta_omega/D_L`. -/
def lowerCentralXi (d : OddCentralChordData) : Real :=
  d.lowerCentralRho - d.lowerCentralOmegaDelta / d.lowerCentralD

/-- The reciprocal parameter `b=1/a=u_+/u_-`. -/
def lowerCentralB (d : OddCentralChordData) : Real :=
  d.a⁻¹

/-- `Q_b=b^2-2b rho+1`. -/
def lowerCentralQ (d : OddCentralChordData) : Real :=
  d.lowerCentralB ^ 2 -
    2 * d.lowerCentralB * d.lowerCentralRho + 1

/-- `S_b=b^2+2b omega_L+1`. -/
def lowerCentralS (d : OddCentralChordData) : Real :=
  d.lowerCentralB ^ 2 +
    2 * d.lowerCentralB * d.lowerCentralOmega + 1

/-- The reference point `cos(pi/(2L+1))`. -/
def lowerCentralReferenceRho (d : OddCentralChordData) : Real :=
  Real.cos (Real.pi / (2 * d.lowerCentralLength + 1))

/-- `f_L(t)=(1+t)U_{L-1}(t)`. -/
def lowerCentralF (d : OddCentralChordData) (t : Real) : Real :=
  (1 + t) * chebyshevU d.m t

/-- The root-sum logarithmic derivative of `f_L`. -/
def lowerCentralLogSlope (d : OddCentralChordData) (t : Real) : Real :=
  1 / (1 + t) +
    ∑ q ∈ chordNodes (d.m + 1), (t - q)⁻¹

/-- The source's positive logarithmic slope at `rho`. -/
def lowerCentralSlopeAtRho (d : OddCentralChordData) : Real :=
  d.lowerCentralLogSlope d.lowerCentralRho

/-- The numerator `N` in `eq:N-positive-target`. -/
def lowerCentralN (d : OddCentralChordData) : Real :=
  (d.lowerCentralRho + d.lowerCentralOmega) *
      (d.lowerCentralS +
        2 * d.lowerCentralOmegaDelta * d.lowerCentralQ *
          d.lowerCentralSlopeAtRho) -
    (1 + d.lowerCentralOmega) * (1 + d.lowerCentralRho) ^ 2

/-! ## Elementary positivity and central-root identities -/

theorem lowerCentralLength_eq (d : OddCentralChordData) :
    d.lowerCentralLength = (d.m : Real) + 1 := by
  simp [lowerCentralLength]

theorem lowerCentralLength_ge_two (d : OddCentralChordData) :
    2 ≤ d.lowerCentralLength := by
  rw [lowerCentralLength]
  exact_mod_cast Nat.succ_le_succ d.hm

theorem lowerCentralLength_pos (d : OddCentralChordData) :
    0 < d.lowerCentralLength :=
  lt_of_lt_of_le (by norm_num) (lowerCentralLength_ge_two d)

theorem lowerCentralRho_spec (d : OddCentralChordData) :
    centralChebyshevFirstNode (d.m + 1) < d.lowerCentralRho ∧
      d.a * d.lowerCentralUPlus = d.lowerCentralUMinus := by
  simpa only [lowerCentralRho, lowerCentralUPlus, lowerCentralUMinus,
    show (((d.m + 1 : Nat) : Int) - 1) = (d.m : Int) by omega] using
      centralRho_spec (d.m + 1) (by omega) d.a d.ha0 d.ha1

theorem lowerCentralRho_above_previousNode (d : OddCentralChordData) :
    centralChebyshevFirstNode d.m < d.lowerCentralRho :=
  (centralChebyshevFirstNode_lt_succ d.m).trans
    (lowerCentralRho_spec d).1

theorem lowerCentralUMinus_pos (d : OddCentralChordData) :
    0 < d.lowerCentralUMinus := by
  exact chebyshevU_pos_above_centralFirstNode d.m d.hm
    (lowerCentralRho_above_previousNode d)

theorem lowerCentralUPlus_pos (d : OddCentralChordData) :
    0 < d.lowerCentralUPlus := by
  exact chebyshevU_pos_above_centralFirstNode (d.m + 1) (by omega)
    (lowerCentralRho_spec d).1

theorem lowerCentralB_pos (d : OddCentralChordData) :
    0 < d.lowerCentralB := by
  exact inv_pos.mpr d.ha0

theorem one_lt_lowerCentralB (d : OddCentralChordData) :
    1 < d.lowerCentralB := by
  rw [lowerCentralB, one_lt_inv₀ d.ha0]
  exact d.ha1

theorem lowerCentralUPlus_eq_B_mul_UMinus (d : OddCentralChordData) :
    d.lowerCentralUPlus = d.lowerCentralB * d.lowerCentralUMinus := by
  have hEq := (lowerCentralRho_spec d).2
  rw [lowerCentralB]
  apply (eq_inv_mul_iff_mul_eq₀ d.ha0.ne').2
  exact hEq

theorem lowerCentralOmega_pos (d : OddCentralChordData) :
    0 < d.lowerCentralOmega := by
  have hdenPos : 0 < 2 * d.lowerCentralLength :=
    mul_pos (by norm_num) (lowerCentralLength_pos d)
  have hanglePos :
      0 < Real.pi / (2 * d.lowerCentralLength) :=
    div_pos Real.pi_pos hdenPos
  have hangleLt :
      Real.pi / (2 * d.lowerCentralLength) < Real.pi / 2 := by
    rw [div_lt_div_iff_of_pos_left Real.pi_pos
      hdenPos (by norm_num : (0 : Real) < 2)]
    nlinarith [lowerCentralLength_ge_two d]
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hangleLt⟩

theorem lowerCentralOmega_lt_one (d : OddCentralChordData) :
    d.lowerCentralOmega < 1 := by
  have hdenPos : 0 < 2 * d.lowerCentralLength :=
    mul_pos (by norm_num) (lowerCentralLength_pos d)
  have hanglePos :
      0 < Real.pi / (2 * d.lowerCentralLength) :=
    div_pos Real.pi_pos hdenPos
  have hangleLePi :
      Real.pi / (2 * d.lowerCentralLength) ≤ Real.pi := by
    rw [div_le_iff₀ hdenPos]
    nlinarith [lowerCentralLength_ge_two d, Real.pi_pos]
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
    (le_refl (0 : Real)) hangleLePi hanglePos
  simpa only [Real.cos_zero, lowerCentralOmega] using hcos

theorem lowerCentralOmegaDelta_pos (d : OddCentralChordData) :
    0 < d.lowerCentralOmegaDelta := by
  exact sub_pos.mpr (lowerCentralOmega_lt_one d)

theorem lowerCentralD_gt_one (d : OddCentralChordData) :
    1 < d.lowerCentralD := by
  unfold lowerCentralD
  have hrho : 0 < d.lowerCentralRho := by
    have hnode : 0 ≤ centralChebyshevFirstNode d.m :=
      transformedFirstNode_nonneg d
    exact hnode.trans_lt (lowerCentralRho_above_previousNode d)
  have homega := lowerCentralOmega_pos d
  have huMinus := lowerCentralUMinus_pos d
  have huPlus := lowerCentralUPlus_pos d
  have hprod :
      0 < 2 * (d.lowerCentralRho + d.lowerCentralOmega) *
        d.lowerCentralUMinus * d.lowerCentralUPlus := by positivity
  linarith

theorem lowerCentralD_pos (d : OddCentralChordData) :
    0 < d.lowerCentralD :=
  lt_trans (by norm_num) (lowerCentralD_gt_one d)

theorem lowerCentralQ_invariant (d : OddCentralChordData) :
    d.lowerCentralUMinus ^ 2 * d.lowerCentralQ = 1 := by
  have hinv := chebyshevU_sq_add_sq_sub (d.m + 1) d.lowerCentralRho
  have hindex : (((d.m + 1 : Nat) : Int) - 1) = (d.m : Int) := by omega
  rw [hindex] at hinv
  change d.lowerCentralUPlus ^ 2 + d.lowerCentralUMinus ^ 2 -
      2 * d.lowerCentralRho * d.lowerCentralUPlus *
        d.lowerCentralUMinus = 1 at hinv
  rw [lowerCentralUPlus_eq_B_mul_UMinus d] at hinv
  unfold lowerCentralQ
  nlinarith

theorem lowerCentralQ_pos (d : OddCentralChordData) :
    0 < d.lowerCentralQ := by
  have huSq : 0 < d.lowerCentralUMinus ^ 2 :=
    sq_pos_of_pos (lowerCentralUMinus_pos d)
  nlinarith [lowerCentralQ_invariant d]

theorem lowerCentralS_pos (d : OddCentralChordData) :
    0 < d.lowerCentralS := by
  have hb := lowerCentralB_pos d
  have hw := lowerCentralOmega_pos d
  unfold lowerCentralS
  positivity

theorem lowerCentralD_mul_Q_eq_S (d : OddCentralChordData) :
    d.lowerCentralD * d.lowerCentralQ = d.lowerCentralS := by
  have hinv := lowerCentralQ_invariant d
  have hu := lowerCentralUPlus_eq_B_mul_UMinus d
  unfold lowerCentralQ at hinv
  unfold lowerCentralD lowerCentralS lowerCentralQ at ⊢
  rw [hu]
  linear_combination (norm := ring_nf)
    2 * d.lowerCentralB *
      (d.lowerCentralRho + d.lowerCentralOmega) * hinv

theorem lowerCentralD_eq_S_div_Q (d : OddCentralChordData) :
    d.lowerCentralD = d.lowerCentralS / d.lowerCentralQ := by
  exact (eq_div_iff (lowerCentralQ_pos d).ne').2
    (lowerCentralD_mul_Q_eq_S d)

theorem lowerCentralRho_sub_Xi (d : OddCentralChordData) :
    d.lowerCentralRho - d.lowerCentralXi =
      d.lowerCentralOmegaDelta * d.lowerCentralQ / d.lowerCentralS := by
  rw [lowerCentralXi, lowerCentralD_eq_S_div_Q]
  field_simp [(lowerCentralQ_pos d).ne',
    (lowerCentralS_pos d).ne']
  ring

theorem lowerCentralXi_lt_Rho (d : OddCentralChordData) :
    d.lowerCentralXi < d.lowerCentralRho := by
  apply sub_pos.mp
  rw [lowerCentralRho_sub_Xi]
  exact div_pos
    (mul_pos (lowerCentralOmegaDelta_pos d) (lowerCentralQ_pos d))
    (lowerCentralS_pos d)

/-! ## The reference root and the location of `xi` -/

theorem lowerCentralReference_angle_pos (d : OddCentralChordData) :
    0 < Real.pi / (2 * d.lowerCentralLength + 1) := by
  exact div_pos Real.pi_pos (by
    nlinarith [lowerCentralLength_pos d])

theorem lowerCentralReference_angle_lt_pi_div_two
    (d : OddCentralChordData) :
    Real.pi / (2 * d.lowerCentralLength + 1) < Real.pi / 2 := by
  have hden : 0 < 2 * d.lowerCentralLength + 1 := by
    nlinarith [lowerCentralLength_pos d]
  rw [div_lt_div_iff_of_pos_left Real.pi_pos
    hden (by norm_num : (0 : Real) < 2)]
  nlinarith [lowerCentralLength_ge_two d]

theorem lowerCentralReferenceRho_pos (d : OddCentralChordData) :
    0 < d.lowerCentralReferenceRho := by
  have hanglePos := lowerCentralReference_angle_pos d
  exact Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hanglePos],
      lowerCentralReference_angle_lt_pi_div_two d⟩

theorem lowerCentralReferenceRho_lt_one (d : OddCentralChordData) :
    d.lowerCentralReferenceRho < 1 := by
  have hangleLePi :
      Real.pi / (2 * d.lowerCentralLength + 1) ≤ Real.pi := by
    have hden : 0 < 2 * d.lowerCentralLength + 1 := by
      nlinarith [lowerCentralLength_pos d]
    rw [div_le_iff₀ hden]
    nlinarith [lowerCentralLength_ge_two d, Real.pi_pos]
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
    (le_refl (0 : Real)) hangleLePi
    (lowerCentralReference_angle_pos d)
  simpa only [Real.cos_zero, lowerCentralReferenceRho] using hcos

theorem lowerCentralReferenceRho_above_succNode
    (d : OddCentralChordData) :
    centralChebyshevFirstNode (d.m + 1) <
      d.lowerCentralReferenceRho := by
  unfold centralChebyshevFirstNode lowerCentralReferenceRho
    lowerCentralLength
  push_cast
  have hsmall :
      0 ≤ Real.pi / (2 * ((d.m : Real) + 1) + 1) := by
    positivity
  have hlarge :
      Real.pi / ((d.m : Real) + 1 + 1) ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity :
      (0 : Real) < (d.m : Real) + 1 + 1)]
    have hcast : (1 : Real) ≤ (d.m : Real) + 1 + 1 := by
      have hm : 0 ≤ (d.m : Real) := Nat.cast_nonneg d.m
      linarith
    nlinarith [Real.pi_pos]
  apply Real.cos_lt_cos_of_nonneg_of_le_pi hsmall hlarge
  rw [div_lt_div_iff_of_pos_left Real.pi_pos (by positivity)
    (by positivity)]
  nlinarith

theorem lowerCentralRatio_reference_eq_one (d : OddCentralChordData) :
    centralChebyshevRatio (d.m + 1) d.lowerCentralReferenceRho = 1 := by
  let theta : Real := Real.pi / (2 * d.lowerCentralLength + 1)
  have hthetaPos : 0 < theta := lowerCentralReference_angle_pos d
  have hthetaLtPi : theta < Real.pi := by
    linarith [lowerCentralReference_angle_lt_pi_div_two d, Real.pi_pos]
  have hsin : Real.sin theta ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hthetaPos hthetaLtPi).ne'
  have hminus := chebyshevU_cos_mul_sin (d.m : Int) theta
  have hplus := chebyshevU_cos_mul_sin ((d.m + 1 : Nat) : Int) theta
  have hsuccIndex :
      (d.m : Int) + 1 = ((d.m + 1 : Nat) : Int) := by omega
  rw [← hsuccIndex] at hplus
  have hangles :
      ((((d.m + 1 : Nat) : Int) + 1 : Int) : Real) * theta =
        Real.pi -
          ((((d.m : Nat) : Int) + 1 : Int) : Real) * theta := by
    have hden : 2 * d.lowerCentralLength + 1 ≠ 0 := by
      nlinarith [lowerCentralLength_pos d]
    dsimp only [theta, lowerCentralLength]
    push_cast
    field_simp [hden]
    ring
  rw [← hsuccIndex] at hangles
  push_cast at hplus hminus hangles
  have hUeq :
      chebyshevU (d.m + 1) d.lowerCentralReferenceRho =
        chebyshevU d.m d.lowerCentralReferenceRho := by
    change chebyshevU (d.m + 1) (Real.cos theta) =
      chebyshevU d.m (Real.cos theta)
    apply (mul_right_cancel₀ hsin)
    rw [hplus, hminus, hangles, Real.sin_pi_sub]
  have hUpos : 0 < chebyshevU (d.m + 1) d.lowerCentralReferenceRho :=
    chebyshevU_pos_above_centralFirstNode (d.m + 1) (by omega)
      (lowerCentralReferenceRho_above_succNode d)
  unfold centralChebyshevRatio
  rw [show (((d.m + 1 : Nat) : Int) - 1) = (d.m : Int) by omega,
    ← hsuccIndex, ← hUeq]
  field_simp [hUpos.ne']

theorem lowerCentralRatio_rho_eq_a (d : OddCentralChordData) :
    centralChebyshevRatio (d.m + 1) d.lowerCentralRho = d.a := by
  unfold centralChebyshevRatio
  rw [show (((d.m + 1 : Nat) : Int) - 1) = (d.m : Int) by omega]
  apply (div_eq_iff (lowerCentralUPlus_pos d).ne').2
  exact (lowerCentralRho_spec d).2.symm

theorem lowerCentralReferenceRho_lt_Rho (d : OddCentralChordData) :
    d.lowerCentralReferenceRho < d.lowerCentralRho := by
  let f := centralChebyshevRatio (d.m + 1)
  have hanti := centralChebyshevRatio_strictAntiOn (d.m + 1) (by omega)
  have hrefMem : d.lowerCentralReferenceRho ∈
      Ioi (centralChebyshevFirstNode (d.m + 1)) :=
    lowerCentralReferenceRho_above_succNode d
  have hrhoMem : d.lowerCentralRho ∈
      Ioi (centralChebyshevFirstNode (d.m + 1)) :=
    (lowerCentralRho_spec d).1
  by_contra hnot
  have hrhoLe : d.lowerCentralRho ≤ d.lowerCentralReferenceRho :=
    le_of_not_gt hnot
  have hne : d.lowerCentralRho ≠ d.lowerCentralReferenceRho := by
    intro heq
    have := lowerCentralRatio_rho_eq_a d
    rw [heq, lowerCentralRatio_reference_eq_one d] at this
    linarith [d.ha1]
  have hlt : d.lowerCentralRho < d.lowerCentralReferenceRho :=
    lt_of_le_of_ne hrhoLe hne
  have hratio := hanti hrhoMem hrefMem hlt
  rw [lowerCentralRatio_rho_eq_a d,
    lowerCentralRatio_reference_eq_one d] at hratio
  exact (lt_asymm d.ha1 hratio)

theorem lowerCentralReferenceRho_gt_Omega (d : OddCentralChordData) :
    d.lowerCentralOmega < d.lowerCentralReferenceRho := by
  unfold lowerCentralOmega lowerCentralReferenceRho
  have hsmall :
      0 ≤ Real.pi / (2 * d.lowerCentralLength + 1) :=
    (lowerCentralReference_angle_pos d).le
  have hlarge :
      Real.pi / (2 * d.lowerCentralLength) ≤ Real.pi := by
    have hden : 0 < 2 * d.lowerCentralLength :=
      mul_pos (by norm_num) (lowerCentralLength_pos d)
    rw [div_le_iff₀ hden]
    nlinarith [lowerCentralLength_ge_two d, Real.pi_pos]
  apply Real.cos_lt_cos_of_nonneg_of_le_pi hsmall hlarge
  apply (div_lt_div_iff_of_pos_left Real.pi_pos
    (by nlinarith [lowerCentralLength_pos d])
    (mul_pos (by norm_num) (lowerCentralLength_pos d))).2
  linarith

theorem lowerCentralXi_gt_two_mul_Omega_sub_one
    (d : OddCentralChordData) :
    2 * d.lowerCentralOmega - 1 < d.lowerCentralXi := by
  have hfrac :
      d.lowerCentralOmegaDelta / d.lowerCentralD <
        d.lowerCentralOmegaDelta := by
    rw [div_lt_iff₀ (lowerCentralD_pos d)]
    nlinarith [lowerCentralOmegaDelta_pos d, lowerCentralD_gt_one d]
  have href := lowerCentralReferenceRho_lt_Rho d
  have homega := lowerCentralReferenceRho_gt_Omega d
  unfold lowerCentralXi lowerCentralOmegaDelta
  unfold lowerCentralOmegaDelta at hfrac
  nlinarith

theorem lowerCentral_two_mul_Omega_sq_sub_one_eq_firstNode
    (d : OddCentralChordData) :
    2 * d.lowerCentralOmega ^ 2 - 1 =
      centralChebyshevFirstNode d.m := by
  unfold lowerCentralOmega centralChebyshevFirstNode
  rw [← Real.cos_two_mul]
  have hangle :
      2 * (Real.pi / (2 * d.lowerCentralLength)) =
        Real.pi / ((d.m : Real) + 1) := by
    rw [lowerCentralLength_eq]
    field_simp [show (d.m : Real) + 1 ≠ 0 by positivity]
  rw [hangle]
  simp only [Nat.cast_add, Nat.cast_one]

theorem lowerCentralXi_above_firstNode (d : OddCentralChordData) :
    centralChebyshevFirstNode d.m < d.lowerCentralXi := by
  have hquad :
      2 * d.lowerCentralOmega ^ 2 - 1 <
        2 * d.lowerCentralOmega - 1 := by
    nlinarith [lowerCentralOmega_pos d, lowerCentralOmega_lt_one d]
  rw [← lowerCentral_two_mul_Omega_sq_sub_one_eq_firstNode]
  exact hquad.trans (lowerCentralXi_gt_two_mul_Omega_sub_one d)

/-! ## The elementary `Delta_omega` and `1-rho` estimates -/

theorem pi_sq_lt_ten : Real.pi ^ 2 < 10 := by
  have hprod :
      0 < ((3.15 : Real) - Real.pi) * ((3.15 : Real) + Real.pi) :=
    mul_pos (sub_pos.mpr Real.pi_lt_d2) (by linarith [Real.pi_pos])
  nlinarith

theorem lowerCentralOmegaDelta_lt_pi_sq_div (d : OddCentralChordData) :
    d.lowerCentralOmegaDelta <
      Real.pi ^ 2 / (8 * d.lowerCentralLength ^ 2) := by
  let theta := Real.pi / (2 * d.lowerCentralLength)
  have htheta : theta ≠ 0 := by
    dsimp only [theta]
    exact div_ne_zero Real.pi_ne_zero
      (mul_ne_zero (by norm_num) (lowerCentralLength_pos d).ne')
  have hcos := Real.one_sub_sq_div_two_lt_cos htheta
  change 1 - Real.cos theta < Real.pi ^ 2 /
    (8 * d.lowerCentralLength ^ 2)
  have hLne : d.lowerCentralLength ≠ 0 :=
    (lowerCentralLength_pos d).ne'
  calc
    1 - Real.cos theta < theta ^ 2 / 2 := by linarith
    _ = Real.pi ^ 2 / (8 * d.lowerCentralLength ^ 2) := by
      dsimp only [theta]
      field_simp [hLne]
      ring

theorem lowerCentralOmegaDelta_lt_five_div (d : OddCentralChordData) :
    d.lowerCentralOmegaDelta < 5 / (4 * d.lowerCentralLength ^ 2) := by
  have hfirst := lowerCentralOmegaDelta_lt_pi_sq_div d
  have hLsq : 0 < d.lowerCentralLength ^ 2 := sq_pos_of_pos
    (lowerCentralLength_pos d)
  apply hfirst.trans
  calc
    Real.pi ^ 2 / (8 * d.lowerCentralLength ^ 2) <
        10 / (8 * d.lowerCentralLength ^ 2) :=
      (div_lt_div_iff_of_pos_right
        (mul_pos (by norm_num) hLsq)).2 pi_sq_lt_ten
    _ = 5 / (4 * d.lowerCentralLength ^ 2) := by
      field_simp [(lowerCentralLength_pos d).ne']
      ring

theorem lowerCentralOmegaDelta_mul_length_lt_one
    (d : OddCentralChordData) :
    d.lowerCentralOmegaDelta * d.lowerCentralLength < 1 := by
  have h := lowerCentralOmegaDelta_lt_five_div d
  have hL := lowerCentralLength_ge_two d
  have hLpos := lowerCentralLength_pos d
  have hden : 0 < 4 * d.lowerCentralLength ^ 2 :=
    mul_pos (by norm_num) (sq_pos_of_pos hLpos)
  have hscaled :
      d.lowerCentralOmegaDelta *
          (4 * d.lowerCentralLength ^ 2) < 5 :=
    (lt_div_iff₀ hden).mp h
  have hscaled' :
      4 * d.lowerCentralLength *
          (d.lowerCentralOmegaDelta * d.lowerCentralLength) < 5 := by
    nlinarith [hscaled]
  have hsq : 0 < d.lowerCentralLength ^ 2 := sq_pos_of_pos hLpos
  nlinarith [hscaled', lowerCentralOmegaDelta_pos d]

theorem lowerCentralReference_one_sub_lt_five_div
    (d : OddCentralChordData) :
    1 - d.lowerCentralReferenceRho <
      5 / (2 * d.lowerCentralLength + 1) ^ 2 := by
  let theta := Real.pi / (2 * d.lowerCentralLength + 1)
  have htheta : theta ≠ 0 := by
    dsimp only [theta]
    exact div_ne_zero Real.pi_ne_zero
      (by nlinarith [lowerCentralLength_pos d])
  have hcos := Real.one_sub_sq_div_two_lt_cos htheta
  have hbase : 0 < 2 * d.lowerCentralLength + 1 := by
    nlinarith [lowerCentralLength_pos d]
  have hden : 0 < (2 * d.lowerCentralLength + 1) ^ 2 :=
    sq_pos_of_pos hbase
  have hpi := pi_sq_lt_ten
  change 1 - Real.cos theta < 5 / (2 * d.lowerCentralLength + 1) ^ 2
  have hfirst :
      1 - Real.cos theta <
        Real.pi ^ 2 / (2 * (2 * d.lowerCentralLength + 1) ^ 2) := by
    calc
      1 - Real.cos theta < theta ^ 2 / 2 := by linarith
      _ = Real.pi ^ 2 /
          (2 * (2 * d.lowerCentralLength + 1) ^ 2) := by
        dsimp only [theta]
        field_simp [hbase.ne']
  exact hfirst.trans (by
    have hrewrite :
        Real.pi ^ 2 / (2 * (2 * d.lowerCentralLength + 1) ^ 2) =
          (Real.pi ^ 2 / 2) /
            (2 * d.lowerCentralLength + 1) ^ 2 := by
      field_simp [hden.ne']
    rw [hrewrite, div_lt_div_iff_of_pos_right hden]
    nlinarith)

/-- Corrected version of the second inequality in `eq:Delta-upsilon-bounds`.
It is an equality at `L=2`, so the weak sign is essential. -/
theorem five_div_reference_den_sq_le_one_fifth
    (d : OddCentralChordData) :
    5 / (2 * d.lowerCentralLength + 1) ^ 2 ≤ (1 : Real) / 5 := by
  have hL := lowerCentralLength_ge_two d
  have hden : 0 < (2 * d.lowerCentralLength + 1) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden (by norm_num : (0 : Real) < 5)]
  nlinarith [sq_nonneg (2 * d.lowerCentralLength - 4)]

/-! ## Strict logarithmic concavity of `f_L` on `[xi,rho]` -/

theorem lowerCentral_node_lt {d : OddCentralChordData} {t q : Real}
    (ht : centralChebyshevFirstNode d.m < t)
    (hq : q ∈ chordNodes (d.m + 1)) :
    q < t := by
  have hqle := chordNode_le_first (d.m + 1)
    (Nat.succ_le_succ d.hm) hq
  simpa only [centralChebyshevFirstNode,
    lowerCentralLength_eq] using hqle.trans_lt ht

theorem lowerCentralF_pos {d : OddCentralChordData} {t : Real}
    (ht : centralChebyshevFirstNode d.m < t) :
    0 < d.lowerCentralF t := by
  have hnodeNonneg : 0 ≤ centralChebyshevFirstNode d.m :=
    transformedFirstNode_nonneg d
  have hone : 0 < 1 + t := by linarith
  exact mul_pos hone
    (chebyshevU_pos_above_centralFirstNode d.m d.hm ht)

theorem lowerCentralLogSlope_pos {d : OddCentralChordData} {t : Real}
    (ht : centralChebyshevFirstNode d.m < t) :
    0 < d.lowerCentralLogSlope t := by
  have hnodeNonneg : 0 ≤ centralChebyshevFirstNode d.m :=
    transformedFirstNode_nonneg d
  have hone : 0 < 1 + t := by linarith
  have hsum :
      0 ≤ ∑ q ∈ chordNodes (d.m + 1), (t - q)⁻¹ := by
    apply Finset.sum_nonneg
    intro q hq
    exact inv_nonneg.mpr (sub_nonneg.mpr
      (lowerCentral_node_lt ht hq).le)
  unfold lowerCentralLogSlope
  have hfirst : 0 < 1 / (1 + t) := one_div_pos.mpr hone
  linarith

theorem lowerCentralLogSlope_strictAntiOn (d : OddCentralChordData) :
    StrictAntiOn d.lowerCentralLogSlope
      (Ioi (centralChebyshevFirstNode d.m)) := by
  intro x hx y hy hxy
  have hnodeNonneg : 0 ≤ centralChebyshevFirstNode d.m :=
    transformedFirstNode_nonneg d
  have hxone : 0 < 1 + x :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (hnodeNonneg.trans hx.le)
  have hyone : 0 < 1 + y :=
    add_pos_of_pos_of_nonneg zero_lt_one
      (hnodeNonneg.trans hy.le)
  have hfirst : 1 / (1 + y) < 1 / (1 + x) := by
    exact one_div_lt_one_div_of_lt hxone (by linarith)
  have hsum :
      (∑ q ∈ chordNodes (d.m + 1), (y - q)⁻¹) ≤
        ∑ q ∈ chordNodes (d.m + 1), (x - q)⁻¹ := by
    apply Finset.sum_le_sum
    intro q hq
    have hxq : 0 < x - q := sub_pos.mpr (lowerCentral_node_lt hx hq)
    have hxyq : x - q ≤ y - q := by linarith
    simpa only [one_div] using one_div_le_one_div_of_le hxq hxyq
  unfold lowerCentralLogSlope
  linarith

theorem lowerCentral_logF_eq_rootLogSum
    {d : OddCentralChordData} {t : Real}
    (ht : centralChebyshevFirstNode d.m < t) :
    Real.log (d.lowerCentralF t) =
      Real.log (2 ^ d.m : Real) + Real.log (1 + t) +
        ∑ q ∈ chordNodes (d.m + 1), Real.log (t - q) := by
  have hnodeNonneg : 0 ≤ centralChebyshevFirstNode d.m :=
    transformedFirstNode_nonneg d
  have hone : 0 < 1 + t := by linarith
  have hfactor : ∀ q ∈ chordNodes (d.m + 1), 0 < t - q := by
    intro q hq
    exact sub_pos.mpr (lowerCentral_node_lt ht hq)
  have hprod : 0 < chordNodeProduct (d.m + 1) t := by
    unfold chordNodeProduct
    exact Finset.prod_pos hfactor
  have hpow : 0 < (2 : Real) ^ d.m := by positivity
  have hU := chebyshevU_eq_chordNodeProduct
    (d.m + 1) (Nat.succ_le_succ d.hm) t
  have hUindex : chebyshevU d.m t =
      2 ^ d.m * chordNodeProduct (d.m + 1) t := by
    simpa only [Nat.add_sub_cancel] using hU
  have hlogProd :
      Real.log (chordNodeProduct (d.m + 1) t) =
        ∑ q ∈ chordNodes (d.m + 1), Real.log (t - q) := by
    unfold chordNodeProduct
    rw [Real.log_prod]
    intro q hq
    exact (hfactor q hq).ne'
  unfold lowerCentralF
  rw [hUindex,
    Real.log_mul hone.ne' (mul_ne_zero hpow.ne' hprod.ne'),
    Real.log_mul hpow.ne' hprod.ne', hlogProd]
  ring

theorem hasDerivAt_log_lowerCentralF
    {d : OddCentralChordData} {t : Real}
    (ht : centralChebyshevFirstNode d.m < t) :
    HasDerivAt (fun u : Real => Real.log (d.lowerCentralF u))
      (d.lowerCentralLogSlope t) t := by
  have hnodeNonneg : 0 ≤ centralChebyshevFirstNode d.m :=
    transformedFirstNode_nonneg d
  have hone : 0 < 1 + t := by linarith
  have hfirst :
      HasDerivAt (fun u : Real => Real.log (1 + u))
        (1 / (1 + t)) t := by
    convert ((hasDerivAt_const t 1).add (hasDerivAt_id t)).log hone.ne'
      using 1
    simp only [Pi.add_apply, id_eq]
    ring
  have hsum :
      HasDerivAt
        (fun u : Real =>
          ∑ q ∈ chordNodes (d.m + 1), Real.log (u - q))
        (∑ q ∈ chordNodes (d.m + 1), (t - q)⁻¹) t := by
    apply HasDerivAt.fun_sum
    intro q hq
    have htq := lowerCentral_node_lt ht hq
    convert ((hasDerivAt_id t).sub_const q).log
      (sub_ne_zero.mpr (ne_of_gt htq)) using 1
    simp only [id_eq, one_div]
  have hexplicit :
      HasDerivAt
        (fun u : Real =>
          Real.log (2 ^ d.m : Real) + Real.log (1 + u) +
            ∑ q ∈ chordNodes (d.m + 1), Real.log (u - q))
        (d.lowerCentralLogSlope t) t := by
    simpa only [lowerCentralLogSlope, zero_add] using
      ((hasDerivAt_const t (Real.log (2 ^ d.m : Real))).add hfirst).add hsum
  apply hexplicit.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
  exact lowerCentral_logF_eq_rootLogSum hu

theorem lowerCentral_log_drop_strict (d : OddCentralChordData) :
    Real.log (d.lowerCentralF d.lowerCentralRho) -
        Real.log (d.lowerCentralF d.lowerCentralXi) >
      (d.lowerCentralRho - d.lowerCentralXi) *
        d.lowerCentralSlopeAtRho := by
  have hxiNode := lowerCentralXi_above_firstNode d
  have hrhoNode := lowerCentralRho_above_previousNode d
  have hxirho := lowerCentralXi_lt_Rho d
  have hcont : ContinuousOn
      (fun u : Real => Real.log (d.lowerCentralF u))
      (Icc d.lowerCentralXi d.lowerCentralRho) := by
    intro t ht
    exact (hasDerivAt_log_lowerCentralF
      (hxiNode.trans_le ht.1)).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Ioo d.lowerCentralXi d.lowerCentralRho,
      HasDerivAt (fun u : Real => Real.log (d.lowerCentralF u))
        (d.lowerCentralLogSlope t) t := by
    intro t ht
    exact hasDerivAt_log_lowerCentralF (hxiNode.trans ht.1)
  obtain ⟨t, ht, hslope⟩ :=
    exists_hasDerivAt_eq_slope
      (f := fun u : Real => Real.log (d.lowerCentralF u))
      (f' := d.lowerCentralLogSlope) hxirho hcont hderiv
  have hanti := lowerCentralLogSlope_strictAntiOn d
    (hxiNode.trans ht.1) hrhoNode ht.2
  have hden : d.lowerCentralRho - d.lowerCentralXi ≠ 0 :=
    sub_ne_zero.mpr hxirho.ne'
  rw [eq_div_iff hden] at hslope
  unfold lowerCentralSlopeAtRho
  have hmul := mul_lt_mul_of_pos_right hanti (sub_pos.mpr hxirho)
  nlinarith [hslope, hmul]

theorem lowerCentralF_Xi_sq_lt_exp (d : OddCentralChordData) :
    d.lowerCentralF d.lowerCentralXi ^ 2 <
      d.lowerCentralF d.lowerCentralRho ^ 2 *
        Real.exp (-2 *
          (d.lowerCentralRho - d.lowerCentralXi) *
            d.lowerCentralSlopeAtRho) := by
  have hxiPos := lowerCentralF_pos (lowerCentralXi_above_firstNode d)
  have hrhoPos := lowerCentralF_pos (lowerCentralRho_above_previousNode d)
  have hlog := lowerCentral_log_drop_strict d
  have hexp :
      Real.exp (2 * Real.log (d.lowerCentralF d.lowerCentralXi)) <
        Real.exp (2 * Real.log (d.lowerCentralF d.lowerCentralRho) +
          (-2 * (d.lowerCentralRho - d.lowerCentralXi) *
            d.lowerCentralSlopeAtRho)) := by
    apply Real.exp_lt_exp.mpr
    linarith
  calc
    d.lowerCentralF d.lowerCentralXi ^ 2 =
        Real.exp (2 * Real.log (d.lowerCentralF d.lowerCentralXi)) := by
      rw [show 2 * Real.log (d.lowerCentralF d.lowerCentralXi) =
          Real.log (d.lowerCentralF d.lowerCentralXi) +
            Real.log (d.lowerCentralF d.lowerCentralXi) by ring,
        Real.exp_add, Real.exp_log hxiPos]
      ring
    _ < Real.exp (2 * Real.log (d.lowerCentralF d.lowerCentralRho) +
          (-2 * (d.lowerCentralRho - d.lowerCentralXi) *
            d.lowerCentralSlopeAtRho)) := hexp
    _ = d.lowerCentralF d.lowerCentralRho ^ 2 *
          Real.exp (-2 * (d.lowerCentralRho - d.lowerCentralXi) *
            d.lowerCentralSlopeAtRho) := by
      rw [Real.exp_add,
        show 2 * Real.log (d.lowerCentralF d.lowerCentralRho) =
          Real.log (d.lowerCentralF d.lowerCentralRho) +
            Real.log (d.lowerCentralF d.lowerCentralRho) by ring,
        Real.exp_add, Real.exp_log hrhoPos]
      ring

theorem lowerCentralSlopeAtRho_pos (d : OddCentralChordData) :
    0 < d.lowerCentralSlopeAtRho := by
  exact lowerCentralLogSlope_pos (lowerCentralRho_above_previousNode d)

theorem lowerCentralF_Xi_sq_lt_rational (d : OddCentralChordData) :
    d.lowerCentralF d.lowerCentralXi ^ 2 <
      d.lowerCentralF d.lowerCentralRho ^ 2 /
        (1 + 2 * (d.lowerCentralRho - d.lowerCentralXi) *
          d.lowerCentralSlopeAtRho) := by
  let t := 2 * (d.lowerCentralRho - d.lowerCentralXi) *
    d.lowerCentralSlopeAtRho
  have ht : 0 < t := by
    dsimp only [t]
    exact mul_pos
      (mul_pos (by norm_num) (sub_pos.mpr (lowerCentralXi_lt_Rho d)))
      (lowerCentralSlopeAtRho_pos d)
  have hexp : Real.exp (-t) < 1 / (1 + t) := by
    have hbase := Real.add_one_lt_exp ht.ne'
    have hden : 0 < 1 + t := by linarith
    have hexpPos := Real.exp_pos t
    rw [Real.exp_neg]
    simpa only [one_div] using
      ((inv_lt_inv₀ hexpPos hden).2
        (by simpa only [add_comm] using hbase))
  have hfirst := lowerCentralF_Xi_sq_lt_exp d
  have hfrhoSq : 0 < d.lowerCentralF d.lowerCentralRho ^ 2 :=
    sq_pos_of_pos (lowerCentralF_pos
      (lowerCentralRho_above_previousNode d))
  dsimp only [t] at hexp ⊢
  have hexp' :
      Real.exp (-2 * (d.lowerCentralRho - d.lowerCentralXi) *
          d.lowerCentralSlopeAtRho) <
        (1 + 2 * (d.lowerCentralRho - d.lowerCentralXi) *
          d.lowerCentralSlopeAtRho)⁻¹ := by
    have harg :
        -(2 * (d.lowerCentralRho - d.lowerCentralXi) *
            d.lowerCentralSlopeAtRho) =
          -2 * (d.lowerCentralRho - d.lowerCentralXi) *
            d.lowerCentralSlopeAtRho := by
      ring
    rw [harg] at hexp
    simpa only [one_div] using hexp
  exact hfirst.trans (mul_lt_mul_of_pos_left hexp' hfrhoSq)

theorem lowerCentralF_Rho_sq (d : OddCentralChordData) :
    d.lowerCentralF d.lowerCentralRho ^ 2 =
      (1 + d.lowerCentralRho) ^ 2 / d.lowerCentralQ := by
  have hinv := lowerCentralQ_invariant d
  change ((1 + d.lowerCentralRho) *
      d.lowerCentralUMinus) ^ 2 = _
  rw [mul_pow]
  apply (eq_div_iff (lowerCentralQ_pos d).ne').2
  linear_combination (norm := ring_nf)
    (1 + d.lowerCentralRho) ^ 2 * hinv

/-! ## The logarithmic derivative at `rho` -/

theorem lowerCentralLogSlope_eq_chebyshevDerivative
    {d : OddCentralChordData} {t : Real}
    (ht : centralChebyshevFirstNode d.m < t) :
    d.lowerCentralLogSlope t =
      1 / (1 + t) +
        deriv (chebyshevU d.m) t / chebyshevU d.m t := by
  let U : Real := chebyshevU d.m t
  let U' : Real := deriv (chebyshevU d.m) t
  have hUpos : 0 < U :=
    chebyshevU_pos_above_centralFirstNode d.m d.hm ht
  have hone : 0 < 1 + t := by
    have hnodeNonneg : 0 ≤ centralChebyshevFirstNode d.m :=
      transformedFirstNode_nonneg d
    linarith
  have hpoly : HasDerivAt (chebyshevU d.m) U' t := by
    have h := (Polynomial.Chebyshev.U Real d.m).hasDerivAt t
    have hderiv :
        (Polynomial.Chebyshev.U Real d.m).derivative.eval t = U' := by
      dsimp only [U']
      symm
      exact (Polynomial.Chebyshev.U Real d.m).deriv
    simpa only [chebyshevU, hderiv] using h
  have hF : HasDerivAt d.lowerCentralF
      (U + (1 + t) * U') t := by
    unfold lowerCentralF
    convert ((hasDerivAt_const t 1).add (hasDerivAt_id t)).mul hpoly
      using 1
    simp only [Pi.add_apply, id_eq]
    ring
  have hlog :
      HasDerivAt (fun u : Real => Real.log (d.lowerCentralF u))
        (1 / (1 + t) + U' / U) t := by
    convert hF.log (mul_ne_zero hone.ne' hUpos.ne') using 1
    dsimp only [U, U']
    unfold lowerCentralF
    field_simp [hone.ne', hUpos.ne']
    rw [add_div, div_self hUpos.ne']
  exact (hasDerivAt_log_lowerCentralF ht).unique hlog

/-- The logarithmic-derivative identity, valid also at `rho=1`. -/
theorem lowerCentralSlopeAtRho_identity (d : OddCentralChordData) :
    (d.lowerCentralRho ^ 2 - 1) * d.lowerCentralSlopeAtRho =
      d.lowerCentralLength *
        (d.lowerCentralB - d.lowerCentralRho) - 1 := by
  let rho := d.lowerCentralRho
  let U : Real := chebyshevU d.m rho
  let U' : Real := deriv (chebyshevU d.m) rho
  let b := d.lowerCentralB
  have hUpos : 0 < U := lowerCentralUMinus_pos d
  have hplus :
      chebyshevU (d.m + 1) rho = b * U := by
    simpa only [rho, U, b, lowerCentralUPlus, lowerCentralUMinus] using
      lowerCentralUPlus_eq_B_mul_UMinus d
  have hrec := chebyshevU_add_one (d.m : Int) rho
  have hprev :
      chebyshevU ((d.m : Int) - 1) rho =
        (2 * rho - b) * U := by
    rw [hplus] at hrec
    nlinarith
  have hpolyDeriv := congrArg
    (fun p : Real[X] => p.eval rho)
    (Polynomial.Chebyshev.add_one_mul_T_eq_poly_in_U
      (R := Real) (d.m : Int))
  have hpolyT := congrArg
    (fun p : Real[X] => p.eval rho)
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
        (b - rho) * U := by
    have hraw :
        (Polynomial.Chebyshev.T Real ((d.m : Int) + 1)).eval rho =
          rho * U - chebyshevU ((d.m : Int) - 1) rho := by
      simpa only [Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_X, chebyshevU, hTindex, hUindex] using hpolyT
    rw [hraw, hprev]
    ring
  have hmain :
      d.lowerCentralLength * ((b - rho) * U) =
        rho * U - (1 - rho ^ 2) * U' := by
    simpa only [Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
      Polynomial.eval_pow, Polynomial.eval_natCast,
      Polynomial.eval_intCast, chebyshevU, hDerivEval, hT,
      Int.cast_natCast, Int.cast_add, Int.cast_one,
      Nat.cast_add, Nat.cast_one, lowerCentralLength_eq] using hpolyDeriv
  have hrhoNonneg : 0 ≤ rho := by
    have href := lowerCentralReferenceRho_pos d
    have hr := lowerCentralReferenceRho_lt_Rho d
    linarith
  have honePlusRho : 1 + rho ≠ 0 := by linarith
  rw [lowerCentralSlopeAtRho,
    lowerCentralLogSlope_eq_chebyshevDerivative
      (lowerCentralRho_above_previousNode d)]
  dsimp only [rho, U, U', b] at hmain hUpos honePlusRho ⊢
  field_simp [hUpos.ne', honePlusRho]
  nlinarith

/-- Quotient form used only away from `rho=1`. -/
theorem lowerCentralSlopeAtRho_eq_quotient
    (d : OddCentralChordData)
    (hrhoOne : d.lowerCentralRho ≠ 1) :
    d.lowerCentralSlopeAtRho =
      (d.lowerCentralLength *
          (d.lowerCentralB - d.lowerCentralRho) - 1) /
        (d.lowerCentralRho ^ 2 - 1) := by
  have hrhoPos := (lowerCentralReferenceRho_pos d).trans
    (lowerCentralReferenceRho_lt_Rho d)
  apply (eq_div_iff (show d.lowerCentralRho ^ 2 - 1 ≠ 0 by
    intro h
    have : d.lowerCentralRho = 1 := by nlinarith
    exact hrhoOne this)).2
  simpa only [mul_comm] using lowerCentralSlopeAtRho_identity d

/-! ## Positivity of `N`: the case `rho>=1` -/

theorem lowerCentralN_pos_of_one_le_Rho
    (d : OddCentralChordData)
    (hrho : 1 ≤ d.lowerCentralRho) :
    0 < d.lowerCentralN := by
  let u := d.lowerCentralB - d.lowerCentralRho
  have hL := lowerCentralLength_pos d
  have hw := lowerCentralOmega_pos d
  have hdelta := lowerCentralOmegaDelta_pos d
  have hslope := lowerCentralSlopeAtRho_pos d
  have hid := lowerCentralSlopeAtRho_identity d
  have hnonneg : 0 ≤ (d.lowerCentralRho ^ 2 - 1) *
      d.lowerCentralSlopeAtRho :=
    mul_nonneg (by nlinarith) hslope.le
  have hu : 1 / d.lowerCentralLength ≤ u := by
    rw [div_le_iff₀ hL]
    dsimp only [u]
    nlinarith
  have hdeltaLt : d.lowerCentralOmegaDelta < 1 / d.lowerCentralLength :=
    (lt_div_iff₀ hL).2 (lowerCentralOmegaDelta_mul_length_lt_one d)
  have huDelta : 0 < u - d.lowerCentralOmegaDelta := by linarith
  have huPos : 0 < u := by linarith
  have hS : (1 + d.lowerCentralRho) ^ 2 < d.lowerCentralS := by
    have hmain : 0 < 2 * d.lowerCentralRho *
        (u - d.lowerCentralOmegaDelta) := by positivity
    have hrest : 0 < u ^ 2 + 2 * d.lowerCentralOmega * u := by positivity
    dsimp only [u] at hmain hrest
    unfold lowerCentralS
    unfold lowerCentralOmegaDelta at hmain
    nlinarith only [hmain, hrest]
  have hcorr : 0 < 2 * d.lowerCentralOmegaDelta * d.lowerCentralQ *
      d.lowerCentralSlopeAtRho := by
    exact mul_pos (mul_pos (mul_pos (by norm_num) hdelta)
      (lowerCentralQ_pos d)) hslope
  have hmain := mul_lt_mul_of_pos_left hS
    (show 0 < d.lowerCentralRho + d.lowerCentralOmega by linarith)
  have hremaining : 0 ≤ (d.lowerCentralRho - 1) *
      (1 + d.lowerCentralRho) ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hrho) (sq_nonneg _)
  have hpositive := mul_pos
    (show 0 < d.lowerCentralRho + d.lowerCentralOmega by linarith) hcorr
  unfold lowerCentralN
  nlinarith only [hmain, hremaining, hpositive]

/-! ## Positivity of `N`: the case `rho<1` -/

/-- `upsilon=1-rho`. -/
def lowerCentralV (d : OddCentralChordData) : Real :=
  1 - d.lowerCentralRho

/-- `Delta_b=b-1`. -/
def lowerCentralDeltaB (d : OddCentralChordData) : Real :=
  d.lowerCentralB - 1

/-- The source's `u=Delta_b+upsilon=b-rho`. -/
def lowerCentralU (d : OddCentralChordData) : Real :=
  d.lowerCentralB - d.lowerCentralRho

/-- `Delta_-=upsilon(2-upsilon)=1-rho^2`. -/
def lowerCentralDeltaMinus (d : OddCentralChordData) : Real :=
  d.lowerCentralV * (2 - d.lowerCentralV)

/-- The quadratic `q(u)` in the positive decomposition of `N`. -/
def lowerCentralQuadratic (d : OddCentralChordData) (u : Real) : Real :=
  d.lowerCentralDeltaMinus *
      (4 - 2 * d.lowerCentralOmegaDelta + u - d.lowerCentralV) +
    2 * d.lowerCentralOmegaDelta *
      ((u + d.lowerCentralV) * (1 - d.lowerCentralLength * u) -
        2 * d.lowerCentralLength * d.lowerCentralV)

/-- The value of `N` at `Delta_b=0`, written as two positive terms. -/
def lowerCentralNZero (d : OddCentralChordData) : Real :=
  d.lowerCentralV *
      ((2 - d.lowerCentralOmegaDelta) * (2 - d.lowerCentralV) -
        4 * d.lowerCentralOmegaDelta * d.lowerCentralLength) +
    2 * d.lowerCentralV * d.lowerCentralOmegaDelta ^ 2 *
      (2 * d.lowerCentralLength - 1) / (2 - d.lowerCentralV)

theorem lowerCentralU_eq_deltaB_add_V (d : OddCentralChordData) :
    d.lowerCentralU = d.lowerCentralDeltaB + d.lowerCentralV := by
  unfold lowerCentralU lowerCentralDeltaB lowerCentralV
  ring

theorem lowerCentralDeltaMinus_eq_one_sub_rho_sq
    (d : OddCentralChordData) :
    d.lowerCentralDeltaMinus = 1 - d.lowerCentralRho ^ 2 := by
  unfold lowerCentralDeltaMinus lowerCentralV
  ring

theorem lowerCentralRho_pos (d : OddCentralChordData) :
    0 < d.lowerCentralRho :=
  (lowerCentralReferenceRho_pos d).trans
    (lowerCentralReferenceRho_lt_Rho d)

theorem lowerCentralV_pos_of_Rho_lt_one
    (d : OddCentralChordData)
    (hrho : d.lowerCentralRho < 1) :
    0 < d.lowerCentralV := by
  unfold lowerCentralV
  linarith

theorem lowerCentralDeltaB_pos (d : OddCentralChordData) :
    0 < d.lowerCentralDeltaB := by
  unfold lowerCentralDeltaB
  exact sub_pos.mpr (one_lt_lowerCentralB d)

/-- The logarithmic-derivative identity gives `v<u<1/L` when `rho<1`. -/
theorem lowerCentralU_range_of_Rho_lt_one
    (d : OddCentralChordData)
    (hrho : d.lowerCentralRho < 1) :
    0 < d.lowerCentralV ∧
      d.lowerCentralV < d.lowerCentralU ∧
      d.lowerCentralU < 1 / d.lowerCentralLength := by
  have hv := lowerCentralV_pos_of_Rho_lt_one d hrho
  have hdb := lowerCentralDeltaB_pos d
  have hvu : d.lowerCentralV < d.lowerCentralU := by
    rw [lowerCentralU_eq_deltaB_add_V]
    linarith
  have hid := lowerCentralSlopeAtRho_identity d
  have hslope := lowerCentralSlopeAtRho_pos d
  have hden : d.lowerCentralRho ^ 2 - 1 < 0 := by
    nlinarith [lowerCentralRho_pos d]
  have hnum : d.lowerCentralLength * d.lowerCentralU - 1 < 0 := by
    have hprod := mul_neg_of_neg_of_pos hden hslope
    unfold lowerCentralU
    linarith
  have huUpper : d.lowerCentralU < 1 / d.lowerCentralLength := by
    rw [lt_div_iff₀ (lowerCentralLength_pos d)]
    nlinarith [hnum]
  exact ⟨hv, hvu, huUpper⟩

theorem lowerCentralV_lt_reference_bound_of_Rho_lt_one
    (d : OddCentralChordData) :
    d.lowerCentralV <
      5 / (2 * d.lowerCentralLength + 1) ^ 2 := by
  have href := lowerCentralReferenceRho_lt_Rho d
  have hbound := lowerCentralReference_one_sub_lt_five_div d
  unfold lowerCentralV
  linarith

theorem lowerCentralV_lt_one_fifth_of_Rho_lt_one
    (d : OddCentralChordData) :
    d.lowerCentralV < (1 : Real) / 5 := by
  exact (lowerCentralV_lt_reference_bound_of_Rho_lt_one d).trans_le
    (five_div_reference_den_sq_le_one_fifth d)

theorem lowerCentralOmegaDelta_lt_five_sixteenths
    (d : OddCentralChordData) :
    d.lowerCentralOmegaDelta < (5 : Real) / 16 := by
  have h := lowerCentralOmegaDelta_lt_five_div d
  have hL := lowerCentralLength_ge_two d
  have hLsq : 4 ≤ d.lowerCentralLength ^ 2 := by nlinarith
  calc
    d.lowerCentralOmegaDelta <
        5 / (4 * d.lowerCentralLength ^ 2) := h
    _ ≤ 5 / 16 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      nlinarith

theorem four_mul_delta_mul_length_lt_five_div_length
    (d : OddCentralChordData) :
    4 * d.lowerCentralOmegaDelta * d.lowerCentralLength <
      5 / d.lowerCentralLength := by
  have h := lowerCentralOmegaDelta_lt_five_div d
  have hL := lowerCentralLength_pos d
  have hden : 0 < 4 * d.lowerCentralLength ^ 2 := by positivity
  have hscaled :
      d.lowerCentralOmegaDelta *
          (4 * d.lowerCentralLength ^ 2) < 5 :=
    (lt_div_iff₀ hden).mp h
  rw [lt_div_iff₀ hL]
  nlinarith [hscaled]

theorem five_div_length_le_five_halves (d : OddCentralChordData) :
    5 / d.lowerCentralLength ≤ (5 : Real) / 2 := by
  exact div_le_div_of_nonneg_left (by norm_num)
    (by norm_num) (lowerCentralLength_ge_two d)

theorem lowerCentralN_decomposition_of_Rho_lt_one
    (d : OddCentralChordData)
    (hrho : d.lowerCentralRho < 1) :
    d.lowerCentralN = d.lowerCentralNZero +
      d.lowerCentralDeltaB *
        (d.lowerCentralRho + d.lowerCentralOmega) /
          d.lowerCentralDeltaMinus *
            d.lowerCentralQuadratic d.lowerCentralU := by
  have hslope := lowerCentralSlopeAtRho_eq_quotient d
    (ne_of_lt hrho)
  have hDelta := lowerCentralDeltaMinus_eq_one_sub_rho_sq d
  have hOneSubRhoSqNe : 1 - d.lowerCentralRho ^ 2 ≠ 0 := by
    nlinarith [lowerCentralRho_pos d]
  have hRhoSqSubOneNe : d.lowerCentralRho ^ 2 - 1 ≠ 0 := by
    nlinarith [lowerCentralRho_pos d]
  have hTwoSubVPos : 0 < 2 - d.lowerCentralV := by
    unfold lowerCentralV
    nlinarith [lowerCentralRho_pos d]
  rw [lowerCentralN, hslope]
  unfold lowerCentralNZero lowerCentralQuadratic
    lowerCentralS lowerCentralQ lowerCentralU lowerCentralDeltaB
    lowerCentralOmegaDelta
  rw [hDelta]
  field_simp [hOneSubRhoSqNe, hRhoSqSubOneNe,
    hTwoSubVPos.ne']
  unfold lowerCentralV
  ring

theorem two_sub_lowerCentralV_gt_nine_fifths
    (d : OddCentralChordData) :
    (9 : Real) / 5 < 2 - d.lowerCentralV := by
  linarith [lowerCentralV_lt_one_fifth_of_Rho_lt_one d]

theorem two_sub_lowerCentralOmegaDelta_gt_twenty_seven_sixteenths
    (d : OddCentralChordData) :
    (27 : Real) / 16 < 2 - d.lowerCentralOmegaDelta := by
  linarith [lowerCentralOmegaDelta_lt_five_sixteenths d]

theorem four_mul_delta_mul_length_lt_five_halves
    (d : OddCentralChordData) :
    4 * d.lowerCentralOmegaDelta * d.lowerCentralLength <
      (5 : Real) / 2 :=
  (four_mul_delta_mul_length_lt_five_div_length d).trans_le
    (five_div_length_le_five_halves d)

theorem lowerCentral_common_bracket_pos (d : OddCentralChordData) :
    0 < (2 - d.lowerCentralOmegaDelta) * (2 - d.lowerCentralV) -
      4 * d.lowerCentralOmegaDelta * d.lowerCentralLength := by
  have htwoV := two_sub_lowerCentralV_gt_nine_fifths d
  have htwoDelta :=
    two_sub_lowerCentralOmegaDelta_gt_twenty_seven_sixteenths d
  have hprod :
      (243 : Real) / 80 <
        (2 - d.lowerCentralOmegaDelta) *
          (2 - d.lowerCentralV) := by
    have hmul := mul_pos
      (sub_pos.mpr htwoDelta) (sub_pos.mpr htwoV)
    nlinarith
  have hfour := four_mul_delta_mul_length_lt_five_halves d
  nlinarith

theorem lowerCentralNZero_pos_of_Rho_lt_one
    (d : OddCentralChordData)
    (hrho : d.lowerCentralRho < 1) :
    0 < d.lowerCentralNZero := by
  have hv := lowerCentralV_pos_of_Rho_lt_one d hrho
  have hB := lowerCentral_common_bracket_pos d
  have hden : 0 < 2 - d.lowerCentralV := by
    linarith [two_sub_lowerCentralV_gt_nine_fifths d]
  have hL : 0 < 2 * d.lowerCentralLength - 1 := by
    linarith [lowerCentralLength_ge_two d]
  unfold lowerCentralNZero
  exact add_pos_of_pos_of_nonneg (mul_pos hv hB) (by positivity)

theorem lowerCentralQuadratic_U_pos_of_Rho_lt_one
    (d : OddCentralChordData)
    (hrho : d.lowerCentralRho < 1) :
    0 < d.lowerCentralQuadratic d.lowerCentralU := by
  have hrange := lowerCentralU_range_of_Rho_lt_one d hrho
  have hB := lowerCentral_common_bracket_pos d
  have hv := hrange.1
  have htwoV : 0 < 2 - d.lowerCentralV := by
    linarith [two_sub_lowerCentralV_gt_nine_fifths d]
  have htwoDelta : 0 < 2 - d.lowerCentralOmegaDelta := by
    linarith [two_sub_lowerCentralOmegaDelta_gt_twenty_seven_sixteenths d]
  have hL := lowerCentralLength_pos d
  have hdelta := lowerCentralOmegaDelta_pos d
  have hu : 0 < 1 - d.lowerCentralLength * d.lowerCentralU := by
    have := (lt_div_iff₀ hL).1 hrange.2.2
    nlinarith
  have hfirst := mul_pos hv hB
  have hsecond : 0 < d.lowerCentralV * (2 - d.lowerCentralV) *
      (2 - d.lowerCentralOmegaDelta + d.lowerCentralU - d.lowerCentralV) :=
    mul_pos (mul_pos hv htwoV) (by linarith [hrange.2.1])
  have huPos : 0 < d.lowerCentralU := by linarith [hrange.2.1]
  have hthird : 0 < 2 * d.lowerCentralOmegaDelta *
      (d.lowerCentralU + d.lowerCentralV) *
      (1 - d.lowerCentralLength * d.lowerCentralU) := by positivity
  unfold lowerCentralQuadratic lowerCentralDeltaMinus
  nlinarith only [hfirst, hsecond, hthird]

theorem lowerCentralN_pos_of_Rho_lt_one
    (d : OddCentralChordData)
    (hrho : d.lowerCentralRho < 1) :
    0 < d.lowerCentralN := by
  rw [lowerCentralN_decomposition_of_Rho_lt_one d hrho]
  have hNzero := lowerCentralNZero_pos_of_Rho_lt_one d hrho
  have hdb := lowerCentralDeltaB_pos d
  have hrhow : 0 < d.lowerCentralRho + d.lowerCentralOmega :=
    add_pos (lowerCentralRho_pos d) (lowerCentralOmega_pos d)
  have hDelta : 0 < d.lowerCentralDeltaMinus := by
    rw [lowerCentralDeltaMinus_eq_one_sub_rho_sq]
    nlinarith [lowerCentralRho_pos d]
  have hq := lowerCentralQuadratic_U_pos_of_Rho_lt_one d hrho
  have hcorr :
      0 < d.lowerCentralDeltaB *
        (d.lowerCentralRho + d.lowerCentralOmega) /
          d.lowerCentralDeltaMinus *
            d.lowerCentralQuadratic d.lowerCentralU := by
    positivity
  linarith

theorem lowerCentralN_pos (d : OddCentralChordData) :
    0 < d.lowerCentralN := by
  rcases lt_or_ge d.lowerCentralRho 1 with hrho | hrho
  · exact lowerCentralN_pos_of_Rho_lt_one d hrho
  · exact lowerCentralN_pos_of_one_le_Rho d hrho

/-! ## Assembly of `eq:central-target` -/

theorem lowerCentral_rational_upper_lt_target (d : OddCentralChordData) :
    (1 + d.lowerCentralOmega) *
        (d.lowerCentralF d.lowerCentralRho ^ 2 /
          (1 + 2 * (d.lowerCentralRho - d.lowerCentralXi) *
            d.lowerCentralSlopeAtRho)) <
      (d.lowerCentralRho + d.lowerCentralOmega) * d.lowerCentralD := by
  let A := d.lowerCentralS +
    2 * d.lowerCentralOmegaDelta * d.lowerCentralQ *
      d.lowerCentralSlopeAtRho
  have hA : 0 < A := by
    dsimp only [A]
    have hS := lowerCentralS_pos d
    have hcorr :
        0 < 2 * d.lowerCentralOmegaDelta * d.lowerCentralQ *
          d.lowerCentralSlopeAtRho := by
      exact mul_pos
        (mul_pos
          (mul_pos (by norm_num) (lowerCentralOmegaDelta_pos d))
          (lowerCentralQ_pos d))
        (lowerCentralSlopeAtRho_pos d)
    linarith
  have hSQ : 0 < d.lowerCentralS / d.lowerCentralQ :=
    div_pos (lowerCentralS_pos d) (lowerCentralQ_pos d)
  have hT :
      1 + 2 * (d.lowerCentralRho - d.lowerCentralXi) *
          d.lowerCentralSlopeAtRho = A / d.lowerCentralS := by
    rw [lowerCentralRho_sub_Xi]
    dsimp only [A]
    field_simp [(lowerCentralS_pos d).ne']
  have hN := lowerCentralN_pos d
  have hBA :
      (1 + d.lowerCentralOmega) *
          (1 + d.lowerCentralRho) ^ 2 / A <
        d.lowerCentralRho + d.lowerCentralOmega := by
    rw [div_lt_iff₀ hA]
    unfold lowerCentralN at hN
    linarith
  have hmul := mul_lt_mul_of_pos_right hBA hSQ
  rw [lowerCentralF_Rho_sq, hT,
    lowerCentralD_eq_S_div_Q]
  convert hmul using 1
  field_simp [(lowerCentralQ_pos d).ne',
    (lowerCentralS_pos d).ne', hA.ne']

/-- The source's strict scalar comparison `eq:central-target`, first in the
compact `f_L` form. -/
theorem lowerCentralF_scalar_target (d : OddCentralChordData) :
    (1 + d.lowerCentralOmega) *
        d.lowerCentralF d.lowerCentralXi ^ 2 <
      (d.lowerCentralRho + d.lowerCentralOmega) * d.lowerCentralD := by
  have hbound := lowerCentralF_Xi_sq_lt_rational d
  have hweight : 0 < 1 + d.lowerCentralOmega := by
    linarith [lowerCentralOmega_pos d]
  have hmul := mul_lt_mul_of_pos_left hbound hweight
  exact hmul.trans (lowerCentral_rational_upper_lt_target d)

/-- Literal expanded statement of `eq:central-target`. -/
theorem lowerCentral_scalar_target (d : OddCentralChordData) :
    (1 + d.lowerCentralOmega) *
        (1 + d.lowerCentralXi) ^ 2 *
          chebyshevU d.m d.lowerCentralXi ^ 2 <
      (d.lowerCentralRho + d.lowerCentralOmega) * d.lowerCentralD := by
  have h := lowerCentralF_scalar_target d
  unfold lowerCentralF at h
  nlinarith [sq_nonneg
    ((1 + d.lowerCentralXi) * chebyshevU d.m d.lowerCentralXi)]

end OddCentralChordData

end

end ConnectedPseudospectrum
