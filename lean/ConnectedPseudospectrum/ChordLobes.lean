import ConnectedPseudospectrum.HalfChordAlgebra
import ConnectedPseudospectrum.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Polynomial.Splits

/-!
# Chebyshev chord lobes

This module formalizes the lobe profile `W_K` and the trigonometric and
hyperbolic channel functions from the branch-classification part of
`lem:mesh`.  Quotients at nodal endpoints are represented by their unique
continuous Chebyshev extensions.
-/

namespace ConnectedPseudospectrum

open Polynomial Set
open scoped BigOperators

noncomputable section

/-- The nodal roots `cos (ell*pi/K)`, `1 <= ell < K`. -/
def chordNodes (K : ℕ) : Finset ℝ :=
  (Finset.range (K - 1)).image fun k =>
    Real.cos (((k + 1 : ℕ) : ℝ) * Real.pi / K)

/-- The monic product over the finite nodal set. -/
def chordNodeProduct (K : ℕ) (u : ℝ) : ℝ :=
  ∏ r ∈ chordNodes K, (u - r)

/-- The logarithmic derivative of the lobe profile away from its nodes and
the two radical endpoints. -/
def chordLogSlope (K : ℕ) (a u : ℝ) : ℝ :=
  (∑ r ∈ chordNodes K, (u - r)⁻¹) -
    u / (Real.cosh (pathLogParameter a) ^ 2 - u ^ 2)

/-- The derivative displayed in `eq:W-log-concave`. -/
def chordLogCurvature (K : ℕ) (a u : ℝ) : ℝ :=
  -(∑ r ∈ chordNodes K, 1 / (u - r) ^ 2) -
    (Real.cosh (pathLogParameter a) ^ 2 + u ^ 2) /
      (Real.cosh (pathLogParameter a) ^ 2 - u ^ 2) ^ 2

/-- A logarithmic lobe profile differing from `log W_K` only by the
positive constant `(K-1) log 2` away from the nodes. -/
def chordLogProfile (K : ℕ) (a u : ℝ) : ℝ :=
  Real.log (Real.cosh (pathLogParameter a) ^ 2 - u ^ 2) / 2 +
    ∑ r ∈ chordNodes K, Real.log |u - r|

/-- The continuous coordinate-free lobe profile
`sqrt(cosh(h)^2-u^2) * |U_{K-1}(u)|`. -/
def chordLobeWeight (K : ℕ) (a u : ℝ) : ℝ :=
  Real.sqrt (Real.cosh (pathLogParameter a) ^ 2 - u ^ 2) *
    |chebyshevU (K - 1 : ℕ) u|

/-- The continuous trigonometric channel `Phi_K`. -/
def chordPhi (K : ℕ) (a θ : ℝ) : ℝ :=
  halfTrigRadical a θ * |chebyshevU (K - 1 : ℕ) (Real.cos θ)|

/-- The continuous hyperbolic channel `Psi_K`. -/
def chordPsi (K : ℕ) (a η : ℝ) : ℝ :=
  halfHypRadical a η * chebyshevU (K - 1 : ℕ) (Real.cosh η)

theorem continuous_chebyshevU (n : ℤ) :
    Continuous (chebyshevU n) := by
  simpa only [chebyshevU] using (Polynomial.Chebyshev.U ℝ n).continuous

theorem continuous_chordLobeWeight (K : ℕ) (a : ℝ) :
    Continuous (chordLobeWeight K a) := by
  unfold chordLobeWeight
  exact (continuous_const.sub (continuous_id.pow 2)).sqrt.mul
    (continuous_chebyshevU (K - 1 : ℕ)).abs

theorem continuous_chordPhi (K : ℕ) (a : ℝ) :
    Continuous (chordPhi K a) := by
  unfold chordPhi halfTrigRadical
  exact (continuous_const.sub (Real.continuous_cos.pow 2)).sqrt.mul
    ((continuous_chebyshevU (K - 1 : ℕ)).comp Real.continuous_cos).abs

theorem continuous_chordPsi (K : ℕ) (a : ℝ) :
    Continuous (chordPsi K a) := by
  unfold chordPsi halfHypRadical
  exact (continuous_const.sub (Real.continuous_cosh.pow 2)).sqrt.mul
    ((continuous_chebyshevU (K - 1 : ℕ)).comp Real.continuous_cosh)

/-- On the hyperbolic coordinate ray the relevant Chebyshev factor is
strictly positive. -/
theorem chebyshevU_cosh_pos (K : ℕ) (hK : 2 ≤ K) {η : ℝ} (hη : 0 ≤ η) :
    0 < chebyshevU (K - 1 : ℕ) (Real.cosh η) := by
  have hcast : ((K - 1 : ℕ) : ℝ) + 1 = K := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ K)
  by_cases hη0 : η = 0
  · subst η
    have hKposNat : 0 < K := by omega
    have hKposReal : (0 : ℝ) < (K : ℝ) := by
      exact_mod_cast hKposNat
    simpa only [Real.cosh_zero, chebyshevU,
      Polynomial.Chebyshev.U_eval_one, Int.cast_natCast, hcast] using hKposReal
  · have hηpos : 0 < η := lt_of_le_of_ne hη (Ne.symm hη0)
    have hreal := Polynomial.Chebyshev.U_real_cosh η ((K - 1 : ℕ) : ℤ)
    have hreal' :
        chebyshevU (K - 1 : ℕ) (Real.cosh η) * Real.sinh η =
          Real.sinh (K * η) := by
      simpa only [chebyshevU, Int.cast_add, Int.cast_natCast, Int.cast_one,
        hcast] using hreal
    have hprod :
        0 < chebyshevU (K - 1 : ℕ) (Real.cosh η) * Real.sinh η := by
      rw [hreal']
      exact Real.sinh_pos_iff.mpr (mul_pos (by positivity) hηpos)
    exact pos_of_mul_pos_left hprod (Real.sinh_pos_iff.mpr hηpos).le

/-- Exact coordinate equivalence `Phi_K(theta)=W_K(cos theta)`. -/
theorem chordLobeWeight_cos (K : ℕ) (a θ : ℝ) :
    chordLobeWeight K a (Real.cos θ) = chordPhi K a θ := by
  rfl

/-- Exact coordinate equivalence `Psi_K(eta)=W_K(cosh eta)`. -/
theorem chordLobeWeight_cosh (K : ℕ) (a η : ℝ)
    (hK : 2 ≤ K) (hη : 0 ≤ η) :
    chordLobeWeight K a (Real.cosh η) = chordPsi K a η := by
  simp only [chordLobeWeight, chordPsi, halfHypRadical]
  rw [abs_of_pos (chebyshevU_cosh_pos K hK hη)]

/-- Denominator-free form of the source definition of `Phi_K`; it also
records its continuous interpretation at `theta=0,pi`. -/
theorem chordPhi_mul_sin {K : ℕ} (a θ : ℝ)
    (hK : 2 ≤ K)
    (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi) :
    chordPhi K a θ * Real.sin θ =
      halfTrigRadical a θ * |Real.sin (K * θ)| := by
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθpi
  have hcheb := chebyshevU_cos_mul_sin (K - 1 : ℕ) θ
  have hcast : ((K - 1 : ℕ) : ℝ) + 1 = K := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ K)
  have hcheb' :
      chebyshevU (K - 1 : ℕ) (Real.cos θ) * Real.sin θ =
        Real.sin (K * θ) := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one, hcast] using hcheb
  rw [chordPhi, mul_assoc]
  congr 1
  rw [← abs_of_nonneg hsin, ← abs_mul, hcheb']

/-- Away from the two trigonometric endpoints, the continuous definition
is the quotient printed in `eq:Phi-Psi-def`. -/
theorem chordPhi_eq_sine_quotient {K : ℕ} (a θ : ℝ)
    (hK : 2 ≤ K)
    (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi)
    (hsin : Real.sin θ ≠ 0) :
    chordPhi K a θ =
      halfTrigRadical a θ * |Real.sin (K * θ)| / Real.sin θ := by
  apply (eq_div_iff hsin).2
  exact chordPhi_mul_sin a θ hK hθ0 hθpi

/-- Denominator-free hyperbolic formula, valid also at `eta=0`. -/
theorem chordPsi_mul_sinh (K : ℕ) (a η : ℝ) (hK : 2 ≤ K) :
    chordPsi K a η * Real.sinh η =
      halfHypRadical a η * Real.sinh (K * η) := by
  have hcast : ((K - 1 : ℕ) : ℝ) + 1 = K := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ K)
  rw [chordPsi, mul_assoc, chebyshevU]
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one, hcast] using
    congrArg (halfHypRadical a η * ·)
      (Polynomial.Chebyshev.U_real_cosh η ((K - 1 : ℕ) : ℤ))

/-- The quotient formula for positive hyperbolic coordinate. -/
theorem chordPsi_eq_sinh_quotient {K : ℕ} (a η : ℝ)
    (hK : 2 ≤ K) (hη : η ≠ 0) :
    chordPsi K a η =
      halfHypRadical a η * Real.sinh (K * η) / Real.sinh η := by
  apply (eq_div_iff (Real.sinh_ne_zero.mpr hη)).2
  exact chordPsi_mul_sinh K a η hK

/-- Both continuous endpoint values of `W_K` vanish. -/
@[simp] theorem chordLobeWeight_cosh_endpoint (K : ℕ) (a : ℝ) :
    chordLobeWeight K a (Real.cosh (pathLogParameter a)) = 0 := by
  simp [chordLobeWeight]

@[simp] theorem chordLobeWeight_neg_cosh_endpoint (K : ℕ) (a : ℝ) :
    chordLobeWeight K a (-Real.cosh (pathLogParameter a)) = 0 := by
  simp [chordLobeWeight]

/-- Exact product over the simple Chebyshev nodes. -/
theorem chebyshevU_eq_chordNodeProduct (K : ℕ) (hK : 2 ≤ K) (u : ℝ) :
    chebyshevU (K - 1 : ℕ) u =
      2 ^ (K - 1) * chordNodeProduct K u := by
  let p : ℝ[X] := Polynomial.Chebyshev.U ℝ (K - 1 : ℕ)
  have hcard : p.roots.card = p.natDegree := by
    dsimp only [p]
    rw [Polynomial.Chebyshev.roots_U_real,
      Polynomial.Chebyshev.natDegree_U_natCast]
    change (Finset.image _ (Finset.range (K - 1))).card = K - 1
    rw [Finset.card_image_of_injOn, Finset.card_range]
    exact (Finset.range (K - 1)).nodup_map_iff_injOn.mp
      (Polynomial.Chebyshev.roots_U_real_nodup (K - 1))
  have hpoly := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (p := p) hcard
  have heval := congrArg (fun q : ℝ[X] => q.eval u) hpoly
  have hcast : ((K - 1 : ℕ) : ℝ) + 1 = K := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ K)
  dsimp only [p] at heval
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_apply,
    Polynomial.eval_sub, Polynomial.eval_X] at heval
  rw [Polynomial.Chebyshev.leadingCoeff_U_natCast,
    Polynomial.Chebyshev.roots_U_real] at heval
  simp only [hcast] at heval
  simpa only [chebyshevU, chordNodeProduct, chordNodes,
    Nat.cast_add, Nat.cast_one, Finset.prod_eq_multiset_prod] using heval.symm

/-- Away from all nodal and radical zeros, `log W_K` is the explicit sum
of logarithms over the Chebyshev roots. -/
theorem log_chordLobeWeight_eq (K : ℕ) (hK : 2 ≤ K) (a u : ℝ)
    (hnodes : ∀ r ∈ chordNodes K, u ≠ r)
    (hu : |u| < Real.cosh (pathLogParameter a)) :
    Real.log (chordLobeWeight K a u) =
      Real.log (2 ^ (K - 1) : ℝ) + chordLogProfile K a u := by
  let c := Real.cosh (pathLogParameter a)
  have hubounds : -c < u ∧ u < c := by
    simpa only [abs_lt] using hu
  have hradpos : 0 < c ^ 2 - u ^ 2 := by
    have hprod : 0 < (c - u) * (c + u) :=
      mul_pos (sub_pos.mpr hubounds.2) (by linarith)
    nlinarith
  have hnodeProd : chordNodeProduct K u ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro r hr
    exact sub_ne_zero.mpr (hnodes r hr)
  have hpowpos : 0 < (2 : ℝ) ^ (K - 1) := by positivity
  have hcheb :
      chebyshevU (K - 1 : ℕ) u =
        2 ^ (K - 1) * chordNodeProduct K u :=
    chebyshevU_eq_chordNodeProduct K hK u
  have hsqrtne : Real.sqrt (c ^ 2 - u ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hradpos).ne'
  have habsChebne :
      |chebyshevU (K - 1 : ℕ) u| ≠ 0 := by
    rw [abs_ne_zero]
    rw [hcheb]
    exact mul_ne_zero hpowpos.ne' hnodeProd
  have hlogNodes :
      Real.log |chordNodeProduct K u| =
        ∑ r ∈ chordNodes K, Real.log |u - r| := by
    rw [chordNodeProduct, Finset.abs_prod, Real.log_prod]
    intro r hr
    exact abs_ne_zero.mpr (sub_ne_zero.mpr (hnodes r hr))
  change Real.log (Real.sqrt (c ^ 2 - u ^ 2) *
    |chebyshevU (K - 1 : ℕ) u|) = _
  rw [Real.log_mul hsqrtne habsChebne, Real.log_sqrt hradpos.le,
    hcheb, abs_mul, abs_of_pos hpowpos,
    Real.log_mul hpowpos.ne' (abs_ne_zero.mpr hnodeProd), hlogNodes]
  simp only [chordLogProfile, c]
  ring

/-- The derivative of the explicit logarithmic profile is exactly the
source's logarithmic derivative. -/
theorem hasDerivAt_chordLogProfile (K : ℕ) (a u : ℝ)
    (hnodes : ∀ r ∈ chordNodes K, u ≠ r)
    (hu : |u| < Real.cosh (pathLogParameter a)) :
    HasDerivAt (chordLogProfile K a) (chordLogSlope K a u) u := by
  let c := Real.cosh (pathLogParameter a)
  have hubounds : -c < u ∧ u < c := by
    simpa only [abs_lt] using hu
  have hradpos : 0 < c ^ 2 - u ^ 2 := by
    have hprod : 0 < (c - u) * (c + u) :=
      mul_pos (sub_pos.mpr hubounds.2) (by linarith)
    nlinarith
  have hrad : HasDerivAt (fun v : ℝ => c ^ 2 - v ^ 2) (-2 * u) u := by
    convert (hasDerivAt_const u (c ^ 2)).sub (hasDerivAt_pow 2 u) using 1
    ring
  have hfirst :
      HasDerivAt (fun v : ℝ => Real.log (c ^ 2 - v ^ 2) / 2)
        (-u / (c ^ 2 - u ^ 2)) u := by
    convert (hrad.log hradpos.ne').div_const 2 using 1
    field_simp [hradpos.ne']
  have hsum :
      HasDerivAt (fun v : ℝ => ∑ r ∈ chordNodes K, Real.log |v - r|)
        (∑ r ∈ chordNodes K, (u - r)⁻¹) u := by
    apply HasDerivAt.fun_sum
    intro r hr
    have h := ((hasDerivAt_id u).sub_const r).log
      (sub_ne_zero.mpr (hnodes r hr))
    simpa only [Real.log_abs, one_div] using h
  change HasDerivAt
    (fun v : ℝ => Real.log (c ^ 2 - v ^ 2) / 2 +
      ∑ r ∈ chordNodes K, Real.log |v - r|)
    ((∑ r ∈ chordNodes K, (u - r)⁻¹) -
      u / (c ^ 2 - u ^ 2)) u
  simpa only [sub_eq_add_neg, neg_div, add_comm] using hfirst.add hsum

/-- The exact derivative identity behind `eq:W-log-concave`. -/
theorem hasDerivAt_chordLogSlope (K : ℕ) (a u : ℝ)
    (hnodes : ∀ r ∈ chordNodes K, u ≠ r)
    (hu : |u| < Real.cosh (pathLogParameter a)) :
    HasDerivAt (chordLogSlope K a) (chordLogCurvature K a u) u := by
  let c := Real.cosh (pathLogParameter a)
  have hsum :
      HasDerivAt (fun v : ℝ => ∑ r ∈ chordNodes K, (v - r)⁻¹)
        (∑ r ∈ chordNodes K, -(1 / (u - r) ^ 2)) u := by
    apply HasDerivAt.fun_sum
    intro r hr
    convert ((hasDerivAt_id u).sub_const r).inv
      (sub_ne_zero.mpr (hnodes r hr)) using 1
    · field_simp [hnodes r hr]
      simp only [id_eq]
  have hubounds : -c < u ∧ u < c := by
    simpa only [abs_lt] using hu
  have hradpos : 0 < c ^ 2 - u ^ 2 := by
    have hprod : 0 < (c - u) * (c + u) :=
      mul_pos (sub_pos.mpr hubounds.2) (by linarith)
    nlinarith
  have hden : HasDerivAt (fun v : ℝ => c ^ 2 - v ^ 2) (-2 * u) u := by
    convert (hasDerivAt_const u (c ^ 2)).sub (hasDerivAt_pow 2 u) using 1
    ring
  have hquot :
      HasDerivAt (fun v : ℝ => v / (c ^ 2 - v ^ 2))
        ((c ^ 2 + u ^ 2) / (c ^ 2 - u ^ 2) ^ 2) u := by
    convert (hasDerivAt_id u).div hden hradpos.ne' using 1
    · field_simp [hradpos.ne']
      simp only [id_eq]
      ring
  simpa only [chordLogSlope, chordLogCurvature, one_div,
    Finset.sum_neg_distrib] using hsum.sub hquot

/-- Strict negativity in `eq:W-log-concave`. -/
theorem chordLogCurvature_neg (K : ℕ) (a u : ℝ)
    (hu : |u| < Real.cosh (pathLogParameter a)) :
    chordLogCurvature K a u < 0 := by
  let c := Real.cosh (pathLogParameter a)
  have hc : 0 < c := Real.cosh_pos _
  have hubounds : -c < u ∧ u < c := by
    simpa only [abs_lt] using hu
  have hradpos : 0 < c ^ 2 - u ^ 2 := by
    have hprod : 0 < (c - u) * (c + u) :=
      mul_pos (sub_pos.mpr hubounds.2) (by linarith)
    nlinarith
  have hsum : 0 ≤ ∑ r ∈ chordNodes K, 1 / (u - r) ^ 2 := by
    positivity
  have hlast :
      0 < (c ^ 2 + u ^ 2) / (c ^ 2 - u ^ 2) ^ 2 := by
    positivity
  change -(∑ r ∈ chordNodes K, 1 / (u - r) ^ 2) -
    (c ^ 2 + u ^ 2) / (c ^ 2 - u ^ 2) ^ 2 < 0
  linarith

/-- On any closed interval strictly between the radical endpoints and
containing no node, the logarithmic derivative is strictly decreasing. -/
theorem chordLogSlope_strictAntiOn_Icc (K : ℕ) (a l r : ℝ)
    (hdom : Icc l r ⊆
      Ioo (-Real.cosh (pathLogParameter a))
        (Real.cosh (pathLogParameter a)))
    (hnodes : ∀ u ∈ Icc l r, ∀ q ∈ chordNodes K, u ≠ q) :
    StrictAntiOn (chordLogSlope K a) (Icc l r) := by
  have hderiv : ∀ u ∈ Icc l r,
      HasDerivAt (chordLogSlope K a) (chordLogCurvature K a u) u := by
    intro u hu
    apply hasDerivAt_chordLogSlope K a u (hnodes u hu)
    simpa only [abs_lt] using hdom hu
  apply strictAntiOn_of_deriv_neg (convex_Icc l r)
  · intro u hu
    exact (hderiv u hu).continuousAt.continuousWithinAt
  · intro u hu
    have huIcc : u ∈ Icc l r := interior_subset hu
    rw [(hderiv u huIcc).deriv]
    exact chordLogCurvature_neg K a u (by
      simpa only [abs_lt] using hdom huIcc)

/-- Open-interval form, used when the interval endpoints themselves are
Chebyshev nodes. -/
theorem chordLogSlope_strictAntiOn_Ioo (K : ℕ) (a l r : ℝ)
    (hdom : Ioo l r ⊆
      Ioo (-Real.cosh (pathLogParameter a))
        (Real.cosh (pathLogParameter a)))
    (hnodes : ∀ u ∈ Ioo l r, ∀ q ∈ chordNodes K, u ≠ q) :
    StrictAntiOn (chordLogSlope K a) (Ioo l r) := by
  have hderiv : ∀ u ∈ Ioo l r,
      HasDerivAt (chordLogSlope K a) (chordLogCurvature K a u) u := by
    intro u hu
    apply hasDerivAt_chordLogSlope K a u (hnodes u hu)
    simpa only [abs_lt] using hdom hu
  apply strictAntiOn_of_deriv_neg (convex_Ioo l r)
  · intro u hu
    exact (hderiv u hu).continuousAt.continuousWithinAt
  · intro u hu
    have huIoo : u ∈ Ioo l r := by simpa only [interior_Ioo] using hu
    rw [(hderiv u huIoo).deriv]
    exact chordLogCurvature_neg K a u (by
      simpa only [abs_lt] using hdom huIoo)

/-- Every genuine nodal lobe has a unique maximum.  The hypotheses say
precisely that the two endpoints are zeros, the open interval is positive,
lies between the radical endpoints, and contains no Chebyshev node. -/
theorem existsUnique_chordLobeMaximum (K : ℕ) (hK : 2 ≤ K)
    (a l r : ℝ) (hlr : l < r)
    (hleft : chordLobeWeight K a l = 0)
    (hright : chordLobeWeight K a r = 0)
    (hpos : ∀ u ∈ Ioo l r, 0 < chordLobeWeight K a u)
    (hdom : Ioo l r ⊆
      Ioo (-Real.cosh (pathLogParameter a))
        (Real.cosh (pathLogParameter a)))
    (hnodes : ∀ u ∈ Ioo l r, ∀ q ∈ chordNodes K, u ≠ q) :
    ∃! u : ℝ, u ∈ Ioo l r ∧
      IsMaxOn (chordLobeWeight K a) (Icc l r) u := by
  obtain ⟨u, huIcc, huMax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨l, le_rfl, hlr.le⟩ (continuous_chordLobeWeight K a).continuousOn
  let m : ℝ := (l + r) / 2
  have hmIoo : m ∈ Ioo l r := by
    constructor <;> dsimp [m] <;> linarith
  have huPos : 0 < chordLobeWeight K a u :=
    (hpos m hmIoo).trans_le (huMax ⟨hmIoo.1.le, hmIoo.2.le⟩)
  have huIoo : u ∈ Ioo l r := by
    constructor
    · refine lt_of_le_of_ne huIcc.1 ?_
      intro hlu
      have hueq : u = l := hlu.symm
      rw [hueq, hleft] at huPos
      exact (lt_irrefl 0 huPos)
    · refine lt_of_le_of_ne huIcc.2 ?_
      intro hur
      rw [hur, hright] at huPos
      exact (lt_irrefl 0 huPos)
  have hcritical : ∀ p ∈ Ioo l r,
      IsMaxOn (chordLobeWeight K a) (Icc l r) p →
        chordLogSlope K a p = 0 := by
    intro p hp hpMax
    have hpLocal : IsLocalMax (chordLogProfile K a) p := by
      refine eventually_nhds_iff.mpr
        ⟨Ioo l r, ?_, isOpen_Ioo, hp.1, hp.2⟩
      intro v hv
      have hweight := hpMax ⟨hv.1.le, hv.2.le⟩
      have hlog := Real.log_le_log (hpos v hv) hweight
      rw [log_chordLobeWeight_eq K hK a v (hnodes v hv)
          (by simpa only [abs_lt] using hdom hv),
        log_chordLobeWeight_eq K hK a p (hnodes p hp)
          (by simpa only [abs_lt] using hdom hp)] at hlog
      linarith
    exact hpLocal.hasDerivAt_eq_zero
      (hasDerivAt_chordLogProfile K a p (hnodes p hp)
        (by simpa only [abs_lt] using hdom hp))
  have hanti := chordLogSlope_strictAntiOn_Ioo K a l r hdom hnodes
  refine ⟨u, ⟨huIoo, huMax⟩, ?_⟩
  intro v hv
  by_contra huv
  have hsu := hcritical u huIoo huMax
  have hsv := hcritical v hv.1 hv.2
  rcases lt_or_gt_of_ne huv with huvlt | hvult
  · have hlt := hanti hv.1 huIoo huvlt
    rw [hsu, hsv] at hlt
    exact (lt_irrefl 0 hlt)
  · have hlt := hanti huIoo hv.1 hvult
    rw [hsu, hsv] at hlt
    exact (lt_irrefl 0 hlt)

/-- Every member of the explicit nodal set is a zero of `W_K`. -/
theorem chordLobeWeight_eq_zero_of_mem_chordNodes
    (K : ℕ) (hK : 2 ≤ K) (a : ℝ) {q : ℝ}
    (hq : q ∈ chordNodes K) :
    chordLobeWeight K a q = 0 := by
  rw [chordLobeWeight, chebyshevU_eq_chordNodeProduct K hK]
  have hprod : chordNodeProduct K q = 0 := by
    apply Finset.prod_eq_zero hq
    simp
  rw [hprod]
  simp

/-- Every Chebyshev node is at most the first (rightmost) node. -/
theorem chordNode_le_first (K : ℕ) (hK : 2 ≤ K) {q : ℝ}
    (hq : q ∈ chordNodes K) :
    q ≤ Real.cos (Real.pi / K) := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
  have hKpos : (0 : ℝ) < K := by positivity
  have hangleNonneg : 0 ≤ Real.pi / (K : ℝ) := by positivity
  have hangleLe :
      Real.pi / (K : ℝ) ≤
        ((k + 1 : ℕ) : ℝ) * Real.pi / K := by
    rw [div_le_div_iff_of_pos_right hKpos]
    have hkone : (1 : ℝ) ≤ k + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    simpa only [Nat.cast_add, Nat.cast_one, one_mul] using
      (mul_le_mul_of_nonneg_right hkone Real.pi_pos.le)
  have hanglePi :
      ((k + 1 : ℕ) : ℝ) * Real.pi / K ≤ Real.pi := by
    rw [div_le_iff₀ hKpos]
    have hklt : k < K - 1 := Finset.mem_range.mp hk
    have hkcast : ((k + 1 : ℕ) : ℝ) ≤ K := by
      exact_mod_cast (by omega : k + 1 ≤ K)
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_right hkcast Real.pi_pos.le)
  exact Real.cos_le_cos_of_nonneg_of_le_pi hangleNonneg hanglePi hangleLe

/-- Every Chebyshev chord node lies in the closed spectral coordinate
interval `[-1,1]`. -/
theorem chordNode_mem_Icc (K : ℕ) {q : ℝ} (hq : q ∈ chordNodes K) :
    q ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
  exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- Every lobe between adjacent Chebyshev nodes has a unique maximum.  The
adjacency hypothesis is the order-theoretic statement that no node lies in
the open interval `(l,r)`. -/
theorem existsUnique_adjacentChordNodeLobeMaximum
    (K : ℕ) (hK : 2 ≤ K) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    {l r : ℝ} (hl : l ∈ chordNodes K) (hr : r ∈ chordNodes K)
    (hlr : l < r)
    (hadjacent : ∀ q ∈ chordNodes K, q ≤ l ∨ r ≤ q) :
    ∃! u : ℝ, u ∈ Ioo l r ∧
      IsMaxOn (chordLobeWeight K a) (Icc l r) u := by
  let c := Real.cosh (pathLogParameter a)
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha₀ ha₁
  have hcOne : 1 < c := by
    dsimp [c]
    exact Real.one_lt_cosh.mpr hh.ne'
  have hlBounds := chordNode_mem_Icc K hl
  have hrBounds := chordNode_mem_Icc K hr
  have hdom : Ioo l r ⊆ Ioo (-c) c := by
    intro u hu
    have hleft : -c < u :=
      ((neg_lt_neg hcOne).trans_le hlBounds.1).trans hu.1
    have hright : u < c :=
      (hu.2.trans_le hrBounds.2).trans hcOne
    exact ⟨hleft, hright⟩
  have hnodes : ∀ u ∈ Ioo l r, ∀ q ∈ chordNodes K, u ≠ q := by
    intro u hu q hq huq
    subst u
    rcases hadjacent q hq with hql | hrq
    · exact (not_lt_of_ge hql) hu.1
    · exact (not_lt_of_ge hrq) hu.2
  have hpos : ∀ u ∈ Ioo l r, 0 < chordLobeWeight K a u := by
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
  exact existsUnique_chordLobeMaximum K hK a l r hlr
    (chordLobeWeight_eq_zero_of_mem_chordNodes K hK a hl)
    (chordLobeWeight_eq_zero_of_mem_chordNodes K hK a hr)
    hpos hdom hnodes

/-- The first Chebyshev node belongs to the explicit nodal set. -/
theorem first_mem_chordNodes (K : ℕ) (hK : 2 ≤ K) :
    Real.cos (Real.pi / K) ∈ chordNodes K := by
  rw [chordNodes, Finset.mem_image]
  refine ⟨0, ?_, ?_⟩
  · simp
    omega
  · norm_num

/-- The outer interval from the source has a unique lobe maximum. -/
theorem existsUnique_outerChordLobeMaximum (K : ℕ) (hK : 2 ≤ K)
    (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    ∃! u : ℝ,
      u ∈ Ioo (Real.cos (Real.pi / K))
        (Real.cosh (pathLogParameter a)) ∧
      IsMaxOn (chordLobeWeight K a)
        (Icc (Real.cos (Real.pi / K))
          (Real.cosh (pathLogParameter a))) u := by
  let l := Real.cos (Real.pi / K)
  let c := Real.cosh (pathLogParameter a)
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha₀ ha₁
  have hcOne : 1 < c := by
    dsimp [c]
    exact Real.one_lt_cosh.mpr hh.ne'
  have hlc : l < c :=
    (Real.cos_le_one (Real.pi / K)).trans_lt hcOne
  have hlzero : chordLobeWeight K a l = 0 := by
    apply chordLobeWeight_eq_zero_of_mem_chordNodes K hK a
    exact first_mem_chordNodes K hK
  have hcZero : chordLobeWeight K a c = 0 := by
    exact chordLobeWeight_cosh_endpoint K a
  have hnodeUpper : ∀ q ∈ chordNodes K, q ≤ l := by
    intro q hq
    exact chordNode_le_first K hK hq
  have hlNonneg : 0 ≤ l := by
    dsimp [l]
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · have hdiv : 0 ≤ Real.pi / (K : ℝ) := by positivity
      linarith [Real.pi_pos]
    · have hKpos : (0 : ℝ) < K := by positivity
      rw [div_le_iff₀ hKpos]
      have hKcast : (2 : ℝ) ≤ K := by exact_mod_cast hK
      nlinarith [Real.pi_pos]
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
  simpa only [l, c] using existsUnique_chordLobeMaximum K hK a l c hlc
    hlzero hcZero hpos hdom hnodes

/-- At an interior maximum of a positive nodal lobe, the exact logarithmic
derivative vanishes. -/
theorem chordLogSlope_eq_zero_of_isMaxOn (K : ℕ) (hK : 2 ≤ K)
    (a l r : ℝ)
    (hpos : ∀ u ∈ Ioo l r, 0 < chordLobeWeight K a u)
    (hdom : Ioo l r ⊆
      Ioo (-Real.cosh (pathLogParameter a))
        (Real.cosh (pathLogParameter a)))
    (hnodes : ∀ u ∈ Ioo l r, ∀ q ∈ chordNodes K, u ≠ q)
    {p : ℝ} (hp : p ∈ Ioo l r)
    (hpMax : IsMaxOn (chordLobeWeight K a) (Icc l r) p) :
    chordLogSlope K a p = 0 := by
  have hpLocal : IsLocalMax (chordLogProfile K a) p := by
    refine eventually_nhds_iff.mpr
      ⟨Ioo l r, ?_, isOpen_Ioo, hp.1, hp.2⟩
    intro v hv
    have hweight := hpMax ⟨hv.1.le, hv.2.le⟩
    have hlog := Real.log_le_log (hpos v hv) hweight
    rw [log_chordLobeWeight_eq K hK a v (hnodes v hv)
        (by simpa only [abs_lt] using hdom hv),
      log_chordLobeWeight_eq K hK a p (hnodes p hp)
        (by simpa only [abs_lt] using hdom hp)] at hlog
    linarith
  exact hpLocal.hasDerivAt_eq_zero
    (hasDerivAt_chordLogProfile K a p (hnodes p hp)
      (by simpa only [abs_lt] using hdom hp))

/-- From its unique maximum to the right endpoint, a positive nodal lobe is
strictly decreasing.  This is the endpoint-side monotonicity used in the
outer branch selection argument. -/
theorem chordLobeWeight_strictAntiOn_endpointSide
    (K : ℕ) (hK : 2 ≤ K) (a l r : ℝ)
    (hright : chordLobeWeight K a r = 0)
    (hpos : ∀ u ∈ Ioo l r, 0 < chordLobeWeight K a u)
    (hdom : Ioo l r ⊆
      Ioo (-Real.cosh (pathLogParameter a))
        (Real.cosh (pathLogParameter a)))
    (hnodes : ∀ u ∈ Ioo l r, ∀ q ∈ chordNodes K, u ≠ q)
    {p : ℝ} (hp : p ∈ Ioo l r)
    (hpMax : IsMaxOn (chordLobeWeight K a) (Icc l r) p) :
    StrictAntiOn (chordLobeWeight K a) (Ioc p r) := by
  have hpSlope : chordLogSlope K a p = 0 :=
    chordLogSlope_eq_zero_of_isMaxOn K hK a l r hpos hdom hnodes hp hpMax
  have hslopeAnti := chordLogSlope_strictAntiOn_Ioo K a l r hdom hnodes
  intro x hx y hy hxy
  by_cases hyr : y = r
  · subst y
    rw [hright]
    exact hpos x ⟨hp.1.trans hx.1, hxy⟩
  · have hylt : y < r := lt_of_le_of_ne hy.2 hyr
    have hxIoo : x ∈ Ioo l r :=
      ⟨hp.1.trans hx.1, hxy.trans hylt⟩
    have hyIoo : y ∈ Ioo l r :=
      ⟨hp.1.trans (hx.1.trans hxy), hylt⟩
    have hprofileAnti :
        StrictAntiOn (chordLogProfile K a) (Icc x y) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc x y)
      · intro z hz
        have hzIoo : z ∈ Ioo l r :=
          ⟨hp.1.trans (hx.1.trans_le hz.1), hz.2.trans_lt hylt⟩
        exact (hasDerivAt_chordLogProfile K a z (hnodes z hzIoo)
          (by simpa only [abs_lt] using hdom hzIoo)).continuousAt.continuousWithinAt
      · intro z hz
        have hzIcc : z ∈ Icc x y := interior_subset hz
        have hzIoo : z ∈ Ioo l r :=
          ⟨hp.1.trans (hx.1.trans_le hzIcc.1), hzIcc.2.trans_lt hylt⟩
        have hzDeriv := hasDerivAt_chordLogProfile K a z
          (hnodes z hzIoo) (by simpa only [abs_lt] using hdom hzIoo)
        rw [hzDeriv.deriv]
        have hzSlope : chordLogSlope K a z < chordLogSlope K a p :=
          hslopeAnti hp hzIoo (hx.1.trans_le hzIcc.1)
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

/-- Every level between zero and a nodal-lobe maximum has exactly one
solution on the endpoint side of that maximum. -/
theorem existsUnique_chordLobeEndpointSolution
    (K : ℕ) (hK : 2 ≤ K) (a l r : ℝ)
    (hright : chordLobeWeight K a r = 0)
    (hpos : ∀ u ∈ Ioo l r, 0 < chordLobeWeight K a u)
    (hdom : Ioo l r ⊆
      Ioo (-Real.cosh (pathLogParameter a))
        (Real.cosh (pathLogParameter a)))
    (hnodes : ∀ u ∈ Ioo l r, ∀ q ∈ chordNodes K, u ≠ q)
    {p level : ℝ} (hp : p ∈ Ioo l r)
    (hpMax : IsMaxOn (chordLobeWeight K a) (Icc l r) p)
    (hlevel₀ : 0 ≤ level)
    (hlevelMax : level < chordLobeWeight K a p) :
    ∃! z : ℝ, z ∈ Ioc p r ∧ chordLobeWeight K a z = level := by
  have hanti := chordLobeWeight_strictAntiOn_endpointSide K hK a l r
    hright hpos hdom hnodes hp hpMax
  have hlevel : level ∈ Icc (chordLobeWeight K a r)
      (chordLobeWeight K a p) := by
    rw [hright]
    exact ⟨hlevel₀, hlevelMax.le⟩
  obtain ⟨z, hzIcc, hzEq⟩ :=
    (intermediate_value_Icc' hp.2.le
      (continuous_chordLobeWeight K a).continuousOn) hlevel
  have hpz : p < z := by
    refine lt_of_le_of_ne hzIcc.1 ?_
    intro hpz
    apply (ne_of_lt hlevelMax)
    simpa only [← hpz] using hzEq.symm
  have hzIoc : z ∈ Ioc p r := ⟨hpz, hzIcc.2⟩
  refine ⟨z, ⟨hzIoc, hzEq⟩, ?_⟩
  intro y hy
  apply hanti.injOn hy.1 hzIoc
  rw [hy.2, hzEq]

/-- The source's endpoint-side outer solution, stated directly for the
outer interval `(cos(pi/K), cosh(h))`. -/
theorem existsUnique_outerChordLobeEndpointSolution
    (K : ℕ) (hK : 2 ≤ K) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    {p level : ℝ}
    (hp : p ∈ Ioo (Real.cos (Real.pi / K))
      (Real.cosh (pathLogParameter a)))
    (hpMax : IsMaxOn (chordLobeWeight K a)
      (Icc (Real.cos (Real.pi / K))
        (Real.cosh (pathLogParameter a))) p)
    (hlevel₀ : 0 ≤ level)
    (hlevelMax : level < chordLobeWeight K a p) :
    ∃! z : ℝ,
      z ∈ Ioc p (Real.cosh (pathLogParameter a)) ∧
        chordLobeWeight K a z = level := by
  let l := Real.cos (Real.pi / K)
  let c := Real.cosh (pathLogParameter a)
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha₀ ha₁
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
  simpa only [l, c] using existsUnique_chordLobeEndpointSolution K hK a l c
    hright hpos hdom hnodes hp hpMax hlevel₀ hlevelMax

end

end ConnectedPseudospectrum
