import ConnectedPseudospectrum.Definitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Logarithmic and hyperbolic path parameter

The folded calculation writes `a = exp (-2h)` with `h>0`.  This module
establishes that parametrization and the elementary identities used to turn
the folded variables into half-angle trigonometric and hyperbolic chords.
-/

namespace ConnectedPseudospectrum

noncomputable section

/-- The paper's positive logarithmic parameter `h=-log(a)/2`. -/
def pathLogParameter (a : ℝ) : ℝ :=
  -Real.log a / 2

/-- For `0<a<1`, the logarithmic path parameter is positive. -/
theorem pathLogParameter_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < pathLogParameter a := by
  have hlog : Real.log a < 0 := Real.log_neg ha0 ha1
  unfold pathLogParameter
  linarith

/-- Exact exponential recovery of the hopping parameter. -/
theorem exp_neg_two_mul_pathLogParameter {a : ℝ} (ha0 : 0 < a) :
    Real.exp (-2 * pathLogParameter a) = a := by
  have hexponent : -2 * pathLogParameter a = Real.log a := by
    unfold pathLogParameter
    ring
  rw [hexponent, Real.exp_log ha0]

/-- The paper's displayed orientation `a=exp(-2h)`. -/
theorem pathParameter_eq_exp_neg_two_mul {a : ℝ} (ha0 : 0 < a) :
    a = Real.exp (-2 * pathLogParameter a) :=
  (exp_neg_two_mul_pathLogParameter ha0).symm

/-- The square-root path rate is `exp(-h)`. -/
theorem pathRate_eq_exp_neg_pathLogParameter {a : ℝ} (ha0 : 0 < a) :
    pathRate a = Real.exp (-pathLogParameter a) := by
  calc
    pathRate a = Real.sqrt a := rfl
    _ = Real.sqrt (Real.exp (Real.log a)) := by rw [Real.exp_log ha0]
    _ = Real.exp (Real.log a / 2) := (Real.exp_half _).symm
    _ = Real.exp (-pathLogParameter a) := by
      congr 1
      unfold pathLogParameter
      ring

/-- The rate squared is the original hopping parameter. -/
theorem pathRate_mul_self {a : ℝ} (ha0 : 0 ≤ a) :
    pathRate a * pathRate a = a := by
  exact Real.mul_self_sqrt ha0

/-- Scaled hyperbolic-cosine identity
`2 sqrt(a) cosh(h)=1+a`. -/
theorem two_pathRate_mul_cosh_pathLogParameter {a : ℝ} (ha0 : 0 < a) :
    2 * pathRate a * Real.cosh (pathLogParameter a) = 1 + a := by
  let h := pathLogParameter a
  let r := pathRate a
  have hrneg : r = Real.exp (-h) := by
    dsimp only [r, h]
    exact pathRate_eq_exp_neg_pathLogParameter ha0
  have hrpos : r * Real.exp h = 1 := by
    calc
      r * Real.exp h = Real.exp (-h) * Real.exp h := by rw [hrneg]
      _ = Real.exp (-h + h) := (Real.exp_add (-h) h).symm
      _ = 1 := by simp
  have hrsq : r * r = a := by
    dsimp only [r]
    exact pathRate_mul_self ha0.le
  calc
    2 * r * Real.cosh h = r * (Real.exp h + Real.exp (-h)) := by
      rw [Real.cosh_eq]
      ring
    _ = r * Real.exp h + r * r := by rw [← hrneg]; ring
    _ = 1 + a := by rw [hrpos, hrsq]

/-- Scaled hyperbolic-sine identity
`2 sqrt(a) sinh(h)=1-a`. -/
theorem two_pathRate_mul_sinh_pathLogParameter {a : ℝ} (ha0 : 0 < a) :
    2 * pathRate a * Real.sinh (pathLogParameter a) = 1 - a := by
  let h := pathLogParameter a
  let r := pathRate a
  have hrneg : r = Real.exp (-h) := by
    dsimp only [r, h]
    exact pathRate_eq_exp_neg_pathLogParameter ha0
  have hrpos : r * Real.exp h = 1 := by
    calc
      r * Real.exp h = Real.exp (-h) * Real.exp h := by rw [hrneg]
      _ = Real.exp (-h + h) := (Real.exp_add (-h) h).symm
      _ = 1 := by simp
  have hrsq : r * r = a := by
    dsimp only [r]
    exact pathRate_mul_self ha0.le
  calc
    2 * r * Real.sinh h = r * (Real.exp h - Real.exp (-h)) := by
      rw [Real.sinh_eq]
      ring
    _ = r * Real.exp h - r * r := by rw [← hrneg]; ring
    _ = 1 - a := by rw [hrpos, hrsq]

/-- The trigonometric chord radical can equally be written with `sinh(h)`.
-/
theorem cosh_sq_sub_cos_sq
    (h θ : ℝ) :
    Real.cosh h ^ 2 - Real.cos θ ^ 2 =
      Real.sinh h ^ 2 + Real.sin θ ^ 2 := by
  nlinarith [Real.cosh_sq_sub_sinh_sq h, Real.sin_sq_add_cos_sq θ]

/-- The hyperbolic chord radical identity. -/
theorem cosh_sq_sub_cosh_sq
    (h η : ℝ) :
    Real.cosh h ^ 2 - Real.cosh η ^ 2 =
      Real.sinh h ^ 2 - Real.sinh η ^ 2 := by
  nlinarith [Real.cosh_sq_sub_sinh_sq h,
    Real.cosh_sq_sub_sinh_sq η]

/-- The scale `2r/cosh(h)` appearing in the half-angle parametrization has
an elementary expression in `a`. -/
theorem two_pathRate_div_cosh_pathLogParameter {a : ℝ} (ha0 : 0 < a) :
    2 * pathRate a / Real.cosh (pathLogParameter a) =
      4 * a / (1 + a) := by
  have hcosh : 0 < Real.cosh (pathLogParameter a) := Real.cosh_pos _
  have hsum : 0 < 1 + a := by linarith
  apply (div_eq_div_iff hcosh.ne' hsum.ne').2
  calc
    (2 * pathRate a) * (1 + a) =
        (2 * pathRate a) *
          (2 * pathRate a * Real.cosh (pathLogParameter a)) := by
      rw [two_pathRate_mul_cosh_pathLogParameter ha0]
    _ = (4 * (pathRate a * pathRate a)) *
        Real.cosh (pathLogParameter a) := by ring
    _ = (4 * a) * Real.cosh (pathLogParameter a) := by
      rw [pathRate_mul_self ha0.le]

end

end ConnectedPseudospectrum
