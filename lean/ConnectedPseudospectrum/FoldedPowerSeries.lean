import ConnectedPseudospectrum.FoldedGenerating
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Formal folded generating functions

The fourth-order transfer recurrence and its boundary residuals are assembled
here into exact formal-power-series identities.  No analytic convergence
hypothesis is used.
-/

namespace ConnectedPseudospectrum

open PowerSeries

noncomputable section

/-- The denominator polynomial `Π(z)` of the folded generating functions. -/
def foldRecurrenceSeries (a x s : ℝ) : PowerSeries ℝ :=
  1 - C (foldC0 a x s) * X ^ 1 + C (foldB a x s) * X ^ 2 -
    C (a ^ 2 * foldC0 a x s) * X ^ 3 + C (a ^ 4) * X ^ 4

/-- Formal generating series of the even folded transfer sequence. -/
def foldEvenPowerSeries (a x s : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (foldEvenSequence a x s)

/-- Formal generating series of the odd folded transfer sequence. -/
def foldOddPowerSeries (a x s : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (foldOddSequence a x s)

/-- Boundary-residual numerator for the even folded series. -/
def foldEvenResidualSeries (a s : ℝ) : PowerSeries ℝ :=
  C 1 * X ^ 0 + C (a * (1 - 2 * foldZeta a s)) * X ^ 1 +
    C (a ^ 2 * (1 - 2 * foldZeta a s)) * X ^ 2 + C (a ^ 3) * X ^ 3

/-- Boundary-residual numerator for the odd folded series. -/
def foldOddResidualSeries (a x s : ℝ) : PowerSeries ℝ :=
  C (x - s) * X ^ 0 - C (x * (1 + a ^ 2) + 2 * a * s) * X ^ 1 +
    C (a ^ 2 * (x - s)) * X ^ 2

/-- A quadratic Chebyshev factor `1-2auz+a²z²`. -/
def foldQuadraticSeries (a u : ℝ) : PowerSeries ℝ :=
  1 - C (2 * a * u) * X ^ 1 + C (a ^ 2) * X ^ 2

/-- The symmetric sum and product identities for `ξ₊,ξ₋` factor the folded
recurrence polynomial into the two quadratic Chebyshev factors.  The
hypotheses are denominator-free, so the identity also applies at a collision
of the two folded variables. -/
theorem foldRecurrenceSeries_eq_mul_foldQuadraticSeries
    {a x s u v : ℝ}
    (hsum : 2 * a * (u + v) = foldC0 a x s)
    (hprod : a ^ 2 * (4 * u * v + 2) = foldB a x s) :
    foldRecurrenceSeries a x s =
      foldQuadraticSeries a u * foldQuadraticSeries a v := by
  rw [foldRecurrenceSeries, foldQuadraticSeries, foldQuadraticSeries,
    ← hsum, ← hprod]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

/-- Coefficient of a scalar monomial times an arbitrary formal series. -/
theorem coeff_C_mul_X_pow_mul_mk_real (c : ℝ) (j k : ℕ) (u : ℕ → ℝ) :
    coeff k (C c * X ^ j * PowerSeries.mk u) =
      c * if j ≤ k then u (k - j) else 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  simp

/-- Coefficient form of multiplying a sequence by the folded recurrence
polynomial, with negative indices represented by zero. -/
theorem coeff_foldRecurrenceSeries_mul_mk (a x s : ℝ)
    (u : ℕ → ℝ) (k : ℕ) :
    coeff k (foldRecurrenceSeries a x s * PowerSeries.mk u) =
      u k - foldC0 a x s * (if 1 ≤ k then u (k - 1) else 0) +
        foldB a x s * (if 2 ≤ k then u (k - 2) else 0) -
        a ^ 2 * foldC0 a x s * (if 3 ≤ k then u (k - 3) else 0) +
        a ^ 4 * (if 4 ≤ k then u (k - 4) else 0) := by
  rw [foldRecurrenceSeries]
  simp only [sub_mul, add_mul, one_mul, map_add, map_sub, coeff_mk,
    coeff_C_mul_X_pow_mul_mk_real]

/-- Exact coefficient table of the even residual polynomial. -/
theorem coeff_foldEvenResidualSeries (a s : ℝ) (k : ℕ) :
    coeff k (foldEvenResidualSeries a s) =
      (if k = 0 then 1 else 0) +
      (if k = 1 then a * (1 - 2 * foldZeta a s) else 0) +
      (if k = 2 then a ^ 2 * (1 - 2 * foldZeta a s) else 0) +
      (if k = 3 then a ^ 3 else 0) := by
  simp only [foldEvenResidualSeries, map_add, coeff_C_mul_X_pow]

/-- Exact coefficient table of the odd residual polynomial. -/
theorem coeff_foldOddResidualSeries (a x s : ℝ) (k : ℕ) :
    coeff k (foldOddResidualSeries a x s) =
      (if k = 0 then x - s else 0) -
      (if k = 1 then x * (1 + a ^ 2) + 2 * a * s else 0) +
      (if k = 2 then a ^ 2 * (x - s) else 0) := by
  rw [foldOddResidualSeries]
  rw [map_add, map_sub]
  rw [coeff_C_mul_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X_pow]

/-- Cross-multiplied even generating-function identity. -/
theorem foldRecurrenceSeries_mul_foldEvenPowerSeries
    {a x s : ℝ} (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    foldRecurrenceSeries a x s * foldEvenPowerSeries a x s =
      foldEvenResidualSeries a s := by
  ext k
  rw [foldEvenPowerSeries, coeff_foldRecurrenceSeries_mul_mk,
    coeff_foldEvenResidualSeries]
  by_cases hk : k < 4
  · interval_cases k
    · norm_num
      exact foldEvenSequence_zero a x s
    · norm_num
      exact foldEvenSequence_residual_one ha0 ha1
    · norm_num
      exact foldEvenSequence_residual_two ha0 ha1
    · norm_num
      exact foldEvenSequence_residual_three ha1
  · have hk4 : 4 ≤ k := by omega
    have hk3 : 3 ≤ k := by omega
    have hk2 : 2 ≤ k := by omega
    have hk1 : 1 ≤ k := by omega
    have hrec := foldEvenSequence_recurrence (a := a) (x := x) (s := s)
      ha1 (k - 4)
    have h4 : k - 4 + 4 = k := by omega
    have h3 : k - 4 + 3 = k - 1 := by omega
    have h2 : k - 4 + 2 = k - 2 := by omega
    have h1 : k - 4 + 1 = k - 3 := by omega
    rw [h4, h3, h2, h1] at hrec
    simp only [if_pos hk1, if_pos hk2, if_pos hk3, if_pos hk4,
      if_neg (show k ≠ 0 by omega),
      if_neg (show k ≠ 1 by omega), if_neg (show k ≠ 2 by omega),
      if_neg (show k ≠ 3 by omega), add_zero]
    exact hrec

/-- Cross-multiplied odd generating-function identity. -/
theorem foldRecurrenceSeries_mul_foldOddPowerSeries
    {a x s : ℝ} (ha1 : a ≠ 1) :
    foldRecurrenceSeries a x s * foldOddPowerSeries a x s =
      foldOddResidualSeries a x s := by
  ext k
  rw [foldOddPowerSeries, coeff_foldRecurrenceSeries_mul_mk,
    coeff_foldOddResidualSeries]
  by_cases hk : k < 4
  · interval_cases k
    · norm_num
      exact foldOddSequence_zero a x s
    · norm_num
      have h := foldOddSequence_residual_one (a := a) (x := x) (s := s) ha1
      nlinarith
    · norm_num
      exact foldOddSequence_residual_two ha1
    · norm_num
      exact foldOddSequence_residual_three ha1
  · have hk4 : 4 ≤ k := by omega
    have hk3 : 3 ≤ k := by omega
    have hk2 : 2 ≤ k := by omega
    have hk1 : 1 ≤ k := by omega
    have hrec := foldOddSequence_recurrence (a := a) (x := x) (s := s)
      ha1 (k - 4)
    have h4 : k - 4 + 4 = k := by omega
    have h3 : k - 4 + 3 = k - 1 := by omega
    have h2 : k - 4 + 2 = k - 2 := by omega
    have h1 : k - 4 + 1 = k - 3 := by omega
    rw [h4, h3, h2, h1] at hrec
    simp only [if_pos hk1, if_pos hk2, if_pos hk3, if_pos hk4,
      if_neg (show k ≠ 0 by omega),
      if_neg (show k ≠ 1 by omega), if_neg (show k ≠ 2 by omega),
      add_zero, sub_zero]
    exact hrec

/-- Factorization of the even numerator in
`eq:fold-generating-even`. -/
theorem foldEvenResidualSeries_eq_factorized (a s : ℝ) :
    foldEvenResidualSeries a s =
      (1 + C a * X) *
        (1 - C (2 * a * foldZeta a s) * X + C (a ^ 2) * X ^ 2) := by
  rw [foldEvenResidualSeries]
  simp only [map_one, map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- Formal quotient form of the even folded generating function. -/
theorem foldEvenPowerSeries_eq_mul_inv_recurrence
    {a x s : ℝ} (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    foldEvenPowerSeries a x s =
      foldEvenResidualSeries a s * (foldRecurrenceSeries a x s)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq (by
    simp [foldRecurrenceSeries] :
      constantCoeff (foldRecurrenceSeries a x s) ≠ 0)).2
  simpa [mul_comm] using foldRecurrenceSeries_mul_foldEvenPowerSeries ha0 ha1

/-- Formal quotient form of the odd folded generating function. -/
theorem foldOddPowerSeries_eq_mul_inv_recurrence
    {a x s : ℝ} (ha1 : a ≠ 1) :
    foldOddPowerSeries a x s =
      foldOddResidualSeries a x s * (foldRecurrenceSeries a x s)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq (by
    simp [foldRecurrenceSeries] :
      constantCoeff (foldRecurrenceSeries a x s) ≠ 0)).2
  simpa [mul_comm] using foldRecurrenceSeries_mul_foldOddPowerSeries ha1

end


end ConnectedPseudospectrum
