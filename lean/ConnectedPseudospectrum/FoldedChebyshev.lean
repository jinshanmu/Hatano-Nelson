import ConnectedPseudospectrum.Chebyshev
import ConnectedPseudospectrum.FoldedPowerSeries

/-!
# Folded Chebyshev generating functions

This module derives the scaled second-kind Chebyshev generating series and
uses formal divided differences to prove the even and odd formulas
`eq:fold-even` and `eq:fold-odd` for distinct folded variables.  The
identities are coefficientwise formal-power-series statements and require no
analytic convergence.
-/

namespace ConnectedPseudospectrum

open PowerSeries

noncomputable section

/-- The generating series with coefficients `a^m U_m(u)`. -/
def foldChebyshevSeries (a u : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun m => a ^ m * chebyshevU m u

theorem chebyshevU_nat_add_two (m : ℕ) (u : ℝ) :
    chebyshevU (m + 2) u =
      2 * u * chebyshevU (m + 1) u - chebyshevU m u := by
  simpa only [Int.natCast_add, Int.cast_ofNat] using
    chebyshevU_add_two (m : ℤ) u

theorem foldQuadraticSeries_mul_foldChebyshevSeries (a u : ℝ) :
    foldQuadraticSeries a u * foldChebyshevSeries a u = 1 := by
  ext k
  rw [foldChebyshevSeries,
    show coeff k (foldQuadraticSeries a u *
        PowerSeries.mk (fun m => a ^ m * chebyshevU m u)) =
      a ^ k * chebyshevU k u -
        2 * a * u * (if 1 ≤ k then a ^ (k - 1) *
          chebyshevU ((k - 1 : ℕ) : ℤ) u else 0) +
        a ^ 2 * (if 2 ≤ k then a ^ (k - 2) *
          chebyshevU ((k - 2 : ℕ) : ℤ) u else 0) by
      rw [foldQuadraticSeries]
      simp only [sub_mul, add_mul, one_mul, map_add, map_sub, coeff_mk,
        coeff_C_mul_X_pow_mul_mk_real]]
  by_cases hk0 : k = 0
  · subst k
    norm_num
  by_cases hk1 : k = 1
  · subst k
    norm_num
    ring
  have hk2 : 2 ≤ k := by omega
  have hrec := chebyshevU_nat_add_two (k - 2) u
  have h2 : ((k - 2 : ℕ) : ℤ) + 2 = (k : ℤ) := by omega
  have h1 : ((k - 2 : ℕ) : ℤ) + 1 = ((k - 1 : ℕ) : ℤ) := by omega
  rw [h2, h1] at hrec
  rw [PowerSeries.coeff_one]
  simp only [if_pos (show 1 ≤ k by omega), if_pos hk2, if_neg hk0]
  have hak1 : a ^ k = a * a ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hak2 : a ^ k = a ^ 2 * a ^ (k - 2) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    a ^ k * chebyshevU k u -
          2 * a * u * (a ^ (k - 1) *
            chebyshevU ((k - 1 : ℕ) : ℤ) u) +
        a ^ 2 * (a ^ (k - 2) * chebyshevU ((k - 2 : ℕ) : ℤ) u) =
      a ^ k * (chebyshevU k u -
        2 * u * chebyshevU ((k - 1 : ℕ) : ℤ) u +
        chebyshevU ((k - 2 : ℕ) : ℤ) u) := by
          linear_combination (norm := ring)
            (2 * u * chebyshevU ((k - 1 : ℕ) : ℤ) u) * hak1 -
              chebyshevU ((k - 2 : ℕ) : ℤ) u * hak2
    _ = 0 := by rw [hrec]; ring

theorem foldChebyshevSeries_eq_inv_foldQuadraticSeries (a u : ℝ) :
    foldChebyshevSeries a u = (foldQuadraticSeries a u)⁻¹ := by
  apply (eq_inv_iff_mul_eq_one (by
    simp [foldQuadraticSeries] :
      constantCoeff (foldQuadraticSeries a u) ≠ 0)).2
  simpa [mul_comm] using foldQuadraticSeries_mul_foldChebyshevSeries a u

/-- The generating series with coefficients
`a^m (U_m(u) + U_{m-1}(u))`. -/
def foldChebyshevPlusPrevSeries (a u : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun m =>
    a ^ m * (chebyshevU m u + chebyshevU ((m : ℤ) - 1) u)

theorem foldChebyshevPlusPrevSeries_eq (a u : ℝ) :
    foldChebyshevPlusPrevSeries a u =
      (1 + C a * X ^ 1) * foldChebyshevSeries a u := by
  ext k
  rw [foldChebyshevPlusPrevSeries, foldChebyshevSeries]
  rw [show coeff k ((1 + C a * X ^ 1) *
      PowerSeries.mk (fun m => a ^ m * chebyshevU m u)) =
      a ^ k * chebyshevU k u +
        a * (if 1 ≤ k then a ^ (k - 1) *
          chebyshevU ((k - 1 : ℕ) : ℤ) u else 0) by
    simp only [add_mul, one_mul, map_add, coeff_mk,
      coeff_C_mul_X_pow_mul_mk_real]]
  rw [coeff_mk]
  by_cases hk : k = 0
  · subst k
    norm_num
  have hk1 : 1 ≤ k := by omega
  have hcast : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by omega
  rw [hcast]
  simp only [if_pos hk1]
  have hpow : a ^ k = a * a ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow]
  ring

/-- The single-variable Chebyshev series appearing in the even folded
formula. -/
def foldEvenChebyshevTermSeries (a u zeta : ℝ) : PowerSeries ℝ :=
  C (u - zeta) * foldChebyshevPlusPrevSeries a u

/-- The degree-`m` numerator function in the even folded divided difference. -/
def foldEvenChebyshevFunction (m : ℕ) (u zeta : ℝ) : ℝ :=
  (u - zeta) *
    (chebyshevU m u + chebyshevU ((m : ℤ) - 1) u)

theorem coeff_foldEvenChebyshevTermSeries (a u zeta : ℝ) (m : ℕ) :
    coeff m (foldEvenChebyshevTermSeries a u zeta) =
      a ^ m * foldEvenChebyshevFunction m u zeta := by
  rw [foldEvenChebyshevTermSeries, coeff_C_mul,
    foldChebyshevPlusPrevSeries, coeff_mk]
  simp only [foldEvenChebyshevFunction]
  ring

theorem foldQuadraticSeries_mul_foldEvenChebyshevTermSeries
    (a u zeta : ℝ) :
    foldQuadraticSeries a u * foldEvenChebyshevTermSeries a u zeta =
      C (u - zeta) * (1 + C a * X ^ 1) := by
  rw [foldEvenChebyshevTermSeries, foldChebyshevPlusPrevSeries_eq]
  calc
    foldQuadraticSeries a u *
        (C (u - zeta) *
          ((1 + C a * X ^ 1) * foldChebyshevSeries a u)) =
      C (u - zeta) * (1 + C a * X ^ 1) *
        (foldQuadraticSeries a u * foldChebyshevSeries a u) := by ring
    _ = C (u - zeta) * (1 + C a * X ^ 1) := by
      rw [foldQuadraticSeries_mul_foldChebyshevSeries]
      ring

/-- The formal divided difference of the two even Chebyshev term series. -/
def foldEvenChebyshevDividedDifferenceSeries
    (a u v zeta : ℝ) : PowerSeries ℝ :=
  C ((u - v)⁻¹) *
    (foldEvenChebyshevTermSeries a u zeta -
      foldEvenChebyshevTermSeries a v zeta)

theorem coeff_foldEvenChebyshevDividedDifferenceSeries
    {a u v zeta : ℝ} (m : ℕ) :
    coeff m (foldEvenChebyshevDividedDifferenceSeries a u v zeta) =
      a ^ m *
        ((foldEvenChebyshevFunction m u zeta -
          foldEvenChebyshevFunction m v zeta) / (u - v)) := by
  rw [foldEvenChebyshevDividedDifferenceSeries, coeff_C_mul, map_sub,
    coeff_foldEvenChebyshevTermSeries,
    coeff_foldEvenChebyshevTermSeries]
  rw [div_eq_mul_inv]
  ring

theorem foldQuadraticProduct_mul_foldEvenChebyshevDividedDifferenceSeries
    {a u v s : ℝ} (huv : u ≠ v) :
    (foldQuadraticSeries a u * foldQuadraticSeries a v) *
        foldEvenChebyshevDividedDifferenceSeries a u v (foldZeta a s) =
      foldEvenResidualSeries a s := by
  have hpoly :
      foldQuadraticSeries a v *
          (C (u - foldZeta a s) * (1 + C a * X ^ 1)) -
          foldQuadraticSeries a u *
            (C (v - foldZeta a s) * (1 + C a * X ^ 1)) =
        C (u - v) * foldEvenResidualSeries a s := by
    rw [foldQuadraticSeries, foldQuadraticSeries, foldEvenResidualSeries]
    simp only [map_one, map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [foldEvenChebyshevDividedDifferenceSeries]
  calc
    (foldQuadraticSeries a u * foldQuadraticSeries a v) *
        (C ((u - v)⁻¹) *
          (foldEvenChebyshevTermSeries a u (foldZeta a s) -
            foldEvenChebyshevTermSeries a v (foldZeta a s))) =
      C ((u - v)⁻¹) *
        (foldQuadraticSeries a v *
            (foldQuadraticSeries a u *
              foldEvenChebyshevTermSeries a u (foldZeta a s)) -
          foldQuadraticSeries a u *
            (foldQuadraticSeries a v *
              foldEvenChebyshevTermSeries a v (foldZeta a s))) := by ring
    _ = C ((u - v)⁻¹) *
        (foldQuadraticSeries a v *
            (C (u - foldZeta a s) * (1 + C a * X ^ 1)) -
          foldQuadraticSeries a u *
            (C (v - foldZeta a s) * (1 + C a * X ^ 1))) := by
      rw [foldQuadraticSeries_mul_foldEvenChebyshevTermSeries,
        foldQuadraticSeries_mul_foldEvenChebyshevTermSeries]
    _ = C ((u - v)⁻¹) * (C (u - v) *
        foldEvenResidualSeries a s) := by rw [hpoly]
    _ = foldEvenResidualSeries a s := by
      rw [← mul_assoc, ← map_mul]
      simp [sub_ne_zero.mpr huv]

theorem foldEvenPowerSeries_eq_chebyshevDividedDifference
    {a x s u v : ℝ} (ha0 : a ≠ 0)
    (huv : u ≠ v)
    (hsum : 2 * a * (u + v) = foldC0 a x s)
    (hprod : a ^ 2 * (4 * u * v + 2) = foldB a x s) :
    foldEvenPowerSeries a x s =
      foldEvenChebyshevDividedDifferenceSeries a u v (foldZeta a s) := by
  have hconst :
      constantCoeff
          (foldQuadraticSeries a u * foldQuadraticSeries a v) ≠ 0 := by
    simp [foldQuadraticSeries]
  have hcand :
      foldEvenChebyshevDividedDifferenceSeries a u v (foldZeta a s) =
        foldEvenResidualSeries a s *
          (foldQuadraticSeries a u * foldQuadraticSeries a v)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq hconst).2
    simpa [mul_comm] using
      foldQuadraticProduct_mul_foldEvenChebyshevDividedDifferenceSeries
        (a := a) (u := u) (v := v) (s := s) huv
  calc
    foldEvenPowerSeries a x s =
        foldEvenResidualSeries a s * (foldRecurrenceSeries a x s)⁻¹ :=
      foldEvenPowerSeries_eq_mul_inv_recurrence ha0
    _ = foldEvenResidualSeries a s *
        (foldQuadraticSeries a u * foldQuadraticSeries a v)⁻¹ := by
      rw [foldRecurrenceSeries_eq_mul_foldQuadraticSeries hsum hprod]
    _ = foldEvenChebyshevDividedDifferenceSeries a u v (foldZeta a s) :=
      hcand.symm

theorem foldEvenSequence_eq_chebyshevDividedDifference
    {a x s u v : ℝ} (ha0 : a ≠ 0)
    (huv : u ≠ v)
    (hsum : 2 * a * (u + v) = foldC0 a x s)
    (hprod : a ^ 2 * (4 * u * v + 2) = foldB a x s)
    (m : ℕ) :
    foldEvenSequence a x s m =
      a ^ m *
        ((foldEvenChebyshevFunction m u (foldZeta a s) -
          foldEvenChebyshevFunction m v (foldZeta a s)) / (u - v)) := by
  have h := congrArg (coeff m)
    (foldEvenPowerSeries_eq_chebyshevDividedDifference
      ha0 huv hsum hprod)
  rw [foldEvenPowerSeries, coeff_mk,
    coeff_foldEvenChebyshevDividedDifferenceSeries] at h
  exact h

/-- The affine coefficient `β` in the odd folded Chebyshev formula. -/
def foldOddBeta (a x s : ℝ) : ℝ :=
  (x * (1 + a ^ 2) + 2 * a * s) / (2 * a)

/-- The degree-`m` numerator function in the odd folded divided difference. -/
def foldOddChebyshevFunction (m : ℕ) (x s beta u : ℝ) : ℝ :=
  ((x - s) * u - beta) * chebyshevU m u

/-- The single-variable Chebyshev series appearing in the odd folded
formula. -/
def foldOddChebyshevTermSeries
    (a x s beta u : ℝ) : PowerSeries ℝ :=
  C ((x - s) * u - beta) * foldChebyshevSeries a u

theorem coeff_foldOddChebyshevTermSeries
    (a x s beta u : ℝ) (m : ℕ) :
    coeff m (foldOddChebyshevTermSeries a x s beta u) =
      a ^ m * foldOddChebyshevFunction m x s beta u := by
  rw [foldOddChebyshevTermSeries, coeff_C_mul,
    foldChebyshevSeries, coeff_mk]
  simp only [foldOddChebyshevFunction]
  ring

theorem foldQuadraticSeries_mul_foldOddChebyshevTermSeries
    (a x s beta u : ℝ) :
    foldQuadraticSeries a u * foldOddChebyshevTermSeries a x s beta u =
      C ((x - s) * u - beta) := by
  rw [foldOddChebyshevTermSeries]
  calc
    foldQuadraticSeries a u *
        (C ((x - s) * u - beta) * foldChebyshevSeries a u) =
      C ((x - s) * u - beta) *
        (foldQuadraticSeries a u * foldChebyshevSeries a u) := by ring
    _ = C ((x - s) * u - beta) := by
      rw [foldQuadraticSeries_mul_foldChebyshevSeries]
      ring

/-- The formal divided difference of the two odd Chebyshev term series. -/
def foldOddChebyshevDividedDifferenceSeries
    (a x s beta u v : ℝ) : PowerSeries ℝ :=
  C ((u - v)⁻¹) *
    (foldOddChebyshevTermSeries a x s beta u -
      foldOddChebyshevTermSeries a x s beta v)

theorem coeff_foldOddChebyshevDividedDifferenceSeries
    {a x s beta u v : ℝ} (m : ℕ) :
    coeff m (foldOddChebyshevDividedDifferenceSeries a x s beta u v) =
      a ^ m *
        ((foldOddChebyshevFunction m x s beta u -
          foldOddChebyshevFunction m x s beta v) / (u - v)) := by
  rw [foldOddChebyshevDividedDifferenceSeries, coeff_C_mul, map_sub,
    coeff_foldOddChebyshevTermSeries,
    coeff_foldOddChebyshevTermSeries]
  rw [div_eq_mul_inv]
  ring

theorem foldQuadraticProduct_mul_foldOddChebyshevDividedDifferenceSeries
    {a x s u v : ℝ} (ha0 : a ≠ 0) (huv : u ≠ v) :
    (foldQuadraticSeries a u * foldQuadraticSeries a v) *
        foldOddChebyshevDividedDifferenceSeries a x s
          (foldOddBeta a x s) u v =
      foldOddResidualSeries a x s := by
  have hbeta :
      2 * a * foldOddBeta a x s = x * (1 + a ^ 2) + 2 * a * s := by
    rw [foldOddBeta]
    field_simp [ha0]
  have hpoly :
      foldQuadraticSeries a v *
          C ((x - s) * u - foldOddBeta a x s) -
          foldQuadraticSeries a u *
            C ((x - s) * v - foldOddBeta a x s) =
        C (u - v) * foldOddResidualSeries a x s := by
    rw [foldQuadraticSeries, foldQuadraticSeries, foldOddResidualSeries,
      ← hbeta]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    ring
  rw [foldOddChebyshevDividedDifferenceSeries]
  calc
    (foldQuadraticSeries a u * foldQuadraticSeries a v) *
        (C ((u - v)⁻¹) *
          (foldOddChebyshevTermSeries a x s (foldOddBeta a x s) u -
            foldOddChebyshevTermSeries a x s (foldOddBeta a x s) v)) =
      C ((u - v)⁻¹) *
        (foldQuadraticSeries a v *
            (foldQuadraticSeries a u *
              foldOddChebyshevTermSeries a x s (foldOddBeta a x s) u) -
          foldQuadraticSeries a u *
            (foldQuadraticSeries a v *
              foldOddChebyshevTermSeries a x s (foldOddBeta a x s) v)) := by ring
    _ = C ((u - v)⁻¹) *
        (foldQuadraticSeries a v *
            C ((x - s) * u - foldOddBeta a x s) -
          foldQuadraticSeries a u *
            C ((x - s) * v - foldOddBeta a x s)) := by
      rw [foldQuadraticSeries_mul_foldOddChebyshevTermSeries,
        foldQuadraticSeries_mul_foldOddChebyshevTermSeries]
    _ = C ((u - v)⁻¹) *
        (C (u - v) * foldOddResidualSeries a x s) := by rw [hpoly]
    _ = foldOddResidualSeries a x s := by
      rw [← mul_assoc, ← map_mul]
      simp [sub_ne_zero.mpr huv]

theorem foldOddPowerSeries_eq_chebyshevDividedDifference
    {a x s u v : ℝ} (ha0 : a ≠ 0)
    (huv : u ≠ v)
    (hsum : 2 * a * (u + v) = foldC0 a x s)
    (hprod : a ^ 2 * (4 * u * v + 2) = foldB a x s) :
    foldOddPowerSeries a x s =
      foldOddChebyshevDividedDifferenceSeries a x s
        (foldOddBeta a x s) u v := by
  have hconst :
      constantCoeff
          (foldQuadraticSeries a u * foldQuadraticSeries a v) ≠ 0 := by
    simp [foldQuadraticSeries]
  have hcand :
      foldOddChebyshevDividedDifferenceSeries a x s
          (foldOddBeta a x s) u v =
        foldOddResidualSeries a x s *
          (foldQuadraticSeries a u * foldQuadraticSeries a v)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq hconst).2
    simpa [mul_comm] using
      foldQuadraticProduct_mul_foldOddChebyshevDividedDifferenceSeries
        (a := a) (x := x) (s := s) (u := u) (v := v) ha0 huv
  calc
    foldOddPowerSeries a x s =
        foldOddResidualSeries a x s * (foldRecurrenceSeries a x s)⁻¹ :=
      foldOddPowerSeries_eq_mul_inv_recurrence
    _ = foldOddResidualSeries a x s *
        (foldQuadraticSeries a u * foldQuadraticSeries a v)⁻¹ := by
      rw [foldRecurrenceSeries_eq_mul_foldQuadraticSeries hsum hprod]
    _ = foldOddChebyshevDividedDifferenceSeries a x s
        (foldOddBeta a x s) u v := hcand.symm

theorem foldOddSequence_eq_chebyshevDividedDifference
    {a x s u v : ℝ} (ha0 : a ≠ 0)
    (huv : u ≠ v)
    (hsum : 2 * a * (u + v) = foldC0 a x s)
    (hprod : a ^ 2 * (4 * u * v + 2) = foldB a x s)
    (m : ℕ) :
    foldOddSequence a x s m =
      a ^ m *
        ((foldOddChebyshevFunction m x s (foldOddBeta a x s) u -
          foldOddChebyshevFunction m x s (foldOddBeta a x s) v) /
            (u - v)) := by
  have h := congrArg (coeff m)
    (foldOddPowerSeries_eq_chebyshevDividedDifference
      ha0 huv hsum hprod)
  rw [foldOddPowerSeries, coeff_mk,
    coeff_foldOddChebyshevDividedDifferenceSeries] at h
  exact h

end


end ConnectedPseudospectrum
