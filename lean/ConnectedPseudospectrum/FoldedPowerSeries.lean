import ConnectedPseudospectrum.FoldedGenerating
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Formal folded generating functions

The five minor recurrences give a linear system of formal series.  Eliminating
the four auxiliary series yields the even and odd determinant generating
functions; the scalar recurrence is then a coefficient identity.
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

/-- Generating series of one coordinate of the signed five-minor orbit. -/
def foldCoordinateSeries (a x s : ℝ) (v : FoldMinorState)
    (f : FoldMinorState → ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun m ↦ f (foldSignedOrbit a x s v m))

/-- Summing the five first-order minor recurrences. -/
theorem foldCoordinateSeries_system (a x s : ℝ) (v : FoldMinorState) :
    let D := foldCoordinateSeries a x s v FoldMinorState.d
    let P := foldCoordinateSeries a x s v FoldMinorState.p
    let Q := foldCoordinateSeries a x s v FoldMinorState.q
    let U := foldCoordinateSeries a x s v FoldMinorState.c
    let R := foldCoordinateSeries a x s v FoldMinorState.r
    D = C v.d + X * (C (x ^ 2 - s ^ 2) * D -
        C s * (C (a ^ 2) * P + Q) + C (2 * a * x) * U - C (a ^ 2) * R) ∧
    P = C v.p + X * (C s * D + C (a ^ 2) * P) ∧
    Q = C v.q + X * (C s * D + Q) ∧
    U = C v.c + X * (-C x * D - C a * U) ∧
    R = C v.r - X * D := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    ext m
    cases m with
    | zero => simp [foldCoordinateSeries, foldSignedOrbit]
    | succ m =>
        simp only [foldCoordinateSeries, map_add, map_sub, sub_mul, neg_mul, map_neg,
          coeff_succ_X_mul, coeff_C, Nat.succ_ne_zero, if_false, zero_add,
          coeff_C_mul, coeff_mk, foldSignedOrbit, foldSignedStep,
          foldMinorScale, foldMinorStep]
        ring

/-- Elimination of the auxiliary minor series. -/
theorem foldCoordinateSeries_elimination (a x s : ℝ) (v : FoldMinorState) :
    (1 - C a * X) * foldRecurrenceSeries a x s *
        foldCoordinateSeries a x s v FoldMinorState.d =
      (C v.d - C (a ^ 2) * X * C v.r) *
          (1 - C (a ^ 2) * X) * (1 - X) * (1 + C a * X) -
        C s * X * (C (a ^ 2) * C v.p * (1 - X) * (1 + C a * X) +
          C v.q * (1 - C (a ^ 2) * X) * (1 + C a * X)) +
        C (2 * a * x) * X * C v.c * (1 - C (a ^ 2) * X) * (1 - X) := by
  obtain ⟨hd, hp, hq, hc, hr⟩ := foldCoordinateSeries_system a x s v
  rw [hr] at hd
  simp only [foldRecurrenceSeries, foldC0, foldB, map_add, map_sub,
    map_mul, map_pow, map_ofNat, map_one] at hd hp hq hc ⊢
  linear_combination
    (1 - C a ^ 2 * X) * (1 - X) * (1 + C a * X) * hd -
    C s * X * C a ^ 2 * (1 - X) * (1 + C a * X) * hp -
    C s * X * (1 - C a ^ 2 * X) * (1 + C a * X) * hq +
    2 * C a * C x * X * (1 - C a ^ 2 * X) * (1 - X) * hc

private theorem one_sub_C_mul_X_ne_zero (a : ℝ) :
    (1 - C a * X : PowerSeries ℝ) ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  simp at this

/-- Direct even generating identity, with a polynomial numerator at every `a`. -/
theorem foldRecurrenceSeries_mul_foldEvenPowerSeries_polynomial
    (a x s : ℝ) :
    foldRecurrenceSeries a x s * foldEvenPowerSeries a x s =
      (1 + C a * X) *
        (1 - C (1 + a ^ 2 + (1 + a) * s) * X + C (a ^ 2) * X ^ 2) := by
  apply mul_left_cancel₀ (one_sub_C_mul_X_ne_zero a)
  have h := foldCoordinateSeries_elimination a x s (foldEvenSeed a)
  change (1 - C a * X) * (foldRecurrenceSeries a x s *
    foldEvenPowerSeries a x s) = _
  rw [← mul_assoc]
  change (1 - C a * X) * foldRecurrenceSeries a x s *
    foldCoordinateSeries a x s (foldEvenSeed a) FoldMinorState.d = _
  rw [h]
  simp only [foldEvenSeed, map_add, map_mul, map_pow, map_one, map_zero]
  by_cases ha : a = 0
  · subst a
    simp
    ring
  · have hi : C a * C a⁻¹ = (1 : PowerSeries ℝ) := by
      rw [← map_mul, mul_inv_cancel₀ ha, map_one]
    linear_combination
      -(C a * X * (1 - X) * (1 + C a * X) *
        (1 - C a ^ 2 * X + C s)) * hi

/-- Cross-multiplied even generating-function identity. -/
theorem foldRecurrenceSeries_mul_foldEvenPowerSeries
    {a x s : ℝ} (ha0 : a ≠ 0) :
    foldRecurrenceSeries a x s * foldEvenPowerSeries a x s =
      foldEvenResidualSeries a s := by
  rw [foldRecurrenceSeries_mul_foldEvenPowerSeries_polynomial]
  have hz : 2 * a * foldZeta a s = 1 + a ^ 2 + (1 + a) * s := by
    unfold foldZeta
    field_simp
  rw [← hz, foldEvenResidualSeries]
  simp only [map_sub, map_mul, map_pow, map_one, map_ofNat]
  ring

/-- Cross-multiplied odd generating-function identity. -/
theorem foldRecurrenceSeries_mul_foldOddPowerSeries
    {a x s : ℝ} :
    foldRecurrenceSeries a x s * foldOddPowerSeries a x s =
      foldOddResidualSeries a x s := by
  apply mul_left_cancel₀ (one_sub_C_mul_X_ne_zero a)
  have h := foldCoordinateSeries_elimination a x s (foldOddSeed x s)
  change (1 - C a * X) * (foldRecurrenceSeries a x s *
    foldOddPowerSeries a x s) = _
  rw [← mul_assoc]
  change (1 - C a * X) * foldRecurrenceSeries a x s *
    foldCoordinateSeries a x s (foldOddSeed x s) FoldMinorState.d = _
  rw [h]
  simp only [foldOddSeed, foldOddResidualSeries, map_add, map_sub,
    map_mul, map_pow, map_neg, map_one, map_zero, map_ofNat]
  ring

/-- The scalar coefficient identity of the even generating function. -/
private theorem foldEvenSequence_coefficient (a x s : ℝ) (k : ℕ) :
    foldEvenSequence a x s k -
        foldC0 a x s * (if 1 ≤ k then foldEvenSequence a x s (k - 1) else 0) +
        foldB a x s * (if 2 ≤ k then foldEvenSequence a x s (k - 2) else 0) -
        a ^ 2 * foldC0 a x s *
          (if 3 ≤ k then foldEvenSequence a x s (k - 3) else 0) +
        a ^ 4 * (if 4 ≤ k then foldEvenSequence a x s (k - 4) else 0) =
      (if k = 0 then 1 else 0) +
        (if k = 1 then a - (1 + a ^ 2 + (1 + a) * s) else 0) +
        (if k = 2 then a ^ 2 - a * (1 + a ^ 2 + (1 + a) * s) else 0) +
        (if k = 3 then a ^ 3 else 0) := by
  have h := foldRecurrenceSeries_mul_foldEvenPowerSeries_polynomial a x s
  have he : (1 + C a * X) *
      (1 - C (1 + a ^ 2 + (1 + a) * s) * X + C (a ^ 2) * X ^ 2) =
        C 1 * X ^ 0 + C (a - (1 + a ^ 2 + (1 + a) * s)) * X ^ 1 +
        C (a ^ 2 - a * (1 + a ^ 2 + (1 + a) * s)) * X ^ 2 +
        C (a ^ 3) * X ^ 3 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_one]
    ring
  rw [he] at h
  have hc := congrArg (coeff k) h
  simpa only [foldEvenPowerSeries, coeff_foldRecurrenceSeries_mul_mk,
    map_add, coeff_C_mul_X_pow] using hc

/-- The scalar coefficient identity of the odd generating function. -/
private theorem foldOddSequence_coefficient {a x s : ℝ} (k : ℕ) :
    foldOddSequence a x s k -
        foldC0 a x s * (if 1 ≤ k then foldOddSequence a x s (k - 1) else 0) +
        foldB a x s * (if 2 ≤ k then foldOddSequence a x s (k - 2) else 0) -
        a ^ 2 * foldC0 a x s *
          (if 3 ≤ k then foldOddSequence a x s (k - 3) else 0) +
        a ^ 4 * (if 4 ≤ k then foldOddSequence a x s (k - 4) else 0) =
      (if k = 0 then x - s else 0) -
        (if k = 1 then x * (1 + a ^ 2) + 2 * a * s else 0) +
        (if k = 2 then a ^ 2 * (x - s) else 0) := by
  have h := congrArg (coeff k)
    (foldRecurrenceSeries_mul_foldOddPowerSeries (a := a) (x := x) (s := s))
  simpa only [foldOddPowerSeries, coeff_foldRecurrenceSeries_mul_mk,
    coeff_foldOddResidualSeries] using h

/-- The even scalar recurrence is a coefficient of its generating identity. -/
theorem foldEvenSequence_recurrence
    {a x s : ℝ} (m : ℕ) :
    foldEvenSequence a x s (m + 4) -
        foldC0 a x s * foldEvenSequence a x s (m + 3) +
        foldB a x s * foldEvenSequence a x s (m + 2) -
        a ^ 2 * foldC0 a x s * foldEvenSequence a x s (m + 1) +
        a ^ 4 * foldEvenSequence a x s m = 0 := by
  simpa using foldEvenSequence_coefficient a x s (m + 4)

/-- The odd scalar recurrence is a coefficient of its generating identity. -/
theorem foldOddSequence_recurrence
    {a x s : ℝ} (m : ℕ) :
    foldOddSequence a x s (m + 4) -
        foldC0 a x s * foldOddSequence a x s (m + 3) +
        foldB a x s * foldOddSequence a x s (m + 2) -
        a ^ 2 * foldC0 a x s * foldOddSequence a x s (m + 1) +
        a ^ 4 * foldOddSequence a x s m = 0 := by
  simpa using foldOddSequence_coefficient (a := a) (x := x) (s := s) (m + 4)

/-- The degree-one even boundary coefficient. -/
theorem foldEvenSequence_residual_one
    {a x s : ℝ} (ha0 : a ≠ 0) :
    foldEvenSequence a x s 1 - foldC0 a x s * foldEvenSequence a x s 0 =
      a * (1 - 2 * foldZeta a s) := by
  have h := foldEvenSequence_coefficient a x s 1
  norm_num at h ⊢
  rw [h]
  unfold foldZeta
  field_simp

/-- The degree-two even boundary coefficient. -/
theorem foldEvenSequence_residual_two
    {a x s : ℝ} (ha0 : a ≠ 0) :
    foldEvenSequence a x s 2 - foldC0 a x s * foldEvenSequence a x s 1 +
      foldB a x s * foldEvenSequence a x s 0 =
      a ^ 2 * (1 - 2 * foldZeta a s) := by
  have h := foldEvenSequence_coefficient a x s 2
  norm_num at h ⊢
  rw [h]
  unfold foldZeta
  field_simp

/-- The degree-three even boundary coefficient. -/
theorem foldEvenSequence_residual_three
    {a x s : ℝ} :
    foldEvenSequence a x s 3 - foldC0 a x s * foldEvenSequence a x s 2 +
      foldB a x s * foldEvenSequence a x s 1 -
      a ^ 2 * foldC0 a x s * foldEvenSequence a x s 0 = a ^ 3 := by
  simpa using foldEvenSequence_coefficient a x s 3

/-- The degree-one odd boundary coefficient. -/
theorem foldOddSequence_residual_one
    {a x s : ℝ} :
    foldOddSequence a x s 1 - foldC0 a x s * foldOddSequence a x s 0 =
      -(x * (1 + a ^ 2) + 2 * a * s) := by
  simpa using foldOddSequence_coefficient (a := a) (x := x) (s := s) 1

/-- The degree-two odd boundary coefficient. -/
theorem foldOddSequence_residual_two
    {a x s : ℝ} :
    foldOddSequence a x s 2 - foldC0 a x s * foldOddSequence a x s 1 +
      foldB a x s * foldOddSequence a x s 0 = a ^ 2 * (x - s) := by
  simpa using foldOddSequence_coefficient (a := a) (x := x) (s := s) 2

/-- The degree-three odd boundary coefficient. -/
theorem foldOddSequence_residual_three
    {a x s : ℝ} :
    foldOddSequence a x s 3 - foldC0 a x s * foldOddSequence a x s 2 +
      foldB a x s * foldOddSequence a x s 1 -
      a ^ 2 * foldC0 a x s * foldOddSequence a x s 0 = 0 := by
  simpa using foldOddSequence_coefficient (a := a) (x := x) (s := s) 3

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
    {a x s : ℝ} (ha0 : a ≠ 0) :
    foldEvenPowerSeries a x s =
      foldEvenResidualSeries a s * (foldRecurrenceSeries a x s)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq (by
    simp [foldRecurrenceSeries] :
      constantCoeff (foldRecurrenceSeries a x s) ≠ 0)).2
  simpa [mul_comm] using foldRecurrenceSeries_mul_foldEvenPowerSeries ha0

/-- Formal quotient form of the odd folded generating function. -/
theorem foldOddPowerSeries_eq_mul_inv_recurrence
    {a x s : ℝ} :
    foldOddPowerSeries a x s =
      foldOddResidualSeries a x s * (foldRecurrenceSeries a x s)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq (by
    simp [foldRecurrenceSeries] :
      constantCoeff (foldRecurrenceSeries a x s) ≠ 0)).2
  simpa [mul_comm] using
    foldRecurrenceSeries_mul_foldOddPowerSeries (a := a) (x := x) (s := s)

end


end ConnectedPseudospectrum
