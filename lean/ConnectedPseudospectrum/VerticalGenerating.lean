import ConnectedPseudospectrum.VerticalPrincipalMinors
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Generating functions for the vertical continuants

This module formalizes equations `eq:T-generating`, `eq:D-F-generating`,
`eq:F-prime-generating`, and `eq:F-prime-convolution` from the source.
All generating functions are formal power series, so no analytic convergence
hypothesis is involved.
-/

namespace ConnectedPseudospectrum

open Filter PowerSeries

noncomputable section

/-- The formal generating series `\sum T_k z^k`. -/
def verticalToeplitzSeries (a x Y t : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => verticalToeplitzDet k a x Y t

/-- The formal generating series `\mathcal D = \sum D_k z^k`. -/
def verticalLeadingSeries (a x Y t : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => verticalLeadingMinor k a x Y t

/-- The formal generating series `\sum R_k z^k`. -/
def verticalTrailingSeries (a x Y t : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => verticalTrailingMinor k a x Y t

/-- The formal generating series of the full vertical-pencil determinants. -/
def verticalPencilSeries (a x Y t : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => verticalPencilDet k a x Y t

/-- The denominator `Q(z,Y)` in `eq:T-generating`. -/
def verticalContinuantQ (a x Y t : ℝ) : PowerSeries ℂ :=
  1 -
    C (verticalToeplitzDiagonal a x Y t : ℂ) * X ^ 1 +
    C ((Complex.normSq (verticalToeplitzFirst a x Y) : ℂ) - (a : ℂ) ^ 2) * X ^ 2 +
    C (2 * (a : ℂ) ^ 2 * (verticalToeplitzDiagonal a x Y t : ℂ) -
        (a : ℂ) *
          ((verticalToeplitzFirst a x Y) ^ 2 +
            (star (verticalToeplitzFirst a x Y)) ^ 2)) * X ^ 3 +
    C ((a : ℂ) ^ 2 *
        ((Complex.normSq (verticalToeplitzFirst a x Y) : ℂ) - (a : ℂ) ^ 2)) * X ^ 4 -
    C ((a : ℂ) ^ 4 * (verticalToeplitzDiagonal a x Y t : ℂ)) * X ^ 5 +
    C ((a : ℂ) ^ 6) * X ^ 6

/-- Coefficients of a monomial times a series are the paper's shifted
sequence with negative indices set to zero. -/
theorem coeff_C_mul_X_pow_mul_mk (c : ℂ) (j k : ℕ) (u : ℕ → ℂ) :
    coeff k (C c * X ^ j * PowerSeries.mk u) = c * lagWithZero u k j := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  simp [lagWithZero]

theorem coeff_succ_C_mul_X_mul_mk (c : ℂ) (k : ℕ) (u : ℕ → ℂ) :
    coeff (k + 1) (C c * (X * PowerSeries.mk u)) = c * u k := by
  rw [coeff_C_mul, coeff_succ_X_mul, coeff_mk]

/-- Coefficient form of `Q \sum T_k z^k = 1-a²z²`. -/
theorem coeff_verticalContinuantQ_mul_verticalToeplitzSeries
    (k : ℕ) (a x Y t : ℝ) :
    coeff k (verticalContinuantQ a x Y t * verticalToeplitzSeries a x Y t) =
      if k = 0 then 1 else if k = 2 then -(a : ℂ) ^ 2 else 0 := by
  cases k with
  | zero =>
      simp [verticalContinuantQ, verticalToeplitzSeries]
  | succ k =>
      have hrec := verticalToeplitzDet_recurrence (k + 1) a x Y t (by omega)
      rw [verticalContinuantQ, verticalToeplitzSeries]
      simp only [sub_mul, add_mul, one_mul, map_add, map_sub, coeff_mk,
        coeff_C_mul_X_pow_mul_mk]
      simp only [Nat.succ_ne_zero, if_false]
      rw [hrec]
      by_cases hk₂ : k + 1 = 2 <;> simp [hk₂] <;> ring

/-- Cross-multiplied form of `eq:T-generating`. -/
theorem verticalContinuantQ_mul_verticalToeplitzSeries (a x Y t : ℝ) :
    verticalContinuantQ a x Y t * verticalToeplitzSeries a x Y t =
      1 - C ((a : ℂ) ^ 2) * X ^ 2 := by
  ext k
  rw [coeff_verticalContinuantQ_mul_verticalToeplitzSeries]
  rw [map_sub, coeff_one, coeff_C_mul_X_pow]
  by_cases hk₀ : k = 0 <;> by_cases hk₂ : k = 2 <;>
    simp [hk₀, hk₂]

/-- Formal-quotient form of `eq:T-generating`. -/
theorem verticalToeplitzSeries_eq_mul_inv_Q (a x Y t : ℝ) :
    verticalToeplitzSeries a x Y t =
      (1 - C ((a : ℂ) ^ 2) * X ^ 2) * (verticalContinuantQ a x Y t)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq (by
    simp [verticalContinuantQ] :
      constantCoeff (verticalContinuantQ a x Y t) ≠ 0)).2
  simpa [mul_comm] using verticalContinuantQ_mul_verticalToeplitzSeries a x Y t

/-- The coefficient identity `D_k=T_k-T_{k-1}` becomes multiplication by
`1-X`. -/
theorem verticalLeadingSeries_eq (a x Y t : ℝ) :
    verticalLeadingSeries a x Y t =
      (1 - X) * verticalToeplitzSeries a x Y t := by
  ext k
  cases k with
  | zero =>
      simp [verticalLeadingSeries, verticalToeplitzSeries,
        verticalLeadingMinor, lagWithZero]
  | succ k =>
      simp [verticalLeadingSeries, verticalToeplitzSeries,
        verticalLeadingMinor, lagWithZero, sub_mul]

/-- The coefficient identity `R_k=T_k-a²T_{k-1}` as a formal generating
series identity. -/
theorem verticalTrailingSeries_eq (a x Y t : ℝ) :
    verticalTrailingSeries a x Y t =
      (1 - C ((a : ℂ) ^ 2) * X) * verticalToeplitzSeries a x Y t := by
  ext k
  cases k with
  | zero =>
      simp [verticalTrailingSeries, verticalToeplitzSeries,
        verticalTrailingMinor, lagWithZero]
  | succ k =>
      simp [verticalTrailingSeries, verticalToeplitzSeries,
        verticalTrailingMinor, lagWithZero, sub_mul, mul_assoc]
      simpa only [← map_pow] using
        (coeff_succ_C_mul_X_mul_mk ((a : ℂ) ^ 2) k
          (fun n => verticalToeplitzDet n a x Y t)).symm

/-- First identity in `eq:D-F-generating`, in cross-multiplied form. -/
theorem verticalContinuantQ_mul_verticalLeadingSeries (a x Y t : ℝ) :
    verticalContinuantQ a x Y t * verticalLeadingSeries a x Y t =
      (1 - X) * (1 - C ((a : ℂ) ^ 2) * X ^ 2) := by
  rw [verticalLeadingSeries_eq]
  calc
    verticalContinuantQ a x Y t *
          ((1 - X) * verticalToeplitzSeries a x Y t) =
        (1 - X) *
          (verticalContinuantQ a x Y t * verticalToeplitzSeries a x Y t) := by
            ring
    _ = (1 - X) * (1 - C ((a : ℂ) ^ 2) * X ^ 2) := by
      rw [verticalContinuantQ_mul_verticalToeplitzSeries]

/-- Second identity in `eq:D-F-generating`. -/
theorem verticalPencilSeries_eq (a x Y t : ℝ) (hY : 0 ≤ Y) :
    verticalPencilSeries a x Y t =
      (1 - C ((a : ℂ) ^ 2) * X) * verticalLeadingSeries a x Y t := by
  ext k
  cases k with
  | zero =>
      simp [verticalPencilSeries, verticalLeadingSeries,
        verticalPencilDet_eq_leadingMinor_sub, hY, lagWithZero]
  | succ k =>
      simp [verticalPencilSeries, verticalLeadingSeries,
        verticalPencilDet_eq_leadingMinor_sub, hY, lagWithZero,
        sub_mul, mul_assoc]
      simpa only [← map_pow] using
        (coeff_succ_C_mul_X_mul_mk ((a : ℂ) ^ 2) k
          (fun n => verticalLeadingMinor n a x Y t)).symm

/-! ## The `Y` derivative of the denominator -/

/-- The squared modulus of the first off-diagonal coefficient, after the
substitution `Y = y²`. -/
theorem normSq_verticalToeplitzFirst (a x Y : ℝ) (hY : 0 ≤ Y) :
    Complex.normSq (verticalToeplitzFirst a x Y) =
      (1 + a) ^ 2 * x ^ 2 + (1 - a) ^ 2 * Y := by
  rw [Complex.normSq_apply]
  simp [verticalToeplitzFirst]
  nlinarith [Real.sq_sqrt hY]

/-- The sum `b² + conj(b)²`, after the substitution `Y = y²`. -/
theorem verticalToeplitzFirst_sq_add_star_sq (a x Y : ℝ) (hY : 0 ≤ Y) :
    verticalToeplitzFirst a x Y ^ 2 +
        star (verticalToeplitzFirst a x Y) ^ 2 =
      ((2 * (1 + a) ^ 2 * x ^ 2 - 2 * (1 - a) ^ 2 * Y : ℝ) : ℂ) := by
  rw [star_verticalToeplitzFirst_eq]
  simp only [verticalToeplitzFirst]
  push_cast
  have hsqrt : (Real.sqrt Y : ℂ) ^ 2 = (Y : ℂ) := by
    norm_cast
    exact Real.sq_sqrt hY
  ring_nf
  simp only [Complex.I_sq]
  simp_rw [hsqrt]
  ring

/-- The factored formal power series appearing as `∂_Y Q` in the source. -/
def verticalContinuantQYDerivative (a : ℝ) : PowerSeries ℂ :=
  -X * (1 - X) * (1 + C (a : ℂ) * X) ^ 2 *
    (1 - C ((a : ℂ) ^ 2) * X)

/-- Exact affine-in-`Y` identity underlying the displayed formula
`∂_Y Q = -z(1-z)(1+az)²(1-a²z)`.  This difference form is valid at the
boundary `Y = 0` as well, provided both parameters represent squares. -/
theorem verticalContinuantQ_add_sub (a x Y s t : ℝ) (hY : 0 ≤ Y)
    (hYs : 0 ≤ Y + s) :
    verticalContinuantQ a x (Y + s) t - verticalContinuantQ a x Y t =
      C (s : ℂ) * verticalContinuantQYDerivative a := by
  rw [verticalContinuantQ, verticalContinuantQ]
  rw [normSq_verticalToeplitzFirst a x (Y + s) hYs,
    normSq_verticalToeplitzFirst a x Y hY]
  rw [verticalToeplitzFirst_sq_add_star_sq a x (Y + s) hYs,
    verticalToeplitzFirst_sq_add_star_sq a x Y hY]
  simp only [verticalToeplitzDiagonal, verticalContinuantQYDerivative]
  push_cast
  simp only [map_add, map_sub, map_mul, map_pow, map_one,
    map_ofNat]
  ring

/-! ## The differentiated generating function -/

/-- The rational factor `φ_a(z)` from `eq:F-prime-generating`. -/
def verticalPhi (a : ℝ) : PowerSeries ℂ :=
  X * (1 + C (a : ℂ) * X) * (1 - C ((a : ℂ) ^ 2) * X) ^ 2 *
    (1 - C (a : ℂ) * X)⁻¹

/-- The cancellation identity that turns differentiation of the quotient
for `ℐ` into the factor `φ_a`. -/
theorem verticalPhi_mul_continuantNumerator (a : ℝ) :
    verticalPhi a * ((1 - X) * (1 - C ((a : ℂ) ^ 2) * X ^ 2)) =
      -(1 - C ((a : ℂ) ^ 2) * X) * verticalContinuantQYDerivative a := by
  have hfactor :
      1 - C ((a : ℂ) ^ 2) * X ^ 2 =
        (1 - C (a : ℂ) * X) * (1 + C (a : ℂ) * X) := by
    simp only [map_pow]
    ring
  have hcancel :
      (1 - C (a : ℂ) * X)⁻¹ * (1 - C (a : ℂ) * X) = 1 :=
    PowerSeries.inv_mul_cancel _ (by simp)
  rw [verticalPhi, verticalContinuantQYDerivative, hfactor]
  calc
    X * (1 + C (a : ℂ) * X) * (1 - C ((a : ℂ) ^ 2) * X) ^ 2 *
          (1 - C (a : ℂ) * X)⁻¹ *
          ((1 - X) *
            ((1 - C (a : ℂ) * X) * (1 + C (a : ℂ) * X))) =
        ((1 - C (a : ℂ) * X)⁻¹ *
            (1 - C (a : ℂ) * X)) *
          (X * (1 + C (a : ℂ) * X) *
            (1 - C ((a : ℂ) ^ 2) * X) ^ 2 *
            (1 - X) * (1 + C (a : ℂ) * X)) := by
      ring
    _ = X * (1 + C (a : ℂ) * X) *
          (1 - C ((a : ℂ) ^ 2) * X) ^ 2 *
          (1 - X) * (1 + C (a : ℂ) * X) := by
      rw [hcancel, one_mul]
    _ = -(1 - C ((a : ℂ) ^ 2) * X) *
          (-X * (1 - X) * (1 + C (a : ℂ) * X) ^ 2 *
            (1 - C ((a : ℂ) ^ 2) * X)) := by
      ring

/-- Exact secant form of `eq:F-prime-generating`.  Dividing by `s` and
letting `s → 0` gives `∂_Y F = φ_a ℐ²`; unlike a merely formal
differentiation, this identity is already valid at the boundary `Y = 0`. -/
theorem verticalPencilSeries_add_sub (a x Y s t : ℝ) (hY : 0 ≤ Y)
    (hYs : 0 ≤ Y + s) :
    verticalPencilSeries a x (Y + s) t - verticalPencilSeries a x Y t =
      C (s : ℂ) * verticalPhi a * verticalLeadingSeries a x Y t *
        verticalLeadingSeries a x (Y + s) t := by
  rw [verticalPencilSeries_eq a x (Y + s) t hYs,
    verticalPencilSeries_eq a x Y t hY]
  have hQne : verticalContinuantQ a x Y t ≠ 0 := by
    intro hQ
    have := congrArg constantCoeff hQ
    simp [verticalContinuantQ] at this
  apply mul_left_cancel₀ hQne
  have hQY := verticalContinuantQ_add_sub a x Y s t hY hYs
  have hQbase := verticalContinuantQ_mul_verticalLeadingSeries a x Y t
  have hQnext := verticalContinuantQ_mul_verticalLeadingSeries a x (Y + s) t
  have hQsolve :
      verticalContinuantQ a x Y t =
        verticalContinuantQ a x (Y + s) t -
          C (s : ℂ) * verticalContinuantQYDerivative a := by
    calc
      verticalContinuantQ a x Y t =
          verticalContinuantQ a x (Y + s) t -
            (verticalContinuantQ a x (Y + s) t -
              verticalContinuantQ a x Y t) := by ring
      _ = verticalContinuantQ a x (Y + s) t -
            C (s : ℂ) * verticalContinuantQYDerivative a := by rw [hQY]
  calc
    verticalContinuantQ a x Y t *
          ((1 - C ((a : ℂ) ^ 2) * X) *
              verticalLeadingSeries a x (Y + s) t -
            (1 - C ((a : ℂ) ^ 2) * X) *
              verticalLeadingSeries a x Y t) =
        (1 - C ((a : ℂ) ^ 2) * X) *
          ((verticalContinuantQ a x (Y + s) t -
                C (s : ℂ) * verticalContinuantQYDerivative a) *
              verticalLeadingSeries a x (Y + s) t -
            verticalContinuantQ a x Y t *
              verticalLeadingSeries a x Y t) := by
      rw [hQsolve]
      ring
    _ = (1 - C ((a : ℂ) ^ 2) * X) *
          (verticalContinuantQ a x (Y + s) t *
              verticalLeadingSeries a x (Y + s) t -
            verticalContinuantQ a x Y t *
              verticalLeadingSeries a x Y t -
            C (s : ℂ) * verticalContinuantQYDerivative a *
              verticalLeadingSeries a x (Y + s) t) := by ring
    _ = -(C (s : ℂ) * (1 - C ((a : ℂ) ^ 2) * X) *
          verticalContinuantQYDerivative a *
          verticalLeadingSeries a x (Y + s) t) := by
      rw [hQnext, hQbase]
      ring
    _ = C (s : ℂ) *
          (verticalPhi a *
            ((1 - X) * (1 - C ((a : ℂ) ^ 2) * X ^ 2))) *
          verticalLeadingSeries a x (Y + s) t := by
      rw [verticalPhi_mul_continuantNumerator]
      ring
    _ = verticalContinuantQ a x Y t *
          (C (s : ℂ) * verticalPhi a *
            verticalLeadingSeries a x Y t *
            verticalLeadingSeries a x (Y + s) t) := by
      rw [← hQbase]
      ring

/-! ## Coefficients and the convolution formula -/

/-- The coefficients of `φ_a`, including the geometric tail beginning at
degree four. -/
def verticalPhiCoefficient (a : ℝ) : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | 2 => 2 * (a : ℂ) * (1 - (a : ℂ))
  | 3 => (a : ℂ) ^ 2 * ((a : ℂ) ^ 2 - 4 * (a : ℂ) + 2)
  | k + 4 => 2 * (a : ℂ) ^ (k + 3) * (1 - (a : ℂ)) ^ 2

/-- Expanded numerator of `φ_a`. -/
theorem verticalPhiNumerator_expansion (a : ℝ) :
    X * (1 + C (a : ℂ) * X) * (1 - C ((a : ℂ) ^ 2) * X) ^ 2 =
      X + C ((a : ℂ) - 2 * (a : ℂ) ^ 2) * X ^ 2 +
        C ((a : ℂ) ^ 4 - 2 * (a : ℂ) ^ 3) * X ^ 3 +
        C ((a : ℂ) ^ 5) * X ^ 4 := by
  simp only [map_pow, map_sub, map_mul, map_ofNat]
  ring

/-- The explicit coefficient sequence solves multiplication by `1-az`. -/
theorem one_sub_mul_verticalPhiCoefficientSeries (a : ℝ) :
    (1 - C (a : ℂ) * X) * PowerSeries.mk (verticalPhiCoefficient a) =
      X * (1 + C (a : ℂ) * X) *
        (1 - C ((a : ℂ) ^ 2) * X) ^ 2 := by
  rw [verticalPhiNumerator_expansion]
  ext k
  cases k with
  | zero => simp [verticalPhiCoefficient]
  | succ k =>
      simp only [sub_mul, one_mul, map_sub, coeff_mk, mul_assoc,
        coeff_succ_C_mul_X_mul_mk, map_add, coeff_X,
        coeff_C_mul_X_pow]
      cases k with
      | zero => simp [verticalPhiCoefficient]
      | succ k =>
          cases k with
          | zero => simp [verticalPhiCoefficient]; ring
          | succ k =>
              cases k with
              | zero => simp [verticalPhiCoefficient]; ring
              | succ k =>
                  cases k with
                  | zero => simp [verticalPhiCoefficient]; ring
                  | succ k =>
                      simp [verticalPhiCoefficient, pow_succ]
                      ring

/-- The rational definition of `φ_a` has the claimed explicit
coefficients. -/
theorem verticalPhi_eq_mk (a : ℝ) :
    verticalPhi a = PowerSeries.mk (verticalPhiCoefficient a) := by
  rw [verticalPhi]
  symm
  apply (eq_mul_inv_iff_mul_eq (by simp :
    constantCoeff (1 - C (a : ℂ) * X) ≠ 0)).2
  simpa [mul_comm] using one_sub_mul_verticalPhiCoefficientSeries a

@[simp] theorem coeff_verticalPhi (a : ℝ) (k : ℕ) :
    coeff k (verticalPhi a) = verticalPhiCoefficient a k := by
  rw [verticalPhi_eq_mk, coeff_mk]

/-- Closed form of every coefficient in the geometric tail of `φ_a`. -/
theorem verticalPhiCoefficient_of_four_le (a : ℝ) {k : ℕ} (hk : 4 ≤ k) :
    verticalPhiCoefficient a k =
      2 * (a : ℂ) ^ (k - 1) * (1 - (a : ℂ)) ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 4 := ⟨k - 4, by omega⟩
  simp [verticalPhiCoefficient]

/-- The convolution `u_k = ∑_{j=0}^k D_j D_{k-j}` from the source. -/
def verticalLeadingConvolution (n : ℕ) (a x Y t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    verticalLeadingMinor j a x Y t * verticalLeadingMinor (n - j) a x Y t

/-- Coefficients of `ℐ²` are exactly the `u_k` convolution. -/
theorem coeff_verticalLeadingSeries_sq (n : ℕ) (a x Y t : ℝ) :
    coeff n (verticalLeadingSeries a x Y t ^ 2) =
      verticalLeadingConvolution n a x Y t := by
  rw [pow_two, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [verticalLeadingSeries, coeff_mk, Nat.succ_eq_add_one,
    verticalLeadingConvolution]

/-- The series on the right side of `eq:F-prime-generating`. -/
def verticalPencilYDerivativeSeries (a x Y t : ℝ) : PowerSeries ℂ :=
  verticalPhi a * verticalLeadingSeries a x Y t ^ 2

/-- Coefficient of the differentiated generating series before splitting
off the first three exceptional coefficients of `φ_a`. -/
theorem coeff_verticalPencilYDerivativeSeries_sum (n : ℕ) (a x Y t : ℝ) :
    coeff n (verticalPencilYDerivativeSeries a x Y t) =
      ∑ k ∈ Finset.range (n + 1),
        verticalPhiCoefficient a k * verticalLeadingConvolution (n - k) a x Y t := by
  rw [verticalPencilYDerivativeSeries, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_verticalPhi, coeff_verticalLeadingSeries_sq,
    Nat.succ_eq_add_one]

/-- Splitting a convolution against the coefficient sequence of `φ_a`
gives exactly the exceptional first three terms and its geometric tail. -/
theorem verticalPhi_convolution (a : ℝ) (u : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), verticalPhiCoefficient a k * u (n - k) =
      lagWithZero u n 1 +
        (2 * (a : ℂ) * (1 - (a : ℂ))) * lagWithZero u n 2 +
        ((a : ℂ) ^ 2 * ((a : ℂ) ^ 2 - 4 * (a : ℂ) + 2)) *
          lagWithZero u n 3 +
        2 * (1 - (a : ℂ)) ^ 2 *
          ∑ k ∈ Finset.Icc 4 n, (a : ℂ) ^ (k - 1) * u (n - k) := by
  by_cases hn : n < 4
  · interval_cases n <;>
      simp [Finset.sum_range_succ, verticalPhiCoefficient, lagWithZero]
  · have hn₄ : 4 ≤ n := by omega
    have hparts :
        Finset.range (n + 1) = Finset.range 4 ∪ Finset.Icc 4 n := by
      ext k
      simp
      omega
    have hdisjoint : Disjoint (Finset.range 4) (Finset.Icc 4 n) := by
      rw [Finset.disjoint_left]
      intro k hkRange hkIcc
      simp only [Finset.mem_range] at hkRange
      simp only [Finset.mem_Icc] at hkIcc
      omega
    rw [hparts, Finset.sum_union hdisjoint]
    have htail :
        ∑ k ∈ Finset.Icc 4 n, verticalPhiCoefficient a k * u (n - k) =
          2 * (1 - (a : ℂ)) ^ 2 *
            ∑ k ∈ Finset.Icc 4 n, (a : ℂ) ^ (k - 1) * u (n - k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [verticalPhiCoefficient_of_four_le a (Finset.mem_Icc.mp hk).1]
      ring
    rw [htail]
    have hn₁ : 1 ≤ n := by omega
    have hn₂ : 2 ≤ n := by omega
    have hn₃ : 3 ≤ n := by omega
    simp [Finset.sum_range_succ, verticalPhiCoefficient, lagWithZero,
      hn₁, hn₂, hn₃]

/-- Equation `eq:F-prime-convolution` from the source, as the coefficient
formula for the right side `φ_a ℐ²` of `eq:F-prime-generating`. -/
theorem coeff_verticalPencilYDerivativeSeries (n : ℕ) (a x Y t : ℝ) :
    coeff n (verticalPencilYDerivativeSeries a x Y t) =
      lagWithZero (fun k => verticalLeadingConvolution k a x Y t) n 1 +
        (2 * (a : ℂ) * (1 - (a : ℂ))) *
          lagWithZero (fun k => verticalLeadingConvolution k a x Y t) n 2 +
        ((a : ℂ) ^ 2 * ((a : ℂ) ^ 2 - 4 * (a : ℂ) + 2)) *
          lagWithZero (fun k => verticalLeadingConvolution k a x Y t) n 3 +
        2 * (1 - (a : ℂ)) ^ 2 *
          ∑ k ∈ Finset.Icc 4 n,
            (a : ℂ) ^ (k - 1) * verticalLeadingConvolution (n - k) a x Y t := by
  rw [coeff_verticalPencilYDerivativeSeries_sum]
  exact verticalPhi_convolution a
    (fun k => verticalLeadingConvolution k a x Y t) n

/-! ## The analytic derivative represented by the formal series -/

/-- The Toeplitz matrix depends continuously on the nonnegative parameter
`Y`; the statement is global because `Real.sqrt` itself is continuous. -/
theorem continuous_verticalToeplitz (n : ℕ) (a x t : ℝ) :
    Continuous (fun Y : ℝ => verticalToeplitz n a x Y t) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp_rw [verticalToeplitz_apply]
  simp only [verticalToeplitzDiagonal, verticalToeplitzFirst]
  fun_prop

/-- Continuity of every Toeplitz continuant as a function of `Y`. -/
theorem continuous_verticalToeplitzDet (n : ℕ) (a x t : ℝ) :
    Continuous (fun Y : ℝ => verticalToeplitzDet n a x Y t) := by
  simpa only [verticalToeplitzDet] using
    (continuous_verticalToeplitz n a x t).matrix_det

/-- Continuity of each leading principal minor `D_n`. -/
theorem continuous_verticalLeadingMinor (n : ℕ) (a x t : ℝ) :
    Continuous (fun Y : ℝ => verticalLeadingMinor n a x Y t) := by
  cases n with
  | zero =>
      simpa only [verticalLeadingMinor_zero] using
        (continuous_const : Continuous fun _ : ℝ => (1 : ℂ))
  | succ n =>
      simpa only [verticalLeadingMinor_succ] using
        (continuous_verticalToeplitzDet (n + 1) a x t).sub
          (continuous_verticalToeplitzDet n a x t)

/-- Continuity of the finite convolution `u_n`. -/
theorem continuous_verticalLeadingConvolution (n : ℕ) (a x t : ℝ) :
    Continuous (fun Y : ℝ => verticalLeadingConvolution n a x Y t) := by
  apply continuous_finset_sum
  intro j _
  exact (continuous_verticalLeadingMinor j a x t).mul
    (continuous_verticalLeadingMinor (n - j) a x t)

/-- For fixed first factor, every coefficient of `φ_a ℐ(Y)ℐ(Y')` is
continuous in the second parameter. -/
theorem continuous_coeff_verticalPhi_mul_leading_mul (n : ℕ)
    (a x Y t : ℝ) :
    Continuous (fun Y' : ℝ =>
      coeff n (verticalPhi a * verticalLeadingSeries a x Y t *
        verticalLeadingSeries a x Y' t)) := by
  let p : PowerSeries ℂ := verticalPhi a * verticalLeadingSeries a x Y t
  change Continuous (fun Y' : ℝ =>
    coeff n (p * verticalLeadingSeries a x Y' t))
  simp only [coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    verticalLeadingSeries, coeff_mk]
  apply continuous_finset_sum
  intro j _
  exact continuous_const.mul
    (continuous_verticalLeadingMinor (n - j) a x t)

/-- Coefficientwise secant identity for the actual determinants `F_n`. -/
theorem verticalPencilDet_sub_eq (n : ℕ) (a x Y Y' t : ℝ)
    (hY : 0 ≤ Y) (hY' : 0 ≤ Y') :
    verticalPencilDet n a x Y' t - verticalPencilDet n a x Y t =
      ((Y' - Y : ℝ) : ℂ) *
        coeff n (verticalPhi a * verticalLeadingSeries a x Y t *
          verticalLeadingSeries a x Y' t) := by
  have hseries := verticalPencilSeries_add_sub a x Y (Y' - Y) t hY (by linarith)
  have hsum : Y + (Y' - Y) = Y' := by ring
  rw [hsum] at hseries
  have hrhs :
      C ((Y' - Y : ℝ) : ℂ) * verticalPhi a *
          verticalLeadingSeries a x Y t * verticalLeadingSeries a x Y' t =
        C ((Y' - Y : ℝ) : ℂ) *
          (verticalPhi a * verticalLeadingSeries a x Y t *
            verticalLeadingSeries a x Y' t) := by ring
  rw [hrhs] at hseries
  have hcoeff := congrArg (coeff n) hseries
  simpa only [map_sub, verticalPencilSeries, coeff_mk, coeff_C_mul] using hcoeff

/-- Away from the base point, the slope is the coefficient of the exact
secant factor. -/
theorem slope_verticalPencilDet_eq (n : ℕ) (a x Y Y' t : ℝ)
    (hY : 0 ≤ Y) (hY' : 0 ≤ Y') (hne : Y' ≠ Y) :
    slope (fun Z : ℝ => verticalPencilDet n a x Z t) Y Y' =
      coeff n (verticalPhi a * verticalLeadingSeries a x Y t *
        verticalLeadingSeries a x Y' t) := by
  rw [slope_def_module, verticalPencilDet_sub_eq n a x Y Y' t hY hY',
    Complex.real_smul]
  have hneComplex : (Y' : ℂ) ≠ (Y : ℂ) := by exact_mod_cast hne
  have hsubComplex : (Y' : ℂ) - (Y : ℂ) ≠ 0 := sub_ne_zero.mpr hneComplex
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ hsubComplex, one_mul]

/-- `eq:F-prime-generating` with its intended analytic meaning: for every
coefficient, the actual determinant has the right derivative on the closed
half-line `Y ≥ 0`, and that derivative is the corresponding coefficient of
`φ_a ℐ(Y)²`. -/
theorem hasDerivWithinAt_verticalPencilDet (n : ℕ) (a x Y t : ℝ)
    (hY : 0 ≤ Y) :
    HasDerivWithinAt (fun Y' : ℝ => verticalPencilDet n a x Y' t)
      (coeff n (verticalPencilYDerivativeSeries a x Y t)) (Set.Ici 0) Y := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  let g : ℝ → ℂ := fun Y' =>
    coeff n (verticalPhi a * verticalLeadingSeries a x Y t *
      verticalLeadingSeries a x Y' t)
  have hg : Continuous g :=
    continuous_coeff_verticalPhi_mul_leading_mul n a x Y t
  have ht : Tendsto g (nhdsWithin Y (Set.Ici 0 \ {Y})) (nhds (g Y)) :=
    hg.continuousAt.mono_left inf_le_left
  have hslope :
      Tendsto (slope (fun Y' : ℝ => verticalPencilDet n a x Y' t) Y)
        (nhdsWithin Y (Set.Ici 0 \ {Y})) (nhds (g Y)) := by
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with Y' hY'
    have hY'nonneg : 0 ≤ Y' := hY'.1
    have hY'ne : Y' ≠ Y := by simpa using hY'.2
    exact (slope_verticalPencilDet_eq n a x Y Y' t hY hY'nonneg hY'ne).symm
  have hseries :
      verticalPhi a * verticalLeadingSeries a x Y t *
          verticalLeadingSeries a x Y t =
        verticalPencilYDerivativeSeries a x Y t := by
    rw [verticalPencilYDerivativeSeries, pow_two]
    ring
  have hcoefficient : g Y =
      coeff n (verticalPencilYDerivativeSeries a x Y t) := by
    exact congrArg (coeff n) hseries
  simpa only [hcoefficient] using hslope

/-- The coefficientwise derivative theorem with the complete displayed
convolution from `eq:F-prime-convolution` substituted for the derivative. -/
theorem hasDerivWithinAt_verticalPencilDet_convolution (n : ℕ)
    (a x Y t : ℝ) (hY : 0 ≤ Y) :
    HasDerivWithinAt (fun Y' : ℝ => verticalPencilDet n a x Y' t)
      (lagWithZero (fun k => verticalLeadingConvolution k a x Y t) n 1 +
        (2 * (a : ℂ) * (1 - (a : ℂ))) *
          lagWithZero (fun k => verticalLeadingConvolution k a x Y t) n 2 +
        ((a : ℂ) ^ 2 * ((a : ℂ) ^ 2 - 4 * (a : ℂ) + 2)) *
          lagWithZero (fun k => verticalLeadingConvolution k a x Y t) n 3 +
        2 * (1 - (a : ℂ)) ^ 2 *
          ∑ k ∈ Finset.Icc 4 n,
            (a : ℂ) ^ (k - 1) * verticalLeadingConvolution (n - k) a x Y t)
      (Set.Ici 0) Y := by
  rw [← coeff_verticalPencilYDerivativeSeries]
  exact hasDerivWithinAt_verticalPencilDet n a x Y t hY

end

end ConnectedPseudospectrum
