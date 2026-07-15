import ConnectedPseudospectrum.FoldedCollision

/-!
# Exact folded Chebyshev formulas at a variable collision

The divided-difference quotients in `eq:fold-even` and `eq:fold-odd` are
interpreted as derivatives when the two folded variables coincide.  This
module proves that interpretation for the actual folded transfer sequences:
the derivative coefficients satisfy the squared quadratic recurrence, their
four boundary residuals agree with the transfer residuals, and fourth-order
recurrence uniqueness gives equality in every degree.
-/

namespace ConnectedPseudospectrum

noncomputable section

theorem foldEvenChebyshevFunction_recurrence
    (m : ℕ) (u zeta : ℝ) :
    foldEvenChebyshevFunction (m + 2) u zeta =
      2 * u * foldEvenChebyshevFunction (m + 1) u zeta -
        foldEvenChebyshevFunction m u zeta := by
  have h2 := chebyshevU_add_two (m : ℤ) u
  have h1 := chebyshevU_add_one (m : ℤ) u
  unfold foldEvenChebyshevFunction
  norm_num at h2 h1 ⊢
  rw [show (m : ℤ) + 2 - 1 = (m : ℤ) + 1 by ring]
  rw [h2, h1]
  rw [show (m : ℤ) - 1 = -1 + (m : ℤ) by ring]
  ring

theorem foldOddChebyshevFunction_recurrence
    (m : ℕ) (x s beta u : ℝ) :
    foldOddChebyshevFunction (m + 2) x s beta u =
      2 * u * foldOddChebyshevFunction (m + 1) x s beta u -
        foldOddChebyshevFunction m x s beta u := by
  have h2 := chebyshevU_add_two (m : ℤ) u
  unfold foldOddChebyshevFunction
  norm_num at h2 ⊢
  rw [h2]
  ring

theorem deriv_foldEvenChebyshevFunction_recurrence
    (m : ℕ) (u zeta : ℝ) :
    deriv (fun v => foldEvenChebyshevFunction (m + 2) v zeta) u =
      2 * foldEvenChebyshevFunction (m + 1) u zeta +
        2 * u * deriv (fun v => foldEvenChebyshevFunction (m + 1) v zeta) u -
        deriv (fun v => foldEvenChebyshevFunction m v zeta) u := by
  have hfun :
      (fun v => foldEvenChebyshevFunction (m + 2) v zeta) =
        (fun v => 2 * v * foldEvenChebyshevFunction (m + 1) v zeta -
          foldEvenChebyshevFunction m v zeta) := by
    funext v
    exact foldEvenChebyshevFunction_recurrence m v zeta
  have h1 := differentiableAt_foldEvenChebyshevFunction (m + 1) u zeta
  have h0 := differentiableAt_foldEvenChebyshevFunction m u zeta
  have hlhs :
      HasDerivAt (fun v => foldEvenChebyshevFunction (m + 2) v zeta)
        (2 * foldEvenChebyshevFunction (m + 1) u zeta +
          2 * u * deriv
            (fun v => foldEvenChebyshevFunction (m + 1) v zeta) u -
          deriv (fun v => foldEvenChebyshevFunction m v zeta) u) u := by
    rw [hfun]
    convert ((((hasDerivAt_id u).const_mul 2).mul h1.hasDerivAt).sub
      h0.hasDerivAt) using 1
    all_goals simp only [id_eq]
    all_goals ring
  exact hlhs.deriv

theorem deriv_foldOddChebyshevFunction_recurrence
    (m : ℕ) (x s beta u : ℝ) :
    deriv (fun v => foldOddChebyshevFunction (m + 2) x s beta v) u =
      2 * foldOddChebyshevFunction (m + 1) x s beta u +
        2 * u * deriv
          (fun v => foldOddChebyshevFunction (m + 1) x s beta v) u -
        deriv (fun v => foldOddChebyshevFunction m x s beta v) u := by
  have hfun :
      (fun v => foldOddChebyshevFunction (m + 2) x s beta v) =
        (fun v => 2 * v * foldOddChebyshevFunction (m + 1) x s beta v -
          foldOddChebyshevFunction m x s beta v) := by
    funext v
    exact foldOddChebyshevFunction_recurrence m x s beta v
  have h1 := differentiableAt_foldOddChebyshevFunction (m + 1) x s beta u
  have h0 := differentiableAt_foldOddChebyshevFunction m x s beta u
  have hlhs :
      HasDerivAt (fun v => foldOddChebyshevFunction (m + 2) x s beta v)
        (2 * foldOddChebyshevFunction (m + 1) x s beta u +
          2 * u * deriv
            (fun v => foldOddChebyshevFunction (m + 1) x s beta v) u -
          deriv (fun v => foldOddChebyshevFunction m x s beta v) u) u := by
    rw [hfun]
    convert ((((hasDerivAt_id u).const_mul 2).mul h1.hasDerivAt).sub
      h0.hasDerivAt) using 1
    all_goals simp only [id_eq]
    all_goals ring
  exact hlhs.deriv

theorem deriv_foldEvenChebyshevFunction_fourthOrder
    (m : ℕ) (u zeta : ℝ) :
    deriv (fun v => foldEvenChebyshevFunction (m + 4) v zeta) u -
        4 * u * deriv
          (fun v => foldEvenChebyshevFunction (m + 3) v zeta) u +
        (4 * u ^ 2 + 2) * deriv
          (fun v => foldEvenChebyshevFunction (m + 2) v zeta) u -
        4 * u * deriv
          (fun v => foldEvenChebyshevFunction (m + 1) v zeta) u +
        deriv (fun v => foldEvenChebyshevFunction m v zeta) u = 0 := by
  have h2 := deriv_foldEvenChebyshevFunction_recurrence (m + 2) u zeta
  have h1 := deriv_foldEvenChebyshevFunction_recurrence (m + 1) u zeta
  have h0 := deriv_foldEvenChebyshevFunction_recurrence m u zeta
  have hf := foldEvenChebyshevFunction_recurrence (m + 1) u zeta
  norm_num at h2 h1 hf
  linear_combination h2 - 2 * u * h1 + h0 + 2 * hf

theorem deriv_foldOddChebyshevFunction_fourthOrder
    (m : ℕ) (x s beta u : ℝ) :
    deriv (fun v => foldOddChebyshevFunction (m + 4) x s beta v) u -
        4 * u * deriv
          (fun v => foldOddChebyshevFunction (m + 3) x s beta v) u +
        (4 * u ^ 2 + 2) * deriv
          (fun v => foldOddChebyshevFunction (m + 2) x s beta v) u -
        4 * u * deriv
          (fun v => foldOddChebyshevFunction (m + 1) x s beta v) u +
        deriv (fun v => foldOddChebyshevFunction m x s beta v) u = 0 := by
  have h2 := deriv_foldOddChebyshevFunction_recurrence
    (m + 2) x s beta u
  have h1 := deriv_foldOddChebyshevFunction_recurrence
    (m + 1) x s beta u
  have h0 := deriv_foldOddChebyshevFunction_recurrence m x s beta u
  have hf := foldOddChebyshevFunction_recurrence (m + 1) x s beta u
  norm_num at h2 h1 hf
  linear_combination h2 - 2 * u * h1 + h0 + 2 * hf

/-- The derivative value that replaces the even divided difference when its
two folded variables collide. -/
def foldEvenCollisionCandidate (a u zeta : ℝ) (m : ℕ) : ℝ :=
  a ^ m * deriv (fun v => foldEvenChebyshevFunction m v zeta) u

/-- The derivative value that replaces the odd divided difference when its
two folded variables collide. -/
def foldOddCollisionCandidate
    (a x s beta u : ℝ) (m : ℕ) : ℝ :=
  a ^ m * deriv (fun v => foldOddChebyshevFunction m x s beta v) u

theorem foldEvenCollisionCandidate_recurrence
    (a u zeta : ℝ) (m : ℕ) :
    foldEvenCollisionCandidate a u zeta (m + 4) -
        4 * a * u * foldEvenCollisionCandidate a u zeta (m + 3) +
        a ^ 2 * (4 * u ^ 2 + 2) *
          foldEvenCollisionCandidate a u zeta (m + 2) -
        4 * a ^ 3 * u * foldEvenCollisionCandidate a u zeta (m + 1) +
        a ^ 4 * foldEvenCollisionCandidate a u zeta m = 0 := by
  have h := deriv_foldEvenChebyshevFunction_fourthOrder m u zeta
  unfold foldEvenCollisionCandidate
  simp only [pow_add]
  linear_combination a ^ m * a ^ 4 * h

theorem foldOddCollisionCandidate_recurrence
    (a x s beta u : ℝ) (m : ℕ) :
    foldOddCollisionCandidate a x s beta u (m + 4) -
        4 * a * u * foldOddCollisionCandidate a x s beta u (m + 3) +
        a ^ 2 * (4 * u ^ 2 + 2) *
          foldOddCollisionCandidate a x s beta u (m + 2) -
        4 * a ^ 3 * u * foldOddCollisionCandidate a x s beta u (m + 1) +
        a ^ 4 * foldOddCollisionCandidate a x s beta u m = 0 := by
  have h := deriv_foldOddChebyshevFunction_fourthOrder m x s beta u
  unfold foldOddCollisionCandidate
  simp only [pow_add]
  linear_combination a ^ m * a ^ 4 * h

theorem deriv_foldEvenChebyshevFunction_zero (u zeta : ℝ) :
    deriv (fun v => foldEvenChebyshevFunction 0 v zeta) u = 1 := by
  norm_num [foldEvenChebyshevFunction, chebyshevU]

theorem deriv_foldEvenChebyshevFunction_one (u zeta : ℝ) :
    deriv (fun v => foldEvenChebyshevFunction 1 v zeta) u =
      4 * u + 1 - 2 * zeta := by
  have h : HasDerivAt (fun v : ℝ => (v - zeta) * (2 * v + 1))
      (4 * u + 1 - 2 * zeta) u := by
    convert ((hasDerivAt_id u).sub_const zeta).mul
      (((hasDerivAt_id u).const_mul 2).add_const 1) using 1
    all_goals simp only [id_eq]
    all_goals ring
  norm_num [foldEvenChebyshevFunction, chebyshevU, h.deriv]

theorem deriv_foldOddChebyshevFunction_zero (x s beta u : ℝ) :
    deriv (fun v => foldOddChebyshevFunction 0 x s beta v) u = x - s := by
  have h : HasDerivAt (fun v : ℝ => (x - s) * v) (x - s) u := by
    convert (hasDerivAt_id u).const_mul (x - s) using 1
    all_goals ring
  norm_num [foldOddChebyshevFunction, chebyshevU, h.deriv]

theorem deriv_foldOddChebyshevFunction_one (x s beta u : ℝ) :
    deriv (fun v => foldOddChebyshevFunction 1 x s beta v) u =
      4 * u * (x - s) - 2 * beta := by
  have h : HasDerivAt
      (fun v : ℝ => ((x - s) * v - beta) * (2 * v))
      (4 * u * (x - s) - 2 * beta) u := by
    convert (((hasDerivAt_id u).const_mul (x - s)).sub_const beta).mul
      ((hasDerivAt_id u).const_mul 2) using 1
    all_goals simp only [id_eq]
    all_goals ring
  norm_num [foldOddChebyshevFunction, chebyshevU, h.deriv]

theorem foldEvenCollisionCandidate_zero (a u zeta : ℝ) :
    foldEvenCollisionCandidate a u zeta 0 = 1 := by
  simp [foldEvenCollisionCandidate, deriv_foldEvenChebyshevFunction_zero]

theorem foldEvenCollisionCandidate_one (a u zeta : ℝ) :
    foldEvenCollisionCandidate a u zeta 1 =
      a * (4 * u + 1 - 2 * zeta) := by
  simp [foldEvenCollisionCandidate, deriv_foldEvenChebyshevFunction_one]

theorem foldOddCollisionCandidate_zero (a x s beta u : ℝ) :
    foldOddCollisionCandidate a x s beta u 0 = x - s := by
  simp [foldOddCollisionCandidate, deriv_foldOddChebyshevFunction_zero]

theorem foldOddCollisionCandidate_one (a x s beta u : ℝ) :
    foldOddCollisionCandidate a x s beta u 1 =
      a * (4 * u * (x - s) - 2 * beta) := by
  simp [foldOddCollisionCandidate, deriv_foldOddChebyshevFunction_one]

theorem foldEvenCollisionCandidate_residual_one (a u zeta : ℝ) :
    foldEvenCollisionCandidate a u zeta 1 -
        4 * a * u * foldEvenCollisionCandidate a u zeta 0 =
      a * (1 - 2 * zeta) := by
  rw [foldEvenCollisionCandidate_zero, foldEvenCollisionCandidate_one]
  ring

theorem foldEvenCollisionCandidate_residual_two (a u zeta : ℝ) :
    foldEvenCollisionCandidate a u zeta 2 -
        4 * a * u * foldEvenCollisionCandidate a u zeta 1 +
        a ^ 2 * (4 * u ^ 2 + 2) *
          foldEvenCollisionCandidate a u zeta 0 =
      a ^ 2 * (1 - 2 * zeta) := by
  have hrec := deriv_foldEvenChebyshevFunction_recurrence 0 u zeta
  norm_num at hrec
  unfold foldEvenCollisionCandidate
  norm_num
  rw [hrec, deriv_foldEvenChebyshevFunction_zero,
    deriv_foldEvenChebyshevFunction_one]
  norm_num [foldEvenChebyshevFunction, chebyshevU]
  ring

theorem foldEvenCollisionCandidate_residual_three (a u zeta : ℝ) :
    foldEvenCollisionCandidate a u zeta 3 -
        4 * a * u * foldEvenCollisionCandidate a u zeta 2 +
        a ^ 2 * (4 * u ^ 2 + 2) *
          foldEvenCollisionCandidate a u zeta 1 -
        4 * a ^ 3 * u * foldEvenCollisionCandidate a u zeta 0 = a ^ 3 := by
  have hrec1 := deriv_foldEvenChebyshevFunction_recurrence 1 u zeta
  have hrec0 := deriv_foldEvenChebyshevFunction_recurrence 0 u zeta
  have hf := foldEvenChebyshevFunction_recurrence 0 u zeta
  norm_num at hrec1 hrec0 hf
  unfold foldEvenCollisionCandidate
  norm_num
  rw [hrec1, hrec0, hf, deriv_foldEvenChebyshevFunction_zero,
    deriv_foldEvenChebyshevFunction_one]
  norm_num [foldEvenChebyshevFunction, chebyshevU]
  ring

theorem foldOddCollisionCandidate_residual_one
    (a x s beta u : ℝ) :
    foldOddCollisionCandidate a x s beta u 1 -
        4 * a * u * foldOddCollisionCandidate a x s beta u 0 =
      -2 * a * beta := by
  rw [foldOddCollisionCandidate_zero, foldOddCollisionCandidate_one]
  ring

theorem foldOddCollisionCandidate_residual_two
    (a x s beta u : ℝ) :
    foldOddCollisionCandidate a x s beta u 2 -
        4 * a * u * foldOddCollisionCandidate a x s beta u 1 +
        a ^ 2 * (4 * u ^ 2 + 2) *
          foldOddCollisionCandidate a x s beta u 0 = a ^ 2 * (x - s) := by
  have hrec := deriv_foldOddChebyshevFunction_recurrence 0 x s beta u
  norm_num at hrec
  unfold foldOddCollisionCandidate
  norm_num
  rw [hrec, deriv_foldOddChebyshevFunction_zero,
    deriv_foldOddChebyshevFunction_one]
  norm_num [foldOddChebyshevFunction, chebyshevU]
  ring

theorem foldOddCollisionCandidate_residual_three
    (a x s beta u : ℝ) :
    foldOddCollisionCandidate a x s beta u 3 -
        4 * a * u * foldOddCollisionCandidate a x s beta u 2 +
        a ^ 2 * (4 * u ^ 2 + 2) *
          foldOddCollisionCandidate a x s beta u 1 -
        4 * a ^ 3 * u * foldOddCollisionCandidate a x s beta u 0 = 0 := by
  have hrec1 := deriv_foldOddChebyshevFunction_recurrence 1 x s beta u
  have hrec0 := deriv_foldOddChebyshevFunction_recurrence 0 x s beta u
  have hf := foldOddChebyshevFunction_recurrence 0 x s beta u
  norm_num at hrec1 hrec0 hf
  unfold foldOddCollisionCandidate
  norm_num
  rw [hrec1, hrec0, hf, deriv_foldOddChebyshevFunction_zero,
    deriv_foldOddChebyshevFunction_one]
  norm_num [foldOddChebyshevFunction, chebyshevU]
  ring

theorem fourthOrderSequence_unique
    {p q : ℕ → ℝ} {c1 c2 c3 c4 : ℝ}
    (hp : ∀ m, p (m + 4) - c1 * p (m + 3) + c2 * p (m + 2) -
      c3 * p (m + 1) + c4 * p m = 0)
    (hq : ∀ m, q (m + 4) - c1 * q (m + 3) + c2 * q (m + 2) -
      c3 * q (m + 1) + c4 * q m = 0)
    (h0 : p 0 = q 0) (h1 : p 1 = q 1)
    (h2 : p 2 = q 2) (h3 : p 3 = q 3) :
    ∀ m, p m = q m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hm : m < 4
      · interval_cases m <;> assumption
      · have hm4 : 4 ≤ m := by omega
        let k := m - 4
        have hk0 : k < m := by dsimp [k]; omega
        have hk1 : k + 1 < m := by dsimp [k]; omega
        have hk2 : k + 2 < m := by dsimp [k]; omega
        have hk3 : k + 3 < m := by dsimp [k]; omega
        have hk4 : k + 4 = m := by dsimp [k]; omega
        have hp' := hp k
        have hq' := hq k
        rw [hk4, ih k hk0, ih (k + 1) hk1, ih (k + 2) hk2,
          ih (k + 3) hk3] at hp'
        rw [hk4] at hq'
        linear_combination hp' - hq'

theorem foldEvenSequence_eq_collisionCandidate
    {a x s u : ℝ} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hsum : 4 * a * u = foldC0 a x s)
    (hprod : a ^ 2 * (4 * u ^ 2 + 2) = foldB a x s) :
    ∀ m, foldEvenSequence a x s m =
      foldEvenCollisionCandidate a u (foldZeta a s) m := by
  have hcand : ∀ m,
      foldEvenCollisionCandidate a u (foldZeta a s) (m + 4) -
          foldC0 a x s *
            foldEvenCollisionCandidate a u (foldZeta a s) (m + 3) +
          foldB a x s *
            foldEvenCollisionCandidate a u (foldZeta a s) (m + 2) -
          a ^ 2 * foldC0 a x s *
            foldEvenCollisionCandidate a u (foldZeta a s) (m + 1) +
          a ^ 4 * foldEvenCollisionCandidate a u (foldZeta a s) m = 0 := by
    intro m
    rw [← hsum, ← hprod]
    have h := foldEvenCollisionCandidate_recurrence
      a u (foldZeta a s) m
    linear_combination h
  have hzero : foldEvenSequence a x s 0 =
      foldEvenCollisionCandidate a u (foldZeta a s) 0 := by
    rw [foldEvenSequence_zero, foldEvenCollisionCandidate_zero]
  have hone : foldEvenSequence a x s 1 =
      foldEvenCollisionCandidate a u (foldZeta a s) 1 := by
    have hp := foldEvenSequence_residual_one
      (a := a) (x := x) (s := s) ha0 ha1
    have hq := foldEvenCollisionCandidate_residual_one
      a u (foldZeta a s)
    rw [← hsum, hzero] at hp
    linear_combination hp - hq
  have htwo : foldEvenSequence a x s 2 =
      foldEvenCollisionCandidate a u (foldZeta a s) 2 := by
    have hp := foldEvenSequence_residual_two
      (a := a) (x := x) (s := s) ha0 ha1
    have hq := foldEvenCollisionCandidate_residual_two
      a u (foldZeta a s)
    rw [← hsum, ← hprod, hzero, hone] at hp
    linear_combination hp - hq
  have hthree : foldEvenSequence a x s 3 =
      foldEvenCollisionCandidate a u (foldZeta a s) 3 := by
    have hp := foldEvenSequence_residual_three
      (a := a) (x := x) (s := s) ha1
    have hq := foldEvenCollisionCandidate_residual_three
      a u (foldZeta a s)
    rw [← hsum, ← hprod, hzero, hone, htwo] at hp
    linear_combination hp - hq
  exact fourthOrderSequence_unique
    (foldEvenSequence_recurrence (a := a) (x := x) (s := s) ha1)
    hcand hzero hone htwo hthree

theorem foldOddSequence_eq_collisionCandidate
    {a x s u : ℝ} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hsum : 4 * a * u = foldC0 a x s)
    (hprod : a ^ 2 * (4 * u ^ 2 + 2) = foldB a x s) :
    ∀ m, foldOddSequence a x s m =
      foldOddCollisionCandidate a x s (foldOddBeta a x s) u m := by
  have hbeta :
      2 * a * foldOddBeta a x s = x * (1 + a ^ 2) + 2 * a * s := by
    unfold foldOddBeta
    field_simp [ha0]
  have hcand : ∀ m,
      foldOddCollisionCandidate a x s (foldOddBeta a x s) u (m + 4) -
          foldC0 a x s *
            foldOddCollisionCandidate a x s (foldOddBeta a x s) u (m + 3) +
          foldB a x s *
            foldOddCollisionCandidate a x s (foldOddBeta a x s) u (m + 2) -
          a ^ 2 * foldC0 a x s *
            foldOddCollisionCandidate a x s (foldOddBeta a x s) u (m + 1) +
          a ^ 4 *
            foldOddCollisionCandidate a x s (foldOddBeta a x s) u m = 0 := by
    intro m
    rw [← hsum, ← hprod]
    have h := foldOddCollisionCandidate_recurrence
      a x s (foldOddBeta a x s) u m
    linear_combination h
  have hzero : foldOddSequence a x s 0 =
      foldOddCollisionCandidate a x s (foldOddBeta a x s) u 0 := by
    rw [foldOddSequence_zero, foldOddCollisionCandidate_zero]
  have hone : foldOddSequence a x s 1 =
      foldOddCollisionCandidate a x s (foldOddBeta a x s) u 1 := by
    have hp := foldOddSequence_residual_one
      (a := a) (x := x) (s := s) ha1
    have hq := foldOddCollisionCandidate_residual_one
      a x s (foldOddBeta a x s) u
    rw [← hsum, hzero] at hp
    linear_combination hp - hq + hbeta
  have htwo : foldOddSequence a x s 2 =
      foldOddCollisionCandidate a x s (foldOddBeta a x s) u 2 := by
    have hp := foldOddSequence_residual_two
      (a := a) (x := x) (s := s) ha1
    have hq := foldOddCollisionCandidate_residual_two
      a x s (foldOddBeta a x s) u
    rw [← hsum, ← hprod, hzero, hone] at hp
    linear_combination hp - hq
  have hthree : foldOddSequence a x s 3 =
      foldOddCollisionCandidate a x s (foldOddBeta a x s) u 3 := by
    have hp := foldOddSequence_residual_three
      (a := a) (x := x) (s := s) ha1
    have hq := foldOddCollisionCandidate_residual_three
      a x s (foldOddBeta a x s) u
    rw [← hsum, ← hprod, hzero, hone, htwo] at hp
    linear_combination hp - hq
  exact fourthOrderSequence_unique
    (foldOddSequence_recurrence (a := a) (x := x) (s := s) ha1)
    hcand hzero hone htwo hthree

theorem foldXiPlus_eq_foldXiMinus_of_discriminant_eq_zero
    {a x s : ℝ} (hdisc : foldDiscriminant a x s = 0) :
    foldXiPlus a x s = foldXiMinus a x s := by
  simp [foldXiPlus, foldXiMinus, hdisc]

theorem foldEvenSequence_eq_deriv_at_foldXi_collision
    {a x s : ℝ} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hdisc : foldDiscriminant a x s = 0) (m : ℕ) :
    foldEvenSequence a x s m =
      a ^ m * deriv
        (fun u => foldEvenChebyshevFunction m u (foldZeta a s))
        (foldXiPlus a x s) := by
  have hxi := foldXiPlus_eq_foldXiMinus_of_discriminant_eq_zero hdisc
  have hsum := foldXiPlus_add_foldXiMinus (x := x) (s := s) ha0
  have hprod := foldXiPlus_mul_foldXiMinus (x := x) (s := s) ha0
    (hdisc ▸ le_rfl)
  rw [← hxi] at hsum hprod
  change foldEvenSequence a x s m =
    foldEvenCollisionCandidate a (foldXiPlus a x s) (foldZeta a s) m
  apply foldEvenSequence_eq_collisionCandidate ha0 ha1
  · linear_combination hsum
  · convert hprod using 1
    all_goals ring

theorem foldOddSequence_eq_deriv_at_foldXi_collision
    {a x s : ℝ} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hdisc : foldDiscriminant a x s = 0) (m : ℕ) :
    foldOddSequence a x s m =
      a ^ m * deriv
        (fun u => foldOddChebyshevFunction m x s (foldOddBeta a x s) u)
        (foldXiPlus a x s) := by
  have hxi := foldXiPlus_eq_foldXiMinus_of_discriminant_eq_zero hdisc
  have hsum := foldXiPlus_add_foldXiMinus (x := x) (s := s) ha0
  have hprod := foldXiPlus_mul_foldXiMinus (x := x) (s := s) ha0
    (hdisc ▸ le_rfl)
  rw [← hxi] at hsum hprod
  change foldOddSequence a x s m =
    foldOddCollisionCandidate a x s (foldOddBeta a x s)
      (foldXiPlus a x s) m
  apply foldOddSequence_eq_collisionCandidate ha0 ha1
  · linear_combination hsum
  · convert hprod using 1
    all_goals ring

end

end ConnectedPseudospectrum
