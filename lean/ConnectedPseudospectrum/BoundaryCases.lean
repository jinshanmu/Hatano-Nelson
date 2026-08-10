import ConnectedPseudospectrum.GeneralPseudospectrum
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Normal and reducible boundary cases

This module records the scalar threshold at the normal endpoint of the
tridiagonal Toeplitz family.  Its parity formula is exactly the quantity
`eta_n` in Proposition 3.2 of the ELA manuscript.  The two parity
transitions are proved separately, since this is where strict
adjacent-dimension monotonicity at the normal endpoint enters.
-/

namespace ConnectedPseudospectrum

open Filter Set

noncomputable section

/-- The elementary quadratic upper bound for `1 - cos x`. -/
private theorem one_sub_cos_le_sq_div_two (x : ℝ) :
    1 - Real.cos x ≤ x ^ 2 / 2 := by
  have hsin : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
  have hsq : Real.sin (x / 2) ^ 2 ≤ (x / 2) ^ 2 := by
    simpa only [sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg _) hsin 2)
  have hid := Real.sin_sq_eq_half_sub (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hid
  nlinarith

/-- The sharp cubic lower Taylor bound for sine on the nonnegative axis. -/
private theorem sub_sin_le_cube_div_six {x : ℝ} (hx : 0 ≤ x) :
    x - Real.sin x ≤ x ^ 3 / 6 := by
  let f : ℝ → ℝ := fun t => Real.sin t - t + t ^ 3 / 6
  have hfderiv : ∀ t : ℝ,
      HasDerivAt f (Real.cos t - 1 + t ^ 2 / 2) t := by
    intro t
    dsimp only [f]
    convert (Real.hasDerivAt_sin t).sub (hasDerivAt_id t) |>.add
      (((hasDerivAt_id t).pow 3).div_const 6) using 1
    simp only [id_eq]
    ring
  have hfmono : Monotone f := by
    apply monotone_of_deriv_nonneg
    · intro t
      exact (hfderiv t).differentiableAt
    · intro t
      rw [(hfderiv t).deriv]
      linarith [one_sub_cos_le_sq_div_two t]
  have h := hfmono hx
  dsimp only [f] at h
  norm_num at h
  linarith

/-- Half the largest adjacent spectral gap for the symmetric Dirichlet path.
This is `eta_n` in the ELA manuscript. -/
def normalThreshold (n : ℕ) : ℝ :=
  if Even n then
    2 * Real.sin (Real.pi / (2 * (n + 1 : ℝ)))
  else
    Real.sin (Real.pi / (n + 1 : ℝ))

@[simp] theorem normalThreshold_even (m : ℕ) :
    normalThreshold (2 * m) =
      2 * Real.sin (Real.pi / (2 * ((2 * m : ℕ) + 1 : ℝ))) := by
  simp [normalThreshold]

@[simp] theorem normalThreshold_odd (m : ℕ) :
    normalThreshold (2 * m + 1) =
      Real.sin (Real.pi / (((2 * m + 1 : ℕ) + 1 : ℝ))) := by
  simp [normalThreshold]

/-- The even-to-odd transition of the normal threshold is strict. -/
theorem normalThreshold_two_mul_add_one_lt (m : ℕ) (hm : 1 ≤ m) :
    normalThreshold (2 * m + 1) < normalThreshold (2 * m) := by
  rw [normalThreshold_odd, normalThreshold_even]
  let x : ℝ := Real.pi / (2 * ((2 * m : ℕ) + 1 : ℝ))
  let y : ℝ := Real.pi / (((2 * m + 1 : ℕ) + 1 : ℝ))
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hy0 : 0 < y := by
    dsimp [y]
    positivity
  have hy_lt_two_x : y < 2 * x := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have htwoX : 2 * x = Real.pi / (2 * (m : ℝ) + 1) := by
      dsimp [x]
      push_cast
      field_simp
    rw [htwoX]
    dsimp [y]
    push_cast
    apply (div_lt_div_iff_of_pos_left Real.pi_pos (by positivity)
      (by positivity)).2
    linarith
  have htwo_x_le : 2 * x ≤ Real.pi / 2 := by
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have htwoX : 2 * x = Real.pi / (2 * (m : ℝ) + 1) := by
      dsimp [x]
      push_cast
      field_simp
    rw [htwoX]
    apply (div_le_div_iff_of_pos_left Real.pi_pos (by positivity)
      (by norm_num)).2
    linarith
  have hsin_y_lt : Real.sin y < Real.sin (2 * x) := by
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [Real.pi_pos]) htwo_x_le hy_lt_two_x
  have hsin_two_x_lt : Real.sin (2 * x) < 2 * Real.sin x := by
    rw [Real.sin_two_mul]
    have hsinx : 0 < Real.sin x := by
      apply Real.sin_pos_of_pos_of_lt_pi hx0
      linarith [htwo_x_le, Real.pi_pos]
    have hcosx : Real.cos x < 1 := by
      simpa using Real.cos_lt_cos_of_nonneg_of_le_pi
        (x := 0) (y := x) (by norm_num)
          (by linarith [htwo_x_le, Real.pi_pos]) hx0
    nlinarith
  change Real.sin y < 2 * Real.sin x
  exact hsin_y_lt.trans hsin_two_x_lt

/-- The odd-to-even transition of the normal threshold is strict. -/
theorem normalThreshold_two_mul_add_two_lt (m : ℕ) (hm : 1 ≤ m) :
    normalThreshold (2 * m + 2) < normalThreshold (2 * m + 1) := by
  rw [show 2 * m + 2 = 2 * (m + 1) by omega,
    normalThreshold_even, normalThreshold_odd]
  let p : ℕ := m + 1
  let x : ℝ := Real.pi / (2 * (p : ℝ))
  let y : ℝ := Real.pi / (2 * ((2 * p : ℕ) + 1 : ℝ))
  have hp : 2 ≤ p := by omega
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hx0 : 0 < x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    have hpi := Real.pi_lt_four
    have hpPos : (0 : ℝ) < p := by positivity
    apply (div_le_iff₀ (mul_pos (by norm_num) hpPos)).2
    nlinarith
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hsinx : x - x ^ 3 / 4 < Real.sin x :=
    Real.sin_gt_sub_cube hx0 hx1
  have hsiny : Real.sin y < y := Real.sin_lt hy0
  have hpiSq : Real.pi ^ 2 < 10 := by
    nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have hpoly : Real.pi ^ 2 * (2 * (p : ℝ) + 1) < 16 * (p : ℝ) ^ 2 := by
    have hpquad : 10 * (2 * (p : ℝ) + 1) ≤ 16 * (p : ℝ) ^ 2 := by
      nlinarith
    have hfac : 0 < 2 * (p : ℝ) + 1 := by positivity
    exact (mul_lt_mul_of_pos_right hpiSq hfac).trans_le hpquad
  have hxy : 2 * y < x - x ^ 3 / 4 := by
    have hp0 : (0 : ℝ) < p := by positivity
    have htwoP : (0 : ℝ) < 2 * p + 1 := by positivity
    have hnumer : 0 < 16 * (p : ℝ) ^ 2 -
        Real.pi ^ 2 * (2 * (p : ℝ) + 1) := sub_pos.mpr hpoly
    have hidentity :
        x - x ^ 3 / 4 - 2 * y =
          Real.pi * (16 * (p : ℝ) ^ 2 -
            Real.pi ^ 2 * (2 * (p : ℝ) + 1)) /
              (32 * (p : ℝ) ^ 3 * (2 * (p : ℝ) + 1)) := by
      dsimp [x, y]
      push_cast
      field_simp
      ring
    rw [← sub_pos, hidentity]
    positivity
  have hresult : 2 * Real.sin y < Real.sin x := by linarith
  have hden : 2 * (m : ℝ) + 1 + 1 = 2 * ((m : ℝ) + 1) := by ring
  simpa [x, y, p, Nat.cast_add, Nat.cast_mul, hden] using hresult

/-- At the normal endpoint the exact threshold is strictly decreasing in
every adjacent dimension `n ≥ 2`. -/
theorem normalThreshold_succ_lt (n : ℕ) (hn : 2 ≤ n) :
    normalThreshold (n + 1) < normalThreshold n := by
  rcases n.even_or_odd' with ⟨m, rfl | rfl⟩
  · exact normalThreshold_two_mul_add_one_lt m (by omega)
  · convert normalThreshold_two_mul_add_two_lt m (by omega) using 1

/-- Explicit uniform remainder bound behind
`eta_n = pi/(n+1) + O(n^{-3})`.  The same constant works in both parity
classes; the even case actually has the stronger factor `1/24`. -/
theorem normalThreshold_error_bound (n : ℕ) :
    0 ≤ Real.pi / (n + 1 : ℝ) - normalThreshold n ∧
      Real.pi / (n + 1 : ℝ) - normalThreshold n ≤
        Real.pi ^ 3 / (6 * (n + 1 : ℝ) ^ 3) := by
  let x : ℝ := Real.pi / (n + 1 : ℝ)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  rcases n.even_or_odd' with ⟨m, rfl | rfl⟩
  · have heta : normalThreshold (2 * m) = 2 * Real.sin (x / 2) := by
      rw [normalThreshold_even]
      congr 2
      dsimp [x]
      push_cast
      field_simp
    have hleft : 0 ≤ x - 2 * Real.sin (x / 2) := by
      have hs := Real.sin_le (show 0 ≤ x / 2 by positivity)
      linarith
    have hright : x - 2 * Real.sin (x / 2) ≤ x ^ 3 / 6 := by
      have hs := sub_sin_le_cube_div_six (show 0 ≤ x / 2 by positivity)
      nlinarith [sq_nonneg x]
    rw [heta]
    constructor
    · exact hleft
    · calc
        x - 2 * Real.sin (x / 2) ≤ x ^ 3 / 6 := hright
        _ = Real.pi ^ 3 / (6 * ((2 * m : ℕ) + 1 : ℝ) ^ 3) := by
          dsimp [x]
          push_cast
          field_simp
  · rw [normalThreshold_odd]
    have hleft : 0 ≤ x - Real.sin x := sub_nonneg.mpr (Real.sin_le hx)
    have hright : x - Real.sin x ≤ x ^ 3 / 6 :=
      sub_sin_le_cube_div_six hx
    have hxdef : x = Real.pi / (((2 * m + 1 : ℕ) + 1 : ℝ)) := by
      rfl
    constructor
    · simpa [hxdef] using hleft
    · rw [hxdef] at hright
      convert hright using 1
      field_simp

end

end ConnectedPseudospectrum
