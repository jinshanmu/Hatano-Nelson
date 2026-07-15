import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# Chebyshev identities for the folded path calculation

This module records the second-kind Chebyshev normalization used in the
paper.  Integer indices are intentional: the transfer formulas use the
boundary value `U₋₁ = 0` as well as the usual natural-number indices.
-/

namespace ConnectedPseudospectrum

open Real

noncomputable section

/-- Evaluation of the second-kind Chebyshev polynomial `Uₙ` at a real point. -/
def chebyshevU (n : ℤ) (x : ℝ) : ℝ :=
  (Polynomial.Chebyshev.U ℝ n).eval x

@[simp] theorem chebyshevU_zero (x : ℝ) : chebyshevU 0 x = 1 := by
  simp [chebyshevU]

@[simp] theorem chebyshevU_one (x : ℝ) : chebyshevU 1 x = 2 * x := by
  simp [chebyshevU]

@[simp] theorem chebyshevU_neg_one (x : ℝ) : chebyshevU (-1) x = 0 := by
  simp [chebyshevU]

/-- The paper's three-term recurrence for the second-kind Chebyshev polynomials. -/
theorem chebyshevU_add_two (n : ℤ) (x : ℝ) :
    chebyshevU (n + 2) x = 2 * x * chebyshevU (n + 1) x - chebyshevU n x := by
  simp [chebyshevU, Polynomial.Chebyshev.U_add_two]

/-- A shifted form of the three-term recurrence. -/
theorem chebyshevU_add_one (n : ℤ) (x : ℝ) :
    chebyshevU (n + 1) x = 2 * x * chebyshevU n x - chebyshevU (n - 1) x := by
  simp [chebyshevU, Polynomial.Chebyshev.U_add_one]

/-- Trigonometric evaluation in a division-free form, valid also at the nodes. -/
theorem chebyshevU_cos_mul_sin (n : ℤ) (θ : ℝ) :
    chebyshevU n (Real.cos θ) * Real.sin θ = Real.sin ((n + 1) * θ) := by
  simp [chebyshevU]

/-- The interior nodal points `cos (kπ/(n+1))`, `1 ≤ k ≤ n`, are zeros of `Uₙ`. -/
theorem chebyshevU_nodal_zero {n k : ℕ} (hk₀ : 0 < k) (hkₙ : k ≤ n) :
    chebyshevU n (Real.cos (k * Real.pi / (n + 1))) = 0 := by
  have hden : (0 : ℝ) < n + 1 := by positivity
  have hangle_pos : (0 : ℝ) < k * Real.pi / (n + 1) := by positivity
  have hk_lt : (k : ℝ) < n + 1 := by exact_mod_cast Nat.lt_succ_of_le hkₙ
  have hangle_lt : (k : ℝ) * Real.pi / (n + 1) < Real.pi := by
    rw [div_lt_iff₀ hden]
    nlinarith [Real.pi_pos]
  have hsin_ne : Real.sin (k * Real.pi / (n + 1 : ℝ)) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hangle_pos hangle_lt).ne'
  refine (mul_eq_zero_iff_right hsin_ne).mp ?_
  rw [chebyshevU_cos_mul_sin]
  have harg :
      ((n : ℝ) + 1) * ((k : ℝ) * Real.pi / (n + 1 : ℝ)) =
        (k : ℝ) * Real.pi := by
    field_simp
  have harg' :
      (((n : ℤ) : ℝ) + 1) * ((k : ℝ) * Real.pi / (n + 1 : ℝ)) =
        (k : ℝ) * Real.pi := by
    simpa only [Int.cast_natCast] using harg
  rw [harg', Real.sin_nat_mul_pi]

/-- On the `k`-th open nodal interval, `Uₙ(cos θ)` has sign `(-1)ᵏ`. -/
theorem chebyshevU_signed_pos_between_nodes {n k : ℕ} (hk : k ≤ n) {θ : ℝ}
    (hleft : (k : ℝ) * Real.pi / (n + 1 : ℝ) < θ)
    (hright : θ < ((k + 1 : ℕ) : ℝ) * Real.pi / (n + 1 : ℝ)) :
    0 < (-1 : ℝ) ^ k * chebyshevU n (Real.cos θ) := by
  have hden : (0 : ℝ) < n + 1 := by positivity
  have hleft_nonneg :
      0 ≤ (k : ℝ) * Real.pi / (n + 1 : ℝ) := by positivity
  have hθpos : 0 < θ := lt_of_le_of_lt hleft_nonneg hleft
  have hk_succ : (k + 1 : ℕ) ≤ n + 1 := Nat.succ_le_succ hk
  have hk_succ_cast : ((k + 1 : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast hk_succ
  have hnode_le_pi :
      ((k + 1 : ℕ) : ℝ) * Real.pi / (n + 1 : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hden]
    nlinarith [Real.pi_pos]
  have hθpi : θ < Real.pi := lt_of_lt_of_le hright hnode_le_pi
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos hθpi
  let φ : ℝ := ((n : ℝ) + 1) * θ - (k : ℝ) * Real.pi
  have hscaled_left :
      (k : ℝ) * Real.pi < θ * (n + 1 : ℝ) :=
    (div_lt_iff₀ hden).mp hleft
  have hscaled_right :
      θ * (n + 1 : ℝ) < ((k + 1 : ℕ) : ℝ) * Real.pi :=
    (lt_div_iff₀ hden).mp hright
  have hφpos : 0 < φ := by
    dsimp [φ]
    nlinarith
  have hφpi : φ < Real.pi := by
    dsimp [φ]
    push_cast at hscaled_right
    nlinarith
  have hsinφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφpos hφpi
  have htrig :
      chebyshevU n (Real.cos θ) * Real.sin θ =
        Real.sin (((n : ℝ) + 1) * θ) := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using
      chebyshevU_cos_mul_sin (n : ℤ) θ
  have hdecomp :
      ((n : ℝ) + 1) * θ = φ + (k : ℝ) * Real.pi := by
    dsimp [φ]
    ring
  have hsin_decomp :
      Real.sin (((n : ℝ) + 1) * θ) = (-1 : ℝ) ^ k * Real.sin φ := by
    rw [hdecomp, Real.sin_add_nat_mul_pi]
  have hsign_sq : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have hprod :
      ((-1 : ℝ) ^ k * chebyshevU n (Real.cos θ)) * Real.sin θ = Real.sin φ := by
    calc
      ((-1 : ℝ) ^ k * chebyshevU n (Real.cos θ)) * Real.sin θ =
          (-1 : ℝ) ^ k *
            (chebyshevU n (Real.cos θ) * Real.sin θ) := by ring
      _ = (-1 : ℝ) ^ k * Real.sin (((n : ℝ) + 1) * θ) := by rw [htrig]
      _ = (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * Real.sin φ) := by rw [hsin_decomp]
      _ = ((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * Real.sin φ := by ring
      _ = Real.sin φ := by rw [hsign_sq, one_mul]
  have hprod_pos :
      0 < ((-1 : ℝ) ^ k * chebyshevU n (Real.cos θ)) * Real.sin θ := by
    rw [hprod]
    exact hsinφ
  exact pos_of_mul_pos_left hprod_pos hsinθ.le

/-- The two polynomial half-angle identities, bundled for their simultaneous induction proof. -/
theorem chebyshevU_half_angle_pair (m : ℕ) (t : ℝ) :
    chebyshevU m (2 * t ^ 2 - 1) + chebyshevU ((m : ℤ) - 1) (2 * t ^ 2 - 1) =
        chebyshevU (2 * m) t ∧
      2 * t * chebyshevU m (2 * t ^ 2 - 1) = chebyshevU (2 * m + 1) t := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      simp only [Nat.cast_succ]
      ring_nf
      rcases ih with ⟨ihEven, ihOdd⟩
      have hstep := chebyshevU_add_one (m : ℤ) (2 * t ^ 2 - 1)
      have hEven := chebyshevU_add_two (2 * (m : ℤ)) t
      have hOdd := chebyshevU_add_two (2 * (m : ℤ) + 1) t
      ring_nf at ihEven ihOdd hstep hEven hOdd
      constructor
      · rw [hstep, hEven]
        linear_combination (norm := ring_nf) 2 * t * ihOdd - ihEven
      · rw [hstep, hOdd, hEven]
        linear_combination (norm := ring_nf) (4 * t ^ 2 - 1) * ihOdd - 2 * t * ihEven

/-- The half-angle identity used for an odd folded size `K = 2m + 1`. -/
theorem chebyshevU_half_angle_even_index (m : ℕ) (t : ℝ) :
    chebyshevU m (2 * t ^ 2 - 1) + chebyshevU ((m : ℤ) - 1) (2 * t ^ 2 - 1) =
      chebyshevU (2 * m) t :=
  (chebyshevU_half_angle_pair m t).1

/-- The denominator-free half-angle identity used for an even folded size `K = 2m + 2`.
This polynomial form also records the continuous interpretation at `t = 0`. -/
theorem chebyshevU_half_angle_odd_index_mul (m : ℕ) (t : ℝ) :
    2 * t * chebyshevU m (2 * t ^ 2 - 1) = chebyshevU (2 * m + 1) t :=
  (chebyshevU_half_angle_pair m t).2

/-- Away from `t = 0`, the even-fold half-angle identity in the quotient form printed in the
paper. -/
theorem chebyshevU_half_angle_odd_index (m : ℕ) {t : ℝ} (ht : t ≠ 0) :
    chebyshevU m (2 * t ^ 2 - 1) = chebyshevU (2 * m + 1) t / (2 * t) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) ht)).2
  simpa [mul_comm] using chebyshevU_half_angle_odd_index_mul m t

end

end ConnectedPseudospectrum
