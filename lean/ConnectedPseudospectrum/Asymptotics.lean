import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounded-error notation at the small-pseudospectrum limit

The paper's `O_a(1)` is encoded pointwise in the fixed parameter `a`: the
error is uniformly bounded for all sufficiently small positive `ε`, while
both the bound and the cutoff may depend on `a`.
-/

namespace ConnectedPseudospectrum

/-- `f(ε) = g(ε) + O(1)` as `ε ↓ 0`, expressed without asymptotic notation. -/
def BoundedErrorAtZero (f g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → |f ε - g ε| ≤ C

/-- The logarithmic--logarithmic scale in `eq:N-asymptotic-main`. -/
noncomputable def criticalScale (a ε : ℝ) : ℝ :=
  2 / Real.log (1 / a) *
    (Real.log (1 / ε) + Real.log (Real.log (1 / ε)))

/-- Precise bounded-error form of the paper's fixed-`a` critical-size
asymptotic.  The natural-valued threshold is coerced to `ℝ`. -/
def HasCriticalSizeAsymptotic (criticalSize : ℝ → ℕ) (a : ℝ) : Prop :=
  BoundedErrorAtZero (fun ε => (criticalSize ε : ℝ)) (criticalScale a)

theorem boundedErrorAtZero_refl (f : ℝ → ℝ) :
    BoundedErrorAtZero f f := by
  refine ⟨0, le_rfl, 1, zero_lt_one, ?_⟩
  intro ε hε hε₀
  simp

theorem BoundedErrorAtZero.symm {f g : ℝ → ℝ}
    (h : BoundedErrorAtZero f g) :
    BoundedErrorAtZero g f := by
  obtain ⟨C, hC, ε₀, hε₀, hbound⟩ := h
  refine ⟨C, hC, ε₀, hε₀, ?_⟩
  intro ε hε hsmall
  simpa only [abs_sub_comm] using hbound ε hε hsmall

theorem BoundedErrorAtZero.trans {f g h : ℝ → ℝ}
    (hfg : BoundedErrorAtZero f g) (hgh : BoundedErrorAtZero g h) :
    BoundedErrorAtZero f h := by
  obtain ⟨C₁, hC₁, ε₁, hε₁, hbound₁⟩ := hfg
  obtain ⟨C₂, hC₂, ε₂, hε₂, hbound₂⟩ := hgh
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, min ε₁ ε₂,
    lt_min hε₁ hε₂, ?_⟩
  intro ε hε hsmall
  have hsmall₁ : ε < ε₁ := hsmall.trans_le (min_le_left ε₁ ε₂)
  have hsmall₂ : ε < ε₂ := hsmall.trans_le (min_le_right ε₁ ε₂)
  calc
    |f ε - h ε| = |(f ε - g ε) + (g ε - h ε)| := by
      rw [sub_add_sub_cancel]
    _ ≤ |f ε - g ε| + |g ε - h ε| := abs_add_le _ _
    _ ≤ C₁ + C₂ := add_le_add (hbound₁ ε hε hsmall₁) (hbound₂ ε hε hsmall₂)

theorem BoundedErrorAtZero.add_same {f g : ℝ → ℝ}
    (h : BoundedErrorAtZero f g) (k : ℝ → ℝ) :
    BoundedErrorAtZero (fun ε => f ε + k ε) (fun ε => g ε + k ε) := by
  obtain ⟨C, hC, ε₀, hε₀, hbound⟩ := h
  refine ⟨C, hC, ε₀, hε₀, ?_⟩
  intro ε hε hsmall
  simpa only [add_sub_add_right_eq_sub] using hbound ε hε hsmall

theorem boundedErrorAtZero_add_const (f : ℝ → ℝ) (c : ℝ) :
    BoundedErrorAtZero (fun ε => f ε + c) f := by
  refine ⟨|c|, abs_nonneg c, 1, zero_lt_one, ?_⟩
  intro ε hε hsmall
  simp

theorem BoundedErrorAtZero.const_mul {f g : ℝ → ℝ}
    (h : BoundedErrorAtZero f g) (c : ℝ) :
    BoundedErrorAtZero (fun ε => c * f ε) (fun ε => c * g ε) := by
  obtain ⟨C, hC, ε₀, hε₀, hbound⟩ := h
  refine ⟨|c| * C, mul_nonneg (abs_nonneg c) hC, ε₀, hε₀, ?_⟩
  intro ε hε hsmall
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (hbound ε hε hsmall) (abs_nonneg c)

theorem log_one_div_pos {a : ℝ} (ha : 0 < a) (ha₁ : a < 1) :
    0 < Real.log (1 / a) := by
  apply Real.log_pos
  rw [one_div]
  exact (one_lt_inv₀ ha).2 ha₁

/-- A logarithmic sandwich determines its inverse up to a bounded error.
The first estimate gives `x` comparable to `y`; substituting this into the
same sandwich then replaces `log x` by `log y`. -/
theorem logarithmic_sandwich_bounded_error {β : ℝ} (hβ : 0 < β)
    (d e : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y : ℝ, ∀ x y : ℝ,
      1 ≤ x → Y ≤ y →
      y + Real.log x + d ≤ β * x →
      β * x ≤ y + Real.log x + e →
      |x - (y + Real.log y) / β| ≤ C := by
  let k := β / 2
  let α := 1 / (2 * β)
  let K := 4 / β
  have hk : 0 < k := by dsimp [k]; positivity
  have hα : 0 < α := by dsimp [α]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hβα : β * α = 1 / 2 := by
    dsimp [α]
    field_simp
  have hkK : k * K = 2 := by
    dsimp [k, K]
    field_simp
    norm_num
  let A := |Real.log k| + |e| + 1
  let B := |d + Real.log α| + |e + Real.log K|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B / β, div_nonneg hB hβ.le, max 1 (max A (2 * |d|)), ?_⟩
  intro x y hx hy hl hu
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hyone : 1 ≤ y := (le_max_left _ _).trans hy
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hyone
  have hAy : A ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hdy : 2 * |d| ≤ y := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  have hlog : Real.log x ≤ k * x + |Real.log k| := by
    have h := Real.log_le_sub_one_of_pos (mul_pos hk hxpos)
    rw [Real.log_mul hk.ne' hxpos.ne'] at h
    linarith [neg_abs_le (Real.log k)]
  have hlow : α * y ≤ x := by
    have := Real.log_nonneg hx
    have hd := neg_abs_le d
    have hprod : β * (α * y) = y / 2 := by rw [← mul_assoc, hβα]; ring
    apply (mul_le_mul_iff_right₀ hβ).mp
    nlinarith
  have hupp : x ≤ K * y := by
    have he := le_abs_self e
    have hprod : k * (K * y) = 2 * y := by rw [← mul_assoc, hkK]
    apply (mul_le_mul_iff_right₀ hk).mp
    dsimp only [k, A] at *
    nlinarith
  have hlogLow : Real.log y + Real.log α ≤ Real.log x := by
    have h := Real.log_le_log (mul_pos hα hypos) hlow
    rw [Real.log_mul hα.ne' hypos.ne'] at h
    linarith
  have hlogUpp : Real.log x ≤ Real.log y + Real.log K := by
    have h := Real.log_le_log hxpos hupp
    rw [Real.log_mul hK.ne' hypos.ne'] at h
    linarith
  have hres : |β * x - (y + Real.log y)| ≤ B := by
    rw [abs_le]
    dsimp only [B]
    constructor
    · linarith [neg_abs_le (d + Real.log α), abs_nonneg (e + Real.log K)]
    · linarith [le_abs_self (e + Real.log K), abs_nonneg (d + Real.log α)]
  have hid : x - (y + Real.log y) / β =
      (β * x - (y + Real.log y)) / β := by
    field_simp
  rw [hid, abs_div, abs_of_pos hβ]
  exact div_le_div_of_nonneg_right hres hβ.le

end ConnectedPseudospectrum
