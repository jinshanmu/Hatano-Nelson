import ConnectedPseudospectrum.JordanBoundary
import ConnectedPseudospectrum.NormalToeplitzBoundary

/-!
# Full complex tridiagonal Toeplitz classification

This module is the literal top-level formal counterpart of `thm:main` in the
ELA manuscript.  It packages the reducible, irreducible nonnormal, and normal
regimes behind the paper's piecewise threshold `Theta_n` and critical order
`N_T`.
-/

namespace ConnectedPseudospectrum

open Filter Set

noncomputable section

/-- The full-family connectedness threshold `Theta_n(alpha,beta)` from
`eq:full-threshold`. -/
def complexToeplitzThreshold (n : ℕ) (α β : ℂ) : ℝ :=
  if α * β = 0 then
    0
  else if ‖α‖ = ‖β‖ then
    max ‖α‖ ‖β‖ * normalThreshold n
  else
    max ‖α‖ ‖β‖ *
      gapBarrier n (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖)

/-- The piecewise scalar representative of the first connected order
`N_T(alpha,beta;epsilon)`.  The `IsLeast` theorem below proves that this
wrapper is literally the minimum in the manuscript. -/
def complexToeplitzCriticalSize (α β : ℂ) (ε : ℝ) : ℕ :=
  if α * β = 0 then
    2
  else if ‖α‖ = ‖β‖ then
    normalCriticalThreshold (max ‖α‖ ‖β‖) ε
  else
    criticalThreshold (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖)
      (ε / max ‖α‖ ‖β‖)

/-- Matrix orders at which the full complex Toeplitz pseudospectrum is
connected. -/
def complexToeplitzConnectedDimensions (α d β : ℂ) (ε : ℝ) : Set ℕ :=
  {n | 2 ≤ n ∧
    IsConnected
      (generalPseudospectrum (complexToeplitzMatrix n α d β) ε)}

private theorem left_ne_zero_of_mul_ne_zero {α β : ℂ}
    (h : α * β ≠ 0) : α ≠ 0 := by
  intro hα
  exact h (by simp [hα])

private theorem right_ne_zero_of_mul_ne_zero {α β : ℂ}
    (h : α * β ≠ 0) : β ≠ 0 := by
  intro hβ
  exact h (by simp [hβ])

private theorem max_norm_pos_of_mul_ne_zero {α β : ℂ}
    (h : α * β ≠ 0) : 0 < max ‖α‖ ‖β‖ := by
  exact lt_max_iff.mpr
    (Or.inl (norm_pos_iff.mpr (left_ne_zero_of_mul_ne_zero h)))

private theorem normalized_modulus_pos_of_mul_ne_zero {α β : ℂ}
    (h : α * β ≠ 0) :
    0 < min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖ := by
  have hα : 0 < ‖α‖ :=
    norm_pos_iff.mpr (left_ne_zero_of_mul_ne_zero h)
  have hβ : 0 < ‖β‖ :=
    norm_pos_iff.mpr (right_ne_zero_of_mul_ne_zero h)
  exact div_pos (lt_min hα hβ) (max_norm_pos_of_mul_ne_zero h)

private theorem normalized_modulus_lt_one_of_norm_ne
    {α β : ℂ} (h : α * β ≠ 0) (hneq : ‖α‖ ≠ ‖β‖) :
    min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖ < 1 := by
  have hminmax : min ‖α‖ ‖β‖ < max ‖α‖ ‖β‖ := by
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · simpa [min_eq_left hlt.le, max_eq_right hlt.le] using hlt
    · simpa [min_eq_right hgt.le, max_eq_left hgt.le] using hgt
  exact (div_lt_one (max_norm_pos_of_mul_ne_zero h)).2 hminmax

/-- Exact fixed-order component topology and connectedness criterion in all
three parameter regimes. -/
theorem complexToeplitz_classification_at_size
    (n : ℕ) (hn : 2 ≤ n) (α d β : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∀ {z : ℂ},
      z ∈ generalPseudospectrum (complexToeplitzMatrix n α d β) ε →
        ContractibleSpace
          (connectedComponentIn
            (generalPseudospectrum (complexToeplitzMatrix n α d β) ε) z)) ∧
    (IsConnected
        (generalPseudospectrum (complexToeplitzMatrix n α d β) ε) ↔
      ε > complexToeplitzThreshold n α β) := by
  by_cases hzero : α * β = 0
  · let Ω : Set ℂ :=
      generalPseudospectrum (complexToeplitzMatrix n α d β) ε
    have hconnected : IsConnected Ω :=
      isConnected_complexToeplitzPseudospectrum_of_mul_eq_zero
        n (by omega) α d β hzero hε
    have hwhole : ContractibleSpace Ω :=
      contractibleSpace_complexToeplitzPseudospectrum_of_mul_eq_zero
        n (by omega) α d β hzero hε
    constructor
    · intro z hz
      letI : ContractibleSpace Ω := hwhole
      have hsubset : Ω ⊆ connectedComponentIn Ω z :=
        hconnected.2.subset_connectedComponentIn hz (Subset.rfl)
      have heq : connectedComponentIn Ω z = Ω :=
        (connectedComponentIn_subset Ω z).antisymm hsubset
      exact (Homeomorph.setCongr heq).contractibleSpace
    · simpa [Ω, complexToeplitzThreshold, hzero] using
        (iff_of_true hconnected hε)
  · have hα : α ≠ 0 := left_ne_zero_of_mul_ne_zero hzero
    have hβ : β ≠ 0 := right_ne_zero_of_mul_ne_zero hzero
    by_cases heq : ‖α‖ = ‖β‖
    · simpa [complexToeplitzThreshold, hzero, heq] using
        (complexToeplitz_normal_corollary n hn d hα hβ heq hε)
    · simpa [complexToeplitzThreshold, hzero, heq] using
        (complexToeplitz_corollary n hn d hα hβ heq hε)

/-- In every irreducible regime, including the normal boundary, the physical
threshold decreases strictly at each adjacent matrix order. -/
theorem complexToeplitzThreshold_succ_lt_of_mul_ne_zero
    {α β : ℂ} (hzero : α * β ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    complexToeplitzThreshold (n + 1) α β <
      complexToeplitzThreshold n α β := by
  have hc : 0 < max ‖α‖ ‖β‖ := max_norm_pos_of_mul_ne_zero hzero
  by_cases heq : ‖α‖ = ‖β‖
  · have hstrict :=
      mul_lt_mul_of_pos_left (normalThreshold_succ_lt n hn) hc
    simpa [complexToeplitzThreshold, hzero, heq] using hstrict
  · have hα : α ≠ 0 := left_ne_zero_of_mul_ne_zero hzero
    have hβ : β ≠ 0 := right_ne_zero_of_mul_ne_zero hzero
    simpa [complexToeplitzThreshold, hzero, heq] using
      (complexToeplitz_scaled_barrier_succ_lt hα hβ heq hn)

/-- The normal endpoint threshold is nonnegative in every dimension. -/
theorem normalThreshold_nonneg (n : ℕ) : 0 ≤ normalThreshold n := by
  by_cases heven : Even n
  · rw [normalThreshold, if_pos heven]
    apply mul_nonneg (by norm_num)
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · have hden : 0 < 2 * (n + 1 : ℝ) := by positivity
      apply (div_le_iff₀ hden).2
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [Real.pi_pos]
  · rw [normalThreshold, if_neg heven]
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · have hden : 0 < (n + 1 : ℝ) := by positivity
      apply (div_le_iff₀ hden).2
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith [Real.pi_pos]

/-- The algebraically decaying normal threshold tends to zero. -/
theorem tendsto_normalThreshold_atTop_zero :
    Tendsto normalThreshold atTop (nhds 0) := by
  apply squeeze_zero'
    (g := fun n : ℕ => Real.pi / (n + 1 : ℝ))
  · exact Filter.Eventually.of_forall normalThreshold_nonneg
  · filter_upwards [] with n
    linarith [(normalThreshold_error_bound n).1]
  · simpa [div_eq_mul_inv] using
      (tendsto_const_nhds (x := Real.pi)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The full piecewise physical threshold tends to zero in all three
regimes. -/
theorem tendsto_complexToeplitzThreshold_atTop_zero (α β : ℂ) :
    Tendsto (fun n : ℕ => complexToeplitzThreshold n α β)
      atTop (nhds 0) := by
  by_cases hzero : α * β = 0
  · simp [complexToeplitzThreshold, hzero]
  · by_cases heq : ‖α‖ = ‖β‖
    · simpa [complexToeplitzThreshold, hzero, heq] using
        (tendsto_const_nhds (x := max ‖α‖ ‖β‖)).mul
          tendsto_normalThreshold_atTop_zero
    · have ha0 := normalized_modulus_pos_of_mul_ne_zero hzero
      have ha1 := normalized_modulus_lt_one_of_norm_ne hzero heq
      simpa [complexToeplitzThreshold, hzero, heq] using
        (tendsto_const_nhds (x := max ‖α‖ ‖β‖)).mul
          (tendsto_gapBarrier_atTop_zero
            (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖) ha0 ha1)

/-- The nonnormal complex family's connected dimensions form the canonical
critical tail after the physical rescaling `epsilon -> epsilon / c`. -/
theorem complexToeplitz_nonnormal_connectedDimensions_eq_tail
    {α β : ℂ} (d : ℂ) (hzero : α * β ≠ 0)
    (hneq : ‖α‖ ≠ ‖β‖) {ε : ℝ} (hε : 0 < ε) :
    complexToeplitzConnectedDimensions α d β ε =
      {n : ℕ |
        criticalThreshold (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖)
          (ε / max ‖α‖ ‖β‖) ≤ n} := by
  have hα : α ≠ 0 := left_ne_zero_of_mul_ne_zero hzero
  have hc : 0 < max ‖α‖ ‖β‖ := max_norm_pos_of_mul_ne_zero hzero
  have ha0 := normalized_modulus_pos_of_mul_ne_zero hzero
  have ha1 := normalized_modulus_lt_one_of_norm_ne hzero hneq
  have hεc : 0 < ε / max ‖α‖ ‖β‖ := div_pos hε hc
  have hcriterion : ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖)
          (ε / max ‖α‖ ‖β‖) ↔
        gapBarrier n (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖) <
          ε / max ‖α‖ ‖β‖) := by
    intro n hn
    exact isConnected_pathPseudospectrum_iff_gapBarrier_lt
      n hn ha0 ha1 hεc
  have hstrict : ∀ {n : ℕ}, 2 ≤ n →
      gapBarrier (n + 1) (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖) <
        gapBarrier n (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖) := by
    intro n hn
    exact gapBarrier_succ_lt n hn ha0 ha1
  rw [← connectedDimensions_eq_criticalThreshold_tail
    ha0 ha1 hεc hcriterion hstrict]
  ext n
  simp only [complexToeplitzConnectedDimensions, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hn, hconnected⟩
    refine ⟨hn, ?_⟩
    rw [complexToeplitzPseudospectrum_eq_affine_image
      n d (Or.inl hα) ε] at hconnected
    exact ((complexAffineHomeomorph (complexToeplitzScale α β) d
      (complexToeplitzScale_ne_zero (Or.inl hα))).isConnected_image).1
        hconnected
  · rintro ⟨hn, hconnected⟩
    refine ⟨hn, ?_⟩
    rw [complexToeplitzPseudospectrum_eq_affine_image
      n d (Or.inl hα) ε]
    exact ((complexAffineHomeomorph (complexToeplitzScale α β) d
      (complexToeplitzScale_ne_zero (Or.inl hα))).isConnected_image).2
        hconnected

/-- The normal complex family's connected dimensions are the exact tail
beginning at `normalCriticalThreshold`. -/
theorem complexToeplitz_normal_connectedDimensions_eq_tail
    {α β : ℂ} (d : ℂ) (hzero : α * β ≠ 0)
    (heq : ‖α‖ = ‖β‖) {ε : ℝ} (hε : 0 < ε) :
    complexToeplitzConnectedDimensions α d β ε =
      {n : ℕ | normalCriticalThreshold (max ‖α‖ ‖β‖) ε ≤ n} := by
  have hα : α ≠ 0 := left_ne_zero_of_mul_ne_zero hzero
  have hβ : β ≠ 0 := right_ne_zero_of_mul_ne_zero hzero
  have hc : 0 < max ‖α‖ ‖β‖ := max_norm_pos_of_mul_ne_zero hzero
  rw [show max ‖α‖ ‖β‖ = ‖α‖ by simp [heq]]
  change {n : ℕ | 2 ≤ n ∧
      IsConnected
        (generalPseudospectrum (complexToeplitzMatrix n α d β) ε)} = _
  rw [complexToeplitz_normal_connectedDimensions_eq_normalCriticalSet
    d hα hβ heq hε]
  ext n
  constructor
  · exact fun hn => normalCriticalThreshold_le hn
  · intro hn
    exact normalCriticalSet_of_threshold_le
      (by simpa [heq] using hc) hε hn

/-- In the zero-product regime every order `n >= 2` is connected. -/
theorem complexToeplitz_zero_connectedDimensions_eq_tail
    {α β : ℂ} (d : ℂ) (hzero : α * β = 0)
    {ε : ℝ} (hε : 0 < ε) :
    complexToeplitzConnectedDimensions α d β ε =
      {n : ℕ | 2 ≤ n} := by
  ext n
  simp only [complexToeplitzConnectedDimensions, Set.mem_setOf_eq]
  constructor
  · exact fun hn => hn.1
  · intro hn
    exact ⟨hn,
      isConnected_complexToeplitzPseudospectrum_of_mul_eq_zero
        n (by omega) α d β hzero hε⟩

/-- The connected matrix orders are exactly the tail beginning at the
piecewise full-family critical size. -/
theorem complexToeplitz_connectedDimensions_eq_criticalSize_tail
    (α d β : ℂ) {ε : ℝ} (hε : 0 < ε) :
    complexToeplitzConnectedDimensions α d β ε =
      {n : ℕ | complexToeplitzCriticalSize α β ε ≤ n} := by
  by_cases hzero : α * β = 0
  · simpa [complexToeplitzCriticalSize, hzero] using
      (complexToeplitz_zero_connectedDimensions_eq_tail d hzero hε)
  · by_cases heq : ‖α‖ = ‖β‖
    · simpa [complexToeplitzCriticalSize, hzero, heq] using
        (complexToeplitz_normal_connectedDimensions_eq_tail d hzero heq hε)
    · simpa [complexToeplitzCriticalSize, hzero, heq] using
        (complexToeplitz_nonnormal_connectedDimensions_eq_tail
          d hzero heq hε)

/-- The piecewise wrapper is literally the first connected matrix order,
which is the formal specification of `N_T`. -/
theorem complexToeplitz_firstConnectedDimension_isLeast
    (α d β : ℂ) {ε : ℝ} (hε : 0 < ε) :
    IsLeast (complexToeplitzConnectedDimensions α d β ε)
      (complexToeplitzCriticalSize α β ε) := by
  rw [complexToeplitz_connectedDimensions_eq_criticalSize_tail α d β hε]
  exact ⟨by simp, fun _ hn => hn⟩

@[simp] theorem complexToeplitzCriticalSize_of_mul_eq_zero
    {α β : ℂ} (hzero : α * β = 0) (ε : ℝ) :
    complexToeplitzCriticalSize α β ε = 2 := by
  simp [complexToeplitzCriticalSize, hzero]

theorem complexToeplitzCriticalSize_of_norm_eq
    {α β : ℂ} (hzero : α * β ≠ 0) (heq : ‖α‖ = ‖β‖) (ε : ℝ) :
    complexToeplitzCriticalSize α β ε =
      normalCriticalThreshold (max ‖α‖ ‖β‖) ε := by
  simp [complexToeplitzCriticalSize, hzero, heq]

theorem complexToeplitzCriticalSize_of_norm_ne
    {α β : ℂ} (hzero : α * β ≠ 0) (hneq : ‖α‖ ≠ ‖β‖) (ε : ℝ) :
    complexToeplitzCriticalSize α β ε =
      criticalThreshold (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖)
        (ε / max ‖α‖ ‖β‖) := by
  simp [complexToeplitzCriticalSize, hzero, hneq]

/-- Exact scaled bounded-error form of `eq:general-nonnormal-critical`.
Unlike the unscaled stability corollary, the comparison function retains
`epsilon / c`, hence exactly retains `log(c/epsilon)` in the displayed
asymptotic. -/
theorem criticalThreshold_div_boundedErrorAtZero_scaled
    {a c : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hc : 0 < c) :
    BoundedErrorAtZero
      (fun ε : ℝ => (criticalThreshold a (ε / c) : ℝ))
      (fun ε : ℝ => criticalScale a (ε / c)) := by
  have hbase : HasCriticalSizeAsymptotic (criticalThreshold a) a :=
    (main_theorem ha0 ha1 zero_lt_one).2.2.2.1
  unfold HasCriticalSizeAsymptotic at hbase
  simpa only [div_eq_mul_inv, mul_comm] using
    hbase.comp_pos_mul (inv_pos.mpr hc)

/-- The full-family critical wrapper satisfies the manuscript's exact scaled
nonnormal critical-order law. -/
theorem complexToeplitzCriticalSize_boundedErrorAtZero_of_norm_ne
    {α β : ℂ} (hzero : α * β ≠ 0) (hneq : ‖α‖ ≠ ‖β‖) :
    BoundedErrorAtZero
      (fun ε : ℝ => (complexToeplitzCriticalSize α β ε : ℝ))
      (fun ε : ℝ =>
        criticalScale (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖)
          (ε / max ‖α‖ ‖β‖)) := by
  simpa [complexToeplitzCriticalSize, hzero, hneq] using
    (criticalThreshold_div_boundedErrorAtZero_scaled
      (normalized_modulus_pos_of_mul_ne_zero hzero)
      (normalized_modulus_lt_one_of_norm_ne hzero hneq)
      (max_norm_pos_of_mul_ne_zero hzero))

/-- The full-family critical wrapper satisfies the normal
`pi*c/epsilon + O(1)` law. -/
theorem complexToeplitzCriticalSize_boundedErrorAtZero_of_norm_eq
    {α β : ℂ} (hzero : α * β ≠ 0) (heq : ‖α‖ = ‖β‖) :
    BoundedErrorAtZero
      (fun ε : ℝ => (complexToeplitzCriticalSize α β ε : ℝ))
      (fun ε : ℝ => Real.pi * max ‖α‖ ‖β‖ / ε) := by
  simpa [complexToeplitzCriticalSize, hzero, heq] using
    (normalCriticalThreshold_boundedErrorAtZero
      (max_norm_pos_of_mul_ne_zero hzero))

/-- Complete kernel-checked assembly of all three branches of the ELA
complex tridiagonal Toeplitz classification `thm:main`. -/
theorem complexToeplitz_main_theorem
    (α d β : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∀ (n : ℕ), 2 ≤ n → ∀ {z : ℂ},
      z ∈ generalPseudospectrum (complexToeplitzMatrix n α d β) ε →
        ContractibleSpace
          (connectedComponentIn
            (generalPseudospectrum (complexToeplitzMatrix n α d β) ε) z)) ∧
    (∀ (n : ℕ), 2 ≤ n →
      (IsConnected
          (generalPseudospectrum (complexToeplitzMatrix n α d β) ε) ↔
        ε > complexToeplitzThreshold n α β)) ∧
    Tendsto (fun n : ℕ => complexToeplitzThreshold n α β)
      atTop (nhds 0) ∧
    ((α * β ≠ 0 → ∀ (n : ℕ), 2 ≤ n →
        complexToeplitzThreshold (n + 1) α β <
          complexToeplitzThreshold n α β) ∧
      (α * β = 0 → ∀ n : ℕ,
        complexToeplitzThreshold n α β = 0)) ∧
    (complexToeplitzConnectedDimensions α d β ε =
      {n : ℕ | complexToeplitzCriticalSize α β ε ≤ n}) ∧
    IsLeast (complexToeplitzConnectedDimensions α d β ε)
      (complexToeplitzCriticalSize α β ε) ∧
    ((α * β = 0 → complexToeplitzCriticalSize α β ε = 2) ∧
      (α * β ≠ 0 ∧ ‖α‖ ≠ ‖β‖ →
        complexToeplitzCriticalSize α β ε =
            criticalThreshold (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖)
              (ε / max ‖α‖ ‖β‖) ∧
          BoundedErrorAtZero
            (fun δ : ℝ => (complexToeplitzCriticalSize α β δ : ℝ))
            (fun δ : ℝ =>
              criticalScale (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖)
                (δ / max ‖α‖ ‖β‖))) ∧
      (α * β ≠ 0 ∧ ‖α‖ = ‖β‖ →
        complexToeplitzCriticalSize α β ε =
            normalCriticalThreshold (max ‖α‖ ‖β‖) ε ∧
          BoundedErrorAtZero
            (fun δ : ℝ => (complexToeplitzCriticalSize α β δ : ℝ))
            (fun δ : ℝ => Real.pi * max ‖α‖ ‖β‖ / δ))) := by
  refine ⟨?_, ?_, tendsto_complexToeplitzThreshold_atTop_zero α β,
    ?_, complexToeplitz_connectedDimensions_eq_criticalSize_tail α d β hε,
    complexToeplitz_firstConnectedDimension_isLeast α d β hε, ?_⟩
  · intro n hn z hz
    exact (complexToeplitz_classification_at_size n hn α d β hε).1 hz
  · intro n hn
    exact (complexToeplitz_classification_at_size n hn α d β hε).2
  · constructor
    · intro hzero n hn
      exact complexToeplitzThreshold_succ_lt_of_mul_ne_zero hzero hn
    · intro hzero n
      simp [complexToeplitzThreshold, hzero]
  · exact ⟨
      fun hzero => complexToeplitzCriticalSize_of_mul_eq_zero hzero ε,
      fun h => ⟨complexToeplitzCriticalSize_of_norm_ne h.1 h.2 ε,
        complexToeplitzCriticalSize_boundedErrorAtZero_of_norm_ne h.1 h.2⟩,
      fun h => ⟨complexToeplitzCriticalSize_of_norm_eq h.1 h.2 ε,
        complexToeplitzCriticalSize_boundedErrorAtZero_of_norm_eq h.1 h.2⟩⟩

end

end ConnectedPseudospectrum
