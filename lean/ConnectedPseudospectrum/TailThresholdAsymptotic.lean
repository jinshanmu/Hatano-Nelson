import ConnectedPseudospectrum.Asymptotics
import ConnectedPseudospectrum.GapDecay

/-!
# Elementary inversion of the geometric tail threshold

This module formalizes the paper's scalar tail model
`Θₙ(r) = (n+1) rⁿ` and its first permanent crossing below a positive
level by direct logarithmic estimates.
-/

namespace ConnectedPseudospectrum

open Filter Set

noncomputable section

/-- The scalar geometric tail model `Θₙ(r)=(n+1)rⁿ`. -/
def tailModel (r : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * r ^ n

/-- `N` is a valid permanent tail crossing for the level `t`. -/
def TailAdmissible (r t : ℝ) (N : ℕ) : Prop :=
  2 ≤ N ∧ ∀ m : ℕ, N ≤ m → tailModel r m < t

/-- The first index at least two after which the whole model tail lies
strictly below `t`.  Its defining set is proved nonempty for `0<r<1` and
`t>0` below. -/
def tailThreshold (r t : ℝ) : ℕ :=
  sInf {N : ℕ | TailAdmissible r t N}

/-- The geometric tail model tends to zero when `0≤r<1`. -/
theorem tendsto_tailModel_atTop_zero {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Tendsto (tailModel r) atTop (nhds 0) := by
  have hself : Tendsto (fun n : ℕ => (n : ℝ) * r ^ n) atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have hpow : Tendsto (fun n : ℕ => r ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hsum :
      Tendsto (fun n : ℕ => (n : ℝ) * r ^ n + r ^ n) atTop (nhds 0) := by
    simpa using hself.add hpow
  apply hsum.congr'
  filter_upwards [] with n
  simp only [tailModel, Nat.cast_add, Nat.cast_one]
  ring

/-- The set defining `tailThreshold` is nonempty under the paper's parameter
hypotheses. -/
theorem nonempty_tailAdmissible {r t : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ht : 0 < t) :
    {N : ℕ | TailAdmissible r t N}.Nonempty := by
  have hevent : ∀ᶠ n : ℕ in atTop, tailModel r n < t :=
    (tendsto_order.1 (tendsto_tailModel_atTop_zero hr0 hr1)).2 t ht
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hevent)
  refine ⟨max 2 N, le_max_left 2 N, ?_⟩
  intro m hm
  exact hN m ((le_max_right 2 N).trans hm)

/-- The selected threshold is itself admissible. -/
theorem tailThreshold_admissible {r t : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ht : 0 < t) :
    TailAdmissible r t (tailThreshold r t) := by
  exact Nat.sInf_mem (nonempty_tailAdmissible hr0 hr1 ht)

theorem two_le_tailThreshold {r t : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ht : 0 < t) :
    2 ≤ tailThreshold r t :=
  (tailThreshold_admissible hr0 hr1 ht).1

/-- Every admissible tail index bounds the selected threshold from above. -/
theorem tailThreshold_le_of_admissible {r t : ℝ} {N : ℕ}
    (hN : TailAdmissible r t N) :
    tailThreshold r t ≤ N := by
  exact Nat.sInf_le hN

/-- A failed point at `m` rules out every candidate no larger than `m`. -/
theorem lt_tailThreshold_of_model_ge {r t : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (ht : 0 < t)
    {m : ℕ} (hm : t ≤ tailModel r m) :
    m < tailThreshold r t := by
  have hT := tailThreshold_admissible hr0 hr1 ht
  by_contra hnot
  have hle : tailThreshold r t ≤ m := Nat.le_of_not_gt hnot
  exact (not_lt_of_ge hm) (hT.2 m hle)

/-- One-step decrease criterion for the geometric tail model. -/
theorem tailModel_succ_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    {n : ℕ} (hn : r / (1 - r) ≤ (n + 1 : ℝ)) :
    tailModel r (n + 1) ≤ tailModel r n := by
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  have hbase : r ≤ (n + 1 : ℝ) * (1 - r) :=
    (div_le_iff₀ hden).1 hn
  have hcoef : ((n + 2 : ℕ) : ℝ) * r ≤ ((n + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hr0 n)
  unfold tailModel
  rw [pow_succ]
  convert hmul using 1
  · push_cast
    ring

/-- Beyond any index satisfying the ratio cutoff, the model is antitone. -/
theorem antitoneOn_tailModel_Ici (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    {K : ℕ} (hK : r / (1 - r) ≤ (K + 1 : ℝ)) :
    AntitoneOn (tailModel r) (Ici K) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  apply tailModel_succ_le r hr0 hr1
  exact hK.trans (by exact_mod_cast Nat.add_le_add_right hn 1)

/-- Once the model is in its decreasing tail, a single strict crossing makes
the index admissible. -/
theorem tailAdmissible_of_cutoff_of_model_lt {r t : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) {N : ℕ}
    (hN2 : 2 ≤ N) (hcut : r / (1 - r) ≤ (N + 1 : ℝ))
    (hmodel : tailModel r N < t) :
    TailAdmissible r t N := by
  refine ⟨hN2, ?_⟩
  intro m hm
  exact ((antitoneOn_tailModel_Ici r hr0 hr1 hcut) (mem_Ici.mpr le_rfl)
    (mem_Ici.mpr hm) hm).trans_lt hmodel

/-- Logarithmic form of a strict model crossing. -/
theorem tailModel_lt_iff_log_gap {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (n : ℕ) :
    tailModel r n < t ↔
      Real.log (1 / t) <
        (-Real.log r) * (n : ℝ) - Real.log ((n + 1 : ℕ) : ℝ) := by
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hpow : 0 < r ^ n := pow_pos hr n
  have hmodel : 0 < tailModel r n := mul_pos hnpos hpow
  rw [← Real.log_lt_log_iff hmodel ht]
  unfold tailModel
  rw [Real.log_mul hnpos.ne' hpow.ne', Real.log_pow, one_div, Real.log_inv]
  push_cast
  constructor <;> intro h <;> linarith

/-- The logarithmic--logarithmic inverse scale for the model parameter `r`. -/
def tailInversionScale (r t : ℝ) : ℝ :=
  1 / (-Real.log r) *
    (Real.log (1 / t) + Real.log (Real.log (1 / t)))

/-- Uniform two-sided logarithmic inversion estimate, obtained from the
crossing at the threshold and the failed crossing at its predecessor. -/
theorem tailThreshold_logarithmic_bounds {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y : ℝ, ∀ t : ℝ,
      0 < t → Y ≤ Real.log (1 / t) →
        |(tailThreshold r t : ℝ) - tailInversionScale r t| ≤ C := by
  let β := -Real.log r
  have hβ : 0 < β := neg_pos.mpr (Real.log_neg hr hr1)
  obtain ⟨C, hC, Y, hbound⟩ := logarithmic_sandwich_bounded_error hβ 0 β
  refine ⟨C, hC, max Y (2 * β), ?_⟩
  intro t ht hy
  let N := tailThreshold r t
  let L := Real.log (1 / t)
  have hLY : Y ≤ L := (le_max_left _ _).trans hy
  have hLβ : 2 * β ≤ L := (le_max_right _ _).trans hy
  have hT : TailAdmissible r t N := tailThreshold_admissible hr.le hr1 ht
  have htwo : t ≤ tailModel r 2 := by
    apply le_of_not_gt
    intro h
    have hgap := (tailModel_lt_iff_log_gap hr ht 2).1 h
    have hlog : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
    change L < β * (2 : ℕ) - Real.log ((2 + 1 : ℕ) : ℝ) at hgap
    norm_num only [Nat.cast_ofNat] at hgap
    linarith
  have hN3 : 3 ≤ N := lt_tailThreshold_of_model_ge hr.le hr1 ht htwo
  have hprev : t ≤ tailModel r (N - 1) := by
    apply le_of_not_gt
    intro h
    have hA : TailAdmissible r t (N - 1) := by
      refine ⟨by omega, ?_⟩
      intro m hm
      by_cases heq : m = N - 1
      · simpa only [heq] using h
      · exact hT.2 m (by omega)
    have hle : N ≤ N - 1 := tailThreshold_le_of_admissible hA
    omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : L + Real.log (N : ℝ) + 0 ≤ β * N := by
    have hgap := (tailModel_lt_iff_log_gap hr ht N).1 (hT.2 N le_rfl)
    have hlog := Real.log_le_log hNpos
      (show (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by exact_mod_cast Nat.le_succ N)
    change L < β * N - Real.log ((N + 1 : ℕ) : ℝ) at hgap
    linarith
  have hu : β * N ≤ L + Real.log (N : ℝ) + β := by
    have hgap : β * (N - 1 : ℕ) - Real.log ((N - 1 + 1 : ℕ) : ℝ) ≤ L := by
      apply le_of_not_gt
      intro h
      exact (not_lt_of_ge hprev) ((tailModel_lt_iff_log_gap hr ht (N - 1)).2 h)
    have hprevid : N - 1 + 1 = N := by omega
    rw [hprevid, Nat.cast_sub (show 1 ≤ N by omega), Nat.cast_one] at hgap
    nlinarith
  have herror := hbound N L (by exact_mod_cast (show 1 ≤ N by omega)) hLY hl hu
  have hscale : (L + Real.log L) / β = tailInversionScale r t := by
    dsimp [tailInversionScale, L, β]
    ring
  rwa [hscale] at herror

/-- Bounded-error inversion of the permanent geometric tail threshold as the
level tends to zero. -/
theorem tailThreshold_boundedErrorAtZero {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    BoundedErrorAtZero (fun t : ℝ => (tailThreshold r t : ℝ))
      (tailInversionScale r) := by
  obtain ⟨C, hC, Y, hbound⟩ := tailThreshold_logarithmic_bounds hr hr1
  let Y₀ := max Y 1
  refine ⟨C, hC, Real.exp (-Y₀), Real.exp_pos _, ?_⟩
  intro t ht hsmall
  have hlog : Real.log t < -Y₀ := by
    have := Real.log_lt_log ht hsmall
    simpa using this
  have hY : Y ≤ Real.log (1 / t) := by
    rw [one_div, Real.log_inv]
    have hYY₀ : Y ≤ Y₀ := le_max_left Y 1
    linarith
  exact hbound t ht hY

/-- At `r=√a`, the scalar inversion scale is exactly the paper's
`criticalScale`; in particular, its prefactor is `2/log(1/a)`. -/
theorem tailInversionScale_pathRate_eq_criticalScale
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (t : ℝ) :
    tailInversionScale (pathRate a) t = criticalScale a t := by
  have hL : 0 < Real.log (1 / a) := log_one_div_pos ha ha1
  have hlog : -Real.log a = Real.log (1 / a) := by
    rw [one_div, Real.log_inv]
  unfold tailInversionScale criticalScale pathRate
  rw [Real.log_sqrt ha.le]
  rw [← hlog]
  field_simp [hL.ne']

/-- Multiplying the small level by a fixed positive constant changes the
logarithmic--logarithmic scale by only a bounded amount. -/
theorem tailInversionScale_mul_stable {r c : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hc : 0 < c) :
    BoundedErrorAtZero (fun t : ℝ => tailInversionScale r (c * t))
      (tailInversionScale r) := by
  let lam : ℝ := -Real.log r
  have hlam : 0 < lam := neg_pos.mpr (Real.log_neg hr hr1)
  let d : ℝ := Real.log c
  let A : ℝ := |d|
  have hA : 0 ≤ A := abs_nonneg d
  have hlogTwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  let C : ℝ := (A + Real.log 2) / lam
  have hC : 0 ≤ C := div_nonneg (add_nonneg hA hlogTwo) hlam.le
  refine ⟨C, hC, Real.exp (-(2 * A + 1)), Real.exp_pos _, ?_⟩
  intro t ht hsmall
  let y : ℝ := Real.log (1 / t)
  let yc : ℝ := Real.log (1 / (c * t))
  have hlogt : Real.log t < -(2 * A + 1) := by
    have := Real.log_lt_log ht hsmall
    simpa using this
  have hyEq : y = -Real.log t := by
    dsimp only [y]
    rw [one_div, Real.log_inv]
  have hyLarge : 2 * A + 1 < y := by rw [hyEq]; linarith
  have hyPos : 0 < y := by linarith
  have hycEq : yc = y - d := by
    dsimp only [yc, d]
    rw [one_div, Real.log_inv, Real.log_mul hc.ne' ht.ne']
    rw [hyEq]
    ring
  have hdUpper : d ≤ A := le_abs_self d
  have hdLower : -A ≤ d := neg_abs_le d
  have hycPos : 0 < yc := by rw [hycEq]; linarith
  have hratioLower : (1 / 2 : ℝ) ≤ yc / y := by
    apply (le_div_iff₀ hyPos).2
    rw [hycEq]
    nlinarith
  have hratioUpper : yc / y ≤ (2 : ℝ) := by
    apply (div_le_iff₀ hyPos).2
    rw [hycEq]
    nlinarith
  have hlogRatioLower :
      -Real.log 2 ≤ Real.log yc - Real.log y := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hratioLower
    rw [Real.log_div hycPos.ne' hyPos.ne'] at h
    have hhalf : Real.log (1 / 2) = -Real.log 2 := by
      rw [Real.log_div one_ne_zero (by norm_num), Real.log_one]
      ring
    rwa [hhalf] at h
  have hlogRatioUpper :
      Real.log yc - Real.log y ≤ Real.log 2 := by
    have h := Real.log_le_log (div_pos hycPos hyPos) hratioUpper
    rwa [Real.log_div hycPos.ne' hyPos.ne'] at h
  have hnum :
      |(yc - y) + (Real.log yc - Real.log y)| ≤ A + Real.log 2 := by
    have hycdiff : yc - y = -d := by rw [hycEq]; ring
    rw [abs_le]
    constructor <;> linarith
  unfold tailInversionScale
  have hscale :
      |1 / lam * (yc + Real.log yc) -
          1 / lam * (y + Real.log y)| =
        |(yc - y) + (Real.log yc - Real.log y)| / lam := by
    have halg :
        1 / lam * (yc + Real.log yc) -
            1 / lam * (y + Real.log y) =
          ((yc - y) + (Real.log yc - Real.log y)) / lam := by
      field_simp [hlam.ne']
      ring
    rw [halg, abs_div, abs_of_pos hlam]
  change |1 / lam * (yc + Real.log yc) -
      1 / lam * (y + Real.log y)| ≤ C
  rw [hscale]
  exact div_le_div_of_nonneg_right hnum hlam.le

/-- Bounded error is preserved by a fixed positive rescaling of the small
argument. -/
theorem BoundedErrorAtZero.comp_pos_mul {f g : ℝ → ℝ}
    (h : BoundedErrorAtZero f g) {c : ℝ} (hc : 0 < c) :
    BoundedErrorAtZero (fun t => f (c * t)) (fun t => g (c * t)) := by
  obtain ⟨C, hC, t₀, ht₀, hbound⟩ := h
  refine ⟨C, hC, t₀ / c, div_pos ht₀ hc, ?_⟩
  intro t ht hsmall
  apply hbound (c * t) (mul_pos hc ht)
  simpa [mul_comm] using (lt_div_iff₀ hc).1 hsmall

/-- Full stability statement: replacing `t` by `c*t`, for any fixed
`c>0`, leaves the same unscaled inversion formula up to bounded error. -/
theorem tailThreshold_mul_boundedErrorAtZero {r c : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hc : 0 < c) :
    BoundedErrorAtZero (fun t : ℝ => (tailThreshold r (c * t) : ℝ))
      (tailInversionScale r) := by
  exact ((tailThreshold_boundedErrorAtZero hr hr1).comp_pos_mul hc).trans
    (tailInversionScale_mul_stable hr hr1 hc)

end

end ConnectedPseudospectrum
