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

/-- The same scale written as a function of `y=log(1/t)` and
`lam=-log r`. -/
private def logTailScale (lam y : ℝ) : ℝ :=
  (y + Real.log y) / lam

/-- Elementary residual estimate underlying the inversion.  For fixed
`lam>0`, adding a fixed displacement `D` to `(y+log y)/lam` leaves the
logarithmic crossing residual convergent to `lam*D+log lam`. -/
private theorem tendsto_logTail_residual (lam : ℝ) (hlam : 0 < lam) (D k : ℝ) :
    Tendsto
      (fun y : ℝ =>
        lam * (logTailScale lam y + D) -
          Real.log (logTailScale lam y + D + k) - y)
      atTop (nhds (lam * D + Real.log lam)) := by
  let R : ℝ → ℝ := fun y =>
    (1 + Real.log y / y) / lam + (D + k) / y
  have hlogDiv :
      Tendsto (fun y : ℝ => Real.log y / y) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hinv : Tendsto (fun y : ℝ => y⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hfirst :
      Tendsto (fun y : ℝ => (1 + Real.log y / y) / lam)
        atTop (nhds (1 / lam)) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa [one_div] using (hone.add hlogDiv).div_const lam
  have hsecond :
      Tendsto (fun y : ℝ => (D + k) / y) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
  have hR : Tendsto R atTop (nhds (1 / lam)) := by
    simpa [R] using hfirst.add hsecond
  have hRpos : ∀ᶠ y : ℝ in atTop, 0 < R y :=
    (tendsto_order.1 hR).1 0 (one_div_pos.mpr hlam)
  have hlogR :
      Tendsto (fun y : ℝ => Real.log (R y)) atTop
        (nhds (Real.log (1 / lam))) := by
    exact (Real.continuousAt_log (one_div_ne_zero hlam.ne')).tendsto.comp hR
  have hsimple :
      Tendsto (fun y : ℝ => lam * D - Real.log (R y)) atTop
        (nhds (lam * D + Real.log lam)) := by
    convert tendsto_const_nhds.sub hlogR using 1
    rw [Real.log_div one_ne_zero hlam.ne', Real.log_one]
    ring_nf
  apply hsimple.congr'
  filter_upwards [eventually_gt_atTop 0, hRpos] with y hy hRy
  have hfactor : logTailScale lam y + D + k = y * R y := by
    dsimp only [logTailScale, R]
    field_simp [hlam.ne', hy.ne']
    ring
  rw [hfactor, Real.log_mul hy.ne' hRy.ne']
  dsimp only [logTailScale]
  field_simp [hlam.ne', hy.ne']
  ring

private theorem tendsto_logTailScale_atTop (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (logTailScale lam) atTop atTop := by
  have hlinear : Tendsto (fun y : ℝ => y / lam) atTop atTop := by
    simpa [div_eq_mul_inv] using
      tendsto_id.atTop_mul_const (inv_pos.mpr hlam)
  apply tendsto_atTop_mono' atTop _ hlinear
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  unfold logTailScale
  exact (div_le_div_iff_of_pos_right hlam).2
    (le_add_of_nonneg_right (Real.log_nonneg hy))

/-- Uniform two-sided logarithmic inversion estimate. -/
theorem tailThreshold_logarithmic_bounds {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y : ℝ, ∀ t : ℝ,
      0 < t → Y ≤ Real.log (1 / t) →
        |(tailThreshold r t : ℝ) - tailInversionScale r t| ≤ C := by
  let lam : ℝ := -Real.log r
  have hlam : 0 < lam := neg_pos.mpr (Real.log_neg hr hr1)
  let C₀ : ℝ := (|Real.log lam| + 2) / lam
  have hC₀ : 0 ≤ C₀ := div_nonneg (by positivity) hlam.le
  have hlamC₀ : lam * C₀ = |Real.log lam| + 2 := by
    dsimp only [C₀]
    field_simp [hlam.ne']
  have hupperLimit : 0 < lam * C₀ + Real.log lam := by
    rw [hlamC₀]
    linarith [neg_abs_le (Real.log lam)]
  have hlowerLimit : lam * (-C₀) + Real.log lam < 0 := by
    rw [mul_neg, hlamC₀]
    linarith [le_abs_self (Real.log lam)]
  have hupperEventually : ∀ᶠ y : ℝ in atTop,
      0 < lam * (logTailScale lam y + C₀) -
        Real.log (logTailScale lam y + C₀ + 2) - y :=
    (tendsto_order.1
      (tendsto_logTail_residual lam hlam C₀ 2)).1 0 hupperLimit
  have hlowerEventually : ∀ᶠ y : ℝ in atTop,
      lam * (logTailScale lam y - C₀) -
        Real.log (logTailScale lam y - C₀) - y < 0 := by
    have h := (tendsto_order.1
      (tendsto_logTail_residual lam hlam (-C₀) 0)).2 0 hlowerLimit
    simpa [sub_eq_add_neg] using h
  have hscale := tendsto_logTailScale_atTop lam hlam
  have hlargeLower : ∀ᶠ y : ℝ in atTop,
      C₀ + 2 ≤ logTailScale lam y :=
    hscale.eventually_ge_atTop (C₀ + 2)
  have hlargeCutoff : ∀ᶠ y : ℝ in atTop,
      r / (1 - r) - C₀ ≤ logTailScale lam y :=
    hscale.eventually_ge_atTop (r / (1 - r) - C₀)
  have hall : ∀ᶠ y : ℝ in atTop,
      (0 < lam * (logTailScale lam y + C₀) -
          Real.log (logTailScale lam y + C₀ + 2) - y) ∧
      (lam * (logTailScale lam y - C₀) -
          Real.log (logTailScale lam y - C₀) - y < 0) ∧
      (C₀ + 2 ≤ logTailScale lam y) ∧
      (r / (1 - r) - C₀ ≤ logTailScale lam y) := by
    filter_upwards [hupperEventually, hlowerEventually, hlargeLower,
      hlargeCutoff] with y hu hl hlow hcut
    exact ⟨hu, hl, hlow, hcut⟩
  obtain ⟨Y, hY⟩ := eventually_atTop.1 hall
  refine ⟨C₀ + 1, by positivity, Y, ?_⟩
  intro t ht hy
  let y := Real.log (1 / t)
  let S := logTailScale lam y
  have hdata := hY y hy
  have hu := hdata.1
  have hl := hdata.2.1
  have hSlow : C₀ + 2 ≤ S := hdata.2.2.1
  have hScut : r / (1 - r) - C₀ ≤ S := hdata.2.2.2
  let N : ℕ := ⌈S + C₀⌉₊
  have hzUpper : 0 ≤ S + C₀ := by linarith
  have hzUpperN : S + C₀ ≤ (N : ℝ) := Nat.le_ceil _
  have hNUpper : (N : ℝ) < S + C₀ + 1 :=
    Nat.ceil_lt_add_one hzUpper
  have hN2 : 2 ≤ N := by
    exact_mod_cast (show (2 : ℝ) ≤ (N : ℝ) by linarith)
  have hNcut : r / (1 - r) ≤ (N + 1 : ℝ) := by
    linarith
  have hNpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hlogUpper :
      Real.log ((N + 1 : ℕ) : ℝ) < Real.log (S + C₀ + 2) := by
    apply Real.log_lt_log hNpos
    push_cast at hNUpper ⊢
    linarith
  have hgapUpper : y <
      lam * (N : ℝ) - Real.log ((N + 1 : ℕ) : ℝ) := by
    nlinarith
  have hlamEq : lam = -Real.log r := rfl
  have hmodelN : tailModel r N < t := by
    apply (tailModel_lt_iff_log_gap hr ht N).2
    simpa only [y, hlamEq] using hgapUpper
  have hTUpper : tailThreshold r t ≤ N :=
    tailThreshold_le_of_admissible
      (tailAdmissible_of_cutoff_of_model_lt hr.le hr1 hN2 hNcut hmodelN)
  let z := S - C₀
  let K : ℕ := ⌊z⌋₊
  have hzTwo : (2 : ℝ) ≤ z := by dsimp only [z]; linarith
  have hzNonneg : 0 ≤ z := hzTwo.trans' (by norm_num)
  have hKLower : (K : ℝ) ≤ z := Nat.floor_le hzNonneg
  have hzK : z < (K : ℝ) + 1 := Nat.lt_floor_add_one z
  have hKpos : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
  have hlogLower : Real.log z < Real.log ((K + 1 : ℕ) : ℝ) := by
    apply Real.log_lt_log (by linarith)
    push_cast
    exact hzK
  have hgapLower :
      lam * (K : ℝ) - Real.log ((K + 1 : ℕ) : ℝ) < y := by
    dsimp only [z] at hKLower hlogLower
    nlinarith
  have hmodelK : t ≤ tailModel r K := by
    apply le_of_not_gt
    intro hlt
    have hgap := (tailModel_lt_iff_log_gap hr ht K).1 hlt
    rw [← hlamEq] at hgap
    change y < lam * (K : ℝ) - Real.log ((K + 1 : ℕ) : ℝ) at hgap
    linarith
  have hKThreshold : K < tailThreshold r t :=
    lt_tailThreshold_of_model_ge hr.le hr1 ht hmodelK
  have hUpperReal : (tailThreshold r t : ℝ) < S + C₀ + 1 := by
    exact (Nat.cast_le.mpr hTUpper).trans_lt hNUpper
  have hLowerReal : S - C₀ < (tailThreshold r t : ℝ) := by
    have hsucc : K + 1 ≤ tailThreshold r t := hKThreshold
    have hsuccReal : (K : ℝ) + 1 ≤ (tailThreshold r t : ℝ) := by
      exact_mod_cast hsucc
    exact (show S - C₀ < (K : ℝ) + 1 by simpa only [z] using hzK).trans_le
      hsuccReal
  have hscaleEq : tailInversionScale r t = S := by
    dsimp only [tailInversionScale, S, y, logTailScale, lam]
    field_simp [hlam.ne']
  rw [hscaleEq]
  rw [abs_le]
  constructor <;> linarith

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
