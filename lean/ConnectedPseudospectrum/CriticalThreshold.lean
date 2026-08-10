import ConnectedPseudospectrum.DimensionTwo
import ConnectedPseudospectrum.LowerBarrierOrder
import ConnectedPseudospectrum.ThresholdBounds

/-!
# Critical threshold and its fixed-parameter asymptotic

This module proves the scalar threshold inversion part of `thm:main` from the
actual connectedness criterion, the strict decrease of the actual gap barrier,
and the lower half of `prop:gap-bounds`.  The upper half and all tail inversion
estimates are already concrete theorems of the project.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- The common critical threshold, represented by the first-hit minimum.  The
theorems below prove that it equals the eventual minimum under the paper's
strict barrier theorem. -/
def criticalThreshold (a ε : ℝ) : ℕ :=
  firstHitThreshold a ε

/-- The lower fixed-order estimate forces the geometric tail crossing to
occur no later than the eventual connectedness threshold. -/
theorem tailThreshold_div_lowerConstant_le_eventualThreshold
    {a ε : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hevent : (eventualSet a ε).Nonempty)
    (hcriterion : ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n a ε ↔ gapBarrier n a < ε))
    (hlower : ∀ {n : ℕ}, 2 ≤ n →
      lowerBarrier n a ≤ gapBarrier n a) :
    tailThreshold (pathRate a) (ε / lowerBarrierOrderConstant a) ≤
      eventualThreshold a ε := by
  have hC : 0 < lowerBarrierOrderConstant a :=
    lowerBarrierOrderConstant_pos ha0 ha1
  have hE := eventualThreshold_mem hevent
  apply tailThreshold_le_of_admissible
  refine ⟨hE.1, ?_⟩
  intro m hm
  have hm2 : 2 ≤ m := hE.1.trans hm
  have hgamma : gapBarrier m a < ε :=
    (hcriterion hm2).1 (hE.2 m hm)
  have hmodel :
      lowerBarrierOrderConstant a * tailModel (pathRate a) m < ε :=
    (lowerBarrierOrderConstant_mul_tailModel_le_lowerBarrier
      ha0 ha1 hm2).trans_lt ((hlower hm2).trans_lt hgamma)
  apply (lt_div_iff₀ hC).2
  simpa only [mul_comm] using hmodel

/-- The explicit upper estimate makes the geometric crossing at level
`2ε` an eventual connectedness candidate. -/
theorem eventualThreshold_le_tailThreshold_two_mul
    {a ε : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε)
    (hcriterion : ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n a ε ↔ gapBarrier n a < ε)) :
    eventualThreshold a ε ≤ tailThreshold (pathRate a) (2 * ε) := by
  have hr0 : 0 ≤ pathRate a := Real.sqrt_nonneg a
  have hr1 : pathRate a < 1 := by
    unfold pathRate
    simpa using (Real.sqrt_lt_sqrt_iff ha0.le).2 ha1
  have htwoε : 0 < (2 : ℝ) * ε := mul_pos (by norm_num) hε
  have hT : TailAdmissible (pathRate a) (2 * ε)
      (tailThreshold (pathRate a) (2 * ε)) :=
    tailThreshold_admissible hr0 hr1 htwoε
  apply eventualThreshold_le
  refine ⟨hT.1, ?_⟩
  intro m hm
  have hm2 : 2 ≤ m := hT.1.trans hm
  apply (hcriterion hm2).2
  have hgammaUpper : gapBarrier m a ≤ upperBarrier m a :=
    gapBarrier_le_upperBarrier hm2 a ha0
  have hlinear : upperBarrier m a ≤ tailModel (pathRate a) m / 2 := by
    simpa only [tailModel] using
      (upperBarrier_le_linear_mul_pow (show 1 ≤ m by omega) a)
  have htail : tailModel (pathRate a) m < 2 * ε := hT.2 m hm
  exact hgammaUpper.trans_lt (hlinear.trans_lt (by linarith))

/-- Strict adjacent decrease identifies the first-hit and eventual minima. -/
theorem criticalThreshold_eq_eventualThreshold_of_succ_lt
    {a ε : ℝ}
    (hcriterion : ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n a ε ↔ gapBarrier n a < ε))
    (hstrict : ∀ {n : ℕ}, 2 ≤ n →
      gapBarrier (n + 1) a < gapBarrier n a) :
    criticalThreshold a ε = eventualThreshold a ε := by
  unfold criticalThreshold
  exact firstHitThreshold_eq_eventualThreshold_of_barrier_antitone
    hcriterion (gapBarrier_antitone_of_succ_lt hstrict)

/-- Among dimensions at least two, connectedness holds exactly at and above
the critical threshold. -/
theorem connectedDimensions_eq_criticalThreshold_tail
    {a ε : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε)
    (hcriterion : ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n a ε ↔ gapBarrier n a < ε))
    (hstrict : ∀ {n : ℕ}, 2 ≤ n →
      gapBarrier (n + 1) a < gapBarrier n a) :
    {n : ℕ | 2 ≤ n ∧ IsConnected (pseudospectrum n a ε)} =
      {n : ℕ | criticalThreshold a ε ≤ n} := by
  have hevent : (eventualSet a ε).Nonempty :=
    eventualSet_nonempty_of_gapBarrier_tendsto ha0 ha1 hε hcriterion
  have hfirst : (firstHitSet a ε).Nonempty :=
    firstHitSet_nonempty_of_eventualSet_nonempty hevent
  have hpersistent :
      ∀ {N : ℕ}, 2 ≤ N → ConnectedAtSize N a ε →
        ∀ {n : ℕ}, N ≤ n → ConnectedAtSize n a ε :=
    connectedAtSize_persistent_of_barrier_antitone
      hcriterion (gapBarrier_antitone_of_succ_lt hstrict)
  change firstHitSet a ε = {n : ℕ | firstHitThreshold a ε ≤ n}
  ext n
  constructor
  · exact fun hn => firstHitThreshold_le hn
  · intro hn
    have hmin := firstHitThreshold_mem hfirst
    exact ⟨hmin.1.trans hn, hpersistent hmin.1 hmin.2 hn⟩

/-- Equation `eq:tail-threshold-bounds`, for the actual critical threshold.
-/
theorem criticalThreshold_tail_sandwich
    {a ε : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε)
    (hcriterion : ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n a ε ↔ gapBarrier n a < ε))
    (hstrict : ∀ {n : ℕ}, 2 ≤ n →
      gapBarrier (n + 1) a < gapBarrier n a)
    (hlower : ∀ {n : ℕ}, 2 ≤ n →
      lowerBarrier n a ≤ gapBarrier n a) :
    tailThreshold (pathRate a) (ε / lowerBarrierOrderConstant a) ≤
        criticalThreshold a ε ∧
      criticalThreshold a ε ≤ tailThreshold (pathRate a) (2 * ε) := by
  have hevent : (eventualSet a ε).Nonempty :=
    eventualSet_nonempty_of_gapBarrier_tendsto ha0 ha1 hε hcriterion
  have heq := criticalThreshold_eq_eventualThreshold_of_succ_lt
    hcriterion hstrict
  rw [heq]
  exact ⟨tailThreshold_div_lowerConstant_le_eventualThreshold
      ha0 ha1 hevent hcriterion hlower,
    eventualThreshold_le_tailThreshold_two_mul ha0 ha1 hε hcriterion⟩

/-- A function squeezed between two functions having bounded error from the
same scale has bounded error from that scale. -/
theorem boundedErrorAtZero_of_sandwich
    {f g h scale : ℝ → ℝ}
    (hf : BoundedErrorAtZero f scale)
    (hh : BoundedErrorAtZero h scale)
    (hsandwich : ∀ ε : ℝ, 0 < ε → f ε ≤ g ε ∧ g ε ≤ h ε) :
    BoundedErrorAtZero g scale := by
  obtain ⟨C₁, hC₁, ε₁, hε₁, hb₁⟩ := hf
  obtain ⟨C₂, hC₂, ε₂, hε₂, hb₂⟩ := hh
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, min ε₁ ε₂,
    lt_min hε₁ hε₂, ?_⟩
  intro ε hε hsmall
  have hsmall₁ : ε < ε₁ := hsmall.trans_le (min_le_left ε₁ ε₂)
  have hsmall₂ : ε < ε₂ := hsmall.trans_le (min_le_right ε₁ ε₂)
  have hbound₁ := hb₁ ε hε hsmall₁
  have hbound₂ := hb₂ ε hε hsmall₂
  have hsand := hsandwich ε hε
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (f ε - scale ε)]
  · linarith [le_abs_self (h ε - scale ε)]

/-- Precise bounded-error form of `eq:N-asymptotic-main`.  The constants are
allowed to depend on the fixed `a`, and no uniformity near `a=1` is claimed.
-/
theorem criticalThreshold_hasCriticalSizeAsymptotic
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hcriterion : ∀ {ε : ℝ}, 0 < ε → ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n a ε ↔ gapBarrier n a < ε))
    (hstrict : ∀ {n : ℕ}, 2 ≤ n →
      gapBarrier (n + 1) a < gapBarrier n a)
    (hlower : ∀ {n : ℕ}, 2 ≤ n →
      lowerBarrier n a ≤ gapBarrier n a) :
    HasCriticalSizeAsymptotic (criticalThreshold a) a := by
  let r := pathRate a
  let C := lowerBarrierOrderConstant a
  have hr : 0 < r := by
    dsimp only [r, pathRate]
    exact Real.sqrt_pos.2 ha0
  have hr1 : r < 1 := by
    dsimp only [r, pathRate]
    simpa using (Real.sqrt_lt_sqrt_iff ha0.le).2 ha1
  have hC : 0 < C := by
    dsimp only [C]
    exact lowerBarrierOrderConstant_pos ha0 ha1
  have hlowerError :
      BoundedErrorAtZero
        (fun ε : ℝ => (tailThreshold r ((1 / C) * ε) : ℝ))
        (tailInversionScale r) :=
    tailThreshold_mul_boundedErrorAtZero hr hr1 (one_div_pos.mpr hC)
  have hupperError :
      BoundedErrorAtZero
        (fun ε : ℝ => (tailThreshold r (2 * ε) : ℝ))
        (tailInversionScale r) :=
    tailThreshold_mul_boundedErrorAtZero hr hr1 (by norm_num)
  have hcriticalError :
      BoundedErrorAtZero (fun ε : ℝ => (criticalThreshold a ε : ℝ))
        (tailInversionScale r) := by
    apply boundedErrorAtZero_of_sandwich hlowerError hupperError
    intro ε hε
    have hsand := criticalThreshold_tail_sandwich ha0 ha1 hε
      (hcriterion hε) hstrict hlower
    exact ⟨by
      exact_mod_cast (show tailThreshold r ((1 / C) * ε) ≤
        criticalThreshold a ε by
          simpa [r, C, div_eq_mul_inv, mul_comm] using hsand.1),
      by exact_mod_cast hsand.2⟩
  unfold HasCriticalSizeAsymptotic
  have hscale : tailInversionScale r = criticalScale a := by
    funext ε
    dsimp only [r]
    exact tailInversionScale_pathRate_eq_criticalScale ha0 ha1 ε
  rwa [hscale] at hcriticalError

/-- The exact two-dimensional endpoint of the critical threshold.  The
strict inequality is inherited from the strict open pseudospectrum. -/
theorem criticalThreshold_eq_two_iff
    {a ε : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε)
    (hcriterion : ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n a ε ↔ gapBarrier n a < ε)) :
    criticalThreshold a ε = 2 ↔ ε > a := by
  have hevent : (eventualSet a ε).Nonempty :=
    eventualSet_nonempty_of_gapBarrier_tendsto ha0 ha1 hε hcriterion
  have hfirst : (firstHitSet a ε).Nonempty :=
    firstHitSet_nonempty_of_eventualSet_nonempty hevent
  unfold criticalThreshold
  rw [firstHitThreshold_eq_two_iff hfirst, hcriterion (by norm_num),
    gapBarrier_two ha0.le ha1.le]

end

end ConnectedPseudospectrum
