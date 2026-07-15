import ConnectedPseudospectrum.GapDecay
import ConnectedPseudospectrum.Thresholds

/-!
# Exact threshold bounds

This module isolates the order-theoretic part of the proof of
`eq:N-two-sided-main`.  The maximum in the lower bound is represented by
adjoining the index `1`; consequently it is exactly `1` when the set of
dimensions obstructed by the lower barrier is empty.
-/

namespace ConnectedPseudospectrum

open Filter Set

noncomputable section

/-- Dimensions at which the explicit lower barrier still prevents strict
connectedness. -/
def lowerObstructionSet (a ε : ℝ) : Set ℕ :=
  {n | 2 ≤ n ∧ ε ≤ lowerBarrier n a}

/-- The maximum used in the lower threshold bound, with the paper's convention
that an empty obstruction set has maximum `1`. -/
def lowerObstructionMaximum (a ε : ℝ) : ℕ :=
  sSup (insert 1 (lowerObstructionSet a ε))

/-- Dimensions at which the explicit upper barrier already guarantees strict
connectedness. -/
def upperBarrierCrossingSet (a ε : ℝ) : Set ℕ :=
  {n | 2 ≤ n ∧ upperBarrier n a < ε}

/-- The least dimension at which the explicit upper barrier is below `ε`. -/
def upperBarrierThreshold (a ε : ℝ) : ℕ :=
  sInf (upperBarrierCrossingSet a ε)

/-- If no dimension is obstructed by the lower barrier, the maximum occurring
in the paper's bound is exactly the stipulated value `1`. -/
theorem lowerObstructionMaximum_eq_one_of_empty {a ε : ℝ}
    (h : lowerObstructionSet a ε = ∅) :
    lowerObstructionMaximum a ε = 1 := by
  simp [lowerObstructionMaximum, h]

/-- The upper-barrier crossing set is nonempty for every positive level. -/
theorem upperBarrierCrossingSet_nonempty {a ε : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε) :
    (upperBarrierCrossingSet a ε).Nonempty := by
  have hevent : ∀ᶠ n : ℕ in atTop, upperBarrier n a < ε :=
    (tendsto_order.1 (tendsto_upperBarrier_atTop_zero a ha0 ha1)).2 ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨max 2 N, le_max_left 2 N, ?_⟩
  exact hN (max 2 N) (le_max_right 2 N)

/-- The selected upper-barrier threshold satisfies its defining strict
crossing. -/
theorem upperBarrierThreshold_mem {a ε : ℝ}
    (h : (upperBarrierCrossingSet a ε).Nonempty) :
    upperBarrierThreshold a ε ∈ upperBarrierCrossingSet a ε := by
  exact Nat.sInf_mem h

/-- Every explicit upper-barrier crossing bounds its selected threshold. -/
theorem upperBarrierThreshold_le {a ε : ℝ} {N : ℕ}
    (hN : N ∈ upperBarrierCrossingSet a ε) :
    upperBarrierThreshold a ε ≤ N := by
  exact Nat.sInf_le hN

/-- Convergence of the actual barriers and the exact geometric criterion make
the eventual-connectedness minimum nonempty. -/
theorem eventualSet_nonempty_of_gapBarrier_tendsto {a ε : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε)
    (hcriterion : ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n a ε ↔ gapBarrier n a < ε)) :
    (eventualSet a ε).Nonempty := by
  have hevent : ∀ᶠ n : ℕ in atTop, gapBarrier n a < ε :=
    (tendsto_order.1 (tendsto_gapBarrier_atTop_zero a ha0 ha1)).2 ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨max 2 N, le_max_left 2 N, ?_⟩
  intro n hn
  apply (hcriterion ((le_max_left 2 N).trans hn)).2
  exact hN n ((le_max_right 2 N).trans hn)

/-- Eventual well-definedness also gives well-definedness of the first-hit
minimum. -/
theorem firstHitSet_nonempty_of_eventualSet_nonempty {a ε : ℝ}
    (h : (eventualSet a ε).Nonempty) :
    (firstHitSet a ε).Nonempty :=
  h.mono (eventualSet_subset_firstHitSet a ε)

/-- A strict adjacent decrease supplies the antitone comparison needed for
all larger dimensions. -/
theorem gapBarrier_antitone_of_succ_lt {a : ℝ}
    (hstrict : ∀ {n : ℕ}, 2 ≤ n →
      gapBarrier (n + 1) a < gapBarrier n a) :
    ∀ {N n : ℕ}, 2 ≤ N → N ≤ n →
      gapBarrier n a ≤ gapBarrier N a := by
  have hanti : AntitoneOn (fun n : ℕ => gapBarrier n a) (Ici 2) := by
    apply antitoneOn_nat_Ici_of_succ_le
    intro n hn
    exact (hstrict hn).le
  intro N n hN hNn
  exact hanti (mem_Ici.mpr hN) (mem_Ici.mpr (hN.trans hNn)) hNn

/-- The lower-barrier obstruction maximum lies strictly before the eventual
threshold.  This is the exact lower inequality in `eq:N-two-sided-main`.
-/
theorem one_add_lowerObstructionMaximum_le_eventualThreshold {a ε : ℝ}
    (hevent : (eventualSet a ε).Nonempty)
    (hcriterion : ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n a ε ↔ gapBarrier n a < ε))
    (hlower : ∀ {n : ℕ}, 2 ≤ n →
      lowerBarrier n a ≤ gapBarrier n a) :
    1 + lowerObstructionMaximum a ε ≤ eventualThreshold a ε := by
  let M := eventualThreshold a ε
  have hM := eventualThreshold_mem hevent
  have hM2 : 2 ≤ M := hM.1
  have hlt : ∀ k ∈ insert 1 (lowerObstructionSet a ε), k < M := by
    intro k hk
    rcases hk with rfl | hk
    · omega
    · by_contra hnot
      have hMk : M ≤ k := Nat.le_of_not_gt hnot
      have hconnected : ConnectedAtSize k a ε := hM.2 k hMk
      have hgap : gapBarrier k a < ε :=
        (hcriterion hk.1).1 hconnected
      exact (not_lt_of_ge (hk.2.trans (hlower hk.1))) hgap
  have hbounded : BddAbove (insert 1 (lowerObstructionSet a ε)) := by
    exact ⟨M, fun k hk => (hlt k hk).le⟩
  have hnonempty : (insert 1 (lowerObstructionSet a ε)).Nonempty :=
    ⟨1, mem_insert 1 _⟩
  have hmaxmem : lowerObstructionMaximum a ε ∈
      insert 1 (lowerObstructionSet a ε) := by
    exact Nat.sSup_mem hnonempty hbounded
  have hmaxlt : lowerObstructionMaximum a ε < M := hlt _ hmaxmem
  dsimp only [M] at hmaxlt
  omega

/-- The first-hit threshold is no larger than the first upper-barrier
crossing.  This is the exact upper inequality in `eq:N-two-sided-main`. -/
theorem firstHitThreshold_le_upperBarrierThreshold {a ε : ℝ}
    (hupper : (upperBarrierCrossingSet a ε).Nonempty)
    (hcriterion : ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n a ε ↔ gapBarrier n a < ε))
    (hgapUpper : ∀ {n : ℕ}, 2 ≤ n →
      gapBarrier n a ≤ upperBarrier n a) :
    firstHitThreshold a ε ≤ upperBarrierThreshold a ε := by
  have hU := upperBarrierThreshold_mem hupper
  apply firstHitThreshold_le
  refine ⟨hU.1, (hcriterion hU.1).2 ?_⟩
  exact (hgapUpper hU.1).trans_lt hU.2

/-- The complete threshold conclusion from the strict barrier theorem, the
geometric connectedness criterion, and the two explicit barrier estimates.
The two minima are proved nonempty rather than assumed. -/
theorem threshold_equality_and_two_sided_bounds {a ε : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε)
    (hcriterion : ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n a ε ↔ gapBarrier n a < ε))
    (hstrict : ∀ {n : ℕ}, 2 ≤ n →
      gapBarrier (n + 1) a < gapBarrier n a)
    (hlower : ∀ {n : ℕ}, 2 ≤ n →
      lowerBarrier n a ≤ gapBarrier n a)
    (hupper : ∀ {n : ℕ}, 2 ≤ n →
      gapBarrier n a ≤ upperBarrier n a) :
    (firstHitSet a ε).Nonempty ∧
      (eventualSet a ε).Nonempty ∧
      firstHitThreshold a ε = eventualThreshold a ε ∧
      1 + lowerObstructionMaximum a ε ≤ firstHitThreshold a ε ∧
      firstHitThreshold a ε ≤ upperBarrierThreshold a ε := by
  have hevent : (eventualSet a ε).Nonempty :=
    eventualSet_nonempty_of_gapBarrier_tendsto ha0 ha1 hε hcriterion
  have hfirst : (firstHitSet a ε).Nonempty :=
    firstHitSet_nonempty_of_eventualSet_nonempty hevent
  have hanti : ∀ {N n : ℕ}, 2 ≤ N → N ≤ n →
      gapBarrier n a ≤ gapBarrier N a :=
    gapBarrier_antitone_of_succ_lt hstrict
  have heq : firstHitThreshold a ε = eventualThreshold a ε :=
    firstHitThreshold_eq_eventualThreshold_of_barrier_antitone hcriterion hanti
  have hUpperSet : (upperBarrierCrossingSet a ε).Nonempty :=
    upperBarrierCrossingSet_nonempty ha0 ha1 hε
  refine ⟨hfirst, hevent, heq, ?_, firstHitThreshold_le_upperBarrierThreshold
    hUpperSet hcriterion hupper⟩
  rw [heq]
  exact one_add_lowerObstructionMaximum_le_eventualThreshold
    hevent hcriterion hlower

end

end ConnectedPseudospectrum
