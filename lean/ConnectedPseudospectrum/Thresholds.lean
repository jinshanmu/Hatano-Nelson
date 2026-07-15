import ConnectedPseudospectrum.Definitions

/-!
# First-hit and eventual connectedness thresholds

This module gives the exact `N_f` and `N_e` definitions from `thm:main` as
least natural numbers.  It also proves their order-theoretic well-definedness
and the precise lemma that turns persistence of connectedness into
`N_f = N_e`.  Later modules supply persistence from the strict decrease of
the concrete barriers and the geometric connectedness criterion.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- The strict pseudospectrum in dimension `n` is connected and nonempty. -/
def ConnectedAtSize (n : ℕ) (a ε : ℝ) : Prop :=
  IsConnected (pseudospectrum n a ε)

/-- Candidate dimensions in the minimum defining the first-hit threshold. -/
def firstHitSet (a ε : ℝ) : Set ℕ :=
  {N | 2 ≤ N ∧ ConnectedAtSize N a ε}

/-- Candidate dimensions in the minimum defining the eventual threshold. -/
def eventualSet (a ε : ℝ) : Set ℕ :=
  {N | 2 ≤ N ∧ ∀ n, N ≤ n → ConnectedAtSize n a ε}

/-- The paper's first-hit threshold `N_f`.  As for `sInf` on naturals, its
value is `0` before nonemptiness is proved; `firstHitThreshold_mem` shows that
under the paper's hypotheses it is the advertised minimum. -/
def firstHitThreshold (a ε : ℝ) : ℕ :=
  sInf (firstHitSet a ε)

/-- The paper's eventual connectedness threshold `N_e`. -/
def eventualThreshold (a ε : ℝ) : ℕ :=
  sInf (eventualSet a ε)

/-- Every eventual candidate is in particular a first-hit candidate. -/
theorem eventualSet_subset_firstHitSet (a ε : ℝ) :
    eventualSet a ε ⊆ firstHitSet a ε := by
  intro N hN
  exact ⟨hN.1, hN.2 N le_rfl⟩

/-- Once nonemptiness is known, `N_f` itself satisfies the defining
first-hit property. -/
theorem firstHitThreshold_mem {a ε : ℝ}
    (h : (firstHitSet a ε).Nonempty) :
    firstHitThreshold a ε ∈ firstHitSet a ε := by
  exact Nat.sInf_mem h

/-- Once nonemptiness is known, `N_e` itself satisfies the defining tail
property. -/
theorem eventualThreshold_mem {a ε : ℝ}
    (h : (eventualSet a ε).Nonempty) :
    eventualThreshold a ε ∈ eventualSet a ε := by
  exact Nat.sInf_mem h

/-- `N_f` is no larger than any first-hit candidate. -/
theorem firstHitThreshold_le {a ε : ℝ} {N : ℕ}
    (hN : N ∈ firstHitSet a ε) :
    firstHitThreshold a ε ≤ N := by
  exact Nat.sInf_le hN

/-- `N_e` is no larger than any eventual candidate. -/
theorem eventualThreshold_le {a ε : ℝ} {N : ℕ}
    (hN : N ∈ eventualSet a ε) :
    eventualThreshold a ε ≤ N := by
  exact Nat.sInf_le hN

/-- The first-hit threshold is at least two whenever it is well-defined. -/
theorem two_le_firstHitThreshold {a ε : ℝ}
    (h : (firstHitSet a ε).Nonempty) :
    2 ≤ firstHitThreshold a ε :=
  (firstHitThreshold_mem h).1

/-- The eventual threshold is at least two whenever it is well-defined. -/
theorem two_le_eventualThreshold {a ε : ℝ}
    (h : (eventualSet a ε).Nonempty) :
    2 ≤ eventualThreshold a ε :=
  (eventualThreshold_mem h).1

/-- The exact minimum characterization of `N_f`. -/
theorem firstHitThreshold_le_iff {a ε : ℝ}
    (h : (firstHitSet a ε).Nonempty) (N : ℕ) :
    firstHitThreshold a ε ≤ N ↔
      ∃ m ≤ N, m ∈ firstHitSet a ε := by
  constructor
  · intro hle
    exact ⟨firstHitThreshold a ε, hle, firstHitThreshold_mem h⟩
  · rintro ⟨m, hmN, hm⟩
    exact (firstHitThreshold_le hm).trans hmN

/-- A persistence statement identifies the two candidate sets exactly. -/
theorem firstHitSet_eq_eventualSet_of_persistent {a ε : ℝ}
    (hpersistent : ∀ {N : ℕ}, 2 ≤ N → ConnectedAtSize N a ε →
      ∀ {n : ℕ}, N ≤ n → ConnectedAtSize n a ε) :
    firstHitSet a ε = eventualSet a ε := by
  apply Set.Subset.antisymm
  · intro N hN
    exact ⟨hN.1, fun n hNn => hpersistent hN.1 hN.2 hNn⟩
  · exact eventualSet_subset_firstHitSet a ε

/-- Persistence of connectedness proves the paper's equality `N_f = N_e`
without any hidden nonemptiness assumption. -/
theorem firstHitThreshold_eq_eventualThreshold_of_persistent {a ε : ℝ}
    (hpersistent : ∀ {N : ℕ}, 2 ≤ N → ConnectedAtSize N a ε →
      ∀ {n : ℕ}, N ≤ n → ConnectedAtSize n a ε) :
    firstHitThreshold a ε = eventualThreshold a ε := by
  unfold firstHitThreshold eventualThreshold
  rw [firstHitSet_eq_eventualSet_of_persistent hpersistent]

/-- Under an antitone barrier and the exact connectedness criterion,
connectedness persists through all larger dimensions. -/
theorem connectedAtSize_persistent_of_barrier_antitone {a ε : ℝ}
    (hcriterion : ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n a ε ↔ gapBarrier n a < ε))
    (hbarrier : ∀ {N n : ℕ}, 2 ≤ N → N ≤ n →
      gapBarrier n a ≤ gapBarrier N a) :
    ∀ {N : ℕ}, 2 ≤ N → ConnectedAtSize N a ε →
      ∀ {n : ℕ}, N ≤ n → ConnectedAtSize n a ε := by
  intro N hN hconnected n hNn
  have hn : 2 ≤ n := hN.trans hNn
  apply (hcriterion hn).2
  exact (hbarrier hN hNn).trans_lt ((hcriterion hN).1 hconnected)

/-- Concrete threshold equality obtained from the exact connectedness
criterion and monotonicity of the actual barrier sequence. -/
theorem firstHitThreshold_eq_eventualThreshold_of_barrier_antitone {a ε : ℝ}
    (hcriterion : ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n a ε ↔ gapBarrier n a < ε))
    (hbarrier : ∀ {N n : ℕ}, 2 ≤ N → N ≤ n →
      gapBarrier n a ≤ gapBarrier N a) :
    firstHitThreshold a ε = eventualThreshold a ε := by
  exact firstHitThreshold_eq_eventualThreshold_of_persistent
    (connectedAtSize_persistent_of_barrier_antitone hcriterion hbarrier)

/-- The threshold is two exactly when dimension two is already connected. -/
theorem firstHitThreshold_eq_two_iff {a ε : ℝ}
    (h : (firstHitSet a ε).Nonempty) :
    firstHitThreshold a ε = 2 ↔ ConnectedAtSize 2 a ε := by
  constructor
  · intro heq
    have hmem := firstHitThreshold_mem h
    rw [heq] at hmem
    exact hmem.2
  · intro htwo
    apply Nat.le_antisymm
    · exact firstHitThreshold_le ⟨le_rfl, htwo⟩
    · exact two_le_firstHitThreshold h

end

end ConnectedPseudospectrum
