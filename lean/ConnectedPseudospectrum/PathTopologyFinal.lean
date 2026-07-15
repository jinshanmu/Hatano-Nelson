import ConnectedPseudospectrum.ConnectednessCriterion
import ConnectedPseudospectrum.VerticalContinuation

/-!
# Unconditional path-pseudospectrum topology

This module instantiates the topological component and connectedness theorems
with the completed vertical least-singular-value monotonicity argument.
-/

namespace ConnectedPseudospectrum

noncomputable section

/-- The actual strict path pseudospectrum is closed under scaling every
vertical fibre toward the real axis. -/
theorem verticalScalingClosed_pathPseudospectrum
    (n : ℕ) (hn : 2 ≤ n) (a ε : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    VerticalScalingClosed (pseudospectrum n a ε) :=
  verticalScalingClosed_pseudospectrum_of_upperMonotone n a ε
    (verticalHeightMonotone n hn a ha0 ha1)

/-- Exact connectedness criterion for the strict open pseudospectrum.  In
particular, equality `ε = γₙ` is disconnected. -/
theorem isConnected_pathPseudospectrum_iff_gapBarrier_lt
    (n : ℕ) (hn : 2 ≤ n) {a ε : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε) :
    IsConnected (pseudospectrum n a ε) ↔ gapBarrier n a < ε := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact isConnected_pseudospectrum_iff_gapBarrier_lt_of_vertical
    m ha0 hε
      (verticalScalingClosed_pathPseudospectrum (m + 1) (by omega)
        a ε ha0 ha1)

/-- Every connected component of the actual strict path pseudospectrum is a
genuine contractible space. -/
theorem contractibleSpace_pathPseudospectral_component
    (n : ℕ) (hn : 2 ≤ n) {a ε : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hε : 0 < ε)
    {z : ℂ} (hz : z ∈ pseudospectrum n a ε) :
    ContractibleSpace (connectedComponentIn (pseudospectrum n a ε) z) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact contractibleSpace_pseudospectral_component_of_vertical
    m ha0 hε
      (verticalScalingClosed_pathPseudospectrum (m + 1) (by omega)
        a ε ha0 ha1) hz

end

end ConnectedPseudospectrum
