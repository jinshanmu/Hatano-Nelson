import ConnectedPseudospectrum.ConnectednessCriterion
import ConnectedPseudospectrum.NormalBoundary
import ConnectedPseudospectrum.NormalCriticalThreshold
import ConnectedPseudospectrum.NormalGapGeometry

/-!
# Exact topology at the normal Toeplitz boundary

This module combines the one-dimensional gap geometry of the symmetric
Dirichlet spectrum with the exact normal-matrix disk formula.  It packages
the exact connectedness threshold for `A_n(1)` and transfers both
connectedness and component contractibility to arbitrary complex
tridiagonal Toeplitz matrices with equal nonzero off-diagonal moduli.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- The real spectral interval is contained in the strict normal
pseudospectrum exactly above the largest adjacent half-gap. -/
theorem spectralInterval_mapsTo_pseudospectrum_one_iff_normalThreshold_lt
    (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) :
    MapsTo (fun x : ℝ => (x : ℂ)) (spectralInterval n 1)
        (pseudospectrum n 1 ε) ↔
      normalThreshold n < ε := by
  have hdisks :
      MapsTo (fun x : ℝ => (x : ℂ)) (spectralInterval n 1)
          (pseudospectrum n 1 ε) ↔
        ∀ x ∈ spectralInterval n 1,
          ∃ k : Fin n, |x - pathEigenvalue n 1 k| < ε := by
    rw [pseudospectrum_one_eq_iUnion_balls n (by omega) ε]
    constructor
    · intro h x hx
      have hz := h hx
      rw [mem_iUnion] at hz
      obtain ⟨k, hk⟩ := hz
      refine ⟨k, ?_⟩
      rw [Metric.mem_ball, dist_eq_norm] at hk
      simpa only [← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using hk
    · intro h x hx
      rw [mem_iUnion]
      obtain ⟨k, hk⟩ := h x hx
      refine ⟨k, ?_⟩
      rw [Metric.mem_ball, dist_eq_norm]
      simpa only [← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using hk
  exact hdisks.trans
    (forall_mem_spectralInterval_exists_abs_sub_pathEigenvalue_lt_iff
      n hn ε)

/-- Exact connectedness threshold for the strict normal endpoint.  Equality
is excluded because the pseudospectrum and the covering disks are open. -/
theorem isConnected_pseudospectrum_one_iff_normalThreshold_lt
    (n : ℕ) (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    IsConnected (pseudospectrum n 1 ε) ↔ normalThreshold n < ε := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact (isConnected_pseudospectrum_iff_spectralInterval_mapsTo_of_vertical
    m zero_lt_one hε
      (verticalScalingClosed_pseudospectrum_one (m + 1) (by omega) ε)).trans
    (spectralInterval_mapsTo_pseudospectrum_one_iff_normalThreshold_lt
      (m + 1) (by omega) ε)

/-- Equal nonzero off-diagonal moduli reduce by an affine homeomorphism to
the normal endpoint.  The exact threshold and contractibility of every
actual component therefore transfer without loss. -/
theorem complexToeplitz_normal_corollary
    (n : ℕ) (hn : 2 ≤ n) {α β : ℂ} (d : ℂ)
    (hα : α ≠ 0) (hβ : β ≠ 0) (heq : ‖α‖ = ‖β‖)
    {ε : ℝ} (hε : 0 < ε) :
    (∀ {z : ℂ},
      z ∈ generalPseudospectrum (complexToeplitzMatrix n α d β) ε →
        ContractibleSpace
          (connectedComponentIn
            (generalPseudospectrum (complexToeplitzMatrix n α d β) ε) z)) ∧
    (IsConnected
      (generalPseudospectrum (complexToeplitzMatrix n α d β) ε) ↔
        ε > ‖α‖ * normalThreshold n) := by
  have hαnorm : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hεα : 0 < ε / ‖α‖ := div_pos hε hαnorm
  constructor
  · intro z hz
    rw [complexToeplitzPseudospectrum_eq_normal_affine_image
      n d hα hβ heq ε] at hz ⊢
    rcases hz with ⟨w, hw, rfl⟩
    let e := complexAffineHomeomorph (complexToeplitzScale α β) d
      (complexToeplitzScale_ne_zero hα)
    let C := connectedComponentIn (pseudospectrum n 1 (ε / ‖α‖)) w
    let hC : e '' C =
        connectedComponentIn
          (e '' pseudospectrum n 1 (ε / ‖α‖)) (e w) :=
      e.image_connectedComponentIn hw
    let hcomponent : C ≃ₜ
        connectedComponentIn
          (e '' pseudospectrum n 1 (ε / ‖α‖)) (e w) :=
      (Homeomorph.image e C).trans (Homeomorph.setCongr hC)
    letI : ContractibleSpace C :=
      contractibleSpace_pseudospectrum_one_component n hn hεα hw
    exact hcomponent.symm.contractibleSpace
  · rw [complexToeplitzPseudospectrum_eq_normal_affine_image
      n d hα hβ heq ε,
      (complexAffineHomeomorph (complexToeplitzScale α β) d
        (complexToeplitzScale_ne_zero hα)).isConnected_image,
      isConnected_pseudospectrum_one_iff_normalThreshold_lt n hn hεα]
    constructor
    · intro h
      have := (lt_div_iff₀ hαnorm).1 h
      simpa [mul_comm] using this
    · intro h
      apply (lt_div_iff₀ hαnorm).2
      simpa [mul_comm] using h

/-- In the equal-modulus regime, the matrix-connected dimensions are exactly
the scalar normal critical set. -/
theorem complexToeplitz_normal_connectedDimensions_eq_normalCriticalSet
    {α β : ℂ} (d : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (heq : ‖α‖ = ‖β‖) {ε : ℝ} (hε : 0 < ε) :
    {n : ℕ | 2 ≤ n ∧
      IsConnected
        (generalPseudospectrum (complexToeplitzMatrix n α d β) ε)} =
      normalCriticalSet ‖α‖ ε := by
  ext n
  change (2 ≤ n ∧
      IsConnected
        (generalPseudospectrum (complexToeplitzMatrix n α d β) ε)) ↔
    2 ≤ n ∧ ‖α‖ * normalThreshold n < ε
  constructor
  · rintro ⟨hn, hconnected⟩
    exact ⟨hn,
      (complexToeplitz_normal_corollary n hn d hα hβ heq hε).2.mp
        hconnected⟩
  · rintro ⟨hn, hthreshold⟩
    exact ⟨hn,
      (complexToeplitz_normal_corollary n hn d hα hβ heq hε).2.mpr
        hthreshold⟩

/-- The scalar `normalCriticalThreshold` is literally the first connected
dimension of the equal-modulus complex Toeplitz family. -/
theorem complexToeplitz_normal_firstConnectedDimension_isLeast
    {α β : ℂ} (d : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (heq : ‖α‖ = ‖β‖) {ε : ℝ} (hε : 0 < ε) :
    IsLeast
      {n : ℕ | 2 ≤ n ∧
        IsConnected
          (generalPseudospectrum (complexToeplitzMatrix n α d β) ε)}
      (normalCriticalThreshold ‖α‖ ε) := by
  rw [complexToeplitz_normal_connectedDimensions_eq_normalCriticalSet
    d hα hβ heq hε]
  exact normalCriticalThreshold_isLeast (norm_pos_iff.mpr hα) hε

end

end ConnectedPseudospectrum
