import ConnectedPseudospectrum.Spectrum

/-!
# The explicit spectral mesh and its interval

This module identifies the two extreme nodes of the simple real spectrum with
the endpoints of `Iₙˢᵖ`, places every displayed eigenvalue in that interval,
and records the vanishing of the actual least singular value at both
endpoints.  These are the endpoint facts used in the gap and topology
arguments.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- The first displayed eigenvalue is the right endpoint of the real
spectral interval. -/
theorem pathEigenvalue_zero (m : ℕ) (a : ℝ) :
    pathEigenvalue (m + 1) a (0 : Fin (m + 1)) =
      spectralRadius (m + 1) a := by
  simp [pathEigenvalue, spectralRadius, pathRate]

/-- The elementary supplementary-angle identity for the last spectral node. -/
private theorem lastPathAngle_eq_pi_sub (m : ℕ) :
    (((m + 1 : ℕ) : ℝ) * Real.pi) / (((m + 2 : ℕ) : ℝ) : ℝ) =
      Real.pi - Real.pi / (((m + 2 : ℕ) : ℝ) : ℝ) := by
  have hden : (((m + 2 : ℕ) : ℝ) : ℝ) ≠ 0 := by positivity
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hden ⊢
  field_simp
  ring

/-- The last displayed eigenvalue is the left endpoint of the real spectral
interval. -/
theorem pathEigenvalue_last (m : ℕ) (a : ℝ) :
    pathEigenvalue (m + 1) a (Fin.last m) =
      -spectralRadius (m + 1) a := by
  unfold pathEigenvalue spectralRadius pathRate
  simp only [Fin.val_last]
  have hangle := lastPathAngle_eq_pi_sub m
  norm_num only [Nat.cast_add, Nat.cast_one] at hangle ⊢
  have hden_eq : (m : ℝ) + 1 + 1 = (m : ℝ) + 2 := by ring
  rw [hden_eq]
  rw [hangle, Real.cos_pi_sub]
  ring

/-- Every explicit eigenvalue lies in the convex hull of the two extreme
nodes, namely `Iₙˢᵖ`. -/
theorem pathEigenvalue_mem_spectralInterval (m : ℕ) {a : ℝ} (ha : 0 < a)
    (k : Fin (m + 1)) :
    pathEigenvalue (m + 1) a k ∈ spectralInterval (m + 1) a := by
  rw [spectralInterval, mem_Icc, ← pathEigenvalue_last m a,
    ← pathEigenvalue_zero m a]
  have hanti : Antitone (pathEigenvalue (m + 1) a) := by
    simpa only [pathEigenvalue_eq_symmetricPathEigenvalue] using
      (symmetricPathEigenvalue_strictAnti (m + 1) (Real.sqrt_pos.2 ha)).antitone
  exact ⟨hanti (Fin.le_last k), hanti (Fin.zero_le k)⟩

/-- The actual least singular value vanishes at the right spectral endpoint. -/
theorem pseudospectralHeight_spectralRadius (m : ℕ) {a : ℝ} (ha : 0 < a) :
    pseudospectralHeight (m + 1) a (spectralRadius (m + 1) a) = 0 := by
  rw [← pathEigenvalue_zero m a]
  exact pseudospectralHeight_pathEigenvalue (m + 1) ha (by omega) 0

/-- The actual least singular value vanishes at the left spectral endpoint. -/
theorem pseudospectralHeight_neg_spectralRadius (m : ℕ) {a : ℝ} (ha : 0 < a) :
    pseudospectralHeight (m + 1) a (-spectralRadius (m + 1) a) = 0 := by
  simpa only [pathEigenvalue_last, Complex.ofReal_neg] using
    pseudospectralHeight_pathEigenvalue (m + 1) ha (by omega) (Fin.last m)

/-- In positive dimension, the height is strictly positive away from all
spectral nodes. -/
theorem pseudospectralHeight_pos_iff_not_spectralNode (m : ℕ) {a : ℝ}
    (ha : 0 < a) (z : ℂ) :
    0 < pseudospectralHeight (m + 1) a z ↔
      ∀ k : Fin (m + 1), z ≠ (pathEigenvalue (m + 1) a k : ℂ) := by
  constructor
  · intro hpos k hzk
    subst z
    exact (ne_of_gt hpos)
      (pseudospectralHeight_pathEigenvalue (m + 1) ha (by omega) k)
  · intro hnodes
    have hne : pseudospectralHeight (m + 1) a z ≠ 0 := by
      intro hzero
      obtain ⟨k, hk⟩ :=
        (pseudospectralHeight_eq_zero_iff (m + 1) ha (by omega) z).1 hzero
      exact hnodes k hk
    exact lt_of_le_of_ne
      (leastSingularValue_nonneg (shiftedPathMatrix (m + 1) a z)) hne.symm

end

end ConnectedPseudospectrum
