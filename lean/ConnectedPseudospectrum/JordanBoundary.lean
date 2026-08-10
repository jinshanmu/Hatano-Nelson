import ConnectedPseudospectrum.ComplexToeplitz
import ConnectedPseudospectrum.RadialTopology

/-!
# One-sided Jordan boundary

This module closes the reducible boundary in Proposition 3.2 of the ELA
manuscript.  The matrix-specific diagonal unitary from `ComplexToeplitz`
supplies invariance under every rotation about the diagonal entry.  The
radial classification in `RadialTopology` then identifies the whole strict
pseudospectrum as an open disk and proves its contractibility.
-/

namespace ConnectedPseudospectrum

open Matrix Set

noncomputable section

private theorem left_zero_rotationInvariant
    (n : ℕ) (d β : ℂ) (ε : ℝ) :
    ∀ u : ℂ, norm u = 1 → ∀ z : ℂ,
      z ∈ generalPseudospectrum (complexToeplitzMatrix n 0 d β) ε →
        d + u * (z - d) ∈
          generalPseudospectrum (complexToeplitzMatrix n 0 d β) ε := by
  intro u hu z hz
  change generalPseudospectralHeight (complexToeplitzMatrix n 0 d β)
      (d + u * (z - d)) < ε
  rw [generalPseudospectralHeight_left_zero_rotation n d β u z hu]
  exact hz

private theorem right_zero_rotationInvariant
    (n : ℕ) (α d : ℂ) (ε : ℝ) :
    ∀ u : ℂ, norm u = 1 → ∀ z : ℂ,
      z ∈ generalPseudospectrum (complexToeplitzMatrix n α d 0) ε →
        d + u * (z - d) ∈
          generalPseudospectrum (complexToeplitzMatrix n α d 0) ε := by
  intro u hu z hz
  change generalPseudospectralHeight (complexToeplitzMatrix n α d 0)
      (d + u * (z - d)) < ε
  rw [generalPseudospectralHeight_right_zero_rotation n α d u z hu]
  exact hz

/-- Every positive strict pseudospectrum of an upper one-sided Toeplitz
matrix is exactly an open disk centered at its unique eigenvalue. -/
theorem exists_eq_ball_complexToeplitzPseudospectrum_of_left_zero
    (n : ℕ) (hn : 0 < n) (d β : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧
      generalPseudospectrum (complexToeplitzMatrix n 0 d β) ε =
        Metric.ball d R := by
  apply exists_eq_ball_of_isOpen_isConnected_rotationInvariant
    (isOpen_generalPseudospectrum _ _)
    (isConnected_complexToeplitzPseudospectrum_of_left_zero n hn d β hε)
  · exact mem_generalPseudospectrum_of_det_generalShift_eq_zero
      (complexToeplitzMatrix n 0 d β) hn hε
        ((det_generalShift_complexToeplitzMatrix_eq_zero_iff_of_left_zero
          n hn d β d).2 rfl)
  · exact isBounded_generalPseudospectrum
      (complexToeplitzMatrix n 0 d β) hn ε hε
  · exact left_zero_rotationInvariant n d β ε

/-- The lower one-sided orientation has the same exact disk description. -/
theorem exists_eq_ball_complexToeplitzPseudospectrum_of_right_zero
    (n : ℕ) (hn : 0 < n) (α d : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧
      generalPseudospectrum (complexToeplitzMatrix n α d 0) ε =
        Metric.ball d R := by
  apply exists_eq_ball_of_isOpen_isConnected_rotationInvariant
    (isOpen_generalPseudospectrum _ _)
    (isConnected_complexToeplitzPseudospectrum_of_right_zero n hn α d hε)
  · exact mem_generalPseudospectrum_of_det_generalShift_eq_zero
      (complexToeplitzMatrix n α d 0) hn hε
        ((det_generalShift_complexToeplitzMatrix_eq_zero_iff_of_right_zero
          n hn α d d).2 rfl)
  · exact isBounded_generalPseudospectrum
      (complexToeplitzMatrix n α d 0) hn ε hε
  · exact right_zero_rotationInvariant n α d ε

/-- Connected rotational invariance also gives contractibility directly,
without choosing the disk radius. -/
theorem contractibleSpace_complexToeplitzPseudospectrum_of_left_zero
    (n : ℕ) (hn : 0 < n) (d β : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContractibleSpace
      (generalPseudospectrum (complexToeplitzMatrix n 0 d β) ε) := by
  apply contractibleSpace_of_isConnected_rotationInvariant
    (isConnected_complexToeplitzPseudospectrum_of_left_zero n hn d β hε)
  · exact mem_generalPseudospectrum_of_det_generalShift_eq_zero
      (complexToeplitzMatrix n 0 d β) hn hε
        ((det_generalShift_complexToeplitzMatrix_eq_zero_iff_of_left_zero
          n hn d β d).2 rfl)
  · exact left_zero_rotationInvariant n d β ε

theorem contractibleSpace_complexToeplitzPseudospectrum_of_right_zero
    (n : ℕ) (hn : 0 < n) (α d : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ContractibleSpace
      (generalPseudospectrum (complexToeplitzMatrix n α d 0) ε) := by
  apply contractibleSpace_of_isConnected_rotationInvariant
    (isConnected_complexToeplitzPseudospectrum_of_right_zero n hn α d hε)
  · exact mem_generalPseudospectrum_of_det_generalShift_eq_zero
      (complexToeplitzMatrix n α d 0) hn hε
        ((det_generalShift_complexToeplitzMatrix_eq_zero_iff_of_right_zero
          n hn α d d).2 rfl)
  · exact right_zero_rotationInvariant n α d ε

/-- Complete contractibility wrapper for the zero-product boundary. -/
theorem contractibleSpace_complexToeplitzPseudospectrum_of_mul_eq_zero
    (n : ℕ) (hn : 0 < n) (α d β : ℂ) (hαβ : α * β = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ContractibleSpace
      (generalPseudospectrum (complexToeplitzMatrix n α d β) ε) := by
  rcases mul_eq_zero.mp hαβ with hα | hβ
  · subst α
    exact contractibleSpace_complexToeplitzPseudospectrum_of_left_zero
      n hn d β hε
  · subst β
    exact contractibleSpace_complexToeplitzPseudospectrum_of_right_zero
      n hn α d hε

end

end ConnectedPseudospectrum
