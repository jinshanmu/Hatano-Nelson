import ConnectedPseudospectrum.LeastSingular

/-!
# Pseudospectra of arbitrary finite complex matrices

This module records the matrix-generic analytic facts used in the proof that
every connected component of a finite-dimensional pseudospectrum contains an
eigenvalue.  The definition uses the attained Euclidean least singular value
from `ConnectedPseudospectrum.LeastSingular`.
-/

namespace ConnectedPseudospectrum

open Matrix Set
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- The shifted matrix `zI - M` for an arbitrary finite complex square
matrix. -/
def generalShift {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  z • 1 - M

/-- The actual Euclidean least singular value of `zI - M`. -/
def generalPseudospectralHeight {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : ℝ :=
  leastSingularValue (generalShift M z)

/-- The strict open `ε`-pseudospectrum of an arbitrary finite complex square
matrix. -/
def generalPseudospectrum {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) : Set ℂ :=
  {z | generalPseudospectralHeight M z < ε}

theorem continuous_generalShift {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (generalShift M) := by
  unfold generalShift
  exact (continuous_id.smul continuous_const).sub continuous_const

theorem continuous_generalPseudospectralHeight {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (generalPseudospectralHeight M) :=
  (continuous_leastSingularValue n).comp (continuous_generalShift M)

theorem isOpen_generalPseudospectrum {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) :
    IsOpen (generalPseudospectrum M ε) := by
  exact isOpen_lt (continuous_generalPseudospectralHeight M) continuous_const

/-- In positive dimension, the least singular value of the scalar matrix
`zI` is exactly `‖z‖`. -/
theorem leastSingularValue_smul_one {n : ℕ} (hn : 0 < n) (z : ℂ) :
    leastSingularValue (z • (1 : Matrix (Fin n) (Fin n) ℂ)) = ‖z‖ := by
  rw [leastSingularValue_smul, leastSingularValue_one hn, mul_one]

/-- The reverse-triangle lower bound for the least singular value of a shifted
matrix. -/
theorem norm_sub_matrixNorm_le_generalPseudospectralHeight {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) (z : ℂ) :
    ‖z‖ - ‖M‖ ≤ generalPseudospectralHeight M z := by
  have hperturb := leastSingularValue_le_add_norm_sub
    (z • (1 : Matrix (Fin n) (Fin n) ℂ)) (generalShift M z)
  have hmatrix :
      z • (1 : Matrix (Fin n) (Fin n) ℂ) - generalShift M z = M := by
    simp [generalShift]
  rw [leastSingularValue_smul_one hn, hmatrix] at hperturb
  unfold generalPseudospectralHeight
  linarith

/-- The strict pseudospectrum lies in the explicit ball of radius
`ε + ‖M‖`. -/
theorem generalPseudospectrum_subset_ball {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) (ε : ℝ) :
    generalPseudospectrum M ε ⊆ Metric.ball 0 (ε + ‖M‖) := by
  intro z hz
  have hlower := norm_sub_matrixNorm_le_generalPseudospectralHeight M hn z
  have hheight : generalPseudospectralHeight M z < ε := hz
  rw [Metric.mem_ball, dist_zero_right]
  linarith

/-- For positive dimension (and in particular for positive `ε`), every
strict pseudospectrum is bounded. -/
theorem isBounded_generalPseudospectrum {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) :
    Bornology.IsBounded (generalPseudospectrum M ε) := by
  refine (Metric.isBounded_ball :
    Bornology.IsBounded (Metric.ball (0 : ℂ) ((ε + ‖M‖) + ε))).subset ?_
  intro z hz
  have hzball := generalPseudospectrum_subset_ball M hn ε hz
  rw [Metric.mem_ball, dist_zero_right] at hzball ⊢
  linarith

/-- A zero of `det (zI - M)` belongs to every positive strict
pseudospectrum. -/
theorem mem_generalPseudospectrum_of_det_generalShift_eq_zero {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : (generalShift M z).det = 0) :
    z ∈ generalPseudospectrum M ε := by
  have hzero : generalPseudospectralHeight M z = 0 := by
    exact (leastSingularValue_eq_zero_iff_det_eq_zero (generalShift M z) hn).2 hz
  change generalPseudospectralHeight M z < ε
  rw [hzero]
  exact hε

/-- Matrix-spectrum membership is equivalent to the familiar determinant
condition needed by the preceding pseudospectral inclusion. -/
theorem det_generalShift_eq_zero_of_mem_spectrum {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) {z : ℂ}
    (hz : z ∈ spectrum ℂ M) :
    (generalShift M z).det = 0 := by
  have hroot : M.charpoly.IsRoot z :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
  have hscalar :
      z • (1 : Matrix (Fin n) (Fin n) ℂ) = Matrix.scalar (Fin n) z := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  calc
    (generalShift M z).det = (Matrix.scalar (Fin n) z - M).det := by
      rw [generalShift, hscalar]
    _ = M.charpoly.eval z := (Matrix.eval_charpoly M z).symm
    _ = 0 := hroot

/-- Spectrum membership is exactly singularity of the shifted matrix. -/
theorem mem_spectrum_iff_det_generalShift_eq_zero {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    z ∈ spectrum ℂ M ↔ (generalShift M z).det = 0 := by
  constructor
  · exact det_generalShift_eq_zero_of_mem_spectrum M
  · intro hdet
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    have hscalar :
        z • (1 : Matrix (Fin n) (Fin n) ℂ) = Matrix.scalar (Fin n) z := by
      rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
    calc
      M.charpoly.eval z = (Matrix.scalar (Fin n) z - M).det :=
        Matrix.eval_charpoly M z
      _ = (generalShift M z).det := by rw [generalShift, hscalar]
      _ = 0 := hdet

/-- Every eigenvalue (encoded as matrix-spectrum membership) belongs to every
positive strict pseudospectrum. -/
theorem mem_generalPseudospectrum_of_mem_spectrum {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : z ∈ spectrum ℂ M) :
    z ∈ generalPseudospectrum M ε := by
  exact mem_generalPseudospectrum_of_det_generalShift_eq_zero M hn hε
    (det_generalShift_eq_zero_of_mem_spectrum M hz)

end

end ConnectedPseudospectrum
