import ConnectedPseudospectrum.ComponentTopology
import ConnectedPseudospectrum.ResolventAnalytic

/-!
# Spectral points in pseudospectral components

The maximum-modulus argument in `lem:component` is valid for an arbitrary
finite complex square matrix.  If a component of a strict pseudospectrum had
no eigenvalue, the matrix-valued resolvent would be holomorphic on its
closure.  Its norm is at most `ε⁻¹` on the frontier, but is strictly larger
than `ε⁻¹` in the component, contradicting the maximum principle.
-/

namespace ConnectedPseudospectrum

open Matrix Set
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Every component of a positive strict finite-dimensional
pseudospectrum contains a zero of `det (zI-M)`. -/
theorem exists_det_generalShift_eq_zero_mem_component
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : z ∈ generalPseudospectrum M ε) :
    ∃ w ∈ connectedComponentIn (generalPseudospectrum M ε) z,
      (generalShift M w).det = 0 := by
  let Ω := generalPseudospectrum M ε
  let C := connectedComponentIn Ω z
  have hΩopen : IsOpen Ω := isOpen_generalPseudospectrum M ε
  have hzC : z ∈ C := mem_connectedComponentIn hz
  have hCbounded : Bornology.IsBounded C :=
    (isBounded_generalPseudospectrum M hn ε hε).subset
      (connectedComponentIn_subset Ω z)
  by_contra hcontra
  have hdetC : ∀ w ∈ C, (generalShift M w).det ≠ 0 := by
    intro w hw hzero
    exact hcontra ⟨w, hw, hzero⟩
  have hdetClosure : ∀ w ∈ closure C,
      (generalShift M w).det ≠ 0 := by
    intro w hw hzero
    have hwΩ : w ∈ Ω :=
      mem_generalPseudospectrum_of_det_generalShift_eq_zero M hn hε hzero
    have hwC : w ∈ C :=
      closure_connectedComponentIn_inter_subset hΩopen z ⟨hw, hwΩ⟩
    exact hdetC w hwC hzero
  have hdClosure : DifferentiableOn ℂ
      (fun w : ℂ => (generalShift M w)⁻¹) (closure C) := by
    intro w hw
    exact (differentiableAt_generalShift_inv M w
      (hdetClosure w hw)).differentiableWithinAt
  have hd : DiffContOnCl ℂ
      (fun w : ℂ => (generalShift M w)⁻¹) C :=
    hdClosure.diffContOnCl
  have hfrontier : ∀ w ∈ frontier C,
      ‖(generalShift M w)⁻¹‖ ≤ ε⁻¹ := by
    intro w hw
    have hwNotΩ : w ∉ Ω :=
      frontier_connectedComponentIn_subset_compl hΩopen z hw
    have hheight : ε ≤ generalPseudospectralHeight M w := by
      change ¬ generalPseudospectralHeight M w < ε at hwNotΩ
      exact not_lt.mp hwNotΩ
    have hwClosure : w ∈ closure C := frontier_subset_closure hw
    have hwdet : (generalShift M w).det ≠ 0 :=
      hdetClosure w hwClosure
    have hheightPos : 0 < generalPseudospectralHeight M w :=
      leastSingularValue_pos_of_det_ne_zero (generalShift M w) hn hwdet
    rw [norm_generalShift_inv_eq_inv_height M hn w hwdet]
    exact (inv_le_inv₀ hheightPos hε).2 hheight
  have hzClosure : z ∈ closure C := subset_closure hzC
  have hnormBound : ‖(generalShift M z)⁻¹‖ ≤ ε⁻¹ :=
    Complex.norm_le_of_forall_mem_frontier_norm_le hCbounded hd
      hfrontier hzClosure
  have hzdet : (generalShift M z).det ≠ 0 :=
    hdetClosure z hzClosure
  have hzheightPos : 0 < generalPseudospectralHeight M z :=
    leastSingularValue_pos_of_det_ne_zero (generalShift M z) hn hzdet
  have hzheight : generalPseudospectralHeight M z < ε := hz
  have hstrict : ε⁻¹ < (generalPseudospectralHeight M z)⁻¹ :=
    (inv_lt_inv₀ hε hzheightPos).2 hzheight
  rw [norm_generalShift_inv_eq_inv_height M hn z hzdet] at hnormBound
  exact (not_lt_of_ge hnormBound) hstrict

/-- Every component of a positive strict finite-dimensional
pseudospectrum contains an eigenvalue of the matrix. -/
theorem exists_mem_spectrum_mem_pseudospectral_component
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε) {z : ℂ}
    (hz : z ∈ generalPseudospectrum M ε) :
    ∃ w ∈ connectedComponentIn (generalPseudospectrum M ε) z,
      w ∈ spectrum ℂ M := by
  obtain ⟨w, hwC, hwdet⟩ :=
    exists_det_generalShift_eq_zero_mem_component M hn hε hz
  refine ⟨w, hwC, Matrix.mem_spectrum_iff_isRoot_charpoly.mpr ?_⟩
  have hscalar :
      w • (1 : Matrix (Fin n) (Fin n) ℂ) = Matrix.scalar (Fin n) w := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
  have heval : M.charpoly.eval w = 0 := by
    calc
      M.charpoly.eval w = (Matrix.scalar (Fin n) w - M).det :=
        Matrix.eval_charpoly M w
      _ = (generalShift M w).det := by rw [generalShift, hscalar]
      _ = 0 := hwdet
  exact heval

end

end ConnectedPseudospectrum
