import ConnectedPseudospectrum.PositivePrincipalSubmatrix
import ConnectedPseudospectrum.VerticalContinuant

/-!
# Positive leading and trailing minors of the vertical pencil

For a positive-definite vertical pencil, every proper leading and trailing
principal block is positive definite.  The exact Toeplitz endpoint formulas
identify their determinants with the paper's `D_k` and `R_k`.
-/

namespace ConnectedPseudospectrum

open Matrix
open scoped ComplexOrder

noncomputable section

/-- A proper leading principal block of the full vertical pencil is the
first-endpoint-corrected Toeplitz matrix. -/
theorem verticalPencil_leading_submatrix
    (k q : ℕ) (hk : 0 < k) (a x Y t : ℝ) (hY : 0 ≤ Y) :
    (verticalPencil (k + (q + 1)) a x Y t).submatrix
        (Fin.castAdd (q + 1)) (Fin.castAdd (q + 1)) =
      leadingCorrectedToeplitz k a x Y t := by
  ext i j
  rw [Matrix.submatrix_apply,
    verticalPencil_apply_eq_verticalToeplitz_sub_endpoints
      (k + (q + 1)) (by omega) a x Y t hY]
  simp only [leadingCorrectedToeplitz, Matrix.sub_apply,
    firstEndpointCorrection]
  rw [verticalToeplitz_apply, verticalToeplitz_apply]
  have heq :
      (Fin.castAdd (q + 1) i = Fin.castAdd (q + 1) j) ↔ i = j :=
    (Fin.castAdd_injective k (q + 1)).eq_iff
  have hlast : i.1 + 1 ≠ k + (q + 1) := by omega
  simp only [Fin.val_castAdd, heq, hlast, and_false, if_false]
  ring

/-- A proper trailing principal block of the full vertical pencil is the
last-endpoint-corrected Toeplitz matrix. -/
theorem verticalPencil_trailing_submatrix
    (k q : ℕ) (hk : 0 < k) (a x Y t : ℝ) (hY : 0 ≤ Y) :
    (verticalPencil ((q + 1) + k) a x Y t).submatrix
        (Fin.natAdd (q + 1)) (Fin.natAdd (q + 1)) =
      trailingCorrectedToeplitz k a x Y t := by
  ext i j
  rw [Matrix.submatrix_apply,
    verticalPencil_apply_eq_verticalToeplitz_sub_endpoints
      ((q + 1) + k) (by omega) a x Y t hY]
  simp only [trailingCorrectedToeplitz, Matrix.sub_apply,
    lastEndpointCorrection]
  rw [verticalToeplitz_apply, verticalToeplitz_apply]
  have heq :
      (Fin.natAdd (q + 1) i = Fin.natAdd (q + 1) j) ↔ i = j :=
    (Fin.natAdd_injective k (q + 1)).eq_iff
  have hupOne :
      q + 1 + j.1 = q + 1 + i.1 + 1 ↔ j.1 = i.1 + 1 := by omega
  have hlowOne :
      q + 1 + i.1 = q + 1 + j.1 + 1 ↔ i.1 = j.1 + 1 := by omega
  have hupTwo :
      q + 1 + j.1 = q + 1 + i.1 + 2 ↔ j.1 = i.1 + 2 := by omega
  have hlowTwo :
      q + 1 + i.1 = q + 1 + j.1 + 2 ↔ i.1 = j.1 + 2 := by omega
  have hfirst : ¬(i = j ∧ q + 1 + i.1 = 0) := by omega
  have hlast :
      (i = j ∧ q + 1 + i.1 + 1 = q + 1 + k) ↔
        (i = j ∧ i.1 + 1 = k) := by omega
  simp only [Fin.val_natAdd, heq, hupOne, hlowOne, hupTwo, hlowTwo,
    hfirst, hlast, if_false]
  ring

/-- Positive definiteness of the full pencil forces every proper leading
minor `D_k` to be strictly positive. -/
theorem verticalLeadingMinor_pos_of_posDef
    (k q : ℕ) (hk : 0 < k) (a x Y t : ℝ) (hY : 0 ≤ Y)
    (hpos : (verticalPencil (k + (q + 1)) a x Y t).PosDef) :
    0 < verticalLeadingMinor k a x Y t := by
  have hminor := det_submatrix_pos_of_posDef
    (verticalPencil (k + (q + 1)) a x Y t) hpos
    (Fin.castAdd (q + 1)) (Fin.castAdd_injective k (q + 1))
  rw [verticalPencil_leading_submatrix k q hk a x Y t hY,
    det_leadingCorrectedToeplitz] at hminor
  exact hminor

/-- Positive definiteness of the full pencil forces every proper trailing
minor `R_k` to be strictly positive. -/
theorem verticalTrailingMinor_pos_of_posDef
    (k q : ℕ) (hk : 0 < k) (a x Y t : ℝ) (hY : 0 ≤ Y)
    (hpos : (verticalPencil ((q + 1) + k) a x Y t).PosDef) :
    0 < verticalTrailingMinor k a x Y t := by
  have hminor := det_submatrix_pos_of_posDef
    (verticalPencil ((q + 1) + k) a x Y t) hpos
    (Fin.natAdd (q + 1)) (Fin.natAdd_injective k (q + 1))
  rw [verticalPencil_trailing_submatrix k q hk a x Y t hY,
    det_trailingCorrectedToeplitz] at hminor
  exact hminor

end

end ConnectedPseudospectrum
