import ConnectedPseudospectrum.FoldedTransfer

/-!
# Boundary data for the folded generating functions

This module specializes the folded transfer to its even and odd initial
states.  It proves the fourth-order recurrence and all four boundary
residuals used in `eq:fold-generating-even` and `eq:fold-generating-odd`.
-/

namespace ConnectedPseudospectrum

open Matrix

noncomputable section

/-- The scalar `ζ_s` in the numerator of the even folded generating
function. -/
def foldZeta (a s : ℝ) : ℝ :=
  (1 + a ^ 2 + (1 + a) * s) / (2 * a)

/-- The first coordinate of the even folded transfer orbit. -/
def foldEvenSequence (a x s : ℝ) (m : ℕ) : ℝ :=
  foldTransferCoordinate a x s (foldEvenInitial a) 0 m

/-- The first coordinate of the odd folded transfer orbit. -/
def foldOddSequence (a x s : ℝ) (m : ℕ) : ℝ :=
  foldTransferCoordinate a x s (foldOddInitial x s) 0 m

/-- The even folded transfer sequence satisfies `eq:fold-recurrence`. -/
theorem foldEvenSequence_recurrence
    {a x s : ℝ} (ha1 : a ≠ 1) (m : ℕ) :
    foldEvenSequence a x s (m + 4) -
        foldC0 a x s * foldEvenSequence a x s (m + 3) +
        foldB a x s * foldEvenSequence a x s (m + 2) -
        a ^ 2 * foldC0 a x s * foldEvenSequence a x s (m + 1) +
        a ^ 4 * foldEvenSequence a x s m = 0 := by
  exact foldTransferCoordinate_recurrence ha1 (foldEvenInitial a) 0 m

/-- The odd folded transfer sequence satisfies `eq:fold-recurrence`. -/
theorem foldOddSequence_recurrence
    {a x s : ℝ} (ha1 : a ≠ 1) (m : ℕ) :
    foldOddSequence a x s (m + 4) -
        foldC0 a x s * foldOddSequence a x s (m + 3) +
        foldB a x s * foldOddSequence a x s (m + 2) -
        a ^ 2 * foldC0 a x s * foldOddSequence a x s (m + 1) +
        a ^ 4 * foldOddSequence a x s m = 0 := by
  exact foldTransferCoordinate_recurrence ha1 (foldOddInitial x s) 0 m

/-- The zeroth even folded coefficient. -/
theorem foldEvenSequence_zero (a x s : ℝ) :
    foldEvenSequence a x s 0 = 1 := by
  simp [foldEvenSequence, foldTransferCoordinate, foldEvenInitial]

/-- The zeroth odd folded coefficient. -/
theorem foldOddSequence_zero (a x s : ℝ) :
    foldOddSequence a x s 0 = x - s := by
  simp [foldOddSequence, foldTransferCoordinate, foldOddInitial]

/-- The degree-one boundary residual for the even folded sequence. -/
theorem foldEvenSequence_residual_one
    {a x s : ℝ} (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    foldEvenSequence a x s 1 - foldC0 a x s * foldEvenSequence a x s 0 =
      a * (1 - 2 * foldZeta a s) := by
  rw [foldEvenSequence_zero]
  rw [show foldEvenSequence a x s 1 =
      x ^ 2 - (1 + s) * (a + s) by
    simp only [foldEvenSequence, foldTransferCoordinate, pow_one]
    rw [foldTransfer_mulVec_evenInitial ha1]
    rfl]
  simp only [foldC0, foldZeta]
  field_simp [ha0]
  ring

/-- The degree-one boundary residual for the odd folded sequence. -/
theorem foldOddSequence_residual_one
    {a x s : ℝ} (ha1 : a ≠ 1) :
    foldOddSequence a x s 1 - foldC0 a x s * foldOddSequence a x s 0 =
      -(x * (1 + a ^ 2) + 2 * a * s) := by
  rw [foldOddSequence_zero]
  rw [show foldOddSequence a x s 1 =
      foldC0 a x s * (x - s) - x * (1 + a ^ 2) - 2 * a * s by
    simp only [foldOddSequence, foldTransferCoordinate, pow_one]
    rw [foldTransfer_mulVec_oddInitial ha1]
    rfl]
  ring

/-- The degree-two boundary residual for the even folded sequence. -/
theorem foldEvenSequence_residual_two
    {a x s : ℝ} (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    foldEvenSequence a x s 2 -
        foldC0 a x s * foldEvenSequence a x s 1 +
        foldB a x s * foldEvenSequence a x s 0 =
      a ^ 2 * (1 - 2 * foldZeta a s) := by
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  simp [foldEvenSequence, foldTransferCoordinate, foldEvenInitial,
    foldTransfer, foldC0, foldB, foldZeta, pow_succ, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  field_simp [ha0, hden]
  ring

/-- The degree-two boundary residual for the odd folded sequence. -/
theorem foldOddSequence_residual_two
    {a x s : ℝ} (ha1 : a ≠ 1) :
    foldOddSequence a x s 2 -
        foldC0 a x s * foldOddSequence a x s 1 +
        foldB a x s * foldOddSequence a x s 0 =
      a ^ 2 * (x - s) := by
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  simp [foldOddSequence, foldTransferCoordinate, foldOddInitial,
    foldTransfer, foldC0, foldB, pow_succ, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  field_simp [hden]
  ring

/-- The degree-three boundary residual for the even folded sequence. -/
theorem foldEvenSequence_residual_three
    {a x s : ℝ} (ha1 : a ≠ 1) :
    foldEvenSequence a x s 3 -
        foldC0 a x s * foldEvenSequence a x s 2 +
        foldB a x s * foldEvenSequence a x s 1 -
        a ^ 2 * foldC0 a x s * foldEvenSequence a x s 0 = a ^ 3 := by
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  simp [foldEvenSequence, foldTransferCoordinate, foldEvenInitial,
    foldTransfer, foldC0, foldB, pow_succ, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  field_simp [hden]
  ring

/-- The degree-three boundary residual for the odd folded sequence. -/
theorem foldOddSequence_residual_three
    {a x s : ℝ} (ha1 : a ≠ 1) :
    foldOddSequence a x s 3 -
        foldC0 a x s * foldOddSequence a x s 2 +
        foldB a x s * foldOddSequence a x s 1 -
        a ^ 2 * foldC0 a x s * foldOddSequence a x s 0 = 0 := by
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  simp [foldOddSequence, foldTransferCoordinate, foldOddInitial,
    foldTransfer, foldC0, foldB, pow_succ, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  field_simp [hden]
  ring

end


end ConnectedPseudospectrum
