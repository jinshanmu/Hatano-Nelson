import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

/-!
# Finite path matrices

Foundational definitions for the upper shift, reversal, and the finite
Hatano--Nelson path matrix.  Indexing is zero based in Lean.
-/

namespace ConnectedPseudospectrum

open Matrix

/-- The upper shift on a finite path. -/
def upperShift (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j.1 = i.1 + 1 then 1 else 0

/-- Reversal of the coordinates of a finite path. -/
def reversal (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i.1 + j.1 + 1 = n then 1 else 0

/-- The real finite Hatano--Nelson path matrix `Aₙ(a) = Vₙ + a Vₙᵀ`. -/
def pathMatrix (n : ℕ) (a : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  upperShift n + a • (upperShift n)ᵀ

@[simp] theorem upperShift_apply (n : ℕ) (i j : Fin n) :
    upperShift n i j = if j.1 = i.1 + 1 then 1 else 0 := rfl

@[simp] theorem reversal_apply (n : ℕ) (i j : Fin n) :
    reversal n i j = if i.1 + j.1 + 1 = n then 1 else 0 := rfl

@[simp] theorem pathMatrix_apply (n : ℕ) (a : ℝ) (i j : Fin n) :
    pathMatrix n a i j =
      (if j.1 = i.1 + 1 then 1 else 0) +
        a * (if i.1 = j.1 + 1 then 1 else 0) := by
  simp [pathMatrix, upperShift, Matrix.transpose_apply, smul_eq_mul]

theorem upperShift_transpose_apply (n : ℕ) (i j : Fin n) :
    (upperShift n)ᵀ i j = if i.1 = j.1 + 1 then 1 else 0 := rfl

end ConnectedPseudospectrum
