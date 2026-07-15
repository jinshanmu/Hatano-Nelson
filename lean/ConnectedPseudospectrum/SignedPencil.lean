import ConnectedPseudospectrum.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The real symmetric signed pencil

Persymmetry converts the real shifted Hatano--Nelson path into the symmetric
matrix `Bₙ(x)=(xI-Aₙ)Jₙ`.  This module records the exact matrix and determinant
identities underlying the signed middle branch in `lem:mesh`.
-/

namespace ConnectedPseudospectrum

open Matrix

noncomputable section

/-- The real symmetric matrix `Bₙ(x)=(xI-Aₙ)Jₙ`. -/
def signedMiddleMatrix (n : ℕ) (a x : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (x • 1 - pathMatrix n a) * reversal n

/-- The paper's signed determinant pencil `xI-Aₙ-sJₙ`. -/
def signedPencil (n : ℕ) (a x s : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  x • 1 - pathMatrix n a - s • reversal n

/-- The determinant `qₙ(x,s)` of the signed pencil. -/
def signedPencilDet (n : ℕ) (a x s : ℝ) : ℝ :=
  (signedPencil n a x s).det

/-- Persymmetry makes `Bₙ(x)` real symmetric. -/
theorem signedMiddleMatrix_isSymm (n : ℕ) (a x : ℝ) :
    (signedMiddleMatrix n a x).IsSymm := by
  rw [Matrix.IsSymm, signedMiddleMatrix, Matrix.transpose_mul,
    reversal_transpose, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul,
    pathMatrix_mul_reversal]
  simp

/-- The reversal matrix is orthogonal. -/
theorem reversal_mem_orthogonal (n : ℕ) :
    reversal n ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff, reversal_transpose,
    reversal_mul_self]

/-- Multiplying the signed pencil by reversal produces the ordinary scalar
eigenvalue pencil of `Bₙ(x)`. -/
theorem signedPencil_mul_reversal (n : ℕ) (a x s : ℝ) :
    signedPencil n a x s * reversal n =
      signedMiddleMatrix n a x - s • 1 := by
  rw [signedPencil, signedMiddleMatrix, Matrix.sub_mul, Matrix.smul_mul,
    reversal_mul_self]

/-- Exact determinant relation, including the orientation factor `det Jₙ`. -/
theorem signedPencilDet_mul_det_reversal (n : ℕ) (a x s : ℝ) :
    signedPencilDet n a x s * (reversal n).det =
      (signedMiddleMatrix n a x - s • 1).det := by
  rw [signedPencilDet, ← Matrix.det_mul, signedPencil_mul_reversal]

/-- Since reversal is invertible, signed-pencil roots are exactly the real
eigenvalue roots of `Bₙ(x)`. -/
theorem signedPencilDet_eq_zero_iff (n : ℕ) (a x s : ℝ) :
    signedPencilDet n a x s = 0 ↔
      (signedMiddleMatrix n a x - s • 1).det = 0 := by
  have hunit : IsUnit (reversal n).det :=
    Matrix.isUnit_det_of_right_inverse (reversal_mul_self n)
  rw [← signedPencilDet_mul_det_reversal]
  exact (mul_eq_zero_iff_right hunit.ne_zero).symm

/-- Complex cast of the real reversal matrix. -/
def complexReversal (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (reversal n).map Complex.ofRealHom

@[simp] theorem complexReversal_star (n : ℕ) :
    star (complexReversal n) = complexReversal n := by
  ext i j
  simp [complexReversal, reversal_apply, add_comm]

/-- The complex cast of reversal is unitary. -/
theorem complexReversal_mem_unitary (n : ℕ) :
    complexReversal n ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, complexReversal_star]
  rw [complexReversal, ← Matrix.map_mul, reversal_mul_self]
  simp

/-- A real spectral shift cast to `ℂ` is the complex shifted path matrix. -/
theorem shiftedPathMatrix_ofReal_eq_map (n : ℕ) (a x : ℝ) :
    shiftedPathMatrix n a (x : ℂ) =
      (x • 1 - pathMatrix n a).map Complex.ofRealHom := by
  ext i j
  by_cases hij : i = j <;>
    simp [shiftedPathMatrix, complexPathMatrix, Matrix.map_apply,
      hij]

/-- The shifted complex path times reversal is the complex cast of the real
symmetric middle matrix. -/
theorem shiftedPathMatrix_mul_complexReversal (n : ℕ) (a x : ℝ) :
    shiftedPathMatrix n a (x : ℂ) * complexReversal n =
      (signedMiddleMatrix n a x).map Complex.ofRealHom := by
  rw [signedMiddleMatrix, Matrix.map_mul, shiftedPathMatrix_ofReal_eq_map,
    complexReversal]

/-- Right multiplication by reversal leaves the actual Euclidean least
singular value unchanged. -/
theorem leastSingularValue_signedMiddleMatrix (n : ℕ) (a x : ℝ) :
    leastSingularValue
        ((signedMiddleMatrix n a x).map Complex.ofRealHom) =
      pseudospectralHeight n a (x : ℂ) := by
  rw [← shiftedPathMatrix_mul_complexReversal]
  exact leastSingularValue_mul_unitary
    (shiftedPathMatrix n a (x : ℂ)) (complexReversal n)
      (complexReversal_mem_unitary n)

end

end ConnectedPseudospectrum
