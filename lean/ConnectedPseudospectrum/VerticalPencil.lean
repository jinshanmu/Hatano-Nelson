import ConnectedPseudospectrum.Definitions
import ConnectedPseudospectrum.PathAlgebra

/-!
# The Hermitian pencil for vertical monotonicity

This module formalizes the first algebraic segment of `lem:vertical`.  The
variable `Y` is kept real in the definition, while formulas replacing
`(√Y)²` by `Y` explicitly assume `0 ≤ Y`, as in the paper where `Y = y²`.
-/

namespace ConnectedPseudospectrum

open Matrix

noncomputable section

/-- The shifted matrix `(x + i√Y)Iₙ - Aₙ(a)` used in the vertical argument. -/
def verticalShiftedMatrix (n : ℕ) (a x Y : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  shiftedPathMatrix n a ((x : ℂ) + Complex.I * (Real.sqrt Y : ℂ))

/-- The Hermitian pencil
`Pₙ(Y,t) = ((x+i√Y)Iₙ-Aₙ)ᴴ ((x+i√Y)Iₙ-Aₙ) - t²Iₙ`. -/
def verticalPencil (n : ℕ) (a x Y t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (verticalShiftedMatrix n a x Y)ᴴ * verticalShiftedMatrix n a x Y -
    ((t ^ 2 : ℝ) : ℂ) • 1

/-- The determinant `Fₙ(Y,t)` of the vertical Hermitian pencil. -/
def verticalPencilDet (n : ℕ) (a x Y t : ℝ) : ℂ :=
  (verticalPencil n a x Y t).det

/-- The pencil is the Gram matrix of the shifted path, minus `t²I`. -/
theorem verticalPencil_eq_gram_sub (n : ℕ) (a x Y t : ℝ) :
    verticalPencil n a x Y t =
      (verticalShiftedMatrix n a x Y)ᴴ * verticalShiftedMatrix n a x Y -
        ((t ^ 2 : ℝ) : ℂ) • 1 :=
  rfl

/-- Adding back `t²I` recovers the Gram matrix exactly. -/
theorem verticalPencil_add_t_sq_one (n : ℕ) (a x Y t : ℝ) :
    verticalPencil n a x Y t + ((t ^ 2 : ℝ) : ℂ) • 1 =
      (verticalShiftedMatrix n a x Y)ᴴ * verticalShiftedMatrix n a x Y := by
  simp [verticalPencil]

/-- Entrywise form of the Gram-minus-scalar pencil. -/
theorem verticalPencil_apply (n : ℕ) (a x Y t : ℝ) (i j : Fin n) :
    verticalPencil n a x Y t i j =
      (∑ k : Fin n,
          star (verticalShiftedMatrix n a x Y k i) *
            verticalShiftedMatrix n a x Y k j) -
        ((t ^ 2 : ℝ) : ℂ) * if i = j then 1 else 0 := by
  classical
  simp [verticalPencil, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, smul_eq_mul]

/-- `Pₙ(Y,t)` is Hermitian in every dimension and for every real parameter. -/
theorem verticalPencil_isHermitian (n : ℕ) (a x Y t : ℝ) :
    (verticalPencil n a x Y t).IsHermitian := by
  apply (isHermitian_conjTranspose_mul_self (verticalShiftedMatrix n a x Y)).sub
  rw [Matrix.IsHermitian]
  simp

/-- The determinant convention in dimension zero is `F₀ = 1`. -/
@[simp] theorem verticalPencilDet_zero (a x Y t : ℝ) :
    verticalPencilDet 0 a x Y t = 1 := by
  exact Matrix.det_fin_zero

/-- In dimension one the two endpoint corrections coincide.  The resulting
matrix has the single entry `x² + Y - t²`, independently of `a`. -/
theorem verticalPencil_one (a x Y t : ℝ) (hY : 0 ≤ Y) :
    verticalPencil 1 a x Y t =
      Matrix.diagonal fun _ : Fin 1 => (((x ^ 2 + Y - t ^ 2 : ℝ) : ℂ)) := by
  classical
  ext i j
  fin_cases i
  fin_cases j
  have hsq : ((Real.sqrt Y : ℂ) ^ 2) = (Y : ℂ) := by
    exact_mod_cast Real.sq_sqrt hY
  have hprod :
      ((x : ℂ) + -(Complex.I * (Real.sqrt Y : ℂ))) *
          ((x : ℂ) + Complex.I * (Real.sqrt Y : ℂ)) =
        (x : ℂ) ^ 2 + (Y : ℂ) := by
    calc
      ((x : ℂ) + -(Complex.I * (Real.sqrt Y : ℂ))) *
            ((x : ℂ) + Complex.I * (Real.sqrt Y : ℂ)) =
          (x : ℂ) ^ 2 - (Complex.I * Complex.I) * (Real.sqrt Y : ℂ) ^ 2 := by ring
      _ = (x : ℂ) ^ 2 + (Real.sqrt Y : ℂ) ^ 2 := by rw [Complex.I_mul_I]; ring
      _ = (x : ℂ) ^ 2 + (Y : ℂ) := by rw [hsq]
  simp [verticalPencil, verticalShiftedMatrix, shiftedPathMatrix,
    complexPathMatrix, Matrix.mul_apply, Matrix.one_apply,
    smul_eq_mul, hprod]

/-- Consequently `F₁(Y,t) = x² + Y - t²`; in particular no endpoint
correction may be counted only once in dimension one. -/
@[simp] theorem verticalPencilDet_one (a x Y t : ℝ) (hY : 0 ≤ Y) :
    verticalPencilDet 1 a x Y t = ((x ^ 2 + Y - t ^ 2 : ℝ) : ℂ) := by
  rw [verticalPencilDet, verticalPencil_one a x Y t hY, Matrix.det_fin_one]
  simp

end

end ConnectedPseudospectrum
