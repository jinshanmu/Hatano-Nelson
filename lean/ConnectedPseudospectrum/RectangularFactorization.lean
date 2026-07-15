import ConnectedPseudospectrum.VerticalToeplitz
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Rectangular path factorization

This module begins the lower-bound half of `prop:gap-bounds`.  It constructs
the two boundary-padding isometries from `ℂⁿ` to `ℂⁿ⁺¹`, computes all four
mixed Gram products, and derives the exact rectangular factorization
`D* C = xI - Aₙ` before any norm estimate is applied.
-/

namespace ConnectedPseudospectrum

open Matrix
open scoped ComplexConjugate

noncomputable section

/-- Pad an `n`-vector by a zero in its first coordinate. -/
def padFirstMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) ℂ :=
  fun i j => if i = Fin.succ j then 1 else 0

/-- Pad an `n`-vector by a zero in its last coordinate. -/
def padLastMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) ℂ :=
  fun i j => if i = Fin.castSucc j then 1 else 0

@[simp] theorem padFirstMatrix_apply (n : ℕ) (i : Fin (n + 1)) (j : Fin n) :
    padFirstMatrix n i j = if i = Fin.succ j then 1 else 0 :=
  rfl

@[simp] theorem padLastMatrix_apply (n : ℕ) (i : Fin (n + 1)) (j : Fin n) :
    padLastMatrix n i j = if i = Fin.castSucc j then 1 else 0 :=
  rfl

/-- Padding at the first coordinate is an isometry at the Gram-matrix level. -/
@[simp] theorem padFirstMatrix_gram (n : ℕ) :
    (padFirstMatrix n)ᴴ * padFirstMatrix n =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single (Fin.succ i)]
    · simp [padFirstMatrix, Matrix.conjTranspose_apply]
    · intro k hk hki
      have hkne : k ≠ Fin.succ i := hki
      simp [padFirstMatrix, Matrix.conjTranspose_apply, hkne]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro k hk
      by_cases hki : k = Fin.succ i
      · subst k
        simp [padFirstMatrix, Matrix.conjTranspose_apply, hij]
      · simp [padFirstMatrix, Matrix.conjTranspose_apply, hki]

/-- Padding at the last coordinate is an isometry at the Gram-matrix level. -/
@[simp] theorem padLastMatrix_gram (n : ℕ) :
    (padLastMatrix n)ᴴ * padLastMatrix n =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single (Fin.castSucc i)]
    · simp [padLastMatrix, Matrix.conjTranspose_apply]
    · intro k hk hki
      have hkne : k ≠ Fin.castSucc i := hki
      simp [padLastMatrix, Matrix.conjTranspose_apply, hkne]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro k hk
      by_cases hki : k = Fin.castSucc i
      · subst k
        simp [padLastMatrix, Matrix.conjTranspose_apply, hij]
      · simp [padLastMatrix, Matrix.conjTranspose_apply, hki]

/-- The first mixed Gram product is the upper path shift. -/
@[simp] theorem padFirstMatrix_star_mul_padLastMatrix (n : ℕ) :
    (padFirstMatrix n)ᴴ * padLastMatrix n = complexUpperShift n := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hcross : Fin.succ i = Fin.castSucc j
  · rw [Finset.sum_eq_single (Fin.succ i)]
    · have hval : j.1 = i.1 + 1 := by
        simpa only [Fin.val_succ, Fin.val_castSucc] using congrArg Fin.val hcross.symm
      simp [padFirstMatrix, padLastMatrix, Matrix.conjTranspose_apply,
        hcross, complexUpperShift_apply, hval]
    · intro k hk hki
      simp [padFirstMatrix, Matrix.conjTranspose_apply, hki]
    · simp
  · rw [Finset.sum_eq_zero]
    · have hval : j.1 ≠ i.1 + 1 := by
        intro h
        apply hcross
        apply Fin.ext
        simpa only [Fin.val_succ, Fin.val_castSucc] using h.symm
      simp [complexUpperShift_apply, hval]
    · intro k hk
      by_cases hki : k = Fin.succ i
      · subst k
        simp [padFirstMatrix, padLastMatrix, Matrix.conjTranspose_apply, hcross]
      · simp [padFirstMatrix, Matrix.conjTranspose_apply, hki]

/-- The other mixed Gram product is the lower path shift. -/
@[simp] theorem padLastMatrix_star_mul_padFirstMatrix (n : ℕ) :
    (padLastMatrix n)ᴴ * padFirstMatrix n = complexLowerShift n := by
  calc
    (padLastMatrix n)ᴴ * padFirstMatrix n =
        ((padFirstMatrix n)ᴴ * padLastMatrix n)ᴴ := by
      simp only [Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    _ = (complexUpperShift n)ᴴ := by
      rw [padFirstMatrix_star_mul_padLastMatrix]
    _ = complexLowerShift n := complexUpperShift_conjTranspose n

/-- The paper's first rectangular factor.  On a vector `u`, its row `j`
is `p u_j - u_{j+1}`, with the two missing endpoint coordinates set to zero. -/
def rectangularC (n : ℕ) (p : ℂ) : Matrix (Fin (n + 1)) (Fin n) ℂ :=
  p • padFirstMatrix n - padLastMatrix n

/-- The paper's second rectangular factor.  Its row `j` is
`u_j - conj(q) u_{j+1}`. -/
def rectangularD (n : ℕ) (q : ℂ) : Matrix (Fin (n + 1)) (Fin n) ℂ :=
  padFirstMatrix n - conj q • padLastMatrix n

/-- Exact Gram matrix of the first rectangular factor. -/
theorem rectangularC_gram (n : ℕ) (p : ℂ) :
    (rectangularC n p)ᴴ * rectangularC n p =
      (conj p * p + 1) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        conj p • complexUpperShift n - p • complexLowerShift n := by
  simp only [rectangularC, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, starRingEnd_apply, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, padFirstMatrix_gram,
    padLastMatrix_gram, padFirstMatrix_star_mul_padLastMatrix,
    padLastMatrix_star_mul_padFirstMatrix]
  module

/-- Exact Gram matrix of the second rectangular factor. -/
theorem rectangularD_gram (n : ℕ) (q : ℂ) :
    (rectangularD n q)ᴴ * rectangularD n q =
      (1 + q * conj q) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        conj q • complexUpperShift n - q • complexLowerShift n := by
  simp only [rectangularD, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, starRingEnd_apply, star_star, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, padFirstMatrix_gram,
    padLastMatrix_gram, padFirstMatrix_star_mul_padLastMatrix,
    padLastMatrix_star_mul_padFirstMatrix]
  module

/-- Algebraic rectangular factorization for arbitrary parameters `p,q`. -/
theorem rectangularD_star_mul_rectangularC (n : ℕ) (p q : ℂ) :
    (rectangularD n q)ᴴ * rectangularC n p =
      (p + q) • (1 : Matrix (Fin n) (Fin n) ℂ) -
        complexUpperShift n - (p * q) • complexLowerShift n := by
  simp only [rectangularC, rectangularD, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, starRingEnd_apply, star_star,
    Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, padFirstMatrix_gram, padLastMatrix_gram,
    padFirstMatrix_star_mul_padLastMatrix, padLastMatrix_star_mul_padFirstMatrix]
  module

/-- The two characteristic roots used in the lower gap bound. -/
def pathRootPlus (r θ : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)

/-- The characteristic root with argument `-θ` and modulus `r`. -/
def pathRootMinus (r θ : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp ((-θ : ℂ) * Complex.I)

/-- The characteristic roots have the required sum. -/
theorem pathRootPlus_add_pathRootMinus (r θ : ℝ) :
    pathRootPlus r θ + pathRootMinus r θ =
      ((2 * r * Real.cos θ : ℝ) : ℂ) := by
  rw [pathRootPlus, pathRootMinus, Complex.exp_mul_I, Complex.exp_mul_I]
  simp
  ring

/-- The characteristic roots have product `r²`. -/
theorem pathRootPlus_mul_pathRootMinus (r θ : ℝ) :
    pathRootPlus r θ * pathRootMinus r θ = ((r ^ 2 : ℝ) : ℂ) := by
  rw [pathRootPlus, pathRootMinus]
  rw [mul_assoc, mul_left_comm (Complex.exp _), ← mul_assoc,
    ← Complex.exp_add]
  simp
  ring

/-- Exact specialization to the shifted finite path matrix. -/
theorem rectangular_path_factorization (n : ℕ) (r θ : ℝ) :
    (rectangularD n (pathRootMinus r θ))ᴴ *
        rectangularC n (pathRootPlus r θ) =
      ((2 * r * Real.cos θ) • (1 : Matrix (Fin n) (Fin n) ℝ) -
        pathMatrix n (r ^ 2)).map Complex.ofRealHom := by
  rw [rectangularD_star_mul_rectangularC,
    pathRootPlus_add_pathRootMinus, pathRootPlus_mul_pathRootMinus]
  ext i j
  simp only [pathMatrix_eq_upper_add_lower, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, complexUpperShift_apply,
    complexLowerShift_apply, Matrix.map_apply, Matrix.add_apply,
    upperShift_apply, lowerShift_apply, smul_eq_mul,
    Complex.ofRealHom_eq_coe]
  split_ifs <;> push_cast <;> ring

end

end ConnectedPseudospectrum
