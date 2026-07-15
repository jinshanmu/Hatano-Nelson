import ConnectedPseudospectrum.FinitePath
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Algebra of finite path matrices

This module proves the reversal, reflection, and persymmetry identities used
for the finite Hatano--Nelson path.  All statements include the empty and
one-dimensional index types; no nonemptiness hypothesis is hidden in the
matrix algebra.
-/

namespace ConnectedPseudospectrum

open Matrix

/-- The lower shift, defined as the transpose of the upper shift. -/
def lowerShift (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (upperShift n)ᵀ

@[simp] theorem lowerShift_apply (n : ℕ) (i j : Fin n) :
    lowerShift n i j = if i.1 = j.1 + 1 then 1 else 0 := by
  rfl

theorem pathMatrix_eq_upper_add_lower (n : ℕ) (a : ℝ) :
    pathMatrix n a = upperShift n + a • lowerShift n := by
  rfl

theorem pathMatrix_transpose_eq_lower_add_upper (n : ℕ) (a : ℝ) :
    (pathMatrix n a)ᵀ = lowerShift n + a • upperShift n := by
  ext i j
  simp only [Matrix.transpose_apply, pathMatrix_apply, lowerShift_apply, upperShift_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

@[simp] theorem pathMatrix_zero_dim (a : ℝ) :
    pathMatrix 0 a = (0 : Matrix (Fin 0) (Fin 0) ℝ) := by
  ext i
  exact Fin.elim0 i

@[simp] theorem pathMatrix_one_dim (a : ℝ) :
    pathMatrix 1 a = (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
  ext i j
  simp [pathMatrix_apply]

private theorem reversal_condition_iff {n : ℕ} (i j : Fin n) :
    i.1 + j.1 + 1 = n ↔ j = i.rev := by
  constructor
  · intro h
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  · intro h
    subst j
    simp only [Fin.val_rev]
    omega

/-- Entrywise, reversal is the permutation matrix of `Fin.rev`. -/
theorem reversal_eq_revPerm (n : ℕ) :
    reversal n = (Fin.revPerm : Equiv.Perm (Fin n)).permMatrix ℝ := by
  ext i j
  rw [reversal_apply]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def]
  by_cases h : i.1 + j.1 + 1 = n
  · have hj : j = i.rev := (reversal_condition_iff i j).mp h
    have hsome : some ((Fin.revPerm : Equiv.Perm (Fin n)) i) = some j := by
      change some i.rev = some j
      rw [hj]
    rw [if_pos h, if_pos hsome]
  · have hj : j ≠ i.rev := fun hji => h ((reversal_condition_iff i j).mpr hji)
    have hsome : ¬some ((Fin.revPerm : Equiv.Perm (Fin n)) i) = some j := by
      intro heq
      change some i.rev = some j at heq
      exact hj (Option.some.inj heq).symm
    rw [if_neg h, if_neg hsome]

@[simp] theorem reversal_transpose (n : ℕ) :
    (reversal n)ᵀ = reversal n := by
  ext i j
  simp only [Matrix.transpose_apply, reversal_apply]
  congr 2
  omega

@[simp] theorem reversal_mulVec_apply (n : ℕ) (v : Fin n → ℝ) (i : Fin n) :
    (reversal n *ᵥ v) i = v i.rev := by
  rw [reversal_eq_revPerm, Matrix.permMatrix_mulVec]
  rfl

@[simp] theorem reversal_mul_apply (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    (reversal n * M) i j = M i.rev j := by
  rw [reversal_eq_revPerm]
  rw [PEquiv.toMatrix_toPEquiv_mul]
  rfl

@[simp] theorem mul_reversal_apply (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    (M * reversal n) i j = M i j.rev := by
  rw [reversal_eq_revPerm]
  rw [PEquiv.mul_toMatrix_toPEquiv]
  rfl

/-- Reversal is an involution, including on the zero-dimensional space. -/
@[simp] theorem reversal_mul_self (n : ℕ) :
    reversal n * reversal n = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp only [reversal_mul_apply, reversal_apply, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  split <;> split <;> simp_all <;> omega

/-- The upper shift is persymmetric with respect to reversal. -/
theorem upperShift_mul_reversal (n : ℕ) :
    upperShift n * reversal n = reversal n * lowerShift n := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [mul_reversal_apply, reversal_mul_apply, upperShift_apply, lowerShift_apply,
    Fin.val_rev]
  by_cases h : n - (j.1 + 1) = i.1 + 1
  · have h' : n - (i.1 + 1) = j.1 + 1 := by omega
    rw [if_pos h, if_pos h']
  · have h' : ¬n - (i.1 + 1) = j.1 + 1 := by omega
    rw [if_neg h, if_neg h']

/-- The lower shift is persymmetric with respect to reversal. -/
theorem lowerShift_mul_reversal (n : ℕ) :
    lowerShift n * reversal n = reversal n * upperShift n := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [mul_reversal_apply, reversal_mul_apply, upperShift_apply, lowerShift_apply,
    Fin.val_rev]
  by_cases h : i.1 = n - (j.1 + 1) + 1
  · have h' : j.1 = n - (i.1 + 1) + 1 := by omega
    rw [if_pos h, if_pos h']
  · have h' : ¬j.1 = n - (i.1 + 1) + 1 := by omega
    rw [if_neg h, if_neg h']

/-- The finite path matrix satisfies `A J = J Aᵀ`. -/
theorem pathMatrix_mul_reversal (n : ℕ) (a : ℝ) :
    pathMatrix n a * reversal n = reversal n * (pathMatrix n a)ᵀ := by
  rw [pathMatrix_transpose_eq_lower_add_upper, pathMatrix_eq_upper_add_lower]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_smul,
    upperShift_mul_reversal, lowerShift_mul_reversal]

/-- Alternating-sign reflection `diag(1,-1,1,-1,...)`. -/
def reflection (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => (-1 : ℝ) ^ i.1

@[simp] theorem reflection_apply (n : ℕ) (i j : Fin n) :
    reflection n i j = if i = j then (-1 : ℝ) ^ i.1 else 0 := by
  simp [reflection, Matrix.diagonal]

@[simp] theorem reflection_transpose (n : ℕ) :
    (reflection n)ᵀ = reflection n := by
  simp [reflection]

private theorem alternatingSign_sq (k : ℕ) :
    ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
  rw [← pow_add]
  have hEven : Even (k + k) := by
    exact ⟨k, by omega⟩
  exact hEven.neg_one_pow

private theorem alternatingSign_mul_succ (k : ℕ) :
    ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ (k + 1)) = -1 := by
  rw [pow_succ, ← mul_assoc, alternatingSign_sq]
  norm_num

/-- Alternating-sign reflection is an involution. -/
@[simp] theorem reflection_mul_self (n : ℕ) :
    reflection n * reflection n = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp only [reflection, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
    Matrix.one_apply]
  by_cases h : i = j
  · subst j
    simp [alternatingSign_sq]
  · simp [h]

/-- Reflection anticommutes with the upper shift. -/
theorem reflection_upperShift_reflection (n : ℕ) :
    reflection n * upperShift n * reflection n = -upperShift n := by
  ext i j
  simp only [reflection, Matrix.diagonal_mul, Matrix.mul_diagonal, upperShift_apply,
    Matrix.neg_apply]
  by_cases h : j.1 = i.1 + 1
  · simp only [h, if_true, mul_one]
    exact alternatingSign_mul_succ i.1
  · simp [h]

/-- Reflection anticommutes with the lower shift. -/
theorem reflection_lowerShift_reflection (n : ℕ) :
    reflection n * lowerShift n * reflection n = -lowerShift n := by
  ext i j
  simp only [reflection, Matrix.diagonal_mul, Matrix.mul_diagonal, lowerShift_apply,
    Matrix.neg_apply]
  by_cases h : i.1 = j.1 + 1
  · simp only [h, if_true, mul_one]
    simpa only [mul_comm] using alternatingSign_mul_succ j.1
  · simp [h]

/-- The path matrix has reflection sign symmetry `Σ A Σ = -A`. -/
theorem reflection_pathMatrix_reflection (n : ℕ) (a : ℝ) :
    reflection n * pathMatrix n a * reflection n = -pathMatrix n a := by
  rw [pathMatrix_eq_upper_add_lower]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    reflection_upperShift_reflection, reflection_lowerShift_reflection]
  simp only [smul_neg, neg_add]

end ConnectedPseudospectrum
