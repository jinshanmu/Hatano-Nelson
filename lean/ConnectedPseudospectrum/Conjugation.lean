import ConnectedPseudospectrum.Definitions

/-!
# Complex-conjugation symmetry

This module proves, directly from the attained Euclidean definition, that
entrywise complex conjugation preserves least singular values.  Since the
finite path matrix is real, this gives the conjugation symmetry of its
pseudospectral height and strict pseudospectrum used in the topological
argument following `lem:component`.
-/

namespace ConnectedPseudospectrum

open Matrix Set
open scoped ComplexConjugate

noncomputable section

/-- Coordinatewise complex conjugation on Euclidean coordinate space. -/
def conjugateVector {n : ℕ} (v : ComplexEuclidean n) : ComplexEuclidean n :=
  WithLp.toLp 2 fun i => conj (v i)

@[simp] theorem conjugateVector_apply {n : ℕ} (v : ComplexEuclidean n) (i : Fin n) :
    conjugateVector v i = conj (v i) :=
  rfl

/-- Coordinatewise conjugation is an isometry for the Euclidean norm. -/
@[simp] theorem norm_conjugateVector {n : ℕ} (v : ComplexEuclidean n) :
    ‖conjugateVector v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- Coordinatewise conjugation is involutive. -/
@[simp] theorem conjugateVector_conjugateVector {n : ℕ} (v : ComplexEuclidean n) :
    conjugateVector (conjugateVector v) = v := by
  ext i
  simp

/-- Entrywise complex conjugation of a matrix (without transposition). -/
def conjugateMatrix {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin m) (Fin n) ℂ :=
  fun i j => conj (M i j)

@[simp] theorem conjugateMatrix_apply {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    conjugateMatrix M i j = conj (M i j) :=
  rfl

/-- Entrywise matrix conjugation is involutive. -/
@[simp] theorem conjugateMatrix_conjugateMatrix {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    conjugateMatrix (conjugateMatrix M) = M := by
  ext i j
  simp

/-- Matrix-vector multiplication commutes with simultaneous conjugation. -/
theorem conjugateMatrix_mulVec_conjugate {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) (i : Fin m) :
    (conjugateMatrix M *ᵥ fun j => conj (v j)) i =
      conj ((M *ᵥ v) i) := by
  simp [Matrix.mulVec, dotProduct, conjugateMatrix]

/-- The Euclidean matrix action commutes with simultaneous conjugation. -/
theorem matrixOperator_conjugateMatrix_conjugateVector {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (v : ComplexEuclidean n) :
    matrixOperator (conjugateMatrix M) (conjugateVector v) =
      conjugateVector (matrixOperator M v) := by
  change WithLp.toLp 2
      ((conjugateMatrix M).mulVec fun j => conj (v j)) =
    WithLp.toLp 2 (fun i => conj ((M.mulVec (WithLp.ofLp v)) i))
  congr 1
  funext i
  exact conjugateMatrix_mulVec_conjugate M (WithLp.ofLp v) i

/-- Entrywise complex conjugation preserves the actual Euclidean least
singular value. -/
@[simp] theorem leastSingularValue_conjugateMatrix {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) :
    leastSingularValue (conjugateMatrix M) = leastSingularValue M := by
  apply le_antisymm
  · by_cases hn : 0 < n
    · let v := leastSingularVector M
      calc
        leastSingularValue (conjugateMatrix M) ≤
            ‖matrixOperator (conjugateMatrix M) (conjugateVector v)‖ :=
          leastSingularValue_le (conjugateMatrix M) hn (conjugateVector v) (by
            simp [v, norm_leastSingularVector M hn])
        _ = ‖matrixOperator M v‖ := by
          rw [matrixOperator_conjugateMatrix_conjugateVector, norm_conjugateVector]
        _ = leastSingularValue M := by
          simp [leastSingularValue, v]
    · have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simp
  · by_cases hn : 0 < n
    · let v := leastSingularVector (conjugateMatrix M)
      calc
        leastSingularValue M =
            leastSingularValue (conjugateMatrix (conjugateMatrix M)) := by simp
        _ ≤ ‖matrixOperator (conjugateMatrix (conjugateMatrix M))
              (conjugateVector v)‖ :=
          leastSingularValue_le (conjugateMatrix (conjugateMatrix M)) hn
            (conjugateVector v) (by
              simp [v, norm_leastSingularVector (conjugateMatrix M) hn])
        _ = ‖matrixOperator (conjugateMatrix M) v‖ := by
          rw [matrixOperator_conjugateMatrix_conjugateVector, norm_conjugateVector]
        _ = leastSingularValue (conjugateMatrix M) := by
          simp [leastSingularValue, v]
    · have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simp

/-- The real path matrix commutes with entrywise conjugation after casting to
complex scalars. -/
@[simp] theorem conjugateMatrix_complexPathMatrix (n : ℕ) (a : ℝ) :
    conjugateMatrix (complexPathMatrix n a) = complexPathMatrix n a := by
  ext i j
  simp [conjugateMatrix, complexPathMatrix_apply]

/-- Conjugating the shifted real path matrix conjugates its spectral
parameter. -/
@[simp] theorem conjugateMatrix_shiftedPathMatrix (n : ℕ) (a : ℝ) (z : ℂ) :
    conjugateMatrix (shiftedPathMatrix n a z) =
      shiftedPathMatrix n a (conj z) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [shiftedPathMatrix, conjugateMatrix, complexPathMatrix_apply]
  · simp [shiftedPathMatrix, conjugateMatrix, complexPathMatrix_apply, hij]

/-- The least-singular-value height of the real path is conjugation
invariant. -/
@[simp] theorem pseudospectralHeight_conj (n : ℕ) (a : ℝ) (z : ℂ) :
    pseudospectralHeight n a (conj z) =
      pseudospectralHeight n a z := by
  change leastSingularValue (shiftedPathMatrix n a (conj z)) =
    leastSingularValue (shiftedPathMatrix n a z)
  rw [← conjugateMatrix_shiftedPathMatrix, leastSingularValue_conjugateMatrix]

/-- The strict pseudospectrum of the real path is invariant under complex
conjugation. -/
theorem mem_pseudospectrum_conj_iff (n : ℕ) (a ε : ℝ) (z : ℂ) :
    conj z ∈ pseudospectrum n a ε ↔
      z ∈ pseudospectrum n a ε := by
  simp [pseudospectrum]

end

end ConnectedPseudospectrum
