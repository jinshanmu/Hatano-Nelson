import ConnectedPseudospectrum.PathAlgebra
import ConnectedPseudospectrum.Definitions
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Reflection symmetry of the real-axis least singular value

The alternating-sign reflection satisfies `Sigma A_n Sigma = -A_n`.
After scalar extension to the complex Euclidean space it is unitary, so
conjugating a shifted path matrix and multiplying by the scalar `-1` do not
change its actual least singular value.  This proves the exact symmetry
`g_n(-x) = g_n(x)` used to reflect every positive-gap comparison to the
corresponding negative gap in lines 1925--1938 of the immutable source.
-/

namespace ConnectedPseudospectrum

open Matrix

noncomputable section

/-- Complex scalar extension of the alternating-sign reflection. -/
def complexReflection (n : Nat) : Matrix (Fin n) (Fin n) Complex :=
  (reflection n).map Complex.ofRealHom

@[simp] theorem complexReflection_star (n : Nat) :
    star (complexReflection n) = complexReflection n := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [complexReflection, reflection_apply]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [complexReflection, reflection_apply, hij, hji]

/-- The complex alternating-sign reflection is an involution. -/
@[simp] theorem complexReflection_mul_self (n : Nat) :
    complexReflection n * complexReflection n =
      (1 : Matrix (Fin n) (Fin n) Complex) := by
  rw [complexReflection, ← Matrix.map_mul, reflection_mul_self]
  simp

/-- The complex alternating-sign reflection is unitary. -/
theorem complexReflection_mem_unitary (n : Nat) :
    complexReflection n ∈ Matrix.unitaryGroup (Fin n) Complex := by
  rw [Matrix.mem_unitaryGroup_iff, complexReflection_star,
    complexReflection_mul_self]

/-- Reflection anticommutes with the complex path matrix. -/
theorem complexReflection_complexPathMatrix_complexReflection
    (n : Nat) (a : Real) :
    complexReflection n * complexPathMatrix n a * complexReflection n =
      -complexPathMatrix n a := by
  have hpath : complexPathMatrix n a =
      (pathMatrix n a).map Complex.ofRealHom := by
    ext i j
    rfl
  rw [hpath, complexReflection, ← Matrix.map_mul, ← Matrix.map_mul,
    reflection_pathMatrix_reflection]
  ext i j
  simp

/-- Conjugating `x I - A_n` by reflection gives `x I + A_n`. -/
theorem complexReflection_shiftedPathMatrix_complexReflection
    (n : Nat) (a x : Real) :
    complexReflection n * shiftedPathMatrix n a (x : Complex) *
        complexReflection n =
      (x : Complex) • (1 : Matrix (Fin n) (Fin n) Complex) +
        complexPathMatrix n a := by
  rw [shiftedPathMatrix, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    complexReflection_mul_self,
    complexReflection_complexPathMatrix_complexReflection,
    sub_neg_eq_add]

/-- The shift at `-x` is minus the reflected conjugate of the shift at
`x`. -/
theorem shiftedPathMatrix_neg_ofReal_eq_neg_reflection
    (n : Nat) (a x : Real) :
    shiftedPathMatrix n a (-(x : Complex)) =
      -(complexReflection n * shiftedPathMatrix n a (x : Complex) *
        complexReflection n) := by
  rw [complexReflection_shiftedPathMatrix_complexReflection]
  unfold shiftedPathMatrix
  module

/-- Left and right multiplication by complex reflection preserve the actual
least singular value. -/
theorem leastSingularValue_complexReflection_mul_mul
    (n : Nat) (M : Matrix (Fin n) (Fin n) Complex) :
    leastSingularValue (complexReflection n * M * complexReflection n) =
      leastSingularValue M := by
  rw [leastSingularValue_mul_unitary
      (complexReflection n * M) (complexReflection n)
      (complexReflection_mem_unitary n),
    leastSingularValue_unitary_mul
      (complexReflection n) M (complexReflection_mem_unitary n)]

/-- The actual pseudospectral height is even on the real axis. -/
theorem pseudospectralHeight_neg_ofReal
    (n : Nat) (a x : Real) :
    pseudospectralHeight n a (-(x : Complex)) =
      pseudospectralHeight n a (x : Complex) := by
  unfold pseudospectralHeight
  rw [shiftedPathMatrix_neg_ofReal_eq_neg_reflection]
  calc
    leastSingularValue
        (-(complexReflection n * shiftedPathMatrix n a (x : Complex) *
          complexReflection n)) =
        leastSingularValue
          ((-1 : Complex) •
            (complexReflection n * shiftedPathMatrix n a (x : Complex) *
              complexReflection n)) := by
          congr 1
          module
    _ = ‖(-1 : Complex)‖ *
        leastSingularValue
          (complexReflection n * shiftedPathMatrix n a (x : Complex) *
            complexReflection n) :=
      leastSingularValue_smul (-1 : Complex) _
    _ = leastSingularValue
        (complexReflection n * shiftedPathMatrix n a (x : Complex) *
          complexReflection n) := by norm_num
    _ = leastSingularValue (shiftedPathMatrix n a (x : Complex)) :=
      leastSingularValue_complexReflection_mul_mul n _

/-- Exact reflection identity `g_n(-x) = g_n(x)` for the paper's real-axis
least-singular-value function. -/
@[simp] theorem realGapValue_neg (n : Nat) (a x : Real) :
    realGapValue n a (-x) = realGapValue n a x := by
  unfold realGapValue
  simpa using pseudospectralHeight_neg_ofReal n a x

end

end ConnectedPseudospectrum
