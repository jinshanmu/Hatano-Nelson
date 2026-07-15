import Mathlib.Analysis.Matrix.PosDef

/-!
# Positive principal submatrices

The vertical determinant argument repeatedly deletes coordinates from a
positive-definite Hermitian matrix.  Mathlib provides the semidefinite
submatrix theorem for arbitrary maps; injectivity upgrades it to positive
definiteness.  This module records that finite-dimensional fact explicitly.
-/

namespace ConnectedPseudospectrum

open Matrix
open scoped ComplexOrder

/-- An injectively indexed principal submatrix of a positive-definite
complex matrix is positive definite. -/
theorem posDef_submatrix_of_injective
    {m n : Type*} (M : Matrix n n ℂ) (hM : M.PosDef)
    (e : m → n) (he : Function.Injective e) :
    (M.submatrix e e).PosDef := by
  refine ⟨hM.isHermitian.submatrix e, ?_⟩
  intro x hx
  have hxmap : x.mapDomain e ≠ 0 :=
    (Finsupp.mapDomain_injective he).ne hx
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using hM.2 hxmap

/-- Consequently, every finite injectively indexed principal minor has
strictly positive determinant. -/
theorem det_submatrix_pos_of_posDef
    {m n : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix n n ℂ) (hM : M.PosDef)
    (e : m → n) (he : Function.Injective e) :
    0 < (M.submatrix e e).det :=
  (posDef_submatrix_of_injective M hM e he).det_pos

end ConnectedPseudospectrum
