import ConnectedPseudospectrum.Definitions
import ConnectedPseudospectrum.PathSpectrum
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Spectrum of the finite Hatano--Nelson path

This module completes the spectral calculation begun in `PathSpectrum`.
For positive `r`, the gauged Dirichlet sine vectors form an eigenbasis of
`A_n(r^2)`.  Consequently its characteristic polynomial is the product of
the displayed, pairwise-distinct linear factors.  We then specialize
`r = sqrt a` and connect the spectral nodes to both determinant and actual
Euclidean least-singular-value vanishing for the complex shifted matrix.
-/

namespace ConnectedPseudospectrum

open Matrix Module Polynomial Set

noncomputable section

/-- Each gauged sine vector is a genuine eigenvector of the linear operator
associated with `A_n(r^2)` when `r > 0`. -/
theorem pathMatrix_hasEigenvector (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    Module.End.HasEigenvector (pathMatrix n (r ^ 2)).toLin'
      (symmetricPathEigenvalue n r k) (pathRightEigenvector n r k) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact pathMatrix_mulVec_pathRightEigenvector n r k
  · exact pathRightEigenvector_ne_zero n hr.ne' k

/-- The `n` displayed gauged sine eigenvectors are linearly independent. -/
theorem pathRightEigenvector_linearIndependent (n : ℕ) {r : ℝ} (hr : 0 < r) :
    LinearIndependent ℝ (pathRightEigenvector n r) := by
  exact Module.End.eigenvectors_linearIndependent' (pathMatrix n (r ^ 2)).toLin'
    (symmetricPathEigenvalue n r) (symmetricPathEigenvalue_injective n hr)
    (pathRightEigenvector n r) (pathMatrix_hasEigenvector n hr)

/-- The basis of `ℝ^n` consisting of the gauged Dirichlet sine eigenvectors. -/
noncomputable def pathRightEigenbasis (n : ℕ) {r : ℝ} (hr : 0 < r) :
    Basis (Fin n) ℝ (Fin n → ℝ) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent
    (pathRightEigenvector_linearIndependent n hr)

@[simp] theorem pathRightEigenbasis_apply (n : ℕ) {r : ℝ} (hr : 0 < r)
    (k : Fin n) :
    pathRightEigenbasis n hr k = pathRightEigenvector n r k := by
  simp [pathRightEigenbasis]

/-- In the gauged sine basis, `A_n(r^2)` is the diagonal matrix of the
displayed eigenvalues. -/
theorem pathMatrix_toMatrix_pathRightEigenbasis (n : ℕ) {r : ℝ} (hr : 0 < r) :
    LinearMap.toMatrix (pathRightEigenbasis n hr) (pathRightEigenbasis n hr)
        (pathMatrix n (r ^ 2)).toLin' =
      diagonal (symmetricPathEigenvalue n r) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  rw [pathRightEigenbasis_apply, Matrix.toLin'_apply,
    pathMatrix_mulVec_pathRightEigenvector]
  rw [← pathRightEigenbasis_apply n hr j]
  rw [map_smul, Finsupp.smul_apply, Basis.repr_self_apply]
  by_cases hij : i = j
  · subst i
    simp
  · simp [hij, Ne.symm hij]

/-- Spectral exhaustion: the spectrum of `A_n(r^2)` is exactly the range of
the `n` displayed eigenvalues. -/
theorem spectrum_pathMatrix_sq (n : ℕ) {r : ℝ} (hr : 0 < r) :
    spectrum ℝ (pathMatrix n (r ^ 2)) =
      Set.range (symmetricPathEigenvalue n r) := by
  calc
    spectrum ℝ (pathMatrix n (r ^ 2)) =
        spectrum ℝ (pathMatrix n (r ^ 2)).toLin' := by
          rw [Matrix.spectrum_toLin']
    _ = spectrum ℝ
        (LinearMap.toMatrix (pathRightEigenbasis n hr) (pathRightEigenbasis n hr)
          (pathMatrix n (r ^ 2)).toLin') := by
            rw [LinearMap.spectrum_toMatrix]
    _ = spectrum ℝ (diagonal (symmetricPathEigenvalue n r)) := by
      rw [pathMatrix_toMatrix_pathRightEigenbasis]
    _ = Set.range (symmetricPathEigenvalue n r) := spectrum_diagonal _

/-- Complete characteristic-polynomial factorization of `A_n(r^2)`. -/
theorem charpoly_pathMatrix_sq (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (pathMatrix n (r ^ 2)).charpoly =
      ∏ k : Fin n, (Polynomial.X -
        Polynomial.C (symmetricPathEigenvalue n r k)) := by
  have hmatrix := congrArg Matrix.charpoly
    (pathMatrix_toMatrix_pathRightEigenbasis n hr)
  simpa only [LinearMap.charpoly_toMatrix, Matrix.charpoly_toLin',
    Matrix.charpoly_diagonal] using hmatrix

/-- Every displayed eigenvalue of `A_n(r^2)` is simple: equivalently, the
characteristic polynomial is separable. -/
theorem charpoly_pathMatrix_sq_separable (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (pathMatrix n (r ^ 2)).charpoly.Separable := by
  rw [charpoly_pathMatrix_sq n hr]
  exact Polynomial.separable_prod_X_sub_C_iff.mpr
    (symmetricPathEigenvalue_injective n hr)

/-- The paper's explicit eigenvalue, using a one-based mathematical index
represented by `k.1 + 1` in Lean. -/
noncomputable def pathEigenvalue (n : ℕ) (a : ℝ) (k : Fin n) : ℝ :=
  2 * Real.sqrt a *
    Real.cos (((k.1 + 1 : ℕ) : ℝ) * Real.pi / ((n + 1 : ℕ) : ℝ))

/-- The specialized displayed value agrees definitionally with the symmetric
path eigenvalue at `r = sqrt a`. -/
theorem pathEigenvalue_eq_symmetricPathEigenvalue (n : ℕ) (a : ℝ) (k : Fin n) :
    pathEigenvalue n a k = symmetricPathEigenvalue n (Real.sqrt a) k := by
  rfl

/-- For `a > 0`, the real spectrum of `A_n(a)` is precisely the paper's
explicit list `2 sqrt(a) cos(k pi/(n+1))`, `1 ≤ k ≤ n`. -/
theorem spectrum_pathMatrix (n : ℕ) {a : ℝ} (ha : 0 < a) :
    spectrum ℝ (pathMatrix n a) = Set.range (pathEigenvalue n a) := by
  have hsqrt : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  simpa only [Real.sq_sqrt ha.le, ← pathEigenvalue_eq_symmetricPathEigenvalue] using
    spectrum_pathMatrix_sq n hsqrt

/-- Characteristic-polynomial factorization in the paper's parameter `a`. -/
theorem charpoly_pathMatrix (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (pathMatrix n a).charpoly =
      ∏ k : Fin n, (Polynomial.X - Polynomial.C (pathEigenvalue n a k)) := by
  have hsqrt : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  simpa only [Real.sq_sqrt ha.le, ← pathEigenvalue_eq_symmetricPathEigenvalue] using
    charpoly_pathMatrix_sq n hsqrt

/-- The paper's eigenvalues are all simple for `a > 0`. -/
theorem charpoly_pathMatrix_separable (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (pathMatrix n a).charpoly.Separable := by
  have hsqrt : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  simpa only [Real.sq_sqrt ha.le] using charpoly_pathMatrix_sq_separable n hsqrt

/-- The complex path matrix is the entrywise scalar extension of the real
path matrix. -/
theorem complexPathMatrix_eq_map (n : ℕ) (a : ℝ) :
    complexPathMatrix n a =
      (pathMatrix n a).map (algebraMap ℝ ℂ) := by
  rfl

/-- The complex characteristic polynomial has the same explicit roots,
viewed in `ℂ`. -/
theorem charpoly_complexPathMatrix (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (complexPathMatrix n a).charpoly =
      ∏ k : Fin n, (Polynomial.X -
        Polynomial.C (pathEigenvalue n a k : ℂ)) := by
  rw [complexPathMatrix_eq_map, Matrix.charpoly_map, charpoly_pathMatrix n ha]
  calc
    Polynomial.map (algebraMap ℝ ℂ)
        (∏ k : Fin n, (Polynomial.X - Polynomial.C (pathEigenvalue n a k))) =
        ∏ k : Fin n, Polynomial.map (algebraMap ℝ ℂ)
          (Polynomial.X - Polynomial.C (pathEigenvalue n a k)) := by
            exact Polynomial.map_prod (algebraMap ℝ ℂ)
              (fun k : Fin n => Polynomial.X - Polynomial.C (pathEigenvalue n a k))
              Finset.univ
    _ = ∏ k : Fin n, (Polynomial.X -
        Polynomial.C (pathEigenvalue n a k : ℂ)) := by
          apply Finset.prod_congr rfl
          intro k hk
          rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
          rfl

/-- The shifted determinant vanishes exactly at one of the displayed real
spectral nodes, now regarded as a complex number. -/
theorem det_shiftedPathMatrix_eq_zero_iff (n : ℕ) {a : ℝ} (ha : 0 < a)
    (z : ℂ) :
    (shiftedPathMatrix n a z).det = 0 ↔
      ∃ k : Fin n, z = (pathEigenvalue n a k : ℂ) := by
  unfold shiftedPathMatrix
  rw [smul_one_eq_diagonal]
  have heval := Matrix.eval_charpoly (complexPathMatrix n a) z
  rw [Matrix.scalar_apply] at heval
  rw [← heval]
  rw [charpoly_complexPathMatrix n ha]
  simp only [Polynomial.eval_prod, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]

/-- In positive dimension, the actual Euclidean least singular value of the
shifted matrix vanishes exactly at the displayed spectral nodes. -/
theorem pseudospectralHeight_eq_zero_iff (n : ℕ) {a : ℝ} (ha : 0 < a)
    (hn : 0 < n) (z : ℂ) :
    pseudospectralHeight n a z = 0 ↔
      ∃ k : Fin n, z = (pathEigenvalue n a k : ℂ) := by
  rw [pseudospectralHeight,
    leastSingularValue_eq_zero_iff_det_eq_zero (shiftedPathMatrix n a z) hn,
    det_shiftedPathMatrix_eq_zero_iff n ha z]

/-- Each displayed node makes the shifted determinant vanish. -/
theorem det_shiftedPathMatrix_pathEigenvalue (n : ℕ) {a : ℝ} (ha : 0 < a)
    (k : Fin n) :
    (shiftedPathMatrix n a (pathEigenvalue n a k)).det = 0 := by
  exact (det_shiftedPathMatrix_eq_zero_iff n ha _).2 ⟨k, rfl⟩

/-- Each displayed node makes the least singular value vanish. -/
theorem pseudospectralHeight_pathEigenvalue (n : ℕ) {a : ℝ} (ha : 0 < a)
    (hn : 0 < n) (k : Fin n) :
    pseudospectralHeight n a (pathEigenvalue n a k) = 0 := by
  exact (pseudospectralHeight_eq_zero_iff n ha hn _).2 ⟨k, rfl⟩

end

end ConnectedPseudospectrum
