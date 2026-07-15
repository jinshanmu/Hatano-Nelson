import ConnectedPseudospectrum.OperatorNormAttainment
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.AbsMax

/-!
# Analytic vector-valued resolvents

For a fixed vector, evaluation of the finite-dimensional matrix resolvent is
complex differentiable throughout the resolvent set.  This is the analytic
input used to prove that every pseudospectral component contains a spectral
point.
-/

namespace ConnectedPseudospectrum

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- Evaluation of a matrix on a fixed Euclidean vector, first bundled as a
complex-linear map of the matrix variable. -/
def matrixApplyLinearMap {n : ℕ} (v : ComplexEuclidean n) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ComplexEuclidean n where
  toFun M := matrixOperator M v
  map_add' M N := by simp
  map_smul' c M := by simp [matrixOperator]

/-- Evaluation of a matrix on a fixed Euclidean vector, bundled as a
continuous complex-linear map of the matrix variable. -/
def matrixApplyCLM {n : ℕ} (v : ComplexEuclidean n) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ComplexEuclidean n :=
  (matrixApplyLinearMap v).toContinuousLinearMap

@[simp] theorem matrixApplyCLM_apply {n : ℕ} (v : ComplexEuclidean n)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    matrixApplyCLM v M = matrixOperator M v :=
  rfl

/-- The resolvent applied to a fixed vector. -/
def resolventVector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (v : ComplexEuclidean n) (z : ℂ) : ComplexEuclidean n :=
  matrixOperator (generalShift M z)⁻¹ v

/-- The shifted matrix depends complex differentiably on the spectral
parameter. -/
theorem differentiable_generalShift {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) :
    Differentiable ℂ (generalShift M) := by
  simpa only [generalShift] using
    (differentiable_id.smul_const
      (1 : Matrix (Fin n) (Fin n) ℂ)).sub_const M

/-- The matrix-valued resolvent is complex differentiable at every point
where the shifted determinant is nonzero. -/
theorem differentiableAt_generalShift_inv {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (hdet : (generalShift M z).det ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ => (generalShift M w)⁻¹) z := by
  have hunit : IsUnit (generalShift M z) :=
    (generalShift M z).isUnit_iff_isUnit_det.mpr
      (isUnit_iff_ne_zero.mpr hdet)
  have hinvRing : DifferentiableAt ℂ
      (fun w : ℂ => Ring.inverse (generalShift M w)) z :=
    (differentiable_generalShift M z).inverse hunit
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using hinvRing

/-- A fixed-vector resolvent is complex differentiable at every point where
the shifted determinant is nonzero. -/
theorem differentiableAt_resolventVector {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (v : ComplexEuclidean n) (z : ℂ)
    (hdet : (generalShift M z).det ≠ 0) :
    DifferentiableAt ℂ (resolventVector M v) z := by
  have hinv := differentiableAt_generalShift_inv M z hdet
  have happ := (matrixApplyCLM v).differentiableAt.comp z hinv
  simpa only [resolventVector, Function.comp_apply,
    matrixApplyCLM_apply] using happ

/-- The fixed-vector resolvent is differentiable on any set disjoint from the
spectrum. -/
theorem differentiableOn_resolventVector {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (v : ComplexEuclidean n) (U : Set ℂ)
    (hU : ∀ z ∈ U, (generalShift M z).det ≠ 0) :
    DifferentiableOn ℂ (resolventVector M v) U := by
  intro z hz
  exact (differentiableAt_resolventVector M v z (hU z hz)).differentiableWithinAt

end

end ConnectedPseudospectrum
