import ConnectedPseudospectrum.PathAlgebra
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Gauge symmetrization and sine eigenvectors for a finite path

The asymmetric finite path with parameter `r ^ 2` is diagonally similar to
the symmetric path with edge weight `r`.  This module also gives the explicit
Dirichlet sine eigenvectors of that symmetric path, with the endpoint cases
included in the proof.
-/

namespace ConnectedPseudospectrum

open Matrix

/-- The diagonal gauge `diag(1, r, ..., r^(n-1))`. -/
def diagonalGauge (n : ℕ) (r : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => r ^ i.1

/-- The explicit inverse candidate for the diagonal gauge. -/
noncomputable def diagonalGaugeInv (n : ℕ) (r : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => (r⁻¹) ^ i.1

@[simp] theorem diagonalGauge_apply (n : ℕ) (r : ℝ) (i j : Fin n) :
    diagonalGauge n r i j = if i = j then r ^ i.1 else 0 := by
  simp [diagonalGauge, Matrix.diagonal]

@[simp] theorem diagonalGaugeInv_apply (n : ℕ) (r : ℝ) (i j : Fin n) :
    diagonalGaugeInv n r i j = if i = j then (r⁻¹) ^ i.1 else 0 := by
  simp [diagonalGaugeInv, Matrix.diagonal]

/-- The explicit inverse is a right inverse whenever `r ≠ 0`. -/
theorem diagonalGauge_mul_inv (n : ℕ) {r : ℝ} (hr : r ≠ 0) :
    diagonalGauge n r * diagonalGaugeInv n r =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp only [diagonalGauge, diagonalGaugeInv, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst j
    simp [hr]
  · simp [h]

/-- The explicit inverse is also a left inverse whenever `r ≠ 0`. -/
theorem diagonalGaugeInv_mul (n : ℕ) {r : ℝ} (hr : r ≠ 0) :
    diagonalGaugeInv n r * diagonalGauge n r =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp only [diagonalGauge, diagonalGaugeInv, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst j
    simp [hr]
  · simp [h]

/-- The symmetric path with common edge weight `r`. -/
def symmetricPath (n : ℕ) (r : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  r • (upperShift n + lowerShift n)

/-- Gauge intertwining, valid even when `r = 0`. -/
theorem diagonalGauge_mul_symmetricPath (n : ℕ) (r : ℝ) :
    diagonalGauge n r * symmetricPath n r =
      pathMatrix n (r ^ 2) * diagonalGauge n r := by
  ext i j
  simp only [diagonalGauge, symmetricPath, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.smul_apply, Matrix.add_apply, upperShift_apply, lowerShift_apply,
    pathMatrix_apply, smul_eq_mul]
  by_cases hu : j.1 = i.1 + 1
  · have hfar : ¬i.1 = i.1 + 1 + 1 := by omega
    simp [hu, hfar, pow_succ]
  · by_cases hl : i.1 = j.1 + 1
    · have hfar : ¬j.1 = j.1 + 1 + 1 := by omega
      simp [hl, hfar, pow_succ]
      ring
    · simp [hu, hl]

/-- Diagonal similarity of the asymmetric and symmetric finite paths. -/
theorem pathMatrix_eq_gauge_symmetricPath_mul_inv (n : ℕ) {r : ℝ} (hr : r ≠ 0) :
    pathMatrix n (r ^ 2) =
      diagonalGauge n r * symmetricPath n r * diagonalGaugeInv n r := by
  calc
    pathMatrix n (r ^ 2) = pathMatrix n (r ^ 2) * 1 := by simp
    _ = pathMatrix n (r ^ 2) * (diagonalGauge n r * diagonalGaugeInv n r) := by
      rw [diagonalGauge_mul_inv n hr]
    _ = (pathMatrix n (r ^ 2) * diagonalGauge n r) * diagonalGaugeInv n r := by
      rw [Matrix.mul_assoc]
    _ = diagonalGauge n r * symmetricPath n r * diagonalGaugeInv n r := by
      rw [diagonalGauge_mul_symmetricPath]

/-- Away from the right endpoint, the upper shift selects the next coordinate. -/
theorem upperShift_mulVec_apply_of_lt (n : ℕ) (v : Fin n → ℝ) (i : Fin n)
    (hi : i.1 + 1 < n) :
    (upperShift n *ᵥ v) i = v ⟨i.1 + 1, hi⟩ := by
  classical
  simp only [Matrix.mulVec, dotProduct, upperShift_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single ⟨i.1 + 1, hi⟩]
  · simp
  · intro j hj hne
    rw [if_neg]
    intro hval
    apply hne
    exact Fin.ext hval
  · simp

/-- At the right endpoint, the upper shift gives zero. -/
theorem upperShift_mulVec_apply_of_not_lt (n : ℕ) (v : Fin n → ℝ) (i : Fin n)
    (hi : ¬ i.1 + 1 < n) :
    (upperShift n *ᵥ v) i = 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, upperShift_apply, ite_mul, one_mul, zero_mul]
  apply Finset.sum_eq_zero
  intro j hj
  rw [if_neg]
  intro hval
  exact hi (hval ▸ j.isLt)

/-- Away from the left endpoint, the lower shift selects the previous coordinate. -/
theorem lowerShift_mulVec_apply_of_pos (n : ℕ) (v : Fin n → ℝ) (i : Fin n)
    (hi : 0 < i.1) :
    (lowerShift n *ᵥ v) i =
      v ⟨i.1 - 1, (Nat.sub_le i.1 1).trans_lt i.isLt⟩ := by
  classical
  simp only [Matrix.mulVec, dotProduct, lowerShift_apply, ite_mul, one_mul, zero_mul]
  let j : Fin n := ⟨i.1 - 1, (Nat.sub_le i.1 1).trans_lt i.isLt⟩
  rw [Finset.sum_eq_single j]
  · rw [if_pos (by dsimp [j]; omega)]
  · intro k hk hne
    rw [if_neg]
    intro hval
    apply hne
    apply Fin.ext
    dsimp [j]
    omega
  · simp

/-- At the left endpoint, the lower shift gives zero. -/
theorem lowerShift_mulVec_apply_of_eq_zero (n : ℕ) (v : Fin n → ℝ) (i : Fin n)
    (hi : i.1 = 0) :
    (lowerShift n *ᵥ v) i = 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, lowerShift_apply, ite_mul, one_mul, zero_mul]
  apply Finset.sum_eq_zero
  intro j hj
  rw [if_neg]
  omega

/-- The `k`-th Dirichlet angle, with `k : Fin n` representing the paper's index `k+1`. -/
noncomputable def pathEigenangle (n : ℕ) (k : Fin n) : ℝ :=
  ((k.1 + 1 : ℕ) : ℝ) * Real.pi / ((n + 1 : ℕ) : ℝ)

/-- The Dirichlet sine vector with entries `sin((i+1) * pathEigenangle n k)`. -/
noncomputable def pathSineVector (n : ℕ) (k : Fin n) : Fin n → ℝ :=
  fun i => Real.sin (((i.1 + 1 : ℕ) : ℝ) * pathEigenangle n k)

/-- The explicit eigenvalue of the symmetric path corresponding to `pathSineVector`. -/
noncomputable def symmetricPathEigenvalue (n : ℕ) (r : ℝ) (k : Fin n) : ℝ :=
  2 * r * Real.cos (pathEigenangle n k)

private theorem sine_three_term (theta : ℝ) (m : ℕ) :
    Real.sin ((m : ℝ) * theta) + Real.sin (((m + 2 : ℕ) : ℝ) * theta) =
      2 * Real.cos theta * Real.sin (((m + 1 : ℕ) : ℝ) * theta) := by
  have hsub : (m : ℝ) * theta = (((m + 1 : ℕ) : ℝ) * theta - theta) := by
    push_cast
    ring
  have hadd : ((m + 2 : ℕ) : ℝ) * theta =
      (((m + 1 : ℕ) : ℝ) * theta + theta) := by
    push_cast
    ring
  calc
    Real.sin ((m : ℝ) * theta) + Real.sin (((m + 2 : ℕ) : ℝ) * theta) =
        Real.sin (((m + 1 : ℕ) : ℝ) * theta - theta) +
          Real.sin (((m + 1 : ℕ) : ℝ) * theta + theta) := by
            rw [hsub, hadd]
    _ = 2 * Real.sin (((m + 1 : ℕ) : ℝ) * theta) * Real.cos theta := by
      rw [Real.two_mul_sin_mul_cos]
    _ = 2 * Real.cos theta * Real.sin (((m + 1 : ℕ) : ℝ) * theta) := by ring

/-- Multiplying the Dirichlet angle by `n+1` gives an integral multiple of `pi`. -/
theorem pathEigenangle_endpoint (n : ℕ) (k : Fin n) :
    (((n + 1 : ℕ) : ℝ) * pathEigenangle n k) =
      ((k.1 + 1 : ℕ) : ℝ) * Real.pi := by
  rw [pathEigenangle]
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

/-- The virtual sine coordinate just beyond the right endpoint is zero. -/
theorem pathSineVector_right_boundary (n : ℕ) (k : Fin n) :
    Real.sin (((n + 1 : ℕ) : ℝ) * pathEigenangle n k) = 0 := by
  rw [pathEigenangle_endpoint]
  exact Real.sin_nat_mul_pi (k.1 + 1)

/-- The Dirichlet sine vectors are eigenvectors of the symmetric weighted path.

The proof treats both missing endpoint coordinates as the sine values at `0`
and `(n+1) * pathEigenangle`, respectively, and proves both are zero.
-/
theorem symmetricPath_mulVec_pathSineVector (n : ℕ) (r : ℝ) (k : Fin n) :
    symmetricPath n r *ᵥ pathSineVector n k =
      symmetricPathEigenvalue n r k • pathSineVector n k := by
  funext i
  have hupper :
      (upperShift n *ᵥ pathSineVector n k) i =
        Real.sin (((i.1 + 2 : ℕ) : ℝ) * pathEigenangle n k) := by
    by_cases hi : i.1 + 1 < n
    · rw [upperShift_mulVec_apply_of_lt n (pathSineVector n k) i hi]
      simp only [pathSineVector]
    · rw [upperShift_mulVec_apply_of_not_lt n (pathSineVector n k) i hi]
      have hindex : i.1 + 2 = n + 1 := by omega
      symm
      simpa only [hindex] using pathSineVector_right_boundary n k
  have hlower :
      (lowerShift n *ᵥ pathSineVector n k) i =
        Real.sin ((i.1 : ℝ) * pathEigenangle n k) := by
    by_cases hi : 0 < i.1
    · rw [lowerShift_mulVec_apply_of_pos n (pathSineVector n k) i hi]
      simp only [pathSineVector]
      congr 2
      norm_cast
      omega
    · have hi0 : i.1 = 0 := by omega
      rw [lowerShift_mulVec_apply_of_eq_zero n (pathSineVector n k) i hi0]
      simp [hi0]
  simp only [symmetricPath, Matrix.smul_mulVec, Matrix.add_mulVec, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul, hupper, hlower, symmetricPathEigenvalue, pathSineVector]
  have hrec :
      Real.sin (((i.1 + 2 : ℕ) : ℝ) * pathEigenangle n k) +
          Real.sin ((i.1 : ℝ) * pathEigenangle n k) =
        2 * Real.cos (pathEigenangle n k) *
          Real.sin (((i.1 + 1 : ℕ) : ℝ) * pathEigenangle n k) := by
    rw [add_comm]
    exact sine_three_term (pathEigenangle n k) i.1
  rw [hrec]
  ring

/-- Every Dirichlet angle lies strictly between `0` and `pi`. -/
theorem pathEigenangle_pos (n : ℕ) (k : Fin n) :
    0 < pathEigenangle n k := by
  rw [pathEigenangle]
  positivity

/-- Every Dirichlet angle lies strictly below `pi`. -/
theorem pathEigenangle_lt_pi (n : ℕ) (k : Fin n) :
    pathEigenangle n k < Real.pi := by
  rw [pathEigenangle]
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
  have hnat : k.1 + 1 < n + 1 := by omega
  have hreal : ((k.1 + 1 : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hmul := mul_lt_mul_of_pos_right hreal Real.pi_pos
  simpa only [mul_comm] using hmul

/-- A Dirichlet sine vector is nonzero; its first coordinate is positive. -/
theorem pathSineVector_ne_zero (n : ℕ) (k : Fin n) :
    pathSineVector n k ≠ 0 := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k.1) k.isLt
  let first : Fin n := ⟨0, hn⟩
  intro hzero
  have hcoord := congrFun hzero first
  have hsin : Real.sin (pathEigenangle n k) = 0 := by
    simpa [pathSineVector, first] using hcoord
  exact (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
    (pathEigenangle_pos n k) (pathEigenangle_lt_pi n k))) hsin

/-- Multiplication by a nondegenerate diagonal gauge is injective on vectors. -/
theorem diagonalGauge_mulVec_injective (n : ℕ) {r : ℝ} (hr : r ≠ 0) :
    Function.Injective (diagonalGauge n r).mulVec := by
  intro v w hvw
  have h := congrArg (fun u => diagonalGaugeInv n r *ᵥ u) hvw
  simpa only [Matrix.mulVec_mulVec, diagonalGaugeInv_mul n hr, Matrix.one_mulVec] using h

/-- The right eigenvector of the asymmetric path obtained by applying the gauge to a sine vector. -/
noncomputable def pathRightEigenvector (n : ℕ) (r : ℝ) (k : Fin n) : Fin n → ℝ :=
  diagonalGauge n r *ᵥ pathSineVector n k

/-- The gauged sine vectors are right eigenvectors of `A_n(r²)`. -/
theorem pathMatrix_mulVec_pathRightEigenvector (n : ℕ) (r : ℝ) (k : Fin n) :
    pathMatrix n (r ^ 2) *ᵥ pathRightEigenvector n r k =
      symmetricPathEigenvalue n r k • pathRightEigenvector n r k := by
  calc
    pathMatrix n (r ^ 2) *ᵥ pathRightEigenvector n r k =
        (pathMatrix n (r ^ 2) * diagonalGauge n r) *ᵥ pathSineVector n k := by
          rw [pathRightEigenvector, ← Matrix.mulVec_mulVec]
    _ = (diagonalGauge n r * symmetricPath n r) *ᵥ pathSineVector n k := by
      rw [diagonalGauge_mul_symmetricPath]
    _ = diagonalGauge n r *ᵥ (symmetricPath n r *ᵥ pathSineVector n k) := by
      rw [Matrix.mulVec_mulVec]
    _ = diagonalGauge n r *ᵥ
        (symmetricPathEigenvalue n r k • pathSineVector n k) := by
          rw [symmetricPath_mulVec_pathSineVector]
    _ = symmetricPathEigenvalue n r k • pathRightEigenvector n r k := by
      rw [Matrix.mulVec_smul, pathRightEigenvector]

/-- For `r ≠ 0`, every gauged sine eigenvector is nonzero. -/
theorem pathRightEigenvector_ne_zero (n : ℕ) {r : ℝ} (hr : r ≠ 0) (k : Fin n) :
    pathRightEigenvector n r k ≠ 0 := by
  intro hzero
  apply pathSineVector_ne_zero n k
  apply diagonalGauge_mulVec_injective n hr
  simpa only [pathRightEigenvector, Matrix.mulVec_zero] using hzero

/-- The Dirichlet angles increase strictly with their zero-based index. -/
theorem pathEigenangle_strictMono (n : ℕ) :
    StrictMono (pathEigenangle n) := by
  intro k l hkl
  rw [pathEigenangle, pathEigenangle]
  have hnat : k.1 + 1 < l.1 + 1 := by omega
  have hreal : ((k.1 + 1 : ℕ) : ℝ) < ((l.1 + 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
  exact mul_lt_mul_of_pos_right hreal Real.pi_pos

/-- For positive edge weight, the displayed eigenvalues strictly decrease with the index. -/
theorem symmetricPathEigenvalue_strictAnti (n : ℕ) {r : ℝ} (hr : 0 < r) :
    StrictAnti (symmetricPathEigenvalue n r) := by
  intro k l hkl
  have hangle : pathEigenangle n k < pathEigenangle n l :=
    pathEigenangle_strictMono n hkl
  have hcos : Real.cos (pathEigenangle n l) < Real.cos (pathEigenangle n k) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi
      (le_of_lt (pathEigenangle_pos n k))
      (le_of_lt (pathEigenangle_lt_pi n l)) hangle
  have hscale : 0 < 2 * r := mul_pos (by norm_num) hr
  simpa only [symmetricPathEigenvalue, mul_assoc] using
    (mul_lt_mul_of_pos_left hcos hscale)

/-- For positive edge weight, the displayed eigenvalues are pairwise distinct. -/
theorem symmetricPathEigenvalue_injective (n : ℕ) {r : ℝ} (hr : 0 < r) :
    Function.Injective (symmetricPathEigenvalue n r) :=
  (symmetricPathEigenvalue_strictAnti n hr).injective

end ConnectedPseudospectrum
