import ConnectedPseudospectrum.MiddleBranchBridge
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Product parity for the signed pencil

This module records the determinant-product argument used in the odd central
gap comparison.  The reversal determinant occurs once in the signed-pencil
identity at each of `c` and `-c`; its square is one, so it leaves no residual
dimension-dependent sign in the product.

The resulting product of `lambda_i^2-c^2` is then combined with an honest
"at most one eigenvalue in `(-c,c)`" hypothesis.  Positivity excludes the
possibility of exactly one negative factor, while nonvanishing excludes an
eigenvalue on either boundary.  The final statements use the existing
Hermitian singular-value bridge to recover the actual Euclidean least
singular value.
-/

namespace ConnectedPseudospectrum

open Matrix

noncomputable section

/-! ## Exact determinant factorization -/

/-- For a real Hermitian matrix, the determinant of `A-sI` is the product
of its decreasingly ordered eigenvalues minus `s`.  This statement includes
the full `(-1)^n` conversion from Mathlib's characteristic-polynomial
convention `det(sI-A)`. -/
theorem det_sub_smul_one_eq_prod_orderedHermitianEigenvalue_sub
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (s : ℝ) :
    (A - s • (1 : Matrix (Fin n) (Fin n) ℝ)).det =
      ∏ i : Fin n, (orderedHermitianEigenvalue hA i - s) := by
  have hmatrix :
      A - s • (1 : Matrix (Fin n) (Fin n) ℝ) =
        -(Matrix.scalar (Fin n) s - A) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hchar :
      A.charpoly.eval s =
        ∏ i : Fin n, (s - orderedHermitianEigenvalue hA i) := by
    rw [charpoly_eq_orderedHermitianEigenvalue_diagonal hA,
      Matrix.charpoly_diagonal]
    simp only [Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
  have hprodNeg :
      (∏ i : Fin n, -(s - orderedHermitianEigenvalue hA i)) =
        (-1 : ℝ) ^ n *
          ∏ i : Fin n, (s - orderedHermitianEigenvalue hA i) := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_neg (s := Finset.univ)
        (fun i : Fin n => s - orderedHermitianEigenvalue hA i))
  calc
    (A - s • (1 : Matrix (Fin n) (Fin n) ℝ)).det =
        (-(Matrix.scalar (Fin n) s - A)).det :=
      congrArg Matrix.det hmatrix
    _ = (-1 : ℝ) ^ n * (Matrix.scalar (Fin n) s - A).det := by
      rw [Matrix.det_neg, Fintype.card_fin]
    _ = (-1 : ℝ) ^ n * A.charpoly.eval s := by
      rw [Matrix.eval_charpoly]
    _ = (-1 : ℝ) ^ n *
        ∏ i : Fin n, (s - orderedHermitianEigenvalue hA i) := by
      rw [hchar]
    _ = ∏ i : Fin n, -(s - orderedHermitianEigenvalue hA i) :=
      hprodNeg.symm
    _ = ∏ i : Fin n, (orderedHermitianEigenvalue hA i - s) := by
      apply Finset.prod_congr rfl
      intro i _
      ring

/-- Exact signed-pencil product factorization.  Although each individual
signed-pencil determinant contains the orientation factor `det J_n`, the
two copies cancel because `(det J_n)^2=1`. -/
theorem signedPencilDet_mul_neg_eq_prod_orderedEigenvalue_sq_sub_sq
    (n : ℕ) (a x c : ℝ) :
    let hB : (signedMiddleMatrix n a x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
    signedPencilDet n a x c * signedPencilDet n a x (-c) =
      ∏ i : Fin n,
        (orderedHermitianEigenvalue hB i ^ 2 - c ^ 2) := by
  dsimp only
  let B : Matrix (Fin n) (Fin n) ℝ := signedMiddleMatrix n a x
  let hB : B.IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
  let d : ℝ := (reversal n).det
  have hdSq : d * d = 1 := by
    calc
      d * d = (reversal n * reversal n).det := by
        exact (Matrix.det_mul (reversal n) (reversal n)).symm
      _ = 1 := by rw [reversal_mul_self, Matrix.det_one]
  have hrelPos :
      signedPencilDet n a x c * d =
        (B - c • (1 : Matrix (Fin n) (Fin n) ℝ)).det :=
    signedPencilDet_mul_det_reversal n a x c
  have hrelNeg :
      signedPencilDet n a x (-c) * d =
        (B - (-c) • (1 : Matrix (Fin n) (Fin n) ℝ)).det :=
    signedPencilDet_mul_det_reversal n a x (-c)
  have hdetPos :
      (B - c • (1 : Matrix (Fin n) (Fin n) ℝ)).det =
        ∏ i : Fin n, (orderedHermitianEigenvalue hB i - c) :=
    det_sub_smul_one_eq_prod_orderedHermitianEigenvalue_sub hB c
  have hdetNeg :
      (B - (-c) • (1 : Matrix (Fin n) (Fin n) ℝ)).det =
        ∏ i : Fin n, (orderedHermitianEigenvalue hB i - (-c)) :=
    det_sub_smul_one_eq_prod_orderedHermitianEigenvalue_sub hB (-c)
  calc
    signedPencilDet n a x c * signedPencilDet n a x (-c) =
        (signedPencilDet n a x c * signedPencilDet n a x (-c)) *
          (d * d) := by rw [hdSq, mul_one]
    _ = (signedPencilDet n a x c * d) *
        (signedPencilDet n a x (-c) * d) := by ring
    _ = (B - c • (1 : Matrix (Fin n) (Fin n) ℝ)).det *
        (B - (-c) • (1 : Matrix (Fin n) (Fin n) ℝ)).det := by
      rw [hrelPos, hrelNeg]
    _ = (∏ i : Fin n, (orderedHermitianEigenvalue hB i - c)) *
        ∏ i : Fin n, (orderedHermitianEigenvalue hB i - (-c)) := by
      rw [hdetPos, hdetNeg]
    _ = ∏ i : Fin n,
        (orderedHermitianEigenvalue hB i ^ 2 - c ^ 2) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr
        (s₁ := (Finset.univ : Finset (Fin n)))
        (s₂ := (Finset.univ : Finset (Fin n))) rfl
      intro i _
      ring

/-! ## The parity argument -/

/-- A positive product of the factors `lambda_i^2-c^2`, together with at
most one eigenvalue strictly inside `(-c,c)`, forces every eigenvalue to lie
strictly outside the closed interval.  Positivity itself supplies the
nonvanishing needed to exclude the boundary. -/
theorem all_abs_gt_of_prod_sq_sub_sq_pos_of_atMostOne
    {ι : Type*} [Fintype ι] (lambda : ι → ℝ) {c : ℝ}
    (hc : 0 ≤ c)
    (hprodPos : 0 < ∏ i : ι, ((lambda i) ^ 2 - c ^ 2))
    (hAtMostOne : ∀ i j : ι,
      |lambda i| < c → |lambda j| < c → i = j) :
    ∀ i : ι, c < |lambda i| := by
  classical
  have hprodNe : (∏ i : ι, ((lambda i) ^ 2 - c ^ 2)) ≠ 0 :=
    ne_of_gt hprodPos
  have hfactorNe : ∀ i : ι, (lambda i) ^ 2 - c ^ 2 ≠ 0 := by
    intro i hi
    apply hprodNe
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have habsNe : ∀ i : ι, |lambda i| ≠ c := by
    intro i hi
    apply hfactorNe i
    rw [← sq_abs (lambda i), hi, sub_self]
  intro i
  by_contra hnotOutside
  have hiLe : |lambda i| ≤ c := le_of_not_gt hnotOutside
  have hiInside : |lambda i| < c :=
    lt_of_le_of_ne hiLe (habsNe i)
  have hiFactorNeg : (lambda i) ^ 2 - c ^ 2 < 0 := by
    apply sub_neg.mpr
    exact sq_lt_sq.mpr (by simpa only [abs_of_nonneg hc] using hiInside)
  have hrestPos :
      0 < ∏ j ∈ Finset.univ.erase i, ((lambda j) ^ 2 - c ^ 2) := by
    apply Finset.prod_pos
      (s := (Finset.univ.erase i : Finset ι))
      (f := fun j : ι => (lambda j) ^ 2 - c ^ 2)
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hjNotInside : ¬ |lambda j| < c := by
      intro hjInside
      exact hji (hAtMostOne i j hiInside hjInside).symm
    have hcLe : c ≤ |lambda j| := le_of_not_gt hjNotInside
    have hcLt : c < |lambda j| :=
      lt_of_le_of_ne hcLe (Ne.symm (habsNe j))
    apply sub_pos.mpr
    exact sq_lt_sq.mpr (by simpa only [abs_of_nonneg hc] using hcLt)
  have hdecomp :
      ((lambda i) ^ 2 - c ^ 2) *
          (∏ j ∈ Finset.univ.erase i, ((lambda j) ^ 2 - c ^ 2)) =
        ∏ j : ι, ((lambda j) ^ 2 - c ^ 2) := by
    change ((lambda i) ^ 2 - c ^ 2) *
        (Finset.univ.erase i).prod (fun j : ι => (lambda j) ^ 2 - c ^ 2) =
      Finset.univ.prod (fun j : ι => (lambda j) ^ 2 - c ^ 2)
    exact Finset.mul_prod_erase Finset.univ
      (fun j : ι => (lambda j) ^ 2 - c ^ 2) (Finset.mem_univ i)
  have hwholeNeg : (∏ j : ι, ((lambda j) ^ 2 - c ^ 2)) < 0 := by
    rw [← hdecomp]
    exact mul_neg_of_neg_of_pos hiFactorNeg hrestPos
  exact (not_lt_of_ge hprodPos.le) hwholeNeg

/-! ## Signed-middle and least-singular-value consequences -/

/-- Positive signed-pencil product plus the at-most-one input forces every
ordered eigenvalue of the signed-middle matrix outside `[-c,c]`. -/
theorem all_abs_orderedSignedMiddleEigenvalue_gt_of_product_pos
    (n : ℕ) (a x : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hproduct :
      0 < signedPencilDet n a x c * signedPencilDet n a x (-c))
    (hAtMostOne :
      let hB : (signedMiddleMatrix n a x).IsHermitian :=
        Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
      ∀ i j : Fin n,
        |orderedHermitianEigenvalue hB i| < c →
        |orderedHermitianEigenvalue hB j| < c → i = j) :
    let hB : (signedMiddleMatrix n a x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
    ∀ i : Fin n, c < |orderedHermitianEigenvalue hB i| := by
  dsimp only at hAtMostOne ⊢
  let hB : (signedMiddleMatrix n a x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
  have hfactorization :=
    signedPencilDet_mul_neg_eq_prod_orderedEigenvalue_sq_sub_sq n a x c
  have hprodPos :
      0 < ∏ i : Fin n,
        (orderedHermitianEigenvalue hB i ^ 2 - c ^ 2) := by
    rw [← hfactorization]
    exact hproduct
  exact all_abs_gt_of_prod_sq_sub_sq_pos_of_atMostOne
    (orderedHermitianEigenvalue hB) hc hprodPos hAtMostOne

/-- If every ordered signed-middle eigenvalue has magnitude greater than
`c`, then the actual Euclidean least singular value, hence `realGapValue`,
is greater than `c`. -/
theorem realGapValue_gt_of_all_abs_orderedSignedMiddleEigenvalue
    (n : ℕ) (hn : 0 < n) (a x c : ℝ)
    (hall :
      let hB : (signedMiddleMatrix n a x).IsHermitian :=
        Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
      ∀ i : Fin n, c < |orderedHermitianEigenvalue hB i|) :
    c < realGapValue n a x := by
  dsimp only at hall
  let hB : (signedMiddleMatrix n a x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
  let hC : ((signedMiddleMatrix n a x).map
      Complex.ofRealHom).IsHermitian :=
    complexSignedMiddleMatrix_isHermitian n a x
  obtain ⟨k, hheight, _⟩ :=
    exists_signedMiddleMatrix_eigenvalue_abs_eq_pseudospectralHeight
      n hn a x
  obtain ⟨j, hj⟩ :=
    exists_orderedSignedMiddleEigenvalue_eq_complexEigenvalue n a x k
  calc
    c < |orderedHermitianEigenvalue hB j| := hall j
    _ = |hC.eigenvalues k| := congrArg abs hj
    _ = pseudospectralHeight n a (x : ℂ) := hheight.symm
    _ = realGapValue n a x := rfl

/-- Product parity excludes both a central eigenvalue and every boundary
eigenvalue, so the paper's actual real-axis gap value is strictly above
`c`. -/
theorem realGapValue_gt_of_signedPencil_product_pos_of_atMostOne
    (n : ℕ) (hn : 0 < n) (a x : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hproduct :
      0 < signedPencilDet n a x c * signedPencilDet n a x (-c))
    (hAtMostOne :
      let hB : (signedMiddleMatrix n a x).IsHermitian :=
        Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
      ∀ i j : Fin n,
        |orderedHermitianEigenvalue hB i| < c →
        |orderedHermitianEigenvalue hB j| < c → i = j) :
    c < realGapValue n a x := by
  apply realGapValue_gt_of_all_abs_orderedSignedMiddleEigenvalue
    n hn a x c
  exact all_abs_orderedSignedMiddleEigenvalue_gt_of_product_pos
    n a x hc hproduct hAtMostOne

/-- The same conclusion stated simultaneously for the complex Euclidean
least singular value of the signed-middle matrix and for `realGapValue`.
The two quantities agree by the unitary reversal bridge. -/
theorem leastSingularValue_and_realGapValue_gt_of_signedPencil_product_pos
    (n : ℕ) (hn : 0 < n) (a x : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hproduct :
      0 < signedPencilDet n a x c * signedPencilDet n a x (-c))
    (hAtMostOne :
      let hB : (signedMiddleMatrix n a x).IsHermitian :=
        Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
      ∀ i j : Fin n,
        |orderedHermitianEigenvalue hB i| < c →
        |orderedHermitianEigenvalue hB j| < c → i = j) :
    c < leastSingularValue
        ((signedMiddleMatrix n a x).map Complex.ofRealHom) ∧
      c < realGapValue n a x := by
  have hgap :=
    realGapValue_gt_of_signedPencil_product_pos_of_atMostOne
      n hn a x hc hproduct hAtMostOne
  constructor
  · simpa only [leastSingularValue_signedMiddleMatrix, realGapValue] using hgap
  · exact hgap

end

end ConnectedPseudospectrum
