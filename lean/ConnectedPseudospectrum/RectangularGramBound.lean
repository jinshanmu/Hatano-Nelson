import ConnectedPseudospectrum.HermitianPathSpectrum
import ConnectedPseudospectrum.RectangularFactorization

/-!
# Sharp Gram bounds for the rectangular path factors

The two rectangular Gram matrices differ from the real symmetric path Gram
matrix only by diagonal phase conjugations.  This module constructs those
unitary phases and transfers the sharp bottom eigenvalue of the symmetric
path to homogeneous Euclidean norm bounds for both rectangular factors.
-/

namespace ConnectedPseudospectrum

open Matrix
open scoped ComplexConjugate ComplexOrder

noncomputable section

/-- The unit complex phase `exp(i theta)`. -/
private def pathPhase (θ : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * Complex.I)

private theorem pathPhase_norm (θ : ℝ) : ‖pathPhase θ‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I θ

private theorem star_pathPhase_mul_pathPhase (θ : ℝ) :
    star (pathPhase θ) * pathPhase θ = 1 := by
  rw [show star (pathPhase θ) = conj (pathPhase θ) from rfl,
    Complex.conj_mul', pathPhase_norm]
  norm_num

private theorem pathPhase_mul_star_pathPhase (θ : ℝ) :
    pathPhase θ * star (pathPhase θ) = 1 := by
  rw [mul_comm, star_pathPhase_mul_pathPhase]

private theorem star_pathPhase_pow_mul_pathPhase_pow (θ : ℝ) (k : ℕ) :
    star (pathPhase θ ^ k) * pathPhase θ ^ k = 1 := by
  rw [star_pow, ← mul_pow, star_pathPhase_mul_pathPhase, one_pow]

/-- The diagonal phase cancelling the argument of `pathRootPlus r theta` in
the Gram matrix of `rectangularC`. -/
def rectangularCPhase (n : ℕ) (θ : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun i => pathPhase θ ^ i.1

/-- The diagonal phase cancelling the argument of `pathRootMinus r theta` in
the Gram matrix of `rectangularD`. -/
def rectangularDPhase (n : ℕ) (θ : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun i => pathPhase (-θ) ^ i.1

@[simp] theorem rectangularCPhase_star_mul_self (n : ℕ) (θ : ℝ) :
    (rectangularCPhase n θ)ᴴ * rectangularCPhase n θ =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [rectangularCPhase, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  apply Matrix.diagonal_eq_diagonal_iff.mpr
  intro i
  rw [Pi.star_apply, star_pow, ← mul_pow, star_pathPhase_mul_pathPhase, one_pow]

@[simp] theorem rectangularCPhase_mul_star_self (n : ℕ) (θ : ℝ) :
    rectangularCPhase n θ * (rectangularCPhase n θ)ᴴ =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [rectangularCPhase, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  apply Matrix.diagonal_eq_diagonal_iff.mpr
  intro i
  rw [Pi.star_apply, star_pow, ← mul_pow, pathPhase_mul_star_pathPhase, one_pow]

/-- The `C` phase matrix is unitary. -/
theorem rectangularCPhase_mem_unitary (n : ℕ) (θ : ℝ) :
    rectangularCPhase n θ ∈
      unitary (Matrix (Fin n) (Fin n) ℂ) :=
  ⟨rectangularCPhase_star_mul_self n θ,
    rectangularCPhase_mul_star_self n θ⟩

@[simp] theorem rectangularDPhase_star_mul_self (n : ℕ) (θ : ℝ) :
    (rectangularDPhase n θ)ᴴ * rectangularDPhase n θ =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [rectangularDPhase, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  apply Matrix.diagonal_eq_diagonal_iff.mpr
  intro i
  rw [Pi.star_apply, star_pow, ← mul_pow, star_pathPhase_mul_pathPhase, one_pow]

@[simp] theorem rectangularDPhase_mul_star_self (n : ℕ) (θ : ℝ) :
    rectangularDPhase n θ * (rectangularDPhase n θ)ᴴ =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [rectangularDPhase, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  apply Matrix.diagonal_eq_diagonal_iff.mpr
  intro i
  rw [Pi.star_apply, star_pow, ← mul_pow, pathPhase_mul_star_pathPhase, one_pow]

/-- The `D` phase matrix is unitary. -/
theorem rectangularDPhase_mem_unitary (n : ℕ) (θ : ℝ) :
    rectangularDPhase n θ ∈
      unitary (Matrix (Fin n) (Fin n) ℂ) :=
  ⟨rectangularDPhase_star_mul_self n θ,
    rectangularDPhase_mul_star_self n θ⟩

private theorem diagonalPathPhase_conj_upper (n : ℕ) (θ : ℝ) :
    (diagonal fun i : Fin n => pathPhase θ ^ i.1)ᴴ *
        complexUpperShift n *
        diagonal (fun i : Fin n => pathPhase θ ^ i.1) =
      pathPhase θ • complexUpperShift n := by
  ext i j
  simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Pi.star_apply, complexUpperShift_apply,
    Matrix.smul_apply, smul_eq_mul]
  by_cases h : j.1 = i.1 + 1
  · rw [if_pos h, h, pow_succ]
    simp only [mul_one]
    rw [← mul_assoc, star_pathPhase_pow_mul_pathPhase_pow, one_mul]
  · simp [h]

private theorem diagonalPathPhase_conj_lower (n : ℕ) (θ : ℝ) :
    (diagonal fun i : Fin n => pathPhase θ ^ i.1)ᴴ *
        complexLowerShift n *
        diagonal (fun i : Fin n => pathPhase θ ^ i.1) =
      star (pathPhase θ) • complexLowerShift n := by
  calc
    (diagonal fun i : Fin n => pathPhase θ ^ i.1)ᴴ *
          complexLowerShift n *
          diagonal (fun i : Fin n => pathPhase θ ^ i.1) =
        ((diagonal fun i : Fin n => pathPhase θ ^ i.1)ᴴ *
          complexUpperShift n *
          diagonal (fun i : Fin n => pathPhase θ ^ i.1))ᴴ := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (pathPhase θ • complexUpperShift n)ᴴ := by
      rw [diagonalPathPhase_conj_upper]
    _ = star (pathPhase θ) • complexLowerShift n := by simp

theorem complexSymmetricPath_eq_shifts (n : ℕ) (r : ℝ) :
    complexSymmetricPath n r =
      (r : ℂ) • (complexUpperShift n + complexLowerShift n) := by
  ext i j
  simp only [complexSymmetricPath_apply, symmetricPath,
    Matrix.smul_apply, Matrix.add_apply, upperShift_apply,
    lowerShift_apply, complexUpperShift_apply, complexLowerShift_apply,
    smul_eq_mul]
  push_cast
  split_ifs <;> rfl

theorem symmetricPathGramMatrix_eq_shifts (n : ℕ) (r : ℝ) :
    symmetricPathGramMatrix n r =
      ((1 + r ^ 2 : ℝ) : ℂ) •
          (1 : Matrix (Fin n) (Fin n) ℂ) -
        (r : ℂ) • complexUpperShift n -
        (r : ℂ) • complexLowerShift n := by
  rw [symmetricPathGramMatrix, complexSymmetricPath_eq_shifts]
  push_cast
  rw [smul_add, sub_sub]
  rfl

private theorem pathRootPlus_eq_mul_pathPhase (r θ : ℝ) :
    pathRootPlus r θ = (r : ℂ) * pathPhase θ :=
  rfl

private theorem pathRootMinus_eq_mul_pathPhase (r θ : ℝ) :
    pathRootMinus r θ = (r : ℂ) * pathPhase (-θ) := by
  simp [pathRootMinus, pathPhase]

private theorem pathPhase_gram_scalar (r θ : ℝ) :
    star ((r : ℂ) * pathPhase θ) *
        ((r : ℂ) * pathPhase θ) + 1 =
      ((1 + r ^ 2 : ℝ) : ℂ) := by
  calc
    star ((r : ℂ) * pathPhase θ) *
          ((r : ℂ) * pathPhase θ) + 1 =
        ((r : ℂ) ^ 2) *
          (star (pathPhase θ) * pathPhase θ) + 1 := by
            rw [StarMul.star_mul,
              show star (r : ℂ) = (r : ℂ) by simp]
            ring
    _ = ((r : ℂ) ^ 2) + 1 := by
      rw [star_pathPhase_mul_pathPhase, mul_one]
    _ = ((1 + r ^ 2 : ℝ) : ℂ) := by push_cast; ring

private theorem rectangularC_gram_eq_shifts (n : ℕ) (r θ : ℝ) :
    (rectangularC n (pathRootPlus r θ))ᴴ *
        rectangularC n (pathRootPlus r θ) =
      ((1 + r ^ 2 : ℝ) : ℂ) •
          (1 : Matrix (Fin n) (Fin n) ℂ) -
        ((r : ℂ) * star (pathPhase θ)) • complexUpperShift n -
        ((r : ℂ) * pathPhase θ) • complexLowerShift n := by
  rw [rectangularC_gram, pathRootPlus_eq_mul_pathPhase,
    show conj ((r : ℂ) * pathPhase θ) =
      star ((r : ℂ) * pathPhase θ) from rfl,
    pathPhase_gram_scalar]
  congr 2
  simp

private theorem rectangularD_gram_eq_shifts (n : ℕ) (r θ : ℝ) :
    (rectangularD n (pathRootMinus r θ))ᴴ *
        rectangularD n (pathRootMinus r θ) =
      ((1 + r ^ 2 : ℝ) : ℂ) •
          (1 : Matrix (Fin n) (Fin n) ℂ) -
        ((r : ℂ) * star (pathPhase (-θ))) • complexUpperShift n -
        ((r : ℂ) * pathPhase (-θ)) • complexLowerShift n := by
  rw [rectangularD_gram, pathRootMinus_eq_mul_pathPhase,
    show conj ((r : ℂ) * pathPhase (-θ)) =
      star ((r : ℂ) * pathPhase (-θ)) from rfl]
  have hscalar := pathPhase_gram_scalar r (-θ)
  rw [add_comm 1, mul_comm ((r : ℂ) * pathPhase (-θ)), hscalar]
  congr 2
  simp

/-- Exact unitary congruence from the `C` Gram matrix to the real symmetric
path Gram matrix. -/
theorem rectangularC_gram_unitary_congruence (n : ℕ) (r θ : ℝ) :
    (rectangularCPhase n θ)ᴴ *
        ((rectangularC n (pathRootPlus r θ))ᴴ *
          rectangularC n (pathRootPlus r θ)) *
        rectangularCPhase n θ =
      symmetricPathGramMatrix n r := by
  have hupper :
      (rectangularCPhase n θ)ᴴ * complexUpperShift n *
          rectangularCPhase n θ =
        pathPhase θ • complexUpperShift n := by
    simpa only [rectangularCPhase] using
      diagonalPathPhase_conj_upper n θ
  have hlower :
      (rectangularCPhase n θ)ᴴ * complexLowerShift n *
          rectangularCPhase n θ =
        star (pathPhase θ) • complexLowerShift n := by
    simpa only [rectangularCPhase] using
      diagonalPathPhase_conj_lower n θ
  rw [rectangularC_gram_eq_shifts, symmetricPathGramMatrix_eq_shifts]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, rectangularCPhase_star_mul_self,
    hupper, hlower, smul_smul]
  simp only [mul_assoc]
  rw [star_pathPhase_mul_pathPhase, pathPhase_mul_star_pathPhase]
  simp

/-- Exact unitary congruence from the `D` Gram matrix to the same real
symmetric path Gram matrix. -/
theorem rectangularD_gram_unitary_congruence (n : ℕ) (r θ : ℝ) :
    (rectangularDPhase n θ)ᴴ *
        ((rectangularD n (pathRootMinus r θ))ᴴ *
          rectangularD n (pathRootMinus r θ)) *
        rectangularDPhase n θ =
      symmetricPathGramMatrix n r := by
  have hupper :
      (rectangularDPhase n θ)ᴴ * complexUpperShift n *
          rectangularDPhase n θ =
        pathPhase (-θ) • complexUpperShift n := by
    simpa only [rectangularDPhase] using
      diagonalPathPhase_conj_upper n (-θ)
  have hlower :
      (rectangularDPhase n θ)ᴴ * complexLowerShift n *
          rectangularDPhase n θ =
        star (pathPhase (-θ)) • complexLowerShift n := by
    simpa only [rectangularDPhase] using
      diagonalPathPhase_conj_lower n (-θ)
  rw [rectangularD_gram_eq_shifts, symmetricPathGramMatrix_eq_shifts]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, rectangularDPhase_star_mul_self,
    hupper, hlower, smul_smul]
  simp only [mul_assoc]
  rw [star_pathPhase_mul_pathPhase, pathPhase_mul_star_pathPhase]
  simp

private theorem gramShift_posSemidef_of_unitary_congruence {n : ℕ}
    (G H Q : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ)
    (hmul : Q * Qᴴ = 1)
    (hcong : Qᴴ * G * Q = H)
    (hH : (H - (δ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef) :
    (G - (δ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
  have hreverse : G = Q * H * Qᴴ := by
    calc
      G = (1 : Matrix (Fin n) (Fin n) ℂ) * G * 1 := by simp
      _ = (Q * Qᴴ) * G * (Q * Qᴴ) := by
        simp only [hmul, Matrix.one_mul, Matrix.mul_one]
      _ = Q * (Qᴴ * G * Q) * Qᴴ := by
        simp only [Matrix.mul_assoc]
      _ = Q * H * Qᴴ := by rw [hcong]
  have hshift :
      G - (δ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
        Q * (H - (δ : ℂ) • 1) * Qᴴ := by
    calc
      G - (δ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
          Q * H * Qᴴ - (δ : ℂ) • 1 := by rw [hreverse]
      _ = Q * H * Qᴴ - Q * ((δ : ℂ) • 1) * Qᴴ := by
        congr 1
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          hmul]
      _ = Q * (H - (δ : ℂ) • 1) * Qᴴ := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [hshift]
  exact hH.mul_mul_conjTranspose_same Q

/-- The `C` Gram matrix minus its sharp lower spectral endpoint is positive
semidefinite. -/
theorem rectangularC_gram_sub_lower_posSemidef (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ((rectangularC n (pathRootPlus r θ))ᴴ *
        rectangularC n (pathRootPlus r θ) -
      (symmetricPathGramLowerEigenvalue n r : ℂ) •
        (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
  exact gramShift_posSemidef_of_unitary_congruence
    ((rectangularC n (pathRootPlus r θ))ᴴ *
      rectangularC n (pathRootPlus r θ))
    (symmetricPathGramMatrix n r) (rectangularCPhase n θ)
    (symmetricPathGramLowerEigenvalue n r)
    (rectangularCPhase_mul_star_self n θ)
    (rectangularC_gram_unitary_congruence n r θ)
    (symmetricPathGram_sub_lower_posSemidef n hn hr)

/-- The analogous sharp semidefinite Gram shift for `D`. -/
theorem rectangularD_gram_sub_lower_posSemidef (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ((rectangularD n (pathRootMinus r θ))ᴴ *
        rectangularD n (pathRootMinus r θ) -
      (symmetricPathGramLowerEigenvalue n r : ℂ) •
        (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
  exact gramShift_posSemidef_of_unitary_congruence
    ((rectangularD n (pathRootMinus r θ))ᴴ *
      rectangularD n (pathRootMinus r θ))
    (symmetricPathGramMatrix n r) (rectangularDPhase n θ)
    (symmetricPathGramLowerEigenvalue n r)
    (rectangularDPhase_mul_star_self n θ)
    (rectangularD_gram_unitary_congruence n r θ)
    (symmetricPathGram_sub_lower_posSemidef n hn hr)

private theorem gramShift_not_posDef_of_unitary_congruence {n : ℕ}
    (G H Q : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ)
    (hstar : Qᴴ * Q = 1) (hcong : Qᴴ * G * Q = H)
    (hH : ¬(H - (δ : ℂ) •
      (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef) :
    ¬(G - (δ : ℂ) •
      (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := by
  intro hG
  have hQinj : Function.Injective Q.mulVec := by
    have hleft : Function.LeftInverse Qᴴ.mulVec Q.mulVec := by
      intro x
      rw [mulVec_mulVec, hstar, one_mulVec]
    exact hleft.injective
  have htrans := hG.conjTranspose_mul_mul_same hQinj
  apply hH
  have hshift :
      Qᴴ * (G - (δ : ℂ) •
          (1 : Matrix (Fin n) (Fin n) ℂ)) * Q =
        H - (δ : ℂ) • 1 := by
    calc
      Qᴴ * (G - (δ : ℂ) •
            (1 : Matrix (Fin n) (Fin n) ℂ)) * Q =
          Qᴴ * G * Q - Qᴴ * ((δ : ℂ) • 1) * Q := by
            rw [Matrix.mul_sub, Matrix.sub_mul]
      _ = H - (δ : ℂ) • (Qᴴ * Q) := by
        rw [hcong]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = H - (δ : ℂ) • 1 := by rw [hstar]
  rw [← hshift]
  exact htrans

/-- The endpoint in the `C` Gram bound is not positive definite, certifying
that the lower coefficient cannot be increased. -/
theorem rectangularC_gram_sub_lower_not_posDef (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ¬((rectangularC n (pathRootPlus r θ))ᴴ *
        rectangularC n (pathRootPlus r θ) -
      (symmetricPathGramLowerEigenvalue n r : ℂ) •
        (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := by
  exact gramShift_not_posDef_of_unitary_congruence
    ((rectangularC n (pathRootPlus r θ))ᴴ *
      rectangularC n (pathRootPlus r θ))
    (symmetricPathGramMatrix n r) (rectangularCPhase n θ)
    (symmetricPathGramLowerEigenvalue n r)
    (rectangularCPhase_star_mul_self n θ)
    (rectangularC_gram_unitary_congruence n r θ)
    (symmetricPathGram_sub_lower_not_posDef n hn hr)

/-- The endpoint in the `D` Gram bound is likewise sharp. -/
theorem rectangularD_gram_sub_lower_not_posDef (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ¬((rectangularD n (pathRootMinus r θ))ᴴ *
        rectangularD n (pathRootMinus r θ) -
      (symmetricPathGramLowerEigenvalue n r : ℂ) •
        (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := by
  exact gramShift_not_posDef_of_unitary_congruence
    ((rectangularD n (pathRootMinus r θ))ᴴ *
      rectangularD n (pathRootMinus r θ))
    (symmetricPathGramMatrix n r) (rectangularDPhase n θ)
    (symmetricPathGramLowerEigenvalue n r)
    (rectangularDPhase_star_mul_self n θ)
    (rectangularD_gram_unitary_congruence n r θ)
    (symmetricPathGram_sub_lower_not_posDef n hn hr)

private theorem star_dotProduct_self_eq_norm_toLp_sq_rectangular
    {n : ℕ} (x : Fin n → ℂ) :
    star x ⬝ᵥ x = ((‖WithLp.toLp 2 x‖ ^ 2 : ℝ) : ℂ) := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp]
  simp

private theorem star_dotProduct_rectangularGramShift_mulVec
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (δ : ℝ)
    (x : Fin n → ℂ) :
    star x ⬝ᵥ
        (((Mᴴ * M) - (δ : ℂ) •
          (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ x) =
      ((‖WithLp.toLp 2 (M *ᵥ x)‖ ^ 2 -
        δ * ‖WithLp.toLp 2 x‖ ^ 2 : ℝ) : ℂ) := by
  have hMx := star_dotProduct_self_eq_norm_toLp_sq_rectangular (M *ᵥ x)
  have hx := star_dotProduct_self_eq_norm_toLp_sq_rectangular x
  rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec,
    dotProduct_mulVec, vecMul_conjTranspose, star_star,
    smul_mulVec, one_mulVec, dotProduct_smul, hMx, hx]
  simp

/-- Sharp homogeneous squared-norm lower bound for the first rectangular
factor.  The coefficient is the exact bottom eigenvalue of its Gram matrix. -/
theorem rectangularC_norm_sq_lower_bound (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) (x : Fin n → ℂ) :
    (1 + r ^ 2 -
        2 * r * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ))) *
        ‖WithLp.toLp 2 x‖ ^ 2 ≤
      ‖WithLp.toLp 2
        (rectangularC n (pathRootPlus r θ) *ᵥ x)‖ ^ 2 := by
  have hquad :=
    (rectangularC_gram_sub_lower_posSemidef n hn hr θ).dotProduct_mulVec_nonneg x
  rw [star_dotProduct_rectangularGramShift_mulVec] at hquad
  have hreal :
      0 ≤ ‖WithLp.toLp 2
          (rectangularC n (pathRootPlus r θ) *ᵥ x)‖ ^ 2 -
        symmetricPathGramLowerEigenvalue n r *
          ‖WithLp.toLp 2 x‖ ^ 2 := by
    exact_mod_cast hquad
  rw [symmetricPathGramLowerEigenvalue_eq] at hreal
  linarith

/-- Sharp homogeneous squared-norm lower bound for the second rectangular
factor. -/
theorem rectangularD_norm_sq_lower_bound (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) (x : Fin n → ℂ) :
    (1 + r ^ 2 -
        2 * r * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ))) *
        ‖WithLp.toLp 2 x‖ ^ 2 ≤
      ‖WithLp.toLp 2
        (rectangularD n (pathRootMinus r θ) *ᵥ x)‖ ^ 2 := by
  have hquad :=
    (rectangularD_gram_sub_lower_posSemidef n hn hr θ).dotProduct_mulVec_nonneg x
  rw [star_dotProduct_rectangularGramShift_mulVec] at hquad
  have hreal :
      0 ≤ ‖WithLp.toLp 2
          (rectangularD n (pathRootMinus r θ) *ᵥ x)‖ ^ 2 -
        symmetricPathGramLowerEigenvalue n r *
          ‖WithLp.toLp 2 x‖ ^ 2 := by
    exact_mod_cast hquad
  rw [symmetricPathGramLowerEigenvalue_eq] at hreal
  linarith

theorem symmetricPathGramLowerEigenvalue_nonneg (n : ℕ)
    {r : ℝ} (hr : 0 < r) :
    0 ≤ symmetricPathGramLowerEigenvalue n r := by
  have hscale : 0 ≤ 2 * r := mul_nonneg (by norm_num) hr.le
  have hcos := mul_le_mul_of_nonneg_left
    (Real.cos_le_one (Real.pi / ((n + 1 : ℕ) : ℝ))) hscale
  rw [symmetricPathGramLowerEigenvalue_eq]
  nlinarith [sq_nonneg (r - 1)]

/-- Unsquared Euclidean norm form of the sharp `C` bound. -/
theorem rectangularC_norm_lower_bound (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) (x : Fin n → ℂ) :
    Real.sqrt
        (1 + r ^ 2 -
          2 * r * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ))) *
        ‖WithLp.toLp 2 x‖ ≤
      ‖WithLp.toLp 2
        (rectangularC n (pathRootPlus r θ) *ᵥ x)‖ := by
  have hsq := rectangularC_norm_sq_lower_bound n hn hr θ x
  change symmetricPathGramLowerEigenvalue n r *
      ‖WithLp.toLp 2 x‖ ^ 2 ≤ _ at hsq
  have hδ := symmetricPathGramLowerEigenvalue_nonneg n hr
  change Real.sqrt (symmetricPathGramLowerEigenvalue n r) *
      ‖WithLp.toLp 2 x‖ ≤ _
  apply (sq_le_sq₀
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (norm_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt hδ]
  exact hsq

/-- Unsquared Euclidean norm form of the sharp `D` bound. -/
theorem rectangularD_norm_lower_bound (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) (x : Fin n → ℂ) :
    Real.sqrt
        (1 + r ^ 2 -
          2 * r * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ))) *
        ‖WithLp.toLp 2 x‖ ≤
      ‖WithLp.toLp 2
        (rectangularD n (pathRootMinus r θ) *ᵥ x)‖ := by
  have hsq := rectangularD_norm_sq_lower_bound n hn hr θ x
  change symmetricPathGramLowerEigenvalue n r *
      ‖WithLp.toLp 2 x‖ ^ 2 ≤ _ at hsq
  have hδ := symmetricPathGramLowerEigenvalue_nonneg n hr
  change Real.sqrt (symmetricPathGramLowerEigenvalue n r) *
      ‖WithLp.toLp 2 x‖ ≤ _
  apply (sq_le_sq₀
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (norm_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt hδ]
  exact hsq

end

end ConnectedPseudospectrum
