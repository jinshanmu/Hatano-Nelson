import ConnectedPseudospectrum.Spectrum
import Mathlib.Analysis.Matrix.PosDef

/-!
# Ordered Hermitian spectrum of the symmetric finite path

This module identifies Mathlib's decreasingly ordered Hermitian eigenvalues
with the explicit Dirichlet cosine list.  The identification is obtained from
the already proved diagonal similarity and characteristic polynomial, followed
by sorting the roots; it is not assumed from the existence of eigenvectors.
-/

namespace ConnectedPseudospectrum

open Matrix Polynomial
open scoped ComplexOrder

noncomputable section

/-- The symmetric real path, cast entrywise to a complex matrix. -/
def complexSymmetricPath (n : ℕ) (r : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (symmetricPath n r).map (algebraMap ℝ ℂ)

@[simp] theorem complexSymmetricPath_apply (n : ℕ) (r : ℝ) (i j : Fin n) :
    complexSymmetricPath n r i j = (symmetricPath n r i j : ℂ) :=
  rfl

/-- The complex cast of the symmetric path is Hermitian. -/
theorem complexSymmetricPath_isHermitian (n : ℕ) (r : ℝ) :
    (complexSymmetricPath n r).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [complexSymmetricPath, symmetricPath, Matrix.conjTranspose_apply,
    upperShift_apply, lowerShift_apply, add_comm]

/-- The real symmetric path has the explicit characteristic polynomial. -/
theorem charpoly_symmetricPath (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (symmetricPath n r).charpoly =
      ∏ k : Fin n, (Polynomial.X -
        Polynomial.C (symmetricPathEigenvalue n r k)) := by
  calc
    (symmetricPath n r).charpoly =
        (diagonalGaugeInv n r *
          (diagonalGauge n r * symmetricPath n r)).charpoly := by
      rw [← Matrix.mul_assoc, diagonalGaugeInv_mul n hr.ne', Matrix.one_mul]
    _ = ((diagonalGauge n r * symmetricPath n r) *
          diagonalGaugeInv n r).charpoly :=
      Matrix.charpoly_mul_comm _ _
    _ = (pathMatrix n (r ^ 2)).charpoly := by
      rw [← pathMatrix_eq_gauge_symmetricPath_mul_inv n hr.ne']
    _ = ∏ k : Fin n, (Polynomial.X -
          Polynomial.C (symmetricPathEigenvalue n r k)) :=
      charpoly_pathMatrix_sq n hr

/-- After casting to `ℂ`, the characteristic polynomial retains the same
explicit linear factorization. -/
theorem charpoly_complexSymmetricPath (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (complexSymmetricPath n r).charpoly =
      ∏ k : Fin n, (Polynomial.X -
        Polynomial.C ((algebraMap ℝ ℂ)
          (symmetricPathEigenvalue n r k))) := by
  rw [complexSymmetricPath, Matrix.charpoly_map, charpoly_symmetricPath n hr]
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro k _
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

/-- The roots of the complex characteristic polynomial are precisely the
explicit, pairwise-distinct real eigenvalues, with multiplicity one. -/
theorem roots_charpoly_complexSymmetricPath (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (complexSymmetricPath n r).charpoly.roots =
      Multiset.map (fun k : Fin n =>
        (algebraMap ℝ ℂ) (symmetricPathEigenvalue n r k)) Finset.univ.val := by
  rw [charpoly_complexSymmetricPath n hr, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- The explicit decreasing list reindexed to the canonical domain used by
`Matrix.IsHermitian.eigenvalues₀`. -/
def orderedSymmetricPathEigenvalue (n : ℕ) (r : ℝ) :
    Fin (Fintype.card (Fin n)) → ℝ :=
  fun i => symmetricPathEigenvalue n r
    (finCongr (Fintype.card_fin n) i)

theorem orderedSymmetricPathEigenvalue_strictAnti (n : ℕ) {r : ℝ}
    (hr : 0 < r) :
    StrictAnti (orderedSymmetricPathEigenvalue n r) := by
  intro i j hij
  apply symmetricPathEigenvalue_strictAnti n hr
  change i.1 < j.1 at hij
  simpa [orderedSymmetricPathEigenvalue] using hij

theorem ofFn_orderedSymmetricPathEigenvalue (n : ℕ) (r : ℝ) :
    List.ofFn (orderedSymmetricPathEigenvalue n r) =
      List.ofFn (symmetricPathEigenvalue n r) := by
  rw [List.ofFn_congr (Fintype.card_fin n)]
  congr 1

/-- Mathlib's decreasingly ordered Hermitian eigenvalues are exactly the
paper's decreasing Dirichlet cosine list. -/
theorem complexSymmetricPath_eigenvalues₀ (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (complexSymmetricPath_isHermitian n r).eigenvalues₀ =
      orderedSymmetricPathEigenvalue n r := by
  let hA := complexSymmetricPath_isHermitian n r
  change hA.eigenvalues₀ = orderedSymmetricPathEigenvalue n r
  rw [← List.ofFn_inj]
  rw [ofFn_orderedSymmetricPathEigenvalue n r]
  rw [← hA.sort_roots_charpoly_eq_eigenvalues₀]
  rw [roots_charpoly_complexSymmetricPath n hr]
  rw [Fin.univ_val_map]
  simp only [Multiset.map_coe, List.map_ofFn,
    RCLike.algebraMap_eq_ofReal, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact (symmetricPathEigenvalue_strictAnti n hr).antitone.sortedGE_ofFn

/-- The largest explicit path eigenvalue. -/
def symmetricPathTopEigenvalue (n : ℕ) (r : ℝ) : ℝ :=
  2 * r * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ))

theorem symmetricPathEigenvalue_first (n : ℕ) (hn : 0 < n) (r : ℝ) :
    symmetricPathEigenvalue n r (⟨0, hn⟩ : Fin n) =
      symmetricPathTopEigenvalue n r := by
  simp [symmetricPathEigenvalue, pathEigenangle, symmetricPathTopEigenvalue]

/-- Every Mathlib Hermitian eigenvalue of the symmetric path is bounded above
by the explicit first Dirichlet eigenvalue. -/
theorem complexSymmetricPath_eigenvalues_le_top (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (i : Fin n) :
    (complexSymmetricPath_isHermitian n r).eigenvalues i ≤
      symmetricPathTopEigenvalue n r := by
  unfold Matrix.IsHermitian.eigenvalues
  rw [complexSymmetricPath_eigenvalues₀ n hr]
  rw [← symmetricPathEigenvalue_first n hn r]
  apply (symmetricPathEigenvalue_strictAnti n hr).antitone
  change 0 ≤ _
  exact Nat.zero_le _

/-- The sharp upper spectral endpoint gives a positive-semidefinite shift of
the complex symmetric path. -/
theorem symmetricPathTop_sub_posSemidef (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) :
    ((algebraMap ℝ ℂ) (symmetricPathTopEigenvalue n r) •
        (1 : Matrix (Fin n) (Fin n) ℂ) -
      complexSymmetricPath n r).PosSemidef := by
  let A := complexSymmetricPath n r
  let hA : A.IsHermitian := complexSymmetricPath_isHermitian n r
  let top := symmetricPathTopEigenvalue n r
  let delta : Fin n → ℂ := fun i =>
    (algebraMap ℝ ℂ) (top - hA.eigenvalues i)
  have hdelta : ∀ i, 0 ≤ delta i := by
    intro i
    change 0 ≤ (algebraMap ℝ ℂ) (top - hA.eigenvalues i)
    rw [RCLike.algebraMap_eq_ofReal, RCLike.ofReal_nonneg]
    exact sub_nonneg.mpr (complexSymmetricPath_eigenvalues_le_top n hn hr i)
  have hdiag : (diagonal delta).PosSemidef :=
    Matrix.PosSemidef.diagonal hdelta
  let U : Matrix (Fin n) (Fin n) ℂ := hA.eigenvectorUnitary
  have hconj : (U * diagonal delta * Uᴴ).PosSemidef :=
    hdiag.mul_mul_conjTranspose_same U
  have hU : U * Uᴴ = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    change (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
      star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) = 1
    exact Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hdeltaMatrix :
      diagonal delta =
        (algebraMap ℝ ℂ) top • (1 : Matrix (Fin n) (Fin n) ℂ) -
          diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [delta, RCLike.algebraMap_eq_ofReal]
    · simp [delta, hij]
  have hspectral :
      A = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * Uᴴ := by
    calc
      A = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := hA.spectral_theorem
      _ = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * Uᴴ := by rfl
  have heq :
      (algebraMap ℝ ℂ) top • (1 : Matrix (Fin n) (Fin n) ℂ) - A =
        U * diagonal delta * Uᴴ := by
    calc
      (algebraMap ℝ ℂ) top • (1 : Matrix (Fin n) (Fin n) ℂ) - A =
          (algebraMap ℝ ℂ) top • (1 : Matrix (Fin n) (Fin n) ℂ) -
            U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * Uᴴ := by
        exact congrArg
          (fun X : Matrix (Fin n) (Fin n) ℂ =>
            (algebraMap ℝ ℂ) top • 1 - X) hspectral
      _ = U * ((algebraMap ℝ ℂ) top •
            (1 : Matrix (Fin n) (Fin n) ℂ) -
              diagonal (RCLike.ofReal ∘ hA.eigenvalues)) * Uᴴ := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
        simp [Matrix.mul_assoc, hU]
      _ = U * diagonal delta * Uᴴ := by rw [hdeltaMatrix]
  rw [show complexSymmetricPath n r = A from rfl,
    show symmetricPathTopEigenvalue n r = top from rfl, heq]
  exact hconj

/-- The endpoint shift is singular, so the preceding semidefinite bound is
sharp. -/
theorem det_symmetricPathTop_sub_eq_zero (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) :
    ((algebraMap ℝ ℂ) (symmetricPathTopEigenvalue n r) •
        (1 : Matrix (Fin n) (Fin n) ℂ) -
      complexSymmetricPath n r).det = 0 := by
  let first : Fin n := ⟨0, hn⟩
  have hroot :
      (complexSymmetricPath n r).charpoly.eval
        ((algebraMap ℝ ℂ) (symmetricPathTopEigenvalue n r)) = 0 := by
    rw [charpoly_complexSymmetricPath n hr, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ first)
    simp [first, symmetricPathEigenvalue_first n hn r]
  rw [Matrix.smul_one_eq_diagonal, ← Matrix.scalar_apply,
    ← Matrix.eval_charpoly]
  exact hroot

theorem symmetricPathTop_sub_not_posDef (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) :
    ¬((algebraMap ℝ ℂ) (symmetricPathTopEigenvalue n r) •
        (1 : Matrix (Fin n) (Fin n) ℂ) -
      complexSymmetricPath n r).PosDef := by
  intro hpos
  have hunit := Matrix.PosDef.isUnit hpos
  have hdetunit :=
    ((algebraMap ℝ ℂ) (symmetricPathTopEigenvalue n r) •
      (1 : Matrix (Fin n) (Fin n) ℂ) -
        complexSymmetricPath n r).isUnit_iff_isUnit_det.mp hunit
  rw [det_symmetricPathTop_sub_eq_zero n hn hr] at hdetunit
  exact not_isUnit_zero hdetunit

/-- The Hermitian matrix `(1+r²)I-S_n(r)` occurring in the Gram estimate. -/
def symmetricPathGramMatrix (n : ℕ) (r : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (algebraMap ℝ ℂ) (1 + r ^ 2) • 1 - complexSymmetricPath n r

/-- Its sharp lower spectral endpoint. -/
def symmetricPathGramLowerEigenvalue (n : ℕ) (r : ℝ) : ℝ :=
  1 + r ^ 2 - symmetricPathTopEigenvalue n r

theorem symmetricPathGramLowerEigenvalue_eq (n : ℕ) (r : ℝ) :
    symmetricPathGramLowerEigenvalue n r =
      1 + r ^ 2 -
        2 * r * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ)) :=
  rfl

theorem symmetricPathGram_sub_lower_eq_top_sub (n : ℕ) (r : ℝ) :
    symmetricPathGramMatrix n r -
        (algebraMap ℝ ℂ) (symmetricPathGramLowerEigenvalue n r) •
          (1 : Matrix (Fin n) (Fin n) ℂ) =
      (algebraMap ℝ ℂ) (symmetricPathTopEigenvalue n r) • 1 -
        complexSymmetricPath n r := by
  ext i j
  simp only [symmetricPathGramMatrix, symmetricPathGramLowerEigenvalue,
    Matrix.sub_apply, Matrix.smul_apply]
  push_cast
  simp only [smul_eq_mul]
  ring

/-- Subtracting the sharp lower endpoint from `(1+r²)I-S_n(r)` leaves a
positive-semidefinite matrix. -/
theorem symmetricPathGram_sub_lower_posSemidef (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) :
    (symmetricPathGramMatrix n r -
      (algebraMap ℝ ℂ) (symmetricPathGramLowerEigenvalue n r) •
        (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
  rw [symmetricPathGram_sub_lower_eq_top_sub]
  exact symmetricPathTop_sub_posSemidef n hn hr

theorem symmetricPathGram_sub_lower_not_posDef (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) :
    ¬(symmetricPathGramMatrix n r -
      (algebraMap ℝ ℂ) (symmetricPathGramLowerEigenvalue n r) •
        (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := by
  rw [symmetricPathGram_sub_lower_eq_top_sub]
  exact symmetricPathTop_sub_not_posDef n hn hr

/-- Every scalar strictly below the sharp lower endpoint can be subtracted
while preserving positive definiteness. -/
theorem symmetricPathGram_sub_posDef_of_lt (n : ℕ) (hn : 0 < n)
    {r t : ℝ} (hr : 0 < r)
    (ht : t < symmetricPathGramLowerEigenvalue n r) :
    (symmetricPathGramMatrix n r -
      (algebraMap ℝ ℂ) t • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := by
  have hendpoint := symmetricPathGram_sub_lower_posSemidef n hn hr
  have hscalar :
      ((algebraMap ℝ ℂ)
        (symmetricPathGramLowerEigenvalue n r - t) •
          (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.posDef_diagonal_iff]
    intro i
    rw [RCLike.algebraMap_eq_ofReal, RCLike.ofReal_pos]
    exact sub_pos.mpr ht
  have hsum := Matrix.PosDef.posSemidef_add hendpoint hscalar
  convert hsum using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  push_cast
  simp only [smul_eq_mul]
  ring

end

end ConnectedPseudospectrum
