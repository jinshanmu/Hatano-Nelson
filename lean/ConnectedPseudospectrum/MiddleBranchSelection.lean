import ConnectedPseudospectrum.MiddleBranchInertia
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Selection of the signed middle eigenvalue branch

This module continues `lem:middle-branch` after the inertia computation.  It
develops the ordered-eigenvalue comparison tools used by the even rank-two
argument and the odd Cauchy-interlacing argument, then applies them to the
signed middle matrix.
-/

namespace ConnectedPseudospectrum

open Matrix Module
open scoped Count

noncomputable section

/-- Over `ℝ`, a symmetric matrix is Hermitian. -/
theorem Matrix.IsSymm.isHermitianReal {n : Type*}
    {A : Matrix n n ℝ} (hA : A.IsSymm) : A.IsHermitian := by
  rw [Matrix.IsHermitian]
  simpa using hA.eq

/-- The decreasingly ordered Hermitian eigenvalues, transported from
Mathlib's canonical `Fin (card (Fin n))` index to `Fin n` by `finCongr`.
Unlike `Matrix.IsHermitian.eigenvalues`, this transport is order preserving. -/
def orderedHermitianEigenvalue {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) : Fin n → ℝ :=
  fun i ↦ hA.eigenvalues₀ ((finCongr (Fintype.card_fin n)).symm i)

/-- Mathlib's ordered orthonormal eigenbasis, with the same canonical
order-preserving transport to `Fin n`. -/
def orderedHermitianEigenbasis {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  ((isHermitian_iff_isSymmetric.1 hA).eigenvectorBasis
      finrank_euclideanSpace).reindex
    (finCongr (Fintype.card_fin n))

/-- Orthogonal matrix whose columns are the decreasingly ordered Hermitian
eigenvectors. -/
def orderedHermitianEigenvectorMatrix {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    Matrix (Fin n) (Fin n) ℝ :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix
    (orderedHermitianEigenbasis hA).toBasis

@[simp] theorem orderedHermitianEigenvectorMatrix_col {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (i : Fin n) :
    (orderedHermitianEigenvectorMatrix hA).col i =
      ⇑(orderedHermitianEigenbasis hA i) :=
  rfl

@[simp] theorem orderedHermitianEigenvectorMatrix_apply {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (p i : Fin n) :
    orderedHermitianEigenvectorMatrix hA p i =
      ⇑(orderedHermitianEigenbasis hA i) p :=
  rfl

/-- The ordered matrix really consists of eigenvectors with the displayed
ordered eigenvalues. -/
theorem mulVec_orderedHermitianEigenbasis {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (i : Fin n) :
    A *ᵥ ⇑(orderedHermitianEigenbasis hA i) =
      orderedHermitianEigenvalue hA i •
        ⇑(orderedHermitianEigenbasis hA i) := by
  simpa only [orderedHermitianEigenbasis, orderedHermitianEigenvalue,
    OrthonormalBasis.reindex_apply, Matrix.toLpLin_apply,
    RCLike.real_smul_eq_coe_smul] using
      congr(⇑$((isHermitian_iff_isSymmetric.1 hA).apply_eigenvectorBasis
        finrank_euclideanSpace
        ((finCongr (Fintype.card_fin n)).symm i)))

/-- The ordered eigenvalues decrease with their `Fin n` index. -/
theorem orderedHermitianEigenvalue_antitone {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    Antitone (orderedHermitianEigenvalue hA) := by
  intro i j hij
  apply hA.eigenvalues₀_antitone
  change i.1 ≤ j.1 at hij ⊢
  simpa [orderedHermitianEigenvalue] using hij

/-- The ordered eigenvector matrix is orthogonal. -/
theorem orderedHermitianEigenvectorMatrix_mem_orthogonal {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    orderedHermitianEigenvectorMatrix hA ∈
      Matrix.orthogonalGroup (Fin n) ℝ := by
  exact OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal
    (EuclideanSpace.basisFun (Fin n) ℝ)
    (orderedHermitianEigenbasis hA)

/-- Spectral coordinates of a real Hermitian matrix. -/
def hermitianCoordinates {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (v : Fin n → ℝ) : Fin n → ℝ :=
  (orderedHermitianEigenvectorMatrix hA)ᵀ *ᵥ v

/-- Parseval identity for the spectral coordinates chosen by Mathlib's
Hermitian spectral theorem. -/
theorem sum_sq_hermitianCoordinates {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (v : Fin n → ℝ) :
    ∑ i, (hermitianCoordinates hA v i) ^ 2 = v ⬝ᵥ v := by
  let U : Matrix (Fin n) (Fin n) ℝ :=
    orderedHermitianEigenvectorMatrix hA
  have hUt : U * Uᵀ = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    exact (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp
      (orderedHermitianEigenvectorMatrix_mem_orthogonal hA)
  calc
    ∑ i, (hermitianCoordinates hA v i) ^ 2 =
        (Uᵀ *ᵥ v) ⬝ᵥ (Uᵀ *ᵥ v) := by
      simp only [hermitianCoordinates, U, dotProduct, pow_two]
    _ = v ⬝ᵥ v := by
      rw [dotProduct_mulVec, vecMul_transpose]
      rw [Matrix.mulVec_mulVec, hUt, Matrix.one_mulVec]

/-- Quadratic form written in Mathlib's decreasingly ordered Hermitian
eigenbasis. -/
theorem dotProduct_mulVec_eq_sum_eigenvalues_mul_sq {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (v : Fin n → ℝ) :
    v ⬝ᵥ (A *ᵥ v) =
      ∑ i, orderedHermitianEigenvalue hA i *
        (hermitianCoordinates hA v i) ^ 2 := by
  let U : Matrix (Fin n) (Fin n) ℝ :=
    orderedHermitianEigenvectorMatrix hA
  let D : Matrix (Fin n) (Fin n) ℝ :=
    diagonal (orderedHermitianEigenvalue hA)
  have hAU : A * U = U * D := by
    ext p i
    change (A *ᵥ (orderedHermitianEigenvectorMatrix hA).col i) p = _
    rw [orderedHermitianEigenvectorMatrix_col,
      mulVec_orderedHermitianEigenbasis]
    simp [D, U, smul_eq_mul, mul_comm]
  have hUUt : U * Uᵀ = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    exact (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp
      (orderedHermitianEigenvectorMatrix_mem_orthogonal hA)
  have hspectral : A = U * D * Uᵀ := by
    calc
      A = A * (U * Uᵀ) := by rw [hUUt, Matrix.mul_one]
      _ = (A * U) * Uᵀ := by noncomm_ring
      _ = U * D * Uᵀ := by rw [hAU]
  conv_lhs => rw [hspectral]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [dotProduct_mulVec]
  rw [← mulVec_transpose]
  simp only [D, mulVec_diagonal, dotProduct, hermitianCoordinates]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Extend a `Fin q` vector by zeros to a `Fin n` vector. -/
def finPrefixPad {q n : ℕ} :
    (Fin q → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun c i := if hi : i.1 < q then c ⟨i.1, hi⟩ else 0
  map_add' c d := by
    funext i
    by_cases hi : i.1 < q <;> simp only [hi, dite_true, dite_false,
      Pi.add_apply, zero_add]
  map_smul' s c := by
    funext i
    by_cases hi : i.1 < q <;> simp only [hi, dite_true, dite_false,
      Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_zero]

/-- Restrict a `Fin n` vector to its first `q` coordinates. -/
def finPrefixTake {q n : ℕ} (hqn : q ≤ n) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin q → ℝ) where
  toFun v i := v ⟨i.1, lt_of_lt_of_le i.2 hqn⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem finPrefixTake_pad {q n : ℕ} (hqn : q ≤ n)
    (c : Fin q → ℝ) :
    finPrefixTake hqn (finPrefixPad c) = c := by
  funext i
  simp [finPrefixTake, finPrefixPad, i.2]

theorem finPrefixPad_injective {q n : ℕ} (hqn : q ≤ n) :
    Function.Injective (finPrefixPad : (Fin q → ℝ) →ₗ[ℝ] (Fin n → ℝ)) := by
  intro c d hcd
  have := congrArg (finPrefixTake hqn) hcd
  simpa only [finPrefixTake_pad] using this

/-- Synthesizing coefficients with the ordered eigenvector matrix is
injective. -/
theorem orderedHermitianEigenvectorMatrix_mulVec_injective {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    Function.Injective
      (fun v ↦ orderedHermitianEigenvectorMatrix hA *ᵥ v) := by
  let U := orderedHermitianEigenvectorMatrix hA
  change Function.Injective (fun v ↦ U *ᵥ v)
  have hUtU : Uᵀ * U = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    exact (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp
      (orderedHermitianEigenvectorMatrix_mem_orthogonal hA)
  intro v w hvw
  have h := congrArg (fun z ↦ Uᵀ *ᵥ z) hvw
  simpa only [Matrix.mulVec_mulVec, hUtU, Matrix.one_mulVec] using h

/-- Spectral coordinates undo synthesis by the ordered orthogonal
eigenvector matrix. -/
@[simp] theorem hermitianCoordinates_orderedEigenvectorMatrix_mulVec
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (c : Fin n → ℝ) :
    hermitianCoordinates hA
        (orderedHermitianEigenvectorMatrix hA *ᵥ c) = c := by
  unfold hermitianCoordinates
  have hUtU :
      (orderedHermitianEigenvectorMatrix hA)ᵀ *
          orderedHermitianEigenvectorMatrix hA =
        (1 : Matrix (Fin n) (Fin n) ℝ) := by
    exact (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp
      (orderedHermitianEigenvectorMatrix_mem_orthogonal hA)
  rw [Matrix.mulVec_mulVec]
  rw [hUtU]
  exact Matrix.one_mulVec c

/-- A vector supported in spectral coordinates `k,…,n-1` has Rayleigh
quotient at most the `k`-th decreasing eigenvalue. -/
theorem dotProduct_mulVec_le_orderedEigenvalue_mul_dotProduct
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (k : Fin n) (v : Fin n → ℝ)
    (hzero : ∀ i : Fin n, i < k → hermitianCoordinates hA v i = 0) :
    v ⬝ᵥ (A *ᵥ v) ≤ orderedHermitianEigenvalue hA k * (v ⬝ᵥ v) := by
  rw [dotProduct_mulVec_eq_sum_eigenvalues_mul_sq hA v,
    ← sum_sq_hermitianCoordinates hA v, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hik : i < k
  · rw [hzero i hik]
    simp
  · exact mul_le_mul_of_nonneg_right
      ((orderedHermitianEigenvalue_antitone hA) (by omega))
      (sq_nonneg _)

/-- A vector supported in spectral coordinates `0,…,k` has Rayleigh
quotient at least the `k`-th decreasing eigenvalue. -/
theorem orderedEigenvalue_mul_dotProduct_le_dotProduct_mulVec
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (k : Fin n) (v : Fin n → ℝ)
    (hzero : ∀ i : Fin n, k < i → hermitianCoordinates hA v i = 0) :
    orderedHermitianEigenvalue hA k * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v) := by
  rw [dotProduct_mulVec_eq_sum_eigenvalues_mul_sq hA v,
    ← sum_sq_hermitianCoordinates hA v, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hki : k < i
  · rw [hzero i hki]
    simp
  · exact mul_le_mul_of_nonneg_right
      ((orderedHermitianEigenvalue_antitone hA) (by omega))
      (sq_nonneg _)

/-- Nonzero real vectors have strictly positive Euclidean squared length. -/
theorem dotProduct_self_pos {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) :
    0 < v ⬝ᵥ v := by
  have hnonneg : 0 ≤ v ⬝ᵥ v := by
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (v i)
  have hne : v ⬝ᵥ v ≠ 0 := fun h ↦ hv (dotProduct_self_eq_zero.mp h)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- A positive-semidefinite difference orders all real quadratic forms. -/
theorem dotProduct_mulVec_le_of_sub_posSemidef {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hBA : (B - A).PosSemidef)
    (v : Fin n → ℝ) :
    v ⬝ᵥ (A *ᵥ v) ≤ v ⬝ᵥ (B *ᵥ v) := by
  have h := hBA.dotProduct_mulVec_nonneg v
  simpa only [star_trivial, Matrix.sub_mulVec, dotProduct_sub,
    sub_nonneg] using h

/-- The overlap map used in the one-sided Weyl monotonicity proof: its
kernel supplies a vector in the first `k+1` spectral modes of `A` and the
last `n-k` spectral modes of `B`. -/
def orderedSpectralOverlap {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : Fin n) :
    (Fin (k.1 + 1) → ℝ) →ₗ[ℝ] (Fin k.1 → ℝ) :=
  (finPrefixTake (Nat.le_of_lt k.2)).comp <|
      (orderedHermitianEigenvectorMatrix hB)ᵀ.mulVecLin.comp <|
      (orderedHermitianEigenvectorMatrix hA).mulVecLin.comp <|
        finPrefixPad

/-- Loewner monotonicity of every decreasingly ordered Hermitian eigenvalue,
proved locally from the spectral theorem and a dimension-count kernel
argument. -/
theorem orderedHermitianEigenvalue_mono_of_sub_posSemidef {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hBA : (B - A).PosSemidef) (k : Fin n) :
    orderedHermitianEigenvalue hA k ≤ orderedHermitianEigenvalue hB k := by
  by_contra! hcontra
  let F := orderedSpectralOverlap hA hB k
  have hdim : Module.finrank ℝ (Fin k.1 → ℝ) <
      Module.finrank ℝ (Fin (k.1 + 1) → ℝ) := by
    simp only [Module.finrank_fin_fun]
    omega
  have hker : LinearMap.ker F ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hcF, hcne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let padded : Fin n → ℝ := finPrefixPad c
  let v : Fin n → ℝ :=
    orderedHermitianEigenvectorMatrix hA *ᵥ padded
  have hpadded_ne : padded ≠ 0 := by
    intro hpadded
    apply hcne
    apply finPrefixPad_injective (by omega : k.1 + 1 ≤ n)
    simpa only [map_zero] using hpadded
  have hvne : v ≠ 0 := by
    intro hv
    apply hpadded_ne
    apply orderedHermitianEigenvectorMatrix_mulVec_injective hA
    simpa only [Matrix.mulVec_zero] using hv
  have hcoordA : hermitianCoordinates hA v = padded := by
    exact hermitianCoordinates_orderedEigenvectorMatrix_mulVec hA padded
  have hAhead : ∀ i : Fin n, k < i →
      hermitianCoordinates hA v i = 0 := by
    intro i hki
    rw [hcoordA]
    simp [padded, finPrefixPad]
    omega
  have hcFzero : F c = 0 := LinearMap.mem_ker.mp hcF
  have hBtail : ∀ i : Fin n, i < k →
      hermitianCoordinates hB v i = 0 := by
    intro i hik
    have hi : i.1 < k.1 := hik
    have hcomponent := congrFun hcFzero ⟨i.1, hi⟩
    change ((orderedHermitianEigenvectorMatrix hB)ᵀ *ᵥ v) i = 0
    rw [mulVec_transpose]
    simpa [F, orderedSpectralOverlap, v, padded, hermitianCoordinates,
      finPrefixTake, Matrix.mulVecLin_apply, LinearMap.comp_apply] using hcomponent
  have hAquad := orderedEigenvalue_mul_dotProduct_le_dotProduct_mulVec
    hA k v hAhead
  have hBquad := dotProduct_mulVec_le_orderedEigenvalue_mul_dotProduct
    hB k v hBtail
  have hABquad := dotProduct_mulVec_le_of_sub_posSemidef hBA v
  have hnorm : 0 < v ⬝ᵥ v := dotProduct_self_pos hvne
  nlinarith

/-- Kernel map for the rank-shift comparison.  Its first component forces
the synthesized vector into the spectral tail of `A`; its second component
forces it into the kernel of the perturbation `R`. -/
def orderedRankShiftOverlap {n r : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (R : Matrix (Fin n) (Fin n) ℝ)
    (k : Fin n) :
    (Fin (k.1 + r + 1) → ℝ) →ₗ[ℝ]
      (Fin k.1 → ℝ) × LinearMap.range R.mulVecLin :=
  LinearMap.prod
    ((finPrefixTake (Nat.le_of_lt k.2)).comp <|
        (orderedHermitianEigenvectorMatrix hA)ᵀ.mulVecLin.comp <|
        (orderedHermitianEigenvectorMatrix hB).mulVecLin.comp <|
          finPrefixPad)
    (R.mulVecLin.rangeRestrict.comp <|
      (orderedHermitianEigenvectorMatrix hB).mulVecLin.comp <|
        finPrefixPad)

/-- Rank-`r` ordered-eigenvalue shift inequality.  If `B-A` has rank at
most `r`, then `λₖ(A) ≥ λₖ₊ᵣ(B)` whenever the shifted index exists.
This is the lower half of the paper's rank-two interlacing. -/
theorem orderedHermitianEigenvalue_rank_shift {n r : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R = B - A)
    (hrank : R.rank ≤ r) (k : Fin n) (hkr : k.1 + r < n) :
    orderedHermitianEigenvalue hB ⟨k.1 + r, hkr⟩ ≤
      orderedHermitianEigenvalue hA k := by
  by_contra! hcontra
  let F := orderedRankShiftOverlap (r := r) hA hB R k
  have hdim :
      Module.finrank ℝ
          ((Fin k.1 → ℝ) × LinearMap.range R.mulVecLin) <
        Module.finrank ℝ (Fin (k.1 + r + 1) → ℝ) := by
    simp only [Module.finrank_prod, Module.finrank_fin_fun]
    change k.1 + R.rank < k.1 + r + 1
    omega
  have hker : LinearMap.ker F ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hcF, hcne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let padded : Fin n → ℝ :=
    finPrefixPad c
  let v : Fin n → ℝ :=
    orderedHermitianEigenvectorMatrix hB *ᵥ padded
  have hpadded_ne : padded ≠ 0 := by
    intro hpadded
    apply hcne
    apply finPrefixPad_injective (by omega : k.1 + r + 1 ≤ n)
    simpa only [map_zero] using hpadded
  have hvne : v ≠ 0 := by
    intro hv
    apply hpadded_ne
    apply orderedHermitianEigenvectorMatrix_mulVec_injective hB
    simpa only [Matrix.mulVec_zero] using hv
  have hcoordB : hermitianCoordinates hB v = padded :=
    hermitianCoordinates_orderedEigenvectorMatrix_mulVec hB padded
  have hBhead : ∀ i : Fin n, (⟨k.1 + r, hkr⟩ : Fin n) < i →
      hermitianCoordinates hB v i = 0 := by
    intro i hi
    have hnot : ¬ i.1 < k.1 + r + 1 := by
      change k.1 + r < i.1 at hi
      omega
    rw [hcoordB]
    change (if h : i.1 < k.1 + r + 1 then c ⟨i.1, h⟩ else 0) = 0
    exact dif_neg hnot
  have hcFzero : F c = 0 := LinearMap.mem_ker.mp hcF
  have hAtail : ∀ i : Fin n, i < k →
      hermitianCoordinates hA v i = 0 := by
    intro i hik
    have hi : i.1 < k.1 := hik
    have hcomponent := congrArg (fun z ↦ z.1 ⟨i.1, hi⟩) hcFzero
    change ((orderedHermitianEigenvectorMatrix hA)ᵀ *ᵥ v) i = 0
    rw [mulVec_transpose]
    simpa [F, orderedRankShiftOverlap, v, padded, finPrefixTake,
      Matrix.mulVecLin_apply, LinearMap.comp_apply] using hcomponent
  have hsnd := congrArg Prod.snd hcFzero
  have hsndVal := congrArg
    (fun z : LinearMap.range R.mulVecLin ↦ (z : Fin n → ℝ)) hsnd
  have hRv : R *ᵥ v = 0 := by
    simpa [F, orderedRankShiftOverlap, v, padded,
      Matrix.mulVecLin_apply, LinearMap.comp_apply] using hsndVal
  have hABv : A *ᵥ v = B *ᵥ v := by
    rw [hR, Matrix.sub_mulVec] at hRv
    exact (sub_eq_zero.mp hRv).symm
  have hAquad := dotProduct_mulVec_le_orderedEigenvalue_mul_dotProduct
    hA k v hAtail
  have hBquad := orderedEigenvalue_mul_dotProduct_le_dotProduct_mulVec
    hB ⟨k.1 + r, hkr⟩ v hBhead
  have hquadEq : v ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (B *ᵥ v) := by rw [hABv]
  have hnorm : 0 < v ⬝ᵥ v := dotProduct_self_pos hvne
  nlinarith

/-- Positive-semidefinite rank-`r` interlacing in the exact decreasing
index convention used by the paper. -/
theorem orderedHermitianEigenvalue_psd_rank_interlace {n r : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hBA : (B - A).PosSemidef) (hrank : (B - A).rank ≤ r)
    (k : Fin n) (hkr : k.1 + r < n) :
    orderedHermitianEigenvalue hB k ≥
        orderedHermitianEigenvalue hA k ∧
      orderedHermitianEigenvalue hA k ≥
        orderedHermitianEigenvalue hB ⟨k.1 + r, hkr⟩ := by
  exact ⟨orderedHermitianEigenvalue_mono_of_sub_posSemidef
      hA hB hBA k,
    orderedHermitianEigenvalue_rank_shift hA hB (B - A) rfl hrank k hkr⟩

/-- The leading principal `n×n` block of an `(n+1)×(n+1)` matrix. -/
def leadingPrincipalMatrix {n : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ B i.castSucc j.castSucc

/-- A leading principal block of a Hermitian matrix is Hermitian. -/
theorem leadingPrincipalMatrix_isHermitian {n : ℕ}
    {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hB : B.IsHermitian) : (leadingPrincipalMatrix B).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simpa [leadingPrincipalMatrix, Matrix.conjTranspose_apply] using
    hB.apply i.castSucc j.castSucc

@[simp] theorem finPrefixPad_succ_castSucc {n : ℕ} (w : Fin n → ℝ)
    (i : Fin n) :
    finPrefixPad w i.castSucc = w i := by
  simp [finPrefixPad, i.2]

@[simp] theorem finPrefixPad_succ_last {n : ℕ} (w : Fin n → ℝ) :
    finPrefixPad w (Fin.last n) = 0 := by
  simp [finPrefixPad]

/-- Compression of multiplication by a matrix to the first `n`
coordinates is multiplication by its leading principal block. -/
theorem finPrefixTake_mulVec_finPrefixPad {n : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (w : Fin n → ℝ) :
    finPrefixTake (Nat.le_succ n)
        (B *ᵥ finPrefixPad w) =
      leadingPrincipalMatrix B *ᵥ w := by
  funext i
  change (B *ᵥ finPrefixPad w) i.castSucc =
    (leadingPrincipalMatrix B *ᵥ w) i
  simp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_castSucc]
  simp [leadingPrincipalMatrix]

/-- Zero padding preserves the real Euclidean squared length. -/
theorem dotProduct_finPrefixPad_succ_self {n : ℕ} (w : Fin n → ℝ) :
    finPrefixPad (n := n + 1) w ⬝ᵥ finPrefixPad (n := n + 1) w =
      w ⬝ᵥ w := by
  unfold dotProduct
  rw [Fin.sum_univ_castSucc]
  simp

/-- Exact quadratic-form compression identity for a leading principal
block. -/
theorem dotProduct_mulVec_finPrefixPad_eq_leadingPrincipal {n : ℕ}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (w : Fin n → ℝ) :
    finPrefixPad (n := n + 1) w ⬝ᵥ
        (B *ᵥ finPrefixPad (n := n + 1) w) =
      w ⬝ᵥ (leadingPrincipalMatrix B *ᵥ w) := by
  have hmul := finPrefixTake_mulVec_finPrefixPad B w
  unfold dotProduct
  rw [Fin.sum_univ_castSucc]
  simp only [finPrefixPad_succ_castSucc, finPrefixPad_succ_last,
    zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun z ↦ w i * z) (congrFun hmul i)

/-- Kernel map for the upper half of leading-principal Cauchy
interlacing. -/
def leadingCauchyUpperOverlap {n : ℕ}
    {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hB : B.IsHermitian) (k : Fin n) :
    (Fin (k.1 + 1) → ℝ) →ₗ[ℝ] (Fin k.1 → ℝ) :=
  let hC := leadingPrincipalMatrix_isHermitian hB
  (finPrefixTake (by omega : k.1 ≤ n + 1)).comp <|
    (orderedHermitianEigenvectorMatrix hB)ᵀ.mulVecLin.comp <|
      finPrefixPad.comp <|
        (orderedHermitianEigenvectorMatrix hC).mulVecLin.comp <|
          finPrefixPad

/-- The `k`-th eigenvalue of a leading principal block is at most the
`k`-th eigenvalue of the full matrix. -/
theorem leadingPrincipal_orderedEigenvalue_le {n : ℕ}
    {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hB : B.IsHermitian) (k : Fin n) :
    orderedHermitianEigenvalue (leadingPrincipalMatrix_isHermitian hB) k ≤
      orderedHermitianEigenvalue hB k.castSucc := by
  let C := leadingPrincipalMatrix B
  let hC : C.IsHermitian := leadingPrincipalMatrix_isHermitian hB
  by_contra! hcontra
  let F := leadingCauchyUpperOverlap hB k
  have hdim : Module.finrank ℝ (Fin k.1 → ℝ) <
      Module.finrank ℝ (Fin (k.1 + 1) → ℝ) := by
    simp only [Module.finrank_fin_fun]
    omega
  have hker : LinearMap.ker F ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hcF, hcne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let smallPad : Fin n → ℝ :=
    finPrefixPad c
  let w : Fin n → ℝ := orderedHermitianEigenvectorMatrix hC *ᵥ smallPad
  let v : Fin (n + 1) → ℝ := finPrefixPad w
  have hsmallPad_ne : smallPad ≠ 0 := by
    intro hz
    apply hcne
    apply finPrefixPad_injective (by omega : k.1 + 1 ≤ n)
    simpa only [map_zero] using hz
  have hwne : w ≠ 0 := by
    intro hz
    apply hsmallPad_ne
    apply orderedHermitianEigenvectorMatrix_mulVec_injective hC
    simpa only [Matrix.mulVec_zero] using hz
  have hvne : v ≠ 0 := by
    intro hz
    apply hwne
    apply finPrefixPad_injective (Nat.le_succ n)
    simpa only [map_zero] using hz
  have hcoordC : hermitianCoordinates hC w = smallPad :=
    hermitianCoordinates_orderedEigenvectorMatrix_mulVec hC smallPad
  have hChead : ∀ i : Fin n, k < i → hermitianCoordinates hC w i = 0 := by
    intro i hki
    have hnot : ¬ i.1 < k.1 + 1 := by
      change k.1 < i.1 at hki
      omega
    rw [hcoordC]
    change (if h : i.1 < k.1 + 1 then c ⟨i.1, h⟩ else 0) = 0
    exact dif_neg hnot
  have hcFzero : F c = 0 := LinearMap.mem_ker.mp hcF
  have hBtail : ∀ i : Fin (n + 1), i < k.castSucc →
      hermitianCoordinates hB v i = 0 := by
    intro i hik
    have hi : i.1 < k.1 := hik
    have hcomponent := congrFun hcFzero ⟨i.1, hi⟩
    change ((orderedHermitianEigenvectorMatrix hB)ᵀ *ᵥ v) i = 0
    rw [mulVec_transpose]
    simpa [F, leadingCauchyUpperOverlap, v, w, smallPad,
      finPrefixTake, Matrix.mulVecLin_apply, LinearMap.comp_apply] using hcomponent
  have hCquad := orderedEigenvalue_mul_dotProduct_le_dotProduct_mulVec
    hC k w hChead
  have hBquad := dotProduct_mulVec_le_orderedEigenvalue_mul_dotProduct
    hB k.castSucc v hBtail
  have hquad := dotProduct_mulVec_finPrefixPad_eq_leadingPrincipal B w
  have hnormEq := dotProduct_finPrefixPad_succ_self w
  have hnorm : 0 < w ⬝ᵥ w := dotProduct_self_pos hwne
  have hcontra' : orderedHermitianEigenvalue hB k.castSucc <
      orderedHermitianEigenvalue hC k := by
    simpa only [hC] using hcontra
  dsimp only [C] at hCquad hquad
  have hquad' : v ⬝ᵥ (B *ᵥ v) =
      w ⬝ᵥ (leadingPrincipalMatrix B *ᵥ w) := by
    simpa only [v] using hquad
  have hnormEq' : v ⬝ᵥ v = w ⬝ᵥ w := by
    simpa only [v] using hnormEq
  rw [hquad', hnormEq'] at hBquad
  nlinarith

/-- The last coordinate as a linear functional. -/
def finLastCoordinate (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun v := v (Fin.last n)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Kernel map for the lower half of leading-principal Cauchy
interlacing. -/
def leadingCauchyLowerOverlap {n : ℕ}
    {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hB : B.IsHermitian) (k : Fin n) :
    (Fin (k.1 + 2) → ℝ) →ₗ[ℝ] (Fin k.1 → ℝ) × ℝ :=
  let hC := leadingPrincipalMatrix_isHermitian hB
  let synth := (orderedHermitianEigenvectorMatrix hB).mulVecLin.comp
    finPrefixPad
  LinearMap.prod
    ((finPrefixTake (Nat.le_of_lt k.2)).comp <|
      (orderedHermitianEigenvectorMatrix hC)ᵀ.mulVecLin.comp <|
        (finPrefixTake (Nat.le_succ n)).comp synth)
    ((finLastCoordinate n).comp synth)

/-- The shifted full-matrix eigenvalue is at most the corresponding
leading-principal eigenvalue. -/
theorem orderedEigenvalue_succ_le_leadingPrincipal {n : ℕ}
    {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hB : B.IsHermitian) (k : Fin n) :
    orderedHermitianEigenvalue hB ⟨k.1 + 1, by omega⟩ ≤
      orderedHermitianEigenvalue (leadingPrincipalMatrix_isHermitian hB) k := by
  let C := leadingPrincipalMatrix B
  let hC : C.IsHermitian := leadingPrincipalMatrix_isHermitian hB
  by_contra! hcontra
  let F := leadingCauchyLowerOverlap hB k
  have hdim : Module.finrank ℝ ((Fin k.1 → ℝ) × ℝ) <
      Module.finrank ℝ (Fin (k.1 + 2) → ℝ) := by
    simp only [Module.finrank_prod, Module.finrank_fin_fun,
      Module.finrank_self]
    omega
  have hker : LinearMap.ker F ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hcF, hcne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let padded : Fin (n + 1) → ℝ :=
    finPrefixPad c
  let v : Fin (n + 1) → ℝ :=
    orderedHermitianEigenvectorMatrix hB *ᵥ padded
  let w : Fin n → ℝ := finPrefixTake (Nat.le_succ n) v
  have hpadded_ne : padded ≠ 0 := by
    intro hz
    apply hcne
    apply finPrefixPad_injective (by omega : k.1 + 2 ≤ n + 1)
    simpa only [map_zero] using hz
  have hvne : v ≠ 0 := by
    intro hz
    apply hpadded_ne
    apply orderedHermitianEigenvectorMatrix_mulVec_injective hB
    simpa only [Matrix.mulVec_zero] using hz
  have hcFzero : F c = 0 := LinearMap.mem_ker.mp hcF
  have hlast : v (Fin.last n) = 0 := by
    have hsnd := congrArg Prod.snd hcFzero
    simpa [F, leadingCauchyLowerOverlap, v, padded, finLastCoordinate,
      Matrix.mulVecLin_apply, LinearMap.comp_apply] using hsnd
  have hpadw : finPrefixPad w = v := by
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · rw [finPrefixPad_succ_castSucc]
      change v ⟨j.1, by omega⟩ = v j.castSucc
      congr
    · simp [hlast]
  have hwne : w ≠ 0 := by
    intro hw
    apply hvne
    rw [← hpadw, hw, map_zero]
  have hcoordB : hermitianCoordinates hB v = padded :=
    hermitianCoordinates_orderedEigenvectorMatrix_mulVec hB padded
  have hBhead : ∀ i : Fin (n + 1),
      (⟨k.1 + 1, by omega⟩ : Fin (n + 1)) < i →
        hermitianCoordinates hB v i = 0 := by
    intro i hi
    have hnot : ¬ i.1 < k.1 + 2 := by
      change k.1 + 1 < i.1 at hi
      omega
    rw [hcoordB]
    change (if h : i.1 < k.1 + 2 then c ⟨i.1, h⟩ else 0) = 0
    exact dif_neg hnot
  have hCtail : ∀ i : Fin n, i < k →
      hermitianCoordinates hC w i = 0 := by
    intro i hik
    have hi : i.1 < k.1 := hik
    have hfst := congrArg (fun z ↦ z.1 ⟨i.1, hi⟩) hcFzero
    change ((orderedHermitianEigenvectorMatrix hC)ᵀ *ᵥ w) i = 0
    rw [mulVec_transpose]
    simpa [F, leadingCauchyLowerOverlap, v, w, padded, finPrefixTake,
      Matrix.mulVecLin_apply, LinearMap.comp_apply] using hfst
  have hBquad := orderedEigenvalue_mul_dotProduct_le_dotProduct_mulVec
    hB ⟨k.1 + 1, by omega⟩ v hBhead
  have hCquad := dotProduct_mulVec_le_orderedEigenvalue_mul_dotProduct
    hC k w hCtail
  have hquad := dotProduct_mulVec_finPrefixPad_eq_leadingPrincipal B w
  have hnormEq := dotProduct_finPrefixPad_succ_self w
  have hnorm : 0 < w ⬝ᵥ w := dotProduct_self_pos hwne
  have hcontra' : orderedHermitianEigenvalue hC k <
      orderedHermitianEigenvalue hB ⟨k.1 + 1, by omega⟩ := by
    simpa only [hC] using hcontra
  rw [hpadw] at hquad hnormEq
  dsimp only [C] at hCquad hquad
  rw [hquad, hnormEq] at hBquad
  nlinarith

/-- Cauchy interlacing for a leading principal real Hermitian block, with
all indices and weak inequalities explicit. -/
theorem leadingPrincipal_cauchy_interlace {n : ℕ}
    {B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hB : B.IsHermitian) (k : Fin n) :
    orderedHermitianEigenvalue hB k.castSucc ≥
        orderedHermitianEigenvalue (leadingPrincipalMatrix_isHermitian hB) k ∧
      orderedHermitianEigenvalue (leadingPrincipalMatrix_isHermitian hB) k ≥
        orderedHermitianEigenvalue hB ⟨k.1 + 1, by omega⟩ := by
  exact ⟨leadingPrincipal_orderedEigenvalue_le hB k,
    orderedEigenvalue_succ_le_leadingPrincipal hB k⟩

/-- Odd-dimensional/even-gap Cauchy selection.  If the two central
eigenvalues of the leading block are `s,-s`, then a positive central
eigenvalue of the full matrix has minimum modulus. -/
theorem oddCentral_abs_min_of_positive_leadingPrincipal
    (m : ℕ) (hm : 0 < m)
    {B : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ}
    (hB : B.IsHermitian) (s : ℝ)
    (hCpos : orderedHermitianEigenvalue
        (leadingPrincipalMatrix_isHermitian hB) ⟨m - 1, by omega⟩ = s)
    (hCneg : orderedHermitianEigenvalue
        (leadingPrincipalMatrix_isHermitian hB) ⟨m, by omega⟩ = -s)
    (hselected : 0 < orderedHermitianEigenvalue hB ⟨m, by omega⟩) :
    0 < orderedHermitianEigenvalue hB ⟨m, by omega⟩ ∧
      ∀ i : Fin (2 * m + 1),
        |orderedHermitianEigenvalue hB ⟨m, by omega⟩| ≤
          |orderedHermitianEigenvalue hB i| := by
  let p : Fin (2 * m) := ⟨m - 1, by omega⟩
  let q : Fin (2 * m) := ⟨m, by omega⟩
  let c : Fin (2 * m + 1) := ⟨m, by omega⟩
  let d : Fin (2 * m + 1) := ⟨m + 1, by omega⟩
  have hp := leadingPrincipal_cauchy_interlace hB p
  have hq := leadingPrincipal_cauchy_interlace hB q
  have hc_le_s : orderedHermitianEigenvalue hB c ≤ s := by
    have h := hp.2
    rw [hCpos] at h
    have hpc : (⟨p.1 + 1, by omega⟩ : Fin (2 * m + 1)) = c := by
      apply Fin.ext
      simp [p, c]
      omega
    rw [hpc] at h
    exact h
  have hs_le_neg_d : s ≤ -orderedHermitianEigenvalue hB d := by
    have h := hq.2
    rw [hCneg] at h
    have h' : -s ≥ orderedHermitianEigenvalue hB d := by
      simpa only [q, d] using h
    linarith
  have hs : 0 < s := hselected.trans_le hc_le_s
  have hdNeg : orderedHermitianEigenvalue hB d < 0 := by
    have hnegS : -s < 0 := neg_lt_zero.mpr hs
    have hd_le : orderedHermitianEigenvalue hB d ≤ -s := by
      linarith
    exact hd_le.trans_lt hnegS
  refine ⟨hselected, ?_⟩
  intro i
  by_cases hi : i.1 ≤ m
  · have hic : i ≤ c := by
      exact hi
    have hci : orderedHermitianEigenvalue hB c ≤
        orderedHermitianEigenvalue hB i :=
      (orderedHermitianEigenvalue_antitone hB) hic
    have hiPos : 0 < orderedHermitianEigenvalue hB i :=
      hselected.trans_le (by simpa only [c] using hci)
    rw [abs_of_pos hiPos, abs_of_pos hselected]
    simpa only [c] using hci
  · have hdi : d ≤ i := by
      change m + 1 ≤ i.1
      omega
    have hid : orderedHermitianEigenvalue hB i ≤
        orderedHermitianEigenvalue hB d :=
      (orderedHermitianEigenvalue_antitone hB) hdi
    have hiNeg : orderedHermitianEigenvalue hB i < 0 := hid.trans_lt hdNeg
    rw [abs_of_neg hiNeg, abs_of_pos hselected]
    have hchain : orderedHermitianEigenvalue hB c ≤
        -orderedHermitianEigenvalue hB i :=
      hc_le_s.trans (hs_le_neg_d.trans (neg_le_neg hid))
    simpa only [c] using hchain

/-- Odd-dimensional/odd-gap Cauchy selection.  Under the opposite central
inertia signs, the negative central eigenvalue has minimum modulus. -/
theorem oddCentral_abs_min_of_negative_leadingPrincipal
    (m : ℕ) (hm : 0 < m)
    {B : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ}
    (hB : B.IsHermitian) (s : ℝ)
    (hCpos : orderedHermitianEigenvalue
        (leadingPrincipalMatrix_isHermitian hB) ⟨m - 1, by omega⟩ = s)
    (hCneg : orderedHermitianEigenvalue
        (leadingPrincipalMatrix_isHermitian hB) ⟨m, by omega⟩ = -s)
    (hselected : orderedHermitianEigenvalue hB ⟨m, by omega⟩ < 0) :
    orderedHermitianEigenvalue hB ⟨m, by omega⟩ < 0 ∧
      ∀ i : Fin (2 * m + 1),
        |orderedHermitianEigenvalue hB ⟨m, by omega⟩| ≤
          |orderedHermitianEigenvalue hB i| := by
  let p : Fin (2 * m) := ⟨m - 1, by omega⟩
  let q : Fin (2 * m) := ⟨m, by omega⟩
  let prev : Fin (2 * m + 1) := ⟨m - 1, by omega⟩
  let c : Fin (2 * m + 1) := ⟨m, by omega⟩
  have hp := leadingPrincipal_cauchy_interlace hB p
  have hq := leadingPrincipal_cauchy_interlace hB q
  have hs_le_prev : s ≤ orderedHermitianEigenvalue hB prev := by
    have h := hp.1
    rw [hCpos] at h
    simpa only [p, prev] using h
  have hneg_c_le_s : -orderedHermitianEigenvalue hB c ≤ s := by
    have h := hq.1
    rw [hCneg] at h
    have h' : orderedHermitianEigenvalue hB c ≥ -s := by
      simpa only [q, c] using h
    linarith
  have hs : 0 < s := (neg_pos.mpr hselected).trans_le hneg_c_le_s
  have hprevPos : 0 < orderedHermitianEigenvalue hB prev :=
    hs.trans_le hs_le_prev
  refine ⟨hselected, ?_⟩
  intro i
  by_cases hi : i.1 < m
  · have hip : i ≤ prev := by
      change i.1 ≤ m - 1
      omega
    have hpi : orderedHermitianEigenvalue hB prev ≤
        orderedHermitianEigenvalue hB i :=
      (orderedHermitianEigenvalue_antitone hB) hip
    have hiPos : 0 < orderedHermitianEigenvalue hB i :=
      hprevPos.trans_le hpi
    rw [abs_of_pos hiPos, abs_of_neg hselected]
    have hchain : -orderedHermitianEigenvalue hB c ≤
        orderedHermitianEigenvalue hB i :=
      hneg_c_le_s.trans (hs_le_prev.trans hpi)
    simpa only [c] using hchain
  · have hci : c ≤ i := by
      change m ≤ i.1
      omega
    have hic : orderedHermitianEigenvalue hB i ≤
        orderedHermitianEigenvalue hB c :=
      (orderedHermitianEigenvalue_antitone hB) hci
    have hiNeg : orderedHermitianEigenvalue hB i < 0 :=
      hic.trans_lt hselected
    rw [abs_of_neg hiNeg, abs_of_neg hselected]
    simpa only [c] using neg_le_neg hic

/-- Abstract even-dimensional/even-gap selection step from
`lem:middle-branch`.  The reflected matrix is a positive-semidefinite
perturbation, so the last positive central eigenvalue is no farther from
zero than the first negative one.  Weak comparison is retained, covering
the multiple-least-singular-value case. -/
theorem evenCentral_abs_min_of_reflection_psd
    (m : ℕ) (hm : 0 < m)
    {A B : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hBA : (B - A).PosSemidef)
    (hreflect : ∀ i : Fin (2 * m),
      orderedHermitianEigenvalue hB i =
        -orderedHermitianEigenvalue hA i.rev)
    (hpos : 0 < orderedHermitianEigenvalue hA ⟨m - 1, by omega⟩)
    (hneg : orderedHermitianEigenvalue hA ⟨m, by omega⟩ < 0) :
    0 < orderedHermitianEigenvalue hA ⟨m - 1, by omega⟩ ∧
      ∀ i : Fin (2 * m),
        |orderedHermitianEigenvalue hA ⟨m - 1, by omega⟩| ≤
          |orderedHermitianEigenvalue hA i| := by
  let c : Fin (2 * m) := ⟨m - 1, by omega⟩
  let d : Fin (2 * m) := ⟨m, by omega⟩
  have hrev : c.rev = d := by
    apply Fin.ext
    simp [c, d]
    omega
  have hmiddle : orderedHermitianEigenvalue hA c ≤
      -orderedHermitianEigenvalue hA d := by
    calc
      orderedHermitianEigenvalue hA c ≤
          orderedHermitianEigenvalue hB c :=
        orderedHermitianEigenvalue_mono_of_sub_posSemidef hA hB hBA c
      _ = -orderedHermitianEigenvalue hA d := by rw [hreflect, hrev]
  refine ⟨by simpa only [c] using hpos, ?_⟩
  intro i
  by_cases hi : i.1 < m
  · have hic : i ≤ c := by
      change i.1 ≤ m - 1
      omega
    have hci : orderedHermitianEigenvalue hA c ≤
        orderedHermitianEigenvalue hA i :=
      (orderedHermitianEigenvalue_antitone hA) hic
    have hiPos : 0 < orderedHermitianEigenvalue hA i := hpos.trans_le hci
    rw [abs_of_pos hiPos]
    simpa only [c, abs_of_pos hpos] using hci
  · have hdi : d ≤ i := by
      change m ≤ i.1
      omega
    have hid : orderedHermitianEigenvalue hA i ≤
        orderedHermitianEigenvalue hA d :=
      (orderedHermitianEigenvalue_antitone hA) hdi
    have hiNeg : orderedHermitianEigenvalue hA i < 0 := hid.trans_lt hneg
    rw [abs_of_neg hiNeg]
    simpa only [c, d, abs_of_pos hpos] using hmiddle.trans (neg_le_neg hid)

/-- Abstract even-dimensional/odd-gap selection for `m≥2`.  This is the
place where the two-index rank shift is essential. -/
theorem evenCentral_abs_min_of_reflection_psd_rank_two
    (m : ℕ) (hm : 2 ≤ m)
    {A B : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hBA : (B - A).PosSemidef) (hrank : (B - A).rank ≤ 2)
    (hreflect : ∀ i : Fin (2 * m),
      orderedHermitianEigenvalue hB i =
        -orderedHermitianEigenvalue hA i.rev)
    (hpos : 0 < orderedHermitianEigenvalue hA ⟨m - 2, by omega⟩)
    (hneg : orderedHermitianEigenvalue hA ⟨m - 1, by omega⟩ < 0) :
    orderedHermitianEigenvalue hA ⟨m - 1, by omega⟩ < 0 ∧
      ∀ i : Fin (2 * m),
        |orderedHermitianEigenvalue hA ⟨m - 1, by omega⟩| ≤
          |orderedHermitianEigenvalue hA i| := by
  let p : Fin (2 * m) := ⟨m - 2, by omega⟩
  let c : Fin (2 * m) := ⟨m - 1, by omega⟩
  let s : Fin (2 * m) := ⟨m, by omega⟩
  have hshift : p.1 + 2 < 2 * m := by simp [p]; omega
  have hshiftIndex : (⟨p.1 + 2, hshift⟩ : Fin (2 * m)) = s := by
    apply Fin.ext
    simp [p, s]
    omega
  have hrev : s.rev = c := by
    apply Fin.ext
    simp [s, c]
    omega
  have hmiddle : -orderedHermitianEigenvalue hA c ≤
      orderedHermitianEigenvalue hA p := by
    have hrankPart := (orderedHermitianEigenvalue_psd_rank_interlace
      hA hB hBA hrank p hshift).2
    rw [hshiftIndex, hreflect, hrev] at hrankPart
    exact hrankPart
  refine ⟨by simpa only [c] using hneg, ?_⟩
  intro i
  by_cases hi : i.1 < m - 1
  · have hip : i ≤ p := by
      change i.1 ≤ m - 2
      omega
    have hpi : orderedHermitianEigenvalue hA p ≤
        orderedHermitianEigenvalue hA i :=
      (orderedHermitianEigenvalue_antitone hA) hip
    have hiPos : 0 < orderedHermitianEigenvalue hA i := hpos.trans_le hpi
    rw [abs_of_pos hiPos]
    simpa only [c, abs_of_neg hneg] using hmiddle.trans hpi
  · have hci : c ≤ i := by
      change m - 1 ≤ i.1
      omega
    have hic : orderedHermitianEigenvalue hA i ≤
        orderedHermitianEigenvalue hA c :=
      (orderedHermitianEigenvalue_antitone hA) hci
    have hiNeg : orderedHermitianEigenvalue hA i < 0 := hic.trans_lt hneg
    rw [abs_of_neg hiNeg]
    simpa only [c, abs_of_neg hneg] using neg_le_neg hic

/-- The exceptional `n=2` odd-gap case: if both ordered eigenvalues are
negative, the larger one has smaller modulus. -/
theorem twoByTwo_top_abs_min_of_negative
    {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.IsHermitian)
    (htop : orderedHermitianEigenvalue hA 0 < 0) :
    ∀ i : Fin 2,
      |orderedHermitianEigenvalue hA 0| ≤
        |orderedHermitianEigenvalue hA i| := by
  intro i
  have hi : orderedHermitianEigenvalue hA i ≤
      orderedHermitianEigenvalue hA 0 :=
    (orderedHermitianEigenvalue_antitone hA) (by omega)
  have hiNeg : orderedHermitianEigenvalue hA i < 0 := hi.trans_lt htop
  rw [abs_of_neg htop, abs_of_neg hiNeg]
  exact neg_le_neg hi

/-- Coordinate ordering `(1,…,m),(2m,…,m+1)` used in
`eq:even-dilation`. -/
def evenFoldEquiv (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  (Equiv.sumCongr (Equiv.refl (Fin m)) (@Fin.revPerm m)).trans <|
    (@finSumFinEquiv m m).trans (finCongr (by omega))

@[simp] theorem evenFoldEquiv_inl_val (m : ℕ) (i : Fin m) :
    (evenFoldEquiv m (Sum.inl i)).1 = i.1 := by
  simp [evenFoldEquiv]

@[simp] theorem evenFoldEquiv_inr_val (m : ℕ) (i : Fin m) :
    (evenFoldEquiv m (Sum.inr i)).1 = 2 * m - 1 - i.1 := by
  simp [evenFoldEquiv, Fin.val_rev]
  omega

theorem evenFoldEquiv_inl_rev_val (m : ℕ) (i : Fin m) :
    ((evenFoldEquiv m (Sum.inl i)).rev).1 = 2 * m - 1 - i.1 := by
  rw [Fin.val_rev, evenFoldEquiv_inl_val]
  omega

theorem evenFoldEquiv_inr_rev_val (m : ℕ) (i : Fin m) :
    ((evenFoldEquiv m (Sum.inr i)).rev).1 = i.1 := by
  rw [Fin.val_rev, evenFoldEquiv_inr_val]
  omega

/-- The real shifted path matrix `Pₙ(x)=xI-Aₙ`. -/
def realShiftedPathMatrix (n : ℕ) (a x : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  x • 1 - pathMatrix n a

/-- Projector onto the last coordinate, with the zero-dimensional case
handled without manufacturing a `Fin 0` element. -/
def lastCoordinateProjector (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j ↦ if i.1 + 1 = m ∧ j.1 + 1 = m then 1 else 0

/-- Off-diagonal dilation in `eq:even-dilation`. -/
def evenPathDilation (m : ℕ) (a x : ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  Matrix.fromBlocks 0 (realShiftedPathMatrix m a x)
    (realShiftedPathMatrix m a x)ᵀ 0

/-- The rank-two positive boundary correction in `eq:even-dilation`. -/
def evenBoundaryCorrection (m : ℕ) (a : ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  Matrix.fromBlocks (lastCoordinateProjector m) 0 0
    (a • lastCoordinateProjector m)

/-- Signed middle matrix after the paper's even folding permutation. -/
def evenFoldedSignedMiddleMatrix (m : ℕ) (a x : ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  (signedMiddleMatrix (2 * m) a x).submatrix
    (evenFoldEquiv m) (evenFoldEquiv m)

/-- Exact coordinate identity `eq:even-dilation`, including both boundary
diagonal corrections. -/
theorem evenFoldedSignedMiddleMatrix_eq_dilation_sub_boundary
    (m : ℕ) (hm : 0 < m) (a x : ℝ) :
    evenFoldedSignedMiddleMatrix m a x =
      evenPathDilation m a x - evenBoundaryCorrection m a := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · have hjrev := evenFoldEquiv_inl_rev_val m j
    simp only [evenFoldedSignedMiddleMatrix, Matrix.submatrix_apply,
      signedMiddleMatrix, mul_reversal_apply, evenFoldEquiv_inl_val,
      evenFoldEquiv_inl_rev_val, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      pathMatrix_apply, evenPathDilation, evenBoundaryCorrection,
      Matrix.sub_apply, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply,
      lastCoordinateProjector, Fin.ext_iff, smul_eq_mul]
    split_ifs <;> (first | omega | norm_num)
  · have hjrev := evenFoldEquiv_inr_rev_val m j
    simp only [evenFoldedSignedMiddleMatrix, Matrix.submatrix_apply,
      signedMiddleMatrix, mul_reversal_apply, evenFoldEquiv_inl_val,
      evenFoldEquiv_inr_rev_val, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, pathMatrix_apply,
      evenPathDilation, evenBoundaryCorrection, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply, sub_zero, realShiftedPathMatrix, Fin.ext_iff,
      smul_eq_mul]
  · have hjrev := evenFoldEquiv_inl_rev_val m j
    simp only [evenFoldedSignedMiddleMatrix, Matrix.submatrix_apply,
      signedMiddleMatrix, mul_reversal_apply,
      evenFoldEquiv_inr_val, evenFoldEquiv_inl_rev_val, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, pathMatrix_apply,
      evenPathDilation, evenBoundaryCorrection, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply, sub_zero, realShiftedPathMatrix,
      Matrix.transpose_apply, Fin.ext_iff, smul_eq_mul]
    split_ifs <;> (first | omega | norm_num)
  · have hjrev := evenFoldEquiv_inr_rev_val m j
    simp only [evenFoldedSignedMiddleMatrix, Matrix.submatrix_apply,
      signedMiddleMatrix, mul_reversal_apply, evenFoldEquiv_inr_val,
      evenFoldEquiv_inr_rev_val, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      pathMatrix_apply, evenPathDilation, evenBoundaryCorrection,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      lastCoordinateProjector, Fin.ext_iff, smul_eq_mul]
    split_ifs <;> (first | omega | norm_num)

/-- Diagonal weights of the even boundary correction. -/
def evenBoundaryWeight (m : ℕ) (a : ℝ) : Fin m ⊕ Fin m → ℝ
  | Sum.inl i => if i.1 + 1 = m then 1 else 0
  | Sum.inr i => if i.1 + 1 = m then a else 0

/-- The two boundary terms in `eq:even-dilation` form one diagonal
matrix in the folded coordinates. -/
theorem evenBoundaryCorrection_eq_diagonal (m : ℕ) (a : ℝ) :
    evenBoundaryCorrection m a = Matrix.diagonal (evenBoundaryWeight m a) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [evenBoundaryCorrection, Matrix.fromBlocks_apply₁₁,
      lastCoordinateProjector, evenBoundaryWeight, Matrix.diagonal_apply,
      Sum.inl.injEq]
    split_ifs <;> (first | omega | norm_num)
  · simp [evenBoundaryCorrection]
  · simp [evenBoundaryCorrection]
  · simp only [evenBoundaryCorrection, Matrix.fromBlocks_apply₂₂,
      Matrix.smul_apply, lastCoordinateProjector, evenBoundaryWeight,
      Matrix.diagonal_apply, Sum.inr.injEq, smul_eq_mul]
    split_ifs <;> (first | omega | norm_num)

/-- For `a ≥ 0`, the boundary correction is positive semidefinite. -/
theorem evenBoundaryCorrection_posSemidef (m : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    (evenBoundaryCorrection m a).PosSemidef := by
  rw [evenBoundaryCorrection_eq_diagonal]
  apply Matrix.PosSemidef.diagonal
  intro i
  rcases i with i | i
  · by_cases h : i.1 + 1 = m <;> simp [evenBoundaryWeight, h]
  · by_cases h : i.1 + 1 = m
    · simpa [evenBoundaryWeight, h] using ha
    · simp [evenBoundaryWeight, h]

/-- The boundary correction has rank at most two, uniformly including
the zero-dimensional and `a=0` degeneracies. -/
theorem evenBoundaryCorrection_rank_le_two (m : ℕ) (a : ℝ) :
    (evenBoundaryCorrection m a).rank ≤ 2 := by
  rw [evenBoundaryCorrection_eq_diagonal, Matrix.rank_diagonal]
  let side : {i // evenBoundaryWeight m a i ≠ 0} → Fin 2 := fun i =>
    match i.1 with
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  have hside : Function.Injective side := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
    apply Subtype.ext
    rcases p with p | p <;> rcases q with q | q
    · have hpLast : p.1 + 1 = m := by
        by_contra h
        apply hp
        simp [evenBoundaryWeight, h]
      have hqLast : q.1 + 1 = m := by
        by_contra h
        apply hq
        simp [evenBoundaryWeight, h]
      exact congrArg Sum.inl (Fin.ext (by omega))
    · simp [side] at hpq
    · simp [side] at hpq
    · have hpLast : p.1 + 1 = m := by
        by_contra h
        apply hp
        simp [evenBoundaryWeight, h]
      have hqLast : q.1 + 1 = m := by
        by_contra h
        apply hq
        simp [evenBoundaryWeight, h]
      exact congrArg Sum.inr (Fin.ext (by omega))
  simpa using Fintype.card_le_of_injective side hside

/-- In the nondegenerate range used by the paper (`m>0`, `a>0`), both
boundary entries are nonzero, so the correction has rank exactly two. -/
theorem evenBoundaryCorrection_rank_eq_two
    (m : ℕ) (hm : 0 < m) {a : ℝ} (ha : 0 < a) :
    (evenBoundaryCorrection m a).rank = 2 := by
  apply le_antisymm (evenBoundaryCorrection_rank_le_two m a)
  rw [evenBoundaryCorrection_eq_diagonal, Matrix.rank_diagonal]
  let last : Fin m := ⟨m - 1, by omega⟩
  have hlast : last.1 + 1 = m := by
    simp only [last]
    omega
  let left : {i // evenBoundaryWeight m a i ≠ 0} :=
    ⟨Sum.inl last, by simp [evenBoundaryWeight, hlast]⟩
  let right : {i // evenBoundaryWeight m a i ≠ 0} :=
    ⟨Sum.inr last, by simp [evenBoundaryWeight, hlast, ha.ne']⟩
  have hlr : left ≠ right := by
    intro h
    have := congrArg Subtype.val h
    simp [left, right] at this
  letI : Nontrivial {i // evenBoundaryWeight m a i ≠ 0} :=
    ⟨⟨left, right, hlr⟩⟩
  exact Fintype.one_lt_card

/-- The signature `Γ = diag(Iₘ,-Iₘ)` in the folded coordinates. -/
def evenSignatureWeight (m : ℕ) : Fin m ⊕ Fin m → ℝ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

/-- The diagonal signature matrix `Γ = diag(Iₘ,-Iₘ)` in the even folded
coordinates. -/
def evenSignature (m : ℕ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  Matrix.diagonal (evenSignatureWeight m)

/-- Signature conjugation negates the off-diagonal dilation. -/
theorem evenSignature_conjugate_dilation (m : ℕ) (a x : ℝ) :
    -(evenSignature m * evenPathDilation m a x * evenSignature m) =
      evenPathDilation m a x := by
  ext i j
  simp only [evenSignature, Matrix.neg_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [evenSignatureWeight, evenPathDilation]

/-- Signature conjugation fixes the block-diagonal boundary correction. -/
theorem evenSignature_conjugate_boundary (m : ℕ) (a : ℝ) :
    evenSignature m * evenBoundaryCorrection m a * evenSignature m =
      evenBoundaryCorrection m a := by
  ext i j
  simp only [evenSignature, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [evenSignatureWeight, evenBoundaryCorrection]

/-- The reflected even matrix `-Γ B Γ` from `eq:alpha-reflection`. -/
def evenReflectedFoldedSignedMiddleMatrix (m : ℕ) (a x : ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ :=
  -(evenSignature m * evenFoldedSignedMiddleMatrix m a x * evenSignature m)

/-- Exact reflected form `\widetilde B = \widehat P + R_bd`. -/
theorem evenReflectedFoldedSignedMiddleMatrix_eq_dilation_add_boundary
    (m : ℕ) (hm : 0 < m) (a x : ℝ) :
    evenReflectedFoldedSignedMiddleMatrix m a x =
      evenPathDilation m a x + evenBoundaryCorrection m a := by
  rw [evenReflectedFoldedSignedMiddleMatrix,
    evenFoldedSignedMiddleMatrix_eq_dilation_sub_boundary m hm]
  calc
    -(evenSignature m *
          (evenPathDilation m a x - evenBoundaryCorrection m a) *
          evenSignature m) =
        -(evenSignature m * evenPathDilation m a x * evenSignature m) +
          evenSignature m * evenBoundaryCorrection m a * evenSignature m := by
            noncomm_ring
    _ = evenPathDilation m a x + evenBoundaryCorrection m a := by
      rw [evenSignature_conjugate_dilation,
        evenSignature_conjugate_boundary]

/-- The reflection is precisely the original folded matrix plus twice the
positive boundary correction. -/
theorem evenReflectedFoldedSignedMiddleMatrix_sub_eq_two_smul_boundary
    (m : ℕ) (hm : 0 < m) (a x : ℝ) :
    evenReflectedFoldedSignedMiddleMatrix m a x -
        evenFoldedSignedMiddleMatrix m a x =
      (2 : ℝ) • evenBoundaryCorrection m a := by
  rw [evenReflectedFoldedSignedMiddleMatrix_eq_dilation_add_boundary m hm,
    evenFoldedSignedMiddleMatrix_eq_dilation_sub_boundary m hm]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- Consequently the reflected-minus-original perturbation is positive
semidefinite for the paper's range `a ≥ 0`. -/
theorem evenReflectedFoldedSignedMiddleMatrix_sub_posSemidef
    (m : ℕ) (hm : 0 < m) {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    (evenReflectedFoldedSignedMiddleMatrix m a x -
      evenFoldedSignedMiddleMatrix m a x).PosSemidef := by
  rw [evenReflectedFoldedSignedMiddleMatrix_sub_eq_two_smul_boundary m hm]
  exact (evenBoundaryCorrection_posSemidef m ha).smul (by norm_num)

/-- The same perturbation has rank at most two. -/
theorem evenReflectedFoldedSignedMiddleMatrix_sub_rank_le_two
    (m : ℕ) (hm : 0 < m) (a x : ℝ) :
    (evenReflectedFoldedSignedMiddleMatrix m a x -
      evenFoldedSignedMiddleMatrix m a x).rank ≤ 2 := by
  rw [evenReflectedFoldedSignedMiddleMatrix_sub_eq_two_smul_boundary m hm,
    Matrix.smul_eq_diagonal_mul]
  exact (Matrix.rank_mul_le_right _ _).trans
    (evenBoundaryCorrection_rank_le_two m a)

/-- Return the reflected folded matrix to the original `Fin (2m)`
coordinate order. -/
def evenReflectedSignedMiddleMatrix (m : ℕ) (a x : ℝ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  (evenReflectedFoldedSignedMiddleMatrix m a x).submatrix
    (evenFoldEquiv m).symm (evenFoldEquiv m).symm

/-- Folding and then unfolding by the inverse permutation recovers the
original signed middle matrix. -/
theorem evenFoldedSignedMiddleMatrix_unfold (m : ℕ) (a x : ℝ) :
    (evenFoldedSignedMiddleMatrix m a x).submatrix
        (evenFoldEquiv m).symm (evenFoldEquiv m).symm =
      signedMiddleMatrix (2 * m) a x := by
  ext i j
  simp [evenFoldedSignedMiddleMatrix]

/-- In original coordinates, reflected minus original is exactly the
inverse reindexing of the folded perturbation. -/
theorem evenReflectedSignedMiddleMatrix_sub_original
    (m : ℕ) (a x : ℝ) :
    evenReflectedSignedMiddleMatrix m a x - signedMiddleMatrix (2 * m) a x =
      (evenReflectedFoldedSignedMiddleMatrix m a x -
        evenFoldedSignedMiddleMatrix m a x).submatrix
          (evenFoldEquiv m).symm (evenFoldEquiv m).symm := by
  rw [← evenFoldedSignedMiddleMatrix_unfold]
  ext i j
  rfl

/-- The original-coordinate reflected perturbation is positive
semidefinite. -/
theorem evenReflectedSignedMiddleMatrix_sub_posSemidef
    (m : ℕ) (hm : 0 < m) {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    (evenReflectedSignedMiddleMatrix m a x -
      signedMiddleMatrix (2 * m) a x).PosSemidef := by
  rw [evenReflectedSignedMiddleMatrix_sub_original]
  exact (evenReflectedFoldedSignedMiddleMatrix_sub_posSemidef m hm ha x).submatrix
    (evenFoldEquiv m).symm

/-- The original-coordinate reflected perturbation retains rank at most
two. -/
theorem evenReflectedSignedMiddleMatrix_sub_rank_le_two
    (m : ℕ) (hm : 0 < m) (a x : ℝ) :
    (evenReflectedSignedMiddleMatrix m a x -
      signedMiddleMatrix (2 * m) a x).rank ≤ 2 := by
  rw [evenReflectedSignedMiddleMatrix_sub_original,
    Matrix.rank_submatrix]
  exact evenReflectedFoldedSignedMiddleMatrix_sub_rank_le_two m hm a x

/-- The reflected matrix is Hermitian in the original coordinates. -/
theorem evenReflectedSignedMiddleMatrix_isHermitian
    (m : ℕ) (hm : 0 < m) {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    (evenReflectedSignedMiddleMatrix m a x).IsHermitian := by
  have hdiff := evenReflectedSignedMiddleMatrix_sub_posSemidef m hm ha x
  have horig : (signedMiddleMatrix (2 * m) a x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm (2 * m) a x)
  have heq : evenReflectedSignedMiddleMatrix m a x =
      (evenReflectedSignedMiddleMatrix m a x -
        signedMiddleMatrix (2 * m) a x) +
        signedMiddleMatrix (2 * m) a x := by
    abel
  rw [heq]
  exact hdiff.isHermitian.add horig

/-- The even signature in the original coordinate order. -/
def evenSignatureFin (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  (evenSignature m).submatrix (evenFoldEquiv m).symm (evenFoldEquiv m).symm

/-- The signature is an involution. -/
theorem evenSignature_mul_self (m : ℕ) :
    evenSignature m * evenSignature m = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [evenSignature, evenSignatureWeight,
    Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> norm_num

/-- Reindexing preserves the signature involution. -/
theorem evenSignatureFin_mul_self (m : ℕ) :
    evenSignatureFin m * evenSignatureFin m = 1 := by
  rw [evenSignatureFin, Matrix.submatrix_mul_equiv,
    evenSignature_mul_self]
  exact Matrix.submatrix_one_equiv (evenFoldEquiv m).symm

/-- In original coordinates the reflected matrix is still `-ΓBΓ`. -/
theorem evenReflectedSignedMiddleMatrix_eq_signature_conjugate
    (m : ℕ) (a x : ℝ) :
    evenReflectedSignedMiddleMatrix m a x =
      -(evenSignatureFin m * signedMiddleMatrix (2 * m) a x *
        evenSignatureFin m) := by
  rw [evenReflectedSignedMiddleMatrix, evenReflectedFoldedSignedMiddleMatrix,
    evenSignatureFin, Matrix.submatrix_neg,
    ← evenFoldedSignedMiddleMatrix_unfold]
  congr 1
  symm
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

/-- Kernel-checked similarity part of `eq:alpha-reflection`: the reflected
matrix has the same characteristic polynomial as the negative original
matrix. -/
theorem evenReflectedSignedMiddleMatrix_charpoly
    (m : ℕ) (a x : ℝ) :
    (evenReflectedSignedMiddleMatrix m a x).charpoly =
      (-signedMiddleMatrix (2 * m) a x).charpoly := by
  rw [evenReflectedSignedMiddleMatrix_eq_signature_conjugate]
  have hrewrite :
      -(evenSignatureFin m * signedMiddleMatrix (2 * m) a x *
          evenSignatureFin m) =
        (evenSignatureFin m * (-signedMiddleMatrix (2 * m) a x)) *
          evenSignatureFin m := by
    noncomm_ring
  rw [hrewrite, Matrix.charpoly_mul_comm]
  have hassoc :
      evenSignatureFin m *
          (evenSignatureFin m * (-signedMiddleMatrix (2 * m) a x)) =
        (evenSignatureFin m * evenSignatureFin m) *
          (-signedMiddleMatrix (2 * m) a x) := by
    noncomm_ring
  rw [hassoc, evenSignatureFin_mul_self, Matrix.one_mul]

/-- The exact rank-two interlacing inequalities `eq:rank-two-interlace`
for the signed middle matrix and its reflected partner. -/
theorem evenSignedMiddleMatrix_rank_two_interlace
    (m : ℕ) (hm : 0 < m) {a : ℝ} (ha : 0 ≤ a) (x : ℝ)
    (k : Fin (2 * m)) (hk : k.1 + 2 < 2 * m) :
    let hA : (signedMiddleMatrix (2 * m) a x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m) a x)
    let hB : (evenReflectedSignedMiddleMatrix m a x).IsHermitian :=
      evenReflectedSignedMiddleMatrix_isHermitian m hm ha x
    orderedHermitianEigenvalue hB k ≥ orderedHermitianEigenvalue hA k ∧
      orderedHermitianEigenvalue hA k ≥
        orderedHermitianEigenvalue hB ⟨k.1 + 2, hk⟩ := by
  dsimp only
  exact orderedHermitianEigenvalue_psd_rank_interlace
    (Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm (2 * m) a x))
    (evenReflectedSignedMiddleMatrix_isHermitian m hm ha x)
    (evenReflectedSignedMiddleMatrix_sub_posSemidef m hm ha x)
    (evenReflectedSignedMiddleMatrix_sub_rank_le_two m hm a x) k hk

/-- Spectral decomposition in the project's genuinely decreasing ordered
real Hermitian eigenbasis. -/
theorem orderedHermitian_spectral_decomposition {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    A = orderedHermitianEigenvectorMatrix hA *
        Matrix.diagonal (orderedHermitianEigenvalue hA) *
        (orderedHermitianEigenvectorMatrix hA)ᵀ := by
  let U := orderedHermitianEigenvectorMatrix hA
  let D := Matrix.diagonal (orderedHermitianEigenvalue hA)
  have hAU : A * U = U * D := by
    ext p i
    change (A *ᵥ (orderedHermitianEigenvectorMatrix hA).col i) p = _
    rw [orderedHermitianEigenvectorMatrix_col,
      mulVec_orderedHermitianEigenbasis]
    simp [D, U, smul_eq_mul, mul_comm]
  have hUUt : U * Uᵀ = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    exact (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp
      (orderedHermitianEigenvectorMatrix_mem_orthogonal hA)
  calc
    A = A * (U * Uᵀ) := by rw [hUUt, Matrix.mul_one]
    _ = (A * U) * Uᵀ := by noncomm_ring
    _ = U * D * Uᵀ := by rw [hAU]

/-- Negating a Hermitian matrix gives the diagonal ordered spectrum with
all signs reversed (before the final order reversal). -/
theorem neg_charpoly_eq_ordered_diagonal {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (-A).charpoly =
      (Matrix.diagonal fun i : Fin n =>
        -orderedHermitianEigenvalue hA i).charpoly := by
  let U := orderedHermitianEigenvectorMatrix hA
  let D := Matrix.diagonal fun i : Fin n =>
    -orderedHermitianEigenvalue hA i
  have hspec := orderedHermitian_spectral_decomposition hA
  have hUtU : Uᵀ * U = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    exact (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp
      (orderedHermitianEigenvectorMatrix_mem_orthogonal hA)
  have hnegSpec : -A = U * D * Uᵀ := by
    calc
      -A = -(U * Matrix.diagonal (orderedHermitianEigenvalue hA) * Uᵀ) :=
        congrArg Neg.neg hspec
      _ = U * (-Matrix.diagonal (orderedHermitianEigenvalue hA)) * Uᵀ := by
        noncomm_ring
      _ = U * D * Uᵀ := by
        simp [D, Matrix.diagonal_neg]
  rw [hnegSpec]
  calc
    (U * D * Uᵀ).charpoly = (Uᵀ * (U * D)).charpoly :=
      Matrix.charpoly_mul_comm _ _
    _ = ((Uᵀ * U) * D).charpoly := by
      congr 1
      noncomm_ring
    _ = D.charpoly := by rw [hUtU, Matrix.one_mul]

/-- Multiplicity-sensitive order reversal under matrix negation.  This is
proved by sorting the full root multiset, so repeated eigenvalues are
handled without a simplicity assumption. -/
theorem orderedHermitianEigenvalue_neg {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∀ i : Fin n,
      orderedHermitianEigenvalue hA.neg i =
        -orderedHermitianEigenvalue hA i.rev := by
  let g : Fin n → ℝ := fun i => -orderedHermitianEigenvalue hA i
  let f : Fin n → ℝ := fun i => -orderedHermitianEigenvalue hA i.rev
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal g
  have hchar : (-A).charpoly = D.charpoly :=
    neg_charpoly_eq_ordered_diagonal hA
  have hrootsD : D.charpoly.roots = Multiset.map g Finset.univ.val := by
    change (Matrix.diagonal g).charpoly.roots =
      Multiset.map g Finset.univ.val
    rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hperm : List.Perm (List.ofFn f) (List.ofFn g) := by
    simpa [f, g, Function.comp_def] using
      (Equiv.Perm.ofFn_comp_perm (@Fin.revPerm n) g)
  have hroots : ((-A).charpoly.roots.map RCLike.re) =
      (List.ofFn f : Multiset ℝ) := by
    calc
      ((-A).charpoly.roots.map RCLike.re) =
          (List.ofFn g : Multiset ℝ) := by
        rw [hchar, hrootsD]
        simp only [Fin.univ_val_map, RCLike.re_to_real, Multiset.map_coe,
          List.map_ofFn, Multiset.coe_eq_coe]
        simpa only [Function.id_comp] using
          (List.Perm.refl (List.ofFn g))
      _ = (List.ofFn f : Multiset ℝ) :=
        (Multiset.coe_eq_coe.mpr hperm).symm
  have hsort := hA.neg.sort_roots_charpoly_eq_eigenvalues₀
  rw [hroots, Multiset.coe_sort] at hsort
  have hf : Antitone f := by
    intro i j hij
    dsimp only [f]
    exact neg_le_neg ((orderedHermitianEigenvalue_antitone hA)
      ((Fin.rev_le_rev).2 hij))
  have hpair : (List.ofFn f).Pairwise
      (fun a b => decide (a ≥ b) = true) := by
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hf.sortedGE_ofFn
  rw [List.mergeSort_of_pairwise hpair] at hsort
  have heig0 : hA.neg.eigenvalues₀ = fun q =>
      f (finCongr (Fintype.card_fin n) q) := by
    apply List.ofFn_inj.mp
    simpa only [Fintype.card_fin] using hsort.symm
  intro i
  unfold orderedHermitianEigenvalue
  rw [heig0]
  simp only [Equiv.apply_symm_apply]
  rfl

/-- The decreasing ordered Hermitian spectrum is determined by the
characteristic polynomial, including all multiplicities. -/
theorem orderedHermitianEigenvalue_eq_of_charpoly_eq {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hchar : A.charpoly = B.charpoly) :
    ∀ i : Fin n,
      orderedHermitianEigenvalue hA i = orderedHermitianEigenvalue hB i := by
  have hsortA := hA.sort_roots_charpoly_eq_eigenvalues₀
  have hsortB := hB.sort_roots_charpoly_eq_eigenvalues₀
  rw [hchar] at hsortA
  have heig0 : hA.eigenvalues₀ = hB.eigenvalues₀ := by
    apply List.ofFn_inj.mp
    exact hsortA.symm.trans hsortB
  intro i
  unfold orderedHermitianEigenvalue
  rw [heig0]

/-- Exact ordered reflection identity `eq:alpha-reflection`, now with the
index reversal and multiplicities certified rather than inferred from an
unordered determinant-root statement. -/
theorem evenReflectedSignedMiddleMatrix_ordered_reflection
    (m : ℕ) (hm : 0 < m) {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    let hA : (signedMiddleMatrix (2 * m) a x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m) a x)
    let hB : (evenReflectedSignedMiddleMatrix m a x).IsHermitian :=
      evenReflectedSignedMiddleMatrix_isHermitian m hm ha x
    ∀ i : Fin (2 * m),
      orderedHermitianEigenvalue hB i =
        -orderedHermitianEigenvalue hA i.rev := by
  dsimp only
  let hA : (signedMiddleMatrix (2 * m) a x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm (2 * m) a x)
  let hB : (evenReflectedSignedMiddleMatrix m a x).IsHermitian :=
    evenReflectedSignedMiddleMatrix_isHermitian m hm ha x
  intro i
  calc
    orderedHermitianEigenvalue hB i =
        orderedHermitianEigenvalue hA.neg i :=
      orderedHermitianEigenvalue_eq_of_charpoly_eq hB hA.neg
        (evenReflectedSignedMiddleMatrix_charpoly m a x) i
    _ = -orderedHermitianEigenvalue hA i.rev :=
      orderedHermitianEigenvalue_neg hA i

/-- Embed coordinates indexed by the positive diagonal weights. -/
def positiveCoordinateEmbedding {n : ℕ} (w : Fin n → ℝ) :
    ({i // 0 < w i} → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun c i := if hi : 0 < w i then c ⟨i, hi⟩ else 0
  map_add' c d := by
    funext i
    by_cases hi : 0 < w i <;> simp [hi]
  map_smul' s c := by
    funext i
    by_cases hi : 0 < w i <;> simp [hi, smul_eq_mul]

theorem positiveCoordinateEmbedding_injective {n : ℕ} (w : Fin n → ℝ) :
    Function.Injective (positiveCoordinateEmbedding w) := by
  intro c d hcd
  funext i
  have h := congrFun hcd i.1
  simpa [positiveCoordinateEmbedding, i.2] using h

/-- Embed coordinates indexed by the negative diagonal weights. -/
def negativeCoordinateEmbedding {n : ℕ} (w : Fin n → ℝ) :
    ({i // w i < 0} → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun c i := if hi : w i < 0 then c ⟨i, hi⟩ else 0
  map_add' c d := by
    funext i
    by_cases hi : w i < 0 <;> simp [hi]
  map_smul' s c := by
    funext i
    by_cases hi : w i < 0 <;> simp [hi, smul_eq_mul]

theorem negativeCoordinateEmbedding_injective {n : ℕ} (w : Fin n → ℝ) :
    Function.Injective (negativeCoordinateEmbedding w) := by
  intro c d hcd
  funext i
  have h := congrFun hcd i.1
  simpa [negativeCoordinateEmbedding, i.2] using h

/-- A nonzero vector supported on positive diagonal weights has strictly
positive diagonal quadratic form. -/
theorem positiveCoordinateEmbedding_diagonal_pos {n : ℕ}
    (w : Fin n → ℝ) {c : {i // 0 < w i} → ℝ} (hc : c ≠ 0) :
    0 < positiveCoordinateEmbedding w c ⬝ᵥ
      (Matrix.diagonal w *ᵥ positiveCoordinateEmbedding w c) := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    simpa only [Function.ne_iff] using hc
  simp only [dotProduct, mulVec_diagonal]
  apply Finset.sum_pos'
  · intro j _
    by_cases hj : 0 < w j
    · simp only [positiveCoordinateEmbedding, LinearMap.coe_mk,
        AddHom.coe_mk, hj, dite_true]
      nlinarith [sq_nonneg (c ⟨j, hj⟩)]
    · simp [positiveCoordinateEmbedding, hj]
  · refine ⟨i.1, Finset.mem_univ _, ?_⟩
    simp only [positiveCoordinateEmbedding, LinearMap.coe_mk,
      AddHom.coe_mk, i.2, dite_true]
    change 0 < c i * (w i * c i)
    rw [show c i * (w i * c i) = w i * c i ^ 2 by ring]
    exact mul_pos i.2 (sq_pos_of_ne_zero hi)

/-- A nonzero vector supported on negative diagonal weights has strictly
negative diagonal quadratic form. -/
theorem negativeCoordinateEmbedding_diagonal_neg {n : ℕ}
    (w : Fin n → ℝ) {c : {i // w i < 0} → ℝ} (hc : c ≠ 0) :
    negativeCoordinateEmbedding w c ⬝ᵥ
      (Matrix.diagonal w *ᵥ negativeCoordinateEmbedding w c) < 0 := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    simpa only [Function.ne_iff] using hc
  simp only [dotProduct, mulVec_diagonal]
  apply Finset.sum_neg'
  · intro j _
    by_cases hj : w j < 0
    · simp only [negativeCoordinateEmbedding, LinearMap.coe_mk,
        AddHom.coe_mk, hj, dite_true]
      nlinarith [sq_nonneg (c ⟨j, hj⟩)]
    · simp [negativeCoordinateEmbedding, hj]
  · refine ⟨i.1, Finset.mem_univ _, ?_⟩
    simp only [negativeCoordinateEmbedding, LinearMap.coe_mk,
      AddHom.coe_mk, i.2, dite_true]
    change c i * (w i * c i) < 0
    rw [show c i * (w i * c i) = w i * c i ^ 2 by ring]
    exact mul_neg_of_neg_of_pos i.2 (sq_pos_of_ne_zero hi)

/-- Pulling a quadratic form through a matrix is exactly transpose
congruence. -/
theorem dotProduct_mulVec_congruence {n : ℕ}
    (A C : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    (C *ᵥ v) ⬝ᵥ (A *ᵥ (C *ᵥ v)) =
      v ⬝ᵥ ((Cᵀ * A * C) *ᵥ v) := by
  rw [dotProduct_mulVec, Matrix.vecMul_mulVec, ← dotProduct_mulVec,
    Matrix.mulVec_mulVec]

/-- Restrict a vector to `len` consecutive coordinates starting at
`start`. -/
def finIntervalTake {start len n : ℕ} (h : start + len ≤ n) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin len → ℝ) where
  toFun v i := v ⟨start + i.1, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- An invertible congruence to a diagonal matrix with exactly `q`
positive entries forces the `q - 1`-st decreasing eigenvalue to be
strictly positive.  This is the positive half of Sylvester inertia,
proved directly by a dimension-overlap argument. -/
theorem orderedHermitianEigenvalue_pos_of_congruent_diagonal
    {n q : ℕ} (hq : 0 < q) (hqn : q ≤ n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (C : Matrix (Fin n) (Fin n) ℝ) (hCunit : IsUnit C)
    (w : Fin n → ℝ) (hcongr : Cᵀ * A * C = Matrix.diagonal w)
    (hcard : Fintype.card {i // 0 < w i} = q) :
    0 < orderedHermitianEigenvalue hA ⟨q - 1, by omega⟩ := by
  let k : Fin n := ⟨q - 1, by omega⟩
  let T : ({i // 0 < w i} → ℝ) →ₗ[ℝ] (Fin (q - 1) → ℝ) :=
    (finPrefixTake (show q - 1 ≤ n by omega)).comp
      (((orderedHermitianEigenvectorMatrix hA)ᵀ).mulVecLin.comp
        (C.mulVecLin.comp (positiveCoordinateEmbedding w)))
  have hdim : Module.finrank ℝ (Fin (q - 1) → ℝ) <
      Module.finrank ℝ ({i // 0 < w i} → ℝ) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hcard]
    omega
  have hker : LinearMap.ker T ≠ ⊥ := T.ker_ne_bot_of_finrank_lt hdim
  rw [Submodule.ne_bot_iff] at hker
  obtain ⟨c, hcT, hc⟩ := hker
  have hc0 : T c = 0 := hcT
  let y : Fin n → ℝ := positiveCoordinateEmbedding w c
  let v : Fin n → ℝ := C *ᵥ y
  have hy : y ≠ 0 := by
    intro hy0
    apply hc
    apply positiveCoordinateEmbedding_injective w
    simpa only [map_zero] using hy0
  have hv : v ≠ 0 := by
    intro hv0
    apply hy
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hCunit)
    simpa only [Matrix.mulVec_zero] using hv0
  have hzero : ∀ i : Fin n, i < k → hermitianCoordinates hA v i = 0 := by
    intro i hik
    have hi : i.1 < q - 1 := by simpa only [k, Fin.mk_lt_mk] using hik
    have hci := congrFun hc0 ⟨i.1, hi⟩
    simpa only [T, LinearMap.comp_apply, finPrefixTake,
      LinearMap.coe_mk, AddHom.coe_mk, hermitianCoordinates, v, y] using hci
  have hquadpos : 0 < v ⬝ᵥ (A *ᵥ v) := by
    change 0 < (C *ᵥ y) ⬝ᵥ (A *ᵥ (C *ᵥ y))
    rw [dotProduct_mulVec_congruence A C y, hcongr]
    exact positiveCoordinateEmbedding_diagonal_pos w hc
  have hupper :=
    dotProduct_mulVec_le_orderedEigenvalue_mul_dotProduct hA k v hzero
  by_contra hnot
  have hnonpos : orderedHermitianEigenvalue hA k ≤ 0 := le_of_not_gt hnot
  have hnorm : 0 ≤ v ⬝ᵥ v := (dotProduct_self_pos hv).le
  have hrhs : orderedHermitianEigenvalue hA k * (v ⬝ᵥ v) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hnonpos hnorm
  exact (not_lt_of_ge (hupper.trans hrhs)) hquadpos

/-- An invertible congruence to a diagonal matrix with exactly `p`
negative entries forces the first of the final `p` decreasing eigenvalues
to be strictly negative.  This is the negative half of Sylvester inertia,
again proved directly by dimension overlap. -/
theorem orderedHermitianEigenvalue_neg_of_congruent_diagonal
    {n p : ℕ} (hp : 0 < p) (hpn : p ≤ n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (C : Matrix (Fin n) (Fin n) ℝ) (hCunit : IsUnit C)
    (w : Fin n → ℝ) (hcongr : Cᵀ * A * C = Matrix.diagonal w)
    (hcard : Fintype.card {i // w i < 0} = p) :
    orderedHermitianEigenvalue hA ⟨n - p, by omega⟩ < 0 := by
  let k : Fin n := ⟨n - p, by omega⟩
  let T : ({i // w i < 0} → ℝ) →ₗ[ℝ] (Fin (p - 1) → ℝ) :=
    (finIntervalTake
      (show (n - p + 1) + (p - 1) ≤ n by omega)).comp
      (((orderedHermitianEigenvectorMatrix hA)ᵀ).mulVecLin.comp
        (C.mulVecLin.comp (negativeCoordinateEmbedding w)))
  have hdim : Module.finrank ℝ (Fin (p - 1) → ℝ) <
      Module.finrank ℝ ({i // w i < 0} → ℝ) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hcard]
    omega
  have hker : LinearMap.ker T ≠ ⊥ := T.ker_ne_bot_of_finrank_lt hdim
  rw [Submodule.ne_bot_iff] at hker
  obtain ⟨c, hcT, hc⟩ := hker
  have hc0 : T c = 0 := hcT
  let y : Fin n → ℝ := negativeCoordinateEmbedding w c
  let v : Fin n → ℝ := C *ᵥ y
  have hy : y ≠ 0 := by
    intro hy0
    apply hc
    apply negativeCoordinateEmbedding_injective w
    simpa only [map_zero] using hy0
  have hv : v ≠ 0 := by
    intro hv0
    apply hy
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hCunit)
    simpa only [Matrix.mulVec_zero] using hv0
  have hzero : ∀ i : Fin n, k < i → hermitianCoordinates hA v i = 0 := by
    intro i hki
    have hki' : n - p < i.1 := by
      simpa only [k, Fin.mk_lt_mk] using hki
    let t : Fin (p - 1) := ⟨i.1 - (n - p + 1), by omega⟩
    have hci := congrFun hc0 t
    have hci' : hermitianCoordinates hA v
        ⟨n - p + 1 + t.1, by omega⟩ = 0 := by
      simpa only [T, LinearMap.comp_apply, finIntervalTake,
        LinearMap.coe_mk, AddHom.coe_mk, hermitianCoordinates, v, y] using hci
    have hind : (⟨n - p + 1 + t.1, by omega⟩ : Fin n) = i := by
      apply Fin.ext
      simp only [t]
      omega
    simpa only [hind] using hci'
  have hquadneg : v ⬝ᵥ (A *ᵥ v) < 0 := by
    change (C *ᵥ y) ⬝ᵥ (A *ᵥ (C *ᵥ y)) < 0
    rw [dotProduct_mulVec_congruence A C y, hcongr]
    exact negativeCoordinateEmbedding_diagonal_neg w hc
  have hlower :=
    orderedEigenvalue_mul_dotProduct_le_dotProduct_mulVec hA k v hzero
  by_contra hnot
  have hnonneg : 0 ≤ orderedHermitianEigenvalue hA k := le_of_not_gt hnot
  have hnorm : 0 ≤ v ⬝ᵥ v := (dotProduct_self_pos hv).le
  have hlhs : 0 ≤ orderedHermitianEigenvalue hA k * (v ⬝ᵥ v) :=
    mul_nonneg hnonneg hnorm
  exact (not_lt_of_ge (hlhs.trans hlower)) hquadneg

/-- The paper's natural-number inertia count is exactly the cardinality
of the positive-coordinate subtype used by the finite-dimensional
Sylvester argument above. -/
theorem middlePositiveInertiaCount_eq_card_positive
    (n : ℕ) (r x : ℝ) :
    middlePositiveInertiaCount n r x =
      Fintype.card {i : Fin n // 0 < middleInertiaWeight n r x i} := by
  unfold middlePositiveInertiaCount
  rw [Nat.count_eq_card_fintype]
  apply Fintype.card_congr
  exact
    { toFun := fun p =>
        ⟨⟨p.1, p.2.1⟩, by
          obtain ⟨hp, hpos⟩ := p.2.2
          simpa only using hpos⟩
      invFun := fun i =>
        ⟨i.1.1, i.1.2, ⟨i.1.2, i.2⟩⟩
      left_inv := by
        intro p
        apply Subtype.ext
        rfl
      right_inv := by
        intro i
        apply Subtype.ext
        rfl }

/-- If none of the diagonal entries vanishes, the negative-entry count
is the complementary cardinality of the positive-entry count. -/
theorem card_negative_eq_sub_of_card_positive {n q : ℕ}
    (w : Fin n → ℝ) (hnz : ∀ i, w i ≠ 0)
    (hpos : Fintype.card {i : Fin n // 0 < w i} = q) :
    Fintype.card {i : Fin n // w i < 0} = n - q := by
  let e : {i : Fin n // w i < 0} ≃ {i : Fin n // ¬ 0 < w i} :=
    { toFun := fun i => ⟨i.1, not_lt_of_ge i.2.le⟩
      invFun := fun i =>
        ⟨i.1, lt_of_le_of_ne (le_of_not_gt i.2) (hnz i.1)⟩
      left_inv := by
        intro i
        apply Subtype.ext
        rfl
      right_inv := by
        intro i
        apply Subtype.ext
        rfl }
  calc
    Fintype.card {i : Fin n // w i < 0} =
        Fintype.card {i : Fin n // ¬ 0 < w i} := Fintype.card_congr e
    _ = Fintype.card (Fin n) - Fintype.card {i : Fin n // 0 < w i} :=
      Fintype.card_subtype_compl (fun i : Fin n => 0 < w i)
    _ = n - q := by simp only [Fintype.card_fin, hpos]

/-- No diagonal entry in the inertia congruence vanishes at an interior
point of an open spectral gap. -/
theorem middleInertiaWeight_ne_zero_of_mem_spectralGap
    (n j : ℕ) (hj : 0 < j) (hjn : j < n) {r : ℝ} (hr : 0 < r)
    {x : ℝ}
    (hxLower : symmetricPathEigenvalue n r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue n r ⟨j - 1, by omega⟩)
    (k : Fin n) :
    middleInertiaWeight n r x k ≠ 0 := by
  unfold middleInertiaWeight middleDiagonalWeight
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact pow_ne_zero _ (inv_ne_zero hr.ne')
    · exact ne_of_gt (pathSineNormSq_pos n k)
  · apply mul_ne_zero
    · exact pow_ne_zero _ (by norm_num)
    · apply sub_ne_zero.mpr
      by_cases hkj : k.1 < j
      · have hkUpper : k ≤ (⟨j - 1, by omega⟩ : Fin n) := by
          exact Fin.mk_le_mk.mpr (by omega)
        have hxEigen : x < symmetricPathEigenvalue n r k :=
          hxUpper.trans_le
            ((symmetricPathEigenvalue_strictAnti n hr).antitone hkUpper)
        exact ne_of_lt hxEigen
      · have hjk : (⟨j, hjn⟩ : Fin n) ≤ k := by
          exact Fin.mk_le_mk.mpr (by omega)
        have hEigenX : symmetricPathEigenvalue n r k < x :=
          lt_of_le_of_lt
            ((symmetricPathEigenvalue_strictAnti n hr).antitone hjk) hxLower
        exact ne_of_gt hEigenX

/-- Exact ordered sign threshold supplied by the signed-middle inertia
certificate: if the gap count is `q`, precisely the first `q` decreasing
eigenvalues are positive and the remaining ones are negative. -/
theorem signedMiddleMatrix_ordered_signs_of_gap
    (n j q : ℕ) (hn : 0 < n) (hj : 0 < j) (hjn : j < n)
    (hq : 0 < q) (hqn : q < n) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue n r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue n r ⟨j - 1, by omega⟩)
    (hcount : middlePositiveInertiaCount n r x = q) :
    let hB : (signedMiddleMatrix n (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n (r ^ 2) x)
    0 < orderedHermitianEigenvalue hB ⟨q - 1, by omega⟩ ∧
      orderedHermitianEigenvalue hB ⟨q, hqn⟩ < 0 := by
  dsimp only
  let B := signedMiddleMatrix n (r ^ 2) x
  let hB : B.IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n (r ^ 2) x)
  let C := middleCongruenceMatrix n r
  let w := middleInertiaWeight n r x
  have hcongr : Matrix.transpose C * B * C = Matrix.diagonal w := by
    exact middleCongruenceMatrix_transpose_mul_signedMiddleMatrix_mul
      n hn hr x
  have hunit : IsUnit C := middleCongruenceMatrix_isUnit n hr
  have hcardpos : Fintype.card {i : Fin n // 0 < w i} = q := by
    rw [← middlePositiveInertiaCount_eq_card_positive n r x]
    exact hcount
  have hnz : ∀ i, w i ≠ 0 := fun i =>
    middleInertiaWeight_ne_zero_of_mem_spectralGap
      n j hj hjn hr hxLower hxUpper i
  have hcardneg : Fintype.card {i : Fin n // w i < 0} = n - q :=
    card_negative_eq_sub_of_card_positive w hnz hcardpos
  have hpos : 0 < orderedHermitianEigenvalue hB ⟨q - 1, by omega⟩ :=
    orderedHermitianEigenvalue_pos_of_congruent_diagonal
      hq hqn.le hB C hunit w hcongr hcardpos
  have hpneg : 0 < n - q := by omega
  have hneg' := orderedHermitianEigenvalue_neg_of_congruent_diagonal
    hpneg (Nat.sub_le n q) hB C hunit w hcongr hcardneg
  have hind : (⟨n - (n - q), by omega⟩ : Fin n) = ⟨q, hqn⟩ := by
    apply Fin.ext
    simp only
    omega
  exact ⟨hpos, by simpa only [hind] using hneg'⟩

/-- Zero positive inertia means that even the largest ordered eigenvalue
is strictly negative.  This covers the exceptional two-dimensional odd
gap without inventing a nonexistent positive threshold index. -/
theorem signedMiddleMatrix_ordered_top_neg_of_gap
    (n j : ℕ) (hn : 0 < n) (hj : 0 < j) (hjn : j < n)
    {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue n r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue n r ⟨j - 1, by omega⟩)
    (hcount : middlePositiveInertiaCount n r x = 0) :
    let hB : (signedMiddleMatrix n (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n (r ^ 2) x)
    orderedHermitianEigenvalue hB ⟨0, hn⟩ < 0 := by
  dsimp only
  let B := signedMiddleMatrix n (r ^ 2) x
  let hB : B.IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n (r ^ 2) x)
  let C := middleCongruenceMatrix n r
  let w := middleInertiaWeight n r x
  have hcongr : Matrix.transpose C * B * C = Matrix.diagonal w :=
    middleCongruenceMatrix_transpose_mul_signedMiddleMatrix_mul n hn hr x
  have hunit : IsUnit C := middleCongruenceMatrix_isUnit n hr
  have hcardpos : Fintype.card {i : Fin n // 0 < w i} = 0 := by
    rw [← middlePositiveInertiaCount_eq_card_positive n r x]
    exact hcount
  have hnz : ∀ i, w i ≠ 0 := fun i =>
    middleInertiaWeight_ne_zero_of_mem_spectralGap
      n j hj hjn hr hxLower hxUpper i
  have hcardneg : Fintype.card {i : Fin n // w i < 0} = n := by
    simpa only [Nat.sub_zero] using
      card_negative_eq_sub_of_card_positive w hnz hcardpos
  have hneg := orderedHermitianEigenvalue_neg_of_congruent_diagonal
    hn (le_refl n) hB C hunit w hcongr hcardneg
  have hind : (⟨n - n, by omega⟩ : Fin n) = ⟨0, hn⟩ := by
    apply Fin.ext
    simp only [Nat.sub_self]
  simpa only [hind] using hneg

/-- Exact central ordered signs in an even-dimensional even-numbered
spectral gap. -/
theorem evenSignedMiddleMatrix_ordered_signs_even_gap
    (m j : ℕ) (hm : 0 < m) (hj : 0 < j) (hjn : j < 2 * m)
    (hjEven : Even j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m) r ⟨j - 1, by omega⟩) :
    let hB : (signedMiddleMatrix (2 * m) (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m) (r ^ 2) x)
    0 < orderedHermitianEigenvalue hB ⟨m - 1, by omega⟩ ∧
      orderedHermitianEigenvalue hB ⟨m, by omega⟩ < 0 := by
  dsimp only
  exact signedMiddleMatrix_ordered_signs_of_gap
    (2 * m) j m (by omega) hj hjn hm (by omega) hr hxLower hxUpper
      (middlePositiveInertiaCount_even_dimension_even_gap
        m j hj hjn hjEven hr hxLower hxUpper)

/-- Exact central ordered signs in an even-dimensional odd-numbered gap
when `m ≥ 2`. -/
theorem evenSignedMiddleMatrix_ordered_signs_odd_gap
    (m j : ℕ) (hm : 2 ≤ m) (hj : 0 < j) (hjn : j < 2 * m)
    (hjOdd : Odd j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m) r ⟨j - 1, by omega⟩) :
    let hB : (signedMiddleMatrix (2 * m) (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m) (r ^ 2) x)
    0 < orderedHermitianEigenvalue hB ⟨m - 2, by omega⟩ ∧
      orderedHermitianEigenvalue hB ⟨m - 1, by omega⟩ < 0 := by
  dsimp only
  exact signedMiddleMatrix_ordered_signs_of_gap
    (2 * m) j (m - 1) (by omega) hj hjn (by omega) (by omega) hr
      hxLower hxUpper
      (middlePositiveInertiaCount_even_dimension_odd_gap
        m j hj hjn hjOdd hr hxLower hxUpper)

/-- The sole `n = 2` odd gap has both ordered eigenvalues negative. -/
theorem twoSignedMiddleMatrix_ordered_top_neg_odd_gap
    (j : ℕ) (hj : 0 < j) (hjn : j < 2) (hjOdd : Odd j)
    {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue 2 r ⟨j, hjn⟩ < x)
    (hxUpper : x < symmetricPathEigenvalue 2 r ⟨j - 1, by omega⟩) :
    let hB : (signedMiddleMatrix 2 (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm 2 (r ^ 2) x)
    orderedHermitianEigenvalue hB 0 < 0 := by
  dsimp only
  exact signedMiddleMatrix_ordered_top_neg_of_gap
    2 j (by omega) hj hjn hr hxLower hxUpper
      (by
        simpa only [Nat.reduceSubDiff] using
          middlePositiveInertiaCount_even_dimension_odd_gap
            1 j hj hjn hjOdd hr hxLower hxUpper)

/-- Exact central ordered signs in an odd-dimensional even-numbered gap. -/
theorem oddSignedMiddleMatrix_ordered_signs_even_gap
    (m j : ℕ) (hm : 0 < m) (hj : 0 < j) (hjn : j < 2 * m + 1)
    (hjEven : Even j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m + 1) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m + 1) r ⟨j - 1, by omega⟩) :
    let hB : (signedMiddleMatrix (2 * m + 1) (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m + 1) (r ^ 2) x)
    0 < orderedHermitianEigenvalue hB ⟨m, by omega⟩ ∧
      orderedHermitianEigenvalue hB ⟨m + 1, by omega⟩ < 0 := by
  dsimp only
  exact signedMiddleMatrix_ordered_signs_of_gap
    (2 * m + 1) j (m + 1) (by omega) hj hjn (by omega) (by omega) hr
      hxLower hxUpper
      (middlePositiveInertiaCount_odd_dimension_even_gap
        m j hj hjn hjEven hr hxLower hxUpper)

/-- Exact central ordered signs in an odd-dimensional odd-numbered gap. -/
theorem oddSignedMiddleMatrix_ordered_signs_odd_gap
    (m j : ℕ) (hm : 0 < m) (hj : 0 < j) (hjn : j < 2 * m + 1)
    (hjOdd : Odd j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m + 1) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m + 1) r ⟨j - 1, by omega⟩) :
    let hB : (signedMiddleMatrix (2 * m + 1) (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m + 1) (r ^ 2) x)
    0 < orderedHermitianEigenvalue hB ⟨m - 1, by omega⟩ ∧
      orderedHermitianEigenvalue hB ⟨m, by omega⟩ < 0 := by
  dsimp only
  exact signedMiddleMatrix_ordered_signs_of_gap
    (2 * m + 1) j m (by omega) hj hjn hm (by omega) hr hxLower hxUpper
      (middlePositiveInertiaCount_odd_dimension_odd_gap
        m j hj hjn hjOdd hr hxLower hxUpper)

/-- The odd folding permutation: it fixes the first `m` coordinates,
reverses the last `m`, and moves the middle coordinate to the end. -/
def oddFoldIndex (m : ℕ) (i : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  if hi : i.1 < m then ⟨i.1, i.2⟩ else ⟨3 * m - i.1, by omega⟩

theorem oddFoldIndex_involutive (m : ℕ) :
    Function.Involutive (oddFoldIndex m) := by
  intro i
  by_cases hi : i.1 < m
  · simp [oddFoldIndex, hi]
  · have hout : ¬3 * m - i.1 < m := by omega
    apply Fin.ext
    simp [oddFoldIndex, hi, hout]
    omega

/-- The involutive coordinate permutation induced by `oddFoldIndex`: it
fixes the first `m` coordinates, reverses the final `m`, and sends the
middle coordinate to the last position. -/
def oddFoldPerm (m : ℕ) : Equiv.Perm (Fin (2 * m + 1)) where
  toFun := oddFoldIndex m
  invFun := oddFoldIndex m
  left_inv := oddFoldIndex_involutive m
  right_inv := oddFoldIndex_involutive m

/-- The standard two-block coordinate equivalence with the arithmetic
normalization `m + m = 2*m` made explicit. -/
def twoBlockFinEquiv (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  (@finSumFinEquiv m m).trans (finCongr (by omega))

@[simp] theorem twoBlockFinEquiv_inl_val (m : ℕ) (i : Fin m) :
    (twoBlockFinEquiv m (Sum.inl i)).1 = i.1 := by
  simp [twoBlockFinEquiv]

@[simp] theorem twoBlockFinEquiv_inr_val (m : ℕ) (i : Fin m) :
    (twoBlockFinEquiv m (Sum.inr i)).1 = m + i.1 := by
  simp [twoBlockFinEquiv]
  omega

@[simp] theorem oddFoldPerm_val_of_lt (m : ℕ)
    (i : Fin (2 * m + 1)) (hi : i.1 < m) :
    (oddFoldPerm m i).1 = i.1 := by
  simp [oddFoldPerm, oddFoldIndex, hi]

@[simp] theorem oddFoldPerm_val_of_le (m : ℕ)
    (i : Fin (2 * m + 1)) (hi : m ≤ i.1) :
    (oddFoldPerm m i).1 = 3 * m - i.1 := by
  simp [oddFoldPerm, oddFoldIndex, not_lt.mpr hi]

theorem oddFoldPerm_inl_val (m : ℕ) (i : Fin m) :
    (oddFoldPerm m ((twoBlockFinEquiv m (Sum.inl i)).castSucc)).1 = i.1 := by
  rw [oddFoldPerm_val_of_lt]
  · simp
  · change i.1 < m
    exact i.2

theorem oddFoldPerm_inr_val (m : ℕ) (i : Fin m) :
    (oddFoldPerm m ((twoBlockFinEquiv m (Sum.inr i)).castSucc)).1 =
      2 * m - i.1 := by
  rw [oddFoldPerm_val_of_le]
  · simp
    omega
  · simp

theorem oddFoldPerm_inl_rev_val (m : ℕ) (i : Fin m) :
    ((oddFoldPerm m
      ((twoBlockFinEquiv m (Sum.inl i)).castSucc)).rev).1 =
        2 * m - i.1 := by
  rw [Fin.val_rev, oddFoldPerm_inl_val]
  omega

theorem oddFoldPerm_inr_rev_val (m : ℕ) (i : Fin m) :
    ((oddFoldPerm m
      ((twoBlockFinEquiv m (Sum.inr i)).castSucc)).rev).1 = i.1 := by
  rw [Fin.val_rev, oddFoldPerm_inr_val]
  omega

/-- The odd signed-middle matrix in the folded order of
`eq:odd-dilation`. -/
def oddFoldedSignedMiddleMatrix (m : ℕ) (a x : ℝ) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  (signedMiddleMatrix (2 * m + 1) a x).submatrix
    (oddFoldPerm m) (oddFoldPerm m)

/-- The coupling vector `w=[-eₘ;-a eₘ]` in `eq:odd-dilation`.
The last-coordinate test makes this definition valid when `m = 0`, where
both summands are empty. -/
def oddDilationCoupling (m : ℕ) (a : ℝ) : Fin m ⊕ Fin m → ℝ
  | Sum.inl i => if i.1 + 1 = m then -1 else 0
  | Sum.inr i => if i.1 + 1 = m then -a else 0

/-- The last folded coordinate is the original middle coordinate. -/
@[simp] theorem oddFoldPerm_last_val (m : ℕ) :
    (oddFoldPerm m (Fin.last (2 * m))).1 = m := by
  rw [oddFoldPerm_val_of_le]
  · simp
    omega
  · change m ≤ 2 * m
    omega

/-- Reversal fixes the original middle coordinate selected by the last
folded coordinate. -/
@[simp] theorem oddFoldPerm_last_rev_val (m : ℕ) :
    ((oddFoldPerm m (Fin.last (2 * m))).rev).1 = m := by
  rw [Fin.val_rev, oddFoldPerm_last_val]
  omega

/-- Exact last column of the bordered odd dilation. -/
theorem oddFoldedSignedMiddleMatrix_last_column
    (m : ℕ) (a x : ℝ) (i : Fin m ⊕ Fin m) :
    oddFoldedSignedMiddleMatrix m a x
        ((twoBlockFinEquiv m i).castSucc) (Fin.last (2 * m)) =
      oddDilationCoupling m a i := by
  rcases i with i | i
  · simp only [oddFoldedSignedMiddleMatrix, Matrix.submatrix_apply,
      signedMiddleMatrix, mul_reversal_apply, oddFoldPerm_inl_val,
      oddFoldPerm_last_rev_val, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, pathMatrix_apply, oddDilationCoupling,
      Fin.ext_iff, smul_eq_mul]
    split_ifs <;> (first | omega | norm_num)
  · simp only [oddFoldedSignedMiddleMatrix, Matrix.submatrix_apply,
      signedMiddleMatrix, mul_reversal_apply, oddFoldPerm_inr_val,
      oddFoldPerm_last_rev_val, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, pathMatrix_apply, oddDilationCoupling,
      Fin.ext_iff, smul_eq_mul]
    split_ifs <;> (first | omega | norm_num)

/-- Exact last row of the bordered odd dilation. -/
theorem oddFoldedSignedMiddleMatrix_last_row
    (m : ℕ) (a x : ℝ) (i : Fin m ⊕ Fin m) :
    oddFoldedSignedMiddleMatrix m a x
        (Fin.last (2 * m)) ((twoBlockFinEquiv m i).castSucc) =
      oddDilationCoupling m a i := by
  rcases i with i | i
  · simp only [oddFoldedSignedMiddleMatrix, Matrix.submatrix_apply,
      signedMiddleMatrix, mul_reversal_apply, oddFoldPerm_last_val,
      oddFoldPerm_inl_rev_val, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, pathMatrix_apply, oddDilationCoupling,
      Fin.ext_iff, smul_eq_mul]
    split_ifs <;> (first | omega | norm_num)
  · simp only [oddFoldedSignedMiddleMatrix, Matrix.submatrix_apply,
      signedMiddleMatrix, mul_reversal_apply, oddFoldPerm_last_val,
      oddFoldPerm_inr_rev_val, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, pathMatrix_apply, oddDilationCoupling,
      Fin.ext_iff, smul_eq_mul]
    split_ifs <;> (first | omega | norm_num)

/-- Exact bottom-right scalar of the bordered odd dilation. -/
@[simp] theorem oddFoldedSignedMiddleMatrix_bottom_right
    (m : ℕ) (a x : ℝ) :
    oddFoldedSignedMiddleMatrix m a x
        (Fin.last (2 * m)) (Fin.last (2 * m)) = x := by
  simp only [oddFoldedSignedMiddleMatrix, Matrix.submatrix_apply,
    signedMiddleMatrix, mul_reversal_apply, oddFoldPerm_last_val,
    oddFoldPerm_last_rev_val, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, pathMatrix_apply, Fin.ext_iff, smul_eq_mul]
  split_ifs <;> (first | omega | norm_num)

/-- The leading `2m × 2m` block in the odd folding is exactly the
off-diagonal dilation `widehat P_m(x)`. -/
theorem oddLeadingPrincipal_submatrix_eq_evenPathDilation
    (m : ℕ) (a x : ℝ) :
    (leadingPrincipalMatrix
      (oddFoldedSignedMiddleMatrix m a x)).submatrix
        (twoBlockFinEquiv m) (twoBlockFinEquiv m) =
      evenPathDilation m a x := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · have hjrev := oddFoldPerm_inl_rev_val m j
    simp only [leadingPrincipalMatrix, Matrix.submatrix_apply,
      oddFoldedSignedMiddleMatrix, signedMiddleMatrix,
      mul_reversal_apply, oddFoldPerm_inl_val,
      oddFoldPerm_inl_rev_val, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, pathMatrix_apply, evenPathDilation,
      Matrix.fromBlocks_apply₁₁, Matrix.zero_apply, Fin.ext_iff,
      smul_eq_mul]
    split_ifs <;> (first | omega | norm_num)
  · have hjrev := oddFoldPerm_inr_rev_val m j
    simp only [leadingPrincipalMatrix, Matrix.submatrix_apply,
      oddFoldedSignedMiddleMatrix, signedMiddleMatrix,
      mul_reversal_apply, oddFoldPerm_inl_val,
      oddFoldPerm_inr_rev_val, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, pathMatrix_apply, evenPathDilation,
      Matrix.fromBlocks_apply₁₂, realShiftedPathMatrix, Fin.ext_iff,
      smul_eq_mul]
  · have hjrev := oddFoldPerm_inl_rev_val m j
    simp only [leadingPrincipalMatrix, Matrix.submatrix_apply,
      oddFoldedSignedMiddleMatrix, signedMiddleMatrix,
      mul_reversal_apply, oddFoldPerm_inr_val,
      oddFoldPerm_inl_rev_val, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, pathMatrix_apply, evenPathDilation,
      Matrix.fromBlocks_apply₂₁, realShiftedPathMatrix,
      Matrix.transpose_apply, Fin.ext_iff, smul_eq_mul]
    split_ifs <;> (first | omega | norm_num)
  · have hjrev := oddFoldPerm_inr_rev_val m j
    simp only [leadingPrincipalMatrix, Matrix.submatrix_apply,
      oddFoldedSignedMiddleMatrix, signedMiddleMatrix,
      mul_reversal_apply, oddFoldPerm_inr_val,
      oddFoldPerm_inr_rev_val, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, pathMatrix_apply, evenPathDilation,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Fin.ext_iff,
      smul_eq_mul]
    split_ifs <;> (first | omega | norm_num)

/-- The dilation in the ordinary `Fin (2m)` coordinate type used by the
ordered-eigenvalue and Cauchy-interlacing infrastructure. -/
def evenPathDilationFin (m : ℕ) (a x : ℝ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  (evenPathDilation m a x).submatrix
    (twoBlockFinEquiv m).symm (twoBlockFinEquiv m).symm

theorem evenPathDilation_isSymm (m : ℕ) (a x : ℝ) :
    (evenPathDilation m a x).IsSymm := by
  rw [Matrix.IsSymm]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [evenPathDilation]

theorem evenPathDilationFin_isHermitian (m : ℕ) (a x : ℝ) :
    (evenPathDilationFin m a x).IsHermitian := by
  exact (Matrix.IsSymm.isHermitianReal
    (evenPathDilation_isSymm m a x)).submatrix _

/-- The folded signature transported to ordinary `Fin (2m)` indices. -/
def evenDilationSignatureFin (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  (evenSignature m).submatrix
    (twoBlockFinEquiv m).symm (twoBlockFinEquiv m).symm

theorem evenDilationSignatureFin_mul_self (m : ℕ) :
    evenDilationSignatureFin m * evenDilationSignatureFin m = 1 := by
  rw [evenDilationSignatureFin, Matrix.submatrix_mul_equiv,
    evenSignature_mul_self]
  exact Matrix.submatrix_one_equiv (twoBlockFinEquiv m).symm

/-- Signature conjugation realizes the exact spectral reflection of the
ordinary-index dilation. -/
theorem evenDilationSignatureFin_conjugate (m : ℕ) (a x : ℝ) :
    -(evenDilationSignatureFin m * evenPathDilationFin m a x *
        evenDilationSignatureFin m) =
      evenPathDilationFin m a x := by
  rw [evenDilationSignatureFin, evenPathDilationFin,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  change (-(evenSignature m * evenPathDilation m a x *
      evenSignature m)).submatrix (twoBlockFinEquiv m).symm
        (twoBlockFinEquiv m).symm =
    (evenPathDilation m a x).submatrix (twoBlockFinEquiv m).symm
      (twoBlockFinEquiv m).symm
  rw [evenSignature_conjugate_dilation]

theorem evenPathDilationFin_charpoly_neg (m : ℕ) (a x : ℝ) :
    (evenPathDilationFin m a x).charpoly =
      (-evenPathDilationFin m a x).charpoly := by
  have hrewrite :
      -(evenDilationSignatureFin m * evenPathDilationFin m a x *
          evenDilationSignatureFin m) =
        (evenDilationSignatureFin m *
          (-evenPathDilationFin m a x)) *
            evenDilationSignatureFin m := by
    noncomm_ring
  have hassoc :
      evenDilationSignatureFin m *
          (evenDilationSignatureFin m *
            (-evenPathDilationFin m a x)) =
        (evenDilationSignatureFin m * evenDilationSignatureFin m) *
          (-evenPathDilationFin m a x) := by
    noncomm_ring
  calc
    (evenPathDilationFin m a x).charpoly =
        (-(evenDilationSignatureFin m *
          evenPathDilationFin m a x *
            evenDilationSignatureFin m)).charpoly :=
      congrArg Matrix.charpoly
        (evenDilationSignatureFin_conjugate m a x).symm
    _ = ((evenDilationSignatureFin m *
          (-evenPathDilationFin m a x)) *
            evenDilationSignatureFin m).charpoly := by rw [hrewrite]
    _ = (evenDilationSignatureFin m *
          (evenDilationSignatureFin m *
            (-evenPathDilationFin m a x))).charpoly := by
      rw [Matrix.charpoly_mul_comm]
    _ = (-evenPathDilationFin m a x).charpoly := by
      rw [hassoc, evenDilationSignatureFin_mul_self, Matrix.one_mul]

/-- Spectral reflection pairs the two central dilation eigenvalues as
`s,-s`, where `s≥0`. -/
theorem evenPathDilationFin_central_pair
    (m : ℕ) (hm : 0 < m) (a x : ℝ) :
    let hD : (evenPathDilationFin m a x).IsHermitian :=
      evenPathDilationFin_isHermitian m a x
    0 ≤ orderedHermitianEigenvalue hD ⟨m - 1, by omega⟩ ∧
      orderedHermitianEigenvalue hD ⟨m, by omega⟩ =
        -orderedHermitianEigenvalue hD ⟨m - 1, by omega⟩ := by
  dsimp only
  let D := evenPathDilationFin m a x
  let hD : D.IsHermitian := evenPathDilationFin_isHermitian m a x
  have hreflect : ∀ i : Fin (2 * m),
      orderedHermitianEigenvalue hD i =
        -orderedHermitianEigenvalue hD i.rev := by
    intro i
    calc
      orderedHermitianEigenvalue hD i =
          orderedHermitianEigenvalue hD.neg i :=
        orderedHermitianEigenvalue_eq_of_charpoly_eq hD hD.neg
          (evenPathDilationFin_charpoly_neg m a x) i
      _ = -orderedHermitianEigenvalue hD i.rev :=
        orderedHermitianEigenvalue_neg hD i
  let c : Fin (2 * m) := ⟨m - 1, by omega⟩
  let d : Fin (2 * m) := ⟨m, by omega⟩
  have hrev : d.rev = c := by
    apply Fin.ext
    simp [c, d]
    omega
  have hpair : orderedHermitianEigenvalue hD d =
      -orderedHermitianEigenvalue hD c := by
    rw [hreflect, hrev]
  have horder : orderedHermitianEigenvalue hD d ≤
      orderedHermitianEigenvalue hD c :=
    (orderedHermitianEigenvalue_antitone hD) (by
      change m - 1 ≤ m
      omega)
  have hc_nonneg : 0 ≤ orderedHermitianEigenvalue hD c := by
    rw [hpair] at horder
    linarith
  exact ⟨by simpa only [c] using hc_nonneg, by simpa only [c, d] using hpair⟩

theorem oddFoldedSignedMiddleMatrix_isHermitian
    (m : ℕ) (a x : ℝ) :
    (oddFoldedSignedMiddleMatrix m a x).IsHermitian := by
  exact (Matrix.IsSymm.isHermitianReal
    (signedMiddleMatrix_isSymm (2 * m + 1) a x)).submatrix _

/-- The leading principal matrix in ordinary coordinates is the
ordinary-index version of the exact folded dilation. -/
theorem oddLeadingPrincipal_eq_evenPathDilationFin
    (m : ℕ) (a x : ℝ) :
    leadingPrincipalMatrix (oddFoldedSignedMiddleMatrix m a x) =
      evenPathDilationFin m a x := by
  ext i j
  change (leadingPrincipalMatrix
      (oddFoldedSignedMiddleMatrix m a x)) i j =
    (evenPathDilation m a x)
      ((twoBlockFinEquiv m).symm i) ((twoBlockFinEquiv m).symm j)
  rw [← oddLeadingPrincipal_submatrix_eq_evenPathDilation]
  simp

/-- The odd folded leading block has central eigenvalues `s,-s`
with `s≥0`, for every real shift. -/
theorem oddLeadingPrincipal_central_pair
    (m : ℕ) (hm : 0 < m) (a x : ℝ) :
    let hB : (oddFoldedSignedMiddleMatrix m a x).IsHermitian :=
      oddFoldedSignedMiddleMatrix_isHermitian m a x
    let hC := leadingPrincipalMatrix_isHermitian hB
    0 ≤ orderedHermitianEigenvalue hC ⟨m - 1, by omega⟩ ∧
      orderedHermitianEigenvalue hC ⟨m, by omega⟩ =
        -orderedHermitianEigenvalue hC ⟨m - 1, by omega⟩ := by
  dsimp only
  let B := oddFoldedSignedMiddleMatrix m a x
  let hB : B.IsHermitian := oddFoldedSignedMiddleMatrix_isHermitian m a x
  let C := leadingPrincipalMatrix B
  let hC : C.IsHermitian := leadingPrincipalMatrix_isHermitian hB
  let D := evenPathDilationFin m a x
  let hD : D.IsHermitian := evenPathDilationFin_isHermitian m a x
  have hCD : C = D := oddLeadingPrincipal_eq_evenPathDilationFin m a x
  have hordered : ∀ i : Fin (2 * m),
      orderedHermitianEigenvalue hC i = orderedHermitianEigenvalue hD i :=
    orderedHermitianEigenvalue_eq_of_charpoly_eq hC hD (by rw [hCD])
  have hpair := evenPathDilationFin_central_pair m hm a x
  constructor
  · rw [hordered]
    exact hpair.1
  · rw [hordered, hordered]
    exact hpair.2

/-- Reindexing by the odd folding permutation preserves the full
characteristic polynomial. -/
theorem oddFoldedSignedMiddleMatrix_charpoly (m : ℕ) (a x : ℝ) :
    (oddFoldedSignedMiddleMatrix m a x).charpoly =
      (signedMiddleMatrix (2 * m + 1) a x).charpoly := by
  have hcharm : Matrix.charmatrix
      (oddFoldedSignedMiddleMatrix m a x) =
      (Matrix.charmatrix
        (signedMiddleMatrix (2 * m + 1) a x)).submatrix
          (oddFoldPerm m) (oddFoldPerm m) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.charmatrix, oddFoldedSignedMiddleMatrix]
    · have hpne : oddFoldPerm m i ≠ oddFoldPerm m j :=
        (oddFoldPerm m).injective.ne hij
      simp [Matrix.charmatrix, oddFoldedSignedMiddleMatrix, hij, hpne]
  rw [Matrix.charpoly, Matrix.charpoly, hcharm,
    Matrix.det_submatrix_equiv_self]

theorem oddFolded_orderedEigenvalue_eq_original
    (m : ℕ) (a x : ℝ) :
    let hB : (oddFoldedSignedMiddleMatrix m a x).IsHermitian :=
      oddFoldedSignedMiddleMatrix_isHermitian m a x
    let hA : (signedMiddleMatrix (2 * m + 1) a x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m + 1) a x)
    ∀ i : Fin (2 * m + 1),
      orderedHermitianEigenvalue hB i = orderedHermitianEigenvalue hA i := by
  dsimp only
  exact orderedHermitianEigenvalue_eq_of_charpoly_eq
    (oddFoldedSignedMiddleMatrix_isHermitian m a x)
    (Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm (2 * m + 1) a x))
    (oddFoldedSignedMiddleMatrix_charpoly m a x)

/-- Odd-dimensional even-gap half of `lem:middle-branch`: the positive
central ordered branch is the least-modulus signed eigenvalue. -/
theorem oddSignedMiddleMatrix_central_abs_min_even_gap
    (m j : ℕ) (hm : 0 < m) (hj : 0 < j) (hjn : j < 2 * m + 1)
    (hjEven : Even j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m + 1) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m + 1) r ⟨j - 1, by omega⟩) :
    let hA : (signedMiddleMatrix (2 * m + 1) (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m + 1) (r ^ 2) x)
    0 < orderedHermitianEigenvalue hA ⟨m, by omega⟩ ∧
      ∀ i : Fin (2 * m + 1),
        |orderedHermitianEigenvalue hA ⟨m, by omega⟩| ≤
          |orderedHermitianEigenvalue hA i| := by
  dsimp only
  let A := signedMiddleMatrix (2 * m + 1) (r ^ 2) x
  let hA : A.IsHermitian := Matrix.IsSymm.isHermitianReal
    (signedMiddleMatrix_isSymm (2 * m + 1) (r ^ 2) x)
  let B := oddFoldedSignedMiddleMatrix m (r ^ 2) x
  let hB : B.IsHermitian :=
    oddFoldedSignedMiddleMatrix_isHermitian m (r ^ 2) x
  have hordered : ∀ i : Fin (2 * m + 1),
      orderedHermitianEigenvalue hB i = orderedHermitianEigenvalue hA i :=
    oddFolded_orderedEigenvalue_eq_original m (r ^ 2) x
  have hsignA := oddSignedMiddleMatrix_ordered_signs_even_gap
    m j hm hj hjn hjEven hr hxLower hxUpper
  have hsignB : 0 < orderedHermitianEigenvalue hB ⟨m, by omega⟩ := by
    rw [hordered]
    exact hsignA.1
  let hC := leadingPrincipalMatrix_isHermitian hB
  have hcentral := oddLeadingPrincipal_central_pair m hm (r ^ 2) x
  let s := orderedHermitianEigenvalue hC ⟨m - 1, by omega⟩
  have hresult := oddCentral_abs_min_of_positive_leadingPrincipal
    m hm hB s rfl hcentral.2 hsignB
  constructor
  · rw [← hordered]
    exact hresult.1
  · intro i
    rw [← hordered, ← hordered]
    exact hresult.2 i

/-- Odd-dimensional odd-gap half of `lem:middle-branch`: the negative
central ordered branch is the least-modulus signed eigenvalue. -/
theorem oddSignedMiddleMatrix_central_abs_min_odd_gap
    (m j : ℕ) (hm : 0 < m) (hj : 0 < j) (hjn : j < 2 * m + 1)
    (hjOdd : Odd j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m + 1) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m + 1) r ⟨j - 1, by omega⟩) :
    let hA : (signedMiddleMatrix (2 * m + 1) (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m + 1) (r ^ 2) x)
    orderedHermitianEigenvalue hA ⟨m, by omega⟩ < 0 ∧
      ∀ i : Fin (2 * m + 1),
        |orderedHermitianEigenvalue hA ⟨m, by omega⟩| ≤
          |orderedHermitianEigenvalue hA i| := by
  dsimp only
  let A := signedMiddleMatrix (2 * m + 1) (r ^ 2) x
  let hA : A.IsHermitian := Matrix.IsSymm.isHermitianReal
    (signedMiddleMatrix_isSymm (2 * m + 1) (r ^ 2) x)
  let B := oddFoldedSignedMiddleMatrix m (r ^ 2) x
  let hB : B.IsHermitian :=
    oddFoldedSignedMiddleMatrix_isHermitian m (r ^ 2) x
  have hordered : ∀ i : Fin (2 * m + 1),
      orderedHermitianEigenvalue hB i = orderedHermitianEigenvalue hA i :=
    oddFolded_orderedEigenvalue_eq_original m (r ^ 2) x
  have hsignA := oddSignedMiddleMatrix_ordered_signs_odd_gap
    m j hm hj hjn hjOdd hr hxLower hxUpper
  have hsignB : orderedHermitianEigenvalue hB ⟨m, by omega⟩ < 0 := by
    rw [hordered]
    exact hsignA.2
  let hC := leadingPrincipalMatrix_isHermitian hB
  have hcentral := oddLeadingPrincipal_central_pair m hm (r ^ 2) x
  let s := orderedHermitianEigenvalue hC ⟨m - 1, by omega⟩
  have hresult := oddCentral_abs_min_of_negative_leadingPrincipal
    m hm hB s rfl hcentral.2 hsignB
  constructor
  · rw [← hordered]
    exact hresult.1
  · intro i
    rw [← hordered, ← hordered]
    exact hresult.2 i

/-- Even-dimensional even-gap half of `lem:middle-branch`, obtained by
combining the exact inertia signs with the positive reflected
perturbation. -/
theorem evenSignedMiddleMatrix_central_abs_min_even_gap
    (m j : ℕ) (hm : 0 < m) (hj : 0 < j) (hjn : j < 2 * m)
    (hjEven : Even j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m) r ⟨j - 1, by omega⟩) :
    let hA : (signedMiddleMatrix (2 * m) (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m) (r ^ 2) x)
    0 < orderedHermitianEigenvalue hA ⟨m - 1, by omega⟩ ∧
      ∀ i : Fin (2 * m),
        |orderedHermitianEigenvalue hA ⟨m - 1, by omega⟩| ≤
          |orderedHermitianEigenvalue hA i| := by
  dsimp only
  let hA : (signedMiddleMatrix (2 * m) (r ^ 2) x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm (2 * m) (r ^ 2) x)
  let hB : (evenReflectedSignedMiddleMatrix m (r ^ 2) x).IsHermitian :=
    evenReflectedSignedMiddleMatrix_isHermitian m hm (sq_nonneg r) x
  have hsign := evenSignedMiddleMatrix_ordered_signs_even_gap
    m j hm hj hjn hjEven hr hxLower hxUpper
  exact evenCentral_abs_min_of_reflection_psd m hm hA hB
    (evenReflectedSignedMiddleMatrix_sub_posSemidef
      m hm (sq_nonneg r) x)
    (evenReflectedSignedMiddleMatrix_ordered_reflection
      m hm (sq_nonneg r) x)
    hsign.1 hsign.2

/-- Even-dimensional odd-gap half of `lem:middle-branch` for `m≥2`,
using the exact rank-two interlacing shift. -/
theorem evenSignedMiddleMatrix_central_abs_min_odd_gap
    (m j : ℕ) (hm : 2 ≤ m) (hj : 0 < j) (hjn : j < 2 * m)
    (hjOdd : Odd j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m) r ⟨j - 1, by omega⟩) :
    let hA : (signedMiddleMatrix (2 * m) (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m) (r ^ 2) x)
    orderedHermitianEigenvalue hA ⟨m - 1, by omega⟩ < 0 ∧
      ∀ i : Fin (2 * m),
        |orderedHermitianEigenvalue hA ⟨m - 1, by omega⟩| ≤
          |orderedHermitianEigenvalue hA i| := by
  dsimp only
  let hA : (signedMiddleMatrix (2 * m) (r ^ 2) x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm (2 * m) (r ^ 2) x)
  let hB : (evenReflectedSignedMiddleMatrix m (r ^ 2) x).IsHermitian :=
    evenReflectedSignedMiddleMatrix_isHermitian m (by omega) (sq_nonneg r) x
  have hsign := evenSignedMiddleMatrix_ordered_signs_odd_gap
    m j hm hj hjn hjOdd hr hxLower hxUpper
  exact evenCentral_abs_min_of_reflection_psd_rank_two m hm hA hB
    (evenReflectedSignedMiddleMatrix_sub_posSemidef
      m (by omega) (sq_nonneg r) x)
    (evenReflectedSignedMiddleMatrix_sub_rank_le_two
      m (by omega) (r ^ 2) x)
    (evenReflectedSignedMiddleMatrix_ordered_reflection
      m (by omega) (sq_nonneg r) x)
    hsign.1 hsign.2

/-- Exceptional `n=2` odd-gap half of `lem:middle-branch`. -/
theorem twoSignedMiddleMatrix_central_abs_min_odd_gap
    (j : ℕ) (hj : 0 < j) (hjn : j < 2) (hjOdd : Odd j)
    {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue 2 r ⟨j, hjn⟩ < x)
    (hxUpper : x < symmetricPathEigenvalue 2 r ⟨j - 1, by omega⟩) :
    let hA : (signedMiddleMatrix 2 (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm 2 (r ^ 2) x)
    orderedHermitianEigenvalue hA 0 < 0 ∧
      ∀ i : Fin 2,
        |orderedHermitianEigenvalue hA 0| ≤
          |orderedHermitianEigenvalue hA i| := by
  dsimp only
  let hA : (signedMiddleMatrix 2 (r ^ 2) x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm 2 (r ^ 2) x)
  have htop := twoSignedMiddleMatrix_ordered_top_neg_odd_gap
    j hj hjn hjOdd hr hxLower hxUpper
  exact ⟨htop, twoByTwo_top_abs_min_of_negative hA htop⟩

end

end ConnectedPseudospectrum
