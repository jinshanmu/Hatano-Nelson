import ConnectedPseudospectrum.HermitianSingularValues
import Mathlib.Data.Nat.Count
import Mathlib.LinearAlgebra.Matrix.Orthogonal

/-!
# Congruence and inertia of the middle signed branch

This module formalizes `eq:B-congruence` and `eq:middle-inertia` from the
proof of `lem:middle-branch`.  The inertia count is certified by an explicit
invertible real congruence to a diagonal matrix; no unproved appeal to
Sylvester's law is made.
-/

namespace ConnectedPseudospectrum

open Matrix

noncomputable section

/-- The inverse gauge followed by reversal can be moved through reversal at
the scalar cost `r⁻⁽ⁿ⁻¹⁾`. -/
theorem diagonalGaugeInv_mul_reversal (n : ℕ) (hn : 0 < n) {r : ℝ}
    (hr : r ≠ 0) :
    diagonalGaugeInv n r * reversal n =
      (r⁻¹) ^ (n - 1) • (reversal n * diagonalGauge n r) := by
  ext i j
  simp only [diagonalGaugeInv, diagonalGauge, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Matrix.smul_apply, reversal_apply, smul_eq_mul]
  by_cases hij : i.1 + j.1 + 1 = n
  · rw [if_pos hij]
    simp only [mul_one]
    have hexp : i.1 + j.1 = n - 1 := by omega
    rw [← hexp, pow_add]
    symm
    calc
      (r⁻¹) ^ i.1 * (r⁻¹) ^ j.1 * (1 * r ^ j.1) =
          (r⁻¹) ^ i.1 * ((r⁻¹) ^ j.1 * r ^ j.1) := by ring
      _ = (r⁻¹) ^ i.1 * ((r⁻¹ * r) ^ j.1) := by rw [mul_pow]
      _ = (r⁻¹) ^ i.1 := by simp [hr]
  · simp [hij]

/-- Exact real congruence `eq:B-congruence`, with the paper's parameter
written as `a=r²`. -/
theorem signedMiddleMatrix_gauge_congruence (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : r ≠ 0) (x : ℝ) :
    signedMiddleMatrix n (r ^ 2) x =
      (r⁻¹) ^ (n - 1) •
        (diagonalGauge n r * (x • 1 - symmetricPath n r) * reversal n *
          diagonalGauge n r) := by
  let G := diagonalGauge n r
  let Gi := diagonalGaugeInv n r
  let S := symmetricPath n r
  let J := reversal n
  have hfactor :
      x • (1 : Matrix (Fin n) (Fin n) ℝ) - G * S * Gi =
        G * (x • 1 - S) * Gi := by
    dsimp only [G, Gi, S]
    rw [Matrix.mul_sub, Matrix.sub_mul]
    simp [Matrix.mul_assoc, diagonalGauge_mul_inv n hr]
  calc
    signedMiddleMatrix n (r ^ 2) x =
        (x • 1 - G * S * Gi) * J := by
      rw [signedMiddleMatrix,
        pathMatrix_eq_gauge_symmetricPath_mul_inv n hr]
    _ = (G * (x • 1 - S) * Gi) * J := by rw [hfactor]
    _ = (G * (x • 1 - S)) * (Gi * J) := by
      simp only [Matrix.mul_assoc]
    _ = (G * (x • 1 - S)) *
        ((r⁻¹) ^ (n - 1) • (J * G)) := by
      rw [diagonalGaugeInv_mul_reversal n hn hr]
    _ = (r⁻¹) ^ (n - 1) • (G * (x • 1 - S) * J * G) := by
      simp [Matrix.mul_assoc]

/-- `eq:B-congruence` in the paper's variables `r=√a`. -/
theorem signedMiddleMatrix_pathRate_congruence (n : ℕ) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    signedMiddleMatrix n a x =
      ((pathRate a)⁻¹) ^ (n - 1) •
        (diagonalGauge n (pathRate a) *
          (x • 1 - symmetricPath n (pathRate a)) * reversal n *
            diagonalGauge n (pathRate a)) := by
  have hr : 0 < pathRate a := Real.sqrt_pos.2 ha
  have hsquare : pathRate a ^ 2 = a := Real.sq_sqrt ha.le
  calc
    signedMiddleMatrix n a x =
        signedMiddleMatrix n (pathRate a ^ 2) x := by rw [hsquare]
    _ = ((pathRate a)⁻¹) ^ (n - 1) •
        (diagonalGauge n (pathRate a) *
          (x • 1 - symmetricPath n (pathRate a)) * reversal n *
            diagonalGauge n (pathRate a)) :=
      signedMiddleMatrix_gauge_congruence n hn hr.ne' x

/-- A Dirichlet sine eigenvector has the reversal sign stated in
`lem:middle-branch`.  The zero-based Lean index `k` corresponds to the
paper's one-based index `k+1`, so the sign is `(-1)^k`. -/
theorem reversal_mulVec_pathSineVector (n : ℕ) (k : Fin n) :
    reversal n *ᵥ pathSineVector n k =
      (-1 : ℝ) ^ k.1 • pathSineVector n k := by
  funext i
  rw [reversal_mulVec_apply]
  simp only [pathSineVector, Pi.smul_apply, smul_eq_mul]
  have hindex : i.rev.1 + 1 + (i.1 + 1) = n + 1 := by
    simp only [Fin.val_rev]
    omega
  have hangle :
      (((i.rev.1 + 1 : ℕ) : ℝ) * pathEigenangle n k) =
        ((k.1 + 1 : ℕ) : ℝ) * Real.pi -
          (((i.1 + 1 : ℕ) : ℝ) * pathEigenangle n k) := by
    have hcast :
        (((i.rev.1 + 1 : ℕ) : ℝ) + ((i.1 + 1 : ℕ) : ℝ)) =
          ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast hindex
    rw [← pathEigenangle_endpoint n k]
    linear_combination hcast * pathEigenangle n k
  rw [hangle, Real.sin_nat_mul_pi_sub]
  rw [pow_succ]
  ring

/-- The diagonal entries obtained by simultaneously diagonalizing the
symmetric path and reversal in the Dirichlet sine basis. -/
def middleDiagonalWeight (n : ℕ) (r x : ℝ) (k : Fin n) : ℝ :=
  (-1 : ℝ) ^ k.1 * (x - symmetricPathEigenvalue n r k)

/-- The symmetric core in `eq:B-congruence`. -/
def middleSymmetricCore (n : ℕ) (r x : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (x • 1 - symmetricPath n r) * reversal n

/-- Each sine vector is an eigenvector of the symmetric middle core with
the signed eigenvalue appearing in the paper's inertia calculation. -/
theorem middleSymmetricCore_mulVec_pathSineVector (n : ℕ) (r x : ℝ)
    (k : Fin n) :
    middleSymmetricCore n r x *ᵥ pathSineVector n k =
      middleDiagonalWeight n r x k • pathSineVector n k := by
  rw [middleSymmetricCore, ← Matrix.mulVec_mulVec,
    reversal_mulVec_pathSineVector, Matrix.mulVec_smul,
    Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    symmetricPath_mulVec_pathSineVector]
  ext i
  simp [middleDiagonalWeight, smul_eq_mul]
  ring

/-- The matrix whose `k`-th column is the `k`-th Dirichlet sine vector. -/
def pathSineMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i k => pathSineVector n k i

@[simp] theorem pathSineMatrix_col (n : ℕ) (k : Fin n) :
    (pathSineMatrix n).col k = pathSineVector n k :=
  rfl

/-- The symmetric path is a real symmetric matrix. -/
theorem symmetricPath_isSymm (n : ℕ) (r : ℝ) :
    (symmetricPath n r).IsSymm := by
  rw [Matrix.IsSymm]
  simp [symmetricPath, lowerShift, add_comm]

/-- The ungauged sine vectors are linearly independent when `r>0`. -/
theorem pathSineVector_linearIndependent (n : ℕ) {r : ℝ} (hr : 0 < r) :
    LinearIndependent ℝ (pathSineVector n) := by
  apply Module.End.eigenvectors_linearIndependent'
    (symmetricPath n r).toLin' (symmetricPathEigenvalue n r)
    (symmetricPathEigenvalue_injective n hr) (pathSineVector n)
  intro k
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact symmetricPath_mulVec_pathSineVector n r k
  · exact pathSineVector_ne_zero n k

/-- The sine matrix is invertible.  This is the explicit change of basis
used in the inertia certificate below. -/
theorem pathSineMatrix_isUnit (n : ℕ) {r : ℝ} (hr : 0 < r) :
    IsUnit (pathSineMatrix n) := by
  apply Matrix.linearIndependent_cols_iff_isUnit.mp
  simpa only [pathSineMatrix_col] using pathSineVector_linearIndependent n hr

/-- Distinct Dirichlet sine vectors are orthogonal for the ordinary real dot
product. -/
theorem pathSineVector_dotProduct_eq_zero (n : ℕ) {r : ℝ} (hr : 0 < r)
    {i j : Fin n} (hij : i ≠ j) :
    pathSineVector n i ⬝ᵥ pathSineVector n j = 0 := by
  let H := symmetricPath n r
  let vi := pathSineVector n i
  let vj := pathSineVector n j
  have hHt : Hᵀ = H := (symmetricPath_isSymm n r).eq
  have hadjoint : vi ⬝ᵥ (H *ᵥ vj) = (H *ᵥ vi) ⬝ᵥ vj := by
    rw [dotProduct_mulVec]
    rw [← hHt]
    rw [vecMul_transpose]
    rw [hHt]
  have hscalar :
      symmetricPathEigenvalue n r j * (vi ⬝ᵥ vj) =
        symmetricPathEigenvalue n r i * (vi ⬝ᵥ vj) := by
    rw [show H *ᵥ vj = symmetricPathEigenvalue n r j • vj from
        symmetricPath_mulVec_pathSineVector n r j,
      show H *ᵥ vi = symmetricPathEigenvalue n r i • vi from
        symmetricPath_mulVec_pathSineVector n r i] at hadjoint
    simpa only [dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_comm] using hadjoint
  have hvalues :
      symmetricPathEigenvalue n r j ≠ symmetricPathEigenvalue n r i := by
    exact (symmetricPathEigenvalue_injective n hr).ne (Ne.symm hij)
  rcases mul_eq_zero.mp
      (show (symmetricPathEigenvalue n r j - symmetricPathEigenvalue n r i) *
          (vi ⬝ᵥ vj) = 0 by nlinarith) with hvalue | hdot
  · exact False.elim (hvalues (sub_eq_zero.mp hvalue))
  · exact hdot

/-- Squared Euclidean length of a Dirichlet sine vector. -/
def pathSineNormSq (n : ℕ) (k : Fin n) : ℝ :=
  pathSineVector n k ⬝ᵥ pathSineVector n k

/-- Every sine-vector squared length is strictly positive. -/
theorem pathSineNormSq_pos (n : ℕ) (k : Fin n) :
    0 < pathSineNormSq n k := by
  have hnonneg : 0 ≤ pathSineNormSq n k := by
    unfold pathSineNormSq dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hne : pathSineNormSq n k ≠ 0 := by
    intro hzero
    apply pathSineVector_ne_zero n k
    exact dotProduct_self_eq_zero.mp hzero
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The Gram matrix of the sine basis is diagonal. -/
theorem pathSineMatrix_transpose_mul_self (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (pathSineMatrix n)ᵀ * pathSineMatrix n =
      diagonal (pathSineNormSq n) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pathSineMatrix,
    Matrix.diagonal_apply, pathSineNormSq, dotProduct]
  by_cases hij : i = j
  · subst j
    simp
  · rw [if_neg hij]
    exact pathSineVector_dotProduct_eq_zero n hr hij

/-- Matrix form of the simultaneous sine-basis diagonalization. -/
theorem middleSymmetricCore_mul_pathSineMatrix (n : ℕ) (r x : ℝ) :
    middleSymmetricCore n r x * pathSineMatrix n =
      pathSineMatrix n * diagonal (middleDiagonalWeight n r x) := by
  ext i k
  rw [Matrix.mul_diagonal]
  change
    (middleSymmetricCore n r x *ᵥ pathSineVector n k) i =
      pathSineVector n k i * middleDiagonalWeight n r x k
  rw [middleSymmetricCore_mulVec_pathSineVector]
  simp [smul_eq_mul, mul_comm]

/-- Congruence of the symmetric core to a diagonal matrix.  The positive
factor `pathSineNormSq` is retained explicitly rather than silently
normalizing the sine vectors. -/
theorem pathSineMatrix_congruence_middleSymmetricCore
    (n : ℕ) {r : ℝ} (hr : 0 < r) (x : ℝ) :
    (pathSineMatrix n)ᵀ * middleSymmetricCore n r x * pathSineMatrix n =
      diagonal fun k => pathSineNormSq n k * middleDiagonalWeight n r x k := by
  rw [Matrix.mul_assoc, middleSymmetricCore_mul_pathSineMatrix]
  rw [← Matrix.mul_assoc, pathSineMatrix_transpose_mul_self n hr]
  rw [Matrix.diagonal_mul_diagonal]

/-- The explicit congruence matrix: inverse diagonal gauge followed by the
Dirichlet sine change of basis. -/
def middleCongruenceMatrix (n : ℕ) (r : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  diagonalGaugeInv n r * pathSineMatrix n

/-- The diagonal weights in the full signed-middle congruence. -/
def middleInertiaWeight (n : ℕ) (r x : ℝ) (k : Fin n) : ℝ :=
  (r⁻¹) ^ (n - 1) * pathSineNormSq n k *
    middleDiagonalWeight n r x k

@[simp] theorem diagonalGaugeInv_transpose (n : ℕ) (r : ℝ) :
    (diagonalGaugeInv n r)ᵀ = diagonalGaugeInv n r := by
  simp [diagonalGaugeInv]

/-- The change of basis in the inertia certificate is invertible. -/
theorem middleCongruenceMatrix_isUnit (n : ℕ) {r : ℝ} (hr : 0 < r) :
    IsUnit (middleCongruenceMatrix n r) := by
  apply IsUnit.mul
  · apply isUnit_iff_exists_inv.mpr
    exact ⟨diagonalGauge n r, diagonalGaugeInv_mul n hr.ne'⟩
  · exact pathSineMatrix_isUnit n hr

/-- Explicit invertible diagonal congruence for the actual real signed
matrix `Bₙ(x)`.  This is a kernel-checked inertia certificate. -/
theorem middleCongruenceMatrix_transpose_mul_signedMiddleMatrix_mul
    (n : ℕ) (hn : 0 < n) {r : ℝ} (hr : 0 < r) (x : ℝ) :
    (middleCongruenceMatrix n r)ᵀ * signedMiddleMatrix n (r ^ 2) x *
        middleCongruenceMatrix n r =
      diagonal (middleInertiaWeight n r x) := by
  let G := diagonalGauge n r
  let Gi := diagonalGaugeInv n r
  let Q := pathSineMatrix n
  let C := middleSymmetricCore n r x
  let c := (r⁻¹) ^ (n - 1)
  have hGiG : Gi * G = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    exact diagonalGaugeInv_mul n hr.ne'
  have hGGi : G * Gi = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    exact diagonalGauge_mul_inv n hr.ne'
  have hB : signedMiddleMatrix n (r ^ 2) x = c • (G * C * G) := by
    rw [signedMiddleMatrix_gauge_congruence n hn hr.ne' x]
    change c • (G * (x • 1 - symmetricPath n r) * reversal n * G) =
      c • (G * C * G)
    congr 1
    dsimp only [C, middleSymmetricCore]
    noncomm_ring
  have hcore : Qᵀ * C * Q =
      diagonal fun k => pathSineNormSq n k * middleDiagonalWeight n r x k := by
    exact pathSineMatrix_congruence_middleSymmetricCore n hr x
  change (Gi * Q)ᵀ * signedMiddleMatrix n (r ^ 2) x * (Gi * Q) = _
  rw [Matrix.transpose_mul, diagonalGaugeInv_transpose, hB]
  calc
    (Qᵀ * Gi) * (c • (G * C * G)) * (Gi * Q) =
        c • (((Qᵀ * Gi) * (G * C * G)) * (Gi * Q)) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = c • (Qᵀ * (Gi * G) * C * (G * Gi) * Q) := by
      congr 1
      noncomm_ring
    _ = c • (Qᵀ * C * Q) := by
      rw [hGiG, hGGi]
      simp
    _ = diagonal (middleInertiaWeight n r x) := by
      rw [hcore]
      ext i j
      by_cases hij : i = j
      · subst j
        simp [middleInertiaWeight, c]
        ring
      · simp [hij]

/-- Multiplication by the positive gauge and norm factors does not change
the sign of a middle diagonal weight. -/
theorem middleInertiaWeight_pos_iff (n : ℕ) {r : ℝ}
    (hr : 0 < r) (x : ℝ) (k : Fin n) :
    0 < middleInertiaWeight n r x k ↔
      0 < middleDiagonalWeight n r x k := by
  have hc : 0 < (r⁻¹) ^ (n - 1) := pow_pos (inv_pos.mpr hr) _
  have hnorm : 0 < pathSineNormSq n k := pathSineNormSq_pos n k
  unfold middleInertiaWeight
  exact mul_pos_iff_of_pos_left (mul_pos hc hnorm)

/-- Sign classification of the diagonal congruence weights in the `j`-th
spectral gap.  Here `j` is one-based as in the paper, while `k` is Lean's
zero-based sine-mode index. -/
theorem middleDiagonalWeight_pos_iff_of_mem_spectralGap
    (n j : ℕ) (hj : 0 < j) (hjn : j < n) {r : ℝ} (hr : 0 < r)
    {x : ℝ}
    (hxLower : symmetricPathEigenvalue n r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue n r ⟨j - 1, by omega⟩)
    (k : Fin n) :
    0 < middleDiagonalWeight n r x k ↔
      (k.1 < j ∧ Odd k.1) ∨ (j ≤ k.1 ∧ Even k.1) := by
  by_cases hkj : k.1 < j
  · have hkUpper : k ≤ (⟨j - 1, by omega⟩ : Fin n) := by
      exact Fin.mk_le_mk.mpr (by omega)
    have hxEigen : x < symmetricPathEigenvalue n r k :=
      hxUpper.trans_le
        ((symmetricPathEigenvalue_strictAnti n hr).antitone hkUpper)
    rcases Nat.even_or_odd k.1 with hkEven | hkOdd
    · have hkNotOdd : ¬ Odd k.1 := Nat.not_odd_iff_even.mpr hkEven
      have hjNotLe : ¬ j ≤ k.1 := by omega
      simp [middleDiagonalWeight, hkEven.neg_one_pow, hkj, hkNotOdd,
        hjNotLe, hxEigen.le]
    · have hkNotEven : ¬ Even k.1 := Nat.not_even_iff_odd.mpr hkOdd
      have hjNotLe : ¬ j ≤ k.1 := by omega
      simp [middleDiagonalWeight, hkOdd.neg_one_pow, hkj, hkOdd,
        hkNotEven, hjNotLe, hxEigen]
  · have hjk : (⟨j, hjn⟩ : Fin n) ≤ k := by
      exact Fin.mk_le_mk.mpr (by omega)
    have hEigenX : symmetricPathEigenvalue n r k < x :=
      lt_of_le_of_lt
        ((symmetricPathEigenvalue_strictAnti n hr).antitone hjk) hxLower
    have hjle : j ≤ k.1 := by omega
    rcases Nat.even_or_odd k.1 with hkEven | hkOdd
    · have hkNotOdd : ¬ Odd k.1 := Nat.not_odd_iff_even.mpr hkEven
      simp [middleDiagonalWeight, hkEven.neg_one_pow, hkj, hjle,
        hkEven, hkNotOdd, hEigenX]
    · have hkNotEven : ¬ Even k.1 := Nat.not_even_iff_odd.mpr hkOdd
      simp [middleDiagonalWeight, hkOdd.neg_one_pow, hkj, hjle,
        hkOdd, hkNotEven, hEigenX.le]

/-- The same gap sign classification for the diagonal entries of the full
congruence certificate. -/
theorem middleInertiaWeight_pos_iff_of_mem_spectralGap
    (n j : ℕ) (hj : 0 < j) (hjn : j < n) {r : ℝ} (hr : 0 < r)
    {x : ℝ}
    (hxLower : symmetricPathEigenvalue n r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue n r ⟨j - 1, by omega⟩)
    (k : Fin n) :
    0 < middleInertiaWeight n r x k ↔
      (k.1 < j ∧ Odd k.1) ∨ (j ≤ k.1 ∧ Even k.1) := by
  rw [middleInertiaWeight_pos_iff n hr]
  exact middleDiagonalWeight_pos_iff_of_mem_spectralGap
    n j hj hjn hr hxLower hxUpper k

/-- Number of positive entries in the actual diagonal matrix supplied by
the signed-middle congruence.  The existential packages the proof that the
natural-number index lies in `Fin n`; proof irrelevance makes the count
independent of that package. -/
def middlePositiveInertiaCount (n : ℕ) (r x : ℝ) : ℕ :=
  Nat.count
    (fun p ↦ ∃ hp : p < n,
      0 < middleInertiaWeight n r x ⟨p, hp⟩) n

/-- Pure parity count equivalent to the paper's positive-inertia count in
the `j`-th gap. -/
def middlePositiveSignCount (n j : ℕ) : ℕ :=
  Nat.count
    (fun k ↦ (k < j ∧ Odd k) ∨ (j ≤ k ∧ Even k)) n

private theorem nat_count_congr_of_lt {p q : ℕ → Prop}
    [DecidablePred p] [DecidablePred q] {n : ℕ}
    (h : ∀ k < n, p k ↔ q k) :
    Nat.count p n = Nat.count q n := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  exact and_congr_right fun hk ↦ h k hk

/-- Among `0,…,n-1`, the even and odd counts are respectively the ceiling
and floor of `n/2`. -/
theorem count_even_and_odd (n : ℕ) :
    Nat.count Even n = (n + 1) / 2 ∧ Nat.count Odd n = n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.count_succ, Nat.count_succ, ih.1, ih.2]
      rcases Nat.even_or_odd n with hnEven | hnOdd
      · rw [if_pos hnEven,
          if_neg (Nat.not_odd_iff_even.mpr hnEven)]
        rcases hnEven with ⟨q, hq⟩
        omega
      · rw [if_neg (Nat.not_even_iff_odd.mpr hnOdd), if_pos hnOdd]
        rcases hnOdd with ⟨q, hq⟩
        omega

private theorem middlePositiveSignCount_eq_of_even_index
    (n j : ℕ) (hjn : j ≤ n) (hjEven : Even j) :
    middlePositiveSignCount n j =
      j / 2 + (n - j + 1) / 2 := by
  let p : ℕ → Prop :=
    fun k ↦ (k < j ∧ Odd k) ∨ (j ≤ k ∧ Even k)
  have hnSplit : n = j + (n - j) := by omega
  have hFirst : Nat.count p j = Nat.count Odd j := by
    apply nat_count_congr_of_lt
    intro k hk
    dsimp only [p]
    constructor
    · rintro (⟨_, hkOdd⟩ | ⟨hjk, _⟩)
      · exact hkOdd
      · omega
    · intro hkOdd
      exact Or.inl ⟨hk, hkOdd⟩
  have hTail :
      Nat.count (fun k ↦ p (j + k)) (n - j) =
        Nat.count Even (n - j) := by
    apply nat_count_congr_of_lt
    intro k _
    dsimp only [p]
    have hjk : j ≤ j + k := Nat.le_add_right j k
    have hnot : ¬ j + k < j := by omega
    simp only [hnot, false_and, hjk, true_and, false_or]
    simp only [Nat.even_add, hjEven, true_iff]
  unfold middlePositiveSignCount
  change Nat.count p n = _
  calc
    Nat.count p n = Nat.count p (j + (n - j)) :=
      congrArg (Nat.count p) hnSplit
    _ = _ := by
      rw [Nat.count_add, hFirst, hTail,
        (count_even_and_odd j).2, (count_even_and_odd (n - j)).1]

private theorem middlePositiveSignCount_eq_of_odd_index
    (n j : ℕ) (hjn : j ≤ n) (hjOdd : Odd j) :
    middlePositiveSignCount n j =
      j / 2 + (n - j) / 2 := by
  let p : ℕ → Prop :=
    fun k ↦ (k < j ∧ Odd k) ∨ (j ≤ k ∧ Even k)
  have hnSplit : n = j + (n - j) := by omega
  have hFirst : Nat.count p j = Nat.count Odd j := by
    apply nat_count_congr_of_lt
    intro k hk
    dsimp only [p]
    constructor
    · rintro (⟨_, hkOdd⟩ | ⟨hjk, _⟩)
      · exact hkOdd
      · omega
    · intro hkOdd
      exact Or.inl ⟨hk, hkOdd⟩
  have hjNotEven : ¬ Even j := Nat.not_even_iff_odd.mpr hjOdd
  have hTail :
      Nat.count (fun k ↦ p (j + k)) (n - j) =
        Nat.count Odd (n - j) := by
    apply nat_count_congr_of_lt
    intro k _
    dsimp only [p]
    have hjk : j ≤ j + k := Nat.le_add_right j k
    have hnot : ¬ j + k < j := by omega
    simp only [hnot, false_and, hjk, true_and, false_or]
    rw [Nat.even_add]
    simp only [hjNotEven, false_iff, Nat.not_even_iff_odd]
  unfold middlePositiveSignCount
  change Nat.count p n = _
  calc
    Nat.count p n = Nat.count p (j + (n - j)) :=
      congrArg (Nat.count p) hnSplit
    _ = _ := by
      rw [Nat.count_add, hFirst, hTail,
        (count_even_and_odd j).2, (count_even_and_odd (n - j)).2]

/-- For an even dimension `n=2m`, the positive inertia in an even-numbered
spectral gap is `m`. -/
theorem middlePositiveSignCount_even_dimension_even_gap
    (m j : ℕ) (hjn : j < 2 * m) (hjEven : Even j) :
    middlePositiveSignCount (2 * m) j = m := by
  rw [middlePositiveSignCount_eq_of_even_index (2 * m) j hjn.le hjEven]
  rcases hjEven with ⟨q, hq⟩
  omega

/-- For an even dimension `n=2m`, the positive inertia in an odd-numbered
spectral gap is `m-1`. -/
theorem middlePositiveSignCount_even_dimension_odd_gap
    (m j : ℕ) (hjn : j < 2 * m) (hjOdd : Odd j) :
    middlePositiveSignCount (2 * m) j = m - 1 := by
  rw [middlePositiveSignCount_eq_of_odd_index (2 * m) j hjn.le hjOdd]
  rcases hjOdd with ⟨q, hq⟩
  omega

/-- For an odd dimension `n=2m+1`, the positive inertia in an even-numbered
spectral gap is `m+1`. -/
theorem middlePositiveSignCount_odd_dimension_even_gap
    (m j : ℕ) (hjn : j < 2 * m + 1) (hjEven : Even j) :
    middlePositiveSignCount (2 * m + 1) j = m + 1 := by
  rw [middlePositiveSignCount_eq_of_even_index
    (2 * m + 1) j hjn.le hjEven]
  rcases hjEven with ⟨q, hq⟩
  omega

/-- For an odd dimension `n=2m+1`, the positive inertia in an odd-numbered
spectral gap is `m`. -/
theorem middlePositiveSignCount_odd_dimension_odd_gap
    (m j : ℕ) (hjn : j < 2 * m + 1) (hjOdd : Odd j) :
    middlePositiveSignCount (2 * m + 1) j = m := by
  rw [middlePositiveSignCount_eq_of_odd_index
    (2 * m + 1) j hjn.le hjOdd]
  rcases hjOdd with ⟨q, hq⟩
  omega

/-- In a spectral gap, the number of positive entries of the actual
congruence diagonal is exactly the parity count used in the paper. -/
theorem middlePositiveInertiaCount_eq_signCount_of_mem_spectralGap
    (n j : ℕ) (hj : 0 < j) (hjn : j < n) {r : ℝ} (hr : 0 < r)
    {x : ℝ}
    (hxLower : symmetricPathEigenvalue n r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue n r ⟨j - 1, by omega⟩) :
    middlePositiveInertiaCount n r x = middlePositiveSignCount n j := by
  unfold middlePositiveInertiaCount middlePositiveSignCount
  apply nat_count_congr_of_lt
  intro k hk
  constructor
  · rintro ⟨hk', hweight⟩
    exact (middleInertiaWeight_pos_iff_of_mem_spectralGap
      n j hj hjn hr hxLower hxUpper ⟨k, hk'⟩).mp hweight
  · intro hsign
    exact ⟨hk,
      (middleInertiaWeight_pos_iff_of_mem_spectralGap
        n j hj hjn hr hxLower hxUpper ⟨k, hk⟩).mpr hsign⟩

/-- `eq:middle-inertia`, even-dimensional/even-gap case, for the actual
diagonal congruent to `Bₙ(x)`. -/
theorem middlePositiveInertiaCount_even_dimension_even_gap
    (m j : ℕ) (hj : 0 < j) (hjn : j < 2 * m)
    (hjEven : Even j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m) r ⟨j - 1, by omega⟩) :
    middlePositiveInertiaCount (2 * m) r x = m := by
  rw [middlePositiveInertiaCount_eq_signCount_of_mem_spectralGap
    (2 * m) j hj hjn hr hxLower hxUpper]
  exact middlePositiveSignCount_even_dimension_even_gap m j hjn hjEven

/-- `eq:middle-inertia`, even-dimensional/odd-gap case. -/
theorem middlePositiveInertiaCount_even_dimension_odd_gap
    (m j : ℕ) (hj : 0 < j) (hjn : j < 2 * m)
    (hjOdd : Odd j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m) r ⟨j - 1, by omega⟩) :
    middlePositiveInertiaCount (2 * m) r x = m - 1 := by
  rw [middlePositiveInertiaCount_eq_signCount_of_mem_spectralGap
    (2 * m) j hj hjn hr hxLower hxUpper]
  exact middlePositiveSignCount_even_dimension_odd_gap m j hjn hjOdd

/-- `eq:middle-inertia`, odd-dimensional/even-gap case. -/
theorem middlePositiveInertiaCount_odd_dimension_even_gap
    (m j : ℕ) (hj : 0 < j) (hjn : j < 2 * m + 1)
    (hjEven : Even j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m + 1) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m + 1) r ⟨j - 1, by omega⟩) :
    middlePositiveInertiaCount (2 * m + 1) r x = m + 1 := by
  rw [middlePositiveInertiaCount_eq_signCount_of_mem_spectralGap
    (2 * m + 1) j hj hjn hr hxLower hxUpper]
  exact middlePositiveSignCount_odd_dimension_even_gap m j hjn hjEven

/-- `eq:middle-inertia`, odd-dimensional/odd-gap case. -/
theorem middlePositiveInertiaCount_odd_dimension_odd_gap
    (m j : ℕ) (hj : 0 < j) (hjn : j < 2 * m + 1)
    (hjOdd : Odd j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m + 1) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m + 1) r ⟨j - 1, by omega⟩) :
    middlePositiveInertiaCount (2 * m + 1) r x = m := by
  rw [middlePositiveInertiaCount_eq_signCount_of_mem_spectralGap
    (2 * m + 1) j hj hjn hr hxLower hxUpper]
  exact middlePositiveSignCount_odd_dimension_odd_gap m j hjn hjOdd


end

end ConnectedPseudospectrum
