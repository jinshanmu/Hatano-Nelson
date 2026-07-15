import ConnectedPseudospectrum.MiddleBranchBridge
import ConnectedPseudospectrum.RectangularGramBound
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# The odd central singular spectrum

This file formalizes lines 1825--1837 of the immutable source.  We write
`q = L - 1`, so the odd matrix order is `2*q+1 = 2*L-1`.  Separating the
zero-based even and odd coordinates gives rectangular blocks of sizes
`(q+1) x q` and `q x (q+1)`.  Their reduced Gram matrices are the same
Toeplitz matrix.  Its explicit characteristic polynomial gives one zero
singular-value square and each of the `q` positive displayed squares twice.
-/

namespace ConnectedPseudospectrum

open Matrix Polynomial
open scoped ComplexConjugate ComplexOrder Matrix

local postfix:1024 "ᴴ" => Matrix.conjTranspose
local infixr:73 " *ᵥ " => Matrix.mulVec

noncomputable section

/-! ## The odd/even coordinate permutation -/

private def oddCentralParityMap (q : ℕ) :
    Fin (q + 1) ⊕ Fin q → Fin (2 * q + 1)
  | Sum.inl i => ⟨2 * i.1, by omega⟩
  | Sum.inr i => ⟨2 * i.1 + 1, by omega⟩

private theorem oddCentralParityMap_bijective (q : ℕ) :
    Function.Bijective (oddCentralParityMap q) := by
  constructor
  · intro i j hij
    have hval := congrArg Fin.val hij
    rcases i with i | i <;> rcases j with j | j
    · apply congrArg Sum.inl
      apply Fin.ext
      simp only [oddCentralParityMap] at hval
      omega
    · simp only [oddCentralParityMap] at hval
      omega
    · simp only [oddCentralParityMap] at hval
      omega
    · apply congrArg Sum.inr
      apply Fin.ext
      simp only [oddCentralParityMap] at hval
      omega
  · intro k
    obtain ⟨i, hi | hi⟩ := Nat.even_or_odd' k.1
    · have hiq : i < q + 1 := by omega
      refine ⟨Sum.inl ⟨i, hiq⟩, ?_⟩
      apply Fin.ext
      simp only [oddCentralParityMap]
      omega
    · have hiq : i < q := by omega
      refine ⟨Sum.inr ⟨i, hiq⟩, ?_⟩
      apply Fin.ext
      simp only [oddCentralParityMap]
      omega

/-- Parity ordering for an odd path: the left block consists of original
coordinates `2i`, and the right block of original coordinates `2i+1`. -/
def oddCentralParityBlockEquiv (q : ℕ) :
    Fin (q + 1) ⊕ Fin q ≃ Fin (2 * q + 1) :=
  Equiv.ofBijective (oddCentralParityMap q)
    (oddCentralParityMap_bijective q)

/-- The ordinary contiguous ordering of the two unequal blocks. -/
def oddCentralTwoBlockEquiv (q : ℕ) :
    Fin (q + 1) ⊕ Fin q ≃ Fin (2 * q + 1) :=
  (@finSumFinEquiv (q + 1) q).trans (finCongr (by omega))

@[simp] theorem oddCentralParityBlockEquiv_inl_val
    (q : ℕ) (i : Fin (q + 1)) :
    (oddCentralParityBlockEquiv q (Sum.inl i)).1 = 2 * i.1 := by
  rfl

@[simp] theorem oddCentralParityBlockEquiv_inr_val
    (q : ℕ) (i : Fin q) :
    (oddCentralParityBlockEquiv q (Sum.inr i)).1 = 2 * i.1 + 1 := by
  rfl

/-- The permutation from contiguous block coordinates to parity coordinates. -/
def oddCentralParityPermutation (q : ℕ) : Equiv.Perm (Fin (2 * q + 1)) :=
  (oddCentralTwoBlockEquiv q).symm.trans (oddCentralParityBlockEquiv q)

/-! ## Rectangular blocks and their Toeplitz Grams -/

/-- The `(q+1) x q` upper-right block after parity separation. -/
def oddCentralUpperBlock (q : ℕ) (a : ℝ) :
    Matrix (Fin (q + 1)) (Fin q) ℂ :=
  padLastMatrix q + (a : ℂ) • padFirstMatrix q

/-- The `q x (q+1)` lower-left block after parity separation. -/
def oddCentralLowerBlock (q : ℕ) (a : ℝ) :
    Matrix (Fin q) (Fin (q + 1)) ℂ :=
  (padFirstMatrix q + (a : ℂ) • padLastMatrix q)ᴴ

@[simp] theorem oddCentralUpperBlock_apply (q : ℕ) (a : ℝ)
    (i : Fin (q + 1)) (j : Fin q) :
    oddCentralUpperBlock q a i j =
      (if i.1 = j.1 then 1 else 0) +
        (a : ℂ) * (if i.1 = j.1 + 1 then 1 else 0) := by
  have hcast : i = Fin.castSucc j ↔ i.1 = j.1 := by
    constructor
    · intro h
      simpa only [Fin.val_castSucc] using congrArg Fin.val h
    · intro h
      apply Fin.ext
      simpa only [Fin.val_castSucc] using h
  have hsucc : i = Fin.succ j ↔ i.1 = j.1 + 1 := by
    constructor
    · intro h
      simpa only [Fin.val_succ] using congrArg Fin.val h
    · intro h
      apply Fin.ext
      simpa only [Fin.val_succ] using h
  simp [oddCentralUpperBlock, hcast, hsucc]

@[simp] theorem oddCentralLowerBlock_apply (q : ℕ) (a : ℝ)
    (i : Fin q) (j : Fin (q + 1)) :
    oddCentralLowerBlock q a i j =
      (if j.1 = i.1 + 1 then 1 else 0) +
        (a : ℂ) * (if j.1 = i.1 then 1 else 0) := by
  have hsucc : j = Fin.succ i ↔ j.1 = i.1 + 1 := by
    constructor
    · intro h
      simpa only [Fin.val_succ] using congrArg Fin.val h
    · intro h
      apply Fin.ext
      simpa only [Fin.val_succ] using h
  have hcast : j = Fin.castSucc i ↔ j.1 = i.1 := by
    constructor
    · intro h
      simpa only [Fin.val_castSucc] using congrArg Fin.val h
    · intro h
      apply Fin.ext
      simpa only [Fin.val_castSucc] using h
  simp [oddCentralLowerBlock, hsucc, hcast]
  split_ifs <;> simp

/-- The parity-separated odd path matrix. -/
def oddCentralOffDiagonal (q : ℕ) (a : ℝ) :
    Matrix (Fin (q + 1) ⊕ Fin q) (Fin (q + 1) ⊕ Fin q) ℂ :=
  Matrix.fromBlocks 0 (oddCentralUpperBlock q a)
    (oddCentralLowerBlock q a) 0

/-- The same block matrix on the ordinary `Fin (2*q+1)` coordinate type. -/
def oddCentralOffDiagonalFin (q : ℕ) (a : ℝ) :
    Matrix (Fin (2 * q + 1)) (Fin (2 * q + 1)) ℂ :=
  (oddCentralOffDiagonal q a).submatrix
    (oddCentralTwoBlockEquiv q).symm (oddCentralTwoBlockEquiv q).symm

/-- Odd/even coordinates give the asserted rectangular block form at `x=0`. -/
theorem complexPathMatrix_oddCentral_parityBlock (q : ℕ) (a : ℝ) :
    (complexPathMatrix (2 * q + 1) a).submatrix
        (oddCentralParityBlockEquiv q) (oddCentralParityBlockEquiv q) =
      oddCentralOffDiagonal q a := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Matrix.submatrix_apply, complexPathMatrix_apply,
      pathMatrix_apply, oddCentralParityBlockEquiv_inl_val,
      oddCentralOffDiagonal, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
    push_cast
    split_ifs <;> (first | omega | norm_num)
  · simp only [Matrix.submatrix_apply, complexPathMatrix_apply,
      pathMatrix_apply, oddCentralParityBlockEquiv_inl_val,
      oddCentralParityBlockEquiv_inr_val, oddCentralOffDiagonal,
      Matrix.fromBlocks_apply₁₂, oddCentralUpperBlock_apply]
    push_cast
    split_ifs <;> (first | omega | norm_num)
  · simp only [Matrix.submatrix_apply, complexPathMatrix_apply,
      pathMatrix_apply, oddCentralParityBlockEquiv_inr_val,
      oddCentralParityBlockEquiv_inl_val, oddCentralOffDiagonal,
      Matrix.fromBlocks_apply₂₁, oddCentralLowerBlock_apply]
    push_cast
    split_ifs <;> (first | omega | norm_num)
  · simp only [Matrix.submatrix_apply, complexPathMatrix_apply,
      pathMatrix_apply, oddCentralParityBlockEquiv_inr_val,
      oddCentralOffDiagonal, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
    push_cast
    split_ifs <;> (first | omega | norm_num)

/-- In ordinary coordinates, parity separation is a literal simultaneous
row-and-column permutation to the displayed block matrix. -/
theorem complexPathMatrix_oddCentral_parityPermutation (q : ℕ) (a : ℝ) :
    (complexPathMatrix (2 * q + 1) a).submatrix
        (oddCentralParityPermutation q) (oddCentralParityPermutation q) =
      oddCentralOffDiagonalFin q a := by
  have hblock := complexPathMatrix_oddCentral_parityBlock q a
  ext i j
  have hij := congrArg
    (fun M : Matrix (Fin (q + 1) ⊕ Fin q) (Fin (q + 1) ⊕ Fin q) ℂ ↦
      M ((oddCentralTwoBlockEquiv q).symm i)
        ((oddCentralTwoBlockEquiv q).symm j)) hblock
  simpa [oddCentralOffDiagonalFin, oddCentralParityPermutation,
    Matrix.submatrix_apply] using hij

/-- The common `q`-dimensional Toeplitz Gram matrix: diagonal `1+a²`,
off-diagonal `a`. -/
def oddCentralGramToeplitz (q : ℕ) (a : ℝ) :
    Matrix (Fin q) (Fin q) ℂ :=
  (((1 + a ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ) +
    (a : ℂ) • complexUpperShift q) +
      (a : ℂ) • complexLowerShift q

theorem oddCentralUpperBlock_eq_rectangularC (q : ℕ) (a : ℝ) :
    oddCentralUpperBlock q a = -rectangularC q (-(a : ℂ)) := by
  ext i j
  simp [oddCentralUpperBlock, rectangularC]

theorem oddCentralLowerBlock_eq_rectangularD_star (q : ℕ) (a : ℝ) :
    oddCentralLowerBlock q a = (rectangularD q (-(a : ℂ)))ᴴ := by
  simp [oddCentralLowerBlock, rectangularD]

theorem oddCentralGramToeplitz_eq_scalar_add_path (q : ℕ) (a : ℝ) :
    oddCentralGramToeplitz q a =
      ((1 + a ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ) +
        complexSymmetricPath q a := by
  rw [oddCentralGramToeplitz, complexSymmetricPath_eq_shifts]
  push_cast
  rw [smul_add]
  abel

/-- Gram identity for the upper rectangular block. -/
theorem oddCentralUpperBlock_gram (q : ℕ) (a : ℝ) :
    (oddCentralUpperBlock q a)ᴴ * oddCentralUpperBlock q a =
      oddCentralGramToeplitz q a := by
  calc
    (oddCentralUpperBlock q a)ᴴ * oddCentralUpperBlock q a =
        (rectangularC q (-(a : ℂ)))ᴴ *
          rectangularC q (-(a : ℂ)) := by
      rw [oddCentralUpperBlock_eq_rectangularC]
      simp
    _ = oddCentralGramToeplitz q a := by
      rw [rectangularC_gram]
      unfold oddCentralGramToeplitz
      simp only [map_neg, Complex.conj_ofReal]
      push_cast
      module

/-- Reduced Gram identity for the lower rectangular block. -/
theorem oddCentralLowerBlock_gram (q : ℕ) (a : ℝ) :
    oddCentralLowerBlock q a * (oddCentralLowerBlock q a)ᴴ =
      oddCentralGramToeplitz q a := by
  calc
    oddCentralLowerBlock q a * (oddCentralLowerBlock q a)ᴴ =
        (rectangularD q (-(a : ℂ)))ᴴ *
          rectangularD q (-(a : ℂ)) := by
      rw [oddCentralLowerBlock_eq_rectangularD_star]
      simp
    _ = oddCentralGramToeplitz q a := by
      rw [rectangularD_gram]
      unfold oddCentralGramToeplitz
      simp only [map_neg, Complex.conj_ofReal]
      push_cast
      module

/-- The full Gram is block diagonal; the larger block has one additional
null direction. -/
theorem oddCentralOffDiagonal_gram (q : ℕ) (a : ℝ) :
    (oddCentralOffDiagonal q a)ᴴ * oddCentralOffDiagonal q a =
      Matrix.fromBlocks
        ((oddCentralLowerBlock q a)ᴴ * oddCentralLowerBlock q a) 0 0
        ((oddCentralUpperBlock q a)ᴴ * oddCentralUpperBlock q a) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [oddCentralOffDiagonal, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply]

/-! ## Exact singular-value squares -/

/-- The square indexed by zero-based `k`; in the paper its index is `k+1`
and `L=q+1`. -/
def oddCentralSingularSquare (q : ℕ) (a : ℝ) (k : Fin q) : ℝ :=
  1 + a ^ 2 + symmetricPathEigenvalue q a k

theorem oddCentralSingularSquare_eq (q : ℕ) (a : ℝ) (k : Fin q) :
    oddCentralSingularSquare q a k =
      1 + a ^ 2 + 2 * a * Real.cos
        (((k.1 + 1 : ℕ) : ℝ) * Real.pi / ((q + 1 : ℕ) : ℝ)) := by
  rfl

/-- Explicit characteristic polynomial of the common Toeplitz Gram. -/
theorem oddCentralGramToeplitz_charpoly (q : ℕ) {a : ℝ} (ha : 0 < a) :
    (oddCentralGramToeplitz q a).charpoly =
      ∏ k : Fin q, (Polynomial.X -
        Polynomial.C ((oddCentralSingularSquare q a k : ℝ) : ℂ)) := by
  have hmatrix : oddCentralGramToeplitz q a =
      complexSymmetricPath q a -
        Matrix.scalar (Fin q) (-((1 + a ^ 2 : ℝ) : ℂ)) := by
    rw [oddCentralGramToeplitz_eq_scalar_add_path]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar_apply]
      ring
    · simp [Matrix.scalar_apply, hij]
  rw [hmatrix, Matrix.charpoly_sub_scalar,
    charpoly_complexSymmetricPath q ha, Polynomial.prod_comp]
  apply Finset.prod_congr rfl
  intro k _
  simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  simp [oddCentralSingularSquare]
  ring

private theorem oddCentralTopGram_charpoly (q : ℕ) (a : ℝ) :
    (((oddCentralLowerBlock q a)ᴴ * oddCentralLowerBlock q a).charpoly) =
      Polynomial.X * (oddCentralGramToeplitz q a).charpoly := by
  let D := rectangularD q (-(a : ℂ))
  have hDgram : Dᴴ * D = oddCentralGramToeplitz q a := by
    calc
      Dᴴ * D =
          oddCentralLowerBlock q a * (oddCentralLowerBlock q a)ᴴ := by
        rw [oddCentralLowerBlock_eq_rectangularD_star]
        simp [D]
      _ = oddCentralGramToeplitz q a := oddCentralLowerBlock_gram q a
  calc
    ((oddCentralLowerBlock q a)ᴴ * oddCentralLowerBlock q a).charpoly =
        (D * Dᴴ).charpoly := by
      rw [oddCentralLowerBlock_eq_rectangularD_star]
      simp [D]
    _ = Polynomial.X ^
          (Fintype.card (Fin (q + 1)) - Fintype.card (Fin q)) *
          (Dᴴ * D).charpoly :=
      Matrix.charpoly_mul_comm_of_le D Dᴴ (by simp)
    _ = Polynomial.X * (oddCentralGramToeplitz q a).charpoly := by
      rw [hDgram]
      simp

/-- Multiplicity-sensitive singular-square factorization in parity-block
coordinates: `0` occurs once and every displayed square occurs twice. -/
theorem oddCentralOffDiagonal_gram_charpoly
    (q : ℕ) {a : ℝ} (ha : 0 < a) :
    ((oddCentralOffDiagonal q a)ᴴ * oddCentralOffDiagonal q a).charpoly =
      Polynomial.X * ∏ k : Fin q,
        (Polynomial.X -
          Polynomial.C ((oddCentralSingularSquare q a k : ℝ) : ℂ)) ^ 2 := by
  rw [oddCentralOffDiagonal_gram]
  simp only [Matrix.charpoly_fromBlocks_zero₁₂]
  rw [oddCentralTopGram_charpoly,
    congrArg Matrix.charpoly (oddCentralUpperBlock_gram q a),
    oddCentralGramToeplitz_charpoly q ha]
  simp_rw [pow_two]
  rw [Finset.prod_mul_distrib]
  ring

/-- The same multiplicity-sensitive factorization for the actual odd path
matrix, not merely for its permuted block representative. -/
theorem complexPathMatrix_oddCentral_gram_charpoly
    (q : ℕ) {a : ℝ} (ha : 0 < a) :
    ((complexPathMatrix (2 * q + 1) a)ᴴ *
        complexPathMatrix (2 * q + 1) a).charpoly =
      Polynomial.X * ∏ k : Fin q,
        (Polynomial.X -
          Polynomial.C ((oddCentralSingularSquare q a k : ℝ) : ℂ)) ^ 2 := by
  let A := complexPathMatrix (2 * q + 1) a
  let e := oddCentralParityBlockEquiv q
  have hblock : A.submatrix e e = oddCentralOffDiagonal q a :=
    complexPathMatrix_oddCentral_parityBlock q a
  have hgram :
      (oddCentralOffDiagonal q a)ᴴ * oddCentralOffDiagonal q a =
        (Aᴴ * A).submatrix e e := by
    rw [← hblock, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv]
  have hchar : ((Aᴴ * A).submatrix e e).charpoly =
      (Aᴴ * A).charpoly := by
    simpa only [Matrix.reindex_apply] using
      Matrix.charpoly_reindex e.symm (Aᴴ * A)
  rw [← hchar, ← hgram]
  exact oddCentralOffDiagonal_gram_charpoly q ha

private theorem oddCentral_complexReversal_mul_self (n : ℕ) :
    complexReversal n * complexReversal n =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [complexReversal, ← Matrix.map_mul, reversal_mul_self]
  simp

/-- The complex-cast signed-middle matrix has the same Gram characteristic
polynomial as the original path matrix. -/
theorem complexSignedMiddleMatrix_oddCentral_gram_charpoly
    (q : ℕ) {a : ℝ} (ha : 0 < a) :
    let C := (signedMiddleMatrix (2 * q + 1) a 0).map Complex.ofRealHom
    (Cᴴ * C).charpoly =
      Polynomial.X * ∏ k : Fin q,
        (Polynomial.X -
          Polynomial.C ((oddCentralSingularSquare q a k : ℝ) : ℂ)) ^ 2 := by
  dsimp only
  let n := 2 * q + 1
  let A := complexPathMatrix n a
  let J := complexReversal n
  let C := (signedMiddleMatrix n a 0).map Complex.ofRealHom
  have hshift : shiftedPathMatrix n a (0 : ℂ) = -A := by
    ext i j
    simp [shiftedPathMatrix, A]
  have hC : C = (-A) * J := by
    calc
      C = shiftedPathMatrix n a (0 : ℂ) * J :=
        (shiftedPathMatrix_mul_complexReversal n a 0).symm
      _ = (-A) * J := by rw [hshift]
  have hgram : Cᴴ * C = J * (Aᴴ * A) * J := by
    rw [hC]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg]
    rw [show Jᴴ = J by exact complexReversal_star n]
    noncomm_ring
  have hchar : (Cᴴ * C).charpoly = (Aᴴ * A).charpoly := by
    rw [hgram]
    calc
      (J * (Aᴴ * A) * J).charpoly =
          (J * (J * (Aᴴ * A))).charpoly :=
        Matrix.charpoly_mul_comm _ _
      _ = ((J * J) * (Aᴴ * A)).charpoly := by
        congr 1
        noncomm_ring
      _ = (Aᴴ * A).charpoly := by
        rw [show J * J = 1 by exact oddCentral_complexReversal_mul_self n,
          Matrix.one_mul]
  rw [show (signedMiddleMatrix (2 * q + 1) a 0).map Complex.ofRealHom = C from rfl,
    hchar]
  exact complexPathMatrix_oddCentral_gram_charpoly q ha

/-! ## The second-smallest value -/

/-- The square of the paper's second-smallest singular value. -/
def oddCentralSecondSingularSquare (q : ℕ) (a : ℝ) : ℝ :=
  1 + a ^ 2 - 2 * a * Real.cos (Real.pi / ((q + 1 : ℕ) : ℝ))

/-- The paper's `s_(L,2)^(0)`, with `L=q+1`. -/
def oddCentralSecondSingularValue (q : ℕ) (a : ℝ) : ℝ :=
  Real.sqrt (oddCentralSecondSingularSquare q a)

private def oddCentralLastIndex (q : ℕ) (hq : 0 < q) : Fin q :=
  ⟨q - 1, by omega⟩

theorem oddCentralSingularSquare_last (q : ℕ) (hq : 0 < q) (a : ℝ) :
    oddCentralSingularSquare q a (oddCentralLastIndex q hq) =
      oddCentralSecondSingularSquare q a := by
  have hden : (((q + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hangle : pathEigenangle q (oddCentralLastIndex q hq) =
      Real.pi - Real.pi / ((q + 1 : ℕ) : ℝ) := by
    unfold pathEigenangle oddCentralLastIndex
    have hlast : q - 1 + 1 = q := Nat.sub_add_cancel hq
    rw [hlast]
    push_cast
    field_simp [hden]
    ring
  rw [oddCentralSingularSquare, symmetricPathEigenvalue, hangle,
    Real.cos_pi_sub, oddCentralSecondSingularSquare]
  ring

theorem oddCentralSingularSquare_strictAnti
    (q : ℕ) {a : ℝ} (ha : 0 < a) :
    StrictAnti (oddCentralSingularSquare q a) := by
  intro i j hij
  dsimp only [oddCentralSingularSquare]
  linarith [symmetricPathEigenvalue_strictAnti q ha hij]

theorem oddCentralSingularSquare_injective
    (q : ℕ) {a : ℝ} (ha : 0 < a) :
    Function.Injective (oddCentralSingularSquare q a) :=
  (oddCentralSingularSquare_strictAnti q ha).injective

theorem oddCentralSecondSingularSquare_pos
    (q : ℕ) {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) :
    0 < oddCentralSecondSingularSquare q a := by
  have hcos := Real.cos_le_one (Real.pi / ((q + 1 : ℕ) : ℝ))
  have hsq : 0 < (1 - a) ^ 2 := sq_pos_of_ne_zero (by linarith)
  rw [oddCentralSecondSingularSquare]
  nlinarith

theorem oddCentralSingularSquare_pos
    (q : ℕ) (hq : 0 < q) {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (k : Fin q) :
    0 < oddCentralSingularSquare q a k := by
  have hmin : oddCentralSingularSquare q a (oddCentralLastIndex q hq) ≤
      oddCentralSingularSquare q a k :=
    (oddCentralSingularSquare_strictAnti q ha₀).antitone (by
      apply Fin.mk_le_mk.mpr
      dsimp only [oddCentralLastIndex]
      omega)
  rw [oddCentralSingularSquare_last q hq] at hmin
  exact (oddCentralSecondSingularSquare_pos q ha₀ ha₁).trans_le hmin

/-- A concise, multiplicity-sensitive certificate for lines 1829--1837.
The characteristic polynomial has one factor `X`, every positive displayed
square has exponent two, and the displayed squares are pairwise distinct. -/
theorem oddCentral_singularSquare_spectrum_certificate
    (q : ℕ) (hq : 0 < q) {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) :
    let C := (signedMiddleMatrix (2 * q + 1) a 0).map Complex.ofRealHom
    (Cᴴ * C).charpoly =
        Polynomial.X * ∏ k : Fin q,
          (Polynomial.X -
            Polynomial.C ((oddCentralSingularSquare q a k : ℝ) : ℂ)) ^ 2 ∧
      Function.Injective (oddCentralSingularSquare q a) ∧
      ∀ k : Fin q, 0 < oddCentralSingularSquare q a k := by
  dsimp only
  exact ⟨complexSignedMiddleMatrix_oddCentral_gram_charpoly q ha₀,
    oddCentralSingularSquare_injective q ha₀,
    oddCentralSingularSquare_pos q hq ha₀ ha₁⟩

private theorem hermitianEigenvalue_sq_is_gramRoot
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℂ} (hC : C.IsHermitian)
    (i : Fin n) :
    (Cᴴ * C).charpoly.eval (((hC.eigenvalues i) ^ 2 : ℝ) : ℂ) = 0 := by
  let s := hC.eigenvalues i
  let v : Fin n → ℂ := ⇑(hC.eigenvectorBasis i)
  have hv : v ≠ 0 := by
    exact (WithLp.ofLp_eq_zero 2).ne.2
      (hC.eigenvectorBasis.orthonormal.ne_zero i)
  have heig : C *ᵥ v = s • v := hC.mulVec_eigenvectorBasis i
  have hgramEig : (Cᴴ * C) *ᵥ v = (((s ^ 2 : ℝ) : ℂ)) • v := by
    rw [hC, ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, heig]
    ext j
    change (s : ℂ) * ((s : ℂ) * v j) = (((s ^ 2 : ℝ) : ℂ)) * v j
    push_cast
    ring
  have hdet :
      ((Cᴴ * C) - (((s ^ 2 : ℝ) : ℂ)) •
        (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hgramEig]
    exact sub_self _
  rw [Matrix.eval_charpoly]
  have hmatrix :
      Matrix.scalar (Fin n) (((s ^ 2 : ℝ) : ℂ)) - Cᴴ * C =
        -((Cᴴ * C) - (((s ^ 2 : ℝ) : ℂ)) •
          (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    ext p r
    by_cases hpr : p = r <;> simp [Matrix.scalar_apply, hpr]
  rw [hmatrix, Matrix.det_neg, hdet, mul_zero]

/-- Every nonzero complex Hermitian eigenvalue of the odd signed-middle
matrix has square equal to one of the `q` displayed Toeplitz eigenvalues. -/
theorem complexSignedMiddleMatrix_oddCentral_eigenvalue_sq
    (q : ℕ) {a : ℝ} (ha : 0 < a) (i : Fin (2 * q + 1))
    (hi : (complexSignedMiddleMatrix_isHermitian (2 * q + 1) a 0).eigenvalues i ≠ 0) :
    ∃ k : Fin q,
      (complexSignedMiddleMatrix_isHermitian (2 * q + 1) a 0).eigenvalues i ^ 2 =
        oddCentralSingularSquare q a k := by
  let C := (signedMiddleMatrix (2 * q + 1) a 0).map Complex.ofRealHom
  let hC : C.IsHermitian :=
    complexSignedMiddleMatrix_isHermitian (2 * q + 1) a 0
  have hroot := hermitianEigenvalue_sq_is_gramRoot hC i
  rw [complexSignedMiddleMatrix_oddCentral_gram_charpoly q ha] at hroot
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_C] at hroot
  have hsquare : ((((hC.eigenvalues i) ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 hi
  have hprod := (mul_eq_zero.mp hroot).resolve_left hsquare
  obtain ⟨k, _, hk⟩ := Finset.prod_eq_zero_iff.mp hprod
  have hk' :
      (((hC.eigenvalues i) ^ 2 : ℝ) : ℂ) -
          (oddCentralSingularSquare q a k : ℂ) = 0 :=
    eq_zero_of_pow_eq_zero hk
  refine ⟨k, ?_⟩
  exact Complex.ofReal_injective (sub_eq_zero.mp hk')

/-- Every nonzero signed-middle eigenvalue is bounded below in absolute
value by the attained second-smallest singular value at the odd centre. -/
theorem oddCentralSecondSingularValue_le_abs_orderedEigenvalue
    (q : ℕ) (hq : 0 < q) {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1)
    (i : Fin (2 * q + 1)) :
    let hB : (signedMiddleMatrix (2 * q + 1) a 0).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * q + 1) a 0)
    orderedHermitianEigenvalue hB i ≠ 0 →
      oddCentralSecondSingularValue q a ≤
        |orderedHermitianEigenvalue hB i| := by
  dsimp only
  let hB : (signedMiddleMatrix (2 * q + 1) a 0).IsHermitian :=
    Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm (2 * q + 1) a 0)
  let hC := complexSignedMiddleMatrix_isHermitian (2 * q + 1) a 0
  intro hi
  obtain ⟨j, hj⟩ :=
    exists_complexSignedMiddleEigenvalue_eq_orderedEigenvalue
      (2 * q + 1) a 0 i
  have hjne : hC.eigenvalues j ≠ 0 := by rw [hj]; exact hi
  obtain ⟨k, hk⟩ :=
    complexSignedMiddleMatrix_oddCentral_eigenvalue_sq q ha₀ j hjne
  have hmin : oddCentralSecondSingularSquare q a ≤
      oddCentralSingularSquare q a k := by
    rw [← oddCentralSingularSquare_last q hq]
    exact (oddCentralSingularSquare_strictAnti q ha₀).antitone (by
      apply Fin.mk_le_mk.mpr
      dsimp only [oddCentralLastIndex]
      omega)
  have hrad := (oddCentralSecondSingularSquare_pos q ha₀ ha₁).le
  rw [oddCentralSecondSingularValue]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (abs_nonneg _)).1
  rw [Real.sq_sqrt hrad, sq_abs, ← hj, hk]
  exact hmin

private theorem oddCentralSecondSquare_is_gramRoot
    (q : ℕ) (hq : 0 < q) {a : ℝ} (ha : 0 < a) :
    let C := (signedMiddleMatrix (2 * q + 1) a 0).map Complex.ofRealHom
    (Cᴴ * C).charpoly.eval
      (oddCentralSecondSingularSquare q a : ℂ) = 0 := by
  dsimp only
  rw [complexSignedMiddleMatrix_oddCentral_gram_charpoly q ha]
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_C]
  apply (mul_eq_zero).2
  right
  apply Finset.prod_eq_zero (Finset.mem_univ (oddCentralLastIndex q hq))
  rw [oddCentralSingularSquare_last q hq]
  simp

/-- The lower endpoint is attained by an actual eigenvalue of the complex
Hermitian signed-middle matrix.  Together with the preceding universal
bound and the doubled Gram factor, this certifies the term
"second-smallest singular value" rather than merely a lower estimate. -/
theorem exists_complexSignedMiddleMatrix_eigenvalue_abs_eq_oddCentralSecond
    (q : ℕ) (hq : 0 < q) {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) :
    let hC : ((signedMiddleMatrix (2 * q + 1) a 0).map
        Complex.ofRealHom).IsHermitian :=
      complexSignedMiddleMatrix_isHermitian (2 * q + 1) a 0
    ∃ i : Fin (2 * q + 1),
      |hC.eigenvalues i| = oddCentralSecondSingularValue q a := by
  dsimp only
  let n := 2 * q + 1
  let C := (signedMiddleMatrix n a 0).map Complex.ofRealHom
  let hC : C.IsHermitian := complexSignedMiddleMatrix_isHermitian n a 0
  let lam := oddCentralSecondSingularSquare q a
  let d := oddCentralSecondSingularValue q a
  have hlam : 0 ≤ lam := (oddCentralSecondSingularSquare_pos q ha₀ ha₁).le
  have hd : 0 ≤ d := Real.sqrt_nonneg lam
  have hdsq : d ^ 2 = lam := Real.sq_sqrt hlam
  have hroot : (Cᴴ * C).charpoly.eval (lam : ℂ) = 0 := by
    exact oddCentralSecondSquare_is_gramRoot q hq ha₀
  have hdetScalar :
      (Matrix.scalar (Fin n) (lam : ℂ) - Cᴴ * C).det = 0 := by
    simpa only [Matrix.eval_charpoly] using hroot
  have hneg :
      Matrix.scalar (Fin n) (lam : ℂ) - Cᴴ * C =
        -((Cᴴ * C) - (lam : ℂ) •
          (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hdetGram :
      ((Cᴴ * C) - (lam : ℂ) •
        (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 := by
    rw [hneg, Matrix.det_neg] at hdetScalar
    exact (mul_eq_zero.mp hdetScalar).resolve_left
      (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0))
  have hfactor :
      (C - (d : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) *
        (C + (d : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) =
        (Cᴴ * C) - (lam : ℂ) •
          (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have hherm : Cᴴ = C := hC
    have hdsqComplex : (d : ℂ) ^ 2 = (lam : ℂ) := by
      exact_mod_cast hdsq
    have hdmul : (d : ℂ) * (d : ℂ) = (lam : ℂ) := by
      simpa only [pow_two] using hdsqComplex
    rw [hherm]
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_sub, smul_smul]
    rw [hdmul]
    module
  have hdetFactors :
      (C - (d : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det *
          (C + (d : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 := by
    rw [← Matrix.det_mul, hfactor]
    exact hdetGram
  rcases mul_eq_zero.mp hdetFactors with hminus | hplus
  · obtain ⟨i, hi⟩ :=
      exists_complexHermitianEigenvalue_eq_of_det_sub_smul_eq_zero hC d hminus
    refine ⟨i, ?_⟩
    rw [hi, abs_of_nonneg hd]
  · have hplus' :
        (C - ((-d : ℝ) : ℂ) •
          (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 := by
      simpa only [Complex.ofReal_neg, neg_smul, sub_neg_eq_add] using hplus
    obtain ⟨i, hi⟩ :=
      exists_complexHermitianEigenvalue_eq_of_det_sub_smul_eq_zero hC (-d) hplus'
    refine ⟨i, ?_⟩
    rw [hi, abs_neg, abs_of_nonneg hd]

/-- Attainment transported to the project's decreasingly ordered real
signed-middle spectrum. -/
theorem exists_orderedSignedMiddleEigenvalue_abs_eq_oddCentralSecond
    (q : ℕ) (hq : 0 < q) {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) :
    let hB : (signedMiddleMatrix (2 * q + 1) a 0).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * q + 1) a 0)
    ∃ i : Fin (2 * q + 1),
      |orderedHermitianEigenvalue hB i| =
        oddCentralSecondSingularValue q a := by
  dsimp only
  obtain ⟨i, hi⟩ :=
    exists_complexSignedMiddleMatrix_eigenvalue_abs_eq_oddCentralSecond
      q hq ha₀ ha₁
  obtain ⟨j, hj⟩ :=
    exists_orderedSignedMiddleEigenvalue_eq_complexEigenvalue
      (2 * q + 1) a 0 i
  refine ⟨j, ?_⟩
  rw [hj, hi]

/-- Exact minimum-positive-absolute-eigenvalue characterization.  Since the
signed-middle matrix is Hermitian and differs from `-A_(2q+1)` by the
orthogonal reversal factor, this is precisely the paper's second-smallest
singular value (the smallest singular value is the unique zero certified by
`oddCentral_singularSquare_spectrum_certificate`). -/
theorem oddCentralSecondSingularValue_is_minimum_positive_abs_eigenvalue
    (q : ℕ) (hq : 0 < q) {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) :
    let hB : (signedMiddleMatrix (2 * q + 1) a 0).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * q + 1) a 0)
    (∃ i : Fin (2 * q + 1),
        orderedHermitianEigenvalue hB i ≠ 0 ∧
          |orderedHermitianEigenvalue hB i| =
            oddCentralSecondSingularValue q a) ∧
      ∀ i : Fin (2 * q + 1),
        orderedHermitianEigenvalue hB i ≠ 0 →
          oddCentralSecondSingularValue q a ≤
            |orderedHermitianEigenvalue hB i| := by
  dsimp only
  obtain ⟨i, hi⟩ :=
    exists_orderedSignedMiddleEigenvalue_abs_eq_oddCentralSecond
      q hq ha₀ ha₁
  have hvaluePos : 0 < oddCentralSecondSingularValue q a := by
    rw [oddCentralSecondSingularValue]
    exact Real.sqrt_pos.2 (oddCentralSecondSingularSquare_pos q ha₀ ha₁)
  have hine : orderedHermitianEigenvalue
      (Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * q + 1) a 0)) i ≠ 0 := by
    intro hiz
    rw [hiz, abs_zero] at hi
    linarith
  refine ⟨⟨i, hine, hi⟩, ?_⟩
  intro j hj
  exact oddCentralSecondSingularValue_le_abs_orderedEigenvalue
    q hq ha₀ ha₁ j hj

end

end ConnectedPseudospectrum
