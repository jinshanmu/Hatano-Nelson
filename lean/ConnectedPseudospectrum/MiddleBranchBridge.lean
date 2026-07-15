import ConnectedPseudospectrum.MiddleBranchSelection
import ConnectedPseudospectrum.HermitianSingularValues
import ConnectedPseudospectrum.SignedPencil
import Mathlib.Analysis.InnerProductSpace.Semisimple

/-!
# Bridge from the selected real middle branch to the actual pseudospectral height

This module completes the spectral interpretation of the ordered real
eigenvalue selected in `MiddleBranchSelection`.  It identifies that value
with the attained complex Euclidean least singular value, records its
signed-pencil root, and supplies the endpoint and continuity facts used by
`lem:middle-branch`.
-/

namespace ConnectedPseudospectrum

open Matrix Module

noncomputable section

/-- A real Hermitian matrix has the same characteristic polynomial as
the diagonal matrix of its decreasingly ordered eigenvalues. -/
theorem charpoly_eq_orderedHermitianEigenvalue_diagonal {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    A.charpoly =
      (Matrix.diagonal (orderedHermitianEigenvalue hA)).charpoly := by
  let U := orderedHermitianEigenvectorMatrix hA
  let D := Matrix.diagonal (orderedHermitianEigenvalue hA)
  have hspec := orderedHermitian_spectral_decomposition hA
  have hUtU : Matrix.transpose U * U =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    exact (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp
      (orderedHermitianEigenvectorMatrix_mem_orthogonal hA)
  calc
    A.charpoly = (U * D * Matrix.transpose U).charpoly := by
      exact congrArg Matrix.charpoly hspec
    _ =
        (Matrix.transpose U * (U * D)).charpoly :=
      Matrix.charpoly_mul_comm _ _
    _ = ((Matrix.transpose U * U) * D).charpoly := by
      congr 1
      noncomm_ring
    _ = D.charpoly := by rw [hUtU, Matrix.one_mul]

/-- Every ordered real Hermitian eigenvalue is a zero of the ordinary
scalar determinant pencil. -/
theorem det_sub_orderedHermitianEigenvalue_smul_eq_zero {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (i : Fin n) :
    (A - orderedHermitianEigenvalue hA i • 1).det = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  let v : Fin n → ℝ := orderedHermitianEigenbasis hA i
  have hv : v ≠ 0 := by
    intro hv0
    apply (orderedHermitianEigenbasis hA).toBasis.ne_zero i
    apply WithLp.ofLp_injective 2
    exact hv0
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    mulVec_orderedHermitianEigenbasis hA i]
  change orderedHermitianEigenvalue hA i • v -
      orderedHermitianEigenvalue hA i • v = 0
  exact sub_self _

/-- Conversely, every real zero of the scalar determinant pencil of a
real Hermitian matrix occurs in the full ordered eigenvalue list. -/
theorem exists_orderedHermitianEigenvalue_eq_of_det_sub_smul_eq_zero
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (s : ℝ) (hdet : (A - s • 1).det = 0) :
    ∃ i : Fin n, orderedHermitianEigenvalue hA i = s := by
  have hroot : A.charpoly.eval s = 0 := by
    rw [Matrix.eval_charpoly]
    have hmatrix : Matrix.scalar (Fin n) s - A = -(A - s • 1) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    rw [hmatrix, Matrix.det_neg, hdet, mul_zero]
  rw [charpoly_eq_orderedHermitianEigenvalue_diagonal hA,
    Matrix.charpoly_diagonal] at hroot
  simp only [Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] at hroot
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hroot
  exact ⟨i, sub_eq_zero.mp hi |>.symm⟩

/-- The selected ordered real eigenvalue is an actual root of the signed
determinant pencil. -/
theorem signedPencilDet_orderedHermitianEigenvalue_eq_zero
    (n : ℕ) (a x : ℝ) (i : Fin n) :
    let hB : (signedMiddleMatrix n a x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
    signedPencilDet n a x (orderedHermitianEigenvalue hB i) = 0 := by
  dsimp only
  rw [signedPencilDet_eq_zero_iff]
  exact det_sub_orderedHermitianEigenvalue_smul_eq_zero
    (Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)) i

/-- A real zero of the scalar determinant pencil of a complex Hermitian
matrix occurs in Mathlib's complete Hermitian eigenvalue list. -/
theorem exists_complexHermitianEigenvalue_eq_of_det_sub_smul_eq_zero
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (s : ℝ)
    (hdet : (A - (s : ℂ) • 1).det = 0) :
    ∃ i : Fin n, hA.eigenvalues i = s := by
  have hroot : A.charpoly.eval (s : ℂ) = 0 := by
    rw [Matrix.eval_charpoly]
    have hmatrix : Matrix.scalar (Fin n) (s : ℂ) - A =
        -(A - (s : ℂ) • 1) := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    rw [hmatrix, Matrix.det_neg, hdet, mul_zero]
  rw [hA.charpoly_eq] at hroot
  simp only [Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C] at hroot
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hroot
  have hiComplex : (hA.eigenvalues i : ℂ) = (s : ℂ) :=
    (sub_eq_zero.mp hi).symm
  exact ⟨i, Complex.ofReal_injective hiComplex⟩

/-- Every complex Hermitian eigenvalue of the cast signed-middle matrix is
one of the ordered eigenvalues of the underlying real symmetric matrix. -/
theorem exists_orderedSignedMiddleEigenvalue_eq_complexEigenvalue
    (n : ℕ) (a x : ℝ) (i : Fin n) :
    let hB : (signedMiddleMatrix n a x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
    let hC : ((signedMiddleMatrix n a x).map
        Complex.ofRealHom).IsHermitian :=
      complexSignedMiddleMatrix_isHermitian n a x
    ∃ j : Fin n,
      orderedHermitianEigenvalue hB j = hC.eigenvalues i := by
  dsimp only
  let B : Matrix (Fin n) (Fin n) ℝ := signedMiddleMatrix n a x
  let hB : B.IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
  let hC : (B.map Complex.ofRealHom).IsHermitian :=
    complexSignedMiddleMatrix_isHermitian n a x
  have hdet :
      (B - hC.eigenvalues i • (1 : Matrix (Fin n) (Fin n) ℝ)).det = 0 := by
    exact (signedPencilDet_eq_zero_iff n a x (hC.eigenvalues i)).1
      (signedPencilDet_eigenvalue_eq_zero n a x i)
  exact exists_orderedHermitianEigenvalue_eq_of_det_sub_smul_eq_zero
    hB (hC.eigenvalues i) hdet

/-- Conversely, each ordered eigenvalue of the real signed-middle matrix
occurs in the Hermitian eigenvalue list after scalar extension to `ℂ`. -/
theorem exists_complexSignedMiddleEigenvalue_eq_orderedEigenvalue
    (n : ℕ) (a x : ℝ) (i : Fin n) :
    let hB : (signedMiddleMatrix n a x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
    let hC : ((signedMiddleMatrix n a x).map
        Complex.ofRealHom).IsHermitian :=
      complexSignedMiddleMatrix_isHermitian n a x
    ∃ j : Fin n,
      hC.eigenvalues j = orderedHermitianEigenvalue hB i := by
  dsimp only
  let B : Matrix (Fin n) (Fin n) ℝ := signedMiddleMatrix n a x
  let C : Matrix (Fin n) (Fin n) ℂ := B.map Complex.ofRealHom
  let hB : B.IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
  let hC : C.IsHermitian := complexSignedMiddleMatrix_isHermitian n a x
  let s : ℝ := orderedHermitianEigenvalue hB i
  have hdetReal :
      (B - s • (1 : Matrix (Fin n) (Fin n) ℝ)).det = 0 :=
    det_sub_orderedHermitianEigenvalue_smul_eq_zero hB i
  have hmap :
      (B - s • (1 : Matrix (Fin n) (Fin n) ℝ)).map Complex.ofRealHom =
        C - (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext p q
    by_cases hpq : p = q
    · subst q
      simp [B, C]
    · simp [B, C, hpq]
  have hdetComplex :
      (C - (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 := by
    have hcast : Complex.ofRealHom
        ((B - s • (1 : Matrix (Fin n) (Fin n) ℝ)).det) = 0 := by
      rw [hdetReal, map_zero]
    rw [Complex.ofRealHom.map_det, RingHom.mapMatrix_apply, hmap] at hcast
    exact hcast
  exact exists_complexHermitianEigenvalue_eq_of_det_sub_smul_eq_zero
    hC s hdetComplex

/-- If an ordered eigenvalue of the real signed-middle matrix has least
absolute value, then its absolute value is exactly the actual complex
Euclidean least singular value of `xI-A_n`. -/
theorem pseudospectralHeight_eq_abs_orderedHermitianEigenvalue_of_min
    (n : ℕ) (hn : 0 < n) (a x : ℝ) (i : Fin n) :
    let hB : (signedMiddleMatrix n a x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
    (∀ j : Fin n,
        |orderedHermitianEigenvalue hB i| ≤
          |orderedHermitianEigenvalue hB j|) →
      pseudospectralHeight n a (x : ℂ) =
        |orderedHermitianEigenvalue hB i| := by
  dsimp only
  let hB : (signedMiddleMatrix n a x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
  let hC : ((signedMiddleMatrix n a x).map
      Complex.ofRealHom).IsHermitian :=
    complexSignedMiddleMatrix_isHermitian n a x
  intro hmin
  obtain ⟨k, hheight, hall⟩ :=
    exists_signedMiddleMatrix_eigenvalue_abs_eq_pseudospectralHeight
      n hn a x
  obtain ⟨j, hj⟩ :=
    exists_orderedSignedMiddleEigenvalue_eq_complexEigenvalue n a x k
  obtain ⟨ell, hell⟩ :=
    exists_complexSignedMiddleEigenvalue_eq_orderedEigenvalue n a x i
  apply le_antisymm
  · calc
      pseudospectralHeight n a (x : ℂ) ≤ |hC.eigenvalues ell| := hall ell
      _ = |orderedHermitianEigenvalue hB i| := congrArg abs hell
  · calc
      |orderedHermitianEigenvalue hB i| ≤
          |orderedHermitianEigenvalue hB j| := hmin j
      _ = |hC.eigenvalues k| := congrArg abs hj
      _ = pseudospectralHeight n a (x : ℂ) := hheight.symm

/-- The sign prescribed by the paper for the middle branch in gap `j`. -/
def middleBranchSign (j : ℕ) : ℝ :=
  if Even j then 1 else -1

/-- Continuous signed-height extension of the middle branch.  The selection
theorems below prove that this is the relevant ordered eigenvalue on every
open spectral gap. -/
def middleBranchExtension (n : ℕ) (a : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  middleBranchSign j * realGapValue n a x

theorem middleBranchSign_of_even {j : ℕ} (hj : Even j) :
    middleBranchSign j = 1 := by
  simp [middleBranchSign, hj]

theorem middleBranchSign_of_odd {j : ℕ} (hj : Odd j) :
    middleBranchSign j = -1 := by
  have hjNotEven : ¬Even j := Nat.not_even_iff_odd.mpr hj
  simp [middleBranchSign, hjNotEven]

/-- The signed-height extension is continuous on the whole real line, hence
in particular across the closure of every spectral gap. -/
theorem continuous_middleBranchExtension (n : ℕ) (a : ℝ) (j : ℕ) :
    Continuous (middleBranchExtension n a j) := by
  unfold middleBranchExtension
  exact continuous_const.mul (continuous_realGapValue n a)

/-- Even dimension, even gap: the selected middle ordered eigenvalue is
positive, equals the actual least singular value, and is a signed-pencil
root. -/
theorem evenMiddleBranch_bridge_even_gap
    (m j : ℕ) (hm : 0 < m) (hj : 0 < j) (hjn : j < 2 * m)
    (hjEven : Even j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m) r ⟨j - 1, by omega⟩) :
    let hA : (signedMiddleMatrix (2 * m) (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m) (r ^ 2) x)
    let s := orderedHermitianEigenvalue hA ⟨m - 1, by omega⟩
    0 < s ∧
      pseudospectralHeight (2 * m) (r ^ 2) (x : ℂ) = |s| ∧
      middleBranchExtension (2 * m) (r ^ 2) j x = s ∧
      signedPencilDet (2 * m) (r ^ 2) x s = 0 := by
  dsimp only
  let hA : (signedMiddleMatrix (2 * m) (r ^ 2) x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm (2 * m) (r ^ 2) x)
  let s := orderedHermitianEigenvalue hA ⟨m - 1, by omega⟩
  have hselection := evenSignedMiddleMatrix_central_abs_min_even_gap
    m j hm hj hjn hjEven hr hxLower hxUpper
  have hheight :
      pseudospectralHeight (2 * m) (r ^ 2) (x : ℂ) = |s| :=
    pseudospectralHeight_eq_abs_orderedHermitianEigenvalue_of_min
      (2 * m) (by omega) (r ^ 2) x ⟨m - 1, by omega⟩ hselection.2
  have hextension : middleBranchExtension (2 * m) (r ^ 2) j x = s := by
    rw [middleBranchExtension, middleBranchSign_of_even hjEven,
      one_mul, realGapValue, hheight, abs_of_pos hselection.1]
  exact ⟨hselection.1, hheight, hextension,
    signedPencilDet_orderedHermitianEigenvalue_eq_zero
      (2 * m) (r ^ 2) x ⟨m - 1, by omega⟩⟩

/-- Even dimension at least four, odd gap: the selected middle ordered
eigenvalue is negative, its magnitude is the actual least singular value,
and it is a signed-pencil root. -/
theorem evenMiddleBranch_bridge_odd_gap
    (m j : ℕ) (hm : 2 ≤ m) (hj : 0 < j) (hjn : j < 2 * m)
    (hjOdd : Odd j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m) r ⟨j - 1, by omega⟩) :
    let hA : (signedMiddleMatrix (2 * m) (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m) (r ^ 2) x)
    let s := orderedHermitianEigenvalue hA ⟨m - 1, by omega⟩
    s < 0 ∧
      pseudospectralHeight (2 * m) (r ^ 2) (x : ℂ) = |s| ∧
      middleBranchExtension (2 * m) (r ^ 2) j x = s ∧
      signedPencilDet (2 * m) (r ^ 2) x s = 0 := by
  dsimp only
  let hA : (signedMiddleMatrix (2 * m) (r ^ 2) x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm (2 * m) (r ^ 2) x)
  let s := orderedHermitianEigenvalue hA ⟨m - 1, by omega⟩
  have hselection := evenSignedMiddleMatrix_central_abs_min_odd_gap
    m j hm hj hjn hjOdd hr hxLower hxUpper
  have hheight :
      pseudospectralHeight (2 * m) (r ^ 2) (x : ℂ) = |s| :=
    pseudospectralHeight_eq_abs_orderedHermitianEigenvalue_of_min
      (2 * m) (by omega) (r ^ 2) x ⟨m - 1, by omega⟩ hselection.2
  have hextension : middleBranchExtension (2 * m) (r ^ 2) j x = s := by
    rw [middleBranchExtension, middleBranchSign_of_odd hjOdd,
      realGapValue, hheight, abs_of_neg hselection.1]
    ring
  exact ⟨hselection.1, hheight, hextension,
    signedPencilDet_orderedHermitianEigenvalue_eq_zero
      (2 * m) (r ^ 2) x ⟨m - 1, by omega⟩⟩

/-- The exceptional two-dimensional odd-gap case.  Its selected branch is
the top ordered eigenvalue (index zero), not an instance of the rank-two
interlacing argument used from dimension four onward. -/
theorem twoMiddleBranch_bridge_odd_gap
    (j : ℕ) (hj : 0 < j) (hjn : j < 2) (hjOdd : Odd j)
    {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue 2 r ⟨j, hjn⟩ < x)
    (hxUpper : x < symmetricPathEigenvalue 2 r ⟨j - 1, by omega⟩) :
    let hA : (signedMiddleMatrix 2 (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm 2 (r ^ 2) x)
    let s := orderedHermitianEigenvalue hA 0
    s < 0 ∧
      pseudospectralHeight 2 (r ^ 2) (x : ℂ) = |s| ∧
      middleBranchExtension 2 (r ^ 2) j x = s ∧
      signedPencilDet 2 (r ^ 2) x s = 0 := by
  dsimp only
  let hA : (signedMiddleMatrix 2 (r ^ 2) x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm 2 (r ^ 2) x)
  let s := orderedHermitianEigenvalue hA 0
  have hselection := twoSignedMiddleMatrix_central_abs_min_odd_gap
    j hj hjn hjOdd hr hxLower hxUpper
  have hheight : pseudospectralHeight 2 (r ^ 2) (x : ℂ) = |s| :=
    pseudospectralHeight_eq_abs_orderedHermitianEigenvalue_of_min
      2 (by omega) (r ^ 2) x 0 hselection.2
  have hextension : middleBranchExtension 2 (r ^ 2) j x = s := by
    rw [middleBranchExtension, middleBranchSign_of_odd hjOdd,
      realGapValue, hheight, abs_of_neg hselection.1]
    ring
  exact ⟨hselection.1, hheight, hextension,
    signedPencilDet_orderedHermitianEigenvalue_eq_zero
      2 (r ^ 2) x 0⟩

/-- Odd dimension, even gap: the central ordered eigenvalue is positive,
equals the actual least singular value, and is a signed-pencil root. -/
theorem oddMiddleBranch_bridge_even_gap
    (m j : ℕ) (hm : 0 < m) (hj : 0 < j) (hjn : j < 2 * m + 1)
    (hjEven : Even j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m + 1) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m + 1) r ⟨j - 1, by omega⟩) :
    let hA : (signedMiddleMatrix (2 * m + 1) (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m + 1) (r ^ 2) x)
    let s := orderedHermitianEigenvalue hA ⟨m, by omega⟩
    0 < s ∧
      pseudospectralHeight (2 * m + 1) (r ^ 2) (x : ℂ) = |s| ∧
      middleBranchExtension (2 * m + 1) (r ^ 2) j x = s ∧
      signedPencilDet (2 * m + 1) (r ^ 2) x s = 0 := by
  dsimp only
  let hA : (signedMiddleMatrix (2 * m + 1) (r ^ 2) x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm (2 * m + 1) (r ^ 2) x)
  let s := orderedHermitianEigenvalue hA ⟨m, by omega⟩
  have hselection := oddSignedMiddleMatrix_central_abs_min_even_gap
    m j hm hj hjn hjEven hr hxLower hxUpper
  have hheight :
      pseudospectralHeight (2 * m + 1) (r ^ 2) (x : ℂ) = |s| :=
    pseudospectralHeight_eq_abs_orderedHermitianEigenvalue_of_min
      (2 * m + 1) (by omega) (r ^ 2) x ⟨m, by omega⟩ hselection.2
  have hextension :
      middleBranchExtension (2 * m + 1) (r ^ 2) j x = s := by
    rw [middleBranchExtension, middleBranchSign_of_even hjEven,
      one_mul, realGapValue, hheight, abs_of_pos hselection.1]
  exact ⟨hselection.1, hheight, hextension,
    signedPencilDet_orderedHermitianEigenvalue_eq_zero
      (2 * m + 1) (r ^ 2) x ⟨m, by omega⟩⟩

/-- Odd dimension, odd gap: the central ordered eigenvalue is negative,
its magnitude is the actual least singular value, and it is a signed-pencil
root. -/
theorem oddMiddleBranch_bridge_odd_gap
    (m j : ℕ) (hm : 0 < m) (hj : 0 < j) (hjn : j < 2 * m + 1)
    (hjOdd : Odd j) {r : ℝ} (hr : 0 < r) {x : ℝ}
    (hxLower : symmetricPathEigenvalue (2 * m + 1) r ⟨j, hjn⟩ < x)
    (hxUpper :
      x < symmetricPathEigenvalue (2 * m + 1) r ⟨j - 1, by omega⟩) :
    let hA : (signedMiddleMatrix (2 * m + 1) (r ^ 2) x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * m + 1) (r ^ 2) x)
    let s := orderedHermitianEigenvalue hA ⟨m, by omega⟩
    s < 0 ∧
      pseudospectralHeight (2 * m + 1) (r ^ 2) (x : ℂ) = |s| ∧
      middleBranchExtension (2 * m + 1) (r ^ 2) j x = s ∧
      signedPencilDet (2 * m + 1) (r ^ 2) x s = 0 := by
  dsimp only
  let hA : (signedMiddleMatrix (2 * m + 1) (r ^ 2) x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm (2 * m + 1) (r ^ 2) x)
  let s := orderedHermitianEigenvalue hA ⟨m, by omega⟩
  have hselection := oddSignedMiddleMatrix_central_abs_min_odd_gap
    m j hm hj hjn hjOdd hr hxLower hxUpper
  have hheight :
      pseudospectralHeight (2 * m + 1) (r ^ 2) (x : ℂ) = |s| :=
    pseudospectralHeight_eq_abs_orderedHermitianEigenvalue_of_min
      (2 * m + 1) (by omega) (r ^ 2) x ⟨m, by omega⟩ hselection.2
  have hextension :
      middleBranchExtension (2 * m + 1) (r ^ 2) j x = s := by
    rw [middleBranchExtension, middleBranchSign_of_odd hjOdd,
      realGapValue, hheight, abs_of_neg hselection.1]
    ring
  exact ⟨hselection.1, hheight, hextension,
    signedPencilDet_orderedHermitianEigenvalue_eq_zero
      (2 * m + 1) (r ^ 2) x ⟨m, by omega⟩⟩

/-- The eigenspace of each displayed path eigenvalue is one-dimensional.
This is the rank statement used in the paper's endpoint simplicity
argument. -/
theorem finrank_pathMatrix_eigenspace_symmetricPathEigenvalue_eq_one
    (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    Module.finrank ℝ
      (Module.End.eigenspace (pathMatrix n (r ^ 2)).toLin'
        (symmetricPathEigenvalue n r k)) = 1 := by
  let T : Module.End ℝ (Fin n → ℝ) := (pathMatrix n (r ^ 2)).toLin'
  let lambda := symmetricPathEigenvalue n r k
  have hhas : Module.End.HasEigenvalue T lambda :=
    Module.End.hasEigenvalue_of_hasEigenvector
      (pathMatrix_hasEigenvector n hr k)
  have hnontrivial : Module.End.eigenspace T lambda ≠ ⊥ :=
    Module.End.hasEigenvalue_iff.mp hhas
  have hone : 1 ≤ Module.finrank ℝ (Module.End.eigenspace T lambda) :=
    Submodule.one_le_finrank_iff.mpr hnontrivial
  have hleMultiplicity := LinearMap.finrank_eigenspace_le T lambda
  have hseparable : T.charpoly.Separable := by
    rw [Matrix.charpoly_toLin']
    exact charpoly_pathMatrix_sq_separable n hr
  have hmultiplicity :=
    Polynomial.rootMultiplicity_le_one_of_separable hseparable lambda
  change Module.finrank ℝ (Module.End.eigenspace T lambda) = 1
  omega

/-- At a displayed spectral node, the real shifted path has rank exactly
`n-1`. -/
theorem realShiftedPathMatrix_rank_at_symmetricPathEigenvalue
    (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    (symmetricPathEigenvalue n r k • 1 - pathMatrix n (r ^ 2)).rank =
      n - 1 := by
  let M : Matrix (Fin n) (Fin n) ℝ :=
    symmetricPathEigenvalue n r k • 1 - pathMatrix n (r ^ 2)
  let T : Module.End ℝ (Fin n → ℝ) := (pathMatrix n (r ^ 2)).toLin'
  let lambda := symmetricPathEigenvalue n r k
  have hker : LinearMap.ker M.mulVecLin =
      Module.End.eigenspace T lambda := by
    ext v
    rw [LinearMap.mem_ker, Module.End.mem_eigenspace_iff]
    change
      (lambda • 1 - pathMatrix n (r ^ 2)).mulVec v = 0 ↔
        (pathMatrix n (r ^ 2)).mulVec v = lambda • v
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    constructor
    · intro h
      exact (sub_eq_zero.mp h).symm
    · intro h
      exact sub_eq_zero.mpr h.symm
  have hnullity : Module.finrank ℝ (Module.End.eigenspace T lambda) = 1 :=
    finrank_pathMatrix_eigenspace_symmetricPathEigenvalue_eq_one n hr k
  have hrankNullity :=
    LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  change M.rank + Module.finrank ℝ (LinearMap.ker M.mulVecLin) =
      Module.finrank ℝ (Fin n → ℝ) at hrankNullity
  rw [hker, hnullity] at hrankNullity
  have hrankSucc : M.rank + 1 = n := by
    simpa using hrankNullity
  change M.rank = n - 1
  omega

/-- Right multiplication by reversal preserves the endpoint rank, so zero
is a geometrically simple eigenvalue of the signed-middle matrix. -/
theorem signedMiddleMatrix_rank_at_symmetricPathEigenvalue
    (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    (signedMiddleMatrix n (r ^ 2)
      (symmetricPathEigenvalue n r k)).rank = n - 1 := by
  have hunit : IsUnit (reversal n).det :=
    Matrix.isUnit_det_of_right_inverse (reversal_mul_self n)
  calc
    (signedMiddleMatrix n (r ^ 2)
        (symmetricPathEigenvalue n r k)).rank =
        ((symmetricPathEigenvalue n r k • 1 - pathMatrix n (r ^ 2)) *
          reversal n).rank := rfl
    _ = (symmetricPathEigenvalue n r k • 1 -
          pathMatrix n (r ^ 2)).rank :=
      Matrix.rank_mul_eq_left_of_isUnit_det _ _ hunit
    _ = n - 1 :=
      realShiftedPathMatrix_rank_at_symmetricPathEigenvalue n hr k

/-- Exact endpoint simplicity certificate: the zero eigenspace of the real
symmetric signed-middle matrix has dimension one.  For a real symmetric
matrix this is the paper's statement that zero is a simple eigenvalue. -/
theorem signedMiddleMatrix_zero_eigenspace_finrank_at_spectral_node
    (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    Module.finrank ℝ
      (Module.End.eigenspace
        (signedMiddleMatrix n (r ^ 2)
          (symmetricPathEigenvalue n r k)).toLin' 0) = 1 := by
  let B := signedMiddleMatrix n (r ^ 2)
    (symmetricPathEigenvalue n r k)
  have hrank : B.rank = n - 1 :=
    signedMiddleMatrix_rank_at_symmetricPathEigenvalue n hr k
  have hrankNullity :=
    LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  change B.rank + Module.finrank ℝ (LinearMap.ker B.mulVecLin) =
      Module.finrank ℝ (Fin n → ℝ) at hrankNullity
  have hnullity : Module.finrank ℝ (LinearMap.ker B.mulVecLin) = 1 := by
    have hklt : k.1 < n := k.isLt
    have hn : 0 < n := by omega
    have hrankSucc : B.rank +
        Module.finrank ℝ (LinearMap.ker B.mulVecLin) = n := by
      simpa using hrankNullity
    rw [hrank] at hrankSucc
    omega
  rw [Module.End.eigenspace_zero, Matrix.toLin'_apply']
  exact hnullity

/-- Algebraic endpoint simplicity: zero has multiplicity exactly one in
the characteristic polynomial of the symmetric signed-middle matrix. -/
theorem signedMiddleMatrix_charpoly_rootMultiplicity_zero_at_spectral_node
    (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    (signedMiddleMatrix n (r ^ 2)
      (symmetricPathEigenvalue n r k)).charpoly.rootMultiplicity 0 = 1 := by
  let B := signedMiddleMatrix n (r ^ 2)
    (symmetricPathEigenvalue n r k)
  let T : Module.End ℝ (EuclideanSpace ℝ (Fin n)) := B.toEuclideanLin
  let hB : B.IsHermitian := Matrix.IsSymm.isHermitianReal
    (signedMiddleMatrix_isSymm n (r ^ 2)
      (symmetricPathEigenvalue n r k))
  have hT : T.IsSymmetric := by
    change B.toEuclideanLin.IsSymmetric
    exact Matrix.isHermitian_iff_isSymmetric.mp hB
  have hsemisimple : T.IsFinitelySemisimple :=
    hT.isFinitelySemisimple
  have hrank : B.rank = n - 1 :=
    signedMiddleMatrix_rank_at_symmetricPathEigenvalue n hr k
  have hrange : Module.finrank ℝ (LinearMap.range T) = B.rank := by
    have h := Matrix.rank_eq_finrank_range_toLin B
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    rw [← Matrix.toEuclideanLin_eq_toLin_orthonormal] at h
    exact h.symm
  have hrankNullity :=
    LinearMap.finrank_range_add_finrank_ker T
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    simp
  have hker : Module.finrank ℝ (LinearMap.ker T) = 1 := by
    rw [hrange, hrank, hdim] at hrankNullity
    have hklt : k.1 < n := k.isLt
    have hn : 0 < n := by omega
    omega
  have heigenspace :
      Module.finrank ℝ (Module.End.eigenspace T 0) = 1 := by
    rw [Module.End.eigenspace_zero]
    exact hker
  have hmultiplicity : T.charpoly.rootMultiplicity 0 = 1 := by
    rw [← LinearMap.finrank_maxGenEigenspace_eq T 0,
      hsemisimple.maxGenEigenspace_eq_eigenspace]
    exact heigenspace
  have hcharpoly : T.charpoly = B.charpoly := by
    change B.toEuclideanLin.charpoly = B.charpoly
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
      Matrix.charpoly_toLin]
  rw [← hcharpoly]
  exact hmultiplicity

/-- The polynomial in `s` represented by the paper's signed determinant
pencil.  The normalizing constant is forced by
`signedPencilDet_mul_det_reversal`; the next theorem proves pointwise
agreement with the determinant definition. -/
def signedPencilPolynomial (n : ℕ) (a x : ℝ) : Polynomial ℝ :=
  Polynomial.C
      (((-1 : ℝ) ^ n) * ((reversal n).det)⁻¹) *
    (signedMiddleMatrix n a x).charpoly

/-- Evaluation of `signedPencilPolynomial` is exactly the determinant
`q_n(x,s)`, not merely a polynomial with the same zero set. -/
theorem signedPencilPolynomial_eval (n : ℕ) (a x s : ℝ) :
    (signedPencilPolynomial n a x).eval s = signedPencilDet n a x s := by
  let B := signedMiddleMatrix n a x
  let d := (reversal n).det
  have hd : d ≠ 0 :=
    (Matrix.isUnit_det_of_right_inverse (reversal_mul_self n)).ne_zero
  have hmatrix : B - s • (1 : Matrix (Fin n) (Fin n) ℝ) =
      -(Matrix.scalar (Fin n) s - B) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hdetShift :
      (B - s • (1 : Matrix (Fin n) (Fin n) ℝ)).det =
        (-1 : ℝ) ^ n * B.charpoly.eval s := by
    calc
      (B - s • (1 : Matrix (Fin n) (Fin n) ℝ)).det =
          (-(Matrix.scalar (Fin n) s - B)).det :=
        congrArg Matrix.det hmatrix
      _ = (-1 : ℝ) ^ n *
          (Matrix.scalar (Fin n) s - B).det := by
        rw [Matrix.det_neg, Fintype.card_fin]
      _ = (-1 : ℝ) ^ n * B.charpoly.eval s := by
        rw [Matrix.eval_charpoly]
  have hrelation : signedPencilDet n a x s * d =
      (B - s • (1 : Matrix (Fin n) (Fin n) ℝ)).det :=
    signedPencilDet_mul_det_reversal n a x s
  unfold signedPencilPolynomial
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  change (((-1 : ℝ) ^ n * d⁻¹) * B.charpoly.eval s) =
    signedPencilDet n a x s
  apply mul_right_cancel₀ hd
  calc
    (((-1 : ℝ) ^ n * d⁻¹) * B.charpoly.eval s) * d =
        (-1 : ℝ) ^ n * B.charpoly.eval s * (d⁻¹ * d) := by
      ring
    _ = (-1 : ℝ) ^ n * B.charpoly.eval s := by
      rw [inv_mul_cancel₀ hd, mul_one]
    _ = (B - s • (1 : Matrix (Fin n) (Fin n) ℝ)).det :=
      hdetShift.symm
    _ = signedPencilDet n a x s * d := hrelation.symm

/-- Literal simple-root statement for the polynomial signed pencil at every
spectral endpoint. -/
theorem signedPencilPolynomial_rootMultiplicity_zero_at_spectral_node
    (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    (signedPencilPolynomial n (r ^ 2)
      (symmetricPathEigenvalue n r k)).rootMultiplicity 0 = 1 := by
  let B := signedMiddleMatrix n (r ^ 2)
    (symmetricPathEigenvalue n r k)
  let d := (reversal n).det
  let c := ((-1 : ℝ) ^ n) * d⁻¹
  have hd : d ≠ 0 :=
    (Matrix.isUnit_det_of_right_inverse (reversal_mul_self n)).ne_zero
  have hc : c ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero n (by norm_num)) (inv_ne_zero hd)
  have hproduct : Polynomial.C c * B.charpoly ≠ 0 :=
    mul_ne_zero (Polynomial.C_ne_zero.mpr hc) B.charpoly_monic.ne_zero
  change (Polynomial.C c * B.charpoly).rootMultiplicity 0 = 1
  rw [Polynomial.rootMultiplicity_mul hproduct,
    Polynomial.rootMultiplicity_C, zero_add]
  exact
    signedMiddleMatrix_charpoly_rootMultiplicity_zero_at_spectral_node
      n hr k

/-- At every displayed spectral node, `s=0` is a root of the signed
determinant pencil. -/
theorem signedPencilDet_symmetricPathEigenvalue_sq_zero
    (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    signedPencilDet n (r ^ 2) (symmetricPathEigenvalue n r k) 0 = 0 := by
  unfold signedPencilDet signedPencil
  simp only [zero_smul, sub_zero]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨pathRightEigenvector n r k,
    pathRightEigenvector_ne_zero n hr.ne' k, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    pathMatrix_mulVec_pathRightEigenvector]
  exact sub_self _

/-- The endpoint is simultaneously a signed-pencil root and a geometrically
simple zero eigenvalue of the symmetric signed-middle matrix. -/
theorem signedPencil_endpoint_zero_and_simple
    (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    signedPencilDet n (r ^ 2) (symmetricPathEigenvalue n r k) 0 = 0 ∧
      Module.finrank ℝ
        (Module.End.eigenspace
          (signedMiddleMatrix n (r ^ 2)
            (symmetricPathEigenvalue n r k)).toLin' 0) = 1 ∧
      (signedMiddleMatrix n (r ^ 2)
        (symmetricPathEigenvalue n r k)).charpoly.rootMultiplicity 0 = 1 ∧
      (signedPencilPolynomial n (r ^ 2)
        (symmetricPathEigenvalue n r k)).rootMultiplicity 0 = 1 :=
  ⟨signedPencilDet_symmetricPathEigenvalue_sq_zero n hr k,
    signedMiddleMatrix_zero_eigenspace_finrank_at_spectral_node n hr k,
    signedMiddleMatrix_charpoly_rootMultiplicity_zero_at_spectral_node
      n hr k,
    signedPencilPolynomial_rootMultiplicity_zero_at_spectral_node n hr k⟩

/-- The actual least singular value, and hence the signed branch extension,
vanishes at every displayed endpoint. -/
theorem realGapValue_symmetricPathEigenvalue_sq_eq_zero
    (n : ℕ) (hn : 0 < n) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    realGapValue n (r ^ 2) (symmetricPathEigenvalue n r k) = 0 := by
  have heigenvalue :
      pathEigenvalue n (r ^ 2) k = symmetricPathEigenvalue n r k := by
    rw [pathEigenvalue_eq_symmetricPathEigenvalue, Real.sqrt_sq_eq_abs,
      abs_of_pos hr]
  unfold realGapValue
  rw [← heigenvalue]
  exact pseudospectralHeight_pathEigenvalue n (sq_pos_of_pos hr) hn k

theorem middleBranchExtension_symmetricPathEigenvalue_sq_eq_zero
    (n : ℕ) (hn : 0 < n) (j : ℕ) {r : ℝ} (hr : 0 < r)
    (k : Fin n) :
    middleBranchExtension n (r ^ 2) j
        (symmetricPathEigenvalue n r k) = 0 := by
  rw [middleBranchExtension,
    realGapValue_symmetricPathEigenvalue_sq_eq_zero n hn hr k, mul_zero]

/-- On the closed `j`-th spectral gap, the selected middle branch has a
continuous extension which vanishes at both endpoints.  Combined with the
five interior selection theorems above, this is the continuation statement
used by `lem:middle-branch`. -/
theorem middleBranchExtension_continuousOn_gapClosure
    (n j : ℕ) (hj : 0 < j) (hjn : j < n) {r : ℝ} (hr : 0 < r) :
    let lower := symmetricPathEigenvalue n r ⟨j, hjn⟩
    let upper := symmetricPathEigenvalue n r ⟨j - 1, by omega⟩
    ContinuousOn (middleBranchExtension n (r ^ 2) j)
        (Set.Icc lower upper) ∧
      middleBranchExtension n (r ^ 2) j lower = 0 ∧
      middleBranchExtension n (r ^ 2) j upper = 0 := by
  dsimp only
  exact ⟨(continuous_middleBranchExtension n (r ^ 2) j).continuousOn,
    middleBranchExtension_symmetricPathEigenvalue_sq_eq_zero
      n (by omega) j hr ⟨j, hjn⟩,
    middleBranchExtension_symmetricPathEigenvalue_sq_eq_zero
      n (by omega) j hr ⟨j - 1, by omega⟩⟩

end

end ConnectedPseudospectrum
