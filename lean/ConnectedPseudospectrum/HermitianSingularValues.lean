import ConnectedPseudospectrum.HermitianLeastSingular
import ConnectedPseudospectrum.SignedPencil

/-!
# Least singular values of Hermitian matrices

For a positive-dimensional Hermitian complex matrix, the attained Euclidean
least singular value is the least absolute value among Mathlib's ordered real
Hermitian eigenvalues.  The proof uses the unitary spectral theorem while
retaining the project's sphere-minimum definition of `leastSingularValue`.
-/

namespace ConnectedPseudospectrum

open Matrix
open scoped ComplexOrder

noncomputable section

private theorem gramShift_diagonal_real {n : ℕ} (f : Fin n → ℝ) (t : ℝ) :
    gramShift (diagonal fun i : Fin n => (f i : ℂ)) t =
      diagonal fun i : Fin n => (((f i) ^ 2 - t ^ 2 : ℝ) : ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [gramShift, pow_two]
  · simp [gramShift, hij]

private theorem exists_diagonal_real_leastSingularValue_eigenvalue
    {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    ∃ i : Fin n,
      leastSingularValue (diagonal fun j : Fin n => (f j : ℂ)) = |f i| ∧
        ∀ j : Fin n,
          leastSingularValue (diagonal fun k : Fin n => (f k : ℂ)) ≤ |f j| := by
  let D : Matrix (Fin n) (Fin n) ℂ :=
    diagonal fun i : Fin n => (f i : ℂ)
  let s : ℝ := leastSingularValue D
  have hs : 0 ≤ s := leastSingularValue_nonneg D
  have hposSemidef : (gramShift D s).PosSemidef :=
    gramShift_leastSingularValue_posSemidef D hn
  have hnotPosDef : ¬(gramShift D s).PosDef := by
    rw [gramShift_posDef_iff_lt_leastSingularValue D hn s hs]
    exact lt_irrefl s
  have hnotUnit : ¬IsUnit (gramShift D s) := by
    intro hunit
    exact hnotPosDef (hposSemidef.posDef_iff_isUnit.mpr hunit)
  have hdet : (gramShift D s).det = 0 := by
    by_contra hne
    apply hnotUnit
    exact (Matrix.isUnit_iff_isUnit_det (gramShift D s)).mpr
      (isUnit_iff_ne_zero.mpr hne)
  have hgram :
      gramShift D s =
        diagonal fun i : Fin n => (((f i) ^ 2 - s ^ 2 : ℝ) : ℂ) := by
    exact gramShift_diagonal_real f s
  rw [hgram, Matrix.det_diagonal] at hdet
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hdet
  have hiReal : f i ^ 2 - s ^ 2 = 0 := by
    exact_mod_cast hi
  have hiAbsSq : |f i| ^ 2 = s ^ 2 := by
    rw [sq_abs]
    linarith
  have his : s = |f i| := by
    nlinarith [abs_nonneg (f i)]
  have hall : ∀ j : Fin n, s ≤ |f j| := by
    intro j
    let v : ComplexEuclidean n := WithLp.toLp 2 (Pi.single j (1 : ℂ))
    have hv : ‖v‖ = 1 := by
      simp [v]
    calc
      s = leastSingularValue D := rfl
      _ ≤ ‖matrixOperator D v‖ := leastSingularValue_le D hn v hv
      _ = |f j| := by
        rw [show v = WithLp.toLp 2 (Pi.single j (1 : ℂ)) from rfl,
          matrixOperator_toLp, show D = diagonal (fun i : Fin n => (f i : ℂ)) from rfl,
          Matrix.diagonal_mulVec_single, PiLp.norm_toLp_single]
        rw [mul_one, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨i, ?_, ?_⟩
  · change s = |f i|
    exact his
  · intro j
    change s ≤ |f j|
    exact hall j

/-- The attained Euclidean least singular value of a positive-dimensional
Hermitian matrix is the absolute value of one of its Hermitian eigenvalues,
and no other Hermitian eigenvalue has smaller absolute value. -/
theorem exists_eigenvalue_abs_eq_leastSingularValue_of_isHermitian
    {n : ℕ} (hn : 0 < n) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) :
    ∃ i : Fin n,
      leastSingularValue A = |hA.eigenvalues i| ∧
        ∀ j : Fin n, leastSingularValue A ≤ |hA.eigenvalues j| := by
  let D : Matrix (Fin n) (Fin n) ℂ :=
    diagonal fun i : Fin n => (hA.eigenvalues i : ℂ)
  let U : Matrix (Fin n) (Fin n) ℂ := hA.eigenvectorUnitary
  have hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    exact hA.eigenvectorUnitary.property
  have hUstar : star U ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    Unitary.star_mem hU
  have hspectral : A = U * D * star U := by
    calc
      A = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := hA.spectral_theorem
      _ = U * D * star U := by
        rfl
  have hleast : leastSingularValue A = leastSingularValue D := by
    calc
      leastSingularValue A = leastSingularValue (U * D * star U) :=
        congrArg leastSingularValue hspectral
      _ = leastSingularValue (U * D) :=
        leastSingularValue_mul_unitary (U * D) (star U) hUstar
      _ = leastSingularValue D :=
        leastSingularValue_unitary_mul U D hU
  obtain ⟨i, hi, hall⟩ :=
    exists_diagonal_real_leastSingularValue_eigenvalue hn hA.eigenvalues
  refine ⟨i, ?_, ?_⟩
  · calc
      leastSingularValue A = leastSingularValue D := hleast
      _ = |hA.eigenvalues i| := hi
  · intro j
    calc
      leastSingularValue A = leastSingularValue D := hleast
      _ ≤ |hA.eigenvalues j| := hall j

/-- The complex cast of the real symmetric signed-middle matrix is
Hermitian. -/
theorem complexSignedMiddleMatrix_isHermitian (n : ℕ) (a x : ℝ) :
    ((signedMiddleMatrix n a x).map Complex.ofRealHom).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [Matrix.conjTranspose_apply,
    (signedMiddleMatrix_isSymm n a x).apply i j]

/-- Every Hermitian eigenvalue of the complex-cast signed-middle matrix is
an actual real root of the paper's signed determinant pencil. -/
theorem signedPencilDet_eigenvalue_eq_zero (n : ℕ) (a x : ℝ) (i : Fin n) :
    signedPencilDet n a x
        ((complexSignedMiddleMatrix_isHermitian n a x).eigenvalues i) = 0 := by
  rw [signedPencilDet_eq_zero_iff]
  let B : Matrix (Fin n) (Fin n) ℝ := signedMiddleMatrix n a x
  let C : Matrix (Fin n) (Fin n) ℂ := B.map Complex.ofRealHom
  let hC : C.IsHermitian := complexSignedMiddleMatrix_isHermitian n a x
  let s : ℝ := hC.eigenvalues i
  change (B - s • (1 : Matrix (Fin n) (Fin n) ℝ)).det = 0
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
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    let v : Fin n → ℂ := ⇑(hC.eigenvectorBasis i)
    have hv : v ≠ 0 := by
      exact (WithLp.ofLp_eq_zero 2).ne.2
        (hC.eigenvectorBasis.orthonormal.ne_zero i)
    refine ⟨v, hv, ?_⟩
    calc
      (C - (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v =
          C *ᵥ v - (s : ℂ) • v := by
        rw [sub_mulVec, smul_mulVec, one_mulVec]
      _ = s • v - (s : ℂ) • v := by
        exact congrArg (fun w : Fin n → ℂ => w - (s : ℂ) • v)
          (hC.mulVec_eigenvectorBasis i)
      _ = 0 := by
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ) s v]
        exact sub_self ((s : ℂ) • v)
  have hcast :
      (((B - s • (1 : Matrix (Fin n) (Fin n) ℝ)).det : ℝ) : ℂ) = 0 := by
    change Complex.ofRealHom
      ((B - s • (1 : Matrix (Fin n) (Fin n) ℝ)).det) = 0
    rw [Complex.ofRealHom.map_det, RingHom.mapMatrix_apply, hmap]
    exact hdetComplex
  exact Complex.ofReal_injective hcast

/-- On the real axis, the pseudospectral height is the absolute value of an
actual Hermitian eigenvalue of the signed-middle matrix, and is the least
absolute value among all those eigenvalues. -/
theorem exists_signedMiddleMatrix_eigenvalue_abs_eq_pseudospectralHeight
    (n : ℕ) (hn : 0 < n) (a x : ℝ) :
    ∃ i : Fin n,
      pseudospectralHeight n a (x : ℂ) =
          |(complexSignedMiddleMatrix_isHermitian n a x).eigenvalues i| ∧
        ∀ j : Fin n,
          pseudospectralHeight n a (x : ℂ) ≤
            |(complexSignedMiddleMatrix_isHermitian n a x).eigenvalues j| := by
  have h := exists_eigenvalue_abs_eq_leastSingularValue_of_isHermitian hn
    (complexSignedMiddleMatrix_isHermitian n a x)
  rw [leastSingularValue_signedMiddleMatrix] at h
  exact h

/-- Consequently, the real-axis pseudospectral height is the absolute value
of a real root of the signed determinant pencil. -/
theorem exists_signedPencil_root_abs_eq_pseudospectralHeight
    (n : ℕ) (hn : 0 < n) (a x : ℝ) :
    ∃ s : ℝ,
      signedPencilDet n a x s = 0 ∧
        pseudospectralHeight n a (x : ℂ) = |s| := by
  obtain ⟨i, hi, _⟩ :=
    exists_signedMiddleMatrix_eigenvalue_abs_eq_pseudospectralHeight n hn a x
  exact ⟨(complexSignedMiddleMatrix_isHermitian n a x).eigenvalues i,
    signedPencilDet_eigenvalue_eq_zero n a x i, hi⟩

end

end ConnectedPseudospectrum
