import ConnectedPseudospectrum.BoundaryCases
import ConnectedPseudospectrum.ComplexToeplitz
import ConnectedPseudospectrum.HermitianSingularValues
import ConnectedPseudospectrum.VerticalTopology

/-!
# Normal Toeplitz boundary

The canonical endpoint `A_n(1)` is Hermitian.  This module diagonalizes its
shift, identifies its strict pseudospectrum with the union of equal open
disks about the explicit Dirichlet eigenvalues, and records the resulting
vertical contraction.  These are the matrix-level inputs for the exact
normal connectedness threshold in Proposition 3.2 of the ELA manuscript.
-/

namespace ConnectedPseudospectrum

open Matrix Set
open scoped ComplexOrder

noncomputable section

private theorem gramShift_diagonal_complex {n : ℕ}
    (f : Fin n → ℂ) (t : ℝ) :
    gramShift (Matrix.diagonal f) t =
      Matrix.diagonal fun i : Fin n => (((‖f i‖ ^ 2 - t ^ 2 : ℝ) : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [gramShift, pow_two, Complex.conj_mul']
  · simp [gramShift, hij]

/-- The least singular value of a nonempty complex diagonal matrix is the
smallest modulus of a diagonal entry, with the minimum attained. -/
theorem exists_diagonal_complex_entry_eq_leastSingularValue
    {n : ℕ} (hn : 0 < n) (f : Fin n → ℂ) :
    ∃ i : Fin n,
      leastSingularValue (Matrix.diagonal f) = ‖f i‖ ∧
        ∀ j : Fin n, leastSingularValue (Matrix.diagonal f) ≤ ‖f j‖ := by
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal f
  let s : ℝ := leastSingularValue D
  have hs : 0 ≤ s := leastSingularValue_nonneg D
  have hsemidef : (gramShift D s).PosSemidef :=
    gramShift_leastSingularValue_posSemidef D hn
  have hnotdef : ¬(gramShift D s).PosDef := by
    rw [gramShift_posDef_iff_lt_leastSingularValue D hn s hs]
    exact lt_irrefl s
  have hnotunit : ¬IsUnit (gramShift D s) := by
    intro hunit
    exact hnotdef (hsemidef.posDef_iff_isUnit.mpr hunit)
  have hdet : (gramShift D s).det = 0 := by
    by_contra hne
    apply hnotunit
    exact (Matrix.isUnit_iff_isUnit_det (gramShift D s)).mpr
      (isUnit_iff_ne_zero.mpr hne)
  have hgram : gramShift D s =
      Matrix.diagonal fun i : Fin n => (((‖f i‖ ^ 2 - s ^ 2 : ℝ) : ℂ)) := by
    exact gramShift_diagonal_complex f s
  rw [hgram, Matrix.det_diagonal] at hdet
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hdet
  have hiReal : ‖f i‖ ^ 2 - s ^ 2 = 0 := by exact_mod_cast hi
  have his : s = ‖f i‖ := by
    nlinarith [norm_nonneg (f i)]
  have hall : ∀ j : Fin n, s ≤ ‖f j‖ := by
    intro j
    let v : ComplexEuclidean n := WithLp.toLp 2 (Pi.single j (1 : ℂ))
    have hv : ‖v‖ = 1 := by simp [v]
    calc
      s = leastSingularValue D := rfl
      _ ≤ ‖matrixOperator D v‖ := leastSingularValue_le D hn v hv
      _ = ‖f j‖ := by
        rw [show v = WithLp.toLp 2 (Pi.single j (1 : ℂ)) from rfl,
          matrixOperator_toLp, show D = Matrix.diagonal f from rfl,
          Matrix.diagonal_mulVec_single, PiLp.norm_toLp_single, mul_one]
  exact ⟨i, his, hall⟩

/-- Unitary diagonalization turns the shifted Hermitian endpoint into the
diagonal list `z - lambda_i`. -/
private theorem leastSingularValue_shift_normal_eq_diagonal
    (n : ℕ) (z : ℂ) :
    let hA := complexPathMatrix_one_isHermitian n
    leastSingularValue (shiftedPathMatrix n 1 z) =
      leastSingularValue
        (Matrix.diagonal fun i : Fin n => z - (hA.eigenvalues i : ℂ)) := by
  dsimp only
  let A := complexPathMatrix n 1
  let hA : A.IsHermitian := complexPathMatrix_one_isHermitian n
  let U : Matrix (Fin n) (Fin n) ℂ := hA.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal fun i : Fin n => z - (hA.eigenvalues i : ℂ)
  have hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    hA.eigenvectorUnitary.property
  have hUstar : star U ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    Unitary.star_mem hU
  have hspectral : A = U *
      Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    exact hA.spectral_theorem
  have hUstarMul : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hD : D = z • (1 : Matrix (Fin n) (Fin n) ℂ) -
      Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, hij]
  have hshift : shiftedPathMatrix n 1 z = U * D * star U := by
    change z • 1 - A = U * D * star U
    rw [hspectral, hD, Matrix.mul_sub, Matrix.sub_mul]
    simp [hUstarMul]
  calc
    leastSingularValue (shiftedPathMatrix n 1 z) =
        leastSingularValue (U * D * star U) := by rw [hshift]
    _ = leastSingularValue (U * D) :=
      leastSingularValue_mul_unitary (U * D) (star U) hUstar
    _ = leastSingularValue D := leastSingularValue_unitary_mul U D hU

/-- Exact normal-matrix formula: the endpoint pseudospectrum is the union of
open disks of radius `epsilon` about the explicit path eigenvalues. -/
theorem pseudospectrum_one_eq_iUnion_balls
    (n : ℕ) (hn : 0 < n) (ε : ℝ) :
    pseudospectrum n 1 ε =
      ⋃ k : Fin n, Metric.ball (pathEigenvalue n 1 k : ℂ) ε := by
  let A := complexPathMatrix n 1
  let hA : A.IsHermitian := complexPathMatrix_one_isHermitian n
  ext z
  rw [mem_iUnion]
  change pseudospectralHeight n 1 z < ε ↔ _
  rw [pseudospectralHeight, leastSingularValue_shift_normal_eq_diagonal]
  obtain ⟨i, hi, hall⟩ :=
    exists_diagonal_complex_entry_eq_leastSingularValue hn
      (fun i : Fin n => z - (hA.eigenvalues i : ℂ))
  constructor
  · intro hz
    have hieig : (hA.eigenvalues i : ℂ) ∈ spectrum ℂ A := by
      rw [hA.spectrum_eq_image_range]
      exact ⟨hA.eigenvalues i, ⟨i, rfl⟩, rfl⟩
    have hidet : (shiftedPathMatrix n 1 (hA.eigenvalues i : ℂ)).det = 0 := by
      exact (mem_spectrum_iff_det_generalShift_eq_zero A
        (hA.eigenvalues i : ℂ)).1 hieig
    obtain ⟨k, hk⟩ :=
      (det_shiftedPathMatrix_eq_zero_iff n zero_lt_one _).1 hidet
    refine ⟨k, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, ← hk, ← hi]
    exact hz
  · rintro ⟨k, hk⟩
    have hnodeSpec : (pathEigenvalue n 1 k : ℂ) ∈ spectrum ℂ A := by
      apply (mem_spectrum_iff_det_generalShift_eq_zero A _).2
      exact det_shiftedPathMatrix_pathEigenvalue n zero_lt_one k
    rw [hA.spectrum_eq_image_range] at hnodeSpec
    obtain ⟨lam, ⟨j, rfl⟩, hlam⟩ := hnodeSpec
    rw [Metric.mem_ball, dist_eq_norm, ← hlam] at hk
    exact (hall j).trans_lt hk

/-- The normal endpoint is vertically closed because each disk in the exact
union has a real center. -/
theorem verticalScalingClosed_pseudospectrum_one
    (n : ℕ) (hn : 0 < n) (ε : ℝ) :
    VerticalScalingClosed (pseudospectrum n 1 ε) := by
  rw [pseudospectrum_one_eq_iUnion_balls n hn ε]
  intro z hz t ht
  rw [mem_iUnion] at hz ⊢
  obtain ⟨k, hk⟩ := hz
  refine ⟨k, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hk ⊢
  have hsq : ‖verticalScale t z - (pathEigenvalue n 1 k : ℂ)‖ ^ 2 ≤
      ‖z - (pathEigenvalue n 1 k : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [verticalScale]
    simp
    have htSq : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
    have hprod := mul_nonneg htSq (sq_nonneg z.im)
    nlinarith
  nlinarith [norm_nonneg (verticalScale t z - (pathEigenvalue n 1 k : ℂ)),
    norm_nonneg (z - (pathEigenvalue n 1 k : ℂ))]

/-- Every connected component of the strict normal endpoint
pseudospectrum is contractible. -/
theorem contractibleSpace_pseudospectrum_one_component
    (n : ℕ) (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : z ∈ pseudospectrum n 1 ε) :
    ContractibleSpace (connectedComponentIn (pseudospectrum n 1 ε) z) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact contractibleSpace_pseudospectral_component_of_vertical
    m zero_lt_one hε
      (verticalScalingClosed_pseudospectrum_one (m + 1) (by omega) ε) hz

end

end ConnectedPseudospectrum
