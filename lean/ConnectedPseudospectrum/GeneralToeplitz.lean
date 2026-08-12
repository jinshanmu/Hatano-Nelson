import ConnectedPseudospectrum.MainTheorem
import ConnectedPseudospectrum.PathComponents
import ConnectedPseudospectrum.SignedPencil
import ConnectedPseudospectrum.VerticalToeplitz
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Homotopy.Contractible

/-!
# Positive-off-diagonal tridiagonal Toeplitz matrices

This module retains the positive-real affine reduction underlying the general
complex-Toeplitz result in the ELA manuscript.  Translation and positive
scaling give an exact affine image
of the normalized path pseudospectrum.  Reversal deals with the opposite
orientation of the two off-diagonals by a unitary conjugation.
-/

namespace ConnectedPseudospectrum

open Matrix Set
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- `tridiag(α,d,β)`, with `α` on the subdiagonal and `β` on the
superdiagonal. -/
def positiveToeplitzMatrix (n : ℕ) (α : ℝ) (d : ℂ) (β : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  d • 1 + (α : ℂ) • complexLowerShift n +
    (β : ℂ) • complexUpperShift n

@[simp] theorem positiveToeplitzMatrix_apply (n : ℕ) (α : ℝ) (d : ℂ)
    (β : ℝ) (i j : Fin n) :
    positiveToeplitzMatrix n α d β i j =
      (if i = j then d else 0) +
        (α : ℂ) * (if i.1 = j.1 + 1 then 1 else 0) +
          (β : ℂ) * (if j.1 = i.1 + 1 then 1 else 0) := by
  simp [positiveToeplitzMatrix, Matrix.one_apply, smul_eq_mul]

/-- If the superdiagonal is larger, the Toeplitz matrix is a translate and
positive multiple of the normalized path matrix. -/
theorem positiveToeplitzMatrix_eq_affine_path_of_lt
    (n : ℕ) {α β : ℝ} (d : ℂ) (hβ : 0 < β) :
    positiveToeplitzMatrix n α d β =
      d • 1 + (β : ℂ) • complexPathMatrix n (α / β) := by
  rw [complexPathMatrix_eq_complex_shifts]
  ext i j
  simp only [positiveToeplitzMatrix, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  push_cast
  field_simp [hβ.ne']
  ring

/-- Complex reversal interchanges the two off-diagonals of the normalized
path matrix. -/
theorem complexReversal_conjugate_complexPathMatrix (n : ℕ) (a : ℝ) :
    complexReversal n * complexPathMatrix n a * complexReversal n =
      complexLowerShift n + (a : ℂ) • complexUpperShift n := by
  change (reversal n).map Complex.ofRealHom *
      (pathMatrix n a).map Complex.ofRealHom *
        (reversal n).map Complex.ofRealHom = _
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  have hreal :
      reversal n * pathMatrix n a * reversal n =
        Matrix.transpose (pathMatrix n a) := by
    calc
      reversal n * pathMatrix n a * reversal n =
          reversal n * (pathMatrix n a * reversal n) := by
            rw [Matrix.mul_assoc]
      _ = reversal n *
          (reversal n * Matrix.transpose (pathMatrix n a)) := by
        rw [pathMatrix_mul_reversal]
      _ = (reversal n * reversal n) *
          Matrix.transpose (pathMatrix n a) := by
        rw [Matrix.mul_assoc]
      _ = Matrix.transpose (pathMatrix n a) := by
        rw [reversal_mul_self, Matrix.one_mul]
  rw [hreal, pathMatrix_transpose_eq_lower_add_upper]
  change (lowerShift n + a • upperShift n).map Complex.ofRealHom =
    (lowerShift n).map Complex.ofRealHom +
      (a : ℂ) • (upperShift n).map Complex.ofRealHom
  rw [Matrix.map_add Complex.ofRealHom
    (fun x y : ℝ => Complex.ofRealHom.map_add x y)
    (lowerShift n) (a • upperShift n)]
  congr 1
  ext i j
  by_cases h : j.1 = i.1 + 1
  · simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, h]
  · simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, h]

/-- If the subdiagonal is larger, reversal reduces the matrix to the same
normalized path family. -/
theorem positiveToeplitzMatrix_eq_reversal_affine_path_of_lt
    (n : ℕ) {α β : ℝ} (d : ℂ) (hα : 0 < α) :
    positiveToeplitzMatrix n α d β =
      complexReversal n *
        (d • 1 + (α : ℂ) • complexPathMatrix n (β / α)) *
          complexReversal n := by
  have hJJ : complexReversal n * complexReversal n = 1 := by
    have hunit := Matrix.mem_unitaryGroup_iff.mp
      (complexReversal_mem_unitary n)
    simpa only [complexReversal_star] using hunit
  symm
  calc
    complexReversal n *
          (d • 1 + (α : ℂ) • complexPathMatrix n (β / α)) *
        complexReversal n =
        d • (complexReversal n * complexReversal n) +
          (α : ℂ) •
            (complexReversal n * complexPathMatrix n (β / α) *
              complexReversal n) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one]
    _ = d • 1 + (α : ℂ) •
          (complexLowerShift n + ((β / α : ℝ) : ℂ) •
            complexUpperShift n) := by
      rw [hJJ, complexReversal_conjugate_complexPathMatrix]
    _ = positiveToeplitzMatrix n α d β := by
      ext i j
      simp only [positiveToeplitzMatrix, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul]
      push_cast
      field_simp [hα.ne']
      ring

/-- The affine map `z ↦ c z + d` used to transport pseudospectra. -/
def pathAffineHomeomorph (c : ℝ) (d : ℂ) (hc : 0 < c) : ℂ ≃ₜ ℂ :=
  affineHomeomorph (c : ℂ) d (Complex.ofReal_ne_zero.mpr hc.ne')

@[simp] theorem pathAffineHomeomorph_apply (c : ℝ) (d z : ℂ)
    (hc : 0 < c) :
    pathAffineHomeomorph c d hc z = (c : ℂ) * z + d :=
  rfl

/-- Translation and positive scaling factor the shifted matrix. -/
theorem generalShift_affine (M : Matrix (Fin n) (Fin n) ℂ)
    (c : ℝ) (d z : ℂ) :
    generalShift (d • 1 + (c : ℂ) • M) ((c : ℂ) * z + d) =
      (c : ℂ) • generalShift M z := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [generalShift]
    ring
  · simp [generalShift, hij]

/-- Least-singular-value height scales exactly under the affine reduction. -/
theorem generalPseudospectralHeight_affine
    (M : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (d z : ℂ) (hc : 0 < c) :
    generalPseudospectralHeight
        (d • 1 + (c : ℂ) • M) ((c : ℂ) * z + d) =
      c * generalPseudospectralHeight M z := by
  unfold generalPseudospectralHeight
  rw [generalShift_affine, leastSingularValue_smul]
  simp [Complex.norm_real, abs_of_pos hc]

/-- Exact affine-image formula for strict pseudospectra. -/
theorem generalPseudospectrum_affine
    (M : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (d : ℂ)
    (hc : 0 < c) (ε : ℝ) :
    generalPseudospectrum (d • 1 + (c : ℂ) • M) ε =
      pathAffineHomeomorph c d hc '' generalPseudospectrum M (ε / c) := by
  let e := pathAffineHomeomorph c d hc
  ext w
  constructor
  · intro hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    change generalPseudospectralHeight M (e.symm w) < ε / c
    apply (lt_div_iff₀ hc).2
    have hw' := hw
    rw [← e.apply_symm_apply w] at hw'
    change generalPseudospectralHeight
      (d • 1 + (c : ℂ) • M)
        ((c : ℂ) * e.symm w + d) < ε at hw'
    rw [generalPseudospectralHeight_affine M c d (e.symm w) hc] at hw'
    simpa only [mul_comm] using hw'
  · rintro ⟨z, hz, rfl⟩
    change generalPseudospectralHeight
      (d • 1 + (c : ℂ) • M) ((c : ℂ) * z + d) < ε
    rw [generalPseudospectralHeight_affine M c d z hc]
    simpa only [mul_comm] using (lt_div_iff₀ hc).1 hz

/-- Connectedness is invariant under the affine reduction. -/
theorem isConnected_generalPseudospectrum_affine_iff
    (M : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (d : ℂ)
    (hc : 0 < c) (ε : ℝ) :
    IsConnected (generalPseudospectrum
      (d • 1 + (c : ℂ) • M) ε) ↔
      IsConnected (generalPseudospectrum M (ε / c)) := by
  rw [generalPseudospectrum_affine]
  exact (pathAffineHomeomorph c d hc).isConnected_image

/-- Conjugation by an involutive unitary preserves every pointwise
pseudospectral height. -/
theorem generalPseudospectralHeight_unitary_involution
    (U M : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hUU : U * U = 1)
    (z : ℂ) :
    generalPseudospectralHeight (U * M * U) z =
      generalPseudospectralHeight M z := by
  have hshift : generalShift (U * M * U) z =
      U * generalShift M z * U := by
    unfold generalShift
    calc
      z • 1 - U * M * U = z • (U * U) - U * M * U := by rw [hUU]
      _ = U * (z • 1) * U - U * M * U := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = U * (z • 1 - M) * U := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
  unfold generalPseudospectralHeight
  rw [hshift,
    leastSingularValue_mul_unitary (U * generalShift M z) U hU,
    leastSingularValue_unitary_mul U (generalShift M z) hU]

/-- Reversal conjugation leaves the full pseudospectrum unchanged. -/
theorem generalPseudospectrum_reversal_conjugate
    (M : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) :
    generalPseudospectrum (complexReversal n * M * complexReversal n) ε =
      generalPseudospectrum M ε := by
  have hU := complexReversal_mem_unitary n
  have hUU : complexReversal n * complexReversal n = 1 := by
    have hunit := Matrix.mem_unitaryGroup_iff.mp hU
    simpa only [complexReversal_star] using hunit
  ext z
  change generalPseudospectralHeight
      (complexReversal n * M * complexReversal n) z < ε ↔
    generalPseudospectralHeight M z < ε
  rw [generalPseudospectralHeight_unitary_involution
    (complexReversal n) M hU hUU z]

/-- Exact normalized pseudospectral formula for positive unequal
off-diagonals. -/
theorem positiveToeplitzPseudospectrum_eq_affine_image
    (n : ℕ) {α β : ℝ} (d : ℂ) (hα : 0 < α) (hβ : 0 < β)
    (hαβ : α ≠ β) (ε : ℝ) :
    generalPseudospectrum (positiveToeplitzMatrix n α d β) ε =
      pathAffineHomeomorph (max α β) d (lt_max_iff.mpr (Or.inl hα)) ''
        pseudospectrum n (min α β / max α β) (ε / max α β) := by
  rcases lt_or_gt_of_ne hαβ with hlt | hgt
  · have hbranch :
        generalPseudospectrum (positiveToeplitzMatrix n α d β) ε =
          pathAffineHomeomorph β d hβ ''
            pseudospectrum n (α / β) (ε / β) := by
      rw [positiveToeplitzMatrix_eq_affine_path_of_lt n d hβ,
        generalPseudospectrum_affine,
        generalPseudospectrum_complexPathMatrix]
    simpa only [min_eq_left hlt.le, max_eq_right hlt.le] using hbranch
  · have hbranch :
        generalPseudospectrum (positiveToeplitzMatrix n α d β) ε =
          pathAffineHomeomorph α d hα ''
            pseudospectrum n (β / α) (ε / α) := by
      rw [positiveToeplitzMatrix_eq_reversal_affine_path_of_lt n d hα,
        generalPseudospectrum_reversal_conjugate,
        generalPseudospectrum_affine,
        generalPseudospectrum_complexPathMatrix]
    simpa only [min_eq_right hgt.le, max_eq_left hgt.le] using hbranch

/-- Historical positive-real specialization of the topological and threshold
assertions now included in `thm:main`. -/
theorem positiveToeplitz_corollary
    (n : ℕ) (hn : 2 ≤ n) {α β : ℝ} (d : ℂ)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≠ β)
    {ε : ℝ} (hε : 0 < ε) :
    let c := max α β
    let a := min α β / c
    (∀ {z : ℂ},
      z ∈ generalPseudospectrum (positiveToeplitzMatrix n α d β) ε →
        ContractibleSpace
          (connectedComponentIn
            (generalPseudospectrum (positiveToeplitzMatrix n α d β) ε) z)) ∧
    (IsConnected
      (generalPseudospectrum (positiveToeplitzMatrix n α d β) ε) ↔
        ε > c * gapBarrier n a) := by
  dsimp only
  have hc : 0 < max α β := lt_max_iff.mpr (Or.inl hα)
  have ha0 : 0 < min α β / max α β :=
    div_pos (lt_min hα hβ) hc
  have hminltmax : min α β < max α β := by
    rcases lt_or_gt_of_ne hαβ with hlt | hgt
    · simpa [min_eq_left hlt.le, max_eq_right hlt.le] using hlt
    · simpa [min_eq_right hgt.le, max_eq_left hgt.le] using hgt
  have ha1 : min α β / max α β < 1 :=
    (div_lt_one hc).2 hminltmax
  have hεc : 0 < ε / max α β := div_pos hε hc
  constructor
  · intro z hz
    rw [positiveToeplitzPseudospectrum_eq_affine_image
      n d hα hβ hαβ ε] at hz ⊢
    rcases hz with ⟨w, hw, rfl⟩
    let e := pathAffineHomeomorph (max α β) d hc
    let C := connectedComponentIn
      (pseudospectrum n (min α β / max α β) (ε / max α β)) w
    let hC : e '' C =
        connectedComponentIn
          (e '' pseudospectrum n (min α β / max α β)
            (ε / max α β)) (e w) :=
      e.image_connectedComponentIn hw
    let hcomponent : C ≃ₜ
        connectedComponentIn
          (e '' pseudospectrum n (min α β / max α β)
            (ε / max α β)) (e w) :=
      (Homeomorph.image e C).trans (Homeomorph.setCongr hC)
    letI : ContractibleSpace C :=
      contractibleSpace_pathPseudospectral_component
        n hn ha0 ha1 hεc hw
    exact hcomponent.symm.contractibleSpace
  · rw [positiveToeplitzPseudospectrum_eq_affine_image
      n d hα hβ hαβ ε,
      (pathAffineHomeomorph (max α β) d hc).isConnected_image,
      isConnected_pathPseudospectrum_iff_gapBarrier_lt
        n hn ha0 ha1 hεc]
    constructor
    · intro h
      have := (lt_div_iff₀ hc).1 h
      simpa [mul_comm] using this
    · intro h
      apply (lt_div_iff₀ hc).2
      simpa [mul_comm] using h

/-- The scaled Toeplitz barriers inherit strict dimension decrease. -/
theorem positiveToeplitz_scaled_barrier_succ_lt
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≠ β)
    {n : ℕ} (hn : 2 ≤ n) :
    max α β * gapBarrier (n + 1) (min α β / max α β) <
      max α β * gapBarrier n (min α β / max α β) := by
  have hc : 0 < max α β := lt_max_iff.mpr (Or.inl hα)
  have ha0 : 0 < min α β / max α β :=
    div_pos (lt_min hα hβ) hc
  have hminltmax : min α β < max α β := by
    rcases lt_or_gt_of_ne hαβ with hlt | hgt
    · simpa [min_eq_left hlt.le, max_eq_right hlt.le] using hlt
    · simpa [min_eq_right hgt.le, max_eq_left hgt.le] using hgt
  have ha1 : min α β / max α β < 1 := (div_lt_one hc).2 hminltmax
  exact mul_lt_mul_of_pos_left
    (gapBarrier_succ_lt n hn ha0 ha1) hc

/-- The quantitative lower and upper barriers transfer by multiplication by
the Toeplitz scale `c = max α β`. -/
theorem positiveToeplitz_scaled_barrier_bounds
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≠ β)
    {n : ℕ} (hn : 2 ≤ n) :
    max α β * lowerBarrier n (min α β / max α β) ≤
        max α β * gapBarrier n (min α β / max α β) ∧
      max α β * gapBarrier n (min α β / max α β) ≤
        max α β * upperBarrier n (min α β / max α β) := by
  have hc : 0 < max α β := lt_max_iff.mpr (Or.inl hα)
  have ha0 : 0 < min α β / max α β :=
    div_pos (lt_min hα hβ) hc
  have hminltmax : min α β < max α β := by
    rcases lt_or_gt_of_ne hαβ with hlt | hgt
    · simpa [min_eq_left hlt.le, max_eq_right hlt.le] using hlt
    · simpa [min_eq_right hgt.le, max_eq_left hgt.le] using hgt
  have ha1 : min α β / max α β < 1 := (div_lt_one hc).2 hminltmax
  exact ⟨mul_le_mul_of_nonneg_left
      (lowerBarrier_le_gapBarrier n hn ha0 ha1) hc.le,
    mul_le_mul_of_nonneg_left
      (gapBarrier_le_upperBarrier hn (min α β / max α β) ha0) hc.le⟩

/-- The connected dimensions of the Toeplitz family are exactly the tail
beginning at the normalized critical threshold. -/
theorem positiveToeplitz_connectedDimensions_eq_criticalThreshold_tail
    {α β : ℝ} (d : ℂ) (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≠ β)
    {ε : ℝ} (hε : 0 < ε) :
    {n : ℕ | 2 ≤ n ∧
      IsConnected
        (generalPseudospectrum (positiveToeplitzMatrix n α d β) ε)} =
      {n : ℕ | criticalThreshold (min α β / max α β) (ε / max α β) ≤ n} := by
  have hc : 0 < max α β := lt_max_iff.mpr (Or.inl hα)
  have ha0 : 0 < min α β / max α β :=
    div_pos (lt_min hα hβ) hc
  have hminltmax : min α β < max α β := by
    rcases lt_or_gt_of_ne hαβ with hlt | hgt
    · simpa [min_eq_left hlt.le, max_eq_right hlt.le] using hlt
    · simpa [min_eq_right hgt.le, max_eq_left hgt.le] using hgt
  have ha1 : min α β / max α β < 1 := (div_lt_one hc).2 hminltmax
  have hεc : 0 < ε / max α β := div_pos hε hc
  have hcriterion : ∀ {n : ℕ}, 2 ≤ n →
      (ConnectedAtSize n (min α β / max α β) (ε / max α β) ↔
        gapBarrier n (min α β / max α β) < ε / max α β) := by
    intro n hn
    exact isConnected_pathPseudospectrum_iff_gapBarrier_lt
      n hn ha0 ha1 hεc
  have hstrict : ∀ {n : ℕ}, 2 ≤ n →
      gapBarrier (n + 1) (min α β / max α β) <
        gapBarrier n (min α β / max α β) := by
    intro n hn
    exact gapBarrier_succ_lt n hn ha0 ha1
  rw [← connectedDimensions_eq_criticalThreshold_tail
    ha0 ha1 hεc hcriterion hstrict]
  ext n
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hn, hconn⟩
    refine ⟨hn, ?_⟩
    rw [positiveToeplitzPseudospectrum_eq_affine_image
      n d hα hβ hαβ ε] at hconn
    exact ((pathAffineHomeomorph (max α β) d hc).isConnected_image).1 hconn
  · rintro ⟨hn, hconn⟩
    refine ⟨hn, ?_⟩
    rw [positiveToeplitzPseudospectrum_eq_affine_image
      n d hα hβ hαβ ε]
    exact ((pathAffineHomeomorph (max α β) d hc).isConnected_image).2 hconn

/-- The normalized critical threshold is literally the first connected
dimension of the positive-off-diagonal Toeplitz family. -/
theorem positiveToeplitz_firstConnectedDimension_isLeast
    {α β : ℝ} (d : ℂ) (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≠ β)
    {ε : ℝ} (hε : 0 < ε) :
    IsLeast
      {n : ℕ | 2 ≤ n ∧
        IsConnected
          (generalPseudospectrum (positiveToeplitzMatrix n α d β) ε)}
      (criticalThreshold (min α β / max α β) (ε / max α β)) := by
  rw [positiveToeplitz_connectedDimensions_eq_criticalThreshold_tail
    d hα hβ hαβ hε]
  constructor
  · simp
  · intro n hn
    exact hn

/-- Replacing the normalized uncertainty by `ε / c`, for a fixed positive
scale `c`, preserves the manuscript's critical-size asymptotic with the
physical uncertainty `ε`. -/
theorem criticalThreshold_div_hasCriticalSizeAsymptotic
    {a c : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hc : 0 < c) :
    HasCriticalSizeAsymptotic (fun ε => criticalThreshold a (ε / c)) a := by
  have hbase : HasCriticalSizeAsymptotic (criticalThreshold a) a :=
    (main_theorem ha0 ha1 zero_lt_one).2.2.2.1
  unfold HasCriticalSizeAsymptotic at hbase ⊢
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
  have hcomp := hbase.comp_pos_mul hcinv
  have hr : 0 < pathRate a := Real.sqrt_pos.2 ha0
  have hr1 : pathRate a < 1 := by
    unfold pathRate
    simpa using (Real.sqrt_lt_sqrt_iff ha0.le).2 ha1
  have hstable := tailInversionScale_mul_stable hr hr1 hcinv
  have hstable' :
      BoundedErrorAtZero (fun ε => criticalScale a (c⁻¹ * ε))
        (criticalScale a) := by
    convert hstable using 1 <;> funext ε
    · exact (tailInversionScale_pathRate_eq_criticalScale
        ha0 ha1 (c⁻¹ * ε)).symm
    · exact (tailInversionScale_pathRate_eq_criticalScale ha0 ha1 ε).symm
  have hcomp' :
      BoundedErrorAtZero
        (fun ε => (criticalThreshold a (ε / c) : ℝ))
        (fun ε => criticalScale a (c⁻¹ * ε)) := by
    simpa only [div_eq_mul_inv, mul_comm] using hcomp
  exact hcomp'.trans hstable'

/-- Explicit transfer of the canonical theorem's threshold bounds, physical-
uncertainty asymptotic, and exact size-two endpoint. -/
theorem positiveToeplitz_threshold_bounds_and_asymptotic
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≠ β)
    {ε : ℝ} (hε : 0 < ε) :
    let c := max α β
    let a := min α β / c
    (1 + lowerObstructionMaximum a (ε / c) ≤
        criticalThreshold a (ε / c) ∧
      criticalThreshold a (ε / c) ≤
        upperBarrierThreshold a (ε / c)) ∧
    HasCriticalSizeAsymptotic (fun δ => criticalThreshold a (δ / c)) a ∧
    (criticalThreshold a (ε / c) = 2 ↔ ε > c * a) := by
  dsimp only
  have hc : 0 < max α β := lt_max_iff.mpr (Or.inl hα)
  have ha0 : 0 < min α β / max α β :=
    div_pos (lt_min hα hβ) hc
  have hminltmax : min α β < max α β := by
    rcases lt_or_gt_of_ne hαβ with hlt | hgt
    · simpa [min_eq_left hlt.le, max_eq_right hlt.le] using hlt
    · simpa [min_eq_right hgt.le, max_eq_left hgt.le] using hgt
  have ha1 : min α β / max α β < 1 := (div_lt_one hc).2 hminltmax
  have hεc : 0 < ε / max α β := div_pos hε hc
  rcases main_theorem ha0 ha1 hεc with ⟨_, _, hthreshold, hasymptotic⟩
  rcases hthreshold with
    ⟨_, _, _, _, _, _, hlower, hupper, _⟩
  have hphysicalTwo :
      (ε / max α β > min α β / max α β ↔
        ε > max α β * (min α β / max α β)) := by
    constructor
    · intro h
      have := (lt_div_iff₀ hc).1 h
      simpa [mul_comm] using this
    · intro h
      apply (lt_div_iff₀ hc).2
      simpa [mul_comm] using h
  exact ⟨⟨hlower, hupper⟩,
    criticalThreshold_div_hasCriticalSizeAsymptotic ha0 ha1 hc,
    hasymptotic.2.trans hphysicalTwo⟩

end

end ConnectedPseudospectrum
