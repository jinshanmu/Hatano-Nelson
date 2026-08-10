import ConnectedPseudospectrum.GeneralToeplitz
import ConnectedPseudospectrum.PseudospectralComponents
import ConnectedPseudospectrum.HermitianPathSpectrum
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Complex tridiagonal Toeplitz matrices

This module upgrades the positive-real reduction in `GeneralToeplitz` to
arbitrary complex off-diagonals.  A diagonal unitary removes their relative
phase.  Translation, rotation and positive scaling then reduce every matrix
with two nonzero off-diagonals to the normalized path family; reversal is
used when the subdiagonal has the larger modulus.

The singular boundary is treated separately.  If exactly one off-diagonal
vanishes, the spectrum is the singleton consisting of the diagonal entry and
the positive strict pseudospectrum is connected in every dimension.  If both
vanish, the pseudospectrum is the corresponding open disk.  Equal nonzero
moduli reduce exactly to the normal endpoint `a = 1`.
-/

namespace ConnectedPseudospectrum

open Matrix Set
open scoped ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

noncomputable section

/-- The complex matrix `tridiag(α,d,β)`, with `α` below and `β` above the
diagonal. -/
def complexToeplitzMatrix (n : ℕ) (α d β : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  d • 1 + α • complexLowerShift n + β • complexUpperShift n

@[simp] theorem complexToeplitzMatrix_apply (n : ℕ) (α d β : ℂ)
    (i j : Fin n) :
    complexToeplitzMatrix n α d β i j =
      (if i = j then d else 0) +
        α * (if i.1 = j.1 + 1 then 1 else 0) +
          β * (if j.1 = i.1 + 1 then 1 else 0) := by
  simp [complexToeplitzMatrix, Matrix.one_apply, smul_eq_mul]

/-! ## Complex affine and unitary invariance -/

/-- The complex affine homeomorphism `z ↦ c z + d`. -/
def complexAffineHomeomorph (c d : ℂ) (hc : c ≠ 0) : ℂ ≃ₜ ℂ :=
  affineHomeomorph c d hc

@[simp] theorem complexAffineHomeomorph_apply (c d z : ℂ) (hc : c ≠ 0) :
    complexAffineHomeomorph c d hc z = c * z + d :=
  rfl

/-- Translation and nonzero complex scaling factor the shifted matrix. -/
theorem generalShift_complexAffine (M : Matrix (Fin n) (Fin n) ℂ)
    (c d z : ℂ) :
    generalShift (d • 1 + c • M) (c * z + d) =
      c • generalShift M z := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [generalShift]
    ring
  · simp [generalShift, hij]

/-- Least-singular-value height scales by the modulus of a complex affine
factor. -/
theorem generalPseudospectralHeight_complexAffine
    (M : Matrix (Fin n) (Fin n) ℂ) (c d z : ℂ) :
    generalPseudospectralHeight (d • 1 + c • M) (c * z + d) =
      ‖c‖ * generalPseudospectralHeight M z := by
  unfold generalPseudospectralHeight
  rw [generalShift_complexAffine, leastSingularValue_smul]

/-- Exact affine-image formula for an arbitrary nonzero complex scale. -/
theorem generalPseudospectrum_complexAffine
    (M : Matrix (Fin n) (Fin n) ℂ) (c d : ℂ) (hc : c ≠ 0) (ε : ℝ) :
    generalPseudospectrum (d • 1 + c • M) ε =
      complexAffineHomeomorph c d hc ''
        generalPseudospectrum M (ε / ‖c‖) := by
  let e := complexAffineHomeomorph c d hc
  have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
  ext w
  constructor
  · intro hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    change generalPseudospectralHeight M (e.symm w) < ε / ‖c‖
    apply (lt_div_iff₀ hcnorm).2
    have hw' := hw
    rw [← e.apply_symm_apply w] at hw'
    change generalPseudospectralHeight
      (d • 1 + c • M) (c * e.symm w + d) < ε at hw'
    rw [generalPseudospectralHeight_complexAffine] at hw'
    simpa only [mul_comm] using hw'
  · rintro ⟨z, hz, rfl⟩
    change generalPseudospectralHeight (d • 1 + c • M) (c * z + d) < ε
    rw [generalPseudospectralHeight_complexAffine]
    simpa only [mul_comm] using (lt_div_iff₀ hcnorm).1 hz

/-- Unitary similarity preserves pointwise pseudospectral height. -/
theorem generalPseudospectralHeight_unitary_conjugate
    (U M : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (z : ℂ) :
    generalPseudospectralHeight (U.conjTranspose * M * U) z =
      generalPseudospectralHeight M z := by
  have hUstar : U.conjTranspose ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    Unitary.star_mem hU
  have hstarU : U.conjTranspose * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hUstar
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using h
  have hshift : generalShift (U.conjTranspose * M * U) z =
      U.conjTranspose * generalShift M z * U := by
    unfold generalShift
    calc
      z • 1 - U.conjTranspose * M * U =
          z • (U.conjTranspose * U) - U.conjTranspose * M * U := by
        rw [hstarU]
      _ = U.conjTranspose * (z • 1) * U - U.conjTranspose * M * U := by
        rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = U.conjTranspose * (z • 1 - M) * U := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
  unfold generalPseudospectralHeight
  rw [hshift,
    leastSingularValue_mul_unitary (U.conjTranspose * generalShift M z) U hU,
    leastSingularValue_unitary_mul U.conjTranspose (generalShift M z) hUstar]

/-- Unitary similarity preserves the full strict pseudospectrum. -/
theorem generalPseudospectrum_unitary_conjugate
    (U M : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (ε : ℝ) :
    generalPseudospectrum (U.conjTranspose * M * U) ε =
      generalPseudospectrum M ε := by
  ext z
  change generalPseudospectralHeight (U.conjTranspose * M * U) z < ε ↔
    generalPseudospectralHeight M z < ε
  rw [generalPseudospectralHeight_unitary_conjugate U M hU z]

/-! ## Phase gauge -/

/-- Relative phase used by the diagonal unitary gauge. -/
def toeplitzGaugePhase (α β : ℂ) : ℂ :=
  Complex.exp (((((α.arg - β.arg) / 2 : ℝ)) : ℂ) * Complex.I)

/-- Common direction of the two gauged off-diagonals. -/
def toeplitzDirection (α β : ℂ) : ℂ :=
  Complex.exp (((((α.arg + β.arg) / 2 : ℝ)) : ℂ) * Complex.I)

/-- Diagonal unitary implementing the complex Toeplitz phase gauge. -/
def complexToeplitzGauge (n : ℕ) (α β : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i : Fin n => toeplitzGaugePhase α β ^ i.1

theorem toeplitzGaugePhase_norm (α β : ℂ) :
    ‖toeplitzGaugePhase α β‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I ((α.arg - β.arg) / 2)

theorem toeplitzDirection_norm (α β : ℂ) :
    ‖toeplitzDirection α β‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I ((α.arg + β.arg) / 2)

theorem toeplitzDirection_ne_zero (α β : ℂ) :
    toeplitzDirection α β ≠ 0 :=
  Complex.exp_ne_zero _

private theorem star_toeplitzGaugePhase_mul_self (α β : ℂ) :
    star (toeplitzGaugePhase α β) * toeplitzGaugePhase α β = 1 := by
  rw [show star (toeplitzGaugePhase α β) =
      (starRingEnd ℂ) (toeplitzGaugePhase α β) from rfl,
    Complex.conj_mul', toeplitzGaugePhase_norm]
  norm_num

private theorem toeplitzGaugePhase_mul_star_self (α β : ℂ) :
    toeplitzGaugePhase α β * star (toeplitzGaugePhase α β) = 1 := by
  rw [mul_comm, star_toeplitzGaugePhase_mul_self]

@[simp] theorem complexToeplitzGauge_star_mul_self
    (n : ℕ) (α β : ℂ) :
    (complexToeplitzGauge n α β).conjTranspose *
      complexToeplitzGauge n α β = 1 := by
  rw [complexToeplitzGauge, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  apply Matrix.diagonal_eq_diagonal_iff.mpr
  intro i
  rw [Pi.star_apply, star_pow, ← mul_pow,
    star_toeplitzGaugePhase_mul_self, one_pow]

@[simp] theorem complexToeplitzGauge_mul_star_self
    (n : ℕ) (α β : ℂ) :
    complexToeplitzGauge n α β *
      (complexToeplitzGauge n α β).conjTranspose = 1 := by
  rw [complexToeplitzGauge, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  apply Matrix.diagonal_eq_diagonal_iff.mpr
  intro i
  rw [Pi.star_apply, star_pow, ← mul_pow,
    toeplitzGaugePhase_mul_star_self, one_pow]

theorem complexToeplitzGauge_mem_unitary (n : ℕ) (α β : ℂ) :
    complexToeplitzGauge n α β ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  Matrix.mem_unitaryGroup_iff.mpr (complexToeplitzGauge_mul_star_self n α β)

private theorem complexToeplitzGauge_conj_upper
    (n : ℕ) (α β : ℂ) :
    (complexToeplitzGauge n α β).conjTranspose * complexUpperShift n *
        complexToeplitzGauge n α β =
      toeplitzGaugePhase α β • complexUpperShift n := by
  ext i j
  simp only [complexToeplitzGauge, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply,
    complexUpperShift_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : j.1 = i.1 + 1
  · rw [if_pos h, h, pow_succ]
    simp only [mul_one]
    rw [← mul_assoc, star_pow, ← mul_pow,
      star_toeplitzGaugePhase_mul_self, one_pow, one_mul]
  · simp [h]

private theorem complexToeplitzGauge_conj_lower
    (n : ℕ) (α β : ℂ) :
    (complexToeplitzGauge n α β).conjTranspose * complexLowerShift n *
        complexToeplitzGauge n α β =
      star (toeplitzGaugePhase α β) • complexLowerShift n := by
  calc
    (complexToeplitzGauge n α β).conjTranspose * complexLowerShift n *
          complexToeplitzGauge n α β =
        ((complexToeplitzGauge n α β).conjTranspose * complexUpperShift n *
          complexToeplitzGauge n α β).conjTranspose := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (toeplitzGaugePhase α β • complexUpperShift n).conjTranspose := by
      rw [complexToeplitzGauge_conj_upper]
    _ = star (toeplitzGaugePhase α β) • complexLowerShift n := by simp

private theorem exp_arg_mul_star_toeplitzGaugePhase (α β : ℂ) :
    Complex.exp ((α.arg : ℂ) * Complex.I) *
        star (toeplitzGaugePhase α β) = toeplitzDirection α β := by
  rw [show star (toeplitzGaugePhase α β) =
      Complex.exp (-(((((α.arg - β.arg) / 2 : ℝ)) : ℂ) * Complex.I)) by
        rw [toeplitzGaugePhase]
        change (starRingEnd ℂ) (Complex.exp _) = _
        rw [← Complex.exp_conj]
        congr 1
        rw [map_mul, Complex.conj_ofReal]
        simp]
  rw [← Complex.exp_add, toeplitzDirection]
  congr 1
  push_cast
  ring

private theorem exp_arg_mul_toeplitzGaugePhase (α β : ℂ) :
    Complex.exp ((β.arg : ℂ) * Complex.I) *
        toeplitzGaugePhase α β = toeplitzDirection α β := by
  rw [toeplitzGaugePhase, toeplitzDirection, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem mul_star_toeplitzGaugePhase (α β : ℂ) :
    α * star (toeplitzGaugePhase α β) =
      toeplitzDirection α β * (‖α‖ : ℂ) := by
  have hpolar := Complex.norm_mul_exp_arg_mul_I α
  calc
    α * star (toeplitzGaugePhase α β) =
        ((‖α‖ : ℂ) * Complex.exp ((α.arg : ℂ) * Complex.I)) *
          star (toeplitzGaugePhase α β) := by rw [hpolar]
    _ = (‖α‖ : ℂ) * toeplitzDirection α β := by
      rw [mul_assoc, exp_arg_mul_star_toeplitzGaugePhase]
    _ = toeplitzDirection α β * (‖α‖ : ℂ) := mul_comm _ _

theorem mul_toeplitzGaugePhase (α β : ℂ) :
    β * toeplitzGaugePhase α β =
      toeplitzDirection α β * (‖β‖ : ℂ) := by
  have hpolar := Complex.norm_mul_exp_arg_mul_I β
  calc
    β * toeplitzGaugePhase α β =
        ((‖β‖ : ℂ) * Complex.exp ((β.arg : ℂ) * Complex.I)) *
          toeplitzGaugePhase α β := by rw [hpolar]
    _ = (‖β‖ : ℂ) * toeplitzDirection α β := by
      rw [mul_assoc, exp_arg_mul_toeplitzGaugePhase]
    _ = toeplitzDirection α β * (‖β‖ : ℂ) := mul_comm _ _

/-- Exact diagonal-unitary reduction to positive off-diagonal moduli and one
common complex direction. -/
theorem complexToeplitzMatrix_phase_reduction
    (n : ℕ) (α d β : ℂ) :
    (complexToeplitzGauge n α β).conjTranspose *
      complexToeplitzMatrix n α d β *
        complexToeplitzGauge n α β =
      d • 1 + toeplitzDirection α β •
        ((‖α‖ : ℂ) • complexLowerShift n +
          (‖β‖ : ℂ) • complexUpperShift n) := by
  calc
    (complexToeplitzGauge n α β).conjTranspose *
      complexToeplitzMatrix n α d β *
          complexToeplitzGauge n α β =
        d • ((complexToeplitzGauge n α β).conjTranspose *
          complexToeplitzGauge n α β) +
        α • ((complexToeplitzGauge n α β).conjTranspose * complexLowerShift n *
          complexToeplitzGauge n α β) +
        β • ((complexToeplitzGauge n α β).conjTranspose * complexUpperShift n *
          complexToeplitzGauge n α β) := by
            simp only [complexToeplitzMatrix, Matrix.mul_add,
              Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
              Matrix.mul_one]
    _ = d • 1 +
        α • (star (toeplitzGaugePhase α β) • complexLowerShift n) +
        β • (toeplitzGaugePhase α β • complexUpperShift n) := by
          rw [complexToeplitzGauge_star_mul_self,
            complexToeplitzGauge_conj_lower,
            complexToeplitzGauge_conj_upper]
    _ = d • 1 + toeplitzDirection α β •
        ((‖α‖ : ℂ) • complexLowerShift n +
          (‖β‖ : ℂ) • complexUpperShift n) := by
      rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul,
        mul_star_toeplitzGaugePhase, mul_toeplitzGaugePhase]
      rw [add_assoc]

/-! ## Canonical path reduction -/

/-- The complex affine coefficient in the normalized Toeplitz reduction. -/
def complexToeplitzScale (α β : ℂ) : ℂ :=
  toeplitzDirection α β * ((max ‖α‖ ‖β‖ : ℝ) : ℂ)

theorem norm_complexToeplitzScale (α β : ℂ) :
    ‖complexToeplitzScale α β‖ = max ‖α‖ ‖β‖ := by
  have hmax : 0 ≤ max ‖α‖ ‖β‖ :=
    (norm_nonneg α).trans (le_max_left ‖α‖ ‖β‖)
  rw [complexToeplitzScale, Complex.norm_mul, toeplitzDirection_norm,
    one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hmax]

theorem complexToeplitzScale_ne_zero {α β : ℂ}
    (hα : α ≠ 0) :
    complexToeplitzScale α β ≠ 0 := by
  apply mul_ne_zero (toeplitzDirection_ne_zero α β)
  exact Complex.ofReal_ne_zero.mpr
    (ne_of_gt (lt_max_iff.mpr (Or.inl (norm_pos_iff.mpr hα))))

/-- With two nonzero off-diagonals, the gauged matrix is either the canonical
affine path or its reversal. -/
theorem complexToeplitzMatrix_phase_reduction_eq_canonical_or_reversal
    (n : ℕ) {α β : ℂ} (d : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    let c := max ‖α‖ ‖β‖
    let a := min ‖α‖ ‖β‖ / c
    let C := d • 1 + complexToeplitzScale α β • complexPathMatrix n a
    (complexToeplitzGauge n α β).conjTranspose *
      complexToeplitzMatrix n α d β *
        complexToeplitzGauge n α β = C ∨
      (complexToeplitzGauge n α β).conjTranspose *
        complexToeplitzMatrix n α d β *
        complexToeplitzGauge n α β =
          complexReversal n * C * complexReversal n := by
  dsimp only
  have hαnorm : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hβnorm : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  rcases le_total ‖α‖ ‖β‖ with hle | hge
  · left
    rw [complexToeplitzMatrix_phase_reduction,
      complexPathMatrix_eq_complex_shifts]
    ext i j
    simp only [complexToeplitzScale, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul]
    simp only [min_eq_left hle, max_eq_right hle]
    push_cast
    field_simp [hβnorm.ne']
    ring
  · right
    rw [complexToeplitzMatrix_phase_reduction]
    have hJJ : complexReversal n * complexReversal n = 1 := by
      have hunit := Matrix.mem_unitaryGroup_iff.mp
        (complexReversal_mem_unitary n)
      simpa only [complexReversal_star] using hunit
    rw [min_eq_right hge, max_eq_left hge]
    rw [show complexToeplitzScale α β =
        toeplitzDirection α β * (‖α‖ : ℂ) by
          simp [complexToeplitzScale, max_eq_left hge]]
    symm
    calc
      complexReversal n *
            (d • 1 + (toeplitzDirection α β * (‖α‖ : ℂ)) •
              complexPathMatrix n (‖β‖ / ‖α‖)) *
          complexReversal n =
        d • (complexReversal n * complexReversal n) +
          (toeplitzDirection α β * (‖α‖ : ℂ)) •
            (complexReversal n * complexPathMatrix n (‖β‖ / ‖α‖) *
              complexReversal n) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
          Matrix.smul_mul, Matrix.mul_one]
      _ = d • 1 + (toeplitzDirection α β * (‖α‖ : ℂ)) •
          (complexLowerShift n + ((‖β‖ / ‖α‖ : ℝ) : ℂ) •
            complexUpperShift n) := by
        rw [hJJ, complexReversal_conjugate_complexPathMatrix]
      _ = d • 1 + toeplitzDirection α β •
          ((‖α‖ : ℂ) • complexLowerShift n +
            (‖β‖ : ℂ) • complexUpperShift n) := by
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        push_cast
        field_simp [hαnorm.ne']

/-- Exact normalized pseudospectral formula for arbitrary complex nonzero
off-diagonals, including the equal-modulus normal endpoint `a = 1`. -/
theorem complexToeplitzPseudospectrum_eq_affine_image
    (n : ℕ) {α β : ℂ} (d : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0) (ε : ℝ) :
    generalPseudospectrum (complexToeplitzMatrix n α d β) ε =
      complexAffineHomeomorph (complexToeplitzScale α β) d
        (complexToeplitzScale_ne_zero hα) ''
        pseudospectrum n
          (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖)
          (ε / max ‖α‖ ‖β‖) := by
  let G := complexToeplitzGauge n α β
  let C := d • 1 + complexToeplitzScale α β •
    complexPathMatrix n (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖)
  have hG := complexToeplitzGauge_mem_unitary n α β
  have hphase := complexToeplitzMatrix_phase_reduction_eq_canonical_or_reversal
    n d hα hβ
  have hpsGauge :
      generalPseudospectrum (complexToeplitzMatrix n α d β) ε =
        generalPseudospectrum
          (G.conjTranspose * complexToeplitzMatrix n α d β * G) ε := by
    exact (generalPseudospectrum_unitary_conjugate G
      (complexToeplitzMatrix n α d β) hG ε).symm
  rw [hpsGauge]
  have hcanonical :
      generalPseudospectrum
          (G.conjTranspose * complexToeplitzMatrix n α d β * G) ε =
        generalPseudospectrum C ε := by
    rcases hphase with hdirect | hreversed
    · exact congrArg (fun M => generalPseudospectrum M ε) hdirect
    · rw [hreversed]
      exact generalPseudospectrum_reversal_conjugate C ε
  rw [hcanonical]
  change generalPseudospectrum
      (d • 1 + complexToeplitzScale α β •
        complexPathMatrix n (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖)) ε = _
  rw [generalPseudospectrum_complexAffine,
    generalPseudospectrum_complexPathMatrix, norm_complexToeplitzScale]

/-- At equal nonzero moduli, the canonical parameter is exactly the normal
endpoint `a = 1`. -/
theorem complexToeplitzPseudospectrum_eq_normal_affine_image
    (n : ℕ) {α β : ℂ} (d : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (heq : ‖α‖ = ‖β‖) (ε : ℝ) :
    generalPseudospectrum (complexToeplitzMatrix n α d β) ε =
      complexAffineHomeomorph (complexToeplitzScale α β) d
        (complexToeplitzScale_ne_zero hα) ''
        pseudospectrum n 1 (ε / ‖α‖) := by
  have hβnorm : ‖β‖ ≠ 0 := (norm_pos_iff.mpr hβ).ne'
  simpa only [heq, min_self, max_self, div_self hβnorm] using
    (complexToeplitzPseudospectrum_eq_affine_image n d hα hβ ε)

/-- The equal-modulus canonical endpoint is Hermitian before its final
rotation and translation. -/
theorem complexPathMatrix_one_isHermitian (n : ℕ) :
    (complexPathMatrix n 1).IsHermitian := by
  rw [Matrix.IsHermitian, complexPathMatrix_eq_complex_shifts]
  simp [add_comm]

/-- For unequal nonzero moduli, the exact topological and connectedness
conclusions transfer from the normalized theorem. -/
theorem complexToeplitz_corollary
    (n : ℕ) (hn : 2 ≤ n) {α β : ℂ} (d : ℂ)
    (hα : α ≠ 0) (hβ : β ≠ 0) (hneq : ‖α‖ ≠ ‖β‖)
    {ε : ℝ} (hε : 0 < ε) :
    let c := max ‖α‖ ‖β‖
    let a := min ‖α‖ ‖β‖ / c
    (∀ {z : ℂ},
      z ∈ generalPseudospectrum (complexToeplitzMatrix n α d β) ε →
        ContractibleSpace
          (connectedComponentIn
            (generalPseudospectrum (complexToeplitzMatrix n α d β) ε) z)) ∧
    (IsConnected
      (generalPseudospectrum (complexToeplitzMatrix n α d β) ε) ↔
        ε > c * gapBarrier n a) := by
  dsimp only
  have hαnorm : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hβnorm : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  have hc : 0 < max ‖α‖ ‖β‖ := lt_max_iff.mpr (Or.inl hαnorm)
  have ha0 : 0 < min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖ :=
    div_pos (lt_min hαnorm hβnorm) hc
  have hminltmax : min ‖α‖ ‖β‖ < max ‖α‖ ‖β‖ := by
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · simpa [min_eq_left hlt.le, max_eq_right hlt.le] using hlt
    · simpa [min_eq_right hgt.le, max_eq_left hgt.le] using hgt
  have ha1 : min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖ < 1 :=
    (div_lt_one hc).2 hminltmax
  have hεc : 0 < ε / max ‖α‖ ‖β‖ := div_pos hε hc
  constructor
  · intro z hz
    rw [complexToeplitzPseudospectrum_eq_affine_image
      n d hα hβ ε] at hz ⊢
    rcases hz with ⟨w, hw, rfl⟩
    let e := complexAffineHomeomorph (complexToeplitzScale α β) d
      (complexToeplitzScale_ne_zero hα)
    let C := connectedComponentIn
      (pseudospectrum n (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖)
        (ε / max ‖α‖ ‖β‖)) w
    let hC : e '' C =
        connectedComponentIn
          (e '' pseudospectrum n (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖)
            (ε / max ‖α‖ ‖β‖)) (e w) :=
      e.image_connectedComponentIn hw
    let hcomponent : C ≃ₜ
        connectedComponentIn
          (e '' pseudospectrum n (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖)
            (ε / max ‖α‖ ‖β‖)) (e w) :=
      (Homeomorph.image e C).trans (Homeomorph.setCongr hC)
    letI : ContractibleSpace C :=
      contractibleSpace_pathPseudospectral_component
        n hn ha0 ha1 hεc hw
    exact hcomponent.symm.contractibleSpace
  · rw [complexToeplitzPseudospectrum_eq_affine_image
      n d hα hβ ε,
      (complexAffineHomeomorph (complexToeplitzScale α β) d
        (complexToeplitzScale_ne_zero hα)).isConnected_image,
      isConnected_pathPseudospectrum_iff_gapBarrier_lt
        n hn ha0 ha1 hεc]
    constructor
    · intro h
      have := (lt_div_iff₀ hc).1 h
      simpa [mul_comm] using this
    · intro h
      apply (lt_div_iff₀ hc).2
      simpa [mul_comm] using h

/-- The scaled barriers retain strict adjacent-dimension decrease precisely
in the unequal-modulus regime. -/
theorem complexToeplitz_scaled_barrier_succ_lt
    {α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) (hneq : ‖α‖ ≠ ‖β‖)
    {n : ℕ} (hn : 2 ≤ n) :
    max ‖α‖ ‖β‖ *
        gapBarrier (n + 1) (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖) <
      max ‖α‖ ‖β‖ *
        gapBarrier n (min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖) := by
  have hαnorm : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hβnorm : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  have hc : 0 < max ‖α‖ ‖β‖ := lt_max_iff.mpr (Or.inl hαnorm)
  have ha0 : 0 < min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖ :=
    div_pos (lt_min hαnorm hβnorm) hc
  have hminltmax : min ‖α‖ ‖β‖ < max ‖α‖ ‖β‖ := by
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · simpa [min_eq_left hlt.le, max_eq_right hlt.le] using hlt
    · simpa [min_eq_right hgt.le, max_eq_left hgt.le] using hgt
  have ha1 : min ‖α‖ ‖β‖ / max ‖α‖ ‖β‖ < 1 :=
    (div_lt_one hc).2 hminltmax
  exact mul_lt_mul_of_pos_left (gapBarrier_succ_lt n hn ha0 ha1) hc

/-! ## Vanishing off-diagonals -/

/-- Diagonal unitary used to rotate a nilpotent Jordan shift. -/
def jordanRotationGauge (n : ℕ) (u : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i : Fin n => u ^ i.1

theorem jordanRotationGauge_mem_unitary (n : ℕ) {u : ℂ}
    (hu : ‖u‖ = 1) :
    jordanRotationGauge n u ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  apply Matrix.mem_unitaryGroup_iff.mpr
  change jordanRotationGauge n u * (jordanRotationGauge n u).conjTranspose = 1
  rw [jordanRotationGauge, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  apply Matrix.diagonal_eq_diagonal_iff.mpr
  intro i
  rw [Pi.star_apply, star_pow, ← mul_pow]
  have hustar : u * star u = 1 := by
    rw [mul_comm]
    simpa [hu] using (Complex.conj_mul' u)
  rw [hustar, one_pow]

theorem jordanRotationGauge_conj_upper (n : ℕ) (u : ℂ) (hu : ‖u‖ = 1) :
    (jordanRotationGauge n u).conjTranspose * complexUpperShift n *
        jordanRotationGauge n u =
      u • complexUpperShift n := by
  ext i j
  simp only [jordanRotationGauge, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.star_apply,
    complexUpperShift_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : j.1 = i.1 + 1
  · rw [if_pos h, h, pow_succ]
    simp only [mul_one]
    rw [← mul_assoc, star_pow, ← mul_pow]
    have hstaru : star u * u = 1 := by
      simpa [hu] using (Complex.conj_mul' u)
    rw [hstaru, one_pow, one_mul]
  · simp [h]

theorem jordanRotationGauge_conj_lower (n : ℕ) (u : ℂ) (hu : ‖u‖ = 1) :
    (jordanRotationGauge n u).conjTranspose * complexLowerShift n *
        jordanRotationGauge n u =
      star u • complexLowerShift n := by
  calc
    (jordanRotationGauge n u).conjTranspose * complexLowerShift n *
          jordanRotationGauge n u =
        ((jordanRotationGauge n u).conjTranspose * complexUpperShift n *
          jordanRotationGauge n u).conjTranspose := by
            simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (u • complexUpperShift n).conjTranspose := by
      rw [jordanRotationGauge_conj_upper n u hu]
    _ = star u • complexLowerShift n := by simp

/-- Rotating the spectral plane about the diagonal entry leaves the
least-singular-value height of an upper one-sided Toeplitz matrix unchanged. -/
theorem generalPseudospectralHeight_left_zero_rotation
    (n : ℕ) (d β u z : ℂ) (hu : ‖u‖ = 1) :
    generalPseudospectralHeight (complexToeplitzMatrix n 0 d β)
        (d + u * (z - d)) =
      generalPseudospectralHeight (complexToeplitzMatrix n 0 d β) z := by
  let Q := jordanRotationGauge n (star u)
  have hstarNorm : ‖star u‖ = 1 := by simpa using hu
  have hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    jordanRotationGauge_mem_unitary n hstarNorm
  have hQstar : Q.conjTranspose ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    Unitary.star_mem hQ
  have hQstarQ : Q.conjTranspose * Q = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hQstar
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using h
  have hustar : u * star u = 1 := by
    rw [mul_comm]
    simpa [hu] using (Complex.conj_mul' u)
  have hshift :
      generalShift (complexToeplitzMatrix n 0 d β) (d + u * (z - d)) =
        u • (Q.conjTranspose *
          generalShift (complexToeplitzMatrix n 0 d β) z * Q) := by
    have hconj :
        Q.conjTranspose * complexUpperShift n * Q =
          star u • complexUpperShift n := by
      dsimp [Q]
      simpa using jordanRotationGauge_conj_upper n (star u) hstarNorm
    have hQshift :
        Q.conjTranspose *
            generalShift (complexToeplitzMatrix n 0 d β) z * Q =
          (z - d) • (1 : Matrix (Fin n) (Fin n) ℂ) -
            (β * star u) • complexUpperShift n := by
      calc
        Q.conjTranspose *
              generalShift (complexToeplitzMatrix n 0 d β) z * Q =
            z • (Q.conjTranspose * Q) -
              (d • (Q.conjTranspose * Q) +
                β • (Q.conjTranspose * complexUpperShift n * Q)) := by
            simp only [generalShift, complexToeplitzMatrix, zero_smul,
              Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
              Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
              Matrix.mul_one, add_zero]
        _ = (z - d) • (1 : Matrix (Fin n) (Fin n) ℂ) -
              (β * star u) • complexUpperShift n := by
            rw [hQstarQ, hconj, smul_smul]
            ext i j
            simp [sub_smul]
            ring
    rw [hQshift]
    ext i j
    simp only [generalShift, complexToeplitzMatrix, zero_smul,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simp
    · by_cases hupper : j.1 = i.1 + 1
      · have hcoeff : u * β * star u = β := by
          calc
            u * β * star u = β * (u * star u) := by ring
            _ = β := by rw [hustar, mul_one]
        simp [hij, hupper]
        simpa only [mul_assoc] using hcoeff.symm
      · simp [hij, hupper]
  unfold generalPseudospectralHeight
  rw [hshift, leastSingularValue_smul,
    leastSingularValue_mul_unitary
      (Q.conjTranspose * generalShift (complexToeplitzMatrix n 0 d β) z) Q hQ,
    leastSingularValue_unitary_mul Q.conjTranspose
      (generalShift (complexToeplitzMatrix n 0 d β) z) hQstar, hu,
    one_mul]

/-- The lower one-sided boundary has the same rotation invariance. -/
theorem generalPseudospectralHeight_right_zero_rotation
    (n : ℕ) (α d u z : ℂ) (hu : ‖u‖ = 1) :
    generalPseudospectralHeight (complexToeplitzMatrix n α d 0)
        (d + u * (z - d)) =
      generalPseudospectralHeight (complexToeplitzMatrix n α d 0) z := by
  let Q := jordanRotationGauge n u
  have hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    jordanRotationGauge_mem_unitary n hu
  have hQstar : Q.conjTranspose ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    Unitary.star_mem hQ
  have hQstarQ : Q.conjTranspose * Q = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hQstar
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using h
  have hustar : u * star u = 1 := by
    rw [mul_comm]
    simpa [hu] using (Complex.conj_mul' u)
  have hshift :
      generalShift (complexToeplitzMatrix n α d 0) (d + u * (z - d)) =
        u • (Q.conjTranspose *
          generalShift (complexToeplitzMatrix n α d 0) z * Q) := by
    have hconj :
        Q.conjTranspose * complexLowerShift n * Q =
          star u • complexLowerShift n := by
      exact jordanRotationGauge_conj_lower n u hu
    have hQshift :
        Q.conjTranspose *
            generalShift (complexToeplitzMatrix n α d 0) z * Q =
          (z - d) • (1 : Matrix (Fin n) (Fin n) ℂ) -
            (α * star u) • complexLowerShift n := by
      calc
        Q.conjTranspose *
              generalShift (complexToeplitzMatrix n α d 0) z * Q =
            z • (Q.conjTranspose * Q) -
              (d • (Q.conjTranspose * Q) +
                α • (Q.conjTranspose * complexLowerShift n * Q)) := by
            simp only [generalShift, complexToeplitzMatrix, zero_smul,
              add_zero, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
              Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
              Matrix.mul_one]
        _ = (z - d) • (1 : Matrix (Fin n) (Fin n) ℂ) -
              (α * star u) • complexLowerShift n := by
            rw [hQstarQ, hconj, smul_smul]
            ext i j
            simp [sub_smul]
            ring
    rw [hQshift]
    ext i j
    simp only [generalShift, complexToeplitzMatrix, zero_smul, add_zero,
      Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simp
    · by_cases hlower : i.1 = j.1 + 1
      · have hcoeff : u * α * star u = α := by
          calc
            u * α * star u = α * (u * star u) := by ring
            _ = α := by rw [hustar, mul_one]
        simp [hij, hlower]
        simpa only [mul_assoc] using hcoeff.symm
      · simp [hij, hlower]
  unfold generalPseudospectralHeight
  rw [hshift, leastSingularValue_smul,
    leastSingularValue_mul_unitary
      (Q.conjTranspose * generalShift (complexToeplitzMatrix n α d 0) z) Q hQ,
    leastSingularValue_unitary_mul Q.conjTranspose
      (generalShift (complexToeplitzMatrix n α d 0) z) hQstar, hu,
    one_mul]

/-- A shifted one-sided Toeplitz matrix is triangular, so its determinant is
the `n`th power of the scalar diagonal shift. -/
theorem det_generalShift_complexToeplitzMatrix_of_left_zero
    (n : ℕ) (d β z : ℂ) :
    (generalShift (complexToeplitzMatrix n 0 d β) z).det = (z - d) ^ n := by
  have htri :
      (generalShift (complexToeplitzMatrix n 0 d β) z).BlockTriangular id := by
    intro i j hij
    have hji : j.1 < i.1 := hij
    simp only [generalShift, complexToeplitzMatrix_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply]
    have hne : i ≠ j := by
      intro h
      subst j
      exact (lt_irrefl i.1) hji
    have hnotUpper : j.1 ≠ i.1 + 1 := by omega
    simp [hne, hnotUpper]
  rw [Matrix.det_of_upperTriangular htri]
  simp [generalShift, complexToeplitzMatrix_apply]

/-- The opposite one-sided boundary has the same determinant. -/
theorem det_generalShift_complexToeplitzMatrix_of_right_zero
    (n : ℕ) (α d z : ℂ) :
    (generalShift (complexToeplitzMatrix n α d 0) z).det = (z - d) ^ n := by
  have htri :
      (generalShift (complexToeplitzMatrix n α d 0) z).BlockTriangular
        OrderDual.toDual := by
    intro i j hij
    have hij' : i.1 < j.1 := hij
    simp only [generalShift, complexToeplitzMatrix_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply]
    have hne : i ≠ j := by
      intro h
      subst j
      exact (lt_irrefl i.1) hij'
    have hnotLower : i.1 ≠ j.1 + 1 := by omega
    simp [hne, hnotLower]
  rw [Matrix.det_of_lowerTriangular _ htri]
  simp [generalShift, complexToeplitzMatrix_apply]

theorem det_generalShift_complexToeplitzMatrix_eq_zero_iff_of_left_zero
    (n : ℕ) (hn : 0 < n) (d β z : ℂ) :
    (generalShift (complexToeplitzMatrix n 0 d β) z).det = 0 ↔ z = d := by
  rw [det_generalShift_complexToeplitzMatrix_of_left_zero]
  simpa [pow_eq_zero_iff hn.ne'] using (sub_eq_zero : z - d = 0 ↔ z = d)

theorem det_generalShift_complexToeplitzMatrix_eq_zero_iff_of_right_zero
    (n : ℕ) (hn : 0 < n) (α d z : ℂ) :
    (generalShift (complexToeplitzMatrix n α d 0) z).det = 0 ↔ z = d := by
  rw [det_generalShift_complexToeplitzMatrix_of_right_zero]
  simpa [pow_eq_zero_iff hn.ne'] using (sub_eq_zero : z - d = 0 ↔ z = d)

private theorem isConnected_generalPseudospectrum_of_unique_det_root
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    (d : ℂ) {ε : ℝ} (hε : 0 < ε)
    (hroot : ∀ z : ℂ, (generalShift M z).det = 0 ↔ z = d) :
    IsConnected (generalPseudospectrum M ε) := by
  have hdDet : (generalShift M d).det = 0 := (hroot d).2 rfl
  have hdΩ : d ∈ generalPseudospectrum M ε :=
    mem_generalPseudospectrum_of_det_generalShift_eq_zero M hn hε hdDet
  have hsubset : generalPseudospectrum M ε ⊆
      connectedComponentIn (generalPseudospectrum M ε) d := by
    intro z hz
    obtain ⟨w, hwComponent, hwdet⟩ :=
      exists_det_generalShift_eq_zero_mem_component M hn hε hz
    have hwd : w = d := (hroot w).1 hwdet
    subst w
    have hcomponents :
        connectedComponentIn (generalPseudospectrum M ε) z =
          connectedComponentIn (generalPseudospectrum M ε) d :=
      connectedComponentIn_eq hwComponent
    exact hcomponents ▸ mem_connectedComponentIn hz
  have heq : connectedComponentIn (generalPseudospectrum M ε) d =
      generalPseudospectrum M ε :=
    (connectedComponentIn_subset _ _).antisymm hsubset
  refine ⟨⟨d, hdΩ⟩, ?_⟩
  rw [← heq]
  exact isPreconnected_connectedComponentIn

/-- A one-sided (Jordan) Toeplitz matrix has connected positive strict
pseudospectrum in every positive dimension; hence its connectedness threshold
is zero and cannot be strictly dimension-monotone. -/
theorem isConnected_complexToeplitzPseudospectrum_of_left_zero
    (n : ℕ) (hn : 0 < n) (d β : ℂ) {ε : ℝ} (hε : 0 < ε) :
    IsConnected (generalPseudospectrum
      (complexToeplitzMatrix n 0 d β) ε) := by
  exact isConnected_generalPseudospectrum_of_unique_det_root
    (complexToeplitzMatrix n 0 d β) hn d hε
      (det_generalShift_complexToeplitzMatrix_eq_zero_iff_of_left_zero
        n hn d β)

theorem isConnected_complexToeplitzPseudospectrum_of_right_zero
    (n : ℕ) (hn : 0 < n) (α d : ℂ) {ε : ℝ} (hε : 0 < ε) :
    IsConnected (generalPseudospectrum
      (complexToeplitzMatrix n α d 0) ε) := by
  exact isConnected_generalPseudospectrum_of_unique_det_root
    (complexToeplitzMatrix n α d 0) hn d hε
      (det_generalShift_complexToeplitzMatrix_eq_zero_iff_of_right_zero
        n hn α d)

/-- With both off-diagonals zero, the least-singular-value height is simply
the distance to the scalar diagonal entry. -/
theorem generalPseudospectralHeight_complexToeplitzMatrix_zero_zero
    (n : ℕ) (hn : 0 < n) (d z : ℂ) :
    generalPseudospectralHeight (complexToeplitzMatrix n 0 d 0) z =
      ‖z - d‖ := by
  unfold generalPseudospectralHeight
  have hshift : generalShift (complexToeplitzMatrix n 0 d 0) z =
      (z - d) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [generalShift, complexToeplitzMatrix]
    · simp [generalShift, complexToeplitzMatrix, hij]
  rw [hshift, leastSingularValue_smul_one hn]

/-- The scalar boundary is exactly the open disk centered at `d`. -/
theorem generalPseudospectrum_complexToeplitzMatrix_zero_zero
    (n : ℕ) (hn : 0 < n) (d : ℂ) (ε : ℝ) :
    generalPseudospectrum (complexToeplitzMatrix n 0 d 0) ε =
      Metric.ball d ε := by
  ext z
  change generalPseudospectralHeight (complexToeplitzMatrix n 0 d 0) z < ε ↔
    dist z d < ε
  rw [generalPseudospectralHeight_complexToeplitzMatrix_zero_zero n hn d z,
    dist_eq_norm]

/-- Complete zero-product boundary classification: whenever `αβ=0`, every
positive strict pseudospectrum is connected. -/
theorem isConnected_complexToeplitzPseudospectrum_of_mul_eq_zero
    (n : ℕ) (hn : 0 < n) (α d β : ℂ) (hαβ : α * β = 0)
    {ε : ℝ} (hε : 0 < ε) :
    IsConnected (generalPseudospectrum
      (complexToeplitzMatrix n α d β) ε) := by
  rcases mul_eq_zero.mp hαβ with hα | hβ
  · subst α
    exact isConnected_complexToeplitzPseudospectrum_of_left_zero
      n hn d β hε
  · subst β
    exact isConnected_complexToeplitzPseudospectrum_of_right_zero
      n hn α d hε

end

end ConnectedPseudospectrum
