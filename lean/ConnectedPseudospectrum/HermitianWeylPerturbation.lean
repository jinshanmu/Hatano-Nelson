import ConnectedPseudospectrum.MiddleBranchSelection
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Hermitian eigenvalue perturbation from quadratic forms

This module proves the ordered Hermitian perturbation estimate needed in the
central-gap comparison.  The estimate is derived from the same spectral
overlap and dimension-count argument as the project's Loewner monotonicity
theorem; no Weyl inequality is assumed.

For the signed-middle pencil, the perturbation from `x=0` is exactly `xJ`.
The identities `Jᵀ=J` and `J²=I` give
`I±J = (1/2)(I±J)ᵀ(I±J)`, hence the needed two Loewner bounds.
-/

namespace ConnectedPseudospectrum

open Matrix Module
open scoped Matrix

local infixr:73 " *ᵥ " => Matrix.mulVec
local postfix:1024 "ᵀ" => Matrix.transpose
local postfix:1024 "ᴴ" => Matrix.conjTranspose

noncomputable section

/-! ## A quadratic-form eigenvalue comparison -/

/-- One-sided ordered-eigenvalue comparison with an additive quadratic-form
error.  This is the min--max ingredient behind the finite-dimensional Weyl
estimate, proved here from the project's spectral overlap map. -/
theorem orderedHermitianEigenvalue_le_add_of_quadratic
    {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (δ : ℝ)
    (hquad : ∀ v : Fin n → ℝ,
      v ⬝ᵥ (A *ᵥ v) ≤ v ⬝ᵥ (B *ᵥ v) + δ * (v ⬝ᵥ v))
    (k : Fin n) :
    orderedHermitianEigenvalue hA k ≤
      orderedHermitianEigenvalue hB k + δ := by
  by_contra! hcontra
  let F := orderedSpectralOverlap hA hB k
  have hdim : Module.finrank ℝ (Fin k.1 → ℝ) <
      Module.finrank ℝ (Fin (k.1 + 1) → ℝ) := by
    simp only [Module.finrank_fin_fun]
    omega
  have hker : LinearMap.ker F ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hcF, hcne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  let padded : Fin n → ℝ :=
    finPrefixPad c
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
  have hcoordA : hermitianCoordinates hA v = padded :=
    hermitianCoordinates_orderedEigenvectorMatrix_mulVec hA padded
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
    rw [Matrix.mulVec_transpose]
    simpa [F, orderedSpectralOverlap, v, padded, hermitianCoordinates,
      finPrefixTake, Matrix.mulVecLin_apply, LinearMap.comp_apply] using hcomponent
  have hAquad := orderedEigenvalue_mul_dotProduct_le_dotProduct_mulVec
    hA k v hAhead
  have hBquad := dotProduct_mulVec_le_orderedEigenvalue_mul_dotProduct
    hB k v hBtail
  have hABquad := hquad v
  have hnorm : 0 < v ⬝ᵥ v := dotProduct_self_pos hvne
  nlinarith

/-- Two-sided Loewner control yields the absolute ordered-eigenvalue
perturbation estimate.  The proof reduces both sides to the preceding
quadratic-form comparison. -/
theorem abs_orderedHermitianEigenvalue_sub_le_of_two_sided_posSemidef
    {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {δ : ℝ}
    (hupper : (δ • (1 : Matrix (Fin n) (Fin n) ℝ) - (B - A)).PosSemidef)
    (hlower : (δ • (1 : Matrix (Fin n) (Fin n) ℝ) + (B - A)).PosSemidef)
    (k : Fin n) :
    |orderedHermitianEigenvalue hB k - orderedHermitianEigenvalue hA k| ≤ δ := by
  have hquadBA : ∀ v : Fin n → ℝ,
      v ⬝ᵥ (B *ᵥ v) ≤
        v ⬝ᵥ (A *ᵥ v) + δ * (v ⬝ᵥ v) := by
    intro v
    have h := hupper.dotProduct_mulVec_nonneg v
    simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
    linarith
  have hquadAB : ∀ v : Fin n → ℝ,
      v ⬝ᵥ (A *ᵥ v) ≤
        v ⬝ᵥ (B *ᵥ v) + δ * (v ⬝ᵥ v) := by
    intro v
    have h := hlower.dotProduct_mulVec_nonneg v
    simp only [star_trivial, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
      dotProduct_sub, dotProduct_smul, smul_eq_mul] at h
    linarith
  have hBA : orderedHermitianEigenvalue hB k ≤
      orderedHermitianEigenvalue hA k + δ :=
    orderedHermitianEigenvalue_le_add_of_quadratic
      hB hA δ hquadBA k
  have hAB : orderedHermitianEigenvalue hA k ≤
      orderedHermitianEigenvalue hB k + δ :=
    orderedHermitianEigenvalue_le_add_of_quadratic
      hA hB δ hquadAB k
  rw [abs_le]
  constructor <;> linarith

/-! ## Positive semidefiniteness of `I ± J` -/

private theorem one_sub_reversal_isHermitian (n : ℕ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) - reversal n).IsHermitian := by
  exact Matrix.IsSymm.isHermitianReal (by
    rw [Matrix.IsSymm, Matrix.transpose_sub, Matrix.transpose_one,
      reversal_transpose])

private theorem one_add_reversal_isHermitian (n : ℕ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + reversal n).IsHermitian := by
  exact Matrix.IsSymm.isHermitianReal (by
    rw [Matrix.IsSymm, Matrix.transpose_add, Matrix.transpose_one,
      reversal_transpose])

/-- `I-J` is positive semidefinite.  Algebraically it is one half of its
own Gram matrix. -/
theorem one_sub_reversal_posSemidef (n : ℕ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) - reversal n).PosSemidef := by
  let M : Matrix (Fin n) (Fin n) ℝ := 1 - reversal n
  have hM : M.IsHermitian := one_sub_reversal_isHermitian n
  have hgram : Mᴴ * M = (2 : ℝ) • M := by
    rw [hM]
    dsimp only [M]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, reversal_mul_self]
    module
  have heq : M = (1 / 2 : ℝ) • (Mᴴ * M) := by
    rw [hgram]
    module
  rw [show (1 : Matrix (Fin n) (Fin n) ℝ) - reversal n = M from rfl,
    heq]
  exact (Matrix.posSemidef_conjTranspose_mul_self M).smul (by norm_num)

/-- `I+J` is positive semidefinite.  Algebraically it is one half of its
own Gram matrix. -/
theorem one_add_reversal_posSemidef (n : ℕ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + reversal n).PosSemidef := by
  let M : Matrix (Fin n) (Fin n) ℝ := 1 + reversal n
  have hM : M.IsHermitian := one_add_reversal_isHermitian n
  have hgram : Mᴴ * M = (2 : ℝ) • M := by
    rw [hM]
    dsimp only [M]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, reversal_mul_self]
    module
  have heq : M = (1 / 2 : ℝ) • (Mᴴ * M) := by
    rw [hgram]
    module
  rw [show (1 : Matrix (Fin n) (Fin n) ℝ) + reversal n = M from rfl,
    heq]
  exact (Matrix.posSemidef_conjTranspose_mul_self M).smul (by norm_num)

/-- A nonnegative multiple of `I-J` is positive semidefinite. -/
theorem smul_one_sub_reversal_posSemidef
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x • ((1 : Matrix (Fin n) (Fin n) ℝ) - reversal n)).PosSemidef :=
  (one_sub_reversal_posSemidef n).smul hx

/-- A nonnegative multiple of `I+J` is positive semidefinite. -/
theorem smul_one_add_reversal_posSemidef
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (x • ((1 : Matrix (Fin n) (Fin n) ℝ) + reversal n)).PosSemidef :=
  (one_add_reversal_posSemidef n).smul hx

/-! ## The signed-middle specialization -/

/-- The signed-middle pencil is affine in the real parameter, with slope
the reversal matrix. -/
theorem signedMiddleMatrix_sub_zero (n : ℕ) (a x : ℝ) :
    signedMiddleMatrix n a x - signedMiddleMatrix n a 0 =
      x • reversal n := by
  rw [signedMiddleMatrix, signedMiddleMatrix, ← Matrix.sub_mul]
  simp only [zero_smul, zero_sub, sub_neg_eq_add, sub_add_cancel,
    Matrix.smul_mul, Matrix.one_mul]

/-- For `x≥0`, every decreasingly ordered eigenvalue of the signed-middle
matrix moves by at most `x` from its value at the centre. -/
theorem abs_orderedSignedMiddleEigenvalue_sub_zero_le
    (n : ℕ) (a : ℝ) {x : ℝ} (hx : 0 ≤ x) (k : Fin n) :
    let hBx : (signedMiddleMatrix n a x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
    let hB0 : (signedMiddleMatrix n a 0).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a 0)
    |orderedHermitianEigenvalue hBx k -
        orderedHermitianEigenvalue hB0 k| ≤ x := by
  dsimp only
  let Bx := signedMiddleMatrix n a x
  let B0 := signedMiddleMatrix n a 0
  let hBx : Bx.IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
  let hB0 : B0.IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a 0)
  have hdiff : Bx - B0 = x • reversal n :=
    signedMiddleMatrix_sub_zero n a x
  have hupper :
      (x • (1 : Matrix (Fin n) (Fin n) ℝ) - (Bx - B0)).PosSemidef := by
    rw [hdiff]
    have heq :
        x • (1 : Matrix (Fin n) (Fin n) ℝ) - x • reversal n =
          x • ((1 : Matrix (Fin n) (Fin n) ℝ) - reversal n) := by
      module
    rw [heq]
    exact smul_one_sub_reversal_posSemidef n hx
  have hlower :
      (x • (1 : Matrix (Fin n) (Fin n) ℝ) + (Bx - B0)).PosSemidef := by
    rw [hdiff]
    have heq :
        x • (1 : Matrix (Fin n) (Fin n) ℝ) + x • reversal n =
          x • ((1 : Matrix (Fin n) (Fin n) ℝ) + reversal n) := by
      module
    rw [heq]
    exact smul_one_add_reversal_posSemidef n hx
  exact abs_orderedHermitianEigenvalue_sub_le_of_two_sided_posSemidef
    hB0 hBx hupper hlower k

/-! ## Isolation of the central zero branch -/

/-- Generic zero-branch isolation.  If every nonzero centre eigenvalue lies
outside `(-s₂,s₂)` and the perturbation plus target radius is smaller than
`s₂`, then any perturbed eigenvalue in `(-c,c)` must originate at a zero
centre eigenvalue.  This is the conclusion available without a separate
nullity-one or inertia theorem. -/
theorem small_perturbed_value_implies_center_zero
    {n : ℕ} (center perturbed : Fin n → ℝ) {x c s₂ : ℝ}
    (hperturb : ∀ i, |perturbed i - center i| ≤ x)
    (hcenterGap : ∀ i, center i ≠ 0 → s₂ ≤ |center i|)
    (hxc : x + c < s₂) (i : Fin n) (hi : |perturbed i| < c) :
    center i = 0 := by
  have hcenterLt : |center i| < s₂ := by
    calc
      |center i| = |(center i - perturbed i) + perturbed i| := by
        rw [sub_add_cancel]
      _ ≤ |center i - perturbed i| + |perturbed i| := abs_add_le _ _
      _ = |perturbed i - center i| + |perturbed i| := by
        rw [abs_sub_comm]
      _ ≤ x + |perturbed i| := by
        exact add_le_add (hperturb i) le_rfl
      _ < x + c := by
        gcongr
      _ < s₂ := hxc
  by_contra hne
  exact (not_lt_of_ge (hcenterGap i hne)) hcenterLt

/-- With uniqueness of the centre zero supplied, the preceding isolation
statement becomes the precise "at most one" cardinal conclusion. -/
theorem atMostOne_small_perturbed_value
    {n : ℕ} (center perturbed : Fin n → ℝ) {x c s₂ : ℝ}
    (hperturb : ∀ i, |perturbed i - center i| ≤ x)
    (hcenterGap : ∀ i, center i ≠ 0 → s₂ ≤ |center i|)
    (hcenterZeroUnique : ∀ i j, center i = 0 → center j = 0 → i = j)
    (hxc : x + c < s₂) :
    ∀ i j : Fin n,
      |perturbed i| < c → |perturbed j| < c → i = j := by
  intro i j hi hj
  apply hcenterZeroUnique i j
  · exact small_perturbed_value_implies_center_zero
      center perturbed hperturb hcenterGap hxc i hi
  · exact small_perturbed_value_implies_center_zero
      center perturbed hperturb hcenterGap hxc j hj

/-- Signed-middle specialization of zero-branch isolation. -/
theorem small_orderedSignedMiddleEigenvalue_implies_center_zero
    (n : ℕ) (a : ℝ) {x c s₂ : ℝ} (hx : 0 ≤ x)
    (hcenterGap :
      let hB0 : (signedMiddleMatrix n a 0).IsHermitian :=
        Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a 0)
      ∀ i : Fin n,
        orderedHermitianEigenvalue hB0 i ≠ 0 →
          s₂ ≤ |orderedHermitianEigenvalue hB0 i|)
    (hxc : x + c < s₂) (i : Fin n) :
    let hBx : (signedMiddleMatrix n a x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
    let hB0 : (signedMiddleMatrix n a 0).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a 0)
    |orderedHermitianEigenvalue hBx i| < c →
      orderedHermitianEigenvalue hB0 i = 0 := by
  dsimp only at hcenterGap ⊢
  let hBx : (signedMiddleMatrix n a x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
  let hB0 : (signedMiddleMatrix n a 0).IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a 0)
  intro hi
  apply small_perturbed_value_implies_center_zero
    (orderedHermitianEigenvalue hB0) (orderedHermitianEigenvalue hBx)
    (x := x) (c := c) (s₂ := s₂)
  · intro j
    exact abs_orderedSignedMiddleEigenvalue_sub_zero_le n a hx j
  · exact hcenterGap
  · exact hxc
  · exact hi

/-- The signed-middle "at most one" conclusion, conditional only on the
separate nullity-one fact for the centre matrix. -/
theorem atMostOne_small_orderedSignedMiddleEigenvalue
    (n : ℕ) (a : ℝ) {x c s₂ : ℝ} (hx : 0 ≤ x)
    (hcenterGap :
      let hB0 : (signedMiddleMatrix n a 0).IsHermitian :=
        Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a 0)
      ∀ i : Fin n,
        orderedHermitianEigenvalue hB0 i ≠ 0 →
          s₂ ≤ |orderedHermitianEigenvalue hB0 i|)
    (hcenterZeroUnique :
      let hB0 : (signedMiddleMatrix n a 0).IsHermitian :=
        Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a 0)
      ∀ i j : Fin n,
        orderedHermitianEigenvalue hB0 i = 0 →
        orderedHermitianEigenvalue hB0 j = 0 → i = j)
    (hxc : x + c < s₂) :
    let hBx : (signedMiddleMatrix n a x).IsHermitian :=
      Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
    ∀ i j : Fin n,
      |orderedHermitianEigenvalue hBx i| < c →
      |orderedHermitianEigenvalue hBx j| < c → i = j := by
  dsimp only at hcenterGap hcenterZeroUnique ⊢
  let hBx : (signedMiddleMatrix n a x).IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a x)
  let hB0 : (signedMiddleMatrix n a 0).IsHermitian :=
    Matrix.IsSymm.isHermitianReal (signedMiddleMatrix_isSymm n a 0)
  apply atMostOne_small_perturbed_value
    (orderedHermitianEigenvalue hB0) (orderedHermitianEigenvalue hBx)
    (x := x) (c := c) (s₂ := s₂)
  · intro i
    exact abs_orderedSignedMiddleEigenvalue_sub_zero_le n a hx i
  · exact hcenterGap
  · exact hcenterZeroUnique
  · exact hxc

end

end ConnectedPseudospectrum
