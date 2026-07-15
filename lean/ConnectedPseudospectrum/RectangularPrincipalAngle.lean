import ConnectedPseudospectrum.RectangularGramBound
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Range hyperplanes and the rectangular principal angle

This module formalizes the normalized range normals and their overlap from
the lower-bound part of `prop:gap-bounds`.  Indices in `Fin (n+1)` correspond
to the paper's rows `0, ..., n`.
-/

namespace ConnectedPseudospectrum

open Matrix
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

/-- The paper's geometric normalization sum
`S_N = sum_{j=0}^n r^(2j)`, where `N=n+1`. -/
def rectangularNormalSq (n : ℕ) (r : ℝ) : ℝ :=
  ∑ j : Fin (n + 1), r ^ (2 * j.1)

theorem rectangularNormalSq_pos (n : ℕ) (r : ℝ) :
    0 < rectangularNormalSq n r := by
  have hnonneg : ∀ j : Fin (n + 1), 0 ≤ r ^ (2 * j.1) := by
    intro j
    rw [mul_comm, pow_mul]
    exact sq_nonneg _
  unfold rectangularNormalSq
  exact Finset.sum_pos' (fun j _ => hnonneg j) ⟨0, Finset.mem_univ _, by simp⟩

theorem rectangularNormalSq_ne_zero (n : ℕ) (r : ℝ) :
    rectangularNormalSq n r ≠ 0 :=
  (rectangularNormalSq_pos n r).ne'

/-- Closed geometric-series form used in the paper. -/
theorem rectangularNormalSq_eq_closed (n : ℕ) {r : ℝ} (hr : r < 1)
    (hr0 : 0 ≤ r) :
    rectangularNormalSq n r =
      (1 - r ^ (2 * (n + 1))) / (1 - r ^ 2) := by
  have hr2 : r ^ 2 ≠ 1 := by
    intro h
    have hfac : (r - 1) * (r + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with hminus | hplus
    · nlinarith
    · nlinarith
  rw [rectangularNormalSq,
    Fin.sum_univ_eq_sum_range (fun j : ℕ => r ^ (2 * j))]
  rw [show (fun j : ℕ => r ^ (2 * j)) = fun j => (r ^ 2) ^ j by
    funext j
    rw [← pow_mul]]
  rw [geom_sum_eq hr2]
  rw [pow_mul]
  have hnum : 1 - (r ^ 2) ^ (n + 1) =
      -((r ^ 2) ^ (n + 1) - 1) := by ring
  have hden : 1 - r ^ 2 = -(r ^ 2 - 1) := by ring
  rw [hnum, hden]
  exact (neg_div_neg_eq _ _).symm

/-- Unnormalized normal to the range of `rectangularC n p`. -/
def rectangularCRawNormal (n : ℕ) (p : ℂ) : Fin (n + 1) → ℂ :=
  fun j => conj p ^ (n - j.1)

/-- Unnormalized normal to the range of `rectangularD n q`. -/
def rectangularDRawNormal (n : ℕ) (q : ℂ) : Fin (n + 1) → ℂ :=
  fun j => q ^ j.1

/-- Adjoint padding at the first coordinate reads the successor entry. -/
@[simp] theorem padFirstMatrix_conjTranspose_mulVec_apply (n : ℕ)
    (y : Fin (n + 1) → ℂ) (j : Fin n) :
    ((padFirstMatrix n)ᴴ *ᵥ y) j = y (Fin.succ j) := by
  simp [Matrix.mulVec, dotProduct, padFirstMatrix,
    Matrix.conjTranspose_apply]

/-- Adjoint padding at the last coordinate reads the cast-successor entry. -/
@[simp] theorem padLastMatrix_conjTranspose_mulVec_apply (n : ℕ)
    (y : Fin (n + 1) → ℂ) (j : Fin n) :
    ((padLastMatrix n)ᴴ *ᵥ y) j = y (Fin.castSucc j) := by
  simp [Matrix.mulVec, dotProduct, padLastMatrix,
    Matrix.conjTranspose_apply]

/-- The displayed `C` normal lies in the kernel of `Cᴴ`, including the
zero-column case. -/
theorem rectangularC_conjTranspose_mulVec_rawNormal (n : ℕ) (p : ℂ) :
    (rectangularC n p)ᴴ *ᵥ rectangularCRawNormal n p = 0 := by
  ext j
  rw [rectangularC, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, sub_mulVec, smul_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply]
  rw [
    padFirstMatrix_conjTranspose_mulVec_apply,
    padLastMatrix_conjTranspose_mulVec_apply]
  change conj p * conj p ^ (n - (j.1 + 1)) - conj p ^ (n - j.1) = 0
  have hj : n - j.1 = (n - (j.1 + 1)) + 1 := by omega
  rw [hj, pow_succ]
  ring

/-- The displayed `D` normal lies in the kernel of `Dᴴ`. -/
theorem rectangularD_conjTranspose_mulVec_rawNormal (n : ℕ) (q : ℂ) :
    (rectangularD n q)ᴴ *ᵥ rectangularDRawNormal n q = 0 := by
  ext j
  rw [rectangularD, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, sub_mulVec, smul_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply]
  rw [
    padFirstMatrix_conjTranspose_mulVec_apply,
    padLastMatrix_conjTranspose_mulVec_apply]
  simp only [starRingEnd_apply, star_star, rectangularDRawNormal,
    Fin.val_succ, Fin.val_castSucc, smul_eq_mul]
  change q ^ (j.1 + 1) - q * q ^ j.1 = 0
  rw [pow_succ]
  ring

/-- Unit-normalized `C` range normal from the paper. -/
def rectangularCNormal (n : ℕ) (r θ : ℝ) : Fin (n + 1) → ℂ :=
  fun j =>
    ((Real.sqrt (rectangularNormalSq n r) : ℂ)⁻¹) *
      rectangularCRawNormal n (pathRootPlus r θ) j

/-- Unit-normalized `D` range normal from the paper. -/
def rectangularDNormal (n : ℕ) (r θ : ℝ) : Fin (n + 1) → ℂ :=
  fun j =>
    ((Real.sqrt (rectangularNormalSq n r) : ℂ)⁻¹) *
      rectangularDRawNormal n (pathRootMinus r θ) j

/-- Normalization does not change the `Cᴴ` kernel identity. -/
theorem rectangularC_conjTranspose_mulVec_normal (n : ℕ) (r θ : ℝ) :
    (rectangularC n (pathRootPlus r θ))ᴴ *ᵥ
      rectangularCNormal n r θ = 0 := by
  rw [show rectangularCNormal n r θ =
      ((Real.sqrt (rectangularNormalSq n r) : ℂ)⁻¹) •
        rectangularCRawNormal n (pathRootPlus r θ) by
    funext j
    rfl]
  rw [mulVec_smul, rectangularC_conjTranspose_mulVec_rawNormal, smul_zero]

/-- Normalization does not change the `Dᴴ` kernel identity. -/
theorem rectangularD_conjTranspose_mulVec_normal (n : ℕ) (r θ : ℝ) :
    (rectangularD n (pathRootMinus r θ))ᴴ *ᵥ
      rectangularDNormal n r θ = 0 := by
  rw [show rectangularDNormal n r θ =
      ((Real.sqrt (rectangularNormalSq n r) : ℂ)⁻¹) •
        rectangularDRawNormal n (pathRootMinus r θ) by
    funext j
    rfl]
  rw [mulVec_smul, rectangularD_conjTranspose_mulVec_rawNormal, smul_zero]

/-- Both characteristic roots lie on the circle of radius `r`. -/
theorem pathRootPlus_norm (r θ : ℝ) (hr : 0 ≤ r) :
    ‖pathRootPlus r θ‖ = r := by
  rw [pathRootPlus, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hr, Complex.norm_exp]
  simp

/-- The conjugate characteristic root has the same radius. -/
theorem pathRootMinus_norm (r θ : ℝ) (hr : 0 ≤ r) :
    ‖pathRootMinus r θ‖ = r := by
  rw [pathRootMinus, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hr, Complex.norm_exp]
  simp

/-- Squared Euclidean norm of the unnormalized `D` range normal. -/
theorem rectangularDRawNormal_norm_sq (n : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (θ : ℝ) :
    ‖WithLp.toLp 2
        (rectangularDRawNormal n (pathRootMinus r θ))‖ ^ 2 =
      rectangularNormalSq n r := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ j : Fin (n + 1),
      ‖pathRootMinus r θ ^ j.1‖ ^ 2) =
    ∑ j : Fin (n + 1), r ^ (2 * j.1)
  apply Finset.sum_congr rfl
  intro j _
  rw [norm_pow, pathRootMinus_norm r θ hr, ← pow_mul]
  congr 1
  omega

/-- Squared Euclidean norm of the reversed unnormalized `C` range normal. -/
theorem rectangularCRawNormal_norm_sq (n : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (θ : ℝ) :
    ‖WithLp.toLp 2
        (rectangularCRawNormal n (pathRootPlus r θ))‖ ^ 2 =
      rectangularNormalSq n r := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ j : Fin (n + 1),
      ‖conj (pathRootPlus r θ) ^ (n - j.1)‖ ^ 2) =
    ∑ j : Fin (n + 1), r ^ (2 * j.1)
  calc
    (∑ j : Fin (n + 1),
        ‖conj (pathRootPlus r θ) ^ (n - j.1)‖ ^ 2) =
        ∑ j : Fin (n + 1), r ^ (2 * (n - j.1)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [norm_pow, Complex.norm_conj, pathRootPlus_norm r θ hr,
            ← pow_mul]
          congr 1
          omega
    _ = ∑ j : Fin (n + 1), r ^ (2 * j.1) := by
      refine Fintype.sum_equiv (Fin.revPerm : Equiv.Perm (Fin (n + 1)))
        _ _ ?_
      intro j
      congr 2
      change n - j.1 = (Fin.rev j).1
      rw [Fin.val_rev]
      omega

/-- The paper's normalized `C` normal is a unit Euclidean vector. -/
theorem rectangularCNormal_norm (n : ℕ) (r θ : ℝ) (hr : 0 ≤ r) :
    ‖WithLp.toLp 2 (rectangularCNormal n r θ)‖ = 1 := by
  have hS : 0 ≤ rectangularNormalSq n r :=
    (rectangularNormalSq_pos n r).le
  have hsqrt : Real.sqrt (rectangularNormalSq n r) ≠ 0 :=
    (Real.sqrt_pos.2 (rectangularNormalSq_pos n r)).ne'
  have hraw :
      ‖WithLp.toLp 2
          (rectangularCRawNormal n (pathRootPlus r θ))‖ =
        Real.sqrt (rectangularNormalSq n r) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [rectangularCRawNormal_norm_sq n hr θ, Real.sq_sqrt hS]
  change ‖((Real.sqrt (rectangularNormalSq n r) : ℂ)⁻¹) •
      WithLp.toLp 2
        (rectangularCRawNormal n (pathRootPlus r θ))‖ = 1
  rw [norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), hraw]
  exact inv_mul_cancel₀ hsqrt

/-- The paper's normalized `D` normal is a unit Euclidean vector. -/
theorem rectangularDNormal_norm (n : ℕ) (r θ : ℝ) (hr : 0 ≤ r) :
    ‖WithLp.toLp 2 (rectangularDNormal n r θ)‖ = 1 := by
  have hS : 0 ≤ rectangularNormalSq n r :=
    (rectangularNormalSq_pos n r).le
  have hsqrt : Real.sqrt (rectangularNormalSq n r) ≠ 0 :=
    (Real.sqrt_pos.2 (rectangularNormalSq_pos n r)).ne'
  have hraw :
      ‖WithLp.toLp 2
          (rectangularDRawNormal n (pathRootMinus r θ))‖ =
        Real.sqrt (rectangularNormalSq n r) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [rectangularDRawNormal_norm_sq n hr θ, Real.sq_sqrt hS]
  change ‖((Real.sqrt (rectangularNormalSq n r) : ℂ)⁻¹) •
      WithLp.toLp 2
        (rectangularDRawNormal n (pathRootMinus r θ))‖ = 1
  rw [norm_smul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), hraw]
  exact inv_mul_cancel₀ hsqrt

/-- The algebraic Hermitian square norm agrees with the Euclidean square
norm after applying `WithLp.toLp 2`. -/
theorem star_dotProduct_self_eq_norm_sq {n : ℕ} (x : Fin n → ℂ) :
    star x ⬝ᵥ x = ((‖WithLp.toLp 2 x‖ ^ 2 : ℝ) : ℂ) := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp]
  simp

/-- The linear functional whose kernel is the hyperplane perpendicular to
`u` for the standard Hermitian product. -/
def rectangularNormalFunctional {n : ℕ} (u : Fin n → ℂ) :
    Module.Dual ℂ (Fin n → ℂ) :=
  dotProductBilin ℂ ℂ (star u)

@[simp] theorem rectangularNormalFunctional_apply {n : ℕ}
    (u y : Fin n → ℂ) :
    rectangularNormalFunctional u y = star u ⬝ᵥ y :=
  rfl

/-- A unit vector defines a nonzero normal functional. -/
theorem rectangularNormalFunctional_ne_zero {n : ℕ} (u : Fin n → ℂ)
    (hu : ‖WithLp.toLp 2 u‖ = 1) :
    rectangularNormalFunctional u ≠ 0 := by
  intro hzero
  have heval : rectangularNormalFunctional u u = 0 := by
    rw [hzero]
    rfl
  rw [rectangularNormalFunctional_apply,
    star_dotProduct_self_eq_norm_sq, hu] at heval
  norm_num at heval

/-- The kernel of a unit normal functional on `ℂ^(n+1)` has dimension `n`. -/
theorem rectangularNormalFunctional_finrank_ker (n : ℕ)
    (u : Fin (n + 1) → ℂ) (hu : ‖WithLp.toLp 2 u‖ = 1) :
    Module.finrank ℂ (LinearMap.ker (rectangularNormalFunctional u)) = n := by
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero
    (rectangularNormalFunctional_ne_zero u hu)
  rw [Module.finrank_fin_fun] at hdim
  omega

/-- An adjoint-kernel vector annihilates the full column range. -/
theorem range_mulVecLin_le_ker_normalFunctional {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (u : Fin m → ℂ)
    (hu : Mᴴ *ᵥ u = 0) :
    LinearMap.range M.mulVecLin ≤
      LinearMap.ker (rectangularNormalFunctional u) := by
  rintro y ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  change star u ⬝ᵥ (M *ᵥ x) = 0
  have hrow : star u ᵥ* M = 0 := by
    have hstar := congrArg star hu
    simpa only [star_mulVec, Matrix.conjTranspose_conjTranspose,
      star_zero] using hstar
  rw [dotProduct_mulVec, hrow, zero_dotProduct]

/-- A positive homogeneous Euclidean lower bound makes a rectangular
matrix injective on its column space. -/
theorem mulVecLin_injective_of_norm_sq_lower_bound {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hbound : ∀ x : Fin n → ℂ,
      δ * ‖WithLp.toLp 2 x‖ ^ 2 ≤
        ‖WithLp.toLp 2 (M *ᵥ x)‖ ^ 2) :
    Function.Injective M.mulVecLin := by
  intro x y hxy
  change M *ᵥ x = M *ᵥ y at hxy
  have hzero : M *ᵥ (x - y) = 0 := by
    rw [mulVec_sub, hxy, sub_self]
  have hb := hbound (x - y)
  have hb' : δ * ‖WithLp.toLp 2 (x - y)‖ ^ 2 ≤ 0 := by
    calc
      δ * ‖WithLp.toLp 2 (x - y)‖ ^ 2 ≤
          ‖WithLp.toLp 2 (M *ᵥ (x - y))‖ ^ 2 := hb
      _ = 0 := by rw [hzero]; simp
  have hnorm : ‖WithLp.toLp 2 (x - y)‖ = 0 := by
    have hn := norm_nonneg (WithLp.toLp 2 (x - y))
    have hsq_nonpos : ‖WithLp.toLp 2 (x - y)‖ ^ 2 ≤ 0 :=
      nonpos_of_mul_nonpos_right hb' hδ
    nlinarith [hsq_nonpos, sq_nonneg ‖WithLp.toLp 2 (x - y)‖]
  have htoLp : WithLp.toLp 2 (x - y) = 0 := norm_eq_zero.mp hnorm
  have hsub : x - y = 0 := (WithLp.toLp_eq_zero 2).mp htoLp
  exact sub_eq_zero.mp hsub

/-- Positivity of the sharp common Gram lower endpoint when `0 < r < 1`. -/
theorem rectangularGramLowerCoefficient_pos (n : ℕ) {r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) :
    0 < 1 + r ^ 2 -
      2 * r * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ)) := by
  have hscale : 0 ≤ 2 * r := by positivity
  have hcos := mul_le_mul_of_nonneg_left
    (Real.cos_le_one (Real.pi / ((n + 1 : ℕ) : ℝ))) hscale
  have hsquare : 0 < (1 - r) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr hr1)
  nlinarith

/-- The first rectangular factor has full column rank. -/
theorem rectangularC_mulVecLin_injective (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    Function.Injective
      (rectangularC n (pathRootPlus r θ)).mulVecLin := by
  apply mulVecLin_injective_of_norm_sq_lower_bound _ _
    (rectangularGramLowerCoefficient_pos n hr hr1)
  intro x
  exact rectangularC_norm_sq_lower_bound n hn hr θ x

/-- The second rectangular factor has full column rank. -/
theorem rectangularD_mulVecLin_injective (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    Function.Injective
      (rectangularD n (pathRootMinus r θ)).mulVecLin := by
  apply mulVecLin_injective_of_norm_sq_lower_bound _ _
    (rectangularGramLowerCoefficient_pos n hr hr1)
  intro x
  exact rectangularD_norm_sq_lower_bound n hn hr θ x

/-- Exact range-hyperplane identity for the paper's first rectangular
factor. -/
theorem rectangularC_range_eq_ker_normalFunctional (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    LinearMap.range (rectangularC n (pathRootPlus r θ)).mulVecLin =
      LinearMap.ker (rectangularNormalFunctional
        (rectangularCNormal n r θ)) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact range_mulVecLin_le_ker_normalFunctional _ _
      (rectangularC_conjTranspose_mulVec_normal n r θ)
  · have hrange :
        Module.finrank ℂ
            (LinearMap.range
              (rectangularC n (pathRootPlus r θ)).mulVecLin) = n := by
      rw [LinearMap.finrank_range_of_inj
        (rectangularC_mulVecLin_injective n hn hr hr1 θ),
        Module.finrank_fin_fun]
    have hker := rectangularNormalFunctional_finrank_ker n
      (rectangularCNormal n r θ) (rectangularCNormal_norm n r θ hr.le)
    exact hrange.trans hker.symm

/-- Exact range-hyperplane identity for the paper's second rectangular
factor. -/
theorem rectangularD_range_eq_ker_normalFunctional (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    LinearMap.range (rectangularD n (pathRootMinus r θ)).mulVecLin =
      LinearMap.ker (rectangularNormalFunctional
        (rectangularDNormal n r θ)) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · exact range_mulVecLin_le_ker_normalFunctional _ _
      (rectangularD_conjTranspose_mulVec_normal n r θ)
  · have hrange :
        Module.finrank ℂ
            (LinearMap.range
              (rectangularD n (pathRootMinus r θ)).mulVecLin) = n := by
      rw [LinearMap.finrank_range_of_inj
        (rectangularD_mulVecLin_injective n hn hr hr1 θ),
        Module.finrank_fin_fun]
    have hker := rectangularNormalFunctional_finrank_ker n
      (rectangularDNormal n r θ) (rectangularDNormal_norm n r θ hr.le)
    exact hrange.trans hker.symm

/-- Sine of the principal angle between the two codimension-one ranges,
represented by the modulus of the Hermitian overlap of their unit normals. -/
def rectangularPrincipalSine (n : ℕ) (r θ : ℝ) : ℝ :=
  ‖rectangularNormalFunctional (rectangularDNormal n r θ)
    (rectangularCNormal n r θ)‖

theorem rectangularPrincipalSine_nonneg (n : ℕ) (r θ : ℝ) :
    0 ≤ rectangularPrincipalSine n r θ :=
  norm_nonneg _

/-- The principal-angle sine defined by the two unit range normals is at
most one. -/
theorem rectangularPrincipalSine_le_one (n : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (θ : ℝ) :
    rectangularPrincipalSine n r θ ≤ 1 := by
  rw [rectangularPrincipalSine, rectangularNormalFunctional_apply,
    dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp]
  simpa [rectangularDNormal_norm n r θ hr,
    rectangularCNormal_norm n r θ hr] using
      norm_inner_le_norm
        (WithLp.toLp 2 (rectangularDNormal n r θ))
        (WithLp.toLp 2 (rectangularCNormal n r θ))

/-- For two unit normals, orthogonal projection from the first hyperplane
to the second loses at most the sine of their principal angle. -/
theorem unitHyperplane_projection_norm_lower_bound {n : ℕ}
    (u v y : EuclideanSpace ℂ (Fin n)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huy : ⟪u, y⟫_ℂ = 0) :
    ‖⟪v, u⟫_ℂ‖ * ‖y‖ ≤ ‖y - ⟪v, y⟫_ℂ • v‖ := by
  let β : ℂ := ⟪u, v⟫_ℂ
  let w : EuclideanSpace ℂ (Fin n) := v - β • u
  have huw : ⟪u, w⟫_ℂ = 0 := by
    dsimp [w, β]
    rw [inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hu]
    norm_num
  have horthw : ⟪β • u, w⟫_ℂ = 0 := by
    rw [inner_smul_left, huw, mul_zero]
  have hdecompw : β • u + w = v := by
    simp [w]
  have hpythw :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (β • u) w horthw
  rw [hdecompw, hv, norm_smul, hu] at hpythw
  simp only [mul_one] at hpythw
  have hwsq : ‖w‖ ^ 2 = 1 - ‖β‖ ^ 2 := by
    nlinarith
  let α : ℂ := ⟪v, y⟫_ℂ
  let z : EuclideanSpace ℂ (Fin n) := y - α • v
  have hvz : ⟪v, z⟫_ℂ = 0 := by
    dsimp [z, α]
    rw [inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hv]
    norm_num
  have horthz : ⟪α • v, z⟫_ℂ = 0 := by
    rw [inner_smul_left, hvz, mul_zero]
  have hdecompz : α • v + z = y := by
    simp [z]
  have hpythz :=
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (α • v) z horthz
  rw [hdecompz, norm_smul, hv] at hpythz
  simp only [mul_one] at hpythz
  have hwinner : ⟪w, y⟫_ℂ = α := by
    dsimp [w, β, α]
    rw [inner_sub_left, inner_smul_left, huy, mul_zero, sub_zero]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) w y
  rw [hwinner] at hcs
  have hcssq : ‖α‖ ^ 2 ≤ ‖w‖ ^ 2 * ‖y‖ ^ 2 := by
    have hsquare := (sq_le_sq₀ (norm_nonneg α)
      (mul_nonneg (norm_nonneg w) (norm_nonneg y))).mpr hcs
    simpa only [mul_pow] using hsquare
  rw [hwsq] at hcssq
  have hsq : (‖β‖ * ‖y‖) ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [mul_pow]
    nlinarith
  have hlinear := (sq_le_sq₀
    (mul_nonneg (norm_nonneg β) (norm_nonneg y))
    (norm_nonneg z)).mp hsq
  rw [show ‖β‖ = ‖⟪v, u⟫_ℂ‖ by
    exact norm_inner_symm u v] at hlinear
  simpa only [z, α] using hlinear

/-- The principal-angle projection lower bound for vectors in the range of
`C`; the projected vector lies in the `D` range hyperplane. -/
theorem rectangularPrincipalProjection_lower_bound (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ)
    {y : Fin (n + 1) → ℂ}
    (hy : y ∈ LinearMap.range
      (rectangularC n (pathRootPlus r θ)).mulVecLin) :
    rectangularPrincipalSine n r θ * ‖WithLp.toLp 2 y‖ ≤
      ‖WithLp.toLp 2 y -
        ⟪WithLp.toLp 2 (rectangularDNormal n r θ),
          WithLp.toLp 2 y⟫_ℂ •
            WithLp.toLp 2 (rectangularDNormal n r θ)‖ := by
  have hyker :
      y ∈ LinearMap.ker
        (rectangularNormalFunctional (rectangularCNormal n r θ)) := by
    rw [← rectangularC_range_eq_ker_normalFunctional n hn hr hr1 θ]
    exact hy
  have huy :
      ⟪WithLp.toLp 2 (rectangularCNormal n r θ),
        WithLp.toLp 2 y⟫_ℂ = 0 := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    exact LinearMap.mem_ker.mp hyker
  have hproj := unitHyperplane_projection_norm_lower_bound
    (WithLp.toLp 2 (rectangularCNormal n r θ))
    (WithLp.toLp 2 (rectangularDNormal n r θ))
    (WithLp.toLp 2 y)
    (rectangularCNormal_norm n r θ hr.le)
    (rectangularDNormal_norm n r θ hr.le) huy
  have hoverlap :
      rectangularPrincipalSine n r θ =
        ‖⟪WithLp.toLp 2 (rectangularDNormal n r θ),
          WithLp.toLp 2 (rectangularCNormal n r θ)⟫_ℂ‖ := by
    rw [rectangularPrincipalSine, rectangularNormalFunctional_apply,
      dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp]
  rw [hoverlap]
  exact hproj

/-- Orthogonal projection onto the hyperplane normal to `u`, in the paper's
plain-coordinate model of complex Euclidean space. -/
def rectangularNormalProjection {n : ℕ} (u y : Fin n → ℂ) : Fin n → ℂ :=
  y - rectangularNormalFunctional u y • u

theorem rectangularNormalProjection_mem_ker {n : ℕ} (u y : Fin n → ℂ)
    (hu : ‖WithLp.toLp 2 u‖ = 1) :
    rectangularNormalProjection u y ∈
      LinearMap.ker (rectangularNormalFunctional u) := by
  rw [LinearMap.mem_ker, rectangularNormalProjection,
    rectangularNormalFunctional_apply, dotProduct_sub,
    dotProduct_smul, star_dotProduct_self_eq_norm_sq, hu]
  norm_num

/-- Plain-coordinate form of the principal-angle projection estimate. -/
theorem rectangularPrincipalProjection_lower_bound_plain (n : ℕ)
    (hn : 0 < n) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ)
    {y : Fin (n + 1) → ℂ}
    (hy : y ∈ LinearMap.range
      (rectangularC n (pathRootPlus r θ)).mulVecLin) :
    rectangularPrincipalSine n r θ * ‖WithLp.toLp 2 y‖ ≤
      ‖WithLp.toLp 2
        (rectangularNormalProjection (rectangularDNormal n r θ) y)‖ := by
  have h := rectangularPrincipalProjection_lower_bound n hn hr hr1 θ hy
  have hcoeff :
      ⟪WithLp.toLp 2 (rectangularDNormal n r θ),
        WithLp.toLp 2 y⟫_ℂ =
      rectangularNormalFunctional (rectangularDNormal n r θ) y := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    rfl
  rw [hcoeff] at h
  exact h

/-- The Hermitian quadratic form of `Mᴴ M` is the squared Euclidean norm
of `M x`. -/
theorem inner_conjTranspose_mulVec_self {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (x : Fin n → ℂ) :
    ⟪WithLp.toLp 2 x,
      WithLp.toLp 2 (Mᴴ *ᵥ (M *ᵥ x))⟫_ℂ =
        (((‖WithLp.toLp 2 (M *ᵥ x)‖ ^ 2 : ℝ) : ℂ)) := by
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm,
    dotProduct_mulVec, vecMul_conjTranspose, star_star,
    star_dotProduct_self_eq_norm_sq]

/-- A lower norm bound for a rectangular map gives the same lower bound for
its adjoint on the map's range. -/
theorem conjTranspose_norm_lower_bound_on_range {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (μ : ℝ)
    (hbound : ∀ x : Fin n → ℂ,
      μ * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 (M *ᵥ x)‖)
    {y : Fin m → ℂ} (hy : y ∈ LinearMap.range M.mulVecLin) :
    μ * ‖WithLp.toLp 2 y‖ ≤ ‖WithLp.toLp 2 (Mᴴ *ᵥ y)‖ := by
  rcases hy with ⟨x, rfl⟩
  by_cases hx : x = 0
  · simp [hx]
  · have hxpos : 0 < ‖WithLp.toLp 2 x‖ := by
      rw [norm_pos_iff]
      exact fun hzero => hx ((WithLp.toLp_eq_zero 2).mp hzero)
    have hcs := norm_inner_le_norm (𝕜 := ℂ)
      (WithLp.toLp 2 x)
      (WithLp.toLp 2 (Mᴴ *ᵥ (M *ᵥ x)))
    rw [inner_conjTranspose_mulVec_self, Complex.norm_real,
      Real.norm_of_nonneg (sq_nonneg _)] at hcs
    have hprod :
        ‖WithLp.toLp 2 x‖ *
            (μ * ‖WithLp.toLp 2 (M *ᵥ x)‖) ≤
          ‖WithLp.toLp 2 x‖ *
            ‖WithLp.toLp 2 (Mᴴ *ᵥ (M *ᵥ x))‖ := by
      calc
        ‖WithLp.toLp 2 x‖ *
            (μ * ‖WithLp.toLp 2 (M *ᵥ x)‖) =
            (μ * ‖WithLp.toLp 2 x‖) *
              ‖WithLp.toLp 2 (M *ᵥ x)‖ := by ring
        _ ≤ ‖WithLp.toLp 2 (M *ᵥ x)‖ *
            ‖WithLp.toLp 2 (M *ᵥ x)‖ :=
          mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)
        _ ≤ ‖WithLp.toLp 2 x‖ *
            ‖WithLp.toLp 2 (Mᴴ *ᵥ (M *ᵥ x))‖ := by
          simpa only [pow_two] using hcs
    exact le_of_mul_le_mul_left hprod hxpos

/-- Product lower bound from the two rectangular Gram estimates and the
principal angle between their ranges. -/
theorem rectangularFactor_norm_lower_bound (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ)
    (x : Fin n → ℂ) :
    (1 + r ^ 2 -
        2 * r * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ))) *
        rectangularPrincipalSine n r θ * ‖WithLp.toLp 2 x‖ ≤
      ‖WithLp.toLp 2
        (((rectangularD n (pathRootMinus r θ))ᴴ *
          rectangularC n (pathRootPlus r θ)) *ᵥ x)‖ := by
  let δ : ℝ := 1 + r ^ 2 -
    2 * r * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ))
  let μ : ℝ := Real.sqrt δ
  let C := rectangularC n (pathRootPlus r θ)
  let D := rectangularD n (pathRootMinus r θ)
  let y : Fin (n + 1) → ℂ := C *ᵥ x
  let uD : Fin (n + 1) → ℂ := rectangularDNormal n r θ
  let z : Fin (n + 1) → ℂ := rectangularNormalProjection uD y
  have hδ : 0 ≤ δ :=
    (rectangularGramLowerCoefficient_pos n hr hr1).le
  have hμ : 0 ≤ μ := Real.sqrt_nonneg _
  have hμsq : μ ^ 2 = δ := Real.sq_sqrt hδ
  have hC : μ * ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 y‖ := by
    exact rectangularC_norm_lower_bound n hn hr θ x
  have hy : y ∈ LinearMap.range C.mulVecLin := by
    exact ⟨x, rfl⟩
  have hprojection :
      rectangularPrincipalSine n r θ * ‖WithLp.toLp 2 y‖ ≤
        ‖WithLp.toLp 2 z‖ := by
    exact rectangularPrincipalProjection_lower_bound_plain n hn hr hr1 θ hy
  have hzker :
      z ∈ LinearMap.ker (rectangularNormalFunctional uD) :=
    rectangularNormalProjection_mem_ker uD y
      (rectangularDNormal_norm n r θ hr.le)
  have hzrange : z ∈ LinearMap.range D.mulVecLin := by
    rw [rectangularD_range_eq_ker_normalFunctional n hn hr hr1 θ]
    exact hzker
  have hDstar : μ * ‖WithLp.toLp 2 z‖ ≤
      ‖WithLp.toLp 2 (Dᴴ *ᵥ z)‖ := by
    apply conjTranspose_norm_lower_bound_on_range D μ
    · intro w
      exact rectangularD_norm_lower_bound n hn hr θ w
    · exact hzrange
  have hDz : Dᴴ *ᵥ z = Dᴴ *ᵥ y := by
    dsimp only [z, uD, D]
    rw [rectangularNormalProjection, mulVec_sub, mulVec_smul,
      rectangularD_conjTranspose_mulVec_normal, smul_zero, sub_zero]
  change δ * rectangularPrincipalSine n r θ *
      ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 ((Dᴴ * C) *ᵥ x)‖
  rw [← Matrix.mulVec_mulVec]
  change _ ≤ ‖WithLp.toLp 2 (Dᴴ *ᵥ y)‖
  calc
    δ * rectangularPrincipalSine n r θ * ‖WithLp.toLp 2 x‖ =
        μ * (rectangularPrincipalSine n r θ *
          (μ * ‖WithLp.toLp 2 x‖)) := by rw [← hμsq]; ring
    _ ≤ μ * (rectangularPrincipalSine n r θ *
        ‖WithLp.toLp 2 y‖) := by
      gcongr
      exact rectangularPrincipalSine_nonneg n r θ
    _ ≤ μ * ‖WithLp.toLp 2 z‖ := by gcongr
    _ ≤ ‖WithLp.toLp 2 (Dᴴ *ᵥ z)‖ := hDstar
    _ = ‖WithLp.toLp 2 (Dᴴ *ᵥ y)‖ := by rw [hDz]

/-- Least-singular-value form of the rectangular principal-angle product
estimate. -/
theorem rectangularFactor_le_leastSingularValue (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    (1 + r ^ 2 -
        2 * r * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ))) *
        rectangularPrincipalSine n r θ ≤
      leastSingularValue
        ((rectangularD n (pathRootMinus r θ))ᴴ *
          rectangularC n (pathRootPlus r θ)) := by
  let M := (rectangularD n (pathRootMinus r θ))ᴴ *
    rectangularC n (pathRootPlus r θ)
  let v := leastSingularVector M
  have h := rectangularFactor_norm_lower_bound n hn hr hr1 θ
    (WithLp.ofLp v)
  have hv : ‖WithLp.toLp 2 (WithLp.ofLp v)‖ = 1 := by
    exact norm_leastSingularVector M hn
  rw [hv, mul_one] at h
  change _ ≤ leastSingularValue M
  rw [leastSingularValue_eq_norm_apply]
  simpa only [matrixOperator_toLp, v] using h

/-- The rectangular product is exactly the shifted path matrix at the
trigonometric point `x = 2 r cos θ`. -/
theorem shiftedPathMatrix_eq_rectangularFactor (n : ℕ) (r θ : ℝ) :
    shiftedPathMatrix n (r ^ 2) ((2 * r * Real.cos θ : ℝ) : ℂ) =
      (rectangularD n (pathRootMinus r θ))ᴴ *
        rectangularC n (pathRootPlus r θ) := by
  rw [rectangular_path_factorization]
  change
    (((2 * r * Real.cos θ : ℝ) : ℂ) •
        (1 : Matrix (Fin n) (Fin n) ℂ) -
      (pathMatrix n (r ^ 2)).map Complex.ofRealHom) =
      (((2 * r * Real.cos θ) •
          (1 : Matrix (Fin n) (Fin n) ℝ) -
        pathMatrix n (r ^ 2)).map Complex.ofRealHom)
  rw [Matrix.map_sub _ (map_sub Complex.ofRealHom),
    Matrix.map_smul' _ _ _ (map_mul Complex.ofRealHom),
    Matrix.map_one _ (map_zero Complex.ofRealHom) (map_one Complex.ofRealHom),
    Complex.ofRealHom_eq_coe]

/-- Principal-angle lower bound for the actual real-axis least singular
value of the path matrix. -/
theorem realGapValue_rectangular_lower_bound (n : ℕ) (hn : 0 < n)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    (1 + r ^ 2 -
        2 * r * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ))) *
        rectangularPrincipalSine n r θ ≤
      realGapValue n (r ^ 2) (2 * r * Real.cos θ) := by
  unfold realGapValue pseudospectralHeight
  rw [shiftedPathMatrix_eq_rectangularFactor]
  exact rectangularFactor_le_leastSingularValue n hn hr hr1 θ

/-- Complex conjugation interchanges the two characteristic roots. -/
theorem conj_pathRootPlus (r θ : ℝ) :
    conj (pathRootPlus r θ) = pathRootMinus r θ := by
  rw [pathRootPlus, pathRootMinus, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj]
  congr 2
  simp

/-- Complex conjugation interchanges the two characteristic roots. -/
theorem conj_pathRootMinus (r θ : ℝ) :
    conj (pathRootMinus r θ) = pathRootPlus r θ := by
  rw [pathRootPlus, pathRootMinus, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj]
  congr 2
  simp

theorem star_pathRootPlus (r θ : ℝ) :
    star (pathRootPlus r θ) = pathRootMinus r θ :=
  conj_pathRootPlus r θ

theorem star_pathRootMinus (r θ : ℝ) :
    star (pathRootMinus r θ) = pathRootPlus r θ :=
  conj_pathRootMinus r θ

/-- The homogeneous geometric sum occurring in the overlap of the two
range normals. -/
def rectangularHomogeneousSum (n : ℕ) (r θ : ℝ) : ℂ :=
  ∑ j : Fin (n + 1),
    pathRootPlus r θ ^ j.1 * pathRootMinus r θ ^ (n - j.1)

/-- Exact normalized overlap before evaluating the homogeneous geometric
sum. -/
theorem rectangularNormalFunctional_overlap_eq (n : ℕ) (r θ : ℝ) :
    rectangularNormalFunctional (rectangularDNormal n r θ)
        (rectangularCNormal n r θ) =
      ((rectangularNormalSq n r : ℂ)⁻¹) *
        rectangularHomogeneousSum n r θ := by
  have hS : 0 ≤ rectangularNormalSq n r :=
    (rectangularNormalSq_pos n r).le
  have hsquare :
      ((Real.sqrt (rectangularNormalSq n r) : ℂ) ^ 2) =
        (rectangularNormalSq n r : ℂ) := by
    exact_mod_cast Real.sq_sqrt hS
  have hscalar :
      ((Real.sqrt (rectangularNormalSq n r) : ℂ)⁻¹) ^ 2 =
        (rectangularNormalSq n r : ℂ)⁻¹ := by
    rw [inv_pow, hsquare]
  rw [rectangularNormalFunctional_apply]
  unfold dotProduct rectangularHomogeneousSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.star_apply, rectangularDNormal, rectangularCNormal,
    rectangularDRawNormal, rectangularCRawNormal]
  rw [StarMul.star_mul, star_inv₀, star_pow,
    show star (Real.sqrt (rectangularNormalSq n r) : ℂ) =
      (Real.sqrt (rectangularNormalSq n r) : ℂ) by simp,
    star_pathRootMinus, starRingEnd_apply, star_pathRootPlus]
  rw [← hscalar]
  ring

/-- Homogeneous two-variable geometric-sum identity. -/
theorem rectangularHomogeneousSum_mul_sub (n : ℕ) (r θ : ℝ) :
    (pathRootPlus r θ - pathRootMinus r θ) *
        rectangularHomogeneousSum n r θ =
      pathRootPlus r θ ^ (n + 1) - pathRootMinus r θ ^ (n + 1) := by
  rw [rectangularHomogeneousSum,
    Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      pathRootPlus r θ ^ j * pathRootMinus r θ ^ (n - j))]
  simpa using
    (Commute.all (pathRootPlus r θ) (pathRootMinus r θ)).mul_geom_sum₂
      (n + 1)

/-- The point `3π/(2(n+1))` selected in the first spectral gap. -/
def rectangularSpecialAngle (n : ℕ) : ℝ :=
  3 * Real.pi / (2 * ((n + 1 : ℕ) : ℝ))

theorem rectangularSpecialAngle_pos (n : ℕ) :
    0 < rectangularSpecialAngle n := by
  unfold rectangularSpecialAngle
  positivity

theorem rectangularSpecialAngle_lt_pi (n : ℕ) (hn : 2 ≤ n) :
    rectangularSpecialAngle n < Real.pi := by
  have hN : (3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 3 ≤ n + 1 by omega)
  have hden : 0 < 2 * ((n + 1 : ℕ) : ℝ) := by positivity
  rw [rectangularSpecialAngle, div_lt_iff₀ hden]
  nlinarith [Real.pi_pos]

theorem rectangularSpecialAngle_sin_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < Real.sin (rectangularSpecialAngle n) :=
  Real.sin_pos_of_pos_of_lt_pi (rectangularSpecialAngle_pos n)
    (rectangularSpecialAngle_lt_pi n hn)

theorem rectangularSpecialAngle_le_pi_div_two (n : ℕ) (hn : 2 ≤ n) :
    rectangularSpecialAngle n ≤ Real.pi / 2 := by
  have hN : (3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 3 ≤ n + 1 by omega)
  have hden : 0 < 2 * ((n + 1 : ℕ) : ℝ) := by positivity
  have hmul : 3 * Real.pi ≤ ((n + 1 : ℕ) : ℝ) * Real.pi :=
    mul_le_mul_of_nonneg_right hN Real.pi_pos.le
  rw [rectangularSpecialAngle, div_le_iff₀ hden]
  nlinarith

theorem baseAngle_le_rectangularSpecialAngle (n : ℕ) :
    Real.pi / ((n + 1 : ℕ) : ℝ) ≤ rectangularSpecialAngle n := by
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have heq :
      rectangularSpecialAngle n =
        (3 / 2 : ℝ) * (Real.pi / ((n + 1 : ℕ) : ℝ)) := by
    rw [rectangularSpecialAngle]
    field_simp
  rw [heq]
  have hbase : 0 ≤ Real.pi / ((n + 1 : ℕ) : ℝ) :=
    div_nonneg Real.pi_pos.le hNpos.le
  nlinarith

/-- The paper's selected first-gap point belongs to the real spectral
interval. -/
theorem rectangularSpecialPoint_mem_spectralInterval (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    2 * r * Real.cos (rectangularSpecialAngle n) ∈
      spectralInterval n (r ^ 2) := by
  have hθnonneg : 0 ≤ rectangularSpecialAngle n :=
    (rectangularSpecialAngle_pos n).le
  have hθle : rectangularSpecialAngle n ≤ Real.pi / 2 :=
    rectangularSpecialAngle_le_pi_div_two n hn
  have hcosθ : 0 ≤ Real.cos (rectangularSpecialAngle n) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθle⟩
  have hbaseNonneg :
      0 ≤ Real.pi / ((n + 1 : ℕ) : ℝ) := by positivity
  have hbaseLe :
      Real.pi / ((n + 1 : ℕ) : ℝ) ≤ rectangularSpecialAngle n :=
    baseAngle_le_rectangularSpecialAngle n
  have hcosLe :
      Real.cos (rectangularSpecialAngle n) ≤
        Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ)) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hbaseNonneg
      (rectangularSpecialAngle_lt_pi n hn).le hbaseLe
  simp only [Nat.cast_add, Nat.cast_one] at hcosLe
  rw [spectralInterval, Set.mem_Icc, spectralRadius, pathRate,
    Real.sqrt_sq_eq_abs, abs_of_pos hr]
  constructor
  · have hxnonneg :
        0 ≤ 2 * r * Real.cos (rectangularSpecialAngle n) := by positivity
    have hradius :
        0 ≤ 2 * r * Real.cos (Real.pi / ((n : ℝ) + 1)) := by
      have hcosBase :
          0 ≤ Real.cos (Real.pi / ((n : ℝ) + 1)) :=
        hcosθ.trans hcosLe
      positivity
    linarith
  · exact mul_le_mul_of_nonneg_left hcosLe (by positivity)

theorem exp_three_pi_div_two_mul_I :
    Complex.exp (((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
      -Complex.I := by
  rw [show (((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
      (Real.pi : ℂ) * Complex.I +
        ((Real.pi / 2 : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_add]
  simp

theorem pathRootPlus_special_pow (n : ℕ) (r : ℝ) :
    pathRootPlus r (rectangularSpecialAngle n) ^ (n + 1) =
      -((r : ℂ) ^ (n + 1)) * Complex.I := by
  rw [pathRootPlus, mul_pow, ← Complex.exp_nat_mul]
  have harg :
      ((n + 1 : ℕ) : ℂ) *
          (((rectangularSpecialAngle n : ℝ) : ℂ) * Complex.I) =
        (((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [rectangularSpecialAngle]
    push_cast
    field_simp
  rw [harg, exp_three_pi_div_two_mul_I]
  ring

theorem pathRootMinus_special_pow (n : ℕ) (r : ℝ) :
    pathRootMinus r (rectangularSpecialAngle n) ^ (n + 1) =
      (r : ℂ) ^ (n + 1) * Complex.I := by
  rw [pathRootMinus, mul_pow, ← Complex.exp_nat_mul]
  have harg :
      ((n + 1 : ℕ) : ℂ) *
          (-((rectangularSpecialAngle n : ℝ) : ℂ) * Complex.I) =
        -(((3 * Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
    rw [rectangularSpecialAngle]
    push_cast
    field_simp
  rw [harg, Complex.exp_neg, exp_three_pi_div_two_mul_I]
  simp

theorem pathRootPlus_sub_pathRootMinus (r θ : ℝ) :
    pathRootPlus r θ - pathRootMinus r θ =
      ((2 * r * Real.sin θ : ℝ) : ℂ) * Complex.I := by
  rw [pathRootPlus, pathRootMinus, Complex.exp_mul_I, Complex.exp_mul_I]
  simp
  ring

/-- Exact modulus of the homogeneous geometric sum at the selected first-gap
point. -/
theorem rectangularHomogeneousSum_norm_special (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    ‖rectangularHomogeneousSum n r (rectangularSpecialAngle n)‖ =
      r ^ n / Real.sin (rectangularSpecialAngle n) := by
  have hsin : 0 < Real.sin (rectangularSpecialAngle n) :=
    rectangularSpecialAngle_sin_pos n hn
  have hden :
      ‖pathRootPlus r (rectangularSpecialAngle n) -
          pathRootMinus r (rectangularSpecialAngle n)‖ =
        2 * r * Real.sin (rectangularSpecialAngle n) := by
    rw [pathRootPlus_sub_pathRootMinus, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hr.le) hsin.le)]
    norm_num
  have hnum :
      ‖pathRootPlus r (rectangularSpecialAngle n) ^ (n + 1) -
          pathRootMinus r (rectangularSpecialAngle n) ^ (n + 1)‖ =
        2 * r ^ (n + 1) := by
    rw [pathRootPlus_special_pow, pathRootMinus_special_pow]
    calc
      ‖-((r : ℂ) ^ (n + 1)) * Complex.I -
          (r : ℂ) ^ (n + 1) * Complex.I‖ =
          ‖((-(2 * r ^ (n + 1)) : ℝ) : ℂ) * Complex.I‖ := by
            congr 1
            push_cast
            ring
      _ = 2 * r ^ (n + 1) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_neg, abs_of_nonneg
            (mul_nonneg (by norm_num) (pow_nonneg hr.le _))]
        norm_num
  have hnorm := congrArg norm
    (rectangularHomogeneousSum_mul_sub n r (rectangularSpecialAngle n))
  rw [norm_mul, hden, hnum] at hnorm
  have hcancel :
      Real.sin (rectangularSpecialAngle n) *
          ‖rectangularHomogeneousSum n r (rectangularSpecialAngle n)‖ =
        r ^ n := by
    apply mul_left_cancel₀ (show 2 * r ≠ 0 by positivity)
    calc
      (2 * r) * (Real.sin (rectangularSpecialAngle n) *
          ‖rectangularHomogeneousSum n r (rectangularSpecialAngle n)‖) =
          (2 * r * Real.sin (rectangularSpecialAngle n)) *
            ‖rectangularHomogeneousSum n r (rectangularSpecialAngle n)‖ := by ring
      _ = 2 * r ^ (n + 1) := hnorm
      _ = (2 * r) * r ^ n := by rw [pow_succ]; ring
  apply (eq_div_iff hsin.ne').2
  rw [mul_comm]
  exact hcancel

/-- Principal-angle overlap at `3π/(2(n+1))`, first in normalization-sum
form. -/
theorem rectangularPrincipalSine_special (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    rectangularPrincipalSine n r (rectangularSpecialAngle n) =
      r ^ n /
        (rectangularNormalSq n r * Real.sin (rectangularSpecialAngle n)) := by
  rw [rectangularPrincipalSine, rectangularNormalFunctional_overlap_eq,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg
      (rectangularNormalSq_pos n r).le,
    rectangularHomogeneousSum_norm_special n hn hr]
  field_simp [rectangularNormalSq_ne_zero n r,
    (rectangularSpecialAngle_sin_pos n hn).ne']

/-- Closed paper form of the principal-angle overlap at the selected
first-gap point. -/
theorem rectangularPrincipalSine_special_closed (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    rectangularPrincipalSine n r (rectangularSpecialAngle n) =
      r ^ n * (1 - r ^ 2) /
        ((1 - r ^ (2 * (n + 1))) *
          Real.sin (rectangularSpecialAngle n)) := by
  rw [rectangularPrincipalSine_special n hn hr,
    rectangularNormalSq_eq_closed n hr1 hr.le]
  have hden : 1 - r ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg r]
  field_simp [hden]

/-- The selected first-gap point proves the explicit lower barrier for the
square-root parameter `a = r²`. -/
theorem rectangularSpecial_lower_le_gapBarrier (n : ℕ) (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (1 + r ^ 2 -
        2 * r * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ))) *
        (r ^ n * (1 - r ^ 2) /
          ((1 - r ^ (2 * (n + 1))) *
            Real.sin (rectangularSpecialAngle n))) ≤
      gapBarrier n (r ^ 2) := by
  have hlower := realGapValue_rectangular_lower_bound n
    (by omega) hr hr1 (rectangularSpecialAngle n)
  rw [rectangularPrincipalSine_special_closed n hn hr hr1] at hlower
  exact hlower.trans (realGapValue_le_gapBarrier n (r ^ 2)
    (2 * r * Real.cos (rectangularSpecialAngle n))
    (rectangularSpecialPoint_mem_spectralInterval n hn hr))

/-- The paper's explicit lower barrier is bounded by the attained real-gap
barrier.  This is the lower inequality in `prop:gap-bounds`. -/
theorem lowerBarrier_le_gapBarrier (n : ℕ) (hn : 2 ≤ n)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    lowerBarrier n a ≤ gapBarrier n a := by
  let r : ℝ := pathRate a
  have hr : 0 < r := Real.sqrt_pos.2 ha
  have hr1 : r < 1 := by
    have hsqrt : Real.sqrt a < Real.sqrt 1 :=
      (Real.sqrt_lt_sqrt_iff ha.le).2 ha1
    simpa [r, pathRate] using hsqrt
  have hrsq : r ^ 2 = a := by
    exact Real.sq_sqrt ha.le
  have h := rectangularSpecial_lower_le_gapBarrier n hn hr hr1
  unfold lowerBarrier
  dsimp only
  rw [show pathRate a = r by rfl]
  calc
    _ = (1 + r ^ 2 -
          2 * r * Real.cos (Real.pi / ((n : ℝ) + 1))) *
          (r ^ n * (1 - r ^ 2) /
            ((1 - r ^ (2 * (n + 1))) *
              Real.sin (3 * Real.pi / (2 * ((n : ℝ) + 1))))) := by ring
    _ ≤ gapBarrier n (r ^ 2) := by
      simpa only [rectangularSpecialAngle, Nat.cast_add, Nat.cast_one] using h
    _ = gapBarrier n a := by rw [hrsq]

end

end ConnectedPseudospectrum
