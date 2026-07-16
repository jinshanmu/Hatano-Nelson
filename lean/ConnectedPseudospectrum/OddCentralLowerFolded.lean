import ConnectedPseudospectrum.OddCentralLowerScalar
import ConnectedPseudospectrum.FoldedChebyshev
import ConnectedPseudospectrum.FoldedMinorBridge

/-!
# Folded determinant certificate for the odd central lower comparison

This module formalizes the folded determinant argument from
`eq:x-star-central` through `eq:q-product-central`.  It turns the strict scalar
inequality `lowerCentral_scalar_target` into the literal determinant-product
statement `eq:q-product-central` for the odd signed pencil of order `2m+1`.

The two folded arguments are used as the unordered pair `xi,-omega`.  The
generic divided-difference theorem only needs their symmetric sum and
product, so no identification with a particular square-root branch is made.
-/

namespace ConnectedPseudospectrum

noncomputable section

namespace OddCentralChordData

/-! ## The source's test abscissa and lower bidiagonal height -/

/-- The lower-comparison bidiagonal height `c=c_L`, with `L=m+1`. -/
def lowerCentralC (d : OddCentralChordData) : Real :=
  centralBidiagonalHeight (d.m + 1) d.a

/-- The radicand defining the positive test abscissa `x_*`. -/
def lowerCentralXStarSq (d : OddCentralChordData) : Real :=
  2 * d.a * d.lowerCentralOmegaDelta *
      (d.lowerCentralRho + d.lowerCentralOmega) /
    (d.transformedZeta + d.lowerCentralOmega)

/-- The positive square-root choice in `eq:x-star-central`. -/
def lowerCentralXStar (d : OddCentralChordData) : Real :=
  Real.sqrt d.lowerCentralXStarSq

/-- The folded numerator `n_s(t)` printed immediately after
`eq:x-star-central`. -/
def lowerCentralNumerator
    (d : OddCentralChordData) (x s t : Real) : Real :=
  -(x * (d.transformedZeta - t) + s * (1 + t)) *
    chebyshevU d.m t

/-- `X_xi=x_*(zeta-xi)`. -/
def lowerCentralXXi (d : OddCentralChordData) : Real :=
  d.lowerCentralXStar * (d.transformedZeta - d.lowerCentralXi)

/-- `Y_xi=c(1+xi)`. -/
def lowerCentralYXi (d : OddCentralChordData) : Real :=
  d.lowerCentralC * (1 + d.lowerCentralXi)

/-- `X_omega=x_*(zeta+omega_L)`. -/
def lowerCentralXOmega (d : OddCentralChordData) : Real :=
  d.lowerCentralXStar * (d.transformedZeta + d.lowerCentralOmega)

/-- `Y_omega=c Delta_omega`. -/
def lowerCentralYOmega (d : OddCentralChordData) : Real :=
  d.lowerCentralC * d.lowerCentralOmegaDelta

/-- The common ratio `r_*=Y_omega/X_omega=X_xi/Y_xi`. -/
def lowerCentralRStar (d : OddCentralChordData) : Real :=
  d.lowerCentralYOmega / d.lowerCentralXOmega

/-- The common nonzero divided-difference factor
`a^(L-1)/(xi+omega_L)`. -/
def lowerCentralFoldFactor (d : OddCentralChordData) : Real :=
  d.a ^ d.m / (d.lowerCentralXi + d.lowerCentralOmega)

theorem lowerCentralZeta_add_Omega_pos (d : OddCentralChordData) :
    0 < d.transformedZeta + d.lowerCentralOmega := by
  linarith [one_lt_transformedZeta d, lowerCentralOmega_pos d]

theorem lowerCentralZeta_sub_Rho_pos (d : OddCentralChordData) :
    0 < d.transformedZeta - d.lowerCentralRho := by
  simpa only [transformedZeta, lowerCentralRho] using
    centralZeta_sub_rho_pos (d.m + 1) (by omega) d.a d.ha0 d.ha1

theorem lowerCentralXi_pos (d : OddCentralChordData) :
    0 < d.lowerCentralXi := by
  have hnode : 0 ≤ centralChebyshevFirstNode d.m :=
    transformedFirstNode_nonneg d
  exact hnode.trans_lt (lowerCentralXi_above_firstNode d)

theorem lowerCentralZeta_sub_Xi_pos (d : OddCentralChordData) :
    0 < d.transformedZeta - d.lowerCentralXi := by
  have hzr := lowerCentralZeta_sub_Rho_pos d
  have hxr := lowerCentralXi_lt_Rho d
  linarith

theorem lowerCentralC_pos (d : OddCentralChordData) :
    0 < d.lowerCentralC := by
  exact centralBidiagonalHeight_pos (d.m + 1) (by omega) d.a d.ha0

theorem lowerCentralXStarSq_pos (d : OddCentralChordData) :
    0 < d.lowerCentralXStarSq := by
  unfold lowerCentralXStarSq
  exact div_pos
    (mul_pos
      (mul_pos
        (mul_pos (by norm_num) d.ha0)
        (lowerCentralOmegaDelta_pos d))
      (add_pos (lowerCentralRho_pos d) (lowerCentralOmega_pos d)))
    (lowerCentralZeta_add_Omega_pos d)

theorem lowerCentralXStar_pos (d : OddCentralChordData) :
    0 < d.lowerCentralXStar := by
  exact Real.sqrt_pos.2 (lowerCentralXStarSq_pos d)

theorem lowerCentralXStar_sq (d : OddCentralChordData) :
    d.lowerCentralXStar ^ 2 = d.lowerCentralXStarSq := by
  exact Real.sq_sqrt (lowerCentralXStarSq_pos d).le

theorem lowerCentralC_sq_eq_rhoLambda (d : OddCentralChordData) :
    d.lowerCentralC ^ 2 =
      1 + d.a ^ 2 - 2 * d.a * d.lowerCentralRho := by
  simpa only [lowerCentralC, lowerCentralRho, centralRhoLambda] using
    centralBidiagonalHeight_sq_eq_rhoLambda
      (d.m + 1) (by omega) d.a d.ha0 d.ha1

theorem lowerCentralC_sq_eq_inv_UPlus_sq (d : OddCentralChordData) :
    d.lowerCentralC ^ 2 = 1 / d.lowerCentralUPlus ^ 2 := by
  simpa only [lowerCentralC, lowerCentralRho, lowerCentralUPlus] using
    centralBidiagonalHeight_sq_eq_inv_chebyshev
      (d.m + 1) (by omega) d.a d.ha0 d.ha1

theorem two_mul_a_mul_lowerCentralZeta (d : OddCentralChordData) :
    2 * d.a * d.transformedZeta = 1 + d.a ^ 2 := by
  unfold transformedZeta
  field_simp [d.ha0.ne']
  ring

theorem lowerCentralZeta_eq_one_add_sq_div (d : OddCentralChordData) :
    d.transformedZeta = (1 + d.a ^ 2) / (2 * d.a) := by
  unfold transformedZeta
  field_simp [d.ha0.ne']
  ring

/-! ## The two rational identities used to locate the folded arguments -/

theorem lowerCentralD_eq_zeta_ratio (d : OddCentralChordData) :
    d.lowerCentralD =
      (d.transformedZeta + d.lowerCentralOmega) /
        (d.transformedZeta - d.lowerCentralRho) := by
  have hz :
      d.transformedZeta - d.lowerCentralRho =
        1 / (2 * d.lowerCentralUMinus * d.lowerCentralUPlus) := by
    simpa only [transformedZeta, lowerCentralRho,
      lowerCentralUMinus, lowerCentralUPlus,
      show (((d.m + 1 : Nat) : Int) - 1) = (d.m : Int) by omega] using
        centralZeta_sub_rho_eq
          (d.m + 1) (by omega) d.a d.ha0 d.ha1
  have huMinus := lowerCentralUMinus_pos d
  have huPlus := lowerCentralUPlus_pos d
  have hprod :
      2 * d.lowerCentralUMinus * d.lowerCentralUPlus *
          (d.transformedZeta - d.lowerCentralRho) = 1 := by
    rw [hz]
    field_simp [huMinus.ne', huPlus.ne']
  apply (eq_div_iff (lowerCentralZeta_sub_Rho_pos d).ne').2
  unfold lowerCentralD
  linear_combination
    (d.lowerCentralRho + d.lowerCentralOmega) * hprod

theorem lowerCentralD_eq_two_a_zeta_UPlus_sq
    (d : OddCentralChordData) :
    d.lowerCentralD =
      2 * d.a * (d.transformedZeta + d.lowerCentralOmega) *
        d.lowerCentralUPlus ^ 2 := by
  have hz :
      d.transformedZeta - d.lowerCentralRho =
        1 / (2 * d.lowerCentralUMinus * d.lowerCentralUPlus) := by
    simpa only [transformedZeta, lowerCentralRho,
      lowerCentralUMinus, lowerCentralUPlus,
      show (((d.m + 1 : Nat) : Int) - 1) = (d.m : Int) by omega] using
        centralZeta_sub_rho_eq
          (d.m + 1) (by omega) d.a d.ha0 d.ha1
  have hcentral := (lowerCentralRho_spec d).2
  have huPlus := lowerCentralUPlus_pos d
  have hzr :
      d.transformedZeta - d.lowerCentralRho =
        1 / (2 * d.a * d.lowerCentralUPlus ^ 2) := by
    calc
      d.transformedZeta - d.lowerCentralRho =
          1 / (2 * d.lowerCentralUMinus * d.lowerCentralUPlus) := hz
      _ = 1 / (2 * d.a * d.lowerCentralUPlus ^ 2) := by
        rw [← hcentral]
        congr 1
        ring
  rw [lowerCentralD_eq_zeta_ratio, hzr]
  field_simp [d.ha0.ne', huPlus.ne']

theorem lowerCentralXi_eq_zeta_fraction (d : OddCentralChordData) :
    d.lowerCentralXi =
      (d.lowerCentralRho * (d.transformedZeta + 1) +
          d.transformedZeta * (d.lowerCentralOmega - 1)) /
        (d.transformedZeta + d.lowerCentralOmega) := by
  rw [lowerCentralXi, lowerCentralD_eq_zeta_ratio]
  unfold lowerCentralOmegaDelta
  field_simp [(lowerCentralZeta_add_Omega_pos d).ne',
    (lowerCentralZeta_sub_Rho_pos d).ne']
  ring

theorem lowerCentralD_affine_identity (d : OddCentralChordData) :
    d.lowerCentralD *
        (d.lowerCentralRho + d.lowerCentralOmega) *
          (d.transformedZeta - d.lowerCentralXi) =
      (d.transformedZeta + d.lowerCentralOmega) *
        (1 + d.lowerCentralXi) := by
  rw [lowerCentralD_eq_zeta_ratio,
    lowerCentralXi_eq_zeta_fraction]
  field_simp [(lowerCentralZeta_add_Omega_pos d).ne',
    (lowerCentralZeta_sub_Rho_pos d).ne']
  ring

/-! ## `xi,-omega` are the unordered folded arguments -/

theorem lowerCentral_folded_sum
    (d : OddCentralChordData) {s : Real}
    (hs : s ^ 2 = d.lowerCentralC ^ 2) :
    2 * d.a * (d.lowerCentralXi + -d.lowerCentralOmega) =
      foldC0 d.a d.lowerCentralXStar s := by
  rw [foldC0, hs, lowerCentralC_sq_eq_rhoLambda,
    lowerCentralXStar_sq, lowerCentralXi_eq_zeta_fraction]
  unfold lowerCentralXStarSq lowerCentralOmegaDelta
  have hden :
      (1 + d.a ^ 2) / (2 * d.a) + d.lowerCentralOmega ≠ 0 := by
    rw [← lowerCentralZeta_eq_one_add_sq_div]
    exact (lowerCentralZeta_add_Omega_pos d).ne'
  have hdenPoly :
      1 + d.a ^ 2 + 2 * d.a * d.lowerCentralOmega ≠ 0 := by
    have haw : 0 < 2 * d.a * d.lowerCentralOmega :=
      mul_pos (mul_pos (by norm_num) d.ha0) (lowerCentralOmega_pos d)
    nlinarith [sq_nonneg d.a]
  rw [lowerCentralZeta_eq_one_add_sq_div]
  field_simp [d.ha0.ne', hden]
  ring

theorem lowerCentral_folded_product
    (d : OddCentralChordData) {s : Real}
    (hs : s ^ 2 = d.lowerCentralC ^ 2) :
    d.a ^ 2 *
        (4 * d.lowerCentralXi * (-d.lowerCentralOmega) + 2) =
      foldB d.a d.lowerCentralXStar s := by
  rw [foldB, hs, lowerCentralC_sq_eq_rhoLambda,
    lowerCentralXStar_sq, lowerCentralXi_eq_zeta_fraction]
  unfold lowerCentralXStarSq lowerCentralOmegaDelta
  have hden :
      (1 + d.a ^ 2) / (2 * d.a) + d.lowerCentralOmega ≠ 0 := by
    rw [← lowerCentralZeta_eq_one_add_sq_div]
    exact (lowerCentralZeta_add_Omega_pos d).ne'
  have hdenPoly :
      1 + d.a ^ 2 + d.a * 2 * d.lowerCentralOmega ≠ 0 := by
    have haw : 0 < d.a * 2 * d.lowerCentralOmega :=
      mul_pos (mul_pos d.ha0 (by norm_num)) (lowerCentralOmega_pos d)
    nlinarith [sq_nonneg d.a]
  rw [lowerCentralZeta_eq_one_add_sq_div]
  field_simp [d.ha0.ne', hden]
  field_simp [hdenPoly]
  ring

theorem lowerCentral_folded_sum_at_C (d : OddCentralChordData) :
    2 * d.a * (d.lowerCentralXi + -d.lowerCentralOmega) =
      foldC0 d.a d.lowerCentralXStar d.lowerCentralC := by
  exact lowerCentral_folded_sum d rfl

theorem lowerCentral_folded_product_at_C (d : OddCentralChordData) :
    d.a ^ 2 *
        (4 * d.lowerCentralXi * (-d.lowerCentralOmega) + 2) =
      foldB d.a d.lowerCentralXStar d.lowerCentralC := by
  exact lowerCentral_folded_product d rfl

theorem lowerCentral_folded_sum_at_neg_C (d : OddCentralChordData) :
    2 * d.a * (d.lowerCentralXi + -d.lowerCentralOmega) =
      foldC0 d.a d.lowerCentralXStar (-d.lowerCentralC) := by
  apply lowerCentral_folded_sum d
  ring

theorem lowerCentral_folded_product_at_neg_C (d : OddCentralChordData) :
    d.a ^ 2 *
        (4 * d.lowerCentralXi * (-d.lowerCentralOmega) + 2) =
      foldB d.a d.lowerCentralXStar (-d.lowerCentralC) := by
  apply lowerCentral_folded_product d
  ring

theorem lowerCentralXi_ne_neg_Omega (d : OddCentralChordData) :
    d.lowerCentralXi ≠ -d.lowerCentralOmega := by
  have hxi := lowerCentralXi_pos d
  have hw := lowerCentralOmega_pos d
  linarith

theorem lowerCentralFoldFactor_pos (d : OddCentralChordData) :
    0 < d.lowerCentralFoldFactor := by
  unfold lowerCentralFoldFactor
  exact div_pos (pow_pos d.ha0 d.m)
    (add_pos (lowerCentralXi_pos d) (lowerCentralOmega_pos d))

/-! ## The four positive `X/Y` quantities and their common ratio -/

theorem lowerCentralXXi_pos (d : OddCentralChordData) :
    0 < d.lowerCentralXXi := by
  exact mul_pos (lowerCentralXStar_pos d)
    (lowerCentralZeta_sub_Xi_pos d)

theorem lowerCentralYXi_pos (d : OddCentralChordData) :
    0 < d.lowerCentralYXi := by
  exact mul_pos (lowerCentralC_pos d) (by
    linarith [lowerCentralXi_pos d])

theorem lowerCentralXOmega_pos (d : OddCentralChordData) :
    0 < d.lowerCentralXOmega := by
  exact mul_pos (lowerCentralXStar_pos d)
    (lowerCentralZeta_add_Omega_pos d)

theorem lowerCentralYOmega_pos (d : OddCentralChordData) :
    0 < d.lowerCentralYOmega := by
  exact mul_pos (lowerCentralC_pos d)
    (lowerCentralOmegaDelta_pos d)

theorem lowerCentralYOmega_mul_YXi_eq_XOmega_mul_XXi
    (d : OddCentralChordData) :
    d.lowerCentralYOmega * d.lowerCentralYXi =
      d.lowerCentralXOmega * d.lowerCentralXXi := by
  have hc := lowerCentralC_sq_eq_inv_UPlus_sq d
  have hx := lowerCentralXStar_sq d
  have hD := lowerCentralD_eq_two_a_zeta_UPlus_sq d
  have haffine := lowerCentralD_affine_identity d
  have hu := lowerCentralUPlus_pos d
  have hz := lowerCentralZeta_add_Omega_pos d
  rw [hD] at haffine
  have hfactored :
      (d.transformedZeta + d.lowerCentralOmega) *
          (2 * d.a * d.lowerCentralUPlus ^ 2 *
            (d.lowerCentralRho + d.lowerCentralOmega) *
              (d.transformedZeta - d.lowerCentralXi)) =
        (d.transformedZeta + d.lowerCentralOmega) *
          (1 + d.lowerCentralXi) := by
    convert haffine using 1
    ring
  have hcore :
      2 * d.a * d.lowerCentralUPlus ^ 2 *
          (d.lowerCentralRho + d.lowerCentralOmega) *
            (d.transformedZeta - d.lowerCentralXi) =
        1 + d.lowerCentralXi := by
    exact mul_left_cancel₀ hz.ne' hfactored
  unfold lowerCentralYOmega lowerCentralYXi lowerCentralXOmega
    lowerCentralXXi
  calc
    d.lowerCentralC * d.lowerCentralOmegaDelta *
          (d.lowerCentralC * (1 + d.lowerCentralXi)) =
        d.lowerCentralC ^ 2 * d.lowerCentralOmegaDelta *
          (1 + d.lowerCentralXi) := by ring
    _ = (1 / d.lowerCentralUPlus ^ 2) *
          d.lowerCentralOmegaDelta * (1 + d.lowerCentralXi) := by
      rw [hc]
    _ = 2 * d.a * d.lowerCentralOmegaDelta *
          (d.lowerCentralRho + d.lowerCentralOmega) *
            (d.transformedZeta - d.lowerCentralXi) := by
      rw [← hcore]
      field_simp [hu.ne']
    _ = d.lowerCentralXStar ^ 2 *
          (d.transformedZeta + d.lowerCentralOmega) *
            (d.transformedZeta - d.lowerCentralXi) := by
      rw [hx]
      unfold lowerCentralXStarSq
      field_simp [hz.ne']
    _ = d.lowerCentralXStar *
          (d.transformedZeta + d.lowerCentralOmega) *
          (d.lowerCentralXStar *
            (d.transformedZeta - d.lowerCentralXi)) := by ring

theorem lowerCentralRStar_eq_XXi_div_YXi
    (d : OddCentralChordData) :
    d.lowerCentralRStar = d.lowerCentralXXi / d.lowerCentralYXi := by
  unfold lowerCentralRStar
  apply (div_eq_div_iff
    (lowerCentralXOmega_pos d).ne'
    (lowerCentralYXi_pos d).ne').2
  simpa only [mul_comm] using
    lowerCentralYOmega_mul_YXi_eq_XOmega_mul_XXi d

theorem lowerCentralRStar_mul_XOmega (d : OddCentralChordData) :
    d.lowerCentralRStar * d.lowerCentralXOmega =
      d.lowerCentralYOmega := by
  unfold lowerCentralRStar
  field_simp [(lowerCentralXOmega_pos d).ne']

theorem lowerCentralRStar_mul_YXi (d : OddCentralChordData) :
    d.lowerCentralRStar * d.lowerCentralYXi =
      d.lowerCentralXXi := by
  rw [lowerCentralRStar_eq_XXi_div_YXi]
  field_simp [(lowerCentralYXi_pos d).ne']

theorem one_half_lt_lowerCentralOmega (d : OddCentralChordData) :
    (1 : Real) / 2 < d.lowerCentralOmega := by
  have hangleNonneg :
      0 ≤ Real.pi / (2 * d.lowerCentralLength) := by
    exact div_nonneg Real.pi_pos.le
      (mul_nonneg (by norm_num) (lowerCentralLength_pos d).le)
  have hthirdLePi : Real.pi / 3 ≤ Real.pi := by
    nlinarith [Real.pi_pos]
  have hangleLtThird :
      Real.pi / (2 * d.lowerCentralLength) < Real.pi / 3 := by
    rw [div_lt_div_iff_of_pos_left Real.pi_pos
      (mul_pos (by norm_num) (lowerCentralLength_pos d))
      (by norm_num : (0 : Real) < 3)]
    nlinarith [lowerCentralLength_ge_two d]
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
    hangleNonneg hthirdLePi hangleLtThird
  rw [Real.cos_pi_div_three] at hcos
  exact hcos

theorem lowerCentralRho_add_Omega_gt_one (d : OddCentralChordData) :
    1 < d.lowerCentralRho + d.lowerCentralOmega := by
  have hrhow : d.lowerCentralOmega < d.lowerCentralRho :=
    (lowerCentralReferenceRho_gt_Omega d).trans
      (lowerCentralReferenceRho_lt_Rho d)
  nlinarith [one_half_lt_lowerCentralOmega d]

theorem lowerCentralXOmega_sq_div_YOmega_sq
    (d : OddCentralChordData) :
    d.lowerCentralXOmega ^ 2 / d.lowerCentralYOmega ^ 2 =
      d.lowerCentralD *
        (d.lowerCentralRho + d.lowerCentralOmega) /
          d.lowerCentralOmegaDelta := by
  have hx := lowerCentralXStar_sq d
  have hc := lowerCentralC_sq_eq_inv_UPlus_sq d
  have hD := lowerCentralD_eq_two_a_zeta_UPlus_sq d
  have hz := lowerCentralZeta_add_Omega_pos d
  have hd := lowerCentralOmegaDelta_pos d
  have hu := lowerCentralUPlus_pos d
  unfold lowerCentralXOmega lowerCentralYOmega
  rw [mul_pow, mul_pow, hx, hc, hD]
  unfold lowerCentralXStarSq
  field_simp [hz.ne', hd.ne', hu.ne']

theorem lowerCentralXOmega_sq_div_YOmega_sq_gt_one
    (d : OddCentralChordData) :
    1 < d.lowerCentralXOmega ^ 2 / d.lowerCentralYOmega ^ 2 := by
  rw [lowerCentralXOmega_sq_div_YOmega_sq]
  have hdeltaLtOne : d.lowerCentralOmegaDelta < 1 := by
    unfold lowerCentralOmegaDelta
    linarith [lowerCentralOmega_pos d]
  have hnum :
      d.lowerCentralOmegaDelta <
        d.lowerCentralD *
          (d.lowerCentralRho + d.lowerCentralOmega) := by
    have hD := lowerCentralD_gt_one d
    have hrw := lowerCentralRho_add_Omega_gt_one d
    exact hdeltaLtOne.trans
      (one_lt_mul_of_lt_of_le hD hrw.le)
  exact (lt_div_iff₀ (lowerCentralOmegaDelta_pos d)).2
    (by simpa only [one_mul] using hnum)

theorem lowerCentralYOmega_lt_XOmega (d : OddCentralChordData) :
    d.lowerCentralYOmega < d.lowerCentralXOmega := by
  have hsquares := lowerCentralXOmega_sq_div_YOmega_sq_gt_one d
  have hy := lowerCentralYOmega_pos d
  have hx := lowerCentralXOmega_pos d
  rw [one_lt_div (sq_pos_of_pos hy)] at hsquares
  exact (sq_lt_sq₀ hy.le hx.le).1 hsquares

theorem lowerCentralRStar_mem_Ioo (d : OddCentralChordData) :
    d.lowerCentralRStar ∈ Set.Ioo 0 1 := by
  unfold lowerCentralRStar
  exact ⟨div_pos (lowerCentralYOmega_pos d)
      (lowerCentralXOmega_pos d),
    (div_lt_one (lowerCentralXOmega_pos d)).2
      (lowerCentralYOmega_lt_XOmega d)⟩

/-! ## The Chebyshev value at the folded nodal argument -/

theorem lowerCentralU_neg_Omega_sq (d : OddCentralChordData) :
    chebyshevU d.m (-d.lowerCentralOmega) ^ 2 =
      1 / (1 - d.lowerCentralOmega ^ 2) := by
  let theta : Real := Real.pi / (2 * d.lowerCentralLength)
  have hthetaPos : 0 < theta := by
    exact div_pos Real.pi_pos
      (mul_pos (by norm_num) (lowerCentralLength_pos d))
  have hthetaLtPi : theta < Real.pi := by
    dsimp only [theta]
    have hangleLt :
        Real.pi / (2 * d.lowerCentralLength) < Real.pi / 2 := by
      rw [div_lt_div_iff_of_pos_left Real.pi_pos
        (mul_pos (by norm_num) (lowerCentralLength_pos d))
        (by norm_num : (0 : Real) < 2)]
      nlinarith [lowerCentralLength_ge_two d]
    linarith [Real.pi_pos]
  have hsinPos : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi hthetaPos hthetaLtPi
  have htrig := chebyshevU_cos_mul_sin (d.m : Int) theta
  have hangle :
      (((d.m : Int) + 1 : Int) : Real) * theta = Real.pi / 2 := by
    have hLne : d.lowerCentralLength ≠ 0 :=
      (lowerCentralLength_pos d).ne'
    dsimp only [theta, lowerCentralLength]
    push_cast
    field_simp [hLne]
  push_cast at hangle
  push_cast at htrig
  have homega : d.lowerCentralOmega = Real.cos theta := by
    rfl
  rw [hangle, Real.sin_pi_div_two] at htrig
  have htrigSq := congrArg (fun q : Real => q ^ 2) htrig
  have hsinSq := Real.sin_sq_add_cos_sq theta
  have hsinEq : Real.sin theta ^ 2 = 1 - Real.cos theta ^ 2 := by
    nlinarith
  have hden : 1 - Real.cos theta ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hsinPos]
  have hpositiveSq :
      chebyshevU d.m d.lowerCentralOmega ^ 2 =
        1 / (1 - d.lowerCentralOmega ^ 2) := by
    rw [homega]
    apply (eq_div_iff hden).2
    rw [← hsinEq]
    nlinarith [htrigSq]
  have hneg := Polynomial.Chebyshev.U_eval_neg
    (R := Real) d.m d.lowerCentralOmega
  have hcast :
      chebyshevU d.m (-d.lowerCentralOmega) =
        (-1 : Real) ^ d.m * chebyshevU d.m d.lowerCentralOmega := by
    unfold chebyshevU
    simpa only [Int.cast_natCast, Int.cast_negOnePow_natCast] using hneg
  have hnegSq :
      chebyshevU d.m (-d.lowerCentralOmega) ^ 2 =
        chebyshevU d.m d.lowerCentralOmega ^ 2 := by
    rw [hcast, mul_pow, negOnePow_sq]
    simp
  rw [hnegSq, hpositiveSq]

/-! ## Strict product comparison from `eq:central-target` -/

theorem lowerCentralXOmega_U_sq_identity
    (d : OddCentralChordData) :
    (d.lowerCentralXOmega *
        chebyshevU d.m (-d.lowerCentralOmega)) ^ 2 =
      d.lowerCentralC ^ 2 * d.lowerCentralD *
        (d.lowerCentralRho + d.lowerCentralOmega) /
          (1 + d.lowerCentralOmega) := by
  have hu := lowerCentralU_neg_Omega_sq d
  have hx := lowerCentralXStar_sq d
  have hc := lowerCentralC_sq_eq_inv_UPlus_sq d
  have hD := lowerCentralD_eq_two_a_zeta_UPlus_sq d
  have hz := lowerCentralZeta_add_Omega_pos d
  have hdelta := lowerCentralOmegaDelta_pos d
  have honew : 0 < 1 + d.lowerCentralOmega := by
    linarith [lowerCentralOmega_pos d]
  have honeSubSq : 0 < 1 - d.lowerCentralOmega ^ 2 := by
    have hprod := mul_pos
      (sub_pos.mpr (lowerCentralOmega_lt_one d)) honew
    nlinarith
  have huPlus := lowerCentralUPlus_pos d
  unfold lowerCentralXOmega
  simp only [mul_pow]
  rw [hx, hu, hc, hD]
  unfold lowerCentralXStarSq lowerCentralOmegaDelta
  field_simp [hz.ne', hdelta.ne', honew.ne', honeSubSq.ne', huPlus.ne']
  ring

theorem lowerCentralYXi_U_sq_lt_XOmega_U_sq
    (d : OddCentralChordData) :
    (d.lowerCentralYXi * chebyshevU d.m d.lowerCentralXi) ^ 2 <
      (d.lowerCentralXOmega *
        chebyshevU d.m (-d.lowerCentralOmega)) ^ 2 := by
  have hscalar := lowerCentral_scalar_target d
  have hcPos := lowerCentralC_pos d
  have hwOne : 0 < 1 + d.lowerCentralOmega := by
    linarith [lowerCentralOmega_pos d]
  rw [lowerCentralXOmega_U_sq_identity]
  unfold lowerCentralYXi
  rw [mul_pow]
  have hscaled := mul_lt_mul_of_pos_left hscalar
    (sq_pos_of_pos hcPos)
  apply (lt_div_iff₀ hwOne).2
  convert hscaled using 1 <;> ring

/-! ## The two source numerator factorizations -/

theorem foldOddBeta_lowerCentral
    (d : OddCentralChordData) (s : Real) :
    foldOddBeta d.a d.lowerCentralXStar s =
      d.lowerCentralXStar * d.transformedZeta + s := by
  unfold foldOddBeta transformedZeta
  field_simp [d.ha0.ne']
  ring

theorem foldOddChebyshevFunction_eq_lowerCentralNumerator
    (d : OddCentralChordData) (s t : Real) :
    foldOddChebyshevFunction d.m d.lowerCentralXStar s
        (foldOddBeta d.a d.lowerCentralXStar s) t =
      d.lowerCentralNumerator d.lowerCentralXStar s t := by
  rw [foldOddBeta_lowerCentral]
  unfold foldOddChebyshevFunction lowerCentralNumerator
  ring

theorem lowerCentralNumerator_C_difference
    (d : OddCentralChordData) :
    d.lowerCentralNumerator d.lowerCentralXStar d.lowerCentralC
          d.lowerCentralXi -
        d.lowerCentralNumerator d.lowerCentralXStar d.lowerCentralC
          (-d.lowerCentralOmega) =
      (1 + d.lowerCentralRStar) *
        (d.lowerCentralXOmega *
            chebyshevU d.m (-d.lowerCentralOmega) -
          d.lowerCentralYXi * chebyshevU d.m d.lowerCentralXi) := by
  have hrX := lowerCentralRStar_mul_XOmega d
  have hrY := lowerCentralRStar_mul_YXi d
  have hleft :
      d.lowerCentralNumerator d.lowerCentralXStar d.lowerCentralC
            d.lowerCentralXi -
          d.lowerCentralNumerator d.lowerCentralXStar d.lowerCentralC
            (-d.lowerCentralOmega) =
        -(d.lowerCentralXXi + d.lowerCentralYXi) *
            chebyshevU d.m d.lowerCentralXi -
          (-(d.lowerCentralXOmega + d.lowerCentralYOmega) *
            chebyshevU d.m (-d.lowerCentralOmega)) := by
    unfold lowerCentralNumerator lowerCentralXXi lowerCentralYXi
      lowerCentralXOmega lowerCentralYOmega lowerCentralOmegaDelta
    ring
  rw [hleft]
  rw [← hrX, ← hrY]
  ring

theorem lowerCentralNumerator_neg_C_difference
    (d : OddCentralChordData) :
    d.lowerCentralNumerator d.lowerCentralXStar (-d.lowerCentralC)
          d.lowerCentralXi -
        d.lowerCentralNumerator d.lowerCentralXStar (-d.lowerCentralC)
          (-d.lowerCentralOmega) =
      (1 - d.lowerCentralRStar) *
        (d.lowerCentralXOmega *
            chebyshevU d.m (-d.lowerCentralOmega) +
          d.lowerCentralYXi * chebyshevU d.m d.lowerCentralXi) := by
  have hrX := lowerCentralRStar_mul_XOmega d
  have hrY := lowerCentralRStar_mul_YXi d
  have hleft :
      d.lowerCentralNumerator d.lowerCentralXStar (-d.lowerCentralC)
            d.lowerCentralXi -
          d.lowerCentralNumerator d.lowerCentralXStar (-d.lowerCentralC)
            (-d.lowerCentralOmega) =
        -(d.lowerCentralXXi - d.lowerCentralYXi) *
            chebyshevU d.m d.lowerCentralXi -
          (-(d.lowerCentralXOmega - d.lowerCentralYOmega) *
            chebyshevU d.m (-d.lowerCentralOmega)) := by
    unfold lowerCentralNumerator lowerCentralXXi lowerCentralYXi
      lowerCentralXOmega lowerCentralYOmega lowerCentralOmegaDelta
    ring
  rw [hleft]
  rw [← hrX, ← hrY]
  ring

theorem lowerCentralNumerator_difference_product_pos
    (d : OddCentralChordData) :
    0 <
      (d.lowerCentralNumerator d.lowerCentralXStar d.lowerCentralC
            d.lowerCentralXi -
        d.lowerCentralNumerator d.lowerCentralXStar d.lowerCentralC
            (-d.lowerCentralOmega)) *
      (d.lowerCentralNumerator d.lowerCentralXStar (-d.lowerCentralC)
            d.lowerCentralXi -
        d.lowerCentralNumerator d.lowerCentralXStar (-d.lowerCentralC)
            (-d.lowerCentralOmega)) := by
  rw [lowerCentralNumerator_C_difference,
    lowerCentralNumerator_neg_C_difference]
  let A := d.lowerCentralXOmega *
    chebyshevU d.m (-d.lowerCentralOmega)
  let B := d.lowerCentralYXi * chebyshevU d.m d.lowerCentralXi
  have hr := lowerCentralRStar_mem_Ioo d
  have hsquares := lowerCentralYXi_U_sq_lt_XOmega_U_sq d
  have hratio : 0 < (1 + d.lowerCentralRStar) *
      (1 - d.lowerCentralRStar) :=
    mul_pos (by linarith [hr.1]) (by linarith [hr.2])
  have hdiff : 0 < (A - B) * (A + B) := by
    dsimp only [A, B]
    nlinarith
  dsimp only [A, B] at hdiff ⊢
  have hfactor := mul_pos hratio hdiff
  convert hfactor using 1
  ring

/-! ## Generic divided difference and the literal signed-pencil product -/

theorem foldOddSequence_lowerCentral
    (d : OddCentralChordData) (s : Real)
    (hs : s ^ 2 = d.lowerCentralC ^ 2) :
    foldOddSequence d.a d.lowerCentralXStar s d.m =
      d.a ^ d.m *
        ((d.lowerCentralNumerator d.lowerCentralXStar s
              d.lowerCentralXi -
            d.lowerCentralNumerator d.lowerCentralXStar s
              (-d.lowerCentralOmega)) /
          (d.lowerCentralXi + d.lowerCentralOmega)) := by
  have h := foldOddSequence_eq_chebyshevDividedDifference
    (a := d.a) (x := d.lowerCentralXStar) (s := s)
    (u := d.lowerCentralXi) (v := -d.lowerCentralOmega)
    d.ha0.ne' d.ha1.ne
    (lowerCentralXi_ne_neg_Omega d)
    (lowerCentral_folded_sum d hs)
    (lowerCentral_folded_product d hs) d.m
  rw [foldOddChebyshevFunction_eq_lowerCentralNumerator,
    foldOddChebyshevFunction_eq_lowerCentralNumerator] at h
  simpa only [sub_neg_eq_add] using h

theorem signedPencilDet_lowerCentral
    (d : OddCentralChordData) (s : Real)
    (hs : s ^ 2 = d.lowerCentralC ^ 2) :
    signedPencilDet (2 * d.m + 1) d.a d.lowerCentralXStar s =
      d.a ^ d.m *
        ((d.lowerCentralNumerator d.lowerCentralXStar s
              d.lowerCentralXi -
            d.lowerCentralNumerator d.lowerCentralXStar s
              (-d.lowerCentralOmega)) /
          (d.lowerCentralXi + d.lowerCentralOmega)) := by
  rw [signedPencilDet_odd_eq_foldOddSequence d.ha1.ne]
  exact foldOddSequence_lowerCentral d s hs

theorem signedPencilDet_lowerCentral_factorized
    (d : OddCentralChordData) (s : Real)
    (hs : s ^ 2 = d.lowerCentralC ^ 2) :
    signedPencilDet (2 * d.m + 1) d.a d.lowerCentralXStar s =
      d.lowerCentralFoldFactor *
        (d.lowerCentralNumerator d.lowerCentralXStar s
            d.lowerCentralXi -
          d.lowerCentralNumerator d.lowerCentralXStar s
            (-d.lowerCentralOmega)) := by
  rw [signedPencilDet_lowerCentral d s hs]
  unfold lowerCentralFoldFactor
  ring

theorem signedPencilDet_lowerCentral_C (d : OddCentralChordData) :
    signedPencilDet (2 * d.m + 1) d.a d.lowerCentralXStar
        d.lowerCentralC =
      d.a ^ d.m *
        ((d.lowerCentralNumerator d.lowerCentralXStar d.lowerCentralC
              d.lowerCentralXi -
            d.lowerCentralNumerator d.lowerCentralXStar d.lowerCentralC
              (-d.lowerCentralOmega)) /
          (d.lowerCentralXi + d.lowerCentralOmega)) := by
  exact signedPencilDet_lowerCentral d d.lowerCentralC rfl

theorem signedPencilDet_lowerCentral_neg_C (d : OddCentralChordData) :
    signedPencilDet (2 * d.m + 1) d.a d.lowerCentralXStar
        (-d.lowerCentralC) =
      d.a ^ d.m *
        ((d.lowerCentralNumerator d.lowerCentralXStar (-d.lowerCentralC)
              d.lowerCentralXi -
            d.lowerCentralNumerator d.lowerCentralXStar (-d.lowerCentralC)
              (-d.lowerCentralOmega)) /
          (d.lowerCentralXi + d.lowerCentralOmega)) := by
  apply signedPencilDet_lowerCentral d (-d.lowerCentralC)
  ring

/-- Literal `eq:q-product-central`. -/
theorem signedPencilDet_lowerCentral_product_pos
    (d : OddCentralChordData) :
    0 <
      signedPencilDet (2 * d.m + 1) d.a d.lowerCentralXStar
          d.lowerCentralC *
        signedPencilDet (2 * d.m + 1) d.a d.lowerCentralXStar
          (-d.lowerCentralC) := by
  rw [signedPencilDet_lowerCentral_C,
    signedPencilDet_lowerCentral_neg_C]
  have hnum := lowerCentralNumerator_difference_product_pos d
  have haPow : 0 < d.a ^ d.m := pow_pos d.ha0 d.m
  have hden : 0 < d.lowerCentralXi + d.lowerCentralOmega :=
    add_pos (lowerCentralXi_pos d) (lowerCentralOmega_pos d)
  have hdiv :
      0 <
        ((d.lowerCentralNumerator d.lowerCentralXStar d.lowerCentralC
              d.lowerCentralXi -
            d.lowerCentralNumerator d.lowerCentralXStar d.lowerCentralC
              (-d.lowerCentralOmega)) /
          (d.lowerCentralXi + d.lowerCentralOmega)) *
        ((d.lowerCentralNumerator d.lowerCentralXStar (-d.lowerCentralC)
              d.lowerCentralXi -
            d.lowerCentralNumerator d.lowerCentralXStar (-d.lowerCentralC)
              (-d.lowerCentralOmega)) /
          (d.lowerCentralXi + d.lowerCentralOmega)) := by
    rw [div_mul_div_comm]
    exact div_pos hnum (mul_pos hden hden)
  have hprod := mul_pos (mul_pos haPow haPow) hdiv
  convert hprod using 1
  ring

end OddCentralChordData

end

end ConnectedPseudospectrum
