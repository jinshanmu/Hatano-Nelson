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

/-! ## Cancellation of the mixed terms in the determinant product -/

theorem lowerCentral_cross_identity (d : OddCentralChordData) :
    d.lowerCentralXStar ^ 2 *
        (d.transformedZeta - d.lowerCentralXi) *
        (d.transformedZeta + d.lowerCentralOmega) =
      d.lowerCentralC ^ 2 * (1 + d.lowerCentralXi) *
        d.lowerCentralOmegaDelta := by
  have haffine := lowerCentralD_affine_identity d
  rw [lowerCentralD_eq_two_a_zeta_UPlus_sq] at haffine
  have hz := lowerCentralZeta_add_Omega_pos d
  have hu := lowerCentralUPlus_pos d
  have hcore :
      2 * d.a * d.lowerCentralUPlus ^ 2 *
          (d.lowerCentralRho + d.lowerCentralOmega) *
            (d.transformedZeta - d.lowerCentralXi) =
        1 + d.lowerCentralXi := by
    apply mul_left_cancel₀ hz.ne'
    convert haffine using 1
    ring
  rw [lowerCentralXStar_sq, lowerCentralC_sq_eq_inv_UPlus_sq]
  unfold lowerCentralXStarSq
  field_simp [hz.ne', hu.ne']
  linear_combination d.lowerCentralOmegaDelta * hcore

theorem lowerCentral_XOmega_sq (d : OddCentralChordData) :
    d.lowerCentralXStar ^ 2 *
        (d.transformedZeta + d.lowerCentralOmega) ^ 2 =
      d.lowerCentralC ^ 2 * d.lowerCentralOmegaDelta *
        (d.lowerCentralD * (d.lowerCentralRho + d.lowerCentralOmega)) := by
  rw [lowerCentralXStar_sq, lowerCentralC_sq_eq_inv_UPlus_sq,
    lowerCentralD_eq_two_a_zeta_UPlus_sq]
  unfold lowerCentralXStarSq
  field_simp [(lowerCentralZeta_add_Omega_pos d).ne',
    (lowerCentralUPlus_pos d).ne']

theorem lowerCentral_XXi_sq (d : OddCentralChordData) :
    d.lowerCentralXStar ^ 2 *
        (d.transformedZeta - d.lowerCentralXi) ^ 2 =
      d.lowerCentralC ^ 2 * (1 + d.lowerCentralXi) ^ 2 *
        d.lowerCentralOmegaDelta /
        (d.lowerCentralD * (d.lowerCentralRho + d.lowerCentralOmega)) := by
  have hT : 0 < d.lowerCentralD *
      (d.lowerCentralRho + d.lowerCentralOmega) :=
    mul_pos (lowerCentralD_pos d)
      (add_pos (lowerCentralRho_pos d) (lowerCentralOmega_pos d))
  apply (eq_div_iff hT.ne').2
  have hcross := lowerCentral_cross_identity d
  have haffine := lowerCentralD_affine_identity d
  linear_combination
    d.lowerCentralXStar ^ 2 *
      (d.transformedZeta - d.lowerCentralXi) * haffine +
      (1 + d.lowerCentralXi) * hcross

theorem one_half_lt_lowerCentralOmega (d : OddCentralChordData) :
    (1 : Real) / 2 < d.lowerCentralOmega := by
  have hdelta := lowerCentralOmegaDelta_lt_five_sixteenths d
  unfold lowerCentralOmegaDelta at hdelta
  linarith

theorem lowerCentralRho_add_Omega_gt_one (d : OddCentralChordData) :
    1 < d.lowerCentralRho + d.lowerCentralOmega := by
  have hrhow : d.lowerCentralOmega < d.lowerCentralRho :=
    (lowerCentralReferenceRho_gt_Omega d).trans
      (lowerCentralReferenceRho_lt_Rho d)
  nlinarith [one_half_lt_lowerCentralOmega d]

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

/-! ## The folded numerator and its product -/

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

theorem lowerCentralNumerator_difference_product
    (d : OddCentralChordData) :
    (d.lowerCentralNumerator d.lowerCentralXStar d.lowerCentralC
          d.lowerCentralXi -
      d.lowerCentralNumerator d.lowerCentralXStar d.lowerCentralC
          (-d.lowerCentralOmega)) *
    (d.lowerCentralNumerator d.lowerCentralXStar (-d.lowerCentralC)
          d.lowerCentralXi -
      d.lowerCentralNumerator d.lowerCentralXStar (-d.lowerCentralC)
          (-d.lowerCentralOmega)) =
      d.lowerCentralC ^ 2 *
        (1 - d.lowerCentralOmegaDelta /
          (d.lowerCentralD * (d.lowerCentralRho + d.lowerCentralOmega))) *
        (d.lowerCentralD * (d.lowerCentralRho + d.lowerCentralOmega) /
          (1 + d.lowerCentralOmega) -
          (1 + d.lowerCentralXi) ^ 2 * chebyshevU d.m d.lowerCentralXi ^ 2) := by
  have hcross := lowerCentral_cross_identity d
  have hproduct :
      (d.lowerCentralNumerator d.lowerCentralXStar d.lowerCentralC
            d.lowerCentralXi -
        d.lowerCentralNumerator d.lowerCentralXStar d.lowerCentralC
            (-d.lowerCentralOmega)) *
      (d.lowerCentralNumerator d.lowerCentralXStar (-d.lowerCentralC)
            d.lowerCentralXi -
        d.lowerCentralNumerator d.lowerCentralXStar (-d.lowerCentralC)
            (-d.lowerCentralOmega)) =
      (d.lowerCentralXStar ^ 2 *
          (d.transformedZeta + d.lowerCentralOmega) ^ 2 -
        d.lowerCentralC ^ 2 * d.lowerCentralOmegaDelta ^ 2) *
          chebyshevU d.m (-d.lowerCentralOmega) ^ 2 -
      (d.lowerCentralC ^ 2 * (1 + d.lowerCentralXi) ^ 2 -
        d.lowerCentralXStar ^ 2 *
          (d.transformedZeta - d.lowerCentralXi) ^ 2) *
          chebyshevU d.m d.lowerCentralXi ^ 2 := by
    unfold lowerCentralNumerator lowerCentralOmegaDelta at *
    linear_combination -2 * chebyshevU d.m (-d.lowerCentralOmega) *
      chebyshevU d.m d.lowerCentralXi * hcross
  rw [hproduct, lowerCentral_XOmega_sq, lowerCentral_XXi_sq,
    lowerCentralU_neg_Omega_sq]
  have hT : 0 < d.lowerCentralD *
      (d.lowerCentralRho + d.lowerCentralOmega) :=
    mul_pos (lowerCentralD_pos d)
      (add_pos (lowerCentralRho_pos d) (lowerCentralOmega_pos d))
  generalize hTdef :
    d.lowerCentralD * (d.lowerCentralRho + d.lowerCentralOmega) = T at hT ⊢
  have hone : 0 < 1 + d.lowerCentralOmega := by
    linarith [lowerCentralOmega_pos d]
  have hden : 0 < 1 - d.lowerCentralOmega ^ 2 := by
    nlinarith [lowerCentralOmega_pos d, lowerCentralOmega_lt_one d]
  unfold lowerCentralOmegaDelta
  field_simp [hT.ne', hone.ne', hden.ne']
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
  rw [lowerCentralNumerator_difference_product]
  have hT : 1 < d.lowerCentralD *
      (d.lowerCentralRho + d.lowerCentralOmega) :=
    one_lt_mul_of_lt_of_le (lowerCentralD_gt_one d)
      (lowerCentralRho_add_Omega_gt_one d).le
  have hdelta : d.lowerCentralOmegaDelta < 1 := by
    unfold lowerCentralOmegaDelta
    linarith [lowerCentralOmega_pos d]
  have hfactor : 0 < 1 - d.lowerCentralOmegaDelta /
      (d.lowerCentralD * (d.lowerCentralRho + d.lowerCentralOmega)) := by
    apply sub_pos.mpr
    apply (div_lt_one (by linarith)).2
    exact hdelta.trans hT
  have htarget : 0 <
      d.lowerCentralD * (d.lowerCentralRho + d.lowerCentralOmega) /
          (1 + d.lowerCentralOmega) -
        (1 + d.lowerCentralXi) ^ 2 * chebyshevU d.m d.lowerCentralXi ^ 2 := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ (by linarith [lowerCentralOmega_pos d])).2
    nlinarith [lowerCentral_scalar_target d]
  exact mul_pos (mul_pos (sq_pos_of_pos (lowerCentralC_pos d)) hfactor) htarget

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
    d.ha0.ne'
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
  rw [signedPencilDet_odd_eq_foldOddSequence]
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
  rw [signedPencilDet_lowerCentral_factorized d d.lowerCentralC rfl,
    signedPencilDet_lowerCentral_factorized d (-d.lowerCentralC) (by ring)]
  have hprod := mul_pos (sq_pos_of_pos (lowerCentralFoldFactor_pos d))
    (lowerCentralNumerator_difference_product_pos d)
  convert hprod using 1
  ring

end OddCentralChordData

end

end ConnectedPseudospectrum
