import ConnectedPseudospectrum.FoldedCollision
import ConnectedPseudospectrum.OuterChordCoordinates
import Mathlib.Tactic

/-!
# Reconstruction from the actual folded variables

This module formalizes the reversible algebra following `eq:channel-xs`.
On the positive-discriminant sheet, the actual folded variables determine
nonnegative half variables.  Their squares reconstruct the original `x` and
`s` coordinates exactly, and their signs recover the corresponding positive
square-root formulas.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- The generic passage from a half variable to its folded argument. -/
def halfFoldArgument (u : ℝ) : ℝ :=
  2 * u ^ 2 - 1

/-- The nonnegative half variable belonging to the smaller folded root. -/
def foldedHalfY (a x s : ℝ) : ℝ :=
  Real.sqrt ((foldXiMinus a x s + 1) / 2)

/-- The nonnegative half variable belonging to the larger folded root. -/
def foldedHalfZ (a x s : ℝ) : ℝ :=
  Real.sqrt ((foldXiPlus a x s + 1) / 2)

theorem foldedHalfY_nonneg (a x s : ℝ) :
    0 ≤ foldedHalfY a x s :=
  Real.sqrt_nonneg _

theorem foldedHalfZ_nonneg (a x s : ℝ) :
    0 ≤ foldedHalfZ a x s :=
  Real.sqrt_nonneg _

/-- The square of the lower half variable is the affine rescaling of
`ξ₋`, on its natural real-half-variable domain. -/
theorem foldedHalfY_sq
    {a x s : ℝ} (hminus : -1 ≤ foldXiMinus a x s) :
    foldedHalfY a x s ^ 2 = (foldXiMinus a x s + 1) / 2 := by
  unfold foldedHalfY
  exact Real.sq_sqrt (by linarith)

/-- The square of the upper half variable is the affine rescaling of
`ξ₊`, on its natural real-half-variable domain. -/
theorem foldedHalfZ_sq
    {a x s : ℝ} (hplus : -1 ≤ foldXiPlus a x s) :
    foldedHalfZ a x s ^ 2 = (foldXiPlus a x s + 1) / 2 := by
  unfold foldedHalfZ
  exact Real.sq_sqrt (by linarith)

/-- Exact relation between the actual smaller folded root and the generic
half-variable fold map. -/
theorem foldXiMinus_eq_halfFoldArgument_foldedHalfY
    {a x s : ℝ} (hminus : -1 ≤ foldXiMinus a x s) :
    foldXiMinus a x s = halfFoldArgument (foldedHalfY a x s) := by
  rw [halfFoldArgument, foldedHalfY_sq hminus]
  ring

/-- Exact relation between the actual larger folded root and the generic
half-variable fold map. -/
theorem foldXiPlus_eq_halfFoldArgument_foldedHalfZ
    {a x s : ℝ} (hplus : -1 ≤ foldXiPlus a x s) :
    foldXiPlus a x s = halfFoldArgument (foldedHalfZ a x s) := by
  rw [halfFoldArgument, foldedHalfZ_sq hplus]
  ring

/-- Nonnegative generic half variables satisfying the two folded-root
relations agree with the square-root reconstruction. -/
theorem foldedHalfVariables_eq_of_generic
    {a x s y z : ℝ} (hy0 : 0 ≤ y) (hz0 : 0 ≤ z)
    (hy : foldXiMinus a x s = halfFoldArgument y)
    (hz : foldXiPlus a x s = halfFoldArgument z) :
    foldedHalfY a x s = y ∧ foldedHalfZ a x s = z := by
  constructor
  · unfold foldedHalfY
    rw [hy]
    unfold halfFoldArgument
    have harg : (2 * y ^ 2 - 1 + 1) / 2 = y ^ 2 := by ring
    rw [harg, Real.sqrt_sq hy0]
  · unfold foldedHalfZ
    rw [hz]
    unfold halfFoldArgument
    have harg : (2 * z ^ 2 - 1 + 1) / 2 = z ^ 2 := by ring
    rw [harg, Real.sqrt_sq hz0]

/-- For positive `a`, a positive folded discriminant orders the two actual
real folded roots strictly. -/
theorem foldXiMinus_lt_foldXiPlus_of_discriminant_pos
    {a x s : ℝ} (ha0 : 0 < a)
    (hdisc : 0 < foldDiscriminant a x s) :
    foldXiMinus a x s < foldXiPlus a x s := by
  have hsqrt : 0 < Real.sqrt (foldDiscriminant a x s) :=
    Real.sqrt_pos.2 hdisc
  have hden : 0 < 4 * a := mul_pos (by norm_num) ha0
  unfold foldXiMinus foldXiPlus
  exact (div_lt_div_iff_of_pos_right hden).2 (by linarith)

/-- The upper reconstructed half variable is strictly positive as soon as
the smaller folded root belongs to the real-half-variable domain. -/
theorem foldedHalfZ_pos_of_discriminant_pos
    {a x s : ℝ} (ha0 : 0 < a)
    (hdisc : 0 < foldDiscriminant a x s)
    (hminus : -1 ≤ foldXiMinus a x s) :
    0 < foldedHalfZ a x s := by
  have hxi := foldXiMinus_lt_foldXiPlus_of_discriminant_pos ha0 hdisc
  unfold foldedHalfZ
  exact Real.sqrt_pos.2 (by linarith)

/-- Positive discriminant gives strict separation of the squared half
variables; this is the collision-free condition used in continuation. -/
theorem foldedHalfY_sq_lt_foldedHalfZ_sq
    {a x s : ℝ} (ha0 : 0 < a)
    (hdisc : 0 < foldDiscriminant a x s)
    (hminus : -1 ≤ foldXiMinus a x s) :
    foldedHalfY a x s ^ 2 < foldedHalfZ a x s ^ 2 := by
  have hxi := foldXiMinus_lt_foldXiPlus_of_discriminant_pos ha0 hdisc
  have hplus : -1 ≤ foldXiPlus a x s := hminus.trans hxi.le
  rw [foldedHalfY_sq hminus, foldedHalfZ_sq hplus]
  linarith

theorem foldedHalfZ_sq_ne_foldedHalfY_sq
    {a x s : ℝ} (ha0 : 0 < a)
    (hdisc : 0 < foldDiscriminant a x s)
    (hminus : -1 ≤ foldXiMinus a x s) :
    foldedHalfZ a x s ^ 2 ≠ foldedHalfY a x s ^ 2 := by
  exact ne_of_gt (foldedHalfY_sq_lt_foldedHalfZ_sq ha0 hdisc hminus)

/-- Joint parameter space `(a,(x,s))` used for branch continuation. -/
abbrev FoldedParameterTriple := ℝ × (ℝ × ℝ)

/-- The actual folded discriminant as a function of all three parameters. -/
def foldedParameterDiscriminant (p : FoldedParameterTriple) : ℝ :=
  foldDiscriminant p.1 p.2.1 p.2.2

/-- The open positive-`a`, positive-discriminant sheet. -/
def foldedPositiveDiscriminantRegion : Set FoldedParameterTriple :=
  {p | 0 < p.1 ∧ 0 < foldedParameterDiscriminant p}

private theorem continuous_foldC0_parameter :
    Continuous (fun p : FoldedParameterTriple ↦
      foldC0 p.1 p.2.1 p.2.2) := by
  unfold foldC0
  fun_prop

theorem continuous_foldedParameterDiscriminant :
    Continuous foldedParameterDiscriminant := by
  unfold foldedParameterDiscriminant foldDiscriminant
  fun_prop

theorem isOpen_foldedPositiveDiscriminantRegion :
    IsOpen foldedPositiveDiscriminantRegion := by
  exact (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_const continuous_foldedParameterDiscriminant)

private theorem continuousAt_foldXiPlus_parameter
    {p : FoldedParameterTriple} (ha0 : p.1 ≠ 0) :
    ContinuousAt
      (fun q : FoldedParameterTriple ↦
        foldXiPlus q.1 q.2.1 q.2.2) p := by
  have hnum : Continuous (fun q : FoldedParameterTriple ↦
      foldC0 q.1 q.2.1 q.2.2 +
        Real.sqrt (foldedParameterDiscriminant q)) :=
    continuous_foldC0_parameter.add
      continuous_foldedParameterDiscriminant.sqrt
  have hden : Continuous (fun q : FoldedParameterTriple ↦ 4 * q.1) := by
    fun_prop
  change ContinuousAt (fun q : FoldedParameterTriple ↦
    (foldC0 q.1 q.2.1 q.2.2 +
      Real.sqrt (foldedParameterDiscriminant q)) / (4 * q.1)) p
  exact hnum.continuousAt.div hden.continuousAt
    (mul_ne_zero (by norm_num) ha0)

private theorem continuousAt_foldXiMinus_parameter
    {p : FoldedParameterTriple} (ha0 : p.1 ≠ 0) :
    ContinuousAt
      (fun q : FoldedParameterTriple ↦
        foldXiMinus q.1 q.2.1 q.2.2) p := by
  have hnum : Continuous (fun q : FoldedParameterTriple ↦
      foldC0 q.1 q.2.1 q.2.2 -
        Real.sqrt (foldedParameterDiscriminant q)) :=
    continuous_foldC0_parameter.sub
      continuous_foldedParameterDiscriminant.sqrt
  have hden : Continuous (fun q : FoldedParameterTriple ↦ 4 * q.1) := by
    fun_prop
  change ContinuousAt (fun q : FoldedParameterTriple ↦
    (foldC0 q.1 q.2.1 q.2.2 -
      Real.sqrt (foldedParameterDiscriminant q)) / (4 * q.1)) p
  exact hnum.continuousAt.div hden.continuousAt
    (mul_ne_zero (by norm_num) ha0)

theorem continuousAt_foldedHalfY_parameter
    {p : FoldedParameterTriple} (ha0 : p.1 ≠ 0) :
    ContinuousAt
      (fun q : FoldedParameterTriple ↦
        foldedHalfY q.1 q.2.1 q.2.2) p := by
  unfold foldedHalfY
  exact (((continuousAt_foldXiMinus_parameter ha0).add
    continuousAt_const).div_const 2).sqrt

theorem continuousAt_foldedHalfZ_parameter
    {p : FoldedParameterTriple} (ha0 : p.1 ≠ 0) :
    ContinuousAt
      (fun q : FoldedParameterTriple ↦
        foldedHalfZ q.1 q.2.1 q.2.2) p := by
  unfold foldedHalfZ
  exact (((continuousAt_foldXiPlus_parameter ha0).add
    continuousAt_const).div_const 2).sqrt

theorem continuousOn_foldedHalfY_positiveDiscriminant :
    ContinuousOn
      (fun p : FoldedParameterTriple ↦
        foldedHalfY p.1 p.2.1 p.2.2)
      foldedPositiveDiscriminantRegion := by
  intro p hp
  exact (continuousAt_foldedHalfY_parameter hp.1.ne').continuousWithinAt

theorem continuousOn_foldedHalfZ_positiveDiscriminant :
    ContinuousOn
      (fun p : FoldedParameterTriple ↦
        foldedHalfZ p.1 p.2.1 p.2.2)
      foldedPositiveDiscriminantRegion := by
  intro p hp
  exact (continuousAt_foldedHalfZ_parameter hp.1.ne').continuousWithinAt

/-- The ordered pair of reconstructed half variables is continuous on the
open positive-discriminant sheet. -/
theorem continuousOn_foldedHalfVariables_positiveDiscriminant :
    ContinuousOn
      (fun p : FoldedParameterTriple ↦
        (foldedHalfY p.1 p.2.1 p.2.2,
          foldedHalfZ p.1 p.2.1 p.2.2))
      foldedPositiveDiscriminantRegion :=
  continuousOn_foldedHalfY_positiveDiscriminant.prodMk
    continuousOn_foldedHalfZ_positiveDiscriminant

/-- The first scale identity needed to invert the folded variables. -/
theorem halfChordScale_sq_mul_cosh_sq
    {a : ℝ} (ha0 : 0 < a) :
    halfChordScale a ^ 2 *
        Real.cosh (pathLogParameter a) ^ 2 = 4 * a := by
  have hc : Real.cosh (pathLogParameter a) ≠ 0 :=
    (Real.cosh_pos _).ne'
  have hr : pathRate a ^ 2 = a := by
    simpa [pow_two] using pathRate_mul_self ha0.le
  unfold halfChordScale
  calc
    (2 * pathRate a / Real.cosh (pathLogParameter a)) ^ 2 *
          Real.cosh (pathLogParameter a) ^ 2 =
        (2 * pathRate a) ^ 2 := by field_simp [hc]
    _ = 4 * pathRate a ^ 2 := by ring
    _ = 4 * a := by rw [hr]

/-- The second scale identity needed to invert the folded variables. -/
theorem four_mul_mul_cosh_sq_pathLogParameter
    {a : ℝ} (ha0 : 0 < a) :
    4 * a * Real.cosh (pathLogParameter a) ^ 2 = (1 + a) ^ 2 := by
  have hr : pathRate a ^ 2 = a := by
    simpa [pow_two] using pathRate_mul_self ha0.le
  have hsum := two_pathRate_mul_cosh_pathLogParameter ha0
  have hsquare := congrArg (fun u : ℝ ↦ u ^ 2) hsum
  calc
    4 * a * Real.cosh (pathLogParameter a) ^ 2 =
        4 * pathRate a ^ 2 * Real.cosh (pathLogParameter a) ^ 2 := by
          rw [hr]
    _ = (2 * pathRate a * Real.cosh (pathLogParameter a)) ^ 2 := by
      ring
    _ = (1 + a) ^ 2 := hsquare

/-- Reconstruction of the original horizontal coordinate from the two
actual folded roots. -/
theorem x_sq_eq_halfChordScale_sq_mul_foldedHalf_sq
    {a x s : ℝ} (ha0 : 0 < a)
    (hdisc : 0 < foldDiscriminant a x s)
    (hminus : -1 ≤ foldXiMinus a x s)
    (hplus : -1 ≤ foldXiPlus a x s) :
    x ^ 2 = halfChordScale a ^ 2 *
      foldedHalfY a x s ^ 2 * foldedHalfZ a x s ^ 2 := by
  have hsum := foldXiPlus_add_foldXiMinus
    (x := x) (s := s) ha0.ne'
  have hprod := foldXiPlus_mul_foldXiMinus
    (x := x) (s := s) ha0.ne' hdisc.le
  have hsym :
      4 * a ^ 2 *
          (foldXiPlus a x s * foldXiMinus a x s +
            (foldXiPlus a x s + foldXiMinus a x s) + 1) =
        (1 + a) ^ 2 * x ^ 2 := by
    calc
      4 * a ^ 2 *
            (foldXiPlus a x s * foldXiMinus a x s +
              (foldXiPlus a x s + foldXiMinus a x s) + 1) =
          a ^ 2 *
              (4 * foldXiPlus a x s * foldXiMinus a x s + 2) +
            2 * a *
              (2 * a * (foldXiPlus a x s + foldXiMinus a x s)) +
            2 * a ^ 2 := by ring
      _ = foldB a x s + 2 * a * foldC0 a x s + 2 * a ^ 2 := by
        rw [hprod, hsum]
      _ = (1 + a) ^ 2 * x ^ 2 := by
        unfold foldB foldC0
        ring
  have hden : 1 + a ≠ 0 := by linarith
  rw [foldedHalfY_sq hminus, foldedHalfZ_sq hplus]
  unfold halfChordScale
  rw [two_pathRate_div_cosh_pathLogParameter ha0]
  symm
  calc
    (4 * a / (1 + a)) ^ 2 *
          ((foldXiMinus a x s + 1) / 2) *
          ((foldXiPlus a x s + 1) / 2) =
        (4 * a ^ 2 *
          (foldXiPlus a x s * foldXiMinus a x s +
            (foldXiPlus a x s + foldXiMinus a x s) + 1)) /
          (1 + a) ^ 2 := by
            field_simp [hden]
            ring
    _ = x ^ 2 := by
      exact (div_eq_iff (pow_ne_zero 2 hden)).2 (by
        nlinarith [hsym])

/-- Reconstruction of the original vertical coordinate from the two
actual folded roots. -/
theorem s_sq_eq_halfChordScale_sq_mul_foldedHalf_complements
    {a x s : ℝ} (ha0 : 0 < a)
    (hdisc : 0 < foldDiscriminant a x s)
    (hminus : -1 ≤ foldXiMinus a x s)
    (hplus : -1 ≤ foldXiPlus a x s) :
    s ^ 2 = halfChordScale a ^ 2 *
      (Real.cosh (pathLogParameter a) ^ 2 - foldedHalfY a x s ^ 2) *
      (Real.cosh (pathLogParameter a) ^ 2 - foldedHalfZ a x s ^ 2) := by
  have hy := foldedHalfY_sq hminus
  have hz := foldedHalfZ_sq hplus
  have hsum := foldXiPlus_add_foldXiMinus
    (x := x) (s := s) ha0.ne'
  have hx := x_sq_eq_halfChordScale_sq_mul_foldedHalf_sq
    ha0 hdisc hminus hplus
  have hhalfSum :
      4 * a * (foldedHalfY a x s ^ 2 + foldedHalfZ a x s ^ 2) =
        foldC0 a x s + 4 * a := by
    rw [hy, hz]
    calc
      4 * a *
            ((foldXiMinus a x s + 1) / 2 +
              (foldXiPlus a x s + 1) / 2) =
          2 * a * (foldXiPlus a x s + foldXiMinus a x s) +
            4 * a := by ring
      _ = foldC0 a x s + 4 * a := by rw [hsum]
  symm
  calc
    halfChordScale a ^ 2 *
          (Real.cosh (pathLogParameter a) ^ 2 -
            foldedHalfY a x s ^ 2) *
          (Real.cosh (pathLogParameter a) ^ 2 -
            foldedHalfZ a x s ^ 2) =
        (halfChordScale a ^ 2 *
          Real.cosh (pathLogParameter a) ^ 2) *
            Real.cosh (pathLogParameter a) ^ 2 -
          (halfChordScale a ^ 2 *
            Real.cosh (pathLogParameter a) ^ 2) *
            (foldedHalfY a x s ^ 2 + foldedHalfZ a x s ^ 2) +
          halfChordScale a ^ 2 * foldedHalfY a x s ^ 2 *
            foldedHalfZ a x s ^ 2 := by ring
    _ = 4 * a * Real.cosh (pathLogParameter a) ^ 2 -
          4 * a *
            (foldedHalfY a x s ^ 2 + foldedHalfZ a x s ^ 2) +
          x ^ 2 := by
      rw [halfChordScale_sq_mul_cosh_sq ha0, ← hx]
    _ = (1 + a) ^ 2 - (foldC0 a x s + 4 * a) + x ^ 2 := by
      rw [four_mul_mul_cosh_sq_pathLogParameter ha0, hhalfSum]
    _ = s ^ 2 := by
      unfold foldC0
      ring

/-- With the positive sign of `x`, square reconstruction recovers the
unsquared half-chord product. -/
theorem x_eq_halfChordScale_mul_foldedHalf
    {a x s : ℝ} (ha0 : 0 < a)
    (hdisc : 0 < foldDiscriminant a x s)
    (hminus : -1 ≤ foldXiMinus a x s)
    (hplus : -1 ≤ foldXiPlus a x s)
    (hx0 : 0 < x) :
    x = halfChordScale a * foldedHalfY a x s * foldedHalfZ a x s := by
  have hright :
      0 ≤ halfChordScale a * foldedHalfY a x s * foldedHalfZ a x s :=
    mul_nonneg
      (mul_nonneg (halfChordScale_pos ha0).le
        (foldedHalfY_nonneg a x s))
      (foldedHalfZ_nonneg a x s)
  apply (sq_eq_sq₀ hx0.le hright).mp
  calc
    x ^ 2 = halfChordScale a ^ 2 *
        foldedHalfY a x s ^ 2 * foldedHalfZ a x s ^ 2 :=
      x_sq_eq_halfChordScale_sq_mul_foldedHalf_sq
        ha0 hdisc hminus hplus
    _ = (halfChordScale a * foldedHalfY a x s *
        foldedHalfZ a x s) ^ 2 := by ring

/-- Reversible horizontal reconstruction stated for arbitrary generic
nonnegative half variables with the paper's fixed positive signs. -/
theorem x_eq_halfChordScale_mul_genericHalfVariables
    {a x s y z : ℝ} (ha0 : 0 < a)
    (hdisc : 0 < foldDiscriminant a x s)
    (hy0 : 0 ≤ y) (hz0 : 0 < z) (hx0 : 0 < x)
    (hy : foldXiMinus a x s = halfFoldArgument y)
    (hz : foldXiPlus a x s = halfFoldArgument z) :
    x = halfChordScale a * y * z := by
  have hminus : -1 ≤ foldXiMinus a x s := by
    rw [hy]
    unfold halfFoldArgument
    nlinarith [sq_nonneg y]
  have hplus : -1 ≤ foldXiPlus a x s := by
    rw [hz]
    unfold halfFoldArgument
    nlinarith [sq_nonneg z]
  have hvars := foldedHalfVariables_eq_of_generic hy0 hz0.le hy hz
  calc
    x = halfChordScale a * foldedHalfY a x s * foldedHalfZ a x s :=
      x_eq_halfChordScale_mul_foldedHalf
        ha0 hdisc hminus hplus hx0
    _ = halfChordScale a * y * z := by rw [hvars.1, hvars.2]

/-- The positive magnitude of `s` is the positive square root of the
reconstructed complementary product. -/
theorem abs_s_eq_halfChordScale_mul_sqrt_foldedHalf_complements
    {a x s : ℝ} (ha0 : 0 < a)
    (hdisc : 0 < foldDiscriminant a x s)
    (hminus : -1 ≤ foldXiMinus a x s)
    (hplus : -1 ≤ foldXiPlus a x s) :
    |s| = halfChordScale a * Real.sqrt
      ((Real.cosh (pathLogParameter a) ^ 2 - foldedHalfY a x s ^ 2) *
        (Real.cosh (pathLogParameter a) ^ 2 - foldedHalfZ a x s ^ 2)) := by
  let P :=
    (Real.cosh (pathLogParameter a) ^ 2 - foldedHalfY a x s ^ 2) *
      (Real.cosh (pathLogParameter a) ^ 2 - foldedHalfZ a x s ^ 2)
  have hsquare := s_sq_eq_halfChordScale_sq_mul_foldedHalf_complements
    ha0 hdisc hminus hplus
  have hsquareP : s ^ 2 = halfChordScale a ^ 2 * P := by
    simpa only [P, mul_assoc] using hsquare
  have hscale : 0 < halfChordScale a := halfChordScale_pos ha0
  have hP : 0 ≤ P := by
    by_contra h
    have hPneg : P < 0 := lt_of_not_ge h
    have hprodneg : halfChordScale a ^ 2 * P < 0 :=
      mul_neg_of_pos_of_neg (sq_pos_of_pos hscale) hPneg
    nlinarith [sq_nonneg s]
  have hright : 0 ≤ halfChordScale a * Real.sqrt P :=
    mul_nonneg hscale.le (Real.sqrt_nonneg _)
  apply (sq_eq_sq₀ (abs_nonneg s) hright).mp
  calc
    |s| ^ 2 = s ^ 2 := by simp
    _ = halfChordScale a ^ 2 * P := hsquareP
    _ = (halfChordScale a * Real.sqrt P) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hP]

/-- Reversible vertical-magnitude reconstruction for arbitrary generic
nonnegative half variables. -/
theorem abs_s_eq_halfChordScale_mul_sqrt_genericHalf_complements
    {a x s y z : ℝ} (ha0 : 0 < a)
    (hdisc : 0 < foldDiscriminant a x s)
    (hy0 : 0 ≤ y) (hz0 : 0 ≤ z)
    (hy : foldXiMinus a x s = halfFoldArgument y)
    (hz : foldXiPlus a x s = halfFoldArgument z) :
    |s| = halfChordScale a * Real.sqrt
      ((Real.cosh (pathLogParameter a) ^ 2 - y ^ 2) *
        (Real.cosh (pathLogParameter a) ^ 2 - z ^ 2)) := by
  have hminus : -1 ≤ foldXiMinus a x s := by
    rw [hy]
    unfold halfFoldArgument
    nlinarith [sq_nonneg y]
  have hplus : -1 ≤ foldXiPlus a x s := by
    rw [hz]
    unfold halfFoldArgument
    nlinarith [sq_nonneg z]
  have hvars := foldedHalfVariables_eq_of_generic hy0 hz0 hy hz
  calc
    |s| = halfChordScale a * Real.sqrt
        ((Real.cosh (pathLogParameter a) ^ 2 - foldedHalfY a x s ^ 2) *
          (Real.cosh (pathLogParameter a) ^ 2 -
            foldedHalfZ a x s ^ 2)) :=
      abs_s_eq_halfChordScale_mul_sqrt_foldedHalf_complements
        ha0 hdisc hminus hplus
    _ = halfChordScale a * Real.sqrt
        ((Real.cosh (pathLogParameter a) ^ 2 - y ^ 2) *
          (Real.cosh (pathLogParameter a) ^ 2 - z ^ 2)) := by
      rw [hvars.1, hvars.2]

/-- If `s` itself has the positive sign, the preceding magnitude formula
recovers `s` without an absolute value. -/
theorem s_eq_halfChordScale_mul_sqrt_foldedHalf_complements
    {a x s : ℝ} (ha0 : 0 < a)
    (hdisc : 0 < foldDiscriminant a x s)
    (hminus : -1 ≤ foldXiMinus a x s)
    (hplus : -1 ≤ foldXiPlus a x s)
    (hs0 : 0 ≤ s) :
    s = halfChordScale a * Real.sqrt
      ((Real.cosh (pathLogParameter a) ^ 2 - foldedHalfY a x s ^ 2) *
        (Real.cosh (pathLogParameter a) ^ 2 - foldedHalfZ a x s ^ 2)) := by
  calc
    s = |s| := (abs_of_nonneg hs0).symm
    _ = halfChordScale a * Real.sqrt
        ((Real.cosh (pathLogParameter a) ^ 2 - foldedHalfY a x s ^ 2) *
          (Real.cosh (pathLogParameter a) ^ 2 - foldedHalfZ a x s ^ 2)) :=
      abs_s_eq_halfChordScale_mul_sqrt_foldedHalf_complements
        ha0 hdisc hminus hplus

end

end ConnectedPseudospectrum
