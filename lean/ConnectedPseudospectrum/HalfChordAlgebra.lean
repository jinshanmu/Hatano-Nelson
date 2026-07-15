import ConnectedPseudospectrum.FoldedExactCollision
import ConnectedPseudospectrum.HyperbolicParameter
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Half-angle chord algebra

This module proves the exact square-root and folded-variable identities in
`eq:half-variable-identities`.  The definitions use the paper's positive
logarithmic parameter, real trigonometric/hyperbolic radicals, and the actual
folded variables from the signed-pencil generating functions.
-/

namespace ConnectedPseudospectrum

noncomputable section

/-- The common scale factor in the half-angle chord parametrization. -/
def halfChordScale (a : ℝ) : ℝ :=
  2 * pathRate a / Real.cosh (pathLogParameter a)

/-- The trigonometric radical in the half-angle chord parametrization. -/
def halfTrigRadical (a θ : ℝ) : ℝ :=
  Real.sqrt
    (Real.cosh (pathLogParameter a) ^ 2 - Real.cos θ ^ 2)

/-- The hyperbolic radical in the half-angle chord parametrization. -/
def halfHypRadical (a η : ℝ) : ℝ :=
  Real.sqrt
    (Real.cosh (pathLogParameter a) ^ 2 - Real.cosh η ^ 2)

/-- The abscissa of the half-angle chord with inner angle `θ` and outer
hyperbolic coordinate `η`. -/
def halfChordX (a θ η : ℝ) : ℝ :=
  halfChordScale a * Real.cos θ * Real.cosh η

/-- The nonnegative height of the half-angle chord with inner angle `θ` and
outer hyperbolic coordinate `η`. -/
def halfChordS (a θ η : ℝ) : ℝ :=
  halfChordScale a * halfTrigRadical a θ * halfHypRadical a η

theorem halfTrigRadicand_nonneg (a θ : ℝ) :
    0 ≤ Real.cosh (pathLogParameter a) ^ 2 - Real.cos θ ^ 2 := by
  nlinarith [Real.cosh_sq_sub_sinh_sq (pathLogParameter a),
    Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sinh (pathLogParameter a))]

theorem halfTrigRadical_sq (a θ : ℝ) :
    halfTrigRadical a θ ^ 2 =
      Real.cosh (pathLogParameter a) ^ 2 - Real.cos θ ^ 2 := by
  exact Real.sq_sqrt (halfTrigRadicand_nonneg a θ)

theorem halfHypRadicand_nonneg {a η : ℝ}
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a) :
    0 ≤ Real.cosh (pathLogParameter a) ^ 2 - Real.cosh η ^ 2 := by
  have hcosh : Real.cosh η ≤ Real.cosh (pathLogParameter a) := by
    rw [Real.cosh_le_cosh]
    rw [abs_of_nonneg hη0, abs_of_nonneg (hη0.trans hηh)]
    exact hηh
  nlinarith [Real.cosh_pos η, Real.cosh_pos (pathLogParameter a)]

theorem halfHypRadical_sq {a η : ℝ}
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a) :
    halfHypRadical a η ^ 2 =
      Real.cosh (pathLogParameter a) ^ 2 - Real.cosh η ^ 2 := by
  exact Real.sq_sqrt (halfHypRadicand_nonneg hη0 hηh)

private theorem halfChord_plus_square_algebra
    {r c y z p q : ℝ} (hc : c ≠ 0)
    (hp : p ^ 2 = c ^ 2 - y ^ 2)
    (hq : q ^ 2 = c ^ 2 - z ^ 2) :
    (2 * r * c + (2 * r / c) * y * z) ^ 2 -
        ((2 * r / c) * p * q) ^ 2 =
      4 * r ^ 2 * (z + y) ^ 2 := by
  calc
    (2 * r * c + (2 * r / c) * y * z) ^ 2 -
          ((2 * r / c) * p * q) ^ 2 =
        4 * r ^ 2 / c ^ 2 *
          ((c ^ 2 + y * z) ^ 2 - p ^ 2 * q ^ 2) := by
            field_simp [hc]
            ring
    _ = 4 * r ^ 2 / c ^ 2 *
          ((c ^ 2 + y * z) ^ 2 -
            (c ^ 2 - y ^ 2) * (c ^ 2 - z ^ 2)) := by rw [hp, hq]
    _ = 4 * r ^ 2 * (z + y) ^ 2 := by
      field_simp [hc]
      ring

private theorem halfChord_minus_square_algebra
    {r c y z p q : ℝ} (hc : c ≠ 0)
    (hp : p ^ 2 = c ^ 2 - y ^ 2)
    (hq : q ^ 2 = c ^ 2 - z ^ 2) :
    (2 * r * c - (2 * r / c) * y * z) ^ 2 -
        ((2 * r / c) * p * q) ^ 2 =
      4 * r ^ 2 * (z - y) ^ 2 := by
  calc
    (2 * r * c - (2 * r / c) * y * z) ^ 2 -
          ((2 * r / c) * p * q) ^ 2 =
        4 * r ^ 2 / c ^ 2 *
          ((c ^ 2 - y * z) ^ 2 - p ^ 2 * q ^ 2) := by
            field_simp [hc]
            ring
    _ = 4 * r ^ 2 / c ^ 2 *
          ((c ^ 2 - y * z) ^ 2 -
            (c ^ 2 - y ^ 2) * (c ^ 2 - z ^ 2)) := by rw [hp, hq]
    _ = 4 * r ^ 2 * (z - y) ^ 2 := by
      field_simp [hc]
      ring

theorem halfChord_plus_identity
    {a θ η : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a) :
    (1 + a + halfChordX a θ η) ^ 2 - halfChordS a θ η ^ 2 =
      4 * a * (Real.cosh η + Real.cos θ) ^ 2 := by
  have hsum := two_pathRate_mul_cosh_pathLogParameter ha0
  have hr := pathRate_mul_self ha0.le
  have hr2 : pathRate a ^ 2 = a := by simpa [pow_two] using hr
  have hp := halfTrigRadical_sq a θ
  have hq := halfHypRadical_sq hη0 hηh
  have hc : Real.cosh (pathLogParameter a) ≠ 0 :=
    (Real.cosh_pos _).ne'
  unfold halfChordX halfChordS halfChordScale
  rw [← hsum]
  have h := halfChord_plus_square_algebra
    (r := pathRate a) hc hp hq
  rw [hr2] at h
  exact h

theorem halfChord_minus_identity
    {a θ η : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a) :
    (1 + a - halfChordX a θ η) ^ 2 - halfChordS a θ η ^ 2 =
      4 * a * (Real.cosh η - Real.cos θ) ^ 2 := by
  have hsum := two_pathRate_mul_cosh_pathLogParameter ha0
  have hr := pathRate_mul_self ha0.le
  have hp := halfTrigRadical_sq a θ
  have hq := halfHypRadical_sq hη0 hηh
  have hr2 : pathRate a ^ 2 = a := by simpa [pow_two] using hr
  have hc : Real.cosh (pathLogParameter a) ≠ 0 :=
    (Real.cosh_pos _).ne'
  unfold halfChordX halfChordS halfChordScale
  rw [← hsum]
  have h := halfChord_minus_square_algebra
    (r := pathRate a) hc hp hq
  rw [hr2] at h
  exact h

private theorem halfChord_foldC0_algebra
    {r a c d y z p q : ℝ} (hc : c ≠ 0)
    (hr : r ^ 2 = a) (hd : c ^ 2 - d ^ 2 = 1)
    (hp : p ^ 2 = c ^ 2 - y ^ 2)
    (hq : q ^ 2 = c ^ 2 - z ^ 2) :
    ((2 * r / c) * y * z) ^ 2 + (2 * r * d) ^ 2 -
        ((2 * r / c) * p * q) ^ 2 =
      4 * a * (z ^ 2 + y ^ 2 - 1) := by
  have hd' : d ^ 2 = c ^ 2 - 1 := by linarith
  calc
    ((2 * r / c) * y * z) ^ 2 + (2 * r * d) ^ 2 -
          ((2 * r / c) * p * q) ^ 2 =
        4 * r ^ 2 / c ^ 2 *
          (y ^ 2 * z ^ 2 + c ^ 2 * d ^ 2 - p ^ 2 * q ^ 2) := by
            field_simp [hc]
            ring
    _ = 4 * a / c ^ 2 *
          (y ^ 2 * z ^ 2 + c ^ 2 * (c ^ 2 - 1) -
            (c ^ 2 - y ^ 2) * (c ^ 2 - z ^ 2)) := by rw [hr, hd', hp, hq]
    _ = 4 * a * (z ^ 2 + y ^ 2 - 1) := by
      field_simp [hc]
      ring

theorem foldC0_halfChord
    {a θ η : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a) :
    foldC0 a (halfChordX a θ η) (halfChordS a θ η) =
      4 * a * (Real.cosh η ^ 2 + Real.cos θ ^ 2 - 1) := by
  have hdiff := two_pathRate_mul_sinh_pathLogParameter ha0
  have hr := pathRate_mul_self ha0.le
  have hr2 : pathRate a ^ 2 = a := by simpa [pow_two] using hr
  have hd := Real.cosh_sq_sub_sinh_sq (pathLogParameter a)
  have hp := halfTrigRadical_sq a θ
  have hq := halfHypRadical_sq hη0 hηh
  have hc : Real.cosh (pathLogParameter a) ≠ 0 :=
    (Real.cosh_pos _).ne'
  unfold foldC0 halfChordX halfChordS halfChordScale
  rw [← hdiff]
  exact halfChord_foldC0_algebra hc hr2 hd hp hq

theorem foldDiscriminant_halfChord
    {a θ η : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a) :
    foldDiscriminant a (halfChordX a θ η) (halfChordS a θ η) =
      16 * a ^ 2 * (Real.cosh η ^ 2 - Real.cos θ ^ 2) ^ 2 := by
  unfold foldDiscriminant
  rw [halfChord_minus_identity ha0 hη0 hηh,
    halfChord_plus_identity ha0 hη0 hηh]
  ring

theorem sqrt_foldDiscriminant_halfChord
    {a θ η : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a) :
    Real.sqrt
        (foldDiscriminant a (halfChordX a θ η) (halfChordS a θ η)) =
      4 * a * (Real.cosh η ^ 2 - Real.cos θ ^ 2) := by
  have hyz : |Real.cos θ| ≤ Real.cosh η :=
    (Real.abs_cos_le_one θ).trans (Real.one_le_cosh η)
  have hsq : Real.cos θ ^ 2 ≤ Real.cosh η ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (Real.cos θ))
      (Real.cosh_pos η).le).2 hyz
    simpa only [sq_abs] using h
  have hnonneg : 0 ≤ 4 * a *
      (Real.cosh η ^ 2 - Real.cos θ ^ 2) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hsq)
  rw [foldDiscriminant_halfChord ha0 hη0 hηh]
  rw [show 16 * a ^ 2 *
      (Real.cosh η ^ 2 - Real.cos θ ^ 2) ^ 2 =
        (4 * a * (Real.cosh η ^ 2 - Real.cos θ ^ 2)) ^ 2 by ring]
  exact Real.sqrt_sq hnonneg

theorem foldXiPlus_halfChord
    {a θ η : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a) :
    foldXiPlus a (halfChordX a θ η) (halfChordS a θ η) =
      2 * Real.cosh η ^ 2 - 1 := by
  rw [foldXiPlus, foldC0_halfChord ha0 hη0 hηh,
    sqrt_foldDiscriminant_halfChord ha0 hη0 hηh]
  field_simp [ha0.ne']
  ring

theorem foldXiMinus_halfChord
    {a θ η : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a) :
    foldXiMinus a (halfChordX a θ η) (halfChordS a θ η) =
      2 * Real.cos θ ^ 2 - 1 := by
  rw [foldXiMinus, foldC0_halfChord ha0 hη0 hηh,
    sqrt_foldDiscriminant_halfChord ha0 hη0 hηh]
  field_simp [ha0.ne']
  ring

theorem foldZeta_signed_halfChord
    {a θ η varsigma : ℝ} (ha0 : 0 < a) :
    foldZeta a (varsigma * halfChordS a θ η) =
      2 * Real.cosh (pathLogParameter a) ^ 2 - 1 +
        2 * varsigma * halfTrigRadical a θ * halfHypRadical a η := by
  have hsum := two_pathRate_mul_cosh_pathLogParameter ha0
  have hr := pathRate_mul_self ha0.le
  have hr2 : pathRate a ^ 2 = a := by simpa [pow_two] using hr
  have hc : Real.cosh (pathLogParameter a) ≠ 0 :=
    (Real.cosh_pos _).ne'
  have hbase :
      1 + a ^ 2 =
        2 * a * (2 * Real.cosh (pathLogParameter a) ^ 2 - 1) := by
    have hsquare := congrArg (fun w : ℝ => w ^ 2) hsum
    dsimp only at hsquare
    have hsquare' :
        4 * pathRate a ^ 2 * Real.cosh (pathLogParameter a) ^ 2 =
          (1 + a) ^ 2 := by
      calc
        4 * pathRate a ^ 2 * Real.cosh (pathLogParameter a) ^ 2 =
            (2 * pathRate a * Real.cosh (pathLogParameter a)) ^ 2 := by ring
        _ = (1 + a) ^ 2 := hsquare
    rw [hr2] at hsquare'
    nlinarith
  unfold foldZeta halfChordS halfChordScale
  rw [hbase, ← hsum]
  field_simp [ha0.ne', hc]
  rw [hr2]
  ring

end

end ConnectedPseudospectrum
