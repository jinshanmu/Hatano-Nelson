import ConnectedPseudospectrum.OuterChordCoordinates
import ConnectedPseudospectrum.HalfChordEvenReduction
import ConnectedPseudospectrum.HalfChordOddReduction

/-!
# Coordinate-free folded algebra on the outer chord

The half-chord calculation is algebraic in its outer variable.  This module
performs that calculation with an arbitrary real outer variable `z`, rather
than choosing either the hyperbolic coordinate `z = cosh eta` or the elliptic
coordinate `z = cos phi`.  In particular, the resulting signed determinant
equations remain valid while the endpoint-side solution passes through
`z = 1`.
-/

namespace ConnectedPseudospectrum

noncomputable section

/-- The positive square-root factor attached to a coordinate-free outer
variable. -/
def outerChordRadical (a z : ℝ) : ℝ :=
  Real.sqrt
    (Real.cosh (pathLogParameter a) ^ 2 - z ^ 2)

/-- In the hyperbolic chart the coordinate-free outer radical is the
existing hyperbolic radical. -/
theorem outerChordRadical_cosh (a η : ℝ) :
    outerChordRadical a (Real.cosh η) = halfHypRadical a η := by
  rfl

/-- In the elliptic chart the coordinate-free outer radical is the same
trigonometric radical used for an inner angle. -/
theorem outerChordRadical_cos (a φ : ℝ) :
    outerChordRadical a (Real.cos φ) = halfTrigRadical a φ := by
  rfl

/-- The outer radical has a nonnegative radicand throughout the closed
coordinate-free chord region. -/
theorem outerChordRadicand_nonneg
    {a z : ℝ}
    (hz : |z| ≤ Real.cosh (pathLogParameter a)) :
    0 ≤ Real.cosh (pathLogParameter a) ^ 2 - z ^ 2 := by
  have hc0 : 0 ≤ Real.cosh (pathLogParameter a) :=
    (Real.cosh_pos _).le
  have hzsq : z ^ 2 ≤ Real.cosh (pathLogParameter a) ^ 2 := by
    have h :=
      (sq_le_sq₀ (abs_nonneg z) hc0).2 hz
    simpa only [sq_abs] using h
  exact sub_nonneg.mpr hzsq

/-- Squaring the coordinate-free outer radical recovers its radicand. -/
theorem outerChordRadical_sq
    {a z : ℝ}
    (hz : |z| ≤ Real.cosh (pathLogParameter a)) :
    outerChordRadical a z ^ 2 =
      Real.cosh (pathLogParameter a) ^ 2 - z ^ 2 := by
  exact Real.sq_sqrt (outerChordRadicand_nonneg hz)

/-- The single square root in `outerChordS` factors as the product of the
inner and outer positive radicals. -/
theorem outerChordS_factorization
    {a θ z : ℝ}
    (hz : |z| ≤ Real.cosh (pathLogParameter a)) :
    outerChordS a θ z =
      halfChordScale a * halfTrigRadical a θ * outerChordRadical a z := by
  unfold outerChordS halfTrigRadical outerChordRadical
  rw [Real.sqrt_mul' _ (outerChordRadicand_nonneg hz)]
  ring

private theorem outerChord_plus_square_algebra
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

private theorem outerChord_minus_square_algebra
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

/-- The first square identity in `eq:half-variable-identities`, with an
arbitrary coordinate-free outer variable. -/
theorem outerChord_plus_identity
    {a θ z : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a)) :
    (1 + a + outerChordX a θ z) ^ 2 - outerChordS a θ z ^ 2 =
      4 * a * (z + Real.cos θ) ^ 2 := by
  have hsum := two_pathRate_mul_cosh_pathLogParameter ha0
  have hr := pathRate_mul_self ha0.le
  have hr2 : pathRate a ^ 2 = a := by simpa [pow_two] using hr
  have hp := halfTrigRadical_sq a θ
  have hq := outerChordRadical_sq hz
  have hc : Real.cosh (pathLogParameter a) ≠ 0 :=
    (Real.cosh_pos _).ne'
  rw [outerChordS_factorization hz]
  unfold outerChordX halfChordScale
  rw [← hsum]
  have h := outerChord_plus_square_algebra
    (r := pathRate a) hc hp hq
  rw [hr2] at h
  exact h

/-- The second square identity in `eq:half-variable-identities`, with an
arbitrary coordinate-free outer variable. -/
theorem outerChord_minus_identity
    {a θ z : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a)) :
    (1 + a - outerChordX a θ z) ^ 2 - outerChordS a θ z ^ 2 =
      4 * a * (z - Real.cos θ) ^ 2 := by
  have hsum := two_pathRate_mul_cosh_pathLogParameter ha0
  have hr := pathRate_mul_self ha0.le
  have hr2 : pathRate a ^ 2 = a := by simpa [pow_two] using hr
  have hp := halfTrigRadical_sq a θ
  have hq := outerChordRadical_sq hz
  have hc : Real.cosh (pathLogParameter a) ≠ 0 :=
    (Real.cosh_pos _).ne'
  rw [outerChordS_factorization hz]
  unfold outerChordX halfChordScale
  rw [← hsum]
  have h := outerChord_minus_square_algebra
    (r := pathRate a) hc hp hq
  rw [hr2] at h
  exact h

private theorem outerChord_foldC0_algebra
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

/-- Coordinate-free evaluation of the folded coefficient `C₀`. -/
theorem foldC0_outerChord
    {a θ z : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a)) :
    foldC0 a (outerChordX a θ z) (outerChordS a θ z) =
      4 * a * (z ^ 2 + Real.cos θ ^ 2 - 1) := by
  have hdiff := two_pathRate_mul_sinh_pathLogParameter ha0
  have hr := pathRate_mul_self ha0.le
  have hr2 : pathRate a ^ 2 = a := by simpa [pow_two] using hr
  have hd := Real.cosh_sq_sub_sinh_sq (pathLogParameter a)
  have hp := halfTrigRadical_sq a θ
  have hq := outerChordRadical_sq hz
  have hc : Real.cosh (pathLogParameter a) ≠ 0 :=
    (Real.cosh_pos _).ne'
  rw [outerChordS_factorization hz]
  unfold foldC0 outerChordX halfChordScale
  rw [← hdiff]
  exact outerChord_foldC0_algebra hc hr2 hd hp hq

/-- Coordinate-free folded discriminant. -/
theorem foldDiscriminant_outerChord
    {a θ z : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a)) :
    foldDiscriminant a (outerChordX a θ z) (outerChordS a θ z) =
      16 * a ^ 2 * (z ^ 2 - Real.cos θ ^ 2) ^ 2 := by
  unfold foldDiscriminant
  rw [outerChord_minus_identity ha0 hz, outerChord_plus_identity ha0 hz]
  ring

/-- On the ordered outer sheet, the real square root of the folded
discriminant selects `z²-cos²(theta)`. -/
theorem sqrt_foldDiscriminant_outerChord
    {a θ z : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a))
    (horder : Real.cos θ ^ 2 < z ^ 2) :
    Real.sqrt
        (foldDiscriminant a (outerChordX a θ z) (outerChordS a θ z)) =
      4 * a * (z ^ 2 - Real.cos θ ^ 2) := by
  have hnonneg : 0 ≤ 4 * a * (z ^ 2 - Real.cos θ ^ 2) := by
    exact mul_nonneg (mul_nonneg (by norm_num) ha0.le)
      (sub_nonneg.mpr horder.le)
  rw [foldDiscriminant_outerChord ha0 hz]
  rw [show 16 * a ^ 2 * (z ^ 2 - Real.cos θ ^ 2) ^ 2 =
      (4 * a * (z ^ 2 - Real.cos θ ^ 2)) ^ 2 by ring]
  exact Real.sqrt_sq hnonneg

/-- The plus folded variable is the coordinate-free outer variable. -/
theorem foldXiPlus_outerChord
    {a θ z : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a))
    (horder : Real.cos θ ^ 2 < z ^ 2) :
    foldXiPlus a (outerChordX a θ z) (outerChordS a θ z) =
      2 * z ^ 2 - 1 := by
  rw [foldXiPlus, foldC0_outerChord ha0 hz,
    sqrt_foldDiscriminant_outerChord ha0 hz horder]
  field_simp [ha0.ne']
  ring

/-- The minus folded variable is the coordinate-free inner variable. -/
theorem foldXiMinus_outerChord
    {a θ z : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a))
    (horder : Real.cos θ ^ 2 < z ^ 2) :
    foldXiMinus a (outerChordX a θ z) (outerChordS a θ z) =
      2 * Real.cos θ ^ 2 - 1 := by
  rw [foldXiMinus, foldC0_outerChord ha0 hz,
    sqrt_foldDiscriminant_outerChord ha0 hz horder]
  field_simp [ha0.ne']
  ring

/-- Changing the chord height by a sign does not change `C₀`. -/
theorem foldC0_signed_outerChord_eq
    (a θ z varsigma : ℝ) (hsign : varsigma ^ 2 = 1) :
    foldC0 a (outerChordX a θ z) (varsigma * outerChordS a θ z) =
      foldC0 a (outerChordX a θ z) (outerChordS a θ z) := by
  unfold foldC0
  nlinarith [sq_nonneg (outerChordS a θ z)]

/-- Changing the chord height by a sign does not change the folded
discriminant. -/
theorem foldDiscriminant_signed_outerChord_eq
    (a θ z varsigma : ℝ) (hsign : varsigma ^ 2 = 1) :
    foldDiscriminant a (outerChordX a θ z)
        (varsigma * outerChordS a θ z) =
      foldDiscriminant a (outerChordX a θ z) (outerChordS a θ z) := by
  unfold foldDiscriminant
  have hsquare : (varsigma * outerChordS a θ z) ^ 2 =
      outerChordS a θ z ^ 2 := by
    rw [mul_pow, hsign, one_mul]
  rw [hsquare]

/-- Signed coordinate-free evaluation of `xi₊`. -/
theorem foldXiPlus_signed_outerChord
    {a θ z varsigma : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a))
    (horder : Real.cos θ ^ 2 < z ^ 2)
    (hsign : varsigma ^ 2 = 1) :
    foldXiPlus a (outerChordX a θ z)
        (varsigma * outerChordS a θ z) = 2 * z ^ 2 - 1 := by
  unfold foldXiPlus
  rw [foldC0_signed_outerChord_eq a θ z varsigma hsign,
    foldDiscriminant_signed_outerChord_eq a θ z varsigma hsign]
  exact foldXiPlus_outerChord ha0 hz horder

/-- Signed coordinate-free evaluation of `xi₋`. -/
theorem foldXiMinus_signed_outerChord
    {a θ z varsigma : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a))
    (horder : Real.cos θ ^ 2 < z ^ 2)
    (hsign : varsigma ^ 2 = 1) :
    foldXiMinus a (outerChordX a θ z)
        (varsigma * outerChordS a θ z) =
      2 * Real.cos θ ^ 2 - 1 := by
  unfold foldXiMinus
  rw [foldC0_signed_outerChord_eq a θ z varsigma hsign,
    foldDiscriminant_signed_outerChord_eq a θ z varsigma hsign]
  exact foldXiMinus_outerChord ha0 hz horder

/-- The ordered coordinate-free folded variables are distinct. -/
theorem foldXi_signed_outerChord_ne
    {a θ z varsigma : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a))
    (horder : Real.cos θ ^ 2 < z ^ 2)
    (hsign : varsigma ^ 2 = 1) :
    foldXiPlus a (outerChordX a θ z)
        (varsigma * outerChordS a θ z) ≠
      foldXiMinus a (outerChordX a θ z)
        (varsigma * outerChordS a θ z) := by
  rw [foldXiPlus_signed_outerChord ha0 hz horder hsign,
    foldXiMinus_signed_outerChord ha0 hz horder hsign]
  linarith

/-- Coordinate-free signed evaluation of the even generating-function
boundary value `zeta`. -/
theorem foldZeta_signed_outerChord
    {a θ z varsigma : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a)) :
    foldZeta a (varsigma * outerChordS a θ z) =
      2 * Real.cosh (pathLogParameter a) ^ 2 - 1 +
        2 * varsigma * halfTrigRadical a θ * outerChordRadical a z := by
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
  rw [outerChordS_factorization hz]
  unfold foldZeta halfChordScale
  rw [hbase, ← hsum]
  field_simp [ha0.ne', hc]
  rw [hr2]
  ring

/-- The sum factor in the even reduction cannot vanish on an ordered
coordinate-free sheet. -/
theorem outerChord_even_prefactor_ne_zero
    {a θ z varsigma : ℝ}
    (hz : |z| ≤ Real.cosh (pathLogParameter a))
    (hsign : varsigma ^ 2 = 1)
    (horder : Real.cos θ ^ 2 < z ^ 2) :
    halfTrigRadical a θ + varsigma * outerChordRadical a z ≠ 0 := by
  have hp0 : 0 ≤ halfTrigRadical a θ := Real.sqrt_nonneg _
  have hq0 : 0 ≤ outerChordRadical a z := Real.sqrt_nonneg _
  have hp := halfTrigRadical_sq a θ
  have hq := outerChordRadical_sq hz
  have hfactor : (varsigma - 1) * (varsigma + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hplus | hminus
  · have hs : varsigma = 1 := by linarith
    rw [hs]
    intro hzero
    have hpzero : halfTrigRadical a θ = 0 := by linarith
    have hqzero : outerChordRadical a z = 0 := by linarith
    nlinarith
  · have hs : varsigma = -1 := by linarith
    rw [hs]
    intro hzero
    nlinarith

/-- The extra odd-fold factor cannot vanish on an ordered coordinate-free
sheet. -/
theorem outerChord_odd_extra_factor_ne_zero
    {a θ z varsigma : ℝ}
    (hz : |z| ≤ Real.cosh (pathLogParameter a))
    (hsign : varsigma ^ 2 = 1)
    (horder : Real.cos θ ^ 2 < z ^ 2) :
    outerChordRadical a z * Real.cos θ +
        varsigma * halfTrigRadical a θ * z ≠ 0 := by
  intro hzero
  have heq : outerChordRadical a z * Real.cos θ =
      -varsigma * halfTrigRadical a θ * z := by
    linarith
  have hsquare :
      (outerChordRadical a z * Real.cos θ) ^ 2 =
        (halfTrigRadical a θ * z) ^ 2 := by
    rw [heq]
    calc
      (-varsigma * halfTrigRadical a θ * z) ^ 2 =
          varsigma ^ 2 * (halfTrigRadical a θ * z) ^ 2 := by ring
      _ = (halfTrigRadical a θ * z) ^ 2 := by rw [hsign, one_mul]
  have hp := halfTrigRadical_sq a θ
  have hq := outerChordRadical_sq hz
  rw [mul_pow, mul_pow, hp, hq] at hsquare
  have hc : 0 < Real.cosh (pathLogParameter a) ^ 2 :=
    sq_pos_of_pos (Real.cosh_pos _)
  nlinarith

/-- Coordinate-free evaluation of the odd generating-function boundary
coefficient. -/
theorem foldOddBeta_signed_outerChord
    {a θ z varsigma : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a)) :
    foldOddBeta a (outerChordX a θ z)
        (varsigma * outerChordS a θ z) =
      halfChordScale a *
        (Real.cos θ * z *
            (2 * Real.cosh (pathLogParameter a) ^ 2 - 1) +
          varsigma * halfTrigRadical a θ * outerChordRadical a z) := by
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
  rw [outerChordS_factorization hz]
  unfold foldOddBeta outerChordX halfChordScale
  rw [hbase]
  field_simp [ha0.ne', hc]

/-- The numerator of the even divided difference factors by the
coordinate-free signed chord equation. -/
theorem foldEvenChebyshev_numerator_signed_outerChord
    (m : ℕ) {a θ z varsigma : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a))
    (horder : Real.cos θ ^ 2 < z ^ 2)
    (hsign : varsigma ^ 2 = 1) :
    foldEvenChebyshevFunction m
          (foldXiPlus a (outerChordX a θ z)
            (varsigma * outerChordS a θ z))
          (foldZeta a (varsigma * outerChordS a θ z)) -
        foldEvenChebyshevFunction m
          (foldXiMinus a (outerChordX a θ z)
            (varsigma * outerChordS a θ z))
          (foldZeta a (varsigma * outerChordS a θ z)) =
      2 * (halfTrigRadical a θ + varsigma * outerChordRadical a z) *
        (halfTrigRadical a θ * chebyshevU (2 * m) (Real.cos θ) -
          varsigma * outerChordRadical a z * chebyshevU (2 * m) z) := by
  rw [foldXiPlus_signed_outerChord ha0 hz horder hsign,
    foldXiMinus_signed_outerChord ha0 hz horder hsign,
    foldZeta_signed_outerChord ha0 hz]
  unfold foldEvenChebyshevFunction
  rw [chebyshevU_half_angle_even_index m z,
    chebyshevU_half_angle_even_index m (Real.cos θ)]
  have hp := halfTrigRadical_sq a θ
  have hq := outerChordRadical_sq hz
  have hzcoef :
      (2 * z ^ 2 - 1 -
          (2 * Real.cosh (pathLogParameter a) ^ 2 - 1 +
            2 * varsigma * halfTrigRadical a θ * outerChordRadical a z)) =
        -2 * outerChordRadical a z *
          (outerChordRadical a z + varsigma * halfTrigRadical a θ) := by
    nlinarith
  have hycoef :
      (2 * Real.cos θ ^ 2 - 1 -
          (2 * Real.cosh (pathLogParameter a) ^ 2 - 1 +
            2 * varsigma * halfTrigRadical a θ * outerChordRadical a z)) =
        -2 * halfTrigRadical a θ *
          (halfTrigRadical a θ + varsigma * outerChordRadical a z) := by
    nlinarith
  have hswap :
      outerChordRadical a z + varsigma * halfTrigRadical a θ =
        varsigma *
          (halfTrigRadical a θ + varsigma * outerChordRadical a z) := by
    calc
      outerChordRadical a z + varsigma * halfTrigRadical a θ =
          varsigma * halfTrigRadical a θ +
            varsigma ^ 2 * outerChordRadical a z := by rw [hsign]; ring
      _ = varsigma *
          (halfTrigRadical a θ + varsigma * outerChordRadical a z) := by ring
  rw [hzcoef, hycoef, hswap]
  ring

/-- Complete even folded-sequence factorization in coordinate-free outer
variables. -/
theorem foldEvenSequence_signed_outerChord_factorization
    (m : ℕ) {a θ z varsigma : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a))
    (horder : Real.cos θ ^ 2 < z ^ 2)
    (hsign : varsigma ^ 2 = 1) :
    foldEvenSequence a (outerChordX a θ z)
        (varsigma * outerChordS a θ z) m =
      a ^ m *
        (2 * (halfTrigRadical a θ + varsigma * outerChordRadical a z) *
          (halfTrigRadical a θ * chebyshevU (2 * m) (Real.cos θ) -
            varsigma * outerChordRadical a z * chebyshevU (2 * m) z) /
          ((2 * z ^ 2 - 1) - (2 * Real.cos θ ^ 2 - 1))) := by
  have hxi := foldXi_signed_outerChord_ne ha0 hz horder hsign
  have hsum := foldXiPlus_add_foldXiMinus
    (x := outerChordX a θ z)
    (s := varsigma * outerChordS a θ z) ha0.ne'
  have hdisc : 0 ≤ foldDiscriminant a (outerChordX a θ z)
      (varsigma * outerChordS a θ z) := by
    rw [foldDiscriminant_signed_outerChord_eq a θ z varsigma hsign,
      foldDiscriminant_outerChord ha0 hz]
    positivity
  have hprod := foldXiPlus_mul_foldXiMinus
    (x := outerChordX a θ z)
    (s := varsigma * outerChordS a θ z) ha0.ne' hdisc
  rw [foldEvenSequence_eq_chebyshevDividedDifference
    ha0.ne' hxi hsum hprod]
  rw [foldEvenChebyshev_numerator_signed_outerChord m ha0 hz horder hsign,
    foldXiPlus_signed_outerChord ha0 hz horder hsign,
    foldXiMinus_signed_outerChord ha0 hz horder hsign]

/-- The even folded determinant vanishes exactly when the signed
coordinate-free chord equation holds. -/
theorem foldEvenSequence_signed_outerChord_eq_zero_iff
    (m : ℕ) {a θ z varsigma : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a))
    (horder : Real.cos θ ^ 2 < z ^ 2)
    (hsign : varsigma ^ 2 = 1) :
    foldEvenSequence a (outerChordX a θ z)
        (varsigma * outerChordS a θ z) m = 0 ↔
      halfTrigRadical a θ * chebyshevU (2 * m) (Real.cos θ) =
        varsigma * outerChordRadical a z * chebyshevU (2 * m) z := by
  rw [foldEvenSequence_signed_outerChord_factorization m ha0
    hz horder hsign]
  have haPow : a ^ m ≠ 0 := pow_ne_zero _ ha0.ne'
  have hpref := outerChord_even_prefactor_ne_zero hz hsign horder
  have hden : (2 * z ^ 2 - 1) - (2 * Real.cos θ ^ 2 - 1) ≠ 0 := by
    linarith
  constructor
  · intro h
    have hdiv :
        2 * (halfTrigRadical a θ + varsigma * outerChordRadical a z) *
              (halfTrigRadical a θ * chebyshevU (2 * m) (Real.cos θ) -
                varsigma * outerChordRadical a z * chebyshevU (2 * m) z) /
            ((2 * z ^ 2 - 1) - (2 * Real.cos θ ^ 2 - 1)) = 0 :=
      (mul_eq_zero.mp h).resolve_left haPow
    have hnum :
        2 * (halfTrigRadical a θ + varsigma * outerChordRadical a z) *
          (halfTrigRadical a θ * chebyshevU (2 * m) (Real.cos θ) -
            varsigma * outerChordRadical a z * chebyshevU (2 * m) z) = 0 := by
      exact ((div_eq_zero_iff.mp hdiv).resolve_right hden)
    have hres :
        halfTrigRadical a θ * chebyshevU (2 * m) (Real.cos θ) -
          varsigma * outerChordRadical a z * chebyshevU (2 * m) z = 0 := by
      rcases mul_eq_zero.mp hnum with htwoPref | hres
      · rcases mul_eq_zero.mp htwoPref with htwo | hp
        · norm_num at htwo
        · exact (hpref hp).elim
      · exact hres
    exact sub_eq_zero.mp hres
  · intro hchord
    have hres :
        halfTrigRadical a θ * chebyshevU (2 * m) (Real.cos θ) -
          varsigma * outerChordRadical a z * chebyshevU (2 * m) z = 0 :=
      sub_eq_zero.mpr hchord
    rw [hres, mul_zero, zero_div, mul_zero]

/-- The numerator of the odd divided difference factors by the
coordinate-free signed chord equation. -/
theorem foldOddChebyshev_numerator_signed_outerChord
    (m : ℕ) {a θ z varsigma : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a))
    (horder : Real.cos θ ^ 2 < z ^ 2)
    (hsign : varsigma ^ 2 = 1) (hy : Real.cos θ ≠ 0) :
    foldOddChebyshevFunction m (outerChordX a θ z)
          (varsigma * outerChordS a θ z)
          (foldOddBeta a (outerChordX a θ z)
            (varsigma * outerChordS a θ z))
          (foldXiPlus a (outerChordX a θ z)
            (varsigma * outerChordS a θ z)) -
        foldOddChebyshevFunction m (outerChordX a θ z)
          (varsigma * outerChordS a θ z)
          (foldOddBeta a (outerChordX a θ z)
            (varsigma * outerChordS a θ z))
          (foldXiMinus a (outerChordX a θ z)
            (varsigma * outerChordS a θ z)) =
      varsigma * halfChordScale a *
        (outerChordRadical a z * Real.cos θ +
          varsigma * halfTrigRadical a θ * z) *
        (halfTrigRadical a θ * chebyshevU (2 * m + 1) (Real.cos θ) -
          varsigma * outerChordRadical a z * chebyshevU (2 * m + 1) z) := by
  rw [foldXiPlus_signed_outerChord ha0 hz horder hsign,
    foldXiMinus_signed_outerChord ha0 hz horder hsign,
    foldOddBeta_signed_outerChord ha0 hz]
  rw [outerChordS_factorization hz]
  unfold foldOddChebyshevFunction outerChordX
  rw [chebyshevU_half_angle_odd_index m (show z ≠ 0 by
      intro hz0
      rw [hz0] at horder
      nlinarith [sq_nonneg (Real.cos θ)]),
    chebyshevU_half_angle_odd_index m hy]
  let L := halfChordScale a
  let y := Real.cos θ
  let p := halfTrigRadical a θ
  let q := outerChordRadical a z
  let c := Real.cosh (pathLogParameter a)
  have hp : p ^ 2 = c ^ 2 - y ^ 2 := halfTrigRadical_sq a θ
  have hq : q ^ 2 = c ^ 2 - z ^ 2 := outerChordRadical_sq hz
  have hzcoef :
      (L * y * z - varsigma * L * p * q) * (2 * z ^ 2 - 1) -
          L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q) =
        -2 * L * q * z * (y * q + varsigma * p * z) := by
    have hzsub : z ^ 2 - c ^ 2 = -q ^ 2 := by linarith
    calc
      (L * y * z - varsigma * L * p * q) * (2 * z ^ 2 - 1) -
            L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q) =
          L * (2 * y * z * (z ^ 2 - c ^ 2) -
            2 * varsigma * p * q * z ^ 2) := by ring
      _ = -2 * L * q * z * (y * q + varsigma * p * z) := by
        rw [hzsub]
        ring
  have hycoef :
      (L * y * z - varsigma * L * p * q) * (2 * y ^ 2 - 1) -
          L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q) =
        -2 * L * p * y * (z * p + varsigma * q * y) := by
    have hysub : y ^ 2 - c ^ 2 = -p ^ 2 := by linarith
    calc
      (L * y * z - varsigma * L * p * q) * (2 * y ^ 2 - 1) -
            L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q) =
          L * (2 * y * z * (y ^ 2 - c ^ 2) -
            2 * varsigma * p * q * y ^ 2) := by ring
      _ = -2 * L * p * y * (z * p + varsigma * q * y) := by
        rw [hysub]
        ring
  have hswap : z * p + varsigma * q * y =
      varsigma * (y * q + varsigma * p * z) := by
    calc
      z * p + varsigma * q * y =
          varsigma ^ 2 * p * z + varsigma * q * y := by rw [hsign]; ring
      _ = varsigma * (y * q + varsigma * p * z) := by ring
  have hzcoef' :
      (L * y * z - varsigma * (L * p * q)) * (2 * z ^ 2 - 1) -
          L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q) =
        -2 * L * q * z * (y * q + varsigma * p * z) := by
    convert hzcoef using 1
    all_goals ring
  have hycoef' :
      (L * y * z - varsigma * (L * p * q)) * (2 * y ^ 2 - 1) -
          L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q) =
        -2 * L * p * y * (z * p + varsigma * q * y) := by
    convert hycoef using 1
    all_goals ring
  change
    (((L * y * z - varsigma * (L * p * q)) * (2 * z ^ 2 - 1) -
        L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q)) *
          (chebyshevU (2 * m + 1) z / (2 * z)) -
      ((L * y * z - varsigma * (L * p * q)) * (2 * y ^ 2 - 1) -
        L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q)) *
          (chebyshevU (2 * m + 1) y / (2 * y))) =
      varsigma * L * (q * y + varsigma * p * z) *
        (p * chebyshevU (2 * m + 1) y -
          varsigma * q * chebyshevU (2 * m + 1) z)
  rw [hzcoef', hycoef', hswap]
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0] at horder
    nlinarith [sq_nonneg (Real.cos θ)]
  have hy0 : y ≠ 0 := hy
  field_simp [hz0, hy0]
  have hbracket :
      -(q * chebyshevU (2 * m + 1) z) -
          -(varsigma * p * chebyshevU (2 * m + 1) y) =
        varsigma *
          (p * chebyshevU (2 * m + 1) y -
            varsigma * q * chebyshevU (2 * m + 1) z) := by
    calc
      -(q * chebyshevU (2 * m + 1) z) -
            -(varsigma * p * chebyshevU (2 * m + 1) y) =
          varsigma * p * chebyshevU (2 * m + 1) y -
            q * chebyshevU (2 * m + 1) z := by ring
      _ = varsigma * p * chebyshevU (2 * m + 1) y -
            varsigma ^ 2 * q * chebyshevU (2 * m + 1) z := by
          simp [hsign]
      _ = varsigma *
          (p * chebyshevU (2 * m + 1) y -
            varsigma * q * chebyshevU (2 * m + 1) z) := by ring
  rw [hbracket]
  ring

/-- Complete odd folded-sequence factorization in coordinate-free outer
variables. -/
theorem foldOddSequence_signed_outerChord_factorization
    (m : ℕ) {a θ z varsigma : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a))
    (horder : Real.cos θ ^ 2 < z ^ 2)
    (hsign : varsigma ^ 2 = 1) (hy : Real.cos θ ≠ 0) :
    foldOddSequence a (outerChordX a θ z)
        (varsigma * outerChordS a θ z) m =
      a ^ m *
        (varsigma * halfChordScale a *
          (outerChordRadical a z * Real.cos θ +
            varsigma * halfTrigRadical a θ * z) *
          (halfTrigRadical a θ * chebyshevU (2 * m + 1) (Real.cos θ) -
            varsigma * outerChordRadical a z * chebyshevU (2 * m + 1) z) /
          ((2 * z ^ 2 - 1) - (2 * Real.cos θ ^ 2 - 1))) := by
  have hxi := foldXi_signed_outerChord_ne ha0 hz horder hsign
  have hsum := foldXiPlus_add_foldXiMinus
    (x := outerChordX a θ z)
    (s := varsigma * outerChordS a θ z) ha0.ne'
  have hdisc : 0 ≤ foldDiscriminant a (outerChordX a θ z)
      (varsigma * outerChordS a θ z) := by
    rw [foldDiscriminant_signed_outerChord_eq a θ z varsigma hsign,
      foldDiscriminant_outerChord ha0 hz]
    positivity
  have hprod := foldXiPlus_mul_foldXiMinus
    (x := outerChordX a θ z)
    (s := varsigma * outerChordS a θ z) ha0.ne' hdisc
  rw [foldOddSequence_eq_chebyshevDividedDifference
    ha0.ne' hxi hsum hprod m]
  rw [foldOddChebyshev_numerator_signed_outerChord m ha0 hz horder hsign hy,
    foldXiPlus_signed_outerChord ha0 hz horder hsign,
    foldXiMinus_signed_outerChord ha0 hz horder hsign]

/-- The odd folded determinant vanishes exactly when the signed
coordinate-free chord equation holds. -/
theorem foldOddSequence_signed_outerChord_eq_zero_iff
    (m : ℕ) {a θ z varsigma : ℝ} (ha0 : 0 < a)
    (hz : |z| ≤ Real.cosh (pathLogParameter a))
    (horder : Real.cos θ ^ 2 < z ^ 2)
    (hsign : varsigma ^ 2 = 1) (hy : Real.cos θ ≠ 0) :
    foldOddSequence a (outerChordX a θ z)
        (varsigma * outerChordS a θ z) m = 0 ↔
      halfTrigRadical a θ * chebyshevU (2 * m + 1) (Real.cos θ) =
        varsigma * outerChordRadical a z * chebyshevU (2 * m + 1) z := by
  rw [foldOddSequence_signed_outerChord_factorization m ha0
    hz horder hsign hy]
  have haPow : a ^ m ≠ 0 := pow_ne_zero _ ha0.ne'
  have hsigma : varsigma ≠ 0 := by
    intro hs
    rw [hs] at hsign
    norm_num at hsign
  have hscale : halfChordScale a ≠ 0 := (halfChordScale_pos ha0).ne'
  have hextra := outerChord_odd_extra_factor_ne_zero hz hsign horder
  have hpref :
      varsigma * halfChordScale a *
          (outerChordRadical a z * Real.cos θ +
            varsigma * halfTrigRadical a θ * z) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hsigma hscale) hextra
  have hden : (2 * z ^ 2 - 1) - (2 * Real.cos θ ^ 2 - 1) ≠ 0 := by
    linarith
  constructor
  · intro h
    have hdiv :
        varsigma * halfChordScale a *
              (outerChordRadical a z * Real.cos θ +
                varsigma * halfTrigRadical a θ * z) *
              (halfTrigRadical a θ *
                  chebyshevU (2 * m + 1) (Real.cos θ) -
                varsigma * outerChordRadical a z *
                  chebyshevU (2 * m + 1) z) /
            ((2 * z ^ 2 - 1) - (2 * Real.cos θ ^ 2 - 1)) = 0 :=
      (mul_eq_zero.mp h).resolve_left haPow
    have hnum :
        varsigma * halfChordScale a *
              (outerChordRadical a z * Real.cos θ +
                varsigma * halfTrigRadical a θ * z) *
              (halfTrigRadical a θ *
                  chebyshevU (2 * m + 1) (Real.cos θ) -
                varsigma * outerChordRadical a z *
                  chebyshevU (2 * m + 1) z) = 0 := by
      exact ((div_eq_zero_iff.mp hdiv).resolve_right hden)
    have hres :
        halfTrigRadical a θ * chebyshevU (2 * m + 1) (Real.cos θ) -
            varsigma * outerChordRadical a z * chebyshevU (2 * m + 1) z = 0 :=
      (mul_eq_zero.mp hnum).resolve_left hpref
    exact sub_eq_zero.mp hres
  · intro hchord
    have hres :
        halfTrigRadical a θ * chebyshevU (2 * m + 1) (Real.cos θ) -
            varsigma * outerChordRadical a z * chebyshevU (2 * m + 1) z = 0 :=
      sub_eq_zero.mpr hchord
    rw [hres, mul_zero, zero_div, mul_zero]

end

end ConnectedPseudospectrum
