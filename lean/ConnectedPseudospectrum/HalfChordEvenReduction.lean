import ConnectedPseudospectrum.HalfChordSigned

/-!
# Even folded determinant reduction to the signed half-chord equation

For `K = 2m+1`, this module substitutes the exact half variables into the
even Chebyshev divided difference, factors every nonzero sheet factor, and
proves that the actual folded transfer sequence vanishes exactly when the
paper's signed half-chord equation holds.
-/

namespace ConnectedPseudospectrum

noncomputable section

theorem halfChord_even_prefactor_ne_zero
    {a θ η varsigma : ℝ}
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a)
    (hsign : varsigma ^ 2 = 1)
    (hdistinct : Real.cosh η ^ 2 ≠ Real.cos θ ^ 2) :
    halfTrigRadical a θ + varsigma * halfHypRadical a η ≠ 0 := by
  have hp0 : 0 ≤ halfTrigRadical a θ := Real.sqrt_nonneg _
  have hq0 : 0 ≤ halfHypRadical a η := Real.sqrt_nonneg _
  have hp := halfTrigRadical_sq a θ
  have hq := halfHypRadical_sq hη0 hηh
  have hfactor : (varsigma - 1) * (varsigma + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hplus | hminus
  · have hs : varsigma = 1 := by linarith
    rw [hs]
    intro hzero
    have hpzero : halfTrigRadical a θ = 0 := by linarith
    have hqzero : halfHypRadical a η = 0 := by linarith
    apply hdistinct
    nlinarith
  · have hs : varsigma = -1 := by linarith
    rw [hs]
    intro hzero
    apply hdistinct
    nlinarith [hp, hq]

theorem foldEvenChebyshev_numerator_signed_halfChord
    (m : ℕ) {a θ η varsigma : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a)
    (hsign : varsigma ^ 2 = 1) :
    foldEvenChebyshevFunction m
          (foldXiPlus a (halfChordX a θ η)
            (varsigma * halfChordS a θ η))
          (foldZeta a (varsigma * halfChordS a θ η)) -
        foldEvenChebyshevFunction m
          (foldXiMinus a (halfChordX a θ η)
            (varsigma * halfChordS a θ η))
          (foldZeta a (varsigma * halfChordS a θ η)) =
      2 * (halfTrigRadical a θ + varsigma * halfHypRadical a η) *
        (halfTrigRadical a θ * chebyshevU (2 * m) (Real.cos θ) -
          varsigma * halfHypRadical a η *
            chebyshevU (2 * m) (Real.cosh η)) := by
  rw [foldXiPlus_signed_halfChord ha0 hη0 hηh hsign,
    foldXiMinus_signed_halfChord ha0 hη0 hηh hsign,
    foldZeta_signed_halfChord ha0]
  unfold foldEvenChebyshevFunction
  rw [chebyshevU_half_angle_even_index m (Real.cosh η),
    chebyshevU_half_angle_even_index m (Real.cos θ)]
  have hp := halfTrigRadical_sq a θ
  have hq := halfHypRadical_sq hη0 hηh
  have hz :
      (2 * Real.cosh η ^ 2 - 1 -
          (2 * Real.cosh (pathLogParameter a) ^ 2 - 1 +
            2 * varsigma * halfTrigRadical a θ * halfHypRadical a η)) =
        -2 * halfHypRadical a η *
          (halfHypRadical a η + varsigma * halfTrigRadical a θ) := by
    nlinarith
  have hy :
      (2 * Real.cos θ ^ 2 - 1 -
          (2 * Real.cosh (pathLogParameter a) ^ 2 - 1 +
            2 * varsigma * halfTrigRadical a θ * halfHypRadical a η)) =
        -2 * halfTrigRadical a θ *
          (halfTrigRadical a θ + varsigma * halfHypRadical a η) := by
    nlinarith
  have hswap :
      halfHypRadical a η + varsigma * halfTrigRadical a θ =
        varsigma *
          (halfTrigRadical a θ + varsigma * halfHypRadical a η) := by
    calc
      halfHypRadical a η + varsigma * halfTrigRadical a θ =
          varsigma * halfTrigRadical a θ +
            varsigma ^ 2 * halfHypRadical a η := by rw [hsign]; ring
      _ = varsigma *
          (halfTrigRadical a θ + varsigma * halfHypRadical a η) := by ring
  rw [hz, hy, hswap]
  ring

theorem foldEvenSequence_signed_halfChord_factorization
    (m : ℕ) {a θ η varsigma : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a)
    (hsign : varsigma ^ 2 = 1)
    (hdistinct : Real.cosh η ^ 2 ≠ Real.cos θ ^ 2) :
    foldEvenSequence a (halfChordX a θ η)
        (varsigma * halfChordS a θ η) m =
      a ^ m *
        (2 * (halfTrigRadical a θ + varsigma * halfHypRadical a η) *
          (halfTrigRadical a θ * chebyshevU (2 * m) (Real.cos θ) -
            varsigma * halfHypRadical a η *
              chebyshevU (2 * m) (Real.cosh η)) /
          ((2 * Real.cosh η ^ 2 - 1) -
            (2 * Real.cos θ ^ 2 - 1))) := by
  have hxi := foldXi_signed_halfChord_ne ha0 hη0 hηh hsign hdistinct
  have hsum := foldXiPlus_add_foldXiMinus
    (x := halfChordX a θ η)
    (s := varsigma * halfChordS a θ η) ha0.ne'
  have hdisc : 0 ≤ foldDiscriminant a (halfChordX a θ η)
      (varsigma * halfChordS a θ η) := by
    rw [foldDiscriminant_signed_halfChord_eq a θ η varsigma hsign,
      foldDiscriminant_halfChord ha0 hη0 hηh]
    positivity
  have hprod := foldXiPlus_mul_foldXiMinus
    (x := halfChordX a θ η)
    (s := varsigma * halfChordS a θ η) ha0.ne' hdisc
  rw [foldEvenSequence_eq_chebyshevDividedDifference
    ha0.ne' hxi hsum hprod]
  rw [foldEvenChebyshev_numerator_signed_halfChord m ha0 hη0 hηh hsign,
    foldXiPlus_signed_halfChord ha0 hη0 hηh hsign,
    foldXiMinus_signed_halfChord ha0 hη0 hηh hsign]

theorem foldEvenSequence_signed_halfChord_eq_zero_iff
    (m : ℕ) {a θ η varsigma : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a)
    (hsign : varsigma ^ 2 = 1)
    (hdistinct : Real.cosh η ^ 2 ≠ Real.cos θ ^ 2) :
    foldEvenSequence a (halfChordX a θ η)
        (varsigma * halfChordS a θ η) m = 0 ↔
      halfTrigRadical a θ * chebyshevU (2 * m) (Real.cos θ) =
        varsigma * halfHypRadical a η *
          chebyshevU (2 * m) (Real.cosh η) := by
  rw [foldEvenSequence_signed_halfChord_factorization m ha0
    hη0 hηh hsign hdistinct]
  have haPow : a ^ m ≠ 0 := pow_ne_zero _ ha0.ne'
  have hpref := halfChord_even_prefactor_ne_zero
    hη0 hηh hsign hdistinct
  have hden :
      (2 * Real.cosh η ^ 2 - 1) - (2 * Real.cos θ ^ 2 - 1) ≠ 0 := by
    intro h
    apply hdistinct
    linarith
  have hden' : 2 * Real.cosh η ^ 2 - 2 * Real.cos θ ^ 2 ≠ 0 := by
    intro h
    apply hdistinct
    linarith
  constructor
  · intro h
    have hdiv :
        2 * (halfTrigRadical a θ + varsigma * halfHypRadical a η) *
              (halfTrigRadical a θ * chebyshevU (2 * m) (Real.cos θ) -
                varsigma * halfHypRadical a η *
                  chebyshevU (2 * m) (Real.cosh η)) /
            ((2 * Real.cosh η ^ 2 - 1) - (2 * Real.cos θ ^ 2 - 1)) = 0 :=
      (mul_eq_zero.mp h).resolve_left haPow
    have hnum :
        2 * (halfTrigRadical a θ + varsigma * halfHypRadical a η) *
          (halfTrigRadical a θ * chebyshevU (2 * m) (Real.cos θ) -
            varsigma * halfHypRadical a η *
              chebyshevU (2 * m) (Real.cosh η)) = 0 := by
      simpa [hden, hden'] using hdiv
    have hres :
        halfTrigRadical a θ * chebyshevU (2 * m) (Real.cos θ) -
          varsigma * halfHypRadical a η *
            chebyshevU (2 * m) (Real.cosh η) = 0 := by
      rcases mul_eq_zero.mp hnum with htwoPref | hres
      · rcases mul_eq_zero.mp htwoPref with htwo | hp
        · norm_num at htwo
        · exact (hpref hp).elim
      · exact hres
    linarith
  · intro hchord
    have hres :
        halfTrigRadical a θ * chebyshevU (2 * m) (Real.cos θ) -
          varsigma * halfHypRadical a η *
            chebyshevU (2 * m) (Real.cosh η) = 0 := by linarith
    rw [hres, mul_zero, zero_div, mul_zero]

end

end ConnectedPseudospectrum
