import ConnectedPseudospectrum.HalfChordAlgebra

/-!
# Distinct-sheet half-chord factors

This module proves the nonvanishing of the additional odd-fold factor on a
distinct-variable sheet, exactly as used when reducing the signed determinant
equation to the half-chord equation.
-/

namespace ConnectedPseudospectrum

noncomputable section

theorem halfChord_odd_extra_factor_ne_zero
    {a θ η varsigma : ℝ}
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a)
    (hsign : varsigma ^ 2 = 1)
    (hdistinct : Real.cosh η ^ 2 ≠ Real.cos θ ^ 2) :
    halfHypRadical a η * Real.cos θ +
        varsigma * halfTrigRadical a θ * Real.cosh η ≠ 0 := by
  intro hzero
  have heq : halfHypRadical a η * Real.cos θ =
      -varsigma * halfTrigRadical a θ * Real.cosh η := by
    linarith
  have hsquare :
      (halfHypRadical a η * Real.cos θ) ^ 2 =
        (halfTrigRadical a θ * Real.cosh η) ^ 2 := by
    rw [heq]
    calc
      (-varsigma * halfTrigRadical a θ * Real.cosh η) ^ 2 =
          varsigma ^ 2 *
            (halfTrigRadical a θ * Real.cosh η) ^ 2 := by ring
      _ = (halfTrigRadical a θ * Real.cosh η) ^ 2 := by rw [hsign, one_mul]
  have hp := halfTrigRadical_sq a θ
  have hq := halfHypRadical_sq hη0 hηh
  rw [mul_pow, mul_pow, hp, hq] at hsquare
  have hc : 0 < Real.cosh (pathLogParameter a) ^ 2 :=
    sq_pos_of_pos (Real.cosh_pos _)
  apply hdistinct
  nlinarith

theorem foldXi_halfChord_ne_of_half_variables_ne
    {a θ η : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a)
    (hdistinct : Real.cosh η ^ 2 ≠ Real.cos θ ^ 2) :
    foldXiPlus a (halfChordX a θ η) (halfChordS a θ η) ≠
      foldXiMinus a (halfChordX a θ η) (halfChordS a θ η) := by
  rw [foldXiPlus_halfChord ha0 hη0 hηh,
    foldXiMinus_halfChord ha0 hη0 hηh]
  intro h
  apply hdistinct
  linarith

end

end ConnectedPseudospectrum
