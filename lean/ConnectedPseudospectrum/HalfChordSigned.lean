import ConnectedPseudospectrum.HalfChordFactor

/-!
# Signed half-chord folded variables

The signed pencil evaluates the folded formulas at `s = varsigma * S`.
This module proves that `C₀`, the discriminant, and the two folded variables
are unchanged when `varsigma² = 1`.
-/

namespace ConnectedPseudospectrum

noncomputable section

theorem foldC0_signed_halfChord_eq
    (a θ η varsigma : ℝ) (hsign : varsigma ^ 2 = 1) :
    foldC0 a (halfChordX a θ η) (varsigma * halfChordS a θ η) =
      foldC0 a (halfChordX a θ η) (halfChordS a θ η) := by
  unfold foldC0
  nlinarith [sq_nonneg (halfChordS a θ η)]

theorem foldDiscriminant_signed_halfChord_eq
    (a θ η varsigma : ℝ) (hsign : varsigma ^ 2 = 1) :
    foldDiscriminant a (halfChordX a θ η)
        (varsigma * halfChordS a θ η) =
      foldDiscriminant a (halfChordX a θ η) (halfChordS a θ η) := by
  unfold foldDiscriminant
  have hsquare : (varsigma * halfChordS a θ η) ^ 2 =
      halfChordS a θ η ^ 2 := by
    rw [mul_pow, hsign, one_mul]
  rw [hsquare]

theorem foldXiPlus_signed_halfChord
    {a θ η varsigma : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a)
    (hsign : varsigma ^ 2 = 1) :
    foldXiPlus a (halfChordX a θ η) (varsigma * halfChordS a θ η) =
      2 * Real.cosh η ^ 2 - 1 := by
  unfold foldXiPlus
  rw [foldC0_signed_halfChord_eq a θ η varsigma hsign,
    foldDiscriminant_signed_halfChord_eq a θ η varsigma hsign]
  exact foldXiPlus_halfChord ha0 hη0 hηh

theorem foldXiMinus_signed_halfChord
    {a θ η varsigma : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a)
    (hsign : varsigma ^ 2 = 1) :
    foldXiMinus a (halfChordX a θ η) (varsigma * halfChordS a θ η) =
      2 * Real.cos θ ^ 2 - 1 := by
  unfold foldXiMinus
  rw [foldC0_signed_halfChord_eq a θ η varsigma hsign,
    foldDiscriminant_signed_halfChord_eq a θ η varsigma hsign]
  exact foldXiMinus_halfChord ha0 hη0 hηh

theorem foldXi_signed_halfChord_ne
    {a θ η varsigma : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a)
    (hsign : varsigma ^ 2 = 1)
    (hdistinct : Real.cosh η ^ 2 ≠ Real.cos θ ^ 2) :
    foldXiPlus a (halfChordX a θ η) (varsigma * halfChordS a θ η) ≠
      foldXiMinus a (halfChordX a θ η) (varsigma * halfChordS a θ η) := by
  rw [foldXiPlus_signed_halfChord ha0 hη0 hηh hsign,
    foldXiMinus_signed_halfChord ha0 hη0 hηh hsign]
  intro h
  apply hdistinct
  linarith

end

end ConnectedPseudospectrum
