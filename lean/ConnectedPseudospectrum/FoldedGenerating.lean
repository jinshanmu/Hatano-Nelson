import ConnectedPseudospectrum.FoldedTransfer

/-!
# Folded determinant sequences

The even and odd sequences are the first coordinates of the signed five-minor
iteration.  Their generating functions are obtained by eliminating the other
four coordinates in `FoldedPowerSeries`.
-/

namespace ConnectedPseudospectrum

noncomputable section

/-- The scalar `ζ_s` in the numerator of the even folded generating function. -/
def foldZeta (a s : ℝ) : ℝ :=
  (1 + a ^ 2 + (1 + a) * s) / (2 * a)

/-- The signed even determinant sequence. -/
def foldEvenSequence (a x s : ℝ) (m : ℕ) : ℝ :=
  (foldSignedOrbit a x s (foldEvenSeed a) m).d

/-- The signed odd determinant sequence. -/
def foldOddSequence (a x s : ℝ) (m : ℕ) : ℝ :=
  (foldSignedOrbit a x s (foldOddSeed x s) m).d

@[simp] theorem foldEvenSequence_zero (a x s : ℝ) :
    foldEvenSequence a x s 0 = 1 := rfl

@[simp] theorem foldOddSequence_zero (a x s : ℝ) :
    foldOddSequence a x s 0 = x - s := rfl

end

end ConnectedPseudospectrum
