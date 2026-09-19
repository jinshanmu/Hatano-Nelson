import ConnectedPseudospectrum.ChordFamilyFoldedRoot
import ConnectedPseudospectrum.FoldedMinorBridge

/-!
# The endpoint-side chord family solves the actual signed pencil

This short bridge combines the actual five-minor identification with the
coordinate-free chord calculation.  Its conclusions concern the literal
determinant `signedPencilDet`, rather than an abstract transfer sequence.
-/

namespace ConnectedPseudospectrum

noncomputable section

/-- For odd `K=2m+1`, every interior chord solves the actual even-order
signed-pencil determinant. -/
theorem signedPencilDet_outerChordFamily_even_eq_zero
    (d : PositiveHalfGap) (m : ℕ) (hK : d.K = 2 * m + 1)
    (θ : d.Angle) (hleft : d.angleLower < θ)
    (hright : θ < d.angleUpper) :
    signedPencilDet (d.K - 1) d.a (outerChordFamilyX d θ)
        (outerChordFamilySignedRoot d θ) = 0 := by
  have hindex : d.K - 1 = 2 * m := by omega
  rw [hindex, signedPencilDet_even_eq_foldEvenSequence]
  exact foldEvenSequence_outerChordFamily_eq_zero d m hK θ hleft hright

/-- For even `K=2m+2`, every interior chord solves the actual odd-order
signed-pencil determinant. -/
theorem signedPencilDet_outerChordFamily_odd_eq_zero
    (d : PositiveHalfGap) (m : ℕ) (hK : d.K = 2 * m + 2)
    (θ : d.Angle) (hleft : d.angleLower < θ)
    (hright : θ < d.angleUpper) :
    signedPencilDet (d.K - 1) d.a (outerChordFamilyX d θ)
        (outerChordFamilySignedRoot d θ) = 0 := by
  have hindex : d.K - 1 = 2 * m + 1 := by omega
  rw [hindex, signedPencilDet_odd_eq_foldOddSequence]
  exact foldOddSequence_outerChordFamily_eq_zero d m hK θ hleft hright

end

end ConnectedPseudospectrum
