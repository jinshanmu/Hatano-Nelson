import ConnectedPseudospectrum.FoldedChebyshev

/-!
# Explicit folded variables

This module realizes the paper's real square-root branch for `ξ₊,ξ₋` and
proves the two symmetric identities used by the folded denominator.  The
product identity is stated on the natural region where the discriminant is
nonnegative; the unordered pair is independent of the choice of sign.
-/

namespace ConnectedPseudospectrum

noncomputable section

/-- Radicand in the definition of the folded variables `ξ₊,ξ₋`. -/
def foldDiscriminant (a x s : ℝ) : ℝ :=
  ((1 + a - x) ^ 2 - s ^ 2) * ((1 + a + x) ^ 2 - s ^ 2)

/-- The plus real square-root branch of the first folded variable. -/
def foldXiPlus (a x s : ℝ) : ℝ :=
  (foldC0 a x s + Real.sqrt (foldDiscriminant a x s)) / (4 * a)

/-- The minus real square-root branch of the second folded variable. -/
def foldXiMinus (a x s : ℝ) : ℝ :=
  (foldC0 a x s - Real.sqrt (foldDiscriminant a x s)) / (4 * a)

/-- Symmetric sum identity `ξ₊+ξ₋=C₀/(2a)`, in denominator-free form. -/
theorem foldXiPlus_add_foldXiMinus
    {a x s : ℝ} (ha0 : a ≠ 0) :
    2 * a * (foldXiPlus a x s + foldXiMinus a x s) =
      foldC0 a x s := by
  rw [foldXiPlus, foldXiMinus]
  field_simp [ha0]
  ring

/-- Symmetric product identity
`a²(4ξ₊ξ₋+2)=𝔟` on the real-folded region. -/
theorem foldXiPlus_mul_foldXiMinus
    {a x s : ℝ} (ha0 : a ≠ 0)
    (hdisc : 0 ≤ foldDiscriminant a x s) :
    a ^ 2 * (4 * foldXiPlus a x s * foldXiMinus a x s + 2) =
      foldB a x s := by
  have hsqrt :
      Real.sqrt (foldDiscriminant a x s) ^ 2 = foldDiscriminant a x s :=
    Real.sq_sqrt hdisc
  rw [foldXiPlus, foldXiMinus]
  unfold foldDiscriminant at hsqrt
  unfold foldDiscriminant foldC0 foldB
  field_simp [ha0]
  nlinarith [hsqrt]

end


end ConnectedPseudospectrum
