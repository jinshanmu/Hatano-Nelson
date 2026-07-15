import ConnectedPseudospectrum.Conjugation
import ConnectedPseudospectrum.VerticalTopology

/-!
# From upper-half-plane monotonicity to vertical scaling

The determinant proof of `lem:vertical` is naturally stated for nonnegative
imaginary coordinates.  Conjugation symmetry extends it to every vertical
fibre and supplies exactly the scaling-closure premise used by the topology
modules.
-/

namespace ConnectedPseudospectrum

open Set
open scoped ComplexConjugate

noncomputable section

/-- A complex point with prescribed real and imaginary coordinates. -/
def verticalPoint (x y : ℝ) : ℂ :=
  (x : ℂ) + (y : ℝ) * Complex.I

@[simp] theorem verticalPoint_re (x y : ℝ) : (verticalPoint x y).re = x := by
  simp [verticalPoint]

@[simp] theorem verticalPoint_im (x y : ℝ) : (verticalPoint x y).im = y := by
  simp [verticalPoint]

/-- The exact monotonicity statement proved by `lem:vertical` on the upper
half-plane. -/
def UpperVerticalHeightMonotone (n : ℕ) (a : ℝ) : Prop :=
  ∀ x : ℝ, ∀ ⦃y₁ y₂ : ℝ⦄, 0 ≤ y₁ → y₁ ≤ y₂ →
    pseudospectralHeight n a (verticalPoint x y₁) ≤
      pseudospectralHeight n a (verticalPoint x y₂)

theorem conj_verticalScale (s : ℝ) (z : ℂ) :
    conj (verticalScale s z) = verticalPoint z.re (s * (-z.im)) := by
  apply Complex.ext <;> simp [verticalScale, verticalPoint]

theorem conj_eq_verticalPoint (z : ℂ) :
    conj z = verticalPoint z.re (-z.im) := by
  apply Complex.ext <;> simp [verticalPoint]

/-- Upper-half-plane monotonicity, together with the already proved real
conjugation symmetry, makes every strict pseudospectrum vertically
scaling-closed. -/
theorem verticalScalingClosed_pseudospectrum_of_upperMonotone
    (n : ℕ) (a ε : ℝ) (hmono : UpperVerticalHeightMonotone n a) :
    VerticalScalingClosed (pseudospectrum n a ε) := by
  intro z hz s hs
  change pseudospectralHeight n a (verticalScale s z) < ε
  have hzheight : pseudospectralHeight n a z < ε := hz
  apply (show pseudospectralHeight n a (verticalScale s z) ≤
      pseudospectralHeight n a z from ?_).trans_lt hzheight
  by_cases hy : 0 ≤ z.im
  · have hsy : 0 ≤ s * z.im := mul_nonneg hs.1 hy
    have hsyle : s * z.im ≤ z.im := by
      nlinarith [hs.2, hy]
    simpa [verticalScale, verticalPoint] using
      hmono z.re hsy hsyle
  · have hyneg : z.im < 0 := lt_of_not_ge hy
    have hsy : 0 ≤ s * (-z.im) :=
      mul_nonneg hs.1 (neg_nonneg.mpr hyneg.le)
    have hsyle : s * (-z.im) ≤ -z.im := by
      nlinarith [hs.2, hyneg]
    have hupper := hmono z.re hsy hsyle
    calc
      pseudospectralHeight n a (verticalScale s z) =
          pseudospectralHeight n a (conj (verticalScale s z)) := by
            rw [pseudospectralHeight_conj]
      _ = pseudospectralHeight n a (verticalPoint z.re (s * (-z.im))) := by
            rw [conj_verticalScale]
      _ ≤ pseudospectralHeight n a (verticalPoint z.re (-z.im)) := hupper
      _ = pseudospectralHeight n a (conj z) := by rw [conj_eq_verticalPoint]
      _ = pseudospectralHeight n a z := pseudospectralHeight_conj n a z

end

end ConnectedPseudospectrum
