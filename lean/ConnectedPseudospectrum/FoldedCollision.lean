import ConnectedPseudospectrum.FoldedVariables
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Folded-variable noncollision formulas and collision limits

This module specializes the even and odd Chebyshev divided differences to
the paper's explicit real folded variables whenever their discriminant is
positive.  It also proves that both divided differences converge to the
derivative prescribed at a collision.
-/

namespace ConnectedPseudospectrum

open Filter Topology
open scoped Topology

noncomputable section

/-- A positive folded discriminant makes the two real square-root branches
distinct. -/
theorem foldXiPlus_ne_foldXiMinus_of_pos
    {a x s : ℝ} (ha0 : a ≠ 0)
    (hdisc : 0 < foldDiscriminant a x s) :
    foldXiPlus a x s ≠ foldXiMinus a x s := by
  intro h
  have hsqrt : 0 < Real.sqrt (foldDiscriminant a x s) :=
    Real.sqrt_pos.2 hdisc
  unfold foldXiPlus foldXiMinus at h
  field_simp [ha0] at h
  linarith

/-- The even folded sequence is the paper's explicit Chebyshev divided
difference on the positive-discriminant region. -/
theorem foldEvenSequence_eq_explicitFoldXi
    {a x s : ℝ} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hdisc : 0 < foldDiscriminant a x s) (m : ℕ) :
    foldEvenSequence a x s m =
      a ^ m *
        ((foldEvenChebyshevFunction m (foldXiPlus a x s) (foldZeta a s) -
          foldEvenChebyshevFunction m (foldXiMinus a x s) (foldZeta a s)) /
            (foldXiPlus a x s - foldXiMinus a x s)) := by
  apply foldEvenSequence_eq_chebyshevDividedDifference ha0 ha1
    (foldXiPlus_ne_foldXiMinus_of_pos ha0 hdisc)
    (foldXiPlus_add_foldXiMinus ha0)
  exact foldXiPlus_mul_foldXiMinus ha0 hdisc.le

/-- The odd folded sequence is the paper's explicit Chebyshev divided
difference on the positive-discriminant region. -/
theorem foldOddSequence_eq_explicitFoldXi
    {a x s : ℝ} (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hdisc : 0 < foldDiscriminant a x s) (m : ℕ) :
    foldOddSequence a x s m =
      a ^ m *
        ((foldOddChebyshevFunction m x s (foldOddBeta a x s)
            (foldXiPlus a x s) -
          foldOddChebyshevFunction m x s (foldOddBeta a x s)
            (foldXiMinus a x s)) /
            (foldXiPlus a x s - foldXiMinus a x s)) := by
  apply foldOddSequence_eq_chebyshevDividedDifference ha0 ha1
    (foldXiPlus_ne_foldXiMinus_of_pos ha0 hdisc)
    (foldXiPlus_add_foldXiMinus ha0)
  exact foldXiPlus_mul_foldXiMinus ha0 hdisc.le

/-- The numerator function in the even divided difference is differentiable
at every real folded variable. -/
theorem differentiableAt_foldEvenChebyshevFunction
    (m : ℕ) (u zeta : ℝ) :
    DifferentiableAt ℝ (fun v => foldEvenChebyshevFunction m v zeta) u := by
  unfold foldEvenChebyshevFunction chebyshevU
  fun_prop

/-- The even divided difference has the derivative value prescribed by the
paper when its two folded variables collide. -/
theorem tendsto_foldEvenChebyshev_dividedDifference
    (m : ℕ) (u zeta : ℝ) :
    Tendsto (fun v =>
      (foldEvenChebyshevFunction m u zeta -
        foldEvenChebyshevFunction m v zeta) / (u - v))
      (𝓝[≠] u)
      (𝓝 (deriv (fun w => foldEvenChebyshevFunction m w zeta) u)) := by
  have h :=
    (differentiableAt_foldEvenChebyshevFunction m u zeta).hasDerivAt.tendsto_slope
  convert h using 1
  funext v
  rw [slope_def_module]
  simp only [smul_eq_mul, div_eq_mul_inv]
  rw [show v - u = -(u - v) by ring, inv_neg]
  ring

/-- The numerator function in the odd divided difference is differentiable
at every real folded variable. -/
theorem differentiableAt_foldOddChebyshevFunction
    (m : ℕ) (x s beta u : ℝ) :
    DifferentiableAt ℝ (fun v => foldOddChebyshevFunction m x s beta v) u := by
  unfold foldOddChebyshevFunction chebyshevU
  fun_prop

/-- The odd divided difference has the derivative value prescribed by the
paper when its two folded variables collide. -/
theorem tendsto_foldOddChebyshev_dividedDifference
    (m : ℕ) (x s beta u : ℝ) :
    Tendsto (fun v =>
      (foldOddChebyshevFunction m x s beta u -
        foldOddChebyshevFunction m x s beta v) / (u - v))
      (𝓝[≠] u)
      (𝓝 (deriv (fun w => foldOddChebyshevFunction m x s beta w) u)) := by
  have h :=
    (differentiableAt_foldOddChebyshevFunction m x s beta u).hasDerivAt.tendsto_slope
  convert h using 1
  funext v
  rw [slope_def_module]
  simp only [smul_eq_mul, div_eq_mul_inv]
  rw [show v - u = -(u - v) by ring, inv_neg]
  ring

end

end ConnectedPseudospectrum
