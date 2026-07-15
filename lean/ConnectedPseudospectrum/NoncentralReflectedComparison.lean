import ConnectedPseudospectrum.NoncentralGapComparison
import ConnectedPseudospectrum.RealGapReflection

/-!
# Reflected noncentral gap comparison

This module formalizes the reflection step in lines 1925--1938 of the
immutable source.  A negative gap is defined literally as the preimage of
the corresponding positive gap under `x |-> -x`.  Its endpoints are the
negatives of the positive endpoints in reverse order.  For a matrix of order
`n`, reflection sends the descending-eigenvalue gap index `j` to `n-j`.

Thus, when `d.K = N`, the predecessor and successor matrix orders are `N-1`
and `N`; their reflected indices are `(N-1)-d.j` and `N-d.j`, respectively.
The evenness of the actual least-singular-value function then transports the
already proved positive successor-to-predecessor comparison verbatim.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- The negative real spectral gap obtained by reflecting the exact positive
gap through the origin. -/
def reflectedNegativeSpectralGap (d : PositiveHalfGap) : Set Real :=
  (fun x : Real => -x) ⁻¹' positiveHalfSpectralGap d

@[simp] theorem mem_reflectedNegativeSpectralGap
    (d : PositiveHalfGap) (x : Real) :
    x ∈ reflectedNegativeSpectralGap d ↔
      -x ∈ positiveHalfSpectralGap d := by
  rfl

/-- Reflection can equivalently be expressed as the image of the positive
gap, since negation is an involution. -/
theorem reflectedNegativeSpectralGap_eq_neg_image
    (d : PositiveHalfGap) :
    reflectedNegativeSpectralGap d =
      (fun x : Real => -x) '' positiveHalfSpectralGap d := by
  ext x
  constructor
  · intro hx
    change -x ∈ positiveHalfSpectralGap d at hx
    exact ⟨-x, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    change - -y ∈ positiveHalfSpectralGap d
    simpa using hy

/-- The reflected negative gap has the two negated spectral endpoints in
reverse order. -/
theorem reflectedNegativeSpectralGap_eq_Ioo
    (d : PositiveHalfGap) :
    reflectedNegativeSpectralGap d =
      Ioo (-positiveHalfGapUpper d) (-positiveHalfGapLower d) := by
  ext x
  change
    (positiveHalfGapLower d < -x /\
      -x < positiveHalfGapUpper d) ↔
    (-positiveHalfGapUpper d < x /\
      x < -positiveHalfGapLower d)
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor <;> linarith
  · rintro ⟨hlower, hupper⟩
    constructor <;> linarith

/-- For a positive-half gap of a matrix of order `d.K-1`, the reflected
descending-eigenvalue gap index is `(d.K-1)-d.j`. -/
def reflectedNegativeGapIndex (d : PositiveHalfGap) : Nat :=
  (d.K - 1) - d.j

/-- The reflected index is nonzero, so it is a genuine interior gap index. -/
theorem reflectedNegativeGapIndex_pos (d : PositiveHalfGap) :
    0 < reflectedNegativeGapIndex d := by
  have hjUpper := d.hjUpper
  unfold reflectedNegativeGapIndex
  omega

/-- The reflected index is strictly below the matrix order. -/
theorem reflectedNegativeGapIndex_lt_matrixOrder (d : PositiveHalfGap) :
    reflectedNegativeGapIndex d < d.K - 1 := by
  have hK := d.hK
  have hj := d.hj
  have hjUpper := d.hjUpper
  unfold reflectedNegativeGapIndex
  omega

/-- Exact predecessor/successor reflected-index map.  The positive index is
unchanged by `successor`, while the reflected negative index increases by
one because the matrix order increases by one. -/
theorem reflectedNegativeGapIndex_predecessor_successor
    (d : PositiveHalfGap) :
    reflectedNegativeGapIndex d = (d.K - 1) - d.j /\
      reflectedNegativeGapIndex d.successor = d.K - d.j := by
  constructor
  · rfl
  · simp only [reflectedNegativeGapIndex,
      PositiveHalfGap.successor_K, PositiveHalfGap.successor_j]
    omega

/-- Actual noncentral negative-gap comparison.  Every point of the reflected
successor gap has a point in the reflected same-origin predecessor gap whose
genuine Euclidean least singular value is strictly larger. -/
theorem exists_predecessorReflectedGapPoint_strict_of_mem_successorGap
    (d : PositiveHalfGap) {x : Real}
    (hx : x ∈ reflectedNegativeSpectralGap d.successor) :
    ∃ xhat : Real,
      xhat ∈ reflectedNegativeSpectralGap d /\
      realGapValue d.K d.a x < realGapValue (d.K - 1) d.a xhat := by
  have hxPositive : -x ∈ positiveHalfSpectralGap d.successor :=
    (mem_reflectedNegativeSpectralGap d.successor x).mp hx
  obtain ⟨yhat, hyhat, hstrict⟩ :=
    exists_predecessorGapPoint_strict_of_mem_successorGap d hxPositive
  refine ⟨-yhat, ?_, ?_⟩
  · exact (mem_reflectedNegativeSpectralGap d (-yhat)).2
      (by simpa using hyhat)
  · simpa only [realGapValue_neg] using hstrict

end

end ConnectedPseudospectrum
