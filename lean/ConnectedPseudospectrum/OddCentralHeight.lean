import ConnectedPseudospectrum.OddCentralUpperComparison
import ConnectedPseudospectrum.RealGapReflection

/-!
# The actual height of the two central gaps in odd dimension

For matrix order `2m+1`, the source defines `d_m` as the maximum of the
actual Euclidean least singular value on the closed positive central gap

`[0, 2 * sqrt(a) * sin (pi / (2m+2))]`.

This module gives that definition literally, proves that the maximum is
attained in the open gap and is positive, and transports it to the negative
central gap by the exact reflection identity for `realGapValue`.  The final
theorem is the strict upper half of `eq:central-interlace`, namely `d_m<c_m`.
-/

namespace ConnectedPseudospectrum

open Set
open OddCentralChordData

noncomputable section

/-- The positive nonzero endpoint of either zero-adjacent spectral gap for
the odd matrix of order `2m+1`. -/
def oddCentralEndpoint (m : Nat) (a : Real) : Real :=
  2 * Real.sqrt a *
    Real.sin (Real.pi / (((2 * m + 2 : Nat) : Real)))

/-- The closed positive zero-adjacent spectral gap used in the definition of
the source's `d_m`. -/
def oddCentralInterval (m : Nat) (a : Real) : Set Real :=
  Icc 0 (oddCentralEndpoint m a)

/-- The reflected closed zero-adjacent spectral gap. -/
def oddNegativeCentralInterval (m : Nat) (a : Real) : Set Real :=
  Icc (-oddCentralEndpoint m a) 0

/-- The union of the two closed zero-adjacent gaps is the symmetric interval
between the first negative and positive eigenvalues. -/
def oddCentralDoubleInterval (m : Nat) (a : Real) : Set Real :=
  Icc (-oddCentralEndpoint m a) (oddCentralEndpoint m a)

/-- The source's literal odd central-gap height `d_m`, defined using the
actual finite-dimensional complex Euclidean least singular value. -/
def oddCentralHeight (m : Nat) (a : Real) : Real :=
  sSup
    (realGapValue (2 * m + 1) a '' oddCentralInterval m a)

/-- The explicit endpoint agrees with the upper endpoint of the specialized
positive-half spectral gap. -/
theorem positiveGap_upperEndpoint_eq_oddCentralEndpoint
    (d : OddCentralChordData) :
    positiveHalfGapUpper d.positiveGap =
      oddCentralEndpoint d.m d.a := by
  simpa only [oddCentralEndpoint] using positiveGap_upperEndpoint d

/-- Under the paper's assumptions, the first positive odd-order eigenvalue
is strictly positive. -/
theorem oddCentralEndpoint_pos (d : OddCentralChordData) :
    0 < oddCentralEndpoint d.m d.a := by
  have hgap :=
    positiveHalfGapLower_lt_positiveHalfGapUpper d.positiveGap
  rw [positiveGap_lowerEndpoint, positiveGap_upperEndpoint] at hgap
  simpa only [oddCentralEndpoint] using hgap

/-- Zero belongs to the closed positive central interval. -/
theorem zero_mem_oddCentralInterval (d : OddCentralChordData) :
    0 ∈ oddCentralInterval d.m d.a := by
  unfold oddCentralInterval
  exact ⟨le_rfl, (oddCentralEndpoint_pos d).le⟩

/-- The image whose supremum defines `oddCentralHeight` is compact. -/
theorem compact_oddCentralRange (m : Nat) (a : Real) :
    IsCompact
      (realGapValue (2 * m + 1) a '' oddCentralInterval m a) := by
  unfold oddCentralInterval
  exact isCompact_Icc.image
    (continuous_realGapValue (2 * m + 1) a)

/-- Under the paper's assumptions, the compact image defining the odd
central height is nonempty. -/
theorem nonempty_oddCentralRange (d : OddCentralChordData) :
    (realGapValue (2 * d.m + 1) d.a ''
      oddCentralInterval d.m d.a).Nonempty :=
  ⟨realGapValue (2 * d.m + 1) d.a 0, 0,
    zero_mem_oddCentralInterval d, rfl⟩

/-- The supremum in the definition of `oddCentralHeight` is attained. -/
theorem exists_realGapValue_eq_oddCentralHeight
    (d : OddCentralChordData) :
    ∃ x ∈ oddCentralInterval d.m d.a,
      realGapValue (2 * d.m + 1) d.a x =
        oddCentralHeight d.m d.a := by
  have hcompact := compact_oddCentralRange d.m d.a
  have hnonempty := nonempty_oddCentralRange d
  have hmem :
      oddCentralHeight d.m d.a ∈
        realGapValue (2 * d.m + 1) d.a ''
          oddCentralInterval d.m d.a := by
    exact hcompact.isClosed.csSup_mem hnonempty
      hcompact.isBounded.bddAbove
  exact hmem

/-- Every actual least-singular-value height on the positive closed central
gap is bounded by `oddCentralHeight`. -/
theorem realGapValue_le_oddCentralHeight
    (m : Nat) (a x : Real) (hx : x ∈ oddCentralInterval m a) :
    realGapValue (2 * m + 1) a x ≤ oddCentralHeight m a := by
  apply le_csSup (compact_oddCentralRange m a).isBounded.bddAbove
  exact ⟨x, hx, rfl⟩

private theorem selectedMiddleHeight_eq_zero_of_root_eq_zero
    (e : PositiveHalfGap) (x : Real)
    (hroot : selectedMiddleRoot e x = 0) :
    selectedMiddleHeight e x = 0 := by
  have hproduct :
      (-1 : Real) ^ e.j * selectedMiddleHeight e x = 0 := by
    calc
      (-1 : Real) ^ e.j * selectedMiddleHeight e x =
          selectedMiddleRoot e x :=
        (selectedMiddleRoot_eq_negOnePow_mul_height e x).symm
      _ = 0 := hroot
  exact (mul_eq_zero.mp hproduct).resolve_left
    (pow_ne_zero e.j (by norm_num))

/-- The actual height at the central eigenvalue zero vanishes. -/
theorem realGapValue_oddCentral_zero_eq_zero
    (d : OddCentralChordData) :
    realGapValue (2 * d.m + 1) d.a 0 = 0 := by
  have hheight := selectedMiddleHeight_eq_zero_of_root_eq_zero
    d.positiveGap (positiveHalfGapLower d.positiveGap)
    (selectedMiddleRoot_positiveHalfGapLower_eq_zero d.positiveGap)
  simpa only [selectedMiddleHeight, positiveGap_matrixOrder,
    positiveGap_a, positiveGap_lowerEndpoint] using hheight

/-- The actual height at the first positive eigenvalue vanishes. -/
theorem realGapValue_oddCentralEndpoint_eq_zero
    (d : OddCentralChordData) :
    realGapValue (2 * d.m + 1) d.a
      (oddCentralEndpoint d.m d.a) = 0 := by
  have hheight := selectedMiddleHeight_eq_zero_of_root_eq_zero
    d.positiveGap (positiveHalfGapUpper d.positiveGap)
    (selectedMiddleRoot_positiveHalfGapUpper_eq_zero d.positiveGap)
  simpa only [selectedMiddleHeight, positiveGap_matrixOrder,
    positiveGap_a, positiveGap_upperEndpoint,
    oddCentralEndpoint] using hheight

/-- By reflection, the actual height also vanishes at the first negative
eigenvalue. -/
theorem realGapValue_neg_oddCentralEndpoint_eq_zero
    (d : OddCentralChordData) :
    realGapValue (2 * d.m + 1) d.a
      (-oddCentralEndpoint d.m d.a) = 0 := by
  calc
    realGapValue (2 * d.m + 1) d.a
        (-oddCentralEndpoint d.m d.a) =
        realGapValue (2 * d.m + 1) d.a
          (oddCentralEndpoint d.m d.a) :=
      realGapValue_neg (2 * d.m + 1) d.a
        (oddCentralEndpoint d.m d.a)
    _ = 0 := realGapValue_oddCentralEndpoint_eq_zero d

/-- A fixed interior test point in the positive odd central gap. -/
def oddCentralMidpoint (m : Nat) (a : Real) : Real :=
  oddCentralEndpoint m a / 2

/-- The chosen midpoint lies strictly inside the positive central gap. -/
theorem oddCentralMidpoint_mem_Ioo (d : OddCentralChordData) :
    oddCentralMidpoint d.m d.a ∈
      Ioo 0 (oddCentralEndpoint d.m d.a) := by
  unfold oddCentralMidpoint
  constructor <;> linarith [oddCentralEndpoint_pos d]

/-- The actual least singular value is positive at the chosen interior
central-gap point. -/
theorem realGapValue_oddCentralMidpoint_pos
    (d : OddCentralChordData) :
    0 < realGapValue (2 * d.m + 1) d.a
      (oddCentralMidpoint d.m d.a) := by
  have hxgap :
      oddCentralMidpoint d.m d.a ∈
        positiveHalfSpectralGap d.positiveGap := by
    rw [positiveHalfSpectralGap_positiveGap]
    simpa only [oddCentralEndpoint] using
      oddCentralMidpoint_mem_Ioo d
  simpa only [selectedMiddleHeight, positiveGap_matrixOrder,
    positiveGap_a] using
      selectedMiddleHeight_pos_of_mem_gap d.positiveGap hxgap

/-- The chosen midpoint also belongs to the closed interval defining the
maximum. -/
theorem oddCentralMidpoint_mem_interval
    (d : OddCentralChordData) :
    oddCentralMidpoint d.m d.a ∈
      oddCentralInterval d.m d.a := by
  unfold oddCentralInterval
  have hmid := oddCentralMidpoint_mem_Ioo d
  exact ⟨hmid.1.le, hmid.2.le⟩

/-- The compact maximum `oddCentralHeight` is strictly positive. -/
theorem oddCentralHeight_pos (d : OddCentralChordData) :
    0 < oddCentralHeight d.m d.a := by
  exact (realGapValue_oddCentralMidpoint_pos d).trans_le
    (realGapValue_le_oddCentralHeight d.m d.a
      (oddCentralMidpoint d.m d.a)
      (oddCentralMidpoint_mem_interval d))

/-- Since both endpoint heights vanish while the maximum is positive, an
actual maximizer lies in the open positive central gap. -/
theorem exists_interior_realGapValue_eq_oddCentralHeight
    (d : OddCentralChordData) :
    ∃ x ∈ Ioo 0 (oddCentralEndpoint d.m d.a),
      realGapValue (2 * d.m + 1) d.a x =
        oddCentralHeight d.m d.a := by
  obtain ⟨x, hx, hvalue⟩ :=
    exists_realGapValue_eq_oddCentralHeight d
  have hxIcc : x ∈ Icc 0 (oddCentralEndpoint d.m d.a) := by
    simpa only [oddCentralInterval] using hx
  have hxvaluePos :
      0 < realGapValue (2 * d.m + 1) d.a x := by
    rw [hvalue]
    exact oddCentralHeight_pos d
  have hxneZero : x ≠ 0 := by
    intro hxzero
    rw [hxzero, realGapValue_oddCentral_zero_eq_zero d] at hxvaluePos
    exact (lt_irrefl 0) hxvaluePos
  have hxneUpper : x ≠ oddCentralEndpoint d.m d.a := by
    intro hxupper
    rw [hxupper, realGapValue_oddCentralEndpoint_eq_zero d] at hxvaluePos
    exact (lt_irrefl 0) hxvaluePos
  exact ⟨x,
    ⟨lt_of_le_of_ne hxIcc.1 (Ne.symm hxneZero),
      lt_of_le_of_ne hxIcc.2 hxneUpper⟩,
    hvalue⟩

/-- Reflection transfers the positive closed-gap bound to the negative
zero-adjacent gap. -/
theorem realGapValue_le_oddCentralHeight_of_mem_negative
    (d : OddCentralChordData) {x : Real}
    (hx : x ∈ oddNegativeCentralInterval d.m d.a) :
    realGapValue (2 * d.m + 1) d.a x ≤
      oddCentralHeight d.m d.a := by
  have hxIcc :
      x ∈ Icc (-oddCentralEndpoint d.m d.a) 0 := by
    simpa only [oddNegativeCentralInterval] using hx
  have hneg : -x ∈ oddCentralInterval d.m d.a := by
    unfold oddCentralInterval
    constructor <;> linarith [hxIcc.1, hxIcc.2]
  calc
    realGapValue (2 * d.m + 1) d.a x =
        realGapValue (2 * d.m + 1) d.a (-x) :=
      (realGapValue_neg (2 * d.m + 1) d.a x).symm
    _ ≤ oddCentralHeight d.m d.a :=
      realGapValue_le_oddCentralHeight d.m d.a (-x) hneg

/-- A reflected interior maximizer shows that the negative central gap has
exactly the same height `oddCentralHeight`. -/
theorem exists_negative_interior_realGapValue_eq_oddCentralHeight
    (d : OddCentralChordData) :
    ∃ x ∈ Ioo (-oddCentralEndpoint d.m d.a) 0,
      realGapValue (2 * d.m + 1) d.a x =
        oddCentralHeight d.m d.a := by
  obtain ⟨x, hx, hvalue⟩ :=
    exists_interior_realGapValue_eq_oddCentralHeight d
  refine ⟨-x, ?_, ?_⟩
  · exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  · rw [realGapValue_neg, hvalue]

/-- On the entire symmetric interval formed by the two closed central gaps,
the actual real-axis height is bounded by `oddCentralHeight`. -/
theorem realGapValue_le_oddCentralHeight_of_mem_doubleInterval
    (d : OddCentralChordData) {x : Real}
    (hx : x ∈ oddCentralDoubleInterval d.m d.a) :
    realGapValue (2 * d.m + 1) d.a x ≤
      oddCentralHeight d.m d.a := by
  have hxIcc :
      x ∈ Icc (-oddCentralEndpoint d.m d.a)
        (oddCentralEndpoint d.m d.a) := by
    simpa only [oddCentralDoubleInterval] using hx
  by_cases hxnonneg : 0 ≤ x
  · apply realGapValue_le_oddCentralHeight d.m d.a x
    exact ⟨hxnonneg, hxIcc.2⟩
  · apply realGapValue_le_oddCentralHeight_of_mem_negative d
    unfold oddNegativeCentralInterval
    exact ⟨hxIcc.1, le_of_not_ge hxnonneg⟩

/-- Explicit-interval wrapper for the strict upper comparison throughout the
positive open central gap. -/
theorem realGapValue_lt_centralBidiagonalHeight_of_mem_positiveOddCentralGap
    (d : OddCentralChordData) {x : Real}
    (hx : x ∈ Ioo 0 (oddCentralEndpoint d.m d.a)) :
    realGapValue (2 * d.m + 1) d.a x <
      centralBidiagonalHeight d.m d.a := by
  apply realGapValue_lt_centralBidiagonalHeight_of_mem_positiveCentralGap d
  rw [positiveHalfSpectralGap_positiveGap]
  simpa only [oddCentralEndpoint] using hx

/-- Reflection gives the same strict upper comparison on the negative open
central gap. -/
theorem realGapValue_lt_centralBidiagonalHeight_of_mem_negativeOddCentralGap
    (d : OddCentralChordData) {x : Real}
    (hx : x ∈ Ioo (-oddCentralEndpoint d.m d.a) 0) :
    realGapValue (2 * d.m + 1) d.a x <
      centralBidiagonalHeight d.m d.a := by
  have hneg :
      -x ∈ Ioo 0 (oddCentralEndpoint d.m d.a) :=
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  calc
    realGapValue (2 * d.m + 1) d.a x =
        realGapValue (2 * d.m + 1) d.a (-x) :=
      (realGapValue_neg (2 * d.m + 1) d.a x).symm
    _ < centralBidiagonalHeight d.m d.a :=
      realGapValue_lt_centralBidiagonalHeight_of_mem_positiveOddCentralGap
        d hneg

/-- Both open zero-adjacent odd central gaps satisfy the pointwise strict
upper comparison with `c_m`. -/
theorem realGapValue_lt_centralBidiagonalHeight_of_mem_oddCentralGaps
    (d : OddCentralChordData) {x : Real}
    (hx : x ∈
      Ioo (-oddCentralEndpoint d.m d.a) 0 ∪
        Ioo 0 (oddCentralEndpoint d.m d.a)) :
    realGapValue (2 * d.m + 1) d.a x <
      centralBidiagonalHeight d.m d.a := by
  rcases hx with hxnegative | hxpositive
  · exact
      realGapValue_lt_centralBidiagonalHeight_of_mem_negativeOddCentralGap
        d hxnegative
  · exact
      realGapValue_lt_centralBidiagonalHeight_of_mem_positiveOddCentralGap
        d hxpositive

/-- Literal strict upper central-height comparison from
`eq:central-interlace`: the actual compact maximum `d_m` is less than the
central bidiagonal least singular value `c_m`. -/
theorem oddCentralHeight_lt_centralBidiagonalHeight
    (d : OddCentralChordData) :
    oddCentralHeight d.m d.a < centralBidiagonalHeight d.m d.a := by
  obtain ⟨x, hx, hvalue⟩ :=
    exists_interior_realGapValue_eq_oddCentralHeight d
  rw [← hvalue]
  exact
    realGapValue_lt_centralBidiagonalHeight_of_mem_positiveOddCentralGap
      d hx

end

end ConnectedPseudospectrum
