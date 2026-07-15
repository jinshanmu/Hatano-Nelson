import ConnectedPseudospectrum.EvenCentralContinuation
import ConnectedPseudospectrum.MeshGapPartition
import ConnectedPseudospectrum.OddCentralHeight

/-!
# Central mesh-gap bridges

This module identifies the parity-specific central cases in
`MeshGapPartition` with the exact central intervals used by the even- and
odd-order height calculations.  Its indices implement the shifts in
lines 1940--1945 of the immutable source:

* mesh parameter `m` and even order `2 * (m + 1)` correspond to `c_(m+1)`;
* mesh parameter `m` and odd order `2 * m + 3` correspond to `d_(m+1)`;
* the predecessor of the first case has odd order `2 * m + 1` and height
  `d_m`.

Only endpoint identities and set equalities are proved here.  No central
height comparison is assumed.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-! ## Canonical data for the two parity cases -/

/-- Even central data of order `2 * (m + 1)` attached to the even mesh
case with parameter `m`. -/
def evenCentralDataOfMesh
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    EvenCentralHalfGapData where
  m := m + 1
  a := a
  hm := by omega
  ha0 := ha0
  ha1 := ha1

@[simp] theorem evenCentralDataOfMesh_m
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    (evenCentralDataOfMesh m a ha0 ha1).m = m + 1 := by
  rfl

@[simp] theorem evenCentralDataOfMesh_a
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    (evenCentralDataOfMesh m a ha0 ha1).a = a := by
  rfl

theorem evenCentralDataOfMesh_order
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    2 * (evenCentralDataOfMesh m a ha0 ha1).m =
      2 * (m + 1) := by
  rfl

/-- Odd central data of order `2 * m + 3` attached to the odd mesh case
with parameter `m`. -/
def oddCentralDataOfMesh
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    OddCentralChordData where
  m := m + 1
  a := a
  hm := by omega
  ha0 := ha0
  ha1 := ha1

@[simp] theorem oddCentralDataOfMesh_m
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    (oddCentralDataOfMesh m a ha0 ha1).m = m + 1 := by
  rfl

@[simp] theorem oddCentralDataOfMesh_a
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    (oddCentralDataOfMesh m a ha0 ha1).a = a := by
  rfl

theorem oddCentralDataOfMesh_order
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    2 * (oddCentralDataOfMesh m a ha0 ha1).m + 1 =
      2 * m + 3 := by
  simp only [oddCentralDataOfMesh_m]
  omega

/-- Odd central data of predecessor order `2 * m + 1` in the even mesh
case.  The hypothesis `m >= 1` is forced by successor order at least four. -/
def oddPredecessorDataOfEvenMesh
    (m : Nat) (hm : 1 ≤ m) (a : Real)
    (ha0 : 0 < a) (ha1 : a < 1) : OddCentralChordData where
  m := m
  a := a
  hm := hm
  ha0 := ha0
  ha1 := ha1

@[simp] theorem oddPredecessorDataOfEvenMesh_m
    (m : Nat) (hm : 1 ≤ m) (a : Real)
    (ha0 : 0 < a) (ha1 : a < 1) :
    (oddPredecessorDataOfEvenMesh m hm a ha0 ha1).m = m := by
  rfl

@[simp] theorem oddPredecessorDataOfEvenMesh_a
    (m : Nat) (hm : 1 ≤ m) (a : Real)
    (ha0 : 0 < a) (ha1 : a < 1) :
    (oddPredecessorDataOfEvenMesh m hm a ha0 ha1).a = a := by
  rfl

theorem oddPredecessorDataOfEvenMesh_order
    (m : Nat) (hm : 1 ≤ m) (a : Real)
    (ha0 : 0 < a) (ha1 : a < 1) :
    2 * (oddPredecessorDataOfEvenMesh m hm a ha0 ha1).m + 1 =
      2 * m + 1 := by
  rfl

/-! ## The single even central gap -/

/-- The lower generic mesh endpoint in the even central case is the
negative endpoint of the specialized even central gap. -/
theorem evenCentralMeshGap_lower_endpoint
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    pathEigenvalue (2 * (m + 1)) a
        (meshGapLowerIndex (evenCentralMeshGapIndex m)) =
      -(evenCentralDataOfMesh m a ha0 ha1).positiveEndpoint := by
  let d := evenCentralDataOfMesh m a ha0 ha1
  rw [pathEigenvalue_eq_symmetricPathEigenvalue]
  simpa only [d, evenCentralDataOfMesh, pathRate,
    meshGapLowerIndex, evenCentralMeshGapIndex] using
      d.negativeEndpoint_eq_symmetricPathEigenvalue.symm

/-- The upper generic mesh endpoint in the even central case is the
positive endpoint of the specialized even central gap. -/
theorem evenCentralMeshGap_upper_endpoint
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    pathEigenvalue (2 * (m + 1)) a
        (meshGapUpperIndex (evenCentralMeshGapIndex m)) =
      (evenCentralDataOfMesh m a ha0 ha1).positiveEndpoint := by
  let d := evenCentralDataOfMesh m a ha0 ha1
  rw [pathEigenvalue_eq_symmetricPathEigenvalue]
  simpa only [d, evenCentralDataOfMesh, pathRate,
    meshGapUpperIndex, evenCentralMeshGapIndex] using
      d.positiveEndpoint_eq_symmetricPathEigenvalue.symm

/-- The even central mesh gap is literally the gap controlled by
`EvenCentralHalfGapData.centralGap_height_eq_and_unique`. -/
theorem evenCentralMeshGap_eq_centralSpectralGap
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    evenCentralMeshGap m a =
      (evenCentralDataOfMesh m a ha0 ha1).centralSpectralGap := by
  unfold evenCentralMeshGap spectralMeshGap
    EvenCentralHalfGapData.centralSpectralGap
  rw [evenCentralMeshGap_lower_endpoint m a ha0 ha1,
    evenCentralMeshGap_upper_endpoint m a ha0 ha1]

/-! ## The two odd central gaps -/

/-- The positive odd central mesh gap starts at the zero eigenvalue. -/
theorem oddPositiveCentralMeshGap_lower_endpoint
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    pathEigenvalue (2 * m + 3) a
        (meshGapLowerIndex (oddPositiveCentralMeshGapIndex m)) = 0 := by
  let d := oddCentralDataOfMesh m a ha0 ha1
  have horder : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
  simpa only [d, oddCentralDataOfMesh, positiveHalfGapLower,
    OddCentralChordData.positiveGap_matrixOrder,
    OddCentralChordData.positiveGap_j,
    OddCentralChordData.positiveGap_a, horder,
    pathEigenvalue_eq_symmetricPathEigenvalue, pathRate,
    meshGapLowerIndex, oddPositiveCentralMeshGapIndex] using
      d.positiveGap_lowerEndpoint

/-- The upper endpoint of the positive odd central mesh gap is the source's
explicit `oddCentralEndpoint`. -/
theorem oddPositiveCentralMeshGap_upper_endpoint
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    pathEigenvalue (2 * m + 3) a
        (meshGapUpperIndex (oddPositiveCentralMeshGapIndex m)) =
      oddCentralEndpoint (m + 1) a := by
  let d := oddCentralDataOfMesh m a ha0 ha1
  have horder : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
  simpa only [d, oddCentralDataOfMesh, positiveHalfGapUpper,
    OddCentralChordData.positiveGap_matrixOrder,
    OddCentralChordData.positiveGap_j,
    OddCentralChordData.positiveGap_a, horder,
    pathEigenvalue_eq_symmetricPathEigenvalue, pathRate,
    meshGapUpperIndex, oddPositiveCentralMeshGapIndex] using
      positiveGap_upperEndpoint_eq_oddCentralEndpoint d

/-- Reflection sends the positive upper endpoint index to the negative
lower endpoint index. -/
theorem oddNegativeCentral_lowerIndex_eq_rev_positiveUpperIndex
    (m : Nat) :
    meshGapLowerIndex (oddNegativeCentralMeshGapIndex m) =
      (meshGapUpperIndex (oddPositiveCentralMeshGapIndex m)).rev := by
  apply Fin.ext
  simp only [meshGapLowerIndex_val, meshGapUpperIndex_val,
    Fin.val_rev, oddNegativeCentralMeshGapIndex,
    oddPositiveCentralMeshGapIndex]
  omega

/-- Reflection fixes the central zero index and identifies it as the upper
endpoint index of the negative central gap. -/
theorem oddNegativeCentral_upperIndex_eq_rev_positiveLowerIndex
    (m : Nat) :
    meshGapUpperIndex (oddNegativeCentralMeshGapIndex m) =
      (meshGapLowerIndex (oddPositiveCentralMeshGapIndex m)).rev := by
  apply Fin.ext
  simp only [meshGapUpperIndex_val, meshGapLowerIndex_val,
    Fin.val_rev, oddNegativeCentralMeshGapIndex,
    oddPositiveCentralMeshGapIndex]
  omega

/-- The lower endpoint of the negative odd central gap is the negative of
the positive central endpoint. -/
theorem oddNegativeCentralMeshGap_lower_endpoint
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    pathEigenvalue (2 * m + 3) a
        (meshGapLowerIndex (oddNegativeCentralMeshGapIndex m)) =
      -oddCentralEndpoint (m + 1) a := by
  rw [oddNegativeCentral_lowerIndex_eq_rev_positiveUpperIndex,
    pathEigenvalue_rev,
    oddPositiveCentralMeshGap_upper_endpoint m a ha0 ha1]

/-- The upper endpoint of the negative odd central gap is zero. -/
theorem oddNegativeCentralMeshGap_upper_endpoint
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    pathEigenvalue (2 * m + 3) a
        (meshGapUpperIndex (oddNegativeCentralMeshGapIndex m)) = 0 := by
  rw [oddNegativeCentral_upperIndex_eq_rev_positiveLowerIndex,
    pathEigenvalue_rev,
    oddPositiveCentralMeshGap_lower_endpoint m a ha0 ha1,
    neg_zero]

/-- Exact open interval for the positive zero-adjacent odd central gap. -/
theorem oddPositiveCentralMeshGap_eq_Ioo
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    spectralMeshGap (2 * m + 3) a
        (oddPositiveCentralMeshGapIndex m) =
      Ioo 0 (oddCentralEndpoint (m + 1) a) := by
  unfold spectralMeshGap
  rw [oddPositiveCentralMeshGap_lower_endpoint m a ha0 ha1,
    oddPositiveCentralMeshGap_upper_endpoint m a ha0 ha1]

/-- Exact open interval for the negative zero-adjacent odd central gap. -/
theorem oddNegativeCentralMeshGap_eq_Ioo
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    spectralMeshGap (2 * m + 3) a
        (oddNegativeCentralMeshGapIndex m) =
      Ioo (-oddCentralEndpoint (m + 1) a) 0 := by
  unfold spectralMeshGap
  rw [oddNegativeCentralMeshGap_lower_endpoint m a ha0 ha1,
    oddNegativeCentralMeshGap_upper_endpoint m a ha0 ha1]

/-- The parity-specific odd mesh set is exactly the union of the two open
central intervals used by the odd height comparison. -/
theorem oddCentralMeshGaps_eq_openCentralIntervals
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    oddCentralMeshGaps m a =
      Ioo (-oddCentralEndpoint (m + 1) a) 0 ∪
        Ioo 0 (oddCentralEndpoint (m + 1) a) := by
  unfold oddCentralMeshGaps
  rw [oddPositiveCentralMeshGap_eq_Ioo m a ha0 ha1,
    oddNegativeCentralMeshGap_eq_Ioo m a ha0 ha1,
    union_comm]

/-- The positive open odd central mesh gap lies in the closed interval whose
maximum defines `oddCentralHeight`. -/
theorem oddPositiveCentralMeshGap_subset_oddCentralInterval
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    spectralMeshGap (2 * m + 3) a
        (oddPositiveCentralMeshGapIndex m) ⊆
      oddCentralInterval (m + 1) a := by
  rw [oddPositiveCentralMeshGap_eq_Ioo m a ha0 ha1]
  intro x hx
  rw [oddCentralInterval, mem_Icc]
  exact ⟨hx.1.le, hx.2.le⟩

/-- The negative open odd central mesh gap lies in its reflected closed
central interval. -/
theorem oddNegativeCentralMeshGap_subset_oddNegativeCentralInterval
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    spectralMeshGap (2 * m + 3) a
        (oddNegativeCentralMeshGapIndex m) ⊆
      oddNegativeCentralInterval (m + 1) a := by
  rw [oddNegativeCentralMeshGap_eq_Ioo m a ha0 ha1]
  intro x hx
  rw [oddNegativeCentralInterval, mem_Icc]
  exact ⟨hx.1.le, hx.2.le⟩

/-- The union of the two open odd central mesh gaps lies in the symmetric
closed double interval. -/
theorem oddCentralMeshGaps_subset_oddCentralDoubleInterval
    (m : Nat) (a : Real) (ha0 : 0 < a) (ha1 : a < 1) :
    oddCentralMeshGaps m a ⊆
      oddCentralDoubleInterval (m + 1) a := by
  let d := oddCentralDataOfMesh m a ha0 ha1
  intro x hx
  rw [oddCentralMeshGaps_eq_openCentralIntervals m a ha0 ha1,
    mem_union] at hx
  rw [oddCentralDoubleInterval, mem_Icc]
  rcases hx with hxnegative | hxpositive
  · exact ⟨hxnegative.1.le,
      hxnegative.2.le.trans (oddCentralEndpoint_pos d).le⟩
  · exact ⟨by
        have hend := oddCentralEndpoint_pos d
        change 0 < oddCentralEndpoint (m + 1) a at hend
        linarith [hxpositive.1],
      hxpositive.2.le⟩

end

end ConnectedPseudospectrum
