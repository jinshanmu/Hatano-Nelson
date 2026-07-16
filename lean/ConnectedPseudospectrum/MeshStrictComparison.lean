import ConnectedPseudospectrum.MeshGapUtilities
import ConnectedPseudospectrum.CentralMeshBridges
import ConnectedPseudospectrum.OddCentralLowerComparison
import ConnectedPseudospectrum.NoncentralReflectedComparison

/-!
# Strict comparison of consecutive real mesh barriers

This module assembles the final comparison in `lem:mesh`.  Every nonspectral point of
the order-`N` real spectral interval is first placed in one of the four
branches of `mem_positive_or_reflected_or_central_meshGap`.  The two
noncentral branches use the positive or reflected same-origin gap
comparison.  The central branches use the exact parity shifts

* `N = 2 * (m + 1)`: successor height `c_(m+1)`, predecessor height `d_m`;
* `N = 2 * m + 3`: successor height `d_(m+1)`, predecessor height `c_(m+1)`.

Thus every successor value is strictly dominated by an actual predecessor
value.  Applying this transfer to an off-spectrum global maximizer proves
the strict inequality between consecutive `gapBarrier`s.  An individual
mesh-gap-height version records the source's max-over-gap step explicitly.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-! ## The two central parity branches -/

/-- If the successor order is `2 * (m + 1)`, its single even central gap is
bounded by `c_(m+1)`.  The strict lower central comparison
`c_(m+1) < d_m` and an attained odd predecessor maximizer give a genuine
predecessor point of order `2 * m + 1` with strictly greater height. -/
theorem exists_oddPredecessorPoint_strict_of_mem_evenCentralMeshGap
    (m : Nat) (hm : 1 ≤ m) {a x : Real}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hx : x ∈ evenCentralMeshGap m a) :
    ∃ xhat ∈ spectralInterval (2 * m + 1) a,
      realGapValue (2 * (m + 1)) a x <
        realGapValue (2 * m + 1) a xhat := by
  let e := evenCentralDataOfMesh m a ha0 ha1
  let d := oddPredecessorDataOfEvenMesh m hm a ha0 ha1
  have hxCentral : x ∈ e.centralSpectralGap := by
    have hx' := hx
    rw [evenCentralMeshGap_eq_centralSpectralGap m a ha0 ha1] at hx'
    simpa only [e] using hx'
  have hxBound :
      realGapValue (2 * (m + 1)) a x ≤
        centralBidiagonalHeight (m + 1) a := by
    have hbound :=
      (EvenCentralHalfGapData.centralGap_height_eq_and_unique e).2
        x hxCentral
    simpa only [e, evenCentralDataOfMesh_m,
      evenCentralDataOfMesh_a] using hbound.1
  have hinterlace :
      centralBidiagonalHeight (m + 1) a <
        oddCentralHeight m a := by
    have h :=
      OddCentralChordData.centralBidiagonalHeight_succ_lt_oddCentralHeight d
    simpa only [d, oddPredecessorDataOfEvenMesh_m,
      oddPredecessorDataOfEvenMesh_a] using h
  obtain ⟨xhat, hxhat, hxhatValue⟩ :=
    exists_interior_realGapValue_eq_oddCentralHeight d
  have hxhatGap : xhat ∈ positiveHalfSpectralGap d.positiveGap := by
    rw [OddCentralChordData.positiveHalfSpectralGap_positiveGap]
    simpa only [oddCentralEndpoint] using hxhat
  have hxhatInterval : xhat ∈ spectralInterval (2 * m + 1) a := by
    have h := positiveHalfSpectralGap_subset_spectralInterval
      d.positiveGap hxhatGap
    simpa only [OddCentralChordData.positiveGap_matrixOrder,
      OddCentralChordData.positiveGap_a, d,
      oddPredecessorDataOfEvenMesh_m,
      oddPredecessorDataOfEvenMesh_a] using h
  have hxhatValue' :
      realGapValue (2 * m + 1) a xhat = oddCentralHeight m a := by
    simpa only [d, oddPredecessorDataOfEvenMesh_m,
      oddPredecessorDataOfEvenMesh_a] using hxhatValue
  refine ⟨xhat, hxhatInterval, ?_⟩
  rw [hxhatValue']
  exact hxBound.trans_lt hinterlace

/-- If the successor order is `2 * m + 3`, both zero-adjacent odd central
gaps are pointwise strictly below `c_(m+1)`.  The predecessor of order
`2 * (m + 1)` attains this value at its centre `xhat = 0`. -/
theorem exists_evenPredecessorPoint_strict_of_mem_oddCentralMeshGaps
    (m : Nat) {a x : Real}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hx : x ∈ oddCentralMeshGaps m a) :
    ∃ xhat ∈ spectralInterval (2 * (m + 1)) a,
      realGapValue (2 * m + 3) a x <
        realGapValue (2 * (m + 1)) a xhat := by
  let d := oddCentralDataOfMesh m a ha0 ha1
  let e := evenCentralDataOfMesh m a ha0 ha1
  have hxDouble : x ∈ oddCentralDoubleInterval (m + 1) a :=
    oddCentralMeshGaps_subset_oddCentralDoubleInterval
      m a ha0 ha1 hx
  have hxBound :
      realGapValue (2 * m + 3) a x ≤ oddCentralHeight (m + 1) a := by
    have h := realGapValue_le_oddCentralHeight_of_mem_doubleInterval
      d (by
        simpa only [d, oddCentralDataOfMesh_m,
          oddCentralDataOfMesh_a] using hxDouble)
    simpa only [d, oddCentralDataOfMesh_order,
      oddCentralDataOfMesh_m, oddCentralDataOfMesh_a] using h
  have hinterlace :
      oddCentralHeight (m + 1) a <
        centralBidiagonalHeight (m + 1) a := by
    have h := oddCentralHeight_lt_centralBidiagonalHeight d
    simpa only [d,
      oddCentralDataOfMesh_m, oddCentralDataOfMesh_a] using h
  have hcenter :
      realGapValue (2 * (m + 1)) a 0 =
        centralBidiagonalHeight (m + 1) a := by
    have h :=
      (EvenCentralHalfGapData.centralGap_height_eq_and_unique e).1
    simpa only [e, evenCentralDataOfMesh_m,
      evenCentralDataOfMesh_a] using h
  refine ⟨0, zero_mem_spectralInterval (2 * (m + 1)) a (by omega), ?_⟩
  calc
    realGapValue (2 * m + 3) a x ≤ oddCentralHeight (m + 1) a :=
      hxBound
    _ < centralBidiagonalHeight (m + 1) a := hinterlace
    _ = realGapValue (2 * (m + 1)) a 0 := hcenter.symm

/-! ## Four-way point transfer -/

/-- Exact successor-to-predecessor transfer for every nonspectral point of
the successor real spectral interval.  The output is an actual predecessor
point, not an abstract bound. -/
theorem exists_predecessorPoint_strict_of_mem_successorInterval_offSpectrum
    (N : Nat) (hN : 3 ≤ N) {a x : Real}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hx : x ∈ spectralInterval N a)
    (hnodes : ∀ k : Fin N, x ≠ pathEigenvalue N a k) :
    ∃ xhat ∈ spectralInterval (N - 1) a,
      realGapValue N a x < realGapValue (N - 1) a xhat := by
  rcases mem_positive_or_reflected_or_central_meshGap
      N hN ha0 ha1 hx hnodes with
      ⟨d, hdK, hda, hxGap⟩ |
      ⟨d, hdK, hda, hxGap⟩ |
      ⟨m, horder, hxGap⟩ |
      ⟨m, horder, hxGap⟩
  · obtain ⟨xhat, hxhatGap, hstrict⟩ :=
      exists_predecessorGapPoint_strict_of_mem_successorGap d hxGap
    have hxhatInterval :=
      positiveHalfSpectralGap_subset_spectralInterval d hxhatGap
    rw [hdK, hda] at hxhatInterval hstrict
    exact ⟨xhat, hxhatInterval, hstrict⟩
  · obtain ⟨xhat, hxhatGap, hstrict⟩ :=
      exists_predecessorReflectedGapPoint_strict_of_mem_successorGap d hxGap
    have hxhatInterval :=
      reflectedNegativeSpectralGap_subset_spectralInterval d hxhatGap
    rw [hdK, hda] at hxhatInterval hstrict
    exact ⟨xhat, hxhatInterval, hstrict⟩
  · subst N
    have hm : 1 ≤ m := by omega
    have hpred : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    simpa only [hpred] using
      exists_oddPredecessorPoint_strict_of_mem_evenCentralMeshGap
        m hm ha0 ha1 hxGap
  · subst N
    have hpred : 2 * m + 3 - 1 = 2 * (m + 1) := by omega
    simpa only [hpred] using
      exists_evenPredecessorPoint_strict_of_mem_oddCentralMeshGaps
        m ha0 ha1 hxGap

/-! ## Per-gap and global strict comparison -/

/-- Every individual compact successor mesh-gap height is strictly below
the predecessor global barrier.  This is the pointwise max-over-gap form of
the comparison used to conclude `lem:mesh`. -/
theorem meshGapHeight_succ_lt_gapBarrier
    (n : Nat) (hn : 2 ≤ n) {a : Real}
    (ha0 : 0 < a) (ha1 : a < 1)
    (j : MeshGapIndex (n + 1)) :
    meshGapHeight (n + 1) a j < gapBarrier n a := by
  obtain ⟨x, hxGap, hxValue⟩ :=
    exists_interior_realGapValue_eq_meshGapHeight (n + 1) ha0 j
  have hxInterval : x ∈ spectralInterval (n + 1) a :=
    spectralMeshGap_subset_spectralInterval (n + 1) ha0 j hxGap
  have hnodes :
      ∀ k : Fin (n + 1), x ≠ pathEigenvalue (n + 1) a k := by
    intro k
    exact ne_pathEigenvalue_of_mem_spectralMeshGap
      (n + 1) ha0 j hxGap k
  obtain ⟨xhat, hxhat, hstrict⟩ :=
    exists_predecessorPoint_strict_of_mem_successorInterval_offSpectrum
      (n + 1) (by omega) ha0 ha1 hxInterval hnodes
  have hxhat' : xhat ∈ spectralInterval n a := by
    simpa only [Nat.add_sub_cancel] using hxhat
  have hstrict' :
      realGapValue (n + 1) a x < realGapValue n a xhat := by
    simpa only [Nat.add_sub_cancel] using hstrict
  calc
    meshGapHeight (n + 1) a j = realGapValue (n + 1) a x :=
      hxValue.symm
    _ < realGapValue n a xhat := hstrict'
    _ ≤ gapBarrier n a :=
      realGapValue_le_gapBarrier n a xhat hxhat'

/-- A successor mesh gap attaining the global barrier is explicit, and its
height is already strictly below the predecessor barrier.  This packages
`gamma_n = max_j gamma_(n,j)` together with the strict comparison. -/
theorem exists_meshGapHeight_eq_gapBarrier_and_lt_predecessor
    (n : Nat) (hn : 2 ≤ n) {a : Real}
    (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ j : MeshGapIndex (n + 1),
      meshGapHeight (n + 1) a j = gapBarrier (n + 1) a ∧
        meshGapHeight (n + 1) a j < gapBarrier n a := by
  obtain ⟨j, hj⟩ :=
    exists_meshGapHeight_eq_gapBarrier (n + 1) (by omega) ha0
  exact ⟨j, hj, meshGapHeight_succ_lt_gapBarrier
    n hn ha0 ha1 j⟩

/-- Strict decrease of the actual global real gap barrier.  The proof uses
an attained off-spectrum maximizer of the successor barrier, exactly as in
the source, and transfers that point through the four-way mesh partition. -/
theorem gapBarrier_succ_lt
    (n : Nat) (hn : 2 ≤ n) {a : Real}
    (ha0 : 0 < a) (ha1 : a < 1) :
    gapBarrier (n + 1) a < gapBarrier n a := by
  obtain ⟨x, hx, hnodes, hxValue⟩ :=
    exists_offSpectrum_realGapValue_eq_gapBarrier
      (n + 1) (by omega) ha0
  obtain ⟨xhat, hxhat, hstrict⟩ :=
    exists_predecessorPoint_strict_of_mem_successorInterval_offSpectrum
      (n + 1) (by omega) ha0 ha1 hx hnodes
  have hxhat' : xhat ∈ spectralInterval n a := by
    simpa only [Nat.add_sub_cancel] using hxhat
  have hstrict' :
      realGapValue (n + 1) a x < realGapValue n a xhat := by
    simpa only [Nat.add_sub_cancel] using hstrict
  calc
    gapBarrier (n + 1) a = realGapValue (n + 1) a x := hxValue.symm
    _ < realGapValue n a xhat := hstrict'
    _ ≤ gapBarrier n a :=
      realGapValue_le_gapBarrier n a xhat hxhat'

end

end ConnectedPseudospectrum
