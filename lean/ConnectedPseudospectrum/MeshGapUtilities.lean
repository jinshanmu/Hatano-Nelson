import ConnectedPseudospectrum.MeshGapPartition

/-!
# Compact gap heights and spectral-mesh utility lemmas

This module supplies the compactness and positivity layer used in
`eq:gamma-def` and the final assembly of `lem:mesh`.  The generic mesh
partition uses open adjacent-node gaps, while the source defines each
individual gap height on the corresponding closed interval.  Both versions
are recorded here and related to the global real barrier `gapBarrier`.

The declarations in this file contain no finite-size comparison.  They only
show that adjacent-node gaps are nonempty and nonspectral in their interiors,
that their compact heights are attained in those interiors, and that at least
one individual gap realizes the global barrier.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-! ## Open mesh gaps -/

/-- Every adjacent-node open spectral gap is nonempty when `a > 0`. -/
theorem spectralMeshGap_nonempty
    (n : Nat) {a : Real} (ha : 0 < a) (j : MeshGapIndex n) :
    (spectralMeshGap n a j).Nonempty := by
  have hindex : meshGapUpperIndex j < meshGapLowerIndex j := by
    change j.val - 1 < j.val
    have hj := j.pos
    omega
  have hgap :
      pathEigenvalue n a (meshGapLowerIndex j) <
        pathEigenvalue n a (meshGapUpperIndex j) :=
    (pathEigenvalue_strictAnti n ha) hindex
  refine ⟨(pathEigenvalue n a (meshGapLowerIndex j) +
      pathEigenvalue n a (meshGapUpperIndex j)) / 2, ?_⟩
  rw [spectralMeshGap, mem_Ioo]
  constructor <;> linarith

/-- Every open adjacent-node gap lies in the convex hull of the spectrum. -/
theorem spectralMeshGap_subset_spectralInterval
    (n : Nat) {a : Real} (ha : 0 < a) (j : MeshGapIndex n) :
    spectralMeshGap n a j ⊆ spectralInterval n a := by
  intro x hx
  have hn : n ≠ 0 := by
    have hj := j.isLt
    omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hlower := pathEigenvalue_mem_spectralInterval m ha
    (meshGapLowerIndex j)
  have hupper := pathEigenvalue_mem_spectralInterval m ha
    (meshGapUpperIndex j)
  rw [spectralMeshGap, mem_Ioo] at hx
  rw [spectralInterval, mem_Icc] at hlower hupper ⊢
  exact ⟨hlower.1.trans hx.1.le, hx.2.le.trans hupper.2⟩

/-- No displayed spectral node lies in an open adjacent-node gap. -/
theorem ne_pathEigenvalue_of_mem_spectralMeshGap
    (n : Nat) {a x : Real} (ha : 0 < a)
    (j : MeshGapIndex n) (hx : x ∈ spectralMeshGap n a j)
    (k : Fin n) :
    x ≠ pathEigenvalue n a k := by
  rw [spectralMeshGap, mem_Ioo] at hx
  by_cases hkj : k.val < j.val
  · have hkUpper : k ≤ meshGapUpperIndex j := by
      change k.val ≤ j.val - 1
      omega
    have hxEigen : x < pathEigenvalue n a k :=
      hx.2.trans_le
        ((pathEigenvalue_strictAnti n ha).antitone hkUpper)
    exact ne_of_lt hxEigen
  · have hLowerK : meshGapLowerIndex j ≤ k := by
      change j.val ≤ k.val
      omega
    have hEigenX : pathEigenvalue n a k < x :=
      lt_of_le_of_lt
        ((pathEigenvalue_strictAnti n ha).antitone hLowerK) hx.1
    exact ne_of_gt hEigenX

/-- The actual Euclidean least singular value is positive in every open
adjacent-node gap. -/
theorem realGapValue_pos_of_mem_spectralMeshGap
    (n : Nat) {a x : Real} (ha : 0 < a)
    (j : MeshGapIndex n) (hx : x ∈ spectralMeshGap n a j) :
    0 < realGapValue n a x := by
  have hn : n ≠ 0 := by
    have hj := j.isLt
    omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  unfold realGapValue
  apply (pseudospectralHeight_pos_iff_not_spectralNode
    m ha (x : Complex)).2
  intro k hk
  apply ne_pathEigenvalue_of_mem_spectralMeshGap
    (m + 1) ha j hx k
  exact Complex.ofReal_injective hk

/-- In every dimension at least two, the compact real barrier is strictly
positive. -/
theorem gapBarrier_pos
    (n : Nat) (hn : 2 ≤ n) {a : Real} (ha : 0 < a) :
    0 < gapBarrier n a := by
  let j : MeshGapIndex n :=
    ⟨1, by omega, by omega⟩
  obtain ⟨x, hx⟩ := spectralMeshGap_nonempty n ha j
  exact (realGapValue_pos_of_mem_spectralMeshGap n ha j hx).trans_le
    (realGapValue_le_gapBarrier n a x
      (spectralMeshGap_subset_spectralInterval n ha j hx))

/-! ## Packaged predecessor gaps -/

/-- The generic mesh index of a packaged positive gap in its own matrix
order `d.K - 1`. -/
def predecessorMeshGapIndex (d : PositiveHalfGap) :
    MeshGapIndex (d.K - 1) where
  val := d.j
  pos := d.hj
  isLt := by
    have hjUpper := d.hjUpper
    omega

/-- A packaged positive gap is its corresponding predecessor mesh gap. -/
theorem spectralMeshGap_predecessor_eq_positiveHalfSpectralGap
    (d : PositiveHalfGap) :
    spectralMeshGap (d.K - 1) d.a (predecessorMeshGapIndex d) =
      positiveHalfSpectralGap d := by
  unfold spectralMeshGap positiveHalfSpectralGap
  rw [pathEigenvalue_eq_symmetricPathEigenvalue,
    pathEigenvalue_eq_symmetricPathEigenvalue]
  rfl

/-- A packaged positive predecessor gap lies in its real spectral interval. -/
theorem positiveHalfSpectralGap_subset_spectralInterval
    (d : PositiveHalfGap) :
    positiveHalfSpectralGap d ⊆
      spectralInterval (d.K - 1) d.a := by
  intro x hx
  apply spectralMeshGap_subset_spectralInterval
    (d.K - 1) d.ha0 (predecessorMeshGapIndex d)
  rw [spectralMeshGap_predecessor_eq_positiveHalfSpectralGap]
  exact hx

/-- The reflected negative predecessor gap lies in the same symmetric real
spectral interval. -/
theorem reflectedNegativeSpectralGap_subset_spectralInterval
    (d : PositiveHalfGap) :
    reflectedNegativeSpectralGap d ⊆
      spectralInterval (d.K - 1) d.a := by
  intro x hx
  have hpositive : -x ∈ positiveHalfSpectralGap d :=
    (mem_reflectedNegativeSpectralGap d x).mp hx
  have hspectral : -x ∈ spectralInterval (d.K - 1) d.a :=
    positiveHalfSpectralGap_subset_spectralInterval d hpositive
  rw [spectralInterval, mem_Icc] at hspectral ⊢
  exact ⟨by linarith [hspectral.2], by linarith [hspectral.1]⟩

/-! ## Closed mesh gaps and their attained heights -/

/-- The source's closed adjacent-node spectral gap `G_{n,j}`. -/
def closedSpectralMeshGap
    (n : Nat) (a : Real) (j : MeshGapIndex n) : Set Real :=
  Icc (pathEigenvalue n a (meshGapLowerIndex j))
    (pathEigenvalue n a (meshGapUpperIndex j))

/-- The open mesh gap is contained in its closed counterpart. -/
theorem spectralMeshGap_subset_closedSpectralMeshGap
    (n : Nat) (a : Real) (j : MeshGapIndex n) :
    spectralMeshGap n a j ⊆ closedSpectralMeshGap n a j := by
  intro x hx
  rw [spectralMeshGap, mem_Ioo] at hx
  rw [closedSpectralMeshGap, mem_Icc]
  exact ⟨hx.1.le, hx.2.le⟩

/-- Every closed adjacent-node gap is nonempty for `a > 0`. -/
theorem closedSpectralMeshGap_nonempty
    (n : Nat) {a : Real} (ha : 0 < a) (j : MeshGapIndex n) :
    (closedSpectralMeshGap n a j).Nonempty := by
  obtain ⟨x, hx⟩ := spectralMeshGap_nonempty n ha j
  exact ⟨x, spectralMeshGap_subset_closedSpectralMeshGap n a j hx⟩

/-- Every closed adjacent-node gap lies in the real spectral interval. -/
theorem closedSpectralMeshGap_subset_spectralInterval
    (n : Nat) {a : Real} (ha : 0 < a) (j : MeshGapIndex n) :
    closedSpectralMeshGap n a j ⊆ spectralInterval n a := by
  intro x hx
  have hn : n ≠ 0 := by
    have hj := j.isLt
    omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hlower := pathEigenvalue_mem_spectralInterval m ha
    (meshGapLowerIndex j)
  have hupper := pathEigenvalue_mem_spectralInterval m ha
    (meshGapUpperIndex j)
  rw [closedSpectralMeshGap, mem_Icc] at hx
  rw [spectralInterval, mem_Icc] at hlower hupper ⊢
  exact ⟨hlower.1.trans hx.1, hx.2.trans hupper.2⟩

/-- The source's individual compact gap height `gamma_{n,j}`. -/
def meshGapHeight
    (n : Nat) (a : Real) (j : MeshGapIndex n) : Real :=
  sSup (realGapValue n a '' closedSpectralMeshGap n a j)

/-- The image defining an individual mesh-gap height is compact. -/
theorem compact_meshGapRange
    (n : Nat) (a : Real) (j : MeshGapIndex n) :
    IsCompact
      (realGapValue n a '' closedSpectralMeshGap n a j) := by
  unfold closedSpectralMeshGap
  exact isCompact_Icc.image (continuous_realGapValue n a)

/-- Under `a > 0`, the compact image defining a mesh-gap height is
nonempty. -/
theorem nonempty_meshGapRange
    (n : Nat) {a : Real} (ha : 0 < a) (j : MeshGapIndex n) :
    (realGapValue n a '' closedSpectralMeshGap n a j).Nonempty := by
  obtain ⟨x, hx⟩ := closedSpectralMeshGap_nonempty n ha j
  refine ⟨realGapValue n a x, ?_⟩
  exact ⟨x, hx, rfl⟩

/-- The compact maximum defining an individual mesh-gap height is attained. -/
theorem exists_realGapValue_eq_meshGapHeight
    (n : Nat) {a : Real} (ha : 0 < a) (j : MeshGapIndex n) :
    ∃ x ∈ closedSpectralMeshGap n a j,
      realGapValue n a x = meshGapHeight n a j := by
  have hcompact := compact_meshGapRange n a j
  have hnonempty := nonempty_meshGapRange n ha j
  have hmem :
      meshGapHeight n a j ∈
        realGapValue n a '' closedSpectralMeshGap n a j := by
    exact hcompact.isClosed.csSup_mem hnonempty
      hcompact.isBounded.bddAbove
  exact hmem

/-- Every value on a closed mesh gap is bounded by its gap height. -/
theorem realGapValue_le_meshGapHeight
    (n : Nat) (a x : Real) (j : MeshGapIndex n)
    (hx : x ∈ closedSpectralMeshGap n a j) :
    realGapValue n a x ≤ meshGapHeight n a j := by
  apply le_csSup (compact_meshGapRange n a j).isBounded.bddAbove
  exact ⟨x, hx, rfl⟩

/-- The least singular value vanishes at the lower endpoint of a mesh gap. -/
@[simp] theorem realGapValue_meshGapLower_eq_zero
    (n : Nat) {a : Real} (ha : 0 < a) (j : MeshGapIndex n) :
    realGapValue n a
      (pathEigenvalue n a (meshGapLowerIndex j)) = 0 := by
  have hn : 0 < n := by
    have hj := j.isLt
    omega
  unfold realGapValue
  exact pseudospectralHeight_pathEigenvalue n ha hn
    (meshGapLowerIndex j)

/-- The least singular value vanishes at the upper endpoint of a mesh gap. -/
@[simp] theorem realGapValue_meshGapUpper_eq_zero
    (n : Nat) {a : Real} (ha : 0 < a) (j : MeshGapIndex n) :
    realGapValue n a
      (pathEigenvalue n a (meshGapUpperIndex j)) = 0 := by
  have hn : 0 < n := by
    have hj := j.isLt
    omega
  unfold realGapValue
  exact pseudospectralHeight_pathEigenvalue n ha hn
    (meshGapUpperIndex j)

/-- Every individual compact mesh-gap height is strictly positive. -/
theorem meshGapHeight_pos
    (n : Nat) {a : Real} (ha : 0 < a) (j : MeshGapIndex n) :
    0 < meshGapHeight n a j := by
  obtain ⟨x, hx⟩ := spectralMeshGap_nonempty n ha j
  exact (realGapValue_pos_of_mem_spectralMeshGap n ha j hx).trans_le
    (realGapValue_le_meshGapHeight n a x j
      (spectralMeshGap_subset_closedSpectralMeshGap n a j hx))

/-- Since both spectral endpoints have height zero, an individual gap-height
maximizer is attained strictly inside the open gap. -/
theorem exists_interior_realGapValue_eq_meshGapHeight
    (n : Nat) {a : Real} (ha : 0 < a) (j : MeshGapIndex n) :
    ∃ x ∈ spectralMeshGap n a j,
      realGapValue n a x = meshGapHeight n a j := by
  obtain ⟨x, hx, hvalue⟩ :=
    exists_realGapValue_eq_meshGapHeight n ha j
  have hxIcc :
      x ∈ Icc (pathEigenvalue n a (meshGapLowerIndex j))
        (pathEigenvalue n a (meshGapUpperIndex j)) := by
    simpa only [closedSpectralMeshGap] using hx
  have hxvaluePos : 0 < realGapValue n a x := by
    rw [hvalue]
    exact meshGapHeight_pos n ha j
  have hxneLower :
      x ≠ pathEigenvalue n a (meshGapLowerIndex j) := by
    intro heq
    rw [heq, realGapValue_meshGapLower_eq_zero n ha j] at hxvaluePos
    exact (lt_irrefl 0) hxvaluePos
  have hxneUpper :
      x ≠ pathEigenvalue n a (meshGapUpperIndex j) := by
    intro heq
    rw [heq, realGapValue_meshGapUpper_eq_zero n ha j] at hxvaluePos
    exact (lt_irrefl 0) hxvaluePos
  refine ⟨x, ?_, hvalue⟩
  rw [spectralMeshGap, mem_Ioo]
  exact ⟨lt_of_le_of_ne hxIcc.1 (Ne.symm hxneLower),
    lt_of_le_of_ne hxIcc.2 hxneUpper⟩

/-! ## Relation with the global barrier -/

/-- Every individual mesh-gap height is bounded by the global barrier. -/
theorem meshGapHeight_le_gapBarrier
    (n : Nat) {a : Real} (ha : 0 < a) (j : MeshGapIndex n) :
    meshGapHeight n a j ≤ gapBarrier n a := by
  obtain ⟨x, hx, hvalue⟩ :=
    exists_realGapValue_eq_meshGapHeight n ha j
  rw [← hvalue]
  exact realGapValue_le_gapBarrier n a x
    (closedSpectralMeshGap_subset_spectralInterval n ha j hx)

/-- A global barrier maximizer is nonspectral in every dimension at least
two. -/
theorem exists_offSpectrum_realGapValue_eq_gapBarrier
    (n : Nat) (hn : 2 ≤ n) {a : Real} (ha : 0 < a) :
    ∃ x ∈ spectralInterval n a,
      (∀ k : Fin n, x ≠ pathEigenvalue n a k) ∧
      realGapValue n a x = gapBarrier n a := by
  obtain ⟨x, hx, hvalue⟩ :=
    exists_realGapValue_eq_gapBarrier n a (by omega)
  have hxpos : 0 < realGapValue n a x := by
    rw [hvalue]
    exact gapBarrier_pos n hn ha
  refine ⟨x, hx, ?_, hvalue⟩
  intro k hk
  have hzero : realGapValue n a x = 0 := by
    rw [hk]
    unfold realGapValue
    exact pseudospectralHeight_pathEigenvalue n ha (by omega) k
  rw [hzero] at hxpos
  exact (lt_irrefl 0) hxpos

/-- Some individual adjacent-node gap realizes the global barrier.  This is
the attained finite-mesh form of `gamma_n = max_j gamma_{n,j}`. -/
theorem exists_meshGapHeight_eq_gapBarrier
    (n : Nat) (hn : 2 ≤ n) {a : Real} (ha : 0 < a) :
    ∃ j : MeshGapIndex n,
      meshGapHeight n a j = gapBarrier n a := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  obtain ⟨x, hx, hnodes, hvalue⟩ :=
    exists_offSpectrum_realGapValue_eq_gapBarrier
      (m + 1) (by omega) ha
  obtain ⟨j, hxgap⟩ :=
    exists_meshGapIndex_of_mem_spectralInterval_of_not_node
      m hx hnodes
  refine ⟨j, le_antisymm
    (meshGapHeight_le_gapBarrier (m + 1) ha j) ?_⟩
  rw [← hvalue]
  exact realGapValue_le_meshGapHeight (m + 1) a x j
    (spectralMeshGap_subset_closedSpectralMeshGap
      (m + 1) a j hxgap)

/-- The global barrier is the supremum of the finite family of individual
mesh-gap heights. -/
theorem gapBarrier_eq_sSup_range_meshGapHeight
    (n : Nat) (hn : 2 ≤ n) {a : Real} (ha : 0 < a) :
    gapBarrier n a =
      sSup (Set.range (fun j : MeshGapIndex n => meshGapHeight n a j)) := by
  obtain ⟨j, hj⟩ := exists_meshGapHeight_eq_gapBarrier n hn ha
  have hbdd :
      BddAbove (Set.range
        (fun k : MeshGapIndex n => meshGapHeight n a k)) := by
    refine ⟨gapBarrier n a, ?_⟩
    rintro y ⟨k, rfl⟩
    exact meshGapHeight_le_gapBarrier n ha k
  apply le_antisymm
  · rw [← hj]
    exact le_csSup hbdd ⟨j, rfl⟩
  · have hnonempty :
        (Set.range
          (fun k : MeshGapIndex n => meshGapHeight n a k)).Nonempty :=
      ⟨meshGapHeight n a j, ⟨j, rfl⟩⟩
    apply csSup_le hnonempty
    rintro y ⟨k, rfl⟩
    exact meshGapHeight_le_gapBarrier n ha k

end

end ConnectedPseudospectrum
