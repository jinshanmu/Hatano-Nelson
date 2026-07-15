import ConnectedPseudospectrum.NoncentralReflectedComparison
import ConnectedPseudospectrum.SpectralInterval

/-!
# Partition of the real spectral mesh into noncentral and central gaps

This module is the combinatorial bridge used in lines 1925--1954 of the
immutable source.  It first partitions the convex hull of the simple path
spectrum into its open adjacent-node gaps.  For a successor matrix of order
`N >= 3`, those gap indices split into four disjoint arithmetic regions:

* positive noncentral indices inherited from a `PositiveHalfGap` with
  predecessor matrix order `N-1`;
* their reflected negative indices;
* the single central index when `N` is even;
* the two zero-adjacent central indices when `N` is odd.

Only the mesh ordering and parity arithmetic are used here.  No central
height comparison is assumed.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- A one-based open-gap index for a path matrix of order `n`.  Its value
`j` labels the gap between zero-based eigenvalue indices `j-1` and `j`. -/
structure MeshGapIndex (n : Nat) where
  /-- The one-based natural-number label of the gap. -/
  val : Nat
  pos : 0 < val
  isLt : val < n

/-- Mesh-gap indices are determined by their one-based natural value. -/
@[ext] theorem MeshGapIndex.ext {n : Nat} {j k : MeshGapIndex n}
    (h : j.val = k.val) : j = k := by
  cases j
  cases k
  simp_all

/-- Lower (smaller-eigenvalue) endpoint index of a mesh gap. -/
def meshGapLowerIndex {n : Nat} (j : MeshGapIndex n) : Fin n :=
  ⟨j.val, j.isLt⟩

/-- Upper (larger-eigenvalue) endpoint index of a mesh gap. -/
def meshGapUpperIndex {n : Nat} (j : MeshGapIndex n) : Fin n :=
  ⟨j.val - 1, (Nat.sub_le _ _).trans_lt j.isLt⟩

@[simp] theorem meshGapLowerIndex_val {n : Nat} (j : MeshGapIndex n) :
    (meshGapLowerIndex j).val = j.val := by
  rfl

@[simp] theorem meshGapUpperIndex_val {n : Nat} (j : MeshGapIndex n) :
    (meshGapUpperIndex j).val = j.val - 1 := by
  rfl

/-- The exact open interval between two adjacent displayed path
eigenvalues. -/
def spectralMeshGap (n : Nat) (a : Real) (j : MeshGapIndex n) : Set Real :=
  Ioo (pathEigenvalue n a (meshGapLowerIndex j))
    (pathEigenvalue n a (meshGapUpperIndex j))

/-- The displayed path eigenvalues are strictly decreasing in their
zero-based index for `a > 0`. -/
theorem pathEigenvalue_strictAnti
    (n : Nat) {a : Real} (ha : 0 < a) :
    StrictAnti (pathEigenvalue n a) := by
  simpa only [pathEigenvalue_eq_symmetricPathEigenvalue] using
    symmetricPathEigenvalue_strictAnti n (Real.sqrt_pos.2 ha)

/-- Every nonspectral point in the real spectral interval lies in an
adjacent-node mesh gap. -/
theorem exists_meshGapIndex_of_mem_spectralInterval_of_not_node
    (m : Nat) {a x : Real}
    (hx : x ∈ spectralInterval (m + 1) a)
    (hnodes : ∀ k : Fin (m + 1),
      x ≠ pathEigenvalue (m + 1) a k) :
    ∃ j : MeshGapIndex (m + 1),
      x ∈ spectralMeshGap (m + 1) a j := by
  rw [spectralInterval, mem_Icc,
    ← pathEigenvalue_last m a, ← pathEigenvalue_zero m a] at hx
  let S : Finset (Fin (m + 1)) :=
    Finset.univ.filter fun k => pathEigenvalue (m + 1) a k < x
  have hlastLt :
      pathEigenvalue (m + 1) a (Fin.last m) < x :=
    lt_of_le_of_ne hx.1 (Ne.symm (hnodes (Fin.last m)))
  have hS : S.Nonempty := by
    refine ⟨Fin.last m, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hlastLt
  let k : Fin (m + 1) := S.min' hS
  have hkMem : k ∈ S := Finset.min'_mem S hS
  have hkLower : pathEigenvalue (m + 1) a k < x := by
    exact (Finset.mem_filter.mp hkMem).2
  have hkPos : 0 < k.val := by
    by_contra hnot
    have hkVal : k.val = 0 := Nat.eq_zero_of_not_pos hnot
    have hkZero : k = 0 := Fin.ext hkVal
    rw [hkZero] at hkLower
    exact (not_lt_of_ge hx.2) hkLower
  let p : Fin (m + 1) := ⟨k.val - 1, by omega⟩
  have hpLt : p < k := by
    change k.val - 1 < k.val
    omega
  have hpNotMem : p ∉ S := by
    intro hpMem
    have hmin : k ≤ p := by
      exact Finset.min'_le S p hpMem
    exact (not_le_of_gt hpLt) hmin
  have hpNotLower : ¬pathEigenvalue (m + 1) a p < x := by
    intro hpLower
    apply hpNotMem
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hpLower
  have hxUpperLe : x ≤ pathEigenvalue (m + 1) a p :=
    le_of_not_gt hpNotLower
  have hxUpper : x < pathEigenvalue (m + 1) a p :=
    lt_of_le_of_ne hxUpperLe (hnodes p)
  let j : MeshGapIndex (m + 1) :=
    ⟨k.val, hkPos, k.isLt⟩
  refine ⟨j, ?_⟩
  constructor
  · simpa only [spectralMeshGap, mem_Ioo, meshGapLowerIndex,
      j, Fin.val_mk] using hkLower
  · have hpEq : meshGapUpperIndex j = p := by
      apply Fin.ext
      rfl
    simpa only [spectralMeshGap, mem_Ioo, hpEq] using hxUpper

/-- A point cannot belong to two distinct adjacent-node mesh gaps. -/
theorem spectralMeshGap_index_unique
    (n : Nat) {a x : Real} (ha : 0 < a)
    (j k : MeshGapIndex n)
    (hj : x ∈ spectralMeshGap n a j)
    (hk : x ∈ spectralMeshGap n a k) :
    j = k := by
  apply MeshGapIndex.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hindex : meshGapLowerIndex j ≤ meshGapUpperIndex k := by
      change j.val ≤ k.val - 1
      omega
    have heig : pathEigenvalue n a (meshGapUpperIndex k) ≤
        pathEigenvalue n a (meshGapLowerIndex j) :=
      (pathEigenvalue_strictAnti n ha).antitone hindex
    exact (not_lt_of_ge heig) (hj.1.trans hk.2)
  · have hindex : meshGapLowerIndex k ≤ meshGapUpperIndex j := by
      change k.val ≤ j.val - 1
      omega
    have heig : pathEigenvalue n a (meshGapUpperIndex j) ≤
        pathEigenvalue n a (meshGapLowerIndex k) :=
      (pathEigenvalue_strictAnti n ha).antitone hindex
    exact (not_lt_of_ge heig) (hk.1.trans hj.2)

/-- Supplementary Dirichlet indices have opposite displayed path
eigenvalues. -/
theorem pathEigenvalue_rev (n : Nat) (a : Real) (k : Fin n) :
    pathEigenvalue n a k.rev = -pathEigenvalue n a k := by
  have hindex : k.rev.val + 1 + (k.val + 1) = n + 1 := by
    simp only [Fin.val_rev]
    omega
  have hindexReal :
      ((k.rev.val + 1 : Nat) : Real) + ((k.val + 1 : Nat) : Real) =
        ((n + 1 : Nat) : Real) := by
    exact_mod_cast hindex
  have hden : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
  have hangle :
      ((k.rev.val + 1 : Nat) : Real) * Real.pi /
          ((n + 1 : Nat) : Real) =
        Real.pi - ((k.val + 1 : Nat) : Real) * Real.pi /
          ((n + 1 : Nat) : Real) := by
    rw [eq_sub_iff_add_eq]
    calc
      ((k.rev.val + 1 : Nat) : Real) * Real.pi /
            ((n + 1 : Nat) : Real) +
          ((k.val + 1 : Nat) : Real) * Real.pi /
            ((n + 1 : Nat) : Real) =
          (((k.rev.val + 1 : Nat) : Real) +
            ((k.val + 1 : Nat) : Real)) * Real.pi /
              ((n + 1 : Nat) : Real) := by ring
      _ = ((n + 1 : Nat) : Real) * Real.pi /
          ((n + 1 : Nat) : Real) := by rw [hindexReal]
      _ = Real.pi := by field_simp [hden.ne']
  unfold pathEigenvalue
  rw [hangle, Real.cos_pi_sub]
  ring

/-- The generic mesh index of the same-index positive successor gap. -/
def successorMeshGapIndex (d : PositiveHalfGap) : MeshGapIndex d.K where
  val := d.j
  pos := d.hj
  isLt := by
    have hjUpper := d.hjUpper
    omega

/-- The generic mesh index of the reflected negative successor gap. -/
def successorReflectedMeshGapIndex
    (d : PositiveHalfGap) : MeshGapIndex d.K where
  val := d.K - d.j
  pos := by
    have hjUpper := d.hjUpper
    omega
  isLt := by
    have hK := d.hK
    have hj := d.hj
    omega

/-- Generic lower endpoint equals the packaged positive successor-gap lower
endpoint. -/
theorem successorMeshGap_lower_endpoint (d : PositiveHalfGap) :
    pathEigenvalue d.K d.a (meshGapLowerIndex (successorMeshGapIndex d)) =
      positiveHalfGapLower d.successor := by
  unfold meshGapLowerIndex successorMeshGapIndex positiveHalfGapLower
  rw [pathEigenvalue_eq_symmetricPathEigenvalue]
  simp only [PositiveHalfGap.successor_K, PositiveHalfGap.successor_j,
    PositiveHalfGap.successor_a, pathRate]
  have hK : d.K + 1 - 1 = d.K := by omega
  unfold symmetricPathEigenvalue pathEigenangle
  dsimp only
  rw [hK]

/-- Generic upper endpoint equals the packaged positive successor-gap upper
endpoint. -/
theorem successorMeshGap_upper_endpoint (d : PositiveHalfGap) :
    pathEigenvalue d.K d.a (meshGapUpperIndex (successorMeshGapIndex d)) =
      positiveHalfGapUpper d.successor := by
  unfold meshGapUpperIndex successorMeshGapIndex positiveHalfGapUpper
  rw [pathEigenvalue_eq_symmetricPathEigenvalue]
  simp only [PositiveHalfGap.successor_K, PositiveHalfGap.successor_j,
    PositiveHalfGap.successor_a, pathRate]
  have hK : d.K + 1 - 1 = d.K := by omega
  unfold symmetricPathEigenvalue pathEigenangle
  dsimp only
  rw [hK]

/-- A packaged positive successor gap is literally its generic adjacent-node
mesh gap. -/
theorem spectralMeshGap_successor_eq_positiveHalfSpectralGap
    (d : PositiveHalfGap) :
    spectralMeshGap d.K d.a (successorMeshGapIndex d) =
      positiveHalfSpectralGap d.successor := by
  unfold spectralMeshGap positiveHalfSpectralGap
  rw [successorMeshGap_lower_endpoint, successorMeshGap_upper_endpoint]

/-- A packaged reflected negative successor gap is literally the generic
mesh gap with reflected index `d.K-d.j`. -/
theorem spectralMeshGap_successorReflected_eq_negativeHalfSpectralGap
    (d : PositiveHalfGap) :
    spectralMeshGap d.K d.a (successorReflectedMeshGapIndex d) =
      reflectedNegativeSpectralGap d.successor := by
  have hj := d.hj
  have hjUpper := d.hjUpper
  have hlowerIndex :
      meshGapLowerIndex (successorReflectedMeshGapIndex d) =
        (meshGapUpperIndex (successorMeshGapIndex d)).rev := by
    apply Fin.ext
    simp only [meshGapLowerIndex_val, meshGapUpperIndex_val, Fin.val_rev,
      successorReflectedMeshGapIndex, successorMeshGapIndex]
    omega
  have hupperIndex :
      meshGapUpperIndex (successorReflectedMeshGapIndex d) =
        (meshGapLowerIndex (successorMeshGapIndex d)).rev := by
    apply Fin.ext
    simp only [meshGapUpperIndex_val, meshGapLowerIndex_val, Fin.val_rev,
      successorReflectedMeshGapIndex, successorMeshGapIndex]
    omega
  rw [reflectedNegativeSpectralGap_eq_Ioo]
  unfold spectralMeshGap
  rw [hlowerIndex, hupperIndex, pathEigenvalue_rev, pathEigenvalue_rev,
    successorMeshGap_upper_endpoint, successorMeshGap_lower_endpoint]

/-- The elementary arithmetic condition ensuring that a successor gap is
already noncentral for the predecessor nodal mesh. -/
theorem meshAngle_le_half_of_two_mul_succ_le
    {N j : Nat} (hN : 0 < N) (h : 2 * (j + 1) ≤ N) :
    ((j + 1 : Nat) : Real) * Real.pi / N ≤ Real.pi / 2 := by
  have hNReal : (0 : Real) < N := by exact_mod_cast hN
  have hcast : (2 : Real) * ((j + 1 : Nat) : Real) ≤ N := by
    exact_mod_cast h
  rw [div_le_iff₀ hNReal]
  nlinarith [Real.pi_pos]

/-- Canonical predecessor `PositiveHalfGap` built from a positive
noncentral successor mesh index. -/
def positiveHalfGapOfMeshIndex
    (N : Nat) (a : Real) (j : MeshGapIndex N)
    (hN : 3 ≤ N) (ha0 : 0 < a) (ha1 : a < 1)
    (hpositive : 2 * (j.val + 1) ≤ N) : PositiveHalfGap where
  K := N
  j := j.val
  a := a
  hK := by omega
  hj := j.pos
  hjUpper := by omega
  ha0 := ha0
  ha1 := ha1
  hhalf := meshAngle_le_half_of_two_mul_succ_le (by omega) hpositive

/-- Building and then reading the positive successor mesh index recovers the
original generic index. -/
theorem successorMeshGapIndex_positiveHalfGapOfMeshIndex
    (N : Nat) (a : Real) (j : MeshGapIndex N)
    (hN : 3 ≤ N) (ha0 : 0 < a) (ha1 : a < 1)
    (hpositive : 2 * (j.val + 1) ≤ N) :
    successorMeshGapIndex
      (positiveHalfGapOfMeshIndex N a j hN ha0 ha1 hpositive) = j := by
  apply MeshGapIndex.ext
  rfl

/-- Building from the reflected positive index recovers the supplied
negative generic gap index. -/
theorem successorReflectedMeshGapIndex_positiveHalfGapOfMeshIndex
    (N : Nat) (a : Real) (j : MeshGapIndex N)
    (hN : 3 ≤ N) (ha0 : 0 < a) (ha1 : a < 1)
    (hnegative : 2 * ((N - j.val) + 1) ≤ N) :
    successorReflectedMeshGapIndex
      (positiveHalfGapOfMeshIndex N a
        ⟨N - j.val,
          by
            have hjLt := j.isLt
            omega,
          by omega⟩ hN ha0 ha1 hnegative) = j := by
  have hjLt := j.isLt
  apply MeshGapIndex.ext
  simp only [successorReflectedMeshGapIndex,
    positiveHalfGapOfMeshIndex]
  omega

/-- The unique central mesh-gap index for an even successor order
`2(m+1)`. -/
def evenCentralMeshGapIndex (m : Nat) :
    MeshGapIndex (2 * (m + 1)) where
  val := m + 1
  pos := by omega
  isLt := by omega

/-- The single central gap of an even-order successor matrix. -/
def evenCentralMeshGap (m : Nat) (a : Real) : Set Real :=
  spectralMeshGap (2 * (m + 1)) a (evenCentralMeshGapIndex m)

/-- Positive zero-adjacent central index for odd successor order `2m+3`. -/
def oddPositiveCentralMeshGapIndex (m : Nat) :
    MeshGapIndex (2 * m + 3) where
  val := m + 1
  pos := by omega
  isLt := by omega

/-- Negative zero-adjacent central index for odd successor order `2m+3`. -/
def oddNegativeCentralMeshGapIndex (m : Nat) :
    MeshGapIndex (2 * m + 3) where
  val := m + 2
  pos := by omega
  isLt := by omega

/-- The two central, zero-adjacent gaps of an odd-order successor matrix. -/
def oddCentralMeshGaps (m : Nat) (a : Real) : Set Real :=
  spectralMeshGap (2 * m + 3) a (oddPositiveCentralMeshGapIndex m) ∪
    spectralMeshGap (2 * m + 3) a (oddNegativeCentralMeshGapIndex m)

/-- Exact arithmetic partition of all gap indices for a successor order
`N >= 3`. -/
theorem meshGapIndex_noncentral_or_central
    (N : Nat) (hN : 3 ≤ N) (j : MeshGapIndex N) :
    2 * (j.val + 1) ≤ N \/
      2 * ((N - j.val) + 1) ≤ N \/
      (∃ m : Nat, N = 2 * (m + 1) ∧ j.val = m + 1) \/
      (∃ m : Nat, N = 2 * m + 3 ∧
        (j.val = m + 1 \/ j.val = m + 2)) := by
  have hjPos := j.pos
  have hjLt := j.isLt
  rcases Nat.even_or_odd N with hEven | hOdd
  · rcases hEven with ⟨q, hq⟩
    by_cases hjLeft : j.val < q
    · exact Or.inl (by omega)
    · by_cases hjCenter : j.val = q
      · refine Or.inr (Or.inr (Or.inl ⟨q - 1, ?_, ?_⟩))
        · omega
        · omega
      · exact Or.inr (Or.inl (by omega))
  · rcases hOdd with ⟨q, hq⟩
    by_cases hjLeft : j.val < q
    · exact Or.inl (by omega)
    · by_cases hjFirst : j.val = q
      · refine Or.inr (Or.inr (Or.inr ⟨q - 1, ?_, ?_⟩))
        · omega
        · left
          omega
      · by_cases hjSecond : j.val = q + 1
        · refine Or.inr (Or.inr (Or.inr ⟨q - 1, ?_, ?_⟩))
          · omega
          · right
            omega
        · exact Or.inr (Or.inl (by omega))

/-- Every nonspectral point of a successor real spectral interval belongs to
a positive noncentral gap, its reflected negative gap, or the parity-specific
central gap set.  The two noncentral witnesses use predecessor parameter
`K=N`, hence compare successor order `N` with predecessor order `N-1`. -/
theorem mem_positive_or_reflected_or_central_meshGap
    (N : Nat) (hN : 3 ≤ N) {a x : Real}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hx : x ∈ spectralInterval N a)
    (hnodes : ∀ k : Fin N, x ≠ pathEigenvalue N a k) :
    (∃ d : PositiveHalfGap,
      d.K = N ∧ d.a = a ∧
        x ∈ positiveHalfSpectralGap d.successor) \/
    (∃ d : PositiveHalfGap,
      d.K = N ∧ d.a = a ∧
        x ∈ reflectedNegativeSpectralGap d.successor) \/
    (∃ m : Nat, N = 2 * (m + 1) ∧
      x ∈ evenCentralMeshGap m a) \/
    (∃ m : Nat, N = 2 * m + 3 ∧
      x ∈ oddCentralMeshGaps m a) := by
  have horder : N - 1 + 1 = N := by omega
  have hxOrder : x ∈ spectralInterval (N - 1 + 1) a := by
    rw [horder]
    exact hx
  have hnodesOrder : ∀ k : Fin (N - 1 + 1),
      x ≠ pathEigenvalue (N - 1 + 1) a k := by
    rw [horder]
    exact hnodes
  obtain ⟨j, hxGap⟩ :
      ∃ j : MeshGapIndex N, x ∈ spectralMeshGap N a j := by
    have hgap := exists_meshGapIndex_of_mem_spectralInterval_of_not_node
      (N - 1) hxOrder hnodesOrder
    exact horder ▸ hgap
  rcases meshGapIndex_noncentral_or_central N hN j with
      hpositive | hnegative | ⟨m, horder, hcenter⟩ |
        ⟨m, horder, hcenter⟩
  · let d := positiveHalfGapOfMeshIndex N a j hN ha0 ha1 hpositive
    have hindex : successorMeshGapIndex d = j := by
      exact successorMeshGapIndex_positiveHalfGapOfMeshIndex
        N a j hN ha0 ha1 hpositive
    refine Or.inl ⟨d, rfl, rfl, ?_⟩
    rw [← spectralMeshGap_successor_eq_positiveHalfSpectralGap, hindex]
    exact hxGap
  · let q : MeshGapIndex N :=
      ⟨N - j.val,
        by
          have hjLt := j.isLt
          omega,
        by
          have hjPos := j.pos
          omega⟩
    let d := positiveHalfGapOfMeshIndex N a q hN ha0 ha1 hnegative
    have hindex : successorReflectedMeshGapIndex d = j := by
      exact successorReflectedMeshGapIndex_positiveHalfGapOfMeshIndex
        N a j hN ha0 ha1 hnegative
    refine Or.inr (Or.inl ⟨d, rfl, rfl, ?_⟩)
    rw [← spectralMeshGap_successorReflected_eq_negativeHalfSpectralGap,
      hindex]
    exact hxGap
  · subst N
    have hj : j = evenCentralMeshGapIndex m := by
      apply MeshGapIndex.ext
      exact hcenter
    refine Or.inr (Or.inr (Or.inl ⟨m, rfl, ?_⟩))
    simpa only [evenCentralMeshGap, hj] using hxGap
  · subst N
    rcases hcenter with hcenter | hcenter
    · have hj : j = oddPositiveCentralMeshGapIndex m := by
        apply MeshGapIndex.ext
        exact hcenter
      refine Or.inr (Or.inr (Or.inr ⟨m, rfl, ?_⟩))
      rw [oddCentralMeshGaps, mem_union]
      exact Or.inl (by simpa only [hj] using hxGap)
    · have hj : j = oddNegativeCentralMeshGapIndex m := by
        apply MeshGapIndex.ext
        exact hcenter
      refine Or.inr (Or.inr (Or.inr ⟨m, rfl, ?_⟩))
      rw [oddCentralMeshGaps, mem_union]
      exact Or.inr (by simpa only [hj] using hxGap)

end

end ConnectedPseudospectrum
