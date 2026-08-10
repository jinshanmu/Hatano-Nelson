import ConnectedPseudospectrum.BoundaryCases
import ConnectedPseudospectrum.MeshGapUtilities

/-!
# Exact gap geometry of the normal Dirichlet path

For the Hermitian endpoint `A_n(1)`, this module identifies the largest
adjacent half-gap of the explicit Dirichlet spectrum with `normalThreshold n`.
It also gives the corresponding strict covering criterion on the closed
spectral interval.  These are purely one-dimensional statements; no matrix
singular-value argument is used here.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- Half the length of the adjacent spectral gap indexed by `j`. -/
def normalAdjacentHalfGap {n : ℕ} (j : MeshGapIndex n) : ℝ :=
  (pathEigenvalue n 1 (meshGapUpperIndex j) -
    pathEigenvalue n 1 (meshGapLowerIndex j)) / 2

/-- Every adjacent half-gap has positive length. -/
theorem normalAdjacentHalfGap_pos {n : ℕ} (j : MeshGapIndex n) :
    0 < normalAdjacentHalfGap j := by
  have hindex : meshGapUpperIndex j < meshGapLowerIndex j := by
    change j.val - 1 < j.val
    have hj := j.pos
    omega
  have hnodes := pathEigenvalue_strictAnti n zero_lt_one hindex
  exact div_pos (sub_pos.mpr hnodes) (by norm_num)

/-- The elementary sine-product formula for an adjacent half-gap. -/
theorem normalAdjacentHalfGap_eq_sine_product {n : ℕ}
    (j : MeshGapIndex n) :
    normalAdjacentHalfGap j =
      2 * Real.sin (Real.pi / (2 * (n + 1 : ℝ))) *
        Real.sin ((2 * (j.val : ℝ) + 1) * Real.pi /
          (2 * (n + 1 : ℝ))) := by
  unfold normalAdjacentHalfGap pathEigenvalue
  simp only [Real.sqrt_one, mul_one, Nat.cast_add, Nat.cast_one,
    meshGapUpperIndex_val, meshGapLowerIndex_val]
  have hj : j.val - 1 + 1 = j.val := by
    have hjpos := j.pos
    omega
  have hjReal : ((j.val - 1 : ℕ) : ℝ) + 1 = (j.val : ℝ) := by
    exact_mod_cast hj
  rw [hjReal]
  let θ := (j.val : ℝ) * Real.pi / ((n : ℝ) + 1)
  let φ := ((j.val : ℝ) + 1) * Real.pi / ((n : ℝ) + 1)
  let b := Real.pi / (2 * ((n : ℝ) + 1))
  let μ := (2 * (j.val : ℝ) + 1) * Real.pi /
    (2 * ((n : ℝ) + 1))
  change (2 * Real.cos θ - 2 * Real.cos φ) / 2 =
    2 * Real.sin b * Real.sin μ
  have hdiff : (θ - φ) / 2 = -b := by
    dsimp [θ, φ, b]
    field_simp
    ring
  have havg : (θ + φ) / 2 = μ := by
    dsimp [θ, φ, μ]
    field_simp
    ring
  rw [show (2 * Real.cos θ - 2 * Real.cos φ) / 2 =
      Real.cos θ - Real.cos φ by ring,
    Real.cos_sub_cos, hdiff, havg, Real.sin_neg]
  ring

/-- Every adjacent half-gap is bounded by the parity-dependent normal
threshold. -/
theorem normalAdjacentHalfGap_le_normalThreshold {n : ℕ}
    (j : MeshGapIndex n) :
    normalAdjacentHalfGap j ≤ normalThreshold n := by
  rcases n.even_or_odd' with ⟨m, rfl | rfl⟩
  · rw [normalAdjacentHalfGap_eq_sine_product, normalThreshold_even]
    let x : ℝ := Real.pi / (2 * (((2 * m : ℕ) : ℝ) + 1))
    have hm : 1 ≤ m := by
      have := j.pos
      have := j.isLt
      omega
    have hx0 : 0 < x := by dsimp [x]; positivity
    have hxpi : x < Real.pi := by
      dsimp [x]
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      apply div_lt_self Real.pi_pos
      push_cast
      nlinarith
    have hsin : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
    have hmid := Real.sin_le_one
      ((2 * (j.val : ℝ) + 1) * Real.pi /
        (2 * (((2 * m : ℕ) : ℝ) + 1)))
    change 2 * Real.sin x *
        Real.sin ((2 * (j.val : ℝ) + 1) * Real.pi /
          (2 * (((2 * m : ℕ) : ℝ) + 1))) ≤
      2 * Real.sin x
    nlinarith
  · rw [normalAdjacentHalfGap_eq_sine_product, normalThreshold_odd]
    let x : ℝ := Real.pi / (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))
    let y : ℝ := (2 * (j.val : ℝ) + 1) * x
    have hm : 1 ≤ m := by
      have := j.pos
      have := j.isLt
      omega
    have hx0 : 0 < x := by dsimp [x]; positivity
    have hxpi : x < Real.pi := by
      dsimp [x]
      have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
      apply div_lt_self Real.pi_pos
      push_cast
      nlinarith
    have hsinx : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
    have hhalf : (2 * (m : ℝ) + 2) * x = Real.pi / 2 := by
      dsimp [x]
      push_cast
      field_simp
      ring
    have hyBound : Real.sin y ≤ Real.cos x := by
      by_cases hjm : j.val ≤ m
      · have hy0 : 0 ≤ y := by
          dsimp [y]
          positivity
        have hyUpper : y ≤ Real.pi / 2 - x := by
          have hjmR : (j.val : ℝ) ≤ m := by exact_mod_cast hjm
          dsimp [y]
          nlinarith
        rw [← Real.sin_pi_div_two_sub x]
        exact Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [Real.pi_pos]) (by linarith [hx0]) hyUpper
      · have hjm' : m + 1 ≤ j.val := by omega
        have hjUpper : j.val ≤ 2 * m := by
          have hjlt := j.isLt
          omega
        have hjmR : (m : ℝ) + 1 ≤ j.val := by exact_mod_cast hjm'
        have hjUpperR : (j.val : ℝ) ≤ 2 * m := by exact_mod_cast hjUpper
        have hreflect0 : 0 ≤ Real.pi - y := by
          dsimp [y]
          nlinarith
        have hreflectUpper : Real.pi - y ≤ Real.pi / 2 - x := by
          dsimp [y]
          nlinarith
        rw [← Real.sin_pi_sub y, ← Real.sin_pi_div_two_sub x]
        exact Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [Real.pi_pos]) (by linarith [hx0]) hreflectUpper
    have htwox :
        Real.pi / (((2 * m + 1 : ℕ) : ℝ) + 1) = 2 * x := by
      dsimp [x]
      field_simp
    have hy :
        (2 * (j.val : ℝ) + 1) * Real.pi /
            (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) = y := by
      dsimp [x, y]
      ring
    rw [htwox]
    rw [hy]
    change 2 * Real.sin x * Real.sin y ≤ Real.sin (2 * x)
    rw [Real.sin_two_mul]
    exact mul_le_mul_of_nonneg_left hyBound (by positivity)

/-- A central adjacent gap attains the normal threshold in every dimension
`n ≥ 2`. -/
theorem exists_normalAdjacentHalfGap_eq_normalThreshold
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ j : MeshGapIndex n,
      normalAdjacentHalfGap j = normalThreshold n := by
  rcases n.even_or_odd' with ⟨m, rfl | rfl⟩
  · have hm : 1 ≤ m := by omega
    let j : MeshGapIndex (2 * m) := ⟨m, by omega, by omega⟩
    refine ⟨j, ?_⟩
    rw [normalAdjacentHalfGap_eq_sine_product, normalThreshold_even]
    have hangle :
        (2 * (j.val : ℝ) + 1) * Real.pi /
            (2 * (((2 * m : ℕ) : ℝ) + 1)) =
          Real.pi / 2 := by
      dsimp [j]
      push_cast
      field_simp
    rw [hangle, Real.sin_pi_div_two, mul_one]
  · have hm : 1 ≤ m := by omega
    let j : MeshGapIndex (2 * m + 1) := ⟨m, by omega, by omega⟩
    refine ⟨j, ?_⟩
    rw [normalAdjacentHalfGap_eq_sine_product, normalThreshold_odd]
    let x : ℝ := Real.pi /
      (2 * (((2 * m + 1 : ℕ) : ℝ) + 1))
    have hangle :
        (2 * (j.val : ℝ) + 1) * Real.pi /
            (2 * (((2 * m + 1 : ℕ) : ℝ) + 1)) =
          Real.pi / 2 - x := by
      dsimp [j, x]
      push_cast
      field_simp
      ring
    have htwox :
        Real.pi / (((2 * m + 1 : ℕ) : ℝ) + 1) = 2 * x := by
      dsimp [x]
      field_simp
    rw [hangle, Real.sin_pi_div_two_sub, htwox, Real.sin_two_mul]

/-- At the midpoint of a gap, every spectral node is at least the half-gap
away. -/
theorem normalAdjacentHalfGap_le_abs_midpoint_sub_pathEigenvalue
    {n : ℕ} (j : MeshGapIndex n) (k : Fin n) :
    normalAdjacentHalfGap j ≤
      |(pathEigenvalue n 1 (meshGapLowerIndex j) +
          pathEigenvalue n 1 (meshGapUpperIndex j)) / 2 -
        pathEigenvalue n 1 k| := by
  let lo := pathEigenvalue n 1 (meshGapLowerIndex j)
  let hi := pathEigenvalue n 1 (meshGapUpperIndex j)
  let x := (lo + hi) / 2
  have hgap : normalAdjacentHalfGap j = (hi - lo) / 2 := by
    rfl
  by_cases hk : k.val < j.val
  · have hkUpper : k ≤ meshGapUpperIndex j := by
      change k.val ≤ j.val - 1
      omega
    have hnode : hi ≤ pathEigenvalue n 1 k :=
      (pathEigenvalue_strictAnti n zero_lt_one).antitone hkUpper
    have habs : -(x - pathEigenvalue n 1 k) ≤
        |x - pathEigenvalue n 1 k| := neg_le_abs _
    have hxhalf : (hi - lo) / 2 = -(x - hi) := by
      dsimp [x]
      ring
    calc
      normalAdjacentHalfGap j = (hi - lo) / 2 := hgap
      _ = -(x - hi) := hxhalf
      _ ≤ -(x - pathEigenvalue n 1 k) := by linarith
      _ ≤ |x - pathEigenvalue n 1 k| := habs
  · have hLowerK : meshGapLowerIndex j ≤ k := by
      change j.val ≤ k.val
      omega
    have hnode : pathEigenvalue n 1 k ≤ lo :=
      (pathEigenvalue_strictAnti n zero_lt_one).antitone hLowerK
    have habs : x - pathEigenvalue n 1 k ≤
        |x - pathEigenvalue n 1 k| := le_abs_self _
    have hxhalf : (hi - lo) / 2 = x - lo := by
      dsimp [x]
      ring
    calc
      normalAdjacentHalfGap j = (hi - lo) / 2 := hgap
      _ = x - lo := hxhalf
      _ ≤ x - pathEigenvalue n 1 k := by linarith
      _ ≤ |x - pathEigenvalue n 1 k| := habs

/-- The open `ε`-neighbourhoods of the normal path eigenvalues cover the
entire closed spectral interval exactly when the largest adjacent half-gap
is strictly smaller than `ε`. -/
theorem forall_mem_spectralInterval_exists_abs_sub_pathEigenvalue_lt_iff
    (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) :
    (∀ x ∈ spectralInterval n 1,
        ∃ k : Fin n, |x - pathEigenvalue n 1 k| < ε) ↔
      normalThreshold n < ε := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  constructor
  · intro hcover
    obtain ⟨j, hj⟩ :=
      exists_normalAdjacentHalfGap_eq_normalThreshold (m + 1) (by omega)
    let lo := pathEigenvalue (m + 1) 1 (meshGapLowerIndex j)
    let hi := pathEigenvalue (m + 1) 1 (meshGapUpperIndex j)
    let x := (lo + hi) / 2
    have hgapPos := normalAdjacentHalfGap_pos j
    have hxGap : x ∈ spectralMeshGap (m + 1) 1 j := by
      rw [spectralMeshGap, mem_Ioo]
      change lo < x ∧ x < hi
      change 0 < (hi - lo) / 2 at hgapPos
      change lo < (lo + hi) / 2 ∧ (lo + hi) / 2 < hi
      constructor <;> nlinarith
    have hxInterval : x ∈ spectralInterval (m + 1) 1 :=
      spectralMeshGap_subset_spectralInterval (m + 1) zero_lt_one j hxGap
    obtain ⟨k, hk⟩ := hcover x hxInterval
    have hlower :=
      normalAdjacentHalfGap_le_abs_midpoint_sub_pathEigenvalue j k
    change normalAdjacentHalfGap j ≤ |x - pathEigenvalue (m + 1) 1 k| at hlower
    rw [hj] at hlower
    exact hlower.trans_lt hk
  · intro hthreshold x hxInterval
    obtain ⟨jCentral, hjCentral⟩ :=
      exists_normalAdjacentHalfGap_eq_normalThreshold (m + 1) (by omega)
    have hthresholdPos : 0 < normalThreshold (m + 1) := by
      rw [← hjCentral]
      exact normalAdjacentHalfGap_pos jCentral
    have hε : 0 < ε := hthresholdPos.trans hthreshold
    by_cases hnode : ∃ k : Fin (m + 1), x = pathEigenvalue (m + 1) 1 k
    · obtain ⟨k, rfl⟩ := hnode
      exact ⟨k, by simpa using hε⟩
    · have hnodes : ∀ k : Fin (m + 1),
          x ≠ pathEigenvalue (m + 1) 1 k := by
        intro k hk
        exact hnode ⟨k, hk⟩
      obtain ⟨j, hxGap⟩ :=
        exists_meshGapIndex_of_mem_spectralInterval_of_not_node
          m hxInterval hnodes
      let lo := pathEigenvalue (m + 1) 1 (meshGapLowerIndex j)
      let hi := pathEigenvalue (m + 1) 1 (meshGapUpperIndex j)
      let midpoint := (lo + hi) / 2
      have hhalf : normalAdjacentHalfGap j = (hi - lo) / 2 := rfl
      have hbound : normalAdjacentHalfGap j ≤ normalThreshold (m + 1) :=
        normalAdjacentHalfGap_le_normalThreshold j
      rw [spectralMeshGap, mem_Ioo] at hxGap
      by_cases hxmid : x ≤ midpoint
      · refine ⟨meshGapLowerIndex j, ?_⟩
        rw [abs_of_pos (sub_pos.mpr hxGap.1)]
        calc
          x - lo ≤ normalAdjacentHalfGap j := by
            rw [hhalf]
            change x ≤ (lo + hi) / 2 at hxmid
            nlinarith
          _ ≤ normalThreshold (m + 1) := hbound
          _ < ε := hthreshold
      · refine ⟨meshGapUpperIndex j, ?_⟩
        rw [abs_of_neg (sub_neg.mpr hxGap.2)]
        calc
          -(x - hi) ≤ normalAdjacentHalfGap j := by
            rw [hhalf]
            change ¬x ≤ (lo + hi) / 2 at hxmid
            nlinarith
          _ ≤ normalThreshold (m + 1) := hbound
          _ < ε := hthreshold

end

end ConnectedPseudospectrum
