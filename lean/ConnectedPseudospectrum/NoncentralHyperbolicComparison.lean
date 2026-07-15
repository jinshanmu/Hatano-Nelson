import ConnectedPseudospectrum.ChordFamilyFoldedRoot
import ConnectedPseudospectrum.NoncentralHyperbolicScale

/-!
# The hyperbolic part of the noncentral gap comparison

This module implements the comparison in lines 1274--1308 of the immutable
source.  If the endpoint-side outer coordinate for the `(N+1)` problem is
`cosh eta`, rescaling the inner angle by `N/(N+1)` gives a strictly lower
level for the `N` problem.  The rightmost return to that lower level is in
the same nodal interval.  The same hyperbolic outer coordinate is still on
the endpoint side for the `N` problem, and the resulting chord height is
strictly larger.

The argument includes `eta = 0`; no division by `sinh eta` is used at that
endpoint.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

namespace PositiveHalfGap

/-- The same-index positive-half gap for the successor matrix size. -/
def successor (d : PositiveHalfGap) : PositiveHalfGap where
  K := d.K + 1
  j := d.j
  a := d.a
  hK := d.hK.trans (Nat.le_succ d.K)
  hj := d.hj
  hjUpper := d.hjUpper.trans (Nat.lt_succ_self d.K)
  ha0 := d.ha0
  ha1 := d.ha1
  hhalf := by
    have hKNat : 0 < d.K := Nat.zero_lt_two.trans_le d.hK
    have hKpos : (0 : ℝ) < d.K := by exact_mod_cast hKNat
    have hKsuccPos : (0 : ℝ) < (d.K : ℝ) + 1 := by positivity
    have hnum : 0 ≤ ((d.j : ℝ) + 1) * Real.pi := by positivity
    calc
      ((d.j + 1 : ℕ) : ℝ) * Real.pi / (d.K + 1 : ℕ) ≤
          ((d.j + 1 : ℕ) : ℝ) * Real.pi / d.K := by
        push_cast
        rw [div_le_div_iff₀ hKsuccPos hKpos]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hnum
      _ ≤ Real.pi / 2 := d.hhalf

@[simp] theorem successor_K (d : PositiveHalfGap) : d.successor.K = d.K + 1 := rfl

@[simp] theorem successor_j (d : PositiveHalfGap) : d.successor.j = d.j := rfl

@[simp] theorem successor_a (d : PositiveHalfGap) : d.successor.a = d.a := rfl

/-- Every packaged positive-half noncentral gap has size at least three. -/
theorem three_le_size (d : PositiveHalfGap) : 3 ≤ d.K := by
  have hjOne : 1 ≤ d.j := d.hj
  have hthree : 3 ≤ d.j + 2 := by
    simpa only [Nat.one_add, Nat.succ_eq_add_one, Nat.add_assoc] using
      Nat.add_le_add_right hjOne 2
  have hjUpper : d.j + 2 ≤ d.K := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (Nat.succ_le_iff.mpr d.hjUpper)
  exact hthree.trans hjUpper

/-- The source rescaling `theta = N theta₀/(N+1)`, packaged in the
successor gap's closed angular interval. -/
def scaleToSuccessor (d : PositiveHalfGap) (θ0 : d.Angle) : d.successor.Angle := by
  let κ := noncentralScale d.K
  have hOneTwo : 1 ≤ 2 := by norm_num
  have hK1 : 1 ≤ d.K := hOneTwo.trans d.hK
  have hκ0 : 0 < κ := noncentralScale_pos hK1
  have hlower : κ * d.angleLower = d.successor.angleLower := by
    dsimp only [κ, noncentralScale, angleLower, successor]
    field_simp
  have hupper : κ * d.angleUpper = d.successor.angleUpper := by
    dsimp only [κ, noncentralScale, angleUpper, successor]
    field_simp
  refine ⟨κ * (θ0 : ℝ), ?_, ?_⟩
  · rw [← hlower]
    exact mul_le_mul_of_nonneg_left θ0.2.1 hκ0.le
  · rw [← hupper]
    exact mul_le_mul_of_nonneg_left θ0.2.2 hκ0.le

@[simp] theorem coe_scaleToSuccessor
    (d : PositiveHalfGap) (θ0 : d.Angle) :
    (d.scaleToSuccessor θ0 : ℝ) = noncentralScale d.K * (θ0 : ℝ) := by
  rfl

theorem scaleToSuccessor_lt
    (d : PositiveHalfGap) {θ0 : d.Angle}
    (hleft : d.angleLower < θ0) :
    (d.scaleToSuccessor θ0 : ℝ) < (θ0 : ℝ) := by
  have hθ0 : 0 < (θ0 : ℝ) :=
    d.angleLower_pos.trans hleft
  have hκ := noncentralScale_lt_one d.K
  simpa only [coe_scaleToSuccessor] using
    (mul_lt_of_lt_one_left hθ0 hκ)

theorem scaleToSuccessor_interior
    (d : PositiveHalfGap) {θ0 : d.Angle}
    (hleft : d.angleLower < θ0) (hright : θ0 < d.angleUpper) :
    d.successor.angleLower < d.scaleToSuccessor θ0 ∧
      (d.scaleToSuccessor θ0 : ℝ) < d.successor.angleUpper := by
  let κ := noncentralScale d.K
  have hOneTwo : 1 ≤ 2 := by norm_num
  have hK1 : 1 ≤ d.K := hOneTwo.trans d.hK
  have hκ0 : 0 < κ := noncentralScale_pos hK1
  have hlower : κ * d.angleLower = d.successor.angleLower := by
    dsimp only [κ, noncentralScale, angleLower, successor]
    field_simp
  have hupper : κ * d.angleUpper = d.successor.angleUpper := by
    dsimp only [κ, noncentralScale, angleUpper, successor]
    field_simp
  constructor
  · rw [← hlower, coe_scaleToSuccessor]
    exact mul_lt_mul_of_pos_left hleft hκ0
  · rw [← hupper, coe_scaleToSuccessor]
    exact mul_lt_mul_of_pos_left hright hκ0

end PositiveHalfGap

/-- A solution of a prescribed inner level which is the rightmost solution
between `theta₀` and the right nodal endpoint.  The final universal clause
makes "rightmost" intrinsic and gives uniqueness without choosing a local
coordinate chart. -/
def IsRightmostInnerSolution
    (d : PositiveHalfGap) (θ0 : d.Angle) (level : ℝ)
    (θhat : d.Angle) : Prop :=
  (θ0 : ℝ) < θhat ∧
    (θhat : ℝ) < d.angleUpper ∧
    chordPhi d.K d.a θhat = level ∧
    ∀ φ : d.Angle,
      (θ0 : ℝ) ≤ φ →
      chordPhi d.K d.a φ = level →
      (φ : ℝ) ≤ θhat

/-- The hyperbolic channel is positive before its terminal radical endpoint,
including at `eta=0`. -/
theorem chordPsi_pos_before_endpoint
    {K : ℕ} (hK : 2 ≤ K) {a η : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hη : η ∈ Ico (0 : ℝ) (pathLogParameter a)) :
    0 < chordPsi K a η := by
  unfold chordPsi
  exact mul_pos
    (halfHypRadical_pos_of_lt_pathLogParameter ha0 ha1 hη.1 hη.2)
    (chebyshevU_cosh_pos K hK hη.1)

/-- A level strictly below the value at `theta₀` has a unique rightmost
return before the right nodal endpoint.  Existence is an IVT/compactness
argument, so the statement also covers a possible tangency elsewhere in the
lobe; the strict endpoint inequalities place the selected return on the
descending side. -/
theorem existsUnique_rightmostInnerSolution
    (d : PositiveHalfGap) (θ0 : d.Angle) {η : ℝ}
    (hη : η ∈ Ico (0 : ℝ) (pathLogParameter d.a))
    (hlevel : chordPsi d.K d.a η < chordPhi d.K d.a θ0) :
    ∃! θhat : d.Angle,
      IsRightmostInnerSolution d θ0 (chordPsi d.K d.a η) θhat := by
  let level := chordPsi d.K d.a η
  let S : Set ℝ :=
    Icc (θ0 : ℝ) d.angleUpper ∩
      {t : ℝ | chordPhi d.K d.a t = level}
  have hrightZero : chordPhi d.K d.a d.angleUpper = 0 := by
    simpa only [PositiveHalfGap.angleUpper] using
      chordPhi_nodal (K := d.K) (k := d.j + 1) d.hK (Nat.succ_pos d.j)
        d.hjUpper d.a
  have hlevelPos : 0 < level := by
    exact chordPsi_pos_before_endpoint d.hK d.ha0 d.ha1 hη
  have hlevelRange : level ∈
      Icc (chordPhi d.K d.a d.angleUpper)
        (chordPhi d.K d.a (θ0 : ℝ)) := by
    rw [hrightZero]
    exact ⟨hlevelPos.le, hlevel.le⟩
  have hcontinuous : ContinuousOn (chordPhi d.K d.a)
      (Icc (θ0 : ℝ) d.angleUpper) :=
    (continuous_chordPhi d.K d.a).continuousOn
  obtain ⟨t, ht, htLevel⟩ :=
    intermediate_value_Icc' θ0.2.2 hcontinuous hlevelRange
  have hSne : S.Nonempty := by
    refine ⟨t, ht, ?_⟩
    exact htLevel
  have hclosedLevel : IsClosed {t : ℝ | chordPhi d.K d.a t = level} :=
    isClosed_eq (continuous_chordPhi d.K d.a) continuous_const
  have hScompact : IsCompact S :=
    isCompact_Icc.inter_right hclosedLevel
  obtain ⟨tmax, htmaxS, htmax⟩ :=
    hScompact.exists_isMaxOn hSne continuous_id.continuousOn
  have htmaxBounds : tmax ∈ Icc (θ0 : ℝ) d.angleUpper := htmaxS.1
  let θhat : d.Angle :=
    ⟨tmax, θ0.2.1.trans htmaxBounds.1, htmaxBounds.2⟩
  have hθhatLevel : chordPhi d.K d.a θhat = level := htmaxS.2
  have hθ0lt : (θ0 : ℝ) < θhat := by
    refine lt_of_le_of_ne htmaxBounds.1 ?_
    intro heq
    have : chordPhi d.K d.a θ0 = level := by
      simpa only [θhat, heq] using hθhatLevel
    exact (ne_of_lt hlevel) this.symm
  have hθhatUpper : (θhat : ℝ) < d.angleUpper := by
    refine lt_of_le_of_ne htmaxBounds.2 ?_
    intro heq
    have : level = 0 := by
      calc
        level = chordPhi d.K d.a θhat := hθhatLevel.symm
        _ = chordPhi d.K d.a d.angleUpper := by rw [heq]
        _ = 0 := hrightZero
    exact (ne_of_gt hlevelPos) this
  have hgreatest : ∀ φ : d.Angle,
      (θ0 : ℝ) ≤ φ →
      chordPhi d.K d.a φ = level →
      (φ : ℝ) ≤ θhat := by
    intro φ hθ0φ hφLevel
    have hφS : (φ : ℝ) ∈ S :=
      ⟨⟨hθ0φ, φ.2.2⟩, hφLevel⟩
    simpa only [id_eq] using htmax hφS
  refine ⟨θhat, ⟨hθ0lt, hθhatUpper, hθhatLevel, hgreatest⟩, ?_⟩
  intro φ hφ
  apply Subtype.ext
  apply le_antisymm
  · exact hgreatest φ hφ.1.le hφ.2.2.1
  · exact hφ.2.2.2 θhat hθ0lt.le hθhatLevel

/-- The raw quotient which remains after cancelling the common hyperbolic
radical in `Psi_N/Psi_(N+1)`. -/
def successorSinhRatio (N : ℕ) (η : ℝ) : ℝ :=
  Real.sinh ((N : ℝ) * η) /
    Real.sinh (((N + 1 : ℕ) : ℝ) * η)

/-- Strict convexity of `sinh` in the source's dilation form. -/
theorem mul_sinh_lt_sinh_mul
    {t η : ℝ} (ht : 1 < t) (hη : 0 < η) :
    t * Real.sinh η < Real.sinh (t * η) := by
  let β : ℝ := 1 / t
  have ht0 : 0 < t := zero_lt_one.trans ht
  have hβ0 : 0 < β := by dsimp only [β]; positivity
  have hβ1 : β < 1 := by
    dsimp only [β]
    exact (div_lt_one ht0).2 ht
  have hty : 0 < t * η := mul_pos ht0 hη
  have hstrict := strictConvexOn_sinh_Ici.2
    (le_refl (0 : ℝ)) hty.le
    (ne_of_lt hty) (sub_pos.mpr hβ1) hβ0 (by ring)
  have hargument : β * (t * η) = η := by
    dsimp only [β]
    field_simp
  have hstrict' :
      Real.sinh (β * (t * η)) < β * Real.sinh (t * η) := by
    simpa only [smul_eq_mul, Real.sinh_zero, mul_zero, zero_add,
      sub_mul, one_mul] using hstrict
  have hright : β * Real.sinh (t * η) = Real.sinh (t * η) / t := by
    dsimp only [β]
    ring
  have hdiv : Real.sinh η < Real.sinh (t * η) / t :=
    calc
      Real.sinh η = Real.sinh (β * (t * η)) := by rw [hargument]
      _ < β * Real.sinh (t * η) := hstrict'
      _ = Real.sinh (t * η) / t := hright
  simpa only [mul_comm] using (lt_div_iff₀ ht0).1 hdiv

/-- The derivative of the successor hyperbolic quotient. -/
theorem hasDerivAt_successorSinhRatio
    {N : ℕ} {eta : ℝ} (heta : eta ≠ 0) :
    HasDerivAt (successorSinhRatio N)
      ((((N : ℝ) * Real.cosh ((N : ℝ) * eta)) *
            Real.sinh (((N + 1 : ℕ) : ℝ) * eta) -
          Real.sinh ((N : ℝ) * eta) *
            (((N + 1 : ℕ) : ℝ) *
              Real.cosh (((N + 1 : ℕ) : ℝ) * eta))) /
        Real.sinh (((N + 1 : ℕ) : ℝ) * eta) ^ 2) eta := by
  have hnum :
      HasDerivAt (fun x : ℝ => Real.sinh ((N : ℝ) * x))
        (Real.cosh ((N : ℝ) * eta) * (N : ℝ)) eta := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id eta).const_mul (N : ℝ)).sinh
  have hden :
      HasDerivAt
        (fun x : ℝ => Real.sinh (((N + 1 : ℕ) : ℝ) * x))
        (Real.cosh (((N + 1 : ℕ) : ℝ) * eta) *
          ((N + 1 : ℕ) : ℝ)) eta := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id eta).const_mul (((N + 1 : ℕ) : ℝ))).sinh
  have hdenNe : Real.sinh (((N + 1 : ℕ) : ℝ) * eta) ≠ 0 := by
    apply Real.sinh_ne_zero.mpr
    exact mul_ne_zero (by positivity) heta
  unfold successorSinhRatio
  convert hnum.div hden hdenNe using 1
  simp only [Nat.cast_add, Nat.cast_one]
  ring

/-- The product-to-sum numerator in the derivative comparison. -/
theorem successorSinhRatio_derivNumerator_neg
    {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η) :
    (N : ℝ) * Real.cosh ((N : ℝ) * η) *
          Real.sinh (((N + 1 : ℕ) : ℝ) * η) -
        Real.sinh ((N : ℝ) * η) *
          (((N + 1 : ℕ) : ℝ) *
            Real.cosh (((N + 1 : ℕ) : ℝ) * η)) < 0 := by
  let n : ℝ := N
  let m : ℝ := N + 1
  let q : ℝ := 2 * n + 1
  have hn : 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast hN
  have hq : 1 < q := by dsimp only [q]; linarith
  have hdilate : q * Real.sinh η < Real.sinh (q * η) :=
    mul_sinh_lt_sinh_mul hq hη
  have hm : m = n + 1 := by rfl
  have hsum :
      Real.sinh (q * η) =
        Real.sinh (m * η) * Real.cosh (n * η) +
          Real.cosh (m * η) * Real.sinh (n * η) := by
    rw [← Real.sinh_add]
    congr 1
    dsimp only [q]
    rw [hm]
    ring
  have hdiff :
      Real.sinh η =
        Real.sinh (m * η) * Real.cosh (n * η) -
          Real.cosh (m * η) * Real.sinh (n * η) := by
    rw [← Real.sinh_sub]
    congr 1
    rw [hm]
    ring
  have hidentity :
      m * Real.cosh (m * η) * Real.sinh (n * η) -
          n * Real.cosh (n * η) * Real.sinh (m * η) =
        (Real.sinh (q * η) - q * Real.sinh η) / 2 := by
    rw [hsum, hdiff, hm]
    dsimp only [q]
    ring
  have hpositive :
      0 < m * Real.cosh (m * η) * Real.sinh (n * η) -
          n * Real.cosh (n * η) * Real.sinh (m * η) := by
    rw [hidentity]
    linarith
  dsimp only [m, n] at hpositive
  norm_num only [Nat.cast_add, Nat.cast_one] at hpositive ⊢
  nlinarith

/-- The raw quotient `sinh(N eta)/sinh((N+1) eta)` is strictly decreasing
for positive `eta`.  This is the differential statement behind the source's
`t coth(t eta)` calculation. -/
theorem successorSinhRatio_strictAntiOn_Ioi
    {N : ℕ} (hN : 1 ≤ N) :
    StrictAntiOn (successorSinhRatio N) (Ioi (0 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
  · intro eta heta
    have hetaPos : 0 < eta := by
      simpa only [mem_Ioi] using heta
    exact (hasDerivAt_successorSinhRatio
      (ne_of_gt hetaPos)).continuousAt.continuousWithinAt
  · intro eta heta
    have hetaPos : 0 < eta := by
      simpa only [interior_Ioi, mem_Ioi] using heta
    have hderiv := hasDerivAt_successorSinhRatio
      (N := N) (ne_of_gt hetaPos)
    rw [hderiv.deriv]
    exact div_neg_of_neg_of_pos
      (successorSinhRatio_derivNumerator_neg hN hetaPos)
      (sq_pos_of_pos (Real.sinh_pos_iff.mpr (mul_pos (by positivity) hetaPos)))

/-- Cancelling the common positive radical identifies the positive-coordinate
`Psi` quotient with the raw successor `sinh` quotient. -/
theorem chordPsi_successor_ratio_eq
    {N : ℕ} (hN : 2 ≤ N) {a η : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (hη0 : 0 < η) (hηh : η < pathLogParameter a) :
    chordPsi N a η / chordPsi (N + 1) a η =
      successorSinhRatio N η := by
  have hradical : 0 < halfHypRadical a η :=
    halfHypRadical_pos_of_lt_pathLogParameter ha0 ha1 hη0.le hηh
  have hsinh : Real.sinh η ≠ 0 :=
    Real.sinh_ne_zero.mpr (ne_of_gt hη0)
  rw [chordPsi_eq_sinh_quotient a η hN (ne_of_gt hη0),
    chordPsi_eq_sinh_quotient a η (hN.trans (Nat.le_succ N))
      (ne_of_gt hη0)]
  unfold successorSinhRatio
  field_simp [ne_of_gt hradical, hsinh]

/-- The full continuous quotient `Psi_N/Psi_(N+1)` is strictly decreasing
on `[0,h)`.  The proof separates the continuous value at zero from the
ordinary positive-coordinate derivative calculation. -/
theorem chordPsi_successor_ratio_strictAntiOn
    {N : ℕ} (hN : 3 ≤ N) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    StrictAntiOn
      (fun η : ℝ => chordPsi N a η / chordPsi (N + 1) a η)
      (Ico (0 : ℝ) (pathLogParameter a)) := by
  have hN2 : 2 ≤ N := (by norm_num : 2 ≤ 3).trans hN
  have hOneTwo : 1 ≤ 2 := by norm_num
  have hN1 : 1 ≤ N := hOneTwo.trans hN2
  intro η hη ξ hξ hηξ
  change chordPsi N a ξ / chordPsi (N + 1) a ξ <
    chordPsi N a η / chordPsi (N + 1) a η
  by_cases hη0 : η = 0
  · subst η
    rw [chordPsi_ratio_zero_eq_noncentralScale hN ha0 ha1]
    exact chordPsi_ratio_lt_noncentralScale hN ha0 ha1
      (by linarith [hξ.1]) hξ.2
  · have hηPos : 0 < η := lt_of_le_of_ne hη.1 (Ne.symm hη0)
    rw [chordPsi_successor_ratio_eq hN2
        ha0 ha1 hηPos hη.2,
      chordPsi_successor_ratio_eq hN2
        ha0 ha1 (hηPos.trans hηξ) hξ.2]
    exact successorSinhRatio_strictAntiOn_Ioi hN1
      hηPos (hηPos.trans hηξ) hηξ

/-- If the selected endpoint-side outer variable for size `N+1` is
`cosh eta`, then a size-`N` inner point at the `Psi_N(eta)` level selects
the same outer variable.  This is the endpoint-side preservation argument
of lines 1283--1302. -/
theorem hyperbolicOuterCoordinate_preserved
    (d : PositiveHalfGap)
    (θM : d.successor.Angle) (θN : d.Angle) {η : ℝ}
    (hη : η ∈ Ico (0 : ℝ) (pathLogParameter d.a))
    (hM : outerChordFamilyZ d.successor θM = Real.cosh η)
    (hNlevel : chordPhi d.K d.a θN = chordPsi d.K d.a η) :
    outerChordFamilyZ d θN = Real.cosh η := by
  have hK3 : 3 ≤ d.K := d.three_le_size
  have hh : 0 < pathLogParameter d.a :=
    pathLogParameter_pos d.ha0 d.ha1
  have huOne : 1 ≤ Real.cosh η := Real.one_le_cosh η
  have huCosh :
      Real.cosh η < Real.cosh (pathLogParameter d.a) :=
    Real.cosh_strictMonoOn hη.1 hh.le hη.2
  have hpMleU :
      outerLobeMaximizer d.successor ≤ Real.cosh η := by
    rw [← hM]
    exact (outerChordFamilyZ_mem d.successor θM).1
  have hpNleU : outerLobeMaximizer d ≤ Real.cosh η := by
    by_contra hnot
    have huLtPN : Real.cosh η < outerLobeMaximizer d :=
      lt_of_not_ge hnot
    have hpNrange : outerLobeMaximizer d ∈
        Icc (1 : ℝ) (Real.cosh (pathLogParameter d.a)) :=
      ⟨huOne.trans huLtPN.le, (outerLobeMaximizer_spec d).1.2.le⟩
    obtain ⟨ξ, ⟨hξ, hpNcosh⟩, -⟩ :=
      existsUnique_hyperbolicOuterCoordinate d.a
        (outerLobeMaximizer d) d.ha0 d.ha1 hpNrange
    have hξLt : ξ < pathLogParameter d.a := by
      refine lt_of_le_of_ne hξ.2 ?_
      intro hξEq
      have hpNEq :
          outerLobeMaximizer d =
            Real.cosh (pathLogParameter d.a) := by
        rw [hpNcosh, hξEq]
      exact (ne_of_lt (outerLobeMaximizer_spec d).1.2) hpNEq
    have hηξ : η < ξ := by
      have hcosh : Real.cosh η < Real.cosh ξ := by
        simpa only [← hpNcosh] using huLtPN
      have habs := Real.cosh_lt_cosh.mp hcosh
      simpa only [abs_of_nonneg hη.1, abs_of_nonneg hξ.1] using habs
    have hpMlePN :
        outerLobeMaximizer d.successor ≤ outerLobeMaximizer d :=
      hpMleU.trans huLtPN.le
    have hantiM := outerChordLobeWeight_strictAntiOn_closedEndpointSide
      d.successor.K d.successor.hK d.a d.ha0 d.ha1
      (outerLobeMaximizer_spec d.successor).1
      (outerLobeMaximizer_spec d.successor).2
    have hweightM :
        chordLobeWeight d.successor.K d.a (outerLobeMaximizer d) <
          chordLobeWeight d.successor.K d.a (Real.cosh η) := by
      exact hantiM
        ⟨hpMleU, huCosh.le⟩
        ⟨hpMlePN, (outerLobeMaximizer_spec d).1.2.le⟩
        huLtPN
    have huDomainN : Real.cosh η ∈
        Icc (Real.cos (Real.pi / d.K))
          (Real.cosh (pathLogParameter d.a)) :=
      ⟨(Real.cos_le_one _).trans huOne, huCosh.le⟩
    have hweightN :
        chordLobeWeight d.K d.a (Real.cosh η) ≤
          chordLobeWeight d.K d.a (outerLobeMaximizer d) :=
      (outerLobeMaximizer_spec d).2 huDomainN
    have hratio := chordPsi_successor_ratio_strictAntiOn
      hK3 d.ha0 d.ha1 hη ⟨hξ.1, hξLt⟩ hηξ
    have hratioWeights :
        chordLobeWeight d.K d.a (outerLobeMaximizer d) /
            chordLobeWeight d.successor.K d.a (outerLobeMaximizer d) <
          chordLobeWeight d.K d.a (Real.cosh η) /
            chordLobeWeight d.successor.K d.a (Real.cosh η) := by
      calc
        chordLobeWeight d.K d.a (outerLobeMaximizer d) /
              chordLobeWeight d.successor.K d.a (outerLobeMaximizer d) =
            chordPsi d.K d.a ξ / chordPsi (d.K + 1) d.a ξ := by
              rw [hpNcosh,
                chordLobeWeight_cosh d.K d.a ξ d.hK hξ.1,
                chordLobeWeight_cosh d.successor.K d.a ξ
                  d.successor.hK hξ.1]
              rfl
        _ < chordPsi d.K d.a η / chordPsi (d.K + 1) d.a η := hratio
        _ = chordLobeWeight d.K d.a (Real.cosh η) /
              chordLobeWeight d.successor.K d.a (Real.cosh η) := by
              rw [chordLobeWeight_cosh d.K d.a η d.hK hη.1,
                chordLobeWeight_cosh d.successor.K d.a η
                  d.successor.hK hη.1]
              rfl
    have hWNpPos :
        0 < chordLobeWeight d.K d.a (outerLobeMaximizer d) := by
      rw [hpNcosh, chordLobeWeight_cosh d.K d.a ξ d.hK hξ.1]
      exact chordPsi_pos_before_endpoint d.hK d.ha0 d.ha1
        ⟨hξ.1, hξLt⟩
    have hWMpPos :
        0 < chordLobeWeight d.successor.K d.a (outerLobeMaximizer d) := by
      rw [hpNcosh,
        chordLobeWeight_cosh d.successor.K d.a ξ d.successor.hK hξ.1]
      exact chordPsi_pos_before_endpoint d.successor.hK d.ha0 d.ha1
        ⟨hξ.1, hξLt⟩
    have hWMuPos :
        0 < chordLobeWeight d.successor.K d.a (Real.cosh η) := by
      rw [chordLobeWeight_cosh d.successor.K d.a η
        d.successor.hK hη.1]
      exact chordPsi_pos_before_endpoint d.successor.hK d.ha0 d.ha1 hη
    have hreverse :
        chordLobeWeight d.K d.a (Real.cosh η) /
            chordLobeWeight d.successor.K d.a (Real.cosh η) <
          chordLobeWeight d.K d.a (outerLobeMaximizer d) /
            chordLobeWeight d.successor.K d.a (outerLobeMaximizer d) := by
      apply (div_lt_div_iff₀ hWMuPos hWMpPos).2
      exact (mul_le_mul_of_nonneg_right hweightN hWMpPos.le).trans_lt
        (mul_lt_mul_of_pos_left hweightM hWNpPos)
    exact (not_lt_of_ge hreverse.le) hratioWeights
  have hantiN := outerChordLobeWeight_strictAntiOn_closedEndpointSide
    d.K d.hK d.a d.ha0 d.ha1
    (outerLobeMaximizer_spec d).1 (outerLobeMaximizer_spec d).2
  apply hantiN.injOn (outerChordFamilyZ_mem d θN)
    ⟨hpNleU, huCosh.le⟩
  rw [chordLobeWeight_outerChordFamilyZ d θN, hNlevel,
    chordLobeWeight_cosh d.K d.a η d.hK hη.1]

/-- The trigonometric radical is strictly increasing on the positive half
angle interval. -/
theorem halfTrigRadical_strictMonoOn_positiveHalf
    {a t₁ t₂ : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (ht₁0 : 0 ≤ t₁) (ht₂half : t₂ ≤ Real.pi / 2)
    (ht₁t₂ : t₁ < t₂) :
    halfTrigRadical a t₁ < halfTrigRadical a t₂ := by
  have ht₂0 : 0 < t₂ := ht₁0.trans_lt ht₁t₂
  have ht₁half : t₁ ≤ Real.pi / 2 := ht₁t₂.le.trans ht₂half
  have hslt : Real.sin t₁ < Real.sin t₂ := by
    apply Real.strictMonoOn_sin
    · constructor <;> linarith [Real.pi_pos]
    · constructor <;> linarith [Real.pi_pos]
    · exact ht₁t₂
  have hs₁0 : 0 ≤ Real.sin t₁ := by
    exact Real.sin_nonneg_of_nonneg_of_le_pi ht₁0
      (ht₁half.trans (half_le_self Real.pi_pos.le))
  have hs₂0 : 0 ≤ Real.sin t₂ := by
    exact Real.sin_nonneg_of_nonneg_of_le_pi ht₂0.le
      (ht₂half.trans (half_le_self Real.pi_pos.le))
  have hsquares : Real.sin t₁ ^ 2 < Real.sin t₂ ^ 2 :=
    (sq_lt_sq₀ hs₁0 hs₂0).2 hslt
  have hsq₁ :
      halfTrigRadical a t₁ ^ 2 =
        Real.sinh (pathLogParameter a) ^ 2 + Real.sin t₁ ^ 2 := by
    rw [halfTrigRadical_sq]
    nlinarith [Real.cosh_sq_sub_sinh_sq (pathLogParameter a),
      Real.sin_sq_add_cos_sq t₁]
  have hsq₂ :
      halfTrigRadical a t₂ ^ 2 =
        Real.sinh (pathLogParameter a) ^ 2 + Real.sin t₂ ^ 2 := by
    rw [halfTrigRadical_sq]
    nlinarith [Real.cosh_sq_sub_sinh_sq (pathLogParameter a),
      Real.sin_sq_add_cos_sq t₂]
  apply (sq_lt_sq₀
    (halfTrigRadical_pos_of_parameter ha0 ha1 t₁).le
    (halfTrigRadical_pos_of_parameter ha0 ha1 t₂).le).1
  rw [hsq₁, hsq₂]
  linarith

/-- At a fixed hyperbolic outer coordinate before the radical endpoint, the
actual coordinate-free chord height strictly increases with the inner angle
on the positive half interval. -/
theorem outerChordS_strictMono_innerAngle_hyperbolic
    {a t₁ t₂ η : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (ht₁0 : 0 ≤ t₁) (ht₂half : t₂ ≤ Real.pi / 2)
    (ht₁t₂ : t₁ < t₂)
    (hη : η ∈ Ico (0 : ℝ) (pathLogParameter a)) :
    outerChordS a t₁ (Real.cosh η) <
      outerChordS a t₂ (Real.cosh η) := by
  rw [outerChordS_cosh a t₁ ⟨hη.1, hη.2.le⟩,
    outerChordS_cosh a t₂ ⟨hη.1, hη.2.le⟩]
  unfold halfChordS
  exact mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_left
      (halfTrigRadical_strictMonoOn_positiveHalf ha0 ha1
        ht₁0 ht₂half ht₁t₂)
      (halfChordScale_pos ha0))
    (halfHypRadical_pos_of_lt_pathLogParameter
      ha0 ha1 hη.1 hη.2)

/-- An interior angle of a packaged nodal interval cannot be a `K`-fold
sine node. -/
theorem sin_size_mul_ne_zero_of_gapInterior
    (d : PositiveHalfGap) {θ0 : d.Angle}
    (hleft : d.angleLower < θ0) (hright : θ0 < d.angleUpper) :
    Real.sin ((d.K : ℝ) * (θ0 : ℝ)) ≠ 0 := by
  have hPhi : 0 < chordPhi d.K d.a θ0 :=
    chordPhi_pos_on_nodalInterval d.K d.j d.hK
      ((Nat.lt_succ_self d.j).trans d.hjUpper)
      d.a ⟨hleft, hright⟩
      (halfTrigRadical_pos_of_parameter d.ha0 d.ha1 θ0)
  have hθ0 : 0 < (θ0 : ℝ) := d.angleLower_pos.trans hleft
  have hθltpi : (θ0 : ℝ) < Real.pi :=
    θ0.2.2.trans_lt (d.angleUpper_le_half.trans_lt
      (half_lt_self Real.pi_pos))
  have hθpi : (θ0 : ℝ) ≤ Real.pi := hθltpi.le
  have hsin : 0 < Real.sin (θ0 : ℝ) :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 hθltpi
  intro hnode
  have hmul := chordPhi_mul_sin d.a (θ0 : ℝ) d.hK hθ0.le hθpi
  rw [hnode, abs_zero, mul_zero] at hmul
  exact (ne_of_gt (mul_pos hPhi hsin)) hmul

/-- `eq:hyper-height-increase`, stated for the actual continuous chord
families at the concrete smaller and larger gap parameters.  The witness is
the unique rightmost return in the same-index size-`N` nodal interval. -/
theorem existsUnique_noncentralHyperbolicComparison
    (d : PositiveHalfGap) (θ0 : d.Angle)
    (hleft : d.angleLower < θ0) (hright : θ0 < d.angleUpper)
    {η : ℝ} (hη : η ∈ Ico (0 : ℝ) (pathLogParameter d.a))
    (hM : outerChordFamilyZ d.successor (d.scaleToSuccessor θ0) =
      Real.cosh η) :
    ∃! θhat : d.Angle,
      IsRightmostInnerSolution d θ0 (chordPsi d.K d.a η) θhat ∧
      outerChordFamilyZ d θhat = Real.cosh η ∧
      outerChordFamilyS d.successor (d.scaleToSuccessor θ0) <
        outerChordFamilyS d θhat := by
  have hK3 : 3 ≤ d.K := d.three_le_size
  have hθ0Half : (θ0 : ℝ) ∈ Ioc (0 : ℝ) (Real.pi / 2) :=
    ⟨d.angleLower_pos.trans hleft,
      θ0.2.2.trans d.angleUpper_le_half⟩
  have hnodal : Real.sin ((d.K : ℝ) * (θ0 : ℝ)) ≠ 0 :=
    sin_size_mul_ne_zero_of_gapInterior d hleft hright
  have hchannel :
      chordPhi (d.K + 1) d.a
          (noncentralScale d.K * (θ0 : ℝ)) =
        chordPsi (d.K + 1) d.a η := by
    calc
      chordPhi (d.K + 1) d.a
            (noncentralScale d.K * (θ0 : ℝ)) =
          chordLobeWeight d.successor.K d.a
            (outerChordFamilyZ d.successor (d.scaleToSuccessor θ0)) := by
              simpa only [PositiveHalfGap.successor_K,
                PositiveHalfGap.successor_a,
                PositiveHalfGap.coe_scaleToSuccessor] using
                (chordLobeWeight_outerChordFamilyZ d.successor
                  (d.scaleToSuccessor θ0)).symm
      _ = chordLobeWeight d.successor.K d.a (Real.cosh η) := by rw [hM]
      _ = chordPsi (d.K + 1) d.a η := by
        rw [chordLobeWeight_cosh d.successor.K d.a η
          d.successor.hK hη.1]
        rfl
  have hlevel :
      chordPsi d.K d.a η < chordPhi d.K d.a θ0 :=
    chordPhi_gt_chordPsi_of_next_eq hK3 d.ha0 d.ha1 hθ0Half
      hnodal hη hchannel
  obtain ⟨θhat, hθhat, hunique⟩ :=
    existsUnique_rightmostInnerSolution d θ0 hη hlevel
  have hN : outerChordFamilyZ d θhat = Real.cosh η :=
    hyperbolicOuterCoordinate_preserved d (d.scaleToSuccessor θ0) θhat
      hη hM hθhat.2.2.1
  have hangle :
      (d.scaleToSuccessor θ0 : ℝ) < (θhat : ℝ) :=
    (d.scaleToSuccessor_lt hleft).trans hθhat.1
  have hheight :
      outerChordFamilyS d.successor (d.scaleToSuccessor θ0) <
        outerChordFamilyS d θhat := by
    unfold outerChordFamilyS
    rw [hM, hN]
    exact outerChordS_strictMono_innerAngle_hyperbolic
      d.ha0 d.ha1
      ((d.successor.angleLower_pos).le.trans
        (d.scaleToSuccessor θ0).2.1)
      (θhat.2.2.trans d.angleUpper_le_half)
      hangle hη
  refine ⟨θhat, ⟨hθhat, hN, hheight⟩, ?_⟩
  intro φ hφ
  exact hunique φ hφ.1

end

end ConnectedPseudospectrum
