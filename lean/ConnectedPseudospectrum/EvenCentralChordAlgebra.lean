import ConnectedPseudospectrum.EvenCentralGap
import ConnectedPseudospectrum.FoldedReconstruction

/-!
# Algebra on the central half-chord of an even path

This module formalizes the closed algebraic content of `eq:even-central-half`
and `eq:z0-central`.  For `K = 2m+1`, it identifies the central inner lobe,
proves that its unique maximum is its centre, constructs the distinguished
outer coordinate `z₀`, and proves the Chebyshev, radical, and lobe identities
printed in `eq:even-central-half` and `eq:z0-central`.

The endpoint-side assertion following `eq:z0-central` is intentionally not
made here.  It requires the signed middle-branch continuation and chord-exhaustion
argument: algebra alone does not distinguish the two points of an outer lobe
having the same level.  In particular, no hypothesis or declaration below
assumes that `centralOuterZ0` lies on the endpoint side of the outer-lobe
maximizer.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-! ## Central half-gap data -/

/-- The parameters of the positive half of the central gap for an even path
of order `2m`. -/
structure EvenCentralHalfGapData where
  /-- Half the even path order, so that the path has order `2m`. -/
  m : ℕ
  /-- The asymmetric path parameter, constrained to lie in `(0,1)`. -/
  a : ℝ
  hm : 1 ≤ m
  ha0 : 0 < a
  ha1 : a < 1

namespace EvenCentralHalfGapData

/-- The odd half-chord size `K=2m+1` used for the order-`2m` path. -/
def K (d : EvenCentralHalfGapData) : ℕ :=
  2 * d.m + 1

/-- The positive nodal endpoint of the central inner lobe. -/
def innerEndpoint (d : EvenCentralHalfGapData) : ℝ :=
  Real.cos ((d.m : ℝ) * Real.pi / d.K)

@[simp] theorem K_eq (d : EvenCentralHalfGapData) :
    d.K = 2 * d.m + 1 := rfl

theorem two_le_K (d : EvenCentralHalfGapData) : 2 ≤ d.K := by
  have hm := d.hm
  unfold K
  omega

theorem K_sub_one (d : EvenCentralHalfGapData) :
    d.K - 1 = 2 * d.m := by
  unfold K
  omega

theorem K_pos (d : EvenCentralHalfGapData) : 0 < d.K :=
  Nat.zero_lt_two.trans_le d.two_le_K

theorem innerEndpoint_pos (d : EvenCentralHalfGapData) :
    0 < d.innerEndpoint := by
  have hKpos : (0 : ℝ) < d.K := by exact_mod_cast d.K_pos
  have hangle :
      (d.m : ℝ) * Real.pi / d.K < Real.pi / 2 := by
    rw [div_lt_iff₀ hKpos]
    unfold K
    push_cast
    nlinarith [Real.pi_pos]
  apply Real.cos_pos_of_mem_Ioo
  have hangleNonneg :
      0 ≤ (d.m : ℝ) * Real.pi / d.K := by positivity
  exact ⟨by linarith [Real.pi_pos], hangle⟩

/-- The two central nodal angles are complementary. -/
theorem cos_succ_angle_eq_neg_innerEndpoint
    (d : EvenCentralHalfGapData) :
    Real.cos (((d.m + 1 : ℕ) : ℝ) * Real.pi / d.K) =
      -d.innerEndpoint := by
  unfold innerEndpoint
  rw [← Real.cos_pi_sub]
  congr 1
  rw [d.K_eq]
  have hden : (2 * (d.m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp [hden]
  ring

theorem innerEndpoint_mem_chordNodes (d : EvenCentralHalfGapData) :
    d.innerEndpoint ∈ chordNodes d.K := by
  rw [chordNodes, Finset.mem_image]
  refine ⟨d.m - 1, ?_, ?_⟩
  · rw [Finset.mem_range]
    have hm := d.hm
    unfold K
    omega
  · unfold innerEndpoint
    rw [Nat.sub_add_cancel d.hm]

theorem neg_innerEndpoint_mem_chordNodes
    (d : EvenCentralHalfGapData) :
    -d.innerEndpoint ∈ chordNodes d.K := by
  rw [chordNodes, Finset.mem_image]
  refine ⟨d.m, ?_, ?_⟩
  · rw [Finset.mem_range]
    have hm := d.hm
    unfold K
    omega
  · exact d.cos_succ_angle_eq_neg_innerEndpoint

/-- There is no Chebyshev node strictly between the two central nodes. -/
theorem chordNode_outside_centralLobe
    (d : EvenCentralHalfGapData) {q : ℝ}
    (hq : q ∈ chordNodes d.K) :
    q ≤ -d.innerEndpoint ∨ d.innerEndpoint ≤ q := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
  have hklt : k < d.K - 1 := Finset.mem_range.mp hk
  have hell : k + 1 < d.K := by omega
  have hKpos : (0 : ℝ) < d.K := by exact_mod_cast d.K_pos
  have hangleNonneg (ell : ℕ) :
      0 ≤ (ell : ℝ) * Real.pi / d.K := by positivity
  have hangleLePi (ell : ℕ) (hellK : ell ≤ d.K) :
      (ell : ℝ) * Real.pi / d.K ≤ Real.pi := by
    rw [div_le_iff₀ hKpos]
    have hcast : (ell : ℝ) ≤ d.K := by exact_mod_cast hellK
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_right hcast Real.pi_pos.le
  by_cases hleft : k + 1 ≤ d.m
  · right
    unfold innerEndpoint
    apply Real.cos_le_cos_of_nonneg_of_le_pi
      (hangleNonneg (k + 1))
      (hangleLePi d.m (by unfold K; omega))
    rw [div_le_div_iff_of_pos_right hKpos]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hleft) Real.pi_pos.le
  · left
    rw [← d.cos_succ_angle_eq_neg_innerEndpoint]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
      (hangleNonneg (d.m + 1))
      (hangleLePi (k + 1) hell.le)
    rw [div_le_div_iff_of_pos_right hKpos]
    have hright : d.m + 1 ≤ k + 1 := by omega
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hright) Real.pi_pos.le

end EvenCentralHalfGapData

/-! ## Evenness and the central-lobe maximum -/

/-- An even-index second-kind Chebyshev polynomial is an even function. -/
theorem chebyshevU_even_index_neg (m : ℕ) (u : ℝ) :
    chebyshevU (2 * m) (-u) = chebyshevU (2 * m) u := by
  have hneg := Polynomial.Chebyshev.U_eval_neg (R := ℝ) (2 * m) u
  unfold chebyshevU
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Int.negOnePow_two_mul,
    Units.val_one, Int.cast_one, one_mul] using hneg

/-- For odd `K=2m+1`, the coordinate-free lobe profile is even. -/
theorem chordLobeWeight_even_evenCentral
    (d : EvenCentralHalfGapData) (u : ℝ) :
    chordLobeWeight d.K d.a (-u) = chordLobeWeight d.K d.a u := by
  unfold chordLobeWeight
  have hindex : ((d.K - 1 : ℕ) : ℤ) = 2 * (d.m : ℤ) := by
    exact_mod_cast d.K_sub_one
  rw [hindex, chebyshevU_even_index_neg]
  simp only [neg_sq]

/-- Existence and uniqueness of the maximum on the full central lobe. -/
theorem existsUnique_evenCentralInnerLobeMaximum
    (d : EvenCentralHalfGapData) :
    ∃! u : ℝ,
      u ∈ Ioo (-d.innerEndpoint) d.innerEndpoint ∧
        IsMaxOn (chordLobeWeight d.K d.a)
          (Icc (-d.innerEndpoint) d.innerEndpoint) u := by
  exact existsUnique_adjacentChordNodeLobeMaximum
    d.K d.two_le_K d.a d.ha0 d.ha1
    (l := -d.innerEndpoint) (r := d.innerEndpoint)
    d.neg_innerEndpoint_mem_chordNodes
    d.innerEndpoint_mem_chordNodes
    (by linarith [d.innerEndpoint_pos])
    (fun q hq => d.chordNode_outside_centralLobe hq)

private theorem evenCentralInnerLobe_center_and_unique
    (d : EvenCentralHalfGapData) :
    IsMaxOn (chordLobeWeight d.K d.a)
        (Icc (-d.innerEndpoint) d.innerEndpoint) 0 ∧
      ∀ u ∈ Ioo (-d.innerEndpoint) d.innerEndpoint,
        IsMaxOn (chordLobeWeight d.K d.a)
          (Icc (-d.innerEndpoint) d.innerEndpoint) u →
          u = 0 := by
  obtain ⟨p, hp, hunique⟩ := existsUnique_evenCentralInnerLobeMaximum d
  have hnegMem : -p ∈ Ioo (-d.innerEndpoint) d.innerEndpoint := by
    exact ⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩
  have hnegMax :
      IsMaxOn (chordLobeWeight d.K d.a)
        (Icc (-d.innerEndpoint) d.innerEndpoint) (-p) := by
    intro u hu
    have hnegu : -u ∈ Icc (-d.innerEndpoint) d.innerEndpoint := by
      exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hle := hp.2 hnegu
    calc
      chordLobeWeight d.K d.a u =
          chordLobeWeight d.K d.a (-u) :=
        (chordLobeWeight_even_evenCentral d u).symm
      _ ≤ chordLobeWeight d.K d.a p := hle
      _ = chordLobeWeight d.K d.a (-p) :=
        (chordLobeWeight_even_evenCentral d p).symm
  have hpSymm : -p = p := hunique (-p) ⟨hnegMem, hnegMax⟩
  have hpZero : p = 0 := by linarith
  constructor
  · simpa only [hpZero] using hp.2
  · intro u hu huMax
    have hup : u = p := hunique u ⟨hu, huMax⟩
    exact hup.trans hpZero

/-- Strict log-concavity and evenness force the unique central-lobe maximum
to occur at `y=0`. -/
theorem evenCentralInnerLobe_center_isMax
    (d : EvenCentralHalfGapData) :
    IsMaxOn (chordLobeWeight d.K d.a)
      (Icc (-d.innerEndpoint) d.innerEndpoint) 0 :=
  (evenCentralInnerLobe_center_and_unique d).1

theorem evenCentralInnerLobe_maximizer_eq_zero
    (d : EvenCentralHalfGapData) {u : ℝ}
    (hu : u ∈ Ioo (-d.innerEndpoint) d.innerEndpoint)
    (huMax : IsMaxOn (chordLobeWeight d.K d.a)
      (Icc (-d.innerEndpoint) d.innerEndpoint) u) :
    u = 0 :=
  (evenCentralInnerLobe_center_and_unique d).2 u hu huMax

/-- The strict comparison `W_K(y)<W_K(0)` on the positive half of the
central lobe used in `eq:even-central-half`. -/
theorem evenCentralInnerLobe_lt_center
    (d : EvenCentralHalfGapData) {y : ℝ}
    (hy0 : 0 < y) (hyEnd : y < d.innerEndpoint) :
    chordLobeWeight d.K d.a y < chordLobeWeight d.K d.a 0 := by
  have hyIoo : y ∈ Ioo (-d.innerEndpoint) d.innerEndpoint :=
    ⟨by linarith [d.innerEndpoint_pos], hyEnd⟩
  have hyIcc : y ∈ Icc (-d.innerEndpoint) d.innerEndpoint :=
    ⟨hyIoo.1.le, hyIoo.2.le⟩
  have hle := evenCentralInnerLobe_center_isMax d hyIcc
  apply lt_of_le_of_ne hle
  intro heq
  have hyMax : IsMaxOn (chordLobeWeight d.K d.a)
      (Icc (-d.innerEndpoint) d.innerEndpoint) y := by
    intro u hu
    rw [heq]
    exact evenCentralInnerLobe_center_isMax d hu
  have hyZero := evenCentralInnerLobe_maximizer_eq_zero d hyIoo hyMax
  exact hy0.ne' hyZero

/-! ## The distinguished outer coordinate `z₀` -/

/-- The coordinate `z₀=sqrt((1+rho_m)/2)` from `eq:z0-central`. -/
def centralOuterZ0 (m : ℕ) (a : ℝ) : ℝ :=
  Real.sqrt ((1 + centralRho m a) / 2)

theorem centralRho_pos
    (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    0 < centralRho m a := by
  have hspec := centralRho_spec m hm a ha0 ha1
  have hangleHalf :
      Real.pi / ((m + 1 : ℕ) : ℝ) ≤ Real.pi / 2 := by
    have hden : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    rw [div_le_div_iff_of_pos_left Real.pi_pos hden (by norm_num)]
    exact_mod_cast Nat.succ_le_succ hm
  have hnodeNonneg : 0 ≤ centralChebyshevFirstNode m := by
    unfold centralChebyshevFirstNode
    have hangleNonneg :
        0 ≤ Real.pi / ((m + 1 : ℕ) : ℝ) := by positivity
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [Real.pi_pos]) hangleHalf
  exact hnodeNonneg.trans_lt hspec.1

theorem centralOuterZ0_sq
    (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    centralOuterZ0 m a ^ 2 = (1 + centralRho m a) / 2 := by
  exact Real.sq_sqrt (by
    have hρ := centralRho_pos m hm a ha0 ha1
    linarith)

theorem centralOuterZ0_pos
    (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    0 < centralOuterZ0 m a := by
  apply Real.sqrt_pos.2
  have hρ := centralRho_pos m hm a ha0 ha1
  linarith

/-- The half-angle Chebyshev identity at the distinguished outer point. -/
theorem chebyshevU_centralOuterZ0
    (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    chebyshevU (2 * m) (centralOuterZ0 m a) =
      chebyshevU m (centralRho m a) +
        chebyshevU ((m : ℤ) - 1) (centralRho m a) := by
  have hhalf := chebyshevU_half_angle_even_index m (centralOuterZ0 m a)
  have harg :
      2 * centralOuterZ0 m a ^ 2 - 1 = centralRho m a := by
    rw [centralOuterZ0_sq m hm a ha0 ha1]
    ring
  rw [harg] at hhalf
  exact hhalf.symm

theorem chebyshevU_centralOuterZ0_eq
    (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    chebyshevU (2 * m) (centralOuterZ0 m a) =
      (1 + a) * chebyshevU m (centralRho m a) := by
  rw [chebyshevU_centralOuterZ0 m hm a ha0 ha1,
    ← (centralRho_spec m hm a ha0 ha1).2]
  ring

theorem centralZeta_sub_rho_pos
    (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    0 < (a + a⁻¹) / 2 - centralRho m a := by
  have hspec := centralRho_spec m hm a ha0 ha1
  have hU := chebyshevU_pos_above_centralFirstNode m hm hspec.1
  have hprev :
      0 < chebyshevU ((m : ℤ) - 1) (centralRho m a) := by
    rw [← hspec.2]
    exact mul_pos ha0 hU
  rw [centralZeta_sub_rho_eq m hm a ha0 ha1]
  exact one_div_pos.mpr (mul_pos (mul_pos (by norm_num) hprev) hU)

/-- The first equality in `eq:z0-central`, before identifying it with `c_m²`. -/
theorem centralOuterZ0_radical_eq_zeta
    (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    4 * a *
        (Real.cosh (pathLogParameter a) ^ 2 - centralOuterZ0 m a ^ 2) =
      2 * a * ((a + a⁻¹) / 2 - centralRho m a) := by
  have hcosh := four_mul_mul_cosh_sq_pathLogParameter ha0
  have hzsq := centralOuterZ0_sq m hm a ha0 ha1
  calc
    4 * a *
          (Real.cosh (pathLogParameter a) ^ 2 -
            centralOuterZ0 m a ^ 2) =
        4 * a * Real.cosh (pathLogParameter a) ^ 2 -
          4 * a * centralOuterZ0 m a ^ 2 := by ring
    _ = (1 + a) ^ 2 - 4 * a * ((1 + centralRho m a) / 2) := by
      rw [hcosh, hzsq]
    _ = 2 * a * ((a + a⁻¹) / 2 - centralRho m a) := by
      field_simp [ha0.ne']
      ring

/-- The second equality in `eq:z0-central`, using the actual least singular
value `c_m`. -/
theorem two_mul_a_mul_centralZeta_sub_rho_eq_height_sq
    (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    2 * a * ((a + a⁻¹) / 2 - centralRho m a) =
      centralBidiagonalHeight m a ^ 2 := by
  rw [centralBidiagonalHeight_sq_eq_rhoLambda m hm a ha0 ha1]
  unfold centralRhoLambda
  field_simp [ha0.ne']
  ring

theorem centralOuterZ0_radical_eq_height_sq
    (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    4 * a *
        (Real.cosh (pathLogParameter a) ^ 2 - centralOuterZ0 m a ^ 2) =
      centralBidiagonalHeight m a ^ 2 := by
  rw [centralOuterZ0_radical_eq_zeta m hm a ha0 ha1,
    two_mul_a_mul_centralZeta_sub_rho_eq_height_sq m hm a ha0 ha1]

theorem centralOuterZ0_lt_cosh
    (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    centralOuterZ0 m a < Real.cosh (pathLogParameter a) := by
  have hheight := centralBidiagonalHeight_pos m hm a ha0
  have hrad := centralOuterZ0_radical_eq_height_sq m hm a ha0 ha1
  have hdiff :
      0 < Real.cosh (pathLogParameter a) ^ 2 -
        centralOuterZ0 m a ^ 2 := by
    apply pos_of_mul_pos_left (b := 4 * a)
    · rw [mul_comm, hrad]
      exact sq_pos_of_pos hheight
    · positivity
  apply (sq_lt_sq₀ (centralOuterZ0_pos m hm a ha0 ha1).le
    (Real.cosh_pos _).le).mp
  linarith

/-- The distinguished point is in the open outer lobe.  This is an
order-theoretic bound only; it does not choose a side of that lobe's
maximizer. -/
theorem cos_pi_div_evenCentralK_lt_centralOuterZ0
    (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    Real.cos (Real.pi / ((2 * m + 1 : ℕ) : ℝ)) <
      centralOuterZ0 m a := by
  let K : ℕ := 2 * m + 1
  let α : ℝ := Real.pi / ((m + 1 : ℕ) : ℝ)
  let β : ℝ := 2 * (Real.pi / (K : ℝ))
  have hK : 2 ≤ K := by dsimp [K]; omega
  have hKpos : (0 : ℝ) < K := by positivity
  have hα0 : 0 ≤ α := by dsimp [α]; positivity
  have hαβ : α < β := by
    dsimp [α, β]
    have hmden : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have hKden : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hKlt : K < 2 * (m + 1) := by dsimp [K]; omega
    have hKltReal : (K : ℝ) < 2 * ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast hKlt
    rw [show 2 * (Real.pi / (K : ℝ)) =
      (2 * Real.pi) / (K : ℝ) by ring]
    rw [div_lt_div_iff₀ hmden hKden]
    nlinarith [mul_lt_mul_of_pos_right hKltReal Real.pi_pos]
  have hβpi : β ≤ Real.pi := by
    dsimp [β]
    rw [show 2 * (Real.pi / (K : ℝ)) =
      (2 * Real.pi) / (K : ℝ) by ring]
    rw [div_le_iff₀ hKpos]
    have hKcast : (2 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith [mul_le_mul_of_nonneg_right hKcast Real.pi_pos.le]
  have hcos : Real.cos β < centralChebyshevFirstNode m := by
    unfold centralChebyshevFirstNode
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hα0 hβpi hαβ
  have hρ := (centralRho_spec m hm a ha0 ha1).1
  have hdouble :
      Real.cos β =
        2 * Real.cos (Real.pi / (K : ℝ)) ^ 2 - 1 := by
    dsimp [β]
    exact Real.cos_two_mul _
  have hsquares :
      Real.cos (Real.pi / (K : ℝ)) ^ 2 <
        centralOuterZ0 m a ^ 2 := by
    rw [centralOuterZ0_sq m hm a ha0 ha1]
    rw [hdouble] at hcos
    nlinarith
  have hcosNonneg : 0 ≤ Real.cos (Real.pi / (K : ℝ)) := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · have : 0 ≤ Real.pi / (K : ℝ) := by positivity
      linarith [Real.pi_pos]
    · rw [div_le_iff₀ hKpos]
      have hKcast : (2 : ℝ) ≤ K := by exact_mod_cast hK
      nlinarith [Real.pi_pos]
  exact (sq_lt_sq₀ hcosNonneg
    (centralOuterZ0_pos m hm a ha0 ha1).le).mp hsquares

/-! ## The two exact lobe levels -/

theorem abs_chebyshevU_even_index_zero (m : ℕ) :
    |chebyshevU (2 * m) 0| = 1 := by
  have hU := Polynomial.Chebyshev.U_eval_two_mul_zero
    (R := ℝ) (m : ℤ)
  have hU' :
      chebyshevU (2 * m) 0 = ((m : ℤ).negOnePow : ℝ) := by
    unfold chebyshevU
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Int.cast_natCast] using hU
  rw [hU', Int.cast_negOnePow_natCast]
  simp

theorem chordLobeWeight_evenCentral_zero
    (d : EvenCentralHalfGapData) :
    chordLobeWeight d.K d.a 0 =
      Real.cosh (pathLogParameter d.a) := by
  unfold chordLobeWeight
  have hindex : ((d.K - 1 : ℕ) : ℤ) = 2 * (d.m : ℤ) := by
    exact_mod_cast d.K_sub_one
  rw [hindex, abs_chebyshevU_even_index_zero]
  simp only [zero_pow (by norm_num : 2 ≠ 0), sub_zero, mul_one]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (Real.cosh_pos _)]

/-- The distinguished outer point has the same level as the centre of the
inner lobe: `W_K(z₀)=cosh(h)`. -/
theorem chordLobeWeight_centralOuterZ0
    (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    chordLobeWeight (2 * m + 1) a (centralOuterZ0 m a) =
      Real.cosh (pathLogParameter a) := by
  let ρ : ℝ := centralRho m a
  let z : ℝ := centralOuterZ0 m a
  let U : ℝ := chebyshevU m ρ
  let c : ℝ := Real.cosh (pathLogParameter a)
  have hρspec := centralRho_spec m hm a ha0 ha1
  have hUpos : 0 < U := by
    exact chebyshevU_pos_above_centralFirstNode m hm hρspec.1
  have hUeven : chebyshevU (2 * m) z = (1 + a) * U := by
    exact chebyshevU_centralOuterZ0_eq m hm a ha0 ha1
  have hrad : 4 * a * (c ^ 2 - z ^ 2) =
      centralBidiagonalHeight m a ^ 2 := by
    exact centralOuterZ0_radical_eq_height_sq m hm a ha0 ha1
  have hinv : centralBidiagonalHeight m a ^ 2 = 1 / U ^ 2 := by
    exact centralBidiagonalHeight_sq_eq_inv_chebyshev m hm a ha0 ha1
  have hscaled : 4 * a * (c ^ 2 - z ^ 2) * U ^ 2 = 1 := by
    rw [hrad, hinv]
    field_simp [hUpos.ne']
  have hdiff : 0 ≤ c ^ 2 - z ^ 2 := by
    apply sub_nonneg.mpr
    apply (sq_le_sq₀ (centralOuterZ0_pos m hm a ha0 ha1).le
      (Real.cosh_pos _).le).2
    exact (centralOuterZ0_lt_cosh m hm a ha0 ha1).le
  have hcosh : 4 * a * c ^ 2 = (1 + a) ^ 2 := by
    exact four_mul_mul_cosh_sq_pathLogParameter ha0
  have hsq :
      chordLobeWeight (2 * m + 1) a z ^ 2 = c ^ 2 := by
    unfold chordLobeWeight
    have hindex : ((((2 * m + 1 : ℕ) - 1 : ℕ)) : ℤ) =
        2 * (m : ℤ) := by
      norm_cast
    rw [hindex, mul_pow, Real.sq_sqrt hdiff, sq_abs, hUeven]
    calc
      (c ^ 2 - z ^ 2) * ((1 + a) * U) ^ 2 =
          (1 + a) ^ 2 * ((c ^ 2 - z ^ 2) * U ^ 2) := by ring
      _ = (4 * a * c ^ 2) * ((c ^ 2 - z ^ 2) * U ^ 2) := by
        rw [hcosh]
      _ = c ^ 2 * (4 * a * (c ^ 2 - z ^ 2) * U ^ 2) := by ring
      _ = c ^ 2 := by rw [hscaled, mul_one]
  apply (sq_eq_sq₀ (by unfold chordLobeWeight; positivity)
    (Real.cosh_pos _).le).mp
  exact hsq

/-! ## Coordinate formulas from `eq:even-central-half` -/

/-- The coordinate-free horizontal expression in the central half-chord. -/
def evenCentralHalfChordX (a y z : ℝ) : ℝ :=
  halfChordScale a * y * z

/-- The square of the coordinate-free central half-chord height. -/
def evenCentralHalfChordHeightSq (a y z : ℝ) : ℝ :=
  (4 * a / Real.cosh (pathLogParameter a) ^ 2) *
    (Real.cosh (pathLogParameter a) ^ 2 - y ^ 2) *
    (Real.cosh (pathLogParameter a) ^ 2 - z ^ 2)

theorem halfChordScale_sq_eq_four_mul_div_cosh_sq
    {a : ℝ} (ha0 : 0 < a) :
    halfChordScale a ^ 2 =
      4 * a / Real.cosh (pathLogParameter a) ^ 2 := by
  have hc : Real.cosh (pathLogParameter a) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (Real.cosh_pos _).ne'
  apply (eq_div_iff hc).2
  exact halfChordScale_sq_mul_cosh_sq ha0

theorem evenCentralHalfChordHeightSq_eq_scale
    {a : ℝ} (ha0 : 0 < a) (y z : ℝ) :
    evenCentralHalfChordHeightSq a y z =
      halfChordScale a ^ 2 *
        (Real.cosh (pathLogParameter a) ^ 2 - y ^ 2) *
        (Real.cosh (pathLogParameter a) ^ 2 - z ^ 2) := by
  rw [halfChordScale_sq_eq_four_mul_div_cosh_sq ha0]
  rfl

/-- The source's displayed coefficient `4a/cosh(h)²` is exactly the
square of the half-chord scale `2r/cosh(h)`. -/
theorem evenCentralHalfChord_source_formulas
    {a y z x s : ℝ}
    (hx : x = evenCentralHalfChordX a y z)
    (hs : s ^ 2 = evenCentralHalfChordHeightSq a y z) :
    x = 2 * pathRate a / Real.cosh (pathLogParameter a) * y * z ∧
      s ^ 2 =
        4 * a / Real.cosh (pathLogParameter a) ^ 2 *
          (Real.cosh (pathLogParameter a) ^ 2 - y ^ 2) *
          (Real.cosh (pathLogParameter a) ^ 2 - z ^ 2) := by
  constructor
  · simpa only [evenCentralHalfChordX, halfChordScale] using hx
  · simpa only [evenCentralHalfChordHeightSq] using hs

/-!
## Remaining continuation obligation

To obtain the strict height comparison used in `eq:central-interlace`, a later module
must prove that the actual signed middle root at `x=0` selects
`centralOuterZ0 m a` on the endpoint side of the outer-lobe maximizer, and
that every nonzero point of the positive central half-gap selects a strictly
larger outer coordinate.  Those facts depend on middle-branch continuation,
noncollision, and chord exhaustion; they are not consequences of the closed
identities proved here.
-/

end

end ConnectedPseudospectrum
