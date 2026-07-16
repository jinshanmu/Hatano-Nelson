import ConnectedPseudospectrum.TailThresholdAsymptotic

/-!
# The lower real Lambert branch and the exact tail threshold

Mathlib does not currently provide Lambert's `W` function.  This module
therefore constructs precisely the lower real branch needed by the paper.
The definition is totalized by the value `0` off the natural real domain
`[-exp (-1), 0)`, while every theorem using the branch either assumes the
domain condition explicitly or derives it from its small-parameter hypotheses.

The main result identifies the permanent integer crossing of
`(n+1) r^n` with the natural-number floor of the lower-branch solution.  A
second result derives the lower-branch logarithmic--logarithmic expansion,
with bounded error, from the independently proved elementary inversion.
-/

namespace ConnectedPseudospectrum

open Filter Set

noncomputable section

/-- The map inverted by Lambert's `W` function. -/
def lambertMap (w : ℝ) : ℝ :=
  w * Real.exp w

/-- Natural real domain of the finite-valued lower branch `W₋₁`. -/
def LowerLambertDomain (z : ℝ) : Prop :=
  -Real.exp (-1) ≤ z ∧ z < 0

theorem hasDerivAt_lambertMap (w : ℝ) :
    HasDerivAt lambertMap (Real.exp w * (w + 1)) w := by
  convert (hasDerivAt_id w).mul (Real.hasDerivAt_exp w) using 1
  all_goals simp only [id_eq]
  ring_nf

/-- On `(-∞,-1]`, the Lambert map is strictly decreasing. -/
theorem lambertMap_strictAntiOn_lower :
    StrictAntiOn lambertMap (Iic (-1)) := by
  apply strictAntiOn_of_deriv_neg (convex_Iic (-1))
  · exact (continuous_id.mul Real.continuous_exp).continuousOn
  · intro w hw
    rw [(hasDerivAt_lambertMap w).deriv]
    have hw' : w < -1 := by simpa using hw
    exact mul_neg_of_pos_of_neg (Real.exp_pos w) (by linarith)

/-- On `[-1,∞)`, the Lambert map is strictly increasing. -/
theorem lambertMap_strictMonoOn_upper :
    StrictMonoOn lambertMap (Ici (-1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (-1))
  · exact (continuous_id.mul Real.continuous_exp).continuousOn
  · intro w hw
    rw [(hasDerivAt_lambertMap w).deriv]
    have hw' : -1 < w := by simpa using hw
    exact mul_pos (Real.exp_pos w) (by linarith)

private theorem tendsto_lambertMap_atBot_zero :
    Tendsto lambertMap atBot (nhds 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).neg.comp
    tendsto_neg_atBot_atTop
  have h' :
      Tendsto (fun w : ℝ => -((-w) ^ 1 * Real.exp (-(-w)))) atBot (nhds 0) := by
    simpa only [neg_zero] using h
  apply h'.congr'
  exact Eventually.of_forall fun w => by simp [lambertMap]

/-- Every point of the natural lower-branch domain has a unique preimage at
or below `-1`. -/
theorem existsUnique_lower_lambert_preimage {z : ℝ}
    (hz : LowerLambertDomain z) :
    ∃! w : ℝ, w ≤ -1 ∧ lambertMap w = z := by
  have hevent : ∀ᶠ w : ℝ in atBot, z < lambertMap w :=
    (tendsto_order.1 tendsto_lambertMap_atBot_zero).1 z hz.2
  obtain ⟨A, hA⟩ := eventually_atBot.1 hevent
  let a : ℝ := min A (-2)
  have haA : a ≤ A := min_le_left A (-2)
  have ha1 : a ≤ -1 := (min_le_right A (-2)).trans (by norm_num)
  have hza : z ≤ lambertMap a := (hA a haA).le
  have hminus : lambertMap (-1) = -Real.exp (-1) := by
    simp [lambertMap]
  have hzminus : lambertMap (-1) ≤ z := by simpa [hminus] using hz.1
  have hcont : ContinuousOn lambertMap (Icc a (-1)) := by
    simpa only [lambertMap] using
      (continuous_id.mul Real.continuous_exp).continuousOn
  obtain ⟨w, hwmem, hweq⟩ :=
    (intermediate_value_Icc' ha1 hcont) ⟨hzminus, hza⟩
  refine ⟨w, ⟨hwmem.2, hweq⟩, ?_⟩
  intro v hv
  exact lambertMap_strictAntiOn_lower.injOn hv.1 hwmem.2
    (hv.2.trans hweq.symm)

/-- Lower real Lambert branch.  Outside `LowerLambertDomain` it is
totalized to `0`; no theorem treats that value as an analytic continuation. -/
def lowerLambertW (z : ℝ) : ℝ :=
  by
    classical
    exact if hz : LowerLambertDomain z then
      Classical.choose (existsUnique_lower_lambert_preimage hz).exists
    else 0

/-- The branch equation and value range on the natural domain. -/
theorem lowerLambertW_spec {z : ℝ} (hz : LowerLambertDomain z) :
    lowerLambertW z ≤ -1 ∧
      lowerLambertW z * Real.exp (lowerLambertW z) = z := by
  rw [lowerLambertW, dif_pos hz]
  simpa [lambertMap] using
    (Classical.choose_spec (existsUnique_lower_lambert_preimage hz).exists)

theorem lowerLambertW_le_neg_one {z : ℝ} (hz : LowerLambertDomain z) :
    lowerLambertW z ≤ -1 :=
  (lowerLambertW_spec hz).1

theorem lowerLambertW_mul_exp {z : ℝ} (hz : LowerLambertDomain z) :
    lowerLambertW z * Real.exp (lowerLambertW z) = z :=
  (lowerLambertW_spec hz).2

/-- Uniqueness characterization of the lower branch. -/
theorem eq_lowerLambertW {z w : ℝ} (hz : LowerLambertDomain z)
    (hw : w ≤ -1) (heq : w * Real.exp w = z) :
    w = lowerLambertW z := by
  exact (existsUnique_lower_lambert_preimage hz).unique
    ⟨hw, by simpa [lambertMap] using heq⟩
    ⟨lowerLambertW_le_neg_one hz,
      by simpa [lambertMap] using lowerLambertW_mul_exp hz⟩

/-- Positive decay parameter `β=-log r` used in the Lambert formula. -/
def tailBeta (r : ℝ) : ℝ :=
  -Real.log r

theorem tailBeta_pos {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    0 < tailBeta r := by
  exact neg_pos.mpr (Real.log_neg hr hr1)

theorem exp_neg_tailBeta {r : ℝ} (hr : 0 < r) :
    Real.exp (-tailBeta r) = r := by
  simp [tailBeta, Real.exp_log hr]

/-- The Lambert argument in the exact threshold formula always lies in the
lower branch's natural domain under the paper's sharp range
`0<t<3r²`. -/
theorem lowerLambert_tail_argument_mem_domain {r t : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (ht : 0 < t) (htop : t < 3 * r ^ 2) :
    LowerLambertDomain (-(tailBeta r * r * t)) := by
  let β := tailBeta r
  have hβ : 0 < β := tailBeta_pos hr hr1
  have hrexp : Real.exp (-β) = r := exp_neg_tailBeta hr
  have hsmall : β * r * t < 3 * β * r ^ 3 := by
    calc
      β * r * t < β * r * (3 * r ^ 2) :=
        mul_lt_mul_of_pos_left htop (mul_pos hβ hr)
      _ = 3 * β * r ^ 3 := by ring_nf
  have hrewrite :
      3 * β * r ^ 3 = (3 * β) * Real.exp (-(3 * β)) := by
    rw [← hrexp, ← Real.exp_nat_mul]
    congr 1
    ring_nf
  have hmax : (3 * β) * Real.exp (-(3 * β)) ≤ Real.exp (-1) :=
    Real.mul_exp_neg_le_exp_neg_one (3 * β)
  constructor
  · rw [neg_le_neg_iff]
    exact hsmall.le.trans (by rwa [hrewrite])
  · exact neg_neg_of_pos (mul_pos (mul_pos hβ hr) ht)

/-- Continuous descending-branch coordinate `x+1` appearing before the
integer floor in the manuscript. -/
def lowerLambertTailCoordinate (r t : ℝ) : ℝ :=
  -lowerLambertW (-(tailBeta r * r * t)) / tailBeta r

/-- The coordinate satisfies the expected continuous crossing equation. -/
theorem lowerLambertTailCoordinate_equation {r t : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (ht : 0 < t) (htop : t < 3 * r ^ 2) :
    lowerLambertTailCoordinate r t *
        Real.exp (-(tailBeta r) * lowerLambertTailCoordinate r t) = r * t := by
  let β := tailBeta r
  let w := lowerLambertW (-(tailBeta r * r * t))
  have hβ : 0 < β := tailBeta_pos hr hr1
  have hz := lowerLambert_tail_argument_mem_domain hr hr1 ht htop
  have hw : w * Real.exp w = -(β * r * t) := by
    simpa [w, β] using lowerLambertW_mul_exp hz
  have hcoord : lowerLambertTailCoordinate r t = -w / β := by
    rfl
  have hexp : -β * lowerLambertTailCoordinate r t = w := by
    rw [hcoord]
    field_simp [hβ.ne']
  rw [hexp, hcoord]
  field_simp [hβ.ne'] at hw ⊢
  linarith

/-- The selected descending root lies strictly beyond the initial index
`2`, i.e. its shifted coordinate is greater than `3`. -/
theorem three_lt_lowerLambertTailCoordinate {r t : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (ht : 0 < t) (htop : t < 3 * r ^ 2) :
    3 < lowerLambertTailCoordinate r t := by
  let β := tailBeta r
  let w := lowerLambertW (-(tailBeta r * r * t))
  have hβ : 0 < β := tailBeta_pos hr hr1
  have hrexp : Real.exp (-β) = r := exp_neg_tailBeta hr
  have hz := lowerLambert_tail_argument_mem_domain hr hr1 ht htop
  have hwle : w ≤ -1 := by
    simpa [w] using lowerLambertW_le_neg_one hz
  have hwmap : lambertMap w = -(β * r * t) := by
    simpa [w, lambertMap, β] using lowerLambertW_mul_exp hz
  have hmap3 : lambertMap (-3 * β) = (-β * r) * (3 * r ^ 2) := by
    unfold lambertMap
    have hpow : Real.exp (-3 * β) = r ^ 3 := by
      rw [← hrexp, ← Real.exp_nat_mul]
      congr 1
      ring_nf
    rw [hpow]
    ring_nf
  have hmaplt : lambertMap (-3 * β) < lambertMap w := by
    rw [hmap3, hwmap]
    have hneg : -β * r < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hβ) hr
    have := mul_lt_mul_of_neg_left htop hneg
    nlinarith
  have hwlt : w < -3 * β := by
    by_cases h3 : -3 * β ≤ -1
    · by_contra hnot
      have hle : -3 * β ≤ w := le_of_not_gt hnot
      have hanti := lambertMap_strictAntiOn_lower.antitoneOn h3 hwle hle
      exact (not_lt_of_ge hanti) hmaplt
    · exact hwle.trans_lt (lt_of_not_ge h3)
  change 3 < -w / β
  exact (lt_div_iff₀ hβ).2 (by linarith)

private theorem lambertMap_nat_tail_point {r : ℝ} (hr : 0 < r)
    (n : ℕ) :
    lambertMap (-(tailBeta r) * ((n + 1 : ℕ) : ℝ)) =
      (-(tailBeta r) * r) * tailModel r n := by
  let β := tailBeta r
  have hrexp : Real.exp (-β) = r := exp_neg_tailBeta hr
  have hpow : r ^ n = Real.exp ((n : ℝ) * (-β)) := by
    rw [← hrexp, Real.exp_nat_mul]
  change (-β * ((n + 1 : ℕ) : ℝ)) *
      Real.exp (-β * ((n + 1 : ℕ) : ℝ)) =
    (-β * r) * (((n + 1 : ℕ) : ℝ) * r ^ n)
  rw [hpow, ← hrexp]
  calc
    (-β * ((n + 1 : ℕ) : ℝ)) *
        Real.exp (-β * ((n + 1 : ℕ) : ℝ)) =
      (-β * ((n + 1 : ℕ) : ℝ)) *
        Real.exp (-β + (n : ℝ) * (-β)) := by
          congr 1
          push_cast
          ring_nf
    _ = (-β * ((n + 1 : ℕ) : ℝ)) *
        (Real.exp (-β) * Real.exp ((n : ℝ) * (-β))) := by
          rw [Real.exp_add]
    _ = (-β * Real.exp (-β)) *
        (((n + 1 : ℕ) : ℝ) * Real.exp ((n : ℝ) * (-β))) := by ring_nf

/-- Literal crossing criterion behind the floor formula: beyond the
manuscript's initial index, the discrete model is below `t` exactly when
the shifted integer lies to the right of the descending Lambert root. -/
theorem tailModel_lt_iff_lowerLambertTailCoordinate_lt {r t : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (ht : 0 < t) (htop : t < 3 * r ^ 2)
    {n : ℕ} (hn : 2 ≤ n) :
    tailModel r n < t ↔
      lowerLambertTailCoordinate r t < ((n + 1 : ℕ) : ℝ) := by
  let β := tailBeta r
  let w := lowerLambertW (-(tailBeta r * r * t))
  let y := lowerLambertTailCoordinate r t
  let q : ℝ := ((n + 1 : ℕ) : ℝ)
  let wq := -β * q
  have hβ : 0 < β := tailBeta_pos hr hr1
  have hz := lowerLambert_tail_argument_mem_domain hr hr1 ht htop
  have hwle : w ≤ -1 := by
    simpa [w] using lowerLambertW_le_neg_one hz
  have hwmap : lambertMap w = -(β * r * t) := by
    simpa [w, lambertMap, β] using lowerLambertW_mul_exp hz
  have hycoord : y = -w / β := by
    rfl
  have hwy : w = -β * y := by
    rw [hycoord]
    field_simp [hβ.ne']
  have hy3 : 3 < y := by
    simpa [y] using three_lt_lowerLambertTailCoordinate hr hr1 ht htop
  have hq3 : 3 ≤ q := by
    dsimp only [q]
    exact_mod_cast Nat.add_le_add_right hn 1
  have hmapq : lambertMap wq = (-β * r) * tailModel r n := by
    simpa [wq, q, β] using lambertMap_nat_tail_point hr n
  have hmapCross :
      tailModel r n < t ↔ lambertMap w < lambertMap wq := by
    rw [hmapq, hwmap]
    have hpos : 0 < β * r := mul_pos hβ hr
    constructor <;> intro h <;> nlinarith
  rw [hmapCross]
  constructor
  · intro hmap
    by_contra hnot
    have hqy : q ≤ y := le_of_not_gt hnot
    by_cases hwqLower : wq ≤ -1
    · have hwwq : w ≤ wq := by
        rw [hwy]
        dsimp only [wq]
        nlinarith
      have hanti :=
        lambertMap_strictAntiOn_lower.antitoneOn hwle hwqLower hwwq
      exact (not_lt_of_ge hanti) hmap
    · have hwqUpper : -1 ≤ wq := (lt_of_not_ge hwqLower).le
      have hwq3 : wq ≤ -3 * β := by
        dsimp only [wq]
        nlinarith
      have hthreeUpper : -1 ≤ -3 * β := hwqUpper.trans hwq3
      have hupper :=
        lambertMap_strictMonoOn_upper.monotoneOn hwqUpper hthreeUpper hwq3
      have hmap3lt : lambertMap (-3 * β) < lambertMap w := by
        have hrexp : Real.exp (-β) = r := exp_neg_tailBeta hr
        have hmap3 :
            lambertMap (-3 * β) = (-β * r) * (3 * r ^ 2) := by
          unfold lambertMap
          have hpow : Real.exp (-3 * β) = r ^ 3 := by
            rw [← hrexp, ← Real.exp_nat_mul]
            congr 1
            ring_nf
          rw [hpow]
          ring_nf
        rw [hmap3, hwmap]
        have hneg : -β * r < 0 :=
          mul_neg_of_neg_of_pos (neg_neg_of_pos hβ) hr
        have := mul_lt_mul_of_neg_left htop hneg
        nlinarith
      exact (not_lt_of_ge hupper) (hmap3lt.trans hmap)
  · intro hyq
    have hwqlt : wq < w := by
      rw [hwy]
      dsimp only [wq]
      nlinarith
    have hwqLower : wq ≤ -1 := hwqlt.le.trans hwle
    exact lambertMap_strictAntiOn_lower hwqLower hwle hwqlt

/-- Exact Lambert-`W₋₁` formula for the permanent geometric tail
threshold.  The natural floor is the type-correct version of the
manuscript's integer-valued floor display. -/
theorem tailThreshold_eq_floor_lowerLambertW {r t : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (ht : 0 < t) (htop : t < 3 * r ^ 2) :
    tailThreshold r t = ⌊ lowerLambertTailCoordinate r t ⌋₊ := by
  let y := lowerLambertTailCoordinate r t
  let N : ℕ := ⌊y⌋₊
  have hy3 : 3 < y := by
    simpa [y] using three_lt_lowerLambertTailCoordinate hr hr1 ht htop
  have hy0 : 0 ≤ y := hy3.le.trans' (by norm_num)
  have hN3 : 3 ≤ N := by
    exact Nat.le_floor hy3.le
  have hyN : y < ((N + 1 : ℕ) : ℝ) := by
    simpa [N] using Nat.lt_floor_add_one y
  have hNadmissible : TailAdmissible r t N := by
    refine ⟨hN3.trans' (by norm_num), ?_⟩
    intro m hm
    apply (tailModel_lt_iff_lowerLambertTailCoordinate_lt hr hr1 ht htop
      (hN3.trans hm |>.trans' (by norm_num))).2
    exact hyN.trans_le (by exact_mod_cast Nat.add_le_add_right hm 1)
  apply le_antisymm (tailThreshold_le_of_admissible hNadmissible)
  have hT := tailThreshold_admissible hr.le hr1 ht
  have hyT : y < (((tailThreshold r t) + 1 : ℕ) : ℝ) :=
    (tailModel_lt_iff_lowerLambertTailCoordinate_lt hr hr1 ht htop hT.1).1
      (hT.2 (tailThreshold r t) le_rfl)
  have hfloorLt : ⌊y⌋₊ < tailThreshold r t + 1 :=
    (Nat.floor_lt hy0).2 hyT
  exact Nat.lt_add_one_iff.mp hfloorLt

/-- The exact threshold formula with the lower branch written out rather
than abbreviated by `lowerLambertTailCoordinate`. -/
theorem tailThreshold_eq_floor_lowerLambertW_explicit {r t : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (ht : 0 < t) (htop : t < 3 * r ^ 2) :
    tailThreshold r t =
      ⌊-lowerLambertW (-(tailBeta r * r * t)) / tailBeta r⌋₊ := by
  simpa [lowerLambertTailCoordinate] using
    tailThreshold_eq_floor_lowerLambertW hr hr1 ht htop

/-- Logarithmic--logarithmic scale in the standard lower-branch expansion. -/
def lowerLambertLogScale (u : ℝ) : ℝ :=
  Real.log (1 / u) + Real.log (Real.log (1 / u))

/-- Formal bounded-error version of the standard lower-branch expansion
`-W₋₁(-u)=log(1/u)+log log(1/u)+O(1)` as `u↓0`.  This is deduced
from the exact floor identity and the independently formalized elementary
inversion, so it introduces no analytic axiom for Lambert `W`. -/
theorem lowerLambertW_lower_branch_boundedErrorAtZero :
    BoundedErrorAtZero (fun u : ℝ => -lowerLambertW (-u))
      lowerLambertLogScale := by
  let r₀ : ℝ := Real.exp (-1)
  let c : ℝ := 1 / r₀
  have hr₀ : 0 < r₀ := Real.exp_pos (-1)
  have hr₀one : r₀ < 1 := by
    dsimp only [r₀]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hc : 0 < c := one_div_pos.mpr hr₀
  obtain ⟨C, hC, u₀, hu₀, hbound⟩ :=
    tailThreshold_mul_boundedErrorAtZero hr₀ hr₀one hc
  refine ⟨1 + C, by positivity, min u₀ (3 * r₀ ^ 3),
    lt_min hu₀ (mul_pos (by norm_num) (pow_pos hr₀ 3)), ?_⟩
  intro u hu hsmall
  have hu₀small : u < u₀ := hsmall.trans_le (min_le_left _ _)
  have hucsmall : u < 3 * r₀ ^ 3 :=
    hsmall.trans_le (min_le_right _ _)
  have hct : 0 < c * u := mul_pos hc hu
  have hctop : c * u < 3 * r₀ ^ 2 := by
    dsimp only [c]
    rw [one_div_mul_eq_div]
    apply (div_lt_iff₀ hr₀).2
    calc
      u < 3 * r₀ ^ 3 := hucsmall
      _ = 3 * r₀ ^ 2 * r₀ := by ring_nf
  have hformula := tailThreshold_eq_floor_lowerLambertW_explicit
    hr₀ hr₀one hct hctop
  have hbeta : tailBeta r₀ = 1 := by
    simp [tailBeta, r₀]
  have harg : -(tailBeta r₀ * r₀ * (c * u)) = -u := by
    rw [hbeta]
    dsimp only [c]
    field_simp [hr₀.ne']
  have hformula' :
      tailThreshold r₀ (c * u) = ⌊-lowerLambertW (-u)⌋₊ := by
    rw [harg, hbeta] at hformula
    simpa using hformula
  have hz : LowerLambertDomain (-u) := by
    simpa [harg] using
      lowerLambert_tail_argument_mem_domain hr₀ hr₀one hct hctop
  let y : ℝ := -lowerLambertW (-u)
  have hyone : 1 ≤ y := by
    dsimp only [y]
    linarith [lowerLambertW_le_neg_one hz]
  have hy0 : 0 ≤ y := zero_le_one.trans hyone
  have hfloorLower : ((⌊y⌋₊ : ℕ) : ℝ) ≤ y := Nat.floor_le hy0
  have hfloorUpper : y < ((⌊y⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one y
  have hround : |y - ((⌊y⌋₊ : ℕ) : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hfloorLower)]
    linarith
  have hscale : tailInversionScale r₀ u = lowerLambertLogScale u := by
    simp [tailInversionScale, lowerLambertLogScale, r₀]
  have htail :
      |((tailThreshold r₀ (c * u) : ℕ) : ℝ) -
          lowerLambertLogScale u| ≤ C := by
    rw [← hscale]
    exact hbound u hu hu₀small
  have hfloor :
      |((⌊y⌋₊ : ℕ) : ℝ) - lowerLambertLogScale u| ≤ C := by
    simpa [y, hformula'] using htail
  change |y - lowerLambertLogScale u| ≤ 1 + C
  calc
    |y - lowerLambertLogScale u| =
        |(y - ((⌊y⌋₊ : ℕ) : ℝ)) +
          (((⌊y⌋₊ : ℕ) : ℝ) - lowerLambertLogScale u)| := by ring_nf
    _ ≤ |y - ((⌊y⌋₊ : ℕ) : ℝ)| +
        |((⌊y⌋₊ : ℕ) : ℝ) - lowerLambertLogScale u| :=
      abs_add_le _ _
    _ ≤ 1 + C := add_le_add hround hfloor

end

end ConnectedPseudospectrum
