import ConnectedPseudospectrum.Asymptotics
import ConnectedPseudospectrum.BoundaryCases

/-!
# Critical dimension at the normal boundary

For a positive hopping scale `c`, this module defines the first dimension
`n ≥ 2` at which `c * normalThreshold n < ε`.  The strict decrease of
`normalThreshold` makes all subsequent dimensions admissible.  The explicit
cubic remainder estimate from `BoundaryCases` then gives the uniform bound

`|normalCriticalThreshold c ε - π c / ε| < 2`

whenever `0 < ε ≤ c`.  This is the scalar content of
`eq:general-normal-critical` in the ELA manuscript.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- Uniform cubic remainder form of
`normalThreshold n = π / (n + 1) + O(n⁻³)`. -/
theorem normalThreshold_cubic_remainder (n : ℕ) :
    |normalThreshold n - Real.pi / (n + 1 : ℝ)| ≤
      Real.pi ^ 3 / (6 * (n + 1 : ℝ) ^ 3) := by
  have herror := normalThreshold_error_bound n
  rw [abs_of_nonpos (by linarith [herror.1])]
  linarith [herror.2]

/-- Dimensions at which the scaled normal half-gap is below `ε`. -/
def normalCriticalSet (c ε : ℝ) : Set ℕ :=
  {n | 2 ≤ n ∧ c * normalThreshold n < ε}

/-- The first dimension at which the scaled normal half-gap is below `ε`.
As usual for `sInf` on naturals, meaningful specifications use positivity of
`c` and `ε`, which makes the defining set nonempty. -/
def normalCriticalThreshold (c ε : ℝ) : ℕ :=
  sInf (normalCriticalSet c ε)

/-- The normal critical set is nonempty for positive scale and tolerance. -/
theorem normalCriticalSet_nonempty {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    (normalCriticalSet c ε).Nonempty := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.pi * c / ε)
  refine ⟨N + 2, ?_⟩
  constructor
  · omega
  · have herror := normalThreshold_error_bound (N + 2)
    push_cast at herror
    have hthreshold : normalThreshold (N + 2) ≤
        Real.pi / (N + 2 + 1 : ℝ) := by
      linarith [herror.1]
    have hden : 0 < (N + 2 + 1 : ℝ) := by positivity
    have hscale : Real.pi * c / (N + 2 + 1 : ℝ) < ε := by
      have hN' : Real.pi * c / ε < (N + 2 + 1 : ℝ) := by
        exact hN.trans (by exact_mod_cast (show N < N + 2 + 1 by omega))
      apply (div_lt_iff₀ hden).2
      apply (div_lt_iff₀ hε).1 at hN'
      nlinarith
    exact (mul_le_mul_of_nonneg_left hthreshold hc.le).trans_lt (by
      simpa [mul_div_assoc, mul_comm] using hscale)

/-- The normal critical threshold satisfies its defining crossing. -/
theorem normalCriticalThreshold_mem {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    normalCriticalThreshold c ε ∈ normalCriticalSet c ε := by
  exact Nat.sInf_mem (normalCriticalSet_nonempty hc hε)

/-- Minimality of the normal critical threshold. -/
theorem normalCriticalThreshold_le {c ε : ℝ} {n : ℕ}
    (hn : n ∈ normalCriticalSet c ε) :
    normalCriticalThreshold c ε ≤ n := by
  exact Nat.sInf_le hn

/-- The normal critical threshold is the least admissible dimension. -/
theorem normalCriticalThreshold_isLeast {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) :
    IsLeast (normalCriticalSet c ε) (normalCriticalThreshold c ε) :=
  ⟨normalCriticalThreshold_mem hc hε, fun _ hn => normalCriticalThreshold_le hn⟩

/-- Every dimension after the first normal crossing is also admissible. -/
theorem normalCriticalSet_of_threshold_le {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    {n : ℕ} (hn : normalCriticalThreshold c ε ≤ n) :
    n ∈ normalCriticalSet c ε := by
  have hm := normalCriticalThreshold_mem hc hε
  obtain ⟨hm2, hmcross⟩ := hm
  constructor
  · exact hm2.trans hn
  · have hantitone : AntitoneOn normalThreshold {k : ℕ | 2 ≤ k} :=
      antitoneOn_nat_Ici_of_succ_le fun k hk =>
        (normalThreshold_succ_lt k hk).le
    exact (mul_le_mul_of_nonneg_left
      (hantitone hm2 (hm2.trans hn) hn) hc.le).trans_lt hmcross

/-- If `ε ≤ c`, the first normal crossing occurs after dimension two.
This isolates the range in which the preceding-dimension inequality is
available. -/
theorem three_le_normalCriticalThreshold {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hεc : ε ≤ c) :
    3 ≤ normalCriticalThreshold c ε := by
  have hm := normalCriticalThreshold_mem hc hε
  by_contra hnot
  have hm2 : 2 ≤ normalCriticalThreshold c ε := hm.1
  have heq : normalCriticalThreshold c ε = 2 := by omega
  have heta : normalThreshold 2 = 1 := by
    rw [show 2 = 2 * 1 by norm_num, normalThreshold_even]
    norm_num [Real.sin_pi_div_six]
  change 2 ≤ normalCriticalThreshold c ε ∧
    c * normalThreshold (normalCriticalThreshold c ε) < ε at hm
  rw [heq, heta, mul_one] at hm
  exact (not_lt_of_ge hεc) hm.2

/-- Just before the first normal crossing, the scaled half-gap is still at
least `ε`. -/
theorem normalCriticalThreshold_predecessor_ge {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hεc : ε ≤ c) :
    ε ≤ c * normalThreshold (normalCriticalThreshold c ε - 1) := by
  let m := normalCriticalThreshold c ε
  have hm3 : 3 ≤ m := three_le_normalCriticalThreshold hc hε hεc
  have hmPred2 : 2 ≤ m - 1 := by omega
  by_contra hnot
  have hcross : c * normalThreshold (m - 1) < ε := lt_of_not_ge hnot
  have hmem : m - 1 ∈ normalCriticalSet c ε := ⟨hmPred2, hcross⟩
  have hmin : m ≤ m - 1 := normalCriticalThreshold_le hmem
  omega

/-- Explicit inversion of the normal threshold.  For `0 < ε ≤ c`, the
critical dimension lies strictly between `π c / ε - 2` and `π c / ε`.
-/
theorem normalCriticalThreshold_scale_bounds {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hεc : ε ≤ c) :
    (normalCriticalThreshold c ε : ℝ) ≤ Real.pi * c / ε ∧
      Real.pi * c / ε < (normalCriticalThreshold c ε : ℝ) + 2 := by
  let m := normalCriticalThreshold c ε
  have hm3 : 3 ≤ m := three_le_normalCriticalThreshold hc hε hεc
  have hprev := normalCriticalThreshold_predecessor_ge hc hε hεc
  have hcross := (normalCriticalThreshold_mem hc hε).2
  have herrorPrev := normalThreshold_error_bound (m - 1)
  have herror := normalThreshold_error_bound m
  push_cast at herror
  have hmPos : 0 < (m : ℝ) := by positivity
  have hetaPrevUpper : normalThreshold (m - 1) ≤ Real.pi / (m : ℝ) := by
    have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ m))
    rw [hcast] at herrorPrev
    linarith [herrorPrev.1]
  have hupper : (m : ℝ) ≤ Real.pi * c / ε := by
    have hscaled : ε ≤ c * (Real.pi / (m : ℝ)) :=
      hprev.trans (mul_le_mul_of_nonneg_left hetaPrevUpper hc.le)
    have hscaled' : ε * (m : ℝ) ≤ c * Real.pi := by
      apply (le_div_iff₀ hmPos).1
      simpa [mul_div_assoc, mul_comm] using hscaled
    exact (le_div_iff₀ hε).2 (by nlinarith)
  have hetaLower :
      Real.pi / (m + 1 : ℝ) -
          Real.pi ^ 3 / (6 * (m + 1 : ℝ) ^ 3) ≤ normalThreshold m := by
    linarith [herror.2]
  have hlowCross : c * (Real.pi / (m + 1 : ℝ) -
      Real.pi ^ 3 / (6 * (m + 1 : ℝ) ^ 3)) < ε :=
    (mul_le_mul_of_nonneg_left hetaLower hc.le).trans_lt hcross
  have hpiSq : Real.pi ^ 2 < 10 := by
    nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have hpoly : Real.pi ^ 2 * ((m : ℝ) + 2) <
      6 * ((m : ℝ) + 1) ^ 2 := by
    have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    have hrough : 10 * ((m : ℝ) + 2) ≤
        6 * ((m : ℝ) + 1) ^ 2 := by nlinarith
    exact (mul_lt_mul_of_pos_right hpiSq (by positivity)).trans_le hrough
  have hfactor : 0 < 1 - Real.pi ^ 2 / (6 * ((m : ℝ) + 1) ^ 2) := by
    have hdenSq : 0 < 6 * ((m : ℝ) + 1) ^ 2 := by positivity
    apply sub_pos.mpr
    apply (div_lt_one hdenSq).2
    have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    nlinarith [hpiSq]
  have hlower : Real.pi * c / ε < (m : ℝ) + 2 := by
    have hmOne : 0 < (m : ℝ) + 1 := by positivity
    have hnormalized :
        Real.pi * c /
            ((m : ℝ) + 1) *
              (1 - Real.pi ^ 2 / (6 * ((m : ℝ) + 1) ^ 2)) < ε := by
      convert hlowCross using 1
      field_simp [hmOne.ne']
    have hratio : Real.pi * c / ε <
        ((m : ℝ) + 1) /
          (1 - Real.pi ^ 2 / (6 * ((m : ℝ) + 1) ^ 2)) := by
      apply (div_lt_div_iff₀ hε hfactor).2
      have hcleared : Real.pi * c *
          (1 - Real.pi ^ 2 / (6 * ((m : ℝ) + 1) ^ 2)) <
            ε * ((m : ℝ) + 1) := by
        apply (div_lt_iff₀ hmOne).1
        convert hnormalized using 1; ring
      nlinarith
    apply hratio.trans_le
    apply (div_le_iff₀ hfactor).2
    have hdenSq : 0 < 6 * ((m : ℝ) + 1) ^ 2 := by positivity
    have hratioError :
        Real.pi ^ 2 * ((m : ℝ) + 2) /
            (6 * ((m : ℝ) + 1) ^ 2) < 1 :=
      (div_lt_one hdenSq).2 hpoly
    calc
      (m : ℝ) + 1 = ((m : ℝ) + 2) - 1 := by ring
      _ ≤ ((m : ℝ) + 2) -
          Real.pi ^ 2 * ((m : ℝ) + 2) /
            (6 * ((m : ℝ) + 1) ^ 2) := by linarith
      _ = ((m : ℝ) + 2) *
          (1 - Real.pi ^ 2 / (6 * ((m : ℝ) + 1) ^ 2)) := by ring
  exact ⟨hupper, hlower⟩

/-- Uniform two-unit error bound, an explicit form of
`normalCriticalThreshold c ε = π c / ε + O(1)`. -/
theorem normalCriticalThreshold_error_lt_two {c ε : ℝ}
    (hc : 0 < c) (hε : 0 < ε) (hεc : ε ≤ c) :
    |(normalCriticalThreshold c ε : ℝ) - Real.pi * c / ε| < 2 := by
  have hbounds := normalCriticalThreshold_scale_bounds hc hε hεc
  rw [abs_lt]
  constructor <;> linarith

/-- Bounded-error formulation of the normal critical-dimension asymptotic. -/
theorem normalCriticalThreshold_boundedErrorAtZero {c : ℝ} (hc : 0 < c) :
    BoundedErrorAtZero
      (fun ε : ℝ => (normalCriticalThreshold c ε : ℝ))
      (fun ε : ℝ => Real.pi * c / ε) := by
  refine ⟨2, by norm_num, c, hc, ?_⟩
  intro ε hε hεc
  exact (normalCriticalThreshold_error_lt_two hc hε hεc.le).le

end

end ConnectedPseudospectrum
