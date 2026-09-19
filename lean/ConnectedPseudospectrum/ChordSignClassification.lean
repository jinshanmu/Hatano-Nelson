import ConnectedPseudospectrum.HalfChordEvenReduction
import ConnectedPseudospectrum.HalfChordOddReduction
import ConnectedPseudospectrum.ChordLobes
import Mathlib.Data.Real.Sign

/-!
# Sign classification for signed half-angle chords

This module proves the sign step following `eq:signed-half-chord`.  It then
combines that classification with the even and odd folded-sequence reductions.
-/

namespace ConnectedPseudospectrum

noncomputable section

/-- An indexed nodal interval with `j < K` lies strictly inside `(0, pi)`. -/
theorem nodalInterval_mem_Ioo_zero_pi
    (K j : ℕ) (hK : 2 ≤ K) (hj : j < K) {θ : ℝ}
    (hθ : (j : ℝ) * Real.pi / K < θ ∧
      θ < ((j + 1 : ℕ) : ℝ) * Real.pi / K) :
    θ ∈ Set.Ioo (0 : ℝ) Real.pi := by
  have hKpos : (0 : ℝ) < K := by positivity
  have hleft : 0 ≤ (j : ℝ) * Real.pi / K := by positivity
  have hjcast : ((j + 1 : ℕ) : ℝ) ≤ K := by
    exact_mod_cast (by omega : j + 1 ≤ K)
  have hendpoint : ((j + 1 : ℕ) : ℝ) * Real.pi / K ≤ Real.pi := by
    rw [div_le_iff₀ hKpos]
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_right hjcast Real.pi_pos.le)
  exact ⟨hleft.trans_lt hθ.1, hθ.2.trans_le hendpoint⟩

/-- On the `j`-th open nodal interval, the Chebyshev factor has signed
positive value `(-1)^j U_{K-1}(cos theta)`. -/
theorem negOnePow_mul_chebyshevU_cos_pos
    (K j : ℕ) (hK : 2 ≤ K) (hj : j < K) {θ : ℝ}
    (hθ : (j : ℝ) * Real.pi / K < θ ∧
      θ < ((j + 1 : ℕ) : ℝ) * Real.pi / K) :
    0 < (-1 : ℝ) ^ j * chebyshevU (K - 1 : ℕ) (Real.cos θ) := by
  have hKpos : (0 : ℝ) < K := by positivity
  have hθrange := nodalInterval_mem_Ioo_zero_pi K j hK hj hθ
  have hsinθ : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθrange.1 hθrange.2
  let δ : ℝ := (K : ℝ) * θ - (j : ℝ) * Real.pi
  have hlower : (j : ℝ) * Real.pi < (K : ℝ) * θ := by
    have h := (div_lt_iff₀ hKpos).mp hθ.1
    simpa only [mul_comm] using h
  have hupper : (K : ℝ) * θ < (j : ℝ) * Real.pi + Real.pi := by
    have h := (lt_div_iff₀ hKpos).mp hθ.2
    calc
      (K : ℝ) * θ = θ * K := by ring
      _ < ((j + 1 : ℕ) : ℝ) * Real.pi := h
      _ = (j : ℝ) * Real.pi + Real.pi := by
        push_cast
        ring
  have hδpos : 0 < δ := by
    dsimp only [δ]
    linarith
  have hδpi : δ < Real.pi := by
    dsimp only [δ]
    linarith
  have hsinδ : 0 < Real.sin δ :=
    Real.sin_pos_of_pos_of_lt_pi hδpos hδpi
  have hdecomp : (K : ℝ) * θ = δ + (j : ℝ) * Real.pi := by
    dsimp only [δ]
    ring
  have hsinK : Real.sin (K * θ) =
      (-1 : ℝ) ^ j * Real.sin δ := by
    rw [hdecomp]
    exact Real.sin_add_nat_mul_pi δ j
  have hsignedSin : 0 < (-1 : ℝ) ^ j * Real.sin (K * θ) := by
    rcases neg_one_pow_eq_or ℝ j with hpow | hpow
    · rw [hsinK, hpow]
      simpa only [one_mul] using hsinδ
    · rw [hsinK, hpow]
      simpa only [neg_one_mul, neg_neg] using hsinδ
  have hcast : ((K - 1 : ℕ) : ℝ) + 1 = K := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ K)
  have hcheb :
      chebyshevU (K - 1 : ℕ) (Real.cos θ) * Real.sin θ =
        Real.sin (K * θ) := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one, hcast] using
      chebyshevU_cos_mul_sin (K - 1 : ℕ) θ
  have hprod :
      0 < ((-1 : ℝ) ^ j *
        chebyshevU (K - 1 : ℕ) (Real.cos θ)) * Real.sin θ := by
    rw [mul_assoc, hcheb]
    exact hsignedSin
  exact pos_of_mul_pos_left hprod hsinθ.le

/-- The real sign of the Chebyshev factor on the `j`-th nodal interval is
exactly `(-1)^j`, as asserted after `eq:signed-half-chord`. -/
theorem sign_chebyshevU_cos_nodalInterval
    (K j : ℕ) (hK : 2 ≤ K) (hj : j < K) {θ : ℝ}
    (hθ : (j : ℝ) * Real.pi / K < θ ∧
      θ < ((j + 1 : ℕ) : ℝ) * Real.pi / K) :
    Real.sign (chebyshevU (K - 1 : ℕ) (Real.cos θ)) = (-1 : ℝ) ^ j := by
  have hsigned := negOnePow_mul_chebyshevU_cos_pos K j hK hj hθ
  rcases neg_one_pow_eq_or ℝ j with hpow | hpow
  · have hpos : 0 < chebyshevU (K - 1 : ℕ) (Real.cos θ) := by
      simpa only [hpow, one_mul] using hsigned
    rw [hpow, Real.sign_of_pos hpos]
  · have hneg : chebyshevU (K - 1 : ℕ) (Real.cos θ) < 0 := by
      rw [hpow, neg_one_mul] at hsigned
      linarith
    rw [hpow, Real.sign_of_neg hneg]

/-- Absolute-value form of the nodal sign classification. -/
theorem chebyshevU_cos_eq_negOnePow_mul_abs
    (K j : ℕ) (hK : 2 ≤ K) (hj : j < K) {θ : ℝ}
    (hθ : (j : ℝ) * Real.pi / K < θ ∧
      θ < ((j + 1 : ℕ) : ℝ) * Real.pi / K) :
    chebyshevU (K - 1 : ℕ) (Real.cos θ) =
      (-1 : ℝ) ^ j * |chebyshevU (K - 1 : ℕ) (Real.cos θ)| := by
  have hsigned := negOnePow_mul_chebyshevU_cos_pos K j hK hj hθ
  rcases neg_one_pow_eq_or ℝ j with hpow | hpow
  · have hpos : 0 < chebyshevU (K - 1 : ℕ) (Real.cos θ) := by
      simpa only [hpow, one_mul] using hsigned
    simp only [hpow, one_mul, abs_of_pos hpos]
  · have hneg : chebyshevU (K - 1 : ℕ) (Real.cos θ) < 0 := by
      rw [hpow, neg_one_mul] at hsigned
      linarith
    simp only [hpow, neg_one_mul, abs_of_neg hneg, neg_neg]

/-- The radical-weighted trigonometric Chebyshev factor is the signed
channel magnitude. -/
theorem halfTrigRadical_mul_chebyshevU_eq_negOnePow_mul_chordPhi
    (K j : ℕ) (hK : 2 ≤ K) (hj : j < K)
    (a : ℝ) {θ : ℝ}
    (hθ : (j : ℝ) * Real.pi / K < θ ∧
      θ < ((j + 1 : ℕ) : ℝ) * Real.pi / K) :
    halfTrigRadical a θ * chebyshevU (K - 1 : ℕ) (Real.cos θ) =
      (-1 : ℝ) ^ j * chordPhi K a θ := by
  rw [chebyshevU_cos_eq_negOnePow_mul_abs K j hK hj hθ]
  simp only [chordPhi]
  ring

/-- The radical-weighted hyperbolic Chebyshev factor is exactly the
hyperbolic channel magnitude. -/
theorem halfHypRadical_mul_chebyshevU_eq_chordPsi
    (K : ℕ) (a η : ℝ) :
    halfHypRadical a η * chebyshevU (K - 1 : ℕ) (Real.cosh η) =
      chordPsi K a η := by
  rfl

/-- Positivity of the trigonometric channel on an open nodal interval,
given positivity of its radical factor. -/
theorem chordPhi_pos_on_nodalInterval
    (K j : ℕ) (hK : 2 ≤ K) (hj : j < K)
    (a : ℝ) {θ : ℝ}
    (hθ : (j : ℝ) * Real.pi / K < θ ∧
      θ < ((j + 1 : ℕ) : ℝ) * Real.pi / K)
    (htrig : 0 < halfTrigRadical a θ) :
    0 < chordPhi K a θ := by
  have hsigned := negOnePow_mul_chebyshevU_cos_pos K j hK hj hθ
  have hcheb : chebyshevU (K - 1 : ℕ) (Real.cos θ) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hsigned
    exact (lt_irrefl 0 hsigned)
  rw [chordPhi]
  exact mul_pos htrig (abs_pos.mpr hcheb)

/-- Positivity of the hyperbolic channel when its radical factor is
positive. -/
theorem chordPsi_pos_of_halfHypRadical_pos
    (K : ℕ) (hK : 2 ≤ K) (a : ℝ) {η : ℝ}
    (hη0 : 0 ≤ η) (hhyp : 0 < halfHypRadical a η) :
    0 < chordPsi K a η := by
  rw [chordPsi]
  exact mul_pos hhyp (chebyshevU_cosh_pos K hK hη0)

/-- Positivity of the outer Chebyshev factor on the half-chord hyperbolic
coordinate range `0 ≤ eta ≤ h`. -/
theorem chebyshevU_cosh_pos_on_halfChord
    (K : ℕ) (hK : 2 ≤ K) {a η : ℝ}
    (hη : η ∈ Set.Icc (0 : ℝ) (pathLogParameter a)) :
    0 < chebyshevU (K - 1 : ℕ) (Real.cosh η) :=
  chebyshevU_cosh_pos K hK hη.1

/-- Sign classification of `eq:signed-half-chord`: on the `j`-th nodal
interval, the signed half-chord equation is equivalent to the forced sign
`varsigma=(-1)^j` together with equality of the two channel magnitudes. -/
theorem signedHalfChord_eq_iff_sign_and_channels
    (K j : ℕ) (hK : 2 ≤ K) (hj : j < K)
    {a θ η varsigma : ℝ}
    (hθ : (j : ℝ) * Real.pi / K < θ ∧
      θ < ((j + 1 : ℕ) : ℝ) * Real.pi / K)
    (hη : η ∈ Set.Icc (0 : ℝ) (pathLogParameter a))
    (hsign : varsigma ^ 2 = 1)
    (htrig : 0 < halfTrigRadical a θ)
    (hhyp : 0 < halfHypRadical a η) :
    (halfTrigRadical a θ *
          chebyshevU (K - 1 : ℕ) (Real.cos θ) =
        varsigma * halfHypRadical a η *
          chebyshevU (K - 1 : ℕ) (Real.cosh η)) ↔
      varsigma = (-1 : ℝ) ^ j ∧
        chordPhi K a θ = chordPsi K a η := by
  have hleft :=
    halfTrigRadical_mul_chebyshevU_eq_negOnePow_mul_chordPhi
      K j hK hj a hθ
  have hright := halfHypRadical_mul_chebyshevU_eq_chordPsi K a η
  have hPhiPos := chordPhi_pos_on_nodalInterval K j hK hj a hθ htrig
  have hPsiPos := chordPsi_pos_of_halfHypRadical_pos K hK a hη.1 hhyp
  have hfactor : (varsigma - 1) * (varsigma + 1) = 0 := by
    nlinarith
  have hvarsigma : varsigma = 1 ∨ varsigma = -1 := by
    rcases mul_eq_zero.mp hfactor with hplus | hminus
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  constructor
  · intro hchord
    rw [hleft, mul_assoc, hright] at hchord
    rcases neg_one_pow_eq_or ℝ j with hpow | hpow
    · rcases hvarsigma with hs | hs
      · refine ⟨hs.trans hpow.symm, ?_⟩
        simpa only [hpow, hs, one_mul] using hchord
      · have hbad : chordPhi K a θ = -chordPsi K a η := by
          simpa only [hpow, hs, one_mul, neg_one_mul] using hchord
        exfalso
        nlinarith
    · rcases hvarsigma with hs | hs
      · have hbad : -chordPhi K a θ = chordPsi K a η := by
          simpa only [hpow, hs, one_mul, neg_one_mul] using hchord
        exfalso
        nlinarith
      · refine ⟨hs.trans hpow.symm, ?_⟩
        have hneg : -chordPhi K a θ = -chordPsi K a η := by
          simpa only [hpow, hs, neg_one_mul] using hchord
        linarith
  · rintro ⟨hvarsigmaSign, hchannels⟩
    rw [hleft, mul_assoc, hright, hvarsigmaSign, hchannels]

/-- For `K=2m+1`, the actual even folded sequence vanishes exactly for
the forced nodal sign and the channel chord equation. -/
theorem foldEvenSequence_eq_zero_iff_sign_and_channels
    (m j : ℕ) (hm : 1 ≤ m) (hj : j < 2 * m + 1)
    {a θ η varsigma : ℝ}
    (ha0 : 0 < a)
    (hθ : (j : ℝ) * Real.pi / ((2 * m + 1 : ℕ) : ℝ) < θ ∧
      θ < ((j + 1 : ℕ) : ℝ) * Real.pi / ((2 * m + 1 : ℕ) : ℝ))
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a)
    (hsign : varsigma ^ 2 = 1)
    (hdistinct : Real.cosh η ^ 2 ≠ Real.cos θ ^ 2)
    (htrig : 0 < halfTrigRadical a θ)
    (hhyp : 0 < halfHypRadical a η) :
    foldEvenSequence a (halfChordX a θ η)
        (varsigma * halfChordS a θ η) m = 0 ↔
      varsigma = (-1 : ℝ) ^ j ∧
        chordPhi (2 * m + 1) a θ = chordPsi (2 * m + 1) a η := by
  rw [foldEvenSequence_signed_halfChord_eq_zero_iff m ha0
    hη0 hηh hsign hdistinct]
  have hclassification := signedHalfChord_eq_iff_sign_and_channels
    (K := 2 * m + 1) (j := j) (by omega) hj hθ
      ⟨hη0, hηh⟩ hsign htrig hhyp
  have hindex : 2 * m + 1 - 1 = 2 * m := by omega
  simpa only [hindex] using hclassification

/-- For `K=2m+2`, the actual odd folded sequence vanishes exactly for
the forced nodal sign and the channel chord equation. -/
theorem foldOddSequence_eq_zero_iff_sign_and_channels
    (m j : ℕ) (hj : j < 2 * m + 2)
    {a θ η varsigma : ℝ}
    (ha0 : 0 < a)
    (hθ : (j : ℝ) * Real.pi / ((2 * m + 2 : ℕ) : ℝ) < θ ∧
      θ < ((j + 1 : ℕ) : ℝ) * Real.pi / ((2 * m + 2 : ℕ) : ℝ))
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a)
    (hsign : varsigma ^ 2 = 1)
    (hdistinct : Real.cosh η ^ 2 ≠ Real.cos θ ^ 2)
    (hy : Real.cos θ ≠ 0)
    (htrig : 0 < halfTrigRadical a θ)
    (hhyp : 0 < halfHypRadical a η) :
    foldOddSequence a (halfChordX a θ η)
        (varsigma * halfChordS a θ η) m = 0 ↔
      varsigma = (-1 : ℝ) ^ j ∧
        chordPhi (2 * m + 2) a θ = chordPsi (2 * m + 2) a η := by
  rw [foldOddSequence_signed_halfChord_eq_zero_iff m ha0
    hη0 hηh hsign hdistinct hy]
  have hclassification := signedHalfChord_eq_iff_sign_and_channels
    (K := 2 * m + 2) (j := j) (by omega) hj hθ
      ⟨hη0, hηh⟩ hsign htrig hhyp
  have hindex : 2 * m + 2 - 1 = 2 * m + 1 := by omega
  simpa only [hindex] using hclassification

end

end ConnectedPseudospectrum
