import ConnectedPseudospectrum.HalfChordSigned

/-!
# Odd folded determinant reduction to the signed half-chord equation

For `K = 2m+2`, this module substitutes the exact half variables into the
odd Chebyshev divided difference, proves the complete numerator factorization,
and cancels only explicitly nonzero factors to obtain the paper's signed
half-chord equation for the actual folded transfer sequence.
-/

namespace ConnectedPseudospectrum

noncomputable section

theorem foldOddBeta_signed_halfChord
    {a θ η varsigma : ℝ} (ha0 : 0 < a) :
    foldOddBeta a (halfChordX a θ η)
        (varsigma * halfChordS a θ η) =
      halfChordScale a *
        (Real.cos θ * Real.cosh η *
            (2 * Real.cosh (pathLogParameter a) ^ 2 - 1) +
          varsigma * halfTrigRadical a θ * halfHypRadical a η) := by
  have hsum := two_pathRate_mul_cosh_pathLogParameter ha0
  have hr := pathRate_mul_self ha0.le
  have hr2 : pathRate a ^ 2 = a := by simpa [pow_two] using hr
  have hc : Real.cosh (pathLogParameter a) ≠ 0 :=
    (Real.cosh_pos _).ne'
  have hbase :
      1 + a ^ 2 =
        2 * a * (2 * Real.cosh (pathLogParameter a) ^ 2 - 1) := by
    have hsquare := congrArg (fun w : ℝ => w ^ 2) hsum
    dsimp only at hsquare
    have hsquare' :
        4 * pathRate a ^ 2 * Real.cosh (pathLogParameter a) ^ 2 =
          (1 + a) ^ 2 := by
      calc
        4 * pathRate a ^ 2 * Real.cosh (pathLogParameter a) ^ 2 =
            (2 * pathRate a * Real.cosh (pathLogParameter a)) ^ 2 := by ring
        _ = (1 + a) ^ 2 := hsquare
    rw [hr2] at hsquare'
    nlinarith
  unfold foldOddBeta halfChordX halfChordS halfChordScale
  rw [hbase]
  field_simp [ha0.ne', hc]

theorem foldOddChebyshev_numerator_signed_halfChord
    (m : ℕ) {a θ η varsigma : ℝ} (ha0 : 0 < a)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a)
    (hsign : varsigma ^ 2 = 1) (hy : Real.cos θ ≠ 0) :
    foldOddChebyshevFunction m (halfChordX a θ η)
          (varsigma * halfChordS a θ η)
          (foldOddBeta a (halfChordX a θ η)
            (varsigma * halfChordS a θ η))
          (foldXiPlus a (halfChordX a θ η)
            (varsigma * halfChordS a θ η)) -
        foldOddChebyshevFunction m (halfChordX a θ η)
          (varsigma * halfChordS a θ η)
          (foldOddBeta a (halfChordX a θ η)
            (varsigma * halfChordS a θ η))
          (foldXiMinus a (halfChordX a θ η)
            (varsigma * halfChordS a θ η)) =
      varsigma * halfChordScale a *
        (halfHypRadical a η * Real.cos θ +
          varsigma * halfTrigRadical a θ * Real.cosh η) *
        (halfTrigRadical a θ * chebyshevU (2 * m + 1) (Real.cos θ) -
          varsigma * halfHypRadical a η *
            chebyshevU (2 * m + 1) (Real.cosh η)) := by
  rw [foldXiPlus_signed_halfChord ha0 hη0 hηh hsign,
    foldXiMinus_signed_halfChord ha0 hη0 hηh hsign,
    foldOddBeta_signed_halfChord ha0]
  unfold foldOddChebyshevFunction
  rw [chebyshevU_half_angle_odd_index m (Real.cosh_pos η).ne',
    chebyshevU_half_angle_odd_index m hy]
  let L := halfChordScale a
  let y := Real.cos θ
  let z := Real.cosh η
  let p := halfTrigRadical a θ
  let q := halfHypRadical a η
  let c := Real.cosh (pathLogParameter a)
  have hp : p ^ 2 = c ^ 2 - y ^ 2 := by
    exact halfTrigRadical_sq a θ
  have hq : q ^ 2 = c ^ 2 - z ^ 2 := by
    exact halfHypRadical_sq hη0 hηh
  have hzcoef :
      (L * y * z - varsigma * L * p * q) * (2 * z ^ 2 - 1) -
          L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q) =
        -2 * L * q * z * (y * q + varsigma * p * z) := by
    have hzsub : z ^ 2 - c ^ 2 = -q ^ 2 := by linarith
    calc
      (L * y * z - varsigma * L * p * q) * (2 * z ^ 2 - 1) -
            L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q) =
          L * (2 * y * z * (z ^ 2 - c ^ 2) -
            2 * varsigma * p * q * z ^ 2) := by ring
      _ = -2 * L * q * z * (y * q + varsigma * p * z) := by
        rw [hzsub]
        ring
  have hycoef :
      (L * y * z - varsigma * L * p * q) * (2 * y ^ 2 - 1) -
          L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q) =
        -2 * L * p * y * (z * p + varsigma * q * y) := by
    have hysub : y ^ 2 - c ^ 2 = -p ^ 2 := by linarith
    calc
      (L * y * z - varsigma * L * p * q) * (2 * y ^ 2 - 1) -
            L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q) =
          L * (2 * y * z * (y ^ 2 - c ^ 2) -
            2 * varsigma * p * q * y ^ 2) := by ring
      _ = -2 * L * p * y * (z * p + varsigma * q * y) := by
        rw [hysub]
        ring
  have hswap : z * p + varsigma * q * y =
      varsigma * (y * q + varsigma * p * z) := by
    calc
      z * p + varsigma * q * y =
          varsigma ^ 2 * p * z + varsigma * q * y := by rw [hsign]; ring
      _ = varsigma * (y * q + varsigma * p * z) := by ring
  have hzcoef' :
      (L * y * z - varsigma * (L * p * q)) * (2 * z ^ 2 - 1) -
          L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q) =
        -2 * L * q * z * (y * q + varsigma * p * z) := by
    convert hzcoef using 1
    all_goals ring
  have hycoef' :
      (L * y * z - varsigma * (L * p * q)) * (2 * y ^ 2 - 1) -
          L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q) =
        -2 * L * p * y * (z * p + varsigma * q * y) := by
    convert hycoef using 1
    all_goals ring
  change
    (((L * y * z - varsigma * (L * p * q)) * (2 * z ^ 2 - 1) -
        L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q)) *
          (chebyshevU (2 * m + 1) z / (2 * z)) -
      ((L * y * z - varsigma * (L * p * q)) * (2 * y ^ 2 - 1) -
        L * (y * z * (2 * c ^ 2 - 1) + varsigma * p * q)) *
          (chebyshevU (2 * m + 1) y / (2 * y))) =
      varsigma * L * (q * y + varsigma * p * z) *
        (p * chebyshevU (2 * m + 1) y -
          varsigma * q * chebyshevU (2 * m + 1) z)
  rw [hzcoef', hycoef', hswap]
  have hz : z ≠ 0 := (Real.cosh_pos η).ne'
  have hy' : y ≠ 0 := hy
  field_simp [hz, hy']
  have hbracket :
      -(q * chebyshevU (2 * m + 1) z) -
          -(varsigma * p * chebyshevU (2 * m + 1) y) =
        varsigma *
          (p * chebyshevU (2 * m + 1) y -
            varsigma * q * chebyshevU (2 * m + 1) z) := by
    calc
      -(q * chebyshevU (2 * m + 1) z) -
            -(varsigma * p * chebyshevU (2 * m + 1) y) =
          varsigma * p * chebyshevU (2 * m + 1) y -
            q * chebyshevU (2 * m + 1) z := by ring
      _ = varsigma * p * chebyshevU (2 * m + 1) y -
            varsigma ^ 2 * q * chebyshevU (2 * m + 1) z := by
          simp [hsign]
      _ = varsigma *
          (p * chebyshevU (2 * m + 1) y -
            varsigma * q * chebyshevU (2 * m + 1) z) := by ring
  rw [hbracket]
  ring

theorem foldOddSequence_signed_halfChord_factorization
    (m : ℕ) {a θ η varsigma : ℝ} (ha0 : 0 < a) (ha1 : a ≠ 1)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a)
    (hsign : varsigma ^ 2 = 1)
    (hdistinct : Real.cosh η ^ 2 ≠ Real.cos θ ^ 2)
    (hy : Real.cos θ ≠ 0) :
    foldOddSequence a (halfChordX a θ η)
        (varsigma * halfChordS a θ η) m =
      a ^ m *
        (varsigma * halfChordScale a *
          (halfHypRadical a η * Real.cos θ +
            varsigma * halfTrigRadical a θ * Real.cosh η) *
          (halfTrigRadical a θ * chebyshevU (2 * m + 1) (Real.cos θ) -
            varsigma * halfHypRadical a η *
              chebyshevU (2 * m + 1) (Real.cosh η)) /
          ((2 * Real.cosh η ^ 2 - 1) -
            (2 * Real.cos θ ^ 2 - 1))) := by
  have hxi := foldXi_signed_halfChord_ne ha0 hη0 hηh hsign hdistinct
  have hsum := foldXiPlus_add_foldXiMinus
    (x := halfChordX a θ η)
    (s := varsigma * halfChordS a θ η) ha0.ne'
  have hdisc : 0 ≤ foldDiscriminant a (halfChordX a θ η)
      (varsigma * halfChordS a θ η) := by
    rw [foldDiscriminant_signed_halfChord_eq a θ η varsigma hsign,
      foldDiscriminant_halfChord ha0 hη0 hηh]
    positivity
  have hprod := foldXiPlus_mul_foldXiMinus
    (x := halfChordX a θ η)
    (s := varsigma * halfChordS a θ η) ha0.ne' hdisc
  rw [foldOddSequence_eq_chebyshevDividedDifference
    ha0.ne' ha1 hxi hsum hprod m]
  rw [foldOddChebyshev_numerator_signed_halfChord m ha0 hη0 hηh hsign hy,
    foldXiPlus_signed_halfChord ha0 hη0 hηh hsign,
    foldXiMinus_signed_halfChord ha0 hη0 hηh hsign]

theorem foldOddSequence_signed_halfChord_eq_zero_iff
    (m : ℕ) {a θ η varsigma : ℝ} (ha0 : 0 < a) (ha1 : a ≠ 1)
    (hη0 : 0 ≤ η) (hηh : η ≤ pathLogParameter a)
    (hsign : varsigma ^ 2 = 1)
    (hdistinct : Real.cosh η ^ 2 ≠ Real.cos θ ^ 2)
    (hy : Real.cos θ ≠ 0) :
    foldOddSequence a (halfChordX a θ η)
        (varsigma * halfChordS a θ η) m = 0 ↔
      halfTrigRadical a θ * chebyshevU (2 * m + 1) (Real.cos θ) =
        varsigma * halfHypRadical a η *
          chebyshevU (2 * m + 1) (Real.cosh η) := by
  rw [foldOddSequence_signed_halfChord_factorization m ha0 ha1
    hη0 hηh hsign hdistinct hy]
  have haPow : a ^ m ≠ 0 := pow_ne_zero _ ha0.ne'
  have hsigma : varsigma ≠ 0 := by
    intro hs
    rw [hs] at hsign
    norm_num at hsign
  have hscale : halfChordScale a ≠ 0 := by
    unfold halfChordScale pathRate
    exact div_ne_zero (mul_ne_zero (by norm_num) (Real.sqrt_pos.2 ha0).ne')
      (Real.cosh_pos _).ne'
  have hextra := halfChord_odd_extra_factor_ne_zero
    hη0 hηh hsign hdistinct
  have hpref :
      varsigma * halfChordScale a *
          (halfHypRadical a η * Real.cos θ +
            varsigma * halfTrigRadical a θ * Real.cosh η) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hsigma hscale) hextra
  have hden :
      (2 * Real.cosh η ^ 2 - 1) - (2 * Real.cos θ ^ 2 - 1) ≠ 0 := by
    intro h
    apply hdistinct
    linarith
  have hden' : 2 * Real.cosh η ^ 2 - 2 * Real.cos θ ^ 2 ≠ 0 := by
    intro h
    apply hdistinct
    linarith
  constructor
  · intro h
    have hdiv :
        varsigma * halfChordScale a *
              (halfHypRadical a η * Real.cos θ +
                varsigma * halfTrigRadical a θ * Real.cosh η) *
              (halfTrigRadical a θ *
                  chebyshevU (2 * m + 1) (Real.cos θ) -
                varsigma * halfHypRadical a η *
                  chebyshevU (2 * m + 1) (Real.cosh η)) /
            ((2 * Real.cosh η ^ 2 - 1) - (2 * Real.cos θ ^ 2 - 1)) = 0 :=
      (mul_eq_zero.mp h).resolve_left haPow
    have hnum :
        varsigma * halfChordScale a *
              (halfHypRadical a η * Real.cos θ +
                varsigma * halfTrigRadical a θ * Real.cosh η) *
              (halfTrigRadical a θ *
                  chebyshevU (2 * m + 1) (Real.cos θ) -
                varsigma * halfHypRadical a η *
              chebyshevU (2 * m + 1) (Real.cosh η)) = 0 := by
      simpa [hden, hden'] using hdiv
    have hres :
        halfTrigRadical a θ * chebyshevU (2 * m + 1) (Real.cos θ) -
            varsigma * halfHypRadical a η *
              chebyshevU (2 * m + 1) (Real.cosh η) = 0 :=
      (mul_eq_zero.mp hnum).resolve_left hpref
    exact sub_eq_zero.mp hres
  · intro hchord
    have hres :
        halfTrigRadical a θ * chebyshevU (2 * m + 1) (Real.cos θ) -
            varsigma * halfHypRadical a η *
              chebyshevU (2 * m + 1) (Real.cosh η) = 0 :=
      sub_eq_zero.mpr hchord
    rw [hres, mul_zero, zero_div, mul_zero]

end

end ConnectedPseudospectrum
