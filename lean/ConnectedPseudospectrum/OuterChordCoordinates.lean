import ConnectedPseudospectrum.ChordLobes
import ConnectedPseudospectrum.HalfChordAlgebra
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Coordinate charts for the endpoint-side outer chord

The outer variable `z` is primary.  Its portion above `1` has the unique
coordinate `z = cosh eta`; its portion below `1` has the unique coordinate
`z = cos phi`.  The coordinate-free chord values are shown to agree with
both chart formulas, including their common value at `z = 1`.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- Every `z` between `1` and `cosh h` has a unique hyperbolic coordinate
in `[0,h]`. -/
theorem existsUnique_hyperbolicOuterCoordinate
    (a z : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hz : z ∈ Icc (1 : ℝ) (Real.cosh (pathLogParameter a))) :
    ∃! η : ℝ, η ∈ Icc (0 : ℝ) (pathLogParameter a) ∧
      z = Real.cosh η := by
  let η := Real.arcosh z
  have hh : 0 < pathLogParameter a := pathLogParameter_pos ha0 ha1
  have hη0 : 0 ≤ η := by
    dsimp only [η]
    exact Real.arcosh_nonneg hz.1
  have hηh : η ≤ pathLogParameter a := by
    have hzpos : 0 < z := zero_lt_one.trans_le hz.1
    have hmono :=
      (Real.arcosh_le_arcosh hzpos
        (Real.cosh_pos (pathLogParameter a))).2 hz.2
    rw [Real.arcosh_cosh hh.le] at hmono
    exact hmono
  have hzη : z = Real.cosh η := by
    dsimp only [η]
    exact (Real.cosh_arcosh hz.1).symm
  refine ⟨η, ⟨⟨hη0, hηh⟩, hzη⟩, ?_⟩
  intro ξ hξ
  calc
    ξ = Real.arcosh (Real.cosh ξ) :=
      (Real.arcosh_cosh hξ.1.1).symm
    _ = Real.arcosh z := by rw [← hξ.2]
    _ = η := rfl

/-- Every `z` on the elliptic part of the outer lobe has a unique angle in
`[0,pi/K)`. -/
theorem existsUnique_ellipticOuterCoordinate
    (K : ℕ) (hK : 2 ≤ K) (z : ℝ)
    (hz : Real.cos (Real.pi / K) < z ∧ z ≤ 1) :
    ∃! φ : ℝ, φ ∈ Ico (0 : ℝ) (Real.pi / K) ∧
      z = Real.cos φ := by
  let φ := Real.arccos z
  have hKpos : (0 : ℝ) < K := by positivity
  have hangle0 : 0 ≤ Real.pi / (K : ℝ) := by positivity
  have hanglePi : Real.pi / (K : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hKpos]
    have hKcast : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
    nlinarith [Real.pi_pos]
  have hzLower : (-1 : ℝ) ≤ z :=
    (Real.neg_one_le_cos (Real.pi / K)).trans (le_of_lt hz.1)
  have hφ0 : 0 ≤ φ := by
    dsimp only [φ]
    exact Real.arccos_nonneg z
  have hφUpper : φ < Real.pi / K := by
    have hstrict := Real.arccos_lt_arccos
      (Real.neg_one_le_cos (Real.pi / K)) hz.1 hz.2
    rw [Real.arccos_cos hangle0 hanglePi] at hstrict
    exact hstrict
  have hzφ : z = Real.cos φ := by
    dsimp only [φ]
    exact (Real.cos_arccos hzLower hz.2).symm
  refine ⟨φ, ⟨⟨hφ0, hφUpper⟩, hzφ⟩, ?_⟩
  intro ψ hψ
  calc
    ψ = Real.arccos (Real.cos ψ) :=
      (Real.arccos_cos hψ.1.1 (hψ.1.2.le.trans hanglePi)).symm
    _ = Real.arccos z := by rw [← hψ.2]
    _ = φ := rfl

/-- Coordinate-free `x=L_0 cos(theta) z`. -/
def outerChordX (a θ z : ℝ) : ℝ :=
  halfChordScale a * Real.cos θ * z

/-- Coordinate-free positive-root magnitude
`s=L_0 sqrt((cosh(h)^2-cos(theta)^2)(cosh(h)^2-z^2))`. -/
def outerChordS (a θ z : ℝ) : ℝ :=
  halfChordScale a * Real.sqrt
    ((Real.cosh (pathLogParameter a) ^ 2 - Real.cos θ ^ 2) *
      (Real.cosh (pathLogParameter a) ^ 2 - z ^ 2))

/-- The elliptic `x` chart. -/
def ellipticChordX (a θ φ : ℝ) : ℝ :=
  halfChordScale a * Real.cos θ * Real.cos φ

/-- The source's elliptic radical expression `s_ell`. -/
def ellipticChordS (a θ φ : ℝ) : ℝ :=
  halfChordScale a * Real.sqrt
    ((Real.sinh (pathLogParameter a) ^ 2 + Real.sin θ ^ 2) *
      (Real.sinh (pathLogParameter a) ^ 2 + Real.sin φ ^ 2))

theorem outerChordX_cosh (a θ η : ℝ) :
    outerChordX a θ (Real.cosh η) = halfChordX a θ η := by
  rfl

theorem outerChordX_cos (a θ φ : ℝ) :
    outerChordX a θ (Real.cos φ) = ellipticChordX a θ φ := by
  rfl

theorem halfChordScale_pos {a : ℝ} (ha0 : 0 < a) :
    0 < halfChordScale a := by
  unfold halfChordScale pathRate
  exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 ha0))
    (Real.cosh_pos _)

/-- The trigonometric radical identity used to pass from the
coordinate-free formula to the elliptic chart. -/
theorem chordRadicand_cos_eq_sinh_sq_add_sin_sq (a t : ℝ) :
    Real.cosh (pathLogParameter a) ^ 2 - Real.cos t ^ 2 =
      Real.sinh (pathLogParameter a) ^ 2 + Real.sin t ^ 2 := by
  nlinarith [Real.cosh_sq_sub_sinh_sq (pathLogParameter a),
    Real.sin_sq_add_cos_sq t]

/-- In the hyperbolic chart, the coordinate-free radical is exactly the
existing half-chord radical product. -/
theorem outerChordS_cosh
    (a θ : ℝ) {η : ℝ}
    (hη : η ∈ Icc (0 : ℝ) (pathLogParameter a)) :
    outerChordS a θ (Real.cosh η) = halfChordS a θ η := by
  have hrad := halfHypRadicand_nonneg hη.1 hη.2
  unfold outerChordS halfChordS halfTrigRadical halfHypRadical
  rw [Real.sqrt_mul' _ hrad]
  ring

/-- In the elliptic chart, the coordinate-free radical is the source's
`s_ell` expression. -/
theorem outerChordS_cos (a θ φ : ℝ) :
    outerChordS a θ (Real.cos φ) = ellipticChordS a θ φ := by
  unfold outerChordS ellipticChordS
  rw [chordRadicand_cos_eq_sinh_sq_add_sin_sq a θ,
    chordRadicand_cos_eq_sinh_sq_add_sin_sq a φ]

/-- The printed `2r/cosh(h)` form of the source's elliptic radical. -/
theorem ellipticChordS_eq_source_formula (a θ φ : ℝ) :
    ellipticChordS a θ φ =
      2 * pathRate a / Real.cosh (pathLogParameter a) *
        Real.sqrt
          ((Real.sinh (pathLogParameter a) ^ 2 + Real.sin θ ^ 2) *
            (Real.sinh (pathLogParameter a) ^ 2 + Real.sin φ ^ 2)) := by
  rfl

theorem outerChordS_nonneg {a : ℝ} (ha0 : 0 < a) (θ z : ℝ) :
    0 ≤ outerChordS a θ z := by
  unfold outerChordS
  exact mul_nonneg (halfChordScale_pos ha0).le (Real.sqrt_nonneg _)

/-- Strict positivity of the coordinate-free chord magnitude away from the
two radical endpoints. -/
theorem outerChordS_pos_of_abs_lt_cosh
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) {z : ℝ}
    (hz : |z| < Real.cosh (pathLogParameter a)) :
    0 < outerChordS a θ z := by
  let h := pathLogParameter a
  let c := Real.cosh h
  have hh : 0 < h := pathLogParameter_pos ha0 ha1
  have hscale : 0 < halfChordScale a := halfChordScale_pos ha0
  have hsinh : 0 < Real.sinh h := Real.sinh_pos_iff.mpr hh
  have htrig : 0 < c ^ 2 - Real.cos θ ^ 2 := by
    have hid := chordRadicand_cos_eq_sinh_sq_add_sin_sq a θ
    change Real.cosh h ^ 2 - Real.cos θ ^ 2 =
      Real.sinh h ^ 2 + Real.sin θ ^ 2 at hid
    dsimp only [c]
    rw [hid]
    nlinarith [sq_pos_of_pos hsinh, sq_nonneg (Real.sin θ)]
  have hzbounds : -c < z ∧ z < c := by
    simpa only [abs_lt] using hz
  have hzrad : 0 < c ^ 2 - z ^ 2 := by
    have hprod : 0 < (c - z) * (c + z) :=
      mul_pos (sub_pos.mpr hzbounds.2) (by linarith)
    nlinarith
  unfold outerChordS
  change 0 < halfChordScale a *
    Real.sqrt ((c ^ 2 - Real.cos θ ^ 2) * (c ^ 2 - z ^ 2))
  exact mul_pos hscale (Real.sqrt_pos.2 (mul_pos htrig hzrad))

/-- Endpoint-side form of positivity: nonnegative `z` strictly below
`cosh(h)` gives a positive chord magnitude. -/
theorem outerChordS_pos_of_nonneg_of_lt_cosh
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) {z : ℝ}
    (hz0 : 0 ≤ z) (hzc : z < Real.cosh (pathLogParameter a)) :
    0 < outerChordS a θ z := by
  apply outerChordS_pos_of_abs_lt_cosh ha0 ha1 θ
  simpa only [abs_of_nonneg hz0] using hzc

/-- At `z=1`, the hyperbolic and elliptic formulas give the same `x` and
the same positive-root magnitude. -/
theorem outerChordFormulas_agree_at_one
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (θ : ℝ) :
    halfChordX a θ 0 = ellipticChordX a θ 0 ∧
      halfChordS a θ 0 = ellipticChordS a θ 0 := by
  have hzero : (0 : ℝ) ∈ Icc 0 (pathLogParameter a) :=
    ⟨le_rfl, (pathLogParameter_pos ha0 ha1).le⟩
  have hxHyp := outerChordX_cosh a θ 0
  have hxEll := outerChordX_cos a θ 0
  have hsHyp := outerChordS_cosh a θ hzero
  have hsEll := outerChordS_cos a θ 0
  simp only [Real.cosh_zero] at hxHyp hsHyp
  simp only [Real.cos_zero] at hxEll hsEll
  exact ⟨hxHyp.symm.trans hxEll, hsHyp.symm.trans hsEll⟩

/-- The overlap point `z=1` belongs to both unique coordinate charts, and
their chord formulas coincide there.  Thus crossing `z=1` changes only the
coordinate used for the same outer variable. -/
theorem outerChordCharts_join_at_one
    (K : ℕ) (hK : 2 ≤ K) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (θ : ℝ) :
    (∃! η : ℝ, η ∈ Icc (0 : ℝ) (pathLogParameter a) ∧
      (1 : ℝ) = Real.cosh η) ∧
    (∃! φ : ℝ, φ ∈ Ico (0 : ℝ) (Real.pi / K) ∧
      (1 : ℝ) = Real.cos φ) ∧
    halfChordX a θ 0 = ellipticChordX a θ 0 ∧
    halfChordS a θ 0 = ellipticChordS a θ 0 := by
  have hhyper := existsUnique_hyperbolicOuterCoordinate a 1 ha0 ha1
    ⟨le_rfl, Real.one_le_cosh _⟩
  have hKpos : (0 : ℝ) < K := by positivity
  have hanglePos : 0 < Real.pi / (K : ℝ) := by positivity
  have hanglePi : Real.pi / (K : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ hKpos]
    have hKcast : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
    nlinarith [Real.pi_pos]
  have hcos : Real.cos (Real.pi / K) < 1 := by
    simpa only [Real.cos_zero] using
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hanglePi hanglePos
  have helliptic := existsUnique_ellipticOuterCoordinate K hK 1
    ⟨hcos, le_rfl⟩
  exact ⟨hhyper, helliptic, outerChordFormulas_agree_at_one ha0 ha1 θ⟩

end

end ConnectedPseudospectrum
