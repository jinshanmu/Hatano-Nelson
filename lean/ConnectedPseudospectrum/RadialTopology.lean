import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Connected rotation-invariant subsets of the complex plane

This module isolates the topological argument used at a one-sided Jordan
boundary: connectedness and rotational invariance force radial star-convexity,
and hence contractibility.  No matrix-specific assumptions enter the proof.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- A connected subset of the complex plane which contains `d` and is
invariant under every rotation about `d` is star-convex about `d`.

The proof uses connectedness only through the intermediate-value property of
the radius. Once an intermediate radius is attained, rotational invariance
moves that point to the prescribed radial segment. -/
theorem starConvex_of_isConnected_rotationInvariant
    {S : Set ℂ} {d : ℂ} (hS : IsConnected S) (hd : d ∈ S)
    (hrot : ∀ u : ℂ, norm u = 1 → ∀ z : ℂ, z ∈ S →
      d + u * (z - d) ∈ S) :
    StarConvex ℝ d S := by
  rw [starConvex_iff_forall_pos hd]
  intro y hy a b ha hb hab
  by_cases hyd : y = d
  · subst y
    rw [← add_smul, hab, one_smul]
    exact hd
  let q : ℂ := a • d + b • y
  have hb0 : 0 ≤ b := hb.le
  have hb1 : b < 1 := by linarith
  have hdisty : 0 < dist y d := dist_pos.mpr hyd
  have hq_sub : q - d = (b : ℂ) * (y - d) := by
    dsimp [q]
    have habC : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    calc
      (a : ℂ) * d + (b : ℂ) * y - d =
          ((a : ℂ) + (b : ℂ)) * d - d +
            (b : ℂ) * (y - d) := by ring
      _ = (b : ℂ) * (y - d) := by rw [habC]; ring
  have hdistq : dist q d = b * dist y d := by
    rw [dist_eq_norm, hq_sub, Complex.norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hb0, ← dist_eq_norm]
  have htarget : b * dist y d ∈ Set.Icc (dist d d) (dist y d) := by
    constructor
    · simpa using mul_nonneg hb0 (dist_nonneg : 0 ≤ dist y d)
    · have hdist_nonneg : 0 ≤ dist y d := dist_nonneg
      nlinarith
  obtain ⟨x, hxS, hxdist⟩ :=
    hS.isPreconnected.intermediate_value hd hy
      (continuous_id.dist continuous_const).continuousOn htarget
  change dist x d = b * dist y d at hxdist
  have hxdist_pos : 0 < dist x d := by
    rw [hxdist]
    exact mul_pos hb hdisty
  have hxd : x ≠ d := dist_pos.mp hxdist_pos
  let u : ℂ := (q - d) / (x - d)
  have hu_norm : norm u = 1 := by
    dsimp [u]
    rw [Complex.norm_div, ← dist_eq_norm, ← dist_eq_norm, hdistq, hxdist]
    field_simp [hb.ne', hdisty.ne']
  have hu := hrot u hu_norm x hxS
  have huq : d + u * (x - d) = q := by
    dsimp [u]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hxd)]
    ring
  rw [huq] at hu
  exact hu

/-- The preceding radial argument gives contractibility without requiring an
explicit formula for the radius of the set. -/
theorem contractibleSpace_of_isConnected_rotationInvariant
    {S : Set ℂ} {d : ℂ} (hS : IsConnected S) (hd : d ∈ S)
    (hrot : ∀ u : ℂ, norm u = 1 → ∀ z : ℂ, z ∈ S →
      d + u * (z - d) ∈ S) :
    ContractibleSpace S :=
  (starConvex_of_isConnected_rotationInvariant hS hd hrot).contractibleSpace
    ⟨d, hd⟩

/-- A nonempty bounded open connected subset of the complex plane which is
invariant under every rotation about `d` is an open disk centered at `d`.

This is the set-theoretic radial classification used for the one-sided
Jordan boundary.  The radius is the supremum of the attained distances from
the center.  Openness excludes the outer circle, while connectedness fills
every smaller radius. -/
theorem exists_eq_ball_of_isOpen_isConnected_rotationInvariant
    {S : Set ℂ} {d : ℂ} (hopen : IsOpen S) (hS : IsConnected S) (hd : d ∈ S)
    (hbounded : Bornology.IsBounded S)
    (hrot : ∀ u : ℂ, norm u = 1 → ∀ z : ℂ, z ∈ S →
      d + u * (z - d) ∈ S) :
    ∃ R : ℝ, 0 < R ∧ S = Metric.ball d R := by
  let radii : Set ℝ := (fun z : ℂ => dist z d) '' S
  obtain ⟨K, hK⟩ := hbounded.subset_closedBall d
  have hradii_nonempty : radii.Nonempty := ⟨dist d d, d, hd, rfl⟩
  have hradii_bdd : BddAbove radii := by
    refine ⟨K, ?_⟩
    rintro r ⟨z, hz, rfl⟩
    exact (Metric.mem_closedBall.mp (hK hz))
  let R : ℝ := sSup radii
  have hRpos : 0 < R := by
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen d hd
    let w : ℂ := d + (δ / 2 : ℝ)
    have hwdist : dist w d = δ / 2 := by
      have hδ0 : 0 ≤ δ := hδ.le
      dsimp [w]
      rw [dist_eq_norm]
      push_cast
      rw [add_sub_cancel_left]
      rw [Complex.norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hδ0]
      norm_num
    have hw : w ∈ S := by
      apply hball
      rw [Metric.mem_ball, hwdist]
      linarith
    have hwle : dist w d ≤ R :=
      le_csSup hradii_bdd ⟨w, hw, rfl⟩
    linarith
  refine ⟨R, hRpos, Set.ext ?_⟩
  intro z
  constructor
  · intro hz
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen z hz
    let u : ℂ := if z = d then 1 else (z - d) / (dist z d : ℂ)
    have hu : norm u = 1 := by
      dsimp [u]
      split_ifs with hzd
      · simp
      · rw [Complex.norm_div, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (dist_pos.mpr hzd), dist_eq_norm, div_self]
        exact (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzd))
    have hzrepr : z = d + (dist z d : ℂ) * u := by
      dsimp [u]
      split_ifs with hzd
      · subst z
        simp
      · rw [mul_div_cancel₀]
        · ring
        · exact_mod_cast (dist_ne_zero.mpr hzd)
    let w : ℂ := z + (δ / 2 : ℝ) * u
    have hwz : dist w z = δ / 2 := by
      have hδ0 : 0 ≤ δ := hδ.le
      dsimp [w]
      rw [dist_eq_norm]
      push_cast
      rw [add_sub_cancel_left, Complex.norm_mul, hu, mul_one]
      rw [Complex.norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hδ0]
      norm_num
    have hw : w ∈ S := by
      apply hball
      rw [Metric.mem_ball, hwz]
      linarith
    have hwd : dist w d = dist z d + δ / 2 := by
      have hwsub : w - d = ((dist z d + δ / 2 : ℝ) : ℂ) * u := by
        calc
          w - d = z + (δ / 2 : ℝ) * u - d := rfl
          _ = (d + (dist z d : ℂ) * u) + (δ / 2 : ℝ) * u - d := by
            exact congrArg (fun q : ℂ => q + (δ / 2 : ℝ) * u - d) hzrepr
          _ = ((dist z d + δ / 2 : ℝ) : ℂ) * u := by
            push_cast
            ring
      calc
        dist w d = ‖w - d‖ := dist_eq_norm _ _
        _ = ‖((dist z d + δ / 2 : ℝ) : ℂ) * u‖ := by rw [hwsub]
        _ = dist z d + δ / 2 := by
          rw [Complex.norm_mul, hu, mul_one]
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity : 0 < dist z d + δ / 2)]
    have hwle : dist w d ≤ R :=
      le_csSup hradii_bdd ⟨w, hw, rfl⟩
    rw [Metric.mem_ball]
    linarith
  · intro hz
    rw [Metric.mem_ball] at hz
    by_cases hzd : z = d
    · simpa [hzd] using hd
    have hzdpos : 0 < dist z d := dist_pos.mpr hzd
    obtain ⟨r, hr, hzr⟩ :=
      (lt_csSup_iff hradii_bdd hradii_nonempty).mp hz
    obtain ⟨w, hw, rfl⟩ := hr
    have htarget : dist z d ∈ Set.Icc (dist d d) (dist w d) := by
      constructor
      · rw [dist_self]
        exact hzdpos.le
      · exact hzr.le
    obtain ⟨x, hx, hxdist⟩ :=
      hS.isPreconnected.intermediate_value hd hw
        (continuous_id.dist continuous_const).continuousOn htarget
    have hxd : x ≠ d := by
      intro h
      subst x
      simp at hxdist
      exact hzd hxdist
    let u : ℂ := (z - d) / (x - d)
    have hu : norm u = 1 := by
      dsimp [u]
      change dist x d = dist z d at hxdist
      rw [Complex.norm_div, ← dist_eq_norm, ← dist_eq_norm, hxdist,
        div_self]
      exact (dist_ne_zero.mpr hzd)
    have hzrot : d + u * (x - d) = z := by
      dsimp [u]
      rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hxd)]
      ring
    simpa [hzrot] using hrot u hu x hx

end

end ConnectedPseudospectrum
