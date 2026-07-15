import ConnectedPseudospectrum.ComponentTopology
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Order.IntermediateValue

/-!
# Component topology under vertical scaling

This module isolates the topological part of the argument following
`lem:vertical`.  The analytic input is expressed only as closure under
vertical scaling; the eventual path-matrix theorem will discharge that input
using the proved least-singular-value monotonicity.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- Scale the imaginary part of a complex number while fixing its real
part. -/
def verticalScale (s : ℝ) (z : ℂ) : ℂ :=
  (z.re : ℂ) + (s * z.im : ℝ) * Complex.I

@[simp] theorem verticalScale_zero (z : ℂ) :
    verticalScale 0 z = (z.re : ℂ) := by
  simp [verticalScale]

@[simp] theorem verticalScale_one (z : ℂ) :
    verticalScale 1 z = z := by
  apply Complex.ext <;> simp [verticalScale]

@[simp] theorem verticalScale_re (s : ℝ) (z : ℂ) :
    (verticalScale s z).re = z.re := by
  simp [verticalScale]

@[simp] theorem verticalScale_im (s : ℝ) (z : ℂ) :
    (verticalScale s z).im = s * z.im := by
  simp [verticalScale]

theorem continuous_verticalScale :
    Continuous (fun p : ℝ × ℂ => verticalScale p.1 p.2) := by
  unfold verticalScale
  fun_prop

theorem continuous_verticalScale_left (z : ℂ) :
    Continuous (fun s : ℝ => verticalScale s z) := by
  unfold verticalScale
  fun_prop

/-- A set is closed under contractions of every vertical fibre toward the
real axis. -/
def VerticalScalingClosed (Ω : Set ℂ) : Prop :=
  ∀ z ∈ Ω, ∀ s ∈ Icc (0 : ℝ) 1, verticalScale s z ∈ Ω

/-- Vertical scaling cannot leave the connected component in which it
starts. -/
theorem verticalScale_mem_connectedComponentIn
    {Ω : Set ℂ} (hΩ : VerticalScalingClosed Ω)
    {z₀ z : ℂ} (hz : z ∈ connectedComponentIn Ω z₀)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    verticalScale s z ∈ connectedComponentIn Ω z₀ := by
  let P : Set ℂ := (fun u : ℝ => verticalScale u z) '' Icc (0 : ℝ) 1
  have hPpre : IsPreconnected P :=
    isPreconnected_Icc.image _ (continuous_verticalScale_left z).continuousOn
  have hzΩ : z ∈ Ω := connectedComponentIn_subset Ω z₀ hz
  have hzP : z ∈ P := by
    refine ⟨1, by simp, ?_⟩
    simp
  have hPΩ : P ⊆ Ω := by
    rintro w ⟨u, hu, rfl⟩
    exact hΩ z hzΩ u hu
  have hPcomponent : P ⊆ connectedComponentIn Ω z :=
    hPpre.subset_connectedComponentIn hzP hPΩ
  have hsP : verticalScale s z ∈ P := ⟨s, hs, rfl⟩
  have htarget : verticalScale s z ∈ connectedComponentIn Ω z :=
    hPcomponent hsP
  have heq : connectedComponentIn Ω z₀ = connectedComponentIn Ω z :=
    connectedComponentIn_eq hz
  exact heq.symm ▸ htarget

/-- The real affine segment between the real parts of any two points in a
component remains in that component, after identifying real numbers with
complex numbers. -/
theorem realSegment_mem_connectedComponentIn
    {Ω : Set ℂ} (hΩ : VerticalScalingClosed Ω)
    {z₀ z b : ℂ}
    (hz : z ∈ connectedComponentIn Ω z₀)
    (hb : b ∈ connectedComponentIn Ω z₀)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (((1 - s) * z.re + s * b.re : ℝ) : ℂ) ∈
      connectedComponentIn Ω z₀ := by
  let C : Set ℂ := connectedComponentIn Ω z₀
  let R : Set ℝ := Complex.re '' C
  have hRpre : IsPreconnected R :=
    isPreconnected_connectedComponentIn.image Complex.re
      Complex.continuous_re.continuousOn
  have hzR : z.re ∈ R := ⟨z, hz, rfl⟩
  have hbR : b.re ∈ R := ⟨b, hb, rfl⟩
  let x : ℝ := (1 - s) * z.re + s * b.re
  have hxR : x ∈ R := by
    by_cases hzb : z.re ≤ b.re
    · apply hRpre.Icc_subset hzR hbR
      dsimp only [x]
      constructor <;> nlinarith [hs.1, hs.2]
    · have hbz : b.re ≤ z.re := le_of_not_ge hzb
      apply hRpre.Icc_subset hbR hzR
      dsimp only [x]
      constructor <;> nlinarith [hs.1, hs.2]
  obtain ⟨w, hwC, hwre⟩ := hxR
  have hreal : verticalScale 0 w ∈ C :=
    verticalScale_mem_connectedComponentIn hΩ hwC (s := 0) (by simp)
  change (x : ℂ) ∈ C
  simpa [verticalScale, hwre] using hreal

/-- A component of a vertically scaling-closed set is genuinely
contractible as soon as it contains a real point.  The contraction first
scales each vertical fibre to the real axis and then contracts the resulting
real interval to the selected real point. -/
theorem contractibleSpace_connectedComponentIn_of_real_mem
    {Ω : Set ℂ} (hΩ : VerticalScalingClosed Ω)
    {z₀ b : ℂ} (hb : b ∈ connectedComponentIn Ω z₀)
    (hbReal : b.im = 0) :
    ContractibleSpace (connectedComponentIn Ω z₀) := by
  let C : Set ℂ := connectedComponentIn Ω z₀
  let bC : C := ⟨b, hb⟩
  let realProjectionMap : C(C, C) :=
    ⟨fun z =>
      ⟨verticalScale 0 z.1,
        verticalScale_mem_connectedComponentIn hΩ z.2 (s := 0) (by simp)⟩,
      by
        apply Continuous.subtype_mk
        unfold verticalScale
        fun_prop⟩
  let verticalHomotopy :
      ContinuousMap.Homotopy (ContinuousMap.id C) realProjectionMap :=
    { toFun := fun p =>
        ⟨verticalScale (1 - (p.1 : ℝ)) p.2.1,
          verticalScale_mem_connectedComponentIn hΩ p.2.2
            (s := 1 - (p.1 : ℝ)) (by
              constructor <;> linarith [p.1.2.1, p.1.2.2])⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        unfold verticalScale
        fun_prop
      map_zero_left := by
        intro z
        apply Subtype.ext
        simp
      map_one_left := by
        intro z
        apply Subtype.ext
        simp [realProjectionMap] }
  let realHomotopy : ContinuousMap.Homotopy realProjectionMap
      (ContinuousMap.const C bC) :=
    { toFun := fun p =>
        ⟨((((1 - (p.1 : ℝ)) * p.2.1.re +
              (p.1 : ℝ) * b.re : ℝ) : ℂ)),
          realSegment_mem_connectedComponentIn hΩ p.2.2 hb p.1.2⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        fun_prop
      map_zero_left := by
        intro z
        apply Subtype.ext
        simp [realProjectionMap, verticalScale]
      map_one_left := by
        intro z
        apply Subtype.ext
        apply Complex.ext <;> simp [hbReal, bC] }
  apply (contractible_iff_id_nullhomotopic C).2
  exact ⟨bC, ⟨verticalHomotopy.trans realHomotopy⟩⟩

end

end ConnectedPseudospectrum
