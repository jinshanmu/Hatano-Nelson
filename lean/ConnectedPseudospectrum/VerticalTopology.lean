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

/-! ## Abstract real-axis criterion -/

/-- A vertically scaling-closed subset of the plane is connected exactly
when it contains the real interval joining two distinguished real points,
provided every component contains a real anchor in that interval.

This is the matrix-independent topological implication used by the
pseudospectral connectedness criterion.  All spectral information is isolated
in the endpoint and component-anchor hypotheses. -/
theorem isConnected_iff_realInterval_mapsTo_of_verticalScaling
    {Ω : Set ℂ} (hΩ : VerticalScalingClosed Ω)
    {l r : ℝ} (hlr : l ≤ r)
    (hl : (l : ℂ) ∈ Ω) (hr : (r : ℂ) ∈ Ω)
    (hanchor : ∀ {z : ℂ}, z ∈ Ω →
      ∃ x ∈ Icc l r, (x : ℂ) ∈ connectedComponentIn Ω z) :
    IsConnected Ω ↔ MapsTo (fun x : ℝ => (x : ℂ)) (Icc l r) Ω := by
  constructor
  · intro hconnected
    let R : Set ℝ := Complex.re '' Ω
    have hRpre : IsPreconnected R :=
      hconnected.2.image Complex.re Complex.continuous_re.continuousOn
    have hlR : l ∈ R := ⟨(l : ℂ), hl, by simp⟩
    have hrR : r ∈ R := ⟨(r : ℂ), hr, by simp⟩
    intro x hx
    have hxR : x ∈ R := hRpre.Icc_subset hlR hrR hx
    obtain ⟨z, hzΩ, hzre⟩ := hxR
    have hrealΩ : verticalScale 0 z ∈ Ω := hΩ z hzΩ 0 (by simp)
    simpa [verticalScale, hzre] using hrealΩ
  · intro hinterval
    let base : ℂ := (r : ℂ)
    have hbaseI : r ∈ Icc l r := ⟨hlr, le_rfl⟩
    have hbaseΩ : base ∈ Ω := hinterval hbaseI
    have hsubset : Ω ⊆ connectedComponentIn Ω base := by
      intro z hzΩ
      obtain ⟨x, hxI, hxComponent⟩ := hanchor hzΩ
      let node : ℂ := (x : ℂ)
      let S : Set ℂ := (fun y : ℝ => (y : ℂ)) '' Icc l r
      have hSpre : IsPreconnected S :=
        isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn
      have hSΩ : S ⊆ Ω := by
        rintro w ⟨y, hyI, rfl⟩
        exact hinterval hyI
      have hnodeS : node ∈ S := ⟨x, hxI, rfl⟩
      have hbaseS : base ∈ S := ⟨r, hbaseI, rfl⟩
      have hbaseNode : base ∈ connectedComponentIn Ω node :=
        (hSpre.subset_connectedComponentIn hnodeS hSΩ) hbaseS
      have hcomponentNode :
          connectedComponentIn Ω z = connectedComponentIn Ω node :=
        connectedComponentIn_eq hxComponent
      have hbaseZ : base ∈ connectedComponentIn Ω z :=
        hcomponentNode.symm ▸ hbaseNode
      have hcomponentBase :
          connectedComponentIn Ω z = connectedComponentIn Ω base :=
        connectedComponentIn_eq hbaseZ
      exact hcomponentBase ▸ mem_connectedComponentIn hzΩ
    have heq : connectedComponentIn Ω base = Ω :=
      (connectedComponentIn_subset Ω base).antisymm hsubset
    refine ⟨⟨base, hbaseΩ⟩, ?_⟩
    rw [← heq]
    exact isPreconnected_connectedComponentIn

/-- Matrix-independent packaging of the second topological consequence:
vertical scaling plus a real anchor in each component makes every component
contractible. -/
theorem contractibleSpace_connectedComponentIn_of_verticalScaling
    {Ω : Set ℂ} (hΩ : VerticalScalingClosed Ω)
    (hanchor : ∀ {z : ℂ}, z ∈ Ω →
      ∃ b ∈ connectedComponentIn Ω z, b.im = 0)
    {z : ℂ} (hz : z ∈ Ω) :
    ContractibleSpace (connectedComponentIn Ω z) := by
  obtain ⟨b, hb, hbReal⟩ := hanchor hz
  exact contractibleSpace_connectedComponentIn_of_real_mem hΩ hb hbReal

end

end ConnectedPseudospectrum
