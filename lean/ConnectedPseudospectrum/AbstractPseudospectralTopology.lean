import ConnectedPseudospectrum.PseudospectralComponents
import ConnectedPseudospectrum.VerticalTopology

/-!
# Matrix-level vertical topology theorem

This module joins the matrix-independent vertical-scaling topology with the
maximum-principle theorem that every finite-dimensional pseudospectral
component contains an eigenvalue.  The endpoints of the real spectrum are
kept explicit; this avoids imposing a particular finite-spectrum minimum and
maximum representation on Mathlib's abstract algebra spectrum.
-/

namespace ConnectedPseudospectrum

open Matrix Set

noncomputable section

/-- The maximum least-singular-value height on a prescribed real interval.
This is the abstract barrier `Gamma(B)` of the ELA manuscript when the
interval is the convex hull of the real spectrum. -/
def generalRealIntervalBarrier {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (l r : ℝ) : ℝ :=
  sSup ((fun x : ℝ => generalPseudospectralHeight M (x : ℂ)) '' Icc l r)

theorem compact_generalRealIntervalHeightRange {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (l r : ℝ) :
    IsCompact
      ((fun x : ℝ => generalPseudospectralHeight M (x : ℂ)) '' Icc l r) := by
  exact isCompact_Icc.image
    ((continuous_generalPseudospectralHeight M).comp
      Complex.continuous_ofReal)

theorem nonempty_generalRealIntervalHeightRange {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) {l r : ℝ} (hlr : l ≤ r) :
    ((fun x : ℝ => generalPseudospectralHeight M (x : ℂ)) ''
      Icc l r).Nonempty :=
  ⟨generalPseudospectralHeight M (l : ℂ), l, ⟨le_rfl, hlr⟩, rfl⟩

/-- The abstract real-interval barrier is attained. -/
theorem exists_generalPseudospectralHeight_eq_generalRealIntervalBarrier
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    {l r : ℝ} (hlr : l ≤ r) :
    ∃ x ∈ Icc l r,
      generalPseudospectralHeight M (x : ℂ) =
        generalRealIntervalBarrier M l r := by
  have hcompact := compact_generalRealIntervalHeightRange M l r
  have hnonempty := nonempty_generalRealIntervalHeightRange M hlr
  have hmem : generalRealIntervalBarrier M l r ∈
      (fun x : ℝ => generalPseudospectralHeight M (x : ℂ)) '' Icc l r := by
    exact hcompact.isClosed.csSup_mem hnonempty hcompact.isBounded.bddAbove
  exact hmem

theorem generalPseudospectralHeight_le_generalRealIntervalBarrier
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    {l r x : ℝ} (hx : x ∈ Icc l r) :
    generalPseudospectralHeight M (x : ℂ) ≤
      generalRealIntervalBarrier M l r := by
  apply le_csSup (compact_generalRealIntervalHeightRange M l r).isBounded.bddAbove
  exact ⟨x, hx, rfl⟩

/-- Containing the prescribed real interval in a strict pseudospectrum is
equivalent to the strict barrier inequality. -/
theorem realInterval_mapsTo_generalPseudospectrum_iff_barrier_lt
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    {l r ε : ℝ} (hlr : l ≤ r) :
    MapsTo (fun x : ℝ => (x : ℂ)) (Icc l r)
        (generalPseudospectrum M ε) ↔
      generalRealIntervalBarrier M l r < ε := by
  constructor
  · intro hinterval
    obtain ⟨x, hx, hxmax⟩ :=
      exists_generalPseudospectralHeight_eq_generalRealIntervalBarrier M hlr
    have hxΩ := hinterval hx
    change generalPseudospectralHeight M (x : ℂ) < ε at hxΩ
    rwa [hxmax] at hxΩ
  · intro hbarrier x hx
    change generalPseudospectralHeight M (x : ℂ) < ε
    exact (generalPseudospectralHeight_le_generalRealIntervalBarrier M hx).trans_lt
      hbarrier

/-- Matrix-level form of the ELA manuscript's vertical topology theorem.

The hypothesis `hspectrum` says that the spectrum lies on the displayed real
interval, while `hl` and `hr` say that both endpoints are spectral.  Under
vertical contraction, every pseudospectral component is contractible and
connectedness is equivalent to containment of the full real spectral
interval. -/
theorem generalPseudospectrum_vertical_topology
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε)
    (hvertical : VerticalScalingClosed (generalPseudospectrum M ε))
    {l r : ℝ} (hlr : l ≤ r)
    (hspectrum : ∀ {w : ℂ}, w ∈ spectrum ℂ M →
      ∃ x ∈ Icc l r, w = (x : ℂ))
    (hl : (l : ℂ) ∈ spectrum ℂ M)
    (hr : (r : ℂ) ∈ spectrum ℂ M) :
    (∀ {z : ℂ}, z ∈ generalPseudospectrum M ε →
      ContractibleSpace
        (connectedComponentIn (generalPseudospectrum M ε) z)) ∧
    (IsConnected (generalPseudospectrum M ε) ↔
      MapsTo (fun x : ℝ => (x : ℂ)) (Icc l r)
        (generalPseudospectrum M ε)) := by
  have hanchor : ∀ {z : ℂ}, z ∈ generalPseudospectrum M ε →
      ∃ x ∈ Icc l r,
        (x : ℂ) ∈ connectedComponentIn (generalPseudospectrum M ε) z := by
    intro z hz
    obtain ⟨w, hwComponent, hwSpectrum⟩ :=
      exists_mem_spectrum_mem_pseudospectral_component M hn hε hz
    obtain ⟨x, hx, rfl⟩ := hspectrum hwSpectrum
    exact ⟨x, hx, hwComponent⟩
  have hlΩ : (l : ℂ) ∈ generalPseudospectrum M ε :=
    mem_generalPseudospectrum_of_mem_spectrum M hn hε hl
  have hrΩ : (r : ℂ) ∈ generalPseudospectrum M ε :=
    mem_generalPseudospectrum_of_mem_spectrum M hn hε hr
  constructor
  · intro z hz
    apply contractibleSpace_connectedComponentIn_of_verticalScaling
      hvertical _ hz
    intro w hw
    obtain ⟨x, hx, hxComponent⟩ := hanchor hw
    exact ⟨(x : ℂ), hxComponent, by simp⟩
  · exact isConnected_iff_realInterval_mapsTo_of_verticalScaling
      hvertical hlr hlΩ hrΩ hanchor

/-- The complete matrix-level theorem including the attained abstract barrier
and the strict inequality appropriate to an open pseudospectrum. -/
theorem generalPseudospectrum_vertical_topology_with_barrier
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hn : 0 < n)
    {ε : ℝ} (hε : 0 < ε)
    (hvertical : VerticalScalingClosed (generalPseudospectrum M ε))
    {l r : ℝ} (hlr : l ≤ r)
    (hspectrum : ∀ {w : ℂ}, w ∈ spectrum ℂ M →
      ∃ x ∈ Icc l r, w = (x : ℂ))
    (hl : (l : ℂ) ∈ spectrum ℂ M)
    (hr : (r : ℂ) ∈ spectrum ℂ M) :
    (∀ {z : ℂ}, z ∈ generalPseudospectrum M ε →
      ContractibleSpace
        (connectedComponentIn (generalPseudospectrum M ε) z)) ∧
    (IsConnected (generalPseudospectrum M ε) ↔
      MapsTo (fun x : ℝ => (x : ℂ)) (Icc l r)
        (generalPseudospectrum M ε)) ∧
    (IsConnected (generalPseudospectrum M ε) ↔
      generalRealIntervalBarrier M l r < ε) := by
  obtain ⟨hcontractible, hconnected⟩ :=
    generalPseudospectrum_vertical_topology M hn hε hvertical hlr
      hspectrum hl hr
  exact ⟨hcontractible, hconnected,
    hconnected.trans
      (realInterval_mapsTo_generalPseudospectrum_iff_barrier_lt M hlr)⟩

end

end ConnectedPseudospectrum
