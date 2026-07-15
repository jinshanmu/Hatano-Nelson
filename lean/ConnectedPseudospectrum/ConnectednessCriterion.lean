import ConnectedPseudospectrum.PathComponents
import ConnectedPseudospectrum.SpectralInterval
import ConnectedPseudospectrum.VerticalTopology

/-!
# Topological connectedness criterion

This module proves the topological implications after isolating the one
remaining analytic input from `lem:vertical`: closure of the strict
pseudospectrum under vertical scaling.  It also proves, unconditionally,
that containment of the compact real spectral interval is equivalent to the
strict inequality `γₙ < ε`.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

/-- Containment of the whole real spectral interval in the strict
pseudospectrum is exactly the strict barrier inequality. -/
theorem spectralInterval_mapsTo_pseudospectrum_iff_gapBarrier_lt
    (n : ℕ) (hn : 1 ≤ n) (a ε : ℝ) :
    MapsTo (fun x : ℝ => (x : ℂ)) (spectralInterval n a)
        (pseudospectrum n a ε) ↔
      gapBarrier n a < ε := by
  constructor
  · intro hinterval
    obtain ⟨x, hx, hxmax⟩ := exists_realGapValue_eq_gapBarrier n a hn
    have hxΩ := hinterval hx
    change realGapValue n a x < ε at hxΩ
    rwa [hxmax] at hxΩ
  · intro hgamma x hx
    change pseudospectralHeight n a x < ε
    exact (realGapValue_le_gapBarrier n a x hx).trans_lt hgamma

/-- Under vertical scaling, connectedness of the strict path
pseudospectrum is equivalent to containing the convex hull of its real
spectrum. -/
theorem isConnected_pseudospectrum_iff_spectralInterval_mapsTo_of_vertical
    (m : ℕ) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hvertical : VerticalScalingClosed (pseudospectrum (m + 1) a ε)) :
    IsConnected (pseudospectrum (m + 1) a ε) ↔
      MapsTo (fun x : ℝ => (x : ℂ)) (spectralInterval (m + 1) a)
        (pseudospectrum (m + 1) a ε) := by
  let Ω := pseudospectrum (m + 1) a ε
  let Isp := spectralInterval (m + 1) a
  constructor
  · intro hconnected
    let R : Set ℝ := Complex.re '' Ω
    have hRpre : IsPreconnected R :=
      hconnected.2.image Complex.re Complex.continuous_re.continuousOn
    have hrightΩ : ((spectralRadius (m + 1) a : ℝ) : ℂ) ∈ Ω := by
      change pseudospectralHeight (m + 1) a (spectralRadius (m + 1) a) < ε
      rw [pseudospectralHeight_spectralRadius m ha]
      exact hε
    have hleftΩ : (((-spectralRadius (m + 1) a : ℝ) : ℂ)) ∈ Ω := by
      change pseudospectralHeight (m + 1) a
        (((-spectralRadius (m + 1) a : ℝ) : ℂ)) < ε
      have hzero : pseudospectralHeight (m + 1) a
          (((-spectralRadius (m + 1) a : ℝ) : ℂ)) = 0 := by
        simpa only [Complex.ofReal_neg] using
          pseudospectralHeight_neg_spectralRadius m ha
      rw [hzero]
      exact hε
    have hrightR : spectralRadius (m + 1) a ∈ R :=
      ⟨(spectralRadius (m + 1) a : ℂ), hrightΩ, by simp⟩
    have hleftR : -spectralRadius (m + 1) a ∈ R :=
      ⟨(((-spectralRadius (m + 1) a : ℝ) : ℂ)), hleftΩ, by simp⟩
    intro x hx
    have hxR : x ∈ R := by
      apply hRpre.Icc_subset hleftR hrightR
      exact hx
    obtain ⟨z, hzΩ, hzre⟩ := hxR
    have hrealΩ : verticalScale 0 z ∈ Ω :=
      hvertical z hzΩ 0 (by simp)
    simpa [verticalScale, hzre] using hrealΩ
  · intro hinterval
    let base : ℂ := (spectralRadius (m + 1) a : ℝ)
    have hbaseI : spectralRadius (m + 1) a ∈ Isp := by
      change spectralRadius (m + 1) a ∈ spectralInterval (m + 1) a
      rw [spectralInterval, mem_Icc]
      exact ⟨neg_le_self (spectralRadius_nonneg (m + 1) a (by omega)), le_rfl⟩
    have hbaseΩ : base ∈ Ω := hinterval hbaseI
    have hsubset : Ω ⊆ connectedComponentIn Ω base := by
      intro z hzΩ
      obtain ⟨k, hkComponent⟩ :=
        exists_pathEigenvalue_mem_pseudospectral_component
          (n := m + 1) (by omega) ha hε hzΩ
      let node : ℂ := (pathEigenvalue (m + 1) a k : ℂ)
      let S : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Isp
      have hSpre : IsPreconnected S :=
        isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn
      have hSΩ : S ⊆ Ω := by
        rintro w ⟨x, hxI, rfl⟩
        exact hinterval hxI
      have hnodeI : pathEigenvalue (m + 1) a k ∈ Isp :=
        pathEigenvalue_mem_spectralInterval m ha k
      have hnodeS : node ∈ S := ⟨pathEigenvalue (m + 1) a k, hnodeI, rfl⟩
      have hbaseS : base ∈ S := ⟨spectralRadius (m + 1) a, hbaseI, rfl⟩
      have hbaseNode : base ∈ connectedComponentIn Ω node :=
        (hSpre.subset_connectedComponentIn hnodeS hSΩ) hbaseS
      have hcomponentNode :
          connectedComponentIn Ω z = connectedComponentIn Ω node :=
        connectedComponentIn_eq hkComponent
      have hbaseZ : base ∈ connectedComponentIn Ω z :=
        hcomponentNode.symm ▸ hbaseNode
      have hcomponentBase :
          connectedComponentIn Ω z = connectedComponentIn Ω base :=
        connectedComponentIn_eq hbaseZ
      exact hcomponentBase ▸ mem_connectedComponentIn hzΩ
    have heq : connectedComponentIn Ω base = Ω :=
      (connectedComponentIn_subset Ω base).antisymm hsubset
    refine ⟨⟨base, hbaseΩ⟩, ?_⟩
    change IsPreconnected Ω
    rw [← heq]
    exact isPreconnected_connectedComponentIn

/-- Conditional exact connectedness criterion with the strict inequality
required by the open pseudospectrum. -/
theorem isConnected_pseudospectrum_iff_gapBarrier_lt_of_vertical
    (m : ℕ) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hvertical : VerticalScalingClosed (pseudospectrum (m + 1) a ε)) :
    IsConnected (pseudospectrum (m + 1) a ε) ↔
      gapBarrier (m + 1) a < ε := by
  exact (isConnected_pseudospectrum_iff_spectralInterval_mapsTo_of_vertical
    m ha hε hvertical).trans
      (spectralInterval_mapsTo_pseudospectrum_iff_gapBarrier_lt
        (m + 1) (by omega) a ε)

/-- Conditional contractibility of every actual pseudospectral component.
This is a genuine `ContractibleSpace` conclusion for the component subtype. -/
theorem contractibleSpace_pseudospectral_component_of_vertical
    (m : ℕ) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hvertical : VerticalScalingClosed (pseudospectrum (m + 1) a ε))
    {z : ℂ} (hz : z ∈ pseudospectrum (m + 1) a ε) :
    ContractibleSpace
      (connectedComponentIn (pseudospectrum (m + 1) a ε) z) := by
  obtain ⟨k, hk⟩ := exists_pathEigenvalue_mem_pseudospectral_component
    (n := m + 1) (by omega) ha hε hz
  apply contractibleSpace_connectedComponentIn_of_real_mem hvertical hk
  simp

end

end ConnectedPseudospectrum
