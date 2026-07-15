import ConnectedPseudospectrum.PseudospectralComponents
import ConnectedPseudospectrum.Spectrum

/-!
# Spectral nodes in components of the path pseudospectrum

This specializes the matrix-generic maximum-principle theorem to the
Hatano--Nelson path and then uses the explicit simple real spectrum.  Thus
every component contains one of the displayed Dirichlet cosine nodes.
-/

namespace ConnectedPseudospectrum

open Matrix Set

noncomputable section

@[simp] theorem generalShift_complexPathMatrix (n : ℕ) (a : ℝ) (z : ℂ) :
    generalShift (complexPathMatrix n a) z = shiftedPathMatrix n a z :=
  rfl

@[simp] theorem generalPseudospectralHeight_complexPathMatrix
    (n : ℕ) (a : ℝ) (z : ℂ) :
    generalPseudospectralHeight (complexPathMatrix n a) z =
      pseudospectralHeight n a z :=
  rfl

@[simp] theorem generalPseudospectrum_complexPathMatrix
    (n : ℕ) (a ε : ℝ) :
    generalPseudospectrum (complexPathMatrix n a) ε =
      pseudospectrum n a ε :=
  rfl

/-- Every component of the positive strict path pseudospectrum contains an
explicit real spectral node. -/
theorem exists_pathEigenvalue_mem_pseudospectral_component
    {n : ℕ} (hn : 0 < n) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    {z : ℂ} (hz : z ∈ pseudospectrum n a ε) :
    ∃ k : Fin n,
      (pathEigenvalue n a k : ℂ) ∈
        connectedComponentIn (pseudospectrum n a ε) z := by
  have hzGeneral :
      z ∈ generalPseudospectrum (complexPathMatrix n a) ε := by
    simpa using hz
  obtain ⟨w, hwComponent, hwdet⟩ :=
    exists_det_generalShift_eq_zero_mem_component
      (complexPathMatrix n a) hn hε hzGeneral
  have hwdet' : (shiftedPathMatrix n a w).det = 0 := by
    simpa using hwdet
  obtain ⟨k, rfl⟩ := (det_shiftedPathMatrix_eq_zero_iff n ha w).1 hwdet'
  refine ⟨k, ?_⟩
  simpa using hwComponent

end

end ConnectedPseudospectrum
