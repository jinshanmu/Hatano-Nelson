import ConnectedPseudospectrum.FinitePath
import ConnectedPseudospectrum.LeastSingular

/-!
# Pseudospectral definitions and attained real barrier

This module records the definitions in `eq:main-definitions`,
`eq:main-U-def`, and `eq:main-L-def`.  The pseudospectrum uses the actual
Euclidean least singular value from `ConnectedPseudospectrum.LeastSingular`.
-/

namespace ConnectedPseudospectrum

open Matrix Set

noncomputable section

/-- The paper's parameter `r = √a`. -/
def pathRate (a : ℝ) : ℝ :=
  Real.sqrt a

/-- The real path matrix, regarded as a complex matrix. -/
def complexPathMatrix (n : ℕ) (a : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (pathMatrix n a i j : ℂ)

@[simp] theorem complexPathMatrix_apply (n : ℕ) (a : ℝ) (i j : Fin n) :
    complexPathMatrix n a i j = (pathMatrix n a i j : ℂ) :=
  rfl

/-- The shifted matrix `zIₙ - Aₙ(a)`. -/
def shiftedPathMatrix (n : ℕ) (a : ℝ) (z : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  z • 1 - complexPathMatrix n a

/-- Least singular value of the shifted path matrix. -/
def pseudospectralHeight (n : ℕ) (a : ℝ) (z : ℂ) : ℝ :=
  leastSingularValue (shiftedPathMatrix n a z)

/-- The strict open Euclidean `ε`-pseudospectrum from the paper. -/
def pseudospectrum (n : ℕ) (a ε : ℝ) : Set ℂ :=
  {z | pseudospectralHeight n a z < ε}

/-- The real-axis least-singular-value function `gₙ`. -/
def realGapValue (n : ℕ) (a x : ℝ) : ℝ :=
  pseudospectralHeight n a x

/-- Half the length of the real spectral interval. -/
def spectralRadius (n : ℕ) (a : ℝ) : ℝ :=
  2 * pathRate a * Real.cos (Real.pi / (n + 1 : ℝ))

/-- The real spectral interval `Iₙˢᵖ`. -/
def spectralInterval (n : ℕ) (a : ℝ) : Set ℝ :=
  Icc (-spectralRadius n a) (spectralRadius n a)

/-- The real-gap barrier `γₙ`, defined as the supremum of the compact image.
For the paper's dimensions this supremum is attained; see
`exists_realGapValue_eq_gapBarrier`. -/
def gapBarrier (n : ℕ) (a : ℝ) : ℝ :=
  sSup (realGapValue n a '' spectralInterval n a)

/-- The explicit upper barrier `𝒰ₙ(a)`. -/
def upperBarrier (n : ℕ) (a : ℝ) : ℝ :=
  pathRate a ^ n *
    (Real.sin (Real.pi / (n + 1 : ℝ)))⁻¹

/-- The explicit lower barrier `𝓛ₙ(a)`. -/
def lowerBarrier (n : ℕ) (a : ℝ) : ℝ :=
  let r := pathRate a
  (1 + r ^ 2 - 2 * r * Real.cos (Real.pi / (n + 1 : ℝ))) *
    (r ^ n * (1 - r ^ 2)) /
      ((1 - r ^ (2 * (n + 1))) *
        Real.sin (3 * Real.pi / (2 * (n + 1 : ℝ))))

theorem continuous_shiftedPathMatrix (n : ℕ) (a : ℝ) :
    Continuous (shiftedPathMatrix n a) := by
  unfold shiftedPathMatrix
  exact (continuous_id.smul continuous_const).sub continuous_const

theorem continuous_pseudospectralHeight (n : ℕ) (a : ℝ) :
    Continuous (pseudospectralHeight n a) :=
  (continuous_leastSingularValue n).comp (continuous_shiftedPathMatrix n a)

theorem isOpen_pseudospectrum (n : ℕ) (a ε : ℝ) :
    IsOpen (pseudospectrum n a ε) := by
  exact isOpen_lt (continuous_pseudospectralHeight n a) continuous_const

theorem continuous_realGapValue (n : ℕ) (a : ℝ) :
    Continuous (realGapValue n a) := by
  unfold realGapValue
  exact (continuous_pseudospectralHeight n a).comp Complex.continuous_ofReal

theorem spectralRadius_nonneg (n : ℕ) (a : ℝ) (hn : 1 ≤ n) :
    0 ≤ spectralRadius n a := by
  have hncast : (2 : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ hn
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hangle_nonneg :
      0 ≤ Real.pi / (n + 1 : ℝ) :=
    div_nonneg Real.pi_pos.le hden.le
  have hangle_le :
      Real.pi / (n + 1 : ℝ) ≤ Real.pi / 2 := by
    exact (div_le_div_iff_of_pos_left Real.pi_pos hden (by norm_num)).2 hncast
  have hcos : 0 ≤ Real.cos (Real.pi / (n + 1 : ℝ)) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, hangle_le⟩
  unfold spectralRadius pathRate
  positivity

theorem zero_mem_spectralInterval (n : ℕ) (a : ℝ) (hn : 1 ≤ n) :
    0 ∈ spectralInterval n a := by
  rw [spectralInterval, mem_Icc]
  have hr := spectralRadius_nonneg n a hn
  exact ⟨neg_nonpos.mpr hr, hr⟩

theorem compact_realGapRange (n : ℕ) (a : ℝ) :
    IsCompact (realGapValue n a '' spectralInterval n a) :=
  isCompact_Icc.image (continuous_realGapValue n a)

theorem nonempty_realGapRange (n : ℕ) (a : ℝ) (hn : 1 ≤ n) :
    (realGapValue n a '' spectralInterval n a).Nonempty :=
  ⟨realGapValue n a 0, 0, zero_mem_spectralInterval n a hn, rfl⟩

/-- The compact real barrier is attained. -/
theorem exists_realGapValue_eq_gapBarrier (n : ℕ) (a : ℝ) (hn : 1 ≤ n) :
    ∃ x ∈ spectralInterval n a, realGapValue n a x = gapBarrier n a := by
  have hcompact := compact_realGapRange n a
  have hnonempty := nonempty_realGapRange n a hn
  have hmem :
      gapBarrier n a ∈ realGapValue n a '' spectralInterval n a := by
    exact hcompact.isClosed.csSup_mem hnonempty hcompact.isBounded.bddAbove
  exact hmem

/-- Every value on the real spectral interval is bounded by `γₙ`. -/
theorem realGapValue_le_gapBarrier (n : ℕ) (a x : ℝ)
    (hx : x ∈ spectralInterval n a) :
    realGapValue n a x ≤ gapBarrier n a := by
  apply le_csSup (compact_realGapRange n a).isBounded.bddAbove
  exact ⟨x, hx, rfl⟩

theorem gapBarrier_nonneg (n : ℕ) (a : ℝ) (hn : 1 ≤ n) :
    0 ≤ gapBarrier n a := by
  exact (leastSingularValue_nonneg (shiftedPathMatrix n a 0)).trans
    (realGapValue_le_gapBarrier n a 0 (zero_mem_spectralInterval n a hn))

end

end ConnectedPseudospectrum
