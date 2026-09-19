import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Algebra of the folded signed-pencil transfer

This module records the five-minor update and its signed iteration.
The subsequent folded-minor module identifies these algebraic states with the
actual minors of the paired signed-pencil matrix.
-/

namespace ConnectedPseudospectrum

open Matrix

noncomputable section

/-- The scalar `C₀=x²+(1-a)²-s²` in the folded recurrence. -/
def foldC0 (a x s : ℝ) : ℝ :=
  x ^ 2 + (1 - a) ^ 2 - s ^ 2

/-- The middle coefficient in the folded fourth-order recurrence. -/
def foldB (a x s : ℝ) : ℝ :=
  (1 + a ^ 2) * x ^ 2 + 2 * a * s ^ 2 + 2 * a ^ 2 - 2 * a - 2 * a ^ 3

/-- The five exposed minors `(d,p,q,c,r)`. -/
structure FoldMinorState where
  /-- The leading determinant coordinate of the exposed-minor state. -/
  d : ℝ
  /-- The first endpoint-deleted minor coordinate. -/
  p : ℝ
  /-- The second endpoint-deleted minor coordinate. -/
  q : ℝ
  /-- The cross-deleted minor coordinate. -/
  c : ℝ
  /-- The preceding leading determinant coordinate. -/
  r : ℝ

/-- The exact update `eq:five-minor-update`. -/
def foldMinorStep (a x s : ℝ) (v : FoldMinorState) : FoldMinorState where
  d := (s ^ 2 - x ^ 2) * v.d + s * (a ^ 2 * v.p + v.q) -
    2 * a * x * v.c + a ^ 2 * v.r
  p := -s * v.d - a ^ 2 * v.p
  q := -s * v.d - v.q
  c := x * v.d + a * v.c
  r := v.d

/-- The terminal five-minor state for even order. -/
def foldEvenTerminalState (a x s : ℝ) : FoldMinorState where
  d := (1 + s) * (a + s) - x ^ 2
  p := -a - s
  q := -1 - s
  c := x
  r := 1

/-- The terminal five-minor state for odd order. -/
def foldOddTerminalState (a x s : ℝ) : FoldMinorState where
  d := x * (1 + a ^ 2) + 2 * a * s - foldC0 a x s * (x - s)
  p := s ^ 2 - s * x - a ^ 2
  q := s ^ 2 - s * x - 1
  c := x ^ 2 - s * x - a
  r := x - s

/-- Fieldwise extensionality for an exposed-minor state. -/
@[ext] theorem foldMinorState_ext {u v : FoldMinorState}
    (hd : u.d = v.d) (hp : u.p = v.p) (hq : u.q = v.q)
    (hc : u.c = v.c) (hr : u.r = v.r) : u = v := by
  cases u
  cases v
  simp_all

/-- Multiplication of all five minor coordinates by one scalar. -/
def foldMinorScale (t : ℝ) (v : FoldMinorState) : FoldMinorState :=
  ⟨t * v.d, t * v.p, t * v.q, t * v.c, t * v.r⟩

/-- The five-minor update after multiplying the size-`m` state by `(-1)^m`. -/
def foldSignedStep (a x s : ℝ) (v : FoldMinorState) : FoldMinorState :=
  foldMinorScale (-1) (foldMinorStep a x s v)

/-- The signed five-minor iteration. -/
def foldSignedOrbit (a x s : ℝ) (v : FoldMinorState) : ℕ → FoldMinorState
  | 0 => v
  | m + 1 => foldSignedStep a x s (foldSignedOrbit a x s v m)

/-- The even seed, including the auxiliary size-zero minors. -/
def foldEvenSeed (a : ℝ) : FoldMinorState := ⟨1, a⁻¹, 1, 0, a⁻¹⟩

/-- The odd seed, including its unpaired middle coordinate. -/
def foldOddSeed (x s : ℝ) : FoldMinorState := ⟨x - s, 1, 1, -1, 0⟩

/-- Signed extension commutes with the common sign of the old minors. -/
theorem foldSignedStep_scale (a x s t : ℝ) (v : FoldMinorState) :
    foldSignedStep a x s (foldMinorScale t v) =
      foldMinorScale (-t) (foldMinorStep a x s v) := by
  ext <;> simp [foldSignedStep, foldMinorScale, foldMinorStep] <;> ring

/-- The first even iterate is the signed terminal block. -/
theorem foldSignedStep_evenSeed (a x s : ℝ) :
    foldSignedStep a x s (foldEvenSeed a) =
      foldMinorScale (-1) (foldEvenTerminalState a x s) := by
  by_cases ha : a = 0
  · subst a
    ext <;> simp [foldSignedStep, foldMinorStep, foldMinorScale,
      foldEvenSeed, foldEvenTerminalState] <;> ring
  · ext <;> simp [foldSignedStep, foldMinorStep, foldMinorScale,
      foldEvenSeed, foldEvenTerminalState]
    all_goals field_simp
    all_goals ring

/-- The first odd iterate is the signed terminal block. -/
theorem foldSignedStep_oddSeed (a x s : ℝ) :
    foldSignedStep a x s (foldOddSeed x s) =
      foldMinorScale (-1) (foldOddTerminalState a x s) := by
  ext <;> simp [foldSignedStep, foldMinorStep, foldMinorScale,
    foldOddSeed, foldOddTerminalState, foldC0] <;> ring

end

end ConnectedPseudospectrum
