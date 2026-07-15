import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Algebra of the folded signed-pencil transfer

This module kernel-checks the five-minor update, its linear invariant, and the
reduced four-dimensional transfer from the folded calculation in `lem:mesh`.
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

/-- The five exposed minors `(d,p,q,c,r)` used before eliminating the linear
invariant. -/
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

/-- The linear invariant `ℓ_m` of the five-minor update. -/
def foldMinorInvariant (a x s : ℝ) (v : FoldMinorState) : ℝ :=
  (1 - a) * v.d - a * s * v.p + s * v.q +
    (1 - a) * x * v.c - a * (1 - a) * v.r

/-- Direct substitution gives `ℓ_{m+1}=-aℓ_m`. -/
theorem foldMinorInvariant_step (a x s : ℝ) (v : FoldMinorState) :
    foldMinorInvariant a x s (foldMinorStep a x s v) =
      -a * foldMinorInvariant a x s v := by
  simp only [foldMinorInvariant, foldMinorStep]
  ring

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

/-- The even terminal state lies on the invariant hyperplane. -/
theorem foldMinorInvariant_evenTerminal (a x s : ℝ) :
    foldMinorInvariant a x s (foldEvenTerminalState a x s) = 0 := by
  simp only [foldMinorInvariant, foldEvenTerminalState]
  ring

/-- The odd terminal state lies on the invariant hyperplane. -/
theorem foldMinorInvariant_oddTerminal (a x s : ℝ) :
    foldMinorInvariant a x s (foldOddTerminalState a x s) = 0 := by
  simp only [foldMinorInvariant, foldOddTerminalState, foldC0]
  ring

/-- Projection of a five-minor state to its first four coordinates. -/
def foldFourProjection (v : FoldMinorState) : Fin 4 → ℝ :=
  ![v.d, v.p, v.q, v.c]

/-- The reduced transfer matrix `eq:fold-four-transfer`. -/
def foldTransfer (a x s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![x ^ 2 - s ^ 2 - a, a ^ 3 * s / (1 - a), -s / (1 - a), a * x;
     s,                   a ^ 2,                 0,              0;
     s,                   0,                     1,              0;
     -x,                  0,                     0,              -a]

/-- Eliminating the fifth minor with the invariant gives the exact reduced
four-dimensional transfer.  The minus sign is the change from unsigned minors
to the paper's `(-1)^m` signed state. -/
theorem neg_foldFourProjection_step_eq_foldTransfer_mulVec
    {a x s : ℝ} (ha1 : a ≠ 1) (v : FoldMinorState)
    (hinv : foldMinorInvariant a x s v = 0) :
    -foldFourProjection (foldMinorStep a x s v) =
      foldTransfer a x s *ᵥ foldFourProjection v := by
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  funext i
  fin_cases i
  · unfold foldMinorInvariant at hinv
    simp [foldFourProjection, foldMinorStep, foldTransfer,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    field_simp [hden]
    linear_combination a * hinv
  · simp [foldFourProjection, foldMinorStep, foldTransfer,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  · simp [foldFourProjection, foldMinorStep, foldTransfer,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring
  · simp [foldFourProjection, foldMinorStep, foldTransfer,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    ring

/-- The formal characteristic polynomial displayed in
`eq:fold-transfer-characteristic`. -/
def foldCharacteristicValue (a x s lam : ℝ) : ℝ :=
  lam ^ 4 - foldC0 a x s * lam ^ 3 + foldB a x s * lam ^ 2 -
    a ^ 2 * foldC0 a x s * lam + a ^ 4

/-- Determinant of a four-dimensional arrowhead matrix.  This elementary
identity keeps the explicit folded characteristic calculation independent of
any inverse or generic-eigenvalue hypothesis. -/
theorem det_arrowhead_four
    (d0 d1 d2 d3 b1 b2 b3 c1 c2 c3 : ℝ) :
    Matrix.det !![d0, b1, b2, b3;
                  c1, d1, 0, 0;
                  c2, 0, d2, 0;
                  c3, 0, 0, d3] =
      d0 * d1 * d2 * d3 - b1 * c1 * d2 * d3 -
        b2 * c2 * d1 * d3 - b3 * c3 * d1 * d2 := by
  let A : Matrix (Fin 4) (Fin 4) ℝ :=
    !![d0, b1, b2, b3;
       c1, d1, 0, 0;
       c2, 0, d2, 0;
       c3, 0, 0, d3]
  change Matrix.det A = _
  have h0 : A.submatrix Fin.succ (0 : Fin 4).succAbove =
      !![d1, 0, 0; 0, d2, 0; 0, 0, d3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h1 : A.submatrix Fin.succ (1 : Fin 4).succAbove =
      !![c1, 0, 0; c2, d2, 0; c3, 0, d3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h2 : A.submatrix Fin.succ (2 : Fin 4).succAbove =
      !![c1, d1, 0; c2, 0, 0; c3, 0, d3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have h3 : A.submatrix Fin.succ (3 : Fin 4).succAbove =
      !![c1, d1, 0; c2, 0, d2; c3, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero]
  rw [Fin.sum_univ_four, h0, h1, h2, h3]
  simp [A, Matrix.det_fin_three]
  ring

/-- Direct determinant calculation for
`eq:fold-transfer-characteristic`. -/
theorem det_sub_foldTransfer_eq_foldCharacteristicValue
    {a x s lam : ℝ} (ha1 : a ≠ 1) :
    Matrix.det (lam • (1 : Matrix (Fin 4) (Fin 4) ℝ) -
      foldTransfer a x s) = foldCharacteristicValue a x s lam := by
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  have hmat : lam • (1 : Matrix (Fin 4) (Fin 4) ℝ) -
      foldTransfer a x s =
      !![lam - (x ^ 2 - s ^ 2 - a), -a ^ 3 * s / (1 - a), s / (1 - a), -a * x;
         -s, lam - a ^ 2, 0, 0;
         -s, 0, lam - 1, 0;
         x, 0, 0, lam + a] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [foldTransfer]
    all_goals ring
  rw [hmat, det_arrowhead_four]
  simp only [foldCharacteristicValue, foldC0, foldB]
  field_simp [hden]
  ring

/-- The folded transfer satisfies the fourth-degree polynomial displayed in
`eq:fold-transfer-characteristic`.  The preceding exact determinant formula
identifies the characteristic polynomial by polynomial extensionality, and
Cayley--Hamilton then supplies the matrix identity used by the recurrence. -/
theorem foldTransfer_polynomial_eq_zero
    {a x s : ℝ} (ha1 : a ≠ 1) :
    foldTransfer a x s ^ 4 -
        foldC0 a x s • foldTransfer a x s ^ 3 +
        foldB a x s • foldTransfer a x s ^ 2 -
        (a ^ 2 * foldC0 a x s) • foldTransfer a x s +
        a ^ 4 • (1 : Matrix (Fin 4) (Fin 4) ℝ) = 0 := by
  let p : Polynomial ℝ :=
    Polynomial.X ^ 4 -
      Polynomial.C (foldC0 a x s) * Polynomial.X ^ 3 +
      Polynomial.C (foldB a x s) * Polynomial.X ^ 2 -
      Polynomial.C (a ^ 2 * foldC0 a x s) * Polynomial.X +
      Polynomial.C (a ^ 4)
  have hscalar (lam : ℝ) :
      Matrix.scalar (Fin 4) lam =
        lam • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hchar : (foldTransfer a x s).charpoly = p := by
    apply Polynomial.funext
    intro lam
    rw [Matrix.eval_charpoly, hscalar,
      det_sub_foldTransfer_eq_foldCharacteristicValue ha1]
    simp only [p, foldCharacteristicValue, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
  have hCH := Matrix.aeval_self_charpoly (foldTransfer a x s)
  rw [hchar] at hCH
  simpa only [p, map_add, map_sub, map_mul, map_pow,
    Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_pow, one_pow, Matrix.smul_mul,
    Matrix.one_mul, smul_smul] using hCH

/-- A coordinate of an iterated folded-transfer orbit. -/
def foldTransferCoordinate (a x s : ℝ) (v : Fin 4 → ℝ)
    (i : Fin 4) (m : ℕ) : ℝ :=
  (foldTransfer a x s ^ m *ᵥ v) i

/-- Every coordinate of every folded-transfer orbit satisfies the paper's
fourth-order scalar recurrence. -/
theorem foldTransferCoordinate_recurrence
    {a x s : ℝ} (ha1 : a ≠ 1) (v : Fin 4 → ℝ)
    (i : Fin 4) (m : ℕ) :
    foldTransferCoordinate a x s v i (m + 4) -
        foldC0 a x s * foldTransferCoordinate a x s v i (m + 3) +
        foldB a x s * foldTransferCoordinate a x s v i (m + 2) -
        a ^ 2 * foldC0 a x s * foldTransferCoordinate a x s v i (m + 1) +
        a ^ 4 * foldTransferCoordinate a x s v i m = 0 := by
  let T := foldTransfer a x s
  have hp := foldTransfer_polynomial_eq_zero (a := a) (x := x) (s := s) ha1
  have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ =>
    ((T ^ m * M) *ᵥ v) i) hp
  dsimp only [T] at h
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
    Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  simpa only [foldTransferCoordinate, pow_add, pow_one, Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mulVec, Pi.zero_apply] using h

/-- The even initial signed four-state at `m=0`. -/
def foldEvenInitial (a : ℝ) : Fin 4 → ℝ :=
  ![1, a⁻¹, 1, 0]

/-- The odd initial signed four-state at `m=0`. -/
def foldOddInitial (x s : ℝ) : Fin 4 → ℝ :=
  ![x - s, 1, 1, -1]

/-- Direct multiplication gives the signed even terminal minors. -/
theorem foldTransfer_mulVec_evenInitial
    {a x s : ℝ} (ha1 : a ≠ 1) :
    foldTransfer a x s *ᵥ foldEvenInitial a =
      ![x ^ 2 - (1 + s) * (a + s), a + s, 1 + s, -x] := by
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  funext i
  fin_cases i
  · simp [foldTransfer, foldEvenInitial, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    field_simp [hden]
    ring
  · simp [foldTransfer, foldEvenInitial, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    by_cases ha0 : a = 0
    · simp [ha0]
    · field_simp [ha0]
      ring
  · simp [foldTransfer, foldEvenInitial, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    ring
  · simp [foldTransfer, foldEvenInitial, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]

/-- Direct multiplication gives the signed odd terminal minors. -/
theorem foldTransfer_mulVec_oddInitial
    {a x s : ℝ} (ha1 : a ≠ 1) :
    foldTransfer a x s *ᵥ foldOddInitial x s =
      ![foldC0 a x s * (x - s) - x * (1 + a ^ 2) - 2 * a * s,
        a ^ 2 - s ^ 2 + s * x,
        1 - s ^ 2 + s * x,
        a + s * x - x ^ 2] := by
  have hden : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  funext i
  fin_cases i
  · simp [foldTransfer, foldOddInitial, foldC0, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    field_simp [hden]
    ring
  · simp [foldTransfer, foldOddInitial, foldC0, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    ring
  · simp [foldTransfer, foldOddInitial, foldC0, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    ring
  · simp [foldTransfer, foldOddInitial, foldC0, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four]
    ring

end

end ConnectedPseudospectrum
