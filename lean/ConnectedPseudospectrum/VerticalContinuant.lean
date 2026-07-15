import ConnectedPseudospectrum.VerticalToeplitz
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Continuants and endpoint cofactors for the vertical pencil

This module formalizes the determinant bookkeeping in equations
`eq:D-R-def` and `eq:T-recurrence` of the source.  In particular, the
dimension-one endpoint collision is kept separate from the two distinct
endpoint cofactors occurring from dimension two onward.
-/

namespace ConnectedPseudospectrum

open Matrix

noncomputable section

/-- A sequence value shifted to the past, with the paper's convention that
all negative-index values are zero. -/
def lagWithZero {R : Type*} [Zero R] (u : ℕ → R) (k shift : ℕ) : R :=
  if shift ≤ k then u (k - shift) else 0

theorem lagWithZero_zero {R : Type*} [Zero R] (u : ℕ → R) (k : ℕ) :
    lagWithZero u k 0 = u k := by
  simp [lagWithZero]

@[simp] theorem lagWithZero_of_le {R : Type*} [Zero R] (u : ℕ → R)
    {k shift : ℕ} (h : shift ≤ k) :
    lagWithZero u k shift = u (k - shift) := by
  simp [lagWithZero, h]

@[simp] theorem lagWithZero_of_lt {R : Type*} [Zero R] (u : ℕ → R)
    {k shift : ℕ} (h : k < shift) :
    lagWithZero u k shift = 0 := by
  simp [lagWithZero, Nat.not_le.mpr h]

/-- The paper's `D_k = T_k - T_{k-1}`, with `T_{-1}=0`. -/
def verticalLeadingMinor (k : ℕ) (a x Y t : ℝ) : ℂ :=
  verticalToeplitzDet k a x Y t -
    lagWithZero (fun m => verticalToeplitzDet m a x Y t) k 1

/-- The paper's `R_k = T_k - a²T_{k-1}`, with `T_{-1}=0`. -/
def verticalTrailingMinor (k : ℕ) (a x Y t : ℝ) : ℂ :=
  verticalToeplitzDet k a x Y t - (a : ℂ) ^ 2 *
    lagWithZero (fun m => verticalToeplitzDet m a x Y t) k 1

@[simp] theorem verticalLeadingMinor_zero (a x Y t : ℝ) :
    verticalLeadingMinor 0 a x Y t = 1 := by
  simp [verticalLeadingMinor]

@[simp] theorem verticalTrailingMinor_zero (a x Y t : ℝ) :
    verticalTrailingMinor 0 a x Y t = 1 := by
  simp [verticalTrailingMinor]

@[simp] theorem verticalLeadingMinor_succ (k : ℕ) (a x Y t : ℝ) :
    verticalLeadingMinor (k + 1) a x Y t =
      verticalToeplitzDet (k + 1) a x Y t - verticalToeplitzDet k a x Y t := by
  simp [verticalLeadingMinor, lagWithZero]

@[simp] theorem verticalTrailingMinor_succ (k : ℕ) (a x Y t : ℝ) :
    verticalTrailingMinor (k + 1) a x Y t =
      verticalToeplitzDet (k + 1) a x Y t -
        (a : ℂ) ^ 2 * verticalToeplitzDet k a x Y t := by
  simp [verticalTrailingMinor, lagWithZero]

/-- The correction supported at the first diagonal entry. -/
def firstEndpointCorrection (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i = j ∧ i.1 = 0 then 1 else 0

/-- The correction supported at the last diagonal entry. -/
def lastEndpointCorrection (n : ℕ) (a : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => if i = j ∧ i.1 + 1 = n then (a : ℂ) ^ 2 else 0

/-- The Toeplitz matrix after lowering its first diagonal entry by one. -/
def leadingCorrectedToeplitz (n : ℕ) (a x Y t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  verticalToeplitz n a x Y t - firstEndpointCorrection n

/-- The Toeplitz matrix after lowering its last diagonal entry by `a²`. -/
def trailingCorrectedToeplitz (n : ℕ) (a x Y t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  verticalToeplitz n a x Y t - lastEndpointCorrection n a

/-- The matrix with both endpoint corrections.  In dimension one both
corrections act on the same entry, as required by the source. -/
def endpointCorrectedToeplitz (n : ℕ) (a x Y t : ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  leadingCorrectedToeplitz n a x Y t - lastEndpointCorrection n a

@[simp] theorem firstEndpointCorrection_succ (n : ℕ) :
    firstEndpointCorrection (n + 1) = Matrix.single 0 0 1 := by
  ext i j
  simp only [firstEndpointCorrection, Matrix.single_apply]
  by_cases h : i = j ∧ i.1 = 0
  · obtain ⟨rfl, hi⟩ := h
    have hiz : i = 0 := Fin.ext hi
    subst i
    simp
  · rw [if_neg h, if_neg]
    intro hsingle
    apply h
    constructor
    · exact hsingle.1.symm.trans hsingle.2
    · simpa using (congr_arg Fin.val hsingle.1).symm

@[simp] theorem lastEndpointCorrection_succ (n : ℕ) (a : ℝ) :
    lastEndpointCorrection (n + 1) a =
      Matrix.single (Fin.last n) (Fin.last n) ((a : ℂ) ^ 2) := by
  ext i j
  simp only [lastEndpointCorrection, Matrix.single_apply]
  by_cases h : i = j ∧ i.1 + 1 = n + 1
  · obtain ⟨rfl, hi⟩ := h
    have hilast : i = Fin.last n := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    subst i
    simp
  · rw [if_neg h, if_neg]
    intro hsingle
    apply h
    constructor
    · exact hsingle.1.symm.trans hsingle.2
    · have hi := congr_arg Fin.val hsingle.1
      simp only [Fin.val_last] at hi
      omega

/-- Determinant affine-linearity for changing one diagonal entry. -/
theorem det_sub_single_diagonal {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) (c : ℂ) :
    (M - Matrix.single i i c).det =
      M.det - c * (M.submatrix i.succAbove i.succAbove).det := by
  classical
  have hmatrix :
      M - Matrix.single i i c =
        M.updateRow i
          (M i + (-c) • (Pi.single i (1 : ℂ) : Fin (n + 1) → ℂ)) := by
    ext r s
    by_cases hr : r = i
    · subst r
      rw [Matrix.updateRow_apply, if_pos rfl]
      by_cases hs : i = s
      · simp [hs]
        ring
      · simp [hs]
    · rw [Matrix.updateRow_apply, if_neg hr]
      simp [Ne.symm hr]
  rw [hmatrix, Matrix.det_updateRow_add, Matrix.updateRow_eq_self,
    Matrix.det_updateRow_smul, ← Matrix.adjugate_apply,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  have heven : Even (i.1 + i.1) := ⟨i.1, by omega⟩
  rw [heven.neg_one_pow]
  ring

/-- Deleting the first row and column of a pure Toeplitz matrix gives the
next smaller pure Toeplitz matrix. -/
theorem verticalToeplitz_submatrix_succ (n : ℕ) (a x Y t : ℝ) :
    (verticalToeplitz (n + 1) a x Y t).submatrix Fin.succ Fin.succ =
      verticalToeplitz n a x Y t := by
  ext i j
  simp only [Matrix.submatrix_apply, verticalToeplitz_apply, Fin.val_succ]
  have hdiag : (Fin.succ i = Fin.succ j) ↔ i = j := Fin.succ_inj
  have hup : (j.1 + 1 = i.1 + 1 + 1) ↔ j.1 = i.1 + 1 := by omega
  have hlow : (i.1 + 1 = j.1 + 1 + 1) ↔ i.1 = j.1 + 1 := by omega
  have hup₂ : (j.1 + 1 = i.1 + 1 + 2) ↔ j.1 = i.1 + 2 := by omega
  have hlow₂ : (i.1 + 1 = j.1 + 1 + 2) ↔ i.1 = j.1 + 2 := by omega
  simp only [hdiag, hup, hlow, hup₂, hlow₂]

/-- Deleting the last row and column of a pure Toeplitz matrix gives the
next smaller pure Toeplitz matrix. -/
theorem verticalToeplitz_submatrix_castSucc (n : ℕ) (a x Y t : ℝ) :
    (verticalToeplitz (n + 1) a x Y t).submatrix Fin.castSucc Fin.castSucc =
      verticalToeplitz n a x Y t := by
  ext i j
  simp only [Matrix.submatrix_apply, verticalToeplitz_apply, Fin.val_castSucc]
  have hdiag : (i.castSucc = j.castSucc) ↔ i = j := by
    constructor
    · intro h
      apply Fin.ext
      exact congr_arg (fun z : Fin (n + 1) => z.1) h
    · intro h
      exact congr_arg (fun z : Fin n => z.castSucc) h
  simp only [hdiag]

/-- The first-corrected Toeplitz determinant is exactly `D_k`. -/
theorem det_leadingCorrectedToeplitz (n : ℕ) (a x Y t : ℝ) :
    (leadingCorrectedToeplitz n a x Y t).det =
      verticalLeadingMinor n a x Y t := by
  cases n with
  | zero => simp [leadingCorrectedToeplitz]
  | succ n =>
      rw [leadingCorrectedToeplitz, firstEndpointCorrection_succ,
        det_sub_single_diagonal, Fin.succAbove_zero,
        verticalToeplitz_submatrix_succ]
      simp [verticalToeplitzDet]

/-- The last-corrected Toeplitz determinant is exactly `R_k`. -/
theorem det_trailingCorrectedToeplitz (n : ℕ) (a x Y t : ℝ) :
    (trailingCorrectedToeplitz n a x Y t).det =
      verticalTrailingMinor n a x Y t := by
  cases n with
  | zero => simp [trailingCorrectedToeplitz]
  | succ n =>
      rw [trailingCorrectedToeplitz, lastEndpointCorrection_succ,
        det_sub_single_diagonal, Fin.succAbove_last,
        verticalToeplitz_submatrix_castSucc]
      simp [verticalToeplitzDet]

/-- Removing the last coordinate from a leading-corrected matrix leaves the
leading-corrected matrix of the next smaller size. -/
theorem leadingCorrectedToeplitz_submatrix_castSucc (n : ℕ) (a x Y t : ℝ) :
    (leadingCorrectedToeplitz (n + 1) a x Y t).submatrix
        Fin.castSucc Fin.castSucc =
      leadingCorrectedToeplitz n a x Y t := by
  ext i j
  simp only [leadingCorrectedToeplitz, Matrix.submatrix_apply, Matrix.sub_apply,
    verticalToeplitz_apply, Fin.val_castSucc, firstEndpointCorrection]
  have hdiag : (i.castSucc = j.castSucc) ↔ i = j := by
    constructor
    · intro h
      apply Fin.ext
      exact congr_arg (fun z : Fin (n + 1) => z.1) h
    · intro h
      exact congr_arg (fun z : Fin n => z.castSucc) h
  simp only [hdiag]

/-- Applying both endpoint changes gives the paper's cofactor identity
`F_k = D_k - a²D_{k-1}` at the determinant level. -/
theorem det_endpointCorrectedToeplitz_succ (n : ℕ) (a x Y t : ℝ) :
    (endpointCorrectedToeplitz (n + 1) a x Y t).det =
      verticalLeadingMinor (n + 1) a x Y t -
        (a : ℂ) ^ 2 * verticalLeadingMinor n a x Y t := by
  rw [endpointCorrectedToeplitz, lastEndpointCorrection_succ,
    det_sub_single_diagonal, Fin.succAbove_last,
    leadingCorrectedToeplitz_submatrix_castSucc,
    det_leadingCorrectedToeplitz, det_leadingCorrectedToeplitz]

/-- Under `Y ≥ 0`, the endpoint-corrected Toeplitz matrix is exactly the
vertical pencil in every dimension, including zero and one. -/
theorem verticalPencil_eq_endpointCorrectedToeplitz
    (n : ℕ) (a x Y t : ℝ) (hY : 0 ≤ Y) :
    verticalPencil n a x Y t = endpointCorrectedToeplitz n a x Y t := by
  cases n with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ n =>
      cases n with
      | zero =>
          rw [verticalPencil_one a x Y t hY]
          ext i j
          fin_cases i
          fin_cases j
          simp [endpointCorrectedToeplitz, leadingCorrectedToeplitz,
            verticalToeplitz_apply, verticalToeplitzDiagonal]
          ring
      | succ n =>
          ext i j
          rw [verticalPencil_apply_eq_verticalToeplitz_sub_endpoints
            (n + 2) (by omega) a x Y t hY]
          rfl

/-- The exact coefficient identity from `eq:D-F-generating`, without using
generating functions. -/
theorem verticalPencilDet_eq_leadingMinor_sub (n : ℕ) (a x Y t : ℝ)
    (hY : 0 ≤ Y) :
    verticalPencilDet n a x Y t =
      verticalLeadingMinor n a x Y t - (a : ℂ) ^ 2 *
        lagWithZero (fun k => verticalLeadingMinor k a x Y t) n 1 := by
  cases n with
  | zero => simp [verticalPencilDet]
  | succ n =>
      rw [verticalPencilDet, verticalPencil_eq_endpointCorrectedToeplitz _ _ _ _ _ hY,
        det_endpointCorrectedToeplitz_succ]
      simp [lagWithZero]

/-! ## Six boundary states for the pentadiagonal continuant -/

/-- The translation-invariant five-diagonal entry with independent first
upper and lower coefficients.  Integer column coordinates allow the two
unmatched columns at a Laplace-expansion frontier to lie to the left of the
current row. -/
def pentadiagonalBandEntry (d b c q : ℂ) (row col : ℤ) : ℂ :=
  d * (if row = col then 1 else 0) +
    b * (if col = row + 1 then 1 else 0) +
    c * (if row = col + 1 then 1 else 0) +
    q * (if col = row + 2 then 1 else 0) +
    q * (if row = col + 2 then 1 else 0)

/-- The smaller of the two unmatched column offsets for a frontier state.
The six states enumerate the two-element subsets of `{-2,-1,0,1}` in
lexicographic order. -/
def continuantFrontierLeft (s : Fin 6) : ℤ :=
  match s.1 with
  | 0 | 1 | 2 => -2
  | 3 | 4 => -1
  | _ => 0

/-- The larger unmatched column offset for a frontier state. -/
def continuantFrontierRight (s : Fin 6) : ℤ :=
  match s.1 with
  | 0 => -1
  | 1 => 0
  | 2 => 1
  | 3 => 0
  | _ => 1

/-- Ordered column coordinate at a frontier.  Positions zero and one are
the unmatched columns; all later positions form the untouched right tail. -/
def continuantFrontierColumn {n : ℕ} (s : Fin 6) (j : Fin n) : ℤ :=
  if j.1 = 0 then continuantFrontierLeft s
  else if j.1 = 1 then continuantFrontierRight s
  else (j.1 : ℤ)

@[simp] theorem continuantFrontierColumn_zero (n : ℕ) (s : Fin 6) :
    continuantFrontierColumn s (0 : Fin (n + 1)) = continuantFrontierLeft s := by
  simp [continuantFrontierColumn]

@[simp] theorem continuantFrontierColumn_one (n : ℕ) (s : Fin 6) :
    continuantFrontierColumn s (1 : Fin (n + 2)) = continuantFrontierRight s := by
  simp [continuantFrontierColumn]

theorem continuantFrontierColumn_of_two_le {n : ℕ} (s : Fin 6) (j : Fin n)
    (hj : 2 ≤ j.1) :
    continuantFrontierColumn s j = (j.1 : ℤ) := by
  rw [continuantFrontierColumn, if_neg (by omega), if_neg (by omega)]

private theorem continuantFrontierColumn_eq_left {n : ℕ} (s : Fin 6) (j : Fin n)
    (hj : j.1 = 0) :
    continuantFrontierColumn s j = continuantFrontierLeft s := by
  rw [continuantFrontierColumn, if_pos hj]

private theorem continuantFrontierColumn_eq_right {n : ℕ} (s : Fin 6) (j : Fin n)
    (h₀ : j.1 ≠ 0) (h₁ : j.1 = 1) :
    continuantFrontierColumn s j = continuantFrontierRight s := by
  rw [continuantFrontierColumn, if_neg h₀, if_pos h₁]

/-- The square minor associated with one of the six width-two frontier
states. -/
def continuantFrontierMatrix (n : ℕ) (d b c q : ℂ) (s : Fin 6) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => pentadiagonalBandEntry d b c q (i.1 : ℤ)
    (continuantFrontierColumn s j)

/-- Determinant of a frontier minor. -/
def continuantFrontierDet (n : ℕ) (d b c q : ℂ) (s : Fin 6) : ℂ :=
  (continuantFrontierMatrix n d b c q s).det

@[simp] theorem continuantFrontierDet_five_zero (d b c q : ℂ) :
    continuantFrontierDet 0 d b c q 5 = 1 := by
  simp [continuantFrontierDet]

@[simp] theorem continuantFrontierDet_five_one (d b c q : ℂ) :
    continuantFrontierDet 1 d b c q 5 = d := by
  rw [continuantFrontierDet, Matrix.det_fin_one]
  norm_num [continuantFrontierMatrix, continuantFrontierColumn,
    continuantFrontierLeft, continuantFrontierRight, pentadiagonalBandEntry]

@[simp] theorem continuantFrontierDet_zero_two (d b c q : ℂ) :
    continuantFrontierDet 2 d b c q 0 = q ^ 2 := by
  rw [continuantFrontierDet, Matrix.det_fin_two]
  norm_num [continuantFrontierMatrix, continuantFrontierColumn,
    continuantFrontierLeft, continuantFrontierRight, pentadiagonalBandEntry]
  ring

@[simp] theorem continuantFrontierDet_one_two (d b c q : ℂ) :
    continuantFrontierDet 2 d b c q 1 = q * c := by
  rw [continuantFrontierDet, Matrix.det_fin_two]
  norm_num [continuantFrontierMatrix, continuantFrontierColumn,
    continuantFrontierLeft, continuantFrontierRight, pentadiagonalBandEntry]

@[simp] theorem continuantFrontierDet_two_two (d b c q : ℂ) :
    continuantFrontierDet 2 d b c q 2 = q * d := by
  rw [continuantFrontierDet, Matrix.det_fin_two]
  norm_num [continuantFrontierMatrix, continuantFrontierColumn,
    continuantFrontierLeft, continuantFrontierRight, pentadiagonalBandEntry]

@[simp] theorem continuantFrontierDet_three_two (d b c q : ℂ) :
    continuantFrontierDet 2 d b c q 3 = c ^ 2 - d * q := by
  rw [continuantFrontierDet, Matrix.det_fin_two]
  norm_num [continuantFrontierMatrix, continuantFrontierColumn,
    continuantFrontierLeft, continuantFrontierRight, pentadiagonalBandEntry]
  ring

@[simp] theorem continuantFrontierDet_four_two (d b c q : ℂ) :
    continuantFrontierDet 2 d b c q 4 = c * d - b * q := by
  rw [continuantFrontierDet, Matrix.det_fin_two]
  norm_num [continuantFrontierMatrix, continuantFrontierColumn,
    continuantFrontierLeft, continuantFrontierRight, pentadiagonalBandEntry]

@[simp] theorem continuantFrontierDet_five_two (d b c q : ℂ) :
    continuantFrontierDet 2 d b c q 5 = d ^ 2 - b * c := by
  rw [continuantFrontierDet, Matrix.det_fin_two]
  norm_num [continuantFrontierMatrix, continuantFrontierColumn,
    continuantFrontierLeft, continuantFrontierRight, pentadiagonalBandEntry]
  ring

@[simp] theorem continuantFrontierColumn_five {n : ℕ} (j : Fin n) :
    continuantFrontierColumn (5 : Fin 6) j = (j.1 : ℤ) := by
  by_cases h₀ : j.1 = 0
  · rw [continuantFrontierColumn, if_pos h₀]
    simp only [continuantFrontierLeft]
    exact_mod_cast h₀.symm
  · by_cases h₁ : j.1 = 1
    · rw [continuantFrontierColumn, if_neg h₀, if_pos h₁]
      simp only [continuantFrontierRight]
      exact_mod_cast h₁.symm
    · rw [continuantFrontierColumn, if_neg h₀, if_neg h₁]

/-- Simultaneously translating a row and a frontier column does not change
the band entry. -/
theorem pentadiagonalBandEntry_add_one (d b c q : ℂ) (row col : ℤ) :
    pentadiagonalBandEntry d b c q (row + 1) (col + 1) =
      pentadiagonalBandEntry d b c q row col := by
  have h₀ : (row + 1 = col + 1) ↔ row = col := by omega
  have h₁ : (col + 1 = row + 1 + 1) ↔ col = row + 1 := by omega
  have h₂ : (row + 1 = col + 1 + 1) ↔ row = col + 1 := by omega
  have h₃ : (col + 1 = row + 1 + 2) ↔ col = row + 2 := by omega
  have h₄ : (row + 1 = col + 1 + 2) ↔ row = col + 2 := by omega
  simp only [pentadiagonalBandEntry, h₀, h₁, h₂, h₃, h₄]

/-- State five is the ordinary pure Toeplitz determinant. -/
theorem continuantFrontierMatrix_five_eq_verticalToeplitz
    (n : ℕ) (a x Y t : ℝ) :
    continuantFrontierMatrix n (verticalToeplitzDiagonal a x Y t : ℂ)
        (verticalToeplitzFirst a x Y) (star (verticalToeplitzFirst a x Y))
        (a : ℂ) 5 =
      verticalToeplitz n a x Y t := by
  ext i j
  simp only [continuantFrontierMatrix, continuantFrontierColumn_five,
    verticalToeplitz_apply]
  have h₀ : (((i.1 : ℤ) = (j.1 : ℤ))) ↔ i = j := by
    constructor
    · intro h
      apply Fin.ext
      exact_mod_cast h
    · intro h
      exact_mod_cast congr_arg Fin.val h
  have h₁ : (((j.1 : ℤ) = (i.1 : ℤ) + 1)) ↔ j.1 = i.1 + 1 := by
    omega
  have h₂ : (((i.1 : ℤ) = (j.1 : ℤ) + 1)) ↔ i.1 = j.1 + 1 := by
    omega
  have h₃ : (((j.1 : ℤ) = (i.1 : ℤ) + 2)) ↔ j.1 = i.1 + 2 := by
    omega
  have h₄ : (((i.1 : ℤ) = (j.1 : ℤ) + 2)) ↔ i.1 = j.1 + 2 := by
    omega
  simp only [pentadiagonalBandEntry, h₀, h₁, h₂, h₃, h₄]

theorem continuantFrontierDet_five_eq_verticalToeplitzDet
    (n : ℕ) (a x Y t : ℝ) :
    continuantFrontierDet n (verticalToeplitzDiagonal a x Y t : ℂ)
        (verticalToeplitzFirst a x Y) (star (verticalToeplitzFirst a x Y))
        (a : ℂ) 5 =
      verticalToeplitzDet n a x Y t := by
  rw [continuantFrontierDet, verticalToeplitzDet,
    continuantFrontierMatrix_five_eq_verticalToeplitz]

private theorem frontierColumn_zero_to_two (m : ℕ) (j : Fin (m + 2)) :
    continuantFrontierColumn (0 : Fin 6)
        ((0 : Fin (m + 3)).succAbove j) =
      continuantFrontierColumn (2 : Fin 6) j + 1 := by
  simp [continuantFrontierColumn, continuantFrontierLeft,
    continuantFrontierRight, Fin.succAbove]
  split_ifs <;> omega

private theorem frontierColumn_one_to_four (m : ℕ) (j : Fin (m + 2)) :
    continuantFrontierColumn (1 : Fin 6)
        ((0 : Fin (m + 3)).succAbove j) =
      continuantFrontierColumn (4 : Fin 6) j + 1 := by
  simp [continuantFrontierColumn, continuantFrontierLeft,
    continuantFrontierRight, Fin.succAbove]
  split_ifs <;> omega

private theorem frontierColumn_two_to_five (m : ℕ) (j : Fin (m + 2)) :
    continuantFrontierColumn (2 : Fin 6)
        ((0 : Fin (m + 3)).succAbove j) =
      continuantFrontierColumn (5 : Fin 6) j + 1 := by
  simp [continuantFrontierColumn, continuantFrontierLeft,
    continuantFrontierRight, Fin.succAbove]
  split_ifs <;> omega

private theorem frontierColumn_three_zero_to_four (m : ℕ) (j : Fin (m + 2)) :
    continuantFrontierColumn (3 : Fin 6)
        ((0 : Fin (m + 3)).succAbove j) =
      continuantFrontierColumn (4 : Fin 6) j + 1 := by
  simp [continuantFrontierColumn, continuantFrontierLeft,
    continuantFrontierRight, Fin.succAbove]
  split_ifs <;> omega

private theorem frontierColumn_delete_one (m : ℕ) (old next : Fin 6)
    (hleft : continuantFrontierLeft old = continuantFrontierLeft next + 1)
    (hright : (2 : ℤ) = continuantFrontierRight next + 1)
    (j : Fin (m + 2)) :
    continuantFrontierColumn old ((1 : Fin (m + 3)).succAbove j) =
      continuantFrontierColumn next j + 1 := by
  by_cases h₀ : j.1 = 0
  · have hs : (1 : Fin (m + 3)).succAbove j = j.castSucc := by
      apply Fin.succAbove_of_castSucc_lt
      change j.1 < 1
      omega
    rw [hs, continuantFrontierColumn_eq_left old _ (by simpa using h₀),
      continuantFrontierColumn_eq_left next j h₀, hleft]
  · have hs : (1 : Fin (m + 3)).succAbove j = j.succ := by
      apply Fin.succAbove_of_le_castSucc
      change 1 ≤ j.1
      omega
    rw [hs, continuantFrontierColumn_of_two_le old _ (by
      simp only [Fin.val_succ]
      omega)]
    by_cases h₁ : j.1 = 1
    · rw [continuantFrontierColumn_eq_right next j h₀ h₁]
      simp only [Fin.val_succ]
      have hj : j.1 + 1 = 2 := by omega
      exact (by exact_mod_cast hj : ((j.1 + 1 : ℕ) : ℤ) = 2).trans hright
    · rw [continuantFrontierColumn_of_two_le next j (by omega)]
      simp only [Fin.val_succ]
      norm_num

private theorem frontierColumn_delete_two (m : ℕ) (old next : Fin 6)
    (hleft : continuantFrontierLeft old = continuantFrontierLeft next + 1)
    (hright : continuantFrontierRight old = continuantFrontierRight next + 1)
    (j : Fin (m + 2)) :
    continuantFrontierColumn old ((2 : Fin (m + 3)).succAbove j) =
      continuantFrontierColumn next j + 1 := by
  by_cases h₀ : j.1 = 0
  · have hs : (2 : Fin (m + 3)).succAbove j = j.castSucc := by
      apply Fin.succAbove_of_castSucc_lt
      change j.1 < 2
      omega
    rw [hs, continuantFrontierColumn_eq_left old _ (by simpa using h₀),
      continuantFrontierColumn_eq_left next j h₀, hleft]
  · by_cases h₁ : j.1 = 1
    · have hs : (2 : Fin (m + 3)).succAbove j = j.castSucc := by
        apply Fin.succAbove_of_castSucc_lt
        change j.1 < 2
        omega
      rw [hs, continuantFrontierColumn_eq_right old _ (by simpa using h₀)
        (by simpa using h₁), continuantFrontierColumn_eq_right next j h₀ h₁,
        hright]
    · have hs : (2 : Fin (m + 3)).succAbove j = j.succ := by
        apply Fin.succAbove_of_le_castSucc
        change 2 ≤ j.1
        omega
      rw [hs, continuantFrontierColumn_of_two_le old _ (by
        simp only [Fin.val_succ]
        omega), continuantFrontierColumn_of_two_le next j (by omega)]
      simp only [Fin.val_succ]
      norm_num

private theorem frontierColumn_three_one_to_two (m : ℕ) (j : Fin (m + 2)) :
    continuantFrontierColumn (3 : Fin 6)
        ((1 : Fin (m + 3)).succAbove j) =
      continuantFrontierColumn (2 : Fin 6) j + 1 := by
  exact frontierColumn_delete_one m 3 2 (by norm_num [continuantFrontierLeft])
    (by norm_num [continuantFrontierRight]) j

private theorem frontierColumn_three_two_to_zero (m : ℕ) (j : Fin (m + 2)) :
    continuantFrontierColumn (3 : Fin 6)
        ((2 : Fin (m + 3)).succAbove j) =
      continuantFrontierColumn (0 : Fin 6) j + 1 := by
  exact frontierColumn_delete_two m 3 0 (by norm_num [continuantFrontierLeft])
    (by norm_num [continuantFrontierRight]) j

private theorem frontierColumn_four_zero_to_five (m : ℕ) (j : Fin (m + 2)) :
    continuantFrontierColumn (4 : Fin 6)
        ((0 : Fin (m + 3)).succAbove j) =
      continuantFrontierColumn (5 : Fin 6) j + 1 := by
  simp [continuantFrontierColumn, continuantFrontierLeft,
    continuantFrontierRight, Fin.succAbove]
  split_ifs <;> omega

private theorem frontierColumn_four_one_to_two (m : ℕ) (j : Fin (m + 2)) :
    continuantFrontierColumn (4 : Fin 6)
        ((1 : Fin (m + 3)).succAbove j) =
      continuantFrontierColumn (2 : Fin 6) j + 1 := by
  exact frontierColumn_delete_one m 4 2 (by norm_num [continuantFrontierLeft])
    (by norm_num [continuantFrontierRight]) j

private theorem frontierColumn_four_two_to_one (m : ℕ) (j : Fin (m + 2)) :
    continuantFrontierColumn (4 : Fin 6)
        ((2 : Fin (m + 3)).succAbove j) =
      continuantFrontierColumn (1 : Fin 6) j + 1 := by
  exact frontierColumn_delete_two m 4 1 (by norm_num [continuantFrontierLeft])
    (by norm_num [continuantFrontierRight]) j

private theorem frontierColumn_five_zero_to_five (m : ℕ) (j : Fin (m + 2)) :
    continuantFrontierColumn (5 : Fin 6)
        ((0 : Fin (m + 3)).succAbove j) =
      continuantFrontierColumn (5 : Fin 6) j + 1 := by
  simp [continuantFrontierColumn, continuantFrontierLeft,
    continuantFrontierRight, Fin.succAbove]
  split_ifs <;> omega

private theorem frontierColumn_five_one_to_four (m : ℕ) (j : Fin (m + 2)) :
    continuantFrontierColumn (5 : Fin 6)
        ((1 : Fin (m + 3)).succAbove j) =
      continuantFrontierColumn (4 : Fin 6) j + 1 := by
  exact frontierColumn_delete_one m 5 4 (by norm_num [continuantFrontierLeft])
    (by norm_num [continuantFrontierRight]) j

private theorem frontierColumn_five_two_to_three (m : ℕ) (j : Fin (m + 2)) :
    continuantFrontierColumn (5 : Fin 6)
        ((2 : Fin (m + 3)).succAbove j) =
      continuantFrontierColumn (3 : Fin 6) j + 1 := by
  exact frontierColumn_delete_two m 5 3 (by norm_num [continuantFrontierLeft])
    (by norm_num [continuantFrontierRight]) j

private theorem frontierSubmatrix_eq (m : ℕ) (d b c q : ℂ)
    (s next : Fin 6) (choice : Fin (m + 3))
    (hcol : ∀ j : Fin (m + 2),
      continuantFrontierColumn s (choice.succAbove j) =
        continuantFrontierColumn next j + 1) :
    (continuantFrontierMatrix (m + 3) d b c q s).submatrix
        Fin.succ choice.succAbove =
      continuantFrontierMatrix (m + 2) d b c q next := by
  ext i j
  simp only [Matrix.submatrix_apply, continuantFrontierMatrix, Fin.val_succ]
  rw [hcol j]
  have hrow : (((i.1 + 1 : ℕ) : ℤ)) = (i.1 : ℤ) + 1 := by norm_num
  rw [hrow]
  exact pentadiagonalBandEntry_add_one d b c q (i.1 : ℤ)
    (continuantFrontierColumn next j)

private theorem frontierSubmatrix_det_zero (m : ℕ) (d b c q : ℂ)
    (s : Fin 6) (choice : Fin (m + 3))
    (hfirst : continuantFrontierColumn s
      (choice.succAbove (0 : Fin (m + 2))) = -2) :
    ((continuantFrontierMatrix (m + 3) d b c q s).submatrix
        Fin.succ choice.succAbove).det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero 0
  intro i
  simp only [Matrix.submatrix_apply, continuantFrontierMatrix, Fin.val_succ]
  rw [hfirst]
  have hnonneg : (0 : ℤ) ≤ (i.1 : ℤ) := by positivity
  have h₀ : ¬((i.1 : ℤ) + 1 = -2) := by omega
  have h₁ : ¬(-2 = (i.1 : ℤ) + 1 + 1) := by omega
  have h₂ : ¬((i.1 : ℤ) + 1 = -1) := by omega
  have h₃ : ¬(-2 = (i.1 : ℤ) + 1 + 2) := by omega
  have h₄ : ¬((i.1 : ℤ) + 1 = 0) := by omega
  simp [pentadiagonalBandEntry, h₀, h₁, h₂, h₃, h₄]

private theorem one_mod_add_three (m : ℕ) : 1 % (m + 3) = 1 := by
  exact Nat.mod_eq_of_lt (by omega)

@[simp] private theorem two_mod_add_three (m : ℕ) : 2 % (m + 3) = 2 := by
  exact Nat.mod_eq_of_lt (by omega)

private theorem continuantFrontierDet_expand_three
    (m : ℕ) (d b c q : ℂ) (s : Fin 6) :
    continuantFrontierDet (m + 3) d b c q s =
      continuantFrontierMatrix (m + 3) d b c q s 0 0 *
          ((continuantFrontierMatrix (m + 3) d b c q s).submatrix
            Fin.succ (0 : Fin (m + 3)).succAbove).det -
        continuantFrontierMatrix (m + 3) d b c q s 0 1 *
          ((continuantFrontierMatrix (m + 3) d b c q s).submatrix
            Fin.succ (1 : Fin (m + 3)).succAbove).det +
        continuantFrontierMatrix (m + 3) d b c q s 0 2 *
          ((continuantFrontierMatrix (m + 3) d b c q s).submatrix
            Fin.succ (2 : Fin (m + 3)).succAbove).det := by
  rw [continuantFrontierDet, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have htail :
      (∑ j : Fin m,
          (-1 : ℂ) ^ ((Fin.succ (Fin.succ (Fin.succ j))).1 : ℕ) *
            continuantFrontierMatrix (m + 3) d b c q s 0
              (Fin.succ (Fin.succ (Fin.succ j))) *
            ((continuantFrontierMatrix (m + 3) d b c q s).submatrix
              Fin.succ
                ((Fin.succ (Fin.succ (Fin.succ j)) : Fin (m + 3)).succAbove)).det) = 0 := by
    apply Fintype.sum_eq_zero
    intro j
    have hval : (Fin.succ (Fin.succ (Fin.succ j))).1 = j.1 + 3 := by
      simp only [Fin.val_succ]
    have hcol :
        continuantFrontierColumn s (Fin.succ (Fin.succ (Fin.succ j))) =
          (j.1 : ℤ) + 3 := by
      rw [continuantFrontierColumn_of_two_le]
      · rw [hval, Nat.cast_add]
        norm_num
      · rw [hval]
        omega
    have hentry :
        continuantFrontierMatrix (m + 3) d b c q s 0
          (Fin.succ (Fin.succ (Fin.succ j))) = 0 := by
      rw [continuantFrontierMatrix, hcol]
      have hj : (0 : ℤ) ≤ (j.1 : ℤ) := by positivity
      have h₀ : ¬((0 : ℤ) = (j.1 : ℤ) + 3) := by omega
      have h₁ : ¬((j.1 : ℤ) + 3 = (0 : ℤ) + 1) := by omega
      have h₂ : ¬((0 : ℤ) = (j.1 : ℤ) + 3 + 1) := by omega
      have h₃ : ¬((j.1 : ℤ) + 3 = (0 : ℤ) + 2) := by omega
      have h₄ : ¬((0 : ℤ) = (j.1 : ℤ) + 3 + 2) := by omega
      have hrow : ((0 : Fin (m + 3)).1 : ℤ) = 0 := by simp
      simp only [pentadiagonalBandEntry]
      rw [hrow, if_neg h₀, if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄]
      ring
    rw [hentry]
    ring
  rw [htail]
  have hone : (1 : Fin (m + 3)) = Fin.succ (0 : Fin (m + 2)) := by
    apply Fin.ext
    simp
  have htwo : (2 : Fin (m + 3)) =
      Fin.succ (Fin.succ (0 : Fin (m + 1))) := by
    apply Fin.ext
    simp
  rw [hone, htwo]
  simp only [Fin.val_zero, Fin.val_succ]
  norm_num
  ring

private theorem frontierInvalid_one (m : ℕ) (d b c q : ℂ) (s : Fin 6)
    (hleft : continuantFrontierLeft s = -2) :
    ((continuantFrontierMatrix (m + 3) d b c q s).submatrix
      Fin.succ (1 : Fin (m + 3)).succAbove).det = 0 := by
  apply frontierSubmatrix_det_zero m d b c q s 1
  rw [Fin.one_succAbove_zero, continuantFrontierColumn_zero, hleft]

private theorem frontierInvalid_two (m : ℕ) (d b c q : ℂ) (s : Fin 6)
    (hleft : continuantFrontierLeft s = -2) :
    ((continuantFrontierMatrix (m + 3) d b c q s).submatrix
      Fin.succ (2 : Fin (m + 3)).succAbove).det = 0 := by
  apply frontierSubmatrix_det_zero m d b c q s 2
  have hs : (2 : Fin (m + 3)).succAbove (0 : Fin (m + 2)) = 0 := by
    apply Fin.succAbove_of_castSucc_lt
    change (0 : ℕ) < 2
    omega
  rw [hs, continuantFrontierColumn_zero, hleft]

/-- First-order continuant transfer for frontier state zero. -/
theorem continuantFrontierDet_zero_succ (m : ℕ) (d b c q : ℂ) :
    continuantFrontierDet (m + 3) d b c q 0 =
      q * continuantFrontierDet (m + 2) d b c q 2 := by
  rw [continuantFrontierDet_expand_three]
  rw [frontierSubmatrix_eq m d b c q 0 2 0 (frontierColumn_zero_to_two m)]
  rw [frontierInvalid_one m d b c q 0 (by norm_num [continuantFrontierLeft]),
    frontierInvalid_two m d b c q 0 (by norm_num [continuantFrontierLeft])]
  simp [continuantFrontierMatrix, continuantFrontierDet,
    continuantFrontierColumn, continuantFrontierLeft, continuantFrontierRight,
    pentadiagonalBandEntry]

/-- First-order continuant transfer for frontier state one. -/
theorem continuantFrontierDet_one_succ (m : ℕ) (d b c q : ℂ) :
    continuantFrontierDet (m + 3) d b c q 1 =
      q * continuantFrontierDet (m + 2) d b c q 4 := by
  rw [continuantFrontierDet_expand_three]
  rw [frontierSubmatrix_eq m d b c q 1 4 0 (frontierColumn_one_to_four m)]
  rw [frontierInvalid_one m d b c q 1 (by norm_num [continuantFrontierLeft]),
    frontierInvalid_two m d b c q 1 (by norm_num [continuantFrontierLeft])]
  simp [continuantFrontierMatrix, continuantFrontierDet,
    continuantFrontierColumn, continuantFrontierLeft, continuantFrontierRight,
    pentadiagonalBandEntry]

/-- First-order continuant transfer for frontier state two. -/
theorem continuantFrontierDet_two_succ (m : ℕ) (d b c q : ℂ) :
    continuantFrontierDet (m + 3) d b c q 2 =
      q * continuantFrontierDet (m + 2) d b c q 5 := by
  rw [continuantFrontierDet_expand_three]
  rw [frontierSubmatrix_eq m d b c q 2 5 0 (frontierColumn_two_to_five m)]
  rw [frontierInvalid_one m d b c q 2 (by norm_num [continuantFrontierLeft]),
    frontierInvalid_two m d b c q 2 (by norm_num [continuantFrontierLeft])]
  simp [continuantFrontierMatrix, continuantFrontierDet,
    continuantFrontierColumn, continuantFrontierLeft, continuantFrontierRight,
    pentadiagonalBandEntry]

/-- First-order continuant transfer for frontier state three. -/
theorem continuantFrontierDet_three_succ (m : ℕ) (d b c q : ℂ) :
    continuantFrontierDet (m + 3) d b c q 3 =
      c * continuantFrontierDet (m + 2) d b c q 4 -
        d * continuantFrontierDet (m + 2) d b c q 2 +
        q * continuantFrontierDet (m + 2) d b c q 0 := by
  rw [continuantFrontierDet_expand_three]
  rw [frontierSubmatrix_eq m d b c q 3 4 0 (frontierColumn_three_zero_to_four m),
    frontierSubmatrix_eq m d b c q 3 2 1 (frontierColumn_three_one_to_two m),
    frontierSubmatrix_eq m d b c q 3 0 2 (frontierColumn_three_two_to_zero m)]
  simp [continuantFrontierMatrix, continuantFrontierDet,
    continuantFrontierColumn, continuantFrontierLeft, continuantFrontierRight,
    pentadiagonalBandEntry]

/-- First-order continuant transfer for frontier state four. -/
theorem continuantFrontierDet_four_succ (m : ℕ) (d b c q : ℂ) :
    continuantFrontierDet (m + 3) d b c q 4 =
      c * continuantFrontierDet (m + 2) d b c q 5 -
        b * continuantFrontierDet (m + 2) d b c q 2 +
        q * continuantFrontierDet (m + 2) d b c q 1 := by
  rw [continuantFrontierDet_expand_three]
  rw [frontierSubmatrix_eq m d b c q 4 5 0 (frontierColumn_four_zero_to_five m),
    frontierSubmatrix_eq m d b c q 4 2 1 (frontierColumn_four_one_to_two m),
    frontierSubmatrix_eq m d b c q 4 1 2 (frontierColumn_four_two_to_one m)]
  simp [continuantFrontierMatrix, continuantFrontierDet,
    continuantFrontierColumn, continuantFrontierLeft, continuantFrontierRight,
    pentadiagonalBandEntry]

/-- First-order continuant transfer for the ordinary Toeplitz state. -/
theorem continuantFrontierDet_five_succ (m : ℕ) (d b c q : ℂ) :
    continuantFrontierDet (m + 3) d b c q 5 =
      d * continuantFrontierDet (m + 2) d b c q 5 -
        b * continuantFrontierDet (m + 2) d b c q 4 +
        q * continuantFrontierDet (m + 2) d b c q 3 := by
  rw [continuantFrontierDet_expand_three]
  rw [frontierSubmatrix_eq m d b c q 5 5 0 (frontierColumn_five_zero_to_five m),
    frontierSubmatrix_eq m d b c q 5 4 1 (frontierColumn_five_one_to_four m),
    frontierSubmatrix_eq m d b c q 5 3 2 (frontierColumn_five_two_to_three m)]
  simp [continuantFrontierMatrix, continuantFrontierDet,
    continuantFrontierColumn, continuantFrontierLeft, continuantFrontierRight,
    pentadiagonalBandEntry]

/-- The six-by-six transfer matrix for the width-two determinant frontier. -/
def continuantTransfer (d b c q : ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 0, q, 0, 0, 0;
     0, 0, 0, 0, q, 0;
     0, 0, 0, 0, 0, q;
     q, 0, -d, 0, c, 0;
     0, q, -b, 0, 0, c;
     0, 0, 0, q, -b, d]

/-- The six frontier determinants at a fixed size, viewed as a column vector. -/
def continuantFrontierVector (n : ℕ) (d b c q : ℂ) : Fin 6 → ℂ :=
  fun s => continuantFrontierDet n d b c q s

/-- The size-two initial frontier vector. -/
def continuantInitialVector (d b c q : ℂ) : Fin 6 → ℂ :=
  ![q ^ 2, q * c, q * d, c ^ 2 - d * q, c * d - b * q, d ^ 2 - b * c]

/-- The six frontier determinants at size two.  This is the finite initial
state from which the transfer recurrence starts. -/
theorem continuantFrontierVector_two (d b c q : ℂ) :
    continuantFrontierVector 2 d b c q =
      continuantInitialVector d b c q := by
  funext s
  fin_cases s
  · change continuantFrontierDet 2 d b c q 0 = q ^ 2
    simp
  · change continuantFrontierDet 2 d b c q 1 = q * c
    simp
  · change continuantFrontierDet 2 d b c q 2 = q * d
    simp
  · change continuantFrontierDet 2 d b c q 3 = c ^ 2 - d * q
    simp
  · change continuantFrontierDet 2 d b c q 4 = c * d - b * q
    simp
  · change continuantFrontierDet 2 d b c q 5 = d ^ 2 - b * c
    simp

/-- From size three onward, the six frontier determinants evolve by the
fixed transfer matrix `continuantTransfer`. -/
theorem continuantFrontierVector_succ (m : ℕ) (d b c q : ℂ) :
    continuantFrontierVector (m + 3) d b c q =
      continuantTransfer d b c q *ᵥ continuantFrontierVector (m + 2) d b c q := by
  funext s
  simp only [continuantFrontierVector]
  fin_cases s
  · change continuantFrontierDet (m + 3) d b c q 0 =
      (continuantTransfer d b c q *ᵥ continuantFrontierVector (m + 2) d b c q) 0
    rw [continuantFrontierDet_zero_succ]
    simp [continuantFrontierVector, continuantTransfer, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
  · change continuantFrontierDet (m + 3) d b c q 1 =
      (continuantTransfer d b c q *ᵥ continuantFrontierVector (m + 2) d b c q) 1
    rw [continuantFrontierDet_one_succ]
    simp [continuantFrontierVector, continuantTransfer, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
  · change continuantFrontierDet (m + 3) d b c q 2 =
      (continuantTransfer d b c q *ᵥ continuantFrontierVector (m + 2) d b c q) 2
    rw [continuantFrontierDet_two_succ]
    simp [continuantFrontierVector, continuantTransfer, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
  · change continuantFrontierDet (m + 3) d b c q 3 =
      (continuantTransfer d b c q *ᵥ continuantFrontierVector (m + 2) d b c q) 3
    rw [continuantFrontierDet_three_succ]
    simp [continuantFrontierVector, continuantTransfer, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring
  · change continuantFrontierDet (m + 3) d b c q 4 =
      (continuantTransfer d b c q *ᵥ continuantFrontierVector (m + 2) d b c q) 4
    rw [continuantFrontierDet_four_succ]
    simp [continuantFrontierVector, continuantTransfer, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring
  · change continuantFrontierDet (m + 3) d b c q 5 =
      (continuantTransfer d b c q *ᵥ continuantFrontierVector (m + 2) d b c q) 5
    rw [continuantFrontierDet_five_succ]
    simp [continuantFrontierVector, continuantTransfer, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]
    ring

/-- The fifth row of the transfer matrix satisfies the characteristic
polynomial that yields the paper's sixth-order continuant recurrence. -/
theorem continuantTransfer_row_five_annihilation (d b c q : ℂ)
    (v : Fin 6 → ℂ) :
    ((continuantTransfer d b c q) ^ 6 *ᵥ v) 5 =
      d * (((continuantTransfer d b c q) ^ 5 *ᵥ v) 5) -
        (b * c - q ^ 2) *
          (((continuantTransfer d b c q) ^ 4 *ᵥ v) 5) -
        (2 * q ^ 2 * d - q * (b ^ 2 + c ^ 2)) *
          (((continuantTransfer d b c q) ^ 3 *ᵥ v) 5) -
        q ^ 2 * (b * c - q ^ 2) *
          (((continuantTransfer d b c q) ^ 2 *ᵥ v) 5) +
        q ^ 4 * d * ((continuantTransfer d b c q *ᵥ v) 5) -
        q ^ 6 * v 5 := by
  simp [continuantTransfer, pow_succ, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, Fin.sum_univ_succ]
  ring

/-- Iteration of the frontier transfer, based at size two. -/
theorem continuantFrontierVector_iterate (m k : ℕ) (d b c q : ℂ) :
    continuantFrontierVector (m + 2 + k) d b c q =
      (continuantTransfer d b c q) ^ k *ᵥ
        continuantFrontierVector (m + 2) d b c q := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show m + 2 + (k + 1) = (m + k) + 3 by omega,
        continuantFrontierVector_succ]
      rw [show m + k + 2 = m + 2 + k by omega, ih]
      rw [Matrix.mulVec_mulVec, ← pow_succ']

/-- Transfer-matrix formula for the ordinary Toeplitz determinant at every
size at least two. -/
theorem continuantFrontierDet_five_eq_transfer (k : ℕ) (d b c q : ℂ) :
    continuantFrontierDet (2 + k) d b c q 5 =
      (((continuantTransfer d b c q) ^ k) *ᵥ
        continuantInitialVector d b c q) 5 := by
  have h := congrFun (continuantFrontierVector_iterate 0 k d b c q) 5
  rw [continuantFrontierVector_two] at h
  simpa [continuantFrontierVector] using h

/-- Homogeneous sixth-order recurrence for the generic pure pentadiagonal
Toeplitz determinant, once all six prior sizes lie in the transfer regime. -/
theorem continuantFrontierDet_five_recurrence (m : ℕ) (d b c q : ℂ) :
    continuantFrontierDet (m + 8) d b c q 5 =
      d * continuantFrontierDet (m + 7) d b c q 5 -
        (b * c - q ^ 2) * continuantFrontierDet (m + 6) d b c q 5 -
        (2 * q ^ 2 * d - q * (b ^ 2 + c ^ 2)) *
          continuantFrontierDet (m + 5) d b c q 5 -
        q ^ 2 * (b * c - q ^ 2) *
          continuantFrontierDet (m + 4) d b c q 5 +
        q ^ 4 * d * continuantFrontierDet (m + 3) d b c q 5 -
        q ^ 6 * continuantFrontierDet (m + 2) d b c q 5 := by
  have h := continuantTransfer_row_five_annihilation d b c q
    (continuantFrontierVector (m + 2) d b c q)
  have h₁ :
      continuantTransfer d b c q *ᵥ continuantFrontierVector (m + 2) d b c q =
        continuantFrontierVector (m + 3) d b c q := by
    simpa using (continuantFrontierVector_iterate m 1 d b c q).symm
  rw [← continuantFrontierVector_iterate m 6 d b c q,
    ← continuantFrontierVector_iterate m 5 d b c q,
    ← continuantFrontierVector_iterate m 4 d b c q,
    ← continuantFrontierVector_iterate m 3 d b c q,
    ← continuantFrontierVector_iterate m 2 d b c q, h₁] at h
  simpa [continuantFrontierVector] using h

/-- The right-hand side of the finite sixth-order continuant recurrence,
with all negative-index values interpreted as zero. -/
def continuantRecurrenceRhs (T : ℕ → ℂ) (d b c q : ℂ) (k : ℕ) : ℂ :=
  d * lagWithZero T k 1 -
    (b * c - q ^ 2) * lagWithZero T k 2 -
    (2 * q ^ 2 * d - q * (b ^ 2 + c ^ 2)) * lagWithZero T k 3 -
    q ^ 2 * (b * c - q ^ 2) * lagWithZero T k 4 +
    q ^ 4 * d * lagWithZero T k 5 -
    q ^ 6 * lagWithZero T k 6 -
    q ^ 2 * if k = 2 then 1 else 0

private theorem continuantFrontierDet_five_recurrence_one (d b c q : ℂ) :
    continuantFrontierDet 1 d b c q 5 =
      continuantRecurrenceRhs
        (fun n => continuantFrontierDet n d b c q 5) d b c q 1 := by
  simp [continuantRecurrenceRhs, lagWithZero]

private theorem continuantFrontierDet_five_recurrence_two (d b c q : ℂ) :
    continuantFrontierDet 2 d b c q 5 =
      continuantRecurrenceRhs
        (fun n => continuantFrontierDet n d b c q 5) d b c q 2 := by
  simp [continuantRecurrenceRhs, lagWithZero]
  ring

private theorem continuantFrontierDet_five_recurrence_three (d b c q : ℂ) :
    continuantFrontierDet 3 d b c q 5 =
      continuantRecurrenceRhs
        (fun n => continuantFrontierDet n d b c q 5) d b c q 3 := by
  rw [show continuantFrontierDet 3 d b c q 5 =
      (((continuantTransfer d b c q) ^ 1) *ᵥ continuantInitialVector d b c q) 5 by
    simpa using continuantFrontierDet_five_eq_transfer 1 d b c q]
  rw [show (continuantTransfer d b c q) ^ 1 = continuantTransfer d b c q by simp]
  simp [continuantRecurrenceRhs, lagWithZero, continuantInitialVector,
    continuantTransfer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem continuantFrontierDet_five_recurrence_four (d b c q : ℂ) :
    continuantFrontierDet 4 d b c q 5 =
      continuantRecurrenceRhs
        (fun n => continuantFrontierDet n d b c q 5) d b c q 4 := by
  rw [show continuantFrontierDet 4 d b c q 5 =
      (((continuantTransfer d b c q) ^ 2) *ᵥ continuantInitialVector d b c q) 5 by
    simpa using continuantFrontierDet_five_eq_transfer 2 d b c q]
  have h₃ : continuantFrontierDet 3 d b c q 5 =
      (((continuantTransfer d b c q) ^ 1) *ᵥ continuantInitialVector d b c q) 5 := by
    simpa using continuantFrontierDet_five_eq_transfer 1 d b c q
  have hpow₂ : (continuantTransfer d b c q) ^ 2 =
      continuantTransfer d b c q * continuantTransfer d b c q := by
    exact pow_two _
  rw [hpow₂, ← Matrix.mulVec_mulVec]
  simp [continuantRecurrenceRhs, lagWithZero, h₃, continuantInitialVector,
    continuantTransfer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private theorem matrix_pow_succ_mulVec (A : Matrix (Fin 6) (Fin 6) ℂ)
    (v : Fin 6 → ℂ) (k : ℕ) :
    A ^ k.succ *ᵥ v = A *ᵥ (A ^ k *ᵥ v) := by
  rw [pow_succ', ← Matrix.mulVec_mulVec]

private theorem continuantFrontierDet_five_recurrence_five (d b c q : ℂ) :
    continuantFrontierDet 5 d b c q 5 =
      continuantRecurrenceRhs
        (fun n => continuantFrontierDet n d b c q 5) d b c q 5 := by
  rw [continuantFrontierDet_five_succ 2 d b c q,
    continuantFrontierDet_four_succ 1 d b c q,
    continuantFrontierDet_three_succ 1 d b c q,
    continuantFrontierDet_four_succ 0 d b c q,
    continuantFrontierDet_two_succ 0 d b c q,
    continuantFrontierDet_one_succ 0 d b c q,
    continuantFrontierDet_zero_succ 0 d b c q]
  simp only [continuantRecurrenceRhs, lagWithZero, Nat.reduceLeDiff,
    Nat.reduceEqDiff, ↓reduceIte]
  rw [continuantFrontierDet_five_succ 0 d b c q]
  rw [continuantFrontierDet_five_zero, continuantFrontierDet_five_one,
    continuantFrontierDet_one_two, continuantFrontierDet_two_two,
    continuantFrontierDet_three_two, continuantFrontierDet_four_two,
    continuantFrontierDet_five_two]
  ring

private theorem continuantFrontierDet_five_recurrence_six (d b c q : ℂ) :
    continuantFrontierDet 6 d b c q 5 =
      continuantRecurrenceRhs
        (fun n => continuantFrontierDet n d b c q 5) d b c q 6 := by
  rw [continuantFrontierDet_five_succ 3 d b c q,
    continuantFrontierDet_four_succ 2 d b c q,
    continuantFrontierDet_three_succ 2 d b c q,
    continuantFrontierDet_four_succ 1 d b c q,
    continuantFrontierDet_two_succ 1 d b c q,
    continuantFrontierDet_one_succ 1 d b c q,
    continuantFrontierDet_zero_succ 1 d b c q,
    continuantFrontierDet_four_succ 0 d b c q,
    continuantFrontierDet_two_succ 0 d b c q,
    continuantFrontierDet_one_succ 0 d b c q]
  simp only [continuantRecurrenceRhs, lagWithZero, Nat.reduceLeDiff,
    Nat.reduceEqDiff, ↓reduceIte]
  rw [continuantFrontierDet_five_recurrence_four]
  simp only [continuantRecurrenceRhs, lagWithZero, Nat.reduceLeDiff,
    Nat.reduceEqDiff, ↓reduceIte]
  rw [continuantFrontierDet_five_recurrence_three]
  simp only [continuantRecurrenceRhs, lagWithZero, Nat.reduceLeDiff,
    Nat.reduceEqDiff, ↓reduceIte]
  rw [continuantFrontierDet_five_zero, continuantFrontierDet_five_one,
    continuantFrontierDet_five_two]
  rw [continuantFrontierDet_one_two, continuantFrontierDet_two_two,
    continuantFrontierDet_four_two]
  ring

private theorem continuantFrontierDet_five_recurrence_seven (d b c q : ℂ) :
    continuantFrontierDet 7 d b c q 5 =
      continuantRecurrenceRhs
        (fun n => continuantFrontierDet n d b c q 5) d b c q 7 := by
  rw [continuantFrontierDet_five_succ 4 d b c q,
    continuantFrontierDet_four_succ 3 d b c q,
    continuantFrontierDet_three_succ 3 d b c q,
    continuantFrontierDet_four_succ 2 d b c q,
    continuantFrontierDet_two_succ 2 d b c q,
    continuantFrontierDet_one_succ 2 d b c q,
    continuantFrontierDet_zero_succ 2 d b c q,
    continuantFrontierDet_four_succ 1 d b c q,
    continuantFrontierDet_two_succ 1 d b c q,
    continuantFrontierDet_one_succ 1 d b c q,
    continuantFrontierDet_four_succ 0 d b c q,
    continuantFrontierDet_two_succ 0 d b c q,
    continuantFrontierDet_one_succ 0 d b c q]
  simp only [continuantRecurrenceRhs, lagWithZero, Nat.reduceLeDiff,
    Nat.reduceEqDiff, ↓reduceIte]
  rw [continuantFrontierDet_five_recurrence_five]
  simp only [continuantRecurrenceRhs, lagWithZero, Nat.reduceLeDiff,
    Nat.reduceEqDiff, ↓reduceIte]
  rw [continuantFrontierDet_five_recurrence_four]
  simp only [continuantRecurrenceRhs, lagWithZero, Nat.reduceLeDiff,
    Nat.reduceEqDiff, ↓reduceIte]
  rw [continuantFrontierDet_five_zero, continuantFrontierDet_five_one,
    continuantFrontierDet_five_two]
  rw [continuantFrontierDet_five_recurrence_three]
  simp only [continuantRecurrenceRhs, lagWithZero, Nat.reduceLeDiff,
    Nat.reduceEqDiff, ↓reduceIte]
  rw [continuantFrontierDet_five_zero, continuantFrontierDet_five_one,
    continuantFrontierDet_five_two]
  rw [continuantFrontierDet_one_two, continuantFrontierDet_two_two,
    continuantFrontierDet_four_two]
  ring

/-- Exact generic continuant recurrence for every positive size.  The
inhomogeneous term at size two is the finite-boundary correction. -/
theorem continuantFrontierDet_five_recurrence_all
    (k : ℕ) (d b c q : ℂ) (hk : 1 ≤ k) :
    continuantFrontierDet k d b c q 5 =
      continuantRecurrenceRhs
        (fun n => continuantFrontierDet n d b c q 5) d b c q k := by
  by_cases hsmall : k ≤ 7
  · interval_cases k
    · exact continuantFrontierDet_five_recurrence_one d b c q
    · exact continuantFrontierDet_five_recurrence_two d b c q
    · exact continuantFrontierDet_five_recurrence_three d b c q
    · exact continuantFrontierDet_five_recurrence_four d b c q
    · exact continuantFrontierDet_five_recurrence_five d b c q
    · exact continuantFrontierDet_five_recurrence_six d b c q
    · exact continuantFrontierDet_five_recurrence_seven d b c q
  · have hk₈ : 8 ≤ k := by omega
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 8 := ⟨k - 8, by omega⟩
    simpa [continuantRecurrenceRhs, lagWithZero] using
      continuantFrontierDet_five_recurrence m d b c q

/-- Equation `eq:T-recurrence` from the source, with `T_k = 0` for negative
indices encoded by `lagWithZero`.  The exceptional final term occurs only at
`k = 2`. -/
theorem verticalToeplitzDet_recurrence (k : ℕ) (a x Y t : ℝ) (hk : 1 ≤ k) :
    verticalToeplitzDet k a x Y t =
      (verticalToeplitzDiagonal a x Y t : ℂ) *
          lagWithZero (fun n => verticalToeplitzDet n a x Y t) k 1 -
        ((Complex.normSq (verticalToeplitzFirst a x Y) : ℂ) - (a : ℂ) ^ 2) *
          lagWithZero (fun n => verticalToeplitzDet n a x Y t) k 2 -
        (2 * (a : ℂ) ^ 2 * (verticalToeplitzDiagonal a x Y t : ℂ) -
            (a : ℂ) *
              ((verticalToeplitzFirst a x Y) ^ 2 +
                (star (verticalToeplitzFirst a x Y)) ^ 2)) *
          lagWithZero (fun n => verticalToeplitzDet n a x Y t) k 3 -
        (a : ℂ) ^ 2 *
          ((Complex.normSq (verticalToeplitzFirst a x Y) : ℂ) - (a : ℂ) ^ 2) *
          lagWithZero (fun n => verticalToeplitzDet n a x Y t) k 4 +
        (a : ℂ) ^ 4 * (verticalToeplitzDiagonal a x Y t : ℂ) *
          lagWithZero (fun n => verticalToeplitzDet n a x Y t) k 5 -
        (a : ℂ) ^ 6 *
          lagWithZero (fun n => verticalToeplitzDet n a x Y t) k 6 -
        (a : ℂ) ^ 2 * if k = 2 then 1 else 0 := by
  have h := continuantFrontierDet_five_recurrence_all k
    (verticalToeplitzDiagonal a x Y t : ℂ)
    (verticalToeplitzFirst a x Y) (star (verticalToeplitzFirst a x Y))
    (a : ℂ) hk
  simp only [continuantRecurrenceRhs] at h
  simp_rw [continuantFrontierDet_five_eq_verticalToeplitzDet] at h
  have hb : verticalToeplitzFirst a x Y * star (verticalToeplitzFirst a x Y) =
      (Complex.normSq (verticalToeplitzFirst a x Y) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  rw [hb] at h
  exact h

end

end ConnectedPseudospectrum
