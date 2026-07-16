import ConnectedPseudospectrum.VerticalGenerating
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Cofactor ratios in the vertical determinant argument

This module formalizes the deleted-principal-cofactor comparison and the
convolution absorption step in `lem:vertical`.
-/

namespace ConnectedPseudospectrum

open Matrix PowerSeries
open scoped ComplexOrder

noncomputable section

/-- Reindex the coordinates left after deleting the coordinate between a
left block of size `k` and a right block of size `j`. -/
def verticalDeletedEmbedding (k j : ℕ) : Fin k ⊕ Fin j → Fin (k + j + 1)
  | Sum.inl i => ⟨i.1, by omega⟩
  | Sum.inr i => ⟨k + 1 + i.1, by omega⟩

theorem verticalDeletedEmbedding_injective (k j : ℕ) :
    Function.Injective (verticalDeletedEmbedding k j) := by
  intro i q h
  cases i with
  | inl i =>
      cases q with
      | inl q =>
          simp only [verticalDeletedEmbedding, Fin.mk.injEq] at h
          exact congrArg Sum.inl (Fin.ext h)
      | inr q =>
          simp only [verticalDeletedEmbedding, Fin.mk.injEq] at h
          omega
  | inr i =>
      cases q with
      | inl q =>
          simp only [verticalDeletedEmbedding, Fin.mk.injEq] at h
          omega
      | inr q =>
          simp only [verticalDeletedEmbedding, Fin.mk.injEq] at h
          exact congrArg Sum.inr (Fin.ext (by omega))

/-- The two blocks left after deletion are coupled only through the original
second off-diagonal. -/
def verticalDeletedCoupledMatrix (p q : ℕ) (a x Y t : ℝ) :
    Matrix (Fin (p + 1) ⊕ Fin (q + 1)) (Fin (p + 1) ⊕ Fin (q + 1)) ℂ :=
  Matrix.fromBlocks
    (leadingCorrectedToeplitz (p + 1) a x Y t)
    (Matrix.single (Fin.last p) 0 (a : ℂ))
    (Matrix.single 0 (Fin.last p) (a : ℂ))
    (trailingCorrectedToeplitz (q + 1) a x Y t)

/-- The actual deleted principal submatrix of the vertical pencil has the
two-block form displayed in `eq:deleted-cofactor`. -/
theorem verticalPencil_deleted_submatrix_eq (p q : ℕ) (a x Y t : ℝ)
    (hY : 0 ≤ Y) :
    (verticalPencil ((p + 1) + (q + 1) + 1) a x Y t).submatrix
        (verticalDeletedEmbedding (p + 1) (q + 1))
        (verticalDeletedEmbedding (p + 1) (q + 1)) =
      verticalDeletedCoupledMatrix p q a x Y t := by
  ext i j
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          simp only [Matrix.submatrix_apply, verticalDeletedEmbedding,
            verticalDeletedCoupledMatrix, Matrix.fromBlocks_apply₁₁,
            leadingCorrectedToeplitz, Matrix.sub_apply, firstEndpointCorrection]
          rw [verticalPencil_apply_eq_verticalToeplitz_sub_endpoints
            (((p + 1) + (q + 1) + 1)) (by omega) a x Y t hY]
          rw [verticalToeplitz_apply, verticalToeplitz_apply]
          simp only [Fin.mk.injEq]
          have heq : (i.1 = j.1) ↔ i = j := by
            exact Fin.ext_iff.symm
          have hlast : i.1 + 1 ≠ (p + 1) + (q + 1) + 1 := by omega
          simp only [heq, hlast, and_false, if_false]
          ring
      | inr j =>
          simp only [Matrix.submatrix_apply, verticalDeletedEmbedding,
            verticalDeletedCoupledMatrix, Matrix.fromBlocks_apply₁₂]
          rw [verticalPencil_apply_eq_verticalToeplitz_sub_endpoints
            (((p + 1) + (q + 1) + 1)) (by omega) a x Y t hY]
          rw [verticalToeplitz_apply]
          simp only [Matrix.single_apply, Fin.mk.injEq]
          have hi := i.isLt
          have hj := j.isLt
          have hdiag : i.1 ≠ p + 1 + 1 + j.1 := by omega
          have hupOne : p + 1 + 1 + j.1 ≠ i.1 + 1 := by omega
          have hlowOne : i.1 ≠ p + 1 + 1 + j.1 + 1 := by omega
          have hupTwo :
              (p + 1 + 1 + j.1 = i.1 + 2) ↔
                (p = i.1 ∧ 0 = j.1) := by omega
          have hlowTwo : i.1 ≠ p + 1 + 1 + j.1 + 2 := by omega
          have hcouple :
              (p = i.1 ∧ 0 = j.1) ↔
                (Fin.last p = i ∧ (0 : Fin (q + 1)) = j) := by
            simp only [Fin.ext_iff, Fin.val_last, Fin.val_zero]
          simp only [hdiag, hupOne, hlowOne, hupTwo, hlowTwo,
            hcouple, false_and, if_false, mul_zero, add_zero, sub_zero]
          by_cases h : Fin.last p = i ∧ (0 : Fin (q + 1)) = j <;> simp [h]
  | inr i =>
      cases j with
      | inl j =>
          simp only [Matrix.submatrix_apply, verticalDeletedEmbedding,
            verticalDeletedCoupledMatrix, Matrix.fromBlocks_apply₂₁]
          rw [verticalPencil_apply_eq_verticalToeplitz_sub_endpoints
            (((p + 1) + (q + 1) + 1)) (by omega) a x Y t hY]
          rw [verticalToeplitz_apply]
          simp only [Matrix.single_apply, Fin.mk.injEq]
          have hi := i.isLt
          have hj := j.isLt
          have hdiag : p + 1 + 1 + i.1 ≠ j.1 := by omega
          have hupOne : j.1 ≠ p + 1 + 1 + i.1 + 1 := by omega
          have hlowOne : p + 1 + 1 + i.1 ≠ j.1 + 1 := by omega
          have hupTwo : j.1 ≠ p + 1 + 1 + i.1 + 2 := by omega
          have hlowTwo :
              (p + 1 + 1 + i.1 = j.1 + 2) ↔
                (0 = i.1 ∧ p = j.1) := by omega
          have hcouple :
              (0 = i.1 ∧ p = j.1) ↔
                ((0 : Fin (q + 1)) = i ∧ Fin.last p = j) := by
            simp only [Fin.ext_iff, Fin.val_last, Fin.val_zero]
          simp only [hdiag, hupOne, hlowOne, hupTwo, hlowTwo,
            hcouple, false_and, if_false, mul_zero, add_zero, sub_zero]
          by_cases h : (0 : Fin (q + 1)) = i ∧ Fin.last p = j <;> simp [h]
      | inr j =>
          simp only [Matrix.submatrix_apply, verticalDeletedEmbedding,
            verticalDeletedCoupledMatrix, Matrix.fromBlocks_apply₂₂,
            trailingCorrectedToeplitz, Matrix.sub_apply, lastEndpointCorrection]
          rw [verticalPencil_apply_eq_verticalToeplitz_sub_endpoints
            (((p + 1) + (q + 1) + 1)) (by omega) a x Y t hY]
          rw [verticalToeplitz_apply, verticalToeplitz_apply]
          simp only [Fin.mk.injEq]
          have hdiag :
              (p + 1 + 1 + i.1 = p + 1 + 1 + j.1) ↔ i = j := by
            constructor
            · intro h
              apply Fin.ext
              omega
            · intro h
              omega
          have hupOne :
              p + 1 + 1 + j.1 = p + 1 + 1 + i.1 + 1 ↔
                j.1 = i.1 + 1 := by omega
          have hlowOne :
              p + 1 + 1 + i.1 = p + 1 + 1 + j.1 + 1 ↔
                i.1 = j.1 + 1 := by omega
          have hupTwo :
              p + 1 + 1 + j.1 = p + 1 + 1 + i.1 + 2 ↔
                j.1 = i.1 + 2 := by omega
          have hlowTwo :
              p + 1 + 1 + i.1 = p + 1 + 1 + j.1 + 2 ↔
                i.1 = j.1 + 2 := by omega
          have hfirst :
              ¬(i = j ∧ p + 1 + 1 + i.1 = 0) := by omega
          have hlast :
              (i = j ∧ p + 1 + 1 + i.1 + 1 =
                  (p + 1) + (q + 1) + 1) ↔
                (i = j ∧ i.1 + 1 = q + 1) := by omega
          simp only [hdiag, hupOne, hlowOne, hupTwo, hlowTwo,
            hfirst, hlast, if_false]
          ring

/-- Removing the first coordinate of a last-endpoint-corrected Toeplitz
matrix preserves the same correction on the smaller last coordinate. -/
theorem trailingCorrectedToeplitz_submatrix_succ (q : ℕ) (a x Y t : ℝ) :
    (trailingCorrectedToeplitz (q + 1) a x Y t).submatrix Fin.succ Fin.succ =
      trailingCorrectedToeplitz q a x Y t := by
  ext i j
  simp only [trailingCorrectedToeplitz, Matrix.submatrix_apply,
    Matrix.sub_apply, lastEndpointCorrection, Fin.val_succ]
  rw [verticalToeplitz_apply, verticalToeplitz_apply]
  simp only [Fin.val_succ]
  have hdiag : (Fin.succ i = Fin.succ j) ↔ i = j := Fin.succ_inj
  have hupOne : j.1 + 1 = i.1 + 1 + 1 ↔ j.1 = i.1 + 1 := by omega
  have hlowOne : i.1 + 1 = j.1 + 1 + 1 ↔ i.1 = j.1 + 1 := by omega
  have hupTwo : j.1 + 1 = i.1 + 1 + 2 ↔ j.1 = i.1 + 2 := by omega
  have hlowTwo : i.1 + 1 = j.1 + 1 + 2 ↔ i.1 = j.1 + 2 := by omega
  have hlast :
      (i = j ∧ i.1 + 1 + 1 = q + 1) ↔ (i = j ∧ i.1 + 1 = q) := by
    omega
  simp only [hdiag, hupOne, hlowOne, hupTwo, hlowTwo, hlast]

/-- Multiplying the two one-entry coupling blocks through a square matrix
produces a single correction at the first coordinate of the right block. -/
theorem verticalCoupling_mul (p q : ℕ) (a : ℝ)
    (Linv : Matrix (Fin (p + 1)) (Fin (p + 1)) ℂ) :
    Matrix.single (0 : Fin (q + 1)) (Fin.last p) (a : ℂ) * Linv *
        Matrix.single (Fin.last p) (0 : Fin (q + 1)) (a : ℂ) =
      Matrix.single 0 0 ((a : ℂ) ^ 2 * Linv (Fin.last p) (Fin.last p)) := by
  ext i j
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      simp [Matrix.mul_apply, Matrix.single_apply]
      ring
    · have hj' : (0 : Fin (q + 1)) ≠ j := Ne.symm hj
      simp [Matrix.mul_apply, Matrix.single_apply, hj']
  · have hi' : (0 : Fin (q + 1)) ≠ i := Ne.symm hi
    simp [Matrix.mul_apply, Matrix.single_apply, hi']

/-- The bottom-right diagonal cofactor of the inverse of a positive
leading block, multiplied by its determinant, is the preceding leading
minor. -/
theorem det_mul_nonsingInv_last_last (p : ℕ) (a x Y t : ℝ)
    (hpos : (leadingCorrectedToeplitz (p + 1) a x Y t).PosDef) :
    (leadingCorrectedToeplitz (p + 1) a x Y t).det *
        (leadingCorrectedToeplitz (p + 1) a x Y t)⁻¹
          (Fin.last p) (Fin.last p) =
      (leadingCorrectedToeplitz p a x Y t).det := by
  let L := leadingCorrectedToeplitz (p + 1) a x Y t
  have hdet : L.det ≠ 0 := hpos.det_pos.ne'
  rw [Matrix.inv_def]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  rw [Fin.succAbove_last, leadingCorrectedToeplitz_submatrix_castSucc]
  rw [show ((-1 : ℂ) ^ ((Fin.last p : ℕ) + (Fin.last p : ℕ))) = 1 by
    rw [show (Fin.last p : ℕ) + (Fin.last p : ℕ) = 2 * p by
      simp only [Fin.val_last]
      omega]
    exact Even.neg_one_pow ⟨p, by omega⟩]
  rw [Ring.inverse_eq_inv]
  rw [one_mul, ← mul_assoc, mul_inv_cancel₀ hdet, one_mul]

/-- Determinant of the coupled block matrix.  The invertibility used in the
Schur complement is supplied by positivity of the leading block. -/
theorem det_verticalDeletedCoupledMatrix (p q : ℕ) (a x Y t : ℝ)
    (hpos : (leadingCorrectedToeplitz (p + 1) a x Y t).PosDef) :
    (verticalDeletedCoupledMatrix p q a x Y t).det =
      verticalLeadingMinor (p + 1) a x Y t *
          verticalTrailingMinor (q + 1) a x Y t -
        (a : ℂ) ^ 2 * verticalLeadingMinor p a x Y t *
          verticalTrailingMinor q a x Y t := by
  let L := leadingCorrectedToeplitz (p + 1) a x Y t
  let R := trailingCorrectedToeplitz (q + 1) a x Y t
  letI : Invertible L := hpos.isUnit.invertible
  rw [verticalDeletedCoupledMatrix, Matrix.det_fromBlocks₁₁]
  rw [verticalCoupling_mul]
  rw [Matrix.invOf_eq_nonsing_inv]
  rw [det_sub_single_diagonal]
  rw [Fin.succAbove_zero, trailingCorrectedToeplitz_submatrix_succ]
  rw [det_leadingCorrectedToeplitz, det_trailingCorrectedToeplitz,
    det_trailingCorrectedToeplitz]
  have hinv := det_mul_nonsingInv_last_last p a x Y t hpos
  calc
    verticalLeadingMinor (p + 1) a x Y t *
          (verticalTrailingMinor (q + 1) a x Y t -
            ((a : ℂ) ^ 2 * L⁻¹ (Fin.last p) (Fin.last p)) *
              verticalTrailingMinor q a x Y t) =
        verticalLeadingMinor (p + 1) a x Y t *
            verticalTrailingMinor (q + 1) a x Y t -
          (a : ℂ) ^ 2 *
            (verticalLeadingMinor (p + 1) a x Y t *
              L⁻¹ (Fin.last p) (Fin.last p)) *
            verticalTrailingMinor q a x Y t := by ring
    _ = verticalLeadingMinor (p + 1) a x Y t *
          verticalTrailingMinor (q + 1) a x Y t -
        (a : ℂ) ^ 2 * verticalLeadingMinor p a x Y t *
          verticalTrailingMinor q a x Y t := by
      rw [show verticalLeadingMinor (p + 1) a x Y t = L.det by
        simp [L, det_leadingCorrectedToeplitz], hinv,
        det_leadingCorrectedToeplitz p a x Y t]

/-- Positivity of any proper leading minor of a positive vertical pencil. -/
theorem verticalLeadingMinor_pos_of_lt (n k : ℕ) (hk : k < n)
    (a x Y t : ℝ) (hY : 0 ≤ Y)
    (hpos : (verticalPencil n a x Y t).PosDef) :
    0 < verticalLeadingMinor k a x Y t := by
  cases k with
  | zero => simp
  | succ k =>
      obtain ⟨q, hq⟩ : ∃ q : ℕ, n = (k + 1) + (q + 1) := by
        use n - (k + 1) - 1
        omega
      subst n
      exact verticalLeadingMinor_pos_of_posDef (k + 1) q (by omega)
        a x Y t hY hpos

/-- Positivity of any proper trailing minor of a positive vertical pencil. -/
theorem verticalTrailingMinor_pos_of_lt (n k : ℕ) (hk : k < n)
    (a x Y t : ℝ) (hY : 0 ≤ Y)
    (hpos : (verticalPencil n a x Y t).PosDef) :
    0 < verticalTrailingMinor k a x Y t := by
  cases k with
  | zero => simp
  | succ k =>
      obtain ⟨q, hq⟩ : ∃ q : ℕ, n = (q + 1) + (k + 1) := by
        use n - (k + 1) - 1
        omega
      subst n
      exact verticalTrailingMinor_pos_of_posDef (k + 1) q (by omega)
        a x Y t hY hpos

/-- The exact deleted-cofactor inequality `eq:deleted-cofactor`. -/
theorem vertical_deleted_cofactor_pos (p q : ℕ) (a x Y t : ℝ)
    (hY : 0 ≤ Y)
    (hpos : (verticalPencil ((p + 1) + (q + 1) + 1) a x Y t).PosDef) :
    0 < verticalLeadingMinor (p + 1) a x Y t *
          verticalTrailingMinor (q + 1) a x Y t -
        (a : ℂ) ^ 2 * verticalLeadingMinor p a x Y t *
          verticalTrailingMinor q a x Y t := by
  have hlead : (leadingCorrectedToeplitz (p + 1) a x Y t).PosDef := by
    have hpos' :
        (verticalPencil ((p + 1) + ((q + 1) + 1)) a x Y t).PosDef := by
      simpa only [Nat.add_assoc] using hpos
    have hsub := posDef_submatrix_of_injective
      (verticalPencil ((p + 1) + ((q + 1) + 1)) a x Y t) hpos'
      (Fin.castAdd ((q + 1) + 1))
      (Fin.castAdd_injective (p + 1) ((q + 1) + 1))
    rw [verticalPencil_leading_submatrix (p + 1) (q + 1) (by omega)
      a x Y t hY] at hsub
    exact hsub
  have hdet := det_submatrix_pos_of_posDef
    (verticalPencil ((p + 1) + (q + 1) + 1) a x Y t) hpos
    (verticalDeletedEmbedding (p + 1) (q + 1))
    (verticalDeletedEmbedding_injective (p + 1) (q + 1))
  rw [verticalPencil_deleted_submatrix_eq p q a x Y t hY,
    det_verticalDeletedCoupledMatrix p q a x Y t hlead] at hdet
  exact hdet

/-! ## The endpoint-minor relations -/

/-- Telescoping `D_k=T_k-T_{k-1}` recovers the Toeplitz continuant. -/
theorem verticalToeplitzDet_eq_sum_leading (k : ℕ) (a x Y t : ℝ) :
    verticalToeplitzDet k a x Y t =
      ∑ l ∈ Finset.range (k + 1), verticalLeadingMinor l a x Y t := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, verticalLeadingMinor_succ, ← ih]
      ring

/-- First identity in `eq:R-D-relation`. -/
theorem verticalTrailingMinor_eq_leading_add_sum (k : ℕ) (a x Y t : ℝ) :
    verticalTrailingMinor k a x Y t =
      verticalLeadingMinor k a x Y t +
        (1 - (a : ℂ) ^ 2) *
          ∑ l ∈ Finset.range k, verticalLeadingMinor l a x Y t := by
  cases k with
  | zero => simp
  | succ k =>
      rw [verticalTrailingMinor_succ, verticalLeadingMinor_succ,
        ← verticalToeplitzDet_eq_sum_leading k]
      ring

/-- Second identity in `eq:R-D-relation`. -/
theorem verticalTrailingMinor_sub_previous (k : ℕ) (a x Y t : ℝ) :
    verticalTrailingMinor (k + 1) a x Y t -
        verticalTrailingMinor k a x Y t =
      verticalLeadingMinor (k + 1) a x Y t -
        (a : ℂ) ^ 2 * verticalLeadingMinor k a x Y t := by
  rw [verticalTrailingMinor_eq_leading_add_sum (k + 1),
    verticalTrailingMinor_eq_leading_add_sum k, Finset.sum_range_succ]
  ring

/-- The positive factor used after the strict ratio alternative. -/
theorem verticalTrailingMinor_sub_sq_leading (k : ℕ) (a x Y t : ℝ) :
    verticalTrailingMinor k a x Y t -
        (a : ℂ) ^ 2 * verticalLeadingMinor k a x Y t =
      (1 - (a : ℂ) ^ 2) *
        ∑ l ∈ Finset.range (k + 1), verticalLeadingMinor l a x Y t := by
  rw [verticalTrailingMinor_eq_leading_add_sum,
    Finset.sum_range_succ]
  ring

private theorem complex_eq_coe_re_of_pos {z : ℂ} (hz : 0 < z) :
    z = (z.re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using (Complex.pos_iff.mp hz).2.symm

/-- The exact quotient inequalities in `eq:ratio-cross`.  Positivity of the
four denominators follows from positive definiteness of the full vertical
pencil. -/
theorem vertical_ratio_cross (p q : ℕ) (a x Y t : ℝ)
    (hY : 0 ≤ Y)
    (hpos : (verticalPencil ((p + 1) + (q + 1) + 1) a x Y t).PosDef) :
    a ^ 2 <
        (verticalLeadingMinor (p + 1) a x Y t).re /
            (verticalLeadingMinor p a x Y t).re *
          ((verticalTrailingMinor (q + 1) a x Y t).re /
            (verticalTrailingMinor q a x Y t).re) ∧
      a ^ 2 <
        (verticalLeadingMinor (q + 1) a x Y t).re /
            (verticalLeadingMinor q a x Y t).re *
          ((verticalTrailingMinor (p + 1) a x Y t).re /
            (verticalTrailingMinor p a x Y t).re) := by
  let n := (p + 1) + (q + 1) + 1
  let D : ℕ → ℝ := fun m => (verticalLeadingMinor m a x Y t).re
  let R : ℕ → ℝ := fun m => (verticalTrailingMinor m a x Y t).re
  have hDpos (m : ℕ) (hm : m < n) : 0 < D m :=
    (Complex.pos_iff.mp
      (verticalLeadingMinor_pos_of_lt n m hm a x Y t hY hpos)).1
  have hRpos (m : ℕ) (hm : m < n) : 0 < R m :=
    (Complex.pos_iff.mp
      (verticalTrailingMinor_pos_of_lt n m hm a x Y t hY hpos)).1
  have hDeq (m : ℕ) (hm : m < n) :
      verticalLeadingMinor m a x Y t = (D m : ℂ) :=
    complex_eq_coe_re_of_pos
      (verticalLeadingMinor_pos_of_lt n m hm a x Y t hY hpos)
  have hReq (m : ℕ) (hm : m < n) :
      verticalTrailingMinor m a x Y t = (R m : ℂ) :=
    complex_eq_coe_re_of_pos
      (verticalTrailingMinor_pos_of_lt n m hm a x Y t hY hpos)
  have hp : p < n := by dsimp [n]; omega
  have hp₁ : p + 1 < n := by dsimp [n]; omega
  have hq : q < n := by dsimp [n]; omega
  have hq₁ : q + 1 < n := by dsimp [n]; omega
  have hcross₁C := sub_pos.mp
    (vertical_deleted_cofactor_pos p q a x Y t hY hpos)
  have hcross₂C :
      (a : ℂ) ^ 2 * verticalLeadingMinor q a x Y t *
          verticalTrailingMinor p a x Y t <
        verticalLeadingMinor (q + 1) a x Y t *
          verticalTrailingMinor (p + 1) a x Y t := by
    have hs :
        (verticalPencil ((q + 1) + (p + 1) + 1) a x Y t).PosDef := by
      rw [show (q + 1) + (p + 1) + 1 =
        (p + 1) + (q + 1) + 1 by omega]
      exact hpos
    exact sub_pos.mp (vertical_deleted_cofactor_pos q p a x Y t hY hs)
  rw [hDeq p hp, hDeq (p + 1) hp₁, hReq q hq,
    hReq (q + 1) hq₁] at hcross₁C
  rw [hDeq q hq, hDeq (q + 1) hq₁, hReq p hp,
    hReq (p + 1) hp₁] at hcross₂C
  norm_cast at hcross₁C hcross₂C
  change a ^ 2 < D (p + 1) / D p * (R (q + 1) / R q) ∧
    a ^ 2 < D (q + 1) / D q * (R (p + 1) / R p)
  constructor
  · rw [div_mul_div_comm]
    exact (lt_div_iff₀ (mul_pos (hDpos p hp) (hRpos q hq))).2 (by
      simpa only [mul_assoc] using hcross₁C)
  · rw [div_mul_div_comm]
    exact (lt_div_iff₀ (mul_pos (hDpos q hq) (hRpos p hp))).2 (by
      simpa only [mul_assoc] using hcross₂C)

/-- Equation `eq:D-ratio-product`, stated without division.  Its hypotheses
are exactly positivity of the full vertical pencil and `0<a<1`. -/
theorem vertical_leading_ratio_product (p q : ℕ) (a x Y t : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hY : 0 ≤ Y)
    (hpos : (verticalPencil ((p + 1) + (q + 1) + 1) a x Y t).PosDef) :
    (a : ℂ) ^ 4 * verticalLeadingMinor p a x Y t *
        verticalLeadingMinor q a x Y t <
      verticalLeadingMinor (p + 1) a x Y t *
        verticalLeadingMinor (q + 1) a x Y t := by
  let n := (p + 1) + (q + 1) + 1
  let D : ℕ → ℝ := fun m => (verticalLeadingMinor m a x Y t).re
  let R : ℕ → ℝ := fun m => (verticalTrailingMinor m a x Y t).re
  have hDpos (m : ℕ) (hm : m < n) : 0 < D m :=
    (Complex.pos_iff.mp
      (verticalLeadingMinor_pos_of_lt n m hm a x Y t hY hpos)).1
  have hRpos (m : ℕ) (hm : m < n) : 0 < R m :=
    (Complex.pos_iff.mp
      (verticalTrailingMinor_pos_of_lt n m hm a x Y t hY hpos)).1
  have hDeq (m : ℕ) (hm : m < n) :
      verticalLeadingMinor m a x Y t = (D m : ℂ) :=
    complex_eq_coe_re_of_pos
      (verticalLeadingMinor_pos_of_lt n m hm a x Y t hY hpos)
  have hReq (m : ℕ) (hm : m < n) :
      verticalTrailingMinor m a x Y t = (R m : ℂ) :=
    complex_eq_coe_re_of_pos
      (verticalTrailingMinor_pos_of_lt n m hm a x Y t hY hpos)
  have hp : p < n := by dsimp [n]; omega
  have hp₁ : p + 1 < n := by dsimp [n]; omega
  have hq : q < n := by dsimp [n]; omega
  have hq₁ : q + 1 < n := by dsimp [n]; omega
  have hcross₁C := (sub_pos.mp
    (vertical_deleted_cofactor_pos p q a x Y t hY hpos))
  have hcross₂C :
      (a : ℂ) ^ 2 * verticalLeadingMinor q a x Y t *
          verticalTrailingMinor p a x Y t <
        verticalLeadingMinor (q + 1) a x Y t *
          verticalTrailingMinor (p + 1) a x Y t := by
    have hs :
        (verticalPencil ((q + 1) + (p + 1) + 1) a x Y t).PosDef := by
      rw [show (q + 1) + (p + 1) + 1 =
        (p + 1) + (q + 1) + 1 by omega]
      exact hpos
    exact sub_pos.mp (vertical_deleted_cofactor_pos q p a x Y t hY hs)
  rw [hDeq p hp, hDeq (p + 1) hp₁, hReq q hq,
    hReq (q + 1) hq₁] at hcross₁C
  rw [hDeq q hq, hDeq (q + 1) hq₁, hReq p hp,
    hReq (p + 1) hp₁] at hcross₂C
  rw [hDeq p hp, hDeq (p + 1) hp₁, hDeq q hq,
    hDeq (q + 1) hq₁]
  norm_cast at hcross₁C hcross₂C ⊢
  have hdiffpC := verticalTrailingMinor_sub_previous p a x Y t
  have hdiffqC := verticalTrailingMinor_sub_previous q a x Y t
  rw [hDeq p hp, hDeq (p + 1) hp₁, hReq p hp,
    hReq (p + 1) hp₁] at hdiffpC
  rw [hDeq q hq, hDeq (q + 1) hq₁, hReq q hq,
    hReq (q + 1) hq₁] at hdiffqC
  norm_cast at hdiffpC hdiffqC
  have hbasepC :
      0 < verticalTrailingMinor p a x Y t -
        (a : ℂ) ^ 2 * verticalLeadingMinor p a x Y t := by
    rw [verticalTrailingMinor_sub_sq_leading]
    apply mul_pos
    · norm_cast
      have hprod : 0 < (1 - a) * (1 + a) :=
        mul_pos (sub_pos.mpr ha₁) (by linarith)
      nlinarith
    · apply Finset.sum_pos
      · intro m hm
        exact verticalLeadingMinor_pos_of_lt n m (by
          simp only [Finset.mem_range] at hm
          simp [n]
          omega) a x Y t hY hpos
      · simp
  have hbaseqC :
      0 < verticalTrailingMinor q a x Y t -
        (a : ℂ) ^ 2 * verticalLeadingMinor q a x Y t := by
    rw [verticalTrailingMinor_sub_sq_leading]
    apply mul_pos
    · norm_cast
      have hprod : 0 < (1 - a) * (1 + a) :=
        mul_pos (sub_pos.mpr ha₁) (by linarith)
      nlinarith
    · apply Finset.sum_pos
      · intro m hm
        exact verticalLeadingMinor_pos_of_lt n m (by
          simp only [Finset.mem_range] at hm
          simp [n]
          omega) a x Y t hY hpos
      · simp
  rw [hDeq p hp, hReq p hp] at hbasepC
  rw [hDeq q hq, hReq q hq] at hbaseqC
  norm_cast at hbasepC hbaseqC
  have halt : a ^ 2 * D p < D (p + 1) ∨
      a ^ 2 * D q < D (q + 1) := by
    by_cases hpLe : D (p + 1) ≤ a ^ 2 * D p
    · right
      apply lt_of_not_ge
      intro hqLe
      have hrp : R (p + 1) ≤ R p := by linarith
      have hrq : R (q + 1) ≤ R q := by linarith
      have hfirst : D (p + 1) * R (q + 1) ≤
          a ^ 2 * D p * R (q + 1) :=
        mul_le_mul_of_nonneg_right hpLe (hRpos (q + 1) hq₁).le
      have hsecond : a ^ 2 * D p * R (q + 1) ≤
          a ^ 2 * D p * R q :=
        mul_le_mul_of_nonneg_left hrq
          (mul_nonneg (sq_nonneg a) (hDpos p hp).le)
      exact (not_lt_of_ge (hfirst.trans hsecond)) hcross₁C
    · left
      exact lt_of_not_ge hpLe
  rcases halt with hpStrict | hqStrict
  · have hcompare : a ^ 2 * D p * R (p + 1) <
        D (p + 1) * R p := by
      rw [← sub_pos]
      calc
        D (p + 1) * R p - a ^ 2 * D p * R (p + 1) =
            (D (p + 1) - a ^ 2 * D p) *
              (R p - a ^ 2 * D p) := by
                rw [show R (p + 1) =
                  R p + D (p + 1) - a ^ 2 * D p by linarith]
                ring
        _ > 0 := mul_pos (sub_pos.mpr hpStrict) hbasepC
    have hchain :
        (a ^ 4 * D p * D q) * R p <
          (D (p + 1) * D (q + 1)) * R p := calc
      (a ^ 4 * D p * D q) * R p =
          (a ^ 2 * D p) * (a ^ 2 * D q * R p) := by ring
      _ < (a ^ 2 * D p) * (D (q + 1) * R (p + 1)) :=
        mul_lt_mul_of_pos_left hcross₂C
          (mul_pos (sq_pos_of_pos ha₀) (hDpos p hp))
      _ = D (q + 1) * (a ^ 2 * D p * R (p + 1)) := by ring
      _ < D (q + 1) * (D (p + 1) * R p) :=
        mul_lt_mul_of_pos_left hcompare (hDpos (q + 1) hq₁)
      _ = (D (p + 1) * D (q + 1)) * R p := by ring
    exact lt_of_mul_lt_mul_right hchain (hRpos p hp).le
  · have hcompare : a ^ 2 * D q * R (q + 1) <
        D (q + 1) * R q := by
      rw [← sub_pos]
      calc
        D (q + 1) * R q - a ^ 2 * D q * R (q + 1) =
            (D (q + 1) - a ^ 2 * D q) *
              (R q - a ^ 2 * D q) := by
                rw [show R (q + 1) =
                  R q + D (q + 1) - a ^ 2 * D q by linarith]
                ring
        _ > 0 := mul_pos (sub_pos.mpr hqStrict) hbaseqC
    have hchain :
        (a ^ 4 * D p * D q) * R q <
          (D (p + 1) * D (q + 1)) * R q := calc
      (a ^ 4 * D p * D q) * R q =
          (a ^ 2 * D q) * (a ^ 2 * D p * R q) := by ring
      _ < (a ^ 2 * D q) * (D (p + 1) * R (q + 1)) :=
        mul_lt_mul_of_pos_left hcross₁C
          (mul_pos (sq_pos_of_pos ha₀) (hDpos q hq))
      _ = D (p + 1) * (a ^ 2 * D q * R (q + 1)) := by ring
      _ < D (p + 1) * (D (q + 1) * R q) :=
        mul_lt_mul_of_pos_left hcompare (hDpos (p + 1) hp₁)
      _ = (D (p + 1) * D (q + 1)) * R q := by ring
    exact lt_of_mul_lt_mul_right hchain (hRpos q hq).le

/-! ## Absorption by the leading-minor convolution -/

/-- Every convolution strictly below the full pencil dimension is positive. -/
theorem verticalLeadingConvolution_pos_of_posDef (n m : ℕ) (hm : m < n)
    (a x Y t : ℝ) (hY : 0 ≤ Y)
    (hpos : (verticalPencil n a x Y t).PosDef) :
    0 < verticalLeadingConvolution m a x Y t := by
  rw [verticalLeadingConvolution]
  apply Finset.sum_pos
  · intro j hj
    simp only [Finset.mem_range] at hj
    apply mul_pos
    · exact verticalLeadingMinor_pos_of_lt n j (by omega) a x Y t hY hpos
    · exact verticalLeadingMinor_pos_of_lt n (m - j) (by omega)
        a x Y t hY hpos
  · simp

/-- Split the convolution into its two positive endpoints and the interior
sum used in `eq:u-absorption`. -/
theorem verticalLeadingConvolution_add_two (m : ℕ) (a x Y t : ℝ) :
    verticalLeadingConvolution (m + 2) a x Y t =
      (∑ p ∈ Finset.range (m + 1),
          verticalLeadingMinor (p + 1) a x Y t *
            verticalLeadingMinor (m + 1 - p) a x Y t) +
        2 * verticalLeadingMinor (m + 2) a x Y t := by
  rw [verticalLeadingConvolution]
  rw [show m + 2 + 1 = (m + 2) + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ']
  have hinner :
      (∑ p ∈ Finset.range (m + 1),
          verticalLeadingMinor (p + 1) a x Y t *
            verticalLeadingMinor (m + 2 - (p + 1)) a x Y t) =
        ∑ p ∈ Finset.range (m + 1),
          verticalLeadingMinor (p + 1) a x Y t *
            verticalLeadingMinor (m + 1 - p) a x Y t := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [Finset.mem_range] at hp
    rw [show m + 2 - (p + 1) = m + 1 - p by omega]
  rw [hinner]
  simp only [verticalLeadingMinor_zero, Nat.sub_zero, Nat.sub_self,
    mul_one, one_mul]
  ring

/-- Equation `eq:u-absorption`: `u_{n-1}>a⁴u_{n-3}` for `n≥3`. -/
theorem verticalLeadingConvolution_absorption (m : ℕ) (a x Y t : ℝ)
    (ha₀ : 0 < a) (ha₁ : a < 1) (hY : 0 ≤ Y)
    (hpos : (verticalPencil (m + 3) a x Y t).PosDef) :
    (a : ℂ) ^ 4 * verticalLeadingConvolution m a x Y t <
      verticalLeadingConvolution (m + 2) a x Y t := by
  have hsum :
      (a : ℂ) ^ 4 * verticalLeadingConvolution m a x Y t <
        ∑ p ∈ Finset.range (m + 1),
          verticalLeadingMinor (p + 1) a x Y t *
            verticalLeadingMinor (m + 1 - p) a x Y t := by
    rw [verticalLeadingConvolution, Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty (by simp)
    intro p hp
    simp only [Finset.mem_range] at hp
    have hpLe : p ≤ m := by omega
    have hpos' :
        (verticalPencil ((p + 1) + ((m - p) + 1) + 1) a x Y t).PosDef := by
      rw [show (p + 1) + ((m - p) + 1) + 1 = m + 3 by omega]
      exact hpos
    have hr := vertical_leading_ratio_product p (m - p) a x Y t
      ha₀ ha₁ hY hpos'
    simpa only [mul_assoc, show m - p + 1 = m + 1 - p by omega] using hr
  rw [verticalLeadingConvolution_add_two]
  exact hsum.trans (lt_add_of_pos_right _ (mul_pos (by norm_num)
    (verticalLeadingMinor_pos_of_lt (m + 3) (m + 2) (by omega)
      a x Y t hY hpos)))

/-! ## Positivity of the determinant derivative -/

/-- The exact coefficient on the right of `eq:F-prime-convolution` is
strictly positive whenever the corresponding vertical pencil is positive
definite.  Together with `hasDerivWithinAt_verticalPencilDet_convolution`,
this is `eq:det-derivative-positive`. -/
theorem coeff_verticalPencilYDerivativeSeries_pos (n : ℕ) (hn : 0 < n)
    (a x Y t : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hY : 0 ≤ Y)
    (hpos : (verticalPencil n a x Y t).PosDef) :
    0 < coeff n (verticalPencilYDerivativeSeries a x Y t) := by
  cases n with
  | zero => omega
  | succ n =>
      cases n with
      | zero =>
          rw [coeff_verticalPencilYDerivativeSeries]
          norm_num [lagWithZero, verticalLeadingConvolution]
      | succ n =>
          cases n with
          | zero =>
              have hD₁ := verticalLeadingMinor_pos_of_lt 2 1 (by omega)
                a x Y t hY hpos
              have hc : 0 < 2 * (a : ℂ) * (1 - (a : ℂ)) := by
                norm_cast
                exact mul_pos (mul_pos (by norm_num) ha₀) (sub_pos.mpr ha₁)
              rw [coeff_verticalPencilYDerivativeSeries]
              simp only [lagWithZero, if_pos (by omega : 1 ≤ 2),
                if_pos (by omega : 2 ≤ 2), if_neg (by omega : ¬3 ≤ 2)]
              norm_num [verticalLeadingConvolution]
              exact add_pos
                (add_pos (by simpa using hD₁) (by simpa using hD₁)) hc
          | succ m =>
              let u : ℕ → ℂ := fun k =>
                verticalLeadingConvolution k a x Y t
              have hu (k : ℕ) (hk : k < m + 3) : 0 < u k :=
                verticalLeadingConvolution_pos_of_posDef (m + 3) k hk
                  a x Y t hY hpos
              have habs : (a : ℂ) ^ 4 * u m < u (m + 2) :=
                verticalLeadingConvolution_absorption m a x Y t
                  ha₀ ha₁ hY hpos
              have htail :
                  0 ≤ ∑ k ∈ Finset.Icc 4 (m + 3),
                    (a : ℂ) ^ (k - 1) * u (m + 3 - k) := by
                apply Finset.sum_nonneg
                intro k hk
                have hkIcc := Finset.mem_Icc.mp hk
                apply mul_nonneg
                · exact pow_nonneg (le_of_lt (by exact_mod_cast ha₀)) _
                · exact (hu (m + 3 - k) (by omega)).le
              have hsecond :
                  0 ≤ (2 * (a : ℂ) * (1 - (a : ℂ))) * u (m + 1) := by
                exact (mul_pos (by
                  norm_cast
                  exact mul_pos (mul_pos (by norm_num) ha₀)
                    (sub_pos.mpr ha₁)) (hu (m + 1) (by omega))).le
              have htailTerm :
                  0 ≤ 2 * (1 - (a : ℂ)) ^ 2 *
                    ∑ k ∈ Finset.Icc 4 (m + 3),
                      (a : ℂ) ^ (k - 1) * u (m + 3 - k) := by
                apply mul_nonneg
                · exact_mod_cast (show 0 ≤ 2 * (1 - a) ^ 2 by positivity)
                · exact htail
              have hcore :
                  0 < u (m + 2) +
                    ((a : ℂ) ^ 2 *
                      ((a : ℂ) ^ 2 - 4 * (a : ℂ) + 2)) * u m := by
                by_cases hc :
                    0 ≤ a ^ 2 * (a ^ 2 - 4 * a + 2)
                · apply add_pos_of_pos_of_nonneg (hu (m + 2) (by omega))
                  apply mul_nonneg
                  · norm_cast
                  · exact (hu m (by omega)).le
                · let B : ℝ := -(a ^ 2 * (a ^ 2 - 4 * a + 2))
                  have hBlt : B < a ^ 4 := by
                    rw [← sub_pos]
                    calc
                      a ^ 4 - B = 2 * a ^ 2 * (1 - a) ^ 2 := by
                        dsimp [B]
                        ring
                      _ > 0 := mul_pos
                        (mul_pos (by norm_num) (sq_pos_of_pos ha₀))
                        (sq_pos_of_pos (sub_pos.mpr ha₁))
                  have hBltC : (B : ℂ) < (a : ℂ) ^ 4 := by
                    exact_mod_cast hBlt
                  have hmul : (B : ℂ) * u m < u (m + 2) :=
                    (mul_lt_mul_of_pos_right hBltC (hu m (by omega))).trans habs
                  have hcEq :
                      (a : ℂ) ^ 2 *
                          ((a : ℂ) ^ 2 - 4 * (a : ℂ) + 2) =
                        -(B : ℂ) := by
                    dsimp [B]
                    push_cast
                    ring
                  rw [hcEq]
                  have hsub : 0 < u (m + 2) - (B : ℂ) * u m :=
                    sub_pos.mpr hmul
                  convert hsub using 1
                  all_goals ring
              have htotal :
                  0 < u (m + 2) +
                      (2 * (a : ℂ) * (1 - (a : ℂ))) * u (m + 1) +
                      ((a : ℂ) ^ 2 *
                        ((a : ℂ) ^ 2 - 4 * (a : ℂ) + 2)) * u m +
                    2 * (1 - (a : ℂ)) ^ 2 *
                      ∑ k ∈ Finset.Icc 4 (m + 3),
                        (a : ℂ) ^ (k - 1) * u (m + 3 - k) := by
                have := add_pos_of_pos_of_nonneg
                  (add_pos_of_pos_of_nonneg hcore hsecond) htailTerm
                convert this using 1
                all_goals ring
              rw [coeff_verticalPencilYDerivativeSeries]
              simpa [u, lagWithZero] using htotal

/-- The analytic derivative and its strict positivity, bundled in the form
used by the continuation argument. -/
theorem hasDerivWithinAt_verticalPencilDet_pos (n : ℕ) (hn : 0 < n)
    (a x Y t : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) (hY : 0 ≤ Y)
    (hpos : (verticalPencil n a x Y t).PosDef) :
    HasDerivWithinAt (fun Y' : ℝ => verticalPencilDet n a x Y' t)
        (coeff n (verticalPencilYDerivativeSeries a x Y t)) (Set.Ici 0) Y ∧
      0 < coeff n (verticalPencilYDerivativeSeries a x Y t) :=
  ⟨hasDerivWithinAt_verticalPencilDet n a x Y t hY,
    coeff_verticalPencilYDerivativeSeries_pos n hn a x Y t
      ha₀ ha₁ hY hpos⟩


end

end ConnectedPseudospectrum
