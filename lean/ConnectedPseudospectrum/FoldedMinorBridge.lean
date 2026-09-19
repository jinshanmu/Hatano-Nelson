import ConnectedPseudospectrum.SignedPencil
import ConnectedPseudospectrum.FoldedGenerating
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# Actual folded signed-pencil matrices and exposed minors

This module connects the five-minor iteration to the determinants of the
actual signed pencils.  The coordinate equivalences below implement the order
`(1,n),(2,n-1),...` used in the proof of `lem:mesh`.
-/

namespace ConnectedPseudospectrum

open Matrix

noncomputable section

/-- A two-sided pair is the sum of its left and right coordinates. -/
def pairSumEquiv (m : ℕ) : Fin m × Fin 2 ≃ Fin m ⊕ Fin m where
  toFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  invFun q := Sum.elim (fun i ↦ (i, 0)) (fun i ↦ (i, 1)) q
  left_inv p := by
    rcases p with ⟨i, j⟩
    fin_cases j <;> rfl
  right_inv q := by
    rcases q with i | i <;> rfl

@[simp] theorem pairSumEquiv_apply_zero (m : ℕ) (i : Fin m) :
    pairSumEquiv m (i, 0) = Sum.inl i := rfl

@[simp] theorem pairSumEquiv_apply_one (m : ℕ) (i : Fin m) :
    pairSumEquiv m (i, 1) = Sum.inr i := rfl

/-- The even paired-coordinate equivalence.  Block `i` contains original
coordinates `i` and `2m-1-i` (zero-based). -/
def evenPairCoordinateEquiv (m : ℕ) : Fin m × Fin 2 ≃ Fin (2 * m) :=
  (pairSumEquiv m).trans <|
    (Equiv.sumCongr (Equiv.refl (Fin m)) (@Fin.revPerm m)).trans <|
      (@finSumFinEquiv m m).trans (finCongr (by omega))

@[simp] theorem evenPairCoordinateEquiv_zero_val (m : ℕ) (i : Fin m) :
    (evenPairCoordinateEquiv m (i, 0)).1 = i.1 := by
  simp [evenPairCoordinateEquiv]

@[simp] theorem evenPairCoordinateEquiv_one_val (m : ℕ) (i : Fin m) :
    (evenPairCoordinateEquiv m (i, 1)).1 = 2 * m - 1 - i.1 := by
  simp [evenPairCoordinateEquiv, Fin.val_rev]
  omega

/-- The odd paired-coordinate equivalence.  The sum's final `Fin 1` is the
unpaired central coordinate. -/
def oddPairCoordinateEquiv (m : ℕ) :
    (Fin m × Fin 2) ⊕ Fin 1 ≃ Fin (2 * m + 1) :=
  (Equiv.sumCongr (pairSumEquiv m) (Equiv.refl (Fin 1))).trans <|
    (Equiv.sumAssoc (Fin m) (Fin m) (Fin 1)).trans <|
      (Equiv.sumCongr (Equiv.refl (Fin m))
        (Equiv.sumComm (Fin m) (Fin 1))).trans <|
        (Equiv.sumCongr (Equiv.refl (Fin m))
          (Equiv.sumCongr (Equiv.refl (Fin 1)) (@Fin.revPerm m))).trans <|
          (Equiv.sumCongr (Equiv.refl (Fin m))
            (@finSumFinEquiv 1 m)).trans <|
            (@finSumFinEquiv m (1 + m)).trans (finCongr (by omega))

@[simp] theorem oddPairCoordinateEquiv_zero_val (m : ℕ) (i : Fin m) :
    (oddPairCoordinateEquiv m (Sum.inl (i, 0))).1 = i.1 := by
  simp [oddPairCoordinateEquiv]

@[simp] theorem oddPairCoordinateEquiv_one_val (m : ℕ) (i : Fin m) :
    (oddPairCoordinateEquiv m (Sum.inl (i, 1))).1 = 2 * m - i.1 := by
  simp [oddPairCoordinateEquiv, Fin.val_rev]
  omega

@[simp] theorem oddPairCoordinateEquiv_center_val (m : ℕ) (i : Fin 1) :
    (oddPairCoordinateEquiv m (Sum.inr i)).1 = m := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [oddPairCoordinateEquiv]

/-- Linearize the even paired blocks, so the exposed pair has indices `0,1`. -/
def evenPairedPermutation (m : ℕ) : Fin (2 * m) ≃ Fin (2 * m) :=
  (finCongr (by omega : 2 * m = m * 2)).trans
    (@finProdFinEquiv m 2).symm |>.trans (evenPairCoordinateEquiv m)

/-- Linearize the odd paired blocks followed by the central coordinate. -/
def oddPairedPermutation (m : ℕ) : Fin (2 * m + 1) ≃ Fin (2 * m + 1) :=
  (finCongr (by omega : 2 * m + 1 = m * 2 + 1)).trans
    (@finSumFinEquiv (m * 2) 1).symm |>.trans
      (Equiv.sumCongr (@finProdFinEquiv m 2).symm (Equiv.refl (Fin 1))) |>.trans
        (oddPairCoordinateEquiv m)

/-- The actual even signed-middle pencil after simultaneous paired
permutation.  This is the paper's `K_m^e`. -/
def foldedEvenPencilMatrix (m : ℕ) (a x s : ℝ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  (signedMiddleMatrix (2 * m) a x - s • 1).submatrix
    (evenPairedPermutation m) (evenPairedPermutation m)

/-- The actual odd signed-middle pencil after simultaneous paired
permutation.  This is the paper's `K_m^o`. -/
def foldedOddPencilMatrix (m : ℕ) (a x s : ℝ) :
    Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
  (signedMiddleMatrix (2 * m + 1) a x - s • 1).submatrix
    (oddPairedPermutation m) (oddPairedPermutation m)

/-- Simultaneous paired permutation preserves the even determinant. -/
theorem foldedEvenPencilMatrix_det (m : ℕ) (a x s : ℝ) :
    (foldedEvenPencilMatrix m a x s).det =
      (signedMiddleMatrix (2 * m) a x - s • 1).det := by
  exact Matrix.det_submatrix_equiv_self _ _

/-- Simultaneous paired permutation preserves the odd determinant. -/
theorem foldedOddPencilMatrix_det (m : ℕ) (a x s : ℝ) :
    (foldedOddPencilMatrix m a x s).det =
      (signedMiddleMatrix (2 * m + 1) a x - s • 1).det := by
  exact Matrix.det_submatrix_equiv_self _ _

/-- Removing the first row and the last column of reversal leaves the
previous reversal matrix. -/
theorem reversal_delete_first_last (n : ℕ) :
    (reversal (n + 1)).submatrix Fin.succ (Fin.last n).succAbove =
      reversal n := by
  ext i j
  simp only [Matrix.submatrix_apply, reversal_apply, Fin.val_succ]
  have hj : ((Fin.last n).succAbove j).1 = j.1 := by
    rw [Fin.succAbove_of_castSucc_lt]
    · rfl
    · simp
  rw [hj]
  by_cases h : i.1 + j.1 + 1 = n
  · have h' : i.1 + 1 + j.1 + 1 = n + 1 := by omega
    rw [if_pos h, if_pos h']
  · have h' : i.1 + 1 + j.1 + 1 ≠ n + 1 := by omega
    rw [if_neg h, if_neg h']

/-- Laplace expansion gives the reversal-determinant recurrence. -/
theorem det_reversal_succ (n : ℕ) :
    (reversal (n + 1)).det = (-1 : ℝ) ^ n * (reversal n).det := by
  rw [Matrix.det_succ_row_zero]
  classical
  rw [Finset.sum_eq_single (Fin.last n)]
  · rw [reversal_delete_first_last]
    simp [reversal_apply]
  · intro j _ hj
    have hjval : j.1 ≠ n := by
      intro h
      apply hj
      exact Fin.ext h
    simp [reversal_apply, hjval]
  · simp

/-- Two successive reversal sizes change the determinant sign. -/
theorem det_reversal_add_two (n : ℕ) :
    (reversal (n + 2)).det = -(reversal n).det := by
  rw [show n + 2 = (n + 1) + 1 by omega, det_reversal_succ,
    det_reversal_succ]
  ring_nf
  simp

/-- Exact even reversal sign from the paper. -/
theorem det_reversal_even (m : ℕ) :
    (reversal (2 * m)).det = (-1 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, det_reversal_add_two, ih,
        pow_succ]
      ring

/-- Exact odd reversal sign from the paper. -/
theorem det_reversal_odd (m : ℕ) :
    (reversal (2 * m + 1)).det = (-1 : ℝ) ^ m := by
  rw [show 2 * m + 1 = 2 * m + 1 by rfl, det_reversal_succ,
    det_reversal_even]
  have heven : Even (2 * m) := ⟨m, by omega⟩
  rw [heven.neg_one_pow]
  simp

/-- The first signed even minor is exactly the signed-pencil determinant. -/
theorem signedPencilDet_even_eq_signed_folded_det (m : ℕ) (a x s : ℝ) :
    signedPencilDet (2 * m) a x s =
      (-1 : ℝ) ^ m * (foldedEvenPencilMatrix m a x s).det := by
  have h := signedPencilDet_mul_det_reversal (2 * m) a x s
  rw [det_reversal_even, ← foldedEvenPencilMatrix_det] at h
  have hsq : ((-1 : ℝ) ^ m) * ((-1 : ℝ) ^ m) = 1 := by
    rw [← pow_add]
    exact (Even.add_self m).neg_one_pow
  calc
    signedPencilDet (2 * m) a x s =
        (signedPencilDet (2 * m) a x s * (-1 : ℝ) ^ m) *
          (-1 : ℝ) ^ m := by rw [mul_assoc, hsq, mul_one]
    _ = (-1 : ℝ) ^ m * (foldedEvenPencilMatrix m a x s).det := by
      rw [h]
      ring

/-- The first signed odd minor is exactly the signed-pencil determinant. -/
theorem signedPencilDet_odd_eq_signed_folded_det (m : ℕ) (a x s : ℝ) :
    signedPencilDet (2 * m + 1) a x s =
      (-1 : ℝ) ^ m * (foldedOddPencilMatrix m a x s).det := by
  have h := signedPencilDet_mul_det_reversal (2 * m + 1) a x s
  rw [det_reversal_odd, ← foldedOddPencilMatrix_det] at h
  have hsq : ((-1 : ℝ) ^ m) * ((-1 : ℝ) ^ m) = 1 := by
    rw [← pow_add]
    exact (Even.add_self m).neg_one_pow
  calc
    signedPencilDet (2 * m + 1) a x s =
        (signedPencilDet (2 * m + 1) a x s * (-1 : ℝ) ^ m) *
          (-1 : ℝ) ^ m := by rw [mul_assoc, hsq, mul_one]
    _ = (-1 : ℝ) ^ m * (foldedOddPencilMatrix m a x s).det := by
      rw [h]
      ring

@[simp] theorem evenPairedPermutation_one_zero :
    evenPairedPermutation 1 (0 : Fin 2) = 0 := by
  decide

@[simp] theorem evenPairedPermutation_one_one :
    evenPairedPermutation 1 (1 : Fin 2) = 1 := by
  decide

@[simp] theorem oddPairedPermutation_one_zero :
    oddPairedPermutation 1 (0 : Fin 3) = 0 := by
  decide

@[simp] theorem oddPairedPermutation_one_one :
    oddPairedPermutation 1 (1 : Fin 3) = 2 := by
  decide

@[simp] theorem oddPairedPermutation_one_two :
    oddPairedPermutation 1 (2 : Fin 3) = 1 := by
  decide

/-- The even terminal paired matrix, including both unequal endpoint
corrections. -/
theorem foldedEvenPencilMatrix_one (a x s : ℝ) :
    foldedEvenPencilMatrix 1 a x s =
      !![-1 - s, x; x, -a - s] := by
  have hzero : evenPairedPermutation 1 (0 : Fin 2) = 0 :=
    evenPairedPermutation_one_zero
  have hone : evenPairedPermutation 1 (1 : Fin 2) = 1 :=
    evenPairedPermutation_one_one
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [foldedEvenPencilMatrix, hzero, hone, signedMiddleMatrix,
      mul_reversal_apply, pathMatrix_apply]

/-- The odd terminal paired matrix. -/
theorem foldedOddPencilMatrix_one (a x s : ℝ) :
    foldedOddPencilMatrix 1 a x s =
      !![-s, x, -1; x, -s, -a; -1, -a, x - s] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [foldedOddPencilMatrix, signedMiddleMatrix,
      mul_reversal_apply, pathMatrix_apply]

/-- The order-zero even folded determinant. -/
theorem foldedEvenPencilMatrix_zero_det (a x s : ℝ) :
    (foldedEvenPencilMatrix 0 a x s).det = 1 := by
  simp [foldedEvenPencilMatrix]

/-- The order-one odd folded determinant. -/
theorem foldedOddPencilMatrix_zero_det (a x s : ℝ) :
    (foldedOddPencilMatrix 0 a x s).det = x - s := by
  rw [foldedOddPencilMatrix_det]
  simp [signedMiddleMatrix]

/-- An `(n+2)`-square matrix viewed with its first two coordinates exposed. -/
def exposedFoldMinorState (n : ℕ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) : FoldMinorState where
  d := K.det
  p := (K.submatrix (0 : Fin (n + 2)).succAbove
    (0 : Fin (n + 2)).succAbove).det
  q := (K.submatrix (1 : Fin (n + 2)).succAbove
    (1 : Fin (n + 2)).succAbove).det
  c := (K.submatrix (0 : Fin (n + 2)).succAbove
    (1 : Fin (n + 2)).succAbove).det
  r := (K.submatrix (fun i : Fin n ↦ i.succ.succ)
    (fun i : Fin n ↦ i.succ.succ)).det

/-- Reindex `K_{m+1}^e` so it has the literal size `(2m)+2` expected by
`exposedFoldMinorState`. -/
def foldedEvenExposedMatrix (m : ℕ) (a x s : ℝ) :
    Matrix (Fin (2 * m + 2)) (Fin (2 * m + 2)) ℝ :=
  (foldedEvenPencilMatrix (m + 1) a x s).submatrix
    (finCongr (by omega)) (finCongr (by omega))

/-- Reindex `K_{m+1}^o` so it has the literal size `(2m+1)+2`. -/
def foldedOddExposedMatrix (m : ℕ) (a x s : ℝ) :
    Matrix (Fin ((2 * m + 1) + 2)) (Fin ((2 * m + 1) + 2)) ℝ :=
  (foldedOddPencilMatrix (m + 1) a x s).submatrix
    (finCongr (by omega)) (finCongr (by omega))

/-- The five actual exposed minors of `K_{m+1}^e`. -/
def foldedEvenActualState (m : ℕ) (a x s : ℝ) : FoldMinorState :=
  exposedFoldMinorState (2 * m) (foldedEvenExposedMatrix m a x s)

/-- The five actual exposed minors of `K_{m+1}^o`. -/
def foldedOddActualState (m : ℕ) (a x s : ℝ) : FoldMinorState :=
  exposedFoldMinorState (2 * m + 1) (foldedOddExposedMatrix m a x s)

/-- The first actual state coordinate is the determinant of `K_{m+1}^e`. -/
theorem foldedEvenActualState_d (m : ℕ) (a x s : ℝ) :
    (foldedEvenActualState m a x s).d =
      (foldedEvenPencilMatrix (m + 1) a x s).det := by
  simp [foldedEvenActualState, exposedFoldMinorState,
    foldedEvenExposedMatrix]

/-- The first actual state coordinate is the determinant of `K_{m+1}^o`. -/
theorem foldedOddActualState_d (m : ℕ) (a x s : ℝ) :
    (foldedOddActualState m a x s).d =
      (foldedOddPencilMatrix (m + 1) a x s).det := by
  simp [foldedOddActualState, exposedFoldMinorState,
    foldedOddExposedMatrix]

/-- Direct evaluation of the five exposed minors of the even terminal
block. -/
theorem foldedEvenActualState_zero (a x s : ℝ) :
    foldedEvenActualState 0 a x s = foldEvenTerminalState a x s := by
  rw [foldedEvenActualState, foldedEvenExposedMatrix]
  have hmatrix :
      (foldedEvenPencilMatrix (0 + 1) a x s).submatrix
          (finCongr (by omega)) (finCongr (by omega)) =
        !![-1 - s, x; x, -a - s] := by
    simpa using foldedEvenPencilMatrix_one a x s
  rw [hmatrix]
  apply foldMinorState_ext
  all_goals simp [exposedFoldMinorState, foldEvenTerminalState,
    Matrix.det_fin_two]
  all_goals ring

/-- Direct evaluation of the five exposed minors of the odd terminal
block. -/
theorem foldedOddActualState_zero (a x s : ℝ) :
    foldedOddActualState 0 a x s = foldOddTerminalState a x s := by
  rw [foldedOddActualState, foldedOddExposedMatrix]
  have hmatrix :
      (foldedOddPencilMatrix (0 + 1) a x s).submatrix
          (finCongr (by omega)) (finCongr (by omega)) =
        !![-s, x, -1; x, -s, -a; -1, -a, x - s] := by
    simpa using foldedOddPencilMatrix_one a x s
  rw [hmatrix]
  apply foldMinorState_ext
  all_goals simp [exposedFoldMinorState, foldOddTerminalState,
    foldC0, Matrix.det_fin_two, Matrix.det_fin_three]
  all_goals ring

/-- Shift an old path coordinate one place into the interior of a path two
vertices longer. -/
def pathInteriorEmbedding (n : ℕ) : Fin n → Fin (n + 2) :=
  fun i ↦ ⟨i.1 + 1, by omega⟩

@[simp] theorem pathInteriorEmbedding_val (n : ℕ) (i : Fin n) :
    (pathInteriorEmbedding n i).1 = i.1 + 1 := rfl

/-- Deleting the two path endpoints from the signed-middle pencil leaves
the signed-middle pencil of order two less. -/
theorem signedMiddlePencil_interior_submatrix
    (n : ℕ) (a x s : ℝ) :
    (signedMiddleMatrix (n + 2) a x - s • 1).submatrix
        (pathInteriorEmbedding n) (pathInteriorEmbedding n) =
      signedMiddleMatrix n a x - s • 1 := by
  ext i j
  have hjrev :
      ((pathInteriorEmbedding n j : Fin (n + 2)).rev).1 = j.rev.1 + 1 := by
    simp only [Fin.val_rev, pathInteriorEmbedding_val]
    omega
  have hRevEq :
      pathInteriorEmbedding n i = (pathInteriorEmbedding n j : Fin (n + 2)).rev ↔
        i = j.rev := by
    constructor
    · intro h
      apply Fin.ext
      have hv := congrArg Fin.val h
      rw [pathInteriorEmbedding_val, hjrev] at hv
      omega
    · intro h
      apply Fin.ext
      rw [pathInteriorEmbedding_val, hjrev]
      exact congrArg (fun z : ℕ ↦ z + 1) (congrArg Fin.val h)
  have hEq : pathInteriorEmbedding n i = pathInteriorEmbedding n j ↔ i = j := by
    exact (Function.Injective.eq_iff (fun _ _ h ↦ Fin.ext (by
      exact Nat.add_right_cancel (congrArg Fin.val h))))
  have hUpper :
      j.rev.1 + 1 = (i.1 + 1) + 1 ↔ j.rev.1 = i.1 + 1 := by
    omega
  have hLower :
      i.1 + 1 = (j.rev.1 + 1) + 1 ↔ i.1 = j.rev.1 + 1 := by
    omega
  simp only [Matrix.submatrix_apply, signedMiddleMatrix, mul_reversal_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, pathMatrix_apply,
    pathInteriorEmbedding_val]
  rw [hjrev]
  simp only [hRevEq, hEq, hUpper, hLower]

/-- The actual even pencil indexed by blocks rather than by their linear
positions. -/
def foldedEvenBlockPencil (m : ℕ) (a x s : ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  (signedMiddleMatrix (2 * m) a x - s • 1).submatrix
    (evenPairCoordinateEquiv m) (evenPairCoordinateEquiv m)

/-- The actual odd pencil indexed by outer blocks plus its central
coordinate. -/
def foldedOddBlockPencil (m : ℕ) (a x s : ℝ) :
    Matrix ((Fin m × Fin 2) ⊕ Fin 1) ((Fin m × Fin 2) ⊕ Fin 1) ℝ :=
  (signedMiddleMatrix (2 * m + 1) a x - s • 1).submatrix
    (oddPairCoordinateEquiv m) (oddPairCoordinateEquiv m)

/-- Moving to the next even folded size shifts every old paired coordinate
one place into the path interior. -/
theorem evenPairCoordinateEquiv_succ_eq_interior
    (m : ℕ) (i : Fin m) (b : Fin 2) :
    evenPairCoordinateEquiv (m + 1) (i.succ, b) =
      pathInteriorEmbedding (2 * m) (evenPairCoordinateEquiv m (i, b)) := by
  apply Fin.ext
  fin_cases b
  · simp
  · simp
    omega

/-- The old even folded pencil is literally the tail obtained after exposing
the new first pair. -/
theorem foldedEvenBlockPencil_tail (m : ℕ) (a x s : ℝ) :
    (foldedEvenBlockPencil (m + 1) a x s).submatrix
        (fun p ↦ (p.1.succ, p.2)) (fun p ↦ (p.1.succ, p.2)) =
      foldedEvenBlockPencil m a x s := by
  ext p q
  rcases p with ⟨i, b⟩
  rcases q with ⟨j, c⟩
  simp only [foldedEvenBlockPencil, Matrix.submatrix_apply]
  rw [evenPairCoordinateEquiv_succ_eq_interior,
    evenPairCoordinateEquiv_succ_eq_interior]
  have h := congrArg
    (fun M : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ ↦
      M (evenPairCoordinateEquiv m (i, b))
        (evenPairCoordinateEquiv m (j, c)))
    (signedMiddlePencil_interior_submatrix (2 * m) a x s)
  simpa only [Matrix.submatrix_apply,
    show 2 * (m + 1) = 2 * m + 2 by omega] using h

/-- The odd tail embedding preserves the outer blocks and its central
coordinate while shifting all original path coordinates by one. -/
def oddBlockTailEmbedding (m : ℕ) :
    ((Fin m × Fin 2) ⊕ Fin 1) → ((Fin (m + 1) × Fin 2) ⊕ Fin 1)
  | Sum.inl p => Sum.inl (p.1.succ, p.2)
  | Sum.inr c => Sum.inr c

/-- Moving to the next odd folded size shifts each old folded coordinate one
place into the path interior. -/
theorem oddPairCoordinateEquiv_tail_eq_interior
    (m : ℕ) (i : (Fin m × Fin 2) ⊕ Fin 1) :
    oddPairCoordinateEquiv (m + 1) (oddBlockTailEmbedding m i) =
      pathInteriorEmbedding (2 * m + 1) (oddPairCoordinateEquiv m i) := by
  rcases i with p | c
  · rcases p with ⟨i, b⟩
    apply Fin.ext
    fin_cases b
    · simp [oddBlockTailEmbedding]
    · simp [oddBlockTailEmbedding]
      omega
  · apply Fin.ext
    have hc : c = 0 := Subsingleton.elim _ _
    subst c
    simp [oddBlockTailEmbedding]

/-- The old odd folded pencil is literally the tail obtained after exposing
the new first pair. -/
theorem foldedOddBlockPencil_tail (m : ℕ) (a x s : ℝ) :
    (foldedOddBlockPencil (m + 1) a x s).submatrix
        (oddBlockTailEmbedding m) (oddBlockTailEmbedding m) =
      foldedOddBlockPencil m a x s := by
  ext i j
  simp only [foldedOddBlockPencil, Matrix.submatrix_apply]
  rw [oddPairCoordinateEquiv_tail_eq_interior,
    oddPairCoordinateEquiv_tail_eq_interior]
  have h := congrArg
    (fun M : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ ↦
      M (oddPairCoordinateEquiv m i) (oddPairCoordinateEquiv m j))
    (signedMiddlePencil_interior_submatrix (2 * m + 1) a x s)
  simpa only [Matrix.submatrix_apply,
    show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega] using h

/-- The interior diagonal block of the folded continuant. -/
def foldInteriorBlock (x s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-s, x; x, -s]

/-- The off-diagonal block coupling a newly exposed pair to the first old
pair. -/
def foldOffBlock (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1; -a, 0]

/-- The sparse upper-right coupling `[E_off,0]` in an even block
extension. -/
def foldedEvenCoupling (m : ℕ) (a : ℝ) :
    Matrix (Fin 2) (Fin m × Fin 2) ℝ :=
  fun i p ↦ if p.1.1 = 0 then foldOffBlock a i p.2 else 0

/-- The newly exposed even pair has the paper's interior diagonal block. -/
theorem foldedEvenBlockPencil_exposed
    (m : ℕ) (hm : 0 < m) (a x s : ℝ) :
    (foldedEvenBlockPencil (m + 1) a x s).submatrix
        (fun b ↦ (0, b)) (fun b ↦ (0, b)) =
      foldInteriorBlock x s := by
  have hm0 : m ≠ 0 := Nat.ne_of_gt hm
  have hlast : 2 * (m + 1) - 1 + 1 = 2 * (m + 1) := by omega
  have houter0 : 2 * (m + 1) - 1 ≠ 0 := by omega
  have hzeroOuter : 0 ≠ 2 * (m + 1) - 1 := Ne.symm houter0
  have houterSize : 2 * (m + 1) - 1 ≠ 2 * (m + 1) := by omega
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [foldedEvenBlockPencil, foldInteriorBlock,
      signedMiddleMatrix, mul_reversal_apply, pathMatrix_apply,
      Matrix.one_apply, Fin.ext_iff, Fin.val_rev, hm0, hlast, houter0,
      hzeroOuter, houterSize]

/-- The upper-right exposed-even coupling is exactly `[E_off,0]`. -/
theorem foldedEvenBlockPencil_coupling
    (m : ℕ) (hm : 0 < m) (a x s : ℝ) :
    (foldedEvenBlockPencil (m + 1) a x s).submatrix
        (fun b ↦ (0, b)) (fun p ↦ (p.1.succ, p.2)) =
      foldedEvenCoupling m a := by
  ext b p
  rcases p with ⟨i, c⟩
  have hzeroNeLeft :
      0 ≠ 2 * (m + 1) - (i.1 + 1 + 1) := by omega
  have hleftNeOne :
      2 * (m + 1) - (i.1 + 1 + 1) ≠ 1 := by omega
  have hright :
      2 * (m + 1) - (2 * (m + 1) - 1 - (i.1 + 1) + 1) =
        i.1 + 1 := by omega
  have hlastNeLeft :
      2 * (m + 1) - 1 ≠ 2 * (m + 1) - (i.1 + 1 + 1) := by
    omega
  have hleftNeLastSucc :
      2 * (m + 1) - (i.1 + 1 + 1) ≠
        2 * (m + 1) - 1 + 1 := by
    omega
  have hsizeEqLeftAddTwo :
      2 * (m + 1) = 2 * (m + 1) - (i.1 + 1 + 1) + 2 ↔
        i.1 = 0 := by
    omega
  have hlastNeRight : 2 * (m + 1) - 1 ≠ i.1 + 1 := by omega
  have hsizeNeRightAddTwo : 2 * (m + 1) ≠ i.1 + 1 + 2 := by omega
  have hiNeLast : i.1 ≠ 2 * (m + 1) - 1 := by omega
  have hspecialRight :
      2 * (m + 1) - (2 * (m + 1) - 1 - 1 + 1) = 1 := by
    omega
  have hlastNeMinusTwo :
      2 * (m + 1) - 1 ≠ 2 * (m + 1) - 2 := by
    omega
  have hminusTwoNeLastSucc :
      2 * (m + 1) - 2 ≠ 2 * (m + 1) - 1 + 1 := by
    omega
  fin_cases b <;> fin_cases c
  · simp [foldedEvenBlockPencil, foldedEvenCoupling, foldOffBlock,
      signedMiddleMatrix, mul_reversal_apply, pathMatrix_apply,
      Fin.ext_iff, Fin.val_rev, hzeroNeLeft, hleftNeOne]
  · by_cases hi : i.1 = 0
    · have hiFin : i = ⟨0, hm⟩ := by
        apply Fin.ext
        exact hi
      subst i
      simp [foldedEvenBlockPencil, foldedEvenCoupling, foldOffBlock,
        signedMiddleMatrix, mul_reversal_apply, pathMatrix_apply,
        Fin.ext_iff, Fin.val_rev, hspecialRight]
    · simp [foldedEvenBlockPencil, foldedEvenCoupling,
        signedMiddleMatrix, mul_reversal_apply, pathMatrix_apply,
        Fin.ext_iff, Fin.val_rev, hright, hi]
  · by_cases hi : i.1 = 0
    · have hiFin : i = ⟨0, hm⟩ := by
        apply Fin.ext
        exact hi
      subst i
      simp [foldedEvenBlockPencil, foldedEvenCoupling, foldOffBlock,
        signedMiddleMatrix, mul_reversal_apply, pathMatrix_apply,
        Fin.ext_iff, Fin.val_rev, hlastNeMinusTwo,
        hminusTwoNeLastSucc]
    · simp [foldedEvenBlockPencil, foldedEvenCoupling,
        signedMiddleMatrix, mul_reversal_apply, pathMatrix_apply,
        Fin.ext_iff, Fin.val_rev, hlastNeLeft, hleftNeLastSucc,
        hsizeEqLeftAddTwo, hi]
  · simp [foldedEvenBlockPencil, foldedEvenCoupling, foldOffBlock,
      signedMiddleMatrix, mul_reversal_apply, pathMatrix_apply,
      Fin.ext_iff, Fin.val_rev, hright, hlastNeRight,
      hsizeNeRightAddTwo, hiNeLast]

/-- The paired block-extension indexing map. -/
def evenBlockExtensionIndex (m : ℕ) :
    Fin 2 ⊕ (Fin m × Fin 2) → Fin (m + 1) × Fin 2
  | Sum.inl b => (0, b)
  | Sum.inr p => (p.1.succ, p.2)

/-- Exact even instance of `eq:fold-block-extension`. -/
theorem foldedEvenBlockPencil_extension
    (m : ℕ) (hm : 0 < m) (a x s : ℝ) :
    (foldedEvenBlockPencil (m + 1) a x s).submatrix
        (evenBlockExtensionIndex m) (evenBlockExtensionIndex m) =
      Matrix.fromBlocks (foldInteriorBlock x s) (foldedEvenCoupling m a)
        (foldedEvenCoupling m a)ᵀ (foldedEvenBlockPencil m a x s) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simpa [evenBlockExtensionIndex] using congrFun (congrFun
      (foldedEvenBlockPencil_exposed m hm a x s) i) j
  · simpa [evenBlockExtensionIndex] using congrFun (congrFun
      (foldedEvenBlockPencil_coupling m hm a x s) i) j
  · simp only [Matrix.submatrix_apply, evenBlockExtensionIndex,
      Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply]
    have hK : (foldedEvenBlockPencil (m + 1) a x s).IsSymm :=
      ((signedMiddleMatrix_isSymm (2 * (m + 1)) a x).sub
        (Matrix.isSymm_one.smul s)).submatrix (evenPairCoordinateEquiv (m + 1))
    calc
      foldedEvenBlockPencil (m + 1) a x s (i.1.succ, i.2) (0, j) =
          foldedEvenBlockPencil (m + 1) a x s (0, j) (i.1.succ, i.2) := by
        exact congrFun (congrFun hK (0, j)) (i.1.succ, i.2)
      _ = foldedEvenCoupling m a j i := congrFun (congrFun
        (foldedEvenBlockPencil_coupling m hm a x s) j) i
  · simpa [evenBlockExtensionIndex] using congrFun (congrFun
      (foldedEvenBlockPencil_tail m a x s) i) j

/-- The sparse upper-right coupling `[E_off,0]` in an odd block
extension. -/
def foldedOddCoupling (m : ℕ) (a : ℝ) :
    Matrix (Fin 2) ((Fin m × Fin 2) ⊕ Fin 1) ℝ
  | i, Sum.inl p => if p.1.1 = 0 then foldOffBlock a i p.2 else 0
  | _, Sum.inr _ => 0

/-- The newly exposed odd pair has the paper's interior diagonal block. -/
theorem foldedOddBlockPencil_exposed
    (m : ℕ) (a x s : ℝ) :
    (foldedOddBlockPencil (m + 1) a x s).submatrix
        (fun b ↦ Sum.inl (0, b)) (fun b ↦ Sum.inl (0, b)) =
      foldInteriorBlock x s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [foldedOddBlockPencil, foldInteriorBlock,
      signedMiddleMatrix, mul_reversal_apply, pathMatrix_apply,
      Matrix.one_apply, Fin.ext_iff, Fin.val_rev]

/-- The upper-right exposed-odd coupling is exactly `[E_off,0]`. -/
theorem foldedOddBlockPencil_coupling
    (m : ℕ) (hm : 0 < m) (a x s : ℝ) :
    (foldedOddBlockPencil (m + 1) a x s).submatrix
        (fun b ↦ Sum.inl (0, b)) (oddBlockTailEmbedding m) =
      foldedOddCoupling m a := by
  ext b p
  rcases p with p | c
  · rcases p with ⟨i, d⟩
    have hzeroNeLeft :
        0 ≠ 2 * (m + 1) - (i.1 + 1) := by
      omega
    have hleftNeOne :
        2 * (m + 1) - (i.1 + 1) ≠ 1 := by
      omega
    have hmirror :
        2 * (m + 1) - (2 * (m + 1) - (i.1 + 1)) =
          i.1 + 1 := by
      omega
    have hsizeNeLeft :
        2 * (m + 1) ≠ 2 * (m + 1) - (i.1 + 1) := by
      omega
    have hleftNeSizeSucc :
        2 * (m + 1) - (i.1 + 1) ≠ 2 * (m + 1) + 1 := by
      omega
    have hsizeEqLeftSucc :
        2 * (m + 1) = 2 * (m + 1) - (i.1 + 1) + 1 ↔
          i.1 = 0 := by
      omega
    have hsizeNeRight : 2 * (m + 1) ≠ i.1 + 1 := by
      omega
    have hsizeNeRightSucc : 2 * (m + 1) ≠ i.1 + 1 + 1 := by
      omega
    have hiNeSize : i.1 ≠ 2 * (m + 1) := by
      omega
    have hspecialMirror :
        2 * (m + 1) - (2 * (m + 1) - 1) = 1 := by
      omega
    have hsizeNePred :
        2 * (m + 1) ≠ 2 * (m + 1) - 1 := by
      omega
    have hsizeEqPredSuccIff :
        2 * (m + 1) = 2 * (m + 1) - 1 + 1 ↔ True :=
      iff_true_intro (by omega)
    fin_cases b <;> fin_cases d
    · simp [foldedOddBlockPencil, foldedOddCoupling, oddBlockTailEmbedding,
        foldOffBlock, signedMiddleMatrix, mul_reversal_apply,
        pathMatrix_apply, Fin.ext_iff, Fin.val_rev,
        hzeroNeLeft, hleftNeOne]
    · by_cases hi : i.1 = 0 <;>
        simp [foldedOddBlockPencil, foldedOddCoupling, oddBlockTailEmbedding,
          foldOffBlock, signedMiddleMatrix, mul_reversal_apply,
          pathMatrix_apply, Fin.ext_iff, Fin.val_rev,
          hmirror, hspecialMirror, hi]
    · by_cases hi : i.1 = 0 <;>
        simp [foldedOddBlockPencil, foldedOddCoupling, oddBlockTailEmbedding,
          foldOffBlock, signedMiddleMatrix, mul_reversal_apply,
          pathMatrix_apply, Fin.ext_iff, Fin.val_rev,
          hsizeNeLeft, hleftNeSizeSucc, hsizeEqLeftSucc, hsizeNePred,
          hsizeEqPredSuccIff, hi]
    · simpa [foldedOddBlockPencil, foldedOddCoupling, oddBlockTailEmbedding,
        foldOffBlock, signedMiddleMatrix, mul_reversal_apply,
        pathMatrix_apply, Fin.ext_iff, Fin.val_rev, hmirror,
        hsizeNeRight, hsizeNeRightSucc] using hiNeSize
  · have hc : c = 0 := Subsingleton.elim _ _
    subst c
    have hcenter : 2 * (m + 1) - (m + 1) = m + 1 := by
      omega
    have hsizeNeCenter : 2 * (m + 1) ≠ m + 1 := by
      omega
    have hsizeNeCenterSucc : 2 * (m + 1) ≠ m + 1 + 1 := by
      omega
    have hm0 : m ≠ 0 := Nat.ne_of_gt hm
    have hmNeSize : m ≠ 2 * (m + 1) := by
      omega
    fin_cases b
    · simpa [foldedOddBlockPencil, foldedOddCoupling, oddBlockTailEmbedding,
        signedMiddleMatrix, mul_reversal_apply, pathMatrix_apply,
        Fin.ext_iff, Fin.val_rev, hcenter] using hm0
    · simpa [foldedOddBlockPencil, foldedOddCoupling, oddBlockTailEmbedding,
        signedMiddleMatrix, mul_reversal_apply, pathMatrix_apply,
        Fin.ext_iff, Fin.val_rev, hcenter, hsizeNeCenter,
        hsizeNeCenterSucc] using hmNeSize

/-- The paired odd block-extension indexing map. -/
def oddBlockExtensionIndex (m : ℕ) :
    Fin 2 ⊕ ((Fin m × Fin 2) ⊕ Fin 1) →
      (Fin (m + 1) × Fin 2) ⊕ Fin 1
  | Sum.inl b => Sum.inl (0, b)
  | Sum.inr p => oddBlockTailEmbedding m p

/-- Exact odd instance of `eq:fold-block-extension`. -/
theorem foldedOddBlockPencil_extension
    (m : ℕ) (hm : 0 < m) (a x s : ℝ) :
    (foldedOddBlockPencil (m + 1) a x s).submatrix
        (oddBlockExtensionIndex m) (oddBlockExtensionIndex m) =
      Matrix.fromBlocks (foldInteriorBlock x s) (foldedOddCoupling m a)
        (foldedOddCoupling m a)ᵀ (foldedOddBlockPencil m a x s) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simpa [oddBlockExtensionIndex] using congrFun (congrFun
      (foldedOddBlockPencil_exposed m a x s) i) j
  · simpa [oddBlockExtensionIndex] using congrFun (congrFun
      (foldedOddBlockPencil_coupling m hm a x s) i) j
  · simp only [Matrix.submatrix_apply, oddBlockExtensionIndex,
      Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply]
    have hK : (foldedOddBlockPencil (m + 1) a x s).IsSymm :=
      ((signedMiddleMatrix_isSymm (2 * (m + 1) + 1) a x).sub
        (Matrix.isSymm_one.smul s)).submatrix (oddPairCoordinateEquiv (m + 1))
    calc
      foldedOddBlockPencil (m + 1) a x s (oddBlockTailEmbedding m i)
          (Sum.inl (0, j)) =
          foldedOddBlockPencil (m + 1) a x s (Sum.inl (0, j))
            (oddBlockTailEmbedding m i) := by
        exact congrFun (congrFun hK (Sum.inl (0, j)))
          (oddBlockTailEmbedding m i)
      _ = foldedOddCoupling m a j i := congrFun (congrFun
        (foldedOddBlockPencil_coupling m hm a x s) j) i
  · simpa [oddBlockExtensionIndex] using congrFun (congrFun
      (foldedOddBlockPencil_tail m a x s) i) j

/-- A symmetric one-coordinate border whose coupling is supported only in
the first coordinate of the old matrix. -/
def singleBorderMatrix (n : ℕ) (d t : ℝ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  fun i j ↦ Fin.cases
    (Fin.cases d (fun q ↦ if q = 0 then t else 0) j)
    (fun p ↦ Fin.cases (if p = 0 then t else 0) (fun q ↦ K p q) j) i

@[simp] theorem singleBorderMatrix_zero_zero (n : ℕ) (d t : ℝ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    singleBorderMatrix n d t K 0 0 = d := rfl

@[simp] theorem singleBorderMatrix_zero_succ (n : ℕ) (d t : ℝ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j : Fin (n + 1)) :
    singleBorderMatrix n d t K 0 j.succ = if j = 0 then t else 0 := rfl

@[simp] theorem singleBorderMatrix_succ_zero (n : ℕ) (d t : ℝ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin (n + 1)) :
    singleBorderMatrix n d t K i.succ 0 = if i = 0 then t else 0 := rfl

@[simp] theorem singleBorderMatrix_succ_succ (n : ℕ) (d t : ℝ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i j : Fin (n + 1)) :
    singleBorderMatrix n d t K i.succ j.succ = K i j := rfl

/-- Universal single-border determinant identity, proved by two literal
Laplace expansions and requiring no invertibility hypothesis. -/
theorem det_singleBorderMatrix (n : ℕ) (d t : ℝ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (singleBorderMatrix n d t K).det =
      d * K.det - t ^ 2 * (K.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simp only [singleBorderMatrix_zero_zero, singleBorderMatrix_zero_succ,
    Fin.val_zero, Fin.val_succ, pow_zero, one_mul, if_pos, zero_add]
  simp only [Fin.succ_ne_zero, if_false, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  have htailMatrix :
      ((singleBorderMatrix n d t K).submatrix Fin.succ
          (0 : Fin (n + 2)).succAbove) = K := by
    ext i j
    simp
  rw [htailMatrix]
  let M := (singleBorderMatrix n d t K).submatrix Fin.succ
    (1 : Fin (n + 2)).succAbove
  have hMdet : M.det = t * (K.submatrix Fin.succ Fin.succ).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have htail' :
        (∑ i : Fin n,
          (-1 : ℝ) ^ (i.succ : ℕ) * M i.succ 0 *
            (M.submatrix i.succ.succAbove Fin.succ).det) = 0 := by
      apply Fintype.sum_eq_zero
      intro i
      simp [M, singleBorderMatrix]
    rw [htail', add_zero]
    have hminor : M.submatrix (0 : Fin (n + 1)).succAbove Fin.succ =
        K.submatrix Fin.succ Fin.succ := by
      ext i j
      simp [M, singleBorderMatrix]
    rw [hminor]
    have hM00 : M 0 0 = t := by
      rfl
    rw [hM00]
    simp
  change d * K.det + (-1 : ℝ) ^ 1 * t * M.det = _
  rw [hMdet]
  ring

@[simp] theorem finCases_one {n : ℕ} {R : Type*} (z : R)
    (f : Fin (n + 1) → R) :
    Fin.cases z f (1 : Fin (n + 2)) = f 0 := rfl

/-- Add one exposed folded pair in the linear coordinate order
`new-left,new-right,old coordinates`. -/
def foldLinearExtension (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    Matrix (Fin (n + 4)) (Fin (n + 4)) ℝ :=
  fun i j ↦ Fin.cases
    (Fin.cases (-s)
      (fun j' ↦ Fin.cases x (fun q ↦ if q = 1 then -1 else 0) j') j)
    (fun i' ↦ Fin.cases
      (Fin.cases x
        (fun j' ↦ Fin.cases (-s) (fun q ↦ if q = 0 then -a else 0) j') j)
      (fun p ↦ Fin.cases (if p = 1 then -1 else 0)
        (fun j' ↦ Fin.cases (if p = 0 then -a else 0) (fun q ↦ K p q) j') j)
      i') i

/-- A single border coupled to coordinate one rather than coordinate zero. -/
def singleBorderMatrixAtOne (n : ℕ) (d t : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ :=
  fun i j ↦ Fin.cases
    (Fin.cases d (fun q ↦ if q = 1 then t else 0) j)
    (fun p ↦ Fin.cases (if p = 1 then t else 0) (fun q ↦ K p q) j) i

/-- Lift a permutation to one extra leading coordinate which it fixes. -/
def liftTailPerm {k : ℕ} (e : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k + 1)) where
  toFun := Fin.cases 0 (fun i ↦ (e i).succ)
  invFun := Fin.cases 0 (fun i ↦ (e.symm i).succ)
  left_inv i := by
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · rfl
    · simp
  right_inv i := by
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · rfl
    · simp

/-- Swap the first two coordinates of a space known to have at least two. -/
def swapFirstTwo (n : ℕ) : Equiv.Perm (Fin (n + 2)) :=
  Equiv.swap 0 1

@[simp] theorem swapFirstTwo_zero (n : ℕ) :
    swapFirstTwo n 0 = 1 := by
  simp [swapFirstTwo]

@[simp] theorem swapFirstTwo_one (n : ℕ) :
    swapFirstTwo n 1 = 0 := by
  simp [swapFirstTwo]

theorem swapFirstTwo_succ (n : ℕ) (i : Fin (n + 1)) :
    swapFirstTwo n i.succ = (1 : Fin (n + 2)).succAbove i := by
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simp
  · rw [Fin.succAbove_of_le_castSucc]
    · rw [swapFirstTwo]
      apply Equiv.swap_apply_of_ne_of_ne
      · intro h
        have hv := congrArg Fin.val h
        simp at hv
      · intro h
        have hv := congrArg Fin.val h
        simp at hv
    · change 1 ≤ i.1 + 1
      omega

theorem swapFirstTwo_eq_one_iff (n : ℕ) (i : Fin (n + 2)) :
    swapFirstTwo n i = 1 ↔ i = 0 := by
  constructor
  · intro h
    apply (swapFirstTwo n).injective
    rw [h, swapFirstTwo_zero]
  · rintro rfl
    exact swapFirstTwo_zero n

/-- Reindexing a coordinate-one border by the lifted first swap turns it
into the coordinate-zero border of the simultaneously swapped old matrix. -/
theorem singleBorderMatrixAtOne_reindex (n : ℕ) (d t : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    (singleBorderMatrixAtOne n d t K).submatrix
        (liftTailPerm (swapFirstTwo n)) (liftTailPerm (swapFirstTwo n)) =
      singleBorderMatrix (n + 1) d t
        (K.submatrix (swapFirstTwo n) (swapFirstTwo n)) := by
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · rfl
    · simp [singleBorderMatrixAtOne, singleBorderMatrix, liftTailPerm,
        swapFirstTwo_eq_one_iff]
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp [singleBorderMatrixAtOne, singleBorderMatrix, liftTailPerm,
        swapFirstTwo_eq_one_iff]
    · rfl

/-- The coordinate-one bordered determinant formula. -/
theorem det_singleBorderMatrixAtOne (n : ℕ) (d t : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    (singleBorderMatrixAtOne n d t K).det =
      d * K.det - t ^ 2 *
        (K.submatrix (1 : Fin (n + 2)).succAbove
          (1 : Fin (n + 2)).succAbove).det := by
  let e := swapFirstTwo n
  let K' := K.submatrix e e
  have hreindex := singleBorderMatrixAtOne_reindex n d t K
  have hdet : (singleBorderMatrixAtOne n d t K).det =
      (singleBorderMatrix (n + 1) d t K').det := by
    rw [← hreindex]
    symm
    exact Matrix.det_submatrix_equiv_self _ _
  rw [hdet, det_singleBorderMatrix]
  have hKdet : K'.det = K.det := Matrix.det_submatrix_equiv_self _ _
  rw [hKdet]
  have hminor : K'.submatrix Fin.succ Fin.succ =
      K.submatrix (1 : Fin (n + 2)).succAbove
        (1 : Fin (n + 2)).succAbove := by
    ext i j
    simp only [K', Matrix.submatrix_apply]
    rw [swapFirstTwo_succ, swapFirstTwo_succ]
  rw [hminor]

/-- Deleting the first new coordinate leaves the `-a` single border. -/
theorem foldLinearExtension_delete_zero
    (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    (foldLinearExtension n a x s K).submatrix
        (0 : Fin (n + 4)).succAbove (0 : Fin (n + 4)).succAbove =
      singleBorderMatrix (n + 1) (-s) (-a) K := by
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · refine Fin.cases ?_ (fun j ↦ ?_) j <;>
      simp [foldLinearExtension, singleBorderMatrix]
  · refine Fin.cases ?_ (fun j ↦ ?_) j <;>
      simp [foldLinearExtension, singleBorderMatrix]

/-- Deleting the second new coordinate leaves the `-1` single border. -/
theorem foldLinearExtension_delete_one
    (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    (foldLinearExtension n a x s K).submatrix
        (1 : Fin (n + 4)).succAbove (1 : Fin (n + 4)).succAbove =
      singleBorderMatrixAtOne n (-s) (-1) K := by
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · refine Fin.cases ?_ (fun j ↦ ?_) j <;>
      simp [foldLinearExtension, singleBorderMatrixAtOne, Fin.succAbove]
  · refine Fin.cases ?_ (fun j ↦ ?_) j <;>
      simp [foldLinearExtension, singleBorderMatrixAtOne, Fin.succAbove]

/-- Deleting both new coordinates recovers the old matrix literally. -/
theorem foldLinearExtension_delete_both
    (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    (foldLinearExtension n a x s K).submatrix
        (fun i : Fin (n + 2) ↦ i.succ.succ)
        (fun i : Fin (n + 2) ↦ i.succ.succ) = K := by
  ext i j
  rfl

/-- The first principal exposed minor and the tail determinant satisfy the
`p` and `r` lines of `eq:five-minor-update` without any nonsingularity
hypothesis. -/
theorem exposedFoldMinorState_extension_pr
    (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    let old := exposedFoldMinorState n K
    let new := exposedFoldMinorState (n + 2) (foldLinearExtension n a x s K)
    new.p = -s * old.d - a ^ 2 * old.p ∧ new.r = old.d := by
  dsimp only
  simp only [exposedFoldMinorState]
  rw [foldLinearExtension_delete_zero, foldLinearExtension_delete_both,
    det_singleBorderMatrix]
  simp only [Fin.succAbove_zero]
  constructor
  · ring
  · trivial

/-- The second principal exposed minor satisfies the `q` line of
`eq:five-minor-update`. -/
theorem exposedFoldMinorState_extension_q
    (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    (exposedFoldMinorState (n + 2) (foldLinearExtension n a x s K)).q =
      -s * (exposedFoldMinorState n K).d -
        (exposedFoldMinorState n K).q := by
  simp only [exposedFoldMinorState]
  rw [foldLinearExtension_delete_one, det_singleBorderMatrixAtOne]
  ring

/-- An asymmetric border: the top row meets old coordinate zero with `u`,
whereas the first column meets old coordinate one with `v`. -/
def crossBorderMatrix (n : ℕ) (d u v : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ :=
  fun i j ↦ Fin.cases
    (Fin.cases d (fun q ↦ if q = 0 then u else 0) j)
    (fun p ↦ Fin.cases (if p = 1 then v else 0) (fun q ↦ K p q) j) i

/-- Literal cross-border determinant formula. -/
theorem det_crossBorderMatrix (n : ℕ) (d u v : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    (crossBorderMatrix n d u v K).det = d * K.det + u * v *
      (K.submatrix (1 : Fin (n + 2)).succAbove Fin.succ).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have htailMatrix :
      (crossBorderMatrix n d u v K).submatrix Fin.succ
          (0 : Fin (n + 3)).succAbove = K := by
    ext i j
    simp [crossBorderMatrix]
  let M := (crossBorderMatrix n d u v K).submatrix Fin.succ
    (1 : Fin (n + 3)).succAbove
  have hMdet : M.det = -v *
      (K.submatrix (1 : Fin (n + 2)).succAbove Fin.succ).det := by
    rw [Matrix.det_succ_column_zero]
    have hsum :
        (∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) * M i 0 *
          (M.submatrix i.succAbove Fin.succ).det) =
          (-1 : ℝ) ^ (1 : ℕ) * M 1 0 *
            (M.submatrix (1 : Fin (n + 2)).succAbove Fin.succ).det := by
      rw [Finset.sum_eq_single (1 : Fin (n + 2))]
      · rfl
      · intro i _ hi
        have hentry : M i 0 = 0 := by
          change (if i = 1 then v else 0) = 0
          simp [hi]
        rw [hentry, mul_zero, zero_mul]
      · simp
    rw [hsum]
    have hminor : M.submatrix (1 : Fin (n + 2)).succAbove Fin.succ =
        K.submatrix (1 : Fin (n + 2)).succAbove Fin.succ := by
      ext i j
      simp [M, crossBorderMatrix, Fin.succAbove]
    rw [hminor]
    have hentry : M 1 0 = v := by rfl
    rw [hentry]
    ring
  have htailSum :
      (∑ j : Fin (n + 2),
        (-1 : ℝ) ^ (j.succ : ℕ) *
          crossBorderMatrix n d u v K 0 j.succ *
            ((crossBorderMatrix n d u v K).submatrix Fin.succ
              j.succ.succAbove).det) = -u * M.det := by
    rw [Finset.sum_eq_single (0 : Fin (n + 2))]
    · change (-1 : ℝ) ^ 1 * u * M.det = -u * M.det
      ring
    · intro j _ hj
      have hentry : crossBorderMatrix n d u v K 0 j.succ = 0 := by
        change (if j = 0 then u else 0) = 0
        simp [hj]
      rw [hentry, mul_zero, zero_mul]
    · simp
  have hzero : crossBorderMatrix n d u v K 0 0 = d := rfl
  rw [hzero, htailMatrix, htailSum, hMdet]
  norm_num
  ring

/-- The off-principal exposed deletion is the cross border above. -/
theorem foldLinearExtension_delete_cross
    (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    (foldLinearExtension n a x s K).submatrix
        (0 : Fin (n + 4)).succAbove (1 : Fin (n + 4)).succAbove =
      crossBorderMatrix n x (-a) (-1) K := by
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · refine Fin.cases ?_ (fun j ↦ ?_) j <;>
      simp [foldLinearExtension, crossBorderMatrix, Fin.succAbove]
  · refine Fin.cases ?_ (fun j ↦ ?_) j <;>
      simp [foldLinearExtension, crossBorderMatrix, Fin.succAbove]

/-- For a symmetric old matrix, the off-principal exposed minor satisfies
the `c` line of `eq:five-minor-update`. -/
theorem exposedFoldMinorState_extension_c
    (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hK : K.IsSymm) :
    (exposedFoldMinorState (n + 2) (foldLinearExtension n a x s K)).c =
      x * (exposedFoldMinorState n K).d +
        a * (exposedFoldMinorState n K).c := by
  simp only [exposedFoldMinorState]
  rw [foldLinearExtension_delete_cross, det_crossBorderMatrix]
  have hminor :
      (K.submatrix (1 : Fin (n + 2)).succAbove Fin.succ).det =
        (K.submatrix (0 : Fin (n + 2)).succAbove
          (1 : Fin (n + 2)).succAbove).det := by
    rw [← Matrix.det_transpose]
    congr 1
    ext i j
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
    rw [show K ((1 : Fin (n + 2)).succAbove j) (Fin.succ i) =
        K (Fin.succ i) ((1 : Fin (n + 2)).succAbove j) by
      exact congrFun (congrFun hK (Fin.succ i))
        ((1 : Fin (n + 2)).succAbove j)]
    rfl
  rw [hminor]
  ring

/-- The remaining cofactor in the first-row expansion of a folded linear
extension: delete the first new row and old column one. -/
def foldLinearAuxMinor (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ :=
  (foldLinearExtension n a x s K).submatrix Fin.succ
    (3 : Fin (n + 4)).succAbove

/-- First cofactor of `foldLinearAuxMinor`. -/
def foldLinearAuxMinorZero (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  (foldLinearAuxMinor n a x s K).submatrix Fin.succ
    (0 : Fin (n + 3)).succAbove

/-- Second cofactor of `foldLinearAuxMinor`. -/
def foldLinearAuxMinorOne (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  (foldLinearAuxMinor n a x s K).submatrix Fin.succ
    (1 : Fin (n + 3)).succAbove

/-- Third cofactor of `foldLinearAuxMinor`. -/
def foldLinearAuxMinorTwo (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  (foldLinearAuxMinor n a x s K).submatrix Fin.succ
    (2 : Fin (n + 3)).succAbove

/-- The first auxiliary cofactor is `-a` times the old off-principal
minor. -/
theorem foldLinearAuxMinorZero_det (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    (foldLinearAuxMinorZero n a x s K).det = -a *
      (K.submatrix (0 : Fin (n + 2)).succAbove
        (1 : Fin (n + 2)).succAbove).det := by
  let A := foldLinearAuxMinorZero n a x s K
  have hentry (i : Fin (n + 2)) :
      A i 0 = if i = 0 then -a else 0 := by
    rfl
  have hminor : A.submatrix (0 : Fin (n + 2)).succAbove Fin.succ =
      K.submatrix (0 : Fin (n + 2)).succAbove
        (1 : Fin (n + 2)).succAbove := by
    ext i j
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> rfl
  rw [Matrix.det_succ_column_zero]
  calc
    (∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) * A i 0 *
        (A.submatrix i.succAbove Fin.succ).det) =
        (-1 : ℝ) ^ (0 : ℕ) * A 0 0 *
          (A.submatrix (0 : Fin (n + 2)).succAbove Fin.succ).det := by
      rw [Finset.sum_eq_single (0 : Fin (n + 2))]
      · rfl
      · intro i _ hi
        rw [hentry, if_neg hi, mul_zero, zero_mul]
      · simp
    _ = -a * (K.submatrix (0 : Fin (n + 2)).succAbove
        (1 : Fin (n + 2)).succAbove).det := by
      rw [hentry, if_pos rfl, hminor]
      ring

/-- The second auxiliary cofactor is the old second principal minor. -/
theorem foldLinearAuxMinorOne_det (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    (foldLinearAuxMinorOne n a x s K).det =
      (K.submatrix (1 : Fin (n + 2)).succAbove
        (1 : Fin (n + 2)).succAbove).det := by
  let A := foldLinearAuxMinorOne n a x s K
  have hentry (i : Fin (n + 2)) :
      A i 0 = if i = 1 then -1 else 0 := by
    rfl
  have hminor : A.submatrix (1 : Fin (n + 2)).succAbove Fin.succ =
      K.submatrix (1 : Fin (n + 2)).succAbove
        (1 : Fin (n + 2)).succAbove := by
    ext i j
    refine Fin.cases ?_ (fun i ↦ ?_) i <;>
      refine Fin.cases ?_ (fun j ↦ ?_) j <;> rfl
  rw [Matrix.det_succ_column_zero]
  calc
    (∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) * A i 0 *
        (A.submatrix i.succAbove Fin.succ).det) =
        (-1 : ℝ) ^ (1 : ℕ) * A 1 0 *
          (A.submatrix (1 : Fin (n + 2)).succAbove Fin.succ).det := by
      rw [Finset.sum_eq_single (1 : Fin (n + 2))]
      · rfl
      · intro i _ hi
        rw [hentry, if_neg hi, mul_zero, zero_mul]
      · simp
    _ = (K.submatrix (1 : Fin (n + 2)).succAbove
        (1 : Fin (n + 2)).succAbove).det := by
      rw [hentry, if_pos rfl, hminor]
      ring

/-- The third auxiliary cofactor is `-a` times the old twice-deleted
minor. -/
theorem foldLinearAuxMinorTwo_det (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    (foldLinearAuxMinorTwo n a x s K).det = -a *
      (K.submatrix (fun i : Fin n ↦ i.succ.succ)
        (fun i : Fin n ↦ i.succ.succ)).det := by
  let A := foldLinearAuxMinorTwo n a x s K
  let B := A.submatrix (1 : Fin (n + 2)).succAbove Fin.succ
  have hentryA (i : Fin (n + 2)) :
      A i 0 = if i = 1 then -1 else 0 := by
    rfl
  have hentryB (i : Fin (n + 1)) :
      B i 0 = if i = 0 then -a else 0 := by
    refine Fin.cases ?_ (fun i ↦ ?_) i
    · rfl
    · rfl
  have hminorB : B.submatrix (0 : Fin (n + 1)).succAbove Fin.succ =
      K.submatrix (fun i : Fin n ↦ i.succ.succ)
        (fun i : Fin n ↦ i.succ.succ) := by
    ext i j
    rfl
  have hBdet : B.det = -a *
      (K.submatrix (fun i : Fin n ↦ i.succ.succ)
        (fun i : Fin n ↦ i.succ.succ)).det := by
    rw [Matrix.det_succ_column_zero]
    calc
      (∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) * B i 0 *
          (B.submatrix i.succAbove Fin.succ).det) =
          (-1 : ℝ) ^ (0 : ℕ) * B 0 0 *
            (B.submatrix (0 : Fin (n + 1)).succAbove Fin.succ).det := by
        rw [Finset.sum_eq_single (0 : Fin (n + 1))]
        · rfl
        · intro i _ hi
          rw [hentryB, if_neg hi, mul_zero, zero_mul]
        · simp
      _ = -a * (K.submatrix (fun i : Fin n ↦ i.succ.succ)
          (fun i : Fin n ↦ i.succ.succ)).det := by
        rw [hentryB, if_pos rfl, hminorB]
        ring
  rw [Matrix.det_succ_column_zero]
  calc
    (∑ i : Fin (n + 2), (-1 : ℝ) ^ (i : ℕ) * A i 0 *
        (A.submatrix i.succAbove Fin.succ).det) =
        (-1 : ℝ) ^ (1 : ℕ) * A 1 0 * B.det := by
      rw [Finset.sum_eq_single (1 : Fin (n + 2))]
      · rfl
      · intro i _ hi
        rw [hentryA, if_neg hi, mul_zero, zero_mul]
      · simp
    _ = -a * (K.submatrix (fun i : Fin n ↦ i.succ.succ)
        (fun i : Fin n ↦ i.succ.succ)).det := by
      rw [hentryA, if_pos rfl, hBdet]
      ring

/-- The leftover cofactor contributes exactly the `q,c,r` terms of the
five-minor determinant update. -/
theorem foldLinearAuxMinor_det (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) :
    (foldLinearAuxMinor n a x s K).det =
      s * (K.submatrix (1 : Fin (n + 2)).succAbove
          (1 : Fin (n + 2)).succAbove).det -
        a * x * (K.submatrix (0 : Fin (n + 2)).succAbove
          (1 : Fin (n + 2)).succAbove).det +
        a ^ 2 * (K.submatrix (fun i : Fin n ↦ i.succ.succ)
          (fun i : Fin n ↦ i.succ.succ)).det := by
  let M := foldLinearAuxMinor n a x s K
  let A₀ := foldLinearAuxMinorZero n a x s K
  let A₁ := foldLinearAuxMinorOne n a x s K
  let A₂ := foldLinearAuxMinorTwo n a x s K
  have hentryZero : foldLinearAuxMinor n a x s K 0
      (0 : Fin (n + 3)) = x := by rfl
  have hentryOne : foldLinearAuxMinor n a x s K 0
      (Fin.succ (0 : Fin (n + 2))) = -s := by rfl
  have hentryTwo : foldLinearAuxMinor n a x s K 0
      (Fin.succ (0 : Fin (n + 1))).succ = -a := by rfl
  have htailEntry (i : Fin n) : M 0 i.succ.succ.succ = 0 := by
    change (if i.succ.succ = (0 : Fin (n + 2)) then -a else 0) = 0
    rw [if_neg]
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hminorZero : M.submatrix Fin.succ
      (0 : Fin (n + 3)).succAbove = A₀ := rfl
  have hminorOne : M.submatrix Fin.succ
      (Fin.succ (0 : Fin (n + 2))).succAbove = A₁ := rfl
  have hminorTwo : M.submatrix Fin.succ
      (Fin.succ (0 : Fin (n + 1))).succ.succAbove = A₂ := rfl
  dsimp only [M, A₀, A₁, A₂] at hminorZero hminorOne hminorTwo
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  have htail :
      (∑ i : Fin n,
        (-1 : ℝ) ^ (i.succ.succ.succ : ℕ) *
          M 0 i.succ.succ.succ *
            (M.submatrix Fin.succ i.succ.succ.succ.succAbove).det) = 0 := by
    apply Fintype.sum_eq_zero
    intro i
    rw [htailEntry, mul_zero, zero_mul]
  rw [htail, add_zero, hminorZero, hminorOne, hminorTwo,
    hentryZero, hentryOne, hentryTwo]
  norm_num
  rw [foldLinearAuxMinorZero_det, foldLinearAuxMinorOne_det,
    foldLinearAuxMinorTwo_det]
  simp only [Fin.succAbove_zero]
  have hmod : 2 % (n + 2 + 1) = 2 := Nat.mod_eq_of_lt (by omega)
  rw [hmod]
  norm_num
  ring

/-- The determinant coordinate of an exposed symmetric matrix obeys the
first line of `eq:five-minor-update`, with no invertibility assumption. -/
theorem exposedFoldMinorState_extension_d
    (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hK : K.IsSymm) :
    (exposedFoldMinorState (n + 2) (foldLinearExtension n a x s K)).d =
      (s ^ 2 - x ^ 2) * (exposedFoldMinorState n K).d +
        s * (a ^ 2 * (exposedFoldMinorState n K).p +
          (exposedFoldMinorState n K).q) -
        2 * a * x * (exposedFoldMinorState n K).c +
        a ^ 2 * (exposedFoldMinorState n K).r := by
  let E := foldLinearExtension n a x s K
  let M := foldLinearAuxMinor n a x s K
  have hentryZero : foldLinearExtension n a x s K 0
      (0 : Fin (n + 4)) = -s := by rfl
  have hentryOne : foldLinearExtension n a x s K 0
      (Fin.succ (0 : Fin (n + 3))) = x := by rfl
  have hentryTwo : foldLinearExtension n a x s K 0
      (Fin.succ (0 : Fin (n + 2))).succ = 0 := by rfl
  have hentryThree : foldLinearExtension n a x s K 0
      (Fin.succ (0 : Fin (n + 1))).succ.succ = -1 := by rfl
  have htailEntry (i : Fin n) : E 0 i.succ.succ.succ.succ = 0 := by
    change (if i.succ.succ = (1 : Fin (n + 2)) then -1 else 0) = 0
    rw [if_neg]
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hminorThree : E.submatrix Fin.succ
      (Fin.succ (0 : Fin (n + 1))).succ.succ.succAbove = M := rfl
  have hdeleteZero : E.submatrix Fin.succ Fin.succ =
      singleBorderMatrix (n + 1) (-s) (-a) K := by
    simpa only [Fin.succAbove_zero] using
      foldLinearExtension_delete_zero n a x s K
  have hdeleteCross : E.submatrix Fin.succ
      (Fin.succ (0 : Fin (n + 3))).succAbove =
        crossBorderMatrix n x (-a) (-1) K := by
    simpa only [Fin.succAbove_zero] using
      foldLinearExtension_delete_cross n a x s K
  dsimp only [E, M] at hminorThree hdeleteZero hdeleteCross
  simp only [exposedFoldMinorState]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have htail :
      (∑ i : Fin n,
        (-1 : ℝ) ^ (i.succ.succ.succ.succ : ℕ) *
          E 0 i.succ.succ.succ.succ *
            (E.submatrix Fin.succ
              i.succ.succ.succ.succ.succAbove).det) = 0 := by
    apply Fintype.sum_eq_zero
    intro i
    rw [htailEntry, mul_zero, zero_mul]
  rw [htail, add_zero]
  simp only [Fin.succAbove_zero]
  rw [hdeleteZero, hdeleteCross, hminorThree, hentryZero, hentryOne,
    hentryTwo, hentryThree]
  norm_num
  rw [det_singleBorderMatrix, det_crossBorderMatrix, foldLinearAuxMinor_det]
  have hminor :
      (K.submatrix (1 : Fin (n + 2)).succAbove Fin.succ).det =
        (K.submatrix (0 : Fin (n + 2)).succAbove
          (1 : Fin (n + 2)).succAbove).det := by
    rw [← Matrix.det_transpose]
    congr 1
    ext i j
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply]
    rw [show K ((1 : Fin (n + 2)).succAbove j) (Fin.succ i) =
        K (Fin.succ i) ((1 : Fin (n + 2)).succAbove j) by
      exact congrFun (congrFun hK (Fin.succ i))
        ((1 : Fin (n + 2)).succAbove j)]
    rfl
  rw [hminor]
  have hmod : 2 % (n + 3) = 2 := Nat.mod_eq_of_lt (by omega)
  rw [hmod]
  norm_num
  ring

/-- Adding an exposed folded pair preserves symmetry. -/
theorem foldLinearExtension_isSymm
    (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hK : K.IsSymm) :
    (foldLinearExtension n a x s K).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  refine Fin.cases ?_ (fun i' ↦ ?_) i
  · refine Fin.cases ?_ (fun j' ↦ ?_) j
    · rfl
    · refine Fin.cases ?_ (fun q ↦ ?_) j'
      · rfl
      · rfl
  · refine Fin.cases ?_ (fun p ↦ ?_) i'
    · refine Fin.cases ?_ (fun j' ↦ ?_) j
      · rfl
      · refine Fin.cases ?_ (fun q ↦ ?_) j'
        · rfl
        · rfl
    · refine Fin.cases ?_ (fun j' ↦ ?_) j
      · rfl
      · refine Fin.cases ?_ (fun q ↦ ?_) j'
        · rfl
        · exact Matrix.IsSymm.ext_iff.mp hK p q

/-- The actual five exposed minors of any symmetric old matrix obey the
literal five-minor update. -/
theorem exposedFoldMinorState_extension
    (n : ℕ) (a x s : ℝ)
    (K : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (hK : K.IsSymm) :
    exposedFoldMinorState (n + 2) (foldLinearExtension n a x s K) =
      foldMinorStep a x s (exposedFoldMinorState n K) := by
  apply foldMinorState_ext
  · simpa only [foldMinorStep] using
      exposedFoldMinorState_extension_d n a x s K hK
  · simpa only [foldMinorStep] using
      (exposedFoldMinorState_extension_pr n a x s K).1
  · simpa only [foldMinorStep] using
      exposedFoldMinorState_extension_q n a x s K
  · simpa only [foldMinorStep] using
      exposedFoldMinorState_extension_c n a x s K hK
  · simpa only [foldMinorStep] using
      (exposedFoldMinorState_extension_pr n a x s K).2

/-- Forget the path coordinates and retain only their linear paired-block
coordinates. -/
def evenLinearBlockEquiv (m : ℕ) : Fin (2 * m) ≃ Fin m × Fin 2 :=
  (finCongr (by omega : 2 * m = m * 2)).trans
    (@finProdFinEquiv m 2).symm

@[simp] theorem evenLinearBlockEquiv_zero (m : ℕ) :
    evenLinearBlockEquiv (m + 1) 0 = (0, 0) := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [evenLinearBlockEquiv, finProdFinEquiv]

@[simp] theorem evenLinearBlockEquiv_one (m : ℕ) :
    evenLinearBlockEquiv (m + 1) 1 = (0, 1) := by
  have hlt : 1 < 2 * (m + 1) := by omega
  apply Prod.ext
  · apply Fin.ext
    simp [evenLinearBlockEquiv, finProdFinEquiv,
      Nat.mod_eq_of_lt hlt]
  · apply Fin.ext
    simp [evenLinearBlockEquiv, finProdFinEquiv]

/-- Removing the first linear pair increments the block index and preserves
the within-pair coordinate. -/
theorem evenLinearBlockEquiv_succ_succ (m : ℕ) (i : Fin (2 * m)) :
    evenLinearBlockEquiv (m + 1) i.succ.succ =
      ((evenLinearBlockEquiv m i).1.succ,
        (evenLinearBlockEquiv m i).2) := by
  apply Prod.ext
  · apply Fin.ext
    simp [evenLinearBlockEquiv, finProdFinEquiv]
    omega
  · apply Fin.ext
    simp [evenLinearBlockEquiv, finProdFinEquiv]
    omega

/-- Linear paired reindexing of the even block pencil is exactly the actual
folded even pencil. -/
theorem foldedEvenPencilMatrix_eq_block_reindex
    (m : ℕ) (a x s : ℝ) :
    foldedEvenPencilMatrix m a x s =
      (foldedEvenBlockPencil m a x s).submatrix
        (evenLinearBlockEquiv m) (evenLinearBlockEquiv m) := by
  rfl

/-- In linear paired coordinates the sparse even coupling has precisely the
two entries used by `foldLinearExtension`. -/
theorem foldedEvenCoupling_linear (m : ℕ) (a : ℝ) (b : Fin 2)
    (i : Fin (2 * (m + 1))) :
    foldedEvenCoupling (m + 1) a b (evenLinearBlockEquiv (m + 1) i) =
      Fin.cases (if i = 1 then -1 else 0)
        (fun _ ↦ if i = 0 then -a else 0) b := by
  fin_cases b
  · refine Fin.cases ?_ (fun i' ↦ ?_) i
    · simp [foldedEvenCoupling, foldOffBlock]
    · refine Fin.cases ?_ (fun i ↦ ?_) i'
      · simp [foldedEvenCoupling, foldOffBlock]
      · rw [evenLinearBlockEquiv_succ_succ]
        have hne : i.succ.succ ≠ (1 : Fin (2 * (m + 1))) := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
        simp [foldedEvenCoupling, hne]
  · refine Fin.cases ?_ (fun i' ↦ ?_) i
    · simp [foldedEvenCoupling, foldOffBlock]
    · refine Fin.cases ?_ (fun i ↦ ?_) i'
      · simp [foldedEvenCoupling, foldOffBlock]
      · rw [evenLinearBlockEquiv_succ_succ]
        simp [foldedEvenCoupling]

/-- Split a linear even folded matrix into its new exposed pair and the old
linear tail. -/
def evenLinearExtensionIndex (m : ℕ) :
    Fin (2 * m + 4) → Fin 2 ⊕ (Fin (m + 1) × Fin 2) :=
  Fin.cases (Sum.inl 0) (fun i' ↦
    Fin.cases (Sum.inl 1)
      (fun i ↦ Sum.inr (evenLinearBlockEquiv (m + 1) i)) i')

/-- The block-extension index following the linear split is the canonical
linear block coordinate of the larger pencil. -/
theorem evenBlockExtensionIndex_linear (m : ℕ) (i : Fin (2 * m + 4)) :
    evenBlockExtensionIndex (m + 1) (evenLinearExtensionIndex m i) =
      evenLinearBlockEquiv (m + 2) i := by
  refine Fin.cases ?_ (fun i' ↦ ?_) i
  · simp [evenLinearExtensionIndex, evenBlockExtensionIndex]
  · refine Fin.cases ?_ (fun i ↦ ?_) i'
    · simp [evenLinearExtensionIndex, evenBlockExtensionIndex]
    · simp [evenLinearExtensionIndex, evenBlockExtensionIndex,
        evenLinearBlockEquiv_succ_succ]

/-- The actual even folded pencils grow by the literal linear extension used
in the universal five-minor calculation. -/
theorem foldedEvenExposedMatrix_succ (m : ℕ) (a x s : ℝ) :
    foldedEvenExposedMatrix (m + 1) a x s =
      foldLinearExtension (2 * m) a x s
        (foldedEvenExposedMatrix m a x s) := by
  let f := evenLinearExtensionIndex m
  have H :
      (foldedEvenBlockPencil (m + 2) a x s).submatrix
          (evenBlockExtensionIndex (m + 1))
          (evenBlockExtensionIndex (m + 1)) =
        Matrix.fromBlocks (foldInteriorBlock x s)
          (foldedEvenCoupling (m + 1) a)
          (foldedEvenCoupling (m + 1) a)ᵀ
          (foldedEvenBlockPencil (m + 1) a x s) := by
    simpa only [show m + 1 + 1 = m + 2 by omega] using
      foldedEvenBlockPencil_extension (m + 1) (by omega) a x s
  have Hsub := congrArg (fun M ↦ M.submatrix f f) H
  calc
    foldedEvenExposedMatrix (m + 1) a x s =
        ((foldedEvenBlockPencil (m + 2) a x s).submatrix
          (evenBlockExtensionIndex (m + 1))
          (evenBlockExtensionIndex (m + 1))).submatrix f f := by
      ext i j
      simp only [Matrix.submatrix_apply, foldedEvenExposedMatrix,
        foldedEvenPencilMatrix_eq_block_reindex, f,
        evenBlockExtensionIndex_linear]
      apply congrArg₂ (foldedEvenBlockPencil (m + 2) a x s)
      · apply Prod.ext
        · apply Fin.ext
          rfl
        · apply Fin.ext
          rfl
      · apply Prod.ext
        · apply Fin.ext
          rfl
        · apply Fin.ext
          rfl
    _ = (Matrix.fromBlocks (foldInteriorBlock x s)
          (foldedEvenCoupling (m + 1) a)
          (foldedEvenCoupling (m + 1) a)ᵀ
          (foldedEvenBlockPencil (m + 1) a x s)).submatrix f f := Hsub
    _ = foldLinearExtension (2 * m) a x s
        (foldedEvenExposedMatrix m a x s) := by
      ext i j
      refine Fin.cases ?_ (fun i' ↦ ?_) i
      · refine Fin.cases ?_ (fun j' ↦ ?_) j
        · simp [f, evenLinearExtensionIndex, foldLinearExtension,
            foldInteriorBlock]
        · refine Fin.cases ?_ (fun q ↦ ?_) j'
          · simp [f, evenLinearExtensionIndex, foldLinearExtension,
              foldInteriorBlock]
          · simp [f, evenLinearExtensionIndex, foldLinearExtension,
              foldedEvenCoupling_linear]
      · refine Fin.cases ?_ (fun p ↦ ?_) i'
        · refine Fin.cases ?_ (fun j' ↦ ?_) j
          · simp [f, evenLinearExtensionIndex, foldLinearExtension,
              foldInteriorBlock]
          · refine Fin.cases ?_ (fun q ↦ ?_) j'
            · simp [f, evenLinearExtensionIndex, foldLinearExtension,
                foldInteriorBlock]
            · simp [f, evenLinearExtensionIndex, foldLinearExtension,
                foldedEvenCoupling_linear]
        · refine Fin.cases ?_ (fun j' ↦ ?_) j
          · simp [f, evenLinearExtensionIndex, foldLinearExtension,
              foldedEvenCoupling_linear]
          · refine Fin.cases ?_ (fun q ↦ ?_) j'
            · simp [f, evenLinearExtensionIndex, foldLinearExtension,
                foldedEvenCoupling_linear]
            · simp only [Matrix.submatrix_apply, f,
                evenLinearExtensionIndex, foldLinearExtension,
                foldedEvenExposedMatrix,
                foldedEvenPencilMatrix_eq_block_reindex]
              apply congrArg₂ (foldedEvenBlockPencil (m + 1) a x s)
              · apply Prod.ext
                · apply Fin.ext
                  rfl
                · apply Fin.ext
                  rfl
              · apply Prod.ext
                · apply Fin.ext
                  rfl
                · apply Fin.ext
                  rfl

/-- Every actual even exposed folded pencil is symmetric. -/
theorem foldedEvenExposedMatrix_isSymm (m : ℕ) (a x s : ℝ) :
    (foldedEvenExposedMatrix m a x s).IsSymm := by
  exact Matrix.IsSymm.submatrix
    (((signedMiddleMatrix_isSymm (2 * (m + 1)) a x).sub
      (Matrix.isSymm_one.smul s)).submatrix (evenPairedPermutation (m + 1)))
    (finCongr (by omega))

/-- The five actual even minors follow the literal folded-minor step. -/
theorem foldedEvenActualState_succ (m : ℕ) (a x s : ℝ) :
    foldedEvenActualState (m + 1) a x s =
      foldMinorStep a x s (foldedEvenActualState m a x s) := by
  rw [foldedEvenActualState, foldedEvenExposedMatrix_succ]
  simpa only [show 2 * (m + 1) = 2 * m + 2 by omega] using
    exposedFoldMinorState_extension (2 * m) a x s
      (foldedEvenExposedMatrix m a x s)
      (foldedEvenExposedMatrix_isSymm m a x s)

/-- Linear paired blocks followed by the central coordinate in odd order. -/
def oddLinearBlockEquiv (m : ℕ) :
    Fin (2 * m + 1) ≃ (Fin m × Fin 2) ⊕ Fin 1 :=
  (finCongr (by omega : 2 * m + 1 = m * 2 + 1)).trans
    (@finSumFinEquiv (m * 2) 1).symm |>.trans
      (Equiv.sumCongr (@finProdFinEquiv m 2).symm (Equiv.refl (Fin 1)))

@[simp] theorem oddLinearBlockEquiv_zero (m : ℕ) :
    oddLinearBlockEquiv (m + 1) 0 = Sum.inl (0, 0) := by
  apply (oddLinearBlockEquiv (m + 1)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  simp [oddLinearBlockEquiv, finProdFinEquiv]

@[simp] theorem oddLinearBlockEquiv_one (m : ℕ) :
    oddLinearBlockEquiv (m + 1) 1 = Sum.inl (0, 1) := by
  apply (oddLinearBlockEquiv (m + 1)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Fin.ext
  have hdim : 2 * (m + 1) + 1 = (m + 1) * 2 + 1 := by omega
  simp [oddLinearBlockEquiv, finProdFinEquiv, hdim]

/-- Removing the first odd linear pair applies the block-tail embedding. -/
theorem oddLinearBlockEquiv_succ_succ (m : ℕ) (i : Fin (2 * m + 1)) :
    oddLinearBlockEquiv (m + 1) i.succ.succ =
      oddBlockTailEmbedding m (oddLinearBlockEquiv m i) := by
  apply (oddLinearBlockEquiv (m + 1)).symm.injective
  rw [Equiv.symm_apply_apply]
  generalize hp : oddLinearBlockEquiv m i = p
  have hi : (oddLinearBlockEquiv m).symm p = i := by
    rw [← hp, Equiv.symm_apply_apply]
  rcases p with p | c
  · rcases p with ⟨k, b⟩
    apply Fin.ext
    have hiv := congrArg Fin.val hi
    simp [oddLinearBlockEquiv, oddBlockTailEmbedding,
      finProdFinEquiv] at hiv ⊢
    omega
  · have hc : c = 0 := Subsingleton.elim _ _
    subst c
    apply Fin.ext
    have hiv := congrArg Fin.val hi
    simp [oddLinearBlockEquiv, oddBlockTailEmbedding,
      finProdFinEquiv] at hiv ⊢
    omega

/-- Linear paired reindexing of the odd block pencil is exactly the actual
folded odd pencil. -/
theorem foldedOddPencilMatrix_eq_block_reindex
    (m : ℕ) (a x s : ℝ) :
    foldedOddPencilMatrix m a x s =
      (foldedOddBlockPencil m a x s).submatrix
        (oddLinearBlockEquiv m) (oddLinearBlockEquiv m) := by
  rfl

/-- In odd linear paired coordinates the sparse coupling is the same
two-entry coupling as in even order. -/
theorem foldedOddCoupling_linear (m : ℕ) (a : ℝ) (b : Fin 2)
    (i : Fin (2 * (m + 1) + 1)) :
    foldedOddCoupling (m + 1) a b (oddLinearBlockEquiv (m + 1) i) =
      Fin.cases (if i = 1 then -1 else 0)
        (fun _ ↦ if i = 0 then -a else 0) b := by
  fin_cases b
  · refine Fin.cases ?_ (fun i' ↦ ?_) i
    · simp [foldedOddCoupling, foldOffBlock]
    · refine Fin.cases ?_ (fun i ↦ ?_) i'
      · simp [foldedOddCoupling, foldOffBlock]
      · rw [oddLinearBlockEquiv_succ_succ]
        have hne : i.succ.succ ≠ (1 : Fin (2 * (m + 1) + 1)) := by
          intro h
          have hv := congrArg Fin.val h
          simp at hv
        rcases htail : oddLinearBlockEquiv m i with p | c
        · simp [oddBlockTailEmbedding, foldedOddCoupling, hne]
        · simp [oddBlockTailEmbedding, foldedOddCoupling, hne]
  · refine Fin.cases ?_ (fun i' ↦ ?_) i
    · simp [foldedOddCoupling, foldOffBlock]
    · refine Fin.cases ?_ (fun i ↦ ?_) i'
      · simp [foldedOddCoupling, foldOffBlock]
      · rw [oddLinearBlockEquiv_succ_succ]
        rcases htail : oddLinearBlockEquiv m i with p | c
        · simp [oddBlockTailEmbedding, foldedOddCoupling]
        · simp [oddBlockTailEmbedding, foldedOddCoupling]

/-- The signed five-minor iteration is the actual even minor state. -/
theorem foldedEvenActualState_signed_orbit (m : ℕ) (a x s : ℝ) :
    foldSignedOrbit a x s (foldEvenSeed a) (m + 1) =
      foldMinorScale ((-1 : ℝ) ^ (m + 1)) (foldedEvenActualState m a x s) := by
  induction m with
  | zero =>
      simpa [foldSignedOrbit, foldedEvenActualState_zero] using
        foldSignedStep_evenSeed a x s
  | succ m ih =>
      rw [foldSignedOrbit, ih, foldSignedStep_scale, foldedEvenActualState_succ]
      congr 1
      rw [pow_succ]
      ring

/-- The actual even determinant is the first coordinate of its minor orbit. -/
theorem foldedEvenActualState_signed_d_eq_sequence
    {a x s : ℝ} (m : ℕ) :
    (-1 : ℝ) ^ (m + 1) * (foldedEvenActualState m a x s).d =
      foldEvenSequence a x s (m + 1) := by
  rw [foldEvenSequence, foldedEvenActualState_signed_orbit]
  rfl

/-- For every even order, the actual signed-pencil determinant is the first
coordinate of the even folded minor orbit. -/
theorem signedPencilDet_even_eq_foldEvenSequence
    {a x s : ℝ} (m : ℕ) :
    signedPencilDet (2 * m) a x s = foldEvenSequence a x s m := by
  cases m with
  | zero =>
      rw [signedPencilDet_even_eq_signed_folded_det,
        foldedEvenPencilMatrix_zero_det, foldEvenSequence_zero]
      norm_num
  | succ m =>
      rw [signedPencilDet_even_eq_signed_folded_det]
      rw [← foldedEvenActualState_d]
      exact foldedEvenActualState_signed_d_eq_sequence m

/-- Split a linear odd folded matrix into its new exposed pair and its old
linear odd tail. -/
def oddLinearExtensionIndex (m : ℕ) :
    Fin (2 * m + 5) → Fin 2 ⊕ ((Fin (m + 1) × Fin 2) ⊕ Fin 1) :=
  Fin.cases (Sum.inl 0) (fun i' ↦
    Fin.cases (Sum.inl 1)
      (fun i ↦ Sum.inr (oddLinearBlockEquiv (m + 1) i)) i')

/-- The odd block-extension index following the linear split is the
canonical linear coordinate of the larger odd pencil. -/
theorem oddBlockExtensionIndex_linear (m : ℕ) (i : Fin (2 * m + 5)) :
    oddBlockExtensionIndex (m + 1) (oddLinearExtensionIndex m i) =
      oddLinearBlockEquiv (m + 2) i := by
  refine Fin.cases ?_ (fun i' ↦ ?_) i
  · simp [oddLinearExtensionIndex, oddBlockExtensionIndex]
  · refine Fin.cases ?_ (fun i ↦ ?_) i'
    · simp [oddLinearExtensionIndex, oddBlockExtensionIndex]
    · simp [oddLinearExtensionIndex, oddBlockExtensionIndex,
        oddLinearBlockEquiv_succ_succ]

/-- The actual odd folded pencils grow by the same literal linear extension
as the even pencils. -/
theorem foldedOddExposedMatrix_succ (m : ℕ) (a x s : ℝ) :
    foldedOddExposedMatrix (m + 1) a x s =
      foldLinearExtension (2 * m + 1) a x s
        (foldedOddExposedMatrix m a x s) := by
  let f := oddLinearExtensionIndex m
  have H :
      (foldedOddBlockPencil (m + 2) a x s).submatrix
          (oddBlockExtensionIndex (m + 1))
          (oddBlockExtensionIndex (m + 1)) =
        Matrix.fromBlocks (foldInteriorBlock x s)
          (foldedOddCoupling (m + 1) a)
          (foldedOddCoupling (m + 1) a)ᵀ
          (foldedOddBlockPencil (m + 1) a x s) := by
    simpa only [show m + 1 + 1 = m + 2 by omega] using
      foldedOddBlockPencil_extension (m + 1) (by omega) a x s
  have Hsub := congrArg (fun M ↦ M.submatrix f f) H
  calc
    foldedOddExposedMatrix (m + 1) a x s =
        ((foldedOddBlockPencil (m + 2) a x s).submatrix
          (oddBlockExtensionIndex (m + 1))
          (oddBlockExtensionIndex (m + 1))).submatrix f f := by
      ext i j
      simp only [Matrix.submatrix_apply, foldedOddExposedMatrix,
        foldedOddPencilMatrix_eq_block_reindex, f,
        oddBlockExtensionIndex_linear]
      apply congrArg₂ (foldedOddBlockPencil (m + 2) a x s)
      · apply (oddLinearBlockEquiv (m + 2)).symm.injective
        apply Fin.ext
        rfl
      · apply (oddLinearBlockEquiv (m + 2)).symm.injective
        apply Fin.ext
        rfl
    _ = (Matrix.fromBlocks (foldInteriorBlock x s)
          (foldedOddCoupling (m + 1) a)
          (foldedOddCoupling (m + 1) a)ᵀ
          (foldedOddBlockPencil (m + 1) a x s)).submatrix f f := Hsub
    _ = foldLinearExtension (2 * m + 1) a x s
        (foldedOddExposedMatrix m a x s) := by
      ext i j
      refine Fin.cases ?_ (fun i' ↦ ?_) i
      · refine Fin.cases ?_ (fun j' ↦ ?_) j
        · simp [f, oddLinearExtensionIndex, foldLinearExtension,
            foldInteriorBlock]
        · refine Fin.cases ?_ (fun q ↦ ?_) j'
          · simp [f, oddLinearExtensionIndex, foldLinearExtension,
              foldInteriorBlock]
          · simp [f, oddLinearExtensionIndex, foldLinearExtension,
              foldedOddCoupling_linear]
      · refine Fin.cases ?_ (fun p ↦ ?_) i'
        · refine Fin.cases ?_ (fun j' ↦ ?_) j
          · simp [f, oddLinearExtensionIndex, foldLinearExtension,
              foldInteriorBlock]
          · refine Fin.cases ?_ (fun q ↦ ?_) j'
            · simp [f, oddLinearExtensionIndex, foldLinearExtension,
                foldInteriorBlock]
            · simp [f, oddLinearExtensionIndex, foldLinearExtension,
                foldedOddCoupling_linear]
        · refine Fin.cases ?_ (fun j' ↦ ?_) j
          · simp [f, oddLinearExtensionIndex, foldLinearExtension,
              foldedOddCoupling_linear]
          · refine Fin.cases ?_ (fun q ↦ ?_) j'
            · simp [f, oddLinearExtensionIndex, foldLinearExtension,
                foldedOddCoupling_linear]
            · simp only [Matrix.submatrix_apply, f,
                oddLinearExtensionIndex, foldLinearExtension,
                foldedOddExposedMatrix,
                foldedOddPencilMatrix_eq_block_reindex]
              apply congrArg₂ (foldedOddBlockPencil (m + 1) a x s)
              · apply (oddLinearBlockEquiv (m + 1)).symm.injective
                apply Fin.ext
                rfl
              · apply (oddLinearBlockEquiv (m + 1)).symm.injective
                apply Fin.ext
                rfl

/-- Every actual odd exposed folded pencil is symmetric. -/
theorem foldedOddExposedMatrix_isSymm (m : ℕ) (a x s : ℝ) :
    (foldedOddExposedMatrix m a x s).IsSymm := by
  exact Matrix.IsSymm.submatrix
    (((signedMiddleMatrix_isSymm (2 * (m + 1) + 1) a x).sub
      (Matrix.isSymm_one.smul s)).submatrix (oddPairedPermutation (m + 1)))
    (finCongr (by omega))

/-- The five actual odd minors follow the literal folded-minor step. -/
theorem foldedOddActualState_succ (m : ℕ) (a x s : ℝ) :
    foldedOddActualState (m + 1) a x s =
      foldMinorStep a x s (foldedOddActualState m a x s) := by
  rw [foldedOddActualState, foldedOddExposedMatrix_succ]
  simpa only [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega] using
    exposedFoldMinorState_extension (2 * m + 1) a x s
      (foldedOddExposedMatrix m a x s)
      (foldedOddExposedMatrix_isSymm m a x s)

/-- The signed five-minor iteration is the actual odd minor state. -/
theorem foldedOddActualState_signed_orbit (m : ℕ) (a x s : ℝ) :
    foldSignedOrbit a x s (foldOddSeed x s) (m + 1) =
      foldMinorScale ((-1 : ℝ) ^ (m + 1)) (foldedOddActualState m a x s) := by
  induction m with
  | zero =>
      simpa [foldSignedOrbit, foldedOddActualState_zero] using
        foldSignedStep_oddSeed a x s
  | succ m ih =>
      rw [foldSignedOrbit, ih, foldSignedStep_scale, foldedOddActualState_succ]
      congr 1
      rw [pow_succ]
      ring

/-- The actual odd determinant is the first coordinate of its minor orbit. -/
theorem foldedOddActualState_signed_d_eq_sequence
    {a x s : ℝ} (m : ℕ) :
    (-1 : ℝ) ^ (m + 1) * (foldedOddActualState m a x s).d =
      foldOddSequence a x s (m + 1) := by
  rw [foldOddSequence, foldedOddActualState_signed_orbit]
  rfl

/-- For every odd order, the actual signed-pencil determinant is the first
coordinate of the odd folded minor orbit. -/
theorem signedPencilDet_odd_eq_foldOddSequence
    {a x s : ℝ} (m : ℕ) :
    signedPencilDet (2 * m + 1) a x s = foldOddSequence a x s m := by
  cases m with
  | zero =>
      rw [signedPencilDet_odd_eq_signed_folded_det,
        foldedOddPencilMatrix_zero_det, foldOddSequence_zero]
      norm_num
  | succ m =>
      rw [signedPencilDet_odd_eq_signed_folded_det]
      rw [← foldedOddActualState_d]
      exact foldedOddActualState_signed_d_eq_sequence m

end

end ConnectedPseudospectrum
