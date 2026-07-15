import ConnectedPseudospectrum.CentralBidiagonal
import ConnectedPseudospectrum.SignedPencil
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# The value at the centre of an even spectral gap

This module formalizes the block calculation in lines 1420--1436 of the
immutable source.  Odd and even path coordinates turn `A_(2m)` into a block
off-diagonal matrix.  Its lower-left block is the actual central bidiagonal
matrix, while a rank-one Gram comparison shows that the other block has no
smaller least singular value.
-/

namespace ConnectedPseudospectrum

open Matrix
open scoped ComplexOrder

noncomputable section

/-! ## The odd/even coordinate permutation -/

/-- A pair with a two-valued side coordinate is the corresponding sum. -/
private def centralPairSumEquiv (m : ℕ) :
    Fin m × Fin 2 ≃ Fin m ⊕ Fin m where
  toFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  invFun q := Sum.elim (fun i ↦ (i, 0)) (fun i ↦ (i, 1)) q
  left_inv p := by
    rcases p with ⟨i, j⟩
    fin_cases j <;> rfl
  right_inv q := by
    rcases q with i | i <;> rfl

/-- The ordinary contiguous two-block ordering. -/
def centralTwoBlockEquiv (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  (@finSumFinEquiv m m).trans (finCongr (by omega))

/-- The parity ordering: left coordinates are `2i`, right coordinates are
`2i+1`. -/
def evenOddBlockEquiv (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  (centralPairSumEquiv m).symm |>.trans
    ((@finProdFinEquiv m 2).trans (finCongr (by omega)))

@[simp] theorem centralTwoBlockEquiv_inl_val (m : ℕ) (i : Fin m) :
    (centralTwoBlockEquiv m (Sum.inl i)).1 = i.1 := by
  simp [centralTwoBlockEquiv]

@[simp] theorem centralTwoBlockEquiv_inr_val (m : ℕ) (i : Fin m) :
    (centralTwoBlockEquiv m (Sum.inr i)).1 = m + i.1 := by
  simp [centralTwoBlockEquiv, Nat.add_comm]

@[simp] theorem evenOddBlockEquiv_inl_val (m : ℕ) (i : Fin m) :
    (evenOddBlockEquiv m (Sum.inl i)).1 = 2 * i.1 := by
  simp [evenOddBlockEquiv, centralPairSumEquiv, finProdFinEquiv]

@[simp] theorem evenOddBlockEquiv_inr_val (m : ℕ) (i : Fin m) :
    (evenOddBlockEquiv m (Sum.inr i)).1 = 2 * i.1 + 1 := by
  simp [evenOddBlockEquiv, centralPairSumEquiv, finProdFinEquiv]
  omega

/-- The permutation from contiguous block coordinates to the original
interlaced path coordinates. -/
def evenOddPermutation (m : ℕ) : Equiv.Perm (Fin (2 * m)) :=
  (centralTwoBlockEquiv m).symm.trans (evenOddBlockEquiv m)

@[simp] theorem evenOddPermutation_twoBlock_inl_val
    (m : ℕ) (i : Fin m) :
    (evenOddPermutation m (centralTwoBlockEquiv m (Sum.inl i))).1 =
      2 * i.1 := by
  simp [evenOddPermutation]

@[simp] theorem evenOddPermutation_twoBlock_inr_val
    (m : ℕ) (i : Fin m) :
    (evenOddPermutation m (centralTwoBlockEquiv m (Sum.inr i))).1 =
      2 * i.1 + 1 := by
  simp [evenOddPermutation]

/-! ## Least singular values and coordinate permutations -/

/-- A complex permutation matrix is unitary. -/
theorem complexPermMatrix_mem_unitary {n : ℕ}
    (e : Equiv.Perm (Fin n)) :
    e.permMatrix ℂ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  change e.permMatrix ℂ * (e.permMatrix ℂ)ᴴ = 1
  rw [Matrix.conjTranspose_permMatrix]
  calc
    e.permMatrix ℂ * (e⁻¹).permMatrix ℂ =
        (e⁻¹ * e).permMatrix ℂ := by
      rw [Matrix.permMatrix_mul]
    _ = 1 := by simp

/-- Simultaneous row and column permutation is unitary conjugation. -/
theorem submatrix_perm_eq_perm_conjugate {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (e : Equiv.Perm (Fin n)) :
    M.submatrix e e =
      e.permMatrix ℂ * M * (e.permMatrix ℂ)ᴴ := by
  rw [Matrix.conjTranspose_permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  rfl

/-- The project's attained Euclidean least singular value is invariant under
simultaneous coordinate permutation. -/
theorem leastSingularValue_submatrix_perm {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (e : Equiv.Perm (Fin n)) :
    leastSingularValue (M.submatrix e e) = leastSingularValue M := by
  let P : Matrix (Fin n) (Fin n) ℂ := e.permMatrix ℂ
  have hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    complexPermMatrix_mem_unitary e
  have hPstar : Pᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    Unitary.star_mem hP
  rw [submatrix_perm_eq_perm_conjugate]
  calc
    leastSingularValue (P * M * Pᴴ) =
        leastSingularValue (P * M) :=
      leastSingularValue_mul_unitary (P * M) Pᴴ hPstar
    _ = leastSingularValue M :=
      leastSingularValue_unitary_mul P M hP

/-! ## The two bidiagonal blocks -/

/-- The upper-right block `I_m+aV_mᵀ` in the source. -/
def complexCentralCompanion (m : ℕ) (a : ℝ) :
    Matrix (Fin m) (Fin m) ℂ :=
  1 + (a : ℂ) • complexLowerShift m

@[simp] theorem complexCentralCompanion_apply (m : ℕ) (a : ℝ)
    (i j : Fin m) :
    complexCentralCompanion m a i j =
      (if i = j then 1 else 0) +
        (a : ℂ) * (if i.1 = j.1 + 1 then 1 else 0) := by
  simp [complexCentralCompanion, complexLowerShift, Matrix.one_apply]

theorem complexCentralBidiagonal_eq_shifts (m : ℕ) (a : ℝ) :
    complexCentralBidiagonal m a =
      (a : ℂ) • 1 + complexUpperShift m := by
  ext i j
  simp [complexCentralBidiagonal_apply, complexUpperShift,
    Matrix.one_apply]

/-- The source's block off-diagonal matrix in sum coordinates. -/
def evenCentralOffDiagonal (m : ℕ) (a : ℝ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  Matrix.fromBlocks 0 (complexCentralCompanion m a)
    (complexCentralBidiagonal m a) 0

/-- The same block matrix on the project's ordinary `Fin (2m)` Euclidean
coordinate space. -/
def evenCentralOffDiagonalFin (m : ℕ) (a : ℝ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
  (evenCentralOffDiagonal m a).submatrix
    (centralTwoBlockEquiv m).symm (centralTwoBlockEquiv m).symm

/-- Odd/even coordinates give exactly the displayed block matrix. -/
theorem complexPathMatrix_evenOddBlock (m : ℕ) (a : ℝ) :
    (complexPathMatrix (2 * m) a).submatrix
        (evenOddBlockEquiv m) (evenOddBlockEquiv m) =
      evenCentralOffDiagonal m a := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Matrix.submatrix_apply, complexPathMatrix_apply,
      pathMatrix_apply, evenOddBlockEquiv_inl_val,
      evenCentralOffDiagonal, Matrix.fromBlocks_apply₁₁,
      Matrix.zero_apply]
    push_cast
    split_ifs <;> (first | omega | norm_num)
  · simp only [Matrix.submatrix_apply, complexPathMatrix_apply,
      pathMatrix_apply, evenOddBlockEquiv_inl_val,
      evenOddBlockEquiv_inr_val, evenCentralOffDiagonal,
      Matrix.fromBlocks_apply₁₂, complexCentralCompanion_apply]
    push_cast
    split_ifs <;> (first | omega | norm_num)
  · simp only [Matrix.submatrix_apply, complexPathMatrix_apply,
      pathMatrix_apply, evenOddBlockEquiv_inr_val,
      evenOddBlockEquiv_inl_val, evenCentralOffDiagonal,
      Matrix.fromBlocks_apply₂₁, complexCentralBidiagonal_apply]
    push_cast
    split_ifs <;> (first | omega | norm_num)
  · simp only [Matrix.submatrix_apply, complexPathMatrix_apply,
      pathMatrix_apply, evenOddBlockEquiv_inr_val,
      evenCentralOffDiagonal, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply]
    push_cast
    split_ifs <;> (first | omega | norm_num)

/-- Ordinary `Fin` coordinates express the displayed relation as a literal
permutation similarity. -/
theorem complexPathMatrix_evenOddPermutation (m : ℕ) (a : ℝ) :
    (complexPathMatrix (2 * m) a).submatrix
        (evenOddPermutation m) (evenOddPermutation m) =
      evenCentralOffDiagonalFin m a := by
  have hblock := complexPathMatrix_evenOddBlock m a
  ext i j
  have hij := congrArg
    (fun M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ ↦
      M ((centralTwoBlockEquiv m).symm i)
        ((centralTwoBlockEquiv m).symm j)) hblock
  simpa [evenCentralOffDiagonalFin, evenOddPermutation,
    Matrix.submatrix_apply] using hij

theorem leastSingularValue_complexPathMatrix_eq_evenCentralOffDiagonal
    (m : ℕ) (a : ℝ) :
    leastSingularValue (complexPathMatrix (2 * m) a) =
      leastSingularValue (evenCentralOffDiagonalFin m a) := by
  rw [← complexPathMatrix_evenOddPermutation]
  symm
  exact leastSingularValue_submatrix_perm
    (complexPathMatrix (2 * m) a) (evenOddPermutation m)

/-! ## The rank-one Gram comparison -/

/-- Projector onto the last coordinate.  Its definition also makes sense in
dimension zero. -/
def centralLastProjector (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.diagonal fun i ↦ if i.1 + 1 = m then 1 else 0

theorem centralLastProjector_posSemidef (m : ℕ) :
    (centralLastProjector m).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  by_cases h : i.1 + 1 = m <;> simp [h]

private theorem complexReversal_mul_self (m : ℕ) :
    complexReversal m * complexReversal m = 1 := by
  have hunit := Matrix.mem_unitaryGroup_iff.mp
    (complexReversal_mem_unitary m)
  simpa only [complexReversal_star] using hunit

private theorem complexUpperShift_mul_reversal (m : ℕ) :
    complexUpperShift m * complexReversal m =
      complexReversal m * complexLowerShift m := by
  change (upperShift m).map Complex.ofRealHom *
      (reversal m).map Complex.ofRealHom =
    (reversal m).map Complex.ofRealHom *
      (lowerShift m).map Complex.ofRealHom
  rw [← Matrix.map_mul, ← Matrix.map_mul, upperShift_mul_reversal]

private theorem complexLowerShift_mul_reversal (m : ℕ) :
    complexLowerShift m * complexReversal m =
      complexReversal m * complexUpperShift m := by
  change (lowerShift m).map Complex.ofRealHom *
      (reversal m).map Complex.ofRealHom =
    (reversal m).map Complex.ofRealHom *
      (upperShift m).map Complex.ofRealHom
  rw [← Matrix.map_mul, ← Matrix.map_mul, lowerShift_mul_reversal]

private theorem complexReversal_conjugate_upper (m : ℕ) :
    complexReversal m * complexUpperShift m * complexReversal m =
      complexLowerShift m := by
  calc
    complexReversal m * complexUpperShift m * complexReversal m =
        complexReversal m *
          (complexUpperShift m * complexReversal m) := by
      rw [Matrix.mul_assoc]
    _ = complexReversal m *
        (complexReversal m * complexLowerShift m) := by
      rw [complexUpperShift_mul_reversal]
    _ = (complexReversal m * complexReversal m) *
        complexLowerShift m := by
      rw [Matrix.mul_assoc]
    _ = complexLowerShift m := by
      rw [complexReversal_mul_self, Matrix.one_mul]

private theorem complexReversal_conjugate_lower (m : ℕ) :
    complexReversal m * complexLowerShift m * complexReversal m =
      complexUpperShift m := by
  calc
    complexReversal m * complexLowerShift m * complexReversal m =
        complexReversal m *
          (complexLowerShift m * complexReversal m) := by
      rw [Matrix.mul_assoc]
    _ = complexReversal m *
        (complexReversal m * complexUpperShift m) := by
      rw [complexLowerShift_mul_reversal]
    _ = (complexReversal m * complexReversal m) *
        complexUpperShift m := by
      rw [Matrix.mul_assoc]
    _ = complexUpperShift m := by
      rw [complexReversal_mul_self, Matrix.one_mul]

private theorem complexReversal_conjugate_mul
    (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℂ) :
    complexReversal m * (A * B) * complexReversal m =
      (complexReversal m * A * complexReversal m) *
        (complexReversal m * B * complexReversal m) := by
  let J := complexReversal m
  have hJ : J * J = 1 := complexReversal_mul_self m
  calc
    J * (A * B) * J = (J * A) * (B * J) := by
      noncomm_ring
    _ = (J * A) * 1 * (B * J) := by simp
    _ = (J * A) * (J * J) * (B * J) := by rw [hJ]
    _ = (J * A * J) * (J * B * J) := by
      noncomm_ring

private theorem one_sub_complexUpper_mul_lower_eq_lastProjector (m : ℕ) :
    (1 : Matrix (Fin m) (Fin m) ℂ) -
        complexUpperShift m * complexLowerShift m =
      centralLastProjector m := by
  ext i j
  rw [Matrix.sub_apply, complexUpperShift_mul_lowerShift_apply]
  simp only [Matrix.one_apply, centralLastProjector,
    Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    by_cases hi : i.1 + 1 < m
    · have hne : i.1 + 1 ≠ m := by omega
      simp [hi, hne]
    · have heq : i.1 + 1 = m := by omega
      simp [heq]
  · simp [hij]

/-- The exact Gram rank-one identity on lines 1427--1430. -/
theorem complexCentralCompanion_gram_sub_reversed_central_gram
    (m : ℕ) (a : ℝ) :
    (complexCentralCompanion m a)ᴴ * complexCentralCompanion m a -
        complexReversal m *
          ((complexCentralBidiagonal m a)ᴴ *
            complexCentralBidiagonal m a) * complexReversal m =
      (1 - a ^ 2 : ℝ) • centralLastProjector m := by
  let U := complexUpperShift m
  let L := complexLowerShift m
  let J := complexReversal m
  have hC : complexCentralBidiagonal m a = (a : ℂ) • 1 + U :=
    complexCentralBidiagonal_eq_shifts m a
  have hD : complexCentralCompanion m a = 1 + (a : ℂ) • L := rfl
  have hCgram :
      (complexCentralBidiagonal m a)ᴴ *
          complexCentralBidiagonal m a =
        (a ^ 2 : ℂ) • 1 + (a : ℂ) • U +
          (a : ℂ) • L + L * U := by
    have hCstar :
        (complexCentralBidiagonal m a)ᴴ = (a : ℂ) • 1 + L := by
      rw [hC, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one, complexUpperShift_conjTranspose]
      simp [L]
    rw [hCstar, hC]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    simp only [smul_add, smul_smul]
    rw [← pow_two]
    abel
  have hDgram :
      (complexCentralCompanion m a)ᴴ * complexCentralCompanion m a =
        1 + (a : ℂ) • L + (a : ℂ) • U +
          (a ^ 2 : ℂ) • (U * L) := by
    have hDstar :
        (complexCentralCompanion m a)ᴴ = 1 + (a : ℂ) • U := by
      rw [hD, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one, complexLowerShift_conjTranspose]
      simp [U]
    rw [hDstar, hD]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    simp only [smul_add, smul_smul]
    rw [← pow_two]
    abel
  have hJULJ : J * (L * U) * J = U * L := by
    rw [complexReversal_conjugate_mul,
      complexReversal_conjugate_lower,
      complexReversal_conjugate_upper]
  have hJJ : J * J = 1 := complexReversal_mul_self m
  have hJUJ : J * U * J = L := complexReversal_conjugate_upper m
  have hJLJ : J * L * J = U := complexReversal_conjugate_lower m
  have hJCgram :
      J * ((complexCentralBidiagonal m a)ᴴ *
          complexCentralBidiagonal m a) * J =
        (a ^ 2 : ℂ) • 1 + (a : ℂ) • L +
          (a : ℂ) • U + U * L := by
    rw [hCgram]
    calc
      J * ((a ^ 2 : ℂ) • 1 + (a : ℂ) • U +
          (a : ℂ) • L + L * U) * J =
          (a ^ 2 : ℂ) • (J * 1 * J) +
            (a : ℂ) • (J * U * J) +
            (a : ℂ) • (J * L * J) + J * (L * U) * J := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
          Matrix.smul_mul]
      _ = (a ^ 2 : ℂ) • 1 + (a : ℂ) • L +
          (a : ℂ) • U + U * L := by
        rw [Matrix.mul_one, hJJ, hJUJ, hJLJ, hJULJ]
  rw [hDgram, hJCgram, ← one_sub_complexUpper_mul_lower_eq_lastProjector]
  dsimp only [U, L]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.real_smul]
  push_cast
  ring

theorem complexCentralCompanion_gramCorrection_posSemidef
    (m : ℕ) {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) :
    ((1 - a ^ 2 : ℝ) • centralLastProjector m).PosSemidef := by
  exact (centralLastProjector_posSemidef m).smul (by nlinarith)

/-- Shifted Gram form of the rank-one comparison. -/
private theorem gramShift_complexCentralCompanion
    (m : ℕ) (a t : ℝ) :
    gramShift (complexCentralCompanion m a) t =
      (complexReversal m)ᴴ *
          gramShift (complexCentralBidiagonal m a) t *
            complexReversal m +
        (1 - a ^ 2 : ℝ) • centralLastProjector m := by
  have hgram :=
    complexCentralCompanion_gram_sub_reversed_central_gram m a
  have hgram' := sub_eq_iff_eq_add.mp hgram
  have hJstar := complexReversal_star m
  have hJconj : (complexReversal m)ᴴ = complexReversal m := by
    rw [← Matrix.star_eq_conjTranspose, hJstar]
  have hJtwo := complexReversal_mul_self m
  rw [hJconj]
  unfold gramShift
  rw [hgram']
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hJtwo]
  abel

/-- The companion block has no smaller least singular value than
`aI+V`. -/
theorem centralBidiagonalHeight_le_companion
    (m : ℕ) (hm : 0 < m) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    centralBidiagonalHeight m a ≤
      leastSingularValue (complexCentralCompanion m a) := by
  let C := complexCentralBidiagonal m a
  let D := complexCentralCompanion m a
  let c := leastSingularValue C
  let d := leastSingularValue D
  by_contra hcd
  have hdc : d < c := lt_of_not_ge hcd
  have hd0 : 0 ≤ d := leastSingularValue_nonneg D
  have hCpos : (gramShift C d).PosDef :=
    (gramShift_posDef_iff_lt_leastSingularValue C hm d hd0).2 hdc
  have hJinj : Function.Injective (complexReversal m).mulVec := by
    intro x y hxy
    have h := congrArg (fun v ↦ complexReversal m *ᵥ v) hxy
    simpa only [Matrix.mulVec_mulVec, complexReversal_mul_self,
      Matrix.one_mulVec] using h
  have hconj :
      ((complexReversal m)ᴴ * gramShift C d *
        complexReversal m).PosDef :=
    hCpos.conjTranspose_mul_mul_same hJinj
  have hDpos : (gramShift D d).PosDef := by
    rw [gramShift_complexCentralCompanion]
    exact hconj.add_posSemidef
      (complexCentralCompanion_gramCorrection_posSemidef m ha₀ ha₁)
  have hdd : d < d :=
    (gramShift_posDef_iff_lt_leastSingularValue D hm d hd0).1 hDpos
  exact (lt_irrefl d) hdd

/-! ## Singular values of the off-diagonal block matrix -/

private theorem blockDiagonal_quadratic
    {p q : Type*} [Fintype p] [Fintype q]
    (A : Matrix p p ℂ) (D : Matrix q q ℂ) (x : p ⊕ q → ℂ) :
    star x ⬝ᵥ
        (Matrix.fromBlocks A 0 0 D *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
      star (x ∘ Sum.inr) ⬝ᵥ (D *ᵥ (x ∘ Sum.inr)) := by
  rw [Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add]
  have hxstar :
      star x = Sum.elim (star (x ∘ Sum.inl)) (star (x ∘ Sum.inr)) := by
    calc
      star x = star (Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr)) :=
        congrArg (fun v ↦ star v) (Sum.elim_comp_inl_inr x).symm
      _ = Sum.elim (star (x ∘ Sum.inl)) (star (x ∘ Sum.inr)) :=
        Function.star_sumElim _ _
  rw [hxstar, sumElim_dotProduct_sumElim]

private theorem blockDiagonal_posDef_iff
    {p q : Type*} [Finite p] [Finite q]
    (A : Matrix p p ℂ) (D : Matrix q q ℂ) :
    (Matrix.fromBlocks A 0 0 D).PosDef ↔ A.PosDef ∧ D.PosDef := by
  classical
  letI : Fintype p := Fintype.ofFinite p
  letI : Fintype q := Fintype.ofFinite q
  constructor
  · intro h
    have hparts := Matrix.isHermitian_fromBlocks_iff.mp h.isHermitian
    constructor
    · apply Matrix.PosDef.of_dotProduct_mulVec_pos hparts.1
      intro u hu
      let x : p ⊕ q → ℂ := Sum.elim u 0
      have hx : x ≠ 0 := by
        intro hx0
        apply hu
        funext i
        have := congrFun hx0 (Sum.inl i)
        simpa only [x, Sum.elim_inl, Pi.zero_apply] using this
      have hquad := h.dotProduct_mulVec_pos hx
      rw [blockDiagonal_quadratic] at hquad
      have hxinl : x ∘ Sum.inl = u := by
        funext i
        rfl
      have hxinr : x ∘ Sum.inr = 0 := by
        funext i
        rfl
      rw [hxinl, hxinr] at hquad
      simpa only [Matrix.mulVec_zero, star_zero, dotProduct_zero,
        add_zero] using hquad
    · apply Matrix.PosDef.of_dotProduct_mulVec_pos hparts.2.2.2
      intro v hv
      let x : p ⊕ q → ℂ := Sum.elim 0 v
      have hx : x ≠ 0 := by
        intro hx0
        apply hv
        funext i
        have := congrFun hx0 (Sum.inr i)
        simpa only [x, Sum.elim_inr, Pi.zero_apply] using this
      have hquad := h.dotProduct_mulVec_pos hx
      rw [blockDiagonal_quadratic] at hquad
      have hxinl : x ∘ Sum.inl = 0 := by
        funext i
        rfl
      have hxinr : x ∘ Sum.inr = v := by
        funext i
        rfl
      rw [hxinl, hxinr] at hquad
      simpa only [Matrix.mulVec_zero, star_zero, dotProduct_zero,
        zero_add] using hquad
  · rintro ⟨hA, hD⟩
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
      (hA.isHermitian.fromBlocks (by simp) hD.isHermitian)
    intro x hx
    have hparts : x ∘ Sum.inl ≠ 0 ∨ x ∘ Sum.inr ≠ 0 := by
      by_contra h
      push_neg at h
      apply hx
      funext i
      rcases i with i | i
      · exact congrFun h.1 i
      · exact congrFun h.2 i
    rw [blockDiagonal_quadratic]
    rcases hparts with hleft | hright
    · exact add_pos_of_pos_of_nonneg
        (hA.dotProduct_mulVec_pos hleft)
        (hD.posSemidef.dotProduct_mulVec_nonneg _)
    · exact add_pos_of_nonneg_of_pos
        (hA.posSemidef.dotProduct_mulVec_nonneg _)
        (hD.dotProduct_mulVec_pos hright)

private theorem posDef_submatrix_equiv_iff
    {p q : Type*} [Finite p] [Finite q]
    (M : Matrix q q ℂ) (e : p ≃ q) :
    (M.submatrix e e).PosDef ↔ M.PosDef := by
  classical
  letI : Fintype p := Fintype.ofFinite p
  letI : Fintype q := Fintype.ofFinite q
  let E : Matrix p q ℂ := e.toPEquiv.toMatrix
  let F : Matrix q p ℂ := e.symm.toPEquiv.toMatrix
  have hEF : E * F = (1 : Matrix p p ℂ) := by
    dsimp only [E, F]
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans,
      Equiv.self_trans_symm, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  have hFE : F * E = (1 : Matrix q q ℂ) := by
    dsimp only [E, F]
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans,
      Equiv.symm_trans_self, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
  have hEstar : Eᴴ = F := by
    ext i j
    by_cases h : e j = i
    · have h' : e.symm i = j := by
        exact e.symm_apply_eq.mpr h.symm
      simp [E, F, Matrix.conjTranspose_apply, PEquiv.toMatrix_apply,
        h, h']
    · have h' : e.symm i ≠ j := by
        intro h'
        exact h (e.symm_apply_eq.mp h').symm
      simp [E, F, Matrix.conjTranspose_apply, PEquiv.toMatrix_apply,
        h, h']
  have hFstar : Fᴴ = E := by
    rw [← hEstar, Matrix.conjTranspose_conjTranspose]
  have hE_inj : Function.Injective E.mulVec := by
    intro x y hxy
    have h := congrArg (fun v ↦ F *ᵥ v) hxy
    simpa only [Matrix.mulVec_mulVec, hFE, Matrix.one_mulVec] using h
  have hF_inj : Function.Injective F.mulVec := by
    intro x y hxy
    have h := congrArg (fun v ↦ E *ᵥ v) hxy
    simpa only [Matrix.mulVec_mulVec, hEF, Matrix.one_mulVec] using h
  have hreindex : M.submatrix e e = E * M * F := by
    dsimp only [E, F]
    rw [PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    ext i j
    rfl
  constructor
  · intro h
    have hconj := h.conjTranspose_mul_mul_same hE_inj
    rw [hreindex, hEstar] at hconj
    have hcollapse : F * (E * M * F) * E = M := by
      calc
        F * (E * M * F) * E = (F * E) * M * (F * E) := by
          simp only [Matrix.mul_assoc]
        _ = M := by rw [hFE, Matrix.one_mul, Matrix.mul_one]
    rwa [hcollapse] at hconj
  · intro h
    have hconj := h.conjTranspose_mul_mul_same hF_inj
    rw [hFstar, ← hreindex] at hconj
    exact hconj

private theorem gramShift_evenCentralOffDiagonalFin
    (m : ℕ) (a t : ℝ) :
    gramShift (evenCentralOffDiagonalFin m a) t =
      (Matrix.fromBlocks
        (gramShift (complexCentralBidiagonal m a) t) 0 0
        (gramShift (complexCentralCompanion m a) t)).submatrix
          (centralTwoBlockEquiv m).symm
          (centralTwoBlockEquiv m).symm := by
  let B := evenCentralOffDiagonal m a
  have hBgram :
      Bᴴ * B - ((t : ℂ) ^ 2) • 1 =
        Matrix.fromBlocks
          (gramShift (complexCentralBidiagonal m a) t) 0 0
          (gramShift (complexCentralCompanion m a) t) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [B, evenCentralOffDiagonal, gramShift,
        Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
        Matrix.one_apply]
  have hReindexed :
      (Bᴴ * B).submatrix
          (centralTwoBlockEquiv m).symm (centralTwoBlockEquiv m).symm -
          ((t : ℂ) ^ 2) • 1 =
        (Matrix.fromBlocks
          (gramShift (complexCentralBidiagonal m a) t) 0 0
          (gramShift (complexCentralCompanion m a) t)).submatrix
            (centralTwoBlockEquiv m).symm
            (centralTwoBlockEquiv m).symm := by
    calc
      (Bᴴ * B).submatrix
            (centralTwoBlockEquiv m).symm (centralTwoBlockEquiv m).symm -
          ((t : ℂ) ^ 2) • 1 =
        (Bᴴ * B - ((t : ℂ) ^ 2) • 1).submatrix
          (centralTwoBlockEquiv m).symm
          (centralTwoBlockEquiv m).symm := by
            ext i j
            simp [Matrix.one_apply]
      _ = (Matrix.fromBlocks
          (gramShift (complexCentralBidiagonal m a) t) 0 0
          (gramShift (complexCentralCompanion m a) t)).submatrix
            (centralTwoBlockEquiv m).symm
            (centralTwoBlockEquiv m).symm :=
        congrArg (fun M ↦ M.submatrix (centralTwoBlockEquiv m).symm
          (centralTwoBlockEquiv m).symm) hBgram
  change
    ((evenCentralOffDiagonal m a).submatrix
          (centralTwoBlockEquiv m).symm
          (centralTwoBlockEquiv m).symm)ᴴ *
        (evenCentralOffDiagonal m a).submatrix
          (centralTwoBlockEquiv m).symm
          (centralTwoBlockEquiv m).symm -
      (((t ^ 2 : ℝ) : ℂ)) • 1 =
        (Matrix.fromBlocks
          (gramShift (complexCentralBidiagonal m a) t) 0 0
          (gramShift (complexCentralCompanion m a) t)).submatrix
            (centralTwoBlockEquiv m).symm
            (centralTwoBlockEquiv m).symm
  have htSq : ((t ^ 2 : ℝ) : ℂ) = (t : ℂ) ^ 2 := by
    norm_cast
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, htSq]
  exact hReindexed

private theorem gramShift_evenCentralOffDiagonalFin_posDef_iff
    (m : ℕ) (a t : ℝ) :
    (gramShift (evenCentralOffDiagonalFin m a) t).PosDef ↔
      (gramShift (complexCentralBidiagonal m a) t).PosDef ∧
        (gramShift (complexCentralCompanion m a) t).PosDef := by
  rw [gramShift_evenCentralOffDiagonalFin,
    posDef_submatrix_equiv_iff]
  exact blockDiagonal_posDef_iff _ _

/-- The singular values of the block off-diagonal matrix are the union of
those of its two blocks; this is the least-value consequence used here. -/
theorem leastSingularValue_evenCentralOffDiagonalFin
    (m : ℕ) (hm : 0 < m) (a : ℝ) :
    leastSingularValue (evenCentralOffDiagonalFin m a) =
      min (centralBidiagonalHeight m a)
        (leastSingularValue (complexCentralCompanion m a)) := by
  let B := evenCentralOffDiagonalFin m a
  let C := complexCentralBidiagonal m a
  let D := complexCentralCompanion m a
  let b := leastSingularValue B
  let c := leastSingularValue C
  let d := leastSingularValue D
  have hm2 : 0 < 2 * m := by omega
  have hb0 : 0 ≤ b := leastSingularValue_nonneg B
  have hc0 : 0 ≤ c := leastSingularValue_nonneg C
  have hd0 : 0 ≤ d := leastSingularValue_nonneg D
  have hcharacterize (t : ℝ) (ht : 0 ≤ t) :
      t < b ↔ t < c ∧ t < d := by
    rw [← gramShift_posDef_iff_lt_leastSingularValue B hm2 t ht,
      gramShift_evenCentralOffDiagonalFin_posDef_iff,
      gramShift_posDef_iff_lt_leastSingularValue C hm t ht,
      gramShift_posDef_iff_lt_leastSingularValue D hm t ht]
  change b = min c d
  apply le_antisymm
  · by_contra h
    have hminb : min c d < b := lt_of_not_ge h
    have hmin0 : 0 ≤ min c d := le_min hc0 hd0
    have hboth := (hcharacterize (min c d) hmin0).1 hminb
    by_cases hcd : c ≤ d
    · rw [min_eq_left hcd] at hboth
      exact (lt_irrefl c) hboth.1
    · have hdc : d ≤ c := le_of_not_ge hcd
      rw [min_eq_right hdc] at hboth
      exact (lt_irrefl d) hboth.2
  · by_contra h
    have hbmin : b < min c d := lt_of_not_ge h
    have hboth : b < c ∧ b < d :=
      ⟨hbmin.trans_le (min_le_left c d),
        hbmin.trans_le (min_le_right c d)⟩
    have hbb := (hcharacterize b hb0).2 hboth
    exact (lt_irrefl b) hbb

/-! ## The centre value -/

private theorem shiftedPathMatrix_zero (n : ℕ) (a : ℝ) :
    shiftedPathMatrix n a 0 = -complexPathMatrix n a := by
  ext i j
  simp [shiftedPathMatrix]

/-- The actual least singular value at the centre of the even central gap is
the paper's `c_m`. -/
theorem realGapValue_even_zero_eq_centralBidiagonalHeight
    (m : ℕ) (hm : 0 < m) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    realGapValue (2 * m) a 0 = centralBidiagonalHeight m a := by
  have hcomp := centralBidiagonalHeight_le_companion m hm a ha₀ ha₁
  unfold realGapValue pseudospectralHeight
  change leastSingularValue
      (shiftedPathMatrix (2 * m) a (0 : ℂ)) =
    centralBidiagonalHeight m a
  rw [shiftedPathMatrix_zero]
  have hneg :
      -(complexPathMatrix (2 * m) a) =
        (-1 : ℂ) • complexPathMatrix (2 * m) a := by
    ext i j
    simp
  rw [hneg, leastSingularValue_smul]
  norm_num
  rw [leastSingularValue_complexPathMatrix_eq_evenCentralOffDiagonal,
    leastSingularValue_evenCentralOffDiagonalFin m hm a,
    min_eq_left hcomp]

end

end ConnectedPseudospectrum
