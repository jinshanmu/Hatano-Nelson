import ConnectedPseudospectrum.ChordLobes
import ConnectedPseudospectrum.HermitianLeastSingular
import ConnectedPseudospectrum.VerticalToeplitz
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Order.IntermediateValue

/-!
# The central bidiagonal singular value

This module formalizes the bidiagonal calculation at the start of the
central-gap argument in `lem:mesh`.  The matrix is the literal finite path
bidiagonal `a I + V`; its height uses the project's attained complex
Euclidean least singular value.
-/

namespace ConnectedPseudospectrum

open Matrix Set
open scoped ComplexOrder

noncomputable section

/-- The real upper bidiagonal matrix `a I_j + V_j`. -/
def realCentralBidiagonal (j : ℕ) (a : ℝ) :
    Matrix (Fin j) (Fin j) ℝ :=
  a • 1 + upperShift j

/-- The same bidiagonal matrix on the complex Euclidean coordinate space. -/
def complexCentralBidiagonal (j : ℕ) (a : ℝ) :
    Matrix (Fin j) (Fin j) ℂ :=
  (realCentralBidiagonal j a).map Complex.ofRealHom

/-- The paper's central even-gap height `c_j`, defined using the actual
attained Euclidean least singular value. -/
def centralBidiagonalHeight (j : ℕ) (a : ℝ) : ℝ :=
  leastSingularValue (complexCentralBidiagonal j a)

@[simp] theorem realCentralBidiagonal_apply (j : ℕ) (a : ℝ)
    (p q : Fin j) :
    realCentralBidiagonal j a p q =
      (if p = q then a else 0) +
        (if q.1 = p.1 + 1 then 1 else 0) := by
  by_cases hpq : p = q
  · subst q
    simp [realCentralBidiagonal, upperShift_apply, smul_eq_mul]
  · simp [realCentralBidiagonal, upperShift_apply,
      smul_eq_mul, hpq]

@[simp] theorem complexCentralBidiagonal_apply (j : ℕ) (a : ℝ)
    (p q : Fin j) :
    complexCentralBidiagonal j a p q =
      (if p = q then (a : ℂ) else 0) +
        (if q.1 = p.1 + 1 then 1 else 0) := by
  simp only [complexCentralBidiagonal, Matrix.map_apply,
    realCentralBidiagonal_apply]
  rw [map_add]
  refine congrArg₂ (fun x y : ℂ ↦ x + y) ?_ ?_
  · by_cases hpq : p = q
    · simp only [hpq, if_true]
      exact Complex.ofRealHom_eq_coe a
    · simp only [hpq, if_false]
      exact (Complex.ofRealHom_eq_coe 0).trans Complex.ofReal_zero
  · by_cases hadj : q.1 = p.1 + 1
    · simp only [hadj, if_true]
      exact (Complex.ofRealHom_eq_coe 1).trans Complex.ofReal_one
    · simp only [hadj, if_false]
      exact (Complex.ofRealHom_eq_coe 0).trans Complex.ofReal_zero

@[simp] theorem centralBidiagonalHeight_zero (a : ℝ) :
    centralBidiagonalHeight 0 a = 0 := by
  simp [centralBidiagonalHeight]

/-! ## The tridiagonal determinant -/

/-- The pure symmetric tridiagonal continuant with diagonal `2at` and
off-diagonal `a`. -/
def centralToeplitz (j : ℕ) (a t : ℝ) :
    Matrix (Fin j) (Fin j) ℝ :=
  fun p q ↦
    if p = q then 2 * a * t
    else if q.1 = p.1 + 1 ∨ p.1 = q.1 + 1 then a
    else 0

/-- The missing first-column norm in `(aI+V)ᵀ(aI+V)`. -/
def centralFirstCorrection (j : ℕ) : Matrix (Fin j) (Fin j) ℝ :=
  fun p q ↦ if p = q ∧ p.1 = 0 then 1 else 0

@[simp] theorem centralToeplitz_apply (j : ℕ) (a t : ℝ)
    (p q : Fin j) :
    centralToeplitz j a t p q =
      if p = q then 2 * a * t
      else if q.1 = p.1 + 1 ∨ p.1 = q.1 + 1 then a
      else 0 :=
  rfl

@[simp] theorem centralFirstCorrection_apply (j : ℕ) (p q : Fin j) :
    centralFirstCorrection j p q =
      if p = q ∧ p.1 = 0 then 1 else 0 :=
  rfl

/-- A one-coordinate symmetric border, used only to prove the continuant
recurrence without an invertibility assumption. -/
private def centralPrepend (n : ℕ) (d b : ℝ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
  fun i j ↦ Fin.cases
    (Fin.cases d (fun q ↦ if q = 0 then b else 0) j)
    (fun p ↦ Fin.cases (if p = 0 then b else 0) (fun q ↦ K p q) j) i

@[simp] private theorem centralPrepend_zero_zero (n : ℕ) (d b : ℝ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    centralPrepend n d b K 0 0 = d := rfl

@[simp] private theorem centralPrepend_zero_succ (n : ℕ) (d b : ℝ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (q : Fin (n + 1)) :
    centralPrepend n d b K 0 q.succ = if q = 0 then b else 0 := rfl

@[simp] private theorem centralPrepend_succ_zero (n : ℕ) (d b : ℝ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p : Fin (n + 1)) :
    centralPrepend n d b K p.succ 0 = if p = 0 then b else 0 := rfl

@[simp] private theorem centralPrepend_succ_succ (n : ℕ) (d b : ℝ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (p q : Fin (n + 1)) :
    centralPrepend n d b K p.succ q.succ = K p q := rfl

private theorem det_centralPrepend (n : ℕ) (d b : ℝ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (centralPrepend n d b K).det =
      d * K.det - b ^ 2 * (K.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simp only [centralPrepend_zero_zero, centralPrepend_zero_succ,
    Fin.val_zero, Fin.val_succ, pow_zero, one_mul, zero_add]
  simp only [Fin.succ_ne_zero, if_false, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  have htailMatrix :
      ((centralPrepend n d b K).submatrix Fin.succ
          (0 : Fin (n + 2)).succAbove) = K := by
    ext i j
    simp [centralPrepend]
  rw [htailMatrix]
  let M := (centralPrepend n d b K).submatrix Fin.succ
    (1 : Fin (n + 2)).succAbove
  have hMdet : M.det = b * (K.submatrix Fin.succ Fin.succ).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have htail' :
        (∑ i : Fin n,
          (-1 : ℝ) ^ (i.succ : ℕ) * M i.succ 0 *
            (M.submatrix i.succ.succAbove Fin.succ).det) = 0 := by
      apply Fintype.sum_eq_zero
      intro i
      simp [M, centralPrepend]
    rw [htail', add_zero]
    have hminor :
        M.submatrix (0 : Fin (n + 1)).succAbove Fin.succ =
          K.submatrix Fin.succ Fin.succ := by
      ext i j
      simp [M, centralPrepend]
    rw [hminor]
    have hM00 : M 0 0 = b := rfl
    rw [hM00]
    norm_num
  change d * K.det + (-1 : ℝ) ^ 1 * b * M.det = _
  rw [hMdet]
  ring

private theorem centralToeplitz_succ_succ (n : ℕ) (a t : ℝ) :
    centralToeplitz (n + 2) a t =
      centralPrepend n (2 * a * t) a (centralToeplitz (n + 1) a t) := by
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · rw [centralToeplitz_apply, centralPrepend_zero_zero]
      rfl
    · rw [centralToeplitz_apply, centralPrepend_zero_succ]
      rw [if_neg (Ne.symm j.succ_ne_zero)]
      simp only [Fin.val_zero, Fin.val_succ, zero_add]
      by_cases hj : j = 0
      · subst j
        norm_num
      · have hjval : j.1 ≠ 0 := fun h ↦ hj (Fin.ext h)
        rw [if_neg hj]
        rw [if_neg]
        omega
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · rw [centralToeplitz_apply, centralPrepend_succ_zero]
      rw [if_neg i.succ_ne_zero]
      simp only [Fin.val_zero, Fin.val_succ, zero_add]
      by_cases hi : i = 0
      · subst i
        norm_num
      · have hival : i.1 ≠ 0 := fun h ↦ hi (Fin.ext h)
        rw [if_neg hi]
        rw [if_neg]
        omega
    · rw [centralToeplitz_apply, centralPrepend_succ_succ,
        centralToeplitz_apply]
      by_cases hij : i = j
      · subst j
        rw [if_pos rfl, if_pos rfl]
      · have hsucc : i.succ ≠ j.succ := by
          intro h
          apply hij
          have hval := congrArg Fin.val h
          change i.1 + 1 = j.1 + 1 at hval
          exact Fin.ext (Nat.add_right_cancel hval)
        rw [if_neg hsucc, if_neg hij]
        have hup :
            j.succ.1 = i.succ.1 + 1 ↔ j.1 = i.1 + 1 := by
          simp only [Fin.val_succ]
          omega
        have hlow :
            i.succ.1 = j.succ.1 + 1 ↔ i.1 = j.1 + 1 := by
          simp only [Fin.val_succ]
          omega
        simp only [hup, hlow]

private theorem centralToeplitz_submatrix_succ (n : ℕ) (a t : ℝ) :
    (centralToeplitz (n + 1) a t).submatrix Fin.succ Fin.succ =
      centralToeplitz n a t := by
  ext i j
  simp [Matrix.submatrix_apply, Fin.ext_iff]

/-- The pure continuant is exactly the scaled second-kind Chebyshev
polynomial, including dimensions zero and one. -/
theorem det_centralToeplitz (j : ℕ) (a t : ℝ) :
    (centralToeplitz j a t).det = a ^ j * chebyshevU j t := by
  induction j using Nat.twoStepInduction with
  | zero => simp
  | one =>
      rw [Matrix.det_fin_one]
      norm_num
      ring
  | more n ih₀ ih₁ =>
      rw [centralToeplitz_succ_succ, det_centralPrepend,
        centralToeplitz_submatrix_succ, ih₁, ih₀]
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega,
        show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega,
        chebyshevU_add_two]
      ring

private theorem centralFirstCorrection_succ (n : ℕ) :
    centralFirstCorrection (n + 1) =
      Matrix.single (0 : Fin (n + 1)) 0 1 := by
  ext i j
  rw [centralFirstCorrection_apply, Matrix.single_apply]
  by_cases hleft : i = j ∧ i.1 = 0
  · rw [if_pos hleft]
    have hi : i = 0 := Fin.ext hleft.2
    have hj : j = 0 := hleft.1 ▸ hi
    rw [if_pos ⟨hi.symm, hj.symm⟩]
  · rw [if_neg hleft]
    have hright : ¬((0 : Fin (n + 1)) = i ∧ (0 : Fin (n + 1)) = j) := by
      intro h
      rcases h with ⟨hi, hj⟩
      apply hleft
      refine ⟨hi.symm.trans hj, ?_⟩
      simpa only [Fin.val_zero] using (congrArg Fin.val hi).symm
    rw [if_neg hright]

private theorem det_sub_first_single {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (c : ℝ) :
    (M - Matrix.single (0 : Fin (n + 1)) 0 c).det =
      M.det - c * (M.submatrix Fin.succ Fin.succ).det := by
  classical
  have hmatrix :
      M - Matrix.single (0 : Fin (n + 1)) 0 c =
        M.updateRow 0
          (M 0 + (-c) •
            (Pi.single (0 : Fin (n + 1)) (1 : ℝ) : Fin (n + 1) → ℝ)) := by
    ext r s
    by_cases hr : r = 0
    · subst r
      rw [Matrix.updateRow_apply, if_pos rfl]
      by_cases hs : (0 : Fin (n + 1)) = s
      · simp [hs]
        ring
      · simp [hs]
    · rw [Matrix.updateRow_apply, if_neg hr]
      have hzero : (0 : Fin (n + 1)) ≠ r := Ne.symm hr
      simp [hzero]
  rw [hmatrix, Matrix.det_updateRow_add, Matrix.updateRow_eq_self,
    Matrix.det_updateRow_smul, ← Matrix.adjugate_apply,
    Matrix.adjugate_fin_succ_eq_det_submatrix]
  norm_num
  ring

/-- Entrywise Gram identity.  It includes the coincident one-dimensional
boundary correctly: only the first correction is present. -/
theorem realCentralBidiagonal_gram_shift (j : ℕ) (a t : ℝ) :
    (realCentralBidiagonal j a)ᵀ * realCentralBidiagonal j a -
        (1 + a ^ 2 - 2 * a * t) •
          (1 : Matrix (Fin j) (Fin j) ℝ) =
      centralToeplitz j a t - centralFirstCorrection j := by
  have htranspose :
      (realCentralBidiagonal j a)ᵀ = a • 1 + lowerShift j := by
    ext p q
    by_cases hpq : p = q
    · subst q
      simp [realCentralBidiagonal, lowerShift, Matrix.transpose_apply,
        smul_eq_mul]
    · have hqp : q ≠ p := Ne.symm hpq
      simp [realCentralBidiagonal, lowerShift, Matrix.transpose_apply,
        smul_eq_mul, hpq, hqp]
  rw [htranspose]
  ext p q
  simp only [realCentralBidiagonal, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    centralToeplitz_apply, centralFirstCorrection_apply]
  rw [lowerShift_mul_upperShift_apply]
  by_cases hpq : p = q
  · subst q
    by_cases hp0 : p.1 = 0
    · simp [hp0, smul_eq_mul]
      ring
    · have hpPos : 0 < p.1 := by omega
      simp [hp0, hpPos, smul_eq_mul]
      ring
  · by_cases hup : q.1 = p.1 + 1
    · have hfar : ¬p.1 = p.1 + 1 + 1 := by omega
      simp [hpq, hup, hfar, smul_eq_mul]
    · by_cases hlow : p.1 = q.1 + 1
      · have hfar : ¬q.1 = q.1 + 1 + 1 := by omega
        simp [hpq, hlow, hfar, smul_eq_mul]
      · simp [hpq, hup, hlow, smul_eq_mul]

/-- Division-free form of `eq:c-determinant`.  This statement is valid for
every real `a`, including `a=0`, and for `j=0,1`. -/
theorem centralBidiagonal_gram_det_divisionFree (j : ℕ) (a t : ℝ) :
    ((realCentralBidiagonal j a)ᵀ * realCentralBidiagonal j a -
        (1 + a ^ 2 - 2 * a * t) •
          (1 : Matrix (Fin j) (Fin j) ℝ)).det =
      a ^ j * chebyshevU j t -
        a ^ (j - 1) * chebyshevU ((j : ℤ) - 1) t := by
  cases j with
  | zero => simp [realCentralBidiagonal]
  | succ n =>
      rw [realCentralBidiagonal_gram_shift,
        centralFirstCorrection_succ, det_sub_first_single,
        centralToeplitz_submatrix_succ, det_centralToeplitz,
        det_centralToeplitz]
      simp only [Nat.succ_sub_one, one_mul, Nat.cast_succ]
      rw [show ((n : ℤ) + 1 - 1) = (n : ℤ) by omega]

/-- The determinant identity exactly as printed in `eq:c-determinant`. -/
theorem centralBidiagonal_gram_det (j : ℕ) {a t : ℝ} (ha : a ≠ 0) :
    ((realCentralBidiagonal j a)ᵀ * realCentralBidiagonal j a -
        (1 + a ^ 2 - 2 * a * t) •
          (1 : Matrix (Fin j) (Fin j) ℝ)).det =
      a ^ j *
        (chebyshevU j t - a⁻¹ * chebyshevU ((j : ℤ) - 1) t) := by
  rw [centralBidiagonal_gram_det_divisionFree]
  cases j with
  | zero => simp
  | succ n =>
      simp only [Nat.succ_sub_one, pow_succ]
      field_simp

/-- Complex-cast version of `eq:c-determinant`, matching the matrix used by
`centralBidiagonalHeight`. -/
theorem complexCentralBidiagonal_gram_det (j : ℕ) {a t : ℝ} (ha : a ≠ 0) :
    ((complexCentralBidiagonal j a)ᴴ * complexCentralBidiagonal j a -
        ((1 + a ^ 2 - 2 * a * t : ℝ) : ℂ) •
          (1 : Matrix (Fin j) (Fin j) ℂ)).det =
      ((a ^ j *
        (chebyshevU j t - a⁻¹ * chebyshevU ((j : ℤ) - 1) t) : ℝ) : ℂ) := by
  let R : Matrix (Fin j) (Fin j) ℝ :=
    (realCentralBidiagonal j a)ᵀ * realCentralBidiagonal j a -
      (1 + a ^ 2 - 2 * a * t) • 1
  have hstar :
      (complexCentralBidiagonal j a)ᴴ =
        ((realCentralBidiagonal j a)ᵀ).map Complex.ofRealHom := by
    ext p q
    simp [complexCentralBidiagonal, Matrix.conjTranspose_apply,
      Matrix.transpose_apply]
  have hmap : R.map Complex.ofRealHom =
      (complexCentralBidiagonal j a)ᴴ * complexCentralBidiagonal j a -
        ((1 + a ^ 2 - 2 * a * t : ℝ) : ℂ) •
          (1 : Matrix (Fin j) (Fin j) ℂ) := by
    calc
      R.map Complex.ofRealHom =
          (((realCentralBidiagonal j a)ᵀ * realCentralBidiagonal j a).map
            Complex.ofRealHom) -
            (((1 + a ^ 2 - 2 * a * t) •
              (1 : Matrix (Fin j) (Fin j) ℝ)).map Complex.ofRealHom) := by
        ext p q
        change Complex.ofRealHom
            (((realCentralBidiagonal j a)ᵀ * realCentralBidiagonal j a) p q -
              ((1 + a ^ 2 - 2 * a * t) •
                (1 : Matrix (Fin j) (Fin j) ℝ)) p q) =
          Complex.ofRealHom
              (((realCentralBidiagonal j a)ᵀ *
                realCentralBidiagonal j a) p q) -
            Complex.ofRealHom
              (((1 + a ^ 2 - 2 * a * t) •
                (1 : Matrix (Fin j) (Fin j) ℝ)) p q)
        exact Complex.ofRealHom.map_sub _ _
      _ = ((realCentralBidiagonal j a)ᵀ).map Complex.ofRealHom *
            (realCentralBidiagonal j a).map Complex.ofRealHom -
            (((1 + a ^ 2 - 2 * a * t) •
              (1 : Matrix (Fin j) (Fin j) ℝ)).map Complex.ofRealHom) := by
        rw [Matrix.map_mul]
      _ = (complexCentralBidiagonal j a)ᴴ * complexCentralBidiagonal j a -
            ((1 + a ^ 2 - 2 * a * t : ℝ) : ℂ) •
              (1 : Matrix (Fin j) (Fin j) ℂ) := by
        rw [← hstar]
        ext p q
        by_cases hpq : p = q
        · subst q
          simp [complexCentralBidiagonal, Matrix.map_apply]
        · simp [complexCentralBidiagonal, Matrix.map_apply, hpq]
  rw [← hmap]
  change (Complex.ofRealHom.mapMatrix R).det = _
  rw [← Complex.ofRealHom.map_det]
  change Complex.ofRealHom
    (((realCentralBidiagonal j a)ᵀ * realCentralBidiagonal j a -
      (1 + a ^ 2 - 2 * a * t) •
        (1 : Matrix (Fin j) (Fin j) ℝ)).det) = _
  rw [centralBidiagonal_gram_det j ha]
  rfl

/-! ## The elementary Chebyshev invariant -/

/-- The exact quadratic Chebyshev identity used in
`eq:c-rho-identities`, with `U_{-1}=0` supplying the `j=0` boundary. -/
theorem chebyshevU_sq_add_sq_sub (j : ℕ) (t : ℝ) :
    chebyshevU j t ^ 2 + chebyshevU ((j : ℤ) - 1) t ^ 2 -
        2 * t * chebyshevU j t * chebyshevU ((j : ℤ) - 1) t = 1 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      have hrec := chebyshevU_add_one (j : ℤ) t
      push_cast at hrec
      push_cast
      rw [show ((j : ℤ) + 1 - 1) = (j : ℤ) by omega]
      rw [hrec]
      nlinarith [ih]

/-! ## The unique outer root of the central continuant -/

/-- The largest zero of `U_j`. -/
def centralChebyshevFirstNode (j : ℕ) : ℝ :=
  Real.cos (Real.pi / ((j + 1 : ℕ) : ℝ))

/-- The quotient used in the source's Christoffel--Darboux argument. -/
def centralChebyshevRatio (j : ℕ) (t : ℝ) : ℝ :=
  chebyshevU ((j : ℤ) - 1) t / chebyshevU j t

/-- The first Chebyshev zero moves strictly to the right with the degree. -/
theorem centralChebyshevFirstNode_lt_succ (j : ℕ) :
    centralChebyshevFirstNode j < centralChebyshevFirstNode (j + 1) := by
  have hsmallPos :
      0 ≤ Real.pi / (((j + 1) + 1 : ℕ) : ℝ) := by positivity
  have hlargePi :
      Real.pi / ((j + 1 : ℕ) : ℝ) ≤ Real.pi := by
    have hden : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 j
    have hpi := mul_le_mul_of_nonneg_left hden Real.pi_pos.le
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (j + 1 : ℕ))]
    simpa only [mul_one] using hpi
  have hangles :
      Real.pi / (((j + 1) + 1 : ℕ) : ℝ) <
        Real.pi / ((j + 1 : ℕ) : ℝ) := by
    apply (div_lt_div_iff_of_pos_left Real.pi_pos (by positivity) (by positivity)).2
    norm_num
  unfold centralChebyshevFirstNode
  exact Real.cos_lt_cos_of_nonneg_of_le_pi hsmallPos hlargePi hangles

/-- Every positive-degree `U_j` is positive strictly above its largest
zero.  This is read directly from the already proved exact root product. -/
theorem chebyshevU_pos_above_centralFirstNode
    (j : ℕ) (hj : 1 ≤ j) {t : ℝ}
    (ht : centralChebyshevFirstNode j < t) :
    0 < chebyshevU j t := by
  have hK : 2 ≤ j + 1 := by omega
  rw [show (j : ℤ) = ((j + 1 - 1 : ℕ) : ℤ) by omega,
    chebyshevU_eq_chordNodeProduct (j + 1) hK]
  have hprod : 0 < chordNodeProduct (j + 1) t := by
    rw [chordNodeProduct]
    apply Finset.prod_pos
    intro q hq
    apply sub_pos.mpr
    exact (chordNode_le_first (j + 1) hK hq).trans_lt ht
  exact mul_pos (by positivity) hprod

/-- The quotient `U_{j-1}/U_j` is positive above the largest zero of
`U_j`. -/
theorem centralChebyshevRatio_pos (j : ℕ) (hj : 1 ≤ j) {t : ℝ}
    (ht : centralChebyshevFirstNode j < t) :
    0 < centralChebyshevRatio j t := by
  have hden := chebyshevU_pos_above_centralFirstNode j hj ht
  cases j with
  | zero => omega
  | succ k =>
      cases k with
      | zero =>
          simpa [centralChebyshevRatio] using
            (div_pos (by norm_num : (0 : ℝ) < 1) hden)
      | succ k =>
          have hnodes := centralChebyshevFirstNode_lt_succ (k + 1)
          have htPrev : centralChebyshevFirstNode (k + 1) < t :=
            hnodes.trans ht
          have hnum := chebyshevU_pos_above_centralFirstNode
            (k + 1) (by omega) htPrev
          rw [centralChebyshevRatio]
          rw [show (((k + 2 : ℕ) : ℤ) - 1) =
            ((k + 1 : ℕ) : ℤ) by omega]
          exact div_pos hnum hden

/-- Continued-fraction form of the three-term recurrence. -/
theorem centralChebyshevRatio_succ (j : ℕ) {t : ℝ}
    (hUj : chebyshevU j t ≠ 0) :
    centralChebyshevRatio (j + 1) t =
      (2 * t - centralChebyshevRatio j t)⁻¹ := by
  have hrec := chebyshevU_add_one (j : ℤ) t
  push_cast at hrec
  simp only [centralChebyshevRatio, Nat.cast_add, Nat.cast_one]
  rw [hrec]
  field_simp [hUj]
  ring_nf

/-- The quotient is strictly decreasing above the largest zero.  This is
an elementary continued-fraction proof equivalent to the source's
Christoffel--Darboux derivative argument. -/
theorem centralChebyshevRatio_strictAntiOn_succ (k : ℕ) :
    StrictAntiOn (centralChebyshevRatio (k + 1))
      (Ioi (centralChebyshevFirstNode (k + 1))) := by
  induction k with
  | zero =>
      intro x hx y hy hxy
      have hx0 : 0 < x := by
        simpa [centralChebyshevFirstNode] using hx
      have hy0 : 0 < y := hx0.trans hxy
      simpa [centralChebyshevRatio] using
        (one_div_strictAntiOn hx0 hy0 hxy)
  | succ k ih =>
      intro x hx y hy hxy
      have hnode := centralChebyshevFirstNode_lt_succ (k + 1)
      have hxPrev : centralChebyshevFirstNode (k + 1) < x :=
        hnode.trans hx
      have hyPrev : centralChebyshevFirstNode (k + 1) < y :=
        hnode.trans hy
      have hratio := ih hxPrev hyPrev hxy
      have hUx := chebyshevU_pos_above_centralFirstNode
        (k + 1) (by omega) hxPrev
      have hUy := chebyshevU_pos_above_centralFirstNode
        (k + 1) (by omega) hyPrev
      have hrecX := centralChebyshevRatio_succ (k + 1) hUx.ne'
      have hrecY := centralChebyshevRatio_succ (k + 1) hUy.ne'
      have hdenX : 0 < 2 * x - centralChebyshevRatio (k + 1) x := by
        have hratioPos := centralChebyshevRatio_pos (k + 2) (by omega) hx
        rw [hrecX] at hratioPos
        exact inv_pos.mp hratioPos
      have hdenY : 0 < 2 * y - centralChebyshevRatio (k + 1) y := by
        have hratioPos := centralChebyshevRatio_pos (k + 2) (by omega) hy
        rw [hrecY] at hratioPos
        exact inv_pos.mp hratioPos
      rw [hrecX, hrecY]
      apply (inv_lt_inv₀ hdenY hdenX).2
      nlinarith

theorem centralChebyshevRatio_strictAntiOn
    (j : ℕ) (hj : 1 ≤ j) :
    StrictAntiOn (centralChebyshevRatio j)
      (Ioi (centralChebyshevFirstNode j)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  simpa [Nat.add_comm] using centralChebyshevRatio_strictAntiOn_succ k

/-- The largest zero is strictly below one. -/
theorem centralChebyshevFirstNode_lt_one (j : ℕ) :
    centralChebyshevFirstNode j < 1 := by
  have hanglePos :
      0 < Real.pi / ((j + 1 : ℕ) : ℝ) := by positivity
  have hanglePi :
      Real.pi / ((j + 1 : ℕ) : ℝ) ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (j + 1 : ℕ))]
    have hjcast : (1 : ℝ) ≤ (j + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    nlinarith [Real.pi_pos]
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi
    (le_refl (0 : ℝ)) hanglePi hanglePos
  simpa [centralChebyshevFirstNode] using hcos

/-- A degree-independent large-argument bound for the quotient. -/
theorem centralChebyshevRatio_le_largeArgument
    (k : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    centralChebyshevRatio (k + 1) t ≤ 1 / (2 * t - 1) := by
  induction k with
  | zero =>
      have hden : 0 < 2 * t - 1 := by linarith
      have hle : 2 * t - 1 ≤ 2 * t := by linarith
      simpa [centralChebyshevRatio] using
        (one_div_le_one_div_of_le hden hle)
  | succ k ih =>
      have hnodePrev := centralChebyshevFirstNode_lt_one (k + 1)
      have htPrev : centralChebyshevFirstNode (k + 1) < t :=
        hnodePrev.trans_le ht
      have hU := chebyshevU_pos_above_centralFirstNode
        (k + 1) (by omega) htPrev
      have hdenBase : 0 < 2 * t - 1 := by linarith
      have hbaseLeOne : 1 / (2 * t - 1) ≤ 1 := by
        have hone : (1 : ℝ) ≤ 2 * t - 1 := by linarith
        simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hone
      have hratioLeOne : centralChebyshevRatio (k + 1) t ≤ 1 :=
        ih.trans hbaseLeOne
      have hdenLe :
          2 * t - 1 ≤ 2 * t - centralChebyshevRatio (k + 1) t := by
        linarith
      rw [centralChebyshevRatio_succ (k + 1) hU.ne']
      simpa only [one_div] using
        one_div_le_one_div_of_le hdenBase hdenLe

/-- Existence and uniqueness of the source's root `rho_j`. -/
theorem existsUnique_centralRho
    (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    ∃! ρ : ℝ,
      centralChebyshevFirstNode j < ρ ∧
        a * chebyshevU j ρ = chebyshevU ((j : ℤ) - 1) ρ := by
  let f : ℝ → ℝ := fun t ↦
    chebyshevU ((j : ℤ) - 1) t - a * chebyshevU j t
  let T : ℝ := 1 + a⁻¹
  let c : ℝ := centralChebyshevFirstNode j
  have hUc : chebyshevU j c = 0 := by
    dsimp [c, centralChebyshevFirstNode]
    simpa only [Nat.cast_one, one_mul, Nat.cast_add] using
      chebyshevU_nodal_zero (n := j) (k := 1) (by omega) hj
  have hUprevC : 0 < chebyshevU ((j : ℤ) - 1) c := by
    cases j with
    | zero => omega
    | succ k =>
        cases k with
        | zero => norm_num
        | succ k =>
            have hnode := centralChebyshevFirstNode_lt_succ (k + 1)
            have hpos := chebyshevU_pos_above_centralFirstNode
              (k + 1) (by omega) hnode
            simpa only [c,
              show (((k + 2 : ℕ) : ℤ) - 1) =
                ((k + 1 : ℕ) : ℤ) by omega] using hpos
  have hfC : 0 < f c := by
    dsimp [f]
    rw [hUc]
    simpa using hUprevC
  have hTOne : 1 ≤ T := by
    have hinv : 1 < a⁻¹ := (one_lt_inv₀ ha₀).2 ha₁
    dsimp [T]
    linarith
  have hnodeT : c < T :=
    (centralChebyshevFirstNode_lt_one j).trans_le hTOne
  have hratioBound := centralChebyshevRatio_le_largeArgument
    (j - 1) hTOne
  have hratioIndex : centralChebyshevRatio (j - 1 + 1) T =
      centralChebyshevRatio j T := by
    rw [Nat.sub_add_cancel hj]
  rw [hratioIndex] at hratioBound
  have hdenT : 0 < 2 * T - 1 := by linarith
  have hboundLt : 1 / (2 * T - 1) < a := by
    rw [div_lt_iff₀ hdenT]
    dsimp [T]
    field_simp [ha₀.ne']
    nlinarith
  have hratioT : centralChebyshevRatio j T < a :=
    hratioBound.trans_lt hboundLt
  have hUjT := chebyshevU_pos_above_centralFirstNode j hj hnodeT
  have hfT : f T < 0 := by
    dsimp [f]
    have h := (div_lt_iff₀ hUjT).mp hratioT
    simpa [centralChebyshevRatio] using sub_neg.mpr h
  have hcT : c ≤ T := hnodeT.le
  have hcont : Continuous f :=
    (continuous_chebyshevU ((j : ℤ) - 1)).sub
      (continuous_const.mul (continuous_chebyshevU j))
  obtain ⟨ρ, hρIcc, hρzero⟩ :=
    (intermediate_value_Icc' hcT hcont.continuousOn)
      (⟨hfT.le, hfC.le⟩ : (0 : ℝ) ∈ Icc (f T) (f c))
  have hcρ : c < ρ := by
    refine lt_of_le_of_ne hρIcc.1 ?_
    intro hρc
    subst ρ
    rw [hρzero] at hfC
    exact (lt_irrefl 0 hfC)
  have hEq : a * chebyshevU j ρ =
      chebyshevU ((j : ℤ) - 1) ρ := by
    dsimp [f] at hρzero
    linarith
  refine ⟨ρ, ⟨hcρ, hEq⟩, ?_⟩
  intro y hy
  apply (centralChebyshevRatio_strictAntiOn j hj).injOn hy.1 hcρ
  have hUρ := chebyshevU_pos_above_centralFirstNode j hj hcρ
  have hUy := chebyshevU_pos_above_centralFirstNode j hj hy.1
  dsimp [centralChebyshevRatio]
  rw [← hEq, ← hy.2]
  field_simp [hUρ.ne', hUy.ne']

/-- The chosen root `rho_j(a)`.  Outside the source's parameter range it is
set to zero; all public facts below carry the source hypotheses. -/
noncomputable def centralRho (j : ℕ) (a : ℝ) : ℝ :=
  if h : 1 ≤ j ∧ 0 < a ∧ a < 1 then
    Classical.choose
      (existsUnique_centralRho j h.1 a h.2.1 h.2.2).exists
  else 0

theorem centralRho_spec
    (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    centralChebyshevFirstNode j < centralRho j a ∧
      a * chebyshevU j (centralRho j a) =
        chebyshevU ((j : ℤ) - 1) (centralRho j a) := by
  rw [centralRho, dif_pos ⟨hj, ha₀, ha₁⟩]
  exact Classical.choose_spec
    (existsUnique_centralRho j hj a ha₀ ha₁).exists

theorem centralRho_unique
    (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1)
    {ρ : ℝ} (hnode : centralChebyshevFirstNode j < ρ)
    (hEq : a * chebyshevU j ρ = chebyshevU ((j : ℤ) - 1) ρ) :
    ρ = centralRho j a := by
  exact (existsUnique_centralRho j hj a ha₀ ha₁).unique
    ⟨hnode, hEq⟩ (centralRho_spec j hj a ha₀ ha₁)

/-! ## Identification with the actual least singular value -/

/-- The upper bidiagonal determinant is the product of its diagonal
entries. -/
theorem det_realCentralBidiagonal (j : ℕ) (a : ℝ) :
    (realCentralBidiagonal j a).det = a ^ j := by
  have htri : (realCentralBidiagonal j a).BlockTriangular id := by
    intro p q hqp
    have hpq : p ≠ q := by
      intro hpq
      subst q
      exact (lt_irrefl p hqp)
    have hadj : ¬q.1 = p.1 + 1 := by
      change q < p at hqp
      omega
    simp [realCentralBidiagonal_apply, hpq, hadj]
  rw [Matrix.det_of_upperTriangular htri]
  simp [realCentralBidiagonal_apply]

theorem det_complexCentralBidiagonal (j : ℕ) (a : ℝ) :
    (complexCentralBidiagonal j a).det = (a ^ j : ℝ) := by
  rw [complexCentralBidiagonal]
  change (Complex.ofRealHom.mapMatrix (realCentralBidiagonal j a)).det = _
  rw [← Complex.ofRealHom.map_det, det_realCentralBidiagonal]
  rfl

/-- For positive dimension and `a>0`, the actual central height is
strictly positive. -/
theorem centralBidiagonalHeight_pos
    (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha : 0 < a) :
    0 < centralBidiagonalHeight j a := by
  have hdet : (complexCentralBidiagonal j a).det ≠ 0 := by
    rw [det_complexCentralBidiagonal]
    exact_mod_cast pow_ne_zero j ha.ne'
  have hne : centralBidiagonalHeight j a ≠ 0 := by
    intro hzero
    apply hdet
    exact (leastSingularValue_eq_zero_iff_det_eq_zero
      (complexCentralBidiagonal j a) (by omega)).1 hzero
  exact lt_of_le_of_ne
    (leastSingularValue_nonneg (complexCentralBidiagonal j a))
    (Ne.symm hne)

/-- The scalar whose square root is selected by a solution of the central
continuant equation. -/
def centralRhoLambda (a ρ : ℝ) : ℝ :=
  1 + a ^ 2 - 2 * a * ρ

/-- A solution of the central equation has nonzero `U_j`. -/
theorem chebyshevU_ne_zero_of_centralEquation
    (j : ℕ) (a ρ : ℝ)
    (hEq : a * chebyshevU j ρ = chebyshevU ((j : ℤ) - 1) ρ) :
    chebyshevU j ρ ≠ 0 := by
  intro hzero
  have hprev : chebyshevU ((j : ℤ) - 1) ρ = 0 := by
    rw [← hEq, hzero, mul_zero]
  have hinv := chebyshevU_sq_add_sq_sub j ρ
  rw [hzero, hprev] at hinv
  norm_num at hinv

/-- Algebraic consequence of the quadratic Chebyshev invariant. -/
theorem centralRhoLambda_eq_inv_sq
    (j : ℕ) (a ρ : ℝ)
    (hEq : a * chebyshevU j ρ = chebyshevU ((j : ℤ) - 1) ρ) :
    centralRhoLambda a ρ = 1 / chebyshevU j ρ ^ 2 := by
  have hU := chebyshevU_ne_zero_of_centralEquation j a ρ hEq
  have hinv := chebyshevU_sq_add_sq_sub j ρ
  rw [← hEq] at hinv
  apply (eq_div_iff (pow_ne_zero 2 hU)).2
  dsimp [centralRhoLambda]
  nlinarith

theorem centralRhoLambda_pos
    (j : ℕ) (a ρ : ℝ)
    (hEq : a * chebyshevU j ρ = chebyshevU ((j : ℤ) - 1) ρ) :
    0 < centralRhoLambda a ρ := by
  have hU := chebyshevU_ne_zero_of_centralEquation j a ρ hEq
  rw [centralRhoLambda_eq_inv_sq j a ρ hEq]
  exact one_div_pos.mpr (sq_pos_of_ne_zero hU)

private theorem centralRoot_gives_height_sq_upperBound
    (j : ℕ) (hj : 1 ≤ j) (a ρ : ℝ) (ha : 0 < a)
    (hEq : a * chebyshevU j ρ = chebyshevU ((j : ℤ) - 1) ρ) :
    centralBidiagonalHeight j a ^ 2 ≤ centralRhoLambda a ρ := by
  let lam : ℝ := centralRhoLambda a ρ
  let tau : ℝ := Real.sqrt lam
  let M : Matrix (Fin j) (Fin j) ℂ := complexCentralBidiagonal j a
  have hlam : 0 < lam := centralRhoLambda_pos j a ρ hEq
  have htausq : tau ^ 2 = lam := Real.sq_sqrt hlam.le
  have hmatrix :
      gramShift M tau =
        Mᴴ * M - ((centralRhoLambda a ρ : ℝ) : ℂ) •
          (1 : Matrix (Fin j) (Fin j) ℂ) := by
    simp only [gramShift, M, tau, lam, htausq]
  have hdet : (gramShift M tau).det = 0 := by
    rw [hmatrix]
    change
      ((complexCentralBidiagonal j a)ᴴ * complexCentralBidiagonal j a -
        ((1 + a ^ 2 - 2 * a * ρ : ℝ) : ℂ) •
          (1 : Matrix (Fin j) (Fin j) ℂ)).det = 0
    rw [complexCentralBidiagonal_gram_det j ha.ne']
    rw [← hEq]
    simp [ha.ne']
  have hnotPosDef : ¬(gramShift M tau).PosDef := by
    intro hpos
    have hunit := Matrix.PosDef.isUnit hpos
    have hdetUnit := (Matrix.isUnit_iff_isUnit_det (gramShift M tau)).mp hunit
    rw [hdet] at hdetUnit
    exact not_isUnit_zero hdetUnit
  have htaunonneg : 0 ≤ tau := Real.sqrt_nonneg lam
  have hnotlt : ¬tau < centralBidiagonalHeight j a := by
    intro hlt
    apply hnotPosDef
    exact (gramShift_posDef_iff_lt_leastSingularValue M (by omega)
      tau htaunonneg).2 hlt
  have hheightNonneg : 0 ≤ centralBidiagonalHeight j a :=
    leastSingularValue_nonneg M
  have hle : centralBidiagonalHeight j a ≤ tau := le_of_not_gt hnotlt
  have hsquare : centralBidiagonalHeight j a ^ 2 ≤ tau ^ 2 :=
    (sq_le_sq₀ hheightNonneg htaunonneg).2 hle
  simpa only [htausq, lam] using hsquare

/-- The least singular value itself yields a real root of the central
continuant equation after the affine spectral change of variables. -/
private theorem centralHeightRootParameter_spec
    (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha : 0 < a) :
    let q := (1 + a ^ 2 - centralBidiagonalHeight j a ^ 2) / (2 * a)
    a * chebyshevU j q = chebyshevU ((j : ℤ) - 1) q := by
  let M : Matrix (Fin j) (Fin j) ℂ := complexCentralBidiagonal j a
  let s : ℝ := centralBidiagonalHeight j a
  let q : ℝ := (1 + a ^ 2 - s ^ 2) / (2 * a)
  have hsnonneg : 0 ≤ s := leastSingularValue_nonneg M
  have hpsd : (gramShift M s).PosSemidef :=
    gramShift_leastSingularValue_posSemidef M (by omega)
  have hnotPosDef : ¬(gramShift M s).PosDef := by
    rw [gramShift_posDef_iff_lt_leastSingularValue M (by omega) s hsnonneg]
    exact lt_irrefl s
  have hnotUnit : ¬IsUnit (gramShift M s) := by
    intro hunit
    exact hnotPosDef (hpsd.posDef_iff_isUnit.mpr hunit)
  have hdet : (gramShift M s).det = 0 := by
    by_contra hne
    apply hnotUnit
    exact (Matrix.isUnit_iff_isUnit_det (gramShift M s)).mpr
      (isUnit_iff_ne_zero.mpr hne)
  have hscalar : 1 + a ^ 2 - 2 * a * q = s ^ 2 := by
    dsimp [q]
    field_simp [ha.ne']
    ring
  have hformula := complexCentralBidiagonal_gram_det j (t := q) ha.ne'
  have hgramEq :
      (complexCentralBidiagonal j a)ᴴ * complexCentralBidiagonal j a -
          ((1 + a ^ 2 - 2 * a * q : ℝ) : ℂ) •
            (1 : Matrix (Fin j) (Fin j) ℂ) =
        gramShift M s := by
    rw [hscalar]
    rfl
  rw [hgramEq, hdet] at hformula
  have hreal :
      a ^ j *
        (chebyshevU j q - a⁻¹ * chebyshevU ((j : ℤ) - 1) q) = 0 := by
    exact_mod_cast hformula.symm
  have hfactor :
      chebyshevU j q - a⁻¹ * chebyshevU ((j : ℤ) - 1) q = 0 :=
    (mul_eq_zero.mp hreal).resolve_left (pow_ne_zero j ha.ne')
  dsimp only
  change a * chebyshevU j q = chebyshevU ((j : ℤ) - 1) q
  calc
    a * chebyshevU j q =
        a * (a⁻¹ * chebyshevU ((j : ℤ) - 1) q) := by
      congr 1
      linarith
    _ = chebyshevU ((j : ℤ) - 1) q := by field_simp

/-- First identity in `eq:c-rho-identities`, before replacing the right
side by the Chebyshev reciprocal. -/
theorem centralBidiagonalHeight_sq_eq_rhoLambda
    (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    centralBidiagonalHeight j a ^ 2 =
      centralRhoLambda a (centralRho j a) := by
  let ρ : ℝ := centralRho j a
  let s : ℝ := centralBidiagonalHeight j a
  let q : ℝ := (1 + a ^ 2 - s ^ 2) / (2 * a)
  have hρ := centralRho_spec j hj a ha₀ ha₁
  have hsqLe : s ^ 2 ≤ centralRhoLambda a ρ :=
    centralRoot_gives_height_sq_upperBound j hj a ρ ha₀ hρ.2
  have hqEq : a * chebyshevU j q =
      chebyshevU ((j : ℤ) - 1) q := by
    exact centralHeightRootParameter_spec j hj a ha₀
  have hqGe : ρ ≤ q := by
    dsimp [q, s, centralRhoLambda] at hsqLe ⊢
    rw [le_div_iff₀ (mul_pos (by norm_num) ha₀)]
    nlinarith
  have hqNode : centralChebyshevFirstNode j < q := hρ.1.trans_le hqGe
  have hqRho : q = ρ := centralRho_unique j hj a ha₀ ha₁ hqNode hqEq
  have hden : 2 * a ≠ 0 := mul_ne_zero (by norm_num) ha₀.ne'
  have hlin : 1 + a ^ 2 - centralBidiagonalHeight j a ^ 2 =
      (2 * a) * centralRho j a := by
    have hraw : 1 + a ^ 2 - centralBidiagonalHeight j a ^ 2 =
        centralRho j a * (2 * a) := by
      apply (div_eq_iff hden).mp
      simpa only [q, s, ρ] using hqRho
    calc
      1 + a ^ 2 - centralBidiagonalHeight j a ^ 2 =
          centralRho j a * (2 * a) := hraw
      _ = (2 * a) * centralRho j a := mul_comm _ _
  dsimp [centralRhoLambda]
  nlinarith

/-- The first displayed `eq:c-rho-identities` equality for the actual
Euclidean least singular value. -/
theorem centralBidiagonalHeight_sq_eq_inv_chebyshev
    (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    centralBidiagonalHeight j a ^ 2 =
      1 / chebyshevU j (centralRho j a) ^ 2 := by
  rw [centralBidiagonalHeight_sq_eq_rhoLambda j hj a ha₀ ha₁]
  exact centralRhoLambda_eq_inv_sq j a (centralRho j a)
    (centralRho_spec j hj a ha₀ ha₁).2

/-- The second equality in `eq:c-rho-identities`. -/
theorem centralZeta_sub_rho_eq
    (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    (a + a⁻¹) / 2 - centralRho j a =
      1 / (2 * chebyshevU ((j : ℤ) - 1) (centralRho j a) *
        chebyshevU j (centralRho j a)) := by
  let ρ : ℝ := centralRho j a
  let U : ℝ := chebyshevU j ρ
  have hEq : a * U = chebyshevU ((j : ℤ) - 1) ρ :=
    (centralRho_spec j hj a ha₀ ha₁).2
  have hU : U ≠ 0 :=
    chebyshevU_ne_zero_of_centralEquation j a ρ hEq
  have hlambda : centralRhoLambda a ρ = 1 / U ^ 2 := by
    simpa only [U] using centralRhoLambda_eq_inv_sq j a ρ hEq
  have hlambdaMul : centralRhoLambda a ρ * U ^ 2 = 1 := by
    rw [hlambda]
    field_simp [hU]
  dsimp [centralRhoLambda] at hlambda
  dsimp [centralRhoLambda, ρ, U] at hEq hU hlambda hlambdaMul ⊢
  rw [← hEq]
  field_simp [ha₀.ne', hU]
  nlinarith [hlambdaMul]

/-- The two identities of `eq:c-rho-identities`, bundled exactly in the
order printed in the source. -/
theorem centralRho_identities
    (j : ℕ) (hj : 1 ≤ j) (a : ℝ) (ha₀ : 0 < a) (ha₁ : a < 1) :
    (centralBidiagonalHeight j a ^ 2 =
        1 / chebyshevU j (centralRho j a) ^ 2) ∧
      ((a + a⁻¹) / 2 - centralRho j a =
        1 / (2 * chebyshevU ((j : ℤ) - 1) (centralRho j a) *
          chebyshevU j (centralRho j a))) :=
  ⟨centralBidiagonalHeight_sq_eq_inv_chebyshev j hj a ha₀ ha₁,
    centralZeta_sub_rho_eq j hj a ha₀ ha₁⟩

end

end ConnectedPseudospectrum
