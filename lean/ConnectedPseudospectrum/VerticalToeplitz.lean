import ConnectedPseudospectrum.PathSpectrum
import ConnectedPseudospectrum.VerticalPencil

/-!
# The pentadiagonal Toeplitz core of the vertical pencil

This module isolates the pure Toeplitz matrix in the proof of `lem:vertical`.
The two missing shift products at the path endpoints give exactly the first
diagonal correction `-1` and the last diagonal correction `-a²`.  The
comparison theorem is stated only from dimension two onward, because in
dimension one the two endpoint corrections coincide.
-/

namespace ConnectedPseudospectrum

open Matrix

noncomputable section

/-- The diagonal coefficient `d = x² + Y + 1 + a² - t²` of the pure
pentadiagonal Toeplitz matrix. -/
def verticalToeplitzDiagonal (a x Y t : ℝ) : ℝ :=
  x ^ 2 + Y + 1 + a ^ 2 - t ^ 2

/-- The first upper-diagonal coefficient
`b = -(1+a)x + i(1-a)√Y`. -/
def verticalToeplitzFirst (a x Y : ℝ) : ℂ :=
  ((-(1 + a) * x : ℝ) : ℂ) +
    Complex.I * (((1 - a) * Real.sqrt Y : ℝ) : ℂ)

/-- The first upper coefficient in terms of the vertical spectral point and
its conjugate. -/
theorem verticalToeplitzFirst_eq (a x Y : ℝ) :
    verticalToeplitzFirst a x Y =
      -((x : ℂ) - Complex.I * (Real.sqrt Y : ℂ)) -
        (a : ℂ) * ((x : ℂ) + Complex.I * (Real.sqrt Y : ℂ)) := by
  apply Complex.ext
  · simp [verticalToeplitzFirst]
    ring
  · simp [verticalToeplitzFirst]
    ring

/-- The first lower coefficient is the complex conjugate of the first upper
coefficient. -/
theorem star_verticalToeplitzFirst_eq (a x Y : ℝ) :
    star (verticalToeplitzFirst a x Y) =
      -((x : ℂ) + Complex.I * (Real.sqrt Y : ℂ)) -
        (a : ℂ) * ((x : ℂ) - Complex.I * (Real.sqrt Y : ℂ)) := by
  apply Complex.ext
  · simp [verticalToeplitzFirst]
    ring
  · simp [verticalToeplitzFirst]
    ring

/-- The real upper shift, cast entrywise to a complex matrix. -/
def complexUpperShift (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (upperShift n).map Complex.ofRealHom

/-- The real lower shift, cast entrywise to a complex matrix. -/
def complexLowerShift (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (lowerShift n).map Complex.ofRealHom

@[simp] theorem complexUpperShift_apply (n : ℕ) (i j : Fin n) :
    complexUpperShift n i j = if j.1 = i.1 + 1 then 1 else 0 := by
  simp [complexUpperShift, upperShift_apply]

@[simp] theorem complexLowerShift_apply (n : ℕ) (i j : Fin n) :
    complexLowerShift n i j = if i.1 = j.1 + 1 then 1 else 0 := by
  simp [complexLowerShift, lowerShift_apply]

@[simp] theorem complexUpperShift_conjTranspose (n : ℕ) :
    (complexUpperShift n)ᴴ = complexLowerShift n := by
  ext i j
  simp [Matrix.conjTranspose_apply]

@[simp] theorem complexLowerShift_conjTranspose (n : ℕ) :
    (complexLowerShift n)ᴴ = complexUpperShift n := by
  ext i j
  simp [Matrix.conjTranspose_apply]

/-- The second upper diagonal of the square of the finite upper shift. -/
theorem upperShift_mul_upperShift_apply (n : ℕ) (i j : Fin n) :
    (upperShift n * upperShift n) i j =
      if j.1 = i.1 + 2 then 1 else 0 := by
  change (upperShift n *ᵥ fun k => upperShift n k j) i = _
  by_cases hi : i.1 + 1 < n
  · rw [upperShift_mulVec_apply_of_lt n _ i hi]
    simp only [upperShift_apply]
  · rw [upperShift_mulVec_apply_of_not_lt n _ i hi]
    rw [if_neg]
    omega

/-- The second lower diagonal of the square of the finite lower shift. -/
theorem lowerShift_mul_lowerShift_apply (n : ℕ) (i j : Fin n) :
    (lowerShift n * lowerShift n) i j =
      if i.1 = j.1 + 2 then 1 else 0 := by
  change (lowerShift n *ᵥ fun k => lowerShift n k j) i = _
  by_cases hi : 0 < i.1
  · rw [lowerShift_mulVec_apply_of_pos n _ i hi]
    simp only [lowerShift_apply]
    by_cases h : i.1 = j.1 + 2
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  · rw [lowerShift_mulVec_apply_of_eq_zero n _ i (by omega)]
    rw [if_neg]
    omega

/-- `VᵀV` is the identity except at the first coordinate. -/
theorem lowerShift_mul_upperShift_apply (n : ℕ) (i j : Fin n) :
    (lowerShift n * upperShift n) i j =
      if i = j ∧ 0 < i.1 then 1 else 0 := by
  change (lowerShift n *ᵥ fun k => upperShift n k j) i = _
  by_cases hi : 0 < i.1
  · rw [lowerShift_mulVec_apply_of_pos n _ i hi]
    simp only [upperShift_apply]
    by_cases hij : i = j
    · subst j
      rw [if_pos (by omega), if_pos ⟨rfl, hi⟩]
    · rw [if_neg]
      · rw [if_neg (fun h => hij h.1)]
      · intro h
        apply hij
        apply Fin.ext
        omega
  · rw [lowerShift_mulVec_apply_of_eq_zero n _ i (by omega)]
    rw [if_neg]
    exact fun h => hi h.2

/-- `VVᵀ` is the identity except at the last coordinate. -/
theorem upperShift_mul_lowerShift_apply (n : ℕ) (i j : Fin n) :
    (upperShift n * lowerShift n) i j =
      if i = j ∧ i.1 + 1 < n then 1 else 0 := by
  change (upperShift n *ᵥ fun k => lowerShift n k j) i = _
  by_cases hi : i.1 + 1 < n
  · rw [upperShift_mulVec_apply_of_lt n _ i hi]
    simp only [lowerShift_apply]
    by_cases hij : i = j
    · subst j
      rw [if_pos (by omega), if_pos ⟨rfl, hi⟩]
    · rw [if_neg]
      · rw [if_neg (fun h => hij h.1)]
      · intro h
        apply hij
        apply Fin.ext
        omega
  · rw [upperShift_mulVec_apply_of_not_lt n _ i hi]
    rw [if_neg]
    exact fun h => hi h.2

theorem complexUpperShift_mul_upperShift_apply (n : ℕ) (i j : Fin n) :
    (complexUpperShift n * complexUpperShift n) i j =
      if j.1 = i.1 + 2 then 1 else 0 := by
  change ((upperShift n).map Complex.ofRealHom *
      (upperShift n).map Complex.ofRealHom) i j = _
  rw [← Matrix.map_mul]
  simp [upperShift_mul_upperShift_apply]

theorem complexLowerShift_mul_lowerShift_apply (n : ℕ) (i j : Fin n) :
    (complexLowerShift n * complexLowerShift n) i j =
      if i.1 = j.1 + 2 then 1 else 0 := by
  change ((lowerShift n).map Complex.ofRealHom *
      (lowerShift n).map Complex.ofRealHom) i j = _
  rw [← Matrix.map_mul]
  simp [lowerShift_mul_lowerShift_apply]

theorem complexLowerShift_mul_upperShift_apply (n : ℕ) (i j : Fin n) :
    (complexLowerShift n * complexUpperShift n) i j =
      if i = j ∧ 0 < i.1 then 1 else 0 := by
  change ((lowerShift n).map Complex.ofRealHom *
      (upperShift n).map Complex.ofRealHom) i j = _
  rw [← Matrix.map_mul]
  simp [lowerShift_mul_upperShift_apply]

theorem complexUpperShift_mul_lowerShift_apply (n : ℕ) (i j : Fin n) :
    (complexUpperShift n * complexLowerShift n) i j =
      if i = j ∧ i.1 + 1 < n then 1 else 0 := by
  change ((upperShift n).map Complex.ofRealHom *
      (lowerShift n).map Complex.ofRealHom) i j = _
  rw [← Matrix.map_mul]
  simp [upperShift_mul_lowerShift_apply]

/-- The pure pentadiagonal Toeplitz matrix with diagonals
`a, conj b, d, b, a`. -/
def verticalToeplitz (n : ℕ) (a x Y t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (verticalToeplitzDiagonal a x Y t : ℂ) • 1 +
    verticalToeplitzFirst a x Y • complexUpperShift n +
    star (verticalToeplitzFirst a x Y) • complexLowerShift n +
    (a : ℂ) •
      (complexUpperShift n * complexUpperShift n +
        complexLowerShift n * complexLowerShift n)

/-- Explicit five-diagonal entry formula for the pure Toeplitz matrix. -/
theorem verticalToeplitz_apply (n : ℕ) (a x Y t : ℝ) (i j : Fin n) :
    verticalToeplitz n a x Y t i j =
      (verticalToeplitzDiagonal a x Y t : ℂ) * (if i = j then 1 else 0) +
        verticalToeplitzFirst a x Y * (if j.1 = i.1 + 1 then 1 else 0) +
        star (verticalToeplitzFirst a x Y) * (if i.1 = j.1 + 1 then 1 else 0) +
        (a : ℂ) * (if j.1 = i.1 + 2 then 1 else 0) +
        (a : ℂ) * (if i.1 = j.1 + 2 then 1 else 0) := by
  simp [verticalToeplitz, Matrix.one_apply, Matrix.smul_apply,
    complexUpperShift_mul_upperShift_apply,
    complexLowerShift_mul_lowerShift_apply, smul_eq_mul]
  ring

/-- The determinant `Tₙ` of the pure pentadiagonal Toeplitz matrix. -/
def verticalToeplitzDet (n : ℕ) (a x Y t : ℝ) : ℂ :=
  (verticalToeplitz n a x Y t).det

/-- The empty Toeplitz determinant has the convention `T₀ = 1`. -/
@[simp] theorem verticalToeplitzDet_zero (a x Y t : ℝ) :
    verticalToeplitzDet 0 a x Y t = 1 := by
  exact Matrix.det_fin_zero

/-- The first Toeplitz determinant is `T₁ = d`. -/
@[simp] theorem verticalToeplitzDet_one (a x Y t : ℝ) :
    verticalToeplitzDet 1 a x Y t =
      (verticalToeplitzDiagonal a x Y t : ℂ) := by
  rw [verticalToeplitzDet, Matrix.det_fin_one]
  simp [verticalToeplitz_apply]

/-- The second Toeplitz determinant is `T₂ = d² - |b|²`. -/
@[simp] theorem verticalToeplitzDet_two (a x Y t : ℝ) :
    verticalToeplitzDet 2 a x Y t =
      (verticalToeplitzDiagonal a x Y t : ℂ) ^ 2 -
        (Complex.normSq (verticalToeplitzFirst a x Y) : ℂ) := by
  rw [verticalToeplitzDet, Matrix.det_fin_two]
  simp only [verticalToeplitz_apply]
  norm_num
  rw [Complex.mul_conj]
  ring

/-- The complex path is the sum of the cast upper shift and `a` times its
lower transpose. -/
theorem complexPathMatrix_eq_complex_shifts (n : ℕ) (a : ℝ) :
    complexPathMatrix n a =
      complexUpperShift n + (a : ℂ) • complexLowerShift n := by
  change (pathMatrix n a).map Complex.ofRealHom =
    complexUpperShift n + (a : ℂ) • complexLowerShift n
  rw [pathMatrix_eq_upper_add_lower]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    complexUpperShift, complexLowerShift, smul_eq_mul, map_add, map_mul,
    Complex.ofRealHom_eq_coe]

/-- Shift-polynomial form of the matrix whose Gram matrix defines the
vertical pencil. -/
theorem verticalShiftedMatrix_eq_complex_shifts (n : ℕ) (a x Y : ℝ) :
    verticalShiftedMatrix n a x Y =
      ((x : ℂ) + Complex.I * (Real.sqrt Y : ℂ)) • 1 -
        complexUpperShift n - (a : ℂ) • complexLowerShift n := by
  rw [verticalShiftedMatrix, shiftedPathMatrix,
    complexPathMatrix_eq_complex_shifts]
  abel

/-- Entrywise Gram expansion before replacing `(√Y)²` by `Y`. -/
theorem verticalPencil_apply_shift_expansion (n : ℕ) (a x Y t : ℝ)
    (i j : Fin n) :
    verticalPencil n a x Y t i j =
      ((((x : ℂ) + Complex.I * (Real.sqrt Y : ℂ)) *
          ((x : ℂ) - Complex.I * (Real.sqrt Y : ℂ))) - (t : ℂ) ^ 2) *
          (if i = j then 1 else 0) +
        verticalToeplitzFirst a x Y * complexUpperShift n i j +
        star (verticalToeplitzFirst a x Y) * complexLowerShift n i j +
        (complexLowerShift n * complexUpperShift n) i j +
        (a : ℂ) ^ 2 * (complexUpperShift n * complexLowerShift n) i j +
        (a : ℂ) * (complexUpperShift n * complexUpperShift n) i j +
        (a : ℂ) * (complexLowerShift n * complexLowerShift n) i j := by
  rw [verticalPencil, verticalShiftedMatrix_eq_complex_shifts]
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, complexUpperShift_conjTranspose,
    complexLowerShift_conjTranspose, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  have hzstar :
      star ((x : ℂ) + Complex.I * (Real.sqrt Y : ℂ)) =
        (x : ℂ) - Complex.I * (Real.sqrt Y : ℂ) := by
    simp
    rfl
  have hastar : star (a : ℂ) = (a : ℂ) := by
    simp
  have ht : (((t ^ 2 : ℝ) : ℂ)) = (t : ℂ) ^ 2 := by
    norm_cast
  rw [hzstar, hastar, ht, star_verticalToeplitzFirst_eq,
    verticalToeplitzFirst_eq]
  ring

/-- For `n ≥ 2`, the vertical pencil is the pure Toeplitz matrix with the
first diagonal lowered by `1` and the last diagonal lowered by `a²`. -/
theorem verticalPencil_apply_eq_verticalToeplitz_sub_endpoints
    (n : ℕ) (hn : 2 ≤ n) (a x Y t : ℝ) (hY : 0 ≤ Y) (i j : Fin n) :
    verticalPencil n a x Y t i j =
      verticalToeplitz n a x Y t i j -
        (if i = j ∧ i.1 = 0 then 1 else 0) -
        (if i = j ∧ i.1 + 1 = n then (a : ℂ) ^ 2 else 0) := by
  rw [verticalPencil_apply_shift_expansion]
  rw [verticalToeplitz_apply]
  rw [complexLowerShift_mul_upperShift_apply,
    complexUpperShift_mul_lowerShift_apply,
    complexUpperShift_mul_upperShift_apply,
    complexLowerShift_mul_lowerShift_apply]
  have hsq : ((Real.sqrt Y : ℂ) ^ 2) = (Y : ℂ) := by
    exact_mod_cast Real.sq_sqrt hY
  have hbase :
      (((x : ℂ) + Complex.I * (Real.sqrt Y : ℂ)) *
          ((x : ℂ) - Complex.I * (Real.sqrt Y : ℂ)) - (t : ℂ) ^ 2) =
        ((x ^ 2 + Y - t ^ 2 : ℝ) : ℂ) := by
    calc
      ((x : ℂ) + Complex.I * (Real.sqrt Y : ℂ)) *
            ((x : ℂ) - Complex.I * (Real.sqrt Y : ℂ)) - (t : ℂ) ^ 2 =
          (x : ℂ) ^ 2 - (Complex.I * (Real.sqrt Y : ℂ)) ^ 2 -
            (t : ℂ) ^ 2 := by
              ring
      _ =
          (x : ℂ) ^ 2 + (Real.sqrt Y : ℂ) ^ 2 - (t : ℂ) ^ 2 := by
            rw [mul_pow, Complex.I_sq]
            ring
      _ = ((x ^ 2 + Y - t ^ 2 : ℝ) : ℂ) := by
        rw [hsq]
        norm_cast
  rw [hbase]
  simp only [complexUpperShift_apply, complexLowerShift_apply]
  by_cases hij : i = j
  · subst j
    by_cases hfirst : i.1 = 0
    · by_cases hlast : i.1 + 1 = n
      · omega
      · have hone : 1 < n := by omega
        have hne : (1 : ℕ) ≠ n := by omega
        simp [hfirst, hone, hne, verticalToeplitzDiagonal]
        ring
    · by_cases hlast : i.1 + 1 = n
      · have hpos : 0 < i.1 := by omega
        simp [hfirst, hlast, hpos,
          verticalToeplitzDiagonal]
        ring
      · have hpos : 0 < i.1 := by omega
        have hlt : i.1 + 1 < n := by omega
        simp [hfirst, hlast, hpos, hlt,
          verticalToeplitzDiagonal]
        ring
  · simp [hij]

end

end ConnectedPseudospectrum
