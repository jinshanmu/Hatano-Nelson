import ConnectedPseudospectrum.OddCentralLowerAngle
import ConnectedPseudospectrum.HermitianWeylPerturbation
import ConnectedPseudospectrum.SignedPencilProductParity

/-!
# The strict lower half of the odd central interlacing comparison

This module completes the lower inequality in `eq:central-interlace`.  At the centre of the odd
signed-middle pencil, zero is a simple eigenvalue and every other absolute
eigenvalue is at least the explicitly attained second singular value.
Weyl perturbation therefore leaves at most one eigenvalue in `(-c,c)` at
the test abscissa `x_*`.  The positive signed-pencil product and its exact
parity factorization exclude that remaining possibility, so the actual
least singular value at `x_*` is strictly greater than `c`.
-/

namespace ConnectedPseudospectrum

open Matrix Module Set

noncomputable section

/-! ## A generic ordered-eigenvalue uniqueness consequence -/

/-- If the zero eigenspace of a real Hermitian matrix has dimension one,
then at most one member of its ordered orthonormal eigenbasis can have
eigenvalue zero. -/
theorem orderedHermitianEigenvalue_zero_unique_of_eigenspace_finrank_eq_one
    {n : Nat} {A : Matrix (Fin n) (Fin n) Real}
    (hA : A.IsHermitian)
    (hsimple :
      Module.finrank Real (Module.End.eigenspace A.toLin' 0) = 1) :
    ∀ i j : Fin n,
      orderedHermitianEigenvalue hA i = 0 →
      orderedHermitianEigenvalue hA j = 0 → i = j := by
  intro i j hi hj
  by_contra hij
  let vi : Fin n → Real := orderedHermitianEigenbasis hA i
  let vj : Fin n → Real := orderedHermitianEigenbasis hA j
  have hviMem : vi ∈ Module.End.eigenspace A.toLin' 0 := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    have heig := mulVec_orderedHermitianEigenbasis hA i
    rw [hi, zero_smul] at heig
    simpa only [vi, zero_smul] using heig
  have hvjMem : vj ∈ Module.End.eigenspace A.toLin' 0 := by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    have heig := mulVec_orderedHermitianEigenbasis hA j
    rw [hj, zero_smul] at heig
    simpa only [vj, zero_smul] using heig
  let vi0 : Module.End.eigenspace A.toLin' 0 := ⟨vi, hviMem⟩
  let vj0 : Module.End.eigenspace A.toLin' 0 := ⟨vj, hvjMem⟩
  have hviNeFun : vi ≠ 0 := by
    intro hzero
    apply (orderedHermitianEigenbasis hA).toBasis.ne_zero i
    apply WithLp.ofLp_injective 2
    exact hzero
  have hviNe : vi0 ≠ 0 := by
    intro hzero
    apply hviNeFun
    have hval := congrArg Subtype.val hzero
    change vi = 0 at hval
    exact hval
  obtain ⟨c, hc⟩ :=
    exists_smul_eq_of_finrank_eq_one hsimple hviNe vj0
  have hcoe := congrArg Subtype.val hc
  change c • vi = vj at hcoe
  have hcross : vj ⬝ᵥ vi = 0 := by
    have hinner :=
      (orderedHermitianEigenbasis hA).inner_eq_zero hij
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
    simpa only [vi, vj, star_trivial] using hinner
  have hself : vj ⬝ᵥ vj = 1 := by
    have hinner := (orderedHermitianEigenbasis hA).inner_eq_one j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
    simpa only [vj, star_trivial] using hinner
  have hdot := congrArg (fun v : Fin n → Real => vj ⬝ᵥ v) hcoe
  simp only [dotProduct_smul, smul_eq_mul, hcross, mul_zero, hself] at hdot
  norm_num at hdot

namespace OddCentralChordData

/-! ## The unique zero at the odd centre -/

/-- The zero-based central spectral index of a path of order `2m+1`. -/
def lowerCentralZeroIndex (d : OddCentralChordData) : Fin (2 * d.m + 1) :=
  ⟨d.m, by omega⟩

/-- The central Dirichlet angle is exactly `pi/2`. -/
theorem pathEigenangle_lowerCentralZeroIndex
    (d : OddCentralChordData) :
    pathEigenangle (2 * d.m + 1) d.lowerCentralZeroIndex =
      Real.pi / 2 := by
  unfold pathEigenangle lowerCentralZeroIndex
  have hden : 2 * (d.m : Real) + 2 ≠ 0 := by positivity
  push_cast
  field_simp [hden]
  ring

/-- Hence the displayed central spectral node is exactly zero. -/
@[simp] theorem symmetricPathEigenvalue_lowerCentralZeroIndex
    (d : OddCentralChordData) (r : Real) :
    symmetricPathEigenvalue (2 * d.m + 1) r
        d.lowerCentralZeroIndex = 0 := by
  unfold symmetricPathEigenvalue
  rw [pathEigenangle_lowerCentralZeroIndex,
    Real.cos_pi_div_two, mul_zero]

/-- The zero eigenspace of the centre signed-middle matrix has dimension
one.  This is the endpoint-simplicity theorem at the exact central node. -/
theorem lowerCentral_centerZeroEigenspace_finrank
    (d : OddCentralChordData) :
    Module.finrank Real
      (Module.End.eigenspace
        (signedMiddleMatrix (2 * d.m + 1) d.a 0).toLin' 0) = 1 := by
  have hsqrt : 0 < Real.sqrt d.a := Real.sqrt_pos.2 d.ha0
  have hsimple :=
    signedMiddleMatrix_zero_eigenspace_finrank_at_spectral_node
      (2 * d.m + 1) hsqrt d.lowerCentralZeroIndex
  rw [Real.sq_sqrt d.ha0.le,
    symmetricPathEigenvalue_lowerCentralZeroIndex] at hsimple
  exact hsimple

/-- In decreasing ordered-eigenvalue coordinates, the centre zero occurs
at a unique index. -/
theorem lowerCentral_centerZero_unique
    (d : OddCentralChordData) :
    let hB0 :
        (signedMiddleMatrix (2 * d.m + 1) d.a 0).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * d.m + 1) d.a 0)
    ∀ i j : Fin (2 * d.m + 1),
      orderedHermitianEigenvalue hB0 i = 0 →
      orderedHermitianEigenvalue hB0 j = 0 → i = j := by
  dsimp only
  let hB0 : (signedMiddleMatrix (2 * d.m + 1) d.a 0).IsHermitian :=
    Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm (2 * d.m + 1) d.a 0)
  exact
    orderedHermitianEigenvalue_zero_unique_of_eigenspace_finrank_eq_one
      hB0 (lowerCentral_centerZeroEigenspace_finrank d)

/-! ## Weyl isolation of the central branch -/

/-- Every nonzero centre eigenvalue is at least the explicit second
singular value in absolute value. -/
theorem lowerCentral_centerNonzeroEigenvalue_ge_secondSingularValue
    (d : OddCentralChordData) :
    let hB0 :
        (signedMiddleMatrix (2 * d.m + 1) d.a 0).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * d.m + 1) d.a 0)
    ∀ i : Fin (2 * d.m + 1),
      orderedHermitianEigenvalue hB0 i ≠ 0 →
        oddCentralSecondSingularValue d.m d.a ≤
          |orderedHermitianEigenvalue hB0 i| := by
  dsimp only
  intro i hi
  have hbound :=
    oddCentralSecondSingularValue_le_abs_orderedEigenvalue
      d.m d.hm d.ha0 d.ha1 i
  dsimp only at hbound
  exact hbound hi

/-- The strict test-radius inequality in the exact form consumed by the
Weyl isolation theorem. -/
theorem lowerCentralXStar_add_C_lt_secondSingularValue
    (d : OddCentralChordData) :
    d.lowerCentralXStar + d.lowerCentralC <
      oddCentralSecondSingularValue d.m d.a :=
  (lowerCentralXStar_add_C_lt_mesh_le_secondSingularValue d).1.trans_le
    (lowerCentralXStar_add_C_lt_mesh_le_secondSingularValue d).2

/-- Weyl perturbation and centre simplicity imply that at most one
ordered eigenvalue at `x_*` can lie in `(-c,c)`. -/
theorem lowerCentral_atMostOne_small_orderedEigenvalue
    (d : OddCentralChordData) :
    let hBx :
        (signedMiddleMatrix (2 * d.m + 1) d.a
          d.lowerCentralXStar).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * d.m + 1) d.a
          d.lowerCentralXStar)
    ∀ i j : Fin (2 * d.m + 1),
      |orderedHermitianEigenvalue hBx i| < d.lowerCentralC →
      |orderedHermitianEigenvalue hBx j| < d.lowerCentralC → i = j := by
  dsimp only
  let hBx :
      (signedMiddleMatrix (2 * d.m + 1) d.a
        d.lowerCentralXStar).IsHermitian :=
    Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm (2 * d.m + 1) d.a
        d.lowerCentralXStar)
  let hB0 :
      (signedMiddleMatrix (2 * d.m + 1) d.a 0).IsHermitian :=
    Matrix.IsSymm.isHermitianReal
      (signedMiddleMatrix_isSymm (2 * d.m + 1) d.a 0)
  have hperturb (i : Fin (2 * d.m + 1)) :
      |orderedHermitianEigenvalue hBx i -
          orderedHermitianEigenvalue hB0 i| ≤ d.lowerCentralXStar := by
    exact abs_orderedSignedMiddleEigenvalue_sub_zero_le
      (2 * d.m + 1) d.a (lowerCentralXStar_pos d).le i
  have hcenterGap (i : Fin (2 * d.m + 1)) :
      orderedHermitianEigenvalue hB0 i ≠ 0 →
        oddCentralSecondSingularValue d.m d.a ≤
          |orderedHermitianEigenvalue hB0 i| := by
    intro hi
    have hbound :=
      oddCentralSecondSingularValue_le_abs_orderedEigenvalue
        d.m d.hm d.ha0 d.ha1 i
    dsimp only at hbound
    exact hbound hi
  have hcenterZeroUnique (i j : Fin (2 * d.m + 1)) :
      orderedHermitianEigenvalue hB0 i = 0 →
      orderedHermitianEigenvalue hB0 j = 0 → i = j :=
    orderedHermitianEigenvalue_zero_unique_of_eigenspace_finrank_eq_one
      hB0 (lowerCentral_centerZeroEigenspace_finrank d) i j
  exact atMostOne_small_perturbed_value
    (orderedHermitianEigenvalue hB0) (orderedHermitianEigenvalue hBx)
    hperturb hcenterGap hcenterZeroUnique
    (lowerCentralXStar_add_C_lt_secondSingularValue d)

/-! ## Product parity and the actual least singular value -/

/-- The source's positive determinant product, restated at the parameters
used by the parity theorem. -/
theorem lowerCentral_signedPencil_product_pos
    (d : OddCentralChordData) :
    0 <
      signedPencilDet (2 * d.m + 1) d.a d.lowerCentralXStar
          d.lowerCentralC *
        signedPencilDet (2 * d.m + 1) d.a d.lowerCentralXStar
          (-d.lowerCentralC) :=
  signedPencilDet_lowerCentral_product_pos d

/-- Positive product parity excludes the sole eigenvalue still allowed by
Weyl: every absolute signed-middle eigenvalue is strictly above `c`. -/
theorem lowerCentralC_lt_abs_orderedEigenvalue
    (d : OddCentralChordData) :
    let hBx :
        (signedMiddleMatrix (2 * d.m + 1) d.a
          d.lowerCentralXStar).IsHermitian :=
      Matrix.IsSymm.isHermitianReal
        (signedMiddleMatrix_isSymm (2 * d.m + 1) d.a
          d.lowerCentralXStar)
    ∀ i : Fin (2 * d.m + 1),
      d.lowerCentralC < |orderedHermitianEigenvalue hBx i| := by
  dsimp only
  exact all_abs_orderedSignedMiddleEigenvalue_gt_of_product_pos
    (2 * d.m + 1) d.a d.lowerCentralXStar
    (lowerCentralC_pos d).le
    (lowerCentral_signedPencil_product_pos d)
    (lowerCentral_atMostOne_small_orderedEigenvalue d)

/-- At the actual positive central-gap test point, the ordinary Euclidean
least singular value is strictly greater than the lower bidiagonal height. -/
theorem lowerCentralC_lt_realGapValue_XStar
    (d : OddCentralChordData) :
    d.lowerCentralC <
      realGapValue (2 * d.m + 1) d.a d.lowerCentralXStar := by
  apply realGapValue_gt_of_all_abs_orderedSignedMiddleEigenvalue
    (2 * d.m + 1) (by omega) d.a d.lowerCentralXStar d.lowerCentralC
  exact lowerCentralC_lt_abs_orderedEigenvalue d

/-! ## The literal strict lower central-height comparison -/

/-- The test point belongs to the closed interval used to define the
attained odd central height. -/
theorem lowerCentralXStar_mem_oddCentralInterval
    (d : OddCentralChordData) :
    d.lowerCentralXStar ∈ oddCentralInterval d.m d.a := by
  have hx := lowerCentralXStar_mem_oddCentralPositiveGap d
  unfold oddCentralInterval
  exact ⟨hx.1.le, hx.2.le⟩

/-- Literal lower half of `eq:central-interlace`:
`c_{m+1}<d_m`, with both quantities carrying their actual definitions. -/
theorem centralBidiagonalHeight_succ_lt_oddCentralHeight
    (d : OddCentralChordData) :
    centralBidiagonalHeight (d.m + 1) d.a <
      oddCentralHeight d.m d.a := by
  calc
    centralBidiagonalHeight (d.m + 1) d.a = d.lowerCentralC := rfl
    _ < realGapValue (2 * d.m + 1) d.a d.lowerCentralXStar :=
      lowerCentralC_lt_realGapValue_XStar d
    _ ≤ oddCentralHeight d.m d.a :=
      realGapValue_le_oddCentralHeight d.m d.a d.lowerCentralXStar
        (lowerCentralXStar_mem_oddCentralInterval d)

end OddCentralChordData

end

end ConnectedPseudospectrum
