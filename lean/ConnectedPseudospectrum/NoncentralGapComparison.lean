import ConnectedPseudospectrum.ChordFamilyExhaustion
import ConnectedPseudospectrum.NoncentralEllipticComparison

/-!
# Assembly of the noncentral chord comparison

This module assembles the hyperbolic and elliptic comparisons for an
arbitrary point of a positive noncentral successor gap.  It implements the
common part of lines 1235--1367 and the preparatory chord-level part of lines
1925--1938 of the immutable source: the successor point is put in canonical chord
coordinates, its inner angle is unscaled to the predecessor nodal interval,
and the endpoint-side outer coordinate is split into its hyperbolic and
elliptic charts.

The angular exhaustion theorem from lines 1218--1225 then turns the
constructed predecessor chord into an actual point of the predecessor
spectral gap, where its chord height is the finite-dimensional Euclidean
least singular value.

The index convention is explicit in the final statement.  If `d.K = N`,
then `d` describes gap `j = d.j` of the predecessor matrix of order `N-1`,
whereas `d.successor` describes the same positive gap index `j` of the
successor matrix of order `N = (N+1)-1`.  Reflection of a gap of a matrix of
order `n` sends the descending-eigenvalue gap index `j` to `n-j`; hence the
corresponding negative indices are `(N-1)-j` for the predecessor and `N-j`
for the successor.  The actual-height reflection identity is proved
separately in `RealGapReflection`.
-/

namespace ConnectedPseudospectrum

open Set

noncomputable section

namespace PositiveHalfGap

/-- Scaling the predecessor left nodal endpoint gives the successor left
nodal endpoint. -/
theorem noncentralScale_mul_angleLower (d : PositiveHalfGap) :
    noncentralScale d.K * d.angleLower = d.successor.angleLower := by
  have hKne : (d.K : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_two.trans_le d.hK))
  dsimp only [noncentralScale, angleLower, successor]
  field_simp [hKne]

/-- Scaling the predecessor right nodal endpoint gives the successor right
nodal endpoint. -/
theorem noncentralScale_mul_angleUpper (d : PositiveHalfGap) :
    noncentralScale d.K * d.angleUpper = d.successor.angleUpper := by
  have hKne : (d.K : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_two.trans_le d.hK))
  dsimp only [noncentralScale, angleUpper, successor]
  field_simp [hKne]

/-- The inverse of `scaleToSuccessor`, packaged in the predecessor's closed
nodal interval. -/
def unscaleFromSuccessor
    (d : PositiveHalfGap) (theta : d.successor.Angle) : d.Angle := by
  have hK1 : 1 <= d.K := (by norm_num : 1 <= 2).trans d.hK
  have hkappa : 0 < noncentralScale d.K := noncentralScale_pos hK1
  refine ⟨(theta : Real) / noncentralScale d.K, ?_, ?_⟩
  · rw [le_div_iff₀ hkappa]
    calc
      d.angleLower * noncentralScale d.K =
          noncentralScale d.K * d.angleLower := mul_comm _ _
      _ = d.successor.angleLower := d.noncentralScale_mul_angleLower
      _ <= (theta : Real) := theta.2.1
  · rw [div_le_iff₀ hkappa]
    calc
      (theta : Real) <= d.successor.angleUpper := theta.2.2
      _ = noncentralScale d.K * d.angleUpper :=
        d.noncentralScale_mul_angleUpper.symm
      _ = d.angleUpper * noncentralScale d.K := mul_comm _ _

@[simp] theorem coe_unscaleFromSuccessor
    (d : PositiveHalfGap) (theta : d.successor.Angle) :
    (d.unscaleFromSuccessor theta : Real) =
      (theta : Real) / noncentralScale d.K := by
  rfl

/-- Unscaling and then applying the source rescaling recovers the successor
angle exactly. -/
theorem scaleToSuccessor_unscaleFromSuccessor
    (d : PositiveHalfGap) (theta : d.successor.Angle) :
    d.scaleToSuccessor (d.unscaleFromSuccessor theta) = theta := by
  have hK1 : 1 <= d.K := (by norm_num : 1 <= 2).trans d.hK
  have hkappa : 0 < noncentralScale d.K := noncentralScale_pos hK1
  apply Subtype.ext
  change noncentralScale d.K *
      ((theta : Real) / noncentralScale d.K) = (theta : Real)
  rw [mul_comm, div_mul_cancel₀ _ hkappa.ne']

/-- An interior successor angle unscales to an interior predecessor angle. -/
theorem unscaleFromSuccessor_interior
    (d : PositiveHalfGap) (theta : d.successor.Angle)
    (hleft : d.successor.angleLower < theta)
    (hright : (theta : Real) < d.successor.angleUpper) :
    d.angleLower < d.unscaleFromSuccessor theta /\
      (d.unscaleFromSuccessor theta : Real) < d.angleUpper := by
  have hK1 : 1 <= d.K := (by norm_num : 1 <= 2).trans d.hK
  have hkappa : 0 < noncentralScale d.K := noncentralScale_pos hK1
  constructor
  · rw [coe_unscaleFromSuccessor, lt_div_iff₀ hkappa]
    calc
      d.angleLower * noncentralScale d.K =
          noncentralScale d.K * d.angleLower := mul_comm _ _
      _ = d.successor.angleLower := d.noncentralScale_mul_angleLower
      _ < (theta : Real) := hleft
  · rw [coe_unscaleFromSuccessor, div_lt_iff₀ hkappa]
    calc
      (theta : Real) < d.successor.angleUpper := hright
      _ = noncentralScale d.K * d.angleUpper :=
        d.noncentralScale_mul_angleUpper.symm
      _ = d.angleUpper * noncentralScale d.K := mul_comm _ _

end PositiveHalfGap

/-- Equality of a selected signed middle root with a canonical signed chord
root identifies their positive heights. -/
theorem selectedMiddleHeight_eq_outerChordFamilyS_of_root_eq
    (d : PositiveHalfGap) (x : Real) (theta : d.Angle)
    (hroot : selectedMiddleRoot d x =
      outerChordFamilySignedRoot d theta) :
    selectedMiddleHeight d x = outerChordFamilyS d theta := by
  apply mul_left_cancel₀
    (pow_ne_zero d.j (by norm_num : (-1 : Real) ≠ 0))
  calc
    (-1 : Real) ^ d.j * selectedMiddleHeight d x =
        selectedMiddleRoot d x :=
      (selectedMiddleRoot_eq_negOnePow_mul_height d x).symm
    _ = outerChordFamilySignedRoot d theta := hroot
    _ = (-1 : Real) ^ d.j * outerChordFamilyS d theta := rfl

/-- Every point of the successor positive noncentral spectral gap has an
interior canonical chord representation, and its actual least singular
value is the canonical chord height. -/
theorem exists_successorOuterChordFamily_representation
    (d : PositiveHalfGap) {x : Real}
    (hx : x ∈ positiveHalfSpectralGap d.successor) :
    ∃ theta : d.successor.Angle,
      d.successor.angleLower < theta /\
      (theta : Real) < d.successor.angleUpper /\
      x = outerChordFamilyX d.successor theta /\
      realGapValue d.K d.a x = outerChordFamilyS d.successor theta := by
  have hclassified : x ∈ middleBranchRawClassifiedSet d.successor :=
    positiveHalfSpectralGap_subset_middleBranchRawClassifiedSet d.successor hx
  obtain ⟨theta, hleft, hright, -, -, hxFamily, hroot⟩ :=
    exists_outerChordFamily_representation_of_classified d.successor
      ⟨hx, hclassified⟩
  have hheight :=
    selectedMiddleHeight_eq_outerChordFamilyS_of_root_eq
      d.successor x theta hroot
  refine ⟨theta, hleft, hright, hxFamily, ?_⟩
  simpa only [selectedMiddleHeight, PositiveHalfGap.successor_K,
    PositiveHalfGap.successor_a, Nat.add_sub_cancel] using hheight

/-- An interior successor chord has exactly one of the two endpoint-side
outer-coordinate descriptions needed by the source comparison.  The point
`z = 1` is assigned to the hyperbolic chart (`eta = 0`). -/
theorem successorOuterCoordinate_cases
    (d : PositiveHalfGap) (theta : d.successor.Angle)
    (hleft : d.successor.angleLower < theta)
    (hright : (theta : Real) < d.successor.angleUpper) :
    (∃ eta : Real,
      eta ∈ Ico (0 : Real) (pathLogParameter d.a) /\
      outerChordFamilyZ d.successor theta = Real.cosh eta) \/
    (∃ phi : Real,
      phi ∈ Ioo (0 : Real) (Real.pi / d.successor.K) /\
      outerChordFamilyZ d.successor theta = Real.cos phi) := by
  let z := outerChordFamilyZ d.successor theta
  have hzlt : z < Real.cosh (pathLogParameter d.a) := by
    simpa only [z, PositiveHalfGap.successor_a] using
      outerChordFamilyZ_lt_cosh d.successor theta hleft hright
  by_cases hone : (1 : Real) <= z
  · have hzrange : z ∈ Icc (1 : Real)
        (Real.cosh (pathLogParameter d.a)) := by
      refine ⟨hone, ?_⟩
      simpa only [z, PositiveHalfGap.successor_a] using
        (outerChordFamilyZ_mem d.successor theta).2
    obtain ⟨eta, heta, -⟩ :=
      existsUnique_hyperbolicOuterCoordinate d.a z d.ha0 d.ha1 hzrange
    have hetane : eta ≠ pathLogParameter d.a := by
      intro heq
      have hzend : z = Real.cosh (pathLogParameter d.a) := by
        simpa only [heq] using heta.2
      exact (ne_of_lt hzlt) hzend
    have hetalt : eta < pathLogParameter d.a :=
      lt_of_le_of_ne heta.1.2 hetane
    exact Or.inl ⟨eta, ⟨heta.1.1, hetalt⟩, heta.2⟩
  · have hzOne : z < 1 := lt_of_not_ge hone
    have hzLower : Real.cos (Real.pi / d.successor.K) < z :=
      (outerLobeMaximizer_spec d.successor).1.1.trans
        (outerLobeMaximizer_lt_outerChordFamilyZ
          d.successor theta hleft hright)
    obtain ⟨phi, hphi, -⟩ :=
      existsUnique_ellipticOuterCoordinate d.successor.K
        d.successor.hK z ⟨hzLower, hzOne.le⟩
    have hphine : phi ≠ 0 := by
      intro heq
      have hzone : z = 1 := by
        simpa only [heq, Real.cos_zero] using hphi.2
      exact (ne_of_lt hzOne) hzone
    have hphipos : 0 < phi :=
      lt_of_le_of_ne hphi.1.1 (Ne.symm hphine)
    exact Or.inr ⟨phi, ⟨hphipos, hphi.1.2⟩, hphi.2⟩

/-- Chord-level noncentral gap comparison.  From any point in the successor
positive gap, the source construction produces an interior predecessor chord
with strictly larger chord height than the point's actual least singular
value. -/
theorem exists_predecessorChord_strict_of_mem_successorGap
    (d : PositiveHalfGap) {x : Real}
    (hx : x ∈ positiveHalfSpectralGap d.successor) :
    ∃ thetahat : d.Angle,
      d.angleLower < thetahat /\
      (thetahat : Real) < d.angleUpper /\
      realGapValue d.K d.a x < outerChordFamilyS d thetahat := by
  obtain ⟨thetaM, hMleft, hMright, -, hheight⟩ :=
    exists_successorOuterChordFamily_representation d hx
  let theta0 : d.Angle := d.unscaleFromSuccessor thetaM
  have htheta0 : d.angleLower < theta0 /\
      (theta0 : Real) < d.angleUpper :=
    d.unscaleFromSuccessor_interior thetaM hMleft hMright
  have hscale : d.scaleToSuccessor theta0 = thetaM := by
    exact d.scaleToSuccessor_unscaleFromSuccessor thetaM
  rcases successorOuterCoordinate_cases d thetaM hMleft hMright with
      ⟨eta, heta, hz⟩ | ⟨phi, hphi, hz⟩
  · have hM : outerChordFamilyZ d.successor
        (d.scaleToSuccessor theta0) = Real.cosh eta := by
      rw [hscale]
      exact hz
    obtain ⟨thetahat, hhat, -⟩ :=
      existsUnique_noncentralHyperbolicComparison d theta0
        htheta0.1 htheta0.2 heta hM
    refine ⟨thetahat, htheta0.1.trans hhat.1.1, hhat.1.2.1, ?_⟩
    calc
      realGapValue d.K d.a x =
          outerChordFamilyS d.successor thetaM := hheight
      _ = outerChordFamilyS d.successor
          (d.scaleToSuccessor theta0) := by rw [hscale]
      _ < outerChordFamilyS d thetahat := hhat.2.2
  · have hM : outerChordFamilyZ d.successor
        (d.scaleToSuccessor theta0) = Real.cos phi := by
      rw [hscale]
      exact hz
    obtain ⟨thetahat, hhat, -⟩ :=
      existsUnique_noncentralEllipticComparison d theta0
        htheta0.1 htheta0.2 hphi hM
    refine ⟨thetahat, htheta0.1.trans hhat.1.1, hhat.1.2.1, ?_⟩
    calc
      realGapValue d.K d.a x =
          outerChordFamilyS d.successor thetaM := hheight
      _ = outerChordFamilyS d.successor
          (d.scaleToSuccessor theta0) := by rw [hscale]
      _ < outerChordFamilyS d thetahat := hhat.2.2

/-- Actual noncentral positive-gap comparison.  Every point of the successor
gap has a point in the same-index predecessor gap whose genuine Euclidean
least singular value is strictly larger. -/
theorem exists_predecessorGapPoint_strict_of_mem_successorGap
    (d : PositiveHalfGap) {x : Real}
    (hx : x ∈ positiveHalfSpectralGap d.successor) :
    ∃ xhat : Real,
      xhat ∈ positiveHalfSpectralGap d /\
      realGapValue d.K d.a x < realGapValue (d.K - 1) d.a xhat := by
  obtain ⟨thetahat, hleft, hright, hstrict⟩ :=
    exists_predecessorChord_strict_of_mem_successorGap d hx
  refine ⟨outerChordFamilyX d thetahat,
    outerChordFamilyX_mem_positiveHalfSpectralGap
      d thetahat hleft hright, ?_⟩
  rw [realGapValue_outerChordFamilyX_eq_outerChordFamilyS
    d thetahat hleft hright]
  exact hstrict

end

end ConnectedPseudospectrum
