import ConnectedPseudospectrum.MiddleBranchBridge
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Local implicit signed-pencil branches at spectral nodes

At a displayed path eigenvalue, the signed-pencil polynomial has a simple
zero at `s = 0`.  This module turns that algebraic simplicity into the
nonvanishing partial derivative required by the implicit function theorem,
then constructs the unique local signed root as a function of `x`.
-/

namespace ConnectedPseudospectrum

open Filter Matrix

open scoped Topology

noncomputable section

/-- The literal signed-pencil determinant regarded as a function of the pair
`(x,s)`. -/
def signedPencilEquation (n : ℕ) (a : ℝ) : ℝ × ℝ → ℝ :=
  fun xs => signedPencilDet n a xs.1 xs.2

/-- The signed-pencil determinant is smooth jointly in `x` and `s`. -/
theorem contDiff_signedPencilEquation
    (n : ℕ) (a : ℝ) (m : WithTop ℕ∞) :
    ContDiff ℝ m (signedPencilEquation n a) := by
  unfold signedPencilEquation signedPencilDet signedPencil
  rw [show (fun xs : ℝ × ℝ =>
      (xs.1 • (1 : Matrix (Fin n) (Fin n) ℝ) - pathMatrix n a -
        xs.2 • reversal n).det) =
      fun xs : ℝ × ℝ =>
        ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
          ∏ i, (xs.1 • (1 : Matrix (Fin n) (Fin n) ℝ) - pathMatrix n a -
            xs.2 • reversal n) (σ i) i by
      funext xs
      exact Matrix.det_apply _]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

/-- Differentiating the determinant in `s` agrees with differentiating its
literal polynomial representative. -/
theorem hasDerivAt_signedPencilDet_in_s
    (n : ℕ) (a x s : ℝ) :
    HasDerivAt (fun t => signedPencilDet n a x t)
      ((signedPencilPolynomial n a x).derivative.eval s) s := by
  simpa only [signedPencilPolynomial_eval] using
    (signedPencilPolynomial n a x).hasDerivAt s

/-- The analytic partial derivative in `s` has the expected polynomial
value. -/
theorem deriv_signedPencilDet_in_s
    (n : ℕ) (a x s : ℝ) :
    deriv (fun t => signedPencilDet n a x t) s =
      (signedPencilPolynomial n a x).derivative.eval s :=
  (hasDerivAt_signedPencilDet_in_s n a x s).deriv

/-- A multiplicity-one endpoint root has nonzero polynomial derivative. -/
theorem signedPencilPolynomial_derivative_eval_zero_ne_at_spectral_node
    (n : ℕ) (hn : 0 < n) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    (signedPencilPolynomial n (r ^ 2)
      (symmetricPathEigenvalue n r k)).derivative.eval 0 ≠ 0 := by
  by_cases hnzero : n = 0
  · exact (Nat.ne_of_gt hn hnzero).elim
  · let p := signedPencilPolynomial n (r ^ 2)
      (symmetricPathEigenvalue n r k)
    have hm : p.rootMultiplicity 0 = 1 :=
      signedPencilPolynomial_rootMultiplicity_zero_at_spectral_node n hr k
    have hpne : p ≠ 0 := by
      intro hpzero
      rw [hpzero, Polynomial.rootMultiplicity_zero] at hm
      omega
    have hpRoot : p.IsRoot 0 := by
      change p.eval 0 = 0
      rw [signedPencilPolynomial_eval]
      exact signedPencilDet_symmetricPathEigenvalue_sq_zero n hr k
    intro hderiv
    have hderivRoot : p.derivative.IsRoot 0 := by
      exact hderiv
    have hmultiple : 1 < p.rootMultiplicity 0 :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot hpne).2
        ⟨hpRoot, hderivRoot⟩
    rw [hm] at hmultiple
    omega

/-- The partial derivative with respect to the signed height is nonzero at
every spectral endpoint.  This is the analytic hypothesis used by the
implicit function theorem. -/
theorem signedPencilDet_partial_s_ne_zero_at_spectral_node
    (n : ℕ) (hn : 0 < n) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    deriv
      (fun s => signedPencilDet n (r ^ 2)
        (symmetricPathEigenvalue n r k) s) 0 ≠ 0 := by
  rw [deriv_signedPencilDet_in_s]
  exact signedPencilPolynomial_derivative_eval_zero_ne_at_spectral_node
    n hn hr k

/-- The total Fréchet derivative used to package the endpoint implicit
function theorem. -/
def signedPencilEquationFDeriv
    (n : ℕ) (a x s : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  fderiv ℝ (signedPencilEquation n a) (x, s)

/-- The signed-pencil equation satisfies Mathlib's `C¹` implicit-function
hypotheses at every path spectral node. -/
theorem signedPencilEndpoint_isContDiffImplicitAt
    (n : ℕ) (hn : 0 < n) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    IsContDiffImplicitAt (𝕜 := ℝ) (1 : WithTop ℕ∞)
      (signedPencilEquation n (r ^ 2))
      (signedPencilEquationFDeriv n (r ^ 2)
        (symmetricPathEigenvalue n r k) 0)
      (symmetricPathEigenvalue n r k, 0) := by
  let x0 := symmetricPathEigenvalue n r k
  let f := signedPencilEquation n (r ^ 2)
  let f' := signedPencilEquationFDeriv n (r ^ 2) x0 0
  let p := signedPencilPolynomial n (r ^ 2) x0
  let d := p.derivative.eval 0
  have hf : ContDiff ℝ (1 : WithTop ℕ∞) f :=
    contDiff_signedPencilEquation n (r ^ 2) 1
  have hfderiv : HasFDerivAt f f' (x0, 0) := by
    exact hf.differentiable_one.differentiableAt.hasFDerivAt
  have hsCurve :
      HasFDerivAt (fun s : ℝ => (x0, s))
        (ContinuousLinearMap.inr ℝ ℝ ℝ) 0 :=
    hasFDerivAt_prodMk_right x0 0
  have hcomp : HasFDerivAt (fun s : ℝ => f (x0, s))
      (f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) 0 := by
    simpa only [Function.comp_apply] using hfderiv.comp 0 hsCurve
  have hpoly : HasFDerivAt (fun s : ℝ => f (x0, s))
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) d) 0 := by
    exact hasDerivAt_signedPencilDet_in_s n (r ^ 2) x0 0
  have hpartial :
      f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ) =
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) d :=
    hcomp.unique hpoly
  have hd : d ≠ 0 :=
    signedPencilPolynomial_derivative_eval_zero_ne_at_spectral_node
      n hn hr k
  have hbijective : Function.Bijective
      (f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) := by
    rw [hpartial]
    constructor
    · intro u v huv
      simp only [ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply, smul_eq_mul] at huv
      exact mul_right_cancel₀ hd huv
    · intro y
      refine ⟨y / d, ?_⟩
      simp only [ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.one_apply, smul_eq_mul]
      exact div_mul_cancel₀ y hd
  change IsContDiffImplicitAt (𝕜 := ℝ) (1 : WithTop ℕ∞) f f' (x0, 0)
  exact
    { hasFDerivAt := hfderiv
      contDiffAt := hf.contDiffAt
      bijective := hbijective
      ne_zero := by norm_num }

/-- The unique local signed-pencil root supplied by the implicit function
theorem at a spectral endpoint. -/
def signedPencilLocalRoot
    (n : ℕ) (hn : 0 < n) {r : ℝ} (hr : 0 < r) (k : Fin n) : ℝ → ℝ :=
  (signedPencilEndpoint_isContDiffImplicitAt n hn hr k).implicitFunction

/-- The local implicit root is `C¹` at its spectral endpoint. -/
theorem contDiffAt_signedPencilLocalRoot
    (n : ℕ) (hn : 0 < n) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    ContDiffAt ℝ (1 : WithTop ℕ∞)
      (signedPencilLocalRoot n hn hr k)
      (symmetricPathEigenvalue n r k) :=
  IsContDiffImplicitAt.contDiffAt_implicitFunction
    (signedPencilEndpoint_isContDiffImplicitAt n hn hr k)

/-- Near the endpoint, the local implicit root is an actual root of the
literal signed determinant. -/
theorem eventually_signedPencilDet_localRoot_eq_zero
    (n : ℕ) (hn : 0 < n) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    ∀ᶠ x in 𝓝 (symmetricPathEigenvalue n r k),
      signedPencilDet n (r ^ 2) x
        (signedPencilLocalRoot n hn hr k x) = 0 := by
  have h := IsContDiffImplicitAt.apply_implicitFunction
    (signedPencilEndpoint_isContDiffImplicitAt n hn hr k)
  simpa only [signedPencilEquation, signedPencilLocalRoot,
    signedPencilDet_symmetricPathEigenvalue_sq_zero n hr k] using h

/-- Practical local uniqueness: every nearby zero of the literal signed
pencil has height equal to the implicit root. -/
theorem eventually_signedPencilLocalRoot_eq_of_det_zero
    (n : ℕ) (hn : 0 < n) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    ∀ᶠ xs in 𝓝 (symmetricPathEigenvalue n r k, 0),
      signedPencilDet n (r ^ 2) xs.1 xs.2 = 0 →
        signedPencilLocalRoot n hn hr k xs.1 = xs.2 := by
  have h := IsContDiffImplicitAt.eventually_implicitFunction_apply_eq
    (signedPencilEndpoint_isContDiffImplicitAt n hn hr k)
  simpa only [signedPencilEquation, signedPencilLocalRoot,
    signedPencilDet_symmetricPathEigenvalue_sq_zero n hr k] using h

/-- The implicit branch passes through the endpoint height `s=0`. -/
theorem signedPencilLocalRoot_symmetricPathEigenvalue_eq_zero
    (n : ℕ) (hn : 0 < n) {r : ℝ} (hr : 0 < r) (k : Fin n) :
    signedPencilLocalRoot n hn hr k
      (symmetricPathEigenvalue n r k) = 0 := by
  have h := eventually_signedPencilLocalRoot_eq_of_det_zero n hn hr k
  exact h.self_of_nhds
    (signedPencilDet_symmetricPathEigenvalue_sq_zero n hr k)

/-- Any two continuous signed-pencil root curves through the same spectral
endpoint agree on some neighborhood of that endpoint. -/
theorem eventuallyEq_continuous_signedPencil_root_curves
    (n : ℕ) (hn : 0 < n) {r : ℝ} (hr : 0 < r) (k : Fin n)
    {g₁ g₂ : ℝ → ℝ}
    (hg₁ : ContinuousAt g₁ (symmetricPathEigenvalue n r k))
    (hg₂ : ContinuousAt g₂ (symmetricPathEigenvalue n r k))
    (hg₁0 : g₁ (symmetricPathEigenvalue n r k) = 0)
    (hg₂0 : g₂ (symmetricPathEigenvalue n r k) = 0)
    (hroot₁ : ∀ᶠ x in 𝓝 (symmetricPathEigenvalue n r k),
      signedPencilDet n (r ^ 2) x (g₁ x) = 0)
    (hroot₂ : ∀ᶠ x in 𝓝 (symmetricPathEigenvalue n r k),
      signedPencilDet n (r ^ 2) x (g₂ x) = 0) :
    g₁ =ᶠ[𝓝 (symmetricPathEigenvalue n r k)] g₂ := by
  let x0 := symmetricPathEigenvalue n r k
  have htendsto₁ : Tendsto (fun x => (x, g₁ x)) (𝓝 x0) (𝓝 (x0, 0)) := by
    have hcont : Tendsto (fun x => (x, g₁ x)) (𝓝 x0)
        (𝓝 (x0, g₁ x0)) := by
      simpa only [id_eq] using (continuousAt_id.prodMk hg₁)
    simpa only [x0, hg₁0] using hcont
  have htendsto₂ : Tendsto (fun x => (x, g₂ x)) (𝓝 x0) (𝓝 (x0, 0)) := by
    have hcont : Tendsto (fun x => (x, g₂ x)) (𝓝 x0)
        (𝓝 (x0, g₂ x0)) := by
      simpa only [id_eq] using (continuousAt_id.prodMk hg₂)
    simpa only [x0, hg₂0] using hcont
  have hunique := eventually_signedPencilLocalRoot_eq_of_det_zero n hn hr k
  have hunique₁ := htendsto₁.eventually hunique
  have hunique₂ := htendsto₂.eventually hunique
  filter_upwards [hroot₁, hroot₂, hunique₁, hunique₂] with x hx₁ hx₂ hu₁ hu₂
  exact (hu₁ hx₁).symm.trans (hu₂ hx₂)

end

end ConnectedPseudospectrum
