# Connected pseudospectrum formalization

This Lean project formalizes the canonical nonnormal theorem and the
complex-Toeplitz extension in `../ELA/ela_pseudospectral_topology.tex`:
component contractibility, the exact connectedness criterion, strict decrease
of the real-gap barrier, quantitative barrier bounds, the exact tail of
connected dimensions, the critical-size asymptotic, the exact two-dimensional
endpoint, the pointwise spectral backward-error minimum, and unitary--affine
reduction of complex tridiagonal Toeplitz matrices.

The public full-family assembly theorem is
`ConnectedPseudospectrum.complexToeplitz_main_theorem` in
`ConnectedPseudospectrum/FullFamilyMain.lean`.  The canonical nonnormal
assembly remains `ConnectedPseudospectrum.main_theorem` in
`ConnectedPseudospectrum/MainTheorem.lean`.

The simplified canonical proofs also correspond to
`../preprint/connectedness_thresholds.tex`. The preprint proof map in
`FORMALIZATION_MAP.md` records the direct five-minor generating functions,
the two-case central estimate, and the adjacent-order logarithmic inversion.

## Scope

The kernel-checked proof includes the complete dependency chain used by the
main theorem:

- explicit spectrum and least-singular-value infrastructure;
- vertical monotonicity and the real-axis topological reduction;
- the persymmetric signed pencil and middle-branch selection;
- folded Chebyshev identities and endpoint-side chord exhaustion;
- noncentral and parity-changing central gap comparisons;
- strict adjacent-size barrier decrease;
- the exact tail identity for connected dimensions;
- rectangular lower and upper bounds;
- elementary logarithmic inversion of `(n+1) r^n`; and
- the exact `n=2` threshold;
- attainment of the norm-minimizing spectral backward error; and
- the matrix-independent vertical-scaling criterion for real-axis
  connectedness and component contractibility;
- exact diagonal-unitary phase removal and complex affine pseudospectral
  transport whenever the overall scale is nonzero, including one-sided
  off-diagonals;
- the affine-image, component, connectedness, and strict scaled-barrier
  conclusions in the unequal-modulus regime;
- exact reduction of the equal-modulus regime to the Hermitian endpoint
  `a = 1`; and
- triangular determinant, singleton-spectrum, connectedness, and scalar-disk
  results on the zero-product boundary; and
- exact rotation invariance, open-disk classification, and contractibility
  for both one-sided Jordan orientations;
- the exact normal union-of-disks formula, largest-half-gap threshold,
  component contractibility, and complex equal-modulus affine transfer;
- the explicit normal cubic error bound and the uniform critical-size estimate
  `|N-pi*c/epsilon|<2`; and
- the general radial classification underlying the Jordan boundary; and
- a single piecewise full-family threshold and critical-size wrapper, with
  exact tail, first-order, decay, and all three critical-order laws.

The shared logarithmic inversion is proved in
`ConnectedPseudospectrum/Asymptotics.lean`. The critical-order proof in
`ConnectedPseudospectrum/CriticalThreshold.lean` applies it directly to the
first connected order and its predecessor. The tail-model results in
`ConnectedPseudospectrum/TailThresholdAsymptotic.lean` use the same estimate.  No Lambert `W`
function, exact Lambert floor formula, or extra small-parameter condition is
part of the current manuscript or formalization.

Bibliography, floating-point illustrations, and the physical interpretation
in the Discussion are non-theorem material and remain outside the kernel
scope.  The backward-error and complex-Toeplitz reduction results are
standalone kernel theorems because they are mathematically independent of
the canonical `main_theorem`; `complexToeplitz_main_theorem` is their
full-family top-level assembly.

`FORMALIZATION_MAP.md` records the proof-stage correspondence, including the
named endpoints for every theorem-bearing boundary statement used in the ELA
classification.

## Pinned environment

- Lean: `leanprover/lean4:v4.28.0`
- Lake: 5.0.0
- Mathlib commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`

## Build and audit

From this directory, run:

```sh
lake build
lake env lean AxiomAudit.lean
```

The umbrella module imports every source module under
`ConnectedPseudospectrum/`; there are no detached proof modules.  The axiom
audit contains 293 selected `#print axioms` commands, including both assembly
theorems.  The only accepted foundational dependencies are `propext`,
`Classical.choice`, and `Quot.sound`.

For a diagnostic unused-argument scan of the umbrella namespace, use a
temporary driver containing:

```lean
import ConnectedPseudospectrum

#lint only unusedArguments in ConnectedPseudospectrum
```

## Trust and source hygiene

The canonical library contains no `sorry`, `admit`, `native_decide`, project
axiom, unsafe declaration, compiler-trust escape, linter suppression, or
command-line option override.  `AxiomAudit.lean` is deliberately separate
from the default library target.

Current validation results are recorded in `STATUS.md`; statement-level
alignment notes are in `LATEX_AUDIT.md`.
