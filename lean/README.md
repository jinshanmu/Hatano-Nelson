# Connected pseudospectrum formalization

This Lean project formalizes the main mathematical theorem in
`../LAA/laa_connected_pseudospectra.tex`: component contractibility, the exact
connectedness criterion, strict decrease of the real-gap barrier, quantitative
barrier bounds, the exact tail of connected dimensions, the critical-size
asymptotic, the exact two-dimensional endpoint, the pointwise spectral
backward-error minimum, and the positive-off-diagonal Toeplitz reduction.

The public assembly theorem is
`ConnectedPseudospectrum.main_theorem` in
`ConnectedPseudospectrum/MainTheorem.lean`.

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
- the affine-image, component, connectedness, scaled-barrier, and connected-
  dimension conclusions for positive unequal Toeplitz off-diagonals.

The logarithmic inversion is proved directly in
`ConnectedPseudospectrum/TailThresholdAsymptotic.lean`.  No Lambert `W`
function, exact Lambert floor formula, or extra small-parameter condition is
part of the current manuscript or formalization.

Bibliography, floating-point illustrations, and the physical interpretation
in the Discussion are non-theorem material and remain outside the kernel
scope.  The backward-error and general-Toeplitz results are standalone
kernel theorems because they are mathematically independent of
`main_theorem`.

`FORMALIZATION_MAP.md` records the proof-stage correspondence.

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
audit contains 238 selected `#print axioms` commands, including the final
theorem.  The only accepted foundational dependencies are `propext`,
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
