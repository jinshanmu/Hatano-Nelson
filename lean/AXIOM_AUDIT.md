# Kernel-axiom audit

Run from `lean/` in the pinned environment:

```sh
lake env lean AxiomAudit.lean
```

`AxiomAudit.lean` contains 284 selected `#print axioms` commands.  The
selection includes the final `ConnectedPseudospectrum.main_theorem` and the
principal endpoints for:

- spectrum and least-singular-value infrastructure;
- the attained pointwise spectral backward-error minimum;
- the abstract vertical-topology theorem and its attained real-axis barrier;
- the complex unitary--affine tridiagonal Toeplitz reduction and boundary
  classifications;
- the connected rotation-invariant radial classification, the exact
  one-sided Jordan disks, and their contractibility;
- the normal union-of-disks formula, largest-half-gap threshold, strict
  connectedness criterion, and equal-modulus complex transfer;
- the explicit normal cubic remainder and bounded-error critical-dimension
  inversion;
- component topology and the connectedness criterion;
- vertical monotonicity;
- folded continuants, collision formulas, and chord exhaustion;
- noncentral and central gap comparisons;
- strict barrier decrease and quantitative bounds;
- elementary threshold inversion, the exact connected tail, and the
  critical-size asymptotic; and
- the exact two-dimensional endpoint.

The exact command list in `AxiomAudit.lean` is authoritative.  This is a
selected closure audit, not a claim that every public declaration is printed
separately; the output for `main_theorem` covers its complete proof dependency
closure.

## Acceptance criterion

Each printed declaration may depend only on:

- `propext`;
- `Classical.choice`; and
- `Quot.sound`.

Any project-specific axiom or compiler-trust escape is a failure.  The five
finite paired-permutation facts use ordinary kernel `decide`, not
`native_decide`, and are printed explicitly.

The latest command result and observed dependency set are recorded in
`STATUS.md`.
