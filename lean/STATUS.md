# Current validation status

Last updated: 2026-09-19 (Asia/Shanghai).

## Acceptance result

The complete formalization, including the simplified preprint proofs, passed
the umbrella build:

```sh
LEAN_NUM_THREADS=2 lake build
```

- Exit status: `0`.
- Final line: `Build completed successfully (8141 jobs).`
- Errors and warnings: none.

The whole namespace also passed the Mathlib unused-argument linter.  The
temporary diagnostic driver was:

```lean
import ConnectedPseudospectrum

#lint only unusedArguments in ConnectedPseudospectrum
```

It found zero errors in 2,478 declarations, plus 2,287 automatically
generated declarations, and ended with `All linting checks passed!`.  The
temporary driver was deleted after the check.

The kernel-axiom audit was run with:

```sh
LEAN_NUM_THREADS=1 lake env lean AxiomAudit.lean
```

It exited `0` for all 293 selected `#print axioms` commands. All reported
dependencies are among `propext`, `Classical.choice`, and `Quot.sound`; no
record contained a project axiom, `sorryAx`, or compiler-trust escape.

## Mathematical scope

`ConnectedPseudospectrum.main_theorem` checks the complete dependency chain
for the canonical nonnormal theorem: component contractibility, the exact
connectedness criterion, strict adjacent-size barrier decrease, the exact
tail of connected dimensions, quantitative bounds, the fixed-parameter
critical-size asymptotic, and the exact size-two endpoint.  Its assumptions
`0 < a`, `a < 1`, and `0 < epsilon` are all used.

`ConnectedPseudospectrum.complexToeplitz_main_theorem` is the full-family
assembly corresponding to `thm:main`.  It uses the piecewise physical
threshold and critical-size wrappers to cover reducible, irreducible
nonnormal, and normal matrices in one theorem, including decay, persistence,
the literal first connected order, and both critical-order asymptotics.  Its
sole explicit hypothesis `0 < epsilon` is used, and all four parameters
`alpha`, `d`, `beta`, and `epsilon` occur in the conclusion.

`AbstractPseudospectralTopology.lean` packages the matrix-independent
vertical-scaling theorem with an attained real-interval barrier.  Under the
stated real-spectrum and endpoint hypotheses it proves component
contractibility and both the real-axis and strict-barrier connectedness
criteria.

`ComplexToeplitz.lean` defines the general complex family
`tridiag(alpha,d,beta)`, proves exact unitary--affine reduction whenever the
overall scale is nonzero (including a one-sided off-diagonal), transfers the
unequal-modulus connectedness and strict
dimension conclusions, reduces equal nonzero moduli to the Hermitian
endpoint, and treats the zero-product boundary by triangular determinant and
connectedness theorems.  The double-zero scalar case is identified exactly
with an open disk.

`BoundaryCases.lean` verifies the displayed normal scalar threshold's parity
formula, strict decrease in every adjacent dimension `n >= 2`, and the
explicit cubic error bound.  `JordanBoundary.lean` packages the exact
one-sided open disks and their contractibility.  `NormalBoundary.lean`,
`NormalGapGeometry.lean`, and `NormalToeplitzBoundary.lean` package the exact
normal union of disks, largest-half-gap threshold, component contractibility,
strict connectedness criterion, and its equal-modulus complex affine
transfer.  `NormalCriticalThreshold.lean` proves the first-hit specification
and the stronger uniform bound `|N-pi*c/epsilon|<2`, hence the normal
`pi*c/epsilon+O(1)` law.

## Lean environment and source integrity

- Lean: `leanprover/lean4:v4.28.0`.
- Lake: 5.0.0.
- Mathlib commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- The umbrella module imports all 114 source modules under
  `ConnectedPseudospectrum/`; there are no detached proof modules.
- Canonical library closure: 115 files, 43,778 lines, 1,809,940 bytes.
- `AxiomAudit.lean` SHA-256:
  `917a8a4848fdb25c7cecd6b6c02c7cdb4b713de75ad042354c332a2cb4529632`.

Static scans of the canonical library found no `sorry`, `admit`,
`native_decide`, project axiom, unsafe declaration, compiler-trust escape,
linter suppression, or Lean option override.  `CheckComplex.lean` and the
temporary lint driver are absent.

## Preprint manuscript alignment

- Current source: `../preprint/connectedness_thresholds.tex`.
- `FORMALIZATION_MAP.md` records the simplified proof routes and their
  corresponding Lean modules.
- The canonical and full-family assembly theorem statements are unchanged.
  Redundant helper premises were removed along their call chains.

## ELA manuscript alignment

- Current source: `../ELA/ela_pseudospectral_topology.tex`.
- `FORMALIZATION_MAP.md` uses the current ELA labels, including
  `thm:canonical-main`, `prop:boundary-cases`,
  `eq:normal-error-bound`, and `eq:general-normal-critical`.
- `LATEX_AUDIT.md` records the statement-level correspondence and proof-scope
  simplifications.

This file records executable Lean validation. LaTeX, bibliography, figures,
and submission-bundle checks are maintained alongside the corresponding
manuscripts.
