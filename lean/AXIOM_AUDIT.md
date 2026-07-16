# Kernel-axiom audit

## Command

Run the audit from `lean/` in the pinned environment with default Lean options:

```sh
lake env lean AxiomAudit.lean
```

No `-D` flags, environment-provided Lean options, or project option overrides
are part of this command.

## Scope

`AxiomAudit.lean` imports the final theorem and selected supporting modules and
contains 230 `#print axioms` commands: 216 whose declaration name is on the
command line and 14 whose name continues on the next line.  This is a selected
endpoint/closure audit, not a claim that every public declaration is printed
individually.

The selection includes:

- the final `ConnectedPseudospectrum.main_theorem`, whose reported axioms cover
  its complete proof dependency closure;
- the literal spectrum/resolvent/least-singular-value equality and attained
  Euclidean least-singular-value infrastructure;
- vertical monotonicity, the connectedness criterion, and component
  contractibility;
- the exact exported quotient inequalities corresponding to `eq:ratio-cross`;
- the folded determinant, signed branch, chord continuation, central and
  noncentral comparisons, and strict barrier decrease;
- barrier bounds, threshold equality, the fixed-parameter asymptotic, and the
  exact size-two characterization;
- the generic and actual-root collision formulas for the folded divided
  differences;
- the complete bordered odd-dilation endpoints and the all-angle normalized
  principal-sine formula; and
- the local lower-Lambert-branch specification and uniqueness, exact explicit
  floor threshold, and logarithmic--logarithmic bounded-error expansion.

The exact declaration list lives in `AxiomAudit.lean`, so the executable audit
is the authoritative scope record.

## Acceptance criterion

Each printed declaration may depend only on:

- `propext`;
- `Classical.choice`; and
- `Quot.sound`.

These are standard foundational Lean/Mathlib principles, not project-specific
mathematical assumptions.  Any project axiom, `Lean.ofReduce*`,
`Lean.trustCompiler`, or another compiler-trust escape is a failure.

Five finite paired-permutation facts use ordinary kernel `decide`, not
`native_decide`.  They are printed explicitly so that a future non-kernel
dependency would be visible.

The final execution result, diagnostics, unique-record count, and observed
dependency set for the current 2026-07-16 source state are recorded in
`STATUS.md`.  The exact command above exited successfully for all 230 distinct
targets, with only the three accepted foundational dependencies observed.
