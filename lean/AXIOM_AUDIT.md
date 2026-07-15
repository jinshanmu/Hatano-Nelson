# Kernel-axiom audit

## Command

Run the audit in the pinned environment with default Lean options:

```sh
lake env lean AxiomAudit.lean
```

No `-D` flags or project option overrides are part of this command.

## Scope

`AxiomAudit.lean` imports the final theorem and selected supporting modules and
contains 211 `#print axioms` commands: 197 single-line commands and 14 whose
declaration names continue on the next line.  This is a selected endpoint
audit, not a claim that every public declaration is printed individually.

The selection includes:

- the final `ConnectedPseudospectrum.main_theorem`, whose reported axioms cover
  its complete proof dependency closure;
- the literal spectrum/resolvent/least-singular-value equality;
- the attained Euclidean least-singular-value infrastructure;
- vertical monotonicity, the connectedness criterion, and component
  contractibility;
- the folded determinant, signed branch, chord continuation, central and
  noncentral comparisons, and strict barrier decrease;
- barrier bounds, threshold equality, the fixed-parameter asymptotic, and the
  exact size-two characterization; and
- representative mapped endpoints not needed directly by the final assembly.

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
`native_decide`.  They are printed explicitly so a future non-kernel
dependency would be visible.

The latest execution result, including the observed dependency set and date,
is recorded in `STATUS.md`.
