# Current validation status

Last updated: 2026-07-16 (Asia/Shanghai).

## Final acceptance result

The current 2026-07-16 source state has passed its final exact acceptance run.

The canonical command is:

```sh
lake build
```

- Exit status: `0`.
- Final line: `Build completed successfully (8130 jobs).`
- Elapsed wall time: approximately 8 minutes 29 seconds.
- Errors, warnings, and linter diagnostics: none.
- The command was run literally with no flags; no `LEAN*` or `LAKE*` option
  variables were set, and no Lean source changed during the run.

The separate default-options trust-audit command is:

```sh
lake env lean AxiomAudit.lean
```

`AxiomAudit.lean` contains 229 selected `#print axioms` commands: 215 whose
declaration name is on the command line and 14 whose name continues on the next
line.  All 229 targets are distinct.  The exact command exited `0`, printed one
record for every target, and produced no error, warning, or linter diagnostic.
The union of the observed dependency sets is exactly `propext`,
`Classical.choice`, and `Quot.sound`; no project axiom or compiler-trust escape
appeared.

## Locked manuscript and compiled artifact

- Audited source:
  `SIMAX_submission_bundle/final_connected_pseudospectrum_proof_2026-07-16.tex`
- Source size: 2,477 lines; 89,709 bytes.
- Source SHA-256:
  `84e0021272c9a9eb5cbfba3f6c82c4219bc2d64382232ebe68084bc9febe29b6`.
- Last full source/scope review: 2026-07-16.
- Compiled PDF:
  `SIMAX_submission_bundle/final_connected_pseudospectrum_proof_2026-07-16.pdf`.
- Final PDF: 33 pages; 832,821 bytes; SHA-256
  `115b022b5e67a5c06046f12ba4d7b43760ae1ed6898d434ad98900eb498022c0`.
- The final `latexmk` run exited successfully.  Its log contains no TeX errors,
  LaTeX/package warnings, undefined references, rerun requests, or overfull
  boxes.  It contains three benign underfull-vbox layout notices on the
  figure/bibliography pages.
- All 33 pages were rendered and visually inspected after the final source
  edit, including the dimension-one, folded-formula, and Lambert-`W` pages;
  no clipping, overlap, or malformed display was found.

The dated source preserves the manuscript's Lambert-`W_{-1}` threshold formula
and lower-branch expansion.  The old bundle name, undated TeX source, and
undated TeX build artifacts are absent.

## Formalization and audit scope

The complete and truthful claim for the current source is:

- the source has 102 labels: 92 mathematical labels, seven section labels, and
  three figure labels;
- all 92 mathematical labels have literal kernel counterparts: zero are
  proof-sufficient and zero are audited-only;
- all six theorem-like environments and the complete proof dependency graph of
  `thm:main` are represented in the canonical library; and
- every mathematical label, plus important unnumbered mathematical and
  physical claims, is accounted for in `FORMALIZATION_MAP.md`.

The 2026-07-16 source aligns the formerly nonliteral statements with what is
proved: it separates dimensionless identities from physical exposition, gives
the complete bordered odd-dilation matrix, states the folded identities on
their proved domains including collision, corrects the weak rational endpoint
bound while retaining the strict consequence, and states the all-angle
principal-sine formula.

`ConnectedPseudospectrum/LambertWThreshold.lean` supplies the lower real branch
that is absent from the pinned Mathlib revision.  It constructs the branch by
unique real inversion, proves its domain/specification and uniqueness, proves
the exact strict discrete crossing and explicit floor formula, and proves the
standard logarithmic--logarithmic bounded-error expansion.  Its totalization
outside the branch domain is never used as a branch identity without the
natural-domain hypothesis.

This remains deliberately narrower than a claim that every physical,
bibliographic, numerical, or unnumbered expository sentence is a Lean theorem.
The dimensional Hamiltonian, PBC/Bloch description, physical left/right modes,
skin-depth interpretation, second-quantized presentation, and dimensional
rescalings are intentionally outside Lean.  The displayed topology numerics are
reproducible floating-point checks, not interval or kernel certificates, and
are not used in `thm:main`.

## Default target and source integrity

- Lean: `leanprover/lean4:v4.28.0`.
- Lake: 5.0.0.
- Mathlib commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- `ConnectedPseudospectrum.lean` directly imports all 103 modules under
  `ConnectedPseudospectrum/`; the default target therefore checks the entire
  104-file canonical library closure.
- Current canonical closure: 41,474 lines; 1,707,190 bytes.
- Current length-prefixed path-and-content SHA-256:
  `b6cbd8b510d243a16401520f93acfcdaa6689806f56c80de6cd9747ce8e6a86d`.
- Total project-owned Lean sources: 105 files, including `AxiomAudit.lean`.

Current configuration hashes:

- `lakefile.toml`:
  `359183f676b6a7f214b89bac6368d042a590a8d060bac7a74da902086e609b00`;
- `lean-toolchain`:
  `db7bb24b756d745bbde83fe92718b51bd3625dae3701ba0f598d0eedcd3f3028`;
- `lake-manifest.json`:
  `7ecc5ae5b8b3e864347c44cc9daf70c0c38bbe2d15571260a1b428a80c042777`;
- `AxiomAudit.lean`:
  `35506314e88390ab0d90a279a14ccc9a94c6734c0370f2035ed53db0bd972db0`.

A current static scan of all 105 project-owned Lean sources and
`lakefile.toml` finds:

- no `set_option` command;
- no `#lint`, `@[nolint]`, linter configuration, linter driver, or linter
  suppression;
- no project `[leanOptions]` section or option override;
- no `sorry`, `admit`, `sorryAx`, `native_decide`, `Lean.ofReduce*`,
  `Lean.trustCompiler`, or `run_tac` in the canonical library; and
- no project `axiom`, `constant`, `opaque`, `unsafe`, `extern`, `partial`, or
  `implemented_by` declaration in the canonical library.

These text scans establish the source configuration, while the exact build
above establishes that the current graph checks with zero diagnostics under
default options.

## Cleanup state

- Removed the transitory Lean `Scratch/` and `scripts/` trees and the standalone
  `LinterAudit.lean` source.
- Removed `.DS_Store`, `__pycache__`, bytecode, editor backup, temporary, and
  empty transitory directories found in the active workspace.
- Preserved normal `.lake` build output, the dated TeX/PDF, the bibliography,
  SIAM class/style, all six figure assets, and the figure-generation script
  needed for reproducibility.
- The intentionally separate `legacy/` material was not treated as transitory
  project state.

## Current documentation

- `README.md`: project scope, pinned environment, canonical commands, and
  reproducibility snapshot.
- `FORMALIZATION_MAP.md`: complete 92-label literal map and important
  unnumbered-scope inventory.
- `LATEX_AUDIT.md`: source alignment, proof repairs, scope limits, and
  numerical-certification caveat.
- `AXIOM_AUDIT.md`: selected endpoint/closure trust-audit procedure.
- `HEARTBEAT_AUDIT.md`: exact default-options and default-heartbeat conditions.
