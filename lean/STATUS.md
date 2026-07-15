# Current validation status

Last updated: 2026-07-16 (Asia/Shanghai).

## Acceptance result

The canonical acceptance command was run exactly from this directory:

```sh
lake build
```

Before the run, the project-owned `.lake/build` directory was absent and the
pinned Mathlib dependency cache had been restored.  The acceptance environment
contained no `LEAN*` or `LAKE*` option variables.

- Exit status: 0.
- Final line: `Build completed successfully (8129 jobs).`
- Fresh project-build elapsed time: 4,459 seconds (74 minutes 19 seconds).
- Diagnostics: zero errors, zero warnings, and zero linter diagnostics.
- No command-line flags, custom Lean options, or linter commands were used.
- The source/configuration fingerprint checked before and after the run was
  unchanged.

The separate default-options trust audit was run exactly as:

```sh
lake env lean AxiomAudit.lean
```

It exited successfully and checked all 211 selected `#print axioms` commands.
An exact confirmation run took 273.697 seconds and parsed as 211 unique output
records, with zero duplicates, malformed records, or diagnostics.
The complete observed dependency set was exactly:

- `propext`;
- `Classical.choice`; and
- `Quot.sound`.

No project-specific axiom, compiler-trust escape, warning, or error was
reported.  The selected declarations include
`ConnectedPseudospectrum.main_theorem`; its output audits the complete proof
dependency closure of the final theorem.  This is an endpoint/closure audit,
not a claim that every public declaration is printed individually.

## Locked manuscript and compiled artifact

- Audited source:
  `/Users/shanmujin/Documents/Hatano-Nelson/SIMAX_submission_bundle/final_connected_pseudospectrum_proof_2026-07-13.tex`
- Source size: 2,449 lines; 88,457 bytes.
- Source SHA-256:
  `b4828ea18c0386e0a694c91af065c523c948ef4cf003a7ee1d823d19a8c72223`.
- Pre-rename SHA-256:
  `7cf4fc9fa4b019f6185560f38b20d8f1901d793b36e068d002c272bdeeed7a6f`.
  The sole byte-level source change was the filename in the line-2 compilation
  comment; mathematical text and line numbering are unchanged.
- Last complete source/scope review: 2026-07-15.
- Compiled PDF: 32 pages; 830,049 bytes; SHA-256
  `67e752afe9d795ad0ab5e29321156e7d98001e9f0775ff8fdffe87cf434d7613`.
- The PDF and log are newer than the source.  All PDF pages render, and the TeX
  and BibTeX logs contain no errors, warnings, undefined references, or rerun
  requests.

The renamed bundle and dated TeX/PDF exist.  The old bundle name, undated TeX,
and undated TeX build artifacts are absent.

## Formalization and audit scope

The complete and truthful claim is:

- the source has 105 labels: 95 mathematical labels, seven section labels,
  and three figure labels;
- the 95 mathematical labels classify as 80 literal kernel counterparts,
  12 proof-sufficient nonliteral counterparts, and three audited-only physical
  exposition items;
- all six theorem-like environments and the complete proof dependency graph of
  `thm:main` are kernel formalized; and
- every mathematical label plus the important unlabeled mathematical and
  physical claims is accounted for in `FORMALIZATION_MAP.md`.

This is deliberately not the stronger, false claim that every mathematical,
physical, bibliographic, numerical, or globally stated complex-root sentence
in the article is a Lean theorem.  Material nonliteral scope includes:

- global negative-discriminant complex folded-root formulas; Lean instead has
  global determinant/transfer identities, explicit real positive-discriminant
  formulas, and exact collision formulas sufficient for the proof-used sheets;
- the exact Lambert-`W_{-1}` floor display; Lean proves an elementary
  bounded-error inversion sufficient for the final asymptotic;
- the full bordered odd-dilation display; Lean proves the exact leading block
  and every interlacing consequence used by the proof;
- physical rescalings, PBC/mode/skin interpretations, and the second-quantized
  presentation; and
- numerical topology values, which are reproducible floating-point checks
  conditional on computed samples, not validated numerical, interval, or
  kernel certificates.

The printed strict rational inequality inside `eq:Delta-upsilon-bounds` is
false at `L=2`.  Lean proves the correct weak inequality and preserves the
downstream strict conclusion, so this is documented as a proof-sufficient
correction rather than concealed as a literal formalization.

## Default target and source integrity

- Lean: `leanprover/lean4:v4.28.0`.
- Lake: 5.0.0.
- Mathlib commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- `ConnectedPseudospectrum.lean` directly imports all 102 modules under
  `ConnectedPseudospectrum/`; the default target therefore checks the entire
  103-file canonical library closure.
- Canonical closure: 40,860 lines; 1,681,754 bytes.
- Length-prefixed path-and-content SHA-256:
  `9c5810d61e561dbfc9ec874acb43570838cf3bb9b04d1ce9c918e98ddeb8924e`.
- Total project-owned Lean sources: 104 files, including `AxiomAudit.lean`.

Configuration hashes:

- `lakefile.toml`:
  `359183f676b6a7f214b89bac6368d042a590a8d060bac7a74da902086e609b00`;
- `lean-toolchain`:
  `db7bb24b756d745bbde83fe92718b51bd3625dae3701ba0f598d0eedcd3f3028`;
- `lake-manifest.json`:
  `7ecc5ae5b8b3e864347c44cc9daf70c0c38bbe2d15571260a1b428a80c042777`;
- `AxiomAudit.lean`:
  `7810d43f7a09b29a0fed17e7da96b3e5405093a008ebac754ccfc8e08c732d4d`.

All 104 project-owned Lean sources and `lakefile.toml` were scanned.  The final
state has:

- no `set_option` command;
- no `#lint`, `@[nolint]`, linter configuration, linter driver, or linter
  suppression;
- no project `[leanOptions]` section or option override;
- no `sorry`, `admit`, `sorryAx`, `native_decide`, `Lean.ofReduce*`,
  `Lean.trustCompiler`, or `run_tac` in the canonical library; and
- no project `axiom`, `constant`, `opaque`, `unsafe`, `extern`, `partial`, or
  `implemented_by` declaration in the canonical library.

## Cleanup state

- Removed the transitory Lean `Scratch/` and `scripts/` trees and the standalone
  `LinterAudit.lean` source.
- Removed `.DS_Store`, `__pycache__`, bytecode, editor backup, temporary, and
  empty transitory directories found in the active workspace.
- Preserved normal `.lake` build output, the dated TeX/PDF and their current
  build records, the bibliography, SIAM class/style, all six figure assets,
  and the figure-generation script needed for reproducibility.
- The intentionally separate `legacy/` material was not treated as transitory
  project state.

## Current documentation

- `README.md`: project scope, pinned environment, canonical commands, and
  reproducibility snapshot.
- `FORMALIZATION_MAP.md`: complete 95-label classification and important
  unlabeled-scope inventory.
- `LATEX_AUDIT.md`: source ambiguities, proof repairs, scope limits, and
  numerical-certification caveat.
- `AXIOM_AUDIT.md`: selected endpoint/closure trust-audit procedure.
- `HEARTBEAT_AUDIT.md`: exact default-options and default-heartbeat evidence.
