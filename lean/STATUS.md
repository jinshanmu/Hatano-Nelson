# Current validation status

Last updated: 2026-07-16 (Asia/Shanghai).

## Acceptance result

The current 2026-07-16 manuscript and Lean source state passed the complete
acceptance run.

The canonical Lean command was run literally, with no flags, option variables,
or source changes during the run:

```sh
lake build
```

- Exit status: `0`.
- Final line: `Build completed successfully (8130 jobs).`
- Errors, warnings, and linter diagnostics: none.
- `lakefile.toml` contains no Lean option or linter override, and the project
  contains no `set_option` command or linter suppression.

The separate default-options trust audit was also run literally:

```sh
lake env lean AxiomAudit.lean
```

It exited `0` for all 230 distinct `#print axioms` targets (216 one-line and 14
wrapped commands), with no diagnostic.  The union of the printed dependency
sets is exactly `propext`, `Classical.choice`, and `Quot.sound`; no project
axiom or compiler-trust escape appears.

## Locked manuscript and PDF

- Source:
  `SIMAX_submission_bundle/final_connected_pseudospectrum_proof_2026-07-16.tex`
- Source size: 2,802 lines; 105,090 bytes.
- Source SHA-256:
  `a7b3d51eb9ef2cd3b33ef6f85857f243df7fffeb7472e6bef4cfffbdc23e5ede`.
- Compiled PDF:
  `SIMAX_submission_bundle/final_connected_pseudospectrum_proof_2026-07-16.pdf`
- PDF size: 37 pages; 845,570 bytes.
- PDF SHA-256:
  `6f5f9e45f2afc1497609b686c5a92eafde8e0ebb0c34cf0285c06d87226dd6e3`.

The final `latexmk` compilation exited successfully.  The final log scan found
no TeX error, LaTeX/package warning, undefined reference, rerun request,
overfull box, or underfull box.  All 37 rendered pages were visually inspected,
including the repaired rectangular bound, the Lambert-`W_{-1}` discussion, the
regenerated figures, and the expanded physical interpretation; no clipping,
overlap, or malformed display was found.  The figure generator was replayed in
the `wirtinger_calculus` Conda environment and reproduced the stated
float64 threshold and analytic bracket.
The shortened running title renders as 49 characters.  The final source has
100 labels, all unique: 90 mathematical, seven section, and three figure
labels.  It uses all 29 unique bibliography entries, with no missing or unused
key, and all 61 unique reference targets resolve.  The primary labels written
to the auxiliary file agree exactly with the source.
The 2026-07-16 `.tex` and compiled `.pdf` are the current audited manuscript
artifacts.  The complete 2026-07-13 `.tex`/`.pdf` snapshot is also retained
unchanged as a historical manuscript version.  Regenerated TeX intermediates
were removed after verification.

The manuscript source and PDF, Python figure-generation script and
reproduction instructions, and complete pinned Lean project are available in
the public GitHub repository `https://github.com/jinshanmu/Hatano-Nelson`.

## Mathematical and labelwise scope

The manuscript has 100 labels: 90 mathematical labels (84 equations, four
lemmas, one theorem, and one proposition), seven section labels, and three
figure labels.  Every one of the 90 mathematical labels has an exact kernel
counterpart with the same mathematical content and hypotheses.  Thus the final
classification is 90 literal, zero proof-sufficient, and zero audited-only.
All 90 labelled mathematical environments retain the content and hypotheses
of the previous audited source.  The Lambert-`W`, asymptotic, and exact
two-site labelled items are likewise unchanged.  The final follow-up modifies
only unlabelled public-availability, fixed-`epsilon`, novelty-positioning, and
AI-disclosure prose, together with regrouping the numerical estimates as
dimensions 5--6 and 7--9 to reflect the connectedness split at `N_c=7`.
The editorial proof roadmap, numbered closure cases, explicit permutation
equality, and grammatical repair do not alter any inference.  No Lean source
file changed.

“One-to-one” is labelwise coverage, not an injective declaration count: every
mathematical label has an exact mapped Lean witness, while one displayed item
may require several declarations and repeated mathematical content may reuse a
theorem.  `FORMALIZATION_MAP.md` is the authoritative label-by-label map.

The complete connectedness-threshold argument is represented in the canonical
library: the spectral and least-singular-value identities, resolvent and
vertical monotonicity steps, connectedness criterion and component topology,
mesh-gap reduction, parity and central/noncentral comparisons, strict
threshold crossing, endpoint cases, final threshold theorem, and the stated
asymptotic consequences.  The exact quotient conjunction for
`eq:ratio-cross`, the two norm inequalities in `eq:rectangular-min`, collision
formulas, and all proof-expansion items recorded in `LATEX_AUDIT.md` are now
stated literally.  The final assembly is
`ConnectedPseudospectrum.main_theorem`.

The Lambert-`W_{-1}` content remains in the manuscript.  Because the pinned
Mathlib revision lacks the needed lower real branch, the project constructs the
branch by unique real inversion on its natural domain and proves its
specification, uniqueness, exact discrete crossing/floor formula, and the
logarithmic--logarithmic bounded-error asymptotic used by the manuscript.

## Physics scope

All physics-facing formulas in the manuscript are unnumbered.  Their signs,
scalings, domains, mode conventions, skin-depth interpretation, condition
number, resolvent expression, and dimensional threshold rescaling were checked
algebraically and numerically where appropriate.  The expanded backward-error,
physical barrier threshold, barrier scale, two-site cancellation, and
spectral-resolution interpretations were checked against the formalized
dimensionless statements.  The positive-sign one-particle representative and
its relation to the opposite sign convention are stated explicitly.

The two dimensionless parameter/gauge identities needed by the proof are also
checked in Lean.  The dimensional Hatano--Nelson Hamiltonian, PBC Bloch ellipse,
physical left/right modes, skin depth, and dimensional rescalings are
intentionally audited exposition outside Lean, as requested.  Bibliographic
claims and floating-point illustrations likewise are not promoted to kernel
theorems and are not used in the main proof.

## Environment and source integrity

- Lean: `leanprover/lean4:v4.28.0`.
- Lake: 5.0.0.
- Mathlib commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- `ConnectedPseudospectrum.lean` directly imports all 103 modules under
  `ConnectedPseudospectrum/`.
- Canonical library closure: 104 files; 41,546 lines; 1,710,377 bytes.
- Length-prefixed path-and-content SHA-256:
  `746623169ca009b33f2c3b76f24ad2f2bc1a4e6b877a74e8ba1bd2905ff9ecc5`.
- Total project-owned Lean sources: 105, including `AxiomAudit.lean`.

Configuration and audit hashes:

- `lakefile.toml`:
  `359183f676b6a7f214b89bac6368d042a590a8d060bac7a74da902086e609b00`;
- `lean-toolchain`:
  `db7bb24b756d745bbde83fe92718b51bd3625dae3701ba0f598d0eedcd3f3028`;
- `lake-manifest.json`:
  `7ecc5ae5b8b3e864347c44cc9daf70c0c38bbe2d15571260a1b428a80c042777`;
- `AxiomAudit.lean`:
  `5d9df8467a698f73a03386ecbebafac58f77f3fe369253b75524a6399f242dc0`.

Static scans of all project-owned Lean sources and `lakefile.toml` found:

- no `set_option`, `#lint`, `@[nolint]`, linter configuration, or option
  override;
- no `sorry`, `admit`, `sorryAx`, `native_decide`, `Lean.ofReduce*`,
  `Lean.trustCompiler`, or `run_tac` in the canonical library; and
- no project `axiom`, `constant`, `opaque`, `unsafe`, `extern`, `partial`, or
  `implemented_by` declaration in the canonical library.

The exact build establishes that the current imported graph checks under all
default options; the source scans make the absence of overrides and trust
escapes explicit.

## Cleanup and current documentation

- Removed the obsolete `HEARTBEAT_AUDIT.md`; heartbeat limits were not part of
  the mathematical or build issue, and no active validation step depends on it.
- Preserved the complete tracked 2026-07-13 manuscript/PDF byte-for-byte as a
  historical version alongside the current 2026-07-16 artifacts.
- Safely removed the transitory 20-page short source and PDF; the full 07-16
  manuscript and its 37-page PDF are the sole canonical current artifacts.
- Removed the superseded reproducibility ZIP, checksum, supplement index, and
  37-page cover-letter note after selecting the public-GitHub availability
  route.
- Removed the transitory Lean `Scratch/` and `scripts/` trees, temporary render
  output, caches, editor/OS debris, and active TeX build intermediates.
- Removed 327 generated artifacts (19,879,313 bytes) from the preserved local
  `legacy/` area while retaining its 49 `.tex` sources locally. The directory
  is ignored and excluded from the GitHub repository.
- Preserved `.lake`, the current manuscript/PDF, bibliography and SIAM support
  files, all figure assets, and the figure-generation source needed for
  reproducibility.

The current documentation set is:

- `README.md`: project scope, submission artifacts, pinned environment, and
  canonical reproduction commands;
- `FORMALIZATION_MAP.md`: complete 90-label literal map and important
  unnumbered-scope inventory;
- `LATEX_AUDIT.md`: manuscript repairs, threshold-proof closure, physics audit,
  and deliberate scope limits;
- `AXIOM_AUDIT.md`: executable endpoint/closure trust-audit procedure; and
- this `STATUS.md`: final build, PDF, scope, hashes, and cleanup evidence.
