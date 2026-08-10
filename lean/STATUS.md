# Current validation status

Last updated: 2026-08-10 (Asia/Shanghai).

## Acceptance result

The LAA formalization passed the complete umbrella build:

```sh
lake build
```

- Exit status: `0`.
- Final line: `Build completed successfully (8131 jobs).`
- Errors and warnings: none.

The whole namespace also passed the Mathlib unused-argument linter.  The
temporary diagnostic driver was:

```lean
import ConnectedPseudospectrum

#lint only unusedArguments in ConnectedPseudospectrum
```

It found zero errors in 2,403 declarations, plus 2,217 automatically
generated declarations, and ended with `All linting checks passed!`.

The kernel-axiom audit was then run with:

```sh
lake env lean AxiomAudit.lean
```

It exited `0` for all 238 selected `#print axioms` commands.  Every record
reported exactly `propext`, `Classical.choice`, and `Quot.sound`; no record
contained a project axiom, `sorryAx`, or compiler-trust escape.

## Mathematical scope

`ConnectedPseudospectrum.main_theorem` checks the complete dependency chain
for the LAA main theorem: component contractibility, the exact connectedness
criterion, strict adjacent-size barrier decrease, the exact tail of connected
dimensions, quantitative bounds, the fixed-parameter critical-size
asymptotic, and the exact size-two endpoint.  Its assumptions `0 < a`,
`a < 1`, and `0 < epsilon` are all used.

`BackwardError.lean` proves both the general pointwise spectral backward-error
minimum and the path-specific formula displayed in the paper.
`GeneralToeplitz.lean` proves the exact affine-image identity and the paper's
positive unequal off-diagonal Toeplitz corollary, including component
contractibility, the connectedness criterion, strict scaled-barrier decrease,
two-sided bounds, the exact connected-dimension tail, the first connected
dimension, the scaled asymptotic, and the exact size-two endpoint.

The critical-size asymptotic uses the direct elementary inversion in
`ConnectedPseudospectrum/TailThresholdAsymptotic.lean`.  No Lambert `W`
function, exact Lambert floor formula, or auxiliary small-parameter condition
remains in the manuscript or formalization.

## Lean environment and source integrity

- Lean: `leanprover/lean4:v4.28.0`.
- Lake: 5.0.0.
- Mathlib commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- The umbrella module imports all 104 source modules under
  `ConnectedPseudospectrum/`; there are no detached proof modules.
- Canonical library closure: 105 files, 41,745 lines, 1,719,923 bytes.
- `AxiomAudit.lean` SHA-256:
  `d9e28d7960d0e32c344e953239546a0782c249969735108685cdab4639ef5523`.

Static scans of the canonical library found no `sorry`, `admit`,
`native_decide`, project axiom, unsafe declaration, compiler-trust escape,
linter suppression, or Lean option override.

## LAA manuscript

- Source: `../LAA/laa_connected_pseudospectra.tex`.
- Source size: 2,680 lines; 97,740 bytes.
- Source SHA-256:
  `f135e47d5c0e7428cbc4762a3c1247359f18e464fc4498aaee97f449f7ba58f3`.
- Compiled PDF: 44 A4 pages; 694,272 bytes.
- PDF SHA-256:
  `b73debecdfe48f0b375af2fdd15cbd76722ef854c2a4d85bff28624baaca4f96`.
- Local submission bundle (not tracked publicly): 12 files; 857,007 bytes.
- Local submission bundle SHA-256:
  `62d277272bfd831856106799982b1809d12cfa3028929dc111e08430530817ea`.

The manuscript was built with the supplied Elsevier `elsarticle` 3.4 class.
The final LaTeX/BibTeX log scan found no error, warning, undefined reference
or citation, rerun request, duplicate label, overfull box, or underfull box.
All 44 pages were rendered and visually checked.  The 12-file submission ZIP
passes a complete archive integrity test, and every archived file matches the
current workspace copy byte for byte.
