# Connected pseudospectrum formalization

This Lean project kernel-checks the complete theorem and proof dependency graph
of the main mathematical result in
`final_connected_pseudospectrum_proof_2026-07-13.tex`.

## Locked manuscript

The audited source is:

```text
/Users/shanmujin/Documents/Hatano-Nelson/SIMAX_submission_bundle/final_connected_pseudospectrum_proof_2026-07-13.tex
```

Its SHA-256 is:

```text
b4828ea18c0386e0a694c91af065c523c948ef4cf003a7ee1d823d19a8c72223
```

The source has 2,449 lines.  Its pre-rename checksum was
`7cf4fc9fa4b019f6185560f38b20d8f1901d793b36e068d002c272bdeeed7a6f`;
the only byte-level change was the dated filename in the line-2 compilation
comment, so the mathematical text and line numbering are unchanged.

## Exact scope

The formalization claim is deliberately narrower than “every mathematical
sentence in the article is a Lean theorem.”  The article has 95 mathematical
theorem/lemma/proposition/equation labels:

- 80 have literal kernel counterparts;
- 12 have proof-sufficient conditional, strengthened, corrected, partial, or
  alternative counterparts; and
- three physical-exposition labels are audited but not kernel formalized.

All six theorem-like environments and every dependency needed for `thm:main`
are kernel formalized.  The final assembly is
`ConnectedPseudospectrum.main_theorem` in
`ConnectedPseudospectrum/MainTheorem.lean`.

`FORMALIZATION_MAP.md` gives the complete 95-label classification and maps the
kernel-backed content to current declarations.  It also inventories important
unlabeled physical, numerical, and global complex-root claims outside the
kernel scope.  `LATEX_AUDIT.md` records source ambiguities, the corrected
strictness error, proof-expansion repairs, and numerical-certification limits.

## Pinned environment

- Lean: `leanprover/lean4:v4.28.0`
- Lake: 5.0.0, bundled with Lean 4.28.0
- Mathlib commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`

## Canonical build

The acceptance command is exactly:

```sh
cd /Users/shanmujin/Documents/Hatano-Nelson/lean
lake build
```

There are no command-line Lean options in this build.  `lakefile.toml` has no
`[leanOptions]` section, linter driver, linter arguments, warning override, or
heartbeat override.  The recorded acceptance environment has no `LEAN*` or
`LAKE*` option variables.  Consequently Lean 4.28.0's defaults apply,
including its default heartbeat budget.

The default target is the umbrella module `ConnectedPseudospectrum.lean`.  It
imports every one of the 102 canonical modules in `ConnectedPseudospectrum/`;
there are no unimported library modules.

## Project hygiene

The repository now contains 104 project-owned `.lean` files: the 103-file
canonical library closure plus `AxiomAudit.lean`.  Transitory `Scratch/` and
`scripts/` content and the standalone linter audit were removed.  No linter
configuration or suppression is part of the project.

The following scans cover every remaining project-owned Lean source.  Each is
expected to produce no matches:

```sh
! rg -n --glob '*.lean' \
  '^\s*(?:local\s+|scoped\s+)?set_option\b|^\s*#lint|@\[[^]]*nolint' \
  .

! rg -n --glob '*.lean' \
  '\b(sorry|admit|sorryAx|native_decide|Lean\.ofReduce[A-Za-z0-9_]*|Lean\.trustCompiler|run_tac)\b' \
  ConnectedPseudospectrum ConnectedPseudospectrum.lean

! rg -n --glob '*.lean' \
  '^\s*(?:@\[[^]]+\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:axiom|constant|opaque|unsafe|extern|partial)\b|implemented_by' \
  ConnectedPseudospectrum ConnectedPseudospectrum.lean
```

The second and third scans target the canonical library.  `AxiomAudit.lean`
contains only imports and diagnostic `#print axioms` commands; its comments
name forbidden trust mechanisms so that the acceptance criterion is explicit.

## Kernel-axiom audit

The separate trust audit uses default Lean options:

```sh
lake env lean AxiomAudit.lean
```

`AxiomAudit.lean` contains 211 selected `#print axioms` commands, including the
final theorem and major mapped endpoints.  `main_theorem`'s own output covers
its dependency closure.  The only accepted foundational dependencies are
`propext`, `Classical.choice`, and `Quot.sound`; project-specific axioms or
compiler-trust escapes are failures.  See `AXIOM_AUDIT.md`.

## Reproducible source snapshot

The canonical library closure consists of 103 files, 40,860 lines, and
1,681,754 bytes.  Its length-prefixed path-and-content SHA-256 is:

```text
9c5810d61e561dbfc9ec874acb43570838cf3bb9b04d1ce9c918e98ddeb8924e
```

The exact computation is:

```sh
python3 - <<'PY'
from pathlib import Path
import hashlib

root = Path('/Users/shanmujin/Documents/Hatano-Nelson/lean')
files = [root / 'ConnectedPseudospectrum.lean'] + sorted(
    (root / 'ConnectedPseudospectrum').glob('*.lean'))
h = hashlib.sha256()
for path in sorted(files):
    relative = str(path.relative_to(root)).encode()
    contents = path.read_bytes()
    h.update(len(relative).to_bytes(8, 'big'))
    h.update(relative)
    h.update(len(contents).to_bytes(8, 'big'))
    h.update(contents)
print(h.hexdigest())
PY
```

`STATUS.md` records the latest clean default build, diagnostics, option scans,
source hashes, cleanup, and remaining scope limitations.
