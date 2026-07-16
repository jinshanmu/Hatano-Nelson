# Connected pseudospectrum formalization

This Lean project kernel-checks all 92 labelled mathematical items and the
complete theorem and proof dependency graph of the main mathematical result in
`SIMAX_submission_bundle/final_connected_pseudospectrum_proof_2026-07-16.tex`.

## Locked manuscript

The audited source is:

```text
SIMAX_submission_bundle/final_connected_pseudospectrum_proof_2026-07-16.tex
```

Its SHA-256 is:

```text
84e0021272c9a9eb5cbfba3f6c82c4219bc2d64382232ebe68084bc9febe29b6
```

The source has 2,477 lines and 89,709 bytes.

## Exact scope

The manuscript has 102 labels: 92 mathematical labels (86 equations, four
lemmas, one theorem, and one proposition), seven section labels, and three
figure labels.  All 92 mathematical labels have literal kernel counterparts;
zero are proof-sufficient and zero are audited-only.  All six theorem-like
environments and every dependency needed for `thm:main` are kernel formalized.
The final assembly is `ConnectedPseudospectrum.main_theorem` in
`ConnectedPseudospectrum/MainTheorem.lean`.

The physical material is intentionally outside the Lean scope.  In particular,
the dimensional Hatano--Nelson Hamiltonian, PBC Bloch ellipse, physical modes,
and skin-depth interpretation are unnumbered exposition in the revised source.
This scope statement also does not promote bibliographic discussion or the
floating-point numerical illustrations to kernel theorems.

`FORMALIZATION_MAP.md` gives the complete 92-label map and separately inventories
important unnumbered physical, numerical, and expository claims.  `LATEX_AUDIT.md`
records the statement-level repairs that made the current labelled mathematics
literal, along with the remaining source caveats.

## Lower Lambert branch

The pinned Mathlib revision does not provide the real lower Lambert branch used
by the manuscript.  `ConnectedPseudospectrum/LambertWThreshold.lean` therefore
constructs a local `W_{-1}`-equivalent function from existence and uniqueness of
the inverse of `x * exp x` on the lower real branch.  It proves the natural
argument-domain facts, the exact strict discrete threshold and floor identity,
and the logarithmic--logarithmic bounded-error expansion used in the source.
The function is totalized outside its natural domain, while every theorem that
identifies it with the lower branch carries the appropriate domain hypothesis.

## Pinned environment

- Lean: `leanprover/lean4:v4.28.0`
- Lake: 5.0.0, bundled with Lean 4.28.0
- Mathlib commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`

## Canonical build

The acceptance command is exactly:

```sh
cd lean
lake build
```

There are no command-line Lean options in this build.  `lakefile.toml` has no
`[leanOptions]` section, linter driver, linter arguments, warning override, or
heartbeat override.  The acceptance environment must contain no `LEAN*` or
`LAKE*` option variables.  Consequently Lean 4.28.0's defaults apply, including
its default heartbeat budget.

The default target is the umbrella module `ConnectedPseudospectrum.lean`.  It
imports all 103 modules in `ConnectedPseudospectrum/`; the canonical library
closure therefore contains 104 files, with no unimported library modules.

## Project hygiene

The repository contains 105 project-owned `.lean` files: the 104-file canonical
library closure plus `AxiomAudit.lean`.  Transitory `Scratch/` and `scripts/`
content and the standalone linter audit have been removed.  No linter
configuration or suppression is part of the project.

The following scans cover every remaining project-owned Lean source.  Each is
expected to produce no matches:

```sh
cd lean

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
contains only imports, comments, and diagnostic `#print axioms` commands; its
comments name forbidden trust mechanisms so that the acceptance criterion is
explicit.

## Kernel-axiom audit

The separate trust audit also uses default Lean options:

```sh
cd lean
lake env lean AxiomAudit.lean
```

`AxiomAudit.lean` contains 229 selected `#print axioms` commands, including the
final theorem, the declarations corresponding to the formerly nonliteral
labels, the exact collision formulas, and the local lower-Lambert-branch
endpoints.  `main_theorem`'s own output covers its dependency closure.  The only
accepted foundational dependencies are `propext`, `Classical.choice`, and
`Quot.sound`; project-specific axioms or compiler-trust escapes are failures.
See `AXIOM_AUDIT.md`.

## Reproducible source snapshot

The current canonical library closure consists of 104 files, 41,474 lines, and
1,707,190 bytes.  Its length-prefixed path-and-content SHA-256 is:

```text
b6cbd8b510d243a16401520f93acfcdaa6689806f56c80de6cd9747ce8e6a86d
```

The exact computation, run from the repository root, is:

```sh
python3 - <<'PY'
from pathlib import Path
import hashlib

root = Path('lean')
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

`STATUS.md` records the final exact-build and axiom-audit evidence, source and
configuration hashes, cleanup state, and the deliberately excluded scope.
