# Default-options and heartbeat audit

## Current requirement

The canonical acceptance command, run from `lean/`, is exactly:

```sh
lake build
```

It has no build flags, no `-D` Lean options, and no environment-provided
`LEAN*` or `LAKE*` option variables in an acceptance run.

## Configuration state

`lakefile.toml` contains no `[leanOptions]` section.  In particular, the
project does not override `maxHeartbeats`, `warningAsError`, `autoImplicit`,
`relaxedAutoImplicit`, or any linter option.  It also has no linter driver or
linter arguments.

All 105 current project-owned Lean files have been text-scanned.  None contains
a `set_option` command, including a local or scoped heartbeat override.  The
former transitory `Scratch/` files containing the only two such commands were
removed; they were never imported by the canonical library.

Therefore the configuration selects Lean 4.28.0's defaults, including its
default 200,000-heartbeat budget per command.  A clean exact `lake build` is the
decisive validation: a timeout, warning, error, or other diagnostic must be
reported rather than converted or suppressed by project configuration.

## Scope of the default target

`ConnectedPseudospectrum.lean` is the default target.  It directly imports all
103 modules under `ConnectedPseudospectrum/`, so the exact build checks the
entire 104-file canonical library closure, including
`LambertWThreshold.lean`.  `AxiomAudit.lean` is a separate diagnostic source
checked by the default-options command documented in `AXIOM_AUDIT.md`.

The final exact build of the current 2026-07-16 source graph completed
successfully with 8,130 jobs and no diagnostics.  The command and evidence are
recorded in `STATUS.md`; no earlier build is being reused as acceptance proof.
