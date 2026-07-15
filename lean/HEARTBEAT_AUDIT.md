# Default-options and heartbeat audit

## Current requirement

The canonical acceptance command is exactly:

```sh
lake build
```

It has no build flags, no `-D` Lean options, and no environment-provided
`LEAN*` or `LAKE*` option variables in the recorded validation run.

## Configuration state

`lakefile.toml` contains no `[leanOptions]` section.  In particular, the
project does not override `maxHeartbeats`, `warningAsError`, `autoImplicit`,
`relaxedAutoImplicit`, or any linter option.  It also has no linter driver or
linter arguments.

All 104 remaining project-owned Lean files were scanned.  None contains a
`set_option` command, including a local or scoped heartbeat override.  The
former transitory `Scratch/` files containing the only two such commands were
removed; they were never imported by the canonical library.

Therefore the build uses Lean 4.28.0's defaults, including its default
200,000-heartbeat budget per command.  A clean exact `lake build` is the
decisive validation: a timeout, warning, error, or other diagnostic would be
reported rather than converted or suppressed by project configuration.

## Scope of the default target

`ConnectedPseudospectrum.lean` is the default target.  It directly imports all
102 modules under `ConnectedPseudospectrum/`, so the exact build checks the
entire 103-file canonical library closure.  `AxiomAudit.lean` is a separate
diagnostic source and is checked by the default-options command documented in
`AXIOM_AUDIT.md`.

The latest clean-build result and source/configuration hashes are recorded in
`STATUS.md`.
