# Contributing to CohLean

Read [README.md](README.md) for the library overview and [ARCHITECTURE.md](ARCHITECTURE.md)
for module ownership. GitHub milestones and issues are the source of truth for planned work.

## Tracker discipline

- Every implementation issue belongs to a milestone and names its intended leaf path.
- Dependencies and acceptance criteria belong in the issue body.
- `ready` and `blocked` are mutually exclusive; `blocked` names the exact prerequisite.
- When a prerequisite merges, close completed issues and update newly unblocked work.
- If a planned flat filename becomes a subsystem, update the issue before implementation.

## Module placement

Declarations use their natural mathematical namespaces, while files use the `CohLean.*`
package hierarchy. Put new code below the narrowest stable owner and import it from the nearest
same-named umbrella module. Keep `CohLean.lean` limited to top-level subsystem imports.

One issue should normally own one leaf path. Avoid unrelated refactors in a feature change;
open a separate issue when another subsystem needs work.

## Proof integrity

There is no `sorry` in this library. Unfinished work is documented explicitly and tracked in
an issue rather than represented by a placeholder theorem or new axiom.

`NumericalVariety` is an intentional axiomatic interface. Its fields may be consumed, but must
not be described as geometrically proved until the corresponding construction exists. A new
axiom requires an issue identifying the geometric work that will discharge it and must remain
consistent with every model under `CohLean/Numerical/Examples/`.

## Validation

Run:

```bash
lake build
lake env lean scripts/Audit.lean
```

Add new public theorems to the appropriate section of `scripts/Audit.lean`. The audit must not
report `sorryAx`; CI also re-elaborates tracked Lean files to catch declarations omitted from
the audit.

The toolchain is pinned. When updating it, update the root and documentation package manifests
and toolchain files together, then verify every shared dependency resolves to one revision.

## Git hygiene

Inspect `git status` before staging and include only files belonging to the change. Planning
and session-continuity documents named `ROADMAP.md` or `HANDOFF.md` are intentionally ignored;
durable plans belong in milestones/issues and transient handoffs belong outside the repository.
