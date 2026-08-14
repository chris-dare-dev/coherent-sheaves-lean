# Contributing to DerivedAlgGeoLean

Read [README.md](README.md) for the library overview and [ARCHITECTURE.md](ARCHITECTURE.md)
for module ownership. GitHub milestones and issues are the source of truth for planned work.

## Tracker discipline

- Every implementation issue belongs to a milestone and names its intended leaf path.
- Dependencies and acceptance criteria belong in the issue body.
- `ready` and `blocked` are mutually exclusive; `blocked` names the exact prerequisite.
- When a prerequisite merges, close completed issues and update newly unblocked work.
- If a planned flat filename becomes a subsystem, update the issue before implementation.

## Module placement

Declarations use their natural mathematical namespaces. Put coherent-sheaf and
numerical algebraic-geometry code below `CohLean`, and stability-condition code
below `BridgelandStabLean`. Put future derived-category and Fourier–Mukai
libraries below their dedicated roots once their first theorem lands. Never add
owner-authored code below `vendor/`.

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
lake env lean scripts/BridgelandAudit.lean > /tmp/bridgeland-audit.txt 2>&1
python3 scripts/check_audit.py /tmp/bridgeland-audit.txt
lake exe runLinter BridgelandStability
lake exe runLinter BridgelandStabLean
lake exe lint-style
python3 scripts/check_pin.py
python3 scripts/check_anchor_free.py
python3 scripts/check_coverage_map.py
lake build emit
lake exe emit --out /tmp/derived-alg-geo-emission.json
python3 scripts/check_emission_coverage.py /tmp/derived-alg-geo-emission.json
```

Add new public theorems to the appropriate subsystem audit: `scripts/Audit.lean`
for `CohLean` and `scripts/BridgelandAudit.lean` for `BridgelandStabLean`. Neither
audit may report `sorryAx`; the emitter is the backstop that catches declarations
omitted from the hand-maintained audits, since it sweeps the environment rather
than a list and so sees private and internal declarations too.

A new library root is not gated by being added to `lakefile.toml`. The emitter
imports `DerivedAlgGeoSweep.lean` and sweeps what that reaches, so import every
new root there as well — `scripts/check_emission_coverage.py` fails when a
tracked module is absent from the emission, which is what stops the gate from
shrinking to a scope where passing means nothing.
The environment linter gates all three libraries. `CohLean`'s pre-existing
backlog is enumerated per declaration in `scripts/nolints.json` rather than
suppressed, so a new violation fails CI while the 203 known ones stay countable.
Do not answer a linter failure with `lake exe runLinter --update`: it rewrites
the file from the current run and would bless your violation along with the
backlog. `scripts/check_nolints.py` fails if the list grows.

Paying the backlog down is welcome as its own contribution — run
`python3 scripts/check_nolints.py --relax` afterwards and lower the ceilings.

The toolchain is pinned. When updating it, update the root and documentation package manifests
and toolchain files together, then verify every shared dependency resolves to one revision.

## Git hygiene

Inspect `git status` before staging and include only files belonging to the change. Planning
and session-continuity documents named `ROADMAP.md` or `HANDOFF.md` are intentionally ignored;
durable plans belong in milestones/issues and transient handoffs belong outside the repository.
