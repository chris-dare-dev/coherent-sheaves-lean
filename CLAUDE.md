# Working in DerivedAlgGeoLean

Read [README.md](README.md) for mathematical scope and
[ARCHITECTURE.md](ARCHITECTURE.md) for module ownership. GitHub milestones and
issues are the source of truth for planned work.

## Reproducible dependencies

`lean-toolchain` and every revision in `lakefile.toml` are exact pins. Mathlib
is the single direct foundational dependency for every library. The separately
versioned `MathFormalContract` package is a zero-dependency leaf and must remain
one; if it acquires a Lake dependency, remove it here until the pin policy is
re-evaluated.

`BridgelandStability` is vendored under `vendor/BridgelandStability`, not fetched
as a Git dependency. Update it only through a deliberate port with provenance,
license, full-build, linter, and axiom-gate evidence.

## Repository taxonomy

- `CohLean/` owns coherent sheaves, algebraic geometry, cohomology, duality,
  intersection theory, numerical invariants, and Riemann–Roch.
- `BridgelandStabLean/` owns stability-condition extensions, abstract lattice
  theory, support, weak stability, tilting, metrics, walls, and symmetries.
- `BridgelandStabLean/Foundation/` owns the replacement root API. It must be
  Mathlib-only and remain anchor-free under `scripts/check_anchor_free.py`.
- `BridgelandStabLean/Compatibility/` is the only place new conversion code may
  name the retained Apache vendor API during the ownership migration.
- `BridgelandStabLean/TStructure/` owns anchor-free abstract t-structure theory.
- `BridgelandStabLean/Anchor/` owns explicit compatibility bridges to the
  foundational library. Nothing anchor-free may depend on it.
- `vendor/BridgelandStability/` is third-party Apache-2.0 source. Do not place
  owner-authored work there.
- Future derived-category and Fourier–Mukai libraries get dedicated roots with
  their first real theorem; do not force them under an unrelated existing root.

Export new leaves through their nearest subsystem umbrella. Keep
`DerivedAlgGeoLean.lean` limited to stable library roots.

## Licence boundary

The owner-authored trunk is MIT. Retained third-party source is Apache-2.0 and
must keep its copyright, licence headers, component `LICENSE`, and `NOTICE`.
Never rewrite third-party headers as MIT. See `LICENSES/README.md`.

The direct vendor-import inventory is frozen by `scripts/check_anchor_free.py`.
Each ownership slice removes entries from that allowlist; new entries outside
`Compatibility/` are forbidden.

## Proof integrity

There is no `sorry` in the owner-authored libraries or the reachable vendored
surface, and there must never be one. Unfinished work belongs in documentation
and a tracker issue, never a placeholder theorem, axiom, or instance.

Keep abstract lattice and stability results distinct from geometric
realizations. A theorem about an abstract Mukai lattice is not automatically a
theorem about a variety or derived category; realization hypotheses stay
explicit.

## Validation

Run before pushing:

```bash
lake exe cache get
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
```

`CohLean` retains its build, axiom-audit, and source-elaboration gates. Its
pre-existing documentation/naming linter backlog is not blanket-suppressed by
the merge; treat that as separate maintenance work.

`scripts/gates.sh` runs that list in CI's order and prints one `GATE <name>:
pass|FAIL` line per gate; `scripts/gates.sh fast` runs build, style, and the two
axiom audits only.

Review `git status` before staging. Keep transient `ROADMAP.md` and `HANDOFF.md`
files outside Git.

## Mathlib conventions

`.claude/references/mathlib-style.md` is the standard: what CI already checks,
what only a reviewer can check, and the deltas this repository keeps on purpose.
Read it before writing Lean.

`scripts/check_mathlib_style.py` runs after every `Write`/`Edit` of an
owner-authored `.lean` file (see `.claude/settings.json`) and blocks on
convention errors. It covers the gap CI leaves: `runLinter` is wired to
`BridgelandStability` and `BridgelandStabLean` only, so `CohLean` and the
umbrella are otherwise unlinted.

The `mathlib-reviewer` agent reviews a branch diff for the conventions no script
can check — names that do not transcribe their statement, and docstrings that
restate the signature instead of explaining it.

## Unattended runs

The `formalize-issue` skill is one hands-off iteration: claim a ready issue,
formalize on an `agent/` branch, run the gates, open a PR, halt. It never
merges and never writes a `sorry`. Pair it with `/loop` for repeats.
