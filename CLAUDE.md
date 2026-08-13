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

Review `git status` before staging. Keep transient `ROADMAP.md` and `HANDOFF.md`
files outside Git.
