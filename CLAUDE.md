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

The stability-condition foundation is repository-owned. It is neither fetched
nor vendored from a separate stability repository; the source-independence gate
rejects reintroduction of the retired source and bridge roots.

## Repository taxonomy

- `CohLean/` owns coherent sheaves, algebraic geometry, cohomology, duality,
  intersection theory, numerical invariants, and Riemann–Roch.
- `BridgelandStabLean/` owns stability-condition extensions, abstract lattice
  theory, support, weak stability, tilting, metrics, walls, and symmetries.
- `BridgelandStabLean/Foundation/` owns the root stability API, including
  slicings, HN filtrations, deformation, and full stability conditions.
- `BridgelandStabLean/TStructure/` owns abstract t-structure theory.
- Future derived-category and Fourier–Mukai libraries get dedicated roots with
  their first real theorem; do not force them under an unrelated existing root.

Export new leaves through their nearest subsystem umbrella. Keep
`DerivedAlgGeoLean.lean` limited to stable library roots.

## Licence boundary

The owner-authored trunk is MIT. Repository-maintained Apache-2.0 files keep
their Mathlib contributor headers, provenance notice, and repository-wide
licence copy; see `LICENSES/README.md`.

## Proof integrity

There is no `sorry` in the libraries, and there must never be one. Unfinished work belongs in documentation
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
lake exe runLinter BridgelandStabLean
lake exe lint-style
python3 scripts/check_pin.py
python3 scripts/check_source_independence.py
python3 scripts/check_coverage_map.py
lake build emit
lake exe emit --out /tmp/derived-alg-geo-emission.json
python3 scripts/check_emission_coverage.py /tmp/derived-alg-geo-emission.json
```

`lake exe emit` is the repository-wide `sorry` gate: it sweeps every constant of
every module below `DerivedAlgGeoSweep.lean` and exits non-zero on `sorryAx`.
Adding a library root to `lakefile.toml` does **not** gate it — the emitter
imports `rootLib` and nothing else, so an unimported root contributes zero
constants and passes vacuously. Import every new root into
`DerivedAlgGeoSweep.lean`; `scripts/check_emission_coverage.py` fails when a
tracked module is missing from the emission.

`CohLean` is now under the environment linter too. Its pre-existing backlog is
enumerated per declaration in `scripts/nolints.json` — 203 entries as of
2026-08-14: 148 `docBlame`, 27 `unusedArguments`, 16 `defsWithUnderscore`,
12 `simpNF` — so the gate rejects anything new while the backlog stays visible
and countable.

**Never resolve a linter failure with `lake exe runLinter --update`.** It
rewrites the whole file from the current run and blesses the new violation
along with everything else, turning the gate off without touching CI or any
Lean file. `scripts/check_nolints.py` fails when the list grows, per linter and
in total. Fix the declaration, or argue for the exception in review.

When you do pay some of it down, run `python3 scripts/check_nolints.py --relax`
and lower the ceilings it prints, so the ratchet holds the new ground.

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
convention errors. It complements the environment linters with checks on the
exact lines changed by a branch.

The `mathlib-reviewer` agent reviews a branch diff for the conventions no script
can check — names that do not transcribe their statement, and docstrings that
restate the signature instead of explaining it.

## Unattended runs

Two skills, one iteration each, both halting before anything a human should
decide. Pair either with `/loop` for repeats.

- `land-pr` works the open PR queue, which is where the work is actually stuck.
  `scripts/pr_queue.py` ranks it. The queue is a cumulative stack — every branch
  is based on `main` but each slice contains its predecessors, so land the
  smallest diff first and never the tip. It never merges.
- `formalize-issue` claims an unclaimed issue and takes it to a PR. Check
  `scripts/pr_queue.py` first: an issue with an open PR is not unclaimed, and
  most of them have one.
