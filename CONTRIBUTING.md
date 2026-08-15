# Contributing to DerivedAlgGeo

## Place code by mathematics

All stable Lean code lives below `DerivedAlgGeo/`. Follow the subject hierarchy
described in `ARCHITECTURE.md`; do not add new top-level libraries or restore
the retired repository roots.

Choose the narrowest natural home:

- geometric objects and theorems: `DerivedAlgGeo/AlgebraicGeometry/`;
- dg, derived, triangulated, and stability-category theory:
  `DerivedAlgGeo/CategoryTheory/`;
- reusable lattice or matrix theory: `DerivedAlgGeo/LinearAlgebra/`;
- exploratory API probes: `DerivedAlgGeo/Development/`.

Use Mathlib's established namespace when extending a Mathlib concept. Add a
same-named umbrella for a new non-leaf directory and export stable leaves
through their nearest existing umbrellas.

## Proof and trust policy

Committed library code must not use `sorry`, `admit`, or hidden axioms. Explicit
mathematical hypotheses and structure fields are acceptable; proof holes are
not. Keep conditional geometry honest by recording the exact hypothesis that a
later realization must supply.

Public declarations belong in the appropriate hand-maintained axiom audit:

- `scripts/AlgebraicGeometryAudit.lean`
- `scripts/StabilityConditionAudit.lean`
- `scripts/DGCategoryAudit.lean`

The completeness ratchet rejects growth in unaudited public declarations. When
the ratchet improves, lower its ceiling; never raise one to make a change pass.

## Local workflow

Build the stable root while developing:

```bash
lake build
```

Run the fast gate before requesting review:

```bash
scripts/gates.sh fast
```

Run the complete CI-equivalent gate before merge:

```bash
scripts/gates.sh
```

The full gate includes:

- Mathlib-style and environment linting for `DerivedAlgGeo`;
- all three axiom audits and the audit-completeness ratchet;
- source-independence, pin, paper-coverage, and no-lint checks;
- repository-wide emission and `sorryAx` coverage checks.

For a focused audit run:

```bash
lake build AlgebraicGeometryAudit StabilityConditionAudit DGCategoryAudit
lake env lean scripts/StabilityConditionAudit.lean \
  > /tmp/stability-condition-audit.txt 2>&1
python3 scripts/check_audit.py /tmp/stability-condition-audit.txt
```

## Documentation

Module docstrings should explain the mathematical statement, assumptions,
conventions, and relationship to surrounding APIs. Avoid provenance language
such as “the old CohLean version”; Git already records that history.

Build generated API documentation through the nested package:

```bash
cd docbuild
lake build DerivedAlgGeo:docs
```

## Changes that move declarations

Structural changes must update imports, umbrellas, audit names, registry
bindings, source-independence checks, documentation, and CI paths in the same
change. A move is complete only when `scripts/gates.sh` passes from a clean
checkout.
