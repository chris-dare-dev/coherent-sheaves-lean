# DerivedAlgGeo

`DerivedAlgGeo` is a Lean 4 library for derived algebraic geometry. It develops
coherent sheaves and their cohomology, derived and dg categories, Bridgeland
stability conditions, Fourier--Mukai prerequisites, duality, intersection
theory, and Riemann--Roch.

The repository follows Mathlib's layout: one public source root, organized by
mathematical subject rather than by the history of the repositories that were
merged into it.

## Source layout

```text
DerivedAlgGeo.lean
DerivedAlgGeo/
├── Algebra/
│   └── Category/Grp/              # generic algebra infrastructure
├── AlgebraicGeometry/
│   ├── CoherentSheaf/
│   ├── Cohomology/
│   ├── Divisors/
│   ├── Duality/
│   ├── IntersectionTheory/
│   ├── Modules/
│   ├── Numerical/
│   ├── Proj/
│   ├── RiemannRoch/
│   └── Variety/
├── CategoryTheory/
│   ├── DGCategory/
│   └── Triangulated/
│       ├── TStructure/
│       └── StabilityCondition/
├── LinearAlgebra/
│   ├── Lattice/
│   └── Matrix/
├── Topology/
└── Development/                   # exploratory code, outside the public root
```

The old `CohLean`, `DGLean`, and `BridgelandStabLean` roots have been retired.
Their content now lives in this subject hierarchy and uses canonical
mathematical namespaces such as `AlgebraicGeometry`, `CategoryTheory`,
`CategoryTheory.Triangulated`, `IntegralLattice`, and `Mukai`.

## Imports

For the complete stable library:

```lean
import DerivedAlgGeo
```

Prefer the narrowest useful umbrella in library code, for example:

```lean
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech
import DerivedAlgGeo.CategoryTheory.DGCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition
```

`DerivedAlgGeo.Development` is intentionally not imported by
`DerivedAlgGeo.lean`; its probes may change while an API is being designed.

## Build and verification

The repository is pinned to Lean/Mathlib v4.32.1.

```bash
lake build
scripts/gates.sh fast
scripts/gates.sh
```

The full gate runs the unified environment linter, source-independence and
coverage checks, the subsystem axiom audits, and the repository-wide
declaration emitter. In particular, it rejects declarations depending on
`sorryAx`.

The maintained audit sources are:

- `scripts/AlgebraicGeometryAudit.lean`
- `scripts/StabilityConditionAudit.lean`
- `scripts/DGCategoryAudit.lean`

Documentation is built from the nested package so `doc-gen4` does not become a
runtime dependency:

```bash
cd docbuild
lake build DerivedAlgGeo:docs
```

See `ARCHITECTURE.md` for ownership and dependency rules and
`CONTRIBUTING.md` for the contribution workflow.

## License

Repository-authored code is released under the MIT license. Files derived from
external sources retain the notices described in `LICENSES/`.
