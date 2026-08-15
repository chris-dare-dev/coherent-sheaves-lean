# ADR-0012 — One Mathlib-style source root

- **Status:** accepted
- **Date:** 2026-08-14 (America/New_York)
- **Decider:** Chris Dare
- **Decision:** use one `DerivedAlgGeo` Lake library and source root, organized
  by mathematical subject.

## Context

The monorepo was assembled from coherent-sheaf, dg-category, and Bridgeland
stability repositories. Their temporary roots (`CohLean`, `DGLean`, and
`BridgelandStabLean`) preserved migration provenance but no longer described
mathematical ownership. They also forced consumers to remember repository
history in imports.

Mathlib provides the appropriate model: one public umbrella and a hierarchy of
subjects with same-named intermediate umbrellas.

## Decision

The public package, source directory, and umbrella are all named
`DerivedAlgGeo`. Most code is owned by:

- `DerivedAlgGeo/AlgebraicGeometry`;
- `DerivedAlgGeo/CategoryTheory`, including `DGCategory`, `Triangulated`,
  `TStructure`, and `StabilityCondition`.

Generic lattice and matrix prerequisites live in `LinearAlgebra`; genuinely
generic helper results may live in small `Algebra` or `Topology` subjects.
Exploratory probes live in `Development` and remain outside the public root.

Declarations use established mathematical namespaces rather than a repository
prefix. The three retired roots and namespaces must not be restored.

## Consequences

- `import DerivedAlgGeo` is the complete stable import.
- Consumers can select narrow subject umbrellas without knowing migration
  history.
- Existing audit lanes remain separate for coverage tracking but inspect one
  library.
- Historical ADRs, reviews, and Git commits retain the old names as provenance;
  current instructions and roadmaps use the new hierarchy.
