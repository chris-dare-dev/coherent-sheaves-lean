# Subject ownership and dependency direction

This document records the stable source-layer contract. An arrow `A → B`
means that modules owned by subject `A` may import modules owned by subject
`B`. The graph is intentionally acyclic:

```text
Development ─┬→ Compatibility ─┬→ AlgebraicGeometry ─┬→ CategoryTheory
             │                 │                     ├→ Algebra
             │                 │                     ├→ LinearAlgebra
             │                 │                     └→ Topology
             │                 └→ CategoryTheory
             ├→ AlgebraicGeometry
             └→ CategoryTheory

CategoryTheory → LinearAlgebra
```

The support subjects `Algebra`, `LinearAlgebra`, and `Topology` are lower
layers. `DerivedAlgGeo.lean` is a public aggregation root, not a subject owner,
so its imports do not add edges to this graph.

## Ownership rule

`CategoryTheory` owns interfaces whose statements are independent of a
geometric realization. `AlgebraicGeometry` owns declarations specialized to
schemes, sheaves, geometric fibers, `Dqc`, derived pullback, finite-type
morphisms, or Fourier--Mukai kernels—even when their proofs are primarily
category theoretic. Proof technique does not determine source ownership.

In particular:

- abstract stability-family data remain in
  `DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families`;
- scheme, Dqc, pullback, finite-type, and kernel realizations live in
  `DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families`;
- `CategoryTheory` must not import either `DerivedAlgGeo.AlgebraicGeometry` or
  `Mathlib.AlgebraicGeometry`;
- `Compatibility` and `Development` are leaf layers and must never become
  dependencies of stable subject modules.

The source-layer gate in `scripts/check_layering.py` reconstructs the collapsed
graph from every tracked library import, rejects cycles and forbidden reverse
edges, and verifies that the relocated geometric family modules do not return
to their former owner.

## Migration compatibility

The former CategoryTheory families umbrella mixed generic interfaces with
geometric realizations. It now exports only the generic interfaces. Existing
declaration names remain in the
`CategoryTheory.Triangulated.StabilityCondition.Families` namespace, so clients
only need to migrate imports:

| Client need | Import |
| --- | --- |
| Generic family interfaces | `DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families` |
| Scheme-specific realizations | `DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families` |
| Former combined surface during migration | `DerivedAlgGeo.Compatibility.StabilityConditionFamilies` |

New library code should use the narrow owner import. The Compatibility import
is public but intentionally a leaf; it provides staged migration without
reintroducing a CategoryTheory-to-geometry edge.
