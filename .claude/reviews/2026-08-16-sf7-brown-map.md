# SF7.2 Brown-map boundary review

## Scope

This slice moves the A.13 input from already-constructed approximation
triangles to the universal maps that Brown representability produces.

## Source correspondence

- `TStructure.ApproximationMap` records surjectivity on Hom from the aisle and
  injectivity after shifting by one.
- `AisleData.ofApproximationMaps` completes the universal map to a
  distinguished triangle.
- Triangulated exactness first kills the connecting morphism using shifted
  injectivity, then factors through the middle term and kills the original map
  using surjectivity. Thus the cone is proved to be right orthogonal.
- `CompactGeneratorApproximation.ofApproximationMaps` feeds this result into
  the A.13 constructor and formula (A.2).
- `Polishchuk.induceOfApproximationMaps` carries the map-level construction
  through categorical A.17.
- `IndExtensionData.ofApproximation` derives the large A.14 aisle and compact
  generation from the constructed A.13 t-structure.

## Trust boundary

No theorem, typeclass, axiom, or `sorry` derives the universal maps merely from
compactness. Mathlib v4.32.1 has neither Brown representability nor a
triangulated homotopy-colimit API, so the transfinite/telescope construction
cannot honestly be hidden behind an existing library theorem. Universal-map
existence and the geometric A.14 restriction equivalences remain explicit.
