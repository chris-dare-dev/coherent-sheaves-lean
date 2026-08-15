# Architecture

## One library, organized by subject

`DerivedAlgGeo` follows the same broad convention as Mathlib: the Lake library,
the public umbrella, and the source directory share one name, and modules are
placed under mathematical subjects. Repository provenance is recorded in Git
and license notices; it is not encoded as permanent package boundaries.

The primary ownership areas are:

| Path | Mathematical ownership |
| --- | --- |
| `DerivedAlgGeo/AlgebraicGeometry` | coherent sheaves, cohomology, divisors, duality, intersection theory, numerical geometry, Proj, and Riemann--Roch |
| `DerivedAlgGeo/CategoryTheory/DGCategory` | dg categories, dg functors, opposites, products, and the homotopy-category seam |
| `DerivedAlgGeo/CategoryTheory/Triangulated/TStructure` | t-structures, hearts, exactness, and heart bridges |
| `DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition` | stability foundations, deformation theory, metrics, group actions, support, walls, weak stability, tilting, and families |
| `DerivedAlgGeo/LinearAlgebra` | integral and Mukai lattices plus matrix infrastructure |
| `DerivedAlgGeo/Algebra` | generic algebra missing from the pinned Mathlib revision |
| `DerivedAlgGeo/Topology` | generic topological infrastructure |
| `DerivedAlgGeo/Development` | exploratory probes that are not part of the stable public umbrella |

`Algebra` and `Topology` are intentionally small. A module belongs there only
when its statement is genuinely independent of algebraic geometry and category
theory. New top-level subjects require a coherent body of reusable mathematics,
not merely a new project milestone.

## Umbrellas

Every non-leaf directory should have a same-named `.lean` umbrella. A new leaf
is exported through its nearest umbrella. Stable subject roots flow upward to
`DerivedAlgGeo.lean`; development probes do not.

Consumers should import the narrowest stable umbrella that provides the API
they need. The all-library import is `import DerivedAlgGeo`.

## Namespaces

Declarations use the mathematical namespace already established by Mathlib
when one exists. Important repository namespaces include:

- `AlgebraicGeometry`
- `CategoryTheory.DGCategory`
- `CategoryTheory.Triangulated`
- `CategoryTheory.Triangulated.TStructure`
- `CategoryTheory.Triangulated.StabilityCondition`
- `IntegralLattice`
- `Mukai`

Do not recreate the retired `CohLean`, `DGLean`, or `BridgelandStabLean`
namespaces. File paths are organizational; declarations may use a more general
namespace when they extend an existing Mathlib API.

## Dependency direction

Generic infrastructure may be used by more specialized mathematics:

```text
Algebra / Topology / LinearAlgebra
                 ↓
CategoryTheory and AlgebraicGeometry
                 ↓
bridges between geometry, derived categories, and stability conditions
```

Avoid importing a large umbrella from a foundational leaf. In particular,
generic dg-category or t-structure files must not depend on geometric examples,
and algebraic-geometry foundations must not depend on a later stability
application merely to obtain a helper lemma.

## Trust and generated artifacts

`DerivedAlgGeoSweep.lean` is a verification umbrella. It adds development code
to the stable root so the emitter can inspect every tracked module; it is not a
second public library API.

The three subsystem audits retain separate declaration lists because their
historical coverage and completeness ratchets are useful, but they all inspect
the one `DerivedAlgGeo` library. `formalization.yaml` and the registry files are
trust and paper-coverage records, not alternate package maps.

## Placement checklist

When adding a module:

1. Place it under the narrowest existing mathematical subject.
2. Use the corresponding mathematical namespace.
3. Export it through each enclosing umbrella that should expose it.
4. Keep exploratory or intentionally unstable work under `Development`.
5. Update the appropriate audit and registry entry when adding public results.
6. Run `scripts/gates.sh` before publishing.
