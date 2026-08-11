# Repository architecture

CohLean is organized by mathematical ownership. Module paths descend from a broad subject to
the smallest stable subsystem and then to a theorem-bearing leaf. Namespace ownership follows
the mathematics and is independent of the package path.

## Package map

| Subsystem | Responsibility |
|---|---|
| `AlgebraicGeometry/Modules` | Affine comparison, presentations, finiteness, and restriction |
| `AlgebraicGeometry/Divisors` | Cartier/effective divisors, invertible sheaves, Picard groups, determinants |
| `AlgebraicGeometry/Proj` | Graded localization, associated/twisting sheaves, and finiteness on projective spectra |
| `AlgebraicGeometry/Variety` | Geometric varieties and certified numerical realizations |
| `Coh` | Coherent-sheaf definitions, descent, affine theory, and abelian structure |
| `Cohomology` | Čech, derived, simplicial, spectral-sequence, and Euler-characteristic theory |
| `Intersection` | Numerical polynomials, intersection numbers, and Chern-character reconstruction |
| `Numerical` | Numerical interfaces, Grothendieck-group invariants, Riemann–Roch, models, and displays |
| `Topology` | Reusable open-cover infrastructure |
| `Development` | Compile-only API audits; not part of the stable root import |

Every non-leaf subsystem has a same-named `.lean` umbrella. `CohLean.lean` imports only stable
top-level umbrellas, keeping navigation and dependency boundaries aligned.

## Dependency direction

```text
schemes and geometric hypotheses
  -> coherent sheaves, divisors, and cohomology
  -> K-theoretic and intersection data
  -> NumericalVariety
  -> dimension-general Riemann–Roch invariants
  -> optional low-dimensional displays
```

The numerical layer is a visible axiomatic boundary. Geometric modules construct data that
discharges that boundary; they do not silently turn assumptions into theorems.

## Growth rules

1. Put a new module under the narrowest mathematical owner that can support more than one
   leaf over the project's lifetime.
2. Prefer a descriptive leaf such as `Duality/Serre.lean` over a long flat filename.
3. Export a new leaf through its nearest umbrella, not directly from `CohLean.lean`.
4. Create a new intermediate directory when a subject gains multiple independent concepts.
5. Keep temporary API reconnaissance under `Development/`; production theorems belong to
   their mathematical owner.

Planned paths in GitHub issues follow these rules so future work extends the tree instead of
re-flattening it.
