# Repository architecture

DerivedAlgGeoLean contains multiple Lean libraries organized by mathematical ownership.
`CohLean` module paths descend from a broad subject to
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
| `Duality` | Canonical sheaves, derived Serre-duality interfaces, and perfect pairings |
| `Intersection` | Numerical polynomials, intersection numbers, and Chern-character reconstruction |
| `Numerical` | Numerical interfaces, Grothendieck-group invariants, Riemann–Roch, models, and displays |
| `RiemannRoch` | Geometric Riemann–Roch, reconstructed Todd data, perfect-resolution dévissage, and scheme-derived numerical bridges through dimension four |
| `Topology` | Reusable open-cover infrastructure |
| `Development` | Compile-only API audits; not part of the stable root import |
| `BridgelandStabLean/Lattice` | Abstract numerical and Mukai lattice infrastructure |
| `BridgelandStabLean/Foundation` | Owner-authored Postnikov towers, HN filtrations, slicings, triangulated Grothendieck groups, class maps, and pre-stability conditions |
| `BridgelandStabLean/Compatibility` | Temporary, explicit adapters across retained third-party boundaries |
| `BridgelandStabLean/StabilityCondition` | Stability metrics, support, symmetry, walls, and weak stability |
| `vendor/BridgelandStability` | Apache-2.0 foundational slicing and deformation implementation |

Every non-leaf subsystem has a same-named `.lean` umbrella. `CohLean.lean` imports only stable
top-level umbrellas, keeping navigation and dependency boundaries aligned.
`DerivedAlgGeoLean.lean` imports the stable roots of both owner-authored libraries.

## Dependency direction

```text
schemes and geometric hypotheses
  -> coherent sheaves, divisors, and cohomology
  -> canonical sheaves and explicit Serre-duality realizations
  -> K-theoretic and intersection data
  -> geometric Riemann--Roch
  -> NumericalVariety
  -> dimension-general Riemann–Roch invariants
  -> optional low-dimensional displays
```

The numerical layer is a visible axiomatic boundary. Geometric modules construct data that
discharges that boundary; they do not silently turn assumptions into theorems.

`BridgelandStabLean/Foundation` is the bottom-up replacement boundary for the vendored
stability implementation. It now owns Postnikov and HN filtrations, slicings,
triangulated Grothendieck groups, pre-stability conditions, thin interval categories,
intrinsic admissible finite length, local finiteness, and full stability conditions.
Owner-authored definitions depend directly on Mathlib.
Conversions involving Apache-2.0 declarations live only under
`BridgelandStabLean/Compatibility/BridgelandStability`; downstream modules migrate to the
owner API one dependency layer at a time. The vendor library is removed only after no
owner-authored module imports it and the full trust gates pass without it.

`Duality/Canonical/Descent` similarly separates the smooth affine-chart theorem from the missing
sheafification comparison: explicit rank-`n` trivializations on the canonical chart cover produce
global finite locally-free cotangent data, while exterior-power and determinant descent remain
visible geometric inputs.

`RiemannRoch/Grothendieck` owns the dimension-independent descent of short-exact-sequence
additive coherent-sheaf invariants through `K₀(Coh X)`. Dimension-specific assemblies reuse
that layer instead of placing shared K-theory machinery under the surface namespace.

On surfaces, `RiemannRoch/Surface/Assembly` discharges HRR for all coherent sheaves from
twist-polynomial reconstruction. Finite locally free resolutions enter only the separate
term-by-term comparison with the classical rank/`c₁`/`c₂` formula.

In positive dimensions through four, `RiemannRoch/HigherDimension/Hirzebruch` uses the same
reconstruction mechanism to discharge HRR and descend it through `K₀(Coh X)`. Its Todd classes
are divisor-numerical representatives; cycle-valued tangent-bundle identifications remain a
separate geometric problem rather than a hidden field or instance.

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
