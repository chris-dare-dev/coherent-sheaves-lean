# Repository architecture

CohLean is a library in its own right, not a staging area for Mathlib. Code is grouped by the
mathematics it implements. Using a Mathlib-style namespace says where a declaration belongs
mathematically; it does not create an obligation to upstream it.

If Mathlib later provides an equivalent declaration, CohLean can adopt it and remove the local
implementation. Contributing CohLean code upstream remains optional and is never a milestone
gate.

## Package map

| Directory | Responsibility |
|---|---|
| `CohLean/Numerical` | Dimension-general numerical intersection data, universal characteristic-class formulas, Riemann--Roch, and numerical pairings |
| `CohLean/Numerical/Specializations` | Optional finite expansions at a chosen dimension; compatibility and display results, not foundational object types |
| `CohLean/Numerical/Examples` | Concrete models witnessing that the numerical axioms are consistent |
| `CohLean/AlgebraicGeometry/Variety.lean` | Geometric varieties over a field, kept distinct from their numerical realizations |
| `CohLean/AlgebraicGeometry/Variety/Numerical.lean` | Certified descent from coherent sheaves and geometric Chern classes to `NumericalVariety` |
| `CohLean/AlgebraicGeometry/Modules` | Module and sheaf-of-modules constructions over schemes |
| `CohLean/Coh` | Coherent sheaves and their categorical properties |
| `CohLean/Divisors` | Cartier and effective divisors, invertible sheaves, tensor/Picard structure, determinant lines, and first Chern classes |
| `CohLean/Cohomology` | Čech and spectral-sequence infrastructure used to compute sheaf cohomology |
| `CohLean/Topology` | General open-set-site infrastructure used by the geometric packages |
| `CohLean/Development` | Compile-only API audits and development probes; not part of the root import |

`CohLean.lean` is the public umbrella import. Development probes and optional numerical display
specializations are explicitly built immediately before `scripts/Audit.lean`, but are
deliberately not pulled into that umbrella.

## Geometric-to-numerical direction

The intended dependency direction is:

```text
scheme X + geometric hypotheses
  -> Coh X, Pic X, divisors, cohomology, K-theoretic/Chern data
  -> numerical intersection ring and numerical Grothendieck group
  -> NumericalVariety n A N
  -> dimension-general Riemann--Roch and stability invariants
  -> optional dimension-specific display formulas
```

`AlgebraicGeometry.Variety k` now bundles an integral finite-type scheme over `Spec k`, and
`SmoothProperVariety k` records the smooth/proper hypotheses currently expressible in Mathlib.
These are geometric source objects, not numerical records.

`Variety.NumericalData` is now the certified bridge. It requires a coherent-sheaf class map
that respects isomorphisms and short exact sequences, geometric Chern classes and Euler
characteristics compatible with that map, and the remaining grading and Riemann--Roch proofs.
Its `toNumericalVariety` constructor computes `chComp` and `toddComp` from the universal
characteristic-class formulas. Thus the remaining trust boundary is visible in named geometric
obligations instead of duplicated numerical component fields.

## Dimension and characteristic classes

Dimension is a parameter of `NumericalRing` and `NumericalVariety`, not a family of separate
surface/threefold/fourfold object definitions. In particular:

- `NumericalVariety.chi_eq_sum` computes the Riemann--Roch expansion for arbitrary `n`;
- `NumericalVariety.structureSheafEulerCharacteristic` selects the top Todd component for
  arbitrary `n`;
- `NumericalVariety.discriminant` is defined in every dimension and lives in codimension two;
- files in `Numerical/Specializations` merely normalize the finite sum for human-readable
  low-dimensional formulas.

`Numerical/CharacteristicClasses.lean` now records the universal conversions from Chern-class
data to Chern-character and Todd components through codimension four. The next characteristic-
class milestones are geometric: construct the Chern classes and Euler characteristic needed to
populate `Variety.NumericalData`, then discharge its grading, exact-sequence, and
Riemann--Roch obligations. The familiar surface, threefold, and fourfold normal forms remain
corollaries.
