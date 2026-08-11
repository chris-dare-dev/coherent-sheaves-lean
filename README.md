# CohLean

CohLean is a Lean 4 library for coherent sheaves, their cohomology, and numerical invariants
on algebraic varieties. The library is dimension-general: surfaces, threefolds, and fourfolds
are specializations of shared definitions rather than separate foundations.

The project aims to connect scheme-theoretic constructions to the numerical data used in
Riemann–Roch and stability theory while keeping every hypothesis and trust boundary explicit.

## What is formalized

- A dimension-general numerical intersection ring and numerical variety interface.
- Universal Chern-character and Todd-class formulas through codimension four.
- Numerical Riemann–Roch, discriminants, duality formulas, and Euler pairings.
- Concrete numerical models in dimension zero and for several classes of surfaces.
- Coherent sheaves on locally noetherian schemes, including locality and abelian-category
  structure.
- Affine comparison and finiteness results for sheaves of modules.
- Degree-zero localization of graded modules, associated sheaves and twisting sheaves on
  projective spectra, with explicit finiteness interfaces.
- Cartier and effective divisors, associated invertible sheaves, Picard-group structure,
  determinants, and first Chern classes.
- Čech, derived-functor, and spectral-sequence infrastructure for sheaf cohomology.
- Euler characteristics and their additivity under explicit finiteness data.
- Numerical polynomials, Snapper-style certificates, surface intersection numbers, and
  Chern-character reconstruction.

Incomplete theorems are described in module documentation and tracked as GitHub issues; the
library contains no `sorry` declarations.

## Repository map

The source tree follows the mathematical dependency hierarchy. Each directory with several
children has an umbrella module of the same name.

```text
CohLean/
├── AlgebraicGeometry/
│   ├── Divisors/                 # Cartier, effective, Picard, determinant
│   ├── Modules/
│   │   ├── Affine/               # comparison, gluing, finiteness, exactness
│   │   ├── Presentation/         # finite presentations and transport
│   │   └── Restriction/          # open-immersion restriction
│   ├── Proj/Modules/              # localization, associated sheaves, shifts, finiteness
│   └── Variety/                  # geometric varieties and numerical descent
├── Coh/
│   ├── Basic/                    # definitions and isomorphism invariance
│   ├── Descent/                  # locality
│   ├── Affine/                   # affine comparison
│   └── Abelian/                  # kernels, extensions, abelian structure
├── Cohomology/
│   ├── Cech/
│   ├── Derived/
│   ├── EulerCharacteristic/
│   ├── Simplicial/
│   └── SpectralSequence/
├── Intersection/
│   ├── ChernCharacter/
│   ├── NumericalPolynomial/
│   └── Surface/
├── Numerical/
│   ├── Core/
│   ├── GrothendieckGroup/
│   ├── RiemannRoch/
│   ├── Specializations/
│   └── Examples/
├── Topology/Opens/
└── Development/                  # compile-only API audits and probes
```

This layout reserves natural growth points for duality, higher-dimensional Riemann–Roch, and
further projective-geometry work represented in the issue tracker.

The Čech-to-derived comparison is complete for open covers of topological spaces. An explicit
injective resolution maps from its global-sections complex to the injective Čech total; the map
is a quasi-isomorphism because injective Čech rows are exact. Consequently every Čech-acyclic
cover computes `Sheaf.H` in all degrees. The resolution and Mathlib's `HasExt` witness remain
explicit inputs because the current library does not install enough injectives for abelian
sheaves globally.

## Building

The repository pins its Lean and Mathlib revisions.

```bash
lake build
lake env lean scripts/Audit.lean
```

The audit checks that public results use only the expected foundational axioms and do not
depend on `sorryAx`.

## Using CohLean

Import the complete stable library with:

```lean
import CohLean
```

Or depend on a narrower umbrella such as `CohLean.Cohomology.Cech` or
`CohLean.Numerical.GrothendieckGroup`.

To combine CohLean with Mathlib in another Lake package, add CohLean as a dependency and keep
the consuming package on the Lean/Mathlib revisions recorded by this repository's
`lean-toolchain` and `lake-manifest.json`.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md). Milestones and issues are the source of truth for
planned work, dependencies, and acceptance criteria. New leaves should be placed beneath the
smallest existing mathematical subsystem and exported through its nearest umbrella module.

## License

Apache 2.0. See [LICENSE](LICENSE).
