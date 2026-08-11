# CohLean

CohLean is a Lean 4 library for coherent sheaves, their cohomology, and numerical invariants
on algebraic varieties. The library is dimension-general: surfaces, threefolds, and fourfolds
are specializations of shared definitions rather than separate foundations.

The project aims to connect scheme-theoretic constructions to the numerical data used in
Riemann–Roch and stability theory while keeping every hypothesis and trust boundary explicit.

## What is formalized

- A dimension-general numerical intersection ring and numerical variety interface.
- Universal Chern-character and Todd-class formulas through codimension four.
- Numerical Riemann–Roch, discriminants, duality formulas, Euler pairings, and the
  nondegenerate numerical Grothendieck quotient with its explicit finite-free lattice boundary.
- Concrete numerical models in dimension zero and for several classes of surfaces.
- Coherent sheaves on locally noetherian schemes, including locality and abelian-category
  structure.
- Affine comparison and finiteness results for sheaves of modules.
- Degree-zero localization of graded modules, associated sheaves and twisting sheaves on
  projective spectra, including the canonical identification of the structure module with the
  structure sheaf, its standard-chart comparisons, and degree-one-chart trivializations of
  nonnegative twists through the canonical basic-open section maps. For polynomial projective
  space, degree-`d` homogeneous polynomials are identified concretely with global sections of
  `O(d)`, and variable-cover Čech terms are explicit homogeneous localizations.
- Cartier and effective divisors, associated invertible sheaves, Picard-group structure,
  determinants, and first Chern classes.
- Čech, derived-functor, and spectral-sequence infrastructure for sheaf cohomology.
- Euler characteristics and their additivity under explicit finiteness data.
- Numerical polynomials, Snapper-style certificates, surface intersection numbers, and
  Chern-character reconstruction.
- Explicit derived/cohomological Serre-duality interfaces, perfect coherent pairings, and the
  proved Euler symmetry for locally free sheaves.
- Geometric Riemann--Roch on smooth proper surfaces from Serre symmetry and Snapper
  intersections: line bundles and effective divisors, reconstructed Todd data, finite locally
  free dévissage, and coherent sheaves carrying explicit two-term perfect resolutions.
- The surface assembly boundary: additive geometric invariants descend through `K₀(Coh X)`,
  geometric HRR discharges the Layer A `NumericalVariety` field, and the Euler-radical quotient
  and K3 specialization reuse the audited Layer A conventions.

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
│   ├── Proj/Modules/              # localization, twists, projective sections, Čech terms
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
│   ├── Finiteness/               # finite-dimensionality boundary and cohomological bounds
│   ├── Simplicial/
│   └── SpectralSequence/
├── Duality/
│   ├── Canonical/                # canonical sheaf, class, and dualizing boundary
│   └── Serre/                    # derived statement, perfect pairings, Euler symmetry
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
├── RiemannRoch/
│   └── Surface/                  # divisors, Todd data, dévissage, and geometric-to-numerical assembly
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

For affine quasi-coherent sheaves, the library proves the non-circular compact-basis criterion of
Stacks Project, Tag 01EW, specializes it to the distinguished-open basis, and derives unconditional
positive-degree vanishing in Mathlib's `Sheaf.H`. The result applies to every quasi-coherent module
sheaf on `Spec R` through the affine module/sheaf comparison, without a noetherian hypothesis.

For quasi-compact schemes with affine diagonal, a fixed finite affine cover now gives an explicit
bound above which the actual derived cohomology of every quasi-coherent module vanishes. The proof
uses local affine `H'`-vanishing on all finite intersections and Mayer--Vietoris induction. This
boundedness is packaged separately from degreewise finite-dimensionality, with a constructor that
combines both inputs into `FiniteCohomology`.

For varieties over a field, the base field now acts canonically and centrally on every coherent
sheaf through the structure morphism. Applying derived cohomology constructs a functorial
`ModuleCat k` lift whose underlying additive groups are definitionally the existing `Sheaf.H`
groups. The remaining projective-finiteness work is therefore geometric Serre finiteness, not a
choice of scalar structures.

For smooth proper varieties of a fixed relative dimension, `Duality/Canonical` packages the
canonical sheaf as the determinant of explicit cotangent data, exposes its Picard class and
Cartier representatives, and records comparison data for a future dualizing object. The data is
kept visible because the pinned Mathlib has Kähler differentials for rings and same-site
presheaves, but not yet a scheme-level relative cotangent sheaf or dualizing-complex API.

`Duality/Serre` now fixes the derived shift convention and packages a linear realization of
Mathlib's actual `Abelian.Ext` groups. From explicit perfect-pairing data it proves complementary
cohomology dimensions and the sign `χ(F)=(-1)^nχ(Fᵛ⊗ω_X)`. On surfaces, the resulting Picard
symmetry and the geometric Snapper pairing prove the divisor Riemann--Roch formula. The
dualizing construction itself remains visible input rather than an axiom.

For surfaces, `RiemannRoch/Surface/NumericalVariety` turns compatible reconstructed Chern data,
geometric Todd components, and a coherent-sheaf HRR theorem into a concrete
`NumericalVariety 2 A K₀(Coh X)`. The HRR statement for virtual classes is proved by additive
descent rather than postulated. Its numerical class map then uses the Euler-radical quotient
from the numerical lattice API, and geometric K3 Todd identities produce the existing Layer A
`K3.IsK3` specialization.

`RiemannRoch/Surface` now reconstructs `td₀`, `td₁=-K_X/2`, and the top Todd representative
from the structure-sheaf twist polynomial, proving `∫td₂=χ(O_X)` and the K3 normalization.
The same package proves the classical rank/`c₁`/`c₂` formula for determinant-equipped finite
locally free sheaves and extends it to coherent sheaves only through a visible two-term perfect
resolution. Its exact-sequence, Grothendieck-group, and Layer A comparisons are term-by-term;
no global resolution property is assumed.

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
