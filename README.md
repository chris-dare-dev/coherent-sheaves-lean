# CohLean

Coherent sheaves, Chern classes and Riemann–Roch for **smooth projective varieties over a
field**, in Lean 4 / Mathlib.

Dimension-general by construction. The core API is stated for a variety of dimension `n`;
surface, threefold, and fourfold formulas are optional displays of general identities rather
than separate foundational notions.

## Why this repo exists

As of August 2026 there is **no** formalisation of coherent sheaves, Chern classes, or
scheme-theoretic Riemann–Roch in any proof assistant. The survey behind that claim:

| Project | Covers | Relevance |
|---|---|---|
| [dmavani25/chip-firing-with-lean](https://github.com/dmavani25/chip-firing-with-lean) | Riemann–Roch for **graphs** (Baker–Norine), ~5.4k LOC | Combinatorial, not scheme theory |
| [a-dangelo/Lean-AG](https://github.com/a-dangelo/Lean-AG) | Görtz–Wedhorn ch. 5 dimension theory, ~800 LOC | Its README lists coherent sheaves, Chern classes, divisors, cohomology and Riemann–Roch as *long-term*, i.e. not done |
| [ProjConstruction/Proj](https://github.com/ProjConstruction/Proj) | Multi-graded Brenner–Schröer Proj, dilatations | Proj infrastructure only |
| [jjaassoonn/DimensionTheory](https://github.com/jjaassoonn/DimensionTheory) | Hilbert polynomials, dimension theory | **Reusable** — Hilbert polynomials drive the Snapper route below |
| [joelriou/lean-derived-categories](https://github.com/joelriou/lean-derived-categories) | Derived categories (now largely upstream) | Prerequisite for Serre duality |
| [YijunYuan/HarderNarasimhan](https://github.com/YijunYuan/HarderNarasimhan) | HN theory, order-theoretic | Deliberately avoids algebraic geometry |

The [Mathlib Initiative roadmap](https://mathlib-initiative.org/roadmap/) lists no
algebraic-geometry targets at all.

## What Mathlib v4.32.1 already provides

Schemes, `Spec`, `Proj`, the proper/smooth/separated/flat morphism classes,
`X.Modules` (the **abelian** category of sheaves of modules on a scheme),
`SheafOfModules.IsQuasicoherent`, `SheafOfModules.IsFinitePresentation`, sheaf cohomology
as `Ext` from the constant sheaf, and the full derived/triangulated stack. For B2 it also
provides locally finite `AlgebraicCycle`s with pushforward, `Scheme.ord`/`ordHom`, arbitrary-rank
`SheafOfModules.IsLocallyFree`, ring-level `Module.Invertible` and `CommRing.Pic`, generic
presheaf-of-modules sheafification, and ideal-sheaf subschemes.

CohLean now supplies coherence and the abelian category `Coh X`. The B2 construction also
supplies a rank-one/invertible-sheaf predicate, the sheafified tensor product with symmetric
monoidal coherence, and the resulting scheme-level `Pic X` group. Cartier divisors are present;
their associated invertible sheaves `O_X(D)` are constructed from local equations, with
`O_X(D + E) ≅ O_X(D) ⊗ O_X(E)`, `O_X(-D)` as tensor inverse, and the induced class-group
homomorphism to `Pic X`. Effective Cartier divisors and their twisted fundamental exact
sequences are present. Ampleness, higher direct images,
finiteness of cohomology, `χ(F)`, Serre duality, Chern classes, intersection numbers, and
Riemann–Roch are not yet present.

## Architecture

See [ARCHITECTURE.md](ARCHITECTURE.md) for the package map, ownership policy, and the intended
descent from geometric varieties and coherent sheaves to numerical data.

### Layer A — `CohLean.Numerical` (the interface)

Everything Bridgeland-stability arguments consume from a variety is *numerical*. Layer A
states exactly that much, as a typeclass, with no schemes anywhere:

* `NumericalRing n A` — the numerical intersection ring `A^•(X)_ℚ`: a commutative
  `ℚ`-algebra graded by codimension, concentrated in degrees `0 … n`, with a degree map
  `∫_X : A → ℚ` supported in top codimension.
* `NumericalVariety n A N` — adds the numerical Grothendieck group `N(X)`, the Chern
  character (by graded components), the Todd class, and `χ`, subject to
  Hirzebruch–Riemann–Roch.

`AlgebraicGeometry.Variety.NumericalData` connects this interface back to geometry: coherent
sheaves map additively through short exact sequences to numerical classes, while `chComp` and
`toddComp` are computed from geometric Chern-class data by universal formulas through
codimension four.

This unblocks downstream stability work immediately, and is falsifiable: the axioms are
visible in the type, and three models exist — a point, a K3 surface of degree `H² = 2d`, and
`ℙ²` — so nothing here is vacuously true. `ℙ²` is there specifically because its
`td₁ = (3/2)H` is nonzero, which the K3 model cannot test.

### Geometric construction — `CohLean.AlgebraicGeometry`, `CohLean.Coh`, and `CohLean.Divisors`

The geometric side is built from Mathlib's scheme theory and permanently maintained in
CohLean. A declaration may be contributed upstream, or replaced when Mathlib independently
acquires an equivalent API, but neither is a roadmap gate or an obligation.

**The design decision that makes this tractable: no Chow rings.** Intersection numbers come
from Snapper's theorem — for proper `X` over a field,
`(n₁,…,n_r) ↦ χ(F ⊗ L₁^{n₁} ⊗ ⋯ ⊗ L_r^{n_r})` is a numerical polynomial, and intersection
numbers are its coefficients. So `c₁` is a Cartier divisor class, `D · D'` is a polynomial
coefficient, and `ch₂` is read off `χ`. No cycles, no rational equivalence, no Chow group.
(Kleiman's numerical-ampleness route; Bădescu, *Algebraic Surfaces*, ch. 1.)

Layer A's fields are the trust boundary. Layer B's job is to discharge them.

## Status

**Picking this up cold? Read [HANDOFF.md](HANDOFF.md).** It carries the current state, the live
piece of work, and the Lean/Mathlib traps this repo has already paid for.

The numerical core is complete and audited for the general expansion and discriminant. Optional
surface, threefold, and fourfold display modules, the K3 and Calabi–Yau-threefold cases, the Euler pairing
`χ(E,F)` that Bridgeland stability is defined against, and the point, K3, and
projective-plane models. Layer B stage B1 is complete: `Coh X` is abelian on a locally
noetherian scheme, and its inclusion into `X.Modules` is exact. The proof includes locality,
the affine comparison and equivalence, and closure under kernels, cokernels, and extensions.
Layer B stage B2 now has its Cartier-divisor foundation: on an integral scheme,
`Scheme.CartierDivisor X` is the abelian group of locally representable sections of
`K(X)ˣ / 𝒪_{X,x}ˣ`, with principal divisors, divisor classes, order-of-vanishing coefficients,
and pullback from explicit compatible function-field data. It also has invertible sheaves,
their symmetric monoidal tensor product, the scheme-level Picard group `Pic X`, and the
associated sheaf `O_X(D)`. Local equations give canonical trivializations and transition
cocycles; multiplication of rational sections proves tensor additivity, principal divisors
become trivial, and Cartier divisor classes map to `Pic X`. Effective Cartier divisors carry
their closed subschemes and the short exact fundamental sequence
`O_X(-D) → O_X → i_* O_D`, together with every Cartier twist
`O_X(E-D) → O_X(E) → O_X(E) ⊗ i_* O_D`; both are also packaged in `Coh X`
under explicit coherence hypotheses.
Every later Layer B stage has a milestone and issue-level dependency graph; see
[ROADMAP.md](ROADMAP.md).

```bash
lake build
lake build CohLean.Development.DivisorAPIAudit \
  CohLean.Numerical.Specializations.Surface \
  CohLean.Numerical.Specializations.Threefold \
  CohLean.Numerical.Specializations.Fourfold
lake env lean scripts/Audit.lean
```

The audit must show only `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.
There is no `sorry` in this library.

## Conventions

* Files are organized by mathematical domain under `CohLean/`; there is no `ForMathlib`
  package. Declarations use mathematical namespaces such as `AlgebraicGeometry.*` when that is
  their natural owner. This does not signal an upstreaming commitment.
* CohLean owns and maintains its infrastructure. Equivalent Mathlib APIs may replace local
  declarations when convenient; upstream contributions are optional.
* Toolchain pinned to `leanprover/lean4:v4.32.1`, the patch release selected by the B2 API
  audit. A downstream package that `require`s CohLean must move its complete Mathlib dependency
  graph to v4.32.1 as well; the existing Bridgeland anchor still pins v4.29.0.
* No `sorry`. Work that is not done is listed as *not done* in the relevant module
  docstring, not stubbed.
