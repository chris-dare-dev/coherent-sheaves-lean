# CohLean

Coherent sheaves, Chern classes and Riemann–Roch for **smooth projective varieties over a
field**, in Lean 4 / Mathlib.

Dimension-general by construction. Surfaces (K3 first) are the near-term target, but every
definition is stated for a variety of dimension `n` so that threefolds and fourfolds are
specialisations rather than rewrites.

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

## What Mathlib v4.29.0 already provides

Schemes, `Spec`, `Proj`, the proper/smooth/separated/flat morphism classes,
`X.Modules` (the **abelian** category of sheaves of modules on a scheme),
`SheafOfModules.IsQuasicoherent`, `SheafOfModules.IsFinitePresentation`, sheaf cohomology
as `Ext` from the constant sheaf, and the full derived/triangulated stack.

Missing, and therefore in scope here: coherence, `Coh X`, divisors, `Pic X`, `O_X(D)`,
line and vector bundles, ampleness, higher direct images, finiteness of cohomology,
`χ(F)`, Serre duality, Chern classes, intersection numbers, Riemann–Roch.

## Architecture: two layers

### Layer A — `CohLean.Numerical` (the interface)

Everything Bridgeland-stability arguments consume from a variety is *numerical*. Layer A
states exactly that much, as a typeclass, with no schemes anywhere:

* `NumericalRing n A` — the numerical intersection ring `A^•(X)_ℚ`: a commutative
  `ℚ`-algebra graded by codimension, concentrated in degrees `0 … n`, with a degree map
  `∫_X : A → ℚ` supported in top codimension.
* `NumericalVariety n A N` — adds the numerical Grothendieck group `N(X)`, the Chern
  character (by graded components), the Todd class, and `χ`, subject to
  Hirzebruch–Riemann–Roch.

This unblocks downstream stability work immediately, and is falsifiable: the axioms are
visible in the type, and three models exist — a point, a K3 surface of degree `H² = 2d`, and
`ℙ²` — so nothing here is vacuously true. `ℙ²` is there specifically because its
`td₁ = (3/2)H` is nonzero, which the K3 model cannot test.

### Layer B — `CohLean.Coh` (the construction)

The real thing, built from Mathlib's scheme theory, in stages that each go upstream.

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

Layer A is complete and audited for the general expansion, the surface, threefold and
fourfold specialisations, the K3 and Calabi–Yau-threefold cases, the Euler pairing
`χ(E,F)` that Bridgeland stability is defined against, and the point, K3, and
projective-plane models. Layer B stage B1 is complete: `Coh X` is abelian on a locally
noetherian scheme, and its inclusion into `X.Modules` is exact. The proof includes locality,
the affine comparison and equivalence, and closure under kernels, cokernels, and extensions.
Every later Layer B stage has a milestone and issue-level dependency graph; see
[ROADMAP.md](ROADMAP.md).

```bash
lake build && lake env lean scripts/Audit.lean
```

The audit must show only `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.
There is no `sorry` in this library.

## Conventions

* Declarations live in Mathlib-style namespaces (`AlgebraicGeometry.*`), never in a
  `CohLean.*` namespace, so that upstreaming a stage is a file move rather than a rename.
* Toolchain pinned to `leanprover/lean4:v4.29.0` to match `bridgeland-stab-lean` and
  `bstab`, which are intended to `require` this package.
* No `sorry`. Work that is not done is listed as *not done* in the relevant module
  docstring, not stubbed.
