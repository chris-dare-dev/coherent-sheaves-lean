# Roadmap

Target: Riemann–Roch for smooth projective varieties over a field, general dimension,
with K3 surfaces as the first worked instance and threefolds/fourfolds as the reason the
whole development is dimension-general.

Estimates assume heavy agent assistance. A solo human should multiply by roughly three.

## Layer A — the numerical interface

| # | Item | Status |
|---|---|---|
| A1 | `NumericalRing n A`, `NumericalVariety n A N` | **done** |
| A2 | `degree_ch_mul_todd` — the general RR expansion, any `n` | **done** |
| A3 | `Surface.chi_eq` — the `n = 2` specialisation | **done** |
| A4 | `Surface.discriminant` — Bogomolov–Gieseker `Δ = c₁² − 2r·ch₂` | **done** |
| A5 | `Examples.Point` — consistency witness, `n = 0` | **done** |
| A6a | `K3.IsK3` (`td₁ = 0`, `∫td₂ = 2`), `K3.chi_eq`, Mukai self-pairing, `⟨v,v⟩ = ∫Δ − 2r²` | **done** |
| A6b | A K3 *model*: `A = ℚ[t]/(t³)` with `∫t² = 2d`, satisfying `IsK3` | next |
| A7 | Threefold specialisation (`n = 3`), then fourfold (`n = 4`) | after A6b |
| A8 | Euler pairing `χ(E,F)` and the numerical lattice `N(X)` as a `ZLattice` | after A7 |

A6a is the mathematics: `IsK3` asserts only the two numerical facts about the Todd class,
so `chi_eq` and `mukaiSelfPairing_eq` are consequences of *those*, visibly and nothing else.

A6b is the model, and it is the only thing standing between Layer A and a non-vacuous
statement in dimension two. The obstacle is `NumericalRing.isInternal`: it needs
`1, t, t²` linearly independent over `ℚ` in `AdjoinRoot (X³)`, converted from
`AdjoinRoot.powerBasis` into an `iSupIndep`-plus-`iSup = ⊤` statement about the
`ℕ`-indexed family of spans. `LinearIndependent.iSupIndep_span_singleton` does the
independence half; the `Fin 3 → ℕ` reindexing and the `⊥`-above-the-dimension tail are the
glue that has to be written. Worth doing once as a reusable
`NumericalRing.ofGradedBasis`, since A7 needs exactly the same thing in dimensions 3
and 4.

## Layer B — the construction

| # | Stage | Estimate | Gate |
|---|---|---|---|
| B1 | `IsCoherent`, `Coh X`; closure under kernels, cokernels, extensions; `Coh X` abelian; affine comparison `Coh (Spec R) ≌ finite `R`-modules` | 2–3 months | definitions **done**, theorems not started |
| B2 | Invertible sheaves, `Pic X`, Cartier divisors, `O_X(D)`, the sequence `0 → O(−D) → O → O_D → 0` | 2–3 months | blocked on B1 |
| B3 | `χ(F)`: finiteness of `Hⁱ(X,F)` for coherent `F` on proper `X` over a field, and additivity of `χ` on short exact sequences | 4–6 months | **the real gate** |
| B4 | Snapper polynomials ⟹ intersection numbers, any dimension | ~3 months | blocked on B3 |
| B5 | Serre duality ⟹ `χ(O(D)) = χ(O) + ½D·(D−K)`, then dévissage to rank `r`; discharge `hirzebruch_riemannRoch` | ~6 months | blocked on B3, B4 |

Total 18–30 months. Layer A exists so that nothing waits on this.

### Notes on individual stages

**B1.** Mathlib gives `X.Modules` abelian plus `IsFinitePresentation ⟹ IsQuasicoherent` and
`⟹ IsFiniteType` as instances. The missing content is closure of the *subcategory*.
`Mathlib/CategoryTheory/ObjectProperty/{Kernels,Extensions,ClosedUnderIsomorphisms}.lean`
are the right vehicles.

**B2.** Upstream Mathlib gained `AlgebraicGeometry/AlgebraicCycle/Basic.lean` (cycles as
locally-finite-support functions, proper pushforward) and `OrderOfVanishing.lean` after
v4.29.0. Neither defines divisors, rational equivalence or Chow groups yet. **Do not
duplicate that work** — bump the toolchain at B2 and build on it, or contribute there.

**B3.** The hardest step and the one everything else waits on. Mathlib's sheaf cohomology
is `Ext` from the constant sheaf, which is the right general definition but not obviously
the one that makes finiteness provable; expect to need Čech cohomology
(`CategoryTheory/Sites/SheafCohomology/Cech.lean`) and the affine vanishing theorem first.

**B4.** Snapper's theorem is dimension-general, so B4 serves threefolds and fourfolds at no
extra cost. Reuse Hilbert-polynomial machinery from `jjaassoonn/DimensionTheory`.

**B5.** Serre duality is the second hard theorem. Mathlib's derived-category infrastructure
(Riou) is unusually strong and is the reason this is attemptable at all.

## Upstreaming

B1–B3 are Mathlib-shaped and should be PR'd as they land. Layer A is *not* Mathlib
material — it is an axiomatic interface, and Mathlib does not take those. It stays here.

## Non-goals

* Non-noetherian schemes. `IsCoherent` is defined as finite presentation, which is
  correct on locally noetherian schemes and strictly stronger elsewhere. Recorded in
  `CohLean/Coh/Defs.lean`.
* Chow rings, rational equivalence, and topological Chern classes. See the Snapper note in
  the README.
* Analytic or transcendental methods. Everything here is algebraic, over an arbitrary
  field unless a statement demands otherwise.
