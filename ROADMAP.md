# Roadmap

Work is tracked as [milestones and issues](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues).
Every issue names the exact file it creates, so issues labelled `ready` can be picked up
simultaneously without merge conflicts. `lakefile.toml` is the one shared file — coordinate
before touching it. The live dependency graph is recorded in each milestone description;
`ready` and `blocked` are mutually exclusive, while `in-progress` means an implementation or
pull request already exists.

Current independent entry points are [#6](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/6),
[#13](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/13),
[#11](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/11),
[#21](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/21),
[#26](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/26),
[#27](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/27), and
[#33](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/33).
[PR #16](https://github.com/chris-dare-dev/coherent-sheaves-lean/pull/16) is the active B1
locality/open-immersion work.


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
| A6b | A K3 *model*: `A = ℚ[t]/(t³)` with `∫t² = 2d`, satisfying `IsK3` | **done** |
| A6c | `Examples.RankOneSurface` — the shared ring; `Examples.ProjectivePlaneModel` — `ℙ²`, `td₁ ≠ 0` | **done** |
| A7a | `Threefold.chi_eq` (`n = 3`) and `CalabiYauThreefold.IsCalabiYau` | **done** ([#4](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/4)) |
| A7b | `Fourfold.chi_eq` (`n = 4`) | **done** ([#5](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/5)) |
| A8 | Euler pairing and the numerical lattice | [#6](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/6) → [#17](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/17) |

A6a is the mathematics: `IsK3` asserts only the two numerical facts about the Todd class,
so `chi_eq` and `mukaiSelfPairing_eq` are consequences of *those*, visibly and nothing else.

A6b is done: `AdjoinRoot (X³)` carries the power basis `1, H, H²`, `NumericalRing.ofGradedBasis`
turns it into the graded ring, and `k3_isK3` checks `td₁ = 0` and `∫td₂ = 2`. Every theorem in
`CohLean/Numerical/K3.lean` is now a statement about an object that exists.

The degree `H² = 2d` is a parameter, and `d : ℕ` rather than `ℚ` because `χ` must be integral:
Riemann–Roch on this model reads `χ(r, c, s) = 2r + 2ds`.

A6c factored the two models. Every Picard-rank-one surface has the same intersection ring
`ℚ[t]/(t³)` up to the single number `∫H²`, so `Examples/RankOneSurface.lean` carries the ring,
the grading, the Chern character and `surfaceDegree_ch_mul_todd` — the reduction of
`ch·td` modulo `H³ = H⁴ = 0` — and a model costs only a Todd class. `ℙ²` matters because its
`td₁ = (3/2)H` is nonzero: the K3 model multiplies that term by zero and so cannot detect a
sign error in it. `p2Chi_lineBundle` pins it down by recovering `χ(O(nH)) = (n+1)(n+2)/2`.

A7 cashes the dimension-general claim. `Threefold.chi_eq` and `Fourfold.chi_eq` are the same
proof as `Surface.chi_eq` with `Finset.sum_range_succ` fired one and two more times; no lemma
in `Numerical/RiemannRoch.lean` had to change, which is the evidence that `degree_ch_mul_todd`
is general rather than a surface theorem stated with a variable in it.

`CalabiYauThreefold.IsCalabiYau` mirrors `K3.IsK3`: two conditions on the Todd class
(`td₁ = 0`, `∫td₃ = 0`) and nothing else. Both the rank term and the `ch₂` term of
`Threefold.chi_eq` drop, leaving `χ(E) = ∫c₁(E)·td₂ + ∫ch₃(E)` — two terms, not the three the
A7 issue sketched, because `td₁ = 0` kills `∫ch₂(E)·td₁` as well.

Neither dimension has a **model** yet, so A7 is in the state A6a was in before A6b: the
theorems are conditional on a `NumericalVariety 3 A N` (resp. `4`) existing. The rank-one
analogues are `ℚ[t]/(t⁴)` with `∫t³ = d` and `ℚ[t]/(t⁵)` with `∫t⁴ = d`, both reachable from
`NumericalRing.ofGradedBasis` the way `Examples/RankOneSurface.lean` is. A Calabi–Yau
threefold model is the one that earns its keep — it is the first place `IsCalabiYau` could be
shown non-vacuous.

A8 is deliberately split into the Euler-pairing construction and the quotient/lattice
construction so that the milestone title has a concrete deliverable for both halves.

## Layer B — the construction

| # | Stage | Estimate | Gate |
|---|---|---|---|
| B1 | Coherent category, locality, affine comparison, closure, abelian/exact inclusion | 2–3 months | [milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/4); PR #16 active, #11 ready |
| B2 | Invertible sheaves, `Pic X`, Cartier divisors, `O_X(D)`, determinant, effective-divisor sequence | 2–3 months | [milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/7); #21 ready, remainder gated |
| B3 | Affine vanishing, cohomology finiteness/boundedness, geometric `χ`, additivity | 4–6 months | [milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/5); #13, #26, #27 ready |
| B4 | Numerical polynomials, Snapper, intersections, numerical Chern data | ~3 months | [milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/9); #33 ready |
| B5 | Canonical sheaf, Serre duality, surface RR, dévissage, Layer A discharge | ~6 months | [milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/8); blocked on B2–B4 |

Total 18–30 months. Layer A exists so that nothing waits on this.

### Notes on individual stages

**B1.** Mathlib gives `X.Modules` abelian plus `IsFinitePresentation ⟹ IsQuasicoherent` and
`⟹ IsFiniteType` as instances. PR #16 proves closure under isomorphisms, finite-presentation
locality, and the equivalence connecting slice restriction to scheme-level restriction along
an open immersion. The remaining graph is explicit in the milestone: global presentations and
the affine comparison feed kernels/cokernels; locality feeds extensions; those closure results
feed the abelian/exact-inclusion assembly.

On the affine-local criterion (issue #12): Mathlib has
`SheafOfModules.QuasicoherentData.bind` and `IsQuasicoherent.of_coversTop`, so local-to-global
is done — **for quasicoherence only**. There is no finite-presentation analogue, and supplying
one is a real Mathlib gap rather than an unwrapping exercise. Note also that `M.over U` lives
on the site `Over U` with topology `J.over U`, so composing restrictions is a site
equivalence, not a triviality; `bind` handles it with `pushforwardPushforwardEquivalence`.
The full plan is on the issue. Issue #11 does not depend on any of this and is the better
first pick for the milestone.

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
