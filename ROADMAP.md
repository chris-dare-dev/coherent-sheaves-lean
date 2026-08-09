# Roadmap

Work is tracked as [milestones and issues](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues).
Every issue names the exact file it creates, so issues labelled `ready` can be picked up
simultaneously without merge conflicts. `lakefile.toml` is the one shared file — coordinate
before touching it. The live dependency graph is recorded in each milestone description;
`ready` and `blocked` are mutually exclusive, while `in-progress` means an implementation or
pull request already exists.

Current independent entry points are [#9](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/9),
[#21](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/21),
[#27](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/27),
and [#33](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/33).


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
| A8a | `NumericalRingWithDual`, `chi₂` (the Euler pairing), `K3.chi₂ = −⟨v,v⟩` | **done** ([#6](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/6)) |
| A8b | The numerical lattice `N(X)` as a `ZLattice`; the radical of `chi₂` | [#17](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/17) |

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

A8a landed with one correction to its issue. Issue #6 asked for `chi₂ E F = chi₂ F E` in even
dimension; that is **false**, and `Surface.chi₂_sub_chi₂_swap` measures the failure exactly:

`χ(E,F) − χ(F,E) = 2·(r_E·∫c₁(F)·td₁ − r_F·∫c₁(E)·td₁)`.

`ℙ²` has `td₁ = (3/2)H ≠ 0`, so the obstruction is real and the repo already contains a model
that exhibits it. Symmetry holds exactly when `td₁ = 0`
(`Surface.chi₂_symm_of_toddComp_one_eq_zero`), hence on K3s and Calabi–Yaus. The general
`χ(E,F) = (-1)ⁿ χ(F,E)` is Serre duality, a B5 theorem about `Ext`, not an identity between
these integrals — it is not asserted at Layer A.

Two design points worth keeping. `NumericalRingWithDual` is a **mixin** over `NumericalRing`,
not a field and not an `extends`: a field breaks every instance in `Numerical/Examples/`, and
an `extends` creates a second path to `NumericalRing n A` whenever a `NumericalVariety` is
also in scope. And `chi₂` needs **no** dual instance at all — `chDual` is the explicit
alternating sum, which the grading alone supplies, so the pairing and all of its consequences
work on any `NumericalVariety`. The involution is used in exactly one lemma,
`chi₂_eq_degree_dual_ch`, which is what earns `chDual` its name.

`NumericalRingWithDual` consequently has **no instance** in the repo yet, so that one bridge
lemma is conditional. The falsifiability check the issue actually asked for —
`K3.chi₂_eq_neg_mukaiPairing`, which pins the `(-1)ⁱ` sign convention — is proved and does not
depend on it. The cheapest instance would be `Examples/RankOneSurface`: `H ↦ −H` extends to
`ℚ[t]/(t³)` because `(−H)³ = 0`, and the grading is by the power basis.

## Layer B — the construction

| # | Stage | Estimate | Gate |
|---|---|---|---|
| B1 | Coherent category, locality, affine comparison, closure, abelian/exact inclusion | 2–3 months | [milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/4); kernels/cokernels complete, #9 then #10 |
| B2 | Invertible sheaves, `Pic X`, Cartier divisors, `O_X(D)`, determinant, effective-divisor sequence | 2–3 months | [milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/7); #21 ready, remainder gated |
| B3 | Affine vanishing, cohomology boundedness, geometric `χ`, additivity | 4–6 months | [milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/5); explicit affine Čech vanishing done; #27 ready, #28 blocked on #27; finiteness deferred, see below |
| B4 | Numerical polynomials, Snapper, intersections, numerical Chern data | ~3 months | [milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/9); #33 ready |
| B5 | Canonical sheaf, Serre duality, surface RR, dévissage, Layer A discharge | ~6 months | [milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/8); blocked on B2–B4 |

Total 18–30 months. Layer A exists so that nothing waits on this.

### Notes on individual stages

**B1.** Mathlib gives `X.Modules` abelian plus `IsFinitePresentation ⟹ IsQuasicoherent` and
`⟹ IsFiniteType` as instances. CohLean proves closure under isomorphisms, finite-presentation
locality, and the equivalence connecting slice restriction to scheme-level restriction along
an open immersion. The affine equivalence now feeds the completed kernel/cokernel closure.
Locality feeds the remaining extension closure, after which those closure results feed the
abelian/exact-inclusion assembly.

On the affine-local criterion (issue #12): Mathlib has
`SheafOfModules.QuasicoherentData.bind` and `IsQuasicoherent.of_coversTop`, so local-to-global
is done — **for quasicoherence only**. There is no finite-presentation analogue, and supplying
one is a real Mathlib gap rather than an unwrapping exercise. Note also that `M.over U` lives
on the site `Over U` with topology `J.over U`, so composing restrictions is a site
equivalence, not a triviality; `bind` handles it with `pushforwardPushforwardEquivalence`.
The full plan is on the issue.

Issue #11 is now done (`CohLean/Coh/Affine.lean`): `M^~` is of finite
presentation whenever `M` is, because `AlgebraicGeometry.presentationTilde` already builds
the global presentation and its index types are the two generating sets that
`Module.FinitePresentation` hands over. Conversely,
`ForMathlib/AffineComparisonGluing.lean` proves `IsIso M.fromTildeΓ` for quasi-coherent `M`,
and `ForMathlib/AffineComparisonFiniteness.lean` transports finite generators and
presentations to a basic-open cover and patches their localized global sections. Thus coherent
sheaves on `Spec R` have finitely presented global sections when `R` is noetherian.
`Coh.affineGlobalSections` and `FGModuleCat.affineTilde` restrict Mathlib's `tilde ⊣ Γ`
adjunction to the two full subcategories, and `Coh.affineEquivalence` packages the resulting
`Coh (Spec R) ≌ FGModuleCat R`. The global-sections restriction itself needs no noetherian
hypothesis; noetherianity first appears in the tilde direction.

One smaller Mathlib gap surfaced on the way and is discharged in
`CohLean/ForMathlib/OpensLimits.lean`: `Presentation.quasicoherentData` assumes
`[HasBinaryProducts C]` for the site, and that instance does not fire on `X.Opens`, because
`Opens` reaches its order twice over and instance search will not unfold the
`CompleteLattice.copy` that reconciles them. Without it a global presentation cannot be
turned into finite presentation on a scheme at all.

**B2.** Upstream Mathlib gained `AlgebraicGeometry/AlgebraicCycle/Basic.lean` (cycles as
locally-finite-support functions, proper pushforward) and `OrderOfVanishing.lean` after
v4.29.0. Neither defines divisors, rational equivalence or Chow groups yet. **Do not
duplicate that work** — bump the toolchain at B2 and build on it, or contribute there.

**B3.** The hardest step and the one everything else waits on. Mathlib's sheaf cohomology
is `Ext` from the constant sheaf, which is the right general definition but not obviously
the one that makes finiteness provable; expect to need Čech cohomology
(`CategoryTheory/Sites/SheafCohomology/Cech.lean`) and the affine vanishing theorem first.

Issue #26 settled how far that goes, and the answer split the stage.
`CohLean/Cohomology/Strategy.lean` records it in full; in one line, **B3 proves vanishing,
not finite-dimensionality.** The Čech route on a finite affine cover is supported — the
hypotheses are `IsNoetherian X` plus an affine diagonal, not properness and not a base
field — and it carries #13, #27, #28 and #30. Serre finiteness (#29) is not supported and
is not close: `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/` has no modules at all, no
graded-module-to-sheaf construction and no twisting sheaf, so the machinery `H^i(ℙⁿ, O(d))`
is stated in has to be built before the classical proof can begin. #31 and #32 therefore
carry finite-dimensionality as a hypothesis rather than deriving it, and become
unconditional unchanged the day #29 lands.

The bridge that carries a short exact sequence of `𝒪ₓ`-modules into `Ext` is done — #56 for
`SheafOfModules`, #59 for the `X.Modules` wrapper; use `Scheme.Modules.toSheaf`. The explicit
affine Čech vanishing chain is also done: #62 connects Mathlib's simplicial
`ExtraDegeneracy` theory to `alternatingCofaceMapComplex`, and
`CohLean/Cohomology/AffineCech.lean` contracts the complex after restriction to each member
of a finite distinguished-open cover and descends exactness along the spanning family. This
proves exactness of the explicit Čech complex in positive degrees; it deliberately does not
claim a comparison with derived-functor sheaf cohomology. Issue #27 supplies that comparison;
#28 is then the short derived-affine-vanishing corollary.

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
