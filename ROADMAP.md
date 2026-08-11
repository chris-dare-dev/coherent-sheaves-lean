# Roadmap

Work is tracked as [milestones and issues](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues).
Every issue names the exact file it creates, so issues labelled `ready` can be picked up
simultaneously without merge conflicts. `lakefile.toml` is the one shared file — coordinate
before touching it. The live dependency graph is recorded in each milestone description;
`ready` and `blocked` are mutually exclusive, while `in-progress` means an implementation or
pull request already exists.

Issue [#22](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/22) supplies the
Cartier-divisor foundation. [#23](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/23)
and #79 supply the symmetric-monoidal Picard-group foundation, and
[#24](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/24) supplies `O_X(D)` and
the class-group map to `Pic X`, and #25 supplies effective Cartier divisors and their
fundamental exact sequences. Issue #36 supplies determinant lines and first Chern classes,
completing B2;
[#33](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/33) supplies the independent
multivariable numerical-polynomial algebra for B4, and
[#34](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/34) connects it to Picard
powers and Euler characteristics through explicit exact-sequence induction data.
[Issue #35](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/35) extracts symmetric
multilinear Picard and Cartier-divisor intersection numbers from those coefficients.
Issue #27 supplies the Čech-to-derived comparison; #28 is the next B3 step, deriving affine
vanishing from that comparison and the explicit affine Čech theorem.


Target: Riemann–Roch for smooth projective varieties over a field, general dimension,
with K3 surfaces as the first worked instance and threefolds/fourfolds as the reason the
whole development is dimension-general.

Estimates assume heavy agent assistance. A solo human should multiply by roughly three.

## Layer A — the numerical interface

| # | Item | Status |
|---|---|---|
| A1 | `NumericalRing n A`, `NumericalVariety n A N` | **done** |
| A2 | `degree_ch_mul_todd` — the general RR expansion, any `n` | **done** |
| A2a | universal `ChernClassData` conversions to `ch₀…ch₄` and `td₀…td₄` | **done** |
| A2b | `Variety.NumericalData`: certified coherent-sheaf/Chern-class descent to `NumericalVariety` | **done** |
| A3 | optional low-dimensional RR displays in `Numerical/Specializations` | **done** |
| A4 | dimension-general `NumericalVariety.discriminant` — `Δ = c₁² − 2r·ch₂` | **done** |
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

A7 cashes the dimension-general claim. The optional `Threefold.chi_eq` and `Fourfold.chi_eq`
displays are the same proof as `Surface.chi_eq` with `Finset.sum_range_succ` fired one and two
more times; no lemma in `Numerical/RiemannRoch.lean` had to change. They live under
`Numerical/Specializations` and are not part of the root import.

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
| B1 | Coherent category, locality, affine comparison, closure, abelian/exact inclusion | 2–3 months | **done** ([milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/4)) |
| B2 | Invertible sheaves, `Pic X`, Cartier divisors, `O_X(D)`, determinant, effective-divisor sequence | 2–3 months | **done** ([milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/7)) |
| B3 | Affine vanishing, cohomology boundedness, geometric `χ`, additivity | 4–6 months | [milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/5); explicit affine Čech vanishing and comparison infrastructure done; conditional geometric `χ` (#31) and additivity/K₀ factorization (#32) done; Serre finiteness and scalar-linearity of connecting maps remain explicit inputs |
| B4 | Numerical polynomials, Snapper, intersections, numerical Chern data | ~3 months | [milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/9); #33–#35 and the surface/general numerical Chern layers #37–#38 implemented with explicit geometric and pairing certificates |
| B5 | Canonical sheaf, Serre duality, surface RR, dévissage, Layer A discharge | ~6 months | [milestone](https://github.com/chris-dare-dev/coherent-sheaves-lean/milestone/8); blocked on B2–B4 |

Total 18–30 months. Layer A exists so that nothing waits on this.

### Notes on individual stages

**B1.** Mathlib gives `X.Modules` abelian plus `IsFinitePresentation ⟹ IsQuasicoherent` and
`⟹ IsFiniteType` as instances. CohLean proves closure under isomorphisms, finite-presentation
locality, and the equivalence connecting slice restriction to scheme-level restriction along
an open immersion. The affine equivalence now feeds the completed kernel/cokernel closure.
Locality feeds extension closure via two finite refinements carrying local lifts of generators
and relations. Together with kernel/cokernel closure, this gives the abelian structure and the
exact inclusion `Coh X ⟶ X.Modules`.

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
Mathlib v4.32 proves `IsIso M.fromTildeΓ` for quasi-coherent `M`, with
`AlgebraicGeometry/Modules/AffineComparisonGluing.lean` retaining CohLean's compatibility
exports, and `AlgebraicGeometry/Modules/AffineComparisonFiniteness.lean` transports finite generators and
presentations to a basic-open cover and patches their localized global sections. Thus coherent
sheaves on `Spec R` have finitely presented global sections when `R` is noetherian.
`Coh.affineGlobalSections` and `FGModuleCat.affineTilde` restrict Mathlib's `tilde ⊣ Γ`
adjunction to the two full subcategories, and `Coh.affineEquivalence` packages the resulting
`Coh (Spec R) ≌ FGModuleCat R`. The global-sections restriction itself needs no noetherian
hypothesis; noetherianity first appears in the tilde direction.

One smaller Mathlib gap surfaced on the way and is discharged in
`CohLean/Topology/Opens/Limits.lean`: `Presentation.quasicoherentData` assumes
`[HasBinaryProducts C]` for the site, and that instance does not fire on `X.Opens`, because
`Opens` reaches its order twice over and instance search will not unfold the
`CompleteLattice.copy` that reconciles them. Without it a global presentation cannot be
turned into finite presentation on a scheme at all.

**B2.** Issue #21 moved CohLean to Lean/Mathlib v4.32.1; v4.32.0 was the first stable release
containing both `AlgebraicGeometry/AlgebraicCycle/Basic.lean` and
`AlgebraicGeometry/OrderOfVanishing.lean`. The compile-only inventory is
`CohLean/Development/DivisorAPIAudit.lean`.

The usable upstream layer is precise: `AlgebraicCycle` and `AlgebraicCycle.map` supply locally
finite cycles and quasicompact pushforward; `Scheme.ordHom` and `Scheme.ord` supply order of
vanishing; `SheafOfModules.IsLocallyFree` supplies arbitrary-rank local freeness; and
`Module.Invertible`/`CommRing.Pic` supply the affine ring-level Picard API. Generic
`PresheafOfModules.sheafification` and `Scheme.IdealSheafData.subscheme` are construction
machinery. Mathlib still has no scheme rank-one/invertible-sheaf predicate, tensor product on
`SheafOfModules`, scheme Picard group, effective Cartier divisors, or `O_X(D)`.

Issue #22 fills the Cartier-divisor gap for integral schemes. `Scheme.CartierDivisor X` is the
abelian group of locally representable sections of the stalkwise quotient
`K(X)ˣ / 𝒪_{X,x}ˣ`; principal equivalence is an explicit quotient, and Mathlib's `Scheme.ord`
descends to codimension-one coefficients. Pullback requires explicit function-field data that
carries local units to local units, since upstream constructs no such map for an arbitrary
scheme morphism. Local finiteness of coefficient support is not upstream, so the coefficient
function is deliberately not repackaged as an `AlgebraicCycle`.

The completed #23/#79 construction defines invertibility as local rank-one freeness, transports
it across isomorphisms, constructs the sheafification of the presheaf tensor, and proves the
rank-one tensor/sheafification comparisons needed for closure. It installs the symmetric
monoidal coherence on invertible sheaves and packages the units of their isomorphism-class
commutative monoid as the scheme-level group `Pic X`. An explicit tensor-inverse constructor is
exported for the forthcoming `O_X(D)`/`O_X(-D)` pair. Together with #22, this unlocks #24.

Issue #24 constructs the intrinsic fractional presheaf generated by inverse local equations and
defines `O_X(D)` by module sheafification. Every local equation trivializes it; changes of
equation satisfy the transition cocycle law. Multiplication of rational sections gives the
canonical `O_X(D) ⊗ O_X(E) ≅ O_X(D + E)`, global equations trivialize principal divisors,
and `O_X(-D)` supplies the explicit inverse used to descend from Cartier divisor classes to
`Pic X`. No unconditional pullback comparison is claimed: the divisor pullback data from #22
does not yet include compatibility with rational sections and module-sheaf pullback.

Issue #25 defines an effective Cartier divisor by a Cartier divisor, its ideal-sheaf closed
subscheme, and an identification of `O_X(-D)` with that ideal. The resulting
`O_X(-D) → O_X → i_* O_D` is short exact in `X.Modules` and lifts to `Coh X` under
explicit coherence hypotheses. Tensoring by an invertible sheaf is proved exact as a reusable
intermediate result, giving the normalized short exact sequence
`O_X(E-D) → O_X(E) → O_X(E) ⊗ i_* O_D` and its coherent lift.

Issue #36 records the actual algebraic top exterior power of a free rank-`n` module and packages
fixed-rank locally free atlases with chosen descended determinant lines. Mathlib has no
exterior-power construction for sheaves of modules, so the global descent and the determinant
comparisons for direct sums and short exact sequences are explicit data rather than hidden
existence assumptions. They produce isomorphism-invariant first Chern classes in `Pic X` and
additivity in its additive notation. Coherent objects are covered only when their underlying
sheaves carry finite locally free determinant data or an explicit two-term finite locally free
resolution; no global resolution theorem for arbitrary coherent sheaves is asserted.

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
unconditional unchanged the day #29 lands. Issue #31 is now implemented in
`CohLean/Cohomology/EulerCharacteristic.lean`: it uses a functorial `ModuleCat k` lift of the
actual `Sheaf.H` groups, proves finite support from the supplied vanishing bound, and exposes
the ordinary finite alternating sum. Issue #32 is now implemented in
`CohLean/Cohomology/EulerCharacteristicAdditivity.lean`: exactness is transported from the
actual `Ext` sequence, bounded alternating dimensions cancel, and `χ` descends explicitly to
`K₀(Coh X)`. Mathlib exposes the connecting maps only additively, so their base-field
linearity is isolated as `LinearConnectingMaps`, never assumed as an axiom.

Issue #57 is now the active umbrella for filling that Proj gap. Its first slice (#94) constructs
degree-zero homogeneous localization of a graded module over Mathlib's existing
`HomogeneousLocalization` ring, reusing `LocalizedModule` rather than introducing another
fraction relation. The remaining dependency order is: associated graded-module sheaves (#95),
graded shifts and `O(d)` (#96), then quasi-coherence/coherence and sections (#97). Natural and
integer gradings remain explicitly distinct until the shift layer supplies their comparison.

The bridge that carries a short exact sequence of `𝒪ₓ`-modules into `Ext` is done — #56 for
`SheafOfModules`, #59 for the `X.Modules` wrapper; use `Scheme.Modules.toSheaf`. The explicit
affine Čech vanishing chain is also done: #62 connects Mathlib's simplicial
`ExtraDegeneracy` theory to `alternatingCofaceMapComplex`, and
`CohLean/Cohomology/AffineCech.lean` contracts the complex after restriction to each member
of a finite distinguished-open cover and descends exactness along the spanning family. This
proves exactness of the explicit Čech complex in positive degrees; it deliberately does not
claim a comparison with derived-functor sheaf cohomology. Issue #27 now supplies that comparison
in `CohLean/Cohomology/CechGlobalComparison.lean`: the global-sections augmentation is exact on
injectives, its bicomplex totalization is a quasi-isomorphism, and an acyclic-cover hypothesis
identifies Čech cohomology with `Sheaf.H`. #28 is then the short derived-affine-vanishing
corollary.

**B4.** Snapper's theorem is dimension-general, so B4 serves threefolds and fourfolds at no
extra cost. Issue #33 audits `jjaassoonn/DimensionTheory` and Mathlib, reuses Mathlib's current
univariate `ForwardDiff` API, and adds the missing arbitrary-rank mixed-difference layer in
`CohLean/Intersection/NumericalPolynomial.lean`. DimensionTheory remains useful design precedent
for integer-valued Hilbert polynomials, but is not a direct dependency: its relevant API is
univariate and pinned to a different Mathlib commit. Issue #34 is implemented in
`CohLean/Intersection/Snapper.lean`: integer powers are formed in `Pic X`, simultaneous twists
are dimension-general and multivariable, and Euler additivity turns each genuine short exact
induction step into a forward difference. The resulting `snapper` theorem, its ordinary
one-variable specialization, isomorphism invariance, and coefficient formulas are proved from a
visible `GeometricInduction` certificate. The certificate isolates the geometric
dimension/hyperplane-section theorem that Mathlib and the current scheme layer do not yet expose;
it is data, not an axiom, and can later be constructed without changing the downstream API.

Issue #35 is implemented in `CohLean/Intersection/Number.lean`. A uniform `TwistContext` keeps
coherence and geometric-induction certificates explicit for every finite Picard family, and its
structure-sheaf specialization defines intersections as top Snapper coefficients. The intrinsic
Picard finite-difference form proves symmetry, tensor-product additivity, integer homogeneity,
principal-divisor invariance, and the point/curve/surface normalizations without Chow groups.

Issue #37 is implemented in `CohLean/Intersection/ChernCharacterSurface.lean`. For a coherent
sheaf carrying explicit two-term perfect determinant data it extracts the virtual rank and
Picard-valued `c₁`; the surface intersection pairing turns `c₁` into its numerical functional.
The polarized structure-sheaf Euler polynomial constructs `td₁ · D`, while `χ(O_X)` supplies
the degree of `td₂`, so the degree of `ch₂(F)` is recovered from `χ(F)`. Isomorphism
invariance, short-exact additivity under a visible virtual-rank hypothesis, the structure-sheaf
and line-bundle cases, and compatibility with the Layer A discriminant degree are proved. The
output intentionally remains degree-level in codimension two: lifting it to a class in a chosen
numerical ring requires the explicit representability/nondegeneracy input tracked by #38.

Issue #38 is implemented in `CohLean/Intersection/ChernCharacter.lean`. Mixed twist
coefficients below top degree are first decontaminated by rational interpolation in a common
scaling variable. A `PairingContext` then separates representability from the explicit
nondegeneracy statement that divisor products distinguish the selected graded piece.
`ReconstructionData` represents the resulting Todd-weighted functionals, and the triangular
identity `τ = ch·td` reconstructs `ch₀` through `ch₄`. Grading, dimension truncation,
isomorphism comparison, exact-sequence additivity, the conditional line-bundle exponential,
and the degree-level surface comparison are proved. The API deliberately makes no unconditional
claim that divisor pairings recover every middle-codimension class on every variety.

**B5.** Serre duality is the second hard theorem. Mathlib's derived-category infrastructure
(Riou) is unusually strong and is the reason this is attemptable at all.

## Ownership and Mathlib interaction

CohLean owns every module in this roadmap. Mathlib-style namespaces record mathematical API
ownership, not a promise to upstream. Contributions to Mathlib are optional; when Mathlib gains
an equivalent API independently, adopting it and deleting the local compatibility code is also
optional maintenance work, never a gate for the next CohLean milestone.

## Non-goals

* Non-noetherian schemes. `IsCoherent` is defined as finite presentation, which is
  correct on locally noetherian schemes and strictly stronger elsewhere. Recorded in
  `CohLean/Coh/Defs.lean`.
* Chow rings, rational equivalence, and topological Chern classes. See the Snapper note in
  the README.
* Analytic or transcendental methods. Everything here is algebraic, over an arbitrary
  field unless a statement demands otherwise.
