# Handoff

Updated 2026-08-09 for the #22 branch, based on `a719258` (#77). For a session picking this
repo up cold.

Read §1 and §7. Everything else is reference.

> Revised 2026-08-08. The previous revision described issue #11 as the live work and Layer A
> as finished at A6; both have moved. **Several sessions work this clone concurrently** — the
> log below interleaves at least three — so treat any "current" claim here as a snapshot and
> check `git log origin/main` before trusting it. §12 is new and is about the machine, not
> the mathematics; read it before your first commit.

---

## 1. Sixty seconds

```bash
git clone git@github.com:chris-dare-dev/coherent-sheaves-lean.git
cd coherent-sheaves-lean
lake exe cache get      # ~5 min, downloads Mathlib oleans. A cache MISS is a real failure --
                        # building Mathlib from source takes hours.
lake build              # ~1 min warm
lake env lean scripts/Audit.lean
```

The audit must print `[propext, Classical.choice, Quot.sound]` on every line and never
`sorryAx`. There is no `sorry` in this library and there never has been.

**State after #22:** `lake build` completes 3271 jobs and 204 declarations are audited.
Every audit line uses only `[propext, Classical.choice, Quot.sound]`; there is no `sorryAx`.
Docs live at
<https://chris-dare-dev.github.io/coherent-sheaves-lean/>.

**Layer A is done through A8a** — the general RR expansion, the `n = 2/3/4` specialisations,
the K3 and Calabi–Yau-threefold cases, and the Euler pairing `χ(E,F)`. Only A8b (the numerical
lattice, #17) remains.

**Layer B stage B1 is complete.** It includes the affine-local criterion, closure under
isomorphism, the slice-equivalence transport, the affine comparison and equivalence, closure
under kernels, cokernels, and extensions, and finally the abelian structure on `Coh X` with
exact inclusion into `X.Modules`. B3 has explicit affine Čech exactness, but not yet the
comparison with derived-functor sheaf cohomology; geometric `χ` does not yet exist.

The live work is §7.

---

## 2. What this is

Coherent sheaves, Chern classes and Riemann–Roch for smooth projective varieties over a field,
in Lean 4 / Mathlib. As of August 2026 no proof assistant has any of it — the survey behind
that claim is in `README.md`, and it still holds.

Dimension-general throughout. Surfaces are the near-term target but nothing is stated only for
`n = 2`; threefolds and fourfolds are meant to be specialisations, not rewrites.

### Two layers, and why

**Layer A — `CohLean.Numerical`.** The numerical interface, as typeclasses, with no schemes
anywhere. `NumericalRing n A` is the intersection ring `A^•(X)_ℚ` graded by codimension with a
degree map in top codimension; `NumericalVariety n A N` adds `N(X)`, the Chern character by
graded components, the Todd class and `χ`, subject to Hirzebruch–Riemann–Roch.

Its fields are **axioms**. `hirzebruch_riemannRoch` in particular is assumed. That is the trust
boundary, it is visible in the type, and Layer B exists to discharge it. Nothing downstream may
treat those fields as proved, and no new axiom goes into Layer A without a line in `ROADMAP.md`
naming the Layer B stage that will discharge it.

**Layer B — `CohLean.Coh`.** The real construction from Mathlib's scheme theory.

### The design decision that makes Layer B tractable

**No Chow rings.** Intersection numbers come from Snapper's theorem: for proper `X` over a
field, `(n₁,…,n_r) ↦ χ(F ⊗ L₁^{n₁} ⊗ ⋯ ⊗ L_r^{n_r})` is a numerical polynomial, and
intersection numbers are its coefficients. So `c₁` is a Cartier divisor class, `D · D'` is a
polynomial coefficient, and `ch₂` is read off `χ`. No cycles, no rational equivalence, no Chow
group. (Kleiman's numerical-ampleness route; Bădescu, *Algebraic Surfaces*, ch. 1.)

If you find yourself about to build a Chow ring, stop and re-read this.

---

## 3. What is proved

### Layer A — complete and audited

| File | Content |
|---|---|
| `Numerical/Defs.lean` | `NumericalRing n A`, `NumericalVariety n A N` |
| `Numerical/RiemannRoch.lean` | `degree_ch_mul_todd` — the RR expansion, proved once **for all `n`** |
| `Numerical/Surface.lean` | `chi_eq` at `n = 2`, *derived* from the above; `discriminant`; `degree_discriminant` |
| `Numerical/Threefold.lean` | `chi_eq` at `n = 3`; `CalabiYauThreefold.IsCalabiYau` (`td₁ = 0`, `∫td₃ = 0`) and its two-term `chi_eq` |
| `Numerical/Fourfold.lean` | `chi_eq` at `n = 4` |
| `Numerical/K3.lean` | `IsK3` (asserts only `td₁ = 0` and `∫td₂ = 2`), `chi_eq`, Mukai self-pairing, `⟨v,v⟩ = ∫Δ − 2r²` |
| `Numerical/Dual.lean` | `NumericalRingWithDual` — the `(-1)ⁱ` involution, as a **mixin** over `NumericalRing`; `chDual`, `ch_add` |
| `Numerical/EulerPairing.lean` | `chi₂ E F = ∫ch(E)^∨·ch(F)·td(X)`, its general expansion, the `n = 2` case, and `K3.chi₂ = −⟨v,v⟩` |
| `Numerical/OfGradedBasis.lean` | `NumericalRing.ofGradedBasis` — builds the graded ring from a basis, discharging the internality obligation once |

`Surface.lean`, `Threefold.lean` and `Fourfold.lean` are the same proof with
`Finset.sum_range_succ` fired one and two more times. Nothing in `RiemannRoch.lean` changed to
admit them — that is the evidence `degree_ch_mul_todd` is dimension-general rather than a
surface theorem with a variable in it.

Two things about the Euler pairing that are easy to get wrong:

* **`chi₂` needs no `NumericalRingWithDual` instance.** `chDual` is the explicit alternating
  sum `Σᵢ (-1)ⁱchᵢ(E)`, which the grading alone supplies, so the pairing and every consequence
  work on any `NumericalVariety`. The involution appears in exactly one lemma,
  `chi₂_eq_degree_dual_ch`, which is what earns `chDual` its name. There is still **no
  instance** of the mixin in the repo, so that one bridge lemma is conditional; the sign
  convention is pinned independently by `K3.chi₂_eq_neg_mukaiPairing`.
* **`chi₂` is not symmetric**, and issue #6 asked for symmetry in even dimension.
  `Surface.chi₂_sub_chi₂_swap` measures the failure: `χ(E,F) − χ(F,E) = 2(r_E∫c₁(F)td₁ −
  r_F∫c₁(E)td₁)`, nonzero on `ℙ²`. Symmetry holds exactly when `td₁ = 0`. The general
  `χ(E,F) = (-1)ⁿχ(F,E)` is Serre duality — a B5 theorem about `Ext`, not an identity between
  these integrals. The correction is recorded on the issue.

Three models, so nothing is vacuous:

| Model | Why it exists |
|---|---|
| `Examples/Point.lean` | dimension zero; proves the axiom set is consistent |
| `Examples/K3Model.lean` | K3 of degree `H² = 2d`; `IsK3` is **proved**, not assumed |
| `Examples/ProjectivePlaneModel.lean` | `ℙ²`, and it earns its keep: `td₁ = (3/2)H ≠ 0`, so it tests the `c₁·td₁` term of `Surface.chi_eq` that the K3 model multiplies by zero. `p2Chi_lineBundle` recovers `χ(O(nH)) = (n+1)(n+2)/2` |

`Examples/RankOneSurface.lean` holds what the two surface models share — every Picard-rank-one
surface has the same ring `ℚ[t]/(t³)` up to the single number `∫H²`. A new rank-one model costs
a Todd class and nothing else.

### Layer B — coherent sheaves form an abelian category

> Everything in this subsection except `Coh/Defs.lean` and the two original `ForMathlib` files
> was written by **other sessions**. This table was checked against each file's module
> docstring, `scripts/Audit.lean`, and the commits that introduced them; the proofs themselves
> were not re-derived. Each of those docstrings has a "Not proved here" section and they are
> unusually precise — read the one for any file you build on.

| File | Content |
|---|---|
| `Coh/Defs.lean` | `IsCoherent` (= finite presentation; correct on locally noetherian schemes, documented as strictly stronger elsewhere), the `coherent` `ObjectProperty`, `Coh X`, the inclusion `ι` |
| `Coh/ClosedUnderIso.lean` | `Coh X` closed under isomorphism |
| `Coh/Local.lean` | the affine-local criterion: `isCoherent_iff_of_affineOpenCover`, and the `Over`-free `isCoherent_iff_restrict_affineOpenCover` |
| `Coh/Affine.lean` | finite presentation of `M^~`, finite global sections of finite-type quasi-coherent sheaves, finite presentation of global sections of coherent sheaves over a noetherian ring, and `Coh (Spec R) ≌ FGModuleCat R` |
| `AlgebraicGeometry/Modules/RestrictOver.lean` | the slice-vs-scheme restriction equivalence; finite presentation invariant in **both** directions |
| `ForMathlib/PresentationIsFinite.lean` | `Presentation.isFinite_of_isIso`, `Presentation.isFinite_map` |
| `ForMathlib/FinitePresentationOfPresentation.lean` | `Presentation.isFinitePresentation_quasicoherentData`, `IsFinitePresentation.of_presentation` |
| `ForMathlib/OpensLimits.lean` | `HasBinaryProducts` and `HasFiniteLimits` on `Opens X`. Mathlib's general lattice instances do not fire because `OrderTop (Opens X)` is unreachable at reducible transparency. **This file replaced two independent workarounds for the same gap** — do not write a third |
| `ForMathlib/AffineComparison.lean` | reduces `IsIso fromTildeΓ` to a statement about localisation of modules, and makes it an `iff` |
| `ForMathlib/QuasicoherentBasicOpen.lean` | refines quasi-coherent presentation data to a basic-open cover |
| `ForMathlib/AffineComparisonGluing.lean` | compatibility exports around Mathlib v4.32's upstream Hartshorne II.5.1 theorem, including `isIso_fromTildeΓ_of_isQuasicoherent` |
| `ForMathlib/AffineComparisonFiniteness.lean` | transports finite generators/presentations to basic opens and patches the localized finite modules |
| `ForMathlib/DivisorAPIAudit.lean` | compile-only B2 inventory: cycles/order of vanishing, local freeness, ring-level Picard data, sheafification, and ideal-sheaf subschemes; records the genuinely missing divisor layer |
| `Divisors/Cartier.lean` | Cartier divisors on an integral scheme as locally representable sections of `K(X)ˣ / 𝒪_{X,x}ˣ`; principal classes, order coefficients, and explicitly-hypothesized pullback |
| `Coh/Kernels.lean` | finite-limit preservation for restriction, localization through kernels, affine/global kernel and cokernel closure, and the two object-property closure instances |
| `Coh/Extensions.lean` | local lifting on two finite refinements and the finite horseshoe presentation proving closure under extensions, with no noetherian hypothesis |
| `Coh/Abelian.lean` | zero and finite-product closure, the abelian instance on `Coh X`, and the exact inclusion into `X.Modules` |
| `ForMathlib/ToSheafExact.lean` | `SheafOfModules.toSheaf` preserves finite colimits, hence epis and short exact sequences. Needed because `Sheaf.H` is `Ext` from the constant sheaf, so the cohomology long exact sequence runs on the *image* of a sequence in `Sheaf J AddCommGrpCat` — and nothing upstream said it survives the trip |
| `Cohomology/Strategy.lean` | **Proves nothing.** A compile-only API map of the upstream declarations B3 can build on: 0 theorems, 6 `example`s, deliberately built to break the day one of them moves. Records the #26 reconnaissance so it is not repeated |

The two original `ForMathlib` files fill a real Mathlib gap: Mathlib has
`IsQuasicoherent.of_coversTop` but **no finite-presentation analogue**, because nothing said
that transporting a presentation preserves `Presentation.IsFinite`. Both files are in Mathlib
namespaces so upstreaming is a file move.

**Still not proved:** geometric `χ`; the invertible-sheaf/`Pic X` and later parts of B2, all of B4, B5. General cohomology finiteness
remains deliberately deferred; the affine global-sections finiteness needed by B1 is proved.

---

## 4. Invariants — do not break these

1. **No `sorry`.** Work not done is written up as not done in the module docstring. There are
   no stubs and there should never be.
2. **Every new public theorem goes into `scripts/Audit.lean`.** CI fails on `sorryAx` and on any
   `declaration uses 'sorry'` warning. A green `lake build` proves nothing on its own — it
   succeeds on sorry-backed declarations.
3. **Mathlib-style namespaces** (`AlgebraicGeometry.*`, `SheafOfModules.*`), never `CohLean.*`,
   so upstreaming a stage is a file move rather than a rename.
4. **Toolchain pinned to `leanprover/lean4:v4.32.1`.** This is the B2 bump: v4.32.0 is the first
   stable release with both `AlgebraicCycle.Basic` and `OrderOfVanishing`. A downstream project
   cannot mix this with a v4.29 Mathlib graph. `bridgeland-stab-lean` still follows an upstream
   BridgelandStability commit pinned to v4.29.0, and no accessible `bstab` repository could be
   located during #21, so neither downstream pin was mutated here.

---

## 5. Working agreements

**Stage by path. Never `git add -A` or `git commit -a`.** More than one session works this
clone. This has already gone wrong once: commit `5317c4b`, whose message is about the
affine-local criterion, actually carries `CONTRIBUTING.md` and all of `docbuild/` — another
session's in-flight work, swept up by my `git add -A`. `/scratch/` is now gitignored so that
throwaway probes cannot be swept, but that only covers probes. Stage the files you touched.

**Probes go in `/scratch/`** and are ignored. Nothing there ships. A probe worth keeping belongs
in `CohLean/` with a docstring; a probe that was a dead end gets written up as prose in the file
it came from.

**Record dead ends in the file, not just in your head.** `PresentationIsFinite.lean` documents
what its failed retry ruled out. That is why the next attempt was cheap.

---

## 6. Where the work is

7 milestones, 27 open issues after this branch. Every issue names the exact file it creates, so `ready` issues can
be worked simultaneously without merge conflicts. `lakefile.toml` is the one genuinely shared
file — in practice `CohLean.lean`, `scripts/Audit.lean`, `ROADMAP.md` and `README.md` are
shared too, and they are where every merge conflict this project has had actually happened.

| Milestone | Open | Gist |
|---|---|---|
| A7 | 0 | **done** — threefold and fourfold RR |
| A8 | 1 | Euler pairing **done**; the numerical lattice (#17) remains |
| B1 | 0 | **done** — `Coh X` abelian with exact inclusion into `X.Modules` |
| B2 | 4 | Cartier divisors are done; `Pic X`, `O_X(D)`, determinant, and the effective-divisor sequence remain |
| B3 | 7 | Cohomology and `χ` — **still the real gate** |
| B4 | 5 | Snapper polynomials → intersection numbers |
| B5 | 7 | Serre duality → RR for surfaces → discharge `hirzebruch_riemannRoch` |

**In progress:** **#23**. **Startable after this branch merges:** **#33**. Issue #27 is already
in progress.
Regenerate this list with `gh issue list --label ready` before choosing,
because tracker labels move faster than this file.

There is no longer an easy pure-Layer-A warm-up: A7 and A8a took them. A fresh session should
expect to land in Layer B, where the cost is Mathlib plumbing rather than mathematics — read
§8 first, it is most of what that costs.

---

## 7. In flight

**B1 is complete. #22 supplies the first B2 construction.** `Divisors/Cartier.lean` defines
Cartier divisors on an integral scheme from the stalkwise quotients `K(X)ˣ / 𝒪_{X,x}ˣ`, proves
their abelian-group operations, packages principal equivalence, and descends `Scheme.ord` to
coefficients. It does not claim coefficient support is locally finite: upstream has no theorem
supporting that `AlgebraicCycle` packaging. Pullback is available precisely from explicit
function-field data preserving local units. #23 (invertible sheaves/`Pic X`) is in progress and
is the remaining input to #24 (`O_X(D)`).

Universe defaulting and iterated-slice elaboration are still the dominant implementation
hazards; the fixes are preserved in §8. The `Finset`/`Set` warning remains retracted.

**B3, and it is still the gate — but its scope shrank.** Commit `33bafa8` closed the #26
reconnaissance and **narrowed the milestone**: B3's roadmap line went from "cohomology
finiteness/boundedness" to "cohomology boundedness", with finiteness deferred. Read that
decision before planning anything here:

* The **Čech route on a finite affine cover is supported**, on `IsNoetherian X` plus an affine
  diagonal — *not* properness and *not* a base field. It carries #13, #27, #28, #30.
* **Serre finiteness (#29) is not supported and is not close.**
  `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/` has no modules at all — no
  graded-module-to-sheaf construction, no `O(d)`, no twist. The machinery `H^i(ℙⁿ, O(d))` is
  stated in has to be built first, which is a bigger job than B1.
* **#31 and #32 therefore carry finite-dimensionality as a hypothesis** rather than deriving
  it, and become unconditional unchanged the day #29 lands.

`Cohomology/Strategy.lean` records all of this and proves nothing; `scripts/Audit.lean` says
so in as many words. #13 (affine Čech vanishing) is done and #27 (Čech vs derived sheaf
cohomology) has an implementation in progress.

PR #58 ("The forgetful functor to abelian sheaves is exact", closed #56) landed as
`c349741` while an earlier revision was being written — a fair illustration of how fast `main`
moves here. Query the live PR list before choosing work; #27 is already marked in progress.
## 8. Gotchas — the expensive part of this repo's history

Each of these cost real time. None is recoverable from reading the code.

### Retracted — do not budget for this

**`Finset` vs `Set` in `presentationTilde` is NOT a problem.** Revisions of this document before
2026-08-08 said to budget for threading a coercion from `Module.FinitePresentation.out`'s
`s : Finset M` into `presentationTilde`'s `s : Set M`, and through `t`'s type as well. It is
accepted exactly as written. Two sessions prepared for a problem that does not exist.

### Instance resolution and universes

**A metavariable in an instance argument fails loudly and misleadingly.**
`Presentation.isFinite_map` is stated over a *second* sheaf of rings `S` on a second site `J'`.
Apply it without pinning `S` and `J'` stays a metavariable; Lean then tries to synthesise
`HasSheafify J' AddCommGrpCat` **against that metavariable** and fails outright rather than
postponing. The error names a missing `HasSheafify (J.over x) AddCommGrpCat` even though
`[∀ X, HasSheafify (J.over X) AddCommGrpCat]` is in scope and prints *identically* under
`pp.universes`. Fix: `exact Presentation.isFinite_map (S := R.over x) P _ _`.

This one hypothesis cost ten attempts, during which I wrongly blamed universe annotation,
section contamination, `variable` auto-inclusion, and `∀`-quantified instance binders — all four
disproved by a three-line probe. See §9.

**Universes default to `0` when nothing pins them.** Symptom is always a type mismatch at
`Type 1`, never an ambiguity. Annotate explicitly (`Foo.{u, u, u}`); named-argument pinning does
not work when the universes bind before the argument. Annotate in your own theorem's
**statement** too, not only at use sites — that is the easiest place to forget.

**`constructor`, not `refine ⟨…⟩`, for a universe-pinned structure goal.** Against a *ground*
`Presentation.IsFinite.{u,u,u} …` goal, `refine ⟨⟨?_⟩, ?_⟩` still elaborates at universe `0`,
and `refine Presentation.IsFinite.mk ?_ ?_` gets stuck synthesising
`WEqualsLocallyBijective ?J AddCommGrpCat` because the head elaborates before the goal unifies.
`constructor` unifies with the goal first and goes through. This is the second half of the
universe-defaulting fix and does not follow from the first.

**`variable` auto-inclusion drops instance binders whose type parameters do not appear in your
statement.** In a `ConcreteCategory` block, `FC` and `CC` often do not occur in the theorem you
are writing — so the `ConcreteCategory` and `forget`-preservation binders are silently dropped
along with them. The failure surfaces much later as an unsolved `Category` metavariable naming
nothing relevant. Write the binders out in the signature. (Note this is a *real* instance of the
mechanism disproved as a theory two items above; it does happen, just not there.)

**`Presheaf.stalkFunctor` forces the space universe to equal `C`'s hom universe.**
`{X : TopCat.{w}}` with `[Category.{v} C]` is unsolvable; it must be `{X : TopCat.{v}}`.

**`preservesColimitsOfSize_shrink` is not a global instance** — it loops. `pushforward (𝟙 _)` is
a left adjoint (`Sheaf/PushforwardContinuous.lean:275`) but only at its own hom universe, so
supply `haveI : PreservesColimitsOfSize.{u, u} … := preservesColimitsOfSize_shrink _` by hand.

**`choose D hD using …`, not `have D := (…).choose`.** With `have`, `D i` is opaque and
`choose_spec` types against `_.choose` rather than `D i` — an error with nothing to do with your
actual problem.

### The `Opens` transparency gap — why `ForMathlib/OpensLimits.lean` exists

`TopologicalSpace.Opens X` reaches its order twice: through the bespoke `SetLike`-derived
`PartialOrder`, and through the `CompleteLattice.copy` built to be *definitionally* equal to it.
Instance search unifies at reducible transparency, where the copy does not unfold — so
**`OrderTop (Opens X)` and `BoundedOrder (Opens X)` do not synthesise**, even though
`CompleteLattice`, `Order.Frame`, `SemilatticeInf`, `Lattice` and `Top` all do.

Everything in `CategoryTheory.Limits.CompleteLattice` sits above `OrderTop`, so no limit instance
on the site `X.Opens` is reachable by default — and without one, a global presentation cannot
become finite presentation on *any* scheme. Mathlib never instantiates
`Presentation.quasicoherentData` at a scheme site, which is why this has not surfaced upstream.

Two sessions hit it and worked around it differently — five workarounds for one gap — before
`ForMathlib/OpensLimits.lean` consolidated them (#51). **Do not add a global `OrderTop`
instance:** `OrderTop` extends `Top`, `Opens` already has one, and that is a data-carrying
diamond that could change which `Top` existing `simp` lemmas are stated against. The bridges in
that file are `private` for exactly that reason, and there is a regression check worth keeping —
**`OrderTop (Opens X)` must still fail to synthesise.**

Expect the shape again; it is not specific to `Opens`.

### Elaboration

**Dependent `Fin` rewrites fail.** You cannot `rw [pb_dim]` inside a hypothesis mentioning
`i : Fin pb.dim` — the motive does not typecheck. Feed the equation to `omega` as a fact about
naturals instead: `have hd := pb_dim; omega`.

**`letI` in a theorem *statement* is zeta-reduced away.** Re-establish the instance in the
tactic block: `letI := k3NumericalVariety d hd` as the first line of the proof.

**`omit [Inst] in` goes before the docstring**, not between the docstring and the theorem.

**A `def` whose type is a class needs `@[reducible]`**, or instance search cannot see through it.

**`rw` only closes goals by `rfl` at reducible transparency.** After unfolding a
pattern-matching `def`, an explicit `rfl` is often needed.

**Dot notation does not fire through a `def`-wrapped type.** `tilde N`'s inferred head symbol is
`SheafOfModules`, not `Scheme.Modules`, so `(tilde N).basicOpenRestriction` fails even though the
namespace is right. It works for terms *declared* at type `(Spec R).Modules`. Issue #59 exists to
address this.

**A dependent rewrite across a change of ambient category is far easier as a `subst`.** When a
`Presentation` must move between `(M.restrict f).over U` for two propositionally-equal `U`, do
not rewrite at the use site — the ambient category depends on `U`. Take the equality as a
hypothesis in a helper lemma and `subst` it there, once. That is the whole technique behind
`Scheme.Hom.presentationOverOfEq`.

### Mathlib specifics at v4.32.1

* The exact B2 inventory is executable in `ForMathlib/DivisorAPIAudit.lean`. Upstream has
  `AlgebraicCycle`, `AlgebraicCycle.map`, `Scheme.ordHom`, `Scheme.ord`, arbitrary-rank
  `SheafOfModules.IsLocallyFree`, ring-level `Module.Invertible` and `CommRing.Pic`, generic
  `PresheafOfModules.sheafification`, and `Scheme.IdealSheafData.subscheme`. It does **not**
  have scheme-level invertible sheaves/`Pic X`, sheaf tensor products, Cartier divisors,
  effective Cartier divisors, or `O_X(D)`.
* Mathlib v4.32 upstreamed `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`. The old
  800-line local Hartshorne II.5.1 proof was replaced by a small compatibility module. Prefer
  the upstream theorem; do not resurrect the old gluing machinery.

* Mathlib has **no** "f.p. + f.p. ⟹ f.p. in a short exact sequence". The usable statement is
  `Module.finitePresentation_of_ker`.
* For "epi ⟹ locally surjective", `Sheaf.isLocallySurjective_iff_epi` in
  `Sites/LocallySurjective.lean` is the prominent one but covers **sheaves of types only**. The
  general version is `Sheaf.isLocallySurjective_iff_epi'`, in `Sites/EpiMono.lean`, and its
  `Balanced (Sheaf J A)` hypothesis does not synthesise on its own.
* It is `Module.Basis`, not `Basis`.
* `Submodule` lives in `Mathlib.Algebra.Module.Submodule.Basic`; `DirectSum.IsInternal` in
  `Algebra/DirectSum/Basic.lean`; the `iSupIndep`-and-`iSup = ⊤` characterisation in
  `Algebra/DirectSum/Module.lean`.
* `LinearIndependent.disjoint_span_image` handles **blocks**, not just single vectors. That is
  why `ofGradedBasis` supports non-injective weights, which is what makes Picard rank > 1
  reachable. Do not restrict to injective weights.
* `simp` is the wrong tool near `PowerBasis`: `coe_basis` fires first and rewrites `basis i` to
  `gen ^ i`, after which `Basis.repr_self` no longer matches. Rewrite by hand.
* **`→ₐ[ℚ]` needs `Mathlib.Algebra.Algebra.Hom`.** `Numerical/Defs.lean` imports
  `Mathlib.Algebra.Algebra.Rat`, which does not carry the notation. The error is
  `expected token` pointing at the arrow, and every field of the class then reports as an
  unknown identifier — four cascading errors from one missing import.

### The A7/A8 additions cost these four (2026-08-08)

* **`norm_num` destroys `algebraMap`.** Expanding `chi₂` at `n = 2` needs
  `degree (algebraMap ℚ A q * x * y) = q * degree (x * y)`. `norm_num` rewrites
  `algebraMap ℚ A ↑(rank E)` into a plain cast, after which no `degree_algebraMap_*` lemma
  matches and `ring` cannot finish. Use `simp only` with an explicit lemma list. The same
  caution applies anywhere `algebraMap` meets a numeric tactic.
* **`simp only` will not reduce `n - i - j` for you at the point you need it.** In the same
  proof the Todd index stayed `2 - 0 - 2` while `toddComp_zero` was in the simp set, so the
  rewrite silently did nothing and the lemma reported as unused. Reduce the indices first with
  the repo's existing idiom, `show (2 : ℕ) - 0 - 2 = 0 from rfl` — the same one `Surface.chi_eq`
  uses. A "this simp argument is unused" warning next to a term that visibly matches means the
  term is not yet in the shape you think it is.
* **Prefer a truncated `Finset.range` to a summand guarded by `if`.** `chi₂_eq_sum` was first
  written as `∑ i ∈ range (n+1), ∑ j ∈ range (n+1), if i + j ≤ n then … else 0`. Specialising it
  then required reducing nine `if`s, and `rw [if_pos …]` only rewrites the occurrences sharing
  one instantiation, so they came out piecemeal. Restating the inner sum over `range (n + 1 - i)`
  removed the `if` entirely and made the `n = 2` case pure `Finset.sum_range_succ`. Widening the
  range back for the proof is one `Finset.sum_subset`.
* **`omega` is not always the cheapest route to a `Finset.range` subset.** `Finset.range_subset`
  resolved to something whose `.mpr` wanted `∀ x < m, x ∈ range n`, not `m ≤ n`, and a `by omega`
  in that position failed with a counterexample naming `n + 1 - i` as an opaque atom. An explicit
  `fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.sub_le _ _))`
  is shorter than diagnosing it.

### Modelling

**`χ` must land in `ℤ`, and that constrains the lattice.** On a K3 this forces the degree
parameter `d` to be a natural number. On `ℙ²` it is sharper: `ch₂ = (c₁² − 2c₂)/2` is a
half-integer whenever `c₁` is odd, so `N` cannot be `ℤ³` with `ch₂` third. The numerical
Grothendieck group is the sublattice where `3c₁ + 2ch₂` is even; substituting `2ch₂ = c₁ + 2v`
reparametrises it by `ℤ³`, and the `ℙ²` model uses those coordinates.

**A model that cannot detect a bug is not a test.** The K3 model has `td₁ = 0` and so multiplies
the `c₁·td₁` term of `Surface.chi_eq` by zero. That is precisely why `ℙ²` exists in the repo.
When you add a model, ask what it can falsify.

### Tooling

* `gh issue comment --body "…"` in bash **command-substitutes backticks**. Use `--body-file`
  with a quoted heredoc (`<<'EOF'`).
* `gh api /repos/…` on Git Bash gets its path rewritten to a Windows path. Omit the leading
  slash: `gh api repos/…`.
* **A probe importing a repo module reads the olean, not your edited source.** Run
  `lake build <Module>` before the probe, or you will debug a stale definition.
* **`gh pr merge` can return 502 and still not have merged**, then hold a stale "merge already in
  progress" lock for several minutes. Confirm against `origin/main`; trust neither the error nor
  its absence.

---

## 9. One process lesson, because it repeated

The pattern that cost the most time: **an error message named something other than the cause,
and I reasoned from the message instead of probing.**

Concretely — `HasSheafify (J.over x) AddCommGrpCat` "missing" while literally in scope. I
produced four theories and tested each by editing the real file and rebuilding: ~4 iterations,
all wrong. Then I wrote this:

```lean
example {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    [hsh : ∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    (x : C) : HasSheafify (J.over x) AddCommGrpCat.{u} := by infer_instance
```

It succeeded, which killed three theories at once and left unification order as the only
survivor — and that was the answer. The probe took two minutes.

**Write the minimal probe first.** If an error claims something is missing that you can see is
present, the error is about *when* Lean looked, not *what* it found.

---

## 10. Suggested order

> This order is a snapshot. Re-check tracker labels before starting.

1. **#23** — invertible sheaves and `Pic X`, building the missing scheme layer over
   `SheafOfModules.IsLocallyFree` and the ring-level Picard API. It is independent of #22.
2. **#33** — multivariable numerical polynomials and finite differences, the independent B4
   entry point.

Issue #27 (Čech versus derived sheaf cohomology) already has an implementation in progress.

A **rank-one model for a Calabi–Yau threefold** is not an issue yet — which today makes it
the only unblocked Layer A task, since #17 is labelled `blocked`. It is also cheap: `ℚ[t]/(t⁴)` with `∫t³ = d` via `NumericalRing.ofGradedBasis`, exactly
as `Examples/RankOneSurface.lean` does it. It would make `CalabiYauThreefold.IsCalabiYau`
non-vacuous, and a `NumericalRingWithDual` instance (`H ↦ −H`, valid since `(−H)⁴ = 0`) falls
out of the same file — which is the one thing keeping `chi₂_eq_degree_dual_ch` conditional.

## 11. Related repos

Same machine, `Source Code/`:

* `bridgeland-stab-lean` — the consumer. `Stab(D)` group actions, metric, HN polygons. Its
  current BridgelandStability anchor pins Lean/Mathlib v4.29.0; the anchor and consumer must
  both migrate to v4.32.1 before it can `require` this CohLean revision.
* `bstab` — named in older handoffs as the Bridgeland deformation-theorem project, but it was
  not present locally or discoverable among repositories accessible to the authenticated
  GitHub account during #21. If restored, its required pin is Lean/Mathlib v4.32.1.
* `stability-mflds` — Python, exact arithmetic: DLP curve, Bogomolov–Gieseker, Bridgeland walls,
  **K3 Mukai lattice**. Useful as an oracle: `mukai.py` computes the same pairing that
  `Numerical/K3.lean` states, so numeric cross-checks are cheap and worth adding to new models.

---

## 12. The machine, not the mathematics

This clone lives inside an Obsidian vault, and the vault's tooling writes to it. None of the
following is about Lean, and all of it will confuse you if you meet it cold.

**`README.md`, `CLAUDE.md`, `HANDOFF.md`, `plans/**` and `docs/**` carry YAML frontmatter in
the working tree that git does not store.** A machine-global `obsidian-strip` clean filter
(`~/.config/git/attributes` + `filter.obsidian-strip.*` in global config) removes it on the way
into a blob. This is deliberate: Obsidian needs the metadata, git should not carry it.

* **Never hand-strip it and never commit it.** If you see `project:` / `type:` /
  `authorship:` at the top of a tracked doc, that is the intended working-tree state.
* **`git status` can report ` M` on those files while `git diff` shows nothing.** `git diff` is
  the truth — it runs the filter. A stale entry is cleared with `git add --renormalize -- <paths>`,
  scoped to the files in question, never `.` (a bare renormalize will stage any real edit
  another session has in flight).
* **A tracked blob must never contain that frontmatter.** As of 2026-08-08 none in this repo
  does. If one ever does again, the fix is to normalise the *blob* and leave the worktree
  alone: `git cat-file -p HEAD:<f> | python ~/.config/git/strip-obsidian-frontmatter.py |
  git hash-object -w --stdin`, then `git update-index --cacheinfo <mode>,<sha>,<f>`. Do **not**
  `git add --renormalize` the file, which would also stage whatever else is uncommitted in it.

**Worktrees are the right way to work here, and they are now safe.** The shared clone is used
by several sessions at once and its `HEAD` moves without warning — during one session it changed
branch three times mid-task. Prefer:

```bash
git worktree add ../coherent-sheaves-lean-<topic>-worktree -b agent/<topic> main
```

Junction `.lake/packages` from the main clone into the new worktree (Windows:
`New-Item -ItemType Junction`) and `lake build` reuses the Mathlib oleans instead of re-cloning
~2 GB. Keep `.lake/build` per-worktree so two sessions cannot clobber each other's artifacts.

> **If you do that, you MUST delete the junction before removing the worktree.**
> `git worktree remove` follows a Windows junction and deletes the **target's** contents —
> the main clone's `.lake/packages` — while leaving the target directory itself in place. It
> exits 0 and prints nothing. Reproduced deliberately on 2026-08-08 in a throwaway repo: target
> 2 files before, 0 after, `exit 0`, no output.
>
> This is not hypothetical here. It happened: removing the `-a8-worktree` emptied the shared
> packages for **every** checkout pointing at it, and the next session's `lake` run failed with
> `mathlib: URL has changed` then `git exited with code 128` — symptoms, not the cause. Recovery
> was `lake exe cache get` (~84 s, the compressed store survived, so nothing re-downloaded).
>
> ```bash
> # before EVERY `git worktree remove` on a junctioned worktree:
> powershell -c "(Get-Item '<wt>/.lake/packages' -Force).LinkType"   # 'Junction' = danger
> powershell -c "(Get-Item '<wt>/.lake/packages' -Force).Delete()"   # removes the link only
> git worktree remove <wt>
> ```
>
> Note `.lake/build` is safe — it is per-worktree and never junctioned.

Until 2026-08-08 the vault indexer treated each sibling worktree as its own *project*, stamping
`project: coherent-sheaves-lean-a7-worktree` and minting a bogus hub note. That is fixed
(`<vault>/.obsidian/vault_paths.py` detects a linked worktree structurally), so worktrees are no
longer indexed at all. If you see a worktree-named project reappear in the vault, that fix
regressed.

**Merge conflicts here are always in the same four files** — `CohLean.lean`,
`scripts/Audit.lean`, `ROADMAP.md`, `README.md`. Keep your hunks small and localised in them and
`git rebase origin/main` stays a two-minute job. Everything else in the repo is per-issue by
design. They are append-only in practice, so conflict resolution is always "keep both sides";
and merging any one PR makes every other open PR conflict, so rebase them one at a time and
rebuild each.

**If you are not in a worktree, you will meet these three situations. The fixes:**

* **A shared file already carries another session's uncommitted edits and you need to commit only
  yours.** Write your changes, then stage a patch containing *only* your hunks:
  `git apply --cached --recount <your.patch>`. The working tree is never touched, so the other
  session notices nothing. Verify with `git diff --cached` before committing.
* **`git checkout <branch>` refuses because a shared file differs between the branches.** Back the
  file up outside the repo, `git checkout -- <file>` to restore it to `HEAD`, switch, then write
  the backup back. Confirm with `md5sum` that you restored it byte-identically. Do **not** force
  the checkout — that discards whatever the other session had in flight.
* **You are about to edit a shared prose file.** Check whether someone is mid-write first:
  compare `stat -c %Y <file>` across a 60–90 second window. This document was being rewritten by
  another session while these very paragraphs were being added.
