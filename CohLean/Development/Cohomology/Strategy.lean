/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import CohLean.AlgebraicGeometry.Proj.Modules.Finiteness

/-!
# Layer B stage 3 — which cohomology finiteness theorem this library will prove

**This file proves nothing.** It is a compile-only API map recording the decision taken in
issue #26, and it exists so that the next session can start the finiteness proof without
repeating the reconnaissance. Every declaration below is an `example` naming an upstream
declaration, so the file fails to build the day one of them moves — which is the only
reason to keep it. Delete it once the decision is encoded in real theorem statements.

## The question

The project milestones target smooth projective varieties over a field, while this strategy was written
promising cohomology finiteness for all **proper** schemes over a field. Those are not the
same theorem and they do not cost the same. This file decides which one is supportable on
`leanprover/lean4:v4.29.0` with the pinned Mathlib, and fixes the hypotheses that appear in
each downstream statement.

## What is upstream, precisely

*Sheaf cohomology exists, with almost no API.* `CategoryTheory.Sheaf.H F n` is defined as
`Ext` from the constant sheaf `ULift ℤ` in
`Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`. It occurs in exactly two Mathlib
files — that one and `MayerVietoris.lean`. There is no vanishing theorem, no finiteness
theorem, and no comparison with Čech cohomology; `Cech.lean` supplies
`cechComplexFunctor` and stops there. That absence is not an oversight to route around, it
is the content of issues #13 and #27.

*Coherent cohomology does not exist upstream at all.* There is no proper-pushforward
finiteness theorem, no Serre finiteness, and no coherent-cohomology anything.
`AlgebraicGeometry.IsProper` is available as a class with the expected stability lemmas,
and `Proj 𝒜 ⟶ Spec 𝒜₀` is known to be proper — but properness of the morphism is the only
part of the classical argument that is in place.

*The projective route now has an explicit construction boundary.*
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/` contains the structure sheaf, the proof
that `Proj` is a scheme, functoriality, and properness, but still no modules. CohLean now supplies
degree-zero localized modules, the locally fractional associated sheaf, integer twists and
`O(d)`. `Proj.Modules.Finiteness` then derives quasi-coherence and coherence from visible affine
comparison data and exposes a degree-bounded global-section interface. What remains for #29 is
not an unspecified API project: it is the concrete polynomial-grading comparison certificate,
followed by the cohomological Serre argument. The missing comparison is a structure field, never
an axiom.

*The affine-cover route is available.* `IsAffineOpen.inf` and `IsAffineOpen.iInf` give
affineness of intersections under an affine diagonal — the separatedness hypothesis in the
Čech argument, in the exact form Mathlib states it — and `IsNoetherian X` already packages
locally noetherian with quasi-compactness, so a finite affine cover with affine finite
intersections is obtainable.

## The decision

**B3 proves vanishing, not finite-dimensionality.** Concretely, stage B3 splits along a
line that was not visible when it was written:

* **Supportable now, via Čech on a finite affine cover.** #13 (affine Čech vanishing for
  tilde modules), #27 (Čech versus derived comparison), #28 (derived affine vanishing), and
  #30 (eventual vanishing and finite cohomological support). The hypotheses are
  `IsNoetherian X` — or quasi-compact plus quasi-separated where that is genuinely enough —
  together with the affine-diagonal instance that `IsAffineOpen.inf` requires. Properness
  never appears, and neither does a base field.
* **Still not proved.** #29, finite-dimensionality of `H^i(X, F)` over a field. Its Proj object
  and finiteness interfaces now exist; the polynomial affine/global-section comparisons and the
  cohomological resolution argument remain. #31 and #32 are downstream of it.

So the milestone target moves from "proper over a field" to **separated noetherian**, for
vanishing only. The projective-to-proper question (#26 question 3, Chow's lemma plus
dévissage) does not arise: this library does not reach the projective case either.

**Consequence for #31 and #32.** The Euler characteristic cannot be *defined* by a theorem
this stage will prove, so it must take finiteness as an input rather than derive it. #31 is now
implemented by `CohLean.Cohomology.EulerCharacteristic.Basic`: `χ` is relative to a functorial
finite-dimensional `k`-linear lift of each `H^i` and an eventual-vanishing bound. #32 proves
additivity from the `Ext` long exact sequence (`Ext.covariantSequence_exact`) plus that bound,
with the hypotheses carried. It is implemented by
`CohLean.Cohomology.EulerCharacteristic.Additivity`; the only additional input is the
base-field-linearity of the connecting maps, since Mathlib currently exposes them only as
additive homomorphisms. Both results become unconditional when Serre finiteness and that
linear compatibility land, without restating them. This keeps the trust boundary where
`CONTRIBUTING.md` puts it: a hypothesis in a statement, never an axiom and never a `sorry`.

## Two shape facts that fix every B3 statement

Both were established by elaboration, not by reading, and both are load-bearing:

1. **`Sheaf.H` needs an explicit `HasExt` and raises the universe.** For `X : Scheme.{u}`
   there is no `HasExt` instance in scope for the Zariski sheaf category; one has to be
   supplied as `HasExt.standard`, and because `Sheaf J AddCommGrpCat.{u}` lives in
   `Type (u + 1)`, the only instance available is `HasExt.{u + 1}`. Cohomology of a sheaf on
   a `Scheme.{u}` therefore lands in `Type (u + 1)`. Every B3 statement inherits that bump;
   deciding it once here is cheaper than each file discovering it.
2. **The bridge from `X.Modules` to abelian sheaves is
   `(SheafOfModules.toSheaf X.ringCatSheaf).obj`.** It is `Additive` and
   `PreservesFiniteLimits`. CohLean's `Scheme.Modules.toSheaf` wrapper also preserves finite
   colimits, so a short exact sequence in `X.Modules` remains short exact in
   `Sheaf J AddCommGrpCat` before `Ext.covariantSequence_exact` applies. The remaining
   interface gap is scalar-linearity of the resulting connecting homomorphisms.

## Dependency graph for #29–#32

```text
  #13 ──┐
        ├──> #28 ──> #30 ──┐
  #27 ──┘                  ├──> #31 ──> #32
                           │
  toSheaf preserves epis ──┘   (new prerequisite, see above)

  #57/#94–#97 interfaces ──> polynomial comparison ──> #29
```

## Not done here

No cohomology group is computed and no Serre-finiteness theorem is proved here. The Proj module
machinery is imported from its real implementation; this file records the remaining boundary and
pins the declarations that #29 will consume.

## References

* [Stacks, Tag 01X8](https://stacks.math.columbia.edu/tag/01X8) — cohomology of quasi-coherent
  sheaves on affines vanishes
* [Stacks, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB) — Čech cohomology on a
  separated scheme computes sheaf cohomology
* [Stacks, Tag 01Y1](https://stacks.math.columbia.edu/tag/01Y1) — finiteness for proper
  morphisms, the theorem this stage does **not** prove
* Hartshorne, *Algebraic Geometry*, III.4 (Čech) and III.5 (Serre finiteness)
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Cohomology.Strategy

/-! ### The cohomology of a sheaf of modules on a scheme is formable

This is the fact that decides the shape of every statement in B3: the `HasExt` instance
has to be supplied by hand, and the result lands one universe up. -/

set_option synthInstance.maxHeartbeats 400000 in
/-- Cohomology of a sheaf of modules on `X : Scheme.{u}` exists and lands in
`Type (u + 1)`. The `HasExt.{u + 1}` instance is not found by synthesis and is not
`HasExt.{u}`; see the module docstring. -/
noncomputable example (X : Scheme.{u}) (M : X.Modules) (n : ℕ) : Type (u + 1) :=
  letI : HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HasExt.standard _
  Sheaf.H ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n

/-! ### The bridge to abelian sheaves, and exactly how exact it is -/

/-- `toSheaf` is additive. -/
example {C : Type*} [Category C] {J : GrothendieckTopology C} (R : Sheaf J RingCat) :
    (SheafOfModules.toSheaf R).Additive := inferInstance

/-- `toSheaf` preserves finite limits, hence kernels and monomorphisms. Preservation of
epimorphisms is *not* upstream, and #32 needs it. -/
noncomputable example {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} R) :=
  inferInstance

/-! ### The long exact sequence engine for #32 -/

/-- The covariant `Ext` long exact sequence attached to a short exact sequence. With
`Sheaf.H` defined as `Ext` from the constant sheaf, this *is* the cohomology long exact
sequence, once the short exact sequence is known to survive `toSheaf`. -/
example := @Abelian.Ext.covariantSequence_exact

/-! ### The Čech side, and what is missing from it -/

/-- Mathlib's Čech complex of a presheaf. There is no comparison with `Sheaf.H` upstream;
supplying one is #27. -/
noncomputable example := @CategoryTheory.cechComplexFunctor

/-! ### The separatedness hypothesis, in the form Mathlib states it

The Čech route needs a finite affine cover whose finite intersections are affine. Mathlib
supplies the second half from an affine diagonal rather than from `IsSeparated` directly,
so that is the hypothesis B3 statements should carry. -/

/-- Intersections of affine opens are affine when the diagonal is affine. -/
example := @IsAffineOpen.inf

/-- The same for finite non-empty families — the shape a Čech complex actually consumes. -/
example := @IsAffineOpen.iInf

/-- `IsNoetherian X` already packages locally noetherian with quasi-compactness, which is
where the *finite* affine cover comes from. -/
example (X : Scheme.{u}) [IsNoetherian X] : CompactSpace X := inferInstance

/-! ### The current projective boundary

`Proj 𝒜 ⟶ Spec 𝒜₀` is proper upstream. CohLean supplies the missing module and twist objects;
the following compile-only references pin the explicit comparison and finiteness interfaces
that separate completed Proj infrastructure from the remaining #29 proof. -/

/-- Quasi-coherence is a theorem once the standard affine `tilde` comparisons are supplied. -/
example := @CohLean.AlgebraicGeometry.Proj.AffineComparisonData.associatedSheaf_isQuasicoherent

/-- Coherence exposes every chart-level noetherianity and finite-generation assumption. -/
example := @CohLean.AlgebraicGeometry.Proj.associatedSheaf_isCoherent_of_noetherian_finite

/-- The global-section theorem is degree-bounded and therefore no stronger than its algebraic
comparison data. -/
example := @CohLean.AlgebraicGeometry.Proj.TwistingSectionRange.globalSections_finite

/-- Finite-variable homogeneous polynomials supply the finite algebraic source for projective
space in each certified degree. -/
example := @CohLean.AlgebraicGeometry.Proj.projectiveSpace_globalSections_finite

/-- Properness of `Proj` over its degree-zero part — the one piece of the classical
projective argument that is already available. -/
example {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ)
    [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A] : IsProper (Proj.toSpecZero 𝒜) :=
  inferInstance

end Cohomology.Strategy

end AlgebraicGeometry
