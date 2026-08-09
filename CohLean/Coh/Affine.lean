/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Coh.Defs
import CohLean.ForMathlib.AffineComparisonFiniteness
import CohLean.ForMathlib.FinitePresentationOfPresentation
import CohLean.ForMathlib.OpensLimits
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Coherent sheaves on an affine scheme

**Layer B, stage 1.** The affine comparison between coherent sheaves on `Spec R` and
finitely presented `R`-modules.

## Main results

* `AlgebraicGeometry.isFinitePresentation_tilde` — `M^~` is of finite presentation whenever
  `M` is a finitely presented `R`-module;
* `AlgebraicGeometry.isCoherent_tilde` — the same statement phrased with
  `Scheme.Modules.IsCoherent`, which is what `Coh (Spec R)` is carved out of;
* `AlgebraicGeometry.isCoherent_tilde_of_finite` — over a noetherian ring the hypothesis
  weakens to finite generation;
* `AlgebraicGeometry.moduleFinite_globalSections_of_isFiniteType` — finite-type
  quasi-coherent sheaves have finite global sections on an affine noetherian scheme;
* `AlgebraicGeometry.moduleFinitePresentation_globalSections_of_isCoherent` — coherent
  sheaves have finitely presented global sections.

## Proof strategy

Mathlib already does the mathematics. `AlgebraicGeometry.presentationTilde` turns a
generating set `s` for `M` together with a generating set `t` for the kernel of `R^s → M`
into a global `SheafOfModules.Presentation (tilde M)`, and that is exactly the data recorded
by `Module.FinitePresentation`. So the content here is only that the presentation is
*finite* — `Presentation.IsFinite` is finiteness of the two index types, and
`presentationTilde` builds them out of `s` and `t` themselves — after which
`SheafOfModules.IsFinitePresentation.of_presentation` applies.

## Two elaboration hazards

Both cost more time than the mathematics, and both are recorded here so the next caller does
not rediscover them.

1. **Universes do not propagate from the goal.** `Presentation.IsFinite` and
   `of_presentation` carry universe parameters that bind *before* their explicit arguments,
   so a goal phrased as `Scheme.Modules.IsCoherent …` does not pin them; Lean defaults them
   to `0` and reports a type mismatch at `Type 1` rather than an ambiguity. Annotating
   `.{u, u, u}` at the use site is what fixes it — `(M := …)` does not, because the
   universes bind first. This is the gotcha already recorded in
   `FinitePresentationOfPresentation.lean`.
2. **Anonymous constructors do not see the expected type here.** `refine ⟨⟨?_⟩, ?_⟩` against
   a ground `Presentation.IsFinite …` goal still elaborates at universe `0`, and
   `refine Presentation.IsFinite.mk ?_ ?_` gets stuck synthesising
   `WEqualsLocallyBijective ?J AddCommGrpCat` because the head is elaborated before the goal
   is unified. `constructor` unifies with the goal first and goes through.

The `Finset`/`Set` mismatch that an earlier investigation predicted — `FinitePresentation`
gives `s : Finset M` while `presentationTilde` wants `s : Set M` and `t : Set (↥s →₀ R)` —
does not in fact bite: the coercion is accepted as written.

The converse finiteness results use the affine comparison and localisation patching developed
in `CohLean.ForMathlib.AffineComparisonFiniteness`.

## Not yet assembled

The two object-level directions needed for the affine equivalence are now proved, but the
categorical equivalence itself is not yet assembled here:

* `Coh (Spec R) ≌` finitely generated `R`-modules.

Nothing downstream may assume the equivalence until #11 packages the functors and natural
isomorphisms.

The required bridge is now available as
`Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`, proved by the gluing argument in
`CohLean.ForMathlib.AffineComparisonGluing`. Its finiteness consequences are now supplied by
`CohLean.ForMathlib.AffineComparisonFiniteness`; only the categorical assembly tracked by #11
remains.

## References

* [Stacks, Tag 01IA](https://stacks.math.columbia.edu/tag/01IA) — quasi-coherent modules on
  an affine scheme
-/

universe u

open CategoryTheory Limits SheafOfModules

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/-- **`M^~` is of finite presentation when `M` is.**

The presentation is Mathlib's `presentationTilde`, whose generator and relation index types
are the two generating sets supplied by `Module.FinitePresentation`; finiteness of the
presentation is therefore finiteness of those sets. -/
theorem isFinitePresentation_tilde (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    SheafOfModules.IsFinitePresentation.{u, u, u} (tilde M) := by
  obtain ⟨s, hs, hker⟩ := (‹Module.FinitePresentation R M›).out
  rw [Submodule.fg_def] at hker
  obtain ⟨t, htfin, ht⟩ := hker
  haveI : Finite ((s : Set M) : Type u) := s.finite_toSet.to_subtype
  haveI : Finite t := htfin.to_subtype
  -- `.{u, u, u}` and `constructor` are both load-bearing; see the module docstring.
  haveI : Presentation.IsFinite.{u, u, u} (presentationTilde M (s : Set M) hs t ht) := by
    constructor
    · constructor
      exact inferInstanceAs (Finite ((s : Set M) : Type u))
    · exact inferInstanceAs (Finite t)
  exact IsFinitePresentation.of_presentation.{u, u, u} (presentationTilde M (s : Set M) hs t ht)

/-- **`M^~` is coherent when `M` is finitely presented.**

This is `isFinitePresentation_tilde` phrased through `Scheme.Modules.IsCoherent`, which is
the predicate `Coh (Spec R)` is carved out of. -/
theorem isCoherent_tilde (M : ModuleCat.{u} R) [Module.FinitePresentation R M] :
    Scheme.Modules.IsCoherent (Spec R) (tilde M) :=
  isFinitePresentation_tilde M

/-- Over a noetherian ring, `M^~` is coherent as soon as `M` is finitely generated.

`Module.finitePresentation_of_finite` is where `IsNoetherianRing` earns its place: finite
generation alone is not enough in general, because the relations need not be finitely
generated. -/
theorem isCoherent_tilde_of_finite [IsNoetherianRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] : Scheme.Modules.IsCoherent (Spec R) (tilde M) :=
  haveI := Module.finitePresentation_of_finite (R := R) (M := M)
  isCoherent_tilde M

/-- A quasi-coherent finite-type module sheaf on an affine noetherian scheme has finitely
generated global sections. The underlying finite-generation theorem does not need the
noetherian hypothesis; it is retained here because this is the public corollary consumed by the
noetherian affine equivalence. -/
theorem moduleFinite_globalSections_of_isFiniteType [IsNoetherianRing R]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (hM : SheafOfModules.IsFiniteType.{u, u, u} M) :
    Module.Finite R (moduleSpecΓFunctor.obj M) :=
  Scheme.Modules.moduleFinite_globalSections_of_isFiniteType M hM

/-- A coherent module sheaf on an affine noetherian scheme has finitely presented global
sections. -/
theorem moduleFinitePresentation_globalSections_of_isCoherent [IsNoetherianRing R]
    (M : (Spec R).Modules) (hM : Scheme.Modules.IsCoherent (Spec R) M) :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := by
  have hM' : SheafOfModules.IsFinitePresentation.{u, u, u} M := hM
  letI : Module.Finite R (moduleSpecΓFunctor.obj M) :=
    Scheme.Modules.moduleFinite_globalSections M hM'
  exact Module.finitePresentation_of_finite R (moduleSpecΓFunctor.obj M)

end AlgebraicGeometry
