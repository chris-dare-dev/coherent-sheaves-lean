/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Coh.Defs
import CohLean.ForMathlib.FinitePresentationOfPresentation
import CohLean.ForMathlib.OpensBinaryProducts
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
  weakens to finite generation.

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

## Not yet proved

Only the forward direction is here. The converse and the equivalence itself are **absent
from this library** — not assumed, not `sorry`ed, simply not done:

* that a coherent sheaf on `Spec R` has finitely presented global sections, for `R`
  noetherian;
* consequently the equivalence `Coh (Spec R) ≌` finitely generated `R`-modules.

Nothing downstream may assume either.

The obstruction is identified and is not a matter of effort in this file. Both statements
need the **affine comparison theorem** — that a quasi-coherent sheaf on `Spec R` is
recovered from its global sections, `IsIso M.fromTildeΓ` — and that theorem is missing from
Mathlib at `v4.29.0`. `SheafOfModules.IsFinitePresentation` is by definition *local* data,
an existential over `QuasicoherentData`, and Mathlib supplies no bridge from it to global
sections: `isIso_fromTildeΓ_of_presentation` needs a **global** presentation as its input,
and the only `IsIso (fromTildeΓ …)` instances are for `unit` and `free ι`. Supplying the
comparison is issue #46; the converse half of #11 waits on it.

## References

* [Stacks, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8) — quasi-coherent modules on
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

end AlgebraicGeometry
