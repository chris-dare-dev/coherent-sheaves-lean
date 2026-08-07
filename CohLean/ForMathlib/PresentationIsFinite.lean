/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Finiteness of a presentation is preserved by transport

Mathlib has two ways of moving a `SheafOfModules.Presentation` around — along an isomorphism
(`Presentation.of_isIso`) and along a colimit-preserving functor (`Presentation.map`) — and
no lemma saying either preserves `Presentation.IsFinite`.

That gap is why `SheafOfModules.IsFinitePresentation` has no local-to-global criterion even
though `IsQuasicoherent` does: `QuasicoherentData.bind` builds its presentations as
`(P.map _ _).of_isIso _`, so without these two instances there is no way to conclude that the
glued data is finite.

Both are cheap, because `Presentation.IsFinite` is nothing more than finiteness of the two
index types `generators.I` and `relations.I`, and neither transport touches them.

## Main results

* `Presentation.isFinite_of_isIso`
* `Presentation.isFinite_map`

Destined for `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`; kept in Mathlib
namespaces so upstreaming is a file move.
-/

universe v₁ v₂ u₁ u₂ u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- Transporting a presentation along an isomorphism keeps it finite: `of_isIso` composes the
generating and relating maps with an iso and leaves both index types alone. -/
instance Presentation.isFinite_of_isIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
    (P : M.Presentation) [P.IsFinite] : (Presentation.of_isIso f P).IsFinite where
  isFiniteType_generators :=
    ⟨inferInstanceAs (Finite P.generators.I)⟩
  finite_relations :=
    inferInstanceAs (Finite P.relations.I)

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [J'.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- Transporting a presentation along a colimit-preserving functor keeps it finite:
`Presentation.map` builds the new generators and relations out of the *same* index types
(`map_generators_I`, `map_relations_I`). -/
instance Presentation.isFinite_map {M : SheafOfModules.{u} R} (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [PreservesColimitsOfSize.{u, u} F]
    (η : F.obj (unit R) ≅ unit S) : (P.map F η).IsFinite where
  isFiniteType_generators := by
    refine ⟨?_⟩
    rw [Presentation.map_generators_I]
    exact inferInstanceAs (Finite P.generators.I)
  finite_relations := by
    rw [Presentation.map_relations_I]
    exact inferInstanceAs (Finite P.relations.I)

/-! ### What these unblock, and the state of the corollary

These two are what every downstream statement about finite presentation needs:
`Presentation.quasicoherentData` (the global case, issue #11) and `QuasicoherentData.bind`
(local-to-global, issue #12) are both built out of exactly `map` and `of_isIso`.

Neither corollary is included. `IsFinitePresentation.of_presentation` was attempted in an
isolated file and removed rather than left broken. What is now **known**, having tried it:

* The `PreservesColimitsOfSize.{u, u}` half is solved. `pushforward (𝟙 (R.over x))` is a left
  adjoint (`Sheaf/PushforwardContinuous.lean:275`) and `preservesColimitsOfSize_shrink _`
  bridges the universe by hand — it cannot be a global instance because it loops.
* The blocker is `HasSheafify (J.over x) AddCommGrpCat` failing to synthesise inside the proof.
  With `set_option pp.universes true` the requirement prints as
  `HasSheafify.{v₁, u, max u₁ v₁, u + 1} (GrothendieckTopology.over.{v₁, u₁} J x) AddCommGrpCat.{u}`,
  which is **exactly** what `[∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]` provides.
* Ruled out, each by a separate attempt: universe drift on an unannotated `AddCommGrpCat`
  (pinning every occurrence to `.{u}` changes nothing); contamination from a second sheaf of
  rings in scope (an isolated file with Mathlib's variable block copied verbatim fails
  identically); `variable` auto-inclusion (writing all binders explicitly in the signature
  fails identically); and instance search declining to instantiate a `∀`-quantified hypothesis
  (naming the binder and applying it at `x` with `haveI` fails identically).

The next step is to read a `set_option trace.Meta.synthInstance true` trace on that goal. That
is a different kind of session from writing the lemma, so it is recorded rather than guessed
at further.

A practical note regardless: introduce local data with `choose D hD using …`, not
`have D := ….choose`. With `have`, `D i` is opaque and `choose_spec` types against `_.choose`
rather than `D i` — an error with nothing to do with the real problem.
-/

end SheafOfModules
