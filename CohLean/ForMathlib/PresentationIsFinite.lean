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

/-! ### What these unblock, and the one thing still in the way

These two are what every downstream statement about finite presentation needs, and both
`Presentation.quasicoherentData` (the global case, issue #11) and `QuasicoherentData.bind`
(the local-to-global case, issue #12) are built out of exactly `map` and `of_isIso`.

Neither corollary is included here. Both were attempted and backed out rather than left
half-proved, and the obstruction is **not** the presentations — it is instance plumbing:

1. `Presentation.isFinite_map` wants `[PreservesColimitsOfSize.{u, u} F]`. For
   `pushforward (𝟙 (R.over x))` this is available but not at the right universe: the functor is
   a left adjoint (`Sheaf/PushforwardContinuous.lean:275`), and the bridge must be supplied by
   hand as `preservesColimitsOfSize_shrink _`, because that lemma is deliberately not a global
   instance — it loops. *This part works.*
2. What does not: with `[∀ X, HasSheafify (J.over X) AddCommGrpCat]` literally in scope,
   `HasSheafify (J.over x) AddCommGrpCat` still fails to synthesize inside
   `Presentation.quasicoherentData`. The unannotated `AddCommGrpCat` in a `variable` line binds
   its universe from the *first* block that mentions it, so a section that also carries a second
   sheaf of rings `S` on a second site `J'` — as this file does, for `map` — ends up with an
   `AddCommGrpCat` at a different universe from the one `quasicoherentData` requires. Writing
   `AddCommGrpCat.{u}` explicitly does not help; it picks a third.

   The fix is almost certainly to state the global corollary in its **own file**, with the
   variable block copied verbatim from Mathlib's `Presentation.quasicoherentData` section and
   nothing else in scope. That is cheap to try and was not worth doing badly here.
3. For `bind` there is a further one: `QuasicoherentData.I` lives in its own universe `w`, and
   `bind` returns `Σ i, (D i).I`. `of_coversTop` has to be stated with that universe explicit
   for the `w` from `exists_quasicoherentData` to match the `w` `bind` produces.

A practical note for whoever picks this up: introduce the local data with
`choose D hD using …`, not `have D := ….choose`. With `have`, `D i` is opaque and
`choose_spec` types against `_.choose` rather than `D i` — a third error with nothing to do
with the real problem.
-/

end SheafOfModules
