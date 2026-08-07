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

/-! ### What these unblock, and what still stands in the way

With both instances above, `QuasicoherentData.bind`'s presentations — built as
`(P.map _ _).of_isIso _` — are finite whenever the local data are, which is the missing step
in `SheafOfModules.IsFinitePresentation.of_coversTop` (issues #11 and #12).

An attempt at that corollary is **not** included here, because it does not follow by
`infer_instance` and the obstructions are not about presentations at all:

1. `Presentation.isFinite_map` needs `[PreservesColimitsOfSize.{u, u} F]`, and the `F` inside
   `bind` is `(pushforwardPushforwardEquivalence …).inverse`. Instance search does not produce
   the universe-matched `PreservesColimitsOfSize` for an equivalence's inverse; Mathlib's own
   file works around this with `local instance : PreservesColimitsOfSize.{0, 0} F :=
   preservesColimitsOfSize_shrink _`, so the same workaround is likely needed, universe-matched.
2. `QuasicoherentData.I` lives in its own universe `w`, and `bind` produces `Σ i, (D i).I`.
   Stating `of_coversTop` so that the `w` coming out of `exists_quasicoherentData` matches the
   one `bind` returns needs the universes written explicitly rather than inferred.

Neither is deep, but both are elaboration work rather than mathematics, and doing them badly
would bury the two clean lemmas above. Recorded on the issues instead of guessed at here.
-/

end SheafOfModules
