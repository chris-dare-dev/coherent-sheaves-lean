/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.ForMathlib.OpensLimits
import CohLean.ForMathlib.OpensCoversTop
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Presentations on a basic-open cover

A quasi-coherent sheaf on an affine scheme has presentations on the members of some cover of the
open-set site. This file refines that cover to basic opens. The result is the geometric input to
the remaining gluing argument in the affine comparison theorem.

## Main results

* `SheafOfModules.Presentation.over` restricts a presentation along an object of a slice site,
  identifying the iterated restriction with restriction to the domain object.
* `SheafOfModules.QuasicoherentData.over` restricts a full family of local presentations.
* `AlgebraicGeometry.Scheme.Modules.exists_basicOpen_presentation_cover` produces basic opens
  `D(gᵢ)` carrying presentations and with the `gᵢ` generating the unit ideal.

## Implementation

The cover index consists of a member `U` of the quasi-coherent presentation cover together with
a basic open contained in `U`. Every point lies in one of the original cover members, and the
basis theorem for principal opens supplies a contained `D(g)` through that point. The identity
`PrimeSpectrum.iSup_basicOpen_eq_top_iff` then turns the resulting topological cover into the
unit-ideal condition.

Restricting a presentation first gives a presentation of `(M.over U).over W`. Passing from there
to `M.over W.left` uses `Over.iteratedSliceEquiv` and
`SheafOfModules.pushforwardPushforwardEquivalence`. Elaborating that equivalence is expensive,
so the increased heartbeat budget is scoped to `Presentation.over` alone.
-/

universe u

open CategoryTheory Limits TopologicalSpace

namespace SheafOfModules

variable {C : Type u} [Category.{u} C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [hasSheafComposeOver : ∀ X,
    (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [hasSheafifyOver : ∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [hasWeakSheafifyOver : ∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [wEqualsLocallyBijectiveOver : ∀ X,
    (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [hasSheafComposeOverOver : ∀ X Y, ((J.over X).over Y).HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [hasSheafifyOverOver : ∀ X Y,
    HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [hasWeakSheafifyOverOver : ∀ X Y,
    HasWeakSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [wEqualsLocallyBijectiveOverOver : ∀ X Y,
    ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option maxHeartbeats 1600000 in
/-- Restrict a presentation on `U` along an object `W ⟶ U` of the slice site.

The direct restriction has target `((M.over U).over W).Presentation`; the iterated-slice
equivalence identifies that target with `(M.over W.left).Presentation`. -/
noncomputable def Presentation.over {M : SheafOfModules.{u} R} {U : C}
    (P : (M.over U).Presentation) (W : Over U) [HasBinaryProducts (Over U)] :
    (M.over W.left).Presentation := by
  haveI : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pushforward.{u} (𝟙 ((R.over U).over W))) :=
    preservesColimitsOfSize_shrink.{u, u, u, u} _
  let P' : ((M.over U).over W).Presentation :=
    P.map (SheafOfModules.pushforward (𝟙 _)) (.refl _)
  letI eW := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv W)
    (S := (R.over U).over W) (R := R.over W.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  exact (P'.map eW.inverse (.refl _)).ofIsIso
    (eW.fullyFaithfulFunctor.preimageIso
      (by exact eW.counitIso.app ((M.over U).over W))).hom

section QuasicoherentDataOver

variable [HasBinaryProducts C] [HasPullbacks C]

local instance (X : C) : HasBinaryProducts (Over X) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

set_option maxHeartbeats 1600000 in
/-- Restrict one of the presentations in `q` to the product with `U`. -/
noncomputable def QuasicoherentData.presentationOver {M : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) (U : C) (i : q.I) :
    ((M.over U).over ((Over.star U).obj (q.X i))).Presentation := by
  let Y := (Over.star U).obj (q.X i)
  let W : Over (q.X i) := Over.mk (prod.snd : U ⨯ q.X i ⟶ q.X i)
  haveI : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pushforward.{u} (𝟙 ((R.over (q.X i)).over W))) :=
    preservesColimitsOfSize_shrink.{u, u, u, u} _
  let P : ((M.over (q.X i)).over W).Presentation :=
    (q.presentation i).map (SheafOfModules.pushforward (𝟙 _)) (.refl _)
  letI eW := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv W)
    (S := (R.over (q.X i)).over W) (R := R.over W.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  let P' : (M.over W.left).Presentation := (P.map eW.inverse (.refl _)).ofIsIso
    (eW.fullyFaithfulFunctor.preimageIso
      (by exact eW.counitIso.app ((M.over (q.X i)).over W))).hom
  letI eY := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv Y)
    (S := (R.over U).over Y) (R := R.over Y.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  change (eY.functor.obj (M.over Y.left)).Presentation
  exact P'.map eY.functor (.refl _)

@[simp]
theorem QuasicoherentData.presentationOver_generators_I {M : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) (U : C) (i : q.I) :
    (q.presentationOver U i).generators.I = (q.presentation i).generators.I := rfl

@[simp]
theorem QuasicoherentData.presentationOver_relations_I {M : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) (U : C) (i : q.I) :
    (q.presentationOver U i).relations.I = (q.presentation i).relations.I := rfl

/-- Restrict local presentation data to an object of the site. The new cover consists of the
products of the old covering objects with the object of restriction. -/
noncomputable def QuasicoherentData.over {M : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) (U : C) : (M.over U).QuasicoherentData where
  I := q.I
  X i := (Over.star U).obj (q.X i)
  coversTop V := by
    rw [GrothendieckTopology.mem_over_iff]
    refine J.superset_covering ?_ (q.coversTop V.left)
    intro Z g hg
    rw [Sieve.overEquiv_iff]
    obtain ⟨i, ⟨k⟩⟩ := hg
    exact ⟨i, ⟨(Over.forgetAdjStar U).homEquiv _ _ k⟩⟩
  presentation i := q.presentationOver U i

end QuasicoherentDataOver

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

local instance (U : TopologicalSpace.Opens (Spec R)) : HasBinaryProducts (Over U) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

/-- Explicit quasi-coherent data on `Spec R` refines to presentations on a basic-open cover. -/
theorem exists_basicOpen_presentation_cover_of_quasicoherentData
    (M : (Spec R).Modules) (q : SheafOfModules.QuasicoherentData.{u, u, u, u} M) :
    ∃ (I : Type u) (g : I → R), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i, Nonempty ((M.over (PrimeSpectrum.basicOpen (g i))).Presentation) := by
  let I := Σ i : q.I, {g : R // PrimeSpectrum.basicOpen g ≤ q.X i}
  let g : I → R := fun i ↦ i.2.1
  refine ⟨I, g, ?_, ?_⟩
  · apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply TopologicalSpace.Opens.ext
    apply Set.ext
    intro x
    constructor
    · intro
      trivial
    intro hx
    obtain ⟨U, f, hf, hxU⟩ := q.coversTop ⊤ x (by simp)
    obtain ⟨i, ⟨k⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp hf
    have hxXi : x ∈ q.X i := k.le hxU
    obtain ⟨V, ⟨_, ⟨a, rfl⟩, rfl⟩, hxV, hV⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxXi (q.X i).2
    rw [TopologicalSpace.Opens.coe_iSup]
    exact Set.mem_iUnion.mpr ⟨⟨i, ⟨a, hV⟩⟩, hxV⟩
  · rintro ⟨i, a, ha⟩
    let W : Over (q.X i) := Over.mk (homOfLE ha)
    exact ⟨(q.presentation i).over W⟩

/-- A quasi-coherent sheaf on `Spec R` has presentations on a basic-open cover.

The algebraic cover condition says that the defining elements generate the unit ideal; equivalently,
the corresponding basic opens have supremum `⊤`. -/
theorem exists_basicOpen_presentation_cover
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ∃ (I : Type u) (g : I → R), Ideal.span (Set.range g) = ⊤ ∧
      ∀ i, Nonempty ((M.over (PrimeSpectrum.basicOpen (g i))).Presentation) := by
  obtain ⟨q⟩ :=
    SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := M)
  exact M.exists_basicOpen_presentation_cover_of_quasicoherentData q

end AlgebraicGeometry.Scheme.Modules
