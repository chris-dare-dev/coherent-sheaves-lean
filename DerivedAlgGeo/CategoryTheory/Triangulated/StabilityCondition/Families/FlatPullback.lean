/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Sheafify
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.ExactPullback

/-!
# Flatness prerequisites for exact pullback

This file begins the geometric discharge of the exactness hypothesis used by
`Families.ExactPullback`.  Mathlib proves that extension of scalars along a
flat ring homomorphism preserves finite limits.  A flat morphism of schemes
has a flat map on every local ring, so the corresponding scalar-extension
functor is left exact at every stalk.

The remaining global step is a natural comparison between the stalk of
module-sheaf pullback and extension of scalars along the stalk map.  That
comparison is not presently exposed by Mathlib's module-sheaf API, so this
file does not yet install `IsExactPullback` from scheme flatness alone.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- The cocone of underlying rings whose point is the local ring of `X` at
`x`.  It is the image of the standard commutative-ring stalk cocone. -/
def moduleStalkRingCocone (X : Scheme.{u}) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf ⋙
      forget₂ CommRingCat RingCat) :=
  (forget₂ CommRingCat RingCat).mapCocone
    (colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf))

/-- The underlying-ring stalk cocone is a colimit cocone. -/
def moduleStalkRingIsColimit (X : Scheme.{u}) (x : X) :
    IsColimit (moduleStalkRingCocone X x) :=
  isColimitOfPreserves (forget₂ CommRingCat RingCat)
    (colimit.isColimit ((OpenNhds.inclusion x).op ⋙ X.presheaf))

/-- The stalk of a presheaf of modules, bundled over the local ring. -/
def presheafModuleStalkFunctor (X : Scheme.{u}) (x : X) :
    PresheafOfModules.{u} X.ringCatSheaf.obj ⥤
      ModuleCat.{u} (X.presheaf.stalk x) :=
  letI : InitiallySmall.{u} (OpenNhds x) :=
    initiallySmall_of_essentiallySmall _
  PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
      X.ringCatSheaf.obj ⋙
    PresheafOfModules.colimitFunctor
      (moduleStalkRingIsColimit X x)

/-- The stalk of a sheaf of modules, bundled as a module over the local ring.

This refines the usual abelian-group-valued stalk functor with the canonical
local-ring module structure. -/
def moduleStalkFunctor (X : Scheme.{u}) (x : X) :
    X.Modules ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  Scheme.Modules.toPresheafOfModules X ⋙
    presheafModuleStalkFunctor X x

/-- The module map on stalks induced by the unit from a presheaf of modules
to its module sheafification. -/
def presheafModuleStalkToSheafificationApp
    (X : Scheme.{u}) (x : X)
    (M : PresheafOfModules.{u} X.ringCatSheaf.obj) :
    (presheafModuleStalkFunctor X x).obj M ⟶
      (moduleStalkFunctor X x).obj
        ((PresheafOfModules.sheafification
          (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).obj M) :=
  (presheafModuleStalkFunctor X x).map
    ((PresheafOfModules.sheafificationAdjunction
      (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.app M)

/-- Module sheafification induces an isomorphism on every module stalk. -/
theorem presheafModuleStalkToSheafificationApp_isIso
    (X : Scheme.{u}) (x : X)
    (M : PresheafOfModules.{u} X.ringCatSheaf.obj) :
    IsIso (presheafModuleStalkToSheafificationApp X x M) := by
  rw [← isIso_iff_of_reflects_iso _
    (forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u})]
  change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) M.presheaf))
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    x AddCommGrpCat M.presheaf

/-- Taking a module stalk commutes naturally with module sheafification. -/
def presheafModuleStalkSheafificationIso
    (X : Scheme.{u}) (x : X) :
    presheafModuleStalkFunctor X x ≅
      PresheafOfModules.sheafification
          (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj) ⋙
        moduleStalkFunctor X x :=
  NatIso.ofComponents
    (fun M ↦
      @asIso _ _ _ _ (presheafModuleStalkToSheafificationApp X x M)
        (presheafModuleStalkToSheafificationApp_isIso X x M))
    (fun {M N} f ↦ by
      rw [asIso_hom, asIso_hom]
      change (presheafModuleStalkFunctor X x).map f ≫
          (presheafModuleStalkFunctor X x).map
            ((PresheafOfModules.sheafificationAdjunction
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.app N) =
        (presheafModuleStalkFunctor X x).map
            ((PresheafOfModules.sheafificationAdjunction
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.app M) ≫
          (presheafModuleStalkFunctor X x).map
            (((PresheafOfModules.sheafification
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).map f).val)
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congr_arg (presheafModuleStalkFunctor X x).map
        ((PresheafOfModules.sheafificationAdjunction
          (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)).unit.naturality f))

/-- Forgetting the local-ring action on `moduleStalkFunctor` recovers the
usual stalk of the underlying sheaf of abelian groups. -/
def moduleStalkForgetIso (X : Scheme.{u}) (x : X) :
    moduleStalkFunctor X x ⋙
        forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf X.ringCatSheaf ⋙
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) :=
  Functor.associator _ _ _

/-- Taking the stalk of a sheaf of modules preserves finite limits. -/
theorem moduleStalkFunctor_preservesFiniteLimits
    (X : Scheme.{u}) (x : X) :
    PreservesFiniteLimits (moduleStalkFunctor X x) := by
  let forgetModule :=
    forget₂ (ModuleCat.{u} (X.presheaf.stalk x)) AddCommGrpCat.{u}
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  let G := TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hF : PreservesFiniteLimits F := inferInstance
  have hG : PreservesFiniteLimits G := inferInstance
  have hFG : PreservesFiniteLimits (F ⋙ G) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ F G hF hG
  have hComposite :
      PreservesFiniteLimits (moduleStalkFunctor X x ⋙ forgetModule) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _
      (moduleStalkForgetIso X x).symm hFG
  letI := hComposite
  exact preservesFiniteLimits_of_reflects_of_preserves
    (moduleStalkFunctor X x) forgetModule

/-- The family of module-stalk functors over all points detects
isomorphisms of sheaves of modules. -/
theorem moduleStalkFunctors_jointlyReflectIsomorphisms (X : Scheme.{u}) :
    JointlyReflectIsomorphisms (moduleStalkFunctor X) where
  isIso {M N} f := by
    intro
    let M' : TopCat.Sheaf AddCommGrpCat.{u} X :=
      ⟨M.presheaf, M.isSheaf⟩
    let N' : TopCat.Sheaf AddCommGrpCat.{u} X :=
      ⟨N.presheaf, N.isSheaf⟩
    let g : M' ⟶ N' := { hom := f.mapPresheaf }
    haveI : IsIso g := by
      rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
      intro x
      have : IsIso
          ((forget₂ (ModuleCat.{u} (X.presheaf.stalk x))
            AddCommGrpCat.{u}).map ((moduleStalkFunctor X x).map f)) :=
        inferInstance
      exact this
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro U
    change IsIso
      (((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map g).app (op U))
    infer_instance

/-- A functor between categories of module sheaves preserves finite limits
as soon as all of its composites with module-stalk functors do. -/
theorem preservesFiniteLimits_of_stalkwise
    {X Y : Scheme.{u}} (F : Y.Modules ⥤ X.Modules)
    (hF : ∀ x : X,
      PreservesFiniteLimits (F ⋙ moduleStalkFunctor X x)) :
    PreservesFiniteLimits F where
  preservesFiniteLimits J _ _ := by
    letI (x : X) : PreservesFiniteLimits (moduleStalkFunctor X x) :=
      moduleStalkFunctor_preservesFiniteLimits X x
    letI (x : X) : PreservesFiniteLimits
        (F ⋙ moduleStalkFunctor X x) :=
      hF x
    refine { preservesLimit := fun {K} ↦
      { preserves := fun {c} hc ↦ ⟨?_⟩ } }
    exact (moduleStalkFunctors_jointlyReflectIsomorphisms X).jointlyReflectsLimit
      (fun x ↦ by
        change IsLimit ((F ⋙ moduleStalkFunctor X x).mapCone c)
        exact isLimitOfPreserves (F ⋙ moduleStalkFunctor X x) hc)

/-- At every point of a flat scheme morphism, extension of scalars along the
induced local-ring map preserves finite limits. -/
theorem flatStalkMap_preservesFiniteLimits
    {T U : SchemeBaseChange S} (f : T ⟶ U) [Flat f.left] (x : T.left) :
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (f.left.stalkMap x).hom) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (Flat.stalkMap f.left x)

/-- The stalkwise model for pullback along a flat scheme morphism—first
take the source sheaf's stalk, then extend scalars along the local-ring
map—preserves finite limits. -/
theorem flatPullbackStalkModel_preservesFiniteLimits
    {T U : SchemeBaseChange S} (f : T ⟶ U) [Flat f.left] (x : T.left) :
    PreservesFiniteLimits
      (moduleStalkFunctor U.left (f.left x) ⋙
        ModuleCat.extendScalars.{u, u, u} (f.left.stalkMap x).hom) := by
  have hStalk : PreservesFiniteLimits
      (moduleStalkFunctor U.left (f.left x)) :=
    moduleStalkFunctor_preservesFiniteLimits U.left (f.left x)
  have hScalars : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (f.left.stalkMap x).hom) :=
    flatStalkMap_preservesFiniteLimits f x
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hStalk hScalars

/-- The precise comparison datum still needed from the module-sheaf
pullback API: actual pullback followed by the stalk at `x` agrees with
stalk followed by extension of scalars along the local-ring map. -/
structure PullbackStalkComparison
    {T U : SchemeBaseChange S} (f : T ⟶ U) where
  /-- At each source point, actual module pullback followed by the stalk is
  naturally isomorphic to stalk followed by extension of scalars. -/
  iso (x : T.left) :
    modulePullback f ⋙ moduleStalkFunctor T.left x ≅
      moduleStalkFunctor U.left (f.left x) ⋙
        ModuleCat.extendScalars.{u, u, u} (f.left.stalkMap x).hom

/-- The pullback-to-stalk comparison for the identity morphism, assembled
from the identity laws for module pullback, stalk maps, and scalar extension. -/
def pullbackStalkComparisonId (T : SchemeBaseChange S) :
    PullbackStalkComparison (𝟙 T) where
  iso x := by
    change modulePullback (𝟙 T) ⋙ moduleStalkFunctor T.left x ≅
      moduleStalkFunctor T.left x ⋙
        ModuleCat.extendScalars ((𝟙 T.left : T.left ⟶ T.left).stalkMap x).hom
    rw [Scheme.Hom.stalkMap_id]
    exact Functor.isoWhiskerRight (modulePullbackId T)
          (moduleStalkFunctor T.left x) ≪≫
        Functor.leftUnitor _ ≪≫
        (Functor.rightUnitor _).symm ≪≫
        Functor.isoWhiskerLeft (moduleStalkFunctor T.left x)
          (ModuleCat.extendScalarsId _).symm

/-- Pullback-to-stalk comparisons compose compatibly with module pullback,
the functoriality of stalk maps, and iterated extension of scalars. -/
def PullbackStalkComparison.comp
    {T U V : SchemeBaseChange S} {f : T ⟶ U} {g : U ⟶ V}
    (hf : PullbackStalkComparison f) (hg : PullbackStalkComparison g) :
    PullbackStalkComparison (f ≫ g) where
  iso x := by
    change modulePullback (f ≫ g) ⋙ moduleStalkFunctor T.left x ≅
      moduleStalkFunctor V.left (g.left (f.left x)) ⋙
        ModuleCat.extendScalars ((f.left ≫ g.left).stalkMap x).hom
    rw [Scheme.Hom.stalkMap_comp]
    exact Functor.isoWhiskerRight (modulePullbackComp f g).symm
          (moduleStalkFunctor T.left x) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (modulePullback g) (hf.iso x) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (hg.iso (f.left x))
          (ModuleCat.extendScalars (f.left.stalkMap x).hom) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft
          (moduleStalkFunctor V.left (g.left (f.left x)))
          (ModuleCat.extendScalarsComp (g.left.stalkMap (f.left x)).hom
            (f.left.stalkMap x).hom).symm

/-- Flat pullback preserves finite limits once the explicit
pullback-to-stalk comparison is supplied. -/
theorem modulePullback_preservesFiniteLimits_of_flat_of_stalkComparison
    {T U : SchemeBaseChange S} (f : T ⟶ U) [Flat f.left]
    (h : PullbackStalkComparison f) :
    PreservesFiniteLimits (modulePullback f) :=
  preservesFiniteLimits_of_stalkwise (modulePullback f) fun x ↦ by
    have hTarget : PreservesFiniteLimits
        (moduleStalkFunctor U.left (f.left x) ⋙
          ModuleCat.extendScalars.{u, u, u} (f.left.stalkMap x).hom) :=
      flatPullbackStalkModel_preservesFiniteLimits f x
    exact @preservesFiniteLimits_of_natIso _ _ _ _ _ _
      (h.iso x).symm hTarget

/-- A flat scheme morphism has exact module-sheaf pullback once its actual
pullback functor is identified with the stalkwise scalar-extension model. -/
theorem isExactPullback_of_flat_of_stalkComparison
    {T U : SchemeBaseChange S} (f : T ⟶ U) [Flat f.left]
    (h : PullbackStalkComparison f) : IsExactPullback f := by
  letI : PreservesFiniteLimits (modulePullback f) :=
    modulePullback_preservesFiniteLimits_of_flat_of_stalkComparison f h
  exact IsExactPullback.of_preservesFiniteLimits f

end SchemeBaseChange

end

end CategoryTheory.Triangulated.StabilityCondition.Families
