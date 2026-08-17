/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.PUnit
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Relative
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.DerivedPullbackLaws

/-!
# The relative-perfect moduli presheaf

This file packages universally-gluable relative-perfect complexes and their
isomorphisms as a groupoid-valued pseudofunctor on an actual diagram of scheme
base changes.  A `RelativePerfectModuliProblem` does not choose unrelated
fiber categories: its fiber over `T` is definitionally the core of
`SchemeUniversallyGluableCategory T.hom`, and every transition functor comes
with a natural comparison to the repository's exact derived pullback.

The explicit system boundary is necessary at the current stage.  Exact
derived pullback has been constructed, but preservation of pseudo-coherence,
finite Tor amplitude, and fiberwise negative Ext is not yet available for
arbitrary scheme morphisms.  Thus this file neither installs such a theorem
nor asserts descent or algebraicity.  It constructs the moduli pseudofunctor
from proved restriction data and gives a concrete identity system and zero
objects, including on geometric-point fibers.
-/

namespace AlgebraicGeometry

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Triangulated.StabilityCondition.Families

noncomputable section

universe u v w

/-- The category underlying the relative-perfect moduli groupoid over one
scheme base change.  Its arrows are only isomorphisms. -/
abbrev RelativePerfectModuliFiber {S : Scheme.{u}}
    (T : SchemeBaseChange S) :=
  Core (SchemeUniversallyGluableCategory T.hom)

/-- Forget a universally-gluable relative-perfect object to the ambient
scheme-derived category. -/
def relativePerfectForget {S : Scheme.{u}} (T : SchemeBaseChange S) :
    SchemeUniversallyGluableCategory T.hom ⥤ T.DerivedFiber :=
  ObjectProperty.ι _ ⋙ SchemeQuasicoherentDerivedCategory.ι T.left

/-- Forget a relative-perfect moduli groupoid to the ambient derived
category. -/
def relativePerfectModuliForget {S : Scheme.{u}} (T : SchemeBaseChange S) :
    RelativePerfectModuliFiber T ⥤ T.DerivedFiber :=
  Core.inclusion _ ⋙ relativePerfectForget T

/-- A groupoid-valued relative-perfect moduli problem on a contravariant
diagram of actual scheme base changes.

The pseudofunctor itself owns the unit, compositor, triangle, and pentagon
laws.  `fiberEquivalence` identifies each of its fibers with the actual core
of universally-gluable relative-perfect complexes.  `ambientComparison`
forces every transition, through those equivalences, to be the repository's
exact derived pullback on both objects and morphisms. -/
structure RelativePerfectModuliProblem (S : Scheme.{u})
    (B : Type v) [Category.{w} B] where
  /-- The contravariant diagram of actual scheme base changes. -/
  base : Bᵒᵖ ⥤ SchemeBaseChange S
  /-- The coherent groupoid-valued presheaf. -/
  presheaf : Pseudofunctor (LocallyDiscrete B) Cat.{u + 1, u + 1}
  /-- Identification of every abstract pseudofunctor fiber with the actual
  relative-perfect moduli groupoid. -/
  fiberEquivalence (X : B) :
    presheaf.obj (.mk X) ≌
      RelativePerfectModuliFiber (base.obj (Opposite.op X))
  /-- Exactness of every pullback used by the diagram. -/
  exactPullback {X Y : B} (f : X ⟶ Y) :
    SchemeBaseChange.IsExactPullback (base.map f.op)
  /-- The pseudofunctor transition is the actual exact derived pullback after
  transport to the concrete moduli groupoids and forgetting to the ambient
  derived categories. -/
  ambientComparison {X Y : B} (f : X ⟶ Y) :
    letI := exactPullback f
    (fiberEquivalence X).functor ⋙
        relativePerfectModuliForget (base.obj (Opposite.op X)) ⋙
      SchemeBaseChange.derivedPullback (base.map f.op) ≅
    (presheaf.map (.mk f)).toFunctor ⋙ (fiberEquivalence Y).functor ⋙
      relativePerfectModuliForget (base.obj (Opposite.op Y))

namespace RelativePerfectModuliProblem

variable {S : Scheme.{u}} {B : Type v} [Category.{w} B]

/-- Every fiber of a relative-perfect moduli problem is a groupoid. -/
instance presheaf_obj_isGroupoid (M : RelativePerfectModuliProblem S B)
    (X : LocallyDiscrete B) : IsGroupoid (M.presheaf.obj X) :=
  isGroupoid_of_reflects_iso (M.fiberEquivalence X.as).functor

end RelativePerfectModuliProblem

/-- Isomorphism classes of universally-gluable relative-perfect objects over
one scheme base change. -/
abbrev RelativePerfectIsomorphismClasses {S : Scheme.{u}}
    (T : SchemeBaseChange S) :=
  Quotient (isIsomorphicSetoid (SchemeUniversallyGluableCategory T.hom))

/-- The isomorphism class represented by one moduli object. -/
def relativePerfectIsomorphismClass {S : Scheme.{u}}
    {T : SchemeBaseChange S}
    (E : SchemeUniversallyGluableCategory T.hom) :
    RelativePerfectIsomorphismClasses T :=
  Quotient.mk (isIsomorphicSetoid _) E

/-- The relative-perfect moduli groupoid on the geometric-point base change
`Spec κ(x) ⟶ S`. -/
abbrev RelativePerfectGeometricFiber {S : Scheme.{u}}
    (T : SchemeBaseChange S) (x : T.left) :=
  RelativePerfectModuliFiber (T.residue x)

/-- The zero complex as an object of the relative-perfect moduli groupoid. -/
def relativePerfectZeroObject {S : Scheme.{u}} (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left] : RelativePerfectModuliFiber T :=
  ⟨⟨SchemeQuasicoherentDerivedCategory.zero T.left,
      schemeUniversallyGluableRelativePerfect_zero T.hom⟩⟩

/-- Every locally Noetherian scheme base change has a nonempty
relative-perfect moduli groupoid. -/
theorem relativePerfectModuliFiber_nonempty {S : Scheme.{u}}
    (T : SchemeBaseChange S) [IsLocallyNoetherian T.left] :
    Nonempty (RelativePerfectModuliFiber T) :=
  ⟨relativePerfectZeroObject T⟩

/-- Every geometric-point fiber has the concrete zero object. -/
def relativePerfectGeometricZeroObject {S : Scheme.{u}}
    (T : SchemeBaseChange S) (x : T.left) :
    RelativePerfectGeometricFiber T x := by
  letI : IsLocallyNoetherian (T.residue x).left := by
    change IsLocallyNoetherian (Spec (T.left.residueField x))
    infer_instance
  exact relativePerfectZeroObject (T.residue x)

/-! ## The concrete identity moduli problem

This is the smallest geometric model of the interface: one actual scheme base
change, identity derived pullback, and the full moduli groupoid at that base.
It proves that the pseudofunctor package is inhabited without asserting
preservation along any nonidentity morphism. -/

/-- The constant diagram at one scheme base change. -/
def identityBaseChangeDiagram {S : Scheme.{u}} (T : SchemeBaseChange S) :
    PUnitᵒᵖ ⥤ SchemeBaseChange S :=
  (Functor.const PUnitᵒᵖ).obj T

/-- The constant groupoid-valued pseudofunctor at one relative-perfect
moduli fiber. -/
def constantRelativePerfectPresheaf {S : Scheme.{u}}
    (T : SchemeBaseChange S) :
    Pseudofunctor (LocallyDiscrete PUnit) Cat.{u + 1, u + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun _ ↦ Cat.of (RelativePerfectModuliFiber T))
    (fun _ ↦ (𝟭 _).toCatHom)
    (fun _ ↦ Cat.Hom.isoMk (Iso.refl _))
    (fun _ _ ↦ Cat.Hom.isoMk (Iso.refl _))
    (fun _ _ _ ↦ by cat_disch)
    (fun _ ↦ by cat_disch)
    (fun _ ↦ by cat_disch)

/-- The coherent identity moduli problem at one scheme base change. -/
def identityRelativePerfectModuliProblem {S : Scheme.{u}}
    (T : SchemeBaseChange S) : RelativePerfectModuliProblem S PUnit where
  base := identityBaseChangeDiagram T
  presheaf := constantRelativePerfectPresheaf T
  fiberEquivalence X :=
    CategoryTheory.Equivalence.refl (C := RelativePerfectModuliFiber T)
  exactPullback f := by
    change SchemeBaseChange.IsExactPullback (𝟙 T)
    infer_instance
  ambientComparison f := by
    change (𝟭 (RelativePerfectModuliFiber T)) ⋙
          relativePerfectModuliForget T ⋙
            SchemeBaseChange.derivedPullback (𝟙 T) ≅
      (𝟭 (RelativePerfectModuliFiber T)) ⋙
        (𝟭 (RelativePerfectModuliFiber T)) ⋙
          relativePerfectModuliForget T
    exact Functor.isoWhiskerLeft (𝟭 (RelativePerfectModuliFiber T))
      (Functor.isoWhiskerLeft (relativePerfectModuliForget T)
          (SchemeBaseChange.derivedPullbackId T) ≪≫
        Functor.rightUnitor (relativePerfectModuliForget T) ≪≫
        (Functor.leftUnitor (relativePerfectModuliForget T)).symm)

end

end AlgebraicGeometry
