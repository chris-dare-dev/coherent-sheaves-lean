/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.BoundedGeometry
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.PreStabilityBaseChange
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.InducingBoundary

/-!
# Geometric pre-stability base change on bounded coherent fibers

This file connects the actual bounded coherent pullback from
`Families.BoundedGeometry` to `FiberPreStabilityBaseChangeData`.

The bridge has three layers.

* `BoundedCoherentPullbackPreimageData` is the explicit preimage witness for
  one geometric pullback.  Its identity and composition constructors use the
  bounded derived-pullback unit and compositor.
* `BoundedCoherentPullbackInducingData` records the left adjoint,
  zero-reflection, and phase-monad premises for that actual pullback.  The
  Appendix-A theorem converts these premises into preimage data.
* `BoundedCoherentDerivedRealization` identifies an abstract strict fiber
  family with the genuine `Dᵇ(Coh)` fibers and their pullbacks.
  `GeometricPreStabilityBaseChangeData.toFiberPreStabilityBaseChangeData`
  then exports the downstream witness without accepting `Slicing.PreimageData`
  from the caller.

The presentable/Ind theorem remains the precisely named input
`HasLeftAdjointInducingTheorem`.  This file does not manufacture that deep
theorem, a left adjoint, or phase-monad control from flatness.  It also proves
no openness or relative-HN existence statement; those are the next geometric
milestone.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u v uV

/-- An equivalence between possibly different triangulated categories, with
all exactness instances bundled so they can be transported with the
equivalence. -/
structure TriangulatedEquivalence
    (C : Type u) (D : Type v)
    [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D] where
  /-- The underlying equivalence. -/
  e : C ≌ D
  /-- The forward functor is additive. -/
  functorAdditive : e.functor.Additive
  /-- The inverse functor is additive. -/
  inverseAdditive : e.inverse.Additive
  /-- The forward functor commutes with shifts. -/
  functorCommShift : e.functor.CommShift ℤ
  /-- The inverse functor commutes with shifts. -/
  inverseCommShift : e.inverse.CommShift ℤ
  /-- The forward functor is triangulated. -/
  functorTriangulated : e.functor.IsTriangulated
  /-- The inverse functor is triangulated. -/
  inverseTriangulated : e.inverse.IsTriangulated

namespace TriangulatedEquivalence

attribute [instance] functorAdditive inverseAdditive functorCommShift
  inverseCommShift functorTriangulated inverseTriangulated

variable {C : Type u} {D : Type v}
  [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

/-- Preimage data for the inverse functor of a bundled triangulated
equivalence. -/
theorem preimageDataInverse (E : TriangulatedEquivalence C D)
    (s : Slicing C) : s.PreimageData E.e.inverse := by
  letI : E.e.symm.functor.Additive := E.inverseAdditive
  letI : E.e.symm.inverse.Additive := E.functorAdditive
  letI : E.e.symm.functor.CommShift ℤ := E.inverseCommShift
  letI : E.e.symm.inverse.CommShift ℤ := E.functorCommShift
  letI : E.e.symm.functor.IsTriangulated := E.inverseTriangulated
  letI : E.e.symm.inverse.IsTriangulated := E.functorTriangulated
  exact s.preimageData_equivalence E.e.symm

end TriangulatedEquivalence

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- Explicit preimage-slicing data for bounded coherent derived pullback along
one morphism of locally Noetherian scheme base changes. -/
structure BoundedCoherentPullbackPreimageData
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f]
    (s : Slicing T.BoundedCoherentDerivedFiber) : Prop where
  /-- The two non-formal slicing axioms for the actual bounded coherent
  pullback. -/
  preimageData : s.PreimageData (boundedCoherentDerivedPullback f)

namespace BoundedCoherentPullbackPreimageData

variable {T U : SchemeBaseChange S} {f : T ⟶ U}
  [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
  [HasCoherentPullback f]
  {s : Slicing T.BoundedCoherentDerivedFiber}

/-- The slicing constructed on the target bounded coherent fiber. -/
def preimage (h : BoundedCoherentPullbackPreimageData f s) :
    Slicing U.BoundedCoherentDerivedFiber :=
  s.preimage (boundedCoherentDerivedPullback f) h.preimageData

/-- The bounded coherent pullback unit supplies the identity preimage
witness. -/
theorem identity (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left]
    [HasCoherentPullback (𝟙 T)] [PreservesPerfectPullback (𝟙 T)]
    [GeometricDerivedPullbackIdentity T]
    (s : Slicing T.BoundedCoherentDerivedFiber) :
    BoundedCoherentPullbackPreimageData (𝟙 T) s where
  preimageData := s.preimageData_id.ofIso
    (GeometricDerivedPullbackIdentity.boundedIso (T := T)).symm

/-- The slicing induced along the identity is the original slicing. -/
@[simp]
theorem preimage_identity (T : SchemeBaseChange S)
    [IsLocallyNoetherian T.left]
    [HasCoherentPullback (𝟙 T)] [PreservesPerfectPullback (𝟙 T)]
    [GeometricDerivedPullbackIdentity T]
    (s : Slicing T.BoundedCoherentDerivedFiber) :
    (identity T s).preimage = s := by
  calc
    (identity T s).preimage =
        s.preimage (Functor.id T.BoundedCoherentDerivedFiber)
          s.preimageData_id :=
      Slicing.preimage_iso s _ _ s.preimageData_id
        (GeometricDerivedPullbackIdentity.boundedIso (T := T)).symm
    _ = s := s.preimage_id

/-- Geometric bounded coherent preimage witnesses compose through the actual
bounded derived-pullback compositor. -/
theorem comp {T U V : SchemeBaseChange S} (f : T ⟶ U) (g : U ⟶ V)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [IsLocallyNoetherian V.left]
    [HasCoherentPullback f] [HasCoherentPullback g]
    [HasCoherentPullback (f ≫ g)]
    [PreservesPerfectPullback f] [PreservesPerfectPullback g]
    [PreservesPerfectPullback (f ≫ g)]
    [GeometricDerivedPullbackComposition f g]
    {s : Slicing T.BoundedCoherentDerivedFiber}
    (hf : BoundedCoherentPullbackPreimageData f s)
    (hg : BoundedCoherentPullbackPreimageData g hf.preimage) :
    BoundedCoherentPullbackPreimageData (f ≫ g) s where
  preimageData := by
    have hgData := hg.preimageData
    change (s.preimage (boundedCoherentDerivedPullback f)
      hf.preimageData).PreimageData (boundedCoherentDerivedPullback g) at hgData
    exact (hf.preimageData.comp hgData).ofIso
      (GeometricDerivedPullbackComposition.boundedIso (f := f) (g := g))

/-- One-step and two-step geometric bounded coherent preimages agree. -/
@[simp]
theorem preimage_comp {T U V : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [IsLocallyNoetherian V.left]
    [HasCoherentPullback f] [HasCoherentPullback g]
    [HasCoherentPullback (f ≫ g)]
    [PreservesPerfectPullback f] [PreservesPerfectPullback g]
    [PreservesPerfectPullback (f ≫ g)]
    [GeometricDerivedPullbackComposition f g]
    {s : Slicing T.BoundedCoherentDerivedFiber}
    (hf : BoundedCoherentPullbackPreimageData f s)
    (hg : BoundedCoherentPullbackPreimageData g hf.preimage) :
    (hf.comp f g hg).preimage = hg.preimage := by
  have hgData := hg.preimageData
  change (s.preimage (boundedCoherentDerivedPullback f)
    hf.preimageData).PreimageData (boundedCoherentDerivedPullback g) at hgData
  calc
    (hf.comp f g hg).preimage =
        s.preimage
          (boundedCoherentDerivedPullback g ⋙
            boundedCoherentDerivedPullback f)
          (hf.preimageData.comp hgData) :=
      Slicing.preimage_iso s _ _
        (hf.preimageData.comp hgData)
        (GeometricDerivedPullbackComposition.boundedIso (f := f) (g := g))
    _ = hg.preimage := by
      apply Slicing.ext
      rfl

end BoundedCoherentPullbackPreimageData

/-- The Appendix-A inducing premises specialized to actual bounded coherent
derived pullback. -/
structure BoundedCoherentPullbackInducingData
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
    [HasCoherentPullback f]
    (s : Slicing T.BoundedCoherentDerivedFiber) where
  /-- A left adjoint to bounded coherent pullback. -/
  leftAdjoint : T.BoundedCoherentDerivedFiber ⥤
    U.BoundedCoherentDerivedFiber
  /-- Adjunction, zero-reflection, and phase-monad control. -/
  premise : s.LeftAdjointInducingPremise
    (boundedCoherentDerivedPullback f) leftAdjoint

namespace BoundedCoherentPullbackInducingData

variable {T U : SchemeBaseChange S} {f : T ⟶ U}
  [IsLocallyNoetherian T.left] [IsLocallyNoetherian U.left]
  [HasCoherentPullback f]
  {s : Slicing T.BoundedCoherentDerivedFiber}

/-- Apply the precisely named presentable/Ind theorem to the actual bounded
coherent pullback. -/
theorem toPreimageData (h : BoundedCoherentPullbackInducingData f s)
    (H : HasLeftAdjointInducingTheorem.{u + 1, u + 1, u + 1, u + 1}) :
    BoundedCoherentPullbackPreimageData f s where
  preimageData := H s (boundedCoherentDerivedPullback f) h.leftAdjoint h.premise

end BoundedCoherentPullbackInducingData

end SchemeBaseChange

/-- A strict triangulated fiber family realized by the genuine bounded
coherent derived categories, with every abstract pullback identified with the
actual bounded coherent pullback. -/
structure BoundedCoherentDerivedRealization
    {S : Scheme.{u}} (F : SchemeTriangulatedFiberFamily S)
    [∀ T : SchemeBaseChange S, IsLocallyNoetherian T.left]
    [∀ {T U : SchemeBaseChange S} (f : T ⟶ U),
      SchemeBaseChange.HasCoherentPullback f] where
  /-- Triangulated equivalence from each abstract fiber to `Dᵇ(Coh)`. -/
  fiberEquivalence (T : SchemeBaseChange S) :
    TriangulatedEquivalence (F.Fiber T) T.BoundedCoherentDerivedFiber
  /-- Abstract pullback is the actual bounded coherent pullback, transported
  through the two fiber equivalences. -/
  pullbackIso {T U : SchemeBaseChange S} (f : T ⟶ U) :
    F.pull f ≅
      (fiberEquivalence U).e.functor ⋙
        (SchemeBaseChange.boundedCoherentDerivedPullback f ⋙
          (fiberEquivalence T).e.inverse)

namespace BoundedCoherentDerivedRealization

variable {S : Scheme.{u}} {F : SchemeTriangulatedFiberFamily S}
  [∀ T : SchemeBaseChange S, IsLocallyNoetherian T.left]
  [∀ {T U : SchemeBaseChange S} (f : T ⟶ U),
    SchemeBaseChange.HasCoherentPullback f]

/-- Transport an inducing theorem for the genuine bounded coherent pullback
through a bounded coherent realization.  The result is preimage data for the
abstract family pullback, not a caller-supplied preimage witness. -/
theorem preimageData (R : BoundedCoherentDerivedRealization F)
    (H : HasLeftAdjointInducingTheorem.{u + 1, u + 1, u + 1, u + 1})
    {T U : SchemeBaseChange S} (f : T ⟶ U)
    (s : Slicing (F.Fiber T))
    (h : SchemeBaseChange.BoundedCoherentPullbackInducingData f
      (s.preimage (R.fiberEquivalence T).e.inverse
        ((R.fiberEquivalence T).preimageDataInverse s))) :
    s.PreimageData (F.pull f) := by
  let hT := (R.fiberEquivalence T).preimageDataInverse s
  let hGeom := h.toPreimageData H
  let hPost : s.PreimageData
      (SchemeBaseChange.boundedCoherentDerivedPullback f ⋙
        (R.fiberEquivalence T).e.inverse) :=
    hT.comp hGeom.preimageData
  let sU := s.preimage _ hPost
  let hU := sU.preimageData_equivalence (R.fiberEquivalence U).e
  have hU' : (s.preimage _ hPost).PreimageData
      (R.fiberEquivalence U).e.functor := by
    simpa [sU] using hU
  exact (hPost.comp hU').ofIso (R.pullbackIso f).symm

end BoundedCoherentDerivedRealization

/-- Geometric inducing data for a pre-stability family.  Unlike
`FiberPreStabilityBaseChangeData`, this structure does not contain a
`Slicing.PreimageData` field: every such witness is constructed from the
actual bounded coherent pullback, its inducing premises, and the named
Appendix-A theorem. -/
structure GeometricPreStabilityBaseChangeData
    {S : Scheme.{u}} (F : SchemeTriangulatedFiberFamily S)
    [∀ T : SchemeBaseChange S, IsLocallyNoetherian T.left]
    [∀ {T U : SchemeBaseChange S} (f : T ⟶ U),
      SchemeBaseChange.HasCoherentPullback f]
    (R : BoundedCoherentDerivedRealization F)
    (H : HasLeftAdjointInducingTheorem.{u + 1, u + 1, u + 1, u + 1})
    {V : Type uV} [AddCommGroup V]
    (classMap : ∀ T, K₀ (F.Fiber T) →+ V)
    (sigma : ∀ T, PreStabilityCondition.WithClassMap
      (F.Fiber T) (classMap T)) where
  /-- The common numerical class is invariant under pullback. -/
  classMapCompatible : F.CompatibleClassMaps V classMap
  /-- All fibers use the same central charge. -/
  chargeCompatible : ∀ {T U} (_ : T ⟶ U), (sigma T).Z = (sigma U).Z
  /-- The geometric inducing premises on the actual bounded coherent
  pullback. -/
  inducing : ∀ {T U} (f : T ⟶ U),
    SchemeBaseChange.BoundedCoherentPullbackInducingData f
      ((sigma T).slicing.preimage (R.fiberEquivalence T).e.inverse
        ((R.fiberEquivalence T).preimageDataInverse (sigma T).slicing))
  /-- The supplied target slicing is the one induced geometrically.  The
  preimage witness occurring here is constructed from `inducing`; it is not a
  field of this structure. -/
  slicingCompatible : ∀ {T U} (f : T ⟶ U),
    (sigma U).slicing = (sigma T).slicing.preimage (F.pull f)
      (R.preimageData H f (sigma T).slicing (inducing f))

namespace GeometricPreStabilityBaseChangeData

variable {S : Scheme.{u}} {F : SchemeTriangulatedFiberFamily S}
  [∀ T : SchemeBaseChange S, IsLocallyNoetherian T.left]
  [∀ {T U : SchemeBaseChange S} (f : T ⟶ U),
    SchemeBaseChange.HasCoherentPullback f]
  {R : BoundedCoherentDerivedRealization F}
  {H : HasLeftAdjointInducingTheorem.{u + 1, u + 1, u + 1, u + 1}}
  {V : Type uV} [AddCommGroup V]
  {classMap : ∀ T, K₀ (F.Fiber T) →+ V}
  {sigma : ∀ T, PreStabilityCondition.WithClassMap
    (F.Fiber T) (classMap T)}

/-- Export the ordinary categorical base-change witness.  Its preimage field
is built from bounded coherent geometry and the inducing theorem. -/
theorem toFiberPreStabilityBaseChangeData
    (h : GeometricPreStabilityBaseChangeData F R H classMap sigma) :
    FiberPreStabilityBaseChangeData F classMap sigma where
  classMap_compatible := h.classMapCompatible
  charge_compatible := h.chargeCompatible
  preimageData := fun f ↦ R.preimageData H f _ (h.inducing f)
  slicing_compatible := h.slicingCompatible

/-- Phase membership is detected by the geometrically realized bounded
coherent pullback. -/
theorem phase_iff
    (h : GeometricPreStabilityBaseChangeData F R H classMap sigma)
    {T U : SchemeBaseChange S} (f : T ⟶ U) (phi : ℝ) (E : F.Fiber U) :
    (sigma U).slicing.P phi E ↔
      (sigma T).slicing.P phi ((F.pull f).obj E) :=
  h.toFiberPreStabilityBaseChangeData.phase_iff f phi E

/-- The geometric witness inherits identity and composition compatibility
from the strict fiber family after its pullbacks have been identified with
bounded coherent derived pullback. -/
theorem phase_iff_comp
    (h : GeometricPreStabilityBaseChangeData F R H classMap sigma)
    {T U V' : SchemeBaseChange S} (f : T ⟶ U) (g : U ⟶ V')
    (phi : ℝ) (E : F.Fiber V') :
    (sigma V').slicing.P phi E ↔
      (sigma T).slicing.P phi ((F.pull f).obj ((F.pull g).obj E)) :=
  h.toFiberPreStabilityBaseChangeData.phase_iff_comp f g phi E

end GeometricPreStabilityBaseChangeData

end

end CategoryTheory.Triangulated.StabilityCondition.Families
