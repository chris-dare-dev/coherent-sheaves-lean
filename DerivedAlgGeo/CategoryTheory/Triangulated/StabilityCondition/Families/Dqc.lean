/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.BoundedGeometry

/-!
# The quasi-coherent cohomology locus in a scheme-derived category

The ambient `SchemeDerivedCategory X` is the derived category of **all**
`𝒪_X`-module sheaves.  The category conventionally denoted `Dqc(X)` is the
full subcategory whose cohomology sheaves are quasi-coherent.  This file makes
that distinction part of the Lean type.

At the current Mathlib pin the full subcategory of quasi-coherent sheaves on a
general scheme is not yet available as an abelian category.  Consequently this
file does not manufacture a triangulated instance on the quasi-coherent
cohomology locus.  Instead it exposes the honest category and names the exact
comparison statements that a later geometric realization must prove.
Unsupported geometric cases therefore remain uninhabited rather than being
silently identified with the all-sheaf derived category.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Coh.ι_additive Coh.ι_preservesFiniteLimits
  Coh.ι_preservesFiniteColimits

/-- An object of the all-module-sheaf derived category has quasi-coherent
cohomology when every one of its canonical cohomology sheaves is
quasi-coherent. -/
def schemeQuasicoherentCohomology (X : Scheme.{u}) :
    ObjectProperty (SchemeDerivedCategory X) :=
  fun E ↦ ∀ n : ℤ,
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((DerivedCategory.homologyFunctor X.Modules n).obj E)

instance (X : Scheme.{u}) :
    (schemeQuasicoherentCohomology X).IsClosedUnderIsomorphisms where
  of_iso e hE n :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor X.Modules n).mapIso e) (hE n)

/-- The honest `Dqc(X)` object class: the full subcategory of the derived
category of all module sheaves cut out by quasi-coherent cohomology. -/
abbrev SchemeQuasicoherentDerivedCategory (X : Scheme.{u}) :=
  (schemeQuasicoherentCohomology X).FullSubcategory

namespace SchemeQuasicoherentDerivedCategory

variable (X : Scheme.{u})

/-- The inclusion of the quasi-coherent cohomology locus into the derived
category of all module sheaves. -/
abbrev ι : SchemeQuasicoherentDerivedCategory X ⥤ SchemeDerivedCategory X :=
  (schemeQuasicoherentCohomology X).ι

/-- Membership in `Dqc(X)` is exactly quasi-coherence of every cohomology
sheaf. -/
theorem mem_iff (E : SchemeDerivedCategory X) :
    schemeQuasicoherentCohomology X E ↔
      ∀ n : ℤ, (SheafOfModules.isQuasicoherent X.ringCatSheaf)
        ((DerivedCategory.homologyFunctor X.Modules n).obj E) :=
  Iff.rfl

end SchemeQuasicoherentDerivedCategory

/-- Exact functors commute with cohomology after passage to derived
categories.  The isomorphism is constructed from a representative complex,
the two localization comparison isomorphisms, and preservation of homology.
-/
noncomputable def mapDerivedCategoryHomologyIso
    {A : Type u} {B : Type v} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A]
    [HasDerivedCategory.{w} B] (F : A ⥤ B)
    (hadd : F.Additive) (hlim : PreservesFiniteLimits F)
    (hcolim : PreservesFiniteColimits F)
    (E : DerivedCategory A) (n : ℤ) :
    (DerivedCategory.homologyFunctor B n).obj (F.mapDerivedCategory.obj E) ≅
      F.obj ((DerivedCategory.homologyFunctor A n).obj E) :=
  by
    letI : F.Additive := hadd
    letI : PreservesFiniteLimits F := hlim
    letI : PreservesFiniteColimits F := hcolim
    let K := DerivedCategory.Q.objPreimage E
    exact (DerivedCategory.homologyFunctor B n).mapIso
        (F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso E).symm) ≪≫
      (DerivedCategory.homologyFunctor B n).mapIso
        (F.mapDerivedCategoryFactors.app K) ≪≫
      (DerivedCategory.homologyFunctorFactors B n).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≪≫
      (K.sc n).mapHomologyIso F ≪≫
      F.mapIso ((DerivedCategory.homologyFunctorFactors A n).app K).symm ≪≫
      F.mapIso ((DerivedCategory.homologyFunctor A n).mapIso
        (DerivedCategory.Q.objObjPreimageIso E))

/-- The exact inclusion of coherent sheaves induces a concrete functor from
their unbounded derived category to the all-module-sheaf derived category. -/
noncomputable def coherentDerivedInclusion
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    SchemeCoherentDerivedCategory X ⥤ SchemeDerivedCategory X :=
  by
    exact @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (Coh.ι X)
      (Coh.ι_additive X) (Coh.ι_preservesFiniteLimits X)
      (Coh.ι_preservesFiniteColimits X)

/-- The derived coherent-sheaf inclusion has quasi-coherent cohomology in
every degree.  This is proved by exactness of `Coh.ι`, not postulated as a
geometric realization. -/
theorem coherentDerivedInclusion_mem_dqc
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    (E : SchemeCoherentDerivedCategory X) :
    schemeQuasicoherentCohomology X ((coherentDerivedInclusion X).obj E) := by
  intro n
  let H := (DerivedCategory.homologyFunctor (Coh X) n).obj E
  have hfp : (SheafOfModules.isFinitePresentation X.ringCatSheaf)
      ((Coh.ι X).obj H) := H.property
  letI : (SheafOfModules.isFinitePresentation X.ringCatSheaf)
      ((Coh.ι X).obj H) := hfp
  have hqc : (SheafOfModules.isQuasicoherent X.ringCatSheaf) ((Coh.ι X).obj H) :=
    inferInstance
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (mapDerivedCategoryHomologyIso (Coh.ι X) (Coh.ι_additive X)
      (Coh.ι_preservesFiniteLimits X) (Coh.ι_preservesFiniteColimits X) E n).symm hqc

/-- The genuine lift of the coherent derived category into the
quasi-coherent-cohomology locus. -/
noncomputable def coherentDerivedToDqc
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    SchemeCoherentDerivedCategory X ⥤ SchemeQuasicoherentDerivedCategory X :=
  (schemeQuasicoherentCohomology X).lift
    (coherentDerivedInclusion X) (coherentDerivedInclusion_mem_dqc X)

/-- Forgetting the quasi-coherent-cohomology proof recovers the derived
coherent-sheaf inclusion definitionally. -/
noncomputable def coherentDerivedToDqcCompInclusion
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    coherentDerivedToDqc X ⋙ SchemeQuasicoherentDerivedCategory.ι X ≅
      coherentDerivedInclusion X :=
  (schemeQuasicoherentCohomology X).liftCompιIso
    (coherentDerivedInclusion X) (coherentDerivedInclusion_mem_dqc X)

/-- Bounded objects in the honest `Dqc(X)` locus are detected by the
canonical t-structure of the ambient all-sheaf derived category. -/
def schemeBoundedQuasicoherent
    (X : Scheme.{u}) : ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  fun E ↦ (DerivedCategory.TStructure.t (C := X.Modules)).bounded E.obj

instance (X : Scheme.{u}) :
    (schemeBoundedQuasicoherent X).IsClosedUnderIsomorphisms where
  of_iso e hE :=
    (DerivedCategory.TStructure.t (C := X.Modules)).bounded.prop_of_iso
      ((SchemeQuasicoherentDerivedCategory.ι X).mapIso e) hE

/-- The bounded part of `Dqc(X)`, defined by ambient cohomological
boundedness. -/
abbrev SchemeBoundedQuasicoherentDerivedCategory (X : Scheme.{u}) :=
  (schemeBoundedQuasicoherent X).FullSubcategory

namespace SchemeBoundedQuasicoherentDerivedCategory

variable (X : Scheme.{u})

/-- The inclusion of bounded quasi-coherent complexes into `Dqc(X)`. -/
abbrev ι : SchemeBoundedQuasicoherentDerivedCategory X ⥤
    SchemeQuasicoherentDerivedCategory X :=
  (schemeBoundedQuasicoherent X).ι

/-- Boundedness is detected after the two honest inclusions into the ambient
derived category. -/
theorem mem_iff (E : SchemeQuasicoherentDerivedCategory X) :
    schemeBoundedQuasicoherent X E ↔
      (DerivedCategory.TStructure.t (C := X.Modules)).bounded E.obj :=
  Iff.rfl

end SchemeBoundedQuasicoherentDerivedCategory

/-- The intrinsic bounded-coherent locus in `Dqc(X)`: ambient boundedness and
finite presentation of every cohomology sheaf.  On a locally Noetherian
scheme this is the expected objectwise description of `Dᵇ(Coh X)`. -/
def schemeBoundedCoherentCohomology
    (X : Scheme.{u}) :
    ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  fun E ↦
    (DerivedCategory.TStructure.t (C := X.Modules)).bounded E.obj ∧
      ∀ n : ℤ, (SheafOfModules.isFinitePresentation X.ringCatSheaf)
        ((DerivedCategory.homologyFunctor X.Modules n).obj E.obj)

instance (X : Scheme.{u}) :
    (schemeBoundedCoherentCohomology X).IsClosedUnderIsomorphisms where
  of_iso e hE := by
    constructor
    · exact (DerivedCategory.TStructure.t (C := X.Modules)).bounded.prop_of_iso
        ((SchemeQuasicoherentDerivedCategory.ι X).mapIso e) hE.1
    · intro n
      exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
        ((DerivedCategory.homologyFunctor X.Modules n).mapIso
          ((SchemeQuasicoherentDerivedCategory.ι X).mapIso e)) (hE.2 n)

/-- The full subcategory of `Dqc(X)` with bounded coherent cohomology. -/
abbrev SchemeBoundedCoherentDqcCategory
    (X : Scheme.{u}) :=
  (schemeBoundedCoherentCohomology X).FullSubcategory

/-- Bounded coherent cohomology implies ambient boundedness. -/
theorem schemeBoundedCoherentCohomology_le_bounded
    (X : Scheme.{u}) :
    schemeBoundedCoherentCohomology X ≤ schemeBoundedQuasicoherent X :=
  fun _ hE ↦ hE.1

/-- The bounded coherent category maps concretely into the intrinsic
bounded-coherent locus in `Dqc(X)`. -/
noncomputable def boundedCoherentDerivedToDqc
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    SchemeBoundedCoherentDerivedCategory X ⥤
      SchemeBoundedCoherentDqcCategory X :=
  by
    exact (schemeBoundedCoherentCohomology X).lift
      (DerivedCategory.Bounded.ι ⋙ coherentDerivedToDqc X)
      (fun E ↦ by
        constructor
        · exact @mapDerivedCategory_bounded _ _ _ _ _ _ _ _ (Coh.ι X)
            (Coh.ι_additive X) (Coh.ι_preservesFiniteLimits X)
            (Coh.ι_preservesFiniteColimits X) E.obj E.property
        · intro n
          let H := (DerivedCategory.homologyFunctor (Coh X) n).obj E.obj
          have hfp : (SheafOfModules.isFinitePresentation X.ringCatSheaf)
              ((Coh.ι X).obj H) := H.property
          exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
            (mapDerivedCategoryHomologyIso (Coh.ι X) (Coh.ι_additive X)
              (Coh.ι_preservesFiniteLimits X) (Coh.ι_preservesFiniteColimits X)
              E.obj n).symm hfp)

/-- Forget bounded-coherent cohomology to the ambient `Dqc(X)` locus. -/
abbrev SchemeBoundedCoherentDqcCategory.ι
    (X : Scheme.{u}) :
    SchemeBoundedCoherentDqcCategory X ⥤
      SchemeQuasicoherentDerivedCategory X :=
  (schemeBoundedCoherentCohomology X).ι

/-- The perfect thick envelope maps through bounded coherent complexes into
the bounded coherent `Dqc` locus. -/
noncomputable def perfectDerivedToDqc
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    SchemePerfectDerivedCategory X ⥤
      SchemeBoundedCoherentDqcCategory X :=
  SchemePerfectDerivedCategory.toBounded X ⋙ boundedCoherentDerivedToDqc X

/-- Perfect objects inside `Dqc(X)`, defined without circular use of
compactness as the essential image of the repository's finite-locally-free
thick envelope. -/
def schemePerfectInDqc
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    ObjectProperty (SchemeQuasicoherentDerivedCategory X) :=
  (perfectDerivedToDqc X ⋙ SchemeBoundedCoherentDqcCategory.ι X).essImage

/-- The exact missing general-scheme identification behind the standard
notation `Dᵇ(Coh X) ⊂ Dqc(X)`.  The comparison field forces the equivalence
to be the concrete derived inclusion constructed above.  No unsupported
scheme is marked as satisfying this proposition. -/
structure BoundedCoherentDqcIdentification
    (X : Scheme.{u}) [IsLocallyNoetherian X] where
  /-- The bounded coherent derived category is equivalent to the intrinsic
  bounded coherent cohomology locus. -/
  equivalence : SchemeBoundedCoherentDerivedCategory X ≌
    SchemeBoundedCoherentDqcCategory X
  /-- The equivalence is the concrete exact derived inclusion. -/
  comparison : equivalence.functor ≅ boundedCoherentDerivedToDqc X

/-- Existence of the general-scheme bounded-coherent identification, kept as
an explicit proposition rather than a typeclass instance. -/
def HasBoundedCoherentDqcIdentification
    (X : Scheme.{u}) [IsLocallyNoetherian X] : Prop :=
  Nonempty (BoundedCoherentDqcIdentification X)

/-- The exact compact/perfect comparison still required by the scheme-level
A.14 realization. This file supplies no unsupported inhabitant; construction
of the needed large triangulated and coproduct structure is a separate
obligation. -/
def PerfectObjectsAreCompactInDqc
    (X : Scheme.{u}) [IsLocallyNoetherian X] : Prop :=
  schemePerfectInDqc X = ObjectProperty.compactObjects.{0}

end

end CategoryTheory.Triangulated.StabilityCondition.Families
