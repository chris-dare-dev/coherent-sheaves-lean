/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech.ComplexNaturality
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.FiniteDimensional

/-!
# The base-field-linear form of the Čech comparison

Everything in the Čech lane is valued in `AddCommGrpCat`, and the interface a finiteness theorem
has to discharge is not: `Module.Finite k` needs the `k`-module structure that
`coherentScalarAction` supplies. This file supplies the missing half.

The `k`-action on a cohomology group is not extra data. For `r : k`, multiplication by `r` is an
endomorphism of the sheaf -- `varietyScalarAction`, built from the central action of global
functions through the variety's structure morphism -- and the action on cohomology is the map
that endomorphism induces. So both sides of the Čech comparison carry an action for the same
reason, and `k`-linearity of the comparison is exactly the statement that it commutes with the
maps induced by an endomorphism, which is `cechComparisonAddEquiv_naturality`.
-/

universe h u

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]

/-- Čech cohomology of an abelian sheaf on a space, as a functor.

The comparison is stated against `cechCohomology`, which is an abbreviation for the same
homology group; naming the functor is what lets an endomorphism of the sheaf act. -/
noncomputable def cechCohomologyFunctor {X : TopCat.{u}} {ind : Type u}
    (U : ind → Opens X) (n : ℕ) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    CategoryTheory.cechComplexFunctor U ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n

noncomputable instance cechCohomologyFunctor_additive {X : TopCat.{u}} {ind : Type u}
    (U : ind → Opens X) (n : ℕ) : (cechCohomologyFunctor U n).Additive := by
  letI : (CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{u}) U).Additive :=
    CategoryTheory.Sheaf.cechComplexFunctor_additive U
  dsimp only [cechCohomologyFunctor]
  infer_instance

/-- The base-field action on the Čech cohomology of a module sheaf over a variety.

It is the action of `varietyScalarAction` pushed through two additive functors: the forgetful
functor to abelian sheaves, and Čech cohomology. -/
noncomputable def cechScalarAction (Y : Variety k) (M : Y.toScheme.Modules)
    {ind : Type u} (U : ind → Opens Y.toScheme) (n : ℕ) :
    k →+* AddMonoid.End
      ((cechCohomologyFunctor U n).obj ((Scheme.Modules.toSheaf Y.toScheme).obj M)) :=
  (addCommGrpEndRingHom _).comp
    (((additiveMapEndRingHom (cechCohomologyFunctor U n)
        ((Scheme.Modules.toSheaf Y.toScheme).obj M)).comp
      (additiveMapEndRingHom (Scheme.Modules.toSheaf Y.toScheme) M)).comp
        (varietyScalarAction Y M))

/-- The base-field module structure on Čech cohomology. -/
@[reducible]
noncomputable def cechCohomologyModule (Y : Variety k) (M : Y.toScheme.Modules)
    {ind : Type u} (U : ind → Opens Y.toScheme) (n : ℕ) :
    Module k ((cechCohomologyFunctor U n).obj ((Scheme.Modules.toSheaf Y.toScheme).obj M)) :=
  Module.compHom _ (cechScalarAction Y M U n)

/-- Scalar multiplication on Čech cohomology is the map induced by multiplication on the
sheaf. -/
lemma cechScalarAction_apply (Y : Variety k) (M : Y.toScheme.Modules)
    {ind : Type u} (U : ind → Opens Y.toScheme) (n : ℕ) (r : k)
    (x : (cechCohomologyFunctor U n).obj ((Scheme.Modules.toSheaf Y.toScheme).obj M)) :
    cechScalarAction Y M U n r x =
      ((cechCohomologyFunctor U n).map
        ((Scheme.Modules.toSheaf Y.toScheme).map (varietyScalarAction Y M r))).hom x :=
  rfl

/-- **The Čech-to-derived comparison is `k`-linear.**

The scalar action on both sides is induced by one endomorphism of the sheaf, so this is the
naturality square of `cechComparisonAddEquiv` at multiplication by `r`, with the canonical
lift of that endomorphism to the chosen resolution. -/
theorem cechComparisonAddEquiv_smul (Y : Variety k) (M : Y.toScheme.Modules)
    {ind : Type u} (U : ind → Opens Y.toScheme)
    (I : InjectiveResolution ((Scheme.Modules.toSheaf Y.toScheme).obj M))
    (hExt : HasExt.{h} (TopCat.Sheaf AddCommGrpCat.{u} Y.toScheme))
    (hcover : @IsCechAcyclicCover (Opens Y.toScheme) _
      (Opens.grothendieckTopology Y.toScheme) _ hExt ind _ U
      ((Scheme.Modules.toSheaf Y.toScheme).obj M))
    (n : ℕ) (r : k)
    (x : (cechCohomology U ((Scheme.Modules.toSheaf Y.toScheme).obj M).obj n :
      AddCommGrpCat.{u})) :
    cechComparisonAddEquiv Limits.isTerminalTop U I hExt hcover n
        (cechScalarAction Y M U n r x) =
      @Sheaf.H.map (Opens Y.toScheme) _ (Opens.grothendieckTopology Y.toScheme) _ hExt _ _
        ((Scheme.Modules.toSheaf Y.toScheme).map (varietyScalarAction Y M r)) n
        (cechComparisonAddEquiv Limits.isTerminalTop U I hExt hcover n x) :=
  cechComparisonAddEquiv_naturality Limits.isTerminalTop U
    ((Scheme.Modules.toSheaf Y.toScheme).map (varietyScalarAction Y M r)) I I
    (CategoryTheory.InjectiveResolution.descHom _ I I).hom'
    (CategoryTheory.InjectiveResolution.Hom.ι'_comp_hom' _) hExt hcover hcover n x

/-- **The Čech comparison against `coherentScalarAction`.**

This is the form the finiteness interface consumes: the target is the group `coherentH` names,
carrying the action `coherentScalarAction` supplies, and the comparison respects it.

The `HasExt` reconciliation is made here and is explicit. `coherentH` fixes its witness as
`HasExt.standard _` at `HasExt.{u + 1}`, while the Čech lane passes the witness positionally so
that instance search cannot pick `HasExt.{u}` -- a different group. The two conventions meet by
instantiating the positional witness at `HasExt.standard _`, written out below rather than left
to elaboration. -/
theorem cechComparisonAddEquiv_coherentSmul (Y : Variety k) (F : Coh Y.toScheme)
    {ind : Type u} (U : ind → Opens Y.toScheme)
    (I : InjectiveResolution
      ((Scheme.Modules.toSheaf Y.toScheme).obj ((Coh.ι Y.toScheme).obj F)))
    (hcover : @IsCechAcyclicCover (Opens Y.toScheme) _
      (Opens.grothendieckTopology Y.toScheme) _
      (HasExt.standard (Sheaf (Opens.grothendieckTopology Y.toScheme) AddCommGrpCat.{u}))
      ind _ U ((Scheme.Modules.toSheaf Y.toScheme).obj ((Coh.ι Y.toScheme).obj F)))
    (n : ℕ) (r : k)
    (x : (cechCohomology U
      ((Scheme.Modules.toSheaf Y.toScheme).obj ((Coh.ι Y.toScheme).obj F)).obj n :
        AddCommGrpCat.{u})) :
    cechComparisonAddEquiv Limits.isTerminalTop U I
        (HasExt.standard (Sheaf (Opens.grothendieckTopology Y.toScheme) AddCommGrpCat.{u}))
        hcover n
        (cechScalarAction Y ((Coh.ι Y.toScheme).obj F) U n r x) =
      coherentHScalarAction Y n F r
        (cechComparisonAddEquiv Limits.isTerminalTop U I
          (HasExt.standard (Sheaf (Opens.grothendieckTopology Y.toScheme) AddCommGrpCat.{u}))
          hcover n x) :=
  cechComparisonAddEquiv_smul Y ((Coh.ι Y.toScheme).obj F) U I
    (HasExt.standard (Sheaf (Opens.grothendieckTopology Y.toScheme) AddCommGrpCat.{u}))
    hcover n r x

end AlgebraicGeometry.Cohomology
