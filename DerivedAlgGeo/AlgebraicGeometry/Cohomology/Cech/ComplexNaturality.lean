/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech.GlobalComparison
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.SpectralSequence.TotalFlipNaturality

/-!
# The Čech comparison as a construction on complexes of sheaves

Every step of the Čech-to-derived comparison built in
`DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech.GlobalComparison` reads its injective
resolution `I` only through the cochain complex `I.cochainComplex`. This file makes that
dependence explicit: each construction is restated for an arbitrary cochain complex of sheaves,
agreeing with the original by definition, and each is shown to commute with an arbitrary
morphism of such complexes.

This is the content that the bare `Nonempty (_ ≃+ _)` form of the comparison cannot supply.
A `k`-action on cohomology arrives as the map induced by a single endomorphism of the sheaf,
so `k`-linearity of the comparison is exactly the statement that the comparison commutes with
the maps induced by that endomorphism — which is what the naturality squares below record.
-/

universe h a u

open CategoryTheory Category Limits Opposite TopologicalSpace

namespace CategoryTheory.Sheaf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{a} C] {J : GrothendieckTopology C}
  [HasFiniteProducts C] [HasSheafify J AddCommGrpCat.{a}] {index : Type a}

/-- Sections over `X`, applied degreewise to a cochain complex of sheaves. -/
noncomputable abbrev sectionsComplexUnlifted (X : C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ) :
    CochainComplex AddCommGrpCat.{a} ℤ :=
  ((sectionsAtFunctorUnlifted X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- The Čech bicomplex `C^{p,q} = Čech^p(U, K^q)` of a cochain complex of sheaves. -/
noncomputable abbrev cechBicomplexOfComplex (U : index → C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ) :
    HomologicalComplex₂ AddCommGrpCat.{a} (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  HomologicalComplex₂.flip
    (((cechCochainFunctorInt U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

/-- The injective Čech bicomplex reads its resolution only through the underlying complex. -/
lemma cechInjectiveBicomplex_eq_cechBicomplexOfComplex
    {F : Sheaf J AddCommGrpCat.{a}} (U : index → C) (I : InjectiveResolution F) :
    cechInjectiveBicomplex U I = cechBicomplexOfComplex U I.cochainComplex :=
  rfl

/-- The sections complex of an injective resolution reads it only through the underlying
complex. -/
lemma injectiveResolutionSectionsComplexUnlifted_eq
    {F : Sheaf J AddCommGrpCat.{a}} (X : C) (I : InjectiveResolution F) :
    injectiveResolutionSectionsComplexUnlifted X I =
      sectionsComplexUnlifted X I.cochainComplex :=
  rfl

variable {K L : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ}

/-- A morphism of cochain complexes of sheaves induces a morphism of Čech bicomplexes. -/
noncomputable abbrev cechBicomplexMap (U : index → C) (Φ : K ⟶ L) :
    cechBicomplexOfComplex U K ⟶ cechBicomplexOfComplex U L :=
  (HomologicalComplex₂.flipFunctor AddCommGrpCat.{a}
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
      (((cechCochainFunctorInt U).mapHomologicalComplex (ComplexShape.up ℤ)).map Φ)

/-- A morphism of cochain complexes of sheaves induces a morphism of sections complexes. -/
noncomputable abbrev sectionsComplexMap (X : C) (Φ : K ⟶ L) :
    sectionsComplexUnlifted X K ⟶ sectionsComplexUnlifted X L :=
  ((sectionsAtFunctorUnlifted X).mapHomologicalComplex (ComplexShape.up ℤ)).map Φ

/-- Global sections of a complex of sheaves map to its degree-zero Čech column. -/
noncomputable def sectionsToCechZeroColumn
    {T : C} (hT : IsTerminal T) (U : index → C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ) :
    sectionsComplexUnlifted T K ⟶ (cechBicomplexOfComplex U K).X 0 where
  f q := globalSectionsToCechZeroInt hT U (K.X q)
  comm' q r _ := globalSectionsToCechZeroInt_naturality hT U (K.d q r)

/-- The degree-zero Čech column map of an injective resolution reads it only through the
underlying complex. -/
lemma injectiveResolutionSectionsToCechZeroColumn_eq
    {T : C} (hT : IsTerminal T) {F : Sheaf J AddCommGrpCat.{a}}
    (U : index → C) (I : InjectiveResolution F) :
    injectiveResolutionSectionsToCechZeroColumn hT U I =
      sectionsToCechZeroColumn hT U I.cochainComplex :=
  rfl

/-- The degree-zero Čech column map commutes with an arbitrary morphism of complexes. -/
lemma sectionsToCechZeroColumn_naturality
    {T : C} (hT : IsTerminal T) (U : index → C) (Φ : K ⟶ L) :
    sectionsComplexMap T Φ ≫ sectionsToCechZeroColumn hT U L =
      sectionsToCechZeroColumn hT U K ≫ (cechBicomplexMap U Φ).f 0 := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact (globalSectionsToCechZeroInt_naturality hT U (Φ.f q)).symm

/-- The augmented row map from the global-sections complex, placed in Čech degree zero, to the
full Čech bicomplex of a cochain complex of sheaves. -/
noncomputable def sectionsToCechBicomplexMap
    {T : C} (hT : IsTerminal T) (U : index → C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ) :
    HomologicalComplex₂.singleZeroBicomplex (sectionsComplexUnlifted T K) ⟶
      cechBicomplexOfComplex U K := by
  let A := sectionsComplexUnlifted T K
  let g := sectionsToCechZeroColumn hT U (index := index) K
  refine HomologicalComplex₂.homMk (fun pq ↦
    if hp : pq.1 = 0 then
      (HomologicalComplex₂.singleZeroXIso A pq.1 hp).hom.f pq.2 ≫ g.f pq.2 ≫
        (HomologicalComplex₂.XXIsoOfEq AddCommGrpCat.{a}
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (cechBicomplexOfComplex U K) hp.symm rfl).hom
    else 0) ?_ ?_
  · intro p p' q hpp
    by_cases hp : p = 0
    · subst p
      have hp' : p' = 1 := by
        change 0 + 1 = p' at hpp
        omega
      subst p'
      simp only [dif_pos True.intro, dif_neg (by omega : ¬ (0 + 1 = (0 : ℤ))),
        comp_zero]
      rw [Category.assoc]
      change (HomologicalComplex₂.singleZeroXIso A 0 rfl).hom.f q ≫
        (globalSectionsToCechZeroInt hT U (K.X q) ≫
          ((cechCochainFunctorInt U).obj (K.X q)).d 0 1) = 0
      rw [globalSectionsToCechZeroInt_comp_d, comp_zero]
    · simp [hp, HomologicalComplex₂.singleZeroBicomplex]
  · intro p q q' hqq
    by_cases hp : p = 0
    · subst p
      simp only [dif_pos True.intro]
      exact (HomologicalComplex.Hom.comm
        ((HomologicalComplex₂.singleZeroXIso A 0 rfl).hom ≫ g) q q')
    · simp [hp]

/-- The augmented bicomplex map of an injective resolution reads it only through the underlying
complex. -/
lemma globalSectionsToCechBicomplexMap_eq
    {T : C} (hT : IsTerminal T) {F : Sheaf J AddCommGrpCat.{a}}
    (U : index → C) (I : InjectiveResolution F) :
    globalSectionsToCechBicomplexMap hT U I =
      sectionsToCechBicomplexMap hT U I.cochainComplex :=
  rfl

/-- The augmented bicomplex map commutes with an arbitrary morphism of complexes. -/
lemma sectionsToCechBicomplexMap_naturality
    {T : C} (hT : IsTerminal T) (U : index → C) (Φ : K ⟶ L) :
    (CochainComplex.singleFunctor (CochainComplex AddCommGrpCat.{a} ℤ) 0).map
          (sectionsComplexMap T Φ) ≫ sectionsToCechBicomplexMap hT U L =
      sectionsToCechBicomplexMap hT U K ≫ cechBicomplexMap U Φ := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases hp : p = 0
  · subst p
    have h := congrArg (fun m : sectionsComplexUnlifted T K ⟶
        (cechBicomplexOfComplex U L).X 0 => m.f q)
      (sectionsToCechZeroColumn_naturality hT U Φ)
    dsimp [sectionsToCechBicomplexMap, HomologicalComplex₂.singleZeroXIso,
      HomologicalComplex₂.XXIsoOfEq] at h ⊢
    have hs : ((CochainComplex.singleFunctor
          (CochainComplex AddCommGrpCat.{a} ℤ) 0).map (sectionsComplexMap T Φ)).f 0 =
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (sectionsComplexUnlifted T K)).hom ≫ sectionsComplexMap T Φ ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (sectionsComplexUnlifted T L)).inv :=
      HomologicalComplex.single_map_f_self (c := ComplexShape.up ℤ) 0 _
    rw [show (((CochainComplex.singleFunctor
        (CochainComplex AddCommGrpCat.{a} ℤ) 0).map (sectionsComplexMap T Φ)).f 0).f q =
          _ from congrArg (fun m => HomologicalComplex.Hom.f m q) hs]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    refine congrArg (fun m => (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (sectionsComplexUnlifted T K)).hom.f q ≫ m) ?_
    simpa using h
  · apply IsZero.eq_of_src
    exact (HomologicalComplex.eval AddCommGrpCat.{a} (ComplexShape.up ℤ) q).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (sectionsComplexUnlifted T K) p hp)

/-- The global-sections complex maps to the Čech total complex of a cochain complex of
sheaves. -/
noncomputable def sectionsToCechTotalMap
    {T : C} (hT : IsTerminal T) (U : index → C)
    (K : CochainComplex (Sheaf J AddCommGrpCat.{a}) ℤ) :
    sectionsComplexUnlifted T K ⟶
      (cechBicomplexOfComplex U K).total (ComplexShape.up ℤ) :=
  (HomologicalComplex₂.singleZeroTotalIso (sectionsComplexUnlifted T K)).inv ≫
    ((HomologicalComplex₂.singleZeroBicomplex
      (sectionsComplexUnlifted T K)).totalFlipIso (ComplexShape.up ℤ)).inv ≫
    HomologicalComplex₂.total.map
      (HomologicalComplex₂.flipMap (sectionsToCechBicomplexMap hT U K))
      (ComplexShape.up ℤ) ≫
    ((cechBicomplexOfComplex U K).totalFlipIso (ComplexShape.up ℤ)).hom

/-- The comparison into the Čech total complex reads an injective resolution only through the
underlying complex. -/
lemma injectiveResolutionSectionsToCechTotalMap_eq
    {T : C} (hT : IsTerminal T) {F : Sheaf J AddCommGrpCat.{a}}
    (U : index → C) (I : InjectiveResolution F) :
    injectiveResolutionSectionsToCechTotalMap hT U I =
      sectionsToCechTotalMap hT U I.cochainComplex :=
  rfl

/-- The comparison into the Čech total complex commutes with an arbitrary morphism of
complexes. -/
lemma sectionsToCechTotalMap_naturality
    {T : C} (hT : IsTerminal T) (U : index → C) (Φ : K ⟶ L) :
    sectionsComplexMap T Φ ≫ sectionsToCechTotalMap hT U L =
      sectionsToCechTotalMap hT U K ≫
        HomologicalComplex₂.total.map (cechBicomplexMap U Φ) (ComplexShape.up ℤ) := by
  dsimp only [sectionsToCechTotalMap]
  have h₁ : sectionsComplexMap T Φ ≫
        (HomologicalComplex₂.singleZeroTotalIso (sectionsComplexUnlifted T L)).inv =
      (HomologicalComplex₂.singleZeroTotalIso (sectionsComplexUnlifted T K)).inv ≫
        HomologicalComplex₂.total.map
          (HomologicalComplex₂.singleZeroBicomplexMap (sectionsComplexMap T Φ))
          (ComplexShape.up ℤ) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq,
      HomologicalComplex₂.singleZeroTotalIso_naturality]
  have h₂ : HomologicalComplex₂.total.map
          (HomologicalComplex₂.flipMap
            (HomologicalComplex₂.singleZeroBicomplexMap (sectionsComplexMap T Φ)))
          (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map
          (HomologicalComplex₂.flipMap (sectionsToCechBicomplexMap hT U L))
          (ComplexShape.up ℤ) =
      HomologicalComplex₂.total.map
          (HomologicalComplex₂.flipMap (sectionsToCechBicomplexMap hT U K))
          (ComplexShape.up ℤ) ≫
        HomologicalComplex₂.total.map
          (HomologicalComplex₂.flipMap (cechBicomplexMap U Φ)) (ComplexShape.up ℤ) := by
    rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp]
    congr 1
    exact ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{a}
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map_comp _ _).symm.trans
      (congrArg (HomologicalComplex₂.flipFunctor AddCommGrpCat.{a}
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map
        (sectionsToCechBicomplexMap_naturality hT U Φ) |>.trans
        ((HomologicalComplex₂.flipFunctor AddCommGrpCat.{a}
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).map_comp _ _))
  rw [← Category.assoc, h₁, Category.assoc, Category.assoc,
    HomologicalComplex₂.totalFlipIso_inv_naturality_assoc, reassoc_of% h₂,
    Category.assoc, HomologicalComplex₂.totalFlipIso_naturality, Category.assoc]

end CategoryTheory.Sheaf
