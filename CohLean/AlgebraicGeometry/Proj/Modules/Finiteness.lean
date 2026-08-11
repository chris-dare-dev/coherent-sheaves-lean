/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.AlgebraicGeometry.Proj.Modules.StructureModule
import CohLean.AlgebraicGeometry.Proj.Modules.TwistChart
import CohLean.AlgebraicGeometry.Proj.Modules.TwistingSheaf
import CohLean.Coh.Affine
import CohLean.Coh.Descent.Locality
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Quasi-coherence, coherence, and sections on `Proj`

This file is the finiteness-facing boundary of CohLean's graded-module sheaf construction.
Mathlib supplies the affine charts

`Spec (A_f)₀ ⟶ Proj A`,

while `CohLean.AlgebraicGeometry.Proj.Modules.AssociatedSheaf` supplies the sheaf `M̃`, its stalks, and the
canonical map

`(M_f)₀ ⟶ Γ(D₊(f), M̃)`.

The general affine comparison is deliberately represented by `AffineComparisonData`: it is an
isomorphism between the restriction of `M̃` to each standard affine chart and Mathlib's affine
`tilde` construction.  For the graded ring considered as a module over itself, this file now
constructs the comparison canonically from `associatedSheafSelfIso`; no certificate input is
needed in that case.  Once comparison data is present, quasi-coherence follows by gluing the
affine presentations, and coherence follows from explicit finite-presentation hypotheses on the
localized modules.

The global-section API is similarly conservative.  `TwistingSectionRange` records exactly the
degrees in which a chosen algebraic module is known to compute `Γ(Proj A, O(d))`; no all-degree
Serre correspondence is asserted.  The projective-space corollary uses Mathlib's finite generation
of homogeneous multivariate polynomials and therefore has no hidden noetherianity assumption.

## Main declarations

* `AffineComparisonData`: affine `tilde` comparison on every standard Proj chart;
* `affineComparisonDataSelf`: the constructed comparison for the structure module;
* `localizedNatShiftDegreeOneIso`: the explicit rank-one trivialization of `A(d)` on a
  degree-one chart;
* `moduleAwayToSection_natShift_degreeOne_bijective`: the corresponding constructed
  basic-open section comparison for every nonnegative twist;
* `associatedSheaf_isQuasicoherent`: quasi-coherence from those comparisons;
* `associatedSheaf_isCoherent_of_finitePresentation`: coherence from explicit finite
  presentation of every localized module;
* `associatedSheaf_isCoherent_of_noetherian_finite`: the common noetherian + finite-generation
  specialization;
* `BasicOpenSectionData`: bijectivity of the canonical basic-open section map;
* `basicOpenSectionDataSelf`: constructed basic-open certificates for the structure module;
* `TwistingSectionRange`: a degree-bounded global-section comparison for `O(d)`;
* `projectiveSpace_globalSections_finite`: finite generation for the polynomial-ring
  specialization in every certified degree.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped DirectSum Pointwise

namespace CohLean.AlgebraicGeometry.Proj

universe u

variable {A M σA σM : Type u}
variable [CommRing A] [AddCommGroup M] [Module A M]
variable [SetLike σA A] [AddSubgroupClass σA A]
variable [SetLike σM M] [AddSubgroupClass σM M]
variable (𝒜 : ℕ → σA) (𝓜 : ℕ → σM)
variable [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

/-! ## The standard affine charts -/

/-- The canonical index type for the standard affine cover of `Proj A`: a positive natural
degree together with a homogeneous element of that degree. -/
abbrev StandardChartIndex := Σ n : PNat, 𝒜 n

/-- The standard affine chart morphism `Spec (A_f)₀ ⟶ Proj A`. -/
def standardAway (i : StandardChartIndex 𝒜) :
    AlgebraicGeometry.Spec (.of (HomogeneousLocalization.Away 𝒜 (i.2 : A))) ⟶
      AlgebraicGeometry.Proj 𝒜 :=
  AlgebraicGeometry.Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2

instance standardAway_isOpenImmersion (i : StandardChartIndex 𝒜) :
    AlgebraicGeometry.IsOpenImmersion (standardAway 𝒜 i) := by
  unfold standardAway
  infer_instance

/-- The degree-zero localization of `M` on a standard affine chart, bundled as a module over
the chart ring `(A_f)₀`. -/
def localizedModule (i : StandardChartIndex 𝒜) :
    ModuleCat.{u} (HomogeneousLocalization.Away 𝒜 (i.2 : A)) :=
  ModuleCat.of _ (DegreeZeroLocalization 𝒜 𝓜 (.powers (i.2 : A)))

@[simp]
theorem standardAway_eq_affineOpenCover_f (i : StandardChartIndex 𝒜) :
    standardAway 𝒜 i = (AlgebraicGeometry.Proj.affineOpenCover 𝒜).f i :=
  rfl

/-! ## Affine comparison and quasi-coherence -/

/-- The exact local input needed to recognize `M̃` as quasi-coherent.

Each field identifies the restriction to a standard chart with the affine sheaf attached to the
degree-zero localized module.  It is data, not an axiom or typeclass: callers can see precisely
where the still-missing graded affine-comparison proof is used. -/
structure AffineComparisonData where
  localIso (i : StandardChartIndex 𝒜) :
    (associatedSheaf 𝒜 𝓜).restrict (standardAway 𝒜 i) ≅
      AlgebraicGeometry.tilde.{u}
        (R := .of (HomogeneousLocalization.Away 𝒜 (i.2 : A)))
        (localizedModule 𝒜 𝓜 i)

/-- For the structure module, the localized module on a standard chart is the chart ring as a
module over itself. -/
noncomputable def localizedModuleSelfIso (i : StandardChartIndex 𝒜) :
    localizedModule 𝒜 𝒜 i ≅
      ModuleCat.of (HomogeneousLocalization.Away 𝒜 (i.2 : A))
        (HomogeneousLocalization.Away 𝒜 (i.2 : A)) :=
  LinearEquiv.toModuleIso
    (DegreeZeroLocalization.selfLinearEquiv 𝒜 (.powers (i.2 : A))).symm

/-- A degree-one homogeneous element, bundled as a standard positive-degree chart index. -/
def degreeOneStandardChart (f : 𝒜 1) : StandardChartIndex 𝒜 :=
  ⟨⟨1, Nat.zero_lt_one⟩, f⟩

/-- On a degree-one chart, the localized module underlying the nonnegative twist `A(d)` is
canonically free of rank one. -/
noncomputable def localizedNatShiftDegreeOneIso (f : 𝒜 1) (d : ℕ) :
    localizedModule 𝒜 (natShift 𝒜 d) (degreeOneStandardChart 𝒜 f) ≅
      ModuleCat.of (HomogeneousLocalization.Away 𝒜 (f : A))
        (HomogeneousLocalization.Away 𝒜 (f : A)) :=
  LinearEquiv.toModuleIso
    (DegreeZeroLocalization.natShiftAwayLinearEquiv 𝒜 f.2 d)

/-- The canonical affine-chart comparison for the graded ring considered as a module over
itself.  This is constructed from the global structure-module isomorphism, restriction of the
unit module, and Mathlib's `tildeSelf`; it is not certificate input. -/
noncomputable def affineComparisonDataSelf : AffineComparisonData 𝒜 𝒜 where
  localIso i :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor
      (standardAway 𝒜 i)).mapIso (associatedSheafSelfIso 𝒜) ≪≫
      AlgebraicGeometry.Scheme.Modules.restrictUnitIso (standardAway 𝒜 i) ≪≫
        (((AlgebraicGeometry.tilde.functor
          (CommRingCat.of (HomogeneousLocalization.Away 𝒜 (i.2 : A)))).mapIso
            (localizedModuleSelfIso 𝒜 i)) ≪≫
          AlgebraicGeometry.tildeSelf).symm

namespace AffineComparisonData

/-- Quasi-coherent data on one range slice, transported from the affine `tilde` presentation. -/
noncomputable def localQuasicoherentData (c : AffineComparisonData 𝒜 𝓜)
    (i : StandardChartIndex 𝒜) :
    SheafOfModules.QuasicoherentData.{u, u, u, u}
      ((associatedSheaf 𝒜 𝓜).over (standardAway 𝒜 i).opensRange) := by
  let q : (AlgebraicGeometry.tilde.{u}
      (R := .of (HomogeneousLocalization.Away 𝒜 (i.2 : A)))
      (localizedModule 𝒜 𝓜 i)).QuasicoherentData.{u, u, u, u} :=
    SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData.some
  let q' : ((associatedSheaf 𝒜 𝓜).restrict
      (standardAway 𝒜 i)).QuasicoherentData.{u, u, u, u} :=
    SheafOfModules.QuasicoherentData.ofIsIso.{u, u, u, u}
      (c.localIso i).inv q
  exact (standardAway 𝒜 i).overQuasicoherentData (associatedSheaf 𝒜 𝓜) q'

/-- The standard affine charts cover `Proj A` in the open-set Grothendieck topology. -/
theorem standardCharts_coversTop :
    (Opens.grothendieckTopology (AlgebraicGeometry.Proj 𝒜)).CoversTop
      (fun i : StandardChartIndex 𝒜 => (standardAway 𝒜 i).opensRange) := by
  apply TopCat.Opens.grothendieckTopology_coversTop
  change (⨆ i, ((AlgebraicGeometry.Proj.affineOpenCover 𝒜).f i).opensRange) = ⊤
  exact (AlgebraicGeometry.Proj.affineOpenCover 𝒜).openCover.iSup_opensRange

/-- Global quasi-coherent data obtained by gluing the standard affine `tilde` presentations. -/
noncomputable def quasicoherentData (c : AffineComparisonData 𝒜 𝓜) :
    (associatedSheaf 𝒜 𝓜).QuasicoherentData.{u, u, u, u} :=
  SheafOfModules.QuasicoherentData.bind (associatedSheaf 𝒜 𝓜)
    (fun i : StandardChartIndex 𝒜 => (standardAway 𝒜 i).opensRange)
    (standardCharts_coversTop 𝒜)
    (localQuasicoherentData 𝒜 𝓜 c)

/-- The associated sheaf of a graded module is quasi-coherent once the canonical affine-chart
comparisons have been supplied. -/
theorem associatedSheaf_isQuasicoherent (c : AffineComparisonData 𝒜 𝓜) :
    (associatedSheaf 𝒜 𝓜).IsQuasicoherent :=
  (quasicoherentData 𝒜 𝓜 c).isQuasicoherent

end AffineComparisonData

/-- The associated structure module is quasi-coherent with no external chart certificate. -/
theorem associatedSheaf_self_isQuasicoherent :
    (associatedSheaf 𝒜 𝒜).IsQuasicoherent :=
  AffineComparisonData.associatedSheaf_isQuasicoherent 𝒜 𝒜
    (affineComparisonDataSelf 𝒜)

/-! ## Coherence -/

/-- Explicit finite-presentation hypotheses for all degree-zero localized modules.  No
noetherianity is needed when these stronger hypotheses are available directly. -/
structure LocalizedFinitePresentationData where
  finitePresentation (i : StandardChartIndex 𝒜) :
    Module.FinitePresentation
      (HomogeneousLocalization.Away 𝒜 (i.2 : A)) (localizedModule 𝒜 𝓜 i)

/-- Explicit hypotheses for the common noetherian criterion: every standard chart ring is
noetherian and every degree-zero localized module is finitely generated. -/
structure LocalizedNoetherianFiniteData where
  isNoetherian (i : StandardChartIndex 𝒜) :
    IsNoetherianRing (HomogeneousLocalization.Away 𝒜 (i.2 : A))
  finite (i : StandardChartIndex 𝒜) :
    Module.Finite
      (HomogeneousLocalization.Away 𝒜 (i.2 : A)) (localizedModule 𝒜 𝓜 i)

/-- Finite presentation of all standard-chart localizations makes the associated sheaf coherent.

The proof uses Mathlib's finite-presentation theorem for affine `tilde`, transports it across the
explicit local comparison, and glues over the canonical affine open cover. -/
theorem associatedSheaf_isCoherent_of_finitePresentation
    (c : AffineComparisonData 𝒜 𝓜)
    (hfin : LocalizedFinitePresentationData 𝒜 𝓜) :
    AlgebraicGeometry.Scheme.Modules.IsCoherent
      (AlgebraicGeometry.Proj 𝒜) (associatedSheaf 𝒜 𝓜) := by
  apply AlgebraicGeometry.Scheme.Modules.IsCoherent.of_affineOpenCover
    (associatedSheaf 𝒜 𝓜) (AlgebraicGeometry.Proj.affineOpenCover 𝒜)
  intro i
  letI : Module.FinitePresentation
      (HomogeneousLocalization.Away 𝒜 (i.2 : A)) (localizedModule 𝒜 𝓜 i) :=
    hfin.finitePresentation i
  have htilde : SheafOfModules.IsFinitePresentation.{u, u, u}
      (AlgebraicGeometry.tilde.{u}
        (R := .of (HomogeneousLocalization.Away 𝒜 (i.2 : A)))
        (localizedModule 𝒜 𝓜 i)) :=
    AlgebraicGeometry.isFinitePresentation_tilde.{u}
      (R := .of (HomogeneousLocalization.Away 𝒜 (i.2 : A)))
      (localizedModule 𝒜 𝓜 i)
  have hrestrict : SheafOfModules.IsFinitePresentation.{u, u, u}
      ((associatedSheaf 𝒜 𝓜).restrict (standardAway 𝒜 i)) :=
    SheafOfModules.IsFinitePresentation.of_iso.{u} (c.localIso i).symm htilde
  exact (standardAway 𝒜 i).isFinitePresentation_over_of_restrict
    (associatedSheaf 𝒜 𝓜) hrestrict

/-- The structure module has the required finite-presentation data on every standard chart. -/
theorem localizedFinitePresentationDataSelf :
    LocalizedFinitePresentationData 𝒜 𝒜 where
  finitePresentation i :=
    Module.FinitePresentation.of_equiv
      (localizedModuleSelfIso 𝒜 i).symm.toLinearEquiv

/-- The associated structure module is coherent without an external comparison or finiteness
certificate. -/
theorem associatedSheaf_self_isCoherent :
    AlgebraicGeometry.Scheme.Modules.IsCoherent
      (AlgebraicGeometry.Proj 𝒜) (associatedSheaf 𝒜 𝒜) :=
  associatedSheaf_isCoherent_of_finitePresentation 𝒜 𝒜
    (affineComparisonDataSelf 𝒜) (localizedFinitePresentationDataSelf 𝒜)

/-- Over noetherian standard chart rings, finite generation of the localized modules is enough
for coherence.  Both hypotheses are fields of `hfin`, so neither is inferred globally. -/
theorem associatedSheaf_isCoherent_of_noetherian_finite
    (c : AffineComparisonData 𝒜 𝓜)
    (hfin : LocalizedNoetherianFiniteData 𝒜 𝓜) :
    AlgebraicGeometry.Scheme.Modules.IsCoherent
      (AlgebraicGeometry.Proj 𝒜) (associatedSheaf 𝒜 𝓜) := by
  let hfp : LocalizedFinitePresentationData 𝒜 𝓜 :=
    { finitePresentation := fun i => by
        letI : IsNoetherianRing (HomogeneousLocalization.Away 𝒜 (i.2 : A)) :=
          hfin.isNoetherian i
        letI : Module.Finite
            (HomogeneousLocalization.Away 𝒜 (i.2 : A)) (localizedModule 𝒜 𝓜 i) :=
          hfin.finite i
        exact Module.finitePresentation_of_finite _ _ }
  exact associatedSheaf_isCoherent_of_finitePresentation 𝒜 𝓜 c hfp

/-! ## Basic-open and global sections -/

/-- Bijectivity certificates for the canonical maps `(M_f)₀ → Γ(D₊(f), M̃)` on all standard
charts.  Keeping this separate from `AffineComparisonData` is useful when a proof only needs
sections and not an isomorphism of sheaves. -/
structure BasicOpenSectionData where
  bijective (i : StandardChartIndex 𝒜) :
    Function.Bijective (moduleAwayToSection 𝒜 𝓜 (i.2 : A))

/-- The canonical basic-open section certificates for the graded ring as a module over itself. -/
theorem basicOpenSectionDataSelf : BasicOpenSectionData 𝒜 𝒜 where
  bijective i := moduleAwayToSection_self_bijective 𝒜 i.2.2 i.1.2

/-- The canonical additive equivalence on a standard basic open, obtained from its explicit
bijectivity certificate. -/
noncomputable def basicOpenSectionEquiv (c : BasicOpenSectionData 𝒜 𝓜)
    (i : StandardChartIndex 𝒜) :
    DegreeZeroLocalization 𝒜 𝓜 (.powers (i.2 : A)) ≃+
      (associatedSheafInType 𝒜 𝓜).1.obj
        (Opposite.op (ProjectiveSpectrum.basicOpen 𝒜 (i.2 : A))) :=
  AddEquiv.ofBijective (moduleAwayToSection 𝒜 𝓜 (i.2 : A)) (c.bijective i)

local notation3 "𝒪" =>
  AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜

/-- Global sections of `O(d)`, viewed as a module over a chosen base ring map into global
functions.  The ring map is explicit because `Γ(Proj A, O)` need not be definitionally `A₀`. -/
def twistingGlobalSectionsModule (R : Type u) [CommRing R]
    (ρ : R →+* 𝒪.1.obj (Opposite.op (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens)))
    (d : ℤ) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars ρ).obj
    ((twistingSheaf 𝒜 d).val.obj (Opposite.op (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens)))

/-- A deliberately degree-bounded identification of algebraic modules with the global sections
of `O(d)`.  This is the precise input consumed by Serre-finiteness arguments; it does not claim a
global-section formula outside `degrees`. -/
structure TwistingSectionRange (R : Type u) [CommRing R]
    (ρ : R →+* 𝒪.1.obj (Opposite.op (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens))) where
  degrees : Set ℕ
  algebraicSections : ℕ → ModuleCat.{u} R
  comparison (d : ℕ) (hd : d ∈ degrees) :
    algebraicSections d ≅ twistingGlobalSectionsModule 𝒜 R ρ (d : ℤ)

/-- Finite generation transfers across a certified global-section comparison in one degree. -/
theorem TwistingSectionRange.globalSections_finite
    {R : Type u} [CommRing R]
    {ρ : R →+* 𝒪.1.obj (Opposite.op (⊤ : (AlgebraicGeometry.Proj 𝒜).Opens))}
    (c : TwistingSectionRange 𝒜 R ρ) (d : ℕ) (hd : d ∈ c.degrees)
    [Module.Finite R (c.algebraicSections d)] :
    Module.Finite R (twistingGlobalSectionsModule 𝒜 R ρ (d : ℤ)) :=
  Module.Finite.equiv (c.comparison d hd).toLinearEquiv

/-! ## Projective-space specialization -/

/-- The standard grading on a multivariate polynomial ring. -/
abbrev polynomialGrading (ι R : Type u) [CommRing R] :
    ℕ → Submodule R (MvPolynomial ι R) :=
  MvPolynomial.homogeneousSubmodule ι R

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every standard variable chart of polynomial projective space has the constructed
basic-open section comparison for each nonnegative twist. -/
theorem projectiveSpace_variableSection_bijective
    (ι R : Type u) [CommRing R] (i : ι) (d : ℕ) :
    Function.Bijective
      (moduleAwayToSection (polynomialGrading ι R)
        (natShift (polynomialGrading ι R) d) (MvPolynomial.X i)) :=
  moduleAwayToSection_natShift_degreeOne_bijective
    (polynomialGrading ι R) (MvPolynomial.isHomogeneous_X R i) d

/-- A section comparison for projective space in degree `d`.  The source is the concrete module
of homogeneous polynomials of degree `d`; the target is `Γ(Proj R[X_i], O(d))`, restricted to the
chosen base-ring action. -/
structure ProjectiveSpaceSectionComparison (ι R : Type u) [CommRing R]
    (ρ : R →+*
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf
        (polynomialGrading ι R)).1.obj
          (Opposite.op (⊤ : (AlgebraicGeometry.Proj (polynomialGrading ι R)).Opens)))
    (d : ℕ) where
  comparison :
    ModuleCat.of R (MvPolynomial.homogeneousSubmodule ι R d) ≅
      twistingGlobalSectionsModule (polynomialGrading ι R) R ρ (d : ℤ)

/-- In a finite-variable projective-space specialization, every certified nonnegative twist has
finitely generated global sections over the base ring. -/
theorem projectiveSpace_globalSections_finite
    {ι R : Type u} [CommRing R] [Finite ι]
    {ρ : R →+*
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf
        (polynomialGrading ι R)).1.obj
          (Opposite.op (⊤ : (AlgebraicGeometry.Proj (polynomialGrading ι R)).Opens))}
    (d : ℕ) (c : ProjectiveSpaceSectionComparison ι R ρ d) :
    Module.Finite R
      (twistingGlobalSectionsModule (polynomialGrading ι R) R ρ (d : ℤ)) := by
  haveI : Module.Finite R (MvPolynomial.homogeneousSubmodule ι R d) :=
    (Module.Finite.iff_fg).2 (MvPolynomial.homogeneousSubmodule_fg ι R d)
  exact Module.Finite.equiv c.comparison.toLinearEquiv

end CohLean.AlgebraicGeometry.Proj
