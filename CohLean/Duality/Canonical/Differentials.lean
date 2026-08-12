/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Duality.Canonical.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Relative differentials of a variety over a field

For a variety `X` over `k`, this file constructs the relative cotangent module sheaf
`Variety.relativeDifferentials X`.  The structure morphism supplies a map from the constant
`k`-presheaf to the structure presheaf.  Objectwise Kähler differentials for this map form a
presheaf of modules; sheafifying it gives an object of `X.toScheme.Modules`.

The resulting sheaf represents `k`-linear derivations into module sheaves: the declarations
`relativeDifferentialsDesc_fac` and `relativeDifferentialsDesc_unique` are its factorization and
uniqueness properties.  On every open, the presheaf before sheafification is literally the
ordinary Kähler differential module. On a standard-smooth chart of relative dimension `n`,
that module is free and has rank `n`.

This construction uses that the base is `Spec k`, so its inverse-image ring can be presented on
the site of `X` by the constant `k`-presheaf.  It does not fill Mathlib's more general TODO for
relative differentials of an arbitrary morphism of ringed spaces. `Canonical.Descent` passes the
objectwise standard-smooth calculation through sheafification to a global finite-locally-free
atlas, constructs the determinant and its sheaf-dual inverse, and feeds them to
`CanonicalSheafData.ofRelativeDifferentials` automatically.
-/

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

namespace Variety

variable {k : Type u} [Field k] (X : Variety k)

/-- The constant base-field presheaf on the opens of a variety. -/
noncomputable def baseFieldPresheaf : X.toScheme.Opensᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const X.toScheme.Opensᵒᵖ).obj (CommRingCat.of k)

/-- The map from the base field to global functions induced by the structure morphism. -/
noncomputable def baseFieldToGlobalSections :
    k →+* Γ(X.toScheme, (⊤ : X.toScheme.Opens)) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    X.structureMorphism.appTop).hom

/-- The structure morphism, presented as a map from the constant base-field presheaf to the
structure presheaf of `X`. -/
noncomputable def baseFieldToStructurePresheaf :
    baseFieldPresheaf X ⟶ X.toScheme.presheaf where
  app U := CommRingCat.ofHom (baseFieldToGlobalSections X) ≫
    X.toScheme.presheaf.map
      (homOfLE (show U.unop ≤ (⊤ : X.toScheme.Opens) from le_top)).op
  naturality := by
    intro U V f
    let rU : Opposite.op (⊤ : X.toScheme.Opens) ⟶ U :=
      (homOfLE (show U.unop ≤ (⊤ : X.toScheme.Opens) from le_top)).op
    let rV : Opposite.op (⊤ : X.toScheme.Opens) ⟶ V :=
      (homOfLE (show V.unop ≤ (⊤ : X.toScheme.Opens) from le_top)).op
    change 𝟙 (CommRingCat.of k) ≫
        (CommRingCat.ofHom (baseFieldToGlobalSections X) ≫
          X.toScheme.presheaf.map rV) =
      (CommRingCat.ofHom (baseFieldToGlobalSections X) ≫
          X.toScheme.presheaf.map rU) ≫ X.toScheme.presheaf.map f
    rw [Category.id_comp, Category.assoc, ← X.toScheme.presheaf.map_comp]
    rw [Subsingleton.elim rV (rU ≫ f)]

/-- The presheaf whose value on `U` is the Kähler differential module of
`k → Γ(U, 𝒪_X)`. -/
noncomputable def relativeDifferentialsPresheaf : X.toScheme.PresheafOfModules :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    (baseFieldToStructurePresheaf X)

/-- The relative cotangent sheaf `Ω¹_{X/k}`, obtained by sheafifying the objectwise Kähler
differential presheaf. -/
noncomputable def relativeDifferentials : X.toScheme.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.toScheme.ringCatSheaf.obj)).obj
    (relativeDifferentialsPresheaf X)

/-- The objectwise universal derivation into the relative-differentials presheaf. -/
noncomputable def relativeDerivationPresheaf :
    (relativeDifferentialsPresheaf X).Derivation'
      (baseFieldToStructurePresheaf X) :=
  PresheafOfModules.DifferentialsConstruction.derivation'
    (baseFieldToStructurePresheaf X)

/-- The sheafification unit from the objectwise Kähler differential presheaf to the underlying
presheaf of the relative cotangent sheaf. -/
noncomputable def relativeDifferentialsSheafification :
    relativeDifferentialsPresheaf X ⟶
      (SheafOfModules.forget X.toScheme.ringCatSheaf).obj
        (relativeDifferentials X) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.toScheme.ringCatSheaf.obj)).unit.app
      (relativeDifferentialsPresheaf X)

/-- The universal `k`-linear derivation `𝒪_X → Ω¹_{X/k}`. -/
noncomputable def relativeDerivation :
    ((SheafOfModules.forget X.toScheme.ringCatSheaf).obj
      (relativeDifferentials X)).Derivation'
        (baseFieldToStructurePresheaf X) :=
  (relativeDerivationPresheaf X).postcomp
    (relativeDifferentialsSheafification X)

/-- A `k`-linear derivation from `𝒪_X` into a module sheaf descends to a morphism from
`Ω¹_{X/k}`. -/
noncomputable def relativeDifferentialsDesc
    (M : X.toScheme.Modules)
    (d : ((SheafOfModules.forget X.toScheme.ringCatSheaf).obj M).Derivation'
      (baseFieldToStructurePresheaf X)) :
    relativeDifferentials X ⟶ M :=
  ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.toScheme.ringCatSheaf.obj)).homEquiv
      (relativeDifferentialsPresheaf X) M).symm
    ((PresheafOfModules.DifferentialsConstruction.isUniversal'
      (baseFieldToStructurePresheaf X)).desc d)

/-- The morphism descended from a derivation factors the universal derivation as prescribed. -/
theorem relativeDifferentialsDesc_fac
    (M : X.toScheme.Modules)
    (d : ((SheafOfModules.forget X.toScheme.ringCatSheaf).obj M).Derivation'
      (baseFieldToStructurePresheaf X)) :
    (relativeDerivation X).postcomp
      ((SheafOfModules.forget X.toScheme.ringCatSheaf).map
        (relativeDifferentialsDesc X M d)) = d := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.toScheme.ringCatSheaf.obj)
  let universal := PresheafOfModules.DifferentialsConstruction.isUniversal'
    (baseFieldToStructurePresheaf X)
  have hdesc : relativeDifferentialsSheafification X ≫
      (SheafOfModules.forget X.toScheme.ringCatSheaf).map
        (relativeDifferentialsDesc X M d) = universal.desc d := by
    change (adj.homEquiv (relativeDifferentialsPresheaf X) M)
        (relativeDifferentialsDesc X M d) = universal.desc d
    exact Equiv.apply_symm_apply _ _
  change ((relativeDerivationPresheaf X).postcomp
      (relativeDifferentialsSheafification X)).postcomp
        ((SheafOfModules.forget X.toScheme.ringCatSheaf).map
          (relativeDifferentialsDesc X M d)) = d
  ext U x
  change (((relativeDifferentialsSheafification X ≫
      (SheafOfModules.forget X.toScheme.ringCatSheaf).map
        (relativeDifferentialsDesc X M d)).app U).hom
          ((relativeDerivationPresheaf X).d x)) = d.d x
  rw [hdesc]
  exact PresheafOfModules.Derivation.congr_d (universal.fac d) x

/-- The morphism descended from a derivation is unique. -/
theorem relativeDifferentialsDesc_unique
    (M : X.toScheme.Modules)
    (d : ((SheafOfModules.forget X.toScheme.ringCatSheaf).obj M).Derivation'
      (baseFieldToStructurePresheaf X))
    (f : relativeDifferentials X ⟶ M)
    (hf : (relativeDerivation X).postcomp
      ((SheafOfModules.forget X.toScheme.ringCatSheaf).map f) = d) :
    f = relativeDifferentialsDesc X M d := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.toScheme.ringCatSheaf.obj)
  let universal := PresheafOfModules.DifferentialsConstruction.isUniversal'
    (baseFieldToStructurePresheaf X)
  apply (adj.homEquiv (relativeDifferentialsPresheaf X) M).injective
  apply universal.postcomp_injective
  have hf' : (relativeDerivationPresheaf X).postcomp
      ((adj.homEquiv (relativeDifferentialsPresheaf X) M) f) = d := by
    rw [Adjunction.homEquiv_unit]
    ext U x
    exact PresheafOfModules.Derivation.congr_d hf x
  have hdesc :
      (adj.homEquiv (relativeDifferentialsPresheaf X) M)
          (relativeDifferentialsDesc X M d) = universal.desc d :=
    Equiv.apply_symm_apply _ _
  exact hf'.trans ((universal.fac d).symm.trans
    (congrArg (relativeDerivationPresheaf X).postcomp hdesc.symm))

/-- Morphisms from `Ω¹_{X/k}` are determined by their composites with the universal
derivation. -/
theorem relativeDifferentials_hom_ext
    (M : X.toScheme.Modules) (f g : relativeDifferentials X ⟶ M)
    (h : (relativeDerivation X).postcomp
        ((SheafOfModules.forget X.toScheme.ringCatSheaf).map f) =
      (relativeDerivation X).postcomp
        ((SheafOfModules.forget X.toScheme.ringCatSheaf).map g)) :
    f = g := by
  let d := (relativeDerivation X).postcomp
    ((SheafOfModules.forget X.toScheme.ringCatSheaf).map f)
  rw [relativeDifferentialsDesc_unique X M d f rfl]
  rw [relativeDifferentialsDesc_unique X M d g h.symm]

/-- Before sheafification, the relative differentials on an open are exactly the ordinary
Kähler differential module of its ring of functions over `k`. -/
@[simp]
theorem relativeDifferentialsPresheaf_obj (U : X.toScheme.Opensᵒᵖ) :
    (relativeDifferentialsPresheaf X).obj U =
      CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf X).app U) := rfl

/-- The presheaf universal derivation is objectwise the ordinary Kähler derivation. -/
@[simp]
theorem relativeDerivationPresheaf_d {U : X.toScheme.Opensᵒᵖ}
    (x : X.toScheme.presheaf.obj U) :
    (relativeDerivationPresheaf X).d x =
      CommRingCat.KaehlerDifferential.d x := rfl

/-- On a standard-smooth affine chart, the objectwise relative differential module is free. -/
theorem relativeDifferentialsPresheaf_obj_free
    (U : X.toScheme.Opensᵒᵖ) (n : ℕ)
    (h : ((baseFieldToStructurePresheaf X).app U).hom.IsStandardSmoothOfRelativeDimension n) :
    Module.Free (X.toScheme.presheaf.obj U)
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf X).app U)) := by
  unfold CommRingCat.KaehlerDifferential
  letI : Algebra (X.baseFieldPresheaf.obj U) (X.toScheme.presheaf.obj U) :=
    ((baseFieldToStructurePresheaf X).app U).hom.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension n
      (X.baseFieldPresheaf.obj U) (X.toScheme.presheaf.obj U) := h
  letI : Algebra.IsStandardSmooth (X.baseFieldPresheaf.obj U)
      (X.toScheme.presheaf.obj U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  change Module.Free (X.toScheme.presheaf.obj U)
    (_root_.KaehlerDifferential (X.baseFieldPresheaf.obj U)
      (X.toScheme.presheaf.obj U))
  exact Algebra.IsStandardSmooth.free_kaehlerDifferential

/-- On a standard-smooth affine chart of relative dimension `n`, objectwise relative
differentials have rank `n`. -/
theorem relativeDifferentialsPresheaf_obj_rank
    (U : X.toScheme.Opensᵒᵖ) (n : ℕ)
    (h : ((baseFieldToStructurePresheaf X).app U).hom.IsStandardSmoothOfRelativeDimension n)
    [Nontrivial (X.toScheme.presheaf.obj U)] :
    Module.rank (X.toScheme.presheaf.obj U)
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf X).app U)) = n := by
  unfold CommRingCat.KaehlerDifferential
  letI : Algebra (X.baseFieldPresheaf.obj U) (X.toScheme.presheaf.obj U) :=
    ((baseFieldToStructurePresheaf X).app U).hom.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension n
      (X.baseFieldPresheaf.obj U) (X.toScheme.presheaf.obj U) := h
  change Module.rank (X.toScheme.presheaf.obj U)
    (_root_.KaehlerDifferential (X.baseFieldPresheaf.obj U)
      (X.toScheme.presheaf.obj U)) = n
  exact Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n

/-- The underlying linear restriction map of the relative-differentials presheaf from an open
`U` to its basic open `D(f)`. -/
noncomputable def relativeDifferentialsBasicOpenRestriction
    {U : X.toScheme.Opens} (f : X.toScheme.presheaf.obj (.op U)) :
    letI : Module (X.toScheme.presheaf.obj (.op U))
        (CommRingCat.KaehlerDifferential
          ((baseFieldToStructurePresheaf X).app
            (.op (X.toScheme.basicOpen f)))) :=
      Module.compHom _
        (X.toScheme.presheaf.map
          (homOfLE (X.toScheme.basicOpen_le f)).op).hom
    CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf X).app (.op U)) →ₗ[
          X.toScheme.presheaf.obj (.op U)]
      CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf X).app
          (.op (X.toScheme.basicOpen f))) :=
  ((relativeDifferentialsPresheaf X).map
    (homOfLE (X.toScheme.basicOpen_le f)).op).hom

/-- On an affine open, restriction of the relative-differentials presheaf to a basic open is
the localization of its module of sections at the defining function. -/
theorem relativeDifferentialsBasicOpenRestriction_isLocalizedModule
    {U : X.toScheme.Opens} (hU : IsAffineOpen U)
    (f : X.toScheme.presheaf.obj (.op U)) :
    letI : Module (X.toScheme.presheaf.obj (.op U))
        (CommRingCat.KaehlerDifferential
          ((baseFieldToStructurePresheaf X).app
            (.op (X.toScheme.basicOpen f)))) :=
      Module.compHom _
        (X.toScheme.presheaf.map
          (homOfLE (X.toScheme.basicOpen_le f)).op).hom
    IsLocalizedModule (Submonoid.powers f)
      (relativeDifferentialsBasicOpenRestriction X f) := by
  let e := (homOfLE (X.toScheme.basicOpen_le f)).op
  letI : Algebra k (X.toScheme.presheaf.obj (.op U)) :=
    ((baseFieldToStructurePresheaf X).app (.op U)).hom.toAlgebra
  letI : Algebra k
      (X.toScheme.presheaf.obj (.op (X.toScheme.basicOpen f))) :=
    ((baseFieldToStructurePresheaf X).app
      (.op (X.toScheme.basicOpen f))).hom.toAlgebra
  letI : Algebra (X.toScheme.presheaf.obj (.op U))
      (X.toScheme.presheaf.obj (.op (X.toScheme.basicOpen f))) :=
    (X.toScheme.presheaf.map e).hom.toAlgebra
  letI : IsScalarTower k (X.toScheme.presheaf.obj (.op U))
      (X.toScheme.presheaf.obj (.op (X.toScheme.basicOpen f))) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change ((baseFieldToStructurePresheaf X).app
        (.op (X.toScheme.basicOpen f))).hom a =
      (X.toScheme.presheaf.map e).hom
        (((baseFieldToStructurePresheaf X).app (.op U)).hom a)
    have h := congrArg (fun q ↦ q.hom a)
      ((baseFieldToStructurePresheaf X).naturality e)
    change ((baseFieldToStructurePresheaf X).app
        (.op (X.toScheme.basicOpen f))).hom ((RingHom.id k) a) =
      (X.toScheme.presheaf.map e).hom
        (((baseFieldToStructurePresheaf X).app (.op U)).hom a) at h
    simpa using h
  letI : IsLocalization.Away f
      (X.toScheme.presheaf.obj (.op (X.toScheme.basicOpen f))) :=
    hU.isLocalization_basicOpen f
  change IsLocalizedModule (Submonoid.powers f)
    (_root_.KaehlerDifferential.map k k
      (X.toScheme.presheaf.obj (.op U))
      (X.toScheme.presheaf.obj (.op (X.toScheme.basicOpen f))))
  infer_instance

/-- On a nonempty standard-smooth affine chart of relative dimension `n`, the objectwise
relative differential module has a chosen basis indexed by `Fin n`.

This strengthens the separate freeness and rank statements to the concrete algebraic
trivialization needed by the affine sheafification comparison. -/
noncomputable def relativeDifferentialsPresheaf_obj_basis
    (U : X.toScheme.Opensᵒᵖ) (n : ℕ)
    (h : ((baseFieldToStructurePresheaf X).app U).hom.IsStandardSmoothOfRelativeDimension n)
    [Nontrivial (X.toScheme.presheaf.obj U)] :
    Module.Basis (Fin n) (X.toScheme.presheaf.obj U)
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf X).app U)) := by
  letI : Algebra (X.baseFieldPresheaf.obj U) (X.toScheme.presheaf.obj U) :=
    ((baseFieldToStructurePresheaf X).app U).hom.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension n
      (X.baseFieldPresheaf.obj U) (X.toScheme.presheaf.obj U) := h
  letI : Algebra.IsStandardSmooth (X.baseFieldPresheaf.obj U)
      (X.toScheme.presheaf.obj U) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  letI : Module.Free (X.toScheme.presheaf.obj U)
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf X).app U)) :=
    relativeDifferentialsPresheaf_obj_free X U n h
  letI : Module.Finite (X.toScheme.presheaf.obj U)
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf X).app U)) :=
    Module.finite_of_rank_eq_nat
      (relativeDifferentialsPresheaf_obj_rank X U n h)
  apply Module.finBasisOfFinrankEq
  apply Nat.cast_injective (R := Cardinal)
  rw [Module.finrank_eq_rank]
  exact relativeDifferentialsPresheaf_obj_rank X U n h

/-- The top exterior power of the objectwise relative differential module on a nonempty
standard-smooth chart is canonically a free module of rank one, after choosing the `Fin n`
basis above. -/
noncomputable def relativeDifferentialsPresheaf_obj_topExteriorPowerEquiv
    (U : X.toScheme.Opensᵒᵖ) (n : ℕ)
    (h : ((baseFieldToStructurePresheaf X).app U).hom.IsStandardSmoothOfRelativeDimension n)
    [Nontrivial (X.toScheme.presheaf.obj U)] :
    (⋀[X.toScheme.presheaf.obj U]^n
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf X).app U))) ≃ₗ[X.toScheme.presheaf.obj U]
      X.toScheme.presheaf.obj U :=
  (relativeDifferentialsPresheaf_obj_basis X U n h).topExteriorPowerEquiv

end Variety

namespace SmoothProperVariety

variable {k : Type u} [Field k] {X : SmoothProperVariety k} {n : ℕ}

namespace CanonicalSheafData

/-- Build canonical-sheaf data using the constructed relative cotangent sheaf.

The smooth pure-dimension certificate and determinant descent remain arguments until the
corresponding geometric theorems are available. -/
noncomputable def ofRelativeDifferentials
    (hSmooth : SmoothOfRelativeDimension n X.toVariety.structureMorphism)
    (D : Scheme.Modules.DeterminantData
      (Variety.relativeDifferentials X.toVariety))
    (hrank : D.rank = n) : CanonicalSheafData X n where
  smoothOfRelativeDimension := hSmooth
  cotangent := Variety.relativeDifferentials X.toVariety
  cotangentDeterminant := D
  cotangent_rank := hrank

/-- The cotangent field of `ofRelativeDifferentials` is the constructed relative cotangent
sheaf. -/
@[simp]
theorem ofRelativeDifferentials_cotangent
    (hSmooth : SmoothOfRelativeDimension n X.toVariety.structureMorphism)
    (D : Scheme.Modules.DeterminantData
      (Variety.relativeDifferentials X.toVariety))
    (hrank : D.rank = n) :
    (ofRelativeDifferentials hSmooth D hrank).cotangent =
      Variety.relativeDifferentials X.toVariety := rfl

end CanonicalSheafData

end SmoothProperVariety

end AlgebraicGeometry
