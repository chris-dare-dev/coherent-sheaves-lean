/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import CohLean.Duality.Canonical.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
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
relative differentials of an arbitrary morphism of ringed spaces. The companion
`Canonical.Descent` module passes the objectwise standard-smooth calculation through
sheafification, constructs the global finite-locally-free atlas and determinant line, and exposes
the automatic constructor `CanonicalSheafData.ofSmoothRelativeDifferentials`.
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

end Variety

namespace SmoothProperVariety

variable {k : Type u} [Field k] {X : SmoothProperVariety k} {n : ℕ}

namespace CanonicalSheafData

/-- Build canonical-sheaf data using the constructed relative cotangent sheaf.

This low-level constructor retains explicit determinant data for callers with a chosen
trivialization. The companion `Canonical.Descent` module provides the automatic constructor
`ofSmoothRelativeDifferentials` from the smooth pure-dimension certificate alone. -/
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
