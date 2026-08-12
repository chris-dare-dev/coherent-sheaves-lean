/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Exterior powers of sheaves of modules

This file constructs exterior powers in two stages. First, a semilinear map of modules induces
a semilinear map on exterior powers. Applying this to restriction maps gives the objectwise
exterior-power presheaf. Sheafification then gives `Scheme.Modules.exteriorPower`.
-/

open CategoryTheory Limits LinearMap

universe u v w w'

namespace LinearMap

variable {R S : Type u} [CommRing R] [CommRing S]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type v} [AddCommGroup N] [Module S N]

/-- A semilinear map induces a semilinear map on exterior powers. -/
noncomputable def exteriorPower (n : ℕ) (σ : R →+* S) (f : M →ₛₗ[σ] N) :
    (⋀[R]^n M) →ₛₗ[σ] (⋀[S]^n N) := by
  letI : Module R (⋀[S]^n N) := Module.compHom _ σ
  let a : M [⋀^(Fin n)]→ₗ[R] (⋀[S]^n N) :=
    { toFun := fun x => _root_.exteriorPower.ιMulti S n (f ∘ x)
      map_update_add' := by
        intro _ x i m m'
        have hu (a : M) : f ∘ Function.update x i a =
            Function.update (f ∘ x) i (f a) := by
          funext j
          by_cases h : j = i
          · subst h
            simp
          · simp [Function.update, h]
        rw [hu, hu, hu, f.map_add]
        exact (_root_.exteriorPower.ιMulti S n).map_update_add _ _ _ _
      map_update_smul' := by
        intro _ x i r m
        have hu (a : M) : f ∘ Function.update x i a =
            Function.update (f ∘ x) i (f a) := by
          funext j
          by_cases h : j = i
          · subst h
            simp
          · simp [Function.update, h]
        rw [hu, hu, f.map_smulₛₗ]
        exact (_root_.exteriorPower.ιMulti S n).map_update_smul _ _ _ _
      map_eq_zero_of_eq' := by
        intro x i j h hij
        apply (_root_.exteriorPower.ιMulti S n).map_eq_zero_of_eq
        · simpa using congrArg f h
        · exact hij }
  let g : (⋀[R]^n M) →ₗ[R] (⋀[S]^n N) :=
    _root_.exteriorPower.alternatingMapLinearEquiv a
  exact
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r x => g.map_smul r x }

@[simp]
theorem exteriorPower_ιMulti (n : ℕ) (σ : R →+* S) (f : M →ₛₗ[σ] N)
    (x : Fin n → M) :
    exteriorPower n σ f (_root_.exteriorPower.ιMulti R n x) =
      _root_.exteriorPower.ιMulti S n (f ∘ x) := by
  letI : Module R (⋀[S]^n N) := Module.compHom _ σ
  change _root_.exteriorPower.alternatingMapLinearEquiv _
      (_root_.exteriorPower.ιMulti R n x) = _
  rw [_root_.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

end LinearMap

namespace PresheafOfModules

variable {C : Type w} [Category.{w'} C]
variable (A : Cᵒᵖ ⥤ CommRingCat.{u})

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The objectwise exterior power of a presheaf of modules. Its restriction maps are the
semilinear exterior powers of the original restriction maps. -/
@[simps obj]
noncomputable def exteriorPower
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) (n : ℕ) :
    PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) where
  obj U := (Q.obj U).exteriorPower n
  map {U V} f := by
    let g := LinearMap.exteriorPower n
      ((A ⋙ forget₂ CommRingCat RingCat).map f).hom (Q.restrictₛₗ f)
    exact ModuleCat.semilinearMapAddEquiv
      ((A ⋙ forget₂ CommRingCat RingCat).map f).hom _ _ g
  map_id U := by
    apply ModuleCat.exteriorPower.hom_ext
    ext x
    dsimp
    change LinearMap.exteriorPower n (A.map (𝟙 U)).hom (Q.restrictₛₗ (𝟙 U))
      (_root_.exteriorPower.ιMulti (A.obj U) n x) =
      _root_.exteriorPower.ιMulti (A.obj U) n x
    rw [LinearMap.exteriorPower_ιMulti]
    congr 1
    funext i
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp (Q.map_id U)) (x i)
  map_comp f g := by
    apply ModuleCat.exteriorPower.hom_ext
    ext x
    dsimp
    change LinearMap.exteriorPower n (A.map (f ≫ g)).hom (Q.restrictₛₗ (f ≫ g))
      (_root_.exteriorPower.ιMulti (A.obj _) n x) = _
    rw [LinearMap.exteriorPower_ιMulti]
    change _root_.exteriorPower.ιMulti (A.obj _) n ((Q.restrictₛₗ (f ≫ g)) ∘ x) =
      LinearMap.exteriorPower n (A.map g).hom (Q.restrictₛₗ g)
        (LinearMap.exteriorPower n (A.map f).hom (Q.restrictₛₗ f)
          (_root_.exteriorPower.ιMulti (A.obj _) n x))
    rw [LinearMap.exteriorPower_ιMulti, LinearMap.exteriorPower_ιMulti]
    congr 1
    funext i
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp (Q.map_comp f g)) (x i)

namespace exteriorPower

variable {A}
variable {Q Q' Q'' : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}

set_option backward.isDefEq.respectTransparency false in
/-- Exterior power is functorial in morphisms of presheaves of modules. -/
noncomputable def map (f : Q ⟶ Q') (n : ℕ) :
    PresheafOfModules.exteriorPower A Q n ⟶
      PresheafOfModules.exteriorPower A Q' n where
  app U := ModuleCat.exteriorPower.map (f.app U) n
  naturality {U V} g := by
    apply ModuleCat.exteriorPower.hom_ext
    ext x
    dsimp [PresheafOfModules.exteriorPower]
    rw [ModuleCat.semilinearMapAddEquiv_apply,
      ModuleCat.semilinearMapAddEquiv_apply, ModuleCat.exteriorPower.map_mk]
    change ModuleCat.exteriorPower.map (f.app V) n
        (LinearMap.exteriorPower n (A.map g).hom (Q.restrictₛₗ g)
          (_root_.exteriorPower.ιMulti (A.obj U) n x)) =
      LinearMap.exteriorPower n (A.map g).hom (Q'.restrictₛₗ g)
        (_root_.exteriorPower.ιMulti (A.obj U) n (f.app U ∘ x))
    rw [LinearMap.exteriorPower_ιMulti]
    erw [ModuleCat.exteriorPower.map_mk]
    rw [LinearMap.exteriorPower_ιMulti]
    congr 1
    funext i
    exact DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (f.naturality g)) (x i)

@[simp]
theorem map_app_ιMulti (f : Q ⟶ Q') (n : ℕ) (U : Cᵒᵖ) (x : Fin n → Q.obj U) :
    (map f n).app U (ModuleCat.exteriorPower.mk x) =
      ModuleCat.exteriorPower.mk (f.app U ∘ x) :=
  ModuleCat.exteriorPower.map_mk _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem map_id (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) (n : ℕ) :
    map (𝟙 Q) n = 𝟙 (PresheafOfModules.exteriorPower A Q n) := by
  ext U : 1
  exact (ModuleCat.exteriorPower.functor (A.obj U) n).map_id (Q.obj U)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem map_comp (f : Q ⟶ Q') (g : Q' ⟶ Q'') (n : ℕ) :
    map (f ≫ g) n = map f n ≫ map g n := by
  ext U : 1
  exact (ModuleCat.exteriorPower.functor (A.obj U) n).map_comp (f.app U) (g.app U)

/-- Exterior power sends an isomorphism of presheaves to an isomorphism. -/
noncomputable def mapIso (e : Q ≅ Q') (n : ℕ) :
    PresheafOfModules.exteriorPower A Q n ≅
      PresheafOfModules.exteriorPower A Q' n where
  hom := map e.hom n
  inv := map e.inv n
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

end exteriorPower

/-- Exterior power as an endofunctor on presheaves of modules. -/
noncomputable def exteriorPowerFunctor (n : ℕ) :
    PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) where
  obj Q := exteriorPower A Q n
  map f := exteriorPower.map f n
  map_id Q := exteriorPower.map_id Q n
  map_comp f g := exteriorPower.map_comp f g n

end PresheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

local instance exteriorPowerCategory : Category X.Modules :=
  inferInstanceAs (Category (SheafOfModules X.ringCatSheaf))

/-- The exterior power of a sheaf of modules, obtained by sheafifying the objectwise exterior
power presheaf. -/
noncomputable def exteriorPower (E : X.Modules) (n : ℕ) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.exteriorPower X.presheaf
      ((SheafOfModules.forget X.ringCatSheaf).obj E) n)

/-- Exterior powers carry isomorphic module sheaves to isomorphic module sheaves. -/
noncomputable def exteriorPowerMapIso {E F : X.Modules} (e : E ≅ F) (n : ℕ) :
    exteriorPower E n ≅ exteriorPower F n :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (PresheafOfModules.exteriorPower.mapIso
      ((SheafOfModules.forget X.ringCatSheaf).mapIso e) n)

/-- The sheafification unit defining the exterior power of a sheaf of modules. -/
noncomputable def exteriorPowerSheafification (E : X.Modules) (n : ℕ) :
    PresheafOfModules.exteriorPower X.presheaf
        ((SheafOfModules.forget X.ringCatSheaf).obj E) n ⟶
      (SheafOfModules.forget X.ringCatSheaf).obj (exteriorPower E n) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app _

def topPowerset (n : ℕ) :
    Set.powersetCard (ULift.{u} (Fin n)) n :=
  ⟨Finset.univ, by simp⟩

@[reducible]
private noncomputable def topPowersetUnique (n : ℕ) :
    Unique (Set.powersetCard (ULift.{u} (Fin n)) n) where
  default := topPowerset n
  uniq s := Subtype.ext (Finset.eq_univ_of_card s.1 (by simpa using s.2))

/-- The top exterior power of a free rank-`n` module is the coefficient ring. -/
noncomputable def topExteriorFreeEquiv
    (R : Type u) [CommRing R] (n : ℕ) :
    (⋀[R]^n (ULift.{u} (Fin n) →₀ R)) ≃ₗ[R] R := by
  letI : Unique (Set.powersetCard (ULift.{u} (Fin n)) n) := topPowersetUnique n
  exact ((Finsupp.basisSingleOne (R := R)).exteriorPower n).repr |>.trans
    (Finsupp.uniqueLinearEquiv R R default)

lemma topExteriorFreeEquiv_ιMulti
    (R : Type u) [CommRing R] (n : ℕ)
    (x : Fin n → (ULift.{u} (Fin n) →₀ R)) :
    topExteriorFreeEquiv R n (_root_.exteriorPower.ιMulti R n x) =
      (Matrix.of fun i j ↦
        x i (Set.powersetCard.ofFinEmbEquiv.symm
          (topPowerset.{u} n) j)).det := by
  letI : Unique (Set.powersetCard (ULift.{u} (Fin n)) n) := topPowersetUnique n
  rw [topExteriorFreeEquiv]
  change ((Finsupp.basisSingleOne (R := R)).exteriorPower n).repr
      (_root_.exteriorPower.ιMulti R n x) default = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  congr 2

private noncomputable def freeAppIsoFinsupp
    (I : Type u) [Finite I] (U : X.Opensᵒᵖ) :
    (SheafOfModules.free (R := X.ringCatSheaf) I).val.obj U ≅
      ModuleCat.of (X.presheaf.obj U) (I →₀ X.presheaf.obj U) := by
  let F := SheafOfModules.evaluation X.ringCatSheaf U
  letI : (SheafOfModules.evaluation X.ringCatSheaf U).Additive := by
    dsimp [SheafOfModules.evaluation]
    infer_instance
  haveI : PreservesColimit (Functor.const (Discrete I) |>.obj
      (SheafOfModules.unit X.ringCatSheaf)) F := by
    infer_instance
  exact IsColimit.coconePointUniqueUpToIso
    (isColimitOfPreserves F (SheafOfModules.isColimitFreeCofan I))
    (ModuleCat.finsuppCoconeIsColimit
      (X.presheaf.obj U) (X.presheaf.obj U) I)

private lemma freeAppIsoFinsupp_ιFree
    (I : Type u) [Finite I] (U : X.Opensᵒᵖ)
    (i : I) (r : X.presheaf.obj U) :
    (freeAppIsoFinsupp (X := X) I U).hom
        ((SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app U r) =
      Finsupp.single i r := by
  let F := SheafOfModules.evaluation X.ringCatSheaf U
  letI : (SheafOfModules.evaluation X.ringCatSheaf U).Additive := by
    dsimp [SheafOfModules.evaluation]
    infer_instance
  haveI : PreservesColimit (Functor.const (Discrete I) |>.obj
      (SheafOfModules.unit X.ringCatSheaf)) F := by
    infer_instance
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitOfPreserves F (SheafOfModules.isColimitFreeCofan I))
    (ModuleCat.finsuppCoconeIsColimit
      (X.presheaf.obj U) (X.presheaf.obj U) I) (Discrete.mk i)
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) r

private noncomputable def constantType (I : Type u) :=
  (Functor.const X.Opensᵒᵖ).obj I

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def freeForgetIso (I : Type u) [Finite I] :
    (SheafOfModules.forget X.ringCatSheaf).obj
        (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
        (constantType (X := X) I) :=
  PresheafOfModules.isoMk (fun U ↦ freeAppIsoFinsupp (X := X) I U) (by
    intro U V f
    rw [← cancel_epi (freeAppIsoFinsupp (X := X) I U).inv]
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro i
    apply LinearMap.ext
    intro r
    simp only [Iso.inv_hom_id_assoc]
    change (freeAppIsoFinsupp (X := X) I V).hom
        (((SheafOfModules.forget X.ringCatSheaf).obj
          (SheafOfModules.free (R := X.ringCatSheaf) I)).map f
            ((freeAppIsoFinsupp (X := X) I U).inv (Finsupp.single i r))) =
      (PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
        (constantType (X := X) I)).map f (Finsupp.single i r)
    have hinv : (freeAppIsoFinsupp (X := X) I U).inv
          (Finsupp.single i r) =
        (SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app U r := by
      apply (freeAppIsoFinsupp (X := X) I U).toLinearEquiv.injective
      exact (freeAppIsoFinsupp (X := X) I U).toLinearEquiv.apply_symm_apply _ |>.trans
        (freeAppIsoFinsupp_ιFree (X := X) I U i r).symm
    rw [hinv]
    change (freeAppIsoFinsupp (X := X) I V).hom
        ((SheafOfModules.free (R := X.ringCatSheaf) I).val.map f
          ((SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app U r)) = _
    have hn := PresheafOfModules.naturality_apply
      (SheafOfModules.ιFree (R := X.ringCatSheaf) i).val f r
    rw [← hn]
    rw [freeAppIsoFinsupp_ιFree]
    change Finsupp.single i (X.presheaf.map f r) =
      (PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
        (constantType (X := X) I)).map f (Finsupp.single i r)
    conv_rhs => rw [← Finsupp.smul_single_one i r]
    rw [PresheafOfModules.map_smul]
    dsimp only [PresheafOfModules.freeObj, constantType]
    rw [show Finsupp.single i (1 : X.presheaf.obj U) =
      ModuleCat.freeMk i from rfl]
    rw [ModuleCat.freeDesc_apply]
    change Finsupp.single i (X.ringCatSheaf.obj.map f r) =
      X.ringCatSheaf.obj.map f r •
        (Finsupp.single i 1 : I →₀ X.ringCatSheaf.obj.obj V)
    simp)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def topExteriorFreePresheafIso (n : ℕ) :
    PresheafOfModules.exteriorPower X.presheaf
        (PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
          (constantType (X := X) (ULift.{u} (Fin n)))) n ≅
      PresheafOfModules.unit X.ringCatSheaf.obj :=
  PresheafOfModules.isoMk (fun U ↦
    (topExteriorFreeEquiv (X.presheaf.obj U) n).toModuleIso) (by
      intro U V f
      apply ModuleCat.exteriorPower.hom_ext
      ext x
      change topExteriorFreeEquiv (X.presheaf.obj V) n
          (LinearMap.exteriorPower n (X.presheaf.map f).hom
            ((PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
              (constantType (X := X) (ULift.{u} (Fin n)))).restrictₛₗ f)
            (_root_.exteriorPower.ιMulti (X.presheaf.obj U) n x)) =
        X.presheaf.map f
          (topExteriorFreeEquiv (X.presheaf.obj U) n
            (_root_.exteriorPower.ιMulti (X.presheaf.obj U) n x))
      rw [LinearMap.exteriorPower_ιMulti]
      change topExteriorFreeEquiv (X.presheaf.obj V) n
          (_root_.exteriorPower.ιMulti (X.presheaf.obj V) n
            (((PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
              (constantType (X := X) (ULift.{u} (Fin n)))).restrictₛₗ f) ∘ x)) =
        X.presheaf.map f
          (topExteriorFreeEquiv (X.presheaf.obj U) n
            (_root_.exteriorPower.ιMulti (X.presheaf.obj U) n x))
      rw [topExteriorFreeEquiv_ιMulti, topExteriorFreeEquiv_ιMulti]
      let σ := (X.presheaf.map f).hom
      have hmap (y : ULift.{u} (Fin n) →₀ X.presheaf.obj U) :
          (show ULift.{u} (Fin n) →₀ X.presheaf.obj V from
            (PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
              (constantType (X := X) (ULift.{u} (Fin n)))).map f y) =
            Finsupp.mapRange σ σ.map_zero y := by
        induction y using Finsupp.induction with
        | zero => simp
        | single_add a r y _ha _hr ih =>
            rw [map_add]
            rw [Finsupp.mapRange_add σ.map_add]
            apply congrArg₂ (fun p q ↦ p + q)
            · conv_lhs => rw [← Finsupp.smul_single_one a r]
              rw [PresheafOfModules.map_smul]
              dsimp only [PresheafOfModules.freeObj, constantType]
              rw [show Finsupp.single a (1 : X.presheaf.obj U) =
                ModuleCat.freeMk a from rfl]
              rw [ModuleCat.freeDesc_apply]
              simp only [Finsupp.mapRange_single]
              simp only [Functor.const_obj_map]
              change (X.ringCatSheaf.obj.map f) r • Finsupp.single a 1 =
                Finsupp.single a ((X.ringCatSheaf.obj.map f) r)
              rw [Finsupp.smul_single_one]
            · exact ih
      have hentry (i j : Fin n) :
          (show ULift.{u} (Fin n) →₀ X.presheaf.obj V from
            (((PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
              (constantType (X := X) (ULift.{u} (Fin n)))).restrictₛₗ f) ∘ x) i)
              (Set.powersetCard.ofFinEmbEquiv.symm (topPowerset.{u} n) j) =
            σ ((show ULift.{u} (Fin n) →₀ X.presheaf.obj U from x i)
              (Set.powersetCard.ofFinEmbEquiv.symm (topPowerset.{u} n) j)) := by
        change (show ULift.{u} (Fin n) →₀ X.presheaf.obj V from
          (PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
            (constantType (X := X) (ULift.{u} (Fin n)))).map f (x i)) _ = _
        rw [hmap]
        simp
      simp_rw [hentry]
      exact (σ.map_det _).symm)

set_option maxHeartbeats 1600000 in
/-- The top exterior power of the free rank-`n` module sheaf is the structure sheaf. -/
noncomputable def topExteriorFreeIso (n : ℕ) :
    exteriorPower
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) n ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (PresheafOfModules.exteriorPower.mapIso
        (freeForgetIso (X := X) (ULift.{u} (Fin n))) n ≪≫
        topExteriorFreePresheafIso (X := X) n) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app
        (SheafOfModules.unit X.ringCatSheaf)

end

end AlgebraicGeometry.Scheme.Modules
