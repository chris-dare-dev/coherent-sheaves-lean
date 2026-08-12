/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Exterior powers of sheaves of modules

This file constructs exterior powers in two stages. First, a semilinear map of modules induces
a semilinear map on exterior powers. Applying this to restriction maps gives the objectwise
exterior-power presheaf. Sheafification then gives `Scheme.Modules.exteriorPower`.
-/

open CategoryTheory LinearMap

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

end

end AlgebraicGeometry.Scheme.Modules
