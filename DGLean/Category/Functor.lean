/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DGLean.Category.Basic

/-!
# DG functors

A dg functor is an object map together with a degree-preserving `k`-linear map
on Hom-complexes that commutes with the differential and respects the identity
and the graded composition.

The map is required to commute with the differential degreewise rather than to
be packaged as a chain map: the composition of `DGCategoryStruct` is already
stated degreewise, and mixing the two styles is what makes later `simp` sets
fight each other.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u' u'' w

open CategoryTheory DGCategoryStruct

variable (k : Type w) [CommRing k]

/-- A dg functor between dg categories over `k`. -/
structure DGFunctor (C : Type u) (D : Type u')
    [DGCategory.{v} k C] [DGCategory.{v} k D] where
  /-- The map on objects. -/
  obj : C → D
  /-- The degree-preserving `k`-linear map on Hom-complexes. -/
  map {X Y : C} (p : ℤ) : (dgHom (k := k) X Y).X p →ₗ[k] (dgHom (k := k) (obj X) (obj Y)).X p
  /-- A dg functor commutes with the differential. -/
  map_d {X Y : C} (p q : ℤ) (f : (dgHom (k := k) X Y).X p) :
    map q (((dgHom (k := k) X Y).d p q).hom f) = ((dgHom (k := k) (obj X) (obj Y)).d p q).hom (map p f)
  /-- A dg functor preserves the identity. -/
  map_id (X : C) : map 0 (dgId X) = dgId (obj X)
  /-- A dg functor preserves the graded composition. -/
  map_comp {X Y Z : C} (p q r : ℤ) (h : p + q = r)
      (f : (dgHom (k := k) X Y).X p) (g : (dgHom (k := k) Y Z).X q) :
    map r (dgComp p q r h f g) = dgComp p q r h (map p f) (map q g)

namespace DGFunctor

variable {k}
variable {C : Type u} {D : Type u'} {E : Type u''}
  [DGCategory.{v} k C] [DGCategory.{v} k D] [DGCategory.{v} k E]

/-- The identity dg functor. -/
@[simps]
def id (C : Type u) [DGCategory.{v} k C] : DGFunctor k C C where
  obj X := X
  map _ := LinearMap.id
  map_d _ _ _ := rfl
  map_id _ := rfl
  map_comp _ _ _ _ _ _ := rfl

/-- Composition of dg functors. -/
@[simps]
def comp (F : DGFunctor k C D) (G : DGFunctor k D E) : DGFunctor k C E where
  obj X := G.obj (F.obj X)
  map p := (G.map p).comp (F.map p)
  map_d p q f := by simp [F.map_d p q f, G.map_d p q (F.map p f)]
  map_id X := by simp [F.map_id X, G.map_id (F.obj X)]
  map_comp p q r h f g := by simp [F.map_comp p q r h f g, G.map_comp p q r h (F.map p f) (F.map q g)]

end DGFunctor
