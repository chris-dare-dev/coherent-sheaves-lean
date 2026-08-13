/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import BridgelandStabLean.ForMathlib.CategoryTheory.Triangulated.TStructure.HeartAbelian
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Image factorisations in triangulated hearts

This Apache-2.0 ForMathlib bridge exposes the two distinguished triangles
attached to the canonical image factorisation of a morphism in a t-structure
heart.  It is derived from Mathlib's abelian-heart instance and its existing
epi-to-triangle theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace BridgelandStabLean.ForMathlib

namespace CategoryTheory.Triangulated.TStructure

open _root_.CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

variable {H : Type u} [Category.{v} H] [Preadditive H]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [IsTriangulated C] in
/-- A monomorphism in any presentation of a t-structure heart completes to a
distinguished triangle whose third vertex is again in that heart. -/
theorem exists_distinguished_triangle_of_heart_mono (t : TStructure C)
    [hHeart : t.Heart H] {X Y : H} (i : X ⟶ Y) [Mono i] :
    ∃ (Q : H) (q : Y ⟶ Q)
      (δ : (t.ιHeart.obj Q) ⟶ (t.ιHeart.obj X)⟦(1 : ℤ)⟧),
      Triangle.mk ((t.ιHeart (H := H)).map i)
        ((t.ιHeart (H := H)).map q) δ ∈ distTriang C := by
  let ι := t.ιHeart (H := H)
  obtain ⟨Z, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map i)
  have hadm : _root_.CategoryTheory.Triangulated.AbelianSubcategory.admissibleMorphism
      ι i := by
    rw [heart_admissible t]
    trivial
  obtain ⟨K, Q, α, β, γ, hT'⟩ := hadm f₂ f₃ hT
  let k : K ⟶ X :=
    _root_.CategoryTheory.Triangulated.AbelianSubcategory.ιK f₃ α
  letI : Mono k :=
    _root_.CategoryTheory.Triangulated.AbelianSubcategory.mono_ιK
      (heart_hι t) hT hT'
  have hk : k = 0 := by
    rw [← cancel_mono i, zero_comp]
    exact _root_.CategoryTheory.Triangulated.AbelianSubcategory.ιK_mor₁ hT α
  have hK : IsZero K := by
    rw [IsZero.iff_id_eq_zero, ← cancel_mono k, Category.id_comp, zero_comp, hk]
  have hshiftK : IsZero ((ι.obj K)⟦(1 : ℤ)⟧) :=
    (shiftFunctor C (1 : ℤ)).map_isZero (ι.map_isZero hK)
  letI : IsIso β := (Triangle.isZero₁_iff_isIso₂ _ hT').1 hshiftK
  refine ⟨Q, ι.preimage (f₂ ≫ β), inv β ≫ f₃, ?_⟩
  refine isomorphic_distinguished _ hT _ ?_
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso β).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [IsTriangulated C] in
/-- An epimorphism in any presentation of a t-structure heart completes to a
distinguished triangle whose first vertex is again in that heart. -/
theorem exists_distinguished_triangle_of_heart_epi (t : TStructure C)
    [hHeart : t.Heart H] {X Y : H} (p : X ⟶ Y) [Epi p] :
    ∃ (K : H) (i : K ⟶ X)
      (δ : (t.ιHeart.obj Y) ⟶ (t.ιHeart.obj K)⟦(1 : ℤ)⟧),
      Triangle.mk ((t.ιHeart (H := H)).map i)
        ((t.ιHeart (H := H)).map p) δ ∈ distTriang C := by
  exact _root_.CategoryTheory.Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
    (heart_hι t) (heart_admissible t) p

/-- The canonical image factorisation of a heart morphism supplies its image,
epimorphic projection, monomorphic inclusion, and the distinguished kernel
triangle of that projection in the ambient triangulated category. -/
theorem exists_image_factorisation_epi_triangle (t : TStructure C)
    {X Y : t.heart.FullSubcategory} (f : X ⟶ Y) :
    ∃ (I K : t.heart.FullSubcategory)
      (p : X ⟶ I) (i : I ⟶ Y)
      (k : K ⟶ X) (δp : I.obj ⟶ K.obj⟦(1 : ℤ)⟧),
      p ≫ i = f ∧ Mono i ∧
        Triangle.mk k.hom p.hom δp ∈ distTriang C := by
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let ι := t.ιHeart (H := t.heart.FullSubcategory)
  let I := Abelian.image f
  let p : X ⟶ I := Abelian.factorThruImage f
  let i : I ⟶ Y := Abelian.image.ι f
  obtain ⟨K, k, δp, hTp⟩ :=
    _root_.CategoryTheory.Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (ι := ι) (heart_hι t) (heart_admissible t) p
  refine ⟨I, K, p, i, k, δp, ?_, inferInstance, ?_⟩
  · exact Abelian.image.fac f
  · exact hTp

/-- The canonical image factorisation of a heart morphism is represented in
the ambient triangulated category by distinguished triangles on both sides of
the image.  Thus the epimorphism onto the image has a kernel in the heart, and
the monomorphism from the image has a cokernel in the heart. -/
theorem exists_image_factorisation_triangles (t : TStructure C)
    {X Y : t.heart.FullSubcategory} (f : X ⟶ Y) :
    ∃ (I K Q : t.heart.FullSubcategory)
      (p : X ⟶ I) (i : I ⟶ Y) (k : K ⟶ X) (q : Y ⟶ Q)
      (δp : I.obj ⟶ K.obj⟦(1 : ℤ)⟧)
      (δi : Q.obj ⟶ I.obj⟦(1 : ℤ)⟧),
      p ≫ i = f ∧ Epi p ∧ Mono i ∧
        Triangle.mk k.hom p.hom δp ∈ distTriang C ∧
        Triangle.mk i.hom q.hom δi ∈ distTriang C := by
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let ι := t.ιHeart (H := t.heart.FullSubcategory)
  let I := Abelian.image f
  let p : X ⟶ I := Abelian.factorThruImage f
  let i : I ⟶ Y := Abelian.image.ι f
  obtain ⟨K, k, δp, hTp⟩ :=
    _root_.CategoryTheory.Triangulated.AbelianSubcategory.exists_distinguished_triangle_of_epi
      (ι := ι) (heart_hι t) (heart_admissible t) p
  obtain ⟨Q, q, δi, hTi⟩ := exists_distinguished_triangle_of_heart_mono t i
  refine ⟨I, K, Q, p, i, k, q, δp, δi, ?_, inferInstance, inferInstance, ?_, ?_⟩
  · exact Abelian.image.fac f
  · exact hTp
  · exact hTi

end CategoryTheory.Triangulated.TStructure

end BridgelandStabLean.ForMathlib
