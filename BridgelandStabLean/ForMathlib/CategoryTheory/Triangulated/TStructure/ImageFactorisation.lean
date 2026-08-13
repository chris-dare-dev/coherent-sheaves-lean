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

end CategoryTheory.Triangulated.TStructure

end BridgelandStabLean.ForMathlib
