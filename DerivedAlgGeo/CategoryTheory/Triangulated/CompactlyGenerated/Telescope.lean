/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.FiniteSupport
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Mapping telescopes in triangulated categories

This file supplies the first missing categorical ingredient in the Brown-style
construction behind Theorem A.13 of arXiv:2607.28411v1.  For a sequence

`X₀ ⟶ X₁ ⟶ X₂ ⟶ ⋯`,

its mapping telescope is the cone of `1 - shift` on the countable coproduct of
the `Xₙ`.  The construction is deliberately triangulated rather than derived:
it only uses a countable coproduct and the axiom completing a morphism to a
distinguished triangle.

The factorization theorem below is the exactness property needed when the
Brown approximation tower is assembled.  It does not assert Brown
representability or compactness of any object.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.Triangulated.MappingTelescope

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

variable (X : ℕ → C) (f : ∀ n, X n ⟶ X (n + 1)) [HasCoproduct X]

/-- The endomorphism of the countable coproduct induced by the transition
maps of a sequence. -/
noncomputable def shiftMap : (∐ X) ⟶ (∐ X) :=
  Sigma.desc (fun n ↦ f n ≫ Sigma.ι X (n + 1))

omit [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] in
@[reassoc (attr := simp)]
theorem ι_shiftMap (n : ℕ) :
    Sigma.ι X n ≫ shiftMap X f = f n ≫ Sigma.ι X (n + 1) := by
  simpa only [shiftMap] using
    (Sigma.ι_desc (fun n ↦ f n ≫ Sigma.ι X (n + 1)) n)

/-- The morphism whose cone defines the mapping telescope. -/
noncomputable def map : (∐ X) ⟶ (∐ X) :=
  𝟙 (∐ X) - shiftMap X f

omit [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
@[reassoc]
theorem ι_map (n : ℕ) :
    Sigma.ι X n ≫ map X f =
      Sigma.ι X n - f n ≫ Sigma.ι X (n + 1) := by
  simp [map]

/-- A mapping telescope for a sequence, presented as a chosen distinguished
cone of `1 - shift`.  Different choices are noncanonically isomorphic; the
Brown construction only uses the distinguished-triangle interface. -/
structure Data where
  /-- The telescope object. -/
  obj : C
  /-- The coproduct-to-telescope morphism. -/
  hom : (∐ X) ⟶ obj
  /-- The connecting morphism. -/
  connecting : obj ⟶ (∐ X)⟦(1 : ℤ)⟧
  /-- The defining triangle is distinguished. -/
  distinguished :
    Triangle.mk (map X f) hom connecting ∈ distTriang C

/-- Every sequence with a countable coproduct admits a mapping telescope. -/
noncomputable def chosen : Data X f := by
  apply Classical.choice
  obtain ⟨Y, g, h, hT⟩ :=
    Pretriangulated.distinguished_cocone_triangle (map X f)
  exact ⟨⟨Y, g, h, hT⟩⟩

namespace Data

variable {X f} (T : Data X f)

/-- Compatible maps out of a sequence factor through its mapping telescope.

This is the `Hom(-, Z)` exactness statement for the distinguished triangle
defining the telescope. -/
theorem exists_desc {Z : C} (g : ∀ n, X n ⟶ Z)
    (hcompat : ∀ n, f n ≫ g (n + 1) = g n) :
    ∃ k : T.obj ⟶ Z, Sigma.desc g = T.hom ≫ k := by
  have hzero : map X f ≫ Sigma.desc g = 0 := by
    apply Sigma.hom_ext
    intro n
    rw [← Category.assoc, ι_map]
    simp only [Preadditive.sub_comp, Sigma.ι_desc,
      Category.assoc, comp_zero]
    rw [hcompat n, sub_self]
  exact Triangle.yoneda_exact₂
    (Triangle.mk (map X f) T.hom T.connecting)
    T.distinguished (Sigma.desc g) hzero

/-- The factorization through a telescope restricts to the original
compatible family on each coproduct summand. -/
theorem exists_desc_comp_ι {Z : C} (g : ∀ n, X n ⟶ Z)
    (hcompat : ∀ n, f n ≫ g (n + 1) = g n) :
    ∃ k : T.obj ⟶ Z, ∀ n, Sigma.ι X n ≫ T.hom ≫ k = g n := by
  obtain ⟨k, hk⟩ := T.exists_desc g hcompat
  refine ⟨k, fun n ↦ ?_⟩
  rw [← hk, Sigma.ι_desc]

end Data

end CategoryTheory.Triangulated.MappingTelescope
