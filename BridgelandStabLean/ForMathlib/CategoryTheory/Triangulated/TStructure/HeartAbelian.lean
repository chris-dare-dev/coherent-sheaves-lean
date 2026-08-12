/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The heart of a t-structure is abelian

Following [BBD, *Faisceaux pervers*, Théorème 1.3.6], via Mathlib's own criterion
`AbelianSubcategory.abelian`.

## Provenance and licence

Vendored from `BridgelandStability.TStructure.HeartAbelian` (revision `9e48f23a`),
which is Apache-2.0. **This file retains the Apache-2.0 header of its origin and
is not relicensed**, notwithstanding the MIT default of the rest of this
repository. It is placed in the `BridgelandStabLean.ForMathlib` namespace rather
than in `CategoryTheory`, so that a module importing both this file and the
foundational library does not see two constants with the same fully-qualified
name.

## Why it is here, and why it is small

Mathlib already ships the BBD criterion — `AbelianSubcategory.abelian`, at
`Mathlib/CategoryTheory/Triangulated/TStructure/AbelianSubcategory.lean` line 302
(`v4.29.0`) / 308 (`v4.32.1`), present and unchanged at both pins. What Mathlib
does **not** do is apply it to a t-structure heart: the only references to
`AbelianSubcategory` anywhere in Mathlib's `Triangulated/TStructure/` directory
are self-references inside that one file.

So heart-is-abelian is not unbuilt mathematics. It is this file: two hypothesis
discharges (`heart_hι`, `heart_admissible`) against machinery Mathlib owns.

## Upstreaming

This is a strong upstreaming candidate precisely because the engine is already
there and only the obvious instance is missing.

**Deletion condition** — delete this file when

```
lake build
```

resolves `Abelian t.heart.FullSubcategory` from Mathlib without this import.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Category
open scoped ZeroObject

universe v' u' v u

namespace BridgelandStabLean.ForMathlib

namespace CategoryTheory.Triangulated.TStructure

open _root_.CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)
  {H : Type u'} [Category.{v'} H] [Preadditive H] [t.Heart H]

/-- **No negative Hom spaces in the heart.** For heart objects `X` and `Y`, every morphism
`ι X ⟶ (ι Y)⟦n⟧` is zero when `n < 0`. -/
theorem heart_hι :
    ∀ ⦃X Y : H⦄ ⦃n : ℤ⦄ (f : (t.ιHeart).obj X ⟶ ((t.ιHeart).obj Y)⟦n⟧),
      n < 0 → f = 0 := by
  intro X Y n f hn
  haveI : t.IsGE ((t.ιHeart.obj Y)⟦n⟧) (-n) := t.isGE_shift _ 0 n (-n)
  exact t.zero f 0 (-n) (by lia)

/-- **Admissibility of heart morphisms.** Every morphism in the heart is admissible: for
`f₁ : X₁ → X₂` in the heart, the cone `X₃` of `ι.map f₁` decomposes as
`(ι K)⟦1⟧ → X₃ → ι Q` via the truncation triangle, with `K, Q` in the heart. -/
theorem heart_admissible :
    AbelianSubcategory.admissibleMorphism (t.ιHeart (H := H)) = ⊤ := by
  ext X₁ X₂ f₁
  simp only [MorphismProperty.top_apply, iff_true]
  intro X₃ f₂ f₃ hT
  set T := Triangle.mk (t.ιHeart.map f₁) f₂ f₃
  haveI hX₃_le : t.IsLE X₃ 0 := by
    have hrot := rot_of_distTriang _ hT
    apply t.isLE₂ _ hrot 0
    · change t.IsLE ((t.ιHeart).obj X₂) 0; infer_instance
    · change t.IsLE (((t.ιHeart).obj X₁)⟦(1 : ℤ)⟧) 0
      haveI := t.isLE_shift ((t.ιHeart).obj X₁) 0 1 (-1)
      exact t.isLE_of_le _ (-1) 0
  haveI hX₃_ge : t.IsGE X₃ (-1) := by
    have hrot := rot_of_distTriang _ hT
    apply t.isGE₂ _ hrot (-1)
    · change t.IsGE ((t.ιHeart).obj X₂) (-1)
      exact t.isGE_of_ge _ (-1) 0
    · change t.IsGE (((t.ιHeart).obj X₁)⟦(1 : ℤ)⟧) (-1)
      exact t.isGE_shift _ 0 1 (-1)
  have hQ_le : t.IsLE ((t.truncGE 0).obj X₃) 0 := by
    have hrot_trunc := rot_of_distTriang _ (t.triangleLTGE_distinguished 0 X₃)
    apply t.isLE₂ _ hrot_trunc 0
    · change t.IsLE X₃ 0; exact hX₃_le
    · change t.IsLE (((t.truncLT 0).obj X₃)⟦(1 : ℤ)⟧) 0
      haveI : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
      haveI := t.isLE_shift ((t.truncLT 0).obj X₃) (-1) 1 (-2)
      exact t.isLE_of_le _ (-2) 0
  have hQ_heart : t.heart ((t.truncGE 0).obj X₃) :=
    (t.mem_heart_iff _).mpr ⟨hQ_le, inferInstance⟩
  have hK_ge : t.IsGE ((t.truncLT 0).obj X₃) (-1) := by
    have hinv := inv_rot_of_distTriang _ (t.triangleLTGE_distinguished 0 X₃)
    apply t.isGE₂ _ hinv (-1)
    · change t.IsGE (((t.truncGE 0).obj X₃)⟦(-1 : ℤ)⟧) (-1)
      haveI : t.IsGE (((t.truncGE 0).obj X₃)⟦(-1 : ℤ)⟧) 1 := t.isGE_shift _ 0 (-1) 1
      exact t.isGE_of_ge _ (-1) 1
    · change t.IsGE X₃ (-1)
      exact hX₃_ge
  haveI : t.IsLE ((t.truncLT 0).obj X₃) (-1) := t.isLE_truncLT_obj ..
  have hK_heart : t.heart (((t.truncLT 0).obj X₃)⟦(-1 : ℤ)⟧) :=
    (t.mem_heart_iff _).mpr ⟨t.isLE_shift _ (-1) (-1) 0, t.isGE_shift _ (-1) (-1) 0⟩
  rw [← t.essImage_ιHeart H] at hQ_heart hK_heart
  obtain ⟨Q, ⟨eQ⟩⟩ := hQ_heart
  obtain ⟨K, ⟨eK⟩⟩ := hK_heart
  let e₁ : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ≅ (t.truncLT 0).obj X₃ :=
    (shiftFunctor C (1 : ℤ)).mapIso eK ≪≫
      (shiftEquiv C (1 : ℤ)).counitIso.app ((t.truncLT 0).obj X₃)
  let α : (t.ιHeart.obj K)⟦(1 : ℤ)⟧ ⟶ X₃ := e₁.hom ≫ (t.truncLTι 0).app X₃
  let β : X₃ ⟶ t.ιHeart.obj Q := (t.truncGEπ 0).app X₃ ≫ eQ.inv
  let γ : t.ιHeart.obj Q ⟶ (t.ιHeart.obj K)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧ :=
    eQ.hom ≫ (t.truncGEδLT 0).app X₃ ≫ (shiftFunctor C (1 : ℤ)).map e₁.inv
  exact ⟨K, Q, α, β, γ, isomorphic_distinguished _
    (t.triangleLTGE_distinguished 0 X₃) _
    (Triangle.isoMk _ _ e₁ (Iso.refl _) eQ
      (by dsimp [α, _root_.CategoryTheory.Triangulated.TStructure.triangleLTGE]; simp)
      (by dsimp [β, _root_.CategoryTheory.Triangulated.TStructure.triangleLTGE]; simp)
      (by dsimp [γ]; simp))⟩

variable [IsTriangulated C] [HasFiniteProducts H] in
/-- **Heart abelianity.** The heart of a t-structure on a triangulated category is abelian,
assuming the heart has finite products. -/
@[reducible]
noncomputable def heartAbelian : Abelian H :=
  AbelianSubcategory.abelian (t.ιHeart (H := H)) (heart_hι t) (heart_admissible t)

/-! ### The heart contains zero and is closed under binary products -/

/-- The zero object lies in the heart of any t-structure. -/
instance heart_containsZero : t.heart.ContainsZero where
  exists_zero := ⟨0, isZero_zero C, (t.mem_heart_iff _).mpr ⟨inferInstance, inferInstance⟩⟩

/-- The biproduct of two heart objects lies in the heart. -/
lemma heart_biprod (X Y : C) (hX : t.heart X) (hY : t.heart Y) :
    t.heart (X ⊞ Y) := by
  rw [t.mem_heart_iff] at hX hY ⊢
  have hT := binaryBiproductTriangle_distinguished X Y
  exact ⟨t.isLE₂ _ hT 0 hX.1 hY.1, t.isGE₂ _ hT 0 hX.2 hY.2⟩

/-- The heart of a t-structure is closed under binary products. -/
instance heart_closedUnderBinaryProducts :
    t.heart.IsClosedUnderBinaryProducts :=
  ObjectProperty.IsClosedUnderLimitsOfShape.mk' (by
    rintro _ ⟨F, hF⟩
    set A := F.obj ⟨WalkingPair.left⟩
    set B := F.obj ⟨WalkingPair.right⟩
    have e_diag : F ≅ pair A B :=
      Discrete.natIso (fun ⟨j⟩ ↦ match j with
        | WalkingPair.left => Iso.refl _
        | WalkingPair.right => Iso.refl _)
    have e : A ⊞ B ≅ limit F :=
      (biprod.isoProd A B) ≪≫ (HasLimit.isoOfNatIso e_diag).symm
    exact t.heart.prop_of_iso e
      (heart_biprod t A B (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)))

/-- The heart of a t-structure is closed under finite products. -/
instance heart_closedUnderFiniteProducts : t.heart.IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- The full subcategory defined by the heart has finite products. -/
noncomputable instance heart_hasFiniteProducts :
    HasFiniteProducts t.heart.FullSubcategory :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- **Heart abelianity (canonical form).** The full subcategory of heart objects of a
t-structure on a triangulated category is abelian. -/
@[reducible]
noncomputable def heartFullSubcategoryAbelian [IsTriangulated C] :
    Abelian t.heart.FullSubcategory :=
  haveI := t.hasHeartFullSubcategory
  heartAbelian t (H := t.heart.FullSubcategory)

/-! ### Distinguished triangles in the heart give short exact sequences -/

set_option backward.isDefEq.respectTransparency false in
/-- A distinguished triangle whose three vertices lie in the heart induces a short
exact sequence in the heart. -/
theorem heartFullSubcategory_shortExact_of_distTriang [IsTriangulated C]
    {A B Q : t.heart.FullSubcategory}
    {f : A ⟶ B} {g : B ⟶ Q} {δ : Q.obj ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f.hom g.hom δ ∈ distTriang C) :
    (ShortComplex.mk f g (by
      ext
      exact comp_distTriang_mor_zero₁₂ _ hT)).ShortExact := by
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let S : ShortComplex t.heart.FullSubcategory := ShortComplex.mk f g (by
    ext
    exact comp_distTriang_mor_zero₁₂ _ hT)
  have hKer : IsLimit (KernelFork.ofι S.f S.zero) := by
    simpa [S] using _root_.CategoryTheory.Triangulated.AbelianSubcategory.isLimitKernelForkOfDistTriang
      (heart_hι t) f g δ hT
  have hCok : IsColimit (CokernelCofork.ofπ S.g S.zero) := by
    simpa [S] using _root_.CategoryTheory.Triangulated.AbelianSubcategory.isColimitCokernelCoforkOfDistTriang
      (heart_hι t) f g δ hT
  have hExact : S.Exact := ShortComplex.exact_of_f_is_kernel (S := S) hKer
  exact ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKer) (Cofork.IsColimit.epi hCok)

/-! ### Truncation-functor naturality -/

@[reassoc]
theorem truncGE_map_comp_descTruncGE
    {X Y Z : C} (g : X ⟶ Y) (f : Y ⟶ Z) (n : ℤ) [t.IsGE Z n] :
    (t.truncGE n).map g ≫ t.descTruncGE f n = t.descTruncGE (g ≫ f) n := by
  apply t.from_truncGE_obj_ext
  rw [← Category.assoc, t.truncGEπ_naturality]
  have h₁ : (g ≫ (t.truncGEπ n).app Y) ≫ t.descTruncGE f n = g ≫ f := by
    simpa [Category.assoc] using
      congrArg (fun k => g ≫ k) (t.π_descTruncGE (f := f) (n := n))
  exact h₁.trans (t.π_descTruncGE (f := g ≫ f) (n := n)).symm

/-! ### An octahedral splitting of the truncation triangle -/

theorem exists_truncLT_octahedral_split [IsTriangulated C]
    {X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ X₁⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) (a : ℤ) :
    ∃ (Z : C) (v : X₂ ⟶ Z) (w : Z ⟶ ((t.truncLT a).obj X₁)⟦(1 : ℤ)⟧)
      (m₁ : (t.truncGE a).obj X₁ ⟶ Z) (m₃ : Z ⟶ X₃),
      Triangle.mk ((t.truncLTι a).app X₁ ≫ f) v w ∈ distTriang C ∧
      Triangle.mk m₁ m₃
        (δ ≫ ((shiftFunctor C (1 : ℤ)).map ((t.truncGEπ a).app X₁))) ∈ distTriang C ∧
      ((t.truncGEπ a).app X₁) ≫ m₁ = f ≫ v ∧
      m₁ ≫ w = (t.truncGEδLT a).app X₁ ∧
      v ≫ m₃ = g := by
  obtain ⟨Z, v, w, h13⟩ := distinguished_cocone_triangle ((t.truncLTι a).app X₁ ≫ f)
  let oct := _root_.CategoryTheory.Triangulated.someOctahedron rfl
    (t.triangleLTGE_distinguished a X₁) hT h13
  refine ⟨Z, v, w, oct.m₁, oct.m₃, h13, ?_, oct.comm₁, oct.comm₂, oct.comm₃⟩
  simpa using oct.mem

end CategoryTheory.Triangulated.TStructure

end BridgelandStabLean.ForMathlib
