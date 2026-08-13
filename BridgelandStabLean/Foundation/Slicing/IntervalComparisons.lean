/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Slicing.IntervalPreabelian

/-!
# Comparison isomorphisms for owner interval limits

The canonical kernel and cokernel selected in a thin interval agree with the
objects computed in the corresponding adjacent abelian hearts.  These
comparison isomorphisms are the bridge from the preabelian existence layer to
strictness and quasi-abelianity.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace BridgelandStabLean.Foundation

open BridgelandStabLean.ForMathlib.CategoryTheory.Triangulated.TStructure

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

section

variable {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]

/-- The canonical interval kernel agrees with the kernel computed in the left
adjacent abelian heart. -/
noncomputable def Slicing.IntervalCat.toLeftHeartKernelIso (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    let t := (s.phaseShift C a).toTStructure C
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
    let FL := Slicing.IntervalCat.toLeftHeart (s := s) (C := C) a b
      (Fact.out : b - a ≤ 1)
    FL.obj (kernel f) ≅ kernel (FL.map f) := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FL := Slicing.IntervalCat.toLeftHeart (s := s) (C := C) a b
    (Fact.out : b - a ≤ 1)
  let fH := FL.map f
  have hKer_mem : s.intervalProp C a b (kernel fH).obj :=
    s.intervalProp_of_mono_leftHeart C (Fact.out : a < b) X.property
      (kernel.ι fH)
  let KI : s.IntervalCat C a b := ⟨(kernel fH).obj, hKer_mem⟩
  let k : KI ⟶ X := ObjectProperty.homMk (kernel.ι fH).hom
  have hk_zero : k ≫ f = 0 := by
    ext
    exact congr_arg (·.hom) (kernel.condition fH)
  let hk_lim : IsLimit (KernelFork.ofι k hk_zero) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W} g hg ↦ ?_)
      (fun {W} g hg ↦ ?_) (fun {W} g hg m hm ↦ ?_)
    · let gH := FL.map g
      have hgH : gH ≫ fH = 0 := by
        apply t.ιHeart.map_injective
        change g.hom ≫ f.hom = 0
        exact congr_arg (·.hom) hg
      exact ObjectProperty.homMk (kernel.lift fH gH hgH).hom
    · let gH := FL.map g
      have hgH : gH ≫ fH = 0 := by
        apply t.ιHeart.map_injective
        change g.hom ≫ f.hom = 0
        exact congr_arg (·.hom) hg
      ext
      exact congr_arg (·.hom) (kernel.lift_ι fH gH hgH)
    · let gH := FL.map g
      have hgH : gH ≫ fH = 0 := by
        apply t.ιHeart.map_injective
        change g.hom ≫ f.hom = 0
        exact congr_arg (·.hom) hg
      let mH : FL.obj W ⟶ kernel fH := ObjectProperty.homMk m.hom
      have hmH : mH ≫ kernel.ι fH = kernel.lift fH gH hgH ≫ kernel.ι fH := by
        ext
        rw [show (kernel.lift fH gH hgH ≫ kernel.ι fH).hom = gH.hom by
          exact congr_arg (·.hom) (kernel.lift_ι fH gH hgH)]
        change m.hom ≫ k.hom = g.hom
        exact congr_arg (·.hom) hm
      have hmEq : mH = kernel.lift fH gH hgH :=
        Fork.IsLimit.hom_ext (kernelIsKernel fH) hmH
      ext
      exact congr_arg (·.hom) hmEq
  let e : KI ≅ kernel f :=
    IsLimit.conePointUniqueUpToIso hk_lim (limit.isLimit _)
  let eH : FL.obj (kernel f) ≅ FL.obj KI := FL.mapIso e.symm
  let j : FL.obj KI ≅ kernel fH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;>
      ext <;> simp
  exact eH ≪≫ j

/-- The canonical interval cokernel agrees with the cokernel computed in the
right adjacent abelian heart. -/
noncomputable def Slicing.IntervalCat.toRightHeartCokernelIso (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) :
    let t := (s.phaseShift C (b - 1)).toDualTStructure C
    letI := t.hasHeartFullSubcategory
    letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
    let FR := Slicing.IntervalCat.toRightHeart (s := s) (C := C) a b
      (Fact.out : b - a ≤ 1)
    FR.obj (cokernel f) ≅ cokernel (FR.map f) := by
  let t := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FR := Slicing.IntervalCat.toRightHeart (s := s) (C := C) a b
    (Fact.out : b - a ≤ 1)
  let fH := FR.map f
  have hCoker_mem : s.intervalProp C a b (cokernel fH).obj :=
    s.intervalProp_of_epi_rightHeart C (Fact.out : a < b) Y.property
      (cokernel.π fH)
  let QI : s.IntervalCat C a b := ⟨(cokernel fH).obj, hCoker_mem⟩
  let p : Y ⟶ QI := ObjectProperty.homMk (cokernel.π fH).hom
  have hp_zero : f ≫ p = 0 := by
    ext
    exact congr_arg (·.hom) (cokernel.condition fH)
  let hp_colim : IsColimit (CokernelCofork.ofπ p hp_zero) := by
    refine CokernelCofork.IsColimit.ofπ _ _ (fun {W} g hg ↦ ?_)
      (fun {W} g hg ↦ ?_) (fun {W} g hg m hm ↦ ?_)
    · let gH := FR.map g
      have hgH : fH ≫ gH = 0 := by
        apply t.ιHeart.map_injective
        change f.hom ≫ g.hom = 0
        exact congr_arg (·.hom) hg
      exact ObjectProperty.homMk (cokernel.desc fH gH hgH).hom
    · let gH := FR.map g
      have hgH : fH ≫ gH = 0 := by
        apply t.ιHeart.map_injective
        change f.hom ≫ g.hom = 0
        exact congr_arg (·.hom) hg
      ext
      exact congr_arg (·.hom) (cokernel.π_desc fH gH hgH)
    · let gH := FR.map g
      have hgH : fH ≫ gH = 0 := by
        apply t.ιHeart.map_injective
        change f.hom ≫ g.hom = 0
        exact congr_arg (·.hom) hg
      let mH : cokernel fH ⟶ FR.obj W := ObjectProperty.homMk m.hom
      have hmH : cokernel.π fH ≫ mH = cokernel.π fH ≫ cokernel.desc fH gH hgH := by
        ext
        rw [show (cokernel.π fH ≫ cokernel.desc fH gH hgH).hom = gH.hom by
          exact congr_arg (·.hom) (cokernel.π_desc fH gH hgH)]
        change p.hom ≫ m.hom = g.hom
        exact congr_arg (·.hom) hm
      have hmEq : mH = cokernel.desc fH gH hgH :=
        Cofork.IsColimit.hom_ext (cokernelIsCokernel fH) hmH
      ext
      exact congr_arg (·.hom) hmEq
  let e : QI ≅ cokernel f :=
    IsColimit.coconePointUniqueUpToIso hp_colim (colimit.isColimit _)
  let eH : FR.obj (cokernel f) ≅ FR.obj QI := FR.mapIso e.symm
  let j : FR.obj QI ≅ cokernel fH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;>
      ext <;> simp
  exact eH ≪≫ j

end

end BridgelandStabLean.Foundation
