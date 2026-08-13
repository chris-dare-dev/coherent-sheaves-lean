/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.QuasiAbelian
import BridgelandStabLean.Foundation.Slicing.IntervalComparisons

/-!
# Strict morphisms detected by adjacent slicing hearts

For a thin slicing interval, monicity in the right adjacent heart detects a
strict monomorphism, while epicity in the left adjacent heart detects a strict
epimorphism.  The proof transports the abelian kernel/cokernel universal
property across the owner comparison isomorphisms and reflects it through the
fully faithful interval embedding.
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

/-- A map in a thin interval which becomes monic in the right adjacent heart
is a strict monomorphism. -/
theorem Slicing.IntervalCat.strictMono_of_mono_toRightHeart (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y)
    [Mono ((Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map f)] :
    IsStrictMono f := by
  let t := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  let eQ := Slicing.IntervalCat.toRightHeartCokernelIso
    (C := C) (s := s) (a := a) (b := b) f
  let eDiag :
      parallelPair (FR.map (cokernel.π f)) 0 ≅
        parallelPair (cokernel.π (FR.map f)) 0 :=
    parallelPair.ext (Iso.refl _) eQ
      (by
        simpa [FR, eQ] using
          Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom
            (C := C) (s := s) (a := a) (b := b) f)
      (by simp)
  have hlim' : IsLimit
      (KernelFork.ofι (FR.map f) (by
        apply t.ιHeart.map_injective
        change (f ≫ cokernel.π f).hom = 0
        simp) : Fork (FR.map (cokernel.π f)) 0) := by
    let c : Fork (cokernel.π (FR.map f)) 0 :=
      KernelFork.ofι (FR.map f) (cokernel.condition (FR.map f))
    let q : Cofork (FR.map f) 0 :=
      CokernelCofork.ofπ (cokernel.π (FR.map f))
        (cokernel.condition (FR.map f))
    have hcanon : IsLimit c :=
      Abelian.monoIsKernelOfCokernel q (cokernelIsCokernel (FR.map f))
    let htrans := (IsLimit.postcomposeInvEquiv eDiag c).symm hcanon
    exact IsLimit.ofIsoLimit htrans <|
      Fork.ext (Iso.refl _) (by
        change (Iso.refl _).hom ≫ c.ι =
          c.ι ≫ eDiag.inv.app WalkingParallelPair.zero
        simp [eDiag])
  have hmap : IsLimit
      (FR.mapCone (KernelFork.ofι f (cokernel.condition f))) :=
    (isLimitMapConeForkEquiv' FR (cokernel.condition f)).symm hlim'
  have hlim : IsLimit (KernelFork.ofι f (cokernel.condition f)) :=
    isLimitOfReflects FR hmap
  exact isStrictMono_of_isLimitKernelFork hlim

/-- A map in a thin interval which becomes epic in the left adjacent heart is
a strict epimorphism. -/
theorem Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y)
    [Epi ((Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map f)] :
    IsStrictEpi f := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  let eK := Slicing.IntervalCat.toLeftHeartKernelIso
    (C := C) (s := s) (a := a) (b := b) f
  let eDiag :
      parallelPair (FL.map (kernel.ι f)) 0 ≅
        parallelPair (kernel.ι (FL.map f)) 0 :=
    parallelPair.ext eK (Iso.refl _)
      (by
        simpa [FL, eK] using
          (Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι
            (C := C) (s := s) (a := a) (b := b) f).symm)
      (by simp)
  have hcolim' : IsColimit
      (CokernelCofork.ofπ (FL.map f) (by
        apply t.ιHeart.map_injective
        change (kernel.ι f ≫ f).hom = 0
        simp) : Cofork (FL.map (kernel.ι f)) 0) := by
    let c : Cofork (kernel.ι (FL.map f)) 0 :=
      CokernelCofork.ofπ (FL.map f) (kernel.condition (FL.map f))
    have hcanon : IsColimit c :=
      Abelian.epiIsCokernelOfKernel
        (KernelFork.ofι (kernel.ι (FL.map f))
          (kernel.condition (FL.map f)))
        (kernelIsKernel (FL.map f))
    let htrans := (IsColimit.precomposeHomEquiv eDiag c).symm hcanon
    exact IsColimit.ofIsoColimit htrans <|
      Cofork.ext (Iso.refl _) (by
        have hπ : Cofork.π ((Cocone.precompose eDiag.hom).obj c) =
            eDiag.hom.app WalkingParallelPair.one ≫ c.π := rfl
        have h₁ : Cofork.π ((Cocone.precompose eDiag.hom).obj c) ≫
              (Iso.refl ((Cocone.precompose eDiag.hom).obj c).pt).hom =
            eDiag.hom.app WalkingParallelPair.one ≫ c.π := by
          simpa [Category.assoc] using congrArg
            (fun k ↦ k ≫ (Iso.refl ((Cocone.precompose eDiag.hom).obj c).pt).hom) hπ
        have h₂ : eDiag.hom.app WalkingParallelPair.one ≫ c.π = FL.map f := by
          simp [c, eDiag]
        exact h₁.trans h₂)
  have hmap : IsColimit
      (FL.mapCocone (CokernelCofork.ofπ f (kernel.condition f))) :=
    (isColimitMapCoconeCoforkEquiv' FL (kernel.condition f)).symm hcolim'
  have hcolim : IsColimit (CokernelCofork.ofπ f (kernel.condition f)) :=
    isColimitOfReflects FL hmap
  exact isStrictEpi_of_isColimitCokernelCofork hcolim

end

end BridgelandStabLean.Foundation
