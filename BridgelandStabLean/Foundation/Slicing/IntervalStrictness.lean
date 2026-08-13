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

/-- A strict monomorphism in a thin interval becomes monic in the right
adjacent heart. -/
theorem Slicing.IntervalCat.mono_toRightHeart_of_strictMono (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) (hf : IsStrictMono f) :
    Mono ((Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map f) := by
  let t := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  let q : Y ⟶ cokernel f := cokernel.π f
  let qH : FR.obj Y ⟶ FR.obj (cokernel f) := FR.map q
  let eQ := Slicing.IntervalCat.toRightHeartCokernelIso
    (C := C) (s := s) (a := a) (b := b) f
  have hqHeq : qH ≫ eQ.hom = cokernel.π (FR.map f) := by
    simpa [qH, FR, eQ] using
      Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom
        (C := C) (s := s) (a := a) (b := b) f
  have himage_zero : Abelian.image.ι (FR.map f) ≫ qH = 0 := by
    apply (cancel_mono eQ.hom).1
    rw [Category.assoc, hqHeq, zero_comp]
    change kernel.ι (cokernel.π (FR.map f)) ≫ cokernel.π (FR.map f) = 0
    exact kernel.condition (cokernel.π (FR.map f))
  have himage_kernel : IsLimit
      (KernelFork.ofι (Abelian.image.ι (FR.map f)) himage_zero) :=
    isKernelOfComp (f := qH) eQ.hom (cokernel.π (FR.map f))
      (kernelIsKernel (cokernel.π (FR.map f))) himage_zero hqHeq
  have hkernel_qH :
      IsLimit (KernelFork.ofι (kernel.ι qH) (kernel.condition qH)) := by
    simpa using kernelIsKernel qH
  let eKh : Abelian.image (FR.map f) ⟶ kernel qH :=
    hkernel_qH.lift
      (KernelFork.ofι (Abelian.image.ι (FR.map f)) himage_zero)
  have heKh : eKh ≫ kernel.ι qH = Abelian.image.ι (FR.map f) := by
    dsimp only [eKh]
    exact hkernel_qH.fac
      (KernelFork.ofι (Abelian.image.ι (FR.map f)) himage_zero)
      Limits.WalkingParallelPair.zero
  let eKi : kernel qH ⟶ Abelian.image (FR.map f) :=
    himage_kernel.lift
      (KernelFork.ofι (kernel.ι qH) (kernel.condition qH))
  have heKi : eKi ≫ Abelian.image.ι (FR.map f) = kernel.ι qH := by
    dsimp only [eKi]
    exact himage_kernel.fac
      (KernelFork.ofι (kernel.ι qH) (kernel.condition qH))
      Limits.WalkingParallelPair.zero
  let eK : Abelian.image (FR.map f) ≅ kernel qH := by
    refine ⟨eKh, eKi, ?_, ?_⟩
    · apply (cancel_mono (Abelian.image.ι (FR.map f))).1
      rw [Category.assoc, heKi, heKh]
      simp
    · apply (cancel_mono (kernel.ι qH)).1
      rw [Category.assoc, heKh, heKi]
      simp
  let iH : FR.obj X ⟶ kernel qH :=
    Abelian.factorThruImage (FR.map f) ≫ eK.hom
  have hiH : iH ≫ kernel.ι qH = FR.map f := by
    change (Abelian.factorThruImage (FR.map f) ≫ eK.hom) ≫
      kernel.ι qH = FR.map f
    rw [Category.assoc, heKh, Abelian.image.fac]
  haveI : Epi iH := by
    letI : IsIso eK.hom := ⟨⟨eK.inv, eK.hom_inv_id, eK.inv_hom_id⟩⟩
    exact CategoryTheory.epi_comp'
      (CategoryTheory.Abelian.instEpiFactorThruImage (f := FR.map f))
      inferInstance
  have hK_mem : s.intervalProp C a b (kernel qH).obj :=
    s.intervalProp_of_epi_rightHeart (C := C) (a := a) (b := b)
      (Fact.out : a < b) X.property iH
  let KI : s.IntervalCat C a b := ⟨(kernel qH).obj, hK_mem⟩
  let k : KI ⟶ Y := ObjectProperty.homMk (kernel.ι qH).hom
  let i : X ⟶ KI := ObjectProperty.homMk iH.hom
  have hk_zero : k ≫ q = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kernel.ι qH ≫ qH).hom = 0
    simp
  have hi : i ≫ k = f := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (iH ≫ kernel.ι qH).hom = (FR.map f).hom
    rw [hiH]
  have hk_limit : IsLimit (KernelFork.ofι k hk_zero) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W} g hg ↦ ?_)
      (fun {W} g hg ↦ ?_) (fun {W} g hg m hm ↦ ?_)
    · let gH := FR.map g
      have hgH : gH ≫ qH = 0 := by
        apply t.ιHeart.map_injective
        change g.hom ≫ q.hom = 0
        exact congr_arg (·.hom) hg
      exact ObjectProperty.homMk (kernel.lift qH gH hgH).hom
    · let gH := FR.map g
      have hgH : gH ≫ qH = 0 := by
        apply t.ιHeart.map_injective
        change g.hom ≫ q.hom = 0
        exact congr_arg (·.hom) hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (kernel.lift qH gH hgH ≫ kernel.ι qH).hom = g.hom
      simp [gH, FR]
    · let gH := FR.map g
      have hgH : gH ≫ qH = 0 := by
        apply t.ιHeart.map_injective
        change g.hom ≫ q.hom = 0
        exact congr_arg (·.hom) hg
      let mH : FR.obj W ⟶ kernel qH := ObjectProperty.homMk m.hom
      have hmH : mH ≫ kernel.ι qH = kernel.lift qH gH hgH ≫ kernel.ι qH := by
        apply t.ιHeart.map_injective
        change m.hom ≫ (kernel.ι qH).hom =
          (kernel.lift qH gH hgH ≫ kernel.ι qH).hom
        simp [gH, FR]
        exact congr_arg (·.hom) hm
      have hmEq : mH = kernel.lift qH gH hgH :=
        Fork.IsLimit.hom_ext (kernelIsKernel qH) hmH
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (kernel.lift qH gH hgH).hom
      simpa [mH] using congr_arg (·.hom) hmEq
  let e : X ≅ KI :=
    IsLimit.conePointUniqueUpToIso hf.isLimitKernelFork hk_limit
  have he : e.hom ≫ k = f := by
    dsimp only [e]
    exact IsLimit.conePointUniqueUpToIso_hom_comp
      hf.isLimitKernelFork hk_limit Limits.WalkingParallelPair.zero
  let j : kernel qH ≅ FR.obj KI := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;>
      ext <;> simp
  have hk_map : j.inv ≫ kernel.ι qH = FR.map k := by
    apply t.ιHeart.map_injective
    change (j.inv ≫ kernel.ι qH).hom = (FR.map k).hom
    simp [FR, k, j]
  have hk_eq : FR.map k = j.inv ≫ kernel.ι qH := hk_map.symm
  let eH : FR.obj X ≅ FR.obj KI := FR.mapIso e
  have hmapf : eH.hom ≫ FR.map k = FR.map f := by
    simpa [eH] using congrArg FR.map he
  letI : IsIso eH.hom := ⟨⟨eH.inv, eH.hom_inv_id, eH.inv_hom_id⟩⟩
  letI : IsIso j.inv := ⟨⟨j.hom, j.inv_hom_id, j.hom_inv_id⟩⟩
  haveI : Mono (eH.hom ≫ (j.inv ≫ kernel.ι qH)) := inferInstance
  have hfac : FR.map f ≫ 𝟙 _ = eH.hom ≫ (j.inv ≫ kernel.ι qH) := by
    simpa [Category.comp_id, hk_eq, Category.assoc] using hmapf.symm
  exact mono_of_mono_fac hfac

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

/-- A strict epimorphism in a thin interval becomes epic in the left adjacent
heart. -/
theorem Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi (s : Slicing C)
    {X Y : s.IntervalCat C a b} (f : X ⟶ Y) (hf : IsStrictEpi f) :
    Epi ((Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
      (Fact.out : b - a ≤ 1)).map f) := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  let k : kernel f ⟶ X := kernel.ι f
  let kH : FL.obj (kernel f) ⟶ FL.obj X := FL.map k
  let eK := Slicing.IntervalCat.toLeftHeartKernelIso
    (C := C) (s := s) (a := a) (b := b) f
  let eQ : cokernel kH ≅ cokernel (kernel.ι (FL.map f)) :=
    cokernel.mapIso kH (kernel.ι (FL.map f)) eK (Iso.refl _)
      (by
        simpa [kH, FL] using
          (Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι
            (C := C) (s := s) (a := a) (b := b) f).symm)
  let d : cokernel kH ⟶ FL.obj Y :=
    eQ.hom ≫ Abelian.factorThruCoimage (FL.map f)
  have hd : cokernel.π kH ≫ d = FL.map f := by
    calc
      cokernel.π kH ≫ d =
          cokernel.π kH ≫ eQ.hom ≫
            Abelian.factorThruCoimage (FL.map f) := by simp [d]
      _ = cokernel.π (kernel.ι (FL.map f)) ≫
            Abelian.factorThruCoimage (FL.map f) := by simp [eQ]
      _ = FL.map f := Abelian.coimage.fac (FL.map f)
  haveI : Mono d := by
    letI : CategoryTheory.NonPreadditiveAbelian t.heart.FullSubcategory :=
      CategoryTheory.Abelian.nonPreadditiveAbelian
        (C := t.heart.FullSubcategory)
    letI : IsIso eQ.hom := ⟨⟨eQ.inv, eQ.hom_inv_id, eQ.inv_hom_id⟩⟩
    letI : Mono eQ.hom := by infer_instance
    change Mono (eQ.hom ≫ Abelian.factorThruCoimage (FL.map f))
    exact CategoryTheory.mono_comp'
      (hg := inferInstance)
      (hf := CategoryTheory.Abelian.instMonoFactorThruCoimage (f := FL.map f))
  have hQ_mem : s.intervalProp C a b (cokernel kH).obj :=
    s.intervalProp_of_mono_leftHeart (C := C) (a := a) (b := b)
      (Fact.out : a < b) Y.property d
  let QI : s.IntervalCat C a b := ⟨(cokernel kH).obj, hQ_mem⟩
  let p : X ⟶ QI := ObjectProperty.homMk (cokernel.π kH).hom
  have hp_zero : k ≫ p = 0 := by
    apply ((s.intervalProp C a b).ι).map_injective
    change (kH ≫ cokernel.π kH).hom = 0
    simp
  have hp_colim : IsColimit (CokernelCofork.ofπ p hp_zero) := by
    refine CokernelCofork.IsColimit.ofπ _ _ (fun {W} g hg ↦ ?_)
      (fun {W} g hg ↦ ?_) (fun {W} g hg m hm ↦ ?_)
    · let gH := FL.map g
      have hgH : kH ≫ gH = 0 := by
        apply t.ιHeart.map_injective
        change k.hom ≫ g.hom = 0
        exact congr_arg (·.hom) hg
      exact ObjectProperty.homMk (cokernel.desc kH gH hgH).hom
    · let gH := FL.map g
      have hgH : kH ≫ gH = 0 := by
        apply t.ιHeart.map_injective
        change k.hom ≫ g.hom = 0
        exact congr_arg (·.hom) hg
      apply ((s.intervalProp C a b).ι).map_injective
      change (cokernel.π kH ≫ cokernel.desc kH gH hgH).hom = g.hom
      simp [gH, FL]
    · let gH := FL.map g
      have hgH : kH ≫ gH = 0 := by
        apply t.ιHeart.map_injective
        change k.hom ≫ g.hom = 0
        exact congr_arg (·.hom) hg
      let mH : cokernel kH ⟶ FL.obj W := ObjectProperty.homMk m.hom
      have hmH : cokernel.π kH ≫ mH =
          cokernel.π kH ≫ cokernel.desc kH gH hgH := by
        apply t.ιHeart.map_injective
        change (cokernel.π kH).hom ≫ m.hom =
          (cokernel.π kH ≫ cokernel.desc kH gH hgH).hom
        simp [gH, FL]
        simpa [mH, p] using congr_arg (·.hom) hm
      have hmEq : mH = cokernel.desc kH gH hgH :=
        Cofork.IsColimit.hom_ext (cokernelIsCokernel kH) hmH
      apply ((s.intervalProp C a b).ι).map_injective
      change m.hom = (cokernel.desc kH gH hgH).hom
      simpa [mH] using congr_arg (·.hom) hmEq
  let e : QI ≅ Y :=
    IsColimit.coconePointUniqueUpToIso hp_colim hf.isColimitCokernelCofork
  have he : p ≫ e.hom = f := by
    dsimp only [e]
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      hp_colim hf.isColimitCokernelCofork Limits.WalkingParallelPair.one
  let j : FL.obj QI ≅ cokernel kH := by
    refine ⟨ObjectProperty.homMk (𝟙 _), ObjectProperty.homMk (𝟙 _), ?_, ?_⟩ <;>
      ext <;> simp
  have hj : FL.map p ≫ j.hom = cokernel.π kH := by
    apply t.ιHeart.map_injective
    change (FL.map p ≫ j.hom).hom = (cokernel.π kH).hom
    simp [FL, p, j]
  have hp_eq : FL.map p = cokernel.π kH ≫ j.inv := by
    letI : IsIso j.hom := ⟨⟨j.inv, j.hom_inv_id, j.inv_hom_id⟩⟩
    letI : Mono j.hom := by infer_instance
    exact (cancel_mono j.hom).1 (by simpa [Category.assoc] using hj)
  have hp_epi : Epi (FL.map p) := by
    letI : IsIso j.inv := ⟨⟨j.hom, j.inv_hom_id, j.hom_inv_id⟩⟩
    haveI : Epi (cokernel.π kH ≫ j.inv) := inferInstance
    simpa [hp_eq]
  let eH : FL.obj QI ≅ FL.obj Y := FL.mapIso e
  have hmapf : FL.map p ≫ eH.hom = FL.map f := by
    simpa [eH] using congrArg FL.map he
  letI : IsIso eH.hom := ⟨⟨eH.inv, eH.hom_inv_id, eH.inv_hom_id⟩⟩
  haveI : Epi (FL.map p ≫ eH.hom) := inferInstance
  simpa [hmapf]

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

/-- Strict epimorphisms in a thin interval are closed under composition. -/
theorem Slicing.IntervalCat.comp_strictEpi (s : Slicing C)
    {X Y Z : s.IntervalCat C a b} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsStrictEpi f) (hg : IsStrictEpi g) :
    IsStrictEpi (f ≫ g) := by
  let t := (s.phaseShift C a).toTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FL := Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  haveI : Epi (FL.map f) :=
    Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi C s f hf
  haveI : Epi (FL.map g) :=
    Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi C s g hg
  haveI : Epi (FL.map (f ≫ g)) := by
    simpa using (show Epi (FL.map f ≫ FL.map g) by infer_instance)
  exact Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart C s (f ≫ g)

/-- Strict monomorphisms in a thin interval are closed under composition. -/
theorem Slicing.IntervalCat.comp_strictMono (s : Slicing C)
    {X Y Z : s.IntervalCat C a b} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsStrictMono f) (hg : IsStrictMono g) :
    IsStrictMono (f ≫ g) := by
  let t := (s.phaseShift C (b - 1)).toDualTStructure C
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := heartFullSubcategoryAbelian t
  let FR := Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b
    (Fact.out : b - a ≤ 1)
  haveI : Mono (FR.map f) :=
    Slicing.IntervalCat.mono_toRightHeart_of_strictMono C s f hf
  haveI : Mono (FR.map g) :=
    Slicing.IntervalCat.mono_toRightHeart_of_strictMono C s g hg
  haveI : Mono (FR.map (f ≫ g)) := by
    simpa using (show Mono (FR.map f ≫ FR.map g) by infer_instance)
  exact Slicing.IntervalCat.strictMono_of_mono_toRightHeart C s (f ≫ g)

end

end BridgelandStabLean.Foundation
