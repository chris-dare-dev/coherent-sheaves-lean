/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Strict morphisms for owner quasi-abelian foundations

This module owns the small categorical vocabulary needed by Bridgeland's
thin-interval argument.  A morphism is strict when its canonical coimage to
image comparison is an isomorphism.  The universal-property criteria below
avoid importing the corresponding vendor module.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace BridgelandStabLean.Foundation

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

section

variable {X Y : C} (f : X ⟶ Y)
  [HasKernel f] [HasCokernel f]
  [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]

/-- A morphism is strict when the canonical coimage-to-image comparison is
an isomorphism. -/
def IsStrict : Prop :=
  IsIso (Abelian.coimageImageComparison f)

/-- A strict monomorphism. -/
structure IsStrictMono : Prop where
  mono : Mono f
  strict : IsStrict f

/-- A strict epimorphism. -/
structure IsStrictEpi : Prop where
  epi : Epi f
  strict : IsStrict f

end

section

variable {X Y : C} {f : X ⟶ Y} [HasZeroObject C]
  [HasKernel f] [HasCokernel f]
  [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]

/-- A morphism which is the cokernel of its kernel is a strict epimorphism. -/
theorem isStrictEpi_of_isColimitCokernelCofork
    (hf : IsColimit (CokernelCofork.ofπ f (kernel.condition f))) :
    IsStrictEpi f := by
  haveI : Epi f := Cofork.IsColimit.epi hf
  let e : Abelian.coimage f ≅ Y :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (kernel.ι f)) hf
  have he : Abelian.coimage.π f ≫ e.hom = f := by
    have he' := IsColimit.comp_coconePointUniqueUpToIso_hom
      (cokernelIsCokernel (kernel.ι f)) hf Limits.WalkingParallelPair.one
    dsimp [Abelian.coimage, e, CokernelCofork.ofπ] at he'
    exact he'
  have hcomp : Abelian.coimageImageComparison f ≫ Abelian.image.ι f = e.hom := by
    apply (cancel_epi (Abelian.coimage.π f)).1
    rw [he]
    exact Abelian.coimage_image_factorisation (f := f)
  refine ⟨inferInstance, ?_⟩
  letI : IsIso (Abelian.image.ι f) := kernel.of_cokernel_of_epi (f := f)
  letI : Mono (Abelian.image.ι f) := by infer_instance
  change IsIso (Abelian.coimageImageComparison f)
  rw [show Abelian.coimageImageComparison f = e.hom ≫ inv (Abelian.image.ι f) from by
    apply (cancel_mono (Abelian.image.ι f)).1
    simpa [Abelian.image] using hcomp]
  infer_instance

/-- A morphism which is the kernel of its cokernel is a strict monomorphism. -/
theorem isStrictMono_of_isLimitKernelFork
    (hf : IsLimit (KernelFork.ofι f (cokernel.condition f))) :
    IsStrictMono f := by
  haveI : Mono f := Fork.IsLimit.mono hf
  have hker : IsLimit
      (KernelFork.ofι (Abelian.image.ι f)
        (kernel.condition (cokernel.π f))) := by
    simpa [Abelian.image, KernelFork.ofι] using
      (kernelIsKernel (cokernel.π f))
  let u : X ⟶ Abelian.image f :=
    hker.lift (KernelFork.ofι f (cokernel.condition f))
  have hu : u ≫ Abelian.image.ι f = f :=
    hker.fac (KernelFork.ofι f (cokernel.condition f))
      Limits.WalkingParallelPair.zero
  let w : Abelian.image f ⟶ X :=
    hf.lift (KernelFork.ofι (Abelian.image.ι f)
      (kernel.condition (cokernel.π f)))
  have hw : w ≫ f = Abelian.image.ι f :=
    hf.fac (KernelFork.ofι (Abelian.image.ι f)
      (kernel.condition (cokernel.π f))) Limits.WalkingParallelPair.zero
  let e : X ≅ Abelian.image f :=
    ⟨u, w, by
      apply (cancel_mono f).1
      rw [Category.assoc, hw, hu]
      simp, by
      apply (cancel_mono (Abelian.image.ι f)).1
      rw [Category.assoc, hu, hw]
      simp⟩
  have he : e.hom ≫ Abelian.image.ι f = f := hu
  have hcomp : Abelian.coimage.π f ≫
      Abelian.coimageImageComparison f = e.hom := by
    apply (cancel_mono (Abelian.image.ι f)).1
    rw [he]
    rw [Category.assoc]
    exact Abelian.coimage_image_factorisation (f := f)
  refine ⟨inferInstance, ?_⟩
  letI : IsIso (Abelian.coimage.π f) := cokernel.of_kernel_of_mono (f := f)
  letI : Epi (Abelian.coimage.π f) := by infer_instance
  letI : IsIso e.hom := ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  change IsIso (Abelian.coimageImageComparison f)
  rw [show Abelian.coimageImageComparison f = inv (Abelian.coimage.π f) ≫ e.hom from by
    apply (cancel_epi (Abelian.coimage.π f)).1
    simpa [Abelian.image] using hcomp]
  infer_instance

/-- A strict epimorphism is the cokernel of its kernel. -/
noncomputable def IsStrictEpi.isColimitCokernelCofork
    (hf : IsStrictEpi f) :
    IsColimit (CokernelCofork.ofπ f (kernel.condition f)) := by
  letI : Epi f := hf.epi
  letI : IsIso (Abelian.coimageImageComparison f) := hf.strict
  letI : IsIso (kernel.ι (cokernel.π f)) :=
    kernel.of_cokernel_of_epi (f := f)
  let e : cokernel (kernel.ι f) ≅ Y :=
    asIso (Abelian.coimageImageComparison f ≫ kernel.ι (cokernel.π f))
  have hm : cokernel.π (kernel.ι f) ≫ e.hom = f := by
    change cokernel.π (kernel.ι f) ≫ Abelian.coimageImageComparison f ≫
      kernel.ι (cokernel.π f) = f
    exact Abelian.coimage_image_factorisation (f := f)
  exact cokernel.cokernelIso (kernel.ι f) f e hm

/-- A strict monomorphism is the kernel of its cokernel. -/
noncomputable def IsStrictMono.isLimitKernelFork
    (hf : IsStrictMono f) :
    IsLimit (KernelFork.ofι f (cokernel.condition f)) := by
  letI : Mono f := hf.mono
  letI : IsIso (Abelian.coimageImageComparison f) := hf.strict
  letI : IsIso (cokernel.π (kernel.ι f)) :=
    cokernel.of_kernel_of_mono (f := f)
  let e : X ≅ kernel (cokernel.π f) :=
    asIso (cokernel.π (kernel.ι f) ≫ Abelian.coimageImageComparison f)
  have hm : e.hom ≫ kernel.ι (cokernel.π f) = f := by
    dsimp [e]
    rw [Category.assoc]
    exact Abelian.coimage_image_factorisation (f := f)
  exact kernel.isoKernel (cokernel.π f) f e hm

/-- A strict epimorphism supplies a normal epimorphism witness. -/
@[reducible]
noncomputable def IsStrictEpi.normalEpi (hf : IsStrictEpi f) : NormalEpi f where
  W := kernel f
  g := kernel.ι f
  w := kernel.condition f
  isColimit := hf.isColimitCokernelCofork

/-- A strict monomorphism supplies a normal monomorphism witness. -/
@[reducible]
noncomputable def IsStrictMono.normalMono (hf : IsStrictMono f) : NormalMono f where
  Z := cokernel f
  g := cokernel.π f
  w := cokernel.condition f
  isLimit := hf.isLimitKernelFork

end

section

variable [HasKernels C] [HasCokernels C]

/-- A kernel inclusion is a strict monomorphism. -/
theorem isStrictMono_kernel {X Y : C} (g : X ⟶ Y) :
    IsStrictMono (kernel.ι g) where
  mono := inferInstance
  strict := by
    have hk0 : kernel.ι (kernel.ι g) =
        (0 : kernel (kernel.ι g) ⟶ kernel g) :=
      (isZero_kernel_of_mono (kernel.ι g)).eq_zero_of_src _
    haveI : IsIso (cokernel.π (kernel.ι (kernel.ι g))) := by
      rw [hk0]
      infer_instance
    have hfactor : kernel.ι (cokernel.π (kernel.ι g)) ≫ g = 0 := by
      have hf := cokernel.π_desc (kernel.ι g) g (kernel.condition g)
      conv_lhs => rhs; rw [← hf]
      rw [← Category.assoc, kernel.condition, zero_comp]
    have hℓj : kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g)
          (cokernel.condition _) ≫
        kernel.lift g (kernel.ι (cokernel.π (kernel.ι g))) hfactor = 𝟙 _ := by
      ext
      simp
    have hjℓ : kernel.lift g (kernel.ι (cokernel.π (kernel.ι g))) hfactor ≫
        kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g)
          (cokernel.condition _) = 𝟙 _ := by
      ext
      simp
    haveI : IsIso
        (kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g)
          (cokernel.condition _)) := ⟨⟨_, hℓj, hjℓ⟩⟩
    change IsIso (Abelian.coimageImageComparison (kernel.ι g))
    have hπ : cokernel.π (kernel.ι (kernel.ι g)) ≫
        Abelian.coimageImageComparison (kernel.ι g) =
        kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g)
          (cokernel.condition _) :=
      cokernel.π_desc _ _ _
    rw [show Abelian.coimageImageComparison (kernel.ι g) =
        inv (cokernel.π (kernel.ι (kernel.ι g))) ≫
          kernel.lift (cokernel.π (kernel.ι g)) (kernel.ι g)
            (cokernel.condition _) from by
      rw [← hπ, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]]
    infer_instance

/-- A cokernel projection is a strict epimorphism. -/
theorem isStrictEpi_cokernel {X Y : C} (g : X ⟶ Y) :
    IsStrictEpi (cokernel.π g) where
  epi := inferInstance
  strict := by
    have hc0 : cokernel.π (cokernel.π g) =
        (0 : cokernel g ⟶ cokernel (cokernel.π g)) :=
      (isZero_cokernel_of_epi (cokernel.π g)).eq_zero_of_tgt _
    haveI : IsIso (kernel.ι (cokernel.π (cokernel.π g))) := by
      rw [hc0]
      infer_instance
    have hfactor : g ≫ cokernel.π (kernel.ι (cokernel.π g)) = 0 := by
      rw [← Abelian.coimage_image_factorisation_assoc g]
      simp
    have hhk : cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g)
          (kernel.condition _) ≫
        cokernel.desc g (cokernel.π (kernel.ι (cokernel.π g))) hfactor = 𝟙 _ := by
      apply (cancel_epi (cokernel.π (kernel.ι (cokernel.π g)))).mp
      simp
    have hkh : cokernel.desc g (cokernel.π (kernel.ι (cokernel.π g))) hfactor ≫
        cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g)
          (kernel.condition _) = 𝟙 _ := by
      apply (cancel_epi (cokernel.π g)).mp
      simp
    haveI : IsIso
        (cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g)
          (kernel.condition _)) := ⟨⟨_, hhk, hkh⟩⟩
    change IsIso (Abelian.coimageImageComparison (cokernel.π g))
    have hcomp : Abelian.coimageImageComparison (cokernel.π g) ≫
        kernel.ι (cokernel.π (cokernel.π g)) =
        cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g)
          (kernel.condition _) := by
      apply (cancel_epi (cokernel.π (kernel.ι (cokernel.π g)))).mp
      simp
    rw [show Abelian.coimageImageComparison (cokernel.π g) =
        cokernel.desc (kernel.ι (cokernel.π g)) (cokernel.π g)
          (kernel.condition _) ≫
          inv (kernel.ι (cokernel.π (cokernel.π g))) from by
      rw [← hcomp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]]
    infer_instance

end

section

variable [Preadditive C] [HasKernels C] [HasCokernels C]

/-- A strict short exact sequence is a short exact complex whose two maps are
strict. -/
structure StrictShortExact (S : ShortComplex C) : Prop where
  shortExact : S.ShortExact
  strict_f : IsStrict S.f
  strict_g : IsStrict S.g

end


end BridgelandStabLean.Foundation
