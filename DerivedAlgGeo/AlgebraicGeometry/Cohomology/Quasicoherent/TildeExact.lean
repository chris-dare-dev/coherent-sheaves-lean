/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Quasicoherent.Kernels
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.AffineVanishing

/-!
# `tilde` is exact, and `Γ` is left exact, on an affine spectrum

The two functor-level facts the quasi-coherent extension argument runs on,
proved in the cohomology layer where that argument will live.

## What is here

* `tilde.functor R` preserves finite limits. Right exactness is free —
  `tilde.adjunction` makes it a left adjoint — so this is the whole of exactness.
  The proof is the kernel closure of `CoherentSheaf/Quasicoherent/Kernels.lean`:
  `tilde` factors through `tildeEquiv` and the inclusion of quasi-coherent
  sheaves, and that inclusion is left exact exactly because quasi-coherence is
  closed under ambient kernels.
* `moduleSpecΓFunctor` preserves finite limits, reconstructed here rather than
  imported — `Abelian/Kernels.lean` proves it for a `private` section functor and
  cannot export it.

Finite products and abelianness on the quasi-coherent subcategory are transported
across `tildeEquiv` rather than postulated, which is why no closure property
beyond kernels is needed to get them.

## What is deliberately not here

The extension closure itself. See the note on #720: the remaining step is the
affine five lemma, and it is blocked on a typing seam rather than on mathematics
— `moduleSpecΓFunctor` has domain `(Spec (.of R)).Modules` while the geometry is
stated over `(Spec R).Modules`, so an instance proved for one is not found for
the other. `Modules/Affine/Equivalence.lean` documents that wrapper problem and
`Abelian/Kernels.lean` works around it with a private retyped section functor.
-/
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

noncomputable section

variable {R : CommRingCat.{u}}

/-! ### Exactness of `tilde` -/

/-- Finite products on affine quasi-coherent sheaves, transported across the
tilde equivalence rather than postulated on the full subcategory. -/
noncomputable local instance qcHasFiniteProducts :
    HasFiniteProducts
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
  ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence (tildeEquiv (R := R)).inverse⟩

noncomputable local instance qcHasBinaryBiproducts :
    HasBinaryBiproducts
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- Quasi-coherent sheaves on an affine spectrum are abelian, by the proved tilde
equivalence with modules over the coordinate ring. -/
noncomputable local instance qcAbelian :
    Abelian (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory :=
  abelianOfEquivalence (tildeEquiv (R := R)).inverse

/-- The inclusion of quasi-coherent sheaves preserves kernels — this is the
kernel closure of `Quasicoherent/Kernels.lean`, in the form limit-preservation
wants it. -/
noncomputable instance qcι_preservesKernel
    {M N : (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory}
    (g : M ⟶ N) :
    PreservesLimit (parallelPair g 0)
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)) :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).preservesKernels_ι g

/-- The inclusion of quasi-coherent sheaves into all module sheaves on an affine
spectrum preserves finite limits. -/
noncomputable instance quasicoherentι_preservesFiniteLimits :
    PreservesFiniteLimits
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- **`tilde` is exact.**

Right exactness is free — `tilde.adjunction` makes it a left adjoint. Left
exactness is this: `tilde` factors through `tildeEquiv` and the inclusion of
quasi-coherent sheaves, and that inclusion is left exact because quasi-coherence
is closed under ambient kernels. -/
noncomputable instance tilde_preservesFiniteLimits :
    PreservesFiniteLimits (tilde.functor R) := by
  letI : PreservesFiniteLimits ((tildeEquiv (R := R)).functor ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso
    (F := (tildeEquiv (R := R)).functor ⋙
      ObjectProperty.ι (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf))
    (G := tilde.functor R) (Iso.refl _)


/-! ### The affine five lemma -/

attribute [local instance] HasExt.standard

/-! `moduleSpecΓFunctor` is definitionally `moduleSpecSectionsFunctor R ⊤`, which
already carries these instances; stating them once here saves every downstream
proof the `change`. -/

noncomputable instance moduleSpecΓFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (moduleSpecΓFunctor (R := R)) := by
  letI hModules : PreservesFiniteLimits (modulesSpecToSheaf (R := R)) :=
    modulesSpecToSheaf_preservesFiniteLimits R
  letI hForget : PreservesFiniteLimits
      (TopCat.Sheaf.forget (ModuleCat R) (Spec R)) := inferInstance
  letI hEval : PreservesFiniteLimits
      ((evaluation (TopologicalSpace.Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
        (.op (⊤ : (Spec R).Opens))) := inferInstance
  letI hTail : PreservesFiniteLimits
      (TopCat.Sheaf.forget (ModuleCat R) (Spec R) ⋙
        (evaluation (TopologicalSpace.Opens (Spec R))ᵒᵖ (ModuleCat R)).obj
          (.op (⊤ : (Spec R).Opens))) :=
    @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hForget hEval
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _ hModules hTail

noncomputable instance moduleSpecΓFunctor_preservesZeroMorphisms :
    (moduleSpecΓFunctor (R := R)).PreservesZeroMorphisms :=
  inferInstance

end

end AlgebraicGeometry
