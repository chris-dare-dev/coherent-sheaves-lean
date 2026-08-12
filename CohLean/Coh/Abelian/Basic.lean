/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import CohLean.Coh.Abelian.Extensions
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.Subcategory

/-!
# The abelian category of coherent sheaves

On a locally noetherian scheme, coherent module sheaves contain zero and are closed under
finite products, kernels, and cokernels. Mathlib's full-subcategory infrastructure therefore
makes `Coh X` abelian. The inclusion into all module sheaves creates kernels and cokernels,
hence preserves finite limits and finite colimits and is exact.

## Main results

* `Coh.abelian`;
* `Coh.exactInclusion`;
* `Coh.shortExact_map_ι`.
-/

universe u

open CategoryTheory Limits ZeroObject

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- The zero sheaf of modules has finite presentation. -/
noncomputable instance isFinitePresentation_containsZero [HasBinaryProducts C] :
    (isFinitePresentation R).ContainsZero where
  exists_zero := by
    let P := presentationOfIsCokernelFree
      (𝟙 (free (R := R) PEmpty)) (0 : free (R := R) PEmpty ⟶ 0) (by simp)
      (CokernelCofork.IsColimit.ofEpiOfIsZero _ (by infer_instance) (isZero_zero _))
    letI : P.IsFinite := by
      constructor
      · refine ⟨?_⟩
        change Finite PEmpty
        infer_instance
      · refine ⟨?_⟩
        change Finite PEmpty
        infer_instance
    exact ⟨0, isZero_zero _, IsFinitePresentation.of_presentation.{u, u, u} P⟩

end SheafOfModules

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The coherent property contains a zero module sheaf. -/
noncomputable instance coherent_containsZero : (coherent X).ContainsZero := by
  change (SheafOfModules.isFinitePresentation X.ringCatSheaf).ContainsZero
  exact SheafOfModules.isFinitePresentation_containsZero (R := X.ringCatSheaf)

/-- Coherent module sheaves are closed under binary products. -/
noncomputable instance coherent_isClosedUnderBinaryProducts :
    (coherent X).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro Y ⟨p⟩
    refine (coherent X).prop_of_iso ?_ ((coherent X).prop_biprod
      (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))
    exact IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

/-- Coherent module sheaves are closed under finite products. -/
noncomputable instance coherent_isClosedUnderFiniteProducts :
    (coherent X).IsClosedUnderFiniteProducts := .mk'

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Coh

variable (X : Scheme.{u})

/-- The preadditive structure inherited by the full subcategory of coherent sheaves. -/
noncomputable instance preadditive : Preadditive (Coh X) :=
  inferInstanceAs (Preadditive (Scheme.coherent X).FullSubcategory)

/-- Coherent sheaves on a locally noetherian scheme form an abelian category. -/
noncomputable instance abelian [IsLocallyNoetherian X] : Abelian (Coh X) := by
  change Abelian (Scheme.coherent X).FullSubcategory
  infer_instance

/-- The inclusion of coherent sheaves preserves zero morphisms. -/
noncomputable instance ι_preservesZeroMorphisms : (ι X).PreservesZeroMorphisms := by
  change (Scheme.coherent X).ι.PreservesZeroMorphisms
  infer_instance

/-- The inclusion of coherent sheaves is additive. -/
noncomputable instance ι_additive : (ι X).Additive := by
  change (Scheme.coherent X).ι.Additive
  infer_instance

/-- The inclusion of coherent sheaves preserves finite limits. -/
noncomputable instance ι_preservesFiniteLimits [IsLocallyNoetherian X] :
    PreservesFiniteLimits (ι X) := by
  letI : HasBinaryBiproducts (Coh X) := HasBinaryBiproducts.of_hasBinaryProducts
  letI : ∀ {A B : Coh X} (f : A ⟶ B), PreservesLimit (parallelPair f 0) (ι X) :=
    fun f ↦ (Scheme.coherent X).preservesKernels_ι f
  exact Functor.preservesFiniteLimits_of_preservesKernels (ι X)

/-- The inclusion of coherent sheaves preserves finite colimits. -/
noncomputable instance ι_preservesFiniteColimits [IsLocallyNoetherian X] :
    PreservesFiniteColimits (ι X) := by
  letI : HasBinaryBiproducts (Coh X) := HasBinaryBiproducts.of_hasBinaryCoproducts
  letI : ∀ {A B : Coh X} (f : A ⟶ B), PreservesColimit (parallelPair f 0) (ι X) :=
    fun f ↦ (Scheme.coherent X).preservesCokernels_ι f
  exact Functor.preservesFiniteColimits_of_preservesCokernels (ι X)

/-- The inclusion of coherent sheaves into all module sheaves, packaged as an exact functor. -/
noncomputable def exactInclusion [IsLocallyNoetherian X] :
    ExactFunctor (Coh X) X.Modules :=
  ExactFunctor.of (ι X)

/-- The inclusion of coherent sheaves sends short exact sequences to short exact sequences. -/
theorem shortExact_map_ι [IsLocallyNoetherian X] {S : ShortComplex (Coh X)}
    (hS : S.ShortExact) : (S.map (ι X)).ShortExact := by
  have hExact : ∀ (T : ShortComplex (Coh X)), T.ShortExact →
      (T.map (ι X)).ShortExact :=
    ((@Functor.exact_tfae _ _ _ _ _ _ (ι X) (ι_additive X)).out 3 0).mp
      (show PreservesFiniteLimits (ι X) ∧ PreservesFiniteColimits (ι X) from
        ⟨inferInstance, inferInstance⟩)
  exact hExact S hS

end AlgebraicGeometry.Coh
