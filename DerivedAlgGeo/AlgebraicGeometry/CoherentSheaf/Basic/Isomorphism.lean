/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Basic.Definitions
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Isomorphism invariance of coherence

A finite local presentation can be transported across an isomorphism of sheaves of modules:
restrict the isomorphism to every object in the chosen cover and postcompose each presentation
with the resulting isomorphism. Consequently, coherent sheaves on a scheme are closed under
isomorphisms in the ambient category of sheaves of modules.
-/

universe u

open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] [Limits.HasBinaryProducts C]
  {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [hasSheafCompose : ∀ X,
    (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [hasSheafify : ∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [hasWeakSheafify : ∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [wEqualsLocallyBijective : ∀ X,
    (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transport local presentation data across an isomorphism of sheaves of modules.

This is the project-facing, iso-valued wrapper around Mathlib's `QuasicoherentData.ofIsIso`.
-/
noncomputable def QuasicoherentData.ofIso {M N : SheafOfModules.{u} R}
    (q : M.QuasicoherentData) (e : M ≅ N) : N.QuasicoherentData :=
  q.ofIsIso e.hom

instance QuasicoherentData.isFinitePresentation_ofIso
    {M N : SheafOfModules.{u} R} (q : M.QuasicoherentData) (e : M ≅ N)
    [q.IsFinitePresentation] : (q.ofIso e).IsFinitePresentation := by
  dsimp only [QuasicoherentData.ofIso]
  infer_instance

omit [Limits.HasBinaryProducts C] in
/-- Finite presentation is preserved by an isomorphism of sheaves of modules. -/
theorem IsFinitePresentation.of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N)
    (hM : M.IsFinitePresentation) : N.IsFinitePresentation := by
  obtain ⟨q, hq⟩ := hM.exists_quasicoherentData
  letI := hq
  exact ⟨q.ofIso e, inferInstance⟩

instance isFinitePresentation_isClosedUnderIsomorphisms :
    (isFinitePresentation R).IsClosedUnderIsomorphisms where
  of_iso e hM := hM.of_iso e

end SheafOfModules

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- Coherent sheaves on `X` are closed under isomorphisms in `X.Modules`. -/
instance coherent_isClosedUnderIsomorphisms :
    (coherent X).IsClosedUnderIsomorphisms where
  of_iso {M N} e hM := by
    change SheafOfModules.IsFinitePresentation N
    change SheafOfModules.IsFinitePresentation M at hM
    exact SheafOfModules.IsFinitePresentation.of_iso
      (R := X.ringCatSheaf) (M := M) (N := N) e hM

end AlgebraicGeometry.Scheme
