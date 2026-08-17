/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Exactness

/-!
# Restricting t-structures detected by a t-exact functor

This file formalizes Steps 2 and 3 of Polishchuk's Theorem A.17 from
arXiv:2607.28411v1. If a t-exact functor detects membership in chosen bounded
subcategories, then restriction of the target t-structure forces restriction
of the source t-structure. If the functor also reflects zero objects, the two
halves of the restricted source t-structure are recognized exactly on the
target; these are formulas (A.3) and (A.4).

The theorem is independent of schemes and of the compact-generation argument
that constructs the large source t-structure in Step 1.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.ObjectProperty

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {F : Functor C D} {t : TStructure C} {t' : TStructure D}
  {P : ObjectProperty C} {Q : ObjectProperty D}

/-- Step 2 of A.17: restriction of the target t-structure and detection of
the two bounded subcategories imply restriction of the source t-structure.

The proof compares truncations using `Functor.mapTruncLEIso` and
`Functor.mapTruncGEIso`. Thus the conclusion is derived from t-exactness and
bounded-subcategory detection; it is not included among the premises. -/
theorem hasInducedTStructure_of_preimage
    [P.IsTriangulated] [Q.IsTriangulated]
    [Q.IsClosedUnderIsomorphisms] [Q.HasInducedTStructure t']
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t t']
    (hmem : ∀ X : C, P X ↔ Q (F.obj X)) :
    P.HasInducedTStructure t := by
  apply HasInducedTStructure.mk'
  intro X hX n
  have hFX : Q (F.obj X) := (hmem X).1 hX
  let TD := (t'.triangleLEGE n (n + 1) rfl).obj (F.obj X)
  have hTD : TD ∈ distTriang D :=
    t'.triangleLEGE_distinguished n (n + 1) rfl (F.obj X)
  have hQ := Q.mem_of_hasInductedTStructure t' TD hTD n (n + 1) rfl
    (by simpa only [TD, TStructure.triangleLEGE_obj_obj₁] using
      t'.isLE_truncLE_obj (F.obj X) n n)
    hFX
    (by simpa only [TD, TStructure.triangleLEGE_obj_obj₃] using
      t'.isGE_truncGE_obj (F.obj X) (n + 1) (n + 1))
  let TD' := (t'.triangleLEGE (n - 1) n (by omega)).obj (F.obj X)
  have hTD' : TD' ∈ distTriang D :=
    t'.triangleLEGE_distinguished (n - 1) n (by omega) (F.obj X)
  have hQ' := Q.mem_of_hasInductedTStructure t' TD' hTD' (n - 1) n (by omega)
    (by simpa only [TD', TStructure.triangleLEGE_obj_obj₁] using
      t'.isLE_truncLE_obj (F.obj X) (n - 1) (n - 1))
    hFX
    (by simpa only [TD', TStructure.triangleLEGE_obj_obj₃] using
      t'.isGE_truncGE_obj (F.obj X) n n)
  constructor
  · apply (hmem _).2
    exact Q.prop_of_iso (F.mapTruncLEIso t t' n X).symm
      (by simpa only [TD, TStructure.triangleLEGE_obj_obj₁] using hQ.1)
  · apply (hmem _).2
    exact Q.prop_of_iso (F.mapTruncGEIso t t' n X).symm
      (by simpa only [TD', TStructure.triangleLEGE_obj_obj₃] using hQ'.2)

/-- The functor between the two full subcategories selected by a detection
equivalence. -/
def preimageLift (F : Functor C D) (hmem : ∀ X : C, P X ↔ Q (F.obj X)) :
    Functor P.FullSubcategory Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F) (fun X ↦ (hmem X.obj).1 X.property)

/-- Formula (A.3) on the restricted categories. -/
theorem tStructure_isLE_iff_map
    [P.IsTriangulated] [Q.IsTriangulated]
    [P.HasInducedTStructure t] [Q.HasInducedTStructure t']
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t t']
    (hzero : ∀ E : C, IsZero (F.obj E) → IsZero E)
    (hmem : ∀ X : C, P X ↔ Q (F.obj X))
    (X : P.FullSubcategory) (n : ℤ) :
    (P.tStructure t).IsLE X n ↔
      (Q.tStructure t').IsLE ((preimageLift F hmem).obj X) n := by
  rw [P.tStructure_isLE_iff, Q.tStructure_isLE_iff]
  exact F.isLE_iff_of_reflectsZeroObjects t t' hzero X.obj n

/-- Formula (A.4) on the restricted categories. -/
theorem tStructure_isGE_iff_map
    [P.IsTriangulated] [Q.IsTriangulated]
    [P.HasInducedTStructure t] [Q.HasInducedTStructure t']
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsTExact t t']
    (hzero : ∀ E : C, IsZero (F.obj E) → IsZero E)
    (hmem : ∀ X : C, P X ↔ Q (F.obj X))
    (X : P.FullSubcategory) (n : ℤ) :
    (P.tStructure t).IsGE X n ↔
      (Q.tStructure t').IsGE ((preimageLift F hmem).obj X) n := by
  rw [P.tStructure_isGE_iff, Q.tStructure_isGE_iff]
  exact F.isGE_iff_of_reflectsZeroObjects t t' hzero X.obj n

end CategoryTheory.ObjectProperty
