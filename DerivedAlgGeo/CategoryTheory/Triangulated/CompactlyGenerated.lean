/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Exactness
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Compact generation in triangulated categories

This file supplies the large-category vocabulary used in Appendix A.2 of
arXiv:2607.28411v1. Mathlib has cardinal-presentable objects and the finite
triangulated envelope, but it does not yet contain the triangulated notion of
a compact object or the coproduct-and-extension closure `Coprod(G)`.

The definitions here follow A.9--A.11 literally:

* `Functor.PreservesSmallCoproducts` means preservation of all coproducts
  indexed in a fixed universe;
* `IsCompactObject` means that `Hom(K, -)` preserves those coproducts;
* `ObjectProperty.coprodClosure` is the smallest isomorphism-, coproduct-, and
  extension-closed object property containing its generators;
* `TStructure.IsCompactlyGeneratedBy` records compact generation of an
  already constructed t-structure.

Theorem A.13, which constructs a t-structure from compact generators, is not
smuggled into a typeclass or a global existence hypothesis here. Its
constructive Brown-tower proof lives in `CompactlyGenerated.Brown`, with the
smallness, local-smallness, coproduct, compactness, and shift-closure
hypotheses stated explicitly.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated Opposite

universe w v u u₁ u₂

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]

/-- A functor preserves the coproducts indexed by types in universe `w`.

Keeping the indexing universe explicit matches Mathlib's universe-sensitive
colimit API and avoids pretending that one category has literally all
large-universe coproducts. -/
def PreservesSmallCoproducts (F : Functor C D) : Prop :=
  ∀ (ι : Type w), PreservesColimitsOfShape (Discrete ι) F

end Functor

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Definition A.9: `K` is compact when `Hom(K, -)` preserves all small
coproducts in the indexing universe `w`.

The Hom functor is valued in additive commutative groups, so the colimit on
the target side is the direct sum of Hom groups.  Using ordinary set-valued
coyoneda here would instead form a disjoint union of Hom sets, which is not
the triangulated notion of compactness. -/
def IsCompactObject (K : C) : Prop :=
  ∀ (ι : Type w),
    PreservesColimitsOfShape (Discrete ι) (preadditiveCoyoneda.obj (op K))

namespace IsCompactObject

variable {K : C} (hK : IsCompactObject.{w} K)

/-- The defining compactness comparison: maps from `K` into a coproduct form
the direct sum of the Hom groups into its summands. -/
noncomputable def coproductComparisonIso {ι : Type w} (X : ι → C)
    [HasCoproduct X]
    [HasColimit (Discrete.functor X ⋙ preadditiveCoyoneda.obj (op K))] :
    (preadditiveCoyoneda.obj (op K)).obj (∐ X) ≅
      colimit (Discrete.functor X ⋙ preadditiveCoyoneda.obj (op K)) := by
  letI : PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op K)) := hK ι
  exact preservesColimitIso (preadditiveCoyoneda.obj (op K))
    (Discrete.functor X)

/-- Under the compactness comparison, postcomposition with a coproduct
injection is the corresponding direct-sum injection. -/
@[reassoc (attr := simp)]
theorem map_ι_coproductComparisonIso_hom {ι : Type w} (X : ι → C)
    [HasCoproduct X]
    [HasColimit (Discrete.functor X ⋙ preadditiveCoyoneda.obj (op K))]
    (i : ι) :
    (preadditiveCoyoneda.obj (op K)).map (Sigma.ι X i) ≫
      (hK.coproductComparisonIso X).hom =
        colimit.ι (Discrete.functor X ⋙ preadditiveCoyoneda.obj (op K))
          ⟨i⟩ := by
  letI : PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op K)) := hK ι
  exact ι_preservesColimitIso_hom
    (preadditiveCoyoneda.obj (op K)) (Discrete.functor X) ⟨i⟩

end IsCompactObject

namespace ObjectProperty

/-- The object property of compact objects. -/
def compactObjects : ObjectProperty C := fun K ↦ IsCompactObject.{w} K

/-- Compactness is invariant under isomorphism. -/
theorem isCompactObject_of_iso {K K' : C} (e : K ≅ K')
    (hK : IsCompactObject.{w} K) : IsCompactObject.{w} K' := by
  intro ι
  letI : PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op K)) := hK ι
  exact preservesColimitsOfShape_of_natIso
    (preadditiveCoyoneda.mapIso e.symm.op)

instance : (compactObjects.{w} (C := C)).IsClosedUnderIsomorphisms where
  of_iso e := isCompactObject_of_iso e

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Definition A.11's `Coprod(P)`: the smallest full subcategory containing
`P` and closed under isomorphisms, small coproducts, and extensions.

The coproduct constructor is phrased using an arbitrary colimit presentation,
not a chosen `∐`, so its universal property does not depend on implementation
choices for colimits. -/
inductive coprodClosure (P : ObjectProperty C) : ObjectProperty C
  | of_mem (X : C) (hX : P X) : coprodClosure P X
  | of_iso {X Y : C} (e : X ≅ Y) (hX : coprodClosure P X) : coprodClosure P Y
  | of_coproduct {ι : Type w} {F : Functor (Discrete ι) C}
      (c : Cocone F) (hc : IsColimit c)
      (hF : ∀ i, coprodClosure P (F.obj i)) : coprodClosure P c.pt
  | of_extension (T : Triangle C) (hT : T ∈ distTriang C)
      (h₁ : coprodClosure P T.obj₁) (h₃ : coprodClosure P T.obj₃) :
      coprodClosure P T.obj₂

variable (P : ObjectProperty C)

/-- Every generator belongs to its coproduct-and-extension closure. -/
lemma le_coprodClosure : P ≤ P.coprodClosure.{w} :=
  fun X hX ↦ .of_mem X hX

instance : P.coprodClosure.{w}.IsClosedUnderIsomorphisms where
  of_iso e hX := .of_iso e hX

instance (ι : Type w) :
    P.coprodClosure.{w}.IsClosedUnderColimitsOfShape (Discrete ι) where
  colimitsOfShape_le := by
    rintro X ⟨hX⟩
    exact .of_coproduct hX.toColimitPresentation.cocone
      hX.toColimitPresentation.isColimit hX.prop_diag_obj

instance : P.coprodClosure.{w}.IsTriangulatedClosed₂ where
  ext₂' T hT h₁ h₃ := P.coprodClosure.{w}.le_isoClosure _ (.of_extension T hT h₁ h₃)

/-- Universal property of `coprodClosure`: it is the smallest property with
the three closure properties in Definition A.11. -/
lemma coprodClosure_le {Q : ObjectProperty C}
    [Q.IsClosedUnderIsomorphisms]
    [∀ (ι : Type w), Q.IsClosedUnderColimitsOfShape (Discrete ι)]
    [Q.IsTriangulatedClosed₂] (hPQ : P ≤ Q) :
    P.coprodClosure.{w} ≤ Q := by
  intro X hX
  induction hX with
  | of_mem X hX => exact hPQ X hX
  | of_iso e _ ih => exact Q.prop_of_iso e ih
  | of_coproduct c hc _ ih => exact Q.prop_of_isColimit hc ih
  | of_extension T hT _ _ ih₁ ih₃ =>
      exact Q.ext_of_isTriangulatedClosed₂ T hT ih₁ ih₃

variable {P}

/-- A coproduct-preserving triangulated functor carries `Coprod(P)` into
`Coprod(F(P))`. This is the closure argument used in Step 1 of A.17. -/
theorem coprodClosure_map_obj
    {D : Type u₂} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D]
    (F : Functor C D) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : F.PreservesSmallCoproducts.{w}) {X : C}
    (hX : P.coprodClosure.{w} X) :
    (P.map F).coprodClosure.{w} (F.obj X) := by
  induction hX with
  | of_mem X hX =>
      exact (P.map F).le_coprodClosure.{w} _ (P.prop_map_obj F hX)
  | of_iso e _ ih =>
      exact .of_iso (F.mapIso e) ih
  | @of_coproduct ι K c hc hK ih =>
      letI : PreservesColimitsOfShape (Discrete ι) F := hF ι
      exact .of_coproduct (F.mapCocone c) (isColimitOfPreserves F hc) ih
  | of_extension T hT _ _ ih₁ ih₃ =>
      exact .of_extension (F.mapTriangle.obj T) (F.map_distinguished T hT) ih₁ ih₃

end ObjectProperty

namespace Adjunction

variable {C : Type u₁} [Category.{v} C] [Preadditive C]
  {D : Type u₂} [Category.{v} D] [Preadditive D]
  {L : Functor D C} {F : Functor C D} [L.Additive]

/-- A left adjoint to a small-coproduct-preserving functor carries compact
objects to compact objects. This is the compactness step in A.16 and A.17. -/
theorem isCompactObject_leftAdjoint_obj (adj : L ⊣ F)
    (hF : F.PreservesSmallCoproducts.{w}) {K : D}
    (hK : IsCompactObject.{w} K) : IsCompactObject.{w} (L.obj K) := by
  intro ι
  letI : PreservesColimitsOfShape (Discrete ι) F := hF ι
  letI : PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op K)) := hK ι
  haveI : PreservesColimitsOfShape (Discrete ι)
      (F ⋙ preadditiveCoyoneda.obj (op K)) := inferInstance
  let e : preadditiveCoyoneda.obj (op (L.obj K)) ≅
      F ⋙ preadditiveCoyoneda.obj (op K) :=
    NatIso.ofComponents
      (fun X ↦ (adj.homAddEquiv K X).toAddCommGrpIso)
      (fun f ↦ by
        ext g
        exact adj.homEquiv_naturality_right g f)
  exact preservesColimitsOfShape_of_natIso e.symm

/-- The essential image under a left adjoint of compact objects is compact
when the right adjoint preserves small coproducts. -/
theorem compactObjects_map_leftAdjoint (adj : L ⊣ F)
    (hF : F.PreservesSmallCoproducts.{w}) {G : ObjectProperty D}
    (hG : G ≤ ObjectProperty.compactObjects.{w} (C := D)) :
    G.map L ≤ ObjectProperty.compactObjects.{w} (C := C) := by
  rintro X ⟨Y, hY, ⟨e⟩⟩
  exact ObjectProperty.isCompactObject_of_iso e
    (adj.isCompactObject_leftAdjoint_obj hF (hG Y hY))

end Adjunction

namespace Triangulated.TStructure

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Definition A.11: `t` is compactly generated by `G` when the generators
are compact and its aisle is exactly `Coprod(G)`. -/
structure IsCompactlyGeneratedBy (t : TStructure C)
    (G : ObjectProperty C) : Prop where
  compact : G ≤ ObjectProperty.compactObjects.{w} (C := C)
  le_zero_eq : t.le 0 = G.coprodClosure.{w}

namespace IsCompactlyGeneratedBy

variable {t : TStructure C} {G : ObjectProperty C}

/-- A generator of a compactly generated t-structure lies in its aisle. -/
theorem isLE_zero_of_generator (h : t.IsCompactlyGeneratedBy.{w} G)
    {X : C} (hX : G X) : t.IsLE X 0 := by
  refine ⟨?_⟩
  rw [h.le_zero_eq]
  exact G.le_coprodClosure.{w} X hX

end IsCompactlyGeneratedBy

end Triangulated.TStructure

namespace Functor

variable {C : Type u₁} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {D : Type u₂} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
  {F : Functor C D} {t : TStructure C} {t' : TStructure D}
  {G : ObjectProperty C} {G' : ObjectProperty D}

/-- A coproduct-preserving triangulated functor which sends compact
generators into the target aisle is right t-exact.

This is Lemma A.16(1) and the right-t-exact half of Step 1 in A.17, isolated
from the geometric setting. -/
theorem isRightTExact_of_compactlyGenerated
    [F.CommShift ℤ] [F.IsTriangulated]
    (hF : F.PreservesSmallCoproducts.{w})
    (h : t.IsCompactlyGeneratedBy.{w} G)
    (h' : t'.IsCompactlyGeneratedBy.{w} G')
    (hgen : G.map F ≤ G'.coprodClosure.{w}) :
    F.IsRightTExact t t' :=
  F.isRightTExact_of_isLE_zero (fun X hX ↦ by
    have hClosure : G.coprodClosure.{w} X := by
      rw [← h.le_zero_eq]
      exact hX.le
    have hMap := G.coprodClosure_map_obj F hF hClosure
    have hTarget : G'.coprodClosure.{w} (F.obj X) :=
      (G.map F).coprodClosure_le hgen (F.obj X) hMap
    refine ⟨?_⟩
    rw [h'.le_zero_eq]
    exact hTarget)

end Functor

namespace Adjunction

variable {C : Type u₁} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {D : Type u₂} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
  {L : Functor D C} {F : Functor C D}
  {tC : TStructure C} {tD : TStructure D} {G : ObjectProperty D}

/-- Step 1 of A.17 after the A.13 t-structure has been constructed.

If `tD` is generated by `G`, `tC` is generated by its left-adjoint image,
`F` preserves coproducts, and the monad `L ⋙ F` is right t-exact, then `F`
is t-exact. The proof follows the paper: `L` is right t-exact by generation,
so its right adjoint `F` is left t-exact; the monad condition sends the source
generators into the target aisle, giving right t-exactness by closure.

The premise is an actually constructed `tC` with a proved aisle formula, not
a global proposition asserting Theorem A.13 or A.17. -/
theorem isTExact_of_compactlyGenerated (adj : L ⊣ F)
    [L.CommShift ℤ] [L.IsTriangulated]
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (hF : F.PreservesSmallCoproducts.{w})
    (hD : tD.IsCompactlyGeneratedBy.{w} G)
    (hC : tC.IsCompactlyGeneratedBy.{w} (G.map L))
    (hmonad : (L ⋙ F).IsRightTExact tD tD) : F.IsTExact tC tD := by
  have hL : L.PreservesSmallCoproducts.{w} := fun ι ↦ by
    haveI : PreservesColimitsOfShape (Discrete ι) L :=
      adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
    infer_instance
  letI : L.IsRightTExact tD tC :=
    L.isRightTExact_of_compactlyGenerated hL hD hC
      (fun X hX ↦ (G.map L).le_coprodClosure.{w} X hX)
  letI : F.IsLeftTExact tC tD :=
    Functor.isLeftTExact_rightAdjoint (F := L) (G := F) adj
  letI : (L ⋙ F).IsRightTExact tD tD := hmonad
  have hgen : (G.map L).map F ≤ G.coprodClosure.{w} := by
    rintro Z ⟨X, ⟨Y, hY, ⟨eL⟩⟩, ⟨eF⟩⟩
    have hYLE : tD.IsLE Y 0 := hD.isLE_zero_of_generator hY
    have hFLYLE : tD.IsLE ((L ⋙ F).obj Y) 0 :=
      Functor.IsRightTExact.isLE_map (F := L ⋙ F) (t := tD) (t' := tD)
        Y 0 hYLE
    have hZLE : tD.IsLE Z 0 := by
      haveI : tD.IsLE (F.obj (L.obj Y)) 0 := by simpa using hFLYLE
      exact tD.isLE_of_iso ((F.mapIso eL).trans eF) 0
    rw [← hD.le_zero_eq]
    exact hZLE.le
  letI : F.IsRightTExact tC tD :=
    F.isRightTExact_of_compactlyGenerated hF hC hD hgen
  exact Functor.isTExact_of (F := F) (t := tC) (t' := tD)

end Adjunction

end CategoryTheory
