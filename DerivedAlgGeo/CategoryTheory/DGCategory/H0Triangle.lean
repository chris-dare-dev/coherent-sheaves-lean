/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import DerivedAlgGeo.CategoryTheory.DGCategory.Cone
import DerivedAlgGeo.CategoryTheory.DGCategory.Rotate
import DerivedAlgGeo.CategoryTheory.DGCategory.Enhancement
import DerivedAlgGeo.CategoryTheory.DGCategory.H0Shift

/-!
# The distinguished triangles of `H⁰`

`dg-enhancements-e6`. `Pretriangulated` carries its distinguished triangles as a
*field*, so transporting a triangulated structure to `H⁰` starts by saying which
triangles those are. This file says it, and discharges the two axioms that follow
from the saying rather than from any computation.

## The definition

A triangle of `H⁰ C` is distinguished when it is isomorphic to one built from a
dg cone: `X → Y → Z → X⟦1⟧` with the second map `IsConeOf.inr` and the third
`IsConeOf.toShift`, the connecting morphism `DGCategory/Cone.lean` extracts.

Two choices in that sentence are worth naming.

**The shift is the chosen one.** `toShift` accepts any `IsShiftBy X 1 X'`, but the
triangle must land in `X⟦1⟧` — the shift `HasShift (H0 C) ℤ` actually uses, which
is `IsPretriangulated.shiftWitness`'s. Using it here rather than an arbitrary
witness keeps a comparison isomorphism out of every subsequent proof; the price is
paid once, in `H0Shift.lean`, where the choice was made.

**The cone is of a representative, not of the morphism.** A morphism of `H⁰` is a
homotopy class, and a cone is built from an actual cocycle. Different
representatives give different cones — isomorphic ones, but not equal — so the
definition quantifies over a cocycle and a cone on it, and closes under
isomorphism at the end. That is also why `distinguished_cocone_triangle` needs
`Quotient.ind` rather than a direct construction.

## What this file does not do

Three of the six `Pretriangulated` fields. `contractible_distinguished` needs the
cone on an identity to be a zero object of `H⁰`; `rotate_distinguished_triangle`
and `complete_distinguished_triangle_morphism` are the two theorems the axiom
system exists for. No `Pretriangulated` instance is claimed here, and the three
lemmas below are stated in the shape those fields want so that the instance is
assembly when they land.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory Limits Pretriangulated

namespace H0

variable {C : Type u} [DGCategory.{v} C]

/-- The morphism of `H⁰` a cocycle represents. -/
def homMk {X Y : C} (f : cocycles X Y) : (show H0 C from X) ⟶ (show H0 C from Y) :=
  QuotientAddGroup.mk f

variable (C) in
/-- The shift functors of `H⁰` are additive. `HasShift` unfolds to
`H0.shiftFunctor` only through `hasShiftMk`, which is not reducible, so instance
search needs to be told. -/
instance shiftFunctor_additive' (n : ℤ) [IsPretriangulated C] :
    (CategoryTheory.shiftFunctor (H0 C) n).Additive :=
  H0.shiftFunctor_additive C n

variable [IsPretriangulated C]

/-- The triangle a cone determines: the morphism, the cone's inclusion of the
target, and the connecting morphism into the chosen shift. -/
noncomputable def coneTriangle {X Y : C} (f : cocycles X Y) {Z : C}
    (hc : IsConeOf f.1 Z) : Triangle (H0 C) :=
  Triangle.mk (homMk f) (homMk ⟨hc.inr, hc.inr_mem_cocycles⟩)
    (homMk ⟨hc.toShift (IsPretriangulated.shiftWitness C X 1),
      hc.toShift_mem_cocycles _⟩)

/-- The cone triangle's first map. Stated so that the rotation proofs can rewrite
with it instead of unfolding `coneTriangle`, whose `dsimp` normal form breaks
type-correctness at `instances` transparency: `H0 C` reduces to `C`, and the
`Triangle.mk` in the unfolded term then reads its objects at the wrong type. -/
@[simp] lemma coneTriangle_mor₁ {X Y : C} (f : cocycles X Y) {Z : C}
    (hc : IsConeOf (f : (dgHom X Y).X 0) Z) : (coneTriangle f hc).mor₁ = homMk f := rfl

@[simp] lemma coneTriangle_mor₂ {X Y : C} (f : cocycles X Y) {Z : C}
    (hc : IsConeOf (f : (dgHom X Y).X 0) Z) :
    (coneTriangle f hc).mor₂ = homMk ⟨hc.inr, hc.inr_mem_cocycles⟩ := rfl

@[simp] lemma coneTriangle_mor₃ {X Y : C} (f : cocycles X Y) {Z : C}
    (hc : IsConeOf (f : (dgHom X Y).X 0) Z) :
    (coneTriangle f hc).mor₃ =
      homMk ⟨hc.toShift (IsPretriangulated.shiftWitness C X 1),
        hc.toShift_mem_cocycles _⟩ := rfl

variable (C) in
/-- The distinguished triangles of `H⁰`: those isomorphic to a cone triangle. -/
def distinguishedTriangles : Set (Triangle (H0 C)) :=
  {T | ∃ (X Y : C) (f : cocycles X Y) (Z : C) (hc : IsConeOf f.1 Z),
    Nonempty (T ≅ coneTriangle f hc)}

/-- A cone triangle is distinguished, by the identity isomorphism. -/
lemma coneTriangle_mem {X Y : C} (f : cocycles X Y) {Z : C} (hc : IsConeOf f.1 Z) :
    coneTriangle f hc ∈ distinguishedTriangles C :=
  ⟨X, Y, f, Z, hc, ⟨Iso.refl _⟩⟩

/-- **`isomorphic_distinguished`.** Immediate from the definition: the class is
defined as an isomorphism-closure, so this is transitivity. -/
lemma isomorphic_distinguished (T₁ : Triangle (H0 C))
    (hT₁ : T₁ ∈ distinguishedTriangles C) (T₂ : Triangle (H0 C)) (e : T₂ ≅ T₁) :
    T₂ ∈ distinguishedTriangles C := by
  obtain ⟨X, Y, f, Z, hc, ⟨e'⟩⟩ := hT₁
  exact ⟨X, Y, f, Z, hc, ⟨e ≪≫ e'⟩⟩

/-- **`distinguished_cocone_triangle`.** Every morphism of `H⁰` fits into a
distinguished triangle: pick a cocycle representing it, take a dg cone on that,
and the triangle is a cone triangle on the nose. -/
lemma distinguished_cocone_triangle {X Y : H0 C} (f : X ⟶ Y) :
    ∃ (Z : H0 C) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distinguishedTriangles C := by
  induction f using Quotient.ind with
  | _ f =>
    obtain ⟨Z, ⟨hc⟩⟩ := IsPretriangulated.exists_cone (C := C) (X := of C X) (Y := of C Y) f.1 f.2
    exact ⟨Z, @homMk C _ (of C Y) Z ⟨hc.inr, hc.inr_mem_cocycles⟩,
      @homMk C _ Z (IsPretriangulated.shiftObj C (of C X) 1)
        ⟨hc.toShift (IsPretriangulated.shiftWitness C (of C X) 1),
          hc.toShift_mem_cocycles _⟩,
      coneTriangle_mem (C := C) f hc⟩


omit [IsPretriangulated C] in
/-- A cone on an identity is a zero object of `H⁰`: its identity is a
coboundary, so it is zero in the quotient. `Enhancement.lean` proves the same
for an object whose dg identity vanishes on the nose; this is the version the
contractible triangle needs, where the identity is only null-homotopic. -/
lemma isZero_of_dgId_mem_coboundaries {Z : C} (h : dgId Z ∈ coboundaries Z Z) :
    IsZero (show H0 C from Z) := by
  rw [IsZero.iff_id_eq_zero]
  show (QuotientAddGroup.mk (⟨dgId Z, dgId_cocycle Z⟩ : cocycles Z Z)) = 0
  rw [QuotientAddGroup.eq_zero_iff]
  exact h

/-- **`contractible_distinguished`.** The triangle `X → X → 0` is distinguished:
a cone on `dgId X` is a zero object of `H⁰`, so it is isomorphic to the chosen
zero object, and every square in sight commutes because it factors through one.

The content is `IsConeOf.dgId_mem_coboundaries_of_dgId`; everything here is the
bookkeeping that turns a null-homotopy into an isomorphism of triangles. -/
lemma contractible_distinguished (X : H0 C) :
    contractibleTriangle X ∈ distinguishedTriangles C := by
  obtain ⟨Z, ⟨hc⟩⟩ := IsPretriangulated.exists_cone (C := C) (X := of C X) (Y := of C X)
    (dgId (of C X)) (dgId_cocycle _)
  refine isomorphic_distinguished _ (coneTriangle_mem (C := C) ⟨dgId (of C X),
    dgId_cocycle _⟩ hc) _ ?_
  have hZ : IsZero (show H0 C from Z) :=
    isZero_of_dgId_mem_coboundaries (C := C) hc.dgId_mem_coboundaries_of_dgId
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((IsZero.iso (isZero_zero (H0 C)) hZ)) ?_ ?_ ?_
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact hZ.eq_of_tgt _ _
  · exact (isZero_zero (H0 C)).eq_of_src _ _

omit [IsPretriangulated C] in
/-- Two cocycles represent the same morphism of `H⁰` when they differ by a
coboundary. The quotient's own `eq_iff_sub_mem` says so; this restates it on the
underlying elements, which is the form every homotopy in the track produces. -/
lemma homMk_eq_homMk {X Y : C} {a b : cocycles X Y}
    (h : (a : (dgHom X Y).X 0) - (b : (dgHom X Y).X 0) ∈ coboundaries X Y) :
    homMk a = homMk b := by
  refine QuotientAddGroup.eq_iff_sub_mem.2 ?_
  show ((a - b : cocycles X Y) : (dgHom X Y).X 0) ∈ coboundaries X Y
  rw [AddSubgroupClass.coe_sub]
  exact h

omit [IsPretriangulated C] in
/-- Negation of an `H⁰` morphism is negation of a representative. -/
lemma homMk_neg {X Y : C} (a : cocycles X Y) : homMk (-a) = -homMk a := rfl

omit [IsPretriangulated C] in
/-- Composition of `H⁰` morphisms is `dgComp` of representatives. -/
lemma homMk_comp {X Y Z : C} (a : cocycles X Y) (b : cocycles Y Z) :
    homMk a ≫ homMk b =
      homMk ⟨dgComp 0 0 0 (by omega) (a : (dgHom X Y).X 0) (b : (dgHom Y Z).X 0),
        Z0.comp_mem a.2 b.2⟩ :=
  rfl

section Rotate

variable {X Y Z W : C} {f : cocycles X Y} (hc : IsConeOf (f : (dgHom X Y).X 0) Z)
  (hd : IsConeOf hc.inr W)

/-- The comparison of `dg-enhancements-e6`'s rotation, as an isomorphism of `H⁰`.

Both composites were proved in `DGCategory/Rotate.lean`: one on the nose, one up
to the primitive exhibited there. In `H⁰` that difference disappears, which is
the whole reason the rotation axiom is a statement about `H⁰` and not about the
dg category. -/
noncomputable def rotateIso :
    (show H0 C from IsPretriangulated.shiftObj C X 1) ≅ (show H0 C from W) where
  hom := homMk ⟨hc.rotateBwd hd (IsPretriangulated.shiftWitness C X 1),
    hc.rotateBwd_closed hd _⟩
  inv := homMk ⟨hc.rotateFwd hd (IsPretriangulated.shiftWitness C X 1),
    hc.rotateFwd_closed hd _⟩
  hom_inv_id := by
    rw [homMk_comp]
    exact congrArg _ (Subtype.ext (hc.rotateBwd_comp_rotateFwd hd _))
  inv_hom_id := by
    rw [homMk_comp]
    exact homMk_eq_homMk (hc.rotateFwd_comp_rotateBwd_sub_dgId hd _)

@[simp] lemma rotateIso_hom :
    (rotateIso hc hd).hom = homMk ⟨hc.rotateBwd hd (IsPretriangulated.shiftWitness C X 1),
      hc.rotateBwd_closed hd _⟩ := rfl

@[simp] lemma rotateIso_inv :
    (rotateIso hc hd).inv = homMk ⟨hc.rotateFwd hd (IsPretriangulated.shiftWitness C X 1),
      hc.rotateFwd_closed hd _⟩ := rfl

/-- The rotation of a cone triangle is the cone triangle on its second map. -/
noncomputable def rotateConeTriangleIso :
    (coneTriangle f hc).rotate ≅ coneTriangle ⟨hc.inr, hc.inr_mem_cocycles⟩ hd :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (rotateIso hc hd)
    -- Term mode throughout: `rw` on these goals unfolds `H0 C` to `C`, and the
    -- categorical rewrites then fail as not type-correct at `instances`
    -- transparency. `exact` elaborates against the stated goal and never does.
    (by exact (Category.comp_id _).trans (Category.id_comp _).symm)
    (by
      exact ((homMk_comp _ _).trans
        (homMk_eq_homMk (hc.toShift_comp_rotateBwd_sub_inr hd _))).trans
        (Category.id_comp _).symm)
    (by
      have key : (rotateIso hc hd).hom ≫
            (coneTriangle ⟨hc.inr, hc.inr_mem_cocycles⟩ hd).mor₃ =
          -(CategoryTheory.shiftFunctor (H0 C) (1 : ℤ)).map (homMk f) :=
        (homMk_comp _ _).trans
          ((congrArg (@homMk C _ _ _) (Subtype.ext
            (hc.rotateBwd_comp_toShift hd (IsPretriangulated.shiftWitness C X 1)
              (IsPretriangulated.shiftWitness C Y 1)))).trans
            ((homMk_neg (C := C) _).trans
              (congrArg Neg.neg (H0.shiftFunctor_map_mk (C := C) 1 f).symm)))
      exact ((congrArg _ (Functor.map_id _ _)).trans (Category.comp_id _)).trans key.symm)

/-- **`rotate_distinguished_triangle`, forward direction.** The rotation of a
distinguished triangle is distinguished. -/
lemma rotate_mem_of_mem (T : Triangle (H0 C)) (hT : T ∈ distinguishedTriangles C) :
    T.rotate ∈ distinguishedTriangles C := by
  obtain ⟨X, Y, f, Z, hc, ⟨e⟩⟩ := hT
  obtain ⟨W, ⟨hd⟩⟩ := IsPretriangulated.exists_cone (C := C) hc.inr hc.inr_mem_cocycles
  exact isomorphic_distinguished _
    (coneTriangle_mem (C := C) ⟨hc.inr, hc.inr_mem_cocycles⟩ hd) _
    ((Pretriangulated.rotate (H0 C)).mapIso e ≪≫ rotateConeTriangleIso hc hd)

end Rotate

end H0

end CategoryTheory
