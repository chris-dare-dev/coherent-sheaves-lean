/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import DerivedAlgGeo.CategoryTheory.DGCategory.Cone
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

end H0

end CategoryTheory
