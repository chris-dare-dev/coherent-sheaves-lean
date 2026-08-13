/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.TriangulatedGrothendieck
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Functoriality of the triangulated Grothendieck group

Triangulated functors induce homomorphisms on the repository-owned
Grothendieck group. Naturally isomorphic functors induce equal homomorphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u' v'

namespace BridgelandStabLean.Foundation

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Object classes transported by a triangulated functor are
triangle-additive. -/
@[nolint unusedArguments]
instance K₀.isTriangleAdditive_map (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    [F.IsTriangulated] : IsTriangleAdditive (fun X => K₀.of D (F.obj X)) where
  additive T hT := K₀.of_triangle D (F.mapTriangle.obj T) (F.map_distinguished T hT)

/-- The homomorphism on Grothendieck groups induced by a triangulated
functor. -/
def K₀.map (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] : K₀ C →+ K₀ D :=
  K₀.lift C (fun X => K₀.of D (F.obj X))

@[simp]
theorem K₀.map_of (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (X : C) : K₀.map F (K₀.of C X) = K₀.of D (F.obj X) :=
  K₀.lift_of C _ X

@[simp]
theorem K₀.map_id : K₀.map (𝟭 C) = AddMonoidHom.id (K₀ C) := by
  ext X
  simp

@[simp]
theorem K₀.map_comp (F : C ⥤ D) {E : Type*} [Category E]
    [HasZeroObject E] [HasShift E ℤ] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    (G : D ⥤ E) [F.Additive] [G.Additive] [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] :
    K₀.map (F ⋙ G) = (K₀.map G).comp (K₀.map F) := by
  ext X
  simp

/-- Naturally isomorphic triangulated functors induce the same map on
Grothendieck groups. -/
theorem K₀.map_congr {F G : C ⥤ D} [F.Additive] [G.Additive]
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (e : F ≅ G) : K₀.map F = K₀.map G := by
  ext X
  exact K₀.of_iso D (e.app X)

end BridgelandStabLean.Foundation
