/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.StabilityCondition.Symmetry.Autoequivalence.Slicing.Transport
import BridgelandStability.GrothendieckGroup.Basic

/-!
# Functoriality of the Grothendieck group

One of the three pieces the `Aut` action on *stability conditions* needs. The
foundational library has `K₀.lift` (its universal property) but no functor action, so this
supplies it.

It turns out to be nearly free. `K₀.lift` wants a `IsTriangleAdditive` function
— one sending distinguished triangles to sums — and `X ↦ [F X]` is exactly that
whenever `F` is triangulated, because `F.map_distinguished` carries a
distinguished triangle to a distinguished triangle and
`(F.mapTriangle.obj T).obj₁` is *definitionally* `F.obj T.obj₁`. So the
instance is one line and the three laws are `ext; simp`.

`K0map_congr` is the one that matters for `AutQuot`: naturally isomorphic
functors induce the *same* map on `K₀`, because isomorphic objects already have
equal classes (`K₀.of_iso`). That is the `K₀`-level analogue of
`TriEquiv.act_congr`, and it is what will let the class-map half of the action
descend to the quotient.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Triangulated

universe w u

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- `X ↦ [F X]` is triangle-additive when `F` is triangulated.

`[F.Additive]` is unused by this term. It is kept so that this instance and
`K₀.mapF` — its only consumer, one line below — ask for the same thing;
deleting it here just re-flags `K₀.mapF`, measured 2026-08-05. The reasoning is
`AutAction.lean`'s module docstring, which owns the argument for all three
sites. -/
@[nolint unusedArguments]
instance isTriangleAdditive_of_isTriangulated
    (F : C ⥤ C) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] :
    IsTriangleAdditive (fun X => K₀.of C (F.obj X)) where
  additive T hT := K₀.of_triangle C (F.mapTriangle.obj T) (F.map_distinguished T hT)

/-- The endomorphism of `K₀ C` induced by a triangulated functor. -/
noncomputable def K₀.mapF (F : C ⥤ C) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] :
    K₀ C →+ K₀ C :=
  K₀.lift C (fun X => K₀.of C (F.obj X))

@[simp]
theorem K₀.mapF_of (F : C ⥤ C) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated] (X : C) :
    K₀.mapF F (K₀.of C X) = K₀.of C (F.obj X) :=
  K₀.lift_of C _ X

theorem K₀.mapF_id : K₀.mapF (𝟭 C) = AddMonoidHom.id (K₀ C) := by
  ext X; simp

theorem K₀.mapF_comp (F G : C ⥤ C) [F.Additive] [G.Additive]
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated] :
    K₀.mapF (F ⋙ G) = (K₀.mapF G).comp (K₀.mapF F) := by
  ext X; simp

/-- **Descent on `K₀`.** Naturally isomorphic functors induce the same map,
since isomorphic objects already have equal classes.

This is the `K₀`-level counterpart of `TriEquiv.act_congr`, and the reason the
class-map half of the `Aut` action will descend to `AutQuot`. -/
theorem K₀.mapF_congr {F G : C ⥤ C} [F.Additive] [G.Additive]
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (h : F ≅ G) : K₀.mapF F = K₀.mapF G := by
  ext X; simp [K₀.of_iso C (h.app X)]

end CategoryTheory.Triangulated
