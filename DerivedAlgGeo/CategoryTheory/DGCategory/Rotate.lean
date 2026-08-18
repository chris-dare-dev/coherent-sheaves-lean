/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.DGCategory.Cone

/-!
# Rotating a cone triangle

`dg-enhancements-e6`. The rotation axiom asks that `Y → Z → X⟦1⟧ → Y⟦1⟧` be
distinguished whenever `X → Y → Z → X⟦1⟧` is. Since a distinguished triangle is
one isomorphic to a *cone* triangle, what has to be produced is a comparison
between a cone on `inr : Y → Z` and the shift `X⟦1⟧`.

## `X⟦1⟧` is not a cone on `inr`, and cannot be made one

`IsConeOf` is a representability condition on the nose: maps into the cone split
*bijectively* in every degree. For a cone `W` on `inr`, that reads
`Hom(V, Y)⟨1⟩ × Hom(V, Z) ≅ Hom(V, W)`, and `Z` itself already splits as
`Hom(V, X)⟨1⟩ × Hom(V, Y)`. So `W` is three summands wide and `X⟦1⟧` is one; they
are not isomorphic as graded objects, and no choice of structure will make them so.

They *are* homotopy equivalent, which is all `H⁰` sees, and that is what this file
constructs: a pair of closed degree-zero maps between `W` and `X⟦1⟧`. The two
extra summands of `W` cancel in `H⁰` rather than being absent.

## The maps

`fwd = snd_W ≫ toShift`. Closed because `δ snd_W = -(fst_W ≫ inr)` — the cone's
one differential correction — and `inr ≫ toShift = 0`, which is the triangle
composing to zero at its second vertex. The correction is killed by the
orthogonality rather than by a choice.

`bwd` has to be assembled against the splitting, and its `inl_W`-component is
forced. Take `s.inv ≫ inl` for the `inr_W`-component: it is not closed, its
differential is `s.inv ≫ f ≫ inr`. The `inl_W`-component `-(s.inv ≫ f)`
contributes exactly `-(s.inv ≫ f ≫ inr)` through `δ inl_W = inr ≫ inr_W`, and its
own differential vanishes because `s.inv` and `f` are both closed. So the sum is
closed, and the sign is solved for rather than guessed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {C : Type u} [DGCategory.{v} C]

namespace IsConeOf

variable {X Y Z W X' : C} {f : (dgHom X Y).X 0} (hc : IsConeOf f Z)
  (hd : IsConeOf hc.inr W) (s : IsShiftBy X 1 X')

/-- The comparison `Cone(inr) ⟶ X⟦1⟧`: project to `Z`, then take the connecting
morphism of the original cone. -/
noncomputable def rotateFwd : (dgHom W X').X 0 :=
  dgComp 0 0 0 (by omega) hd.snd (hc.toShift s)

/-- It is closed. `δ snd_W` is the cone's correction term `-(fst_W ≫ inr)`, and
`inr ≫ toShift = 0` kills it. -/
lemma rotateFwd_closed : ((dgHom W X').d 0 1).hom (hc.rotateFwd hd s) = 0 := by
  have hleib : ((dgHom W X').d 0 1).hom
        (dgComp 0 0 0 (by omega) hd.snd (hc.toShift s)) =
      dgComp 0 1 1 (by omega) hd.snd (((dgHom Z X').d 0 1).hom (hc.toShift s)) +
        (0 : ℤ).negOnePow •
          dgComp 1 0 1 (by omega) (((dgHom W Z).d 0 1).hom hd.snd) (hc.toShift s) :=
    dgComp_leibniz (X := W) (Y := Z) (Z := X') 0 0 0 1 (by omega) (by omega)
      hd.snd (hc.toShift s)
  rw [rotateFwd, hleib, hc.toShift_closed s, hd.delta_snd, Int.negOnePow_zero, one_smul]
  simp only [map_zero, map_neg, AddMonoidHom.neg_apply, zero_add]
  rw [dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega), hc.inr_comp_toShift s]
  simp

/-- The comparison `X⟦1⟧ ⟶ Cone(inr)`, assembled against the splitting of maps
into the cone. -/
noncomputable def rotateBwd : (dgHom X' W).X 0 :=
  dgComp 1 (-1) 0 (by omega) (-dgComp 1 0 1 (by omega) s.inv f) hd.inl +
    dgComp 0 0 0 (by omega) (dgComp 1 (-1) 0 (by omega) s.inv hc.inl) hd.inr

include hc in
/-- The `inl_W`-component's own differential vanishes: `s.inv` is closed by
`IsShiftBy.inv_closed`, and `f` is closed by `IsConeOf.delta_f`. -/
lemma delta_shiftInvComp :
    ((dgHom X' Y).d 1 2).hom (dgComp 1 0 1 (by omega) s.inv f) = 0 := by
  have hleib : ((dgHom X' Y).d 1 2).hom (dgComp 1 0 1 (by omega) s.inv f) =
      dgComp 1 1 2 (by omega) s.inv (((dgHom X Y).d 0 1).hom f) +
        (0 : ℤ).negOnePow •
          dgComp 2 0 2 (by omega) (((dgHom X' X).d 1 2).hom s.inv) f :=
    dgComp_leibniz (X := X') (Y := X) (Z := Y) 1 0 1 2 (by omega) (by omega) s.inv f
  have hinv : ((dgHom X' X).d 1 2).hom s.inv = 0 := s.inv_closed
  rw [hleib, hc.delta_f, hinv]
  simp

/-- The `inr_W`-component is not closed, and this is its differential. -/
lemma delta_shiftInvComp_inl :
    ((dgHom X' Z).d 0 1).hom (dgComp 1 (-1) 0 (by omega) s.inv hc.inl) =
      dgComp 1 0 1 (by omega) s.inv (dgComp 0 0 0 (by omega) f hc.inr) := by
  have hleib : ((dgHom X' Z).d 0 1).hom (dgComp 1 (-1) 0 (by omega) s.inv hc.inl) =
      dgComp 1 0 1 (by omega) s.inv (((dgHom X Z).d (-1) 0).hom hc.inl) +
        (-1 : ℤ).negOnePow •
          dgComp 2 (-1) 1 (by omega) (((dgHom X' X).d 1 2).hom s.inv) hc.inl :=
    dgComp_leibniz (X := X') (Y := X) (Z := Z) 1 (-1) 0 1 (by omega) (by omega)
      s.inv hc.inl
  have hinv : ((dgHom X' X).d 1 2).hom s.inv = 0 := s.inv_closed
  rw [hleib, hc.δ_inl, hinv]
  simp

/-- **The backward comparison is closed.** The two components' differentials are
the same element of `Hom(X⟦1⟧, W)` with opposite signs: the `inl_W`-component
contributes through `δ inl_W = inr ≫ inr_W`, the `inr_W`-component through its
own failure to be closed. The sign in `rotateBwd` is what makes them cancel. -/
lemma rotateBwd_closed : ((dgHom X' W).d 0 1).hom (hc.rotateBwd hd s) = 0 := by
  have hleib₁ : ((dgHom X' W).d 0 1).hom
        (dgComp 1 (-1) 0 (by omega) (-dgComp 1 0 1 (by omega) s.inv f) hd.inl) =
      dgComp 1 0 1 (by omega) (-dgComp 1 0 1 (by omega) s.inv f)
          (((dgHom Y W).d (-1) 0).hom hd.inl) +
        (-1 : ℤ).negOnePow • dgComp 2 (-1) 1 (by omega)
          (((dgHom X' Y).d 1 2).hom (-dgComp 1 0 1 (by omega) s.inv f)) hd.inl :=
    dgComp_leibniz (X := X') (Y := Y) (Z := W) 1 (-1) 0 1 (by omega) (by omega) _ hd.inl
  have hleib₂ : ((dgHom X' W).d 0 1).hom
        (dgComp 0 0 0 (by omega) (dgComp 1 (-1) 0 (by omega) s.inv hc.inl) hd.inr) =
      dgComp 0 1 1 (by omega) (dgComp 1 (-1) 0 (by omega) s.inv hc.inl)
          (((dgHom Z W).d 0 1).hom hd.inr) +
        (0 : ℤ).negOnePow • dgComp 1 0 1 (by omega)
          (((dgHom X' Z).d 0 1).hom (dgComp 1 (-1) 0 (by omega) s.inv hc.inl)) hd.inr :=
    dgComp_leibniz (X := X') (Y := Z) (Z := W) 0 0 0 1 (by omega) (by omega) _ hd.inr
  rw [rotateBwd, map_add, hleib₁, hleib₂, hd.δ_inl, hd.inr_closed]
  simp only [map_neg, AddMonoidHom.neg_apply, map_zero, zero_add]
  rw [hc.delta_shiftInvComp s, hc.delta_shiftInvComp_inl s, Int.negOnePow_zero, one_smul]
  simp only [neg_zero, map_zero, AddMonoidHom.zero_apply, smul_zero, add_zero]
  rw [← dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega) s.inv f hc.inr,
    dgComp_assoc 1 0 0 1 0 1 (by omega) (by omega) (by omega)
      (dgComp 1 0 1 (by omega) s.inv f) hc.inr hd.inr]
  abel

end IsConeOf

end CategoryTheory
