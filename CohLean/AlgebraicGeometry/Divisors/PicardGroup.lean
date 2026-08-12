/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import CohLean.AlgebraicGeometry.Divisors.Symmetric
import Mathlib.CategoryTheory.Monoidal.Skeleton

/-!
# The Picard group of a scheme

The symmetric monoidal category of locally free rank-one sheaves makes `PicardClass X` a
commutative monoid. `Pic X` is its group of units: an element records an isomorphism class and an
explicit tensor-inverse class. `Pic.mkOfTensorInverse` is the downstream constructor for line
bundles such as `O_X(D)` and `O_X(-D)`.
-/
open CategoryTheory MonoidalCategory

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

noncomputable instance picardClassCommMonoid (X : Scheme.{u}) :
    CommMonoid (PicardClass X) :=
  inferInstanceAs (CommMonoid (Skeleton (InvertibleSheaf X)))

namespace PicardClass

theorem one_eq_one (X : Scheme.{u}) :
    one X = (1 : PicardClass X) := by
  rfl

theorem mk_mul_mk (L M : X.Modules)
    [hL : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    [hM : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)] :
    mk L * mk M = mk (tensorObj L M) := by
  let L' : InvertibleSheaf X := ⟨L, hL⟩
  let M' : InvertibleSheaf X := ⟨M, hM⟩
  exact (CategoryTheory.Skeleton.toSkeleton_tensorObj L' M').symm

end PicardClass

/-- The Picard group: tensor-invertible isomorphism classes of locally free rank-one sheaves. -/
abbrev Pic (X : Scheme.{u}) := (PicardClass X)ˣ

namespace Pic

/-- Construct a Picard-group element from an explicit tensor inverse. -/
noncomputable def mkOfTensorInverse (L M : X.Modules)
    [hL : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    [hM : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)]
    (e : tensorObj L M ≅ SheafOfModules.unit X.ringCatSheaf) : Pic X := by
  letI : SheafOfModules.IsInvertible.{u, u, u}
      (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  exact
    { val := PicardClass.mk L
      inv := PicardClass.mk M
      val_inv := by
        rw [PicardClass.mk_mul_mk]
        exact ((PicardClass.mk_eq_mk_iff _ _).2 ⟨e⟩).trans
          (PicardClass.one_eq_one X)
      inv_val := by
        rw [PicardClass.mk_mul_mk]
        exact ((PicardClass.mk_eq_mk_iff _ _).2
          ⟨tensorCommIso M L ≪≫ e⟩).trans (PicardClass.one_eq_one X) }

@[simp]
theorem coe_mkOfTensorInverse (L M : X.Modules)
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)]
    [SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from M)]
    (e : tensorObj L M ≅ SheafOfModules.unit X.ringCatSheaf) :
    (mkOfTensorInverse L M e : PicardClass X) = PicardClass.mk L := rfl

@[simp]
theorem coe_one : ((1 : Pic X) : PicardClass X) = PicardClass.one X := by
  exact (PicardClass.one_eq_one X).symm

end Pic

end


end AlgebraicGeometry.Scheme.Modules
