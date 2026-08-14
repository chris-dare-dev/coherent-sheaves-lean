/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import DGLean.Category.H0
import DGLean.Model.Complexes

/-!
# The seam: `H⁰(C^dg A)` and the homotopy category

`dg-enhancements-e4`'s theorem. The route is to identify this repository's
`cocycles` and `coboundaries` with Mathlib's, so that the Hom-groups of
`H⁰(C^dg A)` *are* `CochainComplex.HomComplex.CohomologyClass _ _ 0`, and then
to use `CohomologyClass.homAddEquiv`, which Mathlib already proves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

open CategoryTheory CochainComplex CochainComplex.HomComplex

variable {A : Type u} [Category.{v} A] [Preadditive A]

namespace Cdg

/-- This repository's degree-zero cocycles are Mathlib's. -/
lemma cocycles_eq (K L : Cdg A) :
    cocycles K L = HomComplex.cocycle (of A K) (of A L) 0 := rfl

/-- This repository's degree-zero coboundaries are Mathlib's, transported along
`cocycles_eq`. Mathlib's version is a subgroup of the cocycles and asks for a
primitive in degree `m` with `m + 1 = 0`; this one is the range of `δ (-1) 0`.
The two conditions are the same condition. -/
lemma mem_coboundaries_iff' (K L : Cdg A) (f : (DGCategoryStruct.dgHom K L).X 0) :
    f ∈ _root_.coboundaries K L ↔ ∃ β : Cochain (of A K) (of A L) (-1), δ (-1) 0 β = f :=
  Iff.rfl

/-! ## Crossing the instance boundary

`Cocycle K L 0` and `↥(cocycles K L)` are the same subtype of the same group,
but `Cocycle` is a `def` carrying `instAddCommGroupCocycle` while the subgroup
carries the one `AddSubgroup` supplies. `AddSubgroup` is indexed by that
instance, so the two subgroup terms do not share a type for `rw`, and an `ext`
proof fails on an application type mismatch rather than on content.

Building the maps explicitly avoids the question: a hand-written
`AddMonoidHom` typechecks by defeq, where instance *matching* would not. -/

/-- This repository's degree-zero cocycles, as Mathlib's. -/
def toCocycle (K L : Cdg A) : ↥(cocycles K L) →+ Cocycle (of A K) (of A L) 0 where
  toFun z := ⟨z.1, z.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- And back. -/
def ofCocycle (K L : Cdg A) : Cocycle (of A K) (of A L) 0 →+ ↥(cocycles K L) where
  toFun z := ⟨z.1, z.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma toCocycle_val (K L : Cdg A) (z : ↥(cocycles K L)) :
    (toCocycle K L z).1 = z.1 := rfl

@[simp]
lemma ofCocycle_val (K L : Cdg A) (z : Cocycle (of A K) (of A L) 0) :
    (ofCocycle K L z).1 = z.1 := rfl

lemma ofCocycle_toCocycle (K L : Cdg A) (z : ↥(cocycles K L)) :
    ofCocycle K L (toCocycle K L z) = z := rfl

lemma toCocycle_ofCocycle (K L : Cdg A) (z : Cocycle (of A K) (of A L) 0) :
    toCocycle K L (ofCocycle K L z) = z := rfl

/-- The two subtypes are the same group; only their instance paths differ. -/
def cocycleAddEquiv (K L : Cdg A) : ↥(cocycles K L) ≃+ Cocycle (of A K) (of A L) 0 where
  toFun := toCocycle K L
  invFun := ofCocycle K L
  left_inv := ofCocycle_toCocycle K L
  right_inv := toCocycle_ofCocycle K L
  map_add' _ _ := rfl

/-! ## Lifting the identification to the quotients -/

lemma coboundariesIn_le_comap (K L : Cdg A) :
    H0.coboundariesIn K L ≤
      (HomComplex.coboundaries (of A K) (of A L) 0).comap (toCocycle K L) := by
  intro z hz
  rw [AddSubgroup.mem_comap, HomComplex.mem_coboundaries_iff _ (-1) (by omega)]
  exact hz

lemma coboundaries_le_comap (K L : Cdg A) :
    HomComplex.coboundaries (of A K) (of A L) 0 ≤
      (H0.coboundariesIn K L).comap (ofCocycle K L) := by
  intro z hz
  rw [HomComplex.mem_coboundaries_iff _ (-1) (by omega)] at hz
  exact hz

/-- The Hom-group of `H⁰(C^dg A)` is Mathlib's group of degree-zero cohomology
classes. Both directions are `QuotientAddGroup.map` of the corresponding
`AddMonoidHom`, and both round trips are `rfl` on representatives. -/
def homEquivCohomologyClass (K L : Cdg A) :
    (↥(cocycles K L) ⧸ H0.coboundariesIn K L) ≃+
      CohomologyClass (of A K) (of A L) 0 where
  toFun := QuotientAddGroup.map _ _ (toCocycle K L) (coboundariesIn_le_comap K L)
  invFun := QuotientAddGroup.map _ _ (ofCocycle K L) (coboundaries_le_comap K L)
  left_inv := by rintro ⟨z⟩; rfl
  right_inv := by rintro ⟨z⟩; rfl
  map_add' := by rintro ⟨a⟩ ⟨b⟩; rfl

/-! ## The Hom-level seam -/

/-- Postcomposition with an isomorphism, as an isomorphism of Hom-groups. Built
by hand because it is used once and the additivity is one `simp`. -/
def postcompAddEquiv {D : Type*} [Category D] [Preadditive D] {X Y Y' : D} (e : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X ⟶ Y') where
  toFun f := f ≫ e.hom
  invFun g := g ≫ e.inv
  left_inv f := by simp
  right_inv g := by simp
  map_add' _ _ := by simp [Preadditive.add_comp]

/-- **The Hom-level seam.** A degree-zero cohomology class in `C^dg A` is a
morphism of the homotopy category, and the correspondence is an isomorphism of
abelian groups.

Everything to the right of `homEquivCohomologyClass` is Mathlib's: the middle
step is `CohomologyClass.homAddEquiv`, and the last undoes the `⟦0⟧` its
statement carries. -/
noncomputable def homSeam (K L : Cdg A) :
    (↥(cocycles K L) ⧸ H0.coboundariesIn K L) ≃+
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (of A K) ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (of A L)) :=
  (homEquivCohomologyClass K L).trans
    (CohomologyClass.homAddEquiv.trans
      (postcompAddEquiv ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).mapIso
        ((shiftFunctorZero (CochainComplex A ℤ) ℤ).app (of A L)))))

end Cdg
