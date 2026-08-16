/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Applying a finite sum of morphisms of abelian groups

`AddCommGrpCat` is preadditive, so a finite family of morphisms `A ⟶ B` can be summed. Mathlib
supplies `AddCommGrpCat.hom_add_apply` for a binary sum but nothing for a `Finset` sum, checked
against the pinned revision. A complex whose differential is an alternating sum of face maps
cannot be evaluated at an element without it.

## Main declarations

* `AddCommGrpCat.hom_sum_apply` — a finite sum of morphisms, applied;
* `AddCommGrpCat.hom_sum_zsmul_apply` — the alternating-sum form, where each summand carries an
  integer coefficient.

## Implementation notes

The `zsmul` step of `hom_sum_zsmul_apply` is `rfl`: the `ℤ`-action on morphisms of abelian
groups is pointwise by construction. Only the `Finset` sum needs an induction.

This is owned library code held against a gap in Mathlib rather than a placeholder; if Mathlib
later declares these names, redeclaring them here is a hard error rather than a shadowing
warning, and the fix is deleting this file.

## Tags

abelian group, preadditive, finite sum
-/

universe u

open CategoryTheory

namespace AddCommGrpCat

/-- A finite sum of morphisms of abelian groups is applied summand by summand. -/
theorem hom_sum_apply {A B : AddCommGrpCat.{u}} {J : Type*} (s : Finset J)
    (f : J → (A ⟶ B)) (a : A) :
    ConcreteCategory.hom (∑ i ∈ s, f i) a = ∑ i ∈ s, ConcreteCategory.hom (f i) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, AddCommGrpCat.hom_add_apply, ih]

/-- An integer-weighted finite sum of morphisms, applied. This is the shape an alternating sum
of face maps takes when evaluated at a cochain. -/
theorem hom_sum_zsmul_apply {A B : AddCommGrpCat.{u}} {J : Type*} (s : Finset J)
    (c : J → ℤ) (f : J → (A ⟶ B)) (a : A) :
    ConcreteCategory.hom (∑ i ∈ s, c i • f i) a =
      ∑ i ∈ s, c i • ConcreteCategory.hom (f i) a := by
  rw [hom_sum_apply]
  rfl

end AddCommGrpCat
