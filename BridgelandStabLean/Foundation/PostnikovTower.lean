/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Owner-authored Postnikov towers

This file begins the repository-owned foundation for Bridgeland stability. A
`PostnikovTower C E` packages a finite filtration of `E` by distinguished
triangles and depends only on Mathlib.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace BridgelandStabLean.Foundation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A finite Postnikov tower of `E`. The `i`-th factor is the third object of
the distinguished triangle connecting consecutive objects in the chain. -/
structure PostnikovTower (E : C) where
  /-- The number of factors. -/
  n : ℕ
  /-- The filtered chain `A₀ ⟶ A₁ ⟶ ⋯ ⟶ Aₙ`. -/
  chain : ComposableArrows C n
  /-- The triangle connecting each consecutive pair. -/
  triangle : Fin n → Pretriangulated.Triangle C
  /-- Every connecting triangle is distinguished. -/
  triangle_dist : ∀ i, triangle i ∈ distTriang C
  /-- The first triangle object agrees with the lower chain object. -/
  triangle_obj₁ : ∀ i, Nonempty ((triangle i).obj₁ ≅ chain.obj' i.val (by lia))
  /-- The second triangle object agrees with the upper chain object. -/
  triangle_obj₂ : ∀ i, Nonempty ((triangle i).obj₂ ≅ chain.obj' (i.val + 1) (by lia))
  /-- The tower begins at a zero object. -/
  base_isZero : IsZero chain.left
  /-- The top of the tower is isomorphic to the filtered object. -/
  top_iso : Nonempty (chain.right ≅ E)
  /-- A tower with no factors filters only a zero object. -/
  zero_isZero : n = 0 → IsZero E

/-- The number of factors in a Postnikov tower. -/
def PostnikovTower.length {E : C} (P : PostnikovTower C E) : ℕ := P.n

variable {C} in
/-- The `i`-th factor of a Postnikov tower. -/
def PostnikovTower.factor {E : C} (P : PostnikovTower C E) (i : Fin P.n) : C :=
  (P.triangle i).obj₃

variable {C} in
/-- The family of all factor objects of a Postnikov tower. -/
def PostnikovTower.factors {E : C} (P : PostnikovTower C E) : Fin P.n → C :=
  P.factor

end BridgelandStabLean.Foundation
